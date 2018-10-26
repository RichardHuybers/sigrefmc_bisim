/*
 * Copyright 2015 Formal Methods and Tools, University of Twente
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#include <unistd.h>
#include <sys/time.h>

#include <sylvan.h>
#include <sylvan_int.h>
#include <sylvan_obj.hpp>

#include <bisimulation.hpp>
#include <blocks.h>
#include <getrss.h>
#include <inert.h>
#include <refine.h>
#include <sigref.h>
#include <sigref_util.hpp>

#include <fstream>

namespace sigref {

using namespace sylvan;
using namespace std;

#define sig_strong(relations, count, partition, prime_variables) CALL(sig_strong, relations, count, partition, prime_variables)
TASK_4(BDD, sig_strong, BDD *, relations, int, count, BDD, partition, BDD, prime_variables)
{
    if (count == 1) {
        /* We assume that the relation is extended to the full domain */
        return sylvan_and_exists(*relations, partition, prime_variables);
    } else {
        bdd_refs_spawn(SPAWN(sig_strong, relations, count/2, partition, prime_variables));
        BDD right = bdd_refs_push(CALL(sig_strong, relations+(count/2), count-count/2, partition, prime_variables));
        BDD left = bdd_refs_push(bdd_refs_sync(SYNC(sig_strong)));
        BDD result = sylvan_or(left, right);
        bdd_refs_pop(2);
        return result;
    }
}


#define par_relprev(dd, relations, relation_count, st_variables) CALL(par_relprev, dd, relations, relation_count, st_variables)
TASK_4(BDD, par_relprev, BDD, dd, BDD*, relations, int, count, BDD, st_variables)
{
    if (count == 1) {
        return sylvan_relprev(*relations, dd, st_variables);
    } else {
        bdd_refs_spawn(SPAWN(par_relprev, dd, relations, count/2, st_variables));
        BDD right = bdd_refs_push(CALL(par_relprev, dd, relations+(count/2), count-count/2, st_variables));
        BDD left = bdd_refs_push(bdd_refs_sync(SYNC(par_relprev)));
        BDD result = sylvan_or(left, right);
        bdd_refs_pop(2);
        return result;
    }
}  


/**
 * Implementation of strong LTS minimisation
 */

TASK_IMPL_1(BDD, min_lts_strong, LTS&, lts)
{
    ofstream nodes_P;
    nodes_P.open("nodes_P_lts.dat");
    nodes_P << "Iteration\tNodes\n";

    ofstream nodes_sigma;
    nodes_sigma.open("nodes_sigma_lts.dat");
    nodes_sigma << "Iteration\tNodes\n";

    /* Gather data, prepare block variables and signatures array */
    int n_relations = lts.getTransitions().size();
    BDD transition_relations[n_relations];
    BDD transition_variables[n_relations];
    for (int i=0; i<n_relations; i++) {
        transition_relations[i] = lts.getTransitions()[i].first.GetBDD();
        transition_variables[i] = lts.getTransitions()[i].second.GetBDD();
    }

    BDD state_variables = lts.getVarS().GetBDD();
    BDD prime_variables = lts.getVarT().GetBDD();
    BDD st_variables = sylvan_and(state_variables, prime_variables);
    sylvan_ref(st_variables);

    int state_length = sylvan_set_count(state_variables);
    int action_length = sylvan_set_count(lts.getVarA().GetBDD());

    prepare_blocks(state_length+1);
    set_signatures_size(1ULL<<block_length);

    /* Extending transition relations to full domain */

    for (int i=0; i<n_relations; i++) {
        transition_relations[i] = extend_relation(transition_relations[i], transition_variables[i], state_length);
        sylvan_protect(transition_relations+i);
    }

    /* Create initial partition */

    BDD partition;
    sylvan_protect(&partition);

    if (lts.getInitialPartition().size() > 0) {
        partition = sylvan_false;
        // note that our algorithms assume a partition is defined on s',b (not s,b)
        for (Bdd dd : lts.getInitialPartition()) {
            // encode next block number
            BDD block = CALL(encode_block, get_next_block());
            bdd_refs_push(block);
            // rename states from s to s'
            BDD states = swap_prime(dd.GetBDD());
            bdd_refs_push(states);
            // block := states' * block
            block = sylvan_and(states, block);
            bdd_refs_push(block);
            // partition := partition + block
            partition = sylvan_or(partition, block);
            bdd_refs_pop(3);
        }
    } else {
        partition = CALL(encode_block, get_next_block());
    }

    size_t n_blocks = count_blocks();

    /* Write some information */

    double n_states = sylvan_satcount(partition, sylvan_and(prime_variables, block_variables));
    long double transitions_before = big_satcount(transition_relations, n_relations, state_length*2+action_length, mtbdd_true);
    long double reachable_transitions_before = big_satcount(transition_relations, n_relations, state_length*2+action_length, lts.getStates().GetBDD());

    INFO("Number of state variables: %d.", state_length);
    INFO("Number of action variables: %d.", action_length);
    INFO("Number of block variables: %d.", block_length);
    INFO("Number of transition relations: %d.", n_relations);
    INFO("Number of transitions: %'0.0Lf.", transitions_before);
    INFO("Number of reachable transitions: %'0.0Lf.", reachable_transitions_before);

    if (verbosity >= 2) {
        size_t node_count = mtbdd_nodecount_more(transition_relations, n_relations);
        INFO("Transition relation: %'zu BDD nodes.", node_count);
    }

    INFO("Initial partition: %'0.0f states in %zu block(s).", n_states, n_blocks);

    if (verbosity >= 2) {
        INFO("Partition: %'zu BDD nodes.", mtbdd_nodecount(partition));
    }

    /* Start partition refinement */

    double t_sig = 0;
    double t_ref = 0;

    double t1 = wctime();

    if (merge_relations) {
        INFO("Taking the union of all transition relations.");
        transition_relations[0] = big_union(transition_relations, n_relations);
        for (int i=1;i<n_relations;i++) transition_relations[i] = sylvan_false;
        n_relations = 1;
        if (verbosity >= 2) {
            INFO("Monolithic transition relation: %'zu BDD nodes.", mtbdd_nodecount(transition_relations[0]));
        }
    }

    nodes_P << 0 << "\t" << sylvan_nodecount(partition) << "\n";

    size_t iteration = 1;
    size_t old_n_blocks = 0;
    while (n_blocks != old_n_blocks) {
        old_n_blocks = n_blocks;

        if (verbosity >= 1) {
            INFO("");
            INFO("Iteration %zu", iteration);
        }

        double i1 = wctime();

        // compute signature
        BDD signature = sig_strong(transition_relations, n_relations, partition, prime_variables);

        // print status
        if (verbosity >= 1) {
            if (verbosity >= 2) {
                INFO("Calculated signature: %'zu BDD nodes. Assigning blocks...", sylvan_nodecount(signature));
            } else {
                INFO("Calculated signature. Assigning blocks...");
            }
        }

        nodes_sigma << iteration << "\t" << sylvan_nodecount(signature) << "\n";

        double i2 = wctime();

        // compute partition (s',b) from signature
        bdd_refs_push(signature);
        partition = refine(signature, state_variables, partition);
        n_blocks = count_blocks();
        bdd_refs_pop(1);

        nodes_P << iteration << "\t" << sylvan_nodecount(partition) << "\n";

        double i3 = wctime();

        INFO("After iteration %zu: %'zu blocks.", ++iteration, n_blocks);

        // update timekeeping
        t_sig += (i2-i1);
        t_ref += (i3-i2);

        // print extra information
        if (verbosity >= 2) {
            INFO("Partition: %'zu BDD nodes.", sylvan_nodecount(partition));
            INFO("Current #nodes in table: %'zu of %'zu BDD nodes.", llmsset_count_marked(nodes), llmsset_get_size(nodes));
        }

        if (verbosity >= 1) {
            INFO("Current/Max RSS: %'zu / %'zu bytes.", getCurrentRSS(), getPeakRSS());
        }
    }

    double t2 = wctime();

    // compute number of transitions
    double transitions_after = count_transitions(0, n_blocks, block_length + action_length);

    INFO("");
    INFO("Time for computing the bisimulation relation: %'0.2f sec.", t2-t1);
    INFO("Time for signature computation: %'0.2f s.", t_sig);
    INFO("Time for partition refinement: %'0.2f s.", t_ref);
    INFO("");
    INFO("Number of iterations: %'zu.", iteration-1);
    INFO("Number of states before bisimulation minimisation: %'0.0f.", n_states);
    INFO("Number of blocks after bisimulation minimisation: %'zu.", n_blocks);
    INFO("Number of transitions before bisimulation minimisation: %'0.0Lf.", transitions_before);
    INFO("Number of reachable transitions before bisimulation minimisation: %'0.0Lf.", reachable_transitions_before);
    INFO("Number of transitions after bisimulation minimisation: %'0.0f.", transitions_after);

    /* RICHARD */
    //BDD partition_prime = rename_vars(partition, prime_variables, state_variables);
    //BDD eq_pairs = sylvan_and_exists(partition, partition_prime, block_variables);
    //INFO("Number of equivalent state pairs: %'zu", (size_t)sylvan_satcount(eq_pairs, sylvan_and(state_variables, prime_variables)));


    nodes_P.close();
    nodes_sigma.close();

    sylvan_deref(st_variables);
    for (int i=0; i<n_relations; i++) {
        sylvan_unprotect(transition_relations+i);
    }
    sylvan_unprotect(&partition);

    return partition;
}


/***
 * Implementation of branching LTS minimisation
 */

TASK_IMPL_1(BDD, min_lts_branching, LTS&, lts)
{
    /* Gather data, prepare block variables and signatures array */

    int n_relations = lts.getTransitions().size();
    BDD transition_relations[n_relations];
    BDD transition_variables[n_relations];
    for (int i=0; i<n_relations; i++) {
        transition_relations[i] = lts.getTransitions()[i].first.GetBDD();
        transition_variables[i] = lts.getTransitions()[i].second.GetBDD();
    }

    BDD state_variables = lts.getVarS().GetBDD();
    BDD prime_variables = lts.getVarT().GetBDD();
    BDD action_variables = lts.getVarA().GetBDD();
    BDD st_variables = sylvan_and(state_variables, prime_variables);
    sylvan_ref(st_variables);

    int state_length = sylvan_set_count(state_variables);
    int action_length = sylvan_set_count(action_variables);

    prepare_blocks(state_length+1);
    set_signatures_size(1ULL<<block_length);

    /* Extending transition relations to full domain */

    for (int i=0; i<n_relations; i++) {
        transition_relations[i] = extend_relation(transition_relations[i], transition_variables[i], state_length);
        sylvan_protect(transition_relations+i);
    }

    /* Create initial partition */

    BDD partition;
    sylvan_protect(&partition);

    if (lts.getInitialPartition().size() > 0) {
        partition = sylvan_false;
        // note that our algorithms assume a partition is defined on s',b (not s,b)
        for (Bdd dd : lts.getInitialPartition()) {
            // encode next block number
            BDD block = CALL(encode_block, get_next_block());
            bdd_refs_push(block);
            // rename states from s to s'
            BDD states = swap_prime(dd.GetBDD());
            bdd_refs_push(states);
            // block := states' * block
            block = sylvan_and(states, block);
            bdd_refs_push(block);
            // partition := partition + block
            partition = sylvan_or(partition, block);
            bdd_refs_pop(3);
        }
    } else {
        partition = CALL(encode_block, get_next_block());
    }

    size_t n_blocks = count_blocks();

    /* Write some information */

    double n_states = sylvan_satcount(partition, sylvan_and(prime_variables, block_variables));
    long double transitions_before = big_satcount(transition_relations, n_relations, state_length*2+action_length, mtbdd_true);
    long double reachable_transitions_before = big_satcount(transition_relations, n_relations, state_length*2+action_length, lts.getStates().GetBDD());

    INFO("Number of state variables: %d.", state_length);
    INFO("Number of action variables: %d.", action_length);
    INFO("Number of block variables: %d.", block_length);
    INFO("Number of transition relations: %d.", n_relations);
    INFO("Number of transitions: %'0.0Lf.", transitions_before);
    INFO("Number of reachable transitions: %'0.0Lf.", reachable_transitions_before);

    if (verbosity >= 2) {
        size_t node_count = mtbdd_nodecount_more(transition_relations, n_relations);
        INFO("Transition relation: %'zu BDD nodes.", node_count);
    }

    INFO("Initial partition: %'0.0f states in %zu block(s).", n_states, n_blocks);

    if (verbosity >= 2) {
        INFO("Partition: %'zu BDD nodes.", mtbdd_nodecount(partition));
    }

    /* Start partition refinement */

    double t_sig = 0;
    double t_ref = 0;

    double t1 = wctime();

    if (merge_relations || closure) {
        INFO("Taking the union of all transition relations.");
        transition_relations[0] = big_union(transition_relations, n_relations);
        for (int i=1;i<n_relations;i++) transition_relations[i] = sylvan_false;
        n_relations = 1;
        if (verbosity >= 2) {
            INFO("Monolithic transition relation: %'zu BDD nodes.", mtbdd_nodecount(transition_relations[0]));
        }
    }

    BDD tau_transitions[n_relations];

    INFO("Precomputing tau transitions for branching bisimulation.");
    for (int i=0; i<n_relations; i++) {
        tau_transitions[i] = sylvan_and(transition_relations[i], lts.getTau().GetBDD());
        sylvan_protect(tau_transitions+i);
    }

    if (closure) {
        INFO("Precomputing closure of tau transition.");

        /* create s=s' */
        BDD eq = sylvan_true;
        for (int i=state_length-1; i>=0; i--) {
            BDD low = sylvan_makenode(2*i+1, eq, sylvan_false);
            bdd_refs_push(low);
            BDD high = sylvan_makenode(2*i+1, sylvan_false, eq);
            bdd_refs_pop(1);
            eq = sylvan_makenode(2*i, low, high);
        }

        /* t := reflexive closure of tau_transitions[0] */
        bdd_refs_push(eq);
        BDD t = sylvan_or(tau_transitions[0], eq);
        bdd_refs_pop(1);

        if (closure == 1) {
            BDD u = sylvan_false;
            int c=0;
            while (u != t) {
                u = t;
                bdd_refs_push(t);
                t = sylvan_relprev(t, t, st_variables);
                bdd_refs_pop(1);
                if (verbosity >= 2) {
                    INFO("Size of squaring %d times: %zu BDD nodes.", ++c, sylvan_nodecount(t));
                }
            }
            tau_transitions[0] = t;
        } else /* closure == 2 */ {
            bdd_refs_push(t);
            t = sylvan_exists(t, action_variables);
            bdd_refs_pop(1);
            bdd_refs_push(t);
            t = sylvan_closure(t);
            bdd_refs_pop(1);
            bdd_refs_push(t);
            tau_transitions[0] = sylvan_and(t, lts.getTau().GetBDD());
            bdd_refs_pop(1);
        }

        if (verbosity >= 2) {
            INFO("Reflexive transitive closure: %'0.0f transitions using %zu BDD nodes.", sylvan_satcount(t, st_variables), sylvan_nodecount(tau_transitions[0]));
        } else if (verbosity == 1) {
            INFO("Reflexive transitive closure: %'0.0f transitions.", sylvan_satcount(t, st_variables));
        }
    }

    size_t iteration = 1;
    size_t old_n_blocks = 0;
    while (n_blocks != old_n_blocks) {
        old_n_blocks = n_blocks;

        if (verbosity >= 1) {
            INFO("");
            INFO("Iteration %zu", iteration);
        }

        double i1 = wctime();

        // compute signature

        // compute the set of inert tau transitions on (s,t,a)
        if (verbosity >= 1) INFO("Computing inert tau transitions.");

        BDD inert[n_relations];
        for (int i=0; i<n_relations; i++) {
            inert[i] = compute_inert(tau_transitions[i], partition, partition, st_variables);
            bdd_refs_push(inert[i]);
        }

        if (verbosity >= 1) INFO("Computing non-inert tau transitions.");

        // remove all inert tau transitions from transition_relation
        BDD non_inert[n_relations];
        for (int i=0; i<n_relations; i++) {
            non_inert[i] = sylvan_and(transition_relations[i], sylvan_not(inert[i]));
            bdd_refs_push(non_inert[i]);
        }

        if (verbosity >= 1) INFO("Quantifying inert tau transitions");

        // abstraction to obtain the set of inert tau transition on (s,t)
        for (int i=0; i<n_relations; i++) {
            inert[i] = sylvan_exists(inert[i], action_variables);
            bdd_refs_push(inert[i]);
        }

        bdd_refs_pop(3*n_relations);
        for (int i=0; i<n_relations; i++) {
            bdd_refs_push(inert[i]);
            bdd_refs_push(non_inert[i]);
        }

        if (verbosity >= 1) INFO("Computing last step.");

        // compute last step of signature on (s,a,B)
        BDD signature = sig_strong(non_inert, n_relations, partition, prime_variables);

        bdd_refs_pop(2*n_relations);
        for (int i=0; i<n_relations; i++) bdd_refs_push(inert[i]);

        if (verbosity >= 1) INFO("Computing backward reachability using tau steps.");

        if (closure) {
            bdd_refs_push(signature);
            signature = sylvan_relprev(inert[0], signature, st_variables);
            bdd_refs_pop(1);
        } else {
            int count = 0;

            // now apply inert transitions repeatedly until fixpoint
            BDD old_sig = sylvan_false;
            while (old_sig != signature) {
                old_sig = signature;

                bdd_refs_push(signature);
                BDD sig_step = par_relprev(signature, inert, n_relations, st_variables);
                bdd_refs_push(sig_step);
                signature = sylvan_or(signature, sig_step);
                bdd_refs_pop(2);

                if (verbosity >= 1) {
                    INFO("Iteration %d done.", ++count);
                }
            }
        }

        if (verbosity >= 2) {
            INFO("Calculated signature: %'zu BDD nodes. Assigning blocks...", sylvan_nodecount(signature));
        } else if (verbosity == 1) {
            INFO("Calculated signature. Assigning blocks...");
        }

        double i2 = wctime();

        // compute partition (s',b) from signature
        bdd_refs_push(signature);
        partition = refine(signature, state_variables, partition);
        n_blocks = count_blocks();
        bdd_refs_pop(1);

        double i3 = wctime();

        INFO("After iteration %zu: %'zu blocks.", iteration++, n_blocks);

        // update timekeeping
        t_sig += (i2-i1);
        t_ref += (i3-i2);

        // print extra information
        if (verbosity >= 2) {
            INFO("Partition: %'zu BDD nodes.", sylvan_nodecount(partition));
            INFO("Current #nodes in table: %'zu of %'zu BDD nodes.", llmsset_count_marked(nodes), llmsset_get_size(nodes));
        }

        if (verbosity >= 1) {
            INFO("Current/Max RSS: %'zu / %'zu bytes.", getCurrentRSS(), getPeakRSS());
        }
    }

    double t2 = wctime();

    // compute number of transitions
    double transitions_after = count_transitions(0, n_blocks, block_length + action_length);

    INFO("");
    INFO("Time for computing the bisimulation relation: %'0.2f sec.", t2-t1);
    INFO("Time for signature computation: %'0.2f s.", t_sig);
    INFO("Time for partition refinement: %'0.2f s.", t_ref);
    INFO("");
    INFO("Number of iterations: %'zu.", iteration-1);
    INFO("Number of states before bisimulation minimisation: %'0.0f.", n_states);
    INFO("Number of blocks after bisimulation minimisation: %'zu.", n_blocks);
    INFO("Number of transitions before bisimulation minimisation: %'0.0Lf.", transitions_before);
    INFO("Number of reachable transitions before bisimulation minimisation: %'0.0Lf.", reachable_transitions_before);
    INFO("Number of transitions after bisimulation minimisation: %'0.0f.", transitions_after);

    sylvan_deref(st_variables);
    for (int i=0; i<n_relations; i++) {
        sylvan_unprotect(transition_relations+i);
        sylvan_unprotect(tau_transitions+i);
    }
    sylvan_unprotect(&partition);

    return partition;
}

}
