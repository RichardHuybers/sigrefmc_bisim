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

#include <stddef.h>
#include <unistd.h>
#include <sys/time.h>

#include <sylvan.h>
#include <sylvan_int.h>
#include <sylvan_obj.hpp>

#include <bisimulation.hpp>
#include <blocks.h>
#include <getrss.h>
#include <refine.h>
#include <sigref.h>
#include <sigref_util.hpp>
#include <sylvan_gmp.h>

namespace sigref {

using namespace sylvan;

/**
 * Implementation of CTMC minimisation
 */
TASK_IMPL_1(BDD, min_ctmc, CTMC&, ctmc)
{
    /* Gather data, prepare block variables and signatures array */

    MTBDD transition_relation = ctmc.getMarkovTransitions().GetMTBDD();
    BDD state_variables = ctmc.getVarS().GetBDD();
    BDD prime_variables = ctmc.getVarT().GetBDD();
    int state_length = sylvan_set_count(state_variables);

    prepare_blocks(state_length+1);
    set_signatures_size(1ULL<<block_length);

    /* Create initial partition */

    BDD partition;
    sylvan_protect(&partition);

    if (ctmc.getInitialPartition().size() > 0) {
        partition = sylvan_false;
        // note that our algorithms assume a partition is defined on s',b (not s,b)
        for (Bdd dd : ctmc.getInitialPartition()) {
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
        // just put all states in one block
        partition = CALL(encode_block, get_next_block());
    }

    size_t n_blocks = count_blocks();

    /* Write some information */

    double n_states = sylvan_satcount(partition, sylvan_and(prime_variables, block_variables));
    double transitions_before = mtbdd_satcount(transition_relation, state_length*2);

    INFO("Number of state variables: %d.", state_length);
    INFO("Number of block variables: %d.", block_length);
    INFO("Number of Markovian transitions: %'0.0f", transitions_before);

    if (verbosity >= 2) {
        INFO("Transition relation: %'zu MTBDD nodes.", mtbdd_nodecount(transition_relation));
    }

    INFO("Initial partition: %'0.0f states in %zu block(s).", n_states, n_blocks);

    if (verbosity >= 2) {
        INFO("Partition: %'zu BDD nodes.", sylvan_nodecount(partition));
    }

    /* Start partition refinement */

    double t_sig = 0;
    double t_ref = 0;

    double t1 = wctime();

    size_t iteration = 1;
    size_t old_n_blocks = 0;
    while (n_blocks != old_n_blocks) {
        old_n_blocks = n_blocks;

        if (verbosity >= 1) {
            INFO("");
            INFO("Iteration %zu", iteration);
        }

        double i1 = wctime();

        // compute signature (s,b) => real/rational
        MTBDD signature;
        if (leaftype == 2) signature = gmp_and_exists(transition_relation, partition, prime_variables);
        else signature = mtbdd_and_exists(transition_relation, partition, prime_variables);

        // print status
        if (verbosity >= 2) {
            INFO("Calculated signature: %'zu BDD nodes. Assigning blocks...", mtbdd_nodecount(signature));
        } else if (verbosity == 1) {
            INFO("Calculated signature. Assigning blocks...");
        }

        double i2 = wctime();

        // compute partition (s',b) from signature
        mtbdd_refs_push(signature);
        partition = refine(signature, state_variables, partition);
        n_blocks = count_blocks();
        mtbdd_refs_pop(1);

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
    double transitions_after = count_transitions(0, n_blocks, block_length);

    INFO("");
    INFO("Time for computing the bisimulation relation: %'0.2f sec.", t2-t1);
    INFO("Time for signature computation: %'0.2f sec.", t_sig);
    INFO("Time for partition refinement: %'0.2f sec.", t_ref);
    INFO("");
    INFO("Number of iterations: %'zu.", iteration-1);
    INFO("Number of states before bisimulation minimisation: %'0.0f.", n_states);
    INFO("Number of blocks after bisimulation minimisation: %'zu.", n_blocks);
    INFO("Number of transitions before bisimulation minimisation: %'0.0f.", transitions_before);
    INFO("Number of transitions after bisimulation minimisation: %'0.0f.", transitions_after);

    sylvan_unprotect(&partition);
    return partition;
}

}
