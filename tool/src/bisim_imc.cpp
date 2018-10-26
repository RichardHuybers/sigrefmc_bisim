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

#include <assert.h>
#include <stddef.h>
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
#include <sylvan_gmp.h>

namespace sigref {

using namespace sylvan;

/**
 * Compute equivalent of functions a and b
 * f(x) = a(x) if b(x) == F (not defined in b)
 * f(x) = b(x) if a(x) == F (not defined in a)
 * f(x) = a(x) if a(x) == b(x)
 * f(x) = neq  if a(x) != b(x)
 * with x being all valuations of vars <vars>
 * and <vars> appearing before any other variables
 * MTBDD "neq" should not appear in a or b
 */
TASK_4(MTBDD, equi, MTBDD, a, MTBDD, b, MTBDD, vars, MTBDD, neq)
{
    if (a == neq || b == neq) return neq; // once, always
    if (a == mtbdd_false) return b;
    if (b == mtbdd_false) return a;
    if (vars == mtbdd_true) return a == b ? a : neq;
    if (a == b) return a;

    sylvan_gc_test();

    uint32_t va = mtbdd_isnode(a) ? mtbdd_getvar(a) : 0xffffffff;
    uint32_t vb = mtbdd_isnode(b) ? mtbdd_getvar(b) : 0xffffffff;
    uint32_t v = va < vb ? va : vb;
    uint32_t vv = mtbdd_getvar(vars);

    for (;;) {
        if (vv == v) break;
        assert(vv < v);
        vars = mtbdd_gethigh(vars);
        if (vars == mtbdd_true) return a == b ? a : neq;
        vv = mtbdd_getvar(vars);
    }

    MTBDD result;
    if (cache_get3(CACHE_EQUI, a, b, vars, &result)) return result;

    MTBDD a0 = va == v ? mtbdd_getlow(a) : a;
    MTBDD a1 = va == v ? mtbdd_gethigh(a) : a;
    MTBDD b0 = vb == v ? mtbdd_getlow(b) : b;
    MTBDD b1 = vb == v ? mtbdd_gethigh(b) : b;

    MTBDD _vars = mtbdd_gethigh(vars);

    mtbdd_refs_spawn(SPAWN(equi, a0, b0, _vars, neq));
    MTBDD r1 = mtbdd_refs_push(CALL(equi, a1, b1, _vars, neq));
    MTBDD r0 = mtbdd_refs_sync(SYNC(equi));
    mtbdd_refs_pop(1);
    result = mtbdd_makenode(v, r0, r1);

    cache_put3(CACHE_EQUI, a, b, vars, result);
    return result;
}


/**
 * Apply transition relation a to set b, and abstraction using <equi>
 */
TASK_3(MTBDD, relprev, MTBDD, a, MTBDD, b, MTBDD, vars)
{
    /* Terminals */
    if (b == mtbdd_false) return mtbdd_false;
    if (a == mtbdd_false) return mtbdd_false;
    if (vars == mtbdd_true) return b;

    /* Perhaps execute garbage collection */
    sylvan_gc_test();

    /* Determine top level */
    uint32_t va = mtbdd_isnode(a) ? mtbdd_getvar(a) : 0xffffffff;
    uint32_t vb = mtbdd_isnode(b) ? mtbdd_getvar(b) : 0xffffffff;
    uint32_t level = va < vb ? va : vb;

    /* Skip vars */
    for (;;) {
        /* check if level is s/t */
        uint32_t vv = mtbdd_getvar(vars);
        if (level == vv || (level^1) == vv) break;
        assert (level > vv); /* no skipping of variables */
        vars = mtbdd_gethigh(vars);
        if (vars == mtbdd_true) {
            assert(a == mtbdd_true); // a must be defined only on vars
            return b;
        }
    }

    /* Consult cache */
    MTBDD result;
    if (cache_get3(CACHE_BDD_RELPREV, a, b, vars, &result)) return result;

    /* Get s and t */
    uint32_t s = level & (~1);
    uint32_t t = s+1;

    MTBDD a0, a1, b0, b1;

    if (va == s) {
        a0 = mtbdd_getlow(a);
        a1 = mtbdd_gethigh(a);
    } else {
        a0 = a1 = a;
    }

    if (vb == s) {
        b0 = mtbdd_getlow(b);
        b1 = mtbdd_gethigh(b);
    } else {
        b0 = b1 = b;
    }

    MTBDD a00, a01, a10, a11;

    if (mtbdd_isnode(a0) && mtbdd_getvar(a0) == t) {
        a00 = mtbdd_getlow(a0);
        a01 = mtbdd_gethigh(a0);
    } else {
        a00 = a01 = a0;
    }

    if (mtbdd_isnode(a1) && mtbdd_getvar(a1) == t) {
        a10 = mtbdd_getlow(a1);
        a11 = mtbdd_gethigh(a1);
    } else {
        a10 = a11 = a1;
    }

    MTBDD _vars = mtbdd_gethigh(vars);
    assert(_vars != mtbdd_true && mtbdd_getvar(_vars) == t);
    _vars = mtbdd_gethigh(_vars);

    mtbdd_refs_spawn(SPAWN(relprev, a00, b0, _vars));
    mtbdd_refs_spawn(SPAWN(relprev, a01, b1, _vars));
    mtbdd_refs_spawn(SPAWN(relprev, a10, b0, _vars));
    mtbdd_refs_spawn(SPAWN(relprev, a11, b1, _vars));

    MTBDD r11 = mtbdd_refs_push(mtbdd_refs_sync(SYNC(relprev)));
    MTBDD r10 = mtbdd_refs_push(mtbdd_refs_sync(SYNC(relprev)));
    MTBDD r01 = mtbdd_refs_push(mtbdd_refs_sync(SYNC(relprev)));
    MTBDD r00 = mtbdd_refs_push(mtbdd_refs_sync(SYNC(relprev)));

    mtbdd_refs_spawn(SPAWN(equi, r00, r01, _vars, mtbdd_true));
    MTBDD r1 = mtbdd_refs_push(CALL(equi, r10, r11, _vars, mtbdd_true));
    MTBDD r0 = mtbdd_refs_sync(SYNC(equi));
    mtbdd_refs_pop(5);
    result = mtbdd_makenode(s, r0, r1);

    cache_put3(CACHE_BDD_RELPREV, a, b, vars, result);
    return result;
}


/***
 * Implementation of strong IMC minimisation
 */

TASK_IMPL_1(BDD, min_imc_strong, IMC&, imc)
{
    /* Gather data, prepare block variables and signatures array */

    assert(imc.getTransitions().size() == 1); // only support 1 transition relation for now
    BDD action_relation = imc.getTransitions()[0].first.GetBDD();
    MTBDD markov_relation = imc.getMarkovTransitions().GetMTBDD();
    mtbdd_protect(&markov_relation); // markov_relation object might be changed

    BDD state_variables = imc.getVarS().GetBDD();
    BDD prime_variables = imc.getVarT().GetBDD();
    BDD action_variables = imc.getVarA().GetBDD();
    int state_length = sylvan_set_count(state_variables);
    int action_length = sylvan_set_count(action_variables);

    BDD st_variables = sylvan_and(state_variables, prime_variables);
    BDD sta_variables = sylvan_and(st_variables, action_variables);
    BDD ta_variables = sylvan_and(prime_variables, action_variables);

    sylvan_ref(st_variables);
    sylvan_ref(sta_variables);
    sylvan_ref(ta_variables);

    prepare_blocks(state_length+1);
    set_signatures_size(1ULL<<block_length);

    /* Create initial partition */

    BDD partition;
    sylvan_protect(&partition);

    if (imc.getInitialPartition().size() > 0) {
        partition = sylvan_false;
        // note that our algorithms assume a partition is defined on s',b (not s,b)
        for (Bdd dd : imc.getInitialPartition()) {
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
    double markov_transitions_before = mtbdd_satcount(markov_relation, state_length*2);
    double action_transitions_before = mtbdd_satcount(action_relation, state_length*2 + action_length);

    INFO("Number of state variables: %d.", state_length);
    INFO("Number of action variables: %d.", action_length);
    INFO("Number of block variables: %d.", block_length);
    INFO("Number of Markovian transitions: %'0.0f", markov_transitions_before);
    INFO("Number of interactive transitions: %'0.0f", action_transitions_before);

    if (verbosity >= 2) {
        INFO("Markovian transition relation: %'zu MTBDD nodes.", mtbdd_nodecount(markov_relation));
        INFO("Interactive transition relation: %'zu BDD nodes.", mtbdd_nodecount(action_relation));
    }

    INFO("Initial partition: %'0.0f states in %zu block(s).", n_states, n_blocks);

    if (verbosity >= 2) {
        INFO("Partition: %'zu BDD nodes.", sylvan_nodecount(partition));
    }

    /* Start preprocessing */

    double t_msig = 0;
    double t_mref = 0;
    double t_isig = 0;
    double t_iref = 0;

    double t1 = wctime();

    /* Compute set of tau transitions */

    if (verbosity >= 1) {
        INFO("Computing tau transitions.");
    }

    BDD tau_transitions = sylvan_and(action_relation, imc.getTau().GetBDD());
    sylvan_protect(&tau_transitions);

    if (verbosity >= 1) {
        INFO("Number of tau transitions: %'0.0f", sylvan_satcount(tau_transitions, sta_variables));
        if (verbosity >= 2) {
            INFO("Tau transition relation: %'zu BDD nodes.", mtbdd_nodecount(tau_transitions));
        }
    }

    /* Compute set of states with outgoing tau transitions */

    if (verbosity >= 1) {
        INFO("Computing tau states.");
    }

    BDD tau_states = sylvan_exists(tau_transitions, ta_variables);
    sylvan_protect(&tau_states);

    /* Set default rate to 0 (when no rates) instead of False */

    if (leaftype == 0) markov_relation = mtbdd_max(markov_relation, mtbdd_double(0));
    else if (leaftype == 1) markov_relation = mtbdd_max(markov_relation, mtbdd_fraction(0, 1));
    else if (leaftype == 2) {
        mpq_t m_zero;
        mpq_init(m_zero);
        mpq_set_ui(m_zero, 0, 1);
        MTBDD zero = mtbdd_gmp(m_zero);
        mpq_clear(m_zero);
        markov_relation = gmp_max(markov_relation, zero);
    }

    /* Apply maximal progress cut */

    INFO("Computing maximal-progress cut.");
    if (leaftype == 2) markov_relation = gmp_times(markov_relation, sylvan_not(tau_states));
    else markov_relation = mtbdd_times(markov_relation, sylvan_not(tau_states));

    if (verbosity >= 1) {
        INFO("Number of Markovian transitions (mp): %'0.0f", mtbdd_satcount(markov_relation, state_length*2));
        if (verbosity >= 2) {
            INFO("Markovian transition relation (mp): %'zu MTBDD nodes.", mtbdd_nodecount(markov_relation));
        }
    }

    /* Start partition refinement */

    size_t iteration = 1;
    size_t old_n_blocks = 0, old_n_blocks2 = 0;
    while (n_blocks != old_n_blocks) {
        old_n_blocks = n_blocks;

        if (verbosity >= 1) {
            INFO("");
            INFO("Iteration %zu", iteration);
        }

        double i1 = wctime();

        // compute strong signature
        MTBDD signature;
        if (leaftype == 2) signature = gmp_and_exists(markov_relation, partition, prime_variables);
        else signature = mtbdd_and_exists(markov_relation, partition, prime_variables);

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

        INFO("After iteration %zu-a: %'zu blocks.", iteration, n_blocks);

        if (old_n_blocks2 == n_blocks) break;
        old_n_blocks2 = n_blocks;

        double i3 = wctime();

        // compute interactive strong signature
        signature = sylvan_and_exists(action_relation, partition, prime_variables);

        double i4 = wctime();

        // compute partition (s',b) from signature
        mtbdd_refs_push(signature);
        partition = refine(signature, state_variables, partition);
        n_blocks = count_blocks();
        mtbdd_refs_pop(1);

        double i5 = wctime();

        // update timekeeping
        t_msig += i2-i1;
        t_mref += i3-i2;
        t_isig += i4-i3;
        t_iref += i5-i4;

        INFO("After iteration %zu-b: %'zu blocks.", iteration++, n_blocks);

        if (verbosity >= 2) {
            INFO("Partition: %'zu BDD nodes.", sylvan_nodecount(partition));
            INFO("Current #nodes in table: %'zu of %'zu BDD nodes.", llmsset_count_marked(nodes), llmsset_get_size(nodes));
        }

        if (verbosity >= 1) {
            INFO("Current/Max RSS: %'zu / %'zu bytes.", getCurrentRSS(), getPeakRSS());
        }
    }

    double t2 = wctime();

    INFO("");
    INFO("Time for computing the bisimulation relation: %'0.2f sec.", t2-t1);
    INFO("Time for Markovian signature computation: %'0.2f s.", t_msig);
    INFO("Time for Markovian partition refinement: %'0.2f s.", t_mref);
    INFO("Time for interactive signature computation: %'0.2f s.", t_isig);
    INFO("Time for interactive partition refinement: %'0.2f s.", t_iref);
    INFO("");
    INFO("Number of iterations: %'zu.", iteration-1);
    INFO("Number of states before bisimulation minimisation: %'0.0f.", n_states);
    INFO("Number of blocks after bisimulation minimisation: %'zu.", n_blocks);

    mtbdd_unprotect(&markov_relation); // markov_relation object might be changed
    sylvan_deref(st_variables);
    sylvan_deref(sta_variables);
    sylvan_deref(ta_variables);
    sylvan_unprotect(&partition);
    sylvan_unprotect(&tau_transitions);
    sylvan_unprotect(&tau_states);

    return partition;
}


/***
 * Implementation of branching IMC minimisation
 */

TASK_IMPL_1(BDD, min_imc_branching, IMC&, imc)
{
    /* Gather data, prepare block variables and signatures array */

    assert(imc.getTransitions().size() == 1); // only support 1 transition relation for now
    BDD action_relation = imc.getTransitions()[0].first.GetBDD();
    MTBDD markov_relation = imc.getMarkovTransitions().GetMTBDD();
    mtbdd_protect(&markov_relation); // markov_relation object might be changed

    BDD state_variables = imc.getVarS().GetBDD();
    BDD prime_variables = imc.getVarT().GetBDD();
    BDD action_variables = imc.getVarA().GetBDD();
    int state_length = sylvan_set_count(state_variables);
    int action_length = sylvan_set_count(action_variables);

    BDD st_variables = sylvan_and(state_variables, prime_variables);
    BDD sta_variables = sylvan_and(st_variables, action_variables);
    BDD ta_variables = sylvan_and(prime_variables, action_variables);

    sylvan_ref(st_variables);
    sylvan_ref(sta_variables);
    sylvan_ref(ta_variables);

    prepare_blocks(state_length+1);
    set_signatures_size(1ULL<<block_length);

    /* Create initial partition */

    BDD partition;
    sylvan_protect(&partition);

    if (imc.getInitialPartition().size() > 0) {
        partition = sylvan_false;
        // note that our algorithms assume a partition is defined on s',b (not s,b)
        for (Bdd dd : imc.getInitialPartition()) {
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
    double markov_transitions_before = mtbdd_satcount(markov_relation, state_length*2);
    double action_transitions_before = mtbdd_satcount(action_relation, state_length*2 + action_length);

    INFO("Number of state variables: %d.", state_length);
    INFO("Number of action variables: %d.", action_length);
    INFO("Number of block variables: %d.", block_length);
    INFO("Number of Markovian transitions: %'0.0f", markov_transitions_before);
    INFO("Number of interactive transitions: %'0.0f", action_transitions_before);

    if (verbosity >= 2) {
        INFO("Markovian transition relation: %'zu MTBDD nodes.", mtbdd_nodecount(markov_relation));
        INFO("Interactive transition relation: %'zu BDD nodes.", mtbdd_nodecount(action_relation));
    }

    INFO("Initial partition: %'0.0f states in %zu block(s).", n_states, n_blocks);

    if (verbosity >= 2) {
        INFO("Partition: %'zu BDD nodes.", sylvan_nodecount(partition));
    }

    /* Start preprocessing */

    double t_msig = 0;
    double t_mref = 0;
    double t_isig = 0;
    double t_iref = 0;

    double t1 = wctime();

    /* Compute set of tau transitions */

    if (verbosity >= 1) {
        INFO("Computing tau transitions.");
    }

    BDD tau_transitions = sylvan_and(action_relation, imc.getTau().GetBDD());
    sylvan_protect(&tau_transitions);

    if (verbosity >= 1) {
        INFO("Number of tau transitions: %'0.0f", sylvan_satcount(tau_transitions, sta_variables));
        if (verbosity >= 2) {
            INFO("Tau transition relation: %'zu BDD nodes.", mtbdd_nodecount(tau_transitions));
        }
    }

    /* Compute set of states with outgoing tau transitions */

    if (verbosity >= 1) {
        INFO("Computing tau states.");
    }

    BDD tau_states = sylvan_exists(tau_transitions, ta_variables);
    sylvan_protect(&tau_states);

    /* Set default rate to 0 (when no rates) instead of False */

    if (leaftype == 0) markov_relation = mtbdd_max(markov_relation, mtbdd_double(0));
    else if (leaftype == 1) markov_relation = mtbdd_max(markov_relation, mtbdd_fraction(0, 1));
    else if (leaftype == 2) {
        mpq_t m_zero;
        mpq_init(m_zero);
        mpq_set_ui(m_zero, 0, 1);
        MTBDD zero = mtbdd_gmp(m_zero);
        mpq_clear(m_zero);
        markov_relation = gmp_max(markov_relation, zero);
    }

    /* Apply maximal progress cut */

    INFO("Computing maximal-progress cut.");
    if (leaftype == 2) markov_relation = gmp_times(markov_relation, sylvan_not(tau_states));
    else markov_relation = mtbdd_times(markov_relation, sylvan_not(tau_states));

    if (verbosity >= 1) {
        INFO("Number of Markovian transitions (mp): %'0.0f", mtbdd_satcount(markov_relation, state_length*2));
        if (verbosity >= 2) {
            INFO("Markovian transition relation (mp): %'zu MTBDD nodes.", mtbdd_nodecount(markov_relation));
        }
    }

    /* For branching bisimulation: make tau transition reflexive */

    if (verbosity >= 1) {
        INFO("Making tau transitions reflexive.");
    }

    /* create s=s' */
    BDD eq = sylvan_true;
    for (int i=state_length-1; i>=0; i--) {
        BDD low = sylvan_makenode(2*i+1, eq, sylvan_false);
        bdd_refs_push(low);
        BDD high = sylvan_makenode(2*i+1, sylvan_false, eq);
        bdd_refs_pop(1);
        eq = sylvan_makenode(2*i, low, high);
    }

    tau_transitions = sylvan_or(tau_transitions, eq);

    /* Start partition refinement */

    size_t iteration = 1;
    size_t old_n_blocks = 0, old_n_blocks2 = 0;
    while (n_blocks != old_n_blocks) {
        old_n_blocks = n_blocks;

        if (verbosity >= 1) {
            INFO("");
            INFO("Iteration %zu", iteration);
        }

        double i1 = wctime();

        // compute branching signature
        if (verbosity >= 1) INFO("Computing last step.");

        MTBDD signature;
        if (leaftype == 2) signature = gmp_and_exists(markov_relation, partition, prime_variables);
        else signature = mtbdd_and_exists(markov_relation, partition, prime_variables);

        if (verbosity >= 2) INFO("Signature: %'zu BDD nodes.", mtbdd_nodecount(signature));

        mtbdd_refs_push(signature);

        if (verbosity >= 1) INFO("Computing inert tau transitions.");

        BDD inert = compute_inert(tau_transitions, partition, partition, st_variables);
        bdd_refs_push(inert);
        inert = sylvan_exists(inert, action_variables);
        bdd_refs_pop(1);

        bdd_refs_push(inert);

        if (closure == 0) {
            if (verbosity >= 1) INFO("Computing backward reachability using tau steps.");

            // now apply inert transitions repeatedly until fixpoint
            MTBDD old_sig = sylvan_false;
            while (old_sig != signature) {
                old_sig = signature;

                signature = CALL(relprev, inert, signature, st_variables);
                mtbdd_refs_pop(1);
                mtbdd_refs_push(signature);
            }
        } else {
            if (verbosity >= 1) INFO("Computing closure of inert tau transitions.");

            if (closure == 1) {
                BDD old_inert = sylvan_false;
                while (old_inert != inert) {
                    old_inert = inert;
                    inert = sylvan_relprev(inert, inert, st_variables);
                    bdd_refs_pop(1);
                    bdd_refs_push(inert);
                }
            } else /* closure == 2 */ {
                inert = sylvan_closure(inert);
                bdd_refs_pop(1);
                bdd_refs_push(inert);
            }

            signature = CALL(relprev, inert, signature, st_variables);
        }

        bdd_refs_pop(1); // inert
        mtbdd_refs_pop(1); // signature

        if (verbosity >= 2) {
            INFO("Calculated signature: %'zu BDD nodes. Assigning blocks...", mtbdd_nodecount(signature));
        } else if (verbosity >= 1) {
            INFO("Calculated signature. Assigning blocks...");
        }

        double i2 = wctime();

        // compute partition (s',b) from signature
        mtbdd_refs_push(signature);
        partition = refine(signature, state_variables, partition);
        n_blocks = count_blocks();
        mtbdd_refs_pop(1);

        INFO("After iteration %zu-a: %'zu blocks.", iteration, n_blocks);

        if (old_n_blocks2 == n_blocks) break;
        old_n_blocks2 = n_blocks;

        double i3 = wctime();

        // compute interactive branching signature
        if (verbosity >= 1) INFO("Computing inert tau transitions.");

        inert = compute_inert(tau_transitions, partition, partition, st_variables);
        bdd_refs_push(inert);
        BDD noninert = sylvan_and(action_relation, sylvan_not(inert));
        bdd_refs_push(noninert);
        inert = sylvan_exists(inert, action_variables);
        bdd_refs_pop(2);

        if (verbosity >= 1) INFO("Inert steps: %'0.0f transitions.", sylvan_satcount(inert, st_variables));
        if (verbosity >= 1) INFO("Non-inert steps: %'0.0f transitions.", sylvan_satcount(noninert, sta_variables));

        if (verbosity >= 1) INFO("Computing last step.");

        bdd_refs_push(inert);

        bdd_refs_push(noninert);
        signature = sylvan_and_exists(noninert, partition, prime_variables);
        bdd_refs_pop(1); // noninert

        if (verbosity >= 1) INFO("Computing backward reachability using tau steps.");

        // now apply inert transitions repeatedly until fixpoint
        BDD old_sig = sylvan_false;
        while (old_sig != signature) {
            old_sig = signature;

            bdd_refs_push(signature);
            signature = sylvan_relprev(inert, signature, st_variables);
            bdd_refs_pop(1);
        }

        bdd_refs_pop(1); // inert

        double i4 = wctime();

        // compute partition (s',b) from signature
        mtbdd_refs_push(signature);
        partition = refine(signature, state_variables, partition);
        n_blocks = count_blocks();
        mtbdd_refs_pop(1);

        double i5 = wctime();

        INFO("After iteration %zu-b: %'zu blocks.", iteration++, n_blocks);

        // update timekeeping
        t_msig += i2-i1;
        t_mref += i3-i2;
        t_isig += i4-i3;
        t_iref += i5-i4;

        if (verbosity >= 2) {
            INFO("Partition: %'zu BDD nodes.", sylvan_nodecount(partition));
            INFO("Current #nodes in table: %'zu of %'zu BDD nodes.", llmsset_count_marked(nodes), llmsset_get_size(nodes));
        }

        if (verbosity >= 1) {
            INFO("Current/Max RSS: %'zu / %'zu bytes.", getCurrentRSS(), getPeakRSS());
        }
    }

    double t2 = wctime();

    INFO("");
    INFO("Time for computing the bisimulation relation: %'0.2f sec.", t2-t1);
    INFO("Time for Markovian signature computation: %'0.2f s.", t_msig);
    INFO("Time for Markovian partition refinement: %'0.2f s.", t_mref);
    INFO("Time for interactive signature computation: %'0.2f s.", t_isig);
    INFO("Time for interactive partition refinement: %'0.2f s.", t_iref);
    INFO("");
    INFO("Number of iterations: %'zu.", iteration-1);
    INFO("Number of states before bisimulation minimisation: %'0.0f.", n_states);
    INFO("Number of blocks after bisimulation minimisation: %'zu.", n_blocks);

    mtbdd_unprotect(&markov_relation); // markov_relation object might be changed
    sylvan_deref(st_variables);
    sylvan_deref(sta_variables);
    sylvan_deref(ta_variables);
    sylvan_unprotect(&partition);
    sylvan_unprotect(&tau_transitions);
    sylvan_unprotect(&tau_states);

    return partition;
}

}
