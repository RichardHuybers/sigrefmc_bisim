/*
 * Copyright 2016 Tom van Dijk, Johannes Kepler University Linz
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

#include <cstddef> // to fix errors with gmp
#include <sylvan_int.h>
#include <sylvan_gmp.h>

#include <quotient.hpp>
#include <refine.h>
#include <blocks.h>
#include <sigref_util.hpp>

namespace sigref {

using namespace sylvan;

/*
 * Declarations for internal methods that implement minimization
 */

/**
 * Given two cubes of equal size for "from" state and "to" state, computes
 * the two cubes in interleaved s,t variables, ending with the given <tail>.
 */
TASK_DECL_4(MTBDD, cubes_to_st, MTBDD, MTBDD, MTBDD, int);
#define cubes_to_st(left, right, tail) CALL(cubes_to_st, left, right, tail, 0)

/**
 * The custom algorithm to minimize an interactive transition relation.
 * Translates s to s (encoded) and t to t (encoded) via block numbers.
 * Also removes tau steps if tau is not set to False but to the tau action.
 */
TASK_DECL_5(BDD, compute_trans_quotient, BDD, BDD, BDD, BDD, BDD);
#define compute_trans_quotient(dd, left, right, st_vars, tau) CALL(compute_trans_quotient, dd, left, right, st_vars, tau)

/**
 * Perform several steps for Markov computation in one step.
 * Before this: compute R(s,B) from R(s,t) and P(t,B)
 * Steps done here: R(s,B) -> R(s,B') -> R(B,B') -> R(s,t)
 *                       Rename   AndExistMax  Rename
 * The first part cannot be combined with the second part because the source block
 * is needed to distinguish transitions from different states for correct rate summation.
 *
 * Input dd: transition relation from state s to block B with <leaf> rate.
 * left: partition from state t to block B
 * s_vars: all s variables
 * map_b_to_t: mapping (for compose) from B to t
 * map_b_to_s: mapping (for compose) from B to s
 */
TASK_DECL_5(MTBDD, compute_markov_quotient, MTBDD, BDD, BDD, BDD, BDD);
#define compute_markov_quotient(dd, left, s_vars, map_b_to_t, map_b_to_s) CALL(compute_markov_quotient, dd, left, s_vars, map_b_to_t, map_b_to_s)

/**
 * Our custom algorithm to minimize a set of states.
 * dd: on variables s
 * partition: on variables t and B
 * s_vars: all variables s
 * map: map from B to s
 */
TASK_DECL_4(BDD, compute_states_quotient, BDD, BDD, BDD, BDD);
#define compute_states_quotient(dd, partition, s_vars, map) CALL(compute_states_quotient, dd, partition, s_vars, map)

/**
 * Wimmer's algorithm to minimize a Markov transition relation
 */
TASK_DECL_3(MTBDD, translate_markov, StateSystem&, MTBDD, BDD);
#define translate_markov(system, markov_trans, partition) CALL(translate_markov, system, markov_trans, partition)

/**
 * Wimmer's old algorithm to minimize an interactive transition relation
 */
TASK_DECL_4(MTBDD, translate_trans_1, LTS&, BDD, BDD, BDD);
#define translate_trans_1(system, trans, partition, tau) CALL(translate_trans_1, system, trans, partition, tau)

/**
 * Wimmer's improved algorithm to minimize an interactive transition relation
 */
TASK_DECL_4(MTBDD, translate_trans_2, LTS&, BDD, BDD, BDD);
#define translate_trans_2(system, trans, partition, tau) CALL(translate_trans_2, system, trans, partition, tau)

/**
 * Wimmer's algorithm to minimize a set of states
 */
TASK_DECL_3(BDD, translate_states, StateSystem&, BDD, BDD);
#define translate_states(system, states, partition) CALL(translate_states, system, states, partition)

/**
 * Print all states to stdout
 */
void enumerate_states(BDD states, BDD state_vars);

/**
 * Print all Markov transitions to stdout
 */
void enumerate_markov_transitions(MTBDD trans, StateSystem &system);

/**
 * Print the partition to stdout
 */
VOID_TASK_DECL_2(enumerate_partition, BDD, BDD);
#define enumerate_partition(partition, prime_vars) CALL(enumerate_partition, partition, prime_vars)

/*
 * Implementations for internal methods that implement minimization
 */

static BDD *block_encoding = NULL;
static int be_state_length;
static BDD be_state_variables;

/**
 * Helper function to pick a state for each block.
 */
VOID_TASK_2(partition_enum, MTBDD, dd, mtbdd_enum_trace_t, trace)
{
    if (dd == mtbdd_false) return;

    uint64_t result = 1;
    if (cache_get3(CACHE_PARTITION_ENUM, dd, 0, 0, &result)) return;
    cache_put3(CACHE_PARTITION_ENUM, dd, 0, 0, result);

    mtbddnode_t ndd = MTBDD_GETNODE(dd);
    uint32_t var = mtbddnode_getvariable(ndd);

    if (var >= block_base) {
        uint64_t block = CALL(decode_block, dd);

        uint8_t new_state[be_state_length];
        for (int i=0; i<be_state_length; i++) new_state[i] = 0;

        while (trace != NULL) {
            assert(trace->var % 2 == 1 && (trace->var-1)/2 < (unsigned int)be_state_length);
            if (trace->val) new_state[(trace->var-1)/2] = 1;
            trace = trace->prev;
        }

        if (block_encoding[block] == 0) {
            // don't bother with compare and swap
            block_encoding[block] = mtbdd_cube(be_state_variables, new_state, mtbdd_true);
        }

        return;
    }

    struct mtbdd_enum_trace t0 = (struct mtbdd_enum_trace){trace, var, 0};
    struct mtbdd_enum_trace t1 = (struct mtbdd_enum_trace){trace, var, 1};
    SPAWN(partition_enum, node_getlow(dd, ndd), &t0);
    CALL(partition_enum, node_gethigh(dd, ndd), &t1);
    SYNC(partition_enum);
}

/**
 * Helper callback (mtbdd_eval_compose_cb) to convert the partition
 * from block encoding to random-state encoding.
 */
TASK_1(MTBDD, convert_partition, MTBDD, block)
{
    if (block == mtbdd_false) return mtbdd_false;
    uint64_t block_number = CALL(decode_block, block);
    assert(block_number > 0 && block_number <= count_blocks());
    assert(block_encoding[block_number] != mtbdd_false);
    return block_encoding[block_number];
}

/**
 * Convert a partition from block encoding to random-state encoding.
 */
TASK_2(MTBDD, create_pick_partition, BDD, partition, BDD, t_vars)
{
    INFO("Picking a state for each block...");

    /* allocate some memory and prepare variables */
    size_t n_blocks = count_blocks();
    block_encoding = (BDD*)calloc(sizeof(BDD), n_blocks + 1);
    be_state_length = sylvan_set_count(t_vars);
    BDD tb_vars = sylvan_and(t_vars, block_variables);
    mtbdd_refs_push(tb_vars);

    /* create new state variables (using block number variables) */
    be_state_variables = mtbdd_true;
    for (int i=0; i<be_state_length; i++) {
        mtbdd_refs_push(be_state_variables);
        be_state_variables = mtbdd_makenode(block_base+2*(be_state_length-i-1), mtbdd_false, be_state_variables);
        mtbdd_refs_pop(1);
    }
    mtbdd_refs_push(be_state_variables);

    /* pick a random state for each block */
    CALL(partition_enum, partition, NULL);
    //mtbdd_enum_par(partition, TASK(partition_enum), NULL);

    mtbdd_refs_pop(2);  // be_state_variables, tb_vars

    /* set block info to new be_state info */
    block_length = be_state_length;
    sylvan_deref(block_variables);
    block_variables = be_state_variables;
    sylvan_ref(block_variables);

    INFO("Converting the partition...");

    /* convert partition */
    partition = mtbdd_eval_compose(partition, t_vars, TASK(convert_partition));
    mtbdd_refs_push(partition);

    free(block_encoding);

    return partition;
}

/**
 * Given two cubes of equal size for "from" state and "to" state, computes
 * the two cubes in interleaved s,t variables, ending with the given <tail>.
 *
 * This works for the "block encoding" and for the "random-state" encoding,
 * because they work with cubes of equal sizes.
 */
TASK_IMPL_4(MTBDD, cubes_to_st, MTBDD, left, MTBDD, right, MTBDD, tail, int, depth)
{
    /* expect left/right have same length */
    if (left == mtbdd_true) {
        assert(right == mtbdd_true);
        return tail;
    }

    assert(left != mtbdd_false && right != mtbdd_false && right != mtbdd_true);

    mtbddnode_t nleft = MTBDD_GETNODE(left);
    mtbddnode_t nright = MTBDD_GETNODE(right);

    /* determine if literals are in positive (1) or negative (0) form. */
    int leftval = node_low(left, nleft) == mtbdd_false ? 1 : 0;
    int rightval = node_low(right, nright) == mtbdd_false ? 1 : 0;

    /* get cofactors and perform recursive call */
    MTBDD subl = leftval ? node_high(left, nleft) : node_low(left, nleft);
    MTBDD subr = rightval ? node_high(right, nright) : node_low(right, nright);
    MTBDD res = CALL(cubes_to_st, subl, subr, tail, depth+1);

    /* compute result for this level */

    if (rightval) {
        res = mtbdd_makenode(2*depth+1, mtbdd_false, res);
    } else {
        res = mtbdd_makenode(2*depth+1, res, mtbdd_false);
    }

    if (leftval) {
        res = mtbdd_makenode(2*depth, mtbdd_false, res);
    } else {
        res = mtbdd_makenode(2*depth, res, mtbdd_false);
    }

    return res;
}

/**
 * Compute the quotient of an interactive transition relation in one step.
 * if tau is set to mtbdd_false, then tau self-loops are not removed.
 * This version uses block encoding.
 */
TASK_IMPL_5(BDD, compute_trans_quotient, BDD, dd, BDD, left, BDD, right, BDD, st_vars, BDD, tau)
{
    /* left follows source state, right follows target state */
    /* left/right defined on t and B, dd defined on s,t and then a or rate */
    /* variables order: s,t < a,B,rate */

    /* obviously, false becomes false */
    if (dd == mtbdd_false) return mtbdd_false;
    /* ignore states without a block */
    if (left == mtbdd_false || right == mtbdd_false) return mtbdd_false;

    uint32_t dd_var = dd != mtbdd_true ? sylvan_var(dd) : (uint32_t)-1;
    uint32_t left_var = sylvan_var(left);
    uint32_t right_var = sylvan_var(right);
    uint32_t top_var = dd_var < right_var ? dd_var : right_var;
    if ((left_var-1) < top_var) top_var = left_var-1;

    uint32_t var = mtbdd_set_first(st_vars);

    /* we can skip s/t variables because sylvan_or */
    while (var < top_var) {
        st_vars = mtbdd_set_next(st_vars);
        if (mtbdd_set_isempty(st_vars)) break;
        var = mtbdd_set_first(st_vars);
    }

    sylvan_gc_test();

    BDD result;
    /* assumption: st_vars does not change during quotient computation */
    if (cache_get3(CACHE_TRANS_QUOTIENT, dd, left, right, &result)) {
        return result;
    }

    if (mtbdd_set_isempty(st_vars)) {
        /* now left contains source block, right contains target block */
        assert(sylvan_var(dd) > 99999);

        result = dd;

        /* remove tau self-loops if tau is set */
        if (tau != mtbdd_false && left == right) {
            result = sylvan_and(result, sylvan_not(tau));
        }

        /* add cubes */
        /*
        uint64_t source = CALL(decode_block, left);
        uint64_t target = CALL(decode_block, right);

        for (int j=0; j<block_length; j++) {
            if (target & (1ULL<<(block_length-j-1))) {
                result = mtbdd_makenode((block_length-j-1)*2+1, mtbdd_false, result);
            } else {
                result = mtbdd_makenode((block_length-j-1)*2+1, result, mtbdd_false);
            }
            if (source & (1ULL<<(block_length-j-1))) {
                result = mtbdd_makenode((block_length-j-1)*2, mtbdd_false, result);
            } else {
                result = mtbdd_makenode((block_length-j-1)*2, result, mtbdd_false);
            }
        }
        */
        result = cubes_to_st(left, right, result);

        /* cache and return */
        cache_put3(CACHE_TRANS_QUOTIENT, dd, left, right, result);
        return result;
    }

    /* compute cofactors */
    BDD dd_low, dd_high;
    if (dd_var == var) {
        dd_low = sylvan_low(dd);
        dd_high = sylvan_high(dd);
    } else {
        dd_low = dd_high = dd;
    }

    /* match left t with s var */
    BDD left_low, left_high;
    if (left_var == var+1) {
        left_low = sylvan_low(left);
        left_high = sylvan_high(left);
    } else {
        left_low = left_high = left;
    }

    /* match right t with t var */
    BDD right_low, right_high;
    if (right_var == var) {
        right_low = sylvan_low(right);
        right_high = sylvan_high(right);
    } else {
        right_low = right_high = right;
    }

    /* compute recursive results */
    mtbdd_refs_spawn(SPAWN(compute_trans_quotient, dd_low, left_low, right_low, sylvan_set_next(st_vars), tau));
    BDD high = CALL(compute_trans_quotient, dd_high, left_high, right_high, sylvan_set_next(st_vars), tau);
    mtbdd_refs_push(high);
    BDD low = mtbdd_refs_sync(SYNC(compute_trans_quotient));
    mtbdd_refs_push(low);

    /*
     * Merge both branches with "or"; this is valid, as we can just take the union of
     * every Block -> Block -> Action we find.
     */

    result = sylvan_or(low, high);
    mtbdd_refs_pop(2);

    /* cache result */
    cache_put3(CACHE_TRANS_QUOTIENT, dd, left, right, result);

    return result;
}

/**
 * Perform several steps for Markov computation in one step.
 * Before this: compute R(s,B) from R(s,t) and P(t,B)
 * Steps done here: R(s,B) -> R(s,B') -> R(B,B') -> R(s,t)
 *                       Rename   AndExistMax  Rename
 *
 * Input dd: transition relation from state s to block B with <leaf> rate.
 * left: partition from state t to block B
 * s_vars: all s variables
 * map: mapping (for compose) from B to t
 */
TASK_IMPL_5(MTBDD, compute_markov_quotient, MTBDD, dd, BDD, left, BDD, s_vars, BDD, map_b_to_t, BDD, map_b_to_s)
{
    /* left follows source state, right follows target state */
    /* left/right defined on t and B, dd defined on s,t and then a or rate */
    /* variables order: s,t < a,B,rate */

    /* obviously, false becomes false */
    if (dd == mtbdd_false) return mtbdd_false;
    /* ignore states without a block */
    if (left == mtbdd_false) return mtbdd_false;

    /* skip variables in s */
    uint32_t dd_var = !mtbdd_isleaf(dd) ? sylvan_var(dd) : (uint32_t)-1;
    uint32_t left_var = sylvan_var(left);
    uint32_t top_var = ((left_var-1) < dd_var) ? left_var-1 : dd_var;
    uint32_t var = mtbdd_set_first(s_vars);

    /* we can skip s variables because max(x, x) = x */
    while (var < top_var) {
        s_vars = mtbdd_set_next(s_vars);
        if (mtbdd_set_isempty(s_vars)) break;
        var = mtbdd_set_first(s_vars);
    }

    sylvan_gc_test();

    BDD result;
    /* assume maps are stable */
    if (cache_get3(CACHE_MARKOV_QUOTIENT, dd, left, s_vars, &result)) {
        return result;
    }

    if (mtbdd_set_isempty(s_vars)) {
        /* now left contains single source block, dd contains target blocks to rate */

        /* rename single source block to s variables */
        MTBDD result = mtbdd_compose(left, map_b_to_s);
        mtbdd_refs_push(result);

        /* rename target blocks to t variables */
        MTBDD part = mtbdd_compose(dd, map_b_to_t);

        /* perform conjunction */
        mtbdd_refs_push(part);
        result = mtbdd_times(part, result);
        mtbdd_refs_pop(2);  // part, result

        /* cache and return */
        cache_put3(CACHE_MARKOV_QUOTIENT, dd, left, s_vars, result);
        return result;
    }

    BDD dd_low, dd_high;
    if (!mtbdd_isleaf(dd) && var == dd_var) {
        dd_low = sylvan_low(dd);
        dd_high = sylvan_high(dd);
    } else {
        dd_low = dd_high = dd;
    }

    /* match left t with s var */
    BDD left_low, left_high;
    if (var+1 == left_var) {
        left_low = sylvan_low(left);
        left_high = sylvan_high(left);
    } else {
        left_low = left_high = left;
    }

    /* compute recursive results */
    mtbdd_refs_spawn(SPAWN(compute_markov_quotient, dd_low, left_low, sylvan_set_next(s_vars), map_b_to_t, map_b_to_s));
    MTBDD high = CALL(compute_markov_quotient, dd_high, left_high, sylvan_set_next(s_vars), map_b_to_t, map_b_to_s);
    mtbdd_refs_push(high);
    MTBDD low = mtbdd_refs_sync(SYNC(compute_markov_quotient));
    mtbdd_refs_push(low);

    /* unprimed, so take the max */
    if (leaftype == 2) result = gmp_max(low, high);
    else result = mtbdd_max(low, high);

    mtbdd_refs_pop(2);  // low, high

    /* cache result */
    cache_put3(CACHE_MARKOV_QUOTIENT, dd, left, s_vars, result);

    return result;
}

/**
 * dd: on variables s
 * part: on variables t and B
 * s_vars: all variables s
 * map: map from B to s
 */
TASK_IMPL_4(BDD, compute_states_quotient, BDD, dd, BDD, part, BDD, s_vars, BDD, map)
{
    /* left follows source state, right follows target state */
    /* left/right defined on t and B, dd defined on s,t and then a or rate */
    /* variables order: s,t < a,B,rate */

    /* obviously, false becomes false */
    if (dd == mtbdd_false) return mtbdd_false;
    /* ignore states without a block */
    if (part == mtbdd_false) return mtbdd_false;

    uint32_t dd_var = dd != mtbdd_true ? sylvan_var(dd) : (uint32_t)-1;
    uint32_t part_var = sylvan_var(part);
    uint32_t top_var = dd_var < (part_var-1) ? dd_var : part_var-1;
    uint32_t var = mtbdd_set_first(s_vars);

    /* we can skip s/t variables because sylvan_or */
    while (var < top_var) {
        s_vars = mtbdd_set_next(s_vars);
        if (mtbdd_set_isempty(s_vars)) break;
        var = mtbdd_set_first(s_vars);
    }

    sylvan_gc_test();

    BDD result;
    /* assumption: st_vars does not change during quotient computation */
    if (cache_get3(CACHE_STATES_QUOTIENT, dd, part, s_vars, &result)) {
        return result;
    }

    if (mtbdd_set_isempty(s_vars)) {
        assert(dd == mtbdd_true);

        /* compute block in s variables */
        result = sylvan_compose(part, map);

        /* cache and return */
        cache_put3(CACHE_STATES_QUOTIENT, dd, part, s_vars, result);
        return result;
    }

    /* compute cofactors */
    BDD dd_low, dd_high;
    if (dd_var == var) {
        dd_low = sylvan_low(dd);
        dd_high = sylvan_high(dd);
    } else {
        dd_low = dd_high = dd;
    }

    /* match part t with s var */
    BDD part_low, part_high;
    if (part_var == var+1) {
        part_low = sylvan_low(part);
        part_high = sylvan_high(part);
    } else {
        part_low = part_high = part;
    }

    /* compute recursive results */
    mtbdd_refs_spawn(SPAWN(compute_states_quotient, dd_low, part_low, sylvan_set_next(s_vars), map));
    BDD high = CALL(compute_states_quotient, dd_high, part_high, sylvan_set_next(s_vars), map);
    mtbdd_refs_push(high);
    BDD low = mtbdd_refs_sync(SYNC(compute_states_quotient));
    mtbdd_refs_push(low);

    result = sylvan_or(low, high);
    mtbdd_refs_pop(2);

    /* cache result */
    cache_put3(CACHE_STATES_QUOTIENT, dd, part, s_vars, result);

    return result;
}

/**
 * Minimize a Markov transition relation using the same algorithm as Wimmer
 */
TASK_IMPL_3(MTBDD, translate_markov, StateSystem&, system, MTBDD, markov_trans, BDD, partition)
{
    /* markov_trans ::= (s, t) => Rate, partition ::= (t, B) */

    /* T(s, t) -> T(s, B) -> T(s, t) -> T(t, B) -> T(s, t) */

    /* r1 := \exists_sum t: T(s, t) \and P(t, B) */
    MTBDD r1;
    if (leaftype == 2) r1 = gmp_and_exists(markov_trans, partition, system.getVarT().GetBDD());
    else r1 = mtbdd_and_exists(markov_trans, partition, system.getVarT().GetBDD());
    mtbdd_refs_push(r1);

    /* r1 := r1[B -> t] */
    MTBDDMAP map = mtbdd_map_empty();
    for (int i=0; i<block_length; i++) {
        mtbdd_refs_push(map);
        map = mtbdd_map_add(map, block_base+2*(block_length-i-1), sylvan_ithvar((block_length-i-1)*2+1));
        mtbdd_refs_pop(1);
    }

    mtbdd_refs_push(map);
    r1 = mtbdd_compose(r1, map);
    mtbdd_refs_pop(2);
    mtbdd_refs_push(r1);

    /* ps := P(t, B)[t -> s] */
    BDD ps = swap_prime(partition);
    mtbdd_refs_push(ps);

    /* r1 := \exists_max s: T(s, t) \and P(s, B) */
    if (leaftype == 2) r1 = gmp_and_abstract_max(r1, ps, system.getVarS().GetBDD());
    else r1 = mtbdd_and_abstract_max(r1, ps, system.getVarS().GetBDD());
    mtbdd_refs_pop(2);
    mtbdd_refs_push(r1);

    /* r1 := r1[B -> s] */
    map = mtbdd_map_empty();
    for (int i=0; i<block_length; i++) {
        mtbdd_refs_push(map);
        map = mtbdd_map_add(map, block_base+2*(block_length-i-1), sylvan_ithvar((block_length-i-1)*2));
        mtbdd_refs_pop(1);
    }

    mtbdd_refs_push(map);
    r1 = mtbdd_compose(r1, map);
    mtbdd_refs_pop(2);

    return r1;
}

/**
 * Minimize an interactive transition relation using the same algorithm as Wimmer (variant 1)
 */
TASK_IMPL_4(MTBDD, translate_trans_1, LTS&, system, BDD, trans, BDD, partition, BDD, tau)
{
    /* trans ::= (s, t, a), partition ::= (t, B) */

    /* r1 := \exists t: T(s, t, a) \and P(t, B) */
    MTBDD r1 = sylvan_and_exists(trans, partition, system.getVarT().GetBDD());
    mtbdd_refs_push(r1);

    /* r1 := r1[B -> t] */
    MTBDDMAP map = mtbdd_map_empty();
    for (int i=0; i<block_length; i++) {
        mtbdd_refs_push(map);
        map = mtbdd_map_add(map, block_base+2*(block_length-i-1), sylvan_ithvar((block_length-i-1)*2+1));
        mtbdd_refs_pop(1);
    }

    mtbdd_refs_push(map);
    r1 = sylvan_compose(r1, map);
    mtbdd_refs_pop(2);
    mtbdd_refs_push(r1);

    /* ps := P(t, B)[t -> s] */
    BDD ps = swap_prime(partition);
    mtbdd_refs_push(ps);

    /* r1 := \exists s: T(s, t, a) \and P(s, B) */
    r1 = sylvan_and_exists(r1, ps, system.getVarS().GetBDD());
    mtbdd_refs_pop(2);
    mtbdd_refs_push(r1);

    /* r1 := r1[B -> s] */
    map = mtbdd_map_empty();
    for (int i=0; i<block_length; i++) {
        mtbdd_refs_push(map);
        map = mtbdd_map_add(map, block_base+2*(block_length-i-1), sylvan_ithvar((block_length-i-1)*2));
        mtbdd_refs_pop(1);
    }

    mtbdd_refs_push(map);
    r1 = sylvan_compose(r1, map);
    mtbdd_refs_pop(2);
    mtbdd_refs_push(r1);

    /* remove tau self-loops */
    if (tau != mtbdd_false) {
        BDD inerttau = tau;
        for (int i=0; i<block_length; i++) {
            BDD low = sylvan_makenode((block_length-i-1)*2+1, inerttau, sylvan_false);
            BDD high = sylvan_makenode((block_length-i-1)*2+1, sylvan_false, inerttau);
            inerttau = sylvan_makenode((block_length-i-1)*2, low, high);
        }
        mtbdd_refs_push(inerttau);
        r1 = sylvan_and(r1, sylvan_not(inerttau));
        mtbdd_refs_pop(1);
    }

    mtbdd_refs_pop(1);
    return r1;
}

/**
 * Minimize an interactive transition relation using the same algorithm as Wimmer (variant 2)
 */
TASK_IMPL_4(MTBDD, translate_trans_2, LTS&, system, BDD, trans, BDD, partition, BDD, tau)
{
    /* trans ::= (s, t, a), partition ::= (t, B) */

    /*
     * Wimmer's improved variant using two sets of block variables:
     * P(t,B') := rename P(s,B): s->t, B->B'
     * T(s,B',a) := and exist T, P
     * T(B,B',a) := and exist T, P(s,B)
     * T(s,t,a) := rename B->s, B'->t
     *
     * That version using our variable assignments:
     * T(s,B,a) := and exist T, P
     * T(t,B',a) := rename T: s->t, B->B'
     * T(B,B',a) := and exist T, P
     * T(s,t,a) := rename T: B->s, B'->t
     *
     * Small advantage here: no need to create copies of P... (but look at sizes of the transition relations!)
     */

    int state_length = sylvan_set_count(system.getVarS().GetBDD());

    /* r1 := \exists t: T(s, t, a) \and P(t, B) */
    MTBDD r1 = sylvan_and_exists(trans, partition, system.getVarT().GetBDD());

    /* r1 := r1[s->t, B -> B'] */
    MTBDDMAP map = mtbdd_map_empty();
    for (int i=0; i<block_length; i++) {
        map = mtbdd_map_add(map, block_base + 2*(block_length-i-1), sylvan_ithvar(block_base + 2*(block_length-i-1)+1));
    }
    for (int i=0; i<state_length; i++) {
        map = mtbdd_map_add(map, 2*(state_length-i-1), sylvan_ithvar(2*(state_length-i-1)+1));
    }

    r1 = sylvan_compose(r1, map);

    /* r1 := \exists s: T(t, a, B') \and P(t, B) */
    r1 = sylvan_and_exists(r1, partition, system.getVarT().GetBDD());

    /* r1 := r1[B -> s, B' -> t] */
    map = mtbdd_map_empty();
    for (int i=0; i<block_length; i++) {
        map = mtbdd_map_add(map, block_base+2*(block_length-i-1)+1, sylvan_ithvar((block_length-i-1)*2+1));
        map = mtbdd_map_add(map, block_base+2*(block_length-i-1), sylvan_ithvar((block_length-i-1)*2));
    }

    r1 = sylvan_compose(r1, map);

    /* remove tau self-loops */
    if (tau != mtbdd_false) {
        BDD inerttau = tau;
        for (int i=0; i<block_length; i++) {
            BDD low = sylvan_makenode((block_length-i-1)*2+1, inerttau, sylvan_false);
            BDD high = sylvan_makenode((block_length-i-1)*2+1, sylvan_false, inerttau);
            inerttau = sylvan_makenode((block_length-i-1)*2, low, high);
        }
        r1 = sylvan_and(r1, sylvan_not(inerttau));
    }

    return r1;
}

TASK_IMPL_3(BDD, translate_states, StateSystem&, system, BDD, states, BDD, partition)
{
    /* ps := P(s, B) */
    /* note that this step is probably free (in cache) */
    BDD ps = swap_prime(partition);
    mtbdd_refs_push(ps);

    /* r1 := \exists s: S(s) /\ P(s, B) */
    BDD r1 = sylvan_and_exists(states, ps, system.getVarS().GetBDD());
    mtbdd_refs_pop(1);
    mtbdd_refs_push(r1);

    /* r1 := r1[B -> s] */
    MTBDDMAP map = mtbdd_map_empty();
    for (int i=0; i<block_length; i++) {
        mtbdd_refs_push(map);
        map = mtbdd_map_add(map, block_base+2*(block_length-i-1), sylvan_ithvar((block_length-i-1)*2));
        mtbdd_refs_pop(1);
    }

    mtbdd_refs_push(map);
    r1 = mtbdd_compose(r1, map);
    mtbdd_refs_pop(2);

    /* r1 is now S(s) again, but s is encoded block */
    return r1;
}

/**
 * Trim unneeded block variables from the partition.
 */
TASK_IMPL_1(BDD, trim_block_variables, BDD, partition)
{
    INFO("Trimming unneeded block variables...");

    /*
     * compute new block length
     */
    int new_block_length = 0;
    size_t block_bits = count_blocks();  // highest number
    while (block_bits != 0) {
        new_block_length++;
        block_bits>>=1;
    }

    /*
     * update partition to lose excessive block variables
     */
    BDD constraint = mtbdd_true;
    for (int i=new_block_length; i<block_length; i++) {
        constraint = mtbdd_makenode(block_base+2*(new_block_length+block_length-i-1), constraint, mtbdd_false);
    }
    block_length = new_block_length;

    /*
     * create new block_variables
     */
    sylvan_deref(block_variables);
    block_variables = mtbdd_true;
    for (int i=0; i<block_length; i++) {
        block_variables = mtbdd_makenode(block_base+2*(block_length-i-1), mtbdd_false, block_variables);
    }
    sylvan_ref(block_variables);

    mtbdd_refs_push(constraint);
    partition = sylvan_constrain(partition, constraint);
    mtbdd_refs_pop(1);

    return partition;
}

/**
 * Compute the new state space for block encoding using a fast method.
 */
TASK_1(BDD, new_state_space, uint64_t, highest_block)
{
    /* block encoding is: first variable is lowest */

    // highest block: 101101
    // then everything EXCEPT  11****
    //                         10111*
    // i.e.                    ****11
    //                         *11101

    // highest block: 110001
    // then everything EXCEPT  111***
    //                         1101**
    //                         11001*
    // i.e.                    ***111
    //                         **1011
    //                         *10011

    // highest block: 100000
    // then everything EXCEPT  11****
    //                         101***
    //                         1001**
    //                         10001*
    //                         100001
    // i.e.                    ****11
    //                         ***101
    //                         **1001
    //                         *10001
    //                         100001

    BDD result = mtbdd_false;  // everything... except block 0
    for (int i=0; i<block_length; i++) {
        result = mtbdd_makenode(2*(block_length-i-1), result, mtbdd_true);
    }

    for (int i=0; i<block_length; i++) {
        if ((highest_block & (1ULL<<i)) == 0) {
            /* take all higher as they are, and set ith to "1" */
            BDD exception = mtbdd_true;
            for (int j=block_length-1; j>i; j--) {
                /* begin with highest */
                if (highest_block & (1ULL<<j)) {
                    exception = mtbdd_makenode(2*j, mtbdd_false, exception);
                } else {
                    exception = mtbdd_makenode(2*j, exception, mtbdd_false);
                }
            }
            /* set ith to "1" */
            exception = mtbdd_makenode(2*i, mtbdd_false, exception);
            result = sylvan_and(result, sylvan_not(exception));
        }
    }

    return result;
}

/**
 * Minimize a CTMC using standard BDD operations
 */
void Minimizations::minimize1(CTMC &ctmc, BDD partition)
{
    LACE_ME;

    INFO("");
    INFO("Computing new Markov transition relation (using standard operations)...");

    sylvan_stats_t s1;
    sylvan_stats_snapshot(&s1);

    double t1 = wctime();

    /* compute using standard operations */
    ctmc.markov_transitions = translate_markov(ctmc, ctmc.getMarkovTransitions().GetMTBDD(), partition);

    double t2 = wctime();

    sylvan_stats_t s2;
    sylvan_stats_snapshot(&s2);

    INFO("Computing new states, initial states, initial partition...");

    ctmc.initialStates = CALL(translate_states, ctmc, ctmc.getInitialStates().GetBDD(), partition);
    ctmc.states = CALL(new_state_space, count_blocks());

    int ip_size = ctmc.initialPartition.size();
    if (ip_size == 0) {
        /* do nothing */
    } else if (ip_size == 1) {
        ctmc.initialPartition[0] = ctmc.states;
    } else if (ip_size == 2) {
        /* only compute first block, then second block is the rest */
        Bdd first = ctmc.initialPartition[0];
        first = CALL(translate_states, ctmc, first.GetBDD(), partition);
        ctmc.initialPartition[0] = first;
        ctmc.initialPartition[1] = ctmc.states * !first;
    } else {
        /* translate each set of states */
        for (int i=0; i<ip_size; i++) {
            ctmc.initialPartition[i] = CALL(translate_states, ctmc, ctmc.initialPartition[i].GetBDD(), partition);
        }
    }

    /* recreate variable sets */
    MTBDD state_vars = mtbdd_true;
    MTBDD prime_vars = mtbdd_true;
    for (int i=0; i<block_length; i++) {
        mtbdd_refs_push(state_vars);
        mtbdd_refs_push(prime_vars);
        state_vars = mtbdd_set_add(state_vars, (block_length-i-1)*2);
        prime_vars = mtbdd_set_add(prime_vars, (block_length-i-1)*2+1);
        mtbdd_refs_pop(2);  // state_vars, prime_vars
    }
    ctmc.varS = state_vars;
    ctmc.varT = prime_vars;

    sylvan_stats_t s3;
    sylvan_stats_snapshot(&s3);

    /* report times */
    INFO("");
    INFO("Time for computing the quotient of the transition relation: %'0.2f sec.", t2-t1);

    /* report number of created/reused nodes */
    {
        size_t created_nodes = s2.counters[BDD_NODES_CREATED] - s1.counters[BDD_NODES_CREATED];
        size_t reused_nodes = s2.counters[BDD_NODES_REUSED] - s1.counters[BDD_NODES_REUSED];
        INFO("Number of MTBDD nodes created: %'zu. (%'zu new, %'zu reused)", created_nodes + reused_nodes, created_nodes, reused_nodes);
        if (verbosity >= 1) {
            size_t created_nodes = s3.counters[BDD_NODES_CREATED] - s2.counters[BDD_NODES_CREATED];
            size_t reused_nodes = s3.counters[BDD_NODES_REUSED] - s2.counters[BDD_NODES_REUSED];
            INFO("Number of MTBDD nodes created: %'zu (%'zu new, %'zu reused).", created_nodes + reused_nodes, created_nodes, reused_nodes);
        }
    }

    /* report sizes of new ctmc */
    {
        MTBDD trans = ctmc.markov_transitions.GetMTBDD();
        double trans_count = mtbdd_satcount(trans, block_length * 2);
        size_t node_count = mtbdd_nodecount(trans);
        INFO("New Markov transition relation: %'0.0f transitions, %'zu MTBDD nodes.", trans_count, node_count);
        if (verbosity >= 1) {
            INFO("New initial states: %'0.0f states, %'zu MTBDD nodes.", mtbdd_satcount(ctmc.initialStates.GetBDD(), block_length), mtbdd_nodecount(ctmc.initialStates.GetBDD()));
            INFO("New states: %'0.0f states, %'zu MTBDD nodes.", mtbdd_satcount(ctmc.states.GetBDD(), block_length), mtbdd_nodecount(ctmc.states.GetBDD()));
            int ip_size = ctmc.initialPartition.size();
            for (int i=0; i<ip_size; i++) {
                INFO("New initial partition [%d]: %'0.0f states, %'zu MTBDD nodes.", i, mtbdd_satcount(ctmc.initialPartition[i].GetBDD(), block_length), mtbdd_nodecount(ctmc.initialPartition[i].GetBDD()));
            }
        }
    }
}

void Minimizations::minimize1(LTS& lts, BDD partition, int improved)
{
    LACE_ME;

    INFO("");
    INFO("Computing new interactive transition relations (using standard operations)...");

    sylvan_stats_t s1;
    sylvan_stats_snapshot(&s1);

    double t1 = wctime();

    /* obtain transition relations */
    std::vector<std::pair<Bdd,Bdd>> transitions = lts.getTransitions();
    int n_relations = transitions.size();
    BDD trans[n_relations];

    /* get tau if branching bisimulation */
    BDD tau = bisimulation == 1 ? lts.getTau().GetBDD() : mtbdd_false;

    /* translate all relations */
    for (int i=0; i<n_relations; i++) {
        int state_length = sylvan_set_count(lts.getVarS().GetBDD());
        trans[i] = transitions[i].first.GetBDD();
        int actual_state_length = sylvan_set_count(transitions[i].second.GetBDD());
        if (state_length*2 != actual_state_length) {
            /* extend the domain of the relation if needed */
            trans[i] = CALL(extend_relation, trans[i], transitions[i].second.GetBDD(), state_length);
        }
        mtbdd_refs_push(trans[i]);
        if (!improved) {
            /* use first algorithm */
            trans[i] = translate_trans_1(lts, trans[i], partition, tau);
        } else {
            /* use improved algorithm */
            trans[i] = translate_trans_2(lts, trans[i], partition, tau);
        }
        mtbdd_refs_pop(1);
        mtbdd_refs_push(trans[i]);
    }

    double t2 = wctime();

    sylvan_stats_t s2;
    sylvan_stats_snapshot(&s2);

    INFO("Computing new states, initial states, inital partition...");

    lts.initialStates = CALL(translate_states, lts, lts.getInitialStates().GetBDD(), partition);
    lts.states = CALL(new_state_space, count_blocks());

    int ip_size = lts.initialPartition.size();
    if (ip_size == 0) {
        /* do nothing */
    } else if (ip_size == 1) {
        lts.initialPartition[0] = lts.states;
    } else if (ip_size == 2) {
        /* only compute first block, then second block is the rest */
        Bdd first = lts.initialPartition[0];
        first = CALL(translate_states, lts, first.GetBDD(), partition);
        lts.initialPartition[0] = first;
        lts.initialPartition[1] = lts.states * !first;
    } else {
        /* translate each set of states */
        for (int i=0; i<ip_size; i++) {
            lts.initialPartition[i] = CALL(translate_states, lts, lts.initialPartition[i].GetBDD(), partition);
        }
    }

    /* recreate variable sets */
    MTBDD state_vars = mtbdd_true;
    MTBDD prime_vars = mtbdd_true;
    MTBDD st_vars = mtbdd_true;
    for (int i=0; i<block_length; i++) {
        mtbdd_refs_push(state_vars);
        mtbdd_refs_push(prime_vars);
        mtbdd_refs_push(st_vars);
        state_vars = mtbdd_set_add(state_vars, (block_length-i-1)*2);
        prime_vars = mtbdd_set_add(prime_vars, (block_length-i-1)*2+1);
        st_vars = mtbdd_set_add(st_vars, (block_length-i-1)*2+1);
        mtbdd_refs_push(st_vars);
        st_vars = mtbdd_set_add(st_vars, (block_length-i-1)*2);
        mtbdd_refs_pop(4);  // state_vars, prime_vars, two times st_vars
    }
    lts.varS = state_vars;
    lts.varT = prime_vars;

    for (int i=0; i<n_relations; i++) {
        lts.transitions[i].first = trans[i];
        lts.transitions[i].second = st_vars;
    }
    mtbdd_refs_pop(n_relations);

    sylvan_stats_t s3;
    sylvan_stats_snapshot(&s3);

    /* report times */
    INFO("");
    INFO("Time for computing the quotient of the transition relation: %'0.2f sec.", t2-t1);

    /* report number of created/reused nodes */
    {
        size_t created_nodes = s2.counters[BDD_NODES_CREATED] - s1.counters[BDD_NODES_CREATED];
        size_t reused_nodes = s2.counters[BDD_NODES_REUSED] - s1.counters[BDD_NODES_REUSED];
        INFO("Number of MTBDD nodes created: %'zu. (%'zu new, %'zu reused)", created_nodes + reused_nodes, created_nodes, reused_nodes);
        if (verbosity >= 1) {
            size_t created_nodes = s3.counters[BDD_NODES_CREATED] - s2.counters[BDD_NODES_CREATED];
            size_t reused_nodes = s3.counters[BDD_NODES_REUSED] - s2.counters[BDD_NODES_REUSED];
            INFO("Number of MTBDD nodes created: %'zu. (%'zu new, %'zu reused)", created_nodes + reused_nodes, created_nodes, reused_nodes);
        }
    }

    /* report sizes of new lts */
    {
        int action_length = sylvan_set_count(lts.getVarA().GetBDD());
        double trans_count = 0;
        for (int i=0; i<n_relations; i++) trans_count += mtbdd_satcount(trans[i], block_length * 2 + action_length);
        size_t node_count = mtbdd_nodecount_more(trans, n_relations);
        INFO("New interactive transition relation: %'0.0f transitions, %'zu MTBDD nodes.", trans_count, node_count);
    }
}

/**
 * Minimize an IMC using standard BDD operations
 */
void Minimizations::minimize1(IMC &imc, BDD partition, int improved)
{
    LACE_ME;

    INFO("");
    INFO("Computing new Markov transition relation (using standard operations)...");

    sylvan_stats_t s1;
    sylvan_stats_snapshot(&s1);

    double t1 = wctime();

    /* compute using standard operations */
    imc.markov_transitions = translate_markov(imc, imc.getMarkovTransitions().GetMTBDD(), partition);

    INFO("Computing new interactive transition relations (using standard operations)...");

    /* obtain transition relations */
    std::vector<std::pair<Bdd,Bdd>> transitions = imc.getTransitions();
    int n_relations = transitions.size();
    BDD trans[n_relations];

    /* get tau if branching bisimulation */
    BDD tau = bisimulation == 1 ? imc.getTau().GetBDD() : mtbdd_false;

    /* translate all relations */
    for (int i=0; i<n_relations; i++) {
        int state_length = sylvan_set_count(imc.getVarS().GetBDD());
        trans[i] = transitions[i].first.GetBDD();
        int actual_state_length = sylvan_set_count(transitions[i].second.GetBDD());
        if (state_length*2 != actual_state_length) {
            /* extend the domain of the relation if needed */
            trans[i] = CALL(extend_relation, trans[i], transitions[i].second.GetBDD(), state_length);
        }
        mtbdd_refs_push(trans[i]);
        if (!improved) {
            /* use first algorithm */
            trans[i] = translate_trans_1(imc, trans[i], partition, tau);
        } else {
            /* use improved algorithm */
            trans[i] = translate_trans_2(imc, trans[i], partition, tau);
        }
        mtbdd_refs_pop(1);
        mtbdd_refs_push(trans[i]);
    }

    double t2 = wctime();

    sylvan_stats_t s2;
    sylvan_stats_snapshot(&s2);

    INFO("Computing new states, initial states, initial partition...");

    imc.initialStates = CALL(translate_states, imc, imc.getInitialStates().GetBDD(), partition);
    imc.states = CALL(new_state_space, count_blocks());

    int ip_size = imc.initialPartition.size();
    if (ip_size == 0) {
        /* do nothing */
    } else if (ip_size == 1) {
        imc.initialPartition[0] = imc.states;
    } else if (ip_size == 2) {
        /* only compute first block, then second block is the rest */
        Bdd first = imc.initialPartition[0];
        first = CALL(translate_states, imc, first.GetBDD(), partition);
        imc.initialPartition[0] = first;
        imc.initialPartition[1] = imc.states * !first;
    } else {
        /* translate each set of states */
        for (int i=0; i<ip_size; i++) {
            imc.initialPartition[i] = CALL(translate_states, imc, imc.initialPartition[i].GetBDD(), partition);
        }
    }

    /* recreate variable sets */
    MTBDD state_vars = mtbdd_true;
    MTBDD prime_vars = mtbdd_true;
    MTBDD st_vars = mtbdd_true;
    for (int i=0; i<block_length; i++) {
        state_vars = mtbdd_set_add(state_vars, (block_length-i-1)*2);
        prime_vars = mtbdd_set_add(prime_vars, (block_length-i-1)*2+1);
        st_vars = mtbdd_set_add(st_vars, (block_length-i-1)*2+1);
        st_vars = mtbdd_set_add(st_vars, (block_length-i-1)*2);
    }
    imc.varS = state_vars;
    imc.varT = prime_vars;

    for (int i=0; i<n_relations; i++) {
        imc.transitions[i].first = trans[i];
        imc.transitions[i].second = st_vars;
    }
    mtbdd_refs_pop(n_relations);

    sylvan_stats_t s3;
    sylvan_stats_snapshot(&s3);

    /* report times */
    INFO("");
    INFO("Time for computing the quotient of the transition relation: %'0.2f sec.", t2-t1);

    /* report number of created/reused nodes */
    {
        size_t created_nodes = s2.counters[BDD_NODES_CREATED] - s1.counters[BDD_NODES_CREATED];
        size_t reused_nodes = s2.counters[BDD_NODES_REUSED] - s1.counters[BDD_NODES_REUSED];
        INFO("Number of MTBDD nodes created: %'zu. (%'zu new, %'zu reused)", created_nodes + reused_nodes, created_nodes, reused_nodes);
        if (verbosity >= 1) {
            size_t created_nodes = s3.counters[BDD_NODES_CREATED] - s2.counters[BDD_NODES_CREATED];
            size_t reused_nodes = s3.counters[BDD_NODES_REUSED] - s2.counters[BDD_NODES_REUSED];
            INFO("Number of MTBDD nodes created: %'zu. (%'zu new, %'zu reused)", created_nodes + reused_nodes, created_nodes, reused_nodes);
        }
    }

    /* report data */
    {
        MTBDD trans = imc.markov_transitions.GetMTBDD();
        double trans_count = mtbdd_satcount(trans, block_length * 2);
        size_t node_count = mtbdd_nodecount(trans);
        INFO("New Markov transition relation: %'0.0f transitions, %'zu MTBDD nodes.", trans_count, node_count);
    }

    {
        int action_length = sylvan_set_count(imc.getVarA().GetBDD());
        double trans_count = 0;
        for (int i=0; i<n_relations; i++) trans_count += mtbdd_satcount(trans[i], block_length * 2 + action_length);
        size_t node_count = mtbdd_nodecount_more(trans, n_relations);
        INFO("New interactive transition relation: %'0.0f transitions, %'zu MTBDD nodes.", trans_count, node_count);
    }
}

void Minimizations::minimize2(CTMC &ctmc, BDD partition)
{
    LACE_ME;

    INFO("");
    INFO("Computing new Markov transition relation (using custom operations)...");

    sylvan_stats_t s1;
    sylvan_stats_snapshot(&s1);

    double t1 = wctime();

    /* create [B -> t] */
    MTBDDMAP map_b_to_t = mtbdd_map_empty();
    for (int i=0; i<block_length; i++) {
        mtbdd_refs_push(map_b_to_t);
        map_b_to_t = mtbdd_map_add(map_b_to_t, block_base+2*(block_length-i-1), sylvan_ithvar(2*(block_length-i-1)+1));
        mtbdd_refs_pop(1);
    }
    mtbdd_refs_push(map_b_to_t);

    /* create [B -> s] */
    MTBDDMAP map_b_to_s = mtbdd_map_empty();
    for (int i=0; i<block_length; i++) {
        mtbdd_refs_push(map_b_to_s);
        map_b_to_s = mtbdd_map_add(map_b_to_s, block_base+2*(block_length-i-1), sylvan_ithvar((block_length-i-1)*2));
        mtbdd_refs_pop(1);
    }
    mtbdd_refs_push(map_b_to_s);

    /* translate the Markov relation */
    MTBDD trans = ctmc.getMarkovTransitions().GetMTBDD();

    /* step 1: compute R(s,B) using AndAbstractPlus */
    // INFO("Step 1/2...");
    if (leaftype == 2) trans = gmp_and_exists(trans, partition, ctmc.getVarT().GetBDD());
    else trans = mtbdd_and_exists(trans, partition, ctmc.getVarT().GetBDD());
    mtbdd_refs_push(trans);

    /* step 2: compute R(s,t) result in one step */
    // INFO("Step 2/2...");
    trans = compute_markov_quotient(trans, partition, ctmc.getVarS().GetBDD(), map_b_to_t, map_b_to_s);
    ctmc.markov_transitions = trans;
    mtbdd_refs_pop(1);  // trans

    double t2 = wctime();

    sylvan_stats_t s2;
    sylvan_stats_snapshot(&s2);

    INFO("Computing new states, initial states, initial partition...");

    BDD state_vars = ctmc.getVarS().GetBDD();
    ctmc.initialStates = compute_states_quotient(ctmc.getInitialStates().GetBDD(), partition, state_vars, map_b_to_s);
    ctmc.states = CALL(new_state_space, count_blocks());

    int ip_size = ctmc.initialPartition.size();
    if (ip_size == 0) {
        /* do nothing */
    } else if (ip_size == 1) {
        ctmc.initialPartition[0] = ctmc.states;
    } else if (ip_size == 2) {
        /* only compute first block, then second block is the rest */
        Bdd first = ctmc.initialPartition[0];
        first = compute_states_quotient(first.GetBDD(), partition, state_vars, map_b_to_s);
        ctmc.initialPartition[0] = first;
        ctmc.initialPartition[1] = ctmc.states * !first;
    } else {
        /* translate each set of states */
        for (int i=0; i<ip_size; i++) {
            ctmc.initialPartition[i] = compute_states_quotient(ctmc.initialPartition[i].GetBDD(), partition, state_vars, map_b_to_s);
        }
    }

    mtbdd_refs_pop(2);  // map_b_to_t, map_b_to_s

    /* recreate variable sets */
    {
        MTBDD state_vars = mtbdd_true;
        MTBDD prime_vars = mtbdd_true;
        for (int i=0; i<block_length; i++) {
            mtbdd_refs_push(state_vars);
            mtbdd_refs_push(prime_vars);
            state_vars = mtbdd_set_add(state_vars, (block_length-i-1)*2);
            prime_vars = mtbdd_set_add(prime_vars, (block_length-i-1)*2+1);
            mtbdd_refs_pop(2);  // state_vars, prime_vars
        }
        ctmc.varS = state_vars;
        ctmc.varT = prime_vars;
    }

    sylvan_stats_t s3;
    sylvan_stats_snapshot(&s3);

    /* report times */
    INFO("");
    INFO("Time for computing the quotient of the transition relation: %'0.2f sec.", t2-t1);

    /* report number of created/reused nodes */
    {
        size_t created_nodes = s2.counters[BDD_NODES_CREATED] - s1.counters[BDD_NODES_CREATED];
        size_t reused_nodes = s2.counters[BDD_NODES_REUSED] - s1.counters[BDD_NODES_REUSED];
        INFO("Number of MTBDD nodes created: %'zu. (%'zu new, %'zu reused)", created_nodes + reused_nodes, created_nodes, reused_nodes);
        if (verbosity >= 1) {
            size_t created_nodes = s3.counters[BDD_NODES_CREATED] - s2.counters[BDD_NODES_CREATED];
            size_t reused_nodes = s3.counters[BDD_NODES_REUSED] - s2.counters[BDD_NODES_REUSED];
            INFO("Number of MTBDD nodes created: %'zu. (%'zu new, %'zu reused)", created_nodes + reused_nodes, created_nodes, reused_nodes);
        }
    }

    /* report data */
    {
        MTBDD trans = ctmc.markov_transitions.GetMTBDD();
        double trans_count = mtbdd_satcount(trans, block_length * 2);
        size_t node_count = mtbdd_nodecount(trans);
        INFO("New Markov transition relation: %'0.0f transitions, %'zu MTBDD nodes.", trans_count, node_count);
        if (verbosity >= 1) {
            INFO("New initial states: %'0.0f states, %'zu MTBDD nodes.", mtbdd_satcount(ctmc.initialStates.GetBDD(), block_length), mtbdd_nodecount(ctmc.initialStates.GetBDD()));
            INFO("New states: %'0.0f states, %'zu MTBDD nodes.", mtbdd_satcount(ctmc.states.GetBDD(), block_length), mtbdd_nodecount(ctmc.states.GetBDD()));
            int ip_size = ctmc.initialPartition.size();
            for (int i=0; i<ip_size; i++) {
                INFO("New initial partition [%d]: %'0.0f states, %'zu MTBDD nodes.", i, mtbdd_satcount(ctmc.initialPartition[i].GetBDD(), block_length), mtbdd_nodecount(ctmc.initialPartition[i].GetBDD()));
            }
        }
    }
}

void Minimizations::minimize2(LTS& lts, BDD partition)
{
    LACE_ME;

    INFO("");
    INFO("Computing new interactive transition relations (using custom operations)...");

    sylvan_stats_t s1;
    sylvan_stats_snapshot(&s1);

    double t1 = wctime();

    /* obtain transition relations */
    std::vector<std::pair<Bdd,Bdd>> transitions = lts.getTransitions();
    int n_relations = transitions.size();
    BDD trans[n_relations];

    /* get tau if branching bisimulation */
    BDD tau = bisimulation == 1 ? lts.getTau().GetBDD() : mtbdd_false;

    BDD st_vars = (lts.getVarS() * lts.getVarT()).GetBDD();

    /* translate all relations */
    for (int i=0; i<n_relations; i++) {
        int state_length = sylvan_set_count(lts.getVarS().GetBDD());
        trans[i] = transitions[i].first.GetBDD();
        int actual_state_length = sylvan_set_count(transitions[i].second.GetBDD());
        if (state_length*2 != actual_state_length) {
            /* extend the domain of the relation if needed */
            trans[i] = CALL(extend_relation, trans[i], transitions[i].second.GetBDD(), state_length);
        }
        mtbdd_refs_push(trans[i]);
        trans[i] = CALL(compute_trans_quotient, trans[i], partition, partition, st_vars, tau);
        mtbdd_refs_pop(1);
        mtbdd_refs_push(trans[i]);
    }

    double t2 = wctime();

    sylvan_stats_t s2;
    sylvan_stats_snapshot(&s2);

    INFO("Computing new states, initial states, initial partition...");

    /* create [B -> s] */
    MTBDD map = mtbdd_map_empty();
    for (int i=0; i<block_length; i++) {
        mtbdd_refs_push(map);
        map = mtbdd_map_add(map, block_base+2*(block_length-i-1), sylvan_ithvar((block_length-i-1)*2));
        mtbdd_refs_pop(1);
    }
    mtbdd_refs_push(map);

    {
        BDD state_vars = lts.getVarS().GetBDD();
        lts.initialStates = compute_states_quotient(lts.getInitialStates().GetBDD(), partition, state_vars, map);
        lts.states = CALL(new_state_space, count_blocks());

        int ip_size = lts.initialPartition.size();
        if (ip_size == 0) {
            /* do nothing */
        } else if (ip_size == 1) {
            lts.initialPartition[0] = lts.states;
        } else if (ip_size == 2) {
            /* only compute first block, then second block is the rest */
            Bdd first = lts.initialPartition[0];
            first = compute_states_quotient(first.GetBDD(), partition, state_vars, map);
            lts.initialPartition[0] = first;
            lts.initialPartition[1] = lts.states * !first;
        } else {
            /* translate each set of states */
            for (int i=0; i<ip_size; i++) {
                lts.initialPartition[i] = compute_states_quotient(lts.initialPartition[i].GetBDD(), partition, state_vars, map);
            }
        }
    }

    /* recreate variable sets */
    {
        MTBDD state_vars = mtbdd_true;
        MTBDD prime_vars = mtbdd_true;
        MTBDD st_vars = mtbdd_true;
        for (int i=0; i<block_length; i++) {
            mtbdd_refs_push(state_vars);
            mtbdd_refs_push(prime_vars);
            mtbdd_refs_push(st_vars);
            state_vars = mtbdd_set_add(state_vars, (block_length-i-1)*2);
            prime_vars = mtbdd_set_add(prime_vars, (block_length-i-1)*2+1);
            st_vars = mtbdd_set_add(st_vars, (block_length-i-1)*2+1);
            mtbdd_refs_push(st_vars);
            st_vars = mtbdd_set_add(st_vars, (block_length-i-1)*2);
            mtbdd_refs_pop(4);  // state_vars, prime_vars, two times st_vars
        }
        lts.varS = state_vars;
        lts.varT = prime_vars;

        for (int i=0; i<n_relations; i++) {
            lts.transitions[i].first = trans[i];
            lts.transitions[i].second = st_vars;
        }
        mtbdd_refs_pop(n_relations);
    }

    sylvan_stats_t s3;
    sylvan_stats_snapshot(&s3);

    /* report times */
    INFO("");
    INFO("Time for computing the quotient of the transition relation: %'0.2f sec.", t2-t1);

    /* report number of created/reused nodes */
    {
        size_t created_nodes = s2.counters[BDD_NODES_CREATED] - s1.counters[BDD_NODES_CREATED];
        size_t reused_nodes = s2.counters[BDD_NODES_REUSED] - s1.counters[BDD_NODES_REUSED];
        INFO("Number of MTBDD nodes created: %'zu. (%'zu new, %'zu reused)", created_nodes + reused_nodes, created_nodes, reused_nodes);
        if (verbosity >= 1) {
            size_t created_nodes = s3.counters[BDD_NODES_CREATED] - s2.counters[BDD_NODES_CREATED];
            size_t reused_nodes = s3.counters[BDD_NODES_REUSED] - s2.counters[BDD_NODES_REUSED];
            INFO("Number of MTBDD nodes created: %'zu. (%'zu new, %'zu reused)", created_nodes + reused_nodes, created_nodes, reused_nodes);
        }
    }

    /* report data */
    {
        int action_length = sylvan_set_count(lts.getVarA().GetBDD());
        double trans_count = 0;
        for (int i=0; i<n_relations; i++) trans_count += mtbdd_satcount(trans[i], block_length * 2 + action_length);
        size_t node_count = mtbdd_nodecount_more(trans, n_relations);
        INFO("New interactive transition relation: %'0.0f transitions, %'zu MTBDD nodes.", trans_count, node_count);
    }
}

void Minimizations::minimize2(IMC &imc, BDD partition)
{
    LACE_ME;

    INFO("");
    INFO("Computing new Markov transition relation (using custom operations)...");

    sylvan_stats_t s1;
    sylvan_stats_snapshot(&s1);

    double t1 = wctime();

    /* create [B -> t] */
    MTBDDMAP map_b_to_t = mtbdd_map_empty();
    for (int i=0; i<block_length; i++) {
        mtbdd_refs_push(map_b_to_t);
        map_b_to_t = mtbdd_map_add(map_b_to_t, block_base+2*(block_length-i-1), sylvan_ithvar(2*(block_length-i-1)+1));
        mtbdd_refs_pop(1);
    }
    mtbdd_refs_push(map_b_to_t);

    /* create [B -> s] */
    MTBDDMAP map_b_to_s = mtbdd_map_empty();
    for (int i=0; i<block_length; i++) {
        mtbdd_refs_push(map_b_to_s);
        map_b_to_s = mtbdd_map_add(map_b_to_s, block_base+2*(block_length-i-1), sylvan_ithvar((block_length-i-1)*2));
        mtbdd_refs_pop(1);
    }
    mtbdd_refs_push(map_b_to_s);

    {
        /* translate the Markov relation */

        /* step 1: compute R(s,B) using AndAbstractPlus */
        // INFO("Step 1/2...");
        MTBDD trans = imc.getMarkovTransitions().GetMTBDD();
        if (leaftype == 2) trans = gmp_and_exists(trans, partition, imc.getVarT().GetBDD());
        else trans = mtbdd_and_exists(trans, partition, imc.getVarT().GetBDD());
        mtbdd_refs_push(trans);

        /* step 2: compute R(s,t) result in one step */
        // INFO("Step 2/2...");
        trans = compute_markov_quotient(trans, partition, imc.getVarS().GetBDD(), map_b_to_t, map_b_to_s);
        imc.markov_transitions = trans;
        mtbdd_refs_pop(1);  // trans
    }

    INFO("Computing new interactive transition relations (using custom operations)...");
    int n_relations;

    {
        /* obtain transition relations */
        std::vector<std::pair<Bdd,Bdd>> transitions = imc.getTransitions();
        n_relations = transitions.size();
        BDD trans[n_relations];

        /* get tau if branching bisimulation */
        BDD tau = bisimulation == 1 ? imc.getTau().GetBDD() : mtbdd_false;

        BDD st_vars = (imc.getVarS() * imc.getVarT()).GetBDD();

        /* translate all relations */
        for (int i=0; i<n_relations; i++) {
            int state_length = sylvan_set_count(imc.getVarS().GetBDD());
            trans[i] = transitions[i].first.GetBDD();
            int actual_state_length = sylvan_set_count(transitions[i].second.GetBDD());
            if (state_length*2 != actual_state_length) {
                /* extend the domain of the relation if needed */
                trans[i] = CALL(extend_relation, trans[i], transitions[i].second.GetBDD(), state_length);
            }
            mtbdd_refs_push(trans[i]);
            imc.transitions[i].first = CALL(compute_trans_quotient, trans[i], partition, partition, st_vars, tau);
            mtbdd_refs_pop(1);
        }
    }

    double t2 = wctime();

    sylvan_stats_t s2;
    sylvan_stats_snapshot(&s2);

    {
        INFO("Computing new states, initial states, initial partition...");

        {
            BDD state_vars = imc.getVarS().GetBDD();
            imc.initialStates = compute_states_quotient(imc.getInitialStates().GetBDD(), partition, state_vars, map_b_to_s);
            imc.states = CALL(new_state_space, count_blocks());

            int ip_size = imc.initialPartition.size();
            if (ip_size == 0) {
                /* do nothing */
            } else if (ip_size == 1) {
                imc.initialPartition[0] = imc.states;
            } else if (ip_size == 2) {
                /* only compute first block, then second block is the rest */
                Bdd first = imc.initialPartition[0];
                first = compute_states_quotient(first.GetBDD(), partition, state_vars, map_b_to_s);
                imc.initialPartition[0] = first;
                imc.initialPartition[1] = imc.states * !first;
            } else {
                /* translate each set of states */
                for (int i=0; i<ip_size; i++) {
                    imc.initialPartition[i] = compute_states_quotient(imc.initialPartition[i].GetBDD(), partition, state_vars, map_b_to_s);
                }
            }
        }
    }

    /* recreate variable sets */
    {
        MTBDD state_vars = mtbdd_true;
        MTBDD prime_vars = mtbdd_true;
        MTBDD st_vars = mtbdd_true;
        for (int i=0; i<block_length; i++) {
            state_vars = mtbdd_set_add(state_vars, (block_length-i-1)*2);
            prime_vars = mtbdd_set_add(prime_vars, (block_length-i-1)*2+1);
            st_vars = mtbdd_set_add(st_vars, (block_length-i-1)*2+1);
            st_vars = mtbdd_set_add(st_vars, (block_length-i-1)*2);
        }
        imc.varS = state_vars;
        imc.varT = prime_vars;

        for (int i=0; i<n_relations; i++) {
            imc.transitions[i].second = st_vars;
        }
        mtbdd_refs_pop(n_relations);
    }

    sylvan_stats_t s3;
    sylvan_stats_snapshot(&s3);

    mtbdd_refs_pop(2);  // map_b_to_t, map_b_to_s

    /* report times */
    INFO("");
    INFO("Time for computing the quotient of the transition relation: %'0.2f sec.", t2-t1);

    /* report number of created/reused nodes */
    {
        size_t created_nodes = s2.counters[BDD_NODES_CREATED] - s1.counters[BDD_NODES_CREATED];
        size_t reused_nodes = s2.counters[BDD_NODES_REUSED] - s1.counters[BDD_NODES_REUSED];
        INFO("Number of MTBDD nodes created: %'zu. (%'zu new, %'zu reused)", created_nodes + reused_nodes, created_nodes, reused_nodes);
        if (verbosity >= 1) {
            size_t created_nodes = s3.counters[BDD_NODES_CREATED] - s2.counters[BDD_NODES_CREATED];
            size_t reused_nodes = s3.counters[BDD_NODES_REUSED] - s2.counters[BDD_NODES_REUSED];
            INFO("Number of MTBDD nodes created: %'zu. (%'zu new, %'zu reused)", created_nodes + reused_nodes, created_nodes, reused_nodes);
        }
    }

    /* report data */
    {
        double trans_count = mtbdd_satcount(imc.getMarkovTransitions().GetMTBDD(), block_length * 2);
        size_t node_count = mtbdd_nodecount(imc.getMarkovTransitions().GetMTBDD());
        INFO("New Markov transition relation: %'0.0f transitions, %'zu MTBDD nodes.", trans_count, node_count);
    }

    {
        int action_length = sylvan_set_count(imc.getVarA().GetBDD());
        double trans_count = 0;
        MTBDD trans[n_relations];
        for (int i=0; i<n_relations; i++) trans[i] = imc.transitions[i].first.GetBDD();
        for (int i=0; i<n_relations; i++) trans_count += mtbdd_satcount(trans[i], block_length * 2 + action_length);
        size_t node_count = mtbdd_nodecount_more(trans, n_relations);
        INFO("New interactive transition relation: %'0.0f transitions, %'zu MTBDD nodes.", trans_count, node_count);
    }
}

void Minimizations::minimize3(CTMC &ctmc, BDD partition)
{
    LACE_ME;

    INFO("");
    INFO("Computing new Markov transition relation (using pick-random encoding)...");

    sylvan_stats_t s1;
    sylvan_stats_snapshot(&s1);

    double t1 = wctime();

    /* pick a random state for each block */
    partition = CALL(create_pick_partition, partition, ctmc.getVarT().GetBDD());
    mtbdd_refs_push(partition);

    INFO("Computing the new transition relation...");

    /* create [B -> t] */
    MTBDDMAP map_b_to_t = mtbdd_map_empty();
    for (int i=0; i<block_length; i++) {
        mtbdd_refs_push(map_b_to_t);
        map_b_to_t = mtbdd_map_add(map_b_to_t, block_base+2*(block_length-i-1), sylvan_ithvar(2*(block_length-i-1)+1));
        mtbdd_refs_pop(1);
    }
    mtbdd_refs_push(map_b_to_t);

    /* create [B -> s] */
    MTBDDMAP map_b_to_s = mtbdd_map_empty();
    for (int i=0; i<block_length; i++) {
        mtbdd_refs_push(map_b_to_s);
        map_b_to_s = mtbdd_map_add(map_b_to_s, block_base+2*(block_length-i-1), sylvan_ithvar((block_length-i-1)*2));
        mtbdd_refs_pop(1);
    }
    mtbdd_refs_push(map_b_to_s);

    /* translate the Markov relation */

    /* step 1: compute R(s,B) using AndAbstractPlus */
    // INFO("Step 1/2...");
    MTBDD trans = ctmc.getMarkovTransitions().GetMTBDD();
    if (leaftype == 2) trans = gmp_and_exists(trans, partition, ctmc.getVarT().GetBDD());
    else trans = mtbdd_and_exists(trans, partition, ctmc.getVarT().GetBDD());
    mtbdd_refs_push(trans);

    /* step 2: compute R(s,t) result in one step */
    // INFO("Step 2/2...");
    trans = compute_markov_quotient(trans, partition, ctmc.getVarS().GetBDD(), map_b_to_t, map_b_to_s);
    ctmc.markov_transitions = trans;
    mtbdd_refs_pop(1);  // trans

    double t2 = wctime();

    sylvan_stats_t s2;
    sylvan_stats_snapshot(&s2);

    INFO("Computing new states, initial states, initial partition...");

    BDD state_vars = ctmc.getVarS().GetBDD();
    ctmc.initialStates = compute_states_quotient(ctmc.getInitialStates().GetBDD(), partition, state_vars, map_b_to_s);
    ctmc.states = CALL(new_state_space, count_blocks());

    int ip_size = ctmc.initialPartition.size();
    if (ip_size == 0) {
        /* do nothing */
    } else if (ip_size == 1) {
        ctmc.initialPartition[0] = ctmc.states;
    } else if (ip_size == 2) {
        /* only compute first block, then second block is the rest */
        Bdd first = ctmc.initialPartition[0];
        first = compute_states_quotient(first.GetBDD(), partition, state_vars, map_b_to_s);
        ctmc.initialPartition[0] = first;
        ctmc.initialPartition[1] = ctmc.states * !first;
    } else {
        /* translate each set of states */
        for (int i=0; i<ip_size; i++) {
            ctmc.initialPartition[i] = compute_states_quotient(ctmc.initialPartition[i].GetBDD(), partition, state_vars, map_b_to_s);
        }
    }

    mtbdd_refs_pop(2);  // map_b_to_t, map_b_to_s
    mtbdd_refs_pop(1);  // partition

    /* recreate variable sets */
    {
        MTBDD state_vars = mtbdd_true;
        MTBDD prime_vars = mtbdd_true;
        for (int i=0; i<block_length; i++) {
            mtbdd_refs_push(state_vars);
            mtbdd_refs_push(prime_vars);
            state_vars = mtbdd_set_add(state_vars, (block_length-i-1)*2);
            prime_vars = mtbdd_set_add(prime_vars, (block_length-i-1)*2+1);
            mtbdd_refs_pop(2);  // state_vars, prime_vars
        }
        ctmc.varS = state_vars;
        ctmc.varT = prime_vars;
    }

    sylvan_stats_t s3;
    sylvan_stats_snapshot(&s3);

    /* report times */
    INFO("");
    INFO("Time for computing the quotient of the transition relation: %'0.2f sec.", t2-t1);

    /* report number of created/reused nodes */
    {
        size_t created_nodes = s2.counters[BDD_NODES_CREATED] - s1.counters[BDD_NODES_CREATED];
        size_t reused_nodes = s2.counters[BDD_NODES_REUSED] - s1.counters[BDD_NODES_REUSED];
        INFO("Number of MTBDD nodes created: %'zu. (%'zu new, %'zu reused)", created_nodes + reused_nodes, created_nodes, reused_nodes);
        if (verbosity >= 1) {
            size_t created_nodes = s3.counters[BDD_NODES_CREATED] - s2.counters[BDD_NODES_CREATED];
            size_t reused_nodes = s3.counters[BDD_NODES_REUSED] - s2.counters[BDD_NODES_REUSED];
            INFO("Number of MTBDD nodes created: %'zu. (%'zu new, %'zu reused)", created_nodes + reused_nodes, created_nodes, reused_nodes);
        }
    }

    /* report data */
    {
        double trans_count = mtbdd_satcount(trans, block_length * 2);
        size_t node_count = mtbdd_nodecount(trans);
        INFO("New Markov transition relation: %'0.0f transitions, %'zu MTBDD nodes.", trans_count, node_count);
        if (verbosity >= 1) {
            INFO("New initial states: %'0.0f states, %'zu MTBDD nodes.", mtbdd_satcount(ctmc.initialStates.GetBDD(), block_length), mtbdd_nodecount(ctmc.initialStates.GetBDD()));
            INFO("New states: %'0.0f states, %'zu MTBDD nodes.", mtbdd_satcount(ctmc.states.GetBDD(), block_length), mtbdd_nodecount(ctmc.states.GetBDD()));
            int ip_size = ctmc.initialPartition.size();
            for (int i=0; i<ip_size; i++) {
                INFO("New initial partition [%d]: %'0.0f states, %'zu MTBDD nodes.", i, mtbdd_satcount(ctmc.initialPartition[i].GetBDD(), block_length), mtbdd_nodecount(ctmc.initialPartition[i].GetBDD()));
            }
        }
    }
}

void Minimizations::minimize3(LTS& lts, BDD partition)
{
    LACE_ME;

    INFO("");
    INFO("Computing new interactive transition relations (using custom operations)...");

    sylvan_stats_t s1;
    sylvan_stats_snapshot(&s1);

    double t1 = wctime();

    /* pick a random state for each block */
    partition = CALL(create_pick_partition, partition, lts.getVarT().GetBDD());
    mtbdd_refs_push(partition);

    INFO("Computing new interactive transition relations...");

    /* obtain transition relations */
    std::vector<std::pair<Bdd,Bdd>> transitions = lts.getTransitions();
    int n_relations = transitions.size();
    BDD trans[n_relations];

    /* get tau if branching bisimulation */
    BDD tau = bisimulation == 1 ? lts.getTau().GetBDD() : mtbdd_false;

    BDD st_vars = (lts.getVarS() * lts.getVarT()).GetBDD();

    /* translate all relations */
    for (int i=0; i<n_relations; i++) {
        int state_length = sylvan_set_count(lts.getVarS().GetBDD());
        trans[i] = transitions[i].first.GetBDD();
        int actual_state_length = sylvan_set_count(transitions[i].second.GetBDD());
        if (state_length*2 != actual_state_length) {
            /* extend the domain of the relation if needed */
            trans[i] = CALL(extend_relation, trans[i], transitions[i].second.GetBDD(), state_length);
        }
        mtbdd_refs_push(trans[i]);
        trans[i] = CALL(compute_trans_quotient, trans[i], partition, partition, st_vars, tau);
        mtbdd_refs_pop(1);
        mtbdd_refs_push(trans[i]);
    }

    double t2 = wctime();

    sylvan_stats_t s2;
    sylvan_stats_snapshot(&s2);

    INFO("Computing new states, initial states, initial partition...");

    /* create [B -> s] */
    MTBDD map = mtbdd_map_empty();
    for (int i=0; i<block_length; i++) {
        mtbdd_refs_push(map);
        map = mtbdd_map_add(map, block_base+2*(block_length-i-1), sylvan_ithvar((block_length-i-1)*2));
        mtbdd_refs_pop(1);
    }
    mtbdd_refs_push(map);

    {
        BDD state_vars = lts.getVarS().GetBDD();
        lts.initialStates = compute_states_quotient(lts.getInitialStates().GetBDD(), partition, state_vars, map);
        lts.states = CALL(new_state_space, count_blocks());

        int ip_size = lts.initialPartition.size();
        if (ip_size == 0) {
            /* do nothing */
        } else if (ip_size == 1) {
            lts.initialPartition[0] = lts.states;
        } else if (ip_size == 2) {
            /* only compute first block, then second block is the rest */
            Bdd first = lts.initialPartition[0];
            first = compute_states_quotient(first.GetBDD(), partition, state_vars, map);
            lts.initialPartition[0] = first;
            lts.initialPartition[1] = lts.states * !first;
        } else {
            /* translate each set of states */
            for (int i=0; i<ip_size; i++) {
                lts.initialPartition[i] = compute_states_quotient(lts.initialPartition[i].GetBDD(), partition, state_vars, map);
            }
        }
    }

    mtbdd_refs_pop(1);  // partition

    /* recreate variable sets */
    {
        MTBDD state_vars = mtbdd_true;
        MTBDD prime_vars = mtbdd_true;
        MTBDD st_vars = mtbdd_true;
        for (int i=0; i<block_length; i++) {
            mtbdd_refs_push(state_vars);
            mtbdd_refs_push(prime_vars);
            mtbdd_refs_push(st_vars);
            state_vars = mtbdd_set_add(state_vars, (block_length-i-1)*2);
            prime_vars = mtbdd_set_add(prime_vars, (block_length-i-1)*2+1);
            st_vars = mtbdd_set_add(st_vars, (block_length-i-1)*2+1);
            mtbdd_refs_push(st_vars);
            st_vars = mtbdd_set_add(st_vars, (block_length-i-1)*2);
            mtbdd_refs_pop(4);  // state_vars, prime_vars, two times st_vars
        }
        lts.varS = state_vars;
        lts.varT = prime_vars;

        for (int i=0; i<n_relations; i++) {
            lts.transitions[i].first = trans[i];
            lts.transitions[i].second = st_vars;
        }
        mtbdd_refs_pop(n_relations);
    }

    sylvan_stats_t s3;
    sylvan_stats_snapshot(&s3);

    /* report times */
    INFO("");
    INFO("Time for computing the quotient of the transition relation: %'0.2f sec.", t2-t1);

    /* report number of created/reused nodes */
    {
        size_t created_nodes = s2.counters[BDD_NODES_CREATED] - s1.counters[BDD_NODES_CREATED];
        size_t reused_nodes = s2.counters[BDD_NODES_REUSED] - s1.counters[BDD_NODES_REUSED];
        INFO("Number of MTBDD nodes created: %'zu. (%'zu new, %'zu reused)", created_nodes + reused_nodes, created_nodes, reused_nodes);
        if (verbosity >= 1) {
            size_t created_nodes = s3.counters[BDD_NODES_CREATED] - s2.counters[BDD_NODES_CREATED];
            size_t reused_nodes = s3.counters[BDD_NODES_REUSED] - s2.counters[BDD_NODES_REUSED];
            INFO("Number of MTBDD nodes created: %'zu. (%'zu new, %'zu reused)", created_nodes + reused_nodes, created_nodes, reused_nodes);
        }
    }

    /* report data */
    {
        int action_length = sylvan_set_count(lts.getVarA().GetBDD());
        double trans_count = 0;
        for (int i=0; i<n_relations; i++) trans_count += mtbdd_satcount(trans[i], block_length * 2 + action_length);
        size_t node_count = mtbdd_nodecount_more(trans, n_relations);
        INFO("New interactive transition relation: %'0.0f transitions, %'zu MTBDD nodes.", trans_count, node_count);
    }
}

void Minimizations::minimize3(IMC &imc, BDD partition)
{
    LACE_ME;

    INFO("");
    INFO("Computing new transition relations (using custom operations)...");

    sylvan_stats_t s1;
    sylvan_stats_snapshot(&s1);

    double t1 = wctime();

    /* pick a random state for each block */
    partition = CALL(create_pick_partition, partition, imc.getVarT().GetBDD());
    mtbdd_refs_push(partition);

    INFO("Computing the new transition relation...");

    /* create [B -> t] */
    MTBDDMAP map_b_to_t = mtbdd_map_empty();
    for (int i=0; i<block_length; i++) {
        mtbdd_refs_push(map_b_to_t);
        map_b_to_t = mtbdd_map_add(map_b_to_t, block_base+2*(block_length-i-1), sylvan_ithvar(2*(block_length-i-1)+1));
        mtbdd_refs_pop(1);
    }
    mtbdd_refs_push(map_b_to_t);

    /* create [B -> s] */
    MTBDDMAP map_b_to_s = mtbdd_map_empty();
    for (int i=0; i<block_length; i++) {
        mtbdd_refs_push(map_b_to_s);
        map_b_to_s = mtbdd_map_add(map_b_to_s, block_base+2*(block_length-i-1), sylvan_ithvar((block_length-i-1)*2));
        mtbdd_refs_pop(1);
    }
    mtbdd_refs_push(map_b_to_s);

    {
        /* translate the Markov relation */

        /* step 1: compute R(s,B) using AndAbstractPlus */
        // INFO("Step 1/2...");
        MTBDD trans = imc.getMarkovTransitions().GetMTBDD();
        if (leaftype == 2) trans = gmp_and_exists(trans, partition, imc.getVarT().GetBDD());
        else trans = mtbdd_and_exists(trans, partition, imc.getVarT().GetBDD());
        mtbdd_refs_push(trans);

        /* step 2: compute R(s,t) result in one step */
        // INFO("Step 2/2...");
        trans = compute_markov_quotient(trans, partition, imc.getVarS().GetBDD(), map_b_to_t, map_b_to_s);
        imc.markov_transitions = trans;
        mtbdd_refs_pop(1);  // trans
    }

    INFO("Computing the new interactive transition relations...");
    int n_relations;

    {
        /* obtain transition relations */
        std::vector<std::pair<Bdd,Bdd>> transitions = imc.getTransitions();
        n_relations = transitions.size();
        BDD trans[n_relations];

        /* get tau if branching bisimulation */
        BDD tau = bisimulation == 1 ? imc.getTau().GetBDD() : mtbdd_false;

        BDD st_vars = (imc.getVarS() * imc.getVarT()).GetBDD();

        /* translate all relations */
        for (int i=0; i<n_relations; i++) {
            int state_length = sylvan_set_count(imc.getVarS().GetBDD());
            trans[i] = transitions[i].first.GetBDD();
            int actual_state_length = sylvan_set_count(transitions[i].second.GetBDD());
            if (state_length*2 != actual_state_length) {
                /* extend the domain of the relation if needed */
                trans[i] = CALL(extend_relation, trans[i], transitions[i].second.GetBDD(), state_length);
            }
            mtbdd_refs_push(trans[i]);
            imc.transitions[i].first = CALL(compute_trans_quotient, trans[i], partition, partition, st_vars, tau);
            mtbdd_refs_pop(1);
        }
    }

    double t2 = wctime();

    sylvan_stats_t s2;
    sylvan_stats_snapshot(&s2);

    {
        INFO("Computing new states, initial states, initial partition...");

        {
            BDD state_vars = imc.getVarS().GetBDD();
            imc.initialStates = compute_states_quotient(imc.getInitialStates().GetBDD(), partition, state_vars, map_b_to_s);
            imc.states = CALL(new_state_space, count_blocks());

            int ip_size = imc.initialPartition.size();
            if (ip_size == 0) {
                /* do nothing */
            } else if (ip_size == 1) {
                imc.initialPartition[0] = imc.states;
            } else if (ip_size == 2) {
                /* only compute first block, then second block is the rest */
                Bdd first = imc.initialPartition[0];
                first = compute_states_quotient(first.GetBDD(), partition, state_vars, map_b_to_s);
                imc.initialPartition[0] = first;
                imc.initialPartition[1] = imc.states * !first;
            } else {
                /* translate each set of states */
                for (int i=0; i<ip_size; i++) {
                    imc.initialPartition[i] = compute_states_quotient(imc.initialPartition[i].GetBDD(), partition, state_vars, map_b_to_s);
                }
            }
        }
    }

    /* recreate variable sets */
    {
        MTBDD state_vars = mtbdd_true;
        MTBDD prime_vars = mtbdd_true;
        MTBDD st_vars = mtbdd_true;
        for (int i=0; i<block_length; i++) {
            state_vars = mtbdd_set_add(state_vars, (block_length-i-1)*2);
            prime_vars = mtbdd_set_add(prime_vars, (block_length-i-1)*2+1);
            st_vars = mtbdd_set_add(st_vars, (block_length-i-1)*2+1);
            st_vars = mtbdd_set_add(st_vars, (block_length-i-1)*2);
        }
        imc.varS = state_vars;
        imc.varT = prime_vars;

        for (int i=0; i<n_relations; i++) {
            imc.transitions[i].second = st_vars;
        }
    }

    sylvan_stats_t s3;
    sylvan_stats_snapshot(&s3);

    mtbdd_refs_pop(2);  // map_b_to_t, map_b_to_s

    /* report times */
    INFO("");
    INFO("Time for computing the quotient of the transition relation: %'0.2f sec.", t2-t1);

    /* report number of created/reused nodes */
    {
        size_t created_nodes = s2.counters[BDD_NODES_CREATED] - s1.counters[BDD_NODES_CREATED];
        size_t reused_nodes = s2.counters[BDD_NODES_REUSED] - s1.counters[BDD_NODES_REUSED];
        INFO("Number of MTBDD nodes created: %'zu. (%'zu new, %'zu reused)", created_nodes + reused_nodes, created_nodes, reused_nodes);
        if (verbosity >= 1) {
            size_t created_nodes = s3.counters[BDD_NODES_CREATED] - s2.counters[BDD_NODES_CREATED];
            size_t reused_nodes = s3.counters[BDD_NODES_REUSED] - s2.counters[BDD_NODES_REUSED];
            INFO("Number of MTBDD nodes created: %'zu. (%'zu new, %'zu reused)", created_nodes + reused_nodes, created_nodes, reused_nodes);
        }
    }

    /* report data */
    {
        double trans_count = mtbdd_satcount(imc.getMarkovTransitions().GetMTBDD(), block_length * 2);
        size_t node_count = mtbdd_nodecount(imc.getMarkovTransitions().GetMTBDD());
        INFO("New Markov transition relation: %'0.0f transitions, %'zu MTBDD nodes.", trans_count, node_count);
    }

    {
        int action_length = sylvan_set_count(imc.getVarA().GetBDD());
        double trans_count = 0;
        MTBDD trans[n_relations];
        for (int i=0; i<n_relations; i++) trans[i] = imc.transitions[i].first.GetBDD();
        for (int i=0; i<n_relations; i++) trans_count += mtbdd_satcount(trans[i], block_length * 2 + action_length);
        size_t node_count = mtbdd_nodecount_more(trans, n_relations);
        INFO("New interactive transition relation: %'0.0f transitions, %'zu MTBDD nodes.", trans_count, node_count);
    }
}


/**
 * Print the partition to stdout
 */
VOID_TASK_IMPL_2(enumerate_partition, BDD, partition, BDD, varT)
{
    int state_length = sylvan_set_count(varT);
    MTBDD vars = sylvan_and(varT, block_variables);
    uint8_t arr[state_length + block_length];
    printf("State    Block\n");
    MTBDD leaf = mtbdd_enum_all_first(partition, vars, arr, NULL);
    while (leaf != mtbdd_false) {
        uint64_t state = 0;
        for (int i=0; i<state_length; i++) if (arr[i]) state |= 1ULL<<i;
        uint64_t block = 0;
        for (int i=0; i<block_length; i++) if (arr[state_length+i]) block |= 1ULL<<i;
        printf("%-8zu %zu\n", state, block);
        leaf = mtbdd_enum_all_next(partition, vars, arr, NULL);
    }
}

/**
 * Print all states to stdout
 */
void
enumerate_states(BDD states, BDD state_vars)
{
    int state_length = sylvan_set_count(state_vars);
    printf("%d\n", state_length);
    uint8_t arr[state_length];
    printf("State\n");
    MTBDD leaf = mtbdd_enum_all_first(states, state_vars, arr, NULL);
    while (leaf != mtbdd_false) {
        uint64_t s = 0;
        for (int i=0; i<state_length; i++) if (arr[i]) s |= 1ULL<<i;
        printf("%zu\n", s);
        leaf = mtbdd_enum_all_next(states, state_vars, arr, NULL);
    }
}

/**
 * Print all Markov transitions to stdout
 */
void
enumerate_markov_transitions(MTBDD trans, StateSystem &system)
{
    Bdd varS = system.getVarS(), varT = system.getVarT();
    int state_length = sylvan_set_count(varS.GetBDD());
    MTBDD vars = (varS * varT).GetBDD();
    uint8_t arr[state_length * 2];
    printf("From     To       Rate\n");
    MTBDD leaf = mtbdd_enum_all_first(trans, vars, arr, NULL);
    while (leaf != mtbdd_false) {
        uint64_t from = 0;
        for (int i=0; i<state_length; i++) if (arr[i*2]) from |= 1ULL<<i;
        uint64_t to = 0;
        for (int i=0; i<state_length; i++) if (arr[i*2+1]) to |= 1ULL<<i;
        printf("%-8zu %-8zu ", from, to);
        mtbdd_fprint_leaf(stdout, leaf);
        printf("\n");
        leaf = mtbdd_enum_all_next(trans, vars, arr, NULL);
    }
}

}
