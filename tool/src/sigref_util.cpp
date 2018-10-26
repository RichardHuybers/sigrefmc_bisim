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

#include <sigref.h>
#include <sigref_util.hpp>
#include <sylvan_int.h>
#include <refine.h>

namespace sigref {

TASK_IMPL_3(BDD, three_and, BDD, a, BDD, b, BDD, c)
{
    if (a == sylvan_false || b == sylvan_false || c == sylvan_false) return sylvan_false;

    if (a == sylvan_true) return sylvan_and(b, c);
    if (b == sylvan_true) return sylvan_and(a, c);
    if (c == sylvan_true) return sylvan_and(a, b);

    BDD result;
    if (cache_get3(CACHE_THREEAND, a, b, c, &result)) return result;

    sylvan_gc_test();

    BDDVAR a_var = sylvan_var(a);
    BDDVAR b_var = sylvan_var(b);
    BDDVAR c_var = sylvan_var(c);

    BDD var = a_var;
    if (var > b_var) var = b_var;
    if (var > c_var) var = c_var;

    BDD a_low, a_high;
    if (var == a_var) {
        a_low = sylvan_low(a);
        a_high = sylvan_high(a);
    } else {
        a_low = a_high = a;
    }

    BDD b_low, b_high;
    if (var == b_var) {
        b_low = sylvan_low(b);
        b_high = sylvan_high(b);
    } else {
        b_low = b_high = b;
    }

    BDD c_low, c_high;
    if (var == c_var) {
        c_low = sylvan_low(c);
        c_high = sylvan_high(c);
    } else {
        c_low = c_high = c;
    }

    bdd_refs_spawn(SPAWN(three_and, a_low, b_low, c_low));
    BDD high = bdd_refs_push(CALL(three_and, a_high, b_high, c_high));
    BDD low = bdd_refs_sync(SYNC(three_and));
    result = sylvan_makenode(var, low, high);
    bdd_refs_pop(1);

    cache_put3(CACHE_THREEAND, a, b, c, result);
    return result;
}

TASK_IMPL_1(MTBDD, swap_prime, MTBDD, set)
{
    if (mtbdd_isleaf(set)) return set;

    // TODO: properly ignore action/block variables
    if (mtbdd_getvar(set) >= 99999) return set;

    MTBDD result;
    if (cache_get3(CACHE_SWAPPRIME, set, 0, 0, &result)) return result;

    sylvan_gc_test();

    mtbdd_refs_spawn(SPAWN(swap_prime, mtbdd_getlow(set)));
    MTBDD high = mtbdd_refs_push(CALL(swap_prime, mtbdd_gethigh(set)));
    MTBDD low = mtbdd_refs_sync(SYNC(swap_prime));
    result = mtbdd_makenode(sylvan_var(set)^1, low, high);
    mtbdd_refs_pop(1);

    cache_put3(CACHE_SWAPPRIME, set, 0, 0, result);
    return result;
}

TASK_IMPL_4(long double, big_satcount, MTBDD*, dds, size_t, count, size_t, nvars, MTBDD, filter)
{
    if (count == 1) {
        MTBDD dd = filter == mtbdd_true ? *dds : mtbdd_times(*dds, filter);
        return (long double)mtbdd_satcount(dd, nvars);
    }
    SPAWN(big_satcount, dds, count/2, nvars, filter);
    long double result = big_satcount(dds+count/2, count-count/2, nvars, filter);
    return result + SYNC(big_satcount);
}

TASK_IMPL_2(MTBDD, big_union, MTBDD*, sets, size_t, count)
{
    if (count == 1) return *sets;
    mtbdd_refs_spawn(SPAWN(big_union, sets, count/2));
    MTBDD right = mtbdd_refs_push(CALL(big_union, sets+count/2, count-count/2));
    MTBDD left = mtbdd_refs_push(mtbdd_refs_sync(SYNC(big_union)));
    MTBDD result = mtbdd_plus(left, right);
    mtbdd_refs_pop(2);
    return result;
}

TASK_IMPL_3(double, count_transitions, size_t, first, size_t, count, size_t, nvars)
{
    if (count == 1) return mtbdd_satcount(get_signature(first), nvars);
    SPAWN(count_transitions, first, count/2, nvars);
    double result = CALL(count_transitions, first+count/2, count-count/2, nvars);
    return result + SYNC(count_transitions);
}

/**
 * Extend a transition relation to a larger domain (using s=s')
 */
TASK_IMPL_3(BDD, extend_relation, BDD, relation, BDD, variables, int, state_length)
{
    /* first determine which state BDD variables are in rel */
    int has[state_length];
    for (int i=0; i<state_length; i++) has[i] = 0;
    BDDSET s = variables;
    while (s != sylvan_true) {
        BDDVAR v = sylvan_var(s);
        if (v/2 >= (unsigned)state_length) break; // action labels
        has[v/2] = 1;
        s = sylvan_high(s);
    }
    /* create "s=s'" for all variables not in rel */
    BDD eq = sylvan_true;
    for (int i=state_length-1; i>=0; i--) {
        if (has[i]) continue;
        BDD low = sylvan_makenode(2*i+1, eq, sylvan_false);
        bdd_refs_push(low);
        BDD high = sylvan_makenode(2*i+1, sylvan_false, eq);
        bdd_refs_pop(1);
        eq = sylvan_makenode(2*i, low, high);
    }

    bdd_refs_push(eq);
    BDD result = sylvan_and(relation, eq);
    bdd_refs_pop(1);

    return result;
}


/**
 * -RICHARD-
 * Rename variables old_vars in BDD F to new_vars
 */
TASK_IMPL_3(BDD, rename_vars, BDD, F, BDD, old_vars, BDD, new_vars)
{
    if (mtbdd_isleaf(F)) return F;
 
    BDDVAR F_var = mtbdd_getvar(F);   
    if (F_var >= 99999) return F;

    BDD result;
    if (cache_get3(CACHE_RENAME, F, old_vars, new_vars, &result)) return result;

    sylvan_gc_test();
    
    BDD old_vars_copy = old_vars;
    BDD new_vars_copy = new_vars;

    while (mtbdd_getvar(old_vars) != F_var) {
        if (mtbdd_isleaf(old_vars)) break;
        old_vars = mtbdd_gethigh(old_vars);
        new_vars = mtbdd_gethigh(new_vars);
    }

    BDD low, high;
    bdd_refs_spawn(SPAWN(rename_vars, mtbdd_gethigh(F), old_vars_copy, new_vars_copy));
    low = CALL(rename_vars, mtbdd_getlow(F), old_vars_copy, new_vars_copy);
    bdd_refs_push(low);
    high = bdd_refs_sync(SYNC(rename_vars));
    bdd_refs_pop(1);
    
    if (F_var == mtbdd_getvar(old_vars))
        F_var = mtbdd_getvar(new_vars);
    
    result = sylvan_makenode(F_var, low, high);

    cache_put3(CACHE_RENAME, F, old_vars_copy, new_vars_copy, result);

    return result;
}



}
