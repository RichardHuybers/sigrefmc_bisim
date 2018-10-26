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

#include <sylvan_int.h>
#include <inert.h>

/**
 * Compute inert transitions (version that skips intersection with a set of actions)
 */
TASK_IMPL_4(BDD, compute_inert, BDD, dd, BDD, left, BDD, right, BDD, st_vars)
{
    /* follow left[t:=s] and right,
       then return true if left = right */
    /* dd: s,t,a   left: t,B   right: t,B */
    /* variables order: s,t < a,B */
    if (dd == sylvan_false) return sylvan_false;
    /* remove states that have no block */
    if (left == sylvan_false || right == sylvan_false) return sylvan_false;
    if (sylvan_set_isempty(st_vars)) {
        /* now: dd: a   left: B   right: B */
        /* check if s and t are in same block */
        if (left != right) return sylvan_false;
        // return sylvan_and(dd, tau);
        return dd; // assuming pre-calculation of dd AND tau
    }

    BDD result;
    /* assumption: st_vars does not change during program */
    if (cache_get3(CACHE_INERT, dd, left, right, &result)) {
        return result;
    }

    sylvan_gc_test();

    BDDVAR var = sylvan_set_first(st_vars);

    BDD dd_low, dd_high;
    if (dd != sylvan_true && var == sylvan_var(dd)) {
        dd_low = sylvan_low(dd);
        dd_high = sylvan_high(dd);
    } else {
        dd_low = dd_high = dd;
    }

    /* by definition, left and right as partitions have variables after st_vars */
    /* note: left and right are defined on "t" variables */
    BDD left_low, left_high;
    if (var+1 == sylvan_var(left)) {
        left_low = sylvan_low(left);
        left_high = sylvan_high(left);
    } else {
        left_low = left_high = left;
    }

    BDD right_low, right_high;
    if (var == sylvan_var(right)) {
        right_low = sylvan_low(right);
        right_high = sylvan_high(right);
    } else {
        right_low = right_high = right;
    }

    bdd_refs_spawn(SPAWN(compute_inert, dd_low, left_low, right_low, sylvan_set_next(st_vars)));
    BDD high = CALL(compute_inert, dd_high, left_high, right_high, sylvan_set_next(st_vars));
    bdd_refs_push(high);
    BDD low = bdd_refs_sync(SYNC(compute_inert));
    bdd_refs_pop(1);
    result = sylvan_makenode(var, low, high);

    cache_put3(CACHE_INERT, dd, left, right, result);

    return result;
}
