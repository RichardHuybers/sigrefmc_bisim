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

#include <stdint.h>
#include <sylvan.h>

#ifndef SIGREF_UTIL_H
#define SIGREF_UTIL_H

namespace sigref {

/**
 * Calculate A & B & C
 */
TASK_DECL_3(BDD, three_and, BDD, BDD, BDD);
#define three_and(a, b, c) CALL(three_and, a, b, c)

/**
 * Substitute each s by a t and vice versa
 */
TASK_DECL_1(MTBDD, swap_prime, MTBDD);
#define swap_prime(set) CALL(swap_prime, set)

/**
 * Compute \BigSatCount sets
 */
TASK_DECL_4(long double, big_satcount, MTBDD*, size_t, size_t, MTBDD);
#define big_satcount(sets, count, nvars, filter) CALL(big_satcount, sets, count, nvars, filter)

/**
 * Compute \BigUnion sets
 */
TASK_DECL_2(MTBDD, big_union, MTBDD*, size_t)
#define big_union(sets, count) CALL(big_union, sets, count)

/**
 * Count number of transitions using the signatures
 */
TASK_DECL_3(double, count_transitions, size_t, size_t, size_t);
#define count_transitions(first, count, nvars) CALL(count_transitions, first, count, nvars)

/**
 * Extend a relation <rel> defined on variables <vars> to the full domain,
 * which has <state_length> state variables (and <state_length> prime variables)
 */
TASK_DECL_3(BDD, extend_relation, BDD, BDD, int);
#define extend_relation(rel, vars, state_length) CALL(extend_relation, rel, vars, state_length)


/**
 * -RICHARD-
 * Rename variables old_vars in BDD a to new_vars
 */
TASK_DECL_3(BDD, rename_vars, BDD, BDD, BDD)
#define rename_vars(a, old_vars, new_vars) CALL(rename_vars, a, old_vars, new_vars)

} // namespace sigref

#endif
