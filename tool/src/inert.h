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

#include <sylvan.h>

#ifndef SIGREF_INERT_H
#define SIGREF_INERT_H

#define CACHE_INERT (257LL<<42)

#ifdef __cplusplus
extern "C" {
#endif

/**
 * Compute inert transitions (version that skips intersection with a set of actions)
 *
 * @param dd the transition relation defined on s,t
 * @param left the assignment from states t to anything (with variables after t) (to match with s in dd)
 * @param right the assignment from states t to anything (with variables after t) (to match with t in dd)
 * @param st_vars the cube of variables s,t
 */
TASK_DECL_4(BDD, compute_inert, BDD, BDD, BDD, BDD);
#define compute_inert(dd, left, right, st_vars) CALL(compute_inert, dd, left, right, st_vars)

#ifdef __cplusplus
}
#endif

#endif
