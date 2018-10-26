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

#ifndef SIGREF_REFINE_H
#define SIGREF_REFINE_H

#ifdef __cplusplus
extern "C" {
#endif

#define refine(signatures, vars, partition) CALL(refine, signature, vars, partition)
TASK_DECL_3(BDD, refine, MTBDD, BDD, BDD);

size_t count_blocks();
void set_signatures_size(size_t count);
size_t get_next_block();
BDD get_signature(size_t index);
void free_refine_data();

#ifdef __cplusplus
}
#endif

#endif
