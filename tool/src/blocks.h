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

#ifndef SIGREF_BLOCKS_H
#define SIGREF_BLOCKS_H

#ifdef __cplusplus
extern "C" {
#endif

extern uint32_t block_base; // base for block variables
extern int block_length; // number of block variables
extern BDD block_variables;

// initialize block_length and block_variables for <nvars> block variables
#define prepare_blocks(nvars) CALL(prepare_blocks, nvars)
VOID_TASK_DECL_1(prepare_blocks, int);

TASK_DECL_1(BDD, encode_block, uint64_t);
TASK_DECL_1(uint64_t, decode_block, BDD);

#ifdef __cplusplus
}
#endif

#endif
