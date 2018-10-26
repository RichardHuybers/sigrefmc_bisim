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

#include <systems.hpp>
#include <sylvan.h>

#ifndef BISIMULATION_H
#define BISIMULATION_H

namespace sigref {

TASK_DECL_1(BDD, min_lts_strong, sigref::LTS&);

TASK_DECL_1(BDD, min_lts_strong2, sigref::LTS&);

TASK_DECL_1(BDD, min_lts_strong3, sigref::LTS&);

TASK_DECL_1(BDD, min_lts_branching, sigref::LTS&);

TASK_DECL_1(BDD, min_ctmc, sigref::CTMC&);

TASK_DECL_1(BDD, min_imc_strong, sigref::IMC&);

TASK_DECL_1(BDD, min_imc_branching, sigref::IMC&);

}

#endif
