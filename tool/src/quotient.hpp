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

#include <sylvan.h>

#include <sigref.h>
#include <systems.hpp>

#ifndef SIGREF_QUOTIENT_H
#define SIGREF_QUOTIENT_H

namespace sigref {

/**
 * Trim unneeded block variables from the partition.
 */
TASK_DECL_1(BDD, trim_block_variables, BDD);
#define trim_block_variables(partition) CALL(trim_block_variables, partition)

class Minimizations {
public:
    /**
     * Minimize a CTMC using the given partition and standard BDD operations.
     */
    static void minimize1(CTMC &ctmc, BDD partition);

    /**
     * Minimize an LTS using the given partition and standard BDD operations.
     * If <improved> is non-zero, use the 'optimized' variation of Wimmer's sigref.
     */
    static void minimize1(LTS &lts, BDD partition, int improved);

    /**
     * Minimize an IMC using the given partition and custom BDD operations.
     * If <improved> is non-zero, use the 'optimized' variation of Wimmer's sigref.
     */
    static void minimize1(IMC &imc, BDD partition, int improved);

    /**
     * Minimize a CTMC using the given partition and custom BDD operations.
     */
    static void minimize2(CTMC &ctmc, BDD partition);

    /**
     * Minimize an LTS using the given partition and custom BDD operations.
     */
    static void minimize2(LTS &lts, BDD partition);

    /**
     * Minimize an IMC using the given partition and custom BDD operations.
     */
    static void minimize2(IMC &imc, BDD partition);

    /**
     * Minimize a CTMC using the given partition and pick-random encoding.
     */
    static void minimize3(CTMC &ctmc, BDD partition);

    /**
     * Minimize an LTS using the given partition and pick-random encoding.
     */
    static void minimize3(LTS &lts, BDD partition);

    /**
     * Minimize an IMC using the given partition and pick-random encoding.
     */
    static void minimize3(IMC &imc, BDD partition);
};

}

#endif
