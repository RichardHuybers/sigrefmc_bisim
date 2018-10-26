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
#include <sigref.h>
#include <parse_bdd.hpp>

namespace sigref {

using namespace sylvan;

BddLtsParser::BddLtsParser(const char* filename)
{
    FILE *f = fopen(filename, "r");
    if (f == NULL) {
        fprintf(stderr, "Cannot open file '%s'!\n", filename);
        return;
    }

    /* Load domain information */
    int numS, statebits, numA;
    if ((fread(&numS, sizeof(int), 1, f) != 1) ||
        (fread(&statebits, sizeof(int), 1, f) != 1) ||
        (fread(&numA, sizeof(int), 1, f) != 1)) {
        fprintf(stderr, "Invalid file format.\n");
        return;
    }

    numS *= statebits;

    /* Compute state, prime, action variables */
    std::vector<uint32_t> bdd_state_vars;
    std::vector<uint32_t> bdd_prime_vars;
    std::vector<uint32_t> bdd_action_vars;

    for (int i=0; i < numS; i++) {
        bdd_state_vars.push_back(i*2);
        bdd_prime_vars.push_back(i*2+1);
    }

    for (int i=0; i < numA; i++) {
        bdd_action_vars.push_back(1000000+i);
    }

    lts.varS = Bdd::VariablesCube(bdd_state_vars);
    lts.varT = Bdd::VariablesCube(bdd_prime_vars);
    lts.varA = Bdd::VariablesCube(bdd_action_vars);

    /* Load initial state */
    sylvan_serialize_fromfile(f);

    size_t set_bdd, set_vector_size, set_state_vars;
    if ((fread(&set_bdd, sizeof(size_t), 1, f) != 1) ||
        (fread(&set_vector_size, sizeof(size_t), 1, f) != 1) ||
        (fread(&set_state_vars, sizeof(size_t), 1, f) != 1)) {
        fprintf(stderr, "Invalid file format.\n");
        return;
    }

    lts.initialStates = sylvan_serialize_get_reversed(set_bdd);
    // ignore set_vector_size and set_state_vars

    /* Load number of transition relations */
    int n_relations;
    if (fread(&n_relations, sizeof(int), 1, f) != 1) {
        fprintf(stderr, "Invalid file format.\n");
        return;
    }

    /* Load each relation */
    for (int i=0; i<n_relations; i++) {
        sylvan_serialize_fromfile(f);

        size_t rel_bdd, rel_vars;
        if ((fread(&rel_bdd, sizeof(size_t), 1, f) != 1) ||
            (fread(&rel_vars, sizeof(size_t), 1, f) != 1)) {
            fprintf(stderr, "Invalid file format.\n");
            return;
        }

        BDD rel = sylvan_serialize_get_reversed(rel_bdd);
        BDD vars = sylvan_serialize_get_reversed(rel_vars);
        lts.transitions.push_back(std::make_pair(Bdd(rel), Bdd(vars)));
    }

    int has_reachable = 0;
    if (fread(&has_reachable, sizeof(int), 1, f) != 1) {
        has_reachable = 0;
    }

    if (has_reachable) {
        /* Load set of reachable states */
        sylvan_serialize_fromfile(f);

        size_t set_bdd, set_vector_size, set_state_vars;
        if ((fread(&set_bdd, sizeof(size_t), 1, f) != 1) ||
            (fread(&set_vector_size, sizeof(size_t), 1, f) != 1) ||
            (fread(&set_state_vars, sizeof(size_t), 1, f) != 1)) {
            fprintf(stderr, "Invalid file format.\n");
            return;
        }

        lts.states = sylvan_serialize_get_reversed(set_bdd);
    } else {
        lts.states = sylvan_true;
    }

    int actions = 0;
    if (fread(&actions, sizeof(int), 1, f) == 1) {
        for (int i=0; i<actions; i++) {
            uint32_t len;
            if (fread(&len, sizeof(uint32_t), 1, f) != 1) {
                fprintf(stderr, "Invalid file format.\n");
                return;
            }
            char s[len+1];
            s[len] = 0;
            if (fread(s, sizeof(char), len, f) != len) {
                fprintf(stderr, "Invalid file format.\n");
            }
            if (strcmp(s, "tau") == 0) {
                tau_action = i;
            }
        }
    }

    fclose(f);

    /* Compute tau from tau_action (default: 0) */
    int action_bits = sylvan_set_count(lts.varA.GetBDD());
    std::vector<uint8_t> tau_value;
    for (int i=0; i<action_bits; i++) {
        tau_value.push_back(tau_action & (1LL<<(action_bits-i-1)) ? 1 : 0);
    }
    lts.tau = Bdd::bddCube(lts.varA, tau_value);

    /* Default initial partition: just 1 block containing the reachable states */
    lts.initialPartition.push_back(lts.states);
}

BddLtsParser::~BddLtsParser()
{
}

}
