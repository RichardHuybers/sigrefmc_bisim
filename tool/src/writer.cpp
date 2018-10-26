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
#include <refine.h>
#include <blocks.h>
#include <systems.hpp>
#include <sigref.h>
#include <sigref_util.hpp>
#include <writer.hpp>

#include <stdio.h>
#include <sylvan_stats.h>

namespace sigref {

using namespace sylvan;

/**
 * Write result using signatures
 */
void
writeSignatures(const char *filename, CTMC& ctmc)
{
    INFO("");
    INFO("Starting writing result (from signatures) to %s...", filename);
    FILE *f = fopen(filename, "w");
    if (f == NULL) {
        fprintf(stderr, "Cannot open file '%s'!\n", filename);
        return;
    }

    LACE_ME;

    /* Count number of blocks and transitions */

    size_t n_blocks = count_blocks();
    double n_transitions = CALL(count_transitions, 0, n_blocks, block_length);

    fprintf(f, "; <number of blocks (1,2,...,N)>; <number of transitions>\n");

    /* First write the number of blocks, the number of transitions, */
    fprintf(f, "%zu %zu\n", n_blocks, (size_t)n_transitions);

    fprintf(f, "; each transition: <from block> <to block> <rate>\n");

    for(size_t i=1; i<=n_blocks; i++) {
        MTBDD sig = get_signature(i-1);

        uint8_t arr[block_length];
        assert((int)sylvan_set_count(block_variables) == block_length);
        MTBDD leaf = mtbdd_enum_all_first(sig, block_variables, arr, NULL);
        while (leaf != mtbdd_false) {
            /* decode block */
            uint64_t to_block = 0;
            for (int j=0; j<block_length; j++) if (arr[j] == 1) to_block |= 1ULL<<j;
            fprintf(f, "%zu %zu ", i, to_block);
            mtbdd_fprint_leaf(f, leaf);
            fprintf(f, "\n");
            leaf = mtbdd_enum_all_next(sig, block_variables, arr, NULL);
        }
    }

    fclose(f);
    (void)ctmc;

    INFO("Finished writing result to %s.", filename);
}

void
writeSignatures(const char *filename, LTS& lts)
{
    INFO("");
    INFO("Starting writing results (from signatures) to %s...", filename);
    FILE *f = fopen(filename, "w");
    if (f == NULL) {
        fprintf(stderr, "Cannot open file '%s'!\n", filename);
        return;
    }

    LACE_ME;

    /* Count number of blocks and transitions */

    size_t n_blocks = count_blocks();
    BDD action_variables = lts.getVarA().GetBDD();
    int action_length = sylvan_set_count(action_variables);
    BDD vars = sylvan_and(action_variables, block_variables);
    double n_transitions = CALL(count_transitions, 0, n_blocks, block_length + action_length);

    fprintf(f, "; <number of blocks (1,2,...,N)>; <number of transitions>\n");

    /* First write the number of blocks, the number of transitions, */
    fprintf(f, "%zu %zu\n", n_blocks, (size_t)n_transitions);

    fprintf(f, "; each transition: <from block>, <to block>, <action>\n");

    for(size_t i=1; i<=n_blocks; i++) {
        MTBDD sig = get_signature(i-1);

        uint8_t arr[block_length];
        MTBDD leaf = mtbdd_enum_all_first(sig, vars, arr, NULL);
        while (leaf != mtbdd_false) {
            /* decode action */
            uint64_t action = 0;
            for (int j=0; j<action_length; j++) if (arr[j] == 1) action |= 1ULL<<j;
            /* decode block */
            uint64_t to_block = 0;
            for (int j=0; j<block_length; j++) if (arr[action_length+j] == 1) to_block |= 1ULL<<j;
            fprintf(f, "%zu, %zu, %zu\n", i, to_block, action);
            leaf = mtbdd_enum_all_next(sig, vars, arr, NULL);
        }
    }

    fclose(f);

    INFO("Finished writing result to %s.", filename);
}

void
writeExplicitOutput(const char *filename, CTMC& ctmc)
{
    INFO("");
    INFO("Starting writing result to %s...", filename);

    FILE *f = fopen(filename, "w");
    if (f == NULL) {
        fprintf(stderr, "Cannot open file '%s'!\n", filename);
        return;
    }

    LACE_ME;

    /* Count number of blocks and transitions */

    MTBDD markov_trans = ctmc.getMarkovTransitions().GetMTBDD();
    int state_length = sylvan_set_count(ctmc.getVarS().GetBDD());
    double n_transitions = mtbdd_satcount(markov_trans, state_length * 2);
    double n_blocks = mtbdd_satcount(ctmc.getStates().GetBDD(), state_length);

    fprintf(f, "; <number of blocks (1,2,...,N)>; <number of transitions>\n");

    /* First write the number of blocks, the number of transitions, */
    fprintf(f, "%zu %zu\n", (size_t)n_blocks, (size_t)n_transitions);

    {
        fprintf(f, "; each initial state\n");
        uint8_t arr[state_length];
        BDD initial_states = ctmc.getInitialStates().GetBDD();
        BDD vars = ctmc.getVarS().GetBDD();
        assert((int)sylvan_set_count(vars) == state_length);
        MTBDD leaf = mtbdd_enum_all_first(initial_states, vars, arr, NULL);
        while (leaf != mtbdd_false) {
            /* decode from block */
            uint64_t block = 0;
            for (int j=0; j<state_length; j++) if (arr[j] == 1) block |= 1ULL<<j;
            fprintf(f, "%zu ", block);
            leaf = mtbdd_enum_all_next(initial_states, vars, arr, NULL);
        }
        fprintf(f, "\n");
    }

    {
        fprintf(f, "; each transition: <from block> <to block> <rate>\n");

        BDD vars = (ctmc.getVarS() * ctmc.getVarT()).GetBDD();
        uint8_t arr[state_length * 2];
        assert((int)sylvan_set_count(vars) == state_length*2);
        MTBDD leaf = mtbdd_enum_all_first(markov_trans, vars, arr, NULL);
        while (leaf != mtbdd_false) {
            /* decode from block */
            uint64_t from_block = 0;
            for (int j=0; j<state_length; j++) if (arr[j*2] == 1) from_block |= 1ULL<<j;
            /* decode to block */
            uint64_t to_block = 0;
            for (int j=0; j<state_length; j++) if (arr[j*2+1] == 1) to_block |= 1ULL<<j;
            fprintf(f, "%zu %zu ", from_block, to_block);
            mtbdd_fprint_leaf(f, leaf);
            fprintf(f, "\n");
            leaf = mtbdd_enum_all_next(markov_trans, vars, arr, NULL);
        }
    }

    fclose(f);
    (void)ctmc;

    INFO("Finished writing result to %s.", filename);
}

void
writeExplicitOutput(const char *filename, LTS& lts)
{
    INFO("");
    INFO("Starting writing result to %s...", filename);
    FILE *f = fopen(filename, "w");
    if (f == NULL) {
        fprintf(stderr, "Cannot open file '%s'!\n", filename);
        return;
    }

    LACE_ME;

    /* Count number of blocks and transitions */

    BDD state_variables = lts.getVarS().GetBDD();
    BDD action_variables = lts.getVarA().GetBDD();
    BDD sta_vars = (lts.getVarS() * lts.getVarT() * lts.getVarA()).GetBDD();
    int state_length = sylvan_set_count(state_variables);
    int action_length = sylvan_set_count(action_variables);
    int sta_length = sylvan_set_count(sta_vars);

    double n_blocks = mtbdd_satcount(lts.getStates().GetBDD(), state_length);
    double n_transitions = 0;
    int n_relations = lts.getTransitions().size();
    for (int i=0; i<n_relations; i++) {
        // blaargh. assume sta_vars
        n_transitions += mtbdd_satcount(lts.getTransitions()[0].first.GetBDD(), sta_length);
    }

    fprintf(f, "; <number of blocks (1,2,...,N)>; <number of transitions>\n");

    /* First write the number of blocks, the number of transitions, */
    fprintf(f, "%zu %zu\n", (size_t)n_blocks, (size_t)n_transitions);

    {
        fprintf(f, "; each initial state\n");
        uint8_t arr[state_length];
        BDD initial_states = lts.getInitialStates().GetBDD();
        BDD vars = lts.getVarS().GetBDD();
        MTBDD leaf = mtbdd_enum_all_first(initial_states, vars, arr, NULL);
        while (leaf != mtbdd_false) {
            /* decode from block */
            uint64_t block = 0;
            for (int j=0; j<state_length; j++) if (arr[j] == 1) block |= 1ULL<<j;
            fprintf(f, "%zu ", block);
            leaf = mtbdd_enum_all_next(initial_states, vars, arr, NULL);
        }
        fprintf(f, "\n");
    }

    fprintf(f, "; each transition: <from block>, <to block>, <action>\n");

    for (int i=0; i<n_relations; i++) {
        BDD rel = lts.getTransitions()[i].first.GetBDD();
        // blaargh. assume sta_vars
        uint8_t arr[sta_length];
        MTBDD leaf = mtbdd_enum_all_first(rel, sta_vars, arr, NULL);
        while (leaf != mtbdd_false) {
            /* decode from block */
            uint64_t from_block = 0;
            for (int j=0; j<state_length; j++) if (arr[2*j] == 1) from_block |= 1ULL<<j;
            /* decode block */
            uint64_t to_block = 0;
            for (int j=0; j<state_length; j++) if (arr[2*j+1] == 1) to_block |= 1ULL<<j;
            /* decode action */
            uint64_t action = 0;
            for (int j=0; j<action_length; j++) if (arr[2*state_length+j] == 1) action |= 1ULL<<j;
            fprintf(f, "%zu, %zu, %zu\n", from_block, to_block, action);
            leaf = mtbdd_enum_all_next(rel, sta_vars, arr, NULL);
        }
    }

    fclose(f);

    INFO("Finished writing result to %s.", filename);
}

void
writeExplicitOutput(const char *filename, IMC& imc)
{
    INFO("");
    INFO("Starting writing result to %s...", filename);
    FILE *f = fopen(filename, "w");
    if (f == NULL) {
        fprintf(stderr, "Cannot open file '%s'!\n", filename);
        return;
    }

    LACE_ME;

    /* Count number of blocks and transitions */

    BDD state_variables = imc.getVarS().GetBDD();
    BDD action_variables = imc.getVarA().GetBDD();
    BDD sta_vars = (imc.getVarS() * imc.getVarT() * imc.getVarA()).GetBDD();
    int state_length = sylvan_set_count(state_variables);
    int action_length = sylvan_set_count(action_variables);
    int sta_length = sylvan_set_count(sta_vars);

    double n_blocks = mtbdd_satcount(imc.getStates().GetBDD(), state_length);
    double n_transitions = 0;
    int n_relations = imc.getTransitions().size();
    for (int i=0; i<n_relations; i++) {
        // blaargh. assume sta_vars
        n_transitions += mtbdd_satcount(imc.getTransitions()[0].first.GetBDD(), sta_length);
    }
    MTBDD markov_trans = imc.getMarkovTransitions().GetMTBDD();
    double n_markov = mtbdd_satcount(markov_trans, state_length * 2);

    fprintf(f, "; <number of blocks (1,2,...,N)>; <number of Markov transitions>; <number of interactive transitions>\n");

    /* First write the number of blocks, the number of transitions, */
    fprintf(f, "%zu %zu %zu\n", (size_t)n_blocks, (size_t)n_markov, (size_t)n_transitions);

    {
        fprintf(f, "; each initial state\n");
        uint8_t arr[state_length];
        BDD initial_states = imc.getInitialStates().GetBDD();
        BDD vars = imc.getVarS().GetBDD();
        MTBDD leaf = mtbdd_enum_all_first(initial_states, vars, arr, NULL);
        while (leaf != mtbdd_false) {
            /* decode from block */
            uint64_t block = 0;
            for (int j=0; j<state_length; j++) if (arr[j] == 1) block |= 1ULL<<j;
            fprintf(f, "%zu ", block);
            leaf = mtbdd_enum_all_next(initial_states, vars, arr, NULL);
        }
        fprintf(f, "\n");
    }

    {
        fprintf(f, "; each transition: <from block> <to block> <rate>\n");

        BDD vars = (imc.getVarS() * imc.getVarT()).GetBDD();
        uint8_t arr[state_length * 2];
        MTBDD leaf = mtbdd_enum_all_first(markov_trans, vars, arr, NULL);
        while (leaf != mtbdd_false) {
            /* decode from block */
            uint64_t from_block = 0;
            for (int j=0; j<state_length; j++) if (arr[j*2] == 1) from_block |= 1ULL<<j;
            /* decode to block */
            uint64_t to_block = 0;
            for (int j=0; j<state_length; j++) if (arr[j*2+1] == 1) to_block |= 1ULL<<j;
            fprintf(f, "%zu %zu ", from_block, to_block);
            mtbdd_fprint_leaf(f, leaf);
            fprintf(f, "\n");
            leaf = mtbdd_enum_all_next(markov_trans, vars, arr, NULL);
        }
    }

    {
        fprintf(f, "; each transition: <from block>, <to block>, <action>\n");

        for (int i=0; i<n_relations; i++) {
            BDD rel = imc.getTransitions()[i].first.GetBDD();
            // blaargh. assume sta_vars
            uint8_t arr[sta_length];
            MTBDD leaf = mtbdd_enum_all_first(rel, sta_vars, arr, NULL);
            while (leaf != mtbdd_false) {
                /* decode from block */
                uint64_t from_block = 0;
                for (int j=0; j<state_length; j++) if (arr[2*j] == 1) from_block |= 1ULL<<j;
                /* decode block */
                uint64_t to_block = 0;
                for (int j=0; j<state_length; j++) if (arr[2*j+1] == 1) to_block |= 1ULL<<j;
                /* decode action */
                uint64_t action = 0;
                for (int j=0; j<action_length; j++) if (arr[2*state_length+j] == 1) action |= 1ULL<<j;
                fprintf(f, "%zu, %zu, %zu\n", from_block, to_block, action);
                leaf = mtbdd_enum_all_next(rel, sta_vars, arr, NULL);
            }
        }
    }

    fclose(f);

    INFO("Finished writing result to %s.", filename);
}

void
writeSymbolicOutput(const char *filename, CTMC& ctmc)
{
    INFO("");
    INFO("Starting writing result to %s...", filename);

    FILE *f = fopen(filename, "w");
    if (f == NULL) {
        fprintf(stderr, "Cannot open file '%s'!\n", filename);
        return;
    }

    int numS = 1;
    int statebits = block_length;
    int numA = 0; // ctmc has no actions
    int n_initial_partitions = ctmc.getInitialPartition().size();

    fwrite(&numS, sizeof(int), 1, f);
    fwrite(&statebits, sizeof(int), 1, f);
    fwrite(&numA, sizeof(int), 1, f);
    fwrite(&n_initial_partitions, sizeof(int), 1, f);

    MTBDD toWrite[3 + n_initial_partitions];
    toWrite[0] = ctmc.getMarkovTransitions().GetMTBDD();
    toWrite[1] = ctmc.getInitialStates().GetBDD();
    toWrite[2] = ctmc.getStates().GetBDD();
    for (int i=0; i<n_initial_partitions; i++) {
        toWrite[3+i] = ctmc.getInitialPartition()[i].GetBDD();
    }

    LACE_ME;
    mtbdd_writer_tobinary(f, toWrite, 3 + n_initial_partitions);

    fclose(f);

    INFO("Finished writing result to %s.", filename);
}

void
writeSymbolicOutput(const char *filename, LTS& lts)
{
    INFO("");
    INFO("Starting writing result to %s...", filename);

    FILE *f = fopen(filename, "w");
    if (f == NULL) {
        fprintf(stderr, "Cannot open file '%s'!\n", filename);
        return;
    }

    int numS = 1;
    int statebits = block_length;
    int numA = sylvan_set_count(lts.getVarA().GetBDD());
    int n_relations = lts.getTransitions().size();
    int n_initial_partitions = lts.getInitialPartition().size();

    fwrite(&numS, sizeof(int), 1, f);
    fwrite(&statebits, sizeof(int), 1, f);
    fwrite(&numA, sizeof(int), 1, f);
    fwrite(&n_relations, sizeof(int), 1, f);
    fwrite(&n_initial_partitions, sizeof(int), 1, f);

    MTBDD toWrite[2 + n_initial_partitions + n_relations*2];
    toWrite[0] = lts.getInitialStates().GetBDD();
    toWrite[1] = lts.getStates().GetBDD();
    for (int i=0; i<n_initial_partitions; i++) {
        toWrite[2+i] = lts.getInitialPartition()[i].GetBDD();
    }
    for (int i=0; i<n_relations; i++) {
        toWrite[2+n_initial_partitions+2*i] = lts.getTransitions()[i].first.GetBDD();
        toWrite[2+n_initial_partitions+2*i+1] = lts.getTransitions()[i].second.GetBDD();
    }

    LACE_ME;
    mtbdd_writer_tobinary(f, toWrite, 2 + n_initial_partitions + n_relations*2);

    fclose(f);

    INFO("Finished writing result to %s.", filename);
}

void
writeSymbolicOutput(const char *filename, IMC& imc)
{
    INFO("");
    INFO("Starting writing result to %s...", filename);

    FILE *f = fopen(filename, "w");
    if (f == NULL) {
        fprintf(stderr, "Cannot open file '%s'!\n", filename);
        return;
    }

    int numS = 1;
    int statebits = block_length;
    int numA = sylvan_set_count(imc.getVarA().GetBDD());
    int n_relations = imc.getTransitions().size();
    int n_initial_partitions = imc.getInitialPartition().size();

    fwrite(&numS, sizeof(int), 1, f);
    fwrite(&statebits, sizeof(int), 1, f);
    fwrite(&numA, sizeof(int), 1, f);
    fwrite(&n_relations, sizeof(int), 1, f);
    fwrite(&n_initial_partitions, sizeof(int), 1, f);

    MTBDD toWrite[3 + n_initial_partitions + n_relations*2];
    toWrite[0] = imc.getMarkovTransitions().GetMTBDD();
    toWrite[1] = imc.getInitialStates().GetBDD();
    toWrite[2] = imc.getStates().GetBDD();
    for (int i=0; i<n_initial_partitions; i++) {
        toWrite[3+i] = imc.getInitialPartition()[i].GetBDD();
    }
    for (int i=0; i<n_relations; i++) {
        toWrite[3+n_initial_partitions+2*i] = imc.getTransitions()[i].first.GetBDD();
        toWrite[3+n_initial_partitions+2*i+1] = imc.getTransitions()[i].second.GetBDD();
    }

    LACE_ME;
    mtbdd_writer_tobinary(f, toWrite, 2 + n_initial_partitions + n_relations*2);

    fclose(f);

    INFO("Finished writing result to %s.", filename);
}

}
