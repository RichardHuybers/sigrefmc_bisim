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

#include <argp.h>
#include <locale.h>
#include <stddef.h>
#include <stdio.h>
#include <sys/time.h>

#ifdef HAVE_PROFILER
#include <gperftools/profiler.h>
#endif

#include <bisimulation.hpp>
#include <parse_bdd.hpp>
#include <parse_xml.hpp>
#include <sigref.h>
#include <sylvan_gmp.h>
#include <refine.h>
#include <writer.hpp>
#include <quotient.hpp>

#include <sigref_util.hpp>

using namespace sylvan;
using namespace sigref;

/* Configuration */
static char* model_filename = NULL;
static char* output_filename = NULL;
#ifdef HAVE_PROFILER
static char* profile_filename = NULL;
#endif
static int workers = 0; // autodetect

int bisimulation = 1; // branching
int leaftype = 2; // 0 = float, 1 = fraction, 2 = gmp
int verbosity = 0; // default: no excessive node counting
int merge_relations = 0; // merge relations to 1 relation
int closure = 0; // 0 = fixpoint, 1 = squaring, 2 = recursive
int reachable = 0; // 0 = no, 1 = yes
int tau_action = 0; // default: 0
int ordering = 0; // 0 = s,t < a < B, 1 = s,t < B < a, default: 0
int quotient_type = 0; // 0 = no quotient, 1 = standard operations, 2 = standard operations variant 2, 3 = custom operations, 4 = pick-random, 5 = test (generate explicit output file for each type except pick-random)
int output_type = 0; // 0 = no output, 1 = explicit output, 2 = symbolic output
const char *table_sizes = "26,31,25,30"; // default table sizes (powers of 2) 

/* argp configuration */
static struct argp_option options[] =
{
    {"workers", 'w', "<workers>", 0, "Number of workers (default=0: autodetect)", 0},
    {"bisi", 'b', "<bisimulation>", 0, "Bisimulation (branching=1, strong=2)", 0},
    {"leaf", 'l', "<leaf type>", 0, "Leaf type (\"floating point\" (default), \"fraction\", \"gmp\")", 0},
    {"verbosity", 'v', "<verbosity>", 0, "Verbosity (default=0, more=1, too much=2)", 0},
    {"merge-relations", 'm', 0, 0, "Merge transition relations into one transition relation", 0},
    {"closure", 'c', "<closure>", 0, "Closure algorithm (\"fixpoint\", \"squaring\" or \"recursive\")", 0},
    {"reachable", 'r', 0, 0, "Limit partition to reachable states", 0},
    {"tau", 't', "<tau-action>", 0, "Which action is tau (default=0)", 0},
    {"blocks-first", 1, 0, 0, "Order block variables before action variables", 0},
    {"table-sizes", 2, "<tablesize,tablemax,cachesize,cachemax>", 0, "Nodes table and operation cache sizes as powers of 2", 0},
#ifdef HAVE_PROFILER
    {"profiler", 'p', "<filename>", 0, "Filename for profiling", 0},
#endif
    {"quotient", 'q', "<quotient type>", 0, "Quotient (type: \"pick-random\", \"block\", \"block-s1\", \"block-s2\")", 0},
    {"output-type", 'o', "<output type>", 0, "Output type (\"explicit\", \"symbolic\")", 0},
    {0, 0, 0, 0, 0, 0}
};

static error_t
parse_opt(int key, char *arg, struct argp_state *state)
{
    switch (key) {
    case 'w':
        workers = atoi(arg);
        break;
    case 'b':
        bisimulation = atoi(arg);
        if (bisimulation<1 || bisimulation>4) argp_usage(state);
        break;
    case 'l':
        if (arg[0] == 'f' && arg[1] == 'l') {
            leaftype = 0;
        } else if (arg[0] == 'f' && arg[1] == 'r') {
            leaftype = 1;
        } else if (arg[0] == 'g') {
            leaftype = 2;
        } else {
            argp_usage(state);
        }
        break;
    case 'v':
        verbosity = atoi(arg);
        if (verbosity<0 || verbosity>2) argp_usage(state);
        break;
    case 'm':
        merge_relations = 1;
        break;
    case 'r':
        reachable = 1;
        break;
    case 't':
        tau_action = atoi(arg);
        break;
    case 1:
        ordering = 1;
        break;
    case 2:
        table_sizes = arg;
        break;
    case 'c':
        if (arg[0] == 'f') {
            closure = 0;
        } else if (arg[0] == 's') {
            closure = 1;
            merge_relations = 1;
        } else if (arg[0] == 'r') {
            closure = 2;
            merge_relations = 1;
        } else {
            argp_usage(state);
        }
        break;
    case 'q':
        if (strncmp(arg, "pick", 4) == 0) {
            quotient_type = 4;
        } else if (strcmp(arg, "block") == 0) {
            quotient_type = 3;
        } else if (strcmp(arg, "block-s1") == 0) {
            quotient_type = 1;
        } else if (strcmp(arg, "block-s2") == 0) {
            quotient_type = 2;
        } else if (strcmp(arg, "test") == 0) {
            quotient_type = 5;
        } else {
            argp_usage(state);
        }
        break;
    case 'o':
        if (arg[0] == 'e') {
            output_type = 1;
        } else if (arg[0] == 's') {
            output_type = 2;
        } else {
            argp_usage(state);
        }
        break;
#ifdef HAVE_PROFILER
    case 'p':
        profile_filename = arg;
        break;
#endif
    case ARGP_KEY_ARG:
        if (state->arg_num == 0) model_filename = arg;
        else if (state->arg_num == 1) output_filename = arg;
        else argp_usage(state);
        break;
    case ARGP_KEY_END:
        if (state->arg_num < 1) argp_usage(state);
        if (output_filename != NULL && output_type == 0) argp_error(state, "Please set an output type with -o.");
        break;
    default:
        return ARGP_ERR_UNKNOWN;
    }
    return 0;
}

static struct argp argp = {options, parse_opt, "<model>", 0, 0, 0, 0};

double t_start;

double
wctime()
{
    struct timeval tv;
    gettimeofday(&tv, NULL);
    return (tv.tv_sec + 1E-6 * tv.tv_usec);
}

/**
 * Small helper function
 */
static char*
to_h(double size, char *buf)
{
    const char* units[] = {"B", "KB", "MB", "GB", "TB", "PB", "EB", "ZB", "YB"};
    int i = 0;
    for (;size>1024;size/=1024) i++;
    sprintf(buf, "%.*f %s", i, size, units[i]);
    return buf;
}

VOID_TASK_0(gc_start)
{
    INFO("(GC) Starting garbage collection...");
}

VOID_TASK_0(gc_end)
{
    INFO("(GC) Garbage collection done.");
}

VOID_TASK_1(main_lace, void*, arg)
{
    setlocale(LC_NUMERIC, "en_US.utf-8");

    t_start = wctime();

    int tablesize, maxtablesize, cachesize, maxcachesize;
    if (sscanf(table_sizes, "%d,%d,%d,%d", &tablesize, &maxtablesize, &cachesize, &maxcachesize) != 4) {
        INFO("Invalid string for --table-sizes, try e.g. --table-sizes=23,28,22,27");
        return;
    }
    if (tablesize < 10 || maxtablesize < 10 || cachesize < 10 || maxcachesize < 10 ||
            tablesize > 40 || maxtablesize > 40 || cachesize > 40 || maxcachesize > 40) {
        INFO("Invalid string for --table-sizes, must be between 10 and 40");
        return;
    }
    if (tablesize > maxtablesize) {
        INFO("Invalid string for --table-sizes, tablesize is larger than maxtablesize");
        return;
    }
    if (cachesize > maxcachesize) {
        INFO("Invalid string for --table-sizes, cachesize is larger than maxcachesize");
        return;
    }

    char buf[32];
    to_h((1ULL<<maxtablesize)*24+(1ULL<<maxcachesize)*36, buf);
    INFO("Sylvan allocates %s virtual memory for nodes table and operation cache.", buf);
    to_h((1ULL<<tablesize)*24+(1ULL<<cachesize)*36, buf);
    INFO("Initial nodes table and operation cache requires %s.", buf);

    sylvan_init_package(1LL<<tablesize, 1LL<<maxtablesize, 1LL<<cachesize, 1LL<<maxcachesize);
    sylvan_set_granularity(3);
    sylvan_init_mtbdd();
    gmp_init();
    sylvan_gc_hook_pregc(TASK(gc_start));
    sylvan_gc_hook_postgc(TASK(gc_end));

    /* Initialization done, now read model from file */

    SystemType sysType;
    LTS lts;
    CTMC ctmc;
    IMC imc;

    const char *dot = strrchr(model_filename, '.');
    if (dot) {
        if (strcmp(dot+1, "bdd") == 0) {
            BddLtsParser parser(model_filename);
            sysType = lts_type;
            lts = *parser.getLTS();
        } else if ((strcmp(dot+1, "xlts") == 0) || (strcmp(dot+1, "xctmc") == 0) || (strcmp(dot+1, "ximc") == 0) || (strcmp(dot+1, "xml") == 0)) {
            LeafType lt = float_type;
            if (leaftype == 1) lt = simple_fraction_type;
            if (leaftype == 2) lt = mpq_type;
            SystemParser reader(model_filename, 0, lt);
            sysType = reader.getType();
            if (sysType == lts_type) {
                lts = *reader.getLTS();
            } else if (sysType == ctmc_type) {
                ctmc = *reader.getCTMC();
            } else {
                imc = *reader.getIMC();
            }
        } else {
            fprintf(stderr, "Unknown extension '%s'!\n", dot+1);
            return;
        }
    } else {
        fprintf(stderr, "Unknown extension ''!\n");
        return;
    }

    INFO("Finished reading system from %s.", model_filename);

#ifdef HAVE_PROFILER
    if (profile_filename != NULL) ProfilerStart(profile_filename);
#endif

    BDD partition = mtbdd_false;
    if (sysType == lts_type && bisimulation == 1) {
        partition = CALL(min_lts_branching, lts);
    } else if (sysType == lts_type && bisimulation == 2) {
        partition = CALL(min_lts_strong, lts);
    } else if (sysType == lts_type && bisimulation == 3) {
        partition = CALL(min_lts_strong2, lts);
    } else if (sysType == lts_type && bisimulation == 4) {
        partition = CALL(min_lts_strong3, lts);
    } else if (sysType == ctmc_type) {
        partition = CALL(min_ctmc, ctmc);
    } else if (sysType == imc_type && bisimulation == 1) {
        partition = CALL(min_imc_branching, imc);
    } else if (sysType == imc_type && bisimulation == 2) {
        partition = CALL(min_imc_strong, imc);
    } else {
        fprintf(stderr, "Unsupported system/bisimulation combination!\n");
        return;
    }

    sylvan_protect(&partition);

#ifdef HAVE_PROFILER
    if (profile_filename != NULL) ProfilerStop();
#endif

    /* With "-q test" we dump the output from different algorithms that should produce
       the same results. This is a feature for testing/debugging. */
    if (quotient_type == 5) {
        if (sysType == ctmc_type) {
            writeSignatures("test-signatures", ctmc);

            INFO("");
            partition = trim_block_variables(partition);

            CTMC copy(ctmc), copy2(ctmc);
            Minimizations::minimize1(copy, partition);
            Minimizations::minimize2(copy2, partition);

            writeExplicitOutput("test-explicit1", copy);
            writeExplicitOutput("test-explicit2", copy2);

            INFO("");
            INFO("Now use the following two commands to test that the output is correct:");
            INFO("diff <(tail -n +3 test-signatures|sort) <(tail -n +5 test-explicit1|sort)");
            INFO("diff test-explicit1 test-explicit2");
        } else if (sysType == lts_type) {
            writeSignatures("test-signatures", lts);

            INFO("");
            partition = trim_block_variables(partition);

            LTS copy(lts), copy2(lts), copy3(lts);
            Minimizations::minimize1(copy, partition, 0);
            Minimizations::minimize1(copy2, partition, 1);
            Minimizations::minimize2(copy3, partition);

            writeExplicitOutput("test-explicit1", copy);
            writeExplicitOutput("test-explicit2", copy2);
            writeExplicitOutput("test-explicit3", copy3);

            INFO("");
            INFO("Now use the following three commands to test that the output is correct:");
            INFO("diff <(tail -n +3 test-signatures|sort) <(tail -n +5 test-explicit1|sort)");
            INFO("diff test-explicit1 test-explicit2");
            INFO("diff test-explicit1 test-explicit3");
        } else {
            fprintf(stderr, "You cannot test IMCs at this moment!\n");
        }
        return;
    }

    /* At this point, the signatures are not protected against garbage collection.
       We might as well free the memory. */
    free_refine_data();

    /* Run garbage collection, to remove influence from caching in the first part
       from measurements of the second part. */
    // sylvan_gc();

    /*
     * 1 = symbolic (by block nr) with standard operations
     * 2 = symbolic (by block nr) with standard operations, improved LTS algorithm
     * 3 = symbolic (by block nr) with custom operations
     * 4 = symbolic (by pick one)
     */

    if (output_type == 1 && quotient_type == 0) quotient_type = 3;
    if (output_type == 2 && quotient_type == 0) quotient_type = 4;

    if (quotient_type != 0) {
        INFO("");
        partition = trim_block_variables(partition);
    }

    if (quotient_type == 1) {
        /* Standard operations, block encoding, variant 1 */
        if (sysType == ctmc_type) Minimizations::minimize1(ctmc, partition);
        if (sysType == lts_type) Minimizations::minimize1(lts, partition, 0);
        if (sysType == imc_type) Minimizations::minimize1(imc, partition, 0);
    } else if (quotient_type == 2) {
        /* Standard operations, block encoding, variant 2 */
        if (sysType == ctmc_type) Minimizations::minimize1(ctmc, partition);
        if (sysType == lts_type) Minimizations::minimize1(lts, partition, 1);
        if (sysType == imc_type) Minimizations::minimize1(imc, partition, 1);
    } else if (quotient_type == 3) {
        /* Custom operations, block encoding */
        if (sysType == ctmc_type) Minimizations::minimize2(ctmc, partition);
        if (sysType == lts_type) Minimizations::minimize2(lts, partition);
        if (sysType == imc_type) Minimizations::minimize2(imc, partition);
    } else if (quotient_type == 4) {
        /* Custom operations, pick-random encoding */
        if (sysType == ctmc_type) Minimizations::minimize3(ctmc, partition);
        if (sysType == lts_type) Minimizations::minimize3(lts, partition);
        if (sysType == imc_type) Minimizations::minimize3(imc, partition);
    }

    if (output_filename != NULL) {
        /* Write output to file */
        if (output_type == 1) {
            if (sysType == ctmc_type) {
                writeExplicitOutput(output_filename, ctmc);
            } else if (sysType == lts_type) {
                writeExplicitOutput(output_filename, lts);
            } else if (sysType == imc_type) {
                writeExplicitOutput(output_filename, imc);
            }
        } else {
            if (sysType == ctmc_type) {
                writeSymbolicOutput(output_filename, ctmc);
            } else if (sysType == lts_type) {
                writeSymbolicOutput(output_filename, lts);
            } else if (sysType == imc_type) {
                writeSymbolicOutput(output_filename, imc);
            }
       }
    }

    sylvan_stats_report(stdout);

    (void)arg;
}

int
main(int argc, char **argv)
{
    argp_parse(&argp, argc, argv, 0, 0, 0);

    // boot program
    lace_init(workers, 1024*1024*16);
    lace_startup(0, TASK(main_lace), NULL);

    return 0;
}
