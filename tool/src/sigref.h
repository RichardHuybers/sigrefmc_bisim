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

#ifndef SIGREF_H
#define SIGREF_H

/* Cache identifiers */
#define CACHE_REFINE            (256LL<<42)
#define CACHE_INERT             (257LL<<42)
#define CACHE_SWAPPRIME         (258LL<<42)
#define CACHE_THREEAND          (259LL<<42)
#define CACHE_EQUI              (260LL<<42)
#define CACHE_ENCODE_BLOCK      (261LL<<42)
#define CACHE_DECODE_BLOCK      (262LL<<42)
#define CACHE_MARKOV_QUOTIENT   (263LL<<42)
#define CACHE_TRANS_QUOTIENT    (264LL<<42)
#define CACHE_STATES_QUOTIENT   (265LL<<42)
#define CACHE_PARTITION_ENUM    (266LL<<42)
#define CACHE_CONVERSE			(267LL<<42) // RICHARD
#define CACHE_BISIM		        (268LL<<42) // RICHARD
#define CACHE_RENAME	        (269LL<<42) // RICHARD

/* Configuration */
extern int bisimulation; // branching
extern int leaftype; // 0 = float, 1 = fraction, 2 = gmp
extern int verbosity; // default: no excessive node counting
extern int merge_relations; // merge relations to 1 relation
extern int closure; // 0 = fixpoint, 1 = squaring, 2 = recursive
extern int reachable; // 0 = no, 1 = yes
extern int tau_action; // action label of tau
extern int ordering; // 0 = s,t < a < B, 1 = s,t < B < a, default: 0

/* Obtain current wallclock time */
extern double t_start;
double wctime();
#define INFO(s, ...) { fprintf(stdout, "[% 8.2f] " s "\n", wctime()-t_start, ##__VA_ARGS__); fflush(stdout); }

#ifndef cas
#define cas(ptr, old, new) (__sync_bool_compare_and_swap((ptr),(old),(new)))
#endif

#endif
