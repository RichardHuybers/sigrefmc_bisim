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

#include <systems.hpp>

#ifndef SIGREF_WRITER_H
#define SIGREF_WRITER_H

using namespace sylvan;

namespace sigref {

void writeSignatures(const char *filename, CTMC& ctmc);
void writeSignatures(const char *filename, LTS& lts);

void writeExplicitOutput(const char* filename, CTMC &ctmc);
void writeExplicitOutput(const char* filename, LTS &lts);
void writeExplicitOutput(const char* filename, IMC &imc);

void writeSymbolicOutput(const char *filename, CTMC& ctmc);
void writeSymbolicOutput(const char *filename, LTS& ctmc);
void writeSymbolicOutput(const char *filename, IMC& imc);

}

#endif
