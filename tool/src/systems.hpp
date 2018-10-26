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

#ifndef __SYSTEMS__HPP__
#define __SYSTEMS__HPP__

#include <map>
#include <vector>

#include <sylvan.h>
#include <sylvan_obj.hpp>

namespace sigref {

class CTMC;
class LTS;
class IMC;

class StateSystem {
    friend class SystemParser;
    friend class BddLtsParser;
    friend class Minimizations;

    sylvan::Bdd states;
    sylvan::Bdd initialStates;
    std::vector<sylvan::Bdd> initialPartition;

    sylvan::Bdd varS;
    sylvan::Bdd varT;
    sylvan::Bdd varA;

public:
    sylvan::Bdd getStates() const { return states; }
    sylvan::Bdd getInitialStates() const { return initialStates; }
    std::vector<sylvan::Bdd> getInitialPartition() const { return initialPartition; }
    sylvan::Bdd getVarS() const { return varS; }
    sylvan::Bdd getVarT() const { return varT; }
    sylvan::Bdd getVarA() const { return varA; }
};

class LTS: public StateSystem
{
    friend class SystemParser;
    friend class BddLtsParser;
    friend class Minimizations;

    std::vector<std::pair<sylvan::Bdd,sylvan::Bdd>> transitions;
    sylvan::Bdd tau;

public:
    std::vector<std::pair<sylvan::Bdd,sylvan::Bdd>> getTransitions() const { return transitions; }
    sylvan::Bdd getTau() const { return tau; }
};

class CTMC: public StateSystem
{
    friend class SystemParser;
    friend class Minimizations;

    sylvan::Mtbdd markov_transitions;

public:
    sylvan::Mtbdd getMarkovTransitions() const { return markov_transitions; }
};

class IMC: public LTS {
    friend class SystemParser;
    friend class Minimizations;

    sylvan::Mtbdd markov_transitions;

public:
    sylvan::Mtbdd getMarkovTransitions() const { return markov_transitions; }
};

} // end namespace sigref

#endif
