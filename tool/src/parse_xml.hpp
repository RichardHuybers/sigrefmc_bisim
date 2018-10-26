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

#ifndef __PARSER_XML__HPP__
#define __PARSER_XML__HPP__

#include <string>
#include <map>
#include <vector>
#include <numeric>
#include <tinyxml.h>

#include <sylvan.h>
#include <sylvan_obj.hpp>
#include <systems.hpp>

namespace sigref {

class ParseError: std::exception
{
public:
    inline ParseError() throw() { }
    inline ParseError(std::string msg) throw(): message(msg.c_str()) { std::cerr << msg << std::endl; }
    inline ParseError(const char* msg) throw(): message(msg) { std::cerr << msg << std::endl; }
    virtual const char * what () const throw() { return message; }

private:
    const char* message;
};

typedef enum {
    lts_type = 0,
    ctmc_type = 1,
    imc_type = 2
} SystemType;

typedef enum {
    float_type = 0,
    simple_fraction_type = 1,
    mpq_type = 2,
} LeafType;

class SystemParser {
public:
    SystemParser(const char* _filename, unsigned int _verbosity, LeafType leaf_type);
    ~SystemParser();

    SystemType getType() const {
        return system_type;
    }

    LTS* getLTS() {
        if (system_type != lts_type) throw ParseError("[ERROR] System is not an LTS!");
        return &lts;
    }

    IMC* getIMC() {
        if (system_type != imc_type) throw ParseError("[ERROR] System is not an IMC!");
        return &imc;
    }

    CTMC* getCTMC() {
        if (system_type != ctmc_type) throw ParseError("[ERROR] System is not a CTMC!");
        return &ctmc;
    }

private:
    void createVariables(TiXmlNode *varinfoNode);

    sylvan::Bdd nodeToBdd(const TiXmlNode* node);
    sylvan::Mtbdd nodeToMtbdd(const TiXmlNode* node);

    sylvan::Bdd computeStateSpace(const sylvan::Bdd& transitions, const sylvan::Mtbdd& markov_transitions) const;

    SystemType system_type;
    LTS lts;
    IMC imc;
    CTMC ctmc;

    LeafType leaf_type;

    mutable std::map<std::string, sylvan::Mtbdd> build_table;
    sylvan::Bdd varS;
    sylvan::Bdd varT;
    sylvan::Bdd varA;
    std::map<int, sylvan::Mtbdd> var_to_mtbdd;
};

} // end namespace sigref

#endif
