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

#ifndef __PARSER_BDD__HPP__
#define __PARSER_BDD__HPP__

#include <string>
#include <map>
#include <vector>
#include <numeric>
#include <tinyxml.h>

#include <sylvan.h>
#include <sylvan_obj.hpp>
#include <systems.hpp>

namespace sigref {

class BddLtsParser {
public:
    BddLtsParser(const char* _filename);
    ~BddLtsParser();

    LTS* getLTS() {
        return &lts;
    }

private:
    LTS lts;
};

} // end namespace sigref

#endif
