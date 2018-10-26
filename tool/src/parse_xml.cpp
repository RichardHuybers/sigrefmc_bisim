/**
 * Heavily modified version of Ralf Wimmer's XML parser
 */

#include <algorithm> // for std::sort
#include <cstddef> // to fix errors with gmp
#include <iomanip>
#include <boost/lexical_cast.hpp>
#include "parse_xml.hpp"
#include <gmp.h>
#include <sylvan_gmp.h>
#include <sigref.h>

namespace sigref {

using namespace sylvan;

/**
 * @brief Tests if an xml-node has a given attribute
 */
inline bool
hasAttribute(const TiXmlNode* node, const char* att)
{
    assert(node->ToElement() != NULL);
    return node->ToElement()->Attribute(att) != NULL;
}

/**
 * @brief Reads the value of the given attribute of an xml-node and converts it to a string.
 */
inline std::string
readStringAttribute(const TiXmlNode* node, const char* att)
{
    assert(node != NULL && att != NULL && hasAttribute(node, att));
    const char *s = node->ToElement()->Attribute(att);
    if (s == NULL) throw ParseError("[ERROR] Attribute not found");
    return std::string(s);
}

/**
 * @brief Reads the value of the given attribute of an xml-node and converts it to an integer.
 */
inline unsigned int
readIntAttribute(const TiXmlNode* node, const char* att)
{
    const std::string numberString = readStringAttribute(node, att);
    try {
        return boost::lexical_cast<unsigned int>(numberString);
    } catch (boost::bad_lexical_cast &) {
        throw ParseError("[ERROR] String " + numberString + " is not a number");
    }
}

/**
  \brief Reads the value of the given attribute of an xml-node and converts it to a double.
 */
inline Mtbdd
readDoubleAttribute(const TiXmlNode* node, const char* att)
{
    const std::string numberString = readStringAttribute(node, att);
    try {
        size_t pos = 0;
        if ((pos = numberString.find('/')) != std::string::npos) {
            const std::string numerator = numberString.substr(0,pos);
            const std::string denominator = numberString.substr(pos+1);
            double value = boost::lexical_cast<double>(numerator)/boost::lexical_cast<double>(denominator);
            if (value == 0.0) return mtbdd_false;
            return Mtbdd::doubleTerminal(value);
        } else {
            double value = boost::lexical_cast<double>(numberString);
            if (value == 0.0) return mtbdd_false;
            return Mtbdd::doubleTerminal(value);
        }
    } catch(boost::bad_lexical_cast&) {
        throw ParseError("[ERROR] String " + numberString + " is not a number");
    }
}

inline Mtbdd
readMPQAttribute(const TiXmlNode* node, const char* att)
{
    const std::string numberString = readStringAttribute(node, att);
    mpq_t gmp_value;
    mpq_init(gmp_value);
    try {
        size_t pos = 0;
        if ((pos = numberString.find('.')) != std::string::npos) {
            mpf_t f_value;
            mpf_init(f_value);
            mpf_set_str(f_value, numberString.c_str(), 10);
            mpq_set_f(gmp_value, f_value);
            mpf_clear(f_value);
        } else {
            mpq_set_str(gmp_value, numberString.c_str(), 10);
        }
        if (mpq_sgn(gmp_value) == 0) {
            mpq_clear(gmp_value);
            return mtbdd_false;
        }
        MTBDD res = mtbdd_gmp(gmp_value);
        mpq_clear(gmp_value);
        return res;
    } catch(boost::bad_lexical_cast&) {
        throw ParseError("[ERROR] String " + numberString + " is not a number");
    }
}

inline Mtbdd
readSimpleFractionAttribute(const TiXmlNode* node, const char* att)
{
    const std::string numberString = readStringAttribute(node, att);

    try {
        size_t pos = 0;
        if ((pos = numberString.find('/')) != std::string::npos) {
            const std::string numerator = numberString.substr(0,pos);
            const std::string denominator = numberString.substr(pos+1);

            uint64_t num = ((uint64_t)boost::lexical_cast<unsigned int>(numerator));
            uint64_t den = ((uint64_t)boost::lexical_cast<unsigned int>(denominator));
            if (num == 0) return mtbdd_false;
            if (num > 0xffffffff || den > 0xffffffff) throw ParseError("[ERROR] Fraction " + numberString + " does not fit in 32-bit integers");
            return Mtbdd::fractionTerminal(num, den);
        } else if ((pos = numberString.find('.')) != std::string::npos) {
            const std::string before = numberString.substr(0,pos);
            const std::string after = numberString.substr(pos+1);
            uint64_t num = boost::lexical_cast<uint64_t>(before+after);
            uint64_t den = 1;
            for (unsigned int i=0; i<after.length(); i++) den *= 10;
            if (num > 0xffffffff || den > 0xffffffff) throw ParseError("[ERROR] Fraction " + numberString + " does not fit in 32-bit integers");
            if (num == 0) return mtbdd_false;
            return Mtbdd::fractionTerminal(num, den);
        } else {
            uint64_t num = (uint64_t)boost::lexical_cast<unsigned int>(numberString);
            if (num == 0) return mtbdd_false;
            if (num > 0xffffffff) throw ParseError("[ERROR] Fraction " + numberString + " does not fit in 32-bit integers");
            return Mtbdd::fractionTerminal(num, 1);
        }
    } catch(boost::bad_lexical_cast&) {
        throw ParseError("[ERROR] String " + numberString + " is not a number, or x/y does not fit in 32-bit integers");
    }
}

SystemParser::SystemParser(const char* filename, unsigned int verbosity, LeafType leaf_type)
{
    // Open the document
    TiXmlDocument document = TiXmlDocument(filename);
    if (!document.LoadFile()) {
        throw ParseError("[ERROR] Could not load the input file.");
    }

    // Get the root node of the XML-document
    TiXmlNode* rootNode = document.RootElement();
    if (rootNode == NULL) {
        throw ParseError("[ERROR] Could not access the root node of the XML-tree");
    }

    // Find out the type of the transition system (lts, ctmc, imc)
    const std::string type_str = readStringAttribute(rootNode, "type");
    if (type_str == "lts") system_type = lts_type;
    else if (type_str == "ctmc") system_type = ctmc_type;
    else if (type_str == "imc") system_type = imc_type;
    else system_type = lts_type;

    this->leaf_type = leaf_type;

    // Traverse the children of the root node and collect the pointers to the parts we need.
    TiXmlNode* varinfoNode = NULL;
    TiXmlNode* initialstateNode = NULL;
    TiXmlNode* transNode = NULL;
    TiXmlNode* markovtransNode = NULL;
    TiXmlNode* initialpartitionNode = NULL;
    TiXmlNode* tauNode = NULL;

    for (TiXmlNode* currentNode = rootNode->FirstChild();
         currentNode != NULL;
         currentNode = currentNode->NextSibling()) {

        if (currentNode->ToElement() == NULL) continue;

        const char* const name = currentNode->ToElement()->Value();

        if (strcmp(name, "variables") == 0) {
            varinfoNode = currentNode;
        } else if (strcmp(name, "dd") == 0) {
            std::string bdd_type = readStringAttribute(currentNode, "type");
            if (bdd_type == "initial_state") {
                initialstateNode = currentNode;
            } else if (bdd_type == "trans") {
                transNode = currentNode;
            } else if (bdd_type == "markov_trans") {
                markovtransNode = currentNode;
            } else if (bdd_type == "tau") {
                tauNode = currentNode;
            }
        } else if (strcmp(name, "initial_partition") == 0) {
            initialpartitionNode = currentNode;
        }
    }

    // Check if we have found the variable information
    if (varinfoNode == NULL) {
        throw ParseError("[ERROR] No variable information found!");
    }

    // Check if the correct information exists for the system type
    switch (system_type) {
    case lts_type:
        if (markovtransNode != NULL) {
            throw ParseError("[ERROR] LTS must not have any Markov transitions!");
        }
        if (transNode == NULL) {
            throw ParseError("[ERROR] LTS must have an interactive transition relation!");
        }
        break;
    case ctmc_type:
        if (transNode != NULL) {
            throw ParseError("[ERROR] CTMCs must not have any interactive transitions!");
        }
        if (markovtransNode == NULL) {
            throw ParseError("[ERROR] CTMCs must have a Markov transition relation!");
        }
        break;
    case imc_type:
        if (transNode == NULL) {
            throw ParseError("[ERROR] IMCs must have an interactive transition relation!");
        }
        if (markovtransNode == NULL) {
            throw ParseError("[ERROR] IMCs must have a Markov transition relation!");
        }
        break;
    }

        // Parse the variable information and create the BDD variables
        // together with an appropriate order for refinement
        if (verbosity > 0) std::cout << "[INFO] Creating BDD variables ... " << std::flush;
        createVariables(varinfoNode);
        if (verbosity > 0) std::cout << "finished." << std::endl;

        // Build the BDDs/ADDs for all parts
        if (verbosity > 0) std::cout << "[INFO] Building BDDs ... " << std::flush;

        std::vector<std::pair<Bdd, Bdd>> transitions;
        Bdd _transitions = Bdd::bddZero();
        if (transNode != NULL) {
            _transitions = nodeToBdd(transNode);
            transitions.push_back(std::make_pair(_transitions, varS * varT));
        }

        Mtbdd markov_transitions;
        if (markovtransNode != NULL) markov_transitions = nodeToMtbdd(markovtransNode);

        Bdd tau;
        if (tauNode != NULL) tau = nodeToBdd(tauNode);
        else {
            // Default value of tau: 0
            int action_bits = sylvan_set_count(varA.GetBDD());
            std::vector<uint8_t> tau_value;
            for (int i=0; i<action_bits; i++) {
                tau_value.push_back(tau_action & (1LL<<(action_bits-i-1)) ? 1 : 0);
            }
            tau = Bdd::bddCube(varA, tau_value);
        }

        Bdd initial_state;
        if (initialstateNode != NULL) initial_state = nodeToBdd(initialstateNode);

        Bdd states = computeStateSpace(_transitions, markov_transitions);

        std::vector<Bdd> initial_partition;
        if (initialpartitionNode != NULL) {
            for (TiXmlNode* currentNode = initialpartitionNode->FirstChild();
                 currentNode != NULL; currentNode = currentNode->NextSibling()) {
                initial_partition.push_back(nodeToBdd(currentNode));
            }
        }
        if (initial_partition.size() == 0) initial_partition.push_back(states);
        if (verbosity > 0) std::cout << "finished." << std::endl;

        // Fill the right system with information
        switch (system_type) {
        case lts_type:
            lts.transitions = transitions;
            lts.states = states;
            lts.tau = tau;
            lts.initialStates = initial_state;
            lts.initialPartition = initial_partition;
            lts.varS = varS;
            lts.varT = varT;
            lts.varA = varA;
            break;

        case imc_type:
            imc.transitions = transitions;
            imc.markov_transitions = markov_transitions;
            imc.states = states;
            imc.tau = tau;
            imc.initialStates = initial_state;
            imc.initialPartition = initial_partition;
            imc.varS = varS;
            imc.varT = varT;
            imc.varA = varA;
            break;

        case ctmc_type:
            ctmc.markov_transitions = markov_transitions;
            ctmc.states = states;
            ctmc.initialStates = initial_state;
            ctmc.initialPartition = initial_partition;
            ctmc.varS = varS;
            ctmc.varT = varT;
            break;

        default:
            break;
        }
}

SystemParser::~SystemParser()
{
}

void
SystemParser::createVariables(TiXmlNode *varinfoNode) {
    unsigned int maxIndex = 0;
    int numS = 0;
    int numA = 0;

    // Calculate highest index, number of state variables, number of action variables
    for (TiXmlNode* currentNode = varinfoNode->FirstChild();
         currentNode != NULL;
         currentNode = currentNode->NextSibling()) {
        const unsigned int index = readIntAttribute(currentNode, "index");
        if (index > maxIndex) maxIndex = index;

        const std::string type = readStringAttribute(currentNode, "type");
        if (type == "ps") numS++;
        else if (type == "in") numA++;
    }

    std::vector<int> state_vars;
    std::vector<uint32_t> action_vars;
    std::map<int, int> state_to_next_vars;

    // Gather all
    for (TiXmlNode* currentNode = varinfoNode->FirstChild();
         currentNode != NULL; currentNode = currentNode->NextSibling()) {
        const unsigned int index = readIntAttribute(currentNode, "index");
        const std::string type = readStringAttribute(currentNode, "type");
        if (type == "ps") {
            state_vars.push_back(index);
            state_to_next_vars[index] = readIntAttribute(currentNode, "corr");
        } else if (type == "in") {
            action_vars.push_back(index);
        }
    }

    std::sort(state_vars.begin(), state_vars.end());
    std::sort(action_vars.begin(), action_vars.end());

    std::vector<uint32_t> bdd_state_vars;
    std::vector<uint32_t> bdd_prime_vars;
    std::vector<uint32_t> bdd_action_vars;

    for (int i=0; i < numS; i++) {
        bdd_state_vars.push_back(i*2);
        bdd_prime_vars.push_back(i*2+1);
        var_to_mtbdd[state_vars[i]] = Mtbdd::mtbddVar(i*2);
        var_to_mtbdd[state_to_next_vars[state_vars[i]]] = Mtbdd::mtbddVar(i*2+1);
    }

    for (int i=0; i < numA; i++) {
        bdd_action_vars.push_back(1000000+i);
        var_to_mtbdd[action_vars[i]] = Mtbdd::mtbddVar(1000000+i);
    }

    varS = Bdd::VariablesCube(bdd_state_vars);
    varT = Bdd::VariablesCube(bdd_prime_vars);
    varA = Bdd::VariablesCube(bdd_action_vars);
}

Bdd
SystemParser::nodeToBdd(const TiXmlNode *node)
{
    LACE_ME;
    if (leaf_type == mpq_type) return gmp_strict_threshold_d(nodeToMtbdd(node).GetMTBDD(), 0);
    else return nodeToMtbdd(node).BddStrictThreshold(0);
}

Mtbdd
SystemParser::nodeToMtbdd(const TiXmlNode* node)
{
    // Have we reached a leaf of the (MT)BDD?
    if (hasAttribute(node, "const_value")) {
        if (leaf_type == float_type) {
            return readDoubleAttribute(node, "const_value");
        } else if (leaf_type == simple_fraction_type) {
            return readSimpleFractionAttribute(node, "const_value");
        } else if (leaf_type == mpq_type) {
            return readMPQAttribute(node, "const_value");
        }
    }

    // The node references another node
    if (hasAttribute(node, "node_ref")) {
        const std::map<std::string, Mtbdd>::const_iterator it =
                build_table.find(readStringAttribute(node, "node_ref"));
        assert(it != build_table.end());
        return it->second;
    }

    // Proper internal node
    const TiXmlNode* child = node->FirstChild();

    // Must have internal id and a variable index
    assert(strcmp(child->Value(), "dd_node")==0);
    assert(hasAttribute(child, "id"));
    assert(hasAttribute(child, "index"));

    // Read the attributes of the node
    const std::string id = readStringAttribute(child, "id");
    const unsigned int index = readIntAttribute(child, "index");

    // Get the then-child of the node
    const TiXmlNode* then_node = child->FirstChild();
    assert(then_node != NULL);
    assert(strcmp(then_node->Value(), "dd_then") == 0);
    Mtbdd then_result = nodeToMtbdd(then_node);

    // Get the else-child of the node
    const TiXmlNode* else_node = then_node->NextSibling();
    assert(else_node != NULL);
    assert(strcmp(else_node->Value(), "dd_else") == 0);
    Mtbdd else_result = nodeToMtbdd(else_node);

    const Mtbdd result = var_to_mtbdd[index].Ite(then_result, else_result);

    if (build_table.find(id) != build_table.end()) {
        assert(build_table[id] == result);
    } else {
        build_table[id] = result;
    }

    return result;
}

Bdd
SystemParser::computeStateSpace(const Bdd& transitions, const Mtbdd& markov_transitions) const {
    LACE_ME;
    Bdd markovs;
    if (leaf_type == mpq_type) markovs = Bdd(gmp_strict_threshold_d(markov_transitions.GetMTBDD(), 0));
    else markovs = markov_transitions.BddStrictThreshold(0);

    // Compute all transitions
    const Bdd all_trans = transitions.ExistAbstract(varA) + markovs;

    // Take all transitions.
    Bdd states = Bdd::bddOne().RelNext(all_trans, varS*varT); // all "to" states
    states += all_trans.ExistAbstract(varT); // all "from" states
    return states;
}

}
