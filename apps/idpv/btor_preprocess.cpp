#include "smt-switch/utils.h"
#include "frontend/btor2_encoder.h"
#include "utils/logger.h"
#include "framework/ts.h"
#include "smt-switch/boolector_factory.h"
#include "smt-switch/identity_walker.h"

#include <iostream>
#include <string>
#include <fstream>
#include <unordered_set>
#include <queue>
#include <stack>

using namespace wasim;
using namespace smt;
using namespace std;

class ConeOfInfluence : public IdentityWalker
{
public:
    ConeOfInfluence(SmtSolver & solver) : IdentityWalker(solver, false) {}

    unordered_set<Term> get_cone(const Term & root) {
        Term root_copy = root;
        visit_and_analyze(root_copy);
        return cone_;
    }

protected:
    WalkerStepResult visit_term(Term & term) override {
        if (cone_.find(term) != cone_.end()) {
            return Walker_Continue;
        }

        // Skip if term is a constant value that doesn't affect the property
        if (term->is_value()) {
            if (is_neutral_constant(term)) {
                std::cout << "Skipping neutral constant: " << term->to_string() << std::endl;
                return Walker_Continue;
            }
        }

        // Analyze operation type and decide whether to include term
        if (!term->is_value() && !term->is_symbol()) {
            Op op = term->get_op();
            if (can_eliminate_term(term, op)) {
                std::cout << "Skipping eliminable term: " << term->to_string() << std::endl;
                return Walker_Continue;
            }
        }

        cone_.insert(term);
        return Walker_Continue;
    }

private:
    unordered_set<Term> cone_;
    
    void visit_and_analyze(Term & root) {
        stack<pair<Term, bool>> node_stack;
        unordered_set<Term> visited;
        
        node_stack.push({root, false});
        
        while (!node_stack.empty()) {
            auto [current, is_processed] = node_stack.top();
            node_stack.pop();
            
            if (!is_processed) {
                // Push back the node as processed
                node_stack.push({current, true});
                
                // Push all children
                for (auto it = current->begin(); it != current->end(); ++it) {
                    if (visited.find(*it) == visited.end()) {
                        node_stack.push({*it, false});
                        visited.insert(*it);
                    }
                }
            } else {
                // Process the node
                visit_term(current);
            }
        }
    }

    bool is_neutral_constant(const Term & term) const {
        // Check if the constant is a neutral value (like 0 for OR, 1 for AND)
        if (term->is_value()) {
            string val = term->to_string();
            if (val == "#b0" || val == "#b1") {
                return true;
            }
        }
        return false;
    }

    bool can_eliminate_term(const Term & term, const Op & op) const {
        // Analyze if the term can be eliminated based on its operation
        if (op.is_null()) return false;

        switch (op.prim_op) {
            case PrimOp::BVAnd:
            case PrimOp::BVOr: {
                // Check if one of the operands is a neutral value
                Term term_copy = term;  // Create non-const copy
                for (auto it = term_copy->begin(); it != term_copy->end(); ++it) {
                    if ((*it)->is_value() && is_neutral_constant(*it)) {
                        return true;
                    }
                }
                break;
            }
            
            case PrimOp::Concat: {
                // If concatenating with zero, we might be able to eliminate
                Term term_copy = term;  // Create non-const copy
                for (auto it = term_copy->begin(); it != term_copy->end(); ++it) {
                    if ((*it)->is_value() && (*it)->to_string() == "#b0") {
                        return true;
                    }
                }
                break;
            }

            default:
                break;
        }
        return false;
    }
};

class BtorPreprocessor {
private:
    SmtSolver solver_;
    TransitionSystem ts_;
    unordered_set<Term> cone_vars_;
    
public:
    BtorPreprocessor(SmtSolver & solver) : solver_(solver), ts_(solver) {}

    void preprocess(const string & input_file, const string & output_file) {
        // parse btor2 file
        BTOR2Encoder encoder(input_file, ts_);

        // compute cone of influence starting from properties
        compute_cone_of_influence();

        // Get base filename without extension
        string base_output = output_file.substr(0, output_file.find_last_of("."));
        
        // Get properties
        TermVec props = ts_.prop();
        
        if (props.empty()) {
            // If no properties, just dump the original way
            dump_smt2(output_file, props);
        } else {
            // Generate separate files for each property
            for (size_t i = 0; i < props.size(); i++) {
                TermVec single_prop = {props[i]};
                string prop_file = base_output + "_prop" + to_string(i) + ".smt2";
                dump_smt2(prop_file, single_prop);
            }
        }
    }

private:
    void compute_cone_of_influence() {
        ConeOfInfluence coi(solver_);
        
        // Start from properties
        TermVec props = ts_.prop();
        for (const Term & prop : props) {
            auto prop_cone = coi.get_cone(prop);
            cone_vars_.insert(prop_cone.begin(), prop_cone.end());
        }

        // Include variables from transition relation that affect properties
        Term trans = ts_.trans();
        auto trans_cone = coi.get_cone(trans);
        cone_vars_.insert(trans_cone.begin(), trans_cone.end());

        // Include variables from initial state that affect properties
        Term init = ts_.init();
        auto init_cone = coi.get_cone(init);
        cone_vars_.insert(init_cone.begin(), init_cone.end());

        // Include variables from constraints
        for (const auto & c : ts_.constraints()) {
            auto constraint_cone = coi.get_cone(c.first);
            cone_vars_.insert(constraint_cone.begin(), constraint_cone.end());
        }
    }

    bool is_in_cone(const Term & var) const {
        // For debugging
        if (cone_vars_.find(var) == cone_vars_.end()) {
            std::cout << "Term not in cone: " << var->to_string() << std::endl;
            return false;
        }
        return true;
    }

    void dump_smt2(const string & output_file, const TermVec & props_to_check) {
        ofstream out(output_file);
        if (!out.is_open()) {
            throw runtime_error("Cannot open output file: " + output_file);
        }

        // write header
        out << ";; Generated by IDPV Btor2 Preprocessor" << endl;
        out << "(set-logic QF_BV)" << endl;

        // declare input variables in cone
        for (const Term & var : ts_.inputvars()) {
            if (is_in_cone(var)) {
                out << "(declare-fun |" << var->to_string() 
                    << "| () " << var->get_sort()->to_string() << ")" << endl;
            }
        }

        // declare state variables in cone
        for (const Term & var : ts_.statevars()) {
            if (is_in_cone(var)) {
                out << "(declare-fun |" << var->to_string() 
                    << "| () " << var->get_sort()->to_string() << ")" << endl;
            }
        }

        // write initial state constraints if they're in the cone
        Term init = ts_.init();
        if ((!init->is_value() || init != solver_->make_term(true)) && is_in_cone(init)) {
            string init_str = init->to_string();
            out << "(assert " << init_str << ")" << endl;
        }

        // write transition system constraints if they're in the cone
        Term trans = ts_.trans();
        if ((!trans->is_value() || trans != solver_->make_term(true)) && is_in_cone(trans)) {
            string trans_str = trans->to_string();
            out << "(assert " << trans_str << ")" << endl;
        }

        // write constraints that are in the cone
        for (const auto & c : ts_.constraints()) {
            if (is_in_cone(c.first)) {
                string constraint_str = c.first->to_string();
                out << "(assert " << constraint_str << ")" << endl;
            }
        }

        // write property constraints - negate for bad properties
        if (!props_to_check.empty()) {
            if (props_to_check.size() == 1) {
                if (is_in_cone(props_to_check[0])) {
                    string prop_str = props_to_check[0]->to_string();
                    out << "(assert (not " << prop_str << "))" << endl;
                }
            } else {
                bool any_in_cone = false;
                string and_expr = "(assert (not (and";
                for (const Term & prop : props_to_check) {
                    if (is_in_cone(prop)) {
                        string prop_str = prop->to_string();
                        and_expr += " " + prop_str;
                        any_in_cone = true;
                    }
                }
                and_expr += ")))";
                if (any_in_cone) {
                    out << and_expr << endl;
                }
            }
        }

        // end
        out << "(check-sat)" << endl;
        out << "(exit)" << endl;
        out.close();
    }
};

int main(int argc, char ** argv) {
    if (argc != 3) {
        cerr << "Usage: " << argv[0] << " <input.btor2> <output.smt2>" << endl;
        return 1;
    }

    try {
        SmtSolver solver = BoolectorSolverFactory::create(false);
        solver->set_logic("QF_BV");
        solver->set_opt("produce-models", "true");
        solver->set_opt("incremental", "true");
        BtorPreprocessor preprocessor(solver);
        preprocessor.preprocess(argv[1], argv[2]);
        cout << "Preprocessing completed successfully." << endl;
        return 0;
    }
    catch (const exception & e) {
        cerr << "Error: " << e.what() << endl;
        return 1;
    }
}
