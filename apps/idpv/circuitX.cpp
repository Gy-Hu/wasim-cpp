#include "assert.h"
#include "config/testpath.h"
#include "framework/symsim.h"
#include "framework/ts.h"
#include "frontend/btor2_encoder.h"
#include "smt-switch/bitwuzla_factory.h"
#include "smt-switch/boolector_factory.h"
#include "smt-switch/identity_walker.h"
#include "smt-switch/smtlib_reader.h"
#include "smt-switch/substitution_walker.h"
#include "smt-switch/utils.h"
#include <iostream>

using namespace smt;
using namespace std;
using namespace wasim;

int main() {
    // Create SMT solver with proper configuration
    SmtSolver s = BoolectorSolverFactory::create(false);
    s->set_logic("QF_BV");
    s->set_opt("incremental", "true");
    s->set_opt("produce-models", "true");
    s->set_opt("produce-unsat-assumptions", "true");
    
    // Create transition system and parse BTOR2 file
    TransitionSystem ts(s);
    BTOR2Encoder btor_parser("../design/test/circuitX_case0.btor2", ts);

    // Get the input variables L and S
    Term L = ts.lookup("L");
    Term S = ts.lookup("S");
    Term D = ts.lookup("D");

    // Create a second copy of S for comparison
    Term S2 = s->make_symbol("S2", S->get_sort());

    // Create second copy of the circuit output using S2
    Term D2 = s->substitute(D, {{S, S2}});

    // Add constraint: S ≠ S2 (to make sure we're testing different S values)
    s->assert_formula(s->make_term(Distinct, S, S2));
    
    // The condition: D1 and D2 must be equal (output should be independent of S)
    Term condition = s->make_term(Equal, D, D2);
    s->assert_formula(condition);
    
    Result r = s->check_sat();
    
    if (r.is_sat()) {
        // If SAT, we found an L value that makes D independent of S
        cout << "Solution found! L value that makes D independent of S:" << endl;
        cout << "L = " << s->get_value(L)->to_string() << endl;
        cout << "Verification with two different S values:" << endl;
        cout << "S1 = " << s->get_value(S)->to_string() << endl;
        cout << "S2 = " << s->get_value(S2)->to_string() << endl;
        cout << "D1 = " << s->get_value(D)->to_string() << " (should equal D2)" << endl;
        cout << "D2 = " << s->get_value(D2)->to_string() << " (should equal D1)" << endl;

        // Additional verification: try all possible S values for the found L
        Term L_val = s->get_value(L);
        s->push();
        s->assert_formula(s->make_term(Equal, L, L_val));
        
        cout << "\nVerifying that this L value works for all S values..." << endl;
        
        // Try to find any S1, S2 that give different outputs
        Term different_outputs = s->make_term(Distinct, D, D2);
        s->assert_formula(different_outputs);
        
        Result verify = s->check_sat();
        if (verify.is_unsat()) {
            cout << "Verified: This L value makes D independent of S for all possible S values!" << endl;
        } else {
            cout << "Error: Found counter-example where outputs differ:" << endl;
            cout << "S1 = " << s->get_value(S)->to_string() << endl;
            cout << "S2 = " << s->get_value(S2)->to_string() << endl;
            cout << "D1 = " << s->get_value(D)->to_string() << endl;
            cout << "D2 = " << s->get_value(D2)->to_string() << endl;
        }
        s->pop();
    } else {
        // If UNSAT, no L value exists that makes D independent of S
        cout << "No solution exists: D always depends on S for all L values." << endl;
    }
    
    return 0;
}
