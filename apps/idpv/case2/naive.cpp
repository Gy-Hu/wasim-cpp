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

#include <iomanip>
#include <chrono>
#include <gmp.h>
#include <gmpxx.h>
#include <iostream>
#include <algorithm>
#include <random>

#include "btor_sweeping.h"  // Remove this line if your project doesn't need it.
#include "smt-switch/utils.h"

using namespace smt;
using namespace std;
using namespace wasim;

std::chrono::time_point<std::chrono::high_resolution_clock> last_time_point;
void print_time() {
    auto now = std::chrono::high_resolution_clock::now();
    auto elapsed_time = std::chrono::duration_cast<std::chrono::milliseconds>(now - last_time_point).count();
    last_time_point = now;  // Update last time point
    std::cout << "[" << elapsed_time / 1000.0 << " s]  ";
}

int main() {
    auto program_start_time = std::chrono::high_resolution_clock::now();
    last_time_point = program_start_time;

    // 1) Create solver
    SmtSolver solver = BoolectorSolverFactory::create(false);
    solver->set_logic("QF_UFBV");
    solver->set_opt("incremental", "true");
    solver->set_opt("produce-models", "true");
    solver->set_opt("produce-unsat-assumptions", "true");

    // 2) Read BTOR2 file and build Transition System
    TransitionSystem sts1(solver);
    // Change this to your actual BTOR2 file path
    BTOR2Encoder btor_parser1("../design/smt-sweeping/case2/cond_mul.btor2", sts1, "a::");

    // 3) Get control bit a::control and output decision bit a::result
    auto a_control = sts1.lookup("a::control");
    auto result = sts1.lookup("a::result");

    // 4) Construct expression: control == 4'b1000
    //    Create a 4-bit BV constant "1000" (binary)
    std::string aa = "1000";
    Sort bv_sort = solver->make_sort(BV, 4);
    auto a_ctl_val = solver->make_term(aa, bv_sort, 2);  // 2nd prarater - bit-width，3rd- binary
    auto control_equals_1000 = solver->make_term(Equal, a_control, a_ctl_val);

    // 5) Property to verify: when control==4'b1000, result should be 0
    //    Which means: (control==4'b1000) => (result == 0)
    //    In SMT, this can be written as: Implies(control_equals_1000, Not(result))
    auto not_result = solver->make_term(Not, result);
    auto implication = solver->make_term(Implies, control_equals_1000, not_result);

    // 6) During verification, we typically assert the negation of the property
    //    We want (control==4'b1000) && result=1 to violate this property
    //    If the result is UNSAT, it means no counterexample exists and the property holds
    auto neg_property = solver->make_term(Not, implication);
    solver->assert_formula(neg_property);

    // 7) Solve and output results
    auto res = solver->check_sat();
    if (res.is_unsat()) {
        std::cout << "UNSAT: No counterexample exists." << std::endl;
        std::cout << "Property holds: when control == 4'b1000, the two multipliers match (result=0)." << std::endl;
    } else {
        std::cout << "SAT: Found a counterexample." << std::endl;
        std::cout << "Property fails: when control == 4'b1000, result can be 1 (mismatch)." << std::endl;
        // Print a model for debugging
        std::cout << "Model example:" << std::endl;
        std::cout << "  control = " << solver->get_value(a_control) << std::endl;
        std::cout << "  result  = " << solver->get_value(result) << std::endl;
    }

    auto program_end_time = std::chrono::high_resolution_clock::now();
    auto total_time = std::chrono::duration_cast<std::chrono::milliseconds>(
                        program_end_time - program_start_time)
                        .count();
    std::cout << "Total execution time: " << total_time / 1000.0 << " s" << std::endl;
    return 0;
}