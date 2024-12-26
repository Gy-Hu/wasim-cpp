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

#include "btor_sweeping.h"
#include "smt-switch/utils.h"

using namespace smt;
using namespace std;
using namespace wasim;

template <typename T, typename... Rest>
inline void hashCombine(std::size_t & seed, T const & v, Rest &&... rest)
{
  std::hash<T> hasher;
  seed ^= hasher(v) + 0x9e3779b9 + (seed << 6) + (seed >> 2);
  (int[]){ 0, (hashCombine(seed, std::forward<Rest>(rest)), 0)... };
}

class NodeData {
private:
    Term term;
    size_t bit_width;
    std::vector<BtorBitVector> simulation_data;
public:
    NodeData() : term(nullptr), bit_width(0) {} 

    NodeData(const Term & t) : term(t), bit_width(0) {}

    NodeData(const Term & t, const size_t & bw) : term(t), bit_width(bw) {}

    Term get_term() const { return term; }
    
    size_t get_bit_width() const { return bit_width; }
    
    const std::vector<BtorBitVector>& get_simulation_data() const {
        return simulation_data; 
    }

    void add_data(const BtorBitVector & data) {
        simulation_data.push_back(data);
    }

    size_t hash(const std::vector<BtorBitVector>& data) const {
        if (data.empty()) {
            return 0;
        }

        size_t hash_val = 0;
        for(const auto v : data) {
            auto clean_val = std::string(btor_bv_to_char(&v));
            assert(clean_val.substr(0, 2) != "#b");
            hashCombine(hash_val, clean_val);
        }
        return hash_val;
    }
};

void create_lut(Term term, std::unordered_map<std::string, std::string>& lut) {
    Term current = term;
    while (current->get_op().prim_op == PrimOp::Store) {
        auto children = TermVec(current->begin(), current->end());
        if (children.size() != 3) {
            throw std::runtime_error("Store operation should have exactly 3 children");
        }
        // store：array、index、value
        auto array = children[0];   // original array
        auto index = children[1];   // stored position
        auto value = children[2];   // sotred value

        lut[index->to_string().substr(2)] = value->to_string().substr(2);
        current = array; // next iteration
    }
}

void btor_bv_operation(const smt::Op& op, 
                      const BtorBitVector& btor_child_1, 
                      const BtorBitVector& btor_child_2, 
                      NodeData &nd) {
    if(op.prim_op == PrimOp::BVAdd) {
        // std::cout << "***** BVAdd *****" << std::endl;
        auto current_val = btor_bv_add(&btor_child_1, &btor_child_2);
        nd.add_data(*current_val);
    } 
    else if(op.prim_op == PrimOp::BVAnd) {
        // std::cout << "***** BVAnd *****" << std::endl;
        auto current_val = btor_bv_and(&btor_child_1, &btor_child_2);
        nd.add_data(*current_val);
    }
    
    else if(op.prim_op == PrimOp::Concat) {
        // std::cout << "***** Concat *****" << std::endl;
        auto current_val = btor_bv_concat(&btor_child_1, &btor_child_2);
        nd.add_data(*current_val);
    }
    else if(op.prim_op == PrimOp::Equal) {
        // std::cout << "***** Equal *****" << std::endl;
        auto current_val = btor_bv_eq(&btor_child_1, &btor_child_2);
        nd.add_data(*current_val);
    }
}

Term resolve_substitution(const Term &term, std::unordered_map<Term, Term> &substitution_map) {
    auto it = substitution_map.find(term);
    if (it != substitution_map.end()) {
        Term substituted_term = it->second;
        if (substitution_map.find(substituted_term) != substitution_map.end()
            && substitution_map.find(substituted_term)->second != substituted_term) {
            return resolve_substitution(substituted_term, substitution_map);
        } else {
            return substituted_term;
        }
    }
    return term;  // Return the term itself if no substitution exists
}

// RAII wrapper for GMP random state
class GmpRandStateGuard
{
    gmp_randstate_t state;

    public:
    GmpRandStateGuard()
    {
        gmp_randinit_default(state);
        gmp_randseed_ui(state, time(NULL));
    }

    ~GmpRandStateGuard() { gmp_randclear(state); }

    void random_128(mpz_t & rand_num)
    {
        mpz_init2(rand_num, 128);
        mpz_urandomb(rand_num, state, 128);
    }

    // operator gmp_randstate_t &() { return state; }
};

std::chrono::time_point<std::chrono::high_resolution_clock> last_time_point;
void print_time() {
    auto now = std::chrono::high_resolution_clock::now();
    auto elapsed_time = std::chrono::duration_cast<std::chrono::milliseconds>(now - last_time_point).count();
    last_time_point = now;  // Update last time point
    std::cout << "[" << elapsed_time / 1000.0 << " ms]  ";
}

int main() {
    last_time_point = std::chrono::high_resolution_clock::now();

    // cout << "Starting program...\n";
    auto start_time = std::chrono::high_resolution_clock::now();

    SmtSolver solver = BoolectorSolverFactory::create(false);

    solver->set_logic("QF_UFBV");
    solver->set_opt("incremental", "true");
    solver->set_opt("produce-models", "true");
    solver->set_opt("produce-unsat-assumptions", "true");

    // cout << "Loading and parsing BTOR2 files...\n";
    TransitionSystem sts1(solver);
    BTOR2Encoder btor_parser1("../design/idpv-test/aes_case/AES_TOP.btor2", sts1, "a::");

    auto a_key_term = sts1.lookup("a::key");
    auto a_input_term = sts1.lookup("a::datain");
    auto a_output_term = sts1.lookup("a::finalout");

    TransitionSystem sts2(solver);
    BTOR2Encoder btor_parser2("../design/idpv-test/aes_case/AES_Verilog.btor2", sts2, "b::");

    auto b_key_term = sts2.lookup("b::key");
    auto b_input_term = sts2.lookup("b::in");
    auto b_output_term = sts2.lookup("b::out");

    print_time();
    std::cout << "init solver" << std::endl;

    solver->assert_formula(sts1.init());
    solver->assert_formula(sts2.init());
    for (const auto & c : sts1.constraints()) solver->assert_formula(c.first);
    for (const auto & c : sts2.constraints()) solver->assert_formula(c.first);

    if (!a_key_term || !a_input_term || !b_input_term || !b_key_term || !a_output_term || !b_output_term) {
        throw std::runtime_error("Required terms not found in models");
    }

    auto root = solver->make_term(Equal, a_output_term, b_output_term);

    std::unordered_map<Term, NodeData> node_data_map; // term -> sim_data
    std::unordered_map<uint32_t, TermVec> hash_term_map; // hash -> TermVec
    std::unordered_map<Term, Term> substitution_map; // term -> term, for substitution
    std::unordered_map<Term, std::unordered_map<std::string, std::string>> all_luts; // state -> lookup table

    // ARRAY INIT
    for (const auto & var_val_pair : sts1.init_constants()) {
        if(var_val_pair.first->get_sort()->get_sort_kind() != ARRAY)
            continue;
        Term val = var_val_pair.second;
        create_lut(val, all_luts[val]);
    }

    for (const auto & var_val_pair : sts2.init_constants()) {
        if(var_val_pair.first->get_sort()->get_sort_kind() != ARRAY)
            continue;
        Term val = var_val_pair.second;
        create_lut(val, all_luts[val]);
    }
    //End of array init

    //simulation
    GmpRandStateGuard rand_guard;
    int num_iterations = 10;

    for (int i = 0; i < num_iterations; ++i) {
        mpz_t key_mpz, input_mpz;
        rand_guard.random_128(key_mpz);
        rand_guard.random_128(input_mpz);

        int bit_length = 128; 
        int decimal_length = (int)std::ceil(bit_length * std::log10(2));

        // Use RAII for GMP strings
        unique_ptr<char, void (*)(void *)> key_str(mpz_get_str(NULL, 10, key_mpz), free);
        unique_ptr<char, void (*)(void *)> input_str(mpz_get_str(NULL, 10, input_mpz), free);

        std::string key_padded(key_str.get());
        std::string input_padded(input_str.get());
        key_padded.insert(key_padded.begin(), decimal_length - key_padded.size(), '0');
        input_padded.insert(input_padded.begin(), decimal_length - input_padded.size(), '0');

        mpz_clear(key_mpz);
        mpz_clear(input_mpz);

        // cout << "key:   " << key_padded << endl;
        // cout << "input: " << input_padded << endl;

        auto bv_key = btor_bv_char_to_bv(key_padded.data());
        auto bv_input = btor_bv_char_to_bv(input_padded.data());

        assert(bv_key->width == bv_input->width);

        //store sim data in NodeData
        node_data_map[a_key_term].add_data(*bv_key);
        node_data_map[a_input_term].add_data(*bv_input);
        node_data_map[b_key_term].add_data(*bv_key);
        node_data_map[b_input_term].add_data(*bv_input);

        substitution_map.insert({a_key_term, a_key_term});
        substitution_map.insert({a_input_term, a_input_term});
        substitution_map.insert({b_key_term, b_key_term});
        substitution_map.insert({b_input_term, b_input_term});
       
    }  
    // end of simulation

    assert(node_data_map[a_key_term].get_simulation_data().size() == num_iterations);
    assert(node_data_map[a_input_term].get_simulation_data().size() == num_iterations);
    assert(node_data_map[b_key_term].get_simulation_data().size() == num_iterations);
    assert(node_data_map[b_input_term].get_simulation_data().size() == num_iterations);

    //start post order traversal
    std::stack<std::pair<Term,bool>> node_stack;
    node_stack.push({root,false});

    print_time();
    cout << "End simulation, Start post order traversal" << endl;

    while(!node_stack.empty()) {
        auto & [current,visited] = node_stack.top();
        if(node_data_map.find(current) != node_data_map.end()) {
            node_stack.pop();
            continue;
        }

        if(!visited) {
            // push all children onto stack
            for(Term child : current) {
                if(child->get_sort()->get_sort_kind() == BV || child->get_sort()->get_sort_kind() == BOOL) {
                    node_stack.push({child,false});
                }
            }
            visited = true;
        } else {
            NodeData& nd = node_data_map[current];
            auto op_type = current->get_op();
            // std::cout << "-----op: " << op_type.to_string() << "-----" << std::endl;

            if(current->is_value()) { // constant
                // std::cout << "Constant: " << current->to_string() << std::endl;
                auto current_str = current->to_string().substr(2);
                // cout << "current_str: " << current_str << endl;
                auto current_bv = btor_bv_char_to_bv(current_str.data());
                for (int i = 0; i < num_iterations; ++i) {
                    nd.add_data(*current_bv);
                }
                btor_bv_free(current_bv);

                assert(nd.get_simulation_data().size() == num_iterations);
                substitution_map.insert({current, current}); // constant don't need substitution
                //TODO: add to hash_term_map ? 
            }
            else if(current->is_symbolic_const() && current->get_op().is_null()) { // leaf nodes
                assert(TermVec(current->begin(), current->end()).empty());// no children
                assert(current->get_sort()->get_sort_kind() != ARRAY); // no array
                assert(node_data_map.find(current) != node_data_map.end()); // data should be computed
                assert(node_data_map[current].get_simulation_data().size() == num_iterations);

                auto current_hash = nd.hash(nd.get_simulation_data()); // use data hash to combine a new hash
                if(hash_term_map.find(current_hash) == hash_term_map.end()) {
                    hash_term_map.insert({current_hash, {current}});
                } else {
                    auto &terms = hash_term_map[current_hash];
                    terms.push_back(current);
                    for(auto & t : terms) {
                        assert(node_data_map.find(t) != node_data_map.end());
                        bool all_equal = true;
                        for(size_t i = 0; i < num_iterations; i++) {
                            #ifdef BTOR_USE_GMP
                                if(node_data_map[t].get_simulation_data()[i].val != node_data_map[current].get_simulation_data()[i].val) 
                            #else
                                if(node_data_map[t].get_simulation_data()[i].bits != node_data_map[current].get_simulation_data()[i].bits
                                  || node_data_map[t].get_simulation_data()[i].len != node_data_map[current].get_simulation_data()[i].len) 
                            #endif
                            {
                                all_equal = false;
                                substitution_map.insert({current, current});
                                break;
                            }
                        }
                        if(all_equal) {
                            auto eq_term = solver->check_sat_assuming(TermVec({solver->make_term(Not, solver->make_term(Equal, t, current))}));
                            if(eq_term.is_unsat()) {
                                substitution_map.insert({current, t});
                            }
                        }
                    }
                }
                
            }
            else { // compute simulation data for current node
                // std::cout << "Computing : " << current->to_string() << std::endl;
                TermVec children(current->begin(), current->end()); // find children
                auto child_size = children.size();
                // cout << "children size: " << child_size << endl;

                if(child_size == 1) {
                    assert(substitution_map.find(children[0]) != substitution_map.end());
                    resolve_substitution(children[0], substitution_map); // substitute child with previous node
                    
                    for(size_t i = 0; i < num_iterations; i++) {
                        auto & sim_data = node_data_map[children[0]].get_simulation_data();
                        assert(sim_data.size() == num_iterations);
                        auto bv_child = sim_data[i];
                        // cout << op_type.prim_op << endl;

                        if(op_type.prim_op == PrimOp::BVNot) {
                            // std::cout << "***** BVNot *****" << std::endl;
                            auto current_val = btor_bv_not(&bv_child);
                            nd.add_data(*current_val);
                        }
                        else if(op_type.prim_op == PrimOp::Extract) {
                            // std::cout << "***** Extract *****" << std::endl;
                            auto high = op_type.idx0;
                            auto low = op_type.idx1;
                            assert(high >= low);
                            auto current_val = btor_bv_slice(&bv_child, high, low);
                            assert(current_val->width == high - low + 1);
                            nd.add_data(*current_val);
                        }
                        else {
                            throw NotImplementedException("Unsupported operator type1: " + op_type.to_string());
                        }
                    }
                    assert(nd.get_simulation_data().size() == num_iterations);
                } 
                else if(child_size == 2) {
                    for (int i = 0; i < 2; ++i) {// skip array, only consider non-array children
                        if (children[i]->get_sort()->get_sort_kind() != ARRAY) {
                            assert(substitution_map.find(children[i]) != substitution_map.end());
                            resolve_substitution(children[i], substitution_map); // substitute child with previous node
                        }
                    }

                    if(op_type.prim_op == PrimOp::Select) { // array
                        auto & array = children[0];
                        auto & index = children[1];
                        assert(all_luts.find(array) != all_luts.end());

                        for (size_t i = 0; i < num_iterations; i++) {
                            auto index_str = std::string(btor_bv_to_char(&node_data_map[index].get_simulation_data()[i]));
                            auto val_str = all_luts[array][index_str];
                            auto val_bv = btor_bv_char_to_bv(val_str.data());
                            nd.add_data(*val_bv);
                        }
                    } else { // other bv operations
                        const auto & child_1 = children[0];
                        const auto & child_2 = children[1];
                        const auto & sim_data_1 = node_data_map[child_1].get_simulation_data();
                        const auto & sim_data_2 = node_data_map[child_2].get_simulation_data();
                        assert(sim_data_1.size() == num_iterations);
                        assert(sim_data_2.size() == num_iterations);

                        for(size_t i = 0; i < num_iterations; i++) {
                            auto & btor_child_1 = sim_data_1[i];
                            auto & btor_child_2 = sim_data_2[i];
                            btor_bv_operation(op_type, btor_child_1, btor_child_2, nd);
                        }
                    }
                    assert(nd.get_simulation_data().size() == num_iterations);
                }
                else if(child_size == 3) {
                    for (int i = 0; i < 3; ++i) {// skip array, only consider non-array children
                        if (children[i]->get_sort()->get_sort_kind() != ARRAY) {
                            assert(substitution_map.find(children[i]) != substitution_map.end());
                            resolve_substitution(children[i], substitution_map); // substitute child with previous node
                        }
                    }

                    for(size_t i = 0; i < num_iterations; i++) {
                        auto & sim_data_1 = node_data_map[children[0]].get_simulation_data();
                        auto & sim_data_2 = node_data_map[children[1]].get_simulation_data();
                        auto & sim_data_3 = node_data_map[children[2]].get_simulation_data();

                        assert(sim_data_1.size() == num_iterations);
                        assert(sim_data_2.size() == num_iterations);
                        assert(sim_data_3.size() == num_iterations);
                        auto btor_child_1 = sim_data_1[i];
                        auto btor_child_2 = sim_data_2[i];
                        auto btor_child_3 = sim_data_3[i];
                
                        if(op_type.prim_op == PrimOp::Ite) {
                            // std::cout << "***** Ite *****" << std::endl;
                            auto current_val = btor_bv_ite(&btor_child_1, &btor_child_2, &btor_child_3);
                            nd.add_data(*current_val);
                        } else {
                            throw NotImplementedException("Unsupported operator type3: " + op_type.to_string());
                        }
                    }
                    assert(nd.get_simulation_data().size() == num_iterations);
                }
                else {
                    throw NotImplementedException("Unsupported operator type4: " + op_type.to_string() + "  with child size: " + std::to_string(child_size));
                }
                
                //create a new current node
                Term new_term = solver->make_term(op_type, children);
                if (node_data_map.find(new_term) == node_data_map.end()) { // check if new node exists or not
                    NodeData new_node_data = nd;
                    node_data_map[new_term] = new_node_data;
                }
                current = new_term;

                auto current_data_hash = nd.hash(nd.get_simulation_data());
                if(hash_term_map.find(current_data_hash) == hash_term_map.end()) {
                    hash_term_map.insert({current_data_hash, {current}});
                    substitution_map.insert({current, current}); // not in hash_term_map, so it is definitely no substitution
                } else {
                    auto &terms = hash_term_map[current_data_hash];
                    terms.push_back(current);
                    for(auto & t : terms) {
                        assert(node_data_map.find(t) != node_data_map.end());
                        bool all_equal = true;
                        for(size_t i = 0; i < num_iterations; i++) {
                            #ifdef BTOR_USE_GMP
                                if(node_data_map[t].get_simulation_data()[i].val != node_data_map[current].get_simulation_data()[i].val)
                            #else
                                if(node_data_map[t].get_simulation_data()[i].bits != node_data_map[current].get_simulation_data()[i].bits
                                    || node_data_map[t].get_simulation_data()[i].len != node_data_map[current].get_simulation_data()[i].len)
                            #endif
                            {
                                all_equal = false;
                                substitution_map.insert({current, current});
                                break;
                            }
                        }
                        if(all_equal) {
                            auto eq_term = solver->check_sat_assuming(TermVec({solver->make_term(Not, solver->make_term(Equal, t, current))}));
                            if(eq_term.is_unsat()) {
                                substitution_map.insert({current, t});
                            } else {
                                substitution_map.insert({current, current});
                            }
                        } else {
                            substitution_map.insert({current, current});
                        }
                    }
                }
            }
        
            if(node_stack.size() == 1){ // root node
                TermVec root_children(current->begin(), current->end());
                if(substitution_map.find(root_children[0]) != substitution_map.end()
                || substitution_map.find(root_children[1]) != substitution_map.end()) {
                    root_children[0] = substitution_map[root_children[0]];
                    root_children[1] = substitution_map[root_children[1]];
                }
                root = solver->make_term(op_type, root_children);
            }     
        }
    }

    print_time();
    std::cout << "Start checking sat" << std::endl;

    auto key_eq = solver->make_term(Equal, a_key_term, b_key_term);
    auto input_eq = solver->make_term(Equal, a_input_term, b_input_term);
    auto output_eq = solver->make_term(Equal, a_output_term, b_output_term);

    solver->assert_formula(key_eq);
    solver->assert_formula(input_eq);

    solver->assert_formula(solver->make_term(Not, output_eq));


    auto res = solver->check_sat();
    if(res.is_unsat()){
        std::cout << "UNSAT" << std::endl;
    } else {
        std::cout << "SAT" << std::endl;
    }

    if(res.is_sat()) {
    std::cout << "SAT - Found counterexample:" << std::endl;
    std::cout << "Input values:" << std::endl;
    std::cout << "key: " << solver->get_value(a_key_term) << std::endl;
    std::cout << "input: " << solver->get_value(a_input_term) << std::endl;
    std::cout << "Outputs:" << std::endl;
    std::cout << "Circuit A: " << solver->get_value(a_output_term) << std::endl;
    std::cout << "Circuit B: " << solver->get_value(b_output_term) << std::endl;
    }

    return 0;
}