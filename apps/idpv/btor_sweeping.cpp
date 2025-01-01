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
    std::vector<BtorBitVector> simulation_data; //TODO: memory usage
public:
    NodeData() : term(nullptr), bit_width(0) {} 

    NodeData(const Term & t) : term(t), bit_width(0) {}

    NodeData(const Term & t, const size_t & bw) : term(t), bit_width(bw) {}

    Term get_term() const { return term; }
    
    size_t get_bit_width() const { return bit_width; }
    
    std::vector<BtorBitVector>& get_simulation_data() {
        return simulation_data;
    }

    // void add_data(const BtorBitVector & data) {
    //     std::cout << "Before moving data, val: " << data.val << std::endl;
    //     simulation_data.push_back(data);
    // }


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

void create_lut(Term current, std::unordered_map<std::string, std::string>& lut) {
    while (current->get_op().prim_op == PrimOp::Store) {
        auto children = TermVec(current->begin(), current->end());
        if (children.size() != 3) {
            throw std::runtime_error("Store operation should have exactly 3 children");
        }
        // store：array、index、value
        auto array = children[0];   // original array
        auto index = children[1];   // stored position
        auto value = children[2];   // sotred value

        // std::cout<< "stored position:" <<std::endl;
        // std::cout<< "stored position" << index->to_string().c_str() << std::endl;
        // std::cout<< "stored value" << value->to_string().c_str() << std::endl;
        
        lut[index->to_string().substr(2)] = value->to_string().substr(2);

        current = children[0]; // next iteration
    }
}

void btor_bv_operation_1child(const smt::Op& op, 
                              const BtorBitVector& btor_child_1, 
                              NodeData &nd) {    
    if(op.prim_op == PrimOp::BVNot) {
        auto current_val = btor_bv_not(&btor_child_1);                    
        // nd.add_data(*current_val);
        nd.get_simulation_data().push_back(*current_val);
        
    }
    else if(op.prim_op == PrimOp::Extract) {
        auto high = op.idx0;
        auto low = op.idx1;
        assert(high >= low);
        // cout << "btor_child_1: " << btor_child_1.bits << ", width: " << btor_child_1.width << ", length: " << btor_child_1.len << endl;
        // cout << "btor_child_1: " << btor_child_1.val << ", width: " << btor_child_1.width << endl;
        auto current_val = btor_bv_slice(&btor_child_1, high, low);
        assert(current_val->width == high - low + 1);
        // nd.add_data(*current_val);
        nd.get_simulation_data().push_back(*current_val);
    }
    else {
        throw NotImplementedException("Unsupported operation type 1 child: " + op.to_string());
    }
}

void btor_bv_operation_2children(const smt::Op& op, 
                                 const BtorBitVector& btor_child_1, 
                                 const BtorBitVector& btor_child_2, 
                                 NodeData &nd) {
    if(op.prim_op == PrimOp::BVAdd) {
        auto current_val = btor_bv_add(&btor_child_1, &btor_child_2);
        nd.get_simulation_data().push_back(*current_val);
    } 
    else if(op.prim_op == PrimOp::BVAnd) {
        auto current_val = btor_bv_and(&btor_child_1, &btor_child_2);
        nd.get_simulation_data().push_back(*current_val);
    }
    else if(op.prim_op == PrimOp::Concat) {
        auto current_val = btor_bv_concat(&btor_child_1, &btor_child_2);
        nd.get_simulation_data().push_back(*current_val);
    }
    else if(op.prim_op == PrimOp::Equal) {
        auto current_val = btor_bv_eq(&btor_child_1, &btor_child_2);
        nd.get_simulation_data().push_back(*current_val);
    }
    else {
        throw NotImplementedException("Unsupported operation type 2 children: " + op.to_string());
    }
}

void btor_bv_operation_3children(const smt::Op& op, 
                                 const BtorBitVector& btor_child_1, 
                                 const BtorBitVector& btor_child_2,
                                 const BtorBitVector& btor_child_3,
                                 NodeData &nd) {
    if(op.prim_op == PrimOp::Ite) {
        auto current_val = btor_bv_ite(&btor_child_1, &btor_child_2, &btor_child_3);
        nd.get_simulation_data().push_back(*current_val);
    }
    else {
        throw NotImplementedException("Unsupported operation type 3 children: " + op.to_string());
    }
}


//one child simulation
void process_child_simulation(Term child, 
                              Term current, 
                              size_t num_iterations, 
                              const smt::Op& op_type,
                              std::unordered_map<Term, NodeData>& node_data_map,
                              std::unordered_map<Term, Term>& substitution_map,
                              bool substitution_happened) {
    Term substitution_child;
    if(child->get_sort()->get_sort_kind() != ARRAY){
        cout << "child here1: " << child->to_string() << endl;
        assert(substitution_map.find(child) != substitution_map.end()); //FIXME:
        substitution_child = substitution_map.at(child);
        substitution_happened = (child != substitution_child);
    }
    else {
        substitution_happened = false;
    }
    // check if substitution happened

    Term effective_child = (substitution_happened)? substitution_child : child;
    auto & sim_data = node_data_map.at(effective_child).get_simulation_data();
    assert(sim_data.size() == num_iterations);

    for(size_t i = 0; i < num_iterations; i++) {
        auto & bv_child = sim_data[i];
        btor_bv_operation_1child(op_type, bv_child, node_data_map.at(current));
    }

    assert(node_data_map.at(current).get_simulation_data().size() == num_iterations);
}

//two children simulation
void process_two_children_simulation(smt::TermVec children, 
                                     Term current, 
                                     size_t num_iterations, 
                                     smt::Op& op_type, 
                                     std::unordered_map<Term, NodeData>& node_data_map,
                                     std::unordered_map<Term, Term>& substitution_map, 
                                     std::unordered_map<Term, std::unordered_map<std::string, std::string>>& all_luts,
                                     NodeData& nd,
                                     bool substitution_happened) {

    bool substitution_happened_local[2] = {false, false}; // for each child track substitution
    
    for (int i = 0; i < 2; ++i) {
        if (children[i]->get_sort()->get_sort_kind() != ARRAY) { // skip arrays
            assert(substitution_map.find(children[i]) != substitution_map.end());
            auto substitution_child = substitution_map.at(children[i]);

            if(children[i] != substitution_child) {
                
                // substitution happened signal
                substitution_happened_local[i] = true;
                substitution_happened = true;
                
                children[i] = substitution_child;  // Update child to its substituted term
            }
        }
    }

     if (op_type.prim_op == PrimOp::Select) {  // Array operation (Select)
        auto& array = children[0];
        auto& index = children[1];

        std::cout << "Looking for array: " << array->to_string() << std::endl;
        assert(all_luts.find(array) != all_luts.end());

        for (size_t i = 0; i < num_iterations; ++i) {
            // Resolve the simulation data for the index child (if substitution happened, we use resolved node)
            auto& sim_data_index = node_data_map.at(index).get_simulation_data();
            assert(sim_data_index.size() == num_iterations);

            auto index_str = std::string(btor_bv_to_char(&sim_data_index[i]));
            auto val_str = all_luts[array][index_str];
            cout << "index: " << index_str << ", value: " << val_str << endl;
            auto val = btor_bv_char_to_bv(val_str.data());
            nd.get_simulation_data().push_back(*val);
        }
    }else { // for other bit-vector operations
        const auto& child_1 = children[0];
        const auto& child_2 = children[1];

        // If substitution happened, we must get the resolved node and use its simulation data
        const auto& sim_data_1 = node_data_map.at(substitution_happened_local[0] ? substitution_map.at(child_1) : child_1).get_simulation_data();
        const auto& sim_data_2 = node_data_map.at(substitution_happened_local[1] ? substitution_map.at(child_2) : child_2).get_simulation_data();
        
        assert(sim_data_1.size() == num_iterations);
        assert(sim_data_2.size() == num_iterations);

        // Perform the operation on the simulation data
        for (size_t i = 0; i < num_iterations; ++i) {
            auto& btor_child_1 = sim_data_1[i];
            auto& btor_child_2 = sim_data_2[i];
            btor_bv_operation_2children(op_type, btor_child_1, btor_child_2, nd);
        }
    }

    assert(nd.get_simulation_data().size() == num_iterations);
}

// three children simulation
void process_three_children_simulation(smt::TermVec& children, 
                                       Term current, 
                                       size_t num_iterations, 
                                       smt::Op& op_type, 
                                       std::unordered_map<Term, NodeData>& node_data_map,
                                       std::unordered_map<Term, Term>& substitution_map, 
                                       std::unordered_map<Term, std::unordered_map<std::string, std::string>>& all_luts,
                                       NodeData& nd,
                                       bool substitution_happened) {
    bool substitution_happened_local[3] = {false, false, false};  // Track substitution for each child

    // Check each child for substitution
    for (int i = 0; i < 3; ++i) {
        if(children[i]->get_sort()->get_sort_kind() != ARRAY){
            cout << "child here3: " << children[i]->to_string() << endl;
            assert(substitution_map.find(children[i]) != substitution_map.end()); //FIXME:
            auto substitution_child = substitution_map.at(children[i]);

            if (children[i] != substitution_child) {  // substitution happened
                substitution_happened_local[i] = true;
                substitution_happened = true;
                children[i] = substitution_child;  // Update child to its resolved (substituted) term
                std::cout << "Substitution happened for child " << i 
                          << ": " << substitution_child->to_string() << std::endl;
            }
        }
        else {
            substitution_happened_local[i] = false;
            std::cout << "Child " << i << " is an array: " << children[i]->to_string() << std::endl;
            assert(all_luts.find(children[i]) != all_luts.end());
            std::cout << "Array LUT entries for child " << i << ":" << std::endl;
            for (const auto& [idx, val] : all_luts[children[i]]) {
                std::cout << "Index: " << idx << ", Value: " << val << std::endl;
            }
        }
    }

    // Now, handle the simulation data and apply the operator
    for (size_t i = 0; i < num_iterations; i++) {
        // Resolve the simulation data for each child (if substitution happened, we use resolved node)
        auto& sim_data_1 = node_data_map.at(substitution_happened_local[0] ? substitution_map.at(children[0]) : children[0]).get_simulation_data();
        auto& sim_data_2 = node_data_map.at(substitution_happened_local[1] ? substitution_map.at(children[1]) : children[1]).get_simulation_data();
        auto& sim_data_3 = node_data_map.at(substitution_happened_local[2] ? substitution_map.at(children[2]) : children[2]).get_simulation_data();

        assert(sim_data_1.size() == num_iterations);
        assert(sim_data_2.size() == num_iterations);
        assert(sim_data_3.size() == num_iterations);

        // Retrieve the bit-vector data for each child at the current iteration
        auto btor_child_1 = sim_data_1[i];
        auto btor_child_2 = sim_data_2[i];
        auto btor_child_3 = sim_data_3[i];
        
        std::cout << "btor_child_1: " << btor_child_1.val << ", width: " << btor_child_1.width << std::endl;
        std::cout << "btor_child_2: " << btor_child_2.val << ", width: " << btor_child_2.width << std::endl;
        std::cout << "btor_child_3: " << btor_child_3.val << ", width: " << btor_child_3.width << std::endl;

        // Apply the operator
        btor_bv_operation_3children(op_type, btor_child_1, btor_child_2, btor_child_3, nd);
    }

    assert(nd.get_simulation_data().size() == num_iterations);
}


// main simulation function
void process_children(Term current, 
                      smt::TermVec& children, 
                      size_t num_iterations, 
                      smt::Op& op_type, 
                      std::unordered_map<Term, NodeData>& node_data_map,
                      std::unordered_map<Term, Term>& substitution_map, 
                      std::unordered_map<Term, std::unordered_map<std::string, std::string>>& all_luts, 
                      NodeData& nd,
                      bool& substitution_happened) {
    if (children.size() == 1) {
        if (children[0]->get_sort()->get_sort_kind() == ARRAY) {
            substitution_happened = false; // 数组节点不需要替换
        }
        process_child_simulation(children[0], current, num_iterations, op_type, node_data_map, substitution_map, substitution_happened);
    } else if (children.size() == 2) {
        process_two_children_simulation(children, current, num_iterations, op_type, node_data_map, substitution_map, all_luts, nd, substitution_happened);
    } else if(children.size() == 3) {
        process_three_children_simulation(children, current, num_iterations, op_type, node_data_map, substitution_map, all_luts, nd, substitution_happened);
    } else {
        throw NotImplementedException("Unsupported number of children: " + std::to_string(children.size()));
    }
}


//check two nodes are equal or not
void compare_two_nodes(int num_iterations, 
                       std::unordered_map<Term, NodeData> &node_data_map,
                       std::unordered_map<Term, Term> &substitution_map,
                       TermVec &terms,
                       Term &current,
                       SmtSolver solver) {
    for(auto & t : terms) {
        assert(node_data_map.find(t) != node_data_map.end());
        
        if(t == current) {
            continue;
        }

        if(t->get_sort() != current->get_sort()) { // ensure the same sort
            continue;
        }

        bool all_equal = true;
        for(size_t i = 0; i < num_iterations; i++) {
            if((btor_bv_compare(&node_data_map[t].get_simulation_data()[i], &node_data_map[current].get_simulation_data()[i])) != 0) {
                all_equal = false;
                substitution_map.insert({current,current});
                break;
            }
        }

        if(all_equal) {
            auto eq_term = solver->check_sat_assuming(TermVec({solver->make_term(Not, solver->make_term(Equal, t, current))}));
            if(eq_term.is_unsat()) {
                std::cout << "******substitution: " << current->to_string() << " -> " << t->to_string() << "*******" << std::endl;
                substitution_map.insert({current, t});
            }
        }
    }
}

//update current node's data hash in hash_term_map
void update_hash_term_map(Term current, 
                          std::unordered_map<uint32_t, smt::TermVec>& hash_term_map,
                          std::unordered_map<Term, NodeData>& node_data_map,
                          std::unordered_map<Term, Term>& substitution_map,
                          size_t num_iterations,
                          SmtSolver solver) {
   
    for(size_t i = 0; i < num_iterations; i++){
        auto & data = node_data_map[current].get_simulation_data()[i];
        // std::cout << "data[" << i << "]: " << data.val << ", " << data.width << endl;
    }
    auto current_hash = node_data_map[current].hash(node_data_map[current].get_simulation_data());



    std::cout << "current data hash: " << current_hash << std::endl;
    if (hash_term_map.find(current_hash) == hash_term_map.end()) {
        hash_term_map.insert({current_hash, {current}});
        substitution_map.insert({current, current});
    } else {
        hash_term_map[current_hash].push_back(current);
        compare_two_nodes(num_iterations, node_data_map, substitution_map, hash_term_map[current_hash], current, solver);
    }
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
        Term var = var_val_pair.first;
        Term val = var_val_pair.second;
        create_lut(val, all_luts[var]);
        substitution_map.insert({var, var});
    }

    for (const auto & var_val_pair : sts2.init_constants()) {
        if(var_val_pair.first->get_sort()->get_sort_kind() != ARRAY)
            continue;
        Term var = var_val_pair.first;
        Term val = var_val_pair.second;
        create_lut(val, all_luts[var]);
        substitution_map.insert({var, var});
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
        unique_ptr<char, void (*)(void *)> key_str(mpz_get_str(NULL, 2, key_mpz), free);
        unique_ptr<char, void (*)(void *)> input_str(mpz_get_str(NULL, 2, input_mpz), free);

        mpz_clear(key_mpz);
        mpz_clear(input_mpz);
        
        auto bv_input = btor_bv_const(input_str.get(), bit_length);
        auto bv_key = btor_bv_const(key_str.get(), bit_length);

        assert(bv_key->width == bv_input->width);

        //store sim data in NodeData
        node_data_map[a_key_term].get_simulation_data().push_back(*bv_key);
        node_data_map[a_input_term].get_simulation_data().push_back(*bv_input);
        node_data_map[b_key_term].get_simulation_data().push_back(*bv_key);
        node_data_map[b_input_term].get_simulation_data().push_back(*bv_input);

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
            auto op_type = current->get_op();
            std::cout << "-----op: " << op_type.to_string() << "-----" << std::endl;

            if(current->is_value()) { // constant
                std::cout << "Constant: " << current->to_string().substr(2) << std::endl;

                auto current_str = current->to_string().substr(2);
                auto current_bv = btor_bv_char_to_bv(current_str.data());
                cout << "current_bv: " << current_bv->width <<", val:" << current_bv->val << endl;
                for (int i = 0; i < num_iterations; ++i) {
                    node_data_map[current].get_simulation_data().push_back(*current_bv);
                }
                // btor_bv_free(current_bv);

                assert(node_data_map[current].get_simulation_data().size() == num_iterations);
                
                // constant don't need substitution
                // substitution_map.insert({current, current}); 

                //update hash_term_map
                update_hash_term_map(current, hash_term_map, node_data_map, substitution_map, num_iterations, solver);
            }
            else if(current->is_symbolic_const() && current->get_op().is_null()) { // leaf nodes
                std::cout << "leaf nodes: " << current->to_string() << std::endl;

                assert(TermVec(current->begin(), current->end()).empty());// no children
                assert(current->get_sort()->get_sort_kind() != ARRAY); // no array
                assert(node_data_map.find(current) != node_data_map.end()); // data should be computed
                assert(node_data_map[current].get_simulation_data().size() == num_iterations);

                //leaf nodes don't need substitution
                // substitution_map.insert({current, current}); 

                //update hash_term_map 
                update_hash_term_map(current, hash_term_map, node_data_map, substitution_map, num_iterations, solver);
            }
            else { // compute simulation data for current node
                std::cout << "Computing : " << current->to_string() << std::endl;
                TermVec children(current->begin(), current->end()); // find children
                auto child_size = children.size();
                cout << "children size: " << child_size << endl;


//simualtion data for current node
//create a new current node
//update hash_term_map and substitution_map

                bool substitution_happened = false;
                process_children(current, children, num_iterations, op_type, node_data_map, substitution_map, all_luts, node_data_map[current], substitution_happened);

                
                if(substitution_happened) {
                    std::cout << "***********Substitution happened***********" << std::endl;
                    Term new_node = solver->make_term(op_type, children);
                    NodeData new_nd = node_data_map[current];
                    node_data_map.insert({new_node, new_nd});

                    //update hash_term_map
                    update_hash_term_map(new_node, hash_term_map, node_data_map, substitution_map, num_iterations, solver);
                } else {
                    std::cout << "No substitution..." << std::endl;
                    update_hash_term_map(current, hash_term_map, node_data_map, substitution_map, num_iterations, solver);
                }    
            }
        
            if(node_stack.size() == 1){ // root node
                TermVec root_children(current->begin(), current->end());
                assert(root_children.size() == 2); // only a::out and b::out are left as root children
                assert(substitution_map.find(root_children[0]) != substitution_map.end());
                assert(substitution_map.find(root_children[1]) != substitution_map.end());

                root_children[0] = substitution_map[root_children[0]];
                root_children[1] = substitution_map[root_children[1]];
                root = solver->make_term(op_type, root_children);
            }            

            node_stack.pop();
        }
    }

    print_time();
    std::cout << "Start checking sat" << std::endl;

    solver->assert_formula(solver->make_term(Not, root));
    auto res = solver->check_sat();
    if(res.is_unsat()){
        std::cout << "UNSAT" << std::endl;
    } else {
        std::cout << "SAT" << std::endl;
    }
    return 0;
}