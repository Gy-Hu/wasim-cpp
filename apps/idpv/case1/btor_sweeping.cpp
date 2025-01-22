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


std::chrono::time_point<std::chrono::high_resolution_clock> last_time_point;
void print_time() {
    auto now = std::chrono::high_resolution_clock::now();
    auto elapsed_time = std::chrono::duration_cast<std::chrono::milliseconds>(now - last_time_point).count();
    last_time_point = now;  // Update last time point
    std::cout << "[" << elapsed_time / 1000.0 << " s]  ";
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
    const std::vector<BtorBitVector>& get_simulation_data() const {
        return simulation_data;
    }

    // void add_data(const BtorBitVector & data) {
    //     std::cout << "Before moving data, val: " << data.val << std::endl;
    //     simulation_data.push_back(data);
    // }

    size_t hash() const {
        return hash(simulation_data);
    }

    static size_t hash(const std::vector<BtorBitVector>& data) {
        if (data.empty()) {
            return 0;
        }

        size_t hash_val = 0;
        for(const auto & v : data) {
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
    else if(op.prim_op == PrimOp::BVXor) {
        auto current_val = btor_bv_xor(&btor_child_1, &btor_child_2);
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
void process_single_child_simulation(const Term & child,  // HZ: const Term &
                              size_t num_iterations, 
                              const smt::Op& op_type,
                              const std::unordered_map<Term, NodeData> & node_data_map,
                              NodeData & out) {

    assert(child->get_sort()->get_sort_kind() != ARRAY);
    // check if substitution happened

    const auto & sim_data = node_data_map.at(child).get_simulation_data();
    assert(sim_data.size() == num_iterations);

    for(size_t i = 0; i < num_iterations; i++) {
        const auto & bv_child = sim_data[i];
        btor_bv_operation_1child(op_type, bv_child, out);
    }

    assert(out.get_simulation_data().size() == num_iterations);
}

//two children simulation
void process_two_children_simulation(const smt::TermVec & children, // const ... &
                                     size_t num_iterations, 
                                     const smt::Op& op_type, 
                                     const std::unordered_map<Term, NodeData>& node_data_map,
                                     const std::unordered_map<Term, std::unordered_map<std::string, std::string>>& all_luts,
                                     NodeData& nd /* OUTPUT */
                                     ) { 

     if (op_type.prim_op == PrimOp::Select) {  // Array operation (Select)
        const auto& array_var = children[0];
        const auto& index_term = children[1];

        // std::cout << "Looking for array: " << array->to_string() << std::endl;
        assert(all_luts.find(array_var) != all_luts.end());

        const auto& sim_data_index = node_data_map.at(index_term).get_simulation_data();
        assert(sim_data_index.size() == num_iterations);

        for (size_t i = 0; i < num_iterations; ++i) {
            // Resolve the simulation data for the index child (if substitution happened, we use resolved node)

            auto index_str = std::string(btor_bv_to_char( & (sim_data_index[i])));
            const auto & val_str = all_luts.at(array_var).at(index_str);
            // cout << "index: " << index_str << ", value: " << val_str << endl;
            auto val = btor_bv_char_to_bv(val_str.data());
            nd.get_simulation_data().push_back(*val);
        }
    }else { // for other bit-vector operations
        const auto& child_1 = children[0];
        const auto& child_2 = children[1];

        // If substitution happened, we must get the resolved node and use its simulation data
        const auto& sim_data_1 = node_data_map.at(child_1).get_simulation_data();
        const auto& sim_data_2 = node_data_map.at(child_2).get_simulation_data();
        
        assert(sim_data_1.size() == num_iterations);
        assert(sim_data_2.size() == num_iterations);

        // Perform the operation on the simulation data
        for (size_t i = 0; i < num_iterations; ++i) {
            const auto& btor_child_1 = sim_data_1[i];
            const auto& btor_child_2 = sim_data_2[i];
            btor_bv_operation_2children(op_type, btor_child_1, btor_child_2, nd);
        }
    }

    assert(nd.get_simulation_data().size() == num_iterations);
}

// three children simulation
void process_three_children_simulation(const smt::TermVec& children, 
                                       size_t num_iterations, 
                                       const smt::Op& op_type, 
                                       const std::unordered_map<Term, NodeData>& node_data_map,
                                       const std::unordered_map<Term, std::unordered_map<std::string, std::string>>& all_luts,
                                       NodeData& nd) {

    // Now, handle the simulation data and apply the operator
    for (size_t i = 0; i < num_iterations; i++) {
        // Resolve the simulation data for each child (if substitution happened, we use resolved node)
        const auto& sim_data_1 = node_data_map.at(children[0]).get_simulation_data();
        const auto& sim_data_2 = node_data_map.at(children[1]).get_simulation_data();
        const auto& sim_data_3 = node_data_map.at(children[2]).get_simulation_data();

        assert(sim_data_1.size() == num_iterations);
        assert(sim_data_2.size() == num_iterations);
        assert(sim_data_3.size() == num_iterations);

        // Retrieve the bit-vector data for each child at the current iteration
        auto btor_child_1 = sim_data_1[i];
        auto btor_child_2 = sim_data_2[i];
        auto btor_child_3 = sim_data_3[i];

        // Apply the operator
        btor_bv_operation_3children(op_type, btor_child_1, btor_child_2, btor_child_3, nd);
    }

    assert(nd.get_simulation_data().size() == num_iterations);
}


// main simulation function
void compute_simulation(
                      const smt::TermVec & children, 
                      size_t num_iterations, 
                      const smt::Op& op_type, 
                      const std::unordered_map<Term, NodeData>& node_data_map,
                      const std::unordered_map<Term, std::unordered_map<std::string, std::string>>& all_luts, 
                      NodeData& nd // output
                      ) {
    if (children.size() == 1) {
        process_single_child_simulation(children[0],  num_iterations, op_type, node_data_map, nd);
    } else if (children.size() == 2) {
        process_two_children_simulation(children, num_iterations, op_type, node_data_map, all_luts, nd);
    } else if(children.size() == 3) {
        process_three_children_simulation(children, num_iterations, op_type, node_data_map, all_luts, nd);
    } else {
        throw NotImplementedException("Unsupported number of children: " + std::to_string(children.size()));
    }
}

void children_substitution(const smt::TermVec& children, smt::TermVec& out, const std::unordered_map<Term, Term>& substitution_map) {
	for (const auto & c : children) {
        auto pos = substitution_map.find(c);
        assert(pos != substitution_map.end());
        out.push_back(pos->second);
	}
} // end of children_substitution



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


int main() {
    auto program_start_time = std::chrono::high_resolution_clock::now();
    last_time_point = program_start_time;
    // auto start_time = std::chrono::high_resolution_clock::now();

    SmtSolver solver = BoolectorSolverFactory::create(true);

    solver->set_logic("QF_UFBV");
    solver->set_opt("incremental", "true");
    solver->set_opt("produce-models", "true");
    solver->set_opt("produce-unsat-assumptions", "true");

    // cout << "Loading and parsing BTOR2 files...\n";
    TransitionSystem sts1(solver);
    BTOR2Encoder btor_parser1("../design/smt-sweeping/case1/AES_TOP.btor2", sts1, "a::");

    auto a_key_term = sts1.lookup("a::key");
    auto a_input_term = sts1.lookup("a::datain");
    auto a_output_term = sts1.lookup("a::finalout");

    TransitionSystem sts2(solver);
    BTOR2Encoder btor_parser2("../design/smt-sweeping/case1/AES_Verilog.btor2", sts2, "b::");

    auto b_key_term = sts2.lookup("b::key");
    auto b_input_term = sts2.lookup("b::in");
    auto b_output_term = sts2.lookup("b::out");

    print_time();
    std::cout << "init solver" << std::endl;

    int count = 0;
    int unsat_count = 0;
    int sat_count = 0;

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
        assert(all_luts.find(var) == all_luts.end());
        create_lut(val, all_luts[var]);
        std::cout << "[array create] " << var->to_string() << " of size " << all_luts[var].size() << std::endl;
    }

    for (const auto & var_val_pair : sts2.init_constants()) {
        if(var_val_pair.first->get_sort()->get_sort_kind() != ARRAY)
            continue;
        Term var = var_val_pair.first;
        Term val = var_val_pair.second;
        assert(all_luts.find(var) == all_luts.end());
        create_lut(val, all_luts[var]);
        std::cout << "[array create] " << var->to_string() << " of size " << all_luts[var].size() << std::endl;
    }

    // Array comparison
    for (auto pos = all_luts.begin(); pos != all_luts.end(); ++ pos) {
        const auto & array_var_i = pos->first;
        auto array_size_i = pos->second.size();
        const auto & idx_val_i = pos->second;
        bool another_array_found = false;
        for (auto pos_j = all_luts.begin(); pos_j != pos; ++pos_j ) {
            auto array_size_j = pos_j->second.size();
            if (array_size_j != array_size_i)
                continue;
            const auto & idx_val_j = pos_j->second;
            bool all_equal = true;
            for (const auto & idx_val_pair : idx_val_i) {
                auto elem_pos = idx_val_j.find(idx_val_pair.first);
                if (elem_pos == idx_val_j.end()) {
                    // no such index
                    all_equal = false;
                    break;
                }
                if (elem_pos->second != idx_val_pair.second) {
                    all_equal = false;
                    break;
                }
            }
            if (!all_equal)
                continue;
            // if equal
            const auto & array_var_j = pos_j->first;
            // std::cout << "[sub array] " << array_var_i ->to_string() << " --> " << array_var_j->to_string() << std::endl;
            substitution_map.insert({array_var_i, array_var_j});
            another_array_found = true;
            // if you find one then it is okay, no need to find the rest
            break;
            // in case multiple pairs exists
            // 0 , 1, 2   . then 2-->0  1-->0
        }
        if (!another_array_found) {
            // std::cout << "[array not sub] " << array_var_i ->to_string() << std::endl;
            substitution_map.insert({array_var_i, array_var_i});
        }
    }


    //End of array init

    //print all luts
    // for (const auto & [var, lut] : all_luts) {
    //     std::cout << var->to_string() << ":" << std::endl;
    //     for (const auto & [idx, val] : lut) {
    //         std::cout << "Index: " << idx << ", Value: " << val << std::endl;
    //     }
    // }

    //simulation
    GmpRandStateGuard rand_guard;
    int num_iterations = 40;

    for (int i = 0; i < num_iterations; ++i) {
        mpz_t key_mpz, input_mpz;
        rand_guard.random_128(key_mpz);
        rand_guard.random_128(input_mpz);

        int bit_length = 128; 

        // Use RAII for GMP strings
        unique_ptr<char, void (*)(void *)> key_str(mpz_get_str(NULL, 2, key_mpz), free);
        unique_ptr<char, void (*)(void *)> input_str(mpz_get_str(NULL, 2, input_mpz), free);

        mpz_clear(key_mpz);
        mpz_clear(input_mpz);
        
        auto bv_input = btor_bv_const(input_str.get(), bit_length);
        auto bv_key = btor_bv_const(key_str.get(), bit_length);

        assert(bv_key->width == bv_input->width);

        //store sim data in NodeData
        node_data_map[a_key_term].get_simulation_data().push_back(*bv_key); // HZ: memory leak
        node_data_map[a_input_term].get_simulation_data().push_back(*bv_input);
        if (a_key_term != b_key_term)
            node_data_map[b_key_term].get_simulation_data().push_back(*bv_key);
        if (a_input_term != b_input_term)
            node_data_map[b_input_term].get_simulation_data().push_back(*bv_input);

        substitution_map.insert({a_key_term, a_key_term});
        substitution_map.insert({a_input_term, a_input_term});
        substitution_map.insert({b_key_term, a_key_term}); // b_key_term -> a_key_term
        substitution_map.insert({b_input_term, a_input_term}); // b_input_term -> a_input_term
    }
    assert(node_data_map[a_key_term].hash() == node_data_map[b_key_term].hash());
    assert(node_data_map[a_input_term].hash() == node_data_map[a_input_term].hash());

    hash_term_map.emplace(node_data_map[a_key_term].hash(), TermVec({a_key_term, b_key_term})); // they should have the same hash
    hash_term_map.emplace(node_data_map[a_input_term].hash(), TermVec({a_input_term, b_input_term}));

    // end of simulation
    assert(node_data_map[a_key_term].get_simulation_data().size() == num_iterations);
    assert(node_data_map[a_input_term].get_simulation_data().size() == num_iterations);
    assert(node_data_map[b_key_term].get_simulation_data().size() == num_iterations);
    assert(node_data_map[b_input_term].get_simulation_data().size() == num_iterations);


    solver->assert_formula(solver->make_term(Equal, a_key_term, b_key_term));
    solver->assert_formula(solver->make_term(Equal, a_input_term, b_input_term));

    solver->assert_formula(sts1.init());
    solver->assert_formula(sts2.init());
    for (const auto & c : sts1.constraints()) solver->assert_formula(c.first);
    for (const auto & c : sts2.constraints()) solver->assert_formula(c.first);


    //start post order traversal
    std::stack<std::pair<Term,bool>> node_stack;
    node_stack.push({root,false});

    print_time();
    cout << "End simulation, Start post order traversal" << endl;

    while(!node_stack.empty()) {
        // std::cout << "."; std::cout.flush();
        auto & [current,visited] = node_stack.top();
        if(substitution_map.find(current) != substitution_map.end()) {
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
            // std::cout << "-----op: " << op_type.to_string() << "-----" << std::endl;
            // cout << "----current: " << current->to_string() << "----" << endl;

            TermVec children(current->begin(), current->end());


            if(current->is_value()) { // constant
                // std::cout << "Constant: " << current->to_string().substr(2) << std::endl;

                auto current_str = current->to_string().substr(2);
                auto current_bv = btor_bv_char_to_bv(current_str.data());
                // cout << "current_bv width: " << current_bv->width <<", val:" << current_bv->val << endl;
                for (int i = 0; i < num_iterations; ++i) {
                    node_data_map[current].get_simulation_data().push_back(*current_bv);
                }
                // btor_bv_free(current_bv);

                assert(node_data_map[current].get_simulation_data().size() == num_iterations);
                // TODO: if you can find a term that is equivalent to this constant
                // case 1 : that term is also a constant, then they should be the same term (Boolector will merge them)
                // case 2 : that term is not a constant, you should not merge either
                // so constant don't need substitution
                substitution_map.insert({current, current}); 
                hash_term_map[node_data_map[current].hash()].push_back(current);
            } else if(current->is_symbolic_const() && current->get_op().is_null()) { // leaf nodes
                // std::cout << "leaf nodes: " << current->to_string() << std::endl;

                assert(TermVec(current->begin(), current->end()).empty());// no children
                assert(current->get_sort()->get_sort_kind() != ARRAY); // no array
                assert(node_data_map.find(current) != node_data_map.end()); // data should be computed
                assert(node_data_map[current].get_simulation_data().size() == num_iterations);

                //leaf nodes don't need substitution
                // substitution_map.insert({current, current}); 

                //update hash_term_map 
                assert(false); // for this example, we should not encounter this case                
            }
            else { // compute simulation data for current node
                // std::cout << "Computing : " << current->to_string() << std::endl;
                TermVec children(current->begin(), current->end()); // find children
                auto child_size = children.size();
                // cout << "children size: " << child_size << endl;

                // 1. substitute children
                bool substitution_happened = false;
                TermVec children_substituted;
                children_substitution(children, children_substituted, substitution_map);
                assert(children_substituted.size() == child_size);
                for (size_t i = 0; i < child_size; ++ i)
                    if (children_substituted.at(i) != children.at(i)) {
                        substitution_happened = true;
                        break;
                    }
                
                auto op_type = current->get_op();
                Term cnode = substitution_happened ? solver->make_term(op_type, children_substituted) : current;

                // 2. compute simulation
                NodeData sim_data;
                compute_simulation(children_substituted, num_iterations, op_type, node_data_map, all_luts, sim_data);
                auto current_hash = sim_data.hash();

                
                Term  term_eq;
                if (hash_term_map.find(current_hash) != hash_term_map.end()) {
                    const auto & sim_data_vec = sim_data.get_simulation_data();
                    TermVec terms_for_solving;
                    const auto & terms_to_check = hash_term_map.at(current_hash);
                    auto cnode_sort = cnode->get_sort();
                    for (const auto & t : terms_to_check) {
                        if (t == cnode) {
                            // structural_same_term_found
                            term_eq = t;
                            break; // no need to do the rest
                        }
                        if ( t->get_sort() != cnode_sort )
                            continue; // not equal
                        const auto & existing_sim_data = node_data_map.at(t).get_simulation_data();
                        bool all_equal = true;
                        for (unsigned rnd = 0; rnd < num_iterations; ++rnd) {
                            if(btor_bv_compare(&existing_sim_data[rnd], &sim_data_vec[rnd]) != 0) {
                                // not equal
                                all_equal = false;
                                break;
                            }
                        }
                        if (all_equal)
                            terms_for_solving.push_back(t);
                    } // end of filtering terms in terms_to_check --> terms_for_solving
                    if (term_eq == nullptr) { // if no structural same term found
                    //    std::cout << "c"  << terms_for_solving.size();
                       std::cout.flush();
                       for (const auto & t : terms_for_solving) {
                          auto result = solver->check_sat_assuming(TermVec({solver->make_term(Not, solver->make_term(Equal, t, cnode))}));
                          count ++;
                          if (result.is_unsat()) {
                            unsat_count ++;
                            term_eq = t;
                            break;
                          } else
                            sat_count ++;
                       } // end of check each term in terms_for_solving
                    } // end of structural_same_term_found
                }

                if (term_eq) {
                    substitution_map.emplace(current, term_eq);
                    // std::cout << "s"; std::cout.flush();
                } else {
                    substitution_map.emplace(current, cnode);
                    hash_term_map[current_hash].push_back(cnode);
                    node_data_map[cnode] = sim_data;
                }
            } // end if it has children
            node_stack.pop();            
        } // end of if visited
    } // end of traversal
    std::cout << std::endl;

    assert(substitution_map.find(root) != substitution_map.end());
    root = substitution_map.at(root);

    cout << "count: " << count << endl;
    cout << "unsat_count: " << unsat_count << endl;
    cout << "sat_count: " << sat_count << endl;
    print_time();
    std::cout << "Start checking sat" << std::endl;

    solver->assert_formula(solver->make_term(Not, root));
    auto res = solver->check_sat();
    print_time();
    if(res.is_unsat()){
        std::cout << "UNSAT" << std::endl;
    } else {
        std::cout << "SAT" << std::endl;
    }

    auto program_end_time = std::chrono::high_resolution_clock::now();
    auto total_time = std::chrono::duration_cast<std::chrono::milliseconds>(program_end_time - program_start_time).count();
    std::cout << "Total execution time: " << total_time / 1000.0 << " s" << std::endl;
    return 0;
}
