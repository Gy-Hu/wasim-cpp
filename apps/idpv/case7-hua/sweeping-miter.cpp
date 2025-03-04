#include "assert.h"
#include "config/testpath.h"
#include "framework/symsim.h"
#include "framework/ts.h"
#include "frontend/btor2_encoder.h"
#include "smt-switch/bitwuzla_factory.h"
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
    if(op.prim_op == PrimOp::Not) {
        auto current_val = btor_bv_not(&btor_child_1);
        nd.get_simulation_data().push_back(*current_val);
    }
    else if(op.prim_op == PrimOp::BVNot) {
        auto current_val = btor_bv_not(&btor_child_1);
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
        nd.get_simulation_data().push_back(*current_val);
    }
    else if(op.prim_op == PrimOp::Zero_Extend) {
        auto current_val = btor_bv_uext(&btor_child_1, op.idx0);
        nd.get_simulation_data().push_back(*current_val);
    }
    else if(op.prim_op == PrimOp::Sign_Extend) {
        auto current_val = btor_bv_sext(&btor_child_1, op.idx0);
        nd.get_simulation_data().push_back(*current_val);
    }
    else if(op.prim_op == PrimOp::BVNeg) {
        auto current_val = btor_bv_neg(&btor_child_1);
        nd.get_simulation_data().push_back(*current_val);
    }
    else {
        cout << "Unsupported operation type 1 child: " << op.to_string() << endl;
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
    else if(op.prim_op == PrimOp::And) {
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
    else if(op.prim_op == PrimOp::Xor) {
        auto current_val = btor_bv_xor(&btor_child_1, &btor_child_2);
        nd.get_simulation_data().push_back(*current_val);
    }
    else if(op.prim_op == PrimOp::Or) {
        auto current_val = btor_bv_or(&btor_child_1, &btor_child_2);
        nd.get_simulation_data().push_back(*current_val);
    }
    else if(op.prim_op == PrimOp::BVOr) {
        auto current_val = btor_bv_or(&btor_child_1, &btor_child_2);
        nd.get_simulation_data().push_back(*current_val);
    }
    else if(op.prim_op == PrimOp::BVMul) {
        auto current_val = btor_bv_mul(&btor_child_1, &btor_child_2);
        nd.get_simulation_data().push_back(*current_val);
    }
    else if(op.prim_op == PrimOp::BVComp) {
        auto current_val = btor_bv_compare(&btor_child_1, &btor_child_2);
        auto current_val_bv = btor_bv_int64_to_bv(current_val, 1);
        nd.get_simulation_data().push_back(*current_val_bv);
    }
    else if(op.prim_op == PrimOp::Distinct) {
        auto current_val = btor_bv_ne(&btor_child_1, &btor_child_2);
        nd.get_simulation_data().push_back(*current_val);
    }
    else if(op.prim_op == PrimOp::BVUdiv) {
        auto current_val = btor_bv_udiv(&btor_child_1, &btor_child_2);
        nd.get_simulation_data().push_back(*current_val);
    }
    else if(op.prim_op == PrimOp::BVSub) {
        auto current_val = btor_bv_sub(&btor_child_1, &btor_child_2);
        nd.get_simulation_data().push_back(*current_val);
    }
    else if(op.prim_op == PrimOp::BVUlt) {
        auto current_val = btor_bv_ult(&btor_child_1, &btor_child_2);
        nd.get_simulation_data().push_back(*current_val);
    }
    else if(op.prim_op == PrimOp::BVUle) {
        auto current_val = btor_bv_ulte(&btor_child_1, &btor_child_2);
        nd.get_simulation_data().push_back(*current_val);
    }
    else if(op.prim_op == PrimOp::BVUgt) {
        auto current_val = btor_bv_ugt(&btor_child_1, &btor_child_2);
        nd.get_simulation_data().push_back(*current_val);
    }
    else if(op.prim_op == PrimOp::BVUge) {
        auto current_val = btor_bv_ugte(&btor_child_1, &btor_child_2);
        nd.get_simulation_data().push_back(*current_val);
    }
    else if(op.prim_op == PrimOp::BVSlt) {
        auto current_val = btor_bv_slt(&btor_child_1, &btor_child_2);
        nd.get_simulation_data().push_back(*current_val);
    }
    else if(op.prim_op == PrimOp::BVSle) {
        auto current_val = btor_bv_slte(&btor_child_1, &btor_child_2);
        nd.get_simulation_data().push_back(*current_val);
    }
    else if(op.prim_op == PrimOp::BVSgt) {
        auto current_val = btor_bv_sgt(&btor_child_1, &btor_child_2);
        nd.get_simulation_data().push_back(*current_val);
    }
    else if(op.prim_op == PrimOp::BVSge) {
        auto current_val = btor_bv_sgte(&btor_child_1, &btor_child_2);
        nd.get_simulation_data().push_back(*current_val);
    }
    else if(op.prim_op == PrimOp::BVNand) {
        auto current_val = btor_bv_nand(&btor_child_1, &btor_child_2);
        nd.get_simulation_data().push_back(*current_val);
    }
    else if(op.prim_op == PrimOp::BVNor) {
        auto current_val = btor_bv_nor(&btor_child_1, &btor_child_2);
        nd.get_simulation_data().push_back(*current_val);
    }
    else if(op.prim_op == PrimOp::BVXnor) {
        auto current_val = btor_bv_xnor(&btor_child_1, &btor_child_2);
        nd.get_simulation_data().push_back(*current_val);
    }
    else if(op.prim_op == PrimOp::BVUrem) {
        auto current_val = btor_bv_urem(&btor_child_1, &btor_child_2);
        nd.get_simulation_data().push_back(*current_val);
    }
    else if(op.prim_op == PrimOp::BVSdiv) {
        auto current_val = btor_bv_sdiv(&btor_child_1, &btor_child_2);
        nd.get_simulation_data().push_back(*current_val);
    }
    else if(op.prim_op == PrimOp::BVSrem) {
        auto current_val = btor_bv_srem(&btor_child_1, &btor_child_2);
        nd.get_simulation_data().push_back(*current_val);
    }
    else if(op.prim_op == PrimOp::BVLshr) {
        auto current_val = btor_bv_srl(&btor_child_1, &btor_child_2);
        nd.get_simulation_data().push_back(*current_val);
    }
    else if(op.prim_op == PrimOp::BVAshr) {
        auto current_val = btor_bv_sra(&btor_child_1, &btor_child_2);
        nd.get_simulation_data().push_back(*current_val);
    }
    else if(op.prim_op == PrimOp::BVShl) {
        auto current_val = btor_bv_sll(&btor_child_1, &btor_child_2);
        nd.get_simulation_data().push_back(*current_val);
    }
    else if(op.prim_op == PrimOp::Implies) {
        auto current_val = btor_bv_implies(&btor_child_1, &btor_child_2);
        nd.get_simulation_data().push_back(*current_val);
    }
    else {
        cout << "Unsupported operation type 2 children: " << op.to_string() << endl;
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
        cout << "Unsupported operation type 3 children: " << op.to_string() << endl;
        throw NotImplementedException("Unsupported operation type 3 children: " + op.to_string());
    }
}


//one child simulation
void process_single_child_simulation(const Term & child,  // HZ: const Term &
                              size_t num_iterations, 
                              const smt::Op& op_type,
                              const std::unordered_map<Term, NodeData> & node_data_map,
                              NodeData & out) {

    // cout << "--child: " << child->to_string() << endl;
    // cout << "***child type:" << child->get_sort()->get_width() << endl;
    // cout << "***child type:" << child->get_op().to_string() << endl;

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
        cout << "Unsupported number of children: " << children.size() << endl;
        throw NotImplementedException("Unsupported number of children: " + std::to_string(children.size()));
    }
}

void children_substitution(const smt::TermVec& children, smt::TermVec& out, const std::unordered_map<Term, Term>& substitution_map) {
	for (const auto & c : children) {
        // cout <<"c: "<< c->to_string() << endl;
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

    void random_input(mpz_t & rand_num, int num)
    {
        mpz_init2(rand_num, num);
        mpz_urandomb(rand_num, state, num);
    }

    // operator gmp_randstate_t &() { return state; }
};

void initialize_arrays(TransitionSystem& sts,
                       std::unordered_map<Term, std::unordered_map<std::string, std::string>>& all_luts,
                       std::unordered_map<Term, Term>& substitution_map
) {
    for (const auto & var_val_pair : sts.init_constants()) {
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
}

void simulation(const TermVec & input_terms,
                const int &num_iterations,
                TransitionSystem& sts,
                std::unordered_map<Term, NodeData>& node_data_map
){
    GmpRandStateGuard rand_guard;
    for(int i=0; i<num_iterations; i++){
        for(auto it : input_terms){
            auto width = it->get_sort()->get_width();
            mpz_t input_mpz;
            rand_guard.random_input(input_mpz,width);
            unique_ptr<char, void (*)(void *)> input_str(mpz_get_str(NULL, 2, input_mpz), free);
            mpz_clear(input_mpz);

            auto bv_input = btor_bv_const(input_str.get(), width);
            node_data_map[it].get_simulation_data().push_back(*bv_input);
        }
    }
}

void post_order(smt::Term& root,
                std::unordered_map<Term, NodeData>& node_data_map,
                std::unordered_map<uint32_t, TermVec>& hash_term_map,
                std::unordered_map<Term, Term>& substitution_map,
                std::unordered_map<Term, std::unordered_map<std::string, std::string>> all_luts,
                int& count,
                int& unsat_count,
                int& sat_count,
                SmtSolver& solver,
                int& num_iterations,
                int timeout_ms = 1000) // Add timeout parameter, default is 1 second
{
    std::stack<std::pair<Term,bool>> node_stack;
    node_stack.push({root,false});

    // Variables for progress tracking
    int total_nodes = 0;
    int processed_nodes = 0;
    enum SweepingStep { NONE, SUBST_CHECK, NEW_NODE, SIM_COMP, EQUIV_SEARCH, MAP_UPDATE };
    SweepingStep current_step = NONE;
    std::string step_names[] = {
        "IDLE",
        "SUBST CHECK",
        "NEW NODE",
        "SIM COMP",
        "EQUIV SEARCH",
        "MAP UPDATE"
    };

    // First pass to count total nodes (optional but gives more accurate progress)
    {
        std::stack<Term> count_stack;
        std::unordered_set<Term> visited;
        count_stack.push(root);
        
        while (!count_stack.empty()) {
            Term current = count_stack.top();
            count_stack.pop();
            
            if (visited.find(current) != visited.end())
                continue;
                
            visited.insert(current);
            total_nodes++;
            
            for (Term child : current) {
                if (child->get_sort()->get_sort_kind() == BV || child->get_sort()->get_sort_kind() == BOOL) {
                    count_stack.push(child);
                }
            }
        }
    }
    
    std::cout << "Begin sweeping with " << total_nodes << " nodes..." << std::endl;
    // std::cout << "============================" << std::endl;

    // Function to update and display progress
    auto update_progress = [&](SweepingStep step) {
        current_step = step;
        const int bar_width = 50;
        float progress = (float)processed_nodes / total_nodes;
        
        std::cout << "\r[";
        int pos = bar_width * progress;
        for (int i = 0; i < bar_width; ++i) {
            if (i < pos) std::cout << "=";
            else if (i == pos) std::cout << ">";
            else std::cout << " ";
        }
        std::cout << "] " << int(progress * 100.0) << "% | "
                  << "Step: " << step_names[step] << " | "
                  << processed_nodes << "/" << total_nodes << " nodes"
                  << std::flush;
    };

    while(!node_stack.empty()) {
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
            TermVec children(current->begin(), current->end());

            if(current->is_value()) { // constant
                auto current_str = current->to_string().substr(2);
                auto current_bv = btor_bv_char_to_bv(current_str.data());
                
                update_progress(SIM_COMP);
                for (int i = 0; i < num_iterations; ++i) {
                    node_data_map[current].get_simulation_data().push_back(*current_bv);
                }

                assert(node_data_map[current].get_simulation_data().size() == num_iterations);
                
                update_progress(MAP_UPDATE);
                substitution_map.insert({current, current}); 
                hash_term_map[node_data_map[current].hash()].push_back(current);
                
                processed_nodes++;
            } 
            else if(current->is_symbolic_const() && current->get_op().is_null()) { // leaf nodes
                update_progress(MAP_UPDATE);
                
                assert(TermVec(current->begin(), current->end()).empty());// no children
                assert(current->get_sort()->get_sort_kind() != ARRAY); // no array
                assert(node_data_map.find(current) != node_data_map.end()); // data should be computed
                assert(node_data_map[current].get_simulation_data().size() == num_iterations);

                substitution_map.insert({current, current}); 
                
                processed_nodes++;           
            }
            else { // compute simulation data for current node
                TermVec children(current->begin(), current->end()); // find children
                auto child_size = children.size();

                update_progress(SUBST_CHECK);
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
                
                update_progress(NEW_NODE);
                Term cnode = substitution_happened ? solver->make_term(op_type, children_substituted) : current;

                update_progress(SIM_COMP);
                NodeData sim_data;
                compute_simulation(children_substituted, num_iterations, op_type, node_data_map, all_luts, sim_data);
                auto current_hash = sim_data.hash();

                update_progress(EQUIV_SEARCH);
                Term term_eq;
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
                       for (const auto & t : terms_for_solving) {
                          // Set timeout option - Bitwuzla expects time-limit in seconds
                        //   solver->set_opt("time-limit", std::to_string(timeout_ms / 1000.0));
                          
                          // Record start time
                          auto start_time = std::chrono::high_resolution_clock::now();
                          
                          // Execute solver
                          auto result = solver->check_sat_assuming(TermVec({solver->make_term(Not, solver->make_term(Equal, t, cnode))}));
                          
                          // Calculate solving time
                          auto end_time = std::chrono::high_resolution_clock::now();
                          auto elapsed = std::chrono::duration_cast<std::chrono::milliseconds>(end_time - start_time).count();
                          
                          count++;
                          
                          // Check if timeout occurred
                          if (elapsed >= timeout_ms) {
                              // Timeout, skip current merge
                              std::cout << "-t-"; // Output 't' to indicate timeout
                              std::cout.flush();
                              continue; 
                          }
                          
                          if (result.is_unsat()) {
                            unsat_count++;
                            term_eq = t;
                            break;
                          } else {
                            sat_count++;
                          }
                       } // end of check each term in terms_for_solving
                    } // end of structural_same_term_found
                }

                update_progress(MAP_UPDATE);
                if (term_eq) {
                    substitution_map.emplace(current, term_eq);
                } else {
                    substitution_map.emplace(current, cnode);
                    hash_term_map[current_hash].push_back(cnode);
                    node_data_map[cnode] = sim_data;
                }
                
                processed_nodes++;
            } // end if it has children
            node_stack.pop();            
        } // end of if visited
    } // end of traversal
    
    // End of processing - Print summary statistics
    std::cout << std::endl;
    // std::cout << "============================" << std::endl;
    std::cout << "Sweeping Summary Statistics:" << std::endl;
    std::cout << "============================" << std::endl;
    
    // Count total terms and find top 5 hash values by frequency
    int total_terms = 0;
    std::vector<std::pair<uint32_t, size_t>> hash_frequencies;
    
    for (const auto& [hash_value, terms] : hash_term_map) {
        hash_frequencies.push_back({hash_value, terms.size()});
        total_terms += terms.size();
    }
    
    // Sort by frequency (highest first)
    std::sort(hash_frequencies.begin(), hash_frequencies.end(), 
              [](const auto& a, const auto& b) { return a.second > b.second; });
    
    std::cout << "Total unique hash values: " << hash_term_map.size() << std::endl;
    std::cout << "Total terms processed: " << total_terms << std::endl;
    std::cout << "Shared hash value ratio: " << (float)(total_terms - hash_term_map.size()) / total_terms * 100.0 << "%" << std::endl;
    
    // Display top 5 hash values with highest term counts
    std::cout << std::endl;
    std::cout << "Top 5 Hash Values by Term Frequency:" << std::endl;
    std::cout << "-----------------------------------" << std::endl;
    std::cout << std::setw(12) << "Hash Value" << " | " 
              << std::setw(10) << "Term Count" << " | " 
              << std::setw(10) << "% of Total" << std::endl;
    std::cout << "-----------------------------------" << std::endl;
    
    int to_display = std::min(5, static_cast<int>(hash_frequencies.size()));
    for (int i = 0; i < to_display; i++) {
        const auto& [hash_value, count] = hash_frequencies[i];
        float percentage = (float)count / total_terms * 100.0;
        
        std::cout << std::setw(12) << hash_value << " | " 
                  << std::setw(10) << count << " | " 
                  << std::setw(9) << std::fixed << std::setprecision(2) << percentage << "%" << std::endl;
    }
    
    std::cout << "============================" << std::endl;
    std::cout << "Sweeping done, begin the last solving using bitwuzla for this property" << std::endl;
}

int main(int argc, char* argv[]) {
    if (argc < 3) {
        std::cerr << "Usage: " << argv[0] << " <BTOR2_FILE_PATH> <SIMULATION_ITERATIONS> [TIMEOUT_MS] [DUMP_SMT]" << std::endl;
        std::cerr << "  BTOR2_FILE_PATH: Path to the BTOR2 file" << std::endl;
        std::cerr << "  SIMULATION_ITERATIONS: Number of simulation iterations" << std::endl;
        std::cerr << "  TIMEOUT_MS: Optional timeout for solver and property checking in milliseconds (default: 50000)" << std::endl;
        std::cerr << "  DUMP_SMT: Optional flag to enable/disable SMT dumping (0=disable, 1=enable, default: 1)" << std::endl;
        return 1;
    }

    std::string btor2_file = argv[1];
    
    int num_iterations = 0;
    try {
        num_iterations = std::stoi(argv[2]);
    } catch (const std::invalid_argument& e) {
        std::cerr << "Error: Invalid number format for SIMULATION_ITERATIONS" << std::endl;
        return 1;
    } catch (const std::out_of_range& e) {
        std::cerr << "Error: SIMULATION_ITERATIONS is out of range" << std::endl;
        return 1;
    }

    auto program_start_time = std::chrono::high_resolution_clock::now();
    last_time_point = program_start_time;

    // Single timeout parameter for both solver and property checking; default is 50000 ms
    int timeout_ms = 50000;
    if (argc >= 4) {
        try {
            timeout_ms = std::stoi(argv[3]);
        } catch (const std::invalid_argument& e) {
            std::cerr << "Warning: Invalid timeout value, using default (50000ms)" << std::endl;
        } catch (const std::out_of_range& e) {
            std::cerr << "Warning: Timeout value out of range, using default (50000ms)" << std::endl;
        }
    }

    SmtSolver solver = BitwuzlaSolverFactory::create(false);

    solver->set_logic("QF_UFBV");
    solver->set_opt("incremental", "true");
    solver->set_opt("produce-models", "true");
    solver->set_opt("produce-unsat-assumptions", "true");
    solver->set_opt("time-limit", std::to_string(timeout_ms / 1000.0));

    // Loading and parsing BTOR2 files
    TransitionSystem sts(solver);
    BTOR2Encoder btor_parser(btor2_file, sts, "a::");

    std::cout << "============================" << std::endl;

    const auto& input_terms = btor_parser.inputsvec(); // all input here
    const auto& output_terms = btor_parser.get_output_terms(); // all output here
    const auto& constraints = btor_parser.get_const_terms(); // all constraints here
    const auto& property = btor_parser.propvec(); // all properties here
    const auto& idvec = btor_parser.idvec();

    for(auto c : constraints) {
        solver->assert_formula(c);
    }

    std::unordered_map<Term, NodeData> node_data_map; // term -> simulation data
    std::unordered_map<uint32_t, TermVec> hash_term_map; // hash -> TermVec
    std::unordered_map<Term, Term> substitution_map; // term -> term, for substitution
    std::unordered_map<Term, std::unordered_map<std::string, std::string>> all_luts; // state -> lookup table

    std::cout << "stage 1 : init array & simulation ...";
    // Array initialization
    initialize_arrays(sts, all_luts, substitution_map);
    // Simulation
    simulation(input_terms, num_iterations, sts, node_data_map);
    std::cout << "done" << std::endl;
   
    for(auto i : input_terms) {
        assert(node_data_map[i].get_simulation_data().size() == num_iterations);
        substitution_map.insert({i, i});
        hash_term_map[node_data_map[i].hash()].push_back(i);
    }

    solver->assert_formula(sts.init());
    for (const auto & c : sts.constraints()) {
        solver->assert_formula(c.first);
    }
    
    int count = 0;
    int unsat_count = 0;
    int sat_count = 0;
    int i = 0;
    
    bool dump_smt = true; // Default is to dump SMT
    if (argc >= 5) {
        try {
            int dump_smt_int = std::stoi(argv[4]);
            dump_smt = (dump_smt_int != 0);
        } catch (const std::invalid_argument& e) {
            std::cerr << "Warning: Invalid DUMP_SMT value, using default (enabled)" << std::endl;
        } catch (const std::out_of_range& e) {
            std::cerr << "Warning: DUMP_SMT value out of range, using default (enabled)" << std::endl;
        }
    }
    
    std::cout << "Using timeout: " << timeout_ms << "ms (" << (timeout_ms / 1000.0) << "s)" << std::endl;
    std::cout << "SMT dumping: " << (dump_smt ? "enabled" : "disabled") << std::endl;

    std::cout << "stage 2 : begin sweeping ... " << std::endl;
    std::cout << "============================" << std::endl;
    
    for(auto root : property) {
        post_order(root, node_data_map, hash_term_map, substitution_map, all_luts, count, unsat_count, sat_count, solver, num_iterations, timeout_ms);
        root = substitution_map.at(root);

        std::cout << "Property ID: " << idvec[i] << " ";
        solver->push();
        auto not_root = solver->make_term(Not, root);
        solver->assert_formula(not_root);
        
        if (dump_smt) {
            SmtSolver dump_solver = BitwuzlaSolverFactory::create(false);
            dump_solver->set_logic("QF_UFBV");
            smt::TermTranslator translator(dump_solver);
            auto translated_not_root = translator.transfer_term(not_root);
            dump_solver->assert_formula(translated_not_root);
            
            std::string safe_path = btor2_file;
            std::replace(safe_path.begin(), safe_path.end(), '/', '_');
            std::replace(safe_path.begin(), safe_path.end(), '\\', '_');
            dump_solver->dump_smt2("property_" + std::to_string(idvec[i]) + "_" + safe_path + ".smt2");
            std::cout << "SMT file dumped for property " << idvec[i] << std::endl;
        }
        
        std::cout << "Timeout used for property checking: " << timeout_ms << "ms (" << (timeout_ms / 1000.0) << "s)" << std::endl;
        
        auto start_time = std::chrono::high_resolution_clock::now();
        auto res = solver->check_sat();
        auto end_time = std::chrono::high_resolution_clock::now();
        auto duration = std::chrono::duration_cast<std::chrono::milliseconds>(end_time - start_time).count();
        
        solver->pop();

        if (res.is_unsat()) {
            std::cout << "Result : UNSAT (took " << duration << "ms)" << std::endl;
        } else if (res.is_sat()) {
            std::cout << "Result : SAT (took " << duration << "ms)" << std::endl;
        } else {
            std::cout << "Result : UNKNOWN - likely timed out after " << duration << "ms" << std::endl;
        }

        std::cout << "For this property, " << unsat_count << " UNSAT when merging, and " << sat_count << " SAT when merging" << std::endl;
        std::cout << "-----------------" << std::endl;

        i++;
    }
    
    std::cout << "All property done" << std::endl;
    auto program_end_time = std::chrono::high_resolution_clock::now();
    auto total_time = std::chrono::duration_cast<std::chrono::milliseconds>(program_end_time - program_start_time).count();
    std::cout << "Total execution time: " << total_time / 1000.0 << " s" << std::endl;
    std::cout << "============================" << std::endl;

    return 0;
}