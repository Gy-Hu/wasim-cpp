# iDPV技术文档

# Btor2 预处理计划

## 1. 现有工具分析

### 1.1 核心处理组件

1. **Btor2解析和编码**
    
    ```cpp
    class BTOR2Encoder {
    public:
      // 构造函数，解析Btor2文件
      BTOR2Encoder(const std::string & filename,
                  TransitionSystem & ts,
                  const std::string & prefix = "");
    
      // 获取属性、输入和状态向量
      const smt::TermVec & propvec() const;
      const smt::TermVec & inputsvec() const;
      const smt::TermVec & statesvec() const;
    
    protected:
      // 布尔值和位向量转换
      smt::Term bool_to_bv(const smt::Term & t) const;
      smt::Term bv_to_bool(const smt::Term & t) const;
    
      // 预处理和解析
      void preprocess(const std::string & filename);
      void parse(const std::string filename);
    
      // 核心数据结构
      const smt::SmtSolver & solver_;
      wasim::TransitionSystem & ts_;
      smt::TermVec inputsvec_;
      smt::TermVec statesvec_;
      std::unordered_map<uint64_t, std::string> state_renaming_table;
    };
    
    ```
    
2. **Btor2操作映射**
    
    ```cpp
    // 位向量操作映射
    const unordered_map<Btor2Tag, smt::PrimOp> bvopmap({
        { BTOR2_TAG_add, BVAdd },
        { BTOR2_TAG_and, BVAnd },
        { BTOR2_TAG_concat, Concat },
        { BTOR2_TAG_mul, BVMul },
        { BTOR2_TAG_not, BVNot },
        { BTOR2_TAG_or, BVOr },
        { BTOR2_TAG_sdiv, BVSdiv },
        { BTOR2_TAG_sgt, BVSgt },
        { BTOR2_TAG_slt, BVSlt }
    });
    
    // 布尔操作映射
    const unordered_map<Btor2Tag, smt::PrimOp> boolopmap({
        { BTOR2_TAG_and, And },
        { BTOR2_TAG_or, Or },
        { BTOR2_TAG_xor, Xor },
        { BTOR2_TAG_not, Not },
        { BTOR2_TAG_iff, Equal }
    });
    
    ```
    
3. **特殊操作处理**
    
    ```cpp
    // 处理初始化
    if (l_->tag == BTOR2_TAG_init) {
        Term init_eq = solver_->make_term(Equal, termargs_);
        ts_.constrain_init(init_eq);
        terms_[l_->id] = init_eq;
    }
    
    // 处理状态更新
    if (l_->tag == BTOR2_TAG_next) {
        Term t0 = termargs_[0];
        Term t1 = termargs_[1];
        ts_.assign_next(t0, t1);
        terms_[l_->id] = t1;
    }
    
    // 处理约束
    if (l_->tag == BTOR2_TAG_constraint) {
        Term constraint = bv_to_bool(termargs_[0]);
        ts_.add_constraint(constraint);
        terms_[l_->id] = constraint;
    }
    
    ```
    
4. **转换系统管理**
    
    ```cpp
    class TransitionSystem {
    public:
      // 构造函数
      TransitionSystem(const smt::SmtSolver & s);
    
      // 状态和变量管理
      void add_statevar(const smt::Term & cv, const smt::Term & nv);
      void add_inputvar(const smt::Term & v);
      Term make_statevar(const string name, const Sort & sort);
      Term make_inputvar(const string name, const Sort & sort);
    
      // 状态转换和约束
      void set_init(const Term & init);
      void constrain_init(const Term & constraint);
      void assign_next(const Term & state, const Term & val);
      void add_constraint(const Term & constraint, bool to_init_and_next);
    
      // 状态访问
      Term curr(const Term & term) const;
      Term next(const Term & term) const;
      bool is_curr_var(const Term & sv) const;
      bool is_next_var(const Term & sv) const;
      bool is_input_var(const Term & sv) const;
    
      // 系统重建和优化
      void rebuild_trans_based_on_coi(const UnorderedTermSet & state_vars_in_coi,
                                    const UnorderedTermSet & input_vars_in_coi);
      void drop_state_updates(const TermVec & svs);
      void replace_terms(const smt::UnorderedTermMap & to_replace);
    
    protected:
      // 核心数据结构
      smt::SmtSolver solver_;
      smt::Term init_;                    // 初始状态约束
      smt::Term trans_;                   // 转换关系
      smt::UnorderedTermSet statevars_;   // 状��变量
      smt::UnorderedTermSet inputvars_;   // 输入变量
      smt::UnorderedTermMap state_updates_; // 状态更新函数
      smt::UnorderedTermMap next_map_;    // 当前到下一状态映射
      smt::UnorderedTermMap curr_map_;    // 下一到当前状态映射
      bool functional_;                    // 是否为功能性转换系统
      bool deterministic_;                 // 是否为确定性系统
    };
    
    ```
    
5. **状态和约束管理**
    
    ```cpp
    class StateAsmpt {
    public:
      // 构造函数
      StateAsmpt(const smt::UnorderedTermMap & sv,
                 const smt::TermVec & asmpt,
                 const std::vector<std::string> & assumption_interp);
    
      // 访问函数
      const smt::UnorderedTermMap & get_sv() const;
      const smt::TermVec & get_assumptions() const;
      const std::vector<std::string> & get_assumption_interp() const;
      smt::UnorderedTermMap & update_sv();
    
    protected:
      smt::UnorderedTermMap sv_;          // 状态变量映射
      smt::TermVec asmpt_;                // 约束条件
      std::vector<std::string> assumption_interp_; // 约束解释
    };
    
    ```
    
6. **轨迹管理**
    
    ```cpp
    class TraceManager {
    public:
      // 构造函数
      TraceManager(const TransitionSystem & ts, smt::SmtSolver & s);
    
      // 状态访问和更新
      const std::vector<StateAsmpt> & get_abs_state() const;
      std::vector<StateAsmpt> & update_abs_state();
    
      // 变量记录
      void record_x_var(const smt::Term & var);
      void record_x_var(const smt::TermVec & var);
      void record_x_var(const smt::UnorderedTermSet & var);
    
    protected:
      const TransitionSystem & ts_;
      smt::SmtSolver solver_;
      const smt::UnorderedTermSet & invar_;
      const smt::UnorderedTermSet & svar_;
      smt::UnorderedTermSet Xvar_;
      smt::UnorderedTermSet base_var_;
      std::vector<StateAsmpt> abs_state_;
    };
    
    ```
    

### 1.2 抽象和简化工具

1. **状态简化**
    - 工具：`framework/state_simplify.h/cpp`
    - 功能：
        - 状态空间归约
        - 等价状态合并
    - 核心实现：
        
        ```cpp
        // 状态简化
        void state_simplify_xvar(StateAsmpt & s,
                               const UnorderedTermSet & set_of_xvar,
                               const SmtSolver & solver);
        // 条件表达式简化
        Term expr_simplify_ite(const Term & expr,
                             const TermVec & assumptions,
                             const SmtSolver & solver);
        
        ```
        
2. **语法引导简化**
    - 工具：`framework/sygus_simplify.h/cpp`
    - 功能：
        - 语法层面优化
        - 表达式重写
    - 核实现：
        
        ```cpp
        // 表达式简化
        Term sygus_simplify_expr(
            const Term & expr,
            const UnorderedTermSet & set_of_xvar_btor,
            SmtSolver & solver);
        
        // 状态简化
        void sygus_simplify(StateAsmpt & state_btor,
                           const UnorderedTermSet & set_of_xvar_btor,
                           SmtSolver & solver);
        
        ```
        
3. **项操作工具**
    - 工具：`framework/term_manip.h/cpp`
    - 功能：
        - 符号创建和管理
        - 表达式构建和操作
    - 核心实现：
        
        ```cpp
        // 创建新的符号变量
        smt::Term free_make_symbol(const std::string & n,
                                  smt::Sort symb_sort,
                                  std::unordered_map<std::string, int> & name_cnt,
                                  smt::SmtSolver & solver);
        
        // 生成one-hot编码
        smt::TermVec one_hot0(const smt::TermVec & one_hot_vec,
                             smt::SmtSolver & solver);
        
        // 可满足性检查
        smt::Result is_sat_res(const smt::TermVec & expr_vec,
                              const smt::SmtSolver & solver,
                              smt::UnorderedTermMap * out = NULL);
        
        // 有效性检查
        bool is_valid_bool(const smt::Term & expr,
                          const smt::SmtSolver & solver);
        
        // 获取项参数
        smt::TermVec args(const smt::Term & term);
        
        ```
        
4. **替换和更新**
    
    ```cpp
    // 解析替换
    Term resolve_substitution(const Term &term,
                            std::unordered_map<Term, Term> &substitution_map);
    
    // 更新状态
    void update_state_updates(UnorderedTermMap & new_state_updates,
                            SubstitutionWalker & sw,
                            bool functional_);
    
    ```
    

### 1.3 分析工具

1. **符号遍历**
    - 工具：`framework/symtraverse.h/cpp`
    - 功能：
        - 状态空间遍历
        - 分支点管理
    - 核心实现：
        
        ```cpp
        class SymbolicTraverse {
        public:
            // 遍历一步
            unsigned traverse_one_step(
                const smt::TermVec & assumptions,
                const std::vector<TraverseBranchingNode> & branching_point);
        
            // 完整遍历
            unsigned traverse(
                const smt::TermVec & assumptions,
                const std::vector<TraverseBranchingNode> & branching_point);
        
        protected:
            // 状态管理
            bool deeper_choice();
            bool next_choice();
        
            // 可达性检查
            bool check_reachable(const StateAsmpt & state);
        
            // 状态简化
            void simplify_state(StateAsmpt & state);
        };
        
        ```
        
2. **AST遍历**
    - 工具：`apps/idpv/parallel-ast.cpp`
    - 功能：
        - AST节点深度计算
        - 等价节点识别
    - 核心实现：
        
        ```cpp
        class DepthWalker : public IdentityWalker {
        public:
            DepthWalker(const SmtSolver &solver,
                        unordered_map<Term, int> &node_depth_map)
                : IdentityWalker(solver, true),
                  node_depth_map_(node_depth_map) {}
        
        protected:
            virtual WalkerStepResult visit_term(Term &term) {
                if (node_depth_map_.find(term) != node_depth_map_.end()) {
                    return Walker_Skip;
                }
        
                int max_child_depth = -1;
                for (const auto &child : term) {
                    auto it = node_depth_map_.find(child);
                    if (it != node_depth_map_.end()) {
                        max_child_depth = max(max_child_depth, it->second);
                    }
                }
        
                node_depth_map_[term] = max_child_depth + 1;
                return Walker_Continue;
            }
        
        private:
            unordered_map<Term, int> &node_depth_map_;
        };
        
        ```
        
3. **独立性检查**
    - 工具：`framework/independence_check.h/cpp`
    - 功能：
        - 变量独立性分析
        - 依赖关系检查
    - 应用：
        
        ```cpp
        IndependenceChecker checker(ts);
        checker.check_independence(var1, var2);
        
        ```
        

### 1.4 Btor Sweeping

1. **核心数据结构**
    
    ```cpp
    // 位向量表示
    struct BtorBitVector {
      uint32_t width;
      #ifdef BTOR_USE_GMP
        mpz_t val;
      #else
        uint32_t len;
        BTOR_BV_TYPE bits[];
      #endif
    };
    
    // 节点数据管理
    class NodeData {
    private:
        Term term;
        size_t bit_width;
        std::vector<BtorBitVector> simulation_data;
    public:
        void add_data(const BtorBitVector& bv);
        size_t hash(const std::vector<BtorBitVector>& data);
    };
    
    ```
    
2. **位向量操作**
    
    ```cpp
    // 位向量基本操作
    BtorBitVector* btor_bv_and(const BtorBitVector* a, const BtorBitVector* b);
    BtorBitVector* btor_bv_concat(const BtorBitVector* a, const BtorBitVector* b);
    BtorBitVector* btor_bv_slice(const BtorBitVector* bv, uint32_t upper, uint32_t lower);
    
    // 等价性检查
    BtorBitVector* btor_bv_eq(const BtorBitVector* a, const BtorBitVector* b);
    
    ```
    
3. **等价类识别**
    
    ```cpp
    // 模拟数据收集
    for (int i = 0; i < num_iterations; ++i) {
        mpz_t key_mpz, input_mpz;
        rand_guard.random_128(key_mpz);
        rand_guard.random_128(input_mpz);
    
        // 收集模拟数据
        NodeData& nd = node_data_map[current];
        auto op_type = current->get_op();
        btor_bv_operation(op_type, btor_child_1, btor_child_2, nd);
    }
    
    // 等价性验证
    bool all_equal = true;
    for(size_t k = 0; k < num_iterations; ++k) {
        #ifdef BTOR_USE_GMP
            if(node_data_map[t].simulation_data[k].val !=
               node_data_map[current].simulation_data[k].val)
        #else
            if(node_data_map[t].simulation_data[k].bits !=
               node_data_map[current].simulation_data[k].bits ||
               node_data_map[t].simulation_data[k].len !=
               node_data_map[current].simulation_data[k].len)
        #endif
        {
            all_equal = false;
            break;
        }
    }
    
    // SMT求解验证
    if(all_equal) {
        auto eq_term = solver->check_sat_assuming(
            TermVec({solver->make_term(Not,
                    solver->make_term(Equal, t, current))}));
        if(eq_term.is_unsat()) {
            substitution_map.insert({current, t});
        }
    }
    
    ```
    
4. **替换应用**
    
    ```cpp
    // 构建替换映射
    std::unordered_map<Term, Term> substitution_map;
    std::unordered_map<uint32_t, TermVec> hash_term_map;
    
    // 应用替换
    for (const auto & sv : state_btor.get_sv()) {
        const auto & var = sv.first;
        const auto & expr = sv.second;
        auto expr_new = solver->substitute(expr, substitution_map);
        sv_to_replace.emplace(var, expr_new);
    }
    
    ```
    

## 2. 预处理策略实现

### 2.1 结构抽象

1. **独立性检查**
    
    ```cpp
    // 检查表达式e是否独立于变量v
    bool e_is_independent_of_v(const smt::Term & e,
                             const smt::Term & v,
                             const smt::TermVec & assumptions);
    
    // 检查表达式是否永远有效
    bool e_is_always_valid(const smt::Term & e,
                          smt::TermVec assumptions,
                          const smt::SmtSolver & s);
    
    // 检查表达式是否永远无效
    bool e_is_always_invalid(const smt::Term & e,
                           smt::TermVec assumptions,
                           const smt::SmtSolver & s);
    
    ```
    
2. **等价性检查**
    
    ```cpp
    // 检查初始条件
    check_res init_check(smt::Term init,
                        smt::Term inv,
                        smt::Term asmpt,
                        smt::SmtSolver & solver);
    
    // 检查不变式
    check_res inv_check(smt::Term inv,
                       smt::Term trans_update,
                       smt::Term asmpt,
                       TransitionSystem sts,
                       smt::SmtSolver & solver);
    
    // 检查属性
    check_res prop_check(smt::Term prop,
                        smt::Term inv,
                        smt::Term asmpt,
                        smt::SmtSolver & solver);
    
    ```
    
3. **等价类识别**
    
    ```cpp
    // 检查两个项是否在所有模拟数据上相等
    bool all_equal = true;
    for(size_t k = 0; k < num_iterations; ++k) {
        if (node_data_map[terms[i]].simulation_data[k] !=
            node_data_map[terms[j]].simulation_data[k]) {
            all_equal = false;
            break;
        }
    }
    
    ```
    

### 2.2 项操作和简化

1. **表达式简化**
    
    ```cpp
    // 简化ITE表达式
    smt::Term expr_simplify_ite(const smt::Term & expr,
                               const smt::TermVec & assumptions,
                               const smt::SmtSolver & solver);
    
    // 语法引导简化
    void sygus_simplify(StateAsmpt & state_btor,
                       const smt::UnorderedTermSet & set_of_xvar_btor,
                       smt::SmtSolver & solver);
    
    // 结构化简化
    static smt::Term structure_simplify(const smt::Term & v,
                                      const smt::TermVec & assumptions,
                                      const smt::UnorderedTermSet & set_of_xvar,
                                      smt::TermTranslator & translator);
    
    ```
    
2. **状态简化**
    
    ```cpp
    // 变量简化
    void get_xvar_independent(const smt::TermVec & assumptions,
                            const smt::UnorderedTermSet & set_of_xvar,
                            const smt::Term & expr,
                            const smt::SmtSolver & solver,
                            smt::UnorderedTermSet & xvar_that_can_be_removed);
    
    // 获取变量替换映射
    void get_xvar_sub(const smt::TermVec & assumptions,
                     const smt::UnorderedTermSet & set_of_xvar,
                     const smt::UnorderedTermSet & free_var,
                     const smt::SmtSolver & solver,
                     smt::UnorderedTermMap & xvar_sub);
    
    // 检查表达式是否包含X变量
    bool expr_contains_X(const smt::Term & expr,
                        const smt::UnorderedTermSet & set_of_xvar);
    
    // 检查表达式是否为常量
    smt::Term check_if_constant(const smt::Term & expr,
                               const smt::TermVec & assumptions,
                               const smt::SmtSolver & solver);
    
    // 检查布尔表达式是否可约简
    int is_reducible_bool(const smt::Term & expr,
                         const smt::TermVec & assumptions,
                         const smt::SmtSolver & solver);
    
    // 检查位向量表达式是否可约简
    int is_reducible_bv_width1(const smt::Term & expr,
                              const smt::TermVec & assumptions,
                              const smt::SmtSolver & solver);
    
    ```
    
3. **项操作工具**
    
    ```cpp
    // 创建新的符号变量
    smt::Term free_make_symbol(const std::string & n,
                              smt::Sort symb_sort,
                              std::unordered_map<std::string, int> & name_cnt,
                              smt::SmtSolver & solver);
    
    // 生成one-hot编码
    smt::TermVec one_hot0(const smt::TermVec & one_hot_vec,
                          smt::SmtSolver & solver);
    
    // 可满足性检查
    smt::Result is_sat_res(const smt::TermVec & expr_vec,
                          const smt::SmtSolver & solver,
                          smt::UnorderedTermMap * out = NULL);
    
    // 有效性检查
    bool is_valid_bool(const smt::Term & expr,
                      const smt::SmtSolver & solver);
    
    // 获取项的参数
    smt::TermVec args(const smt::Term & term);
    
    ```
    
4. **替换和更新**
    
    ```cpp
    // 解析替换
    Term resolve_substitution(const Term &term,
                            std::unordered_map<Term, Term> &substitution_map);
    
    // 更新状态
    void update_state_updates(UnorderedTermMap & new_state_updates,
                            SubstitutionWalker & sw,
                            bool functional_);
    
    ```
    

### 2.3 位宽操作

1. **位宽扩展和截断**
    
    ```cpp
    // 零���展
    Term zero_extended = solver_->make_term(Op(Zero_Extend, extend_width), term);
    
    // 符号扩展
    Term sign_extended = solver_->make_term(Op(Sign_Extend, extend_width), term);
    
    // 位截断
    Term extracted = solver_->make_term(Op(Extract, high_bit, low_bit), term);
    
    ```
    
2. **位宽检查和转换**
    
    ```cpp
    // 获取位宽
    int width = term->get_sort()->get_width();
    
    // 创建特定位宽的常量
    Sort sort = solver_->make_sort(BV, width);
    Term constant = solver_->make_term(value, sort);
    
    // 位宽匹配检查
    assert(t0->get_sort()->get_width() == t1->get_sort()->get_width());
    
    ```
    
3. **溢出检查**
    
    ```cpp
    // 无符号加法溢出检查
    Term t0_extended = solver_->make_term(Op(Zero_Extend, 1), t0);
    Term t1_extended = solver_->make_term(Op(Zero_Extend, 1), t1);
    Term sum = solver_->make_term(BVAdd, t0_extended, t1_extended);
    Term overflow = solver_->make_term(Op(Extract, width, width), sum);
    
    // 有符号加法溢出检查
    Term t0_top = solver_->make_term(Op(Extract, width - 1, width - 1), t0);
    Term t1_top = solver_->make_term(Op(Extract, width - 1, width - 1), t1);
    Term sum_top = solver_->make_term(Op(Extract, width - 1, width - 1), sum);
    Term overflow = solver_->make_term(Equal,
                                     solver_->make_term(Equal, t0_top, t1_top),
                                     solver_->make_term(Distinct, t0_top, sum_top));
    
    ```
    

### 2.4 数据流分析

1. **变量依赖分析**
    
    ```cpp
    // 获取自由变量
    smt::UnorderedTermSet free_vars;
    smt::get_free_symbols(expr, free_vars);
    
    // 检查变量依赖
    bool has_dependency = false;
    for (const auto & v : free_vars) {
        if (set_of_xvar.find(v) != set_of_xvar.end()) {
            has_dependency = true;
            break;
        }
    }
    
    ```
    
2. **状态依赖分析**
    
    ```cpp
    // 检查状态变量依赖
    bool has_state_dependency = false;
    for (const auto & v : free_vars) {
        if (ts.is_curr_var(v) || ts.is_next_var(v)) {
            has_state_dependency = true;
            break;
        }
    }
    
    // 检查输入变量依赖
    bool has_input_dependency = false;
    for (const auto & v : free_vars) {
        if (ts.is_input_var(v)) {
            has_input_dependency = true;
            break;
        }
    }
    
    ```
    
3. **约束依赖分析**
    
    ```cpp
    // 获取约束中的变量
    smt::UnorderedTermSet constraint_vars;
    for (const auto & constraint : constraints) {
        smt::get_free_symbols(constraint, constraint_vars);
    }
    
    // 检查约束依赖
    bool has_constraint_dependency = false;
    for (const auto & v : free_vars) {
        if (constraint_vars.find(v) != constraint_vars.end()) {
            has_constraint_dependency = true;
            break;
        }
    }
    
    ```
    

### 2.5 Btor Sweeping实现

1. **等价类识别**
    
    ```cpp
    void identify_equivalence_classes() {
        // 1. 哈希值计算
        std::unordered_map<uint32_t, TermVec> hash_term_map;
    
        // 2. 模拟数据收集
        for (const auto & term : terms) {
            NodeData nd(term);
            simulate_and_collect(nd);
            uint32_t hash = nd.hash(nd.get_simulation_data());
            hash_term_map[hash].push_back(term);
        }
    
        // 3. 等价性验证
        for (const auto & hash_terms : hash_term_map) {
            verify_equivalence_class(hash_terms.second);
        }
    }
    
    ```
    
2. **替换策略**
    
    ```cpp
    void apply_substitutions() {
        // 1. 构建替换映射
        UnorderedTermMap substitution_map;
    
        // 2. 验证和应用替换
        for (const auto & equiv_class : equivalence_classes) {
            Term representative = select_representative(equiv_class);
            for (const auto & term : equiv_class) {
                if (term != representative) {
                    substitution_map[term] = representative;
                }
            }
        }
    
        // 3. 执行替换
        Term result = solver->substitute(term, substitution_map);
    }
    
    ```
    

## 3. 优化流程

### 3.1 基本流程

1. **初始化和解析**
    
    ```cpp
    // 1. 创建求解器
    smt::SmtSolver solver = smt::BoolectorSolverFactory::create(false);
    solver->set_logic("QF_BV");
    solver->set_opt("produce-models", "true");
    solver->set_opt("incremental", "true");
    
    // 2. 创建转换系统
    TransitionSystem ts(solver);
    
    // 3. 解析Btor2文件
    BTOR2Encoder encoder(filename, ts);
    
    // 4. 获取系统信息
    const smt::TermVec & inputs = encoder.inputsvec();
    const smt::TermVec & states = encoder.statesvec();
    
    ```
    
2. **状态简化**
    
    ```cpp
    // 1. 创建状态和约束
    StateAsmpt state(sv_map, assumptions, assumption_interp);
    
    // 2. 变量独立性检查
    smt::UnorderedTermSet xvar_to_remove;
    get_xvar_independent(assumptions,
                        set_of_xvar,
                        expr,
                        solver,
                        xvar_to_remove);
    
    // 3. 状态变量简化
    state_simplify_xvar(state, set_of_xvar, solver);
    
    // 4. 语法引导简化
    sygus_simplify(state, set_of_xvar, solver);
    
    ```
    
3. **系统优化**
    
    ```cpp
    // 1. 重建转换系统
    ts.rebuild_trans_based_on_coi(state_vars_in_coi, input_vars_in_coi);
    
    // 2. 移除状态更新
    ts.drop_state_updates(state_vars_to_drop);
    
    // 3. 替换
    ts.replace_terms(term_substitution_map);
    
    // 4. 检查系统属性
    bool is_functional = ts.is_functional();
    bool is_deterministic = ts.is_deterministic();
    
    ```
    

### 3.2 正确性保证

```cpp
// 1. 可达性检查
bool reachable_before = tracemgr.check_reachable(abs_state);
state_simplify_xvar(abs_state, simulator_.get_Xs(), solver_);
bool reachable_after = tracemgr.check_reachable(abs_state);
assert(reachable_before && reachable_after);

// 2. 等价性检查
bool all_equal = true;
for(size_t k = 0; k < num_iterations; ++k) {
    if (node_data_map[terms[i]].simulation_data[k] !=
        node_data_map[terms[j]].simulation_data[k]) {
        all_equal = false;
        break;
    }
}

// 3. 约束验证
smt::Result r = solver->check_sat_assuming(assumptions);
if (!r.is_sat()) {
    // 约束不满足
    return nullptr;
}

```

## 4. 注意事项

### 4.1 求解器配置

```cpp
// 1. 求解器初始化
smt::SmtSolver solver = smt::BoolectorSolverFactory::create(false);

// 2. 逻辑设置
solver->set_logic("QF_BV");  // 使用位向量逻辑
solver->set_opt("produce-models", "true");  // 启用模型生成
solver->set_opt("incremental", "true");  // 启用增量求解

// 3. 求解器切换
smt::SmtSolver solver_cvc5 = smt::Cvc5SolverFactory::create(false);
smt::TermTranslator btor2cvc(solver_cvc5);  // 项转换器

```

### 4.2 状态管理注意点

```cpp
// 1. 状态变量检查
bool is_state = ts.is_curr_var(var);
bool is_next = ts.is_next_var(var);
bool is_input = ts.is_input_var(var);

// 2. 状态更新查
bool no_next_vars = ts.no_next(term);  // 检查否包含next变量

// 3. 约束添加
ts.constrain_init(constraint);  // 添加初始状态约束
ts.add_constraint(constraint, true);  // 添加全局约束

```

### 4.3 简化策略选择

```cpp
// 1. 变量独立性检查
if (expr_contains_X(expr, set_of_xvar)) {
    // 需要进行简化
    smt::UnorderedTermSet xvar_to_remove;
    get_xvar_independent(assumptions, set_of_xvar, expr, solver, xvar_to_remove);
}

// 2. 常量检查和简化
smt::Term constant = check_if_constant(expr, assumptions, solver);
if (constant != nullptr) {
    // 可以直接替换为常量
    return constant;
}

// 3. 条件表达式简化
if (expr->get_op() == smt::Ite) {
    return expr_simplify_ite(expr, assumptions, solver);
}

```

### 4.4 性能优化

```cpp
// 1. COI优化
ts.rebuild_trans_based_on_coi(state_vars_in_coi, input_vars_in_coi);

// 2. 状态更新优化
for (const auto & var : state_vars_in_coi) {
    const auto & elem = state_updates_.find(var);
    if (elem != state_updates_.end()) {
        Term next_func = elem->second;
        reduced_state_updates[var] = next_func;
    }
}

// 3. 约束优化
for (const auto & e : prev_constraints) {
    add_constraint(e.first, e.second);
}

```

### 4.5 正确性保证

```cpp
// 1. 可达性检查
bool reachable_before = tracemgr.check_reachable(abs_state);
state_simplify_xvar(abs_state, simulator_.get_Xs(), solver_);
bool reachable_after = tracemgr.check_reachable(abs_state);
assert(reachable_before && reachable_after);

// 2. 等价性检查
bool all_equal = true;
for(size_t k = 0; k < num_iterations; ++k) {
    if (node_data_map[terms[i]].simulation_data[k] !=
        node_data_map[terms[j]].simulation_data[k]) {
        all_equal = false;
        break;
    }
}

// 3. 约束验证
smt::Result r = solver->check_sat_assuming(assumptions);
if (!r.is_sat()) {
    // 约束不满足
    return nullptr;
}

```