 #include "smt-switch/utils.h"                                                                                                                             
 #include "frontend/btor2_encoder.h"                                                                                                                       
 #include "utils/logger.h"                                                                                                                                 
 #include "framework/ts.h"                                                                                                                                 
 #include "smt-switch/boolector_factory.h"                                                                                                                 
 #include "smt-switch/identity_walker.h"                                                                                                                   
                                                                                                                                                           
 #include <iostream>                                                                                                                                       
 #include <string>                                                                                                                                         
 #include <fstream>                                                                                                                                        
 #include <chrono>                                                                                                                                         
 #include <memory>                                                                                                                                         
 #include <vector>                                                                                                                                         
 #include <unordered_map>                                                                                                                                  
 #include <thread>                                                                                                                                         
 #include <mutex>                                                                                                                                          
 #include <queue>                                                                                                                                          
                                                                                                                                                           
 using namespace wasim;                                                                                                                                    
 using namespace smt;                                                                                                                                      
 using namespace std;                                                                                                                                      
                                                                                                                                                           
 class BatchProcessor {                                                                                                                                    
 public:                                                                                                                                                   
     static constexpr size_t BATCH_SIZE = 10000; // 每批处理的行数                                                                                         
     static constexpr size_t MAX_MEMORY = 1024 * 1024 * 1024; // 1GB 内存限制                                                                              
                                                                                                                                                           
     BatchProcessor(const SmtSolver& solver) : solver_(solver) {}                                                                                          
                                                                                                                                                           
     // 处理一个表达式，返回处理后的项                                                                                                                     
     Term process_term(const Term& term) {                                                                                                                 
         string term_str = term->to_string();                                                                                                              
                                                                                                                                                           
         // 检查缓存                                                                                                                                       
         {                                                                                                                                                 
             lock_guard<mutex> lock(cache_mutex_);                                                                                                         
             auto it = term_cache_.find(term_str);                                                                                                         
             if (it != term_cache_.end()) {                                                                                                                
                 return it->second;                                                                                                                        
             }                                                                                                                                             
         }                                                                                                                                                 
                                                                                                                                                           
         Term result;                                                                                                                                      
         if (term->is_symbolic_const()) {                                                                                                                  
             result = term;                                                                                                                                
         } else {                                                                                                                                          
             // 递归处理子项                                                                                                                               
             TermVec new_children;                                                                                                                         
             for (const Term& child : term->get_children()) {                                                                                              
                 new_children.push_back(process_term(child));                                                                                              
             }                                                                                                                                             
                                                                                                                                                           
             // 创建新项                                                                                                                                   
             if (new_children.empty()) {                                                                                                                   
                 result = term;                                                                                                                            
             } else {                                                                                                                                      
                 result = solver_->make_term(term->get_op(), new_children);                                                                                
             }                                                                                                                                             
         }                                                                                                                                                 
                                                                                                                                                           
         // 更新缓存                                                                                                                                       
         {                                                                                                                                                 
             lock_guard<mutex> lock(cache_mutex_);                                                                                                         
             term_cache_[term_str] = result;                                                                                                               
         }                                                                                                                                                 
                                                                                                                                                           
         return result;                                                                                                                                    
     }                                                                                                                                                     
                                                                                                                                                           
     // 清理缓存以释放内存                                                                                                                                 
     void clear_cache() {                                                                                                                                  
         lock_guard<mutex> lock(cache_mutex_);                                                                                                             
         term_cache_.clear();                                                                                                                              
     }                                                                                                                                                     
                                                                                                                                                           
 private:                                                                                                                                                  
     const SmtSolver& solver_;                                                                                                                             
     unordered_map<string, Term> term_cache_;                                                                                                              
     mutex cache_mutex_;                                                                                                                                   
 };                                                                                                                                                        
                                                                                                                                                           
 class BtorPreprocessor {                                                                                                                                  
 private:                                                                                                                                                  
     SmtSolver solver_;                                                                                                                                    
     TransitionSystem ts_;                                                                                                                                 
     BatchProcessor batch_processor_;                                                                                                                      
     static constexpr size_t BUFFER_SIZE = 64 * 1024 * 1024;  // 64MB buffer                                                                               
                                                                                                                                                           
     // 分批写入变量声明                                                                                                                                   
     void write_vars_batch(ofstream& out, const UnorderedTermSet& vars, const string& type) {                                                              
         vector<Term> vars_vec(vars.begin(), vars.end());                                                                                                  
         size_t total = vars.size();                                                                                                                       
         size_t batch_size = BatchProcessor::BATCH_SIZE;                                                                                                   
                                                                                                                                                           
         for (size_t i = 0; i < total; i += batch_size) {                                                                                                  
             size_t current_batch_size = min(batch_size, total - i);                                                                                       
             stringstream batch_ss;                                                                                                                        
                                                                                                                                                           
             for (size_t j = 0; j < current_batch_size; j++) {                                                                                             
                 const Term& var = vars_vec[i + j];                                                                                                        
                 batch_ss << "(declare-fun |" << var->to_string()                                                                                          
                         << "| () " << var->get_sort()->to_string() << ")\n";                                                                              
             }                                                                                                                                             
                                                                                                                                                           
             out << batch_ss.str();                                                                                                                        
             out.flush();                                                                                                                                  
                                                                                                                                                           
             cout << "Processed " << min(i + batch_size, total) << "/" << total                                                                            
                  << " " << type << "\n";                                                                                                                  
         }                                                                                                                                                 
     }                                                                                                                                                     
                                                                                                                                                           
     // 分批处理约束                                                                                                                                       
     void write_constraints_batch(ofstream& out,                                                                                                           
                                const vector<pair<Term, bool>>& constraints) {                                                                             
         size_t total = constraints.size();                                                                                                                
         size_t batch_size = BatchProcessor::BATCH_SIZE;                                                                                                   
                                                                                                                                                           
         for (size_t i = 0; i < total; i += batch_size) {                                                                                                  
             size_t current_batch_size = min(batch_size, total - i);                                                                                       
             stringstream batch_ss;                                                                                                                        
                                                                                                                                                           
             for (size_t j = 0; j < current_batch_size; j++) {                                                                                             
                 const auto& constraint = constraints[i + j];                                                                                              
                 if (!constraint.first->is_value()) {                                                                                                      
                     Term processed = batch_processor_.process_term(constraint.first);                                                                     
                     batch_ss << "(assert " << processed->to_string() << ")\n";                                                                            
                 }                                                                                                                                         
             }                                                                                                                                             
                                                                                                                                                           
             out << batch_ss.str();                                                                                                                        
             out.flush();                                                                                                                                  
                                                                                                                                                           
             cout << "Processed " << min(i + batch_size, total) << "/" << total                                                                            
                  << " constraints\n";                                                                                                                     
                                                                                                                                                           
             // 定期清理缓存以控制内存使用                                                                                                                 
             if ((i + batch_size) % (batch_size * 10) == 0) {                                                                                              
                 batch_processor_.clear_cache();                                                                                                           
             }                                                                                                                                             
         }                                                                                                                                                 
     }                                                                                                                                                     
                                                                                                                                                           
     // 写入属性                                                                                                                                           
     void write_properties(ofstream& out, const TermVec& props) {                                                                                          
         if (!props.empty()) {                                                                                                                             
             stringstream ss;                                                                                                                              
             if (props.size() == 1) {                                                                                                                      
                 Term processed = batch_processor_.process_term(props[0]);                                                                                 
                 ss << "(assert (not " << processed->to_string() << "))\n";                                                                                
             } else {                                                                                                                                      
                 ss << "(assert (not (and";                                                                                                                
                 for (const Term& prop : props) {                                                                                                          
                     Term processed = batch_processor_.process_term(prop);                                                                                 
                     ss << " " << processed->to_string();                                                                                                  
                 }                                                                                                                                         
                 ss << ")))\n";                                                                                                                            
             }                                                                                                                                             
             out << ss.str();                                                                                                                              
         }                                                                                                                                                 
     }                                                                                                                                                     
                                                                                                                                                           
 public:                                                                                                                                                   
     BtorPreprocessor() :                                                                                                                                  
         solver_(BoolectorSolverFactory::create(false)),                                                                                                   
         ts_(solver_),                                                                                                                                     
         batch_processor_(solver_)                                                                                                                         
     {                                                                                                                                                     
         solver_->set_logic("QF_BV");                                                                                                                      
         solver_->set_opt("incremental", "true");                                                                                                          
     }                                                                                                                                                     
                                                                                                                                                           
     void preprocess(const string& input_file, const string& output_file) {                                                                                
         // 获取输入文件大小用于进度报告                                                                                                                   
         ifstream in(input_file, ios::ate | ios::binary);                                                                                                  
         if (!in.is_open()) {                                                                                                                              
             throw runtime_error("Cannot open input file: " + input_file);                                                                                 
         }                                                                                                                                                 
         size_t file_size = in.tellg();                                                                                                                    
         in.close();                                                                                                                                       
                                                                                                                                                           
         cout << "Processing BTOR2 file of size: " << file_size / (1024*1024) << "MB\n";                                                                   
                                                                                                                                                           
         // 解析 BTOR2 文件                                                                                                                                
         auto parse_start = chrono::steady_clock::now();                                                                                                   
         cout << "Parsing BTOR2 file...\n";                                                                                                                
         BTOR2Encoder encoder(input_file, ts_);                                                                                                            
         auto parse_end = chrono::steady_clock::now();                                                                                                     
         auto parse_duration = chrono::duration_cast<chrono::seconds>(parse_end - parse_start);                                                            
         cout << "Parsing completed in " << parse_duration.count() << " seconds.\n";                                                                       
                                                                                                                                                           
         // 生成 SMT2 文件                                                                                                                                 
         cout << "Generating SMT2 files...\n";                                                                                                             
         auto gen_start = chrono::steady_clock::now();                                                                                                     
                                                                                                                                                           
         const TermVec& props = ts_.prop();                                                                                                                
                                                                                                                                                           
         // 为每个 property 生成单独的 SMT2 文件                                                                                                           
         for (size_t i = 0; i < props.size(); ++i) {                                                                                                       
             string prop_output_file = output_file;                                                                                                        
             auto dot_pos = prop_output_file.find_last_of('.');                                                                                            
             if (dot_pos != string::npos) {                                                                                                                
                 prop_output_file.insert(dot_pos, "_prop" + to_string(i));                                                                                 
             } else {                                                                                                                                      
                 prop_output_file += "_prop" + to_string(i);                                                                                               
             }                                                                                                                                             
                                                                                                                                                           
             cout << "\nGenerating SMT2 file for property " << i << "...\n";                                                                               
             TermVec single_prop = {props[i]};                                                                                                             
             dump_smt2(prop_output_file, single_prop);                                                                                                     
                                                                                                                                                           
             // 每个属性处理完后清理缓存                                                                                                                   
             batch_processor_.clear_cache();                                                                                                               
         }                                                                                                                                                 
                                                                                                                                                           
         auto gen_end = chrono::steady_clock::now();                                                                                                       
         auto gen_duration = chrono::duration_cast<chrono::seconds>(gen_end - gen_start);                                                                  
         cout << "SMT2 generation completed in " << gen_duration.count() << " seconds.\n";                                                                 
     }                                                                                                                                                     
                                                                                                                                                           
     void dump_smt2(const string& output_file, const TermVec& props_to_check) {                                                                            
         ofstream out(output_file, ios::binary);                                                                                                           
         if (!out.is_open()) {                                                                                                                             
             throw runtime_error("Cannot open output file: " + output_file);                                                                               
         }                                                                                                                                                 
                                                                                                                                                           
         // 设置文件缓冲区                                                                                                                                 
         vector<char> buffer(BUFFER_SIZE);                                                                                                                 
         out.rdbuf()->pubsetbuf(buffer.data(), BUFFER_SIZE);                                                                                               
                                                                                                                                                           
         // 写入头部                                                                                                                                       
         out << ";; Generated by IDPV Btor2 Preprocessor\n(set-logic QF_BV)\n";                                                                            
                                                                                                                                                           
         // 分批写入变量声明                                                                                                                               
         cout << "Writing input variables...\n";                                                                                                           
         write_vars_batch(out, ts_.inputvars(), "input variables");                                                                                        
                                                                                                                                                           
         cout << "Writing state variables...\n";                                                                                                           
         write_vars_batch(out, ts_.statevars(), "state variables");                                                                                        
                                                                                                                                                           
         // 写入初始状态                                                                                                                                   
         cout << "Writing initial state...\n";                                                                                                             
         Term processed_init = batch_processor_.process_term(ts_.init());                                                                                  
         out << "(assert " << processed_init->to_string() << ")\n";                                                                                        
         out.flush();                                                                                                                                      
                                                                                                                                                           
         // 分批写入约束                                                                                                                                   
         cout << "Writing constraints...\n";                                                                                                               
         write_constraints_batch(out, ts_.constraints());                                                                                                  
                                                                                                                                                           
         // 写入属性                                                                                                                                       
         cout << "Writing properties...\n";                                                                                                                
         write_properties(out, props_to_check);                                                                                                            
                                                                                                                                                           
         // 写入结尾                                                                                                                                       
         out << "(check-sat)\n(exit)\n";                                                                                                                   
         out.flush();                                                                                                                                      
         out.close();                                                                                                                                      
                                                                                                                                                           
         cout << "SMT2 file generation completed.\n";                                                                                                      
     }                                                                                                                                                     
 };                                                                                                                                                        
                                                                                                                                                           
 int main(int argc, char** argv) {                                                                                                                         
     if (argc != 3) {                                                                                                                                      
         cerr << "Usage: " << argv[0] << " <input.btor2> <output.smt2>" << endl;                                                                           
         return 1;                                                                                                                                         
     }                                                                                                                                                     
                                                                                                                                                           
     try {                                                                                                                                                 
         cout << "Starting BTOR2 to SMT2 conversion...\n";                                                                                                 
         auto total_start = chrono::steady_clock::now();                                                                                                   
                                                                                                                                                           
         BtorPreprocessor preprocessor;                                                                                                                    
         preprocessor.preprocess(argv[1], argv[2]);                                                                                                        
                                                                                                                                                           
         auto total_end = chrono::steady_clock::now();                                                                                                     
         auto total_duration = chrono::duration_cast<chrono::seconds>(total_end - total_start);                                                            
         cout << "Total conversion completed in " << total_duration.count() << " seconds.\n";                                                              
         return 0;                                                                                                                                         
     }                                                                                                                                                     
     catch (const exception& e) {                                                                                                                          
         cerr << "Error: " << e.what() << endl;                                                                                                            
         return 1;                                                                                                                                         
     }                                                                                                                                                     
 }                 