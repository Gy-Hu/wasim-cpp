# Debugging Notes for smt-switch Compilation Issues

## Initial Problem
Compilation errors in smt-switch when building with Bitwuzla backend, specifically undefined references to string conversion functions and invalid symbol table entries.

## Attempted Solutions

### Attempt 1: Modifying Link Order
- **Hypothesis**: The issue was related to link order, with solver backends needing smt-switch core library symbols.
- **Action**: Modified `bitwuzla/CMakeLists.txt` to change link order and include smt-switch core library first.
- **Result**: Failed. Still got undefined references to `smt::to_string(smt::SortKind)` and other symbols.
- **Lesson**: Link order wasn't the primary issue.

### Attempt 2: Using --start-group Linker Option
- **Hypothesis**: There might be circular dependencies that could be resolved with `--start-group`.
- **Action**: Added `LDFLAGS="-Wl,--start-group"` to the build command.
- **Result**: Failed. Got new errors about invalid string offsets in `.strtab` section.
- **Lesson**: The problem was deeper than just symbol resolution order.

### Attempt 3: Modifying Static Library Repacking
- **Hypothesis**: The static library repacking process was corrupting symbol tables.
- **Action**: Changed `ar -qc` to `ar -rcs` in both Bitwuzla and Boolector CMake files.
- **Result**: Failed. Still seeing symbol table corruption.
- **Lesson**: While this was a step in the right direction for proper symbol table handling, it didn't address the root cause.

## Key Insights

1. **Multiple Issues**: We're dealing with at least two distinct problems:
   - Symbol resolution for string conversion functions
   - Symbol table corruption in static libraries

2. **Static Library Complexity**: The project's approach of repacking static libraries introduces complexity:
   - Merging multiple static libraries
   - Maintaining symbol tables
   - Handling dependencies between components

3. **Build System Structure**: The current build system has several layers:
   - Core smt-switch library
   - Solver backend libraries
   - Static library repacking
   - Test linking

## Next Steps to Consider

1. **Investigate Build Order**:
   - Ensure smt-switch core library is fully built before backends
   - Verify symbol visibility in core library

2. **Static Library Analysis**:
   - Examine symbol tables in intermediate static libraries
   - Check for compatibility between different compiler/linker versions

3. **Alternative Approaches**:
   - Consider using shared libraries for development
   - Explore modern CMake features for better dependency management
   - Look into whether static library repacking is necessary

## Lessons Learned

1. **Debug Incrementally**: Each attempt should focus on one aspect of the problem.
2. **Read Error Messages Carefully**: The shift from undefined references to symbol table corruption was significant.
3. **Understand Build System**: Need deeper understanding of how CMake, static libraries, and linking work together.
4. **Documentation**: Keep track of attempts and failures to avoid repeating unsuccessful approaches.

## New Analysis (After Code Review)

### Comparison with Boolector Implementation

1. **Class Design Differences**:
   - **Boolector**:
     * Uses BoolectorSortBase as base class with concrete subclasses
     * Each subclass (BoolectorBVSort, BoolectorArraySort, BoolectorUFSort) handles specific sort types
     * Base class provides default implementations for all virtual functions
     * Clean separation of concerns and type-specific logic
   
   - **Bitwuzla**:
     * Single BzlaSort class directly inheriting from AbsSort
     * No specialized classes for different sort types
     * Missing implementations of some virtual functions
     * Less structured approach to type-specific behavior

2. **Virtual Function Implementation**:
   - **Boolector**: All virtual functions are accounted for, either with proper implementations or appropriate error messages
   - **Bitwuzla**: Missing crucial virtual function implementations, particularly to_string()

### Potential Solutions

1. **Complete Refactor Approach**:
   - Create BzlaSortBase as new base class
   - Implement specialized sort classes (BzlaBVSort, BzlaArraySort, etc.)
   - Mirror Boolector's successful design pattern
   - Pros:
     * Cleaner, more maintainable code
     * Better type safety and error handling
     * Follows proven design pattern
   - Cons:
     * Significant code changes required
     * Higher risk of introducing new bugs
     * More time-consuming

2. **Minimal Fix Approach**:
   - Add missing virtual function implementations to BzlaSort
   - Keep current single-class design
   - Pros:
     * Faster to implement
     * Minimal code changes
     * Lower risk of new issues
   - Cons:
     * Misses opportunity to improve design
     * May be harder to maintain long-term
     * Doesn't address structural issues

### Additional Considerations

1. **Symbol Table Issues**:
   - Both approaches need to ensure proper symbol visibility
   - May still need to address static library repacking
   - Consider impact on build system complexity

2. **Testing Impact**:
   - Complete refactor requires more extensive testing
   - Minimal fix might be easier to verify
   - Need to consider test coverage for virtual functions

3. **Future Maintenance**:
   - Consider which approach better serves future development
   - Think about impact on other backends
   - Consider contribution guidelines and project standards

## 检索记录和发现 (2024-01-09)

1. 检查了 btor 的实现：
   - `deps/smt-switch/btor/include/boolector_sort.h`
   - `deps/smt-switch/btor/src/boolector_sort.cpp`
   - 发现 btor 实现了完整的类层次结构，包括 `BoolectorSortBase` 和其派生类

2. 检查了 AbsSort 的定义：
   - `deps/smt-switch/include/sort.h`
   - 定义了必须实现的虚函数，包括 `to_string()`

3. 检查了 Bitwuzla 的实现：
   - `deps/smt-switch/bitwuzla/include/bitwuzla_sort.h`
   - `deps/smt-switch/bitwuzla/src/bitwuzla_sort.cpp`
   - 已经实现了所有必要的 `to_string()` 方法

4. 检查了 Term 相关实现：
   - `deps/smt-switch/include/term.h` (AbsTerm 的定义)
   - `deps/smt-switch/bitwuzla/include/bitwuzla_term.h`
   - `deps/smt-switch/bitwuzla/src/bitwuzla_term.cpp`
   - 发现 `BzlaTerm::to_string()` 依赖于 `to_string_formatted("smt2")`

5. 检查了 Op 的定义：
   - `deps/smt-switch/include/ops.h`
   - 定义了 `Op` 结构体和其 `to_string()` 方法

关键发现：
1. Bitwuzla 后端已经实现了所有必要的 `to_string()` 方法
2. 链接错误可能不是由于缺少方法实现导致的
3. 问题可能出在：
   - 静态库重打包过程中的符号丢失
   - 链接顺序问题
   - 符号可见性问题

下一步建议：
1. 检查 CMake 构建系统中的库打包和链接过程
2. 验证符号的可见性设置
3. 尝试使用 `nm` 或类似工具检查静态库中的符号
4. 考虑使用动态链接进行测试，以验证是否是静态链接特有的问题