# EUF Theory Solver and Lazy SMT Solver

**Author:** ZHANG Boyuan  
**Course:** Tutorial 3 (Week 4) - DAI TD4  
**Topic:** Theory Solver for the Theory of Equality using Equality with Uninterpreted Functions (EUF)

## 📋 Overview

This project implements two solvers for the Theory of Equality:
1. **EUF Solver**: A decision procedure for conjunctions of equality literals using congruence closure
2. **Lazy SMT Solver**: An offline lazy SMT solver that combines boolean reasoning with the EUF solver

## 🛠️ Implementation Details

### 1. EUF Solver (`euf_solver`)

The EUF solver implements a decision procedure for formulas that are conjunctions of equality/inequality literals.

#### Implemented Functions/Components:

**`EGraph` Class:**
- **`__init__(terms)`**: Constructs a DAG from the set of terms
  - Implements depth-based sorting to ensure proper processing order (shallow terms before deep nested terms)
  - Creates nodes with proper argument tracking for function applications
  
- **`find(node_id)`**: Union-Find operation with path compression
  - Returns the representative of an equivalence class
  
- **`union(id1, id2)`**: Merges two equivalence classes
  - Makes `id2` the representative of the merged class
  
- **`congruent(id1, id2)`**: Checks if two nodes are congruent
  - Returns `True` if they have the same function symbol and their arguments are in the same equivalence classes
  
- **`merge(id1, id2)`**: Merges congruence classes recursively
  - Implements the congruence closure algorithm
  - Recursively merges parents that become congruent
  
- **`merge_equalities(equalities)`**: Processes a list of equalities
  - Merges all equalities to compute the congruence closure
  
- **`check_consistency(inequalities)`**: Verifies consistency
  - Returns `False` if any inequality's terms end up in the same equivalence class
  - Returns `True` if all inequalities are consistent

**`euf_solver(formula)` Function:**
- **Input**: A conjunction of equality/inequality literals
- **Output**: `True` if satisfiable, `False` if unsatisfiable
- **Algorithm**:
  1. Extract all terms from the formula
  2. Split into equalities and inequalities
  3. Build the E-graph
  4. Compute congruence closure by merging equalities
  5. Check if inequalities create conflicts

#### Key Bug Fix:
Fixed the term sorting algorithm to use actual depth calculation instead of binary classification. This ensures that `f(a,b)` is processed before `f(f(a,b),b)`, which is critical for proper argument tracking in the graph.

### 2. Lazy SMT Solver (`lazy_smt_solver`)

The lazy SMT solver extends the EUF solver to handle arbitrary boolean combinations of equality atoms.

#### Implemented Functions:

**`lazy_smt_solver(formula)` Function:**
- **Input**: A PySMT formula with boolean connectives and equality atoms
- **Output**: `True` if satisfiable, `False` if unsatisfiable
- **Algorithm**:
  1. **Boolean Abstraction**: Create a mapping from equality atoms to fresh boolean variables
  2. **SAT Enumeration**: Use a SAT solver to enumerate boolean models
  3. **Theory Checking**: For each boolean model:
     - Convert the assignment back to theory literals
     - Call `euf_solver()` to check theory consistency
     - If consistent: return SAT
     - If inconsistent: block this model and continue
  4. **Exhaustion**: If all models are checked and none are satisfiable, return UNSAT

## 🧪 Testing

### Running the EUF Solver Tests

The project includes 10 test cases in the `test_cases/` directory (t0.smt2 through t9.smt2).

```bash
# Run all test cases with the EUF solver
python test_solver.py

# Run a specific test case
python test_solver.py --test_case t1.smt2
```

**Expected Output:**
```
Runing test cases:
[SUCCESS] t0.smt2: returned Satisfiable
[SUCCESS] t1.smt2: returned Unsatisfiable
[SUCCESS] t2.smt2: returned Unsatisfiable
[SUCCESS] t3.smt2: returned Satisfiable
[SUCCESS] t4.smt2: returned Unsatisfiable
[SUCCESS] t5.smt2: returned Unsatisfiable
[SUCCESS] t6.smt2: returned Satisfiable
[SUCCESS] t7.smt2: returned Unsatisfiable
[SUCCESS] t8.smt2: returned Unsatisfiable
[SUCCESS] t9.smt2: returned Unsatisfiable
```

**Result:** ✅ **All 10 tests pass** (10/10)

### Running the Lazy SMT Solver Tests

```bash
# Run the lazy SMT solver on the same test cases
python test_lazy_smt.py
```

**Expected Output:**
```
Testing Lazy SMT Solver on all test cases:
============================================================
[SUCCESS] t0.smt2: Satisfiable
[SUCCESS] t1.smt2: Unsatisfiable
[SUCCESS] t2.smt2: Unsatisfiable
[SUCCESS] t3.smt2: Satisfiable
[SUCCESS] t4.smt2: Unsatisfiable
[SUCCESS] t5.smt2: Unsatisfiable
[SUCCESS] t6.smt2: Satisfiable
[SUCCESS] t7.smt2: Unsatisfiable
[SUCCESS] t8.smt2: Unsatisfiable
[SUCCESS] t9.smt2: Unsatisfiable
============================================================
All tests passed!
```

**Result:** ✅ **All 10 tests pass** (10/10)

### Running Demo Examples

```bash
# Run the demo examples in main()
python euf.py
```

**Expected Output:**
```
Test 1: a = b
EUF Solver: True
Lazy SMT Solver: True

Test 2: a = b AND a != b
EUF Solver: False
Lazy SMT Solver: False

Test 3: (a = b) OR (b = c)
Lazy SMT Solver: True

Test 4: ((a = b) OR (b = c)) AND (a != c)
Lazy SMT Solver: True
```

## 📦 Prerequisites

### Installation

1. **Python 3**: Ensure Python 3 is installed

2. **Install PySMT**:
```bash
pip install pysmt
```

3. **Install Z3 solver**:
```bash
pysmt-install --z3
```

4. **Verify installation**:
```bash
pysmt-install --check
```

You should see Z3 listed as installed.

## 📂 Project Structure

```
.
├── euf.py              # Main implementation file (SUBMIT THIS)
├── utils.py            # Utility functions (provided)
├── test_solver.py      # Test script for EUF solver (provided)
├── test_lazy_smt.py    # Test script for lazy SMT solver (created for testing)
├── test_cases/         # SMT-LIB test cases (provided)
│   ├── t0.smt2
│   ├── t1.smt2
│   └── ...
└── README.md           # This file
```

## 🐛 Debug Files

The following debug files were created during development and are **not required** for submission:
- `debug_test.py`
- `debug_t1.py`
- `debug_detailed.py`
- `test_lazy_smt.py`

These files are in `.gitignore` and will not be pushed to the repository.

## 🔧 Python Cache Files (.pyc)

### What are .pyc files?

`.pyc` files are **Python bytecode compiled files**. When you run a Python script, Python automatically compiles your `.py` source code into bytecode and stores it in these `.pyc` files for faster execution next time.

They appear in the `__pycache__/` directory with names like:
- `euf.cpython-313.pyc`
- `utils.cpython-313.pyc`

The `cpython-313` indicates they were compiled with CPython version 3.13.

### Why do they appear in the untracked list?

When you run `git status`, you'll see:
```
Untracked files:
    __pycache__/
```

These are **not source code** and should **not be committed** to version control because:
- They are automatically regenerated when you run Python
- They are platform/version specific
- They make the repository messy

### How to handle .pyc files?

**Solution:** Add them to `.gitignore`

Create or update `.gitignore` in your project root:

```bash
# Python cache files
__pycache__/
*.pyc
*.pyo
*.pyd
.Python

# Debug files (optional)
debug_*.py
test_lazy_smt.py
```

After creating `.gitignore`, run:
```bash
git add .gitignore
git commit -m "Add .gitignore for Python cache files"
```

## 📤 Submission

### For Moodle Submission:
- **Submit only:** `euf.py`
- **Deadline:** Monday February 9th at 23:59

### For GitHub:
```bash
# Add .gitignore first
git add .gitignore

# Add the main implementation file
git add euf.py

# Add README
git add README.md

# Commit with a meaningful message
git commit -m "Complete EUF and lazy SMT solver implementation with documentation"

# Push to GitHub
git push origin master
```

## ✅ Verification Checklist

- [x] EUF solver implemented with congruence closure
- [x] All 10 test cases pass for EUF solver (10/10)
- [x] Lazy SMT solver implemented with boolean abstraction
- [x] All 10 test cases pass for lazy SMT solver (10/10)
- [x] Code properly documented with comments
- [x] Author name added to file header
- [x] README created with complete instructions
- [x] `.gitignore` configured to exclude cache files

## 📚 Key Algorithms Implemented

### Congruence Closure Algorithm
The EUF solver implements the classic congruence closure algorithm:
1. Build an E-graph (expression graph) from all terms
2. Initialize each term to its own equivalence class
3. Merge equivalence classes based on given equalities
4. Propagate congruences: if `f(a) ≡ f(b)`, then when `a ≡ b` is asserted, merge `f(a)` and `f(b)`
5. Check for conflicts with inequalities

### Lazy SMT (DPLL(T)) Algorithm
The lazy SMT solver implements an offline version of DPLL(T):
1. Abstract theory atoms to boolean variables
2. Use SAT solver to find boolean assignments
3. For each assignment, check theory consistency
4. If inconsistent, learn a blocking clause and continue
5. If consistent, return SAT; if all assignments exhausted, return UNSAT

## 🎓 Learning Outcomes

Through this tutorial, I learned:
- How to implement union-find data structures with path compression
- The congruence closure algorithm for equality reasoning
- How to integrate SAT and theory solvers in a lazy SMT architecture
- The importance of proper term ordering in graph construction
- How to use PySMT library for SMT formula manipulation
