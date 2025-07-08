# Difny-VCG

A verification-condition (VC) generator for a simple imperative language called Difny, which is a blend of Dafny and IMP.

## Overview

Difny-VCG is a program verifier that automatically proves the correctness of programs written in the Difny language. It uses formal verification techniques to ensure that programs satisfy their specifications before execution, catching potential bugs at compile time.

## What is Difny?

Difny is a simple imperative programming language that combines the verification-friendly features of Dafny with the simplicity of IMP (Imperative Language). It supports:

- **Basic Types**: Integers and arrays
- **Control Structures**: Conditionals, loops with invariants
- **Verification Annotations**: Preconditions (`requires`), postconditions (`ensures`), assertions (`assert`), and assumptions (`assume`)
- **Methods**: Function definitions with contracts
- **Array Operations**: Multi-dimensional array access and manipulation

## Architecture

The verifier follows a five-step pipeline:

```
Difny source program
    ↓ (parse)
Abstract Syntax Tree (AST)
    ↓ (compile)
Guarded Command Language (GCL)
    ↓ (wp)
Verification Conditions (VC)
    ↓ (encode)
SMT constraints
    ↓ (solve)
Verification Result
```

### Key Components

1. **Parser** (`lexer.mll`, `menhir_parser.mly`): Converts Difny source code into an abstract syntax tree
2. **Compiler** (`verify.ml`): Translates Difny AST into guarded command language (GCL)
3. **Weakest Precondition** (`verify.ml`): Computes verification conditions using weakest precondition calculus
4. **SMT Encoding** (`smt.ml`): Converts verification conditions into SMT-LIB format for Z3 solver
5. **Solver Integration**: Uses Z3 SMT solver to check validity of verification conditions

## Features

### Level 1: Basic IMP Language
- Integer arithmetic and boolean expressions
- Assignment, conditional, and loop statements
- Loop invariants for verification
- Assertions and assumptions

### Level 2: Array Support
- Multi-dimensional array operations
- Array read/write operations
- Array bounds checking through preconditions

### Level 3: Method Verification
- Method definitions with contracts
- Preconditions and postconditions
- Method calls and recursion
- Mutual recursion support

## Language Syntax

### Types
```ocaml
TYPE := "int" | "array" "<" TYPE ">"
```

### Arithmetic Expressions
```ocaml
AEXP := n              (* integer constant *)
      | PATH           (* memory read *)
      | "-" AEXP       (* unary minus *)
      | AEXP "+" AEXP  (* addition *)
      | AEXP "-" AEXP  (* subtraction *)
      | AEXP "*" AEXP  (* multiplication *)
      | AEXP "%" AEXP  (* modulo *)
      | "(" AEXP ")"   (* parentheses *)
```

### Boolean Expressions
```ocaml
BEXP := "true" | "false"
      | AEXP "==" AEXP (* equality *)
      | AEXP "!=" AEXP (* inequality *)
      | AEXP "<" AEXP  (* less than *)
      | AEXP "<=" AEXP (* less than or equal *)
      | AEXP ">" AEXP  (* greater than *)
      | AEXP ">=" AEXP (* greater than or equal *)
      | "!" BEXP       (* negation *)
      | BEXP "&&" BEXP (* conjunction *)
      | BEXP "||" BEXP (* disjunction *)
```

### Statements
```ocaml
STMT := PATH ":=" AEXP ";"           (* assignment *)
      | "if" BEXP "{" BLOCK "}" "else" "{" BLOCK "}"
      | "while" BEXP INVARIANT* "{" BLOCK "}"
      | "assert" FORMULA ";"         (* assertion *)
      | "assume" FORMULA ";"         (* assumption *)
      | id ":=" "*" ";"              (* havoc *)
      | id ":=" id "(" ARGS ")" ";"  (* method call *)
```

### Methods
```ocaml
METHOD := "method" id "(" PARAMS ")" 
          "returns" "(" id ":" TYPE ")"
          REQUIRES*
          ENSURES*
          "{" LOCAL* BLOCK "return" AEXP ";" "}"
```

## Example Programs

### Simple Loop with Invariant
```ocaml
method sum(n: int) returns (result: int)
requires n >= 0;
ensures result == n * (n + 1) / 2;
{
    var i: int;
    var s: int;
    i := 0;
    s := 0;
    while i <= n
        invariant s == i * (i - 1) / 2;
        invariant i <= n + 1;
    {
        s := s + i;
        i := i + 1;
    }
    return s;
}
```

### Array Manipulation
```ocaml
method reverse(a: array<int>, n: int) returns (b: array<int>)
requires n >= 0;
ensures forall i :: 0 <= i < n ==> b[i] == a[n - 1 - i];
{
    var i: int;
    b := a;
    i := 0;
    while i < n / 2
        invariant 0 <= i <= n / 2;
        invariant forall j :: 0 <= j < i ==> b[j] == a[n - 1 - j];
        invariant forall j :: i <= j < n - i ==> b[j] == a[j];
        invariant forall j :: n - i <= j < n ==> b[j] == a[n - 1 - j];
    {
        var temp: int;
        temp := b[i];
        b[i] := b[n - 1 - i];
        b[n - 1 - i] := temp;
        i := i + 1;
    }
    return b;
}
```

## Installation and Usage

### Prerequisites
- OCaml (with opam and dune)
- Z3 SMT solver (version 4.13.0 or later)
- Dafny (optional, for comparison testing)

### Building
```bash
# Install dependencies
opam install . --deps-only -y

# Build the project
dune build

# Install the executable
make install
```

### Running the Verifier
```bash
# Verify a Difny program
difny verify <file>

# Run with debug output
difny verify <file> -v debug

# Run tests
dune runtest
```

### Command Line Options
```bash
difny --help           # Show all commands
difny verify --help    # Show verification options
```

## Verification Results

The verifier outputs one of three results for each method:

- **`<method_name>: verified`** - The method satisfies its specification
- **`<method_name>: not verified`** - A counterexample is provided showing why verification failed
- **`<method_name>: unknown`** - The verifier cannot determine correctness (timeout or complexity)

## Technical Details

### Verification Condition Generation
The verifier uses weakest precondition calculus to generate verification conditions. For a method with precondition `P`, body `S`, and postcondition `Q`, it computes:

```
VC = P ==> wp(S, Q)
```

### SMT Encoding
Verification conditions are encoded into SMT-LIB format and sent to the Z3 solver. The encoding handles:
- Integer arithmetic and comparisons
- Boolean logic and quantifiers
- Array theory (select/store operations)
- Method contracts and recursion

### Array Theory
Arrays are modeled functionally using:
- `select(a, i)` - Read value at index `i` in array `a`
- `store(a, i, v)` - Create new array with value `v` at index `i`

## Project Structure

```
Difny-VCG/
├── lib/                    # Core implementation
│   ├── lang.ml            # Language definitions and AST
│   ├── lexer.mll          # Lexical analyzer
│   ├── menhir_parser.mly  # Parser
│   ├── desugar.ml         # AST desugaring
│   ├── verify.ml          # Main verification logic
│   ├── smt.ml             # SMT encoding
│   └── pretty.ml          # Pretty printing
├── bin/                   # Executable entry point
├── test/                  # Test cases and benchmarks
└── dune-project           # Build configuration
```

## Contributing

This project is part of a formal verification course. The implementation focuses on demonstrating core concepts in program verification:

- Weakest precondition calculus
- Guarded command language
- SMT solving integration
- Loop invariant reasoning
- Method contract verification

## License

This project is developed for educational purposes as part of a formal verification course.
