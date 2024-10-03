#### Authorship
 * Authors: Ethan Cheong (<echeong@andrew.cmu.edu>), Wu Meng Hui (<menghuiw@andrew.cmu.edu>)
---

#### TODOs after getting l4 working:
- Integrate MH structure changes into lab5_memory
    - Then fix unnecessary branch/jump statements.
    - Fix unnecessary movs when doing mem accesses also (the zero extend?)

    (- Change structure to allow for neededness and regalloc to work
        - to allow liveness and neededness to work on IF statements, change it so that 3AS assem contains IFs, but AS doesn't. Do neededness analysis on the 3AS. which contains ifs. Then do the conversion to gotos in instruction selection, which will in fact assign temps - so you need to change the temp count calculation in intcodegen. Then do regalloc.)

- Pre-l5 regalloc improvements: 
    - MCS Speed

- Optimizing Regalloc 

#### Notes for l5:
- You need to do neededness analysis multiple times for deadcode elim. Might be able to set it up so you can update the neededness info so you don't have to start from scractch. (But Jan says this might not be needed)
    - Note that l5 only grades on "real" programs, not pathological ones.
- What is an optimization pass?
    - Optional
    - Try to optimize for runtime, memory usage mainly in "almost all cases". But code size and energy use are general considerations (that we don't care about). 
- How to pick optimizations?
    - Compare your compiled code to godbolt, GCC. See what's diff and think what optimizations would get your code closer.
    - talk to TAs or other teams...
- ##### Regalloc optimisation
    TODO: Ask TAs about this.
    As of now, we 
    1) Construct interference graph
    2) Construct ordering using MCS
    3) Assign 13 colours to registers
    
    4) Spill if more colours are needed
    New step!
    5) Coalesce non-interfering moves between 3 and 4
  
    Idea: we are done with regalloc, but we aren't happy with assignments. Remove `move t <- s`, which we can do if `t` and `s` do not interfere.
     - If there is no interference, we can use the same register for both of them: then you can just remove that since it's a self-move.
     TODO: can you do this for our new movs (mov_sign_extend and mov_truncate?) PROBABLY NOT! ask winston.

    Greedy coalescing after coloring, before assigning registers and stack spilling
    - While you can:
        - Consider each mov t <- s
        - If there's an edge between the nodes in the intf graph, then skip
        - Otherwise, if there's a color c <= c_max that hasn't been used in neighbourhoods of t and s (note that this isn't necessarily the colour of t or s)
            - Create a new node u with color c in the colouring, create edges from u to all vertices in N(t) U N(s) 
            - remove t and s from the graph.
            - replace t and s with u in the program.
    The actual algorithm is more complicated. Look at the paper.

    It's HARD to efficiently implement this (because of the "while you can"). Jan says start with EXPENSIVE movs first, especially if you aren't in SSA form. Aka you do movs inside loops first. Then go for movs where both are numbers over 13, because those are expensive because they become stack to stack moves
    
    why not rename s to t? Its much easier to create bugs that way.

    - Note: This might make the interference graph get denser, which might require us to spill more temps. 

    some ideas for regalloc in general: if something is called i, maybe assign it to a register because it is a loop counter!

- ##### Splitting live ranges
    Dissatisfied with the interference graph (how do you know) this 
    without trying to colour it first? (maybe )
    We have a temp x that we use throughout the body of a function. We might want to introduce a move somewhere in the middle to rename x to x'. This increases the number of nodes in the interference graph so that the graph becomes more sparse, so we have to spill potentially less.
    
    Main idea: a single move instruction is a low price to pay since temp spilling would introduce a large number of memory moves.
    - Problem: No good and simple heuristics for our case for when we want to do this.
    - Idea: do one round of register allocation, see that you're unhappy because of spills. Then look at the graph and see whether we have too much interference, then find the possible temps for which we need to split the live range.

- ##### Peephole Optimizations
    Local optimizations that modify a few lines at a time.

    General notation:
    ```
    l:  ins0         l: ins'0
    ...        -->    ...
    l': insn         l': ins'n
    ```
    
    - Constant folding: replace binop with a constant if both of the operands are constants.
        ```
        l: x <- c1 @ c2 --> x <- c       where c = c1 @ c2 defined
                        --> raise(arith) otherwise
        ```
        - after this, you can do constant propagation and then deadcode elim. Can have big impact.
    - Optimizing conditionals
        ```
        l: if c1?c2 then l1 else l2 --> l: goto l1 where c1?c2
                                    --> l: goto l2 where !(c1?c2)
        ```
        - After this, a whole block could become deadcode. So run deadcode elim towards the end.  
    - Offset computation of records of records
        ```
        l1: x <- y + c1  --> l1: x <- y + c1
        l2: z <- x + c2      l2: z <- y + c    where c = c1+c2
        ```
        - Then eliminate first line with deadcode elim.
    - Strength reduction - replace complex instrutions with simpler one.
        ```
        a + 0 --> a
        a - 0 --> a
        a * 0 --> 0
        a * 1 --> a
        a * 2^n --> a << n
        a * b + a * c --> a * (b+c)
        ```
    To decide which ones to implement, compare code to the benchmark compiler.
    Try not to introduce bugs: note that x+1 is not necessarily greater than x, because we might have wrap-arounds.
    - Null sequences 
        Note: we have to be careful when choosing the optimizations that we do on final assem, because they may do things like setting flags which might mess up our cmps and tests.
        ```
        l : x <- x  --> l: nop
        ```
        This next one should be pretty close to the end, since it destroys basic block structure.
        ```
        l: goto l' --> l: nop
        l': ins    --> l':ins
        ```
        This last one should be done close to the end as well, since it tends to happen when we spill to the stack. Maybe after the codegen.
        ```
        l1: x <- y    -->  l1: x <-- y
        l2 : y <- x        l2: nop
        ```
        The last example arises if you have something like
        ```
        a <- a + x
        a <- a + y
        ```
        Say all of them get spilled to the stack:
        ```
        r10 <- a
        r10 <- x + r10
        a <- r10
        r10 <- a
        r10 <- y + r10
        a <- r10
        ```
- ##### Common Subexpression Elimination
    ```
    l: x <- s1 @ s2             l: x <- s1 @ s2
    ...                 -->     ...
    l': y <- s1 @ s1            l': y <- x
    ```
    Problems:
    - maybe s1 or s2 change in the middle, or x. BUT if we are in SSA form then these things can't happen.
    - Also, every pass in the code that leads to l' has to go through l. This might not be the case. (We say this is the case if l DOMINATES l', and write l > l').
    Example:
    ```
    lab1:
        x <- a + b // l1
        if a < 0 then lab2 else lab3
    lab2:
        y <- a + b
        goto lab4
    lab3:
        z <- x + b
        goto lab4
    lab4:
        u <- a + b // can we replace this? l4
        ...
    ```
    We can't replace it with y, since in some cases we don't define it.
    We can replace it with x, since l1 dominates l4. How do we determine if an instruction dominates another? Dominator graph.
   
- ##### Loop optimizations
    - Loop: back edge in CFG from k to h that dominates k. 
        - h is the header node.
    - optimize inner loops first
    - examples to try:
        - loop hoisting
            - only do this if the loop guard happens at least once.
        - unrolling
        - induction-variable elimination
        - Tiling/fusion/interchange

### Current regalloc params DO NOT DELETE
- _skip_mcs: 1
- _skip_regalloc_l1_l2: 2542 `simeonpoisson-randomizedlarge.l1`
- _skip_regalloc_l3: 5181 `voldemort-charity-burbage.l3`
- _skip_regalloc_per_function: _______ 


L4 TODOs:
- Add type fields to functions, ternary, and pointer, struct, array.
- TODO: Cmp (specifically equals) must be able to accomodate quads, because
we might want to check if two pointers are equal.
- Add destination to AST.
- Translation - convert env to a Map (Functional Data structure) so it aligns
  with heap memory.
- disallow moves from double to quad temps by mediating changes in data size
 ( for example, zeroextending the double). We can probably get around this
 by properly sizing all temps
 - Array lookup - check if null array at runtime, then shortcircuit

General notes
- Some phases have an `only-main` flag. This is used to skip certain parts of
  phases (e.g. doing passes to find the last line an arg appears) for the l1 and
  l2 test cases.
## Compiler Phases (Frontend)
For frontend phases, we first run all phases on the header files. Typechecking
ensures that header files only comprise typedefs and function declarations.

Then we run the same phases on the .c0 file.
### Parsing
- The original parse.ml file has not been changed
We implemented the grammar in `c0_lexer.mll` and `c0_parser.mly` as described
in the l3 handout.
- Postops are expanded into assignments.
- Asnops (`+=` or `/=`) are expanded into assignments. 
Note that we can't expand asnops in l4 (TODO).

### Elaboration
Elaboration takes in an AST program and returns an AST program, with the following
changes:
- For loops are expanded into while loops
- Removes intermediate statements (such as `Block`) that were parsed
- Elaborates on statements to more closely resemble assem code,

### Typechecking
`header_typecheck` takes in an elaborated AST program (of a header file) and 
produces a typechecking environment, which will be passed to `typecheck`. It 
throws a failure if the header is not well-typed.

`typecheck` takes in an elaborated AST program of the c0 file and the environment produced from `header_typecheck` and throws a failure if the header is not well-typed.

The typechecking environment contains the following:
- `gamma` (From l2)
- `delta` (From l2)
- `epsilon` (Delta from l3)
- `omega` (From l3)
- `used` - functions in used must be defined 
- `returns` - true if the function returns in every control path.

The core typechecking logic is contained within `syn_exp` and `chk_stm`. 
`syn_exp` works as described in the lecture notes; `chk_stm` throws a failure
if typechecking fails, and returns the environment in the conclusion of a 
typechecking rule if it succeeds.

TODO: Change failwith to error, so that span information is printed.

Finally, we add a `elaborate_decl` phase solely to elaborate declarations into
initialization and assignment to the new initialized variable.

## Translation (Middle End)
Translation (`trans.ml`) takes in an elaborated AST (represented as a list of statements) and returns a IR of the form Tree.program. 

Its goals are to:
1. Make control flow explicit with conditional and unconditional jumps
2. Make the evaluation order explicit in order to isolate effectful operations
3. Tag tail recursive functions

For L3, it assumes the AST has been fully elaborated except:
1. `Expr_stms` will be translated into expressions themselves.
2. Assignment operations are elaborated (will not be the case for L4)

To accomplish isolation of effectful operations, we distinguish between commands, which have side effects, and expressions, which are pure.

We use a mutable global doubly linked list to collect the list of commands that is output by translation. The translation helper functions `trans_exp`, `trans_boolean_exp` and `trans_stm` will all append commands to the doubly linked list. This is distinct from the lecture notes, where `trans_exp(e)` returns a tuple `(ins(e), res(e))` where `ins(e)` is a sequence of commands and res(e) is a pure expression. Note that each function definition is now "flattened"; in AST the body of function definitions were represented by right-leaning trees of statements, but now they are represented as lists.

The translation rules we use are exactly those in the lecture notes, including trans_boolean_exp (which is `cp(b,e1,e2)` in the lecture nodes). In addition, we add translation rules for while expressions and ternary expressions, which use cp, and rules for translating function calls.

We also have to add a rule for `cp(b,e1,e2)` for ternary expressions, since the result of a ternary expression can be a boolean expression.

In addition, in this stage we also remove unops by converting them to their equivalent binop. For example, `-x` is converted to `0 - x`, and `~x` is converted to `0xFFFFFFFF ^ x`.

In order to ensure consistency of temp numbers between states, we require that `Temp.create()` must have been called in `top.ml`.

TODO: Possible optimizations
1. Clear hashtables and pass it across functions
2. Clear DLL and pass it across functions

## Compiler Phases (Backend)

Intermediate Code generation -> Register Allocation -> Stack Spilling -> Instruction Selection

### Intermediate Code Generation
The intermediate code generation phase (`intcodegen`) takes in a list of a tuple of function signature and list of IR trees cmd and generates a list of (function signature , list of 3-address abstract assembly instructions) pairs. The output doesn't contain registers yet. 

Since temps are being assigned here, we assume that `Temp.create()` has already been called in top.ml, so that temp numbers persist through stages.

We generate a list of assembly instructions (using an accumulator to complete this in linear time). 
Instead of using maximal munch, we do not generate temps for consts or ints in order to reduce the 
number of unnecessary temps we create. This reduces the strain on our later compiler phases.

### Instruction Selection
After intermediate code generation, a new IR is generated where we convert 3-address abstract assembly to 2-address abstract assembly (`assem`). The code can now contain registers. Any instructions involving div/mod/sar/sal are also expanded out into binops with mov instructions to ensure that the operations are using registers/memory locations as necessary.

Each operand now has an associated size; they are all assumed to be doubles for L3.

It does the following:
1. Selection of instructions except mov (done after `regalloc`)
2. Call-clobbered arguments to functions are saved to the stack
3. Non-call-clobbered arguments have their corresponding register/stack offset inserted into the assembly 

`mov` instructions are not expanded, as we do not yet know what `t1 <- t2` will be replaced with before register allocation. 

"Call-clobbered arguments" are arguments in a function definition where their last reference in a function is after a call. They are called call-clobbered because we cannot assume that their register/stack offset (for example, edi for the first argument register) maintains its value throughout the entire function, due to the presence of nested function calls. Hence, we have to save them onto the stack.

"Non-call-clobbered arguments" are arguments where the last time they are used in a function precedes any nested function calls. Because the last time they are referenced in a function happens before (or at) the first function call, we can continue to use the argument registers / the stack offsets throughout the body of the function without fear of a function call overwriting them, and do not need to save them onto the stack.

Notice in the definition above we don't account for control flow. We don't want to have a full register allocation pass here. If the function body contains control flow, we simply say that all arguments are call-clobbered.

#### Conversion of instructions during instruction selection
Certain x86 instructions require that one of their operands is a register. As such, we make use of a scratch register %r10d.

1.  Add / Sub / Mul: converted directly to their x86 equivalent. 
    For example, `d = s1 - s2` is converted to

        movl s1, %r10d
        subl s2, %r10d
        movl %r10d, d

2.  Div / Mod: `d = r1 / r2` is converted to

        movl r1, %eax
        cltd
        idivl   r2
        movl    %eax, d

    while `d = r1 % r2` is converted to

        mov r1, %rax
        cltd
        idivl  r2
        movl  %edx, d

3. Sal / Sar `d = r1 @ r2` is converted to 

        movl rhs ecx % some test register
        test ecx ecx
        jl exn
        cmp 31 ecx
        jg exn
        movl lhs, %r10d
        sal ecx, %r10d
        movl %r10d, d
        jmp end
        exn: movl $0, r10d
        idivl r10d
        end:
    
    This checks if r2 < 0 or if r2 > 31. If so, divide by 0 to throw an arithmetic exception; otherwise, do the shift.

### Register Allocation
Register allocation takes in a list of abstract assembly funcs, and then does the following:
    liveness analysis -> build interference graph -> max cardinality search -> greedy graph colouring -> replace temps

It also takes in tuning parameters `_skip_regalloc_per_function` and `_skip_mcs` which allow us to skip either max cardinality search or the entire register allocation phase, depending on how many operands the input has. 
It also skips tail-recursive functions with 16 or fewer temps, since those will use the red zone instead of registers

#### Special registers
- `%r10d` -> We use this as a scratch register for translation of arithmetic operations and movs. Should not be allocated. 
- `%rsp` -> The stack pointer. Should not be allocated.

#### Liveness Analysis
Liveness analysis takes in a list of abstract assembly instruction and a mapping from function label to their arguments (constructed by `extract_args`) , and outputs a list of `Liveness.line`, which are then used in building the interference graph. 

Certain x86 instructions have to be treated carefully. Notably,
- Div and Mod are specified to use %eax and %edx, since they both use the idiv instruction.
- Sal and Sal use %ecx.

We maintain the following data structures, which are all currently hash tables:
- `pred_table`: maps a line to a set of all its predecessors.
- `jump_table`: maps a label to the line the label is on.
- `livein_table` / `liveout_table` / `uses_table` / `defs_table`: maps a line to its livein/liveout/uses/defs set.
- `movs_table`: maps a line to whether it contains a mov instruction

The current implementation of liveness uses Liveness by Variable, defined in the lecture notes.

#### Build interference graph
This takes in a list of `Liveness.line` (the output of Liveness Analysis) and returns a Hashtbl with keys being `Node.t` and values being a Set of `Node.t`. The Hashtbl is an adjacency list representation of the adjacency graph, and the graph is undirected, so both forward and backward edges are represented.

#### Max Cardinality Search
This takes in a Hashtbl representing the interference graph, and returns a simplicial elimination ordering of nodes using the algorithm specified in the lecture notes and recitation.

#### Greedy Colouring
This takes a Hashtbl representing the interference graph and a list of Nodes, and returns a Hashtbl with keys and values being `Node.t`, representing a mapping from input operands to regalloc to the register they are allocated to.

It requires that the list of Nodes contains all Nodes in the interference graph. If Max Cardinality Search is skipped, the compiler will provide the keys of the interference graph Hashtbl as the ordering (arbitrary ordering).

This is the set of registers that are available for allocation, in order of priority:

    `AX, DI, SI, DX, CX, R8, R9, R11, BX, BP, R12, R13, R14, R15`
    
Caller-saved registers are prioritized before callee-saved ones, to try and avoid functions having to save callee-saved registers.
Notably, `R10` is not there since we use it as a scratch register. The other registers are available for allocation. However, any register that's available as an operand in the input code must be coloured by itself first. In practice, we achieve this by taking the list of nodes that is input, and partitioning it into a list of registers and a list of other operands, and then joining the two resulting lists together (in linear time).

`Node.t` can be either `Entry` (which contains a register) or `Null` (which indicates that we didn't have enough registers to colour that node).

#### Replacing Temps
Finally, `replacetemps.ml` will take the original assembly, and the mapping produced by greedy colouring, and produce assembly with all temps replaced with the registers they have been allocated with.

### Stack Spilling
The stack spilling phase (`stackspill`):
1. Takes in a list of abstract assembly instructions with registers and temps, and outputs a list of abstract assembly instructions with registers and references to the stack. After this phase, there should be no more temps.
2. Translate function definitions and calls to follow calling convention

We spill temps by hashing them and storing the corresponding offset in a hash table.
If we use the red zone (for tail recursive functions with fewer than 128 bytes) then we do not modify the stack pointer. The red zone CANNOT be used if a function defn 
was regalloced; we use the `regalloc` field of the function header to indicate this.

Recall that we may have assigned some function arguments to the stack in `instrsel`. However, we only know the amount of space we need on the stack at the start of this phase (due to regalloc). We decrement the stack pointer by `stack_offset` after entering a function; hence, we also need to increment the offset of all existing references to the stack by the same amount.

This phase requires that:
1. Temps are not referenced before they are assigned to for the first time

Temps are assigned a position in the stack in the order that they are encountered in this phase, regardless of their initial numbering. For example, in the code below:

    t5 <- 3
    r11d <- 5 + t5
    r12d <- r11d * t5
    t2 <- r12d + t5
    ret

`t5` would be assigned stack offset -8, and `t2` would be assigned stack offset -16.
If we are using the red zone, then stack offsets are positive instead of negative.

### Code Generation
The code generation phase (codegen) outputs the final x86 assembly.

`mov` instructions are handled here and translated by using scratch register `r10d` if the src and dest are both memory locations, otherwise they are translated directly.

## TODOs (Spring Break)
- Add SSA conversion
- finish todos in code
