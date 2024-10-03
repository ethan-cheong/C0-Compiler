#### Authorship
 * Authors: Ethan Cheong (<echeong@andrew.cmu.edu>), Wu Meng Hui (<menghuiw@andrew.cmu.edu>)
---

## Data structures
- TODO: Fill this up before checkin

## Special registers
- %r10d -> We use this as a scratch register for arithmetic operations. Should not be allocated (??)
- %rsp -> The stack pointer. Should not be allocated.
- %rbp -> For stack pointing. SHOULD be allocated.
    - possibility: rbp points to the start of the current frame. But not necessary, since we can just use math to calculate the rsp offset (frame size) manually.
- %edx -> idiv and mod.
- %ecx -> sal and sar.

## TODOs (Lab 3)
- Get rid of the prologue/epilogue. 
- Migrate Epilogue to instr_sel.
    - This will require adding word size to Assem
- Register allocation
    - Start with caller saved registers, then do the callee saved ones.
- Semantic analysis
    - Make sure that functions have right # of arguments
    - Make sure that arguments have the right types
- Codegen of functions:
    - TODO: goto office hours and ask how they plan to do it.
- Translation to IR trees
    - Function calls should be commands since they have side effects - similar idea to division. 
- Extend Assem
    - You could add new inst d <- call f. 
- Add liveness analysis for functions
    - Using call f.
- instruction selection for function calls - for call f
    - Caller saved: In regalloc, say that def(l,r) if l: call f and caller-save(r)
    - Callee saved 
        Solution 1: Store callee saved regs on the stack, and restore at return. 
            - optimisation: only store the ones that are used
            - We should probably try this first
        Solution 2: If reg alloc is good, store all callee saved registers in temps.
            - then let the register allocator deal with it. (This works if it is good.) 
            - might not be the best.
    - When you move the stack pointer, you always want to move it it by 8+ 0mod16. So 8, 24, 40, 56, ...
    - Count the number of temps you use in the function call. for registers.
        - First pass - maybe save all of the 6 registers on the stack. Add 6*8 to every frame size.
        - Jan's recommendation:
    - For optimisation later red zone - for a leaf function, you don't have to move ths stack pointer. There's 128 bytes below the stack pointer where the OS just doesn't touch it, so if you need less than 128 bytes for a leaf function, you don't need to decrement the stack pointer.

Recall Division
---------------
Assem: 
    l : d <- s1 / s2
    what doesn't work well is to require S1 = eax in reg alloc.
    Instead, we want to keep live ranges of pre-coloured temps short. Do this by defining division to be:

    eax <- s1
    edx <- signextend(eax)
    eax <- eax / s2
    d <- eax.

    In this case, division uses eax and edx.


## Compiler Phases (Frontend)

### Elaboration
- Removes syntactic sugar (e.g., for loops)
- Removes intermediate statements that were parsed
- Elaborates on statements to more closely resemble assem code,
e.g., split up a declaration into an initialization and an assignment

### Typechecking
- Takes in the elaborated AST and checks the types for the AST
- A statement is well-typed if it is judged as well-typed
- An expression is well-typed if the variables are typed according to Gamma
- Typechecking analyses each sequence to ensure there are:
    - Only well-typed expressions adhering to the requirements of the expressions
    - Statements are well-typed
- Once a variable leaves the scope of a definition (represented by a branch in the tree and moving to the next branch),
    - The variable is removed from delta
    - The variable is no longer in scope
    - If the same variable is then re-defined, it will not hbe initalised with the same values

### Translation
Translation (`trans.ml`) takes in an elaborated AST (represented as a statement) and returns a IR of the form Tree.program. 

Its goals are to:
1. Make control flow explicit with conditional and unconditional jumps
2. Make the evaluation order explicit in order to isolate effectful operations

It assumes that the elaborated AST has been fully elaborated:
1. There are no more asops e.g. +=, -= 
2. For expressions have been elaborated into while expressions
3. int x = 0 (declare with init expressions) have been elaborated into 
a sequence of declare + assign expressions
4. There are no more Declare_intermediate statements 
of the form decl * tau * mstm list; these have been elaborated into 
sequences
5. Expr_stms are included in case they cause a runtime exception
6. There are no Blocks; these have been elaborated into chains of sequences
    Block [a; b; c] -> seq(a, seq(b, seq(c, nop)))

It also assumes that typechecking has passed on the AST.

To accomplish isolation of effectful operations, we distinguish between commands, which have side effects, and expressions, which are pure.

We use a mutable global doubly linked list to collect the list of commands that is output by translation. The translation helper functions trans_exp, trans_boolean_exp and trans_stm will all append commands to the doubly linked list. This is distinct from the lecture notes, where trans_exp(e)returns a tuple (ins(e), res(e)) where ins(e) is a sequence of commands and res(e) is a pure expression.

The translation rules we use are exactly those in the lecture notes, including trans_boolean_exp (which is cp(b,e1,e2) in the lecture nodes). In addition, we add translation rules for while expressions using cp:
    tr(while(b, s)) = 
    goto cmp;
    l1: tr(s);
    cmp: cp(b, l1, l2);
    l2:  

and for ternary expressions:
    tr(c ? e1 : e2) = 
    cp(c, l1, l2);
    l1: ins(e1);
    t <- res(e1);
    goto l3;
    l2: ins(e2);
    t <- res(e2);
    l3;

We also have to add a rule for cp(b,e1,e2) for ternary expressions, since the result of a ternary expression can be a boolean expression. 
(e.g. x<1 ? true: false;)
    cp((c?t1:t2), e1, e2) =
    res(c?t1:t2)
    t <- ins(c?t1:t2);
    if (t = true,e1,e2);

In addition, in this stage we also remove unops by converting them to their equivalent binop. For example, -x is converted to 0 - x, and ~x is converted to 0xFFFFFFFF ^ x.

In order to ensure consistency of temp numbers between states, we require that Temp.create() must have been called in top.ml.

        
## Compiler Phases (Backend)

Intermediate Code generation -> Register Allocation -> Stack Spilling -> Instruction Selection

### Intermediate Code Generation
The intermediate code generation phase (intcodegen) takes in an IR tree (which at this stage, is a list of Tree.cmd, each element of which is a tree...) and generates a list of 3-address abstract assembly instructions. We assume that the input is exactly the output of translation. 

Since temps are being assigned here, we assume that Temp.create () has already been called in top.ml, so that temp numbers persist through stages.

We use maximal munch on each Tree.cmd tree to generate a list of assembly instructions (using a accumulator to complete this in linear time), and then concat the products together to get a single list.

### Instruction Selection
After intermediate code generation, a new IR is generated where we convert 3-address abstract assembly to 2-address abstract assembly (assem). Any instructions involving div/mod/sar/sal are also expanded out into binops with mov instructions to ensure that the operations are using registers/memory locations as necessary.

It requires that 
1. The program represented by the input list is well-formed

It does the following:
1. Conversion of instructions except mov
2. Adds a prologue:

    pushq %rbp  
    movq  $rsp, %rbp

and an epilogue:
    
    popq %rbp
    ret

to all instruction lists.

The exception is that `mov` instructions are not expanded, as there is a mov of `t1 <- t2` which is spilled to stack. 

#### Conversion of instructions during instruction selection
Certain x86 instructions require that one of their operands is a register. As such, we make use of a scratch register %r10d.

1.  Add / Sub / Mul: converted directly to their x86 equivalent. 
    For example, `d = s1 - s2` is converted to

    movl s1, %r10
    subl s2, %r10
    movl %r10, d

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
        movl lhs, %r10
        sal ecx, %r10
        movl %r10, d
        jmp end
        exn: movl $0, r10d
        idivl r10d
        end:
    
    This checks if r2 < 0 or if r2 > 31. If so, divide by 0 to throw an arithmetic exception; otherwise, do the shift.

### Register Allocation
Register allocation takes in a list of abstract assembly instructions, and then does the following:
    liveness analysis -> build interference graph -> max cardinality search -> greedy graph colouring -> replace temps

Liveness analysis also outputs the number of distinct assembly operands. This allows us to skip either max cardinality search or the entire register allocation phase, depending on how many operands the input has. The thresholds for skipping are controlled by `_skip_mcs` and `_skip_colouring` in `top.ml`.

#### Liveness Analysis
Liveness analysis takes in a list of abstract assembly instruction, and outputs a list of Liveness.line, which are then used in building the interference graph. It also outputs an int which contains the number of operands in the file. We use this to "short-circuit" register allocation for pathalogical test cases.

Certain x86 instructions have to be treated carefully. Notably,
- Div and Mod are specified to use %eax and %edx, since they both use the idiv instruction.
- Sal and Sal use %ecx.
- Constructs liveness by variable. Traverses the control flow graph to update the liveness information

#### Build interference graph
This takes in a list of Liveness.line (the output of Liveness Analysis) and returns a Hashtbl with keys being Node.t and values being a Set of Node.t. The Hashtbl is an adjacency list representation of the adjacency graph, and the graph is undirected, so both forward and backward edges are represented.

#### Max Cardinality Search
This takes in a Hashtbl representing the interference graph, and returns a simplicial elimination ordering of nodes using the algorithm specified in the lecture notes and recitation.

#### Greedy Colouring
This takes a Hashtbl representing the interference graph and a list of Nodes, and returns a Hashtbl with keys and values being Node.t, representing a mapping from input operands to regalloc to the register they are allocated to.

It requires that the list of Nodes contains all Nodes in the interference graph. If Max Cardinality Search is skipped, the compiler will provide the keys of the interference graph Hashtbl as the ordering (arbitrary ordering).

This is the set of registers that are available for allocation:
    [ EAX; EBX; ECX; EDX; ESI; EDI; R8D; R9D; R11D; R12D; R13D; R14D; R15D ]
Notably, R10D is not there since we use it as a scratch register, and the stack pointer and frame pointer are not there as well.
The other registers are available for allocation. However, any register that's available as an operand in the input code must be coloured by itself first. In practice, we achieve this by taking the list of nodes that is input, and partitioning it into a list of registers and a list of other operands, and then joining the two resulting lists together (in linear time).

Node.t can be either Entry (which contains a register) or Null (which indicates that we didn't have enough registers to colour that node).

#### Replacing Temps
Finally, replacetemps.ml will take the original assembly instr list, and the Hashtbl produced by greedy colouring, and produce a new assembly instr list with all temps replaced with the registers they have been allocated with.

### Stack Spilling
The stack spilling phase (stackspill) takes in a list of abstract assembly instructions with registers and temps, and outputs a list of abstract assembly instructions with registers and references to the stack. After this phase, there should be no more temps.

This phase requires that:
1. Temps are not referenced before they are assigned to for the first time

Temps are assigned a position in the stack in the order that they are encountered in this phase, regardless of their initial numbering. For example, in the code below:

    t5 <- 3
    r11d <- 5 + t5
    r12d <- r11d * t5
    t2 <- r12d + t5
    ret

t5 would be assigned stack offset -4, and t2 would be assigned stack offset -8.

We spill temps by hashing them and storing the corresponding offset in a hash table. The hash table is initialized with size 500 and is allowed to grow.

### Code Generation
The code generation phase (codegen) takes in a list of abstract assembly instructions with registers and stack references, and returns a list of finalassem instructions, which resemble x86 instructions.

 `mov` instructions are handled here and translated by using scratch register `r10d` if the src and dest are both memory locations, otherwise they are translated directly.



## Tips from Lectures and TAs
- Talk to TAs about compiler design decisions
    - Ask them what options we have for IR beyond just lists.
- Set up local testing - done.
- Make sure you pass all test cases in first 3 labs
- Start working on reg alloc from Friday onwards
- Use comments and documentation
- testing - use --prune flag with keep.txt in relevant test folder.