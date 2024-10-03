#### Authorship
 * Authors: Ethan Cheong (<echeong@andrew.cmu.edu>), Wu Meng Hui (<menghuiw@andrew.cmu.edu>)
---

## Special registers
- %r10d -> We use this as a scratch register for arithmetic operations. Should not be allocated in regalloc
- %rsp -> The stack pointer. Should not be allocated in regalloc
- %rbp -> For stack pointing
- %edx -> used by the idivl instruction; needs special consideration during register allocation. (usable during graph colouring, but MAY BE PRE-COLOURED)
- %eax -> Not allocated

## Compiler Phases (Frontend)

Parse Tree --sem analysis--> AST --elaboration--> elaborated AST --trans--> IR tree

### Elaboration
Goals: 
 - Remove syntactic sugar
 - Make scope explicit
 - Don't want to convert too far away from original code. If not, you can't give an error message back to the user

Example:
  Turning for loops into while loop 
  for (int x = 4; x < 8128; x++) {y = y + x}
  ----elaboration---->
  WRONG: int x = 4; while (x < 8128) ... Wrong because the scope of x doesn't end after the while loop!
  Jan recommends that for declarations, always have something like:
    use decl(x, int, s) <- s is the statement that is the scope of x.
  RIGHT:
    decl(x, int, while(x < 8128){y = y+4; x = x + 1})
        
## Compiler Phases (Backend)

Intermediate Code generation -> Register Allocation -> Stack Spilling -> Instruction Translation

### Intermediate Code Generation
The intermediate code generation phase (intcodegen) takes in an IR tree and generates a list of 3-address abstract assembly instructions. As of lab 1, we have not changed anything from the starter code provided to us.

### Register Allocation
Register allocation takes in a list of abstract assembly instructions, and then does the following:
    liveness analysis -> build interference graph -> max cardinality search -> greedy graph colouring -> replace temps

Liveness analysis also outputs the number of distinct assembly operands. This allows us to skip either max cardinality search or the entire register allocation phase, depending on how many operands the input has. The thresholds for skipping are controlled by `_skip_mcs` and `_skip_colouring` in `top.ml`.

#### Liveness Analysis
Liveness analysis takes in a list of abstract assembly instruction, and outputs a list of Liveness.line, which are then used in building the interference graph. It also outputs an int which contains the number of operands in the file. We use this to "short-circuit" register allocation for pathalogical test cases.

Certain x86 instructions have to be treated carefully. Notably,
- Div and Mod are specified to use %eax and %edx, since they both use the idiv instruction.

The algorithm currently used is the one in recitation; however, this is inefficient, especially when while loops are introduced.
TODO: Change to the new algorithm mentioned in lecture for lab 2.

Notes from lecture
- Simplify rules to the use/def/succ form so that we can expand this to loops and conditionals.
- Might help to have "false successors". So succ(l,l') is l' can be a succ of l if l' exists.
  Example:
    l : d <- x o y
    Then conclude: use(l,x), use(l,y), def(l,d), succ(l,l+1) (IF THE SUCCESSOR EXISTS)
- When we have loops, there are several ways we can do it:
  - Line-oriented approach: do backward passes until we find no more changes.
    Note that this is inefficient since we have to check set membership many many times, 
    especially for when we have nested for loops (possible test case)
  Example with loops: gcd(x1,x2)     |    pass 1     |    pass 2 (additional to add)
    l1: if (x != 0) then l2 else l8  |   x1, x2      |  -
    l2: q <- x1 / x2                 |   x1, x2      |  -
    l3: t <- x1 * q                  |   x1, q, x2   |  -
    l4: r <- x1 - t                  |   x1, t, x2   |  -
    l5: x1 <- x2                     |   x2, r .     |  -
    l6: x2 <- r                      |     r         |  x1
    l7: goto l1                      |     -         |  x1, x2
    l8: ret <- x1                    |    x1         |
    l9: return                       |    ret        |  ret
   After we do one more pass, we find there are no more changes. So we are done.
   - Variable-oriented approach: start at the back and look at variables used at the line.
     Then propagate backwards to its predecessors until it is defined, or it is already live there.
     Then continue to the next upwards line.
     
     This version is more efficient since we only have to check membership once for each line.
     Less set operations, Jan recommends this approach.

                          gcd(x1,x2)     |    
        l1: if (x != 0) then l2 else l8  |              x2  -       -
        l2: q <- x1 / x2                 |              x2  x1     -
        l3: t <- x1 * q                  |              x2  x1  -  q
        l4: r <- x1 - t                  |           -  x2  x1  t
        l5: x1 <- x2                     |           r  x2
        l6: x2 <- r                      |      x1   r  -
        l7: goto l1                      |      x1 -    x2  -
        l8: ret <- x1                    |   -  x1
        l9: return                       |  ret  

- Constructing interference graph from this:
    - Overlapping live ranges: if we use a variable oriented approach, if two variables are live at the same line, then we know they interfere. 
      Good: This always results in a chordal graph SSA form.
      But: This doesn't work if you have dead code in the program.
      Example: 
        l1: a <- 1
        l2: b <- 2          a
        l3: ret <- a        a
        l4: return          ret
      Register allocation will use RAX for all registers, returning the wrong result.
    - Assignment based: live-out set formulation. Look at liveness analysis lecture: 5.8
      Good: This results in sparser graphs. 
      Bad: This doesn't necessarily result in chordal graphs. Also, having sparser graphs might be bad if we have many temps - puts a heavy strain on our data structures.

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

### Instruction Translation
The instruction translation phase (instrtrans) takes in a list of abstract assembly instructions with registers and stack references, and returns a list of finalassem instructions, which resemble x86 instructions.

It requires that 
1. The program represented by the input list is well-formed

It does the following:
1. Conversion of instructions
2. Adds a prologue:

    pushq %rbp  
    movq  $rsp, %rbp

and an epilogue:
    
    popq %rbp
    ret

to all instruction lists.

#### Conversion of instructions during translation
Certain x86 instructions require that one of their operands is a register. As such, we make use of a scratch register %r10d.

1. Mov: Converted directly to the x86 equivalent, except if both the src and dest are references. 
    In that case, we use %r10d as an intermediate register. 
    For example, `-4(%rbp) <- -8(%rbp)` is converted to 

    movl -8(%rbp), %r10d
    movl %r10d, -4(%rbp)

2.  Add / Sub / Mul: converted directly to their x86 equivalent. 
    For example, `d = s1 - s2` is converted to

    movl s1, %r10
    subl s2, %r10
    movl %r10, d

3.  Div / Mod: `d = r1 / r2` is converted to

        movl r1, %eax
        cltd
        idivl   r2
        movl    %eax, d

    while `d = r1 % r2` is converted to

        mov r1, %rax
        cltd
        idivl  r2
        movl  %edx, d

## Tips from Lectures and TAs
- Talk to TAs about compiler design decisions
    - Ask them what options we have for IR beyond just lists.
- Set up local testing - done.
- Make sure you pass all test cases in first 3 labs
- Start working on reg alloc from Friday onwards
- Use comments and documentation
- testing - use --prune flag with keep.txt in relevant test folder.



# Interference graph building

# Construct interference graph
1. Requires: uses, liveout
2. Returns: adjlist (hashtbl of Node to List of Nodes.)
    - Currently done, but will need to update once loops and jumps are introduced (see TODO in buildintfgraph.ml)
    - Also will need to update succ_table generation

# Maximimal Cardinality Search
1. Requires: adjlist (hashtbl of Node to List of Nodes.)
2. Returns: List of Nodes in reverse order of removal from graph.

# Greedy graph colouring
1. Requires: adjlist and ordered List of Nodes
2. Returns: Hashmap from Nodes to Nodes