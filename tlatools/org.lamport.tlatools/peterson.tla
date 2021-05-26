---- MODULE peterson ----
EXTENDS TLC, Naturals, FiniteSets
\*
\* Specification of Peterson's algorithm in TLA+.
\*

(*
    Summary of the algorithm in pseudocode (i.e. PlusCal).

    variables flag = [i \in {0, 1} |-> FALSE],  turn = 0;
        \* Declares the global variables flag and turn and their initial values;
        \* flag is a 2-element array with initially flag[0] = flag[1] = FALSE.
        process (proc \in {0,1}) {
        \* Declares two processes with identifier self equal to 0 and 1.
        a1: while (TRUE) {
                skip ;  \* the noncritical section
        a2:  flag[self] := TRUE ;
        a3:  turn := 1 - self ;   
        a4:  await (flag[1-self] = FALSE) \/ (turn = self);
        cs:  skip ;  \* the critical section
        a5:  flag[self] := FALSE               }     }     }
*)
        
VARIABLE flag, turn

\* The program counter for each process.
VARIABLE pc

vars == << flag, turn, pc >>

\* The set of processes.
\* ProcSet == ({0,1})
CONSTANT ProcSet

ASSUME Cardinality(ProcSet) = 2

\* Return the other process.
Other(p) == CHOOSE q \in ProcSet : q # p

Init == 
    \* /\ flag = [i \in {0, 1} |-> FALSE]
    /\ flag = [i \in ProcSet |-> FALSE]
    /\ turn = CHOOSE p \in ProcSet : TRUE
    /\ pc = [self \in ProcSet |-> "a1"]

\*
\* The transitions of the protocol.
\*

a1(self) == /\ pc[self] = "a1"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "a2"]
            /\ UNCHANGED << flag, turn >>

\* A process sets its own flag to TRUE.
a2(self) == /\ pc[self] = "a2"
            /\ flag' = [flag EXCEPT ![self] = TRUE]
            /\ pc' = [pc EXCEPT ![self] = "a3"]
            /\ turn' = turn


\* A process updates 'turn'.
a3(self) == /\ pc[self] = "a3"
            /\ turn' = Other(self)
            /\ pc' = [pc EXCEPT ![self] = "a4"]
            /\ flag' = flag

\* A process enters the critical section.
a4(self) == /\ pc[self] = "a4"
            /\ (flag[Other(self)] = FALSE) \/ (turn = self)
            /\ pc' = [pc EXCEPT ![self] = "cs"]
            /\ UNCHANGED << flag, turn >>

\* A process exits the critical section.
cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "a5"]
            /\ UNCHANGED << flag, turn >>

\* A process resets its own flag to FALSE after it left the critical section.
a5(self) == /\ pc[self] = "a5"
            /\ flag' = [flag EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = "a1"]
            /\ turn' = turn

Next == 
    \E self \in ProcSet : 
        \/ a1(self)
        \/ a2(self) 
        \/ a3(self) 
        \/ a4(self) 
        \/ cs(self) 
        \/ a5(self)

Spec == /\ Init /\ [][Next]_vars

\* The mutual exclusion property i.e. the processes cannot be 
\* inside the critical sectuion at the same time.
Mutex == \A p,q \in ProcSet : (p # q) => ~(pc[p] = "cs" /\ pc[q] = "cs")
MutexWrong == \A p,q \in ProcSet : (p # q) => ~(pc[p] = "cs" /\ pc[q] = "a4")

NextUnchanged == UNCHANGED vars

Symmetry == Permutations(ProcSet)

Inv424test == \A self \in ProcSet : ~(pc[self] = "a3") \/ (flag[self] /\ (TRUE))

\* (pc[self] = "a3") => flag[self]
--------------------------------------------------------

\* 
\* Defining the inductive invariant.
\*

TypeOK == 
    /\ flag \in [ProcSet -> {TRUE, FALSE}]
    /\ turn \in ProcSet
    /\ pc \in [ProcSet -> {"a1","a2","a3","a4","a5","cs"}]    

\*
\* Inductive strengthening assertions.
\*

\* If a process is at any of these positions, then its flag must be true.
A1 == \A p \in ProcSet : (pc[p] \in {"a3","a4","cs", "a5"}) => flag[p]

\* If, after we gave the turn to the other process, the turn is now ours, then
\* this means the other process must have set 'turn' to our process id after we
\* TRUE. So, the other process must be stuck at a4 waiting for our flag to be
\* released, or for its turn again.
A2 == \A p \in ProcSet : 
        (pc[p] \in {"a4", "cs","a5"} /\ turn = p) => (pc[Other(p)] = "a4")

\* Inductive invariant.
Ind == 
    /\ TypeOK
    /\ Mutex
    /\ A1
    /\ A2

\* For checking the inductive invariant.
IInit == Ind

\* Inv155_learned == \A self \in ProcSet : flag[self] \/ (~(pc[self] = "a4") /\ (TRUE))
\* Inv204_learned == \A self \in ProcSet : flag[self] \/ (~(pc[self] = "a3") /\ (TRUE))
\* Inv368_learned == \A self \in ProcSet : ~(pc[self] = "cs") \/ (flag[self] /\ (TRUE))
\* Inv153_learned == \A self \in ProcSet : ~flag[self] \/ (~(pc[self] = "a2") /\ (TRUE))
\* Inv141_learned == \A self \in ProcSet : ~(pc[self] = "a5") \/ (flag[self] /\ (TRUE))
\* Inv112_learned == \A self \in ProcSet : ~(pc[self] = "a1") \/ (~flag[self] /\ (TRUE))
\* Inv468_learned == \A self \in ProcSet : ~flag[self] \/ (~~flag[self] /\ (~(pc[self] = "a2") /\ (TRUE)))
\* Inv208_learned == \A self \in ProcSet : flag[self] \/ (((flag[Other(self)] = FALSE) \/ (turn = self)) \/ (~(pc[self] = "cs") /\ (TRUE)))
\* Inv311_learned == \A self \in ProcSet : ~(pc[self] = "a2") \/ (~(pc[self] = "a3") /\ (~flag[self] /\ (TRUE)))
\* Inv81_learned == \A self \in ProcSet : (pc[self] = "a2") \/ (flag[self] \/ (~(pc[self] = "cs") /\ (TRUE)))






Inv766_learned == \A self \in ProcSet : ~~flag[self] \/ (~(pc[Other(self)] = "a2") /\ (TRUE))
Inv775_learned == \A self \in ProcSet : ~~flag[self] \/ (~(pc[Other(self)] = "a5") /\ (TRUE))
Inv781_learned == \A self \in ProcSet : ~~flag[self] \/ (~(pc[self] = "a1") /\ (TRUE))
Inv762_learned == \A self \in ProcSet : ~~flag[self] \/ (~(pc[Other(self)] = "a4") /\ (TRUE))
Inv766a_learned == \A self \in ProcSet : ~~flag[self] \/ (~(turn = Other(self)) /\ (TRUE))
====