------------------------------ MODULE FairSeq2 ------------------------------
EXTENDS Integers
(***************************************************************************
PlusCal options (version 1.5)
--fair algorithm FairSeq {
    variable x = 0 ;
    fair { while (x < 10) {
            x := x+1;
         }
    }
}
 ***************************************************************************)
\* BEGIN TRANSLATION PCal-07e0e68497291a78b07d8fb9d5597180
VARIABLES x, pc

vars == << x, pc >>

Init == (* Global variables *)
        /\ x = 0
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF x < 10
               THEN /\ x' = x+1
                    /\ pc' = "Lbl_1"
               ELSE /\ pc' = "Done"
                    /\ x' = x

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION TLA-8d9de25f8162fd0489585bc374dff964
=============================================================================
\* Modification History
\* Last modified Sun Mar 20 10:13:11 PDT 2011 by lamport
\* Created Sun Mar 20 10:10:54 PDT 2011 by lamport
