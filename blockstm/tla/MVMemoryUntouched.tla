-------------------------- MODULE MVMemoryUntouched --------------------------
EXTENDS Integers

(*
  Minimal MVMemory regression model for the "untouched store" cleanup case.

  Scenario:
    - A txn first writes to store 0 (key 0).
    - After re-execution, it writes only to store 1 (key 1).
    - Correct behavior: the old write in store 0 is removed.

  Constant CleanupUntouched toggles whether the old store-0 write is deleted.
  With CleanupUntouched = FALSE, TLC should find a counterexample.
*)

CONSTANTS
  CleanupUntouched

ASSUME CleanupUntouched \in BOOLEAN

Keys == 0..1
InitVal == [k \in Keys |-> 0]

VARIABLES
  phase,     \* "Exec1" | "Exec2" | "Read" | "Done"
  mem,       \* [Keys -> Int] (what is currently stored)
  readVal    \* Int (what the later reader observes at key 0)

vars == <<phase, mem, readVal>>

TypeOK ==
  /\ phase \in {"Exec1", "Exec2", "Read", "Done"}
  /\ mem \in [Keys -> Int]
  /\ readVal \in Int

Init ==
  /\ phase = "Exec1"
  /\ mem = InitVal
  /\ readVal = 0

Exec1 ==
  /\ phase = "Exec1"
  /\ phase' = "Exec2"
  /\ mem' = [mem EXCEPT ![0] = 1]
  /\ readVal' = readVal

Exec2 ==
  /\ phase = "Exec2"
  /\ phase' = "Read"
  /\ mem' = IF CleanupUntouched
              THEN [mem EXCEPT ![1] = 2, ![0] = InitVal[0]]
              ELSE [mem EXCEPT ![1] = 2]
  /\ readVal' = readVal

Read ==
  /\ phase = "Read"
  /\ phase' = "Done"
  /\ mem' = mem
  /\ readVal' = mem[0]

Next == Exec1 \/ Exec2 \/ Read

Spec == Init /\ [][Next]_vars

(****************************** SAFETY ************************************)

\* After re-exec writes only key 1, key 0 must look like InitVal.
NoStaleUntouchedAtDone ==
  phase = "Done" => readVal = InitVal[0]

THEOREM TypeOK
THEOREM NoStaleUntouchedAtDone
====
