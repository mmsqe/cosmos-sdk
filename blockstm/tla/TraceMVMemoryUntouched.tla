----------------------- MODULE TraceMVMemoryUntouched -----------------------
EXTENDS Integers, Sequences

(******************************************************************************
Trace-validation style harness for MVMemory untouched-store cleanup.

This mirrors the approach discussed in etcd-io/raft#111:
  - the implementation (or a test harness) records a finite trace of steps,
  - TLC checks that the spec can follow exactly those transitions.

Here the trace is just a sequence of step labels:
  StepTrace = << PhExec1, PhExec2, PhRead >>

The harness *disallows stuttering before the trace ends* so that an invalid trace
causes TLC to deadlock/fail quickly rather than silently stutter forever.
******************************************************************************)

CONSTANTS
  CleanupUntouched,
  StepTrace

\* Keep the on-disk config (.cfg) free of quoted strings.
PhExec1 == "Exec1"
PhExec2 == "Exec2"
PhRead  == "Read"
PhDone  == "Done"

ASSUME CleanupUntouched \in BOOLEAN
ASSUME StepTrace \in Seq({PhExec1, PhExec2, PhRead})

Keys == 0..1
InitVal == [k \in Keys |-> 0]

VARIABLES
  phase,     \* "Exec1" | "Exec2" | "Read" | "Done"
  mem,       \* [Keys -> Int]
  readVal,   \* Int
  step       \* 1..Len(StepTrace)+1

vars == <<phase, mem, readVal, step>>

TypeOK ==
  /\ phase \in {PhExec1, PhExec2, PhRead, PhDone}
  /\ mem \in [Keys -> Int]
  /\ readVal \in Int
  /\ step \in 1..(Len(StepTrace) + 1)

Init ==
  /\ phase = PhExec1
  /\ mem = InitVal
  /\ readVal = 0
  /\ step = 1

Exec1 ==
  /\ phase = PhExec1
  /\ phase' = PhExec2
  /\ mem' = [mem EXCEPT ![0] = 1]
  /\ readVal' = readVal

Exec2 ==
  /\ phase = PhExec2
  /\ phase' = PhRead
  /\ mem' = IF CleanupUntouched
              THEN [mem EXCEPT ![1] = 2, ![0] = InitVal[0]]
              ELSE [mem EXCEPT ![1] = 2]
  /\ readVal' = readVal

Read ==
  /\ phase = PhRead
  /\ phase' = PhDone
  /\ mem' = mem
  /\ readVal' = mem[0]

StepAction ==
  /\ step <= Len(StepTrace)
  /\ LET e == StepTrace[step]
     IN  \/ /\ e = PhExec1 /\ Exec1
         \/ /\ e = PhExec2 /\ Exec2
         \/ /\ e = PhRead  /\ Read
  /\ step' = step + 1

Next == StepAction

Spec == Init /\ [][Next]_vars

(****************************** SAFETY ************************************)

NoStaleUntouchedAtDone ==
  phase = PhDone => readVal = InitVal[0]

\* If the trace claims there are more steps, the spec must be able to take one.
\* This is the key "trace validation" check: recorded steps constrain transitions.
TraceStepEnabled ==
  step <= Len(StepTrace) => ENABLED Next

THEOREM TypeOK
THEOREM NoStaleUntouchedAtDone
THEOREM TraceStepEnabled
====
