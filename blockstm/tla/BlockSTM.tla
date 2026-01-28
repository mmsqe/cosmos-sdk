---------------------------- MODULE BlockSTM ----------------------------
EXTENDS Integers, FiniteSets, Sequences, TLC

(*
  A small, TLC-friendly model of Block-STM-style optimistic parallel execution
  with re-validation.

  Safety goal: when all transactions validate in block order (0..N-1), each
  transaction must have read the same value as in sequential block order.

  Validation mode (constant ValueBased):
    ValueBased = FALSE  \* validate by observed writer/version
    ValueBased = TRUE   \* validate by observed value
*)

CONSTANTS
  ValueBased \* BOOLEAN

ASSUME ValueBased \in BOOLEAN

(****************************** MODEL ************************************)

\* Fixed tiny model (ABA-shaped) to keep TLC runs fast and deterministic.
Txns == 0..3
Keys == 0..1

InitVal == [k \in Keys |-> 0]

\* Each txn i reads ReadKey[i], then writes (read + Delta[i]) to WriteKey[i].
ReadKey == [i \in Txns |-> 0]
WriteKey == [i \in Txns |-> IF i = 3 THEN 1 ELSE 0]
Delta == [i \in Txns |-> IF i = 0 THEN 1 ELSE IF i = 1 THEN -1 ELSE IF i = 2 THEN 1 ELSE 0]

\* Status is minimal: we model only Ready and Executed.
Status == {"Ready", "Executed"}

VARIABLES
  status,    \* [Txns -> Status]
  inc,       \* [Txns -> Nat]
  vIdx,      \* Nat validation index (commit order)
  validated, \* [Txns -> BOOLEAN]
  readVal,   \* [Txns -> Int] observed value at last execution
  readVer,   \* [Txns -> (Int \X Nat)] observed writer version <<txn, inc>> or <<-1,0>>
  writeVal   \* [Txns -> Int] value written at last execution

Vars == <<status, inc, vIdx, validated, readVal, readVer, writeVal>>

TypeOK ==
  /\ status \in [Txns -> Status]
  /\ inc \in [Txns -> Nat]
  /\ vIdx \in 0..Cardinality(Txns)
  /\ validated \in [Txns -> BOOLEAN]
  /\ readVal \in [Txns -> Int]
  /\ readVer \in [Txns -> (Int \X Nat)]
  /\ writeVal \in [Txns -> Int]

\* Writers that are currently visible to txn i for key k:
PriorWriters(i, k) == {j \in Txns : j < i /\ status[j] = "Executed" /\ WriteKey[j] = k}

VisibleWriter(i, k) ==
  IF PriorWriters(i, k) = {}
    THEN -1
    ELSE CHOOSE m \in PriorWriters(i, k) : \A x \in PriorWriters(i, k) : x <= m

VisibleVal(i, k) ==
  IF VisibleWriter(i, k) = -1 THEN InitVal[k] ELSE writeVal[VisibleWriter(i, k)]

TxnCount == Cardinality(Txns)

\* When all txns are validated in order.
Done == vIdx = TxnCount

Init ==
  /\ status = [i \in Txns |-> "Ready"]
  /\ inc = [i \in Txns |-> 0]
  /\ vIdx = 0
  /\ validated = [i \in Txns |-> FALSE]
  /\ readVal = [i \in Txns |-> 0]
  /\ readVer = [i \in Txns |-> <<-1, 0>>]
  /\ writeVal = [i \in Txns |-> 0]

ReadFromTxn(i) == readVer[i][1]
ReadFromInc(i) == readVer[i][2]

(***************************** TRANSITIONS **********************************)

Exec(i) ==
  /\ i \in Txns
  /\ status[i] = "Ready"
  /\ LET rk == ReadKey[i]
         w  == VisibleWriter(i, rk)
         v  == VisibleVal(i, rk)
         ver == IF w = -1 THEN <<-1, 0>> ELSE <<w, inc[w]>>
     IN
       /\ status' = [status EXCEPT ![i] = "Executed"]
       /\ inc' = inc
       /\ vIdx' = vIdx
       /\ validated' = [validated EXCEPT ![i] = FALSE]
       /\ readVal' = [readVal EXCEPT ![i] = v]
       /\ readVer' = [readVer EXCEPT ![i] = ver]
       /\ writeVal' = [writeVal EXCEPT ![i] = v + Delta[i]]

Abort(i) ==
  /\ i \in Txns
  /\ status[i] = "Executed"
  /\ status' = [status EXCEPT ![i] = "Ready"]
  /\ inc' = [inc EXCEPT ![i] = inc[i] + 1]
  /\ vIdx' = vIdx
  /\ validated' = [validated EXCEPT ![i] = FALSE]
  /\ readVal' = [readVal EXCEPT ![i] = 0]
  /\ readVer' = [readVer EXCEPT ![i] = <<-1, 0>>]
  /\ writeVal' = [writeVal EXCEPT ![i] = 0]

Validate(i) ==
  /\ i \in Txns
  /\ i = vIdx
  /\ status[i] = "Executed"
  /\ ~validated[i]
  /\ LET rk == ReadKey[i]
         cw == VisibleWriter(i, rk)
         cv == VisibleVal(i, rk)
         cver == IF cw = -1 THEN <<-1, 0>> ELSE <<cw, inc[cw]>>
         ok == IF ValueBased THEN (cv = readVal[i]) ELSE (cver = readVer[i])
     IN
       IF ok
         THEN
           /\ status' = status
           /\ inc' = inc
           /\ vIdx' = vIdx + 1
           /\ validated' = [validated EXCEPT ![i] = TRUE]
           /\ readVal' = readVal
           /\ readVer' = readVer
           /\ writeVal' = writeVal
         ELSE Abort(i)

ExecStep == \E i \in Txns : Exec(i)
ValidateStep == IF vIdx \in Txns THEN Validate(vIdx) ELSE FALSE

Next == ExecStep \/ ValidateStep

Spec == Init /\ [][Next]_Vars

(****************************** SAFETY ************************************)

\* Reads never come from the future.
NoFutureReads ==
  \A i \in Txns :
    status[i] = "Executed" => (ReadFromTxn(i) = -1 \/ ReadFromTxn(i) < i)

\* If everything validated, each txn read the sequentially-visible value.
\* (With fixed block order 0..N-1, sequential visibility is "last writer < i".)
SoundAtDone ==
  Done => (\A i \in Txns : readVal[i] = VisibleVal(i, ReadKey[i]))

THEOREM TypeOK
THEOREM NoFutureReads
THEOREM SoundAtDone
====
