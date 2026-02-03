------------------- MODULE TraceMVMemoryUntouchedTV_bug -------------------
EXTENDS Sequences

PhExec1 == "Exec1"
PhExec2 == "Exec2"
PhRead  == "Read"

VARIABLES phase, mem, readVal, step

TV == INSTANCE TraceMVMemoryUntouched
  WITH CleanupUntouched <- FALSE,
  StepTrace <- << PhExec1, PhExec2, PhRead >>,
  phase <- phase,
  mem <- mem,
  readVal <- readVal,
  step <- step

Spec == TV!Spec
TypeOK == TV!TypeOK
NoStaleUntouchedAtDone == TV!NoStaleUntouchedAtDone
TraceStepEnabled == TV!TraceStepEnabled
====
