# BlockSTM TLA+ regression checks

## What it checks

- Optimistic execution + ordered validation/commit
- Abort + re-execute when reads become inconsistent
- At completion, reads match a sequential execution in block order

Configs cover both validation styles:

- Version-based (`ValueBased = FALSE`)
- Value-based (`ValueBased = TRUE`)

## Running TLC

- `make tlc`

Individual configs:

- `make tlc-version`
- `make tlc-value`
- `make tlc-aba-version`
- `make tlc-aba-value`

MVMemory untouched-store cleanup regression:

- `make tlc-mvmemory` (should pass)
- `make tlc-mvmemory-bug` (expected failure; demonstrates what happens if old keys in an untouched store are not deleted)

Trace-validation style harness (recorded steps constrain the spec):

- `make tlc-mvmemory-trace` (should pass)
- `make tlc-mvmemory-trace-bug` (expected failure)

This is the same high-level idea as the trace validation discussion in https://github.com/etcd-io/raft/issues/111:
you run the implementation/tests to produce a trace (often NDJSON), transform it into a `CONSTANT Trace = <<...>>`,
and then run TLC on a harness spec that only allows transitions matching that trace.
