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
