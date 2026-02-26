# StringAlgebra-VOA

Lean 4 formalization of vertex operator algebra infrastructure.

## Scope

1. `StringAlgebra/VOA/Basic.lean`
2. `StringAlgebra/VOA/FormalDistributions.lean`
3. `StringAlgebra/VOA/VertexAlgebra.lean`
4. `StringAlgebra/VOA/Virasoro.lean`
5. `StringAlgebra/VOA/Modules.lean`
6. `StringAlgebra/VOA/Examples.lean`

## Build

```bash
lake build StringAlgebra.VOA
```

## Audit

```bash
rg -n '^\s*sorry\b' StringAlgebra/VOA --glob '*.lean'
rg -n '^\s*class\s+.*(Axiom|Axioms|Assumption|Assumptions)' StringAlgebra/VOA --glob '*.lean'
rg -n '^\s*axiom\s|\badmit\b|Classical\.choose|Classical\.epsilon|^\s*unsafe\s' StringAlgebra/VOA --glob '*.lean'
```

## Status (2026-02-26)

1. Theorem-level `sorry` count: `0`
2. No assumption-bundle wrapper classes.
3. No hidden-choice smuggling patterns.

## Related Repositories

1. Control repo: https://github.com/xiyin137/StringAlgebra
2. MZV: https://github.com/xiyin137/StringAlgebra-MZV
3. Linfinity: https://github.com/xiyin137/StringAlgebra-Linfinity
4. MTC: https://github.com/xiyin137/StringAlgebra-MTC
