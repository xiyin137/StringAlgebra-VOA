# StringAlgebra VOA

Standalone extraction of `StringAlgebra.VOA` from the StringAlgebra monorepo.

## Status (2026-02-26)

1. Theorem-level `sorry` count in `StringAlgebra/VOA`: 0
2. Anti-smuggling policy: no `axiom` smuggling, no assumption-bundle wrapper classes.
3. Build target: `lake build StringAlgebra.VOA`

## Quick Audit Commands

```bash
lake build StringAlgebra.VOA
rg -n '^\s*sorry\b' StringAlgebra/VOA --glob '*.lean'
rg -n '^\s*class\s+.*(Axiom|Axioms|Assumption|Assumptions)' StringAlgebra/VOA --glob '*.lean'
rg -n '^\s*axiom\s|\badmit\b|Classical\.choose|Classical\.epsilon|^\s*unsafe\s' StringAlgebra/VOA --glob '*.lean'
```
