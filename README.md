# stringgeometry-supermanifolds

Lean formalization of supermanifold foundations and integration theory.

This repository is the source-of-truth supergeometry component in the split
`StringGeometry` architecture.

## Architecture

### Position in the overall project

- `stringgeometry-supermanifolds` is independent.
- `stringgeometry-super-riemann-surfaces` depends on this repo (and on
  `stringgeometry-riemann-surfaces`).

### Internal layers

1. Algebraic and categorical foundations
   - superalgebras, super ring category, super domain function algebra
2. Geometric local model infrastructure
   - supermanifold charts/atlases and sheaf-level structure
3. Linear algebra and Jacobian/Berezinian layer
   - supermatrices, parity bookkeeping, Berezinian identities
4. Integration pipeline
   - codimension-1 integral forms, pullback, exterior derivative, local Stokes,
     global Stokes assembly, partition-of-unity interfaces
5. Design and proof-planning notes
   - proof architecture and dependency notes for major theorems

## Repository Map

- `StringGeometry/Supermanifolds.lean`
  - umbrella module imports for the active supermanifold stack.
- `StringGeometry/Supermanifolds/Superalgebra.lean`
- `StringGeometry/Supermanifolds/SuperRingCat.lean`
- `StringGeometry/Supermanifolds/SuperDomainAlgebra.lean`
- `StringGeometry/Supermanifolds/Supermanifolds.lean`
  - foundational supermanifold definitions and sheaf structure.
- `StringGeometry/Supermanifolds/SuperJacobian.lean`
- `StringGeometry/Supermanifolds/Helpers/`
  - reusable lemmas for graded algebra, odd derivations, supermatrices,
    Berezinian computations, nilpotent Taylor/inverse machinery.
- `StringGeometry/Supermanifolds/FPS/`
  - formal power series support infrastructure.
- `StringGeometry/Supermanifolds/Sheaves/`
  - super sheaf basics.
- `StringGeometry/Supermanifolds/Integration/`
  - integration core, pullback, exterior derivative, Stokes theorem, global
    Stokes, partition of unity, and legacy compatibility module.
- `StringGeometry/Supermanifolds/ProofIdeas/`
  - markdown design notes for integration and theorem dependencies.
- `StringGeometry/Supermanifolds/TODO.md`
  - tracked status of remaining proof obligations and dependency flowcharts.

## Build

```bash
lake update
lake build
```

## Targeted Checks

Run targeted builds before pushing:

```bash
lake build SGSupermanifolds
lake build StringGeometry.Supermanifolds.Integration.GlobalStokes
```

Allowed in-progress files are tracked in:

- `StringGeometry/Supermanifolds/sorry_allowlist.txt`

## CI

GitHub Actions workflow:

- `.github/workflows/lean-ci.yml`

Current triggers are intentionally limited to:

- `pull_request`
- `workflow_dispatch`

## Notes

- Namespace remains `StringGeometry.*` for compatibility with the umbrella repo
  and downstream components.
