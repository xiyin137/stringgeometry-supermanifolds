import StringGeometry.Supermanifolds.BerezinIntegration

/-!
# Core Integration API

Core definitions for supermanifold integration used by the modern pipeline:
- `IntegralForm`
- `SuperCoordChange`
- `berezinIntegralOdd`
- `localBerezinIntegral`
- global integration support structures

Legacy compatibility aliases (`IntegralForm.pullback`, `super_stokes`, etc.)
are provided in `Integration/Legacy.lean` and should not be used in new code.
-/

