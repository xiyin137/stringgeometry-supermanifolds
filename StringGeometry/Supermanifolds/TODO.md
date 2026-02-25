# Supermanifolds Folder - Status and Plan

## Summary

The algebraic foundations are substantial, with most local integration
infrastructure formalized. Global assembly still has open proof obligations.

**Post-audit status** (5 rounds of comprehensive audit + targeted fixes):
- `BodyIntegral.SatisfiesChangeOfVar` — was vacuously strong, now properly parameterized
- `globalBerezinIntegral` — now takes `Set` argument for domain localization
- `SuperPartitionOfUnity` — `super_sum_eq_one` REMOVED from structure (was vacuous:
  evaluated each ρ_α in its own chart). Now an explicit `hSuperSum` hypothesis
  in GlobalStokes.lean using `composeEvalAt`
- `GlobalIntegralForm.SatisfiesSuperCocycle` — restricted to atlas transitions
- `global_super_stokes_no_boundary` — proper `hDivThm` classical divergence theorem
- StokesTheorem.lean hypotheses fixed (now use `d0_is_divergence`)
- Previous vacuous GlobalStokes placeholders replaced with explicit bridge hypotheses

**What IS genuinely proven** (real theorems, not tautologies):
- Local reduction: super Stokes → classical divergence theorem (via `d0_is_divergence`)
- Core algebraic infrastructure used by the active pipeline (Taylor, composition,
  pullback, Berezinian, partition normalization)
- Berezinian cocycle from chain rule
- `partialEven_mul`: product rule for ∂/∂xⁱ on Grassmann products

**Current folder total**: 20 `sorry` occurrences (allowlisted and tracked).

**What is NOT yet derived from local infrastructure**:
- Bridge hypotheses for global PU independence (double-sum transport expansions)
- Global correction-term cancellation from the PU derivative identity
  (`d(Σ ρ_α) = 0`) in the super setting
- Full coefficient-level support vanishing for generic super partitions of unity
- Super PU witness extraction from pure paracompactness/atlas data
- Body-level pullback identity needed by CoV bridge (now in explicit finite-sum form)

**Recently completed**:
- Leibniz rule for d₀ on products: `d0Codim1_mulByFunction`
  (proved in `Integration/ExteriorDerivative.lean`)
- Exact-term vanishing from divergence + support:
  `exact_term_zero_from_divergence` (GlobalStokes.lean)

---

## Current Status by File

### Excellent (no sorrys, genuinely proven)
| File | Notes |
|------|-------|
| Superalgebra.lean | Complete algebraic foundations, `grassmann_basis_card` proven |
| SuperRingCat.lean | map_maxIdeal properly formulated |
| SuperDomainAlgebra.lean | Ring/Algebra instances for SuperDomainFunction proven |
| Supermanifolds.lean | All placeholders fixed, proper sheaf conditions |
| PartialOddDerivation.lean | `partialOdd_odd_derivation'` proven |
| SuperJacobian.lean | Super Jacobian with proper grading, parity proven |
| Helpers/SuperMatrix.lean | SuperMatrix with block multiplication |
| Helpers/Berezinian.lean | Berezinian computation, ber_congr |
| Helpers/BerezinianMul.lean | `ber_mul` proven (2900+ lines) |
| Helpers/PartialOddLeibniz.lean | Sign lemmas for Leibniz rule |
| Helpers/GrassmannSmooth.lean | GrassmannSmooth predicate, all closure properties proven |
| Helpers/NilpotentTaylor.lean | Full Taylor expansion, all proven (0 sorrys) |
| Helpers/NilpotentInverse.lean | Geometric series inverse, bridge lemmas — all proven (0 sorrys) |
| Integration/SuperCompose.lean | Super function composition — all proven (0 sorrys) |
| Integration/IntegralFormCodim.lean | Codimension-1 integral forms, complete |
| Integration/PartitionOfUnity.lean | All proven |
| Integration/StokesTheorem.lean | Local Stokes via d0_is_divergence reduction (0 sorrys) |
| Integration/Pullback.lean | pullbackProper, berezinianCarrierAt_grassmannSmooth — all proven (0 sorrys) |
| Integration/ExteriorDerivative.lean | d₀, linearity, `d0_is_divergence`, `partialEven_mul`, `d0Codim1_mulByFunction` (0 sorrys) |
| Integration/GlobalStokes.lean | Placeholder-free; includes `global_super_stokes_no_boundary_more_reduced` with internally derived exact-term vanishing |
| BerezinIntegration.lean | Legacy placeholders removed; canonical witness constructor `BodyPartitionWitness.toSuperPartition` added |

### Has Honest Sorrys (definitions mostly correct, proofs pending)
| File | Sorrys | Notes |
|------|--------|-------|
| Helpers/FiniteGrassmann.lean | 2 | Legacy approximate composition (`composeLegacyApprox`) smoothness + downstream chain-rule placeholder |
| Helpers/SuperChainRule.lean | 5 | Legacy full-cocycle-to-chain-rule bridge has pending proofs |
| Helpers/FormalPowerSeries.lean | 1 | Jacobi identity bridge step remains sorry |
| FPS/LogExp.lean | 1 | Inverse identity bridge step remains sorry |

### Legacy/Tautological (marked, not counting as "proven")
| File | Notes |
|------|-------|
| BerezinIntegration.lean: `super_stokes_legacy` | Hypothesis restates conclusion. Superseded by StokesTheorem.lean |
| BerezinIntegration.lean: `super_divergence_theorem_legacy` | Proves `x = x` via rfl. Boundary integral not formalized |
| BerezinIntegration.lean: `IntegralForm.pullbackLegacy` | Legacy approximate composition-only pullback. Superseded by `pullbackProper` in Pullback.lean |
| Integration/Legacy.lean | Deprecated compatibility aliases for legacy names |

### Sorrys Independent of Integration Pipeline
| File | Notes |
|------|-------|
| Batchelor.lean | `batchelor_theorem`, `batchelor_splitting`, `splitting_nonuniqueness` — deep theorems |

---

## Remaining Work (Integration Pipeline)

### Priority 1: Leibniz Rule for d₀ on Products — DONE
**Result**: `d0Codim1_mulByFunction` and `wedgeEvenDeriv` are now formalized in
`Integration/ExteriorDerivative.lean`.
**Use**: This is the key algebraic decomposition step for the global Stokes proof.

### Priority 2: Prove Body-Level Pullback Identity (`hPullbackBody`)
**Status**:
- `berezin_change_of_variables` is proved from bridge hypothesis `hPullbackBody`.
- `pullback_berezinOdd_expand` (Pullback.lean) now gives the explicit finite Grassmann
  sum formula for the pullback top component.
- `berezin_change_of_variables_from_pullback_expansion` (GlobalStokes.lean) is added;
  it reduces CoV to this explicit expansion bridge.
**What remains**: Discharge the explicit finite-sum bridge from Pullback/Berezinian infrastructure:
`berezinIntegralOdd (pullbackProper φ ω).coefficient =
  (berezinIntegralOdd ω.coefficient) ∘ φ.bodyMap · det(Dφ.bodyMap)`.

### Priority 3: Discharge Bridge Hypotheses for `globalBerezinIntegral_independent_proper`
**Status**: The theorem is now proved from explicit double-sum bridge hypotheses
(`cross`, `hExpand₁`, `hExpand₂`).
**What remains**: Derive those hypotheses from cocycle + CoV + PU machinery.

### Priority 4: Discharge Bridge Hypotheses for `global_super_stokes_no_boundary`
**Status**:
- Added `global_super_stokes_no_boundary_reduced` in `GlobalStokes.lean`.
- This new theorem derives `hGlobalExpand` and `hLeibnizDecomp` internally from
  definitions + `d0Codim1_mulByFunction` + body-integral linearity.
- Added `exact_term_zero_from_divergence`, deriving chartwise exact-term vanishing
  from `hDivThm` plus full coefficient support vanishing (`hSupportFull`).
- Added `global_super_stokes_no_boundary_more_reduced`, which now derives
  `hExactZero` internally.
- Added `global_super_stokes_no_boundary_lift_partition`, which derives
  `hSupportFull` automatically from `hLift : ρ_α = liftToSuper(h_α)`.
- Added `global_super_stokes_no_boundary_body_partition`, specializing directly
  to `BodyPartitionWitness.toSuperPartition`.
**What remains**:
- Derive global correction cancellation (`hCorrectionZero`) from the super PU
  derivative identity.

### Priority 5: `partition_of_unity_exists` (BerezinIntegration.lean)
**Status**: Done in assumption-driven form via `BodyPartitionWitness`:
- Added canonical constructor `BodyPartitionWitness.toSuperPartition`.
- Added explicit properties:
  - `BodyPartitionWitness.toSuperPartition_functions`
  - `BodyPartitionWitness.toSuperPartition_support_full`
- `partition_of_unity_exists` now wraps this canonical constructor.
**What remains**: derive `BodyPartitionWitness` automatically from pure
paracompactness/atlas infrastructure (Mathlib `SmoothPartitionOfUnity` bridge).

---

## Dependency Flowchart (Global Stokes)

```text
Local algebraic derivative layer
--------------------------------
partialEven_mul
  └─> d0Codim1_mulByFunction (DONE)
        └─> Leibniz decomposition for chart terms: d0(ρ·ν) = ρ·d0(ν) + correction

Local integration layer
-----------------------
d0_is_divergence
super_stokes_codim1_no_boundary (StokesTheorem.lean)
hDivThm (classical divergence theorem hypothesis)
  └─> exact_term_zero_from_divergence (DONE, under hSupportFull)

Global change-of-variables layer
--------------------------------
pullbackEvalAt + berezinianCarrierAt + BodyIntegral.SatisfiesChangeOfVar
  └─> pullback_berezinOdd_expand (DONE: explicit top-component finite-sum formula)
        └─> explicit pullback-top reduction to body determinant (TODO)
              ├─> berezin_change_of_variables_from_pullback_expansion (DONE, via explicit bridge)
              └─> berezin_change_of_variables (DONE, via hPullbackBody bridge)
                    └─> globalBerezinIntegral_independent_proper (DONE via bridge hypotheses; TODO to derive bridges)

Global partition layer
----------------------
hSuperSum (super partition identity: Σ ρ_α = 1 in common chart)
hSupportFull (all coefficients vanish off support domains; currently assumed)
hLift (lifted PU case: ρ_α = liftToSuper h_α)
BodyPartitionWitness.toSuperPartition (canonical lifted PU construction)
SatisfiesSuperCocycle
BodyIntegral.IsLinear
  ├─> used in globalBerezinIntegral_independent_proper
  ├─> used in global_super_stokes_no_boundary_more_reduced (exact-term derivation)
  ├─> support_full_of_lift_partition (DONE)
  └─> correction-term cancellation in global_super_stokes_no_boundary (still TODO to derive)

Final theorem
-------------
d0Codim1_mulByFunction
+ d0_is_divergence
+ super_stokes_codim1_no_boundary / hDivThm
+ hSuperSum cancellation
  ├─> global_super_stokes_no_boundary (DONE via bridge hypotheses)
  ├─> global_super_stokes_no_boundary_reduced (DONE; two bridge hypotheses eliminated)
  └─> global_super_stokes_no_boundary_more_reduced (DONE; exact-term bridge eliminated)
      └─> global_super_stokes_no_boundary_lift_partition (DONE; hSupportFull removed in lifted case)
          └─> global_super_stokes_no_boundary_body_partition (DONE; canonical witness PU specialization)
```

---

## Key Proven Infrastructure (Reusable)

| Component | File | Used By |
|-----------|------|---------|
| `grassmann_soul_nilpotent` | FiniteGrassmann.lean | Phase 1 (Taylor termination) |
| `hasNoConstant_pow_vanishes` | NilpotentInverse.lean | Phase 4 (geometric inverse) |
| `grassmannGeomInverse_mul/_right` | NilpotentInverse.lean | Phases 4, 5 |
| `ringInverse_eq_grassmannInv` | NilpotentInverse.lean | Classical.choose = geometric series |
| `finiteGrassmann_inv_grassmannSmooth` | NilpotentInverse.lean | Berezinian smoothness |
| `det_even_grassmannSmooth` | NilpotentInverse.lean | Determinant smoothness |
| `adjugate_even_grassmannSmooth` | NilpotentInverse.lean | Berezinian smoothness (Pullback) |
| `matInv_even_grassmannSmooth` | NilpotentInverse.lean | Berezinian smoothness (Pullback) |
| `ringInverse_even_grassmannSmooth` | NilpotentInverse.lean | Ring.inverse smoothness |
| `berezinianCarrierAt_grassmannSmooth` | Pullback.lean | Phase 3 (pullback smoothness) |
| `smoothTaylorGrassmann` | NilpotentTaylor.lean | Phase 2 (composition) |
| `composeEvalAt` | SuperCompose.lean | Phases 3, 5 |
| `pullbackEvalAt` | Pullback.lean | Phases 6-8 |
| `normalizedPartition_sum_one` | PartitionOfUnity.lean | Phase 5 |
| `SuperMatrix.ber_mul` | BerezinianMul.lean | Phase 3 (pullback composition) |
| `berezinian_cocycle_from_chain_rule` | SuperChainRule.lean | Phase 7 |
| `d0_is_divergence` | ExteriorDerivative.lean | Local Stokes reduction |
| `partialEven_mul` | ExteriorDerivative.lean | Leibniz rule for d₀ |
| `d0Codim1_mulByFunction` | ExteriorDerivative.lean | Global Stokes decomposition step |
| Local Stokes (2 theorems) | StokesTheorem.lean | Global Stokes |

---

## Definitions Audit Summary (5 rounds)

### Fixed across audit rounds:
| Issue | Location | Fix |
|-------|----------|-----|
| **C1**: `SatisfiesChangeOfVar` vacuous | BerezinIntegration.lean | Now requires diffeomorphism Φ, signed det |
| **C2**: `globalBerezinIntegral` no domain | BerezinIntegration.lean | `bodyIntegral` now takes `Set` argument |
| **C3**: `SuperPartitionOfUnity` body-only sum | BerezinIntegration.lean | `super_sum_eq_one` REMOVED, now hypothesis `hSuperSum` |
| **H1**: Body-only cocycle | GlobalStokes.lean | Added `SatisfiesSuperCocycle` using `pullbackEvalAt` |
| **H1b**: `SatisfiesSuperCocycle` over-quantified | GlobalStokes.lean | Restricted to `SuperTransition` |
| **H2-H4**: Vacuous proofs exploiting C1 | GlobalStokes.lean | Replaced by explicit bridge-hypothesis theorems |
| **H5**: StokesTheorem hypotheses vacuous | StokesTheorem.lean | Uses `d0_is_divergence` + classical div thm |
| **H6**: `hLocalStokes` per-chart (false) | GlobalStokes.lean | Replaced with `hDivThm` |

---

## References

- Witten, "Notes On Supermanifolds And Integration" (1209.2199): sections 3.1-3.5
- Rogers, "Supermanifolds" (2007): Chapter 11
- Bernstein-Leites, "Integral Forms And The Stokes Formula On Supermanifolds" (1977)
- Deligne-Morgan, "Notes on Supersymmetry" (for supermatrix algebra)
