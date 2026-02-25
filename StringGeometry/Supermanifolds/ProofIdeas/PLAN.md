# Integration Pipeline — Development Plan

## Architecture

**Track A (Local)**: Codimension-1 forms → d₀ → divergence → local Stokes. **COMPLETE (0 sorrys).**

**Track B (Global)**: Super composition → pullback → PU → CoV → independence → global Stokes. **Definitions corrected, 3 sorrys remain in GlobalStokes.lean.**

---

## Current State

### Complete (0 sorrys, genuinely proven)

| File | Content |
|------|---------|
| Helpers/NilpotentTaylor.lean | Full Taylor expansion in nilpotent elements |
| Helpers/NilpotentInverse.lean | (1+ε)⁻¹ via geometric series, bridge lemmas, det/adjugate/matInv smoothness |
| Helpers/GrassmannSmooth.lean | GrassmannSmooth predicate and closure properties |
| Helpers/SuperChainRule.lean | `berezinian_cocycle_from_chain_rule` |
| Helpers/BerezinianMul.lean | `ber_mul` (2900+ lines) |
| Helpers/Berezinian.lean | Ber computation |
| Integration/SuperCompose.lean | `composeEvalAt`, `composeProper` |
| Integration/Pullback.lean | `pullbackEvalAt`, `pullbackProper`, `berezinianCarrierAt_grassmannSmooth` |
| Integration/PartitionOfUnity.lean | `normalizedPartition_sum_one` (algebraic core) |
| Integration/IntegralFormCodim.lean | Codimension-1 integral forms |
| Integration/ExteriorDerivative.lean | d₀, linearity, `d0_is_divergence`, **`partialEven_mul`** (product rule) |
| Integration/StokesTheorem.lean | Local Stokes: super → classical divergence |

### Recently Completed
- **`partialEven_mul`** (ExteriorDerivative.lean): Product rule ∂(fg)/∂xⁱ = (∂f/∂xⁱ)g + f(∂g/∂xⁱ) for Grassmann products. Uses `partialEvenSmooth` helper + Leibniz for SmoothFunction products + distribution through sums/ite/smul.
- **SuperPartitionOfUnity fix**: Removed wrong `super_sum_eq_one` from structure (evaluated in own chart = vacuous). Now `hSuperSum` hypothesis in GlobalStokes.lean using `composeEvalAt`.

### Honest Sorrys (correct signatures, proofs pending)

| Location | Sorry | What's Needed |
|----------|-------|---------------|
| GlobalStokes.lean | `berezin_change_of_variables` | Body-level reduction lemma |
| GlobalStokes.lean | `globalBerezinIntegral_independent_proper` | Double-sum trick |
| GlobalStokes.lean | `global_super_stokes_no_boundary` | Leibniz rule + partition derivative cancellation |
| BerezinIntegration.lean | `partition_of_unity_exists` | Connect Mathlib paracompactness |
| BerezinIntegration.lean | `globalBerezinIntegral_independent` | Same as `_proper` version |
| BerezinIntegration.lean | `berezin_change_of_variables_formula` | Legacy, superseded by GlobalStokes |
| BerezinIntegration.lean | `IntegralForm.pullback` | Superseded by `pullbackProper` |

---

## Proof Dependencies

```
d0Codim1_mulByFunction (Leibniz rule for d₀)     ← IN PROGRESS
  ← partialEven_mul ✓
  ← SuperDomainFunction Ring/Algebra instances ✓ (mul_add, mul_sum, smul_mul_assoc)

berezin_change_of_variables
  ← body-level reduction lemma (NEW)
  ← pullbackEvalAt, berezinianCarrierAt (Pullback.lean) ✓
  ← BodyIntegral.SatisfiesChangeOfVar (fixed) ✓

globalBerezinIntegral_independent_proper
  ← berezin_change_of_variables
  ← SatisfiesSuperCocycle (fixed) ✓
  ← hSuperSum hypotheses ✓ (added to theorem signature)
  ← BodyIntegral.IsLinear ✓

global_super_stokes_no_boundary
  ← d0Codim1_mulByFunction (Leibniz) ← IN PROGRESS
  ← d0_is_divergence ✓
  ← hDivThm (hypothesis: classical divergence theorem)
  ← partition derivative cancellation: ∂(Σρ_α)/∂xⁱ = 0
    ← hSuperSum ✓
```

---

## Execution Order

### Step 1: Fix SuperPartitionOfUnity definition ✓ DONE
Removed `super_sum_eq_one` from structure. Now `hSuperSum` hypothesis in GlobalStokes.lean.

### Step 2: Prove `partialEven_mul` (product rule) ✓ DONE
~120 lines of infrastructure in ExteriorDerivative.lean. Uses `partialEvenSmooth` at SmoothFunction level.

### Step 3: Prove Leibniz rule for d₀ ← CURRENT
Using `partialEven_mul` + Ring/Algebra instances on SuperDomainFunction:

```lean
theorem d0Codim1_mulByFunction (ρ : SuperDomainFunction p q) (ν : IntegralFormCodim1 p q) :
    d0Codim1 (IntegralFormCodim1.mulByFunction ρ ν) =
    IntegralForm.mulByFunction ρ (d0Codim1 ν) + wedgeEvenDeriv ρ ν
```

Key insight: SuperDomainFunction has `Ring` + `Algebra ℝ` instances (SuperDomainAlgebra.lean), so `mul_sum`, `smul_mul_assoc` etc. are available. This simplifies factoring ρ out of sums.

### Step 4: Prove body-level reduction lemma
Show that `berezinIntegralOdd(pullbackProper φ ω)` at body level equals
`(berezinIntegralOdd ω) ∘ φ.bodyMap · det(body Jacobian)`.

### Step 5: Prove `berezin_change_of_variables`
Combine body-level reduction with `hChangeOfVar.change_of_var`.

### Step 6: Prove `globalBerezinIntegral_independent_proper`
Double-sum trick using Steps 1 and 5.

### Step 7: Prove `global_super_stokes_no_boundary`
Leibniz (Step 3) + local Stokes + partition derivative cancellation (Step 1).

---

## Available Berezinian Infrastructure

| Lemma | File | Used By |
|-------|------|---------|
| `ber_mul` | BerezinianMul.lean | `berezinian_cocycle_from_chain_rule` |
| `SuperMatrix.ber` | Berezinian.lean | `berezinianAt`, `pullbackEvalAt` |
| `berezinianCarrierAt` | Pullback.lean | `pullbackProper`, CoV body reduction |
| `berezinianCarrierAt_grassmannSmooth` | Pullback.lean | Smoothness of Ber coefficients |
| `berezinian_cocycle_from_chain_rule` | SuperChainRule.lean | `berezinian_cocycle_full` |
| `ringInverse_eq_grassmannInv` | NilpotentInverse.lean | Bridge: Ring.inverse = geom series |
| `grassmannGeomInverse_mul/_right` | NilpotentInverse.lean | PU normalization (S · S⁻¹ = 1) |
| `det_even_grassmannSmooth` | NilpotentInverse.lean | Determinant smoothness |
| `adjugate_even_grassmannSmooth` | NilpotentInverse.lean | Berezinian smoothness |
| `matInv_even_grassmannSmooth` | NilpotentInverse.lean | Berezinian smoothness |

---

## Key Definitions (Post-Audit, Verified Sound)

| Definition | Status |
|------------|--------|
| `BodyIntegral.SatisfiesChangeOfVar` | Fixed: requires Φ, hBij, signed det |
| `globalBerezinIntegral` | Fixed: bodyIntegral takes Set argument |
| `SuperPartitionOfUnity` | Fixed: `super_sum_eq_one` removed, now hypothesis `hSuperSum` |
| `GlobalIntegralForm.SatisfiesSuperCocycle` | Fixed: restricted to SuperTransition |
| `GlobalIntegralForm.compatible_body` | Fixed: signed det |

---

## References

- Witten, "Notes On Supermanifolds And Integration" (1209.2199)
- Rogers, "Supermanifolds" (2007), Chapter 11
- Bernstein-Leites, "Integral Forms And Stokes Formula" (1977)
