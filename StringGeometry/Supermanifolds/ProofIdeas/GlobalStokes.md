# Global Stokes Theorem — Proof Ideas

## Status: 3 honest sorrys remaining in GlobalStokes.lean

## Completed Infrastructure
- **partialEven_mul** — PROVEN in ExteriorDerivative.lean (product rule for ∂/∂xⁱ on Grassmann products)
- **SuperPartitionOfUnity fix** — DONE. Removed wrong `super_sum_eq_one` from structure (was vacuous: evaluated each ρ_α in its own chart). Now taken as hypothesis `hSuperSum` in GlobalStokes.lean using `composeEvalAt`. Proved by `normalizedPartition_sum_one` in PartitionOfUnity.lean.
- **SatisfiesChangeOfVar** — FIXED (no longer vacuous)
- **SatisfiesSuperCocycle** — FIXED (restricted to atlas transitions)
- **SuperDomainFunction Ring/Algebra** — DISCOVERED: full `Ring` and `Algebra ℝ` instances exist in SuperDomainAlgebra.lean. This means `mul_add`, `add_mul`, `Algebra.smul_mul_assoc`, `Algebra.mul_smul_comm` etc. are all available, greatly simplifying remaining proofs.

## Overview of What's Needed

Three theorems need proofs:
1. `berezin_change_of_variables` — super CoV reduces to body CoV
2. `globalBerezinIntegral_independent_proper` — PU independence (double-sum trick)
3. `global_super_stokes_no_boundary` — ∫_M dν = 0

---

## Next Step: Leibniz Rule for d₀ on Products

### Mathematical Statement

For a super function ρ and codim-1 form ν = Σᵢ fᵢ d̂xⁱ δ(dθ):

  d₀(ρ · ν) = ρ · d₀ν + Σᵢ (-1)ⁱ (∂ρ/∂xⁱ) · fᵢ [Dx Dθ]

### Proof Strategy (simplified by Ring/Algebra instances)

Since `SuperDomainFunction p q` has `Ring` and `Algebra ℝ` instances:

1. **LHS**: `d0Codim1(mulByFunction ρ ν)` coefficient at K is:
   `Σᵢ (-1)ⁱ • (partialEven i (ρ * νᵢ))_K`

2. **Apply `partialEven_mul`**: Each term becomes:
   `(-1)ⁱ • ((∂ᵢρ * νᵢ + ρ * ∂ᵢνᵢ)_K)`

3. **Distribute smul over add**: Using `smul_add`:
   `(-1)ⁱ • (∂ᵢρ * νᵢ)_K + (-1)ⁱ • (ρ * ∂ᵢνᵢ)_K`

4. **Split the sum**: `Finset.sum_add_distrib` gives two sums.

5. **Factor ρ from second sum**: Using `Algebra.smul_mul_assoc` and ring distributivity:
   `Σᵢ (-1)ⁱ • (ρ * ∂ᵢνᵢ)_K = (ρ * Σᵢ (-1)ⁱ • ∂ᵢνᵢ)_K`

   This requires showing ρ distributes through `Finset.sum` and `smul`.
   Key lemma needed: `(ρ * Finset.sum s f)_K = Finset.sum s (fun i => (ρ * f i)_K)`.
   This follows from `mul_sum` (available because SuperDomainFunction is a Ring) applied coefficient-wise.

6. The second sum is then `(mulByFunction ρ (d0Codim1 ν)).coefficient_K`.

### Lean Statement

```lean
/-- Wedge product of d₀ρ with a codim-1 form: Σᵢ (-1)ⁱ (∂ρ/∂xⁱ) · νᵢ [Dx Dθ] -/
noncomputable def wedgeEvenDeriv {p q : ℕ} (ρ : SuperDomainFunction p q)
    (ν : IntegralFormCodim1 p q) : IntegralForm p q :=
  ⟨⟨fun K => Finset.univ.sum fun (i : Fin p) =>
    ((-1 : ℝ) ^ (i : ℕ)) • ((partialEven i ρ) * ν.components i).coefficients K⟩⟩

theorem d0Codim1_mulByFunction {p q : ℕ} (ρ : SuperDomainFunction p q)
    (ν : IntegralFormCodim1 p q) :
    d0Codim1 (IntegralFormCodim1.mulByFunction ρ ν) =
    IntegralForm.mulByFunction ρ (d0Codim1 ν) + wedgeEvenDeriv ρ ν
```

### Key Helper Lemma: mul distributes through coefficient-level sum

Need to show that `IntegralForm.mulByFunction ρ (d0Codim1 ν)` at coefficient K equals
`Σᵢ (-1)ⁱ • (ρ * ∂ᵢνᵢ)_K`. Unfolding:

```
(ρ * d₀ν.coefficient)_K
= (ρ * ⟨fun K => Σᵢ (-1)ⁱ • (∂ᵢνᵢ)_K⟩)_K
```

This requires: `(ρ * f)_K` distributes over the definition of `f_K` as a sum.
Since multiplication at the SuperDomainFunction level distributes over the
Grassmann product formula, and the d₀ν coefficient involves a sum over i in
the SmoothFunction-valued coefficients, we need:

Option A: Work at the `SuperDomainFunction` level using `mul_sum` + `smul_mul_assoc`
from the Ring/Algebra instance, then unfold to coefficient K.

Option B: Define intermediate lemma `mul_coefficient_sum` showing
`(f * ⟨fun K => Σ_i g_i_K⟩).coefficients K = Σ_i (f * ⟨fun K => g_i_K⟩).coefficients K`.

Option A is cleaner.

---

## 1. `berezin_change_of_variables`

**Statement**: ∫_U φ*(ω) = ∫_V ω under super coordinate change φ.

**Proof strategy**:

Step 1: Unfold both sides. LHS = bodyIntegral (berezinIntegralOdd (pullbackProper φ ω).coefficient) U.
RHS = bodyIntegral (berezinIntegralOdd ω.coefficient) V.

Step 2: The pullback coefficient is `composeEvalAt(f, φ, x) * berezinianCarrierAt(φ, x)`.
The Berezin integral extracts the top θ-component (Finset.univ coefficient).

Step 3: **Key body-level reduction lemma** (needs to be proved):
At body level (θ=0), the top-θ component of `(f ∘ φ) · Ber(J_φ)` equals
`f_top(φ_body(x)) · det(J_body(x))`.

Why: At θ=0, the only surviving term in the Grassmann product `(f ∘ φ) · Ber`
at the Finset.univ component comes from:
- `(f ∘ φ)_univ · Ber_∅` (top of f times body of Ber)
- All other terms have `(f ∘ φ)_I · Ber_J` with I ∪ J = univ, I ≠ univ,
  so Ber_J with J ≠ ∅ contributes nilpotent corrections.

At body level, these nilpotent corrections vanish, giving:
`berezinIntegralOdd(pullback) at body = f_top(φ_body(x)) · Ber_body(x)`

And `Ber_body = det(A_body)/det(D_body)`. After the det(D) cancellation in Berezin
integration (θ-substitution θ'=Dθ produces 1/det(D) which cancels the det(D) in the
Berezinian denominator), we get `det(A_body) = det(body Jacobian)`.

Step 4: Apply `hChangeOfVar.change_of_var` with Φ = φ.bodyMap, matching pointwise.

**Infrastructure needed**:
- Lemma: `berezinIntegralOdd(pullbackProper φ ω)` at body = `(berezinIntegralOdd ω) ∘ φ.bodyMap · det(body Jacobian)`
- Top-θ component extraction from Grassmann product
- Berezinian body value = det(Jacobian)

**Available infrastructure**:
- `pullbackEvalAt` (Pullback.lean): computes the pullback at a body point
- `berezinianCarrierAt` (Pullback.lean): the Berezinian as Grassmann element
- `berezinianCarrierAt_grassmannSmooth` (Pullback.lean): smoothness of Ber coefficients
- `composeEvalAt` (SuperCompose.lean): super function composition at a point
- `BodyIntegral.SatisfiesChangeOfVar`: the classical CoV hypothesis (properly formulated)

---

## 2. `globalBerezinIntegral_independent_proper`

**Statement**: Σ_α ∫_{U_α} ρ_α · f_α = Σ_β ∫_{U_β} σ_β · f_β

**Proof (double-sum trick, Witten §3.1)**:

Step 1: Insert 1 = Σ_β σ_β (via `hSuperSum₂` hypothesis):
  Σ_α ∫_{U_α} ρ_α · f_α = Σ_{α,β} ∫_{U_α} ρ_α · σ_β · f_α

Step 2: On U_α ∩ U_β, use super cocycle (SatisfiesSuperCocycle):
  f_α(x) = pullbackEvalAt(T_{βα}, f_β, x) = (f_β ∘ T)(x) · Ber(J)(x)

Step 3: Change of variables (theorem 1 above):
  ∫_{U_α} (ρ_α · σ_β) · f_α = ∫_{U_β} (ρ_α · σ_β) · f_β

Step 4: Reorder sum and use `hSuperSum₁`:
  = Σ_β ∫_{U_β} (Σ_α ρ_α) · σ_β · f_β
  = Σ_β ∫_{U_β} 1 · σ_β · f_β
  = Σ_β ∫_{U_β} σ_β · f_β

**Requirements**:
- `berezin_change_of_variables` (theorem 1)
- `SatisfiesSuperCocycle` on the GlobalIntegralForm ✓
- `hSuperSum₁`, `hSuperSum₂` hypotheses ✓ (added to theorem signature)
- Linearity of bodyIntegral ✓

---

## 3. `global_super_stokes_no_boundary`

**Statement**: ∫_M dν = 0 for closed M.

**Proof outline**:

Step 1: Expand: ∫_M dν = Σ_α ∫_{U_α} ρ_α · (dν)_α

Step 2: Leibniz rule for d₀ on products (using `d0Codim1_mulByFunction`):
  ρ_α · d₀(ν_α) = d₀(ρ_α · ν_α) - Σᵢ (-1)ⁱ (∂ρ_α/∂xⁱ) · (ν_α)_i

Step 3: Each ∫ d₀(ρ_α · ν_α) = 0:
  - ρ_α · ν_α has compact support in U_α (ρ_α vanishes on ∂U_α)
  - By d0_is_divergence: d₀(ρ_α · ν_α) = div(signed components)
  - By hDivThm: ∫_U div(compactly supported F) = 0

Step 4: Correction terms cancel:
  Σ_α Σᵢ (-1)ⁱ ∫ (∂ρ_α/∂xⁱ) · (ν_α)_i
  = Σᵢ (-1)ⁱ ∫ (∂(Σ_α ρ_α)/∂xⁱ) · fᵢ     (by linearity of ∂/∂xⁱ)
  = Σᵢ (-1)ⁱ ∫ (∂1/∂xⁱ) · fᵢ                (by hSuperSum: Σ_α ρ_α = 1)
  = 0                                          (derivative of constant = 0)

Step 5: Combining: ∫_M dν = Σ_α [0 - correction_α] = 0 - 0 = 0.

**Infrastructure needed**:
(a) **d0Codim1_mulByFunction** (Leibniz rule) — IN PROGRESS
(b) **Compact support of ρ_α · ν_α** — from `support_subset` of the PU
(c) **Partition derivative identity**: ∂(Σ_α ρ_α)/∂xⁱ = 0
    - Follows from `hSuperSum` (Σ ρ_α = 1) + `partialEven` of constant = 0
(d) **Connection**: d₀(ρ_α · ν_α) is divergence of compactly supported vector field

---

## Key Discovery: SuperDomainFunction Algebra Structure

`SuperDomainFunction p q` has full `Ring` and `Algebra ℝ` instances
(SuperDomainAlgebra.lean:658 and :759). This provides:
- `mul_add`, `add_mul` (distributivity)
- `mul_assoc` (associativity)
- `Algebra.smul_mul_assoc`, `Algebra.mul_smul_comm` (scalar-mult compatibility)
- `mul_sum`, `Finset.sum_mul` (distribution over sums, from Semiring)

These bypass the need for coefficient-level gymnastics in many proofs.

---

## Berezinian Infrastructure Usage

The Integration/ files use the following from the Berezinian infrastructure:

1. **BerezinianMul.lean** (`ber_mul`): Used in `berezinian_cocycle_full`
   via `berezinian_cocycle_from_chain_rule`.
2. **Berezinian.lean** (`SuperMatrix.ber`, `berezinianAt`): Used in Pullback.lean
   for `pullbackEvalAt`.
3. **SuperChainRule.lean** (`berezinian_cocycle_from_chain_rule`): Berezinian cocycle.
4. **NilpotentInverse.lean** (geometric series, `grassmannGeomInverse`): PU normalization.
5. **GrassmannSmooth.lean** (`grassmannSmooth` predicate): Pullback smoothness.

---

## References

- Witten, "Notes On Supermanifolds And Integration" (1209.2199), §3.1-3.5
- Rogers, "Supermanifolds" (2007), Chapter 11
- Bernstein-Leites, "Integral Forms And The Stokes Formula On Supermanifolds" (1977)
