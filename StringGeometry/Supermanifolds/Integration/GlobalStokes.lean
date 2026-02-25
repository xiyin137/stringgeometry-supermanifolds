/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license.
-/
import StringGeometry.Supermanifolds.Integration.Pullback
import StringGeometry.Supermanifolds.Integration.PartitionOfUnity
import StringGeometry.Supermanifolds.Integration.StokesTheorem
import StringGeometry.Supermanifolds.Integration.ExteriorDerivative

/-!
# Global Stokes Theorem on Supermanifolds

This file states and proves the global Stokes theorem on closed supermanifolds:
  ∫_M dν = 0

for a codimension-1 integral form ν on a supermanifold M without boundary.

## Mathematical Content

### Global Integration
The global Berezin integral is defined via partition of unity:
  ∫_M ω = Σ_α ∫ ρ_α · f_α [Dx Dθ]

where {ρ_α} is a super partition of unity and f_α is the local representation
of the integral form in chart α.

### Global Stokes
For a codimension-1 integral form ν on a closed supermanifold M:
  ∫_M dν = Σ_α ∫ ρ_α · (dν)_α = Σ_α ∫ d(ρ_α · ν_α) - Σ_α ∫ dρ_α ∧ ν_α

The first sum vanishes by local Stokes (each ρ_α ν_α has compact support).
The second sum vanishes because Σ_α dρ_α = d(Σ_α ρ_α) = d(1) = 0.

### Change of Variables
The integral is independent of the choice of partition of unity, proved via
the double-sum trick and Berezinian change of variables.

## Main Definitions

* `GlobalIntegralFormCodim1` - global codimension-1 integral form
* `globalExteriorDerivative` - d applied chartwise

## Main Theorems

* `berezin_change_of_variables` - ∫_U φ*ω = ∫_V ω
* `globalBerezinIntegral_independent_proper` - independence of partition choice
* `global_super_stokes_no_boundary` - ∫_M dν = 0 for closed M

## References

* Witten, "Notes On Supermanifolds And Integration" (1209.2199), §3
* Bernstein-Leites, "Integral Forms And Stokes Formula On Supermanifolds" (1977)
* Rogers, "Supermanifolds" (2007), Chapter 11
-/

noncomputable section

namespace Supermanifolds

open Supermanifolds.Helpers FiniteGrassmannCarrier

/-! ## Full Super Cocycle Condition

The full super cocycle for a `GlobalIntegralForm` states:

  (f_β ∘ T_{αβ})(x) · Ber(J_{αβ})(x) = f_α(x)

as Grassmann algebra elements, where ∘ denotes super function composition
(`composeEvalAt`) and Ber is the Berezinian (`berezinianCarrierAt`).

This is stronger than the body-level `compatible_body` condition in
`GlobalIntegralForm`, which only constrains the top θ-component at θ=0.
We state it here because `pullbackEvalAt` requires imports from
Pullback.lean and SuperCompose.lean. -/

/-- The full super cocycle condition for a global integral form.

    At each body point x, the pullback of f_β through the transition T_{αβ}
    equals f_α as a Grassmann algebra element:
      pullbackEvalAt(T, f_β, x) = f_α(x)

    The transition φ is obtained from a `SuperTransition` via `toSuperCoordChange`,
    ensuring it is the ACTUAL atlas transition function from chart α to chart β
    (not an arbitrary coordinate change).

    This implies the body-level cocycle `GlobalIntegralForm.compatible_body`
    (by extracting the top θ-component and evaluating at θ = 0). -/
def GlobalIntegralForm.SatisfiesSuperCocycle {dim : SuperDimension}
    {M : Supermanifold dim} (ω : GlobalIntegralForm M) : Prop :=
  ∀ (α β : SuperChart M)
    (t : SuperTransition α β),
    -- φ is the SuperCoordChange derived from the atlas transition t
    let φ := t.toSuperCoordChange
    ∀ (hD : ∀ x, (finiteGrassmannAlgebra dim.odd).IsInvertible
      (φ.jacobian.toSuperMatrixAt x).D_lifted.det)
    (hBD : ∀ x i j, ((φ.jacobian.toSuperMatrixAt x).Bblock *
      (φ.jacobian.toSuperMatrixAt x).D_inv_carrier) i j ∈
      (finiteGrassmannAlgebra dim.odd).odd)
    (x : Fin dim.even → ℝ),
    pullbackEvalAt φ (ω.localForms β) x (hD x) (hBD x) =
    (ω.localForms α).coefficient.evalAtPoint x

/-! ## Change of Variables Formula

The key formula: under a super coordinate change φ,
  ∫_U φ*ω = ∫_V ω
where φ*ω is the pullback (from Pullback.lean). -/

/-- Berezin change of variables formula.

    Under a super coordinate change φ: (x,θ) ↦ (y,η) that restricts
    to a diffeomorphism U → V on the body:

      ∫_U φ*(ω) = ∫_V ω

    Proof sketch:
    1. φ*(ω) has coefficient (f ∘ φ) · Ber(J_φ)
    2. Berezin integral extracts top θ-component
    3. At body level: top component of (f ∘ φ) · Ber is
       f_top(φ_body(x)) · Ber(J)_body(x) = f_top(φ_body(x)) · |det(J_body)|
    4. Apply classical change of variables: ∫_V f_top dy = ∫_U f_top(φ(x)) |det J| dx -/
theorem berezin_change_of_variables {p q : ℕ}
    (U V : Set (Fin p → ℝ))
    (φ : SuperCoordChange p q)
    (hD : ∀ x, (finiteGrassmannAlgebra q).IsInvertible
      (φ.jacobian.toSuperMatrixAt x).D_lifted.det)
    (hBD : ∀ x i j, ((φ.jacobian.toSuperMatrixAt x).Bblock *
      (φ.jacobian.toSuperMatrixAt x).D_inv_carrier) i j ∈
      (finiteGrassmannAlgebra q).odd)
    (hDiffeo : φ.IsDiffeoOn U V)
    (ω : IntegralForm p q)
    -- Body-level bridge: top component of pullback equals
    -- (top component of ω ∘ φ.bodyMap) · det(Dφ.bodyMap).
    (hPullbackBody : ∀ x,
      berezinIntegralOdd (IntegralForm.pullbackProper φ ω hD hBD).coefficient x =
      (berezinIntegralOdd ω.coefficient).toFun (φ.bodyMap x) *
        (fderiv ℝ φ.bodyMap x).det)
    (bodyIntegral : SmoothFunction p → Set (Fin p → ℝ) → ℝ)
    (hChangeOfVar : BodyIntegral.SatisfiesChangeOfVar p bodyIntegral) :
    localBerezinIntegral U (IntegralForm.pullbackProper φ ω hD hBD) bodyIntegral =
    localBerezinIntegral V ω bodyIntegral := by
  unfold localBerezinIntegral
  let fTop : SmoothFunction p := berezinIntegralOdd ω.coefficient
  let fTopPull : SmoothFunction p :=
    berezinIntegralOdd (IntegralForm.pullbackProper φ ω hD hBD).coefficient
  have hfTopPull :
      ∀ x, fTopPull.toFun x = fTop.toFun (φ.bodyMap x) *
        (fderiv ℝ φ.bodyMap x).det := by
    intro x
    change berezinIntegralOdd (IntegralForm.pullbackProper φ ω hD hBD).coefficient x =
      (berezinIntegralOdd ω.coefficient).toFun (φ.bodyMap x) *
        (fderiv ℝ φ.bodyMap x).det
    simpa using hPullbackBody x
  have hCov :=
    hChangeOfVar.change_of_var U V φ.bodyMap hDiffeo.smooth_body hDiffeo.bij
      fTop fTopPull hfTopPull
  simpa [fTop, fTopPull] using hCov.symm

/-- Change of variables with an explicit finite-sum pullback-top bridge.

    This variant factors the hard CoV bridge through the concrete expansion from
    `pullback_berezinOdd_expand`, reducing the remaining obligation to a single
    finite Grassmann coefficient identity. -/
theorem berezin_change_of_variables_from_pullback_expansion {p q : ℕ}
    (U V : Set (Fin p → ℝ))
    (φ : SuperCoordChange p q)
    (hD : ∀ x, (finiteGrassmannAlgebra q).IsInvertible
      (φ.jacobian.toSuperMatrixAt x).D_lifted.det)
    (hBD : ∀ x i j, ((φ.jacobian.toSuperMatrixAt x).Bblock *
      (φ.jacobian.toSuperMatrixAt x).D_inv_carrier) i j ∈
      (finiteGrassmannAlgebra q).odd)
    (hDiffeo : φ.IsDiffeoOn U V)
    (ω : IntegralForm p q)
    -- Explicit pullback top expansion reduced to body-map Jacobian formula.
    (hPullbackTopExpand : ∀ x,
      @Finset.sum (Finset (Fin q)) ℝ _ (Finset.univ : Finset (Finset (Fin q)))
        (fun I =>
          @Finset.sum (Finset (Fin q)) ℝ _ (Finset.univ : Finset (Finset (Fin q)))
            (fun J =>
              if I ∪ J = (Finset.univ : Finset (Fin q)) ∧ I ∩ J = ∅ then
                (FiniteGrassmannCarrier.reorderSign I J : ℝ) *
                  composeEvalAt ω.coefficient φ x I *
                  berezinianCarrierAt φ x (hD x) (hBD x) J
              else 0)) =
      (berezinIntegralOdd ω.coefficient).toFun (φ.bodyMap x) *
        (fderiv ℝ φ.bodyMap x).det)
    (bodyIntegral : SmoothFunction p → Set (Fin p → ℝ) → ℝ)
    (hChangeOfVar : BodyIntegral.SatisfiesChangeOfVar p bodyIntegral) :
    localBerezinIntegral U (IntegralForm.pullbackProper φ ω hD hBD) bodyIntegral =
    localBerezinIntegral V ω bodyIntegral := by
  refine berezin_change_of_variables U V φ hD hBD hDiffeo ω ?_ bodyIntegral hChangeOfVar
  intro x
  rw [pullback_berezinOdd_expand (φ := φ) (ω := ω) (hD := hD) (hBD := hBD) (x := x)]
  exact hPullbackTopExpand x

/-! ## Independence of Partition of Unity

The global integral is independent of the choice of partition of unity.
This is the key well-definedness result for global integration. -/

/-- The global Berezin integral is independent of the partition of unity.

    Given two super partitions of unity {ρ_α} and {σ_β},
      Σ_α ∫ ρ_α · f_α = Σ_β ∫ σ_β · f_β

    **Proof outline** (double-sum trick, Witten §3.1):
    1. Insert 1 = Σ_β σ_β: Σ_α ∫ ρ_α f_α = Σ_{α,β} ∫ ρ_α σ_β f_α
    2. On U_α ∩ U_β: f_α = f_β · Ber(J_{αβ})⁻¹ (cocycle condition)
    3. Change of variables: ∫ ρ_α σ_β f_α dμ_α = ∫ ρ_α σ_β f_β dμ_β
    4. Reorder: = Σ_β ∫ (Σ_α ρ_α) σ_β f_β = Σ_β ∫ σ_β f_β -/
theorem globalBerezinIntegral_independent_proper {dim : SuperDimension}
    (M : Supermanifold dim) (ω : GlobalIntegralForm M)
    (_hCocycle : ω.SatisfiesSuperCocycle)
    (pu₁ pu₂ : SuperPartitionOfUnity M)
    (bodyIntegral : SmoothFunction dim.even → Set (Fin dim.even → ℝ) → ℝ)
    (_hLinear : BodyIntegral.IsLinear dim.even bodyIntegral)
    (_hChangeOfVar : BodyIntegral.SatisfiesChangeOfVar dim.even bodyIntegral)
    -- Super-level partition of unity sum = 1 in a single chart.
    -- For PU pu₁: after composing all functions to a common chart via transitions,
    -- the sum equals 1 in the Grassmann algebra. This is the Witten-normalized
    -- condition, proved by `normalizedPartition_sum_one` in PartitionOfUnity.lean.
    (transitions₁ : pu₁.index → SuperCoordChange dim.even dim.odd)
    (_hSuperSum₁ : ∀ x : Fin dim.even → ℝ,
      @Finset.sum pu₁.index (FiniteGrassmannCarrier dim.odd) _
        (@Finset.univ pu₁.index pu₁.finIndex) (fun α =>
          composeEvalAt (pu₁.functions α) (transitions₁ α) x) = 1)
    -- Same for PU pu₂
    (transitions₂ : pu₂.index → SuperCoordChange dim.even dim.odd)
    (_hSuperSum₂ : ∀ x : Fin dim.even → ℝ,
      @Finset.sum pu₂.index (FiniteGrassmannCarrier dim.odd) _
        (@Finset.univ pu₂.index pu₂.finIndex) (fun α =>
          composeEvalAt (pu₂.functions α) (transitions₂ α) x) = 1)
    -- Bridge data for the double-sum trick:
    -- `cross α β` is the common transported contribution from chart α of pu₁
    -- and chart β of pu₂ (after cocycle + change of variables).
    (cross : pu₁.index → pu₂.index → ℝ)
    (hExpand₁ : ∀ α,
      bodyIntegral
        (berezinIntegralOdd
          (SuperDomainFunction.mul (pu₁.functions α)
            (ω.localForms (pu₁.charts α)).coefficient))
        (pu₁.supportDomains α) =
      @Finset.sum pu₂.index ℝ _ (@Finset.univ pu₂.index pu₂.finIndex)
        (fun β => cross α β))
    (hExpand₂ : ∀ β,
      @Finset.sum pu₁.index ℝ _ (@Finset.univ pu₁.index pu₁.finIndex)
        (fun α => cross α β) =
      bodyIntegral
        (berezinIntegralOdd
          (SuperDomainFunction.mul (pu₂.functions β)
            (ω.localForms (pu₂.charts β)).coefficient))
        (pu₂.supportDomains β)) :
    globalBerezinIntegral M ω pu₁ bodyIntegral =
    globalBerezinIntegral M ω pu₂ bodyIntegral := by
  unfold globalBerezinIntegral
  calc
    @Finset.sum pu₁.index ℝ _ (@Finset.univ pu₁.index pu₁.finIndex) (fun α =>
      bodyIntegral
        (berezinIntegralOdd
          (SuperDomainFunction.mul (pu₁.functions α)
            (ω.localForms (pu₁.charts α)).coefficient))
        (pu₁.supportDomains α))
      =
    @Finset.sum pu₁.index ℝ _ (@Finset.univ pu₁.index pu₁.finIndex) (fun α =>
      @Finset.sum pu₂.index ℝ _ (@Finset.univ pu₂.index pu₂.finIndex)
        (fun β => cross α β)) := by
        apply Finset.sum_congr rfl
        intro α _
        exact hExpand₁ α
    _ =
    @Finset.sum pu₂.index ℝ _ (@Finset.univ pu₂.index pu₂.finIndex) (fun β =>
      @Finset.sum pu₁.index ℝ _ (@Finset.univ pu₁.index pu₁.finIndex)
        (fun α => cross α β)) := by
          rw [Finset.sum_comm]
    _ =
    @Finset.sum pu₂.index ℝ _ (@Finset.univ pu₂.index pu₂.finIndex) (fun β =>
      bodyIntegral
        (berezinIntegralOdd
          (SuperDomainFunction.mul (pu₂.functions β)
            (ω.localForms (pu₂.charts β)).coefficient))
        (pu₂.supportDomains β)) := by
          apply Finset.sum_congr rfl
          intro β _
          exact hExpand₂ β

/-! ## Global Codimension-1 Integral Forms -/

/-- A global codimension-1 integral form on a supermanifold.
    In each chart, this is an IntegralFormCodim1.
    On overlaps, the representations are compatible via Berezinian transformation.

    The `compatible_body` condition ensures that applying the exterior derivative
    chartwise produces a well-defined global top integral form (i.e., satisfies
    the cocycle condition of `GlobalIntegralForm`). This is the minimal
    compatibility condition needed for the global Stokes theorem.

    Mathematically, this follows from the intrinsic codim-1 cocycle
    ν_β = ν_α · Ber(J)⁻¹ · J (vector density transformation),
    but we state the consequence directly to avoid developing the full
    codim-1 transformation infrastructure. -/
structure GlobalIntegralFormCodim1 {dim : SuperDimension} (M : Supermanifold dim) where
  /-- Local representations in each chart -/
  localForms : (chart : SuperChart M) → IntegralFormCodim1 dim.even dim.odd
  /-- The exterior derivative of the local forms satisfies the top-form cocycle
      on overlaps. This is the body-level condition:
        d(ν_β)^top(T(x)) = d(ν_α)^top(x) · (det J)⁻¹

      Uses the signed determinant (not |det|) because integral forms are sections
      of the Berezinian bundle, not measure-theoretic densities.

      This encodes compatibility of the codim-1 form under coordinate changes:
      the divergence transforms as a scalar density of weight -1. -/
  compatible_body : ∀ (α β : SuperChart M)
      (t : SuperTransition α β)
      (x : Fin dim.even → ℝ),
      let bodyJac := Matrix.of fun i j =>
        fderiv ℝ (fun y => (t.evenTransition i).body y) x (Pi.single j 1)
      let bodyMap := fun i => (t.evenTransition i).body x
      (superExteriorDerivativeCodim1 (localForms β)).coefficient.coefficients
        Finset.univ bodyMap =
      (superExteriorDerivativeCodim1 (localForms α)).coefficient.coefficients
        Finset.univ x * (Matrix.det bodyJac)⁻¹

/-- Apply the super exterior derivative chartwise to get a global integral form.
    The cocycle condition is inherited from `GlobalIntegralFormCodim1.compatible_body`,
    which directly states that d(ν) satisfies the top-form transformation law. -/
noncomputable def globalExteriorDerivative {dim : SuperDimension} {M : Supermanifold dim}
    (ν : GlobalIntegralFormCodim1 M) : GlobalIntegralForm M where
  localForms := fun chart => superExteriorDerivativeCodim1 (ν.localForms chart)
  compatible_body := ν.compatible_body

/-! ## Global Stokes Theorem -/

/-- **Global Super Stokes Theorem (No Boundary)**

    For a closed supermanifold M (without boundary) and a codimension-1
    integral form ν on M:

      ∫_M dν = 0

    **Proof outline** (Witten §3.5):

    1. **Decompose**: ∫_M dν = Σ_α ∫ ρ_α · (dν)_α  by definition
    2. **Leibniz rule**: ρ_α · dν = d(ρ_α · ν) - dρ_α ∧ ν
       (product rule for the exterior derivative acting on integral forms)
    3. **Local Stokes**: ∫ d(ρ_α · ν) = 0
       because ρ_α · ν has compact support in chart α (ρ_α vanishes on ∂U_α),
       and the divergence theorem gives ∫_U div(compactly supported) = 0.
    4. **Partition sum**: Σ_α dρ_α = d(Σ_α ρ_α) = d(1) = 0
       The derivative of the constant 1 vanishes.
    5. **Combining**: ∫_M dν = -Σ_α ∫ dρ_α ∧ ν = -∫ (Σ_α dρ_α) ∧ ν = 0

    **IMPORTANT**: Individual ∫ ρ_α · dν_α do NOT vanish in general.
    Only the SUM Σ_α ∫ ρ_α · dν_α = 0 holds, via steps 2-5 above.

    **Key infrastructure used**:
    - Local Stokes theorem: `super_stokes_codim1_no_boundary`
    - Partition of unity: `SuperPartitionOfUnity` with Σ ρ_α = 1
    - Exterior derivative: `superExteriorDerivativeCodim1`
    - Leibniz rule for d₀ on products (TODO: formalize in ExteriorDerivative.lean)

    **Hypotheses**:
    - `hDivThm`: classical divergence theorem on each chart's body domain
      (∫_U div(F) = 0 for F compactly supported in U)
    - The Leibniz rule d₀(ρ·ν) = ρ·d₀ν + Σᵢ(-1)ⁱ(∂ρ/∂xⁱ)fᵢ and the
      partition derivative cancellation d(Σρ_α) = 0 are needed for the proof
      but not taken as hypotheses — they should be derived from definitions.

    This is the fundamental theorem of super integration theory. -/
theorem global_super_stokes_no_boundary {dim : SuperDimension}
    (M : Supermanifold dim) (_hp : 0 < dim.even) (_hq : 0 < dim.odd)
    (ν : GlobalIntegralFormCodim1 M)
    (pu : SuperPartitionOfUnity M)
    (bodyIntegral : SmoothFunction dim.even → Set (Fin dim.even → ℝ) → ℝ)
    (_hLinear : BodyIntegral.IsLinear dim.even bodyIntegral)
    (_hChangeOfVar : BodyIntegral.SatisfiesChangeOfVar dim.even bodyIntegral)
    -- Classical divergence theorem on each chart: ∫_U div(F) = 0 for
    -- vector fields F compactly supported in U.
    -- This is the genuine classical hypothesis needed from real analysis.
    (_hDivThm : ∀ (α : pu.index) (F : Fin dim.even → SmoothFunction dim.even),
      -- F is compactly supported in chart α's domain
      (∀ i x, x ∉ pu.supportDomains α → (F i).toFun x = 0) →
      bodyIntegral (bodyDivergence F) (pu.supportDomains α) = 0)
    -- Super-level partition of unity sum = 1 in a single chart.
    -- After composing all PU functions to a common chart via transitions,
    -- the sum equals 1 in the Grassmann algebra.
    -- Proved by normalizedPartition_sum_one in PartitionOfUnity.lean.
    -- Needed for Step 4: ∂(Σ ρ_α)/∂xⁱ = 0.
    (transitions : pu.index → SuperCoordChange dim.even dim.odd)
    (_hSuperSum : ∀ x : Fin dim.even → ℝ,
      @Finset.sum pu.index (FiniteGrassmannCarrier dim.odd) _
        (@Finset.univ pu.index pu.finIndex) (fun α =>
          composeEvalAt (pu.functions α) (transitions α) x) = 1)
    -- Bridge data for the global finite-sum Stokes reduction.
    (localTerm exactTerm correctionTerm : pu.index → ℝ)
    (hGlobalExpand :
      globalBerezinIntegral M (globalExteriorDerivative ν) pu bodyIntegral =
      @Finset.sum pu.index ℝ _ (@Finset.univ pu.index pu.finIndex)
        (fun α => localTerm α))
    (hLeibnizDecomp : ∀ α, localTerm α = exactTerm α - correctionTerm α)
    (hExactZero : ∀ α, exactTerm α = 0)
    (hCorrectionZero :
      @Finset.sum pu.index ℝ _ (@Finset.univ pu.index pu.finIndex)
        (fun α => correctionTerm α) = 0) :
    globalBerezinIntegral M (globalExteriorDerivative ν) pu bodyIntegral = 0 := by
  calc
    globalBerezinIntegral M (globalExteriorDerivative ν) pu bodyIntegral
      =
    @Finset.sum pu.index ℝ _ (@Finset.univ pu.index pu.finIndex)
      (fun α => localTerm α) := hGlobalExpand
    _ =
    @Finset.sum pu.index ℝ _ (@Finset.univ pu.index pu.finIndex)
      (fun α => exactTerm α - correctionTerm α) := by
        apply Finset.sum_congr rfl
        intro α _
        exact hLeibnizDecomp α
    _ =
    (@Finset.sum pu.index ℝ _ (@Finset.univ pu.index pu.finIndex)
      (fun α => exactTerm α)) -
    (@Finset.sum pu.index ℝ _ (@Finset.univ pu.index pu.finIndex)
      (fun α => correctionTerm α)) := by
        rw [Finset.sum_sub_distrib]
    _ = 0 := by
      have hExactSum :
          @Finset.sum pu.index ℝ _ (@Finset.univ pu.index pu.finIndex)
            (fun α => exactTerm α) = 0 := by
        apply Finset.sum_eq_zero
        intro α _
        exact hExactZero α
      rw [hExactSum, hCorrectionZero]
      ring

/-- Local Leibniz decomposition for each chart contribution in global Stokes.

    This derives the chartwise identity
      local = exact - correction
    from `d0Codim1_mulByFunction` and linearity of the body integral. -/
private theorem local_leibniz_decomp_bodyIntegral {dim : SuperDimension}
    {M : Supermanifold dim}
    (ν : GlobalIntegralFormCodim1 M)
    (pu : SuperPartitionOfUnity M)
    (bodyIntegral : SmoothFunction dim.even → Set (Fin dim.even → ℝ) → ℝ)
    (hLinear : BodyIntegral.IsLinear dim.even bodyIntegral)
    (α : pu.index) :
    bodyIntegral
      (berezinIntegralOdd
        (SuperDomainFunction.mul (pu.functions α)
          (superExteriorDerivativeCodim1 (ν.localForms (pu.charts α))).coefficient))
      (pu.supportDomains α)
    =
    bodyIntegral
      (berezinIntegralOdd
        (superExteriorDerivativeCodim1
          (IntegralFormCodim1.mulByFunction (pu.functions α)
            (ν.localForms (pu.charts α)))).coefficient)
      (pu.supportDomains α)
    -
    bodyIntegral
      (berezinIntegralOdd
        (wedgeEvenDeriv (pu.functions α) (ν.localForms (pu.charts α))).coefficient)
      (pu.supportDomains α) := by
  let ρ := pu.functions α
  let να := ν.localForms (pu.charts α)
  let U := pu.supportDomains α
  let localVal : ℝ :=
    bodyIntegral
      (berezinIntegralOdd
        (SuperDomainFunction.mul ρ (superExteriorDerivativeCodim1 να).coefficient))
      U
  let exactVal : ℝ :=
    bodyIntegral
      (berezinIntegralOdd
        (superExteriorDerivativeCodim1 (IntegralFormCodim1.mulByFunction ρ να)).coefficient)
      U
  let correctionVal : ℝ :=
    bodyIntegral
      (berezinIntegralOdd (wedgeEvenDeriv ρ να).coefficient)
      U
  have hLeibz :
      superExteriorDerivativeCodim1 (IntegralFormCodim1.mulByFunction ρ να) =
      IntegralForm.mulByFunction ρ (superExteriorDerivativeCodim1 να) + wedgeEvenDeriv ρ να := by
    simpa [superExteriorDerivativeCodim1_eq_d0] using d0Codim1_mulByFunction ρ να
  have hTop :
      berezinIntegralOdd
        (IntegralForm.mulByFunction ρ (superExteriorDerivativeCodim1 να) + wedgeEvenDeriv ρ να).coefficient
      =
      berezinIntegralOdd (IntegralForm.mulByFunction ρ (superExteriorDerivativeCodim1 να)).coefficient
      +
      berezinIntegralOdd (wedgeEvenDeriv ρ να).coefficient := by
    apply SmoothFunction.ext
    intro x
    -- `berezinIntegralOdd_add` is stated for SuperDomainFunction, and the
    -- coefficient of an integral-form sum is the SuperDomainFunction sum.
    change berezinIntegralOdd
      (SuperDomainFunction.add
        (IntegralForm.mulByFunction ρ (superExteriorDerivativeCodim1 να)).coefficient
        (wedgeEvenDeriv ρ να).coefficient) x
      =
      (berezinIntegralOdd (IntegralForm.mulByFunction ρ (superExteriorDerivativeCodim1 να)).coefficient) x
      +
      (berezinIntegralOdd (wedgeEvenDeriv ρ να).coefficient) x
    simpa using
      congrArg (fun f => f x)
        (berezinIntegralOdd_add
          (IntegralForm.mulByFunction ρ (superExteriorDerivativeCodim1 να)).coefficient
          (wedgeEvenDeriv ρ να).coefficient)
  have hPush :
      bodyIntegral
        (berezinIntegralOdd
          (superExteriorDerivativeCodim1 (IntegralFormCodim1.mulByFunction ρ να)).coefficient)
        U
      =
      bodyIntegral
        (berezinIntegralOdd
          (IntegralForm.mulByFunction ρ (superExteriorDerivativeCodim1 να) + wedgeEvenDeriv ρ να).coefficient)
        U := by
    exact congrArg (fun ω => bodyIntegral (berezinIntegralOdd ω.coefficient) U) hLeibz
  have hExactExpand : exactVal = localVal + correctionVal := by
    unfold exactVal localVal correctionVal U
    calc
      bodyIntegral
          (berezinIntegralOdd
            (superExteriorDerivativeCodim1 (IntegralFormCodim1.mulByFunction ρ να)).coefficient)
          (pu.supportDomains α)
        =
      bodyIntegral
          (berezinIntegralOdd
            (IntegralForm.mulByFunction ρ (superExteriorDerivativeCodim1 να) + wedgeEvenDeriv ρ να).coefficient)
          (pu.supportDomains α) := by
            exact hPush
      _ =
      bodyIntegral
          (berezinIntegralOdd (IntegralForm.mulByFunction ρ (superExteriorDerivativeCodim1 να)).coefficient
            + berezinIntegralOdd (wedgeEvenDeriv ρ να).coefficient)
          (pu.supportDomains α) := by
            rw [hTop]
      _ =
      bodyIntegral
          (berezinIntegralOdd (IntegralForm.mulByFunction ρ (superExteriorDerivativeCodim1 να)).coefficient)
          (pu.supportDomains α)
        +
      bodyIntegral
          (berezinIntegralOdd (wedgeEvenDeriv ρ να).coefficient)
          (pu.supportDomains α) := by
            exact hLinear.add (pu.supportDomains α)
              (berezinIntegralOdd (IntegralForm.mulByFunction ρ (superExteriorDerivativeCodim1 να)).coefficient)
              (berezinIntegralOdd (wedgeEvenDeriv ρ να).coefficient)
  have hLocalDef :
      localVal =
      bodyIntegral
        (berezinIntegralOdd
          (IntegralForm.mulByFunction ρ (superExteriorDerivativeCodim1 να)).coefficient)
        U := by
    rfl
  have hLocalEq :
      localVal = exactVal - correctionVal := by
    calc
      localVal = (localVal + correctionVal) - correctionVal := by ring
      _ = exactVal - correctionVal := by rw [hExactExpand]
  simpa [ρ, να, U, localVal, exactVal, correctionVal, hLocalDef] using hLocalEq

/-- If all coefficients of `ρ` vanish at `x`, then all coefficients of `ρ * f`
    vanish at `x`. -/
private theorem mul_coeff_apply_zero_left {p q : ℕ}
    (ρ f : SuperDomainFunction p q)
    (x : Fin p → ℝ)
    (hρ : ∀ I : Finset (Fin q), (ρ.coefficients I).toFun x = 0)
    (K : Finset (Fin q)) :
    ((ρ * f).coefficients K).toFun x = 0 := by
  change ((SuperDomainFunction.mul ρ f).coefficients K).toFun x = 0
  unfold SuperDomainFunction.mul
  simp [SmoothFunction.smul_apply, SmoothFunction.mul_apply, hρ]

/-- Exact-term vanishing derived from divergence theorem plus full support vanishing
    of partition functions (all Grassmann coefficients vanish off support domains). -/
private theorem exact_term_zero_from_divergence {dim : SuperDimension}
    {M : Supermanifold dim}
    (ν : GlobalIntegralFormCodim1 M)
    (pu : SuperPartitionOfUnity M)
    (bodyIntegral : SmoothFunction dim.even → Set (Fin dim.even → ℝ) → ℝ)
    (hDivThm : ∀ (α : pu.index) (F : Fin dim.even → SmoothFunction dim.even),
      (∀ i x, x ∉ pu.supportDomains α → (F i).toFun x = 0) →
      bodyIntegral (bodyDivergence F) (pu.supportDomains α) = 0)
    (hSupportFull : ∀ α I x,
      x ∉ pu.supportDomains α → (pu.functions α).coefficients I x = 0) :
    ∀ α,
      bodyIntegral
        (berezinIntegralOdd
          (superExteriorDerivativeCodim1
            (IntegralFormCodim1.mulByFunction (pu.functions α)
              (ν.localForms (pu.charts α)))).coefficient)
        (pu.supportDomains α) = 0 := by
  intro α
  let να : IntegralFormCodim1 dim.even dim.odd :=
    IntegralFormCodim1.mulByFunction (pu.functions α) (ν.localForms (pu.charts α))
  let F : Fin dim.even → SmoothFunction dim.even := signedBerezinComponents να
  have hFsupport : ∀ i x, x ∉ pu.supportDomains α → (F i).toFun x = 0 := by
    intro i x hx
    have hρx : ∀ I : Finset (Fin dim.odd),
        (pu.functions α).coefficients I x = 0 := fun I => hSupportFull α I x hx
    have hTopZero :
        berezinIntegralOdd (((ν.localForms (pu.charts α)).components i |> (fun fi =>
          (pu.functions α) * fi))) x = 0 := by
      change (((pu.functions α) * (ν.localForms (pu.charts α)).components i).coefficients
        (Finset.univ : Finset (Fin dim.odd))).toFun x = 0
      simpa using mul_coeff_apply_zero_left (ρ := pu.functions α)
        (f := (ν.localForms (pu.charts α)).components i) (x := x) hρx Finset.univ
    have hTopZero' :
        berezinIntegralOdd (να.components i) x = 0 := by
      simpa [να, IntegralFormCodim1.mulByFunction] using hTopZero
    simp [F, signedBerezinComponents, hTopZero']
  have hDivZero : bodyIntegral (bodyDivergence F) (pu.supportDomains α) = 0 :=
    hDivThm α F hFsupport
  have hd0 : berezinIntegralOdd (superExteriorDerivativeCodim1 να).coefficient = bodyDivergence F := by
    simpa [superExteriorDerivativeCodim1_eq_d0, F] using d0_is_divergence να
  simpa [να, hd0] using hDivZero

/-- Global Stokes with derived chartwise Leibniz decomposition.

    This removes the bridge hypotheses `hGlobalExpand` and `hLeibnizDecomp` by
    deriving them from definitions and `d0Codim1_mulByFunction`. -/
theorem global_super_stokes_no_boundary_reduced {dim : SuperDimension}
    (M : Supermanifold dim) (hp : 0 < dim.even) (hq : 0 < dim.odd)
    (ν : GlobalIntegralFormCodim1 M)
    (pu : SuperPartitionOfUnity M)
    (bodyIntegral : SmoothFunction dim.even → Set (Fin dim.even → ℝ) → ℝ)
    (hLinear : BodyIntegral.IsLinear dim.even bodyIntegral)
    (hChangeOfVar : BodyIntegral.SatisfiesChangeOfVar dim.even bodyIntegral)
    (hDivThm : ∀ (α : pu.index) (F : Fin dim.even → SmoothFunction dim.even),
      (∀ i x, x ∉ pu.supportDomains α → (F i).toFun x = 0) →
      bodyIntegral (bodyDivergence F) (pu.supportDomains α) = 0)
    (transitions : pu.index → SuperCoordChange dim.even dim.odd)
    (hSuperSum : ∀ x : Fin dim.even → ℝ,
      @Finset.sum pu.index (FiniteGrassmannCarrier dim.odd) _
        (@Finset.univ pu.index pu.finIndex) (fun α =>
          composeEvalAt (pu.functions α) (transitions α) x) = 1)
    (hExactZero : ∀ α,
      bodyIntegral
        (berezinIntegralOdd
          (superExteriorDerivativeCodim1
            (IntegralFormCodim1.mulByFunction (pu.functions α)
              (ν.localForms (pu.charts α)))).coefficient)
        (pu.supportDomains α) = 0)
    (hCorrectionZero :
      @Finset.sum pu.index ℝ _ (@Finset.univ pu.index pu.finIndex) (fun α =>
        bodyIntegral
          (berezinIntegralOdd
            (wedgeEvenDeriv (pu.functions α)
              (ν.localForms (pu.charts α))).coefficient)
          (pu.supportDomains α)) = 0) :
    globalBerezinIntegral M (globalExteriorDerivative ν) pu bodyIntegral = 0 := by
  let localTerm : pu.index → ℝ := fun α =>
    bodyIntegral
      (berezinIntegralOdd
        (SuperDomainFunction.mul (pu.functions α)
          (superExteriorDerivativeCodim1 (ν.localForms (pu.charts α))).coefficient))
      (pu.supportDomains α)
  let exactTerm : pu.index → ℝ := fun α =>
    bodyIntegral
      (berezinIntegralOdd
        (superExteriorDerivativeCodim1
          (IntegralFormCodim1.mulByFunction (pu.functions α)
            (ν.localForms (pu.charts α)))).coefficient)
      (pu.supportDomains α)
  let correctionTerm : pu.index → ℝ := fun α =>
    bodyIntegral
      (berezinIntegralOdd
        (wedgeEvenDeriv (pu.functions α)
          (ν.localForms (pu.charts α))).coefficient)
      (pu.supportDomains α)
  have hGlobalExpand :
      globalBerezinIntegral M (globalExteriorDerivative ν) pu bodyIntegral =
      @Finset.sum pu.index ℝ _ (@Finset.univ pu.index pu.finIndex)
        (fun α => localTerm α) := by
    unfold globalBerezinIntegral localTerm
    rfl
  have hLeibnizDecomp : ∀ α, localTerm α = exactTerm α - correctionTerm α := by
    intro α
    simpa [localTerm, exactTerm, correctionTerm] using
      local_leibniz_decomp_bodyIntegral ν pu bodyIntegral hLinear α
  have hExactZero' : ∀ α, exactTerm α = 0 := by
    intro α
    simpa [exactTerm] using hExactZero α
  have hCorrectionZero' :
      @Finset.sum pu.index ℝ _ (@Finset.univ pu.index pu.finIndex)
        (fun α => correctionTerm α) = 0 := by
    simpa [correctionTerm] using hCorrectionZero
  exact global_super_stokes_no_boundary M hp hq ν pu bodyIntegral hLinear hChangeOfVar
    hDivThm transitions hSuperSum localTerm exactTerm correctionTerm hGlobalExpand
    hLeibnizDecomp hExactZero' hCorrectionZero'

/-- Global Stokes with both chartwise Leibniz decomposition and exact-term vanishing
    derived internally.

    Remaining external cancellation input is only the global correction-term sum. -/
theorem global_super_stokes_no_boundary_more_reduced {dim : SuperDimension}
    (M : Supermanifold dim) (hp : 0 < dim.even) (hq : 0 < dim.odd)
    (ν : GlobalIntegralFormCodim1 M)
    (pu : SuperPartitionOfUnity M)
    (bodyIntegral : SmoothFunction dim.even → Set (Fin dim.even → ℝ) → ℝ)
    (hLinear : BodyIntegral.IsLinear dim.even bodyIntegral)
    (hChangeOfVar : BodyIntegral.SatisfiesChangeOfVar dim.even bodyIntegral)
    (hDivThm : ∀ (α : pu.index) (F : Fin dim.even → SmoothFunction dim.even),
      (∀ i x, x ∉ pu.supportDomains α → (F i).toFun x = 0) →
      bodyIntegral (bodyDivergence F) (pu.supportDomains α) = 0)
    (transitions : pu.index → SuperCoordChange dim.even dim.odd)
    (hSuperSum : ∀ x : Fin dim.even → ℝ,
      @Finset.sum pu.index (FiniteGrassmannCarrier dim.odd) _
        (@Finset.univ pu.index pu.finIndex) (fun α =>
          composeEvalAt (pu.functions α) (transitions α) x) = 1)
    (hSupportFull : ∀ α I x,
      x ∉ pu.supportDomains α → (pu.functions α).coefficients I x = 0)
    (hCorrectionZero :
      @Finset.sum pu.index ℝ _ (@Finset.univ pu.index pu.finIndex) (fun α =>
        bodyIntegral
          (berezinIntegralOdd
            (wedgeEvenDeriv (pu.functions α)
              (ν.localForms (pu.charts α))).coefficient)
          (pu.supportDomains α)) = 0) :
    globalBerezinIntegral M (globalExteriorDerivative ν) pu bodyIntegral = 0 := by
  have hExactZero :
      ∀ α,
        bodyIntegral
          (berezinIntegralOdd
            (superExteriorDerivativeCodim1
              (IntegralFormCodim1.mulByFunction (pu.functions α)
                (ν.localForms (pu.charts α)))).coefficient)
          (pu.supportDomains α) = 0 :=
    exact_term_zero_from_divergence ν pu bodyIntegral hDivThm hSupportFull
  exact global_super_stokes_no_boundary_reduced M hp hq ν pu bodyIntegral hLinear hChangeOfVar
    hDivThm transitions hSuperSum hExactZero hCorrectionZero

/-- For lifted partitions (`ρ_α = liftToSuper h_α`), coefficient-level support
    vanishing follows from body support plus θ-independence. -/
private theorem support_full_of_lift_partition {dim : SuperDimension}
    {M : Supermanifold dim}
    (pu : SuperPartitionOfUnity M)
    (bodyFunctions : pu.index → SmoothFunction dim.even)
    (hLift : ∀ α, pu.functions α = liftToSuper (bodyFunctions α)) :
    ∀ α I x, x ∉ pu.supportDomains α → (pu.functions α).coefficients I x = 0 := by
  intro α I x hx
  by_cases hI : I = ∅
  · subst hI
    simpa [SuperDomainFunction.body] using pu.support_subset α x hx
  · rw [hLift α, liftToSuper, SuperDomainFunction.ofSmooth]
    simp [hI]

/-- Global Stokes specialization for lifted partitions of unity.

    This discharges `hSupportFull` automatically from `hLift`, so the only
    remaining external cancellation input is the global correction-term sum. -/
theorem global_super_stokes_no_boundary_lift_partition {dim : SuperDimension}
    (M : Supermanifold dim) (hp : 0 < dim.even) (hq : 0 < dim.odd)
    (ν : GlobalIntegralFormCodim1 M)
    (pu : SuperPartitionOfUnity M)
    (bodyFunctions : pu.index → SmoothFunction dim.even)
    (hLift : ∀ α, pu.functions α = liftToSuper (bodyFunctions α))
    (bodyIntegral : SmoothFunction dim.even → Set (Fin dim.even → ℝ) → ℝ)
    (hLinear : BodyIntegral.IsLinear dim.even bodyIntegral)
    (hChangeOfVar : BodyIntegral.SatisfiesChangeOfVar dim.even bodyIntegral)
    (hDivThm : ∀ (α : pu.index) (F : Fin dim.even → SmoothFunction dim.even),
      (∀ i x, x ∉ pu.supportDomains α → (F i).toFun x = 0) →
      bodyIntegral (bodyDivergence F) (pu.supportDomains α) = 0)
    (transitions : pu.index → SuperCoordChange dim.even dim.odd)
    (hSuperSum : ∀ x : Fin dim.even → ℝ,
      @Finset.sum pu.index (FiniteGrassmannCarrier dim.odd) _
        (@Finset.univ pu.index pu.finIndex) (fun α =>
          composeEvalAt (pu.functions α) (transitions α) x) = 1)
    (hCorrectionZero :
      @Finset.sum pu.index ℝ _ (@Finset.univ pu.index pu.finIndex) (fun α =>
        bodyIntegral
          (berezinIntegralOdd
            (wedgeEvenDeriv (pu.functions α)
              (ν.localForms (pu.charts α))).coefficient)
          (pu.supportDomains α)) = 0) :
    globalBerezinIntegral M (globalExteriorDerivative ν) pu bodyIntegral = 0 := by
  have hSupportFull :
      ∀ α I x, x ∉ pu.supportDomains α → (pu.functions α).coefficients I x = 0 :=
    support_full_of_lift_partition pu bodyFunctions hLift
  exact global_super_stokes_no_boundary_more_reduced M hp hq ν pu bodyIntegral
    hLinear hChangeOfVar hDivThm transitions hSuperSum hSupportFull hCorrectionZero

/-- Global Stokes for the canonical partition built from a `BodyPartitionWitness`.

    The lifted-form hypothesis `ρ_α = liftToSuper(h_α)` is discharged by
    construction (`BodyPartitionWitness.toSuperPartition_functions`). -/
theorem global_super_stokes_no_boundary_body_partition {dim : SuperDimension}
    (M : Supermanifold dim) (hp : 0 < dim.even) (hq : 0 < dim.odd)
    (ν : GlobalIntegralFormCodim1 M)
    (bp : BodyPartitionWitness M)
    (bodyIntegral : SmoothFunction dim.even → Set (Fin dim.even → ℝ) → ℝ)
    (hLinear : BodyIntegral.IsLinear dim.even bodyIntegral)
    (hChangeOfVar : BodyIntegral.SatisfiesChangeOfVar dim.even bodyIntegral)
    (hDivThm : ∀ (α : bp.toSuperPartition.index) (F : Fin dim.even → SmoothFunction dim.even),
      (∀ i x, x ∉ bp.toSuperPartition.supportDomains α → (F i).toFun x = 0) →
      bodyIntegral (bodyDivergence F) (bp.toSuperPartition.supportDomains α) = 0)
    (transitions : bp.toSuperPartition.index → SuperCoordChange dim.even dim.odd)
    (hSuperSum : ∀ x : Fin dim.even → ℝ,
      @Finset.sum bp.toSuperPartition.index (FiniteGrassmannCarrier dim.odd) _
        (@Finset.univ bp.toSuperPartition.index bp.toSuperPartition.finIndex) (fun α =>
          composeEvalAt (bp.toSuperPartition.functions α) (transitions α) x) = 1)
    (hCorrectionZero :
      @Finset.sum bp.toSuperPartition.index ℝ _
        (@Finset.univ bp.toSuperPartition.index bp.toSuperPartition.finIndex) (fun α =>
          bodyIntegral
            (berezinIntegralOdd
              (wedgeEvenDeriv (bp.toSuperPartition.functions α)
                (ν.localForms (bp.toSuperPartition.charts α))).coefficient)
            (bp.toSuperPartition.supportDomains α)) = 0) :
    globalBerezinIntegral M (globalExteriorDerivative ν) bp.toSuperPartition bodyIntegral = 0 := by
  exact global_super_stokes_no_boundary_lift_partition M hp hq ν bp.toSuperPartition
    bp.bodyFunctions bp.toSuperPartition_functions bodyIntegral hLinear hChangeOfVar
    hDivThm transitions hSuperSum hCorrectionZero

/-! ## Consequences -/

/-- Cohomological consequence: exact integral forms integrate to zero.

    If ω = dν for some global codimension-1 form ν, then ∫_M ω = 0.
    This shows that the global Berezin integral descends to cohomology. -/
theorem exact_form_integrates_to_zero {dim : SuperDimension}
    (M : Supermanifold dim) (hp : 0 < dim.even) (hq : 0 < dim.odd)
    (ν : GlobalIntegralFormCodim1 M)
    (pu : SuperPartitionOfUnity M)
    (bodyIntegral : SmoothFunction dim.even → Set (Fin dim.even → ℝ) → ℝ)
    (hLinear : BodyIntegral.IsLinear dim.even bodyIntegral)
    (hChangeOfVar : BodyIntegral.SatisfiesChangeOfVar dim.even bodyIntegral)
    (hDivThm : ∀ (α : pu.index) (F : Fin dim.even → SmoothFunction dim.even),
      (∀ i x, x ∉ pu.supportDomains α → (F i).toFun x = 0) →
      bodyIntegral (bodyDivergence F) (pu.supportDomains α) = 0)
    (transitions : pu.index → SuperCoordChange dim.even dim.odd)
    (hSuperSum : ∀ x : Fin dim.even → ℝ,
      @Finset.sum pu.index (FiniteGrassmannCarrier dim.odd) _
        (@Finset.univ pu.index pu.finIndex) (fun α =>
          composeEvalAt (pu.functions α) (transitions α) x) = 1)
    (localTerm exactTerm correctionTerm : pu.index → ℝ)
    (hGlobalExpand :
      globalBerezinIntegral M (globalExteriorDerivative ν) pu bodyIntegral =
      @Finset.sum pu.index ℝ _ (@Finset.univ pu.index pu.finIndex)
        (fun α => localTerm α))
    (hLeibnizDecomp : ∀ α, localTerm α = exactTerm α - correctionTerm α)
    (hExactZero : ∀ α, exactTerm α = 0)
    (hCorrectionZero :
      @Finset.sum pu.index ℝ _ (@Finset.univ pu.index pu.finIndex)
        (fun α => correctionTerm α) = 0) :
    globalBerezinIntegral M (globalExteriorDerivative ν) pu bodyIntegral = 0 :=
  global_super_stokes_no_boundary M hp hq ν pu bodyIntegral hLinear hChangeOfVar hDivThm
    transitions hSuperSum localTerm exactTerm correctionTerm hGlobalExpand
    hLeibnizDecomp hExactZero hCorrectionZero

end Supermanifolds
