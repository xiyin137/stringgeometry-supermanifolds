/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license.
-/
import StringGeometry.Supermanifolds.Integration.SuperCompose
import StringGeometry.Supermanifolds.Helpers.NilpotentInverse

/-!
# Partition of Unity on Supermanifolds

Constructs a super partition of unity from a body (ordinary) partition of unity,
following Witten's construction (arXiv:1209.2199, §3.1).

## Mathematical Content

### The Problem
On a supermanifold M with charts {U_α}, we need even super functions {ρ_α}
satisfying Σ_α ρ_α = 1 as super functions. A naive lift of body PU functions
fails because the raw sum picks up nilpotent θ-corrections from coordinate
transitions.

### The Solution (Witten)
1. Start with body PU {ρ̃_α} on M_red
2. Lift each ρ̃_α to θ-independent super function in chart α
3. Express all lifts in a common chart β via super composition
4. Raw sum S_β = 1 + ε_β where ε_β is nilpotent (body sum = 1, rest nilpotent)
5. Normalize: ρ_α := (lift_α ρ̃_α ∘ T_{αβ}) · S_β⁻¹
6. Result: Σ_α ρ_α = S_β · S_β⁻¹ = 1 exactly

## Main Definitions

* `BodyPartitionData` - data for a body-level partition of unity
* `rawSumAt` - the unnormalized sum of lifted partition functions
* `normalizedPartitionAt` - the normalized partition function at a point

## Main Theorems

* `rawSumAt_body_eq_one` - the body component of the raw sum equals 1
* `rawSumAt_hasNoConstant_soul` - the soul of the raw sum has no constant term
* `normalizedPartition_sum_one` - the normalized partition sums to 1

## References

* Witten, "Notes On Supermanifolds And Integration" (1209.2199), §3.1
* Rogers, "Supermanifolds" (2007), §11.2
-/

noncomputable section

namespace Supermanifolds

open Supermanifolds.Helpers FiniteGrassmannCarrier

/-! ## Body Partition of Unity Data

We abstract the body partition of unity as a structure, avoiding the complexity
of connecting directly to Mathlib's `SmoothPartitionOfUnity`. The existence of
such data follows from paracompactness of M_red. -/

/-- Data for a body-level partition of unity on a supermanifold.
    This captures the output of an ordinary smooth partition of unity on M_red,
    expressed in local coordinates of the charts. -/
structure BodyPartitionData {dim : SuperDimension} (M : Supermanifold dim) where
  /-- Finite index set -/
  index : Type*
  [finIndex : Fintype index]
  [decEqIndex : DecidableEq index]
  /-- Associated chart for each index -/
  charts : index → SuperChart M
  /-- Smooth body PU functions, each expressed in its own chart's coordinates -/
  bodyFunctions : index → SmoothFunction dim.even
  /-- Each body function is nonneg -/
  nonneg : ∀ α (x : Fin dim.even → ℝ), 0 ≤ (bodyFunctions α).toFun x
  /-- Support in chart domains -/
  supportDomains : index → Set (Fin dim.even → ℝ)
  supportDomains_open : ∀ α, IsOpen (supportDomains α)
  support_subset : ∀ α (x : Fin dim.even → ℝ),
    x ∉ supportDomains α → (bodyFunctions α).toFun x = 0
  /-- Body sum = 1: at each point of M_red, the sum of body PU functions equals 1.
      Each body function is evaluated in its own chart's coordinates. -/
  body_sum_one : ∀ (p : M.body),
    @Finset.sum index ℝ _ (@Finset.univ index finIndex) (fun α =>
      @dite ℝ (p ∈ (charts α).domain) (Classical.dec _)
        (fun h => (bodyFunctions α).toFun
          (fun i => ((charts α).bodyCoord ⟨p, h⟩ : EuclideanSpace ℝ (Fin dim.even)) i))
        (fun _ => 0)) = 1

/-! ## Pointwise Construction in a Fixed Chart

For a fixed chart β, we express the lifted partition functions in chart β's
coordinates using super composition, then normalize. -/

/-- The raw (unnormalized) sum of lifted partition functions at a body point x,
    evaluated in a fixed chart β's coordinates.

    S_β(x) = Σ_α (liftToSuper ρ̃_α) ∘ T_{αβ}(x)

    where T_{αβ} is the transition from chart β to chart α. Each term
    lifts ρ̃_α to chart α as θ-independent, then uses super composition to
    express it in chart β's coordinates (introducing θ-dependence).

    For the special case α = β, the composition is the identity and
    the contribution is just ρ̃_β(x) (θ-independent). -/
def rawSumAt {dim : SuperDimension} {M : Supermanifold dim}
    (bp : BodyPartitionData M)
    (β : SuperChart M)
    (transitions : bp.index → SuperCoordChange dim.even dim.odd)
    (x : Fin dim.even → ℝ) : FiniteGrassmannCarrier dim.odd :=
  @Finset.sum bp.index (FiniteGrassmannCarrier dim.odd) _
    (@Finset.univ bp.index bp.finIndex) fun α =>
    composeEvalAt (liftToSuper (bp.bodyFunctions α)) (transitions α) x

/-- The body component of the raw sum equals 1.

    At θ = 0, the super composition reduces to ordinary composition at body level:
    (liftToSuper ρ̃_α ∘ T_{αβ})|_{θ=0} = ρ̃_α(T_body_{αβ}(x))

    Summing over α: Σ_α ρ̃_α(T_body_{αβ}(x)) = 1 by the body PU property.

    Note: This requires that the transitions correctly map to chart α's
    body coordinates, which is expressed by the `body_compatible` hypothesis. -/
theorem rawSumAt_body_eq_one {dim : SuperDimension} {M : Supermanifold dim}
    (bp : BodyPartitionData M)
    (β : SuperChart M)
    (transitions : bp.index → SuperCoordChange dim.even dim.odd)
    (p : M.body) (hp : p ∈ β.domain)
    (x : Fin dim.even → ℝ)
    (hx : x = fun i => (β.bodyCoord ⟨p, hp⟩ : EuclideanSpace ℝ (Fin dim.even)) i)
    (body_compatible : ∀ α (hα : p ∈ (bp.charts α).domain),
      (transitions α).bodyMap x =
        fun i => ((bp.charts α).bodyCoord ⟨p, hα⟩ : EuclideanSpace ℝ (Fin dim.even)) i)
    (body_outside : ∀ α, p ∉ (bp.charts α).domain →
      grassmannBody (composeEvalAt (liftToSuper (bp.bodyFunctions α)) (transitions α) x) = 0) :
    grassmannBody (rawSumAt bp β transitions x) = 1 := by
  -- Step 1: body of sum = sum of bodies
  unfold rawSumAt grassmannBody
  have sum_eval_empty : ∀ (s : Finset bp.index)
      (g : bp.index → FiniteGrassmannCarrier dim.odd),
      (s.sum g) ∅ = s.sum (fun n => g n ∅) := by
    intro s g; haveI := bp.decEqIndex
    induction s using Finset.induction_on with
    | empty => rfl
    | insert a s ha ih =>
      simp only [Finset.sum_insert ha, add_apply]
      rw [ih]
  rw [sum_eval_empty]
  -- Step 2: each term's body = ρ̃_α(T_body(x)) or 0
  have hterm : ∀ α,
      (composeEvalAt (liftToSuper (bp.bodyFunctions α)) (transitions α) x) ∅ =
      @dite ℝ (p ∈ (bp.charts α).domain) (Classical.dec _)
        (fun h => (bp.bodyFunctions α).toFun
          (fun i => ((bp.charts α).bodyCoord ⟨p, h⟩ : EuclideanSpace ℝ (Fin dim.even)) i))
        (fun _ => 0) := by
    intro α
    by_cases hα : p ∈ (bp.charts α).domain
    · -- In chart domain: body = g(bodyMap x) = g(chart coords)
      rw [dif_pos hα]
      change grassmannBody (composeEvalAt (liftToSuper (bp.bodyFunctions α)) (transitions α) x) = _
      rw [grassmannBody_composeEvalAt_liftToSuper, body_compatible α hα]
    · -- Outside chart domain: body = 0
      rw [dif_neg hα]
      exact body_outside α hα
  simp_rw [hterm]
  exact bp.body_sum_one p

/-- The soul part of the raw sum has no constant term (is nilpotent).

    Since the body of S is 1, we have S = 1 + soul(S), and soul(S)
    is nilpotent (has no constant term) by `grassmannSoul_hasNoConstant`. -/
theorem rawSumAt_soul_nilpotent {dim : SuperDimension} {M : Supermanifold dim}
    (bp : BodyPartitionData M)
    (β : SuperChart M)
    (transitions : bp.index → SuperCoordChange dim.even dim.odd)
    (x : Fin dim.even → ℝ)
    (hbody : grassmannBody (rawSumAt bp β transitions x) = 1) :
    hasNoConstant (grassmannSoul (rawSumAt bp β transitions x)) :=
  grassmannSoul_hasNoConstant _

/-! ## Normalization

The raw sum S = 1 + soul(S) where soul(S) is nilpotent. This means
S is invertible via the geometric series, and we can normalize. -/

/-- grassmannScalar 1 = 1 as a FiniteGrassmannCarrier element. -/
private theorem grassmannScalar_one_eq {q : ℕ} :
    grassmannScalar (q := q) 1 = (1 : FiniteGrassmannCarrier q) := by
  funext I; simp [grassmannScalar, one_apply]

/-- The raw sum can be decomposed as 1 + ε where ε is nilpotent. -/
theorem rawSumAt_eq_one_add_eps {dim : SuperDimension} {M : Supermanifold dim}
    (bp : BodyPartitionData M)
    (β : SuperChart M)
    (transitions : bp.index → SuperCoordChange dim.even dim.odd)
    (x : Fin dim.even → ℝ)
    (hbody : grassmannBody (rawSumAt bp β transitions x) = 1) :
    rawSumAt bp β transitions x =
      1 + grassmannSoul (rawSumAt bp β transitions x) := by
  let S := rawSumAt bp β transitions x
  have hdecomp := grassmann_body_soul_decomp S
  -- hdecomp : S = grassmannBodyEmbed S + grassmannSoul S
  -- grassmannBodyEmbed S = grassmannScalar (grassmannBody S) = grassmannScalar 1
  have hbe : grassmannBodyEmbed S = 1 := by
    unfold grassmannBodyEmbed
    rw [hbody, grassmannScalar_one_eq]
  rw [hbe] at hdecomp
  exact hdecomp

/-- The raw sum is invertible (it equals 1 + nilpotent). -/
theorem rawSumAt_isUnit {dim : SuperDimension} {M : Supermanifold dim}
    (bp : BodyPartitionData M)
    (β : SuperChart M)
    (transitions : bp.index → SuperCoordChange dim.even dim.odd)
    (x : Fin dim.even → ℝ)
    (hbody : grassmannBody (rawSumAt bp β transitions x) = 1) :
    IsUnit (rawSumAt bp β transitions x) := by
  rw [rawSumAt_eq_one_add_eps bp β transitions x hbody]
  exact isUnit_one_add_hasNoConstant _ (grassmannSoul_hasNoConstant _)

/-- The inverse of the raw sum, computed via the geometric series.
    S⁻¹ = Σ_{n=0}^{q} (-soul(S))^n -/
def rawSumInverseAt {dim : SuperDimension} {M : Supermanifold dim}
    (bp : BodyPartitionData M)
    (β : SuperChart M)
    (transitions : bp.index → SuperCoordChange dim.even dim.odd)
    (x : Fin dim.even → ℝ) : FiniteGrassmannCarrier dim.odd :=
  grassmannGeomInverse (grassmannSoul (rawSumAt bp β transitions x))

/-- The raw sum times its inverse equals 1 (right inverse).
    Proof: S = 1 + soul(S), so S · geomInverse(soul(S)) = (1 + ε) · Σ(-ε)^n = 1
    by grassmannGeomInverse_mul_right. -/
theorem rawSumAt_mul_inverse {dim : SuperDimension} {M : Supermanifold dim}
    (bp : BodyPartitionData M)
    (β : SuperChart M)
    (transitions : bp.index → SuperCoordChange dim.even dim.odd)
    (x : Fin dim.even → ℝ)
    (hbody : grassmannBody (rawSumAt bp β transitions x) = 1) :
    rawSumAt bp β transitions x * rawSumInverseAt bp β transitions x = 1 := by
  -- Use set to abbreviate and avoid timeout during rw
  unfold rawSumInverseAt
  set S := rawSumAt bp β transitions x with hS_def
  set ε := grassmannSoul S with hε_def
  -- S = 1 + ε
  have hS_eq : S = 1 + ε := rawSumAt_eq_one_add_eps bp β transitions x hbody
  rw [hS_eq]
  exact grassmannGeomInverse_mul_right ε (grassmannSoul_hasNoConstant S)

/-- The inverse times the raw sum equals 1 (left inverse).
    Proof: grassmannGeomInverse(soul(S)) * (1 + soul(S)) = 1
    by grassmannGeomInverse_mul. -/
theorem rawSumInverseAt_mul {dim : SuperDimension} {M : Supermanifold dim}
    (bp : BodyPartitionData M)
    (β : SuperChart M)
    (transitions : bp.index → SuperCoordChange dim.even dim.odd)
    (x : Fin dim.even → ℝ)
    (hbody : grassmannBody (rawSumAt bp β transitions x) = 1) :
    rawSumInverseAt bp β transitions x * rawSumAt bp β transitions x = 1 := by
  unfold rawSumInverseAt
  set S := rawSumAt bp β transitions x with hS_def
  set ε := grassmannSoul S with hε_def
  have hS_eq : S = 1 + ε := rawSumAt_eq_one_add_eps bp β transitions x hbody
  rw [hS_eq]
  exact grassmannGeomInverse_mul ε (grassmannSoul_hasNoConstant S)

/-! ## Normalized Partition Functions -/

/-- The normalized α-th partition function at point x in chart β's coordinates.
    ρ_α(x) = (lift_α ρ̃_α ∘ T_{αβ})(x) · S_β(x)⁻¹ -/
def normalizedPartitionAt {dim : SuperDimension} {M : Supermanifold dim}
    (bp : BodyPartitionData M) (α : bp.index)
    (β : SuperChart M)
    (transitions : bp.index → SuperCoordChange dim.even dim.odd)
    (x : Fin dim.even → ℝ) : FiniteGrassmannCarrier dim.odd :=
  composeEvalAt (liftToSuper (bp.bodyFunctions α)) (transitions α) x *
  rawSumInverseAt bp β transitions x

/-- The sum of normalized partition functions equals 1.

    Σ_α ρ_α(x) = Σ_α [(lift ρ̃_α ∘ T) · S⁻¹]
               = (Σ_α lift ρ̃_α ∘ T) · S⁻¹
               = S · S⁻¹ = 1

    Uses the right-distributive law: (Σ a_α) · b = Σ (a_α · b). -/
theorem normalizedPartition_sum_one {dim : SuperDimension} {M : Supermanifold dim}
    (bp : BodyPartitionData M)
    (β : SuperChart M)
    (transitions : bp.index → SuperCoordChange dim.even dim.odd)
    (x : Fin dim.even → ℝ)
    (hbody : grassmannBody (rawSumAt bp β transitions x) = 1) :
    @Finset.sum bp.index (FiniteGrassmannCarrier dim.odd) _
      (@Finset.univ bp.index bp.finIndex) (fun α =>
        normalizedPartitionAt bp α β transitions x) = 1 := by
  unfold normalizedPartitionAt
  -- Factor out S⁻¹: Σ_α (f_α · S⁻¹) = (Σ_α f_α) · S⁻¹
  rw [← Finset.sum_mul]
  -- Σ_α f_α = rawSumAt = S
  show rawSumAt bp β transitions x * rawSumInverseAt bp β transitions x = 1
  exact rawSumAt_mul_inverse bp β transitions x hbody

/-! ## Construction of SuperPartitionOfUnity

To build a full `SuperPartitionOfUnity M` from `BodyPartitionData M`, we need
the normalized partition functions as SuperDomainFunctions (smooth in x).
The smoothness of each coefficient in x follows from:
- Taylor derivatives of body functions are smooth
- Transition function coefficients are smooth
- Geometric series inverse coefficients are finite sums/products of smooth functions
-/

/-- The body of a lifted function equals the original function. -/
private theorem liftToSuper_body {p q : ℕ} (f : SmoothFunction p) :
    (liftToSuper (p := p) (q := q) f).body = f := by
  show (SuperDomainFunction.ofSmooth f).coefficients ∅ = f
  simp only [SuperDomainFunction.ofSmooth, ite_true]

/-- The non-empty coefficient of a lifted function is zero. -/
private theorem liftToSuper_coefficients_ne {p q : ℕ} (f : SmoothFunction p)
    {I : Finset (Fin q)} (hI : I ≠ ∅) :
    (liftToSuper (p := p) (q := q) f).coefficients I = 0 := by
  show (SuperDomainFunction.ofSmooth f).coefficients I = 0
  simp only [SuperDomainFunction.ofSmooth, hI, ite_false]

-- Universe annotation: both BodyPartitionData and SuperPartitionOfUnity share the same
-- universe for their index types.
universe u_idx

/-- Construct a SuperPartitionOfUnity from body partition data.

    This uses naive lifts of the body partition functions: each ρ̃_α is lifted
    to a θ-independent super function liftToSuper(ρ̃_α) in chart α's coordinates.

    The body-level sum-to-one property is preserved because
    (liftToSuper f).body = f, so the body-level sum equals the original body PU sum.

    Note: the Witten normalization (using transitions and rawSumAt) gives the
    stronger property that the super-level sum is exactly 1 (including
    nilpotent corrections). This construction only guarantees body-level sum = 1,
    which is what `SuperPartitionOfUnity` requires.

    The additional `h_in_chart` hypothesis ensures that support domains are
    contained within chart coordinate images, a natural requirement for any
    well-formed body partition of unity. -/
theorem superPartitionFromBody {dim : SuperDimension} {M : Supermanifold dim}
    (bp : @BodyPartitionData.{u_idx} dim M)
    (β : SuperChart M)
    (transitions : bp.index → SuperCoordChange dim.even dim.odd)
    (hbody : ∀ (p : M.body) (hp : p ∈ β.domain),
      let x := fun i => (β.bodyCoord ⟨p, hp⟩ : EuclideanSpace ℝ (Fin dim.even)) i
      grassmannBody (rawSumAt bp β transitions x) = 1)
    (h_in_chart : ∀ α (x : Fin dim.even → ℝ),
      x ∈ bp.supportDomains α →
      ∃ (p : M.body) (hp : p ∈ (bp.charts α).domain),
        (fun i => ((bp.charts α).bodyCoord ⟨p, hp⟩ : EuclideanSpace ℝ (Fin dim.even)) i) = x) :
    Nonempty (@SuperPartitionOfUnity.{u_idx} dim M) :=
  letI := bp.finIndex
  letI := bp.decEqIndex
  ⟨{ index := bp.index
     functions := fun α => liftToSuper (bp.bodyFunctions α)
     functions_even := fun α I hI => by
       have hne : I ≠ ∅ := by intro h; subst h; simp at hI
       show (liftToSuper (bp.bodyFunctions α)).coefficients I = SmoothFunction.const 0
       rw [liftToSuper_coefficients_ne _ hne]; rfl
     nonneg := fun α x => by
       show 0 ≤ (liftToSuper (bp.bodyFunctions α)).body x
       rw [liftToSuper_body]; exact bp.nonneg α x
     charts := bp.charts
     supportDomains := bp.supportDomains
     supportDomains_open := bp.supportDomains_open
     support_subset := fun α x hx => by
       show (liftToSuper (bp.bodyFunctions α)).body x = 0
       rw [liftToSuper_body]; exact bp.support_subset α x hx
     supportDomains_in_chart := h_in_chart
     body_sum_eq_one := fun pt => by
       simp_rw [show ∀ α, (liftToSuper (q := dim.odd) (bp.bodyFunctions α)).body =
         bp.bodyFunctions α from fun α => liftToSuper_body _]
       exact bp.body_sum_one pt }⟩

end Supermanifolds
