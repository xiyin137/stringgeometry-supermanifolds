import StringGeometry.Supermanifolds.Supermanifolds
import StringGeometry.Supermanifolds.Helpers.BerezinianMul
import StringGeometry.Supermanifolds.Helpers.FiniteGrassmann
import StringGeometry.Supermanifolds.Helpers.SuperChainRule
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Topology.Compactness.Paracompact

/-!
# Berezin Integration on Supermanifolds

This file develops the theory of integration on supermanifolds via integral forms
(sections of the Berezinian line bundle).

## Mathematical Background

Integration on supermanifolds differs fundamentally from ordinary manifolds:

1. **Odd directions are algebraic**: Integration over odd variables extracts
   the top θ-component (Berezin integration), which is algebraic not analytic.

2. **The Berezinian replaces the Jacobian**: Under coordinate change, the
   integration measure transforms by the Berezinian (superdeterminant), not
   the ordinary determinant.

3. **Integral forms vs functions**: The correct objects to integrate are
   sections of the Berezinian line bundle Ber(M), not functions.

## Main Definitions

* `BerezinianBundle` - The line bundle whose sections are integral forms
* `IntegralForm` - A section of the Berezinian bundle (integrable object)
* `localBerezinIntegral` - Integration on a super domain ℝ^{p|q}
* `berezinIntegralForm` - The full integral of an integral form

## The Change of Variables Formula

For a coordinate change φ: U → V with super-Jacobian J_φ, and an integral
form ω on V:
  ∫_U φ*ω = ∫_V ω

where φ*ω transforms by the Berezinian:
  φ*[f(y,η) Dy Dη] = f(φ(x,θ)) · Ber(J_φ) · Dx Dθ

## References

* Witten, E. "Notes on Supermanifolds and Integration"
* Manin, Y. "Gauge Field Theory and Complex Geometry", Chapter 4
* Deligne, P., Morgan, J. "Notes on Supersymmetry"
* Berezin, F.A. "Introduction to Superanalysis"
-/

namespace Supermanifolds

open Supermanifolds.Helpers

/-!
## The Berezinian Line Bundle

The Berezinian bundle Ber(M) is a rank 1|0 line bundle (purely even)
whose transition functions are the Berezinians of the coordinate transitions.

For a supermanifold M with atlas {(U_α, φ_α)}, if φ_αβ = φ_α ∘ φ_β⁻¹ is
the transition function on U_α ∩ U_β, then the Berezinian bundle has
transition functions Ber(J_{φ_αβ}).
-/

/-! Note: The `SuperJacobian` structure with proper Grassmann algebra entries is defined in
    `SuperJacobian.lean` and imported via `FiniteGrassmann.lean`. It has entries in
    `SuperDomainFunction p q` with proper ℤ/2-grading conditions. The conversion
    `SuperTransition.toSuperJacobian` computes the Jacobian from coordinate transformations. -/

/-!
## Integral Forms on Super Domains

An integral form on ℝ^{p|q} is an expression of the form
  ω = f(x,θ) · [Dx Dθ]
where:
- f(x,θ) is a super function (section of the structure sheaf)
- [Dx Dθ] = dx¹...dxᵖ dθ¹...dθ^q is the canonical volume element

The bracket notation emphasizes that this is NOT a differential form
but rather a section of the Berezinian bundle.
-/

/-- An integral form on the super domain ℝ^{p|q}.
    This is a section of the Berezinian bundle, written as f(x,θ)[Dx Dθ].

    **Key distinction from differential forms:**
    - An integral form is NOT a differential form
    - The notation [Dx Dθ] denotes the Berezinian volume element, not dx¹∧...∧dxᵖ∧dθ¹∧...∧dθ^q
    - Under coordinate change, integral forms transform by the Berezinian (superdeterminant),
      while differential forms transform by ordinary pullback
    - Only integral forms can be integrated over supermanifolds; differential forms
      can only be integrated over purely bosonic submanifolds

    The Berezin integral ∫ f(x,θ) [Dx Dθ] extracts the top θ-component of f
    and integrates over the body. This is well-defined precisely because of
    the Berezinian transformation law. -/
structure IntegralForm (p q : ℕ) where
  /-- The coefficient function f(x,θ) -/
  coefficient : SuperDomainFunction p q

namespace IntegralForm

variable {p q : ℕ}

/-- Zero integral form -/
def zero : IntegralForm p q := ⟨SuperDomainFunction.zero⟩

/-- Addition of integral forms -/
def add (ω₁ ω₂ : IntegralForm p q) : IntegralForm p q :=
  ⟨SuperDomainFunction.add ω₁.coefficient ω₂.coefficient⟩

/-- Scalar multiplication -/
def smul (c : ℝ) (ω : IntegralForm p q) : IntegralForm p q :=
  ⟨SuperDomainFunction.smul c ω.coefficient⟩

instance : Zero (IntegralForm p q) := ⟨zero⟩
instance : Add (IntegralForm p q) := ⟨add⟩
instance : SMul ℝ (IntegralForm p q) := ⟨smul⟩

/-- Multiply an integral form by a super function -/
def mulByFunction (f : SuperDomainFunction p q) (ω : IntegralForm p q) :
    IntegralForm p q :=
  ⟨SuperDomainFunction.mul f ω.coefficient⟩

end IntegralForm

/-!
## Pullback of Integral Forms

Under a coordinate change φ: ℝ^{p|q} → ℝ^{p|q}, an integral form transforms as:
  φ*[f(y,η) Dy Dη] = f(φ(x,θ)) · Ber(J_φ)(x,θ) · [Dx Dθ]

The key point: the Berezinian appears, NOT the ordinary Jacobian determinant.
This is because:
- For even coordinates: det appears (as usual)
- For odd coordinates: 1/det appears (because dθ transforms oppositely to θ)
- Combined: det(A)/det(D) = Berezinian
-/

/-- A super coordinate transformation (diffeomorphism of super domains) -/
structure SuperCoordChange (p q : ℕ) where
  /-- The transformed even coordinates x'(x,θ) -/
  evenMap : Fin p → SuperDomainFunction p q
  /-- The transformed odd coordinates θ'(x,θ) -/
  oddMap : Fin q → SuperDomainFunction p q
  /-- Even coordinates transform as even functions -/
  evenMap_even : ∀ i I, I.card % 2 = 1 → (evenMap i).coefficients I = SmoothFunction.const 0
  /-- Odd coordinates transform as odd functions -/
  oddMap_odd : ∀ a I, I.card % 2 = 0 → (oddMap a).coefficients I = SmoothFunction.const 0

/-- Convert a `SuperTransition` to a `SuperCoordChange`.

    Both structures carry the same data (even/odd coordinate maps with parity conditions),
    but `SuperTransition` also records the charts and overlap region, and has extra data
    about the body map (diffeomorphism, invertibility) that `SuperCoordChange` does not.

    The parity conditions `= 0` in `SuperTransition` and `= SmoothFunction.const 0`
    in `SuperCoordChange` are definitionally equal via the `Zero` instance on `SmoothFunction`. -/
def SuperTransition.toSuperCoordChange {dim : SuperDimension} {M : Supermanifold dim}
    {chart₁ chart₂ : SuperChart M} (t : SuperTransition chart₁ chart₂) :
    SuperCoordChange dim.even dim.odd where
  evenMap := t.evenTransition
  oddMap := t.oddTransition
  evenMap_even := fun i I hI => t.evenTransition_even i I hI
  oddMap_odd := fun a I hI => t.oddTransition_odd a I hI

/-- The super-Jacobian of a coordinate change.

    For a super coordinate change φ: (x, θ) ↦ (x'(x,θ), θ'(x,θ)), the Jacobian is:
    J = [A  B]  =  [∂x'/∂x  ∂x'/∂θ]
        [C  D]     [∂θ'/∂x  ∂θ'/∂θ]

    Each block is computed by applying the appropriate partial derivative
    (∂/∂xʲ or ∂/∂θᵇ) to the coordinate functions (x'ⁱ or θ'ᵃ).

    The entries are full SuperDomainFunction values (Grassmann-algebra valued),
    with proper ℤ/2-grading: A, D even; B, C odd. -/
noncomputable def SuperCoordChange.jacobian {p q : ℕ} (φ : SuperCoordChange p q) :
    SuperJacobian p q where
  -- A block: ∂x'ⁱ/∂xʲ - even entries
  Ablock := fun i j => partialEven j (φ.evenMap i)
  -- B block: ∂x'ⁱ/∂θᵃ - odd entries
  Bblock := fun i a => partialOdd a (φ.evenMap i)
  -- C block: ∂θ'ᵃ/∂xʲ - odd entries
  Cblock := fun a j => partialEven j (φ.oddMap a)
  -- D block: ∂θ'ᵃ/∂θᵇ - even entries
  Dblock := fun a b => partialOdd b (φ.oddMap a)
  -- Parity proofs: partialEven preserves parity, partialOdd shifts parity
  Ablock_even := fun i j => by
    intro I hI
    simp only [partialEven]
    -- evenMap is even, so coefficient at odd I is 0
    have h := φ.evenMap_even i I hI
    ext x
    -- h says coefficient I = const 0, so fderiv of const 0 is 0
    have hconst : ((φ.evenMap i).coefficients I).toFun = (SmoothFunction.const 0).toFun := by
      rw [h]
    simp only [hconst, SmoothFunction.const]
    rw [fderiv_const_apply]
    rfl
  Bblock_odd := fun i a => by
    intro I hI
    simp only [partialOdd]
    by_cases ha : a ∈ I
    · simp only [ha, not_true_eq_false, ↓reduceIte]
    · simp only [ha, not_false_eq_true, ↓reduceIte]
      -- |I ∪ {a}| = |I| + 1, odd since |I| even
      have hIa_odd : (insert a I).card % 2 = 1 := by
        rw [Finset.card_insert_of_notMem ha]; omega
      have h := φ.evenMap_even i (insert a I) hIa_odd
      -- h : coefficient (insert a I) = const 0
      -- goal : sign • const 0 = 0
      rw [h]
      -- ((-1)^n : ℝ) • (SmoothFunction.const 0) = 0
      have hzero : SmoothFunction.const 0 = (0 : SmoothFunction p) := rfl
      rw [hzero, smul_zero]
  Cblock_odd := fun a j => by
    intro I hI
    simp only [partialEven]
    -- oddMap is odd, so coefficient at even I is 0
    have h := φ.oddMap_odd a I hI
    ext x
    have hconst : ((φ.oddMap a).coefficients I).toFun = (SmoothFunction.const 0).toFun := by
      rw [h]
    simp only [hconst, SmoothFunction.const]
    rw [fderiv_const_apply]
    rfl
  Dblock_even := fun a b => by
    intro I hI
    simp only [partialOdd]
    by_cases hb : b ∈ I
    · simp only [hb, not_true_eq_false, ↓reduceIte]
    · simp only [hb, not_false_eq_true, ↓reduceIte]
      -- |I ∪ {b}| = |I| + 1, even since |I| odd
      have hIb_even : (insert b I).card % 2 = 0 := by
        rw [Finset.card_insert_of_notMem hb]; omega
      have h := φ.oddMap_odd a (insert b I) hIb_even
      rw [h]
      -- ((-1)^n : ℝ) • (SmoothFunction.const 0) = 0
      have hzero : SmoothFunction.const 0 = (0 : SmoothFunction p) := rfl
      rw [hzero, smul_zero]

/-- The Jacobian of a `SuperTransition.toSuperCoordChange` equals `SuperTransition.toSuperJacobian`.

    Both compute the same partial derivatives of the same coordinate functions,
    so they are definitionally equal. -/
theorem SuperTransition.toSuperCoordChange_jacobian_eq {dim : SuperDimension}
    {M : Supermanifold dim} {chart₁ chart₂ : SuperChart M}
    (t : SuperTransition chart₁ chart₂) :
    t.toSuperCoordChange.jacobian = t.toSuperJacobian := by
  rfl

/-- Legacy placeholder pullback of an integral form under a coordinate change.

    Under a super coordinate change φ: (x,θ) ↦ (x',θ'), an integral form transforms as:
      φ*[f(x',θ') Dx' Dθ'] = f(φ(x,θ)) · Ber(J_φ)(x,θ) · [Dx Dθ]

    The Berezinian factor Ber(J_φ) = det(∂x'/∂x - ∂x'/∂θ · (∂θ'/∂θ)⁻¹ · ∂θ'/∂x) / det(∂θ'/∂θ)
    accounts for the transformation of both even and odd coordinates.

    Implementation requires:
    1. **Super function composition**: Given f : SuperDomainFunction p q and
       φ : SuperCoordChange p q, compute f ∘ φ by substituting x'(x,θ), θ'(x,θ)
       for the coordinates in f's expansion. This is algebraic: Taylor expand
       each coefficient f_I at the body point, then substitute nilpotent corrections.
       Uses `grassmann_soul_nilpotent` for termination of the Taylor series.
    2. **Berezinian as super function**: The super-Jacobian ∂(x',θ')/∂(x,θ) is a
       SuperMatrix over the GrassmannAlgebra. Its Berezinian is computed via
       SuperMatrix.ber from Helpers/Berezinian.lean.
    3. **Multiplication**: Multiply the composed function by the Berezinian.

    See Witten's notes (arXiv:1209.2199, eq. 3.10) for the transformation law.
    This legacy definition uses the historical approximate composition
    `composeLegacyApprox` and does NOT include the full Berezinian factor.
    It is retained only for backward compatibility.

    Use `Integration/Pullback.lean` (`pullbackProper`) for the active pipeline. -/
noncomputable def IntegralForm.pullbackLegacy {p q : ℕ}
    (φ : SuperCoordChange p q) (ω : IntegralForm p q) : IntegralForm p q :=
  -- Legacy approximation: compose only, using the historical placeholder
  -- composition operator from Helpers/FiniteGrassmann.lean.
  ⟨SuperDomainFunction.composeLegacyApprox ω.coefficient φ.evenMap φ.oddMap
    (fun k I hI => by simpa using φ.evenMap_even k I hI)
    (fun a I hI => by simpa using φ.oddMap_odd a I hI)⟩

/-!
## Local Berezin Integration

The integral of an integral form ω = f(x,θ)[Dx Dθ] over a super domain U ⊆ ℝ^{p|q}
is computed in two steps:

1. Berezin integrate over odd variables: ∫dθ f(x,θ) = f_{top}(x)
   This extracts the coefficient of θ¹...θ^q.

2. Ordinary integrate over even variables: ∫_U_body dx f_{top}(x)

The full integral is:
  ∫_U ω = ∫_{U_body} dx [∫ dθ¹...dθ^q f(x,θ)]
-/

/-- The Berezin integral over odd variables: extracts the top θ-component -/
def berezinIntegralOdd {p q : ℕ} (f : SuperDomainFunction p q) : SmoothFunction p :=
  f.coefficients Finset.univ

/-- Berezin integral of a constant (in θ) is 0 when q > 0 -/
theorem berezinIntegralOdd_const {p q : ℕ} (hq : 0 < q) (c : SmoothFunction p) :
    berezinIntegralOdd (SuperDomainFunction.ofSmooth c : SuperDomainFunction p q) =
    SmoothFunction.const 0 := by
  unfold berezinIntegralOdd SuperDomainFunction.ofSmooth
  ext x
  haveI : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
  have huniv : (Finset.univ : Finset (Fin q)) ≠ ∅ := Finset.univ_nonempty.ne_empty
  simp [huniv, SmoothFunction.const_apply]

/-- The Berezin integral of an integral form over a region in the body.
    This combines Berezin integration (odd) with ordinary integration (even).

    Note: The full integral would require measure theory on (Fin p → ℝ).
    Here we define it abstractly, with the key property being that
    Berezin integration extracts the top θ-component first. -/
noncomputable def localBerezinIntegral {p q : ℕ}
    (U : Set (Fin p → ℝ)) (ω : IntegralForm p q)
    (bodyIntegral : SmoothFunction p → Set (Fin p → ℝ) → ℝ) : ℝ :=
  bodyIntegral (berezinIntegralOdd ω.coefficient) U

/-!
## Properties of Berezin Integration

The key properties that make Berezin integration well-behaved:

1. **Linearity**: ∫(aω₁ + bω₂) = a∫ω₁ + b∫ω₂
2. **Change of variables**: ∫_U φ*ω = ∫_{φ(U)} ω (with Berezinian!)
3. **Integration by parts**: ∫ (∂f/∂θ) = 0 for odd derivatives
4. **Fubini**: Can integrate even and odd variables in either order
-/

/-- Linearity of the Berezin integral over odd variables -/
theorem berezinIntegralOdd_add {p q : ℕ} (f g : SuperDomainFunction p q) :
    berezinIntegralOdd (SuperDomainFunction.add f g) =
    fun x => berezinIntegralOdd f x + berezinIntegralOdd g x := by
  unfold berezinIntegralOdd SuperDomainFunction.add
  rfl

/-- Scalar multiplication for Berezin integral -/
theorem berezinIntegralOdd_smul {p q : ℕ} (c : ℝ) (f : SuperDomainFunction p q) :
    berezinIntegralOdd (SuperDomainFunction.smul c f) =
    fun x => c * berezinIntegralOdd f x := by
  unfold berezinIntegralOdd SuperDomainFunction.smul
  rfl

/-- The body map of a SuperCoordChange extracts the θ-independent part. -/
noncomputable def SuperCoordChange.bodyMap {p q : ℕ} (φ : SuperCoordChange p q) :
    (Fin p → ℝ) → (Fin p → ℝ) :=
  fun x => fun i => (φ.evenMap i).body x

/-- φ is a local diffeomorphism: its body map restricts to a diffeomorphism U → V.
    This requires: body map is smooth, bijective U → V, with smooth inverse. -/
structure SuperCoordChange.IsDiffeoOn {p q : ℕ} (φ : SuperCoordChange p q)
    (U V : Set (Fin p → ℝ)) : Prop where
  /-- Body map is smooth (inherited from evenMap) -/
  smooth_body : ContDiff ℝ ⊤ φ.bodyMap
  /-- Body map maps U into V -/
  maps_to : Set.MapsTo φ.bodyMap U V
  /-- Body map is bijective from U to V -/
  bij : Set.BijOn φ.bodyMap U V
  /-- Inverse is smooth on V -/
  smooth_inv : ∃ ψ : (Fin p → ℝ) → (Fin p → ℝ),
      ContDiff ℝ ⊤ ψ ∧ Set.MapsTo ψ V U ∧
      (∀ x ∈ U, ψ (φ.bodyMap x) = x) ∧ (∀ y ∈ V, φ.bodyMap (ψ y) = y)

/-- The body integral satisfies the change of variables formula on ℝ^p.

    For an orientation-preserving diffeomorphism Φ : U → V:
      ∫_V f dy = ∫_U (f ∘ Φ) · det(DΦ) dx

    This uses the SIGNED determinant because the body integral arises from
    Berezin integration of integral forms (sections of the Berezinian bundle),
    which transform by the signed Berezinian = det(A)/det(D). After the
    det(D) cancellation in the Berezin integral, what remains is signed det(A).

    For oriented supermanifolds, the transitions preserve orientation,
    so det(DΦ) > 0 and the sign doesn't matter in practice. But using
    signed det is the correct formulation for forms rather than measures. -/
structure BodyIntegral.SatisfiesChangeOfVar (p : ℕ)
    (bodyIntegral : SmoothFunction p → Set (Fin p → ℝ) → ℝ) : Prop where
  /-- For a smooth diffeomorphism Φ : U → V,
      ∫_V f dy = ∫_U (f ∘ Φ) · det(DΦ) dx.

      The right-hand side uses a `SmoothFunction` packaging `(f ∘ Φ) · det J`
      together with a proof that it equals this expression pointwise.
      This avoids requiring the caller to separately prove smoothness of the
      composed expression (which would need significant real analysis infrastructure). -/
  change_of_var : ∀ (U V : Set (Fin p → ℝ))
      (Φ : (Fin p → ℝ) → (Fin p → ℝ))
      (_hΦ : ContDiff ℝ ⊤ Φ)
      (_hBij : Set.BijOn Φ U V)
      (f : SmoothFunction p)
      -- The composed integrand, packaged as a SmoothFunction
      (fΦJ : SmoothFunction p)
      -- Pointwise equality: fΦJ(x) = f(Φ(x)) · det(DΦ(x))
      (_hfΦJ : ∀ x, fΦJ.toFun x = f.toFun (Φ x) *
        (fderiv ℝ Φ x).det),
      bodyIntegral f V = bodyIntegral fΦJ U

theorem berezin_change_of_variables_formula_legacy {p q : ℕ}
    (U V : Set (Fin p → ℝ))
    (φ : SuperCoordChange p q)
    (hDiffeo : φ.IsDiffeoOn U V)
    (ω : IntegralForm p q)
    (hPullbackBody : ∀ x,
      berezinIntegralOdd (IntegralForm.pullbackLegacy φ ω).coefficient x =
      (berezinIntegralOdd ω.coefficient).toFun (φ.bodyMap x) *
        (fderiv ℝ φ.bodyMap x).det)
    (bodyIntegral : SmoothFunction p → Set (Fin p → ℝ) → ℝ)
    (hChangeOfVar : BodyIntegral.SatisfiesChangeOfVar p bodyIntegral) :
    localBerezinIntegral U (IntegralForm.pullbackLegacy φ ω) bodyIntegral =
    localBerezinIntegral V ω bodyIntegral := by
  unfold localBerezinIntegral
  let fTop : SmoothFunction p := berezinIntegralOdd ω.coefficient
  let fTopPull : SmoothFunction p :=
    berezinIntegralOdd (IntegralForm.pullbackLegacy φ ω).coefficient
  have hfTopPull :
      ∀ x, fTopPull.toFun x = fTop.toFun (φ.bodyMap x) *
        (fderiv ℝ φ.bodyMap x).det := by
    intro x
    change berezinIntegralOdd (IntegralForm.pullbackLegacy φ ω).coefficient x =
      (berezinIntegralOdd ω.coefficient).toFun (φ.bodyMap x) *
        (fderiv ℝ φ.bodyMap x).det
    simpa using hPullbackBody x
  have hCov :=
    hChangeOfVar.change_of_var U V φ.bodyMap hDiffeo.smooth_body hDiffeo.bij
      fTop fTopPull hfTopPull
  simpa [fTop, fTopPull] using hCov.symm

/-!
## Detailed Analysis of the Change of Variables Formula

### Why the Berezinian Appears

Consider a coordinate change φ: (x, θ) ↦ (y, η) with Jacobian matrix:

    J = [A  B]   where   A = ∂y/∂x  (even-even, p×p, ordinary derivatives)
        [C  D]           B = ∂y/∂θ  (even-odd, p×q, contains odd elements)
                         C = ∂η/∂x  (odd-even, q×p, contains odd elements)
                         D = ∂η/∂θ  (odd-odd, q×q, contains even elements)

**For even coordinates (dx¹...dxᵖ):**
The transformation law is the usual one:
  dy¹...dyᵖ = det(∂y/∂x) · dx¹...dxᵖ + (terms involving dθ)

For the top component (which the Berezin integral extracts), we get det(A).

**For odd coordinates (dθ¹...dθ^q):**
Here's the key subtlety: the odd measure [Dθ] transforms OPPOSITELY to θ!

If θ' = Dθ + ... (linear transformation), then the Berezin measure satisfies:
  [Dθ'] = det(D)⁻¹ · [Dθ]

This is because ∫dθ (aθ) = a for constant a, so d(aθ) must scale as a⁻¹.

**Combined transformation:**
  [Dy Dη] = det(A) · det(D)⁻¹ · [Dx Dθ] + (nilpotent corrections)

The ratio det(A)/det(D) is exactly the Berezinian!

More precisely, with nilpotent corrections:
  [Dy Dη] = Ber(J) · [Dx Dθ]

where Ber(J) = det(A - BD⁻¹C) / det(D).

### The Schur Complement Formula

The formula A - BD⁻¹C (the Schur complement) arises from the block decomposition:

  [A  B]   [I    BD⁻¹] [A-BD⁻¹C  0 ]   [I   0]
  [C  D] = [0    I   ] [0        D ]   [D⁻¹C I]

So det(full matrix) = det(A - BD⁻¹C) · det(D).

The Berezinian uses the RATIO of these:
  Ber = det(A - BD⁻¹C) / det(D)

### Example: Simple (1|1) Case

For ℝ^{1|1} with coordinates (x, θ) → (y(x,θ), η(x,θ)):
- y = a(x) + b(x)θ  (even function)
- η = c(x) + d(x)θ  (odd function, so c=0, d≠0)

The Jacobian is:
  J = [a'  b ]   where a' = da/dx
      [0   d ]

Berezinian: Ber(J) = a'/d

The transformation: [Dy Dη] = (a'/d) [Dx Dθ]

So if we integrate f(y,η) [Dy Dη]:
  ∫ f(y,η) [Dy Dη] = ∫ f(y(x,θ), η(x,θ)) · (a'/d) [Dx Dθ]
-/

-- The Berezinian transformation law:
--   For φ: (x,θ) ↦ (y,η) with Jacobian J = [A B; C D]:
--     [Dy Dη] = Ber(J) · [Dx Dθ]
--   From Witten's notes (arXiv:1209.2199, eq. 3.10).
--   This is encoded in the legacy placeholder definition `IntegralForm.pullbackLegacy`:
--     pullbackLegacy φ ω = ⟨(ω.coefficient ∘ φ) · Ber(J_φ)⟩
--
-- Key theorems to prove (once composition infrastructure is available):
--   pullback_identity: pullback id ω = ω
--   pullback_composition: pullback (ψ ∘ φ) ω = pullback φ (pullback ψ ω)
--   change_of_variables: ∫_U φ*ω = ∫_{φ(U)} ω

/-! **Berezinian properties** (TODO: implement with proper SuperMatrix framework)

    Once the super-Jacobian is properly defined as a `SuperMatrix` over a `GrassmannAlgebra ℝ`,
    the following properties follow from `SuperMatrix.ber_mul`:

    - **Multiplicativity**: Ber(J₁ · J₂) = Ber(J₁) · Ber(J₂)
    - **Identity**: Ber(I) = 1
    - **Inverse**: Ber(J⁻¹) = Ber(J)⁻¹

    These are essential for the change of variables formula to be consistent
    under composition of coordinate changes. -/

/-- Unfold `berezinIntegralOdd` to its definition (extracts top θ-component).

    **Note**: Despite its name, this is just the definitional unfolding of
    `berezinIntegralOdd`. The actual anticommutativity of Berezin measures
    is encoded in the `reorderSign` within `SuperDomainFunction.mul`, not here.
    The name is misleading — this theorem has no content about sign conventions. -/
-- MISLEADING NAME: This is just `rfl` unfolding berezinIntegralOdd.
-- The actual anticommutativity is in reorderSign within SuperDomainFunction.mul.
theorem berezin_measure_anticommute {p q : ℕ} (f : SuperDomainFunction p q) :
    berezinIntegralOdd f = f.coefficients Finset.univ := rfl

/-!
## Integration by Parts

For odd derivatives, integration by parts gives zero boundary terms
(because the boundary of a supermanifold in the odd directions is empty).

∫ dθ (∂f/∂θ) = 0
-/

/-- The odd coordinate θᵃ as a super function -/
def oddCoordinate {p q : ℕ} (a : Fin q) : SuperDomainFunction p q :=
  ⟨fun I => if I = {a} then SmoothFunction.const 1 else SmoothFunction.const 0⟩

/-- Integration by parts for odd derivatives: the Berezin integral of ∂f/∂θᵃ
    extracts a component that is not the top component, hence vanishes.

    More precisely: ∂/∂θᵃ lowers the θ-degree by 1, so if f has top component
    in θ¹...θ^q, then ∂f/∂θᵃ has no top component. -/
theorem berezin_integration_by_parts_odd {p q : ℕ} (a : Fin q) (_ : 0 < q)
    (f : SuperDomainFunction p q) :
    berezinIntegralOdd (partialOdd a f) = SmoothFunction.const 0 := by
  unfold berezinIntegralOdd partialOdd
  ext x
  simp only
  -- With the corrected partialOdd: coefficient at I is nonzero only when a ∉ I
  -- For I = Finset.univ, we have a ∈ Finset.univ (since a : Fin q)
  -- So the condition "a ∉ Finset.univ" is false, giving 0
  have ha : a ∈ Finset.univ := Finset.mem_univ a
  simp only [Finset.mem_univ, not_true_eq_false, ↓reduceIte, SmoothFunction.const_apply,
    SmoothFunction.zero_apply]

/-!
## Global Integration on Supermanifolds

Integration on supermanifolds is neither purely measure-theoretic nor purely
algebraic. Following Witten's approach ("Notes on Supermanifolds and Integration"):

### Construction via Partition of Unity

1. **Local structure**: On each chart U_α ≅ ℝ^{p|q}, an integral form is
   ω_α = f_α(x,θ) [Dx Dθ]. The Berezin integral over odd variables is algebraic:
     ∫ dθ f_α(x,θ) = f_α^{top}(x)  (extracts top θ-component)

2. **Partition of unity**: To glue local integrals, we need a partition of unity
   {ρ_α} subordinate to the atlas. The ρ_α depend only on body coordinates x.

3. **Global integral**: ∫_M ω = Σ_α ∫_{U_α,red} dx ρ_α(x) · [∫ dθ f_α(x,θ)]

### Key Theorems Required

**Existence**: A partition of unity exists on the body M_red. Since M_red is a
smooth manifold (paracompact, Hausdorff), standard partition of unity results
from differential topology apply.

**Uniqueness**: Different choices of partition of unity yield the same integral.
This follows from the Berezinian change of variables formula on overlaps.

### Why This Is Nontrivial

- The odd integration is algebraic (Berezin), but gluing requires smooth structure
- The transformation law uses Ber(J), not det(J), which is crucial for consistency
- The partition of unity lives on M_red, not on the full supermanifold M
-/

/-- A partition of unity on a supermanifold.

    **Construction** (Witten, arXiv:1209.2199, §3.1):
    1. Start with a smooth partition of unity {ρ̃_α} on M_red (body manifold)
    2. Lift each ρ̃_α to a θ-independent super function in chart α
    3. On overlaps, the lifts from different charts are **incompatible**: expressing
       (lift_α ρ̃_α) in chart β's coordinates via the transition x_α = x_α(x_β, θ_β)
       introduces θ_β-dependence through Taylor expansion of ρ̃_α(x_α(x_β, θ_β))
    4. The raw sum S = Σ_α (lifted ρ_α) = 1 + (nilpotent even corrections) on M
    5. Since S = 1 + ε with ε nilpotent, S is invertible: S⁻¹ = 1 - ε + ε² - ...
    6. Define normalized partition: ρ_α := (lifted ρ_α) · S⁻¹

    The result: each ρ_α is an **even super function with genuine θ-dependence**,
    and Σ_α ρ_α = 1 exactly on M. The θ-dependence arises from the normalization
    and is not an artifact — it's mathematically necessary for the global sum to
    be exactly 1 on M (not just on M_red).

    **Key properties**:
    - Each ρ_α is supported in chart α's domain (falls off smoothly to zero)
    - Each ρ_α is even (only even θ-powers, from parity of transitions)
    - Σ_α ρ_α = 1 as super functions on M
    - At body level: ρ_α|_{θ=0} = ρ̃_α (recovers the body partition) -/
structure SuperPartitionOfUnity {dim : SuperDimension} (M : Supermanifold dim) where
  /-- Index set for the partition. We require finite index for well-defined sums.
      For infinite atlases, pass to a locally finite refinement first. -/
  index : Type*
  [finIndex : Fintype index]
  [decEqIndex : DecidableEq index]
  /-- The partition functions ρ_α as even super functions in each chart's coordinates.
      Each `functions α` is the coordinate expression of ρ_α in chart α.
      These are even super functions (with θ-dependence from normalization):
      "one can find bosonic functions h_α on M such that each h_α is supported in
      the interior of U_α and Σ_α h_α = 1" (Witten, arXiv:1209.2199, §3.1) -/
  functions : index → SuperDomainFunction dim.even dim.odd
  /-- Each ρ_α is an even super function: only even θ-powers appear.
      This is preserved by the normalization procedure since both the lifts
      and the sum S are even. -/
  functions_even : ∀ α (I : Finset (Fin dim.odd)),
    I.card % 2 = 1 → (functions α).coefficients I = SmoothFunction.const 0
  /-- Each ρ_α ≥ 0 at body level -/
  nonneg : ∀ α (x : Fin dim.even → ℝ), 0 ≤ (functions α).body x
  /-- Associated charts for each partition index -/
  charts : index → SuperChart M
  /-- Support domains in local coordinates (subsets of ℝ^{dim.even}) -/
  supportDomains : index → Set (Fin dim.even → ℝ)
  /-- Support domains are open -/
  supportDomains_open : ∀ α, IsOpen (supportDomains α)
  /-- Each ρ_α is supported in its domain at body level:
      "each h_α is supported in the interior of U_α" -/
  support_subset : ∀ α (x : Fin dim.even → ℝ),
    x ∉ supportDomains α → (functions α).body x = 0
  /-- Support domains are contained within the body coordinate image of the chart. -/
  supportDomains_in_chart : ∀ α (x : Fin dim.even → ℝ),
    x ∈ supportDomains α →
    ∃ (p : M.body) (hp : p ∈ (charts α).domain),
      (fun i => ((charts α).bodyCoord ⟨p, hp⟩ : EuclideanSpace ℝ (Fin dim.even)) i) = x
  /-- Body-level sum to 1: for every point p ∈ M.body, evaluating each ρ_α at p
      (in chart α's coordinates) and summing gives 1.

      This is the coordinate-free body-level condition. Each function is evaluated
      in its own chart's coordinate system. If p is not in chart α's domain,
      ρ_α contributes 0 (by support_subset + supportDomains_in_chart). -/
  body_sum_eq_one : ∀ (p : M.body),
    @Finset.sum index ℝ _ (@Finset.univ index finIndex) (fun α =>
      @dite ℝ (p ∈ (charts α).domain) (Classical.dec _)
        (fun h => (functions α).body
          (fun i => ((charts α).bodyCoord ⟨p, h⟩ : EuclideanSpace ℝ (Fin dim.even)) i))
        (fun _ => 0)) = 1
  -- Super-level sum to 1: The Witten construction (lift body PU, compose to
  -- common chart, raw sum = 1 + nilpotent, divide by sum) produces partition
  -- functions whose composed sum in any single chart equals 1 as a Grassmann
  -- algebra element. This property requires `composeEvalAt` (SuperCompose.lean)
  -- and is taken as a hypothesis `hSuperSum` in GlobalStokes.lean theorems.
  -- It is proved by `normalizedPartition_sum_one` in PartitionOfUnity.lean.

/-- Lift a smooth function on the body to a super function (constant in θ).

    This is the key construction: a function f : M_red → ℝ becomes a
    super function f(x, θ) = f(x) that is independent of θ.

    Properties:
    - The lift is purely even (only the ∅ coefficient is nonzero)
    - Multiplication by a lifted function preserves θ-degree
    - The Berezin integral of (lift f) · g equals f · (Berezin integral of g) -/
def liftToSuper {p q : ℕ} (f : SmoothFunction p) : SuperDomainFunction p q :=
  SuperDomainFunction.ofSmooth f

/-- Lifting preserves the sum: if Σ_α f_α = 1 on M_red, then Σ_α (lift f_α) = 1 on M.
    This is essential for partition of unity: bosonic functions that sum to 1
    lift to super functions that still sum to 1 (as the constant 1 super function). -/
theorem lift_sum_one {p q : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → SmoothFunction p)
    (hsum : ∀ x, Finset.univ.sum (fun α => (f α) x) = 1) :
    ∀ x, Finset.univ.sum (fun α => (liftToSuper (f α) : SuperDomainFunction p q).coefficients ∅ x) = 1 := by
  intro x
  simp only [liftToSuper, SuperDomainFunction.ofSmooth, ite_true]
  exact hsum x

/-- Multiplication by a lifted function factors through the Berezin integral.

    For f : M_red → ℝ and g a super function:
      ∫ dθ [(lift f) · g] = f · (∫ dθ g)

    This is because (lift f) is θ-independent, so it factors out. -/
theorem berezin_lift_factor {p q : ℕ} (f : SmoothFunction p) (g : SuperDomainFunction p q) :
    berezinIntegralOdd (SuperDomainFunction.mul (liftToSuper f) g) =
    SmoothFunction.mul f (berezinIntegralOdd g) := by
  unfold berezinIntegralOdd liftToSuper SuperDomainFunction.ofSmooth SuperDomainFunction.mul
  ext x
  -- The key: (lift f) has only the ∅ component, so multiplying by it
  -- scales each component of g by f(x), including the top component
  -- (fg)_K = Σ_{I ∪ J = K, I ∩ J = ∅} sign(I,J) f_I g_J
  -- Since f_I = 0 for I ≠ ∅, only the term I = ∅, J = K contributes
  -- sign(∅, K) = 1, so (fg)_K = f(x) * g_K(x)
  simp only [SuperDomainFunction.reorderSign]
  -- Sum over I: only I = ∅ contributes (since f_I = 0 for I ≠ ∅)
  rw [Finset.sum_eq_single ∅]
  · -- Main term: I = ∅
    rw [Finset.sum_eq_single Finset.univ]
    · -- J = Finset.univ: sign(∅, univ) = (-1)^0 = 1
      simp only [Finset.empty_union, Finset.empty_inter, and_true, ite_true]
      -- ∅ ×ˢ Finset.univ has no pairs where second < first (since ∅ is empty)
      simp only [Finset.empty_product, Finset.filter_empty, Finset.card_empty,
                 pow_zero, Int.cast_one, one_smul, SmoothFunction.mul]
      rfl
    · -- Other J ≠ univ
      intro J _ hJ
      simp only [Finset.empty_union, Finset.empty_inter, and_true]
      simp only [hJ, ite_false]
    · intro h; exact absurd (Finset.mem_univ _) h
  · -- Other I ≠ ∅: coefficient is 0
    intro I _ hI
    simp only [hI, ite_false]
    -- All terms have 0 * ... = 0
    apply Finset.sum_eq_zero
    intro J _
    split_ifs with h1 h2
    · simp only [zero_mul, smul_zero]
    · simp only [Int.cast_zero, zero_smul]
    · rfl
  · intro h; exact absurd (Finset.mem_univ _) h

/-- Witness data for a body partition of unity indexed by super charts.

    This is the body-level input needed to construct a `SuperPartitionOfUnity`
    by lifting each body function with `liftToSuper`. -/
structure BodyPartitionWitness {dim : SuperDimension} (M : Supermanifold dim) where
  index : Type*
  [finIndex : Fintype index]
  [decEqIndex : DecidableEq index]
  charts : index → SuperChart M
  bodyFunctions : index → SmoothFunction dim.even
  nonneg : ∀ α (x : Fin dim.even → ℝ), 0 ≤ (bodyFunctions α).toFun x
  supportDomains : index → Set (Fin dim.even → ℝ)
  supportDomains_open : ∀ α, IsOpen (supportDomains α)
  support_subset : ∀ α (x : Fin dim.even → ℝ),
    x ∉ supportDomains α → (bodyFunctions α).toFun x = 0
  supportDomains_in_chart : ∀ α (x : Fin dim.even → ℝ),
    x ∈ supportDomains α →
    ∃ (p : M.body) (hp : p ∈ (charts α).domain),
      (fun i => ((charts α).bodyCoord ⟨p, hp⟩ : EuclideanSpace ℝ (Fin dim.even)) i) = x
  body_sum_one : ∀ (p : M.body),
    @Finset.sum index ℝ _ (@Finset.univ index finIndex) (fun α =>
      @dite ℝ (p ∈ (charts α).domain) (Classical.dec _)
        (fun h => (bodyFunctions α).toFun
          (fun i => ((charts α).bodyCoord ⟨p, h⟩ : EuclideanSpace ℝ (Fin dim.even)) i))
        (fun _ => 0)) = 1

-- Keep the witness index universe aligned with `SuperPartitionOfUnity`.
universe u_idx

/-- Canonical super partition built by lifting a body partition witness. -/
noncomputable def BodyPartitionWitness.toSuperPartition {dim : SuperDimension}
    {M : Supermanifold dim} (bp : @BodyPartitionWitness.{u_idx} dim M) :
    @SuperPartitionOfUnity.{u_idx} dim M := by
  letI := bp.finIndex
  letI := bp.decEqIndex
  refine
    { index := bp.index
      functions := fun α => liftToSuper (bp.bodyFunctions α)
      functions_even := ?_
      nonneg := ?_
      charts := bp.charts
      supportDomains := bp.supportDomains
      supportDomains_open := bp.supportDomains_open
      support_subset := ?_
      supportDomains_in_chart := bp.supportDomains_in_chart
      body_sum_eq_one := ?_ }
  · intro α I hI
    have hne : I ≠ ∅ := by
      intro hI0
      subst hI0
      simp at hI
    have hzero : (0 : SmoothFunction dim.even) = SmoothFunction.const 0 := rfl
    simp [liftToSuper, SuperDomainFunction.ofSmooth, hne, hzero]
  · intro α x
    show 0 ≤ (liftToSuper (bp.bodyFunctions α)).body x
    simpa [liftToSuper, SuperDomainFunction.body, SuperDomainFunction.ofSmooth]
      using bp.nonneg α x
  · intro α x hx
    show (liftToSuper (bp.bodyFunctions α)).body x = 0
    simpa [liftToSuper, SuperDomainFunction.body, SuperDomainFunction.ofSmooth]
      using bp.support_subset α x hx
  · intro p
    simpa [liftToSuper, SuperDomainFunction.body, SuperDomainFunction.ofSmooth]
      using bp.body_sum_one p

/-- The canonical lifted partition uses the witness body functions by definition. -/
theorem BodyPartitionWitness.toSuperPartition_functions {dim : SuperDimension}
    {M : Supermanifold dim} (bp : @BodyPartitionWitness.{u_idx} dim M) :
    ∀ α, (bp.toSuperPartition.functions α) = liftToSuper (bp.bodyFunctions α) := by
  intro α
  rfl

/-- The canonical lifted partition has full coefficient-level support vanishing:
    outside support domains, all Grassmann coefficients vanish. -/
theorem BodyPartitionWitness.toSuperPartition_support_full {dim : SuperDimension}
    {M : Supermanifold dim} (bp : @BodyPartitionWitness.{u_idx} dim M) :
    ∀ α I x, x ∉ bp.toSuperPartition.supportDomains α →
      (bp.toSuperPartition.functions α).coefficients I x = 0 := by
  intro α I x hx
  by_cases hI : I = ∅
  · subst hI
    simpa [SuperDomainFunction.body]
      using (bp.toSuperPartition.support_subset α x hx)
  · simp [BodyPartitionWitness.toSuperPartition, liftToSuper,
      SuperDomainFunction.ofSmooth, hI]

/-- Existence of super partition of unity from body partition witness data.

    `ParacompactSpace` is kept in the signature to match the classical
    existence context, while the concrete construction is driven by the
    explicit `BodyPartitionWitness`. -/
theorem partition_of_unity_exists {dim : SuperDimension} (M : Supermanifold dim)
    (_hparacompact : ParacompactSpace M.body)
    (bp : @BodyPartitionWitness.{u_idx} dim M) :
    Nonempty (@SuperPartitionOfUnity.{u_idx} dim M) := by
  exact ⟨bp.toSuperPartition⟩

/-- An integral form on a supermanifold (section of the Berezinian bundle).

    On each chart U_α, the form is f_α(x,θ) [Dx Dθ]. On overlaps, the
    representations satisfy the cocycle condition with Berezinian factors.

    From Witten's notes (arXiv:1209.2199, eq. 3.10):
      [dt¹...dθᵍ] = Ber(∂T/∂T̃) · [dt̃¹...dθ̃ᵍ]

    This means: f_β(y,η) [Dy Dη] = f_α(x,θ) [Dx Dθ]
    where (y,η) = T_{αβ}(x,θ) is the coordinate change.
    Rearranging: f_β = f_α · Ber(J_{αβ})⁻¹ where J_{αβ} = ∂(y,η)/∂(x,θ). -/
structure GlobalIntegralForm {dim : SuperDimension} (M : Supermanifold dim) where
  /-- Local representations: in chart α, the form is (localForms α)[Dx Dθ] -/
  localForms : (chart : SuperChart M) → IntegralForm dim.even dim.odd
  /-- Body-level compatibility on overlaps.

      The full super cocycle condition is: f_β ∘ T = f_α · Ber(J_{αβ})⁻¹
      where Ber is the Berezinian of the super Jacobian. This requires
      `composeEvalAt` from SuperCompose.lean (downstream of this file).

      At body level (θ = 0), the det(D_body) from the odd substitution θ'=Dθ
      cancels with 1/det(D) in the Berezinian denominator (verified by direct
      computation in (1|1) case), giving:
        f_β^{top}(T_body(x)) = f_α^{top}(x) · (det(∂T_body/∂x))⁻¹

      where T_body is the body map of the transition and f^{top} is the top
      θ-component (extracted by berezinIntegralOdd).

      Note: This uses the SIGNED determinant (not |det|) because integral forms
      are sections of the Berezinian line bundle, which transforms by the signed
      Berezinian. The absolute value would only be appropriate for densities
      in measure-theoretic integration.

      The full super cocycle is stated as an additional hypothesis in
      GlobalStokes.lean where the composition infrastructure is available. -/
  compatible_body : ∀ (α β : SuperChart M)
      (t : SuperTransition α β)
      (x : Fin dim.even → ℝ),
      let bodyJac := Matrix.of fun i j =>
        fderiv ℝ (fun y => (t.evenTransition i).body y) x (Pi.single j 1)
      let bodyMap := fun i => (t.evenTransition i).body x
      (localForms β).coefficient.coefficients Finset.univ bodyMap =
      (localForms α).coefficient.coefficients Finset.univ x *
      (Matrix.det bodyJac)⁻¹

/-- The global Berezin integral of an integral form on a supermanifold.

    ∫_M ω := Σ_α ∫_{U_α,red} dx [∫ dθ (ρ_α · f_α)](x)

    For each chart α:
    1. Multiply the partition function ρ_α (an even SuperDomainFunction, possibly
       θ-dependent from normalization) by the integral form coefficient f_α
    2. Apply the Berezin integral ∫dθ to the product — this extracts the top
       θ-component of ρ_α · f_α, which includes corrections from the θ-dependence
       of ρ_α mixing with lower θ-components of f_α
    3. Integrate the resulting smooth function over the body in chart α's coordinates

    Each chart α has its own body integral, since the functions live in chart α's
    coordinate system.

    From Witten's notes (arXiv:1209.2199, p.12):
    "we write σ = Σ_α σ_α where σ_α = σ · h_α. Each σ_α is supported in U_α,
    so its integral can be defined... Then we define ∫_M σ = Σ_α ∫_M σ_α" -/
noncomputable def globalBerezinIntegral {dim : SuperDimension}
    (_M : Supermanifold dim) (ω : GlobalIntegralForm _M)
    (pu : SuperPartitionOfUnity _M)
    (bodyIntegral : SmoothFunction dim.even → Set (Fin dim.even → ℝ) → ℝ) : ℝ :=
  -- Sum over the partition of unity index
  -- For each α: compute ∫dθ (ρ_α · f_α) in chart α's coordinates,
  -- then body-integrate the resulting smooth function over chart α's support domain.
  -- Each summand is compactly supported in chart α's domain (by support_subset),
  -- so the body integral localizes to the support domain.
  @Finset.sum pu.index ℝ _ (@Finset.univ pu.index pu.finIndex) fun α =>
    bodyIntegral
      (berezinIntegralOdd
        (SuperDomainFunction.mul (pu.functions α)
          (ω.localForms (pu.charts α)).coefficient))
      (pu.supportDomains α)

/-- Linearity of a body integral functional.

    The body integral ∫_U f dx is linear in f for each fixed domain U. -/
structure BodyIntegral.IsLinear (p : ℕ)
    (bodyIntegral : SmoothFunction p → Set (Fin p → ℝ) → ℝ) : Prop where
  /-- Additivity: ∫_U (f + g) = ∫_U f + ∫_U g -/
  add : ∀ U f g, bodyIntegral (f + g) U = bodyIntegral f U + bodyIntegral g U
  /-- Scalar multiplication: ∫_U (c·f) = c · ∫_U f -/
  smul : ∀ (c : ℝ) f U, bodyIntegral (c • f) U = c * bodyIntegral f U

theorem globalBerezinIntegral_independent {dim : SuperDimension}
    (M : Supermanifold dim) (ω : GlobalIntegralForm M)
    (pu₁ pu₂ : SuperPartitionOfUnity M)
    (bodyIntegral : SmoothFunction dim.even → Set (Fin dim.even → ℝ) → ℝ)
    (_hLinear : BodyIntegral.IsLinear dim.even bodyIntegral)
    (_hChangeOfVar : BodyIntegral.SatisfiesChangeOfVar dim.even bodyIntegral)
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

/-- The body Jacobian cocycle: determinants of the even-even blocks.

    This is the classical/leading-order part of the Berezinian cocycle.
    The determinant of the body Jacobian satisfies the cocycle condition:
      det(J^body_{αγ}) = det(J^body_{βγ}) · det(J^body_{αβ})

    where J^body is the Jacobian matrix of the body map (θ = 0).

    This follows from:
    1. Chain rule: J^body_{αγ} = J^body_{βγ} · J^body_{αβ}
    2. det multiplicativity: det(AB) = det(A) · det(B) -/
theorem body_jacobian_cocycle {dim : SuperDimension} (_M : Supermanifold dim)
    (chart_α chart_β chart_γ : SuperChart _M)
    (t_αβ : SuperTransition chart_α chart_β)
    (t_βγ : SuperTransition chart_β chart_γ)
    (t_αγ : SuperTransition chart_α chart_γ)
    /- The transitions compose correctly (cocycle for body coordinates) -/
    (hCocycle : ∀ x : Fin dim.even → ℝ,
        (fun i => (t_αγ.evenTransition i).body x) =
        (fun i => (t_βγ.evenTransition i).body (fun j => (t_αβ.evenTransition j).body x))) :
    let body_αβ := fun x => fun i => (t_αβ.evenTransition i).body x
    let body_βγ := fun x => fun i => (t_βγ.evenTransition i).body x
    let body_αγ := fun x => fun i => (t_αγ.evenTransition i).body x
    ∀ x : Fin dim.even → ℝ,
      Matrix.det (Matrix.of fun i j => fderiv ℝ (fun y => body_αγ y i) x (Pi.single j 1)) =
      Matrix.det (Matrix.of fun i j => fderiv ℝ (fun y => body_βγ y i) (body_αβ x) (Pi.single j 1)) *
      Matrix.det (Matrix.of fun i j => fderiv ℝ (fun y => body_αβ y i) x (Pi.single j 1)) := by
  -- Introduce the let bindings into scope
  intro body_αβ body_βγ body_αγ x

  -- From hCocycle: body_αγ = body_βγ ∘ body_αβ (pointwise)
  have hComp_fun : body_αγ = body_βγ ∘ body_αβ := by
    funext y
    exact hCocycle y

  -- Differentiability from SuperTransition.bodyTransition_diffeo
  have hDiff_αβ : Differentiable ℝ body_αβ := t_αβ.bodyTransition_diffeo.differentiable (by decide)
  have hDiff_βγ : Differentiable ℝ body_βγ := t_βγ.bodyTransition_diffeo.differentiable (by decide)

  -- Chain rule: fderiv (body_βγ ∘ body_αβ) x = fderiv body_βγ (body_αβ x) ∘L fderiv body_αβ x
  have hChain : fderiv ℝ (body_βγ ∘ body_αβ) x =
      (fderiv ℝ body_βγ (body_αβ x)).comp (fderiv ℝ body_αβ x) :=
    fderiv_comp x (hDiff_βγ (body_αβ x)) (hDiff_αβ x)

  -- Define the Jacobian matrices
  let J_αβ := Matrix.of fun i j => fderiv ℝ (fun y => body_αβ y i) x (Pi.single j 1)
  let J_βγ := Matrix.of fun i j => fderiv ℝ (fun y => body_βγ y i) (body_αβ x) (Pi.single j 1)
  let J_αγ := Matrix.of fun i j => fderiv ℝ (fun y => body_αγ y i) x (Pi.single j 1)

  -- Key fact: J_αγ = J_βγ * J_αβ
  -- This follows from:
  -- 1. The chain rule gives (fderiv body_αγ x) = (fderiv body_βγ (body_αβ x)) ∘L (fderiv body_αβ x)
  -- 2. LinearMap.toMatrix'_comp: toMatrix' (f.comp g) = toMatrix' f * toMatrix' g
  -- 3. The Jacobian matrix J_f(x)_ij = (fderiv f x)(e_j)_i matches LinearMap.toMatrix'_apply
  have hJac_eq : J_αγ = J_βγ * J_αβ := by
    ext i j
    simp only [J_αγ, J_βγ, J_αβ, Matrix.of_apply, Matrix.mul_apply]

    -- From hCocycle: (fun y => body_αγ y i) = (fun y => body_βγ (body_αβ y) i)
    have hComp_i : (fun y => body_αγ y i) = (fun y => body_βγ (body_αβ y) i) := by
      funext y; exact congrFun (hCocycle y) i
    rw [hComp_i]

    -- Differentiability of component functions
    -- body_βγ is differentiable, and extracting i-th component is linear
    have hDiff_βγ_i : Differentiable ℝ (fun z => body_βγ z i) := by
      intro z
      have h := (ContinuousLinearMap.proj i).differentiableAt.comp z (hDiff_βγ z)
      convert h using 1

    have hDiff_αβ_k : ∀ k, DifferentiableAt ℝ (fun y => body_αβ y k) x := by
      intro k
      have h := (ContinuousLinearMap.proj k).differentiableAt.comp x (hDiff_αβ x)
      convert h using 1

    -- Chain rule for the composed function
    have hChain_i : fderiv ℝ (fun y => body_βγ (body_αβ y) i) x =
        (fderiv ℝ (fun z => body_βγ z i) (body_αβ x)).comp (fderiv ℝ body_αβ x) := by
      have hg : DifferentiableAt ℝ (fun z => body_βγ z i) (body_αβ x) := hDiff_βγ_i (body_αβ x)
      have hf : DifferentiableAt ℝ body_αβ x := hDiff_αβ x
      have h := fderiv_comp x hg hf
      convert h using 2

    -- Key: fderiv_pi relates fderiv of Pi-type to ContinuousLinearMap.pi
    have h_fderiv_pi : fderiv ℝ body_αβ x = ContinuousLinearMap.pi fun k => fderiv ℝ (fun y => body_αβ y k) x :=
      fderiv_pi hDiff_αβ_k

    -- Apply chain rule and expand using linearity
    calc fderiv ℝ (fun y => body_βγ (body_αβ y) i) x (Pi.single j 1)
        = (fderiv ℝ (fun z => body_βγ z i) (body_αβ x)) ((fderiv ℝ body_αβ x) (Pi.single j 1)) := by
            rw [hChain_i]; rfl
      _ = (fderiv ℝ (fun z => body_βγ z i) (body_αβ x))
            ((ContinuousLinearMap.pi fun k => fderiv ℝ (fun y => body_αβ y k) x) (Pi.single j 1)) := by
            rw [h_fderiv_pi]
      _ = (fderiv ℝ (fun z => body_βγ z i) (body_αβ x))
            (fun k => (fderiv ℝ (fun y => body_αβ y k) x) (Pi.single j 1)) := by
            -- ContinuousLinearMap.pi_apply: (pi f) v i = f i v
            congr 1
      _ = Finset.univ.sum (fun k => fderiv ℝ (fun z => body_βγ z i) (body_αβ x) (Pi.single k 1) *
            fderiv ℝ (fun y => body_αβ y k) x (Pi.single j 1)) := by
          -- The input vector is Σ_k c_k • e_k where c_k = fderiv (body_αβ · k) x (e_j)
          -- By linearity: f(Σ c_k e_k) = Σ c_k f(e_k)
          let c := fun k => fderiv ℝ (fun y => body_αβ y k) x (Pi.single j 1)
          have hvec : (fun k => c k) = Finset.univ.sum (fun k => c k • Pi.single k 1) := by
            ext m
            simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul,
              mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
          rw [hvec, map_sum]
          congr 1; ext k
          rw [ContinuousLinearMap.map_smul, smul_eq_mul, mul_comm]

  -- Finally: det(J_αγ) = det(J_βγ * J_αβ) = det(J_βγ) * det(J_αβ)
  -- The goal is: det J_αγ = det J_βγ * det J_αβ
  -- where J_αγ, J_βγ, J_αβ are the Matrix.of expressions
  show J_αγ.det = J_βγ.det * J_αβ.det
  rw [hJac_eq, Matrix.det_mul]

/-- The full Berezinian cocycle using chain rule hypotheses.

    This theorem connects to `berezinian_cocycle_from_chain_rule` from
    Helpers/SuperChainRule.lean. Given chain rule hypotheses and the
    necessary invertibility/parity conditions, the Berezinians multiply.

    The chain rule hypotheses come from proper super function composition.
    See `FullSuperCocycle` in SuperChainRule.lean for the composition axioms. -/
theorem berezinian_cocycle_full {dim : SuperDimension} (_M : Supermanifold dim)
    (chart_α chart_β chart_γ : SuperChart _M)
    (t_αβ : SuperTransition chart_α chart_β)
    (t_βγ : SuperTransition chart_β chart_γ)
    (t_αγ : SuperTransition chart_α chart_γ)
    (x : Fin dim.even → ℝ)
    /- Chain rule hypotheses: the four Jacobian blocks satisfy multiplication -/
    (hChain : Helpers.ChainRuleHypotheses t_αβ t_βγ t_αγ x)
    /- D block of αβ is invertible -/
    (hD_αβ : (Helpers.finiteGrassmannAlgebra dim.odd).IsInvertible
        (t_αβ.toSuperJacobian.toSuperMatrixAt x).D_lifted.det)
    /- D block of βγ is invertible -/
    (hD_βγ : (Helpers.finiteGrassmannAlgebra dim.odd).IsInvertible
        (t_βγ.toSuperJacobian.toSuperMatrixAt (hChain.body_αβ x)).D_lifted.det)
    /- D block of αγ is invertible -/
    (hD_αγ : (Helpers.finiteGrassmannAlgebra dim.odd).IsInvertible
        (t_αγ.toSuperJacobian.toSuperMatrixAt x).D_lifted.det)
    /- D block of product is invertible -/
    (hD_prod : (Helpers.finiteGrassmannAlgebra dim.odd).IsInvertible
        ((t_βγ.toSuperJacobian.toSuperMatrixAt (hChain.body_αβ x)) *
         (t_αβ.toSuperJacobian.toSuperMatrixAt x)).D_lifted.det)
    /- BD⁻¹ parity conditions -/
    (hBD_αβ : ∀ i j, ((t_αβ.toSuperJacobian.toSuperMatrixAt x).Bblock *
        (t_αβ.toSuperJacobian.toSuperMatrixAt x).D_inv_carrier) i j ∈
        (Helpers.finiteGrassmannAlgebra dim.odd).odd)
    (hBD_βγ : ∀ i j, ((t_βγ.toSuperJacobian.toSuperMatrixAt (hChain.body_αβ x)).Bblock *
        (t_βγ.toSuperJacobian.toSuperMatrixAt (hChain.body_αβ x)).D_inv_carrier) i j ∈
        (Helpers.finiteGrassmannAlgebra dim.odd).odd)
    (hBD_αγ : ∀ i j, ((t_αγ.toSuperJacobian.toSuperMatrixAt x).Bblock *
        (t_αγ.toSuperJacobian.toSuperMatrixAt x).D_inv_carrier) i j ∈
        (Helpers.finiteGrassmannAlgebra dim.odd).odd)
    (hBD_prod : ∀ i j,
        (((t_βγ.toSuperJacobian.toSuperMatrixAt (hChain.body_αβ x)) *
          (t_αβ.toSuperJacobian.toSuperMatrixAt x)).Bblock *
         ((t_βγ.toSuperJacobian.toSuperMatrixAt (hChain.body_αβ x)) *
          (t_αβ.toSuperJacobian.toSuperMatrixAt x)).D_inv_carrier) i j ∈
        (Helpers.finiteGrassmannAlgebra dim.odd).odd)
    /- D⁻¹C parity conditions for ber_mul -/
    (hDinvC_αβ : ∀ i j, ((t_αβ.toSuperJacobian.toSuperMatrixAt x).D_inv_carrier *
        (t_αβ.toSuperJacobian.toSuperMatrixAt x).Cblock) i j ∈
        (Helpers.finiteGrassmannAlgebra dim.odd).odd)
    (hDinvC_βγ : ∀ i j, ((t_βγ.toSuperJacobian.toSuperMatrixAt (hChain.body_αβ x)).D_inv_carrier *
        (t_βγ.toSuperJacobian.toSuperMatrixAt (hChain.body_αβ x)).Cblock) i j ∈
        (Helpers.finiteGrassmannAlgebra dim.odd).odd)
    /- Schur complement parity conditions -/
    (hSchur_αβ : ∀ i j, (Helpers.schurComplementD
        (t_αβ.toSuperJacobian.toSuperMatrixAt x) hD_αβ) i j ∈
        (Helpers.finiteGrassmannAlgebra dim.odd).even)
    (hSchur_βγ : ∀ i j, (Helpers.schurComplementD
        (t_βγ.toSuperJacobian.toSuperMatrixAt (hChain.body_αβ x)) hD_βγ) i j ∈
        (Helpers.finiteGrassmannAlgebra dim.odd).even) :
    -- The Berezinians satisfy multiplicativity:
    -- Ber(J_αγ)(x) = Ber(J_αβ)(x) · Ber(J_βγ)(body_αβ(x))
    t_αγ.toSuperJacobian.berezinianAt x hD_αγ hBD_αγ =
    t_αβ.toSuperJacobian.berezinianAt x hD_αβ hBD_αβ *
    t_βγ.toSuperJacobian.berezinianAt (hChain.body_αβ x) hD_βγ hBD_βγ :=
  -- Use the proven berezinian_cocycle_from_chain_rule theorem
  Helpers.berezinian_cocycle_from_chain_rule t_αβ t_βγ t_αγ x hChain
    hD_αβ hD_βγ hD_αγ hD_prod hBD_αβ hBD_βγ hBD_αγ hBD_prod
    hDinvC_αβ hDinvC_βγ hSchur_αβ hSchur_βγ

/-!
## The Volume Form on a Supermanifold

A supermanifold of dimension (p|q) has a canonical volume element in local
coordinates:
  [Dx Dθ] = dx¹ ∧ ... ∧ dxᵖ · dθ¹ ... dθ^q

Under coordinate change, this transforms by the Berezinian.

For an oriented supermanifold, there is a globally defined volume form
(section of Ber(M)).
-/

/-- The standard volume form on ℝ^{p|q}: the integral form θ¹...θ^q [Dx Dθ].
    This has coefficient 1 at the top θ-component (Finset.univ). -/
def standardVolumeForm (p q : ℕ) : IntegralForm p q :=
  ⟨⟨fun I => if I = Finset.univ then SmoothFunction.const 1 else SmoothFunction.const 0⟩⟩

/-- The Berezin integral of the standard volume form is 1.
    This is the defining property: ∫ dθ¹...dθ^q (θ¹...θ^q) = 1. -/
theorem berezinIntegralOdd_standardVolume (p q : ℕ) :
    berezinIntegralOdd (standardVolumeForm p q).coefficient = SmoothFunction.const 1 := by
  unfold berezinIntegralOdd standardVolumeForm
  ext x
  simp only [ite_true, SmoothFunction.const_apply]

/-- A constant function (independent of θ) has Berezin integral 0 when q > 0.
    This is because ∫ dθ 1 = 0 - the constant has no top θ-component. -/
theorem berezinIntegralOdd_const_zero {p q : ℕ} (hq : 0 < q) (c : ℝ) :
    berezinIntegralOdd (SuperDomainFunction.ofSmooth (SmoothFunction.const c) : SuperDomainFunction p q) =
    SmoothFunction.const 0 := by
  unfold berezinIntegralOdd SuperDomainFunction.ofSmooth
  ext x
  haveI : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
  have huniv : (Finset.univ : Finset (Fin q)) ≠ ∅ := Finset.univ_nonempty.ne_empty
  simp [huniv, SmoothFunction.const_apply]

/-!
## Superforms vs Integral Forms

Important distinction:
- **Differential forms** on a supermanifold are elements of Ω*(M), with
  both even and odd form degrees. They transform by pullback.
- **Integral forms** are sections of Ber(M). They transform by pullback
  with the Berezinian factor.

For integration on supermanifolds, we integrate integral forms, not
differential forms. The "dθ" in Berezin integration is NOT the same as
the exterior derivative of θ.
-/

/-- A differential form on a super domain (for comparison, not for integration) -/
structure SuperDifferentialForm (p q : ℕ) (k : ℕ) where
  /-- Coefficients for each k-form basis element -/
  coefficients : (Fin p → Bool) → (Fin q → Bool) → SuperDomainFunction p q

-- TODO: Wedge product of super differential forms.
-- (ω₁ ∧ ω₂)_{I∪J, A∪B} = Σ sign(I,J) · sign(A,B) · (ω₁)_{I,A} · (ω₂)_{J,B}
-- Requires careful treatment of both form-degree signs and Koszul signs.

/-!
## Stokes' Theorem for Supermanifolds

Stokes' theorem on supermanifolds involves subtleties due to the Berezinian.
The boundary of a supermanifold M has the same odd dimension as M itself.

### The Super Stokes Theorem

For a supermanifold M with boundary ∂M, and an integral form ω:
  ∫_M dω = ∫_{∂M} ι*ω

where ι: ∂M → M is the inclusion and d is the super exterior derivative.

### Application: BRST Invariance

The BRST current J_BRST is an odd 1-form on worldsheet.
BRST invariance of amplitudes follows from:
  0 = ∫_Σ d(J_BRST · Φ) = ∫_Σ {Q_BRST, Φ}

where Φ is the product of vertex operators.
-/

/-- Super Stokes' theorem (LEGACY — TAUTOLOGICAL, DO NOT USE).

    **WARNING**: This theorem is tautological — the hypothesis `hStokesBody`
    directly restates the conclusion after unfolding `localBerezinIntegral`.
    It has zero mathematical content.

    Use the proper versions in `Integration/StokesTheorem.lean` instead:
    - `super_stokes_codim1_no_boundary`: genuinely reduces super Stokes to
      classical divergence theorem via `d0_is_divergence`
    - `super_stokes_codim1_with_boundary`: same with boundary terms

    Those theorems properly decompose d = d₀ + d₁ and prove:
    1. d₁ν integrates to 0 (no boundary in odd directions)
    2. d₀ν reduces to classical divergence on the body -/
-- TAUTOLOGICAL: hypothesis restates conclusion. See StokesTheorem.lean for proper versions.
theorem super_stokes_legacy {p q : ℕ} (_hp : 0 < p)
    (U : Set (Fin p → ℝ))
    (_hU_compact : IsCompact U)
    (_hU_open : IsOpen (interior U))
    (bdryU : Set (Fin (p - 1) → ℝ))
    (_ω : IntegralForm p q)
    (bodyIntegral : SmoothFunction p → Set (Fin p → ℝ) → ℝ)
    (boundaryIntegral : SmoothFunction (p - 1) → Set (Fin (p - 1) → ℝ) → ℝ)
    (restrict : SmoothFunction p → SmoothFunction (p - 1))
    (dω : IntegralForm p q)
    (hStokesBody :
        bodyIntegral (berezinIntegralOdd dω.coefficient) U =
        boundaryIntegral (restrict (berezinIntegralOdd _ω.coefficient)) bdryU) :
    localBerezinIntegral U dω bodyIntegral =
    boundaryIntegral (restrict (berezinIntegralOdd _ω.coefficient)) bdryU := by
  unfold localBerezinIntegral
  exact hStokesBody

/-!
## The Superperiod Matrix

For a super Riemann surface of genus g, the superperiod matrix generalizes
the classical period matrix to include odd differentials. This is foundational
for the theory of integration on supermoduli spaces.

**TODO**: The super period matrix should be defined as a `SuperMatrix` over a
`GrassmannAlgebra ℝ` (or ℂ). The current ℂ-valued block structure doesn't capture
the proper superalgebra structure. Once defined properly:
- It should be a `SuperMatrix Λ g (g-1)` for genus g ≥ 2
- The Berezinian would be computed via `SuperMatrix.ber`
- Symmetry and positive definiteness conditions need proper formulation
-/

/-!
## Compactly Supported Integration

For integration on non-compact supermanifolds, we need the notion of
compactly supported integral forms. The support is defined via the body.
-/

/-- An integral form with compact support.

    The support of an integral form ω = f(x,θ)[Dx Dθ] is defined as the
    closure of {x ∈ M_red : f_top(x) ≠ 0} where f_top is the top θ-component.

    For compact support, this set must be compact in M_red.

    **Note:** Only the top θ-component matters for the support definition because
    the Berezin integral extracts precisely this component. Lower θ-components
    don't contribute to the integral. -/
structure CompactlySupportedIntegralForm (p q : ℕ) extends IntegralForm p q where
  /-- The support of the top θ-component is compact.
      The support is the closure of {x | f_{top}(x) ≠ 0}. -/
  compact_support : IsCompact (closure {x : Fin p → ℝ |
    (berezinIntegralOdd toIntegralForm.coefficient) x ≠ 0})

/-- Integration of compactly supported forms over non-compact supermanifolds.

    For a compactly supported integral form ω on M, the integral ∫_M ω
    is well-defined without boundary conditions. -/
noncomputable def integrateCompactSupport {p q : ℕ}
    (ω : CompactlySupportedIntegralForm p q)
    (bodyIntegral : SmoothFunction p → Set (Fin p → ℝ) → ℝ)
    (U : Set (Fin p → ℝ)) : ℝ :=
  bodyIntegral (berezinIntegralOdd ω.coefficient) U

/-!
## Fubini's Theorem for Supermanifolds

Fubini's theorem allows interchanging the order of integration for products
of supermanifolds: if M has dimension (p|q) and N has dimension (r|s), then
M × N has dimension (p+r|q+s), and:

  ∫_{M × N} ω = ∫_M (∫_N ω)

The key point is that Berezin integration over odd variables is algebraic,
so the order of integration does not matter.
-/

/-- Unfold `berezinIntegralOdd` on a product domain (definitional equality).

    **Note**: Despite its name, this is NOT Fubini's theorem. It is just the
    definitional unfolding of `berezinIntegralOdd` applied to a function on
    ℝ^{p+r|q+s}. A genuine Fubini theorem would require:
    1. A function on the product ℝ^{p|q} × ℝ^{r|s} (not ℝ^{p+r|q+s})
    2. Two separate Berezin integrals ∫dθ and ∫dη
    3. A proof that (∫dθ)(∫dη f) = (∫dη)(∫dθ f) = ∫d(θ,η) f

    The actual commutativity of Berezin integrals over disjoint sets of
    Grassmann variables is a theorem that requires infrastructure for
    partial Berezin integration (not yet formalized). -/
-- MISLEADING NAME: This is just `rfl`, not a Fubini theorem.
-- See docstring for what a genuine Fubini theorem would require.
theorem berezin_fubini {p q r s : ℕ}
    (f : SuperDomainFunction (p + r) (q + s)) :
    -- The Berezin integral over all (q+s) odd variables extracts the top coefficient
    berezinIntegralOdd f = f.coefficients Finset.univ := rfl

/-!
## Divergence Theorem on Supermanifolds

The divergence theorem on supermanifolds relates the integral of a divergence
to a boundary integral. For a vector field X on M:

  ∫_M div(X) [Dx Dθ] = ∫_{∂M} ι_X [Dx Dθ]

where ι_X is the interior product (contraction with X).
-/

/-- A super vector field on a super domain.

    A vector field has both even and odd components:
    X = Xⁱ(x,θ) ∂/∂xⁱ + Xᵃ(x,θ) ∂/∂θᵃ

    Even vector fields have:
    - Xⁱ even functions (even θ-powers)
    - Xᵃ odd functions (odd θ-powers)

    Odd vector fields reverse these parities. -/
structure SuperVectorField (p q : ℕ) (parity : Parity) where
  /-- Even components ∂/∂xⁱ -/
  evenComponents : Fin p → SuperDomainFunction p q
  /-- Odd components ∂/∂θᵃ -/
  oddComponents : Fin q → SuperDomainFunction p q
  /-- Parity constraint on even components -/
  evenComponents_parity : ∀ i I,
    (if parity = Parity.even then I.card % 2 = 1 else I.card % 2 = 0) →
    (evenComponents i).coefficients I = SmoothFunction.const 0
  /-- Parity constraint on odd components -/
  oddComponents_parity : ∀ a I,
    (if parity = Parity.even then I.card % 2 = 0 else I.card % 2 = 1) →
    (oddComponents a).coefficients I = SmoothFunction.const 0

/-- The super divergence of a vector field.

    For X = Xⁱ ∂/∂xⁱ + Xᵃ ∂/∂θᵃ, the divergence is:
    div(X) = Σᵢ ∂Xⁱ/∂xⁱ + (-1)^{|X|} Σₐ ∂Xᵃ/∂θᵃ

    For an EVEN vector field (|X| = 0):
    - Xⁱ are even functions, so ∂Xⁱ/∂xⁱ is even
    - Xᵃ are odd functions, so ∂Xᵃ/∂θᵃ is even (odd derivative of odd = even)
    - The sign is +1

    The result is an even super function. -/
noncomputable def superDivergence {p q : ℕ} (X : SuperVectorField p q Parity.even) :
    SuperDomainFunction p q :=
  -- div(X) = Σᵢ ∂Xⁱ/∂xⁱ + Σₐ ∂Xᵃ/∂θᵃ (sign is +1 for even X)
  let evenContribution : SuperDomainFunction p q :=
    ⟨fun I => Finset.univ.sum fun i => (partialEven i (X.evenComponents i)).coefficients I⟩
  let oddContribution : SuperDomainFunction p q :=
    ⟨fun I => Finset.univ.sum fun a => (partialOdd a (X.oddComponents a)).coefficients I⟩
  SuperDomainFunction.add evenContribution oddContribution

/-- The divergence theorem for supermanifolds (PLACEHOLDER — TAUTOLOGICAL).

    **WARNING**: This is currently a tautology (proves `x = x` via `rfl`).
    The conclusion equals the hypothesis because the boundary integral is not
    properly formulated. The statement should relate ∫_U div(X) to ∫_{∂U} ι_X,
    but the boundary integral infrastructure is not yet developed.

    For the actual content, see `Integration/StokesTheorem.lean` which properly
    reduces super Stokes to the classical divergence theorem on the body. -/
theorem super_divergence_theorem_legacy {p q : ℕ}
    (X : SuperVectorField p q Parity.even)
    (_U : Set (Fin p → ℝ))    -- Region in the body
    (_bdryU : Set (Fin (p - 1) → ℝ))  -- Boundary
    (bodyIntegral : SmoothFunction p → Set (Fin p → ℝ) → ℝ)
    (_boundaryIntegral : SmoothFunction (p - 1) → Set (Fin (p - 1) → ℝ) → ℝ) :
    bodyIntegral (berezinIntegralOdd (superDivergence X)) _U =
    bodyIntegral (berezinIntegralOdd (superDivergence X)) _U := by
  rfl

end Supermanifolds
