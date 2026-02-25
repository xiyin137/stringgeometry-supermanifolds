/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license.
-/
import StringGeometry.Supermanifolds.Helpers.NilpotentTaylor
import StringGeometry.Supermanifolds.Helpers.GrassmannSmooth
import StringGeometry.Supermanifolds.Integration.Core

/-!
# Super Function Composition

Proper composition of super domain functions with coordinate changes on ℝ^{p|q}.

## Mathematical Setup

A `SuperDomainFunction p q` is f(x, θ) = Σ_{I ⊆ {1,...,q}} f_I(x) θ^I where f_I : ℝ^p → ℝ smooth.

A `SuperCoordChange p q` is a coordinate transformation φ = (y, η) where:
- y_k(x,θ) = (φ.evenMap k)(x,θ) — even coordinate functions
- η_a(x,θ) = (φ.oddMap a)(x,θ) — odd coordinate functions

The composition is:
  (f ∘ φ)(x,θ) = Σ_I f_I(y(x,θ)) · η(x,θ)^I

where f_I(y(x,θ)) is computed using the nilpotent Taylor expansion from NilpotentTaylor.lean.
The Taylor expansion terminates because the soul parts of y_k are nilpotent in Λ_q.

## Main Definitions

* `grassmannMonomial` - ordered product η_{a₁} · η_{a₂} · ... · η_{aₖ}
* `composeEvalAt` - evaluate f ∘ φ at a body point x, returning a Grassmann algebra element
* `SuperDomainFunction.composeProper` - full composition as a SuperDomainFunction

## Important: Commutative Ring, Not Field

The Grassmann algebra FiniteGrassmannCarrier q is a commutative ring with ZERO DIVISORS,
not a field. All scalar operations use ℝ-multiplication via SMul, never Grassmann division.

## References

* Witten, "Notes On Supermanifolds And Integration" (1209.2199), §3
* Rogers, "Supermanifolds" (2007), Chapter 4
-/

noncomputable section

namespace Supermanifolds

open Supermanifolds.Helpers FiniteGrassmannCarrier

/-! ## Grassmann Monomials -/

/-- Ordered Grassmann monomial: for I = {a₁ < a₂ < ... < aₖ},
    grassmannMonomial eta I = η_{a₁} · η_{a₂} · ... · η_{aₖ}

    For I = ∅, this is the empty product = 1 (multiplicative identity). -/
def grassmannMonomial {q : ℕ} (eta : Fin q → FiniteGrassmannCarrier q)
    (I : Finset (Fin q)) : FiniteGrassmannCarrier q :=
  ((I.sort (· ≤ ·)).map eta).prod

/-- The empty monomial is the multiplicative identity. -/
@[simp]
theorem grassmannMonomial_empty {q : ℕ} (eta : Fin q → FiniteGrassmannCarrier q) :
    grassmannMonomial eta ∅ = 1 := by
  simp [grassmannMonomial]

/-- Singleton monomial is just the element itself. -/
theorem grassmannMonomial_singleton {q : ℕ} (eta : Fin q → FiniteGrassmannCarrier q)
    (a : Fin q) :
    grassmannMonomial eta {a} = eta a := by
  simp [grassmannMonomial, Finset.sort_singleton, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one]

/-! ## Pointwise Composition -/

/-- Evaluate the composition f ∘ φ at a body point x, returning a Grassmann algebra element.

    Formula: (f ∘ φ)(x) = Σ_I smoothTaylorGrassmann(f_I, y(x)) · grassmannMonomial(η(x), I)

    where:
    - y_k(x) = (φ.evenMap k).evalAtPoint x ∈ FiniteGrassmannCarrier q
    - η_a(x) = (φ.oddMap a).evalAtPoint x ∈ FiniteGrassmannCarrier q
    - f_I(y(x)) is the nilpotent Taylor expansion of the I-th coefficient of f

    The Taylor expansion terminates because the soul parts of y_k(x) are nilpotent
    in the Grassmann algebra Λ_q (by grassmann_soul_nilpotent).

    The evalAtPoint of each coordinate function produces a Grassmann element:
    y_k(x) = Σ_J (φ.evenMap k).coefficients J x · θ^J
    whose body is (φ.evenMap k).body x and whose soul has no constant term.

    IMPORTANT: The 1/n! factors in the Taylor expansion use ℝ-scalar multiplication,
    never division in the Grassmann algebra (which has zero divisors). -/
def composeEvalAt {p q : ℕ}
    (f : SuperDomainFunction p q) (φ : SuperCoordChange p q)
    (x : Fin p → ℝ) : FiniteGrassmannCarrier q :=
  let y : Fin p → FiniteGrassmannCarrier q :=
    fun k => (φ.evenMap k).evalAtPoint x
  let eta : Fin q → FiniteGrassmannCarrier q :=
    fun a => (φ.oddMap a).evalAtPoint x
  Finset.univ.sum fun (I : Finset (Fin q)) =>
    smoothTaylorGrassmann (f.coefficients I) y * grassmannMonomial eta I

/-! ## Smoothness Infrastructure for Composition -/

/-- evalAtPoint of a SuperDomainFunction has smooth coefficients. -/
theorem evalAtPoint_grassmannSmooth {p q : ℕ} (sdf : SuperDomainFunction p q) :
    GrassmannSmooth (fun x => sdf.evalAtPoint x) :=
  fun J => (sdf.coefficients J).smooth

/-- grassmannSoul of a GrassmannSmooth family is GrassmannSmooth. -/
theorem grassmannSoul_grassmannSmooth {p q : ℕ}
    {y : (Fin p → ℝ) → FiniteGrassmannCarrier q}
    (hy : GrassmannSmooth y) :
    GrassmannSmooth (fun x => grassmannSoul (y x)) := by
  intro J
  show ContDiff ℝ ⊤ (fun x => grassmannSoul (y x) J)
  simp only [grassmannSoul]
  by_cases hJ : J = ∅
  · simp [hJ]; exact contDiff_const
  · simp [hJ]; exact hy J

/-- smoothTaylorGrassmann preserves GrassmannSmooth: if each y_k(x) has smooth
    coefficients in x, then smoothTaylorGrassmann f (y(x)) has smooth coefficients. -/
theorem smoothTaylorGrassmann_grassmannSmooth {p q : ℕ}
    (f : SmoothFunction p)
    (y : (Fin p → ℝ) → Fin p → FiniteGrassmannCarrier q)
    (hy : ∀ k, GrassmannSmooth (fun x => y x k)) :
    GrassmannSmooth (fun x => smoothTaylorGrassmann f (y x)) := by
  -- Unfold: smoothTaylorGrassmann f (y x) = Σ_{n≤q} taylorTermGrassmann n f (body y x) (soul y x)
  -- Each term is a sum of (scalar at x) • (Grassmann product), all smooth.
  show GrassmannSmooth (fun x =>
    (Finset.range (q + 1)).sum fun n =>
      taylorTermGrassmann n f (fun k => grassmannBody (y x k)) (fun k => grassmannSoul (y x k)))
  -- Body map is smooth as ℝ^p → ℝ^p
  have hbody_smooth : ContDiff ℝ ⊤ (fun x => fun k => grassmannBody (y x k)) :=
    contDiff_pi.mpr (fun k => hy k ∅)
  -- Soul coefficients are smooth
  have hsoul_smooth : ∀ k, GrassmannSmooth (fun x => grassmannSoul (y x k)) :=
    fun k => grassmannSoul_grassmannSmooth (hy k)
  -- Each Taylor term is GrassmannSmooth
  apply GrassmannSmooth.finset_sum
  intro n _
  -- taylorTermGrassmann n f a δ = Σ_dirs (1/n! * ∂ⁿf(a)) • Π_i δ(dirs i)
  show GrassmannSmooth (fun x =>
    Finset.univ.sum fun dirs : Fin n → Fin p =>
      ((↑n.factorial)⁻¹ * (iteratedPartialDeriv (List.ofFn dirs) f).toFun
        (fun k => grassmannBody (y x k))) •
      (List.ofFn fun i => grassmannSoul (y x (dirs i))).prod)
  apply GrassmannSmooth.finset_sum
  intro dirs _
  -- (scalar) • (product) is GrassmannSmooth
  apply GrassmannSmooth.smul_fun
  · -- Scalar: (1/n!) * ∂ⁿf(body(y(x))) is smooth in x
    exact contDiff_const.mul
      ((iteratedPartialDeriv (List.ofFn dirs) f).smooth.comp hbody_smooth)
  · -- Product: Π_i soul(y(x, dirs i)) is GrassmannSmooth
    exact GrassmannSmooth.ofFn_prod (fun i => hsoul_smooth (dirs i))

/-- grassmannMonomial with GrassmannSmooth inputs is GrassmannSmooth. -/
theorem grassmannMonomial_grassmannSmooth {p q : ℕ}
    (eta : (Fin p → ℝ) → Fin q → FiniteGrassmannCarrier q)
    (heta : ∀ a, GrassmannSmooth (fun x => eta x a))
    (I : Finset (Fin q)) :
    GrassmannSmooth (fun x => grassmannMonomial (eta x) I) := by
  show GrassmannSmooth (fun x => ((I.sort (· ≤ ·)).map (eta x)).prod)
  exact GrassmannSmooth.map_prod _ (fun a _ => heta a)

/-! ## Full Composition -/

/-- Full composition of a SuperDomainFunction with a SuperCoordChange,
    producing a new SuperDomainFunction.

    The J-th coefficient of (f ∘ φ) is the function x ↦ (composeEvalAt f φ x) J,
    which extracts the J-th Grassmann component of the composed value.

    Smoothness of each coefficient follows from:
    1. Taylor derivatives of f.coefficients I at body(y(x)) are smooth in x
    2. Grassmann products of φ.evenMap/oddMap coefficients at x are smooth in x
    3. Finite sums and products of smooth functions are smooth -/
def SuperDomainFunction.composeProper {p q : ℕ}
    (f : SuperDomainFunction p q) (φ : SuperCoordChange p q)
    : SuperDomainFunction p q where
  coefficients J := {
    toFun := fun x => composeEvalAt f φ x J
    smooth := by
      -- The key smoothness ingredients:
      have htaylor : ∀ I, GrassmannSmooth (fun x =>
          smoothTaylorGrassmann (f.coefficients I)
            (fun k => (φ.evenMap k).evalAtPoint x)) :=
        fun I => smoothTaylorGrassmann_grassmannSmooth (f.coefficients I)
          (fun x k => (φ.evenMap k).evalAtPoint x)
          (fun k => evalAtPoint_grassmannSmooth (φ.evenMap k))
      have hmonomial : ∀ I, GrassmannSmooth (fun x =>
          grassmannMonomial (fun a => (φ.oddMap a).evalAtPoint x) I) :=
        fun I => grassmannMonomial_grassmannSmooth
          (fun x a => (φ.oddMap a).evalAtPoint x)
          (fun a => evalAtPoint_grassmannSmooth (φ.oddMap a)) I
      -- composeEvalAt is a sum of (Taylor term) * (monomial), each GrassmannSmooth
      show ContDiff ℝ ⊤ (fun x => composeEvalAt f φ x J)
      simp only [composeEvalAt]
      exact (GrassmannSmooth.finset_sum (fun I _ => (htaylor I).mul (hmonomial I))) J
  }

/-! ## Properties of composeEvalAt -/

/-- composeEvalAt distributes: the J-th component is a finite sum over
    multi-indices I of Taylor-expanded coefficients times monomial components. -/
theorem composeEvalAt_apply {p q : ℕ}
    (f : SuperDomainFunction p q) (φ : SuperCoordChange p q)
    (x : Fin p → ℝ) (J : Finset (Fin q)) :
    composeEvalAt f φ x J =
    Finset.univ.sum (fun (I : Finset (Fin q)) =>
      (smoothTaylorGrassmann (f.coefficients I)
        (fun k => (φ.evenMap k).evalAtPoint x) *
       grassmannMonomial (fun a => (φ.oddMap a).evalAtPoint x) I) J) := by
  show (Finset.univ.sum fun I =>
    smoothTaylorGrassmann (f.coefficients I)
      (fun k => (φ.evenMap k).evalAtPoint x) *
    grassmannMonomial (fun a => (φ.oddMap a).evalAtPoint x) I) J =
    Finset.univ.sum (fun I =>
      (smoothTaylorGrassmann (f.coefficients I)
        (fun k => (φ.evenMap k).evalAtPoint x) *
       grassmannMonomial (fun a => (φ.oddMap a).evalAtPoint x) I) J)
  exact Finset.sum_apply _ _ _

/-- When f has only a body component (f = ofSmooth g), the composition simplifies:
    only the I = ∅ term contributes from the outer sum (since f_I = 0 for I ≠ ∅). -/
theorem composeEvalAt_ofSmooth {p q : ℕ}
    (g : SmoothFunction p) (φ : SuperCoordChange p q) (x : Fin p → ℝ) :
    composeEvalAt (SuperDomainFunction.ofSmooth g) φ x =
    smoothTaylorGrassmann g (fun k => (φ.evenMap k).evalAtPoint x) := by
  show Finset.univ.sum (fun I =>
    smoothTaylorGrassmann ((SuperDomainFunction.ofSmooth g).coefficients I)
      (fun k => (φ.evenMap k).evalAtPoint x) *
    grassmannMonomial (fun a => (φ.oddMap a).evalAtPoint x) I) =
    smoothTaylorGrassmann g (fun k => (φ.evenMap k).evalAtPoint x)
  rw [Finset.sum_eq_single ∅]
  · -- I = ∅ term: coefficient is g, monomial is 1
    simp only [SuperDomainFunction.ofSmooth, ↓reduceIte, grassmannMonomial_empty, mul_one]
  · -- I ≠ ∅ terms vanish: coefficient is 0 (from ofSmooth), so Taylor of 0 = 0
    intro I _ hI
    simp only [SuperDomainFunction.ofSmooth, hI, ↓reduceIte]
    have h0 : smoothTaylorGrassmann (0 : SmoothFunction p)
        (fun k => (φ.evenMap k).evalAtPoint x) = grassmannScalar 0 := by
      convert smoothTaylorGrassmann_const 0 (fun k => (φ.evenMap k).evalAtPoint x)
    rw [h0, show grassmannScalar (q := q) 0 = 0 from by funext I; simp [grassmannScalar]]
    exact zero_mul _
  · intro h; exact absurd (Finset.mem_univ ∅) h

/-! ## Body-level Properties -/

/-- The body map of a coordinate change applied to x gives the body of y(x). -/
theorem SuperCoordChange.bodyMap_eq_body {p q : ℕ} (φ : SuperCoordChange p q) (x : Fin p → ℝ) :
    φ.bodyMap x = fun k => grassmannBody ((φ.evenMap k).evalAtPoint x) := by
  funext k
  simp only [SuperCoordChange.bodyMap, SuperDomainFunction.body, grassmannBody,
    SuperDomainFunction.evalAtPoint]

/-- The body of composeEvalAt of a lifted body function equals the body function
    evaluated at the body map.

    grassmannBody (composeEvalAt (liftToSuper g) φ x) = g.toFun (φ.bodyMap x)

    This combines:
    - composeEvalAt_ofSmooth: reduces to smoothTaylorGrassmann
    - smoothTaylorGrassmann_body: body of Taylor expansion = f at body points
    - bodyMap_eq_body: body of evenMap = bodyMap -/
theorem grassmannBody_composeEvalAt_liftToSuper {p q : ℕ}
    (g : SmoothFunction p) (φ : SuperCoordChange p q) (x : Fin p → ℝ) :
    grassmannBody (composeEvalAt (liftToSuper g) φ x) = g.toFun (φ.bodyMap x) := by
  rw [show liftToSuper g = SuperDomainFunction.ofSmooth g from rfl,
      composeEvalAt_ofSmooth, smoothTaylorGrassmann_body,
      SuperCoordChange.bodyMap_eq_body]

/-! ## Linearity Properties -/

/-- composeEvalAt is additive in f:
    (f + g) ∘ φ at x = (f ∘ φ at x) + (g ∘ φ at x).

    This follows from the linearity of the Taylor expansion and
    the distributive law in the Grassmann algebra. -/
theorem composeEvalAt_add {p q : ℕ}
    (f g : SuperDomainFunction p q) (φ : SuperCoordChange p q) (x : Fin p → ℝ)
    (hfg : ∀ I, (f + g).coefficients I = ⟨fun x => f.coefficients I x + g.coefficients I x,
      (f.coefficients I).smooth.add (g.coefficients I).smooth⟩) :
    composeEvalAt (f + g) φ x =
    composeEvalAt f φ x + composeEvalAt g φ x := by
  simp only [composeEvalAt]
  rw [← Finset.sum_add_distrib]
  congr 1
  ext I
  rw [hfg I]
  rw [smoothTaylorGrassmann_add, add_mul]

/-- composeEvalAt respects scalar multiplication:
    (c • f) ∘ φ at x = c • (f ∘ φ at x).

    This uses the fact that Taylor expansion commutes with ℝ-scalar multiplication
    (the key property that avoids division in the Grassmann algebra). -/
theorem composeEvalAt_smul {p q : ℕ}
    (c : ℝ) (f : SuperDomainFunction p q) (φ : SuperCoordChange p q) (x : Fin p → ℝ)
    (hcf : ∀ I, (c • f).coefficients I = ⟨fun x => c * f.coefficients I x,
      contDiff_const.mul (f.coefficients I).smooth⟩) :
    composeEvalAt (c • f) φ x =
    c • composeEvalAt f φ x := by
  simp only [composeEvalAt]
  rw [Finset.smul_sum]
  congr 1
  ext I
  rw [hcf I]
  rw [smoothTaylorGrassmann_smul, smul_mul_assoc]

/-! ## Connection to the Existing Placeholder

The old `SuperDomainFunction.composeLegacyApprox` in FiniteGrassmann.lean is a placeholder that
only handles the body coefficient correctly (and returns 0 for all non-body coefficients).

`composeProper` replaces this with the full computation using nilpotent Taylor expansion.
The two agree on the body coefficient when restricted to body-only composition:
`composeProper.coefficients ∅ x ≈ composeLegacyApprox.coefficients ∅ x`
(to first order in soul parts).

For the global integration pipeline:
- Phase 3 (`IntegralForm.pullbackProper`) uses `composeEvalAt` to compute ω ∘ φ at each point
- Phase 6 (change of variables) needs `composeProper` for the full coefficient computation
-/

end Supermanifolds
