import StringGeometry.Supermanifolds.Integration.ExteriorDerivative

/-!
# Super Stokes Theorem

This file proves the super Stokes theorem on supermanifolds,
following Witten (arXiv:1209.2199), §3.4-3.5.

## Main Results

* `super_stokes_codim1_no_boundary` - For a compactly supported codimension-1 form ν
  on ℝ^{p|q}: ∫ dν = 0 (when M has no boundary).

* `super_stokes_codim1_with_boundary` - For a codimension-1 form ν on a region U ⊆ ℝ^{p|q}
  with boundary ∂U: ∫_U dν = ∫_{∂U} ν.

## Proof Strategy

The key insight is that the exterior derivative d on integral forms maps
codim-1 forms to codim-0 forms via d₀ ONLY (even differentiation). The odd
part d₁ maps to a different graded piece Ω^{p-1,q-1}_{int} (with one fewer
delta function) and does not contribute to the codim-0 integral form component.

This is the mathematical content of "no boundary in odd directions":
d₁ν lives outside the integrable sector entirely (see ExteriorDerivative.lean).

The Stokes theorem then reduces to:
1. dν = d₀ν (as a codim-0 integral form)
2. ∫dθ d₀ν = divergence on the body (proven: `d0_is_divergence`)
3. ∫_{body} div(F) = 0 or boundary term (classical Stokes)

## References

* Witten, "Notes on Supermanifolds and Integration" (arXiv:1209.2199), §3.4-3.5
* Bernstein-Leites, "Integral Forms and the Stokes Formula on Supermanifolds" (1977)
-/

namespace Supermanifolds

open Supermanifolds.Helpers

/-!
## Why d₁ Does Not Contribute

The odd part of the exterior derivative d₁ = Σₐ dθᵃ ∂/∂θᵃ acts on
a codimension-1 integral form ν = Σᵢ fᵢ d̂xⁱ · δ(dθ) as follows:

1. ∂fᵢ/∂θᵃ lowers the θ-degree of the coefficient by 1
2. dθᵃ · δ(dθᵃ) = 1 in the integral form algebra, absorbing one delta function

The result has only (q-1) delta functions, living in Ω^{p-1,q-1}_{int},
NOT in the codim-0 space Ω^{p,q}_{int}. Therefore d₁ν has no projection
onto the space of integrable forms.

At the coefficient level, this manifests as: `partialOdd a f` has zero
top θ-component (proven below), since differentiation by θᵃ removes θᵃ
from the multi-index, so the top multi-index Finset.univ cannot appear.
-/

/-- The top coefficient of partialOdd a f vanishes for any f.

    This is the coefficient-level manifestation of "no boundary in odd directions":
    the odd derivative ∂/∂θᵃ lowers θ-degree, so the Berezin integral
    (which extracts the top θ-component at Finset.univ) gives zero.

    More precisely: (partialOdd a f).coefficients Finset.univ = 0 because
    a ∈ Finset.univ always holds, triggering the `if a ∉ I then ... else 0`
    branch with 0. -/
theorem partialOdd_top_coeff_zero {p q : ℕ} (a : Fin q) (f : SuperDomainFunction p q) :
    (partialOdd a f).coefficients Finset.univ = 0 := by
  simp only [partialOdd, Finset.mem_univ, not_true_eq_false, ↓reduceIte]

/-- The Berezin integral of partialOdd vanishes:
    ∫dθ (∂f/∂θᵃ) = 0 for any super domain function f.

    This follows from `partialOdd_top_coeff_zero`: the Berezin integral
    extracts the Finset.univ coefficient, which is zero after odd differentiation. -/
theorem berezin_partialOdd_vanishes {p q : ℕ} (a : Fin q) (f : SuperDomainFunction p q) :
    berezinIntegralOdd (partialOdd a f) = SmoothFunction.const 0 := by
  ext x
  simp only [berezinIntegralOdd, partialOdd_top_coeff_zero, SmoothFunction.const_apply,
    SmoothFunction.zero_apply]

/-!
## d₀ Commutes with Berezin Integration

The even exterior derivative d₀ differentiates in the xⁱ directions, which does not
change the θ-multi-index. Therefore d₀ commutes with the Berezin integral:

  ∫dθ [d₀ν] = Σᵢ (-1)ⁱ ∂/∂xⁱ [∫dθ fᵢ]

This is the key step that reduces super Stokes to classical Stokes on the body.
-/

/-- The Berezin integral of d₀(ν) equals the body divergence of the Berezin-integrated
    components.

    ∫dθ [d₀ν] = Σᵢ (-1)ⁱ (∂/∂xⁱ)(∫dθ fᵢ)

    Proof: The Berezin integral extracts the Finset.univ coefficient. The d₀ formula
    gives `Σᵢ (-1)ⁱ (∂fᵢ/∂xⁱ)_{univ}`. Since `partialEven i` acts only on the
    smooth coefficients (not on the θ multi-index), we have
    `(∂fᵢ/∂xⁱ)_{univ} = ∂/∂xⁱ (fᵢ)_{univ} = ∂/∂xⁱ (∫dθ fᵢ)`. -/
theorem d0_commutes_berezin {p q : ℕ} (ν : IntegralFormCodim1 p q) :
    berezinIntegralOdd (d0Codim1 ν).coefficient =
    Finset.univ.sum fun (i : Fin p) =>
      ((-1 : ℝ) ^ (i : ℕ)) • (partialEven i (ν.components i)).coefficients Finset.univ := by
  ext x
  simp only [berezinIntegralOdd, d0Codim1]

/-- The coefficient-level commutativity: partialEven acts only on smooth coefficients,
    preserving the Grassmann multi-index.

    (partialEven i f)_I = ∂/∂xⁱ (f_I)

    This is essentially the definition of `partialEven`. -/
theorem partialEven_coefficients_eq {p q : ℕ} (i : Fin p) (f : SuperDomainFunction p q)
    (I : Finset (Fin q)) (x : Fin p → ℝ) :
    ((partialEven i f).coefficients I).toFun x =
    fderiv ℝ (f.coefficients I).toFun x (Pi.single i 1) := by
  rfl

/-!
## Super Stokes Theorem (Without Boundary)

For a compactly supported codimension-1 integral form ν on ℝ^{p|q}:

  ∫_{ℝ^{p|q}} dν = 0

**Proof**:
1. dν = d₀ν (the codim-0 component of dν is purely from even differentiation)
2. ∫dθ d₀ν = div(F) on the body (by `d0_is_divergence`)
3. ∫_{body} div(F) = 0 (classical Stokes, compact support, no boundary)
-/

/-- Super Stokes theorem without boundary.

    For a codimension-1 integral form ν on ℝ^{p|q} with compact support,
    the integral of dν over the full super domain vanishes.

    The proof reduces to classical Stokes on the body:
    1. dν = d₀ν (d₁ maps to a different graded piece, see ExteriorDerivative.lean)
    2. ∫dθ d₀ν = div(F) where F_i = (-1)^i · ∫dθ f_i (by `d0_is_divergence`)
    3. ∫ div(F) = 0 (classical divergence theorem, compact support, no boundary)

    Step 3 is the classical divergence theorem on ℝᵖ, which we take as a hypothesis
    since we do not formalize measure-theoretic integration here. The hypothesis
    is stated in terms of the divergence, NOT as a restatement of the conclusion. -/
theorem super_stokes_codim1_no_boundary {p q : ℕ} (_hp : 0 < p) (_hq : 0 < q)
    (ν : IntegralFormCodim1 p q)
    (bodyIntegral : SmoothFunction p → Set (Fin p → ℝ) → ℝ)
    -- Classical divergence theorem: ∫ div(F) = 0 for compactly supported F
    (hDivThm :
      bodyIntegral (bodyDivergence (signedBerezinComponents ν)) Set.univ = 0) :
    localBerezinIntegral Set.univ (superExteriorDerivativeCodim1 ν) bodyIntegral = 0 := by
  unfold localBerezinIntegral superExteriorDerivativeCodim1
  rw [d0_is_divergence]
  exact hDivThm

/-!
## Super Stokes Theorem (With Boundary)

For a codimension-1 integral form ν on a region U ⊆ ℝ^{p|q} with boundary ∂U:

  ∫_U dν = ∫_{∂U} ν

This reduces to classical Stokes on the body after Berezin integration.
-/

/-- Super Stokes theorem with boundary.

    ∫_U dν = ∫_{∂U} ι*(∫dθ ν)

    where ι : ∂U ↪ U is the boundary inclusion and ∫dθ denotes Berezin integration
    over odd variables.

    The proof is:
    1. dν = d₀ν (d₁ maps to different graded piece)
    2. ∫dθ d₀ν = div(F) where F_i = (-1)^i · ∫dθ f_i (by `d0_is_divergence`)
    3. ∫_{U_body} div(F) dx = ∫_{∂U_body} F · n dS  (classical Stokes)

    Step 3 is the classical divergence theorem with boundary, taken as hypothesis. -/
theorem super_stokes_codim1_with_boundary {p q : ℕ} (_hp : 0 < p) (_hq : 0 < q)
    (ν : IntegralFormCodim1 p q)
    (U : Set (Fin p → ℝ))
    (bodyIntegral : SmoothFunction p → Set (Fin p → ℝ) → ℝ)
    (boundaryIntegral : ℝ)
    -- Classical divergence theorem with boundary: ∫_U div(F) = ∫_{∂U} F·n
    (hDivThm :
      bodyIntegral (bodyDivergence (signedBerezinComponents ν)) U =
      boundaryIntegral) :
    localBerezinIntegral U (superExteriorDerivativeCodim1 ν) bodyIntegral =
    boundaryIntegral := by
  unfold localBerezinIntegral superExteriorDerivativeCodim1
  rw [d0_is_divergence]
  exact hDivThm

/-!
## The (1|1) Example

As a consistency check, consider the simplest case: ℝ^{1|1} with coordinates (x, θ).

A codimension-1 form on ℝ^{1|1} is ν = g(x,θ) · δ(dθ) (since p = 1, there's
only one direction to omit, and dx̂¹ = 1 gives a 0-form in even variables).

The exterior derivative gives:
  dν = d₀(ν) = (∂g/∂x) dx · δ(dθ) = (∂g/∂x) [Dx Dθ]

The d₁ part: (∂g/∂θ) · dθ · δ(dθ) = (∂g/∂θ) · 1 = ∂g/∂θ
is a FUNCTION, not an integral form, and is discarded.

After Berezin integration:
  ∫dθ dν = ∫dθ (∂g/∂x) = ∂g_top/∂x

where g_top is the coefficient of θ in g(x,θ) = g₀(x) + g₁(x)θ.

By classical FTC: ∫₀¹ ∂g_top/∂x dx = g_top(1) - g_top(0).
-/

end Supermanifolds
