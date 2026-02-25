import StringGeometry.Supermanifolds.Integration.Core

/-!
# Codimension-1 Integral Forms on Super Domains

This file defines integral forms of codimension 1 on super domains ℝ^{p|q}.
These are needed for the super Stokes theorem.

## Mathematical Background

A codimension-0 integral form (defined in `BerezinIntegration.lean`) is an expression
  ω = f(x,θ) [Dx Dθ]
where [Dx Dθ] = dx¹ ∧ ... ∧ dxᵖ · δ(dθ¹)...δ(dθ^q) is the full Berezinian volume element.

A **codimension-1 integral form** has one fewer dx factor:
  ν = Σᵢ fᵢ(x,θ) dx¹ ∧ ... ∧ d̂xⁱ ∧ ... ∧ dxᵖ · δ(dθ¹)...δ(dθ^q)

where d̂xⁱ means dxⁱ is omitted. This is the object that appears in super Stokes' theorem:
  ∫_M dν = ∫_{∂M} ν

## Main Definitions

* `IntegralFormCodim1 p q` - A codimension-1 integral form on ℝ^{p|q}
* Operations: zero, add, smul, neg, mulByFunction

## References

* Witten, "Notes on Supermanifolds and Integration" (arXiv:1209.2199), §3.2-3.5
* Bernstein-Leites, "Integral Forms and the Stokes Formula on Supermanifolds" (1977)
-/

namespace Supermanifolds

open Supermanifolds.Helpers

/-!
## Codimension-1 Integral Forms

A codimension-1 integral form on ℝ^{p|q} is a collection of p super domain functions
(fᵢ)_{i=0,...,p-1}, representing:

  ν = Σᵢ fᵢ(x,θ) · dx¹ ∧ ... ∧ d̂xⁱ ∧ ... ∧ dxᵖ · δ(dθ¹)...δ(dθ^q)

where d̂xⁱ means the i-th factor is omitted from the wedge product.

The component fᵢ is the coefficient of the (p-1)-form that misses the dxⁱ direction.
Under integration, only the top θ-component of each fᵢ contributes (via Berezin integration).
-/

/-- A codimension-1 integral form on the super domain ℝ^{p|q}.

    This represents ν = Σᵢ fᵢ(x,θ) · dx¹ ∧ ... ∧ d̂xⁱ ∧ ... ∧ dxᵖ · δ(dθ)
    where d̂xⁱ means dxⁱ is omitted.

    Each component `fᵢ` is a super domain function that serves as the coefficient
    of the (p-1)-form missing the i-th even direction. -/
structure IntegralFormCodim1 (p q : ℕ) where
  /-- The i-th component: coefficient of dx¹ ∧ ... ∧ d̂xⁱ ∧ ... ∧ dxᵖ · δ(dθ) -/
  components : Fin p → SuperDomainFunction p q

namespace IntegralFormCodim1

variable {p q : ℕ}

/-- Zero codimension-1 form -/
def zero : IntegralFormCodim1 p q :=
  ⟨fun _ => SuperDomainFunction.zero⟩

/-- Addition of codimension-1 forms -/
def add (ν₁ ν₂ : IntegralFormCodim1 p q) : IntegralFormCodim1 p q :=
  ⟨fun i => SuperDomainFunction.add (ν₁.components i) (ν₂.components i)⟩

/-- Scalar multiplication of a codimension-1 form -/
def smul (c : ℝ) (ν : IntegralFormCodim1 p q) : IntegralFormCodim1 p q :=
  ⟨fun i => SuperDomainFunction.smul c (ν.components i)⟩

/-- Negation of a codimension-1 form -/
def neg (ν : IntegralFormCodim1 p q) : IntegralFormCodim1 p q :=
  ⟨fun i => SuperDomainFunction.neg (ν.components i)⟩

instance : Zero (IntegralFormCodim1 p q) := ⟨zero⟩
instance : Add (IntegralFormCodim1 p q) := ⟨add⟩
instance : Neg (IntegralFormCodim1 p q) := ⟨neg⟩
instance : SMul ℝ (IntegralFormCodim1 p q) := ⟨smul⟩

/-- Extensionality for codimension-1 forms -/
@[ext]
theorem ext {ν₁ ν₂ : IntegralFormCodim1 p q}
    (h : ∀ i, ν₁.components i = ν₂.components i) : ν₁ = ν₂ := by
  cases ν₁; cases ν₂; simp only [mk.injEq]; funext i; exact h i

/-- Multiplication by a super function (left action).

    Given g(x,θ) and ν = Σᵢ fᵢ dx̂ⁱ · δ(dθ), the product is:
    g · ν = Σᵢ (g · fᵢ) dx̂ⁱ · δ(dθ)

    This uses the Grassmann algebra multiplication from `SuperDomainFunction.mul`. -/
def mulByFunction (g : SuperDomainFunction p q) (ν : IntegralFormCodim1 p q) :
    IntegralFormCodim1 p q :=
  ⟨fun i => SuperDomainFunction.mul g (ν.components i)⟩

/-!
## Berezin Integration of Codimension-1 Forms

The Berezin integral over odd variables acts componentwise on a codimension-1 form:
  ∫dθ ν = Σᵢ (∫dθ fᵢ) dx̂ⁱ

This produces a classical (p-1)-form on the body ℝᵖ with smooth coefficients.
-/

/-- Berezin integration of each component: extracts the top θ-coefficient of each fᵢ.
    The result is a collection of smooth functions on the body ℝᵖ, one per missing direction. -/
def berezinComponents (ν : IntegralFormCodim1 p q) : Fin p → SmoothFunction p :=
  fun i => berezinIntegralOdd (ν.components i)

/-- The codimension-1 form is compactly supported if all component functions
    have compactly supported top θ-coefficients on the body. -/
def IsCompactlySupported (ν : IntegralFormCodim1 p q) : Prop :=
  ∀ i : Fin p, _root_.HasCompactSupport (ν.berezinComponents i).toFun

/-!
## Single-Component Forms

A codimension-1 form with only one nonzero component is useful for constructing
test cases (e.g., the (1|1) example).
-/

/-- A codimension-1 form with a single nonzero component in direction i. -/
def single (i : Fin p) (f : SuperDomainFunction p q) : IntegralFormCodim1 p q :=
  ⟨fun j => if j = i then f else SuperDomainFunction.zero⟩

/-- In the (1|1) case, a codimension-1 form is determined by a single super function
    (since p = 1, there's only one direction to omit). -/
def ofFunction_1_q (f : SuperDomainFunction 1 q) : IntegralFormCodim1 1 q :=
  ⟨fun _ => f⟩

end IntegralFormCodim1

end Supermanifolds
