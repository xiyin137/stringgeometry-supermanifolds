# Phase 1: Super Function Composition — Proof Ideas

## Goal

Implement `SuperDomainFunction.compose` with full coefficient tracking.

## Mathematical Setup

A `SuperDomainFunction p q` is f(x, θ) = Σ_{I ⊆ {1,...,q}} f_I(x) θ^I where f_I : ℝ^p → ℝ smooth.

A coordinate change φ : ℝ^{p|q} → ℝ^{p|q} is given by:
- Even: y_i(x,θ) = φ^i(x,θ) = a_i(x) + Σ_{|J|≥2, even} b^i_J(x) θ^J
- Odd:  η_a(x,θ) = ψ^a(x,θ) = Σ_{|K| odd} c^a_K(x) θ^K

We want (f ∘ φ)(x,θ) = Σ_I f_I(y(x,θ)) · η(x,θ)^I.

## Key Insight: Nilpotent Taylor Expansion

Write y_i(x,θ) = a_i(x) + δy_i(x,θ) where δy_i is the "soul part" (nilpotent).

Since δy_i is a sum of terms with θ's, and θ^{q+1} = 0 in Λ_q, we have δy^{q+1} = 0.

So the Taylor expansion of f_I around a(x) terminates:

  f_I(y(x,θ)) = Σ_{n=0}^{q} (1/n!) Σ_{k₁...k_n} (∂ⁿf_I/∂y_{k₁}...∂y_{k_n})(a(x)) · δy_{k₁} · ... · δy_{k_n}

This is a **finite** sum because δy is nilpotent.

## Implementation Strategy

### Step 1: Soul Decomposition
Already available: `grassmann_body_soul_decomp` gives x = body(x) + soul(x).

### Step 2: Nilpotent Taylor Expansion
```lean
/-- Taylor expansion of a smooth function applied to body + nilpotent -/
noncomputable def smoothTaylorGrassmann {p q : ℕ} (f : SmoothFunction p)
    (body : Fin p → ℝ) (soul : Fin p → FiniteGrassmannCarrier q)
    (h_nilp : ∀ i, (soul i) ^ (q + 1) = 0) : FiniteGrassmannCarrier q :=
  -- f(body + soul) = Σ_{n=0}^{q} (1/n!) Σ_{k₁...k_n} f^(n)_{k₁...k_n}(body) · soul_{k₁} · ... · soul_{k_n}
```

The key lemma: this terminates because multi-index derivatives of smooth functions exist (ContDiff ℝ ⊤) and the nilpotent products vanish beyond degree q.

### Step 3: Odd Coordinate Substitution
For η^I = η_{a₁} · ... · η_{a_k}, each η_a is a sum of odd-degree θ-monomials. The product η^I is computed using Grassmann multiplication (already available via the Ring instance on FiniteGrassmannCarrier).

### Step 4: Assemble the Composition
```
(f ∘ φ)(x,θ) = Σ_I f_I(y(x,θ)) · η(x,θ)^I
```

Each term is a product of Grassmann algebra elements evaluated at x.

### Step 5: Extract Coefficients
Read off the coefficient of each θ^J in the resulting Grassmann expression to get the SuperDomainFunction coefficients.

## Proof of Smoothness

The smoothness of (f ∘ φ) in x follows from:
1. Each f_I is smooth (given)
2. Each a_i(x), b^i_J(x), c^a_K(x) are smooth (given)
3. Partial derivatives of f_I are smooth (from ContDiff ℝ ⊤)
4. Finite sums and products of smooth functions are smooth
5. Each coefficient of (f ∘ φ) is a finite sum of products of smooth functions

## Connection to Existing Infrastructure

- `FiniteGrassmannCarrier q` has Ring instance → handles Grassmann multiplication
- `grassmann_soul_nilpotent` → guarantees Taylor termination
- `SmoothFunction.extendToGrassmann` → first-order approximation (exists, needs extension to all orders)
- `partialEven` → provides ∂f/∂x_i as SmoothFunction (for Taylor coefficients)

## Estimated Difficulty

MEDIUM-HIGH. The mathematical content is clear but coefficient tracking is combinatorially complex. The key challenge is expressing multi-variable Taylor expansion over the Grassmann algebra in Lean's type system.

## IMPORTANT: Commutative Ring, Not Field

The even part of FiniteGrassmannCarrier q is a commutative ring with ZERO DIVISORS.
This means:
- Taylor 1/n! factor MUST be ℝ-scalar multiplication: `((n.factorial : ℝ)⁻¹) • (...)`
- NEVER use division within the Grassmann algebra
- Products δ_{k₁} · ... · δ_{k_n} are computed in the Grassmann ring
- When all δ_k are even (from even coordinates), they commute → order doesn't matter
- The FPS infrastructure (expNilpotent, logOneSubNilpotent) uses `Algebra ℚ R` correctly

## Simplification for Phase 2

For the pullback formula, we actually only need the **value** of (f ∘ φ) at each point x (as a Grassmann algebra element), not the full SuperDomainFunction decomposition. This means we can implement:

```lean
/-- Evaluate f ∘ φ at a point x, returning a Grassmann algebra element -/
noncomputable def composeEvalAt {p q : ℕ}
    (f : SuperDomainFunction p q) (φ : SuperCoordChange p q)
    (x : Fin p → ℝ) : FiniteGrassmannCarrier q := ...
```

This is significantly simpler than the full composition and suffices for the pullback.
