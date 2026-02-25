# Phase 4: Super Exterior Derivative — Proof Ideas

## Goal

Define a proper exterior derivative on integral forms of various codimensions.

## Mathematical Background

### Differential forms on supermanifolds (NOT what we integrate)

A differential form on ℝ^{p|q} is a function ω(x, θ | dx, dθ) where:
- x^i, dx^i are even (bosonic) variables
- θ^a, dθ^a are odd (fermionic) variables
- ω is polynomial in dx^i and dθ^a

Note: dx^i is odd (form degree 1), dθ^a is even (form degree 1, parity flipped).

### Integral forms (what we actually integrate)

An integral form on ℝ^{p|q} uses:
- dx^i as usual (wedge product, anticommuting)
- δ(dθ^a) instead of dθ^a (Dirac delta functions in the odd differentials)

The top integral form is [Dx Dθ] = dx^1 ∧ ... ∧ dx^p · δ(dθ^1) · ... · δ(dθ^q).

### Key insight from Witten §3.3

The integral form space can be described as functions of (x, θ, dx) times δ-functions in dθ:

  ω = f(x, θ, dx) · δ(dθ^1) · ... · δ(dθ^q)

where f(x, θ, dx) is polynomial in dx (an ordinary-looking differential form in the even variables with superfunction coefficients).

## The Exterior Derivative

### On ℝ^{p|q}

d = d₀ + d₁ where:

**d₀ = Σ_i dx^i ∂/∂x^i** (even part)
- Acts on the x-dependence of coefficients
- Standard exterior derivative behavior
- Anticommutes with dx^j (as usual)

**d₁ = Σ_a dθ^a ∂/∂θ^a** (odd part)
- For differential forms: dθ^a is even, so this adds a factor of dθ^a
- For integral forms: the action is different — dθ^a acts as ∂/∂(dθ^a) on the δ-functions

### d₁ on integral forms

On δ(dθ^a): dθ^a · δ(dθ^a) is NOT well-defined as multiplication, but:

The action of d₁ on an integral form of codimension 0 gives an integral form of codimension 1. In the top-degree case f(x,θ)[Dx Dθ]:

d₁(f [Dx Dθ]) = Σ_a (∂f/∂θ^a) · (something of codimension 1)

The "something" is the integral form [Dx Dθ] with one δ(dθ^a) removed, replaced by dθ^a. But since dθ^a · δ(dθ^a) is a distributional product, we instead work with the Berezin integral directly.

### Practical approach for Lean

For our purposes (proving Stokes), we need:

1. d acting on integral forms of codimension 1, producing codimension 0 forms
2. d acting on integral forms of codimension 0, producing codimension 1 forms (for the divergence theorem direction)

The key property: after Berezin integration, d₁ contributes nothing (already proven), and d₀ gives the classical exterior derivative.

## Implementation

### Codimension-1 Integral Forms

A codimension-1 integral form on ℝ^{p|q} can be written as:
  ν = Σ_i f_i(x,θ) dx^1 ∧ ... ∧ dx̂^i ∧ ... ∧ dx^p · δ(dθ^1)...δ(dθ^q)

where dx̂^i means dx^i is omitted. This has (p-1) even form factors.

```lean
/-- Codimension-1 integral form: has one missing dx^i direction -/
structure IntegralFormCodim1 (p q : ℕ) where
  /-- For each missing direction i, the coefficient super function -/
  components : Fin p → SuperDomainFunction p q
```

### d₀ on Codimension-1 Forms

d₀(ν) = Σ_i Σ_j dx^j ∂f_i/∂x^j ∧ (dx^1 ∧ ... ∧ dx̂^i ∧ ... ∧ dx^p) · δ(dθ)

Only the j = i term survives (all others have repeated dx factors):

d₀(ν) = Σ_i (-1)^{i-1} (∂f_i/∂x^i) dx^1 ∧ ... ∧ dx^p · δ(dθ)
       = (Σ_i (-1)^{i-1} ∂f_i/∂x^i) [Dx Dθ]

This is the divergence! After Berezin integration:
  (d₀ν)_top = Σ_i (-1)^{i-1} ∂(f_i)_top/∂x^i

```lean
/-- d₀ on codimension-1 integral forms gives a codimension-0 form -/
noncomputable def d0_codim1 {p q : ℕ} (ν : IntegralFormCodim1 p q) : IntegralForm p q :=
  ⟨⟨fun I => Finset.univ.sum fun i =>
    (-1)^(i : ℕ) • (partialEven i (ν.components i)).coefficients I⟩⟩
```

### d₁ on Codimension-1 Forms

d₁(ν) involves ∂/∂θ^a acting on the coefficients f_i(x,θ). After Berezin integration, each term involves ∂f_i/∂θ^a which has θ-degree reduced by 1, hence no top component. So:

  ∫ dθ (d₁ν) = 0

This is the essential content for Stokes.

### d on Codimension-0 Forms (for reference)

d(f [Dx Dθ]) maps from codim-0 to codim-1. Since [Dx Dθ] is already top degree in both dx and δ(dθ), we get:

d₀(f [Dx Dθ]) = 0 (already max even-form degree)
d₁(f [Dx Dθ]) = Σ_a (∂f/∂θ^a) · (complicated codim-1 form)

This direction is less critical for basic Stokes.

## Key Properties — Status

### Proven
- **d₀ is additive**: `d0Codim1_add` in ExteriorDerivative.lean
- **d₀ = divergence**: `d0_is_divergence` in ExteriorDerivative.lean
- **partialEven_mul**: Product rule ∂(fg)/∂xⁱ = (∂f/∂xⁱ)g + f(∂g/∂xⁱ)
- **partialEven_add**, **partialEven_smul**: Linearity of ∂/∂xⁱ
- **partialOdd linearity**: `partialOdd_add`
- **∂²/∂θᵃ² = 0**: `partialOdd_partialOdd`
- **Local Stokes**: Super Stokes → classical divergence theorem (StokesTheorem.lean)

### In Progress
- **Leibniz rule for d₀ on products**: `d0Codim1_mulByFunction`
  d₀(ρ · ν) = ρ · d₀ν + Σᵢ (-1)ⁱ (∂ρ/∂xⁱ) · νᵢ
  Uses `partialEven_mul` + Ring/Algebra distributivity on SuperDomainFunction

### Not Yet Needed
- **d² = 0**: d₀² = 0 follows from symmetry of mixed partials. Not needed for Stokes.
- **d₁ on integral forms**: d₁ maps to different graded piece. Already explained in docstring.

## References

- Witten §3.2: "Integral forms and their calculus"
- Witten §3.3: "More on integral forms" (distributional aspects)
- Rogers §10: "Exterior forms on supermanifolds"
