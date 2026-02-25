# Stokes Theorem on Supermanifolds — Proof Ideas

## Status: ✅ CORE THEOREMS PROVEN

The core Stokes theorem (Track A) is fully proven in `Integration/StokesTheorem.lean`.

## What's Proven

### Key Lemma: d₁ Integration Vanishes
```lean
theorem berezin_d1_vanishes {p q : ℕ} (_hq : 0 < q) (ν : IntegralFormCodim1 p q) :
    berezinIntegralOdd (d1Codim1 ν).coefficient = SmoothFunction.const 0
```
**Proof**: The Berezin integral evaluates at `I = Finset.univ`. For each summand
`(partialOdd a f)`, the coefficient at `Finset.univ` is 0 because `a ∈ Finset.univ`
always holds, so the `if a ∉ I then ... else 0` branch gives 0. The sum of zeros is zero.

### d₀ Commutes with Berezin Integration
```lean
theorem d0_commutes_berezin {p q : ℕ} (ν : IntegralFormCodim1 p q) :
    berezinIntegralOdd (d0Codim1 ν).coefficient =
    Finset.univ.sum fun (i : Fin p) =>
      ((-1 : ℝ) ^ (i : ℕ)) • (partialEven i (ν.components i)).coefficients Finset.univ
```
**Proof**: By definition — `d0Codim1` and `berezinIntegralOdd` act on different indices.

### Super Stokes Without Boundary
```lean
theorem super_stokes_codim1_no_boundary {p q : ℕ} (_hp : 0 < p) (hq : 0 < q)
    (ν : IntegralFormCodim1 p q)
    (bodyIntegral : SmoothFunction p → Set (Fin p → ℝ) → ℝ)
    (hClassicalStokes : bodyIntegral (berezinIntegralOdd (d0Codim1 ν).coefficient) Set.univ = 0) :
    localBerezinIntegral Set.univ (superExteriorDerivativeCodim1 ν) bodyIntegral = 0
```
**Proof**: Split d = d₀ + d₁. d₁ vanishes by `berezin_d1_vanishes`. d₀ part equals body integral of divergence, which vanishes by classical Stokes hypothesis.

### Super Stokes With Boundary
```lean
theorem super_stokes_codim1_with_boundary {p q : ℕ} (_hp : 0 < p) (hq : 0 < q)
    (ν : IntegralFormCodim1 p q)
    (U : Set (Fin p → ℝ))
    (bodyIntegral : SmoothFunction p → Set (Fin p → ℝ) → ℝ)
    (boundaryIntegral : ℝ)
    (hClassicalStokes : bodyIntegral (berezinIntegralOdd (d0Codim1 ν).coefficient) U = boundaryIntegral) :
    localBerezinIntegral U (superExteriorDerivativeCodim1 ν) bodyIntegral = boundaryIntegral
```

## The (1|1) Worked Example

Consider ℝ^{1|1} with coordinates (x, θ).

**Setup**: A codimension-1 form on ℝ^{1|1} is:
  ν = g(x,θ) · δ(dθ)
Since p = 1, there's only one even direction, so omitting dx¹ leaves a 0-form.

In our formalization: `ν : IntegralFormCodim1 1 1` with `ν.components 0 = g`.

**Super function**: g(x,θ) = g₀(x) + g₁(x)θ where:
- `g.coefficients ∅ = g₀` (body part)
- `g.coefficients {0} = g₁` (soul part, coefficient of θ)

**Exterior derivative**:
- d₀(ν) = (∂g/∂x) dx · δ(dθ) = (∂g/∂x) [Dx Dθ]
  - In our formalization: `(d0Codim1 ν).coefficient.coefficients I = (-1)⁰ • (partialEven 0 g).coefficients I = (partialEven 0 g).coefficients I`
- d₁(ν): involves ∂g/∂θ acting on δ-functions. Berezin integral gives 0.

**Berezin integration**: ∫dθ [d₀ν] = (∂g/∂x)_{top} = ∂g₁/∂x

**Classical Stokes on [0,1]**: ∫₀¹ (∂g₁/∂x) dx = g₁(1) - g₁(0)

**Conclusion**: ∫_{[0,1]^{1|1}} dν = g₁(1) - g₁(0) = ∫_{∂[0,1]^{1|1}} ν

This matches the with-boundary theorem when `boundaryIntegral = g₁(1) - g₁(0)`.

## Remaining Work

### Extension to Global Supermanifolds
The current theorems work locally on ℝ^{p|q}. To extend globally:
1. Use partition of unity to decompose ν = Σ_α ν_α (each supported in one chart)
2. Apply local Stokes to each piece
3. Sum using linearity

Requires: `partition_of_unity_exists` (currently sorry).

### Boundary Theory (Phase 6 of Plan)
For a proper boundary theory:
1. Define `SupermanifoldWithBoundary` (Witten §3.5)
2. Define boundary restriction functor ι* for integral forms
3. Show ∂M is a supermanifold of dimension (p-1|q)

### Orientation
- M_red must be oriented for integration
- Odd directions don't affect orientation
- The boundary orientation is induced from M_red

## Subtleties

### Why d₁ vanishes after integration
There is NO boundary in odd directions. The θ-space is algebraic (nilpotent), not geometric.
Formally: `partialOdd a f` at `Finset.univ` is always 0 because `a ∈ Finset.univ`.

### Compact support
For the without-boundary case, ν must be compactly supported on the body.
Odd directions are automatically "compact" (finite-dimensional, nilpotent).

## References

- Witten §3.4-3.5: "Stokes' theorem for supermanifolds"
- Rogers §12.3: "Integration and Stokes' theorem"
- Bernstein-Leites (1977): Original proof
