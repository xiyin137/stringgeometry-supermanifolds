# Phase 2: Integral Form Pullback — Proof Ideas

## Goal

Replace the placeholder `IntegralForm.pullback` with a proper implementation.

## Mathematical Content

For a super coordinate change φ : (x,θ) ↦ (y,η), the pullback of an integral form is:

  φ*[f(y,η) Dy Dη] = f(φ(x,θ)) · Ber(J_φ)(x,θ) · [Dx Dθ]

where:
- f(φ(x,θ)) is the composition from Phase 1
- Ber(J_φ) = det(A - BD⁻¹C) / det(D) is the Berezinian of the super Jacobian
- J_φ = [∂y/∂x, ∂y/∂θ; ∂η/∂x, ∂η/∂θ] is the super Jacobian matrix

## Implementation

### Step 1: Pointwise Evaluation

At each body point x ∈ ℝ^p, evaluate:

1. **Compose**: (f ∘ φ)(x) as a FiniteGrassmannCarrier q element
   - Uses `composeEvalAt` from Phase 1

2. **Berezinian**: Ber(J_φ)(x) as a FiniteGrassmannCarrier q element
   - Uses existing `SuperJacobian.berezinianAt`

3. **Multiply**: product in FiniteGrassmannCarrier q (Ring instance available)

### Step 2: Extract Coefficients

The product (f ∘ φ)(x) · Ber(J_φ)(x) is a Grassmann algebra element. Extract the coefficient of each θ^I to get the SuperDomainFunction:

```lean
noncomputable def IntegralForm.pullback' {p q : ℕ}
    (φ : SuperCoordChange p q) (ω : IntegralForm p q)
    (hD_inv : ...) (hBD_odd : ...) : IntegralForm p q :=
  ⟨⟨fun I => ⟨fun x =>
    let composed := composeEvalAt ω.coefficient φ x
    let ber := φ.jacobian.berezinianAt x hD_inv hBD_odd
    let product := composed * ber  -- In FiniteGrassmannCarrier q
    extractCoefficient product I
  , by ... ⟩⟩⟩
```

### Step 3: Smoothness

The composed-and-multiplied function is smooth in x because:
- Each coefficient of `composeEvalAt` is smooth in x (Phase 1)
- Each coefficient of `berezinianAt` is smooth in x (derivatives of smooth functions)
- Products and sums of smooth functions are smooth

## Key Properties

### Pullback of Identity = Identity
```lean
theorem pullback_id (ω : IntegralForm p q) :
    IntegralForm.pullback' (SuperCoordChange.id) ω = ω
```
Proof: The identity coordinate change has J = I, so Ber(I) = 1, and f ∘ id = f.

### Functoriality (Pullback of Composition)
```lean
theorem pullback_comp (φ ψ : SuperCoordChange p q) (ω : IntegralForm p q) :
    IntegralForm.pullback' φ (IntegralForm.pullback' ψ ω) =
    IntegralForm.pullback' (ψ.comp φ) ω
```
Proof: Uses Ber(J_{ψ∘φ}) = Ber(J_ψ) · Ber(J_φ) (Berezinian multiplicativity, already proven as `ber_mul`).

### Change of Variables
```lean
theorem pullback_preserves_integral (φ : SuperCoordChange p q) (ω : IntegralForm p q)
    (U V : Set (Fin p → ℝ)) (hφ : φ.IsDiffeoOn U V) :
    localBerezinIntegral U (IntegralForm.pullback' φ ω) bodyIntegral =
    localBerezinIntegral V ω bodyIntegral
```
Proof:
1. Berezin integral of pullback extracts top θ-coefficient of (f∘φ) · Ber(J_φ)
2. At θ=0: Ber(J_φ)|_{body} = det(∂y/∂x) / det(∂η/∂θ)|_{body}
3. For the body integral, this gives the standard change of variables with det(body Jacobian)
4. Apply classical change of variables theorem

## Connection to Existing Infrastructure

- `SuperCoordChange.jacobian` — already computes J_φ
- `SuperJacobian.toSuperMatrixAt` — converts to SuperMatrix at a point
- `SuperJacobian.berezinianAt` — computes Ber at a point
- `SuperMatrix.ber_mul` — Berezinian multiplicativity (proven)
- `berezinian_cocycle_from_chain_rule` — cocycle condition (proven)

The main new piece is `composeEvalAt` from Phase 1.

## Estimated Difficulty

MEDIUM. Once Phase 1 (composition) is done, the pullback is a relatively straightforward combination of existing infrastructure.
