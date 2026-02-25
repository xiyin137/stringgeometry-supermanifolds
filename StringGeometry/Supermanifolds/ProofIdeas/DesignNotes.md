# Supermanifold Theory - Design Notes

## Key Distinction: Fermionic Coordinates vs Grassmann Algebra Coefficients

### The Local Model ℝ^{p|q}

For a super domain ℝ^{p|q}, there are **q fermionic coordinates** θ₁,...,θq.
The structure sheaf assigns to each open U ⊆ ℝ^p:

```
O(U) = C^∞(U, ℝ) ⊗_ℝ ∧(ℝ^q)
```

Sections have the form:
```
f(x,θ) = Σ_I f_I(x) θ^I
```
where:
- I ranges over subsets of {1,...,q}
- f_I : U → ℝ are smooth **ℝ-valued** coefficient functions
- θ^I = θ^{i₁} ∧ ... ∧ θ^{i_k} for I = {i₁ < ... < i_k}

**In the local model, coefficients are in ℝ**, not in a Grassmann algebra.

### Transition Maps and Grassmann Algebra Coefficients

When gluing local models to form a supermanifold, transition maps
```
φ_αβ : U_α ∩ U_β → ℝ^{p|q}
```
have the form:
```
x'_i = f^i_0(x) + θ^j f^i_j(x) + θ^j θ^k f^i_{jk}(x) + ...
θ'_s = ψ^s_j(x) θ^j + ψ^s_{jk}(x) θ^j θ^k + ...
```

For a **single supermanifold** (not a family):
- The coefficients f^i_I, ψ^s_I are still ℝ-valued

For **families of supermanifolds** (e.g., parameterized by odd moduli η₁,...,η_s):
- The coefficients can be **Grassmann algebra-valued** (involving η's)
- This is essential for super Riemann surfaces and supermoduli spaces

### Super Riemann Surfaces

As noted in Witten's "Notes On Supermanifolds And Integration" (arXiv:1209.2199):

> "Though M depends on η₁...ηs, it does not have a reduced space that depends on
> those parameters. The reason is that since the gluing functions ψ^i_αβ can depend
> on the η's, we will in general get gluing laws such as θ_α = θ_β + η and we cannot
> consistently set the θ's to zero unless we also set the η's to zero."

This is why:
- Supermoduli space of super Riemann surfaces involves Grassmann-valued transition maps
- There is no elementary map from supermoduli space to ordinary moduli space
- The Grassmann algebra for coefficients is **separate** from the fermionic coordinates

### Summary

| Context | Fermionic coords | Coefficient algebra |
|---------|-----------------|---------------------|
| Local model ℝ^{p|q} | θ₁,...,θq | ℝ |
| Single supermanifold | θ₁,...,θq | ℝ |
| Family of supermanifolds | θ₁,...,θq | Grassmann algebra (involving η's) |
| Supermoduli space | θ₁,...,θq (on fibers) | Full Grassmann algebra |

## Grassmann Algebra Matrix Warning

**Be careful when manipulating matrices over Grassmann algebra!**

Some properties of matrices over a field do **NOT** apply to matrices over a (super)commutative ring:

1. **Determinant multiplicativity**: `Matrix.det_mul` requires `CommRing` - OK for Grassmann algebra
2. **Invertibility criteria**: A matrix over Grassmann algebra may not have a standard inverse even if its body has nonzero determinant
3. **Eigenvalue decomposition**: Does not generally apply
4. **Rank-nullity**: More subtle over non-fields
5. **Berezinian**: Requires special invertibility conditions (D block must be invertible)

**Key distinction**:
- `body_jacobian_cocycle`: Works over ℝ - standard `Matrix.det_mul` applies
- `berezinian_cocycle_full`: Works over Grassmann algebra - requires `SuperMatrix.ber_mul` (which needs additional hypotheses)

When proving cocycle conditions:
- For body maps: Use `Matrix.det_mul` directly (matrices over ℝ)
- For full Berezinian: Need `SuperMatrix.ber_mul` with invertibility hypotheses

See Deligne-Morgan "Notes on Supersymmetry" for rigorous treatment of supermatrices.

## Grassmann Algebra: Commutative Ring, NOT a Field

**Critical distinction**: The even part of the Grassmann algebra Λ_q is a **commutative ring** with
**zero divisors**, NOT a field. This has several important consequences:

### Zero Divisors
- Example in Λ₂: θ₁θ₂ · θ₁θ₂ = 0, but θ₁θ₂ ≠ 0
- Even elements like θ₁θ₂ ∈ Λ₂^even can be zero divisors
- Products of soul elements can vanish even when neither factor is zero

### Division is Not Available
- `FiniteGrassmannCarrier q` has no `Field` instance
- NEVER use `(x : FiniteGrassmannCarrier q)⁻¹` or division within the Grassmann algebra
- Taylor coefficients 1/n! must be **ℝ-scalar multiplication**: `((n.factorial : ℝ)⁻¹) • (...)`
- The `FPSLogExp` infrastructure handles this correctly via `Algebra ℚ R` (rational scalar action)

### Invertibility Requires Nonzero Body
- An element `a ∈ FiniteGrassmannCarrier q` is invertible iff `grassmannBody a ≠ 0`
- The inverse is constructed via: `a⁻¹ = (body a)⁻¹ · (1 + (body a)⁻¹ · soul a)⁻¹`
- The second factor uses the geometric series `(1 + ε)⁻¹ = Σ (-ε)^n` (terminates by nilpotency)
- This is analogous to `FPSBasic.invertible_iff_constantTerm_invertible` for formal power series

### Berezinian Invertibility
- The Berezinian `Ber(J_φ) = det(A - BD⁻¹C) / det(D)` requires:
  - `det(D)` has **nonzero body** (essential hypothesis, NOT automatic)
  - `det(A - BD⁻¹C)` has **nonzero body** (for the overall Berezinian to be defined)
- These are carried as explicit hypotheses in `SuperJacobian.berezinianAt`

### Implications for Taylor Expansion
- The nilpotent Taylor expansion `f(a + δ) = Σ (1/n!) D^n f(a) · δ^n` uses:
  - Derivatives `D^n f(a)` evaluated at **real** points → produces ℝ values
  - Products `δ_{k₁} · ... · δ_{k_n}` computed in the Grassmann **ring** (not field)
  - Scalar multiplication `(1/n! : ℝ) • (product)` to combine
- The sum truncates at order q because products of q+1 or more soul elements vanish
  (by `grassmann_soul_nilpotent` / `hasNoConstant` argument)
- When δ_k come from **even** coordinate functions, they commute → multinomial formula applies
- When δ_k are general Grassmann elements, ordering in the product matters

### Connection to Existing FPS Infrastructure
- `FPSLogExp.expNilpotent` uses `(k.factorial : ℚ)⁻¹ • L^k` — correct ℚ-scalar multiplication
- `FPSLogExp.logOneSubNilpotent` uses `algebraMap ℚ R (1/(k+1)) * x^(k+1)` — correct rational coefficients
- Both work over `CommRing R` with `Algebra ℚ R`, applicable to even Grassmann subalgebra
- For the full Grassmann algebra (not commutative), these results apply to even elements only

## Partition of Unity: Witten Construction

### The key insight

A partition of unity on a supermanifold cannot be obtained by simply lifting
body PU functions. In chart α, `liftToSuper(ρ̃_α)` is θ-independent. But
when expressed in chart β via the transition T_{αβ}, the even coordinate map
`x_α = x_α(x_β, θ_β)` introduces θ_β-dependence via Taylor expansion.

Therefore the raw sum `S = Σ_α (lift ρ̃_α ∘ T_{αβ})` in chart β is NOT 1.
Its body is 1 (because the body transition reduces to the body PU sum), but
it picks up nilpotent even corrections: `S = 1 + ε` where `ε` is nilpotent.

### The construction (Witten §3.1)

Since S = 1 + ε with ε nilpotent, S is invertible:
  S⁻¹ = 1 - ε + ε² - ... (terminates by nilpotency of ε)

Define ρ_α := (lift ρ̃_α ∘ T_{αβ}) · S⁻¹. Then:
  Σ_α ρ_α = S · S⁻¹ = 1

This is an EXACT identity in the Grassmann algebra, not approximate.

### Formalization status

The algebraic core is fully proven:
- `rawSumAt` computes S
- `rawSumAt_body_eq_one` proves body(S) = 1
- `rawSumInverseAt` computes S⁻¹ via `grassmannGeomInverse`
- `rawSumAt_mul_inverse` proves S · S⁻¹ = 1
- `normalizedPartitionAt` computes ρ_α = (lift ∘ T) · S⁻¹
- `normalizedPartition_sum_one` proves Σ ρ_α = 1

### Design fix for SuperPartitionOfUnity — DONE

The `super_sum_eq_one` field was removed from the `SuperPartitionOfUnity` structure
(it evaluated each function in its own chart — vacuously true). Now the super-level
sum condition is taken as an explicit hypothesis `hSuperSum` in GlobalStokes.lean
theorems, using `composeEvalAt` to express all PU functions in a single chart.
This is proved by `normalizedPartition_sum_one` in PartitionOfUnity.lean.

## Integral Forms vs Densities

Integral forms are sections of the Berezinian line bundle. Under coordinate
change, they transform by the SIGNED Berezinian (not |Ber|). This is different
from measure-theoretic densities which use |det|.

Consequence: `compatible_body` and `SatisfiesChangeOfVar` use signed det,
not |det|. This was fixed in the audit (Round 5).

For oriented supermanifolds, transitions preserve orientation, so
det(body Jacobian) > 0 and the sign doesn't matter in practice.

## Berezinian Body-Level Cancellation

In the Berezin integral of a pullback, the det(D) from the odd substitution
θ' = Dθ + ... (which gives a factor 1/det(D) in the Berezin measure) cancels
with det(D) in the denominator of the Berezinian Ber = det(A-BD⁻¹C)/det(D).

Net result at body level: only det(A_body) = det(body Jacobian) remains.

This is why `compatible_body` has `(det bodyJac)⁻¹` and not the full Berezinian.

## Product Rule for partialEven — PROVEN

The Leibniz rule for `partialEven i` on products of super functions:

  ∂(f·g)/∂xⁱ = (∂f/∂xⁱ)·g + f·(∂g/∂xⁱ)

is proven as `partialEven_mul` in ExteriorDerivative.lean (~120 lines).

**Proof approach**: Instead of working through the full Grassmann product formula
directly, the proof introduces `partialEvenSmooth` at the `SmoothFunction` level
with helper lemmas (distributes over sum, ite, smul; satisfies Leibniz for
SmoothFunction products via `fderiv_mul`). Then a single `simp_rw` chain
transforms the LHS into the RHS by distributing through the Grassmann sum structure.

## SuperDomainFunction Has Full Ring/Algebra Structure

**Key discovery**: `SuperDomainFunction p q` has `Ring` and `Algebra ℝ` instances
(SuperDomainAlgebra.lean:658, :759). This provides:
- `mul_add`, `add_mul` — distributivity
- `mul_assoc` — associativity
- `mul_sum`, `Finset.sum_mul` — distribution over sums (from Semiring)
- `Algebra.smul_mul_assoc`, `Algebra.mul_smul_comm` — scalar compatibility
- `one_mul`, `mul_one` — identity

This dramatically simplifies proofs that need to factor/distribute multiplication
through sums, which arise in the Leibniz rule for d₀ and global integration.
