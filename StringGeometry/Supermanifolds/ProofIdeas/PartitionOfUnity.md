# Partition of Unity on Supermanifolds

## The Construction (Witten, arXiv:1209.2199 §3.1)

### Step 1: Body partition of unity

Start with a smooth partition of unity {ρ̃_α} on M_red subordinate to {U_α,red}.
Exists by paracompactness (Mathlib's `SmoothPartitionOfUnity.exists_isSubordinate`).

### Step 2: Lift to supermanifold

In chart α, lift ρ̃_α to a θ-independent super function:

    (lift ρ̃_α)(x_α, θ_α) := ρ̃_α(x_α)

This is `liftToSuper` in the code — it puts ρ̃_α in the ∅-coefficient and
zeros everywhere else.

### Step 3: Compose to a common chart

To sum the partition functions, express them all in one chart β.
Use super composition: `composeEvalAt(liftToSuper ρ̃_α, T_{αβ}, x_β)`.

The transition T_{αβ} has even coordinate map x_α = x_α(x_β, θ_β) with
θ-dependent corrections. Taylor expanding ρ̃_α(x_α(x_β, θ_β)) gives:

    ρ̃_α(body(x_α)) + derivatives × (nilpotent θ-corrections) + ...

This is NOT θ-independent in chart β.

### Step 4: Raw sum = 1 + nilpotent

The raw sum in chart β: S_β(x) = Σ_α composeEvalAt(liftToSuper ρ̃_α, T_{αβ}, x)

- Body: grassmannBody(S_β) = 1 (body PU sum, proved in `rawSumAt_body_eq_one`)
- Soul: nilpotent (proved in `rawSumAt_soul_nilpotent`)
- Decomposition: S = 1 + ε where ε is nilpotent (proved in `rawSumAt_eq_one_add_eps`)

### Step 5: Normalize by dividing by sum

Since S = 1 + ε with ε nilpotent, S is invertible:

    S⁻¹ = grassmannGeomInverse(ε) = Σ_{n=0}^q (-ε)^n

This terminates because ε^{q+1} = 0 by nilpotency of the Grassmann soul.

Define: ρ_α := composeEvalAt(liftToSuper ρ̃_α, T_{αβ}, x) · S⁻¹

### Step 6: Verify sum = 1

Σ_α ρ_α = Σ_α [(lift ∘ T) · S⁻¹] = (Σ_α lift ∘ T) · S⁻¹ = S · S⁻¹ = 1

This is proved in `normalizedPartition_sum_one`.

---

## Formalization Status

### What's proven (PartitionOfUnity.lean, 0 sorrys)

| Lemma | Content |
|-------|---------|
| `rawSumAt_body_eq_one` | grassmannBody(S) = 1 |
| `rawSumAt_soul_nilpotent` | soul(S) has no constant term |
| `rawSumAt_eq_one_add_eps` | S = 1 + soul(S) |
| `rawSumAt_isUnit` | S is invertible |
| `rawSumAt_mul_inverse` | S · S⁻¹ = 1 |
| `rawSumInverseAt_mul` | S⁻¹ · S = 1 |
| `normalizedPartition_sum_one` | Σ_α ρ_α = 1 |
| `superPartitionFromBody` | Constructs SuperPartitionOfUnity from body data |

### Fix Applied — DONE

**Problem**: `SuperPartitionOfUnity.super_sum_eq_one` evaluated each function in
its own chart, which trivially gives I≠∅ components = 0. Useless for the
double-sum trick (needs sum in a SINGLE chart to be 1).

**Solution**: Removed `super_sum_eq_one` from the `SuperPartitionOfUnity` structure
entirely. The super-level sum condition is now an explicit hypothesis `hSuperSum`
in the GlobalStokes.lean theorems that need it:

```lean
(transitions : pu.index → SuperCoordChange dim.even dim.odd)
(hSuperSum : ∀ x : Fin dim.even → ℝ,
    @Finset.sum pu.index (FiniteGrassmannCarrier dim.odd) _
      (@Finset.univ pu.index pu.finIndex) (fun α =>
        composeEvalAt (pu.functions α) (transitions α) x) = 1)
```

This is satisfied by the Witten-normalized partition, proved in
`normalizedPartition_sum_one` (PartitionOfUnity.lean).

### What's sorry'd

**`partition_of_unity_exists`** (BerezinIntegration.lean): Needs to connect
Mathlib's paracompactness → body PU → `BodyPartitionData` → `superPartitionFromBody`.

---

## Interaction with Berezin Integration

For the Berezin integral of ρ_α · f_α, note that ρ_α is θ-DEPENDENT
(after normalization). So:

    ∫dθ [ρ_α · f] ≠ ρ̃_α · ∫dθ f

The product ρ_α · f mixes θ-components. Only at body level (leading order)
does the factorization hold, via `berezin_lift_factor` for the θ-independent
part.

This is fine — the global integral is still well-defined, and the
double-sum trick with Σ ρ_α = 1 handles the corrections exactly.

---

## References

- Witten, "Notes on Supermanifolds and Integration" (arXiv:1209.2199), §3.1
- Rogers, "Supermanifolds" (2007), §11.2
