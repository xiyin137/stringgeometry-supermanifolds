/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license.
-/
import StringGeometry.Supermanifolds.Integration.SuperCompose
import StringGeometry.Supermanifolds.Helpers.NilpotentInverse
import StringGeometry.Supermanifolds.Helpers.GrassmannSmooth

/-!
# Pullback of Integral Forms

Implements the pullback of integral forms under super coordinate changes:
  φ*[f(y,η) Dy Dη] = f(φ(x,θ)) · Ber(J_φ)(x,θ) · [Dx Dθ]

## Main Definitions

* `IntegralForm.pullbackProper` - pullback using composition + Berezinian

## Main Theorems

* `pullbackProper_apply` - pointwise formula for pullback coefficients

## Mathematical Content

The pullback has two ingredients:
1. **Composition**: f ∘ φ computed via nilpotent Taylor expansion (from SuperCompose.lean)
2. **Berezinian**: Ber(J_φ) = det(A - BD⁻¹C)/det(D) from FiniteGrassmann.lean

The product of these two Grassmann algebra elements gives the pullback integral form.

## References

* Witten, "Notes On Supermanifolds And Integration" (1209.2199), eq. 3.10
-/

noncomputable section

namespace Supermanifolds

open Supermanifolds.Helpers FiniteGrassmannCarrier

/-! ## Berezinian as a FiniteGrassmannCarrier Element -/

/-- Extract the Berezinian at a point as a FiniteGrassmannCarrier element.
    This bridges the type gap between `(finiteGrassmannAlgebra q).evenCarrier`
    (which is `FiniteGrassmannEven q = {x : FiniteGrassmannCarrier q // x.isEven}`)
    and the `FiniteGrassmannCarrier q` used in compositions and products. -/
def berezinianCarrierAt {p q : ℕ} (φ : SuperCoordChange p q) (x : Fin p → ℝ)
    (hD : (finiteGrassmannAlgebra q).IsInvertible (φ.jacobian.toSuperMatrixAt x).D_lifted.det)
    (hBD : ∀ i j, ((φ.jacobian.toSuperMatrixAt x).Bblock *
      (φ.jacobian.toSuperMatrixAt x).D_inv_carrier) i j ∈
      (finiteGrassmannAlgebra q).odd) :
    FiniteGrassmannCarrier q :=
  (φ.jacobian.berezinianAt x hD hBD).val

/-! ## Pullback Pointwise Evaluation -/

/-- Evaluate the pullback of an integral form at a body point x.
    Returns the full Grassmann algebra element:
      (ω.coefficient ∘ φ)(x) · Ber(J_φ)(x) -/
def pullbackEvalAt {p q : ℕ}
    (φ : SuperCoordChange p q) (ω : IntegralForm p q) (x : Fin p → ℝ)
    (hD : (finiteGrassmannAlgebra q).IsInvertible (φ.jacobian.toSuperMatrixAt x).D_lifted.det)
    (hBD : ∀ i j, ((φ.jacobian.toSuperMatrixAt x).Bblock *
      (φ.jacobian.toSuperMatrixAt x).D_inv_carrier) i j ∈
      (finiteGrassmannAlgebra q).odd) :
    FiniteGrassmannCarrier q :=
  composeEvalAt ω.coefficient φ x * berezinianCarrierAt φ x hD hBD

/-- The Berezinian at each point has smooth coefficients as a function of x.

    Each coefficient of Ber(J_φ)(x) is a polynomial in (det D_body(x))⁻¹ and
    the Jacobian entry coefficients at x:
    - Matrix entries of A, B, C, D blocks have smooth coefficients (from evalAtPoint)
    - Matrix products, sums, determinants are polynomial in entries
    - The Grassmann inverse uses the geometric series (polynomial in nilpotent part)
    - (det D_body(x))⁻¹ is smooth since det D_body is nowhere-zero by hD

    The formal proof requires bridging the abstract `Classical.choose`-based inverse
    in GrassmannAlgebra.inv with the explicit geometric series construction. -/
theorem berezinianCarrierAt_grassmannSmooth {p q : ℕ} (φ : SuperCoordChange p q)
    (hD : ∀ x, (finiteGrassmannAlgebra q).IsInvertible
      (φ.jacobian.toSuperMatrixAt x).D_lifted.det)
    (hBD : ∀ x i j, ((φ.jacobian.toSuperMatrixAt x).Bblock *
      (φ.jacobian.toSuperMatrixAt x).D_inv_carrier) i j ∈
      (finiteGrassmannAlgebra q).odd) :
    GrassmannSmooth (fun x => berezinianCarrierAt φ x (hD x) (hBD x)) := by
  -- The Berezinian = det(Schur complement) · det(D)⁻¹
  -- ber.val = det(schurD_lifted).val * (Λ.inv(det(D_lifted))).val by evenVal_mul
  -- Each factor is algebraic in the Jacobian entries (smooth) and the Grassmann inverse (smooth).
  let Mx := fun x => φ.jacobian.toSuperMatrixAt x
  -- Step 1: D_lifted entries .val = Dblock entries are GrassmannSmooth
  have hDL : ∀ i j, GrassmannSmooth (fun x => ((Mx x).D_lifted i j).val) := by
    intro i j
    have h : ∀ x, ((Mx x).D_lifted i j).val = (Mx x).Dblock i j :=
      fun x => (finiteGrassmannAlgebra q).liftEvenMatrix_spec _ _ i j
    simp_rw [h]
    exact evalAtPoint_grassmannSmooth (φ.jacobian.Dblock i j)
  -- Step 2: D_lifted⁻¹ entries .val are GrassmannSmooth (by matInv_even_grassmannSmooth)
  have hDLinv : ∀ i j, GrassmannSmooth (fun x => ((Mx x).D_lifted⁻¹ i j).val) :=
    matInv_even_grassmannSmooth hDL hD
  -- Step 3: D_inv_carrier entries are GrassmannSmooth
  -- D_inv_carrier = matrixEvenToCarrier(D_lifted⁻¹), so entries = (D_lifted⁻¹ entries).val
  have hDinvC : ∀ i j, GrassmannSmooth (fun x => (Mx x).D_inv_carrier i j) := by
    intro i j
    show GrassmannSmooth (fun x => ((Mx x).D_lifted⁻¹ i j).val)
    exact hDLinv i j
  -- Step 4: A, B, C block entries are GrassmannSmooth
  have hA : ∀ i j, GrassmannSmooth (fun x => (Mx x).Ablock i j) :=
    fun i j => evalAtPoint_grassmannSmooth (φ.jacobian.Ablock i j)
  have hB : ∀ i j, GrassmannSmooth (fun x => (Mx x).Bblock i j) :=
    fun i j => evalAtPoint_grassmannSmooth (φ.jacobian.Bblock i j)
  have hC : ∀ i j, GrassmannSmooth (fun x => (Mx x).Cblock i j) :=
    fun i j => evalAtPoint_grassmannSmooth (φ.jacobian.Cblock i j)
  -- Step 5: schurD_carrier entries are GrassmannSmooth (A - B*D_inv*C)
  have hSchur : ∀ i j, GrassmannSmooth (fun x => (Mx x).schurD_carrier i j) :=
    matSub_grassmannSmooth hA
      (matMul_grassmannSmooth (matMul_grassmannSmooth hB hDinvC) hC)
  -- Step 6: schurD_lifted entries .val = schurD_carrier entries are GrassmannSmooth
  have hSL : ∀ i j, GrassmannSmooth (fun x =>
      ((finiteGrassmannAlgebra q).liftEvenMatrix (Mx x).schurD_carrier
        ((Mx x).schurD_even (hBD x)) i j).val) := by
    intro i j
    have h : ∀ x, ((finiteGrassmannAlgebra q).liftEvenMatrix (Mx x).schurD_carrier
        ((Mx x).schurD_even (hBD x)) i j).val = (Mx x).schurD_carrier i j :=
      fun x => (finiteGrassmannAlgebra q).liftEvenMatrix_spec _ _ i j
    simp_rw [h]; exact hSchur i j
  -- Step 7: Combine. ber.val = det(schurD).val * inv(det(D)).val
  have h_eq : ∀ x, berezinianCarrierAt φ x (hD x) (hBD x) =
      ((finiteGrassmannAlgebra q).liftEvenMatrix (Mx x).schurD_carrier
        ((Mx x).schurD_even (hBD x))).det.val *
      ((finiteGrassmannAlgebra q).inv ((Mx x).D_lifted.det) (hD x)).val := by
    intro x; exact evenVal_mul _ _
  simp_rw [h_eq]
  exact (det_even_grassmannSmooth hSL).mul
    (finiteGrassmann_inv_grassmannSmooth (det_even_grassmannSmooth hDL) hD)

/-! ## Full Pullback as IntegralForm -/

/-- Proper pullback of an integral form under a super coordinate change.

    φ*[f(y,η) Dy Dη] = f(φ(x,θ)) · Ber(J_φ)(x,θ) · [Dx Dθ]

    Hypotheses:
    - `hD`: the D-block determinant is invertible at every point
    - `hBD`: the BD⁻¹ product has odd entries at every point

    These are standard requirements for the Berezinian to be defined,
    and hold automatically for any valid super coordinate change
    (where ∂θ'/∂θ is invertible). -/
def IntegralForm.pullbackProper {p q : ℕ}
    (φ : SuperCoordChange p q) (ω : IntegralForm p q)
    (hD : ∀ x, (finiteGrassmannAlgebra q).IsInvertible
      (φ.jacobian.toSuperMatrixAt x).D_lifted.det)
    (hBD : ∀ x i j, ((φ.jacobian.toSuperMatrixAt x).Bblock *
      (φ.jacobian.toSuperMatrixAt x).D_inv_carrier) i j ∈
      (finiteGrassmannAlgebra q).odd) :
    IntegralForm p q where
  coefficient := {
    coefficients := fun J => {
      toFun := fun x => pullbackEvalAt φ ω x (hD x) (hBD x) J
      smooth := by
        -- pullbackEvalAt = composeEvalAt * berezinianCarrierAt
        -- Both factors have smooth coefficients, so the product does.
        show ContDiff ℝ ⊤ (fun x => pullbackEvalAt φ ω x (hD x) (hBD x) J)
        simp only [pullbackEvalAt]
        -- Factor 1: composeEvalAt has smooth coefficients (from SuperCompose)
        have h1 : GrassmannSmooth (fun x => composeEvalAt ω.coefficient φ x) :=
          GrassmannSmooth.finset_sum (fun I _ =>
            (smoothTaylorGrassmann_grassmannSmooth (ω.coefficient.coefficients I)
              (fun x k => (φ.evenMap k).evalAtPoint x)
              (fun k => evalAtPoint_grassmannSmooth (φ.evenMap k))).mul
            (grassmannMonomial_grassmannSmooth
              (fun x a => (φ.oddMap a).evalAtPoint x)
              (fun a => evalAtPoint_grassmannSmooth (φ.oddMap a)) I))
        -- Factor 2: berezinianCarrierAt has smooth coefficients
        have h2 := berezinianCarrierAt_grassmannSmooth φ hD hBD
        exact (h1.mul h2) J
    }
  }

/-- The J-th coefficient of the pullback at point x is the J-th Grassmann
    component of (f ∘ φ)(x) · Ber(J_φ)(x). -/
theorem pullbackProper_apply {p q : ℕ}
    (φ : SuperCoordChange p q) (ω : IntegralForm p q)
    (hD : ∀ x, (finiteGrassmannAlgebra q).IsInvertible
      (φ.jacobian.toSuperMatrixAt x).D_lifted.det)
    (hBD : ∀ x i j, ((φ.jacobian.toSuperMatrixAt x).Bblock *
      (φ.jacobian.toSuperMatrixAt x).D_inv_carrier) i j ∈
      (finiteGrassmannAlgebra q).odd)
    (x : Fin p → ℝ) (J : Finset (Fin q)) :
    ((IntegralForm.pullbackProper φ ω hD hBD).coefficient.coefficients J).toFun x =
    pullbackEvalAt φ ω x (hD x) (hBD x) J := by
  rfl

/-! ## Properties of the Pullback -/

/-- The pullback of the zero form is zero. -/
theorem pullbackProper_zero {p q : ℕ}
    (φ : SuperCoordChange p q)
    (hD : ∀ x, (finiteGrassmannAlgebra q).IsInvertible
      (φ.jacobian.toSuperMatrixAt x).D_lifted.det)
    (hBD : ∀ x i j, ((φ.jacobian.toSuperMatrixAt x).Bblock *
      (φ.jacobian.toSuperMatrixAt x).D_inv_carrier) i j ∈
      (finiteGrassmannAlgebra q).odd) :
    IntegralForm.pullbackProper φ (0 : IntegralForm p q) hD hBD = 0 := by
  -- The pullback of 0: composition of 0 gives 0, then 0 * Ber = 0
  show IntegralForm.mk _ = IntegralForm.mk _
  congr 1; ext I x
  show (composeEvalAt (0 : IntegralForm p q).coefficient φ x *
    berezinianCarrierAt φ x (hD x) (hBD x)) I = 0
  -- (0 : IntegralForm).coefficient = (0 : SuperDomainFunction) definitionally
  change (composeEvalAt (0 : SuperDomainFunction p q) φ x *
    berezinianCarrierAt φ x (hD x) (hBD x)) I = 0
  -- composeEvalAt of the zero function is 0
  have hc : composeEvalAt (0 : SuperDomainFunction p q) φ x = 0 := by
    simp only [composeEvalAt]
    apply Finset.sum_eq_zero
    intro J _
    rw [SuperDomainFunction.zero_coefficients]
    -- (0 : SmoothFunction p) = ⟨fun _ => 0, contDiff_const⟩ definitionally
    change smoothTaylorGrassmann ⟨fun _ => (0 : ℝ), contDiff_const⟩ _ *
      grassmannMonomial _ J = 0
    rw [smoothTaylorGrassmann_const]
    have : grassmannScalar (q := q) 0 = 0 := by
      funext K; simp [grassmannScalar]
    rw [this, zero_mul]
  rw [hc, zero_mul, zero_apply]

/-! ## Berezin Integral of Pullback

The key property: the Berezin integral of the pullback equals the integral
of the original form in the new coordinates. This is the change of variables formula. -/

/-- The top-component extraction commutes with pullback in a specific way:
    berezinIntegralOdd of the pullback coefficient equals
    (top component of composed function · Berezinian) integrated over the body. -/
theorem pullback_berezinOdd {p q : ℕ}
    (φ : SuperCoordChange p q) (ω : IntegralForm p q)
    (hD : ∀ x, (finiteGrassmannAlgebra q).IsInvertible
      (φ.jacobian.toSuperMatrixAt x).D_lifted.det)
    (hBD : ∀ x i j, ((φ.jacobian.toSuperMatrixAt x).Bblock *
      (φ.jacobian.toSuperMatrixAt x).D_inv_carrier) i j ∈
      (finiteGrassmannAlgebra q).odd)
    (x : Fin p → ℝ) :
    berezinIntegralOdd (IntegralForm.pullbackProper φ ω hD hBD).coefficient x =
    pullbackEvalAt φ ω x (hD x) (hBD x) (Finset.univ : Finset (Fin q)) := by
  -- berezinIntegralOdd extracts the top (Finset.univ) component
  -- pullbackProper_apply tells us the coefficient at Finset.univ
  unfold berezinIntegralOdd
  rfl

/-- Explicit finite-sum expansion of the pullback top coefficient.

    This rewrites the top Berezin component as the convolution formula for
    Grassmann multiplication at `Finset.univ`. It is the concrete target used
    to discharge the body-level CoV bridge in `GlobalStokes.lean`. -/
theorem pullback_berezinOdd_expand {p q : ℕ}
    (φ : SuperCoordChange p q) (ω : IntegralForm p q)
    (hD : ∀ x, (finiteGrassmannAlgebra q).IsInvertible
      (φ.jacobian.toSuperMatrixAt x).D_lifted.det)
    (hBD : ∀ x i j, ((φ.jacobian.toSuperMatrixAt x).Bblock *
      (φ.jacobian.toSuperMatrixAt x).D_inv_carrier) i j ∈
      (finiteGrassmannAlgebra q).odd)
    (x : Fin p → ℝ) :
    berezinIntegralOdd (IntegralForm.pullbackProper φ ω hD hBD).coefficient x =
    Finset.univ.sum (fun I =>
      Finset.univ.sum (fun J =>
        if I ∪ J = (Finset.univ : Finset (Fin q)) ∧ I ∩ J = ∅ then
          (FiniteGrassmannCarrier.reorderSign I J : ℝ) *
            composeEvalAt ω.coefficient φ x I *
            berezinianCarrierAt φ x (hD x) (hBD x) J
        else 0)) := by
  rw [pullback_berezinOdd]
  unfold pullbackEvalAt
  simp [FiniteGrassmannCarrier.mul_apply]

end Supermanifolds
