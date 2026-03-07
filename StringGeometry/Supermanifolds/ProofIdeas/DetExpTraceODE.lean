/-
ODE-based proof of det(exp(A)) = exp(tr(A)) for nilpotent matrices over commutative ℚ-algebras.

Strategy:
1. Define epm(X) = Σ_k C(1/k! * A^k) * X^k (polynomial matrix)
2. Show deriv(epm_{ij}) = (C(A) * epm)_{ij} (entry-wise derivative)
3. Leibniz formula: deriv(det M) = Σ_j det(M.updateCol j (deriv col j))
4. Trace identity: Σ_j det(M.updateCol j ((A*M) col j)) = tr(A) * det(M)
5. ODE: deriv(det(epm)) = C(tr(A)) * det(epm)
6. ODE uniqueness + eval: det(expMatrixNilpotent A N) = exp(tr(A))
-/
import Mathlib.Algebra.Algebra.Rat
import Mathlib.RingTheory.Nilpotent.Exp
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Coeff
import StringGeometry.Supermanifolds.Helpers.FormalPowerSeries

open Finset Nat Matrix Polynomial FormalPowerSeries

namespace DetExpTraceODE

variable {S : Type*} [CommRing S] [Algebra ℚ S]

/-! ### Polynomial matrix exponential -/

/-- Polynomial version of expMatrixNilpotent: entries are polynomials in X. -/
noncomputable def expPolyMatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) S) (N : ℕ) :
    Matrix (Fin n) (Fin n) (Polynomial S) :=
  Matrix.of (fun i j => ∑ k ∈ range (N + 1),
    Polynomial.C (algebraMap ℚ S (1 / ↑(k !)) * (A ^ k) i j) * X ^ k)

/-- Constant matrix: lift A to polynomial constants. -/
noncomputable def constMatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) S) :
    Matrix (Fin n) (Fin n) (Polynomial S) :=
  Matrix.of (fun i j => Polynomial.C (A i j))

/-- Nilpotent exp polynomial: Σ_{k < M} C(c^k/k!) * X^k. -/
noncomputable def nilExpPoly (c : S) (M : ℕ) : Polynomial S :=
  ∑ k ∈ range M, Polynomial.C (algebraMap ℚ S (1 / ↑(k !)) * c ^ k) * X ^ k

/-! ### Helper lemmas -/

/-- In a ℚ-algebra, positive natural numbers are units. -/
lemma natCast_isUnit_of_pos (n : ℕ) (hn : 0 < n) : IsUnit (↑n : S) := by
  rw [show (↑n : S) = algebraMap ℚ S (↑n : ℚ) from (map_natCast _ n).symm]
  exact (IsUnit.of_mul_eq_one (algebraMap ℚ S ((↑n : ℚ)⁻¹))
    (by rw [← map_mul, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (by omega)), map_one]))

/-- Factorial cancellation: 1/(k+1)! * (k+1) = 1/k! -/
lemma factorial_cancel_alg (k : ℕ) :
    algebraMap ℚ S (1 / ↑((k + 1) !)) * (↑(k + 1) : S) =
    algebraMap ℚ S (1 / ↑(k !)) := by
  rw [← map_natCast (algebraMap ℚ S), ← map_mul]; congr 1
  rw [Nat.factorial_succ, Nat.cast_mul]
  field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_pos k).ne',
    Nat.cast_ne_zero.mpr (show k + 1 ≠ 0 by omega)]

/-- Variant with c^{k+1} factor. -/
lemma factorial_cancel_with_pow (k : ℕ) (c : S) :
    algebraMap ℚ S (1 / ↑((k + 1) !)) * c ^ (k + 1) * (↑(k + 1) : S) =
    algebraMap ℚ S (1 / ↑(k !)) * c ^ (k + 1) := by
  calc _ = (algebraMap ℚ S (1 / ↑((k + 1) !)) * ↑(k + 1)) * c ^ (k + 1) := by ring
    _ = _ := by rw [factorial_cancel_alg k]

/-! ### eval at 0 and 1 -/

omit [Algebra ℚ S] in
lemma eval_det_eq {n : ℕ} (M : Matrix (Fin n) (Fin n) (Polynomial S)) (r : S) :
    Polynomial.eval r M.det = (M.map (Polynomial.eval r)).det := by
  have h := RingHom.map_det (Polynomial.evalRingHom r) M
  simpa [RingHom.mapMatrix, Polynomial.coe_evalRingHom] using h

lemma eval_zero_expPolyMatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) S) (N : ℕ) :
    (expPolyMatrix A N).map (Polynomial.eval 0) = 1 := by
  ext i j
  simp only [expPolyMatrix, Matrix.of_apply, Matrix.map_apply, Matrix.one_apply]
  rw [Polynomial.eval_finset_sum, Finset.sum_range_succ']
  simp only [Nat.factorial_zero, Nat.cast_one, div_one, map_one, pow_zero, one_mul,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
    zero_pow (Nat.succ_ne_zero _), mul_zero, Finset.sum_const_zero]
  simp [Matrix.one_apply]

lemma eval_one_expPolyMatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) S) (N : ℕ) :
    (expPolyMatrix A N).map (Polynomial.eval 1) = MatrixExpLog.expMatrixNilpotent A N := by
  ext i j
  simp only [expPolyMatrix, Matrix.of_apply, Matrix.map_apply, Polynomial.eval_finset_sum,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
    one_pow, mul_one]
  unfold MatrixExpLog.expMatrixNilpotent
  simp only [Matrix.sum_apply, Algebra.smul_def]
  apply Finset.sum_congr rfl; intro k _
  simp [Matrix.mul_apply, Algebra.algebraMap_eq_smul_one, Matrix.one_apply, Finset.mem_univ]

lemma nilExpPoly_eval_zero (c : S) (M : ℕ) (hM : 0 < M) :
    Polynomial.eval 0 (nilExpPoly c M) = 1 := by
  cases M with
  | zero => omega
  | succ N =>
    unfold nilExpPoly
    rw [Polynomial.eval_finset_sum, Finset.sum_range_succ']
    simp only [Nat.factorial_zero, Nat.cast_one, div_one, map_one, pow_zero, mul_one,
      Polynomial.eval_one, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X, zero_pow (Nat.succ_ne_zero _), mul_zero, Finset.sum_const_zero,
      zero_add]

lemma nilExpPoly_eval_one (c : S) (M : ℕ) (hNil : c ^ M = 0) :
    Polynomial.eval 1 (nilExpPoly c M) = IsNilpotent.exp c := by
  unfold nilExpPoly
  rw [Polynomial.eval_finset_sum]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
    one_pow, mul_one]
  rw [IsNilpotent.exp_eq_sum hNil]
  apply Finset.sum_congr rfl; intro k _
  rw [show (1 : ℚ) / (↑(k !) : ℚ) = (↑(k !) : ℚ)⁻¹ from one_div _, Algebra.smul_def]

/-! ### Entry-wise derivative identity -/

/-- Entry-wise derivative of expPolyMatrix equals (constMatrix(A) * expPolyMatrix). -/
lemma deriv_expPolyMatrix_entry {n : ℕ} (A : Matrix (Fin n) (Fin n) S) (N : ℕ)
    (hNil : A ^ N = 0) (i j : Fin n) :
    Polynomial.derivative ((expPolyMatrix A N) i j) =
    ∑ l, Polynomial.C (A i l) * (expPolyMatrix A N) l j := by
  unfold expPolyMatrix
  simp only [Matrix.of_apply]
  -- Both sides equal Σ_{m < N} C(1/m! * (A^{m+1})_{ij}) * X^m
  -- LHS: derivative computation + factorial cancellation
  rw [map_sum, Finset.sum_range_succ']
  simp only [Nat.factorial_zero, Nat.cast_one, div_one, map_one, pow_zero, one_mul,
    mul_one, Polynomial.derivative_C, add_zero]
  conv_lhs =>
    arg 2; ext k
    rw [Polynomial.derivative_C_mul_X_pow, show k + 1 - 1 = k from by omega,
        show Polynomial.C (algebraMap ℚ S (1 / ↑((k + 1) !)) * (A ^ (k + 1)) i j * ↑(k + 1)) =
          Polynomial.C (algebraMap ℚ S (1 / ↑(k !)) * (A ^ (k + 1)) i j) from by
          congr 1; rw [mul_assoc, mul_comm ((A ^ (k + 1)) i j) _, ← mul_assoc,
                        factorial_cancel_alg k]]
  -- RHS: matrix multiplication + dropping zero last term
  simp_rw [Finset.mul_sum, ← mul_assoc, ← Polynomial.C_mul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul]
  conv_rhs =>
    arg 2; ext k; arg 1
    rw [show (∑ i_1, Polynomial.C (A i i_1 * (algebraMap ℚ S (1 / ↑(k !)) * (A ^ k) i_1 j))) =
      Polynomial.C (algebraMap ℚ S (1 / ↑(k !)) * (A ^ (k + 1)) i j) from by
      simp_rw [← map_sum]; congr 1
      rw [_root_.pow_succ', mul_apply, Finset.mul_sum]
      congr 1; ext l; ring]
  rw [Finset.sum_range_succ]
  have hAN1 : (A ^ (N + 1)) i j = 0 := by
    have : A ^ (N + 1) = 0 := by rw [_root_.pow_succ', hNil, mul_zero]
    simp [this]
  rw [hAN1, mul_zero, map_zero, zero_mul, add_zero]

/-! ### Leibniz formula for determinant derivative -/

omit [Algebra ℚ S] in
/-- Derivative of determinant = sum over columns of det with that column differentiated. -/
theorem derivative_det_eq_sum_updateCol {n : ℕ}
    (M : Matrix (Fin n) (Fin n) (Polynomial S)) :
    Polynomial.derivative M.det =
    ∑ j : Fin n, (M.updateCol j (fun i => Polynomial.derivative (M i j))).det := by
  conv_lhs => rw [Matrix.det_apply']
  rw [map_sum]
  have sign_deriv : ∀ (σ : Equiv.Perm (Fin n)) (p : Polynomial S),
      Polynomial.derivative (↑↑(Equiv.Perm.sign σ) * p) =
      ↑↑(Equiv.Perm.sign σ) * Polynomial.derivative p := by
    intro σ p
    have h : (↑↑(Equiv.Perm.sign σ) : Polynomial S) = Polynomial.C (↑↑(Equiv.Perm.sign σ) : S) := by
      cases Equiv.Perm.sign σ with | mk val prop => rw [map_intCast]
    rw [h, Polynomial.derivative_C_mul]
  simp_rw [sign_deriv, Polynomial.derivative_prod_finset, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro j _
  rw [Matrix.det_apply']
  apply Finset.sum_congr rfl; intro σ _
  rw [← Finset.mul_prod_erase Finset.univ (fun i => (M.updateCol j
    (fun k => Polynomial.derivative (M k j))) (σ i) i) (Finset.mem_univ j)]
  simp only [Matrix.updateCol_self]
  congr 1; rw [mul_comm]; congr 1
  apply Finset.prod_congr rfl; intro i hi
  rw [Matrix.updateCol_ne (Finset.mem_erase.mp hi).1]

/-! ### Trace identity -/

omit [Algebra ℚ S] in
/-- Sum of dets with columns replaced by (A*M) columns equals tr(A)*det(M). -/
theorem sum_det_updateCol_mul_eq_trace_mul_det
    {m : Type*} [DecidableEq m] [Fintype m] {R : Type*} [CommRing R]
    (A M : Matrix m m R) :
    ∑ j, (M.updateCol j (fun i => (A * M) i j)).det = A.trace * M.det := by
  simp_rw [← cramer_apply, cramer_eq_adjugate_mulVec, mulVec, dotProduct]
  rw [Finset.sum_comm]
  simp_rw [mul_comm (M.adjugate _ _)]
  change ∑ k, ∑ j, (A * M) k j * M.adjugate j k = _
  rw [show (∑ k, ∑ j, (A * M) k j * M.adjugate j k) =
    ((A * M) * M.adjugate).trace from by simp [Matrix.trace, Matrix.mul_apply]]
  rw [Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.mul_smul, Matrix.trace_smul,
      Matrix.mul_one, smul_eq_mul, mul_comm]

/-! ### ODE for det(expPolyMatrix) -/

/-- The ODE: derivative(det(epm(X))) = C(tr(A)) * det(epm(X)). -/
theorem ode_det_expPolyMatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) S) (N : ℕ)
    (hNil : A ^ N = 0) :
    Polynomial.derivative (expPolyMatrix A N).det =
    Polynomial.C A.trace * (expPolyMatrix A N).det := by
  set M := expPolyMatrix A N with hM_def
  rw [derivative_det_eq_sum_updateCol M]
  have hderiv_eq : ∀ j₀ : Fin n,
      (M.updateCol j₀ (fun i => Polynomial.derivative (M i j₀))).det =
      (M.updateCol j₀ (fun i => (constMatrix A * M) i j₀)).det := by
    intro j₀; congr 1; ext i j'
    by_cases hj : j' = j₀
    · subst hj; simp only [updateCol_self]
      rw [deriv_expPolyMatrix_entry A N hNil i j', hM_def]
      unfold constMatrix; rw [mul_apply]; simp [Matrix.of_apply]
    · simp [updateCol_ne hj]
  simp_rw [hderiv_eq]
  rw [sum_det_updateCol_mul_eq_trace_mul_det (constMatrix A) M]
  congr 1
  unfold constMatrix Matrix.trace
  simp [Matrix.of_apply, Matrix.diag, map_sum]

/-! ### ODE uniqueness -/

/-- If P' = C(c)*P and P(0) = 0, then P = 0 (in a ℚ-algebra). -/
lemma poly_ode_zero {c : S} {P : Polynomial S}
    (hODE : Polynomial.derivative P = Polynomial.C c * P) (h0 : P.coeff 0 = 0) :
    P = 0 := by
  have hcoeff : ∀ k, P.coeff k = 0 := by
    intro k; induction k with
    | zero => exact h0
    | succ k ih =>
      have hrec := congr_arg (fun p => p.coeff k) hODE
      simp only [Polynomial.coeff_derivative, Polynomial.coeff_C_mul] at hrec
      rw [ih, mul_zero] at hrec
      have hunit : IsUnit (↑(k + 1) : S) := natCast_isUnit_of_pos (k + 1) (by omega)
      rw [show (↑k + 1 : S) = (↑(k + 1) : S) from by push_cast; ring] at hrec
      rw [mul_comm] at hrec
      exact hunit.mul_right_eq_zero.mp hrec
  ext k; simp [hcoeff k]

/-! ### ODE for nilExpPoly -/

/-- The nilpotent exp polynomial satisfies E' = C(c) * E. -/
lemma nilExpPoly_ode (c : S) (M : ℕ) (hNil : c ^ M = 0) :
    Polynomial.derivative (nilExpPoly c M) = Polynomial.C c * nilExpPoly c M := by
  cases M with
  | zero => simp only [nilExpPoly, Finset.range_zero, Finset.sum_empty, map_zero, mul_zero]
  | succ N =>
    set T := ∑ k ∈ range N, Polynomial.C (algebraMap ℚ S (1 / ↑(k !)) * c ^ (k + 1)) * X ^ k
    have hL : Polynomial.derivative (nilExpPoly c (N + 1)) = T := by
      unfold nilExpPoly
      rw [map_sum, Finset.sum_range_succ']
      simp only [Nat.factorial_zero, Nat.cast_one, div_one, map_one, pow_zero, mul_one,
        Polynomial.derivative_one, add_zero]
      apply Finset.sum_congr rfl; intro k _
      rw [Polynomial.derivative_C_mul_X_pow, show k + 1 - 1 = k from by omega, show
        Polynomial.C (algebraMap ℚ S (1 / ↑((k + 1) !)) * c ^ (k + 1) * ↑(k + 1)) =
        Polynomial.C (algebraMap ℚ S (1 / ↑(k !)) * c ^ (k + 1)) from by
          congr 1; exact factorial_cancel_with_pow k c]
    have hR : Polynomial.C c * nilExpPoly c (N + 1) = T := by
      unfold nilExpPoly
      rw [Finset.mul_sum, Finset.sum_range_succ]
      simp only [← mul_assoc, ← Polynomial.C_mul]
      have hlast : c * algebraMap ℚ S (1 / ↑(N !)) * c ^ N =
          algebraMap ℚ S (1 / ↑(N !)) * c ^ (N + 1) := by rw [pow_succ]; ring
      rw [hlast, hNil, mul_zero, map_zero, zero_mul, add_zero]
      apply Finset.sum_congr rfl; intro k _
      congr 1; rw [pow_succ]; ring
    rw [hL, hR]

/-! ### Main theorem -/

omit [Algebra ℚ S] in
/-- Trace of a nilpotent matrix is nilpotent (from Mathlib via Cayley-Hamilton). -/
lemma trace_isNilpotent {n : ℕ} (A : Matrix (Fin n) (Fin n) S) (hNil : IsNilpotent A) :
    IsNilpotent A.trace :=
  Matrix.isNilpotent_trace_of_isNilpotent hNil

/-- det(exp(A)) = exp(tr(A)) for nilpotent matrices over commutative ℚ-algebras. -/
theorem det_expMatrix_eq_exp_trace_ode {n : ℕ}
    (A : Matrix (Fin n) (Fin n) S) (N : ℕ) (hNil : A ^ N = 0) :
    (MatrixExpLog.expMatrixNilpotent A N).det = IsNilpotent.exp A.trace := by
  set P := (expPolyMatrix A N).det
  have hA_nil : IsNilpotent A := ⟨N, hNil⟩
  have htr_nil : IsNilpotent A.trace := trace_isNilpotent A hA_nil
  obtain ⟨M, htrM⟩ := htr_nil
  set E := nilExpPoly A.trace M
  have hP_ode : Polynomial.derivative P = Polynomial.C A.trace * P :=
    ode_det_expPolyMatrix A N hNil
  have hE_ode : Polynomial.derivative E = Polynomial.C A.trace * E :=
    nilExpPoly_ode A.trace M htrM
  have hP0 : Polynomial.eval 0 P = 1 := by
    rw [eval_det_eq, eval_zero_expPolyMatrix, det_one]
  have hE0 : Polynomial.eval 0 E = 1 := by
    cases M with
    | zero =>
      simp only [pow_zero] at htrM
      haveI : Subsingleton S := subsingleton_of_zero_eq_one htrM.symm
      exact Subsingleton.elim _ _
    | succ M' => exact nilExpPoly_eval_zero A.trace (M' + 1) (by omega)
  have hQ_ode : Polynomial.derivative (P - E) = Polynomial.C A.trace * (P - E) := by
    rw [map_sub, hP_ode, hE_ode, mul_sub]
  have hQ0 : (P - E).coeff 0 = 0 := by
    rw [Polynomial.coeff_sub, Polynomial.coeff_zero_eq_eval_zero,
        Polynomial.coeff_zero_eq_eval_zero, hP0, hE0, sub_self]
  have hPE : P = E := sub_eq_zero.mp (poly_ode_zero hQ_ode hQ0)
  have hP1 : Polynomial.eval 1 P = (MatrixExpLog.expMatrixNilpotent A N).det := by
    rw [eval_det_eq, eval_one_expPolyMatrix]
  have hE1 : Polynomial.eval 1 E = IsNilpotent.exp A.trace :=
    nilExpPoly_eval_one A.trace M htrM
  calc (MatrixExpLog.expMatrixNilpotent A N).det
      = Polynomial.eval 1 P := hP1.symm
    _ = Polynomial.eval 1 E := by rw [hPE]
    _ = IsNilpotent.exp A.trace := hE1

end DetExpTraceODE
