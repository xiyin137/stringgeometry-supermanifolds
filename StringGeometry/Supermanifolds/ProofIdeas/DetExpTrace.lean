import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.RingTheory.Nilpotent.Exp
import StringGeometry.Supermanifolds.Helpers.FormalPowerSeries

open Finset Nat

namespace DetExpTraceScratch

open FormalPowerSeries
open MatrixExpLog

variable {S : Type*} [CommRing S] [Algebra ℚ S]

/-- If `a` is nilpotent and `exp(a) = 1`, then `a = 0`. -/
theorem exp_eq_one_imp_zero {R : Type*} [Ring R] [Module ℚ R] (a : R)
    (hNil : IsNilpotent a) (hExp : IsNilpotent.exp a = 1) : a = 0 := by
  set N := nilpotencyClass a
  have haN : a ^ N = 0 := pow_nilpotencyClass hNil
  cases hN0 : N with
  | zero =>
    rw [hN0] at haN; simp at haN
    exact (subsingleton_of_zero_eq_one haN.symm).elim _ _
  | succ M =>
    cases M with
    | zero => rw [hN0] at haN; simpa using haN
    | succ M' =>
      have hExpSum : (∑ i ∈ Finset.range (M' + 2), ((↑(Nat.factorial i) : ℚ)⁻¹ • a ^ i)) = 1 := by
        rw [← hN0]; rwa [IsNilpotent.exp_eq_sum haN] at hExp
      rw [show M' + 2 = (M' + 1) + 1 from rfl, Finset.sum_range_succ'] at hExpSum
      simp only [Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero, one_smul] at hExpSum
      set tail := ∑ k ∈ Finset.range (M' + 1), ((↑(Nat.factorial (k + 1)) : ℚ)⁻¹ • a ^ (k + 1))
      have htail_zero : tail = 0 := by
        have := sub_eq_zero.mpr hExpSum; simp at this; exact this
      set u := ∑ k ∈ Finset.range (M' + 1), ((↑(Nat.factorial (k + 1)) : ℚ)⁻¹ • a ^ k)
      have hfactor : a * u = 0 := by
        show a * (∑ k ∈ Finset.range (M' + 1), _) = 0
        rw [Finset.mul_sum]
        convert htail_zero using 1
        apply Finset.sum_congr rfl; intro i _
        rw [mul_smul_comm]; congr 1; rw [← _root_.pow_succ']
      have hu_eq : u = 1 + a * ∑ k ∈ Finset.range M', ((↑(Nat.factorial (k + 2)) : ℚ)⁻¹ • a ^ k) := by
        show (∑ k ∈ Finset.range (M' + 1), _) = _
        rw [Finset.sum_range_succ', Finset.mul_sum, add_comm]
        congr 1
        · simp [Nat.factorial]
        · apply Finset.sum_congr rfl; intro i _
          rw [mul_smul_comm]; congr 1; rw [← _root_.pow_succ']
      set w := ∑ k ∈ Finset.range M', ((↑(Nat.factorial (k + 2)) : ℚ)⁻¹ • a ^ k)
      have haw_comm : Commute a w := by
        apply Commute.sum_right; intro k _
        exact Commute.smul_right (Commute.pow_right (Commute.refl a) k) _
      have haw_nil : IsNilpotent (a * w) := by
        obtain ⟨n, hn⟩ := hNil; exact ⟨n, by rw [haw_comm.mul_pow, hn, zero_mul]⟩
      have hu_unit : IsUnit u := by rw [hu_eq]; exact haw_nil.isUnit_one_add
      exact hu_unit.mul_left_eq_zero.mp hfactor

noncomputable def detExpPoly {n : ℕ} (A : Matrix (Fin n) (Fin n) S) (N : ℕ) : Polynomial S :=
  (expMatrixNilpotent ((Polynomial.X : Polynomial S) • A.map Polynomial.C) N).det

theorem detExpPoly_eval {n : ℕ} (A : Matrix (Fin n) (Fin n) S) (N : ℕ) (r : S) :
    (detExpPoly A N).eval r = (expMatrixNilpotent (r • A) N).det := by
  unfold detExpPoly
  rw [← Polynomial.coe_evalRingHom, RingHom.map_det]
  have hbase :
      (((Polynomial.X : Polynomial S) • A.map Polynomial.C).map (Polynomial.evalRingHom r)) =
        r • A := by
    ext i j
    change Polynomial.eval r (Polynomial.X * Polynomial.C (A i j)) = r * A i j
    rw [Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C]
  congr 1
  ext i j
  change (Polynomial.evalRingHom r)
      ((expMatrixNilpotent ((Polynomial.X : Polynomial S) • A.map Polynomial.C) N) i j) =
    (expMatrixNilpotent (r • A) N) i j
  unfold expMatrixNilpotent
  rw [Matrix.sum_apply, map_sum, Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro k hk
  change Polynomial.eval r
      ((algebraMap ℚ (Polynomial S) (1 / Nat.factorial k)) *
        (((Polynomial.X : Polynomial S) • A.map Polynomial.C) ^ k) i j) =
    (algebraMap ℚ S (1 / Nat.factorial k)) * ((r • A) ^ k) i j
  rw [Polynomial.eval_mul]
  congr 1
  · change Polynomial.eval r
        (Polynomial.C (algebraMap ℚ S (1 / Nat.factorial k))) =
      algebraMap ℚ S (1 / Nat.factorial k)
    rw [Polynomial.eval_C]
  · have hpow :
        ((((Polynomial.X : Polynomial S) • A.map Polynomial.C) ^ k).map
          (Polynomial.evalRingHom r)) =
          ((((Polynomial.X : Polynomial S) • A.map Polynomial.C).map
            (Polynomial.evalRingHom r)) ^ k) := by
        simpa using
          (Matrix.map_pow ((Polynomial.X : Polynomial S) • A.map Polynomial.C)
            (Polynomial.evalRingHom r) k)
    rw [hbase] at hpow
    exact congrArg (fun M : Matrix (Fin n) (Fin n) S => M i j) hpow

@[simp] theorem detExpPoly_eval_zero {n : ℕ} (A : Matrix (Fin n) (Fin n) S) (N : ℕ) :
    (detExpPoly A N).eval 0 = 1 := by
  rw [detExpPoly_eval]
  rw [zero_smul]
  have hzero : expMatrixNilpotent (0 : Matrix (Fin n) (Fin n) S) N = 1 := by
    induction N with
    | zero =>
        unfold expMatrixNilpotent
        simp
    | succ N ih =>
        unfold expMatrixNilpotent
        rw [Finset.sum_range_succ']
        simpa [ih]
  rw [hzero, Matrix.det_one]

theorem expMatrixNilpotent_map_rat
    {R T : Type*} [CommRing R] [CommRing T] [Algebra ℚ R] [Algebra ℚ T]
    {n : ℕ} (f : R →+* T)
    (hf : ∀ q : ℚ, f (algebraMap ℚ R q) = algebraMap ℚ T q)
    (A : Matrix (Fin n) (Fin n) R) (N : ℕ) :
    (expMatrixNilpotent A N).map f = expMatrixNilpotent (A.map f) N := by
  unfold expMatrixNilpotent
  ext i j
  rw [Matrix.map_apply, Matrix.sum_apply, map_sum, Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro k hk
  change f ((algebraMap ℚ R (1 / Nat.factorial k)) * (A ^ k) i j) =
    (algebraMap ℚ T (1 / Nat.factorial k)) * ((A.map f) ^ k) i j
  rw [map_mul, hf]
  congr 1
  exact congrArg (fun M : Matrix (Fin n) (Fin n) T => M i j) (Matrix.map_pow A f k)

theorem detExpPoly_taylor {n : ℕ}
    (A : Matrix (Fin n) (Fin n) S) (N : ℕ) (hNil : A ^ N = 0) (r : S) :
    Polynomial.taylor r (detExpPoly A N) =
      Polynomial.C ((detExpPoly A N).eval r) * detExpPoly A N := by
  let M : Matrix (Fin n) (Fin n) (Polynomial S) :=
    (Polynomial.X : Polynomial S) • A.map Polynomial.C
  let Cmat : Matrix (Fin n) (Fin n) (Polynomial S) :=
    (Polynomial.C r : Polynomial S) • A.map Polynomial.C
  have hAmapNil : (A.map Polynomial.C) ^ N = 0 := by
    calc
      (A.map Polynomial.C) ^ N = (A ^ N).map Polynomial.C := by
        symm
        simpa using (Matrix.map_pow A Polynomial.C N)
      _ = 0 := by
        simpa using congrArg (fun B : Matrix (Fin n) (Fin n) S => B.map Polynomial.C) hNil
  have hMNil : M ^ N = 0 := by
    dsimp [M]
    rw [smul_pow, hAmapNil, smul_zero]
  have hCmatNil : Cmat ^ N = 0 := by
    dsimp [Cmat]
    rw [smul_pow, hAmapNil, smul_zero]
  have hmapM :
      M.map ((Polynomial.taylorAlgHom r).toRingHom) = Cmat + M := by
    funext i
    funext j
    dsimp [M, Cmat]
    change Polynomial.taylor r (Polynomial.X * Polynomial.C (A i j)) =
      (Polynomial.C r * Polynomial.C (A i j) + Polynomial.X * Polynomial.C (A i j))
    rw [Polynomial.taylor_mul, Polynomial.taylor_X, Polynomial.taylor_C]
    ring
  have hsum :
      Cmat + M =
        ((Polynomial.C r + Polynomial.X : Polynomial S) • A.map Polynomial.C) := by
    ext i j
    dsimp [M, Cmat]
    simp [add_mul]
  have hsumNil :
      (((Polynomial.C r + Polynomial.X : Polynomial S) • A.map Polynomial.C) ^ N) = 0 := by
    rw [smul_pow, hAmapNil, smul_zero]
  have hComm : Commute Cmat M := by
    dsimp [Cmat, M]
    simpa using
      (((Commute.refl (A.map Polynomial.C)).smul_left (Polynomial.C r)).smul_right
        (Polynomial.X : Polynomial S))
  have hconstExp :
      expMatrixNilpotent Cmat N = (expMatrixNilpotent (r • A) N).map Polynomial.C := by
    have hCmat :
        (r • A).map Polynomial.C = Cmat := by
      ext i j
      dsimp [Cmat]
      simp [Algebra.smul_def]
    simpa [hCmat] using
      (expMatrixNilpotent_map_rat (R := S) (T := Polynomial S)
        (f := Polynomial.C) (A := r • A) (N := N)
        (fun q => rfl)).symm
  calc
    Polynomial.taylor r (detExpPoly A N)
        = ((expMatrixNilpotent M N).map ((Polynomial.taylorAlgHom r).toRingHom)).det := by
            change (Polynomial.taylorAlgHom r) (detExpPoly A N) = _
            unfold detExpPoly
            dsimp [M]
            change ((Polynomial.taylorAlgHom r).toRingHom)
                ((expMatrixNilpotent (Polynomial.X • A.map Polynomial.C) N).det) = _
            simpa using
              (RingHom.map_det ((Polynomial.taylorAlgHom r).toRingHom)
                (expMatrixNilpotent (Polynomial.X • A.map Polynomial.C) N))
    _ = (expMatrixNilpotent (Cmat + M) N).det := by
          rw [expMatrixNilpotent_map_rat ((Polynomial.taylorAlgHom r).toRingHom)]
          · rw [hmapM]
          · intro q
            change Polynomial.taylor r (Polynomial.C (algebraMap ℚ S q)) =
              Polynomial.C (algebraMap ℚ S q)
            rw [Polynomial.taylor_C]
    _ = (expMatrixNilpotent (((Polynomial.C r + Polynomial.X : Polynomial S) •
          A.map Polynomial.C)) N).det := by rw [hsum]
    _ = (@IsNilpotent.exp (Matrix (Fin n) (Fin n) (Polynomial S)) _
          (matrixModuleQ (S := Polynomial S))
          (((Polynomial.C r + Polynomial.X : Polynomial S) • A.map Polynomial.C))).det := by
            rw [← expMatrixNilpotent_eq_IsNilpotent_exp
              (((Polynomial.C r + Polynomial.X : Polynomial S) • A.map Polynomial.C)) N hsumNil]
    _ =
        ((@IsNilpotent.exp (Matrix (Fin n) (Fin n) (Polynomial S)) _
            (matrixModuleQ (S := Polynomial S)) Cmat) *
          (@IsNilpotent.exp (Matrix (Fin n) (Fin n) (Polynomial S)) _
            (matrixModuleQ (S := Polynomial S)) M)).det := by
              congr 1
              rw [show ((Polynomial.C r + Polynomial.X : Polynomial S) • A.map Polynomial.C) =
                  Cmat + M by rw [← hsum]]
              exact @IsNilpotent.exp_add_of_commute
                (Matrix (Fin n) (Fin n) (Polynomial S)) _
                (matrixModuleQ (S := Polynomial S)) Cmat M hComm ⟨N, hCmatNil⟩ ⟨N, hMNil⟩
    _ =
        ((@IsNilpotent.exp (Matrix (Fin n) (Fin n) (Polynomial S)) _
            (matrixModuleQ (S := Polynomial S)) Cmat)).det *
        ((@IsNilpotent.exp (Matrix (Fin n) (Fin n) (Polynomial S)) _
            (matrixModuleQ (S := Polynomial S)) M)).det := by
              rw [Matrix.det_mul]
    _ = (Polynomial.C ((detExpPoly A N).eval r)) * detExpPoly A N := by
          rw [← expMatrixNilpotent_eq_IsNilpotent_exp Cmat N hCmatNil]
          rw [← expMatrixNilpotent_eq_IsNilpotent_exp M N hMNil]
          unfold detExpPoly
          rw [hconstExp]
          have hdetC :
              ((expMatrixNilpotent (r • A) N).map Polynomial.C).det =
                Polynomial.C ((expMatrixNilpotent (r • A) N).det) := by
            symm
            simpa using
              (RingHom.map_det (Polynomial.C : S →+* Polynomial S)
                (expMatrixNilpotent (r • A) N))
          rw [hdetC]
          congr 1
          symm
          simpa [detExpPoly, M] using congrArg Polynomial.C (detExpPoly_eval A N r)

theorem detExpPoly_map_C {n : ℕ} (A : Matrix (Fin n) (Fin n) S) (N : ℕ) :
    detExpPoly (S := Polynomial S) (A.map Polynomial.C) N =
      (detExpPoly A N).map Polynomial.C := by
  unfold detExpPoly
  have hmapExp :
      expMatrixNilpotent
          ((Polynomial.X : Polynomial (Polynomial S)) •
            (A.map Polynomial.C).map Polynomial.C) N =
        (expMatrixNilpotent ((Polynomial.X : Polynomial S) • A.map Polynomial.C) N).map
          (Polynomial.mapRingHom (Polynomial.C : S →+* Polynomial S)) := by
    have hmapBase :
        (((Polynomial.X : Polynomial S) • A.map Polynomial.C).map
          (Polynomial.mapRingHom (Polynomial.C : S →+* Polynomial S))) =
          ((Polynomial.X : Polynomial (Polynomial S)) •
            (A.map Polynomial.C).map Polynomial.C) := by
      funext i
      funext j
      change Polynomial.map (Polynomial.C : S →+* Polynomial S)
          (Polynomial.X * Polynomial.C (A i j)) =
        Polynomial.X * Polynomial.C (Polynomial.C (A i j))
      rw [Polynomial.map_mul, Polynomial.map_X, Polynomial.map_C]
    have htmp :=
      (expMatrixNilpotent_map_rat (R := Polynomial S) (T := Polynomial (Polynomial S))
        (f := Polynomial.mapRingHom (Polynomial.C : S →+* Polynomial S))
        (hf := by
          intro q
          rw [show (algebraMap ℚ (Polynomial S) q) =
              Polynomial.C (algebraMap ℚ S q) by rfl]
          change Polynomial.map (Polynomial.C : S →+* Polynomial S)
              (Polynomial.C (algebraMap ℚ S q)) =
            (algebraMap ℚ (Polynomial (Polynomial S))) q
          rw [Polynomial.map_C]
          rfl)
        (A := ((Polynomial.X : Polynomial S) • A.map Polynomial.C)) (N := N)).symm
    rw [hmapBase] at htmp
    exact htmp
  rw [hmapExp]
  symm
  simpa using
    (RingHom.map_det (Polynomial.mapRingHom (Polynomial.C : S →+* Polynomial S))
      (expMatrixNilpotent ((Polynomial.X : Polynomial S) • A.map Polynomial.C) N))

theorem detExpPoly_derivative_eq_coeffOne_mul {n : ℕ}
    (A : Matrix (Fin n) (Fin n) S) (N : ℕ) (hNil : A ^ N = 0) :
    (detExpPoly A N).derivative =
      Polynomial.C ((detExpPoly A N).coeff 1) * detExpPoly A N := by
  let P : Polynomial S := detExpPoly A N
  have hAmapNil : (A.map Polynomial.C) ^ N = 0 := by
    calc
      (A.map Polynomial.C) ^ N = (A ^ N).map Polynomial.C := by
        symm
        simpa using (Matrix.map_pow A Polynomial.C N)
      _ = 0 := by
        simpa using congrArg (fun B : Matrix (Fin n) (Fin n) S => B.map Polynomial.C) hNil
  have ht :
      Polynomial.taylor (Polynomial.X : Polynomial S)
          (detExpPoly (S := Polynomial S) (A.map Polynomial.C) N) =
        Polynomial.C
            ((detExpPoly (S := Polynomial S) (A.map Polynomial.C) N).eval
              (Polynomial.X : Polynomial S)) *
          detExpPoly (S := Polynomial S) (A.map Polynomial.C) N :=
    detExpPoly_taylor (S := Polynomial S) (A := A.map Polynomial.C) N hAmapNil
      (Polynomial.X : Polynomial S)
  rw [detExpPoly_map_C] at ht
  have hEvalX :
      ((detExpPoly A N).map Polynomial.C).eval (Polynomial.X : Polynomial S) =
        detExpPoly A N := by
    simpa [Polynomial.eval₂_eq_eval_map] using
      (Polynomial.eval₂_C_X (p := detExpPoly A N))
  rw [hEvalX] at ht
  have hcoeff :=
    congrArg (fun Q : Polynomial (Polynomial S) => Q.coeff 1) ht
  dsimp [P] at hcoeff ⊢
  have hleft :
      (Polynomial.taylor (Polynomial.X : Polynomial S)
          ((detExpPoly A N).map Polynomial.C)).coeff 1 =
        (detExpPoly A N).derivative := by
    rw [Polynomial.taylor_coeff_one, Polynomial.derivative_map]
    simpa [Polynomial.eval₂_eq_eval_map] using
      (Polynomial.eval₂_C_X (p := (detExpPoly A N).derivative))
  have hright :
      (Polynomial.C (detExpPoly A N) * (detExpPoly A N).map Polynomial.C).coeff 1 =
        Polynomial.C ((detExpPoly A N).coeff 1) * detExpPoly A N := by
    rw [Polynomial.coeff_C_mul]
    simp [mul_comm]
  rw [hleft, hright] at hcoeff
  exact hcoeff

theorem detExpPoly_coeff_recurrence {n : ℕ}
    (A : Matrix (Fin n) (Fin n) S) (N m : ℕ) (hNil : A ^ N = 0) :
    (detExpPoly A N).coeff (m + 1) * (m + 1) =
      (detExpPoly A N).coeff 1 * (detExpPoly A N).coeff m := by
  have hderiv := congrArg (fun Q : Polynomial S => Q.coeff m)
    (detExpPoly_derivative_eq_coeffOne_mul A N hNil)
  simpa [Polynomial.coeff_derivative, Polynomial.coeff_C_mul,
    Nat.cast_succ, mul_comm, mul_left_comm, mul_assoc] using hderiv

theorem detExpPoly_coeff_eq_pow_coeffOne {n : ℕ}
    (A : Matrix (Fin n) (Fin n) S) (N m : ℕ) (hNil : A ^ N = 0) :
    (detExpPoly A N).coeff m =
      algebraMap ℚ S (1 / Nat.factorial m) * ((detExpPoly A N).coeff 1) ^ m := by
  induction m with
  | zero =>
      rw [Polynomial.coeff_zero_eq_eval_zero, detExpPoly_eval_zero]
      simp
  | succ m ih =>
      have hrec := detExpPoly_coeff_recurrence A N m hNil
      have hrec' :
          (detExpPoly A N).coeff (m + 1) * algebraMap ℚ S (m + 1 : ℚ) =
            (detExpPoly A N).coeff 1 * (detExpPoly A N).coeff m := by
        simpa [Nat.cast_add, Nat.cast_one] using hrec
      have hdiv :
          algebraMap ℚ S (1 / (m + 1 : ℚ)) * algebraMap ℚ S (m + 1 : ℚ) = 1 := by
        have hrat : ((1 / (m + 1 : ℚ)) * (m + 1 : ℚ)) = 1 := by
          field_simp
        simpa [map_mul] using congrArg (algebraMap ℚ S) hrat
      calc
        (detExpPoly A N).coeff (m + 1)
            = (algebraMap ℚ S (1 / (m + 1 : ℚ)) * algebraMap ℚ S (m + 1 : ℚ)) *
                (detExpPoly A N).coeff (m + 1) := by rw [hdiv, one_mul]
        _ = algebraMap ℚ S (1 / (m + 1 : ℚ)) *
              ((detExpPoly A N).coeff (m + 1) * algebraMap ℚ S (m + 1 : ℚ)) := by
                simp [mul_assoc, mul_left_comm, mul_comm]
        _ = algebraMap ℚ S (1 / (m + 1 : ℚ)) *
              ((detExpPoly A N).coeff 1 * (detExpPoly A N).coeff m) := by
                rw [hrec']
        _ = algebraMap ℚ S (1 / (m + 1 : ℚ)) *
              ((detExpPoly A N).coeff 1 *
                (algebraMap ℚ S (1 / Nat.factorial m) * ((detExpPoly A N).coeff 1) ^ m)) := by
                rw [ih]
        _ = (algebraMap ℚ S (1 / (m + 1 : ℚ)) *
                algebraMap ℚ S (1 / Nat.factorial m)) *
              ((detExpPoly A N).coeff 1) ^ (m + 1) := by
                rw [pow_succ]
                simp [mul_assoc, mul_left_comm, mul_comm]
        _ = algebraMap ℚ S (1 / Nat.factorial (m + 1)) *
              ((detExpPoly A N).coeff 1) ^ (m + 1) := by
                have hrat :
                    ((1 / (m + 1 : ℚ)) * (1 / Nat.factorial m : ℚ)) =
                      (1 / Nat.factorial (m + 1) : ℚ) := by
                  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
                  field_simp
                rw [← map_mul]
                rw [hrat]

theorem detExpPoly_eval_one_eq_exp_coeffOne {n : ℕ}
    (A : Matrix (Fin n) (Fin n) S) (N : ℕ) (hNil : A ^ N = 0) :
    (detExpPoly A N).eval 1 = IsNilpotent.exp ((detExpPoly A N).coeff 1) := by
  let P : Polynomial S := detExpPoly A N
  let a : S := P.coeff 1
  have hpow : a ^ (P.natDegree + 1) = 0 := by
    have hcoeff :
        P.coeff (P.natDegree + 1) =
          algebraMap ℚ S (1 / Nat.factorial (P.natDegree + 1)) * a ^ (P.natDegree + 1) := by
      simpa [P, a] using detExpPoly_coeff_eq_pow_coeffOne A N (P.natDegree + 1) hNil
    have hzero : P.coeff (P.natDegree + 1) = 0 := by
      exact Polynomial.coeff_eq_zero_of_natDegree_lt (Nat.lt_succ_self _)
    rw [hzero] at hcoeff
    have hunit :
        IsUnit (algebraMap ℚ S (1 / Nat.factorial (P.natDegree + 1) : ℚ)) := by
      have hq_ne : (1 / Nat.factorial (P.natDegree + 1) : ℚ) ≠ 0 := by
        have hfact_ne : (Nat.factorial (P.natDegree + 1) : ℚ) ≠ 0 := by
          exact_mod_cast Nat.factorial_ne_zero (P.natDegree + 1)
        simpa [one_div] using inv_ne_zero hfact_ne
      exact IsUnit.map (algebraMap ℚ S) (isUnit_iff_ne_zero.mpr hq_ne)
    have hcoeff' :
        algebraMap ℚ S (1 / Nat.factorial (P.natDegree + 1) : ℚ) * a ^ (P.natDegree + 1) =
          algebraMap ℚ S (1 / Nat.factorial (P.natDegree + 1) : ℚ) * 0 := by
      simpa using hcoeff.symm
    simpa using hunit.mul_left_cancel hcoeff'
  calc
    P.eval 1 = ∑ i ∈ Finset.range (P.natDegree + 1), P.coeff i * 1 ^ i := by
      simpa using (Polynomial.eval_eq_sum_range (p := P) (1 : S))
    _ = ∑ i ∈ Finset.range (P.natDegree + 1),
          algebraMap ℚ S (1 / Nat.factorial i) * a ^ i := by
          apply Finset.sum_congr rfl
          intro i hi
          simpa [a, P] using detExpPoly_coeff_eq_pow_coeffOne A N i hNil
    _ = IsNilpotent.exp a := by
          symm
          simpa [Algebra.smul_def] using
            (@IsNilpotent.exp_eq_sum S _ _ a (P.natDegree + 1) hpow)

noncomputable def expPolyMatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) S) (N : ℕ) :
    Matrix (Fin n) (Fin n) (Polynomial S) :=
  Matrix.of (fun i j => ∑ k ∈ Finset.range (N + 1),
    Polynomial.C (algebraMap ℚ S (1 / ↑(k.factorial)) * (A ^ k) i j) * Polynomial.X ^ k)

noncomputable def constMatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) S) :
    Matrix (Fin n) (Fin n) (Polynomial S) :=
  Matrix.of (fun i j => Polynomial.C (A i j))

lemma factorial_cancel_alg' (k : ℕ) :
    algebraMap ℚ S (1 / ↑((k + 1).factorial)) * (↑(k + 1) : S) =
      algebraMap ℚ S (1 / ↑(k.factorial)) := by
  rw [← map_natCast (algebraMap ℚ S), ← map_mul]
  congr 1
  rw [Nat.factorial_succ, Nat.cast_mul]
  field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_pos k).ne',
    Nat.cast_ne_zero.mpr (show k + 1 ≠ 0 by omega)]

theorem detExpPoly_eq_det_expPolyMatrix {n : ℕ}
    (A : Matrix (Fin n) (Fin n) S) (N : ℕ) :
    detExpPoly A N = (expPolyMatrix A N).det := by
  unfold detExpPoly expPolyMatrix expMatrixNilpotent
  congr 1
  apply Matrix.ext
  intro i j
  simp only [Matrix.sum_apply, Matrix.of_apply]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Matrix.smul_apply, smul_pow, ← Matrix.map_pow A Polynomial.C k]
  simp only [Matrix.smul_apply, Algebra.smul_def]
  calc
    Polynomial.C (algebraMap ℚ S (1 / ↑k !)) *
        (Polynomial.X ^ k * Polynomial.C ((A ^ k) i j))
      = Polynomial.C (algebraMap ℚ S (1 / ↑k !)) *
          (Polynomial.C ((A ^ k) i j) * Polynomial.X ^ k) := by
            ac_rfl
    _ = (Polynomial.C (algebraMap ℚ S (1 / ↑k !)) *
          Polynomial.C ((A ^ k) i j)) * Polynomial.X ^ k := by
            rw [mul_assoc]
    _ = Polynomial.C ((algebraMap ℚ S (1 / ↑k !)) * (A ^ k) i j) * Polynomial.X ^ k := by
            rw [← Polynomial.C_mul]

/-- Entry-wise derivative of `expPolyMatrix` equals left multiplication by `A`. -/
lemma deriv_expPolyMatrix_entry {n : ℕ} (A : Matrix (Fin n) (Fin n) S) (N : ℕ)
    (hNil : A ^ N = 0) (i j : Fin n) :
    Polynomial.derivative ((expPolyMatrix A N) i j) =
      ∑ l, Polynomial.C (A i l) * (expPolyMatrix A N) l j := by
  unfold expPolyMatrix
  simp only [Matrix.of_apply]
  rw [map_sum, Finset.sum_range_succ']
  simp only [Nat.factorial_zero, Nat.cast_one, div_one, map_one, pow_zero, one_mul,
    mul_one, Polynomial.derivative_C, add_zero]
  conv_lhs =>
    arg 2; ext k
    rw [Polynomial.derivative_C_mul_X_pow, show k + 1 - 1 = k from by omega,
        show Polynomial.C (algebraMap ℚ S (1 / ↑((k + 1).factorial)) * (A ^ (k + 1)) i j * ↑(k + 1)) =
          Polynomial.C (algebraMap ℚ S (1 / ↑(k.factorial)) * (A ^ (k + 1)) i j) from by
          congr 1
          rw [mul_assoc, mul_comm ((A ^ (k + 1)) i j) _, ← mul_assoc, factorial_cancel_alg' k]]
  simp_rw [Finset.mul_sum, ← mul_assoc, ← Polynomial.C_mul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul]
  conv_rhs =>
    arg 2; ext k; arg 1
    rw [show (∑ i_1, Polynomial.C (A i i_1 * (algebraMap ℚ S (1 / ↑(k.factorial)) * (A ^ k) i_1 j))) =
      Polynomial.C (algebraMap ℚ S (1 / ↑(k.factorial)) * (A ^ (k + 1)) i j) from by
      simp_rw [← map_sum]
      congr 1
      rw [_root_.pow_succ', Matrix.mul_apply, Finset.mul_sum]
      congr 1
      ext l
      ring]
  rw [Finset.sum_range_succ]
  have hAN1 : (A ^ (N + 1)) i j = 0 := by
    have h : A ^ (N + 1) = 0 := by rw [_root_.pow_succ', hNil, mul_zero]
    simp [h]
  rw [hAN1, mul_zero, map_zero, zero_mul, add_zero]

/-- Derivative of determinant = sum over columns of det with that column differentiated. -/
lemma derivative_det_eq_sum_updateCol {n : ℕ}
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
  apply Finset.sum_congr rfl
  intro j _
  rw [Matrix.det_apply']
  apply Finset.sum_congr rfl
  intro σ _
  rw [← Finset.mul_prod_erase Finset.univ (fun i => (M.updateCol j
    (fun k => Polynomial.derivative (M k j))) (σ i) i) (Finset.mem_univ j)]
  simp only [Matrix.updateCol_self]
  congr 1
  rw [mul_comm]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  rw [Matrix.updateCol_ne (Finset.mem_erase.mp hi).1]

/-- Sum of dets with one column replaced by `(A * M)` equals `tr(A) * det(M)`. -/
lemma sum_det_updateCol_mul_eq_trace_mul_det'
    {m : Type*} [DecidableEq m] [Fintype m] {R : Type*} [CommRing R]
    (A M : Matrix m m R) :
    ∑ j, (M.updateCol j (fun i => (A * M) i j)).det = A.trace * M.det := by
  simp_rw [← Matrix.cramer_apply, Matrix.cramer_eq_adjugate_mulVec, Matrix.mulVec,
    dotProduct]
  rw [Finset.sum_comm]
  simp_rw [mul_comm (M.adjugate _ _)]
  change ∑ k, ∑ j, (A * M) k j * M.adjugate j k = _
  rw [show (∑ k, ∑ j, (A * M) k j * M.adjugate j k) =
    ((A * M) * M.adjugate).trace from by simp [Matrix.trace, Matrix.mul_apply]]
  rw [Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.mul_smul, Matrix.trace_smul,
      Matrix.mul_one, smul_eq_mul, mul_comm]

theorem detExpPoly_derivative_eq_trace_mul {n : ℕ}
    (A : Matrix (Fin n) (Fin n) S) (N : ℕ) (hNil : A ^ N = 0) :
    (detExpPoly A N).derivative = Polynomial.C A.trace * detExpPoly A N := by
  rw [detExpPoly_eq_det_expPolyMatrix]
  set M := expPolyMatrix A N with hM_def
  rw [derivative_det_eq_sum_updateCol M]
  have hderiv_eq : ∀ j₀ : Fin n,
      (M.updateCol j₀ (fun i => Polynomial.derivative (M i j₀))).det =
        (M.updateCol j₀ (fun i => (constMatrix A * M) i j₀)).det := by
    intro j₀
    congr 1
    ext i j'
    by_cases hj : j' = j₀
    · subst hj
      simp only [Matrix.updateCol_self]
      rw [deriv_expPolyMatrix_entry A N hNil i j', hM_def]
      unfold constMatrix
      rw [Matrix.mul_apply]
      simp [Matrix.of_apply]
    · simp [Matrix.updateCol_ne hj]
  simp_rw [hderiv_eq]
  rw [sum_det_updateCol_mul_eq_trace_mul_det' (constMatrix A) M]
  congr 1
  unfold constMatrix Matrix.trace
  simp [Matrix.of_apply, Matrix.diag, map_sum]

theorem detExpPoly_coeff_one_eq_trace {n : ℕ}
    (A : Matrix (Fin n) (Fin n) S) (N : ℕ) (hNil : A ^ N = 0) :
    (detExpPoly A N).coeff 1 = A.trace := by
  have hcoeff :=
    congrArg (fun Q : Polynomial S => Polynomial.eval 0 Q)
      (detExpPoly_derivative_eq_trace_mul A N hNil)
  have hcoeff0 : Polynomial.eval 0 (Polynomial.derivative (detExpPoly A N)) = A.trace := by
    simpa [Polynomial.eval_zero, detExpPoly_eval_zero] using hcoeff
  have hcoeff1 : (Polynomial.derivative (detExpPoly A N)).coeff 0 = A.trace := by
    simpa [Polynomial.coeff_zero_eq_eval_zero] using hcoeff0
  simpa [Polynomial.coeff_derivative] using hcoeff1

/-- Scratch proof for Jacobi's nilpotent determinant formula.

This now closes the theorem by a non-circular determinant ODE argument in the scratch file.
It is kept here as a test proof before any library-level transplant. -/
theorem det_expMatrix_eq_exp_trace_test {n : ℕ}
    (A : Matrix (Fin n) (Fin n) S) (N : ℕ) (hNil : A ^ N = 0) :
    (expMatrixNilpotent A N).det = IsNilpotent.exp A.trace := by
  calc
    (expMatrixNilpotent A N).det = (detExpPoly A N).eval 1 := by
      simpa using (detExpPoly_eval A N (1 : S)).symm
    _ = IsNilpotent.exp ((detExpPoly A N).coeff 1) := by
      exact detExpPoly_eval_one_eq_exp_coeffOne A N hNil
    _ = IsNilpotent.exp A.trace := by
      congr 1
      exact detExpPoly_coeff_one_eq_trace A N hNil

end DetExpTraceScratch
