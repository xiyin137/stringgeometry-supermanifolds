import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.Module.Rat
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.RingTheory.PowerSeries.WellKnown
import StringGeometry.Supermanifolds.FPS.LogExp

open Finset Nat PowerSeries

namespace ExpNegLogGeomScratch

open FPSLogExp

variable {R : Type*} [CommRing R] [Algebra ℚ R]

local instance : IsAddTorsionFree R := IsAddTorsionFree.of_module_rat (M := R)

/-- The formal power series `log(1 / (1 - X)) = ∑_{n≥1} X^n / n`. -/
noncomputable def logInvOneSubSeries : R⟦X⟧ :=
  PowerSeries.mk fun n =>
    if n = 0 then 0 else algebraMap ℚ R ((1 : ℚ) / n)

@[simp] theorem coeff_logInvOneSubSeries_zero :
    coeff 0 (logInvOneSubSeries (R := R)) = 0 := by
  simp [logInvOneSubSeries]

@[simp] theorem coeff_logInvOneSubSeries_succ (n : ℕ) :
    coeff (n + 1) (logInvOneSubSeries (R := R)) =
      algebraMap ℚ R ((1 : ℚ) / (n + 1)) := by
  simp [logInvOneSubSeries]

@[simp] theorem constantCoeff_logInvOneSubSeries :
    constantCoeff (logInvOneSubSeries (R := R)) = 0 := by
  simp [logInvOneSubSeries]

theorem derivative_logInvOneSubSeries :
    d⁄dX R (logInvOneSubSeries (R := R)) = (PowerSeries.mk 1 : R⟦X⟧) := by
  ext n
  rw [PowerSeries.coeff_derivative, coeff_logInvOneSubSeries_succ, PowerSeries.coeff_mk]
  have hrat : ((1 : ℚ) / (n + 1 : ℚ)) * (n + 1 : ℚ) = 1 := by
    field_simp
  have hmap := congrArg (algebraMap ℚ R) hrat
  simpa [RingHom.map_mul] using hmap

theorem constantCoeff_subst_C_eq_sum_of_nilpotent
    (f : R⟦X⟧) (a : R) (M : ℕ) (ha : a ^ (M + 1) = 0) :
    constantCoeff (f.subst (C a)) =
      ∑ k ∈ Finset.range (M + 1), coeff k f * a ^ k := by
  have hsubst : PowerSeries.HasSubst (C a : R⟦X⟧) := by
    change IsNilpotent (constantCoeff (C a : R⟦X⟧))
    simpa using (show IsNilpotent a from ⟨M + 1, ha⟩)
  have h0 :
      MvPowerSeries.constantCoeff (f.subst (C a)) =
        ∑ᶠ d : ℕ, coeff d f * MvPowerSeries.constantCoeff ((C a : R⟦X⟧) ^ d) := by
    simpa using (PowerSeries.constantCoeff_subst (a := C a) (ha := hsubst) (f := f))
  have h1 :
      (∑ᶠ d : ℕ, coeff d f * MvPowerSeries.constantCoeff ((C a : R⟦X⟧) ^ d)) =
        ∑ᶠ d : ℕ, coeff d f * a ^ d := by
    apply finsum_congr
    intro d
    have hc : MvPowerSeries.constantCoeff ((C a : R⟦X⟧) ^ d) = a ^ d := by
      change PowerSeries.constantCoeff ((C a : R⟦X⟧) ^ d) = a ^ d
      rw [RingHom.map_pow, PowerSeries.constantCoeff_C]
    rw [hc]
  have h2 :
      (∑ᶠ d : ℕ, coeff d f * a ^ d) =
        ∑ k ∈ Finset.range (M + 1), coeff k f * a ^ k := by
    rw [finsum_eq_sum_of_support_subset (s := Finset.range (M + 1))]
    · intro d hd
      simp only [Function.mem_support, Finset.mem_coe, Finset.mem_range] at hd ⊢
      by_contra hd'
      have hge : M + 1 ≤ d := by omega
      have hpow : a ^ d = 0 := pow_eq_zero_of_le hge ha
      rw [hpow, mul_zero] at hd
      exact hd rfl
  exact h0.trans (h1.trans h2)

theorem constantCoeff_exp_subst_eq_expNilpotent_of_nilpotent
    (b : R⟦X⟧) (hb : PowerSeries.HasSubst b) (M : ℕ)
    (hM : (constantCoeff b) ^ (M + 1) = 0) :
    constantCoeff ((PowerSeries.exp R).subst b) =
      expNilpotent (constantCoeff b) M := by
  have h0 :
      MvPowerSeries.constantCoeff ((PowerSeries.exp R).subst b) =
        ∑ᶠ d : ℕ, coeff d (PowerSeries.exp R) * MvPowerSeries.constantCoeff (b ^ d) := by
    simpa using (PowerSeries.constantCoeff_subst (a := b) (ha := hb) (f := PowerSeries.exp R))
  have h1 :
      (∑ᶠ d : ℕ, coeff d (PowerSeries.exp R) * MvPowerSeries.constantCoeff (b ^ d)) =
        ∑ᶠ d : ℕ, coeff d (PowerSeries.exp R) * (constantCoeff b) ^ d := by
    apply finsum_congr
    intro d
    have hc : MvPowerSeries.constantCoeff (b ^ d) = (constantCoeff b) ^ d := by
      change PowerSeries.constantCoeff (b ^ d) = (constantCoeff b) ^ d
      rw [RingHom.map_pow]
    rw [hc]
  have h2 :
      (∑ᶠ d : ℕ, coeff d (PowerSeries.exp R) * (constantCoeff b) ^ d) =
        ∑ k ∈ Finset.range (M + 1), coeff k (PowerSeries.exp R) * (constantCoeff b) ^ k := by
    rw [finsum_eq_sum_of_support_subset (s := Finset.range (M + 1))]
    · intro d hd
      simp only [Function.mem_support, Finset.mem_coe, Finset.mem_range] at hd ⊢
      by_contra hd'
      have hge : M + 1 ≤ d := by omega
      have hpow : (constantCoeff b) ^ d = 0 := pow_eq_zero_of_le hge hM
      rw [hpow, mul_zero] at hd
      exact hd rfl
  have h3 :
      (∑ k ∈ Finset.range (M + 1), coeff k (PowerSeries.exp R) * (constantCoeff b) ^ k) =
        expNilpotent (constantCoeff b) M := by
    unfold expNilpotent
    apply Finset.sum_congr rfl
    intro k hk
    rw [PowerSeries.coeff_exp]
    rw [show ((1 : ℚ) / (k.factorial : ℚ)) = (k.factorial : ℚ)⁻¹ by simp [one_div]]
    rw [Algebra.smul_def]
  exact h0.trans (h1.trans (h2.trans h3))

noncomputable def expLogInvOneSubSeries : R⟦X⟧ :=
  (PowerSeries.exp R).subst (logInvOneSubSeries (R := R))

theorem expLogInvOneSub_mul_one_sub_eq_one :
    expLogInvOneSubSeries (R := R) * (1 - X) = 1 := by
  let g : R⟦X⟧ := logInvOneSubSeries (R := R)
  let F : R⟦X⟧ := (PowerSeries.exp R).subst g
  have hg_subst : PowerSeries.HasSubst g := by
    apply PowerSeries.HasSubst.of_constantCoeff_zero'
    dsimp [g]
    simp [logInvOneSubSeries]
  have hderiv_F : d⁄dX R F = F * (PowerSeries.mk 1 : R⟦X⟧) := by
    dsimp [F]
    rw [PowerSeries.derivative_subst (A := R) hg_subst, PowerSeries.derivative_exp]
    rw [derivative_logInvOneSubSeries]
  have hconst_F : constantCoeff F = 1 := by
    dsimp [F]
    have hzero : constantCoeff ((PowerSeries.exp R - 1).subst g) = 0 := by
      apply PowerSeries.constantCoeff_subst_eq_zero
      · dsimp [g]
        exact constantCoeff_logInvOneSubSeries (R := R)
      · simp
    have hexp : (1 : R⟦X⟧) + (PowerSeries.exp R - 1) = PowerSeries.exp R := by
      abel
    have hone_const : constantCoeff (((1 : R⟦X⟧)).subst g) = 1 := by
      rw [show (1 : R⟦X⟧) = ((1 : Polynomial R) : R⟦X⟧) by simp]
      rw [PowerSeries.subst_coe hg_subst]
      have h : constantCoeff ((Polynomial.aeval g) (1 : Polynomial R)) = 1 := by simp
      exact h
    rw [← hexp, PowerSeries.subst_add hg_subst, map_add, hone_const, hzero]
    simp
  have hderiv_one_sub : d⁄dX R ((1 : R⟦X⟧) - X) = -1 := by
    ext n
    cases n with
    | zero =>
        rw [PowerSeries.coeff_derivative, PowerSeries.coeff_zero_eq_constantCoeff_apply]
        rw [show (-1 : R⟦X⟧) = C (-1 : R) by simp, PowerSeries.constantCoeff_C]
        simp [PowerSeries.coeff_X]
    | succ n =>
        rw [PowerSeries.coeff_derivative]
        rw [show (-1 : R⟦X⟧) = C (-1 : R) by simp, PowerSeries.coeff_C]
        simp [PowerSeries.coeff_X]
  have hderiv_prod : d⁄dX R (F * (1 - X)) = 0 := by
    calc
      d⁄dX R (F * (1 - X))
          = F * (d⁄dX R ((1 : R⟦X⟧) - X)) + ((1 : R⟦X⟧) - X) * (d⁄dX R F) := by
            simpa [PowerSeries.derivative, smul_eq_mul] using
              (PowerSeries.derivativeFun_mul (f := F) (g := ((1 : R⟦X⟧) - X)))
      _ = F * (d⁄dX R ((1 : R⟦X⟧) - X)) + ((1 : R⟦X⟧) - X) * (d⁄dX R F) := by
            rfl
      _ = F * (-1) + ((1 : R⟦X⟧) - X) * (F * (PowerSeries.mk 1 : R⟦X⟧)) := by
            rw [hderiv_one_sub, hderiv_F]
      _ = F * (-1) + F * ((PowerSeries.mk 1 : R⟦X⟧) * ((1 : R⟦X⟧) - X)) := by
            let A : R⟦X⟧ := (1 : R⟦X⟧) - X
            have hmul1 : A * (F * (PowerSeries.mk 1 : R⟦X⟧)) =
                (A * F) * (PowerSeries.mk 1 : R⟦X⟧) := by
              exact (mul_assoc _ _ _).symm
            have hmul2 : (A * F) * (PowerSeries.mk 1 : R⟦X⟧) =
                (F * A) * (PowerSeries.mk 1 : R⟦X⟧) := by
              exact congrArg (fun t : R⟦X⟧ => t * (PowerSeries.mk 1 : R⟦X⟧)) (mul_comm A F)
            have hmul3 : (F * A) * (PowerSeries.mk 1 : R⟦X⟧) =
                F * (A * (PowerSeries.mk 1 : R⟦X⟧)) := by
              exact mul_assoc _ _ _
            have hmul4 : F * (A * (PowerSeries.mk 1 : R⟦X⟧)) =
                F * ((PowerSeries.mk 1 : R⟦X⟧) * A) := by
              exact congrArg (fun t : R⟦X⟧ => F * t) (mul_comm A (PowerSeries.mk 1 : R⟦X⟧))
            have hmul : A * (F * (PowerSeries.mk 1 : R⟦X⟧)) =
                F * ((PowerSeries.mk 1 : R⟦X⟧) * A) := by
              exact hmul1.trans (hmul2.trans (hmul3.trans hmul4))
            dsimp [A] at hmul
            exact congrArg (fun t : R⟦X⟧ => F * (-1) + t) hmul
      _ = F * (-1) + F * 1 := by
            rw [PowerSeries.mk_one_mul_one_sub_eq_one]
      _ = 0 := by
            ext n
            rw [show coeff n (F * (-1 : R⟦X⟧) + F * (1 : R⟦X⟧)) =
                coeff n (F * (-1 : R⟦X⟧)) + coeff n (F * (1 : R⟦X⟧)) by
                  exact (PowerSeries.coeff n).map_add _ _]
            rw [show coeff n (0 : R⟦X⟧) = 0 by exact (PowerSeries.coeff n).map_zero]
            rw [show F * (-1 : R⟦X⟧) = C (-1 : R) * F by
              rw [show (-1 : R⟦X⟧) = C (-1 : R) by simp]
              exact mul_comm _ _]
            rw [show F * (1 : R⟦X⟧) = C (1 : R) * F by
              rw [show (1 : R⟦X⟧) = C (1 : R) by simp]
              exact mul_comm _ _]
            rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul]
            simp
  have hconst_prod : constantCoeff (F * (1 - X)) = constantCoeff (1 : R⟦X⟧) := by
    rw [map_mul]
    simp [hconst_F]
  have hmain : F * (1 - X) = 1 := by
    have hderiv_prod' : d⁄dX R (F * (1 - X)) = d⁄dX R (1 : R⟦X⟧) := by
      calc
        d⁄dX R (F * (1 - X)) = 0 := hderiv_prod
        _ = d⁄dX R (1 : R⟦X⟧) := by
              symm
              simpa using (PowerSeries.derivative_C (R := R) (r := (1 : R)))
    exact PowerSeries.derivative.ext hderiv_prod' hconst_prod
  simpa [F, expLogInvOneSubSeries] using hmain

theorem expNilpotent_neg_log_eq_geom_test
    (x : R) (N : ℕ) (_hN : 1 ≤ N) (hx : x ^ (N + 1) = 0) :
    expNilpotent (-logOneSubNilpotent x N) (N + 1) =
      ∑ k ∈ range (N + 1), x ^ k := by
  let L : R := -logOneSubNilpotent x N
  have hg_subst : PowerSeries.HasSubst (logInvOneSubSeries (R := R)) := by
    apply PowerSeries.HasSubst.of_constantCoeff_zero'
    simp [logInvOneSubSeries]
  have hx_subst : PowerSeries.HasSubst (C x : R⟦X⟧) := by
    change IsNilpotent (constantCoeff (C x : R⟦X⟧))
    simpa using (show IsNilpotent x from ⟨N + 1, hx⟩)
  have hLconst :
      constantCoeff ((logInvOneSubSeries (R := R)).subst (C x)) = L := by
    rw [constantCoeff_subst_C_eq_sum_of_nilpotent
      (f := logInvOneSubSeries (R := R)) (a := x) (M := N) hx]
    rw [Finset.sum_range_succ']
    simp [L, coeff_logInvOneSubSeries_succ]
    simpa [L] using (neg_logOneSubNilpotent_eq (R := R) x N).symm
  have hLnil_base : (logOneSubNilpotent x N) ^ (N + 1) = 0 :=
    logOneSubNilpotent_nilpotent (R := R) x N hx
  have hLnil : L ^ (N + 2) = 0 := by
    dsimp [L]
    rw [pow_succ, neg_eq_neg_one_mul, mul_pow, hLnil_base]
    simp
  have hLog_subst : PowerSeries.HasSubst ((logInvOneSubSeries (R := R)).subst (C x)) := by
    change IsNilpotent (constantCoeff ((logInvOneSubSeries (R := R)).subst (C x)))
    rw [hLconst]
    exact ⟨N + 2, hLnil⟩
  have hExp_const :
      constantCoeff (((PowerSeries.exp R).subst ((logInvOneSubSeries (R := R)).subst (C x)))) =
        expNilpotent L (N + 1) := by
    have htmp :=
      constantCoeff_exp_subst_eq_expNilpotent_of_nilpotent
        (b := (logInvOneSubSeries (R := R)).subst (C x)) (hb := hLog_subst) (M := N + 1) (by
          rw [hLconst]
          exact hLnil)
    rw [hLconst] at htmp
    exact htmp
  have hOneSub_const :
      constantCoeff (((1 - X : R⟦X⟧)).subst (C x)) = 1 - x := by
    rw [show (1 - X : R⟦X⟧) = ((1 - Polynomial.X : Polynomial R) : R⟦X⟧) by simp]
    rw [PowerSeries.subst_coe hx_subst]
    have hpoly : (Polynomial.aeval (C x)) (1 - Polynomial.X : Polynomial R) = (1 : R⟦X⟧) - C x := by
      have h :=
        RingHom.map_sub ((Polynomial.aeval (C x)).toRingHom) (1 : Polynomial R) Polynomial.X
      change (Polynomial.aeval (C x)) (1 - Polynomial.X : Polynomial R) =
        (Polynomial.aeval (C x)) (1 : Polynomial R) - (Polynomial.aeval (C x)) Polynomial.X at h
      rw [Polynomial.aeval_one, Polynomial.aeval_X] at h
      exact h
    refine hpoly ▸ ?_
    rw [map_sub, PowerSeries.constantCoeff_one, PowerSeries.constantCoeff_C]
  have hScalar :
      expNilpotent L (N + 1) * (1 - x) = 1 := by
    have hone_sub_const : constantCoeff (((1 : R⟦X⟧)).subst (C x)) = 1 := by
      rw [show (1 : R⟦X⟧) = ((1 : Polynomial R) : R⟦X⟧) by simp]
      rw [PowerSeries.subst_coe hx_subst]
      rw [Polynomial.aeval_one, PowerSeries.constantCoeff_one]
    have hps_sub :
        (((expLogInvOneSubSeries (R := R)) * (1 - X)).subst (C x)) = ((1 : R⟦X⟧).subst (C x)) := by
      exact congrArg (PowerSeries.subst (C x))
        (expLogInvOneSub_mul_one_sub_eq_one (R := R))
    have hconst_sub := congrArg PowerSeries.constantCoeff hps_sub
    rw [PowerSeries.subst_mul hx_subst, map_mul] at hconst_sub
    rw [expLogInvOneSubSeries, PowerSeries.subst_comp_subst_apply hg_subst hx_subst] at hconst_sub
    rw [hExp_const, hOneSub_const, hone_sub_const] at hconst_sub
    simpa [L] using hconst_sub
  have hgeom : (∑ k ∈ range (N + 1), x ^ k) * (1 - x) = 1 := by
    rw [geom_sum_mul_neg, hx, sub_zero]
  calc
    expNilpotent L (N + 1) = expNilpotent L (N + 1) * 1 := by rw [mul_one]
    _ = expNilpotent L (N + 1) * ((∑ k ∈ range (N + 1), x ^ k) * (1 - x)) := by rw [hgeom]
    _ = (expNilpotent L (N + 1) * (∑ k ∈ range (N + 1), x ^ k)) * (1 - x) := by ring
    _ = (expNilpotent L (N + 1) * (1 - x)) * (∑ k ∈ range (N + 1), x ^ k) := by ring
    _ = 1 * (∑ k ∈ range (N + 1), x ^ k) := by rw [hScalar]
    _ = ∑ k ∈ range (N + 1), x ^ k := by rw [one_mul]

end ExpNegLogGeomScratch
