import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Algebra.Basic
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.Data.ZMod.Basic

/-!
# Helper Lemmas for Graded Rings

This file contains foundational lemmas for ℤ/2-graded rings and algebras
that are needed for superalgebra theory.

## Main results

* `neg_one_zsmul_eq_neg` - (-1) • x = -x in a module
* `zsmul_neg_one_sq` - ((-1)^n)² = 1
* Lemmas for handling graded ring structures

These lemmas help bridge type class instances and simplify proofs involving
the Koszul sign convention.
-/

namespace Supermanifolds.Helpers

/-!
## Integer scalar multiplication lemmas
-/

/-- (-1 : ℤ) • x = -x in any AddCommGroup with ℤ-module structure -/
theorem neg_one_zsmul_eq_neg {M : Type*} [AddCommGroup M] (x : M) :
    (-1 : ℤ) • x = -x := by
  simp

/-- 1 • x = x in any AddCommGroup with ℤ-module structure -/
theorem one_zsmul_eq_self {M : Type*} [AddCommGroup M] (x : M) :
    (1 : ℤ) • x = x := one_smul ℤ x

/-- (-1)² = 1 as integers -/
theorem neg_one_sq : (-1 : ℤ) * (-1 : ℤ) = 1 := by ring

/-- (-1)^(2n) = 1 -/
theorem neg_one_pow_even (n : ℕ) : (-1 : ℤ) ^ (2 * n) = 1 := by
  have : (-1 : ℤ) ^ 2 = 1 := by norm_num
  rw [pow_mul, this]; exact _root_.one_pow n

/-- (-1)^(2n+1) = -1 -/
theorem neg_one_pow_odd (n : ℕ) : (-1 : ℤ) ^ (2 * n + 1) = -1 := by
  rw [pow_succ, neg_one_pow_even]
  ring

/-!
## Grading compatibility lemmas
-/

/-- In a ring, integer scalar multiplication equals multiplication by the integer -/
theorem ring_zsmul_eq_mul {R : Type*} [Ring R] (n : ℤ) (x : R) :
    n • x = (n : R) * x := by
  rw [← smul_one_mul, Int.smul_one_eq_cast]

/-- x = -x implies 2x = 0 -/
theorem eq_neg_self_iff {M : Type*} [AddCommGroup M] (x : M) :
    x = -x ↔ x + x = 0 := by
  constructor
  · intro h
    calc x + x = x + (-x) := by rw [← h]
    _ = 0 := add_neg_cancel x
  · intro h
    have hxx : x + x = 0 := h
    have : -x = -x + (x + x) := by rw [hxx]; simp
    rw [← add_assoc, add_comm (-x) x, add_neg_cancel, zero_add] at this
    exact this.symm

/-- In characteristic zero with no zero divisors, x = -x implies x = 0 -/
theorem eq_neg_self_implies_zero {R : Type*} [Ring R] [NoZeroDivisors R] [CharZero R]
    (x : R) (h : x = -x) : x = 0 := by
  have h2 : x + x = 0 := eq_neg_self_iff x |>.mp h
  have h2x : (2 : R) * x = 0 := by
    have : (2 : R) * x = x + x := two_mul x
    rw [this, h2]
  rcases mul_eq_zero.mp h2x with h2z | hx
  · have : (2 : R) ≠ 0 := two_ne_zero
    contradiction
  · exact hx

/-!
## ZMod 2 lemmas for parity
-/

/-- The only elements of ZMod 2 are 0 and 1 -/
theorem zmod2_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x
  · left; rfl
  · right; rfl

/-- x + x = 0 in ZMod 2 -/
theorem zmod2_add_self (x : ZMod 2) : x + x = 0 := by
  fin_cases x <;> native_decide

/-- (-1)^n depends only on n mod 2 -/
theorem neg_one_pow_mod_two (n : ℕ) :
    (-1 : ℤ) ^ n = if n % 2 = 0 then 1 else -1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    simp only [ih]
    split_ifs with h1 h2 h2
    · -- n % 2 = 0, (n+1) % 2 = 0 impossible
      omega
    · -- n % 2 = 0, (n+1) % 2 ≠ 0
      ring
    · -- n % 2 ≠ 0, (n+1) % 2 = 0
      ring
    · -- n % 2 ≠ 0, (n+1) % 2 ≠ 0 impossible
      omega

/-!
## Submodule intersection lemmas
-/

/-- If v ∈ M₀ and v ∈ M₁ where M₀ ∩ M₁ = {0}, then v = 0 -/
theorem mem_both_submodules_eq_zero {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (M₀ M₁ : Submodule R M)
    (h_disjoint : M₀ ⊓ M₁ = ⊥)
    (v : M) (hv₀ : v ∈ M₀) (hv₁ : v ∈ M₁) : v = 0 := by
  have hv : v ∈ M₀ ⊓ M₁ := Submodule.mem_inf.mpr ⟨hv₀, hv₁⟩
  rw [h_disjoint] at hv
  simp only [Submodule.mem_bot] at hv
  exact hv

end Supermanifolds.Helpers
