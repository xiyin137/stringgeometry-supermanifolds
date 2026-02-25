/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license.
-/
import StringGeometry.Supermanifolds.Helpers.FiniteGrassmann
import StringGeometry.Supermanifolds.Helpers.NilpotentTaylor
import StringGeometry.Supermanifolds.Helpers.GrassmannSmooth

/-!
# Nilpotent Inverse in Grassmann Algebra

Constructs the inverse of `1 + ε` where `ε` is nilpotent in `FiniteGrassmannCarrier q`,
using the geometric series `(1 + ε)⁻¹ = Σ_{n=0}^{q} (-ε)^n`.

## Main Definitions

* `grassmannGeomInverse` - explicit geometric series inverse for 1 + ε
* `SuperDomainFunction.nilpotentInverse` - SuperDomainFunction-level inverse

## Main Theorems

* `grassmannGeomInverse_mul` - (Σ (-ε)^n) · (1 + ε) = 1
* `SuperDomainFunction.nilpotentInverse_mul` - S · S⁻¹ = 1 pointwise
-/

noncomputable section

namespace Supermanifolds

open Supermanifolds.Helpers FiniteGrassmannCarrier

/-! ## Nilpotency of Elements with No Constant Term -/

/-- Elements with no constant term vanish when raised to the (q+1)-th power. -/
theorem hasNoConstant_pow_vanishes {q : ℕ} (ε : FiniteGrassmannCarrier q)
    (hε : hasNoConstant ε) : ε ^ (q + 1) = 0 := by
  funext K
  have hK : K.card ≤ q := by
    have := Finset.card_le_card (Finset.subset_univ K)
    simp only [Finset.card_fin] at this; exact this
  suffices h : ∀ (n : ℕ) (K : Finset (Fin q)), K.card < n → (ε ^ n) K = 0 by
    apply h; omega
  intro n
  induction n with
  | zero => intro K' hK'; omega
  | succ m ih =>
    intro K' hK'
    rw [pow_succ]
    change (Finset.univ.sum fun I => Finset.univ.sum fun J =>
      if I ∪ J = K' ∧ I ∩ J = ∅ then reorderSign I J * (ε ^ m) I * ε J else 0) = 0
    apply Finset.sum_eq_zero; intro I _; apply Finset.sum_eq_zero; intro J _
    split_ifs with hIJ
    · obtain ⟨hK_eq, hDisj⟩ := hIJ
      have hCard : K'.card = I.card + J.card := by
        rw [← hK_eq]
        exact Finset.card_union_of_disjoint (Finset.disjoint_iff_inter_eq_empty.mpr hDisj)
      by_cases hJ : J = ∅
      · rw [hJ, hε]; ring
      · have hJne : J.Nonempty := Finset.nonempty_iff_ne_empty.mpr hJ
        have hJcard := hJne.card_pos
        rw [ih I (by omega)]; ring
    · rfl

/-- Negation preserves hasNoConstant. -/
theorem neg_hasNoConstant {q : ℕ} {ε : FiniteGrassmannCarrier q}
    (hε : hasNoConstant ε) : hasNoConstant (-ε) := by
  show (-ε) ∅ = 0; show -(ε ∅) = 0; rw [hε, neg_zero]

/-- Elements with no constant term are nilpotent (in Mathlib's sense). -/
theorem hasNoConstant_isNilpotent {q : ℕ} (ε : FiniteGrassmannCarrier q)
    (hε : hasNoConstant ε) : IsNilpotent ε :=
  ⟨q + 1, hasNoConstant_pow_vanishes ε hε⟩

/-- The soul of any Grassmann element is nilpotent (Mathlib IsNilpotent version). -/
theorem grassmannSoul_isNilpotent {q : ℕ} (x : FiniteGrassmannCarrier q) :
    IsNilpotent (grassmannSoul x) :=
  hasNoConstant_isNilpotent _ (grassmannSoul_hasNoConstant x)

/-! ## Geometric Series Inverse -/

/-- Explicit geometric series inverse for `1 + ε` where `ε` is nilpotent.
    (1 + ε)⁻¹ = Σ_{n=0}^{q} (-ε)^n = 1 - ε + ε² - ε³ + ... + (-1)^q ε^q -/
def grassmannGeomInverse {q : ℕ} (ε : FiniteGrassmannCarrier q) : FiniteGrassmannCarrier q :=
  (Finset.range (q + 1)).sum fun n => (-ε) ^ n

/-- The geometric series inverse is a left inverse: (Σ (-ε)^n) · (1 + ε) = 1.

    Uses Mathlib's `geom_sum_mul_neg`: Σ x^i * (1 - x) = 1 - x^{N+1},
    applied with x = -ε. -/
theorem grassmannGeomInverse_mul {q : ℕ} (ε : FiniteGrassmannCarrier q)
    (hε : hasNoConstant ε) :
    grassmannGeomInverse ε * (1 + ε) = 1 := by
  unfold grassmannGeomInverse
  have key := geom_sum_mul_neg (-ε) (q + 1)
  -- key : (Σ (-ε)^i) * (1 - (-ε)) = 1 - (-ε)^{q+1}
  -- 1 - (-ε) = 1 + ε
  rw [sub_neg_eq_add] at key
  -- (-ε)^{q+1} = 0
  have hpow : (-ε) ^ (q + 1) = 0 := hasNoConstant_pow_vanishes (-ε) (neg_hasNoConstant hε)
  rw [key, hpow, sub_zero]

/-- The geometric series inverse is a right inverse: (1 + ε) · (Σ (-ε)^n) = 1.

    Uses Mathlib's `mul_neg_geom_sum`: (1 - x) * Σ x^i = 1 - x^{N+1},
    applied with x = -ε. -/
theorem grassmannGeomInverse_mul_right {q : ℕ} (ε : FiniteGrassmannCarrier q)
    (hε : hasNoConstant ε) :
    (1 + ε) * grassmannGeomInverse ε = 1 := by
  unfold grassmannGeomInverse
  have key := mul_neg_geom_sum (-ε) (q + 1)
  rw [sub_neg_eq_add] at key
  have hpow : (-ε) ^ (q + 1) = 0 := hasNoConstant_pow_vanishes (-ε) (neg_hasNoConstant hε)
  rw [key, hpow, sub_zero]

/-- 1 + ε is a unit when ε has no constant term. -/
theorem isUnit_one_add_hasNoConstant {q : ℕ} (ε : FiniteGrassmannCarrier q)
    (hε : hasNoConstant ε) : IsUnit (1 + ε) :=
  (hasNoConstant_isNilpotent ε hε).isUnit_one_add

/-- Scalar multiplication preserves `hasNoConstant`. -/
theorem smul_hasNoConstant {q : ℕ} (c : ℝ) {ε : FiniteGrassmannCarrier q}
    (hε : hasNoConstant ε) : hasNoConstant (c • ε) := by
  show (c • ε) ∅ = 0; show c * ε ∅ = 0; rw [hε, mul_zero]

/-! ## SuperDomainFunction-level Helpers -/

/-- The nilpotent part ε(x) for a given point, as a FiniteGrassmannCarrier. -/
def nilpotentPartAt {p q : ℕ} (S : SuperDomainFunction p q) (x : Fin p → ℝ) :
    FiniteGrassmannCarrier q :=
  fun I => if I = ∅ then (0 : ℝ) else (S.coefficients I).toFun x

/-- The evaluation of S at x, as a FiniteGrassmannCarrier. -/
def evalGrassmannAt {p q : ℕ} (S : SuperDomainFunction p q) (x : Fin p → ℝ) :
    FiniteGrassmannCarrier q :=
  fun I => (S.coefficients I).toFun x

/-- The nilpotent part has no constant term. -/
theorem nilpotentPartAt_hasNoConstant {p q : ℕ}
    (S : SuperDomainFunction p q) (x : Fin p → ℝ) :
    hasNoConstant (nilpotentPartAt S x) := by
  show nilpotentPartAt S x ∅ = 0; simp [nilpotentPartAt]

/-- The nilpotent part has smooth coefficients as a function of x. -/
theorem nilpotentPartAt_grassmannSmooth {p q : ℕ} (S : SuperDomainFunction p q) :
    GrassmannSmooth (fun x => nilpotentPartAt S x) := by
  intro I
  show ContDiff ℝ ⊤ (fun x => nilpotentPartAt S x I)
  simp only [nilpotentPartAt]
  by_cases hI : I = ∅
  · simp [hI]; exact contDiff_const
  · simp [hI]; exact (S.coefficients I).smooth

/-! ## SuperDomainFunction-level Inverse -/

/-- Inverse of a SuperDomainFunction whose body is identically 1.
    At each point x, the Grassmann element S(x) = 1 + ε(x) where ε(x) is nilpotent,
    so the inverse is computed via the geometric series pointwise. -/
def SuperDomainFunction.nilpotentInverse {p q : ℕ}
    (S : SuperDomainFunction p q)
    (h_body_one : ∀ x, (S.coefficients ∅).toFun x = 1) : SuperDomainFunction p q where
  coefficients J := {
    toFun := fun x => grassmannGeomInverse (nilpotentPartAt S x) J
    smooth := by
      -- grassmannGeomInverse ε = Σ_{n=0}^{q} (-ε)^n where ε has smooth coefficients
      have hε := nilpotentPartAt_grassmannSmooth S
      -- grassmannGeomInverse (nilpotentPartAt S x) = (Finset.range (q+1)).sum ((-ε)^n)
      show ContDiff ℝ ⊤ (fun x => grassmannGeomInverse (nilpotentPartAt S x) J)
      simp only [grassmannGeomInverse]
      exact (GrassmannSmooth.finset_sum (fun n _ => hε.neg.pow n)) J
  }

/-- S(x) equals 1 + ε(x) as elements of FiniteGrassmannCarrier q. -/
theorem evalGrassmannAt_eq_one_add_eps {p q : ℕ}
    (S : SuperDomainFunction p q) (h_body_one : ∀ x, (S.coefficients ∅).toFun x = 1)
    (x : Fin p → ℝ) :
    evalGrassmannAt S x = 1 + nilpotentPartAt S x := by
  funext I
  show (S.coefficients I).toFun x =
    (1 : FiniteGrassmannCarrier q) I + nilpotentPartAt S x I
  simp only [nilpotentPartAt, one_apply]
  split_ifs with hI
  · subst hI; simp [h_body_one x]
  · simp

/-- The nilpotent inverse is a right inverse at each point:
    S(x) * S⁻¹(x) = 1 in the Grassmann algebra. -/
theorem SuperDomainFunction.nilpotentInverse_mul {p q : ℕ}
    (S : SuperDomainFunction p q)
    (h_body_one : ∀ x, (S.coefficients ∅).toFun x = 1) (x : Fin p → ℝ) :
    evalGrassmannAt S x * grassmannGeomInverse (nilpotentPartAt S x) = 1 := by
  rw [evalGrassmannAt_eq_one_add_eps S h_body_one x]
  exact grassmannGeomInverse_mul_right _ (nilpotentPartAt_hasNoConstant S x)

/-- The nilpotent inverse is a left inverse at each point:
    S⁻¹(x) * S(x) = 1 in the Grassmann algebra. -/
theorem SuperDomainFunction.nilpotentInverse_mul_left {p q : ℕ}
    (S : SuperDomainFunction p q)
    (h_body_one : ∀ x, (S.coefficients ∅).toFun x = 1) (x : Fin p → ℝ) :
    grassmannGeomInverse (nilpotentPartAt S x) * evalGrassmannAt S x = 1 := by
  rw [evalGrassmannAt_eq_one_add_eps S h_body_one x]
  exact grassmannGeomInverse_mul _ (nilpotentPartAt_hasNoConstant S x)

/-! ## Explicit Inverse for General Grassmann Elements

For `v : FiniteGrassmannCarrier q` with `v ∅ ≠ 0`, the inverse is:
  v⁻¹ = (v ∅)⁻¹ • grassmannGeomInverse((v ∅)⁻¹ • grassmannSoul v)

This uses the factoring v = (v ∅) • (1 + δ) where δ = (v ∅)⁻¹ • grassmannSoul v. -/

/-- Factoring: v = (v ∅) • (1 + (v ∅)⁻¹ • grassmannSoul v) when v ∅ ≠ 0 -/
theorem grassmann_factor {q : ℕ} (v : FiniteGrassmannCarrier q) (hv : v ∅ ≠ 0) :
    v = (v ∅) • ((1 : FiniteGrassmannCarrier q) + (v ∅)⁻¹ • grassmannSoul v) := by
  funext I
  show v I = (v ∅) * ((1 : FiniteGrassmannCarrier q) I + (v ∅)⁻¹ * grassmannSoul v I)
  by_cases hI : I = ∅
  · subst hI; simp [grassmannSoul, one_apply]
  · simp only [grassmannSoul, hI, ↓reduceIte, show (1 : FiniteGrassmannCarrier q) I = 0 from by
      simp [one_apply, hI], zero_add]
    rw [← mul_assoc, mul_inv_cancel₀ hv, one_mul]

/-- Explicit inverse for a Grassmann element with nonzero body.
    For v = c + ε where c = v ∅ ≠ 0 and ε = grassmannSoul v:
    v⁻¹ = c⁻¹ • (Σ_{n=0}^q (-c⁻¹ε)^n) -/
noncomputable def grassmannExplicitInverse {q : ℕ} (v : FiniteGrassmannCarrier q)
    (_ : v ∅ ≠ 0) : FiniteGrassmannCarrier q :=
  (v ∅)⁻¹ • grassmannGeomInverse ((v ∅)⁻¹ • grassmannSoul v)

/-- The explicit inverse is a right inverse: v * v⁻¹ = 1. -/
theorem grassmannExplicitInverse_mul_right {q : ℕ} (v : FiniteGrassmannCarrier q)
    (hv : v ∅ ≠ 0) :
    v * grassmannExplicitInverse v hv = 1 := by
  unfold grassmannExplicitInverse
  set c := v ∅ with hc_def
  set δ := c⁻¹ • grassmannSoul v
  have hδ : hasNoConstant δ := smul_hasNoConstant c⁻¹ (grassmannSoul_hasNoConstant v)
  have hv_eq : v = c • ((1 : FiniteGrassmannCarrier q) + δ) := grassmann_factor v hv
  calc v * (c⁻¹ • grassmannGeomInverse δ)
      = (c • (1 + δ)) * (c⁻¹ • grassmannGeomInverse δ) := by rw [hv_eq]
    _ = c • ((1 + δ) * (c⁻¹ • grassmannGeomInverse δ)) := smul_mul_assoc c _ _
    _ = c • (c⁻¹ • ((1 + δ) * grassmannGeomInverse δ)) := by rw [mul_smul_comm]
    _ = (c * c⁻¹) • ((1 + δ) * grassmannGeomInverse δ) := smul_smul c c⁻¹ _
    _ = (1 : ℝ) • ((1 + δ) * grassmannGeomInverse δ) := by rw [mul_inv_cancel₀ hv]
    _ = (1 + δ) * grassmannGeomInverse δ := one_smul _ _
    _ = 1 := grassmannGeomInverse_mul_right δ hδ

/-- The explicit inverse is a left inverse: v⁻¹ * v = 1. -/
theorem grassmannExplicitInverse_mul_left {q : ℕ} (v : FiniteGrassmannCarrier q)
    (hv : v ∅ ≠ 0) :
    grassmannExplicitInverse v hv * v = 1 := by
  unfold grassmannExplicitInverse
  set c := v ∅ with hc_def
  set δ := c⁻¹ • grassmannSoul v
  have hδ : hasNoConstant δ := smul_hasNoConstant c⁻¹ (grassmannSoul_hasNoConstant v)
  have hv_eq : v = c • ((1 : FiniteGrassmannCarrier q) + δ) := grassmann_factor v hv
  calc (c⁻¹ • grassmannGeomInverse δ) * v
      = (c⁻¹ • grassmannGeomInverse δ) * (c • (1 + δ)) := by rw [hv_eq]
    _ = c⁻¹ • (grassmannGeomInverse δ * (c • (1 + δ))) := smul_mul_assoc c⁻¹ _ _
    _ = c⁻¹ • (c • (grassmannGeomInverse δ * (1 + δ))) := by rw [mul_smul_comm]
    _ = (c⁻¹ * c) • (grassmannGeomInverse δ * (1 + δ)) := smul_smul c⁻¹ c _
    _ = (1 : ℝ) • (grassmannGeomInverse δ * (1 + δ)) := by rw [inv_mul_cancel₀ hv]
    _ = grassmannGeomInverse δ * (1 + δ) := one_smul _ _
    _ = 1 := grassmannGeomInverse_mul δ hδ

/-! ## Bridge: Λ.inv equals explicit inverse for finiteGrassmannAlgebra -/

/-- The abstract inverse `Λ.inv` (via Classical.choose) equals the explicit geometric
    series inverse when pushed to carrier via `.val`.

    This bridges the opaque `Classical.choose` with the computable geometric series. -/
theorem finiteGrassmann_inv_val_eq_explicit {q : ℕ}
    (x : (finiteGrassmannAlgebra q).evenCarrier)
    (hx : (finiteGrassmannAlgebra q).IsInvertible x) :
    ((finiteGrassmannAlgebra q).inv x hx).val =
    grassmannExplicitInverse x.val hx := by
  -- By uniqueness of two-sided inverses:
  -- Left inverse: (inv x).val * x.val = 1 (from Λ.inv_mul)
  -- Right inverse: x.val * explicit_inv = 1 (from grassmannExplicitInverse_mul_right)
  have h_left : ((finiteGrassmannAlgebra q).inv x hx).val * x.val = 1 :=
    congrArg Subtype.val ((finiteGrassmannAlgebra q).inv_mul x hx)
  have h_right : x.val * grassmannExplicitInverse x.val hx = 1 :=
    grassmannExplicitInverse_mul_right x.val hx
  calc ((finiteGrassmannAlgebra q).inv x hx).val
      = ((finiteGrassmannAlgebra q).inv x hx).val * 1 := (mul_one _).symm
    _ = ((finiteGrassmannAlgebra q).inv x hx).val *
        (x.val * grassmannExplicitInverse x.val hx) := by rw [h_right]
    _ = (((finiteGrassmannAlgebra q).inv x hx).val * x.val) *
        grassmannExplicitInverse x.val hx := (mul_assoc _ _ _).symm
    _ = 1 * grassmannExplicitInverse x.val hx := by rw [h_left]
    _ = grassmannExplicitInverse x.val hx := one_mul _

/-! ## GrassmannSmooth for Explicit Inverse -/

/-- The soul of a GrassmannSmooth function is GrassmannSmooth. -/
theorem grassmannSoul_grassmannSmooth {p q : ℕ}
    {f : (Fin p → ℝ) → FiniteGrassmannCarrier q}
    (hf : GrassmannSmooth f) :
    GrassmannSmooth (fun x => grassmannSoul (f x)) := by
  intro J
  show ContDiff ℝ ⊤ (fun x => grassmannSoul (f x) J)
  simp only [grassmannSoul]
  by_cases hJ : J = ∅
  · simp only [hJ, ↓reduceIte]; exact contDiff_const
  · simp only [hJ, ↓reduceIte]; exact hf J

/-- The explicit inverse of a GrassmannSmooth function with nonzero body is GrassmannSmooth.

    For `f(x) = c(x) + ε(x)` where `c(x) = f(x) ∅ ≠ 0`:
    `f(x)⁻¹ = c(x)⁻¹ • grassmannGeomInverse(c(x)⁻¹ • ε(x))`

    Each coefficient of the result is smooth because:
    - `c(x)⁻¹` is smooth (composition with `·⁻¹` away from zero)
    - `grassmannGeomInverse` is a polynomial (finite sum of powers) in the coefficients -/
theorem grassmannExplicitInverse_grassmannSmooth {p q : ℕ}
    {f : (Fin p → ℝ) → FiniteGrassmannCarrier q}
    (hf : GrassmannSmooth f) (hne : ∀ x, f x ∅ ≠ 0) :
    GrassmannSmooth (fun x => grassmannExplicitInverse (f x) (hne x)) := by
  -- grassmannExplicitInverse (f x) = (f x ∅)⁻¹ • grassmannGeomInverse((f x ∅)⁻¹ • grassmannSoul(f x))
  show GrassmannSmooth (fun x =>
    (f x ∅)⁻¹ • grassmannGeomInverse ((f x ∅)⁻¹ • grassmannSoul (f x)))
  -- c(x) = f(x) ∅ is smooth
  have hc : ContDiff ℝ ⊤ (fun x => f x ∅) := hf ∅
  -- c(x)⁻¹ is smooth (Mathlib's ContDiff.inv)
  have hc_inv : ContDiff ℝ ⊤ (fun x => (f x ∅)⁻¹) := hc.inv hne
  -- grassmannSoul(f(x)) is GrassmannSmooth
  have hsoul : GrassmannSmooth (fun x => grassmannSoul (f x)) :=
    grassmannSoul_grassmannSmooth hf
  -- δ(x) = c(x)⁻¹ • grassmannSoul(f(x)) is GrassmannSmooth
  have hδ : GrassmannSmooth (fun x => (f x ∅)⁻¹ • grassmannSoul (f x)) :=
    GrassmannSmooth.smul_fun hc_inv hsoul
  -- grassmannGeomInverse(δ(x)) = Σ_{n=0}^q (-δ(x))^n is GrassmannSmooth
  have hgeom : GrassmannSmooth
      (fun x => grassmannGeomInverse ((f x ∅)⁻¹ • grassmannSoul (f x))) := by
    show GrassmannSmooth (fun x =>
      (Finset.range (q + 1)).sum fun n => (-((f x ∅)⁻¹ • grassmannSoul (f x))) ^ n)
    exact GrassmannSmooth.finset_sum (fun n _ => hδ.neg.pow n)
  -- c(x)⁻¹ • result is GrassmannSmooth
  exact GrassmannSmooth.smul_fun hc_inv hgeom

/-- The abstract inverse (via Λ.inv) is GrassmannSmooth when the input is GrassmannSmooth
    with nonzero body.

    Uses the bridge: `(Λ.inv x hx).val = grassmannExplicitInverse x.val hx`. -/
theorem finiteGrassmann_inv_grassmannSmooth {p q : ℕ}
    {f : (Fin p → ℝ) → (finiteGrassmannAlgebra q).evenCarrier}
    (hf : GrassmannSmooth (fun x => (f x).val))
    (hInv : ∀ x, (finiteGrassmannAlgebra q).IsInvertible (f x)) :
    GrassmannSmooth (fun x => ((finiteGrassmannAlgebra q).inv (f x) (hInv x)).val) := by
  -- Rewrite using the bridge lemma
  have h_eq : ∀ x, ((finiteGrassmannAlgebra q).inv (f x) (hInv x)).val =
      grassmannExplicitInverse (f x).val (hInv x) :=
    fun x => finiteGrassmann_inv_val_eq_explicit (f x) (hInv x)
  show GrassmannSmooth (fun x => ((finiteGrassmannAlgebra q).inv (f x) (hInv x)).val)
  have : (fun x => ((finiteGrassmannAlgebra q).inv (f x) (hInv x)).val) =
      (fun x => grassmannExplicitInverse (f x).val (hInv x)) := funext h_eq
  rw [this]
  exact grassmannExplicitInverse_grassmannSmooth hf hInv

/-! ## GrassmannSmooth for Even Products and Determinants -/

/-- ℤ-scalar multiplication preserves GrassmannSmooth.
    Uses that zsmul on FiniteGrassmannCarrier is pointwise: (n • a) J = ↑n * a J. -/
theorem GrassmannSmooth.zsmul_const {p q : ℕ} (n : ℤ)
    {f : (Fin p → ℝ) → FiniteGrassmannCarrier q}
    (hf : GrassmannSmooth f) :
    GrassmannSmooth (fun x => n • f x) := by
  intro J
  -- zsmul on FiniteGrassmannCarrier q is pointwise: (n • a) I = ↑n * a I
  -- So (n • f x) J = ↑n * (f x J), which is ContDiff as constant * smooth
  exact contDiff_const.mul (hf J)

/-- `.val` distributes over multiplication for FiniteGrassmannEven. -/
theorem evenVal_mul {q : ℕ} (a b : FiniteGrassmannEven q) :
    (a * b).val = a.val * b.val :=
  (evenToCarrierHom (q := q)).map_mul a b

/-- Product of even-valued GrassmannSmooth functions is GrassmannSmooth.
    Uses induction via Fin.prod_univ_succ in evenCarrier (CommMonoid),
    then distributes .val to carrier via the ring hom. -/
theorem evenProd_grassmannSmooth {p q n : ℕ}
    {f : Fin n → (Fin p → ℝ) → (finiteGrassmannAlgebra q).evenCarrier}
    (hf : ∀ i, GrassmannSmooth (fun x => (f i x).val)) :
    GrassmannSmooth (fun x => (Finset.univ.prod (fun i => f i x)).val) := by
  induction n with
  | zero =>
    have h : ∀ x, Finset.univ.prod (fun i : Fin 0 => f i x) = 1 :=
      fun x => Fin.prod_univ_zero _
    simp_rw [h]; show GrassmannSmooth (fun _ => (1 : FiniteGrassmannEven q).val)
    exact GrassmannSmooth.one
  | succ m ih =>
    have h : ∀ x, (Finset.univ.prod (fun i : Fin (m + 1) => f i x)).val =
        (f 0 x).val * (Finset.univ.prod (fun i : Fin m => f (Fin.succ i) x)).val := by
      intro x; rw [Fin.prod_univ_succ]; exact evenVal_mul _ _
    simp_rw [h]
    exact (hf 0).mul (ih (fun i => hf (Fin.succ i)))

/-- `.val` distributes over `Finset.sum` for FiniteGrassmannEven. -/
private theorem evenVal_sum {q : ℕ} {ι : Type*} (s : Finset ι)
    (f : ι → FiniteGrassmannEven q) :
    (s.sum f).val = s.sum (fun i => (f i).val) :=
  map_sum (evenToCarrierHom (q := q)) f s

/-- `.val` distributes over ℤ-scalar multiplication for FiniteGrassmannEven.
    By definition: zsmul n x = ⟨n • x.val, _⟩, so (n • x).val = n • x.val. -/
private theorem evenVal_zsmul {q : ℕ} (n : ℤ) (a : FiniteGrassmannEven q) :
    (n • a).val = n • a.val := rfl

/-- The determinant of an evenCarrier-valued matrix with GrassmannSmooth entries
    has GrassmannSmooth .val.

    Uses: det M = ∑ σ, sign(σ) • ∏ i, M(σ(i), i), then distributes .val
    over the sum and ℤ-scalar multiplication. -/
theorem det_even_grassmannSmooth {p q n : ℕ}
    {M : (Fin p → ℝ) → Matrix (Fin n) (Fin n) (finiteGrassmannAlgebra q).evenCarrier}
    (hM : ∀ i j, GrassmannSmooth (fun x => (M x i j).val)) :
    GrassmannSmooth (fun x => ((M x).det).val) := by
  -- Step 1: Rewrite det using the explicit formula and distribute .val
  have h_val_det : ∀ x, ((M x).det).val =
      Finset.univ.sum (fun σ : Equiv.Perm (Fin n) =>
        (Equiv.Perm.sign σ : ℤ) • (Finset.univ.prod (fun i => M x (σ i) i)).val) := by
    intro x
    exact (congrArg Subtype.val (Matrix.det_apply (M x))).trans
      ((evenVal_sum _ _).trans (Finset.sum_congr rfl fun σ _ => rfl))
  simp_rw [h_val_det]
  -- Step 2: The sum is GrassmannSmooth
  exact GrassmannSmooth.finset_sum (fun σ _ =>
    GrassmannSmooth.zsmul_const _ (evenProd_grassmannSmooth (fun i => hM (σ i) i)))

/-- Matrix product of carrier-valued matrices with GrassmannSmooth entries
    has GrassmannSmooth entries. -/
theorem matMul_grassmannSmooth {p q n m l : ℕ}
    {A : (Fin p → ℝ) → Matrix (Fin n) (Fin m) (FiniteGrassmannCarrier q)}
    {B : (Fin p → ℝ) → Matrix (Fin m) (Fin l) (FiniteGrassmannCarrier q)}
    (hA : ∀ i j, GrassmannSmooth (fun x => A x i j))
    (hB : ∀ i j, GrassmannSmooth (fun x => B x i j)) :
    ∀ i j, GrassmannSmooth (fun x => (A x * B x) i j) := by
  intro i j
  show GrassmannSmooth (fun x => Finset.univ.sum (fun k => A x i k * B x k j))
  exact GrassmannSmooth.finset_sum (fun k _ => (hA i k).mul (hB k j))

/-- Subtraction of carrier-valued matrices with GrassmannSmooth entries
    has GrassmannSmooth entries. -/
theorem matSub_grassmannSmooth {p q n m : ℕ}
    {A B : (Fin p → ℝ) → Matrix (Fin n) (Fin m) (FiniteGrassmannCarrier q)}
    (hA : ∀ i j, GrassmannSmooth (fun x => A x i j))
    (hB : ∀ i j, GrassmannSmooth (fun x => B x i j)) :
    ∀ i j, GrassmannSmooth (fun x => (A x - B x) i j) := by
  intro i j
  show GrassmannSmooth (fun x => A x i j - B x i j)
  exact (hA i j).sub (hB i j)

/-! ## Ring.inverse Bridge and Matrix Inverse Smoothness -/

/-- Ring.inverse on evenCarrier agrees with GrassmannAlgebra.inv
    when the element is invertible (body ≠ 0). Both are the unique two-sided inverse. -/
theorem ringInverse_eq_grassmannInv {q : ℕ} (a : (finiteGrassmannAlgebra q).evenCarrier)
    (h : (finiteGrassmannAlgebra q).IsInvertible a) :
    Ring.inverse a = (finiteGrassmannAlgebra q).inv a h := by
  have hU := ((finiteGrassmannAlgebra q).isUnit_iff_body_ne_zero a).mpr h
  calc Ring.inverse a
      = 1 * Ring.inverse a := (one_mul _).symm
    _ = ((finiteGrassmannAlgebra q).inv a h * a) * Ring.inverse a := by
          rw [(finiteGrassmannAlgebra q).inv_mul a h]
    _ = (finiteGrassmannAlgebra q).inv a h * (a * Ring.inverse a) := mul_assoc _ _ _
    _ = (finiteGrassmannAlgebra q).inv a h * 1 := by
          rw [Ring.mul_inverse_cancel a hU]
    _ = (finiteGrassmannAlgebra q).inv a h := mul_one _

/-- Ring.inverse of an even element with invertible body has GrassmannSmooth .val. -/
theorem ringInverse_even_grassmannSmooth {p q : ℕ}
    {f : (Fin p → ℝ) → (finiteGrassmannAlgebra q).evenCarrier}
    (hf : GrassmannSmooth (fun x => (f x).val))
    (hInv : ∀ x, (finiteGrassmannAlgebra q).IsInvertible (f x)) :
    GrassmannSmooth (fun x => (Ring.inverse (f x)).val) := by
  have h_eq : ∀ x, (Ring.inverse (f x)).val =
      ((finiteGrassmannAlgebra q).inv (f x) (hInv x)).val :=
    fun x => congrArg Subtype.val (ringInverse_eq_grassmannInv (f x) (hInv x))
  simp_rw [h_eq]
  exact finiteGrassmann_inv_grassmannSmooth hf hInv

/-- Adjugate of an even-valued matrix with GrassmannSmooth entries has GrassmannSmooth .val
    entries. Uses: adjugate M i j = det(M.updateRow j (Pi.single i 1)). -/
theorem adjugate_even_grassmannSmooth {p q n : ℕ}
    {M : (Fin p → ℝ) → Matrix (Fin n) (Fin n) (finiteGrassmannAlgebra q).evenCarrier}
    (hM : ∀ i j, GrassmannSmooth (fun x => (M x i j).val)) :
    ∀ i j, GrassmannSmooth (fun x => ((M x).adjugate i j).val) := by
  intro i0 j0
  -- adjugate M i0 j0 = det(M.updateRow j0 (Pi.single i0 1))
  simp_rw [Matrix.adjugate_apply]
  -- Apply det_even_grassmannSmooth to the updated matrix
  apply det_even_grassmannSmooth
  intro k l
  -- Expand updateRow to if-then-else, then split on whether k = j0
  simp_rw [Matrix.updateRow_apply]
  by_cases hk : k = j0
  · -- Row j0: entry is Pi.single i0 1 l (constant in x)
    simp_rw [if_pos hk]
    exact GrassmannSmooth.const _
  · -- Other rows: entry is M x k l (GrassmannSmooth by hypothesis)
    simp_rw [if_neg hk]
    exact hM k l

/-- Matrix inverse entries over evenCarrier with GrassmannSmooth .val entries have
    GrassmannSmooth .val, when the determinant is invertible at every point.

    Uses: M⁻¹ = Ring.inverse(det M) • adjugate(M), so each entry is
    Ring.inverse(det M) * adjugate(M) i j. -/
theorem matInv_even_grassmannSmooth {p q n : ℕ}
    {M : (Fin p → ℝ) → Matrix (Fin n) (Fin n) (finiteGrassmannAlgebra q).evenCarrier}
    (hM : ∀ i j, GrassmannSmooth (fun x => (M x i j).val))
    (hDet : ∀ x, (finiteGrassmannAlgebra q).IsInvertible (M x).det) :
    ∀ i j, GrassmannSmooth (fun x => ((M x)⁻¹ i j).val) := by
  intro i j
  -- M⁻¹ = Ring.inverse(det M) • adjugate(M)
  -- Each entry: (M⁻¹ i j) = Ring.inverse(det M) * adjugate(M) i j
  have h_entry : ∀ x, ((M x)⁻¹ i j).val =
      (Ring.inverse (M x).det).val * ((M x).adjugate i j).val := by
    intro x
    -- M⁻¹ = Ring.inverse(det M) • adjugate(M) by definition
    change ((Ring.inverse (M x).det • (M x).adjugate) i j).val = _
    -- (c • N) i j = c * N i j
    show (Ring.inverse (M x).det * (M x).adjugate i j).val = _
    exact evenVal_mul _ _
  simp_rw [h_entry]
  exact (ringInverse_even_grassmannSmooth (det_even_grassmannSmooth hM) hDet).mul
    (adjugate_even_grassmannSmooth hM i j)

end Supermanifolds
