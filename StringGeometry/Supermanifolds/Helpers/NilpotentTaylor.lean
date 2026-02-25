/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license.
-/
import StringGeometry.Supermanifolds.Supermanifolds
import StringGeometry.Supermanifolds.Helpers.FiniteGrassmann

/-!
# Nilpotent Taylor Expansion

Full Taylor expansion of smooth functions applied to Grassmann-valued inputs.

For f : ℝ^p → ℝ smooth and y = (y₁,...,yₚ) with yₖ = aₖ + δₖ where δₖ are
nilpotent Grassmann elements:

  f(a + δ) = Σ_{n=0}^{q} (1/n!) Σ_{k₁,...,kₙ} (∂ⁿf/∂x_{k₁}...∂x_{kₙ})(a) · δ_{k₁}·...·δ_{kₙ}

This terminates because products of q+1 or more elements with no constant term vanish
in the Grassmann algebra Λ_q.

## Main Definitions

* `SmoothFunction.partialDeriv` - partial derivative ∂f/∂x_i
* `iteratedPartialDeriv` - iterated partial derivatives ∂ⁿf/∂x_{k₁}...∂x_{kₙ}
* `taylorTermGrassmann` - n-th order Taylor term
* `smoothTaylorGrassmann` - full Taylor expansion (truncated at order q by nilpotency)

## Main Theorems

* `smoothTaylorGrassmann_scalar` - at scalar inputs, expansion equals f(a) as scalar
* `prod_list_hasNoConstant_vanishes` - products of >q elements with no constant term vanish
* `taylorTermGrassmann_beyond_q` - Taylor terms of order > q vanish

## Important: Commutative Ring, Not Field

The Grassmann algebra FiniteGrassmannCarrier q is a commutative ring with ZERO DIVISORS,
not a field. All "division by n!" is handled via ℝ-scalar multiplication:

  ((n.factorial : ℝ)⁻¹) • (...)

Never use division within the Grassmann algebra itself.

## References

* Witten, "Notes On Supermanifolds And Integration" (1209.2199), §3
* Rogers, "Supermanifolds" (2007), Chapter 4
-/

noncomputable section

namespace Supermanifolds

open Supermanifolds.Helpers FiniteGrassmannCarrier

/-! ## Smooth Partial Derivatives -/

/-- Partial derivative of a smooth function f : ℝ^p → ℝ with respect to x_i.
    Uses Mathlib's Fréchet derivative applied to the i-th unit direction. -/
def SmoothFunction.partialDeriv {p : ℕ} (i : Fin p)
    (f : SmoothFunction p) : SmoothFunction p where
  toFun := fun x => fderiv ℝ f.toFun x (Pi.single i 1)
  smooth := f.smooth.fderiv_right
    (le_of_eq (WithTop.top_add (1 : WithTop ℕ∞))) |>.clm_apply contDiff_const

/-- The partial derivative of a constant function is the zero function. -/
theorem SmoothFunction.partialDeriv_const {p : ℕ} (c : ℝ) (i : Fin p) :
    SmoothFunction.partialDeriv i ⟨fun _ => c, contDiff_const⟩ =
    (⟨fun _ => 0, contDiff_const⟩ : SmoothFunction p) := by
  ext x
  show fderiv ℝ (fun (_ : Fin p → ℝ) => c) x (Pi.single i 1) = 0
  rw [(hasFDerivAt_const c x).fderiv]
  rfl

/-- Iterated partial derivative of a smooth function.
    `iteratedPartialDeriv [i₁, i₂, ..., iₙ] f` computes
    ∂ⁿf / ∂x_{i₁} ∂x_{i₂} ... ∂x_{iₙ}

    For C^∞ functions, mixed partials are symmetric (Schwarz's theorem),
    so the order of indices doesn't affect the value.

    The recursion applies the leftmost derivative last:
    iteratedPartialDeriv [i, j] f = ∂/∂x_i (∂f/∂x_j) -/
def iteratedPartialDeriv {p : ℕ} :
    List (Fin p) → SmoothFunction p → SmoothFunction p
  | [], f => f
  | i :: rest, f => SmoothFunction.partialDeriv i (iteratedPartialDeriv rest f)

/-- Iterated partial derivative preserves smoothness (trivially, since
    each application of partialDeriv produces a SmoothFunction). -/
theorem iteratedPartialDeriv_smooth {p : ℕ} (dirs : List (Fin p)) (f : SmoothFunction p) :
    ContDiff ℝ ⊤ (iteratedPartialDeriv dirs f).toFun :=
  (iteratedPartialDeriv dirs f).smooth

/-- Empty list gives the original function. -/
@[simp]
theorem iteratedPartialDeriv_nil {p : ℕ} (f : SmoothFunction p) :
    iteratedPartialDeriv [] f = f := rfl

/-- Single-element list gives the partial derivative. -/
@[simp]
theorem iteratedPartialDeriv_singleton {p : ℕ} (i : Fin p) (f : SmoothFunction p) :
    iteratedPartialDeriv [i] f = SmoothFunction.partialDeriv i f := rfl

/-- Cons list splits into partial derivative of the rest. -/
@[simp]
theorem iteratedPartialDeriv_cons {p : ℕ} (i : Fin p) (rest : List (Fin p))
    (f : SmoothFunction p) :
    iteratedPartialDeriv (i :: rest) f =
    SmoothFunction.partialDeriv i (iteratedPartialDeriv rest f) := rfl

/-- Iterated partial derivatives of a constant function are all zero (for non-empty lists). -/
theorem iteratedPartialDeriv_const {p : ℕ} (c : ℝ) :
    ∀ (dirs : List (Fin p)), dirs ≠ [] →
    iteratedPartialDeriv dirs (⟨fun _ => c, contDiff_const⟩ : SmoothFunction p) =
    ⟨fun _ => 0, contDiff_const⟩ := by
  intro dirs
  induction dirs with
  | nil => intro h; exact absurd rfl h
  | cons i rest ih =>
    intro _
    simp only [iteratedPartialDeriv_cons]
    cases rest with
    | nil =>
      -- Single derivative of a constant
      exact SmoothFunction.partialDeriv_const c i
    | cons j rest' =>
      -- iteratedPartialDeriv (j :: rest') (const c) = const 0 by IH
      rw [ih (List.cons_ne_nil _ _)]
      -- partialDeriv i (const 0) = const 0
      exact SmoothFunction.partialDeriv_const 0 i

/-! ## Linearity of Iterated Partial Derivatives -/

/-- Iterated partial derivative is additive: ∂ⁿ(f+g)(x) = ∂ⁿf(x) + ∂ⁿg(x). -/
theorem iteratedPartialDeriv_add_apply {p : ℕ} (dirs : List (Fin p))
    (f g : SmoothFunction p) (x : Fin p → ℝ) :
    (iteratedPartialDeriv dirs
      ⟨fun x => f.toFun x + g.toFun x, f.smooth.add g.smooth⟩).toFun x =
    (iteratedPartialDeriv dirs f).toFun x +
    (iteratedPartialDeriv dirs g).toFun x := by
  induction dirs generalizing x with
  | nil => rfl
  | cons i rest ih =>
    simp only [iteratedPartialDeriv_cons, SmoothFunction.partialDeriv]
    have ih_fun : (iteratedPartialDeriv rest
        ⟨fun x => f.toFun x + g.toFun x, f.smooth.add g.smooth⟩).toFun =
        fun y => (iteratedPartialDeriv rest f).toFun y +
                 (iteratedPartialDeriv rest g).toFun y :=
      funext ih
    rw [ih_fun]
    -- Convert lambda form to Pi.add form for fderiv_add
    have hpi : (fun y => (iteratedPartialDeriv rest f).toFun y +
        (iteratedPartialDeriv rest g).toFun y) =
        (iteratedPartialDeriv rest f).toFun +
        (iteratedPartialDeriv rest g).toFun := rfl
    rw [hpi, fderiv_add
      ((iteratedPartialDeriv rest f).smooth.differentiable (by decide)).differentiableAt
      ((iteratedPartialDeriv rest g).smooth.differentiable (by decide)).differentiableAt]
    rfl

/-- Iterated partial derivative commutes with scalar multiplication:
    ∂ⁿ(c·f)(x) = c · ∂ⁿf(x). -/
theorem iteratedPartialDeriv_smul_apply {p : ℕ} (dirs : List (Fin p))
    (c : ℝ) (f : SmoothFunction p) (x : Fin p → ℝ) :
    (iteratedPartialDeriv dirs
      ⟨fun x => c * f.toFun x, contDiff_const.mul f.smooth⟩).toFun x =
    c * (iteratedPartialDeriv dirs f).toFun x := by
  induction dirs generalizing x with
  | nil => rfl
  | cons i rest ih =>
    simp only [iteratedPartialDeriv_cons, SmoothFunction.partialDeriv]
    have ih_fun : (iteratedPartialDeriv rest
        ⟨fun x => c * f.toFun x, contDiff_const.mul f.smooth⟩).toFun =
        fun y => c * (iteratedPartialDeriv rest f).toFun y :=
      funext ih
    rw [ih_fun]
    -- Convert c * h to c • h for fderiv_const_smul
    have hsmul : (fun y => c * (iteratedPartialDeriv rest f).toFun y) =
        (fun y => c • (iteratedPartialDeriv rest f).toFun y) :=
      funext (fun y => (smul_eq_mul c _).symm)
    rw [hsmul]
    -- Convert lambda form to Pi.smul form
    have hpi : (fun y => c • (iteratedPartialDeriv rest f).toFun y) =
        c • (iteratedPartialDeriv rest f).toFun := rfl
    rw [hpi, fderiv_const_smul
      ((iteratedPartialDeriv rest f).smooth.differentiable (by decide)).differentiableAt]
    simp [ContinuousLinearMap.smul_apply, smul_eq_mul]

/-! ## Product Vanishing in Grassmann Algebra

Products of sufficiently many elements with no constant term vanish in Λ_q,
because the Grassmann algebra has only q generators and any monomial
of degree > q is zero.

Note: FiniteGrassmannCarrier q is a RING with ZERO DIVISORS, not a field.
This vanishing result depends on the Grassmann algebra structure, not on
invertibility properties. -/

/-- A product of elements with no constant term has no constant term (if nonempty). -/
theorem List.prod_hasNoConstant {q : ℕ} (fs : List (FiniteGrassmannCarrier q))
    (hall : ∀ f ∈ fs, hasNoConstant f) (hne : fs ≠ []) : hasNoConstant fs.prod := by
  induction fs with
  | nil => exact absurd rfl hne
  | cons f rest ih =>
    rw [List.prod_cons]
    cases rest with
    | nil =>
      simp only [List.prod_nil]
      have : f * 1 = f := mul_one f
      rw [this]
      exact hall f (List.Mem.head _)
    | cons g rest' =>
      apply mul_hasNoConstant
      · exact hall f (List.Mem.head _)
      · exact ih (fun x hx => hall x (List.Mem.tail _ hx)) (List.cons_ne_nil _ _)

/-- Products of more than q elements with no constant term vanish in Λ_q.
    This is the fundamental reason why nilpotent Taylor expansions terminate.

    The proof generalizes `grassmann_soul_nilpotent`: each factor has no constant
    term, so it contributes at least "degree 1" to the product. After q+1 factors,
    the total degree exceeds q, which is impossible since Fin q has only q elements. -/
theorem prod_list_hasNoConstant_vanishes {q : ℕ} (fs : List (FiniteGrassmannCarrier q))
    (hall : ∀ f ∈ fs, hasNoConstant f) (hlen : q < fs.length) : fs.prod = 0 := by
  funext K
  have hK : K.card ≤ q := by
    have := Finset.card_le_card (Finset.subset_univ K)
    simp only [Finset.card_fin] at this
    exact this
  -- General lemma quantifying over K
  suffices h : ∀ (gs : List (FiniteGrassmannCarrier q)) (K' : Finset (Fin q)),
      (∀ g ∈ gs, hasNoConstant g) → K'.card < gs.length → gs.prod K' = 0 by
    exact h fs K hall (by omega)
  intro gs
  induction gs with
  | nil =>
    intro K' _ hK'
    simp at hK'
  | cons g rest ih =>
    intro K' hgs hK'
    rw [List.prod_cons]
    show (Finset.univ.sum fun I => Finset.univ.sum fun J =>
      if I ∪ J = K' ∧ I ∩ J = ∅ then reorderSign I J * g I * rest.prod J else 0) = 0
    apply Finset.sum_eq_zero
    intro I _
    apply Finset.sum_eq_zero
    intro J _
    split_ifs with hIJ
    · obtain ⟨hK_eq, hDisj⟩ := hIJ
      have hCard : K'.card = I.card + J.card := by
        rw [← hK_eq]
        exact Finset.card_union_of_disjoint (Finset.disjoint_iff_inter_eq_empty.mpr hDisj)
      by_cases hI : I = ∅
      · have hg_nc : hasNoConstant g := hgs g (List.Mem.head _)
        rw [hI, hg_nc]
        ring
      · have hIcard : I.card ≥ 1 := Finset.one_le_card.mpr (Finset.nonempty_iff_ne_empty.mpr hI)
        have hJcard : J.card < rest.length := by
          simp only [List.length_cons] at hK'
          omega
        have hrest : ∀ r ∈ rest, hasNoConstant r :=
          fun r hr => hgs r (List.Mem.tail _ hr)
        rw [ih J hrest hJcard]
        ring
    · rfl

/-! ## Taylor Terms -/

/-- The n-th order Taylor term for a smooth function with Grassmann-valued increments.

    T_n(f, a, δ) = Σ_{k₁,...,kₙ ∈ Fin p} ((1/n!) · (∂ⁿf/∂x_{k₁}...∂x_{kₙ})(a)) • (δ_{k₁}·...·δ_{kₙ})

    Key design choice: the 1/n! factor and derivative value are combined into a single
    ℝ scalar, which then acts on the Grassmann product via SMul ℝ. We NEVER divide
    within the Grassmann algebra (it is a commutative ring with zero divisors, not a field).

    The sum is over all ordered tuples (k₁,...,kₙ) ∈ (Fin p)^n. By Schwarz's theorem,
    the mixed partials are symmetric, so the multinomial structure is encoded in the
    overcounting: each multi-index α with |α| = n appears n!/α! times, and the
    1/n! factor converts this to the correct multinomial coefficient 1/α!. -/
def taylorTermGrassmann {p q : ℕ} (n : ℕ) (f : SmoothFunction p)
    (a : Fin p → ℝ) (delta : Fin p → FiniteGrassmannCarrier q) : FiniteGrassmannCarrier q :=
  Finset.univ.sum fun (dirs : Fin n → Fin p) =>
    (((n.factorial : ℝ)⁻¹ * (iteratedPartialDeriv (List.ofFn dirs) f).toFun a)) •
    (List.ofFn (fun i => delta (dirs i))).prod

/-- Full nilpotent Taylor expansion of a smooth function applied to Grassmann-valued inputs.

    f̃(y) = Σ_{n=0}^{q} T_n(f, body(y), soul(y))

    The sum is truncated at n = q because products of q+1 or more Grassmann elements
    with no constant term vanish (by `prod_list_hasNoConstant_vanishes`).

    This replaces the first-order approximation `SmoothFunction.extendToGrassmann`. -/
def smoothTaylorGrassmann {p q : ℕ}
    (f : SmoothFunction p) (y : Fin p → FiniteGrassmannCarrier q) : FiniteGrassmannCarrier q :=
  let a := fun k => grassmannBody (y k)
  let delta := fun k => grassmannSoul (y k)
  (Finset.range (q + 1)).sum fun n => taylorTermGrassmann n f a delta

/-! ## Key Properties -/

/-- The zeroth-order Taylor term is f(a) embedded as a Grassmann scalar. -/
theorem taylorTermGrassmann_zero {p q : ℕ} (f : SmoothFunction p)
    (a : Fin p → ℝ) (delta : Fin p → FiniteGrassmannCarrier q) :
    taylorTermGrassmann 0 f a delta = grassmannScalar (f.toFun a) := by
  simp only [taylorTermGrassmann]
  -- Fin 0 → Fin p has a unique element, so the sum is a singleton
  have huniq : (Finset.univ : Finset (Fin 0 → Fin p)) = {Fin.elim0} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    exact ⟨Finset.mem_univ _, fun x _ => Subsingleton.elim x _⟩
  rw [huniq, Finset.sum_singleton]
  simp only [Nat.factorial_zero, Nat.cast_one, inv_one, one_mul]
  -- List.ofFn with Fin 0 is empty, empty product is 1
  change f.toFun a • (List.ofFn (fun i : Fin 0 => delta (Fin.elim0 i))).prod =
    grassmannScalar (f.toFun a)
  simp only [List.ofFn_zero, List.prod_nil]
  -- r • 1 = grassmannScalar r
  funext I
  simp only [smul_apply, one_apply, grassmannScalar]
  split_ifs <;> ring

/-- When all increments are zero, the n-th Taylor term vanishes for n ≥ 1. -/
theorem taylorTermGrassmann_zero_delta {p q : ℕ} (n : ℕ) (hn : 1 ≤ n)
    (f : SmoothFunction p) (a : Fin p → ℝ) :
    taylorTermGrassmann n f a (fun _ => (0 : FiniteGrassmannCarrier q)) = 0 := by
  simp only [taylorTermGrassmann]
  apply Finset.sum_eq_zero
  intro dirs _
  -- The product contains at least one factor of 0 (since n ≥ 1)
  suffices hprod : (List.ofFn (fun i : Fin n =>
      (fun _ : Fin p => (0 : FiniteGrassmannCarrier q)) (dirs i))).prod = 0 by
    rw [hprod, smul_zero]
  -- Simplify: each element is 0
  have hsimpl : (fun i : Fin n =>
      (fun _ : Fin p => (0 : FiniteGrassmannCarrier q)) (dirs i)) =
      fun _ => 0 := by ext; rfl
  rw [hsimpl]
  -- List of n ≥ 1 zeros has product 0
  cases n with
  | zero => omega
  | succ m => rw [List.ofFn_succ, List.prod_cons]; exact zero_mul _

/-- Taylor terms of order > q vanish because the product of q+1 or more
    soul elements (each with no constant term) is zero in Λ_q.

    This justifies the truncation in `smoothTaylorGrassmann`. -/
theorem taylorTermGrassmann_beyond_q {p q : ℕ} (n : ℕ) (hn : q < n)
    (f : SmoothFunction p) (a : Fin p → ℝ)
    (delta : Fin p → FiniteGrassmannCarrier q)
    (h_noconst : ∀ k, hasNoConstant (delta k)) :
    taylorTermGrassmann n f a delta = 0 := by
  simp only [taylorTermGrassmann]
  apply Finset.sum_eq_zero
  intro dirs _
  have hprod : (List.ofFn (fun i : Fin n => delta (dirs i))).prod = 0 := by
    apply prod_list_hasNoConstant_vanishes
    · intro f hf
      rw [List.mem_ofFn] at hf
      obtain ⟨i, rfl⟩ := hf
      exact h_noconst (dirs i)
    · simp only [List.length_ofFn]
      exact hn
  rw [hprod]
  funext I
  simp only [smul_apply, zero_apply, mul_zero]

/-- The Taylor expansion at scalar inputs equals f(a) embedded as scalar.
    This is the fundamental correctness property: when y_k has no soul part,
    the expansion reduces to the function value. -/
theorem smoothTaylorGrassmann_scalar {p q : ℕ} (f : SmoothFunction p)
    (a : Fin p → ℝ) :
    smoothTaylorGrassmann (p := p) (q := q) f (fun k => grassmannScalar (a k)) =
    grassmannScalar (f.toFun a) := by
  simp only [smoothTaylorGrassmann]
  have h_body : (fun k => grassmannBody (grassmannScalar (a k) : FiniteGrassmannCarrier q)) =
      a := by
    funext k; simp [grassmannBody, grassmannScalar]
  have h_soul : (fun k => grassmannSoul (grassmannScalar (a k) : FiniteGrassmannCarrier q)) =
      (fun _ => (0 : FiniteGrassmannCarrier q)) := by
    funext k I
    simp only [grassmannSoul, grassmannScalar]
    by_cases hI : I = ∅ <;> simp [hI]
  rw [h_body, h_soul]
  -- Use Finset.sum_eq_single: the sum reduces to the n=0 term
  rw [Finset.sum_eq_single 0]
  · exact taylorTermGrassmann_zero f a _
  · intro n _ hn
    exact taylorTermGrassmann_zero_delta n (Nat.pos_of_ne_zero hn) f a
  · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h

/-- The soul of a Grassmann element has no constant term. -/
theorem grassmannSoul_hasNoConstant' {q : ℕ} (y : FiniteGrassmannCarrier q) :
    hasNoConstant (grassmannSoul y) := grassmannSoul_empty y

/-- Taylor terms of order > q vanish in the full expansion, for any input.
    This is a corollary of `taylorTermGrassmann_beyond_q` applied to soul parts. -/
theorem taylorTermGrassmann_beyond_q' {p q : ℕ} (n : ℕ) (hn : q < n)
    (f : SmoothFunction p) (y : Fin p → FiniteGrassmannCarrier q) :
    taylorTermGrassmann n f (fun k => grassmannBody (y k))
      (fun k => grassmannSoul (y k)) = 0 :=
  taylorTermGrassmann_beyond_q n hn f _ _ (fun k => grassmannSoul_hasNoConstant' (y k))

/-! ## Constant Function Property -/

/-- The Taylor expansion of a constant function gives the constant as scalar. -/
theorem smoothTaylorGrassmann_const {p q : ℕ} (c : ℝ)
    (y : Fin p → FiniteGrassmannCarrier q) :
    smoothTaylorGrassmann (⟨fun _ => c, contDiff_const⟩ : SmoothFunction p) y =
    grassmannScalar (q := q) c := by
  simp only [smoothTaylorGrassmann]
  rw [Finset.sum_eq_single 0]
  · exact taylorTermGrassmann_zero _ _ _
  · -- All higher terms vanish: iterated derivatives of constants are zero
    intro n _ hn
    simp only [taylorTermGrassmann]
    apply Finset.sum_eq_zero
    intro dirs _
    have hderiv_zero : (iteratedPartialDeriv (List.ofFn dirs)
        (⟨fun _ => c, contDiff_const⟩ : SmoothFunction p)).toFun
        (fun k => grassmannBody (y k)) = 0 := by
      have hne : List.ofFn dirs ≠ [] := by
        intro h
        have : (List.ofFn dirs).length = n := List.length_ofFn
        rw [h, List.length_nil] at this
        exact hn this.symm
      have hconst := iteratedPartialDeriv_const c (List.ofFn dirs) hne
      rw [hconst]
    rw [hderiv_zero, mul_zero, zero_smul]
  · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h

/-! ## Body Extraction

The body (∅ component) of the Taylor expansion equals the function
evaluated at the body points of the inputs. Higher-order terms vanish
because they involve products of soul elements (which have no constant term). -/

/-- Evaluation at ∅ commutes with Finset.sum on FiniteGrassmannCarrier.
    This is needed because FiniteGrassmannCarrier has custom Add (not Pi.instAdd),
    so Finset.sum_apply from Mathlib doesn't directly match. -/
private theorem sum_eval_empty {q : ℕ} {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (g : ι → FiniteGrassmannCarrier q) :
    (s.sum g) ∅ = s.sum (fun n => g n ∅) := by
  induction s using Finset.induction_on with
  | empty => rfl
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha, add_apply]
    rw [ih]

/-- The body of the Taylor expansion equals f evaluated at body(y).

    grassmannBody (smoothTaylorGrassmann f y) = f.toFun (fun k => grassmannBody (y k))

    Only the n=0 term contributes to the body: T₀ = grassmannScalar (f(a)).
    For n ≥ 1, each Taylor term involves at least one soul factor (hasNoConstant),
    so its ∅ component vanishes. -/
theorem smoothTaylorGrassmann_body {p q : ℕ} (f : SmoothFunction p)
    (y : Fin p → FiniteGrassmannCarrier q) :
    grassmannBody (smoothTaylorGrassmann f y) = f.toFun (fun k => grassmannBody (y k)) := by
  show (smoothTaylorGrassmann f y) ∅ = f.toFun (fun k => (y k) ∅)
  show ((Finset.range (q + 1)).sum fun n => taylorTermGrassmann n f
    (fun k => grassmannBody (y k)) (fun k => grassmannSoul (y k))) ∅ =
    f.toFun (fun k => (y k) ∅)
  rw [sum_eval_empty, Finset.sum_eq_single 0]
  · -- n=0 term: taylorTermGrassmann 0 gives grassmannScalar (f.toFun a)
    rw [taylorTermGrassmann_zero]
    simp [grassmannScalar, grassmannBody]
  · -- n≥1 terms: each involves products of soul elements → body = 0
    intro n _ hn
    simp only [taylorTermGrassmann]
    rw [sum_eval_empty]
    apply Finset.sum_eq_zero; intro dirs _
    simp only [smul_apply]
    suffices h : (List.ofFn (fun i : Fin n => grassmannSoul (y (dirs i)))).prod ∅ = 0 by
      rw [h]; ring
    have hne : (List.ofFn (fun i : Fin n => grassmannSoul (y (dirs i)))) ≠ [] := by
      intro h
      have : (List.ofFn (fun i : Fin n => grassmannSoul (y (dirs i)))).length = n :=
        List.length_ofFn
      rw [h, List.length_nil] at this; exact hn this.symm
    exact List.prod_hasNoConstant _ (fun g hg => by
      rw [List.mem_ofFn] at hg; obtain ⟨i, rfl⟩ := hg
      exact grassmannSoul_hasNoConstant' (y (dirs i))) hne
  · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h

/-! ## Taylor Expansion Linearity

The Taylor expansion is linear in the function argument:
- `smoothTaylorGrassmann_add`: ∂ⁿ(f+g) = ∂ⁿf + ∂ⁿg
- `smoothTaylorGrassmann_smul`: ∂ⁿ(c·f) = c · ∂ⁿf

These are used for linearity of super function composition. -/

/-- Taylor expansion is additive in f. -/
theorem smoothTaylorGrassmann_add {p q : ℕ}
    (f g : SmoothFunction p) (y : Fin p → FiniteGrassmannCarrier q) :
    smoothTaylorGrassmann ⟨fun x => f x + g x, f.smooth.add g.smooth⟩ y =
    smoothTaylorGrassmann f y + smoothTaylorGrassmann g y := by
  simp only [smoothTaylorGrassmann]
  rw [← Finset.sum_add_distrib]
  congr 1
  ext n
  simp only [taylorTermGrassmann]
  rw [← Finset.sum_add_distrib]
  congr 1
  ext dirs
  rw [iteratedPartialDeriv_add_apply, mul_add, add_smul]

/-- Taylor expansion commutes with scalar multiplication. -/
theorem smoothTaylorGrassmann_smul {p q : ℕ}
    (c : ℝ) (f : SmoothFunction p) (y : Fin p → FiniteGrassmannCarrier q) :
    smoothTaylorGrassmann ⟨fun x => c * f x, contDiff_const.mul f.smooth⟩ y =
    c • smoothTaylorGrassmann f y := by
  simp only [smoothTaylorGrassmann]
  rw [Finset.smul_sum]
  congr 1
  ext n
  simp only [taylorTermGrassmann]
  rw [Finset.smul_sum]
  congr 1
  ext dirs
  rw [iteratedPartialDeriv_smul_apply]
  funext I
  simp only [smul_apply]
  ring

/-! ## Connection to Composition

The Taylor expansion is the key building block for super function composition.
Given a coordinate change φ = (y, η) on ℝ^{p|q}, the composition f ∘ φ at a
body point x evaluates as:

  (f ∘ φ)(x) = Σ_I f_I(y(x,θ)) · η(x,θ)^I

where f_I(y(x,θ)) = smoothTaylorGrassmann f_I (y evaluated at x).

See `SuperCompose.lean` (Phase 2) for the full composition infrastructure. -/

end Supermanifolds
