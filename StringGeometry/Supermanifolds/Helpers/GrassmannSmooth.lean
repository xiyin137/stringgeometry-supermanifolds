/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license.
-/
import StringGeometry.Supermanifolds.Helpers.FiniteGrassmann

/-!
# Smoothness of Grassmann-Valued Functions

Provides the `GrassmannSmooth` predicate and closure properties for
functions `(Fin p → ℝ) → FiniteGrassmannCarrier q` whose coefficients
are individually smooth (ContDiff ℝ ⊤).

## Main Definition

* `GrassmannSmooth` - all Grassmann coefficients are smooth

## Main Theorems

* `GrassmannSmooth.mul` - product of smooth Grassmann functions has smooth coefficients
* `GrassmannSmooth.pow` - power of smooth Grassmann function has smooth coefficients
* `GrassmannSmooth.sum` - finite sum of smooth Grassmann functions has smooth coefficients

These enable mechanical smoothness proofs for composed/pullback super domain functions.
-/

noncomputable section

namespace Supermanifolds.Helpers

open FiniteGrassmannCarrier

/-- A Grassmann-valued function has smooth coefficients:
    every component `J : Finset (Fin q)` of the output is smooth in `x`. -/
def GrassmannSmooth {p q : ℕ} (f : (Fin p → ℝ) → FiniteGrassmannCarrier q) : Prop :=
  ∀ J : Finset (Fin q), ContDiff ℝ ⊤ (fun x => f x J)

namespace GrassmannSmooth

variable {p q : ℕ}

/-- A constant Grassmann element has smooth coefficients. -/
theorem const (c : FiniteGrassmannCarrier q) :
    GrassmannSmooth (fun (_ : Fin p → ℝ) => c) :=
  fun _ => contDiff_const

/-- Zero has smooth coefficients. -/
theorem zero : GrassmannSmooth (fun (_ : Fin p → ℝ) => (0 : FiniteGrassmannCarrier q)) :=
  const 0

/-- One has smooth coefficients. -/
theorem one : GrassmannSmooth (fun (_ : Fin p → ℝ) => (1 : FiniteGrassmannCarrier q)) :=
  const 1

/-- Addition preserves smoothness of coefficients. -/
theorem add {f g : (Fin p → ℝ) → FiniteGrassmannCarrier q}
    (hf : GrassmannSmooth f) (hg : GrassmannSmooth g) :
    GrassmannSmooth (fun x => f x + g x) := by
  intro J
  show ContDiff ℝ ⊤ (fun x => f x J + g x J)
  exact (hf J).add (hg J)

/-- Negation preserves smoothness of coefficients. -/
theorem neg {f : (Fin p → ℝ) → FiniteGrassmannCarrier q}
    (hf : GrassmannSmooth f) :
    GrassmannSmooth (fun x => -f x) := by
  intro J
  show ContDiff ℝ ⊤ (fun x => -(f x J))
  exact (hf J).neg

/-- Subtraction preserves smoothness of coefficients. -/
theorem sub {f g : (Fin p → ℝ) → FiniteGrassmannCarrier q}
    (hf : GrassmannSmooth f) (hg : GrassmannSmooth g) :
    GrassmannSmooth (fun x => f x - g x) := by
  intro J
  show ContDiff ℝ ⊤ (fun x => f x J - g x J)
  exact (hf J).sub (hg J)

/-- Constant scalar multiplication preserves smoothness. -/
theorem smul_const (c : ℝ) {f : (Fin p → ℝ) → FiniteGrassmannCarrier q}
    (hf : GrassmannSmooth f) :
    GrassmannSmooth (fun x => c • f x) := by
  intro J
  show ContDiff ℝ ⊤ (fun x => c * f x J)
  exact contDiff_const.mul (hf J)

/-- Scalar multiplication by a smooth function preserves smoothness. -/
theorem smul_fun {c : (Fin p → ℝ) → ℝ} {f : (Fin p → ℝ) → FiniteGrassmannCarrier q}
    (hc : ContDiff ℝ ⊤ c) (hf : GrassmannSmooth f) :
    GrassmannSmooth (fun x => c x • f x) := by
  intro J
  show ContDiff ℝ ⊤ (fun x => c x * f x J)
  exact hc.mul (hf J)

/-- Grassmann multiplication preserves smoothness of coefficients.

    Key lemma: since `(f * g) K = Σ_{I∪J=K, I∩J=∅} sign(I,J) * f_I * g_J`,
    and each summand is a constant times a product of smooth functions,
    the result is smooth. -/
theorem mul {f g : (Fin p → ℝ) → FiniteGrassmannCarrier q}
    (hf : GrassmannSmooth f) (hg : GrassmannSmooth g) :
    GrassmannSmooth (fun x => f x * g x) := by
  intro K
  show ContDiff ℝ ⊤ (fun x => (f x * g x) K)
  simp only [mul_apply]
  -- Goal: ContDiff ℝ ⊤ (fun x => Σ I, Σ J, if I∪J=K ∧ I∩J=∅ then sign*f_I*g_J else 0)
  apply ContDiff.sum
  intro I _
  apply ContDiff.sum
  intro J _
  by_cases h : I ∪ J = K ∧ I ∩ J = ∅
  · simp only [if_pos h]
    exact (contDiff_const.mul (hf I)).mul (hg J)
  · simp only [if_neg h]
    exact contDiff_const

/-- Power preserves smoothness (by induction). -/
theorem pow {f : (Fin p → ℝ) → FiniteGrassmannCarrier q}
    (hf : GrassmannSmooth f) (n : ℕ) :
    GrassmannSmooth (fun x => f x ^ n) := by
  induction n with
  | zero =>
    show GrassmannSmooth (fun x => (1 : FiniteGrassmannCarrier q))
    exact one
  | succ m ih =>
    show GrassmannSmooth (fun x => f x ^ m * f x)
    exact ih.mul hf

/-- Finite sum of GrassmannSmooth functions is GrassmannSmooth. -/
theorem finset_sum {ι : Type*} {s : Finset ι}
    {f : ι → (Fin p → ℝ) → FiniteGrassmannCarrier q}
    (hf : ∀ i ∈ s, GrassmannSmooth (f i)) :
    GrassmannSmooth (fun x => s.sum (fun i => f i x)) := by
  intro J
  show ContDiff ℝ ⊤ (fun x => s.sum (fun i => f i x) J)
  -- (Σ_i f_i x) J = Σ_i (f_i x J) by Finset.sum_apply
  have : (fun x => (s.sum (fun i => f i x)) J) =
         (fun x => s.sum (fun i => f i x J)) := by
    funext x; exact Finset.sum_apply _ _ _
  rw [this]
  exact ContDiff.sum (fun i hi => hf i hi J)

/-- Finite product of GrassmannSmooth functions is GrassmannSmooth. -/
theorem list_prod {fs : List ((Fin p → ℝ) → FiniteGrassmannCarrier q)}
    (hfs : ∀ f ∈ fs, GrassmannSmooth f) :
    GrassmannSmooth (fun x => fs.map (· x) |>.prod) := by
  induction fs with
  | nil =>
    show GrassmannSmooth (fun _ => 1)
    exact one
  | cons f rest ih =>
    simp only [List.map_cons, List.prod_cons]
    have hf_mem : f ∈ f :: rest := .head rest
    have ih_hyp : ∀ g ∈ rest, GrassmannSmooth g :=
      fun g hg => hfs g (List.mem_cons_of_mem f hg)
    exact (hfs f hf_mem).mul (ih ih_hyp)

/-- Product of GrassmannSmooth functions indexed by List.ofFn. -/
theorem ofFn_prod {n : ℕ} {f : Fin n → (Fin p → ℝ) → FiniteGrassmannCarrier q}
    (hf : ∀ i, GrassmannSmooth (f i)) :
    GrassmannSmooth (fun x => (List.ofFn (fun i => f i x)).prod) := by
  suffices h : (fun x => (List.ofFn (fun i => f i x)).prod) =
      (fun x => ((List.ofFn f).map (· x)).prod) by
    rw [h]; apply list_prod
    intro g hg
    simp only [List.mem_ofFn] at hg
    obtain ⟨i, rfl⟩ := hg
    exact hf i
  funext x; congr 1
  show List.ofFn (fun i => f i x) = (List.ofFn f).map (· x)
  rw [List.map_ofFn]; rfl

/-- Product of GrassmannSmooth functions mapped from a list. -/
theorem map_prod {ι : Type*} (as : List ι)
    {f : ι → (Fin p → ℝ) → FiniteGrassmannCarrier q}
    (hf : ∀ a ∈ as, GrassmannSmooth (f a)) :
    GrassmannSmooth (fun x => (as.map (fun a => f a x)).prod) := by
  suffices h : (fun x => (as.map (fun a => f a x)).prod) =
      (fun x => ((as.map f).map (· x)).prod) by
    rw [h]; apply list_prod
    intro g hg
    rw [List.mem_map] at hg
    obtain ⟨a, ha, rfl⟩ := hg
    exact hf a ha
  funext x; congr 1; rw [List.map_map]; rfl

/-- GrassmannSmooth is preserved under applying a smooth body function
    (composition of a smooth ℝ-valued function with the coefficients). -/
theorem of_coefficients {S : (Fin p → ℝ) → Finset (Fin q) → ℝ}
    (hS : ∀ J, ContDiff ℝ ⊤ (fun x => S x J)) :
    GrassmannSmooth (fun x J => S x J) :=
  hS

end GrassmannSmooth

end Supermanifolds.Helpers