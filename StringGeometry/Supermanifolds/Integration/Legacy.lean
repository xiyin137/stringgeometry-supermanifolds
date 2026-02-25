import StringGeometry.Supermanifolds.BerezinIntegration

/-!
# Legacy Integration Compatibility

This file provides deprecated aliases for legacy declarations that were moved
to `*_legacy` names in `BerezinIntegration.lean`.

New code should use:
- `Integration/Pullback.lean` (`IntegralForm.pullbackProper`)
- `Integration/StokesTheorem.lean`
- `Integration/GlobalStokes.lean`
-/

namespace Supermanifolds

noncomputable abbrev IntegralForm.pullback {p q : ℕ}
    (φ : SuperCoordChange p q) (ω : IntegralForm p q) : IntegralForm p q :=
  IntegralForm.pullbackLegacy φ ω

theorem berezin_change_of_variables_formula {p q : ℕ}
    (U V : Set (Fin p → ℝ))
    (φ : SuperCoordChange p q)
    (hDiffeo : φ.IsDiffeoOn U V)
    (ω : IntegralForm p q)
    (hPullbackBody : ∀ x,
      berezinIntegralOdd (IntegralForm.pullback φ ω).coefficient x =
      (berezinIntegralOdd ω.coefficient).toFun (φ.bodyMap x) *
        (fderiv ℝ φ.bodyMap x).det)
    (bodyIntegral : SmoothFunction p → Set (Fin p → ℝ) → ℝ)
    (hChangeOfVar : BodyIntegral.SatisfiesChangeOfVar p bodyIntegral) :
    localBerezinIntegral U (IntegralForm.pullback φ ω) bodyIntegral =
    localBerezinIntegral V ω bodyIntegral :=
  berezin_change_of_variables_formula_legacy U V φ hDiffeo ω hPullbackBody bodyIntegral hChangeOfVar

theorem super_stokes {p q : ℕ} (_hp : 0 < p)
    (U : Set (Fin p → ℝ))
    (_hU_compact : IsCompact U)
    (_hU_open : IsOpen (interior U))
    (bdryU : Set (Fin (p - 1) → ℝ))
    (_ω : IntegralForm p q)
    (bodyIntegral : SmoothFunction p → Set (Fin p → ℝ) → ℝ)
    (boundaryIntegral : SmoothFunction (p - 1) → Set (Fin (p - 1) → ℝ) → ℝ)
    (restrict : SmoothFunction p → SmoothFunction (p - 1))
    (dω : IntegralForm p q)
    (hStokesBody :
        bodyIntegral (berezinIntegralOdd dω.coefficient) U =
        boundaryIntegral (restrict (berezinIntegralOdd _ω.coefficient)) bdryU) :
    localBerezinIntegral U dω bodyIntegral =
    boundaryIntegral (restrict (berezinIntegralOdd _ω.coefficient)) bdryU :=
  super_stokes_legacy _hp U _hU_compact _hU_open bdryU _ω bodyIntegral boundaryIntegral
    restrict dω hStokesBody

theorem super_divergence_theorem {p q : ℕ}
    (X : SuperVectorField p q Parity.even)
    (_U : Set (Fin p → ℝ))
    (_bdryU : Set (Fin (p - 1) → ℝ))
    (bodyIntegral : SmoothFunction p → Set (Fin p → ℝ) → ℝ)
    (_boundaryIntegral : SmoothFunction (p - 1) → Set (Fin (p - 1) → ℝ) → ℝ) :
    bodyIntegral (berezinIntegralOdd (superDivergence X)) _U =
    bodyIntegral (berezinIntegralOdd (superDivergence X)) _U :=
  super_divergence_theorem_legacy X _U _bdryU bodyIntegral _boundaryIntegral

attribute [deprecated IntegralForm.pullbackLegacy (since := "2026-02-25")] IntegralForm.pullback
attribute [deprecated berezin_change_of_variables_formula_legacy (since := "2026-02-25")] berezin_change_of_variables_formula
attribute [deprecated super_stokes_legacy (since := "2026-02-25")] super_stokes
attribute [deprecated super_divergence_theorem_legacy (since := "2026-02-25")] super_divergence_theorem

end Supermanifolds
