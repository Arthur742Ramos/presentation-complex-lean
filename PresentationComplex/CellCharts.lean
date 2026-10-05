import Mathlib.Analysis.Convex.GaugeRescale
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.CWComplex.Classical.Basic

/-!
# The genuine square-to-disk bridge

Mathlib's classical CW characteristic cells use the maximum norm on `Fin n → ℝ`.
The adjunction theorem uses a Euclidean complex disk. We construct an ambient
homeomorphism carrying the open square, closed square, and boundary square to the
corresponding complex disk subsets. This is proved geometric data, not a CW oracle.
-/
noncomputable section
open Set Metric Bornology
namespace PresentationComplex

/-- The standard real-linear coordinates on the complex plane. -/
def planeCoordinates : (Fin 2 → ℝ) ≃L[ℝ] ℂ :=
  (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).trans Complex.equivRealProdCLM.symm

private def square : Set ℂ :=
  planeCoordinates '' (closedBall (0 : Fin 2 → ℝ) 1)

private theorem square_compact : IsCompact square :=
  (isCompact_closedBall (0 : Fin 2 → ℝ) 1).image planeCoordinates.continuous

private theorem square_interior : interior square =
    planeCoordinates '' (ball (0 : Fin 2 → ℝ) 1) := by
  change interior (planeCoordinates.toHomeomorph '' closedBall 0 1) =
    planeCoordinates.toHomeomorph '' ball 0 1
  rw [← planeCoordinates.toHomeomorph.image_interior]
  rw [interior_closedBall _ (by norm_num : (1 : ℝ) ≠ 0)]

private theorem square_frontier : frontier square =
    planeCoordinates '' (sphere (0 : Fin 2 → ℝ) 1) := by
  change frontier (planeCoordinates.toHomeomorph '' closedBall 0 1) =
    planeCoordinates.toHomeomorph '' sphere 0 1
  rw [← planeCoordinates.toHomeomorph.image_frontier]
  rw [frontier_closedBall _ (by norm_num : (1 : ℝ) ≠ 0)]

private theorem rescale_exists : ∃ h : ℂ ≃ₜ ℂ,
    h '' interior square = ball 0 1 ∧
    h '' closure square = closedBall 0 1 ∧
    h '' frontier square = sphere 0 1 := by
  apply exists_homeomorph_image_interior_closure_frontier_eq_unitBall
  · exact (convex_closedBall (0 : Fin 2 → ℝ) 1).linear_image planeCoordinates.toLinearMap
  · rw [square_interior]
    exact (show (ball (0 : Fin 2 → ℝ) 1).Nonempty from ⟨0, by simp⟩).image _
  · exact square_compact.isBounded

/-- An ambient square-to-disk homeomorphism respecting the whole cell filtration. -/
def squareToComplex : (Fin 2 → ℝ) ≃ₜ ℂ :=
  planeCoordinates.toHomeomorph.trans (Classical.choose rescale_exists)

theorem squareToComplex_ball : squareToComplex '' ball 0 1 = ball 0 1 := by
  change ((Classical.choose rescale_exists : ℂ ≃ₜ ℂ) ∘ (planeCoordinates : (Fin 2 → ℝ) → ℂ)) '' ball 0 1 = _
  rw [image_comp, ← square_interior]
  exact (Classical.choose_spec rescale_exists).1

theorem squareToComplex_closedBall : squareToComplex '' closedBall 0 1 = closedBall 0 1 := by
  change ((Classical.choose rescale_exists : ℂ ≃ₜ ℂ) ∘ (planeCoordinates : (Fin 2 → ℝ) → ℂ)) '' closedBall 0 1 = _
  rw [image_comp, ← square]
  exact (congrArg (fun A : Set ℂ => (Classical.choose rescale_exists : ℂ ≃ₜ ℂ) '' A)
    square_compact.isClosed.closure_eq.symm).trans (Classical.choose_spec rescale_exists).2.1

theorem squareToComplex_sphere : squareToComplex '' sphere 0 1 = sphere 0 1 := by
  change ((Classical.choose rescale_exists : ℂ ≃ₜ ℂ) ∘ (planeCoordinates : (Fin 2 → ℝ) → ℂ)) '' sphere 0 1 = _
  rw [image_comp, ← square_frontier]
  exact (Classical.choose_spec rescale_exists).2.2

/-- The actual closed-cell chart from Mathlib's maximum-norm 2-cell to the complex disk. -/
def closedDiskChart : (closedBall (0 : Fin 2 → ℝ) 1) ≃ₜ
    {z : ℂ // ‖z‖ ≤ 1} :=
  (squareToComplex.image (closedBall 0 1)).trans
    (Homeomorph.setCongr (by
      rw [squareToComplex_closedBall]
      ext z
      change dist z 0 ≤ 1 ↔ ‖z‖ ≤ 1
      simp only [dist_zero_right]))

/-- The actual open-cell chart, not merely a continuous parameterization. -/
def openDiskChart : (ball (0 : Fin 2 → ℝ) 1) ≃ₜ
    {z : ℂ // ‖z‖ < 1} :=
  (squareToComplex.image (ball 0 1)).trans
    (Homeomorph.setCongr (by
      rw [squareToComplex_ball]
      ext z
      change dist z 0 < 1 ↔ ‖z‖ < 1
      simp only [dist_zero_right]))

end PresentationComplex
