module

public import PresentationComplex.Characteristic
public import Mathlib.Topology.UnitInterval

@[expose] public section

/-! Mathlib's maximum-norm one-cell is explicitly parameterized by the unit interval. -/
noncomputable section
open Set Metric unitInterval
namespace PresentationComplex

theorem norm_finOne (x : Fin 1 → ℝ) : ‖x‖ = |x 0| := by
  have hc : x = fun _ => x 0 := funext fun i => congrArg x (Subsingleton.elim i 0)
  rw [hc,pi_norm_const,Real.norm_eq_abs]

/-- The actual closed one-cell chart, with both boundary points preserved. -/
def closedIntervalChart : ClosedCellDomain 1 ≃ₜ I where
  toFun x := ⟨(x.val 0 + 1) / 2, by
    have hx : |x.val 0| ≤ 1 := by
      simpa only [mem_closedBall,dist_zero_right,norm_finOne] using x.property
    have hb := abs_le.mp hx
    constructor <;> linarith⟩
  invFun t := ⟨fun _ => 2*t.val-1, by
    rw [mem_closedBall,dist_zero_right,norm_finOne]
    apply abs_le.mpr
    constructor <;> linarith [t.property.1,t.property.2]⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp only
    ring
  right_inv t := by
    apply Subtype.ext
    simp only
    ring
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (((continuous_apply 0).comp continuous_subtype_val).add continuous_const).div_const 2
  continuous_invFun := by fun_prop

/-- The corresponding open-cell homeomorphism onto (0,1). -/
def openIntervalChart : OpenCellDomain 1 ≃ₜ Ioo (0 : I) 1 where
  toFun x := ⟨closedIntervalChart ⟨x.val,ball_subset_closedBall x.property⟩,by
    have hx : |x.val 0| < 1 := by
      simpa only [mem_ball,dist_zero_right,norm_finOne] using x.property
    have hb := abs_lt.mp hx
    constructor
    · change (0 : ℝ) < (x.val 0 + 1) / 2
      linarith
    · change (x.val 0 + 1) / 2 < (1 : ℝ)
      linarith⟩
  invFun t := ⟨fun _ => 2*t.val.val-1,by
    rw [mem_ball,dist_zero_right,norm_finOne]
    apply abs_lt.mpr
    have ht0 : (0 : ℝ) < t.val.val := t.property.1
    have ht1 : t.val.val < (1 : ℝ) := t.property.2
    constructor <;> linarith⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    dsimp [closedIntervalChart]
    ring
  right_inv t := by
    apply Subtype.ext
    apply Subtype.ext
    dsimp [closedIntervalChart]
    ring
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact closedIntervalChart.continuous.comp (continuous_subtype_val.subtype_mk _)
  continuous_invFun := by fun_prop

/-- The boundary of the closed 1-cell maps precisely to the two interval endpoints. -/
theorem closedIntervalChart_boundary (x : ClosedCellDomain 1) (hx : ‖x.val‖ = 1) :
    closedIntervalChart x = 0 ∨ closedIntervalChart x = 1 := by
  rw [norm_finOne] at hx
  have h : x.val 0 = -1 ∨ x.val 0 = 1 := by
    rcases abs_eq_abs.mp (show |x.val 0| = |(1 : ℝ)| from by simpa using hx) with h | h
    · exact Or.inr h
    · exact Or.inl h
  rcases h with h | h
  · left
    apply Subtype.ext
    simp [closedIntervalChart,h]
  · right
    apply Subtype.ext
    simp [closedIntervalChart,h]

end PresentationComplex
