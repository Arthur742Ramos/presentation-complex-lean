module

public import CellAttachment.CircleGenerator

@[expose] public section

/-! Descending an actual based loop to the actual complex circle. -/
noncomputable section
open unitInterval
open Set
universe u
namespace PresentationComplex
variable {X : Type u} [TopologicalSpace X] {x₀ : X}

private def circleFromPeriod : AddCircle (1 : ℝ) ≃ₜ Circle :=
  AddCircle.homeomorphCircle one_ne_zero

/-- The endpoint-identified interval descent, transported to the actual complex unit circle. -/
def loopCircleMap (p : Path x₀ x₀) : C(Circle, X) where
  toFun z := AddCircle.liftIco (1 : ℝ) 0 p.extend (circleFromPeriod.symm z)
  continuous_toFun :=
    (AddCircle.liftIco_zero_continuous (by simp) p.continuous_extend.continuousOn).comp
      circleFromPeriod.symm.continuous

private theorem circleFromPeriod_generator (t : I) :
    circleFromPeriod (t.val : AddCircle (1 : ℝ)) = CellAttachment.circleGenerator t := by
  rw [circleFromPeriod, AddCircle.homeomorphCircle_apply, AddCircle.toCircle_apply_mk,
    CellAttachment.circleGenerator_apply]
  congr 1
  ring

/-- Pointwise compatibility with the actual unit-speed generating circle loop. -/
theorem loopCircleMap_generator (p : Path x₀ x₀) (t : I) :
    loopCircleMap p (CellAttachment.circleGenerator t) = p t := by
  rw [← circleFromPeriod_generator]
  change AddCircle.liftIco (1 : ℝ) 0 p.extend
    (circleFromPeriod.symm (circleFromPeriod (t.val : AddCircle (1 : ℝ)))) = p t
  rw [circleFromPeriod.symm_apply_apply]
  by_cases ht : t.val < 1
  · rw [AddCircle.liftIco_zero_coe_apply ⟨t.property.1,ht⟩]
    exact p.extend_apply t.property
  · have heq : t = 1 := Subtype.ext (le_antisymm t.property.2 (le_of_not_gt ht))
    subst t
    change AddCircle.liftIco (1 : ℝ) 0 p.extend ((1 : ℝ) : AddCircle (1 : ℝ)) = p 1
    rw [AddCircle.coe_period]
    rw [← AddCircle.coe_zero, AddCircle.liftIco_zero_coe_apply (by norm_num)]
    simp

@[simp] theorem loopCircleMap_one (p : Path x₀ x₀) : loopCircleMap p 1 = x₀ := by
  simpa only [Path.source] using loopCircleMap_generator p 0

end PresentationComplex

namespace PresentationComplex
open Set
variable {X : Type u} [TopologicalSpace X] {x₀ : X}

/-- Descending to the circle does not enlarge a loop's image. -/
theorem loopCircleMap_range_subset (p : Path x₀ x₀) :
    Set.range (loopCircleMap p) ⊆ Set.range p := by
  rintro _ ⟨z,rfl⟩
  let t := AddCircle.equivIco (1 : ℝ) 0 (circleFromPeriod.symm z)
  have ht : t.val ∈ Set.Icc (0 : ℝ) 1 := by
    exact ⟨t.property.1, by simpa using t.property.2.le⟩
  refine ⟨⟨t.val,ht⟩,?_⟩
  exact (p.extend_apply ht).symm

end PresentationComplex
