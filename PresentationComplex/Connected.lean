module

public import CellAttachment.Adjunction
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Topology.Connected.PathConnected

@[expose] public section

/-! Genuine path connectedness of arbitrary disk adjunctions. -/
noncomputable section
open Set Metric
namespace PresentationComplex
universe u v
variable {X : Type u} [TopologicalSpace X] {R : Type v}

theorem disk_pathConnected : PathConnectedSpace CellAttachment.Disk := by
  have h : IsPathConnected (closedBall (0 : ℂ) 1) :=
    (convex_closedBall (0 : ℂ) 1).isPathConnected ⟨0, by simp⟩
  have hd : (closedBall (0 : ℂ) 1) = {z : ℂ | ‖z‖ ≤ 1} := by
    ext z
    simp only [mem_closedBall, dist_zero_right, mem_setOf_eq]
  rw [hd] at h
  exact isPathConnected_iff_pathConnectedSpace.mp h

/-- Attaching any family of actual disks to a nonempty path-connected base
preserves actual continuous-path connectedness, even for empty/duplicate families. -/
theorem attachment_pathConnected (f : R → C(Circle, X)) (x₀ : X)
    [PathConnectedSpace X] : PathConnectedSpace (CellAttachment.Space f) := by
  letI : PathConnectedSpace CellAttachment.Disk := disk_pathConnected
  have hjoin : ∀ y : CellAttachment.Space f,
      Joined y (CellAttachment.inclusion f x₀) := by
    intro y
    obtain ⟨a,rfl⟩ := (CellAttachment.quotientMap_isQuotientMap f).surjective y
    cases a with
    | inl x =>
      exact ⟨(PathConnectedSpace.somePath x x₀).map
        (CellAttachment.inclusion f).continuous⟩
    | inr w =>
      rcases w with ⟨i,z⟩
      have p : Joined (CellAttachment.characteristic f i z)
          (CellAttachment.inclusion f (f i 1)) := by
        rw [← CellAttachment.characteristic_boundary f i 1]
        exact ⟨(PathConnectedSpace.somePath z (CellAttachment.boundaryInclusion 1)).map
          (CellAttachment.characteristic f i).continuous⟩
      exact p.trans ⟨(PathConnectedSpace.somePath (f i 1) x₀).map
        (CellAttachment.inclusion f).continuous⟩
  exact ⟨⟨CellAttachment.inclusion f x₀⟩, fun x y => (hjoin x).trans (hjoin y).symm⟩

end PresentationComplex
