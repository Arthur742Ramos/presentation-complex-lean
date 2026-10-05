module

public import PresentationComplex.RelatorConstruction
public import PresentationComplex.WordLoops
public import PresentationComplex.LoopCircle
public import PresentationComplex.Connected
public import CellAttachment.Statement

@[expose] public section

/-! Genuine circle maps and disk adjunction for arbitrary presentations. -/
noncomputable section
open Set Path.Homotopic
universe u v
namespace PresentationComplex
variable {S : Type u} {R : Type v}

private theorem based_attaching_class {X : Type*} [TopologicalSpace X] {x₀ : X}
    (f : C(Circle,X)) (h : f 1 = x₀) (p : Path x₀ x₀)
    (hp : ∀ t, f (CellAttachment.circleGenerator t) = p t) :
    Path.Homotopic.Quotient.mk (((Path.refl x₀).cast rfl h).trans
      (((CellAttachment.circleGenerator.map f.continuous)).trans
        ((Path.refl x₀).cast rfl h).symm)) = Path.Homotopic.Quotient.mk p := by
  cases h
  have heq : CellAttachment.circleGenerator.map f.continuous = p := by
    apply Path.ext
    funext t
    exact hp t
  rw [heq]
  simp only [Path.cast_rfl_rfl,Path.refl_symm,Path.Homotopic.Quotient.mk_trans,Path.Homotopic.Quotient.mk_refl,
    Path.Homotopic.Quotient.refl_trans,Path.Homotopic.Quotient.trans_refl]

/-- Exact relator compatibility, including constant anchors rather than an assumed oracle. -/
theorem attachingLoopClass_eq (r : R → FreeGroup S) (i : R) :
    CellAttachment.attachingLoopClass (relatorMap r) (base S) (anchorPath r) i =
      freeGroupEquiv S (r i) := by
  rw [freeGroupEquiv_relatorLoop]
  exact based_attaching_class (relatorMap r i) (relatorMap_one r i) (relatorLoop (r i))
    (loopCircleMap_generator _)

end PresentationComplex
