module

public import PresentationComplex.WordLoopConstruction
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

/-- Every relator's finite word loop descends continuously to the actual circle. -/
def relatorMap (r : R → FreeGroup S) : R → C(Circle, Bouquet S) :=
  fun i => loopCircleMap (relatorLoop (r i))

@[simp] theorem relatorMap_one (r : R → FreeGroup S) (i : R) :
    relatorMap r i 1 = base S := loopCircleMap_one _

/-- The genuine boundary-generated quotient of the bouquet and indexed closed disks. -/
abbrev Space (r : R → FreeGroup S) := CellAttachment.Space (relatorMap r)

/-- The actual continuous bouquet inclusion. -/
def inclusion (r : R → FreeGroup S) : C(Bouquet S, Space r) :=
  CellAttachment.inclusion (relatorMap r)

/-- The actual image of the bouquet vertex. -/
def point (r : R → FreeGroup S) : Space r := inclusion r (base S)

instance (r : R → FreeGroup S) : PathConnectedSpace (Space r) :=
  attachment_pathConnected (relatorMap r) (base S)

/-- The constant based anchoring path to the attaching circle's based image. -/
def anchorPath (r : R → FreeGroup S) (i : R) :
    Path (base S) (relatorMap r i 1) :=
  (Path.refl (base S)).cast rfl (relatorMap_one r i)

/-- Each individual disk boundary lies in a finite bouquet subgraph. -/
theorem relatorMap_range_subset (r : R → FreeGroup S) (i : R) :
    Set.range (relatorMap r i) ⊆ wordCarrier (relatorWord (r i)) := by
  classical
  exact (loopCircleMap_range_subset (relatorLoop (r i))).trans
    (wordLoop_range_subset (relatorWord (r i)))

/-- The exact subgroup of the free group imposed by the presentation. -/
def relatorNormalClosure (r : R → FreeGroup S) : Subgroup (FreeGroup S) :=
  Subgroup.normalClosure (Set.range r)

instance relatorNormalClosure_normal (r : R → FreeGroup S) :
    (relatorNormalClosure r).Normal := by
  unfold relatorNormalClosure
  infer_instance

end PresentationComplex
