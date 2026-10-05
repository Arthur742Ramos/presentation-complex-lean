module

public import FiniteGraphFreeGroup.Realization
public import Mathlib.CategoryTheory.SingleObj

@[expose] public section

/-!
# The arbitrary bouquet and its canonical free-group generators

The vertex is universe-correct even when the generator type is not small.
The topology is exactly the weak endpoint quotient in `graphRealization`.
-/

open CategoryTheory Quiver

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
universe u
namespace PresentationComplex

/-- The single vertex, in the same universe as the edge labels. -/
def Vertex (S : Type u) : Type u := PUnit

instance (S : Type u) : Inhabited (Vertex S) := ⟨PUnit.unit⟩
instance (S : Type u) : Subsingleton (Vertex S) := inferInstanceAs (Subsingleton PUnit)

instance (S : Type u) : Quiver.{u} (Vertex S) where
  Hom _ _ := S

instance (S : Type u) : FiniteGraphFreeGroup.WeaklyConnected (Vertex S) where
  path a b := by
    have h : a = b := Subsingleton.elim _ _
    subst b
    exact ⟨Quiver.Path.nil⟩

/-- The total edge indices of the one-vertex graph are exactly its labels. -/
def edgeIndexEquiv (S : Type u) : Quiver.Total (Vertex S) ≃ S where
  toFun e := e.hom
  invFun s := ⟨default, default, s⟩
  left_inv := by
    rintro ⟨a, b, s⟩
    cases a
    cases b
    rfl
  right_inv _ := rfl

/-- The actual endpoint quotient of one vertex and one interval for each label. -/
abbrev Bouquet (S : Type u) := FiniteGraphFreeGroup.graphRealization (Vertex S)

/-- The image of the unique vertex in the endpoint quotient. -/
def base (S : Type u) : Bouquet S := FiniteGraphFreeGroup.graphVertex (default : Vertex S)

/-- The actual forward traversal of the interval indexed by `s`. -/
def edgeLoop {S : Type u} (s : S) : Path (base S) (base S) :=
  FiniteGraphFreeGroup.graphRealizationForwardPath
    (show (default : Vertex S) ⟶ (default : Vertex S) from s)

instance (S : Type u) : PathConnectedSpace (Bouquet S) :=
  FiniteGraphFreeGroup.graphRealization_pathConnected (default : Vertex S)

end PresentationComplex
