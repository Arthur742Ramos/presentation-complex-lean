module

public import PresentationComplex.BouquetConstruction
public import FiniteGraphFreeGroup.TopologicalComparison
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

abbrev bouquetVertexGroup (S : Type u) :=
  FiniteGraphFreeGroup.graphFundamentalGroup (default : Vertex S)

/-- The actual edge in the free groupoid, regarded as an endomorphism. -/
def edgeEnd {S : Type u} (s : S) : bouquetVertexGroup S :=
  (Quiver.FreeGroupoid.of (Vertex S)).map
    (show (default : Vertex S) ⟶ (default : Vertex S) from s)

/-- The label map into the one-object groupoid of the free group. -/
def labelPrefunctor (S : Type u) : Vertex S ⥤q CategoryTheory.SingleObj (FreeGroup S) where
  obj _ := CategoryTheory.SingleObj.star _
  map s := FreeGroup.of s

/-- Its unique extension to the free groupoid. -/
def labelFunctor (S : Type u) : Quiver.FreeGroupoid (Vertex S) ⥤ CategoryTheory.SingleObj (FreeGroup S) :=
  Quiver.FreeGroupoid.lift (labelPrefunctor S)

/-- Read a free-group word from a combinatorial loop. -/
def vertexGroupToFree (S : Type u) : bouquetVertexGroup S →* FreeGroup S :=
  (CategoryTheory.SingleObj.toEnd (FreeGroup S)).symm.toMonoidHom.comp
    ((labelFunctor S).mapEnd ((Quiver.FreeGroupoid.of (Vertex S)).obj default))

/-- Realize a free-group word as a combinatorial loop. -/
def freeToVertexGroup (S : Type u) : FreeGroup S →* bouquetVertexGroup S :=
  FreeGroup.lift edgeEnd

@[simp]
theorem vertexGroupToFree_edgeEnd {S : Type u} (s : S) :
    vertexGroupToFree S (edgeEnd s) = FreeGroup.of s := by
  have h := Prefunctor.congr_hom
    (Quiver.FreeGroupoid.lift_spec (labelPrefunctor S))
    (show (default : Vertex S) ⟶ (default : Vertex S) from s)
  exact h

@[simp]
theorem freeToVertexGroup_of {S : Type u} (s : S) :
    freeToVertexGroup S (FreeGroup.of s) = edgeEnd s :=
  FreeGroup.lift_apply_of

/-- The two universal-property maps are mutually inverse on the free group. -/
theorem vertexGroupToFree_freeToVertexGroup (S : Type u) (w : FreeGroup S) :
    vertexGroupToFree S (freeToVertexGroup S w) = w := by
  have h : (vertexGroupToFree S).comp (freeToVertexGroup S) =
      MonoidHom.id (FreeGroup S) := by
    apply FreeGroup.lift.symm.injective
    funext s
    change vertexGroupToFree S (freeToVertexGroup S (FreeGroup.of s)) = FreeGroup.of s
    simp
  exact DFunLike.congr_fun h w

/-- The same inverse equation on the free groupoid follows from its universal property. -/
theorem freeToVertexGroup_vertexGroupToFree (S : Type u) (g : bouquetVertexGroup S) :
    freeToVertexGroup S (vertexGroupToFree S g) = g := by
  let E : Quiver.FreeGroupoid (Vertex S) ⥤ Quiver.FreeGroupoid (Vertex S) :=
    labelFunctor S ⋙ CategoryTheory.SingleObj.functor
      (C := Quiver.FreeGroupoid (Vertex S))
      (X := (Quiver.FreeGroupoid.of (Vertex S)).obj (default : Vertex S))
      (freeToVertexGroup S)
  have hrest : Quiver.FreeGroupoid.of (Vertex S) ⋙q E.toPrefunctor =
      Quiver.FreeGroupoid.of (Vertex S) := by
    apply Prefunctor.ext
      (fun x => by cases x; rfl)
    intro x y s
    cases x
    cases y
    change freeToVertexGroup S ((labelFunctor S).map
      ((Quiver.FreeGroupoid.of (Vertex S)).map s)) = edgeEnd s
    rw [show (labelFunctor S).map ((Quiver.FreeGroupoid.of (Vertex S)).map s) =
      FreeGroup.of s from vertexGroupToFree_edgeEnd s]
    exact freeToVertexGroup_of s
  have hE : E = 𝟭 (Quiver.FreeGroupoid (Vertex S)) :=
    (Quiver.FreeGroupoid.lift_unique (Quiver.FreeGroupoid.of (Vertex S)) E hrest).trans
      (Quiver.FreeGroupoid.lift_unique (Quiver.FreeGroupoid.of (Vertex S))
        (𝟭 _) rfl).symm
  have h := Prefunctor.congr_hom (congrArg Functor.toPrefunctor hE) g
  exact h

/-- The universe-correct one-vertex free groupoid is the free group on its edge labels. -/
def vertexGroupEquiv (S : Type u) : bouquetVertexGroup S ≃* FreeGroup S where
  toFun := vertexGroupToFree S
  invFun := freeToVertexGroup S
  left_inv := freeToVertexGroup_vertexGroupToFree S
  right_inv := vertexGroupToFree_freeToVertexGroup S
  map_mul' := (vertexGroupToFree S).map_mul

/-- The canonical topological realization of free-group words. -/
def freeGroupEquiv (S : Type u) : FreeGroup S ≃* FundamentalGroup (Bouquet S) (base S) :=
  (vertexGroupEquiv S).symm.trans
    (FiniteGraphFreeGroup.graphCombinatorialToTopologicalEquiv (default : Vertex S))

/-- The canonical labeling of topological loops. -/
def bouquetEquiv (S : Type u) : FundamentalGroup (Bouquet S) (base S) ≃* FreeGroup S :=
  (freeGroupEquiv S).symm

@[simp]
theorem freeGroupEquiv_of {S : Type u} (s : S) :
    freeGroupEquiv S (FreeGroup.of s) = Path.Homotopic.Quotient.mk (edgeLoop s) := by
  change FiniteGraphFreeGroup.graphCombinatorialToTopological (default : Vertex S)
    (freeToVertexGroup S (FreeGroup.of s)) = _
  rw [freeToVertexGroup_of]
  have h := Prefunctor.congr_hom
    (FiniteGraphFreeGroup.graphFreeGroupoidToTopological_restrict (V := Vertex S))
    (show (default : Vertex S) ⟶ (default : Vertex S) from s)
  exact h

@[simp]
theorem bouquetEquiv_edgeLoop {S : Type u} (s : S) :
    bouquetEquiv S (Path.Homotopic.Quotient.mk (edgeLoop s)) = FreeGroup.of s := by
  rw [← freeGroupEquiv_of]
  exact (freeGroupEquiv S).symm_apply_apply _

end PresentationComplex
