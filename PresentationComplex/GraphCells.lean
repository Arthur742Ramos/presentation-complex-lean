import FiniteGraphFreeGroup.TopologicalCover
import Mathlib.Topology.Homeomorph.Lemmas

/-! Genuine open interval cells of arbitrary graph realizations. -/
noncomputable section
open Set Function CategoryTheory Quiver unitInterval
open FiniteGraphFreeGroup
universe u
namespace PresentationComplex
variable {V : Type u} [Quiver.{u} V]

/-- The interior of an actual characteristic interval. -/
def edgeInterior (e : Quiver.Total V) : C(Ioo (0 : I) 1, graphRealization V) where
  toFun t := graphEdgePath e t
  continuous_toFun := (graphEdgePath e).continuous.comp continuous_subtype_val

private def rawEdgeInterior (e : Quiver.Total V) (t : Ioo (0 : I) 1) :
    graphRealizationPre V :=
  Sum.inr ⟨graphDiscreteEdge e,t.val⟩

private theorem rawEdgeInterior_isOpenMap (e : Quiver.Total V) :
    IsOpenMap (rawEdgeInterior e) :=
  isOpenMap_inr.comp (isOpenMap_sigmaMk.comp isOpen_Ioo.isOpenMap_subtype_val)

private theorem rawEdgeInterior_image_saturated (e : Quiver.Total V)
    (A : Set (Ioo (0 : I) 1)) {x y : graphRealizationPre V}
    (h : Relation.EqvGen (graphRealizationGenerator (V := V)) x y) :
    x ∈ rawEdgeInterior e '' A ↔ y ∈ rawEdgeInterior e '' A := by
  suffices hx : ∀ {x y : graphRealizationPre V},
      Relation.EqvGen (graphRealizationGenerator (V := V)) x y →
      x ∈ rawEdgeInterior e '' A → y ∈ rawEdgeInterior e '' A from
    ⟨hx h, hx h.symm⟩
  intro x y h
  rintro ⟨t,ht,rfl⟩
  have hpre : y ∈ graphEdgeInteriorPre e :=
    (graphEdgeInteriorPre_saturated e h).mp (by
      simp only [rawEdgeInterior,graphEdgeInteriorPre,mem_setOf_eq,true_and]
      exact t.property)
  cases y with
  | inl v => simp [graphEdgeInteriorPre] at hpre
  | inr w =>
    rcases w with ⟨eb,t'⟩
    have he : eb = graphDiscreteEdge e := hpre.1
    subst eb
    have heq := graphRealization_interior_eqvGen_eq
      t.property.1 t.property.2 hpre.2.1 hpre.2.2 h
    have ht' : t' = t.val := heq.2.symm
    subst t'
    exact ⟨t,ht,rfl⟩

/-- Each actual edge interior embeds openly in the quotient, without finite-degree assumptions. -/
theorem edgeInterior_isOpenEmbedding (e : Quiver.Total V) :
    Topology.IsOpenEmbedding (edgeInterior e) := by
  apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
  · exact (edgeInterior e).continuous
  · intro t t' h
    have hi := graphRealization_interior_eqvGen_eq
      t.property.1 t.property.2 t'.property.1 t'.property.2 (Quotient.exact h)
    exact Subtype.ext hi.2
  · intro A hA
    have hopen := (rawEdgeInterior_isOpenMap e) A hA
    have hq := graphRealization_image_isOpen_of_saturated
      (rawEdgeInterior_image_saturated e A) hopen
    rw [← image_comp] at hq
    exact hq

/-- The open-cell range is exactly the existing quotient interior. -/
theorem edgeInterior_range (e : Quiver.Total V) :
    Set.range (edgeInterior e) = graphEdgeInterior e := by
  ext x
  constructor
  · rintro ⟨t,rfl⟩
    exact graphEdgePath_mem_graphEdgeInterior e t.property.1 t.property.2
  · rintro ⟨w,hw,rfl⟩
    cases w with
    | inl v => simp [graphEdgeInteriorPre] at hw
    | inr w =>
      rcases w with ⟨eb,t⟩
      have he : eb = graphDiscreteEdge e := hw.1
      subst eb
      exact ⟨⟨t,hw.2⟩,rfl⟩

end PresentationComplex
