import PresentationComplex.Bouquet
import PresentationComplex.GraphCells
import PresentationComplex.IntervalCharts

/-! Explicit characteristic cells and quotient weak topology of the arbitrary bouquet. -/
noncomputable section
open Set Metric CategoryTheory Quiver unitInterval
open FiniteGraphFreeGroup
universe u
namespace PresentationComplex
variable {S : Type u}

/-- The unique zero-cell's actual characteristic map. -/
def bouquetChar0 (S : Type u) : C(ClosedCellDomain 0, Bouquet S) :=
  ContinuousMap.const _ (base S)

/-- The actual closed interval indexed by a generator, in Mathlib's one-cell coordinates. -/
def bouquetChar1 (s : S) : C(ClosedCellDomain 1, Bouquet S) :=
  (graphEdgePath ((edgeIndexEquiv S).symm s)).comp
    ⟨closedIntervalChart,closedIntervalChart.continuous⟩

/-- The zero-cell interior is genuinely embedded. -/
theorem bouquetChar0_interiorEmbedding (S : Type u) :
    Topology.IsEmbedding (cellInterior 0 (bouquetChar0 S)) :=
  Topology.IsEmbedding.of_subsingleton _

/-- The one-cell interiors are genuine embedded open intervals. -/
theorem bouquetChar1_interiorEmbedding (s : S) :
    Topology.IsEmbedding (cellInterior 1 (bouquetChar1 s)) := by
  have he := (edgeInterior_isOpenEmbedding ((edgeIndexEquiv S).symm s)).isEmbedding.comp
    openIntervalChart.isEmbedding
  convert he using 1
  ext x
  rfl

/-- The closed one-cell is precisely the actual generator-loop image. -/
theorem bouquetChar1_range (s : S) : Set.range (bouquetChar1 s) = Set.range (edgeLoop s) := by
  change Set.range ((graphEdgePath ((edgeIndexEquiv S).symm s)) ∘ closedIntervalChart) = _
  rw [closedIntervalChart.surjective.range_comp]
  rfl

/-- The open one-cell is precisely the actual quotient edge interior. -/
theorem bouquetChar1_interior_range (s : S) :
    Set.range (cellInterior 1 (bouquetChar1 s)) =
      graphEdgeInterior ((edgeIndexEquiv S).symm s) := by
  change Set.range ((edgeInterior ((edgeIndexEquiv S).symm s)) ∘ openIntervalChart) = _
  rw [openIntervalChart.surjective.range_comp]
  exact edgeInterior_range _

/-- Both characteristic one-cell boundary points are the actual bouquet vertex. -/
theorem bouquetChar1_boundary (s : S) (x : ClosedCellDomain 1) (hx : ‖x.val‖ = 1) :
    bouquetChar1 s x = base S := by
  rcases closedIntervalChart_boundary x hx with hx | hx
  · change graphEdgePath ((edgeIndexEquiv S).symm s) (closedIntervalChart x) = _
    rw [hx,graphEdgePath_zero]
    rfl
  · change graphEdgePath ((edgeIndexEquiv S).symm s) (closedIntervalChart x) = _
    rw [hx,graphEdgePath_one]
    rfl

/-- The bouquet's topology is exactly the weak topology tested on its closed interval cells. -/
theorem bouquet_weakTopology (A : Set (Bouquet S))
    (h1 : ∀ s, IsClosed ((bouquetChar1 s) ⁻¹' A)) : IsClosed A := by
  rw [← isQuotientMap_quotient_mk'.isCoinducing.isClosed_preimage]
  rw [isClosed_sum_iff]
  constructor
  · exact isClosed_discrete _
  · rw [isClosed_sigma_iff]
    intro eb
    let e : Quiver.Total (Vertex S) := graphEdgeUnderlying eb
    let s : S := edgeIndexEquiv S e
    have he : (edgeIndexEquiv S).symm s = e := (edgeIndexEquiv S).symm_apply_apply e
    have hc := (h1 s).preimage closedIntervalChart.symm.continuous
    change IsClosed ((graphEdgePath e) ⁻¹' A)
    convert hc using 1
    ext t
    simp only [mem_preimage,bouquetChar1,ContinuousMap.comp_apply,
      ContinuousMap.coe_mk,closedIntervalChart.apply_symm_apply,he]

end PresentationComplex

namespace PresentationComplex
open Set Metric CategoryTheory Quiver unitInterval
open FiniteGraphFreeGroup
variable {S : Type u}

@[simp] theorem bouquetChar0_range (S : Type u) :
    Set.range (bouquetChar0 S) = {base S} := by
  ext x
  constructor
  · rintro ⟨z,rfl⟩
    rfl
  · intro hx
    have h : x = base S := hx
    subst x
    exact ⟨⟨0,by simp⟩,rfl⟩

@[simp] theorem bouquetChar0_interior_range (S : Type u) :
    Set.range (cellInterior 0 (bouquetChar0 S)) = {base S} := by
  ext x
  constructor
  · rintro ⟨z,rfl⟩
    rfl
  · intro hx
    have h : x = base S := hx
    subst x
    exact ⟨⟨0,by simp⟩,rfl⟩

/-- The vertex is never an open one-cell point. -/
theorem base_not_mem_bouquetChar1_interior (s : S) :
    base S ∉ Set.range (cellInterior 1 (bouquetChar1 s)) := by
  rintro ⟨z,hz⟩
  let t := openIntervalChart z
  exact graphRealization_edge_interior_ne_vertex ((edgeIndexEquiv S).symm s)
    (ne_of_gt t.property.1) (ne_of_lt t.property.2) default hz

/-- Distinct labels retain distinct, disjoint actual interval interiors. -/
theorem bouquetChar1_interiors_disjoint {s t : S} (h : s ≠ t) :
    Disjoint (Set.range (cellInterior 1 (bouquetChar1 s)))
      (Set.range (cellInterior 1 (bouquetChar1 t))) := by
  rw [bouquetChar1_interior_range,bouquetChar1_interior_range]
  exact graphEdgeInterior_disjoint ((edgeIndexEquiv S).symm.injective.ne h)

/-- Actual closed cells exhaust the arbitrary weak bouquet. -/
theorem bouquet_closed_cells_cover (x : Bouquet S) :
    x = base S ∨ ∃ s z, bouquetChar1 s z = x := by
  obtain ⟨a,rfl⟩ := isQuotientMap_quotient_mk'.surjective x
  cases a with
  | inl v =>
    left
    have hv : graphVertexUnderlying v = (default : Vertex S) := Subsingleton.elim _ _
    exact congrArg graphVertex hv
  | inr w =>
    rcases w with ⟨eb,t⟩
    let e := graphEdgeUnderlying eb
    refine Or.inr ⟨edgeIndexEquiv S e,closedIntervalChart.symm t,?_⟩
    simp only [bouquetChar1,ContinuousMap.comp_apply,ContinuousMap.coe_mk,
      Equiv.symm_apply_apply,closedIntervalChart.apply_symm_apply]
    rfl

end PresentationComplex
