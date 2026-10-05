module

public import Mathlib.Topology.CWComplex.Classical.Basic
public import Mathlib.Topology.Homeomorph.Lemmas

@[expose] public section

/-! A characteristic closed-cell map with a genuinely embedded open cell induces
Mathlib's required partial equivalence. This helper does not assert CW axioms. -/
noncomputable section
attribute [local instance] Classical.propDecidable
open Set Metric
universe u
namespace PresentationComplex
variable {X : Type u} [TopologicalSpace X] (n : ℕ)

abbrev ClosedCellDomain := closedBall (0 : Fin n → ℝ) 1
abbrev OpenCellDomain := ball (0 : Fin n → ℝ) 1

/-- Restrict a characteristic closed-cell map to its open cell. -/
def cellInterior (c : C(ClosedCellDomain n, X)) : C(OpenCellDomain n, X) where
  toFun x := c ⟨x, ball_subset_closedBall x.property⟩
  continuous_toFun := c.continuous.comp (continuous_subtype_val.subtype_mk _)

/-- Extend the characteristic map outside its closed domain only set-theoretically.
CW continuity is required precisely on the closed ball. -/
def cellExtension (x₀ : X) (c : C(ClosedCellDomain n, X)) (x : Fin n → ℝ) : X :=
  if hx : x ∈ ClosedCellDomain n then c ⟨x,hx⟩ else x₀

@[simp] theorem cellExtension_apply (x₀ : X) (c : C(ClosedCellDomain n, X))
    (x : ClosedCellDomain n) : cellExtension n x₀ c x = c x := by
  simp only [cellExtension, dif_pos x.property]

/-- A characteristic map, paired with its actual open-cell inverse. -/
def cellPartialEquiv (x₀ : X) (c : C(ClosedCellDomain n, X))
    (he : Topology.IsEmbedding (cellInterior n c)) : PartialEquiv (Fin n → ℝ) X where
  toFun := cellExtension n x₀ c
  invFun y := if hy : y ∈ Set.range (cellInterior n c) then
    (he.toHomeomorph.symm ⟨y,hy⟩).val else 0
  source := ball 0 1
  target := Set.range (cellInterior n c)
  map_source' := by
    intro x hx
    refine ⟨⟨x,hx⟩,?_⟩
    exact (cellExtension_apply n x₀ c ⟨x,ball_subset_closedBall hx⟩).symm
  map_target' := by
    intro y hy
    simp only [dif_pos hy]
    exact (he.toHomeomorph.symm ⟨y,hy⟩).property
  left_inv' := by
    intro x hx
    have h : cellExtension n x₀ c x = cellInterior n c ⟨x,hx⟩ := by
      exact cellExtension_apply n x₀ c ⟨x,ball_subset_closedBall hx⟩
    rw [h]
    simp only [show cellInterior n c ⟨x,hx⟩ ∈ Set.range (cellInterior n c) from
      ⟨⟨x,hx⟩,rfl⟩, dif_pos]
    exact congrArg Subtype.val (he.toHomeomorph_symm_apply ⟨x,hx⟩)
  right_inv' := by
    intro y hy
    simp only [dif_pos hy]
    rw [show cellExtension n x₀ c (he.toHomeomorph.symm ⟨y,hy⟩).val =
      cellInterior n c (he.toHomeomorph.symm ⟨y,hy⟩) from by
        exact cellExtension_apply n x₀ c
          ⟨(he.toHomeomorph.symm ⟨y,hy⟩).val,
            ball_subset_closedBall (he.toHomeomorph.symm ⟨y,hy⟩).property⟩]
    exact congrArg Subtype.val (he.toHomeomorph.apply_symm_apply ⟨y,hy⟩)

@[simp] theorem cellPartialEquiv_source (x₀ : X) (c : C(ClosedCellDomain n, X))
    (he : Topology.IsEmbedding (cellInterior n c)) :
    (cellPartialEquiv n x₀ c he).source = ball 0 1 := rfl

theorem cellPartialEquiv_continuousOn (x₀ : X) (c : C(ClosedCellDomain n, X))
    (he : Topology.IsEmbedding (cellInterior n c)) :
    ContinuousOn (cellPartialEquiv n x₀ c he) (closedBall 0 1) := by
  rw [continuousOn_iff_continuous_restrict]
  change Continuous (fun z : ClosedCellDomain n => cellExtension n x₀ c z)
  exact c.continuous.congr (fun z => (cellExtension_apply n x₀ c z).symm)

theorem cellPartialEquiv_continuousOn_symm (x₀ : X) (c : C(ClosedCellDomain n, X))
    (he : Topology.IsEmbedding (cellInterior n c)) :
    ContinuousOn (cellPartialEquiv n x₀ c he).symm (cellPartialEquiv n x₀ c he).target := by
  rw [continuousOn_iff_continuous_restrict]
  have hc : Continuous (fun y : Set.range (cellInterior n c) =>
      (he.toHomeomorph.symm y).val) :=
    continuous_subtype_val.comp he.toHomeomorph.symm.continuous
  change Continuous (fun y : Set.range (cellInterior n c) =>
    if hy : y.val ∈ Set.range (cellInterior n c) then
      (he.toHomeomorph.symm ⟨y.val,hy⟩).val else 0)
  apply hc.congr
  intro y
  simp only [dif_pos y.property]

end PresentationComplex

namespace PresentationComplex
open Set Metric
variable {X : Type u} [TopologicalSpace X] (n : ℕ)

theorem cellPartialEquiv_open_image (x₀ : X) (c : C(ClosedCellDomain n, X))
    (he : Topology.IsEmbedding (cellInterior n c)) :
    cellPartialEquiv n x₀ c he '' ball 0 1 = Set.range (cellInterior n c) :=
  (cellPartialEquiv n x₀ c he).image_source_eq_target

theorem cellPartialEquiv_closed_image (x₀ : X) (c : C(ClosedCellDomain n, X))
    (he : Topology.IsEmbedding (cellInterior n c)) :
    cellPartialEquiv n x₀ c he '' closedBall 0 1 = Set.range c := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact ⟨⟨x,hx⟩, (cellExtension_apply n x₀ c ⟨x,hx⟩).symm⟩
  · rintro ⟨x,rfl⟩
    exact ⟨x,x.property,cellExtension_apply n x₀ c x⟩

/-- Geometric data used to construct an ordinary Mathlib CW structure.
These fields are proved for the concrete quotient in subsequent modules;
this helper isolates the partial-equivalence bookkeeping. -/
structure CWGeometry (X : Type u) [TopologicalSpace X] where
  cell : ℕ → Type u
  char : ∀ n, cell n → C(ClosedCellDomain n, X)
  interiorEmbedding : ∀ n i, Topology.IsEmbedding (cellInterior n (char n i))
  disjoint : (Set.univ : Set (Σ n, cell n)).PairwiseDisjoint
    (fun ni => Set.range (cellInterior ni.1 (char ni.1 ni.2)))
  finiteBoundary : ∀ n i, ∃ I : ∀ m, Finset (cell m),
    ∀ z : ClosedCellDomain n, ‖z.val‖ = 1 →
      char n i z ∈ ⋃ (m < n) (j ∈ I m), Set.range (char m j)
  weakTopology : ∀ A : Set X, (∀ n i, IsClosed ((char n i) ⁻¹' A)) → IsClosed A
  cover : ∀ x : X, ∃ n i z, char n i z = x

/-- Construct the exact classical CW structure from proved closed-cell geometry. -/
def CWGeometry.toCWComplex (d : CWGeometry X) (x₀ : X) :
    Topology.CWComplex (Set.univ : Set X) where
  cell := d.cell
  map n i := cellPartialEquiv n x₀ (d.char n i) (d.interiorEmbedding n i)
  source_eq _ _ := rfl
  continuousOn n i := cellPartialEquiv_continuousOn n x₀ _ _
  continuousOn_symm n i := cellPartialEquiv_continuousOn_symm n x₀ _ _
  pairwiseDisjoint' := by
    simpa only [cellPartialEquiv_open_image] using d.disjoint
  mapsTo' n i := by
    obtain ⟨I,hI⟩ := d.finiteBoundary n i
    refine ⟨I,?_⟩
    intro z hz
    have hn : ‖z‖ = 1 := mem_sphere_zero_iff_norm.mp hz
    have hc : z ∈ closedBall (0 : Fin n → ℝ) 1 := by
      simpa only [mem_closedBall,dist_zero_right,hn] using le_refl (1 : ℝ)
    simpa only [cellPartialEquiv_closed_image,
      show cellPartialEquiv n x₀ (d.char n i) (d.interiorEmbedding n i) z =
        d.char n i ⟨z,hc⟩ from cellExtension_apply n x₀ (d.char n i) ⟨z,hc⟩]
      using hI ⟨z,hc⟩ hn
  closed' A _hA h := by
    apply d.weakTopology A
    intro n i
    have hc := (h n i).preimage (d.char n i).continuous
    rw [cellPartialEquiv_closed_image] at hc
    convert hc using 1
    ext z
    simp only [mem_preimage,mem_inter_iff,mem_range_self,and_true]
  union' := by
    simp only [cellPartialEquiv_closed_image]
    ext x
    simp only [mem_iUnion,mem_range,mem_univ,iff_true]
    exact d.cover x

end PresentationComplex
