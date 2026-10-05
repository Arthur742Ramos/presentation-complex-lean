import PresentationComplex.BouquetCells
import PresentationComplex.CellCharts
import PresentationComplex.Relators
import CellAttachment.Embeddings

/-!
# Ordinary CW structure on the actual presentation adjunction

The characteristic maps are the actual vertex, generator intervals, and
indexed attached disks. No indexed disk is removed, even when its relator is
constant or duplicates another relator. Closure finiteness is derived from
each relator's finite word support, and the weak topology is the actual
quotient topology.
-/
noncomputable section
open Set Metric CategoryTheory Quiver unitInterval
open FiniteGraphFreeGroup
universe u v
namespace PresentationComplex
variable {S : Type u} {R : Type v}

/-- The canonical 0-, 1-, and 2-cell indices, in the ambient universe. -/
def presentationCell (S : Type u) (R : Type v) : ℕ → Type (max u v)
  | 0 => PUnit
  | 1 => ULift.{v} S
  | 2 => ULift.{u} R
  | _ + 3 => PEmpty

/-- The actual indexed disk characteristic, in Mathlib's square coordinates. -/
def attachmentChar2 (f : R → C(Circle,Bouquet S)) (i : R) :
    C(ClosedCellDomain 2, CellAttachment.Space f) :=
  (CellAttachment.characteristic f i).comp
    ⟨closedDiskChart,closedDiskChart.continuous⟩

/-- The genuine characteristic maps for the whole adjunction. -/
def attachmentChar (f : R → C(Circle,Bouquet S)) :
    ∀ n, presentationCell S R n → C(ClosedCellDomain n,CellAttachment.Space f)
  | 0, _ => (CellAttachment.inclusion f).comp (bouquetChar0 S)
  | 1, i => (CellAttachment.inclusion f).comp (bouquetChar1 i.down)
  | 2, i => attachmentChar2 f i.down
  | _ + 3, i => PEmpty.elim i

private theorem attachmentChar0_embedding (f : R → C(Circle,Bouquet S)) :
    Topology.IsEmbedding (cellInterior 0 (attachmentChar f 0 PUnit.unit)) :=
  Topology.IsEmbedding.of_subsingleton _

private theorem attachmentChar1_embedding (f : R → C(Circle,Bouquet S)) (i : S) :
    Topology.IsEmbedding (cellInterior 1 (attachmentChar f 1 ⟨i⟩)) := by
  exact (CellAttachment.inclusion_isClosedEmbedding f).isEmbedding.comp
    (bouquetChar1_interiorEmbedding i)

private theorem attachmentChar2_interior (f : R → C(Circle,Bouquet S)) (i : R) :
    cellInterior 2 (attachmentChar2 f i) =
      (CellAttachment.interiorMap f).comp
        ⟨fun z => ⟨i,openDiskChart z⟩,
          (continuous_sigmaMk (i := i)).comp openDiskChart.continuous⟩ := by
  ext z
  rfl

private theorem attachmentChar2_embedding (f : R → C(Circle,Bouquet S)) (i : R) :
    Topology.IsEmbedding (cellInterior 2 (attachmentChar2 f i)) := by
  rw [attachmentChar2_interior]
  exact (CellAttachment.interiorMap_isOpenEmbedding f).isEmbedding.comp
    (Topology.IsEmbedding.sigmaMk.comp openDiskChart.isEmbedding)

private theorem attachmentChar0_interior_range (f : R → C(Circle,Bouquet S)) :
    Set.range (cellInterior 0 (attachmentChar f 0 PUnit.unit)) =
      {CellAttachment.inclusion f (base S)} := by
  change Set.range ((CellAttachment.inclusion f) ∘ cellInterior 0 (bouquetChar0 S)) = _
  rw [Set.range_comp,bouquetChar0_interior_range,Set.image_singleton]

private theorem attachmentChar1_interior_range (f : R → C(Circle,Bouquet S)) (s : S) :
    Set.range (cellInterior 1 (attachmentChar f 1 ⟨s⟩)) =
      CellAttachment.inclusion f '' Set.range (cellInterior 1 (bouquetChar1 s)) := by
  change Set.range ((CellAttachment.inclusion f) ∘ cellInterior 1 (bouquetChar1 s)) = _
  exact Set.range_comp _ _

private theorem attachmentChar2_mem_interiors (f : R → C(Circle,Bouquet S))
    (i : R) (z : OpenCellDomain 2) :
    cellInterior 2 (attachmentChar2 f i) z ∈ CellAttachment.interiors f := by
  rw [attachmentChar2_interior]
  exact CellAttachment.interiorRepresentative_mem_interiors f i (openDiskChart z)

private theorem attachmentChar2_disjoint_base (f : R → C(Circle,Bouquet S))
    (i : R) (z : OpenCellDomain 2) (x : Bouquet S) :
    cellInterior 2 (attachmentChar2 f i) z ≠ CellAttachment.inclusion f x := by
  rw [attachmentChar2_interior]
  exact CellAttachment.interior_ne_inclusion f i (openDiskChart z) x

private theorem attachmentChar2_disjoint (f : R → C(Circle,Bouquet S))
    {i j : R} (hij : i ≠ j) :
    Disjoint (Set.range (cellInterior 2 (attachmentChar2 f i)))
      (Set.range (cellInterior 2 (attachmentChar2 f j))) := by
  rw [Set.disjoint_left]
  rintro x ⟨z,rfl⟩ ⟨w,hw⟩
  have he : (⟨j,openDiskChart w⟩ : Σ _ : R,CellAttachment.OpenDisk) =
      ⟨i,openDiskChart z⟩ :=
    (CellAttachment.interiorMap_isOpenEmbedding f).injective hw
  exact hij (congrArg Sigma.fst he).symm

private theorem attachmentChar_pairwiseDisjoint (f : R → C(Circle,Bouquet S)) :
    (Set.univ : Set (Σ n,presentationCell S R n)).PairwiseDisjoint
      (fun ni => Set.range (cellInterior ni.1 (attachmentChar f ni.1 ni.2))) := by
  intro a _ b _ hab
  rcases a with ⟨n,i⟩
  rcases b with ⟨m,j⟩
  change Disjoint (Set.range (cellInterior n (attachmentChar f n i)))
    (Set.range (cellInterior m (attachmentChar f m j)))
  rcases n with _ | _ | _ | n <;> rcases m with _ | _ | _ | m
  · change PUnit at i j
    have hij : i = j := Subsingleton.elim _ _
    cases hij
    exact (hab rfl).elim
  · rw [Set.disjoint_left]
    rintro x ⟨z,rfl⟩ ⟨w,hw⟩
    have h := (CellAttachment.inclusion_injective f) hw
    exact base_not_mem_bouquetChar1_interior j.down ⟨w,h⟩
  · rw [Set.disjoint_left]
    rintro x ⟨z,rfl⟩ ⟨w,hw⟩
    exact attachmentChar2_disjoint_base f j.down w (base S) hw
  · exact PEmpty.elim j
  · rw [Set.disjoint_left]
    rintro x ⟨z,rfl⟩ ⟨w,hw⟩
    have h := (CellAttachment.inclusion_injective f) hw
    exact base_not_mem_bouquetChar1_interior i.down ⟨z,h.symm⟩
  · change Disjoint (Set.range (cellInterior 1 (attachmentChar f 1 ⟨i.down⟩)))
      (Set.range (cellInterior 1 (attachmentChar f 1 ⟨j.down⟩)))
    rw [attachmentChar1_interior_range,attachmentChar1_interior_range]
    apply Set.disjoint_image_of_injective (CellAttachment.inclusion_injective f)
    apply bouquetChar1_interiors_disjoint
    intro h
    apply hab
    cases i
    cases j
    cases h
    rfl
  · rw [Set.disjoint_left]
    rintro x ⟨z,rfl⟩ ⟨w,hw⟩
    exact attachmentChar2_disjoint_base f j.down w (cellInterior 1 (bouquetChar1 i.down) z) hw
  · exact PEmpty.elim j
  · rw [Set.disjoint_left]
    rintro x ⟨z,rfl⟩ ⟨w,hw⟩
    exact attachmentChar2_disjoint_base f i.down z (base S) hw.symm
  · rw [Set.disjoint_left]
    rintro x ⟨z,rfl⟩ ⟨w,hw⟩
    exact attachmentChar2_disjoint_base f i.down z (cellInterior 1 (bouquetChar1 j.down) w) hw.symm
  · apply attachmentChar2_disjoint f
    intro h
    apply hab
    cases i
    cases j
    cases h
    rfl
  · exact PEmpty.elim j
  · exact PEmpty.elim i
  · exact PEmpty.elim i
  · exact PEmpty.elim i
  · exact PEmpty.elim i

private theorem attachment_weakTopology (f : R → C(Circle,Bouquet S))
    (A : Set (CellAttachment.Space f))
    (h : ∀ n i, IsClosed ((attachmentChar f n i) ⁻¹' A)) : IsClosed A := by
  rw [← (CellAttachment.quotientMap_isQuotientMap f).isCoinducing.isClosed_preimage]
  rw [isClosed_sum_iff]
  constructor
  · apply bouquet_weakTopology
    intro s
    exact h 1 ⟨s⟩
  · rw [isClosed_sigma_iff]
    intro i
    have hc := (h 2 ⟨i⟩).preimage closedDiskChart.symm.continuous
    convert hc using 1
    ext z
    simp only [mem_preimage,attachmentChar,attachmentChar2,ContinuousMap.comp_apply,
      ContinuousMap.coe_mk,closedDiskChart.apply_symm_apply]
    rfl

private theorem attachment_closed_cells_cover (f : R → C(Circle,Bouquet S))
    (x : CellAttachment.Space f) : ∃ n i z, attachmentChar f n i z = x := by
  obtain ⟨a,rfl⟩ := (CellAttachment.quotientMap_isQuotientMap f).surjective x
  cases a with
  | inl y =>
    rcases bouquet_closed_cells_cover y with hy | ⟨s,z,hz⟩
    · subst y
      exact ⟨0,PUnit.unit,⟨0,by simp⟩,rfl⟩
    · exact ⟨1,⟨s⟩,z,congrArg (CellAttachment.inclusion f) hz⟩
  | inr w =>
    rcases w with ⟨i,z⟩
    exact ⟨2,⟨i⟩,closedDiskChart.symm z,by
      simp only [attachmentChar,attachmentChar2,ContinuousMap.comp_apply,
        ContinuousMap.coe_mk,closedDiskChart.apply_symm_apply]
      rfl⟩

private theorem closedDiskChart_boundary (z : ClosedCellDomain 2) (hz : ‖z.val‖ = 1) :
    ‖(closedDiskChart z : ℂ)‖ = 1 := by
  apply mem_sphere_zero_iff_norm.mp
  rw [← squareToComplex_sphere]
  exact ⟨z.val,mem_sphere_zero_iff_norm.mpr hz,rfl⟩

/-- A finite word carrier is contained in the corresponding finitely many closed cells. -/
private theorem attachment_finite_boundary (f : R → C(Circle,Bouquet S))
    (support : R → Finset S)
    (hsupport : ∀ i,Set.range (f i) ⊆ {base S} ∪ ⋃ s ∈ support i,Set.range (edgeLoop s)) :
    ∀ n i, ∃ F : ∀ m,Finset (presentationCell S R m),
      ∀ z : ClosedCellDomain n, ‖z.val‖ = 1 →
        attachmentChar f n i z ∈ ⋃ (m < n) (j ∈ F m),Set.range (attachmentChar f m j) := by
  classical
  intro n i
  rcases n with _ | _ | _ | n
  · refine ⟨fun _ => ∅,?_⟩
    intro z hz
    have hzero : z.val = 0 := Subsingleton.elim _ _
    have hn : ‖z.val‖ = 0 := by rw [hzero,norm_zero]
    exact (zero_ne_one (hn.symm.trans hz)).elim
  · let F : ∀ m,Finset (presentationCell S R m)
      | 0 => {PUnit.unit}
      | _ + 1 => ∅
    refine ⟨F,?_⟩
    intro z hz
    have hb := bouquetChar1_boundary i.down z hz
    refine mem_iUnion.mpr ⟨0,mem_iUnion.mpr ⟨by omega,mem_iUnion.mpr ⟨PUnit.unit,
      mem_iUnion.mpr ⟨by exact Finset.mem_singleton_self _,?_⟩⟩⟩⟩
    exact ⟨⟨0,by simp⟩,by
      change CellAttachment.inclusion f (base S) = CellAttachment.inclusion f (bouquetChar1 i.down z)
      rw [hb]⟩
  · let F : ∀ m,Finset (presentationCell S R m)
      | 0 => {PUnit.unit}
      | 1 => (support i.down).map ⟨ULift.up,ULift.up_injective⟩
      | _ + 2 => ∅
    refine ⟨F,?_⟩
    intro z hz
    let w := CellAttachment.diskBoundaryPoint (closedDiskChart z) (closedDiskChart_boundary z hz)
    have hb : attachmentChar f 2 i z = CellAttachment.inclusion f (f i.down w) :=
      CellAttachment.characteristic_boundary f i.down w
    rw [hb]
    rcases hsupport i.down ⟨w,rfl⟩ with hw | hw
    · have hw' : f i.down w = base S := hw
      rw [hw']
      refine mem_iUnion.mpr ⟨0,mem_iUnion.mpr ⟨by omega,mem_iUnion.mpr ⟨PUnit.unit,
        mem_iUnion.mpr ⟨by exact Finset.mem_singleton_self _,?_⟩⟩⟩⟩
      exact ⟨⟨0,by simp⟩,rfl⟩
    · rcases mem_iUnion.mp hw with ⟨s,hw⟩
      rcases mem_iUnion.mp hw with ⟨hs,hw⟩
      rw [← bouquetChar1_range] at hw
      rcases hw with ⟨t,ht⟩
      refine mem_iUnion.mpr ⟨1,mem_iUnion.mpr ⟨by omega,mem_iUnion.mpr ⟨⟨s⟩,
        mem_iUnion.mpr ⟨by exact Finset.mem_map.mpr ⟨s,hs,rfl⟩,?_⟩⟩⟩⟩
      exact ⟨t,congrArg (CellAttachment.inclusion f) ht⟩
  · exact PEmpty.elim i

/-- Proved geometric CW data for arbitrary, individually finitely supported attachments. -/
def attachmentCWGeometry (f : R → C(Circle,Bouquet S))
    (support : R → Finset S)
    (hsupport : ∀ i,Set.range (f i) ⊆ {base S} ∪ ⋃ s ∈ support i,Set.range (edgeLoop s)) :
    CWGeometry (CellAttachment.Space f) where
  cell := presentationCell S R
  char := attachmentChar f
  interiorEmbedding n i := by
    rcases n with _ | _ | _ | n
    · exact attachmentChar0_embedding f
    · exact attachmentChar1_embedding f i.down
    · exact attachmentChar2_embedding f i.down
    · exact PEmpty.elim i
  disjoint := attachmentChar_pairwiseDisjoint f
  finiteBoundary := attachment_finite_boundary f support hsupport
  weakTopology := attachment_weakTopology f
  cover := attachment_closed_cells_cover f

/-- The concrete ordinary Mathlib CW structure on the actual presentation space. -/
@[instance_reducible] def presentationCW (r : R → FreeGroup S) : Topology.CWComplex (Set.univ : Set (Space r)) :=
  (attachmentCWGeometry (relatorMap r) (fun i => wordSupport (relatorWord (r i)))
    (fun i => relatorMap_range_subset r i)).toCWComplex (point r)

/-- Every generator remains an indexed one-cell. -/
def presentationCW_generatorCells (r : R → FreeGroup S) :
    (presentationCW r).cell 1 ≃ S := Equiv.ulift

/-- Every relator index remains a genuine disk cell, including duplicates and identities. -/
def presentationCW_relatorCells (r : R → FreeGroup S) :
    (presentationCW r).cell 2 ≃ R := Equiv.ulift

/-- No cells occur above dimension two. -/
theorem presentationCW_noHigherCells (r : R → FreeGroup S) (n : ℕ) (hn : 2 < n) :
    IsEmpty ((presentationCW r).cell n) := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le (show 3 ≤ n by omega)
  change IsEmpty (presentationCell S R (3+k))
  rw [Nat.add_comm]
  exact inferInstanceAs (IsEmpty PEmpty)

end PresentationComplex
