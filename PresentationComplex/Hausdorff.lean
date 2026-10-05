module

public import PresentationComplex.Bouquet
public import PresentationComplex.GraphCells
public import CellAttachment.Retraction
public import CellAttachment.Embeddings
public import Mathlib.Topology.Separation.Hausdorff

@[expose] public section

/-! Actual Hausdorffness of the weak bouquet and genuine disk adjunction.
Mathlib's CW class omits a Hausdorff assumption; these are independent quotient
separation proofs, so the headline uses a genuine Hausdorff CW complex. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
open Set Function CategoryTheory Quiver unitInterval
open FiniteGraphFreeGroup
universe u v
namespace PresentationComplex

def Separated {X : Type*} [TopologicalSpace X] (x y : X) : Prop :=
  ∃ A B : Set X, IsOpen A ∧ IsOpen B ∧ x ∈ A ∧ y ∈ B ∧ Disjoint A B

theorem Separated.symm {X : Type*} [TopologicalSpace X] {x y : X}
    (h : Separated x y) : Separated y x := by
  rcases h with ⟨A,B,hA,hB,hx,hy,hd⟩
  exact ⟨B,A,hB,hA,hy,hx,hd.symm⟩

theorem separated_continuous {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [T2Space Y] (f : C(X,Y)) {x y : X} (h : f x ≠ f y) :
    Separated x y := by
  rcases t2_separation h with ⟨A,B,hA,hB,hx,hy,hd⟩
  exact ⟨f ⁻¹' A,f ⁻¹' B,hA.preimage f.continuous,hB.preimage f.continuous,
    hx,hy,hd.preimage _⟩

theorem separated_openEmbedding {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [T2Space X] (f : X → Y) (hf : Topology.IsOpenEmbedding f)
    {x y : X} (h : x ≠ y) : Separated (f x) (f y) := by
  rcases t2_separation h with ⟨A,B,hA,hB,hx,hy,hd⟩
  refine ⟨f '' A,f '' B,hf.isOpenMap _ hA,hf.isOpenMap _ hB,
    ⟨x,hx,rfl⟩,⟨y,hy,rfl⟩,?_⟩
  apply disjoint_left.mpr
  rintro z ⟨a,ha,he⟩ ⟨b,hb,he'⟩
  have hab : a = b := hf.injective (he.trans he'.symm)
  subst b
  exact disjoint_left.mp hd ha hb

section Bouquet
variable (S : Type u)

def rawBouquetHeight : graphRealizationPre (Vertex S) → ℝ
  | Sum.inl _ => 0
  | Sum.inr z => min z.2.val (1-z.2.val)

theorem rawBouquetHeight_respects {x y : graphRealizationPre (Vertex S)}
    (h : Relation.EqvGen (graphRealizationGenerator (V := Vertex S)) x y) :
    rawBouquetHeight S x = rawBouquetHeight S y := by
  induction h with
  | rel x y h => cases h <;> norm_num [rawBouquetHeight]
  | refl x => rfl
  | symm x y h ih => exact ih.symm
  | trans x y z hxy hyz ihxy ihyz => exact ihxy.trans ihyz

/-- A continuous height vanishing exactly at the bouquet vertex. -/
def bouquetHeight : C(Bouquet S,ℝ) where
  toFun := Quotient.lift (rawBouquetHeight S) (fun _ _ h => rawBouquetHeight_respects S h)
  continuous_toFun := by
    apply continuous_coinduced_dom.mpr
    have hc : Continuous (Sum.elim (fun _ : WithDiscreteTopology (Vertex S) => (0 : ℝ))
        (fun z : Σ _ : WithDiscreteTopology (Quiver.Total (Vertex S)), I => min z.2.val (1-z.2.val))) := by
      apply Continuous.sumElim
      · exact continuous_const
      · apply continuous_sigma
        intro e
        exact continuous_subtype_val.min (continuous_const.sub continuous_subtype_val)
    exact hc.congr (fun z => by cases z <;> rfl)

def bouquetAllInteriors : C((Σ _ : S, Ioo (0 : I) 1),Bouquet S) where
  toFun p := edgeInterior ((edgeIndexEquiv S).symm p.1) p.2
  continuous_toFun := by
    apply continuous_sigma
    intro s
    exact (edgeInterior ((edgeIndexEquiv S).symm s)).continuous

theorem bouquetAllInteriors_isOpenEmbedding :
    Topology.IsOpenEmbedding (bouquetAllInteriors S) := by
  apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
  · exact (bouquetAllInteriors S).continuous
  · rintro ⟨s,t⟩ ⟨s',t'⟩ h
    dsimp only [bouquetAllInteriors,ContinuousMap.coe_mk,edgeInterior] at h
    have he := graphRealization_interior_eqvGen_eq t.property.1 t.property.2
      t'.property.1 t'.property.2 (Quotient.exact h)
    have hs : s = s' := (edgeIndexEquiv S).symm.injective he.1
    subst s'
    exact Sigma.ext rfl (heq_of_eq (Subtype.ext he.2))
  · rw [isOpenMap_sigma]
    intro s
    simpa only [bouquetAllInteriors,ContinuousMap.coe_mk] using
      (edgeInterior_isOpenEmbedding ((edgeIndexEquiv S).symm s)).isOpenMap

theorem bouquet_point_cases (x : Bouquet S) :
    x = base S ∨ ∃ p, bouquetAllInteriors S p = x := by
  obtain ⟨a,rfl⟩ := Quotient.mk'_surjective x
  cases a with
  | inl v =>
    left
    exact congrArg graphVertex (Subsingleton.elim (graphVertexUnderlying v) default)
  | inr w =>
    rcases w with ⟨eb,t⟩
    let e : Quiver.Total (Vertex S) := graphEdgeUnderlying eb
    change graphEdgePath e t = base S ∨ _
    by_cases ht0 : t = 0
    · left
      rw [ht0,graphEdgePath_zero]
      exact congrArg graphVertex (Subsingleton.elim e.left default)
    by_cases ht1 : t = 1
    · left
      rw [ht1,graphEdgePath_one]
      exact congrArg graphVertex (Subsingleton.elim e.right default)
    · right
      have hp : 0 < t := lt_of_le_of_ne (unitInterval.nonneg t) (Ne.symm ht0)
      have hq : t < 1 := lt_of_le_of_ne (unitInterval.le_one t) ht1
      refine ⟨⟨edgeIndexEquiv S e,⟨t,hp,hq⟩⟩,?_⟩
      dsimp only [bouquetAllInteriors,ContinuousMap.coe_mk,edgeInterior]
      change graphEdgePath ((edgeIndexEquiv S).symm (edgeIndexEquiv S e)) t = _
      rw [(edgeIndexEquiv S).symm_apply_apply]
      rfl

theorem bouquet_base_interior_separated (p : Σ _ : S, Ioo (0 : I) 1) :
    Separated (base S) (bouquetAllInteriors S p) := by
  apply separated_continuous (bouquetHeight S)
  dsimp only [bouquetHeight,ContinuousMap.coe_mk,bouquetAllInteriors,edgeInterior,
    base,graphVertex,graphEdgePath,graphRealizationQuotient,Quotient.lift_mk,rawBouquetHeight]
  change (0 : ℝ) ≠ min p.2.val.val (1-p.2.val.val)
  apply ne_of_lt
  apply lt_min
  · exact p.2.property.1
  · have h := p.2.property.2
    change p.2.val.val < 1 at h
    linarith

/-- The genuine weak endpoint quotient is Hausdorff for arbitrary generator types. -/
instance bouquet_t2Space : T2Space (Bouquet S) where
  t2 x y hxy := by
    rcases bouquet_point_cases S x with rfl | ⟨p,rfl⟩
    · rcases bouquet_point_cases S y with rfl | ⟨q,rfl⟩
      · exact (hxy rfl).elim
      · exact bouquet_base_interior_separated S q
    · rcases bouquet_point_cases S y with rfl | ⟨q,rfl⟩
      · exact (bouquet_base_interior_separated S p).symm
      · exact separated_openEmbedding _ (bouquetAllInteriors_isOpenEmbedding S)
          (fun h => hxy (congrArg (bouquetAllInteriors S) h))
end Bouquet

section Attachment
variable {X : Type u} [TopologicalSpace X] {R : Type v}

def rawDiskRadius : CellAttachment.Raw X R → ℝ
  | Sum.inl _ => 1
  | Sum.inr p => ‖p.2.val‖

/-- The actual quotient disk radius, equal to one on the whole old base. -/
def attachmentRadius (f : R → C(Circle,X)) : C(CellAttachment.Space f,ℝ) where
  toFun := Quot.lift (rawDiskRadius (X := X) (R := R)) (by
    intro a b h
    cases h with
    | boundary i z => exact Circle.norm_coe z)
  continuous_toFun := by
    apply continuous_quot_lift
    have hc : Continuous (Sum.elim (fun _ : X => (1 : ℝ))
        (fun p : Σ _ : R, CellAttachment.Disk => ‖p.2.val‖)) := by
      apply Continuous.sumElim
      · exact continuous_const
      · apply continuous_sigma
        intro i
        exact continuous_subtype_val.norm
    exact hc.congr (fun z => by cases z <;> rfl)

theorem attachment_point_cases (f : R → C(Circle,X)) (z : CellAttachment.Space f) :
    (∃ x, CellAttachment.inclusion f x = z) ∨
      ∃ p : Σ _ : R, CellAttachment.OpenDisk, CellAttachment.interiorMap f p = z := by
  obtain ⟨a,rfl⟩ := (CellAttachment.quotientMap_isQuotientMap f).surjective z
  cases a with
  | inl x => exact Or.inl ⟨x,rfl⟩
  | inr p =>
    rcases p with ⟨i,z⟩
    by_cases hz : ‖z.val‖ = 1
    · exact Or.inl ⟨f i (CellAttachment.diskBoundaryPoint z hz),
        (CellAttachment.characteristic_boundary f i (CellAttachment.diskBoundaryPoint z hz)).symm⟩
    · have hz' : ‖z.val‖ < 1 := lt_of_le_of_ne z.property hz
      exact Or.inr ⟨⟨i,⟨z.val,hz'⟩⟩,rfl⟩

theorem attachment_old_points_separated [T2Space X]
    (f : R → C(Circle,X)) (x₀ x y : X) (hxy : x ≠ y) :
    Separated (CellAttachment.inclusion f x) (CellAttachment.inclusion f y) := by
  let r := CellAttachment.neighborhoodRetraction f x₀
  rcases t2_separation hxy with ⟨A,B,hA,hB,hx,hy,hd⟩
  have ho := (CellAttachment.puncturedNeighborhood_isOpen f).isOpenMap_subtype_val
  refine ⟨Subtype.val '' (r ⁻¹' A),Subtype.val '' (r ⁻¹' B),
    ho _ (hA.preimage r.continuous),ho _ (hB.preimage r.continuous),
    ⟨CellAttachment.neighborhoodInclusion f x,hx,rfl⟩,
    ⟨CellAttachment.neighborhoodInclusion f y,hy,rfl⟩,?_⟩
  apply disjoint_left.mpr
  rintro z ⟨a,ha,he⟩ ⟨b,hb,he'⟩
  have hab : a = b := Subtype.ext (he.trans he'.symm)
  subst b
  exact disjoint_left.mp hd ha hb

theorem attachment_old_interior_separated (f : R → C(Circle,X))
    (x : X) (p : Σ _ : R, CellAttachment.OpenDisk) :
    Separated (CellAttachment.inclusion f x) (CellAttachment.interiorMap f p) := by
  apply separated_continuous (attachmentRadius f)
  change (1 : ℝ) ≠ ‖p.2.val‖
  exact ne_of_gt p.2.property

/-- Genuine disk adjunctions preserve Hausdorffness, with no finite/countable restriction. -/
theorem attachment_t2Space [T2Space X] (f : R → C(Circle,X)) (x₀ : X) :
    T2Space (CellAttachment.Space f) := by
  constructor
  intro z w hzw
  rcases attachment_point_cases f z with ⟨x,rfl⟩ | ⟨p,rfl⟩
  · rcases attachment_point_cases f w with ⟨y,rfl⟩ | ⟨q,rfl⟩
    · exact attachment_old_points_separated f x₀ x y
        (fun h => hzw (congrArg (CellAttachment.inclusion f) h))
    · exact attachment_old_interior_separated f x q
  · rcases attachment_point_cases f w with ⟨y,rfl⟩ | ⟨q,rfl⟩
    · exact (attachment_old_interior_separated f y p).symm
    · exact separated_openEmbedding _ (CellAttachment.interiorMap_isOpenEmbedding f)
        (fun h => hzw (congrArg (CellAttachment.interiorMap f) h))
end Attachment

end PresentationComplex
