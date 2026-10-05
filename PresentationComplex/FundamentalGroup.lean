import PresentationComplex.Relators
import CellAttachment.Main

/-! The exact ordinary path-based fundamental group of the genuine quotient,
with literal bouquet-inclusion and generator compatibility. -/
noncomputable section
open Path.Homotopic
universe u v
namespace PresentationComplex
variable {S : Type u} {R : Type v}

/-- The actual inclusion-induced map, preceded by the proved bouquet equivalence. -/
def presentationMap (r : R → FreeGroup S) : FreeGroup S →*
    FundamentalGroup (Space r) (point r) :=
  (CellAttachment.inclusionPi1 (relatorMap r) (base S)).comp
    (freeGroupEquiv S).toMonoidHom

/-- The actual quotient inclusion is surjective with precisely the prescribed relators. -/
theorem presentationMap_exact (r : R → FreeGroup S) :
    Function.Surjective (presentationMap r) ∧
      (presentationMap r).ker = relatorNormalClosure r := by
  obtain ⟨hs,hk⟩ := CellAttachment.cell_attachment_exact
    (relatorMap r) (base S) (anchorPath r)
  have hrel : CellAttachment.attachingLoopClass (relatorMap r) (base S) (anchorPath r) =
      fun i => freeGroupEquiv S (r i) := funext (attachingLoopClass_eq r)
  have hk' : (CellAttachment.inclusionPi1 (relatorMap r) (base S)).ker =
      Subgroup.normalClosure (Set.range (fun i => freeGroupEquiv S (r i))) := by
    simpa only [CellAttachment.attachingNormalClosure,hrel] using hk
  exact CellAttachment.exact_comp_equiv (freeGroupEquiv S) r
    (CellAttachment.inclusionPi1 (relatorMap r) (base S)) hs hk'

/-- The proved inclusion-compatible quotient equivalence. -/
def quotientToPresentationPi1 (r : R → FreeGroup S) :
    (FreeGroup S ⧸ relatorNormalClosure r) ≃*
      FundamentalGroup (Space r) (point r) :=
  CellAttachment.quotientNormalClosureEquiv r (presentationMap r)
    (presentationMap_exact r).1 (presentationMap_exact r).2

/-- Label actual continuous loops by the presented group. -/
def presentationPi1Equiv (r : R → FreeGroup S) :
    FundamentalGroup (Space r) (point r) ≃*
      (FreeGroup S ⧸ relatorNormalClosure r) :=
  (quotientToPresentationPi1 r).symm

/-- Compatibility with the actual bouquet inclusion, not an unspecified map. -/
theorem presentationPi1Equiv_inclusion (r : R → FreeGroup S) :
    (presentationPi1Equiv r).toMonoidHom.comp
      (CellAttachment.inclusionPi1 (relatorMap r) (base S)) =
    (QuotientGroup.mk' (relatorNormalClosure r)).comp (bouquetEquiv S).toMonoidHom := by
  ext x
  obtain ⟨w,rfl⟩ := (freeGroupEquiv S).surjective x
  change presentationPi1Equiv r (presentationMap r w) =
    QuotientGroup.mk' (relatorNormalClosure r) ((freeGroupEquiv S).symm (freeGroupEquiv S w))
  rw [(freeGroupEquiv S).symm_apply_apply]
  rw [← CellAttachment.quotientNormalClosureEquiv_mk r (presentationMap r)
    (presentationMap_exact r).1 (presentationMap_exact r).2 w]
  exact (quotientToPresentationPi1 r).symm_apply_apply _

/-- The generator indexed by s is exactly the actual forward interval loop in the quotient. -/
theorem presentationPi1Equiv_generator (r : R → FreeGroup S) (s : S) :
    presentationPi1Equiv r (Path.Homotopic.Quotient.mk ((edgeLoop s).map (inclusion r).continuous)) =
      QuotientGroup.mk' (relatorNormalClosure r) (FreeGroup.of s) := by
  have h := DFunLike.congr_fun (presentationPi1Equiv_inclusion r) (Path.Homotopic.Quotient.mk (edgeLoop s))
  change presentationPi1Equiv r
      (Path.Homotopic.Quotient.mk ((edgeLoop s).map (inclusion r).continuous)) =
    QuotientGroup.mk' (relatorNormalClosure r) (bouquetEquiv S (Path.Homotopic.Quotient.mk (edgeLoop s))) at h
  rw [bouquetEquiv_edgeLoop] at h
  exact h

end PresentationComplex
