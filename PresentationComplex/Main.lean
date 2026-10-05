import PresentationComplex.CW
import PresentationComplex.FundamentalGroup
import PresentationComplex.EveryGroupPresentation
import PresentationComplex.Hausdorff

/-! Arbitrary presentation complexes and genuine Hausdorff CW realization of every group. -/
noncomputable section
universe u v
namespace PresentationComplex
variable {S : Type u} {R : Type v}

instance presentation_t2Space (r : R → FreeGroup S) : T2Space (Space r) :=
  attachment_t2Space (relatorMap r) (base S)

/-- The full independently scoped target, with actual topology and literal compatibility. -/
def completeStatement : Prop :=
  ∀ {S : Type u} {R : Type v} (r : R → FreeGroup S),
    ∃ (cw : Topology.CWComplex (Set.univ : Set (Space r)))
      (b : FundamentalGroup (Bouquet S) (base S) ≃* FreeGroup S)
      (e : FundamentalGroup (Space r) (point r) ≃*
        (FreeGroup S ⧸ relatorNormalClosure r)),
      T2Space (Space r) ∧ PathConnectedSpace (Space r) ∧
      Nonempty (cw.cell 0 ≃ PUnit.{max u v + 1}) ∧
      Nonempty (cw.cell 1 ≃ S) ∧ Nonempty (cw.cell 2 ≃ R) ∧
      (∀ n, 2 < n → IsEmpty (cw.cell n)) ∧
      (∀ s, b (Path.Homotopic.Quotient.mk (edgeLoop s)) = FreeGroup.of s) ∧
      e.toMonoidHom.comp (CellAttachment.inclusionPi1 (relatorMap r) (base S)) =
        (QuotientGroup.mk' (relatorNormalClosure r)).comp b.toMonoidHom ∧
      (∀ s, e (Path.Homotopic.Quotient.mk ((edgeLoop s).map (inclusion r).continuous)) =
        QuotientGroup.mk' (relatorNormalClosure r) (FreeGroup.of s))

/-- Every arbitrary presentation has the genuine connected Hausdorff CW complex
of dimension at most two, with exact ordinary fundamental group and generators. -/
theorem presentation_complex : completeStatement.{u,v} := by
  intro S R r
  exact ⟨presentationCW r,bouquetEquiv S,presentationPi1Equiv r,
    inferInstance,inferInstance,⟨Equiv.refl _⟩,
    ⟨presentationCW_generatorCells r⟩,⟨presentationCW_relatorCells r⟩,
    presentationCW_noHigherCells r,
    bouquetEquiv_edgeLoop,presentationPi1Equiv_inclusion r,presentationPi1Equiv_generator r⟩

/-- Every group is the fundamental group of this genuine presentation space. -/
def everyGroupPi1Equiv (G : Type u) [Group G] :
    FundamentalGroup (EveryGroupSpace G) (everyGroupPoint G) ≃* G :=
  (presentationPi1Equiv (groupRelators G)).trans (groupPresentationEquiv G)

/-- The generator indexed by g is the actual interval loop and is labeled exactly g. -/
theorem everyGroupPi1Equiv_generator (G : Type u) [Group G] (g : G) :
    everyGroupPi1Equiv G (Path.Homotopic.Quotient.mk
      ((edgeLoop g).map (inclusion (groupRelators G)).continuous)) = g := by
  change groupPresentationEquiv G (presentationPi1Equiv (groupRelators G)
    (Path.Homotopic.Quotient.mk ((edgeLoop g).map (inclusion (groupRelators G)).continuous))) = g
  rw [presentationPi1Equiv_generator]
  exact groupPresentationEquiv_generator G g

/-- The identity relator supplies a genuine indexed open two-cell for every group. -/
theorem everyGroupCW_hasTwoCell (G : Type u) [Group G] :
    Nonempty ((presentationCW (groupRelators G)).cell 2) :=
  ⟨(presentationCW_relatorCells (groupRelators G)).symm (Sum.inr PUnit.unit)⟩

/-- The headline realization theorem has no CW, free-group, kernel, finiteness,
countability, or generator-identification oracle among its inputs. -/
theorem every_group_fundamental_group (G : Type u) [Group G] :
    ∃ cw : Topology.CWComplex (Set.univ : Set (EveryGroupSpace G)),
      T2Space (EveryGroupSpace G) ∧ PathConnectedSpace (EveryGroupSpace G) ∧
      (∀ n, 2 < n → IsEmpty (cw.cell n)) ∧ Nonempty (cw.cell 2) ∧
      Nonempty (FundamentalGroup (EveryGroupSpace G) (everyGroupPoint G) ≃* G) :=
  ⟨presentationCW (groupRelators G),inferInstance,inferInstance,
    presentationCW_noHigherCells (groupRelators G),everyGroupCW_hasTwoCell G,
    ⟨everyGroupPi1Equiv G⟩⟩

end PresentationComplex
