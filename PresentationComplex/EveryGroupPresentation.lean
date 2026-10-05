module

public import PresentationComplex.EveryGroupConstruction
public import CellAttachment.GroupQuotient

@[expose] public section

/-! Every group has an explicit multiplication-and-identity presentation.
This is an algebraic ingredient only; the topological realization uses the
separately constructed actual presentation complex. -/
noncomputable section
open Set
universe u
namespace PresentationComplex
variable (G : Type u) [Group G]


abbrev groupNormalClosure := Subgroup.normalClosure (Set.range (groupRelators G))
abbrev GroupPresentation := FreeGroup G ⧸ groupNormalClosure G

/-- The genuine free-group evaluation homomorphism. -/
def groupEvaluation : FreeGroup G →* G := FreeGroup.lift id

theorem groupEvaluation_relator (i : (G × G) ⊕ PUnit.{u+1}) :
    groupEvaluation G (groupRelators G i) = 1 := by
  cases i with
  | inl p => cases p; simp [groupRelators,groupEvaluation]
  | inr _ => simp [groupRelators,groupEvaluation]

/-- The quotient projection associated to this explicit presentation. -/
def groupProjection : FreeGroup G →* GroupPresentation G :=
  QuotientGroup.mk' (groupNormalClosure G)

theorem groupProjection_relator (i : (G × G) ⊕ PUnit.{u+1}) :
    groupProjection G (groupRelators G i) = 1 :=
  (QuotientGroup.eq_one_iff _).mpr
    (Subgroup.subset_normalClosure (Set.mem_range_self i))

/-- Evaluation descends because the actual specified relations evaluate to one. -/
def presentationEvaluation : GroupPresentation G →* G :=
  CellAttachment.liftNormalClosure (groupRelators G) (groupEvaluation G)
    (groupEvaluation_relator G)

/-- The inverse uses the generator indexed by each element of the group. -/
def groupToPresentation : G →* GroupPresentation G where
  toFun g := groupProjection G (FreeGroup.of g)
  map_one' := groupProjection_relator G (Sum.inr PUnit.unit)
  map_mul' g h := by
    have hk := groupProjection_relator G (Sum.inl (g,h))
    have hk' : groupProjection G (FreeGroup.of g) * groupProjection G (FreeGroup.of h) *
        (groupProjection G (FreeGroup.of (g*h)))⁻¹ = 1 := by
      simpa only [groupRelators,map_mul,map_inv] using hk
    exact (mul_inv_eq_one.mp hk').symm

@[simp] theorem presentationEvaluation_generator (g : G) :
    presentationEvaluation G (groupProjection G (FreeGroup.of g)) = g := by
  simp only [presentationEvaluation,groupProjection,
    CellAttachment.liftNormalClosure_mk,groupEvaluation,FreeGroup.lift_apply_of,id_eq]

/-- No kernel oracle: both inverse equations are proved from generators and relations. -/
def groupPresentationEquiv : GroupPresentation G ≃* G where
  toFun := presentationEvaluation G
  invFun := groupToPresentation G
  left_inv := by
    intro x
    have he : (groupToPresentation G).comp (presentationEvaluation G) =
        MonoidHom.id (GroupPresentation G) := by
      apply QuotientGroup.monoidHom_ext
      apply FreeGroup.lift.symm.injective
      funext g
      change groupToPresentation G
        (presentationEvaluation G (groupProjection G (FreeGroup.of g))) =
          groupProjection G (FreeGroup.of g)
      rw [presentationEvaluation_generator]
      rfl
    exact DFunLike.congr_fun he x
  right_inv := presentationEvaluation_generator G
  map_mul' := (presentationEvaluation G).map_mul

@[simp] theorem groupPresentationEquiv_generator (g : G) :
    groupPresentationEquiv G (groupProjection G (FreeGroup.of g)) = g :=
  presentationEvaluation_generator G g

end PresentationComplex
