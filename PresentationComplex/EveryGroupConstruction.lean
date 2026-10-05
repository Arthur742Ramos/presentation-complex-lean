module

public import PresentationComplex.Relators

@[expose] public section

/-! Construction-only data for the every-group realization challenge.
No CW structure, Hausdorffness, or fundamental-group realization proof is imported. -/
noncomputable section
universe u
namespace PresentationComplex
variable (G : Type u) [Group G]

/-- One relator for every multiplication table entry, plus the identity generator. -/
def groupRelators : (G × G) ⊕ PUnit.{u+1} → FreeGroup G
  | Sum.inl (g,h) => FreeGroup.of g * FreeGroup.of h * (FreeGroup.of (g*h))⁻¹
  | Sum.inr _ => FreeGroup.of (1 : G)


/-- The actual complex associated to the multiplication-and-identity presentation. -/
abbrev EveryGroupSpace (G : Type u) [Group G] := Space (groupRelators G)

/-- Its actual distinguished zero-cell. -/
def everyGroupPoint (G : Type u) [Group G] : EveryGroupSpace G := point (groupRelators G)

end PresentationComplex
