module

public import PresentationComplex.WordLoopConstruction
public import PresentationComplex.Bouquet
public import Mathlib.GroupTheory.FreeGroup.Reduce

@[expose] public section

/-! Actual finite word loops in the arbitrary weak bouquet. Mathlib multiplies
loop classes in reverse chronological order, and this recursion respects it. -/
noncomputable section
open Set
open Path.Homotopic
universe u
namespace PresentationComplex
variable {S : Type u}

theorem freeGroupEquiv_mk_wordLoop (w : List (S × Bool)) :
    freeGroupEquiv S (FreeGroup.mk w) = Path.Homotopic.Quotient.mk (wordLoop w) := by
  induction w with
  | nil =>
    change freeGroupEquiv S 1 = (1 : FundamentalGroup (Bouquet S) (base S))
    exact (freeGroupEquiv S).map_one
  | cons l w ih =>
    rw [show FreeGroup.mk (l :: w) = FreeGroup.mk [l] * FreeGroup.mk w from
      rfl, map_mul, ih]
    have hsigned : freeGroupEquiv S (FreeGroup.mk [l]) = Path.Homotopic.Quotient.mk (signedEdgeLoop l) := by
      cases l with
      | mk s b =>
        cases b
        · rw [show FreeGroup.mk [(s,false)] = (FreeGroup.of s)⁻¹ from rfl,
            map_inv,freeGroupEquiv_of]
          rfl
        · exact freeGroupEquiv_of s
    rw [hsigned]
    rfl

theorem freeGroupEquiv_relatorLoop (g : FreeGroup S) :
    freeGroupEquiv S g = Path.Homotopic.Quotient.mk (relatorLoop g) := by
  classical
  simpa only [FreeGroup.mk_toWord,relatorLoop,relatorWord] using
    freeGroupEquiv_mk_wordLoop (FreeGroup.toWord g)

end PresentationComplex
