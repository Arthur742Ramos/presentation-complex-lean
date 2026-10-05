import PresentationComplex.Bouquet
import Mathlib.GroupTheory.FreeGroup.Reduce

/-! Actual finite word loops in the arbitrary weak bouquet. Mathlib multiplies
loop classes in reverse chronological order, and this recursion respects it. -/
noncomputable section
open Set
open Path.Homotopic
universe u
namespace PresentationComplex
variable {S : Type u}

/-- The positive or negative actual traversal of a labeled interval. -/
def signedEdgeLoop (l : S × Bool) : Path (base S) (base S) :=
  if l.2 then edgeLoop l.1 else (edgeLoop l.1).symm

/-- A finite word's continuous loop, in Mathlib's multiplication convention. -/
def wordLoop : List (S × Bool) → Path (base S) (base S)
  | [] => Path.refl (base S)
  | l :: w => (wordLoop w).trans (signedEdgeLoop l)

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

/-- The canonical finite representative chosen with classical equality internally. -/
def relatorWord (g : FreeGroup S) : List (S × Bool) := by
  classical
  exact g.toWord

/-- A chosen reduced representative, without any public decidable-equality hypothesis. -/
def relatorLoop (g : FreeGroup S) : Path (base S) (base S) := by
  classical
  exact wordLoop (relatorWord g)

theorem freeGroupEquiv_relatorLoop (g : FreeGroup S) :
    freeGroupEquiv S g = Path.Homotopic.Quotient.mk (relatorLoop g) := by
  classical
  simpa only [FreeGroup.mk_toWord,relatorLoop,relatorWord] using
    freeGroupEquiv_mk_wordLoop (FreeGroup.toWord g)

/-- The finite set of edge labels used by this representative. -/
def wordSupport (w : List (S × Bool)) : Finset S := by
  classical
  exact (w.map Prod.fst).toFinset

/-- The explicit finite subgraph containing a word loop's whole image. -/
def wordCarrier (w : List (S × Bool)) : Set (Bouquet S) :=
  {base S} ∪ ⋃ s ∈ wordSupport w, Set.range (edgeLoop s)

theorem wordLoop_range_subset (w : List (S × Bool)) :
    Set.range (wordLoop w) ⊆ wordCarrier w := by
  classical
  induction w with
  | nil => simp [wordLoop,wordCarrier]
  | cons l w ih =>
    rw [wordLoop,Path.trans_range]
    apply union_subset
    · exact ih.trans (by
        intro x hx
        rcases hx with hx | hx
        · exact Or.inl hx
        · right
          rcases mem_iUnion.mp hx with ⟨s,hs⟩
          rcases mem_iUnion.mp hs with ⟨hs,hx⟩
          exact mem_iUnion.mpr ⟨s,mem_iUnion.mpr ⟨by
            simpa [wordSupport] using Or.inr hs,hx⟩⟩)
    · intro x hx
      right
      refine mem_iUnion.mpr ⟨l.1,mem_iUnion.mpr ⟨by simp [wordSupport],?_⟩⟩
      cases l with
      | mk s b =>
        cases b <;> simpa [signedEdgeLoop,Path.symm_range] using hx

end PresentationComplex
