/-
Adapted minimal arbitrary-graph interface from Arthur742Ramos/finite-graph-fundamental-group
commit dd57e3ab8bc5a7042fcc5498e778b008d87ac032, Apache-2.0.
Finite-rank spanning-tree/counting wrappers are intentionally excluded.
-/
import Mathlib.CategoryTheory.Groupoid.FreeGroupoid
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.Combinatorics.Quiver.Arborescence
import Mathlib.GroupTheory.FreeGroup.NielsenSchreier
open CategoryTheory Quiver
noncomputable section
universe u
namespace FiniteGraphFreeGroup
class WeaklyConnected (V : Type u) [Quiver.{u} V] : Prop where
  path : ∀ a b : V,
    Nonempty (@Quiver.Path (Symmetrify V) (Quiver.symmetrifyQuiver V) a b)
abbrev graphFundamentalGroup {V : Type u} [Quiver.{u} V] (root : V) :=
  End ((Quiver.FreeGroupoid.of V).obj root)
/-- An arborescence cannot contain an edge and its formal reverse. -/
lemma no_reverse_edges {V : Type u} [Quiver.{u} V]
    (T : WideSubquiver (Symmetrify V)) [hT : @Arborescence T T.quiver]
    {a b : V} (e : @Quiver.Hom V _ a b)
    (h₁ : T a b (Sum.inl e)) (h₂ : T b a (Sum.inr e)) : False := by
  let p : @Quiver.Path T T.quiver hT.root a := (hT.uniquePath a).default
  let q : @Quiver.Path T T.quiver hT.root b := (hT.uniquePath b).default
  let f : @Quiver.Hom T T.quiver a b := ⟨Sum.inl e, h₁⟩
  let g : @Quiver.Hom T T.quiver b a := ⟨Sum.inr e, h₂⟩
  have hpq : q = p.cons f := ((hT.uniquePath b).uniq _).symm
  have hqp : p = q.cons g := ((hT.uniquePath a).uniq _).symm
  have hpq_len : q.length = p.length + 1 :=
    congrArg (@Quiver.Path.length T T.quiver hT.root b) hpq
  have hqp_len : p.length = q.length + 1 :=
    congrArg (@Quiver.Path.length T T.quiver hT.root a) hqp
  omega
end FiniteGraphFreeGroup
