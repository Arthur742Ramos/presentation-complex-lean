# Independent statement review

Reviewed 2026-10-05 against graph source `dd57e3ab8bc5a7042fcc5498e778b008d87ac032`, cell source `8883b95e8ace951e27c2bc86f95d02397787dd59`, and Mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55` / Lean `4.35.0-rc2`.

## Verdict and scope

The requested arbitrary presentation-complex theorem is mathematically correct. It works for independent generator and relator universes, without finite or countable hypotheses, when the bouquet and disk adjunction carry their actual weak quotient topologies. This review approves the target's scope and compatibility requirements; it does **not** certify an implementation or an exact-toolchain port of the graph source.

No free-group, CW, generator, relator-representation, or attachment oracle is an acceptable hypothesis. The bouquet equivalence, attaching maps, CW structure, and compatibility equations must be constructed and proved. Standard Lean logical axioms such as classical choice are not custom mathematical axioms.

The graph comparison at `FiniteGraphFreeGroup/TopologicalComparison.lean:1807` needs only `WeaklyConnected`; the following finite-rank theorem does need finiteness and must not be substituted. The frozen cell theorem supplies genuine adjunction and actual inclusion compatibility in independent universes. The graph repository uses Lean 4.32, so importing its textual proof into the 4.35 target still requires port verification.

## Recommended complete statement

Use fixed, implemented definitions, rather than existentially unspecified spaces:

- `Bouquet S`: the quotient of one explicit vertex together with one interval for each `s : S`, identifying both endpoints with that vertex
- `base S`, `edgeLoop S s`: that vertex and the actual interval traversal
- `relatorMap r : R → C(Circle, Bouquet S)`: a circle map constructed from a finite word representing each `r i`, based at `base S`
- `Space r := CellAttachment.Space (relatorMap r)` and `point r := CellAttachment.inclusion _ (base S)`
- `j r := CellAttachment.inclusion (relatorMap r)`
- `N r := Subgroup.normalClosure (Set.range r)`

The following is a specification skeleton, with those definitions still to be implemented:

```lean
universe u v

def completeStatement : Prop :=
  ∀ {S : Type u} {R : Type v} (r : R → FreeGroup S),
  ∃ (cw : Topology.CWComplex (Set.univ : Set (Space r)))
    (b : FundamentalGroup (Bouquet S) (base S) ≃* FreeGroup S)
    (e : FundamentalGroup (Space r) (point r) ≃*
      (FreeGroup S ⧸ N r)),
    PathConnectedSpace (Space r) ∧
    (∀ n, 2 < n → IsEmpty (cw.cell n)) ∧
    (∀ s, b (.mk (edgeLoop S s)) = FreeGroup.of s) ∧
    e.toMonoidHom.comp (FundamentalGroup.map (j r) (base S)) =
      (QuotientGroup.mk' (N r)).comp b.toMonoidHom ∧
    (∀ s, e (.mk ((edgeLoop S s).map (j r).continuous)) =
      QuotientGroup.mk' (N r) (FreeGroup.of s))
```

The final equation follows from the preceding equations, but is worth exposing as a named generator compatibility theorem. The actual relator bridge must also prove that `b` sends each specified whiskered attaching loop class to `r i`; this is a proof obligation, not an assumed input.

Prefer a named canonical CW structure whose 0-, 1-, and 2-cell types are respectively one point, a universe lift of `S`, and a universe lift of `R`; higher cell types are empty. This explicitly preserves every indexed disk.

## Universe and multiplication hazards

1. `Space r` naturally lives in `Type (max u v)`. Mathlib's `CWComplex` cell types live in the ambient space's universe. Lift the cell indices as needed; do not impose `u = v` or shrink either index type.
2. Exact Mathlib defines `Quiver.SingleObj S : Type` as a Unit tag, with arrows in the universe of `S`. It is not already a `Type u` vertex. The graph comparison ties vertex and arrow universes through `{V : Type u} [Quiver.{u} V]`. A tiny exact-toolchain probe confirmed that naïvely applying this same-universe API to `Quiver.SingleObj S` fails instance synthesis for arbitrary `u`. A vertex type `PUnit.{u+1}` with `Hom _ _ := S` passes the corresponding probe. Use it or prove a universe-lift adapter.
3. Exact Mathlib has `FundamentalGroup.mul_def : p * q = q.trans p`. Thus chronological left-to-right traversal of a word represents the reversed algebraic product. One correct recursion is `wordLoop [] := Path.refl base` and `wordLoop (letter :: tail) := (wordLoop tail).trans (signedGenerator letter)`. Prove its class equals the free-group lift of `FreeGroup.mk`; do not rely on informal multiplication conventions.
4. Mathlib's characteristic maps use `Fin n → ℝ` with the maximum metric. Its 2-ball is a square, whereas the attachment's `Disk` is a complex Euclidean disk. An actual homeomorphism respecting interior, closure, and frontier is required. The proved convex-body homeomorphism theorem in `Mathlib/Analysis/Convex/GaugeRescale.lean` is one possible bridge.

## Required non-oracle lemmas

1. The one-vertex free groupoid's endomorphism group is `FreeGroup S`, with the actual edge-generator equations; combine it with the arbitrary graph comparison.
2. Explicit finite word loops, their algebraic class equation, and finite edge-support bounds. `FreeGroup.toWord` and `mk_toWord` in `FreeGroup/Reduce.lean` support this without a decidable-equality hypothesis in the public theorem; use classical equality internally.
3. Loop-to-circle descent through `circleGenerator`, proving the based value and equality or homotopy of the induced loop. The circle quotient/fiber fact must be proved, not assumed.
4. Genuine quotient normal forms and open interior embeddings for bouquet edges and disks, with disjoint cells, inverse continuity, characteristic continuity, and exhaustive union.
5. CW closure-finiteness from the finite support of each relator word. An arbitrary family is allowed because each individual word is finite.
6. CW weak topology from the actual quotient tests and the bouquet's weak topology. The cell source already proves the base inclusion is a closed embedding and the coproduct of disk interiors is an open embedding.
7. Target path-connectedness from representatives: connect bouquet points through the vertex and disk points by a disk path to the based attaching boundary. Do not infer it merely from fundamental-group surjectivity.
8. Transport of normal closures across the bouquet equivalence and of the cell theorem's quotient equivalence, preserving the actual inclusion equation.

## Every-group headline and edge cases

For any `G : Type u` with `[Group G]`, take generators `S := G` and relator indices `(G × G) ⊕ PUnit`, with multiplication relators `of g * of h * (of (g * h))⁻¹` and identity relator `of 1`. Prove the quotient equivalence to `G` using `FreeGroup.lift id` and the inverse `g ↦ [of g]`; then compose with the presentation-complex equivalence. Expose that the actual generator loop for `g` maps to `g`.

- Empty `S` still has the explicit vertex; an interval-only coproduct would incorrectly give the empty space
- Empty `R` gives the actual bouquet, with no disk cells
- Identity relators attach genuine constant-boundary disks, producing sphere summands rather than disappearing topologically
- Duplicate relators retain distinct indexed 2-cell interiors; their normal-closure redundancy does not authorize collapsing their disks
- Trivial `G` is covered by the same multiplication/identity presentation

## Verification boundary

No source modules were modified and no heavy compilation was run. A small probe using cached exact Mathlib imports checked the SingleObj/PUnit universe issue and accepted `cw.cell n` in the no-higher-cells predicate. Full graph-port, CW, attachment assembly, examples, and transitive `#print axioms` checks remain implementation requirements.
