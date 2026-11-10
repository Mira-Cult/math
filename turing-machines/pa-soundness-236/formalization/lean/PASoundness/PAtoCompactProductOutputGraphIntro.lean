import PASoundness.PAtoCompactProductOutputGraphAlpha

/-! Introduce the actual graph-9 witness despite an inner binder also named
9: first move the inner binder to 65 constructively, introduce 9, restore the
inner syntax and apply the scoped graph-witness alpha conversion. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductOutputGraphIntro

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactProductOutputPartialBase PASoundness.PAtoCompactProductOutputAdjoinInvariant9
open PASoundness.PAtoCompactProductOutputGraphAlpha

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

theorem graph_nine_not_inner_binder : 9 ∉ (shift9 nextInvariant9).binders := by decide

/-- A proved invariant for the concrete free graph 9 supplies the required
existential graph-58 invariant, with all inner scopes kept capture-safe. -/
noncomputable def introduce_graph : KDerivation (imp nextInvariant9.encode
    (existsCode 58 partialInvariant.encode)) := by
  have hforward := (shift_equiv nextInvariant9 next_safe).forward
  have hintro := existsIntroduce 9 (shift9 nextInvariant9) graph_nine_not_inner_binder
  have hrestore := existsCongr 9 (shift_equiv nextInvariant9 next_safe).backward
  exact compose hforward (compose hintro (compose hrestore graph_existential_alpha))

theorem introduce_graph_certificate : theoremCode (certificate introduce_graph) =
    imp nextInvariant9.encode (existsCode 58 partialInvariant.encode) := certificate_correct _

end PASoundness.PAtoCompactProductOutputGraphIntro

#print axioms PASoundness.PAtoCompactProductOutputGraphIntro.introduce_graph
#print axioms PASoundness.PAtoCompactProductOutputGraphIntro.introduce_graph_certificate
