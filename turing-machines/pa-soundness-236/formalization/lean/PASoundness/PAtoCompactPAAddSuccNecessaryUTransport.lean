import PASoundness.PAtoCompactAllTermTransport
import PASoundness.PAtoCompactTermGraphReplace
import PASoundness.PAtoCompactScopedAlphaInvariant
import PASoundness.PAtoCompactFreeNames

/-! Capture-safe relabeling and allocator transport for an existential term
value. This is a finite K implication. It does not establish existence of the
source witness, term functionality, or an arithmetic axiom. -/
namespace PASoundness.PAtoCompactPAAddSuccNecessaryUTransport
open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactAllTermTransport
open PASoundness.PAtoCompactTermGraphReplace PASoundness.PAtoCompactTermGraphBinderRange
open PASoundness.PAtoCompactScopedAlphaInvariant PASoundness.PAtoCompactFreeNames
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- An existential term-graph output may be renamed to a fresh source name,
then transported to another allocation base. Source/target variables may
alias each other; the two binder labels must be distinct from all mapped term
variables; the old name is below `b` and the new name is below both bases. -/
noncomputable def existential_graph_transport {α : Type} [DecidableEq α]
    (v : α → Nat) (t : Peano.language.Term α) (b c old new : Nat)
    (hob : old < b) (hnb : new < b) (hnc : new < c)
    (hvb : ∀ a ∈ t.varFinset, v a < b)
    (hvc : ∀ a ∈ t.varFinset, v a < c)
    (hold : ∀ a ∈ t.varFinset, v a ≠ old)
    (hnew : ∀ a ∈ t.varFinset, v a ≠ new) :
    KDerivation (imp (existsCode old (termGraph v t old b).encode)
      (existsCode new (termGraph v t new c).encode)) := by
  have hm := (termGraph_base_transport v t b c new hnb hnc hvb hvc).1
  have hc := existsCongr new hm
  by_cases h : old = new
  · subst new
    exact hc
  · have hb : old ∉ (termGraph v t old b).binders :=
      termGraph_below_not_binder v t old b old hob
    have hn : new ∉ (termGraph v t old b).names := by
      intro he
      rw [Formula.names_eq_free_union_binders] at he
      rcases Finset.mem_union.mp he with hf | hb'
      · have hf' := termGraph_free_subset v t old b hf
        rcases Finset.mem_union.mp hf' with hvar | hout
        · obtain ⟨a, ha, heq⟩ := Finset.mem_image.mp hvar
          exact (hnew a ha) heq
        · have hh := Finset.mem_singleton.mp hout
          exact h hh.symm
      · exact termGraph_below_not_binder v t old b new hnb hb'
    have hr : replace old new (termGraph v t old b) = termGraph v t new b := by
      rw [replace_termGraph v t old b old new hob]
      have hv : ∀ a ∈ t.varFinset, (rename old new ∘ v) a = v a := by
        intro a ha
        simp [rename, hold a ha]
      rw [termGraph_name_agree t (rename old new ∘ v) v hv]
      simp [rename]
    have ha := (existentialAlpha old new (termGraph v t old b) h hb hn).1
    rw [hr] at ha
    exact compose ha hc

theorem existential_graph_transport_certificate {α : Type} [DecidableEq α]
    (v : α → Nat) (t : Peano.language.Term α) (b c old new : Nat)
    (hob : old < b) (hnb : new < b) (hnc : new < c)
    (hvb : ∀ a ∈ t.varFinset, v a < b)
    (hvc : ∀ a ∈ t.varFinset, v a < c)
    (hold : ∀ a ∈ t.varFinset, v a ≠ old)
    (hnew : ∀ a ∈ t.varFinset, v a ≠ new) :
    theoremCode (certificate (existential_graph_transport v t b c old new hob hnb hnc hvb hvc hold hnew)) =
      imp (existsCode old (termGraph v t old b).encode)
        (existsCode new (termGraph v t new c).encode) := certificate_correct _
end PASoundness.PAtoCompactPAAddSuccNecessaryUTransport
#print axioms PASoundness.PAtoCompactPAAddSuccNecessaryUTransport.existential_graph_transport
#print axioms PASoundness.PAtoCompactPAAddSuccNecessaryUTransport.existential_graph_transport_certificate
