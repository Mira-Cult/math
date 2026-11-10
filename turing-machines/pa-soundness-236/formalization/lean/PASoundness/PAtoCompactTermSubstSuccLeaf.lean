import PASoundness.PAtoCompactUnaryGraphFunctionalityFull
import PASoundness.PAtoCompactSuccGraphOutputClosed
import PASoundness.PAtoCompactSuccTermTotality

/-! The variable occurrence of a source term, after replacing that variable
with a successor term. The same term-graph witness is retained in both K
directions; no truth theorem is used. -/
namespace PASoundness.PAtoCompactTermSubstSuccLeaf

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactUnaryTermTransport
open PASoundness.PAtoCompactUnaryGraphFunctionalityFull
open PASoundness.PAtoCompactSuccGraphOutputClosed PASoundness.PAtoCompactSuccTermTotality

set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Replace a variable-graph output by the graph of the successor term, given
the successor graph at the variable's value name. Variable and output labels
may coincide. All labels remain below the actual graph allocator. -/
noncomputable def succ_leaf_forward {α : Type} [DecidableEq α] (v : α → Nat)
    (u : Peano.language.Term α) (b q r : Nat)
    (hq : q < b) (hr : r < b) (hv : ∀ a ∈ u.varFinset, v a < b) :
    KDerivation (imp (termGraph v (.func .succ ![u]) q b).encode
      (imp (termGraph id (.var q : Peano.Term) r b).encode
        (termGraph v (.func .succ ![u]) r b).encode)) := by
  have ho := succ_graph_output v u b q r hq hr hv
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let G := (termGraph v (.func .succ ![u]) q b).encode
  let V := (termGraph id (.var q : Peano.Term) r b).encode
  let Γ := [V, G]
  have hG : Context Γ G := .hypothesis (by simp [Γ])
  have hV : Context Γ V := Context.head _ _
  have hD : Context Γ (domainAt b r).encode := Context.conjunctionLeft hV
  have hE : Context Γ (equivAt b q r).encode := Context.conjunctionRight hV
  exact .mp hE (.mp hG (.mp hD (.closed ho)))

/-- In the reverse direction, unary graph functionality gives the required
quotient equivalence. Candidate inputs for the term's variables are supplied
by actual K derivations from the guard, not assumed as semantic truth. -/
noncomputable def succ_leaf_reverse {α : Type} [DecidableEq α] (v : α → Nat)
    (g : Formula) (u : Peano.language.Term α) (hu : UnaryTerm u)
    (b q r : Nat) (hq : q < b) (hr : r < b)
    (hv : ∀ a ∈ u.varFinset, v a < b) (hg : ∀ x ∈ g.free, x < b)
    (hd : ∀ a ∈ u.varFinset, KDerivation (imp g.encode (domainAt b (v a)).encode)) :
    KDerivation (imp g.encode
      (imp (termGraph v (.func .succ ![u]) q b).encode
        (imp (termGraph v (.func .succ ![u]) r b).encode
          (termGraph id (.var q : Peano.Term) r b).encode))) := by
  have hv' : ∀ a ∈ (.func .succ ![u] : Peano.language.Term α).varFinset, v a < b := by
    simpa [Term.varFinset] using hv
  have hd' : ∀ a ∈ (.func .succ ![u] : Peano.language.Term α).varFinset,
      KDerivation (imp g.encode (domainAt b (v a)).encode) := by
    intro a ha
    apply hd a
    simpa [Term.varFinset] using ha
  have hf := unary_functional v g (UnaryTerm.succ hu) b q r hv' hg hd' hq hr
  have hdom := termGraph_domain v (.func .succ ![u]) r b
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let G := (termGraph v (.func .succ ![u]) q b).encode
  let T := (termGraph v (.func .succ ![u]) r b).encode
  let Γ := [T, G, g.encode]
  have hg' : Context Γ g.encode := .hypothesis (by simp [Γ])
  have hG : Context Γ G := .hypothesis (by simp [Γ])
  have hT : Context Γ T := Context.head _ _
  have hD : Context Γ (domainAt b r).encode := .mp hT (.closed hdom)
  have hE : Context Γ (equivAt b q r).encode := .mp hT (.mp hG (.mp hg' (.closed hf)))
  exact Context.conjunctionIntro hD hE

end PASoundness.PAtoCompactTermSubstSuccLeaf

#print axioms PASoundness.PAtoCompactTermSubstSuccLeaf.succ_leaf_forward
#print axioms PASoundness.PAtoCompactTermSubstSuccLeaf.succ_leaf_reverse
