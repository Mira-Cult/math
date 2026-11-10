import PASoundness.PAtoCompactSuccGraphOutputClosed
import PASoundness.PAtoCompactDynamicSymmetry

/-! Reverse successor graph output transport, obtained from finite K
candidate-relative symmetry and the forward graph transport. -/
namespace PASoundness.PAtoCompactSuccGraphOutputReverse

open FirstOrder FirstOrder.Language
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactSuccGraphOutputClosed
open PASoundness.PAtoCompactDynamicSymmetry

/-- An equivalent candidate can replace the existing output of a successor
graph. The required candidate condition is retained at the new output; all
source and output labels lie below the graph's existential witness. -/
noncomputable def succ_graph_output_reverse {α : Type} [DecidableEq α]
    (v : α → Nat) (t : Peano.language.Term α) (b q r : Nat)
    (hq : q < b) (hr : r < b) (hv : ∀ a ∈ t.varFinset, v a < b) :
    KDerivation (imp (domainAt b q).encode
      (imp (termGraph v (.func .succ ![t]) r b).encode
        (imp (equivAt b q r).encode (termGraph v (.func .succ ![t]) q b).encode))) := by
  have hs := dynamic_symmetry b q r (by omega) (by omega)
  have hf := succ_graph_output v t b r q hr hq hv
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let D := (domainAt b q).encode
  let G := (termGraph v (.func .succ ![t]) r b).encode
  let E := (equivAt b q r).encode
  let Γ := [E, G, D]
  have hd : Context Γ D := .hypothesis (by simp [Γ])
  have hg : Context Γ G := .hypothesis (by simp [Γ])
  have he : Context Γ E := Context.head _ _
  have her := Context.mp he (Context.mp hd (.closed hs))
  exact .mp her (.mp hg (.mp hd (.closed hf)))

theorem succ_graph_output_reverse_certificate {α : Type} [DecidableEq α]
    (v : α → Nat) (t : Peano.language.Term α) (b q r : Nat)
    (hq : q < b) (hr : r < b) (hv : ∀ a ∈ t.varFinset, v a < b) :
    theoremCode (certificate (succ_graph_output_reverse v t b q r hq hr hv)) =
      imp (domainAt b q).encode
        (imp (termGraph v (.func .succ ![t]) r b).encode
          (imp (equivAt b q r).encode (termGraph v (.func .succ ![t]) q b).encode)) :=
  certificate_correct _

end PASoundness.PAtoCompactSuccGraphOutputReverse

#print axioms PASoundness.PAtoCompactSuccGraphOutputReverse.succ_graph_output_reverse
#print axioms PASoundness.PAtoCompactSuccGraphOutputReverse.succ_graph_output_reverse_certificate
