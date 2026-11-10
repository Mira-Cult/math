import PASoundness.PAtoCompactSuccTermSpareAlpha
import PASoundness.PAtoCompactSuccTermTotality

/-! Extracting the actual private child graph of a successor term into a
fresh, explicitly named witness. This is finite K proof data, not a proof of
term-graph existence, functionality, quotient cancellation, or PA axioms. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactSuccGraphExtractSpareWitness

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactSuccTermTotality
open PASoundness.PAtoCompactSuccTermSpareAlpha

/-- From the actual successor graph, retain the output-domain condition and
extract its child graph together with the quotient-successor relation at a
fresh spare witness. Distinct source variables may use the same name; the
spare must differ from the output and every mapped child variable. -/
def extract_spare {α : Type} [DecidableEq α] (v : α → Nat)
    (t : Peano.language.Term α) (out b w : Nat)
    (hw : w < b) (hout : out < b) (hwo : w ≠ out)
    (hvars : ∀ a ∈ t.varFinset, v a < b ∧ v a ≠ w) :
    KDerivation (imp (termGraph v (.func .succ ![t]) out b).encode
      (both (domainAt b out).encode
        (existsCode w (spareBody v t out b w).encode))) := by
  let T := termGraph v (.func .succ ![t]) out b
  let F := succBody v t out b
  let Γ := [T.encode]
  have ht : Context Γ (both (domainAt b out).encode (existsCode b F.encode)) := by
    have hh := Context.head [] T.encode
    simpa [Γ, T, F, succBody, termGraph, andF, CompactNamed.Formula.not,
      CompactNamed.Formula.encode, both, neg, existsCode] using hh
  have hd := Context.conjunctionLeft ht
  have he := Context.conjunctionRight ht
  have ha := (succBody_spare_alpha v t out b w hw hout hwo hvars).forward
  have he' : Context Γ (existsCode w (spareBody v t out b w).encode) := by
    apply Context.mp he
    simpa only [CompactNamed.Formula.encode] using Context.closed ha
  exact Context.closeEmpty (Context.deduction (Context.conjunctionIntro hd he'))

theorem extract_spare_certificate {α : Type} [DecidableEq α] (v : α → Nat)
    (t : Peano.language.Term α) (out b w : Nat)
    (hw : w < b) (hout : out < b) (hwo : w ≠ out)
    (hvars : ∀ a ∈ t.varFinset, v a < b ∧ v a ≠ w) :
    theoremCode (certificate (extract_spare v t out b w hw hout hwo hvars)) =
      imp (termGraph v (.func .succ ![t]) out b).encode
        (both (domainAt b out).encode (existsCode w (spareBody v t out b w).encode)) :=
  certificate_correct _

end PASoundness.PAtoCompactSuccGraphExtractSpareWitness

#print axioms PASoundness.PAtoCompactSuccGraphExtractSpareWitness.extract_spare
#print axioms PASoundness.PAtoCompactSuccGraphExtractSpareWitness.extract_spare_certificate
