import PASoundness.PAtoCompactCandidateFixed
import PASoundness.PAtoCompactGuardBaseTransport
import PASoundness.PAtoCompactCandidateDynamicReflexivity
import PASoundness.PAtoCompactVariableTermTotality
import PASoundness.PAtoCompactSuccTermReplacement
import PASoundness.PAtoCompactMapNamesCongr
import PASoundness.PAtoCompactAlphaMapOne
import PASoundness.PAtoCompactFreeVacuity
import PASoundness.PAtoCompactQuotientSuccessorPackage

/-! Finite K ingredients for candidate-relative quotient-successor existence. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactSuccessorQuotientExistence

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactGuardBaseTransport
open PASoundness.PAtoCompactCandidateFixed PASoundness.PAtoCompactCandidateExact
open PASoundness.PAtoCompactAdjunction PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactCandidateDynamicReflexivity
open PASoundness.PAtoCompactMapNamesCongr PASoundness.PAtoCompactAlphaMapOne
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactGuardElimination
open PASoundness.PAtoCompactFreeNames PASoundness.PAtoCompactFreeVacuity
open PASoundness.PAtoCompactTransitiveWitness
open PASoundness.PAtoCompactQuotientSuccessorPackage

/-- A candidate has a raw successor that is again a candidate. The output
name is existentially bound; all freshness conditions concern syntax names. -/
def raw_candidate_successor (b x o : Nat) (hx : x < b+2) (ho : o < b)
    (hxo : x ≠ o) :
    KDerivation (imp (domainAt b x).encode
      (existsCode o (both (successorCode x o (b+10)) (domainAt b o).encode))) := by
  have hf : [x,o,b+10,b+32,b+33,b+34,b+40,b+41,b+42,b+35,b+36,b+38,b+39,
      b+43,b+37,b+44,b+45,b+46,b+47,b+100].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      not_false_eq_true, List.nodup_nil, and_true]
    omega
  have hp := predicate_names_lt x (b+100)
  have hwc : b+10 ≠ adjunctionPredicate x (b+100) := by omega
  have hoc : o ≠ adjunctionPredicate x (b+100) := by omega
  rw [domainAt_encode, domainAt_encode]
  exact fixed_candidate_successor_exists x o (b+10) (b+32) (b+33) (b+34)
    (b+40) (b+41) (b+42) (b+35) (b+36) (b+38) (b+39) (b+43) (b+37)
    (b+44) (b+45) (b+46) (b+47) (b+100) hf hwc hoc

/-- Existentially lift a supplied finite K packaging proof from a raw
candidate successor to the guarded quotient successor. -/
def quotient_exists_of_pack (b x o : Nat) (hx : x < b+2) (ho : o < b)
    (hxo : x ≠ o)
    (hpack : KDerivation (imp (domainAt b x).encode
      (imp (both (successorCode x o (b+10)) (domainAt b o).encode)
        (andF (domainAt b o) (succAt b x o)).encode))) :
    KDerivation (imp (domainAt (b+64) x).encode
      (existsCode o (andF (domainAt b o) (succAt b x o)).encode)) := by
  let D := (domainAt b x).encode
  let A := both (successorCode x o (b+10)) (domainAt b o).encode
  let B := (andF (domainAt b o) (succAt b x o)).encode
  have hv : KDerivation (imp D (allCode o D)) := by
    apply free_vacuity o (domainAt b x)
    intro h
    have he : o = x := Finset.mem_singleton.mp (domainAt_free b x h)
    exact hxo he.symm
  have hall : KDerivation (imp D (allCode o (imp A B))) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply generalizeOne o hv
    exact .mp (Context.head [] _) (.closed hpack)
  have hm : KDerivation (imp D (existsCode o B)) := by
    apply Context.closeEmpty
    apply Context.deduction
    let Γ := [D]
    have hd : Context Γ D := Context.head [] _
    have ha : Context Γ (existsCode o A) := .mp hd (.closed (raw_candidate_successor b x o hx ho hxo))
    have hh : Context Γ (allCode o (imp A B)) := .mp hd (.closed hall)
    exact exists_map_context hh ha
  exact compose (domainAt_transport (b+64) b x (by omega) (by omega)) hm

/-- Every candidate has a candidate quotient successor. The proof constructs
the raw candidate successor and packages it into the literal `succAt` graph;
no successor-closure or soundness premise remains. -/
def quotient_successor_exists (b x o : Nat) (hx : x < b+2) (ho : o < b)
    (hxo : x ≠ o) :
    KDerivation (imp (domainAt (b+64) x).encode
      (existsCode o (andF (domainAt b o) (succAt b x o)).encode)) :=
  quotient_exists_of_pack b x o hx ho hxo (package b x o hx ho)

theorem quotient_successor_exists_certificate (b x o : Nat) (hx : x < b+2)
    (ho : o < b) (hxo : x ≠ o) :
    theoremCode (certificate (quotient_successor_exists b x o hx ho hxo)) =
      imp (domainAt (b+64) x).encode
        (existsCode o (andF (domainAt b o) (succAt b x o)).encode) :=
  certificate_correct _

end PASoundness.PAtoCompactSuccessorQuotientExistence

#print axioms PASoundness.PAtoCompactSuccessorQuotientExistence.raw_candidate_successor
#print axioms PASoundness.PAtoCompactSuccessorQuotientExistence.quotient_exists_of_pack
#print axioms PASoundness.PAtoCompactSuccessorQuotientExistence.quotient_successor_exists
#print axioms PASoundness.PAtoCompactSuccessorQuotientExistence.quotient_successor_exists_certificate
