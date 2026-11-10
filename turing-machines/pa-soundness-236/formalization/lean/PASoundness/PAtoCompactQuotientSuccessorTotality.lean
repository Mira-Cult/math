import PASoundness.PAtoCompactCandidateDynamicReflexivity
import PASoundness.PAtoCompactAdjunction
import PASoundness.PAtoCompactCandidateFixed
import PASoundness.PAtoCompactGuardBaseTransport
import PASoundness.PAtoCompactFreeVacuity

/-! K proof-data ingredients for existence of the quotient successor. A raw
successor witness with its candidate guard is constructed; packaging it as a
quotient-successor witness remains separate. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactQuotientSuccessorTotality

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactAdjunction
open PASoundness.PAtoCompactCandidateFixed PASoundness.PAtoCompactGuardBaseTransport
open PASoundness.PAtoCompactFreeNames PASoundness.PAtoCompactFreeVacuity

def rawAt (base a w : Nat) : Formula := .all (base+10) (namedSuccessorBody a w (base+10))

def matrix (base a out w : Nat) : Formula :=
  andF (domainAt base a) (andF (domainAt base out) (andF (domainAt base w)
    (andF (rawAt base a w) (equivAt base w out))))

theorem equiv_normal : normalizeBottom equivalentFormula = equivalentFormula := by decide

theorem successor_shape (base a out : Nat) :
    succAt base a out = .ex (base+9) (matrix base a out (base+9)) := by
  rfl

/-- A quotient-successor record supplies the candidate guard on its output. -/
def successor_output_domain (base a out : Nat) (ho : out ≠ base+9) :
    KDerivation (imp (succAt base a out).encode (domainAt base out).encode) := by
  let w := base+9
  let D := domainAt base out
  let body := matrix base a out w
  have hbody : KDerivation (imp body.encode D.encode) := by
    apply Context.closeEmpty
    apply Context.deduction
    let Γ := [body.encode]
    have h : Context Γ (both (domainAt base a).encode
        (both D.encode (both (domainAt base w).encode
          (both (rawAt base a w).encode (equivAt base w out).encode)))) := by
      have hh : Context Γ body.encode := Context.head [] _
      simpa [body, matrix, andF, Formula.encode, Formula.not, both, neg] using hh
    exact Context.conjunctionLeft (Context.conjunctionRight h)
  have hwfree : w ∉ D.free := by
    intro h
    have hs := domainAt_free base out h
    have he : w = out := Finset.mem_singleton.mp hs
    exact ho he.symm
  have hv := free_vacuity w D hwfree
  rw [successor_shape]
  change KDerivation (imp (existsCode w body.encode) D.encode)
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.existsElim hv
  · exact .closed (.generalize w hbody)
  · exact Context.head [] _

theorem successor_output_domain_certificate (base a out : Nat) (ho : out ≠ base+9) :
    theoremCode (certificate (successor_output_domain base a out ho)) =
      imp (succAt base a out).encode (domainAt base out).encode := certificate_correct _

/-- Candidate closure provides a raw successor witness at the exact private
names of the generated successor template. -/
def raw_candidate_exists (base a o : Nat) (ha : a < base) (ho : o < base) (hoa : o ≠ a) :
    KDerivation (imp (domainAt base a).encode
      (existsCode o (both (rawAt base a o).encode (domainAt base o).encode))) := by
  have fresh : [a,o,base+10,base+32,base+33,base+34,base+101,
      base+102,base+103,base+35,base+36,base+38,base+39,base+104,
      base+37,base+105,base+106,base+107,base+108,base+100].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_false_eq_true,
      not_or, List.nodup_nil, and_true]
    omega
  have hc := predicate_names_lt a (base+100)
  have h := fixed_candidate_successor_exists a o (base+10)
    (base+32) (base+33) (base+34) (base+101) (base+102) (base+103)
    (base+35) (base+36) (base+38) (base+39) (base+104) (base+37)
    (base+105) (base+106) (base+107) (base+108) (base+100) fresh
    (by omega) (by omega)
  simpa only [domainAt_encode, rawAt, Formula.encode, namedSuccessorBody,
    successorCode, namedBoth, namedEither, Formula.not, both, neg, either] using h

theorem raw_candidate_exists_certificate (base a o : Nat) (ha : a < base)
    (ho : o < base) (hoa : o ≠ a) :
    theoremCode (certificate (raw_candidate_exists base a o ha ho hoa)) =
      imp (domainAt base a).encode
        (existsCode o (both (rawAt base a o).encode (domainAt base o).encode)) :=
  certificate_correct _

end PASoundness.PAtoCompactQuotientSuccessorTotality

#print axioms PASoundness.PAtoCompactQuotientSuccessorTotality.successor_shape
#print axioms PASoundness.PAtoCompactQuotientSuccessorTotality.successor_output_domain
#print axioms PASoundness.PAtoCompactQuotientSuccessorTotality.successor_output_domain_certificate
#print axioms PASoundness.PAtoCompactQuotientSuccessorTotality.raw_candidate_exists
#print axioms PASoundness.PAtoCompactQuotientSuccessorTotality.raw_candidate_exists_certificate
