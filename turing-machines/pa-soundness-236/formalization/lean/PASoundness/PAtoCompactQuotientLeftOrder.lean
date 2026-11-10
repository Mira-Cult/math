import PASoundness.PAtoCompactQuotientOrder
import PASoundness.PAtoCompactQuotientLeftTransAtWitness
import PASoundness.PAtoCompactTransitiveWitness
import PASoundness.PAtoCompactPartialInverseAtSource

/-! Left-argument substitutivity of the proposed quotient order in one
orientation, as a finite K derivation. The exact candidate condition remains
an object-level antecedent. No quotient congruence in the other direction,
order axioms, arithmetic interpretation or PA soundness bridge is asserted. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactQuotientLeftOrder
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactQuotientOrder
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactCandidateExact
open PASoundness.PAtoCompactPartialInverseAtSource PASoundness.PAtoCompactTransitiveWitness
open PASoundness.PAtoCompactQuotientLeftTransAtWitness

/-- Source order statement: names 1 and 8 are the two operands. Replacing
right 1 before left 0 avoids accidentally replacing the new left name. -/
def sourceLess : Formula := replace 0 1 (replace 1 8 lessFormula)

/-- Target order statement: names 0 and 8 are the two operands. -/
def targetLess : Formula := replace 1 8 lessFormula

def sourceBody : Formula := namedBoth (.member 8 7)
  (replace 0 1 (replace 1 7 equivalentFormula))

def targetBody : Formula := namedBoth (.member 8 7) (replace 1 7 equivalentFormula)

theorem source_less_syntax : sourceLess = .ex 7 sourceBody := by decide

theorem target_less_syntax : targetLess = .ex 7 targetBody := by decide

/-- Replace the left order argument using E in the direction E(0,1). The
same named member witness is retained throughout, and the input candidate
condition is an explicit hypothesis. -/
def left_order_substitutivity : KDerivation
    (imp (candidateCode 0 37 32 33 34 30 35 10 36)
      (imp equivalentFormula.encode (imp sourceLess.encode targetLess.encode))) := by
  let D := candidateCode 0 37 32 33 34 30 35 10 36
  let E := equivalentFormula.encode
  let A := sourceBody.encode
  let B := targetBody.encode
  let Γ := [E,D]
  have hD : Context Γ D := .hypothesis (by simp [Γ])
  have hE : Context Γ E := Context.head _ _
  have hlocal : Context Γ (imp A B) := by
    apply Context.deduction
    let Δ := A :: Γ
    have hA : Context Δ A := Context.head _ _
    have hmem : Context Δ (member 8 7) := Context.conjunctionLeft hA
    have hEq : Context Δ (replace 0 1 (replace 1 7 equivalentFormula)).encode :=
      Context.conjunctionRight hA
    have hTarget : Context Δ (replace 1 7 equivalentFormula).encode :=
      .mp hEq (.mp (Context.under hE A) (.mp (Context.under hD A) (.closed trans_at_witness)))
    exact Context.conjunctionIntro hmem hTarget
  have hvD : KDerivation (imp D (allCode 7 D)) := by
    have h := (namedCandidate 0).vacuity 7 (by decide)
    simpa only [D,named_candidate_code] using h
  have hvE : KDerivation (imp E (allCode 7 E)) := equivalentFormula.vacuity 7 (by decide)
  have hall : Context Γ (allCode 7 (imp A B)) := Context.generalize 7 (by
    intro h hh
    simp only [Γ,List.mem_cons,List.not_mem_nil,or_false] at hh
    by_cases he : h = E
    · subst h; exact hvE
    · have hd : h = D := hh.resolve_left he
      subst h; exact hvD) hlocal
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Δ := [sourceLess.encode,E,D]
  have hsource : Context Δ (existsCode 7 A) := by
    have h := Context.head [E,D] sourceLess.encode
    simpa only [Δ,source_less_syntax,Formula.encode,A] using h
  have hall' : Context Δ (allCode 7 (imp A B)) := Context.weaken hall (by
    intro h hh
    simp only [Γ,List.mem_cons,List.not_mem_nil,or_false] at hh
    simp [Δ,hh])
  have htarget : Context Δ (existsCode 7 B) := exists_map_context hall' hsource
  simpa only [target_less_syntax,Formula.encode,B] using htarget

theorem left_order_substitutivity_certificate :
    theoremCode (certificate left_order_substitutivity) =
      imp (candidateCode 0 37 32 33 34 30 35 10 36)
        (imp equivalentFormula.encode (imp sourceLess.encode targetLess.encode)) :=
  certificate_correct left_order_substitutivity

end PASoundness.PAtoCompactQuotientLeftOrder

#print axioms PASoundness.PAtoCompactQuotientLeftOrder.left_order_substitutivity
#print axioms PASoundness.PAtoCompactQuotientLeftOrder.left_order_substitutivity_certificate
