import PASoundness.PAtoCompactOrderIsomorphism
import PASoundness.PAtoCompactTransitiveWitness
import PASoundness.PAtoCompactAdjunction

/-! A pointwise no-garbage preservation lemma for a candidate diagonal graph.
This is finite K proof data conditional on the displayed successor/adjunction
pointwise consequences and the supplied pair witness. It does not construct a
graph, establish global induction, or use semantic soundness. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactDiagonalNoGarbageStep
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactAdjunction
open PASoundness.PAtoCompactTransitiveWitness PASoundness.PAtoCompactOrderIsomorphism

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def oldEntryBody : Nat := both (member 0 3) (pairFormula 9 3 3).encode
def newEntryBody : Nat := both (member 1 3) (pairFormula 9 3 3).encode
def oldEntry : Nat := existsCode 3 oldEntryBody
def newEntry : Nat := existsCode 3 newEntryBody

def body_lift : KDerivation (imp (imp (member 0 3) (member 1 3))
    (imp oldEntryBody newEntryBody)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [oldEntryBody, imp (member 0 3) (member 1 3)]
  have hb : Context Γ oldEntryBody := .hypothesis (by simp [Γ])
  have hi : Context Γ (imp (member 0 3) (member 1 3)) := .hypothesis (by simp [Γ])
  exact Context.conjunctionIntro (.mp (Context.conjunctionLeft hb) hi) (Context.conjunctionRight hb)

/-- Equality of pair witnesses transports the literal relational pair code. -/
def pair_witness_replace : KDerivation (imp (equal 9 8)
    (imp (pairFormula 8 0 0).encode (pairFormula 9 0 0).encode)) := by
  have h := (CompactNamed.equalityReplace 8 9 (pairFormula 8 0 0) (by decide) (by decide)).1
  have he : CompactNamed.replace 8 9 (pairFormula 8 0 0) = pairFormula 9 0 0 := by decide
  rw [he] at h
  exact compose (equalitySymmetry 9 8) h

/-- The k=k witness can be introduced into the new entry existential. -/
def new_entry_intro : KDerivation
    (imp (both (member 1 0) (pairFormula 9 0 0).encode) newEntry) := by
  let f := namedBoth (.member 1 3) (pairFormula 9 3 3)
  have h := exists_variable_intro 3 0 f (by decide) (by decide) (by decide)
  have he : CompactNamed.replace 3 0 f = namedBoth (.member 1 0) (pairFormula 9 0 0) := by decide
  rw [he] at h
  simpa [f, newEntry, newEntryBody, namedBoth, CompactNamed.Formula.encode,
    CompactProof.both, CompactProof.neg] using h

/-- For one chosen graph-entry name 9, old diagonal witnesses transfer across
an explicit inclusion and a newly adjoined diagonal pair. Assumptions are
pointwise graph membership and old witness implications, universal membership
inclusion, membership of the old endpoint in the successor, and the supplied
new Kuratowski pair. None of those hypotheses is asserted here. -/
def no_garbage_step : KDerivation
    (imp (imp (member 7 9) (either (equal 9 8) (member 6 9)))
      (imp (imp (member 6 9) oldEntry)
        (imp (allCode 3 (imp (member 0 3) (member 1 3)))
          (imp (member 1 0) (imp (pairFormula 8 0 0).encode
            (imp (member 7 9) newEntry)))))) := by
  let A := imp (member 7 9) (either (equal 9 8) (member 6 9))
  let B := imp (member 6 9) oldEntry
  let H := allCode 3 (imp (member 0 3) (member 1 3))
  let K := member 1 0
  let P := (pairFormula 8 0 0).encode
  let M := member 7 9
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [M,P,K,H,B,A]
  have hm : Context Γ M := .hypothesis (by simp [Γ])
  have hp : Context Γ P := .hypothesis (by simp [Γ])
  have hk : Context Γ K := .hypothesis (by simp [Γ])
  have hh : Context Γ H := .hypothesis (by simp [Γ])
  have hb : Context Γ B := .hypothesis (by simp [Γ])
  have ha : Context Γ A := .hypothesis (by simp [Γ])
  have hcases : Context Γ (either (equal 9 8) (member 6 9)) := .mp hm ha
  apply Context.disjunctionElim hcases
  · have he : Context (equal 9 8 :: Γ) (equal 9 8) := Context.head Γ _
    have hp' : Context (equal 9 8 :: Γ) P := Context.under hp _
    have hpair : Context (equal 9 8 :: Γ) (pairFormula 9 0 0).encode :=
      .mp hp' (.mp he (.closed pair_witness_replace))
    have hk' : Context (equal 9 8 :: Γ) K := Context.under hk _
    exact .mp (Context.conjunctionIntro hk' hpair) (.closed new_entry_intro)
  · have ho : Context (member 6 9 :: Γ) (member 6 9) := Context.head Γ _
    have hold : Context (member 6 9 :: Γ) oldEntry := .mp ho (Context.under hb _)
    have hh' : Context (member 6 9 :: Γ) H := Context.under hh _
    have hall : Context (member 6 9 :: Γ) (allCode 3 (imp oldEntryBody newEntryBody)) :=
      Context.allMP hh' (.closed (.generalize 3 body_lift))
    exact exists_map_context hall hold

theorem no_garbage_step_certificate : theoremCode (certificate no_garbage_step) =
    imp (imp (member 7 9) (either (equal 9 8) (member 6 9)))
      (imp (imp (member 6 9) oldEntry)
        (imp (allCode 3 (imp (member 0 3) (member 1 3)))
          (imp (member 1 0) (imp (pairFormula 8 0 0).encode
            (imp (member 7 9) newEntry))))) := certificate_correct no_garbage_step

end PASoundness.PAtoCompactDiagonalNoGarbageStep

#print axioms PASoundness.PAtoCompactDiagonalNoGarbageStep.no_garbage_step
#print axioms PASoundness.PAtoCompactDiagonalNoGarbageStep.no_garbage_step_certificate
