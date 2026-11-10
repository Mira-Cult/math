import PASoundness.PAtoCompactAdditionOldTargetWitnessTransfer
import PASoundness.PAtoCompactPointAdjoin

/-! Conditional quantified right-bijection assembly for an unequal added
endpoint: the old target set is name 34, the added target is 32, and the
new target set is 40. This supplies no old-target or top-target case proofs,
full bijection, or addition totality. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactAdditionRightBijectionCases
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactPointAdjoin PASoundness.PAtoCompactAdditionOldTargetWitnessTransfer
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Preimage and its guarded uniqueness at target name v. -/
def rightBody (v : Nat) : Formula := .ex 2
  (namedBoth (.member 38 2) (namedBoth (graphFormula 9 2 v)
    (.all 4 (.imp (namedBoth (.member 38 4) (graphFormula 9 4 v)) (.equal 4 2)))))
/-- New target coverage and guarded uniqueness. -/
def rightClause : Formula := .all 3 (.imp (.member 40 3) (rightBody 3))

theorem old_witness_alignment : rightBody 28 = .ex 2 newWitnessBody := by decide

/-- An explicit target adjunction yields its actual old-or-new case split. -/
def target_split : KDerivation (imp (adjoinCode 34 32 40 41)
    (imp (member 40 28) (either (equal 28 32) (member 34 28)))) := by
  let f := namedBoth (.imp (.member 40 41) (namedEither (.equal 41 32) (.member 34 41)))
    (.imp (namedEither (.equal 41 32) (.member 34 41)) (.member 40 41))
  have h := universalInstance 41 28 f (by decide) (by decide) (by decide)
  have hc : KDerivation (imp (adjoinCode 34 32 40 41)
      (both (imp (member 40 28) (either (equal 28 32) (member 34 28)))
        (imp (either (equal 28 32) (member 34 28)) (member 40 28)))) := by
    simpa [f,adjoinCode,namedBoth,namedEither,Formula.encode,replace,rename,both,neg,either] using h
  apply Context.closeEmpty
  apply Context.deduction
  have hpair := Context.mp (Context.head [] (adjoinCode 34 32 40 41)) (.closed hc)
  exact Context.conjunctionLeft hpair

/-- A common context and explicit old and top case proofs yield the quantified
new target clause under the supplied target adjunction. -/
def right_from_cases (P : Nat)
    (hvP : KDerivation (imp P (allCode 28 P)))
    (hOld : KDerivation (imp P (imp (member 34 28) (rightBody 28).encode)))
    (hTop : KDerivation (imp P (imp (equal 28 32) (rightBody 28).encode))) :
    KDerivation (imp P (imp (adjoinCode 34 32 40 41) rightClause.encode)) := by
  let S := adjoinCode 34 32 40 41
  let M := member 40 28
  let C := (rightBody 28).encode
  let Γ := [S,P]
  have hvS : KDerivation (imp S (allCode 28 S)) := by
    have h := (namedAdjoin 34 32 40 41).vacuity 28 (by decide)
    simpa [S,namedAdjoin,namedBoth,namedEither,Formula.encode,adjoinCode,both,neg,either] using h
  have hlocal : Context Γ (imp M C) := by
    apply Context.deduction
    have hs : Context (M :: Γ) S := .hypothesis (by simp [Γ])
    have hp : Context (M :: Γ) P := .hypothesis (by simp [Γ])
    have hm : Context (M :: Γ) M := Context.head _ _
    have hc : Context (M :: Γ) (either (equal 28 32) (member 34 28)) :=
      .mp hm (.mp hs (.closed target_split))
    apply Context.disjunctionElim hc
    · exact .mp (Context.head _ (equal 28 32)) (.mp (Context.under hp _) (.closed hTop))
    · exact .mp (Context.head _ (member 34 28)) (.mp (Context.under hp _) (.closed hOld))
  have hv : ∀ z, z ∈ Γ → KDerivation (imp z (allCode 28 z)) := by
    intro z hz
    simp only [Γ,List.mem_cons,List.not_mem_nil,or_false] at hz
    by_cases h : z = S
    · subst z; exact hvS
    · have h' : z = P := hz.resolve_left h
      subst z; exact hvP
  have hall : Context Γ (allCode 28 (imp M C)) := Context.generalize 28 hv hlocal
  let f : Formula := .imp (.member 40 28) (rightBody 28)
  have hAlpha := (universalAlpha 28 3 f (by decide) (by decide) (by decide)).1
  have hsyntax : replace 28 3 f = .imp (.member 40 3) (rightBody 3) := by decide
  rw [hsyntax] at hAlpha
  have hfinal : Context Γ rightClause.encode := .mp hall (.closed hAlpha)
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  exact hfinal

theorem right_from_cases_certificate (P : Nat)
    (hvP : KDerivation (imp P (allCode 28 P)))
    (hOld : KDerivation (imp P (imp (member 34 28) (rightBody 28).encode)))
    (hTop : KDerivation (imp P (imp (equal 28 32) (rightBody 28).encode))) :
    theoremCode (certificate (right_from_cases P hvP hOld hTop)) =
      imp P (imp (adjoinCode 34 32 40 41) rightClause.encode) :=
  certificate_correct (right_from_cases P hvP hOld hTop)
end PASoundness.PAtoCompactAdditionRightBijectionCases
#print axioms PASoundness.PAtoCompactAdditionRightBijectionCases.target_split
#print axioms PASoundness.PAtoCompactAdditionRightBijectionCases.right_from_cases
#print axioms PASoundness.PAtoCompactAdditionRightBijectionCases.right_from_cases_certificate
