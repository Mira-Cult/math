import PASoundness.PAtoCompactSuccCongruenceData
import PASoundness.PAtoCompactSuccessorInjective
import PASoundness.PAtoCompactTransitiveClosure

/-! Capture-safe assembly of the exact right/preimage bijection clause from
explicit old-target and new-endpoint K proof interfaces. This is conditional
on those interfaces and a supplied successor graph; no old graph cleanliness,
coverage, irreflexivity, graph existence, or quotient property is assumed or
proved here beyond what the displayed premises supply. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactSuccBijectionRight
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactSuccCongruenceData PASoundness.PAtoCompactSuccessorInjective
open PASoundness.PAtoCompactTransitiveClosure

/-- Exact preimage witness body at a displayed target label. -/
def rightBody (v : Nat) : Formula := .ex 2
  (namedBoth (.member 7 2) (namedBoth (graphFormula 9 2 v)
    (.all 4 (.imp (namedBoth (.member 7 4) (graphFormula 9 4 v)) (.equal 4 2)))))

/-- Exact right bijection clause, with original binder 3. -/
def rightClause : Formula := .all 3 (.imp (.member 8 3) (rightBody 3))

/-- The other clause is exposed to verify exact conjunction alignment. -/
def leftClause : Formula := .all 2 (.imp (.member 7 2) (.ex 3
  (namedBoth (.member 8 3) (namedBoth (graphFormula 9 2 3)
    (.all 4 (.imp (namedBoth (.member 8 4) (graphFormula 9 2 4)) (.equal 4 3)))))))

theorem new_bijection_alignment : newBijection = namedBoth leftClause rightClause := by decide

/-- The exact successor graph yields the old-or-new case split at a fresh
pointwise target name. -/
def target_split : KDerivation (imp targetSuccessor
    (imp (member 8 28) (either (equal 28 1) (member 1 28)))) :=
  successor_inspect 1 8 15 28 (by decide) (by decide) (by decide)

/-- For a supplied common hypothesis P, old-target and endpoint proof
interfaces imply the whole exact right clause. P must be vacuous at name 28;
both cases remain explicit proof-data premises. -/
def right_from_cases (P : Nat)
    (hvP : KDerivation (imp P (allCode 28 P)))
    (hOld : KDerivation (imp P (imp (member 1 28) (rightBody 28).encode)))
    (hTop : KDerivation (imp P (imp (equal 28 1) (rightBody 28).encode))) :
    KDerivation (imp P (imp targetSuccessor rightClause.encode)) := by
  let S := targetSuccessor
  let M := member 8 28
  let C := (rightBody 28).encode
  let Γ := [S,P]
  have hvS : KDerivation (imp S (allCode 28 S)) :=
    successor_vacuity 1 8 15 28 (by decide) (by decide) (by decide)
  have hlocal : Context Γ (imp M C) := by
    apply Context.deduction
    have hs : Context (M :: Γ) S := .hypothesis (by simp [Γ])
    have hp : Context (M :: Γ) P := .hypothesis (by simp [Γ])
    have hm : Context (M :: Γ) M := Context.head _ _
    have hc : Context (M :: Γ) (either (equal 28 1) (member 1 28)) :=
      .mp hm (.mp hs (.closed target_split))
    apply Context.disjunctionElim hc
    · exact .mp (Context.head _ (equal 28 1))
        (.mp (Context.under hp _) (.closed hTop))
    · exact .mp (Context.head _ (member 1 28))
        (.mp (Context.under hp _) (.closed hOld))
  have hv : ∀ z, z ∈ Γ → KDerivation (imp z (allCode 28 z)) := by
    intro z hz
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hz
    by_cases h : z = S
    · subst z; exact hvS
    · have h' : z = P := hz.resolve_left h
      subst z; exact hvP
  have hall : Context Γ (allCode 28 (imp M C)) := Context.generalize 28 hv hlocal
  let f : Formula := .imp (.member 8 28) (rightBody 28)
  have hAlpha := (CompactNamed.universalAlpha 28 3 f (by decide) (by decide) (by decide)).1
  have hsyntax : CompactNamed.replace 28 3 f = .imp (.member 8 3) (rightBody 3) := by decide
  rw [hsyntax] at hAlpha
  have hfinal : Context Γ rightClause.encode := by
    exact .mp hall (.closed hAlpha)
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  exact hfinal

theorem right_from_cases_certificate (P : Nat)
    (hvP : KDerivation (imp P (allCode 28 P)))
    (hOld : KDerivation (imp P (imp (member 1 28) (rightBody 28).encode)))
    (hTop : KDerivation (imp P (imp (equal 28 1) (rightBody 28).encode))) :
    theoremCode (certificate (right_from_cases P hvP hOld hTop)) =
      imp P (imp targetSuccessor rightClause.encode) :=
  certificate_correct (right_from_cases P hvP hOld hTop)

end PASoundness.PAtoCompactSuccBijectionRight

#print axioms PASoundness.PAtoCompactSuccBijectionRight.right_from_cases
#print axioms PASoundness.PAtoCompactSuccBijectionRight.right_from_cases_certificate
