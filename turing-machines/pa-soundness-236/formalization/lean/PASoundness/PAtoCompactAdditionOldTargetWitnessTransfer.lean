import PASoundness.PAtoCompactAdditionOldTargetUniform
import PASoundness.CompactQuantifiers
import PASoundness.PAtoCompactTransitiveWitness

/-! Transfer a supplied old preimage witness to the distinct-top addition
successor graph. The old witness, source/edge inclusions, clean-source guard,
edge split and suffix filter are literal K antecedents. This is not a full
bijection or addition totality. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactAdditionOldTargetWitnessTransfer
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactTransitiveWitness
open PASoundness.PAtoCompactFilteredSubset PASoundness.PAtoCompactFilterInstantiation
open PASoundness.PAtoCompactAdditionSuccessorGraphClean PASoundness.PAtoCompactAdditionOldTargetUniform
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The old target's preimage, with the old source-domain guard and uniqueness. -/
def oldWitnessBody : Formula := namedBoth (.member 31 2)
  (namedBoth (graphFormula 6 2 28)
    (.all 4 (.imp (namedBoth (.member 31 4) (graphFormula 6 4 28)) (.equal 4 2))))
/-- New-graph preimage body, with new source-domain guard and uniqueness. -/
def newWitnessBody : Formula := namedBoth (.member 38 2)
  (namedBoth (graphFormula 9 2 28)
    (.all 4 (.imp (namedBoth (.member 38 4) (graphFormula 9 4 28)) (.equal 4 2))))
/-- Uniform inclusion of the old source domain in the new one. -/
def sourceInclusion : Formula := .all 29 (.imp (.member 31 29) (.member 38 29))
/-- Uniform preservation of old edges at target 28. -/
def graphInclusion : Formula := .all 29 (.imp (graphFormula 6 29 28) (graphFormula 9 29 28))

private def old_unique_alpha : KDerivation (imp
    (allCode 4 (imp (both (member 31 4) (graphFormula 6 4 28).encode) (equal 4 2)))
    oldUniqueUniform.encode) := by
  let f : Formula := .imp (namedBoth (.member 31 4) (graphFormula 6 4 28)) (.equal 4 2)
  have h := (universalAlpha 4 29 f (by decide) (by decide) (by decide)).1
  have hr : replace 4 29 f = .imp (namedBoth (.member 31 29) (graphFormula 6 29 28)) (.equal 29 2) := by decide
  rw [hr] at h
  exact h
private def source_instance : KDerivation (imp sourceInclusion.encode (imp (member 31 2) (member 38 2))) := by
  let f : Formula := .imp (.member 31 29) (.member 38 29)
  have h := universalInstance 29 2 f (by decide) (by decide) (by decide)
  have hr : replace 29 2 f = .imp (.member 31 2) (.member 38 2) := by decide
  rw [hr] at h
  exact h
private def graph_instance : KDerivation (imp graphInclusion.encode
    (imp (graphFormula 6 2 28).encode (graphFormula 9 2 28).encode)) := by
  let f : Formula := .imp (graphFormula 6 29 28) (graphFormula 9 29 28)
  have h := universalInstance 29 2 f (by decide) (by decide) (by decide)
  have hr : replace 29 2 f = .imp (graphFormula 6 2 28) (graphFormula 9 2 28) := by decide
  rw [hr] at h
  exact h

/-- The same old preimage remains a unique new preimage under the supplied
inclusions and the distinct-top uniqueness premises. -/
def old_target_witness_transfer : KDerivation (imp suffix (imp (member 34 28)
    (imp splitUniform.encode (imp sourceGuardUniform.encode
      (imp sourceInclusion.encode (imp graphInclusion.encode
        (imp (Formula.ex 2 oldWitnessBody).encode (Formula.ex 2 newWitnessBody).encode))))))) := by
  let F := suffix
  let T := member 34 28
  let S := splitUniform.encode
  let D := sourceGuardUniform.encode
  let I := sourceInclusion.encode
  let J := graphInclusion.encode
  let O := oldWitnessBody.encode
  let V := newWitnessBody.encode
  let Γ := [J,I,D,S,T,F]
  have hf : Context Γ F := .hypothesis (by simp [Γ])
  have ht : Context Γ T := .hypothesis (by simp [Γ])
  have hs : Context Γ S := .hypothesis (by simp [Γ])
  have hd : Context Γ D := .hypothesis (by simp [Γ])
  have hi : Context Γ I := .hypothesis (by simp [Γ])
  have hj : Context Γ J := .hypothesis (by simp [Γ])
  have hlocal : Context Γ (imp O V) := by
    apply Context.deduction
    have ho : Context (O :: Γ) O := Context.head Γ O
    have hsource : Context (O :: Γ) (member 31 2) := Context.conjunctionLeft ho
    have hedge : Context (O :: Γ) (graphFormula 6 2 28).encode :=
      Context.conjunctionLeft (Context.conjunctionRight ho)
    have hu : Context (O :: Γ) (allCode 4 (imp
        (both (member 31 4) (graphFormula 6 4 28).encode) (equal 4 2))) :=
      Context.conjunctionRight (Context.conjunctionRight ho)
    have hu' : Context (O :: Γ) oldUniqueUniform.encode := .mp hu (.closed old_unique_alpha)
    have hnewU : Context (O :: Γ) newUnique :=
      .mp (Context.under hd O) (.mp (Context.under hs O) (.mp hu'
        (.mp (Context.under ht O) (.mp (Context.under hf O) (.closed old_target_unique_uniform)))))
    have hnewS : Context (O :: Γ) (member 38 2) :=
      .mp hsource (.mp (Context.under hi O) (.closed source_instance))
    have hnewG : Context (O :: Γ) (graphFormula 9 2 28).encode :=
      .mp hedge (.mp (Context.under hj O) (.closed graph_instance))
    exact Context.conjunctionIntro hnewS (Context.conjunctionIntro hnewG hnewU)
  have hvT : KDerivation (imp T (allCode 2 T)) := membershipVacuity 34 28 2 (by decide) (by decide)
  let fF : Formula := .all 35 (namedFilterBody 32 34 35 (Formula.member 33 35).not)
  have hvF : KDerivation (imp F (allCode 2 F)) := by
    have h := fF.vacuity 2 (by decide)
    simpa [F,fF,suffix,namedFilterBody,namedBoth,Formula.not,Formula.encode,
      filterGraph,filterPredicate,both,neg] using h
  have hvS : KDerivation (imp S (allCode 2 S)) := splitUniform.vacuity 2 (by decide)
  have hvD : KDerivation (imp D (allCode 2 D)) := sourceGuardUniform.vacuity 2 (by decide)
  have hvI : KDerivation (imp I (allCode 2 I)) := sourceInclusion.vacuity 2 (by decide)
  have hvJ : KDerivation (imp J (allCode 2 J)) := graphInclusion.vacuity 2 (by decide)
  have hv : ∀ z, z ∈ Γ → KDerivation (imp z (allCode 2 z)) := by
    intro z hz
    simp only [Γ,List.mem_cons,List.not_mem_nil,or_false] at hz
    by_cases hJ : z = J
    · subst z; exact hvJ
    · by_cases hI : z = I
      · subst z; exact hvI
      · by_cases hD : z = D
        · subst z; exact hvD
        · by_cases hS : z = S
          · subst z; exact hvS
          · by_cases hT : z = T
            · subst z; exact hvT
            · have hF : z = F := ((((hz.resolve_left hJ).resolve_left hI).resolve_left hD).resolve_left hS).resolve_left hT
              subst z; exact hvF
  have hall : Context Γ (allCode 2 (imp O V)) := Context.generalize 2 hv hlocal
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  have hw : Context ((Formula.ex 2 oldWitnessBody).encode :: Γ) (existsCode 2 O) := Context.head _ _
  have hall' : Context ((Formula.ex 2 oldWitnessBody).encode :: Γ) (allCode 2 (imp O V)) := Context.under hall _
  change Context ((Formula.ex 2 oldWitnessBody).encode :: Γ) (existsCode 2 V)
  exact exists_map_context hall' hw

theorem old_target_witness_transfer_certificate : theoremCode (certificate old_target_witness_transfer) =
    imp suffix (imp (member 34 28) (imp splitUniform.encode (imp sourceGuardUniform.encode
      (imp sourceInclusion.encode (imp graphInclusion.encode
        (imp (Formula.ex 2 oldWitnessBody).encode (Formula.ex 2 newWitnessBody).encode)))))) :=
  certificate_correct old_target_witness_transfer
end PASoundness.PAtoCompactAdditionOldTargetWitnessTransfer
#print axioms PASoundness.PAtoCompactAdditionOldTargetWitnessTransfer.old_target_witness_transfer
#print axioms PASoundness.PAtoCompactAdditionOldTargetWitnessTransfer.old_target_witness_transfer_certificate
