import PASoundness.PAtoCompactAdditionOldTargetPoint

/-! Quantified uniqueness for an old target in the addition-successor graph.
All old uniqueness, edge-split and old-source guard formulas are explicit K
antecedents. This is not a graph construction, full bijection, arithmetic
totality, or PA proof translation; it does not assume suffix transitivity. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactAdditionOldTargetUniform
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactFilteredSubset
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactFilterInstantiation
open PASoundness.PAtoCompactAdditionSuccessorGraphClean PASoundness.PAtoCompactAdditionOldTargetPoint
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The supplied old uniqueness with fresh competitor binder 29. -/
def oldUniqueUniform : Formula := .all 29 (.imp
  (namedBoth (.member 31 29) (graphFormula 6 29 28)) (.equal 29 2))
/-- A new edge is old or is the adjoined edge (31,32). -/
def splitUniform : Formula := .all 29 (.imp (graphFormula 9 29 28)
  (namedEither (graphFormula 6 29 28) (namedBoth (.equal 29 31) (.equal 28 32))))
/-- Every old edge into 28 has a source in the old source domain. -/
def sourceGuardUniform : Formula := .all 29 (.imp (graphFormula 6 29 28) (.member 31 29))
/-- New source uniqueness over source-domain name 38. -/
def newUnique : Nat := allCode 4 (imp
  (both (member 38 4) (graphFormula 9 4 28).encode) (equal 4 2))

private def old_instance : KDerivation (imp oldUniqueUniform.encode oldUnique) := by
  let f : Formula := .imp (namedBoth (.member 31 29) (graphFormula 6 29 28)) (.equal 29 2)
  have h := universalInstance 29 4 f (by decide) (by decide) (by decide)
  have hr : replace 29 4 f = .imp (namedBoth (.member 31 4) (graphFormula 6 4 28)) (.equal 4 2) := by decide
  rw [hr] at h
  exact h

private def split_instance : KDerivation (imp splitUniform.encode edgeSplit) := by
  let f : Formula := .imp (graphFormula 9 29 28)
    (namedEither (graphFormula 6 29 28) (namedBoth (.equal 29 31) (.equal 28 32)))
  have h := universalInstance 29 4 f (by decide) (by decide) (by decide)
  have hr : replace 29 4 f = .imp (graphFormula 9 4 28)
      (namedEither (graphFormula 6 4 28) (namedBoth (.equal 4 31) (.equal 28 32))) := by decide
  rw [hr] at h
  exact h

private def guard_instance : KDerivation (imp sourceGuardUniform.encode oldSourceGuard) := by
  let f : Formula := .imp (graphFormula 6 29 28) (.member 31 29)
  have h := universalInstance 29 4 f (by decide) (by decide) (by decide)
  have hr : replace 29 4 f = .imp (graphFormula 6 4 28) (.member 31 4) := by decide
  rw [hr] at h
  exact h

/-- Every new-graph edge at an old target has the supplied unique source,
from the literal filter and explicit old-graph premises. -/
def old_target_unique_uniform : KDerivation (imp suffix (imp (member 34 28)
    (imp oldUniqueUniform.encode (imp splitUniform.encode
      (imp sourceGuardUniform.encode newUnique))))) := by
  let F := suffix
  let T := member 34 28
  let U := oldUniqueUniform.encode
  let S := splitUniform.encode
  let D := sourceGuardUniform.encode
  let W := both (member 38 4) (graphFormula 9 4 28).encode
  let Γ := [D,S,U,T,F]
  have hf : Context Γ F := .hypothesis (by simp [Γ])
  have ht : Context Γ T := .hypothesis (by simp [Γ])
  have hu : Context Γ U := .hypothesis (by simp [Γ])
  have hs : Context Γ S := .hypothesis (by simp [Γ])
  have hd : Context Γ D := .hypothesis (by simp [Γ])
  have hu' : Context Γ oldUnique := .mp hu (.closed old_instance)
  have hs' : Context Γ edgeSplit := .mp hs (.closed split_instance)
  have hd' : Context Γ oldSourceGuard := .mp hd (.closed guard_instance)
  have hi : Context Γ (imp (graphFormula 9 4 28).encode (equal 4 2)) :=
    .mp hd' (.mp hs' (.mp hu' (.mp ht (.mp hf (.closed old_target_unique_point)))))
  have hpoint : Context Γ (imp W (equal 4 2)) := by
    apply Context.deduction
    have hw : Context (W :: Γ) W := Context.head Γ W
    exact .mp (Context.conjunctionRight hw) (Context.under hi W)
  have hvT : KDerivation (imp T (allCode 4 T)) := membershipVacuity 34 28 4 (by decide) (by decide)
  let fF : Formula := .all 35 (namedFilterBody 32 34 35 (Formula.member 33 35).not)
  have hvF : KDerivation (imp F (allCode 4 F)) := by
    have h := fF.vacuity 4 (by decide)
    simpa [F,fF,suffix,namedFilterBody,namedBoth,Formula.not,Formula.encode,
      filterGraph,filterPredicate,both,neg] using h
  have hvU : KDerivation (imp U (allCode 4 U)) := oldUniqueUniform.vacuity 4 (by decide)
  have hvS : KDerivation (imp S (allCode 4 S)) := splitUniform.vacuity 4 (by decide)
  have hvD : KDerivation (imp D (allCode 4 D)) := sourceGuardUniform.vacuity 4 (by decide)
  have hv : ∀ z, z ∈ Γ → KDerivation (imp z (allCode 4 z)) := by
    intro z hz
    simp only [Γ,List.mem_cons,List.not_mem_nil,or_false] at hz
    by_cases hD : z = D
    · subst z; exact hvD
    · by_cases hS : z = S
      · subst z; exact hvS
      · by_cases hU : z = U
        · subst z; exact hvU
        · by_cases hT : z = T
          · subst z; exact hvT
          · have hF : z = F := (((hz.resolve_left hD).resolve_left hS).resolve_left hU).resolve_left hT
            subst z; exact hvF
  have hall : Context Γ newUnique := Context.generalize 4 hv hpoint
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  exact hall

theorem old_target_unique_uniform_certificate : theoremCode (certificate old_target_unique_uniform) =
    imp suffix (imp (member 34 28) (imp oldUniqueUniform.encode (imp splitUniform.encode
      (imp sourceGuardUniform.encode newUnique)))) := certificate_correct old_target_unique_uniform
end PASoundness.PAtoCompactAdditionOldTargetUniform
#print axioms PASoundness.PAtoCompactAdditionOldTargetUniform.old_target_unique_uniform
#print axioms PASoundness.PAtoCompactAdditionOldTargetUniform.old_target_unique_uniform_certificate
