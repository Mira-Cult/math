import PASoundness.PAtoCompactAdditionUnequalTopUnique
import PASoundness.PAtoCompactAdditionSuccessorEdgeSplitUnique

/-! Top-edge uniqueness for the unequal-endpoint addition graph. The pair,
old graph and adjunction remain explicit K assumptions. No whole bijection,
arithmetic totality or suffix transitivity is asserted. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactAdditionTopEdgeCases
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactPointAdjoin PASoundness.PAtoCompactAdditionSuccessorGraphClean
open PASoundness.PAtoCompactFilteredSubset PASoundness.PAtoCompactFilterInstantiation
open PASoundness.PAtoCompactAdditionSuccessorEdgeSplitUnique PASoundness.PAtoCompactAdditionUnequalTopUnique
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

private def base : KDerivation (edgeSplitBody 31 32 2 3).encode := by
  simpa [edgeSplitBody, namedAdjoin, namedEither, namedBoth, Formula.encode,
    adjoinCode, CompactProof.both, CompactProof.neg, CompactDerivations.either] using edge_split_23
private def at4 : KDerivation (edgeSplitBody 31 32 4 3).encode := by
  have h := universalInstance 2 4 (edgeSplitBody 31 32 2 3) (by decide) (by decide) (by decide)
  have hc := KDerivation.mp (.generalize 2 base) h
  have hr : replace 2 4 (edgeSplitBody 31 32 2 3) = edgeSplitBody 31 32 4 3 := by decide
  rw [hr] at hc
  exact hc
private def source4 : KDerivation (edgeSplitBody 31 32 31 3).encode := by
  have h := universalInstance 2 31 (edgeSplitBody 31 32 2 3) (by decide) (by decide) (by decide)
  have hc := KDerivation.mp (.generalize 2 base) h
  have hr : replace 2 31 (edgeSplitBody 31 32 2 3) = edgeSplitBody 31 32 31 3 := by decide
  rw [hr] at hc
  exact hc

def source_split : KDerivation (imp (adjoinCode 6 11 9 16)
    (imp (pairFormula 11 31 32).encode (sourceSplit 4))) := by
  have h := universalInstance 3 4 (edgeSplitBody 31 32 31 3) (by decide) (by decide) (by decide)
  have hc := KDerivation.mp (.generalize 3 source4) h
  have hr : replace 3 4 (edgeSplitBody 31 32 31 3) = edgeSplitBody 31 32 31 4 := by decide
  rw [hr] at hc
  simpa [edgeSplitBody, sourceSplit, namedAdjoin, namedEither, namedBoth, Formula.encode,
    adjoinCode, CompactProof.both, CompactProof.neg, CompactDerivations.either] using hc

def target_split : KDerivation (imp (adjoinCode 6 11 9 16)
    (imp (pairFormula 11 31 32).encode (targetSplit 4))) := by
  have h := universalInstance 3 32 (edgeSplitBody 31 32 4 3) (by decide) (by decide) (by decide)
  have hc := KDerivation.mp (.generalize 3 at4) h
  have hr : replace 3 32 (edgeSplitBody 31 32 4 3) = edgeSplitBody 31 32 4 32 := by decide
  rw [hr] at hc
  simpa [edgeSplitBody, targetSplit, namedAdjoin, namedEither, namedBoth, Formula.encode,
    adjoinCode, CompactProof.both, CompactProof.neg, CompactDerivations.either] using hc

/-- Every new edge at source 31 has target 32, at the displayed point 4. -/
def source_unique : KDerivation (imp (adjoinCode 6 11 9 16)
    (imp (pairFormula 11 31 32).encode (imp oldClean.encode
      (imp (graphFormula 9 31 4).encode (equal 4 32))))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [oldClean.encode, (pairFormula 11 31 32).encode, adjoinCode 6 11 9 16]
  have hc : Context Γ oldClean.encode := .head _ _
  have hp : Context Γ (pairFormula 11 31 32).encode := .hypothesis (by simp [Γ])
  have ha : Context Γ (adjoinCode 6 11 9 16) := .hypothesis (by simp [Γ])
  have hs : Context Γ (sourceSplit 4) := .mp hp (.mp ha (.closed source_split))
  exact .mp hs (.mp hc (.closed (source_top_unique 4 (by decide))))

/-- Every new edge at target 32 has source 31, at the displayed point 4. -/
def target_unique : KDerivation (imp suffix (imp (adjoinCode 6 11 9 16)
    (imp (pairFormula 11 31 32).encode (imp oldClean.encode
      (imp (graphFormula 9 4 32).encode (equal 4 31)))))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [oldClean.encode, (pairFormula 11 31 32).encode, adjoinCode 6 11 9 16, suffix]
  have hc : Context Γ oldClean.encode := .head _ _
  have hp : Context Γ (pairFormula 11 31 32).encode := .hypothesis (by simp [Γ])
  have ha : Context Γ (adjoinCode 6 11 9 16) := .hypothesis (by simp [Γ])
  have hf : Context Γ suffix := .hypothesis (by simp [Γ])
  have hs : Context Γ (targetSplit 4) := .mp hp (.mp ha (.closed target_split))
  exact .mp hs (.mp hc (.mp hf (.closed (target_top_unique 4 (by decide)))))


private def pairF : Formula := pairFormula 11 31 32
private def adjF : Formula := namedAdjoin 6 11 9 16
private def sufF : Formula := .all 35 (namedFilterBody 32 34 35 (Formula.member 33 35).not)
private def adjV : KDerivation (imp (adjoinCode 6 11 9 16)
    (allCode 4 (adjoinCode 6 11 9 16))) := by
  have h := adjF.vacuity 4 (by decide)
  simpa [adjF,namedAdjoin,namedBoth,namedEither,Formula.encode,adjoinCode,both,neg,either] using h
private def suffixV : KDerivation (imp suffix (allCode 4 suffix)) := by
  have h := sufF.vacuity 4 (by decide)
  simpa [sufF,suffix,namedFilterBody,namedBoth,Formula.not,Formula.encode,
    PAtoCompactFilteredSubset.filterGraph,PAtoCompactFilteredSubset.filterPredicate,both,neg] using h

/-- Uniform pointwise uniqueness at the new source, with the supplied pair,
old graph and adjunction retained. -/
def source_unique_all : KDerivation (imp (adjoinCode 6 11 9 16)
    (imp (pairFormula 11 31 32).encode (imp oldClean.encode
      (allCode 4 (imp (graphFormula 9 31 4).encode (equal 4 32)))))) := by
  let A := adjoinCode 6 11 9 16
  let P := (pairFormula 11 31 32).encode
  let C := oldClean.encode
  let Γ := [C,P,A]
  have hv : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 4 h)) := by
    intro h hh
    simp only [Γ,List.mem_cons,List.not_mem_nil,or_false] at hh
    by_cases hc : h = C
    · subst h; exact oldClean.vacuity 4 (by decide)
    · by_cases hp : h = P
      · subst h; exact pairF.vacuity 4 (by decide)
      · have ha : h = A := by simpa [hc,hp] using hh
        subst h; exact adjV
  have hp : Context Γ (imp (graphFormula 9 31 4).encode (equal 4 32)) := by
    have hc : Context Γ C := .head _ _
    have hp : Context Γ P := .hypothesis (by simp [Γ])
    have ha : Context Γ A := .hypothesis (by simp [Γ])
    exact .mp hc (.mp hp (.mp ha (.closed source_unique)))
  have hall := Context.generalize 4 hv hp
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  exact hall

/-- Uniform pointwise uniqueness at the new target, without a transitive
suffix assumption. -/
def target_unique_all : KDerivation (imp suffix (imp (adjoinCode 6 11 9 16)
    (imp (pairFormula 11 31 32).encode (imp oldClean.encode
      (allCode 4 (imp (graphFormula 9 4 32).encode (equal 4 31))))))) := by
  let F := suffix
  let A := adjoinCode 6 11 9 16
  let P := (pairFormula 11 31 32).encode
  let C := oldClean.encode
  let Γ := [C,P,A,F]
  have hv : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 4 h)) := by
    intro h hh
    simp only [Γ,List.mem_cons,List.not_mem_nil,or_false] at hh
    by_cases hc : h = C
    · subst h; exact oldClean.vacuity 4 (by decide)
    · by_cases hp : h = P
      · subst h; exact pairF.vacuity 4 (by decide)
      · by_cases ha : h = A
        · subst h; exact adjV
        · have hf : h = F := by simpa [hc,hp,ha] using hh
          subst h; exact suffixV
  have hp : Context Γ (imp (graphFormula 9 4 32).encode (equal 4 31)) := by
    have hc : Context Γ C := .head _ _
    have hp : Context Γ P := .hypothesis (by simp [Γ])
    have ha : Context Γ A := .hypothesis (by simp [Γ])
    have hf : Context Γ F := .hypothesis (by simp [Γ])
    exact .mp hc (.mp hp (.mp ha (.mp hf (.closed target_unique))))
  have hall := Context.generalize 4 hv hp
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  exact hall


theorem source_unique_all_certificate : theoremCode (certificate source_unique_all) =
    imp (adjoinCode 6 11 9 16) (imp (pairFormula 11 31 32).encode
      (imp oldClean.encode (allCode 4
        (imp (graphFormula 9 31 4).encode (equal 4 32))))) :=
  certificate_correct source_unique_all

theorem target_unique_all_certificate : theoremCode (certificate target_unique_all) =
    imp suffix (imp (adjoinCode 6 11 9 16) (imp (pairFormula 11 31 32).encode
      (imp oldClean.encode (allCode 4
        (imp (graphFormula 9 4 32).encode (equal 4 31)))))) :=
  certificate_correct target_unique_all

end PASoundness.PAtoCompactAdditionTopEdgeCases
#print axioms PASoundness.PAtoCompactAdditionTopEdgeCases.source_unique
#print axioms PASoundness.PAtoCompactAdditionTopEdgeCases.target_unique

#print axioms PASoundness.PAtoCompactAdditionTopEdgeCases.source_unique_all
#print axioms PASoundness.PAtoCompactAdditionTopEdgeCases.target_unique_all

#print axioms PASoundness.PAtoCompactAdditionTopEdgeCases.source_unique_all_certificate
#print axioms PASoundness.PAtoCompactAdditionTopEdgeCases.target_unique_all_certificate
