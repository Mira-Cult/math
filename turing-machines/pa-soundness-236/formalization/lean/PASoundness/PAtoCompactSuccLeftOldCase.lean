import PASoundness.PAtoCompactSuccCongruenceData
import PASoundness.PAtoCompactGraphAdjoinPreserve
import PASoundness.PAtoCompactTransitiveClosure
import PASoundness.PAtoCompactSuccLeftUniqueTransfer
import PASoundness.CompactQuantifiers

/-! Old-source witness transfer for conditional successor-bijection. All
old uniqueness, graph-split, endpoint and non-self-membership premises remain
explicit; no graph collection, quotient law or semantic soundness is assumed. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactSuccLeftOldCase
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactSuccCongruenceData PASoundness.PAtoCompactGraphAdjoinPreserve
open PASoundness.PAtoCompactTransitiveClosure PASoundness.PAtoCompactTransitiveWitness
open PASoundness.PAtoCompactSuccLeftUniqueTransfer
open PASoundness.PAtoCompactGraphRestriction PASoundness.PAtoCompactPointAdjoin
open PASoundness.PAtoCompactAdjunction
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Old witness at names 2 and 3, including its guarded uniqueness. -/
def oldBody : Formula := namedBoth (.member 1 3) (namedBoth (graphFormula 6 2 3)
  (.all 4 (.imp (namedBoth (.member 1 4) (graphFormula 6 2 4)) (.equal 4 3))))

/-- The corresponding witness body for the supplied successor domains and
adjoined graph. -/
def newBody : Formula := namedBoth (.member 8 3) (namedBoth (graphFormula 9 2 3)
  (.all 4 (.imp (namedBoth (.member 8 4) (graphFormula 9 2 4)) (.equal 4 3))))

def oldUnique : Nat := allCode 4
  (imp (both (member 1 4) (graphFormula 6 2 4).encode) (equal 4 3))
def newUnique : Nat := allCode 4
  (imp (both (member 8 4) (graphFormula 9 2 4).encode) (equal 4 3))

/-- Old bijection supplies a guarded old-target witness for source name 2. -/
def old_witness_exists : KDerivation
    (imp oldMatrix (imp (member 0 2) (existsCode 3 oldBody.encode))) := by
  let f : Formula := .imp (.member 0 2) (.ex 3 oldBody)
  have hinst := CompactNamed.allSpecialize 2 f (by decide)
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [member 0 2,oldMatrix]
  have hm : Context Γ oldMatrix := .hypothesis (by simp [Γ])
  have hx : Context Γ (member 0 2) := Context.head _ _
  have hb : Context Γ bijectionFormula.encode := Context.conjunctionLeft hm
  have hl : Context Γ (allCode 2 f.encode) := Context.conjunctionLeft hb
  exact .mp hx (.mp hl (.closed hinst))

/-- The old target remains inside the supplied successor target. -/
def old_target_preserved : KDerivation
    (imp targetSuccessor (imp (member 1 3) (member 8 3))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [member 1 3,targetSuccessor]
  have hm : Context Γ (member 1 3) := Context.head _ _
  have hs : Context Γ targetSuccessor := .hypothesis (by simp [Γ])
  have he : Context Γ (either (equal 3 1) (member 1 3)) :=
    Context.disjunctionRight (a := equal 3 1) hm
  exact .mp he (.mp hs (.closed (successor_include 1 8 15 3 (by decide) (by decide) (by decide))))

/-- An existing edge survives the supplied point adjunction. -/
def old_edge_preserved : KDerivation
    (imp newGraph (imp (graphFormula 6 2 3).encode (graphFormula 9 2 3).encode)) :=
  adjoin_preserves_edge 6 11 9 16 2 3 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

/-- The old-source existential witness transfers to the extended target and
graph, given explicit K proofs of the uniform edge split and the clean-edge
target guard. These two proof-data premises are not assumed semantically. -/
def old_source_case
    (hSplit : KDerivation (imp newGraph (imp newPair (allCode 4 edgeSplit))))
    (hGuard : KDerivation (imp cleanGraph (allCode 4 oldTargetGuard))) :
    KDerivation (imp oldMatrix (imp cleanGraph (imp sourceIrreflexive
      (imp targetSuccessor (imp newGraph (imp newPair (imp (member 0 2)
        (existsCode 3 newBody.encode)))))))) := by
  let C := cleanGraph
  let N := sourceIrreflexive
  let T := targetSuccessor
  let G := newGraph
  let P := newPair
  let M := member 0 2
  let O := oldMatrix
  let Γ := [M,P,G,T,N,C]
  let fC : Formula := .all 19 (.imp (.member 6 19) (edgePredicate 19 0 1))
  let fN : Formula := Formula.not (.member 0 0)
  let fT : Formula := namedSuccessor 1 8 15
  let fG : Formula := namedAdjoin 6 11 9 16
  let fP : Formula := pairFormula 11 0 1
  let fM : Formula := .member 0 2
  have hvC : KDerivation (imp C (allCode 3 C)) := by
    have h := fC.vacuity 3 (by decide)
    simpa [fC,C,cleanGraph,Formula.encode] using h
  have hvN : KDerivation (imp N (allCode 3 N)) := by
    have h := fN.vacuity 3 (by decide)
    simpa [fN,N,sourceIrreflexive,Formula.not,Formula.encode,CompactProof.neg] using h
  have hvT : KDerivation (imp T (allCode 3 T)) := by
    have h := fT.vacuity 3 (by decide)
    simpa [fT,T,targetSuccessor,namedSuccessor,namedSuccessorBody,namedBoth,namedEither,
      successorCode,Formula.encode,CompactProof.both,CompactProof.neg,CompactDerivations.either] using h
  have hvG : KDerivation (imp G (allCode 3 G)) := by
    have h := fG.vacuity 3 (by decide)
    simpa [fG,G,newGraph,namedAdjoin,namedBoth,namedEither,adjoinCode,Formula.encode,
      CompactProof.both,CompactProof.neg,CompactDerivations.either] using h
  have hvP : KDerivation (imp P (allCode 3 P)) := fP.vacuity 3 (by decide)
  have hvM : KDerivation (imp M (allCode 3 M)) := fM.vacuity 3 (by decide)
  have hpoint : Context Γ (imp oldBody.encode newBody.encode) := by
    apply Context.deduction
    let Δ := oldBody.encode :: Γ
    have ho : Context Δ oldBody.encode := Context.head Γ _
    have hm : Context Δ M := .hypothesis (by simp [Δ,Γ])
    have hp : Context Δ P := .hypothesis (by simp [Δ,Γ])
    have hg : Context Δ G := .hypothesis (by simp [Δ,Γ])
    have ht : Context Δ T := .hypothesis (by simp [Δ,Γ])
    have hn : Context Δ N := .hypothesis (by simp [Δ,Γ])
    have hc : Context Δ C := .hypothesis (by simp [Δ,Γ])
    change Context Δ (both (member 1 3) (both (graphFormula 6 2 3).encode oldUnique)) at ho
    have hm' : Context Δ (member 8 3) :=
      .mp (Context.conjunctionLeft ho) (.mp ht (.closed old_target_preserved))
    have hg' : Context Δ (graphFormula 9 2 3).encode :=
      .mp (Context.conjunctionLeft (Context.conjunctionRight ho)) (.mp hg (.closed old_edge_preserved))
    have hu : Context Δ oldUnique := Context.conjunctionRight (Context.conjunctionRight ho)
    have hsplit : Context Δ (allCode 4 edgeSplit) := .mp hp (.mp hg (.closed hSplit))
    have hguard : Context Δ (allCode 4 oldTargetGuard) := .mp hc (.closed hGuard)
    have hunique : Context Δ newUnique :=
      .mp hm (.mp hn (.mp hguard (.mp hsplit (.mp hu (.closed competitor_unique_all)))))
    change Context Δ (both (member 8 3) (both (graphFormula 9 2 3).encode newUnique))
    exact Context.conjunctionIntro hm' (Context.conjunctionIntro hg' hunique)
  have hfv : ∀ z, z ∈ Γ → KDerivation (imp z (allCode 3 z)) := by
    intro z hz
    simp only [Γ,List.mem_cons,List.not_mem_nil,or_false] at hz
    by_cases h : z = M
    · subst z; exact hvM
    · by_cases h' : z = P
      · subst z; exact hvP
      · by_cases h'' : z = G
        · subst z; exact hvG
        · by_cases h''' : z = T
          · subst z; exact hvT
          · by_cases h'''' : z = N
            · subst z; exact hvN
            · have he : z = C := ((((hz.resolve_left h).resolve_left h').resolve_left h'').resolve_left h''').resolve_left h''''
              subst z; exact hvC
  have hall : Context Γ (allCode 3 (imp oldBody.encode newBody.encode)) := Context.generalize 3 hfv hpoint
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Ω := [M,P,G,T,N,C,O]
  have ho : Context Ω O := .hypothesis (by simp [Ω])
  have hm : Context Ω M := Context.head _ _
  have hex : Context Ω (existsCode 3 oldBody.encode) := .mp hm (.mp ho (.closed old_witness_exists))
  have hall' : Context Ω (allCode 3 (imp oldBody.encode newBody.encode)) :=
    Context.weaken hall (by
      intro z hz
      simp only [Γ,Ω,List.mem_cons,List.not_mem_nil,or_false] at *
      tauto)
  exact exists_map_context hall' hex

theorem old_source_case_certificate
    (hSplit : KDerivation (imp newGraph (imp newPair (allCode 4 edgeSplit))))
    (hGuard : KDerivation (imp cleanGraph (allCode 4 oldTargetGuard))) :
    theoremCode (certificate (old_source_case hSplit hGuard)) =
      imp oldMatrix (imp cleanGraph (imp sourceIrreflexive
        (imp targetSuccessor (imp newGraph (imp newPair (imp (member 0 2)
          (existsCode 3 newBody.encode))))))) := certificate_correct (old_source_case hSplit hGuard)

end PASoundness.PAtoCompactSuccLeftOldCase

#print axioms PASoundness.PAtoCompactSuccLeftOldCase.old_witness_exists
#print axioms PASoundness.PAtoCompactSuccLeftOldCase.old_target_preserved
#print axioms PASoundness.PAtoCompactSuccLeftOldCase.old_edge_preserved
#print axioms PASoundness.PAtoCompactSuccLeftOldCase.old_source_case
#print axioms PASoundness.PAtoCompactSuccLeftOldCase.old_source_case_certificate
