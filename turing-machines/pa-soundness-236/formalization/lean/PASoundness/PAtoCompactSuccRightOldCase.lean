import PASoundness.PAtoCompactSuccCongruenceData
import PASoundness.PAtoCompactSuccBijectionRight
import PASoundness.PAtoCompactTransitiveWitness
import PASoundness.PAtoCompactSuccCongruenceEdgeSplit
import PASoundness.PAtoCompactSuccCongruenceEdgeCoverage
import PASoundness.PAtoCompactSuccCleanEndpoint

/-! Pointwise uniqueness for an old target in a conditional successor-graph
extension. The old-edge domain guard and the new-edge split are explicit
antecedents, as is encoded target irreflexivity. This does not establish those
premises, construct a graph, prove surjectivity, or prove PA soundness. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactSuccRightOldCase
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactSuccCongruenceData
open PASoundness.PAtoCompactZeroSuccessor PASoundness.CompactNamed
open PASoundness.PAtoCompactSuccBijectionRight PASoundness.PAtoCompactTransitiveWitness
open PASoundness.PAtoCompactTransitiveClosure PASoundness.PAtoCompactPointAdjoin
open PASoundness.PAtoCompactPartialInverseOldEdge PASoundness.PAtoCompactSuccCongruenceEdgeCoverage
open PASoundness.PAtoCompactSuccCongruenceEdgeSplit PASoundness.PAtoCompactSuccCleanEndpoint
open PASoundness.PAtoCompactGraphRestriction

/-- Supplied old-graph uniqueness at competing source name 4. -/
def oldUniqueAt : Nat := imp
  (both (member 0 4) (graphFormula 6 4 28).encode) (equal 4 2)

/-- A new edge at the competing source is an old edge or the new top edge. -/
def splitAt : Nat := imp (graphFormula 9 4 28).encode
  (either (graphFormula 6 4 28).encode (both (equal 4 0) (equal 28 1)))

/-- The explicit source-domain consequence for old edges. -/
def oldEdgeSourceAt : Nat := imp (graphFormula 6 4 28).encode (member 0 4)

/-- Under the displayed old-target, no-self, split, domain and uniqueness
hypotheses, every new edge into the old target has the old preimage. The
source-domain guard for applying old uniqueness is derived explicitly from
the supplied old-edge premise; no global graph cleanliness is inferred. -/
def old_target_unique_point : KDerivation (imp (member 1 28)
    (imp targetIrreflexive (imp oldUniqueAt (imp splitAt
      (imp oldEdgeSourceAt (imp (graphFormula 9 4 28).encode (equal 4 2))))))) := by
  let T := member 1 28
  let N := targetIrreflexive
  let U := oldUniqueAt
  let S := splitAt
  let D := oldEdgeSourceAt
  let G := (graphFormula 9 4 28).encode
  let O := (graphFormula 6 4 28).encode
  let E := both (equal 4 0) (equal 28 1)
  let Γ := [G,D,S,U,N,T]
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  have ht : Context Γ T := .hypothesis (by simp [Γ])
  have hn : Context Γ N := .hypothesis (by simp [Γ])
  have hu : Context Γ U := .hypothesis (by simp [Γ])
  have hs : Context Γ S := .hypothesis (by simp [Γ])
  have hd : Context Γ D := .hypothesis (by simp [Γ])
  have hg : Context Γ G := .hypothesis (by simp [Γ])
  have hc : Context Γ (either O E) := .mp hg hs
  apply Context.disjunctionElim hc
  · have ho : Context (O :: Γ) O := Context.head Γ O
    have hsource : Context (O :: Γ) (member 0 4) := .mp ho (Context.under hd O)
    have hold : Context (O :: Γ) (both (member 0 4) O) := Context.conjunctionIntro hsource ho
    exact .mp hold (Context.under hu O)
  · have he : Context (E :: Γ) E := Context.head Γ E
    have htEq : Context (E :: Γ) (equal 28 1) := Context.conjunctionRight he
    have hself : Context (E :: Γ) (member 1 1) :=
      .mp htEq (.mp (Context.under ht E) (.closed (memberRightEquality 1 28 1)))
    have hbot : Context (E :: Γ) 1 := .mp hself (Context.under hn E)
    exact Context.explode (equal 4 2) hbot

theorem old_target_unique_point_certificate :
    theoremCode (certificate old_target_unique_point) =
      imp (member 1 28) (imp targetIrreflexive (imp oldUniqueAt (imp splitAt
        (imp oldEdgeSourceAt (imp (graphFormula 9 4 28).encode (equal 4 2)))))) :=
  certificate_correct old_target_unique_point

/-- Uniform versions use the fresh binder 29 so that generalization over the
new clause's competing-source name 4 is capture-safe. -/
def oldUniqueUniform : Formula := .all 29 (.imp
  (namedBoth (.member 0 29) (graphFormula 6 29 28)) (.equal 29 2))

def splitUniform : Formula := .all 29 (.imp (graphFormula 9 29 28)
  (namedEither (graphFormula 6 29 28) (namedBoth (.equal 29 0) (.equal 28 1))))

def edgeDomainUniform : Formula := .all 29 (.imp (graphFormula 6 29 28) (.member 0 29))

/-- Exact new uniqueness clause for the fixed old-target name 28. -/
def newUnique : Nat := allCode 4 (imp
  (both (member 7 4) (graphFormula 9 4 28).encode) (equal 4 2))

def old_unique_instance : KDerivation (imp oldUniqueUniform.encode oldUniqueAt) := by
  let f : Formula := .imp (namedBoth (.member 0 29) (graphFormula 6 29 28)) (.equal 29 2)
  have h := CompactNamed.universalInstance 29 4 f (by decide) (by decide) (by decide)
  have hr : CompactNamed.replace 29 4 f =
      .imp (namedBoth (.member 0 4) (graphFormula 6 4 28)) (.equal 4 2) := by decide
  rw [hr] at h
  exact h

def split_instance : KDerivation (imp splitUniform.encode splitAt) := by
  let f : Formula := .imp (graphFormula 9 29 28)
    (namedEither (graphFormula 6 29 28) (namedBoth (.equal 29 0) (.equal 28 1)))
  have h := CompactNamed.universalInstance 29 4 f (by decide) (by decide) (by decide)
  have hr : CompactNamed.replace 29 4 f = .imp (graphFormula 9 4 28)
      (namedEither (graphFormula 6 4 28) (namedBoth (.equal 4 0) (.equal 28 1))) := by decide
  rw [hr] at h
  exact h

def edge_domain_instance : KDerivation (imp edgeDomainUniform.encode oldEdgeSourceAt) := by
  let f : Formula := .imp (graphFormula 6 29 28) (.member 0 29)
  have h := CompactNamed.universalInstance 29 4 f (by decide) (by decide) (by decide)
  have hr : CompactNamed.replace 29 4 f = .imp (graphFormula 6 4 28) (.member 0 4) := by decide
  rw [hr] at h
  exact h

/-- The original old uniqueness clause can be renamed away from the new
competing-source binder. This is a K alpha proof, not a semantic change. -/
def old_unique_alpha : KDerivation (imp
    (allCode 4 (imp (both (member 0 4) (graphFormula 6 4 28).encode) (equal 4 2)))
    oldUniqueUniform.encode) := by
  let f : Formula := .imp (namedBoth (.member 0 4) (graphFormula 6 4 28)) (.equal 4 2)
  have h := (CompactNamed.universalAlpha 4 29 f (by decide) (by decide) (by decide)).1
  have hr : CompactNamed.replace 4 29 f =
      .imp (namedBoth (.member 0 29) (graphFormula 6 29 28)) (.equal 29 2) := by decide
  rw [hr] at h
  exact h

/-- Quantified new-graph uniqueness follows from explicit uniform old-domain
and edge-split premises, plus old uniqueness and target irreflexivity. -/
def old_target_unique_all : KDerivation (imp (member 1 28)
    (imp targetIrreflexive (imp oldUniqueUniform.encode (imp splitUniform.encode
      (imp edgeDomainUniform.encode newUnique))))) := by
  let T := member 1 28
  let N := targetIrreflexive
  let U := oldUniqueUniform.encode
  let S := splitUniform.encode
  let D := edgeDomainUniform.encode
  let W := both (member 7 4) (graphFormula 9 4 28).encode
  let Γ := [D,S,U,N,T]
  have ht : Context Γ T := .hypothesis (by simp [Γ])
  have hn : Context Γ N := .hypothesis (by simp [Γ])
  have hu : Context Γ U := .hypothesis (by simp [Γ])
  have hs : Context Γ S := .hypothesis (by simp [Γ])
  have hd : Context Γ D := .hypothesis (by simp [Γ])
  have hu' : Context Γ oldUniqueAt := .mp hu (.closed old_unique_instance)
  have hs' : Context Γ splitAt := .mp hs (.closed split_instance)
  have hd' : Context Γ oldEdgeSourceAt := .mp hd (.closed edge_domain_instance)
  have hi : Context Γ (imp (graphFormula 9 4 28).encode (equal 4 2)) :=
    .mp hd' (.mp hs' (.mp hu' (.mp hn (.mp ht (.closed old_target_unique_point)))))
  have hpoint : Context Γ (imp W (equal 4 2)) := by
    apply Context.deduction
    have hw : Context (W :: Γ) W := Context.head Γ W
    exact .mp (Context.conjunctionRight hw) (Context.under hi W)
  have hvT : KDerivation (imp T (allCode 4 T)) := membershipVacuity 1 28 4 (by decide) (by decide)
  let fn : Formula := Formula.not (.member 1 1)
  have hvN : KDerivation (imp N (allCode 4 N)) := by
    have h := fn.vacuity 4 (by decide)
    simpa [fn, N, targetIrreflexive, Formula.not, Formula.encode, CompactProof.neg] using h
  have hvU : KDerivation (imp U (allCode 4 U)) := oldUniqueUniform.vacuity 4 (by decide)
  have hvS : KDerivation (imp S (allCode 4 S)) := splitUniform.vacuity 4 (by decide)
  have hvD : KDerivation (imp D (allCode 4 D)) := edgeDomainUniform.vacuity 4 (by decide)
  have hv : ∀ z, z ∈ Γ → KDerivation (imp z (allCode 4 z)) := by
    intro z hz
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hz
    by_cases heD : z = D
    · subst z; exact hvD
    · by_cases heS : z = S
      · subst z; exact hvS
      · by_cases heU : z = U
        · subst z; exact hvU
        · by_cases heN : z = N
          · subst z; exact hvN
          · have heT : z = T := (((hz.resolve_left heD).resolve_left heS).resolve_left heU).resolve_left heN
            subst z; exact hvT
  have hall : Context Γ newUnique := Context.generalize 4 hv hpoint
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  exact hall

theorem old_target_unique_all_certificate :
    theoremCode (certificate old_target_unique_all) = imp (member 1 28)
      (imp targetIrreflexive (imp oldUniqueUniform.encode (imp splitUniform.encode
        (imp edgeDomainUniform.encode newUnique)))) :=
  certificate_correct old_target_unique_all

/-- A supplied old preimage and its guarded uniqueness certificate. -/
def oldWitnessBody (v : Nat) : Formula := namedBoth (.member 0 2)
  (namedBoth (graphFormula 6 2 v)
    (.all 4 (.imp (namedBoth (.member 0 4) (graphFormula 6 4 v)) (.equal 4 2))))

def oldWitness (v : Nat) : Formula := .ex 2 (oldWitnessBody v)

def sourceInclusionUniform : Formula := .all 29 (.imp (.member 0 29) (.member 7 29))

def graphInclusionUniform : Formula := .all 29
  (.imp (graphFormula 6 29 28) (graphFormula 9 29 28))

def source_inclusion_instance : KDerivation (imp sourceInclusionUniform.encode
    (imp (member 0 2) (member 7 2))) := by
  let f : Formula := .imp (.member 0 29) (.member 7 29)
  have h := CompactNamed.universalInstance 29 2 f (by decide) (by decide) (by decide)
  have hr : CompactNamed.replace 29 2 f = .imp (.member 0 2) (.member 7 2) := by decide
  rw [hr] at h
  exact h

def graph_inclusion_instance : KDerivation (imp graphInclusionUniform.encode
    (imp (graphFormula 6 2 28).encode (graphFormula 9 2 28).encode)) := by
  let f : Formula := .imp (graphFormula 6 29 28) (graphFormula 9 29 28)
  have h := CompactNamed.universalInstance 29 2 f (by decide) (by decide) (by decide)
  have hr : CompactNamed.replace 29 2 f =
      .imp (graphFormula 6 2 28) (graphFormula 9 2 28) := by decide
  rw [hr] at h
  exact h

/-- An old preimage witness transfers to the exact new preimage body under
the explicit uniform inclusions, edge split and old-edge domain premise. -/
def old_target_witness_transfer : KDerivation (imp (member 1 28)
    (imp targetIrreflexive (imp splitUniform.encode (imp edgeDomainUniform.encode
      (imp sourceInclusionUniform.encode (imp graphInclusionUniform.encode
        (imp (oldWitness 28).encode (rightBody 28).encode))))))) := by
  let T := member 1 28
  let N := targetIrreflexive
  let S := splitUniform.encode
  let D := edgeDomainUniform.encode
  let I := sourceInclusionUniform.encode
  let J := graphInclusionUniform.encode
  let O := (oldWitnessBody 28).encode
  let V : Formula := namedBoth (.member 7 2) (namedBoth (graphFormula 9 2 28)
    (.all 4 (.imp (namedBoth (.member 7 4) (graphFormula 9 4 28)) (.equal 4 2))))
  let Γ := [J,I,D,S,N,T]
  have ht : Context Γ T := .hypothesis (by simp [Γ])
  have hn : Context Γ N := .hypothesis (by simp [Γ])
  have hs : Context Γ S := .hypothesis (by simp [Γ])
  have hd : Context Γ D := .hypothesis (by simp [Γ])
  have hi : Context Γ I := .hypothesis (by simp [Γ])
  have hj : Context Γ J := .hypothesis (by simp [Γ])
  have hlocal : Context Γ (imp O V.encode) := by
    apply Context.deduction
    have ho : Context (O :: Γ) O := Context.head Γ O
    have hsource : Context (O :: Γ) (member 0 2) := Context.conjunctionLeft ho
    have hedge : Context (O :: Γ) (graphFormula 6 2 28).encode :=
      Context.conjunctionLeft (Context.conjunctionRight ho)
    have hu : Context (O :: Γ) (allCode 4 (imp
        (both (member 0 4) (graphFormula 6 4 28).encode) (equal 4 2))) :=
      Context.conjunctionRight (Context.conjunctionRight ho)
    have hu' : Context (O :: Γ) oldUniqueUniform.encode := .mp hu (.closed old_unique_alpha)
    have hnewU : Context (O :: Γ) newUnique :=
      .mp (Context.under hd O) (.mp (Context.under hs O) (.mp hu'
        (.mp (Context.under hn O) (.mp (Context.under ht O) (.closed old_target_unique_all)))))
    have hnewS : Context (O :: Γ) (member 7 2) :=
      .mp hsource (.mp (Context.under hi O) (.closed source_inclusion_instance))
    have hnewG : Context (O :: Γ) (graphFormula 9 2 28).encode :=
      .mp hedge (.mp (Context.under hj O) (.closed graph_inclusion_instance))
    exact Context.conjunctionIntro hnewS (Context.conjunctionIntro hnewG hnewU)
  have hvT : KDerivation (imp T (allCode 2 T)) := membershipVacuity 1 28 2 (by decide) (by decide)
  let fn : Formula := Formula.not (.member 1 1)
  have hvN : KDerivation (imp N (allCode 2 N)) := by
    have h := fn.vacuity 2 (by decide)
    simpa [fn,N,targetIrreflexive,Formula.not,Formula.encode,CompactProof.neg] using h
  have hvS : KDerivation (imp S (allCode 2 S)) := splitUniform.vacuity 2 (by decide)
  have hvD : KDerivation (imp D (allCode 2 D)) := edgeDomainUniform.vacuity 2 (by decide)
  have hvI : KDerivation (imp I (allCode 2 I)) := sourceInclusionUniform.vacuity 2 (by decide)
  have hvJ : KDerivation (imp J (allCode 2 J)) := graphInclusionUniform.vacuity 2 (by decide)
  have hv : ∀ z, z ∈ Γ → KDerivation (imp z (allCode 2 z)) := by
    intro z hz
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hz
    by_cases heJ : z = J
    · subst z; exact hvJ
    · by_cases heI : z = I
      · subst z; exact hvI
      · by_cases heD : z = D
        · subst z; exact hvD
        · by_cases heS : z = S
          · subst z; exact hvS
          · by_cases heN : z = N
            · subst z; exact hvN
            · have heT : z = T := ((((hz.resolve_left heJ).resolve_left heI).resolve_left heD).resolve_left heS).resolve_left heN
              subst z; exact hvT
  have hall : Context Γ (allCode 2 (imp O V.encode)) := Context.generalize 2 hv hlocal
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  have hw : Context ((oldWitness 28).encode :: Γ) (existsCode 2 O) := Context.head _ _
  have hall' : Context ((oldWitness 28).encode :: Γ) (allCode 2 (imp O V.encode)) := Context.under hall _
  change Context ((oldWitness 28).encode :: Γ) (existsCode 2 V.encode)
  exact exists_map_context hall' hw

theorem old_target_witness_transfer_certificate :
    theoremCode (certificate old_target_witness_transfer) = imp (member 1 28)
      (imp targetIrreflexive (imp splitUniform.encode (imp edgeDomainUniform.encode
        (imp sourceInclusionUniform.encode (imp graphInclusionUniform.encode
          (imp (oldWitness 28).encode (rightBody 28).encode)))))) :=
  certificate_correct old_target_witness_transfer

/-- The exact old right-bijection clause and its companion, for extracting
the existing preimage witness from the supplied old matrix. -/
def oldRightClause : Formula := .all 3 (.imp (.member 1 3) (oldWitness 3))

def oldLeftClause : Formula := .all 2 (.imp (.member 0 2) (.ex 3
  (namedBoth (.member 1 3) (namedBoth (graphFormula 6 2 3)
    (.all 4 (.imp (namedBoth (.member 1 4) (graphFormula 6 2 4)) (.equal 4 3)))))))

theorem old_bijection_alignment : bijectionFormula = namedBoth oldLeftClause oldRightClause := by decide

/-- The old matrix supplies a preimage witness for each old target, at the
fresh target label 28 used in the new-clause proof. -/
def old_target_witness : KDerivation (imp oldMatrix
    (imp (member 1 28) (oldWitness 28).encode)) := by
  let f : Formula := .imp (.member 1 3) (oldWitness 3)
  have h := CompactNamed.universalInstance 3 28 f (by decide) (by decide) (by decide)
  have hr : CompactNamed.replace 3 28 f = .imp (.member 1 28) (oldWitness 28) := by decide
  rw [hr] at h
  have h' : KDerivation (imp oldRightClause.encode
      (imp (member 1 28) (oldWitness 28).encode)) := h
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [oldMatrix]
  have hm : Context Γ oldMatrix := Context.head [] _
  have hb : Context Γ bijectionFormula.encode := Context.conjunctionLeft hm
  rw [old_bijection_alignment] at hb
  have hr' : Context Γ oldRightClause.encode := Context.conjunctionRight hb
  exact .mp hr' (.closed h')

/-- The old-target branch of the new right-bijection clause. The displayed
uniform split, domain and inclusion premises remain explicit. -/
def old_target_case : KDerivation (imp oldMatrix (imp targetIrreflexive
    (imp splitUniform.encode (imp edgeDomainUniform.encode
      (imp sourceInclusionUniform.encode (imp graphInclusionUniform.encode
        (imp (member 1 28) (rightBody 28).encode))))))) := by
  let M := oldMatrix
  let N := targetIrreflexive
  let S := splitUniform.encode
  let D := edgeDomainUniform.encode
  let I := sourceInclusionUniform.encode
  let J := graphInclusionUniform.encode
  let T := member 1 28
  let Γ := [T,J,I,D,S,N,M]
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  have hm : Context Γ M := .hypothesis (by simp [Γ])
  have hn : Context Γ N := .hypothesis (by simp [Γ])
  have hs : Context Γ S := .hypothesis (by simp [Γ])
  have hd : Context Γ D := .hypothesis (by simp [Γ])
  have hi : Context Γ I := .hypothesis (by simp [Γ])
  have hj : Context Γ J := .hypothesis (by simp [Γ])
  have ht : Context Γ T := .hypothesis (by simp [Γ])
  have hw : Context Γ (oldWitness 28).encode := .mp ht (.mp hm (.closed old_target_witness))
  exact .mp hw (.mp hj (.mp hi (.mp hd (.mp hs (.mp hn (.mp ht (.closed old_target_witness_transfer)))))))

theorem old_target_case_certificate : theoremCode (certificate old_target_case) =
    imp oldMatrix (imp targetIrreflexive (imp splitUniform.encode (imp edgeDomainUniform.encode
      (imp sourceInclusionUniform.encode (imp graphInclusionUniform.encode
        (imp (member 1 28) (rightBody 28).encode)))))) := certificate_correct old_target_case

/-- The supplied source-successor graph yields the uniform old-source
inclusion needed by the old-target witness transfer. -/
def source_inclusion_from_successor : KDerivation
    (imp sourceSuccessor sourceInclusionUniform.encode) := by
  let S := sourceSuccessor
  let F : Formula := .imp (.member 0 29) (.member 7 29)
  have hpoint : KDerivation (imp S F.encode) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [member 0 29,S]
    have hm : Context Γ (member 0 29) := Context.head _ _
    have hs : Context Γ S := .hypothesis (by simp [Γ])
    have he : Context Γ (either (equal 29 0) (member 0 29)) :=
      Context.disjunctionRight (a := equal 29 0) hm
    exact .mp he (.mp hs (.closed (successor_include 0 7 14 29 (by decide) (by decide) (by decide))))
  have hv : KDerivation (imp S (allCode 29 S)) :=
    successor_vacuity 0 7 14 29 (by decide) (by decide) (by decide)
  apply Context.closeEmpty
  apply Context.deduction
  have hs : Context [S] S := Context.head [] _
  have hp : Context [S] F.encode := .mp hs (.closed hpoint)
  exact Context.generalize 29 (by
    intro z hz
    have he : z = S := by simpa using hz
    subst z
    exact hv) hp

/-- Point adjunction preserves every old edge at the displayed old target. -/
def graph_inclusion_from_adjoin : KDerivation
    (imp newGraph graphInclusionUniform.encode) := by
  let A := newGraph
  let F : Formula := .imp (graphFormula 6 29 28) (graphFormula 9 29 28)
  have hp : KDerivation (imp A F.encode) :=
    compose old_inclusion (graph_edge_monotone 6 9 29 28)
  have hv : KDerivation (imp A (allCode 29 A)) := by
    have h := (namedAdjoin 6 11 9 16).vacuity 29 (by decide)
    simpa [A,newGraph,namedAdjoin,namedBoth,namedEither,adjoinCode,Formula.encode,
      CompactProof.both,CompactProof.neg,CompactDerivations.either] using h
  apply Context.closeEmpty
  apply Context.deduction
  have ha : Context [A] A := Context.head [] _
  have hf : Context [A] F.encode := .mp ha (.closed hp)
  exact Context.generalize 29 (by
    intro z hz
    have he : z = A := by simpa using hz
    subst z
    exact hv) hf

/-- A supplied clean old graph yields the uniform old-source endpoint guard. -/
def edge_domain_from_clean : KDerivation
    (imp cleanGraph edgeDomainUniform.encode) := by
  let C := cleanGraph
  let F : Formula := .imp (graphFormula 6 29 28) (.member 0 29)
  have hp : KDerivation (imp C F.encode) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [(graphFormula 6 29 28).encode,C]
    have hg : Context Γ (graphFormula 6 29 28).encode := Context.head _ _
    have hc : Context Γ C := .hypothesis (by simp [Γ])
    exact Context.conjunctionLeft (.mp hg (.mp hc (.closed (clean_endpoints 29 28 (by decide)))))
  let f : Formula := .all 19 (.imp (.member 6 19) (edgePredicate 19 0 1))
  have hv : KDerivation (imp C (allCode 29 C)) := by
    have h := f.vacuity 29 (by decide)
    simpa [f,C,cleanGraph,Formula.encode] using h
  apply Context.closeEmpty
  apply Context.deduction
  have hc : Context [C] C := Context.head [] _
  have hf : Context [C] F.encode := .mp hc (.closed hp)
  exact Context.generalize 29 (by
    intro z hz
    have he : z = C := by simpa using hz
    subst z
    exact hv) hf

/-- Specialize the established two-coordinate edge split to old target 28
and then quantify the fresh competing-source name 29. -/
def split_from_adjoin_pair : KDerivation
    (imp newGraph (imp newPair splitUniform.encode)) := by
  let f : Formula := .imp (graphFormula 9 2 3) conclusion
  let f29 : Formula := .imp (graphFormula 9 29 3)
    (namedEither (graphFormula 6 29 3) (namedBoth (.equal 29 0) (.equal 3 1)))
  let f2928 : Formula := .imp (graphFormula 9 29 28)
    (namedEither (graphFormula 6 29 28) (namedBoth (.equal 29 0) (.equal 28 1)))
  have hi2 := CompactNamed.universalInstance 2 29 (.all 3 f) (by decide) (by decide) (by decide)
  have hr2 : CompactNamed.replace 2 29 (.all 3 f) = .all 3 f29 := by decide
  rw [hr2] at hi2
  have hi3 := CompactNamed.universalInstance 3 28 f29 (by decide) (by decide) (by decide)
  have hr3 : CompactNamed.replace 3 28 f29 = f2928 := by decide
  rw [hr3] at hi3
  have hp : KDerivation (imp (allCode 2 (allCode 3 f.encode)) f2928.encode) := compose hi2 hi3
  let A := newGraph
  let P := newPair
  let Γ := [P,A]
  have ha : Context Γ A := .hypothesis (by simp [Γ])
  have hpair : Context Γ P := Context.head _ _
  have hall : Context Γ (allCode 2 (allCode 3 f.encode)) :=
    .mp hpair (.mp ha (.closed edge_split_all))
  have hlocal : Context Γ f2928.encode := .mp hall (.closed hp)
  have hvA : KDerivation (imp A (allCode 29 A)) := by
    have h := (namedAdjoin 6 11 9 16).vacuity 29 (by decide)
    simpa [A,newGraph,namedAdjoin,namedBoth,namedEither,adjoinCode,Formula.encode,
      CompactProof.both,CompactProof.neg,CompactDerivations.either] using h
  have hvP : KDerivation (imp P (allCode 29 P)) := (pairFormula 11 0 1).vacuity 29 (by decide)
  have hv : ∀ z, z ∈ Γ → KDerivation (imp z (allCode 29 z)) := by
    intro z hz
    simp only [Γ,List.mem_cons,List.not_mem_nil,or_false] at hz
    by_cases he : z = P
    · subst z; exact hvP
    · have he' : z = A := hz.resolve_left he
      subst z; exact hvA
  have hresult : Context Γ splitUniform.encode := Context.generalize 29 hv hlocal
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  exact hresult

/-- The completed old-target branch, using only the supplied old matrix,
clean old graph, source successor, target irreflexivity, and new graph/pair.
The original target-domain hypothesis remains explicit. -/
def old_target_case_from_data : KDerivation (imp oldMatrix (imp cleanGraph
    (imp sourceSuccessor (imp targetIrreflexive (imp newGraph (imp newPair
      (imp (member 1 28) (rightBody 28).encode))))))) := by
  let Γ := [member 1 28,newPair,newGraph,targetIrreflexive,sourceSuccessor,cleanGraph,oldMatrix]
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  have hm : Context Γ oldMatrix := .hypothesis (by simp [Γ])
  have hc : Context Γ cleanGraph := .hypothesis (by simp [Γ])
  have hsrc : Context Γ sourceSuccessor := .hypothesis (by simp [Γ])
  have hn : Context Γ targetIrreflexive := .hypothesis (by simp [Γ])
  have ha : Context Γ newGraph := .hypothesis (by simp [Γ])
  have hp : Context Γ newPair := .hypothesis (by simp [Γ])
  have ht : Context Γ (member 1 28) := .hypothesis (by simp [Γ])
  have hS : Context Γ splitUniform.encode := .mp hp (.mp ha (.closed split_from_adjoin_pair))
  have hD : Context Γ edgeDomainUniform.encode := .mp hc (.closed edge_domain_from_clean)
  have hI : Context Γ sourceInclusionUniform.encode := .mp hsrc (.closed source_inclusion_from_successor)
  have hJ : Context Γ graphInclusionUniform.encode := .mp ha (.closed graph_inclusion_from_adjoin)
  exact .mp ht (.mp hJ (.mp hI (.mp hD (.mp hS (.mp hn (.mp hm (.closed old_target_case)))))))

theorem old_target_case_from_data_certificate :
    theoremCode (certificate old_target_case_from_data) = imp oldMatrix (imp cleanGraph
      (imp sourceSuccessor (imp targetIrreflexive (imp newGraph (imp newPair
        (imp (member 1 28) (rightBody 28).encode)))))) :=
  certificate_correct old_target_case_from_data

end PASoundness.PAtoCompactSuccRightOldCase

#print axioms PASoundness.PAtoCompactSuccRightOldCase.old_target_unique_point
#print axioms PASoundness.PAtoCompactSuccRightOldCase.old_target_unique_point_certificate
#print axioms PASoundness.PAtoCompactSuccRightOldCase.old_unique_alpha
#print axioms PASoundness.PAtoCompactSuccRightOldCase.old_target_unique_all
#print axioms PASoundness.PAtoCompactSuccRightOldCase.old_target_unique_all_certificate
#print axioms PASoundness.PAtoCompactSuccRightOldCase.old_target_witness_transfer
#print axioms PASoundness.PAtoCompactSuccRightOldCase.old_target_witness_transfer_certificate
#print axioms PASoundness.PAtoCompactSuccRightOldCase.old_target_witness
#print axioms PASoundness.PAtoCompactSuccRightOldCase.old_target_case
#print axioms PASoundness.PAtoCompactSuccRightOldCase.old_target_case_certificate
#print axioms PASoundness.PAtoCompactSuccRightOldCase.old_target_case_from_data
#print axioms PASoundness.PAtoCompactSuccRightOldCase.old_target_case_from_data_certificate
