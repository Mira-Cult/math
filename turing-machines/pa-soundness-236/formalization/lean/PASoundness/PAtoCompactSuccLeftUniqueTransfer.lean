import PASoundness.PAtoCompactOrderIsomorphism
import PASoundness.CompactDerivations

/-! Pointwise K transfer of old-target uniqueness to an adjoined graph.
The old-edge target-domain guard, new-edge split, old uniqueness, source
membership and encoded source irreflexivity are explicit antecedents. This
constructs no graph, proves no totality or quotient law, and never assumes
that compact code 1 is false in arbitrary raw K models. -/
namespace PASoundness.PAtoCompactSuccLeftUniqueTransfer
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactOrderIsomorphism

/-- Old uniqueness for the fixed source 2, chosen target 3 and competitor 4. -/
def oldUnique : Nat := imp (both (member 1 4) (graphFormula 6 2 4).encode) (equal 4 3)

/-- The explicitly supplied old-edge target guard. -/
def oldTargetGuard : Nat := imp (graphFormula 6 2 4).encode (member 1 4)

/-- The pointwise supplied old/new split of a graph-9 edge. -/
def edgeSplit : Nat := imp (graphFormula 9 2 4).encode
  (either (graphFormula 6 2 4).encode (both (equal 2 0) (equal 4 1)))

/-- An old source cannot be the newly adjoined source, under encoded
irreflexivity; all graph and target-domain premises are retained. -/
def competitor_unique : KDerivation (imp oldUnique (imp edgeSplit
    (imp oldTargetGuard (imp (neg (member 0 0)) (imp (member 0 2)
      (imp (graphFormula 9 2 4).encode (equal 4 3))))))) := by
  let U := oldUnique
  let S := edgeSplit
  let G := oldTargetGuard
  let N := neg (member 0 0)
  let M := member 0 2
  let A := (graphFormula 9 2 4).encode
  let O := (graphFormula 6 2 4).encode
  let T := both (equal 2 0) (equal 4 1)
  let Γ := [A,M,N,G,S,U]
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  have hu : Context Γ U := .hypothesis (by simp [Γ])
  have hs : Context Γ S := .hypothesis (by simp [Γ])
  have hg : Context Γ G := .hypothesis (by simp [Γ])
  have hn : Context Γ N := .hypothesis (by simp [Γ])
  have hm : Context Γ M := .hypothesis (by simp [Γ])
  have ha : Context Γ A := Context.head _ _
  have hcases : Context Γ (either O T) := .mp ha hs
  apply Context.disjunctionElim hcases
  · have ho : Context (O :: Γ) O := Context.head Γ O
    have htarget : Context (O :: Γ) (member 1 4) := .mp ho (Context.under hg O)
    have hguarded : Context (O :: Γ) (both (member 1 4) O) := Context.conjunctionIntro htarget ho
    exact .mp hguarded (Context.under hu O)
  · have ht : Context (T :: Γ) T := Context.head Γ T
    have heq : Context (T :: Γ) (equal 2 0) := Context.conjunctionLeft ht
    have hself : Context (T :: Γ) (member 0 0) :=
      .mp heq (.mp (Context.under hm T) (.closed (memberRightEquality 0 2 0)))
    have hbottom : Context (T :: Γ) 1 := .mp hself (Context.under hn T)
    exact Context.explode (equal 4 3) hbottom

theorem competitor_unique_certificate : theoremCode (certificate competitor_unique) =
    imp oldUnique (imp edgeSplit (imp oldTargetGuard (imp (neg (member 0 0))
      (imp (member 0 2) (imp (graphFormula 9 2 4).encode (equal 4 3)))))) :=
  certificate_correct competitor_unique

/-- A source/edge uniqueness implication also accepts an explicit target-domain
guard in its antecedent. This is propositional K proof data. -/
def add_target_guard (A X C : Nat) : KDerivation (imp (imp A C) (imp (both X A) C)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [both X A, imp A C]
  have ha : Context Γ (both X A) := Context.head _ _
  have hi : Context Γ (imp A C) := .hypothesis (by simp [Γ])
  exact .mp (Context.conjunctionRight ha) hi

/-- Uniform uniqueness for new targets of one old source. The uniformly
quantified old target-guard and edge-split premises are explicit, as are
the old guarded uniqueness clause and encoded source irreflexivity. -/
def competitor_unique_all : KDerivation
    (imp (allCode 4 oldUnique) (imp (allCode 4 edgeSplit)
      (imp (allCode 4 oldTargetGuard) (imp (neg (member 0 0)) (imp (member 0 2)
        (allCode 4 (imp (both (member 8 4) (graphFormula 9 2 4).encode) (equal 4 3)))))))) := by
  let U := allCode 4 oldUnique
  let S := allCode 4 edgeSplit
  let G := allCode 4 oldTargetGuard
  let N := neg (member 0 0)
  let M := member 0 2
  let A := (graphFormula 9 2 4).encode
  let C := equal 4 3
  let Γ := [M,N,G,S,U]
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  have hu : Context Γ U := .hypothesis (by simp [Γ])
  have hs : Context Γ S := .hypothesis (by simp [Γ])
  have hg : Context Γ G := .hypothesis (by simp [Γ])
  have hn : Context Γ N := .hypothesis (by simp [Γ])
  have hm : Context Γ M := Context.head _ _
  have hvN : KDerivation (imp N (allCode 4 N)) :=
    negationVacuity 4 (membershipVacuity 0 0 4 (by decide) (by decide))
  have hvM : KDerivation (imp M (allCode 4 M)) :=
    membershipVacuity 0 2 4 (by decide) (by decide)
  have hN : Context Γ (allCode 4 N) := .mp hn (.closed hvN)
  have hM : Context Γ (allCode 4 M) := .mp hm (.closed hvM)
  have h0 := Context.allMP hu (.closed (.generalize 4 competitor_unique))
  have h1 := Context.allMP hs h0
  have h2 := Context.allMP hg h1
  have h3 := Context.allMP hN h2
  have h4 : Context Γ (allCode 4 (imp A C)) := Context.allMP hM h3
  exact Context.allMP h4 (.closed (.generalize 4 (add_target_guard A (member 8 4) C)))

theorem competitor_unique_all_certificate : theoremCode (certificate competitor_unique_all) =
    imp (allCode 4 oldUnique) (imp (allCode 4 edgeSplit)
      (imp (allCode 4 oldTargetGuard) (imp (neg (member 0 0)) (imp (member 0 2)
        (allCode 4 (imp (both (member 8 4) (graphFormula 9 2 4).encode) (equal 4 3))))))) :=
  certificate_correct competitor_unique_all

end PASoundness.PAtoCompactSuccLeftUniqueTransfer

#print axioms PASoundness.PAtoCompactSuccLeftUniqueTransfer.competitor_unique
#print axioms PASoundness.PAtoCompactSuccLeftUniqueTransfer.competitor_unique_certificate
#print axioms PASoundness.PAtoCompactSuccLeftUniqueTransfer.competitor_unique_all
#print axioms PASoundness.PAtoCompactSuccLeftUniqueTransfer.competitor_unique_all_certificate
