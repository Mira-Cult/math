import PASoundness.PAtoCompactSuccBijectionLeft

/-! Capture-safe quantification of an explicitly supplied pointwise witness
for the left clause of the unequal-top addition graph. The witness has
stronger unguarded uniqueness; the target clause asks only uniqueness among
target-domain members. This is a conditional K proof constructor, not a proof
of the pointwise witness, bijection, addition totality, or PA soundness. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactAdditionLeftQuantified
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactSuccBijectionLeft
open PASoundness.PAtoCompactZeroSuccessor
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Strong witness supplied by the old-source and top-source point proofs. -/
def strongBody : Formula := namedBoth (.member 40 3) (namedBoth (graphFormula 9 2 3)
  (.all 4 (.imp (graphFormula 9 2 4) (.equal 4 3))))
/-- Literal witness required by the first bijection conjunct. -/
def weakBody : Formula := namedBoth (.member 40 3) (namedBoth (graphFormula 9 2 3)
  (.all 4 (.imp (namedBoth (.member 40 4) (graphFormula 9 2 4)) (.equal 4 3))))
/-- First bijection conjunct with source 38, target 40, and graph 9. -/
def leftClause : Formula := .all 2 (.imp (.member 38 2) (.ex 3 weakBody))

theorem left_clause_alignment :
    replace 8 40 (replace 7 38 leftFormula) = leftClause := by decide

/-- Unguarded graph uniqueness gives uniqueness restricted to the new target. -/
def strong_implies_weak : KDerivation (imp strongBody.encode weakBody.encode) := by
  let G := (graphFormula 9 2 4).encode
  let E := equal 4 3
  let M := member 40 4
  have hpoint : KDerivation (imp (imp G E) (imp (both M G) E)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [both M G,imp G E]
    have hp : Context Γ (both M G) := .head _ _
    have hi : Context Γ (imp G E) := .hypothesis (by simp [Γ])
    exact .mp (Context.conjunctionRight hp) hi
  have hall : KDerivation (imp (allCode 4 (imp G E))
      (allCode 4 (imp (both M G) E))) := allCongr 4 hpoint
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [strongBody.encode]
  have h : Context Γ strongBody.encode := .head _ _
  change Context Γ (both (member 40 3) (both (graphFormula 9 2 3).encode
    (allCode 4 (imp G E)))) at h
  change Context Γ (both (member 40 3) (both (graphFormula 9 2 3).encode
    (allCode 4 (imp (both M G) E))))
  exact Context.conjunctionIntro (Context.conjunctionLeft h)
    (Context.conjunctionIntro (Context.conjunctionLeft (Context.conjunctionRight h))
      (.mp (Context.conjunctionRight (Context.conjunctionRight h)) (.closed hall)))

/-- Quantify a pointwise witness, retaining the supplied K vacuity of the
common premise at the source variable. -/
def left_from_point (P : Nat)
    (hVacuity : KDerivation (imp P (allCode 2 P)))
    (hPoint : KDerivation (imp P (imp (member 38 2) (existsCode 3 strongBody.encode)))) :
    KDerivation (imp P leftClause.encode) := by
  have hmap : KDerivation (imp (existsCode 3 strongBody.encode) (existsCode 3 weakBody.encode)) :=
    existsCongr 3 strong_implies_weak
  have hlocal : Context [P] (imp (member 38 2) (existsCode 3 weakBody.encode)) := by
    apply Context.deduction
    let Γ := [member 38 2,P]
    have hp : Context Γ P := .hypothesis (by simp [Γ])
    have hm : Context Γ (member 38 2) := .head _ _
    exact .mp (.mp hm (.mp hp (.closed hPoint))) (.closed hmap)
  have hv : ∀ z, z ∈ [P] → KDerivation (imp z (allCode 2 z)) := by
    intro z hz
    have he : z = P := by simpa only [List.mem_singleton] using hz
    cases he
    exact hVacuity
  have hall : Context [P] (allCode 2 (imp (member 38 2) (existsCode 3 weakBody.encode))) :=
    Context.generalize 2 hv hlocal
  apply Context.closeEmpty
  apply Context.deduction
  exact hall

theorem left_from_point_certificate (P : Nat)
    (hVacuity : KDerivation (imp P (allCode 2 P)))
    (hPoint : KDerivation (imp P (imp (member 38 2) (existsCode 3 strongBody.encode)))) :
    theoremCode (certificate (left_from_point P hVacuity hPoint)) = imp P leftClause.encode :=
  certificate_correct (left_from_point P hVacuity hPoint)
end PASoundness.PAtoCompactAdditionLeftQuantified
#print axioms PASoundness.PAtoCompactAdditionLeftQuantified.strong_implies_weak
#print axioms PASoundness.PAtoCompactAdditionLeftQuantified.left_from_point
#print axioms PASoundness.PAtoCompactAdditionLeftQuantified.left_from_point_certificate
