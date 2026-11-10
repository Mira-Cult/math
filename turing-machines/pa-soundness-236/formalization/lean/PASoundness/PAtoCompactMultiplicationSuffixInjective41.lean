import PASoundness.PAtoCompactOrderIsomorphism
import PASoundness.PAtoCompactFreeVacuity
import PASoundness.PAtoCompactAdjunction

/-! Pointwise inverse functionality of a supplied suffix bijection. This is a
finite K derivation with explicit source and target membership guards. It does
not assume uniqueness of pair representatives, construct a graph, or prove
multiplication. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactMultiplicationSuffixInjective41
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactFreeVacuity
open PASoundness.PAtoCompactAdjunction PASoundness.PAtoCompactZeroSuccessor
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Supplied bijection from source 31 to target 40, represented by graph 6. -/
def suffixBijection : Formula := replace 1 40 (replace 0 31 bijectionFormula)

private def witness (x y : Nat) : Formula := namedBoth (.member 31 x)
  (namedBoth (graphFormula 6 x y)
    (.all 4 (.imp (namedBoth (.member 31 4) (graphFormula 6 4 y)) (.equal 4 x))))
private def forwardBody : Formula := .imp (.member 31 2) (.ex 3
  (namedBoth (.member 40 3) (namedBoth (graphFormula 6 2 3)
    (.all 4 (.imp (namedBoth (.member 40 4) (graphFormula 6 2 4)) (.equal 4 3))))))
private def reverseBody : Formula := .imp (.member 40 3) (.ex 2 (witness 2 3))
private def result : Formula := .equal 41 8
private def source4 : Formula := .member 31 41
private def source8 : Formula := .member 31 8
private def target5 : Formula := .member 40 5
private def edge4 : Formula := graphFormula 6 41 5
private def edge8 : Formula := graphFormula 6 8 5
private def W : Formula := witness 2 5

private def witness_point : KDerivation (imp W.encode
    (imp source4.encode (imp source8.encode
      (imp edge4.encode (imp edge8.encode result.encode))))) := by
  have h4 := universalInstance 4 41
    (.imp (namedBoth (.member 31 4) (graphFormula 6 4 5)) (.equal 4 2))
      (by decide) (by decide) (by decide)
  have hshape4 : replace 4 41
      (.imp (namedBoth (.member 31 4) (graphFormula 6 4 5)) (.equal 4 2)) =
      .imp (namedBoth (.member 31 41) (graphFormula 6 41 5)) (.equal 41 2) := by decide
  rw [hshape4] at h4
  have h8 := universalInstance 4 8
    (.imp (namedBoth (.member 31 4) (graphFormula 6 4 5)) (.equal 4 2))
      (by decide) (by decide) (by decide)
  have hshape : replace 4 8
      (.imp (namedBoth (.member 31 4) (graphFormula 6 4 5)) (.equal 4 2)) =
      .imp (namedBoth (.member 31 8) (graphFormula 6 8 5)) (.equal 8 2) := by decide
  rw [hshape] at h8
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [edge8.encode,edge4.encode,source8.encode,source4.encode,W.encode]
  have hw : Context Γ W.encode := .hypothesis (by simp [Γ])
  have hw' : Context Γ (both (member 31 2) (both (graphFormula 6 2 5).encode
      (allCode 4 (imp (both (member 31 4) (graphFormula 6 4 5).encode) (equal 4 2))))) := by
    simpa [W,witness,namedBoth,Formula.encode,Formula.not,both,neg] using hw
  have hall := Context.conjunctionRight (Context.conjunctionRight hw')
  have hs4 : Context Γ (member 31 41) := .hypothesis (by simp [Γ,source4,Formula.encode])
  have hs8 : Context Γ (member 31 8) := .hypothesis (by simp [Γ,source8,Formula.encode])
  have he4 : Context Γ (graphFormula 6 41 5).encode := .hypothesis (by simp [Γ,edge4])
  have he8 : Context Γ (graphFormula 6 8 5).encode := .hypothesis (by simp [Γ,edge8])
  have hi4 : Context Γ (equal 41 2) := .mp (Context.conjunctionIntro hs4 he4) (.mp hall (.closed h4))
  have hi8 : Context Γ (equal 8 2) := .mp (Context.conjunctionIntro hs8 he8) (.mp hall (.closed h8))
  exact Context.eqTrans hi4 (Context.eqSymm hi8)

/-- A supplied suffix bijection maps distinct source values to distinct target
values in the literal guarded sense: two source members with edges to the
same target member are equal. -/
def inverse_unique : KDerivation (imp suffixBijection.encode
    (imp (member 40 5) (imp (member 31 41) (imp (member 31 8)
      (imp (graphFormula 6 41 5).encode (imp (graphFormula 6 8 5).encode (equal 41 8))))))) := by
  have hrev : KDerivation (imp suffixBijection.encode (allCode 3 reverseBody.encode)) := by
    apply Context.closeEmpty
    apply Context.deduction
    have hb : Context [suffixBijection.encode] suffixBijection.encode := .head _ _
    change Context [suffixBijection.encode] (both (allCode 2 forwardBody.encode)
      (allCode 3 reverseBody.encode)) at hb
    exact Context.conjunctionRight hb
  have hinst := universalInstance 3 5 reverseBody (by decide) (by decide) (by decide)
  have hshape : replace 3 5 reverseBody = .imp target5 (.ex 2 W) := by decide
  rw [hshape] at hinst
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [edge8.encode,edge4.encode,source8.encode,source4.encode,target5.encode,suffixBijection.encode]
  have he8 : Context Γ edge8.encode := .head _ _
  have he4 : Context Γ edge4.encode := .hypothesis (by simp [Γ])
  have hs8 : Context Γ source8.encode := .hypothesis (by simp [Γ])
  have hs4 : Context Γ source4.encode := .hypothesis (by simp [Γ])
  have ht : Context Γ target5.encode := .hypothesis (by simp [Γ])
  have hb : Context Γ suffixBijection.encode := .hypothesis (by simp [Γ])
  have hex : Context Γ (existsCode 2 W.encode) := .mp ht (.mp (.mp hb (.closed hrev)) (.closed hinst))
  have hp : Context Γ (imp W.encode result.encode) := by
    apply Context.deduction
    let Δ := W.encode :: Γ
    have hw : Context Δ W.encode := .head _ _
    exact .mp (.under he8 _) (.mp (.under he4 _) (.mp (.under hs8 _)
      (.mp (.under hs4 _) (.mp hw (.closed witness_point)))))
  have hv : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 2 h)) := by
    intro h hh
    simp only [Γ,List.mem_cons,List.not_mem_nil,or_false] at hh
    by_cases h1 : h = edge8.encode
    · subst h; exact free_vacuity 2 edge8 (by decide)
    by_cases h2 : h = edge4.encode
    · subst h; exact free_vacuity 2 edge4 (by decide)
    by_cases h3 : h = source8.encode
    · subst h; exact source8.vacuity 2 (by decide)
    by_cases h4 : h = source4.encode
    · subst h; exact source4.vacuity 2 (by decide)
    by_cases h5 : h = target5.encode
    · subst h; exact target5.vacuity 2 (by decide)
    have h6 : h = suffixBijection.encode := by simpa [h1,h2,h3,h4,h5] using hh
    subst h; exact free_vacuity 2 suffixBijection (by decide)
  have hall := Context.generalize 2 hv hp
  exact Context.existsElim (result.vacuity 2 (by decide)) hall hex

theorem inverse_unique_certificate : theoremCode (certificate inverse_unique) =
    imp suffixBijection.encode (imp (member 40 5) (imp (member 31 41) (imp (member 31 8)
      (imp (graphFormula 6 41 5).encode (imp (graphFormula 6 8 5).encode (equal 41 8)))))) :=
  certificate_correct inverse_unique
end PASoundness.PAtoCompactMultiplicationSuffixInjective41
#print axioms PASoundness.PAtoCompactMultiplicationSuffixInjective41.inverse_unique
#print axioms PASoundness.PAtoCompactMultiplicationSuffixInjective41.inverse_unique_certificate
