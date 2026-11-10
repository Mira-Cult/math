import PASoundness.PAtoCompactFirstAdditionCleanSuffix
import PASoundness.PAtoCompactSecondAdditionCleanSuffix
import PASoundness.PAtoCompactSeededSpanMatrixFromCommonCutSource
import PASoundness.PAtoCompactFreeVacuity

/-! Two literal addition witnesses with the same candidate operands and
candidate results yield an isomorphism matrix between the results. Actual
cuts, suffixes and clean graphs are retained through the finite K proof. -/
namespace PASoundness.PAtoCompactAdditionRawOutputEquivalence

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactFreeVacuity
open PASoundness.PAtoCompactPartialCompositionAtSource

set_option maxRecDepth 262144
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

private abbrev A1 := PASoundness.PAtoCompactFirstAdditionCutAllocation.addition
private abbrev A2 := PASoundness.PAtoCompactSecondAdditionCutAllocation.addition
private abbrev B1 := PASoundness.PAtoCompactFirstAdditionCleanSuffix.strengthenedBody
private abbrev B2 := PASoundness.PAtoCompactSecondAdditionCleanSuffix.strengthenedBody
private abbrev M1 := PASoundness.PAtoCompactSuffixCleanWitness.cleanMatrix
private abbrev M2 := PASoundness.PAtoCompactSecondAdditionCleanSuffixWitness.cleanMatrix
private abbrev O := PASoundness.PAtoCompactSeededSpanMatrixWitness.output
private def inner1 : Formula := .ex 31 B1
private def inner2 : Formula := .ex 38 B2

def guard : Formula := namedBoth (namedCandidate 28) (namedBoth (namedCandidate 1)
  (namedBoth (namedCandidate 0) (namedBoth (namedCandidate 8) (namedBoth A1 A2))))

private def vacNil (x : Nat) : ∀ h, h ∈ ([] : List Nat) → KDerivation (imp h (allCode x h)) := by
  intro h hh
  exact False.elim (by simpa using hh)

private def vacCons {x a : Nat} {Γ : List Nat}
    (ha : KDerivation (imp a (allCode x a)))
    (ht : ∀ h, h ∈ Γ → KDerivation (imp h (allCode x h))) :
    ∀ h, h ∈ a :: Γ → KDerivation (imp h (allCode x h)) := by
  intro h hh
  simp only [List.mem_cons] at hh
  by_cases he : h = a
  · subst h; exact ha
  · exact ht h (hh.resolve_left he)

/-- The same cut, suffix and clean-graph witnesses from each input are used
to construct one result isomorphism graph. No operand or result inequality is
assumed. -/
def raw_addition_outputs_equivalent : KDerivation (imp guard.encode O.encode) := by
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [guard.encode]
  have hg : Context Γ guard.encode := .head _ _
  have hr := Context.conjunctionRight hg
  have hr := Context.conjunctionRight hr
  have hr := Context.conjunctionRight hr
  have hr := Context.conjunctionRight hr
  have ha1 : Context Γ A1.encode := Context.conjunctionLeft hr
  have ha2 : Context Γ A2.encode := Context.conjunctionRight hr
  have hex1 : Context Γ (existsCode 40 inner1.encode) := by
    simpa only [PASoundness.PAtoCompactFirstAdditionCleanSuffix.output,inner1,Formula.encode] using
      Context.mp ha1 (.closed PASoundness.PAtoCompactFirstAdditionCleanSuffix.first_addition_clean_suffix)
  have hex2 : Context Γ (existsCode 41 inner2.encode) := by
    simpa only [PASoundness.PAtoCompactSecondAdditionCleanSuffix.output,inner2,Formula.encode] using
      Context.mp ha2 (.closed PASoundness.PAtoCompactSecondAdditionCleanSuffix.second_addition_clean_suffix)
  have hpoint : Context (M2.encode :: B2.encode :: M1.encode :: B1.encode :: Γ) O.encode := by
    let Δ := [M2.encode,B2.encode,M1.encode,B1.encode,guard.encode]
    have hm2 : Context Δ M2.encode := .head _ _
    have hb2 : Context Δ B2.encode := .hypothesis (by simp [Δ])
    have hm1 : Context Δ M1.encode := .hypothesis (by simp [Δ])
    have hb1 : Context Δ B1.encode := .hypothesis (by simp [Δ])
    have hg' : Context Δ guard.encode := .hypothesis (by simp [Δ])
    have hc28 : Context Δ (namedCandidate 28).encode := Context.conjunctionLeft hg'
    have hr := Context.conjunctionRight hg'
    have hc1 : Context Δ (namedCandidate 1).encode := Context.conjunctionLeft hr
    have hr := Context.conjunctionRight hr
    have hc0 : Context Δ (namedCandidate 0).encode := Context.conjunctionLeft hr
    have hc8 : Context Δ (namedCandidate 8).encode := Context.conjunctionLeft (Context.conjunctionRight hr)
    have hbody1 : Context Δ PASoundness.PAtoCompactFirstAdditionCutAllocation.allocatedBody.encode := Context.conjunctionLeft hb1
    have hbody2 : Context Δ PASoundness.PAtoCompactSecondAdditionCutAllocation.allocatedBody.encode := Context.conjunctionLeft hb2
    have hr1 := Context.conjunctionRight hbody1
    have hr2 := Context.conjunctionRight hbody2
    have he1 : Context Δ PASoundness.PAtoCompactSeededSpanCutEquivalenceFromEquivalences.firstEquivalence.encode := Context.conjunctionLeft hr1
    have he2 : Context Δ PASoundness.PAtoCompactSeededSpanCutEquivalenceFromEquivalences.secondEquivalence.encode := Context.conjunctionLeft hr2
    have hrel1 : Context Δ PASoundness.PAtoCompactSeededSpanCutCandidate.sourceRelation.encode := Context.conjunctionLeft hbody1
    have hrel2 : Context Δ PASoundness.PAtoCompactSeededSpanCutCandidate.targetRelation.encode := Context.conjunctionLeft hbody2
    have hf1 : Context Δ PASoundness.PAtoCompactFirstSpanPathOutside.suffixFilter.encode := Context.conjunctionLeft (Context.conjunctionRight hr1)
    have hf2 : Context Δ PASoundness.PAtoCompactFirstSpanTargetOutside.targetFilter.encode := Context.conjunctionLeft (Context.conjunctionRight hr2)
    have hp1 := Context.conjunctionLeft hm1
    have hp2 := Context.conjunctionLeft hm2
    have hbij1 : Context Δ PASoundness.PAtoCompactSeededSpanSuffixForwardCoverage.firstBijection.encode := Context.conjunctionLeft hp1
    have hbij2 : Context Δ PASoundness.PAtoCompactSeededSpanSuffixForwardCoverage.secondBijection.encode := Context.conjunctionLeft hp2
    have ho1 : Context Δ PASoundness.PAtoCompactFirstSuffixOrderWiden.suffixOrder.encode := Context.conjunctionRight hp1
    have ho2 : Context Δ PASoundness.PAtoCompactSecondSuffixOrderWiden.suffixOrder.encode := Context.conjunctionRight hp2
    have hclean1 : Context Δ PASoundness.PAtoCompactSuffixCleanGraphGuard.storedClean.encode := Context.conjunctionRight hm1
    have hclean2 : Context Δ PASoundness.PAtoCompactFirstSpanTargetOutside.targetClean.encode := Context.conjunctionRight hm2
    have hs1 : Context Δ PASoundness.PAtoCompactFirstSpanPathOutside.outsideGuard.encode := Context.conjunctionIntro hclean1 hf1
    have hs2 : Context Δ PASoundness.PAtoCompactFirstSpanTargetOutside.targetGuard.encode := Context.conjunctionIntro hclean2 hf2
    have heq : Context Δ PASoundness.PAtoCompactSeededSpanCutEquivalenceFromEquivalences.guard.encode :=
      Context.conjunctionIntro hc28 (Context.conjunctionIntro he1 he2)
    have hbase : Context Δ PASoundness.PAtoCompactSeededSpanMatrixFromCutEquivalence.fixedBase.encode :=
      Context.conjunctionIntro hc0 (Context.conjunctionIntro hc8 (Context.conjunctionIntro hrel1
        (Context.conjunctionIntro hrel2 (Context.conjunctionIntro hs1 hs2))))
    have hguard : Context Δ PASoundness.PAtoCompactSeededSpanMatrixFromCommonCutSource.guard.encode :=
      Context.conjunctionIntro heq (Context.conjunctionIntro hc1 (Context.conjunctionIntro hbij1
        (Context.conjunctionIntro hbij2 (Context.conjunctionIntro hbase (Context.conjunctionIntro ho1 ho2)))))
    exact .mp hguard (.closed PASoundness.PAtoCompactSeededSpanMatrixFromCommonCutSource.matrix_from_common_cut_source)
  let Γ7 := B2.encode :: M1.encode :: B1.encode :: Γ
  have hv7 : ∀ h, h ∈ Γ7 → KDerivation (imp h (allCode 7 h)) :=
    vacCons (free_vacuity 7 B2 (by decide)) (vacCons (free_vacuity 7 M1 (by decide))
      (vacCons (free_vacuity 7 B1 (by decide)) (vacCons (free_vacuity 7 guard (by decide)) (vacNil 7))))
  have hex7 : Context Γ7 (existsCode 7 M2.encode) := by
    have hb : Context Γ7 B2.encode := .head _ _
    exact Context.conjunctionRight hb
  have h7 : Context Γ7 O.encode := Context.existsElim (free_vacuity 7 O (by decide))
    (Context.generalize 7 hv7 (Context.deduction hpoint)) hex7
  let Γ38 := M1.encode :: B1.encode :: Γ
  have hv38 : ∀ h, h ∈ Γ38 → KDerivation (imp h (allCode 38 h)) :=
    vacCons (free_vacuity 38 M1 (by decide)) (vacCons (free_vacuity 38 B1 (by decide))
      (vacCons (free_vacuity 38 guard (by decide)) (vacNil 38)))
  have hall38 := Context.generalize 38 hv38 (Context.deduction h7)
  have h38 : Context (inner2.encode :: Γ38) O.encode := by
    have he : Context (inner2.encode :: Γ38) inner2.encode := .head _ _
    exact Context.existsElim (free_vacuity 38 O (by decide)) (.under hall38 _) he
  have hv41 : ∀ h, h ∈ Γ38 → KDerivation (imp h (allCode 41 h)) :=
    vacCons (free_vacuity 41 M1 (by decide)) (vacCons (free_vacuity 41 B1 (by decide))
      (vacCons (free_vacuity 41 guard (by decide)) (vacNil 41)))
  have hex2' : Context Γ38 (existsCode 41 inner2.encode) := .under (.under hex2 B1.encode) M1.encode
  have h41 : Context Γ38 O.encode := Context.existsElim (free_vacuity 41 O (by decide))
    (Context.generalize 41 hv41 (Context.deduction h38)) hex2'
  let Γ6 := B1.encode :: Γ
  have hv6 : ∀ h, h ∈ Γ6 → KDerivation (imp h (allCode 6 h)) :=
    vacCons (free_vacuity 6 B1 (by decide)) (vacCons (free_vacuity 6 guard (by decide)) (vacNil 6))
  have hex6 : Context Γ6 (existsCode 6 M1.encode) := by
    have hb : Context Γ6 B1.encode := .head _ _
    exact Context.conjunctionRight hb
  have h6 : Context Γ6 O.encode := Context.existsElim (free_vacuity 6 O (by decide))
    (Context.generalize 6 hv6 (Context.deduction h41)) hex6
  have hv31 : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 31 h)) :=
    vacCons (free_vacuity 31 guard (by decide)) (vacNil 31)
  have hall31 := Context.generalize 31 hv31 (Context.deduction h6)
  have h31 : Context (inner1.encode :: Γ) O.encode := by
    have he : Context (inner1.encode :: Γ) inner1.encode := .head _ _
    exact Context.existsElim (free_vacuity 31 O (by decide)) (.under hall31 _) he
  have hv40 : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 40 h)) :=
    vacCons (free_vacuity 40 guard (by decide)) (vacNil 40)
  exact Context.existsElim (free_vacuity 40 O (by decide))
    (Context.generalize 40 hv40 (Context.deduction h31)) hex1

theorem raw_addition_outputs_equivalent_certificate : theoremCode (certificate raw_addition_outputs_equivalent) =
    imp guard.encode O.encode := certificate_correct raw_addition_outputs_equivalent

end PASoundness.PAtoCompactAdditionRawOutputEquivalence

#print axioms PASoundness.PAtoCompactAdditionRawOutputEquivalence.guard
#print axioms PASoundness.PAtoCompactAdditionRawOutputEquivalence.raw_addition_outputs_equivalent
#print axioms PASoundness.PAtoCompactAdditionRawOutputEquivalence.raw_addition_outputs_equivalent_certificate
