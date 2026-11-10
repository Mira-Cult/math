import PASoundness.PAtoCompactSuffixCleanGraphGuard
import PASoundness.PAtoCompactCommonSourceSpanInputMatrices
import PASoundness.PAtoCompactScopedActiveReplace
import PASoundness.PAtoCompactFreeVacuity

/-! Widen the first graph's order clause from suffix31 to whole0. A stored-clean
graph edge supplies suffix membership for each compared output, so the actual
suffix order applies. The suffix order and stored-pair cleanliness remain
explicit K antecedents; no suffix or whole candidacy is inferred. -/
namespace PASoundness.PAtoCompactFirstSuffixOrderWiden

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactScopedActiveReplace PASoundness.PAtoCompactFreeVacuity
open PASoundness.PAtoCompactSuffixCleanGraphGuard

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def suffixOrder : Formula := replace 25 1 (replace 1 31 (replace 0 25 orderFormula))
def wholeOrder : Formula := PASoundness.PAtoCompactCommonSourceSpanInputMatrices.firstOrder
private def comparison : Formula := namedBoth (.imp (.member 4 2) (.member 5 3))
  (.imp (.member 5 3) (.member 4 2))
private def orderPoint (target : Nat) : Formula := .imp
  (namedBoth (.member 1 2) (namedBoth (.member 1 4) (namedBoth (.member target 3)
    (namedBoth (.member target 5) (namedBoth (graphFormula 6 2 3) (graphFormula 6 4 5)))))) comparison
private theorem suffix_shape : suffixOrder = .all 2 (.all 4 (.all 3 (.all 5 (orderPoint 31)))) := by decide
private theorem whole_shape : wholeOrder = .all 2 (.all 4 (.all 3 (.all 5 (orderPoint 0)))) := by decide

private def cleanFrame : Formula := .imp storedClean (.imp (graphFormula 6 2 4) (.member 31 4))
private def clean44 : Formula := replace 2 44 cleanFrame
private def clean5 : Formula := replace 4 5 clean44

private def clean_first : KDerivation (imp storedClean.encode
    (imp (graphFormula 6 2 3).encode (member 31 3))) := by
  have hbase : KDerivation cleanFrame.encode := by simpa only [cleanFrame,Formula.encode] using clean_target_point
  have h := replace_derivation 4 3 cleanFrame (by decide) (by decide) hbase
  have ha : replace 4 3 cleanFrame = .imp storedClean (.imp (graphFormula 6 2 3) (.member 31 3)) := by decide
  rw [ha] at h
  exact h

private def clean_second : KDerivation (imp storedClean.encode
    (imp (graphFormula 6 4 5).encode (member 31 5))) := by
  have hbase : KDerivation cleanFrame.encode := by simpa only [cleanFrame,Formula.encode] using clean_target_point
  have h44 := replace_derivation 2 44 cleanFrame (by decide) (by decide) hbase
  have h5 := replace_derivation 4 5 clean44 (by decide) (by decide) (by simpa only [clean44] using h44)
  have h4 := replace_derivation 44 4 clean5 (by decide) (by decide) (by simpa only [clean5] using h5)
  have ha : replace 44 4 clean5 = .imp storedClean (.imp (graphFormula 6 4 5) (.member 31 5)) := by decide
  rw [ha] at h4
  exact h4

private def suffix_at_point : KDerivation (imp suffixOrder.encode (orderPoint 31).encode) := by
  have h2 := allSpecialize 2 (.all 4 (.all 3 (.all 5 (orderPoint 31)))) (by decide)
  have h4 := allSpecialize 4 (.all 3 (.all 5 (orderPoint 31))) (by decide)
  have h3 := allSpecialize 3 (.all 5 (orderPoint 31)) (by decide)
  have h5 := allSpecialize 5 (orderPoint 31) (by decide)
  simpa only [suffix_shape,Formula.encode] using compose h2 (compose h4 (compose h3 h5))

/-- The exact first whole-domain order follows from the actual suffix order
and the explicitly supplied stored-pair-clean graph6. -/
def first_suffix_order_widen : KDerivation (imp suffixOrder.encode
    (imp storedClean.encode wholeOrder.encode)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [storedClean.encode,suffixOrder.encode]
  have hc : Context Γ storedClean.encode := .head _ _
  have ho : Context Γ suffixOrder.encode := .hypothesis (by simp [Γ])
  have hp : Context Γ (orderPoint 0).encode := by
    apply Context.deduction
    let D := (namedBoth (.member 1 2) (namedBoth (.member 1 4) (namedBoth (.member 0 3)
      (namedBoth (.member 0 5) (namedBoth (graphFormula 6 2 3) (graphFormula 6 4 5)))))).encode
    let Δ := [D,storedClean.encode,suffixOrder.encode]
    have hd : Context Δ D := .head _ _
    have hsource2 : Context Δ (member 1 2) := Context.conjunctionLeft hd
    have hr := Context.conjunctionRight hd
    have hsource4 : Context Δ (member 1 4) := Context.conjunctionLeft hr
    have hr := Context.conjunctionRight hr
    have hr := Context.conjunctionRight hr
    have hr := Context.conjunctionRight hr
    have he1 : Context Δ (graphFormula 6 2 3).encode := Context.conjunctionLeft hr
    have he2 : Context Δ (graphFormula 6 4 5).encode := Context.conjunctionRight hr
    have hc' : Context Δ storedClean.encode := .under hc D
    have ho' : Context Δ suffixOrder.encode := .under ho D
    have hm3 : Context Δ (member 31 3) := .mp he1 (.mp hc' (.closed clean_first))
    have hm5 : Context Δ (member 31 5) := .mp he2 (.mp hc' (.closed clean_second))
    have hsuffix : Context Δ (orderPoint 31).encode := .mp ho' (.closed suffix_at_point)
    have hguard : Context Δ (both (member 1 2) (both (member 1 4) (both (member 31 3)
      (both (member 31 5) (both (graphFormula 6 2 3).encode (graphFormula 6 4 5).encode))))) :=
      Context.conjunctionIntro hsource2 (Context.conjunctionIntro hsource4 (Context.conjunctionIntro hm3
        (Context.conjunctionIntro hm5 (Context.conjunctionIntro he1 he2))))
    exact .mp hguard hsuffix
  have hv (v : Nat) (freshC : v ∉ storedClean.free) (freshO : v ∉ suffixOrder.free) :
      ∀ h, h ∈ Γ → KDerivation (imp h (allCode v h)) := by
    intro h hh
    simp only [Γ,List.mem_cons,List.not_mem_nil,or_false] at hh
    by_cases he : h = storedClean.encode
    · subst h; exact free_vacuity v storedClean freshC
    · have he' : h = suffixOrder.encode := hh.resolve_left he
      subst h; exact free_vacuity v suffixOrder freshO
  have hall := Context.generalize 2 (hv 2 (by decide) (by decide))
    (Context.generalize 4 (hv 4 (by decide) (by decide))
      (Context.generalize 3 (hv 3 (by decide) (by decide))
        (Context.generalize 5 (hv 5 (by decide) (by decide)) hp)))
  simpa only [whole_shape,Formula.encode] using hall

theorem first_suffix_order_widen_certificate : theoremCode (certificate first_suffix_order_widen) =
    imp suffixOrder.encode (imp storedClean.encode wholeOrder.encode) := certificate_correct first_suffix_order_widen

end PASoundness.PAtoCompactFirstSuffixOrderWiden

#print axioms PASoundness.PAtoCompactFirstSuffixOrderWiden.suffixOrder
#print axioms PASoundness.PAtoCompactFirstSuffixOrderWiden.wholeOrder
#print axioms PASoundness.PAtoCompactFirstSuffixOrderWiden.first_suffix_order_widen
#print axioms PASoundness.PAtoCompactFirstSuffixOrderWiden.first_suffix_order_widen_certificate
