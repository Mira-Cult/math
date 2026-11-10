import PASoundness.PAtoCompactFirstSpanPathOutside

/-! The first common-source path's target-side point lies outside cut 41,
under explicit stored-pair cleanliness of graph 7 into suffix 38 and the
literal filter suffix38 = whole8 minus cut41. -/
namespace PASoundness.PAtoCompactFirstSpanTargetOutside

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactFilteredSubset PASoundness.PAtoCompactFilterInstantiation
open PASoundness.PAtoCompactFreeVacuity PASoundness.PAtoCompactScopedActiveReplace
open PASoundness.PAtoCompactSuffixCleanGraphGuard PASoundness.PAtoCompactCommonSourceSpanBase
open PASoundness.PAtoCompactSuccGraphOutputLift

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def targetClean : Formula := replace 6 7 (replace 31 38 storedClean)
def targetPredicate : Formula := (Formula.member 41 35).not
def targetFilter : Formula := .all 35 (namedFilterBody 8 38 35 targetPredicate)
def targetGuard : Formula := namedBoth targetClean targetFilter
private theorem target_filter_code : targetFilter.encode =
    filterGraph 8 38 35 (neg (member 41 35)) := by rfl
private def target : Formula := (Formula.member 41 3).not
private def original : Formula := .imp storedClean (.imp (graphFormula 6 2 4) (.member 31 4))
private def p44 : Formula := replace 2 44 original
private def p3 : Formula := replace 4 3 p44
private def p4 : Formula := replace 44 4 p3
private def p38 : Formula := replace 31 38 p4

private def clean_point : KDerivation
    (imp targetClean.encode (imp (graphFormula 7 4 3).encode (member 38 3))) := by
  have hbase : KDerivation original.encode := by simpa only [original,Formula.encode] using clean_target_point
  have h44 := replace_derivation 2 44 original (by decide) (by decide) hbase
  have h3 := replace_derivation 4 3 p44 (by decide) (by decide) (by simpa only [p44] using h44)
  have h4 := replace_derivation 44 4 p3 (by decide) (by decide) (by simpa only [p3] using h3)
  have h38 := replace_derivation 31 38 p4 (by decide) (by decide) (by simpa only [p4] using h4)
  have h7 := replace_derivation 6 7 p38 (by decide) (by decide) (by simpa only [p38] using h38)
  have ha : replace 6 7 p38 = .imp targetClean (.imp (graphFormula 7 4 3) (.member 38 3)) := by decide
  rw [ha] at h7
  exact h7

private def filter_point : KDerivation
    (imp targetFilter.encode (imp (member 38 3) (neg (member 41 3)))) := by
  have hi := filter_at 8 38 35 3 targetPredicate (by decide) (by decide) (by decide)
    (by decide) (by decide)
  have hi' : KDerivation (imp targetFilter.encode
      (both (imp (member 38 3) (both (member 8 3) (neg (member 41 3))))
        (imp (both (member 8 3) (neg (member 41 3))) (member 38 3)))) := by
    simpa [target_filter_code,targetPredicate,Formula.not,Formula.encode,replace,rename,neg] using hi
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [member 38 3,targetFilter.encode]
  have hm : Context Γ (member 38 3) := .head _ _
  have hf : Context Γ targetFilter.encode := .hypothesis (by simp [Γ])
  have hb : Context Γ (both (imp (member 38 3) (both (member 8 3) (neg (member 41 3))))
      (imp (both (member 8 3) (neg (member 41 3))) (member 38 3))) := .mp hf (.closed hi')
  have hp : Context Γ (imp (member 38 3) (both (member 8 3) (neg (member 41 3)))) :=
    Context.conjunctionLeft hb
  have hm' : Context Γ (both (member 8 3) (neg (member 41 3))) := .mp hm hp
  exact Context.conjunctionRight hm'

private def path_body_outside : KDerivation (imp targetGuard.encode
    (imp spanPathBody.encode target.encode)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [spanPathBody.encode,targetGuard.encode]
  have hb : Context Γ spanPathBody.encode := .head _ _
  have hg : Context Γ targetGuard.encode := .hypothesis (by simp [Γ])
  have hc : Context Γ targetClean.encode := Context.conjunctionLeft hg
  have hf : Context Γ targetFilter.encode := Context.conjunctionRight hg
  have he : Context Γ (graphFormula 7 4 3).encode :=
    Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight hb))
  have hm : Context Γ (member 38 3) := .mp he (.mp hc (.closed clean_point))
  exact .mp hm (.mp hf (.closed filter_point))

/-- The first actual path's target-side endpoint is outside cut 41. -/
def first_path_target_outside : KDerivation (imp targetGuard.encode
    (imp spanPath.encode (neg (member 41 3)))) := by
  have h := guarded_exists_left 4 targetGuard.encode spanPathBody.encode target.encode
    (free_vacuity 4 targetGuard (by decide)) (free_vacuity 4 target (by decide)) path_body_outside
  simpa only [spanPath,target,Formula.not,Formula.encode,CompactProof.neg] using h

theorem first_path_target_outside_certificate : theoremCode (certificate first_path_target_outside) =
    imp targetGuard.encode (imp spanPath.encode (neg (member 41 3))) :=
  certificate_correct first_path_target_outside

end PASoundness.PAtoCompactFirstSpanTargetOutside

#print axioms PASoundness.PAtoCompactFirstSpanTargetOutside.targetClean
#print axioms PASoundness.PAtoCompactFirstSpanTargetOutside.targetPredicate
#print axioms PASoundness.PAtoCompactFirstSpanTargetOutside.targetFilter
#print axioms PASoundness.PAtoCompactFirstSpanTargetOutside.targetGuard
#print axioms PASoundness.PAtoCompactFirstSpanTargetOutside.first_path_target_outside
#print axioms PASoundness.PAtoCompactFirstSpanTargetOutside.first_path_target_outside_certificate
