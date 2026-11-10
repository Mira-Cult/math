import PASoundness.PAtoCompactSuffixCleanGraphGuard
import PASoundness.PAtoCompactFilterInstantiation
import PASoundness.PAtoCompactSeededSpanOrderSplit
import PASoundness.PAtoCompactSuccGraphOutputLift
import PASoundness.PAtoCompactScopedActiveReplace

/-! The first common-source path lands outside cut 40 when graph 6 is stored-
pair clean into suffix 31 and the supplied suffix is whole 0 minus cut 40.
The actual path witness and both premises remain explicit; no candidate or
suffix transitivity is assumed. -/
namespace PASoundness.PAtoCompactFirstSpanPathOutside

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactFilteredSubset PASoundness.PAtoCompactFilterInstantiation
open PASoundness.PAtoCompactFreeVacuity PASoundness.PAtoCompactScopedActiveReplace
open PASoundness.PAtoCompactSuffixCleanGraphGuard PASoundness.PAtoCompactCommonSourceSpanBase
open PASoundness.PAtoCompactSuccGraphOutputLift

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def suffixPredicate : Formula := (Formula.member 40 35).not
def suffixFilter : Formula := .all 35 (namedFilterBody 0 31 35 suffixPredicate)
def outsideGuard : Formula := namedBoth storedClean suffixFilter
private theorem suffix_filter_code : suffixFilter.encode =
    filterGraph 0 31 35 (neg (member 40 35)) := by rfl
private def target : Formula := (Formula.member 40 2).not
private def original : Formula := .imp storedClean (.imp (graphFormula 6 2 4) (.member 31 4))
private def at44 : Formula := replace 2 44 original
private def at2 : Formula := replace 4 2 at44

private def clean_point : KDerivation
    (imp storedClean.encode (imp (graphFormula 6 4 2).encode (member 31 2))) := by
  have hbase : KDerivation original.encode := by
    simpa only [original,Formula.encode] using clean_target_point
  have h44 := replace_derivation 2 44 original (by decide) (by decide) hbase
  have h2 := replace_derivation 4 2 at44 (by decide) (by decide) (by simpa only [at44] using h44)
  have h4 := replace_derivation 44 4 at2 (by decide) (by decide) (by simpa only [at2] using h2)
  have ha : replace 44 4 at2 = .imp storedClean (.imp (graphFormula 6 4 2) (.member 31 2)) := by decide
  rw [ha] at h4
  exact h4

private def filter_point : KDerivation
    (imp suffixFilter.encode (imp (member 31 2) (neg (member 40 2)))) := by
  have hi := filter_at 0 31 35 2 suffixPredicate (by decide) (by decide) (by decide)
    (by decide) (by decide)
  have hi' : KDerivation (imp suffixFilter.encode
      (both (imp (member 31 2) (both (member 0 2) (neg (member 40 2))))
        (imp (both (member 0 2) (neg (member 40 2))) (member 31 2)))) := by
    simpa [suffix_filter_code,suffixPredicate,Formula.not,Formula.encode,replace,rename,neg] using hi
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [member 31 2,suffixFilter.encode]
  have hm : Context Γ (member 31 2) := .head _ _
  have hf : Context Γ suffixFilter.encode := .hypothesis (by simp [Γ])
  have hb : Context Γ (both (imp (member 31 2) (both (member 0 2) (neg (member 40 2))))
      (imp (both (member 0 2) (neg (member 40 2))) (member 31 2))) := .mp hf (.closed hi')
  have hp : Context Γ (imp (member 31 2) (both (member 0 2) (neg (member 40 2)))) :=
    Context.conjunctionLeft hb
  have hm' : Context Γ (both (member 0 2) (neg (member 40 2))) := .mp hm hp
  exact Context.conjunctionRight hm'

private def path_body_outside : KDerivation (imp outsideGuard.encode
    (imp spanPathBody.encode target.encode)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [spanPathBody.encode,outsideGuard.encode]
  have hb : Context Γ spanPathBody.encode := .head _ _
  have hg : Context Γ outsideGuard.encode := .hypothesis (by simp [Γ])
  have hc : Context Γ storedClean.encode := Context.conjunctionLeft hg
  have hf : Context Γ suffixFilter.encode := Context.conjunctionRight hg
  have he : Context Γ (graphFormula 6 4 2).encode :=
    Context.conjunctionLeft (Context.conjunctionRight (Context.conjunctionRight hb))
  have hm : Context Γ (member 31 2) := .mp he (.mp hc (.closed clean_point))
  exact .mp hm (.mp hf (.closed filter_point))

/-- With the actual clean graph and relative-complement filter, the first
span path's source-side endpoint is outside cut 40. -/
def first_path_source_outside : KDerivation (imp outsideGuard.encode
    (imp spanPath.encode (neg (member 40 2)))) := by
  have h := guarded_exists_left 4 outsideGuard.encode spanPathBody.encode target.encode
    (free_vacuity 4 outsideGuard (by decide)) (free_vacuity 4 target (by decide)) path_body_outside
  simpa only [spanPath,target,Formula.not,Formula.encode,CompactProof.neg] using h

theorem first_path_source_outside_certificate : theoremCode (certificate first_path_source_outside) =
    imp outsideGuard.encode (imp spanPath.encode (neg (member 40 2))) :=
  certificate_correct first_path_source_outside

end PASoundness.PAtoCompactFirstSpanPathOutside

#print axioms PASoundness.PAtoCompactFirstSpanPathOutside.suffixPredicate
#print axioms PASoundness.PAtoCompactFirstSpanPathOutside.suffixFilter
#print axioms PASoundness.PAtoCompactFirstSpanPathOutside.outsideGuard
#print axioms PASoundness.PAtoCompactFirstSpanPathOutside.first_path_source_outside
#print axioms PASoundness.PAtoCompactFirstSpanPathOutside.first_path_source_outside_certificate
