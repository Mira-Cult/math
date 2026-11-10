import PASoundness.PAtoCompactAdditionCandidateTotalityClosed
import PASoundness.PAtoCompactScopedActiveReplace

/-! Capture-safe relabeling of the fixed candidate-guarded addition totality
proof. This creates no new semantic assumption and does not itself prove the
arbitrary-label or arbitrary-base interface. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactAdditionTotalityFixedRename
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactOrdinalAddition
open PASoundness.PAtoCompactScopedActiveReplace
open PASoundness.PAtoCompactAdditionCandidateTotalityClosed
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

private def source : Formula := .imp (domainAt 100 200) (.imp (domainAt 100 30)
  (.ex 32 (andF (domainAt 100 32) (replace 31 200 additionFormula))))
private def target : Formula := .imp (domainAt 100 31) (.imp (domainAt 100 30)
  (.ex 32 (andF (domainAt 100 32) additionFormula)))

private theorem source200 : 200 ∉ source.binders := by decide
private theorem source31 : 31 ∉ source.binders := by decide
private theorem source_replace : replace 200 31 source = target := by decide

/-- A finite K proof of candidate-guarded addition output for the fixed
input labels 30 and 31. The output witness is at label 32. -/
def fixed_renamed : KDerivation
    (imp (domainAt 100 30).encode (imp (domainAt 100 31).encode
      (existsCode 32 (andF (domainAt 100 32) additionFormula).encode))) := by
  have hsource : KDerivation source.encode := by
    simpa [source, Formula.encode, andF, Formula.not, both, neg] using candidate_addition_total
  have hm := replace_derivation 200 31 source source200 source31 hsource
  rw [source_replace] at hm
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [(domainAt 100 31).encode, (domainAt 100 30).encode]
  have h31 : Context Γ (domainAt 100 31).encode := .head _ _
  have h30 : Context Γ (domainAt 100 30).encode := .hypothesis (by simp [Γ])
  exact .mp h30 (.mp h31 (.closed hm))

theorem fixed_renamed_certificate : theoremCode (certificate fixed_renamed) =
    imp (domainAt 100 30).encode (imp (domainAt 100 31).encode
      (existsCode 32 (andF (domainAt 100 32) additionFormula).encode)) :=
  certificate_correct fixed_renamed
end PASoundness.PAtoCompactAdditionTotalityFixedRename
#print axioms PASoundness.PAtoCompactAdditionTotalityFixedRename.fixed_renamed
#print axioms PASoundness.PAtoCompactAdditionTotalityFixedRename.fixed_renamed_certificate
