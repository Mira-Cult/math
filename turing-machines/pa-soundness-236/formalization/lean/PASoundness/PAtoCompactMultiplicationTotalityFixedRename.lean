import PASoundness.PAtoCompactTermTranslation
import PASoundness.PAtoCompactScopedActiveReplace

/-! Capture-safe fixed-label transport for an explicitly supplied K proof of
candidate-guarded multiplication totality. This is a proof-data transformer:
it does not establish its input proof, arbitrary-label totality or the PA bridge. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactMultiplicationTotalityFixedRename
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactScopedActiveReplace
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

private def source : Formula := .imp (domainAt 300 200) (.imp (domainAt 300 30)
  (.ex 32 (andF (domainAt 300 32) (mulAt 300 200 30 32))))
private def intermediate : Formula := .imp (domainAt 300 200) (.imp (domainAt 300 31)
  (.ex 32 (andF (domainAt 300 32) (mulAt 300 200 31 32))))
private def target : Formula := .imp (domainAt 300 30) (.imp (domainAt 300 31)
  (.ex 32 (andF (domainAt 300 32) (mulAt 300 30 31 32))))

private theorem source30 : 30 ∉ source.binders := by decide
private theorem source31 : 31 ∉ source.binders := by decide
private theorem intermediate200 : 200 ∉ intermediate.binders := by decide
private theorem intermediate30 : 30 ∉ intermediate.binders := by decide
private theorem source_replace : replace 30 31 source = intermediate := by decide
private theorem intermediate_replace : replace 200 30 intermediate = target := by decide

/-- Two capture-safe free-name substitutions turn the supplied finite K
proof for first input 200 and second input 30 into one for inputs 30 and 31.
The output binder 32 is retained. -/
def fixed_renamed
    (hsource : KDerivation (imp (domainAt 300 200).encode (imp (domainAt 300 30).encode
      (existsCode 32 (andF (domainAt 300 32) (mulAt 300 200 30 32)).encode)))) :
    KDerivation (imp (domainAt 300 30).encode (imp (domainAt 300 31).encode
      (existsCode 32 (andF (domainAt 300 32) (mulAt 300 30 31 32)).encode))) := by
  have hs : KDerivation source.encode := by
    simpa [source, Formula.encode] using hsource
  have hmid := replace_derivation 30 31 source source30 source31 hs
  rw [source_replace] at hmid
  have htarget := replace_derivation 200 30 intermediate intermediate200 intermediate30 hmid
  rw [intermediate_replace] at htarget
  simpa [target, Formula.encode] using htarget

theorem fixed_renamed_certificate
    (hsource : KDerivation (imp (domainAt 300 200).encode (imp (domainAt 300 30).encode
      (existsCode 32 (andF (domainAt 300 32) (mulAt 300 200 30 32)).encode)))) :
    theoremCode (certificate (fixed_renamed hsource)) =
      imp (domainAt 300 30).encode (imp (domainAt 300 31).encode
        (existsCode 32 (andF (domainAt 300 32) (mulAt 300 30 31 32)).encode)) :=
  certificate_correct (fixed_renamed hsource)
end PASoundness.PAtoCompactMultiplicationTotalityFixedRename
#print axioms PASoundness.PAtoCompactMultiplicationTotalityFixedRename.fixed_renamed
#print axioms PASoundness.PAtoCompactMultiplicationTotalityFixedRename.fixed_renamed_certificate
