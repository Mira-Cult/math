import PASoundness.PAtoCompactAnchoredForwardWitnessWithLex
import PASoundness.PAtoCompactMultiplicationCanonicalBaseStep
import PASoundness.PAtoCompactFreeVacuity

/-! Eliminate the actual nested multiplication graph witnesses, conditional on
an explicit pointwise K proof at the innermost same-witness context. The four
original witnesses are not reselected. This does not construct the pointwise
proof or assert multiplication totality. -/
namespace PASoundness.PAtoCompactMultiplicationRetainedRawElim
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactAnchoredForwardWitnessWithLex
open PASoundness.PAtoCompactAnchoredProductWitnessPackage PASoundness.PAtoCompactCleanSuffixRowPackage
open PASoundness.PAtoCompactScopedRowLexLift PASoundness.PAtoCompactForwardContextWithLex
open PASoundness.PAtoCompactAnchoredLexSharedProjection
open PASoundness.PAtoCompactMultiplicationCanonicalBaseStep PASoundness.PAtoCompactFreeVacuity
set_option maxRecDepth 262144
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

private def eliminate (x a b : Nat) (h : KDerivation (imp a b))
    (hv : KDerivation (imp b (allCode x b))) : KDerivation (imp (existsCode x a) b) := by
  apply Context.closeEmpty
  apply Context.deduction
  exact Context.existsElim hv (.closed (.generalize x h)) (Context.head [] _)

private def drop_left (a b c : Nat) (h : KDerivation (imp b c)) :
    KDerivation (imp (both a b) c) := by
  apply Context.closeEmpty
  apply Context.deduction
  exact .mp (Context.conjunctionRight (Context.head [] _)) (.closed h)

/-- If the common innermost context implies the actual new raw product, the
original retained suffix, old graph, map graph and row graph package implies
that same product. The supplied pointwise K derivation is the only proof-data
input; no separate witness choice or semantic soundness is used. -/
def retained_to_rawNew
    (point : KDerivation (imp contextWithLex.encode rawNew.encode)) :
    KDerivation (imp retainedLexResult rawNew.encode) := by
  let R := rawNew.encode
  have v64 : KDerivation (imp R (allCode 64 R)) := free_vacuity 64 rawNew (by decide)
  have v6 : KDerivation (imp R (allCode 6 R)) := free_vacuity 6 rawNew (by decide)
  have v10 : KDerivation (imp R (allCode 10 R)) := free_vacuity 10 rawNew (by decide)
  have v40 : KDerivation (imp R (allCode 40 R)) := free_vacuity 40 rawNew (by decide)
  have h64 := eliminate 64 contextWithLex.encode R point v64
  have h6 := eliminate 6 (both cleanMatrix.encode (existsCode 64 contextWithLex.encode)) R
    (drop_left cleanMatrix.encode (existsCode 64 contextWithLex.encode) R h64) v6
  have h10 := eliminate 10
    (both oldBody.encode (existsCode 6 (both cleanMatrix.encode (existsCode 64 contextWithLex.encode)))) R
    (drop_left oldBody.encode (existsCode 6 (both cleanMatrix.encode (existsCode 64 contextWithLex.encode))) R h6) v10
  have h40 := eliminate 40
    (both suffixData.encode (existsCode 10 (both oldBody.encode
      (existsCode 6 (both cleanMatrix.encode (existsCode 64 contextWithLex.encode)))))) R
    (drop_left suffixData.encode (existsCode 10 (both oldBody.encode
      (existsCode 6 (both cleanMatrix.encode (existsCode 64 contextWithLex.encode))))) R h10) v40
  simpa only [retainedLexResult,nested,R] using h40

theorem retained_to_rawNew_certificate
    (point : KDerivation (imp contextWithLex.encode rawNew.encode)) :
    theoremCode (certificate (retained_to_rawNew point)) =
      imp retainedLexResult rawNew.encode := certificate_correct _
end PASoundness.PAtoCompactMultiplicationRetainedRawElim
#print axioms PASoundness.PAtoCompactMultiplicationRetainedRawElim.retained_to_rawNew
#print axioms PASoundness.PAtoCompactMultiplicationRetainedRawElim.retained_to_rawNew_certificate
