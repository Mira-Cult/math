import PASoundness.PAtoCompactSuccRightZeroGrammar
import PASoundness.PAtoCompactAddUnaryTotalityClosed

/-! Guarded graph existence for terms built from unary terms using successor
and right-zero addition. This is a fragment of the established addition-unary
totality result; no multiplication or substitution compatibility is inferred. -/
namespace PASoundness.PAtoCompactSuccRightZeroTotality

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactGuardedBridge
open PASoundness.PAtoCompactUnaryTermTransport PASoundness.PAtoCompactUnaryGuardedCanonical
open PASoundness.PAtoCompactAddUnaryTotalityInduction
open PASoundness.PAtoCompactSuccRightZeroGrammar

/-- The unary subfragment is included in the addition-unary fragment. -/
noncomputable def unary_to_addUnary {α : Type} {t : Peano.language.Term α} (h : UnaryTerm t) :
    AddUnaryTerm t := by
  induction h with
  | var a => exact .var a
  | zero => exact .zero
  | succ h ih => exact .succ ih

/-- The exact grammar is included in the established totality fragment. -/
noncomputable def to_addUnary {α : Type} {t : Peano.language.Term α} (h : SuccRightZeroTerm t) :
    AddUnaryTerm t := by
  induction h with
  | unary h => exact unary_to_addUnary h
  | succ h ih => exact .succ ih
  | addZero h ih => exact .add ih .zero

/-- The formula guard must cover the mapped variables. The output and
allocation names obey the explicit freshness bounds. -/
noncomputable def guarded_total {α : Type} [DecidableEq α] (v : α → Nat)
    (φ : Peano.Formula) {t : Peano.language.Term α} (h : SuccRightZeroTerm t)
    (b out : Nat) (hb : out + 1 < b)
    (hnames : ∀ z ∈ φ.freeVarFinset, z < out)
    (hcover : ∀ a ∈ t.varFinset, v a ∈ φ.freeVarFinset) :
    KDerivation (imp (guardFormula φ).encode (existsCode out (termGraph v t out b).encode)) :=
  PASoundness.PAtoCompactAddUnaryGuardedTotality.guarded_total v φ (to_addUnary h)
    PASoundness.PAtoCompactAddUnaryTotalityClosed.additionExistence b out hb hnames hcover

/-- Canonical output and allocator names lie above the guarded source names. -/
noncomputable def canonical_total {α : Type} [DecidableEq α] (v : α → Nat)
    (φ : Peano.Formula) {t : Peano.language.Term α} (h : SuccRightZeroTerm t)
    (hcover : ∀ a ∈ t.varFinset, v a ∈ φ.freeVarFinset) :
    KDerivation (imp (guardFormula φ).encode
      (existsCode (outputName φ) (termGraph v t (outputName φ) (allocatorBase φ)).encode)) :=
  PASoundness.PAtoCompactAddUnaryTotalityClosed.canonical_total v φ (to_addUnary h) hcover

theorem canonical_total_certificate {α : Type} [DecidableEq α] (v : α → Nat)
    (φ : Peano.Formula) {t : Peano.language.Term α} (h : SuccRightZeroTerm t)
    (hcover : ∀ a ∈ t.varFinset, v a ∈ φ.freeVarFinset) :
    theoremCode (certificate (canonical_total v φ h hcover)) =
      imp (guardFormula φ).encode
        (existsCode (outputName φ) (termGraph v t (outputName φ) (allocatorBase φ)).encode) :=
  certificate_correct _

end PASoundness.PAtoCompactSuccRightZeroTotality

#print axioms PASoundness.PAtoCompactSuccRightZeroTotality.unary_to_addUnary
#print axioms PASoundness.PAtoCompactSuccRightZeroTotality.to_addUnary
#print axioms PASoundness.PAtoCompactSuccRightZeroTotality.guarded_total
#print axioms PASoundness.PAtoCompactSuccRightZeroTotality.canonical_total
#print axioms PASoundness.PAtoCompactSuccRightZeroTotality.canonical_total_certificate
