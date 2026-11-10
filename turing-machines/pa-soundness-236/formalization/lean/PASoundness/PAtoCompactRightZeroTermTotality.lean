import PASoundness.PAtoCompactRightZeroTermGrammar
import PASoundness.PAtoCompactAddUnaryTotalityClosed

/-! Guarded graph existence for unary terms followed by any finite number
of additions of zero on the right. This is an inclusion into the already
proved addition-unary totality theorem; it does not assert substitution
compatibility or uniform graph existence under a guard lacking coverage. -/
namespace PASoundness.PAtoCompactRightZeroTermTotality

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactGuardedBridge
open PASoundness.PAtoCompactUnaryTermTransport PASoundness.PAtoCompactUnaryGuardedCanonical
open PASoundness.PAtoCompactAddUnaryTotalityInduction
open PASoundness.PAtoCompactRightZeroTermGrammar

/-- Unary terms belong to the proved addition-unary totality fragment. -/
noncomputable def unary_to_addUnary {α : Type} {t : Peano.language.Term α} (h : UnaryTerm t) :
    AddUnaryTerm t := by
  induction h with
  | var a => exact .var a
  | zero => exact .zero
  | succ h ih => exact .succ ih

/-- Every repeated-right-zero term belongs to the addition-unary fragment. -/
noncomputable def to_addUnary {α : Type} {t : Peano.language.Term α} (h : RightZeroTerm t) :
    AddUnaryTerm t := by
  induction h with
  | unary h => exact unary_to_addUnary h
  | addZero h ih => exact .add ih .zero

/-- The actual graph has an output under a formula guard covering its mapped
variables. All source names are below the output, with a spare allocator name. -/
noncomputable def guarded_total {α : Type} [DecidableEq α] (v : α → Nat)
    (φ : Peano.Formula) {t : Peano.language.Term α} (h : RightZeroTerm t)
    (b out : Nat) (hb : out + 1 < b)
    (hnames : ∀ z ∈ φ.freeVarFinset, z < out)
    (hcover : ∀ a ∈ t.varFinset, v a ∈ φ.freeVarFinset) :
    KDerivation (imp (guardFormula φ).encode (existsCode out (termGraph v t out b).encode)) :=
  PASoundness.PAtoCompactAddUnaryGuardedTotality.guarded_total v φ (to_addUnary h)
    PASoundness.PAtoCompactAddUnaryTotalityClosed.additionExistence b out hb hnames hcover

/-- Canonical names are chosen above all guard and source variable names. -/
noncomputable def canonical_total {α : Type} [DecidableEq α] (v : α → Nat)
    (φ : Peano.Formula) {t : Peano.language.Term α} (h : RightZeroTerm t)
    (hcover : ∀ a ∈ t.varFinset, v a ∈ φ.freeVarFinset) :
    KDerivation (imp (guardFormula φ).encode
      (existsCode (outputName φ) (termGraph v t (outputName φ) (allocatorBase φ)).encode)) :=
  PASoundness.PAtoCompactAddUnaryTotalityClosed.canonical_total v φ (to_addUnary h) hcover

theorem canonical_total_certificate {α : Type} [DecidableEq α] (v : α → Nat)
    (φ : Peano.Formula) {t : Peano.language.Term α} (h : RightZeroTerm t)
    (hcover : ∀ a ∈ t.varFinset, v a ∈ φ.freeVarFinset) :
    theoremCode (certificate (canonical_total v φ h hcover)) =
      imp (guardFormula φ).encode
        (existsCode (outputName φ) (termGraph v t (outputName φ) (allocatorBase φ)).encode) :=
  certificate_correct _

end PASoundness.PAtoCompactRightZeroTermTotality

#print axioms PASoundness.PAtoCompactRightZeroTermTotality.unary_to_addUnary
#print axioms PASoundness.PAtoCompactRightZeroTermTotality.to_addUnary
#print axioms PASoundness.PAtoCompactRightZeroTermTotality.guarded_total
#print axioms PASoundness.PAtoCompactRightZeroTermTotality.canonical_total
#print axioms PASoundness.PAtoCompactRightZeroTermTotality.canonical_total_certificate
