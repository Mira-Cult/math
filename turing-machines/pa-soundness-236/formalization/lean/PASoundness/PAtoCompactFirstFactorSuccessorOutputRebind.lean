import PASoundness.PAtoCompactFirstFactorSuccessorTestRebind

/-! Rename the bound common output in a supplied first-factor successor
frame. This is a finite K proof transformer, not an existence proof. -/
namespace PASoundness.PAtoCompactFirstFactorSuccessorOutputRebind

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactFirstFactorOutputAlpha PASoundness.PAtoCompactFirstFactorSuccessorTestRebind

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Change the output binder in a supplied frame while retaining its single
witness across candidate, literal-cut, addition and successor-product facts.
Both output names must avoid the three free inputs of the output body; the
inputs may alias. The two output names may also coincide. -/
def rebind_output (b x y p s old new w : Nat)
    (hold : old < b) (hnew : new < b+2)
    (holdp : old ≠ p) (holdy : old ≠ y) (holds : old ≠ s)
    (hnewp : new ≠ p) (hnewy : new ≠ y) (hnews : new ≠ s)
    (d : KDerivation (guardedFrame b x y p s old w)) :
    KDerivation (guardedFrame b x y p s new w) := by
  by_cases hsame : old = new
  · subst new
    exact d
  · have halpha := output_alpha b p y s old new hold hnew holdp holdy holds
      hsame hnewp hnewy hnews
    unfold guardedFrame at d ⊢
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    apply Context.deduction
    apply Context.deduction
    apply Context.deduction
    let Γ := [(mulAt b x y p).encode, successorCode x s w,
      (domainAt b p).encode, (domainAt b y).encode, (domainAt b x).encode]
    have hm : Context Γ (mulAt b x y p).encode := .head _ _
    have hw : Context Γ (successorCode x s w) := .hypothesis (by simp [Γ])
    have hp : Context Γ (domainAt b p).encode := .hypothesis (by simp [Γ])
    have hy : Context Γ (domainAt b y).encode := .hypothesis (by simp [Γ])
    have hx : Context Γ (domainAt b x).encode := .hypothesis (by simp [Γ])
    have he : Context Γ (existsCode old (body b p y s old).encode) :=
      .mp hm (.mp hw (.mp hp (.mp hy (.mp hx (.closed d)))))
    exact .mp he (.closed halpha)

theorem rebind_output_certificate (b x y p s old new w : Nat)
    (hold : old < b) (hnew : new < b+2)
    (holdp : old ≠ p) (holdy : old ≠ y) (holds : old ≠ s)
    (hnewp : new ≠ p) (hnewy : new ≠ y) (hnews : new ≠ s)
    (d : KDerivation (guardedFrame b x y p s old w)) :
    theoremCode (certificate (rebind_output b x y p s old new w hold hnew
      holdp holdy holds hnewp hnewy hnews d)) = guardedFrame b x y p s new w :=
  certificate_correct _

end PASoundness.PAtoCompactFirstFactorSuccessorOutputRebind

#print axioms PASoundness.PAtoCompactFirstFactorSuccessorOutputRebind.rebind_output
#print axioms PASoundness.PAtoCompactFirstFactorSuccessorOutputRebind.rebind_output_certificate
