import PASoundness.PAtoCompactFirstFactorOutputAlpha
import PASoundness.PAtoCompactRawSuccessorBinderBridge

/-! Change the raw successor test binder in a supplied, guarded
first-factor successor-output proof. This transforms proof data and preserves
its existential output; it constructs neither that proof nor an output. -/
namespace PASoundness.PAtoCompactFirstFactorSuccessorTestRebind

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactRawSuccessorBinderBridge
open PASoundness.PAtoCompactFirstFactorOutputAlpha

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Candidate inputs and old product together with raw successor yield one
output retaining candidate, cut, sum and successor product. `w` is the
raw successor's bound test name, while `out` binds the common output. -/
def guardedFrame (b x y p s out w : Nat) : Nat :=
  imp (domainAt b x).encode (imp (domainAt b y).encode
    (imp (domainAt b p).encode (imp (successorCode x s w)
      (imp (mulAt b x y p).encode (existsCode out (body b p y s out).encode)))))

/-- Replace the antecedent's test binder while leaving the four input
labels and the bound common output unchanged. Both test labels must be
fresh for the two successor operands. Other input labels may coincide with
each other, and this transformer does not need a distinct output label. -/
def rebind (b x y p s out old new : Nat)
    (holdx : old ≠ x) (holds : old ≠ s)
    (hnewx : new ≠ x) (hnews : new ≠ s)
    (d : KDerivation (guardedFrame b x y p s out old)) :
    KDerivation (guardedFrame b x y p s out new) := by
  have htest := raw_successor_rename x s new old hnewx hnews holdx holds
  unfold guardedFrame at d ⊢
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [(mulAt b x y p).encode, successorCode x s new,
    (domainAt b p).encode, (domainAt b y).encode, (domainAt b x).encode]
  have hm : Context Γ (mulAt b x y p).encode := .head _ _
  have hn : Context Γ (successorCode x s new) := .hypothesis (by simp [Γ])
  have hp : Context Γ (domainAt b p).encode := .hypothesis (by simp [Γ])
  have hy : Context Γ (domainAt b y).encode := .hypothesis (by simp [Γ])
  have hx : Context Γ (domainAt b x).encode := .hypothesis (by simp [Γ])
  have ho : Context Γ (successorCode x s old) := .mp hn (.closed htest)
  exact .mp hm (.mp ho (.mp hp (.mp hy (.mp hx (.closed d)))))

theorem rebind_certificate (b x y p s out old new : Nat)
    (holdx : old ≠ x) (holds : old ≠ s)
    (hnewx : new ≠ x) (hnews : new ≠ s)
    (d : KDerivation (guardedFrame b x y p s out old)) :
    theoremCode (certificate (rebind b x y p s out old new holdx holds hnewx hnews d)) =
      guardedFrame b x y p s out new := certificate_correct _

end PASoundness.PAtoCompactFirstFactorSuccessorTestRebind

#print axioms PASoundness.PAtoCompactFirstFactorSuccessorTestRebind.guardedFrame
#print axioms PASoundness.PAtoCompactFirstFactorSuccessorTestRebind.rebind
#print axioms PASoundness.PAtoCompactFirstFactorSuccessorTestRebind.rebind_certificate
