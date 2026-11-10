import PASoundness.PAtoCompactSuccessorQuotientIntro
import PASoundness.PAtoCompactGuardBaseTransport

/-! Capture-safe K transports from the raw successor relation and candidate
input guard to the binder names used in dynamic successor congruence. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactRawSuccBridge
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactAdjunction
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactGuardBaseTransport
open PASoundness.PAtoCompactTransitiveDomain

/-- Rename the bound test name of a raw successor graph. Operand names may
coincide; both test names must be fresh for them. -/
def raw_successor_alpha (x y q r : Nat) (hqr : q ≠ r)
    (hxq : x ≠ q) (hyq : y ≠ q) (hxr : x ≠ r) (hyr : y ≠ r) :
    KDerivation (imp (namedSuccessor x y q).encode (namedSuccessor x y r).encode) := by
  have h := universalAlpha q r (namedSuccessorBody x y q) hqr (by simp [namedSuccessorBody, namedBoth, namedEither, Formula.binders])
    (by simp [namedSuccessorBody, namedBoth, namedEither, Formula.names, Ne.symm hqr, Ne.symm hxr, Ne.symm hyr])
  simpa [namedSuccessor, namedSuccessorBody, namedBoth, namedEither, replace, rename, Formula.encode,
    hxq, hyq, Ne.symm hxq, Ne.symm hyq] using h.1

/-- Candidate domain yields its first transitivity conjunct, with its actual
private binder names. -/
def candidate_transitive (b x : Nat) :
    KDerivation (imp (domainAt b x).encode
      (namedTransitive x (b+33) (b+34)).encode) := by
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [(domainAt b x).encode]
  have h : Context Γ (domainAt b x).encode := Context.head [] _
  have h1 := Context.conjunctionLeft h
  exact Context.conjunctionLeft h1

/-- Transport the candidate and extract transitivity at the binder names
used by the raw congruence frame. -/
def candidate_transitive_frame (b d x : Nat)
    (hd : 29 ≤ d) (hb : x < b+32) (hx : x < d+2) :
    KDerivation (imp (domainAt b x).encode
      (namedTransitive x (d+4) (d+5)).encode) := by
  let c := d - 29
  have hc : x < c+32 := by dsimp [c]; omega
  have h := compose (domainAt_transport b c x hb hc) (candidate_transitive c x)
  have h1 : c+33 = d+4 := by dsimp [c]; omega
  have h2 : c+34 = d+5 := by dsimp [c]; omega
  simpa only [h1,h2] using h

end PASoundness.PAtoCompactRawSuccBridge
#print axioms PASoundness.PAtoCompactRawSuccBridge.raw_successor_alpha

#print axioms PASoundness.PAtoCompactRawSuccBridge.candidate_transitive

#print axioms PASoundness.PAtoCompactRawSuccBridge.candidate_transitive_frame
