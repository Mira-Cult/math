import PASoundness.PAtoCompactFirstFactorRenameSyntax
import PASoundness.PAtoCompactFirstFactorSuccessorTestRebind

/-! Exact encoding bridge between named and numeric presentations of the
same first-factor successor frame. This syntactic identity establishes no K
proof of the frame. -/
namespace PASoundness.PAtoCompactFirstFactorFrameEncoding

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactAdjunction
open PASoundness.PAtoCompactFirstFactorRenameSyntax PASoundness.PAtoCompactFirstFactorSuccessorTestRebind

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The named frame is exactly the numeric guarded frame. All variable names,
including the local binders, are arbitrary. -/
theorem assigned_encode (b r w x y p s : Nat) :
    (assignedFrame b r w x y p s).encode = guardedFrame b x y p s r w := by
  simp [assignedFrame, guardedFrame, namedSuccessor, namedSuccessorBody,
    namedBoth, namedEither, Formula.encode, successorCode, CompactProof.both,
    CompactProof.neg, CompactDerivations.either]

/-- Reinterpret a supplied proof of the numeric frame in named form. -/
def to_named (b r w x y p s : Nat) (d : KDerivation (guardedFrame b x y p s r w)) :
    KDerivation (assignedFrame b r w x y p s).encode := by
  rw [assigned_encode]
  exact d

/-- Reinterpret a supplied proof of the named frame in numeric form. -/
def to_numeric (b r w x y p s : Nat) (d : KDerivation (assignedFrame b r w x y p s).encode) :
    KDerivation (guardedFrame b x y p s r w) := by
  rw [assigned_encode] at d
  exact d

end PASoundness.PAtoCompactFirstFactorFrameEncoding

#print axioms PASoundness.PAtoCompactFirstFactorFrameEncoding.assigned_encode
#print axioms PASoundness.PAtoCompactFirstFactorFrameEncoding.to_named
#print axioms PASoundness.PAtoCompactFirstFactorFrameEncoding.to_numeric
