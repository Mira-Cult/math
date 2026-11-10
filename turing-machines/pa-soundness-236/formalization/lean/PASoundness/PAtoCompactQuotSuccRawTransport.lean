import PASoundness.PAtoCompactAdjunction

/-! Explicit K alpha/equality transport for the two fresh raw-successor
witness graphs. The endpoint aliases remain hypotheses; no quotient
successor witness or injectivity theorem is asserted here. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactQuotSuccRawTransport
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactAdjunction
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- With the first predecessor alias tied to name 2, rename the raw test
binder 8 to 9 and transport the predecessor through K equality. -/
def first_raw_transport : KDerivation
    (imp (equal 40 2) (imp (namedSuccessor 40 0 8).encode (successorCode 2 0 9))) := by
  let F := namedSuccessor 40 0 9
  have halpha : KDerivation (imp (namedSuccessor 40 0 8).encode F.encode) := by
    have h := (universalAlpha 8 9 (namedSuccessorBody 40 0 8)
      (by decide) (by decide) (by decide)).1
    simpa [F, namedSuccessor, namedSuccessorBody, namedBoth, namedEither,
      Formula.encode, replace, rename, CompactProof.both, CompactProof.neg,
      CompactDerivations.either] using h
  have hrepl := (equalityReplace 40 2 F (by decide) (by decide)).1
  have hshape : replace 40 2 F = namedSuccessor 2 0 9 := by decide
  rw [hshape] at hrepl
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [(namedSuccessor 40 0 8).encode, equal 40 2]
  have hf : Context Γ (namedSuccessor 40 0 8).encode := Context.head _ _
  have he : Context Γ (equal 40 2) := .hypothesis (by simp [Γ])
  have hfinal : Context Γ (namedSuccessor 2 0 9).encode :=
    .mp (.mp hf (.closed halpha)) (.mp he (.closed hrepl))
  simpa [Γ, namedSuccessor, namedSuccessorBody, namedBoth, namedEither,
    successorCode, Formula.encode, CompactProof.both, CompactProof.neg,
    CompactDerivations.either] using hfinal

/-- The second predecessor graph is converted independently, with output
witness name 1 and fresh raw test binder 10. -/
def second_raw_transport : KDerivation
    (imp (equal 42 5) (imp (namedSuccessor 42 1 8).encode (successorCode 5 1 10))) := by
  let F := namedSuccessor 42 1 10
  have halpha : KDerivation (imp (namedSuccessor 42 1 8).encode F.encode) := by
    have h := (universalAlpha 8 10 (namedSuccessorBody 42 1 8)
      (by decide) (by decide) (by decide)).1
    simpa [F, namedSuccessor, namedSuccessorBody, namedBoth, namedEither,
      Formula.encode, replace, rename, CompactProof.both, CompactProof.neg,
      CompactDerivations.either] using h
  have hrepl := (equalityReplace 42 5 F (by decide) (by decide)).1
  have hshape : replace 42 5 F = namedSuccessor 5 1 10 := by decide
  rw [hshape] at hrepl
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [(namedSuccessor 42 1 8).encode, equal 42 5]
  have hf : Context Γ (namedSuccessor 42 1 8).encode := Context.head _ _
  have he : Context Γ (equal 42 5) := .hypothesis (by simp [Γ])
  have hfinal : Context Γ (namedSuccessor 5 1 10).encode :=
    .mp (.mp hf (.closed halpha)) (.mp he (.closed hrepl))
  simpa [Γ, namedSuccessor, namedSuccessorBody, namedBoth, namedEither,
    successorCode, Formula.encode, CompactProof.both, CompactProof.neg,
    CompactDerivations.either] using hfinal

theorem first_raw_transport_certificate : theoremCode (certificate first_raw_transport) =
    imp (equal 40 2) (imp (namedSuccessor 40 0 8).encode (successorCode 2 0 9)) :=
  certificate_correct first_raw_transport

theorem second_raw_transport_certificate : theoremCode (certificate second_raw_transport) =
    imp (equal 42 5) (imp (namedSuccessor 42 1 8).encode (successorCode 5 1 10)) :=
  certificate_correct second_raw_transport

end PASoundness.PAtoCompactQuotSuccRawTransport

#print axioms PASoundness.PAtoCompactQuotSuccRawTransport.first_raw_transport
#print axioms PASoundness.PAtoCompactQuotSuccRawTransport.second_raw_transport
