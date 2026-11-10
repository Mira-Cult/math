import PASoundness.PAtoCompactUnorderedPair

/-! Capture-safe alpha conversion of the test and witness binders in literal
unordered-pair graphs. These finite K derivations do not assert pair existence,
uniqueness, or a quotient interpretation. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPairAlpha
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactUnorderedPair
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Rename the universally quantified test label in a pair graph. The input
and output test labels must be distinct from each other and from all graph
parameters. Endpoint names a and b may coincide. -/
def pair_test_alpha (a b s q r : Nat)
    (hqa : q ≠ a) (hqb : q ≠ b) (hqs : q ≠ s)
    (hrq : r ≠ q) (hra : r ≠ a) (hrb : r ≠ b) (hrs : r ≠ s) :
    KDerivation (imp (pairCode a b s q) (pairCode a b s r)) := by
  let f : CompactNamed.Formula := namedBoth
    (.imp (.member s q) (namedEither (.equal q a) (.equal q b)))
    (.imp (namedEither (.equal q a) (.equal q b)) (.member s q))
  have h := (CompactNamed.universalAlpha q r f (Ne.symm hrq)
    (by simp [f, namedBoth, namedEither, CompactNamed.Formula.binders])
    (by simp [f, namedBoth, namedEither, CompactNamed.Formula.names,
      hrq, hra, hrb, hrs])).1
  simpa [f, pairCode, namedBoth, namedEither, CompactNamed.Formula.encode,
    CompactNamed.replace, CompactNamed.rename, CompactProof.both, CompactProof.neg,
    CompactDerivations.either, hqa, hqb, hqs, hrq, hra, hrb, hrs,
    Ne.symm hqa, Ne.symm hqb, Ne.symm hqs, Ne.symm hrq,
    Ne.symm hra, Ne.symm hrb, Ne.symm hrs] using h

/-- Rename the existentially bound pair witness while retaining its test
label; the endpoint names may coincide. -/
def pair_witness_alpha (a b s d q : Nat)
    (hsa : s ≠ a) (hsb : s ≠ b) (hsq : s ≠ q) (hds : d ≠ s) (hda : d ≠ a)
    (hdb : d ≠ b) (hdq : d ≠ q) :
    KDerivation (imp (existsCode s (pairCode a b s q))
      (existsCode d (pairCode a b d q))) := by
  let f := namedPair a b s q
  have h := (CompactNamed.existentialAlpha s d f (Ne.symm hds)
    (by simp [f, namedPair, namedBoth, namedEither, CompactNamed.Formula.binders, hsq])
    (by simp [f, namedPair, namedBoth, namedEither, CompactNamed.Formula.names,
      hds, hda, hdb, hdq])).1
  simpa [f, pairCode, namedPair, namedBoth, namedEither, CompactNamed.Formula.encode,
    CompactNamed.replace, CompactNamed.rename, CompactProof.both, CompactProof.neg,
    CompactDerivations.either, hsa, hsb, hsq, hds, hda, hdb, hdq,
    Ne.symm hsa, Ne.symm hsb, Ne.symm hsq, Ne.symm hds,
    Ne.symm hda, Ne.symm hdb, Ne.symm hdq] using h

/-- Rename a pair test binder inside an existing existential witness binder. -/
def pair_exists_test_alpha (a b s q r : Nat)
    (hqa : q ≠ a) (hqb : q ≠ b) (hqs : q ≠ s)
    (hrq : r ≠ q) (hra : r ≠ a) (hrb : r ≠ b) (hrs : r ≠ s) :
    KDerivation (imp (existsCode s (pairCode a b s q))
      (existsCode s (pairCode a b s r))) :=
  existsCongr s (pair_test_alpha a b s q r hqa hqb hqs hrq hra hrb hrs)

theorem pair_test_alpha_certificate (a b s q r : Nat)
    (hqa : q ≠ a) (hqb : q ≠ b) (hqs : q ≠ s)
    (hrq : r ≠ q) (hra : r ≠ a) (hrb : r ≠ b) (hrs : r ≠ s) :
    theoremCode (certificate (pair_test_alpha a b s q r hqa hqb hqs hrq hra hrb hrs)) =
      imp (pairCode a b s q) (pairCode a b s r) :=
  certificate_correct (pair_test_alpha a b s q r hqa hqb hqs hrq hra hrb hrs)

theorem pair_witness_alpha_certificate (a b s d q : Nat)
    (hsa : s ≠ a) (hsb : s ≠ b) (hsq : s ≠ q) (hds : d ≠ s)
    (hda : d ≠ a) (hdb : d ≠ b) (hdq : d ≠ q) :
    theoremCode (certificate (pair_witness_alpha a b s d q hsa hsb hsq hds hda hdb hdq)) =
      imp (existsCode s (pairCode a b s q)) (existsCode d (pairCode a b d q)) :=
  certificate_correct (pair_witness_alpha a b s d q hsa hsb hsq hds hda hdb hdq)

end PASoundness.PAtoCompactPairAlpha

#print axioms PASoundness.PAtoCompactPairAlpha.pair_test_alpha
#print axioms PASoundness.PAtoCompactPairAlpha.pair_witness_alpha
#print axioms PASoundness.PAtoCompactPairAlpha.pair_exists_test_alpha
