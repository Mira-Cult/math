import PASoundness.PAtoCompactUnorderedPair

/-! Capture-safe vacuity and witness introduction for an explicit unordered
pair graph. These are finite K proof transformations and do not assert that
any pair graph exists, that representatives are unique, or that a quotient
has been constructed. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPairQuantifiers
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactAdjunction
open PASoundness.PAtoCompactUnorderedPair
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- A fresh name can be quantified over a pair graph without changing its
free or bound names. -/
def pair_vacuity (a b s q r : Nat)
    (hra : r ≠ a) (hrb : r ≠ b) (hrs : r ≠ s) (hrq : r ≠ q) :
    KDerivation (imp (pairCode a b s q) (allCode r (pairCode a b s q))) := by
  let f := namedPair a b s q
  have hn : r ∉ f.names := by
    simp [f, namedPair, namedBoth, namedEither, CompactNamed.Formula.names,
      hra, hrb, hrs, hrq]
  have h := f.vacuity r hn
  simpa [f, namedPair, namedBoth, namedEither, pairCode, CompactNamed.Formula.encode,
    CompactProof.both, CompactProof.neg, CompactDerivations.either] using h

/-- A fixed graph witness can be introduced at a fresh existential binder.
The two element names a and b may coincide. -/
def pair_existential_intro_of_fresh (a b c d q : Nat)
    (hdc : d ≠ c) (hda : d ≠ a) (hdb : d ≠ b) (hdq : d ≠ q) (hcq : c ≠ q) :
    KDerivation (imp (pairCode a b c q) (existsCode d (pairCode a b d q))) := by
  let f := namedPair a b d q
  have h := exists_variable_intro d c f hdc
    (by simp [f, namedPair, namedBoth, namedEither, CompactNamed.Formula.binders, hdq])
    (by simp [f, namedPair, namedBoth, namedEither, CompactNamed.Formula.binders, hcq])
  simpa [f, namedPair, namedBoth, namedEither, pairCode,
    CompactNamed.Formula.encode, CompactNamed.replace, CompactNamed.rename,
    CompactProof.both, CompactProof.neg, CompactDerivations.either,
    hdc, hda, hdb, hdq, hcq, Ne.symm hdc, Ne.symm hda, Ne.symm hdb,
    Ne.symm hdq, Ne.symm hcq] using h

/-- Pairwise-distinct-name specialization of witness introduction. -/
def pair_existential_intro (a b c d q : Nat)
    (fresh : [a,b,c,d,q].Nodup) :
    KDerivation (imp (pairCode a b c q) (existsCode d (pairCode a b d q))) := by
  have hdc : d ≠ c := by intro h; subst d; simp at fresh
  have hda : d ≠ a := by intro h; subst d; simp at fresh
  have hdb : d ≠ b := by intro h; subst d; simp at fresh
  have hdq : d ≠ q := by intro h; subst d; simp at fresh
  have hcq : c ≠ q := by intro h; subst c; simp at fresh
  exact pair_existential_intro_of_fresh a b c d q hdc hda hdb hdq hcq

theorem pair_vacuity_certificate (a b s q r : Nat)
    (hra : r ≠ a) (hrb : r ≠ b) (hrs : r ≠ s) (hrq : r ≠ q) :
    theoremCode (certificate (pair_vacuity a b s q r hra hrb hrs hrq)) =
      imp (pairCode a b s q) (allCode r (pairCode a b s q)) :=
  certificate_correct (pair_vacuity a b s q r hra hrb hrs hrq)

theorem pair_existential_intro_certificate (a b c d q : Nat)
    (fresh : [a,b,c,d,q].Nodup) :
    theoremCode (certificate (pair_existential_intro a b c d q fresh)) =
      imp (pairCode a b c q) (existsCode d (pairCode a b d q)) :=
  certificate_correct (pair_existential_intro a b c d q fresh)

end PASoundness.PAtoCompactPairQuantifiers

#print axioms PASoundness.PAtoCompactPairQuantifiers.pair_vacuity
#print axioms PASoundness.PAtoCompactPairQuantifiers.pair_existential_intro_of_fresh
#print axioms PASoundness.PAtoCompactPairQuantifiers.pair_existential_intro
#print axioms PASoundness.PAtoCompactPairQuantifiers.pair_existential_intro_certificate
