import PASoundness.PAtoCompactOrderIsomorphism
import PASoundness.CompactDerivations

/-! Pointwise no-spurious-edge case split for an adjunction. The displayed
pair-coordinate alias theorem is an explicit K proof-data premise; it is not
assumed as an axiom. No inverse graph existence or induction is claimed.
Code 1 remains literal compact falsum. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPartialInversePointCase
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactOrderIsomorphism
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Fixed-name instance of pair-coordinate injectivity across a pair-object
alias. Name 19 is the tested pair witness, 11 the appended pair, and 3,2 and
13,12 are the new and designated coordinates. -/
def pairAliasCode : Nat := imp (equal 19 11)
  (imp (pairFormula 19 3 2).encode
    (imp (pairFormula 11 13 12).encode (both (equal 3 13) (equal 2 12))))

/-- If the tested element of h′ is either already in h or equals the appended
pair, then its displayed pair coordinates either already occur in h or equal
the appended coordinates. The supplied alias derivation is an explicit
metatheoretic proof-data argument. -/
def no_spurious_point
    (hAlias : KDerivation pairAliasCode) : KDerivation
    (imp (imp (member 9 19) (either (member 7 19) (equal 19 11)))
      (imp (member 9 19) (imp (pairFormula 19 3 2).encode
        (imp (pairFormula 11 13 12).encode
          (either (both (member 7 19) (pairFormula 19 3 2).encode)
            (both (equal 3 13) (equal 2 12))))))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let A := imp (member 9 19) (either (member 7 19) (equal 19 11))
  let P := (pairFormula 19 3 2).encode
  let Q := (pairFormula 11 13 12).encode
  let L := both (member 7 19) P
  let R := both (equal 3 13) (equal 2 12)
  let Γ := [Q,P,member 9 19,A]
  have ha : Context Γ A := .hypothesis (by simp [Γ])
  have hp : Context Γ P := .hypothesis (by simp [Γ])
  have hq : Context Γ Q := Context.head _ _
  have hm : Context Γ (member 9 19) := .hypothesis (by simp [Γ])
  have hc : Context Γ (either (member 7 19) (equal 19 11)) := .mp hm ha
  apply Context.disjunctionElim hc
  · have hold : Context (member 7 19 :: Γ) (member 7 19) := Context.head _ _
    have hp' : Context (member 7 19 :: Γ) P := Context.under hp _
    exact Context.disjunctionLeft (b := R) (Context.conjunctionIntro hold hp')
  · have he : Context (equal 19 11 :: Γ) (equal 19 11) := Context.head _ _
    have hp' : Context (equal 19 11 :: Γ) P := Context.under hp _
    have hq' : Context (equal 19 11 :: Γ) Q := Context.under hq _
    have hab : Context (equal 19 11 :: Γ) R :=
      .mp hq' (.mp hp' (.mp he (.closed hAlias)))
    exact Context.disjunctionRight (a := L) hab

theorem no_spurious_point_certificate (hAlias : KDerivation pairAliasCode) :
    theoremCode (certificate (no_spurious_point hAlias)) =
      imp (imp (member 9 19) (either (member 7 19) (equal 19 11)))
        (imp (member 9 19) (imp (pairFormula 19 3 2).encode
          (imp (pairFormula 11 13 12).encode
            (either (both (member 7 19) (pairFormula 19 3 2).encode)
              (both (equal 3 13) (equal 2 12)))))) :=
  certificate_correct (no_spurious_point hAlias)

end PASoundness.PAtoCompactPartialInversePointCase

#print axioms PASoundness.PAtoCompactPartialInversePointCase.no_spurious_point
#print axioms PASoundness.PAtoCompactPartialInversePointCase.no_spurious_point_certificate
