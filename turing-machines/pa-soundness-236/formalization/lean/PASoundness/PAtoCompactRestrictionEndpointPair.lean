import PASoundness.PAtoCompactKuratowskiInjectivity

/-! Transport endpoints from a shared literal K pair witness.
No graph existence or quotient property is assumed or established. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactRestrictionEndpointPair
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactKuratowskiInjectivity
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- If the same pair witness 19 represents both `(25,26)` and `(u,v)`,
the displayed endpoint memberships transfer by K equality. The `Nodup`
condition concerns variable labels; their interpreted objects may coincide.
Names x and y need not be distinct from any of these labels, although a
caller eliminating 25 or 26 must impose its own capture-safe freshness. -/
def endpoints_of_shared_pair (x y u v : Nat)
    (fresh : [19,25,26,u,v,20,21,22,23,24].Nodup) :
    KDerivation (imp (member x 25)
      (imp (member y 26)
        (imp (pairFormula 19 25 26).encode
          (imp (pairFormula 19 u v).encode (both (member x u) (member y v)))))) := by
  let A := member x 25
  let B := member y 26
  let C := (pairFormula 19 25 26).encode
  let D := (pairFormula 19 u v).encode
  let Γ := [D,C,B,A]
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  have ha : Context Γ A := .hypothesis (by simp [Γ])
  have hb : Context Γ B := .hypothesis (by simp [Γ])
  have hc : Context Γ C := .hypothesis (by simp [Γ])
  have hd : Context Γ D := .head _ _
  have he : Context Γ (both (equal 25 u) (equal 26 v)) :=
    .mp hd (.mp hc (.closed (pair_coordinates 19 25 26 u v fresh)))
  have hxu : Context Γ (member x u) :=
    .mp (Context.conjunctionLeft he) (.mp ha (.closed (memberRightEquality x 25 u)))
  have hyv : Context Γ (member y v) :=
    .mp (Context.conjunctionRight he) (.mp hb (.closed (memberRightEquality y 26 v)))
  exact Context.conjunctionIntro hxu hyv

theorem endpoints_of_shared_pair_certificate (x y u v : Nat)
    (fresh : [19,25,26,u,v,20,21,22,23,24].Nodup) :
    theoremCode (certificate (endpoints_of_shared_pair x y u v fresh)) =
      imp (member x 25)
        (imp (member y 26)
          (imp (pairFormula 19 25 26).encode
            (imp (pairFormula 19 u v).encode (both (member x u) (member y v))))) :=
  certificate_correct (endpoints_of_shared_pair x y u v fresh)

end PASoundness.PAtoCompactRestrictionEndpointPair

#print axioms PASoundness.PAtoCompactRestrictionEndpointPair.endpoints_of_shared_pair
