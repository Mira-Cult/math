import PASoundness.PAtoCompactUnorderedPair

/-! Finite K proofs of elementary coordinate comparison for unordered-pair
graphs. A shared pair object fixes the other coordinate when the first one is
fixed; no uniqueness of pair representatives or quotient is asserted. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactUnorderedCoordinates
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactUnorderedPair

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def namedPairBody (a b s q : Nat) : CompactNamed.Formula :=
  namedBoth (.imp (.member s q) (namedEither (.equal q a) (.equal q b)))
    (.imp (namedEither (.equal q a) (.equal q b)) (.member s q))

/-- Instantiate an unordered-pair graph at a capture-safe name. -/
def pair_instance (a b s q v : Nat)
    (hqa : q ≠ a) (hqb : q ≠ b) (hqs : q ≠ s) (hqv : q ≠ v) :
    KDerivation (imp (pairCode a b s q)
      (both (imp (member s v) (either (equal v a) (equal v b)))
        (imp (either (equal v a) (equal v b)) (member s v)))) := by
  have h := CompactNamed.universalInstance q v (namedPairBody a b s q) hqv
    (by simp [namedPairBody, namedBoth, namedEither, CompactNamed.Formula.binders])
    (by simp [namedPairBody, namedBoth, namedEither, CompactNamed.Formula.binders])
  simpa [namedPairBody, namedBoth, namedEither, pairCode,
    CompactNamed.Formula.encode, CompactNamed.replace, CompactNamed.rename,
    CompactProof.both, CompactProof.neg, CompactDerivations.either,
    hqa, hqb, hqs, hqv, Ne.symm hqa, Ne.symm hqb, Ne.symm hqs, Ne.symm hqv] using h

/-- If the same represented set is {a,b} and {a,c}, then b=c.
The graph binders may differ and neither graph needs extensionality. -/
def pair_second_coordinate (a b c s q r : Nat)
    (hqa : q ≠ a) (hqb : q ≠ b) (hqc : q ≠ c) (hqs : q ≠ s)
    (hra : r ≠ a) (hrb : r ≠ b) (hrc : r ≠ c) (hrs : r ≠ s) :
    KDerivation (imp (pairCode a b s q) (imp (pairCode a c s r) (equal b c))) := by
  let A := pairCode a b s q
  let B := pairCode a c s r
  let Γ := [B,A]
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  have ha : Context Γ A := .hypothesis (by simp [Γ])
  have hb : Context Γ B := .hypothesis (by simp [Γ])
  have hAb := Context.mp ha (.closed (pair_instance a b s q b hqa hqb hqs hqb))
  have hAc := Context.mp ha (.closed (pair_instance a b s q c hqa hqb hqs hqc))
  have hBb := Context.mp hb (.closed (pair_instance a c s r b hra hrc hrs hrb))
  have hBc := Context.mp hb (.closed (pair_instance a c s r c hra hrc hrs hrc))
  have hbpair : Context Γ (either (equal b a) (equal b b)) :=
    Context.disjunctionRight (a := equal b a) (.closed (equalityReflexive b))
  have hcpair : Context Γ (either (equal c a) (equal c c)) :=
    Context.disjunctionRight (a := equal c a) (.closed (equalityReflexive c))
  have hbm : Context Γ (member s b) := .mp hbpair (Context.conjunctionRight hAb)
  have hcm : Context Γ (member s c) := .mp hcpair (Context.conjunctionRight hBc)
  have hbcase : Context Γ (either (equal b a) (equal b c)) :=
    .mp hbm (Context.conjunctionLeft hBb)
  have hccase : Context Γ (either (equal c a) (equal c b)) :=
    .mp hcm (Context.conjunctionLeft hAc)
  apply Context.disjunctionElim hbcase
  · have hba : Context (equal b a :: Γ) (equal b a) := Context.head Γ _
    have hccase' := Context.under hccase (equal b a)
    apply Context.disjunctionElim hccase'
    · have hca : Context (equal c a :: equal b a :: Γ) (equal c a) := Context.head _ _
      exact Context.eqTrans (Context.under hba _) (Context.eqSymm hca)
    · exact Context.eqSymm (Context.head _ (equal c b))
  · exact Context.head Γ (equal b c)

theorem pair_second_coordinate_certificate (a b c s q r : Nat)
    (hqa : q ≠ a) (hqb : q ≠ b) (hqc : q ≠ c) (hqs : q ≠ s)
    (hra : r ≠ a) (hrb : r ≠ b) (hrc : r ≠ c) (hrs : r ≠ s) :
    theoremCode (certificate (pair_second_coordinate a b c s q r
      hqa hqb hqc hqs hra hrb hrc hrs)) =
      imp (pairCode a b s q) (imp (pairCode a c s r) (equal b c)) :=
  certificate_correct (pair_second_coordinate a b c s q r hqa hqb hqc hqs hra hrb hrc hrs)

end PASoundness.PAtoCompactUnorderedCoordinates

#print axioms PASoundness.PAtoCompactUnorderedCoordinates.pair_second_coordinate
#print axioms PASoundness.PAtoCompactUnorderedCoordinates.pair_second_coordinate_certificate
