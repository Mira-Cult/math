import PASoundness.PAtoCompactUnorderedCoordinates

/-! K coordinate comparison when one object is both a singleton and an
unordered pair. No extensionality, equality of representatives, or quotient
interpretation is asserted. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactSingletonPairCoordinates
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactSingleton PASoundness.PAtoCompactUnorderedPair
open PASoundness.PAtoCompactUnorderedCoordinates

/-- A shared object representing both {a} and {b,c} forces b=a and c=a.
All graph-test freshness constraints are explicit. -/
def singleton_pair_coordinates (a b c s q r : Nat)
    (hqa : q ≠ a) (hqb : q ≠ b) (hqc : q ≠ c) (hqs : q ≠ s)
    (hrb : r ≠ b) (hrc : r ≠ c) (hrs : r ≠ s) :
    KDerivation (imp (singletonCode a s q)
      (imp (pairCode b c s r) (both (equal b a) (equal c a)))) := by
  let A := singletonCode a s q
  let B := pairCode b c s r
  let Γ := [B,A]
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  have ha : Context Γ A := .hypothesis (by simp [Γ])
  have hb : Context Γ B := .hypothesis (by simp [Γ])
  have hsB := Context.mp ha (.closed
    (PAtoCompactUnorderedPair.singleton_instance a s q b hqa hqs hqb))
  have hsC := Context.mp ha (.closed
    (PAtoCompactUnorderedPair.singleton_instance a s q c hqa hqs hqc))
  have hpB := Context.mp hb (.closed (pair_instance b c s r b hrb hrc hrs hrb))
  have hpC := Context.mp hb (.closed (pair_instance b c s r c hrb hrc hrs hrc))
  have hbb : Context Γ (either (equal b b) (equal b c)) :=
    Context.disjunctionLeft (b := equal b c) (.closed (equalityReflexive b))
  have hcc : Context Γ (either (equal c b) (equal c c)) :=
    Context.disjunctionRight (a := equal c b) (.closed (equalityReflexive c))
  have hbm : Context Γ (member s b) := .mp hbb (Context.conjunctionRight hpB)
  have hcm : Context Γ (member s c) := .mp hcc (Context.conjunctionRight hpC)
  have hba : Context Γ (equal b a) := .mp hbm (Context.conjunctionLeft hsB)
  have hca : Context Γ (equal c a) := .mp hcm (Context.conjunctionLeft hsC)
  exact Context.conjunctionIntro hba hca

theorem singleton_pair_coordinates_certificate (a b c s q r : Nat)
    (hqa : q ≠ a) (hqb : q ≠ b) (hqc : q ≠ c) (hqs : q ≠ s)
    (hrb : r ≠ b) (hrc : r ≠ c) (hrs : r ≠ s) :
    theoremCode (certificate (singleton_pair_coordinates a b c s q r
      hqa hqb hqc hqs hrb hrc hrs)) =
      imp (singletonCode a s q) (imp (pairCode b c s r) (both (equal b a) (equal c a))) :=
  certificate_correct (singleton_pair_coordinates a b c s q r hqa hqb hqc hqs hrb hrc hrs)

end PASoundness.PAtoCompactSingletonPairCoordinates

#print axioms PASoundness.PAtoCompactSingletonPairCoordinates.singleton_pair_coordinates
#print axioms PASoundness.PAtoCompactSingletonPairCoordinates.singleton_pair_coordinates_certificate
