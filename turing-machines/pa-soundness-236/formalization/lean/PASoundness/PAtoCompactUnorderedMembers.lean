import PASoundness.PAtoCompactUnorderedCoordinates

/-! The two advertised coordinates belong to an unordered pair, in literal
K proof data. These helpers do not assert representative uniqueness. -/
set_option maxRecDepth 65536
namespace PASoundness.PAtoCompactUnorderedMembers
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactUnorderedPair PASoundness.PAtoCompactUnorderedCoordinates

/-- The first advertised coordinate belongs to the pair. -/
def pair_left_member (a b s q : Nat) (hqa : q ≠ a) (hqb : q ≠ b) (hqs : q ≠ s) :
    KDerivation (imp (pairCode a b s q) (member s a)) := by
  apply Context.closeEmpty
  apply Context.deduction
  let A := pairCode a b s q
  have hi := Context.mp (Context.head [] A) (.closed (pair_instance a b s q a hqa hqb hqs hqa))
  have hd : Context [A] (either (equal a a) (equal a b)) :=
    Context.disjunctionLeft (b := equal a b) (.closed (equalityReflexive a))
  exact .mp hd (Context.conjunctionRight hi)

/-- The second advertised coordinate belongs to the pair. -/
def pair_right_member (a b s q : Nat) (hqa : q ≠ a) (hqb : q ≠ b) (hqs : q ≠ s) :
    KDerivation (imp (pairCode a b s q) (member s b)) := by
  apply Context.closeEmpty
  apply Context.deduction
  let A := pairCode a b s q
  have hi := Context.mp (Context.head [] A) (.closed (pair_instance a b s q b hqa hqb hqs hqb))
  have hd : Context [A] (either (equal b a) (equal b b)) :=
    Context.disjunctionRight (a := equal b a) (.closed (equalityReflexive b))
  exact .mp hd (Context.conjunctionRight hi)

end PASoundness.PAtoCompactUnorderedMembers

#print axioms PASoundness.PAtoCompactUnorderedMembers.pair_left_member
#print axioms PASoundness.PAtoCompactUnorderedMembers.pair_right_member
