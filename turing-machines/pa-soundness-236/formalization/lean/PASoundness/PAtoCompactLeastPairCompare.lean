import PASoundness.PAtoCompactLeastPredecessor

/-! A bounded K comparison step for a two-element represented subset. Code 1
is literal self-membership at name 0; the encoded disjunction is not an
unqualified semantic claim for arbitrary raw K structures. Existence of the
pair or least member is not asserted here. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactLeastPairCompare
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactLeastCounterexample PASoundness.PAtoCompactLeastPredecessor

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- If a and b belong to c and a least member m of c is one of a,b, then a and
b are comparable under the encoded membership order. -/
def compare_from_least (c m r a b : Nat)
    (hrc : r ≠ c) (hrm : r ≠ m) (hra : r ≠ a) (hrb : r ≠ b) :
    KDerivation (imp (leastMemberCode c m r) (imp (member c a) (imp (member c b)
      (imp (imp (member c m) (either (equal m a) (equal m b)))
        (either (equal a b) (either (member b a) (member a b))))))) := by
  let L := leastMemberCode c m r
  let A := member c a
  let B := member c b
  let E := imp (member c m) (either (equal m a) (equal m b))
  let C := either (equal a b) (either (member b a) (member a b))
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [E,B,A,L]
  have hl : Context Γ L := .hypothesis (by simp [Γ])
  have ha : Context Γ A := .hypothesis (by simp [Γ])
  have hb : Context Γ B := .hypothesis (by simp [Γ])
  have he : Context Γ E := .hypothesis (by simp [Γ])
  have hm : Context Γ (member c m) := Context.conjunctionLeft hl
  have hcase : Context Γ (either (equal m a) (equal m b)) := .mp hm he
  apply Context.disjunctionElim hcase
  · let Δ := equal m a :: Γ
    have heq : Context Δ (equal m a) := Context.head Γ _
    have hl' : Context Δ L := Context.under hl _
    have hb' : Context Δ B := Context.under hb _
    have hbc : Context Δ (either (equal b m) (member b m)) :=
      .mp hb' (.mp hl' (.closed (least_member_at c m r b hrc hrm hrb)))
    apply Context.disjunctionElim hbc
    · have hbm : Context (equal b m :: Δ) (equal b m) := Context.head Δ _
      have hma : Context (equal b m :: Δ) (equal m a) := Context.under heq _
      have hab : Context (equal b m :: Δ) (equal a b) := Context.eqSymm (Context.eqTrans hbm hma)
      exact Context.disjunctionLeft hab
    · have hbm : Context (member b m :: Δ) (member b m) := Context.head Δ _
      have hma : Context (member b m :: Δ) (equal m a) := Context.under heq _
      have hba : Context (member b m :: Δ) (member b a) :=
        .mp hma (.mp hbm (.closed (memberRightEquality b m a)))
      exact Context.disjunctionRight (Context.disjunctionLeft hba)
  · let Δ := equal m b :: Γ
    have heq : Context Δ (equal m b) := Context.head Γ _
    have hl' : Context Δ L := Context.under hl _
    have ha' : Context Δ A := Context.under ha _
    have hac : Context Δ (either (equal a m) (member a m)) :=
      .mp ha' (.mp hl' (.closed (least_member_at c m r a hrc hrm hra)))
    apply Context.disjunctionElim hac
    · have ham : Context (equal a m :: Δ) (equal a m) := Context.head Δ _
      have hmb : Context (equal a m :: Δ) (equal m b) := Context.under heq _
      exact Context.disjunctionLeft (Context.eqTrans ham hmb)
    · have ham : Context (member a m :: Δ) (member a m) := Context.head Δ _
      have hmb : Context (member a m :: Δ) (equal m b) := Context.under heq _
      have hab : Context (member a m :: Δ) (member a b) :=
        .mp hmb (.mp ham (.closed (memberRightEquality a m b)))
      exact Context.disjunctionRight (Context.disjunctionRight hab)

theorem compare_from_least_certificate (c m r a b : Nat)
    (hrc : r ≠ c) (hrm : r ≠ m) (hra : r ≠ a) (hrb : r ≠ b) :
    theoremCode (certificate (compare_from_least c m r a b hrc hrm hra hrb)) =
      imp (leastMemberCode c m r) (imp (member c a) (imp (member c b)
        (imp (imp (member c m) (either (equal m a) (equal m b)))
          (either (equal a b) (either (member b a) (member a b)))))) :=
  certificate_correct (compare_from_least c m r a b hrc hrm hra hrb)

end PASoundness.PAtoCompactLeastPairCompare

#print axioms PASoundness.PAtoCompactLeastPairCompare.compare_from_least
#print axioms PASoundness.PAtoCompactLeastPairCompare.compare_from_least_certificate
