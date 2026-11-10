import PASoundness.PAtoCompactTransitiveClosure

/-! Literal K reduction of lexicographic comparison for two product edges in
the same new row. Equality of the major coordinates and both minor/output
comparison implications are explicit premises. This does not construct the
row, extract the minor comparisons from its graph, or prove multiplication. -/
namespace PASoundness.PAtoCompactMultiplicationSameRowLex
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTransitiveClosure
attribute [local irreducible] imp Cantor.pair Cantor.triangle
set_option maxRecDepth 65536
set_option maxHeartbeats 0

def forwardMinor : Nat := both (imp (member 8 4) (member 9 5))
  (imp (member 9 5) (member 8 4))
def reverseMinor : Nat := both (imp (member 4 8) (member 5 9))
  (imp (member 5 9) (member 4 8))
def forwardLex : Nat := either (member 7 3) (both (equal 3 7) (member 8 4))
def reverseLex : Nat := either (member 3 7) (both (equal 7 3) (member 4 8))
def forwardClause : Nat := both (imp (member 9 5) forwardLex)
  (imp forwardLex (member 9 5))
def reverseClause : Nat := both (imp (member 5 9) reverseLex)
  (imp reverseLex (member 5 9))

/-- Given equal major coordinates, the exact forward lex disjunction is
interderivable with the minor-coordinate membership. -/
def forward_reduction : KDerivation (imp (equal 3 7)
    (both (imp forwardLex (member 8 4)) (imp (member 8 4) forwardLex))) := by
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [equal 3 7]
  have he : Context Γ (equal 3 7) := .head _ _
  have hleft : Context Γ (imp forwardLex (member 8 4)) := by
    apply Context.deduction
    let Δ := forwardLex :: Γ
    have hl : Context Δ forwardLex := .head _ _
    apply Context.disjunctionElim hl
    · let Θ := member 7 3 :: Δ
      have hm : Context Θ (member 7 3) := .head _ _
      have hh : Context Θ (member 7 7) := .mp (.under (.under he _) _)
        (.mp hm (.closed (memberRightEquality 7 3 7)))
      exact Context.explode _ (.mp hh (.closed (self_membership_implies_code_one 7)))
    · exact Context.conjunctionRight (Context.head _ _)
  have hright : Context Γ (imp (member 8 4) forwardLex) := by
    apply Context.deduction
    exact Context.disjunctionRight (Context.conjunctionIntro (.under he _) (.head _ _))
  exact Context.conjunctionIntro hleft hright

/-- The corresponding reverse disjunction reduces to reverse minor
membership, even when the two major labels denote the same object. -/
def reverse_reduction : KDerivation (imp (equal 3 7)
    (both (imp reverseLex (member 4 8)) (imp (member 4 8) reverseLex))) := by
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [equal 3 7]
  have he : Context Γ (equal 3 7) := .head _ _
  have hes : Context Γ (equal 7 3) := Context.eqSymm he
  have hleft : Context Γ (imp reverseLex (member 4 8)) := by
    apply Context.deduction
    let Δ := reverseLex :: Γ
    have hl : Context Δ reverseLex := .head _ _
    apply Context.disjunctionElim hl
    · let Θ := member 3 7 :: Δ
      have hm : Context Θ (member 3 7) := .head _ _
      have hh : Context Θ (member 3 3) := .mp (.under (.under hes _) _)
        (.mp hm (.closed (memberRightEquality 3 7 3)))
      exact Context.explode _ (.mp hh (.closed (self_membership_implies_code_one 3)))
    · exact Context.conjunctionRight (Context.head _ _)
  have hright : Context Γ (imp (member 4 8) reverseLex) := by
    apply Context.deduction
    exact Context.disjunctionRight (Context.conjunctionIntro (.under hes _) (.head _ _))
  exact Context.conjunctionIntro hleft hright

/-- A pair of exact minor/output order comparisons yields both corresponding
product lex comparisons when the major coordinates are equal. -/
def same_row_lex : KDerivation (imp (equal 3 7) (imp forwardMinor
    (imp reverseMinor (both forwardClause reverseClause)))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [reverseMinor,forwardMinor,equal 3 7]
  have hr : Context Γ reverseMinor := .head _ _
  have hf : Context Γ forwardMinor := .hypothesis (by simp [Γ])
  have he : Context Γ (equal 3 7) := .hypothesis (by simp [Γ])
  have hF := Context.mp he (.closed forward_reduction)
  have hR := Context.mp he (.closed reverse_reduction)
  have hfor1 : Context Γ (imp (member 9 5) forwardLex) := by
    apply Context.deduction
    have hb : Context (member 9 5 :: Γ) (member 8 4) :=
      .mp (.head _ _) (.under (Context.conjunctionRight hf) _)
    exact .mp hb (.under (Context.conjunctionRight hF) _)
  have hfor2 : Context Γ (imp forwardLex (member 9 5)) := by
    apply Context.deduction
    have hb : Context (forwardLex :: Γ) (member 8 4) :=
      .mp (.head _ _) (.under (Context.conjunctionLeft hF) _)
    exact .mp hb (.under (Context.conjunctionLeft hf) _)
  have hrev1 : Context Γ (imp (member 5 9) reverseLex) := by
    apply Context.deduction
    have hb : Context (member 5 9 :: Γ) (member 4 8) :=
      .mp (.head _ _) (.under (Context.conjunctionRight hr) _)
    exact .mp hb (.under (Context.conjunctionRight hR) _)
  have hrev2 : Context Γ (imp reverseLex (member 5 9)) := by
    apply Context.deduction
    have hb : Context (reverseLex :: Γ) (member 4 8) :=
      .mp (.head _ _) (.under (Context.conjunctionLeft hR) _)
    exact .mp hb (.under (Context.conjunctionLeft hr) _)
  exact Context.conjunctionIntro (Context.conjunctionIntro hfor1 hfor2)
    (Context.conjunctionIntro hrev1 hrev2)

theorem same_row_lex_certificate : theoremCode (certificate same_row_lex) =
    imp (equal 3 7) (imp forwardMinor (imp reverseMinor (both forwardClause reverseClause))) :=
  certificate_correct same_row_lex
end PASoundness.PAtoCompactMultiplicationSameRowLex
#print axioms PASoundness.PAtoCompactMultiplicationSameRowLex.forward_reduction
#print axioms PASoundness.PAtoCompactMultiplicationSameRowLex.reverse_reduction
#print axioms PASoundness.PAtoCompactMultiplicationSameRowLex.same_row_lex
#print axioms PASoundness.PAtoCompactMultiplicationSameRowLex.same_row_lex_certificate
