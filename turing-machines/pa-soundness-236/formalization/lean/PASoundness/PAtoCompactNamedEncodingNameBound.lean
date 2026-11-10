import PASoundness.CompactNamed
import PASoundness.PAtoCompactFilteredSubset

/-! Syntactic upper bounds for every literal name in the compact named formula
IR, including quantified binder names. No K derivability or semantic soundness
is involved. -/
namespace PASoundness.PAtoCompactNamedEncodingNameBound
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.PAtoCompactFilteredSubset

private theorem imp_left_le (a b : Nat) : a ≤ imp a b := by
  have h := Cantor.left_le_pair a b
  unfold imp
  omega

private theorem imp_right_le (a b : Nat) : b ≤ imp a b := by
  have h := Cantor.right_le_pair a b
  unfold imp
  omega

private theorem member_left_lt (a b : Nat) : a < member a b := by
  have h := Cantor.left_le_pair a b
  unfold member
  omega

private theorem member_right_lt (a b : Nat) : b < member a b := by
  have h := Cantor.right_le_pair a b
  unfold member
  omega

private theorem equal_left_lt (a b : Nat) : a < equal a b := by
  have h := Cantor.left_le_pair a b
  unfold equal
  omega

private theorem equal_right_lt (a b : Nat) : b < equal a b := by
  have h := Cantor.right_le_pair a b
  unfold equal
  omega

private theorem all_left_lt (a b : Nat) : a < allCode a b := by
  have h := Cantor.left_le_pair a b
  unfold allCode
  omega

private theorem all_right_lt (a b : Nat) : b < allCode a b := by
  have h := Cantor.right_le_pair a b
  unfold allCode
  omega

private theorem exists_left_lt (a b : Nat) : a < existsCode a b := by
  have h := all_left_lt a (neg b)
  have h' := imp_left_le (allCode a (neg b)) 1
  change a < imp (allCode a (neg b)) 1
  exact lt_of_lt_of_le h h'

private theorem exists_right_le (a b : Nat) : b ≤ existsCode a b := by
  have h := imp_left_le b 1
  have h' := all_right_lt a (neg b)
  have h'' := imp_left_le (allCode a (neg b)) 1
  unfold existsCode neg at *
  omega

/-- Every variable name occurring in the named compact formula, including
bound labels, is strictly smaller than the formula's literal encoding. -/
theorem names_lt_encode (f : Formula) : ∀ x ∈ f.names, x < f.encode := by
  induction f with
  | truth => simp [Formula.names]
  | bottom => simp [Formula.names]
  | imp a b ia ib =>
      intro x hx
      simp only [Formula.names, Finset.mem_union] at hx
      change x < imp a.encode b.encode
      rcases hx with ha | hb
      · exact lt_of_lt_of_le (ia x ha) (imp_left_le _ _)
      · exact lt_of_lt_of_le (ib x hb) (imp_right_le _ _)
  | member a b =>
      intro x hx
      simp only [Formula.names, Finset.mem_insert, Finset.mem_singleton] at hx
      change x < member a b
      rcases hx with rfl | rfl
      · exact member_left_lt _ _
      · exact member_right_lt _ _
  | equal a b =>
      intro x hx
      simp only [Formula.names, Finset.mem_insert, Finset.mem_singleton] at hx
      change x < equal a b
      rcases hx with rfl | rfl
      · exact equal_left_lt _ _
      · exact equal_right_lt _ _
  | all y a ia =>
      intro x hx
      simp only [Formula.names, Finset.mem_insert] at hx
      change x < allCode y a.encode
      rcases hx with rfl | ha
      · exact all_left_lt _ _
      · exact lt_trans (ia x ha) (all_right_lt _ _)
  | ex y a ia =>
      intro x hx
      simp only [Formula.names, Finset.mem_insert] at hx
      change x < existsCode y a.encode
      rcases hx with rfl | ha
      · exact exists_left_lt _ _
      · exact lt_of_lt_of_le (ia x ha) (exists_right_le _ _)

/-- The computed filter selector is absent from every named formula, including
its binder labels. -/
theorem filter_selector_not_in_names (Y t : Nat) (f : Formula) :
    filterPredicate Y t (neg f.encode) ∉ f.names := by
  intro hx
  have hf := names_lt_encode f _ hx
  have hn := imp_left_le f.encode 1
  have hs := (filterPredicate_bounds Y t (neg f.encode)).2.2
  change f.encode ≤ neg f.encode at hn
  omega

end PASoundness.PAtoCompactNamedEncodingNameBound

#print axioms PASoundness.PAtoCompactNamedEncodingNameBound.names_lt_encode
#print axioms PASoundness.PAtoCompactNamedEncodingNameBound.filter_selector_not_in_names
