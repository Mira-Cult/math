import PASoundness.PAtoCompactLeastCounterexample
import PASoundness.PAtoCompactGreatestSuccessor

/-! Standard HF truth of the least/greatest subset conditions at finite
ordinals. This is semantic validation of the displayed conditions, not a K
derivation that an arithmetic domain exists. -/
namespace PASoundness.PAtoCompactOrdinalExtrema
open PASoundness.CompactMatrix PASoundness.HFCoding
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactPredecessor PASoundness.PAtoCompactLeastCounterexample
open PASoundness.PAtoCompactGreatestSuccessor

/-- Every nonempty represented subset of a finite ordinal has a least and a
  greatest member under the represented membership order. -/
theorem ordinal_subset_extrema (n u : Nat)
    (hsub : ∀ v, bit u v = true → bit (ordinal n).code v = true)
    (hne : ∃ v, bit u v = true) :
    (∃ m, bit u m = true ∧ ∀ v, bit u v = true →
      (v = m ∨ bit v m = true)) ∧
    (∃ m, bit u m = true ∧ ∀ v, bit u v = true →
      (v = m ∨ bit m v = true)) := by
  classical
  let s := (Finset.range n).filter (fun i => bit u (ordinal i).code = true)
  have repr : ∀ v, bit u v = true → ∃ i < n, v = (ordinal i).code := by
    intro v hv
    have h : (⟨v⟩ : Object) ∈ ordinal n := hsub v hv
    obtain ⟨i, hi, he⟩ := (mem_ordinal _ _).mp h
    exact ⟨i, hi, congrArg Object.code he⟩
  have hs : s.Nonempty := by
    obtain ⟨v,hv⟩ := hne
    obtain ⟨i,hi,he⟩ := repr v hv
    exact ⟨i, by simp [s, hi, ← he, hv]⟩
  constructor
  · refine ⟨(ordinal (s.min' hs)).code, ?_, ?_⟩
    · exact (Finset.mem_filter.mp (s.min'_mem hs)).2
    · intro v hv
      obtain ⟨i,hi,he⟩ := repr v hv
      have his : i ∈ s := by simp [s, hi, ← he, hv]
      have hle := s.min'_le i his
      by_cases h : i = s.min' hs
      · left; simp [he, h]
      · right
        subst v
        change ordinal (s.min' hs) ∈ ordinal i
        exact ordinal_member (by omega)
  · refine ⟨(ordinal (s.max' hs)).code, ?_, ?_⟩
    · exact (Finset.mem_filter.mp (s.max'_mem hs)).2
    · intro v hv
      obtain ⟨i,hi,he⟩ := repr v hv
      have his : i ∈ s := by simp [s, hi, ← he, hv]
      have hle := s.le_max' i his
      by_cases h : i = s.max' hs
      · left; simp [he, h]
      · right
        subst v
        change ordinal i ∈ ordinal (s.max' hs)
        exact ordinal_member (by omega)

/-- In standard HF semantics, each finite ordinal satisfies the literal
least-subset and greatest-subset formulas under the displayed fresh names. -/
theorem ordinal_extrema_codes (x u k a m r n : Nat) (ρ : Environment)
    (fresh : [x,u,k,a,m,r].Nodup) (hx : ρ x = (ordinal n).code) :
    (decode (leastSubsetsCode x u k a m r)).Realize ρ ∧
    (decode (greatestSubsetsCode x u k m r)).Realize ρ := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, not_false_eq_true] at fresh
  simp only [leastSubsetsCode, greatestSubsetsCode, subsetCode, nonemptyCode,
    leastMemberCode, hasGreatestCode, greatestCode, CompactDerivations.either,
    CompactSemantics.realize_all, CompactSemantics.realize_imp,
    CompactSemantics.realize_exists, CompactSemantics.realize_both,
    CompactSemantics.realize_neg, CompactSemantics.realize_member,
    CompactSemantics.realize_equal]
  simp_all [CompactMatrix.update, Ne.symm]
  constructor
  · intro v hs a ha
    obtain ⟨w,hw,hmin⟩ := (ordinal_subset_extrema n v hs ⟨a,ha⟩).1
    refine ⟨w,hw,?_⟩
    intro z hz hne
    exact (hmin z hz).resolve_left hne
  · intro v hs a ha
    obtain ⟨w,hw,hmax⟩ := (ordinal_subset_extrema n v hs ⟨a,ha⟩).2
    refine ⟨w,hw,?_⟩
    intro z hz hne
    exact (hmax z hz).resolve_left hne

end PASoundness.PAtoCompactOrdinalExtrema

#print axioms PASoundness.PAtoCompactOrdinalExtrema.ordinal_subset_extrema
#print axioms PASoundness.PAtoCompactOrdinalExtrema.ordinal_extrema_codes
