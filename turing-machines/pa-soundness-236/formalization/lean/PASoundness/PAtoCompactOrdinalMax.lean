import PASoundness.HFCoding

/-! Standard-HF finite ordinal closure. This is a semantic finite-set fact,
not a theorem of the compact calculus or an internal quotient result. -/
namespace PASoundness.PAtoCompactOrdinalMax
open PASoundness.HFCoding

/-- A transitive HF object all of whose members are finite ordinals is itself
  a finite ordinal. Its largest member, when present, determines its index. -/
theorem transitive_ordinal_members (x : Object)
    (ht : ∀ a, a ∈ x → ∀ b, b ∈ a → b ∈ x)
    (hm : ∀ a, a ∈ x → ∃ n, a = ordinal n) :
    ∃ n, x = ordinal n := by
  classical
  let S := (elements x).image Object.code
  by_cases hs : S.Nonempty
  · have hmax := S.max'_mem hs
    obtain ⟨a,ha,hcode⟩ := Finset.mem_image.mp hmax
    have hax : a ∈ x := (mem_elements a x).mp ha
    obtain ⟨n,han⟩ := hm a hax
    refine ⟨n+1, ?_⟩
    apply HFCoding.ext
    intro b
    constructor
    · intro hb
      obtain ⟨k,hbk⟩ := hm b hb
      have hbS : b.code ∈ S := Finset.mem_image.mpr ⟨b, (mem_elements b x).mpr hb, rfl⟩
      have hbound : b.code ≤ a.code := by
        rw [hcode]
        exact S.le_max' b.code hbS
      have hle : k ≤ n := ordinal_code_strictMono.le_iff_le.mp (by simpa [hbk, han] using hbound)
      apply (mem_ordinal b (n+1)).mpr
      exact ⟨k, by omega, hbk⟩
    · intro hb
      obtain ⟨k,hkn,hbk⟩ := (mem_ordinal b (n+1)).mp hb
      by_cases he : k = n
      · rw [hbk, he, ← han]
        exact hax
      · apply ht a hax b
        rw [hbk, han]
        exact ordinal_member (by omega)
  · have hnone : ∀ a, a ∉ x := by
      intro a ha
      apply hs
      exact ⟨a.code, Finset.mem_image.mpr ⟨a, (mem_elements a x).mpr ha, rfl⟩⟩
    refine ⟨0, ?_⟩
    apply HFCoding.ext
    intro a
    simp [ordinal, hnone]

end PASoundness.PAtoCompactOrdinalMax

#print axioms PASoundness.PAtoCompactOrdinalMax.transitive_ordinal_members
