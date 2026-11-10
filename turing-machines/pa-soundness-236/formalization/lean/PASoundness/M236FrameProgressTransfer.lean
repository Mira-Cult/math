import PASoundness.M236Observer
/-! Frame progress is invariant under singleton-bit ordered-output refinement. -/
namespace PASoundness.M236Observer
open PASoundness.Observer PASoundness.UnaryCodec

theorem prefix_length_attained {C : Type} (M : WordEventSystem C Bool)
    (bits : M.PhysicalBits) (m k : Nat) (hk : k ≤ (M.prefixWord m).length) :
    ∃ i, i ≤ m ∧ (M.prefixWord i).length = k := by
  induction m with
  | zero =>
    simp only [WordEventSystem.prefix_zero, List.length_nil] at hk
    have : k = 0 := by omega
    subst k
    exact ⟨0, Nat.le_refl _, rfl⟩
  | succ m ih =>
    by_cases hprev : k ≤ (M.prefixWord m).length
    · obtain ⟨i, hi, he⟩ := ih hprev
      exact ⟨i, by omega, he⟩
    · refine ⟨m+1, by omega, ?_⟩
      have hb := bits m
      simp only [WordEventSystem.prefix_succ, List.length_append] at hk ⊢
      omega

theorem output_prefix_attained {C : Type} (M : WordEventSystem C Bool)
    (bits : M.PhysicalBits) (w : List Bool) (hw : M.OutputPrefix w) :
    ∃ i, M.prefixWord i = w := by
  obtain ⟨m, suffix, hm⟩ := hw
  have hk : w.length ≤ (M.prefixWord m).length := by rw [hm, List.length_append]; omega
  obtain ⟨i, hi, hlen⟩ := prefix_length_attained M bits m w.length hk
  obtain ⟨tail, ht⟩ := M.prefix_extends hi
  have heq : M.prefixWord i ++ tail = w ++ suffix := ht.symm.trans hm
  have htakes := congrArg (List.take w.length) heq
  have hleft : List.take w.length (M.prefixWord i ++ tail) = M.prefixWord i :=
    List.take_left' hlen
  have hright : List.take w.length (w ++ suffix) = w := List.take_left
  rw [hleft, hright] at htakes
  exact ⟨i, htakes⟩

theorem output_prefix_attained_after {C : Type} (M : WordEventSystem C Bool)
    (bits : M.PhysicalBits) (t : Nat) (w : List Bool) (hw : M.OutputPrefix w)
    (hprefix : M.prefixWord t <+: w) : ∃ u, t ≤ u ∧ M.prefixWord u = w := by
  obtain ⟨u, hu⟩ := output_prefix_attained M bits w hw
  by_cases htu : t ≤ u
  · exact ⟨u, htu, hu⟩
  · have hut : u ≤ t := by omega
    obtain ⟨suffix, hs⟩ := M.prefix_extends hut
    have hprefix' : w <+: M.prefixWord t := by
      refine ⟨suffix, ?_⟩
      simpa only [hu] using hs.symm
    have heq : w = M.prefixWord t := hprefix'.eq_of_length_le hprefix.length_le
    exact ⟨t, Nat.le_refl _, heq.symm⟩

theorem frameProgress_of_sameOutput {S T : Type}
    {source : WordEventSystem S Bool} {target : WordEventSystem T Bool}
    (hs : source.PhysicalBits) (ht : target.PhysicalBits)
    (same : SameOutput source target) (hframe : FrameProgress source) : FrameProgress target := by
  intro t
  have hp : target.OutputPrefix (target.prefixWord t) := ⟨t, [], by simp⟩
  have hp' := (same _).mpr hp
  obtain ⟨u, hu⟩ := output_prefix_attained source hs (target.prefixWord t) hp'
  obtain ⟨v, huv, hc, hz⟩ := hframe u
  have htarget : target.OutputPrefix (source.prefixWord v) :=
    (same _).mp ⟨v, [], by simp⟩
  obtain ⟨suffix, he⟩ := source.prefix_extends huv
  have hprefix : target.prefixWord t <+: source.prefixWord v := by
    refine ⟨suffix, ?_⟩
    simpa only [hu] using he.symm
  obtain ⟨q, htq, hq⟩ := output_prefix_attained_after target ht t (source.prefixWord v) htarget hprefix
  exact ⟨q, htq, by simpa only [hq] using hc, by simpa only [hq] using hz⟩

theorem frameProgress_iff_of_sameOutput {S T : Type}
    {source : WordEventSystem S Bool} {target : WordEventSystem T Bool}
    (hs : source.PhysicalBits) (ht : target.PhysicalBits) (same : SameOutput source target) :
    FrameProgress source ↔ FrameProgress target :=
  ⟨frameProgress_of_sameOutput hs ht same,
   frameProgress_of_sameOutput ht hs (fun w => (same w).symm)⟩
end PASoundness.M236Observer
