import Sude.PrefixSortedLabelSplit

/-! A simultaneous choice of sorted lower halves within every value fiber.
This is value selection only, not the slot allocation or the depth bound. -/
namespace Sude
noncomputable section

/-- Every value group gets a labelled lower half of size `floor(card/2)`;
every lower value is at most every upper value in the same group. Fibers of
size zero or one have empty lower halves. -/
theorem prefix_global_sorted_lower_choices {V G : Type*} [DecidableEq V] [DecidableEq G]
    (values : Finset V) (key : V → G) (x : V → ℝ) :
    ∃ lower : Finset V, lower ⊆ values ∧
      (∀ g, ((values.filter (fun v => key v = g)).filter (fun v => v ∈ lower)).card =
        (values.filter (fun v => key v = g)).card / 2) ∧
      (∀ g, ∀ a ∈ (values.filter (fun v => key v = g)).filter (fun v => v ∈ lower),
        ∀ b ∈ (values.filter (fun v => key v = g)) \ lower, x a ≤ x b) := by
  classical
  let B : G → Finset V := fun g => values.filter (fun v => key v = g)
  have heach : ∀ g, ∃ T : Finset V, T ⊆ B g ∧ T.card = (B g).card / 2 ∧
      (∀ a ∈ T, ∀ b ∈ B g \ T, x a ≤ x b) := by
    intro g
    by_cases h : 2 ≤ (B g).card
    · exact prefix_sorted_label_split (B g) x h
    · refine ⟨∅, Finset.empty_subset _, ?_, ?_⟩
      · simp only [Finset.card_empty]
        omega
      · simp
  let T : G → Finset V := fun g => Classical.choose (heach g)
  have hT (g : G) : T g ⊆ B g ∧ (T g).card = (B g).card / 2 ∧
      (∀ a ∈ T g, ∀ b ∈ B g \ T g, x a ≤ x b) := Classical.choose_spec (heach g)
  let lower := values.filter (fun v => v ∈ T (key v))
  have hsubset : lower ⊆ values := Finset.filter_subset _ _
  have hfiber (g : G) : (B g).filter (fun v => v ∈ lower) = T g := by
    ext v
    constructor
    · intro hv
      have hvg : key v = g := (Finset.mem_filter.mp (Finset.mem_filter.mp hv).1).2
      have hvin : v ∈ T (key v) := (Finset.mem_filter.mp (Finset.mem_filter.mp hv).2).2
      simpa [hvg] using hvin
    · intro hv
      have hvB : v ∈ B g := (hT g).1 hv
      have hvg : key v = g := (Finset.mem_filter.mp hvB).2
      have hvvalues : v ∈ values := (Finset.mem_filter.mp hvB).1
      have hvlower : v ∈ lower := Finset.mem_filter.mpr ⟨hvvalues, by simpa [hvg] using hv⟩
      exact Finset.mem_filter.mpr ⟨hvB, hvlower⟩
  refine ⟨lower, hsubset, ?_, ?_⟩
  · intro g
    change ((B g).filter (fun v => v ∈ lower)).card = (B g).card / 2
    rw [hfiber]
    exact (hT g).2.1
  · intro g a ha b hb
    change a ∈ (B g).filter (fun v => v ∈ lower) at ha
    change b ∈ B g \ lower at hb
    have haT : a ∈ T g := by simpa [hfiber g] using ha
    have hbB := (Finset.mem_sdiff.mp hb).1
    have hbnot : b ∉ T g := by
      intro hbT
      have : b ∈ (B g).filter (fun v => v ∈ lower) := by simpa [hfiber g] using hbT
      exact (Finset.mem_sdiff.mp hb).2 (Finset.mem_filter.mp this).2
    exact (hT g).2.2 a haT b (Finset.mem_sdiff.mpr ⟨hbB, hbnot⟩)

end
end Sude
