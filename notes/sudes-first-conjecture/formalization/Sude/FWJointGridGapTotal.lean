import Sude.FWJointSupportedIndex

/-! Exact gap totals for the supplied FW grid labels and their injective
physical relabeling. No physical witness or gap hypothesis is constructed. -/
namespace Sude
noncomputable section

/-- The supported seed, growth, bridge and wide labels retain every supplied
gap exactly once. The bridge family is restricted to its five supported tags. -/
theorem fw_joint_grid_gap_total {P J : ℕ}
    (seed : Fin 16 → ℕ) (growth : Fin P → ℕ)
    (bridge : ℕ → ℕ) (wide : Fin J → ℕ) :
    (∑ x ∈ fwJointGridLabels (fwJointPreWideGridLabels P) J,
      Sum.elim (Sum.elim (Sum.elim seed growth) bridge) wide x) =
      (∑ i, seed i) + (∑ i, growth i) +
        (∑ i ∈ Finset.range 5, bridge i) + ∑ i, wide i := by
  classical
  have hd₁ : Disjoint
      ((fwJointPreWideGridLabels P).map ⟨Sum.inl, Sum.inl_injective⟩)
      ((Finset.univ : Finset (Fin J)).map ⟨Sum.inr, Sum.inr_injective⟩) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    simp only [Finset.mem_map] at hx hy
    obtain ⟨a, _, rfl⟩ := hx
    obtain ⟨b, _, hb⟩ := hy
    cases hb
  have hd₂ : Disjoint
      ((Finset.univ : Finset (Fin 16 ⊕ Fin P)).map ⟨Sum.inl, Sum.inl_injective⟩)
      ((Finset.range 5).image (Sum.inr : ℕ → (Fin 16 ⊕ Fin P) ⊕ ℕ)) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    simp only [Finset.mem_map, Finset.mem_image] at hx hy
    obtain ⟨a, _, rfl⟩ := hx
    obtain ⟨b, _, hb⟩ := hy
    cases hb
  rw [fwJointGridLabels, Finset.sum_union hd₁, Finset.sum_map, Finset.sum_map]
  rw [fwJointPreWideGridLabels, Finset.sum_union hd₂, Finset.sum_map,
    Finset.sum_image (by intro a _ b _ h; exact Sum.inr_injective h)]
  rw [Fintype.sum_sum_type]
  rfl

/-- An injective actual-slot map transports the exact label total, assuming
the physical gap agrees with the supplied gap at each supported label. -/
theorem fw_joint_grid_gap_total_on_slots {P J : ℕ} {K : Type*} [DecidableEq K]
    (seed : Fin 16 → ℕ) (growth : Fin P → ℕ)
    (bridge : ℕ → ℕ) (wide : Fin J → ℕ)
    (slot : {x // x ∈ fwJointGridLabels (fwJointPreWideGridLabels P) J} → K)
    (gap : K → ℕ) (hinj : Function.Injective slot)
    (hgap : ∀ x, gap (slot x) =
      Sum.elim (Sum.elim (Sum.elim seed growth) bridge) wide x.val) :
    (∑ k ∈ (fwJointGridLabels (fwJointPreWideGridLabels P) J).attach.image slot, gap k) =
      (∑ i, seed i) + (∑ i, growth i) +
        (∑ i ∈ Finset.range 5, bridge i) + ∑ i, wide i := by
  classical
  rw [Finset.sum_image (by intro a _ b _ h; exact hinj h)]
  simp_rw [hgap]
  rw [Finset.sum_attach]
  exact fw_joint_grid_gap_total seed growth bridge wide

/-- If the supplied seed gaps are two and the supplied prefix radius is
exactly their total plus the growth gaps, the transported physical total is
that radius plus the five bridge gaps and the wide gaps. -/
theorem fw_joint_grid_actual_radius_on_slots {P J : ℕ} {K : Type*} [DecidableEq K]
    (seed : Fin 16 → ℕ) (growth : Fin P → ℕ)
    (bridge : ℕ → ℕ) (wide : Fin J → ℕ) (last : ℕ)
    (slot : {x // x ∈ fwJointGridLabels (fwJointPreWideGridLabels P) J} → K)
    (gap : K → ℕ) (hinj : Function.Injective slot)
    (hgap : ∀ x, gap (slot x) =
      Sum.elim (Sum.elim (Sum.elim seed growth) bridge) wide x.val)
    (hseed : ∀ i, seed i = 2) (hlast : last = 32 + ∑ i, growth i) :
    (∑ k ∈ (fwJointGridLabels (fwJointPreWideGridLabels P) J).attach.image slot, gap k) =
      last + (∑ i ∈ Finset.range 5, bridge i) + ∑ i, wide i := by
  rw [fw_joint_grid_gap_total_on_slots seed growth bridge wide slot gap hinj hgap]
  have hs : (∑ i, seed i) = 32 := by simp [hseed]
  rw [hs, hlast]

end
end Sude
