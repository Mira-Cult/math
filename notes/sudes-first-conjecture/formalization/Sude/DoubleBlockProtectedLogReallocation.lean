import Sude.DoubleBlockLogSelection
import Sude.FWBridgeWideDoubleReallocation

/-! Conditional realization of independently selected double-block midpoint
controls on a single square, preserving supplied disjoint protected families.
No geometric packing, line-sum, grid, or numerical invoice is asserted. -/
namespace Sude
noncomputable section

/-- The actual midpoint score on the final square, centered using the source
square's stage means and the fixed destination line incidences. -/
def doubleBlockActualCenteredScore {n P B : ℕ}
    (cells : (Fin P × Fin B × Fin 2) × Bool → Cell n)
    (line : Cell n → Prop) (old new : Cell n ≃ Fin (n * n)) : ℝ :=
  ∑ j, ∑ b, ((∑ p, physicalPairLineWeight cells line (j,b,p) *
    doubleBlockPairMidpoint cells new j b p) -
    doubleBlockLineWeight cells line j b * doubleStageMidpointMean cells old j)

/-- The sampled score is exactly the actual centered midpoint score whenever
the final square realizes the sampled whole-block and shared-swap controls. -/
theorem double_block_actual_centered_score_eq_sample {n P B : ℕ}
    (cells : (Fin P × Fin B × Fin 2) × Bool → Cell n)
    (line : Cell n → Prop) (old new : Cell n ≃ Fin (n * n))
    (π : Fin P → Equiv.Perm (Fin B)) (s : (Fin P × Fin B) → Bool)
    (hentry : ∀ j b p side, entry new (cells ((j,b,p),side)) =
      entry old (cells ((j,π j b, doubleBlockPairSwap (s (j,b)) p),side))) :
    doubleBlockActualCenteredScore cells line old new = doubleBlockSampleScore cells line old π s := by
  classical
  unfold doubleBlockActualCenteredScore doubleBlockSampleScore
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro b _
  rw [double_block_weighted_midpoint_eq_swap cells line old new π (fun j b => s (j,b)) hentry j b]

/-- Select and install two disjoint double-block families on the same source
square. Both logarithmic invoices and all source gap and support assumptions
are supplied. The resulting score bounds concern midpoint contributions only. -/
theorem double_block_two_family_protected_log_reallocation
    {n P W B m : ℕ} {α β : Type*} (hB : 0 < B) (hm : 0 < m)
    (old : Cell n ≃ Fin (n * n))
    (bridge : (Fin P × Fin B × Fin 2) × Bool → Cell n)
    (wide : (Fin W × Fin B × Fin 2) × Bool → Cell n)
    (seed : α → Cell n) (growth : β → Cell n)
    (hb : Function.Injective bridge) (hw : Function.Injective wide)
    (hbw : ∀ x y, bridge x ≠ wide y)
    (hbs : ∀ x y, bridge x ≠ seed y) (hbg : ∀ x y, bridge x ≠ growth y)
    (hws : ∀ x y, wide x ≠ seed y) (hwg : ∀ x y, wide x ≠ growth y)
    (line : Fin m → Cell n → Prop)
    (lob hib : Fin P → ℝ) (low hiw : Fin W → ℝ)
    (Vb Vw : ℝ) (hVb : 0 < Vb) (hVw : 0 < Vw)
    (hintervalb : ∀ j b p, doubleBlockPairMidpoint bridge old j b p ∈ Set.Icc (lob j) (hib j))
    (hintervalw : ∀ j b p, doubleBlockPairMidpoint wide old j b p ∈ Set.Icc (low j) (hiw j))
    (hinvoiceb : ∀ l, doubleBlockCombinedProxy bridge (line l) lob hib ≤ Vb / 4)
    (hinvoicew : ∀ l, doubleBlockCombinedProxy wide (line l) low hiw ≤ Vw / 4)
    (gapb : Fin P → Fin B → ℕ) (gapw : Fin W → Fin B → ℕ)
    (hgapb : ∀ j b p, entry old (bridge ((j,b,p),true)) =
      entry old (bridge ((j,b,p),false)) + gapb j b)
    (hgapw : ∀ j b p, entry old (wide ((j,b,p),true)) =
      entry old (wide ((j,b,p),false)) + gapw j b) :
    ∃ (πb : Fin P → Equiv.Perm (Fin B)) (sb : (Fin P × Fin B) → Bool)
      (πw : Fin W → Equiv.Perm (Fin B)) (sw : (Fin W × Fin B) → Bool)
      (new : Cell n ≃ Fin (n * n)),
      (∀ j b p side, entry new (bridge ((j,b,p),side)) =
        entry old (bridge ((j,πb j b,doubleBlockPairSwap (sb (j,b)) p),side))) ∧
      (∀ j b p side, entry new (wide ((j,b,p),side)) =
        entry old (wide ((j,πw j b,doubleBlockPairSwap (sw (j,b)) p),side))) ∧
      (∀ x, entry new (seed x) = entry old (seed x)) ∧
      (∀ x, entry new (growth x) = entry old (growth x)) ∧
      (∀ c, c ∉ Set.range bridge → c ∉ Set.range wide → entry new c = entry old c) ∧
      (∀ j, Finset.univ.image (fun x : (Fin B × Fin 2) × Bool =>
        entry new (bridge ((j,x.1.1,x.1.2),x.2))) =
        Finset.univ.image (fun x : (Fin B × Fin 2) × Bool =>
        entry old (bridge ((j,x.1.1,x.1.2),x.2)))) ∧
      (∀ j, Finset.univ.image (fun x : (Fin B × Fin 2) × Bool =>
        entry new (wide ((j,x.1.1,x.1.2),x.2))) =
        Finset.univ.image (fun x : (Fin B × Fin 2) × Bool =>
        entry old (wide ((j,x.1.1,x.1.2),x.2)))) ∧
      (∀ gap : Fin P → Fin B → ℕ, (∀ j b p,
        entry old (bridge ((j,b,p),true)) = entry old (bridge ((j,b,p),false)) + gap j b) →
        ∀ j b p, entry new (bridge ((j,b,p),true)) =
          entry new (bridge ((j,b,p),false)) + gap j (πb j b)) ∧
      (∀ gap : Fin W → Fin B → ℕ, (∀ j b p,
        entry old (wide ((j,b,p),true)) = entry old (wide ((j,b,p),false)) + gap j b) →
        ∀ j b p, entry new (wide ((j,b,p),true)) =
          entry new (wide ((j,b,p),false)) + gap j (πw j b)) ∧
      (∀ j b p, entry new (bridge ((j,b,p),true)) =
        entry new (bridge ((j,b,p),false)) + gapb j (πb j b)) ∧
      (∀ j b p, entry new (wide ((j,b,p),true)) =
        entry new (wide ((j,b,p),false)) + gapw j (πw j b)) ∧
      (∀ l, |doubleBlockActualCenteredScore bridge (line l) old new| <
        Real.sqrt (Vb * Real.log (4 * (m : ℝ)) / 2)) ∧
      (∀ l, |doubleBlockActualCenteredScore wide (line l) old new| <
        Real.sqrt (Vw * Real.log (4 * (m : ℝ)) / 2)) := by
  classical
  obtain ⟨πb, sb, hscoreb⟩ := double_block_log_simultaneous_sample_exists hB hm Vb hVb
    bridge line old lob hib hintervalb hinvoiceb
  obtain ⟨πw, sw, hscorew⟩ := double_block_log_simultaneous_sample_exists hB hm Vw hVw
    wide line old low hiw hintervalw hinvoicew
  obtain ⟨new, hbe, hwe, hsf, hgf, hfix, hbi, hwi, hbgap, hwgap⟩ :=
    fw_reallocate_two_double_families old bridge wide seed growth hb hw hbw hbs hbg hws hwg
      πb (fun j b => doubleBlockPairSwap (sb (j,b)))
      πw (fun j b => doubleBlockPairSwap (sw (j,b)))
  refine ⟨πb, sb, πw, sw, new, hbe, hwe, hsf, hgf, hfix, hbi, hwi, hbgap, hwgap, hbgap gapb hgapb, hwgap gapw hgapw, ?_, ?_⟩
  · intro l
    rw [double_block_actual_centered_score_eq_sample bridge (line l) old new πb sb hbe]
    exact hscoreb l
  · intro l
    rw [double_block_actual_centered_score_eq_sample wide (line l) old new πw sw hwe]
    exact hscorew l

end
end Sude
