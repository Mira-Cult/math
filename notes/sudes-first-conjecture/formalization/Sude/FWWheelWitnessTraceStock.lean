import Sude.FWWheelActualStock
import Sude.FWBridgeSeedWideRolePreservation

/-! Stock accounting for the same actual bridge, retained-seed, and wide
witnesses, conditional on a supplied growth trace. No new selection, layout,
source numerical estimate, or trace existence is asserted. -/
namespace Sude
noncomputable section

/-- The complete early value reservation using the actual selected witnesses. -/
def fwWheelWitnessEarlyValues {n : ℕ} (batches : ℕ → List DoublePair)
    (candidates : Finset ℕ) (hcard : candidates.card = 17 * (6 * (n + 8)))
    (kept : Finset ℕ) (hsub : kept ⊆ Finset.range 17) (blocks : List DoublePair) : Finset ℕ :=
  fwBridgeSeedProtectedValues batches candidates hcard kept hsub ∪
    (doubleBatchLow blocks ∪ doubleBatchHigh blocks)

/-- The actual witness interfaces imply the complete FW10 early charge;
no distinctness between different families is needed for this upper bound. -/
theorem fw_wheel_witness_early_card {n : ℕ} (batches : ℕ → List DoublePair)
    (hvalid : ∀ j < 5, FWBridgeSequentialValid n ∅ batches j)
    (candidates : Finset ℕ) (hcard : candidates.card = 17 * (6 * (n + 8)))
    (kept : Finset ℕ) (hsub : kept ⊆ Finset.range 17) (hkept : kept.card = 16)
    (hinj : Function.Injective (sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard))
    (blocks : List DoublePair)
    (hblocks : blocks.length = 3 * (n / 450) * (3 * (n + 8))) :
    (fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks).card ≤ fwEarlyBudget n := by
  have hlen : ∀ j < 5, (batches j).length = 3 * (n + 8) := fun j hj => (hvalid j hj).1.1
  have hret : (retainedSeedEndpoints candidates 17 (6 * (n + 8)) 2 hcard kept hsub).card =
      2 * (6 * (n + 8)) * 16 := by
    rw [retainedSeedEndpoints, Finset.card_image_of_injective _ hinj, retainedSeedLabels_card, hkept]
  have hwide := fw_wheel_wide_batch_card n blocks hblocks
  simpa [fwWheelWitnessEarlyValues, fwBridgeSeedProtectedValues] using
    fw_wheel_early_reserved_card n batches hlen _ _ hret hwide

/-- Given a trace starting after these very witnesses' early reservation,
it avoids the whole reservation, charges exactly 2Q per step, and retains
the actual screened-stock lower bound. The trace itself remains supplied. -/
theorem fw_wheel_witness_trace_stock {n : ℕ} (hn : 13 ≤ n * n)
    (batches : ℕ → List DoublePair) (hvalid : ∀ j < 5, FWBridgeSequentialValid n ∅ batches j)
    (candidates : Finset ℕ) (hcard : candidates.card = 17 * (6 * (n + 8)))
    (kept : Finset ℕ) (hsub : kept ⊆ Finset.range 17) (hkept : kept.card = 16)
    (hinj : Function.Injective (sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard))
    (blocks : List DoublePair)
    (hblocks : blocks.length = 3 * (n / 450) * (3 * (n + 8)))
    (radius last : ℕ) (final : Finset ℕ) (stages : List BTSelectedStage)
    (trace : BTGrowingTrace 2 (6 * (n + 8))
      (((poolFinset n).filter (fun p => 43 < p)) \
        fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks)
      radius final last stages) :
    let early := fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks
    let initial := ((poolFinset n).filter (fun p => 43 < p)) \ early
    early.card ≤ fwEarlyBudget n ∧
    final ⊆ initial ∧
    final.card + 2 * (6 * (n + 8)) * stages.length = initial.card ∧
    n * n ≤ final.card + fwEarlyBudget n + 13 + 2 * (6 * (n + 8)) * stages.length ∧
    (∀ stage ∈ stages, Disjoint stage.footprint early) ∧
    stages.Pairwise (fun x y => Disjoint x.footprint y.footprint) := by
  dsimp only
  let retained := retainedSeedEndpoints candidates 17 (6 * (n + 8)) 2 hcard kept hsub
  let wide := doubleBatchLow blocks ∪ doubleBatchHigh blocks
  have hlen : ∀ j < 5, (batches j).length = 3 * (n + 8) := fun j hj => (hvalid j hj).1.1
  have hret : retained.card = 2 * (6 * (n + 8)) * 16 := by
    dsimp [retained, retainedSeedEndpoints]
    rw [Finset.card_image_of_injective _ hinj, retainedSeedLabels_card, hkept]
  have hwide := fw_wheel_wide_batch_card n blocks hblocks
  have hstock := fw_wheel_screened_actual_stock n hn batches hlen retained wide hret hwide
    radius last final stages (by simpa [fwWheelWitnessEarlyValues, fwBridgeSeedProtectedValues,
      retained, wide] using trace)
  have hacct := trace.final_accounting
  refine ⟨fw_wheel_witness_early_card batches hvalid candidates hcard kept hsub hkept hinj blocks hblocks,
    hacct.1, hacct.2.1, hstock, ?_, trace.pairwise_disjoint⟩
  intro stage hstage
  apply Finset.disjoint_left.mpr
  intro p hp hearly
  have hmem := trace.footprints_subset stage hstage hp
  exact (Finset.mem_sdiff.mp hmem).2 hearly

/-- The remaining entries of a supplied trace are actual pool primes above
43 and hence units for the first exact-window wheel. -/
theorem fw_wheel_witness_trace_screened_units {n : ℕ}
    (batches : ℕ → List DoublePair)
    (candidates : Finset ℕ) (hcard : candidates.card = 17 * (6 * (n + 8)))
    (kept : Finset ℕ) (hsub : kept ⊆ Finset.range 17) (blocks : List DoublePair)
    (radius last : ℕ) (final : Finset ℕ) (stages : List BTSelectedStage)
    (trace : BTGrowingTrace 2 (6 * (n + 8))
      (((poolFinset n).filter (fun p => 43 < p)) \
        fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks)
      radius final last stages) :
    ∀ p ∈ final, p ∈ pool n ∧ 43 < p ∧ p % 2 = 1 ∧
      Nat.Coprime p 15015 ∧ (p : ℝ) ≤ poolMaximum n := by
  intro p hp
  have hinit := trace.final_accounting.1 hp
  have hscreen := Finset.mem_filter.mp (Finset.mem_sdiff.mp hinit).1
  have hpool := mem_poolFinset.mp hscreen.1
  have hprime := pool_prime_and_residue hpool
  exact ⟨hpool, hscreen.2, hprime.2,
    fw_screened_prime_coprime_15015 p hprime.1 hscreen.2, by
      exact_mod_cast pool_le_poolMaximum hpool⟩

/-- An exact normalized stock envelope, obtained with no additional source
numerical premise. It may be negative until a separate WW4 floor is proved. -/
theorem fw_wheel_witness_trace_normalized_stock {n : ℕ} (hn : 13 ≤ n * n)
    (batches : ℕ → List DoublePair) (hvalid : ∀ j < 5, FWBridgeSequentialValid n ∅ batches j)
    (candidates : Finset ℕ) (hcard : candidates.card = 17 * (6 * (n + 8)))
    (kept : Finset ℕ) (hsub : kept ⊆ Finset.range 17) (hkept : kept.card = 16)
    (hinj : Function.Injective (sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard))
    (blocks : List DoublePair)
    (hblocks : blocks.length = 3 * (n / 450) * (3 * (n + 8)))
    (radius last : ℕ) (final : Finset ℕ) (stages : List BTSelectedStage)
    (trace : BTGrowingTrace 2 (6 * (n + 8))
      (((poolFinset n).filter (fun p => 43 < p)) \
        fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks)
      radius final last stages) :
    ((((n * n : ℕ) : ℝ) - 13 - fwEarlyBudget n -
        2 * ((6 * (n + 8) : ℕ) : ℝ) * stages.length) / (poolMaximum n : ℝ)) *
      (poolMaximum n : ℝ) ≤ final.card := by
  have hx : (0 : ℝ) < poolMaximum n := by exact_mod_cast (poolMaximum_prime n).pos
  have hstock := (fw_wheel_witness_trace_stock hn batches hvalid candidates hcard kept hsub hkept
    hinj blocks hblocks radius last final stages trace).2.2.2.1
  have hstockR : ((n * n : ℕ) : ℝ) ≤ (final.card : ℝ) + fwEarlyBudget n + 13 +
      2 * ((6 * (n + 8) : ℕ) : ℝ) * stages.length := by exact_mod_cast hstock
  have heq : ((((n * n : ℕ) : ℝ) - 13 - fwEarlyBudget n -
        2 * ((6 * (n + 8) : ℕ) : ℝ) * stages.length) / (poolMaximum n : ℝ)) *
      (poolMaximum n : ℝ) = (((n * n : ℕ) : ℝ) - 13 - fwEarlyBudget n -
        2 * ((6 * (n + 8) : ℕ) : ℝ) * stages.length) := by field_simp
  rw [heq]
  linarith


end
end Sude
