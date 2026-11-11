import Sude.FWEnhancedPhaseBounds
import Sude.FWFullStockIterationFromCharge

/-! One enhanced affine phase from an explicit stage-charge hypothesis.
    Linked schedules and numeric targets remain conditional inputs. -/
namespace Sude
noncomputable section

/-- One fixed-wheel phase with a certified lower radius and an explicit
finite-recurrence target. The same trace and witness reservation are used. -/
theorem fw_enhanced_single_phase_of_charge (i : Fin 8)
    (upperSharp : RSIndexUpperSharp) {n : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 21248)
    (hQ : ((6 * (n + 8) : ℕ) : ℝ) ≤ (1 / 69780 : ℝ) * (poolMaximum n : ℝ))
    (batches : ℕ → List DoublePair) (hvalid : ∀ j < 5, FWBridgeSequentialValid n ∅ batches j)
    (candidates : Finset ℕ) (hcard : candidates.card = 17 * (6 * (n + 8)))
    (kept : Finset ℕ) (hsub : kept ⊆ Finset.range 17) (hkept : kept.card = 16)
    (hinj : Function.Injective (sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard))
    (blocks : List DoublePair) (hblocks : blocks.length = 3 * (n / 450) * (3 * (n + 8)))
    (fuel last floor target : ℕ) (S : Finset ℕ) (stages : List BTSelectedStage)
    (trace : BTGrowingTrace 2 (6 * (n + 8))
      (((poolFinset n).filter (fun p => 43 < p)) \
        fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks)
      32 S last stages)
    (hcap : stages.length + fuel ≤ 238) (hfloor : 11648 ≤ floor) (hbelow : floor ≤ last)
    (horigin : fwAffineOriginUpper i ≤ floor)
    (htarget : target ≤ fwEnhancedPhaseRun i stages.length fuel floor) :
    ∃ (final : Finset ℕ) (actualFinal : ℕ) (extra : List BTSelectedStage),
      BTGrowingTrace 2 (6 * (n + 8))
        (((poolFinset n).filter (fun p => 43 < p)) \
          fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks)
        32 final actualFinal (stages ++ extra) ∧
      extra.length ≤ fuel ∧ final ⊆ S ∧
      final.card + 2 * (6 * (n + 8)) * extra.length = S.card ∧
      fwVaryingStockMass (poolMaximum n) (stages ++ extra).length ≤ (final.card : ℝ) ∧
      ((poolMaximum n : ℝ) / 23 ≤ actualFinal ∨
        (extra.length = fuel ∧ target ≤ actualFinal)) ∧
      NarrowedStages ((poolMaximum n : ℝ) / 6) extra ∧
      (∀ stage ∈ extra, Disjoint stage.footprint
        (fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks)) ∧
      last ≤ actualFinal ∧ 2 ∣ actualFinal ∧
      FWFullStockSchedule i n stages.length last actualFinal extra := by
  have hX : (0 : ℝ) < poolMaximum n := by exact_mod_cast (poolMaximum_prime n).pos
  have hshift := fw_indexed_affine_shift_of_radius i hX
    (show (3257 / 100000 : ℝ) ≤ 3257 / 100000 by rfl) (le_trans horigin hbelow)
  obtain ⟨final, actualFinal, extra, htrace, hlen, hsubset, hcard', hstock, hstop,
    hnarrow, hdisj, hgrows, heven, hsched⟩ :=
    fw_full_stock_iterate_bounded_of_charge i upperSharp hnlo hnhi hQ batches hvalid
      candidates hcard kept hsub hkept hinj blocks hblocks fuel last S stages trace hcap
      (by omega) hshift
  refine ⟨final, actualFinal, extra, htrace, hlen, hsubset, hcard', hstock, ?_,
    hnarrow, hdisj, hgrows, heven, hsched⟩
  rcases hstop with hcross | hfull
  · exact Or.inl hcross
  · right
    refine ⟨hfull, ?_⟩
    have hbound := fw_enhanced_phase_schedule_lower hsched floor hbelow
    rw [hfull] at hbound
    exact htarget.trans hbound

end
end Sude
