import Sude.FWFullStockTraceStep

/-! Fixed-wheel, first-band continuation using full-stock matching. This
iteration uses each selected gap as the next actual radius and records both
the source minimum and the stronger selected-gap condition. It does not
assert cap crossing, the frozen complete recipe, or physical placement. -/
namespace Sude
noncomputable section

/-- Source and enhanced thresholds at the actual stage index and radius. -/
def fwFullStockSourceD (i : Fin 8) (n j R : ℕ) : ℝ :=
  fwAffineThreshold 2 (fwMixedWheelRho i) (3981035 / 10000000)
    (fwFirstBandMu j * (poolMaximum n : ℝ)) R 1 (poolMaximum n : ℝ) (fwMixedWheelError i)

def fwFullStockEnhancedD (i : Fin 8) (j R : ℕ) : ℝ :=
  fwAffineUniformStockThreshold (fwFirstBandMu j) (6 / 69780) R (23 / 48)
    (fwMixedWheelRho i) (fwMixedWheelError i)

/-- Each added stage records the original source minimum and the stronger
full-stock selected-gap guarantee, with the exact actual-radius update. -/
inductive FWFullStockSchedule (i : Fin 8) (n : ℕ) :
    ℕ → ℕ → ℕ → List BTSelectedStage → Prop
  | nil (j actual : ℕ) : FWFullStockSchedule i n j actual actual []
  | cons (j actual actualFinal : ℕ) (stage : BTSelectedStage) (tail : List BTSelectedStage)
      (hcap : j < 238) (hbefore : (actual : ℝ) < (poolMaximum n : ℝ) / 23)
      (hshift : 0 < (actual : ℝ) - fwAffineOrigin (fwMixedWheelError i) 1
        (poolMaximum n) (3981035 / 10000000) ((3257 / 100000 : ℝ) * poolMaximum n))
      (hminimum : stage.minimum = fwFullStockSourceD i n j actual)
      (hpositive : 0 < stage.gap) (heven : 2 ∣ stage.gap)
      (henhanced : fwFullStockEnhancedD i j actual ≤ stage.gap)
      (hplus : 2 * ⌈fwFullStockSourceD i n j actual / 2⌉₊ + 2 ≤ stage.gap)
      (hupper : stage.gap ≤ actual)
      (hrest : FWFullStockSchedule i n (j + 1) (actual + stage.gap) actualFinal tail) :
      FWFullStockSchedule i n j actual actualFinal (stage :: tail)


/-- Iterate full-stock selections at actual radii on the same supplied
first-band trace, stopping on actual crossing or exhaustion of the given fuel. -/
theorem fw_full_stock_iterate_bounded (i : Fin 8)
    (bmor : BMORFinitePiFour) (lower : RSIndexLower) (upper : RSIndexUpper)
    (upperSharp : RSIndexUpperSharp) {n : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 21248)
    (batches : ℕ → List DoublePair) (hvalid : ∀ j < 5, FWBridgeSequentialValid n ∅ batches j)
    (candidates : Finset ℕ) (hcard : candidates.card = 17 * (6 * (n + 8)))
    (kept : Finset ℕ) (hsub : kept ⊆ Finset.range 17) (hkept : kept.card = 16)
    (hinj : Function.Injective (sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard))
    (blocks : List DoublePair) (hblocks : blocks.length = 3 * (n / 450) * (3 * (n + 8)))
    (fuel last : ℕ) (S : Finset ℕ) (stages : List BTSelectedStage)
    (trace : BTGrowingTrace 2 (6 * (n + 8))
      (((poolFinset n).filter (fun p => 43 < p)) \
        fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks)
      32 S last stages)
    (hcap : stages.length + fuel ≤ 238) (hlast : 11648 ≤ last)
    (hshift : 0 < (last : ℝ) - fwAffineOrigin (fwMixedWheelError i) 1 (poolMaximum n)
      (3981035 / 10000000) ((3257 / 100000 : ℝ) * poolMaximum n)) :
    ∃ (final : Finset ℕ) (actualFinal : ℕ) (extra : List BTSelectedStage),
      BTGrowingTrace 2 (6 * (n + 8))
        (((poolFinset n).filter (fun p => 43 < p)) \
          fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks)
        32 final actualFinal (stages ++ extra) ∧
      extra.length ≤ fuel ∧ final ⊆ S ∧
      final.card + 2 * (6 * (n + 8)) * extra.length = S.card ∧
      fwVaryingStockMass (poolMaximum n) (stages ++ extra).length ≤ (final.card : ℝ) ∧
      ((poolMaximum n : ℝ) / 23 ≤ actualFinal ∨ extra.length = fuel) ∧
      NarrowedStages ((poolMaximum n : ℝ) / 6) extra ∧
      (∀ stage ∈ extra, Disjoint stage.footprint
        (fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks)) ∧
      last ≤ actualFinal ∧ 2 ∣ actualFinal ∧
      FWFullStockSchedule i n stages.length last actualFinal extra := by
  induction fuel generalizing S last stages with
  | zero =>
    have hstock := (fw_first_band_varying_stock_mass bmor lower upper upperSharp hnlo hnhi
      batches hvalid candidates hcard kept hsub hkept hinj blocks hblocks 32 last S stages trace
      (by omega)).2
    have heven := (fw_even_trace_radius_lower trace).2
    refine ⟨S, last, [], ?_, by simp, Finset.Subset.rfl, by simp, ?_, ?_, ?_, ?_, le_rfl, heven,
      FWFullStockSchedule.nil _ _⟩
    · simpa using trace
    · simpa using hstock
    · right; simp
    · simp [NarrowedStages]
    · simp
  | succ fuel ih =>
    by_cases hdone : (poolMaximum n : ℝ) / 23 ≤ last
    · have hstock := (fw_first_band_varying_stock_mass bmor lower upper upperSharp hnlo hnhi
        batches hvalid candidates hcard kept hsub hkept hinj blocks hblocks 32 last S stages trace
        (by omega)).2
      have heven := (fw_even_trace_radius_lower trace).2
      refine ⟨S, last, [], ?_, by simp, Finset.Subset.rfl, by simp, ?_, ?_, ?_, ?_, le_rfl, heven,
        FWFullStockSchedule.nil _ _⟩
      · simpa using trace
      · simpa using hstock
      · exact Or.inl hdone
      · simp [NarrowedStages]
      · simp
    · have hj : stages.length < 238 := by omega
      have hnotdone : (last : ℝ) < (poolMaximum n : ℝ) / 23 := lt_of_not_ge hdone
      obtain ⟨hD, hDR, gap, chosen, hgap, hdiv, hstrong, hsource, hplus, hmax, hcard',
        hpairs, hmatch, hfoot, hdisj, hsize, hdeplete, hmid, hgain, htrace⟩ :=
        fw_full_stock_append_stage i bmor lower upper upperSharp hnlo hnhi batches hvalid
          candidates hcard kept hsub hkept hinj blocks hblocks last S stages trace hj hlast
          hnotdone hshift
      let Dsource := fwFullStockSourceD i n stages.length last
      let stage : BTSelectedStage := ⟨gap, chosen, Dsource⟩
      have htrace' : BTGrowingTrace 2 (6 * (n + 8))
          (((poolFinset n).filter (fun p => 43 < p)) \
            fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks)
          32 (S \ pairFootprint chosen gap) (last + gap) (stages ++ [stage]) := by
        exact htrace
      have hcap' : (stages ++ [stage]).length + fuel ≤ 238 := by simp; omega
      have hlast' : 11648 ≤ last + gap := by omega
      have hshift' : 0 < ((last + gap : ℕ) : ℝ) -
          fwAffineOrigin (fwMixedWheelError i) 1 (poolMaximum n)
            (3981035 / 10000000) ((3257 / 100000 : ℝ) * poolMaximum n) := by
        push_cast
        have hg : (0 : ℝ) ≤ gap := by positivity
        linarith
      obtain ⟨final, actualFinal, extra, hfinal, hlen, hfinalSub, hfinalCard, hfinalStock,
        hstop, hnarrow, havoids, hgrows, hefinal, hsched⟩ :=
        ih (last + gap) (S \ pairFootprint chosen gap) (stages ++ [stage]) htrace' hcap' hlast' hshift'
      refine ⟨final, actualFinal, stage :: extra, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hefinal, ?_⟩
      · simpa [stage, List.append_assoc] using hfinal
      · simpa using Nat.succ_le_succ hlen
      · exact hfinalSub.trans Finset.sdiff_subset
      · change final.card + (2 * (6 * (n + 8))) * (extra.length + 1) = S.card
        rw [Nat.mul_add, Nat.mul_one]
        omega
      · simpa [List.append_assoc] using hfinalStock
      · rcases hstop with hs | hs
        · exact Or.inl hs
        · right; simpa using congrArg Nat.succ hs
      · intro s hs p hp q hq
        rcases List.mem_cons.mp hs with rfl | hs
        · simpa [stage] using hmid p hp q hq
        · exact hnarrow s hs p hp q hq
      · intro s hs
        rcases List.mem_cons.mp hs with rfl | hs
        · simpa [stage, BTSelectedStage.footprint] using hdisj
        · exact havoids s hs
      · omega
      · have hrest : FWFullStockSchedule i n (stages.length + 1) (last + stage.gap) actualFinal extra := by
          simpa only [List.length_append, List.length_cons, List.length_nil, Nat.add_zero] using hsched
        exact FWFullStockSchedule.cons stages.length last actualFinal stage extra hj hnotdone hshift
          rfl hgap hdiv hstrong hplus hmax hrest

end
end Sude
