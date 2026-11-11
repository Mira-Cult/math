import Sude.FWEnhancedBT16TenStages
import Sude.FWBT16WidthCompare
import Sude.FWBT16TraceGrowth

/-! Conditional first-band crossing for the same screened early witnesses.
Montgomery--Vaughan and the named BMOR/RS bounds remain explicit. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 800000

/-- The selected trace reaches X/23 within 238 stages: it either crosses
before the BT continuation, or ten actual-width BT stages force crossing.
The result concerns the screened trace, not physical installation or line sums. -/
theorem fw_enhanced_from_seed_bt16_crossing
    (mv : MVBrunTitchmarsh)
    (bmor : BMORFinitePiFour) (lower : RSIndexLower) (upper : RSIndexUpper)
    (upperSharp : RSIndexUpperSharp) {n : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 21248)
    (batches : ℕ → List DoublePair) (hvalid : ∀ j < 5, FWBridgeSequentialValid n ∅ batches j)
    (candidates : Finset ℕ) (hcard : candidates.card = 17 * (6 * (n + 8)))
    (kept : Finset ℕ) (hsub : kept ⊆ Finset.range 17) (hkept : kept.card = 16)
    (hinj : Function.Injective (sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard))
    (blocks : List DoublePair) (hblocks : blocks.length = 3 * (n / 450) * (3 * (n + 8))) :
    let initial := ((poolFinset n).filter (fun p => 43 < p)) \
      fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks
    ∃ (final : Finset ℕ) (last : ℕ) (stages : List BTSelectedStage),
      BTGrowingTrace 2 (6 * (n + 8)) initial 32 final last stages ∧
      stages.length ≤ 238 ∧
      final ⊆ initial ∧
      final.card + 2 * (6 * (n + 8)) * stages.length = initial.card ∧
      stages.Pairwise (fun x y => Disjoint x.footprint y.footprint) ∧
      NarrowedStages ((poolMaximum n : ℝ) / 6) stages ∧
      (∀ stage ∈ stages, Disjoint stage.footprint
        (fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks)) ∧
      (poolMaximum n : ℝ) / 23 ≤ last := by
  dsimp only
  obtain ⟨stock, last, stages, trace, hcap, hsubstock, hcardstock, hnarrow, havoid, hstop⟩ :=
    fw_enhanced_from_seed_stop_or_ten_bt16 mv bmor lower upper upperSharp hnlo hnhi
      batches hvalid candidates hcard kept hsub hkept hinj blocks hblocks
  rcases hstop with hcross | ⟨hcomplete, hlen, hlast, hstock, final, last', extra,
    htrace, hsuffix, hextralen, htotal, hstop, hwidth, hnarrowExtra,
    hfinalsub, hfinalcard, hpairwise, havoidExtra⟩
  · exact ⟨stock, last, stages, trace, by omega, hsubstock, hcardstock,
      trace.pairwise_disjoint, hnarrow, havoid, hcross⟩
  · have hcross : (poolMaximum n : ℝ) / 23 ≤ last' := by
      rcases hstop with hcross | hten
      · exact hcross
      · have hfixed := fw_bt16_varying_width_trace_fixed (by exact hwidth)
          (by omega : stages.length + extra.length ≤ 239) 0
        exact (fw_bt16_ten_width_stages_cross upperSharp hnlo hnhi hsuffix hfixed hlast hten).le
    refine ⟨final, last', stages ++ extra, htrace, ?_, htrace.final_accounting.1,
      htrace.final_accounting.2.1, hpairwise, narrowed_append hnarrow hnarrowExtra, ?_, hcross⟩
    · simpa using htotal
    · intro stage hs
      rcases List.mem_append.mp hs with hs | hs
      · exact havoid stage hs
      · exact havoidExtra stage hs

end
end Sude
