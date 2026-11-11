import Sude.FWWheelFirstBandActualStep

/-! A source-labeled record of the adaptive first-window iteration.
The record does not claim the mixed recipe or crossing before the cap. -/
namespace Sude
noncomputable section

/-- Pointwise WW5 real input at stage index j and actual radius R, using
our conservative first-band mass envelope. -/
def fwFirstWindowA (j R : ℕ) : ℝ :=
  (3981035 / 10000000 : ℝ) *
    ((403 / 10000 : ℝ) - 2 * (1 / 69780 : ℝ) * j) * R - 1 / 2

/-- Exact natural floor T and the WW5 lower gap cutoff. -/
def fwFirstWindowT (j R : ℕ) : ℕ := ⌊fwFirstWindowA j R⌋₊

def fwFirstWindowCutoff (j R : ℕ) : ℕ :=
  2 * min
    (fwWheelWindowCutoff (fwWheelUnit 15015) 15015 (Nat.totient 15015)
      (fwFirstWindowT j R) (Nat.totient_pos.mpr (by decide))) (R / 2)

/-- Each appended stage records its actual stage index, pre-step radius,
nonnegative floor input, exact T-derived cutoff as its stored minimum, even
selected gap at least that cutoff and at most the radius, and the exact
radius/index recurrence. X fixes the actual pre-crossing condition. -/
inductive FWFirstWindowSchedule (X : ℝ) : ℕ → ℕ → ℕ → List BTSelectedStage → Prop
  | nil (j R : ℕ) : FWFirstWindowSchedule X j R R []
  | cons (j R last : ℕ) (stage : BTSelectedStage) (tail : List BTSelectedStage)
      (hcap : j < 238) (hbefore : (R : ℝ) < X / 23)
      (hfloor : 0 ≤ fwFirstWindowA j R)
      (hminimum : stage.minimum = (fwFirstWindowCutoff j R : ℝ))
      (hpositive : 0 < stage.gap) (heven : 2 ∣ stage.gap)
      (hlower : fwFirstWindowCutoff j R ≤ stage.gap) (hupper : stage.gap ≤ R)
      (hrest : FWFirstWindowSchedule X (j + 1) (R + stage.gap) last tail) :
      FWFirstWindowSchedule X j R last (stage :: tail)

/-- Preserve the supplied prefix and record the exact first-window source
parameters and recurrence for every appended stage, stopping at crossing or
238. The source mixed recipe and crossing by the cap remain unproved. -/
theorem fw_first_band_trace_labeled_window_bounded_stop
    (bmor : BMORFinitePiFour) (lower : RSIndexLower) (upper : RSIndexUpper)
    (upperSharp : RSIndexUpperSharp) {n : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 21248)
    (batches : ℕ → List DoublePair) (hvalid : ∀ j < 5, FWBridgeSequentialValid n ∅ batches j)
    (candidates : Finset ℕ) (hcard : candidates.card = 17 * (6 * (n + 8)))
    (kept : Finset ℕ) (hsub : kept ⊆ Finset.range 17) (hkept : kept.card = 16)
    (hinj : Function.Injective (sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard))
    (blocks : List DoublePair)
    (hblocks : blocks.length = 3 * (n / 450) * (3 * (n + 8)))
    (last : ℕ) (final : Finset ℕ) (stages : List BTSelectedStage)
    (trace : BTGrowingTrace 2 (6 * (n + 8))
      (((poolFinset n).filter (fun p => 43 < p)) \
        fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks)
      32 final last stages) (hsteps : stages.length ≤ 238) :
    ∃ (final' : Finset ℕ) (last' : ℕ) (extra : List BTSelectedStage),
      BTGrowingTrace 2 (6 * (n + 8))
        (((poolFinset n).filter (fun p => 43 < p)) \
          fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks)
        32 final' last' (stages ++ extra) ∧
      (stages ++ extra).length ≤ 238 ∧
      ((poolMaximum n : ℝ) / 23 ≤ last' ∨ (stages ++ extra).length = 238) ∧
      NarrowedStages ((poolMaximum n : ℝ) / 6) extra ∧
      FWFirstWindowSchedule (poolMaximum n) stages.length last last' extra := by
  let initial := ((poolFinset n).filter (fun p => 43 < p)) \
    fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks
  have hrun : ∀ fuel : ℕ, ∀ (final : Finset ℕ) (last : ℕ) (stages : List BTSelectedStage),
      BTGrowingTrace 2 (6 * (n + 8)) initial 32 final last stages →
      stages.length + fuel = 238 →
      ∃ (final' : Finset ℕ) (last' : ℕ) (extra : List BTSelectedStage),
        BTGrowingTrace 2 (6 * (n + 8)) initial 32 final' last' (stages ++ extra) ∧
        (stages ++ extra).length ≤ 238 ∧
        ((poolMaximum n : ℝ) / 23 ≤ last' ∨ (stages ++ extra).length = 238) ∧
        NarrowedStages ((poolMaximum n : ℝ) / 6) extra ∧
        FWFirstWindowSchedule (poolMaximum n) stages.length last last' extra := by
    intro fuel
    induction fuel with
    | zero =>
      intro final last stages trace hlen
      refine ⟨final, last, [], ?_, ?_, ?_, ?_, FWFirstWindowSchedule.nil _ _⟩
      · simpa using trace
      · simpa using (show stages.length ≤ 238 by omega)
      · right
        simpa using (show stages.length = 238 by omega)
      · simp [NarrowedStages]
    | succ fuel ih =>
      intro final last stages trace hlen
      by_cases hdone : (poolMaximum n : ℝ) / 23 ≤ last
      · refine ⟨final, last, [], ?_, ?_, ?_, ?_, FWFirstWindowSchedule.nil _ _⟩
        · simpa using trace
        · simpa using (show stages.length ≤ 238 by omega)
        · exact Or.inl hdone
        · simp [NarrowedStages]
      · have hsteps' : stages.length < 238 := by omega
        have hnotdone : (last : ℝ) < (poolMaximum n : ℝ) / 23 := lt_of_not_ge hdone
        let m : ℝ := 403 / 10000 - 2 * (1 / 69780 : ℝ) * stages.length
        let T : ℕ := ⌊(3981035 / 10000000 : ℝ) * m * last - 1 / 2⌋₊
        let cutoff : ℕ := 2 * min
          (fwWheelWindowCutoff (fwWheelUnit 15015) 15015 (Nat.totient 15015) T
            (Nat.totient_pos.mpr (by decide))) (last / 2)
        obtain ⟨gap, chosen, hgap, hdiv, hcut, hmax, hcard', hpairs, hmatch, hfoot,
          hav, hsize, hdepl, hmid, hradius, htrace⟩ :=
          fw_first_band_trace_first_window_append_at_last bmor lower upper upperSharp hnlo hnhi
            batches hvalid candidates hcard kept hsub hkept hinj blocks hblocks last final stages
            (by simpa [initial] using trace) hsteps' hnotdone
        let stage : BTSelectedStage := ⟨gap, chosen, (cutoff : ℝ)⟩
        have htrace' : BTGrowingTrace 2 (6 * (n + 8)) initial 32
            (final \ pairFootprint chosen gap) (last + gap) (stages ++ [stage]) := by
          exact htrace
        have hlen' : (stages ++ [stage]).length + fuel = 238 := by simp; omega
        obtain ⟨final', last', extra, hfinal, hcap, hstop, hnarrow, hsched⟩ :=
          ih (final \ pairFootprint chosen gap) (last + gap) (stages ++ [stage]) htrace' hlen'
        refine ⟨final', last', stage :: extra, ?_, ?_, ?_, ?_, ?_⟩
        · simpa [List.append_assoc] using hfinal
        · simpa [List.append_assoc] using hcap
        · simpa [List.append_assoc] using hstop
        · intro s hs p hp q hq
          rcases List.mem_cons.mp hs with rfl | hs
          · simpa [stage] using hmid p hp q hq
          · exact hnarrow s hs p hp q hq
        · have hfloor := (fw_first_band_floor_of_even_trace trace hsteps').2
          have hfloor' : 0 ≤ fwFirstWindowA stages.length last := by
            exact hfloor
          have hcut' : fwFirstWindowCutoff stages.length last ≤ stage.gap := by
            exact hcut
          have hrest : FWFirstWindowSchedule (poolMaximum n) (stages.length + 1)
              (last + stage.gap) last' extra := by
            simpa only [List.length_append, List.length_cons, List.length_nil, Nat.add_zero] using hsched
          exact FWFirstWindowSchedule.cons stages.length last last' stage extra hsteps'
            hnotdone hfloor' rfl hgap hdiv hcut' hmax hrest
  have hstart : stages.length + (238 - stages.length) = 238 := by omega
  simpa [initial] using hrun (238 - stages.length) final last stages trace hstart

/-- Starting from the empty trace retains the labels for every constructed stage. -/
theorem fw_first_band_first_window_labeled_trace_bounded_stop
    (bmor : BMORFinitePiFour) (lower : RSIndexLower) (upper : RSIndexUpper)
    (upperSharp : RSIndexUpperSharp) {n : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 21248)
    (batches : ℕ → List DoublePair) (hvalid : ∀ j < 5, FWBridgeSequentialValid n ∅ batches j)
    (candidates : Finset ℕ) (hcard : candidates.card = 17 * (6 * (n + 8)))
    (kept : Finset ℕ) (hsub : kept ⊆ Finset.range 17) (hkept : kept.card = 16)
    (hinj : Function.Injective (sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard))
    (blocks : List DoublePair)
    (hblocks : blocks.length = 3 * (n / 450) * (3 * (n + 8))) :
    let initial := ((poolFinset n).filter (fun p => 43 < p)) \
      fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks
    ∃ (final : Finset ℕ) (last : ℕ) (stages : List BTSelectedStage),
      BTGrowingTrace 2 (6 * (n + 8)) initial 32 final last stages ∧
      stages.length ≤ 238 ∧
      ((poolMaximum n : ℝ) / 23 ≤ last ∨ stages.length = 238) ∧
      NarrowedStages ((poolMaximum n : ℝ) / 6) stages ∧
      FWFirstWindowSchedule (poolMaximum n) 0 32 last stages := by
  dsimp only
  let initial := ((poolFinset n).filter (fun p => 43 < p)) \
    fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks
  obtain ⟨final, last, extra, htrace, hcap, hstop, hnarrow, hsched⟩ :=
    fw_first_band_trace_labeled_window_bounded_stop bmor lower upper upperSharp hnlo hnhi
      batches hvalid candidates hcard kept hsub hkept hinj blocks hblocks 32 initial []
      (BTGrowingTrace.nil _ _) (by simp)
  exact ⟨final, last, extra, by simpa [initial] using htrace,
    by simpa using hcap, by simpa using hstop, hnarrow, by simpa using hsched⟩


end
end Sude
