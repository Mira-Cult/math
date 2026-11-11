import Sude.FWEighthAffinePhase

/-! Conditional first-band composition from an empty trace. Actual crossing
may stop any phase; otherwise all eight fixed-mass affine schedules exhaust
their fuel. This does not discharge the BT gate or prove physical placement. -/
namespace Sude
noncomputable section

/-- Narrowing is preserved when selected-stage lists are appended. -/
theorem narrowed_append {width : ℝ} {a b : List BTSelectedStage}
    (ha : NarrowedStages width a) (hb : NarrowedStages width b) :
    NarrowedStages width (a ++ b) := by
  intro stage hs
  rcases List.mem_append.mp hs with ha' | hb'
  · exact ha stage ha'
  · exact hb stage hb'

/-- A completed first-window and eight-wheel fixed-mass certificate with
linked actual and certified radii. This does not assert crossing. -/
inductive FWCompletedAffinePhases (n : ℕ) : ℕ → List BTSelectedStage → Prop
  | mk (R0 last0 R1 last1 R2 last2 R3 last3 R4 last4 R5 last5 R6 last6 R7 last7 R8 last8 : ℕ)
      (window first second third fourth fifth sixth seventh eighth : List BTSelectedStage)
      (hwindow : FWFirstWindowCertifiedSchedule (poolMaximum n) 0 32 32 R0 last0 window)
      (hwindowlen : window.length = 118)
      (hfirst : FWMixedAffineCertifiedSchedule 0 n 23
        ((3257 / 100000 : ℝ) * (poolMaximum n : ℝ))
        ((3257 / 100000 : ℝ) * (poolMaximum n : ℝ))
        (3981035 / 10000000) R0 last0 R1 last1 first)
      (hfirstlen : first.length = 6)
      (hsecond : FWMixedAffineCertifiedSchedule 1 n 23
        ((3257 / 100000 : ℝ) * (poolMaximum n : ℝ))
        ((3257 / 100000 : ℝ) * (poolMaximum n : ℝ))
        (3981035 / 10000000) R1 last1 R2 last2 second)
      (hsecondlen : second.length = 11)
      (hthird : FWMixedAffineCertifiedSchedule 2 n 23
        ((3257 / 100000 : ℝ) * (poolMaximum n : ℝ))
        ((3257 / 100000 : ℝ) * (poolMaximum n : ℝ))
        (3981035 / 10000000) R2 last2 R3 last3 third)
      (hthirdlen : third.length = 12)
      (hfourth : FWMixedAffineCertifiedSchedule 3 n 23
        ((3257 / 100000 : ℝ) * (poolMaximum n : ℝ))
        ((3257 / 100000 : ℝ) * (poolMaximum n : ℝ))
        (3981035 / 10000000) R3 last3 R4 last4 fourth)
      (hfourthlen : fourth.length = 9)
      (hfifth : FWMixedAffineCertifiedSchedule 4 n 23
        ((3257 / 100000 : ℝ) * (poolMaximum n : ℝ))
        ((3257 / 100000 : ℝ) * (poolMaximum n : ℝ))
        (3981035 / 10000000) R4 last4 R5 last5 fifth)
      (hfifthlen : fifth.length = 10)
      (hsixth : FWMixedAffineCertifiedSchedule 5 n 23
        ((3257 / 100000 : ℝ) * (poolMaximum n : ℝ))
        ((3257 / 100000 : ℝ) * (poolMaximum n : ℝ))
        (3981035 / 10000000) R5 last5 R6 last6 sixth)
      (hsixthlen : sixth.length = 10)
      (hseventh : FWMixedAffineCertifiedSchedule 6 n 23
        ((3257 / 100000 : ℝ) * (poolMaximum n : ℝ))
        ((3257 / 100000 : ℝ) * (poolMaximum n : ℝ))
        (3981035 / 10000000) R6 last6 R7 last7 seventh)
      (hseventhlen : seventh.length = 8)
      (heighth : FWMixedAffineCertifiedSchedule 7 n 23
        ((3257 / 100000 : ℝ) * (poolMaximum n : ℝ))
        ((3257 / 100000 : ℝ) * (poolMaximum n : ℝ))
        (3981035 / 10000000) R7 last7 R8 last8 eighth)
      (heighthlen : eighth.length = 44)
      : FWCompletedAffinePhases n last8 ((((((((window ++ first) ++ second) ++ third) ++ fourth) ++ fifth) ++ sixth) ++ seventh) ++ eighth)

/-- Construct the first-window and affine trace up to actual crossing or the
228-stage fuel cap, preserving the linked phase schedules at the cap. -/
theorem fw_first_band_stop_or_228
    (bmor : BMORFinitePiFour) (lower : RSIndexLower) (upper : RSIndexUpper)
    (upperSharp : RSIndexUpperSharp) {n : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 21248)
    (batches : ℕ → List DoublePair) (hvalid : ∀ j < 5, FWBridgeSequentialValid n ∅ batches j)
    (candidates : Finset ℕ) (hcard : candidates.card = 17 * (6 * (n + 8)))
    (kept : Finset ℕ) (hsub : kept ⊆ Finset.range 17) (hkept : kept.card = 16)
    (hinj : Function.Injective (sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard))
    (blocks : List DoublePair) (hblocks : blocks.length = 3 * (n / 450) * (3 * (n + 8))) :
    ∃ (final : Finset ℕ) (last : ℕ) (stages : List BTSelectedStage),
      BTGrowingTrace 2 (6 * (n + 8))
        (((poolFinset n).filter (fun p => 43 < p)) \
          fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks)
        32 final last stages ∧
      NarrowedStages ((poolMaximum n : ℝ) / 6) stages ∧
      stages.length ≤ 228 ∧
      ((poolMaximum n : ℝ) / 23 ≤ last ∨
        (FWCompletedAffinePhases n last stages ∧ stages.length = 228)) := by
  let initial := ((poolFinset n).filter (fun p => 43 < p)) \
    fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks
  obtain ⟨S0, R0, last0, window, htrace0, hlen0, hstop0, hnarrow0, _, _, _, hsched0⟩ :=
    fw_first_band_certified_first_window_bounded_stop bmor lower upper upperSharp hnlo hnhi
      batches hvalid candidates hcard kept hsub hkept hinj blocks hblocks 32 32 initial []
      (BTGrowingTrace.nil _ _) (by simp) (by simp) (by norm_num) (by simp)
  simp only [List.nil_append, List.length_nil] at htrace0 hlen0 hstop0 hsched0
  change BTGrowingTrace 2 (6 * (n + 8)) (((poolFinset n).filter (fun p => 43 < p)) \
    fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks) 32 S0 last0 window at htrace0
  rcases hstop0 with hcross0 | hfull0
  · exact ⟨S0, last0, window, htrace0, hnarrow0, by omega, Or.inl hcross0⟩
  obtain ⟨S1, R1, last1, first, htrace1, hlen1, _, _, hstop1, _, hnarrow1, _, _, _, hsched1⟩ :=
    fw_first_affine_phase_from_118 bmor lower upper upperSharp hnlo hnhi
      batches hvalid candidates hcard kept hsub hkept hinj blocks hblocks R0 last0 S0 window htrace0 hsched0 hfull0
  have hn1 : NarrowedStages ((poolMaximum n : ℝ) / 6) (window ++ first) := narrowed_append hnarrow0 hnarrow1
  rcases hstop1 with hcross1 | hfull1
  · refine ⟨S1, last1, (window ++ first), htrace1, hn1, ?_, Or.inl hcross1⟩
    simp only [List.length_append]
    omega
  obtain ⟨S2, R2, last2, second, htrace2, hlen2, _, _, hstop2, _, hnarrow2, _, _, _, hsched2⟩ :=
    fw_second_affine_phase_after_first bmor lower upper upperSharp hnlo hnhi
      batches hvalid candidates hcard kept hsub hkept hinj blocks hblocks R0 last0 R1 last1 S1 window first hsched0 hfull0 hsched1 hfull1 htrace1
  have hn2 : NarrowedStages ((poolMaximum n : ℝ) / 6) ((window ++ first) ++ second) := narrowed_append hn1 hnarrow2
  rcases hstop2 with hcross2 | hfull2
  · refine ⟨S2, last2, ((window ++ first) ++ second), htrace2, hn2, ?_, Or.inl hcross2⟩
    simp only [List.length_append]
    omega
  obtain ⟨S3, R3, last3, third, htrace3, hlen3, _, _, hstop3, _, hnarrow3, _, _, _, hsched3⟩ :=
    fw_third_affine_phase_after_second bmor lower upper upperSharp hnlo hnhi
      batches hvalid candidates hcard kept hsub hkept hinj blocks hblocks R0 last0 R1 last1 R2 last2 S2 window first second hsched0 hfull0 hsched1 hfull1 hsched2 hfull2 htrace2
  have hn3 : NarrowedStages ((poolMaximum n : ℝ) / 6) (((window ++ first) ++ second) ++ third) := narrowed_append hn2 hnarrow3
  rcases hstop3 with hcross3 | hfull3
  · refine ⟨S3, last3, (((window ++ first) ++ second) ++ third), htrace3, hn3, ?_, Or.inl hcross3⟩
    simp only [List.length_append]
    omega
  obtain ⟨S4, R4, last4, fourth, htrace4, hlen4, _, _, hstop4, _, hnarrow4, _, _, _, hsched4⟩ :=
    fw_fourth_affine_phase_after_third bmor lower upper upperSharp hnlo hnhi
      batches hvalid candidates hcard kept hsub hkept hinj blocks hblocks R0 last0 R1 last1 R2 last2 R3 last3 S3 window first second third hsched0 hfull0 hsched1 hfull1 hsched2 hfull2 hsched3 hfull3 htrace3
  have hn4 : NarrowedStages ((poolMaximum n : ℝ) / 6) ((((window ++ first) ++ second) ++ third) ++ fourth) := narrowed_append hn3 hnarrow4
  rcases hstop4 with hcross4 | hfull4
  · refine ⟨S4, last4, ((((window ++ first) ++ second) ++ third) ++ fourth), htrace4, hn4, ?_, Or.inl hcross4⟩
    simp only [List.length_append]
    omega
  obtain ⟨S5, R5, last5, fifth, htrace5, hlen5, _, _, hstop5, _, hnarrow5, _, _, _, hsched5⟩ :=
    fw_fifth_affine_phase_after_fourth bmor lower upper upperSharp hnlo hnhi
      batches hvalid candidates hcard kept hsub hkept hinj blocks hblocks R0 last0 R1 last1 R2 last2 R3 last3 R4 last4 S4 window first second third fourth hsched0 hfull0 hsched1 hfull1 hsched2 hfull2 hsched3 hfull3 hsched4 hfull4 htrace4
  have hn5 : NarrowedStages ((poolMaximum n : ℝ) / 6) (((((window ++ first) ++ second) ++ third) ++ fourth) ++ fifth) := narrowed_append hn4 hnarrow5
  rcases hstop5 with hcross5 | hfull5
  · refine ⟨S5, last5, (((((window ++ first) ++ second) ++ third) ++ fourth) ++ fifth), htrace5, hn5, ?_, Or.inl hcross5⟩
    simp only [List.length_append]
    omega
  obtain ⟨S6, R6, last6, sixth, htrace6, hlen6, _, _, hstop6, _, hnarrow6, _, _, _, hsched6⟩ :=
    fw_sixth_affine_phase_after_fifth bmor lower upper upperSharp hnlo hnhi
      batches hvalid candidates hcard kept hsub hkept hinj blocks hblocks R0 last0 R1 last1 R2 last2 R3 last3 R4 last4 R5 last5 S5 window first second third fourth fifth hsched0 hfull0 hsched1 hfull1 hsched2 hfull2 hsched3 hfull3 hsched4 hfull4 hsched5 hfull5 htrace5
  have hn6 : NarrowedStages ((poolMaximum n : ℝ) / 6) ((((((window ++ first) ++ second) ++ third) ++ fourth) ++ fifth) ++ sixth) := narrowed_append hn5 hnarrow6
  rcases hstop6 with hcross6 | hfull6
  · refine ⟨S6, last6, ((((((window ++ first) ++ second) ++ third) ++ fourth) ++ fifth) ++ sixth), htrace6, hn6, ?_, Or.inl hcross6⟩
    simp only [List.length_append]
    omega
  obtain ⟨S7, R7, last7, seventh, htrace7, hlen7, _, _, hstop7, _, hnarrow7, _, _, _, hsched7⟩ :=
    fw_seventh_affine_phase_after_sixth bmor lower upper upperSharp hnlo hnhi
      batches hvalid candidates hcard kept hsub hkept hinj blocks hblocks R0 last0 R1 last1 R2 last2 R3 last3 R4 last4 R5 last5 R6 last6 S6 window first second third fourth fifth sixth hsched0 hfull0 hsched1 hfull1 hsched2 hfull2 hsched3 hfull3 hsched4 hfull4 hsched5 hfull5 hsched6 hfull6 htrace6
  have hn7 : NarrowedStages ((poolMaximum n : ℝ) / 6) (((((((window ++ first) ++ second) ++ third) ++ fourth) ++ fifth) ++ sixth) ++ seventh) := narrowed_append hn6 hnarrow7
  rcases hstop7 with hcross7 | hfull7
  · refine ⟨S7, last7, (((((((window ++ first) ++ second) ++ third) ++ fourth) ++ fifth) ++ sixth) ++ seventh), htrace7, hn7, ?_, Or.inl hcross7⟩
    simp only [List.length_append]
    omega
  obtain ⟨S8, R8, last8, eighth, htrace8, hlen8, _, _, hstop8, _, hnarrow8, _, _, _, hsched8⟩ :=
    fw_eighth_affine_phase_after_seventh bmor lower upper upperSharp hnlo hnhi
      batches hvalid candidates hcard kept hsub hkept hinj blocks hblocks R0 last0 R1 last1 R2 last2 R3 last3 R4 last4 R5 last5 R6 last6 R7 last7 S7 window first second third fourth fifth sixth seventh hsched0 hfull0 hsched1 hfull1 hsched2 hfull2 hsched3 hfull3 hsched4 hfull4 hsched5 hfull5 hsched6 hfull6 hsched7 hfull7 htrace7
  have hn8 : NarrowedStages ((poolMaximum n : ℝ) / 6) ((((((((window ++ first) ++ second) ++ third) ++ fourth) ++ fifth) ++ sixth) ++ seventh) ++ eighth) := narrowed_append hn7 hnarrow8
  rcases hstop8 with hcross8 | hfull8
  · refine ⟨S8, last8, ((((((((window ++ first) ++ second) ++ third) ++ fourth) ++ fifth) ++ sixth) ++ seventh) ++ eighth), htrace8, hn8, ?_, Or.inl hcross8⟩
    simp only [List.length_append]
    omega
  · refine ⟨S8, last8, ((((((((window ++ first) ++ second) ++ third) ++ fourth) ++ fifth) ++ sixth) ++ seventh) ++ eighth), htrace8, hn8, ?_, Or.inr ⟨?_, ?_⟩⟩
    · simp only [List.length_append]; omega
    · exact FWCompletedAffinePhases.mk R0 last0 R1 last1 R2 last2 R3 last3 R4 last4 R5 last5 R6 last6 R7 last7 R8 last8 window first second third fourth fifth sixth seventh eighth hsched0 hfull0 hsched1 hfull1 hsched2 hfull2 hsched3 hfull3 hsched4 hfull4 hsched5 hfull5 hsched6 hfull6 hsched7 hfull7 hsched8 hfull8
    · simp only [List.length_append]; omega

end
end Sude
