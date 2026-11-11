import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S166C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18666)) 348389421 348422189 = 106 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 348389421 348422189).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18666 348389421 348422189
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18666)) 348422189 348454957 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 348422189 348454957).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18666 348422189 348454957
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18667)) 348454957 348487725 = 118 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 348454957 348487725).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18667 348454957 348487725
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18668)) 348487725 348520493 = 105 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 348487725 348520493).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18668 348487725 348520493
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 348389421 348454957).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 348389421 ≤ 348422189)
    (by decide : 348422189 ≤ 348454957) block0 block1

theorem join_0_1 : (twinPrimeSegment 348454957 348520493).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 348454957 ≤ 348487725)
    (by decide : 348487725 ≤ 348520493) block2 block3

theorem join_1_0 : (twinPrimeSegment 348389421 348520493).card = 437 := by
  simpa using combineTwinPrimeSegments (by decide : 348389421 ≤ 348454957)
    (by decide : 348454957 ≤ 348520493) join_0_0 join_0_1

theorem total : (twinPrimeSegment 348389421 348520493).card = 437 := join_1_0

end S166C02
end Sude.GeneratedTwinScan
