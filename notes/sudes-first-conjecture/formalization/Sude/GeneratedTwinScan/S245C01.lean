import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S245C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22670)) 513933357 513966125 = 112 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 513933357 513966125).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22670 513933357 513966125
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22671)) 513966125 513998893 = 119 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 513966125 513998893).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22671 513966125 513998893
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22672)) 513998893 514031661 = 106 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 513998893 514031661).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22672 513998893 514031661
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22672)) 514031661 514064429 = 93 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 514031661 514064429).card = 93 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22672 514031661 514064429
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 513933357 513998893).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 513933357 ≤ 513966125)
    (by decide : 513966125 ≤ 513998893) block0 block1

theorem join_0_1 : (twinPrimeSegment 513998893 514064429).card = 199 := by
  simpa using combineTwinPrimeSegments (by decide : 513998893 ≤ 514031661)
    (by decide : 514031661 ≤ 514064429) block2 block3

theorem join_1_0 : (twinPrimeSegment 513933357 514064429).card = 430 := by
  simpa using combineTwinPrimeSegments (by decide : 513933357 ≤ 513998893)
    (by decide : 513998893 ≤ 514064429) join_0_0 join_0_1

theorem total : (twinPrimeSegment 513933357 514064429).card = 430 := join_1_0

end S245C01
end Sude.GeneratedTwinScan
