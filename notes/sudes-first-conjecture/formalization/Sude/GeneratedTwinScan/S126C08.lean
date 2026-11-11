import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S126C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16288)) 265289773 265322541 = 107 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 265289773 265322541).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16288 265289773 265322541
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16289)) 265322541 265355309 = 138 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 265322541 265355309).card = 138 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16289 265322541 265355309
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16290)) 265355309 265388077 = 128 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 265355309 265388077).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16290 265355309 265388077
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16291)) 265388077 265420845 = 121 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 265388077 265420845).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16291 265388077 265420845
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 265289773 265355309).card = 245 := by
  simpa using combineTwinPrimeSegments (by decide : 265289773 ≤ 265322541)
    (by decide : 265322541 ≤ 265355309) block0 block1

theorem join_0_1 : (twinPrimeSegment 265355309 265420845).card = 249 := by
  simpa using combineTwinPrimeSegments (by decide : 265355309 ≤ 265388077)
    (by decide : 265388077 ≤ 265420845) block2 block3

theorem join_1_0 : (twinPrimeSegment 265289773 265420845).card = 494 := by
  simpa using combineTwinPrimeSegments (by decide : 265289773 ≤ 265355309)
    (by decide : 265355309 ≤ 265420845) join_0_0 join_0_1

theorem total : (twinPrimeSegment 265289773 265420845).card = 494 := join_1_0

end S126C08
end Sude.GeneratedTwinScan
