import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S152C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17891)) 320077869 320110637 = 106 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 320077869 320110637).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17891 320077869 320110637
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17892)) 320110637 320143405 = 125 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 320110637 320143405).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17892 320110637 320143405
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17893)) 320143405 320176173 = 101 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 320143405 320176173).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17893 320143405 320176173
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17894)) 320176173 320208941 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 320176173 320208941).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17894 320176173 320208941
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 320077869 320143405).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 320077869 ≤ 320110637)
    (by decide : 320110637 ≤ 320143405) block0 block1

theorem join_0_1 : (twinPrimeSegment 320143405 320208941).card = 220 := by
  simpa using combineTwinPrimeSegments (by decide : 320143405 ≤ 320176173)
    (by decide : 320176173 ≤ 320208941) block2 block3

theorem join_1_0 : (twinPrimeSegment 320077869 320208941).card = 451 := by
  simpa using combineTwinPrimeSegments (by decide : 320077869 ≤ 320143405)
    (by decide : 320143405 ≤ 320208941) join_0_0 join_0_1

theorem total : (twinPrimeSegment 320077869 320208941).card = 451 := join_1_0

end S152C10
end Sude.GeneratedTwinScan
