import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S089C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13677)) 187039789 187072557 = 132 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 187039789 187072557).card = 132 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13677 187039789 187072557
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13678)) 187072557 187105325 = 121 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 187072557 187105325).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13678 187072557 187105325
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13679)) 187105325 187138093 = 121 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 187105325 187138093).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13679 187105325 187138093
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13681)) 187138093 187170861 = 120 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 187138093 187170861).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13681 187138093 187170861
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 187039789 187105325).card = 253 := by
  simpa using combineTwinPrimeSegments (by decide : 187039789 ≤ 187072557)
    (by decide : 187072557 ≤ 187105325) block0 block1

theorem join_0_1 : (twinPrimeSegment 187105325 187170861).card = 241 := by
  simpa using combineTwinPrimeSegments (by decide : 187105325 ≤ 187138093)
    (by decide : 187138093 ≤ 187170861) block2 block3

theorem join_1_0 : (twinPrimeSegment 187039789 187170861).card = 494 := by
  simpa using combineTwinPrimeSegments (by decide : 187039789 ≤ 187105325)
    (by decide : 187105325 ≤ 187170861) join_0_0 join_0_1

theorem total : (twinPrimeSegment 187039789 187170861).card = 494 := join_1_0

end S089C03
end Sude.GeneratedTwinScan
