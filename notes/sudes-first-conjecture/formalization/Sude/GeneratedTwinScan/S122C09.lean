import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S122C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16033)) 257032237 257065005 = 118 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 257032237 257065005).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16033 257032237 257065005
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16034)) 257065005 257097773 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 257065005 257097773).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16034 257065005 257097773
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16035)) 257097773 257130541 = 119 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 257097773 257130541).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16035 257097773 257130541
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16036)) 257130541 257163309 = 121 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 257130541 257163309).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16036 257130541 257163309
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 257032237 257097773).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 257032237 ≤ 257065005)
    (by decide : 257065005 ≤ 257097773) block0 block1

theorem join_0_1 : (twinPrimeSegment 257097773 257163309).card = 240 := by
  simpa using combineTwinPrimeSegments (by decide : 257097773 ≤ 257130541)
    (by decide : 257130541 ≤ 257163309) block2 block3

theorem join_1_0 : (twinPrimeSegment 257032237 257163309).card = 470 := by
  simpa using combineTwinPrimeSegments (by decide : 257032237 ≤ 257097773)
    (by decide : 257097773 ≤ 257163309) join_0_0 join_0_1

theorem total : (twinPrimeSegment 257032237 257163309).card = 470 := join_1_0

end S122C09
end Sude.GeneratedTwinScan
