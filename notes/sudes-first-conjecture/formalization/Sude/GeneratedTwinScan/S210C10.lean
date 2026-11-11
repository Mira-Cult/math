import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S210C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21017)) 441712685 441745453 = 116 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 441712685 441745453).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21017 441712685 441745453
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21018)) 441745453 441778221 = 96 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 441745453 441778221).card = 96 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21018 441745453 441778221
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21019)) 441778221 441810989 = 89 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 441778221 441810989).card = 89 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21019 441778221 441810989
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21020)) 441810989 441843757 = 127 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 441810989 441843757).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21020 441810989 441843757
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 441712685 441778221).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 441712685 ≤ 441745453)
    (by decide : 441745453 ≤ 441778221) block0 block1

theorem join_0_1 : (twinPrimeSegment 441778221 441843757).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 441778221 ≤ 441810989)
    (by decide : 441810989 ≤ 441843757) block2 block3

theorem join_1_0 : (twinPrimeSegment 441712685 441843757).card = 428 := by
  simpa using combineTwinPrimeSegments (by decide : 441712685 ≤ 441778221)
    (by decide : 441778221 ≤ 441843757) join_0_0 join_0_1

theorem total : (twinPrimeSegment 441712685 441843757).card = 428 := join_1_0

end S210C10
end Sude.GeneratedTwinScan
