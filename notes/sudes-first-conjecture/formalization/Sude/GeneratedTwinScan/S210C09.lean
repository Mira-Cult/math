import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S210C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21014)) 441581613 441614381 = 109 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 441581613 441614381).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21014 441581613 441614381
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21015)) 441614381 441647149 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 441614381 441647149).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21015 441614381 441647149
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21016)) 441647149 441679917 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 441647149 441679917).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21016 441647149 441679917
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21016)) 441679917 441712685 = 87 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 441679917 441712685).card = 87 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21016 441679917 441712685
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 441581613 441647149).card = 220 := by
  simpa using combineTwinPrimeSegments (by decide : 441581613 ≤ 441614381)
    (by decide : 441614381 ≤ 441647149) block0 block1

theorem join_0_1 : (twinPrimeSegment 441647149 441712685).card = 201 := by
  simpa using combineTwinPrimeSegments (by decide : 441647149 ≤ 441679917)
    (by decide : 441679917 ≤ 441712685) block2 block3

theorem join_1_0 : (twinPrimeSegment 441581613 441712685).card = 421 := by
  simpa using combineTwinPrimeSegments (by decide : 441581613 ≤ 441647149)
    (by decide : 441647149 ≤ 441712685) join_0_0 join_0_1

theorem total : (twinPrimeSegment 441581613 441712685).card = 421 := join_1_0

end S210C09
end Sude.GeneratedTwinScan
