import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S077C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12770)) 163053613 163086381 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 163053613 163086381).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12770 163053613 163086381
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12771)) 163086381 163119149 = 140 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 163086381 163119149).card = 140 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12771 163086381 163119149
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12773)) 163119149 163151917 = 125 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 163119149 163151917).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12773 163119149 163151917
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12774)) 163151917 163184685 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 163151917 163184685).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12774 163151917 163184685
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 163053613 163119149).card = 253 := by
  simpa using combineTwinPrimeSegments (by decide : 163053613 ≤ 163086381)
    (by decide : 163086381 ≤ 163119149) block0 block1

theorem join_0_1 : (twinPrimeSegment 163119149 163184685).card = 244 := by
  simpa using combineTwinPrimeSegments (by decide : 163119149 ≤ 163151917)
    (by decide : 163151917 ≤ 163184685) block2 block3

theorem join_1_0 : (twinPrimeSegment 163053613 163184685).card = 497 := by
  simpa using combineTwinPrimeSegments (by decide : 163053613 ≤ 163119149)
    (by decide : 163119149 ≤ 163184685) join_0_0 join_0_1

theorem total : (twinPrimeSegment 163053613 163184685).card = 497 := join_1_0

end S077C12
end Sude.GeneratedTwinScan
