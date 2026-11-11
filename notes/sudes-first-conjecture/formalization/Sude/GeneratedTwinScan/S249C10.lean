import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S249C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22880)) 523501613 523534381 = 116 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 523501613 523534381).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22880 523501613 523534381
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22881)) 523534381 523567149 = 109 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 523534381 523567149).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22881 523534381 523567149
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22882)) 523567149 523599917 = 92 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 523567149 523599917).card = 92 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22882 523567149 523599917
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22883)) 523599917 523632685 = 101 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 523599917 523632685).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22883 523599917 523632685
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 523501613 523567149).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 523501613 ≤ 523534381)
    (by decide : 523534381 ≤ 523567149) block0 block1

theorem join_0_1 : (twinPrimeSegment 523567149 523632685).card = 193 := by
  simpa using combineTwinPrimeSegments (by decide : 523567149 ≤ 523599917)
    (by decide : 523599917 ≤ 523632685) block2 block3

theorem join_1_0 : (twinPrimeSegment 523501613 523632685).card = 418 := by
  simpa using combineTwinPrimeSegments (by decide : 523501613 ≤ 523567149)
    (by decide : 523567149 ≤ 523632685) join_0_0 join_0_1

theorem total : (twinPrimeSegment 523501613 523632685).card = 418 := join_1_0

end S249C10
end Sude.GeneratedTwinScan
