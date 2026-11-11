import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S179C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19392)) 376045613 376078381 = 114 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 376045613 376078381).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19392 376045613 376078381
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19393)) 376078381 376111149 = 122 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 376078381 376111149).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19393 376078381 376111149
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19394)) 376111149 376143917 = 94 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 376111149 376143917).card = 94 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19394 376111149 376143917
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19395)) 376143917 376176685 = 102 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 376143917 376176685).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19395 376143917 376176685
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 376045613 376111149).card = 236 := by
  simpa using combineTwinPrimeSegments (by decide : 376045613 ≤ 376078381)
    (by decide : 376078381 ≤ 376111149) block0 block1

theorem join_0_1 : (twinPrimeSegment 376111149 376176685).card = 196 := by
  simpa using combineTwinPrimeSegments (by decide : 376111149 ≤ 376143917)
    (by decide : 376143917 ≤ 376176685) block2 block3

theorem join_1_0 : (twinPrimeSegment 376045613 376176685).card = 432 := by
  simpa using combineTwinPrimeSegments (by decide : 376045613 ≤ 376111149)
    (by decide : 376111149 ≤ 376176685) join_0_0 join_0_1

theorem total : (twinPrimeSegment 376045613 376176685).card = 432 := join_1_0

end S179C05
end Sude.GeneratedTwinScan
