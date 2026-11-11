import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S106C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14954)) 223608877 223641645 = 126 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 223608877 223641645).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14954 223608877 223641645
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14955)) 223641645 223674413 = 120 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 223641645 223674413).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14955 223641645 223674413
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14956)) 223674413 223707181 = 121 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 223674413 223707181).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14956 223674413 223707181
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14957)) 223707181 223739949 = 131 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 223707181 223739949).card = 131 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14957 223707181 223739949
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 223608877 223674413).card = 246 := by
  simpa using combineTwinPrimeSegments (by decide : 223608877 ≤ 223641645)
    (by decide : 223641645 ≤ 223674413) block0 block1

theorem join_0_1 : (twinPrimeSegment 223674413 223739949).card = 252 := by
  simpa using combineTwinPrimeSegments (by decide : 223674413 ≤ 223707181)
    (by decide : 223707181 ≤ 223739949) block2 block3

theorem join_1_0 : (twinPrimeSegment 223608877 223739949).card = 498 := by
  simpa using combineTwinPrimeSegments (by decide : 223608877 ≤ 223674413)
    (by decide : 223674413 ≤ 223739949) join_0_0 join_0_1

theorem total : (twinPrimeSegment 223608877 223739949).card = 498 := join_1_0

end S106C10
end Sude.GeneratedTwinScan
