import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S172C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19027)) 362020909 362053677 = 116 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 362020909 362053677).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19027 362020909 362053677
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19028)) 362053677 362086445 = 119 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 362053677 362086445).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19028 362053677 362086445
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19029)) 362086445 362119213 = 118 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 362086445 362119213).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19029 362086445 362119213
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19030)) 362119213 362151981 = 113 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 362119213 362151981).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19030 362119213 362151981
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 362020909 362086445).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 362020909 ≤ 362053677)
    (by decide : 362053677 ≤ 362086445) block0 block1

theorem join_0_1 : (twinPrimeSegment 362086445 362151981).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 362086445 ≤ 362119213)
    (by decide : 362119213 ≤ 362151981) block2 block3

theorem join_1_0 : (twinPrimeSegment 362020909 362151981).card = 466 := by
  simpa using combineTwinPrimeSegments (by decide : 362020909 ≤ 362086445)
    (by decide : 362086445 ≤ 362151981) join_0_0 join_0_1

theorem total : (twinPrimeSegment 362020909 362151981).card = 466 := join_1_0

end S172C10
end Sude.GeneratedTwinScan
