import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S084C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13323)) 177471533 177504301 = 133 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 177471533 177504301).card = 133 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13323 177471533 177504301
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13324)) 177504301 177537069 = 141 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 177504301 177537069).card = 141 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13324 177504301 177537069
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13325)) 177537069 177569837 = 119 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 177537069 177569837).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13325 177537069 177569837
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13326)) 177569837 177602605 = 121 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 177569837 177602605).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13326 177569837 177602605
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 177471533 177537069).card = 274 := by
  simpa using combineTwinPrimeSegments (by decide : 177471533 ≤ 177504301)
    (by decide : 177504301 ≤ 177537069) block0 block1

theorem join_0_1 : (twinPrimeSegment 177537069 177602605).card = 240 := by
  simpa using combineTwinPrimeSegments (by decide : 177537069 ≤ 177569837)
    (by decide : 177569837 ≤ 177602605) block2 block3

theorem join_1_0 : (twinPrimeSegment 177471533 177602605).card = 514 := by
  simpa using combineTwinPrimeSegments (by decide : 177471533 ≤ 177537069)
    (by decide : 177537069 ≤ 177602605) join_0_0 join_0_1

theorem total : (twinPrimeSegment 177471533 177602605).card = 514 := join_1_0

end S084C10
end Sude.GeneratedTwinScan
