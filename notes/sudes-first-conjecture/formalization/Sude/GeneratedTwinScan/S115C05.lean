import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S115C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15551)) 241827885 241860653 = 112 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 241827885 241860653).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15551 241827885 241860653
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15552)) 241860653 241893421 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 241860653 241893421).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15552 241860653 241893421
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15553)) 241893421 241926189 = 132 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 241893421 241926189).card = 132 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15553 241893421 241926189
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15555)) 241926189 241958957 = 126 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 241926189 241958957).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15555 241926189 241958957
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 241827885 241893421).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 241827885 ≤ 241860653)
    (by decide : 241860653 ≤ 241893421) block0 block1

theorem join_0_1 : (twinPrimeSegment 241893421 241958957).card = 258 := by
  simpa using combineTwinPrimeSegments (by decide : 241893421 ≤ 241926189)
    (by decide : 241926189 ≤ 241958957) block2 block3

theorem join_1_0 : (twinPrimeSegment 241827885 241958957).card = 482 := by
  simpa using combineTwinPrimeSegments (by decide : 241827885 ≤ 241893421)
    (by decide : 241893421 ≤ 241958957) join_0_0 join_0_1

theorem total : (twinPrimeSegment 241827885 241958957).card = 482 := join_1_0

end S115C05
end Sude.GeneratedTwinScan
