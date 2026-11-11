import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S132C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16697)) 278790189 278822957 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 278790189 278822957).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16697 278790189 278822957
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16698)) 278822957 278855725 = 119 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 278822957 278855725).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16698 278822957 278855725
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16699)) 278855725 278888493 = 96 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 278855725 278888493).card = 96 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16699 278855725 278888493
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16700)) 278888493 278921261 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 278888493 278921261).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16700 278888493 278921261
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 278790189 278855725).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 278790189 ≤ 278822957)
    (by decide : 278822957 ≤ 278855725) block0 block1

theorem join_0_1 : (twinPrimeSegment 278855725 278921261).card = 210 := by
  simpa using combineTwinPrimeSegments (by decide : 278855725 ≤ 278888493)
    (by decide : 278888493 ≤ 278921261) block2 block3

theorem join_1_0 : (twinPrimeSegment 278790189 278921261).card = 444 := by
  simpa using combineTwinPrimeSegments (by decide : 278790189 ≤ 278855725)
    (by decide : 278855725 ≤ 278921261) join_0_0 join_0_1

theorem total : (twinPrimeSegment 278790189 278921261).card = 444 := join_1_0

end S132C15
end Sude.GeneratedTwinScan
