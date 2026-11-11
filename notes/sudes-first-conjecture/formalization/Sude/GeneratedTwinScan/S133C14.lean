import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S133C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16756)) 280756269 280789037 = 112 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 280756269 280789037).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16756 280756269 280789037
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16757)) 280789037 280821805 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 280789037 280821805).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16757 280789037 280821805
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16758)) 280821805 280854573 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 280821805 280854573).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16758 280821805 280854573
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16759)) 280854573 280887341 = 104 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 280854573 280887341).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16759 280854573 280887341
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 280756269 280821805).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 280756269 ≤ 280789037)
    (by decide : 280789037 ≤ 280821805) block0 block1

theorem join_0_1 : (twinPrimeSegment 280821805 280887341).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 280821805 ≤ 280854573)
    (by decide : 280854573 ≤ 280887341) block2 block3

theorem join_1_0 : (twinPrimeSegment 280756269 280887341).card = 441 := by
  simpa using combineTwinPrimeSegments (by decide : 280756269 ≤ 280821805)
    (by decide : 280821805 ≤ 280887341) join_0_0 join_0_1

theorem total : (twinPrimeSegment 280756269 280887341).card = 441 := join_1_0

end S133C14
end Sude.GeneratedTwinScan
