import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S170C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18885)) 356646957 356679725 = 122 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 356646957 356679725).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18885 356646957 356679725
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18886)) 356679725 356712493 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 356679725 356712493).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18886 356679725 356712493
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18887)) 356712493 356745261 = 100 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 356712493 356745261).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18887 356712493 356745261
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18888)) 356745261 356778029 = 99 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 356745261 356778029).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18888 356745261 356778029
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 356646957 356712493).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 356646957 ≤ 356679725)
    (by decide : 356679725 ≤ 356712493) block0 block1

theorem join_0_1 : (twinPrimeSegment 356712493 356778029).card = 199 := by
  simpa using combineTwinPrimeSegments (by decide : 356712493 ≤ 356745261)
    (by decide : 356745261 ≤ 356778029) block2 block3

theorem join_1_0 : (twinPrimeSegment 356646957 356778029).card = 432 := by
  simpa using combineTwinPrimeSegments (by decide : 356646957 ≤ 356712493)
    (by decide : 356712493 ≤ 356778029) join_0_0 join_0_1

theorem total : (twinPrimeSegment 356646957 356778029).card = 432 := join_1_0

end S170C01
end Sude.GeneratedTwinScan
