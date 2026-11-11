import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S156C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18102)) 327680045 327712813 = 123 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 327680045 327712813).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18102 327680045 327712813
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18103)) 327712813 327745581 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 327712813 327745581).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18103 327712813 327745581
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18104)) 327745581 327778349 = 109 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 327745581 327778349).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18104 327745581 327778349
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18105)) 327778349 327811117 = 117 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 327778349 327811117).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18105 327778349 327811117
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 327680045 327745581).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 327680045 ≤ 327712813)
    (by decide : 327712813 ≤ 327745581) block0 block1

theorem join_0_1 : (twinPrimeSegment 327745581 327811117).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 327745581 ≤ 327778349)
    (by decide : 327778349 ≤ 327811117) block2 block3

theorem join_1_0 : (twinPrimeSegment 327680045 327811117).card = 457 := by
  simpa using combineTwinPrimeSegments (by decide : 327680045 ≤ 327745581)
    (by decide : 327745581 ≤ 327811117) join_0_0 join_0_1

theorem total : (twinPrimeSegment 327680045 327811117).card = 457 := join_1_0

end S156C04
end Sude.GeneratedTwinScan
