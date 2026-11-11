import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S124C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16126)) 260046893 260079661 = 91 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 260046893 260079661).card = 91 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16126 260046893 260079661
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16128)) 260079661 260112429 = 107 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 260079661 260112429).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16128 260079661 260112429
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16129)) 260112429 260145197 = 123 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 260112429 260145197).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16129 260112429 260145197
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16130)) 260145197 260177965 = 118 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 260145197 260177965).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16130 260145197 260177965
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 260046893 260112429).card = 198 := by
  simpa using combineTwinPrimeSegments (by decide : 260046893 ≤ 260079661)
    (by decide : 260079661 ≤ 260112429) block0 block1

theorem join_0_1 : (twinPrimeSegment 260112429 260177965).card = 241 := by
  simpa using combineTwinPrimeSegments (by decide : 260112429 ≤ 260145197)
    (by decide : 260145197 ≤ 260177965) block2 block3

theorem join_1_0 : (twinPrimeSegment 260046893 260177965).card = 439 := by
  simpa using combineTwinPrimeSegments (by decide : 260046893 ≤ 260112429)
    (by decide : 260112429 ≤ 260177965) join_0_0 join_0_1

theorem total : (twinPrimeSegment 260046893 260177965).card = 439 := join_1_0

end S124C00
end Sude.GeneratedTwinScan
