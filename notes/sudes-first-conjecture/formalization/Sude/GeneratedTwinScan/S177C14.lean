import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S177C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19314)) 373030957 373063725 = 124 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 373030957 373063725).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19314 373030957 373063725
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19315)) 373063725 373096493 = 96 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 373063725 373096493).card = 96 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19315 373063725 373096493
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19316)) 373096493 373129261 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 373096493 373129261).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19316 373096493 373129261
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19317)) 373129261 373162029 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 373129261 373162029).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19317 373129261 373162029
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 373030957 373096493).card = 220 := by
  simpa using combineTwinPrimeSegments (by decide : 373030957 ≤ 373063725)
    (by decide : 373063725 ≤ 373096493) block0 block1

theorem join_0_1 : (twinPrimeSegment 373096493 373162029).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 373096493 ≤ 373129261)
    (by decide : 373129261 ≤ 373162029) block2 block3

theorem join_1_0 : (twinPrimeSegment 373030957 373162029).card = 455 := by
  simpa using combineTwinPrimeSegments (by decide : 373030957 ≤ 373096493)
    (by decide : 373096493 ≤ 373162029) join_0_0 join_0_1

theorem total : (twinPrimeSegment 373030957 373162029).card = 455 := join_1_0

end S177C14
end Sude.GeneratedTwinScan
