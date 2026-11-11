import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S140C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17193)) 295567405 295600173 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 295567405 295600173).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17193 295567405 295600173
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17193)) 295600173 295632941 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 295600173 295632941).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17193 295600173 295632941
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17194)) 295632941 295665709 = 139 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 295632941 295665709).card = 139 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17194 295632941 295665709
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17195)) 295665709 295698477 = 118 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 295665709 295698477).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17195 295665709 295698477
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 295567405 295632941).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 295567405 ≤ 295600173)
    (by decide : 295600173 ≤ 295632941) block0 block1

theorem join_0_1 : (twinPrimeSegment 295632941 295698477).card = 257 := by
  simpa using combineTwinPrimeSegments (by decide : 295632941 ≤ 295665709)
    (by decide : 295665709 ≤ 295698477) block2 block3

theorem join_1_0 : (twinPrimeSegment 295567405 295698477).card = 484 := by
  simpa using combineTwinPrimeSegments (by decide : 295567405 ≤ 295632941)
    (by decide : 295632941 ≤ 295698477) join_0_0 join_0_1

theorem total : (twinPrimeSegment 295567405 295698477).card = 484 := join_1_0

end S140C15
end Sude.GeneratedTwinScan
