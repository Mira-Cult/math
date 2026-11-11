import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S158C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18232)) 332398637 332431405 = 108 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 332398637 332431405).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18232 332398637 332431405
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18233)) 332431405 332464173 = 125 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 332431405 332464173).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18233 332431405 332464173
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18234)) 332464173 332496941 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 332464173 332496941).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18234 332464173 332496941
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18235)) 332496941 332529709 = 121 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 332496941 332529709).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18235 332496941 332529709
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 332398637 332464173).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 332398637 ≤ 332431405)
    (by decide : 332431405 ≤ 332464173) block0 block1

theorem join_0_1 : (twinPrimeSegment 332464173 332529709).card = 236 := by
  simpa using combineTwinPrimeSegments (by decide : 332464173 ≤ 332496941)
    (by decide : 332496941 ≤ 332529709) block2 block3

theorem join_1_0 : (twinPrimeSegment 332398637 332529709).card = 469 := by
  simpa using combineTwinPrimeSegments (by decide : 332398637 ≤ 332464173)
    (by decide : 332464173 ≤ 332529709) join_0_0 join_0_1

theorem total : (twinPrimeSegment 332398637 332529709).card = 469 := join_1_0

end S158C08
end Sude.GeneratedTwinScan
