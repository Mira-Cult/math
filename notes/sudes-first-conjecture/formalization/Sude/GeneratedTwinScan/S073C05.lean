import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S073C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12400)) 153747501 153780269 = 123 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 153747501 153780269).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12400 153747501 153780269
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12402)) 153780269 153813037 = 117 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 153780269 153813037).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12402 153780269 153813037
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12403)) 153813037 153845805 = 117 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 153813037 153845805).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12403 153813037 153845805
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12404)) 153845805 153878573 = 127 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 153845805 153878573).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12404 153845805 153878573
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 153747501 153813037).card = 240 := by
  simpa using combineTwinPrimeSegments (by decide : 153747501 ≤ 153780269)
    (by decide : 153780269 ≤ 153813037) block0 block1

theorem join_0_1 : (twinPrimeSegment 153813037 153878573).card = 244 := by
  simpa using combineTwinPrimeSegments (by decide : 153813037 ≤ 153845805)
    (by decide : 153845805 ≤ 153878573) block2 block3

theorem join_1_0 : (twinPrimeSegment 153747501 153878573).card = 484 := by
  simpa using combineTwinPrimeSegments (by decide : 153747501 ≤ 153813037)
    (by decide : 153813037 ≤ 153878573) join_0_0 join_0_1

theorem total : (twinPrimeSegment 153747501 153878573).card = 484 := join_1_0

end S073C05
end Sude.GeneratedTwinScan
