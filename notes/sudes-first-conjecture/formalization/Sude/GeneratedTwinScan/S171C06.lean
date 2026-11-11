import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S171C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18958)) 359399469 359432237 = 105 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 359399469 359432237).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18958 359399469 359432237
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18959)) 359432237 359465005 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 359432237 359465005).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18959 359432237 359465005
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18960)) 359465005 359497773 = 102 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 359465005 359497773).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18960 359465005 359497773
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18961)) 359497773 359530541 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 359497773 359530541).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18961 359497773 359530541
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 359399469 359465005).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 359399469 ≤ 359432237)
    (by decide : 359432237 ≤ 359465005) block0 block1

theorem join_0_1 : (twinPrimeSegment 359465005 359530541).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 359465005 ≤ 359497773)
    (by decide : 359497773 ≤ 359530541) block2 block3

theorem join_1_0 : (twinPrimeSegment 359399469 359530541).card = 437 := by
  simpa using combineTwinPrimeSegments (by decide : 359399469 ≤ 359465005)
    (by decide : 359465005 ≤ 359530541) join_0_0 join_0_1

theorem total : (twinPrimeSegment 359399469 359530541).card = 437 := join_1_0

end S171C06
end Sude.GeneratedTwinScan
