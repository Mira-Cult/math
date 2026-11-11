import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S097C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14273)) 203685933 203718701 = 123 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 203685933 203718701).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14273 203685933 203718701
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14274)) 203718701 203751469 = 128 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 203718701 203751469).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14274 203718701 203751469
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14275)) 203751469 203784237 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 203751469 203784237).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14275 203751469 203784237
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14276)) 203784237 203817005 = 102 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 203784237 203817005).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14276 203784237 203817005
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 203685933 203751469).card = 251 := by
  simpa using combineTwinPrimeSegments (by decide : 203685933 ≤ 203718701)
    (by decide : 203718701 ≤ 203751469) block0 block1

theorem join_0_1 : (twinPrimeSegment 203751469 203817005).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 203751469 ≤ 203784237)
    (by decide : 203784237 ≤ 203817005) block2 block3

theorem join_1_0 : (twinPrimeSegment 203685933 203817005).card = 467 := by
  simpa using combineTwinPrimeSegments (by decide : 203685933 ≤ 203751469)
    (by decide : 203751469 ≤ 203817005) join_0_0 join_0_1

theorem total : (twinPrimeSegment 203685933 203817005).card = 467 := join_1_0

end S097C02
end Sude.GeneratedTwinScan
