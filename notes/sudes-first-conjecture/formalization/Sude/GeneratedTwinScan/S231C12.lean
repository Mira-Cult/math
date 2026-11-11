import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S231C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22046)) 486015021 486047789 = 110 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 486015021 486047789).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22046 486015021 486047789
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22047)) 486047789 486080557 = 90 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 486047789 486080557).card = 90 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22047 486047789 486080557
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22047)) 486080557 486113325 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 486080557 486113325).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22047 486080557 486113325
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22048)) 486113325 486146093 = 133 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 486113325 486146093).card = 133 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22048 486113325 486146093
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 486015021 486080557).card = 200 := by
  simpa using combineTwinPrimeSegments (by decide : 486015021 ≤ 486047789)
    (by decide : 486047789 ≤ 486080557) block0 block1

theorem join_0_1 : (twinPrimeSegment 486080557 486146093).card = 246 := by
  simpa using combineTwinPrimeSegments (by decide : 486080557 ≤ 486113325)
    (by decide : 486113325 ≤ 486146093) block2 block3

theorem join_1_0 : (twinPrimeSegment 486015021 486146093).card = 446 := by
  simpa using combineTwinPrimeSegments (by decide : 486015021 ≤ 486080557)
    (by decide : 486080557 ≤ 486146093) join_0_0 join_0_1

theorem total : (twinPrimeSegment 486015021 486146093).card = 446 := join_1_0

end S231C12
end Sude.GeneratedTwinScan
