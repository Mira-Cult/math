import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S240C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22441)) 503578669 503611437 = 98 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 503578669 503611437).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22441 503578669 503611437
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22442)) 503611437 503644205 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 503611437 503644205).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22442 503611437 503644205
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22442)) 503644205 503676973 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 503644205 503676973).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22442 503644205 503676973
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22443)) 503676973 503709741 = 108 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 503676973 503709741).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22443 503676973 503709741
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 503578669 503644205).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 503578669 ≤ 503611437)
    (by decide : 503611437 ≤ 503644205) block0 block1

theorem join_0_1 : (twinPrimeSegment 503644205 503709741).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 503644205 ≤ 503676973)
    (by decide : 503676973 ≤ 503709741) block2 block3

theorem join_1_0 : (twinPrimeSegment 503578669 503709741).card = 438 := by
  simpa using combineTwinPrimeSegments (by decide : 503578669 ≤ 503644205)
    (by decide : 503644205 ≤ 503709741) join_0_0 join_0_1

theorem total : (twinPrimeSegment 503578669 503709741).card = 438 := join_1_0

end S240C02
end Sude.GeneratedTwinScan
