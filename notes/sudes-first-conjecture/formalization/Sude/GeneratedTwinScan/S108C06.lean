import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S108C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15076)) 227278893 227311661 = 140 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 227278893 227311661).card = 140 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15076 227278893 227311661
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15077)) 227311661 227344429 = 119 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 227311661 227344429).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15077 227311661 227344429
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15079)) 227344429 227377197 = 121 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 227344429 227377197).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15079 227344429 227377197
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15080)) 227377197 227409965 = 108 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 227377197 227409965).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15080 227377197 227409965
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 227278893 227344429).card = 259 := by
  simpa using combineTwinPrimeSegments (by decide : 227278893 ≤ 227311661)
    (by decide : 227311661 ≤ 227344429) block0 block1

theorem join_0_1 : (twinPrimeSegment 227344429 227409965).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 227344429 ≤ 227377197)
    (by decide : 227377197 ≤ 227409965) block2 block3

theorem join_1_0 : (twinPrimeSegment 227278893 227409965).card = 488 := by
  simpa using combineTwinPrimeSegments (by decide : 227278893 ≤ 227344429)
    (by decide : 227344429 ≤ 227409965) join_0_0 join_0_1

theorem total : (twinPrimeSegment 227278893 227409965).card = 488 := join_1_0

end S108C06
end Sude.GeneratedTwinScan
