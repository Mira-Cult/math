import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S229C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21933)) 481034285 481067053 = 116 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 481034285 481067053).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21933 481034285 481067053
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21933)) 481067053 481099821 = 100 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 481067053 481099821).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21933 481067053 481099821
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21934)) 481099821 481132589 = 94 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 481099821 481132589).card = 94 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21934 481099821 481132589
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21935)) 481132589 481165357 = 88 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 481132589 481165357).card = 88 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21935 481132589 481165357
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 481034285 481099821).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 481034285 ≤ 481067053)
    (by decide : 481067053 ≤ 481099821) block0 block1

theorem join_0_1 : (twinPrimeSegment 481099821 481165357).card = 182 := by
  simpa using combineTwinPrimeSegments (by decide : 481099821 ≤ 481132589)
    (by decide : 481132589 ≤ 481165357) block2 block3

theorem join_1_0 : (twinPrimeSegment 481034285 481165357).card = 398 := by
  simpa using combineTwinPrimeSegments (by decide : 481034285 ≤ 481099821)
    (by decide : 481099821 ≤ 481165357) join_0_0 join_0_1

theorem total : (twinPrimeSegment 481034285 481165357).card = 398 := join_1_0

end S229C06
end Sude.GeneratedTwinScan
