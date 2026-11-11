import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S182C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19547)) 382074925 382107693 = 105 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 382074925 382107693).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19547 382074925 382107693
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19548)) 382107693 382140461 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 382107693 382140461).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19548 382107693 382140461
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19549)) 382140461 382173229 = 123 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 382140461 382173229).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19549 382140461 382173229
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19550)) 382173229 382205997 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 382173229 382205997).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19550 382173229 382205997
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 382074925 382140461).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 382074925 ≤ 382107693)
    (by decide : 382107693 ≤ 382140461) block0 block1

theorem join_0_1 : (twinPrimeSegment 382140461 382205997).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 382140461 ≤ 382173229)
    (by decide : 382173229 ≤ 382205997) block2 block3

theorem join_1_0 : (twinPrimeSegment 382074925 382205997).card = 456 := by
  simpa using combineTwinPrimeSegments (by decide : 382074925 ≤ 382140461)
    (by decide : 382140461 ≤ 382205997) join_0_0 join_0_1

theorem total : (twinPrimeSegment 382074925 382205997).card = 456 := join_1_0

end S182C03
end Sude.GeneratedTwinScan
