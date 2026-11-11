import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S217C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21370)) 456654893 456687661 = 118 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 456654893 456687661).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21370 456654893 456687661
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21371)) 456687661 456720429 = 109 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 456687661 456720429).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21371 456687661 456720429
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21371)) 456720429 456753197 = 104 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 456720429 456753197).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21371 456720429 456753197
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21372)) 456753197 456785965 = 101 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 456753197 456785965).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21372 456753197 456785965
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 456654893 456720429).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 456654893 ≤ 456687661)
    (by decide : 456687661 ≤ 456720429) block0 block1

theorem join_0_1 : (twinPrimeSegment 456720429 456785965).card = 205 := by
  simpa using combineTwinPrimeSegments (by decide : 456720429 ≤ 456753197)
    (by decide : 456753197 ≤ 456785965) block2 block3

theorem join_1_0 : (twinPrimeSegment 456654893 456785965).card = 432 := by
  simpa using combineTwinPrimeSegments (by decide : 456654893 ≤ 456720429)
    (by decide : 456720429 ≤ 456785965) join_0_0 join_0_1

theorem total : (twinPrimeSegment 456654893 456785965).card = 432 := join_1_0

end S217C12
end Sude.GeneratedTwinScan
