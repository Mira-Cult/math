import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S080C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12974)) 168296493 168329261 = 126 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 168296493 168329261).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12974 168296493 168329261
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12975)) 168329261 168362029 = 128 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 168329261 168362029).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12975 168329261 168362029
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12976)) 168362029 168394797 = 119 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 168362029 168394797).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12976 168362029 168394797
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12977)) 168394797 168427565 = 126 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 168394797 168427565).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12977 168394797 168427565
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 168296493 168362029).card = 254 := by
  simpa using combineTwinPrimeSegments (by decide : 168296493 ≤ 168329261)
    (by decide : 168329261 ≤ 168362029) block0 block1

theorem join_0_1 : (twinPrimeSegment 168362029 168427565).card = 245 := by
  simpa using combineTwinPrimeSegments (by decide : 168362029 ≤ 168394797)
    (by decide : 168394797 ≤ 168427565) block2 block3

theorem join_1_0 : (twinPrimeSegment 168296493 168427565).card = 499 := by
  simpa using combineTwinPrimeSegments (by decide : 168296493 ≤ 168362029)
    (by decide : 168362029 ≤ 168427565) join_0_0 join_0_1

theorem total : (twinPrimeSegment 168296493 168427565).card = 499 := join_1_0

end S080C04
end Sude.GeneratedTwinScan
