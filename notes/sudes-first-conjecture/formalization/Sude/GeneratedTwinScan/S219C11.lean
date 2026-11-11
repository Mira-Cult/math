import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S219C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21465)) 460718125 460750893 = 105 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 460718125 460750893).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21465 460718125 460750893
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21465)) 460750893 460783661 = 102 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 460750893 460783661).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21465 460750893 460783661
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21466)) 460783661 460816429 = 129 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 460783661 460816429).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21466 460783661 460816429
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21467)) 460816429 460849197 = 99 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 460816429 460849197).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21467 460816429 460849197
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 460718125 460783661).card = 207 := by
  simpa using combineTwinPrimeSegments (by decide : 460718125 ≤ 460750893)
    (by decide : 460750893 ≤ 460783661) block0 block1

theorem join_0_1 : (twinPrimeSegment 460783661 460849197).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 460783661 ≤ 460816429)
    (by decide : 460816429 ≤ 460849197) block2 block3

theorem join_1_0 : (twinPrimeSegment 460718125 460849197).card = 435 := by
  simpa using combineTwinPrimeSegments (by decide : 460718125 ≤ 460783661)
    (by decide : 460783661 ≤ 460849197) join_0_0 join_0_1

theorem total : (twinPrimeSegment 460718125 460849197).card = 435 := join_1_0

end S219C11
end Sude.GeneratedTwinScan
