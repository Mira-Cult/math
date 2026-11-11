import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S141C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17231)) 296878125 296910893 = 110 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 296878125 296910893).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17231 296878125 296910893
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17232)) 296910893 296943661 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 296910893 296943661).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17232 296910893 296943661
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17233)) 296943661 296976429 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 296943661 296976429).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17233 296943661 296976429
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17233)) 296976429 297009197 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 296976429 297009197).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17233 296976429 297009197
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 296878125 296943661).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 296878125 ≤ 296910893)
    (by decide : 296910893 ≤ 296943661) block0 block1

theorem join_0_1 : (twinPrimeSegment 296943661 297009197).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 296943661 ≤ 296976429)
    (by decide : 296976429 ≤ 297009197) block2 block3

theorem join_1_0 : (twinPrimeSegment 296878125 297009197).card = 448 := by
  simpa using combineTwinPrimeSegments (by decide : 296878125 ≤ 296943661)
    (by decide : 296943661 ≤ 297009197) join_0_0 join_0_1

theorem total : (twinPrimeSegment 296878125 297009197).card = 448 := join_1_0

end S141C09
end Sude.GeneratedTwinScan
