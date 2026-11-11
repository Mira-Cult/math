import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S187C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19833)) 393347117 393379885 = 105 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 393347117 393379885).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19833 393347117 393379885
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19834)) 393379885 393412653 = 109 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 393379885 393412653).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19834 393379885 393412653
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19835)) 393412653 393445421 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 393412653 393445421).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19835 393412653 393445421
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19836)) 393445421 393478189 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 393445421 393478189).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19836 393445421 393478189
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 393347117 393412653).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 393347117 ≤ 393379885)
    (by decide : 393379885 ≤ 393412653) block0 block1

theorem join_0_1 : (twinPrimeSegment 393412653 393478189).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 393412653 ≤ 393445421)
    (by decide : 393445421 ≤ 393478189) block2 block3

theorem join_1_0 : (twinPrimeSegment 393347117 393478189).card = 440 := by
  simpa using combineTwinPrimeSegments (by decide : 393347117 ≤ 393412653)
    (by decide : 393412653 ≤ 393478189) join_0_0 join_0_1

theorem total : (twinPrimeSegment 393347117 393478189).card = 440 := join_1_0

end S187C09
end Sude.GeneratedTwinScan
