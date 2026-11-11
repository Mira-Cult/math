import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S102C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14662)) 214958125 214990893 = 89 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 214958125 214990893).card = 89 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14662 214958125 214990893
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14663)) 214990893 215023661 = 137 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 214990893 215023661).card = 137 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14663 214990893 215023661
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14664)) 215023661 215056429 = 126 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 215023661 215056429).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14664 215023661 215056429
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14665)) 215056429 215089197 = 107 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 215056429 215089197).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14665 215056429 215089197
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 214958125 215023661).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 214958125 ≤ 214990893)
    (by decide : 214990893 ≤ 215023661) block0 block1

theorem join_0_1 : (twinPrimeSegment 215023661 215089197).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 215023661 ≤ 215056429)
    (by decide : 215056429 ≤ 215089197) block2 block3

theorem join_1_0 : (twinPrimeSegment 214958125 215089197).card = 459 := by
  simpa using combineTwinPrimeSegments (by decide : 214958125 ≤ 215023661)
    (by decide : 215023661 ≤ 215089197) join_0_0 join_0_1

theorem total : (twinPrimeSegment 214958125 215089197).card = 459 := join_1_0

end S102C08
end Sude.GeneratedTwinScan
