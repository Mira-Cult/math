import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S243C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22581)) 509870125 509902893 = 105 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 509870125 509902893).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22581 509870125 509902893
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22581)) 509902893 509935661 = 101 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 509902893 509935661).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22581 509902893 509935661
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22582)) 509935661 509968429 = 106 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 509935661 509968429).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22582 509935661 509968429
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22583)) 509968429 510001197 = 109 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 509968429 510001197).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22583 509968429 510001197
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 509870125 509935661).card = 206 := by
  simpa using combineTwinPrimeSegments (by decide : 509870125 ≤ 509902893)
    (by decide : 509902893 ≤ 509935661) block0 block1

theorem join_0_1 : (twinPrimeSegment 509935661 510001197).card = 215 := by
  simpa using combineTwinPrimeSegments (by decide : 509935661 ≤ 509968429)
    (by decide : 509968429 ≤ 510001197) block2 block3

theorem join_1_0 : (twinPrimeSegment 509870125 510001197).card = 421 := by
  simpa using combineTwinPrimeSegments (by decide : 509870125 ≤ 509935661)
    (by decide : 509935661 ≤ 510001197) join_0_0 join_0_1

theorem total : (twinPrimeSegment 509870125 510001197).card = 421 := join_1_0

end S243C02
end Sude.GeneratedTwinScan
