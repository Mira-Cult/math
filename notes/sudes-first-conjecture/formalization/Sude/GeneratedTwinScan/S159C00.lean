import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S159C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18261)) 333447213 333479981 = 132 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 333447213 333479981).card = 132 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18261 333447213 333479981
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18262)) 333479981 333512749 = 109 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 333479981 333512749).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18262 333479981 333512749
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18263)) 333512749 333545517 = 108 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 333512749 333545517).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18263 333512749 333545517
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18264)) 333545517 333578285 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 333545517 333578285).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18264 333545517 333578285
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 333447213 333512749).card = 241 := by
  simpa using combineTwinPrimeSegments (by decide : 333447213 ≤ 333479981)
    (by decide : 333479981 ≤ 333512749) block0 block1

theorem join_0_1 : (twinPrimeSegment 333512749 333578285).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 333512749 ≤ 333545517)
    (by decide : 333545517 ≤ 333578285) block2 block3

theorem join_1_0 : (twinPrimeSegment 333447213 333578285).card = 463 := by
  simpa using combineTwinPrimeSegments (by decide : 333447213 ≤ 333512749)
    (by decide : 333512749 ≤ 333578285) join_0_0 join_0_1

theorem total : (twinPrimeSegment 333447213 333578285).card = 463 := join_1_0

end S159C00
end Sude.GeneratedTwinScan
