import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S078C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12806)) 163971117 164003885 = 129 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 163971117 164003885).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12806 163971117 164003885
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12807)) 164003885 164036653 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 164003885 164036653).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12807 164003885 164036653
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12808)) 164036653 164069421 = 110 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 164036653 164069421).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12808 164036653 164069421
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12810)) 164069421 164102189 = 105 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 164069421 164102189).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12810 164069421 164102189
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 163971117 164036653).card = 237 := by
  simpa using combineTwinPrimeSegments (by decide : 163971117 ≤ 164003885)
    (by decide : 164003885 ≤ 164036653) block0 block1

theorem join_0_1 : (twinPrimeSegment 164036653 164102189).card = 215 := by
  simpa using combineTwinPrimeSegments (by decide : 164036653 ≤ 164069421)
    (by decide : 164069421 ≤ 164102189) block2 block3

theorem join_1_0 : (twinPrimeSegment 163971117 164102189).card = 452 := by
  simpa using combineTwinPrimeSegments (by decide : 163971117 ≤ 164036653)
    (by decide : 164036653 ≤ 164102189) join_0_0 join_0_1

theorem total : (twinPrimeSegment 163971117 164102189).card = 452 := join_1_0

end S078C03
end Sude.GeneratedTwinScan
