import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S211C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21073)) 444071981 444104749 = 100 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 444071981 444104749).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21073 444071981 444104749
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21074)) 444104749 444137517 = 102 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 444104749 444137517).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21074 444104749 444137517
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21075)) 444137517 444170285 = 107 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 444137517 444170285).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21075 444137517 444170285
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21076)) 444170285 444203053 = 118 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 444170285 444203053).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21076 444170285 444203053
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 444071981 444137517).card = 202 := by
  simpa using combineTwinPrimeSegments (by decide : 444071981 ≤ 444104749)
    (by decide : 444104749 ≤ 444137517) block0 block1

theorem join_0_1 : (twinPrimeSegment 444137517 444203053).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 444137517 ≤ 444170285)
    (by decide : 444170285 ≤ 444203053) block2 block3

theorem join_1_0 : (twinPrimeSegment 444071981 444203053).card = 427 := by
  simpa using combineTwinPrimeSegments (by decide : 444071981 ≤ 444137517)
    (by decide : 444137517 ≤ 444203053) join_0_0 join_0_1

theorem total : (twinPrimeSegment 444071981 444203053).card = 427 := join_1_0

end S211C12
end Sude.GeneratedTwinScan
