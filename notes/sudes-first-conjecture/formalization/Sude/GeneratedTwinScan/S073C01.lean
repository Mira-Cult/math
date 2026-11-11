import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S073C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12379)) 153223213 153255981 = 116 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 153223213 153255981).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12379 153223213 153255981
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12380)) 153255981 153288749 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 153255981 153288749).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12380 153255981 153288749
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12382)) 153288749 153321517 = 120 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 153288749 153321517).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12382 153288749 153321517
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12383)) 153321517 153354285 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 153321517 153354285).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12383 153321517 153354285
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 153223213 153288749).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 153223213 ≤ 153255981)
    (by decide : 153255981 ≤ 153288749) block0 block1

theorem join_0_1 : (twinPrimeSegment 153288749 153354285).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 153288749 ≤ 153321517)
    (by decide : 153321517 ≤ 153354285) block2 block3

theorem join_1_0 : (twinPrimeSegment 153223213 153354285).card = 469 := by
  simpa using combineTwinPrimeSegments (by decide : 153223213 ≤ 153288749)
    (by decide : 153288749 ≤ 153354285) join_0_0 join_0_1

theorem total : (twinPrimeSegment 153223213 153354285).card = 469 := join_1_0

end S073C01
end Sude.GeneratedTwinScan
