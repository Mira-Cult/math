import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S205C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20741)) 430178349 430211117 = 120 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 430178349 430211117).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20741 430178349 430211117
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20742)) 430211117 430243885 = 104 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 430211117 430243885).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20742 430211117 430243885
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20743)) 430243885 430276653 = 107 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 430243885 430276653).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20743 430243885 430276653
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20743)) 430276653 430309421 = 87 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 430276653 430309421).card = 87 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20743 430276653 430309421
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 430178349 430243885).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 430178349 ≤ 430211117)
    (by decide : 430211117 ≤ 430243885) block0 block1

theorem join_0_1 : (twinPrimeSegment 430243885 430309421).card = 194 := by
  simpa using combineTwinPrimeSegments (by decide : 430243885 ≤ 430276653)
    (by decide : 430276653 ≤ 430309421) block2 block3

theorem join_1_0 : (twinPrimeSegment 430178349 430309421).card = 418 := by
  simpa using combineTwinPrimeSegments (by decide : 430178349 ≤ 430243885)
    (by decide : 430243885 ≤ 430309421) join_0_0 join_0_1

theorem total : (twinPrimeSegment 430178349 430309421).card = 418 := join_1_0

end S205C02
end Sude.GeneratedTwinScan
