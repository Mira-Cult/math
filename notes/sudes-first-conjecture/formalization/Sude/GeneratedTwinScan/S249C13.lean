import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S249C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22889)) 523894829 523927597 = 101 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 523894829 523927597).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22889 523894829 523927597
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22890)) 523927597 523960365 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 523927597 523960365).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22890 523927597 523960365
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22890)) 523960365 523993133 = 99 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 523960365 523993133).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22890 523960365 523993133
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22891)) 523993133 524025901 = 111 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 523993133 524025901).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22891 523993133 524025901
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 523894829 523960365).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 523894829 ≤ 523927597)
    (by decide : 523927597 ≤ 523960365) block0 block1

theorem join_0_1 : (twinPrimeSegment 523960365 524025901).card = 210 := by
  simpa using combineTwinPrimeSegments (by decide : 523960365 ≤ 523993133)
    (by decide : 523993133 ≤ 524025901) block2 block3

theorem join_1_0 : (twinPrimeSegment 523894829 524025901).card = 423 := by
  simpa using combineTwinPrimeSegments (by decide : 523894829 ≤ 523960365)
    (by decide : 523960365 ≤ 524025901) join_0_0 join_0_1

theorem total : (twinPrimeSegment 523894829 524025901).card = 423 := join_1_0

end S249C13
end Sude.GeneratedTwinScan
