import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S156C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18091)) 327286829 327319597 = 101 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 327286829 327319597).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18091 327286829 327319597
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18092)) 327319597 327352365 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 327319597 327352365).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18092 327319597 327352365
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18093)) 327352365 327385133 = 94 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 327352365 327385133).card = 94 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18093 327352365 327385133
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18094)) 327385133 327417901 = 120 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 327385133 327417901).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18094 327385133 327417901
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 327286829 327352365).card = 209 := by
  simpa using combineTwinPrimeSegments (by decide : 327286829 ≤ 327319597)
    (by decide : 327319597 ≤ 327352365) block0 block1

theorem join_0_1 : (twinPrimeSegment 327352365 327417901).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 327352365 ≤ 327385133)
    (by decide : 327385133 ≤ 327417901) block2 block3

theorem join_1_0 : (twinPrimeSegment 327286829 327417901).card = 423 := by
  simpa using combineTwinPrimeSegments (by decide : 327286829 ≤ 327352365)
    (by decide : 327352365 ≤ 327417901) join_0_0 join_0_1

theorem total : (twinPrimeSegment 327286829 327417901).card = 423 := join_1_0

end S156C01
end Sude.GeneratedTwinScan
