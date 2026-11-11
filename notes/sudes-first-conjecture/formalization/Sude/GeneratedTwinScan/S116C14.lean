import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S116C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15656)) 245104685 245137453 = 114 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 245104685 245137453).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15656 245104685 245137453
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15657)) 245137453 245170221 = 110 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 245137453 245170221).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15657 245137453 245170221
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15658)) 245170221 245202989 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 245170221 245202989).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15658 245170221 245202989
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15660)) 245202989 245235757 = 118 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 245202989 245235757).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15660 245202989 245235757
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 245104685 245170221).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 245104685 ≤ 245137453)
    (by decide : 245137453 ≤ 245170221) block0 block1

theorem join_0_1 : (twinPrimeSegment 245170221 245235757).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 245170221 ≤ 245202989)
    (by decide : 245202989 ≤ 245235757) block2 block3

theorem join_1_0 : (twinPrimeSegment 245104685 245235757).card = 455 := by
  simpa using combineTwinPrimeSegments (by decide : 245104685 ≤ 245170221)
    (by decide : 245170221 ≤ 245235757) join_0_0 join_0_1

theorem total : (twinPrimeSegment 245104685 245235757).card = 455 := join_1_0

end S116C14
end Sude.GeneratedTwinScan
