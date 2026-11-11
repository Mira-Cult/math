import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S228C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21909)) 479985709 480018477 = 110 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 479985709 480018477).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21909 479985709 480018477
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21910)) 480018477 480051245 = 97 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 480018477 480051245).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21910 480018477 480051245
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21910)) 480051245 480084013 = 96 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 480051245 480084013).card = 96 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21910 480051245 480084013
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21911)) 480084013 480116781 = 101 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 480084013 480116781).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21911 480084013 480116781
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 479985709 480051245).card = 207 := by
  simpa using combineTwinPrimeSegments (by decide : 479985709 ≤ 480018477)
    (by decide : 480018477 ≤ 480051245) block0 block1

theorem join_0_1 : (twinPrimeSegment 480051245 480116781).card = 197 := by
  simpa using combineTwinPrimeSegments (by decide : 480051245 ≤ 480084013)
    (by decide : 480084013 ≤ 480116781) block2 block3

theorem join_1_0 : (twinPrimeSegment 479985709 480116781).card = 404 := by
  simpa using combineTwinPrimeSegments (by decide : 479985709 ≤ 480051245)
    (by decide : 480051245 ≤ 480116781) join_0_0 join_0_1

theorem total : (twinPrimeSegment 479985709 480116781).card = 404 := join_1_0

end S228C14
end Sude.GeneratedTwinScan
