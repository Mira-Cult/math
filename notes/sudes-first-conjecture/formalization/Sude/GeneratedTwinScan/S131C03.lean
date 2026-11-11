import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S131C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16587)) 275120173 275152941 = 122 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 275120173 275152941).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16587 275120173 275152941
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16588)) 275152941 275185709 = 122 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 275152941 275185709).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16588 275152941 275185709
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16589)) 275185709 275218477 = 109 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 275185709 275218477).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16589 275185709 275218477
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16590)) 275218477 275251245 = 126 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 275218477 275251245).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16590 275218477 275251245
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 275120173 275185709).card = 244 := by
  simpa using combineTwinPrimeSegments (by decide : 275120173 ≤ 275152941)
    (by decide : 275152941 ≤ 275185709) block0 block1

theorem join_0_1 : (twinPrimeSegment 275185709 275251245).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 275185709 ≤ 275218477)
    (by decide : 275218477 ≤ 275251245) block2 block3

theorem join_1_0 : (twinPrimeSegment 275120173 275251245).card = 479 := by
  simpa using combineTwinPrimeSegments (by decide : 275120173 ≤ 275185709)
    (by decide : 275185709 ≤ 275251245) join_0_0 join_0_1

theorem total : (twinPrimeSegment 275120173 275251245).card = 479 := join_1_0

end S131C03
end Sude.GeneratedTwinScan
