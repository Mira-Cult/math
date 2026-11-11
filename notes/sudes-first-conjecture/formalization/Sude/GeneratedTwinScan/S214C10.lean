import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S214C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21216)) 450101293 450134061 = 95 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 450101293 450134061).card = 95 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21216 450101293 450134061
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21217)) 450134061 450166829 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 450134061 450166829).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21217 450134061 450166829
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21217)) 450166829 450199597 = 111 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 450166829 450199597).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21217 450166829 450199597
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21218)) 450199597 450232365 = 101 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 450199597 450232365).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21218 450199597 450232365
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 450101293 450166829).card = 211 := by
  simpa using combineTwinPrimeSegments (by decide : 450101293 ≤ 450134061)
    (by decide : 450134061 ≤ 450166829) block0 block1

theorem join_0_1 : (twinPrimeSegment 450166829 450232365).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 450166829 ≤ 450199597)
    (by decide : 450199597 ≤ 450232365) block2 block3

theorem join_1_0 : (twinPrimeSegment 450101293 450232365).card = 423 := by
  simpa using combineTwinPrimeSegments (by decide : 450101293 ≤ 450166829)
    (by decide : 450166829 ≤ 450232365) join_0_0 join_0_1

theorem total : (twinPrimeSegment 450101293 450232365).card = 423 := join_1_0

end S214C10
end Sude.GeneratedTwinScan
