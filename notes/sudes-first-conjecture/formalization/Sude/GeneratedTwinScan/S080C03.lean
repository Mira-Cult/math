import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S080C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12969)) 168165421 168198189 = 129 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 168165421 168198189).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12969 168165421 168198189
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12970)) 168198189 168230957 = 123 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 168198189 168230957).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12970 168198189 168230957
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12971)) 168230957 168263725 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 168230957 168263725).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12971 168230957 168263725
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12972)) 168263725 168296493 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 168263725 168296493).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12972 168263725 168296493
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 168165421 168230957).card = 252 := by
  simpa using combineTwinPrimeSegments (by decide : 168165421 ≤ 168198189)
    (by decide : 168198189 ≤ 168230957) block0 block1

theorem join_0_1 : (twinPrimeSegment 168230957 168296493).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 168230957 ≤ 168263725)
    (by decide : 168263725 ≤ 168296493) block2 block3

theorem join_1_0 : (twinPrimeSegment 168165421 168296493).card = 483 := by
  simpa using combineTwinPrimeSegments (by decide : 168165421 ≤ 168230957)
    (by decide : 168230957 ≤ 168296493) join_0_0 join_0_1

theorem total : (twinPrimeSegment 168165421 168296493).card = 483 := join_1_0

end S080C03
end Sude.GeneratedTwinScan
