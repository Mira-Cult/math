import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S154C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18023)) 324796461 324829229 = 118 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 324796461 324829229).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18023 324796461 324829229
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18023)) 324829229 324861997 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 324829229 324861997).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18023 324829229 324861997
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18024)) 324861997 324894765 = 132 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 324861997 324894765).card = 132 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18024 324861997 324894765
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18025)) 324894765 324927533 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 324894765 324927533).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18025 324894765 324927533
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 324796461 324861997).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 324796461 ≤ 324829229)
    (by decide : 324829229 ≤ 324861997) block0 block1

theorem join_0_1 : (twinPrimeSegment 324861997 324927533).card = 247 := by
  simpa using combineTwinPrimeSegments (by decide : 324861997 ≤ 324894765)
    (by decide : 324894765 ≤ 324927533) block2 block3

theorem join_1_0 : (twinPrimeSegment 324796461 324927533).card = 477 := by
  simpa using combineTwinPrimeSegments (by decide : 324796461 ≤ 324861997)
    (by decide : 324861997 ≤ 324927533) join_0_0 join_0_1

theorem total : (twinPrimeSegment 324796461 324927533).card = 477 := join_1_0

end S154C14
end Sude.GeneratedTwinScan
