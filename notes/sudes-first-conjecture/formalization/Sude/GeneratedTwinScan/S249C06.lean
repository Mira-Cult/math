import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S249C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22869)) 522977325 523010093 = 85 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 522977325 523010093).card = 85 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22869 522977325 523010093
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22870)) 523010093 523042861 = 100 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 523010093 523042861).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22870 523010093 523042861
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22870)) 523042861 523075629 = 109 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 523042861 523075629).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22870 523042861 523075629
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22871)) 523075629 523108397 = 107 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 523075629 523108397).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22871 523075629 523108397
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 522977325 523042861).card = 185 := by
  simpa using combineTwinPrimeSegments (by decide : 522977325 ≤ 523010093)
    (by decide : 523010093 ≤ 523042861) block0 block1

theorem join_0_1 : (twinPrimeSegment 523042861 523108397).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 523042861 ≤ 523075629)
    (by decide : 523075629 ≤ 523108397) block2 block3

theorem join_1_0 : (twinPrimeSegment 522977325 523108397).card = 401 := by
  simpa using combineTwinPrimeSegments (by decide : 522977325 ≤ 523042861)
    (by decide : 523042861 ≤ 523108397) join_0_0 join_0_1

theorem total : (twinPrimeSegment 522977325 523108397).card = 401 := join_1_0

end S249C06
end Sude.GeneratedTwinScan
