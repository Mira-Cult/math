import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S191C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20034)) 401342509 401375277 = 102 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 401342509 401375277).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20034 401342509 401375277
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20035)) 401375277 401408045 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 401375277 401408045).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20035 401375277 401408045
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20035)) 401408045 401440813 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 401408045 401440813).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20035 401408045 401440813
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20036)) 401440813 401473581 = 105 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 401440813 401473581).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20036 401440813 401473581
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 401342509 401408045).card = 210 := by
  simpa using combineTwinPrimeSegments (by decide : 401342509 ≤ 401375277)
    (by decide : 401375277 ≤ 401408045) block0 block1

theorem join_0_1 : (twinPrimeSegment 401408045 401473581).card = 220 := by
  simpa using combineTwinPrimeSegments (by decide : 401408045 ≤ 401440813)
    (by decide : 401440813 ≤ 401473581) block2 block3

theorem join_1_0 : (twinPrimeSegment 401342509 401473581).card = 430 := by
  simpa using combineTwinPrimeSegments (by decide : 401342509 ≤ 401408045)
    (by decide : 401408045 ≤ 401473581) join_0_0 join_0_1

theorem total : (twinPrimeSegment 401342509 401473581).card = 430 := join_1_0

end S191C06
end Sude.GeneratedTwinScan
