import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S120C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15893)) 252575789 252608557 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 252575789 252608557).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15893 252575789 252608557
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15894)) 252608557 252641325 = 125 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 252608557 252641325).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15894 252608557 252641325
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15895)) 252641325 252674093 = 109 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 252641325 252674093).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15895 252641325 252674093
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15896)) 252674093 252706861 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 252674093 252706861).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15896 252674093 252706861
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 252575789 252641325).card = 240 := by
  simpa using combineTwinPrimeSegments (by decide : 252575789 ≤ 252608557)
    (by decide : 252608557 ≤ 252641325) block0 block1

theorem join_0_1 : (twinPrimeSegment 252641325 252706861).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 252641325 ≤ 252674093)
    (by decide : 252674093 ≤ 252706861) block2 block3

theorem join_1_0 : (twinPrimeSegment 252575789 252706861).card = 468 := by
  simpa using combineTwinPrimeSegments (by decide : 252575789 ≤ 252641325)
    (by decide : 252641325 ≤ 252706861) join_0_0 join_0_1

theorem total : (twinPrimeSegment 252575789 252706861).card = 468 := join_1_0

end S120C07
end Sude.GeneratedTwinScan
