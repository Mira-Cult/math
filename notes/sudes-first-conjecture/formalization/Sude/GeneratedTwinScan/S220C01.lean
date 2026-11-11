import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S220C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21483)) 461504557 461537325 = 116 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 461504557 461537325).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21483 461504557 461537325
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21484)) 461537325 461570093 = 109 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 461537325 461570093).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21484 461537325 461570093
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21484)) 461570093 461602861 = 97 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 461570093 461602861).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21484 461570093 461602861
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21485)) 461602861 461635629 = 125 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 461602861 461635629).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21485 461602861 461635629
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 461504557 461570093).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 461504557 ≤ 461537325)
    (by decide : 461537325 ≤ 461570093) block0 block1

theorem join_0_1 : (twinPrimeSegment 461570093 461635629).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 461570093 ≤ 461602861)
    (by decide : 461602861 ≤ 461635629) block2 block3

theorem join_1_0 : (twinPrimeSegment 461504557 461635629).card = 447 := by
  simpa using combineTwinPrimeSegments (by decide : 461504557 ≤ 461570093)
    (by decide : 461570093 ≤ 461635629) join_0_0 join_0_1

theorem total : (twinPrimeSegment 461504557 461635629).card = 447 := join_1_0

end S220C01
end Sude.GeneratedTwinScan
