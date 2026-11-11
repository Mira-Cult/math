import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S246C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22717)) 516030509 516063277 = 111 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 516030509 516063277).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22717 516030509 516063277
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22717)) 516063277 516096045 = 101 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 516063277 516096045).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22717 516063277 516096045
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22718)) 516096045 516128813 = 119 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 516096045 516128813).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22718 516096045 516128813
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22719)) 516128813 516161581 = 113 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 516128813 516161581).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22719 516128813 516161581
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 516030509 516096045).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 516030509 ≤ 516063277)
    (by decide : 516063277 ≤ 516096045) block0 block1

theorem join_0_1 : (twinPrimeSegment 516096045 516161581).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 516096045 ≤ 516128813)
    (by decide : 516128813 ≤ 516161581) block2 block3

theorem join_1_0 : (twinPrimeSegment 516030509 516161581).card = 444 := by
  simpa using combineTwinPrimeSegments (by decide : 516030509 ≤ 516096045)
    (by decide : 516096045 ≤ 516161581) join_0_0 join_0_1

theorem total : (twinPrimeSegment 516030509 516161581).card = 444 := join_1_0

end S246C01
end Sude.GeneratedTwinScan
