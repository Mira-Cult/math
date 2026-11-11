import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S152C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17854)) 318767149 318799917 = 106 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 318767149 318799917).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17854 318767149 318799917
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17855)) 318799917 318832685 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 318799917 318832685).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17855 318799917 318832685
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17856)) 318832685 318865453 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 318832685 318865453).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17856 318832685 318865453
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17857)) 318865453 318898221 = 127 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 318865453 318898221).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17857 318865453 318898221
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 318767149 318832685).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 318767149 ≤ 318799917)
    (by decide : 318799917 ≤ 318832685) block0 block1

theorem join_0_1 : (twinPrimeSegment 318832685 318898221).card = 240 := by
  simpa using combineTwinPrimeSegments (by decide : 318832685 ≤ 318865453)
    (by decide : 318865453 ≤ 318898221) block2 block3

theorem join_1_0 : (twinPrimeSegment 318767149 318898221).card = 458 := by
  simpa using combineTwinPrimeSegments (by decide : 318767149 ≤ 318832685)
    (by decide : 318832685 ≤ 318898221) join_0_0 join_0_1

theorem total : (twinPrimeSegment 318767149 318898221).card = 458 := join_1_0

end S152C00
end Sude.GeneratedTwinScan
