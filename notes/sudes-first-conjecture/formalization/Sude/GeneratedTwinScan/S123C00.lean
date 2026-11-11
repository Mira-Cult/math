import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S123C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16061)) 257949741 257982509 = 111 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 257949741 257982509).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16061 257949741 257982509
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16062)) 257982509 258015277 = 120 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 257982509 258015277).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16062 257982509 258015277
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16063)) 258015277 258048045 = 119 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 258015277 258048045).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16063 258015277 258048045
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16064)) 258048045 258080813 = 103 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 258048045 258080813).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16064 258048045 258080813
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 257949741 258015277).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 257949741 ≤ 257982509)
    (by decide : 257982509 ≤ 258015277) block0 block1

theorem join_0_1 : (twinPrimeSegment 258015277 258080813).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 258015277 ≤ 258048045)
    (by decide : 258048045 ≤ 258080813) block2 block3

theorem join_1_0 : (twinPrimeSegment 257949741 258080813).card = 453 := by
  simpa using combineTwinPrimeSegments (by decide : 257949741 ≤ 258015277)
    (by decide : 258015277 ≤ 258080813) join_0_0 join_0_1

theorem total : (twinPrimeSegment 257949741 258080813).card = 453 := join_1_0

end S123C00
end Sude.GeneratedTwinScan
