import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S130C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16560)) 274202669 274235437 = 128 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 274202669 274235437).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16560 274202669 274235437
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16561)) 274235437 274268205 = 122 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 274235437 274268205).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16561 274235437 274268205
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16562)) 274268205 274300973 = 119 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 274268205 274300973).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16562 274268205 274300973
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16563)) 274300973 274333741 = 121 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 274300973 274333741).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16563 274300973 274333741
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 274202669 274268205).card = 250 := by
  simpa using combineTwinPrimeSegments (by decide : 274202669 ≤ 274235437)
    (by decide : 274235437 ≤ 274268205) block0 block1

theorem join_0_1 : (twinPrimeSegment 274268205 274333741).card = 240 := by
  simpa using combineTwinPrimeSegments (by decide : 274268205 ≤ 274300973)
    (by decide : 274300973 ≤ 274333741) block2 block3

theorem join_1_0 : (twinPrimeSegment 274202669 274333741).card = 490 := by
  simpa using combineTwinPrimeSegments (by decide : 274202669 ≤ 274268205)
    (by decide : 274268205 ≤ 274333741) join_0_0 join_0_1

theorem total : (twinPrimeSegment 274202669 274333741).card = 490 := join_1_0

end S130C12
end Sude.GeneratedTwinScan
