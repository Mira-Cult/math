import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S189C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19929)) 397148205 397180973 = 114 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 397148205 397180973).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19929 397148205 397180973
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19930)) 397180973 397213741 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 397180973 397213741).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19930 397180973 397213741
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19931)) 397213741 397246509 = 104 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 397213741 397246509).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19931 397213741 397246509
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19931)) 397246509 397279277 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 397246509 397279277).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19931 397246509 397279277
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 397148205 397213741).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 397148205 ≤ 397180973)
    (by decide : 397180973 ≤ 397213741) block0 block1

theorem join_0_1 : (twinPrimeSegment 397213741 397279277).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 397213741 ≤ 397246509)
    (by decide : 397246509 ≤ 397279277) block2 block3

theorem join_1_0 : (twinPrimeSegment 397148205 397279277).card = 446 := by
  simpa using combineTwinPrimeSegments (by decide : 397148205 ≤ 397213741)
    (by decide : 397213741 ≤ 397279277) join_0_0 join_0_1

theorem total : (twinPrimeSegment 397148205 397279277).card = 446 := join_1_0

end S189C06
end Sude.GeneratedTwinScan
