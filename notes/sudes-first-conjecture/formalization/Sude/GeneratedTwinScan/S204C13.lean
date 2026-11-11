import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S204C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20725)) 429522989 429555757 = 122 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 429522989 429555757).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20725 429522989 429555757
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20726)) 429555757 429588525 = 102 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 429555757 429588525).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20726 429555757 429588525
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20727)) 429588525 429621293 = 105 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 429588525 429621293).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20727 429588525 429621293
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20728)) 429621293 429654061 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 429621293 429654061).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20728 429621293 429654061
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 429522989 429588525).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 429522989 ≤ 429555757)
    (by decide : 429555757 ≤ 429588525) block0 block1

theorem join_0_1 : (twinPrimeSegment 429588525 429654061).card = 219 := by
  simpa using combineTwinPrimeSegments (by decide : 429588525 ≤ 429621293)
    (by decide : 429621293 ≤ 429654061) block2 block3

theorem join_1_0 : (twinPrimeSegment 429522989 429654061).card = 443 := by
  simpa using combineTwinPrimeSegments (by decide : 429522989 ≤ 429588525)
    (by decide : 429588525 ≤ 429654061) join_0_0 join_0_1

theorem total : (twinPrimeSegment 429522989 429654061).card = 443 := join_1_0

end S204C13
end Sude.GeneratedTwinScan
