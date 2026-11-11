import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S117C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15673)) 245628973 245661741 = 123 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 245628973 245661741).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15673 245628973 245661741
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15674)) 245661741 245694509 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 245661741 245694509).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15674 245661741 245694509
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15675)) 245694509 245727277 = 105 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 245694509 245727277).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15675 245694509 245727277
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15676)) 245727277 245760045 = 111 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 245727277 245760045).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15676 245727277 245760045
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 245628973 245694509).card = 241 := by
  simpa using combineTwinPrimeSegments (by decide : 245628973 ≤ 245661741)
    (by decide : 245661741 ≤ 245694509) block0 block1

theorem join_0_1 : (twinPrimeSegment 245694509 245760045).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 245694509 ≤ 245727277)
    (by decide : 245727277 ≤ 245760045) block2 block3

theorem join_1_0 : (twinPrimeSegment 245628973 245760045).card = 457 := by
  simpa using combineTwinPrimeSegments (by decide : 245628973 ≤ 245694509)
    (by decide : 245694509 ≤ 245760045) join_0_0 join_0_1

theorem total : (twinPrimeSegment 245628973 245760045).card = 457 := join_1_0

end S117C02
end Sude.GeneratedTwinScan
