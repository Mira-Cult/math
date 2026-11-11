import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S076C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12631)) 159514669 159547437 = 136 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 159514669 159547437).card = 136 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12631 159514669 159547437
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12632)) 159547437 159580205 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 159547437 159580205).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12632 159547437 159580205
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12633)) 159580205 159612973 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 159580205 159612973).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12633 159580205 159612973
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12635)) 159612973 159645741 = 103 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 159612973 159645741).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12635 159612973 159645741
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 159514669 159580205).card = 254 := by
  simpa using combineTwinPrimeSegments (by decide : 159514669 ≤ 159547437)
    (by decide : 159547437 ≤ 159580205) block0 block1

theorem join_0_1 : (twinPrimeSegment 159580205 159645741).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 159580205 ≤ 159612973)
    (by decide : 159612973 ≤ 159645741) block2 block3

theorem join_1_0 : (twinPrimeSegment 159514669 159645741).card = 472 := by
  simpa using combineTwinPrimeSegments (by decide : 159514669 ≤ 159580205)
    (by decide : 159580205 ≤ 159645741) join_0_0 join_0_1

theorem total : (twinPrimeSegment 159514669 159645741).card = 472 := join_1_0

end S076C01
end Sude.GeneratedTwinScan
