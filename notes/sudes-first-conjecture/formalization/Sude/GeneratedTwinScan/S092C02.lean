import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S092C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13900)) 193200173 193232941 = 123 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 193200173 193232941).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13900 193200173 193232941
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13902)) 193232941 193265709 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 193232941 193265709).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13902 193232941 193265709
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13903)) 193265709 193298477 = 137 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 193265709 193298477).card = 137 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13903 193265709 193298477
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13904)) 193298477 193331245 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 193298477 193331245).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13904 193298477 193331245
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 193200173 193265709).card = 241 := by
  simpa using combineTwinPrimeSegments (by decide : 193200173 ≤ 193232941)
    (by decide : 193232941 ≤ 193265709) block0 block1

theorem join_0_1 : (twinPrimeSegment 193265709 193331245).card = 251 := by
  simpa using combineTwinPrimeSegments (by decide : 193265709 ≤ 193298477)
    (by decide : 193298477 ≤ 193331245) block2 block3

theorem join_1_0 : (twinPrimeSegment 193200173 193331245).card = 492 := by
  simpa using combineTwinPrimeSegments (by decide : 193200173 ≤ 193265709)
    (by decide : 193265709 ≤ 193331245) join_0_0 join_0_1

theorem total : (twinPrimeSegment 193200173 193331245).card = 492 := join_1_0

end S092C02
end Sude.GeneratedTwinScan
