import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S221C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21529)) 463470637 463503405 = 95 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 463470637 463503405).card = 95 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21529 463470637 463503405
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21529)) 463503405 463536173 = 117 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 463503405 463536173).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21529 463503405 463536173
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21530)) 463536173 463568941 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 463536173 463568941).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21530 463536173 463568941
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21531)) 463568941 463601709 = 106 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 463568941 463601709).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21531 463568941 463601709
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 463470637 463536173).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 463470637 ≤ 463503405)
    (by decide : 463503405 ≤ 463536173) block0 block1

theorem join_0_1 : (twinPrimeSegment 463536173 463601709).card = 220 := by
  simpa using combineTwinPrimeSegments (by decide : 463536173 ≤ 463568941)
    (by decide : 463568941 ≤ 463601709) block2 block3

theorem join_1_0 : (twinPrimeSegment 463470637 463601709).card = 432 := by
  simpa using combineTwinPrimeSegments (by decide : 463470637 ≤ 463536173)
    (by decide : 463536173 ≤ 463601709) join_0_0 join_0_1

theorem total : (twinPrimeSegment 463470637 463601709).card = 432 := join_1_0

end S221C00
end Sude.GeneratedTwinScan
