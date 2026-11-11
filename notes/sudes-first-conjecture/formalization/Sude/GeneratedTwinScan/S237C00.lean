import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S237C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22294)) 497025069 497057837 = 105 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 497025069 497057837).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22294 497025069 497057837
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22295)) 497057837 497090605 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 497057837 497090605).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22295 497057837 497090605
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22296)) 497090605 497123373 = 107 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 497090605 497123373).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22296 497090605 497123373
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22296)) 497123373 497156141 = 111 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 497123373 497156141).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22296 497123373 497156141
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 497025069 497090605).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 497025069 ≤ 497057837)
    (by decide : 497057837 ≤ 497090605) block0 block1

theorem join_0_1 : (twinPrimeSegment 497090605 497156141).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 497090605 ≤ 497123373)
    (by decide : 497123373 ≤ 497156141) block2 block3

theorem join_1_0 : (twinPrimeSegment 497025069 497156141).card = 441 := by
  simpa using combineTwinPrimeSegments (by decide : 497025069 ≤ 497090605)
    (by decide : 497090605 ≤ 497156141) join_0_0 join_0_1

theorem total : (twinPrimeSegment 497025069 497156141).card = 441 := join_1_0

end S237C00
end Sude.GeneratedTwinScan
