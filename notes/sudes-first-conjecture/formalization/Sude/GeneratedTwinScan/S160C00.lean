import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S160C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18318)) 335544365 335577133 = 124 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 335544365 335577133).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18318 335544365 335577133
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18319)) 335577133 335609901 = 97 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 335577133 335609901).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18319 335577133 335609901
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18320)) 335609901 335642669 = 120 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 335609901 335642669).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18320 335609901 335642669
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18321)) 335642669 335675437 = 97 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 335642669 335675437).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18321 335642669 335675437
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 335544365 335609901).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 335544365 ≤ 335577133)
    (by decide : 335577133 ≤ 335609901) block0 block1

theorem join_0_1 : (twinPrimeSegment 335609901 335675437).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 335609901 ≤ 335642669)
    (by decide : 335642669 ≤ 335675437) block2 block3

theorem join_1_0 : (twinPrimeSegment 335544365 335675437).card = 438 := by
  simpa using combineTwinPrimeSegments (by decide : 335544365 ≤ 335609901)
    (by decide : 335609901 ≤ 335675437) join_0_0 join_0_1

theorem total : (twinPrimeSegment 335544365 335675437).card = 438 := join_1_0

end S160C00
end Sude.GeneratedTwinScan
