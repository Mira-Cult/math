import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S156C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18095)) 327417901 327450669 = 112 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 327417901 327450669).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18095 327417901 327450669
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18096)) 327450669 327483437 = 127 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 327450669 327483437).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18096 327450669 327483437
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18097)) 327483437 327516205 = 123 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 327483437 327516205).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18097 327483437 327516205
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18098)) 327516205 327548973 = 117 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 327516205 327548973).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18098 327516205 327548973
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 327417901 327483437).card = 239 := by
  simpa using combineTwinPrimeSegments (by decide : 327417901 ≤ 327450669)
    (by decide : 327450669 ≤ 327483437) block0 block1

theorem join_0_1 : (twinPrimeSegment 327483437 327548973).card = 240 := by
  simpa using combineTwinPrimeSegments (by decide : 327483437 ≤ 327516205)
    (by decide : 327516205 ≤ 327548973) block2 block3

theorem join_1_0 : (twinPrimeSegment 327417901 327548973).card = 479 := by
  simpa using combineTwinPrimeSegments (by decide : 327417901 ≤ 327483437)
    (by decide : 327483437 ≤ 327548973) join_0_0 join_0_1

theorem total : (twinPrimeSegment 327417901 327548973).card = 479 := join_1_0

end S156C02
end Sude.GeneratedTwinScan
