import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S184C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19671)) 386924589 386957357 = 117 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 386924589 386957357).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19671 386924589 386957357
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19672)) 386957357 386990125 = 125 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 386957357 386990125).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19672 386957357 386990125
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19672)) 386990125 387022893 = 97 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 386990125 387022893).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19672 386990125 387022893
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19673)) 387022893 387055661 = 111 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 387022893 387055661).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19673 387022893 387055661
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 386924589 386990125).card = 242 := by
  simpa using combineTwinPrimeSegments (by decide : 386924589 ≤ 386957357)
    (by decide : 386957357 ≤ 386990125) block0 block1

theorem join_0_1 : (twinPrimeSegment 386990125 387055661).card = 208 := by
  simpa using combineTwinPrimeSegments (by decide : 386990125 ≤ 387022893)
    (by decide : 387022893 ≤ 387055661) block2 block3

theorem join_1_0 : (twinPrimeSegment 386924589 387055661).card = 450 := by
  simpa using combineTwinPrimeSegments (by decide : 386924589 ≤ 386990125)
    (by decide : 386990125 ≤ 387055661) join_0_0 join_0_1

theorem total : (twinPrimeSegment 386924589 387055661).card = 450 := join_1_0

end S184C08
end Sude.GeneratedTwinScan
