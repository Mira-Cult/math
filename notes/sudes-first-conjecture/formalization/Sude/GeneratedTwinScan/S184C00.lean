import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S184C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19644)) 385876013 385908781 = 106 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 385876013 385908781).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19644 385876013 385908781
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19645)) 385908781 385941549 = 106 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 385908781 385941549).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19645 385908781 385941549
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19646)) 385941549 385974317 = 119 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 385941549 385974317).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19646 385941549 385974317
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19647)) 385974317 386007085 = 91 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 385974317 386007085).card = 91 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19647 385974317 386007085
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 385876013 385941549).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 385876013 ≤ 385908781)
    (by decide : 385908781 ≤ 385941549) block0 block1

theorem join_0_1 : (twinPrimeSegment 385941549 386007085).card = 210 := by
  simpa using combineTwinPrimeSegments (by decide : 385941549 ≤ 385974317)
    (by decide : 385974317 ≤ 386007085) block2 block3

theorem join_1_0 : (twinPrimeSegment 385876013 386007085).card = 422 := by
  simpa using combineTwinPrimeSegments (by decide : 385876013 ≤ 385941549)
    (by decide : 385941549 ≤ 386007085) join_0_0 join_0_1

theorem total : (twinPrimeSegment 385876013 386007085).card = 422 := join_1_0

end S184C00
end Sude.GeneratedTwinScan
