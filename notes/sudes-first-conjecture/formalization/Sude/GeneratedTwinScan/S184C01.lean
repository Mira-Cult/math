import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S184C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19647)) 386007085 386039853 = 99 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 386007085 386039853).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19647 386007085 386039853
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19648)) 386039853 386072621 = 103 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 386039853 386072621).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19648 386039853 386072621
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19649)) 386072621 386105389 = 109 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 386072621 386105389).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19649 386072621 386105389
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19650)) 386105389 386138157 = 129 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 386105389 386138157).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19650 386105389 386138157
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 386007085 386072621).card = 202 := by
  simpa using combineTwinPrimeSegments (by decide : 386007085 ≤ 386039853)
    (by decide : 386039853 ≤ 386072621) block0 block1

theorem join_0_1 : (twinPrimeSegment 386072621 386138157).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 386072621 ≤ 386105389)
    (by decide : 386105389 ≤ 386138157) block2 block3

theorem join_1_0 : (twinPrimeSegment 386007085 386138157).card = 440 := by
  simpa using combineTwinPrimeSegments (by decide : 386007085 ≤ 386072621)
    (by decide : 386072621 ≤ 386138157) join_0_0 join_0_1

theorem total : (twinPrimeSegment 386007085 386138157).card = 440 := join_1_0

end S184C01
end Sude.GeneratedTwinScan
