import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S224C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21689)) 470417453 470450221 = 104 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 470417453 470450221).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21689 470417453 470450221
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21690)) 470450221 470482989 = 117 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 470450221 470482989).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21690 470450221 470482989
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21691)) 470482989 470515757 = 118 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 470482989 470515757).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21691 470482989 470515757
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21692)) 470515757 470548525 = 106 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 470515757 470548525).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21692 470515757 470548525
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 470417453 470482989).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 470417453 ≤ 470450221)
    (by decide : 470450221 ≤ 470482989) block0 block1

theorem join_0_1 : (twinPrimeSegment 470482989 470548525).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 470482989 ≤ 470515757)
    (by decide : 470515757 ≤ 470548525) block2 block3

theorem join_1_0 : (twinPrimeSegment 470417453 470548525).card = 445 := by
  simpa using combineTwinPrimeSegments (by decide : 470417453 ≤ 470482989)
    (by decide : 470482989 ≤ 470548525) join_0_0 join_0_1

theorem total : (twinPrimeSegment 470417453 470548525).card = 445 := join_1_0

end S224C05
end Sude.GeneratedTwinScan
