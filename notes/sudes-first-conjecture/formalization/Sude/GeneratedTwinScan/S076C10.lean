import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S076C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12677)) 160694317 160727085 = 133 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 160694317 160727085).card = 133 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12677 160694317 160727085
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12679)) 160727085 160759853 = 102 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 160727085 160759853).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12679 160727085 160759853
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12680)) 160759853 160792621 = 123 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 160759853 160792621).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12680 160759853 160792621
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12681)) 160792621 160825389 = 130 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 160792621 160825389).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12681 160792621 160825389
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 160694317 160759853).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 160694317 ≤ 160727085)
    (by decide : 160727085 ≤ 160759853) block0 block1

theorem join_0_1 : (twinPrimeSegment 160759853 160825389).card = 253 := by
  simpa using combineTwinPrimeSegments (by decide : 160759853 ≤ 160792621)
    (by decide : 160792621 ≤ 160825389) block2 block3

theorem join_1_0 : (twinPrimeSegment 160694317 160825389).card = 488 := by
  simpa using combineTwinPrimeSegments (by decide : 160694317 ≤ 160759853)
    (by decide : 160759853 ≤ 160825389) join_0_0 join_0_1

theorem total : (twinPrimeSegment 160694317 160825389).card = 488 := join_1_0

end S076C10
end Sude.GeneratedTwinScan
