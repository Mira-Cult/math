import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S076C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12626)) 159383597 159416365 = 101 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 159383597 159416365).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12626 159383597 159416365
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12627)) 159416365 159449133 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 159416365 159449133).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12627 159416365 159449133
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12628)) 159449133 159481901 = 137 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 159449133 159481901).card = 137 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12628 159449133 159481901
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12629)) 159481901 159514669 = 104 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 159481901 159514669).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12629 159481901 159514669
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 159383597 159449133).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 159383597 ≤ 159416365)
    (by decide : 159416365 ≤ 159449133) block0 block1

theorem join_0_1 : (twinPrimeSegment 159449133 159514669).card = 241 := by
  simpa using combineTwinPrimeSegments (by decide : 159449133 ≤ 159481901)
    (by decide : 159481901 ≤ 159514669) block2 block3

theorem join_1_0 : (twinPrimeSegment 159383597 159514669).card = 458 := by
  simpa using combineTwinPrimeSegments (by decide : 159383597 ≤ 159449133)
    (by decide : 159449133 ≤ 159514669) join_0_0 join_0_1

theorem total : (twinPrimeSegment 159383597 159514669).card = 458 := join_1_0

end S076C00
end Sude.GeneratedTwinScan
