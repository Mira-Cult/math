import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S168C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18795)) 353239085 353271853 = 102 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 353239085 353271853).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18795 353239085 353271853
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18796)) 353271853 353304621 = 127 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 353271853 353304621).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18796 353271853 353304621
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18797)) 353304621 353337389 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 353304621 353337389).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18797 353304621 353337389
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18798)) 353337389 353370157 = 96 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 353337389 353370157).card = 96 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18798 353337389 353370157
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 353239085 353304621).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 353239085 ≤ 353271853)
    (by decide : 353271853 ≤ 353304621) block0 block1

theorem join_0_1 : (twinPrimeSegment 353304621 353370157).card = 208 := by
  simpa using combineTwinPrimeSegments (by decide : 353304621 ≤ 353337389)
    (by decide : 353337389 ≤ 353370157) block2 block3

theorem join_1_0 : (twinPrimeSegment 353239085 353370157).card = 437 := by
  simpa using combineTwinPrimeSegments (by decide : 353239085 ≤ 353304621)
    (by decide : 353304621 ≤ 353370157) join_0_0 join_0_1

theorem total : (twinPrimeSegment 353239085 353370157).card = 437 := join_1_0

end S168C07
end Sude.GeneratedTwinScan
