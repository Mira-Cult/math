import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S079C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12877)) 165806125 165838893 = 123 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 165806125 165838893).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12877 165806125 165838893
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12879)) 165838893 165871661 = 132 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 165838893 165871661).card = 132 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12879 165838893 165871661
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12880)) 165871661 165904429 = 121 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 165871661 165904429).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12880 165871661 165904429
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12881)) 165904429 165937197 = 136 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 165904429 165937197).card = 136 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12881 165904429 165937197
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 165806125 165871661).card = 255 := by
  simpa using combineTwinPrimeSegments (by decide : 165806125 ≤ 165838893)
    (by decide : 165838893 ≤ 165871661) block0 block1

theorem join_0_1 : (twinPrimeSegment 165871661 165937197).card = 257 := by
  simpa using combineTwinPrimeSegments (by decide : 165871661 ≤ 165904429)
    (by decide : 165904429 ≤ 165937197) block2 block3

theorem join_1_0 : (twinPrimeSegment 165806125 165937197).card = 512 := by
  simpa using combineTwinPrimeSegments (by decide : 165806125 ≤ 165871661)
    (by decide : 165871661 ≤ 165937197) join_0_0 join_0_1

theorem total : (twinPrimeSegment 165806125 165937197).card = 512 := join_1_0

end S079C01
end Sude.GeneratedTwinScan
