import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S109C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15120)) 228589613 228622381 = 116 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 228589613 228622381).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15120 228589613 228622381
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15121)) 228622381 228655149 = 124 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 228622381 228655149).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15121 228622381 228655149
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15122)) 228655149 228687917 = 125 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 228655149 228687917).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15122 228655149 228687917
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15123)) 228687917 228720685 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 228687917 228720685).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15123 228687917 228720685
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 228589613 228655149).card = 240 := by
  simpa using combineTwinPrimeSegments (by decide : 228589613 ≤ 228622381)
    (by decide : 228622381 ≤ 228655149) block0 block1

theorem join_0_1 : (twinPrimeSegment 228655149 228720685).card = 237 := by
  simpa using combineTwinPrimeSegments (by decide : 228655149 ≤ 228687917)
    (by decide : 228687917 ≤ 228720685) block2 block3

theorem join_1_0 : (twinPrimeSegment 228589613 228720685).card = 477 := by
  simpa using combineTwinPrimeSegments (by decide : 228589613 ≤ 228655149)
    (by decide : 228655149 ≤ 228720685) join_0_0 join_0_1

theorem total : (twinPrimeSegment 228589613 228720685).card = 477 := join_1_0

end S109C00
end Sude.GeneratedTwinScan
