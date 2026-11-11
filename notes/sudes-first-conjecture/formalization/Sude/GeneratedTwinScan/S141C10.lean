import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S141C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17234)) 297009197 297041965 = 97 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 297009197 297041965).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17234 297009197 297041965
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17235)) 297041965 297074733 = 133 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 297041965 297074733).card = 133 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17235 297041965 297074733
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17236)) 297074733 297107501 = 107 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 297074733 297107501).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17236 297074733 297107501
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17237)) 297107501 297140269 = 101 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 297107501 297140269).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17237 297107501 297140269
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 297009197 297074733).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 297009197 ≤ 297041965)
    (by decide : 297041965 ≤ 297074733) block0 block1

theorem join_0_1 : (twinPrimeSegment 297074733 297140269).card = 208 := by
  simpa using combineTwinPrimeSegments (by decide : 297074733 ≤ 297107501)
    (by decide : 297107501 ≤ 297140269) block2 block3

theorem join_1_0 : (twinPrimeSegment 297009197 297140269).card = 438 := by
  simpa using combineTwinPrimeSegments (by decide : 297009197 ≤ 297074733)
    (by decide : 297074733 ≤ 297140269) join_0_0 join_0_1

theorem total : (twinPrimeSegment 297009197 297140269).card = 438 := join_1_0

end S141C10
end Sude.GeneratedTwinScan
