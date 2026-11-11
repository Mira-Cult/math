import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S201C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20541)) 421920813 421953581 = 112 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 421920813 421953581).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20541 421920813 421953581
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20542)) 421953581 421986349 = 102 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 421953581 421986349).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20542 421953581 421986349
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20543)) 421986349 422019117 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 421986349 422019117).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20543 421986349 422019117
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20543)) 422019117 422051885 = 108 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 422019117 422051885).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20543 422019117 422051885
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 421920813 421986349).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 421920813 ≤ 421953581)
    (by decide : 421953581 ≤ 421986349) block0 block1

theorem join_0_1 : (twinPrimeSegment 421986349 422051885).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 421986349 ≤ 422019117)
    (by decide : 422019117 ≤ 422051885) block2 block3

theorem join_1_0 : (twinPrimeSegment 421920813 422051885).card = 438 := by
  simpa using combineTwinPrimeSegments (by decide : 421920813 ≤ 421986349)
    (by decide : 421986349 ≤ 422051885) join_0_0 join_0_1

theorem total : (twinPrimeSegment 421920813 422051885).card = 438 := join_1_0

end S201C03
end Sude.GeneratedTwinScan
