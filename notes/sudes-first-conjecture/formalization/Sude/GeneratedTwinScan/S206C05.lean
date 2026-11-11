import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S206C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20801)) 432668717 432701485 = 98 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 432668717 432701485).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20801 432668717 432701485
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20802)) 432701485 432734253 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 432701485 432734253).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20802 432701485 432734253
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20803)) 432734253 432767021 = 108 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 432734253 432767021).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20803 432734253 432767021
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20803)) 432767021 432799789 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 432767021 432799789).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20803 432767021 432799789
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 432668717 432734253).card = 209 := by
  simpa using combineTwinPrimeSegments (by decide : 432668717 ≤ 432701485)
    (by decide : 432701485 ≤ 432734253) block0 block1

theorem join_0_1 : (twinPrimeSegment 432734253 432799789).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 432734253 ≤ 432767021)
    (by decide : 432767021 ≤ 432799789) block2 block3

theorem join_1_0 : (twinPrimeSegment 432668717 432799789).card = 431 := by
  simpa using combineTwinPrimeSegments (by decide : 432668717 ≤ 432734253)
    (by decide : 432734253 ≤ 432799789) join_0_0 join_0_1

theorem total : (twinPrimeSegment 432668717 432799789).card = 431 := join_1_0

end S206C05
end Sude.GeneratedTwinScan
