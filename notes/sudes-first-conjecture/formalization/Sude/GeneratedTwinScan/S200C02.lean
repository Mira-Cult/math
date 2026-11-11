import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S200C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20487)) 419692589 419725357 = 104 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 419692589 419725357).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20487 419692589 419725357
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20487)) 419725357 419758125 = 109 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 419725357 419758125).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20487 419725357 419758125
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20488)) 419758125 419790893 = 136 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 419758125 419790893).card = 136 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20488 419758125 419790893
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20489)) 419790893 419823661 = 131 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 419790893 419823661).card = 131 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20489 419790893 419823661
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 419692589 419758125).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 419692589 ≤ 419725357)
    (by decide : 419725357 ≤ 419758125) block0 block1

theorem join_0_1 : (twinPrimeSegment 419758125 419823661).card = 267 := by
  simpa using combineTwinPrimeSegments (by decide : 419758125 ≤ 419790893)
    (by decide : 419790893 ≤ 419823661) block2 block3

theorem join_1_0 : (twinPrimeSegment 419692589 419823661).card = 480 := by
  simpa using combineTwinPrimeSegments (by decide : 419692589 ≤ 419758125)
    (by decide : 419758125 ≤ 419823661) join_0_0 join_0_1

theorem total : (twinPrimeSegment 419692589 419823661).card = 480 := join_1_0

end S200C02
end Sude.GeneratedTwinScan
