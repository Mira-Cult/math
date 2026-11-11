import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S075C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12558)) 157679661 157712429 = 124 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 157679661 157712429).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12558 157679661 157712429
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12559)) 157712429 157745197 = 140 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 157712429 157745197).card = 140 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12559 157712429 157745197
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12560)) 157745197 157777965 = 108 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 157745197 157777965).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12560 157745197 157777965
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12562)) 157777965 157810733 = 121 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 157777965 157810733).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12562 157777965 157810733
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 157679661 157745197).card = 264 := by
  simpa using combineTwinPrimeSegments (by decide : 157679661 ≤ 157712429)
    (by decide : 157712429 ≤ 157745197) block0 block1

theorem join_0_1 : (twinPrimeSegment 157745197 157810733).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 157745197 ≤ 157777965)
    (by decide : 157777965 ≤ 157810733) block2 block3

theorem join_1_0 : (twinPrimeSegment 157679661 157810733).card = 493 := by
  simpa using combineTwinPrimeSegments (by decide : 157679661 ≤ 157745197)
    (by decide : 157745197 ≤ 157810733) join_0_0 join_0_1

theorem total : (twinPrimeSegment 157679661 157810733).card = 493 := join_1_0

end S075C03
end Sude.GeneratedTwinScan
