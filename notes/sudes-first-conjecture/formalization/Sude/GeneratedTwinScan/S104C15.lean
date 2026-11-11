import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S104C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14835)) 220069933 220102701 = 112 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 220069933 220102701).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14835 220069933 220102701
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14836)) 220102701 220135469 = 128 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 220102701 220135469).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14836 220102701 220135469
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14838)) 220135469 220168237 = 121 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 220135469 220168237).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14838 220135469 220168237
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14839)) 220168237 220201005 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 220168237 220201005).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14839 220168237 220201005
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 220069933 220135469).card = 240 := by
  simpa using combineTwinPrimeSegments (by decide : 220069933 ≤ 220102701)
    (by decide : 220102701 ≤ 220135469) block0 block1

theorem join_0_1 : (twinPrimeSegment 220135469 220201005).card = 236 := by
  simpa using combineTwinPrimeSegments (by decide : 220135469 ≤ 220168237)
    (by decide : 220168237 ≤ 220201005) block2 block3

theorem join_1_0 : (twinPrimeSegment 220069933 220201005).card = 476 := by
  simpa using combineTwinPrimeSegments (by decide : 220069933 ≤ 220135469)
    (by decide : 220135469 ≤ 220201005) join_0_0 join_0_1

theorem total : (twinPrimeSegment 220069933 220201005).card = 476 := join_1_0

end S104C15
end Sude.GeneratedTwinScan
