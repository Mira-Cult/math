import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S231C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22031)) 485359661 485392429 = 98 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 485359661 485392429).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22031 485359661 485392429
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22032)) 485392429 485425197 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 485392429 485425197).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22032 485392429 485425197
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22033)) 485425197 485457965 = 107 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 485425197 485457965).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22033 485425197 485457965
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22033)) 485457965 485490733 = 113 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 485457965 485490733).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22033 485457965 485490733
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 485359661 485425197).card = 211 := by
  simpa using combineTwinPrimeSegments (by decide : 485359661 ≤ 485392429)
    (by decide : 485392429 ≤ 485425197) block0 block1

theorem join_0_1 : (twinPrimeSegment 485425197 485490733).card = 220 := by
  simpa using combineTwinPrimeSegments (by decide : 485425197 ≤ 485457965)
    (by decide : 485457965 ≤ 485490733) block2 block3

theorem join_1_0 : (twinPrimeSegment 485359661 485490733).card = 431 := by
  simpa using combineTwinPrimeSegments (by decide : 485359661 ≤ 485425197)
    (by decide : 485425197 ≤ 485490733) join_0_0 join_0_1

theorem total : (twinPrimeSegment 485359661 485490733).card = 431 := join_1_0

end S231C07
end Sude.GeneratedTwinScan
