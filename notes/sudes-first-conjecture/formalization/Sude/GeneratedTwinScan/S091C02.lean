import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S091C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13825)) 191103021 191135789 = 126 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 191103021 191135789).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13825 191103021 191135789
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13826)) 191135789 191168557 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 191135789 191168557).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13826 191135789 191168557
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13827)) 191168557 191201325 = 119 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 191168557 191201325).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13827 191168557 191201325
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13828)) 191201325 191234093 = 118 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 191201325 191234093).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13828 191201325 191234093
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 191103021 191168557).card = 244 := by
  simpa using combineTwinPrimeSegments (by decide : 191103021 ≤ 191135789)
    (by decide : 191135789 ≤ 191168557) block0 block1

theorem join_0_1 : (twinPrimeSegment 191168557 191234093).card = 237 := by
  simpa using combineTwinPrimeSegments (by decide : 191168557 ≤ 191201325)
    (by decide : 191201325 ≤ 191234093) block2 block3

theorem join_1_0 : (twinPrimeSegment 191103021 191234093).card = 481 := by
  simpa using combineTwinPrimeSegments (by decide : 191103021 ≤ 191168557)
    (by decide : 191168557 ≤ 191234093) join_0_0 join_0_1

theorem total : (twinPrimeSegment 191103021 191234093).card = 481 := join_1_0

end S091C02
end Sude.GeneratedTwinScan
