import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S243C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22595)) 510525485 510558253 = 121 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 510525485 510558253).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22595 510525485 510558253
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22596)) 510558253 510591021 = 120 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 510558253 510591021).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22596 510558253 510591021
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22596)) 510591021 510623789 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 510591021 510623789).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22596 510591021 510623789
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22597)) 510623789 510656557 = 98 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 510623789 510656557).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22597 510623789 510656557
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 510525485 510591021).card = 241 := by
  simpa using combineTwinPrimeSegments (by decide : 510525485 ≤ 510558253)
    (by decide : 510558253 ≤ 510591021) block0 block1

theorem join_0_1 : (twinPrimeSegment 510591021 510656557).card = 211 := by
  simpa using combineTwinPrimeSegments (by decide : 510591021 ≤ 510623789)
    (by decide : 510623789 ≤ 510656557) block2 block3

theorem join_1_0 : (twinPrimeSegment 510525485 510656557).card = 452 := by
  simpa using combineTwinPrimeSegments (by decide : 510525485 ≤ 510591021)
    (by decide : 510591021 ≤ 510656557) join_0_0 join_0_1

theorem total : (twinPrimeSegment 510525485 510656557).card = 452 := join_1_0

end S243C07
end Sude.GeneratedTwinScan
