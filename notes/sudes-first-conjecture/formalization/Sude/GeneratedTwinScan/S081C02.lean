import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S081C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13044)) 170131501 170164269 = 116 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 170131501 170164269).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13044 170131501 170164269
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13045)) 170164269 170197037 = 102 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 170164269 170197037).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13045 170164269 170197037
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13047)) 170197037 170229805 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 170197037 170229805).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13047 170197037 170229805
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13048)) 170229805 170262573 = 92 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 170229805 170262573).card = 92 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13048 170229805 170262573
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 170131501 170197037).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 170131501 ≤ 170164269)
    (by decide : 170164269 ≤ 170197037) block0 block1

theorem join_0_1 : (twinPrimeSegment 170197037 170262573).card = 206 := by
  simpa using combineTwinPrimeSegments (by decide : 170197037 ≤ 170229805)
    (by decide : 170229805 ≤ 170262573) block2 block3

theorem join_1_0 : (twinPrimeSegment 170131501 170262573).card = 424 := by
  simpa using combineTwinPrimeSegments (by decide : 170131501 ≤ 170197037)
    (by decide : 170197037 ≤ 170262573) join_0_0 join_0_1

theorem total : (twinPrimeSegment 170131501 170262573).card = 424 := join_1_0

end S081C02
end Sude.GeneratedTwinScan
