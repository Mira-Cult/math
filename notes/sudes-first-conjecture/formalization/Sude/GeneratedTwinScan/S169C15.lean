import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S169C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18879)) 356384813 356417581 = 92 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 356384813 356417581).card = 92 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18879 356384813 356417581
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18879)) 356417581 356450349 = 122 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 356417581 356450349).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18879 356417581 356450349
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18880)) 356450349 356483117 = 105 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 356450349 356483117).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18880 356450349 356483117
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18881)) 356483117 356515885 = 102 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 356483117 356515885).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18881 356483117 356515885
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 356384813 356450349).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 356384813 ≤ 356417581)
    (by decide : 356417581 ≤ 356450349) block0 block1

theorem join_0_1 : (twinPrimeSegment 356450349 356515885).card = 207 := by
  simpa using combineTwinPrimeSegments (by decide : 356450349 ≤ 356483117)
    (by decide : 356483117 ≤ 356515885) block2 block3

theorem join_1_0 : (twinPrimeSegment 356384813 356515885).card = 421 := by
  simpa using combineTwinPrimeSegments (by decide : 356384813 ≤ 356450349)
    (by decide : 356450349 ≤ 356515885) join_0_0 join_0_1

theorem total : (twinPrimeSegment 356384813 356515885).card = 421 := join_1_0

end S169C15
end Sude.GeneratedTwinScan
