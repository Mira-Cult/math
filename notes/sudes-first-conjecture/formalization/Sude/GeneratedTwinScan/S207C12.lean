import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S207C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20873)) 435683373 435716141 = 112 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 435683373 435716141).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20873 435683373 435716141
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20874)) 435716141 435748909 = 121 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 435716141 435748909).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20874 435716141 435748909
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20875)) 435748909 435781677 = 105 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 435748909 435781677).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20875 435748909 435781677
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20876)) 435781677 435814445 = 95 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 435781677 435814445).card = 95 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20876 435781677 435814445
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 435683373 435748909).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 435683373 ≤ 435716141)
    (by decide : 435716141 ≤ 435748909) block0 block1

theorem join_0_1 : (twinPrimeSegment 435748909 435814445).card = 200 := by
  simpa using combineTwinPrimeSegments (by decide : 435748909 ≤ 435781677)
    (by decide : 435781677 ≤ 435814445) block2 block3

theorem join_1_0 : (twinPrimeSegment 435683373 435814445).card = 433 := by
  simpa using combineTwinPrimeSegments (by decide : 435683373 ≤ 435748909)
    (by decide : 435748909 ≤ 435814445) join_0_0 join_0_1

theorem total : (twinPrimeSegment 435683373 435814445).card = 433 := join_1_0

end S207C12
end Sude.GeneratedTwinScan
