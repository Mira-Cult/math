import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S079C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12888)) 166068269 166101037 = 116 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 166068269 166101037).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12888 166068269 166101037
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12889)) 166101037 166133805 = 107 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 166101037 166133805).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12889 166101037 166133805
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12890)) 166133805 166166573 = 101 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 166133805 166166573).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12890 166133805 166166573
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12891)) 166166573 166199341 = 125 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 166166573 166199341).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12891 166166573 166199341
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 166068269 166133805).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 166068269 ≤ 166101037)
    (by decide : 166101037 ≤ 166133805) block0 block1

theorem join_0_1 : (twinPrimeSegment 166133805 166199341).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 166133805 ≤ 166166573)
    (by decide : 166166573 ≤ 166199341) block2 block3

theorem join_1_0 : (twinPrimeSegment 166068269 166199341).card = 449 := by
  simpa using combineTwinPrimeSegments (by decide : 166068269 ≤ 166133805)
    (by decide : 166133805 ≤ 166199341) join_0_0 join_0_1

theorem total : (twinPrimeSegment 166068269 166199341).card = 449 := join_1_0

end S079C03
end Sude.GeneratedTwinScan
