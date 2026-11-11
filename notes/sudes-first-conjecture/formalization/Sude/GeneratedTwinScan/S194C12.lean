import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S194C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20210)) 408420397 408453165 = 102 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 408420397 408453165).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20210 408420397 408453165
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20211)) 408453165 408485933 = 102 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 408453165 408485933).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20211 408453165 408485933
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20211)) 408485933 408518701 = 119 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 408485933 408518701).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20211 408485933 408518701
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20212)) 408518701 408551469 = 86 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 408518701 408551469).card = 86 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20212 408518701 408551469
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 408420397 408485933).card = 204 := by
  simpa using combineTwinPrimeSegments (by decide : 408420397 ≤ 408453165)
    (by decide : 408453165 ≤ 408485933) block0 block1

theorem join_0_1 : (twinPrimeSegment 408485933 408551469).card = 205 := by
  simpa using combineTwinPrimeSegments (by decide : 408485933 ≤ 408518701)
    (by decide : 408518701 ≤ 408551469) block2 block3

theorem join_1_0 : (twinPrimeSegment 408420397 408551469).card = 409 := by
  simpa using combineTwinPrimeSegments (by decide : 408420397 ≤ 408485933)
    (by decide : 408485933 ≤ 408551469) join_0_0 join_0_1

theorem total : (twinPrimeSegment 408420397 408551469).card = 409 := join_1_0

end S194C12
end Sude.GeneratedTwinScan
