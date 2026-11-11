import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S212C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21101)) 445251629 445284397 = 116 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 445251629 445284397).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21101 445251629 445284397
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21102)) 445284397 445317165 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 445284397 445317165).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21102 445284397 445317165
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21103)) 445317165 445349933 = 125 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 445317165 445349933).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21103 445317165 445349933
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21104)) 445349933 445382701 = 94 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 445349933 445382701).card = 94 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21104 445349933 445382701
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 445251629 445317165).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 445251629 ≤ 445284397)
    (by decide : 445284397 ≤ 445317165) block0 block1

theorem join_0_1 : (twinPrimeSegment 445317165 445382701).card = 219 := by
  simpa using combineTwinPrimeSegments (by decide : 445317165 ≤ 445349933)
    (by decide : 445349933 ≤ 445382701) block2 block3

theorem join_1_0 : (twinPrimeSegment 445251629 445382701).card = 446 := by
  simpa using combineTwinPrimeSegments (by decide : 445251629 ≤ 445317165)
    (by decide : 445317165 ≤ 445382701) join_0_0 join_0_1

theorem total : (twinPrimeSegment 445251629 445382701).card = 446 := join_1_0

end S212C05
end Sude.GeneratedTwinScan
