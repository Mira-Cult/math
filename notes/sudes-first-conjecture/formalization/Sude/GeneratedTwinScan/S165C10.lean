import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S165C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18637)) 347340845 347373613 = 101 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 347340845 347373613).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18637 347340845 347373613
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18638)) 347373613 347406381 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 347373613 347406381).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18638 347373613 347406381
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18639)) 347406381 347439149 = 104 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 347406381 347439149).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18639 347406381 347439149
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18640)) 347439149 347471917 = 124 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 347439149 347471917).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18640 347439149 347471917
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 347340845 347406381).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 347340845 ≤ 347373613)
    (by decide : 347373613 ≤ 347406381) block0 block1

theorem join_0_1 : (twinPrimeSegment 347406381 347471917).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 347406381 ≤ 347439149)
    (by decide : 347439149 ≤ 347471917) block2 block3

theorem join_1_0 : (twinPrimeSegment 347340845 347471917).card = 445 := by
  simpa using combineTwinPrimeSegments (by decide : 347340845 ≤ 347406381)
    (by decide : 347406381 ≤ 347471917) join_0_0 join_0_1

theorem total : (twinPrimeSegment 347340845 347471917).card = 445 := join_1_0

end S165C10
end Sude.GeneratedTwinScan
