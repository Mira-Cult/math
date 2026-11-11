import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S183C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19637)) 385613869 385646637 = 101 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 385613869 385646637).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19637 385613869 385646637
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19638)) 385646637 385679405 = 98 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 385646637 385679405).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19638 385646637 385679405
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19639)) 385679405 385712173 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 385679405 385712173).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19639 385679405 385712173
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19640)) 385712173 385744941 = 103 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 385712173 385744941).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19640 385712173 385744941
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 385613869 385679405).card = 199 := by
  simpa using combineTwinPrimeSegments (by decide : 385613869 ≤ 385646637)
    (by decide : 385646637 ≤ 385679405) block0 block1

theorem join_0_1 : (twinPrimeSegment 385679405 385744941).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 385679405 ≤ 385712173)
    (by decide : 385712173 ≤ 385744941) block2 block3

theorem join_1_0 : (twinPrimeSegment 385613869 385744941).card = 415 := by
  simpa using combineTwinPrimeSegments (by decide : 385613869 ≤ 385679405)
    (by decide : 385679405 ≤ 385744941) join_0_0 join_0_1

theorem total : (twinPrimeSegment 385613869 385744941).card = 415 := join_1_0

end S183C14
end Sude.GeneratedTwinScan
