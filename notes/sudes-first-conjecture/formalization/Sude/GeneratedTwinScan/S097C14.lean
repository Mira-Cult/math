import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S097C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14327)) 205258797 205291565 = 125 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 205258797 205291565).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14327 205258797 205291565
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14329)) 205291565 205324333 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 205291565 205324333).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14329 205291565 205324333
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14330)) 205324333 205357101 = 95 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 205324333 205357101).card = 95 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14330 205324333 205357101
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14331)) 205357101 205389869 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 205357101 205389869).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14331 205357101 205389869
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 205258797 205324333).card = 237 := by
  simpa using combineTwinPrimeSegments (by decide : 205258797 ≤ 205291565)
    (by decide : 205291565 ≤ 205324333) block0 block1

theorem join_0_1 : (twinPrimeSegment 205324333 205389869).card = 207 := by
  simpa using combineTwinPrimeSegments (by decide : 205324333 ≤ 205357101)
    (by decide : 205357101 ≤ 205389869) block2 block3

theorem join_1_0 : (twinPrimeSegment 205258797 205389869).card = 444 := by
  simpa using combineTwinPrimeSegments (by decide : 205258797 ≤ 205324333)
    (by decide : 205324333 ≤ 205389869) join_0_0 join_0_1

theorem total : (twinPrimeSegment 205258797 205389869).card = 444 := join_1_0

end S097C14
end Sude.GeneratedTwinScan
