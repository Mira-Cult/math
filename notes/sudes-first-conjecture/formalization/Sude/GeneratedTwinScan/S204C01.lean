import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S204C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20687)) 427950125 427982893 = 103 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 427950125 427982893).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20687 427950125 427982893
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20688)) 427982893 428015661 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 427982893 428015661).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20688 427982893 428015661
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20689)) 428015661 428048429 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 428015661 428048429).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20689 428015661 428048429
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20690)) 428048429 428081197 = 113 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 428048429 428081197).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20690 428048429 428081197
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 427950125 428015661).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 427950125 ≤ 427982893)
    (by decide : 427982893 ≤ 428015661) block0 block1

theorem join_0_1 : (twinPrimeSegment 428015661 428081197).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 428015661 ≤ 428048429)
    (by decide : 428048429 ≤ 428081197) block2 block3

theorem join_1_0 : (twinPrimeSegment 427950125 428081197).card = 443 := by
  simpa using combineTwinPrimeSegments (by decide : 427950125 ≤ 428015661)
    (by decide : 428015661 ≤ 428081197) join_0_0 join_0_1

theorem total : (twinPrimeSegment 427950125 428081197).card = 443 := join_1_0

end S204C01
end Sude.GeneratedTwinScan
