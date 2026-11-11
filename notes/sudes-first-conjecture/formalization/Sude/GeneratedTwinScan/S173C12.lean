import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S173C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19089)) 364380205 364412973 = 104 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 364380205 364412973).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19089 364380205 364412973
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19090)) 364412973 364445741 = 109 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 364412973 364445741).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19090 364412973 364445741
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19091)) 364445741 364478509 = 101 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 364445741 364478509).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19091 364445741 364478509
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19092)) 364478509 364511277 = 99 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 364478509 364511277).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19092 364478509 364511277
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 364380205 364445741).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 364380205 ≤ 364412973)
    (by decide : 364412973 ≤ 364445741) block0 block1

theorem join_0_1 : (twinPrimeSegment 364445741 364511277).card = 200 := by
  simpa using combineTwinPrimeSegments (by decide : 364445741 ≤ 364478509)
    (by decide : 364478509 ≤ 364511277) block2 block3

theorem join_1_0 : (twinPrimeSegment 364380205 364511277).card = 413 := by
  simpa using combineTwinPrimeSegments (by decide : 364380205 ≤ 364445741)
    (by decide : 364445741 ≤ 364511277) join_0_0 join_0_1

theorem total : (twinPrimeSegment 364380205 364511277).card = 413 := join_1_0

end S173C12
end Sude.GeneratedTwinScan
