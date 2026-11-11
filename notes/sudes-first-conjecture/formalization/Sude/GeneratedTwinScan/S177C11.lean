import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S177C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19304)) 372637741 372670509 = 121 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 372637741 372670509).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19304 372637741 372670509
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19305)) 372670509 372703277 = 101 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 372670509 372703277).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19305 372670509 372703277
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19306)) 372703277 372736045 = 107 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 372703277 372736045).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19306 372703277 372736045
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19307)) 372736045 372768813 = 123 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 372736045 372768813).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19307 372736045 372768813
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 372637741 372703277).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 372637741 ≤ 372670509)
    (by decide : 372670509 ≤ 372703277) block0 block1

theorem join_0_1 : (twinPrimeSegment 372703277 372768813).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 372703277 ≤ 372736045)
    (by decide : 372736045 ≤ 372768813) block2 block3

theorem join_1_0 : (twinPrimeSegment 372637741 372768813).card = 452 := by
  simpa using combineTwinPrimeSegments (by decide : 372637741 ≤ 372703277)
    (by decide : 372703277 ≤ 372768813) join_0_0 join_0_1

theorem total : (twinPrimeSegment 372637741 372768813).card = 452 := join_1_0

end S177C11
end Sude.GeneratedTwinScan
