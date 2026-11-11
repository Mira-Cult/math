import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S145C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17465)) 305004589 305037357 = 109 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 305004589 305037357).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17465 305004589 305037357
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17466)) 305037357 305070125 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 305037357 305070125).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17466 305037357 305070125
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17467)) 305070125 305102893 = 132 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 305070125 305102893).card = 132 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17467 305070125 305102893
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17468)) 305102893 305135661 = 96 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 305102893 305135661).card = 96 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17468 305102893 305135661
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 305004589 305070125).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 305004589 ≤ 305037357)
    (by decide : 305037357 ≤ 305070125) block0 block1

theorem join_0_1 : (twinPrimeSegment 305070125 305135661).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 305070125 ≤ 305102893)
    (by decide : 305102893 ≤ 305135661) block2 block3

theorem join_1_0 : (twinPrimeSegment 305004589 305135661).card = 455 := by
  simpa using combineTwinPrimeSegments (by decide : 305004589 ≤ 305070125)
    (by decide : 305070125 ≤ 305135661) join_0_0 join_0_1

theorem total : (twinPrimeSegment 305004589 305135661).card = 455 := join_1_0

end S145C07
end Sude.GeneratedTwinScan
