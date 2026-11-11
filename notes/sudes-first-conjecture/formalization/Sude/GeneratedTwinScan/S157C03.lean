import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S157C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18157)) 329646125 329678893 = 120 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 329646125 329678893).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18157 329646125 329678893
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18157)) 329678893 329711661 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 329678893 329711661).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18157 329678893 329711661
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18158)) 329711661 329744429 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 329711661 329744429).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18158 329711661 329744429
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18159)) 329744429 329777197 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 329744429 329777197).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18159 329744429 329777197
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 329646125 329711661).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 329646125 ≤ 329678893)
    (by decide : 329678893 ≤ 329711661) block0 block1

theorem join_0_1 : (twinPrimeSegment 329711661 329777197).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 329711661 ≤ 329744429)
    (by decide : 329744429 ≤ 329777197) block2 block3

theorem join_1_0 : (twinPrimeSegment 329646125 329777197).card = 464 := by
  simpa using combineTwinPrimeSegments (by decide : 329646125 ≤ 329711661)
    (by decide : 329711661 ≤ 329777197) join_0_0 join_0_1

theorem total : (twinPrimeSegment 329646125 329777197).card = 464 := join_1_0

end S157C03
end Sude.GeneratedTwinScan
