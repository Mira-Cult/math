import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S158C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18218)) 331874349 331907117 = 111 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 331874349 331907117).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18218 331874349 331907117
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18219)) 331907117 331939885 = 115 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 331907117 331939885).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18219 331907117 331939885
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18220)) 331939885 331972653 = 110 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 331939885 331972653).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18220 331939885 331972653
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18221)) 331972653 332005421 = 111 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 331972653 332005421).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18221 331972653 332005421
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 331874349 331939885).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 331874349 ≤ 331907117)
    (by decide : 331907117 ≤ 331939885) block0 block1

theorem join_0_1 : (twinPrimeSegment 331939885 332005421).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 331939885 ≤ 331972653)
    (by decide : 331972653 ≤ 332005421) block2 block3

theorem join_1_0 : (twinPrimeSegment 331874349 332005421).card = 447 := by
  simpa using combineTwinPrimeSegments (by decide : 331874349 ≤ 331939885)
    (by decide : 331939885 ≤ 332005421) join_0_0 join_0_1

theorem total : (twinPrimeSegment 331874349 332005421).card = 447 := join_1_0

end S158C04
end Sude.GeneratedTwinScan
