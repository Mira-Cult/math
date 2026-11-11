import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S220C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21492)) 461897773 461930541 = 109 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 461897773 461930541).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21492 461897773 461930541
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21493)) 461930541 461963309 = 95 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 461930541 461963309).card = 95 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21493 461930541 461963309
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21494)) 461963309 461996077 = 101 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 461963309 461996077).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21494 461963309 461996077
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21494)) 461996077 462028845 = 111 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 461996077 462028845).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21494 461996077 462028845
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 461897773 461963309).card = 204 := by
  simpa using combineTwinPrimeSegments (by decide : 461897773 ≤ 461930541)
    (by decide : 461930541 ≤ 461963309) block0 block1

theorem join_0_1 : (twinPrimeSegment 461963309 462028845).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 461963309 ≤ 461996077)
    (by decide : 461996077 ≤ 462028845) block2 block3

theorem join_1_0 : (twinPrimeSegment 461897773 462028845).card = 416 := by
  simpa using combineTwinPrimeSegments (by decide : 461897773 ≤ 461963309)
    (by decide : 461963309 ≤ 462028845) join_0_0 join_0_1

theorem total : (twinPrimeSegment 461897773 462028845).card = 416 := join_1_0

end S220C04
end Sude.GeneratedTwinScan
