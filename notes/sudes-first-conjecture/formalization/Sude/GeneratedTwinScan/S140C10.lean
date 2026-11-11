import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S140C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17173)) 294912045 294944813 = 106 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 294912045 294944813).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17173 294912045 294944813
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17174)) 294944813 294977581 = 106 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 294944813 294977581).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17174 294944813 294977581
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17175)) 294977581 295010349 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 294977581 295010349).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17175 294977581 295010349
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17176)) 295010349 295043117 = 122 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 295010349 295043117).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17176 295010349 295043117
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 294912045 294977581).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 294912045 ≤ 294944813)
    (by decide : 294944813 ≤ 294977581) block0 block1

theorem join_0_1 : (twinPrimeSegment 294977581 295043117).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 294977581 ≤ 295010349)
    (by decide : 295010349 ≤ 295043117) block2 block3

theorem join_1_0 : (twinPrimeSegment 294912045 295043117).card = 446 := by
  simpa using combineTwinPrimeSegments (by decide : 294912045 ≤ 294977581)
    (by decide : 294977581 ≤ 295043117) join_0_0 join_0_1

theorem total : (twinPrimeSegment 294912045 295043117).card = 446 := join_1_0

end S140C10
end Sude.GeneratedTwinScan
