import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S128C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16412)) 269353005 269385773 = 109 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 269353005 269385773).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16412 269353005 269385773
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16413)) 269385773 269418541 = 121 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 269385773 269418541).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16413 269385773 269418541
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16414)) 269418541 269451309 = 107 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 269418541 269451309).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16414 269418541 269451309
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16415)) 269451309 269484077 = 105 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 269451309 269484077).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16415 269451309 269484077
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 269353005 269418541).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 269353005 ≤ 269385773)
    (by decide : 269385773 ≤ 269418541) block0 block1

theorem join_0_1 : (twinPrimeSegment 269418541 269484077).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 269418541 ≤ 269451309)
    (by decide : 269451309 ≤ 269484077) block2 block3

theorem join_1_0 : (twinPrimeSegment 269353005 269484077).card = 442 := by
  simpa using combineTwinPrimeSegments (by decide : 269353005 ≤ 269418541)
    (by decide : 269418541 ≤ 269484077) join_0_0 join_0_1

theorem total : (twinPrimeSegment 269353005 269484077).card = 442 := join_1_0

end S128C07
end Sude.GeneratedTwinScan
