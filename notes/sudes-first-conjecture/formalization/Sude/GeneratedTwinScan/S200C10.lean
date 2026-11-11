import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S200C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20512)) 420741165 420773933 = 121 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 420741165 420773933).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20512 420741165 420773933
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20513)) 420773933 420806701 = 120 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 420773933 420806701).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20513 420773933 420806701
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20514)) 420806701 420839469 = 122 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 420806701 420839469).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20514 420806701 420839469
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20515)) 420839469 420872237 = 105 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 420839469 420872237).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20515 420839469 420872237
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 420741165 420806701).card = 241 := by
  simpa using combineTwinPrimeSegments (by decide : 420741165 ≤ 420773933)
    (by decide : 420773933 ≤ 420806701) block0 block1

theorem join_0_1 : (twinPrimeSegment 420806701 420872237).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 420806701 ≤ 420839469)
    (by decide : 420839469 ≤ 420872237) block2 block3

theorem join_1_0 : (twinPrimeSegment 420741165 420872237).card = 468 := by
  simpa using combineTwinPrimeSegments (by decide : 420741165 ≤ 420806701)
    (by decide : 420806701 ≤ 420872237) join_0_0 join_0_1

theorem total : (twinPrimeSegment 420741165 420872237).card = 468 := join_1_0

end S200C10
end Sude.GeneratedTwinScan
