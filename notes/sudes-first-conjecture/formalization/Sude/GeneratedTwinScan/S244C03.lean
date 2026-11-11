import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S244C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22630)) 512098349 512131117 = 127 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 512098349 512131117).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22630 512098349 512131117
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22631)) 512131117 512163885 = 110 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 512131117 512163885).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22631 512131117 512163885
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22631)) 512163885 512196653 = 105 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 512163885 512196653).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22631 512163885 512196653
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22632)) 512196653 512229421 = 106 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 512196653 512229421).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22632 512196653 512229421
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 512098349 512163885).card = 237 := by
  simpa using combineTwinPrimeSegments (by decide : 512098349 ≤ 512131117)
    (by decide : 512131117 ≤ 512163885) block0 block1

theorem join_0_1 : (twinPrimeSegment 512163885 512229421).card = 211 := by
  simpa using combineTwinPrimeSegments (by decide : 512163885 ≤ 512196653)
    (by decide : 512196653 ≤ 512229421) block2 block3

theorem join_1_0 : (twinPrimeSegment 512098349 512229421).card = 448 := by
  simpa using combineTwinPrimeSegments (by decide : 512098349 ≤ 512163885)
    (by decide : 512163885 ≤ 512229421) join_0_0 join_0_1

theorem total : (twinPrimeSegment 512098349 512229421).card = 448 := join_1_0

end S244C03
end Sude.GeneratedTwinScan
