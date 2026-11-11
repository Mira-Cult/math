import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S147C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17573)) 308805677 308838445 = 112 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 308805677 308838445).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17573 308805677 308838445
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17574)) 308838445 308871213 = 122 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 308838445 308871213).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17574 308838445 308871213
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17575)) 308871213 308903981 = 106 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 308871213 308903981).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17575 308871213 308903981
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17576)) 308903981 308936749 = 117 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 308903981 308936749).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17576 308903981 308936749
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 308805677 308871213).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 308805677 ≤ 308838445)
    (by decide : 308838445 ≤ 308871213) block0 block1

theorem join_0_1 : (twinPrimeSegment 308871213 308936749).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 308871213 ≤ 308903981)
    (by decide : 308903981 ≤ 308936749) block2 block3

theorem join_1_0 : (twinPrimeSegment 308805677 308936749).card = 457 := by
  simpa using combineTwinPrimeSegments (by decide : 308805677 ≤ 308871213)
    (by decide : 308871213 ≤ 308936749) join_0_0 join_0_1

theorem total : (twinPrimeSegment 308805677 308936749).card = 457 := join_1_0

end S147C04
end Sude.GeneratedTwinScan
