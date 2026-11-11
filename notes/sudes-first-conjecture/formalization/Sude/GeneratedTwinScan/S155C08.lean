import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S155C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18059)) 326107181 326139949 = 128 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 326107181 326139949).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18059 326107181 326139949
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18060)) 326139949 326172717 = 135 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 326139949 326172717).card = 135 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18060 326139949 326172717
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18061)) 326172717 326205485 = 123 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 326172717 326205485).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18061 326172717 326205485
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18062)) 326205485 326238253 = 101 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 326205485 326238253).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18062 326205485 326238253
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 326107181 326172717).card = 263 := by
  simpa using combineTwinPrimeSegments (by decide : 326107181 ≤ 326139949)
    (by decide : 326139949 ≤ 326172717) block0 block1

theorem join_0_1 : (twinPrimeSegment 326172717 326238253).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 326172717 ≤ 326205485)
    (by decide : 326205485 ≤ 326238253) block2 block3

theorem join_1_0 : (twinPrimeSegment 326107181 326238253).card = 487 := by
  simpa using combineTwinPrimeSegments (by decide : 326107181 ≤ 326172717)
    (by decide : 326172717 ≤ 326238253) join_0_0 join_0_1

theorem total : (twinPrimeSegment 326107181 326238253).card = 487 := join_1_0

end S155C08
end Sude.GeneratedTwinScan
