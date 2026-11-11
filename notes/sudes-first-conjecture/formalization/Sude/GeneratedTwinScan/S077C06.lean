import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S077C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12739)) 162267181 162299949 = 112 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 162267181 162299949).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12739 162267181 162299949
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12740)) 162299949 162332717 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 162299949 162332717).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12740 162299949 162332717
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12742)) 162332717 162365485 = 119 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 162332717 162365485).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12742 162332717 162365485
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12743)) 162365485 162398253 = 140 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 162365485 162398253).card = 140 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12743 162365485 162398253
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 162267181 162332717).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 162267181 ≤ 162299949)
    (by decide : 162299949 ≤ 162332717) block0 block1

theorem join_0_1 : (twinPrimeSegment 162332717 162398253).card = 259 := by
  simpa using combineTwinPrimeSegments (by decide : 162332717 ≤ 162365485)
    (by decide : 162365485 ≤ 162398253) block2 block3

theorem join_1_0 : (twinPrimeSegment 162267181 162398253).card = 489 := by
  simpa using combineTwinPrimeSegments (by decide : 162267181 ≤ 162332717)
    (by decide : 162332717 ≤ 162398253) join_0_0 join_0_1

theorem total : (twinPrimeSegment 162267181 162398253).card = 489 := join_1_0

end S077C06
end Sude.GeneratedTwinScan
