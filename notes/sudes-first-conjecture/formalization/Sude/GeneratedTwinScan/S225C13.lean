import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S225C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21762)) 473563181 473595949 = 110 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 473563181 473595949).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21762 473563181 473595949
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21763)) 473595949 473628717 = 107 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 473595949 473628717).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21763 473595949 473628717
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21763)) 473628717 473661485 = 99 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 473628717 473661485).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21763 473628717 473661485
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21764)) 473661485 473694253 = 98 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 473661485 473694253).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21764 473661485 473694253
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 473563181 473628717).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 473563181 ≤ 473595949)
    (by decide : 473595949 ≤ 473628717) block0 block1

theorem join_0_1 : (twinPrimeSegment 473628717 473694253).card = 197 := by
  simpa using combineTwinPrimeSegments (by decide : 473628717 ≤ 473661485)
    (by decide : 473661485 ≤ 473694253) block2 block3

theorem join_1_0 : (twinPrimeSegment 473563181 473694253).card = 414 := by
  simpa using combineTwinPrimeSegments (by decide : 473563181 ≤ 473628717)
    (by decide : 473628717 ≤ 473694253) join_0_0 join_0_1

theorem total : (twinPrimeSegment 473563181 473694253).card = 414 := join_1_0

end S225C13
end Sude.GeneratedTwinScan
