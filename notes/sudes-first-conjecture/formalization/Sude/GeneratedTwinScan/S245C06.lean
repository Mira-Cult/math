import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S245C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22685)) 514588717 514621485 = 83 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 514588717 514621485).card = 83 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22685 514588717 514621485
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22685)) 514621485 514654253 = 101 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 514621485 514654253).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22685 514621485 514654253
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22686)) 514654253 514687021 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 514654253 514687021).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22686 514654253 514687021
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22687)) 514687021 514719789 = 110 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 514687021 514719789).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22687 514687021 514719789
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 514588717 514654253).card = 184 := by
  simpa using combineTwinPrimeSegments (by decide : 514588717 ≤ 514621485)
    (by decide : 514621485 ≤ 514654253) block0 block1

theorem join_0_1 : (twinPrimeSegment 514654253 514719789).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 514654253 ≤ 514687021)
    (by decide : 514687021 ≤ 514719789) block2 block3

theorem join_1_0 : (twinPrimeSegment 514588717 514719789).card = 407 := by
  simpa using combineTwinPrimeSegments (by decide : 514588717 ≤ 514654253)
    (by decide : 514654253 ≤ 514719789) join_0_0 join_0_1

theorem total : (twinPrimeSegment 514588717 514719789).card = 407 := join_1_0

end S245C06
end Sude.GeneratedTwinScan
