import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S132C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16642)) 276955181 276987949 = 129 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 276955181 276987949).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16642 276955181 276987949
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16643)) 276987949 277020717 = 104 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 276987949 277020717).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16643 276987949 277020717
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16644)) 277020717 277053485 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 277020717 277053485).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16644 277020717 277053485
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16645)) 277053485 277086253 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 277053485 277086253).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16645 277053485 277086253
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 276955181 277020717).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 276955181 ≤ 276987949)
    (by decide : 276987949 ≤ 277020717) block0 block1

theorem join_0_1 : (twinPrimeSegment 277020717 277086253).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 277020717 ≤ 277053485)
    (by decide : 277053485 ≤ 277086253) block2 block3

theorem join_1_0 : (twinPrimeSegment 276955181 277086253).card = 458 := by
  simpa using combineTwinPrimeSegments (by decide : 276955181 ≤ 277020717)
    (by decide : 277020717 ≤ 277086253) join_0_0 join_0_1

theorem total : (twinPrimeSegment 276955181 277086253).card = 458 := join_1_0

end S132C01
end Sude.GeneratedTwinScan
