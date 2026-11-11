import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S116C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15619)) 243925037 243957805 = 139 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 243925037 243957805).card = 139 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15619 243925037 243957805
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15620)) 243957805 243990573 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 243957805 243990573).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15620 243957805 243990573
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15621)) 243990573 244023341 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 243990573 244023341).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15621 243990573 244023341
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15622)) 244023341 244056109 = 121 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 244023341 244056109).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15622 244023341 244056109
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 243925037 243990573).card = 247 := by
  simpa using combineTwinPrimeSegments (by decide : 243925037 ≤ 243957805)
    (by decide : 243957805 ≤ 243990573) block0 block1

theorem join_0_1 : (twinPrimeSegment 243990573 244056109).card = 236 := by
  simpa using combineTwinPrimeSegments (by decide : 243990573 ≤ 244023341)
    (by decide : 244023341 ≤ 244056109) block2 block3

theorem join_1_0 : (twinPrimeSegment 243925037 244056109).card = 483 := by
  simpa using combineTwinPrimeSegments (by decide : 243925037 ≤ 243990573)
    (by decide : 243990573 ≤ 244056109) join_0_0 join_0_1

theorem total : (twinPrimeSegment 243925037 244056109).card = 483 := join_1_0

end S116C05
end Sude.GeneratedTwinScan
