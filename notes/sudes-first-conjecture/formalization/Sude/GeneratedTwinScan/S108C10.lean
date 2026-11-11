import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S108C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15094)) 227803181 227835949 = 114 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 227803181 227835949).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15094 227803181 227835949
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15095)) 227835949 227868717 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 227835949 227868717).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15095 227835949 227868717
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15096)) 227868717 227901485 = 123 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 227868717 227901485).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15096 227868717 227901485
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15097)) 227901485 227934253 = 125 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 227901485 227934253).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15097 227901485 227934253
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 227803181 227868717).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 227803181 ≤ 227835949)
    (by decide : 227835949 ≤ 227868717) block0 block1

theorem join_0_1 : (twinPrimeSegment 227868717 227934253).card = 248 := by
  simpa using combineTwinPrimeSegments (by decide : 227868717 ≤ 227901485)
    (by decide : 227901485 ≤ 227934253) block2 block3

theorem join_1_0 : (twinPrimeSegment 227803181 227934253).card = 473 := by
  simpa using combineTwinPrimeSegments (by decide : 227803181 ≤ 227868717)
    (by decide : 227868717 ≤ 227934253) join_0_0 join_0_1

theorem total : (twinPrimeSegment 227803181 227934253).card = 473 := join_1_0

end S108C10
end Sude.GeneratedTwinScan
