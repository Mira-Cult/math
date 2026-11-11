import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S139C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17082)) 291766317 291799085 = 131 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 291766317 291799085).card = 131 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17082 291766317 291799085
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17083)) 291799085 291831853 = 123 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 291799085 291831853).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17083 291799085 291831853
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17084)) 291831853 291864621 = 118 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 291831853 291864621).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17084 291831853 291864621
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17085)) 291864621 291897389 = 110 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 291864621 291897389).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17085 291864621 291897389
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 291766317 291831853).card = 254 := by
  simpa using combineTwinPrimeSegments (by decide : 291766317 ≤ 291799085)
    (by decide : 291799085 ≤ 291831853) block0 block1

theorem join_0_1 : (twinPrimeSegment 291831853 291897389).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 291831853 ≤ 291864621)
    (by decide : 291864621 ≤ 291897389) block2 block3

theorem join_1_0 : (twinPrimeSegment 291766317 291897389).card = 482 := by
  simpa using combineTwinPrimeSegments (by decide : 291766317 ≤ 291831853)
    (by decide : 291831853 ≤ 291897389) join_0_0 join_0_1

theorem total : (twinPrimeSegment 291766317 291897389).card = 482 := join_1_0

end S139C02
end Sude.GeneratedTwinScan
