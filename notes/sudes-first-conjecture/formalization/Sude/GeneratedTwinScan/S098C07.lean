import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S098C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14369)) 206438445 206471213 = 120 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 206438445 206471213).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14369 206438445 206471213
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14370)) 206471213 206503981 = 120 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 206471213 206503981).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14370 206471213 206503981
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14371)) 206503981 206536749 = 111 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 206503981 206536749).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14371 206503981 206536749
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14372)) 206536749 206569517 = 121 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 206536749 206569517).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14372 206536749 206569517
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 206438445 206503981).card = 240 := by
  simpa using combineTwinPrimeSegments (by decide : 206438445 ≤ 206471213)
    (by decide : 206471213 ≤ 206503981) block0 block1

theorem join_0_1 : (twinPrimeSegment 206503981 206569517).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 206503981 ≤ 206536749)
    (by decide : 206536749 ≤ 206569517) block2 block3

theorem join_1_0 : (twinPrimeSegment 206438445 206569517).card = 472 := by
  simpa using combineTwinPrimeSegments (by decide : 206438445 ≤ 206503981)
    (by decide : 206503981 ≤ 206569517) join_0_0 join_0_1

theorem total : (twinPrimeSegment 206438445 206569517).card = 472 := join_1_0

end S098C07
end Sude.GeneratedTwinScan
