import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S182C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19544)) 381943853 381976621 = 118 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 381943853 381976621).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19544 381943853 381976621
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19545)) 381976621 382009389 = 102 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 381976621 382009389).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19545 381976621 382009389
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19545)) 382009389 382042157 = 98 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 382009389 382042157).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19545 382009389 382042157
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19546)) 382042157 382074925 = 111 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 382042157 382074925).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19546 382042157 382074925
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 381943853 382009389).card = 220 := by
  simpa using combineTwinPrimeSegments (by decide : 381943853 ≤ 381976621)
    (by decide : 381976621 ≤ 382009389) block0 block1

theorem join_0_1 : (twinPrimeSegment 382009389 382074925).card = 209 := by
  simpa using combineTwinPrimeSegments (by decide : 382009389 ≤ 382042157)
    (by decide : 382042157 ≤ 382074925) block2 block3

theorem join_1_0 : (twinPrimeSegment 381943853 382074925).card = 429 := by
  simpa using combineTwinPrimeSegments (by decide : 381943853 ≤ 382009389)
    (by decide : 382009389 ≤ 382074925) join_0_0 join_0_1

theorem total : (twinPrimeSegment 381943853 382074925).card = 429 := join_1_0

end S182C02
end Sude.GeneratedTwinScan
