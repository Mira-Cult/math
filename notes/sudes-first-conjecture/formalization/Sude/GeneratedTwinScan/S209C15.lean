import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S209C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20983)) 440270893 440303661 = 106 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 440270893 440303661).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20983 440270893 440303661
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20984)) 440303661 440336429 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 440303661 440336429).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20984 440303661 440336429
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20984)) 440336429 440369197 = 102 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 440336429 440369197).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20984 440336429 440369197
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20985)) 440369197 440401965 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 440369197 440401965).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20985 440369197 440401965
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 440270893 440336429).card = 224 := by
  simpa using combineTwinPrimeSegments (by decide : 440270893 ≤ 440303661)
    (by decide : 440303661 ≤ 440336429) block0 block1

theorem join_0_1 : (twinPrimeSegment 440336429 440401965).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 440336429 ≤ 440369197)
    (by decide : 440369197 ≤ 440401965) block2 block3

theorem join_1_0 : (twinPrimeSegment 440270893 440401965).card = 438 := by
  simpa using combineTwinPrimeSegments (by decide : 440270893 ≤ 440336429)
    (by decide : 440336429 ≤ 440401965) join_0_0 join_0_1

theorem total : (twinPrimeSegment 440270893 440401965).card = 438 := join_1_0

end S209C15
end Sude.GeneratedTwinScan
