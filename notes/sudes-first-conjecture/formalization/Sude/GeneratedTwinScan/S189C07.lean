import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S189C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19932)) 397279277 397312045 = 108 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 397279277 397312045).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19932 397279277 397312045
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19933)) 397312045 397344813 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 397312045 397344813).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19933 397312045 397344813
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19934)) 397344813 397377581 = 107 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 397344813 397377581).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19934 397344813 397377581
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19935)) 397377581 397410349 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 397377581 397410349).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19935 397377581 397410349
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 397279277 397344813).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 397279277 ≤ 397312045)
    (by decide : 397312045 ≤ 397344813) block0 block1

theorem join_0_1 : (twinPrimeSegment 397344813 397410349).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 397344813 ≤ 397377581)
    (by decide : 397377581 ≤ 397410349) block2 block3

theorem join_1_0 : (twinPrimeSegment 397279277 397410349).card = 447 := by
  simpa using combineTwinPrimeSegments (by decide : 397279277 ≤ 397344813)
    (by decide : 397344813 ≤ 397410349) join_0_0 join_0_1

theorem total : (twinPrimeSegment 397279277 397410349).card = 447 := join_1_0

end S189C07
end Sude.GeneratedTwinScan
