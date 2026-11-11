import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S230C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22007)) 484311085 484343853 = 117 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 484311085 484343853).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22007 484311085 484343853
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22008)) 484343853 484376621 = 96 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 484343853 484376621).card = 96 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22008 484343853 484376621
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22009)) 484376621 484409389 = 107 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 484376621 484409389).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22009 484376621 484409389
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22010)) 484409389 484442157 = 103 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 484409389 484442157).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22010 484409389 484442157
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 484311085 484376621).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 484311085 ≤ 484343853)
    (by decide : 484343853 ≤ 484376621) block0 block1

theorem join_0_1 : (twinPrimeSegment 484376621 484442157).card = 210 := by
  simpa using combineTwinPrimeSegments (by decide : 484376621 ≤ 484409389)
    (by decide : 484409389 ≤ 484442157) block2 block3

theorem join_1_0 : (twinPrimeSegment 484311085 484442157).card = 423 := by
  simpa using combineTwinPrimeSegments (by decide : 484311085 ≤ 484376621)
    (by decide : 484376621 ≤ 484442157) join_0_0 join_0_1

theorem total : (twinPrimeSegment 484311085 484442157).card = 423 := join_1_0

end S230C15
end Sude.GeneratedTwinScan
