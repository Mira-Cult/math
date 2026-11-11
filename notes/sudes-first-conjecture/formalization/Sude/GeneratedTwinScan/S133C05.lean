import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S133C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16721)) 279576621 279609389 = 122 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 279576621 279609389).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16721 279576621 279609389
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16722)) 279609389 279642157 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 279609389 279642157).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16722 279609389 279642157
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16723)) 279642157 279674925 = 105 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 279642157 279674925).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16723 279642157 279674925
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16724)) 279674925 279707693 = 110 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 279674925 279707693).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16724 279674925 279707693
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 279576621 279642157).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 279576621 ≤ 279609389)
    (by decide : 279609389 ≤ 279642157) block0 block1

theorem join_0_1 : (twinPrimeSegment 279642157 279707693).card = 215 := by
  simpa using combineTwinPrimeSegments (by decide : 279642157 ≤ 279674925)
    (by decide : 279674925 ≤ 279707693) block2 block3

theorem join_1_0 : (twinPrimeSegment 279576621 279707693).card = 449 := by
  simpa using combineTwinPrimeSegments (by decide : 279576621 ≤ 279642157)
    (by decide : 279642157 ≤ 279707693) join_0_0 join_0_1

theorem total : (twinPrimeSegment 279576621 279707693).card = 449 := join_1_0

end S133C05
end Sude.GeneratedTwinScan
