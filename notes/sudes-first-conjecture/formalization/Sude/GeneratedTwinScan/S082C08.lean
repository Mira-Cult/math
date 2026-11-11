import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S082C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13154)) 173015085 173047853 = 118 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 173015085 173047853).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13154 173015085 173047853
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13156)) 173047853 173080621 = 133 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 173047853 173080621).card = 133 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13156 173047853 173080621
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13157)) 173080621 173113389 = 124 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 173080621 173113389).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13157 173080621 173113389
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13158)) 173113389 173146157 = 137 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 173113389 173146157).card = 137 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13158 173113389 173146157
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 173015085 173080621).card = 251 := by
  simpa using combineTwinPrimeSegments (by decide : 173015085 ≤ 173047853)
    (by decide : 173047853 ≤ 173080621) block0 block1

theorem join_0_1 : (twinPrimeSegment 173080621 173146157).card = 261 := by
  simpa using combineTwinPrimeSegments (by decide : 173080621 ≤ 173113389)
    (by decide : 173113389 ≤ 173146157) block2 block3

theorem join_1_0 : (twinPrimeSegment 173015085 173146157).card = 512 := by
  simpa using combineTwinPrimeSegments (by decide : 173015085 ≤ 173080621)
    (by decide : 173080621 ≤ 173146157) join_0_0 join_0_1

theorem total : (twinPrimeSegment 173015085 173146157).card = 512 := join_1_0

end S082C08
end Sude.GeneratedTwinScan
