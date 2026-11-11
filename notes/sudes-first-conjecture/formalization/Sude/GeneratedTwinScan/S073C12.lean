import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S073C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12437)) 154665005 154697773 = 127 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 154665005 154697773).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12437 154665005 154697773
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12439)) 154697773 154730541 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 154697773 154730541).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12439 154697773 154730541
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12440)) 154730541 154763309 = 127 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 154730541 154763309).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12440 154730541 154763309
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 12441)) 154763309 154796077 = 129 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 154763309 154796077).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 12441 154763309 154796077
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 154665005 154730541).card = 241 := by
  simpa using combineTwinPrimeSegments (by decide : 154665005 ≤ 154697773)
    (by decide : 154697773 ≤ 154730541) block0 block1

theorem join_0_1 : (twinPrimeSegment 154730541 154796077).card = 256 := by
  simpa using combineTwinPrimeSegments (by decide : 154730541 ≤ 154763309)
    (by decide : 154763309 ≤ 154796077) block2 block3

theorem join_1_0 : (twinPrimeSegment 154665005 154796077).card = 497 := by
  simpa using combineTwinPrimeSegments (by decide : 154665005 ≤ 154730541)
    (by decide : 154730541 ≤ 154796077) join_0_0 join_0_1

theorem total : (twinPrimeSegment 154665005 154796077).card = 497 := join_1_0

end S073C12
end Sude.GeneratedTwinScan
