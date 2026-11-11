import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S229C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21948)) 481689645 481722413 = 123 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 481689645 481722413).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21948 481689645 481722413
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21948)) 481722413 481755181 = 120 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 481722413 481755181).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21948 481722413 481755181
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21949)) 481755181 481787949 = 94 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 481755181 481787949).card = 94 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21949 481755181 481787949
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21950)) 481787949 481820717 = 106 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 481787949 481820717).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21950 481787949 481820717
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 481689645 481755181).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 481689645 ≤ 481722413)
    (by decide : 481722413 ≤ 481755181) block0 block1

theorem join_0_1 : (twinPrimeSegment 481755181 481820717).card = 200 := by
  simpa using combineTwinPrimeSegments (by decide : 481755181 ≤ 481787949)
    (by decide : 481787949 ≤ 481820717) block2 block3

theorem join_1_0 : (twinPrimeSegment 481689645 481820717).card = 443 := by
  simpa using combineTwinPrimeSegments (by decide : 481689645 ≤ 481755181)
    (by decide : 481755181 ≤ 481820717) join_0_0 join_0_1

theorem total : (twinPrimeSegment 481689645 481820717).card = 443 := join_1_0

end S229C11
end Sude.GeneratedTwinScan
