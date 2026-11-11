import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S227C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21837)) 476839981 476872749 = 105 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 476839981 476872749).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21837 476839981 476872749
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21838)) 476872749 476905517 = 125 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 476872749 476905517).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21838 476872749 476905517
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21838)) 476905517 476938285 = 93 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 476905517 476938285).card = 93 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21838 476905517 476938285
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21839)) 476938285 476971053 = 109 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 476938285 476971053).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21839 476938285 476971053
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 476839981 476905517).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 476839981 ≤ 476872749)
    (by decide : 476872749 ≤ 476905517) block0 block1

theorem join_0_1 : (twinPrimeSegment 476905517 476971053).card = 202 := by
  simpa using combineTwinPrimeSegments (by decide : 476905517 ≤ 476938285)
    (by decide : 476938285 ≤ 476971053) block2 block3

theorem join_1_0 : (twinPrimeSegment 476839981 476971053).card = 432 := by
  simpa using combineTwinPrimeSegments (by decide : 476839981 ≤ 476905517)
    (by decide : 476905517 ≤ 476971053) join_0_0 join_0_1

theorem total : (twinPrimeSegment 476839981 476971053).card = 432 := join_1_0

end S227C06
end Sude.GeneratedTwinScan
