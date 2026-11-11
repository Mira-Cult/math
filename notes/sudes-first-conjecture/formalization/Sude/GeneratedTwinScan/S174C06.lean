import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S174C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19123)) 365690925 365723693 = 118 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 365690925 365723693).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19123 365690925 365723693
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19124)) 365723693 365756461 = 102 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 365723693 365756461).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19124 365723693 365756461
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19125)) 365756461 365789229 = 104 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 365756461 365789229).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19125 365756461 365789229
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19126)) 365789229 365821997 = 105 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 365789229 365821997).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19126 365789229 365821997
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 365690925 365756461).card = 220 := by
  simpa using combineTwinPrimeSegments (by decide : 365690925 ≤ 365723693)
    (by decide : 365723693 ≤ 365756461) block0 block1

theorem join_0_1 : (twinPrimeSegment 365756461 365821997).card = 209 := by
  simpa using combineTwinPrimeSegments (by decide : 365756461 ≤ 365789229)
    (by decide : 365789229 ≤ 365821997) block2 block3

theorem join_1_0 : (twinPrimeSegment 365690925 365821997).card = 429 := by
  simpa using combineTwinPrimeSegments (by decide : 365690925 ≤ 365756461)
    (by decide : 365756461 ≤ 365821997) join_0_0 join_0_1

theorem total : (twinPrimeSegment 365690925 365821997).card = 429 := join_1_0

end S174C06
end Sude.GeneratedTwinScan
