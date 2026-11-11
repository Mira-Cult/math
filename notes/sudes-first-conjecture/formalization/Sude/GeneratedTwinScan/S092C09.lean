import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S092C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13933)) 194117677 194150445 = 138 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 194117677 194150445).card = 138 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13933 194117677 194150445
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13934)) 194150445 194183213 = 135 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 194150445 194183213).card = 135 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13934 194150445 194183213
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13936)) 194183213 194215981 = 119 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 194183213 194215981).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13936 194183213 194215981
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13937)) 194215981 194248749 = 111 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 194215981 194248749).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13937 194215981 194248749
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 194117677 194183213).card = 273 := by
  simpa using combineTwinPrimeSegments (by decide : 194117677 ≤ 194150445)
    (by decide : 194150445 ≤ 194183213) block0 block1

theorem join_0_1 : (twinPrimeSegment 194183213 194248749).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 194183213 ≤ 194215981)
    (by decide : 194215981 ≤ 194248749) block2 block3

theorem join_1_0 : (twinPrimeSegment 194117677 194248749).card = 503 := by
  simpa using combineTwinPrimeSegments (by decide : 194117677 ≤ 194183213)
    (by decide : 194183213 ≤ 194248749) join_0_0 join_0_1

theorem total : (twinPrimeSegment 194117677 194248749).card = 503 := join_1_0

end S092C09
end Sude.GeneratedTwinScan
