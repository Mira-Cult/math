import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S173C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19086)) 364249133 364281901 = 107 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 364249133 364281901).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19086 364249133 364281901
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19087)) 364281901 364314669 = 106 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 364281901 364314669).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19087 364281901 364314669
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19087)) 364314669 364347437 = 119 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 364314669 364347437).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19087 364314669 364347437
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19088)) 364347437 364380205 = 109 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 364347437 364380205).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19088 364347437 364380205
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 364249133 364314669).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 364249133 ≤ 364281901)
    (by decide : 364281901 ≤ 364314669) block0 block1

theorem join_0_1 : (twinPrimeSegment 364314669 364380205).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 364314669 ≤ 364347437)
    (by decide : 364347437 ≤ 364380205) block2 block3

theorem join_1_0 : (twinPrimeSegment 364249133 364380205).card = 441 := by
  simpa using combineTwinPrimeSegments (by decide : 364249133 ≤ 364314669)
    (by decide : 364314669 ≤ 364380205) join_0_0 join_0_1

theorem total : (twinPrimeSegment 364249133 364380205).card = 441 := join_1_0

end S173C11
end Sude.GeneratedTwinScan
