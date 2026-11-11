import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S216C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21330)) 454950957 454983725 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 454950957 454983725).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21330 454950957 454983725
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21331)) 454983725 455016493 = 84 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 454983725 455016493).card = 84 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21331 454983725 455016493
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21331)) 455016493 455049261 = 97 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 455016493 455049261).card = 97 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21331 455016493 455049261
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21332)) 455049261 455082029 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 455049261 455082029).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21332 455049261 455082029
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 454950957 455016493).card = 199 := by
  simpa using combineTwinPrimeSegments (by decide : 454950957 ≤ 454983725)
    (by decide : 454983725 ≤ 455016493) block0 block1

theorem join_0_1 : (twinPrimeSegment 455016493 455082029).card = 212 := by
  simpa using combineTwinPrimeSegments (by decide : 455016493 ≤ 455049261)
    (by decide : 455049261 ≤ 455082029) block2 block3

theorem join_1_0 : (twinPrimeSegment 454950957 455082029).card = 411 := by
  simpa using combineTwinPrimeSegments (by decide : 454950957 ≤ 455016493)
    (by decide : 455016493 ≤ 455082029) join_0_0 join_0_1

theorem total : (twinPrimeSegment 454950957 455082029).card = 411 := join_1_0

end S216C15
end Sude.GeneratedTwinScan
