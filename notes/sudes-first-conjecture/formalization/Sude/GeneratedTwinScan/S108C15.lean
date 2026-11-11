import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S108C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15115)) 228458541 228491309 = 132 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 228458541 228491309).card = 132 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15115 228458541 228491309
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15117)) 228491309 228524077 = 107 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 228491309 228524077).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15117 228491309 228524077
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15118)) 228524077 228556845 = 101 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 228524077 228556845).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15118 228524077 228556845
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 15119)) 228556845 228589613 = 113 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 228556845 228589613).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 15119 228556845 228589613
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 228458541 228524077).card = 239 := by
  simpa using combineTwinPrimeSegments (by decide : 228458541 ≤ 228491309)
    (by decide : 228491309 ≤ 228524077) block0 block1

theorem join_0_1 : (twinPrimeSegment 228524077 228589613).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 228524077 ≤ 228556845)
    (by decide : 228556845 ≤ 228589613) block2 block3

theorem join_1_0 : (twinPrimeSegment 228458541 228589613).card = 453 := by
  simpa using combineTwinPrimeSegments (by decide : 228458541 ≤ 228524077)
    (by decide : 228524077 ≤ 228589613) join_0_0 join_0_1

theorem total : (twinPrimeSegment 228458541 228589613).card = 453 := join_1_0

end S108C15
end Sude.GeneratedTwinScan
