import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S160C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18329)) 335937581 335970349 = 122 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 335937581 335970349).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18329 335937581 335970349
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18330)) 335970349 336003117 = 123 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 335970349 336003117).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18330 335970349 336003117
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18331)) 336003117 336035885 = 107 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 336003117 336035885).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18331 336003117 336035885
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18332)) 336035885 336068653 = 118 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 336035885 336068653).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18332 336035885 336068653
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 335937581 336003117).card = 245 := by
  simpa using combineTwinPrimeSegments (by decide : 335937581 ≤ 335970349)
    (by decide : 335970349 ≤ 336003117) block0 block1

theorem join_0_1 : (twinPrimeSegment 336003117 336068653).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 336003117 ≤ 336035885)
    (by decide : 336035885 ≤ 336068653) block2 block3

theorem join_1_0 : (twinPrimeSegment 335937581 336068653).card = 470 := by
  simpa using combineTwinPrimeSegments (by decide : 335937581 ≤ 336003117)
    (by decide : 336003117 ≤ 336068653) join_0_0 join_0_1

theorem total : (twinPrimeSegment 335937581 336068653).card = 470 := join_1_0

end S160C03
end Sude.GeneratedTwinScan
