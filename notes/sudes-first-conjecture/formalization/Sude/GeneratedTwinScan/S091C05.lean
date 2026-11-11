import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S091C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13839)) 191496237 191529005 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 191496237 191529005).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13839 191496237 191529005
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13840)) 191529005 191561773 = 126 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 191529005 191561773).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13840 191529005 191561773
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13841)) 191561773 191594541 = 118 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 191561773 191594541).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13841 191561773 191594541
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13842)) 191594541 191627309 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 191594541 191627309).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13842 191594541 191627309
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 191496237 191561773).card = 239 := by
  simpa using combineTwinPrimeSegments (by decide : 191496237 ≤ 191529005)
    (by decide : 191529005 ≤ 191561773) block0 block1

theorem join_0_1 : (twinPrimeSegment 191561773 191627309).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 191561773 ≤ 191594541)
    (by decide : 191594541 ≤ 191627309) block2 block3

theorem join_1_0 : (twinPrimeSegment 191496237 191627309).card = 473 := by
  simpa using combineTwinPrimeSegments (by decide : 191496237 ≤ 191561773)
    (by decide : 191561773 ≤ 191627309) join_0_0 join_0_1

theorem total : (twinPrimeSegment 191496237 191627309).card = 473 := join_1_0

end S091C05
end Sude.GeneratedTwinScan
