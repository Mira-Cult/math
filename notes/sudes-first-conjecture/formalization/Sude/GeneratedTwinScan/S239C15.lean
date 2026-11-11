import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S239C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22432)) 503185453 503218221 = 102 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 503185453 503218221).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22432 503185453 503218221
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22433)) 503218221 503250989 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 503218221 503250989).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22433 503218221 503250989
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22433)) 503250989 503283757 = 98 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 503250989 503283757).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22433 503250989 503283757
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22434)) 503283757 503316525 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 503283757 503316525).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22434 503283757 503316525
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 503185453 503250989).card = 210 := by
  simpa using combineTwinPrimeSegments (by decide : 503185453 ≤ 503218221)
    (by decide : 503218221 ≤ 503250989) block0 block1

theorem join_0_1 : (twinPrimeSegment 503250989 503316525).card = 210 := by
  simpa using combineTwinPrimeSegments (by decide : 503250989 ≤ 503283757)
    (by decide : 503283757 ≤ 503316525) block2 block3

theorem join_1_0 : (twinPrimeSegment 503185453 503316525).card = 420 := by
  simpa using combineTwinPrimeSegments (by decide : 503185453 ≤ 503250989)
    (by decide : 503250989 ≤ 503316525) join_0_0 join_0_1

theorem total : (twinPrimeSegment 503185453 503316525).card = 420 := join_1_0

end S239C15
end Sude.GeneratedTwinScan
