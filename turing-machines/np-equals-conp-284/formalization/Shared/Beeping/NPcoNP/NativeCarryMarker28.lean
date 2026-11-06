import Shared.Beeping.NPcoNP.NativeHalfMarkerRetain

/-! The literal state-1 carry creates a protected left marker. A known one
to the right forces state 27 to reach state 28, leaving a zero corridor. -/
namespace Shared.Beeping.NPcoNP.NativeCarryMarker28
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState1Scan
open Shared.Beeping.NPcoNP.NativeHalfState1FiniteSupport
open Shared.Beeping.NPcoNP.NativeHalfState27Scan
open Shared.Beeping.NPcoNP.NativeHalfMarkerRetain
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

/-- The carry and scan produce a marker, a strictly later state-28 head,
and an entirely zero corridor between them. The entire destination tape
is explicitly determined by the two paid scans. -/
theorem carry_to28 (h p z : Int) (t : Int → Bool)
    (left : ∀ q, q≤z → t q=false) (hp : h<p) (hone : t p=true) :
    ∃ j l : Nat,
      let mark := h-(j : Int)
      let scanHead := mark+1
      let u := put (result t h j) (scanHead+(l : Int)) false
      let head28 := scanHead+(l : Int)+1
      mark≤h ∧ head28≤p+1 ∧ u mark=true ∧
      (∀ q, mark<q → q<head28 → u q=false) ∧
      (∀ q, h<q → head28≤q → u q=t q) ∧
      (∀ q, q<mark → u q=t q) ∧
      silentSegment machine (cfg 1 h t) (cfg 28 head28 u) ((j+1)+(l+1)) := by
  let k := (h-min z h).toNat
  have hk : h-(k : Int)≤z := by
    have hn : 0≤h-min z h := by omega
    have he : (k : Int)=h-min z h := Int.toNat_of_nonneg hn
    omega
  obtain ⟨j,_hj,hword⟩ := first_zero k h t (left _ hk)
  let mark := h-(j : Int)
  let carried := result t h j
  let scanHead := mark+1
  have hmark : carried mark=true := by simp [carried,result,put,mark]
  have hp' : scanHead≤p := by dsimp [scanHead,mark]; omega
  have hright : carried p=true := by
    rw [show carried p=t p from result_preserves_above t h p j hp]
    exact hone
  obtain ⟨l,hzeros,hfirst⟩ := first_one scanHead p carried hp' hright
  let hit := scanHead+(l : Int)
  let u := put carried hit false
  let head28 := hit+1
  have hat : hit≤p := by
    by_contra hn
    have hpos : scanHead≤p := hp'
    let i := (p-scanHead).toNat
    have hi : (i : Int)=p-scanHead := Int.toNat_of_nonneg (by omega)
    have hil : i<l := by dsimp [hit] at hn; omega
    have hz := hzeros i hil
    have he : scanHead+(i : Int)=p := by omega
    rw [he,hright] at hz
    contradiction
  have umark : u mark=true := by
    dsimp [u,hit,scanHead]
    rw [put_other _ _ _ _ (by omega)]
    exact hmark
  have hcorr : ∀ q, mark<q → q<head28 → u q=false := by
    intro q hq hq'
    by_cases he : q=hit
    · subst q; simp [u,put]
    · have hlt : q<hit := by dsimp [head28] at hq'; omega
      have hge : scanHead≤q := by dsimp [scanHead]; omega
      let i := (q-scanHead).toNat
      have hi : (i : Int)=q-scanHead := Int.toNat_of_nonneg (by omega)
      have hil : i<l := by dsimp [hit] at hlt; omega
      have hz := hzeros i hil
      have hpos : scanHead+(i : Int)=q := by omega
      rw [hpos] at hz
      rw [show u q=carried q from put_other _ _ _ _ he]
      exact hz
  have hframe : ∀ q, h<q → head28≤q → u q=t q := by
    intro q hq hq'
    rw [show u q=carried q from put_other _ _ _ _ (by dsimp [head28] at hq'; omega)]
    exact result_preserves_above t h q j hq
  have hleft : ∀ q, q<mark → u q=t q := by
    intro q hq
    rw [show u q=carried q from put_other _ _ _ _ (by dsimp [hit,scanHead]; omega)]
    have hne : q≠h-(j : Int) := by dsimp [mark] at hq; omega
    have hn : ¬ (h-(j : Int)<q ∧ q≤h) := by dsimp [mark] at hq; omega
    simp [carried,result,put,cleared,hne,hn]
  have hs1 := scan t h j hword
  have hs27 := scan_to_one scanHead carried l hzeros hfirst
  have hall := segAdd machine _ _ _ (j+1) (l+1) hs1 hs27
  refine ⟨j,l,by omega,by change head28≤p+1; dsimp [head28]; omega,umark,hcorr,hframe,hleft,?_⟩
  simpa only [mark,scanHead,hit,head28,u,carried] using hall

#print axioms carry_to28
end Shared.Beeping.NPcoNP.NativeCarryMarker28
