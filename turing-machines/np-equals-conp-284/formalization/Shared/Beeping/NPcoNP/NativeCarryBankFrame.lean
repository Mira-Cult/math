import Shared.Beeping.NPcoNP.NativeCarrySelectorGeneric

/-! A supplied zero separator bounds the state-1 carry and protects every
cell to its right through the return and selector. No graph successor is
identified by this finite progress theorem. -/
namespace Shared.Beeping.NPcoNP.NativeCarryBankFrame
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState28Exact
open Shared.Beeping.NPcoNP.NativeHalfMarkerExact
open Shared.Beeping.NPcoNP.NativeCarryMarker28
open Shared.Beeping.NPcoNP.NativeCarrySelectorGeneric
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

/-- A protected one and a later zero separator bound the carry's writes
strictly left of the separator and produce the state-83 selector marker. -/
theorem carry_to83_preserving_bank (h p z separator : Int) (t : Int → Bool)
    (left : ∀ q, q≤z → t q=false) (hp : h<p) (hone : t p=true)
    (hsep : p+1≤separator) (blank : t separator=false) :
    ∃ (steps : Nat) (out : Int → Bool) (mark : Int), 0<steps ∧
      mark≤h ∧ out mark=true ∧ (∀ q, q<mark → out q=t q) ∧
      (∀ q, separator≤q → out q=t q) ∧
      silentSegment machine (cfg 1 h t) (cfg 83 (mark-1) out) steps := by
  obtain ⟨j,l,hmarkle,hheadle,hmark,hcorr,hframe,hleft,hcarry⟩ := carry_to28 h p z t left hp hone
  let mark := h-(j : Int)
  let scanHead := mark+1
  let u := put (NativeHalfState1Scan.result t h j) (scanHead+(l : Int)) false
  let head28 := scanHead+(l : Int)+1
  have h28sep : head28≤separator := by dsimp [head28,scanHead,mark] at hheadle ⊢; omega
  have hus : u separator=false := by
    have he : u separator=t separator := hframe separator (by omega) (by simpa only [head28,scanHead,mark] using h28sep)
    exact he.trans blank
  let k := (separator-head28).toNat
  have hk : head28+(k : Int)=separator := by
    have he : (k : Int)=separator-head28 := Int.toNat_of_nonneg (by omega)
    omega
  obtain ⟨n,stop,out,hn,hstop,houtmark,hzero,hones,hexact,hpres,hreturn⟩ :=
    state28_to83_exact head28 mark u (by dsimp [head28,scanHead]; omega)
      (by simpa only [u,head28,scanHead,mark] using hmark)
      (by simpa only [u,head28,scanHead,mark] using hcorr) k (by simpa only [hk] using hus)
  have hstoplt : stop<separator := by
    by_contra hh
    have ho := hones separator h28sep (by omega)
    rw [hus] at ho
    contradiction
  have houtleft : ∀ q, q<mark → out q=t q := by
    intro q hq
    rw [hpres q (by dsimp [head28,scanHead]; omega)]
    exact hleft q (by simpa only [mark] using hq)
  have houtright : ∀ q, separator≤q → out q=t q := by
    intro q hq
    rw [hexact]
    have he : u q=t q := hframe q (by omega) (by simpa only [head28,scanHead,mark] using (show head28≤q by omega))
    rw [put_other _ _ _ _ (by omega)]
    rw [show clearRange u head28 (stop+1) q=u q by
      simp only [clearRange,if_neg (show ¬ (head28≤q ∧ q<stop+1) by omega)]]
    exact he
  refine ⟨(j+1)+(l+1)+n,out,mark,by omega,?_,houtmark,houtleft,houtright,?_⟩
  · simpa only [mark] using hmarkle
  · exact segAdd machine _ _ _ _ _ (by simpa only [u,head28,scanHead,mark] using hcarry) hreturn

/-- The carry and selector terminate silently, preserve the entire bank from
the separator onward, and reach state 93 just after a true control cell. -/
theorem carry_selector_preserving_bank (h p z separator : Int) (t : Int → Bool)
    (left : ∀ q, q≤z → t q=false) (hp : h<p) (hone : t p=true)
    (hsep : p+1≤separator) (blank : t separator=false) :
    ∃ (steps : Nat) (out : Int → Bool) (mark finalHead : Int), 0<steps ∧
      mark≤h ∧ out mark=true ∧ (∀ q, q<mark → out q=t q) ∧
      (∀ q, separator≤q → out q=t q) ∧ out (finalHead-1)=true ∧
      silentSegment machine (cfg 1 h t) (cfg 93 finalHead out) steps := by
  obtain ⟨a,out,mark,ha,hm,hmark,hleft,hbank,hcarry⟩ :=
    carry_to83_preserving_bank h p z separator t left hp hone hsep blank
  let start := mark-1
  let z' := min z (mark-1)
  let k := (start-z').toNat
  have hk : (k : Int)=start-z' := Int.toNat_of_nonneg (by dsimp [start,z']; omega)
  have hblank : ∀ i : Nat, k ≤ i → out (start-(i : Int))=false := by
    intro i hi
    have hq : start-(i : Int)≤z' := by omega
    rw [hleft _ (by dsimp [z'] at hq; omega)]
    apply left
    dsimp [z'] at hq
    omega
  have hmarker : out (start+1)=true := by simpa [start] using hmark
  obtain ⟨d,finalHead,hd,_hbound,hfinal,hselector⟩ :=
    selector_to93_bound out start k hblank hmarker
  exact ⟨a+d,out,mark,finalHead,by omega,hm,hmark,hleft,hbank,hfinal,
    segAdd machine _ _ _ a d (by simpa only [start] using hcarry) hselector⟩

#print axioms carry_to83_preserving_bank
#print axioms carry_selector_preserving_bank
end Shared.Beeping.NPcoNP.NativeCarryBankFrame
