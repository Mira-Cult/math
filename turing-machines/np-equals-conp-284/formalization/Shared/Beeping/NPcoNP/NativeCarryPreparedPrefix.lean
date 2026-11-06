import Shared.Beeping.NPcoNP.NativeCarryAnchor
import Shared.Beeping.NPcoNP.NativeCarryBankFrame
import Shared.Beeping.NPcoNP.NativeSelectorPrefixReturn

/-! A known zero bounds the carry marker; the literal carry preserves the
bank and the prefix left of that marker. -/
namespace Shared.Beeping.NPcoNP.NativeCarryPreparedPrefix
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeIncSelected
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState28Exact
open Shared.Beeping.NPcoNP.NativeHalfMarkerExact
open Shared.Beeping.NPcoNP.NativeCarryAnchor
open Shared.Beeping.NPcoNP.NativeSelectorPrefixReturn
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- A known zero bounds the produced marker, while a later blank separator
protects every bank cell throughout the carry. -/
theorem carry_to83_with_anchor (h p anchor separator : Int) (t : Int → Bool)
    (hanchor : anchor≤h) (anchorZero : t anchor=false) (hp : h<p) (hone : t p=true)
    (hsep : p+1≤separator) (blank : t separator=false) :
    ∃ (steps : Nat) (out : Int → Bool) (mark : Int), 0<steps ∧
      anchor≤mark ∧ mark≤h ∧ out mark=true ∧ (∀ q, q<mark → out q=t q) ∧
      (∀ q, separator≤q → out q=t q) ∧
      silentSegment machine (cfg 1 h t) (cfg 83 (mark-1) out) steps := by
  obtain ⟨j,l,hmarklo,hmarkle,hheadle,hmark,hcorr,hframe,hleft,hcarry⟩ := carry_to28_anchor h p anchor t hanchor anchorZero hp hone
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
  refine ⟨(j+1)+(l+1)+n,out,mark,by omega,?_,?_,houtmark,houtleft,houtright,?_⟩
  · simpa only [mark] using hmarklo
  · simpa only [mark] using hmarkle
  · exact segAdd machine _ _ _ _ _ (by simpa only [u,head28,scanHead,mark] using hcarry) hreturn


/-- A carry whose control prefix begins with a known zero-bounded prepared
header returns to the same parser origin. The prefix before the new marker
and the entire bank are preserved; the suffix/graph successor is separate. -/
theorem carry_returns_to_origin (h p origin separator : Int) (t : Int → Bool)
    (xs : List Bool) (hpos : h=origin+((xs.length : Nat) : Int)-1)
    (hanchor : origin+2≤h) (anchorZero : t (origin+2)=false)
    (count : xs.count false≤11) (word : Holds t origin xs)
    (first : t origin=true) (left : ∀ q, q<origin → t q=false)
    (hp : h<p) (hone : t p=true) (hsep : p+1≤separator) (blank : t separator=false) :
    ∃ (steps : Nat) (out : Int → Bool) (mark : Int), 0<steps ∧
      origin+2≤mark ∧ mark≤h ∧ out mark=true ∧
      (∀ q, q<mark → out q=t q) ∧ (∀ q, separator≤q → out q=t q) ∧
      silentSegment machine (cfg 1 h t) (cfg 93 (origin+1) out) steps := by
  obtain ⟨a,out,mark,ha,hlo,hhi,hmark,hframe,hbank,hcarry⟩ :=
    carry_to83_with_anchor h p (origin+2) separator t hanchor anchorZero hp hone hsep blank
  let j := (mark-origin).toNat
  let pref := xs.take j
  have hj : (j : Int)=mark-origin := Int.toNat_of_nonneg (by omega)
  have hjle : j≤xs.length := by omega
  have hlen : pref.length=j := by simp [pref,List.length_take_of_le hjle]
  have hcount : pref.count false≤11 := by
    have hc := congrArg (List.count false) (List.take_append_drop j xs)
    simp only [List.count_append] at hc
    dsimp [pref]
    omega
  have hpref : Holds t origin pref := by
    apply holds_prefix t origin (xs.take j) (xs.drop j)
    simpa only [List.take_append_drop] using word
  have hout : Holds out origin pref := by
    apply holds_transport t out origin pref hpref
    intro q hq hq'
    exact (hframe q (by rw [hlen] at hq'; omega)).symm
  have houtleft : ∀ q, q<origin → out q=false := by
    intro q hq
    rw [hframe q (by omega)]
    exact left q hq
  have houtfirst : out origin=true := (hframe origin (by omega)).trans first
  obtain ⟨b,hb,hselector⟩ := selector_returns_to_origin out origin pref hcount hout houtleft houtfirst
  have hstart : origin+((pref.length : Nat) : Int)-1=mark-1 := by rw [hlen]; omega
  rw [hstart] at hselector
  exact ⟨a+b,out,mark,by omega,hlo,hhi,hmark,hframe,hbank,
    segAdd machine _ _ _ a b hcarry hselector⟩

#print axioms carry_to83_with_anchor
#print axioms carry_returns_to_origin
end Shared.Beeping.NPcoNP.NativeCarryPreparedPrefix
