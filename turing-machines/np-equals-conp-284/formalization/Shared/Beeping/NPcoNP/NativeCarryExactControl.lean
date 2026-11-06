import Shared.Beeping.NPcoNP.NativeCarryAnchor
import Shared.Beeping.NPcoNP.NativeCarryPreparedPrefix
import Shared.Beeping.NPcoNP.NativeHalfTapeScan
import Shared.Beeping.NPcoNP.NativeIncBank

/-! Exact location of the rightward marker hit after a bounded left carry. -/
namespace Shared.Beeping.NPcoNP.NativeCarryExactControl
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState1Scan
open Shared.Beeping.NPcoNP.NativeHalfState1FiniteSupport
open Shared.Beeping.NPcoNP.NativeHalfState27Scan
open Shared.Beeping.NPcoNP.NativeHalfMarkerRetain
open Shared.Beeping.NPcoNP.NativeHalfState28Exact
open Shared.Beeping.NPcoNP.NativeHalfMarkerExact
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeIncSelected
open Shared.Beeping.NPcoNP.NativeSelectorPrefixReturn
open Shared.Beeping.NPcoNP.NativeIncBank
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

/-- A finite carry word identifies a zero followed by ones up to the head. -/
theorem carry_word_exact (t : Int → Bool) (h : Int) (k : Nat)
    (word : downHolds t h (List.replicate k true ++ [false])) :
    t (h-(k : Int))=false ∧ ∀ q, h-(k : Int)<q → q≤h → t q=true := by
  induction k generalizing h with
  | zero =>
    simp only [List.replicate_zero,List.nil_append,downHolds] at word
    refine ⟨by simpa using word.1,?_⟩
    intro q hq hq'
    omega
  | succ k ih =>
    simp only [List.replicate_succ,List.cons_append,downHolds] at word
    obtain ⟨hz,ho⟩ := ih (h-1) word.2
    have he : h-((k+1 : Nat) : Int)=h-1-(k : Int) := by push_cast; omega
    rw [he]
    refine ⟨hz,?_⟩
    intro q hq hq'
    by_cases hqeq : q=h
    · simpa only [hqeq] using word.1
    · exact ho q hq (by omega)

/-- If the protected one is preceded by zeros to the right of the carry head,
the rightward scan consumes exactly that one. -/
theorem carry_to28_exact (h p anchor : Int) (t : Int → Bool)
    (hanchor : anchor≤h) (anchorZero : t anchor=false)
    (hp : h<p) (hone : t p=true)
    (between : ∀ q, h<q → q<p → t q=false) :
    ∃ j l : Nat,
      let mark := h-(j : Int)
      let scanHead := mark+1
      let u := put (result t h j) (scanHead+(l : Int)) false
      let head28 := scanHead+(l : Int)+1
      anchor≤mark ∧ mark≤h ∧ t mark=false ∧
      (∀ q, mark<q → q≤h → t q=true) ∧ head28=p+1 ∧ u mark=true ∧
      (∀ q, mark<q → q<head28 → u q=false) ∧
      (∀ q, h<q → head28≤q → u q=t q) ∧
      (∀ q, q<mark → u q=t q) ∧
      silentSegment machine (cfg 1 h t) (cfg 28 head28 u) ((j+1)+(l+1)) := by
  let k := (h-anchor).toNat
  have hk : h-(k : Int)=anchor := by
    have he : (k : Int)=h-anchor := Int.toNat_of_nonneg (by omega)
    omega
  obtain ⟨j,hj,hword⟩ := first_zero k h t (by simpa only [hk] using anchorZero)
  let mark := h-(j : Int)
  have ⟨hmarkZero,hmarkOnes⟩ := carry_word_exact t h j hword
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
    let i := (p-scanHead).toNat
    have hi : (i : Int)=p-scanHead := Int.toNat_of_nonneg (by omega)
    have hil : i<l := by dsimp [hit] at hn; omega
    have hz := hzeros i hil
    have he : scanHead+(i : Int)=p := by omega
    rw [he,hright] at hz
    contradiction
  have hhitOne : carried hit=true := by simpa only [hit] using hfirst
  have hhitgt : h<hit := by
    by_contra hn
    have hmarkHit : mark<hit := by dsimp [hit,scanHead]; omega
    have hz : carried hit=false := by
      dsimp [carried,result,put,cleared]
      simp only [if_neg (show hit≠h-(j : Int) by dsimp [mark] at hmarkHit; omega),
        if_pos (show h-(j : Int)<hit ∧ hit≤h by dsimp [mark] at hmarkHit; omega)]
    rw [hz] at hhitOne
    contradiction
  have hhitEq : hit=p := by
    by_contra hn
    have hp' : hit<p := by omega
    have he : carried hit=t hit := result_preserves_above t h hit j hhitgt
    rw [he,between hit hhitgt hp'] at hhitOne
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
  have hall := segAdd machine _ _ _ (j+1) (l+1) (scan t h j hword)
    (scan_to_one scanHead carried l hzeros hfirst)
  refine ⟨j,l,?_,by omega,hmarkZero,hmarkOnes,by change head28=p+1; dsimp [head28]; omega,umark,hcorr,hframe,hleft,?_⟩
  · omega
  · simpa only [mark,scanHead,hit,head28,u,carried] using hall


/-- For a zero gap followed by a marked one and a solid control run, the
carry sets its bounded left marker, clears the intervening control cells,
places the right marker immediately before the separator and preserves the
complete prefix and bank outside those cells. -/
theorem carry_to83_exact_control_relaxed (h p anchor separator : Int) (t : Int → Bool)
    (hanchor : anchor≤h) (anchorZero : t anchor=false)
    (hp : h<p) (hone : t p=true) (between : ∀ q, h<q → q<p → t q=false)
    (hsep : p+1≤separator) (ones : ∀ q, p<q → q<separator → t q=true)
    (blank : t separator=false) :
    ∃ (steps : Nat) (out : Int → Bool) (mark : Int), 0<steps ∧
      anchor≤mark ∧ mark≤h ∧ t mark=false ∧ (∀ q, mark<q → q≤h → t q=true) ∧ out mark=true ∧
      (∀ q, q<mark → out q=t q) ∧ (∀ q, mark<q → q<separator-1 → out q=false) ∧
      out (separator-1)=true ∧ (∀ q, separator≤q → out q=t q) ∧
      silentSegment machine (cfg 1 h t) (cfg 83 (mark-1) out) steps := by
  obtain ⟨j,l,hmarklo,hmarkle,hmarkZero,hmarkOnes,hheadEq,hmark,hcorr,hframe,hleft,hcarry⟩ :=
    carry_to28_exact h p anchor t hanchor anchorZero hp hone between
  let mark := h-(j : Int)
  let scanHead := mark+1
  let u := put (result t h j) (scanHead+(l : Int)) false
  let head28 := scanHead+(l : Int)+1
  have hhead : head28=p+1 := by simpa only [head28,scanHead,mark] using hheadEq
  have hus : u separator=false := by
    have he : u separator=t separator := hframe separator (by omega)
      (by simpa only [head28,scanHead,mark] using (show head28≤separator by omega))
    exact he.trans blank
  let k := (separator-head28).toNat
  have hk : head28+(k : Int)=separator := by
    have he : (k : Int)=separator-head28 := Int.toNat_of_nonneg (by omega)
    omega
  obtain ⟨m,stop,out,hm,hstop,houtmark,hzero,hones,hexact,hpres,hreturn⟩ :=
    state28_to83_exact head28 mark u (by dsimp [head28,scanHead]; omega)
      (by simpa only [u,head28,scanHead,mark] using hmark)
      (by simpa only [u,head28,scanHead,mark] using hcorr) k (by simpa only [hk] using hus)
  have hstoplt : stop<separator := by
    by_contra hh
    have ho := hones separator (by omega) (by omega)
    rw [hus] at ho
    contradiction
  have hstopEq : stop=separator-1 := by
    by_contra hh
    have ht : t (stop+1)=true := ones (stop+1) (by omega) (by omega)
    have hu : u (stop+1)=t (stop+1) := hframe (stop+1) (by omega)
      (by simpa only [head28,scanHead,mark] using (show head28≤stop+1 by omega))
    rw [hu,ht] at hzero
    contradiction
  have houtleft : ∀ q, q<mark → out q=t q := by
    intro q hq
    rw [hpres q (by dsimp [head28,scanHead]; omega)]
    exact hleft q (by simpa only [mark] using hq)
  have houtgap : ∀ q, mark<q → q<separator-1 → out q=false := by
    intro q hq hq'
    rw [hexact,put_other _ _ _ _ (by omega)]
    by_cases hq28 : q<head28
    · rw [show clearRange u head28 (stop+1) q=u q by
        simp only [clearRange,if_neg (show ¬ (head28≤q ∧ q<stop+1) by omega)]]
      exact hcorr q (by simpa only [mark] using hq) (by simpa only [head28,scanHead,mark] using hq28)
    · simp only [clearRange,if_pos (show head28≤q ∧ q<stop+1 by omega)]
  have houtrightMark : out (separator-1)=true := by
    rw [hexact,←hstopEq]
    simp [put]
  have houtbank : ∀ q, separator≤q → out q=t q := by
    intro q hq
    rw [hexact,put_other _ _ _ _ (by omega)]
    rw [show clearRange u head28 (stop+1) q=u q by
      simp only [clearRange,if_neg (show ¬ (head28≤q ∧ q<stop+1) by omega)]]
    exact hframe q (by omega) (by simpa only [head28,scanHead,mark] using (show head28≤q by omega))
  refine ⟨(j+1)+(l+1)+m,out,mark,by omega,?_,?_,hmarkZero,hmarkOnes,houtmark,houtleft,houtgap,houtrightMark,houtbank,?_⟩
  · simpa only [mark] using hmarklo
  · simpa only [mark] using hmarkle
  · exact segAdd machine _ _ _ _ _ (by simpa only [u,head28,scanHead,mark] using hcarry) hreturn

/-- Compatibility wrapper with the original stronger spacing hypothesis. -/
theorem carry_to83_exact_control (h p anchor separator : Int) (t : Int → Bool)
    (hanchor : anchor≤h) (anchorZero : t anchor=false)
    (hp : h<p) (hone : t p=true) (between : ∀ q, h<q → q<p → t q=false)
    (hsep : p+1<separator) (ones : ∀ q, p<q → q<separator → t q=true)
    (blank : t separator=false) :
    ∃ (steps : Nat) (out : Int → Bool) (mark : Int), 0<steps ∧
      anchor≤mark ∧ mark≤h ∧ t mark=false ∧ (∀ q, mark<q → q≤h → t q=true) ∧ out mark=true ∧
      (∀ q, q<mark → out q=t q) ∧ (∀ q, mark<q → q<separator-1 → out q=false) ∧
      out (separator-1)=true ∧ (∀ q, separator≤q → out q=t q) ∧
      silentSegment machine (cfg 1 h t) (cfg 83 (mark-1) out) steps := by
  exact carry_to83_exact_control_relaxed h p anchor separator t hanchor anchorZero hp hone between (by omega) ones blank

/-- The exact carry and selector return to the original parser origin with a
bounded changed marker, a fully cleared control gap, a right marker and an
unchanged bank. The graph successor is not identified by this theorem. -/
theorem carry_to_origin_exact_control_relaxed (h p origin separator : Int) (t : Int → Bool)
    (xs : List Bool) (hpos : h=origin+((xs.length : Nat) : Int)-1)
    (hanchor : origin+2≤h) (anchorZero : t (origin+2)=false)
    (count : xs.count false≤11) (word : Holds t origin xs)
    (first : t origin=true) (left : ∀ q, q<origin → t q=false)
    (hp : h<p) (hone : t p=true) (between : ∀ q, h<q → q<p → t q=false)
    (hsep : p+1≤separator) (ones : ∀ q, p<q → q<separator → t q=true)
    (blank : t separator=false) :
    ∃ (steps : Nat) (out : Int → Bool) (mark : Int), 0<steps ∧
      origin+2≤mark ∧ mark≤h ∧ t mark=false ∧ (∀ q, mark<q → q≤h → t q=true) ∧ out mark=true ∧
      (∀ q, q<mark → out q=t q) ∧ (∀ q, mark<q → q<separator-1 → out q=false) ∧
      out (separator-1)=true ∧ (∀ q, separator≤q → out q=t q) ∧
      silentSegment machine (cfg 1 h t) (cfg 93 (origin+1) out) steps := by
  obtain ⟨a,out,mark,ha,hlo,hhi,hmarkZero,hmarkOnes,hmark,hframe,hgap,hright,hbank,hcarry⟩ :=
    carry_to83_exact_control_relaxed h p (origin+2) separator t hanchor anchorZero hp hone between hsep ones blank
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
  exact ⟨a+b,out,mark,by omega,hlo,hhi,hmarkZero,hmarkOnes,hmark,hframe,hgap,hright,hbank,
    segAdd machine _ _ _ a b hcarry hselector⟩

/-- Compatibility wrapper with the original stronger spacing hypothesis. -/
theorem carry_to_origin_exact_control (h p origin separator : Int) (t : Int → Bool)
    (xs : List Bool) (hpos : h=origin+((xs.length : Nat) : Int)-1)
    (hanchor : origin+2≤h) (anchorZero : t (origin+2)=false)
    (count : xs.count false≤11) (word : Holds t origin xs)
    (first : t origin=true) (left : ∀ q, q<origin → t q=false)
    (hp : h<p) (hone : t p=true) (between : ∀ q, h<q → q<p → t q=false)
    (hsep : p+1<separator) (ones : ∀ q, p<q → q<separator → t q=true)
    (blank : t separator=false) :
    ∃ (steps : Nat) (out : Int → Bool) (mark : Int), 0<steps ∧
      origin+2≤mark ∧ mark≤h ∧ t mark=false ∧ (∀ q, mark<q → q≤h → t q=true) ∧ out mark=true ∧
      (∀ q, q<mark → out q=t q) ∧ (∀ q, mark<q → q<separator-1 → out q=false) ∧
      out (separator-1)=true ∧ (∀ q, separator≤q → out q=t q) ∧
      silentSegment machine (cfg 1 h t) (cfg 93 (origin+1) out) steps := by
  exact carry_to_origin_exact_control_relaxed h p origin separator t xs hpos hanchor anchorZero count word first left hp hone between (by omega) ones blank

/-- A single right marker immediately before the separator also suffices.
The output restores that marker, clears the gap, and preserves the bank. -/
theorem carry_to_origin_single_marker (h origin separator : Int) (t : Int → Bool)
    (xs : List Bool) (hpos : h=origin+((xs.length : Nat) : Int)-1)
    (hanchor : origin+2≤h) (anchorZero : t (origin+2)=false)
    (count : xs.count false≤11) (word : Holds t origin xs)
    (first : t origin=true) (left : ∀ q, q<origin → t q=false)
    (hp : h<separator-1) (hone : t (separator-1)=true)
    (between : ∀ q, h<q → q<separator-1 → t q=false)
    (blank : t separator=false) :
    ∃ (steps : Nat) (out : Int → Bool) (mark : Int), 0<steps ∧
      origin+2≤mark ∧ mark≤h ∧ t mark=false ∧ (∀ q, mark<q → q≤h → t q=true) ∧ out mark=true ∧
      (∀ q, q<mark → out q=t q) ∧ (∀ q, mark<q → q<separator-1 → out q=false) ∧
      out (separator-1)=true ∧ (∀ q, separator≤q → out q=t q) ∧
      silentSegment machine (cfg 1 h t) (cfg 93 (origin+1) out) steps := by
  exact carry_to_origin_exact_control_relaxed h (separator-1) origin separator t xs hpos hanchor
    anchorZero count word first left hp hone between (by omega) (by intro q hq hq'; omega) blank

/-- Exact control word determined by an unchanged prefix, a new one and the
subsequent cleared gap. -/
theorem control_word_of_frame (t out : Int → Bool) (origin mark separator : Int)
    (xs : List Bool) (n : Nat) (hlo : origin≤mark)
    (hhi : mark≤origin+((xs.length : Nat) : Int)) (word : Holds t origin xs)
    (unchanged : ∀ q, q<mark → out q=t q) (one : out mark=true)
    (gap : ∀ q, mark<q → q<separator-1 → out q=false)
    (room : mark+(n : Int)<separator-1) :
    Holds out origin (xs.take (mark-origin).toNat ++ true::List.replicate n false) := by
  let j := (mark-origin).toNat
  let pref := xs.take j
  have hj : (j : Int)=mark-origin := Int.toNat_of_nonneg (by omega)
  have hjle : j≤xs.length := by omega
  have hlen : pref.length=j := by simp [pref,List.length_take_of_le hjle]
  have hpref : Holds t origin pref := by
    apply holds_prefix t origin (xs.take j) (xs.drop j)
    simpa only [List.take_append_drop] using word
  have hout : Holds out origin pref := by
    apply holds_transport t out origin pref hpref
    intro q hq hq'
    exact (unchanged q (by rw [hlen] at hq'; omega)).symm
  have hz : Holds out (mark+1) (List.replicate n false) := by
    apply holds_of_get
    intro i hi
    have hi' : i<n := by simpa using hi
    have hq : mark<mark+1+(i : Int) := by omega
    have hq' : mark+1+(i : Int)<separator-1 := by omega
    simpa using gap (mark+1+(i : Int)) hq hq'
  have htail : Holds out mark (true::List.replicate n false) := ⟨one,hz⟩
  have he : origin+((pref.length : Nat) : Int)=mark := by rw [hlen]; omega
  have hall := holds_append_intro out origin pref (true::List.replicate n false) hout (by simpa only [he] using htail)
  simpa only [pref,j] using hall

/-- The exact carry produces every finite prefix of its new control word,
up to the right marker, and returns to the original parser origin. -/
theorem carry_to_origin_control_word_relaxed (h p origin separator : Int) (t : Int → Bool)
    (xs : List Bool) (hpos : h=origin+((xs.length : Nat) : Int)-1)
    (hanchor : origin+2≤h) (anchorZero : t (origin+2)=false)
    (count : xs.count false≤11) (word : Holds t origin xs)
    (first : t origin=true) (left : ∀ q, q<origin → t q=false)
    (hp : h<p) (hone : t p=true) (between : ∀ q, h<q → q<p → t q=false)
    (hsep : p+1≤separator) (ones : ∀ q, p<q → q<separator → t q=true)
    (blank : t separator=false) :
    ∃ (steps : Nat) (out : Int → Bool) (mark : Int), 0<steps ∧
      origin+2≤mark ∧ mark≤h ∧ t mark=false ∧ (∀ q, mark<q → q≤h → t q=true) ∧
      (∀ n : Nat, mark+(n : Int)<separator-1 →
        Holds out origin (xs.take (mark-origin).toNat ++ true::List.replicate n false)) ∧
      out (separator-1)=true ∧ (∀ q, separator≤q → out q=t q) ∧
      silentSegment machine (cfg 1 h t) (cfg 93 (origin+1) out) steps := by
  obtain ⟨steps,out,mark,hs,hlo,hhi,hzero,hones,hone',hprefix,hgap,hright,hbank,hseg⟩ :=
    carry_to_origin_exact_control_relaxed h p origin separator t xs hpos hanchor anchorZero count word first left
      hp hone between hsep ones blank
  refine ⟨steps,out,mark,hs,hlo,hhi,hzero,hones,?_,hright,hbank,hseg⟩
  intro n hn
  exact control_word_of_frame t out origin mark separator xs n (by omega) (by omega) word hprefix hone' hgap hn

/-- Compatibility wrapper with the original stronger spacing hypothesis. -/
theorem carry_to_origin_control_word (h p origin separator : Int) (t : Int → Bool)
    (xs : List Bool) (hpos : h=origin+((xs.length : Nat) : Int)-1)
    (hanchor : origin+2≤h) (anchorZero : t (origin+2)=false)
    (count : xs.count false≤11) (word : Holds t origin xs)
    (first : t origin=true) (left : ∀ q, q<origin → t q=false)
    (hp : h<p) (hone : t p=true) (between : ∀ q, h<q → q<p → t q=false)
    (hsep : p+1<separator) (ones : ∀ q, p<q → q<separator → t q=true)
    (blank : t separator=false) :
    ∃ (steps : Nat) (out : Int → Bool) (mark : Int), 0<steps ∧
      origin+2≤mark ∧ mark≤h ∧ t mark=false ∧ (∀ q, mark<q → q≤h → t q=true) ∧
      (∀ n : Nat, mark+(n : Int)<separator-1 →
        Holds out origin (xs.take (mark-origin).toNat ++ true::List.replicate n false)) ∧
      out (separator-1)=true ∧ (∀ q, separator≤q → out q=t q) ∧
      silentSegment machine (cfg 1 h t) (cfg 93 (origin+1) out) steps := by
  exact carry_to_origin_control_word_relaxed h p origin separator t xs hpos hanchor anchorZero count word first left hp hone between (by omega) ones blank

#print axioms carry_word_exact
#print axioms carry_to28_exact
#print axioms carry_to83_exact_control
#print axioms carry_to_origin_exact_control
#print axioms carry_to_origin_single_marker
#print axioms carry_to_origin_control_word
end Shared.Beeping.NPcoNP.NativeCarryExactControl
