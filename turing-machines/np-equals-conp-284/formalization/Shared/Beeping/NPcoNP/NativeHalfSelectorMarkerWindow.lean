import Shared.Beeping.NPcoNP.NativeHalfSelectorWindow
import Shared.Beeping.NPcoNP.NativeHalfEntryTo93

/-! Selector windows whose right neighbor is the carry marker. Unlike the
older `false :: encode xs` window, the last zero is not assumed at the marker. -/
namespace Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow

open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfSelectorExact
open Shared.Beeping.NPcoNP.NativeHalfSelectorWindow
open Shared.Beeping.NPcoNP.NativeHalfSelectorReturn
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.Bootstrap284CanonicalTape
open Shared.Beeping.NPcoNP.Bootstrap284BankDecode
open Shared.Beeping.NPcoNP.NativeHalfState1Layout
open Shared.Beeping.NPcoNP.NativeHalfEntryCorrect
open Shared.Beeping.NPcoNP.NativeHalfEntryTo93
open Shared.Beeping.NPcoNP.NativeHalfState1Canonical
open Shared.Beeping.NPcoNP.NativeHalfState1Scan
open Shared.Beeping.NPcoNP.NativeHalfState28Exact
open Shared.Beeping.NPcoNP.UnarySuffixShift
open Shared.Beeping.NPcoNP.UnaryBank

set_option maxRecDepth 8192
set_option maxHeartbeats 5000000

/-- The exact left-to-right window read backwards by the selector. -/
def markerWindow (xs : List Nat) : List Bool := (encode xs.reverse).reverse

@[simp] theorem markerWindow_length (xs : List Nat) :
    (markerWindow xs).length=(encode xs).length := by
  simp [markerWindow,encode_length_reverse]

/-- The old window consists of this window followed by a zero. -/
theorem markerWindow_append_zero (xs : List Nat) :
    markerWindow xs ++ [false]=false :: encode xs := by
  simpa [markerWindow] using encode_reverse xs.reverse

/-- The older full window requires a zero at the cell occupied by the carry
marker, so the two hypotheses cannot be silently identified. -/
theorem legacy_window_marker_zero (t : Int → Bool) (a : Int) (xs : List Nat)
    (hx : Holds t a (false :: encode xs)) :
    t (a+((encode xs).length : Int))=false := by
  rw [← markerWindow_append_zero xs] at hx
  have hi : (markerWindow xs).length<(markerWindow xs ++ [false]).length := by simp
  have ht := holds_get t a (markerWindow xs ++ [false]) hx (markerWindow xs).length hi
  simpa [markerWindow_length] using ht

theorem legacy_window_incompatible (t : Int → Bool) (a : Int) (xs : List Nat)
    (hm : t (a+((encode xs).length : Int))=true) :
    ¬ Holds t a (false :: encode xs) := by
  intro hx
  have hz := legacy_window_marker_zero t a xs hx
  rw [hm] at hz
  contradiction

/-- A finite leftward run of ones ending at the first zero has a unique length. -/
theorem carry_length_unique (t : Int → Bool) (h : Int) (k j : Nat)
    (hk : downHolds t h (List.replicate k true ++ [false]))
    (hj : downHolds t h (List.replicate j true ++ [false])) : k=j := by
  induction k generalizing h j with
  | zero =>
    cases j with
    | zero => rfl
    | succ j =>
      simp only [List.replicate_zero,List.nil_append,downHolds] at hk
      simp only [List.replicate_succ,List.cons_append,downHolds] at hj
      rw [hk.1] at hj
      cases hj.1
  | succ k ih =>
    cases j with
    | zero =>
      simp only [List.replicate_succ,List.cons_append,downHolds] at hk
      simp only [List.replicate_zero,List.nil_append,downHolds] at hj
      rw [hj.1] at hk
      cases hk.1
    | succ j =>
      simp only [List.replicate_succ,List.cons_append,downHolds] at hk hj
      have he := ih (h-1) j hk.2 hj.2
      exact congrArg Nat.succ he

/-- Fourteen blocks immediately left of a marker are read in reverse order.
No value is imposed on the marker or other cells. -/
theorem marker_window_to92 (t : Int → Bool) (a : Int) (xs : List Nat)
    (hl : xs.length=14) (hx : Holds t a (markerWindow xs)) :
    silentSegment machine (cfg 83 (a+((encode xs).length : Int)-1) t)
      (cfg 92 (a-1) t) (encode xs).length := by
  have hd := holds_reverse t a (markerWindow xs) hx
  have hd' : downHolds t (a+((encode xs).length : Int)-1) (encode xs.reverse) := by
    simpa [markerWindow,encode_length_reverse] using hd
  have hd'' : downHolds t (a+((encode xs).length : Int)-1) (encode xs.reverse ++ []) := by
    simpa using hd'
  have hs := (selector_on_values xs.reverse _ t [] (by simpa using hl) hd'').2
  have hlen := encode_length_reverse xs
  rw [hlen] at hs
  have hp : a+((encode xs).length : Int)-1-((encode xs).length : Int)=a-1 := by omega
  rw [hp] at hs
  exact hs

/-- A one immediately to the left completes the final state-92 scan in one
step, without changing the tape. -/
theorem marker_window_to93 (t : Int → Bool) (a : Int) (xs : List Nat)
    (hl : xs.length=14) (hx : Holds t a (markerWindow xs)) (hm : t (a-1)=true) :
    silentSegment machine (cfg 83 (a+((encode xs).length : Int)-1) t)
      (cfg 93 a t) ((encode xs).length+1) := by
  have hs := marker_window_to92 t a xs hl hx
  have hr := oneSeg machine _ _ (step92_one (a-1) t hm)
  have h := segAdd machine _ _ _ (encode xs).length 1 hs hr
  simpa using h

/-- Exact physical bank state after the carry, first-block scan and selector.
The first output block uses the selector's temporary unary-marker form. -/
def BankPost (back : Int → Bool) (ctrl : Int) (value : Nat) (left right : List Nat)
    (head : Int) (k : Nat) (out : Int → Bool) : Prop :=
  let values := left ++ [value/2] ++ right ++ List.replicate ((value+1)/2) 0
  ∃ (t : Int → Bool) (stop : Int),
    Holds t (ctrl+2) (encode values) ∧ t=state1Tape back ctrl head values ∧
    (∀ q≤head, t q=back q) ∧
    stop=ctrl+2+((values.headD 0 : Nat) : Int) ∧
    (∀ q, ctrl+3+((values.headD 0 : Nat) : Int)≤q → out q=t q) ∧
    (∃ tail, values=(values.headD 0)::tail ∧
      Holds out (ctrl+2) (List.replicate (values.headD 0) false ++ [true,false]) ∧
      Holds out (ctrl+4+((values.headD 0 : Nat) : Int)) (encode tail)) ∧
    out=put (clearRange (put (result t head k) (ctrl+2) false) (ctrl+3) (stop+1)) stop true

/-- Complete selector-output tape, expressed using only the original prefix,
returned control head, carry length and updated finite bank. -/
def selectorOutputTape (back : Int → Bool) (ctrl : Int) (value : Nat)
    (left right : List Nat) (head : Int) (k : Nat) : Int → Bool :=
  let values := left ++ [value/2] ++ right ++ List.replicate ((value+1)/2) 0
  let stop := ctrl+2+((values.headD 0 : Nat) : Int)
  put (clearRange (put (result (state1Tape back ctrl head values) head k)
    (ctrl+2) false) (ctrl+3) (stop+1)) stop true

/-- The existential intermediate tape and stop in `BankPost` are unique;
the postcondition therefore fixes every output cell. -/
theorem bankPost_out_eq (back : Int → Bool) (ctrl : Int) (value : Nat)
    (left right : List Nat) (head : Int) (k : Nat) (out : Int → Bool)
    (h : BankPost back ctrl value left right head k out) :
    out=selectorOutputTape back ctrl value left right head k := by
  dsimp [BankPost] at h
  obtain ⟨t,stop,hbank,hcanonical,hprefix,hstop,hframe,hphysical,hexact⟩ := h
  dsimp [selectorOutputTape]
  rw [hcanonical,hstop] at hexact
  exact hexact

/-- The unchanged suffix of a bank postcondition decodes to exactly the
remaining register values. -/
theorem bankPost_suffix_decodes (back : Int → Bool) (ctrl : Int) (value : Nat)
    (left right : List Nat) (head : Int) (k : Nat) (out : Int → Bool)
    (h : BankPost back ctrl value left right head k out) :
    let values := left ++ [value/2] ++ right ++ List.replicate ((value+1)/2) 0
    ∃ tail, values=(values.headD 0)::tail ∧
      decode tail.length (readCells out (ctrl+4+((values.headD 0 : Nat) : Int)) (encode tail).length)=some (tail,[]) := by
  dsimp [BankPost] at h
  dsimp only
  obtain ⟨t,stop,hbank,hcanonical,hprefix,hstop,hframe,⟨tail,hvalues,hfirst,htail⟩,hexact⟩ := h
  refine ⟨tail,hvalues,?_⟩
  rw [read_of_holds _ _ _ htail]
  simpa only [List.append_nil] using decode_encode tail []

/-- If every carry location compatible with the supplied control prefix has
this finite fourteen-block window and its left marker, the actual selected
entry reaches state 93 at the exact window boundary. The hypothesis is only a
tape layout condition; selector reachability and silent progress are proved. -/
theorem selected_entry_to93_with_window (back : Int → Bool) (ctrl z : Int)
    (value : Nat) (left right xs : List Nat) (hz : ∀ p≤z, back p=false)
    (hl : xs.length=14)
    (hwindow : ∀ (head : Int) (k : Nat),
      (value%2=1 → head=ctrl-1) → (value%2=0 → head≤ctrl-2) →
      (value%2=0 → back (head+1)=false) →
      (value%2=0 → ∀ q, head+1<q → q<ctrl → back q=true) →
      downHolds back head (List.replicate k true ++ [false]) →
      let p := head-(k : Int)
      let a := p-((encode xs).length : Int)
      Holds back a (markerWindow xs) ∧ back (a-1)=true) :
    let base := before back ctrl (leftSuffix left)
    let b := ctrl+2+((leftSuffix left).length : Int)
    ∃ (n : Nat) (p : Int) (out : Int → Bool), 0<n ∧
      (∃ (head : Int) (k : Nat), p=head-(k : Int) ∧
        (value%2=1 → head=ctrl-1) ∧ (value%2=0 → head≤ctrl-2) ∧
        (value%2=0 → back (head+1)=false) ∧
        (value%2=0 → ∀ q, head+1<q → q<ctrl → back q=true) ∧
        downHolds back head (List.replicate k true ++ [false]) ∧
        BankPost back ctrl value left right head k out) ∧
      out p=true ∧ (∀ q<p, out q=back q) ∧
      silentSegment machine (cfg 29 (b-1) (selectedTape base b value right))
        (cfg 93 (p-((encode xs).length : Int)) out) n := by
  dsimp only
  obtain ⟨n,p,e,hn,hstate,hhead,hcarry,hmark,hfound,hprefix,hfirst⟩ :=
    selected_entry_to83 back ctrl z value left right hz
  obtain ⟨head,k,t,stop,hp,hodd,heven,hstop,hones,hdown,hbank,hcanonical,hback,hstoppos,hframe,hphysical,hexact⟩ := hcarry
  have hw := hwindow head k hodd heven hstop hones hdown
  rw [← hp] at hw
  let a := p-((encode xs).length : Int)
  have hwin : Holds e.tape a (markerWindow xs) := by
    apply holds_transport back e.tape a (markerWindow xs) hw.1
    intro q hq hq'
    symm
    apply hprefix
    have hlen := markerWindow_length xs
    rw [hlen] at hq'
    dsimp [a] at hq'
    omega
  have hleft : e.tape (a-1)=true := by
    rw [hprefix (a-1) (by dsimp [a]; omega)]
    exact hw.2
  have hseg := marker_window_to93 e.tape a xs hl hwin hleft
  have hpos : a+((encode xs).length : Int)-1=e.head := by rw [hhead]; dsimp [a]; omega
  rw [hpos] at hseg
  have he : e=cfg 83 e.head e.tape := by
    have hh : e=cfg e.state e.head e.tape := by cases e; rfl
    simpa only [hstate] using hh
  rw [← he] at hseg
  refine ⟨n+((encode xs).length+1),p,e.tape,by omega,⟨head,k,hp,hodd,heven,hstop,hones,hdown,⟨t,stop,hbank,hcanonical,hback,hstoppos,hframe,hphysical,hexact⟩⟩,hmark,hprefix,?_⟩
  exact segAdd machine _ _ _ n ((encode xs).length+1) hfirst hseg

/-- For an odd selected value, the actual carry location is the first zero
of the supplied prefix, so only that one concrete fourteen-block window is
required. -/
theorem selected_odd_entry_to93_with_window (back : Int → Bool) (ctrl z : Int)
    (value : Nat) (left right xs : List Nat) (k : Nat)
    (hz : ∀ p≤z, back p=false) (ho : value%2=1) (hl : xs.length=14)
    (hcarry : downHolds back (ctrl-1) (List.replicate k true ++ [false]))
    (hwin : Holds back (ctrl-1-(k : Int)-((encode xs).length : Int)) (markerWindow xs))
    (hleft : back (ctrl-1-(k : Int)-((encode xs).length : Int)-1)=true) :
    let base := before back ctrl (leftSuffix left)
    let b := ctrl+2+((leftSuffix left).length : Int)
    let p := ctrl-1-(k : Int)
    ∃ (n : Nat) (out : Int → Bool), 0<n ∧
      BankPost back ctrl value left right (ctrl-1) k out ∧ out p=true ∧
      (∀ q<p, out q=back q) ∧
      silentSegment machine (cfg 29 (b-1) (selectedTape base b value right))
        (cfg 93 (p-((encode xs).length : Int)) out) n := by
  dsimp only
  have hwindow : ∀ (head : Int) (j : Nat),
      (value%2=1 → head=ctrl-1) → (value%2=0 → head≤ctrl-2) →
      (value%2=0 → back (head+1)=false) →
      (value%2=0 → ∀ q, head+1<q → q<ctrl → back q=true) →
      downHolds back head (List.replicate j true ++ [false]) →
      let p := head-(j : Int)
      let a := p-((encode xs).length : Int)
      Holds back a (markerWindow xs) ∧ back (a-1)=true := by
    intro head j hodd heven hstop hones hdown
    have hh : head=ctrl-1 := hodd ho
    subst head
    have hj : j=k := carry_length_unique back (ctrl-1) j k hdown hcarry
    subst j
    exact ⟨hwin,hleft⟩
  obtain ⟨n,p,out,hn,hmeta,hm,hprefix,hseg⟩ :=
    selected_entry_to93_with_window back ctrl z value left right xs hz hl hwindow
  obtain ⟨head,j,hp,hodd,heven,hstop,hones,hdown,hbankpost⟩ := hmeta
  have hh : head=ctrl-1 := hodd ho
  subst head
  have hj : j=k := carry_length_unique back (ctrl-1) j k hdown hcarry
  subst j
  subst p
  exact ⟨n,out,hn,hbankpost,hm,hprefix,hseg⟩

/-- The first zero left of a run of ones has a unique predecessor. -/
theorem clearing_head_unique (back : Int → Bool) (ctrl h h' : Int)
    (hb : h≤ctrl-2) (hb' : h'≤ctrl-2)
    (hz : back (h+1)=false) (hz' : back (h'+1)=false)
    (ho : ∀ q, h+1<q → q<ctrl → back q=true)
    (ho' : ∀ q, h'+1<q → q<ctrl → back q=true) : h=h' := by
  by_contra hn
  by_cases hlt : h<h'
  · have ht := ho (h'+1) (by omega) (by omega)
    rw [hz'] at ht
    contradiction
  · have ht := ho' (h+1) (by omega) (by omega)
    rw [hz] at ht
    contradiction

/-- For an even selected value, the first zero consumed by state 95 and the
subsequent carry uniquely determine the one concrete selector window. -/
theorem selected_even_entry_to93_with_window (back : Int → Bool) (ctrl z : Int)
    (value : Nat) (left right xs : List Nat) (head : Int) (k : Nat)
    (hz : ∀ p≤z, back p=false) (he : value%2=0) (hl : xs.length=14)
    (hbound : head≤ctrl-2) (hstop : back (head+1)=false)
    (hones : ∀ q, head+1<q → q<ctrl → back q=true)
    (hcarry : downHolds back head (List.replicate k true ++ [false]))
    (hwin : Holds back (head-(k : Int)-((encode xs).length : Int)) (markerWindow xs))
    (hleft : back (head-(k : Int)-((encode xs).length : Int)-1)=true) :
    let base := before back ctrl (leftSuffix left)
    let b := ctrl+2+((leftSuffix left).length : Int)
    let p := head-(k : Int)
    ∃ (n : Nat) (out : Int → Bool), 0<n ∧
      BankPost back ctrl value left right head k out ∧ out p=true ∧
      (∀ q<p, out q=back q) ∧
      silentSegment machine (cfg 29 (b-1) (selectedTape base b value right))
        (cfg 93 (p-((encode xs).length : Int)) out) n := by
  dsimp only
  have hwindow : ∀ (h : Int) (j : Nat),
      (value%2=1 → h=ctrl-1) → (value%2=0 → h≤ctrl-2) →
      (value%2=0 → back (h+1)=false) →
      (value%2=0 → ∀ q, h+1<q → q<ctrl → back q=true) →
      downHolds back h (List.replicate j true ++ [false]) →
      let p := h-(j : Int)
      let a := p-((encode xs).length : Int)
      Holds back a (markerWindow xs) ∧ back (a-1)=true := by
    intro h j hodd heven hzero htrue hdown
    have hh : h=head := clearing_head_unique back ctrl h head (heven he) hbound
      (hzero he) hstop (htrue he) hones
    subst h
    have hj : j=k := carry_length_unique back head j k hdown hcarry
    subst j
    exact ⟨hwin,hleft⟩
  obtain ⟨n,p,out,hn,hmeta,hm,hprefix,hseg⟩ :=
    selected_entry_to93_with_window back ctrl z value left right xs hz hl hwindow
  obtain ⟨h,j,hp,hodd,heven,hzero,htrue,hdown,hbankpost⟩ := hmeta
  have hh : h=head := clearing_head_unique back ctrl h head (heven he) hbound
    (hzero he) hstop (htrue he) hones
  subst h
  have hj : j=k := carry_length_unique back head j k hdown hcarry
  subst j
  subst p
  exact ⟨n,out,hn,hbankpost,hm,hprefix,hseg⟩

/-- Exact whole-tape output for an odd selected value with the specified
finite control and selector windows. -/
theorem selected_odd_entry_to93_exact (back : Int → Bool) (ctrl z : Int)
    (value : Nat) (left right xs : List Nat) (k : Nat)
    (hz : ∀ p≤z, back p=false) (ho : value%2=1) (hl : xs.length=14)
    (hcarry : downHolds back (ctrl-1) (List.replicate k true ++ [false]))
    (hwin : Holds back (ctrl-1-(k : Int)-((encode xs).length : Int)) (markerWindow xs))
    (hleft : back (ctrl-1-(k : Int)-((encode xs).length : Int)-1)=true) :
    let base := before back ctrl (leftSuffix left)
    let b := ctrl+2+((leftSuffix left).length : Int)
    let p := ctrl-1-(k : Int)
    let out := selectorOutputTape back ctrl value left right (ctrl-1) k
    ∃ n : Nat, 0<n ∧ out p=true ∧ (∀ q<p, out q=back q) ∧
      silentSegment machine (cfg 29 (b-1) (selectedTape base b value right))
        (cfg 93 (p-((encode xs).length : Int)) out) n := by
  dsimp only
  obtain ⟨n,out,hn,hpost,hmark,hprefix,hseg⟩ :=
    selected_odd_entry_to93_with_window back ctrl z value left right xs k hz ho hl hcarry hwin hleft
  have he := bankPost_out_eq back ctrl value left right (ctrl-1) k out hpost
  rw [he] at hmark hprefix hseg
  exact ⟨n,hn,hmark,hprefix,hseg⟩

/-- Exact whole-tape output for an even selected value with the specified
finite control and selector windows. -/
theorem selected_even_entry_to93_exact (back : Int → Bool) (ctrl z : Int)
    (value : Nat) (left right xs : List Nat) (head : Int) (k : Nat)
    (hz : ∀ p≤z, back p=false) (he : value%2=0) (hl : xs.length=14)
    (hbound : head≤ctrl-2) (hstop : back (head+1)=false)
    (hones : ∀ q, head+1<q → q<ctrl → back q=true)
    (hcarry : downHolds back head (List.replicate k true ++ [false]))
    (hwin : Holds back (head-(k : Int)-((encode xs).length : Int)) (markerWindow xs))
    (hleft : back (head-(k : Int)-((encode xs).length : Int)-1)=true) :
    let base := before back ctrl (leftSuffix left)
    let b := ctrl+2+((leftSuffix left).length : Int)
    let p := head-(k : Int)
    let out := selectorOutputTape back ctrl value left right head k
    ∃ n : Nat, 0<n ∧ out p=true ∧ (∀ q<p, out q=back q) ∧
      silentSegment machine (cfg 29 (b-1) (selectedTape base b value right))
        (cfg 93 (p-((encode xs).length : Int)) out) n := by
  dsimp only
  obtain ⟨n,out,hn,hpost,hmark,hprefix,hseg⟩ :=
    selected_even_entry_to93_with_window back ctrl z value left right xs head k
      hz he hl hbound hstop hones hcarry hwin hleft
  have hout := bankPost_out_eq back ctrl value left right head k out hpost
  rw [hout] at hmark hprefix hseg
  exact ⟨n,hn,hmark,hprefix,hseg⟩

end Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow

#print axioms Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow.legacy_window_incompatible
#print axioms Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow.marker_window_to93
#print axioms Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow.selected_entry_to93_with_window

#print axioms Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow.selected_odd_entry_to93_with_window

#print axioms Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow.selected_even_entry_to93_with_window

#print axioms Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow.bankPost_suffix_decodes

#print axioms Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow.selected_odd_entry_to93_exact
#print axioms Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow.selected_even_entry_to93_exact
