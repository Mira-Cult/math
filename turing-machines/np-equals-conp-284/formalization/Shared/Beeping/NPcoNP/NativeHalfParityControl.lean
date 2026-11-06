import Shared.Beeping.NPcoNP.NativeHalfEntryTo93
import Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
import Shared.Beeping.NPcoNP.NativeHalfWindowDispatch

/-! A paid native-HALF return has distinguishable parity control effects when
its supplied control prefix ends in a zero separator. Graph interpretation
and reachability of that separator remain separate obligations. -/
namespace Shared.Beeping.NPcoNP.NativeHalfParityControl
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState1Scan
open Shared.Beeping.NPcoNP.NativeHalfMarkerRetain
open Shared.Beeping.NPcoNP.NativeHalfState1Layout
open Shared.Beeping.NPcoNP.NativeHalfState1Canonical
open Shared.Beeping.NPcoNP.NativeHalfEntryCorrect
open Shared.Beeping.NPcoNP.NativeHalfEntryTo93
open Shared.Beeping.NPcoNP.NativeHalfCarryTo93
open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.NativeHalfSelectorExact
open Shared.Beeping.NPcoNP.NativeHalfWindowDispatch
open Shared.Beeping.NPcoNP.NativeHalfState28Exact
open Shared.Beeping.NPcoNP.UnarySuffixShift
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 9000000

/-- Under a zero immediately before the control header, the paid carry
encodes odd and even results at distinct marker positions and in that cell.
The supplied `BankPost` is the complete physical output relation. -/
theorem parity_from_bankPost (back : Int → Bool) (ctrl : Int) (value : Nat)
    (left right : List Nat) (head : Int) (k : Nat) (p : Int) (out : Int → Bool)
    (separator : back (ctrl-1)=false) (hp : p=head-(k : Int))
    (hodd : value%2=1 → head=ctrl-1) (heven : value%2=0 → head≤ctrl-2)
    (hword : downHolds back head (List.replicate k true ++ [false]))
    (hmarker : out p=true) (hpost : BankPost back ctrl value left right head k out) :
    (value%2=1 → p=ctrl-1) ∧ (value%2=0 → p<ctrl-1) ∧
    (out (ctrl-1)=true ↔ value%2=1) := by
  dsimp [BankPost] at hpost
  obtain ⟨t,stop,hbank,hcanonical,htprefix,hstopFirst,hrightFrame,hphysicalBank,hexact⟩ := hpost
  have hoddpos : value%2=1 → p=ctrl-1 := by
    intro hv
    have hh := hodd hv
    have hk : k=0 := by
      cases k with
      | zero => rfl
      | succ k =>
        simp only [List.replicate_succ,List.cons_append,downHolds] at hword
        have hc : back (ctrl-1)=true := by simpa only [hh] using hword.1
        rw [separator] at hc
        contradiction
    rw [hk] at hp
    simpa [hh] using hp
  have hevenpos : value%2=0 → p<ctrl-1 := by
    intro hv
    have hh := heven hv
    omega
  have hevenbit : value%2=0 → out (ctrl-1)=false := by
    intro hv
    have hh := heven hv
    have htc : t (ctrl-1)=false := by
      rw [hcanonical]
      unfold state1Tape
      rw [before_prefix _ _ _ _ (by omega)]
      split_ifs with h
      · rfl
      · exact separator
    have hstopgt : ctrl+2≤stop := by rw [hstopFirst]; omega
    rw [hexact,put_other _ _ _ _ (by omega)]
    change (if ctrl+3≤ctrl-1 ∧ ctrl-1<stop+1 then false else
      put (result t head k) (ctrl+2) false (ctrl-1))=false
    rw [if_neg (by omega),put_other _ _ _ _ (by omega)]
    rw [result_preserves_above t head (ctrl-1) k (by omega)]
    exact htc
  have hbit : out (ctrl-1)=true ↔ value%2=1 := by
    constructor
    · intro hc
      by_contra hn
      have hv : value%2=0 := by omega
      rw [hevenbit hv] at hc
      contradiction
    · intro hv
      rw [← hoddpos hv]
      exact hmarker
  exact ⟨hoddpos,hevenpos,hbit⟩

/-- Under the explicit separator condition, odd and even selected values
leave different bits in the control cell. The complete paid native-HALF
computation and subsequent selector scan are silent and finite. The updated
bank's first encoded block is partially consumed by the selector, as stated
by the physical bank postcondition. -/
theorem selected_entry_to93_parity (back : Int → Bool) (ctrl z : Int)
    (value : Nat) (left right : List Nat) (hz : ∀ p≤z, back p=false)
    (separator : back (ctrl-1)=false) :
    let base := before back ctrl (leftSuffix left)
    let b := ctrl+2+((leftSuffix left).length : Int)
    let values := left ++ [value/2] ++ right ++ List.replicate ((value+1)/2) 0
    ∃ (n : Nat) (p : Int) (e : Config 284), 0<n ∧ e.state=93 ∧
      (value%2=1 → p=ctrl-1) ∧ (value%2=0 → p<ctrl-1) ∧
      (e.tape (ctrl-1)=true ↔ value%2=1) ∧
      e.tape p=true ∧ (∀ q<p, e.tape q=back q) ∧
      (∃ tail, values=(values.headD 0)::tail ∧
        Holds e.tape (ctrl+2) (List.replicate (values.headD 0) false ++ [true,false]) ∧
        Holds e.tape (ctrl+4+((values.headD 0 : Nat):Int)) (encode tail)) ∧
      silentSegment machine (cfg 29 (b-1) (selectedTape base b value right)) e n := by
  dsimp only
  let base := before back ctrl (leftSuffix left)
  let b := ctrl+2+((leftSuffix left).length : Int)
  let values := left ++ [value/2] ++ right ++ List.replicate ((value+1)/2) 0
  obtain ⟨m,p,c,hm,hstate,hhead,hcarry,hmarker,hfound,hprefix,hseg⟩ :=
    selected_entry_to83 back ctrl z value left right hz
  obtain ⟨head,k,t,stop,hp,hodd,heven,hstop,hones,hword,hbank,hcanonical,
    htprefix,hstopFirst,hrightFrame,hphysicalBank,hexact⟩ := hcarry
  have hpost : BankPost back ctrl value left right head k c.tape :=
    ⟨t,stop,hbank,hcanonical,htprefix,hstopFirst,hrightFrame,hphysicalBank,hexact⟩
  obtain ⟨hoddpos,hevenpos,hcbit⟩ :=
    parity_from_bankPost back ctrl value left right head k p c.tape separator hp hodd heven hword hmarker hpost
  have htail : ∀ q≤min z (p-1), c.tape q=false := by
    intro q hq
    have hzq : q≤z := le_trans hq (min_le_left _ _)
    have hpq : q<p := by have := le_trans hq (min_le_right z (p-1)); omega
    rw [hprefix q hpq]
    exact hz q hzq
  obtain ⟨n,e,hn,hstate',htape,hcont⟩ :=
    state83_to_93 c.head (min z (p-1)) c.tape htail hfound
  have hcfg : c=cfg 83 c.head c.tape := by
    have he : c=cfg c.state c.head c.tape := by cases c; rfl
    simpa only [hstate] using he
  have hseg' : silentSegment machine c e n := by simpa [← hcfg] using hcont
  refine ⟨m+n,p,e,by omega,hstate',hoddpos,hevenpos,?_,?_,?_,?_,?_⟩
  · rw [htape]; exact hcbit
  · rw [htape]; exact hmarker
  · intro q hq; rw [htape]; exact hprefix q hq
  · rw [htape]; exact hphysicalBank
  · exact segAdd machine _ _ _ m n hseg hseg'

/-- With the same fourteen-block layout hypothesis used by the selector
refinement, the parity bit survives to the exact state-93 selector boundary.
The full bank postcondition and the old prefix are retained. -/
theorem selected_entry_to93_window_parity (back : Int → Bool) (ctrl z : Int)
    (value : Nat) (left right xs : List Nat) (hz : ∀ q≤z, back q=false)
    (separator : back (ctrl-1)=false) (hl : xs.length=14)
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
      (value%2=1 → p=ctrl-1) ∧ (value%2=0 → p<ctrl-1) ∧
      (out (ctrl-1)=true ↔ value%2=1) ∧
      out p=true ∧ (∀ q<p, out q=back q) ∧
      (∃ (head : Int) (k : Nat), p=head-(k : Int) ∧
        (value%2=1 → head=ctrl-1) ∧ (value%2=0 → head≤ctrl-2) ∧
        (value%2=0 → back (head+1)=false) ∧
        (value%2=0 → ∀ q, head+1<q → q<ctrl → back q=true) ∧
        downHolds back head (List.replicate k true ++ [false]) ∧
        BankPost back ctrl value left right head k out) ∧
      silentSegment machine (cfg 29 (b-1) (selectedTape base b value right))
        (cfg 93 (p-((encode xs).length : Int)) out) n := by
  dsimp only
  obtain ⟨n,p,out,hn,hmeta,hmarker,hprefix,hseg⟩ :=
    selected_entry_to93_with_window back ctrl z value left right xs hz hl hwindow
  have hmeta' := hmeta
  obtain ⟨head,k,hp,hodd,heven,hstop,hones,hword,hpost⟩ := hmeta
  obtain ⟨ho,he,hbit⟩ :=
    parity_from_bankPost back ctrl value left right head k p out separator hp hodd heven hword hmarker hpost
  exact ⟨n,p,out,hn,ho,he,hbit,hmarker,hprefix,hmeta',hseg⟩

/-- The same return contract pays the first physical dispatcher transition
after state 93, reaching state 6 with the branch bit and bank unchanged. -/
theorem selected_entry_to6_window_parity (back : Int → Bool) (ctrl z : Int)
    (value : Nat) (left right xs : List Nat) (hz : ∀ q≤z, back q=false)
    (separator : back (ctrl-1)=false) (hl : xs.length=14)
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
      (value%2=1 → p=ctrl-1) ∧ (value%2=0 → p<ctrl-1) ∧
      (out (ctrl-1)=true ↔ value%2=1) ∧ out p=true ∧
      (∀ q<p, out q=back q) ∧
      (∃ (head : Int) (k : Nat), BankPost back ctrl value left right head k out) ∧
      silentSegment machine (cfg 29 (b-1) (selectedTape base b value right))
        (cfg 6 (p-((encode xs).length : Int)+1) out) n := by
  dsimp only
  obtain ⟨n,p,out,hn,hoddpos,hevenpos,hbit,hmarker,hprefix,hmeta,hseg⟩ :=
    selected_entry_to93_window_parity back ctrl z value left right xs hz separator hl hwindow
  obtain ⟨head,k,hp,hodd,heven,hstop,hones,hword,hpost⟩ := hmeta
  have hw := hwindow head k hodd heven hstop hones hword
  rw [← hp] at hw
  have hcont := selected_window_to6 back out p xs _ n hl hw.1 hprefix hseg
  exact ⟨n+1,p,out,by omega,hoddpos,hevenpos,hbit,hmarker,hprefix,⟨head,k,hpost⟩,hcont⟩

/-- Every nonempty unary marker window ends in a one. -/
theorem marker_window_last_one (t : Int → Bool) (a : Int) (xs : List Nat)
    (hne : xs≠[]) (hw : Holds t a (markerWindow xs)) :
    t (a+((encode xs).length : Int)-1)=true := by
  have hrev := Shared.Beeping.NPcoNP.NativeHalfSelectorWindow.holds_reverse t a (markerWindow xs) hw
  have hrevxs : xs.reverse≠[] := by simpa using hne
  obtain ⟨v,vs,hxs⟩ := List.exists_cons_of_ne_nil hrevxs
  have hlen : (encode (v::vs)).length=(encode xs).length := by
    rw [← hxs]
    exact encode_length_reverse xs
  have ht : downHolds t (a+((encode xs).length : Int)-1) (encode (v::vs)) := by
    simpa [markerWindow,markerWindow_length,hxs,hlen] using hrev
  simp [encode,block,List.replicate_succ,downHolds] at ht
  exact ht.1

/-- In the odd branch, the selected-window hypothesis and separator force
an adjacent one. A second zero at that cell would make the hypothesis
inconsistent, so it cannot be silently added as a common branch invariant. -/
theorem odd_window_requires_previous_one (back : Int → Bool) (ctrl : Int)
    (value : Nat) (xs : List Nat) (ho : value%2=1)
    (separator : back (ctrl-1)=false) (hl : xs.length=14)
    (hwindow : ∀ (head : Int) (k : Nat),
      (value%2=1 → head=ctrl-1) → (value%2=0 → head≤ctrl-2) →
      (value%2=0 → back (head+1)=false) →
      (value%2=0 → ∀ q, head+1<q → q<ctrl → back q=true) →
      downHolds back head (List.replicate k true ++ [false]) →
      let p := head-(k : Int)
      let a := p-((encode xs).length : Int)
      Holds back a (markerWindow xs) ∧ back (a-1)=true) :
    back (ctrl-2)=true := by
  have hcarry : downHolds back (ctrl-1) (List.replicate 0 true ++ [false]) := by
    simpa [downHolds] using separator
  have hw := hwindow (ctrl-1) 0 (by intro _; rfl) (by intro he; omega)
    (by intro he; omega) (by intro he; omega) hcarry
  have hne : xs≠[] := by intro hn; simp [hn] at hl
  have he := marker_window_last_one back (ctrl-1-(0:Int)-((encode xs).length : Int)) xs hne hw.1
  have hp : ctrl-1-(0:Int)-((encode xs).length : Int)+((encode xs).length : Int)-1=ctrl-2 := by omega
  rwa [hp] at he

/-- A double-zero boundary cannot simultaneously satisfy the odd selector
window hypothesis. -/
theorem odd_double_zero_window_impossible (back : Int → Bool) (ctrl : Int)
    (value : Nat) (xs : List Nat) (ho : value%2=1)
    (separator : back (ctrl-1)=false) (separator2 : back (ctrl-2)=false) (hl : xs.length=14)
    (hwindow : ∀ (head : Int) (k : Nat),
      (value%2=1 → head=ctrl-1) → (value%2=0 → head≤ctrl-2) →
      (value%2=0 → back (head+1)=false) →
      (value%2=0 → ∀ q, head+1<q → q<ctrl → back q=true) →
      downHolds back head (List.replicate k true ++ [false]) →
      let p := head-(k : Int)
      let a := p-((encode xs).length : Int)
      Holds back a (markerWindow xs) ∧ back (a-1)=true) : False := by
  have h := odd_window_requires_previous_one back ctrl value xs ho separator hl hwindow
  rw [separator2] at h
  contradiction

#print axioms parity_from_bankPost
#print axioms selected_entry_to93_parity
#print axioms selected_entry_to93_window_parity
#print axioms selected_entry_to6_window_parity
#print axioms marker_window_last_one
#print axioms odd_window_requires_previous_one
#print axioms odd_double_zero_window_impossible
end Shared.Beeping.NPcoNP.NativeHalfParityControl
