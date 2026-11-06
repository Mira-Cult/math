import Shared.Beeping.NPcoNP.NativePositiveGenericFrame
import Shared.Beeping.NPcoNP.NativeBankReturn23Generic

/-! Positive-bank return for a supplied literal scanner chain. -/
namespace Shared.Beeping.NPcoNP.NativePositiveGenericReturn
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalfMarkerUnitContinue
open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.Native279BankScan
open Shared.Beeping.NPcoNP.NativePositiveGeneric
open Shared.Beeping.NPcoNP.NativePositiveGenericFrame
open Shared.Beeping.NPcoNP.NativeBankReturn23Generic
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 25000000

theorem positive_return_generic {q0 q1 q2 q3 : Fin 284} {m : Nat}
    (r0 : RightRow q0 q1) (r1 : RightRow q1 q2) (r2 : RightRow q2 q3)
    (chain : Chain m q3 42) (h separator : Int) (t : Int → Bool)
    (values : List Nat) (v : Nat) (vs : List Nat) (hlen : values.length=m)
    (hlong : h+6≤separator)
    (mark : t (h+2)=true) (z1 : t (h+3)=false) (z2 : t (h+4)=false)
    (ones : ∀ q, h+5≤q → q<separator → t q=true) (sep : t separator=false)
    (bank : Holds t (separator+1) (encode values ++ (encode ((v+1)::vs) ++ [false,false]))) :
    let pos := separator+1+((encode values).length : Int)
    ∃ (k : Nat) (out : Int → Bool), 0<k ∧
      Holds out pos (encode (v::vs) ++ [true,false,false]) ∧
      out (h+2)=false ∧ out (h+3)=false ∧ out (h+4)=true ∧
      (∀ q, h+5≤q → q<separator → out q=true) ∧ out separator=false ∧
      (∀ q, q<pos → q≠h+2 → q≠h+4 → out q=t q) ∧
      (∀ q, separator+1+((encode values).length : Int)+2+
        ((List.replicate v true ++ vs.flatMap (fun z => false :: List.replicate (z+1) true)).length : Int)<q → out q=t q) ∧
      (∃ bound : Int, ∀ q, bound≤q → out q=t q) ∧
      silentSegment machine (cfg q0 (h+3) t) (cfg 1 (h+1) out) k := by
  dsimp only
  let pos := separator+1+((encode values).length : Int)
  let touched := clearAt pos t
  let u := setAt (h+4) (clearAt (h+2) touched)
  let original := setAt pos u
  let suffix := List.replicate v true ++ vs.flatMap (fun z => false :: List.replicate (z+1) true)
  let f := pos+2+(suffix.length : Int)
  let out := spec original f (suffix.length+2)
  let r := (separator-(h+6)).toNat
  let ys := unaryBankPrefix r values
  let count := (separator-(h+5)).toNat+(encode values).length+5+(2*ys.reverse.length+7)+(2*suffix.length+7)
  obtain ⟨h2,h3,h4,hones,hsep,hframe,hresult⟩ :=
    NativePositiveGenericFrame.positive_control_frame r0 r1 r2 chain h separator t values v vs hlen hlong mark z1 z2 ones sep bank
  have hstep : silentSegment machine (cfg q0 (h+3) t) (cfg 23 (pos-2) out) count := by
    simpa only [pos,touched,u,original,suffix,f,out,r,ys,count] using
      (positive_touch_shift_generic r0 r1 r2 chain h separator t values v vs hlen hlong mark z1 z2 ones sep bank).2.2.2
  have hpref : Holds t (separator+1) (encode values) := holds_prefix_word t (separator+1) _ _ bank
  have hpref' : Holds out (separator+1) (encode values ++ []) := by
    have hp : Holds out (separator+1) (encode values) := by
      apply holds_transport t out _ _ hpref
      intro q hq hq'
      have hqpos : q<pos := by dsimp [pos]; omega
      exact (hframe q hqpos (by omega) (by omega)).symm
    simpa using hp
  have hc : ∀ q, (h+1)+4≤q → q<separator → out q=true := by
    intro q hq hq'
    exact hones q (by omega) hq'
  have h2' : out ((h+1)+1)=false := by
    simpa only [show h+1+1=h+2 by omega] using h2
  have h3' : out ((h+1)+2)=false := by
    simpa only [show h+1+2=h+3 by omega] using h3
  have h4' : out ((h+1)+3)=true := by
    simpa only [show h+1+3=h+4 by omega] using h4
  have hret := return23_generic_weak (h+1) separator out values [] (by omega)
    h2' h3' h4' hc hsep hpref'
  have hret' : silentSegment machine (cfg 23 (pos-2) out) (cfg 1 (h+1) out) (ys.length+3) := by
    have he : separator+((encode values).length : Int)-1=pos-2 := by dsimp [pos]; omega
    have hr : separator-(h+1+5)=separator-(h+6) := by omega
    simpa only [he,hr,r,ys] using hret
  have hall := segAdd machine _ _ _ count (ys.length+3) hstep hret'
  have htail := (positive_touch_shift_generic r0 r1 r2 chain h separator t values v vs hlen hlong mark z1 z2 ones sep bank).2.2.1
  change (∀ q, separator≤q → (q<pos ∨ f<q) → out q=t q) at htail
  have hright : ∀ q, max separator (f+1)≤q → out q=t q := by
    intro q hq
    apply htail q (le_trans (le_max_left _ _) hq)
    right
    have hf : f+1≤q := le_trans (le_max_right _ _) hq
    omega
  have hexact : ∀ q, f<q → out q=t q := by
    intro q hq
    apply htail q (by dsimp [f,pos] at hq; omega)
    exact Or.inr hq
  exact ⟨count+(ys.length+3),out,by omega,hresult,h2,h3,h4,hones,hsep,hframe,hexact,⟨max separator (f+1),hright⟩,hall⟩

#print axioms positive_return_generic
end Shared.Beeping.NPcoNP.NativePositiveGenericReturn
