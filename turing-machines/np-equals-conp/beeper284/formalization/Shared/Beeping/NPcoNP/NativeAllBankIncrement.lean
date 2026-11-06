import Shared.Beeping.NPcoNP.NativeAllBankScan
import Shared.Beeping.NPcoNP.NativeIncrementGeneric

/-! Uniform literal increment through the bank insertion and state-23 return.
The initial window is supplied; later control carry and reselection are separate. -/
namespace Shared.Beeping.NPcoNP.NativeAllBankIncrement
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.NativeAllBankScan
open Shared.Beeping.NPcoNP.NativeIncrementGeneric
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 131072
set_option maxHeartbeats 25000000

/-- Every increment entry scans to its indexed unary block, restores the
control scan, inserts one unit into the target value, and reaches state 23
silently. The supplied control run is nonempty and the bank sentinel explicit.
This does not cover the following carry or reachability of the input window. -/
theorem increment_to23 (n : Fin 12) (h : Int) (t : Int → Bool) (k : Nat)
    (values : List Nat) (value : Nat) (rest : List Nat)
    (marker : t h=true) (hlen : values.length=n.val) (hk : 0<k)
    (h0 : t (h+1)=false) (h1 : t (h+2)=false)
    (control : ∀ i : Nat, i<k → t (h+3+(i : Int))=true)
    (delimiter : t (h+3+(k : Int))=false)
    (bank : Holds t (h+4+(k : Int)) (encode (values++value::rest) ++ [false])) :
    let pos := h+4+(k : Int)+((encode values).length : Int)
    ∃ (steps : Nat) (e : Config 284), 0<steps ∧ e.state=23 ∧
      e.head=pos+1+((value+(encode rest).length : Nat) : Int) ∧ e.tape (h+2)=true ∧
      Holds e.tape (h+4+(k : Int)) (encode (values++(value+1)::rest)) ∧
      (∀ q, q≠h+2 → (q<pos+1 ∨ pos+1+((value+(encode rest).length : Nat) : Int)<q) →
        e.tape q=clearAt h t q) ∧
      silentSegment machine (cfg (operationAt n true) h t) e steps := by
  dsimp only
  let u := (cfg (operationAt n true) h t).write false
  let separator := h+3+(k : Int)
  let base := h-8
  let pos := separator+1+((encode values).length : Int)
  have hu : ∀ q, q≠h → u q=t q := by intro q hq; simp [u,cfg,Config.write,hq]
  have hu0 : u (h+1)=false := (hu _ (by omega)).trans h0
  have hu1 : u (h+2)=false := (hu _ (by omega)).trans h1
  have hucontrol : ∀ i : Nat, i<k → u (h+3+(i : Int))=true := by
    intro i hi
    exact (hu _ (by omega)).trans (control i hi)
  have husep : u separator=false := (hu _ (by dsimp [separator]; omega)).trans delimiter
  have hsepEq : separator+1=h+4+(k : Int) := by dsimp [separator]; omega
  have hubank : Holds u (separator+1) (encode (values++value::rest) ++ [false]) := by
    apply NativeHalfScannerFrames.holds_transport t u (separator+1) _
      (by rw [hsepEq]; exact bank)
    intro q hq _
    exact (hu q (by dsimp [separator] at hq; omega)).symm
  have hscanbank : Holds u (h+1+3+(k : Int))
      (encode values ++ (block value ++ (encode rest ++ [false]))) := by
    have he : h+1+3+(k : Int)=separator+1 := by dsimp [separator]; omega
    rw [he]
    simpa [encode_append,encode,List.append_assoc] using hubank
  have hscan := entry_scan_all_positions n true h t k values value (encode rest ++ [false])
    marker hlen (by simpa [u] using hu0) (by simpa [u,Int.add_assoc] using hu1)
    (by simpa [u,Int.add_assoc] using hucontrol)
    (by simpa [u,separator,Int.add_assoc] using husep) (by simpa [u] using hscanbank)
  have hu8 : u (base+8)=false := by simp [u,base,cfg,Config.write]
  have hu9 : u (base+9)=false := by
    have he : base+9=h+1 := by dsimp [base]; omega
    simpa only [he] using hu0
  have hu10 : u (base+10)=false := by
    have he : base+10=h+2 := by dsimp [base]; omega
    simpa only [he] using hu1
  have hurun : ∀ q, base+11≤q → q<separator → u q=true := by
    intro q hq hq'
    let i := (q-(h+3)).toNat
    have hi : (i : Int)=q-(h+3) := Int.toNat_of_nonneg (by dsimp [base] at hq; omega)
    have hil : i<k := by dsimp [separator] at hq'; omega
    have he : h+3+(i : Int)=q := by omega
    simpa only [he] using hucontrol i hil
  obtain ⟨e,hstate,hhead,hmark,hresult,hframe,hreturn⟩ :=
    restore_then_increment_full base separator u values value rest (by dsimp [base,separator]; omega)
      hu8 hu9 hu10 hurun husep hubank
  have hscan' : silentSegment machine (cfg (operationAt n true) h t)
      (cfg 262 (pos-2) (clearAt pos u)) (1+(k+(encode values).length+5)) := by
    have he : h+1+3+(k : Int)+((encode values).length : Int)=pos := by
      dsimp [pos,separator]; omega
    simpa only [u,he,Bool.not_true] using hscan
  refine ⟨(1+(k+(encode values).length+5)) +
    ((2*(unaryBankPrefix (separator-(base+12)).toNat values).length+7) +
      (value+2+(encode rest).length)),e,by omega,hstate,?_,?_,?_,?_,?_⟩
  · have he : h+4+(k : Int)+((encode values).length : Int)=pos := by dsimp [pos,separator]; omega
    simpa only [he] using hhead
  · have he : base+10=h+2 := by dsimp [base]; omega
    simpa only [he] using hmark
  · rw [←hsepEq]
    exact hresult
  · have he : base+10=h+2 := by dsimp [base]; omega
    have hp : h+4+(k : Int)+((encode values).length : Int)=pos := by dsimp [pos,separator]; omega
    have hu_eq : u=clearAt h t := rfl
    simpa only [he,hp,hu_eq] using hframe
  · exact segAdd machine _ _ _ _ _ hscan' (by simpa [pos] using hreturn)

#print axioms increment_to23
end Shared.Beeping.NPcoNP.NativeAllBankIncrement
