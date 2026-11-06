import Shared.Beeping.NPcoNP.NativeHalfState14Cycle
import Shared.Beeping.NPcoNP.NativeHalfBankFirst
import Shared.Beeping.NPcoNP.NativeHalfScannerFrames

/-! Exact local one-block equations for the literal 14/22 insertion scan.
These are physical tape facts, not an assertion of graph reachability. -/
namespace Shared.Beeping.NPcoNP.NativeIncBlock
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState14Cycle
open Shared.Beeping.NPcoNP.NativeHalfBankFirst
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

/-- Scan n consecutive ones, without changing the tape or emitting events. -/
theorem scan_ones (n : Nat) (h : Int) (t : Int → Bool)
    (ones : ∀ i : Nat, i<n → t (h+(i : Int))=true) :
    silentSegment machine (cfg 14 h t) (cfg 14 (h+(n : Int)) t) n := by
  induction n generalizing h with
  | zero => simp [silentSegment,WordEventSystem.advance,WordEventSystem.wordFrom]
  | succ n ih =>
    have h0 : t h=true := by simpa using ones 0 (by omega)
    have htail : ∀ i : Nat, i<n → t ((h+1)+(i : Int))=true := by
      intro i hi
      have ht := ones (i+1) (by omega)
      have he : (h+1)+(i : Int)=h+((i+1 : Nat):Int) := by push_cast; omega
      rw [he]
      exact ht
    have hs := oneSeg machine _ _ (step14_one h t h0)
    have hr := ih (h+1) htail
    have hall := segAdd machine _ _ _ 1 n hs hr
    have he : (h+1)+(n : Int)=h+((n+1 : Nat):Int) := by push_cast; omega
    simpa [he,Nat.add_comm] using hall

/-- A zero delimiter followed by a one is swapped, then state 14 resumes
on the cell after that pair. The entire infinite tape is explicitly given. -/
theorem shift_next_block (n : Nat) (h : Int) (t : Int → Bool)
    (ones : ∀ i : Nat, i<n → t (h+(i : Int))=true)
    (delimiter : t (h+(n : Int))=false)
    (nextOne : t (h+(n : Int)+1)=true) :
    silentSegment machine (cfg 14 h t)
      (cfg 14 (h+(n : Int)+2)
        (clearAt (h+(n : Int)+1) (setAt (h+(n : Int)) t))) (n+2) := by
  exact segAdd machine _ _ _ n 2 (scan_ones n h t ones)
    (restart (h+(n : Int)) t delimiter nextOne)

/-- A zero delimiter followed by zero ends the scan. -/
theorem shift_last_block (n : Nat) (h : Int) (t : Int → Bool)
    (ones : ∀ i : Nat, i<n → t (h+(i : Int))=true)
    (delimiter : t (h+(n : Int))=false)
    (lastZero : t (h+(n : Int)+1)=false) :
    silentSegment machine (cfg 14 h t)
      (cfg 23 (h+(n : Int)) (setAt (h+(n : Int)) t)) (n+2) := by
  exact segAdd machine _ _ _ n 2 (scan_ones n h t ones)
    (finish (h+(n : Int)) t delimiter lastZero)

/-- The two-cell write in `shift_next_block` leaves every other cell intact. -/
theorem shift_next_frame (p q : Int) (t : Int → Bool)
    (h0 : q≠p) (h1 : q≠p+1) :
    clearAt (p+1) (setAt p t) q=t q := by
  simp [clearAt,setAt,h0,h1]

theorem shift_next_bits (p : Int) (t : Int → Bool) :
    clearAt (p+1) (setAt p t) p=true ∧
      clearAt (p+1) (setAt p t) (p+1)=false := by
  constructor
  · simp [clearAt,setAt,show p≠p+1 by omega]
  · simp [clearAt]

/-- An encoded selected block followed by another nonempty unary block makes
one exact insertion iteration. -/
theorem encoded_two_blocks (v w : Nat) (rest : List Nat) (h : Int) (t : Int → Bool)
    (bank : Holds t h (encode (v::w::rest))) :
    silentSegment machine (cfg 14 h t)
      (cfg 14 (h+((v+3 : Nat) : Int))
        (clearAt (h+((v+2 : Nat) : Int)) (setAt (h+((v+1 : Nat) : Int)) t))) (v+3) := by
  have first := first_block_cells t h v (w::rest) bank
  have tail := first_block_tail t h v (w::rest) bank
  have hone : t (h+((v+2 : Nat) : Int))=true := by
    have hh : t (h+((v+2 : Nat) : Int))=true ∧
        Holds t (h+((v+2 : Nat) : Int)+1) (List.replicate w true ++ false :: encode rest) := by
      simpa [encode,block,List.replicate_succ,List.append_assoc,Holds] using tail
    exact hh.1
  have hones : ∀ i : Nat, i<v+1 → t (h+(i : Int))=true := by
    intro i hi
    exact first.1 i (by omega)
  have hs := shift_next_block (v+1) h t hones first.2 (by
    have he : h+((v+1 : Nat) : Int)+1=h+((v+2 : Nat) : Int) := by push_cast; omega
    rw [he]
    exact hone)
  have hhead : h+((v+1 : Nat) : Int)+2=h+((v+3 : Nat) : Int) := by push_cast; omega
  have hsecond : h+((v+1 : Nat) : Int)+1=h+((v+2 : Nat) : Int) := by push_cast; omega
  simpa only [hhead,hsecond,show v+1+2=v+3 by omega] using hs

theorem holds_ones_delimiter (n : Nat) (h : Int) (t : Int → Bool)
    (ones : ∀ i : Nat, i<n → t (h+(i : Int))=true)
    (last : t (h+(n : Int))=false) :
    Holds t h (List.replicate n true ++ [false]) := by
  induction n generalizing h with
  | zero => simpa [Holds] using last
  | succ n ih =>
    simp only [List.replicate_succ,List.cons_append,Holds]
    refine ⟨by simpa using ones 0 (by omega),?_⟩
    apply ih (h+1)
    · intro i hi
      have hh := ones (i+1) (by omega)
      have he : h+1+(i : Int)=h+((i+1 : Nat):Int) := by push_cast; omega
      rw [he]
      exact hh
    · have he : h+1+(n : Int)=h+((n+1 : Nat):Int) := by push_cast; omega
      rw [he]
      exact last

/-- The physical iteration changes the first unary value from v to v+1 and
preserves the unconsumed portion of the following block and the remaining
encoded bank. This is a local two-block fact, not a full runtime invariant. -/
theorem encoded_two_blocks_contents (v w : Nat) (rest : List Nat) (h : Int) (t : Int → Bool)
    (bank : Holds t h (encode (v::w::rest))) :
    let u := clearAt (h+((v+2 : Nat) : Int)) (setAt (h+((v+1 : Nat) : Int)) t)
    Holds u h (block (v+1)) ∧
      Holds u (h+((v+3 : Nat) : Int)) (List.replicate w true ++ false :: encode rest) ∧
      silentSegment machine (cfg 14 h t) (cfg 14 (h+((v+3 : Nat) : Int)) u) (v+3) := by
  dsimp only
  let p : Int := h+((v+1 : Nat) : Int)
  let u := clearAt (p+1) (setAt p t)
  have hp2 : p+1=h+((v+2 : Nat):Int) := by dsimp [p]; push_cast; omega
  have hp3 : p+2=h+((v+3 : Nat):Int) := by dsimp [p]; push_cast; omega
  have first := first_block_cells t h v (w::rest) bank
  have tail := first_block_tail t h v (w::rest) bank
  have ht : Holds t (p+2) (List.replicate w true ++ false :: encode rest) := by
    have hh : t (h+((v+2 : Nat):Int))=true ∧
        Holds t (h+((v+2 : Nat):Int)+1) (List.replicate w true ++ false :: encode rest) := by
      simpa [encode,block,List.replicate_succ,List.append_assoc,Holds] using tail
    have he : h+((v+2 : Nat):Int)+1=p+2 := by omega
    rw [he] at hh
    exact hh.2
  have hones : ∀ i : Nat, i<v+2 → u (h+(i : Int))=true := by
    intro i hi
    by_cases hsmall : i<v+1
    · have hne0 : h+(i : Int)≠p := by dsimp [p]; omega
      have hne1 : h+(i : Int)≠p+1 := by dsimp [p]; omega
      have hf := shift_next_frame p (h+(i : Int)) t hne0 hne1
      change clearAt (p+1) (setAt p t) (h+(i : Int))=t (h+(i : Int)) at hf
      change clearAt (p+1) (setAt p t) (h+(i : Int))=true
      rw [hf]
      exact first.1 i (by omega)
    · have heq : h+(i : Int)=p := by dsimp [p]; omega
      rw [heq]
      exact (shift_next_bits p t).1
  have hlast : u (h+((v+2 : Nat):Int))=false := by
    rw [← hp2]
    exact (shift_next_bits p t).2
  have hprefix : Holds u h (block (v+1)) := by
    have hh := holds_ones_delimiter (v+2) h u hones hlast
    simpa [block,Nat.add_assoc] using hh
  have htail : Holds u (p+2) (List.replicate w true ++ false :: encode rest) := by
    apply holds_transport t u (p+2) _ ht
    intro q hq _
    symm
    exact shift_next_frame p q t (by omega) (by omega)
  have hs := encoded_two_blocks v w rest h t bank
  have heq : clearAt (h+((v+2 : Nat):Int)) (setAt (h+((v+1 : Nat):Int)) t)=u := by
    change clearAt (h+((v+2 : Nat):Int)) (setAt p t) = clearAt (p+1) (setAt p t)
    rw [hp2]
  rw [heq]
  rw [heq] at hs
  exact ⟨hprefix,by rw [←hp3]; exact htail,hs⟩

#print axioms encoded_two_blocks_contents
#print axioms encoded_two_blocks
#print axioms shift_next_block
#print axioms shift_last_block
#print axioms shift_next_frame
end Shared.Beeping.NPcoNP.NativeIncBlock
