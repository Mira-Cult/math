import Shared.Beeping.NPcoNP.Native54Redispatch
import Shared.Beeping.NPcoNP.NativeBankScanGeneric

/-! The state-273 scanner traverses the first ten encoded bank blocks and
physically touches the next block. The source-register correspondence is a
separate obligation. -/
namespace Shared.Beeping.NPcoNP.Native273BankScan
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfRows
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.UnaryBank
open Shared.Beeping.NPcoNP.NativeBankScanGeneric
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

inductive PrefixRow : Fin 284 → Fin 284 → Prop where
  | r274 : PrefixRow 274 273 | r273 : PrefixRow 273 272 | r272 : PrefixRow 272 282
  | r282 : PrefixRow 282 281 | r281 : PrefixRow 281 280
  | r280 : PrefixRow 280 279 | r279 : PrefixRow 279 278
  | r278 : PrefixRow 278 277
  | r277 : PrefixRow 277 276 | r276 : PrefixRow 276 275 | r275 : PrefixRow 275 271
  | r271 : PrefixRow 271 270

theorem row_zero {q r : Fin 284} (hr : PrefixRow q r) :
    machine.table.row q false=⟨false,.right,r,false⟩ := by cases hr <;> decide

theorem row_one {q r : Fin 284} (hr : PrefixRow q r) :
    machine.table.row q true=⟨true,.right,q,false⟩ := by cases hr <;> decide

theorem step_zero {q r : Fin 284} (hr : PrefixRow q r) (h : Int) (t : Int → Bool)
    (ht : t h=false) : machine.step (cfg q h t)=(cfg r (h+1) t,false) := by
  have hw : (⟨q,h,t⟩ : Config 284).write false=t := by rw [←ht]; exact write_current _
  simp [cfg,Machine.step,ht,row_zero hr,Move.apply,hw]

theorem step_one {q r : Fin 284} (hr : PrefixRow q r) (h : Int) (t : Int → Bool)
    (ht : t h=true) : machine.step (cfg q h t)=(cfg q (h+1) t,false) := by
  have hw : (⟨q,h,t⟩ : Config 284).write true=t := by rw [←ht]; exact write_current _
  simp [cfg,Machine.step,ht,row_one hr,Move.apply,hw]

/-- A specified one-run and its zero delimiter are scanned in exactly `k+1`
silent transitions, leaving the whole tape unchanged. -/
theorem scan_run {q r : Fin 284} (hr : PrefixRow q r) (k : Nat) (h : Int)
    (t : Int → Bool) (ones : ∀ i : Nat, i<k → t (h+(i : Int))=true)
    (zero : t (h+(k : Int))=false) :
    silentSegment machine (cfg q h t) (cfg r (h+(k : Int)+1) t) (k+1) := by
  induction k generalizing h with
  | zero => simpa using oneSeg machine _ _ (step_zero hr h t (by simpa using zero))
  | succ k ih =>
    have ho : t h=true := by simpa using ones 0 (by omega)
    have hon : ∀ i : Nat, i<k → t ((h+1)+(i : Int))=true := by
      intro i hi
      have he : (h+1)+(i : Int)=h+((i+1 : Nat) : Int) := by push_cast; omega
      rw [he]
      exact ones (i+1) (by omega)
    have hz : t ((h+1)+(k : Int))=false := by
      have he : (h+1)+(k : Int)=h+((Nat.succ k : Nat) : Int) := by push_cast; omega
      simpa only [he] using zero
    have hs := segAdd machine _ _ _ 1 (k+1)
      (oneSeg machine _ _ (step_one hr h t ho)) (ih (h+1) hon hz)
    have he : (h+1)+(k : Int)+1=h+((Nat.succ k : Nat) : Int)+1 := by push_cast; omega
    simpa [he,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hs

/-- Scan one complete encoded unary value and expose the remaining word and
its final zero delimiter. -/
theorem scan_block {q r : Fin 284} (hr : PrefixRow q r) (n : Nat) (h : Int)
    (t : Int → Bool) (rest : List Bool) (hm : Holds t h (block n ++ rest)) :
    Holds t (h+((n+2 : Nat) : Int)) rest ∧
      t (h+((n+1 : Nat) : Int))=false ∧
      silentSegment machine (cfg q h t) (cfg r (h+((n+2 : Nat) : Int)) t) (n+2) := by
  have hm' : Holds t h (List.replicate (n+1) true ++ false :: rest) := by
    simpa [block,List.append_assoc] using hm
  have hh := split_ones (n+1) h t (false :: rest) hm'
  have hz := hh.2.1
  have hs' := scan_run hr (n+1) h t hh.1 hz
  have ht := hh.2.2
  have he : h+((n+1 : Nat) : Int)+1=h+((n+2 : Nat) : Int) := by push_cast; omega
  refine ⟨?_,hz,?_⟩
  · simpa only [he] using ht
  · simpa only [he,show n+1+1=n+2 by omega] using hs'


/-- Two zero steps and the control run lead to ten complete bank
blocks. The next block's first one is cleared and the machine reaches state
262. The list values, target value and tail are arbitrary. -/
theorem scan_to262 (h : Int) (t : Int → Bool) (k a b : Nat)
    (xs : List Nat) (value : Nat) (tail : List Bool)
    (hlen : xs.length=8) (h0 : t h=false) (h1 : t (h+1)=false)
    (control : ∀ i : Nat, i<k → t (h+2+(i : Int))=true)
    (delimiter : t (h+2+(k : Int))=false)
    (bank : Holds t (h+3+(k : Int)) (encode (a::b::xs) ++ (block value ++ tail))) :
    let pos := h+3+(k : Int)+((encode (a::b::xs)).length : Int)
    (∀ q, q≠pos → clearAt pos t q=t q) ∧
    silentSegment machine (cfg 273 h t) (cfg 262 (pos-2) (clearAt pos t))
      (k+(encode (a::b::xs)).length+5) := by
  dsimp only
  let start := h+3+(k : Int)
  let pos := start+((encode (a::b::xs)).length : Int)
  have ha := oneSeg machine _ _ (step_zero PrefixRow.r273 h t h0)
  have hb := oneSeg machine _ _ (step_zero PrefixRow.r272 (h+1) t h1)
  have hab : silentSegment machine (cfg 273 h t) (cfg 282 (h+2) t) 2 := by
    have hs := segAdd machine _ _ _ 1 1 ha hb
    simpa [Int.add_assoc] using hs
  have hc := scan_run PrefixRow.r282 k (h+2) t control delimiter
  have hc' : silentSegment machine (cfg 282 (h+2) t) (cfg 281 start t) (k+1) := by
    have he : h+2+(k : Int)+1=start := by dsimp [start]; omega
    simpa only [he] using hc
  have hbank : Holds t start (block a ++ (block b ++ (encode xs ++ (block value ++ tail)))) := by
    simpa [start,encode,List.append_assoc] using bank
  obtain ⟨hrest1,_hz1,hs1⟩ := scan_block PrefixRow.r281 a start t
    (block b ++ (encode xs ++ (block value ++ tail))) hbank
  obtain ⟨hrest2,_hz2,hs2⟩ := scan_block PrefixRow.r280 b (start+((a+2 : Nat) : Int)) t
    (encode xs ++ (block value ++ tail)) hrest1
  have chain : Native279BankScan.Chain 8 279 42 :=
    .cons .r279 (.cons .r278 (.cons .r277 (.cons .r276 (.cons .r275
      (.cons .r271 (.cons .r270 (.cons .r9 (.refl 42))))))))
  obtain ⟨hrest,hlast,hscan⟩ := Native279BankScan.scan_bank chain xs
    (start+((a+2 : Nat) : Int)+((b+2 : Nat) : Int)) t (block value ++ tail) hlen hrest2
  have hlenall : (encode (a::b::xs)).length=(a+2)+(b+2)+(encode xs).length := by
    simp [encode]; omega
  have hend : start+((a+2 : Nat) : Int)+((b+2 : Nat) : Int)+((encode xs).length : Int)=pos := by
    dsimp [pos]; rw [hlenall]; push_cast; omega
  have htarget : t pos=true := by
    rw [hend] at hrest
    simp only [block,List.replicate_succ,List.cons_append,Holds] at hrest
    exact hrest.1
  have hzero : t (pos-1)=false := by
    have hh := hlast (by decide)
    rw [hend] at hh
    exact hh
  let u := clearAt pos t
  have hz' : u (pos-1)=false := by simp [u,clearAt,show pos-1≠pos by omega,hzero]
  have hs3 := oneSeg machine _ _ (Native279BankScan.step42_one pos t htarget)
  have hs4 := oneSeg machine _ _ (Native279BankScan.step283_zero (pos-1) u hz')
  have hlast2 : silentSegment machine (cfg 42 pos t) (cfg 262 (pos-2) u) 2 := by
    have hs := segAdd machine _ _ _ 1 1 hs3 hs4
    have he : pos-1-1=pos-2 := by omega
    simpa [u,he] using hs
  have hblocks := segAdd machine _ _ _ (a+2) (b+2) hs1 hs2
  have hblocks' := segAdd machine _ _ _ ((a+2)+(b+2)) (encode xs).length hblocks hscan
  have hblocks'' : silentSegment machine (cfg 281 start t) (cfg 42 pos t)
      (encode (a::b::xs)).length := by simpa only [hend,hlenall] using hblocks'
  have hpre := segAdd machine _ _ _ 2 (k+1) hab hc'
  have hmiddle := segAdd machine _ _ _ (2+(k+1)) (encode (a::b::xs)).length hpre hblocks''
  have hall := segAdd machine _ _ _ (2+(k+1)+(encode (a::b::xs)).length) 2 hmiddle hlast2
  constructor
  · intro q hq
    simp [clearAt,hq]
  · have hc : 2+(k+1)+(encode (a::b::xs)).length+2=k+(encode (a::b::xs)).length+5 := by omega
    rw [hc] at hall
    simpa [pos,start,u] using hall

#print axioms scan_to262
end Shared.Beeping.NPcoNP.Native273BankScan
