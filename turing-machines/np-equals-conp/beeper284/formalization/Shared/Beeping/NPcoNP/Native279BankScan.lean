import Shared.Beeping.NPcoNP.NativeFirstZeroNext
import Shared.Beeping.NPcoNP.NativeIncBank

/-! Exact rightward unary-block scans for literal state 279 and its successor
states. This proves physical tape behavior only, without assuming that a
physical block index is a particular graph-register index. -/
namespace Shared.Beeping.NPcoNP.Native279BankScan
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfRows
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000

inductive RightRow : Fin 284 → Fin 284 → Prop where
  | r274 : RightRow 274 273 | r273 : RightRow 273 272 | r272 : RightRow 272 282
  | r282 : RightRow 282 281 | r281 : RightRow 281 280
  | r280 : RightRow 280 279
  | r279 : RightRow 279 278 | r278 : RightRow 278 277
  | r277 : RightRow 277 276 | r276 : RightRow 276 275
  | r275 : RightRow 275 271 | r271 : RightRow 271 270
  | r270 : RightRow 270 9 | r9 : RightRow 9 42

theorem row_zero {q r : Fin 284} (hr : RightRow q r) :
    machine.table.row q false=⟨false,.right,r,false⟩ := by cases hr <;> decide

theorem row_one {q r : Fin 284} (hr : RightRow q r) :
    machine.table.row q true=⟨true,.right,q,false⟩ := by cases hr <;> decide

theorem step_zero {q r : Fin 284} (hr : RightRow q r) (h : Int) (t : Int → Bool)
    (ht : t h=false) : machine.step (cfg q h t)=(cfg r (h+1) t,false) := by
  have hw : (⟨q,h,t⟩ : Config 284).write false=t := by rw [←ht]; exact write_current _
  simp [cfg,Machine.step,ht,row_zero hr,Move.apply,hw]

theorem step_one {q r : Fin 284} (hr : RightRow q r) (h : Int) (t : Int → Bool)
    (ht : t h=true) : machine.step (cfg q h t)=(cfg q (h+1) t,false) := by
  have hw : (⟨q,h,t⟩ : Config 284).write true=t := by rw [←ht]; exact write_current _
  simp [cfg,Machine.step,ht,row_one hr,Move.apply,hw]

/-- A specified one-run and its zero delimiter are scanned in exactly `k+1`
silent transitions, leaving the whole tape unchanged. -/
theorem scan_run {q r : Fin 284} (hr : RightRow q r) (k : Nat) (h : Int)
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
theorem scan_block {q r : Fin 284} (hr : RightRow q r) (n : Nat) (h : Int)
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

inductive Chain : Nat → Fin 284 → Fin 284 → Prop where
  | refl (q) : Chain 0 q q
  | cons {m q r s} : RightRow q r → Chain m r s → Chain (m+1) q s

theorem chain_five : Chain 5 276 42 := by
  exact .cons .r276 (.cons .r275 (.cons .r271 (.cons .r270 (.cons .r9 (.refl 42)))))

/-- A chain of scanners traverses exactly the given encoded bank values.
For a nonempty chain it also records the final delimiter. -/
theorem scan_bank {m : Nat} {q r : Fin 284} (hc : Chain m q r)
    (xs : List Nat) (h : Int) (t : Int → Bool) (rest : List Bool)
    (hl : xs.length=m) (hm : Holds t h (encode xs ++ rest)) :
    Holds t (h+((encode xs).length : Int)) rest ∧
      (0<m → t (h+((encode xs).length : Int)-1)=false) ∧
      silentSegment machine (cfg q h t) (cfg r (h+((encode xs).length : Int)) t)
        (encode xs).length := by
  induction hc generalizing xs h with
  | refl q =>
    cases xs with
    | nil =>
      simp only [encode,List.nil_append,List.length_nil,Nat.cast_zero,add_zero] at hm ⊢
      refine ⟨hm,by omega,?_⟩
      simp [silentSegment,W,WordEventSystem.advance,WordEventSystem.wordFrom]
    | cons x xs => simp at hl
  | @cons m q r s hr hc ih =>
    cases xs with
    | nil => simp at hl
    | cons x xs =>
      have hl' : xs.length=m := by simp at hl; omega
      have hm' : Holds t h (block x ++ (encode xs ++ rest)) := by
        simpa [encode,List.append_assoc] using hm
      obtain ⟨htail,hzero,hfirst⟩ := scan_block hr x h t (encode xs ++ rest) hm'
      obtain ⟨hend,hlast,hsecond⟩ := ih xs (h+((x+2 : Nat) : Int)) hl' htail
      have hseg := segAdd machine _ _ _ (x+2) (encode xs).length hfirst hsecond
      have he : h+((x+2 : Nat) : Int)+((encode xs).length : Int)=
          h+(((x+2+(encode xs).length : Nat)) : Int) := by push_cast; omega
      rw [he] at hend hlast hseg
      have hlen : (encode (x::xs)).length=x+2+(encode xs).length := by simp [encode]
      refine ⟨?_,?_,?_⟩
      · simpa only [hlen] using hend
      · intro _
        by_cases hpos : 0<m
        · simpa only [hlen] using hlast hpos
        · have hnil : xs=[] := by cases xs with | nil => rfl | cons a as => simp at hl'; omega
          subst xs
          have hh : h+((x+2 : Nat) : Int)-1=h+((x+1 : Nat) : Int) := by push_cast; omega
          have he : (encode [x]).length=x+2 := by simp [encode]
          rw [he,hh]
          exact hzero
      · simpa only [hlen] using hseg

theorem row42_one : machine.table.row 42 true=⟨false,.left,283,false⟩ := by decide
theorem row283_zero : machine.table.row 283 false=⟨false,.left,262,false⟩ := by decide

theorem step42_one (h : Int) (t : Int → Bool) (ht : t h=true) :
    machine.step (cfg 42 h t)=(cfg 283 (h-1) (clearAt h t),false) := by
  have hw : (⟨42,h,t⟩ : Config 284).write false=clearAt h t := rfl
  simp [cfg,Machine.step,ht,row42_one,Move.apply,hw]

theorem step283_zero (h : Int) (t : Int → Bool) (ht : t h=false) :
    machine.step (cfg 283 h t)=(cfg 262 (h-1) t,false) := by
  have hw : (⟨283,h,t⟩ : Config 284).write false=t := by rw [←ht]; exact write_current _
  simp [cfg,Machine.step,ht,row283_zero,Move.apply,hw]

/-- Starting at state 279 on two zeros, scan a finite control run, then five
unary bank values; clear the first cell of the following value and return to
state 262. The entire output tape and exact silent duration are specified. -/
theorem scan279_to262 (h : Int) (t : Int → Bool) (k : Nat)
    (values : List Nat) (value : Nat) (tail : List Bool)
    (hlen : values.length=5) (h0 : t h=false) (h1 : t (h+1)=false)
    (control : ∀ i : Nat, i<k → t (h+2+(i : Int))=true)
    (delimiter : t (h+2+(k : Int))=false)
    (bank : Holds t (h+3+(k : Int)) (encode values ++ (block value ++ tail))) :
    let pos := h+3+(k : Int)+((encode values).length : Int)
    (∀ q, q≠pos → clearAt pos t q=t q) ∧
    silentSegment machine (cfg 279 h t) (cfg 262 (pos-2) (clearAt pos t))
      (k+(encode values).length+5) := by
  dsimp only
  let start := h+3+(k : Int)
  let pos := start+((encode values).length : Int)
  have ha := oneSeg machine _ _ (step_zero RightRow.r279 h t h0)
  have hb := oneSeg machine _ _ (step_zero RightRow.r278 (h+1) t h1)
  have hab : silentSegment machine (cfg 279 h t) (cfg 277 (h+2) t) 2 := by
    have hs := segAdd machine _ _ _ 1 1 ha hb
    simpa [Int.add_assoc] using hs
  have hc := scan_run RightRow.r277 k (h+2) t control delimiter
  have hc' : silentSegment machine (cfg 277 (h+2) t) (cfg 276 start t) (k+1) := by
    have he : h+2+(k : Int)+1=start := by dsimp [start]; omega
    simpa only [he] using hc
  obtain ⟨hrest,hlast,hscan⟩ := scan_bank chain_five values start t (block value ++ tail) hlen bank
  have htarget : t pos=true := by
    change Holds t pos (block value ++ tail) at hrest
    simp only [block,List.replicate_succ,List.cons_append,Holds] at hrest
    exact hrest.1
  have hzero : t (pos-1)=false := by
    have hh := hlast (by decide)
    simpa [pos] using hh
  let u := clearAt pos t
  have hz' : u (pos-1)=false := by simp [u,clearAt,show pos-1≠pos by omega,hzero]
  have hs1 := oneSeg machine _ _ (step42_one pos t htarget)
  have hs2 := oneSeg machine _ _ (step283_zero (pos-1) u hz')
  have hlast2 : silentSegment machine (cfg 42 pos t) (cfg 262 (pos-2) u) 2 := by
    have hs := segAdd machine _ _ _ 1 1 hs1 hs2
    have he : pos-1-1=pos-2 := by omega
    simpa [u,he] using hs
  have hpre := segAdd machine _ _ _ 2 (k+1) hab hc'
  have hmiddle := segAdd machine _ _ _ (2+(k+1)) (encode values).length hpre hscan
  have hall := segAdd machine _ _ _ (2+(k+1)+(encode values).length) 2 hmiddle hlast2
  constructor
  · intro q hq
    simp [clearAt,hq]
  · have hc : 2+(k+1)+(encode values).length+2=k+(encode values).length+5 := by omega
    rw [hc] at hall
    simpa [pos,start,u] using hall

#print axioms scan_run
#print axioms scan_block
#print axioms scan_bank
#print axioms scan279_to262
end Shared.Beeping.NPcoNP.Native279BankScan
