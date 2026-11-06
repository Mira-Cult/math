import Shared.Beeping.NPcoNP.Native279BankScan

/-! A generic literal scanner assembled from verified right-moving rows. -/
namespace Shared.Beeping.NPcoNP.NativeBankScanGeneric
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfState16Progress
open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.Native279BankScan
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000

/-- Two specified zero rows, a control-run row and a scanner chain traverse
an arbitrary finite bank prefix. The delimiter after the final scanned block
(or the control delimiter for the empty prefix) allows the target touch. -/
theorem scan_to262 {q0 q1 q2 q3 : Fin 284} {m : Nat}
    (r0 : RightRow q0 q1) (r1 : RightRow q1 q2) (r2 : RightRow q2 q3)
    (chain : Chain m q3 42) (h : Int) (t : Int → Bool) (k : Nat)
    (values : List Nat) (value : Nat) (tail : List Bool)
    (hlen : values.length=m) (h0 : t h=false) (h1 : t (h+1)=false)
    (control : ∀ i : Nat, i<k → t (h+2+(i : Int))=true)
    (delimiter : t (h+2+(k : Int))=false)
    (bank : Holds t (h+3+(k : Int)) (encode values ++ (block value ++ tail))) :
    let pos := h+3+(k : Int)+((encode values).length : Int)
    (∀ q, q≠pos → clearAt pos t q=t q) ∧
    silentSegment machine (cfg q0 h t) (cfg 262 (pos-2) (clearAt pos t))
      (k+(encode values).length+5) := by
  dsimp only
  let start := h+3+(k : Int)
  let pos := start+((encode values).length : Int)
  have ha := oneSeg machine _ _ (step_zero r0 h t h0)
  have hb := oneSeg machine _ _ (step_zero r1 (h+1) t h1)
  have hab : silentSegment machine (cfg q0 h t) (cfg q2 (h+2) t) 2 := by
    have hs := segAdd machine _ _ _ 1 1 ha hb
    simpa [Int.add_assoc] using hs
  have hc := scan_run r2 k (h+2) t control delimiter
  have hc' : silentSegment machine (cfg q2 (h+2) t) (cfg q3 start t) (k+1) := by
    have he : h+2+(k : Int)+1=start := by dsimp [start]; omega
    simpa only [he] using hc
  obtain ⟨hrest,hlast,hscan⟩ := scan_bank chain values start t (block value ++ tail) hlen bank
  have htarget : t pos=true := by
    change Holds t pos (block value ++ tail) at hrest
    simp only [block,List.replicate_succ,List.cons_append,Holds] at hrest
    exact hrest.1
  have hzero : t (pos-1)=false := by
    by_cases hm : 0<m
    · have hh := hlast hm
      simpa [pos] using hh
    · have hv : values=[] := by
        cases values with
        | nil => rfl
        | cons x xs => simp at hlen; omega
      subst values
      have he : pos-1=h+2+(k : Int) := by simp [pos,start,encode]; omega
      simpa only [he] using delimiter
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


#print axioms scan_to262
end Shared.Beeping.NPcoNP.NativeBankScanGeneric
