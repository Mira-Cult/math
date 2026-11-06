import Shared.Beeping.NPcoNP.NativeAllBankZeroPrepare
import Shared.Beeping.NPcoNP.NativeSelectorPrefixReturn
import Shared.Beeping.NPcoNP.NativeSelectorThirteen
import Shared.Beeping.NPcoNP.NativeIncBank
import Shared.Beeping.NPcoNP.NativeHalfTapeScan

/-! A conditional zero-entry preparation returns to the original parser when
its prepared selector prefix has at most eleven zero bits. -/
namespace Shared.Beeping.NPcoNP.NativeAllBankPrepareReturn
open PASoundness Shared.Beeping Shared.Beeping.Machines
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState10Exact
open Shared.Beeping.NPcoNP.NativeAllBankScan
open Shared.Beeping.NPcoNP.NativeAllBankZeroPrepare
open Shared.Beeping.NPcoNP.NativeSelectorPrefixReturn
open Shared.Beeping.NPcoNP.NativeSelectorThirteen
open Shared.Beeping.NPcoNP.NativeIncBank
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 30000000

/-- If the scanned run is empty, the selector starts at the end of the
original path, so the full eleven-zero path bound suffices. -/
theorem zero_prepare_empty_returns (n : Fin 12) (inc : Bool) (origin x : Int)
    (t : Int → Bool) (path : List Bool)
    (hentry : x=origin+((path.length : Nat) : Int)) (hlen : 0<path.length)
    (count : path.count false≤11) (word : Holds t origin path)
    (left : ∀ q, q<origin → t q=false) (first : t origin=true)
    (h0 : t x=false) (h1 : t (x+1)=false) (h2 : t (x+2)=false)
    (marker : t (x+3)=true) :
    let out := setAt x t
    ∃ steps : Nat, 0<steps ∧ Holds out origin path ∧ out x=true ∧
      out (x+1)=false ∧ out (x+2)=false ∧ out (x+3)=true ∧
      (∀ q, q≠x → out q=t q) ∧
      silentSegment machine (cfg (operationAt n inc) x t) (cfg 93 (origin+1) out) steps := by
  dsimp only
  let out := setAt x t
  have hframe : ∀ q, q≠x → out q=t q := by intro q hq; simp [out,setAt,hq]
  have hword : Holds out origin path := by
    apply holds_transport t out origin path word
    intro q hq hq'
    exact (hframe q (by omega)).symm
  have houtleft : ∀ q, q<origin → out q=false := by
    intro q hq
    rw [hframe q (by omega)]
    exact left q hq
  have hfirst : out origin=true := by
    rw [hframe origin (by omega)]
    exact first
  have hprepare := ordinary_zero_prepare n inc x t 0 h0 h1 h2 (by intro i hi; omega) (by simpa using marker)
  have hprepare' : silentSegment machine (cfg (operationAt n inc) x t) (cfg 83 (x-1) out) 7 := by
    simpa [out,fill_empty] using hprepare
  obtain ⟨b,hb,hselector⟩ := selector_returns_to_origin out origin path count hword houtleft hfirst
  have hhead : origin+((path.length : Nat) : Int)-1=x-1 := by omega
  rw [hhead] at hselector
  refine ⟨7+b,by omega,hword,?_,?_,?_,?_,hframe,segAdd machine _ _ _ 7 b hprepare' hselector⟩
  · simp [out,setAt]
  · simpa [out,setAt,show x+1≠x by omega] using h1
  · simpa [out,setAt,show x+2≠x by omega] using h2
  · simpa [out,setAt,show x+3≠x by omega] using marker

/-- With a nonempty scanned run and at most eleven zeros in the original path,
zero-entry preparation and the selector silently return to the same parser.
The extra two zeros are accounted for in the selector's thirteen-zero bound. -/
theorem zero_prepare_returns_11 (n : Fin 12) (inc : Bool) (origin x : Int)
    (t : Int → Bool) (path : List Bool) (k : Nat)
    (hentry : x=origin+((path.length : Nat) : Int)) (hlen : 0<path.length)
    (count : path.count false≤11) (word : Holds t origin path)
    (left : ∀ q, q<origin → t q=false) (first : t origin=true)
    (hk : 0<k) (h0 : t x=false) (h1 : t (x+1)=false) (h2 : t (x+2)=false)
    (zeros : ∀ i : Nat, i<k → t (x+3+(i : Int))=false)
    (marker : t (x+3+(k : Int))=true) :
    let out := fillRange (setAt x t) (x+3) (x+3+(k : Int))
    ∃ steps : Nat, 0<steps ∧ Holds out origin path ∧ out x=true ∧
      out (x+1)=false ∧ out (x+2)=false ∧
      (∀ q, x+3≤q → q≤x+3+(k : Int) → out q=true) ∧
      (∀ q, q<x ∨ x+3+(k : Int)≤q → out q=t q) ∧
      silentSegment machine (cfg (operationAt n inc) x t) (cfg 93 (origin+1) out) steps := by
  dsimp only
  let out := fillRange (setAt x t) (x+3) (x+3+(k : Int))
  have hframe : ∀ q, q<x ∨ x+3+(k : Int)≤q → out q=t q := by
    intro q hq
    have hn : ¬ (x+3≤q ∧ q<x+3+(k : Int)) := by omega
    have he : q≠x := by omega
    simp [out,fillRange,setAt,hn,he]
  have hword : Holds out origin path := by
    apply holds_transport t out origin path word
    intro q hq hq'
    exact (hframe q (Or.inl (by omega))).symm
  have houtleft : ∀ q, q<origin → out q=false := by
    intro q hq
    rw [hframe q (Or.inl (by omega))]
    exact left q hq
  have hfirst : out origin=true := by
    rw [hframe origin (Or.inl (by omega))]
    exact first
  have hx : out x=true := by simp [out,fillRange,setAt]
  have hx1 : out (x+1)=false := by
    simpa [out,fillRange,setAt,show x+1≠x by omega] using h1
  have hx2 : out (x+2)=false := by
    simpa [out,fillRange,setAt,show x+2≠x by omega] using h2
  have hcontrol : ∀ q, x+3≤q → q≤x+3+(k : Int) → out q=true := by
    intro q hq hq'
    by_cases he : q=x+3+(k : Int)
    · rw [hframe q (Or.inr (by omega)),he]
      exact marker
    · simp [out,fillRange,show x+3≤q ∧ q<x+3+(k : Int) by omega]
  let xs := path ++ [true,false,false] ++ List.replicate (k-1) true
  have htail : Holds out x ([true,false,false] ++ List.replicate (k-1) true) := by
    simp only [List.cons_append,List.nil_append,Holds]
    refine ⟨hx,?_,?_,?_⟩
    · simpa only [show x+1=x+1 by rfl] using hx1
    · simpa only [show x+1+1=x+2 by omega] using hx2
    · have hr : Holds out (x+3) (List.replicate (k-1) true) := by
        apply holds_of_get
        intro i hi
        have htrue := hcontrol (x+3+(i : Int)) (by omega) (by simp at hi; omega)
        simpa using htrue
      simpa only [show x+1+1+1=x+3 by omega] using hr
  have hxsword : Holds out origin xs := by
    have hh := holds_append_intro out origin path
      ([true,false,false] ++ List.replicate (k-1) true) hword (by simpa only [hentry] using htail)
    simpa only [xs,List.append_assoc] using hh
  have hxscount : xs.count false≤13 := by
    simp [xs,List.count_append,List.count_replicate]
    omega
  have hxslen : xs.length=path.length+k+2 := by
    simp only [xs,List.length_append,List.length_cons,List.length_nil,List.length_replicate]
    omega
  obtain ⟨b,hb,hselector⟩ := selector_returns_to_origin_13 out origin xs hxscount hxsword houtleft hfirst
  have hhead : origin+((xs.length : Nat) : Int)-1=x+3+(k : Int)-2 := by rw [hxslen]; omega
  rw [hhead] at hselector
  have hprepare := ordinary_zero_prepare n inc x t k h0 h1 h2 zeros marker
  have hprepare' : silentSegment machine (cfg (operationAt n inc) x t)
      (cfg 83 (x+3+(k : Int)-2) out) (k+5) := by
    simpa [out,show k≠0 by omega] using hprepare
  refine ⟨k+5+b,by omega,hword,hx,hx1,hx2,hcontrol,hframe,?_⟩
  exact segAdd machine _ _ _ _ _ hprepare' hselector

/-- Original nine-zero interface. -/
theorem zero_prepare_returns (n : Fin 12) (inc : Bool) (origin x : Int)
    (t : Int → Bool) (path : List Bool) (k : Nat)
    (hentry : x=origin+((path.length : Nat) : Int)) (hlen : 0<path.length)
    (count : path.count false≤9) (word : Holds t origin path)
    (left : ∀ q, q<origin → t q=false) (first : t origin=true)
    (hk : 0<k) (h0 : t x=false) (h1 : t (x+1)=false) (h2 : t (x+2)=false)
    (zeros : ∀ i : Nat, i<k → t (x+3+(i : Int))=false)
    (marker : t (x+3+(k : Int))=true) :
    let out := fillRange (setAt x t) (x+3) (x+3+(k : Int))
    ∃ steps : Nat, 0<steps ∧ Holds out origin path ∧ out x=true ∧
      out (x+1)=false ∧ out (x+2)=false ∧
      (∀ q, x+3≤q → q≤x+3+(k : Int) → out q=true) ∧
      (∀ q, q<x ∨ x+3+(k : Int)≤q → out q=t q) ∧
      silentSegment machine (cfg (operationAt n inc) x t) (cfg 93 (origin+1) out) steps := by
  exact zero_prepare_returns_11 n inc origin x t path k hentry hlen (by omega) word left first hk h0 h1 h2 zeros marker

/-- The empty and nonempty preparations both return under the established
eleven-zero path bound and expose the same prepared control window. -/
theorem zero_prepare_returns_all (n : Fin 12) (inc : Bool) (origin x : Int)
    (t : Int → Bool) (path : List Bool) (k : Nat)
    (hentry : x=origin+((path.length : Nat) : Int)) (hlen : 0<path.length)
    (count : path.count false≤11) (word : Holds t origin path)
    (left : ∀ q, q<origin → t q=false) (first : t origin=true)
    (h0 : t x=false) (h1 : t (x+1)=false) (h2 : t (x+2)=false)
    (zeros : ∀ i : Nat, i<k → t (x+3+(i : Int))=false)
    (marker : t (x+3+(k : Int))=true) :
    let out := fillRange (setAt x t) (x+3) (x+3+(k : Int))
    ∃ steps : Nat, 0<steps ∧ Holds out origin path ∧ out x=true ∧
      out (x+1)=false ∧ out (x+2)=false ∧
      (∀ q, x+3≤q → q≤x+3+(k : Int) → out q=true) ∧
      (∀ q, q<x ∨ x+3+(k : Int)≤q → out q=t q) ∧
      silentSegment machine (cfg (operationAt n inc) x t) (cfg 93 (origin+1) out) steps := by
  cases k with
  | zero =>
    have hm : t (x+3)=true := by simpa using marker
    obtain ⟨steps,hs,hw,hx,hx1,hx2,hx3,hframe,hseg⟩ :=
      zero_prepare_empty_returns n inc origin x t path hentry hlen count word left first h0 h1 h2 hm
    refine ⟨steps,hs,?_,?_,?_,?_,?_,?_,?_⟩
    · simpa [fill_empty] using hw
    · simpa [fill_empty] using hx
    · simpa [fill_empty] using hx1
    · simpa [fill_empty] using hx2
    · intro q hq hq'
      have he : q=x+3 := by simp at hq'; omega
      simpa [fill_empty,he] using hx3
    · intro q hq
      have hne : q≠x := by simp at hq; omega
      simpa [fill_empty] using hframe q hne
    · simpa [fill_empty] using hseg
  | succ k =>
    exact zero_prepare_returns_11 n inc origin x t path (k+1) hentry hlen count word left first
      (by omega) h0 h1 h2 zeros marker

#print axioms zero_prepare_empty_returns
#print axioms zero_prepare_returns_11
#print axioms zero_prepare_returns
#print axioms zero_prepare_returns_all
end Shared.Beeping.NPcoNP.NativeAllBankPrepareReturn
