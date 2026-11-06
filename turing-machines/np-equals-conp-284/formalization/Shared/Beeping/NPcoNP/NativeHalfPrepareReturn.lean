import Shared.Beeping.NPcoNP.NativeHalfZeroPreparation
import Shared.Beeping.NPcoNP.NativeHalfTapeScan

/-! Return to the parser after HALF zero-entry preparation. -/
namespace Shared.Beeping.NPcoNP.NativeHalfPrepareReturn
open PASoundness Shared.Beeping Shared.Beeping.Machines
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfState10Exact
open Shared.Beeping.NPcoNP.NativeHalfZeroPreparation
open Shared.Beeping.NPcoNP.NativeSelectorPrefixReturn
open Shared.Beeping.NPcoNP.NativeSelectorThirteen
open Shared.Beeping.NPcoNP.NativeIncBank
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 30000000

theorem half_prepare_empty_returns (q : Fin 284) (hq : q=74 ∨ q=75 ∨ q=76 ∨ q=77) (origin x : Int)
    (t : Int → Bool) (path : List Bool)
    (hentry : x=origin+((path.length : Nat) : Int)) (hlen : 0<path.length)
    (count : path.count false≤11) (word : Holds t origin path)
    (left : ∀ q, q<origin → t q=false) (first : t origin=true)
    (h0 : t x=false) (h1 : t (x+1)=false)
    (marker : t (x+2)=true) :
    let out := setAt x t
    ∃ steps : Nat, 0<steps ∧ Holds out origin path ∧ out x=true ∧
      out (x+1)=false ∧ out (x+2)=true ∧
      (∀ q, q≠x → out q=t q) ∧
      silentSegment machine (cfg q x t) (cfg 93 (origin+1) out) steps := by
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
  have hprepare := zero_prepare_to83 q hq x t 0 h0 h1 (by intro i hi; omega) (by simpa using marker)
  have hprepare' : silentSegment machine (cfg q x t) (cfg 83 (x-1) out) 5 := by
    simpa [out,fill_empty] using hprepare
  obtain ⟨b,hb,hselector⟩ := selector_returns_to_origin out origin path count hword houtleft hfirst
  have hhead : origin+((path.length : Nat) : Int)-1=x-1 := by omega
  rw [hhead] at hselector
  refine ⟨5+b,by omega,hword,?_,?_,?_,hframe,segAdd machine _ _ _ 5 b hprepare' hselector⟩
  · simp [out,setAt]
  · simpa [out,setAt,show x+1≠x by omega] using h1
  · simpa [out,setAt,show x+2≠x by omega] using marker

theorem half_prepare_returns (q : Fin 284) (hq : q=74 ∨ q=75 ∨ q=76 ∨ q=77) (origin x : Int)
    (t : Int → Bool) (path : List Bool) (k : Nat)
    (hentry : x=origin+((path.length : Nat) : Int)) (hlen : 0<path.length)
    (count : path.count false≤11) (word : Holds t origin path)
    (left : ∀ q, q<origin → t q=false) (first : t origin=true)
    (hk : 0<k) (h0 : t x=false) (h1 : t (x+1)=false)
    (zeros : ∀ i : Nat, i<k → t (x+2+(i : Int))=false)
    (marker : t (x+2+(k : Int))=true) :
    let out := fillRange (setAt x t) (x+2) (x+2+(k : Int))
    ∃ steps : Nat, 0<steps ∧ Holds out origin path ∧ out x=true ∧
      out (x+1)=false ∧
      (∀ q, x+2≤q → q≤x+2+(k : Int) → out q=true) ∧
      (∀ q, q<x ∨ x+2+(k : Int)≤q → out q=t q) ∧
      silentSegment machine (cfg q x t) (cfg 93 (origin+1) out) steps := by
  dsimp only
  let out := fillRange (setAt x t) (x+2) (x+2+(k : Int))
  have hframe : ∀ q, q<x ∨ x+2+(k : Int)≤q → out q=t q := by
    intro q hq
    have hn : ¬ (x+2≤q ∧ q<x+2+(k : Int)) := by omega
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
  have hcontrol : ∀ q, x+2≤q → q≤x+2+(k : Int) → out q=true := by
    intro q hq hq'
    by_cases he : q=x+2+(k : Int)
    · rw [hframe q (Or.inr (by omega)),he]
      exact marker
    · simp [out,fillRange,show x+2≤q ∧ q<x+2+(k : Int) by omega]
  let xs := path ++ [true,false] ++ List.replicate (k-1) true
  have htail : Holds out x ([true,false] ++ List.replicate (k-1) true) := by
    simp only [List.cons_append,List.nil_append,Holds]
    refine ⟨hx,?_,?_⟩
    · simpa only [show x+1=x+1 by rfl] using hx1
    · have hr : Holds out (x+2) (List.replicate (k-1) true) := by
        apply holds_of_get
        intro i hi
        have htrue := hcontrol (x+2+(i : Int)) (by omega) (by simp at hi; omega)
        simpa using htrue
      simpa only [show x+1+1=x+2 by omega] using hr
  have hxsword : Holds out origin xs := by
    have hh := holds_append_intro out origin path
      ([true,false] ++ List.replicate (k-1) true) hword (by simpa only [hentry] using htail)
    simpa only [xs,List.append_assoc] using hh
  have hxscount : xs.count false≤13 := by
    simp [xs,List.count_append,List.count_replicate]
    omega
  have hxslen : xs.length=path.length+k+1 := by
    simp only [xs,List.length_append,List.length_cons,List.length_nil,List.length_replicate]
    omega
  obtain ⟨b,hb,hselector⟩ := selector_returns_to_origin_13 out origin xs hxscount hxsword houtleft hfirst
  have hhead : origin+((xs.length : Nat) : Int)-1=x+2+(k : Int)-2 := by rw [hxslen]; omega
  rw [hhead] at hselector
  have hprepare := zero_prepare_to83 q hq x t k h0 h1 zeros marker
  have hprepare' : silentSegment machine (cfg q x t)
      (cfg 83 (x+2+(k : Int)-2) out) (k+4) := by
    simpa [out,show k≠0 by omega] using hprepare
  refine ⟨k+4+b,by omega,hword,hx,hx1,hcontrol,hframe,?_⟩
  exact segAdd machine _ _ _ _ _ hprepare' hselector

/-- Both possible run lengths produce a prepared HALF marker and return to
the original parser under the eleven-zero grammar-path bound. -/
theorem half_prepare_returns_all (q : Fin 284) (hq : q=74 ∨ q=75 ∨ q=76 ∨ q=77)
    (origin x : Int) (t : Int → Bool) (path : List Bool) (k : Nat)
    (hentry : x=origin+((path.length : Nat) : Int)) (hlen : 0<path.length)
    (count : path.count false≤11) (word : Holds t origin path)
    (left : ∀ q, q<origin → t q=false) (first : t origin=true)
    (h0 : t x=false) (h1 : t (x+1)=false)
    (zeros : ∀ i : Nat, i<k → t (x+2+(i : Int))=false)
    (marker : t (x+2+(k : Int))=true) :
    let out := fillRange (setAt x t) (x+2) (x+2+(k : Int))
    ∃ steps : Nat, 0<steps ∧ Holds out origin path ∧ out x=true ∧ out (x+1)=false ∧
      (∀ q, x+2≤q → q≤x+2+(k : Int) → out q=true) ∧
      (∀ q, q<x ∨ x+2+(k : Int)≤q → out q=t q) ∧
      silentSegment machine (cfg q x t) (cfg 93 (origin+1) out) steps := by
  cases k with
  | zero =>
    have hm : t (x+2)=true := by simpa using marker
    obtain ⟨steps,hs,hw,hx,hx1,hx2,hframe,hseg⟩ :=
      half_prepare_empty_returns q hq origin x t path hentry hlen count word left first h0 h1 hm
    refine ⟨steps,hs,?_,?_,?_,?_,?_,?_⟩
    · simpa [fill_empty] using hw
    · simpa [fill_empty] using hx
    · simpa [fill_empty] using hx1
    · intro p hp hp'
      have he : p=x+2 := by simp at hp'; omega
      simpa [fill_empty,he] using hx2
    · intro p hp
      have hne : p≠x := by simp at hp; omega
      simpa [fill_empty] using hframe p hne
    · simpa [fill_empty] using hseg
  | succ k =>
    exact half_prepare_returns q hq origin x t path (k+1) hentry hlen count word left first
      (by omega) h0 h1 zeros marker

#print axioms half_prepare_empty_returns
#print axioms half_prepare_returns
#print axioms half_prepare_returns_all
end Shared.Beeping.NPcoNP.NativeHalfPrepareReturn
