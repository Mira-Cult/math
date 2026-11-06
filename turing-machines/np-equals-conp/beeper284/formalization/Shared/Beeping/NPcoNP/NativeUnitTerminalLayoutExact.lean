import Shared.Beeping.NPcoNP.NativeUnitControlMerge
import Shared.Beeping.NPcoNP.NativeUnitWindowTerminalPhased
import Shared.Beeping.NPcoNP.NativeHalfMarkerUnitContinue
import Shared.Beeping.NPcoNP.Bootstrap284CanonicalTape

/-! Exact phased unit/terminal macro restoring the marked selector layout,
updated bank, and protected trailing sentinel. -/
namespace Shared.Beeping.NPcoNP.NativeUnitTerminalLayoutExact
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.NativeHalfMarkerUnitContinue
open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.NativeUnitWindowTerminalPhased
open Shared.Beeping.NPcoNP.NativeUnitControlMerge
open Shared.Beeping.NPcoNP.Bootstrap284CanonicalTape
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 9000000

/-- One compound unit/terminal step produces the next fourteen-block
selector, its two markers, and an incremented bank with one trailing zero.
Two initial bank sentinels are required to retain the latter property. -/
theorem unit_terminal_next_layout_exact (t : Int → Bool) (a b : Int) (k z r v : Nat)
    (zs rest : List Nat)
    (window : Holds t a (markerWindow (List.replicate k 0 ++ 1::0::z::zs)))
    (hlen : (List.replicate k 0 ++ 1::0::z::zs).length=14)
    (hr : 1<r)
    (pre : t (a+((2*k : Nat):Int)+3)=false)
    (scanword : Holds t (a+((2*k : Nat):Int)+6) (List.replicate r true ++ [false]))
    (bank : Holds t (a+((2*k : Nat):Int)+6+(r : Int)+1) (encode (v::rest) ++ [false,false]))
    (terminalPos : b+((2*13 : Nat):Int)+3=a+((2*k : Nat):Int)+3)
    (terminal : Holds t b (markerWindow (List.replicate 13 0 ++ [1])))
    (terminalBefore : t (b-1)=true)
    (left0 : t (a-2)=false) (left1 : t (a-1)=true) (before : t (a-3)=true)
    (marker : t (a+((encode (List.replicate k 0 ++ 1::0::z::zs)).length : Int))=true)
    (alignment : a+((encode (List.replicate k 0 ++ 1::0::z::zs)).length : Int)=
      a+((2*k : Nat):Int)+4+(r : Int)) :
    let d := a+((2*k : Nat):Int)+4
    let base := d+2+(r : Int)+1
    let values := (v+1)::rest
    let next := List.replicate (k+1) 0 ++ 3::z::zs
    ∃ mid : Config 284, mid.state=23 ∧
      silentSegment machine (cfg 93 a t) mid
        ((2*k+4)+(r+v+6+(encode rest).length)) ∧
      next.length=14 ∧
      let final := setAt (d-1) (setAt d mid.tape)
      Holds final (a-2) (markerWindow next) ∧ final (a-3)=true ∧
      final (a+((encode (List.replicate k 0 ++ 1::0::z::zs)).length : Int))=true ∧
      Holds final base (encode values ++ [false]) ∧
      Holds final (a+((encode (List.replicate k 0 ++ 1::0::z::zs)).length : Int))
        (List.replicate 2 true ++ [false]) ∧
      (∀ q, q≠d-1 → (q<base ∨ base+(((v+1)+(encode rest).length : Nat):Int)<q) → final q=t q) ∧
      (a-2)+((encode next).length : Int)-1=d+(r : Int)-1 ∧
      silentSegment machine mid (cfg 83 (d+(r : Int)-1) final)
        ((encode values).length+r+2+(2*r+7)+(4*13+(r-1)+12)) := by
  dsimp only
  let xs := List.replicate k 0 ++ 1::0::z::zs
  let d := a+((2*k : Nat):Int)+4
  let base := d+2+(r : Int)+1
  let last := base+(((v+1)+(encode rest).length : Nat):Int)
  let values := (v+1)::rest
  let next := List.replicate (k+1) 0 ++ 3::z::zs
  have hbase : base=a+((2*k : Nat):Int)+6+(r : Int)+1 := by dsimp [base,d]; omega
  have hbank2 : Holds t base (encode (v::rest) ++ [false,false]) := by
    rw [hbase]
    exact bank
  have hbank1 : Holds t base (encode (v::rest) ++ [false]) := by
    apply holds_prefix_word t base (encode (v::rest) ++ [false]) [false]
    simpa [List.append_assoc] using hbank2
  have hlenOld : (encode values).length=(encode (v::rest)).length+1 := by
    simp [values,encode,block_length]
    omega
  have ht : t (base+((encode values).length : Int))=false := by
    have hget := holds_get t base (encode (v::rest) ++ [false,false]) hbank2
      ((encode (v::rest)).length+1) (by simp)
    have hv : (encode (v::rest) ++ [false,false])[(encode (v::rest)).length+1] = false := by simp
    rw [hv] at hget
    simpa [hlenOld] using hget
  obtain ⟨mid,hs,hfirst,hout,hframe,hseg⟩ :=
    unit_through_terminal_phased_exact t a b k z r v zs rest window hr pre scanword
      (by rw [←hbase]; exact hbank1) (by decide) terminalPos terminal terminalBefore
  let final := setAt (d-1) (setAt d mid.tape)
  have halign : a+((encode xs).length : Int)=d+(r : Int) := by simpa [xs,d] using alignment
  have hframe' : ∀ q, q≤a+((encode xs).length : Int) → q≠a+((2*k+3 : Nat):Int) → final q=t q := by
    intro q hq hne
    apply hframe q
    · dsimp [d] at *
      omega
    · left
      dsimp [base]
      omega
  have hwritten : final (a+((2*k+3 : Nat):Int))=true := by
    have he : a+((2*k+3 : Nat):Int)=d-1 := by dsimp [d]; omega
    rw [he]
    simp [final,setAt]
  obtain ⟨hwindow,hbefore,hmarker⟩ :=
    merge_control_window t final a k z zs window left0 left1 before marker hwritten hframe'
  have hsent : final (base+((encode values).length : Int))=false := by
    have hnonneg : (0:Int)≤((encode values).length : Int) := by omega
    have hne : base+((encode values).length : Int)≠d-1 := by dsimp [base]; omega
    have hvalLen : (encode values).length=(v+1)+(encode rest).length+2 := by
      simp [values,encode,block_length]
      omega
    have hgt : last<base+((encode values).length : Int) := by
      dsimp [last]
      rw [hvalLen]
      push_cast
      omega
    have hh : final (base+((encode values).length : Int))=
        t (base+((encode values).length : Int)) := hframe _ hne (Or.inr hgt)
    exact hh.trans ht
  have hfull : Holds final base (encode values ++ [false]) := by
    apply holds_append_intro final base (encode values) [false] hout
    simpa [Holds] using hsent
  have hnext : next.length=14 := by
    dsimp [next,xs] at *
    simp only [List.length_append,List.length_replicate,List.length_cons] at *
    omega
  have hsplit := split_ones r (a+((2*k : Nat):Int)+6) t [false] scanword
  have hone : t (a+((encode xs).length : Int)+1)=true := by
    have hh := hsplit.1 (r-1) (by omega)
    have he : a+((2*k : Nat):Int)+6+((r-1 : Nat):Int) =
        a+((encode xs).length : Int)+1 := by dsimp [d] at halign; omega
    rw [he] at hh
    exact hh
  have hzero : t (a+((encode xs).length : Int)+2)=false := by
    have hh := hsplit.2.1
    have he : a+((2*k : Nat):Int)+6+(r : Int) =
        a+((encode xs).length : Int)+2 := by dsimp [d] at halign; omega
    rw [he] at hh
    exact hh
  have hone' : final (a+((encode xs).length : Int)+1)=true := by
    have hh : final (a+((encode xs).length : Int)+1)=
        t (a+((encode xs).length : Int)+1) := hframe _ (by dsimp [d] at halign ⊢; omega)
          (Or.inl (by dsimp [base]; omega))
    exact hh.trans hone
  have hzero' : final (a+((encode xs).length : Int)+2)=false := by
    have hh : final (a+((encode xs).length : Int)+2)=
        t (a+((encode xs).length : Int)+2) := hframe _ (by dsimp [d] at halign ⊢; omega)
          (Or.inl (by dsimp [base]; omega))
    exact hh.trans hzero
  have hext : Holds final (a+((encode xs).length : Int)) (List.replicate 2 true ++ [false]) := by
    simp only [List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append,Holds]
    refine ⟨hmarker,hone',?_,trivial⟩
    have he : a+((encode xs).length : Int)+1+1=a+((encode xs).length : Int)+2 := by omega
    rw [he]
    exact hzero'
  have hhead : (a-2)+((encode next).length : Int)-1=d+(r : Int)-1 := by
    have hh := merged_window_length k z zs
    change (encode next).length=(encode xs).length+2 at hh
    rw [hh]
    push_cast
    omega
  exact ⟨mid,hs,hfirst,hnext,hwindow,hbefore,hmarker,hfull,hext,hframe,hhead,hseg⟩

#print axioms unit_terminal_next_layout_exact
end Shared.Beeping.NPcoNP.NativeUnitTerminalLayoutExact
