import Shared.Beeping.NPcoNP.NativeAllZeroTerminalReturn

/-! Preserve an arbitrary supplied finite bank suffix through the
marker-present terminal return. This does not assert recurrence. -/
namespace Shared.Beeping.NPcoNP.NativeAllZeroTerminalSuffix
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfState14Progress
open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeHalfBankFirst
open Shared.Beeping.NPcoNP.NativeHalfMarkerUnitContinue
open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.NativeAllZeroTerminalReturn
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 12000000
attribute [local irreducible] machine

/-- The increment consumes one of two explicitly supplied zero sentinels;
every bit of a following finite suffix is preserved. -/
theorem all_zero_terminal_return_suffix (a : Int) (r v : Nat) (rest : List Nat)
    (suffix : List Bool) (t : Int → Bool)
    (window : Holds t a (markerWindow (List.replicate 13 0 ++ [0])))
    (earlier : t (a-1)=true)
    (marker : t (a+28)=true) (nextZero : t (a+29)=false)
    (h0 : t (a+30)=false) (h1 : t (a+31)=false)
    (hz : ∀ i : Nat, i<r+2 → t (a+32+(i : Int))=false)
    (hm : t (a+34+(r : Int))=true)
    (delimiter : t (a+35+(r : Int))=false)
    (bank : Holds t (a+36+(r : Int)) ((encode (v::rest) ++ [false,false]) ++ suffix)) :
    ∃ mid : Config 284, mid.state=23 ∧
      silentSegment machine (cfg 93 a t) mid
        ((2*r+66)+((2*11+4)+((r+3)+v+6+(encode rest).length))) ∧
      let final := setAt (a+29) (setAt (a+30) mid.tape)
      Holds final (a+2) (markerWindow (List.replicate 12 0 ++ [3,r])) ∧
      final (a+1)=true ∧
      Holds final (a+36+(r : Int)) ((encode ((v+1)::rest) ++ [false]) ++ suffix) ∧
      (∀ q, q≠a+29 →
        (q<a+30 ∨ a+36+(r : Int)+(((v+1)+(encode rest).length : Nat):Int)<q) →
        final q=t q) ∧
      silentSegment machine mid (cfg 83 (a+32+(r : Int)) final)
        ((encode ((v+1)::rest)).length+(r+3)+2+(2*(r+3)+7)+(4*13+((r+3)-1)+12)) := by
  let base := a+36+(r : Int)
  let old := encode (v::rest) ++ [false,false]
  let new := encode ((v+1)::rest) ++ [false]
  have hpref : Holds t base old := holds_prefix_word t base old suffix bank
  have htail : Holds t (base+((old.length : Nat):Int)) suffix :=
    holds_append_tail t base old suffix bank
  obtain ⟨mid,hs,hfirst,hwindow,hbefore,hbank,hframe,hreturn⟩ :=
    all_zero_terminal_return_framed a r v rest t window earlier marker nextZero h0 h1 hz hm delimiter hpref
  let final := setAt (a+29) (setAt (a+30) mid.tape)
  have hlen : new.length=old.length := by
    simp [new,old,encode,block_length]
    omega
  have hsize : new.length=(v+1)+(encode rest).length+3 := by
    simp [new,encode,block_length]
    omega
  have htail' : Holds final (base+((new.length : Nat):Int)) suffix := by
    apply holds_transport t final _ suffix
      (by rw [hlen]; exact htail)
    intro q hq _
    symm
    apply hframe q
    · dsimp [base] at hq
      have hn : (0:Int)≤((new.length : Nat):Int) := by omega
      omega
    · right
      rw [hsize] at hq
      dsimp [base] at hq
      push_cast at hq
      omega
  have hfull : Holds final base (new++suffix) :=
    holds_append_intro final base new suffix hbank htail'
  exact ⟨mid,hs,hfirst,hwindow,hbefore,hfull,hframe,hreturn⟩

#print axioms all_zero_terminal_return_suffix
end Shared.Beeping.NPcoNP.NativeAllZeroTerminalSuffix
