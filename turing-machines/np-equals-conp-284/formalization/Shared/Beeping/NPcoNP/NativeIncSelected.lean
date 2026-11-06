import Shared.Beeping.NPcoNP.NativeIncReturn

/-! A selected unary register after an arbitrary protected prior. This is a
supplied physical layout, not a graph-to-tape representation theorem. -/
namespace Shared.Beeping.NPcoNP.NativeIncSelected
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfBankFirst
open Shared.Beeping.NPcoNP.NativeHalfScannerFrames
open Shared.Beeping.NPcoNP.NativeIncBank
open Shared.Beeping.NPcoNP.NativeIncReturn
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000

theorem holds_prefix (t : Int → Bool) (h : Int) (xs ys : List Bool)
    (hw : Holds t h (xs++ys)) : Holds t h xs := by
  induction xs generalizing h with
  | nil => trivial
  | cons b xs ih =>
    simp only [List.cons_append,Holds] at hw ⊢
    exact ⟨hw.1,ih (h+1) hw.2⟩

/-- The literal increment stage preserves the complete encoded prior and
increments the selected next value. Its subsequent return to state 93 is
positive, finite and silent, but no final tape correspondence is asserted. -/
theorem reachable_selected_increment_then_93 (time : Nat) (prior rest : List Nat)
    (v : Nat) (base : Int) (t : Int → Bool)
    (hc : machine.system.run time =
      cfg 14 (base+((encode prior).length : Int)) t)
    (bank : Holds t base (encode (prior ++ v::rest) ++ [false])) :
    ∃ (mid out : Config 284) (extra : Nat), mid.state=23 ∧
      Holds mid.tape base (encode (prior ++ (v+1)::rest)) ∧
      (∀ p<base, mid.tape p=t p) ∧
      0<extra ∧ out.state=93 ∧
      silentSegment machine (machine.system.run time) mid (v+3+(encode rest).length) ∧
      silentSegment machine mid out extra := by
  let h := base+((encode prior).length : Int)
  have whole : Holds t base (encode prior ++ (encode (v::rest) ++ [false])) := by
    simpa [encode_append,List.append_assoc] using bank
  have hprefix : Holds t base (encode prior) := holds_prefix t base _ _ whole
  have hselected : Holds t h (encode (v::rest) ++ [false]) := by
    exact holds_append_tail t base (encode prior) (encode (v::rest) ++ [false]) whole
  obtain ⟨mid,out,extra,h23,hhead,hselected',hframe,hextra,h93,hseg,hreturn⟩ :=
    reachable_increment_then_93 time v rest h t hc hselected
  have hprefix' : Holds mid.tape base (encode prior) := by
    apply holds_transport t mid.tape base (encode prior) hprefix
    intro p hlo hhi
    symm
    apply hframe p
    left
    exact hhi
  have hwhole : Holds mid.tape base (encode (prior ++ (v+1)::rest)) := by
    have hh := holds_append_intro mid.tape base (encode prior) (encode ((v+1)::rest))
      hprefix' hselected'
    simpa [encode_append] using hh
  refine ⟨mid,out,extra,h23,hwhole,?_,hextra,h93,hseg,hreturn⟩
  intro p hp
  apply hframe p
  left
  dsimp [h]
  have hn : (0 : Int)≤(encode prior).length := by omega
  omega

#print axioms reachable_selected_increment_then_93
end Shared.Beeping.NPcoNP.NativeIncSelected
