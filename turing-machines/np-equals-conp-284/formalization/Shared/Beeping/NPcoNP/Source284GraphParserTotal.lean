import Shared.Beeping.NPcoNP.Source284GraphParserLiteral
import Shared.Beeping.NPcoNP.Source284GraphParserDouble
import Shared.Beeping.NPcoNP.Source284ScanSemantics

/-! Composing the marker/payload loop of the checked register graph.
The entry bank is supplied; no physical-tape reachability is asserted. -/
namespace Shared.Beeping.NPcoNP.Source284GraphParserTotal

open PASoundness PASoundness.RegisterMachine
open Shared.Beeping.NPcoNP.Parent290Coalesced
open Shared.Beeping.NPcoNP.Source284GraphParserLiteral
open Shared.Beeping.NPcoNP.Source284GraphParserDouble
open Shared.Beeping.NPcoNP.Source284Parser

abbrev B := PASoundness.RegisterMachine.Bank 12
abbrev C := PASoundness.RegisterMachine.Config 12 185

def header (b : B) (s n e : Nat) : B :=
  write (write (write b 0 s) 5 n) 6 e

@[simp] theorem header_zero (b : B) (s n e : Nat) : header b s n e 0 = s := by
  simp [header, write]
@[simp] theorem header_five (b : B) (s n e : Nat) : header b s n e 5 = n := by
  simp [header, write]
@[simp] theorem header_six (b : B) (s n e : Nat) : header b s n e 6 = e := by
  simp [header, write]
@[simp] theorem header_ten (b : B) (s n e : Nat) : header b s n e 10 = b 10 := by
  simp [header, write]

@[simp] theorem header_set_zero (b : B) (s n e x : Nat) :
    write (header b s n e) 0 x = header b x n e := by
  funext i
  fin_cases i <;> simp [header, write]

@[simp] theorem header_set_five (b : B) (s n e x : Nat) :
    write (header b s n e) 5 x = header b s x e := by
  funext i
  fin_cases i <;> simp [header, write]

@[simp] theorem header_set_six (b : B) (s n e x : Nat) :
    write (header b s n e) 6 x = header b s n x := by
  funext i
  fin_cases i <;> simp [header, write]

def SilentSegment (a z : C) (k : Nat) : Prop :=
  target.system.advance a k = z ∧ target.system.wordFrom a k = []

theorem cat {a b c : C} {k l : Nat}
    (h : SilentSegment a b k) (g : SilentSegment b c l) :
    SilentSegment a c (k+l) := by
  rcases h with ⟨ha, hw⟩
  rcases g with ⟨ga, gw⟩
  constructor
  · rw [WordEventSystem.advance_add, ha, ga]
  · rw [WordEventSystem.wordFrom_add, ha, hw, gw]
    rfl

theorem first_step (b : B) (s n e : Nat) :
    SilentSegment ⟨13,header b s n e⟩
      ⟨if s % 2 = 0 then 22 else 14, header b (s/2) n e⟩ 1 := by
  have hs := marker_step (header b s n e)
  simp only [header_zero, header_set_zero] at hs
  constructor
  · simpa [WordEventSystem.advance] using congrArg Prod.fst hs
  · simpa [WordEventSystem.wordFrom, WordEventSystem.advance] using congrArg Prod.snd hs

theorem finish_even (b : B) (s n e : Nat) (h : s % 2 = 0) :
    SilentSegment ⟨13,header b s n e⟩ ⟨23,header b 0 n e⟩ (1+(s/2+1)) := by
  have ha := first_step b s n e
  simp only [h, if_true] at ha
  have hc := Source284GraphParserLiteral.clear_segment (s/2) (header b (s/2) n e) (by simp)
  simp only [header_set_zero] at hc
  exact cat ha hc

theorem next_odd (b : B) (s n e : Nat) (h : s % 2 = 1) (hz : b 10 = 0) :
    ∃ k, 0 < k ∧ SilentSegment ⟨13,header b s n e⟩
      ⟨13,header b (s/4) (n+1) (2*e+(s/2)%2)⟩ k := by
  have ha := first_step b s n e
  have hn : s % 2 ≠ 0 := by omega
  simp only [hn, if_false] at ha
  have hd := double_segment (header b (s/2) n e) (by simpa using hz)
  simp only [header_six, header_set_six] at hd
  let q := (s/2)%2
  let k := if q = 0 then 2 else 3
  have hp := Source284GraphParserLiteral.payload_steps (header b (s/2) n (2*e))
  simp only [header_zero, header_five, header_six, header_set_zero,
    header_set_five, header_set_six, Nat.div_div_eq_div_mul] at hp
  have hp' : SilentSegment ⟨19, header b (s/2) n (2*e)⟩
      ⟨13,header b (s/4) (n+1) (2*e+(s/2)%2)⟩ k := by
    simpa [SilentSegment, k, q] using hp
  refine ⟨1+(7*e+2)+k, by omega, ?_⟩
  exact cat (cat ha ⟨hd.1, hd.2.1⟩) hp'

theorem loop (b : B) (s n e : Nat) (hz : b 10 = 0) :
    ∃ k, 0 < k ∧ SilentSegment ⟨13,header b s n e⟩
      ⟨23,header b 0 (run s n e).1 (run s n e).2⟩ k := by
  induction s using Nat.strong_induction_on generalizing n e with
  | h s ih =>
    by_cases ho : s % 2 = 1
    · have hs : 0 < s := by omega
      have hlt : s/4 < s := Nat.div_lt_self hs (by decide)
      obtain ⟨k, hk, hf⟩ := next_odd b s n e ho hz
      obtain ⟨l, hl, hg⟩ := ih (s/4) hlt (n+1) (2*e+(s/2)%2)
      rw [run_odd s n e ho]
      exact ⟨k+l, by omega, cat hf hg⟩
    · have he : s % 2 = 0 := by omega
      rw [run_even s n e he]
      exact ⟨1+(s/2+1), by omega, finish_even b s n e he⟩

end Shared.Beeping.NPcoNP.Source284GraphParserTotal
