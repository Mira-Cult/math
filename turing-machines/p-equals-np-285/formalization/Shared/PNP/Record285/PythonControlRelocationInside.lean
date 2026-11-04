import Shared.PNP.Record285.PythonControlRelocationInvariant

/-! The checked decoder control-flow targets keep the entire reference loop
stack inside the shared region until its exit. Fault remains explicit. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace Shared.PNP.Record285.PythonControlRelocationInside
open Shared.PNP.Record285.PythonSyntax
open Shared.PNP.Record285.PythonStraight
open Shared.PNP.Record285.PythonControl
open Shared.PNP.Record285.PythonControlRelocation
open Shared.PNP.Record285.PythonControlRelocationStep
open Shared.PNP.Record285.PythonControlRelocationInvariant

def Inside : Status → Prop
  | .fault => True
  | .returned _ => False
  | .live c => 47 ≤ c.pc ∧ c.pc ≤ 65 ∧ ∃ inner,
      c.loops = inner++referenceBase ∧ ∀ l ∈ inner, 47 ≤ l.head ∧ l.head ≤ 65

theorem live_inside (pc : Nat) (s : Store) (inner : List Loop)
    (hlo : 47 ≤ pc) (hhi : pc ≤ 65)
    (hheads : ∀ l ∈ inner, 47 ≤ l.head ∧ l.head ≤ 65) :
    Inside (.live ⟨pc,s,inner++referenceBase⟩) :=
  ⟨hlo,hhi,inner,rfl,hheads⟩

theorem reference_step_bounded (pc : Nat) (s : Store) (inner : List Loop) (line : Line)
    (hlo : 47 ≤ pc) (hhi : pc < 65)
    (hheads : ∀ l ∈ inner, 47 ≤ l.head ∧ l.head ≤ 65)
    (hsettle : settle pc (inner++referenceBase)=(pc,inner++referenceBase))
    (hrow : code[pc]?=some line) (hallowed : Allowed line) (hb : LineBounds pc line) :
    Inside (step code (.live ⟨pc,s,inner++referenceBase⟩)).1 := by
  have hnextlo : 47 ≤ pc+1 := by omega
  have hnexthi : pc+1 ≤ 65 := by omega
  cases line with
  | function n a => exact False.elim hallowed
  | blank => exact False.elim hallowed
  | call i n => exact False.elim hallowed
  | return_ i e => exact False.elim hallowed
  | break_ i => exact False.elim hallowed
  | while_ level e =>
    change 47 ≤ seek code (pc+1) level ∧ seek code (pc+1) level ≤ 65 at hb
    cases he : eval s e with
    | none => simp [step,hsettle,hrow,he,Inside]
    | some v =>
      by_cases hz : v=0
      · simp only [step,hsettle,Prod.fst,Prod.snd,hrow,he,if_pos hz]
        exact live_inside _ _ _ hb.1 hb.2 hheads
      · simp only [step,hsettle,Prod.fst,Prod.snd,hrow,he,if_neg hz]
        apply live_inside (pc+1) s (⟨pc,seek code (pc+1) level⟩::inner) hnextlo hnexthi
        intro l hl
        simp only [List.mem_cons] at hl
        rcases hl with rfl | hl
        · change 47 ≤ pc ∧ pc ≤ 65
          exact ⟨hlo,by omega⟩
        · exact hheads l hl
  | if_ level e =>
    change 47 ≤ jumpFalse code pc level ∧ jumpFalse code pc level ≤ 65 at hb
    cases he : eval s e with
    | none => simp [step,hsettle,hrow,he,Inside]
    | some v =>
      by_cases hz : v=0
      · simp only [step,hsettle,Prod.fst,Prod.snd,hrow,he,if_pos hz]
        exact live_inside _ _ _ hb.1 hb.2 hheads
      · simp only [step,hsettle,Prod.fst,Prod.snd,hrow,he,if_neg hz]
        exact live_inside _ _ _ hnextlo hnexthi hheads
  | else_ level =>
    change 47 ≤ seek code (pc+1) level ∧ seek code (pc+1) level ≤ 65 at hb
    simp only [step,hsettle,Prod.fst,Prod.snd,hrow]
    exact live_inside _ _ _ hb.1 hb.2 hheads
  | assign level name e =>
    cases he : simple (.assign level name e) s with
    | none => simp only [step,hsettle,Prod.fst,Prod.snd,hrow,he,Inside]
    | some v =>
      simp only [step,hsettle,Prod.fst,Prod.snd,hrow,he]
      exact live_inside _ _ _ hnextlo hnexthi hheads
  | assignMany level names es =>
    cases he : simple (.assignMany level names es) s with
    | none => simp only [step,hsettle,Prod.fst,Prod.snd,hrow,he,Inside]
    | some v =>
      simp only [step,hsettle,Prod.fst,Prod.snd,hrow,he]
      exact live_inside _ _ _ hnextlo hnexthi hheads
  | aug level name op e =>
    cases he : simple (.aug level name op e) s with
    | none => simp only [step,hsettle,Prod.fst,Prod.snd,hrow,he,Inside]
    | some v =>
      simp only [step,hsettle,Prod.fst,Prod.snd,hrow,he]
      exact live_inside _ _ _ hnextlo hnexthi hheads

end Shared.PNP.Record285.PythonControlRelocationInside
