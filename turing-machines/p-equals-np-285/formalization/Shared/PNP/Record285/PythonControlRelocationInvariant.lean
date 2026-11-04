import Shared.PNP.Record285.PythonControlRelocationActual

/-! Bounds needed to compose decoder relocation across many line steps. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace Shared.PNP.Record285.PythonControlRelocationInvariant
open Shared.PNP.Record285.PythonControl
open Shared.PNP.Record285.PythonControlRelocation
open Shared.PNP.Record285.PythonSyntax

theorem settle_shared_bounded (pc : Nat) (inner : List Loop)
    (hlo : 47 ≤ pc) (hhi : pc ≤ 65)
    (hheads : ∀ l ∈ inner, 47 ≤ l.head ∧ l.head ≤ 65) :
    ∃ target remaining, 47 ≤ target ∧ target ≤ 65 ∧
      (∀ l ∈ remaining, 47 ≤ l.head ∧ l.head ≤ 65) ∧
      settle pc (inner ++ referenceBase) = (target,remaining ++ referenceBase) ∧
      settle (pc+47) (inner.map shiftLoop ++ candidateBase) =
        (target+47,remaining.map shiftLoop ++ candidateBase) := by
  induction inner generalizing pc with
  | nil =>
    refine ⟨pc,[],hlo,hhi,by simp,?_,?_⟩ <;>
      simp [settle,referenceBase,candidateBase] <;> omega
  | cons l rest ih =>
    have hl : 47 ≤ l.head ∧ l.head ≤ 65 := hheads l (by simp)
    have hr : ∀ x ∈ rest, 47 ≤ x.head ∧ x.head ≤ 65 := by
      intro x hx
      exact hheads x (by simp [hx])
    by_cases h : l.exit ≤ pc
    · have hc : (shiftLoop l).exit ≤ pc+47 := by simp [shiftLoop]; omega
      obtain ⟨target,remaining,htlo,hthi,hrem,href,hcand⟩ := ih l.head hl.1 hl.2 hr
      refine ⟨target,remaining,htlo,hthi,hrem,?_,?_⟩
      · simpa [settle,h] using href
      · simpa [settle,h,hc,shiftLoop] using hcand
    · have hc : ¬ (shiftLoop l).exit ≤ pc+47 := by simp [shiftLoop]; omega
      refine ⟨pc,l::rest,hlo,hhi,hheads,?_,?_⟩
      · simp [settle,h]
      · simp [settle,h,hc,shiftLoop]

def LineBounds (pc : Nat) : Line → Prop
  | .while_ level _ => 47 ≤ seek code (pc+1) level ∧ seek code (pc+1) level ≤ 65
  | .if_ level _ => 47 ≤ jumpFalse code pc level ∧ jumpFalse code pc level ≤ 65
  | .else_ level => 47 ≤ seek code (pc+1) level ∧ seek code (pc+1) level ≤ 65
  | _ => True

instance (pc : Nat) (line : Line) : Decidable (LineBounds pc line) := by
  cases line <;> simp [LineBounds] <;> infer_instance

def boundsCheck (i : Nat) : Bool :=
  match code[47+i]? with
  | none => false
  | some line => decide (LineBounds (47+i) line)

theorem bounds_checks : (List.range 18).all boundsCheck = true := by decide

theorem decoder_bounds (i : Nat) (hi : i < 18) (line : Line)
    (hline : code[47+i]? = some line) : LineBounds (47+i) line := by
  have h := (List.all_eq_true).1 bounds_checks i (List.mem_range.2 hi)
  exact of_decide_eq_true (by simpa [boundsCheck,hline] using h)

end Shared.PNP.Record285.PythonControlRelocationInvariant
