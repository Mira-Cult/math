import Shared.Beeping.ComparisonTM2
import Shared.Beeping.Controller

/-! A single terminating comparison program returns the Boolean result and
both updated controller counters. It is suitable for a later restart loop;
the restart and event emission are not constructed in this module. -/
namespace Shared.Beeping.ControllerCode
open Turing.ToPartrec
open Shared.Beeping.ComparisonTM2

def candidate (R : Nat → Nat → Bool) (e n : Nat) : Nat := if R e n then e else e+1
def test (R : Nat → Nat → Bool) (e n : Nat) : Nat := if R e n then n+1 else 0

theorem candidate_computable (R : Nat → Nat → Bool) (hR : Computable₂ R) :
    Computable₂ (candidate R) := by
  have h := Computable.cond hR Computable.fst (Computable.succ.comp Computable.fst)
  apply h.of_eq
  rintro ⟨e,n⟩
  simp only [candidate]
  cases R e n <;> rfl

theorem test_computable (R : Nat → Nat → Bool) (hR : Computable₂ R) :
    Computable₂ (test R) := by
  have h := Computable.cond hR (Computable.succ.comp Computable.snd) (Computable.const 0)
  apply h.of_eq
  rintro ⟨e,n⟩
  simp only [test]
  cases R e n <;> rfl

theorem numeric_has_code (f : Nat → Nat → Nat) (hf : Computable₂ f) :
    ∃ c : Code, ∀ e n, c.eval [e,n] = pure [f e n] := by
  have hp : Nat.Partrec' (fun v : List.Vector Nat 2 =>
      (pure (f v.head v.tail.head) : Part Nat)) := Nat.Partrec'.part_iff₂.mpr hf.partrec₂
  obtain ⟨c,hc⟩ := Code.exists_code hp
  refine ⟨c, ?_⟩
  intro e n
  have h := hc (⟨[e,n],rfl⟩ : List.Vector Nat 2)
  change c.eval [e,n] = pure [f e n] at h
  exact h

/-- A finite code computes the result and updated counters in one call.
The inputs and outputs are ordinary natural-number lists. -/
theorem has_update_code (R : Nat → Nat → Bool) (hR : Computable₂ R) :
    ∃ c : Code, ∀ e n, c.eval [e,n] =
      pure [result R e n,candidate R e n,test R e n] := by
  obtain ⟨cb,hb⟩ := comparison_has_code R hR
  obtain ⟨ce,he⟩ := numeric_has_code (candidate R) (candidate_computable R hR)
  obtain ⟨cn,hn⟩ := numeric_has_code (test R) (test_computable R hR)
  refine ⟨Code.cons cb (Code.cons ce (Code.cons cn Code.nil)), ?_⟩
  intro e n
  simp [Code.cons_eval,hb e n,he e n,hn e n]

end Shared.Beeping.ControllerCode
