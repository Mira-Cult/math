import Shared.PNP.Record285.PythonControlBegin

/-! A finite typed-interpreter segment with exact zero-or-one event accounting. -/
set_option maxRecDepth 8192
namespace Shared.PNP.Record285.PythonControlLocal
open Shared.PNP.Record285.PythonControl
open Shared.PNP.Record285.PythonControlSkip (pySystem Silent)
open Shared.PNP.Record285.PythonControlBegin (Marked)

def Local (a b : Status) (n : Nat) (event : Bool) : Prop :=
  pySystem.advance a n=b ∧
    (event=true ↔ ∃ j, j<n ∧ pySystem.BeepFrom a j) ∧
    ∀ j k, j<n → k<n → pySystem.BeepFrom a j → pySystem.BeepFrom a k → j=k

theorem silent_local {a b : Status} {n : Nat} (h : Silent a b n) : Local a b n false := by
  refine ⟨h.1,?_,?_⟩
  · constructor
    · intro hf; cases hf
    · rintro ⟨j,hj,hb⟩; exact False.elim (h.2 j hj hb)
  · intro j k hj hk hb hkbeep
    exact False.elim (h.2 j hj hb)

theorem marked_local {a b : Status} {n mark : Nat} (h : Marked a b n mark)
    (hmark : mark<n) : Local a b n true := by
  refine ⟨h.1,?_,?_⟩
  · constructor
    · intro _
      exact ⟨mark,hmark,(h.2 mark hmark).2 rfl⟩
    · intro _; rfl
  · intro j k hj hk hb hkbeep
    have hjm := (h.2 j hj).1 hb
    have hkm := (h.2 k hk).1 hkbeep
    exact hjm.trans hkm.symm

end Shared.PNP.Record285.PythonControlLocal
