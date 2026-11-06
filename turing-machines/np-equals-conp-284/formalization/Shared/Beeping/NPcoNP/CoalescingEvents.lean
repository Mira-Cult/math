import Shared.Beeping.NPcoNP.CoalescingProgram
import Shared.Beeping.WordBridge

/-! Event consequences of conditional lockstep register coalescing. The
source-run ownership and row translation assumptions remain explicit. -/

namespace Shared.Beeping.NPcoNP.CoalescingAlgebra
open PASoundness
open Shared.Beeping

theorem stepWord_eq {n m states : Nat} (f : Fin n → Fin m)
    (source : MaskInvariant.Program n states) (target : MaskInvariant.Program m states)
    (hstart : target.start = source.start) (hrows : RowsTranslate f source target)
    (howner : ∀ t, AccessOK f (source.system.run t).bank
      source.code[(source.system.run t).state].action) (t : Nat) :
    (target.system.step (target.system.run t)).2 =
      (source.system.step (source.system.run t)).2 := by
  rw [run_pack f source target hstart hrows howner t,
    step_commutes f source target hrows _ (howner t)]

theorem beepAt_iff {n m states : Nat} (f : Fin n → Fin m)
    (source : MaskInvariant.Program n states) (target : MaskInvariant.Program m states)
    (hstart : target.start = source.start) (hrows : RowsTranslate f source target)
    (howner : ∀ t, AccessOK f (source.system.run t).bank
      source.code[(source.system.run t).state].action) (t : Nat) :
    source.system.erase.BeepAt t ↔ target.system.erase.BeepAt t := by
  rw [WordEventSystem.erase_beep_iff, WordEventSystem.erase_beep_iff,
    stepWord_eq f source target hstart hrows howner t]

theorem eventuallySilent_iff {n m states : Nat} (f : Fin n → Fin m)
    (source : MaskInvariant.Program n states) (target : MaskInvariant.Program m states)
    (hstart : target.start = source.start) (hrows : RowsTranslate f source target)
    (howner : ∀ t, AccessOK f (source.system.run t).bank
      source.code[(source.system.run t).state].action) :
    source.system.erase.EventuallySilent ↔ target.system.erase.EventuallySilent := by
  simp only [EventSystem.EventuallySilent, beepAt_iff f source target hstart hrows howner]

theorem infinitelyManyBeeps_iff {n m states : Nat} (f : Fin n → Fin m)
    (source : MaskInvariant.Program n states) (target : MaskInvariant.Program m states)
    (hstart : target.start = source.start) (hrows : RowsTranslate f source target)
    (howner : ∀ t, AccessOK f (source.system.run t).bank
      source.code[(source.system.run t).state].action) :
    source.system.erase.InfinitelyManyBeeps ↔ target.system.erase.InfinitelyManyBeeps := by
  rw [← EventSystem.not_eventuallySilent_iff_infinitelyMany,
    ← EventSystem.not_eventuallySilent_iff_infinitelyMany,
    eventuallySilent_iff f source target hstart hrows howner]

end Shared.Beeping.NPcoNP.CoalescingAlgebra
