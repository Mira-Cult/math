import Shared.Beeping.NPcoNP.Source284SerializerStripWindow

/-! State relocation adds a fixed offset only to nonzero states. It reflects
finite tape windows as well as preserving them. -/
namespace Shared.Beeping.NPcoNP.Source284UnliftWindow

open Shared.Beeping.NPcoNP.Source284Relative (Window)
open Shared.Beeping.NPcoNP.Source284SourceRelocation (lift)

theorem window_reflect (k d : Nat) (a b : Source284Relative.Config)
    (h : Window k (lift d a) (lift d b)) : Window k a b := by
  rcases a with ⟨al,ar,as⟩
  rcases b with ⟨bl,br,bs⟩
  rcases h with ⟨hs,hl,hr⟩
  refine ⟨?_,hl,hr⟩
  change (if as = 0 then 0 else as+2*d) = (if bs = 0 then 0 else bs+2*d) at hs
  by_cases ha : as = 0 <;> by_cases hb : bs = 0 <;> simp [ha,hb] at hs ⊢ <;> omega

end Shared.Beeping.NPcoNP.Source284UnliftWindow
