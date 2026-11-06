import Shared.Beeping.NPcoNP.Swap284FirstExit

/-! Conditional instances for two seven-label candidate site mappings.
The six `Rows` equations and zero-work entry remain explicit hypotheses;
this module does not claim that either mapping is the generated grammar. -/

namespace Shared.Beeping.NPcoNP.Swap284Sites
open Shared.Beeping.NPcoNP.Swap284Register
open PASoundness.RegisterMachine

/-- Candidate mapping for the first retained six-row swap and its exit. -/
def site71 : Labels 185 :=
  ⟨⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩,
   ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩⟩

/-- Candidate mapping for the second retained six-row swap and its exit. -/
def site162 : Labels 185 :=
  ⟨⟨162, by decide⟩, ⟨163, by decide⟩, ⟨164, by decide⟩,
   ⟨165, by decide⟩, ⟨166, by decide⟩, ⟨167, by decide⟩, ⟨168, by decide⟩⟩

theorem site71_separated : ExitSeparated site71 := by
  intro pc hpc
  cases pc <;> simp_all [ExitSeparated, Labels.at, site71]

theorem site162_separated : ExitSeparated site162 := by
  intro pc hpc
  cases pc <;> simp_all [ExitSeparated, Labels.at, site162]

/-- Exact first-exit, full-bank preservation, and silent event word for a
site with established row equations and an externally zero work register. -/
def SiteResult (p : Program 12 185) (a : Labels 185) (b : Bank) : Prop :=
  let k := 4*(b L)+2*(b R)+3
  let out := p.system.advance ⟨a.testL,b⟩ k
  0 < k ∧ out.state = a.exit ∧
  (∀ t < k, (p.system.advance ⟨a.testL,b⟩ t).state ≠ a.exit) ∧
  out.bank L = b R ∧ out.bank R = b L ∧ out.bank Q = 0 ∧
  (∀ i, i ≠ L → i ≠ R → i ≠ Q → out.bank i = b i) ∧
  p.system.wordFrom ⟨a.testL,b⟩ k = []

theorem site_correct (p : Program 12 185) (a : Labels 185)
    (hrows : Rows p a) (hsep : ExitSeparated a) (b : Bank) (hz : b Q = 0) :
    SiteResult p a b := by
  have hfirst := register_first_exit p a hrows hsep b hz
  have hswap := swap_from_bank p a hrows b hz
  dsimp [SiteResult] at *
  exact ⟨hfirst.1, hfirst.2.1, hfirst.2.2, hswap.2.1, hswap.2.2.1,
    hswap.2.2.2.1, hswap.2.2.2.2.1, hswap.2.2.2.2.2.1⟩

theorem site71_correct (p : Program 12 185) (hrows : Rows p site71)
    (b : Bank) (hz : b Q = 0) : SiteResult p site71 b :=
  site_correct p site71 hrows site71_separated b hz

theorem site162_correct (p : Program 12 185) (hrows : Rows p site162)
    (b : Bank) (hz : b Q = 0) : SiteResult p site162 b :=
  site_correct p site162 hrows site162_separated b hz

end Shared.Beeping.NPcoNP.Swap284Sites
