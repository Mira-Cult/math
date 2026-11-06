import Shared.Beeping.NPcoNP.Swap284Register

/-! A first-exit theorem for the conditional register-level swap segment.
The explicit label-separation hypothesis has not been checked against the
producer's generated grammar or physical table. -/

namespace Shared.Beeping.NPcoNP.Swap284Register
open Shared.Beeping.NPcoNP.Swap284Steps
open PASoundness.RegisterMachine

/-- The exit label differs from every active local program counter. -/
def ExitSeparated {n : Nat} (a : Labels n) : Prop :=
  ∀ pc, pc ≠ .exit → a.at pc ≠ a.exit

/-- From a zero-work entry, the register program cannot visit its designated
exit label before the claimed exact number of retained primitive steps. -/
theorem register_no_early_exit {n : Nat} (p : Program 12 n) (a : Labels n)
    (hrows : Rows p a) (hsep : ExitSeparated a) (b : Bank) (hz : b Q = 0)
    (t : Nat) (ht : t < 4*(b L)+2*(b R)+3) :
    (p.system.advance ⟨a.testL,b⟩ t).state ≠ a.exit := by
  let c := cfg .testL (b L) (b R) 0 b
  have hentry : embed a c = ⟨a.testL,b⟩ := by
    change (⟨a.testL, bank (cfg .testL (b L) (b R) 0 b)⟩ :
      PASoundness.RegisterMachine.Config 12 n) = ⟨a.testL,b⟩
    rw [bank_roundtrip b hz]
  have ht' : t ≤ rank c := by
    dsimp [c, rank, cfg]
    omega
  have hsegment := (segment p a hrows c t ht').1
  rw [hentry] at hsegment
  have hne : ((Swap284Steps.step^[t]) c).pc ≠ .exit := by
    exact swap_no_early_exit (b L) (b R) t b ht
  have hlabel := hsep _ hne
  rw [hsegment]
  exact hlabel

/-- With separation, the end label is reached for the first time at the
positive exact primitive count. The full-bank and no-event conclusions at
that time are provided separately by `swap_from_bank`. -/
theorem register_first_exit {n : Nat} (p : Program 12 n) (a : Labels n)
    (hrows : Rows p a) (hsep : ExitSeparated a) (b : Bank) (hz : b Q = 0) :
    let k := 4*(b L)+2*(b R)+3
    0 < k ∧
    (p.system.advance ⟨a.testL,b⟩ k).state = a.exit ∧
    ∀ t < k, (p.system.advance ⟨a.testL,b⟩ t).state ≠ a.exit := by
  dsimp only
  have hrun := swap_from_bank p a hrows b hz
  exact ⟨hrun.2.2.2.2.2.2, hrun.1,
    fun t ht => register_no_early_exit p a hrows hsep b hz t ht⟩

end Shared.Beeping.NPcoNP.Swap284Register
