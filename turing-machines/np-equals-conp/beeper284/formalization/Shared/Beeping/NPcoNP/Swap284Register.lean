import Shared.Beeping.RegisterMachine
import Shared.Beeping.NPcoNP.Swap284Rank

/-! Conditional connection of the six-row local swap model to the shared
finite-register program semantics. The actual generated-row identities,
entry-zero condition, physical sharing and binary-tape refinement are not
established here. -/

namespace Shared.Beeping.NPcoNP.Swap284Register
open Shared.Beeping.NPcoNP.Swap284Steps
open PASoundness.RegisterMachine

abbrev Bank := PASoundness.RegisterMachine.Bank 12

def L : Fin 12 := ⟨8, by decide⟩
def R : Fin 12 := ⟨1, by decide⟩
def Q : Fin 12 := ⟨10, by decide⟩

structure Labels (n : Nat) where
  testL : Fin n
  incQ : Fin n
  testR : Fin n
  incL : Fin n
  testQ : Fin n
  incR : Fin n
  exit : Fin n

def Labels.at {n : Nat} (a : Labels n) : PC → Fin n
  | .testL => a.testL | .incQ => a.incQ | .testR => a.testR
  | .incL => a.incL | .testQ => a.testQ | .incR => a.incR | .exit => a.exit

/-- Explicit six equations required of a supplied register program. These
are hypotheses, not a claim that the producer grammar was decoded. -/
structure Rows {n : Nat} (p : Program 12 n) (a : Labels n) : Prop where
  testL : p.code[a.testL] = ⟨.decNZ L, a.incQ, a.testR⟩
  incQ : p.code[a.incQ] = ⟨.inc Q, a.testL, a.testL⟩
  testR : p.code[a.testR] = ⟨.decNZ R, a.incL, a.testQ⟩
  incL : p.code[a.incL] = ⟨.inc L, a.testR, a.testR⟩
  testQ : p.code[a.testQ] = ⟨.decNZ Q, a.incR, a.exit⟩
  incR : p.code[a.incR] = ⟨.inc R, a.testQ, a.testQ⟩

def bank (c : Swap284Steps.Config Bank) : Bank :=
  fun i => if i = L then c.left else if i = R then c.right
    else if i = Q then c.work else c.other i

def embed {n : Nat} (a : Labels n) (c : Swap284Steps.Config Bank) :
    PASoundness.RegisterMachine.Config 12 n := ⟨a.at c.pc, bank c⟩

theorem one_step {n : Nat} (p : Program 12 n) (a : Labels n)
    (h : Rows p a) (c : Swap284Steps.Config Bank) (hc : c.pc ≠ .exit) :
    p.system.step (embed a c) = (embed a (Swap284Steps.step c), []) := by
  rcases c with ⟨pc,l,r,q,o⟩
  rcases h with ⟨h0,h1,h2,h3,h4,h5⟩
  cases pc <;> cases l <;> cases r <;> cases q <;>
    simp_all [embed, bank, Labels.at, Program.system,
      Swap284Steps.step, execute, write, L, R, Q, funext_iff]
  all_goals
    intro x
    by_cases h8 : x = (8 : Fin 12) <;> by_cases h1 : x = (1 : Fin 12) <;>
      by_cases h10 : x = (10 : Fin 12) <;> simp_all

/-- Each step before local exit agrees with the register program and emits
no output. The rank bounds the whole segment and excludes an infinite stall. -/
theorem segment {n : Nat} (p : Program 12 n) (a : Labels n)
    (h : Rows p a) (c : Swap284Steps.Config Bank) (k : Nat)
    (hk : k ≤ Swap284Steps.rank c) :
    p.system.advance (embed a c) k = embed a ((Swap284Steps.step^[k]) c) ∧
    p.system.wordFrom (embed a c) k = [] := by
  induction k with
  | zero => simp [PASoundness.WordEventSystem.advance, PASoundness.WordEventSystem.wordFrom]
  | succ k ih =>
    obtain ⟨ha, hw⟩ := ih (by omega)
    have hr := Swap284Steps.rank_iter c k
    have hne : ((Swap284Steps.step^[k]) c).pc ≠ .exit := by
      intro hx
      have hz : Swap284Steps.rank ((Swap284Steps.step^[k]) c) = 0 := by
        simp [Swap284Steps.rank, hx]
      omega
    have hs := one_step p a h ((Swap284Steps.step^[k]) c) hne
    constructor
    · simp [PASoundness.WordEventSystem.advance, ha, hs, Function.iterate_succ_apply']
    · simp [PASoundness.WordEventSystem.wordFrom, hw, ha, hs]

/-- Conditional whole-swap segment, preserving the untouched bank values and
producing the empty event word. -/
theorem swap_segment {n : Nat} (p : Program 12 n) (a : Labels n)
    (h : Rows p a) (l r : Nat) (other : Bank) :
    let c := cfg .testL l r 0 other
    let k := 4*l+2*r+3
    p.system.advance (embed a c) k = embed a (cfg .exit r l 0 other) ∧
    p.system.wordFrom (embed a c) k = [] ∧ 0 < k := by
  have hs := segment p a h (cfg .testL l r 0 other) (4*l+2*r+3)
    (by simp [Swap284Steps.rank, cfg])
  constructor
  · simpa [Swap284Steps.swap_run] using hs.1
  constructor
  · exact hs.2
  · omega

theorem bank_other (c : Swap284Steps.Config Bank) (i : Fin 12)
    (hl : i ≠ L) (hr : i ≠ R) (hq : i ≠ Q) : bank c i = c.other i := by
  simp [bank, hl, hr, hq]

theorem bank_roundtrip (b : Bank) (h : b Q = 0) :
    bank (cfg .testL (b L) (b R) 0 b) = b := by
  funext i
  by_cases hl : i = L
  · subst i; simp [bank, cfg]
  by_cases hr : i = R
  · subst i; simp [bank, cfg, L, R, Q]
  by_cases hq : i = Q
  · subst i
    simpa [bank, cfg, L, R, Q] using h.symm
  simp [bank, cfg, hl, hr, hq]

/-- The same conditional segment from an arbitrary register bank with zero
work. Every register outside the three named carriers is preserved. -/
theorem swap_from_bank {n : Nat} (p : Program 12 n) (a : Labels n)
    (h : Rows p a) (b : Bank) (hz : b Q = 0) :
    let k := 4*(b L)+2*(b R)+3
    let out := p.system.advance ⟨a.testL,b⟩ k
    out.state = a.exit ∧ out.bank L = b R ∧ out.bank R = b L ∧ out.bank Q = 0 ∧
    (∀ i, i ≠ L → i ≠ R → i ≠ Q → out.bank i = b i) ∧
    p.system.wordFrom ⟨a.testL,b⟩ k = [] ∧ 0 < k := by
  have hs := swap_segment p a h (b L) (b R) b
  have he : embed a (cfg .testL (b L) (b R) 0 b) = ⟨a.testL,b⟩ := by
    change (⟨a.testL, bank (cfg .testL (b L) (b R) 0 b)⟩ :
      PASoundness.RegisterMachine.Config 12 n) = ⟨a.testL, b⟩
    rw [bank_roundtrip b hz]
  dsimp only at hs
  rw [he] at hs
  rcases hs with ⟨ha, hw, hp⟩
  simp only [ha, embed, Labels.at, bank, cfg] at *
  refine ⟨by simp, by simp [L, R, Q], by simp [L, R, Q],
    by simp [L, R, Q], ?_, hw, hp⟩
  intro i h8 h1 h10
  simp [h8,h1,h10]

end Shared.Beeping.NPcoNP.Swap284Register
