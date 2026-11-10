import PASoundness.PAtoCompactSuccTermTotality
import PASoundness.PAtoCompactScopedVacuity
import PASoundness.PAtoCompactAllTermTransport

/-! Reduction of successor term-graph functionality to child functionality
and quotient-successor compatibility. The first constructor takes explicit
vacuity proofs; later constructors derive them from freshness. The two K
implications remain inputs, not established compatibility theorems. -/
namespace PASoundness.PAtoCompactSuccessorGraphFunctionalityConditional

open FirstOrder FirstOrder.Language
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactFreeNames PASoundness.PAtoCompactFreeVacuity
open PASoundness.PAtoCompactScopedVacuity
open PASoundness.PAtoCompactAllTermTransport

set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- If the two explicit child witnesses are equivalent, a supplied finite K
compatibility proof for the quotient-successor relation makes the successor
outputs equivalent. The conclusion eliminates the two child witnesses; all
vacuity proofs needed to do so remain explicit. -/
def successor_functionality {α : Type} (v : α → Nat) (t : Peano.language.Term α)
    (b c p q e f : Nat) (g : Formula)
    (child : KDerivation (imp g.encode
      (imp (termGraph v t b (b+64)).encode
        (imp (termGraph v t c (c+64)).encode (equivAt e b c).encode))))
    (next : KDerivation (imp g.encode
      (imp (equivAt e b c).encode (imp (succAt b b p).encode
        (imp (succAt c c q).encode (equivAt f p q).encode)))))
    (vgb : KDerivation (imp g.encode (allCode b g.encode)))
    (vgc : KDerivation (imp g.encode (allCode c g.encode)))
    (vg1b : KDerivation (imp (termGraph v (.func .succ ![t]) p b).encode
      (allCode b (termGraph v (.func .succ ![t]) p b).encode)))
    (vg2b : KDerivation (imp (termGraph v (.func .succ ![t]) q c).encode
      (allCode b (termGraph v (.func .succ ![t]) q c).encode)))
    (vg1c : KDerivation (imp (termGraph v (.func .succ ![t]) p b).encode
      (allCode c (termGraph v (.func .succ ![t]) p b).encode)))
    (vg2c : KDerivation (imp (termGraph v (.func .succ ![t]) q c).encode
      (allCode c (termGraph v (.func .succ ![t]) q c).encode)))
    (vbody1c : KDerivation (imp (andF (termGraph v t b (b+64)) (succAt b b p)).encode
      (allCode c (andF (termGraph v t b (b+64)) (succAt b b p)).encode)))
    (veb : KDerivation (imp (equivAt f p q).encode (allCode b (equivAt f p q).encode)))
    (vec : KDerivation (imp (equivAt f p q).encode (allCode c (equivAt f p q).encode))) :
    KDerivation (imp g.encode
      (imp (termGraph v (.func .succ ![t]) p b).encode
        (imp (termGraph v (.func .succ ![t]) q c).encode (equivAt f p q).encode))) := by
  let A := (termGraph v (.func .succ ![t]) p b).encode
  let B := (termGraph v (.func .succ ![t]) q c).encode
  let C := (andF (termGraph v t b (b+64)) (succAt b b p)).encode
  let D := (andF (termGraph v t c (c+64)) (succAt c c q)).encode
  let E := (equivAt f p q).encode
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [B,A,g.encode]
  have hA : Context Γ A := .hypothesis (by simp [Γ])
  have hB : Context Γ B := .head _ _
  have hExA : Context Γ (existsCode b C) := Context.conjunctionRight hA
  apply Context.existsElim veb _ hExA
  apply Context.generalize b
  · intro n hn
    change n ∈ [B,A,g.encode] at hn
    by_cases h : n = B
    · subst n; exact vg2b
    · by_cases h' : n = A
      · subst n; exact vg1b
      · have h'' : n = g.encode := by simpa [h, h'] using hn
        subst n; exact vgb
  apply Context.deduction
  let Δ := [C,B,A,g.encode]
  have hC : Context Δ C := .head _ _
  have hB' : Context Δ B := .hypothesis (by simp [Δ])
  have hExB : Context Δ (existsCode c D) := Context.conjunctionRight hB'
  apply Context.existsElim vec _ hExB
  apply Context.generalize c
  · intro n hn
    change n ∈ [C,B,A,g.encode] at hn
    by_cases h : n = C
    · subst n; exact vbody1c
    · by_cases h' : n = B
      · subst n; exact vg2c
      · by_cases h'' : n = A
        · subst n; exact vg1c
        · have hlast : n = g.encode := by simpa [h, h', h''] using hn
          subst n; exact vgc
  apply Context.deduction
  let Θ := [D,C,B,A,g.encode]
  have hD : Context Θ D := .head _ _
  have hC' : Context Θ C := .hypothesis (by simp [Θ])
  have hg : Context Θ g.encode := .hypothesis (by simp [Θ])
  have hc1 : Context Θ (termGraph v t b (b+64)).encode := Context.conjunctionLeft hC'
  have hs1 : Context Θ (succAt b b p).encode := Context.conjunctionRight hC'
  have hc2 : Context Θ (termGraph v t c (c+64)).encode := Context.conjunctionLeft hD
  have hs2 : Context Θ (succAt c c q).encode := Context.conjunctionRight hD
  have he : Context Θ (equivAt e b c).encode := .mp hc2 (.mp hc1 (.mp hg (.closed child)))
  exact .mp hs2 (.mp hs1 (.mp he (.mp hg (.closed next))))

/-- As above, but all vacuity proofs are constructed from explicit freshness
and name bounds. The child and quotient-successor implications remain inputs. -/
def successor_functionality_fresh {α : Type} [DecidableEq α]
    (v : α → Nat) (t : Peano.language.Term α)
    (b c p q e f : Nat) (g : Formula)
    (hbc : b < c) (hp : p < b) (hq : q < b)
    (hv : ∀ a ∈ t.varFinset, v a < b)
    (hgb : b ∉ g.free) (hgc : c ∉ g.free)
    (child : KDerivation (imp g.encode
      (imp (termGraph v t b (b+64)).encode
        (imp (termGraph v t c (c+64)).encode (equivAt e b c).encode))))
    (next : KDerivation (imp g.encode
      (imp (equivAt e b c).encode (imp (succAt b b p).encode
        (imp (succAt c c q).encode (equivAt f p q).encode))))) :
    KDerivation (imp g.encode
      (imp (termGraph v (.func .succ ![t]) p b).encode
        (imp (termGraph v (.func .succ ![t]) q c).encode (equivAt f p q).encode))) := by
  let s : Peano.language.Term α := .func .succ ![t]
  have hs : s.varFinset = t.varFinset := by simp [s, Term.varFinset]
  have hvb : ∀ a ∈ s.varFinset, b ≠ v a := by
    intro a ha
    have h := hv a (hs ▸ ha)
    omega
  have hvc : ∀ a ∈ s.varFinset, c ≠ v a := by
    intro a ha
    have h := hv a (hs ▸ ha)
    omega
  have hbody : c ∉ (andF (termGraph v t b (b+64)) (succAt b b p)).free := by
    intro hc
    rw [andF_free, Finset.mem_union] at hc
    rcases hc with hc | hc
    · have hh := termGraph_free_subset v t b (b+64) hc
      rcases Finset.mem_union.mp hh with hh | hh
      · obtain ⟨a, ha, he⟩ := Finset.mem_image.mp hh
        have h := hv a ha
        omega
      · have hh := Finset.mem_singleton.mp hh
        omega
    · have hh := succAt_free b b p hc
      simp only [Finset.mem_insert, Finset.mem_singleton] at hh
      omega
  have heb : b ∉ (equivAt f p q).free := by
    intro h
    have hh := equivAt_free f p q h
    simp only [Finset.mem_insert, Finset.mem_singleton] at hh
    omega
  have hec : c ∉ (equivAt f p q).free := by
    intro h
    have hh := equivAt_free f p q h
    simp only [Finset.mem_insert, Finset.mem_singleton] at hh
    omega
  exact successor_functionality v t b c p q e f g child next
    (free_vacuity b g hgb) (free_vacuity c g hgc)
    (termGraph_vacuity v s p b b (by omega) hvb)
    (termGraph_vacuity v s q c b (by omega) hvb)
    (termGraph_vacuity v s p b c (by omega) hvc)
    (termGraph_vacuity v s q c c (by omega) hvc)
    (free_vacuity c _ hbody) (free_vacuity b _ heb) (free_vacuity c _ hec)

/-- The same conditional functionality implication at a common graph base.
An explicitly fresh second allocator is used only to expose distinct
existential child witnesses. -/
noncomputable def successor_functionality_same_base {α : Type} [DecidableEq α]
    (v : α → Nat) (t : Peano.language.Term α)
    (b c p q e f : Nat) (g : Formula)
    (hbc : b < c) (hp : p < b) (hq : q < b)
    (hv : ∀ a ∈ t.varFinset, v a < b)
    (hgb : b ∉ g.free) (hgc : c ∉ g.free)
    (child : KDerivation (imp g.encode
      (imp (termGraph v t b (b+64)).encode
        (imp (termGraph v t c (c+64)).encode (equivAt e b c).encode))))
    (next : KDerivation (imp g.encode
      (imp (equivAt e b c).encode (imp (succAt b b p).encode
        (imp (succAt c c q).encode (equivAt f p q).encode))))) :
    KDerivation (imp g.encode
      (imp (termGraph v (.func .succ ![t]) p b).encode
        (imp (termGraph v (.func .succ ![t]) q b).encode (equivAt f p q).encode))) := by
  let s : Peano.language.Term α := .func .succ ![t]
  have hs : s.varFinset = t.varFinset := by simp [s, Term.varFinset]
  have hvb : ∀ a ∈ s.varFinset, v a < b := by
    intro a ha
    exact hv a (hs ▸ ha)
  have hvc : ∀ a ∈ s.varFinset, v a < c := by
    intro a ha
    have h := hvb a ha
    omega
  have ht := (termGraph_base_transport v s b c q hq (by omega) hvb hvc).1
  have h := successor_functionality_fresh v t b c p q e f g hbc hp hq hv hgb hgc child next
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [(termGraph v s q b).encode, (termGraph v s p b).encode, g.encode]
  have hg : Context Γ g.encode := .hypothesis (by simp [Γ])
  have hp' : Context Γ (termGraph v s p b).encode := .hypothesis (by simp [Γ])
  have hq' : Context Γ (termGraph v s q b).encode := .head _ _
  exact .mp (.mp hq' (.closed ht)) (.mp hp' (.mp hg (.closed h)))

end PASoundness.PAtoCompactSuccessorGraphFunctionalityConditional

#print axioms PASoundness.PAtoCompactSuccessorGraphFunctionalityConditional.successor_functionality
#print axioms PASoundness.PAtoCompactSuccessorGraphFunctionalityConditional.successor_functionality_fresh
#print axioms PASoundness.PAtoCompactSuccessorGraphFunctionalityConditional.successor_functionality_same_base
