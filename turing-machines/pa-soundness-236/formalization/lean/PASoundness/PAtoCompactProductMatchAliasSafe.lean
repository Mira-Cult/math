import PASoundness.PAtoCompactProductMatchInstantiateName
import PASoundness.PAtoCompactEquivStepsSyntax

/-! Stage all six product-congruence labels through fresh placeholders.
The six final labels may coincide in any pattern. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductMatchAliasSafe

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactEquivStepsSyntax
open PASoundness.PAtoCompactProductMatchInstantiateName PASoundness.PAtoCompactProductMatchDomainCongruence

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Sequentially instantiate a frame with names below its private block. -/
def instantiate_steps (b : Nat) : (steps : List (Nat × Nat)) →
    (∀ p ∈ steps, p.1 < b ∧ p.2 < b + 2) →
    (x y z u v w : Nat) → KDerivation (frame b x y z u v w).encode →
      KDerivation (frame b (applySteps steps x) (applySteps steps y) (applySteps steps z)
        (applySteps steps u) (applySteps steps v) (applySteps steps w)).encode
  | [], _, _, _, _, _, _, _, h => h
  | (r,s) :: rest, safe, x, y, z, u, v, w, h => by
    have hrs := safe (r,s) (by simp)
    have htail : ∀ p ∈ rest, p.1 < b ∧ p.2 < b + 2 := by
      intro p hp
      exact safe p (by simp [hp])
    have hnext := instantiate_name b x y z u v w r s hrs.1 hrs.2 h
    exact instantiate_steps b rest htail (rename r s x) (rename r s y) (rename r s z)
      (rename r s u) (rename r s v) (rename r s w) hnext

def placeholder (x y z u v w : Nat) : Nat := x + y + z + u + v + w + 50
def chosenBase (x y z u v w : Nat) : Nat := placeholder x y z u v w + 50
def fixedStages (p : Nat) : List (Nat × Nat) :=
  [(0,p),(1,p+1),(2,p+2),(42,p+3),(43,p+4),(44,p+5)]
def finalStages (p x y z u v w : Nat) : List (Nat × Nat) :=
  [(p,x),(p+1,y),(p+2,z),(p+3,u),(p+4,v),(p+5,w)]
def stages (x y z u v w : Nat) : List (Nat × Nat) :=
  let p := placeholder x y z u v w
  fixedStages p ++ finalStages p x y z u v w

theorem applySteps_append (left right : List (Nat × Nat)) (a : Nat) :
    applySteps (left ++ right) a = applySteps right (applySteps left a) := by
  induction left generalizing a with
  | nil => rfl
  | cons p rest ih =>
    cases p with
    | mk x y => simpa [applySteps] using ih (rename x y a)

theorem stages_safe (x y z u v w : Nat) :
    ∀ q ∈ stages x y z u v w, q.1 < chosenBase x y z u v w ∧
      q.2 < chosenBase x y z u v w + 2 := by
  intro q hq
  simp only [stages, fixedStages, finalStages, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [chosenBase, placeholder] <;> omega

theorem stages_values (x y z u v w : Nat) :
    applySteps (stages x y z u v w) 0 = x ∧
    applySteps (stages x y z u v w) 1 = y ∧
    applySteps (stages x y z u v w) 2 = z ∧
    applySteps (stages x y z u v w) 42 = u ∧
    applySteps (stages x y z u v w) 43 = v ∧
    applySteps (stages x y z u v w) 44 = w := by
  let p := placeholder x y z u v w
  have hp : 44 < p := by dsimp [p, placeholder]; omega
  have hx : x < p := by dsimp [p, placeholder]; omega
  have hy : y < p := by dsimp [p, placeholder]; omega
  have hz : z < p := by dsimp [p, placeholder]; omega
  have hu : u < p := by dsimp [p, placeholder]; omega
  have hv : v < p := by dsimp [p, placeholder]; omega
  have hw : w < p := by dsimp [p, placeholder]; omega
  have hf : applySteps (fixedStages p) 0 = p ∧
      applySteps (fixedStages p) 1 = p+1 ∧ applySteps (fixedStages p) 2 = p+2 ∧
      applySteps (fixedStages p) 42 = p+3 ∧ applySteps (fixedStages p) 43 = p+4 ∧
      applySteps (fixedStages p) 44 = p+5 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals
      apply applySteps_hit
      · simp [fixedStages]
      · intro k hk
        simpa [fixedStages] using hk
      · rintro ⟨a,b⟩ h
        simp only [fixedStages, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
        rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
          simp only <;> omega
  have hl : applySteps (finalStages p x y z u v w) p = x ∧
      applySteps (finalStages p x y z u v w) (p+1) = y ∧
      applySteps (finalStages p x y z u v w) (p+2) = z ∧
      applySteps (finalStages p x y z u v w) (p+3) = u ∧
      applySteps (finalStages p x y z u v w) (p+4) = v ∧
      applySteps (finalStages p x y z u v w) (p+5) = w := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals
      apply applySteps_hit
      · simp [finalStages]
      · intro k hk
        simpa (disch := omega) [finalStages] using hk
      · rintro ⟨a,b⟩ h
        simp only [finalStages, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
        rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
          simp only <;> omega
  rcases hf with ⟨hf0,hf1,hf2,hf42,hf43,hf44⟩
  change applySteps (fixedStages p ++ finalStages p x y z u v w) 0 = x ∧
    applySteps (fixedStages p ++ finalStages p x y z u v w) 1 = y ∧
    applySteps (fixedStages p ++ finalStages p x y z u v w) 2 = z ∧
    applySteps (fixedStages p ++ finalStages p x y z u v w) 42 = u ∧
    applySteps (fixedStages p ++ finalStages p x y z u v w) 43 = v ∧
    applySteps (fixedStages p ++ finalStages p x y z u v w) 44 = w
  simpa only [applySteps_append, hf0, hf1, hf2, hf42, hf43, hf44] using hl

/-- Arbitrary syntactic labels, including aliases, admit the same guarded
product congruence at a fresh common allocator chosen from those labels. -/
noncomputable def alias_safe_congruence (x y z u v w : Nat) :
    KDerivation (frame (chosenBase x y z u v w) x y z u v w).encode := by
  let b := chosenBase x y z u v w
  have hb : 44 < b + 2 := by dsimp [b, chosenBase, placeholder]; omega
  have h0 : KDerivation (frame b 0 1 2 42 43 44).encode := by
    simpa [frame, Formula.encode] using domain_product_congruence b hb
  have h := instantiate_steps b (stages x y z u v w) (stages_safe x y z u v w)
    0 1 2 42 43 44 h0
  rcases stages_values x y z u v w with ⟨h0',h1',h2',h42',h43',h44'⟩
  simpa [b, h0', h1', h2', h42', h43', h44'] using h

theorem alias_safe_congruence_certificate (x y z u v w : Nat) :
    theoremCode (certificate (alias_safe_congruence x y z u v w)) =
      (frame (chosenBase x y z u v w) x y z u v w).encode := certificate_correct _

end PASoundness.PAtoCompactProductMatchAliasSafe

#print axioms PASoundness.PAtoCompactProductMatchAliasSafe.instantiate_steps
#print axioms PASoundness.PAtoCompactProductMatchAliasSafe.alias_safe_congruence
#print axioms PASoundness.PAtoCompactProductMatchAliasSafe.alias_safe_congruence_certificate
