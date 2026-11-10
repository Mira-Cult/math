import PASoundness.PAtoCompactGuardedBridge
import PASoundness.PAtoCompactEmptyDomain
import PASoundness.PAtoCompactFormulaTranslation
import PASoundness.CompactNamed
import PASoundness.PAtoCompactAlphaMapOne

set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-! Finite K proof ingredients for eliminating a candidate guard. Every
vacuity and inhabitation condition is displayed in the relevant interface;
this is not the unrestricted guarded modus-ponens transformer. -/

namespace PASoundness.PAtoCompactGuardElimination

open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.CompactNamed PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactFormulaTranslation
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactZeroExistence
open PASoundness.PAtoCompactEmptyDomain

theorem mapNames_compose (f g : Nat → Nat) (a : Formula) :
    mapNames f (mapNames g a) = mapNames (f ∘ g) a := by
  induction a with
  | truth | bottom | member | equal => rfl
  | imp a b ia ib => simp [mapNames, ia, ib]
  | all x a ih | ex x a ih => simp [mapNames, ih, Function.comp_def]

theorem one_not_domain_binder (base : Nat) : 1 ∉ (domainAt base 1).binders := by
  intro h
  have hh := oneMap_private (domainTemplate 0) base 0 1
    templates_inputs_unbound.1 templates_names_bounded.1 1 h
  omega

theorem target_not_domain_names (base x : Nat) (hx : x < base + 2) (h1 : x ≠ 1) :
    x ∉ (domainAt base 1).names := by
  intro h
  rw [domainAt, mapNames_names] at h
  obtain ⟨z, _, hz⟩ := Finset.mem_image.mp h
  by_cases hzero : z = 0
  · simp [oneMap, hzero] at hz
    exact h1 hz.symm
  · simp [oneMap, hzero] at hz
    omega

theorem replace_domain_one (base x : Nat) :
    replace 1 x (domainAt base 1) = domainAt base x := by
  rw [← PAtoCompactAlphaMapOne.map_eq_replace 1 x (domainAt base 1)
    (one_not_domain_binder base)]
  unfold domainAt
  rw [mapNames_compose]
  congr 1
  funext z
  by_cases hzero : z = 0
  · simp [oneMap, rename, hzero]
  · have hne : base + 2 + z ≠ 1 := by omega
    simp [oneMap, rename, hzero, hne]

/-- A zero object witnesses candidate inhabitance for any generated private
binder block when its distinguished object variable is 1. -/
def candidate_at_one_exists (base : Nat) :
    KDerivation (existsCode 1 (domainAt base 1).encode) := by
  have hf : [1, base+40, base+32, base+33, base+34, base+35,
      base+36, base+37, base+38, base+39].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
      or_false, not_or, not_false_eq_true, List.nodup_nil, and_true]
    repeat' apply And.intro
    all_goals omega
  have hz := zero_candidate 1 (base+40) (base+32) (base+33) (base+34)
    (base+35) (base+36) (base+37) (base+38) (base+39) hf
  have h : KDerivation (imp (zeroCode 1 (base+40)) (domainAt base 1).encode) := by
    simpa only [domainAt_code, PAtoCompactCandidateExact.candidateCode] using hz
  exact .mp (zero_graph_exists (base+40) (by omega)) (existsCongr 1 h)

/-- The candidate predicate used by the generated translation is inhabited
for any source name below its private binder block. -/
def candidate_exists (base x : Nat) (hx : x < base + 2) :
    KDerivation (existsCode x (domainAt base x).encode) := by
  by_cases he : x = 1
  · subst x
    exact candidate_at_one_exists base
  · have h := (existentialAlpha 1 x (domainAt base 1) (Ne.symm he)
      (one_not_domain_binder base) (target_not_domain_names base x hx he)).1
    rw [replace_domain_one base x] at h
    exact .mp (candidate_at_one_exists base) h

/-- Remove an existentially inhabited guard while retaining a context guard.
Both vacuity proofs and the actual K proof of inhabitance are explicit. -/
def eliminate_guard (x a g b : Nat)
    (hvG : KDerivation (imp g (allCode x g)))
    (hvB : KDerivation (imp b (allCode x b)))
    (he : KDerivation (existsCode x a))
    (d : KDerivation (imp g (imp a b))) : KDerivation (imp g b) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.existsElim hvB
  · apply generalizeOne x hvG
    exact .mp (Context.head [] g) (.closed d)
  · exact .closed he

/-- Specialization to the literal candidate predicate. -/
def eliminate_candidate (x base g b : Nat)
    (hvG : KDerivation (imp g (allCode x g)))
    (hvB : KDerivation (imp b (allCode x b)))
    (he : KDerivation (existsCode x (domainAt base x).encode))
    (d : KDerivation (imp g (imp (domainAt base x).encode b))) :
    KDerivation (imp g b) :=
  eliminate_guard x _ g b hvG hvB he d

/-- A fresh candidate variable can be eliminated using the constructed zero
witness. The vacuity proofs are still explicit K proof-data inputs. -/
def eliminate_fresh_candidate (x base g b : Nat) (hx : x < base + 2)
    (hvG : KDerivation (imp g (allCode x g)))
    (hvB : KDerivation (imp b (allCode x b)))
    (d : KDerivation (imp g (imp (domainAt base x).encode b))) :
    KDerivation (imp g b) :=
  eliminate_candidate x base g b hvG hvB (candidate_exists base x hx) d

end PASoundness.PAtoCompactGuardElimination

#print axioms PASoundness.PAtoCompactGuardElimination.eliminate_guard
#print axioms PASoundness.PAtoCompactGuardElimination.eliminate_candidate
#print axioms PASoundness.PAtoCompactGuardElimination.candidate_at_one_exists
#print axioms PASoundness.PAtoCompactGuardElimination.candidate_exists
#print axioms PASoundness.PAtoCompactGuardElimination.eliminate_fresh_candidate
