import PASoundness.PAtoCompactGuardedAllImp
import PASoundness.PAtoCompactGuardedEqualityReflexivity
import PASoundness.PAtoCompactFreeVacuity
import PASoundness.CompactFreshen
import PASoundness.CompactQuantifiers

set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-! Capture-safe K instantiation and a conditional guarded PA universal
elimination constructor. Term-graph existence and substitution compatibility
are explicit per-instance K proof inputs. In particular, graph existence is
not postulated uniformly when the substituted variable is absent: then the
term's free names need not be covered by the axiom guard. -/
namespace PASoundness.PAtoCompactGuardedAllElim

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactFormulaTranslation
open PASoundness.PAtoCompactGuardedBridge PASoundness.PAtoCompactGuardedAllImp
open PASoundness.PAtoCompactGuardedAllImpAlignment PASoundness.PAtoCompactFreeVacuity
open PASoundness.PAtoCompactGuardedGeneralizationAlignment

/-- A binder fresh for both the generated scope and the witness label. -/
def instanceBinder (φ : Peano.Formula) (x q : Nat) : Nat :=
  max (universalCeiling φ x) q + 1

def instanceScope (φ : Peano.Formula) (x q : Nat) : Formula :=
  let z := instanceBinder φ x q
  .imp (domainAt (z+1) z) (bodyAt x φ z)

def instanceStart (φ : Peano.Formula) (x q : Nat) : Nat :=
  max ((instanceScope φ x q).names.sup id) (max (instanceBinder φ x q) q) + 1

theorem names_lt_instanceStart (φ : Peano.Formula) (x q : Nat) :
    ∀ v ∈ (instanceScope φ x q).names, v < instanceStart φ x q := by
  intro v hv
  have hle : v ≤ (instanceScope φ x q).names.sup id := Finset.le_sup (f := id) hv
  unfold instanceStart
  omega

/-- The literal named output of capture-safe instantiation at `q`. -/
def instanceBody (φ : Peano.Formula) (x q : Nat) : Formula :=
  replace (instanceBinder φ x q) q
    (freshen (instanceScope φ x q) (instanceStart φ x q) (names_lt_instanceStart φ x q)).formula

/-- An actual finite K proof instantiates the translated universal at any
selected name, even if the source formula or its generated binders use that
name. Freshening is syntactic and does not use a soundness theorem. -/
noncomputable def universal_instance (φ : Peano.Formula) (x q : Nat) :
    KDerivation (imp (code (FOL.allAt x φ)) (instanceBody φ x q).encode) := by
  let z := instanceBinder φ x q
  let f := instanceScope φ x q
  let start := instanceStart φ x q
  let fresh := freshen f start (names_lt_instanceStart φ x q)
  have htop : topName x φ < z := by
    have hh := ceiling_top φ x
    dsimp [z, instanceBinder]
    omega
  have hz : z ∉ (originalChild φ x).names := by
    intro hz
    have hh := ceiling_child φ x z hz
    dsimp [z, instanceBinder] at hh
    omega
  have hqz : z ≠ q := by dsimp [z, instanceBinder]; omega
  have hzstart : z < start := by dsimp [start, z, instanceStart]; omega
  have hqstart : q < start := by dsimp [start, instanceStart]; omega
  have hzbind : z ∉ fresh.formula.binders := by
    intro h
    have hh := fresh.binders_ge z h
    omega
  have hqbind : q ∉ fresh.formula.binders := by
    intro h
    have hh := fresh.binders_ge q h
    omega
  have align := (align_at φ x z htop hz).1
  have hfresh := allCongr z fresh.equivalent.forward
  have hinst := universalInstance z q fresh.formula hqz hzbind hqbind
  change KDerivation (imp (formula (FOL.allAt x φ)).encode
    (replace z q fresh.formula).encode)
  exact compose align (compose hfresh hinst)

/-- A per-instance term graph and syntactic substitution bridge suffice for
the guarded PA universal-elimination leaf. All three absence hypotheses are
syntactic free-name conditions. `total` and `substitution` are actual finite
K proofs; neither is inferred from the standard-model truth theorem. -/
noncomputable def allElim_of_witness (φ : Peano.Formula) (x : Nat) (t : Peano.Term)
    (q : Nat) (graph : Formula)
    (hguard : q ∉ (guardFormula ((FOL.allAt x φ).imp (FOL.substAt φ x t))).free)
    (hall : q ∉ (formula (FOL.allAt x φ)).free)
    (htarget : q ∉ (formula (FOL.substAt φ x t)).free)
    (total : KDerivation (imp (guardFormula ((FOL.allAt x φ).imp (FOL.substAt φ x t))).encode
      (existsCode q graph.encode)))
    (substitution : KDerivation (imp (guardFormula ((FOL.allAt x φ).imp (FOL.substAt φ x t))).encode
      (imp graph.encode (imp (instanceBody φ x q).encode (code (FOL.substAt φ x t)))))) :
    KDerivation (guardedCode ((FOL.allAt x φ).imp (FOL.substAt φ x t))) := by
  let G := (guardFormula ((FOL.allAt x φ).imp (FOL.substAt φ x t))).encode
  let A := code (FOL.allAt x φ)
  let B := code (FOL.substAt φ x t)
  have hvG : KDerivation (imp G (allCode q G)) := free_vacuity q _ hguard
  have hvA : KDerivation (imp A (allCode q A)) := free_vacuity q _ hall
  have hvB : KDerivation (imp B (allCode q B)) := free_vacuity q _ htarget
  change KDerivation (imp G (imp A B))
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [A, G]
  have ha : Context Γ A := Context.head [G] A
  have hg : Context Γ G := .hypothesis (by simp [Γ])
  apply Context.existsElim hvB
  · apply Context.generalize q
    · intro h hh
      by_cases he : h = A
      · subst h
        exact hvA
      · have hg' : h = G := by simpa [Γ, he] using hh
        subst h
        exact hvG
    · apply Context.deduction
      let Δ := [graph.encode, A, G]
      have hgraph : Context Δ graph.encode := Context.head [A, G] _
      have hA : Context Δ A := .hypothesis (by simp [Δ])
      have hG : Context Δ G := .hypothesis (by simp [Δ])
      have hi : Context Δ (instanceBody φ x q).encode := .mp hA (.closed (universal_instance φ x q))
      exact .mp hi (.mp hgraph (.mp hG (.closed substitution)))
  · exact .mp hg (.closed total)

theorem allElim_of_witness_certificate (φ : Peano.Formula) (x : Nat) (t : Peano.Term)
    (q : Nat) (graph : Formula)
    (hguard : q ∉ (guardFormula ((FOL.allAt x φ).imp (FOL.substAt φ x t))).free)
    (hall : q ∉ (formula (FOL.allAt x φ)).free)
    (htarget : q ∉ (formula (FOL.substAt φ x t)).free)
    (total : KDerivation (imp (guardFormula ((FOL.allAt x φ).imp (FOL.substAt φ x t))).encode
      (existsCode q graph.encode)))
    (substitution : KDerivation (imp (guardFormula ((FOL.allAt x φ).imp (FOL.substAt φ x t))).encode
      (imp graph.encode (imp (instanceBody φ x q).encode (code (FOL.substAt φ x t)))))) :
    theoremCode (certificate (allElim_of_witness φ x t q graph hguard hall htarget total substitution)) =
      guardedCode ((FOL.allAt x φ).imp (FOL.substAt φ x t)) := certificate_correct _

/-- The actual PA leaf being constructed. -/
def allElimFormula (φ : Peano.Formula) (x : Nat) (t : Peano.Term) : Peano.Formula :=
  (FOL.allAt x φ).imp (FOL.substAt φ x t)

/-- When the substituted variable occurs in the source, every variable of
the term occurs in the axiom's free support. The absent-variable case has no
such guarantee and must not rely on uniform guarded term totality. -/
theorem termVars_in_axiom_of_occurs (φ : Peano.Formula) (x : Nat) (t : Peano.Term)
    (hx : x ∈ φ.freeVarFinset) : t.varFinset ⊆ (allElimFormula φ x t).freeVarFinset := by
  intro y hy
  have hs : y ∈ (FOL.substAt φ x t).freeVarFinset := by
    rw [FOL.substAt, PASoundness.SyntaxTransport.formula_subst_freeVars]
    exact ⟨x, hx, by simpa using hy⟩
  simp [allElimFormula, BoundedFormula.freeVarFinset, hs]

/-- When the replaced variable occurs, each free variable of the substituting
term has an actual K projection from the axiom's guard. This is only an input
to term totality, not a proof of totality for arbitrary terms. -/
def termVar_guard (φ : Peano.Formula) (x : Nat) (t : Peano.Term) (y : Nat)
    (hx : x ∈ φ.freeVarFinset) (hy : y ∈ t.varFinset) :
    KDerivation (imp (guardFormula (allElimFormula φ x t)).encode
      (domainAt (guardBase (allElimFormula φ x t)) y).encode) :=
  PASoundness.PAtoCompactGuardedEqualityReflexivity.guardFormula_projection
    (allElimFormula φ x t) y (termVars_in_axiom_of_occurs φ x t hx hy)

/-- A witness label outside the free support of the guard, translated
universal, and concrete substituted conclusion. -/
def witnessName (φ : Peano.Formula) (x : Nat) (t : Peano.Term) : Nat :=
  ((guardFormula (allElimFormula φ x t)).free ∪
    (formula (FOL.allAt x φ)).free ∪ (formula (FOL.substAt φ x t)).free).sup id + 1

theorem witnessName_guard_fresh (φ : Peano.Formula) (x : Nat) (t : Peano.Term) :
    witnessName φ x t ∉ (guardFormula (allElimFormula φ x t)).free := by
  intro h
  have hm : witnessName φ x t ≤
      ((guardFormula (allElimFormula φ x t)).free ∪
        (formula (FOL.allAt x φ)).free ∪ (formula (FOL.substAt φ x t)).free).sup id :=
    Finset.le_sup (f := id) (Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl h))))
  unfold witnessName at hm
  omega

theorem witnessName_all_fresh (φ : Peano.Formula) (x : Nat) (t : Peano.Term) :
    witnessName φ x t ∉ (formula (FOL.allAt x φ)).free := by
  intro h
  have hm : witnessName φ x t ≤
      ((guardFormula (allElimFormula φ x t)).free ∪
        (formula (FOL.allAt x φ)).free ∪ (formula (FOL.substAt φ x t)).free).sup id :=
    Finset.le_sup (f := id) (Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr h))))
  unfold witnessName at hm
  omega

theorem witnessName_target_fresh (φ : Peano.Formula) (x : Nat) (t : Peano.Term) :
    witnessName φ x t ∉ (formula (FOL.substAt φ x t)).free := by
  intro h
  have hm : witnessName φ x t ≤
      ((guardFormula (allElimFormula φ x t)).free ∪
        (formula (FOL.allAt x φ)).free ∪ (formula (FOL.substAt φ x t)).free).sup id :=
    Finset.le_sup (f := id) (Finset.mem_union.mpr (Or.inr h))
  unfold witnessName at hm
  omega

/-- Concrete PA-term graph specialization. Each leaf still requires its own
finite K graph-existence and substitution-compatibility proofs; in particular
this does not posit a false uniform totality principle for unused terms. -/
noncomputable def allElim_of_termGraph (φ : Peano.Formula) (x : Nat) (t : Peano.Term)
    (base : Nat)
    (total : KDerivation (imp (guardFormula (allElimFormula φ x t)).encode
      (existsCode (witnessName φ x t)
        (termGraph id t (witnessName φ x t) base).encode)))
    (substitution : KDerivation (imp (guardFormula (allElimFormula φ x t)).encode
      (imp (termGraph id t (witnessName φ x t) base).encode
        (imp (instanceBody φ x (witnessName φ x t)).encode (code (FOL.substAt φ x t)))))) :
    KDerivation (guardedCode (allElimFormula φ x t)) :=
  allElim_of_witness φ x t (witnessName φ x t)
    (termGraph id t (witnessName φ x t) base)
    (witnessName_guard_fresh φ x t) (witnessName_all_fresh φ x t)
    (witnessName_target_fresh φ x t) total substitution

theorem allElim_of_termGraph_certificate (φ : Peano.Formula) (x : Nat) (t : Peano.Term)
    (base : Nat)
    (total : KDerivation (imp (guardFormula (allElimFormula φ x t)).encode
      (existsCode (witnessName φ x t)
        (termGraph id t (witnessName φ x t) base).encode)))
    (substitution : KDerivation (imp (guardFormula (allElimFormula φ x t)).encode
      (imp (termGraph id t (witnessName φ x t) base).encode
        (imp (instanceBody φ x (witnessName φ x t)).encode (code (FOL.substAt φ x t)))))) :
    theoremCode (certificate (allElim_of_termGraph φ x t base total substitution)) =
      guardedCode (allElimFormula φ x t) := certificate_correct _

end PASoundness.PAtoCompactGuardedAllElim

#print axioms PASoundness.PAtoCompactGuardedAllElim.universal_instance
#print axioms PASoundness.PAtoCompactGuardedAllElim.allElim_of_witness
#print axioms PASoundness.PAtoCompactGuardedAllElim.allElim_of_witness_certificate
#print axioms PASoundness.PAtoCompactGuardedAllElim.witnessName_guard_fresh
#print axioms PASoundness.PAtoCompactGuardedAllElim.termVars_in_axiom_of_occurs
#print axioms PASoundness.PAtoCompactGuardedAllElim.termVar_guard
#print axioms PASoundness.PAtoCompactGuardedAllElim.witnessName_all_fresh
#print axioms PASoundness.PAtoCompactGuardedAllElim.witnessName_target_fresh
#print axioms PASoundness.PAtoCompactGuardedAllElim.allElim_of_termGraph
#print axioms PASoundness.PAtoCompactGuardedAllElim.allElim_of_termGraph_certificate
