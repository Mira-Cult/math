import PASoundness.CompactNamed
import PASoundness.PAtoCompactVacuousEqualityAlignment
import PASoundness.PAtoCompactVariableTermTotality
import PASoundness.CompactQuantifiers
import PASoundness.PAtoCompactTermVariableAtomCompat
import PASoundness.PAtoCompactDynamicTransitivityFinal
import PASoundness.PAtoCompactVacuousQuantifierFree
import PASoundness.PAtoCompactAllElimVariable
import PASoundness.PAtoCompactAllElimVariableFull

/-! Capture-safe existential elimination for graph-witness implications.
The displayed vacuity and pointwise K derivations are explicit inputs. -/
namespace PASoundness.PAtoCompactAllElimTermEquality

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open FirstOrder FirstOrder.Language
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactScopedEqualityReplace
open PASoundness.PAtoCompactVacuousEqualityAlignment PASoundness.PAtoCompactVariableTermTotality
open PASoundness.PAtoCompactTermVariableAtomCompat PASoundness.PAtoCompactFreeNames
open PASoundness.PAtoCompactFreeVacuity
open PASoundness.PAtoCompactFormulaTranslation PASoundness.PAtoCompactAllTermTransport
open PASoundness.PAtoCompactVacuousQuantifierFree
open PASoundness.PAtoCompactAllElimVariable PASoundness.PAtoCompactAllElimVariableFull
open PASoundness.PAtoCompactUnaryGuardedCanonical PASoundness.PAtoCompactUnaryTermTransport
open PASoundness.PAtoCompactGuardedBridge PASoundness.PAtoCompactGuardedAllElim
open PASoundness.PAtoCompactGuardBaseTransport PASoundness.PAtoCompactSuccTermTotality
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Lift a guarded pointwise implication through an existential antecedent.
The guard and conclusion each need a K vacuity proof for the witness name. -/
def exists_left_guarded (x G M T : Nat)
    (vg : KDerivation (imp G (allCode x G)))
    (vt : KDerivation (imp T (allCode x T)))
    (pointwise : KDerivation (imp G (imp M T))) :
    KDerivation (imp G (imp (existsCode x M) T)) := by
  have hall : Context [G] (allCode x (imp M T)) := by
    apply generalizeOne x vg
    exact .mp (Context.head [] G) (.closed pointwise)
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  exact Context.existsElim vt (Context.under hall (existsCode x M))
    (Context.head [G] (existsCode x M))

/-- Eliminate both value witnesses from an atomic equality frame, provided
the pointwise matrix-to-conclusion derivation and all four vacuity proofs. -/
def two_exists_left_guarded (x y G M T : Nat)
    (vgx : KDerivation (imp G (allCode x G)))
    (vgy : KDerivation (imp G (allCode y G)))
    (vtx : KDerivation (imp T (allCode x T)))
    (vty : KDerivation (imp T (allCode y T)))
    (pointwise : KDerivation (imp G (imp M T))) :
    KDerivation (imp G (imp (existsCode x (existsCode y M)) T)) :=
  exists_left_guarded x G (existsCode y M) T vgx vtx
    (exists_left_guarded y G M T vgy vty pointwise)

theorem two_exists_left_guarded_certificate (x y G M T : Nat)
    (vgx : KDerivation (imp G (allCode x G)))
    (vgy : KDerivation (imp G (allCode y G)))
    (vtx : KDerivation (imp T (allCode x T)))
    (vty : KDerivation (imp T (allCode y T)))
    (pointwise : KDerivation (imp G (imp M T))) :
    theoremCode (certificate (two_exists_left_guarded x y G M T vgx vgy vtx vty pointwise)) =
      imp G (imp (existsCode x (existsCode y M)) T) := certificate_correct _

/-- Introduce the two target equality-frame witnesses, using the concrete
graph value `q` for the left side and retaining the second frame witness.
All source names must be below the frame's allocation boundary. -/
def target_frame_from_matrix (t : Peano.Term) (q z b : Nat)
    (hq : q < b) (hz : z < b) (ht : ∀ a ∈ t.varFinset, a < b) :
    KDerivation (imp (matrix id t (.var z) q (b+1) (b+2)
      (b+2+termCost t) (b+2+termCost t+termCost (.var z))).encode
      (equalityFrame id t (.var z) b).encode) := by
  let p := b+2
  let s := b+2+termCost t
  let e := b+2+termCost t+termCost (.var z : Peano.Term)
  let N := matrix id t (.var z) b (b+1) p s e
  let M := matrix id t (.var z) q (b+1) p s e
  have hNb : b ∉ N.binders := matrix_below_not_binder id t (.var z) b (b+1) p s e b
    (by dsimp [p]; omega) (by dsimp [s]; omega) (by dsimp [e]; omega)
  have hNq : q ∉ N.binders := matrix_below_not_binder id t (.var z) b (b+1) p s e q
    (by dsimp [p]; omega) (by dsimp [s]; omega) (by dsimp [e]; omega)
  have hMb : b+1 ∉ M.binders := matrix_below_not_binder id t (.var z) q (b+1) p s e (b+1)
    (by dsimp [p]; omega) (by dsimp [s]; omega) (by dsimp [e]; omega)
  have hrepl : replace b q N = M := by
    dsimp [N, M]
    rw [matrix_replace_fresh_source id t (.var z) b (b+1) p s e b q
      (by dsimp [p]; omega) (by dsimp [s]; omega) (by dsimp [e]; omega)
      (by intro a ha; have := ht a ha; simp only [id_eq]; omega)
      (by intro a ha; have he : a = z := by simpa [Term.varFinset] using ha
          simp only [id_eq]; omega)]
    simp [rename]
  have hi := existsIntroduce (b+1) M hMb
  have ho := exists_from_instance b q (.ex (b+1) N) (by omega)
    (by simpa [Formula.binders] using hNb)
    (by simpa [Formula.binders, show q ≠ b+1 by omega] using hNq)
  have ho' : KDerivation (imp (existsCode (b+1) M.encode)
      (equalityFrame id t (.var z) b).encode) := by
    change KDerivation (imp (existsCode (b+1) (replace b q N).encode)
      (equalityFrame id t (.var z) b).encode) at ho
    rw [hrepl] at ho
    exact ho
  exact compose hi ho'

/-- Eliminate the source frame's two value witnesses and introduce the
target frame witnesses. The graph's value is reused, so no graph
functionality is required. The displayed transitivity derivation is the
only quotient-law input. -/
noncomputable def frame_of_graph (t : Peano.Term) (q z b : Nat)
    (hq : q < b) (hz : z < b) (ht : ∀ a ∈ t.varFinset, a < b)
    (trans : KDerivation (imp (domainAt (b+2+termCost t+termCost (.var z : Peano.Term)) q).encode
      (imp (equivAt (b+2+termCost t+termCost (.var z : Peano.Term)) q b).encode
        (imp (equivAt (b+2+termCost t+termCost (.var z : Peano.Term)) b (b+1)).encode
          (equivAt (b+2+termCost t+termCost (.var z : Peano.Term)) q (b+1)).encode)))) :
    KDerivation (imp (termGraph id t q (b+2)).encode
      (imp (equalityFrame id (.var q) (.var z) b).encode
        (equalityFrame id t (.var z) b).encode)) := by
  let G := termGraph id t q (b+2)
  let T := equalityFrame id t (.var z) b
  let M := matrix id (.var q) (.var z) b (b+1) (b+2)
    (b+2+termCost (.var q : Peano.Term))
    (b+2+termCost (.var q : Peano.Term)+termCost (.var z : Peano.Term))
  have gf (a : Nat) (ha : b ≤ a) : a ∉ G.free := by
    intro h
    have hh := termGraph_free_subset id t q (b+2) h
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_singleton] at hh
    rcases hh with ⟨v, hv, hv'⟩ | he
    · have := ht v hv
      simp only [id_eq] at hv'
      omega
    · omega
  have tf0 : b ∉ T.free := by simp [T, equalityFrame, Formula.free]
  have tf1 : b+1 ∉ T.free := by simp [T, equalityFrame, Formula.free]
  have vG0 := free_vacuity b G (gf b (by omega))
  have vG1 := free_vacuity (b+1) G (gf (b+1) (by omega))
  have vT0 := free_vacuity b T tf0
  have vT1 := free_vacuity (b+1) T tf1
  have hm := matrix_of_graph_rebased t q z b (b+1) (b+2)
    (b+2+termCost (.var q : Peano.Term))
    (b+2+termCost (.var q : Peano.Term)+termCost (.var z : Peano.Term))
    (b+2) (b+2+termCost t) (b+2+termCost t+termCost (.var z : Peano.Term))
    (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) trans
  have hi := target_frame_from_matrix t q z b hq hz ht
  have pointwise : KDerivation (imp G.encode (imp M.encode T.encode)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [M.encode, G.encode]
    have hG : Context Γ G.encode := .hypothesis (by simp [Γ])
    have hM : Context Γ M.encode := Context.head _ _
    exact .mp (.mp hM (.mp hG (.closed hm))) (.closed hi)
  exact two_exists_left_guarded b (b+1) G.encode M.encode T.encode vG0 vG1 vT0 vT1 pointwise

/-- The same graph-to-atomic-equality implication at the actual source
formula allocation bases. The graph's input and output names are below its
explicit allocator boundary, and `b` is a fresh equality-frame boundary. -/
noncomputable def atomic_of_graph (t : Peano.Term) (q z b d : Nat)
    (hq : q < b) (hz : z < b) (ht : ∀ a ∈ t.varFinset, a < b)
    (hqd : q < d) (htd : ∀ a ∈ t.varFinset, a < d) :
    KDerivation (imp (termGraph id t q d).encode
      (imp (code ((.var q : Peano.Term).equal (.var z)))
        (code (t.equal (.var z))))) := by
  let S := ((.var q : Peano.Term).equal (.var z))
  let T := t.equal (.var z)
  let sb := scopeBase S Fin.elim0
  let tb := scopeBase T Fin.elim0
  have hqS : q < sb := by
    apply free_lt_scopeBase S Fin.elim0
    simp [S, eq_free, Term.varFinset]
  have hzS : z < sb := by
    apply free_lt_scopeBase S Fin.elim0
    simp [S, eq_free, Term.varFinset]
  have hzT : z < tb := by
    apply free_lt_scopeBase T Fin.elim0
    simp [T, eq_free, Term.varFinset]
  have htT : ∀ a ∈ t.varFinset, a < tb := by
    intro a ha
    apply free_lt_scopeBase T Fin.elim0
    simp [T, eq_free, ha]
  have hg := (termGraph_base_transport id t d (b+2) q hqd (by omega)
    (by intro a ha; simpa using htd a ha) (by intro a ha; simp only [id_eq]; have := ht a ha; omega)).1
  have hs := (equalityFrame_base_transport id (.var q : Peano.Term) (.var z : Peano.Term) sb b
    (by intro a ha; have he : a = q := by simpa [Term.varFinset] using ha
        simpa [he] using hqS)
    (by intro a ha; have he : a = z := by simpa [Term.varFinset] using ha
        simpa [he] using hzS)
    (by intro a ha; have he : a = q := by simpa [Term.varFinset] using ha
        simpa [he] using hq)
    (by intro a ha; have he : a = z := by simpa [Term.varFinset] using ha
        simpa [he] using hz)).1
  have ht' := (equalityFrame_base_transport id t (.var z : Peano.Term) b tb
    (by intro a ha; simpa using ht a ha)
    (by intro a ha; have he : a = z := by simpa [Term.varFinset] using ha
        simpa [he] using hz)
    (by intro a ha; simpa using htT a ha)
    (by intro a ha; have he : a = z := by simpa [Term.varFinset] using ha
        simpa [he] using hzT)).1
  let f := b+2+termCost t+termCost (.var z : Peano.Term)
  have trans := PASoundness.PAtoCompactDynamicTransitivityFinal.dynamic_transitivity f q b (b+1)
    (by dsimp [f]; omega) (by dsimp [f]; omega) (by dsimp [f]; omega)
  have hf := frame_of_graph t q z b hq hz ht trans
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [code S, (termGraph id t q d).encode]
  have hG : Context Γ (termGraph id t q d).encode := .hypothesis (by simp [Γ])
  have hS : Context Γ (code S) := Context.head _ _
  have hSb : Context Γ (equalityFrame id (.var q) (.var z) b).encode := by
    apply Context.mp _ (.closed hs)
    simpa only [code, original_shape, S, sb] using hS
  have hTb := Context.mp hSb (Context.mp (Context.mp hG (.closed hg)) (.closed hf))
  have hT := Context.mp hTb (.closed ht')
  simpa only [Γ, code, original_shape, S, T, tb] using hT

/-- Choose the private equality-frame base internally. -/
noncomputable def atomic_of_graph_fresh (t : Peano.Term) (q z d : Nat)
    (hqd : q < d) (htd : ∀ a ∈ t.varFinset, a < d) :
    KDerivation (imp (termGraph id t q d).encode
      (imp (code ((.var q : Peano.Term).equal (.var z)))
        (code (t.equal (.var z))))) := by
  let b := max q (max z (t.varFinset.sup id)) + 1
  apply atomic_of_graph t q z b d (by dsimp [b]; omega) (by dsimp [b]; omega) _ hqd htd
  intro a ha
  have hh : a ≤ t.varFinset.sup id := Finset.le_sup (f := id) ha
  dsimp [b]
  omega

/-- Guarded elimination for the atom `x = z` from the actual guarded
graph-existence derivation for t. The graph-existence input is explicit and
is only required for this nonvacuous axiom. -/
noncomputable def atomic_allElim_of_total (x z : Nat) (t : Peano.Term) (hzx : z ≠ x)
    (total : KDerivation (imp (guardFormula (allElimFormula
      ((.var x : Peano.Term).equal (.var z)) x t)).encode
      (existsCode (outputName (allElimFormula ((.var x : Peano.Term).equal (.var z)) x t))
        (termGraph id t (outputName (allElimFormula ((.var x : Peano.Term).equal (.var z)) x t))
          (allocatorBase (allElimFormula ((.var x : Peano.Term).equal (.var z)) x t))).encode))) :
    KDerivation (guardedCode (allElimFormula ((.var x : Peano.Term).equal (.var z)) x t)) := by
  let φ := ((.var x : Peano.Term).equal (.var z))
  let A := allElimFormula φ x t
  let q := outputName A
  let d := allocatorBase A
  let G := (guardFormula A).encode
  let U := code (FOL.allAt x φ)
  let B := code (FOL.substAt φ x t)
  let X := (termGraph id t q d).encode
  have hx : x ∈ φ.freeVarFinset := by simp [φ, eq_free, Term.varFinset]
  have hcover : ∀ a ∈ t.varFinset, a ∈ A.freeVarFinset := by
    intro a ha
    exact termVars_in_axiom_of_occurs φ x t hx ha
  have htd : ∀ a ∈ t.varFinset, a < d := by
    intro a ha
    have hm := hcover a ha
    have hl : a ≤ A.freeVarFinset.sup id := Finset.le_sup (f := id) hm
    dsimp [d, allocatorBase, q, outputName, guardBase]
    omega
  have hqd : q < d := by dsimp [q, d, allocatorBase]; omega
  have vg : KDerivation (imp G (allCode q G)) := free_vacuity q _ (outputName_guard_fresh φ x t)
  have vu : KDerivation (imp U (allCode q U)) := free_vacuity q _ (outputName_all_fresh φ x t)
  have vb : KDerivation (imp B (allCode q B)) := free_vacuity q _ (outputName_target_fresh φ x t)
  have hi := variable_instance φ x q
  have hc := atomic_of_graph_fresh t q z d hqd htd
  have hd := termGraph_domain id t q d
  have hqz : q < instanceBinder φ x q + 1 := by
    unfold instanceBinder
    omega
  have hdt := domainAt_transport d (instanceBinder φ x q + 1) q (by omega) (by omega)
  have hinst : KDerivation (imp U (imp (domainAt (instanceBinder φ x q + 1) q).encode
      (code ((.var q : Peano.Term).equal (.var z))))) := by
    simpa [φ, FOL.substAt, FOL.equality_subst, Term.subst, hzx] using hi
  have htarget : code (t.equal (.var z)) = B := by
    simp [B, φ, FOL.substAt, FOL.equality_subst, Term.subst, hzx]
  change KDerivation (imp G (imp U B))
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [U, G]
  have hG : Context Γ G := .hypothesis (by simp [Γ])
  apply Context.existsElim vb
  · apply Context.generalize q
    · intro h hh
      by_cases he : h = U
      · subst h; exact vu
      · have he' : h = G := by simpa [Γ, he] using hh
        subst h; exact vg
    · apply Context.deduction
      let Δ := [X, U, G]
      have hX : Context Δ X := Context.head _ _
      have hU : Context Δ U := .hypothesis (by simp [Δ])
      have hD := Context.mp (Context.mp hX (.closed hd)) (.closed hdt)
      have hsource := Context.mp hD (Context.mp hU (.closed hinst))
      have htarget' := Context.mp hsource (Context.mp hX (.closed hc))
      simpa only [htarget] using htarget'
  · exact .mp hG (.closed total)

/-- Unary substitution terms have the required guarded graph existence. -/
noncomputable def atomic_allElim_unary (x z : Nat) (t : Peano.Term) (hzx : z ≠ x)
    (ht : UnaryTerm t) :
    KDerivation (guardedCode (allElimFormula ((.var x : Peano.Term).equal (.var z)) x t)) := by
  apply atomic_allElim_of_total x z t hzx
  let φ := ((.var x : Peano.Term).equal (.var z))
  let A := allElimFormula φ x t
  have hx : x ∈ φ.freeVarFinset := by simp [φ, eq_free, Term.varFinset]
  have hcover : ∀ a ∈ t.varFinset, id a ∈ A.freeVarFinset := by
    intro a ha
    exact termVars_in_axiom_of_occurs φ x t hx ha
  exact unary_total id A ht hcover

end PASoundness.PAtoCompactAllElimTermEquality

#print axioms PASoundness.PAtoCompactAllElimTermEquality.exists_left_guarded
#print axioms PASoundness.PAtoCompactAllElimTermEquality.two_exists_left_guarded
#print axioms PASoundness.PAtoCompactAllElimTermEquality.two_exists_left_guarded_certificate
#print axioms PASoundness.PAtoCompactAllElimTermEquality.target_frame_from_matrix
#print axioms PASoundness.PAtoCompactAllElimTermEquality.frame_of_graph
#print axioms PASoundness.PAtoCompactAllElimTermEquality.atomic_of_graph
#print axioms PASoundness.PAtoCompactAllElimTermEquality.atomic_of_graph_fresh
#print axioms PASoundness.PAtoCompactAllElimTermEquality.atomic_allElim_of_total
#print axioms PASoundness.PAtoCompactAllElimTermEquality.atomic_allElim_unary
