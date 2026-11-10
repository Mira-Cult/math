import PASoundness.PAtoCompactAllElimTermEquality
import PASoundness.PAtoCompactTermAtomGeneralMatrix
import PASoundness.PAtoCompactGeneralAtomFrameIntro

/-! A graph witness for a substituting term can be shared in an atomic
equality whose right side is an arbitrary unchanged PA term. -/
namespace PASoundness.PAtoCompactAllElimTermEqualityGeneral

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactScopedEqualityReplace
open PASoundness.PAtoCompactVacuousEqualityAlignment PASoundness.PAtoCompactFreeNames
open PASoundness.PAtoCompactFreeVacuity PASoundness.PAtoCompactFormulaTranslation
open PASoundness.PAtoCompactAllTermTransport PASoundness.PAtoCompactVacuousQuantifierFree
open PASoundness.PAtoCompactAllElimTermEquality PASoundness.PAtoCompactTermAtomGeneralMatrix
open PASoundness.PAtoCompactGeneralAtomFrameIntro
open PASoundness.PAtoCompactGuardedBridge PASoundness.PAtoCompactGuardedAllElim
open PASoundness.PAtoCompactAllElimVariable PASoundness.PAtoCompactAllElimVariableFull
open PASoundness.PAtoCompactUnaryGuardedCanonical PASoundness.PAtoCompactUnaryTermTransport
open PASoundness.PAtoCompactGuardBaseTransport PASoundness.PAtoCompactSuccTermTotality

set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Reuse the same graph witness to transfer an equality matrix, then
eliminate the two source witnesses and introduce the target witnesses. -/
noncomputable def frame_of_graph (t s : Peano.Term) (q b : Nat)
    (hq : q < b) (ht : ∀ a ∈ t.varFinset, a < b)
    (hs : ∀ a ∈ s.varFinset, a < b)
    (trans : KDerivation (imp (domainAt (b+2+termCost t+termCost s) q).encode
      (imp (equivAt (b+2+termCost t+termCost s) q b).encode
        (imp (equivAt (b+2+termCost t+termCost s) b (b+1)).encode
          (equivAt (b+2+termCost t+termCost s) q (b+1)).encode)))) :
    KDerivation (imp (termGraph id t q (b+2)).encode
      (imp (equalityFrame id (.var q) s b).encode
        (equalityFrame id t s b).encode)) := by
  let G := termGraph id t q (b+2)
  let T := equalityFrame id t s b
  let M := matrix id (.var q) s b (b+1) (b+2)
    (b+2+termCost (.var q : Peano.Term))
    (b+2+termCost (.var q : Peano.Term)+termCost s)
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
  have hm := matrix_of_graph_rebased t s q b (b+1) (b+2)
    (b+2+termCost (.var q : Peano.Term))
    (b+2+termCost (.var q : Peano.Term)+termCost s)
    (b+2) (b+2+termCost t) (b+2+termCost t+termCost s)
    (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)
    (by intro a ha; have := hs a ha; omega)
    (by intro a ha; have := hs a ha; omega) trans
  have hi := target_frame_from_matrix t s q b hq ht hs
  have pointwise : KDerivation (imp G.encode (imp M.encode T.encode)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [M.encode, G.encode]
    have hG : Context Γ G.encode := .hypothesis (by simp [Γ])
    have hM : Context Γ M.encode := Context.head _ _
    exact .mp (.mp hM (.mp hG (.closed hm))) (.closed hi)
  exact two_exists_left_guarded b (b+1) G.encode M.encode T.encode vG0 vG1 vT0 vT1 pointwise

/-- Graph compatibility at the actual source and target equality-code bases. -/
noncomputable def atomic_of_graph (t s : Peano.Term) (q b d : Nat)
    (hq : q < b) (ht : ∀ a ∈ t.varFinset, a < b)
    (hs : ∀ a ∈ s.varFinset, a < b) (hqd : q < d)
    (htd : ∀ a ∈ t.varFinset, a < d) :
    KDerivation (imp (termGraph id t q d).encode
      (imp (code ((.var q : Peano.Term).equal s)) (code (t.equal s)))) := by
  let S := ((.var q : Peano.Term).equal s)
  let T := t.equal s
  let sb := scopeBase S Fin.elim0
  let tb := scopeBase T Fin.elim0
  have hqS : q < sb := by
    apply free_lt_scopeBase S Fin.elim0
    simp [S, eq_free, Term.varFinset]
  have hsS : ∀ a ∈ s.varFinset, a < sb := by
    intro a ha
    apply free_lt_scopeBase S Fin.elim0
    simp [S, eq_free, ha]
  have hsT : ∀ a ∈ s.varFinset, a < tb := by
    intro a ha
    apply free_lt_scopeBase T Fin.elim0
    simp [T, eq_free, ha]
  have htT : ∀ a ∈ t.varFinset, a < tb := by
    intro a ha
    apply free_lt_scopeBase T Fin.elim0
    simp [T, eq_free, ha]
  have hg := (termGraph_base_transport id t d (b+2) q hqd (by omega)
    (by intro a ha; simpa using htd a ha) (by intro a ha; simp only [id_eq]; have := ht a ha; omega)).1
  have hs' := (equalityFrame_base_transport id (.var q : Peano.Term) s sb b
    (by intro a ha; have he : a = q := by simpa [Term.varFinset] using ha
        simpa [he] using hqS)
    (by intro a ha; simpa using hsS a ha)
    (by intro a ha; have he : a = q := by simpa [Term.varFinset] using ha
        simpa [he] using hq)
    (by intro a ha; simpa using hs a ha)).1
  have ht' := (equalityFrame_base_transport id t s b tb
    (by intro a ha; simpa using ht a ha)
    (by intro a ha; simpa using hs a ha)
    (by intro a ha; simpa using htT a ha)
    (by intro a ha; simpa using hsT a ha)).1
  let f := b+2+termCost t+termCost s
  have trans := PASoundness.PAtoCompactDynamicTransitivityFinal.dynamic_transitivity f q b (b+1)
    (by dsimp [f]; omega) (by dsimp [f]; omega) (by dsimp [f]; omega)
  have hf := frame_of_graph t s q b hq ht hs trans
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [code S, (termGraph id t q d).encode]
  have hG : Context Γ (termGraph id t q d).encode := .hypothesis (by simp [Γ])
  have hS : Context Γ (code S) := Context.head _ _
  have hSb : Context Γ (equalityFrame id (.var q) s b).encode := by
    apply Context.mp _ (.closed hs')
    simpa only [code, original_shape, S, sb] using hS
  have hTb := Context.mp hSb (Context.mp (Context.mp hG (.closed hg)) (.closed hf))
  have hT := Context.mp hTb (.closed ht')
  simpa only [Γ, code, original_shape, S, T, tb] using hT

/-- The equality-frame allocation bound is selected internally. -/
noncomputable def atomic_of_graph_fresh (t s : Peano.Term) (q d : Nat)
    (hqd : q < d) (htd : ∀ a ∈ t.varFinset, a < d) :
    KDerivation (imp (termGraph id t q d).encode
      (imp (code ((.var q : Peano.Term).equal s)) (code (t.equal s)))) := by
  let b := max q (max (s.varFinset.sup id) (t.varFinset.sup id)) + 1
  apply atomic_of_graph t s q b d (by dsimp [b]; omega) _ _ hqd htd
  · intro a ha
    have hh : a ≤ t.varFinset.sup id := Finset.le_sup (f := id) ha
    dsimp [b]
    omega
  · intro a ha
    have hh : a ≤ s.varFinset.sup id := Finset.le_sup (f := id) ha
    dsimp [b]
    omega

/-- Substitution leaves a PA term fixed when its variable is absent. -/
theorem term_subst_of_fresh (s t : Peano.Term) (x : Nat) (hx : x ∉ s.varFinset) :
    s.subst (fun y => if y = x then t else .var y) = s := by
  induction s with
  | var a =>
      have hax : a ≠ x := by
        intro h
        subst a
        exact hx (by simp [Term.varFinset])
      simp [Term.subst, hax]
  | func f ss ih =>
      simp only [Term.subst]
      congr 1
      funext i
      apply ih i
      intro hh
      apply hx
      simp only [Term.varFinset, Finset.mem_biUnion, Finset.mem_univ, true_and]
      exact ⟨i, hh⟩

theorem atom_subst_fresh_right (s t : Peano.Term) (x : Nat) (hx : x ∉ s.varFinset) :
    FOL.substAt ((.var x : Peano.Term).equal s) x t = t.equal s := by
  simp only [FOL.substAt, FOL.equality_subst, Term.subst, ↓reduceIte]
  rw [term_subst_of_fresh s t x hx]

/-- The nonvacuous `x = s` leaf follows from guarded existence of the
substituting term's graph when x is absent from the unchanged right term. -/
noncomputable def atomic_allElim_of_total (x : Nat) (s t : Peano.Term)
    (hx : x ∉ s.varFinset)
    (total : KDerivation (imp (guardFormula (allElimFormula
      ((.var x : Peano.Term).equal s) x t)).encode
      (existsCode (outputName (allElimFormula ((.var x : Peano.Term).equal s) x t))
        (termGraph id t (outputName (allElimFormula ((.var x : Peano.Term).equal s) x t))
          (allocatorBase (allElimFormula ((.var x : Peano.Term).equal s) x t))).encode))) :
    KDerivation (guardedCode (allElimFormula ((.var x : Peano.Term).equal s) x t)) := by
  let φ := ((.var x : Peano.Term).equal s)
  let A := allElimFormula φ x t
  let q := outputName A
  let d := allocatorBase A
  let G := (guardFormula A).encode
  let U := code (FOL.allAt x φ)
  let B := code (FOL.substAt φ x t)
  let X := (termGraph id t q d).encode
  have hoccurs : x ∈ φ.freeVarFinset := by simp [φ, eq_free, Term.varFinset]
  have hcover : ∀ a ∈ t.varFinset, a ∈ A.freeVarFinset := by
    intro a ha
    exact termVars_in_axiom_of_occurs φ x t hoccurs ha
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
  have hc := atomic_of_graph_fresh t s q d hqd htd
  have hd := termGraph_domain id t q d
  have hqz : q < instanceBinder φ x q + 1 := by
    unfold instanceBinder
    omega
  have hdt := domainAt_transport d (instanceBinder φ x q + 1) q (by omega) (by omega)
  have hinst : KDerivation (imp U (imp (domainAt (instanceBinder φ x q + 1) q).encode
      (code ((.var q : Peano.Term).equal s)))) := by
    simpa [φ, atom_subst_fresh_right s (.var q) x hx] using hi
  have htarget : code (t.equal s) = B := by
    simp [B, φ, atom_subst_fresh_right s t x hx]
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

/-- Unary terms have the required guarded graph-existence derivation. -/
noncomputable def atomic_allElim_unary (x : Nat) (s t : Peano.Term)
    (hx : x ∉ s.varFinset) (ht : UnaryTerm t) :
    KDerivation (guardedCode (allElimFormula ((.var x : Peano.Term).equal s) x t)) := by
  apply atomic_allElim_of_total x s t hx
  let φ := ((.var x : Peano.Term).equal s)
  let A := allElimFormula φ x t
  have hoccurs : x ∈ φ.freeVarFinset := by simp [φ, eq_free, Term.varFinset]
  have hcover : ∀ a ∈ t.varFinset, id a ∈ A.freeVarFinset := by
    intro a ha
    exact termVars_in_axiom_of_occurs φ x t hoccurs ha
  exact unary_total id A ht hcover

end PASoundness.PAtoCompactAllElimTermEqualityGeneral

#print axioms PASoundness.PAtoCompactAllElimTermEqualityGeneral.atomic_of_graph
#print axioms PASoundness.PAtoCompactAllElimTermEqualityGeneral.atomic_of_graph_fresh
#print axioms PASoundness.PAtoCompactAllElimTermEqualityGeneral.atomic_allElim_of_total
#print axioms PASoundness.PAtoCompactAllElimTermEqualityGeneral.atomic_allElim_unary
