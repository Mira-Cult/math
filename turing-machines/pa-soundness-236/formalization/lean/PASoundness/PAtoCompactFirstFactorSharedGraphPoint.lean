import PASoundness.PAtoCompactMulNodeWitnessIntro
import PASoundness.PAtoCompactPAAddSuccSharedSmallWitness
import PASoundness.PAtoCompactAllTermTransport
import PASoundness.PAtoCompactSuccBaseMultiAlpha
import PASoundness.PAtoCompactMulBaseMultiAlpha

/-! Pointwise construction of both sides of a first-factor multiplication
successor equation at one common output. The arithmetic relations and child
graphs are supplied as antecedents; existence and the PA axiom are not proved. -/
namespace PASoundness.PAtoCompactFirstFactorSharedGraphPoint

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactTermZeroGuarded
open PASoundness.PAtoCompactMulNodeWitnessIntro PASoundness.PAtoCompactPAAddSuccSharedSmallWitness
open PASoundness.PAtoCompactAllTermTransport PASoundness.PAtoCompactGuardBaseTransport
open PASoundness.PAtoCompactSuccTermTotality PASoundness.PAtoCompactSuccBaseMultiAlpha
open PASoundness.PAtoCompactMulBaseMultiAlpha

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Given the displayed child graphs, candidate guards and arithmetic diamond,
construct both generated graphs with the same output. All witness labels may
alias, as may the represented values. This does not construct the diamond. -/
noncomputable def shared_graphs {α : Type} [DecidableEq α]
    (v : α → Nat) (t u : Peano.language.Term α) (e x y sx p out : Nat)
    (hx : x < e) (hy : y < e) (hsx : sx < e) (hp : p < e) (ho : out < e)
    (ht : ∀ a ∈ t.varFinset, v a < e) (hu : ∀ a ∈ u.varFinset, v a < e) :
    KDerivation (imp (domainAt e sx).encode (imp (domainAt e p).encode
      (imp (domainAt e out).encode (imp (termGraph v t x e).encode
        (imp (termGraph v u y e).encode (imp (succAt e x sx).encode
          (imp (mulAt e x y p).encode (imp (addAt e p y out).encode
            (imp (mulAt e sx y out).encode
              (andF (termGraph v (binaryTerm false (.func .succ ![t]) u) out e)
                (termGraph v (binaryTerm true (binaryTerm false t u) u) out e)).encode))))))))) := by
  let st : Peano.language.Term α := .func .succ ![t]
  let tu := binaryTerm false t u
  let inner := e+64
  have hst : ∀ a ∈ st.varFinset, v a < e := by
    intro a ha
    apply ht
    simpa [st, Term.varFinset] using ha
  have htu : ∀ a ∈ tu.varFinset, v a < e := by
    intro a ha
    simp only [tu, binaryTerm, Bool.false_eq_true, ↓reduceIte, Term.varFinset,
      Finset.mem_biUnion, Finset.mem_univ, true_and] at ha
    obtain ⟨i, hi⟩ := ha
    fin_cases i
    · exact ht a hi
    · exact hu a hi
  have hTinner := (termGraph_base_transport v t e (inner+64) x hx (by dsimp [inner]; omega)
    ht (by intro a ha; have := ht a ha; dsimp [inner]; omega)).1
  have hUleft := (termGraph_base_transport v u e (e+64+termCost st) y hy (by omega)
    hu (by intro a ha; have := hu a ha; omega)).1
  have hUinner := (termGraph_base_transport v u e (inner+64+termCost t) y hy
    (by dsimp [inner]; omega) hu (by intro a ha; have := hu a ha; dsimp [inner]; omega)).1
  have hUright := (termGraph_base_transport v u e (e+64+termCost tu) y hy (by omega)
    hu (by intro a ha; have := hu a ha; omega)).1
  have hsxD := domainAt_transport e inner sx (by omega) (by dsimp [inner]; omega)
  have hpD := domainAt_transport e inner p (by omega) (by dsimp [inner]; omega)
  have hS := (succAt_base_alpha e inner x sx (by omega) (by omega)
    (by dsimp [inner]; omega) (by dsimp [inner]; omega)).forward
  have hM := (mulAt_base_alpha e inner x y p (by omega) (by omega) (by omega)
    (by dsimp [inner]; omega) (by dsimp [inner]; omega) (by dsimp [inner]; omega)).forward
  have hsGraph := succTerm_from_witness v t inner sx x (by dsimp [inner]; omega)
    (by dsimp [inner]; omega) (by intro a ha; have := ht a ha; dsimp [inner]; omega)
  have hLeft := from_witnesses v st u e out sx y ho hsx hy hst hu
  have hOld := from_witnesses v t u inner p x y (by dsimp [inner]; omega)
    (by dsimp [inner]; omega) (by dsimp [inner]; omega)
    (by intro a ha; have := ht a ha; dsimp [inner]; omega)
    (by intro a ha; have := hu a ha; dsimp [inner]; omega)
  have hRight := add_graph_from_witnesses v tu u e out p y ho hp hy htu hu
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [(mulAt e sx y out).encode, (addAt e p y out).encode,
    (mulAt e x y p).encode, (succAt e x sx).encode, (termGraph v u y e).encode,
    (termGraph v t x e).encode, (domainAt e out).encode, (domainAt e p).encode,
    (domainAt e sx).encode]
  have hNew : Context Γ (mulAt e sx y out).encode := .head _ _
  have hAdd : Context Γ (addAt e p y out).encode := .hypothesis (by simp [Γ])
  have hOldM : Context Γ (mulAt e x y p).encode := .hypothesis (by simp [Γ])
  have hSucc : Context Γ (succAt e x sx).encode := .hypothesis (by simp [Γ])
  have hU : Context Γ (termGraph v u y e).encode := .hypothesis (by simp [Γ])
  have hT : Context Γ (termGraph v t x e).encode := .hypothesis (by simp [Γ])
  have hOut : Context Γ (domainAt e out).encode := .hypothesis (by simp [Γ])
  have hP : Context Γ (domainAt e p).encode := .hypothesis (by simp [Γ])
  have hSX : Context Γ (domainAt e sx).encode := .hypothesis (by simp [Γ])
  have hSuccGraph : Context Γ (termGraph v st sx inner).encode :=
    .mp (.mp hSucc (.closed hS))
      (.mp (.mp hT (.closed hTinner)) (.mp (.mp hSX (.closed hsxD)) (.closed hsGraph)))
  have hLeftGraph : Context Γ (termGraph v (binaryTerm false st u) out e).encode :=
    .mp hNew (.mp (.mp hU (.closed hUleft)) (.mp hSuccGraph (.mp hOut (.closed hLeft))))
  have hOldGraph : Context Γ (termGraph v tu p inner).encode :=
    .mp (.mp hOldM (.closed hM)) (.mp (.mp hU (.closed hUinner))
      (.mp (.mp hT (.closed hTinner)) (.mp (.mp hP (.closed hpD)) (.closed hOld))))
  have hRightGraph : Context Γ (termGraph v (binaryTerm true tu u) out e).encode :=
    .mp hAdd (.mp (.mp hU (.closed hUright)) (.mp hOldGraph (.mp hOut (.closed hRight))))
  have h := Context.conjunctionIntro hLeftGraph hRightGraph
  simpa [st, tu, andF, CompactNamed.Formula.not, Formula.encode, both, neg] using h

end PASoundness.PAtoCompactFirstFactorSharedGraphPoint

#print axioms PASoundness.PAtoCompactFirstFactorSharedGraphPoint.shared_graphs
