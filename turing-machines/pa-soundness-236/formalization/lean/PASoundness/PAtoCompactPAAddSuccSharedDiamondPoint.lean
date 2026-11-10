import PASoundness.PAtoCompactPAAddSuccSharedSmallWitness
import PASoundness.PAtoCompactAllTermTransport
import PASoundness.PAtoCompactAddBaseMultiAlpha
import PASoundness.PAtoCompactSuccBaseMultiAlpha

/-! Assemble the two actual addition-successor term graphs at one output
from an explicitly supplied arithmetic diamond. This is a finite K proof and
does not construct the diamond or source graphs. -/
namespace PASoundness.PAtoCompactPAAddSuccSharedDiamondPoint

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactTermZeroGuarded
open PASoundness.PAtoCompactPAAddSuccSharedSmallWitness PASoundness.PAtoCompactAllTermTransport
open PASoundness.PAtoCompactGuardBaseTransport PASoundness.PAtoCompactSuccTermTotality
open PASoundness.PAtoCompactAddBaseMultiAlpha PASoundness.PAtoCompactSuccBaseMultiAlpha

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] PASoundness.CompactProof.imp Cantor.pair Cantor.triangle

/-- Pointwise shared graph construction. The two source graphs and all
arithmetic relations are at base `e`; the resulting left and right term graphs
may use different bases. Every displayed witness may alias another. -/
noncomputable def shared_graphs_of_diamond {α : Type} [DecidableEq α]
    (v : α → Nat) (t u : Peano.language.Term α)
    (e l r x y sy z out : Nat)
    (hxe : x < e) (hye : y < e) (hsye : sy < e) (hze : z < e) (hoe : out < e)
    (hxl : x < l) (hyl : y < l) (hsyl : sy < l) (hol : out < l)
    (hxr : x < r) (hyr : y < r) (hzr : z < r) (hor : out < r)
    (hte : ∀ a ∈ t.varFinset, v a < e) (hue : ∀ a ∈ u.varFinset, v a < e)
    (htl : ∀ a ∈ t.varFinset, v a < l) (hul : ∀ a ∈ u.varFinset, v a < l)
    (htr : ∀ a ∈ t.varFinset, v a < r) (hur : ∀ a ∈ u.varFinset, v a < r) :
    KDerivation (imp (domainAt e sy).encode (imp (domainAt e z).encode
      (imp (domainAt e out).encode (imp (termGraph v t x e).encode
        (imp (termGraph v u y e).encode (imp (succAt e y sy).encode
          (imp (addAt e x y z).encode (imp (succAt e z out).encode
            (imp (addAt e x sy out).encode
              (andF (termGraph v (binaryTerm true t (.func .succ ![u])) out l)
                (termGraph v (.func .succ ![binaryTerm true t u]) out r)).encode))))))))) := by
  let lt := l + 64
  let lu := l + 64 + termCost t
  let ra := r + 64
  let rt := ra + 64
  let ru := ra + 64 + termCost t
  have hgtl := (termGraph_base_transport v t e lt x hxe (by dsimp [lt]; omega)
    hte (by intro a ha; have := htl a ha; dsimp [lt]; omega)).1
  have hgul := (termGraph_base_transport v u e (lu+64) y hye (by dsimp [lu]; omega)
    hue (by intro a ha; have := hul a ha; dsimp [lu]; omega)).1
  have hgtr := (termGraph_base_transport v t e rt x hxe (by dsimp [rt, ra]; omega)
    hte (by intro a ha; have := htr a ha; dsimp [rt, ra]; omega)).1
  have hgur := (termGraph_base_transport v u e ru y hye (by dsimp [ru, ra]; omega)
    hue (by intro a ha; have := hur a ha; dsimp [ru, ra]; omega)).1
  have hsyD := domainAt_transport e lu sy (by omega) (by dsimp [lu]; omega)
  have hzD := domainAt_transport e ra z (by omega) (by dsimp [ra]; omega)
  have hoD₁ := domainAt_transport e l out (by omega) (by omega)
  have hoD₂ := domainAt_transport e r out (by omega) (by omega)
  have hs₁ := (succAt_base_alpha e lu y sy (by omega) (by omega)
    (by dsimp [lu]; omega) (by dsimp [lu]; omega)).forward
  have hs₂ := (succAt_base_alpha e r z out (by omega) (by omega) (by omega) (by omega)).forward
  have ha₁ := (addAt_base_alpha e l x sy out (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega)).forward
  have ha₂ := (addAt_base_alpha e ra x y z (by omega) (by omega) (by omega)
    (by dsimp [ra]; omega) (by dsimp [ra]; omega) (by dsimp [ra]; omega)).forward
  have hsGraph := succTerm_from_witness v u lu sy y (by dsimp [lu]; omega)
    (by dsimp [lu]; omega) (by intro a ha; have := hul a ha; dsimp [lu]; omega)
  have hleft := add_graph_from_witnesses v t (.func .succ ![u]) l out x sy
    hol hxl hsyl htl (by simpa [Term.varFinset] using hul)
  have hadd := add_graph_from_witnesses v t u ra z x y (by dsimp [ra]; omega)
    (by dsimp [ra]; omega) (by dsimp [ra]; omega)
    (by intro a ha; have := htr a ha; dsimp [ra]; omega)
    (by intro a ha; have := hur a ha; dsimp [ra]; omega)
  have hright := succTerm_from_witness v (binaryTerm true t u) r out z hor hzr
    (by intro a ha; simp only [binaryTerm, ↓reduceIte, Term.varFinset,
      Finset.mem_biUnion, Finset.mem_univ, true_and] at ha
        obtain ⟨i, hi⟩ := ha
        fin_cases i
        · exact htr a hi
        · exact hur a hi)
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
  let Γ := [(addAt e x sy out).encode, (succAt e z out).encode,
    (addAt e x y z).encode, (succAt e y sy).encode, (termGraph v u y e).encode,
    (termGraph v t x e).encode, (domainAt e out).encode, (domainAt e z).encode,
    (domainAt e sy).encode]
  have hA₁ : Context Γ (addAt e x sy out).encode := .head _ _
  have hS₂ : Context Γ (succAt e z out).encode := .hypothesis (by simp [Γ])
  have hA₂ : Context Γ (addAt e x y z).encode := .hypothesis (by simp [Γ])
  have hS₁ : Context Γ (succAt e y sy).encode := .hypothesis (by simp [Γ])
  have hU : Context Γ (termGraph v u y e).encode := .hypothesis (by simp [Γ])
  have hT : Context Γ (termGraph v t x e).encode := .hypothesis (by simp [Γ])
  have hO : Context Γ (domainAt e out).encode := .hypothesis (by simp [Γ])
  have hZ : Context Γ (domainAt e z).encode := .hypothesis (by simp [Γ])
  have hY : Context Γ (domainAt e sy).encode := .hypothesis (by simp [Γ])
  have huS : Context Γ (termGraph v (.func .succ ![u]) sy lu).encode :=
    .mp (.mp hS₁ (.closed hs₁)) (.mp (.mp hU (.closed hgul)) (.mp (.mp hY (.closed hsyD)) (.closed hsGraph)))
  have hL : Context Γ (termGraph v (binaryTerm true t (.func .succ ![u])) out l).encode :=
    .mp (.mp hA₁ (.closed ha₁)) (.mp huS (.mp (.mp hT (.closed hgtl)) (.mp (.mp hO (.closed hoD₁)) (.closed hleft))))
  have hzG : Context Γ (termGraph v (binaryTerm true t u) z ra).encode :=
    .mp (.mp hA₂ (.closed ha₂)) (.mp (.mp hU (.closed hgur)) (.mp (.mp hT (.closed hgtr)) (.mp (.mp hZ (.closed hzD)) (.closed hadd))))
  have hR : Context Γ (termGraph v (.func .succ ![binaryTerm true t u]) out r).encode :=
    .mp (.mp hS₂ (.closed hs₂)) (.mp hzG (.mp (.mp hO (.closed hoD₂)) (.closed hright)))
  have h := Context.conjunctionIntro hL hR
  simpa [andF, CompactNamed.Formula.not, Formula.encode, both, neg] using h

end PASoundness.PAtoCompactPAAddSuccSharedDiamondPoint

#print axioms PASoundness.PAtoCompactPAAddSuccSharedDiamondPoint.shared_graphs_of_diamond
