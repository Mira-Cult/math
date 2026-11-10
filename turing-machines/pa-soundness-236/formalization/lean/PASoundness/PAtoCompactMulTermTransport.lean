import PASoundness.PAtoCompactMulBaseMultiAlpha
import PASoundness.PAtoCompactMulTermTransportWitness
import PASoundness.PAtoCompactZeroTermBaseTransport

/-! Conditional finite K transport for a multiplication term node. Actual
bidirectional child-graph transports remain explicit proof-data inputs. -/
namespace PASoundness.PAtoCompactMulTermTransport

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.CompactHilbertBasis PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactMulBaseMultiAlpha PASoundness.PAtoCompactGuardBaseTransport
open PASoundness.PAtoCompactMulTermTransportWitness PASoundness.PAtoCompactZeroTermBaseTransport

/-- Move a multiplication node to a higher base using the four supplied
child graph proofs and capture-safe transport of both witness binders. -/
def mulTerm_ordered {α : Type} [DecidableEq α] (v : α → Nat)
    (t u : Peano.language.Term α) (old base out : Nat)
    (ho : old + 1 < base) (hout : out < old)
    (hvt : ∀ a ∈ t.varFinset, v a < old)
    (hvu : ∀ a ∈ u.varFinset, v a < old)
    (leftF : KDerivation (imp (termGraph v t old (old + 64)).encode
      (termGraph v t old (base + 64)).encode))
    (leftB : KDerivation (imp (termGraph v t old (base + 64)).encode
      (termGraph v t old (old + 64)).encode))
    (rightF : KDerivation (imp (termGraph v u (old + 1) (old + 64 + termCost t)).encode
      (termGraph v u (old + 1) (base + 64 + termCost t)).encode))
    (rightB : KDerivation (imp (termGraph v u (old + 1) (base + 64 + termCost t)).encode
      (termGraph v u (old + 1) (old + 64 + termCost t)).encode)) :
    KDerivation (imp (termGraph v (.func .mul ![t, u]) out old).encode
      (termGraph v (.func .mul ![t, u]) out base).encode) ×
    KDerivation (imp (termGraph v (.func .mul ![t, u]) out base).encode
      (termGraph v (.func .mul ![t, u]) out old).encode) := by
  have hmul := mulAt_base_alpha old base old (old + 1) out
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hrF := andF_transport _ _ _ _ rightF hmul.forward
  have hrB := andF_transport _ _ _ _ rightB hmul.backward
  have hiF : KDerivation (imp
      (andF (termGraph v t old (old + 64))
        (andF (termGraph v u (old + 1) (old + 64 + termCost t))
          (mulAt old old (old + 1) out))).encode
      (rebasedBody v t u old base out).encode) :=
    andF_transport _ _ _ _ leftF hrF
  have hiB : KDerivation (imp
      (rebasedBody v t u old base out).encode
      (andF (termGraph v t old (old + 64))
        (andF (termGraph v u (old + 1) (old + 64 + termCost t))
          (mulAt old old (old + 1) out))).encode) :=
    andF_transport _ _ _ _ leftB hrB
  have ha := rebased_exists_alpha v t u old base out ho hout hvt hvu
  have heF := compose (existsCongr old (existsCongr (old + 1) hiF)) ha.forward
  have heB := compose ha.backward (existsCongr old (existsCongr (old + 1) hiB))
  have hdF := domainAt_transport old base out (by omega) (by omega)
  have hdB := domainAt_transport base old out (by omega) (by omega)
  constructor
  · change KDerivation (imp (andF (domainAt old out) (.ex old (.ex (old + 1)
        (andF (termGraph v t old (old + 64))
          (andF (termGraph v u (old + 1) (old + 64 + termCost t))
            (mulAt old old (old + 1) out)))))).encode
      (andF (domainAt base out) (.ex base (.ex (base + 1)
        (rebasedBody v t u base base out)))).encode)
    exact andF_transport _ _ _ _ hdF heF
  · change KDerivation (imp (andF (domainAt base out) (.ex base (.ex (base + 1)
        (rebasedBody v t u base base out)))).encode
      (andF (domainAt old out) (.ex old (.ex (old + 1)
        (andF (termGraph v t old (old + 64))
          (andF (termGraph v u (old + 1) (old + 64 + termCost t))
            (mulAt old old (old + 1) out)))))).encode)
    exact andF_transport _ _ _ _ hdB heB

/-- Both original witness labels lie below this common higher block. -/
def intermediateBase (b c : Nat) : Nat := max b c + 2

/-- Arbitrary-base multiplication-node transport, conditional on the eight
actual child K proofs at the two original witness pairs and common high bases. -/
def mulTerm_base_transport {α : Type} [DecidableEq α] (v : α → Nat)
    (t u : Peano.language.Term α) (b c out : Nat)
    (hbo : out < b) (hco : out < c)
    (hbt : ∀ a ∈ t.varFinset, v a < b) (hct : ∀ a ∈ t.varFinset, v a < c)
    (hbu : ∀ a ∈ u.varFinset, v a < b) (hcu : ∀ a ∈ u.varFinset, v a < c)
    (blF : KDerivation (imp (termGraph v t b (b + 64)).encode
      (termGraph v t b (intermediateBase b c + 64)).encode))
    (blB : KDerivation (imp (termGraph v t b (intermediateBase b c + 64)).encode
      (termGraph v t b (b + 64)).encode))
    (brF : KDerivation (imp (termGraph v u (b + 1) (b + 64 + termCost t)).encode
      (termGraph v u (b + 1) (intermediateBase b c + 64 + termCost t)).encode))
    (brB : KDerivation (imp (termGraph v u (b + 1) (intermediateBase b c + 64 + termCost t)).encode
      (termGraph v u (b + 1) (b + 64 + termCost t)).encode))
    (clF : KDerivation (imp (termGraph v t c (c + 64)).encode
      (termGraph v t c (intermediateBase b c + 64)).encode))
    (clB : KDerivation (imp (termGraph v t c (intermediateBase b c + 64)).encode
      (termGraph v t c (c + 64)).encode))
    (crF : KDerivation (imp (termGraph v u (c + 1) (c + 64 + termCost t)).encode
      (termGraph v u (c + 1) (intermediateBase b c + 64 + termCost t)).encode))
    (crB : KDerivation (imp (termGraph v u (c + 1) (intermediateBase b c + 64 + termCost t)).encode
      (termGraph v u (c + 1) (c + 64 + termCost t)).encode)) :
    KDerivation (imp (termGraph v (.func .mul ![t, u]) out b).encode
      (termGraph v (.func .mul ![t, u]) out c).encode) ×
    KDerivation (imp (termGraph v (.func .mul ![t, u]) out c).encode
      (termGraph v (.func .mul ![t, u]) out b).encode) := by
  have hbd : b + 1 < intermediateBase b c := by unfold intermediateBase; omega
  have hcd : c + 1 < intermediateBase b c := by unfold intermediateBase; omega
  have hb := mulTerm_ordered v t u b (intermediateBase b c) out hbd hbo hbt hbu blF blB brF brB
  have hc := mulTerm_ordered v t u c (intermediateBase b c) out hcd hco hct hcu clF clB crF crB
  exact ⟨compose hb.1 hc.2, compose hc.1 hb.2⟩

theorem mulTerm_base_transport_certificates {α : Type} [DecidableEq α] (v : α → Nat)
    (t u : Peano.language.Term α) (b c out : Nat)
    (hbo : out < b) (hco : out < c)
    (hbt : ∀ a ∈ t.varFinset, v a < b) (hct : ∀ a ∈ t.varFinset, v a < c)
    (hbu : ∀ a ∈ u.varFinset, v a < b) (hcu : ∀ a ∈ u.varFinset, v a < c)
    (blF : KDerivation (imp (termGraph v t b (b + 64)).encode
      (termGraph v t b (intermediateBase b c + 64)).encode))
    (blB : KDerivation (imp (termGraph v t b (intermediateBase b c + 64)).encode
      (termGraph v t b (b + 64)).encode))
    (brF : KDerivation (imp (termGraph v u (b + 1) (b + 64 + termCost t)).encode
      (termGraph v u (b + 1) (intermediateBase b c + 64 + termCost t)).encode))
    (brB : KDerivation (imp (termGraph v u (b + 1) (intermediateBase b c + 64 + termCost t)).encode
      (termGraph v u (b + 1) (b + 64 + termCost t)).encode))
    (clF : KDerivation (imp (termGraph v t c (c + 64)).encode
      (termGraph v t c (intermediateBase b c + 64)).encode))
    (clB : KDerivation (imp (termGraph v t c (intermediateBase b c + 64)).encode
      (termGraph v t c (c + 64)).encode))
    (crF : KDerivation (imp (termGraph v u (c + 1) (c + 64 + termCost t)).encode
      (termGraph v u (c + 1) (intermediateBase b c + 64 + termCost t)).encode))
    (crB : KDerivation (imp (termGraph v u (c + 1) (intermediateBase b c + 64 + termCost t)).encode
      (termGraph v u (c + 1) (c + 64 + termCost t)).encode)) :
    theoremCode (certificate (mulTerm_base_transport v t u b c out hbo hco hbt hct hbu hcu
      blF blB brF brB clF clB crF crB).1) =
        imp (termGraph v (.func .mul ![t, u]) out b).encode
          (termGraph v (.func .mul ![t, u]) out c).encode ∧
    theoremCode (certificate (mulTerm_base_transport v t u b c out hbo hco hbt hct hbu hcu
      blF blB brF brB clF clB crF crB).2) =
        imp (termGraph v (.func .mul ![t, u]) out c).encode
          (termGraph v (.func .mul ![t, u]) out b).encode :=
  ⟨certificate_correct _, certificate_correct _⟩

end PASoundness.PAtoCompactMulTermTransport

#print axioms PASoundness.PAtoCompactMulTermTransport.mulTerm_ordered
#print axioms PASoundness.PAtoCompactMulTermTransport.mulTerm_base_transport
#print axioms PASoundness.PAtoCompactMulTermTransport.mulTerm_base_transport_certificates
