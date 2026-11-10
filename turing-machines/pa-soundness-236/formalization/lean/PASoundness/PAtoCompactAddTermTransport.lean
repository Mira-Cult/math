import PASoundness.PAtoCompactAddTermBody
import PASoundness.PAtoCompactAddBaseMultiAlpha
import PASoundness.PAtoCompactZeroTermBaseTransport

/-! Conditional finite K transport for an addition term node. The two
recursive child graphs are transported at their existing output witnesses;
all child transports are explicit finite K proof inputs. -/
namespace PASoundness.PAtoCompactAddTermTransport

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.CompactHilbertBasis PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactGuardBaseTransport PASoundness.PAtoCompactZeroTermBaseTransport
open PASoundness.PAtoCompactAddBaseMultiAlpha PASoundness.PAtoCompactAddTermBody

/-- A parent addition node moves to a higher base once the two child graphs
have been rebased at their original output names, in both K directions. -/
def addTerm_ordered {α : Type} [DecidableEq α] (v : α → Nat)
    (l r : Peano.language.Term α) (old base out : Nat)
    (ho : old + 1 < base) (hout : out < old)
    (hl : ∀ a ∈ l.varFinset, v a < old) (hr : ∀ a ∈ r.varFinset, v a < old)
    (leftF : KDerivation (imp (termGraph v l old (old + 64)).encode
      (termGraph v l old (base + 64)).encode))
    (leftB : KDerivation (imp (termGraph v l old (base + 64)).encode
      (termGraph v l old (old + 64)).encode))
    (rightF : KDerivation (imp (termGraph v r (old + 1) (old + 64 + termCost l)).encode
      (termGraph v r (old + 1) (base + 64 + termCost l)).encode))
    (rightB : KDerivation (imp (termGraph v r (old + 1) (base + 64 + termCost l)).encode
      (termGraph v r (old + 1) (old + 64 + termCost l)).encode)) :
    KDerivation (imp (termGraph v (.func .add ![l, r]) out old).encode
      (termGraph v (.func .add ![l, r]) out base).encode) ×
    KDerivation (imp (termGraph v (.func .add ![l, r]) out base).encode
      (termGraph v (.func .add ![l, r]) out old).encode) := by
  have hadd := addAt_base_alpha old base old (old + 1) out
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hiF : KDerivation (imp
      (andF (termGraph v l old (old + 64))
        (andF (termGraph v r (old + 1) (old + 64 + termCost l))
          (addAt old old (old + 1) out))).encode
      (rebasedBody v l r old (old + 1) base out).encode) :=
    andF_transport _ _ _ _ leftF (andF_transport _ _ _ _ rightF hadd.forward)
  have hiB : KDerivation (imp
      (rebasedBody v l r old (old + 1) base out).encode
      (andF (termGraph v l old (old + 64))
        (andF (termGraph v r (old + 1) (old + 64 + termCost l))
          (addAt old old (old + 1) out))).encode) :=
    andF_transport _ _ _ _ leftB (andF_transport _ _ _ _ rightB hadd.backward)
  have ha := rebased_exists_alpha v l r old base out ho hout hl hr
  have heF := compose (existsCongr old (existsCongr (old + 1) hiF)) ha.forward
  have heB := compose ha.backward (existsCongr old (existsCongr (old + 1) hiB))
  have hdF := domainAt_transport old base out (by omega) (by omega)
  have hdB := domainAt_transport base old out (by omega) (by omega)
  constructor
  · change KDerivation (imp (andF (domainAt old out) (.ex old (.ex (old + 1)
        (andF (termGraph v l old (old + 64))
          (andF (termGraph v r (old + 1) (old + 64 + termCost l))
            (addAt old old (old + 1) out)))))).encode
      (andF (domainAt base out) (.ex base (.ex (base + 1)
        (rebasedBody v l r base (base + 1) base out)))).encode)
    exact andF_transport _ _ _ _ hdF heF
  · change KDerivation (imp (andF (domainAt base out) (.ex base (.ex (base + 1)
        (rebasedBody v l r base (base + 1) base out)))).encode
      (andF (domainAt old out) (.ex old (.ex (old + 1)
        (andF (termGraph v l old (old + 64))
          (andF (termGraph v r (old + 1) (old + 64 + termCost l))
            (addAt old old (old + 1) out)))))).encode)
    exact andF_transport _ _ _ _ hdB heB

/-- A common third parent block strictly beyond both pairs of witnesses. -/
def intermediateBase (b c : Nat) : Nat := max b c + 2

/-- Arbitrary-base addition-node transport, conditional on actual K proofs
for both child graphs at each original witness and the common high block. -/
def addTerm_base_transport {α : Type} [DecidableEq α] (v : α → Nat)
    (l r : Peano.language.Term α) (b c out : Nat)
    (hbo : out < b) (hco : out < c)
    (hbl : ∀ a ∈ l.varFinset, v a < b) (hcl : ∀ a ∈ l.varFinset, v a < c)
    (hbr : ∀ a ∈ r.varFinset, v a < b) (hcr : ∀ a ∈ r.varFinset, v a < c)
    (blF : KDerivation (imp (termGraph v l b (b + 64)).encode
      (termGraph v l b (intermediateBase b c + 64)).encode))
    (blB : KDerivation (imp (termGraph v l b (intermediateBase b c + 64)).encode
      (termGraph v l b (b + 64)).encode))
    (brF : KDerivation (imp (termGraph v r (b + 1) (b + 64 + termCost l)).encode
      (termGraph v r (b + 1) (intermediateBase b c + 64 + termCost l)).encode))
    (brB : KDerivation (imp (termGraph v r (b + 1) (intermediateBase b c + 64 + termCost l)).encode
      (termGraph v r (b + 1) (b + 64 + termCost l)).encode))
    (clF : KDerivation (imp (termGraph v l c (c + 64)).encode
      (termGraph v l c (intermediateBase b c + 64)).encode))
    (clB : KDerivation (imp (termGraph v l c (intermediateBase b c + 64)).encode
      (termGraph v l c (c + 64)).encode))
    (crF : KDerivation (imp (termGraph v r (c + 1) (c + 64 + termCost l)).encode
      (termGraph v r (c + 1) (intermediateBase b c + 64 + termCost l)).encode))
    (crB : KDerivation (imp (termGraph v r (c + 1) (intermediateBase b c + 64 + termCost l)).encode
      (termGraph v r (c + 1) (c + 64 + termCost l)).encode)) :
    KDerivation (imp (termGraph v (.func .add ![l, r]) out b).encode
      (termGraph v (.func .add ![l, r]) out c).encode) ×
    KDerivation (imp (termGraph v (.func .add ![l, r]) out c).encode
      (termGraph v (.func .add ![l, r]) out b).encode) := by
  have hbd : b + 1 < intermediateBase b c := by unfold intermediateBase; omega
  have hcd : c + 1 < intermediateBase b c := by unfold intermediateBase; omega
  have hb := addTerm_ordered v l r b (intermediateBase b c) out hbd hbo hbl hbr blF blB brF brB
  have hc := addTerm_ordered v l r c (intermediateBase b c) out hcd hco hcl hcr clF clB crF crB
  exact ⟨compose hb.1 hc.2, compose hc.1 hb.2⟩

end PASoundness.PAtoCompactAddTermTransport

#print axioms PASoundness.PAtoCompactAddTermTransport.addTerm_ordered
#print axioms PASoundness.PAtoCompactAddTermTransport.addTerm_base_transport
