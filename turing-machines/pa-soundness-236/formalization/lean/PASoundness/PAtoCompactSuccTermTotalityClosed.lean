import PASoundness.PAtoCompactSuccTermTotality
import PASoundness.PAtoCompactSuccessorQuotientExistence

/-! Successor-term totality from a child existence derivation. The
candidate-preserving quotient-successor construction is now internal to K;
the only remaining proof-data premise is the child existence derivation. -/
namespace PASoundness.PAtoCompactSuccTermTotalityClosed

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactSuccTermTotality
open PASoundness.PAtoCompactSuccessorQuotientExistence

/-- Given an actual K child-existence proof under `g`, construct an actual K
successor-term existence proof under the same `g`. Freshness concerns only
syntactic names; no distinctness of represented values is required. -/
def succ_total_from_fresh_child {α : Type} [DecidableEq α] (v : α → Nat)
    (t : Peano.language.Term α) (b out x : Nat) (g : CompactNamed.Formula)
    (hout : out < b) (hx : x < b) (hxo : x ≠ out)
    (hv : ∀ a ∈ t.varFinset, v a < b)
    (hxv : ∀ a ∈ t.varFinset, v a ≠ x)
    (hov : ∀ a ∈ t.varFinset, v a ≠ out)
    (hxg : x ∉ g.free) (hog : out ∉ g.free)
    (child : KDerivation (imp g.encode
      (existsCode x (termGraph v t x (b+64)).encode))) :
    KDerivation (imp g.encode (existsCode out (termGraph v (.func .succ ![t]) out b).encode)) :=
  PAtoCompactSuccTermTotality.succ_total_from_fresh_child v t b out x g hout hx hxo hv
    hxv hov hxg hog child (quotient_successor_exists b x out (by omega) hout hxo)

theorem succ_total_from_fresh_child_certificate {α : Type} [DecidableEq α] (v : α → Nat)
    (t : Peano.language.Term α) (b out x : Nat) (g : CompactNamed.Formula)
    (hout : out < b) (hx : x < b) (hxo : x ≠ out)
    (hv : ∀ a ∈ t.varFinset, v a < b)
    (hxv : ∀ a ∈ t.varFinset, v a ≠ x)
    (hov : ∀ a ∈ t.varFinset, v a ≠ out)
    (hxg : x ∉ g.free) (hog : out ∉ g.free)
    (child : KDerivation (imp g.encode
      (existsCode x (termGraph v t x (b+64)).encode))) :
    theoremCode (certificate (succ_total_from_fresh_child v t b out x g hout hx hxo hv
      hxv hov hxg hog child)) =
      imp g.encode (existsCode out (termGraph v (.func .succ ![t]) out b).encode) :=
  certificate_correct _

end PASoundness.PAtoCompactSuccTermTotalityClosed

#print axioms PASoundness.PAtoCompactSuccTermTotalityClosed.succ_total_from_fresh_child
#print axioms PASoundness.PAtoCompactSuccTermTotalityClosed.succ_total_from_fresh_child_certificate
