import PASoundness.PAtoCompactAdditionOutputArbitraryBases
import PASoundness.PAtoCompactAdditionOutputAllocatedFixed

/-! Specialize the supplied fixed-label proof to arbitrary names and a common
allocator. The K proof-data transformation is noncomputable. This relation
lemma does not itself construct term-graph output transport. -/
namespace PASoundness.PAtoCompactAdditionOutputUniformRelation
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactAdditionOutputFrame
open PASoundness.PAtoCompactAdditionOutputArbitraryBases PASoundness.PAtoCompactAdditionOutputAllocatedFixed
set_option maxRecDepth 262144
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The supplied source addition and four domain guards transport across the
output equivalence at any allocator whose private binders avoid the four free
names. All displayed names and their denoted objects may coincide. -/
noncomputable def output_relation (b x y q r : Nat)
    (hx : x < b + 2) (hy : y < b + 2) (hq : q < b + 2) (hr : r < b + 2) :
    KDerivation (imp (addAt b x y q).encode (imp (domainAt b q).encode
      (imp (domainAt b r).encode (imp (domainAt b y).encode
        (imp (domainAt b x).encode (imp (equivAt b q r).encode (addAt b x y r).encode)))))) := by
  have hfixed : KDerivation (frame 100 30 31 32 8).encode := by
    simpa only [frame,Formula.encode] using allocated_output_fixed
  exact output_at_independent_bases b b b b b b b x y q r
    (by omega) (by omega) (by omega) (by omega)
    hx hy hq hq hr hx hy hr hfixed

theorem output_relation_certificate (b x y q r : Nat)
    (hx : x < b + 2) (hy : y < b + 2) (hq : q < b + 2) (hr : r < b + 2) :
    theoremCode (certificate (output_relation b x y q r hx hy hq hr)) =
      imp (addAt b x y q).encode (imp (domainAt b q).encode
        (imp (domainAt b r).encode (imp (domainAt b y).encode
          (imp (domainAt b x).encode (imp (equivAt b q r).encode (addAt b x y r).encode))))) :=
  certificate_correct _
end PASoundness.PAtoCompactAdditionOutputUniformRelation

#print axioms PASoundness.PAtoCompactAdditionOutputUniformRelation.output_relation
#print axioms PASoundness.PAtoCompactAdditionOutputUniformRelation.output_relation_certificate
