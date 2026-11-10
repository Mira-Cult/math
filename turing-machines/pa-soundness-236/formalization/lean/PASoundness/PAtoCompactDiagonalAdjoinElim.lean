import PASoundness.PAtoCompactPointAdjoin

/-! A concrete K point-adjunction witness for the diagonal successor step.
It constructs one extension of the supplied old graph by the supplied pair
point, with the graph output bound at name 7. This alone does not build the
point, an identity graph, or a graph-collection operator. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactDiagonalAdjoinElim
open PASoundness.CompactProof PASoundness.PAtoCompactPointAdjoin

/-- For any values assigned to graph name 6 and point name 8, K proves a graph
exists at name 7 whose name-19 membership test is the exact adjunction graph. -/
def fixed_adjoin_exists : KDerivation (existsCode 7 (adjoinCode 6 8 7 19)) :=
  let hc := PAtoCompactPointAdjoinSelector.predicate_names_lt 6 8 30
  adjoin_graph_exists_fresh 6 8 30 19 7
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by omega) (by decide) (by decide) (by decide) (by decide) (by omega)

theorem fixed_adjoin_exists_certificate :
    theoremCode (certificate fixed_adjoin_exists) = existsCode 7 (adjoinCode 6 8 7 19) :=
  certificate_correct fixed_adjoin_exists

end PASoundness.PAtoCompactDiagonalAdjoinElim

#print axioms PASoundness.PAtoCompactDiagonalAdjoinElim.fixed_adjoin_exists
#print axioms PASoundness.PAtoCompactDiagonalAdjoinElim.fixed_adjoin_exists_certificate
