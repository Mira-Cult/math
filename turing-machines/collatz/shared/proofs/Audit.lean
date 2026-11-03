import CollatzTM

/- Reproducible theorem-type and transitive axiom audits. -/
#check CollatzTM.M12.canonicalNat_one
#check CollatzTM.M12.canonicalNat_even
#check CollatzTM.M12.canonicalNat_odd
#check CollatzTM.M12.Binary.bitlength_eq_log2
#check CollatzTM.M12.halts_iff_collatz
#check CollatzTM.M12.totality_iff_collatz
#check CollatzTM.M16.init_exact
#check CollatzTM.M16.reset_pos
#check CollatzTM.M16.even_macro_pos
#check CollatzTM.M16.odd_macro
#check CollatzTM.M16.odd_macro_halt_exact
#check CollatzTM.M16.halts_iff_shortcut_cycle
#check CollatzTM.M16.halts_iff_ordinary_cycle
#check CollatzTM.Arithmetic.exists_top
#check CollatzTM.Arithmetic.counter_iff

#print axioms CollatzTM.TableAudit.twelve_table_exact
#print axioms CollatzTM.TableAudit.sixteen_table_exact
#print axioms CollatzTM.TableAudit.twelve_halt_transition
#print axioms CollatzTM.TableAudit.sixteen_halt_transition
#print axioms CollatzTM.finiteTape_run
#print axioms CollatzTM.M12.canonicalNat_one
#print axioms CollatzTM.M12.canonicalNat_even
#print axioms CollatzTM.M12.canonicalNat_odd
#print axioms CollatzTM.M12.canonicalNat_finite
#print axioms CollatzTM.M12.Binary.bitlength_eq_log2
#print axioms CollatzTM.M12.evaluatorSpec
#print axioms CollatzTM.M12.halts_iff_collatz
#print axioms CollatzTM.M12.totality_iff_collatz
#print axioms CollatzTM.M16.init_exact
#print axioms CollatzTM.M16.canonical_finite
#print axioms CollatzTM.M16.reset_pos
#print axioms CollatzTM.M16.even_macro_pos
#print axioms CollatzTM.M16.odd_macro
#print axioms CollatzTM.M16.odd_macro_halt_exact
#print axioms CollatzTM.M16.machine_spec
#print axioms CollatzTM.M16.halts_iff_shortcut_cycle
#print axioms CollatzTM.M16.halts_iff_ordinary_cycle
#print axioms CollatzTM.Arithmetic.exists_top
#print axioms CollatzTM.Arithmetic.counter_iff
