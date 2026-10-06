import P23.Artin.CanonicalRelations
import P23.Artin.MixedTraceObstructions
import P23.Artin.PureTraceObstructions

/-!
# Run 10 symbolic regression

This file exercises the generic canonical-relation engine and every exact
mixed/pure survivor-family obstruction authorized for Run 10.
-/

open P23.OneTie
open P23.Artin

#check dual_relation_of_common_quotient
#check coeff_transfer_of_dual_relation
#check coeff_transfer_of_common_quotient
#check coeff_eq_zero_of_annihilator

#check mixedYZ_y_not_mem_trace
#check mixedYQ_y_not_mem_trace
#check mixedZP_z_not_mem_trace
#check mixedPQ_y_not_mem_trace_of_u_gt_one
#check mixedPQ_z_not_mem_trace_of_v_gt_one
#check mixedPQ_not_variablesInTrace

#check p4Z_z_not_mem_trace
#check p4Z_not_variablesInTrace
#check p5Z_z_not_mem_trace
#check p5Z_not_variablesInTrace
#check CanonicalTraceObstructions
#check canonicalTraceObstructions

/-! The concrete calls below pin the load-bearing endpoint and
nonprimitive parameter regimes. -/

example : True := by
  have := mixedYZ_y_not_mem_trace (k := ℚ) (a := 2) (u := 1) (v := 1)
    (by omega) (by omega) (by omega)
  trivial

-- M4/YQ: h = r+1 = 1.
example : True := by
  have := mixedYQ_y_not_mem_trace (k := ℚ)
    (a := 4) (b := 2) (r := 0) (u := 2) (v := 1)
    (by omega) (by omega) (by omega) (by omega) (by omega)
  trivial

-- M4/YQ: h = r+1 = a-1.
example : True := by
  have := mixedYQ_y_not_mem_trace (k := ℚ)
    (a := 4) (b := 2) (r := 2) (u := 2) (v := 1)
    (by omega) (by omega) (by omega) (by omega) (by omega)
  trivial

-- M4/YQ at a = 2 (both endpoint regimes coincide).
example : True := by
  have := mixedYQ_y_not_mem_trace (k := ℚ)
    (a := 2) (b := 1) (r := 0) (u := 1) (v := 1)
    (by omega) (by omega) (by omega) (by omega) (by omega)
  trivial

example : True := by
  have := mixedZP_z_not_mem_trace (k := ℚ)
    (a := 3) (c := 2) (r := 1) (u := 1) (v := 2)
    (by omega) (by omega) (by omega) (by omega) (by omega)
  trivial

-- M5/PQ, u > 1 branch.
example : True := by
  have := mixedPQ_y_not_mem_trace_of_u_gt_one (k := ℚ)
    (a := 3) (b := 1) (c := 1) (u := 2) (v := 1)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  trivial

-- M5/PQ, v > 1 branch.
example : True := by
  have := mixedPQ_z_not_mem_trace_of_v_gt_one (k := ℚ)
    (a := 3) (b := 1) (c := 1) (u := 1) (v := 2)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  trivial

-- Nonprimitive tie parameters.
example : True := by
  have := mixedPQ_not_variablesInTrace (k := ℚ)
    (a := 4) (b := 2) (c := 2) (u := 3) (v := 2)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (mixedPQ_isLiveTie (by omega) (by omega) (by omega) (by omega) (by omega))
  trivial

-- P4Z at V = 1 and b = 2.
example : True := by
  have := p4Z_z_not_mem_trace (k := ℚ) (a := 2) (b := 2) (V := 1)
    (by omega) (by omega) (by omega)
  trivial

-- P5Z at v = 1.
example : True := by
  have := p5Z_z_not_mem_trace (k := ℚ) (a := 2) (b := 2) (v := 1)
    (by omega) (by omega) (by omega)
  trivial

