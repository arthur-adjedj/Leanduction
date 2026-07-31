module
public meta import Leanduction.NestedPositivity
public meta import Leanduction.SparseParametricity
public meta import Leanduction.SparseRecursor
public meta import Lean.Util.Trace

meta initialize
  Lean.registerTraceClass `Leanduction (inherited := true)
