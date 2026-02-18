module
import Leanduction.NestedPositivity
import Leanduction.SparseParametricity
import Leanduction.SparseRecursor
public meta import Lean.Util.Trace

meta initialize
  Lean.registerTraceClass `Leanduction (inherited := true)
