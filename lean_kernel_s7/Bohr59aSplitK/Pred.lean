import Bohr59aCoreK.FastArith3
import Bohr59aCoreK.TrigTab
import Bohr59aCoreK.AllP

/-!
# The link predicate of the split k = 7 modules (core Lean only)

`PF7 key`: the fast kernel vertex check (`vertexOKKpF3`, bound `2552/1000`) accepts `key` with some packed hint. The
generated link modules prove `allP PF7` over key chunks from the vertex theorems; the glue
(`Bohr59aSplitK/Glue7.lean`) turns it into the `∃ Y Wr x, vertexOKKh …` form of `boxOK_of_K2h`.
-/

namespace Bohr59aSplitK

open Bohr59aK Bohr59aCore

/-- some packed hint makes the fast kernel vertex check true (k = 7, bound 2552/1000) -/
def PF7 (key : List Comp) : Prop := ∃ n, vertexOKKpF3 trigTT 7 2552 1000 key n = true

end Bohr59aSplitK
