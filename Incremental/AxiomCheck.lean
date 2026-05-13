import Incremental.Busy
import Incremental.LessBusy
import Incremental.Shake.Standard

/-! Ensure `Classical.choice` does not sneak in -/

/--
info:
'Incremental.Busy' does not depend on any axioms
-/
#guard_msgs in
#print axioms Incremental.Busy

/--
info:
'Incremental.LessBusy' depends on axioms: [propext, Quot.sound, Incremental.Task.Monad.freeTheorem]
-/
#guard_msgs in
#print axioms Incremental.LessBusy

/--
info:
'Incremental.Shake' depends on axioms: [propext, Quot.sound, Incremental.Task.Monad.freeTheorem]
-/
#guard_msgs in
#print axioms Incremental.Shake
