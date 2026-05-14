import Incremental.Busy
import Incremental.LessBusy
import Incremental.Shake.Standard
import Incremental.Shake.Trace
import Incremental.Shake.Cancel

/--
info: 'Incremental.MTasks.freeTheorem' does not depend on any axioms
-/
#guard_msgs in
#print axioms Incremental.MTasks.freeTheorem

/--
info: 'Incremental.Busy' does not depend on any axioms
-/
#guard_msgs in
#print axioms Incremental.Busy

/--
info: 'Incremental.LessBusy' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Incremental.LessBusy

/--
info: 'Incremental.Shake' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Incremental.Shake

/--
info: 'Incremental.ShakeTrace' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Incremental.ShakeTrace

/--
info: 'Incremental.ShakeCancel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Incremental.ST.instLawfulMonad,
 Incremental.ST.lawfulMonadAttach]
-/
#guard_msgs in
#print axioms Incremental.ShakeCancel
