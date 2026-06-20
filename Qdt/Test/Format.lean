import Qdt.Test

open Qdt

#fmt ( def f := fun x => x ) ↦ ( def f := fun x => x )
#fmt ( def f := fun x y => x ) ↦ ( def f := fun x y => x )
#fmt ( def f := fun (x) => x ) ↦ ( def f := fun x => x )
#fmt ( def f := fun (x y) => x ) ↦ ( def f := fun x y => x )
#fmt ( def f := fun (a) (b) => a ) ↦ ( def f := fun a b => a )

#fmt ( def f := fun (x : X) => x ) ↦ ( def f := fun x : X => x )
#fmt ( def f := fun (x y : X) => x ) ↦ ( def f := fun x y : X => x )

#fmt ( def f := fun (x : X) (y : Y) => x ) ↦ ( def f := fun (x : X) (y : Y) => x )
#fmt ( def f := fun (x : X) (y : X) => x ) ↦ ( def f := fun (x : X) (y : X) => x )
#fmt ( def f := fun (x : X) y => x ) ↦ ( def f := fun (x : X) y => x )
#fmt ( def f := fun (x) (y : Y) => x ) ↦ ( def f := fun x (y : Y) => x )

#fmt ( def f := fun {x : X} => x ) ↦ ( def f := fun {x : X} => x )
#fmt ( def f := fun {x y : X} => x ) ↦ ( def f := fun {x y : X} => x )
#fmt ( def f := fun {x} => x ) ↦ ( def f := fun {x} => x )
#fmt ( def f := fun {x y} => x ) ↦ ( def f := fun {x y} => x )

#fmt ( def f (x) := x ) ↦ ( def f x := x )
#fmt ( def f (x y) := x ) ↦ ( def f x y := x )
#fmt ( def f (a) (b) := a ) ↦ ( def f a b := a )
#fmt ( def f a b := a ) ↦ ( def f a b := a )

#fmt ( def f (x : X) := x ) ↦ ( def f (x : X) := x )
#fmt ( def f (x y : X) := x ) ↦ ( def f (x y : X) := x )
#fmt ( def f (x : X) (y : Y) := x ) ↦ ( def f (x : X) (y : Y) := x )

#fmt ( def f {x : X} := x ) ↦ ( def f {x : X} := x )
#fmt ( def f {x} := x ) ↦ ( def f {x} := x )
