import Qdt.Test

#pass (
  inductive Eq.{u} {α : Type u} : α → α → Type u where
    | refl (a : α) : Eq a a

  def rec.{w, u}
      (α : Type u)
      (a : α)
      (motive : (b : α) → Eq.{u} a b → Type w)
      (refl : motive a (Eq.refl.{u} a))
      (b : α)
      (h : Eq.{u} a b) :
      motive b h :=
    @Eq.rec.{w, u} α a motive refl b h
)

#pass (
  inductive Pair.{u} {α : Type u} : α → α → Type u where
    | mk (a : α) (b : α) : Pair a b

  def mkExp.{u} (α : Type u) (a b : α) : Pair.{u} a b := Pair.mk.{u} a b

  def rec.{w, u}
      (α : Type u)
      (a b : α)
      (motive : Pair.{u} a b → Type w)
      (mk : motive (Pair.mk.{u} a b))
      (h : Pair.{u} a b) :
      motive h :=
    @Pair.rec.{w, u} α a b motive mk h
)

#pass (
  inductive Diag.{u} {α : Type u} : α → α → Type u where
    | mk (a : α) : Diag a a

  def rec.{w, u}
      (α : Type u)
      (a : α)
      (motive : (b : α) → Diag.{u} a b → Type w)
      (mk : motive a (Diag.mk.{u} a))
      (b : α)
      (h : Diag.{u} a b) :
      motive b h :=
    @Diag.rec.{w, u} α a motive mk b h
)

#pass (
  inductive HEq.{u} {α : Type u} : α → α → Type u where
    | refl {a : α} : HEq a a

  def rec.{w, u}
      (α : Type u)
      (a : α)
      (motive : (b : α) → HEq.{u} a b → Type w)
      (refl : motive a (@HEq.refl.{u} α a))
      (b : α)
      (h : HEq.{u} a b) :
      motive b h :=
    @HEq.rec.{w, u} α a motive refl b h
)

#pass (
  inductive Bar : Type where
    | val

  inductive Foo : Bar → Type where
    | mk : Foo Bar.val

  def rec.{w}
      (motive : (b : Bar) → Foo b → Type w)
      (mk : motive Bar.val Foo.mk)
      (b : Bar)
      (f : Foo b) :
      motive b f :=
    @Foo.rec.{w} motive mk b f
)

#pass (
  inductive Swap.{u} {α : Type u} : α → α → Type u where
    | mk (a b : α) : Swap b a

  def rec.{w, u}
      (α : Type u)
      (motive : (x y : α) → Swap.{u} x y → Type w)
      (mk : (a b : α) → motive b a (Swap.mk.{u} a b))
      (x y : α)
      (s : Swap.{u} x y) :
      motive x y s :=
    @Swap.rec.{w, u} α motive mk x y s
)

#pass (
  inductive Acc.{u, v} (α : Type u) (r : α → α → Type v) : α → Type (max u v) where
    | intro (x : α) (h : (y : α) → r y x → Acc α r y) : Acc α r x

  def rec.{w, u, v}
      (α : Type u)
      (r : α → α → Type v)
      (motive : (a : α) → Acc.{u, v} α r a → Type w)
      (intro :
        (x : α) → (h : (y : α) → r y x → Acc.{u, v} α r y) →
        ((y : α) → (a : r y x) → motive y (h y a)) → motive x (Acc.intro.{u, v} x h))
      (a : α)
      (t : Acc.{u, v} α r a) :
      motive a t :=
    @Acc.rec.{w, u, v} α r motive intro a t
)

#pass (
  inductive Sym.{u} {α : Type u} : α → Type u where
    | left (a : α) : Sym a
    | right (a : α) : Sym a

  def rec.{w, u}
      (α : Type u)
      (a : α)
      (motive : Sym.{u} a → Type w)
      (left : motive (Sym.left.{u} a))
      (right : motive (Sym.right.{u} a))
      (s : Sym.{u} a) :
      motive s :=
    @Sym.rec.{w, u} α a motive left right s
)

#pass (
  inductive Nat : Type where
    | zero
    | succ (n : Nat)

  inductive Mixed : Nat → Type where
    | nil : Mixed Nat.zero
    | wrap (n : Nat) : Mixed n

  def rec.{w}
      (motive : (n : Nat) → Mixed n → Type w)
      (nil : motive Nat.zero Mixed.nil)
      (wrap : (n : Nat) → motive n (Mixed.wrap n))
      (n : Nat)
      (m : Mixed n) :
      motive n m :=
    @Mixed.rec.{w} motive nil wrap n m
)

#pass (
  inductive Box.{u} (α : Type u) : Type u where
    | mk (a : α) : Box α

  def rec.{w, u}
      (α : Type u)
      (motive : Box.{u} α → Type w)
      (mk : (a : α) → motive (Box.mk.{u} a))
      (b : Box.{u} α) :
      motive b :=
    @Box.rec.{w, u} α motive mk b
)

#pass (
  inductive Color : Type where
    | red
    | blue

  inductive Tag : Color → Type where
    | mkRed : Tag Color.red
    | mkBlue : Tag Color.blue

  def rec.{w}
      (motive : (c : Color) → Tag c → Type w)
      (mkRed : motive Color.red Tag.mkRed)
      (mkBlue : motive Color.blue Tag.mkBlue)
      (c : Color)
      (t : Tag c) :
      motive c t :=
    @Tag.rec.{w} motive mkRed mkBlue c t
)

#pass (
  inductive Nat : Type where
    | zero
    | succ (n : Nat)

  inductive Vec.{u} (α : Type u) : Nat → Type u where
    | nil : Vec α Nat.zero
    | cons (n : Nat) (a : α) (xs : Vec α n) : Vec α (Nat.succ n)

  def rec.{w, u}
      (α : Type u)
      (motive : (n : Nat) → Vec.{u} α n → Type w)
      (nil : motive Nat.zero (@Vec.nil.{u} α))
      (cons :
        (n : Nat) → (a : α) → (xs : Vec.{u} α n) → motive n xs →
        motive (Nat.succ n) (@Vec.cons.{u} α n a xs))
      (n : Nat)
      (v : Vec.{u} α n) :
      motive n v :=
    @Vec.rec.{w, u} α motive nil cons n v
)

#pass (
  inductive Sigma.{u} : (α : Type u) → α → Type (u + 1) where
    | mk (α : Type u) (a : α) : Sigma α a

  def rec.{w, u}
      (α : Type u)
      (a : α)
      (motive : Sigma.{u} α a → Type w)
      (mk : motive (Sigma.mk.{u} α a))
      (s : Sigma.{u} α a) :
      motive s :=
    @Sigma.rec.{w, u} α a motive mk s
)

#pass (
  inductive Eq.{u} {α : Type u} : α → α → Type u where
    | refl (a : α) : Eq a a

  def typeApp.{u} (α : Type u) (a b : α) : Type u := Eq.{u} a b

  def reflApp.{u} (α : Type u) (a : α) : Eq.{u} a a := Eq.refl.{u} a
)

#pass (
  inductive Two.{u} {α : Type u} : α → Type u where
    | mk1 (a : α) : Two a
    | mk2 {a : α} : Two a

  def useMk1.{u} (α : Type u) (a : α) : Two.{u} a := Two.mk1.{u} a
  def useMk2.{u} (α : Type u) (a : α) : Two.{u} a := @Two.mk2.{u} α a
)

#pass (
  inductive Color : Type where
    | red
    | green

  inductive Void : Color → Type where

  def rec.{w}
      (motive : (c : Color) → Void c → Type w)
      (c : Color)
      (v : Void c) :
      motive c v :=
    @Void.rec.{w} motive c v
)

#pass (
  inductive Endo.{u} {α : Type u} : (α → α) → Type u where
    | mk (f : α → α) : Endo f

  def rec.{w, u}
      (α : Type u)
      (f : α → α)
      (motive : Endo.{u} f → Type w)
      (mk : motive (Endo.mk.{u} f))
      (e : Endo.{u} f) :
      motive e :=
    @Endo.rec.{w, u} α f motive mk e
)

#pass (
  inductive Triple.{u} {α : Type u} : α → Type u where
    | a (x : α) : Triple x
    | b (x : α) : Triple x
    | c (x : α) : Triple x

  def rec.{w, u}
      (α : Type u)
      (x : α)
      (motive : Triple.{u} x → Type w)
      (a : motive (Triple.a.{u} x))
      (b : motive (Triple.b.{u} x))
      (c : motive (Triple.c.{u} x))
      (t : Triple.{u} x) :
      motive t :=
    @Triple.rec.{w, u} α x motive a b c t
)

#pass (
  inductive Partial.{u} {α : Type u} : α → α → Type u where
    | mk1 (a b : α) : Partial a b
    | mk2 (a : α) : Partial a a

  def rec.{w, u}
      (α : Type u)
      (a : α)
      (motive : (b : α) → Partial.{u} a b → Type w)
      (mk1 : (b : α) → motive b (Partial.mk1.{u} a b))
      (mk2 : motive a (Partial.mk2.{u} a))
      (b : α)
      (p : Partial.{u} a b) :
      motive b p :=
    @Partial.rec.{w, u} α a motive mk1 mk2 b p
)

#pass (
  inductive Eq3.{u} {α : Type u} : α → α → α → Type u where
    | refl (a : α) : Eq3 a a a

  def appType.{u} (α : Type u) (a b c : α) : Type u := Eq3.{u} a b c
  def appRefl.{u} (α : Type u) (a : α) : Eq3.{u} a a a := Eq3.refl.{u} a
)

#pass (
  inductive Foo.{u} (α : Type u) : α → Type u where
    | mk (a : α) : Foo α a

  def useMk.{u} (α : Type u) (a : α) : Foo.{u} α a := @Foo.mk.{u} α a

  def rec.{w, u}
      (α : Type u)
      (a : α)
      (motive : Foo.{u} α a → Type w)
      (mk : motive (@Foo.mk.{u} α a))
      (f : Foo.{u} α a) :
      motive f :=
    @Foo.rec.{w, u} α a motive mk f
)

#pass (
  inductive Five.{u} {α : Type u} : α → α → α → α → α → Type u where
    | mk (a b c d e : α) : Five a b c d e

  def rec.{w, u}
      (α : Type u)
      (a b c d e : α)
      (motive : Five.{u} a b c d e → Type w)
      (mk : motive (Five.mk.{u} a b c d e))
      (f : Five.{u} a b c d e) :
      motive f :=
    @Five.rec.{w, u} α a b c d e motive mk f
)

#pass (
  inductive Eq.{u} {α : Type u} : α → α → Type u where
    | refl (a : α) : Eq a a

  def usedAt0 (a : Type) (x : a) : Eq.{0} x x := Eq.refl.{0} x

  def usedAt1 (a : Type 1) (x : a) : Eq.{1} x x := Eq.refl.{1} x
)

#pass (
  inductive Foo.{u} {α : Type u} : α → Type u where
    | mk (a : α) : Foo a

  inductive Outer.{u} {α : Type u} : α → Type u where
    | wrap (a : α) (p : Foo.{u} a) : Outer a

  def useOuter.{u} (α : Type u) (a : α) (p : Foo.{u} a) : Outer.{u} a :=
    Outer.wrap.{u} a p

  def rec.{w, u}
      (α : Type u)
      (a : α)
      (motive : Outer.{u} a → Type w)
      (wrap : (p : Foo.{u} a) → motive (Outer.wrap.{u} a p))
      (o : Outer.{u} a) :
      motive o :=
    @Outer.rec.{w, u} α a motive wrap o
)

#pass (
  inductive Foo.{u} {α : Type u} : α → Type u where
    | mk (x : α) (a : α) : Foo a

  def useMk.{u} (α : Type u) (x a : α) : Foo.{u} a := @Foo.mk.{u} α x a

  def rec.{w, u}
      (α : Type u)
      (motive : (b : α) → Foo.{u} b → Type w)
      (mk : (x : α) → (a : α) → motive a (@Foo.mk.{u} α x a))
      (b : α)
      (f : Foo.{u} b) :
      motive b f :=
    @Foo.rec.{w, u} α motive mk b f
)
