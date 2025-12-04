set_option autoImplicit false

inductive E {α : Type} : α → α → Type where
  | refl (a : α) : E a a

infix:50 (priority := high) " = " => E

def Even := (n k : Int) × E n (k + k)

def funex (A : Type) (B : A → Type) (f g : (x : A) → B x) (h : (x : A) → E (f x) (g x)) : E f g := sorry
def funext_nd (A B : Type) (f g : A → B) (h : (x : A) → E (f x) (g x)) : E f g := funex A (fun _ => B) f g h

def compose (A B C : Type) (g : B → C) (f : A → B) : A → C := fun x => g (f x)
def refl := @E.refl
def eq_rec (A : Type) (a : A) (motive : (b : A) → a = b → Type) (rfl : motive a (refl a)) (b : A) (t : a = b) : motive b t := sorry
def eq_ndrec (A : Type) (a : A) (motive : A → Type) (rfl : motive a) (b : A) (t : a = b) : motive b := eq_rec A a (fun b _ => motive b) rfl b t
def eq_subst (A : Type) (motive : A → Type) (a b : A) (h : a = b) (ha : motive a) : motive b := eq_ndrec A a motive ha b h
def eq_symm (A : Type) (a b : A) (hab : a = b) : b = a := eq_subst A (fun x => x = a) a b hab (refl a)
def eq_trans (A : Type) (a b c : A) (hab : a = b) (hbc : b = c) : a = c := eq_subst A (fun x => a = x) b c hbc hab
def congr_arg (A B : Type) (f : A → B) (x y : A) (e : x = y) : f x = f y := eq_subst A (fun z => f x = f z) x y e (refl (f x))
def foo2 (B : Type) (f : Unit → B) : f = (fun _ => f ()) := refl f


def eta_sigma1 (A : Type) (B : A → Type) (p : (a : A) × B a) : p = ⟨p.fst, p.snd⟩ := refl p
def eta_sigma2 (A : Type) (B : A → Type) (p : (a : A) × B a) : ⟨p.fst, p.snd⟩ = p := refl p


def Isomorphism (A B : Type) :=
  (hom : A → B) ×
  (inv : B → A) ×
  compose A B A inv hom = @id A ×
  compose B A B hom inv = @id B

def eq_ext (A : Type) (a b : A) (h1 h2 : a = b) : h1 = h2 := sorry

def foo (A B : Type) (p : A × B) : (p.fst, p.snd) = p := refl p


def fst {A : Type} {B : A → Type} := @Sigma.fst A B
def snd {A : Type} {B : A → Type} := @Sigma.snd A B

def int_iso_even : Isomorphism Int Even :=
  let hom : Int → Even := fun k => ⟨k + k, ⟨k, refl (k + k)⟩⟩;
  let inv : Even → Int := fun e => fst (snd e);
  ⟨hom,
   inv,
   refl (@id Int),
   funext_nd Even Even (compose Even Int Even hom inv) id
     (fun e =>
      let n := fst e;
      let k := fst (snd e);
      let k2 := k + k;
      let hnk := snd (snd e);
      let hkn := eq_symm Int n k2 hnk;
      eq_trans Even (hom k) ⟨n, ⟨k, eq_symm Int k2 n hkn⟩⟩ e
        (eq_rec Int k2
          (fun y p => hom k = ⟨y, ⟨k, eq_symm Int k2 y p⟩⟩)
          (eq_symm Even ⟨k2, ⟨k, eq_symm Int k2 k2 (refl k2)⟩⟩ ⟨k2, ⟨k, refl k2⟩⟩
            (congr_arg (k2 = k2) Even
              (fun p => ⟨k2, ⟨k, p⟩⟩)
              (eq_symm Int k2 k2 (refl k2))
              (refl k2)
              (eq_ext Int k2 k2 (eq_symm Int k2 k2 (refl k2)) (refl k2))))
          n hkn)
        (congr_arg (n = k2) Even
          (fun p => ⟨n, ⟨k, p⟩⟩)
          (eq_symm Int k2 n hkn)
          hnk
          (eq_ext Int n k2 (eq_symm Int k2 n hkn) hnk)))
  ⟩
