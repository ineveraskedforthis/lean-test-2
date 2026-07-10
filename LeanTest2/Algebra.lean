namespace algebra

universe u v w

@[simp]
def is_symmetric_2 {k : Type u}  (m : k → k → k) :=
  ∀ a, ∀ b, m a b = m b a

@[simp]
def is_left_identity {k : Type u} (m : k → k → k) (e : k) :=
  ∀ a, m e a = a

@[simp]
def is_right_identity {k : Type u} (m : k → k → k) (e : k) :=
  ∀ a, m a e = a

@[simp]
def is_associative {k : Type u} (m : k → k → k) :=
  ∀ a, ∀ b, ∀ c, m (m a b) c = m a (m b c)

@[simp]
def is_left_linear {k : Type u} (add : k → k → k) (mul: k → k → k) :=
  ∀ a, ∀ b, ∀ c, mul (add a b) c = add (mul a c) (mul b c)

@[simp]
def is_right_linear {k : Type u} (add : k → k → k) (mul: k → k → k) :=
  ∀ a, ∀ b, ∀ c, mul a (add b c) = add (mul a b) (mul a c)

@[simp]
def is_left_inverse {k : Type u} (m : k → k → k) (e : k) (inv: k → k) :=
  ∀ a, m (inv a) a =e

@[simp]
def is_right_inverse {k : Type u} (m : k → k → k) (e : k) (inv: k → k) :=
  ∀ a, m a (inv a) =e


theorem left_identity_is_right_identity
  (k : Type u)
  (m : k → k → k)
  (le : k)  (lmul_e_left : is_left_identity m le)
  (re : k)  (rmul_e_right : is_right_identity m re)
  :
  (le = re)
  := by
  rw [is_right_identity] at rmul_e_right
  rw [is_left_identity] at lmul_e_left
  have h := lmul_e_left re
  rw [←lmul_e_left re]
  rw [rmul_e_right]

class Pointed_Zero (k : Type u) where
  zero : k

class Additive (k : Type u) where
  add : k → k → k

class Multiplicative (k : Type u) where
  mul : k → k → k

class Pointed_Multiplicative_Identity (k : Type u) where
  e : k

infix:90 "⊹" => Additive.add
infix:95 "⋆" => Multiplicative.mul

class Commutative_Multiplicative (k : Type u) extends Multiplicative k where
  mul_is_comm (a b) : mul a b = mul b a

class Additive_Monoid (k : Type u) extends Pointed_Zero k, Additive k where
  add_zero_any (a : k) : add zero a = a
  add_any_zero (a : k) : add a zero = a
  add_is_assoc (a b c : k) : add (add a b) c = add a (add b c)

notation "⟨0⟩" => Pointed_Zero.zero
notation "⟨1⟩" => Pointed_Multiplicative_Identity.e

class Multiplicative_Monoid (k : Type u) extends Pointed_Multiplicative_Identity k, Multiplicative k where
  mul_any_e (a : k) : mul a e = a
  mul_e_any (a : k) : mul e a = a
  mul_is_assoc (a b c) : mul (mul a b) c = mul a (mul b c)

export Additive_Monoid (add_zero_any add_any_zero)
attribute [simp] add_zero_any add_any_zero

export Multiplicative_Monoid (mul_any_e mul_e_any)
attribute [simp] mul_any_e mul_e_any

class Commutative_Additive_Monoid (k : Type u) extends Additive_Monoid k where
  add_is_comm (a b : k) : add a b = add b a

class Commutative_Multiplicative_Monoid (k : Type u) extends Multiplicative_Monoid k, Commutative_Multiplicative k

class Ring (k : Type u) extends Commutative_Additive_Monoid k, Commutative_Multiplicative_Monoid k where
  add_inverse : k → k
  -- non_trivial : ¬ e = zero
  add_add_inverse_self : is_left_inverse add zero add_inverse
  mul_is_linear_left : is_left_linear add mul
  mul_is_linear_right : is_right_linear add mul


export Ring (add_add_inverse_self)
attribute [simp] add_add_inverse_self

class Ring_to_String (k : Type u) extends Ring k, ToString k

class function_wrapper (F : Type) (S T: outParam Type) where
  original_function : F → S → T

instance [function_wrapper F S T]
  : CoeFun F (fun _ ↦ S → T) where
  coe := function_wrapper.original_function
attribute [coe] function_wrapper.original_function

structure Additive_Monoid_hom₁
  (s : Type w) [Ms : Additive_Monoid s]
  (k : Type u) [Mk : Additive_Monoid k] where
  original_function : s → k
  map_zero : original_function Ms.zero = Mk.zero
  map_add (x y : s) : original_function (Ms.add x y) = Mk.add (original_function x) (original_function y)

attribute [simp] Additive_Monoid_hom₁.map_zero

instance
  [Additive_Monoid s] [Additive_Monoid k]
  : CoeFun (Additive_Monoid_hom₁ s k) (fun _ ↦ s → k) where
  coe := Additive_Monoid_hom₁.original_function
attribute [coe] Additive_Monoid_hom₁.original_function

structure Multiplicative_Monoid_hom₁
  (s : Type w) [Ms : Multiplicative_Monoid s]
  (k : Type u) [Mk : Multiplicative_Monoid k] where
  original_function : s → k
  map_e : original_function Ms.e = Mk.e
  map_mul (x y : s) : original_function (Ms.mul x y) = Mk.mul (original_function x) (original_function y)

attribute [simp] Multiplicative_Monoid_hom₁.map_e

instance
  [Multiplicative_Monoid s] [Multiplicative_Monoid k]
  : CoeFun (Multiplicative_Monoid_hom₁ s k) (fun _ ↦ s → k) where
  coe := Multiplicative_Monoid_hom₁.original_function

attribute [coe] Multiplicative_Monoid_hom₁.original_function

structure Ring_hom₁
  (s : Type w) [Ring s]
  (k : Type u) [Ring k]
  extends Additive_Monoid_hom₁ s k, Multiplicative_Monoid_hom₁ s k

class Additive_Monoid_hom₂
  (F : Type)
  (s t : outParam Type)
  [As : Additive_Monoid s] [At : Additive_Monoid t] extends function_wrapper F s t
  where
  map_zero (f : F) : original_function f As.zero = At.zero
  map_add (f : F) (x y : s) : original_function f (As.add x y) = At.add (original_function f x) (original_function f y)

-- instance [Additive_Monoid M] [Additive_Monoid N] [Additive_Monoid_hom₂ F M N] : CoeFun F (fun _ ↦ M → N) where
--   coe := Additive_Monoid_hom₂.original_function
-- attribute [coe] Additive_Monoid_hom₂.original_function
attribute [simp] Additive_Monoid_hom₂.map_zero

class Multiplicative_Monoid_hom₂
  (F : Type)
  (s t : outParam Type)
  [As : Multiplicative_Monoid s] [At : Multiplicative_Monoid t] extends function_wrapper F s t
  where
  map_e (f : F) : original_function f As.e = At.e
  map_mul (f : F) (x y : s) : original_function f (As.mul x y) = At.mul (original_function f x) (original_function f y)

-- instance [Multiplicative_Monoid M] [Multiplicative_Monoid N] [Multiplicative_Monoid_hom₂ F M N]
--   : function_wrapper M N (Multiplicative_Monoid_hom₂ F M N)  where
--   coe := Multiplicative_Monoid_hom₂.original_function
-- attribute [coe] Multiplicative_Monoid_hom₂.original_function
attribute [simp] Multiplicative_Monoid_hom₂.map_e

@[simp]
def compose_Ring_hom [Ring R] [Ring S] [Ring T] (f : Ring_hom₁ R S) (g : Ring_hom₁ S T) : Ring_hom₁ R T :=
  {
    original_function (x) := g.original_function ( f.original_function x )
    map_zero := by simp
    map_add := by
      intro x y;
      rw [f.map_add, g.map_add]
    map_e := by rw [f.map_e, g.map_e]
    map_mul := by
      intro x y;
      rw [f.map_mul, g.map_mul]
  }

instance (R S : Type) [Ring R] [Ring S] : Multiplicative_Monoid_hom₂ (Ring_hom₁ R S) R S where
  original_function := fun f ↦ f.toMultiplicative_Monoid_hom₁.original_function
  map_e := fun f ↦ f.toMultiplicative_Monoid_hom₁.map_e
  map_mul := fun f ↦ f.toMultiplicative_Monoid_hom₁.map_mul

variable[Ring R] [Ring S] (test : Ring_hom₁ R S)
#check CoeFun.coe test

class free_algebra (s : Type w) (k : Type u) [Ring s] extends Ring k where
  var : k
  induced_map {t : Type} [Ring t] (f : Ring_hom₁ s t) (target : t)
    : Ring_hom₁ k t
  induced_map_is_valid {t : Type} [Ring t] (f : Ring_hom₁ s t) (target : t)
    : (induced_map f target).original_function var = target

theorem add_inverse_of_non_zero_is_non_zero (R : Ring k) (a : k) (ha : ¬a = R.zero)
  : ¬ R.add_inverse a = R.zero
  := by
  intro q
  apply ha
  have h_a_add_inverse := R.add_add_inverse_self a
  rw [q] at h_a_add_inverse
  rw [R.add_zero_any] at h_a_add_inverse
  apply h_a_add_inverse

theorem left_inverse_is_right_inverse (k : Type u) (e : k)
  (op : k → k → k) (h_op : is_associative op)
  (h_e : ∀ a : k, op e a = a) (h_e' : ∀ a : k, op a e = a)
  (left_inv : k → k) (h_left_inv : ∀ a : k, op (left_inv a) a = e)
  (right_inv : k → k) (h_right_inv : ∀ a : k, op a (right_inv a) = e)
  (x : k)
  :
  left_inv x = right_inv x
  := by
  have hx := h_left_inv x
  rw [←h_e (right_inv x)]
  rw [←hx]
  rw [h_op]
  rw [h_right_inv]
  rw [h_e']


theorem Ring_left_inverse_is_right_inverse (R : Ring k) : is_right_inverse R.add R.zero R.add_inverse := by
  simp
  intro x
  rw [R.add_is_comm]
  apply R.add_add_inverse_self

theorem left_inverse_is_unique (R : Ring k)
  (x : k)
  (left_inv : k) (h_left_inv : R.add left_inv x = R.zero)
  : left_inv = R.add_inverse x := by
  have h : R.zero = R.zero := rfl
  have ri := Ring_left_inverse_is_right_inverse R x
  rw [←R.add_any_zero left_inv]
  rw [←ri]
  rw [←R.add_is_assoc]
  rw [h_left_inv]
  rw [R.add_zero_any]

@[simp]
theorem mul_zero_any [R : Ring k] (a : k)
  : R.mul R.zero a = R.zero
  := by
  rw [←R.add_any_zero (R.mul R.zero a)]
  have ri := Ring_left_inverse_is_right_inverse R (R.mul R.zero a)
  conv =>
    lhs
    arg 2
    rw [←ri]
  rw [←R.add_is_assoc]
  rw [←R.mul_is_linear_left]
  rw [R.add_zero_any]
  rw [ri]

@[simp]
theorem mul_any_zero [R : Ring k] (a : k)
  : R.mul a R.zero = R.zero
  := by
  rw [R.mul_is_comm]
  apply mul_zero_any

@[simp]
theorem add_inverse_of_zero [R : Ring k]
  : R.add_inverse R.zero = R.zero := by
  refine Eq.symm (left_inverse_is_unique R ⟨0⟩ ⟨0⟩ ?_)
  apply R.add_zero_any

theorem add_inverse_is_zero [R : Ring k] (x : k) (h : R.add_inverse x = R.zero) : x = R.zero := by
  have q := R.add_add_inverse_self x
  rw [h, R.add_zero_any] at q
  apply q

-- class extended_Ring_properties k [R : Ring k] where
--   mul_any_zero (a : k) : mul.mul a Pointed_Zero.zero = Pointed_Zero.zero
--   mul_zero_any (a : k) : mul.mul Pointed_Zero.zero a = Pointed_Zero.zero
--   zero_add_inverse : R.add_inverse R.zero = R.zero

-- instance (k : Type u) [Ring k] : extended_Ring_properties (k) where
--   mul_any_zero := mul_any_zero
--   mul_zero_any := mul_zero_any
--   zero_add_inverse := add_inverse_of_zero

-- attribute [simp] extended_Ring_properties.mul_any_zero extended_Ring_properties.mul_zero_any extended_Ring_properties.zero_add_inverse

theorem e_eq_zero_then_one_element {k : Type u} [R: Ring k] (h : R.e = R.zero) (a : k) : (a = R.zero) := by
  rw [←R.mul_e_any a]
  rw [h]
  apply mul_zero_any

theorem inverse_respects_mul (R : Ring k) (a : k) (b : k)
  : R.mul (R.add_inverse a) b = R.add_inverse (R.mul a b)
  := by
  apply left_inverse_is_unique
  rw [←R.mul_is_linear_left]
  rw [R.add_add_inverse_self]
  apply mul_zero_any


class Ring_with_fixed_identities (k : Type u) (k_z : k) (k_e : k) extends Ring k where
  kz_is_zero : k_z = Pointed_Zero.zero
  ke_is_e : k_e = Pointed_Multiplicative_Identity.e

@[reducible]
def Ring_has_fixed_identities (k : Type u) [R : Ring k] : Ring_with_fixed_identities k R.zero R.e := {
  kz_is_zero := rfl
  ke_is_e := rfl
}

class field k extends Ring k where
  mul_inverse : k → k
  mul_inverse_is_inverse : is_left_inverse mul e mul_inverse


@[reducible]
def transfer_ring
  (k : Type u) (R : Ring k)
  (t : Type v)
  (forward : t → k)
  (back : k → t)
  (hbf : ∀ x : t, back (forward x) = x)
  (hfb : ∀ x : k, forward (back x) = x)
  : Ring t := {
  zero := back R.zero
  e := back R.e
  add x y := back (R.add (forward x) (forward y))
  add_zero_any := by
    simp_all
  add_any_zero := by
    simp_all
  add_is_assoc := by
    intro a b c
    simp_all
    rw [R.add_is_assoc]
  add_is_comm := by
    intro a b;
    rw [R.add_is_comm]
  mul x y := back (R.mul (forward x) (forward y))
  mul_any_e := by simp_all
  mul_e_any := by simp_all
  mul_is_assoc := by
    intro a b c
    simp_all
    rw [R.mul_is_assoc]
  mul_is_comm := by
    intro a b;
    rw [R.mul_is_comm]
  add_inverse x := back (R.add_inverse (forward x))
  add_add_inverse_self := by
    intro a
    simp
    rw [hfb, R.add_add_inverse_self]
  mul_is_linear_left := by
    intro a b c;
    simp_all
    rw [R.mul_is_linear_left]
  mul_is_linear_right := by
    intro a b c;
    simp_all
    rw [R.mul_is_linear_right]
}


end algebra
