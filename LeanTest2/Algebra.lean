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

class choose_zero (k : Type u) where
  zero : k

class add (k : Type u) where
  add : k → k → k

class mul (k : Type u) where
  mul : k → k → k

class choose_e (k : Type u) where
  e : k

infix:90 "⊹" => add.add
infix:95 "⋆" => mul.mul

class commutative_mul (k : Type u) extends mul k where
  mul_is_comm (a b) : mul a b = mul b a

class additive_monoid (k : Type u) extends choose_zero k, add k where
  add_zero_left (a : k) : add zero a = a
  add_zero_right (a : k) : add a zero = a
  add_is_assoc (a b c : k) : add (add a b) c = add a (add b c)

notation "⟨0⟩" => choose_zero.zero
notation "⟨1⟩" => choose_e.e

class multiplicative_monoid (k : Type u) extends choose_e k, mul k where
  mul_e_right (a : k) : mul a e = a
  mul_e_left (a : k) : mul e a = a
  mul_is_assoc (a b c) : mul (mul a b) c = mul a (mul b c)

export additive_monoid (add_zero_left add_zero_right)
attribute [simp] add_zero_left add_zero_right

export multiplicative_monoid (mul_e_right mul_e_left)
attribute [simp] mul_e_right mul_e_left

class commutative_additive_monoid (k : Type u) extends additive_monoid k where
  add_is_comm (a b : k) : add a b = add b a

class commutative_multiplicative_monoid (k : Type u) extends multiplicative_monoid k, commutative_mul k

class ring (k : Type u) extends commutative_additive_monoid k, commutative_multiplicative_monoid k where
  add_inverse : k → k
  -- non_trivial : ¬ e = zero
  add_inverse_is_inverse : is_left_inverse add zero add_inverse
  mul_is_linear_left : is_left_linear add mul
  mul_is_linear_right : is_right_linear add mul


export ring (add_inverse_is_inverse)
attribute [simp] add_inverse_is_inverse

class ring_to_string (k : Type u) extends ring k, ToString k

class function_wrapper (F : Type) (S T: outParam Type) where
  original_function : F → S → T

instance [function_wrapper F S T]
  : CoeFun F (fun _ ↦ S → T) where
  coe := function_wrapper.original_function
attribute [coe] function_wrapper.original_function

structure additive_monoid_hom₁
  (s : Type w) [Ms : additive_monoid s]
  (k : Type u) [Mk : additive_monoid k] where
  original_function : s → k
  map_zero : original_function Ms.zero = Mk.zero
  map_add (x y : s) : original_function (Ms.add x y) = Mk.add (original_function x) (original_function y)

export additive_monoid_hom₁ (map_zero)
attribute [simp] map_zero

instance
  [additive_monoid s] [additive_monoid k]
  : CoeFun (additive_monoid_hom₁ s k) (fun _ ↦ s → k) where
  coe := additive_monoid_hom₁.original_function
attribute [coe] additive_monoid_hom₁.original_function

structure multiplicative_monoid_hom₁
  (s : Type w) [Ms : multiplicative_monoid s]
  (k : Type u) [Mk : multiplicative_monoid k] where
  original_function : s → k
  map_e : original_function Ms.e = Mk.e
  map_mul (x y : s) : original_function (Ms.mul x y) = Mk.mul (original_function x) (original_function y)

export multiplicative_monoid_hom₁ (map_e)
attribute [simp] map_e

instance
  [multiplicative_monoid s] [multiplicative_monoid k]
  : CoeFun (multiplicative_monoid_hom₁ s k) (fun _ ↦ s → k) where
  coe := multiplicative_monoid_hom₁.original_function
attribute [coe] multiplicative_monoid_hom₁.original_function

structure ring_hom₁
  (s : Type w) [ring s]
  (k : Type u) [ring k]
  extends additive_monoid_hom₁ s k, multiplicative_monoid_hom₁ s k

class additive_monoid_hom₂
  (F : Type)
  (s t : outParam Type)
  [As : additive_monoid s] [At : additive_monoid t] extends function_wrapper F s t
  where
  map_zero (f : F) : original_function f As.zero = At.zero
  map_add (f : F) (x y : s) : original_function f (As.add x y) = At.add (original_function f x) (original_function f y)

-- instance [additive_monoid M] [additive_monoid N] [additive_monoid_hom₂ F M N] : CoeFun F (fun _ ↦ M → N) where
--   coe := additive_monoid_hom₂.original_function
-- attribute [coe] additive_monoid_hom₂.original_function
attribute [simp] additive_monoid_hom₂.map_zero

class multiplicative_monoid_hom₂
  (F : Type)
  (s t : outParam Type)
  [As : multiplicative_monoid s] [At : multiplicative_monoid t] extends function_wrapper F s t
  where
  map_e (f : F) : original_function f As.e = At.e
  map_mul (f : F) (x y : s) : original_function f (As.mul x y) = At.mul (original_function f x) (original_function f y)

-- instance [multiplicative_monoid M] [multiplicative_monoid N] [multiplicative_monoid_hom₂ F M N]
--   : function_wrapper M N (multiplicative_monoid_hom₂ F M N)  where
--   coe := multiplicative_monoid_hom₂.original_function
-- attribute [coe] multiplicative_monoid_hom₂.original_function
attribute [simp] multiplicative_monoid_hom₂.map_e

@[simp]
def compose_ring_hom [ring R] [ring S] [ring T] (f : ring_hom₁ R S) (g : ring_hom₁ S T) : ring_hom₁ R T :=
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

instance (R S : Type) [ring R] [ring S] : multiplicative_monoid_hom₂ (ring_hom₁ R S) R S where
  original_function := fun f ↦ f.tomultiplicative_monoid_hom₁.original_function
  map_e := fun f ↦ f.tomultiplicative_monoid_hom₁.map_e
  map_mul := fun f ↦ f.tomultiplicative_monoid_hom₁.map_mul

variable[ring R] [ring S] (test : ring_hom₁ R S)
#check CoeFun.coe test

class free_algebra (s : Type w) (k : Type u) [ring s] extends ring k where
  var : k
  induced_map {t : Type} [ring t] (f : ring_hom₁ s t) (target : t)
    : ring_hom₁ k t
  induced_map_is_valid {t : Type} [ring t] (f : ring_hom₁ s t) (target : t)
    : (induced_map f target).original_function var = target

theorem add_inverse_of_non_zero_is_non_zero (R : ring k) (a : k) (ha : ¬a = R.zero)
  : ¬ R.add_inverse a = R.zero
  := by
  intro q
  apply ha
  have h_a_add_inverse := R.add_inverse_is_inverse a
  rw [q] at h_a_add_inverse
  rw [R.add_zero_left] at h_a_add_inverse
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


theorem ring_left_inverse_is_right_inverse (R : ring k) : is_right_inverse R.add R.zero R.add_inverse := by
  simp
  intro x
  rw [R.add_is_comm]
  apply R.add_inverse_is_inverse

theorem left_inverse_is_unique (R : ring k)
  (x : k)
  (left_inv : k) (h_left_inv : R.add left_inv x = R.zero)
  : left_inv = R.add_inverse x := by
  have h : R.zero = R.zero := rfl
  have ri := ring_left_inverse_is_right_inverse R x
  rw [←R.add_zero_right left_inv]
  rw [←ri]
  rw [←R.add_is_assoc]
  rw [h_left_inv]
  rw [R.add_zero_left]

@[simp]
theorem mul_zero_any_is_zero [R : ring k] (a : k)
  : R.mul R.zero a = R.zero
  := by
  rw [←R.add_zero_right (R.mul R.zero a)]
  have ri := ring_left_inverse_is_right_inverse R (R.mul R.zero a)
  conv =>
    lhs
    arg 2
    rw [←ri]
  rw [←R.add_is_assoc]
  rw [←R.mul_is_linear_left]
  rw [R.add_zero_left]
  rw [ri]

@[simp]
theorem mul_any_zero_is_zero [R : ring k] (a : k)
  : R.mul a R.zero = R.zero
  := by
  rw [R.mul_is_comm]
  apply mul_zero_any_is_zero

@[simp]
theorem add_inverse_of_zero [R : ring k]
  : R.add_inverse R.zero = R.zero := by
  refine Eq.symm (left_inverse_is_unique R ⟨0⟩ ⟨0⟩ ?_)
  apply R.add_zero_left

theorem add_inverse_is_zero [R : ring k] (x : k) (h : R.add_inverse x = R.zero) : x = R.zero := by
  have q := R.add_inverse_is_inverse x
  rw [h, R.add_zero_left] at q
  apply q

-- class extended_ring_properties k [R : ring k] where
--   mul_any_zero (a : k) : mul.mul a choose_zero.zero = choose_zero.zero
--   mul_zero_any (a : k) : mul.mul choose_zero.zero a = choose_zero.zero
--   zero_add_inverse : R.add_inverse R.zero = R.zero

-- instance (k : Type u) [ring k] : extended_ring_properties (k) where
--   mul_any_zero := mul_any_zero_is_zero
--   mul_zero_any := mul_zero_any_is_zero
--   zero_add_inverse := add_inverse_of_zero

-- attribute [simp] extended_ring_properties.mul_any_zero extended_ring_properties.mul_zero_any extended_ring_properties.zero_add_inverse

theorem e_eq_zero_then_one_element {k : Type u} [R: ring k] (h : R.e = R.zero) (a : k) : (a = R.zero) := by
  rw [←R.mul_e_left a]
  rw [h]
  apply mul_zero_any_is_zero

theorem inverse_respects_mul (R : ring k) (a : k) (b : k)
  : R.mul (R.add_inverse a) b = R.add_inverse (R.mul a b)
  := by
  apply left_inverse_is_unique
  rw [←R.mul_is_linear_left]
  rw [R.add_inverse_is_inverse]
  apply mul_zero_any_is_zero


class field k extends ring k where
  mul_inverse : k → k
  mul_inverse_is_inverse : is_left_inverse mul e mul_inverse

end algebra
