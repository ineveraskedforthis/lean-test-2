def hello := "world"

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

class choose_zero (k : Type u) where
  zero : k

class add (k : Type u) where
  add : k → k → k

class mul (k : Type u) where
  mul : k → k → k

class choose_e (k : Type u) where
  e : k

infix:90 "⊹" => add.add
infix:95 "*" => mul.mul

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

-- class type_wrapper where
--   k : Type

-- class add (k : Type u) where
--   zero : k

-- class mul (k : Type u) where
--   e : k
--   mul : k → k → k
--   mul_e_left (a : k) : mul e a = a
--   mul_e_right (a : k) : mul a e = a

-- class mul_assoc (k : Type u) extends mul k where
--   mul_is_assoc (a b c : k) : mul (mul a b) c = mul a (mul b c)

-- class add_comm (k : Type u) extends add k where
--   add_is_comm (a b : k) : add a b = add b a

-- class add_inverse (k : Type u) extends add k where
--   inverse : k → k
--   add_inverse_left (a : k) : add (inverse a) a = zero
--   add_inverse_right (a : k) : add a (inverse a) = zero

-- class mul_comm (k : Type u) extends mul k where
--   mul_is_comm (a b : k) : mul a b = mul b a

-- class add_comm_inverse (k : Type u) extends add_comm k, add_inverse k


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
theorem mul_zero_any_is_zero (R : ring k) (a : k)
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
theorem mul_any_zero_is_zero (R : ring k) (a : k)
  : R.mul a R.zero = R.zero
  := by
  rw [R.mul_is_comm]
  apply mul_zero_any_is_zero

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

inductive polynomial_degree_type where
  | bottom : polynomial_degree_type
  | value : Nat → polynomial_degree_type

def trim_coeff {k : Type u} (is_zero : k → Bool) (a : Array k) : Array k :=
  if h : a.size = 0 then a else (if is_zero a.back then trim_coeff is_zero (a.pop) else a)
  termination_by a.size

def trim_leading_zeros_internal {k : Type u} [Z : choose_zero k] [BEq k] [LawfulBEq k] (a : List k) : List k :=
  match a with
  | [] => a
  | x :: a' => if x == Z.zero then trim_leading_zeros_internal a' else a


theorem trim_leading_zeros_internal_idempotent {k : Type u}  [Z : choose_zero k] [BEq k] [LawfulBEq k] (a : List k) :
  trim_leading_zeros_internal (trim_leading_zeros_internal a) = trim_leading_zeros_internal a
  := by
  match a with
  | [] => simp [trim_leading_zeros_internal]
  | x :: a' =>
    if hx : x == Z.zero then
      rw [trim_leading_zeros_internal]
      simp [hx]
      rw [trim_leading_zeros_internal_idempotent]
    else
      rw [trim_leading_zeros_internal]
      simp [hx]
      rw [trim_leading_zeros_internal]
      simp [hx]


def trim_polynomial_list {k : Type u} [Z : choose_zero k] [BEq k] [LawfulBEq k] (a : List k) : List k :=
  (trim_leading_zeros_internal a.reverse).reverse

prefix:100 "↓" => trim_polynomial_list

@[simp]
theorem trim_polynomial_list_idempotent {k : Type u} [Z : choose_zero k] [BEq k] [LawfulBEq k] (a : List k) :
  trim_polynomial_list (trim_polynomial_list a) = trim_polynomial_list a
  := by
  simp [trim_polynomial_list, trim_leading_zeros_internal_idempotent]

@[simp]
theorem trim_zero_glue_generator_internal
  {k : Type u} [Z : choose_zero k] [BEq k] [LawfulBEq k]
  (a : List k) : trim_leading_zeros_internal (Z.zero :: a) = trim_leading_zeros_internal a
  := by
  rw [trim_leading_zeros_internal]
  simp

@[simp]
theorem trim_zero_glue_generator_internal'
  {k : Type u} [Z : choose_zero k] [BEq k] [LawfulBEq k] : trim_leading_zeros_internal ([Z.zero]) = []
  := by
  repeat rw [trim_leading_zeros_internal]
  simp

@[simp]
theorem trim_zero_glue_generator
  {k : Type u} [Z : choose_zero k] [BEq k] [LawfulBEq k]
  (a : List k) : trim_polynomial_list (a ++ [Z.zero]) = trim_polynomial_list a
  := by
  rw [trim_polynomial_list]
  rw [trim_polynomial_list]
  rw [List.reverse_concat]
  rw [trim_zero_glue_generator_internal]

@[simp]
theorem trim_zero_glue_generator'
  {k : Type u} [Z : choose_zero k] [BEq k] [LawfulBEq k] : trim_polynomial_list ([Z.zero]) = []
  := by
  rw [trim_polynomial_list]
  rw [List.reverse_singleton]
  rw [trim_zero_glue_generator_internal']
  rw [List.reverse_nil]

@[simp]
theorem trim_zero_glue_nil
  {k : Type u} [Z : choose_zero k] [BEq k] [LawfulBEq k] : trim_polynomial_list ([] : List k) = []
  := by
  rw [trim_polynomial_list]
  rw [List.reverse_nil]
  rw [trim_leading_zeros_internal]
  rw [List.reverse_nil]

@[simp]
theorem trim_zero_glue_singleton
  {k : Type u} [Z : choose_zero k] [BEq k] [LawfulBEq k] : trim_polynomial_list ([Z.zero]) = []
  := by
  simp [trim_polynomial_list, trim_leading_zeros_internal]

@[simp]
theorem trim_non_zero_singleton
  {k : Type u} [Z : choose_zero k] [BEq k] [LawfulBEq k] (x: k) (hx : ¬(x == Z.zero)) : trim_polynomial_list ([x]) = [x]
  := by
  simp_all [trim_polynomial_list, trim_leading_zeros_internal]

theorem trim_singleton {k : Type u} [Z : choose_zero k] [BEq k] [LawfulBEq k] (x: k)
  : trim_polynomial_list ([x]) = if x == Z.zero then [] else [x] := by
  grind [trim_zero_glue_singleton, trim_non_zero_singleton]

theorem trim_respects_zero_pop
  {k : Type u} (is_zero : k → Bool)
  (a : Array k) (non_empty : 0 < a.size) (zero_at_back : is_zero a.back)
  :
  trim_coeff is_zero a = trim_coeff is_zero a.pop := by
  rw [trim_coeff]
  have non_empty' := Nat.ne_zero_iff_zero_lt.mpr non_empty
  split
  contradiction
  rfl

theorem pop_preserves_array {k : Type u} (a : Array k) (i : Nat) (h : i <a.pop.size) (h' : i < a.size) : a.pop[i] = a[i] := by
  exact Array.getElem_pop h

theorem empty_trim_condition {k : Type u} (is_zero : k → Bool) (a : Array k) (h : (trim_coeff is_zero a).size = 0) :
  a.all is_zero := by
  if empty : a.size = 0 then
    grind
  else
    have empty' := Nat.ne_zero_iff_zero_lt.mp empty
    simp at empty
    if zero_at_back : is_zero a.back then
      have respect_pop := trim_respects_zero_pop is_zero a empty' zero_at_back
      rw [respect_pop] at h
      have pop_is_zero := empty_trim_condition is_zero a.pop h
      simp
      intro i i_is_valid
      if i_is_small : i < a.pop.size then
        have test := Array.all_eq_true.mp pop_is_zero
        rw [←Array.getElem_pop i_is_small]
        apply test i i_is_small
      else
        grind only [= Array.size_pop, = Array.back_eq_getElem]
    else
      false_or_by_contra
      rw [trim_coeff] at h
      simp[zero_at_back] at h
      contradiction


def array_degree {k : Type u} (p : Array k) : polynomial_degree_type :=
  match p.size with
  | 0 => polynomial_degree_type.bottom
  | d + 1 => polynomial_degree_type.value d

def get_coeff_array  {k : Type u} (zero : k) (p : Array k) (i : Nat) : k :=
  if h : i < p.size then p[i] else zero

def get_coeff_list  {k : Type u} (zero : k) (p : List k) (i : Nat) : k :=
  match p[i]? with
  | none => zero
  | some x => x

theorem zero_array_has_zero_coeffs
  {k : Type u} [BEq k] [LawfulBEq k] (zero : k)
  (p : Array k) (h: p.all (fun x ↦ x == zero))
  (i : Nat) :
  get_coeff_array zero p i = zero := by
  rw [get_coeff_array]
  split
  have h' := Array.all_eq_true.mp h
  simp at h'
  apply h'
  rfl

theorem zero_list_has_zero_coeffs
  {k : Type u} [BEq k] [LawfulBEq k] (zero : k)
  (p : List k) (h: p.all (fun x ↦ x == zero))
  (i : Nat) :
  get_coeff_list zero p i = zero := by
  rw [get_coeff_list]
  split
  · case h_1 x hx => rfl
  · case h_2 x x' hx =>
    -- rw [beq_iff_eq.] at h
    have h' := List.all_eq_true.mp h
    have x_mem : x' ∈ p := by
      exact List.mem_of_getElem? hx
    exact beq_iff_eq.mp (h' x' x_mem)


def mul_polynomial_array_at_degree_internal_summand
  {k : Type u} (k_zero : k) (k_mul : k → k → k)
  (a : Array k) (b : Array k) (i : Nat) (j : Nat) : k
  :=
  let ca := get_coeff_array k_zero a i
  let cb := get_coeff_array k_zero b j
  k_mul ca cb

def mul_polynomial_list_at_degree_internal_summand
  {k : Type u} (k_zero : k) (k_mul : k → k → k)
  (a : List k) (b : List k) (i : Nat) (j : Nat) : k
  :=
  let ca := get_coeff_list k_zero a i
  let cb := get_coeff_list k_zero b j
  k_mul ca cb

theorem mul_polynomial_at_degree_internal_summand_symmetry
  {k : Type u}  (k_zero : k) (k_mul : k → k → k) (mul_comm : is_symmetric_2 k_mul)
  (a : List k) (b : List k) (i : Nat) (j : Nat)
  :
  (mul_polynomial_list_at_degree_internal_summand k_zero k_mul a b i j)
  =
  (mul_polynomial_list_at_degree_internal_summand k_zero k_mul b a j i)
  :=
  by
  simp[mul_polynomial_list_at_degree_internal_summand]
  apply mul_comm


def mul_polynomial_list_at_degree_internal
  {k : Type u} (k_zero : k) (k_mul : k → k → k) (k_add : k →  k → k)
  (a : List k) (b : List k) (d : Nat) (current : Nat) (acc : k) : k
  :=
  let current_summand := mul_polynomial_list_at_degree_internal_summand k_zero k_mul a b current (d - current)
  match current with
  | 0 => k_add acc current_summand
  | i + 1 => mul_polynomial_list_at_degree_internal k_zero k_mul k_add a b d i (k_add acc (k_add acc current_summand))

theorem mul_polynomial_at_degree_zero_polynomial_left
  {k : Type u} [BEq k]  [LawfulBEq k]  (k_zero : k) (k_mul : k → k → k) (k_add : k →  k → k)
  (mul_comm : is_symmetric_2 k_mul)
  (mul_zero_left : ∀ x : k, k_mul k_zero x = k_zero)
  (add_zero_left : ∀ x : k, k_add k_zero x = x)
  (a : List k) (b : List k) (h : a.all (fun (x) ↦ (x == k_zero)))
  (d : Nat) (current : Nat)
  :
  (mul_polynomial_list_at_degree_internal k_zero k_mul k_add a b d current k_zero) = k_zero
  := by
  rw [mul_polynomial_list_at_degree_internal.eq_def]
  rw [mul_polynomial_list_at_degree_internal_summand]
  split
  · case h_1 x =>
    have coeff_is_zero := zero_list_has_zero_coeffs k_zero a h 0
    rw [coeff_is_zero]
    rw [add_zero_left, mul_zero_left]
  · case h_2 x y =>
    have coeff_is_zero := zero_list_has_zero_coeffs k_zero a h y.succ
    rw [coeff_is_zero, mul_zero_left]
    simp
    repeat rw [add_zero_left]
    apply mul_polynomial_at_degree_zero_polynomial_left
    repeat assumption

theorem mul_polynomial_at_degree_zero_polynomial_right
  {k : Type u} [BEq k]  [LawfulBEq k]  (k_zero : k) (k_mul : k → k → k) (k_add : k →  k → k)
  (mul_comm : is_symmetric_2 k_mul)
  (mul_zero_right : ∀ x : k, k_mul x k_zero = k_zero)
  (add_zero_left : ∀ x : k, k_add k_zero x = x)
  (a : List k) (b : List k) (h : b.all (fun (x) ↦ (x == k_zero)))
  (d : Nat) (current : Nat)
  :
  (mul_polynomial_list_at_degree_internal k_zero k_mul k_add a b d current k_zero) = k_zero
  := by
  rw [mul_polynomial_list_at_degree_internal.eq_def]
  rw [mul_polynomial_list_at_degree_internal_summand]
  split
  · case h_1 x =>
    have coeff_is_zero := zero_list_has_zero_coeffs k_zero b h (d - 0)
    rw [coeff_is_zero]
    rw [add_zero_left, mul_zero_right]
  · case h_2 x y =>
    have coeff_is_zero := zero_list_has_zero_coeffs k_zero b h (d - y.succ)
    rw [coeff_is_zero, mul_zero_right]
    simp
    repeat rw [add_zero_left]
    apply mul_polynomial_at_degree_zero_polynomial_right
    repeat assumption

def  mul_polynomial_list_at_degree
  {k : Type u} (k_zero : k) (k_mul : k → k → k) (k_add : k →  k → k)
  (a : List k) (b : List k) (d : Nat) : k
  :=
  mul_polynomial_list_at_degree_internal k_zero k_mul k_add a b d d k_zero

theorem mul_polynomial_at_degree_zero_polynomial_left'
  {k : Type u} [BEq k]  [LawfulBEq k]  (k_zero : k) (k_mul : k → k → k) (k_add : k →  k → k)
  (mul_comm : is_symmetric_2 k_mul)
  (mul_zero_left : ∀ x : k, k_mul k_zero x = k_zero)
  (add_zero_left : ∀ x : k, k_add k_zero x = x)
  (a : List k) (b : List k) (h : a.all (fun (x) ↦ (x == k_zero)))
  (d : Nat)
  :
  (mul_polynomial_list_at_degree k_zero k_mul k_add a b d) = k_zero
  := by
  rw [mul_polynomial_list_at_degree]
  apply mul_polynomial_at_degree_zero_polynomial_left
  repeat assumption

theorem mul_polynomial_at_degree_zero_polynomial_right'
  {k : Type u} [BEq k]  [LawfulBEq k]  (k_zero : k) (k_mul : k → k → k) (k_add : k →  k → k)
  (mul_comm : is_symmetric_2 k_mul)
  (mul_zero_right : ∀ x : k, k_mul x k_zero = k_zero)
  (add_zero_left : ∀ x : k, k_add k_zero x = x)
  (a : List k) (b : List k) (h : b.all (fun (x) ↦ (x == k_zero)))
  (d : Nat)
  :
  (mul_polynomial_list_at_degree k_zero k_mul k_add a b d) = k_zero
  := by
  rw [mul_polynomial_list_at_degree]
  apply mul_polynomial_at_degree_zero_polynomial_right
  repeat assumption


def mul_polynomial_internal
  {k : Type u} (k_zero : k) (k_mul : k → k → k) (k_add : k →  k → k)
  (a : List k) (b : List k) (current : Nat) (acc : List k)
  :=
  let mul_at_current := mul_polynomial_list_at_degree k_zero k_mul k_add a b current
  match current with
  | 0 => mul_at_current :: acc
  | next_current + 1 => mul_polynomial_internal k_zero k_mul k_add a b next_current (mul_at_current :: acc)

theorem mul_polynomial_zero_left_internal
  {k : Type u} [BEq k] [LawfulBEq k]  (k_zero : k) (k_mul : k → k → k) (k_add : k →  k → k)
  (mul_comm : is_symmetric_2 k_mul)
  (mul_zero_left : ∀ x : k, k_mul k_zero x = k_zero)
  (add_zero_left : ∀ x : k, k_add k_zero x = x)
  (a : List k) (b : List k) (h : a.all (fun (x) ↦ (x == k_zero))) (current : Nat)
  (acc : List k) (h_acc : acc.all (fun (x) ↦ (x == k_zero)))
  :
  (mul_polynomial_internal k_zero k_mul k_add a b current acc).all (fun (x) ↦ (x == k_zero)) :=
  by
  rw [mul_polynomial_internal.eq_def]
  simp
  intro x
  split
  · case h_1 n =>
      rw [mul_polynomial_list_at_degree, mul_polynomial_list_at_degree_internal, add_zero_left]
      intro x_mem
      have x_mem' := List.mem_cons.mp x_mem
      rcases x_mem' with x_mem_summand | x_mem_acc
      · case inl =>
        rw [mul_polynomial_list_at_degree_internal_summand] at x_mem_summand
        rw [x_mem_summand]
        rw [zero_list_has_zero_coeffs]
        rw [mul_zero_left]
        apply List.all_eq_true.mpr
        intro new_x new_x_in_a
        rw [List.all_eq_true] at h
        apply h
        assumption
      · case inr =>
        rw [List.all_eq_true] at h_acc
        rw [←beq_iff_eq]
        apply h_acc
        assumption
  · case h_2 n d =>
    intro x_mem
    let mul_at_current := mul_polynomial_list_at_degree k_zero k_mul k_add a b d.succ
    let next_acc := mul_at_current :: acc
    have next_acc_is_zero : next_acc.all (fun(x)↦ (x == k_zero)) := by
      apply List.all_eq_true.mpr
      intro x x_mem_acc
      have x_mem' := List.mem_cons.mp x_mem_acc
      rcases x_mem' with x_mem_summand | x_mem_acc
      · case inl =>
        rw [beq_iff_eq]
        rw [x_mem_summand]
        apply mul_polynomial_at_degree_zero_polynomial_left
        repeat assumption
      · case inr =>
        apply List.all_eq_true.mp h_acc
        assumption
    have induction_step := mul_polynomial_zero_left_internal
      k_zero k_mul  k_add mul_comm mul_zero_left  add_zero_left a b h d next_acc next_acc_is_zero

    have h_induction_step := List.all_eq_true.mp induction_step x
    rw [beq_iff_eq] at h_induction_step
    apply h_induction_step
    apply x_mem

def mul_polynomial
  {k : Type u} (k_zero : k) (k_mul : k → k → k) (k_add : k →  k → k)
  (a : List k) (b : List k)
  :=
  mul_polynomial_internal k_zero k_mul k_add a b 0 []

theorem mul_polynomial_zero_left
  {k : Type u} [BEq k] [LawfulBEq k]  (k_zero : k) (k_mul : k → k → k) (k_add : k →  k → k)
  (mul_comm : is_symmetric_2 k_mul)
  (mul_zero_left : ∀ x : k, k_mul k_zero x = k_zero)
  (add_zero_left : ∀ x : k, k_add k_zero x = x)
  (a : List k) (b : List k) (h : a.all (fun (x) ↦ (x == k_zero)))
  :
  (mul_polynomial k_zero k_mul k_add a b).all (fun (x) ↦ (x == k_zero))
  := by
  rw [mul_polynomial]
  apply mul_polynomial_zero_left_internal
  repeat assumption
  simp

def add_polynomial
  {k : Type u} [A : add k]
  (a : List k) (b : List k) : List k
  :=
  match a, b with
  | [], [] => []
  | [], b' => b'
  | a', [] => a'
  | xa :: a', xb :: b' => A.add xa xb :: (add_polynomial a' b')

infix:90 "+₀" => add_polynomial

@[simp]
theorem add_polynomial_zero_left_0
  {k : Type u} [A : add k] [BEq k] [LawfulBEq k]
  (a : List k)
  :
  add_polynomial [] a = a
  := by
  rw [add_polynomial.eq_def]
  split
  repeat rfl
  simp_all

@[simp]
theorem add_polynomial_zero_right_0
  {k : Type u} [A : add k] [BEq k] [LawfulBEq k]
  (a : List k)
  :
  add_polynomial a [] = a
  := by
  rw [add_polynomial.eq_def]
  split
  repeat rfl
  simp_all

@[simp]
theorem add_polynomial_zero_left_1
  {k : Type u} [BEq k] [LawfulBEq k] [Z : choose_zero k] [A : add k]
  (add_zero_left : ∀ x : k, A.add Z.zero x = x)
  (a : List k)
  :
  trim_polynomial_list (add_polynomial [Z.zero] a) = trim_polynomial_list a
  := by
  rw [add_polynomial.eq_def]
  split
  rfl
  rfl
  rw [trim_zero_glue_generator']
  rw [trim_zero_glue_nil]
  · case h_4 xa y xb z w =>
    simp at w
    rw [← And.left w]
    rw [And.right w]
    rw [add_zero_left]
    rw [add_polynomial_zero_left_0]

@[simp]
theorem add_polynomial_zero_right_1
  {k : Type u} [BEq k] [LawfulBEq k] [Z : choose_zero k] [A : add k]
  (add_zero_right: ∀ x : k, A.add x Z.zero = x)
  (a : List k)
  :
  trim_polynomial_list (add_polynomial a [Z.zero]) = trim_polynomial_list a
  := by
  rw [add_polynomial.eq_def]
  split
  rfl
  rw [trim_zero_glue_generator']
  rw [trim_zero_glue_nil]
  simp
  · case h_4 xa y xb z w =>
    simp at w
    rw [← And.left w]
    rw [And.right w]
    rw [add_zero_right]
    rw [add_polynomial_zero_right_0]

def polynomial_shift
  {k : Type u}  [Z : choose_zero k]
  (a : List k) (n : Nat) : List k
  :=
  match n with
  | 0 => a
  | i + 1 => Z.zero :: polynomial_shift a i

def polynomial_shift_1
  {k : Type u} [Z : choose_zero k] (a : List k) : List k
  :=
  Z.zero :: a

prefix:100 "σ" => polynomial_shift_1

def polynomial_left_scalar_action
  {k : Type u} [M : mul k]
  (s : k) (a : List k) : List k
  :=
  a.map (M.mul s)

infix:90 "∘→" => polynomial_left_scalar_action


def polynomial_right_scalar_action
  {k : Type u} [M : mul k]
  (a : List k) (s : k) : List k
  :=
  a.map (M.mul . s)

infix:90 "←∘" => polynomial_right_scalar_action

@[simp]
theorem polynomial_left_identity_scalar_action
  {k : Type u} [M : mul k]
  (a : List k)  (k_left_identity : k) (h_identity : is_left_identity M.mul k_left_identity)
  : polynomial_left_scalar_action k_left_identity a = a
  := by
  rw [polynomial_left_scalar_action]
  exact List.map_id'' h_identity a

@[simp]
theorem polynomial_right_identity_scalar_action
  {k : Type u} [M : mul k]
  (a : List k)  (k_right_identity : k) (h_identity : is_right_identity M.mul k_right_identity)
  : polynomial_right_scalar_action a k_right_identity = a
  := by
  rw [polynomial_right_scalar_action]
  exact List.map_id'' h_identity a

def mul_polynomial'
  {k : Type u} [Z : choose_zero k] [A : add k] [M : mul k]
  (a : List k) (b : List k) : List k
  :=
  match a with
  | [] => []
  | x :: a' =>
    add_polynomial
      (polynomial_left_scalar_action x b)
      (polynomial_shift_1 (mul_polynomial' a' b))

infix:90 "*₀" => mul_polynomial'

def mul_polynomial''
  {k : Type u} [Z : choose_zero k] [A : add k] [M : mul k]
  (a : List k) (b : List k) : List k
  :=
  match b with
  | [] => []
  | x :: b' =>
    add_polynomial
      (polynomial_right_scalar_action a x)
      (polynomial_shift_1 (mul_polynomial' a b'))

def respect_trim {k : Type u}  [BEq k] [LawfulBEq k] [Z : choose_zero k] (f : List k → List k)
  := ∀ a, trim_polynomial_list (f a) = trim_polynomial_list (f (trim_polynomial_list a))

def respect_trim_2 {k : Type u}  [BEq k] [LawfulBEq k] [Z : choose_zero k] (f : List k → List k → List k)
  := ∀ a, ∀ b, trim_polynomial_list (f a b) = trim_polynomial_list (f (trim_polynomial_list a) (trim_polynomial_list b))

def respect_trim_internal {k : Type u}  [BEq k] [LawfulBEq k] [Z : choose_zero k] (f : List k → List k)
  := ∀ a, trim_leading_zeros_internal (f a) = trim_leading_zeros_internal (f (trim_leading_zeros_internal a))

theorem append_respects_trim_internal {k : Type u} [BEq k] [LawfulBEq k] [Z : choose_zero k] (x : k)
  : respect_trim_internal (. ++ [x])
  := by
  intro a
  match a with
  | [] => simp [trim_leading_zeros_internal]
  | x :: a' =>
    rw [trim_leading_zeros_internal]
    simp
    split
    · case isTrue hx =>
      rw [beq_iff_eq] at hx
      rw [hx]
      rw [trim_zero_glue_generator_internal]
      rw [append_respects_trim_internal]
    · case isFalse hx =>
      simp


theorem add_polynomial_commutes_with_cons {k : Type u} [BEq k] [LawfulBEq k] [A : add k] :
  ∀ a, ∀ b, ∀ xa, ∀ xb,
  (A.add xa xb) :: (add_polynomial a b)
  = (add_polynomial (xa :: a) (xb :: b)) := by
  intro a b xa xb
  match a, b with
  | [], [] => simp [add_polynomial]
  | [], b => simp [add_polynomial_zero_left_0, add_polynomial]
  | a, [] => simp [add_polynomial_zero_right_0, add_polynomial]
  | xa' :: a', xb' :: b' => simp [add_polynomial]

theorem cons_respects_trim {k : Type u} [BEq k] [LawfulBEq k] [choose_zero k] (x : k)
  : respect_trim (List.cons x)
  := by
  intro a
  simp [trim_polynomial_list]
  rw [append_respects_trim_internal]

theorem trim_zero_all
  {k : Type u} [BEq k] [LawfulBEq k] [Z : choose_zero k] (a : List k) (ha : a.all (fun x ↦ (x == Z.zero)))
  : trim_polynomial_list a = []
  := by
  match a with
  | [] => exact trim_zero_glue_nil
  | xa :: a' =>
    rw [cons_respects_trim]
    have ha' : a'.all (fun x ↦ (x == Z.zero)) := by
      rw [List.all_cons] at ha
      simp_all
      apply ha.right
    conv =>
      arg 1
      arg 1
      rw [trim_zero_all a' ha']
    have hxa : xa == Z.zero := by
      rw [List.all_cons] at ha
      simp_all
    rw [eq_of_beq hxa]
    rw [trim_zero_glue_singleton]

theorem trim_internal_helper_not_all_zero
  {k : Type u} [BEq k] [LawfulBEq k] [Z : choose_zero k]
  (x : k) (a : List k)
  (ha : ¬a.all (fun x ↦ x == Z.zero))
  : trim_leading_zeros_internal (a ++ [x]) = trim_leading_zeros_internal a ++ [x] := by
  simp at ha
  match a with
  | [] =>
    simp_all
  | xa :: a' =>
    conv =>
      lhs
      rw [List.cons_append]
      rw [trim_leading_zeros_internal]
    if xa = Z.zero then
      simp_all [trim_internal_helper_not_all_zero]
    else
      simp_all [trim_leading_zeros_internal]


theorem trim_internal_helper_all_zero {k : Type u} [BEq k] [LawfulBEq k] [Z : choose_zero k] (x : k) (a : List k)
  (ha : a.all (fun x ↦ x == Z.zero))
  : trim_leading_zeros_internal (a ++ [x]) = trim_leading_zeros_internal [x] := by
  rw [trim_leading_zeros_internal]
  rw [trim_leading_zeros_internal]
  if h : x == Z.zero then
    rw [trim_leading_zeros_internal.eq_def]
    split
    · case h_1 =>
      simp_all
    · case h_2 q1 q2 q3 q4 =>
      rw [h]
      have hq := List.cons_eq_append_iff.mp q4.symm
      rcases hq with h1 | hq2
      simp_all [trim_leading_zeros_internal]
      rcases hq2 with ⟨ a', ⟨ ha'_l, ha'_r⟩ ⟩
      have ha_f := List.all_eq_true.mp ha
      have q2_is_zero : q2 == Z.zero := by
        apply ha_f
        rw [ha'_l]
        exact List.mem_cons_self
      rw [q2_is_zero]
      rw [ha'_r]
      rw [trim_internal_helper_all_zero]
      simp_all [trim_leading_zeros_internal]
      simp at ha
      simp
      intro element
      intro element_in_a'
      have a'_sub_a' : a' ⊆ a' := by exact List.subset_def.mpr fun {a} a_1 => a_1
      have tmp := List.subset_cons_of_subset q2 a'_sub_a'
      rw [←ha'_l] at tmp
      apply ha
      simp_all
  else
    rw [trim_leading_zeros_internal.eq_def]
    split
    · case h_1 =>
      simp_all
    · case h_2 q1 q2 q3 q4 =>
      simp [h]
      have hq := List.cons_eq_append_iff.mp q4.symm
      rcases hq with h1 | hq2
      simp_all [trim_leading_zeros_internal]
      rcases hq2 with ⟨ a', ⟨ ha'_l, ha'_r⟩ ⟩
      have ha_f := List.all_eq_true.mp ha
      have q2_is_zero : q2 == Z.zero := by
        apply ha_f
        rw [ha'_l]
        exact List.mem_cons_self
      rw [q2_is_zero]
      rw [ha'_r]
      rw [trim_internal_helper_all_zero]
      simp_all [trim_leading_zeros_internal]
      simp at ha
      simp
      intro element
      intro element_in_a'
      have a'_sub_a' : a' ⊆ a' := by exact List.subset_def.mpr fun {a} a_1 => a_1
      have tmp := List.subset_cons_of_subset q2 a'_sub_a'
      rw [←ha'_l] at tmp
      apply ha
      simp_all
  termination_by a

theorem trim_helper_all_zero {k : Type u} [BEq k] [LawfulBEq k] [Z : choose_zero k] (x : k) (a : List k)
  (ha : a.all (fun x ↦ x == Z.zero))
  : trim_polynomial_list (x :: a) = trim_polynomial_list [x] := by
  match a with
  | [] => simp
  | xa :: a' =>
    rw [trim_polynomial_list]
    rw [trim_polynomial_list]
    rw [List.reverse_cons]
    rw [trim_internal_helper_all_zero]
    rw [List.reverse_singleton]
    rw [List.all_reverse]
    assumption


theorem not_all_zero_if_trim_is_not_nil {k : Type u} [BEq k] [LawfulBEq k] [Z : choose_zero k] (a : List k)
  (h : ¬ trim_polynomial_list a = []) : (¬ a.all (fun x ↦ x == Z.zero)) := by
  false_or_by_contra
  apply h
  apply trim_zero_all
  assumption

theorem trim_helper_not_all_zero {k : Type u} [BEq k] [LawfulBEq k] [Z : choose_zero k] (x : k) (a : List k)
  (ha : ¬ a.all (fun x ↦ x == Z.zero))
  : trim_polynomial_list (x :: a) = x :: trim_polynomial_list a := by
  rw [trim_polynomial_list]
  rw [List.reverse_cons]
  rw [trim_internal_helper_not_all_zero]
  rw [List.reverse_append]
  rw [List.reverse_singleton]
  rw [List.singleton_append]
  rw [← trim_polynomial_list]
  rw [List.all_reverse]
  assumption

theorem add_polynomial_of_all_zero {k : Type u} [BEq k] [LawfulBEq k]
  [A : add k] [Z : choose_zero k] (add_zero_left: ∀ x : k, A.add Z.zero x = x)
  (a : List k) (b: List k) (ha : a.all (fun x ↦ (x == Z.zero))) (hb : b.all (fun x ↦ (x == Z.zero)))
  : (add_polynomial a b).all (fun x ↦ (x == Z.zero))
  := by
  match a, b with
  | [], [] => simp
  | [xa], [xb] => simp_all[add_polynomial]
  | [], b' =>
    simp_all [add_polynomial_zero_left_0]
    apply hb
  | a', [] =>
    simp_all [add_polynomial_zero_right_0]
    apply ha
  | xa :: a', xb :: b' =>
    rw [add_polynomial]
    rw [List.all_cons]
    rw [add_polynomial_of_all_zero]
    simp_all
    assumption
    rw [List.all_cons, Bool.and_eq_true_iff] at ha
    apply ha.right
    rw [List.all_cons, Bool.and_eq_true_iff] at hb
    apply hb.right

theorem add_polynomial_of_all_zero' {k : Type u} [BEq k] [LawfulBEq k]
  [A : add k] [Z : choose_zero k] (add_zero_left: ∀ x : k, A.add Z.zero x = x)
  (a : List k) (b: List k) (ha : a.all (fun x ↦ (x == Z.zero))) (hb : b.all (fun x ↦ (x == Z.zero)))
  : trim_polynomial_list (add_polynomial a b) = []
  := by
  rw [trim_zero_all]
  apply add_polynomial_of_all_zero
  repeat assumption

theorem add_polynomial_all_zero_left {k : Type u} [BEq k] [LawfulBEq k]
  [A : add k] [Z : choose_zero k] (add_zero_left: ∀ x : k, A.add Z.zero x = x)
  (a : List k) (b: List k) (ha : a.all (fun x ↦ (x == Z.zero)))
  : trim_polynomial_list (add_polynomial a b) = trim_polynomial_list b := by
  match a, b with
  | [], [] => rw [add_polynomial_zero_left_0]
  | a', [] =>
    rw [add_polynomial_zero_right_0]
    rw [trim_zero_glue_nil]
    rw [trim_zero_all]
    assumption
  | [], b' =>
    rw [add_polynomial_zero_left_0]
  | xa :: a', xb :: b' =>
    rw [add_polynomial]
    rw [cons_respects_trim]
    rw [add_polynomial_all_zero_left]
    simp_all
    rw [←cons_respects_trim]
    assumption
    simp_all
    apply ha.right

theorem add_polynomial_all_zero_right {k : Type u} [BEq k] [LawfulBEq k]
  [A : add k] [Z : choose_zero k] (add_zero_right: ∀ x : k, A.add x Z.zero = x)
  (a : List k) (b: List k) (hb : b.all (fun x ↦ (x == Z.zero)))
  : trim_polynomial_list (add_polynomial a b) = trim_polynomial_list a := by
  match a, b with
  | [], [] => rw [add_polynomial_zero_left_0]
  | a', [] =>
    rw [add_polynomial_zero_right_0]
  | [], b' =>
    rw [add_polynomial_zero_left_0]
    rw [trim_zero_glue_nil]
    rw [trim_zero_all]
    assumption
  | xa :: a', xb :: b' =>
    rw [add_polynomial]
    rw[cons_respects_trim]
    rw[add_polynomial_all_zero_right]
    rw [←cons_respects_trim]
    simp_all
    assumption
    simp_all
    apply hb.right

theorem polynomial_shift_1_respect_trim {k : Type u} [BEq k] [LawfulBEq k] [Z : choose_zero k] (a : List k)
  : trim_polynomial_list ( polynomial_shift_1 a)
  = trim_polynomial_list ( polynomial_shift_1 (trim_polynomial_list a))
  := by
  rw [polynomial_shift_1, polynomial_shift_1]
  rw [cons_respects_trim]

theorem add_polynomial_respect_trim {k : Type u} [BEq k] [LawfulBEq k] [A : additive_monoid k]
  (a : List k) (b : List k)
  : trim_polynomial_list (add_polynomial a b)
  = trim_polynomial_list (add_polynomial (trim_polynomial_list a) (trim_polynomial_list b))
  := by
  match a, b with
  | [], [] => simp [trim_zero_glue_nil]
  | [], b' =>
    rw [add_polynomial_zero_left_0]
    rw [trim_zero_glue_nil]
    rw [add_polynomial_zero_left_0]
    rewrite [trim_polynomial_list_idempotent]
    rfl
  | a', [] =>
    rw [add_polynomial_zero_right_0]
    rw [trim_zero_glue_nil]
    rw [add_polynomial_zero_right_0]
    rewrite [trim_polynomial_list_idempotent]
    rfl
  | [xa] , [xb] =>
    rw [add_polynomial]
    rw [add_polynomial_zero_left_0]
    rw [trim_polynomial_list]
    rw [List.reverse_singleton]
    rw [trim_leading_zeros_internal]
    if hxa : xa == A.zero then
      if xb == A.zero then
        simp_all[trim_polynomial_list, trim_leading_zeros_internal]
      else
        simp_all[trim_polynomial_list, trim_leading_zeros_internal, add_polynomial_zero_left_0]
    else
      if hxb : xb == A.zero then
        simp_all[trim_polynomial_list, trim_leading_zeros_internal, add_polynomial_zero_right_0]
      else
        simp_all[trim_polynomial_list, trim_leading_zeros_internal, add_polynomial]
  | xa :: a', xb :: b' =>
    if ha : a'.all (fun x ↦ x == A.zero) then
      rw [trim_helper_all_zero xa a' ha]
      if hb : b'.all (fun x ↦ x == A.zero) then
        rw [trim_helper_all_zero xb b' hb]
        rw [trim_singleton]
        rw [trim_singleton]
        split
        split
        · case isTrue.isTrue hxa hxb =>
          rw [add_polynomial_zero_left_0]
          rw [trim_zero_glue_nil]
          rw [add_polynomial]
          rw [trim_zero_all]
          rw [List.all_cons]
          rw [add_polynomial_of_all_zero]
          simp
          rw [eq_of_beq hxa]
          rw [A.add_zero_left]
          apply eq_of_beq hxb
          simp_all
          repeat assumption
        · case isTrue.isFalse hxa hxb =>
          rw [add_polynomial_zero_left_0]
          rw [add_polynomial]
          rw [cons_respects_trim]
          rw [add_polynomial_of_all_zero']
          simp_all
          apply A.add_zero_left
          repeat assumption
        split
        · case isFalse.isTrue hxa hxb =>
          rw [add_polynomial_zero_right_0]
          rw [add_polynomial]
          rw [cons_respects_trim]
          rw [add_polynomial_of_all_zero']
          simp_all
          apply A.add_zero_left
          repeat assumption
        · case isFalse.isFalse hxa hxb =>
          rw [add_polynomial]
          rw [add_polynomial]
          rw [add_polynomial_zero_left_0]
          rw [cons_respects_trim]
          rw [add_polynomial_of_all_zero']
          apply A.add_zero_left
          repeat assumption
      else
        rw [trim_helper_not_all_zero xb b' hb]
        rw [add_polynomial]

        conv =>
          lhs
          rw [cons_respects_trim]
          rw [add_polynomial_all_zero_left ]
          rfl
          apply add_zero_left
          apply ha

        repeat rw [←cons_respects_trim]

        if hxa : xa == A.zero then
          rw [eq_of_beq hxa, add_zero_left, trim_zero_glue_singleton, add_polynomial_zero_left_0]
          rw [cons_respects_trim]
        else
          rw [trim_non_zero_singleton]
          rw [add_polynomial, add_polynomial_zero_left_0, cons_respects_trim]
          assumption
    else
      if hb : b'.all (fun x ↦ x == A.zero) then
        conv =>
          rhs
          arg 1
          arg 2
          rw [trim_helper_all_zero]
          rfl
          apply hb
        rw [add_polynomial]
        conv =>
          lhs
          rw [cons_respects_trim]
          rw [add_polynomial_all_zero_right]
          rfl
          apply add_zero_right
          apply hb
        conv =>
          rhs
          rw [trim_helper_not_all_zero]
          rw [trim_singleton]
          rfl
          apply ha

        split
        rw [add_polynomial_zero_right_0]
        simp_all
        rw [add_polynomial, add_polynomial_zero_right_0]
      else
        rw[trim_helper_not_all_zero]
        rw[trim_helper_not_all_zero]
        rw[add_polynomial]
        rw[add_polynomial]
        conv =>
          rhs
          rw [cons_respects_trim]
          rw[←add_polynomial_respect_trim]
          rfl
        rw[cons_respects_trim]
        assumption
        assumption
  termination_by a.length + b.length


theorem add_polynomial_respects_trim_second_arg {k : Type u} [BEq k] [LawfulBEq k]
  [A : additive_monoid k] (a : List k )
  : respect_trim (add_polynomial a)
  := by
  intro b
  rw [add_polynomial_respect_trim]
  conv =>
    rhs
    rw [add_polynomial_respect_trim]
    rfl
  rw [trim_polynomial_list_idempotent]
  repeat assumption

@[simp]
theorem mul_polynomial'_zero_left
  {k : Type u} [Z : choose_zero k] [A : add k] [M : mul k]
  (a : List k)
  :
  mul_polynomial' [] a = []
  := by
  rw [mul_polynomial']

@[simp]
theorem mul_polynomial'_zero_right
  {k : Type u}  [BEq k] [LawfulBEq k] [Z : choose_zero k] [A : add k] [M : mul k]
  (a : List k)
  :
  trim_polynomial_list (mul_polynomial' a []) = []
  := by
  match a with
  | [] =>
    simp [mul_polynomial', trim_zero_glue_nil]
  | x :: a' =>
    rw [mul_polynomial']
    rw [polynomial_left_scalar_action]
    rw[List.map_nil]
    rw[add_polynomial_zero_left_0]
    rw [polynomial_shift_1]
    rw [cons_respects_trim]
    rw [mul_polynomial'_zero_right]
    rw [trim_zero_glue_generator']

@[simp]
theorem mul_zero_scalar_right
  {k : Type u}  [BEq k] [LawfulBEq k] [Z : choose_zero k] [M : mul k]
  (a : k)
  :
  trim_polynomial_list (polynomial_right_scalar_action [] a) = []
  := by
  simp[polynomial_right_scalar_action]

@[simp]
theorem mul_zero_scalar_left
  {k : Type u}  [BEq k] [LawfulBEq k] [Z : choose_zero k] [M : mul k]
  (a : k)
  :
  trim_polynomial_list (polynomial_left_scalar_action a []) = []
  := by
  simp[polynomial_left_scalar_action]

theorem polynomial_scalar_action
  {k : Type u} [BEq k] [LawfulBEq k] [Z : choose_zero k] [A : add k] [M : mul k]
  (add_zero_right: ∀ x : k, A.add x Z.zero = x)
  (a : List k) (s : k)
  :
  trim_polynomial_list (mul_polynomial' [s] a)
  =
  trim_polynomial_list (polynomial_left_scalar_action s a)
  := by
  rw [mul_polynomial']
  rw [mul_polynomial'_zero_left]
  rw [polynomial_shift_1]
  rw [add_polynomial_zero_right_1]
  apply add_zero_right


theorem polynomial_scalar_action'
  {k : Type u} [BEq k] [LawfulBEq k] [A : additive_monoid k] [M : mul k]
  (a : List k) (s : k)
  :
  trim_polynomial_list (mul_polynomial' a [s])
  =
  trim_polynomial_list (polynomial_right_scalar_action a s)
  := by
  match a with
  | [] =>
    simp
  | xa :: a' =>
    rw [mul_polynomial']
    rw [polynomial_left_scalar_action]
    rw [add_polynomial_respect_trim]
    rw [polynomial_shift_1_respect_trim]
    rw [polynomial_scalar_action']
    rw [←polynomial_shift_1_respect_trim]
    rw [←add_polynomial_respect_trim]
    rw [polynomial_shift_1]
    simp
    rw [add_polynomial]
    rw [add_polynomial_zero_left_0]
    rw [polynomial_right_scalar_action]
    rw [add_zero_right]
    rw [polynomial_right_scalar_action]
    rw [List.map_cons]
    repeat assumption

def monomial
  {k : Type u} [Z : choose_zero k] (a : k) (n : Nat)
  :=
  polynomial_shift [a] n

@[simp]
theorem left_identity_is_polynomial_left_identity
  {k : Type u} [BEq k] [LawfulBEq k] [Z : choose_zero k] [A : add k] [M : mul k]
  (k_left_identity : k) (add_zero_right : ∀ x : k, A.add x Z.zero = x)
  (h_identity : is_left_identity M.mul k_left_identity)
  (a : List k)
  :
  trim_polynomial_list (mul_polynomial' [k_left_identity] a)
  =
  trim_polynomial_list a
  := by
  rw [polynomial_scalar_action]
  rw [polynomial_left_identity_scalar_action]
  repeat assumption

@[simp]
theorem right_identity_is_polynomial_right_identity
  {k : Type u} [BEq k] [LawfulBEq k] [A : additive_monoid k] [M : mul k]
  (k_right_identity : k)
  (h_right_identity : is_right_identity M.mul k_right_identity)
  (a : List k)
  :
  trim_polynomial_list (mul_polynomial' a [k_right_identity])
  =
  trim_polynomial_list a
  := by
  rw [polynomial_scalar_action']
  rw [polynomial_right_identity_scalar_action]
  repeat assumption


theorem add_polynomial_scalar_left
  {k : Type u} [BEq k] [LawfulBEq k] [A : add k] (a : List k) (x : k) (y : k)
  : add_polynomial [x] (y :: a) = (A.add x y) :: a := by
  rw [add_polynomial]
  rw [add_polynomial_zero_left_0]

theorem polynomial_left_scalar_action_cons_linear_right
  {k : Type u}  [BEq k] [LawfulBEq k] [Z : choose_zero k] [A : add k] [M : mul k]
  (add_zero_right : ∀ x : k, A.add x Z.zero = x)
  (a : k) (x : k) (b : List k)  :
  trim_polynomial_list (polynomial_left_scalar_action a (x :: b))
  = trim_polynomial_list (add_polynomial
      [M.mul a x]
      (polynomial_shift_1 (polynomial_left_scalar_action a b)))
  := by
  rw [polynomial_left_scalar_action, polynomial_shift_1]
  simp
  rw [add_polynomial_scalar_left]
  rw [add_zero_right]
  rw [polynomial_left_scalar_action]

theorem polynomial_right_scalar_action_cons_linear_left
  {k : Type u}  [BEq k] [LawfulBEq k] [Z : choose_zero k] [A : add k] [M : mul k]
  (add_zero_right : ∀ x : k, A.add x Z.zero = x)
  (a : List k) (x : k) (b : k)  :
  trim_polynomial_list (polynomial_right_scalar_action (x :: a) b)
  = trim_polynomial_list (add_polynomial
      [M.mul x b]
      (polynomial_shift_1 (polynomial_right_scalar_action a b)))
  := by
  rw [polynomial_right_scalar_action, polynomial_shift_1]
  simp
  rw [add_polynomial_scalar_left]
  rw [add_zero_right]
  rw [polynomial_right_scalar_action]

theorem polynomial_shift_1_respects_trim
  {k : Type u} [BEq k] [LawfulBEq k] [choose_zero k] (a : List k)
  : trim_polynomial_list (polynomial_shift_1 a) = trim_polynomial_list (polynomial_shift_1 (trim_polynomial_list a))  := by
  rw [polynomial_shift_1, cons_respects_trim, ←polynomial_shift_1]

theorem polynomial_shift_1_respects_addition
  {k : Type u} [BEq k] [LawfulBEq k] [Z : choose_zero k] [A : add k] (add_zero_right : ∀ x : k, A.add x Z.zero = x) (a : List k) (b : List k) :
  polynomial_shift_1 (add_polynomial a b) = add_polynomial (polynomial_shift_1 a) (polynomial_shift_1 b)
  := by
  rw [polynomial_shift_1, polynomial_shift_1, polynomial_shift_1]
  rw [add_polynomial]
  rw [add_zero_right]


theorem add_polynomial_associative
  {k : Type u} [BEq k] [LawfulBEq k] [A : add k] (add_assoc : is_associative A.add)
  (a : List k) (b : List k) (c : List k):
  add_polynomial a (add_polynomial b c) = add_polynomial (add_polynomial a b) c := by
  match a, b, c with
  | [], b, c => simp [add_polynomial_zero_left_0]
  | a, [], c => simp [add_polynomial_zero_left_0, add_polynomial_zero_right_0]
  | a, b, [] => simp [add_polynomial_zero_right_0]
  | xa :: a', xb :: b', xc :: c' =>
    repeat rw [add_polynomial]
    rw [add_polynomial_associative]
    rw [add_assoc]
    apply add_assoc

theorem add_polynomial_associative'
  {k : Type u} [BEq k] [LawfulBEq k] [A : additive_monoid k] (a : List k) (b : List k) (c : List k):
  trim_polynomial_list (
    add_polynomial
      (trim_polynomial_list a)
      (trim_polynomial_list (add_polynomial (trim_polynomial_list b) (trim_polynomial_list c)))
  )
  =
  trim_polynomial_list (
    add_polynomial
      (trim_polynomial_list (add_polynomial (trim_polynomial_list a) (trim_polynomial_list b)))
      (trim_polynomial_list c)
  ) := by
  conv =>
    rhs
    arg 1
    arg 1
    rw [←add_polynomial_respect_trim]
    rfl
    repeat (tactic => assumption)
  conv =>
    rhs
    rw [←add_polynomial_respect_trim]
    rfl
    repeat (tactic => assumption)

  rw [←add_polynomial_associative]
  conv =>
    rhs
    rw [add_polynomial_respect_trim]
    rfl
    repeat (tactic => assumption)

  conv =>
    rhs
    arg 1
    arg 2
    rw [add_polynomial_respect_trim]
    rfl
    repeat (tactic => assumption)
  apply A.add_is_assoc
  repeat assumption

theorem add_polynomial_symmetric
  {k : Type u} [BEq k] [LawfulBEq k] (A : add k) (k_add_symmetric : is_symmetric_2 A.add) (a : List k) (b : List k):
  (add_polynomial a b) = (add_polynomial b a) := by
  match a, b with
  | [], b =>
    simp[add_polynomial_zero_left_0, add_polynomial_zero_right_0]
  | a, [] =>
    simp[add_polynomial_zero_left_0, add_polynomial_zero_right_0]
  | xa :: a', xb :: b' =>
    rw [add_polynomial, add_polynomial, k_add_symmetric , add_polynomial_symmetric]
    repeat assumption


theorem mul_polynomial'_cons_linear_right
  {k : Type u}
  [BEq k]
  [LawfulBEq k]
  [A : commutative_additive_monoid k]
  [M : mul k]
  (a : List k)
  (x : k)
  (b : List k)  :
  trim_polynomial_list (mul_polynomial' a (x :: b))
  = trim_polynomial_list (add_polynomial (polynomial_right_scalar_action a x)
      (polynomial_shift_1 (mul_polynomial' a b)))
  := by
  match a with
  | [] =>
    rw [mul_polynomial'_zero_left]
    rw [polynomial_right_scalar_action]
    simp
    rw [polynomial_shift_1]
    rw [trim_zero_glue_singleton]
  | x' :: a' =>
    rw[mul_polynomial']
    rw[add_polynomial_respect_trim]
    rw[polynomial_shift_1_respects_trim]
    rw[mul_polynomial'_cons_linear_right]
    rw[←polynomial_shift_1_respects_trim]
    rw[polynomial_shift_1_respects_addition]
    rw[polynomial_left_scalar_action_cons_linear_right]
    rw [←add_polynomial_respect_trim]
    rw [add_polynomial_symmetric]
    rw [add_polynomial_associative]
    conv =>
      lhs
      arg 1
      rw [←add_polynomial_associative]
      arg 2
      rw [add_polynomial_symmetric]
      rfl
      apply A.add_is_comm
      apply A.add_is_assoc
    rw [←add_polynomial_associative]

    conv =>
      lhs
      rw [add_polynomial_respect_trim]
      arg 1
      arg 2
      arg 1
      rw [add_polynomial_associative]
      rfl
      apply A.add_is_assoc


    conv =>
      lhs
      arg 1
      arg 2
      rw [add_polynomial_symmetric]
      rfl
      apply A.add_is_comm

    rw [← add_polynomial_respect_trim]
    conv =>
      lhs
      rw [add_polynomial_associative]
      rfl
      apply A.add_is_assoc

    conv =>
      lhs
      arg 1
      arg 1
      rw [add_polynomial_symmetric]
      rfl
      apply A.add_is_comm
    rw [add_polynomial_respect_trim]
    rw [←polynomial_right_scalar_action_cons_linear_left]

    rw [←polynomial_shift_1_respects_addition]

    conv =>
      lhs
      arg 1
      arg 2
      rw [add_polynomial_symmetric]
      rw [←mul_polynomial']
      rfl
      apply A.add_is_comm

    rw [← add_polynomial_respect_trim]
    apply A.add_zero_right

    apply A.add_zero_right
    apply A.add_is_assoc
    apply A.add_is_assoc
    apply A.add_is_comm
    apply A.add_zero_right
    apply A.add_zero_right

theorem left_and_right_scalar_actions_coincide
  {k : Type u} [BEq k] [LawfulBEq k] [commutative_mul k]
  (a : List k) (s : k)
  : polynomial_left_scalar_action s a = polynomial_right_scalar_action a s
  := by
  rw [polynomial_left_scalar_action, polynomial_right_scalar_action]
  rw [List.map_eq_map_iff]
  intro element
  intro h_element
  apply commutative_mul.mul_is_comm


theorem mul_polynomial'_symmetric
  {k : Type u} [BEq k] [LawfulBEq k]
  [A : commutative_additive_monoid k]
  [M : commutative_multiplicative_monoid k]
  (a : List k) (b : List k)
  :
  trim_polynomial_list (mul_polynomial' a b) = trim_polynomial_list (mul_polynomial' b a)
  := by
  match a with
  | [] =>
    rw [mul_polynomial'_zero_left]
    rw [mul_polynomial'_zero_right]
    exact trim_zero_glue_nil
  | x :: a' =>
    rw [mul_polynomial']
    rw [mul_polynomial'_cons_linear_right]
    conv =>
      lhs
      rw [add_polynomial_respect_trim]
      rfl
      repeat tactic => assumption

    conv =>
      rhs
      rw [add_polynomial_respect_trim]
      rfl
      repeat tactic => assumption

    rw [polynomial_shift_1_respects_trim]
    rw [mul_polynomial'_symmetric]
    rw [←polynomial_shift_1_respects_trim]

    rw [left_and_right_scalar_actions_coincide]


def add_polynomial_safe
  {k : Type u} [Z : choose_zero k] [A : add k] [BEq k] [LawfulBEq k] (a : List k) (b : List k)
  :=
  trim_polynomial_list (add_polynomial (trim_polynomial_list a) (trim_polynomial_list b))

def mul_polynomial_safe
  {k : Type u} [BEq k] [LawfulBEq k] [Z : choose_zero k] [A : add k] [M : mul k]
  (a : List k) (b : List k) :=
  trim_polynomial_list (mul_polynomial' (trim_polynomial_list a) (trim_polynomial_list b))

theorem mul_polynomial_safe_is_symmetric
  {k : Type u} [BEq k] [LawfulBEq k]
  [A : commutative_additive_monoid k]
  [M : commutative_multiplicative_monoid k]
  (a b : List k)
  : mul_polynomial_safe a b = mul_polynomial_safe b a := by
  rw[mul_polynomial_safe]
  rw[mul_polynomial'_symmetric]
  rw[←mul_polynomial_safe]

theorem add_polynomial_safe_is_associative
  {k : Type u} [BEq k] [LawfulBEq k] [additive_monoid k]
  (a : List k) (b : List k) (c : List k):
    add_polynomial_safe a (add_polynomial_safe b c) =
    add_polynomial_safe (add_polynomial_safe a b) c
  := by
  rw [add_polynomial_safe, add_polynomial_safe, add_polynomial_safe, add_polynomial_safe]
  rw [trim_polynomial_list_idempotent, trim_polynomial_list_idempotent]
  rw [add_polynomial_associative']
  repeat assumption

structure reduced_polynomial (k : Type u) [Z : choose_zero k] [BEq k] [LawfulBEq k] where
  value : List k
  is_reduced : trim_polynomial_list value = value


theorem ext_both_directions (k : Type u) [Z : choose_zero k] [BEq k] [LawfulBEq k] {p q : reduced_polynomial k} : p = q ↔ p.value = q.value := by
  constructor
  · intro h; simp [h]
  · intro h; cases p; cases q; simp at h; simp [h]

@[ext]
theorem ext_direct (k : Type u) [Z : choose_zero k] [BEq k] [LawfulBEq k] {p q : reduced_polynomial k}
  (values_are_equal : p.value = q.value) :  p = q := by
  cases p;
  cases q;
  simp at values_are_equal
  simp [values_are_equal]

theorem ext_reverse (k : Type u) [Z : choose_zero k] [BEq k] [LawfulBEq k] {p q : reduced_polynomial k}
  (h : p = q) : p.value = q.value := by
  cases p;
  cases q;
  simp at h
  simp [h]

instance reduced_are_BEq (k : Type u) [Z : choose_zero k] [BEq k] [LawfulBEq k] : BEq (reduced_polynomial k) where
  beq := by
    intro a
    intro b
    apply a.value == b.value

instance {k : Type u} [Z : choose_zero k] [BEq k] [LawfulBEq k] : LawfulBEq (reduced_polynomial k) where
  eq_of_beq := by
    intro a b
    rw [BEq.beq]
    rw [reduced_are_BEq]
    intro a_eq_b
    simp_all
    apply ext_direct
    assumption
  rfl := by
    intro a
    rw [BEq.beq]
    rw [reduced_are_BEq]
    simp


theorem add_polynomial_safe_is_reduced
  {k : Type u} [Z : choose_zero k] [A : add k]
  [BEq k] [LawfulBEq k]
  (a : List k) (b : List k)
  : trim_polynomial_list (add_polynomial_safe a b) = add_polynomial_safe a b
  := by
  rw [add_polynomial_safe]
  rw [trim_polynomial_list_idempotent]

theorem mul_polynomial_safe_is_reduced
  {k : Type u} [BEq k] [LawfulBEq k] [Z : choose_zero k] [A : add k] [M : mul k]
  (a : List k) (b : List k)
  : trim_polynomial_list (mul_polynomial_safe a b)
  = mul_polynomial_safe a b
  := by
  rw [mul_polynomial_safe]
  rw [trim_polynomial_list_idempotent]

def add_reduced_polynomial
  {k : Type u} [Z : choose_zero k] [A : add k]
  [BEq k] [LawfulBEq k]
  (a : reduced_polynomial k) (b : reduced_polynomial k)
  : reduced_polynomial k
  := {
    value := add_polynomial_safe a.value b.value
    is_reduced := by
      apply add_polynomial_safe_is_reduced
  }

def mul_reduced_polynomial
  {k : Type u} [BEq k] [LawfulBEq k] [Z : choose_zero k] [A : add k] [M : mul k]
  (a : reduced_polynomial k) (b : reduced_polynomial k)
  : reduced_polynomial k
  := {
    value := mul_polynomial_safe a.value b.value
    is_reduced := by
      apply mul_polynomial_safe_is_reduced
  }

def add_inverse {k : Type u} {R : ring k} [BEq k] [LawfulBEq k] (a : reduced_polynomial k) : List k :=
  a.value.map R.add_inverse

structure reduced_polynomial_ring_data_layout (k : Type u) [ring k] [BEq k] [LawfulBEq k] where
  add : reduced_polynomial k → reduced_polynomial k  → reduced_polynomial k
  mul : reduced_polynomial k → reduced_polynomial k  → reduced_polynomial k
  add_inverse : reduced_polynomial k → reduced_polynomial k



@[simp]
theorem no_leading_zero_after_trimming_leading_zero {k : Type u} [BEq k] [LawfulBEq k]
  [Z : choose_zero k]
  (a : List k) (b :List k) (c : k) (h : trim_leading_zeros_internal a = c :: b) :
  ¬ c = Z.zero := by
  rw [trim_leading_zeros_internal.eq_def] at h
  split at h
  simp_all
  split at h
  apply no_leading_zero_after_trimming_leading_zero
  assumption
  simp_all

theorem reduced_iff_non_zero_tail {k : Type u} [BEq k] [LawfulBEq k] [Z : choose_zero k] (s : k) (a : List k)
  :  trim_polynomial_list (a ++ [s]) = (a ++ [s]) ↔ ¬ s = Z.zero := by
  constructor
  intro h
  rw [trim_polynomial_list] at h
  simp_all
  rw [trim_leading_zeros_internal] at h
  false_or_by_contra
  simp_all
  have afsds := no_leading_zero_after_trimming_leading_zero a.reverse a.reverse Z.zero h
  apply afsds
  rfl

  intro s_not_zero
  rw [trim_polynomial_list]
  simp
  rw [trim_leading_zeros_internal]
  simp_all

@[simp]
theorem reduced_tail_of_reduced_internal {R : ring k} [BEq k] [LawfulBEq k]
  (x : k) (a : List k) (h : trim_leading_zeros_internal (a ++ [x]) = a ++ [x]) :
  trim_leading_zeros_internal a = a := by
  rw [trim_leading_zeros_internal.eq_def] at h
  split at h
  case h_1 a' ha' =>
    simp_all
  case h_2 a' a'' ha =>
    have ha' :=List.cons_eq_append_iff.mp (Eq.symm ha)
    rcases ha' with ha'1 |ha'2
    · case inl =>
      simp_all [trim_leading_zeros_internal]
    · case inr =>
      rcases ha'2 with ⟨ q, ⟨ qq, qqq ⟩  ⟩
      rw [qq]
      rw [trim_leading_zeros_internal]
      split
      case isTrue a'_is_zero =>
        rw [qq] at ha
        have q_def := (List.cons_inj_right a').mp ha
        rw [qq] at h
        simp at a'_is_zero
        rw [a'_is_zero] at h
        simp at h
        have dafe := no_leading_zero_after_trimming_leading_zero a'' (q ++ [x]) R.zero h
        contradiction
      case isFalse a'_is_not_zero =>
        rfl

theorem a_decomposition {k : Type u} (a : List k) (x : k) : ∃ c, ∃ aq, x :: a = aq ++ [c] :=
    match a with
    | [] => ⟨ x, by simp ⟩
    | xa :: a' => by
      rcases a_decomposition a' xa with ⟨ tail, head, tail_is_okay ⟩
      rw [tail_is_okay]
      exists tail, (x :: head)


@[simp]
theorem reduced_of_reduced_tail {R : ring k} [BEq k] [LawfulBEq k]
  (x : k) (x' : k) (a : List k) (h : trim_polynomial_list (x :: a) = (x :: a)) :
  trim_polynomial_list (x' :: (x :: a)) = (x' :: (x :: a)) := by
  have a_d := a_decomposition a x
  rcases a_d with ⟨ tail, head, valid_decomposition ⟩
  rw [valid_decomposition]
  repeat rw [←List.cons_append]
  rw [valid_decomposition] at h
  have non_zero_tail := (reduced_iff_non_zero_tail tail head).mp h
  apply (reduced_iff_non_zero_tail tail (x' :: head)).mpr
  apply non_zero_tail

theorem reduced_tail_of_reduced {R : ring k} [BEq k] [LawfulBEq k]
  (x : k) (a : List k) (h : trim_polynomial_list (x :: a) = x :: a) :
  trim_polynomial_list a = a := by
  rw [trim_polynomial_list] at *
  simp_all
  rw [reduced_tail_of_reduced_internal]
  apply List.reverse_reverse
  apply x
  apply h

theorem add_inverse_is_reduced (k : Type u) [R : ring k] [BEq k] [LawfulBEq k]
  (a : List k)
  (is_reduced : trim_polynomial_list a = a)
  :
  trim_polynomial_list (a.map R.add_inverse) = a.map R.add_inverse := by
  match a with
  | [] =>
    simp
  | [xa] =>
    simp_all [trim_singleton]
    apply add_inverse_of_non_zero_is_non_zero
    apply is_reduced
  | xa :: xa' :: a' =>
    have xa'_a'_is_reduced := reduced_tail_of_reduced xa (xa' :: a') is_reduced
    have a'_is_reduced := reduced_tail_of_reduced xa' a' (reduced_tail_of_reduced xa (xa' :: a') is_reduced)
    have a'_inversed_is_reduced := add_inverse_is_reduced k a' a'_is_reduced
    rw [List.map_cons, List.map_cons]
    apply reduced_of_reduced_tail
    rw [←List.map_cons]
    apply add_inverse_is_reduced
    apply reduced_tail_of_reduced xa
    apply is_reduced

theorem inverse_is_left_inverse (R : ring k) [BEq k] [LawfulBEq k] (a : List k) :
  trim_polynomial_list (add_polynomial (a.map R.add_inverse) a) = [] :=
  by
  match a with
  | [] => simp
  | x :: a =>
    rw [List.map_cons]
    rw [add_polynomial]
    rw [cons_respects_trim]
    rw [R.add_inverse_is_inverse]
    rw [inverse_is_left_inverse]
    apply trim_zero_glue_singleton

theorem polynomial_left_scalar_action_left_linear (R : ring k) [BEq k] [LawfulBEq k] (x y : k) (a : List k) :
  (polynomial_left_scalar_action (R.add x y) a)
  =
  (add_polynomial (polynomial_left_scalar_action x a) (polynomial_left_scalar_action y a))
  := by
  repeat rw [polynomial_left_scalar_action]
  match a with
  | [] => simp
  | xa :: a' =>
    simp
    rw [add_polynomial]
    rw [R.mul_is_linear_left x y xa]
    apply (List.cons_inj_right _).mpr
    rw [←polynomial_left_scalar_action]
    rw [polynomial_left_scalar_action_left_linear]
    rw [polynomial_left_scalar_action, polynomial_left_scalar_action]

theorem polynomial_left_scalar_action_right_linear (R : ring k) [BEq k] [LawfulBEq k] (x : k) (a b : List k) :
  (polynomial_left_scalar_action x (add_polynomial  a b) )
  =
  (add_polynomial (polynomial_left_scalar_action x a) (polynomial_left_scalar_action x b))
  := by
  repeat rw [polynomial_left_scalar_action]
  match a, b with
  | [], [] => simp
  | [], _ => simp
  | _, [] => simp
  | xa :: a, xb :: b =>
    rw [List.map_cons]
    rw [List.map_cons]
    rw [add_polynomial]
    rw [add_polynomial]
    rw [List.map_cons]
    rw [R.mul_is_comm]
    rw [R.mul_is_linear_left]
    rw [R.mul_is_comm]
    conv =>
      lhs
      arg 1
      arg 2
      rw [R.mul_is_comm]
    apply (List.cons_inj_right _).mpr
    rw [←polynomial_left_scalar_action]
    rw [←polynomial_left_scalar_action]
    rw [←polynomial_left_scalar_action]
    apply polynomial_left_scalar_action_right_linear

theorem mul_polynomial_is_left_linear (R : ring k) [BEq k] [LawfulBEq k] (a : List k) (b : List k) (c : List k) :
  trim_polynomial_list (mul_polynomial' ( add_polynomial a b ) c)
  =
  trim_polynomial_list (add_polynomial ( mul_polynomial' a c ) ( mul_polynomial' b c ) )
  := by
  match a, b with
  | [], [] => simp
  | [], b => simp
  | a, [] => simp
  | xa :: a', xb :: b' =>
    rw [add_polynomial]
    rw [mul_polynomial']
    rw [add_polynomial_respect_trim]
    rw [polynomial_shift_1_respect_trim]
    rw [mul_polynomial_is_left_linear]
    rw [← polynomial_shift_1_respect_trim]
    rw [← add_polynomial_respect_trim]
    rw [polynomial_left_scalar_action_left_linear]
    rw [mul_polynomial']
    rw [mul_polynomial']
    rw [add_polynomial_associative]
    rw [polynomial_shift_1_respects_addition]
    rw [add_polynomial_associative]

    conv =>
      arg 1
      arg 1
      arg 1
      rw [←add_polynomial_associative]
      arg 2
      rw [add_polynomial_symmetric]
      repeat tactic => assumption
      rfl
      repeat tactic => assumption
      apply R.add_is_comm
      apply R.add_is_assoc

    rw [add_polynomial_associative]
    apply R.add_is_assoc
    apply R.add_is_assoc
    apply R.add_zero_right
    apply R.add_is_assoc

def trim_polynomial_list' {k : Type u} [BEq k] [LawfulBEq k] [choose_zero k] (a : List k) : List k :=
  match a with
  | [] => []
  | x :: a' =>
    match trim_polynomial_list a' with
    | [] => trim_polynomial_list [x]
    | a_trimmed => x :: a_trimmed

@[simp]
theorem trim_definitions_are_equivalent {k : Type u} [BEq k] [LawfulBEq k] [choose_zero k] (a : List k)
  : trim_polynomial_list' a = trim_polynomial_list a
  := by
  symm
  rw [trim_polynomial_list'.eq_def]
  split
  simp
  split
  rw [cons_respects_trim]
  case h_1 q1 q2 q3 q4 q5 q6 =>
    rw [trim_helper_all_zero]
    rw [q6]
    simp
  case h_2 q1 q2 q3 q4 q5 q6 =>
    rw [trim_helper_not_all_zero]
    apply not_all_zero_if_trim_is_not_nil
    apply q6


theorem trim_is_nil_if_all_zero {k : Type u} [BEq k] [LawfulBEq k] [Z : choose_zero k] (a : List k)
  (ha : a.all (fun x ↦ x == Z.zero))
  : trim_polynomial_list  a = [] := by
  match a with
  | [] => simp
  | xa :: a' =>
    rw [←trim_definitions_are_equivalent]
    rw [trim_polynomial_list']
    split
    case h_1 =>
      simp at ha
      rw [ha.left]
      simp
    case h_2 q1 q2 q3 =>
      rw [List.all] at ha
      rw [Bool.and_eq_true_iff] at ha
      have qq := trim_is_nil_if_all_zero a' ha.right
      contradiction

theorem all_zero_if_trim_is_nil {k : Type u} [BEq k] [LawfulBEq k] [Z : choose_zero k] (a : List k)
  (ha : trim_polynomial_list a = [])
  : a.all (fun x ↦ x == Z.zero) := by
  match a with
  | [] => simp_all
  | xa :: a' =>
    rw [←trim_definitions_are_equivalent] at ha
    rw [trim_polynomial_list'] at ha
    split at ha
    case h_1 q qq =>
      rw [List.all_cons]
      rw [Bool.and_eq_true]
      and_intros
      rw [trim_singleton] at ha
      simp_all
      apply all_zero_if_trim_is_nil
      apply qq
    case h_2 q qq =>
      rw [List.all_cons]
      rw [Bool.and_eq_true]
      and_intros
      have qqq := List.cons_ne_nil _ _ ha
      contradiction
      have qqq := List.cons_ne_nil _ _ ha
      contradiction


theorem polynomial_left_scalar_action_respects_trim  (R : ring k) [BEq k] [LawfulBEq k] (x : k) (a : List k)
  :
  trim_polynomial_list (polynomial_left_scalar_action x ( trim_polynomial_list a))
  =
  trim_polynomial_list (polynomial_left_scalar_action x a)
  := by
  match a with
  | [] => simp
  | xa :: a' =>
    repeat rw [←trim_definitions_are_equivalent]
    rw [trim_polynomial_list']
    repeat rw [trim_definitions_are_equivalent]

    split
    case h_1 q1 q2 =>

      -- rw [polynomial_left_scalar_action_respects_trim]
      rw [polynomial_left_scalar_action]
      -- simp_all
      rw [polynomial_left_scalar_action]
      simp_all
      conv =>
        rhs
        rw [cons_respects_trim]
      have ha' := all_zero_if_trim_is_nil a' q2
      rw [←polynomial_left_scalar_action]
      rw [←polynomial_left_scalar_action]
      conv =>
        rhs
        rw [←polynomial_left_scalar_action_respects_trim]
      rw [q2]
      simp_all [trim_singleton, polynomial_left_scalar_action]
      rw [apply_ite (List.map (R.mul x))]
      rw [apply_ite (trim_polynomial_list)]
      simp_all
      if xa = R.zero then
        simp_all
      else
        simp_all
        rw [trim_singleton]
    case h_2 q1 q2 =>
      conv =>
        rhs
        rw [polynomial_left_scalar_action]
        rw [List.map_cons]
        rw [←polynomial_left_scalar_action]
        rw [cons_respects_trim]
        rw [←polynomial_left_scalar_action_respects_trim]
        rw [←cons_respects_trim]
        rw [polynomial_left_scalar_action]
        rw [←List.map_cons]
        rw [←polynomial_left_scalar_action]
  termination_by a


theorem mul_polynomial_respects_trim_1  (R : ring k) [BEq k] [LawfulBEq k] (a : List k) (b : List k)
  :
  trim_polynomial_list
    (mul_polynomial' (trim_polynomial_list a) b)
  =
  trim_polynomial_list
    (mul_polynomial' a b)
  := by
  match a with
  | [] => simp
  | xa :: a' =>
    conv =>
      lhs
      arg 1
      rw [← trim_definitions_are_equivalent]
      rw [trim_polynomial_list']
    split
    case h_1 q1 q2 =>
      rw [mul_polynomial']
      conv =>
        rhs
        rw [add_polynomial_respect_trim]
        rw [polynomial_shift_1_respect_trim]
        rw [←mul_polynomial_respects_trim_1]
        rfl
      rw [q2]
      simp_all [polynomial_shift_1]
      rw [trim_singleton]
      split
      rw [polynomial_left_scalar_action]
      simp_all
      apply trim_zero_all
      simp_all
      case isFalse w1 w2 =>
        rw [mul_polynomial']
        simp_all [polynomial_shift_1, polynomial_left_scalar_action]
    case h_2 q1 q2 =>
      rw [mul_polynomial']
      rw [add_polynomial_respect_trim]
      rw [polynomial_shift_1_respect_trim]
      rw [mul_polynomial_respects_trim_1]
      rw [←polynomial_shift_1_respect_trim]
      rw [←add_polynomial_respect_trim]
      rw [←mul_polynomial']

theorem mul_polynomial_respects_trim  (R : ring k) [BEq k] [LawfulBEq k] (a : List k) (b : List k)
  :
  trim_polynomial_list
    (mul_polynomial' (trim_polynomial_list a) (trim_polynomial_list b))
  =
  trim_polynomial_list
    (mul_polynomial' a b)
  := by
  match a with
  | [] => simp
  | xa :: a' =>
    rw [mul_polynomial']
    rw [add_polynomial_respect_trim]
    rw [←polynomial_left_scalar_action_respects_trim]
    rw [polynomial_shift_1_respect_trim]
    conv =>
      rhs
      rw[←mul_polynomial_respects_trim]

    rw [←polynomial_shift_1_respect_trim]
    rw [←add_polynomial_respect_trim]
    rw [←mul_polynomial']
    conv =>
      rhs
      rw [←mul_polynomial_respects_trim_1]
    rw [←cons_respects_trim]

theorem left_scalar_action_is_associative (R : ring k) [BEq k] [LawfulBEq k]
  (a : k) (b : List k) (c : List k) :
  trim_polynomial_list (mul_polynomial' (polynomial_left_scalar_action a b) c)
  =
  trim_polynomial_list (polynomial_left_scalar_action a (mul_polynomial' b c))
  := by
  match b with
  | [] =>
    simp_all [polynomial_left_scalar_action]
  | x :: b' =>
    rw [mul_polynomial']
    rw [polynomial_left_scalar_action]
    rw [List.map_cons]
    rw [mul_polynomial']
    rw [← polynomial_left_scalar_action]
    rw [add_polynomial_respect_trim]
    rw [polynomial_shift_1_respect_trim]
    rw [left_scalar_action_is_associative]
    rw [← polynomial_shift_1_respect_trim]
    rw [← add_polynomial_respect_trim]
    rw [polynomial_shift_1]
    rw [polynomial_shift_1]

    rw [polynomial_left_scalar_action_right_linear]


    rw [polynomial_left_scalar_action]
    rw [polynomial_left_scalar_action]
    rw [polynomial_left_scalar_action]
    rw [polynomial_left_scalar_action]

    rw [List.map_map]

    have h_mul_comp (a b: k) : R.mul a ∘ R.mul b = R.mul (R.mul a b) := by
      ext
      simp
      rw [R.mul_is_assoc]
    rw [h_mul_comp]

    rw [polynomial_left_scalar_action]
    rw [List.map_cons]

    conv =>
      rhs
      arg 1
      arg 2
      rw [R.mul_is_comm]
      rw [mul_zero_any_is_zero]

theorem left_scalar_action_zero (R : ring k) [BEq k] [LawfulBEq k] (a : List k) :
  trim_polynomial_list (polynomial_left_scalar_action R.zero a) = []
  := by
  apply trim_is_nil_if_all_zero
  rw [polynomial_left_scalar_action]
  simp

theorem mul_polynomial_is_associative (R : ring k) [BEq k] [LawfulBEq k]
  (a : List k) (b : List k) (c : List k) :
  trim_polynomial_list (mul_polynomial' (mul_polynomial' a b) c)
  =
  trim_polynomial_list (mul_polynomial' a (mul_polynomial' b c))
  := by
  match a with
  | [] => simp
  | x :: a' =>
    rw [mul_polynomial']
    -- rw [mul_polynomial']
    rw [mul_polynomial_is_left_linear]

    rw [mul_polynomial']
    rw [add_polynomial_respect_trim]
    rw [polynomial_shift_1]
    rw [mul_polynomial']
    conv =>
      lhs
      arg 1
      arg 2
      rw [add_polynomial_respect_trim]
      rw [polynomial_shift_1_respect_trim]
      rfl
    rw [mul_polynomial_is_associative]
    repeat rw [polynomial_shift_1]
    rw [← cons_respects_trim]
    conv =>
      lhs
      arg 1
      arg 2
      rw [← add_polynomial_respect_trim]
      rfl
    rw [left_scalar_action_is_associative]
    conv =>
      rhs
      rw [add_polynomial_respect_trim]
      rfl
    congr  2
    rw [add_polynomial_respect_trim]
    rw [left_scalar_action_zero]
    rw [add_polynomial_zero_left_0]
    rw [trim_polynomial_list_idempotent]

def reduced_polynomial_ring_example (k : Type u) [R : ring k] [BEq k] [LawfulBEq k] : reduced_polynomial_ring_data_layout k :=
  {
    add := add_reduced_polynomial
    mul := mul_reduced_polynomial
    add_inverse (a : reduced_polynomial k) := {
      value := a.value.map R.add_inverse
      is_reduced := by
        apply add_inverse_is_reduced k a.value
        apply a.is_reduced
    }
  }

instance polynomial_ring
  (k : Type u) [R : ring k] [BEq k] [LawfulBEq k]: ring (reduced_polynomial k) :=
  {
    add := add_reduced_polynomial
    zero := {
      value := []
      is_reduced := by
        apply trim_zero_glue_nil
    }
    add_inverse (a : reduced_polynomial k) := {
      value := a.value.map R.add_inverse
      is_reduced := by
        apply add_inverse_is_reduced k a.value
        apply a.is_reduced
    }
    mul := mul_reduced_polynomial
    e := {
      value := trim_polynomial_list [R.e]
      is_reduced := by apply trim_polynomial_list_idempotent
    }
    -- non_trivial := by
      -- simp
    add_inverse_is_inverse := by
      rw [is_left_inverse]
      intro a
      rw [add_reduced_polynomial]
      simp [add_polynomial_safe]
      rw [←add_polynomial_respect_trim]
      apply inverse_is_left_inverse
    add_is_comm := by
      intro a b
      rw [add_reduced_polynomial, add_reduced_polynomial]
      simp
      rw [add_polynomial_safe]
      rw [add_polynomial_symmetric]
      rw [←add_polynomial_safe]
      apply R.add_is_comm
    mul_is_comm := by
      intro a b
      simp [mul_reduced_polynomial, mul_reduced_polynomial]
      rw [mul_polynomial_safe_is_symmetric]
    mul_e_left := by
      intro a
      rw [mul_reduced_polynomial]
      apply ext_direct
      simp
      rw [mul_polynomial_safe]
      rw [trim_singleton]
      split
      simp_all
      rw [←a.is_reduced]
      apply trim_zero_all
      simp_all [e_eq_zero_then_one_element]
      simp_all [a.is_reduced]
    add_zero_left := by
      intro a
      simp [add_reduced_polynomial, add_polynomial_safe, trim_zero_glue_nil]
      apply ext_direct
      simp
      rw [a.is_reduced]
    mul_is_linear_left := by
      intro a b c
      repeat rw [mul_reduced_polynomial]
      repeat rw [add_reduced_polynomial]
      simp
      repeat rw [add_polynomial_safe]
      repeat rw [mul_polynomial_safe]
      repeat rw [←add_polynomial_respect_trim]
      rw [a.is_reduced]
      rw [b.is_reduced]
      rw [←mul_polynomial_is_left_linear]
      rw [trim_polynomial_list_idempotent]
      rw [mul_polynomial_respects_trim]
      rw [c.is_reduced]
    mul_is_linear_right := by
      intro a b c
      repeat rw [mul_reduced_polynomial]
      repeat rw [add_reduced_polynomial]
      simp
      repeat rw [add_polynomial_safe]
      repeat rw [mul_polynomial_safe]
      rw [mul_polynomial'_symmetric]
      rw [←a.is_reduced]
      rw [b.is_reduced]
      rw [c.is_reduced]
      rw [mul_polynomial_respects_trim]
      rw [mul_polynomial_respects_trim]
      rw [mul_polynomial_is_left_linear]
      repeat rw [a.is_reduced]
      rw [add_polynomial_respect_trim]
      rw [add_polynomial_respect_trim]
      rw [mul_polynomial'_symmetric]
      conv =>
        rhs
        arg 1
        arg 2
        rw [mul_polynomial'_symmetric]
    add_is_assoc := by
      intro a b c
      repeat rw [add_reduced_polynomial]
      simp
      rw [add_polynomial_safe_is_associative]
    mul_is_assoc := by
      intro a b c
      rw [mul_reduced_polynomial]
      rw [mul_reduced_polynomial]
      rw [mul_reduced_polynomial]
      rw [mul_reduced_polynomial]
      simp
      rw [mul_polynomial_safe]
      rw [mul_polynomial_safe]
      rw [mul_polynomial_safe]
      rw [mul_polynomial_safe]
      simp
      repeat rw [mul_polynomial_respects_trim]
      rw [mul_polynomial_is_associative]
      rw [a.is_reduced, b.is_reduced, c.is_reduced]
    mul_e_right := by
      intro a
      rw [mul_reduced_polynomial]
      apply ext_direct
      simp
      rw [mul_polynomial_safe]
      rw [trim_singleton]
      split
      simp_all
      rw [←a.is_reduced]
      apply trim_zero_all
      simp_all [e_eq_zero_then_one_element]
      simp_all [a.is_reduced]
    add_zero_right := by
      intro a
      simp [add_reduced_polynomial, add_polynomial_safe, a.is_reduced]
  }

theorem polynomial_ring_add {k : Type u} [ring k] [BEq k] [LawfulBEq k] (a b : reduced_polynomial k) :
  a ⊹ b = add_reduced_polynomial a b := by
  exact ext_direct k rfl

theorem polynomial_ring_mul {k : Type u} [ring k] [BEq k] [LawfulBEq k] (a b : reduced_polynomial k) :
  a * b = mul_reduced_polynomial a b := by
  exact ext_direct k rfl

theorem polynomial_ring_e {k : Type u} [R : ring k] [BEq k] [LawfulBEq k] :
  (polynomial_ring k).e.value = trim_polynomial_list [R.e]:= by
  rfl

def eval_polynomial'
  {base : Type v} [ring base]
  {target : Type u} [ring target]
  (eval_x : target) (f : base → target) (a : List base)
  : target
  :=
  match a with
  | [] => choose_zero.zero
  | xa :: a' => f xa ⊹ eval_x * (eval_polynomial' eval_x f a')

def eval_polynomial
  {base : Type v} [ring base]
  {target : Type u} [ring target]
  (eval_x : target) (f : ring_hom₁ base target) (a : List base)
  : target
  :=
  match a with
  | [] => choose_zero.zero
  | xa :: a' => f.original_function xa ⊹ eval_x * (eval_polynomial eval_x f a')


-- set_option trace.Meta.synthInstance true

@[simp]
theorem eval_polynomial_ignores_trim
  {base : Type v} [Rb : ring base] [BEq base] [LawfulBEq base]
  {target : Type u} [Rt : ring target]
  (eval_x : target) (f : ring_hom₁ base target)
  (x : List base) :
  eval_polynomial eval_x f (trim_polynomial_list x) = eval_polynomial eval_x f x
  := by
  match x with
  | [] => simp
  | xi :: x' =>
    rw [eval_polynomial]
    conv =>
      rhs
      rw [←eval_polynomial_ignores_trim]
      rfl
    rw [←trim_definitions_are_equivalent]
    rw [trim_polynomial_list']
    split
    simp_all [eval_polynomial]
    rw [trim_singleton]
    rw [eval_polynomial.eq_def]
    split
    simp_all
    case h_2 q qq qqq =>
      split at qqq
      simp_all
      simp_all [eval_polynomial]
    rw [eval_polynomial]

theorem eval_polynomial_add
  {base : Type v} [ring base] [BEq base] [LawfulBEq base]
  {target : Type u} [ring target]
  (eval_x : target) (f : ring_hom₁ base target)
  (x y : List base)
  : eval_polynomial eval_x f (add_polynomial x y) = (eval_polynomial eval_x f x) ⊹ (eval_polynomial eval_x f y)
  := by
  match x, y with
  | [], [] =>
    simp [eval_polynomial]
  | x', [] =>
    simp [eval_polynomial]
  | [], y' =>
    simp [eval_polynomial]
  | xi :: x', yi :: y'=>
    rw [eval_polynomial]
    rw [eval_polynomial]
    rw [additive_monoid.add_is_assoc]
    conv =>
      rhs
      arg 2
      arg 2
      rw [commutative_additive_monoid.add_is_comm]
    conv =>
      rhs
      arg 2
      rw [←additive_monoid.add_is_assoc]
    rw [←ring.mul_is_linear_right]
    rw [←eval_polynomial_add]
    rw [←additive_monoid.add_is_assoc]
    rw [commutative_additive_monoid.add_is_comm]
    rw [←additive_monoid.add_is_assoc]
    rw [←additive_monoid_hom₁.map_add]
    rw [←eval_polynomial]
    rw [commutative_additive_monoid.add_is_comm]
    rw [add_polynomial_commutes_with_cons]


theorem polynomial_left_scalar_action_is_mul
  {k : Type u} [BEq k] [LawfulBEq k]
  [A : additive_monoid k] [M : mul k]
  (s : k) (a : List k) :
  trim_polynomial_list (polynomial_left_scalar_action s a) = trim_polynomial_list (mul_polynomial' [s] a) := by
  rw [mul_polynomial']
  simp [polynomial_shift_1]

theorem polynomial_right_scalar_action_is_mul
  {k : Type u} [BEq k] [LawfulBEq k]
  [A : commutative_additive_monoid k] [M : mul k]
  (a : List k) (s : k) :
  trim_polynomial_list (polynomial_right_scalar_action a s) = trim_polynomial_list (mul_polynomial' a [s]) := by
  rw [mul_polynomial'_cons_linear_right]
  rw [add_polynomial_respect_trim]
  rw [polynomial_shift_1_respect_trim]
  simp [polynomial_shift_1]

theorem eval_polynomial_mul
  {base : Type v} [ring base] [BEq base] [LawfulBEq base]
  {target : Type u} [ring target]
  (eval_x : target) (f : ring_hom₁ base target)
  (x y : List base)
  : eval_polynomial eval_x f (mul_polynomial' x y) = (eval_polynomial eval_x f x) * (eval_polynomial eval_x f y)
  := by
  match x, y with
  | [], [] =>
    simp [eval_polynomial]
  | x', [] =>
    simp [eval_polynomial]
    rw [←eval_polynomial_ignores_trim]
    simp [eval_polynomial]
  | [], y' =>
    simp [eval_polynomial]
  | xi :: x', yi :: y'=>
    rw [eval_polynomial]
    rw [eval_polynomial]

    rw [ring.mul_is_linear_left]
    rw [ring.mul_is_linear_right]
    rw [ring.mul_is_linear_right]
    conv =>
      rhs
      arg 2
      arg 2
      arg 2
      rw [commutative_mul.mul_is_comm]
    conv =>
      rhs
      arg 2
      arg 2
      rw [multiplicative_monoid.mul_is_assoc]
      arg 2
      rw [←multiplicative_monoid.mul_is_assoc]
    rw [←eval_polynomial_mul]

    rw [←eval_polynomial_ignores_trim]
    rw [mul_polynomial'_cons_linear_right]
    rw [mul_polynomial']
    rw [polynomial_shift_1]
    rw [polynomial_shift_1]
    rw [eval_polynomial_ignores_trim]
    rw [eval_polynomial_add]
    rw [eval_polynomial]
    rw [←eval_polynomial_ignores_trim]
    rw [polynomial_right_scalar_action_cons_linear_left]
    rw [eval_polynomial_ignores_trim]
    rw [eval_polynomial_add]
    rw [eval_polynomial_add]
    rw [polynomial_shift_1]
    simp [eval_polynomial]
    rw [ring_hom₁.map_mul]
    rw [ring.mul_is_linear_right]
    repeat rw [←additive_monoid.add_is_assoc]
    congr 1
    repeat rw [additive_monoid.add_is_assoc]
    congr 1
    rw [←eval_polynomial_ignores_trim]
    rw [polynomial_right_scalar_action_is_mul]
    rw [eval_polynomial_ignores_trim]
    rw [commutative_additive_monoid.add_is_comm]
    congr 1
    rw [←multiplicative_monoid.mul_is_assoc]
    conv =>
      rhs
      arg 1
      rw [commutative_mul.mul_is_comm]
    rw [multiplicative_monoid.mul_is_assoc]
    congr 1
    rw [←eval_polynomial_ignores_trim]
    rw [polynomial_left_scalar_action_is_mul]
    rw [eval_polynomial_ignores_trim]
    rw [eval_polynomial_mul]
    simp [eval_polynomial]
    rw [eval_polynomial_mul]
    simp [eval_polynomial, multiplicative_monoid.mul_is_assoc]
    congr 1
    apply commutative_multiplicative_monoid.mul_is_comm
    apply add_zero_right
  termination_by x.length + y.length


def eval_polynomial_ring_arrow
  {base : Type v} [ring base] [BEq base] [LawfulBEq base]
  {target : Type} [ring target]
  (f : ring_hom₁ base target) (eval_x : target)
  : ring_hom₁ (reduced_polynomial base) target :=
  {
    original_function (x) := eval_polynomial eval_x f x.value
    map_add (a b) := by
      rw [polynomial_ring_add]
      rw [add_reduced_polynomial]
      simp_all
      rw [add_polynomial_safe]
      rw [←add_polynomial_respect_trim]
      rw [eval_polynomial_ignores_trim]
      rw [eval_polynomial_add]
    map_zero := by
      simp [eval_polynomial]
    map_e := by
      rw [polynomial_ring_e]
      rw [eval_polynomial_ignores_trim]
      rw [eval_polynomial]
      rw [eval_polynomial]
      simp_all
      apply f.map_e
    map_mul := by
      intro a b
      rw [polynomial_ring_mul]
      rw [mul_reduced_polynomial]
      simp
      rw [mul_polynomial_safe]
      simp [eval_polynomial_mul]
  }

def base_inclusion
  {base : Type v} [BEq base] [LawfulBEq base] [ring base]
  (x : base) : reduced_polynomial base :=
  {
    value := trim_polynomial_list [x]
    is_reduced := by exact trim_polynomial_list_idempotent [x]
  }

def inclusion_base_to_free_algebra
  {base : Type v} [BEq base] [LawfulBEq base] [ring base]
  : ring_hom₁ base (reduced_polynomial base)
  :=
  {
    original_function := base_inclusion
    map_add := by
      intro a b
      apply ext_direct
      simp [
        base_inclusion, polynomial_ring_add,
        add_reduced_polynomial, add_polynomial_safe,
        ←add_polynomial_respect_trim, add_polynomial]
    map_zero := by
      simp [base_inclusion]
      rfl
    map_e := by
      simp [base_inclusion]
      rfl
    map_mul := by
      intro a b
      apply ext_direct
      simp [base_inclusion, polynomial_ring_mul, mul_reduced_polynomial, mul_polynomial_safe, mul_polynomial_respects_trim,
      mul_polynomial', polynomial_shift_1, polynomial_left_scalar_action]
  }

instance free_algebra_over_ring {base : Type v} [ring base] [BEq base] [LawfulBEq base] : free_algebra base (reduced_polynomial base) :=
  {
    var := {
      value := trim_polynomial_list [choose_zero.zero, choose_e.e]
      is_reduced := by apply trim_polynomial_list_idempotent
    }
    induced_map f fx := eval_polynomial_ring_arrow f fx
    induced_map_is_valid := by
      intro target target_ring f fx
      rw [eval_polynomial_ring_arrow]
      simp [eval_polynomial]
      rw [f.map_e]
      simp
  }



-- @[reducible]
-- def polynomial_string
--   (k : Type u) [R : ring_to_string k] [BEq k] [LawfulBEq k] (variable_name : String)
--   : ring_to_string (reduced_polynomial k) where
--   toString (x : reduced_polynomial k) := convert_polynomial_to_string k R.zero x.value variable_name 0

-- instance polynomial_for_print (k : Type u) [R : ring_to_string k] [BEq k] [LawfulBEq k] (variable_name : String) : ring

instance : choose_zero Nat where
  zero := 0

instance : add Nat where
  add := Nat.add

instance : mul Nat where
  mul := Nat.mul


instance Z : ring_to_string Int := {
  add := Int.add
  add_inverse := Int.neg
  mul := Int.mul
  e := 1
  zero := 0
  add_inverse_is_inverse := by
    simp
    intro a
    rw [Int.add_comm]
    rw [←Int.sub_self a]
    rfl
  add_is_comm :=by simp; apply Int.add_comm
  add_is_assoc := by simp; apply Int.add_assoc
  mul_is_comm := by simp; apply Int.mul_comm
  mul_is_assoc := by simp; apply Int.mul_assoc
  mul_e_left := by simp
  add_zero_left := by simp
  mul_e_right := by simp
  add_zero_right := by simp
  mul_is_linear_left :=
    by
    intro a b c
    apply Int.add_mul
  mul_is_linear_right := by
    intro a b c
    apply Int.mul_add
}


class polynomials_with_string_representation
  (k : Type u) [BEq k] [LawfulBEq k] [choose_zero k] [ToString k] (X : String) extends reduced_polynomial k
  -- where
  -- base : reduced_polynomial k
  -- var := X

@[reducible, simp]
def silly_convert {k : Type u} [BEq k] [ring k] [LawfulBEq k] [choose_zero k] [ToString k] (x : reduced_polynomial k) (X : String) : polynomials_with_string_representation k X :=
  {
    value := x.value
    is_reduced := x.is_reduced
  }


theorem ext_both_directions_print  (k : Type u) [Z : choose_zero k] [ToString k]  [BEq k] [LawfulBEq k] (X : String) {p q : polynomials_with_string_representation k X} : p = q ↔ p.value = q.value := by
  constructor
  · intro h;
    rw[h]
  · intro h;
    rcases p with ⟨ pv, pvr ⟩
    rcases q with ⟨ qv, qvr ⟩
    simp_all;


@[ext]
theorem ext_direct_print (k : Type u) [Z : choose_zero k] [ToString k] [BEq k] [LawfulBEq k] (X : String) {p q : polynomials_with_string_representation k X}
  (values_are_equal : p.value = q.value) :  p = q := by
  apply (ext_both_directions_print k X).mpr
  assumption

theorem ext_reverse_print (k : Type u) [Z : choose_zero k] [ToString k] [BEq k] [LawfulBEq k] (X : String) {p q : polynomials_with_string_representation k X}
  (h : p = q) : (p.value = q.value) := by
  apply (ext_both_directions_print k X).mp
  assumption

@[reducible]
def silly_add {k : Type u} [BEq k] [R : ring k] [LawfulBEq k] [ToString k] (X : String) (a b : polynomials_with_string_representation k X) : polynomials_with_string_representation k X
  := silly_convert ((polynomial_ring k).add a.toreduced_polynomial b.toreduced_polynomial) X


@[reducible]
def silly_mul {k : Type u} [BEq k] [R : ring k] [LawfulBEq k] [ToString k] (X : String) (a b : polynomials_with_string_representation k X) : polynomials_with_string_representation k X
  := silly_convert ((polynomial_ring k).mul a.toreduced_polynomial b.toreduced_polynomial) X

-- theorem silly_add_silly : silly_add a b = silly_add (silly_convert a) (silly_convert b)

@[reducible]
instance polynomials_with_string_representation_are_ring
  (k : Type u) [BEq k] [R : ring k] [LawfulBEq k] [ToString k] (X : String) : ring (polynomials_with_string_representation k X) :=
  {
    zero := silly_convert (polynomial_ring k).zero X
    add (a b) := silly_add X a b
    add_zero_left := by
      intro a
      rw [silly_add]
      rw [silly_convert]
      rw [silly_convert]
      simp
    add_zero_right := by
      intro a
      rw [silly_add]
      rw [silly_convert]
      rw [silly_convert]
      simp
    add_is_assoc := by
      intro a b c
      rw [silly_add]
      rw [silly_add]
      rw [silly_add]
      rw [silly_add]
      rw [silly_convert]
      rw [silly_convert]
      rw [silly_convert]
      rw [silly_convert]
      simp
      rw [(polynomial_ring k).add_is_assoc]
    add_is_comm := by
      intro a b
      rw [silly_add]
      rw [silly_add]
      rw [silly_convert]
      rw [silly_convert]
      rw [(polynomial_ring k).add_is_comm]
    mul (a b) := silly_mul X a b
    e := silly_convert (polynomial_ring k).e X
    mul_e_right := by
      intro a
      rw [silly_mul]
      rw [silly_convert]
      rw [silly_convert]
      simp
    mul_e_left := by
      intro a
      rw [silly_mul]
      rw [silly_convert]
      rw [silly_convert]
      simp
    mul_is_assoc := by
      intro a b c
      rw [silly_mul]
      rw [silly_mul]
      rw [silly_mul]
      rw [silly_mul]
      rw [silly_convert]
      rw [silly_convert]
      rw [silly_convert]
      rw [silly_convert]
      simp
      rw [(polynomial_ring k).mul_is_assoc]
    mul_is_comm := by
      intro a b
      rw [silly_mul]
      rw [silly_mul]
      rw [silly_convert]
      rw [silly_convert]
      rw [(polynomial_ring k).mul_is_comm]
    add_inverse (x) := silly_convert ((polynomial_ring k).add_inverse x.toreduced_polynomial) X
    add_inverse_is_inverse := by
      intro a
      simp
      rw [silly_add]
      rw [silly_convert]
      simp
      apply ext_direct_print
      simp
      congr
      apply (polynomial_ring k).add_inverse_is_inverse
    mul_is_linear_left := by
      intro a b c
      simp
      rw [silly_mul]
      rw [silly_mul]
      rw [silly_mul]
      rw [silly_add]
      rw [silly_add]
      rw [silly_convert]
      rw [silly_convert]
      rw [silly_convert]
      rw [silly_convert]
      rw [silly_convert]
      apply ext_direct_print
      simp
      rw [(polynomial_ring k).mul_is_linear_left]
    mul_is_linear_right := by
      intro a b c
      simp
      rw [silly_mul]
      rw [silly_mul]
      rw [silly_mul]
      rw [silly_add]
      rw [silly_add]
      rw [silly_convert]
      rw [silly_convert]
      rw [silly_convert]
      rw [silly_convert]
      rw [silly_convert]
      apply ext_direct_print
      simp
      rw [(polynomial_ring k).mul_is_linear_right]
  }


def monom_repr {k : Type u}
  [BEq k] [LawfulBEq k] [ToString k]
  (zero : k) (one : k) (power : Nat) (X: String) (x: k) (not_last : Bool)
  := if x == zero then "" else (if power == 0 ∨ ¬x == one then ToString.toString x else "") ++ (if power > 0 then X ++ Nat.toSuperscriptString power else "") ++ if not_last then " + " else ""

def convert_polynomial_to_sequence
  (k : Type u)
  [BEq k] [LawfulBEq k] [ToString k] (zero : k) (one : k) (p : List k) (element : String) (power : Nat)
  : List String :=
  match p with
  | [] => []
  | [x] => [monom_repr zero one power element x False]
  | x :: p' =>
    (monom_repr zero one power element x True)
    :: (convert_polynomial_to_sequence k zero one p' element (power + 1))

def concat_strings (a : List String) :=
  match a with
  | [] => ""
  | q :: a' => q ++ (concat_strings a')

def  convert_polynomial_to_string
  (k : Type u) [BEq k] [LawfulBEq k] [ToString k] (zero : k) (one : k) (p : List k) (element : String) (power : Nat) : String :=
  match convert_polynomial_to_sequence k zero one p element power with
  | [] => ""
  | [x] => x
  | a => concat_strings a

instance polynomial_has_string
  (k : Type u) [Z : choose_zero k] [E : choose_e k] [ToString k] [BEq k] [LawfulBEq k] (X : String)
  : ToString (polynomials_with_string_representation k X)
  where
  toString (x) := (convert_polynomial_to_string k Z.zero E.e x.value X 0)

@[simp]
def zero_polynomial : reduced_polynomial Int := {
  value := []
  is_reduced := by simp
}

@[simp]
def e_polynomial : reduced_polynomial Int := {
  value := [1]
  is_reduced :=
    by
    simp [trim_polynomial_list, trim_leading_zeros_internal]
    apply Int.one_ne_zero
}

@[simp]
def generator : reduced_polynomial Int := {
  value := [0, 1]
  is_reduced :=by
    simp_all [trim_polynomial_list, trim_leading_zeros_internal]
    have hh := Int.one_ne_zero
    intro h
    contradiction
}

instance printable_are_BEq (k : Type u) [ToString k] [Z : choose_zero k] [BEq k] [LawfulBEq k] (X : String) : BEq (polynomials_with_string_representation k X) where
  beq := by
    intro a
    intro b
    apply a.value == b.value

instance {k : Type u} [ToString k] [Z : choose_zero k] [BEq k] [LawfulBEq k] (X : String) : LawfulBEq (polynomials_with_string_representation k X) where
  eq_of_beq := by
    intro a b
    rw [BEq.beq]
    rw [printable_are_BEq]
    intro a_eq_b
    simp_all
    apply ext_direct_print
    assumption
  rfl := by
    intro a
    rw [BEq.beq]
    rw [printable_are_BEq]
    simp

@[reducible]
def polynomial (k : Type u) [ToString k] [BEq k] [LawfulBEq k] [R : ring k] (X : String) := polynomials_with_string_representation k X


-- @[reducible]
-- def Z_x := polynomial Int var1
-- @[reducible]
-- def Z_xy := polynomial_ring (polynomial Int)

def var1 := "α"
def var2 := "β"

@[reducible]
def p1 : polynomial (polynomial Int var1) var2 := {
  value := [silly_convert generator var1]
  is_reduced := by
    simp [trim_polynomial_list, trim_leading_zeros_internal, silly_convert]
    intro h
    have q := (ext_reverse_print Int var1) h
    simp at q
  }


@[reducible]
def p2 : polynomial (polynomial Int var1) var2 := {
  value := [silly_convert zero_polynomial var1, silly_convert e_polynomial var1]
  is_reduced := by
    simp [trim_polynomial_list, trim_leading_zeros_internal, silly_convert]
    split
    simp
    intro h
    have q := (ext_reverse_print Int var1) h
    simp at q
    intro h
    have q := (ext_reverse_print Int var1) h
    simp at q
}

def to_str := ("(" ++ (polynomial_has_string (polynomial Int var1) var2).toString · ++ ")")

@[reducible]
def mul_xy := (polynomials_with_string_representation_are_ring (polynomial Int var1) var2).mul

@[reducible]
def q := (p1 ⊹ p2)

def str := to_str q ++ " * " ++ to_str q ++ " * " ++ to_str q ++ " == " ++ to_str ( (q * q) * q )

#eval str

@[reducible]
def q3 :=  (q * q) * q

@[simp]
def to_print
  {base : Type v} [BEq base] [LawfulBEq base] [ring base] [ToString base] (X : String)
  : ring_hom₁ (reduced_polynomial base) (polynomials_with_string_representation base X)
  :=
  {
    original_function := (silly_convert · X)
    map_add := by
      intro a b
      apply ext_direct_print
      simp
    map_zero := by
      simp
      rfl
    map_e := by
      simp
      rfl
    map_mul := by
      intro a b
      apply ext_direct_print
      simp
  }

@[simp]
def from_print
  {base : Type v} [BEq base] [LawfulBEq base] [ring base] [ToString base] (X : String)
  : ring_hom₁  (polynomials_with_string_representation base X) (reduced_polynomial base)
  :=
  {
    original_function (x) := {
      value := x.value
      is_reduced := x.is_reduced
    }
    map_add := by
      intro a b
      exact ext_direct base rfl
    map_zero := by
      exact ext_direct base rfl
    map_e := by
      exact ext_direct base rfl
    map_mul := by
      intro a b
      exact ext_direct base rfl
  }

instance
  print_polynomial_algebra
  (base : Type) [ToString base] [ring base] [BEq base] [LawfulBEq base] (X : String)
  : free_algebra base (polynomials_with_string_representation base X) :=
  {
    var := {
      value := trim_polynomial_list [choose_zero.zero, choose_e.e]
      is_reduced := by apply trim_polynomial_list_idempotent
    }
    induced_map f fx :=
      compose_ring_hom (from_print X) (free_algebra_over_ring.induced_map f fx)
    induced_map_is_valid := by
      intro target target_ring f fx
      simp
      exact (free_algebra_over_ring).induced_map_is_valid f fx
  }



def base_inclusion_example
  : ring_hom₁ (polynomial Int var1) (polynomial (polynomial Int var1) var2)
  := by
  apply compose_ring_hom inclusion_base_to_free_algebra
  apply to_print

@[reducible]
def a := to_print var2 (inclusion_base_to_free_algebra (print_polynomial_algebra Int var1).var)
@[reducible]
def b := (print_polynomial_algebra (polynomial Int var1) var2).var
@[reducible]
def A := (print_polynomial_algebra (polynomial Int var1) var2)

@[reducible]
def eval_poly (p : polynomial (polynomial Int var1) var2) (arg : polynomial (polynomial Int var1) var2) :=
  (A.induced_map base_inclusion_example arg).original_function p

#eval eval_poly (a ⊹ b) (b * (b * b))

@[reducible]
def evaluated := eval_polynomial q (compose_ring_hom inclusion_base_to_free_algebra (to_print var2)) q3.value

#eval to_str q3 ++ " evaluated at " ++ var2 ++ " = " ++ to_str q ++ " is equal to " ++ to_str evaluated



def mul_nat_polynomial (a : List Nat) (b : List Nat) := mul_polynomial' a b

-- #eval convert_polynomial_to_string Nat 0 (trim_polynomial_list (mul_nat_polynomial [1, 2, 1, 0] [1, 2, 1])) var1 0
