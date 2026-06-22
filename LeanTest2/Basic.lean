def hello := "world"

@[simp]
def is_symmetric_2 {k : Type}  (m : k → k → k) :=
  ∀ a, ∀ b, m a b = m b a

@[simp]
def is_left_identity {k : Type} (m : k → k → k) (e : k) :=
  ∀ a, m e a = a

@[simp]
def is_right_identity {k : Type} (m : k → k → k) (e : k) :=
  ∀ a, m a e = a

@[simp]
def is_associative {k : Type} (m : k → k → k) :=
  ∀ a, ∀ b, ∀ c, m (m a b) c = m a (m b c)


theorem left_identity_is_right_identity
  (k : Type)
  (m : k → k → k)
  (le : k)  (le_is_left_identity : is_left_identity m le)
  (re : k)  (re_is_right_identity : is_right_identity m re)
  :
  (le = re)
  := by
  rw [is_right_identity] at re_is_right_identity
  rw [is_left_identity] at le_is_left_identity
  have h := le_is_left_identity re
  rw [←le_is_left_identity re]
  rw [re_is_right_identity]

@[simp]
def is_left_linear {k : Type} (add : k → k → k) (mul: k → k → k) :=
  ∀ a, ∀ b, ∀ c, mul (add a b) c = add (mul a c) (mul b c)

@[simp]
def is_right_linear {k : Type} (add : k → k → k) (mul: k → k → k) :=
  ∀ a, ∀ b, ∀ c, mul a (add b c) = add (mul a b) (mul a c)

@[simp]
def is_left_inverse {k : Type} (m : k → k → k) (e : k) (inv: k → k) :=
  ∀ a, m (inv a) a =e

@[simp]
def is_right_inverse {k : Type} (m : k → k → k) (e : k) (inv: k → k) :=
  ∀ a, m a (inv a) =e

class ring where
  k : Type
  add : k → k → k
  add_inverse : k → k
  mul : k → k → k
  e : k
  zero : k
  non_trivial : ¬ e = zero
  add_inverse_is_inverse : is_left_inverse add zero add_inverse
  add_is_comm : is_symmetric_2 add
  add_is_assoc : is_associative add
  mul_is_comm : is_symmetric_2 mul
  mul_is_assoc : is_associative mul
  e_is_left_identity : is_left_identity mul e
  zero_is_left_identity : is_left_identity add zero
  e_is_right_identity : is_right_identity mul e
  zero_is_right_identity : is_right_identity add zero
  mul_is_linear : is_left_linear add mul

theorem add_inverse_of_non_zero_is_non_zero (R : ring) (a : R.k) (ha : ¬a = R.zero)
  : ¬ R.add_inverse a = R.zero
  := by
  intro q
  apply ha
  have h_a_add_inverse := R.add_inverse_is_inverse a
  rw [q] at h_a_add_inverse
  rw [R.zero_is_left_identity] at h_a_add_inverse
  apply h_a_add_inverse

theorem left_inverse_is_right_inverse (k : Type) (e : k)
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


theorem ring_left_inverse_is_right_inverse (R : ring) : is_right_inverse R.add R.zero R.add_inverse := by
  simp
  intro x
  rw [R.add_is_comm]
  apply R.add_inverse_is_inverse

theorem left_inverse_is_unique (R : ring)
  (x : R.k)
  (left_inv : R.k) (h_left_inv : R.add left_inv x = R.zero)
  : left_inv = R.add_inverse x := by
  have h : R.zero = R.zero := rfl
  have ri := ring_left_inverse_is_right_inverse R x
  rw [←R.zero_is_right_identity left_inv]
  rw [←ri]
  rw [←R.add_is_assoc]
  rw [h_left_inv]
  rw [R.zero_is_left_identity]


theorem mul_zero_any_is_zero (R : ring) (a : R.k)
  : R.mul R.zero a = R.zero
  := by
  rw [←R.zero_is_right_identity (R.mul R.zero a)]
  have ri := ring_left_inverse_is_right_inverse R (R.mul R.zero a)
  conv =>
    lhs
    arg 2
    rw [←ri]
  rw [←R.add_is_assoc]
  rw [←R.mul_is_linear]
  rw [R.zero_is_left_identity]
  rw [ri]


theorem inverse_respects_mul (R : ring) (a : R.k) (b : R.k)
  : R.mul (R.add_inverse a) b = R.add_inverse (R.mul a b)
  := by
  apply left_inverse_is_unique
  rw [←R.mul_is_linear]
  rw [R.add_inverse_is_inverse]
  apply mul_zero_any_is_zero


class field extends ring where
  mul_inverse : k → k
  mul_inverse_is_inverse : is_left_inverse mul e mul_inverse

def affine_space (k : Type) (n : Nat) :=
  match n with
  | 0 => Unit
  | d + 1 => affine_space k d × k


def coordinate {k : Type} {n : Nat} (zero : k) : affine_space k n → Nat → k :=
match n with
| 0 => fun _ _ => zero
| d+1 => fun (p : affine_space k (d+1)) (i : Nat) =>
  match p, i with
  | (_, x), 0   => x
  | (rest, _), i+1 => coordinate zero (rest : affine_space k d) i


def point235 : affine_space Nat 3 := ((((), 2), 3), 5)
#eval coordinate 0 point235 0
#eval coordinate 0 point235 1
#eval coordinate 0 point235 2
#eval coordinate 0 point235 3
#eval coordinate 0 point235 4

inductive polynomial_degree_type where
  | bottom : polynomial_degree_type
  | value : Nat → polynomial_degree_type

def trim_coeff {k : Type} (is_zero : k → Bool) (a : Array k) : Array k :=
  if h : a.size = 0 then a else (if is_zero a.back then trim_coeff is_zero (a.pop) else a)
  termination_by a.size

def trim_leading_zeros_internal {k : Type} [BEq k] [LawfulBEq k] (zero : k) (a : List k) : List k :=
  match a with
  | [] => a
  | x :: a' => if x == zero then trim_leading_zeros_internal zero a' else a


theorem trim_leading_zeros_internal_idempotent {k : Type} [BEq k] [LawfulBEq k] (zero : k) (a : List k) :
  trim_leading_zeros_internal zero (trim_leading_zeros_internal zero a) = trim_leading_zeros_internal zero a
  := by
  -- rw [trim_leading_zeros_internal.eq_def]
  match a with
  | [] => simp [trim_leading_zeros_internal]
  | x :: a' =>
    if hx : x == zero then
      rw [trim_leading_zeros_internal]
      simp [hx]
      rw [trim_leading_zeros_internal_idempotent]
    else
      rw [trim_leading_zeros_internal]
      simp [hx]
      rw [trim_leading_zeros_internal]
      simp [hx]


def trim_polynomial_list {k : Type} [BEq k] [LawfulBEq k] (zero : k) (a : List k) : List k :=
  (trim_leading_zeros_internal zero a.reverse).reverse



@[simp]
theorem trim_polynomial_list_idempotent {k : Type} [BEq k] [LawfulBEq k] (zero : k) (a : List k) :
  trim_polynomial_list zero (trim_polynomial_list zero a) = trim_polynomial_list zero a
  := by
  simp [trim_polynomial_list, trim_leading_zeros_internal_idempotent]

@[simp]
theorem trim_zero_glue_generator_internal
  {k : Type} [BEq k] [LawfulBEq k] (zero : k)
  (a : List k) : trim_leading_zeros_internal zero (zero :: a) = trim_leading_zeros_internal zero  a
  := by
  rw [trim_leading_zeros_internal]
  simp

@[simp]
theorem trim_zero_glue_generator_internal'
  {k : Type} [BEq k] [LawfulBEq k] (zero : k) : trim_leading_zeros_internal zero ([zero]) = []
  := by
  repeat rw [trim_leading_zeros_internal]
  simp

@[simp]
theorem trim_zero_glue_generator
  {k : Type} [BEq k] [LawfulBEq k] (zero : k)
  (a : List k) : trim_polynomial_list zero (a ++ [zero]) = trim_polynomial_list zero a
  := by
  rw [trim_polynomial_list]
  rw [trim_polynomial_list]
  rw [List.reverse_concat]
  rw [trim_zero_glue_generator_internal]

@[simp]
theorem trim_zero_glue_generator'
  {k : Type} [BEq k] [LawfulBEq k] (zero : k) : trim_polynomial_list zero ([zero]) = []
  := by
  rw [trim_polynomial_list]
  rw [List.reverse_singleton]
  rw [trim_zero_glue_generator_internal']
  rw [List.reverse_nil]

@[simp]
theorem trim_zero_glue_nil
  {k : Type} [BEq k] [LawfulBEq k] (zero : k) : trim_polynomial_list zero [] = []
  := by
  rw [trim_polynomial_list]
  rw [List.reverse_nil]
  rw [trim_leading_zeros_internal]
  rw [List.reverse_nil]

@[simp]
theorem trim_zero_glue_singleton
  {k : Type} [BEq k] [LawfulBEq k] (zero : k) : trim_polynomial_list zero ([zero]) = []
  := by
  simp [trim_polynomial_list, trim_leading_zeros_internal]

@[simp]
theorem trim_non_zero_singleton
  {k : Type} [BEq k] [LawfulBEq k] (zero : k) (x: k) (hx : ¬(x == zero)) : trim_polynomial_list zero ([x]) = [x]
  := by
  simp_all [trim_polynomial_list, trim_leading_zeros_internal]

theorem trim_singleton {k : Type} [BEq k] [LawfulBEq k] (zero : k) (x: k)
  : trim_polynomial_list zero ([x]) = if x == zero then [] else [x] := by
  grind [trim_zero_glue_singleton, trim_non_zero_singleton]

theorem trim_respects_zero_pop
  {k : Type} (is_zero : k → Bool)
  (a : Array k) (non_empty : 0 < a.size) (zero_at_back : is_zero a.back)
  :
  trim_coeff is_zero a = trim_coeff is_zero a.pop := by
  rw [trim_coeff]
  have non_empty' := Nat.ne_zero_iff_zero_lt.mpr non_empty
  split
  contradiction
  rfl

theorem pop_preserves_array {k : Type} (a : Array k) (i : Nat) (h : i <a.pop.size) (h' : i < a.size) : a.pop[i] = a[i] := by
  exact Array.getElem_pop h

theorem empty_trim_condition {k : Type} (is_zero : k → Bool) (a : Array k) (h : (trim_coeff is_zero a).size = 0) :
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


def array_degree {k : Type} (p : Array k) : polynomial_degree_type :=
  match p.size with
  | 0 => polynomial_degree_type.bottom
  | d + 1 => polynomial_degree_type.value d

def get_coeff_array  {k : Type} (zero : k) (p : Array k) (i : Nat) : k :=
  if h : i < p.size then p[i] else zero

def get_coeff_list  {k : Type} (zero : k) (p : List k) (i : Nat) : k :=
  match p[i]? with
  | none => zero
  | some x => x

theorem zero_array_has_zero_coeffs
  {k : Type} [BEq k] [LawfulBEq k] (zero : k)
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
  {k : Type} [BEq k] [LawfulBEq k] (zero : k)
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
  {k : Type} (k_zero : k) (k_mul : k → k → k)
  (a : Array k) (b : Array k) (i : Nat) (j : Nat) : k
  :=
  let ca := get_coeff_array k_zero a i
  let cb := get_coeff_array k_zero b j
  k_mul ca cb

def mul_polynomial_list_at_degree_internal_summand
  {k : Type} (k_zero : k) (k_mul : k → k → k)
  (a : List k) (b : List k) (i : Nat) (j : Nat) : k
  :=
  let ca := get_coeff_list k_zero a i
  let cb := get_coeff_list k_zero b j
  k_mul ca cb

theorem mul_polynomial_at_degree_internal_summand_symmetry
  {k : Type}  (k_zero : k) (k_mul : k → k → k) (mul_comm : is_symmetric_2 k_mul)
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
  {k : Type} (k_zero : k) (k_mul : k → k → k) (k_add : k →  k → k)
  (a : List k) (b : List k) (d : Nat) (current : Nat) (acc : k) : k
  :=
  let current_summand := mul_polynomial_list_at_degree_internal_summand k_zero k_mul a b current (d - current)
  match current with
  | 0 => k_add acc current_summand
  | i + 1 => mul_polynomial_list_at_degree_internal k_zero k_mul k_add a b d i (k_add acc (k_add acc current_summand))

theorem mul_polynomial_at_degree_zero_polynomial_left
  {k : Type} [BEq k]  [LawfulBEq k]  (k_zero : k) (k_mul : k → k → k) (k_add : k →  k → k)
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
  {k : Type} [BEq k]  [LawfulBEq k]  (k_zero : k) (k_mul : k → k → k) (k_add : k →  k → k)
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
  {k : Type} (k_zero : k) (k_mul : k → k → k) (k_add : k →  k → k)
  (a : List k) (b : List k) (d : Nat) : k
  :=
  mul_polynomial_list_at_degree_internal k_zero k_mul k_add a b d d k_zero

theorem mul_polynomial_at_degree_zero_polynomial_left'
  {k : Type} [BEq k]  [LawfulBEq k]  (k_zero : k) (k_mul : k → k → k) (k_add : k →  k → k)
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
  {k : Type} [BEq k]  [LawfulBEq k]  (k_zero : k) (k_mul : k → k → k) (k_add : k →  k → k)
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
  {k : Type} (k_zero : k) (k_mul : k → k → k) (k_add : k →  k → k)
  (a : List k) (b : List k) (current : Nat) (acc : List k)
  :=
  let mul_at_current := mul_polynomial_list_at_degree k_zero k_mul k_add a b current
  match current with
  | 0 => mul_at_current :: acc
  | next_current + 1 => mul_polynomial_internal k_zero k_mul k_add a b next_current (mul_at_current :: acc)

theorem mul_polynomial_zero_left_internal
  {k : Type} [BEq k] [LawfulBEq k]  (k_zero : k) (k_mul : k → k → k) (k_add : k →  k → k)
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
  {k : Type} (k_zero : k) (k_mul : k → k → k) (k_add : k →  k → k)
  (a : List k) (b : List k)
  :=
  mul_polynomial_internal k_zero k_mul k_add a b 0 []

theorem mul_polynomial_zero_left
  {k : Type} [BEq k] [LawfulBEq k]  (k_zero : k) (k_mul : k → k → k) (k_add : k →  k → k)
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
  {k : Type} (k_add : k →  k → k)
  (a : List k) (b : List k) : List k
  :=
  match a, b with
  | [], [] => []
  | [], b' => b'
  | a', [] => a'
  | xa :: a', xb :: b' => k_add xa xb :: (add_polynomial k_add a' b')

@[simp]
theorem add_polynomial_zero_left_0
  {k : Type} [BEq k] [LawfulBEq k] (k_add : k →  k → k)
  (a : List k)
  :
  add_polynomial k_add [] a = a
  := by
  rw [add_polynomial.eq_def]
  split
  repeat rfl
  simp_all

@[simp]
theorem add_polynomial_zero_right_0
  {k : Type} [BEq k] [LawfulBEq k] (k_add : k →  k → k)
  (a : List k)
  :
  add_polynomial k_add a [] = a
  := by
  rw [add_polynomial.eq_def]
  split
  repeat rfl
  simp_all

@[simp]
theorem add_polynomial_zero_left_1
  {k : Type} [BEq k] [LawfulBEq k] (k_zero : k) (k_add : k →  k → k)
  (add_zero_left : ∀ x : k, k_add k_zero x = x)
  (a : List k)
  :
  trim_polynomial_list k_zero (add_polynomial k_add [k_zero] a) = trim_polynomial_list k_zero a
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
  {k : Type} [BEq k] [LawfulBEq k] (k_zero : k) (k_add : k →  k → k)
  (add_zero_right: ∀ x : k, k_add x k_zero = x)
  (a : List k)
  :
  trim_polynomial_list k_zero (add_polynomial k_add a [k_zero]) = trim_polynomial_list k_zero a
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
  {k : Type} (k_zero : k)
  (a : List k) (n : Nat) : List k
  :=
  match n with
  | 0 => a
  | i + 1 => k_zero :: polynomial_shift k_zero a i

def polynomial_shift_1
  {k : Type} (k_zero : k) (a : List k) : List k
  :=
  k_zero :: a

def polynomial_left_scalar_action
  {k : Type} (k_mul : k → k → k)
  (s : k) (a : List k) : List k
  :=
  a.map (k_mul s)

def polynomial_right_scalar_action
  {k : Type} (k_mul : k → k → k)
  (a : List k) (s : k) : List k
  :=
  a.map (k_mul . s)

@[simp]
theorem polynomial_left_identity_scalar_action
  {k : Type} (k_mul : k → k → k)
  (a : List k)  (k_left_identity : k) (h_identity : is_left_identity k_mul k_left_identity)
  : polynomial_left_scalar_action k_mul k_left_identity a = a
  := by
  rw [polynomial_left_scalar_action]
  exact List.map_id'' h_identity a

@[simp]
theorem polynomial_right_identity_scalar_action
  {k : Type} (k_mul : k → k → k)
  (a : List k)  (k_right_identity : k) (h_identity : is_right_identity k_mul k_right_identity)
  : polynomial_right_scalar_action k_mul a k_right_identity = a
  := by
  rw [polynomial_right_scalar_action]
  exact List.map_id'' h_identity a

def mul_polynomial'
  {k : Type} (k_zero : k) (k_mul : k → k → k) (k_add : k →  k → k)
  (a : List k) (b : List k) : List k
  :=
  match a with
  | [] => []
  | x :: a' =>
    add_polynomial k_add
      (polynomial_left_scalar_action k_mul x b)
      (polynomial_shift_1 k_zero (mul_polynomial' k_zero k_mul k_add a' b))



def mul_polynomial''
  {k : Type} (k_zero : k) (k_mul : k → k → k) (k_add : k →  k → k)
  (a : List k) (b : List k) : List k
  :=
  match b with
  | [] => []
  | x :: b' =>
    add_polynomial k_add
      (polynomial_right_scalar_action k_mul a x)
      (polynomial_shift_1 k_zero (mul_polynomial' k_zero k_mul k_add a b'))

def respect_trim {k : Type}  [BEq k] [LawfulBEq k] (k_zero : k) (f : List k → List k)
  := ∀ a, trim_polynomial_list k_zero (f a) = trim_polynomial_list k_zero (f (trim_polynomial_list k_zero a))

def respect_trim_2 {k : Type}  [BEq k] [LawfulBEq k] (k_zero : k) (f : List k → List k → List k)
  := ∀ a, ∀ b, trim_polynomial_list k_zero (f a b) = trim_polynomial_list k_zero (f (trim_polynomial_list k_zero a) (trim_polynomial_list k_zero b))

def respect_trim_internal {k : Type}  [BEq k] [LawfulBEq k] (k_zero : k) (f : List k → List k)
  := ∀ a, trim_leading_zeros_internal k_zero (f a) = trim_leading_zeros_internal k_zero (f (trim_leading_zeros_internal k_zero a))

theorem append_respects_trim_internal {k : Type} [BEq k] [LawfulBEq k] (k_zero : k) (x : k)
  : respect_trim_internal k_zero (. ++ [x])
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


theorem add_polynomial_commutes_with_cons {k : Type} [BEq k] [LawfulBEq k] (k_add : k →  k → k) :
  ∀ a, ∀ b, ∀ xa, ∀ xb,
  (k_add xa xb) :: (add_polynomial k_add a b)
  = (add_polynomial k_add (xa :: a) (xb :: b)) := by
  intro a b xa xb
  match a, b with
  | [], [] => simp [add_polynomial]
  | [], b => simp [add_polynomial_zero_left_0, add_polynomial]
  | a, [] => simp [add_polynomial_zero_right_0, add_polynomial]
  | xa' :: a', xb' :: b' => simp [add_polynomial]

theorem cons_respects_trim {k : Type} [BEq k] [LawfulBEq k] (k_zero : k) (x : k)
  : respect_trim k_zero (List.cons x)
  := by
  intro a
  simp [trim_polynomial_list]
  rw [append_respects_trim_internal]

theorem trim_zero_all
  {k : Type} [BEq k] [LawfulBEq k] (zero : k) (a : List k) (ha : a.all (fun x ↦ (x == zero)))
  : trim_polynomial_list zero a = []
  := by
  match a with
  | [] => exact trim_zero_glue_nil zero
  | xa :: a' =>
    rw [cons_respects_trim]
    have ha' : a'.all (fun x ↦ (x == zero)) := by
      rw [List.all_cons] at ha
      simp_all
      apply ha.right
    conv =>
      arg 1
      arg 2
      rw [trim_zero_all zero a' ha']
    have hxa : xa == zero := by
      rw [List.all_cons] at ha
      simp_all
    rw [eq_of_beq hxa]
    rw [trim_zero_glue_singleton]

theorem trim_internal_helper_not_all_zero {k : Type} [BEq k] [LawfulBEq k] (k_zero : k) (x : k) (a : List k)
  (ha : ¬a.all (fun x ↦ x == k_zero))
  : trim_leading_zeros_internal k_zero (a ++ [x]) = trim_leading_zeros_internal k_zero a ++ [x] := by
  simp at ha
  match a with
  | [] =>
    simp_all
  | xa :: a' =>
    conv =>
      lhs
      rw [List.cons_append]
      rw [trim_leading_zeros_internal]
    if xa = k_zero then
      simp_all [trim_internal_helper_not_all_zero]
    else
      simp_all [trim_leading_zeros_internal]

theorem trim_internal_helper_all_zero {k : Type} [BEq k] [LawfulBEq k] (k_zero : k) (x : k) (a : List k)
  (ha : a.all (fun x ↦ x == k_zero))
  : trim_leading_zeros_internal k_zero (a ++ [x]) = trim_leading_zeros_internal k_zero [x] := by
  rw [trim_leading_zeros_internal]
  rw [trim_leading_zeros_internal]
  if h : x == k_zero then
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
      have q2_is_zero : q2 == k_zero := by
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
      have q2_is_zero : q2 == k_zero := by
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

theorem trim_helper_all_zero {k : Type} [BEq k] [LawfulBEq k] (k_zero : k) (x : k) (a : List k)
  (ha : a.all (fun x ↦ x == k_zero))
  : trim_polynomial_list k_zero (x :: a) = trim_polynomial_list k_zero [x] := by
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


theorem not_all_zero_if_trim_is_not_nil {k : Type} [BEq k] [LawfulBEq k] (k_zero : k) (a : List k)
  (h : ¬ trim_polynomial_list k_zero a = []) : (¬ a.all (fun x ↦ x == k_zero)) := by
  false_or_by_contra
  apply h
  apply trim_zero_all
  assumption

theorem trim_helper_not_all_zero {k : Type} [BEq k] [LawfulBEq k] (k_zero : k) (x : k) (a : List k)
  (ha : ¬ a.all (fun x ↦ x == k_zero))
  : trim_polynomial_list k_zero (x :: a) = x :: trim_polynomial_list k_zero a := by
  rw [trim_polynomial_list]
  rw [List.reverse_cons]
  rw [trim_internal_helper_not_all_zero]
  rw [List.reverse_append]
  rw [List.reverse_singleton]
  rw [List.singleton_append]
  rw [← trim_polynomial_list]
  rw [List.all_reverse]
  assumption

theorem add_polynomial_of_all_zero {k : Type} [BEq k] [LawfulBEq k]
  (k_zero : k) (k_add : k →  k → k) (add_zero_left: ∀ x : k, k_add k_zero x = x)
  (a : List k) (b: List k) (ha : a.all (fun x ↦ (x == k_zero))) (hb : b.all (fun x ↦ (x == k_zero)))
  : (add_polynomial k_add a b).all (fun x ↦ (x == k_zero))
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

theorem add_polynomial_of_all_zero' {k : Type} [BEq k] [LawfulBEq k]
  (k_zero : k) (k_add : k →  k → k) (add_zero_left: ∀ x : k, k_add k_zero x = x)
  (a : List k) (b: List k) (ha : a.all (fun x ↦ (x == k_zero))) (hb : b.all (fun x ↦ (x == k_zero)))
  : trim_polynomial_list k_zero (add_polynomial k_add a b) = []
  := by
  rw [trim_zero_all]
  apply add_polynomial_of_all_zero
  repeat assumption

theorem add_polynomial_all_zero_left {k : Type} [BEq k] [LawfulBEq k]
  (k_zero : k) (k_add : k →  k → k) (add_zero_left: ∀ x : k, k_add k_zero x = x)
  (a : List k) (b: List k) (ha : a.all (fun x ↦ (x == k_zero)))
  : trim_polynomial_list k_zero (add_polynomial k_add a b) = trim_polynomial_list k_zero b := by
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

theorem add_polynomial_all_zero_right {k : Type} [BEq k] [LawfulBEq k]
  (k_zero : k) (k_add : k →  k → k) (add_zero_right: ∀ x : k, k_add x k_zero = x)
  (a : List k) (b: List k) (hb : b.all (fun x ↦ (x == k_zero)))
  : trim_polynomial_list k_zero (add_polynomial k_add a b) = trim_polynomial_list k_zero a := by
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

theorem polynomial_shift_1_respect_trim {k : Type} [BEq k] [LawfulBEq k](k_zero : k)  (a : List k)
  : trim_polynomial_list k_zero ( polynomial_shift_1 k_zero a)
  = trim_polynomial_list k_zero ( polynomial_shift_1 k_zero (trim_polynomial_list k_zero a))
  := by
  rw [polynomial_shift_1, polynomial_shift_1]
  rw [cons_respects_trim]

theorem add_polynomial_respect_trim {k : Type} [BEq k] [LawfulBEq k]
  (k_zero : k) (k_add : k →  k → k)
  (add_zero_left: ∀ x : k, k_add k_zero x = x)
  (add_zero_right: ∀ x : k, k_add x k_zero = x)
  (a : List k) (b : List k)
  : trim_polynomial_list k_zero (add_polynomial k_add a b)
  = trim_polynomial_list k_zero (add_polynomial k_add (trim_polynomial_list k_zero a) (trim_polynomial_list k_zero b))
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
    if hxa : xa == k_zero then
      if xb == k_zero then
        simp_all[trim_polynomial_list, trim_leading_zeros_internal]
      else
        simp_all[trim_polynomial_list, trim_leading_zeros_internal, add_polynomial_zero_left_0]
    else
      if hxb : xb == k_zero then
        simp_all[trim_polynomial_list, trim_leading_zeros_internal, add_polynomial_zero_right_0]
      else
        simp_all[trim_polynomial_list, trim_leading_zeros_internal, add_polynomial]
  | xa :: a', xb :: b' =>
    if ha : a'.all (fun x ↦ x == k_zero) then
      rw [trim_helper_all_zero k_zero xa a' ha]
      if hb : b'.all (fun x ↦ x == k_zero) then
        rw [trim_helper_all_zero k_zero xb b' hb]
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
          rw [add_zero_left]
          apply eq_of_beq hxb
          repeat assumption
        · case isTrue.isFalse hxa hxb =>
          rw [add_polynomial_zero_left_0]
          rw [add_polynomial]
          rw [cons_respects_trim]
          rw [add_polynomial_of_all_zero']
          simp_all
          repeat assumption
        split
        · case isFalse.isTrue hxa hxb =>
          rw [add_polynomial_zero_right_0]
          rw [add_polynomial]
          rw [cons_respects_trim]
          rw [add_polynomial_of_all_zero']
          simp_all
          repeat assumption
        · case isFalse.isFalse hxa hxb =>
          rw [add_polynomial]
          rw [add_polynomial]
          rw [add_polynomial_zero_left_0]
          rw [cons_respects_trim]
          rw [add_polynomial_of_all_zero']
          repeat assumption
      else
        rw [trim_helper_not_all_zero k_zero xb b' hb]
        rw [add_polynomial]

        conv =>
          lhs
          rw [cons_respects_trim]
          rw [add_polynomial_all_zero_left ]
          rfl
          apply add_zero_left
          apply ha

        repeat rw [←cons_respects_trim]

        if hxa : xa == k_zero then
          rw [eq_of_beq hxa, add_zero_left, trim_zero_glue_singleton, add_polynomial_zero_left_0]
          rw [cons_respects_trim]
        else
          rw [trim_non_zero_singleton]
          rw [add_polynomial, add_polynomial_zero_left_0, cons_respects_trim]
          assumption
    else
      if hb : b'.all (fun x ↦ x == k_zero) then
        conv =>
          rhs
          arg 2
          arg 3
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
          apply add_zero_left
          apply add_zero_right
        rw[cons_respects_trim]
        assumption
        assumption
  termination_by a.length + b.length


theorem add_polynomial_respects_trim_second_arg {k : Type} [BEq k] [LawfulBEq k]
  (k_zero : k) (k_add : k →  k → k) (a : List k )
  (add_zero_left: ∀ x : k, k_add k_zero x = x)
  (add_zero_right: ∀ x : k, k_add x k_zero = x)
  : respect_trim k_zero (add_polynomial k_add a)
  := by
  intro b
  rw [add_polynomial_respect_trim]
  conv =>
    rhs
    rw [add_polynomial_respect_trim]
    rfl
    apply add_zero_left
    apply add_zero_right
  rw [trim_polynomial_list_idempotent]
  repeat assumption

@[simp]
theorem mul_polynomial'_zero_left
  {k : Type} (k_zero : k) (k_mul : k → k → k) (k_add : k →  k → k)
  (a : List k)
  :
  mul_polynomial' k_zero k_mul k_add [] a = []
  := by
  rw [mul_polynomial']

@[simp]
theorem mul_polynomial'_zero_right
  {k : Type}  [BEq k] [LawfulBEq k] (k_zero : k) (k_mul : k → k → k) (k_add : k →  k → k)
  (a : List k)
  :
  trim_polynomial_list k_zero (mul_polynomial' k_zero k_mul k_add a []) = []
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
  {k : Type}  [BEq k] [LawfulBEq k] (k_zero : k) (k_mul : k → k → k)
  (a : k)
  :
  trim_polynomial_list k_zero (polynomial_right_scalar_action k_mul [] a) = []
  := by
  simp[polynomial_right_scalar_action]

@[simp]
theorem mul_zero_scalar_left
  {k : Type}  [BEq k] [LawfulBEq k] (k_zero : k) (k_mul : k → k → k)
  (a : k)
  :
  trim_polynomial_list k_zero (polynomial_left_scalar_action k_mul a []) = []
  := by
  simp[polynomial_left_scalar_action]

theorem polynomial_scalar_action
  {k : Type} [BEq k] [LawfulBEq k] (k_zero : k) (k_mul : k → k → k) (k_add : k →  k → k)
  (add_zero_right: ∀ x : k, k_add x k_zero = x)
  (a : List k) (s : k)
  :
  trim_polynomial_list k_zero (mul_polynomial' k_zero k_mul k_add [s] a)
  =
  trim_polynomial_list k_zero (polynomial_left_scalar_action k_mul s a)
  := by
  rw [mul_polynomial']
  rw [mul_polynomial'_zero_left]
  rw [polynomial_shift_1]
  rw [add_polynomial_zero_right_1]
  apply add_zero_right


theorem polynomial_scalar_action'
  {k : Type} [BEq k] [LawfulBEq k] (k_zero : k) (k_mul : k → k → k) (k_add : k →  k → k)
  (add_zero_right: ∀ x : k, k_add x k_zero = x)
  (add_zero_left: ∀ x : k, k_add k_zero x = x)
  (a : List k) (s : k)
  :
  trim_polynomial_list k_zero (mul_polynomial' k_zero k_mul k_add a [s])
  =
  trim_polynomial_list k_zero (polynomial_right_scalar_action k_mul a s)
  := by
  match a with
  | [] =>
    simp
  | xa :: a' =>
    rw [mul_polynomial']
    rw [polynomial_left_scalar_action]
    rw [add_polynomial_respect_trim]
    rw [polynomial_shift_1_respect_trim]
    rw [polynomial_scalar_action' k_zero]
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
  {k : Type} (k_zero : k) (a : k) (n : Nat)
  :=
  polynomial_shift k_zero [a] n

@[simp]
theorem left_identity_is_polynomial_left_identity
  {k : Type} [BEq k] [LawfulBEq k] (k_zero : k)
  (k_mul : k → k → k) (k_add : k →  k → k) (k_left_identity : k) (add_zero_right : ∀ x : k, k_add x k_zero = x)
  (h_identity : is_left_identity k_mul k_left_identity)
  (a : List k)
  :
  trim_polynomial_list k_zero (mul_polynomial' k_zero k_mul k_add [k_left_identity] a)
  =
  trim_polynomial_list k_zero a
  := by
  rw [polynomial_scalar_action]
  rw [polynomial_left_identity_scalar_action]
  repeat assumption

@[simp]
theorem right_identity_is_polynomial_right_identity
  {k : Type} [BEq k] [LawfulBEq k] (k_zero : k)
  (k_mul : k → k → k) (k_add : k →  k → k) (k_right_identity : k)
  (add_zero_right : ∀ x : k, k_add x k_zero = x)
  (add_zero_left : ∀ x : k, k_add k_zero x = x)
  (h_right_identity : is_right_identity k_mul k_right_identity)
  (a : List k)
  :
  trim_polynomial_list k_zero (mul_polynomial' k_zero k_mul k_add a [k_right_identity])
  =
  trim_polynomial_list k_zero a
  := by
  rw [polynomial_scalar_action']
  rw [polynomial_right_identity_scalar_action]
  repeat assumption


theorem add_polynomial_scalar_left
  {k : Type} [BEq k] [LawfulBEq k]  (k_add : k →  k → k) (a : List k) (x : k) (y : k)
  : add_polynomial k_add [x] (y :: a) = (k_add x y) :: a := by
  rw [add_polynomial]
  rw [add_polynomial_zero_left_0]

theorem polynomial_left_scalar_action_cons_linear_right
  {k : Type}  [BEq k] [LawfulBEq k]  (k_zero : k) (k_mul : k → k → k) (k_add : k →  k → k)
  (add_zero_right : ∀ x : k, k_add x k_zero = x)
  (a : k) (x : k) (b : List k)  :
  trim_polynomial_list k_zero (polynomial_left_scalar_action k_mul a (x :: b))
  = trim_polynomial_list k_zero (add_polynomial k_add
      [k_mul a x]
      (polynomial_shift_1 k_zero (polynomial_left_scalar_action k_mul a b)))
  := by
  rw [polynomial_left_scalar_action, polynomial_shift_1]
  simp
  rw [add_polynomial_scalar_left]
  rw [add_zero_right]
  rw [polynomial_left_scalar_action]

theorem polynomial_right_scalar_action_cons_linear_left
  {k : Type}  [BEq k] [LawfulBEq k]  (k_zero : k) (k_mul : k → k → k) (k_add : k →  k → k)
  (add_zero_right : ∀ x : k, k_add x k_zero = x)
  (a : List k) (x : k) (b : k)  :
  trim_polynomial_list k_zero (polynomial_right_scalar_action k_mul (x :: a) b)
  = trim_polynomial_list k_zero (add_polynomial k_add
      [k_mul x b]
      (polynomial_shift_1 k_zero (polynomial_right_scalar_action k_mul a b)))
  := by
  rw [polynomial_right_scalar_action, polynomial_shift_1]
  simp
  rw [add_polynomial_scalar_left]
  rw [add_zero_right]
  rw [polynomial_right_scalar_action]

theorem polynomial_shift_1_respects_trim
  {k : Type} [BEq k] [LawfulBEq k] (k_zero : k) : respect_trim k_zero (polynomial_shift_1 k_zero) := by
  intro a
  rw [polynomial_shift_1, cons_respects_trim, ←polynomial_shift_1]

theorem polynomial_shift_1_respects_addition
  {k : Type} [BEq k] [LawfulBEq k] (k_zero : k) (k_add : k →  k → k) (add_zero_right : ∀ x : k, k_add x k_zero = x) (a : List k) (b : List k) :
  polynomial_shift_1 k_zero (add_polynomial k_add a b) = add_polynomial k_add (polynomial_shift_1 k_zero a) (polynomial_shift_1 k_zero b)
  := by
  rw [polynomial_shift_1, polynomial_shift_1, polynomial_shift_1]
  rw [add_polynomial]
  rw [add_zero_right]


theorem add_polynomial_associative
  {k : Type} [BEq k] [LawfulBEq k] (k_add : k →  k → k) (k_add_assoc : is_associative k_add)
  (a : List k) (b : List k) (c : List k):
  add_polynomial k_add a (add_polynomial k_add b c) = add_polynomial k_add (add_polynomial k_add a b) c := by
  match a, b, c with
  | [], b, c => simp [add_polynomial_zero_left_0]
  | a, [], c => simp [add_polynomial_zero_left_0, add_polynomial_zero_right_0]
  | a, b, [] => simp [add_polynomial_zero_right_0]
  | xa :: a', xb :: b', xc :: c' =>
    repeat rw [add_polynomial]
    rw [add_polynomial_associative]
    rw [k_add_assoc]
    apply k_add_assoc

theorem add_polynomial_associative'
  {k : Type} [BEq k] [LawfulBEq k] (k_zero : k) (k_add : k →  k → k) (k_add_assoc : is_associative k_add)
  (add_zero_left : ∀ x : k, k_add k_zero x = x)
  (add_zero_right : ∀ x : k, k_add x k_zero = x)
  (a : List k) (b : List k) (c : List k):
  trim_polynomial_list k_zero (
    add_polynomial k_add
      (trim_polynomial_list k_zero a)
      (trim_polynomial_list k_zero (add_polynomial k_add (trim_polynomial_list k_zero b) (trim_polynomial_list k_zero c)))
  )
  =
  trim_polynomial_list k_zero (
    add_polynomial k_add
      (trim_polynomial_list k_zero (add_polynomial k_add (trim_polynomial_list k_zero a) (trim_polynomial_list k_zero b)))
      (trim_polynomial_list k_zero c)
  ) := by
  conv =>
    rhs
    arg 2
    arg 2
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
    arg 2
    arg 3
    rw [add_polynomial_respect_trim]
    rfl
    repeat (tactic => assumption)

  repeat assumption

theorem add_polynomial_symmetric
  {k : Type} [BEq k] [LawfulBEq k] (k_add : k →  k → k) (k_add_symmetric : is_symmetric_2 k_add) (a : List k) (b : List k):
  (add_polynomial k_add a b) = (add_polynomial k_add b a) := by
  match a, b with
  | [], b =>
    simp[add_polynomial_zero_left_0, add_polynomial_zero_right_0]
  | a, [] =>
    simp[add_polynomial_zero_left_0, add_polynomial_zero_right_0]
  | xa :: a', xb :: b' =>
    rw [add_polynomial, add_polynomial, k_add_symmetric , add_polynomial_symmetric]
    repeat assumption


theorem mul_polynomial'_cons_linear_right
  {k : Type}
  [BEq k]
  [LawfulBEq k]
  (k_zero : k)
  (k_mul : k → k → k)
  (k_add : k →  k → k)
  (k_add_assoc : is_associative k_add)
  (k_add_symmetric : is_symmetric_2 k_add)
  (add_zero_left : ∀ x : k, k_add k_zero x = x)
  (add_zero_right : ∀ x : k, k_add x k_zero = x)
  (a : List k)
  (x : k)
  (b : List k)  :
  trim_polynomial_list k_zero (mul_polynomial' k_zero k_mul k_add a (x :: b))
  = trim_polynomial_list k_zero (add_polynomial k_add
      (polynomial_right_scalar_action k_mul a x)
      (polynomial_shift_1 k_zero (mul_polynomial' k_zero k_mul k_add a b)))
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
      arg 2
      rw [←add_polynomial_associative]
      arg 2
      rw [add_polynomial_symmetric]
      rfl
      apply k_add_symmetric
      apply k_add_assoc
    rw [←add_polynomial_associative]

    conv =>
      lhs
      rw [add_polynomial_respect_trim]
      arg 2
      arg 3
      arg 2
      rw [add_polynomial_associative]
      rfl
      repeat tactic => assumption


    conv =>
      lhs
      arg 2
      arg 3
      rw [add_polynomial_respect_trim]
      arg 2
      arg 2
      rw [add_polynomial_symmetric]
      rw [←polynomial_right_scalar_action_cons_linear_left]
      rfl
      repeat tactic => assumption

    conv =>
      lhs
      arg 2
      arg 3
      rw [add_polynomial_symmetric]
      rfl
      repeat tactic => assumption

    rw [← add_polynomial_respect_trim]
    conv =>
      lhs
      rw [add_polynomial_associative]
      rfl
      repeat tactic => assumption

    conv =>
      lhs
      rw [add_polynomial_respect_trim]
      arg 2
      arg 2
      rw [add_polynomial_respect_trim]
      rw [trim_polynomial_list_idempotent]
      rw [←add_polynomial_respect_trim]
      rw [add_polynomial_symmetric]
      rw [←polynomial_shift_1_respects_addition]
      rw [←mul_polynomial']
      rfl
      repeat tactic => assumption


    rw [←add_polynomial_respect_trim]
    rw [add_polynomial_symmetric]

    rw [add_polynomial_respect_trim]
    rw [trim_polynomial_list_idempotent]
    rw [←add_polynomial_respect_trim]

    repeat assumption

theorem left_and_right_scalar_actions_coincide
  {k : Type} [BEq k] [LawfulBEq k] (k_mul : k → k → k) (k_mul_comm : is_symmetric_2 k_mul)
  (a : List k) (s : k)
  : polynomial_left_scalar_action k_mul s a = polynomial_right_scalar_action k_mul a s
  := by
  rw [polynomial_left_scalar_action, polynomial_right_scalar_action]
  rw [List.map_eq_map_iff]
  intro element
  intro h_element
  apply k_mul_comm


theorem mul_polynomial'_symmetric
  {k : Type} [BEq k] [LawfulBEq k] (k_zero : k) (k_left_identity : k)
  (k_mul : k → k → k) (k_add : k →  k → k)
  (add_zero_left : ∀ x : k, k_add k_zero x = x)
  (add_zero_right : ∀ x : k, k_add x k_zero = x)
  (k_mul_comm : is_symmetric_2 k_mul)
  (k_mul_assoc : is_associative k_mul)
  (k_add_comm : is_symmetric_2 k_add)
  (k_add_assoc : is_associative k_add)
  (h_identity : is_left_identity k_mul k_left_identity)
  (a : List k) (b : List k)
  :
  trim_polynomial_list k_zero (mul_polynomial' k_zero k_mul k_add a b) = trim_polynomial_list k_zero (mul_polynomial' k_zero k_mul k_add b a)
  := by
  match a with
  | [] =>
    rw [mul_polynomial'_zero_left]
    rw [mul_polynomial'_zero_right]
    exact trim_zero_glue_nil k_zero
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
    assumption
    apply k_left_identity
    repeat assumption

def mul_nat_polynomial (a : List Nat) (b : List Nat) := mul_polynomial' (0: Nat) (Nat.mul) (Nat.add) a b

def add_polynomial_safe {k: Type} [BEq k] [LawfulBEq k] (k_zero : k) (k_add : k → k → k) (a : List k) (b : List k) :=
  trim_polynomial_list k_zero (add_polynomial k_add (trim_polynomial_list k_zero a) (trim_polynomial_list k_zero b))

def mul_polynomial_safe {k: Type} [BEq k] [LawfulBEq k] (k_zero : k)
  (k_mul : k → k → k) (k_add : k → k → k) (a : List k) (b : List k) :=
  trim_polynomial_list k_zero (mul_polynomial' k_zero k_mul k_add (trim_polynomial_list k_zero a) (trim_polynomial_list k_zero b))

theorem mul_polynomial_safe_is_symmetric
  {k : Type} [BEq k] [LawfulBEq k] (k_zero : k) (k_left_identity : k)
  (k_mul : k → k → k) (k_add : k →  k → k)
  (add_zero_left : ∀ x : k, k_add k_zero x = x)
  (add_zero_right : ∀ x : k, k_add x k_zero = x)
  (k_mul_comm : is_symmetric_2 k_mul)
  (k_mul_assoc : is_associative k_mul)
  (k_add_comm : is_symmetric_2 k_add)
  (k_add_assoc : is_associative k_add)
  (h_identity : is_left_identity k_mul k_left_identity)
  : is_symmetric_2 (mul_polynomial_safe k_zero k_mul k_add) := by
  intro a b
  rw[mul_polynomial_safe]
  rw[mul_polynomial'_symmetric k_zero k_left_identity k_mul k_add]
  rw[←mul_polynomial_safe]
  repeat assumption

theorem add_polynomial_safe_is_associative
  {k : Type} [BEq k] [LawfulBEq k] (k_zero : k) (k_add : k →  k → k) (k_add_assoc : is_associative k_add)
  (add_zero_left : ∀ x : k, k_add k_zero x = x)
  (add_zero_right : ∀ x : k, k_add x k_zero = x)
  (a : List k) (b : List k) (c : List k):
    add_polynomial_safe k_zero k_add a (add_polynomial_safe k_zero k_add b c) =
    add_polynomial_safe k_zero k_add (add_polynomial_safe k_zero k_add a b) c
  := by
  rw [add_polynomial_safe, add_polynomial_safe, add_polynomial_safe, add_polynomial_safe]
  rw [trim_polynomial_list_idempotent, trim_polynomial_list_idempotent]
  rw [add_polynomial_associative']
  repeat assumption

structure reduced_polynomial {k : Type} [BEq k] [LawfulBEq k] (zero : k)  where
  value : List k
  is_reduced : trim_polynomial_list zero value = value

theorem ext_both_directions {k : Type} [BEq k] [LawfulBEq k]  (zero : k) {p q : reduced_polynomial zero} : p = q ↔ p.value = q.value := by
  constructor
  · intro h; simp [h]
  · intro h; cases p; cases q; simp at h; simp [h]

@[ext]
theorem ext_direct {k : Type} [BEq k] [LawfulBEq k]  (zero : k) {p q : reduced_polynomial zero}
  (values_are_equal : p.value = q.value) :  p = q := by
  cases p;
  cases q;
  simp at values_are_equal
  simp [values_are_equal]






theorem add_polynomial_safe_is_reduced
  {k : Type}
  [BEq k] [LawfulBEq k]
  (k_zero : k) (k_add : k → k → k)
  (a : List k) (b : List k)
  : trim_polynomial_list k_zero (add_polynomial_safe k_zero k_add a b) = add_polynomial_safe k_zero k_add a b
  := by
  rw [add_polynomial_safe]
  rw [trim_polynomial_list_idempotent]

theorem mul_polynomial_safe_is_reduced
  {k: Type} [BEq k] [LawfulBEq k] (k_zero : k)
  (k_mul : k → k → k) (k_add : k → k → k)
  (a : List k) (b : List k)
  : trim_polynomial_list k_zero (mul_polynomial_safe k_zero k_mul k_add a b)
  = mul_polynomial_safe k_zero k_mul k_add a b
  := by
  rw [mul_polynomial_safe]
  rw [trim_polynomial_list_idempotent]

def add_reduced_polynomial
  {k : Type}
  [BEq k] [LawfulBEq k]
  (k_zero : k) (k_add : k → k → k)
  (a : reduced_polynomial k_zero) (b : reduced_polynomial k_zero)
  : reduced_polynomial k_zero
  := {
    value := add_polynomial_safe k_zero k_add a.value b.value
    is_reduced := by
      apply add_polynomial_safe_is_reduced k_zero k_add
  }

def mul_reduced_polynomial
  {k: Type} [BEq k] [LawfulBEq k] (k_zero : k)
  (k_mul : k → k → k) (k_add : k → k → k)
  (a : reduced_polynomial k_zero) (b : reduced_polynomial k_zero)
  : reduced_polynomial k_zero
  := {
    value := mul_polynomial_safe k_zero k_mul k_add a.value b.value
    is_reduced := by
      apply mul_polynomial_safe_is_reduced
  }

def add_inverse {R : ring} [BEq R.k] [LawfulBEq R.k] (a : reduced_polynomial R.zero) : List R.k :=
  a.value.map R.add_inverse

@[simp]
theorem no_leading_zero_after_trimming_leading_zero {k : Type} [BEq k] [LawfulBEq k]
  (zero : k) (a : List k) (b :List k) (c : k) (h : trim_leading_zeros_internal zero a = c :: b) :
  ¬ c = zero := by
  rw [trim_leading_zeros_internal.eq_def] at h
  split at h
  simp_all
  split at h
  apply no_leading_zero_after_trimming_leading_zero
  assumption
  simp_all

theorem reduced_iff_non_zero_tail {k : Type} [BEq k] [LawfulBEq k] (zero : k) (s : k) (a : List k)
  :  trim_polynomial_list zero (a ++ [s]) = (a ++ [s]) ↔ ¬ s = zero := by
  constructor
  intro h
  rw [trim_polynomial_list] at h
  simp_all
  rw [trim_leading_zeros_internal] at h
  false_or_by_contra
  simp_all
  have afsds := no_leading_zero_after_trimming_leading_zero zero a.reverse a.reverse zero h
  apply afsds
  rfl

  intro s_not_zero
  rw [trim_polynomial_list]
  simp
  rw [trim_leading_zeros_internal]
  simp_all

@[simp]
theorem reduced_tail_of_reduced_internal {R : ring} [BEq R.k] [LawfulBEq R.k]
  (x : R.k) (a : List R.k) (h : trim_leading_zeros_internal R.zero (a ++ [x]) = a ++ [x]) :
  trim_leading_zeros_internal R.zero a = a := by
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
        have dafe := no_leading_zero_after_trimming_leading_zero R.zero a'' (q ++ [x]) R.zero h
        contradiction
      case isFalse a'_is_not_zero =>
        rfl

theorem a_decomposition {k : Type} (a : List k) (x : k) : ∃ c, ∃ aq, x :: a = aq ++ [c] :=
    match a with
    | [] => ⟨ x, by simp ⟩
    | xa :: a' => by
      rcases a_decomposition a' xa with ⟨ tail, head, tail_is_okay ⟩
      rw [tail_is_okay]
      exists tail, (x :: head)


@[simp]
theorem reduced_of_reduced_tail {R : ring} [BEq R.k] [LawfulBEq R.k]
  (x : R.k) (x' : R.k) (a : List R.k) (h : trim_polynomial_list R.zero (x :: a) = (x :: a)) :
  trim_polynomial_list R.zero (x' :: (x :: a)) = (x' :: (x :: a)) := by
  have a_d := a_decomposition a x
  rcases a_d with ⟨ tail, head, valid_decomposition ⟩
  rw [valid_decomposition]
  repeat rw [←List.cons_append]
  rw [valid_decomposition] at h
  have non_zero_tail := (reduced_iff_non_zero_tail R.zero tail head).mp h
  apply (reduced_iff_non_zero_tail R.zero tail (x' :: head)).mpr
  apply non_zero_tail

theorem reduced_tail_of_reduced {R : ring} [BEq R.k] [LawfulBEq R.k]
  (x : R.k) (a : List R.k) (h : trim_polynomial_list R.zero (x :: a) = x :: a) :
  trim_polynomial_list R.zero a = a := by
  rw [trim_polynomial_list] at *
  simp_all
  rw [reduced_tail_of_reduced_internal]
  apply List.reverse_reverse
  apply x
  apply h

theorem add_inverse_is_reduced (R : ring) [BEq R.k] [LawfulBEq R.k]
  (a : List R.k)
  (is_reduced : trim_polynomial_list R.zero a = a)
  :
  trim_polynomial_list R.zero (a.map R.add_inverse) =(a.map R.add_inverse) := by
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
    have a'_inversed_is_reduced := add_inverse_is_reduced R a' a'_is_reduced
    rw [List.map_cons, List.map_cons]
    apply reduced_of_reduced_tail
    rw [←List.map_cons]
    apply add_inverse_is_reduced
    apply reduced_tail_of_reduced xa
    apply is_reduced

theorem inverse_is_left_inverse (R : ring) [BEq R.k] [LawfulBEq R.k] (a : List R.k) :
  trim_polynomial_list R.zero (add_polynomial R.add (a.map R.add_inverse) a) = [] :=
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

theorem polynomial_left_scalar_action_left_linear (R : ring) [BEq R.k] [LawfulBEq R.k] (x y : R.k) (a : List R.k) :
  (polynomial_left_scalar_action R.mul (R.add x y) a)
  =
  (add_polynomial R.add (polynomial_left_scalar_action R.mul x a) (polynomial_left_scalar_action R.mul y a))
  := by
  repeat rw [polynomial_left_scalar_action]
  match a with
  | [] => simp
  | xa :: a' =>
    simp
    rw [add_polynomial]
    rw [R.mul_is_linear x y xa]
    apply (List.cons_inj_right _).mpr
    rw [←polynomial_left_scalar_action]
    rw [polynomial_left_scalar_action_left_linear]
    rw [polynomial_left_scalar_action, polynomial_left_scalar_action]

theorem polynomial_left_scalar_action_right_linear (R : ring) [BEq R.k] [LawfulBEq R.k] (x : R.k) (a b : List R.k) :
  (polynomial_left_scalar_action R.mul x (add_polynomial R.add a b) )
  =
  (add_polynomial R.add (polynomial_left_scalar_action R.mul x a) (polynomial_left_scalar_action R.mul x b))
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
    rw [R.mul_is_linear]
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

theorem mul_polynomial_is_left_linear (R : ring) [BEq R.k] [LawfulBEq R.k] (a : List R.k) (b : List R.k) (c : List R.k) :
  trim_polynomial_list R.zero (mul_polynomial' R.zero R.mul R.add  ( add_polynomial R.add a b ) c)
  =
  trim_polynomial_list R.zero (add_polynomial R.add ( mul_polynomial' R.zero R.mul R.add  a c ) ( mul_polynomial' R.zero R.mul R.add b c ) )
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
      arg 2
      arg 2
      arg 2
      rw [←add_polynomial_associative]
      arg 3
      rw [add_polynomial_symmetric]
      repeat tactic => assumption
      rfl
      repeat tactic => assumption
      apply R.add_is_comm
      apply R.add_is_assoc

    rw [add_polynomial_associative]
    apply R.add_is_assoc
    apply R.add_is_assoc
    apply R.zero_is_right_identity
    apply R.add_is_assoc
    apply R.zero_is_left_identity
    apply R.zero_is_right_identity
    apply R.zero_is_left_identity
    apply R.zero_is_right_identity


def trim_polynomial_list' {k : Type} [BEq k] [LawfulBEq k] (zero : k) (a : List k) : List k :=
  match a with
  | [] => []
  | x :: a' =>
    match trim_polynomial_list zero a' with
    | [] => trim_polynomial_list zero [x]
    | a_trimmed => x :: a_trimmed

@[simp]
theorem trim_definitions_are_equivalent {k : Type} [BEq k] [LawfulBEq k] (zero : k) (a : List k)
  : trim_polynomial_list' zero a = trim_polynomial_list zero a
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


theorem trim_is_nil_if_all_zero {k : Type} [BEq k] [LawfulBEq k] (k_zero : k) (a : List k)
  (ha : a.all (fun x ↦ x == k_zero))
  : trim_polynomial_list k_zero a = [] := by
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
      have qq := trim_is_nil_if_all_zero k_zero a' ha.right
      contradiction

theorem all_zero_if_trim_is_nil {k : Type} [BEq k] [LawfulBEq k] (k_zero : k) (a : List k)
  (ha : trim_polynomial_list k_zero a = [])
  : a.all (fun x ↦ x == k_zero) := by
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


theorem polynomial_left_scalar_action_respects_trim  (R : ring) [BEq R.k] [LawfulBEq R.k] (x : R.k) (a : List R.k)
  :
  trim_polynomial_list R.zero (polynomial_left_scalar_action R.mul x ( trim_polynomial_list R.zero a))
  =
  trim_polynomial_list R.zero (polynomial_left_scalar_action R.mul x a)
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
      have ha' := all_zero_if_trim_is_nil R.zero a' q2
      rw [←polynomial_left_scalar_action]
      rw [←polynomial_left_scalar_action]
      conv =>
        rhs
        rw [←polynomial_left_scalar_action_respects_trim]
      rw [q2]
      simp_all [trim_singleton, polynomial_left_scalar_action]
      rw [apply_ite (List.map (R.mul x))]
      rw [apply_ite (trim_polynomial_list R.zero)]
      simp_all
      if xa = R.zero then
        simp_all
        rw [R.mul_is_comm]
        apply mul_zero_any_is_zero R
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


theorem mul_polynomial_respects_trim_1  (R : ring) [BEq R.k] [LawfulBEq R.k] (a : List R.k) (b : List R.k)
  :
  trim_polynomial_list R.zero
    (mul_polynomial' R.zero R.mul R.add (trim_polynomial_list R.zero a) b)
  =
  trim_polynomial_list R.zero
    (mul_polynomial' R.zero R.mul R.add a b)
  := by
  match a with
  | [] => simp
  | xa :: a' =>
    conv =>
      lhs
      arg 2
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
        apply R.zero_is_left_identity
        apply R.zero_is_right_identity
      rw [q2]
      simp_all [polynomial_shift_1]
      rw [trim_singleton]
      split
      rw [polynomial_left_scalar_action]
      simp_all
      apply trim_zero_all
      simp_all
      intro x hx
      apply mul_zero_any_is_zero
      case isFalse w1 w2 =>
        rw [mul_polynomial']
        simp_all [polynomial_shift_1, polynomial_left_scalar_action]
        rw [add_polynomial_all_zero_right]
        apply R.zero_is_right_identity
        simp
    case h_2 q1 q2 =>
      rw [mul_polynomial']
      rw [add_polynomial_respect_trim]
      rw [polynomial_shift_1_respect_trim]
      rw [mul_polynomial_respects_trim_1]
      rw [←polynomial_shift_1_respect_trim]
      rw [←add_polynomial_respect_trim]
      rw [←mul_polynomial']
      apply R.zero_is_left_identity
      apply R.zero_is_right_identity
      apply R.zero_is_left_identity
      apply R.zero_is_right_identity



theorem mul_polynomial_respects_trim  (R : ring) [BEq R.k] [LawfulBEq R.k] (a : List R.k) (b : List R.k)
  :
  trim_polynomial_list R.zero
    (mul_polynomial' R.zero R.mul R.add (trim_polynomial_list R.zero a) (trim_polynomial_list R.zero b))
  =
  trim_polynomial_list R.zero
    (mul_polynomial' R.zero R.mul R.add a b)
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
    apply R.zero_is_left_identity
    apply R.zero_is_right_identity
    apply R.zero_is_left_identity
    apply R.zero_is_right_identity

theorem left_scalar_action_is_associative (R : ring) [BEq R.k] [LawfulBEq R.k]
  (a : R.k) (b : List R.k) (c : List R.k) :
  trim_polynomial_list R.zero (mul_polynomial' R.zero R.mul R.add (polynomial_left_scalar_action R.mul a b) c)
  =
  trim_polynomial_list R.zero (polynomial_left_scalar_action R.mul a (mul_polynomial' R.zero R.mul R.add b c))
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

    have h_mul_comp (a b: R.k) : R.mul a ∘ R.mul b = R.mul (R.mul a b) := by
      ext
      simp
      rw [R.mul_is_assoc]
    rw [h_mul_comp]

    rw [polynomial_left_scalar_action]
    rw [List.map_cons]

    conv =>
      rhs
      arg 2
      arg 3
      rw [R.mul_is_comm]
      rw [mul_zero_any_is_zero]
    apply R.zero_is_left_identity
    apply R.zero_is_right_identity
    apply R.zero_is_left_identity
    apply R.zero_is_right_identity


theorem left_scalar_action_zero (R : ring) [BEq R.k] [LawfulBEq R.k] (a : List R.k) :
  trim_polynomial_list R.zero (polynomial_left_scalar_action R.mul R.zero a) = []
  := by
  apply trim_is_nil_if_all_zero
  rw [polynomial_left_scalar_action]
  simp
  intro x hx
  rw [mul_zero_any_is_zero]


theorem mul_polynomial_is_associative (R : ring) [BEq R.k] [LawfulBEq R.k]
  (a : List R.k) (b : List R.k) (c : List R.k) :
  trim_polynomial_list R.zero (mul_polynomial' R.zero R.mul R.add (mul_polynomial' R.zero R.mul R.add a b) c)
  =
  trim_polynomial_list R.zero (mul_polynomial' R.zero R.mul R.add a (mul_polynomial' R.zero R.mul R.add b c))
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
      arg 2
      arg 3
      rw [add_polynomial_respect_trim]
      rw [polynomial_shift_1_respect_trim]
      rfl
      apply R.zero_is_left_identity
      apply R.zero_is_right_identity
    rw [mul_polynomial_is_associative]
    repeat rw [polynomial_shift_1]
    rw [← cons_respects_trim]
    conv =>
      lhs
      arg 2
      arg 3
      rw [← add_polynomial_respect_trim]
      rfl
      apply R.zero_is_left_identity
      apply R.zero_is_right_identity
    rw [left_scalar_action_is_associative]
    conv =>
      rhs
      rw [add_polynomial_respect_trim]
      rfl
      apply R.zero_is_left_identity
      apply R.zero_is_right_identity
    congr  2
    rw [add_polynomial_respect_trim]
    rw [left_scalar_action_zero]
    rw [add_polynomial_zero_left_0]
    rw [trim_polynomial_list_idempotent]
    apply R.zero_is_left_identity
    apply R.zero_is_right_identity
    apply R.zero_is_left_identity
    apply R.zero_is_right_identity



@[reducible]
def polynomial_ring (R : ring) [BEq R.k] [LawfulBEq R.k] : ring :=
  {
    k := (reduced_polynomial R.zero)
    add := add_reduced_polynomial R.zero R.add
    zero := {
      value := []
      is_reduced := by
        apply trim_zero_glue_nil
    }
    add_inverse (a : reduced_polynomial R.zero) := {
      value := a.value.map R.add_inverse
      is_reduced := by
        apply add_inverse_is_reduced R a.value
        apply a.is_reduced
    }
    mul := mul_reduced_polynomial R.zero R.mul R.add
    e := {
      value := [R.e]
      is_reduced := by
        simp [R.non_trivial]
    }
    non_trivial := by
      simp
    add_inverse_is_inverse := by
      rw [is_left_inverse]
      intro a
      rw [add_reduced_polynomial]
      simp [add_polynomial_safe]
      rw [←add_polynomial_respect_trim]
      apply inverse_is_left_inverse
      apply R.zero_is_left_identity
      apply R.zero_is_right_identity
    add_is_comm := by
      rw [is_symmetric_2]
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
      rw [mul_polynomial_safe_is_symmetric R.zero R.e]
      apply R.zero_is_left_identity
      intro x
      rw [R.add_is_comm]
      apply R.zero_is_left_identity
      apply R.mul_is_comm
      apply R.mul_is_assoc
      apply R.add_is_comm
      apply R.add_is_assoc
      apply R.e_is_left_identity
    e_is_left_identity := by
      intro a
      rw [mul_reduced_polynomial]
      apply ext_direct
      simp
      rw [mul_polynomial_safe]
      rw [trim_singleton]
      simp [R.non_trivial, a.is_reduced]
      rw [left_identity_is_polynomial_left_identity]
      apply a.is_reduced
      intro x
      apply R.zero_is_right_identity x
      apply R.e_is_left_identity
    zero_is_left_identity := by
      intro a
      simp [add_reduced_polynomial, add_polynomial_safe, trim_zero_glue_nil]
      apply ext_direct
      simp
      rw [a.is_reduced]
    mul_is_linear := by
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
      apply R.zero_is_left_identity
      apply R.zero_is_right_identity
      apply R.zero_is_left_identity
      apply R.zero_is_right_identity
      apply R.zero_is_left_identity
      apply R.zero_is_right_identity
    add_is_assoc := by
      rw [is_associative]
      intro a b c
      repeat rw [add_reduced_polynomial]
      simp
      rw [add_polynomial_safe_is_associative R.zero  R.add R.add_is_assoc]
      apply R.zero_is_left_identity
      intro x
      rw [R.add_is_comm]
      apply R.zero_is_left_identity
    mul_is_assoc := by
      rw [is_associative]
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
    e_is_right_identity := by
      intro a
      rw [mul_reduced_polynomial]
      apply ext_direct
      simp
      rw [mul_polynomial_safe]
      rw [trim_singleton]
      simp [R.non_trivial, a.is_reduced]
      rw [right_identity_is_polynomial_right_identity]
      apply a.is_reduced
      intro x
      apply R.zero_is_right_identity x
      apply R.zero_is_left_identity
      apply R.e_is_right_identity
    zero_is_right_identity := by
      intro a
      simp [add_reduced_polynomial, add_polynomial_safe, a.is_reduced]
  }


#eval mul_nat_polynomial [1, 2, 1, 0] [1, 2, 1]
