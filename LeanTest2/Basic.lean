def hello := "world"

def is_symmetric_2 {k : Type} (m : k → k → k) :=
  ∀ a, ∀ b, m a b = m b a

def is_left_identity {k : Type} (m : k → k → k) (e : k) :=
  ∀ a, m e a = a

def is_right_identity {k : Type} (m : k → k → k) (e : k) :=
  ∀ a, m a e = a

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

def is_left_linear {k : Type} (add : k → k → k) (mul: k → k → k) :=
  ∀ a, ∀ b, ∀ c, mul a (add b c) = add (mul a b) (mul a c)

def is_right_linear {k : Type} (add : k → k → k) (mul: k → k → k) :=
  ∀ a, ∀ b, ∀ c, mul (add b c) a = add (mul b a) (mul c a)

def is_left_inverse {k : Type} (m : k → k → k) (e : k) (inv: k → k) :=
  ∀ a, m (inv a) a =e

class ring (k : Type) where
  add : k → k → k
  add_inverse : k → k
  mul : k → k → k
  e : k
  zero : k
  add_inverse_is_inverse : is_left_inverse add zero add_inverse
  add_is_comm : is_symmetric_2 add
  mul_is_comm : is_symmetric_2 mul
  e_is_identity : is_left_identity mul e
  zero_is_identity : is_left_identity add zero
  mul_is_linear : is_left_linear add mul

class field (k : Type) extends ring k where
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

theorem trim_polynomial_list_idempotent {k : Type} [BEq k] [LawfulBEq k] (zero : k) (a : List k) :
  trim_polynomial_list zero (trim_polynomial_list zero a) = trim_polynomial_list zero a
  := by
  simp [trim_polynomial_list, trim_leading_zeros_internal_idempotent]

theorem trim_zero_glue_generator_internal
  {k : Type} [BEq k] [LawfulBEq k] (zero : k)
  (a : List k) : trim_leading_zeros_internal zero (zero :: a) = trim_leading_zeros_internal zero  a
  := by
  rw [trim_leading_zeros_internal]
  simp

theorem trim_zero_glue_generator_internal'
  {k : Type} [BEq k] [LawfulBEq k] (zero : k) : trim_leading_zeros_internal zero ([zero]) = []
  := by
  repeat rw [trim_leading_zeros_internal]
  simp

theorem trim_zero_glue_generator
  {k : Type} [BEq k] [LawfulBEq k] (zero : k)
  (a : List k) : trim_polynomial_list zero (a ++ [zero]) = trim_polynomial_list zero a
  := by
  rw [trim_polynomial_list]
  rw [trim_polynomial_list]
  rw [List.reverse_concat]
  rw [trim_zero_glue_generator_internal]

theorem trim_zero_glue_generator'
  {k : Type} [BEq k] [LawfulBEq k] (zero : k) : trim_polynomial_list zero ([zero]) = []
  := by
  rw [trim_polynomial_list]
  rw [List.reverse_singleton]
  rw [trim_zero_glue_generator_internal']
  rw [List.reverse_nil]

theorem trim_zero_glue_nil
  {k : Type} [BEq k] [LawfulBEq k] (zero : k) : trim_polynomial_list zero ([]) = []
  := by
  rw [trim_polynomial_list]
  rw [List.reverse_nil]
  rw [trim_leading_zeros_internal]
  rw [List.reverse_nil]

theorem trim_zero_glue_singleton
  {k : Type} [BEq k] [LawfulBEq k] (zero : k) : trim_polynomial_list zero ([zero]) = []
  := by
  simp [trim_polynomial_list, trim_leading_zeros_internal]

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
  {k : Type} (k_zero : k) (k_mul : k → k → k) (mul_comm : is_symmetric_2 k_mul)
  (a : List k) (b : List k) (i : Nat) (j : Nat)
  :
  mul_polynomial_list_at_degree_internal_summand k_zero k_mul a b i j
  =
  mul_polynomial_list_at_degree_internal_summand k_zero k_mul b a j i
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
  {k : Type} [BEq k]  [LawfulBEq k] (k_zero : k) (k_mul : k → k → k) (k_add : k →  k → k)
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
  {k : Type} [BEq k]  [LawfulBEq k] (k_zero : k) (k_mul : k → k → k) (k_add : k →  k → k)
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
  {k : Type} [BEq k]  [LawfulBEq k] (k_zero : k) (k_mul : k → k → k) (k_add : k →  k → k)
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
  {k : Type} [BEq k]  [LawfulBEq k] (k_zero : k) (k_mul : k → k → k) (k_add : k →  k → k)
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
  {k : Type} [BEq k] [LawfulBEq k] (k_zero : k) (k_mul : k → k → k) (k_add : k →  k → k)
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
  {k : Type} [BEq k] [LawfulBEq k] (k_zero : k) (k_mul : k → k → k) (k_add : k →  k → k)
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

theorem polynomial_left_identity_scalar_action
  {k : Type} (k_mul : k → k → k)
  (a : List k)  (k_left_identity : k) (h_identity : is_left_identity k_mul k_left_identity)
  : polynomial_left_scalar_action k_mul k_left_identity a = a
  := by
  rw [polynomial_left_scalar_action]
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
  {k : Type} [BEq k] [LawfulBEq k] (zero : k) (a : List k) (ha : a.all (fun x ↦ (x == zero))) : trim_polynomial_list zero a = []
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
      rw [trim_zero_glue_generator_internal]
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
  | [], [] => simp[add_polynomial_zero_left_0]
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
        simp_all[trim_polynomial_list, trim_leading_zeros_internal, add_polynomial_zero_left_0]
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

theorem mul_polynomial'_zero_left
  {k : Type} (k_zero : k) (k_mul : k → k → k) (k_add : k →  k → k)
  (a : List k)
  :
  mul_polynomial' k_zero k_mul k_add [] a = []
  := by
  rw [mul_polynomial']

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



def monomial
  {k : Type} (k_zero : k) (a : k) (n : Nat)
  :=
  polynomial_shift k_zero [a] n

theorem left_identity_is_polynomial_left_identity
  {k : Type} [BEq k] [LawfulBEq k] (k_zero : k)
  (k_mul : k → k → k) (k_add : k →  k → k) (k_left_identity : k) (add_zero_right : ∀ x : k, k_add x k_zero = x)
  (h_identity : is_left_identity k_mul k_left_identity)
  (a : List k)
  :
  trim_polynomial_list k_zero a
  =
  trim_polynomial_list k_zero (mul_polynomial' k_zero k_mul k_add [k_left_identity] a)
  := by
  rw [polynomial_scalar_action]
  rw [polynomial_left_identity_scalar_action]
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
  add_polynomial k_add a b = add_polynomial k_add b a := by
  match a, b with
  | [], b => simp[add_polynomial_zero_left_0, add_polynomial_zero_right_0]
  | a, [] => simp[add_polynomial_zero_left_0, add_polynomial_zero_right_0]
  | xa :: a', xb :: b' =>
    rw [add_polynomial, add_polynomial, k_add_symmetric, add_polynomial_symmetric]
    repeat assumption


def mul_polynomial'_cons_linear_right
  {k : Type} [BEq k] [LawfulBEq k]  (k_zero : k) (k_mul : k → k → k) (k_add : k →  k → k)
  (k_add_assoc : is_associative k_add) (k_add_symmetric : is_symmetric_2 k_add)
  (add_zero_left : ∀ x : k, k_add k_zero x = x)
  (add_zero_right : ∀ x : k, k_add x k_zero = x)
  (a : List k) (x : k) (b : List k)  :
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
    rw [add_polynomial_zero_left_0 ]
    rw [mul_polynomial'_zero_left]
    rw [polynomial_shift_1]
    rw [trim_zero_glue_singleton]
    rw [trim_zero_glue_nil]
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

#eval mul_nat_polynomial [1, 2, 1, 0] []
