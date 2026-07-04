import LeanTest2.Algebra
import LeanTest2.Trim

namespace polynomial_ring

universe u v w

open algebra

def get_coeff_array  {k : Type u} (zero : k) (p : Array k) (i : Nat) : k :=
  if h : i < p.size then p[i] else zero

def get_coeff_list  {k : Type u} [choose_zero k] (p : List k) (i : Nat) : k :=
  match p[i]? with
  | none => algebra.choose_zero.zero
  | some x => x

theorem zero_array_has_zero_coeffs
  {k : Type u} [BEq k] [LawfulBEq k] (zero : k)
  (p : Array k) (h: p.all (fun x ↦ x == zero))
  (i : Nat) :
  get_coeff_array zero p i = zero := by
  rw [get_coeff_array]
  split
  have h' := LawfulBEq.eq_of_beq (Array.all_eq_true.mp h i (by assumption))
  apply h'; rfl

theorem zero_list_has_zero_coeffs
  {k : Type u} [BEq k] [LawfulBEq k] [choose_zero k]
  (p : List k) (h: ∀ x ∈ p, x = choose_zero.zero)
  (i : Nat) :
  (get_coeff_list p i) = choose_zero.zero := by
  rw [get_coeff_list]
  split
  · case h_1 x hx =>
    rfl
  · case h_2 x x' hx =>
    have q : x' ∈ p := by
      exact List.mem_of_getElem? hx
    apply h x' q

def add_poly
  {k : Type u} [A : add k]
  (a : List k) (b : List k) : List k
  :=
  match a, b with
  | [], [] => []
  | [], b' => b'
  | a', [] => a'
  | xa :: a', xb :: b' => A.add xa xb :: (add_poly a' b')

infix:90 "+₀" => add_poly

@[simp]
theorem add_poly.nil_any
  {k : Type u} [A : add k] [BEq k] [LawfulBEq k]
  (a : List k)
  :
  add_poly [] a = a
  := by
  match a with
  | [] => rw [add_poly]
  | xa :: a'=>
    rw [add_poly]
    apply List.cons_ne_nil

@[simp]
theorem add_poly.any_nil
  {k : Type u} [A : add k] [BEq k] [LawfulBEq k]
  (a : List k)
  :
  add_poly a [] = a
  := by
  match a with
  | [] => rw [add_poly]
  | xa :: a'=>
    rw [add_poly]
    apply List.cons_ne_nil

@[simp]
theorem add_poly.zero_any
  {k : Type u} [BEq k] [LawfulBEq k] [Z : choose_zero k] [A : add k]
  (add_zero_left : ∀ x : k, A.add Z.zero x = x)
  (a : List k)
  :
  trim_utilities.tail (· == Z.zero) (add_poly [Z.zero] a) = trim_utilities.tail (· == Z.zero) a
  := by
  match a with
  | [] =>
    rw [add_poly, trim_utilities.tail.P_singleton (· == Z.zero) Z.zero _, trim_utilities.tail.nil]
    apply BEq.rfl
    apply List.cons_ne_nil
  | xa :: a'=>
    rw [add_poly, add_poly.nil_any, add_zero_left]

@[simp]
theorem add_poly.any_zero
  {k : Type u} [BEq k] [LawfulBEq k] [A : additive_monoid k]
  (a : List k)
  :
  trim_utilities.tail (· == A.zero)  (add_poly a [A.zero]) = trim_utilities.tail (· == A.zero)  a
  := by
  match a with
  | [] =>
    rw [add_poly, trim_utilities.tail.P_singleton (· == A.zero) A.zero _, trim_utilities.tail.nil]
    apply BEq.rfl
    apply List.cons_ne_nil
  | xa :: a'=>
    rw [add_poly, add_poly.any_nil, add_zero_right]

def shift
  {k : Type u} [Z : choose_zero k] (a : List k) : List k
  :=
  Z.zero :: a

prefix:100 "σ" => shift

def action.left
  {k : Type u} [M : mul k]
  (s : k) (a : List k) : List k
  :=
  a.map (M.mul s)

infix:90 "∘→" => action.left


def action.right
  {k : Type u} [M : mul k]
  (a : List k) (s : k) : List k
  :=
  a.map (M.mul . s)

infix:90 "←∘" => action.right

@[simp]
theorem action.left.identity
  {k : Type u} [M : mul k]
  (a : List k)  (k_left_identity : k) (h_identity : is_left_identity M.mul k_left_identity)
  : action.left k_left_identity a = a
  := by
  rw [action.left]
  exact List.map_id'' h_identity a

@[simp]
theorem action.right.identity
  {k : Type u} [M : mul k]
  (a : List k)  (k_right_identity : k) (h_identity : is_right_identity M.mul k_right_identity)
  : action.right a k_right_identity = a
  := by
  rw [action.right]
  exact List.map_id'' h_identity a

def mul_poly
  {k : Type u} [Z : choose_zero k] [A : add k] [M : mul k]
  (a : List k) (b : List k) : List k
  :=
  match a with
  | [] => []
  | x :: a' =>
    add_poly
      (action.left x b)
      (shift (mul_poly a' b))

infix:90 "*₀" => mul_poly

theorem add_poly.cons {k : Type u} [BEq k] [LawfulBEq k] [A : add k]
  (xa xb : k) (a b : List k) :
  (A.add xa xb) :: (add_poly a b)
  = (add_poly (xa :: a) (xb :: b)) := by
  rw [add_poly]


theorem add_poly.zero_zero {k : Type u} [BEq k] [LawfulBEq k]
  [A : add k] [Z : choose_zero k] (add_zero_left: ∀ x : k, A.add Z.zero x = x)
  (a : List k) (b: List k) (ha : ∀ x ∈ a, x = Z.zero) (hb : ∀ x ∈ b, x = Z.zero)
  : ∀ x ∈ (add_poly a b), x = Z.zero
  := by
  match a, b with
  | [], [] =>
    rw [add_poly]
    apply ha
  | [], b' =>
    rw [add_poly.nil_any]
    exact hb
  | a', [] =>
    rw [add_poly.any_nil]
    exact ha
  | xa :: a', xb :: b' =>
    intro x
    rw [add_poly]
    rw [List.mem_cons]
    intro hx
    cases hx
    · case inl x_repr =>
      have hxa := ha xa
      have hxb := hb xb
      rw [List.mem_cons] at hxa hxb
      have xa_zero := hxa (Or.intro_left _ rfl)
      have xb_zero := hxb (Or.intro_left _ rfl)
      rw [xa_zero, xb_zero, add_zero_left] at x_repr
      exact x_repr
    · case inr x_mem =>
      apply zero_zero add_zero_left a' b'
      intro xa hxa; exact (ha xa (List.mem_cons.mpr (Or.intro_right _ hxa)))
      intro xb hxb; exact (hb xb (List.mem_cons.mpr (Or.intro_right _ hxb)))
      assumption


theorem add_poly.zero_zero' {k : Type u} [BEq k] [LawfulBEq k]
  [A : add k] [Z : choose_zero k] (add_zero_left: ∀ x : k, A.add Z.zero x = x)
  (a : List k) (b: List k) (ha : ∀ x ∈ a, x = Z.zero) (hb : ∀ x ∈ b, x = Z.zero)
  : trim_utilities.tail (· == choose_zero.zero) (add_poly a b) = []
  := by
  apply trim_utilities.tail.nil_of_all
  intro x hx
  rw [beq_iff_eq]
  apply zero_zero add_zero_left a b ha hb x hx

theorem add_poly.zero_any' {k : Type u} [BEq k] [LawfulBEq k]
  [A : add k] [Z : choose_zero k] (add_zero_left: ∀ x : k, A.add Z.zero x = x)
  (a : List k) (b: List k) (ha : ∀ x ∈ a, x = Z.zero)
  : trim_utilities.tail (· == choose_zero.zero) (add_poly a b) = trim_utilities.tail (· == choose_zero.zero) b := by
  match a, b with
  | [], [] => rw [add_poly]
  | a', [] =>
    rw [add_poly.any_nil]
    rw [trim_utilities.tail.nil_of_all, trim_utilities.tail.nil]
    intro x hx
    rw [beq_iff_eq]
    apply ha x hx
  | [], b' =>
    rw [add_poly.nil_any]
  | xa :: a', xb :: b' =>
    rw [add_poly]
    rw [trim_utilities.tail.cons]
    rw [zero_any']
    have hxa := ha xa
    rw [List.mem_cons] at hxa
    rw [hxa (Or.intro_left _ rfl)]
    rw [add_zero_left]
    rw [←trim_utilities.tail.cons]
    apply add_zero_left
    intro xa'
    have hxa' := ha xa'
    rw [List.mem_cons] at hxa'
    intro xa'_mem
    exact (hxa' (Or.intro_right _ xa'_mem))

theorem add_poly.any_zero' {k : Type u} [BEq k] [LawfulBEq k]
  [A : add k] [Z : choose_zero k] (add_zero_right: ∀ x : k, A.add x Z.zero = x)
  (a : List k) (b: List k) (hb : ∀ x ∈ b, x = Z.zero)
  : trim_utilities.tail (· == choose_zero.zero) (add_poly a b) = trim_utilities.tail (· == choose_zero.zero) a := by
  match a, b with
  | [], [] => rw [add_poly]
  | a', [] =>
    rw [add_poly.any_nil]
  | [], b' =>
    rw [add_poly.nil_any]
    rw [trim_utilities.tail.nil_of_all, trim_utilities.tail.nil]
    intro x hx
    rw [beq_iff_eq]
    apply hb x hx
  | xa :: a', xb :: b' =>
    rw [add_poly]
    rw [trim_utilities.tail.cons]
    rw [any_zero']
    have hxb := hb xb
    rw [List.mem_cons] at hxb
    rw [hxb (Or.intro_left _ rfl)]
    rw [add_zero_right]
    rw [←trim_utilities.tail.cons]
    apply add_zero_right
    intro xb'
    have hxb' := hb xb'
    rw [List.mem_cons] at hxb'
    intro xa'_mem
    exact (hxb' (Or.intro_right _ xa'_mem))

theorem shift.trim
  {k : Type u} [BEq k] [LawfulBEq k] [Z : choose_zero k] (a : List k)
  : trim_utilities.tail (· == choose_zero.zero) ( shift a)
  = trim_utilities.tail (· == choose_zero.zero) ( shift (trim_utilities.tail (· == choose_zero.zero) a))
  := by
  rw [shift, shift, trim_utilities.tail.cons]


theorem add_poly.trim {k : Type u} [BEq k] [LawfulBEq k] [A : additive_monoid k]
  (a : List k) (b : List k)
  : trim_utilities.tail (· == choose_zero.zero) (add_poly a b)
  = trim_utilities.tail (· == choose_zero.zero) (add_poly (trim_utilities.tail (· == choose_zero.zero) a) (trim_utilities.tail (· == choose_zero.zero) b))
  := by
  match a, b with
  | [], [] =>
    rw [trim_utilities.tail.nil, add_poly.nil_any]
  | [], b' =>
    rw [add_poly.nil_any, trim_utilities.tail.nil, add_poly.nil_any, trim_utilities.tail.idempotent]
  | a', [] =>
    rw [add_poly.any_nil, trim_utilities.tail.nil, add_poly.any_nil, trim_utilities.tail.idempotent]
  -- | [xa] , [xb] =>
  --   rw [add_poly]
  --   rw [trim_utilities.tail]
  --   -- simp_all [trim_utilities.tail]
  --   if hxa : xa == A.zero then
  --     if xb == A.zero then
  --       simp_all
  --     else
  --       simp_all
  --   else
  --     if hxb : xb == A.zero then
  --       simp_all
  --     else
  --       rw [add_poly]
  --       simp_all

  --       -- simp_all[add_poly]
  | xa :: a', xb :: b' =>
    rw [add_poly]
    rw [trim_utilities.tail.cons]
    rw [add_poly.trim]
    rw [←trim_utilities.tail.cons]
    rw [add_poly.cons]
    rw [trim_utilities.tail.cons']
    rw [trim_utilities.tail]
    rw [trim_utilities.tail.cons']
    rw [trim_utilities.tail]
    repeat rw [trim_utilities.tail.idempotent]

    if hxa : xa = A.zero then
      if hxb : xb = A.zero then
        simp_all; split <;> split <;> simp_all
      else
        simp_all; split <;> simp_all
    else
      if hxb : xb = A.zero then
        simp_all; split <;> simp_all
      else
        simp_all


-- set_option diagnostics false
-- set_option trace.profiler false

@[simp]
theorem mul_poly_zero_left
  {k : Type u} [Z : choose_zero k] [A : add k] [M : mul k]
  (a : List k)
  :
  mul_poly [] a = []
  := by
  rw [mul_poly]

@[simp]
theorem mul_poly.any_nil
  {k : Type u}  [BEq k] [LawfulBEq k] [Z : choose_zero k] [A : add k] [M : mul k]
  (a : List k)
  :
  trim_utilities.tail (· == choose_zero.zero) (mul_poly a []) = []
  := by
  match a with
  | [] => simp [mul_poly]
  | x :: a' =>
    rw [mul_poly]
    rw [action.left]
    rw [List.map_nil]
    simp [shift]
    rw [trim_utilities.tail.cons]
    rw [mul_poly.any_nil]
    simp

@[simp]
theorem action.right.nil
  {k : Type u}  [BEq k] [LawfulBEq k] [Z : choose_zero k] [M : mul k]
  (a : k)
  :
  trim_utilities.tail (· == choose_zero.zero) (action.right [] a) = []
  := by
  rw[action.right, List.map_nil, trim_utilities.tail.nil]


@[simp]
theorem action.left.nil
  {k : Type u}  [BEq k] [LawfulBEq k] [Z : choose_zero k] [M : mul k]
  (a : k)
  :
  trim_utilities.tail (· == choose_zero.zero) (action.left a []) = []
  := by
  rw [action.left, List.map_nil, trim_utilities.tail.nil]

theorem action.left.from_mul
  {k : Type u} [BEq k] [LawfulBEq k] [A : additive_monoid k] [M : mul k]
  (a : List k) (s : k)
  :
  trim_utilities.tail (· == choose_zero.zero) (mul_poly [s] a)
  =
  trim_utilities.tail (· == choose_zero.zero) (action.left s a)
  := by
  rw [mul_poly]
  simp_all [shift]

theorem action.right.from_mul
  {k : Type u} [BEq k] [LawfulBEq k] [A : additive_monoid k] [M : mul k]
  (a : List k) (s : k)
  :
  trim_utilities.tail (· == choose_zero.zero) (mul_poly a [s])
  =
  trim_utilities.tail (· == choose_zero.zero) (action.right a s)
  := by
  match a with
  | [] =>
    simp
  | xa :: a' =>
    rw [mul_poly]
    rw [action.left]
    rw [add_poly.trim]
    rw [shift.trim]
    rw [action.right.from_mul]
    rw [←shift.trim]
    rw [←add_poly.trim]
    rw [shift]
    simp
    rw [add_poly]
    rw [action.right]
    rw [action.right]
    simp

@[simp]
theorem mul_poly.identity_any
  {k : Type u} [BEq k] [LawfulBEq k] [A : additive_monoid k] [M : mul k]
  (k_left_identity : k) (h_identity : is_left_identity M.mul k_left_identity)
  (a : List k)
  :
  trim_utilities.tail (· == choose_zero.zero) (mul_poly [k_left_identity] a)
  =
  trim_utilities.tail (· == choose_zero.zero) a
  := by
  rw [action.left.from_mul a k_left_identity]
  rw [action.left.identity]
  repeat assumption

@[simp]
theorem mul_poly.any_identity
  {k : Type u} [BEq k] [LawfulBEq k] [A : additive_monoid k] [M : mul k]
  (k_right_identity : k)
  (h_right_identity : is_right_identity M.mul k_right_identity)
  (a : List k)
  :
  trim_utilities.tail (· == choose_zero.zero) (mul_poly a [k_right_identity])
  =
  trim_utilities.tail (· == choose_zero.zero) a
  := by
  rw [action.right.from_mul]
  rw [action.right.identity]
  repeat assumption


theorem add_poly.singleton_any
  {k : Type u} [BEq k] [LawfulBEq k] [A : add k] (a : List k) (x : k) (y : k)
  : add_poly [x] (y :: a) = (A.add x y) :: a := by
  simp [add_poly]

theorem action.left.cons_linear
  {k : Type u}  [BEq k] [LawfulBEq k] [Z : choose_zero k] [A : add k] [M : mul k]
  (add_zero_right : ∀ x : k, A.add x Z.zero = x)
  (a : k) (x : k) (b : List k)  :
  trim_utilities.tail (· == choose_zero.zero) (action.left a (x :: b))
  = trim_utilities.tail (· == choose_zero.zero) (add_poly
      [M.mul a x]
      (shift (action.left a b)))
  := by
  rw [action.left, shift]
  simp
  rw [add_poly.singleton_any]
  rw [add_zero_right]
  rw [action.left]

theorem action.right.cons_linear
  {k : Type u}  [BEq k] [LawfulBEq k] [Z : choose_zero k] [A : add k] [M : mul k]
  (add_zero_right : ∀ x : k, A.add x Z.zero = x)
  (a : List k) (x : k) (b : k)  :
  trim_utilities.tail (· == choose_zero.zero) (action.right (x :: a) b)
  = trim_utilities.tail (· == choose_zero.zero) (add_poly
      [M.mul x b]
      (shift (action.right a b)))
  := by
  rw [action.right, shift]
  simp
  rw [add_poly.singleton_any]
  rw [add_zero_right]
  rw [action.right]

theorem shift.add
  {k : Type u} [BEq k] [LawfulBEq k] [Z : choose_zero k] [A : add k] (add_zero_right : ∀ x : k, A.add x Z.zero = x) (a : List k) (b : List k) :
  shift (add_poly a b) = add_poly (shift a) (shift b)
  := by
  rw [shift, shift, shift]
  rw [add_poly]
  rw [add_zero_right]

theorem add.shift_shift {k : Type u} [BEq k] [LawfulBEq k] [Z : choose_zero k] [A : add k] (add_zero_right : ∀ x : k, A.add x Z.zero = x) (a : List k) (b : List k) :
  add_poly (shift a) (shift b) = shift (add_poly a b)
  := by symm; apply shift.add add_zero_right a b

theorem add_poly.associative
  {k : Type u} [BEq k] [LawfulBEq k] [A : additive_monoid k]
  (a : List k) (b : List k) (c : List k):
  add_poly a (add_poly b c) = add_poly (add_poly a b) c := by
  match a, b, c with
  | [], b, c => simp
  | a, [], c => simp
  | a, b, [] => simp
  | xa :: a', xb :: b', xc :: c' =>
    repeat rw [add_poly]
    rw [add_poly.associative]
    rw [A.add_is_assoc]

theorem add_poly.associative'
  {k : Type u} [BEq k] [LawfulBEq k] [A : additive_monoid k] (a : List k) (b : List k) (c : List k):
  trim_utilities.tail (· == choose_zero.zero) (
    add_poly
      (trim_utilities.tail (· == choose_zero.zero) a)
      (trim_utilities.tail (· == choose_zero.zero) (
        add_poly
          (trim_utilities.tail (· == choose_zero.zero) b)
          (trim_utilities.tail (· == choose_zero.zero) c)
        )
      )
  )
  =
  trim_utilities.tail (· == choose_zero.zero) (
    add_poly
      (trim_utilities.tail (· == choose_zero.zero) (
        add_poly
          (trim_utilities.tail (· == choose_zero.zero) a)
          (trim_utilities.tail (· == choose_zero.zero) b)
        )
      )
      (trim_utilities.tail (· == choose_zero.zero) c)
  ) := by
  conv in trim_utilities.tail (· == choose_zero.zero) (add_poly (trim_utilities.tail (· == choose_zero.zero) b) _) =>
    rw[←add_poly.trim]
  conv in trim_utilities.tail (· == choose_zero.zero) (add_poly (trim_utilities.tail (· == choose_zero.zero) a) _) =>
    rw[←add_poly.trim]
  conv in trim_utilities.tail (· == choose_zero.zero) (add_poly (trim_utilities.tail (· == choose_zero.zero) a) _) =>
    rw[←add_poly.trim]
  rw[←add_poly.trim]
  rw [add_poly.associative]


theorem add_poly.commutative
  {k : Type u} [BEq k] [LawfulBEq k] [A : commutative_additive_monoid k] (a : List k) (b : List k):
  (add_poly a b) = (add_poly b a) := by
  match a, b with
  | [], b => simp
  | a, [] => simp
  | xa :: a', xb :: b' =>
    rw [add_poly, add_poly, A.add_is_comm , add_poly.commutative]
    repeat assumption


theorem mul_poly.any_cons
  {k : Type u}
  [BEq k]
  [LawfulBEq k]
  [A : commutative_additive_monoid k]
  [M : mul k]
  (a : List k)
  (x : k)
  (b : List k)  :
  trim_utilities.tail (· == choose_zero.zero) (mul_poly a (x :: b))
  = trim_utilities.tail (· == choose_zero.zero) (add_poly (action.right a x)
      (shift (mul_poly a b)))
  := by
  match a with
  | [] =>
    rw [mul_poly_zero_left]
    rw [action.right]
    simp
    rw [shift]
    simp
  | x' :: a' =>
    rw[mul_poly]
    rw[
      add_poly.trim,
        action.left.cons_linear,
        shift.trim,
          mul_poly.any_cons,
        ← shift.trim,
      ←add_poly.trim
    ]
    rw [shift.add]
    rw [←add_poly.associative]
    conv in (σ(_) +₀ (_ +₀ _)) =>
      rw [add_poly.associative]
      arg 1
      rw [add_poly.commutative]
      rfl
    rw [←add_poly.associative]
    rw [add_poly.associative]
    rw [add_poly.trim, ←action.right.cons_linear, ←add_poly.trim]
    rw [add.shift_shift]
    rw [add_poly.trim, shift.trim, ←mul_poly, ←shift.trim, ←add_poly.trim]
    apply add_zero_right
    apply add_zero_right
    apply A.add_zero_right
    apply A.add_zero_right


theorem action.left_eq_right
  {k : Type u} [BEq k] [LawfulBEq k] [commutative_mul k]
  (a : List k) (s : k)
  : action.left s a = action.right a s
  := by
  rw [action.left, action.right]
  rw [List.map_eq_map_iff]
  intro element
  intro h_element
  apply commutative_mul.mul_is_comm

theorem mul_poly.commutative
  {k : Type u} [BEq k] [LawfulBEq k]
  [A : commutative_additive_monoid k]
  [M : commutative_multiplicative_monoid k]
  (a : List k) (b : List k)
  :
  trim_utilities.tail (· == choose_zero.zero) (mul_poly a b) = trim_utilities.tail (· == choose_zero.zero) (mul_poly b a)
  := by
  match a with
  | [] => simp
  | x :: a' =>
    rw [mul_poly, mul_poly.any_cons, action.left_eq_right]
    rw [
      add_poly.trim,
        shift.trim,
          mul_poly.commutative,
        ← shift.trim,
      ←add_poly.trim,
    ]


def add_poly_safe
  {k : Type u} [Z : choose_zero k] [A : add k] [BEq k] [LawfulBEq k] (a : List k) (b : List k)
  :=
  trim_utilities.tail (· == choose_zero.zero) (add_poly (trim_utilities.tail (· == choose_zero.zero) a) (trim_utilities.tail (· == choose_zero.zero) b))

def mul_poly_safe
  {k : Type u} [BEq k] [LawfulBEq k] [Z : choose_zero k] [A : add k] [M : mul k]
  (a : List k) (b : List k) :=
  trim_utilities.tail (· == choose_zero.zero) (mul_poly (trim_utilities.tail (· == choose_zero.zero) a) (trim_utilities.tail (· == choose_zero.zero) b))

theorem mul_poly_safe.commutative
  {k : Type u} [BEq k] [LawfulBEq k]
  [A : commutative_additive_monoid k]
  [M : commutative_multiplicative_monoid k]
  (a b : List k)
  : mul_poly_safe a b = mul_poly_safe b a := by
  rw[mul_poly_safe, mul_poly.commutative, ←mul_poly_safe]

theorem add_poly_safe.associative
  {k : Type u} [BEq k] [LawfulBEq k] [additive_monoid k]
  (a : List k) (b : List k) (c : List k):
    add_poly_safe a (add_poly_safe b c) =
    add_poly_safe (add_poly_safe a b) c
  := by
  rw [add_poly_safe, add_poly_safe, add_poly_safe, add_poly_safe]
  rw [trim_utilities.tail.idempotent, trim_utilities.tail.idempotent]
  rw [add_poly.associative']

structure reduced_polynomial (k : Type u) (P : k → Bool) where
  value : List k
  is_reduced : trim_utilities.tail P value = value

theorem ext_both_directions (k : Type u) (P : k → Bool) {p q : reduced_polynomial k P} : p = q ↔ p.value = q.value := by
  constructor
  · intro h; simp [h]
  · intro h; cases p; cases q; simp at h; simp [h]

@[ext]
theorem ext_direct (k : Type u) (P : k → Bool) {p q : reduced_polynomial k P}
  (values_are_equal : p.value = q.value) :  p = q := by
  cases p;
  cases q;
  simp at values_are_equal
  simp [values_are_equal]

theorem ext_reverse (k : Type u) (P : k → Bool) {p q : reduced_polynomial k P}
  (h : p = q) : p.value = q.value := by
  cases p;
  cases q;
  simp at h
  simp [h]

instance reduced_are_BEq (k : Type u) [Z : choose_zero k] [BEq k] [LawfulBEq k] : BEq (reduced_polynomial k (· == Z.zero)) where
  beq := by
    intro a
    intro b
    apply a.value == b.value

instance {k : Type u} [Z : choose_zero k] [BEq k] [LawfulBEq k] : LawfulBEq (reduced_polynomial k (· == Z.zero)) where
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


theorem add_poly_safe.reduced
  {k : Type u} [Z : choose_zero k] [A : add k]
  [BEq k] [LawfulBEq k]
  (a : List k) (b : List k)
  : trim_utilities.tail (· == choose_zero.zero) (add_poly_safe a b) = add_poly_safe a b
  := by
  rw [add_poly_safe]
  rw [trim_utilities.tail.idempotent]

theorem mul_poly_safe.reduced
  {k : Type u} [BEq k] [LawfulBEq k] [Z : choose_zero k] [A : add k] [M : mul k]
  (a : List k) (b : List k)
  : trim_utilities.tail (· == choose_zero.zero) (mul_poly_safe a b)
  = mul_poly_safe a b
  := by
  rw [mul_poly_safe]
  rw [trim_utilities.tail.idempotent]

def add_reduced_poly
  {k : Type u} [Z : choose_zero k] [A : add k]
  [BEq k] [LawfulBEq k]
  (a : reduced_polynomial k (· == Z.zero)) (b : reduced_polynomial k (· == Z.zero))
  : reduced_polynomial k (· == Z.zero)
  := {
    value := add_poly_safe a.value b.value
    is_reduced := by apply add_poly_safe.reduced
  }

def mul_reduced_poly
  {k : Type u} [BEq k] [LawfulBEq k] [Z : choose_zero k] [A : add k] [M : mul k]
  (a : reduced_polynomial k (· == Z.zero)) (b : reduced_polynomial k (· == Z.zero))
  : reduced_polynomial k (· == Z.zero)
  := {
    value := mul_poly_safe a.value b.value
    is_reduced := by
      apply mul_poly_safe.reduced
  }

def add_reduced_poly.inverse {k : Type u} {R : ring k} [BEq k] [LawfulBEq k] (a : reduced_polynomial k (· == R.zero)) : List k :=
  a.value.map R.add_inverse

theorem a_decomposition {k : Type u} (a : List k) (x : k) : ∃ c, ∃ aq, x :: a = aq ++ [c] :=
    match a with
    | [] => ⟨ x, by simp ⟩
    | xa :: a' => by
      rcases a_decomposition a' xa with ⟨ tail, head, tail_is_okay ⟩
      rw [tail_is_okay]
      exists tail, (x :: head)

theorem add_inverse_preserves_zero {k : Type u} [BEq k] [LawfulBEq k] [R : ring k] (x : k) : (· == R.zero) (x) ↔ (· == R.zero) (R.add_inverse x) := by
  constructor
  intro hx
  simp_all
  intro hx
  simp_all
  exact add_inverse_is_zero x hx

theorem add_inverse_is_reduced (k : Type u) [R : ring k] [BEq k] [LawfulBEq k]
  (a : List k)
  (is_reduced : trim_utilities.tail (· == choose_zero.zero) a = a)
  :
  trim_utilities.tail (· == choose_zero.zero) (a.map R.add_inverse) = a.map R.add_inverse := by
  rw [trim_utilities.tail.map (· == choose_zero.zero) a R.add_inverse add_inverse_preserves_zero]
  rw [is_reduced]

theorem inverse_is_left_inverse (R : ring k) [BEq k] [LawfulBEq k] (a : List k) :
  trim_utilities.tail (· == choose_zero.zero) (add_poly (a.map R.add_inverse) a) = [] :=
  by
  match a with
  | [] => simp
  | x :: a =>
    rw [List.map_cons]
    rw [add_poly]
    rw [add_inverse_is_inverse]
    rw [trim_utilities.tail.cons]
    rw [inverse_is_left_inverse]
    simp

theorem action.left.left_linear (R : ring k) [BEq k] [LawfulBEq k] (x y : k) (a : List k) :
  (action.left (R.add x y) a)
  =
  (add_poly (action.left x a) (action.left y a))
  := by
  repeat rw [action.left]
  match a with
  | [] => simp
  | xa :: a' =>
    simp
    rw [add_poly]
    rw [R.mul_is_linear_left x y xa]
    apply (List.cons_inj_right _).mpr
    rw [←action.left]
    rw [action.left.left_linear]
    rw [action.left, action.left]


theorem action.left.right_linear (R : ring k) [BEq k] [LawfulBEq k] (x : k) (a b : List k) :
  (action.left x (add_poly  a b) )
  =
  (add_poly (action.left x a) (action.left x b))
  := by
  repeat rw [action.left]
  match a, b with
  | [], [] => simp
  | [], _ => simp
  | _, [] => simp
  | xa :: a, xb :: b =>
    rw [List.map_cons]
    rw [List.map_cons]
    rw [add_poly]
    rw [add_poly]
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
    rw [←action.left]
    rw [←action.left]
    rw [←action.left]
    apply action.left.right_linear

theorem mul_poly.left_linear [R : ring k] [BEq k] [LawfulBEq k] (a : List k) (b : List k) (c : List k) :
  trim_utilities.tail (· == choose_zero.zero) (mul_poly ( add_poly a b ) c)
  =
  trim_utilities.tail (· == choose_zero.zero) (add_poly ( mul_poly a c ) ( mul_poly b c ) )
  := by
  match a, b with
  | [], [] => simp
  | [], b => simp
  | a, [] => simp
  | xa :: a', xb :: b' =>
    rw [add_poly]
    rw [mul_poly]
    rw [add_poly.trim, shift.trim, mul_poly.left_linear, ← shift.trim, ← add_poly.trim]

    rw [action.left.left_linear]
    rw [mul_poly]
    rw [mul_poly]
    rw [add_poly.associative]
    rw [shift.add]
    rw [add_poly.associative]

    conv in (((action.left _ _) +₀ (_)) +₀ σ _) =>
      rw [←add_poly.associative]
      arg 2
      rw [add_poly.commutative]

    rw [add_poly.associative]
    apply R.add_zero_right

theorem action.left.trim  (R : ring k) [BEq k] [LawfulBEq k] (x : k) (a : List k)
  :
  trim_utilities.tail (· == choose_zero.zero) (action.left x ( trim_utilities.tail (· == choose_zero.zero) a))
  =
  trim_utilities.tail (· == choose_zero.zero) (action.left x a)
  := by
  match a with
  | [] => simp
  | xa :: a' =>
    rw [trim_utilities.tail]
    split
    case h_1 q1 q2 =>
      rw [action.left]
      rw [action.left]
      simp_all
      conv =>
        rhs
        rw [trim_utilities.tail.cons]
      have ha' := trim_utilities.tail.all_of_nil (· == choose_zero.zero) a' q2
      rw [←action.left]
      rw [←action.left]
      conv =>
        rhs
        rw [←action.left.trim]
      rw [q2]
      simp_all [trim_utilities.tail.singleton, action.left]
      rw [apply_ite (List.map (R.mul x))]
      rw [apply_ite (trim_utilities.tail (· == choose_zero.zero))]
      simp_all
    case h_2 q1 q2 =>
      conv =>
        rhs
        rw [action.left]
        rw [List.map_cons]
        rw [←action.left]
        rw [trim_utilities.tail.cons, ←action.left.trim, ←trim_utilities.tail.cons]
        rw [action.left]
        rw [←List.map_cons]
        rw [←action.left]

theorem action.left.zero [R : ring k] [BEq k] [LawfulBEq k] (a : List k)
  : trim_utilities.tail  (· == choose_zero.zero) (action.left R.zero a) = [] := by
  apply trim_utilities.tail.nil_of_all (· == choose_zero.zero) (action.left R.zero a) _
  match a with
  | [] =>
    rw [action.left]
    simp
  | ha :: ta =>
    intro x hx
    rw [action.left, List.map_cons, List.mem_cons, mul_zero_any_is_zero, ←action.left] at hx
    cases hx
    simpa
    · case inr w =>
      exact trim_utilities.tail.all_of_nil (· == choose_zero.zero) (action.left R.zero ta) (action.left.zero ta) x w


theorem mul_poly.trim_1  [R : ring k] [BEq k] [LawfulBEq k] (a : List k) (b : List k)
  :
  trim_utilities.tail (· == choose_zero.zero)
    (mul_poly (trim_utilities.tail (· == choose_zero.zero) a) b)
  =
  trim_utilities.tail (· == choose_zero.zero)
    (mul_poly a b)
  := by
  match a with
  | [] => simp
  | xa :: a' =>
    -- conv =>
      -- lhs
    rw [trim_utilities.tail]
    split
    case h_1 q1 q2 =>
      rw [mul_poly]
      rw [add_poly.trim]
      rw [shift.trim]
      conv => rhs; rw [←mul_poly.trim_1]
      rw [q2]
      rw [shift]
      simp_all
      rw [apply_ite (mul_poly · b), apply_ite (trim_utilities.tail (· == choose_zero.zero)), action.left.from_mul]
      if h : xa == R.zero then
        rw [beq_iff_eq] at h
        simp_all [action.left.zero]
      else
        rw [trim_utilities.tail.idempotent]
        rw [beq_iff_eq] at h
        simp_all
    case h_2 q1 q2 =>
      rw [
        mul_poly,
          add_poly.trim,
            shift.trim,
              mul_poly.trim_1,
            ←shift.trim,
          ←add_poly.trim,
        ←mul_poly
      ]

theorem mul_poly.trim  [R : ring k] [BEq k] [LawfulBEq k] (a : List k) (b : List k)
  :
  trim_utilities.tail (· == choose_zero.zero)
    (mul_poly (trim_utilities.tail (· == choose_zero.zero) a) (trim_utilities.tail (· == choose_zero.zero) b))
  =
  trim_utilities.tail (· == choose_zero.zero)
    (mul_poly a b)
  := by
  match a with
  | [] => simp
  | xa :: a' =>
    rw [mul_poly]
    have h := mul_poly.trim a' b
    rw [add_poly.trim, ←action.left.trim, shift.trim, ←h, ←shift.trim, ←add_poly.trim]
    rw [←mul_poly, trim_utilities.tail.cons]
    rw [mul_poly.trim_1]

theorem action.left.right_associative [R : ring k] [BEq k] [LawfulBEq k]
  (a : k) (b : List k) (c : List k) :
  trim_utilities.tail (· == choose_zero.zero) (mul_poly (action.left a b) c)
  =
  trim_utilities.tail (· == choose_zero.zero) (action.left a (mul_poly b c))
  := by
  match b with
  | [] =>
    simp_all [action.left]
  | x :: b' =>
    rw [mul_poly]
    rw [action.left]
    rw [List.map_cons]
    rw [mul_poly]
    rw [← action.left]
    rw [add_poly.trim, shift.trim, action.left.right_associative, ← shift.trim, ← add_poly.trim]
    rw [shift]
    rw [shift]
    rw [action.left.right_linear]

    rw [action.left]
    rw [action.left]
    rw [action.left]
    rw [action.left]

    rw [List.map_map]

    have h_mul_comp (a b: k) : R.mul a ∘ R.mul b = R.mul (R.mul a b) := by
      ext
      simp
      rw [R.mul_is_assoc]
    rw [h_mul_comp]

    rw [action.left]
    rw [List.map_cons]
    rw [mul_any_zero_is_zero]

theorem mul_poly.associative (R : ring k) [BEq k] [LawfulBEq k]
  (a : List k) (b : List k) (c : List k) :
  trim_utilities.tail (· == choose_zero.zero) (mul_poly (mul_poly a b) c)
  =
  trim_utilities.tail (· == choose_zero.zero) (mul_poly a (mul_poly b c))
  := by
  match a with
  | [] => simp
  | x :: a' =>
    rw [mul_poly]
    -- rw [mul_poly]
    rw [mul_poly.left_linear]
    rw [shift, mul_poly, mul_poly]
    conv => rhs; rw [add_poly.trim]
    conv => lhs; rw [add_poly.trim]
    congr 2
    · case e_a.e_a =>
      rw [action.left.right_associative]
    · case e_a.e_b =>
      rw [
        add_poly.trim,
        action.left.zero,
        add_poly.nil_any,
        shift.trim,
          mul_poly.associative,
        ← shift.trim,
        trim_utilities.tail.idempotent
      ]

theorem degenerate_polynomial_ring {k : Type u} [R : ring k] [BEq k] [LawfulBEq k] (a : reduced_polynomial k (· == R.zero)) (h : R.e = R.zero) :
  a.value = [] := by
  rw [←a.is_reduced]
  apply trim_utilities.tail.nil_of_all
  have q := e_eq_zero_then_one_element h
  intro x
  rw [q x]
  simp


instance polynomial_ring
  (k : Type u) [R : ring k] [BEq k] [LawfulBEq k]: ring (reduced_polynomial k (· == R.zero)) :=
  {
    add := add_reduced_poly
    zero := {
      value := []
      is_reduced := by apply trim_utilities.tail.nil
    }
    add_inverse (a : reduced_polynomial k (· == R.zero)) := {
      value := a.value.map R.add_inverse
      is_reduced := by
        apply add_inverse_is_reduced k a.value
        apply a.is_reduced
    }
    mul := mul_reduced_poly
    e := {
      value := trim_utilities.tail (· == choose_zero.zero) [R.e]
      is_reduced := by apply trim_utilities.tail.idempotent
    }
    -- non_trivial := by
      -- simp
    add_inverse_is_inverse := by
      rw [is_left_inverse]
      intro a
      rw [add_reduced_poly]
      simp [add_poly_safe]
      rw [←add_poly.trim]
      apply inverse_is_left_inverse
    add_is_comm := by
      intro a b
      rw [add_reduced_poly, add_reduced_poly]
      simp
      rw [add_poly_safe]
      rw [add_poly.commutative]
      rw [←add_poly_safe]
    mul_is_comm := by
      intro a b
      simp [mul_reduced_poly, mul_reduced_poly]
      rw [mul_poly_safe.commutative]
    mul_e_left := by
      intro a
      rw [mul_reduced_poly]
      apply ext_direct
      simp
      rw [mul_poly_safe, mul_poly.trim_1, apply_ite (mul_poly · (trim_utilities.tail (· == R.zero) a.value))]
      rw [mul_poly, apply_ite (trim_utilities.tail _), trim_utilities.tail.nil, mul_poly.identity_any, a.is_reduced, a.is_reduced]
      split
      symm
      apply degenerate_polynomial_ring
      apply beq_iff_eq.mp
      assumption
      rfl
      apply R.mul_e_left
    add_zero_left := by
      intro a
      simp [add_reduced_poly, add_poly_safe, trim_utilities.tail.nil]
      apply ext_direct
      simp
      rw [a.is_reduced]
      rw [a.is_reduced]
    mul_is_linear_left := by
      intro a b c
      repeat rw [mul_reduced_poly]
      repeat rw [add_reduced_poly]
      simp
      repeat rw [add_poly_safe]
      repeat rw [mul_poly_safe]
      repeat rw [←add_poly.trim]
      rw [a.is_reduced]
      rw [b.is_reduced]
      rw [←mul_poly.left_linear]
      rw [trim_utilities.tail.idempotent]
      rw [mul_poly.trim]
      rw [c.is_reduced]
    mul_is_linear_right := by
      intro a b c
      repeat rw [mul_reduced_poly]
      repeat rw [add_reduced_poly]
      simp
      repeat rw [add_poly_safe]
      repeat rw [mul_poly_safe]
      rw [mul_poly.commutative]
      rw [←a.is_reduced]
      rw [b.is_reduced]
      rw [c.is_reduced]
      rw [mul_poly.trim]
      rw [mul_poly.trim]
      rw [mul_poly.left_linear]
      repeat rw [a.is_reduced]
      rw [add_poly.trim]
      rw [add_poly.trim]
      rw [mul_poly.commutative]
      conv =>
        rhs
        arg 2
        arg 2
        rw [mul_poly.commutative]
    add_is_assoc := by
      intro a b c
      repeat rw [add_reduced_poly]
      simp
      rw [add_poly_safe.associative]
    mul_is_assoc := by
      intro a b c
      rw [mul_reduced_poly]
      rw [mul_reduced_poly]
      rw [mul_reduced_poly]
      rw [mul_reduced_poly]
      simp
      rw [mul_poly_safe]
      rw [mul_poly_safe]
      rw [mul_poly_safe]
      rw [mul_poly_safe]
      -- simp
      repeat rw [mul_poly.trim]
      repeat rw [reduced_polynomial.is_reduced]
      rw [mul_poly.trim_1]
      conv => rhs; rw [←mul_poly.trim_1]
      repeat rw [mul_poly.trim]
      rw [mul_poly.associative]
    mul_e_right := by
      intro a
      rw [mul_reduced_poly]
      apply ext_direct
      simp
      rw [
        mul_poly_safe,
        apply_ite (trim_utilities.tail (· == R.zero)),
        apply_ite (mul_poly (trim_utilities.tail (· == R.zero) a.value)),
        apply_ite (trim_utilities.tail (· == R.zero)),
        mul_poly.trim,
        mul_poly.trim,
        mul_poly.any_nil, mul_poly.any_identity, a.is_reduced
      ]
      split
      symm
      apply degenerate_polynomial_ring
      apply beq_iff_eq.mp
      assumption
      rfl
      apply R.mul_e_right
    add_zero_right := by
      intro a
      simp [add_reduced_poly, add_poly_safe, a.is_reduced]
  }

theorem polynomial_ring.identity_is (k : Type u) [R : ring k] [BEq k] [LawfulBEq k] : (polynomial_ring k).e = {
      value := trim_utilities.tail (· == choose_zero.zero) [R.e]
      is_reduced := by apply trim_utilities.tail.idempotent
    } := by rfl

theorem polynomial_ring.zero_is (k : Type u) [R : ring k] [BEq k] [LawfulBEq k] : (polynomial_ring k).zero = {
      value := []
      is_reduced := by exact trim_utilities.tail.nil fun x => x == ⟨0⟩
    } := by rfl

theorem polynomial_ring.zero_value (k : Type u) [R : ring k] [BEq k] [LawfulBEq k] : (⟨0⟩ : (reduced_polynomial k (· == ⟨0⟩))).value = [] := by
  rfl


@[reducible]
def ring_replace_identity (k : Type u) [R : ring k]
  (replace_zero : k) (replace_e: k)
  (h_zero : replace_zero = R.zero)
  (h_e : replace_e = R.e)
  : ring_with_fixed_identities k replace_zero replace_e :=
  {
    kz_is_zero := h_zero
    ke_is_e := h_e
  }


instance polynomial_ring_with_fixed_identity
  (k : Type u) (k_z k_e : k) [R : ring_with_fixed_identities k k_z k_e] [BEq k] [LawfulBEq k]
  (t_z t_e : (reduced_polynomial k (· == choose_zero.zero)))
  (h_z : t_z.value = [])
  (h_e : t_e.value = trim_utilities.tail (· == choose_zero.zero) [R.e])
  :
    ring_with_fixed_identities
    (reduced_polynomial k (· == choose_zero.zero)) t_z t_e
    -- ({
    --   value := []
    --   is_reduced := by apply trim_utilities.tail.nil
    -- })
    -- ({
    --   value := trim_utilities.tail (· == choose_zero.zero) [R.e]
    --   is_reduced := by apply trim_utilities.tail.idempotent
    -- })
  := ring_replace_identity (reduced_polynomial k (· == choose_zero.zero)) t_z t_e (
    by (exact polynomial_ring.ext_direct_iff.mpr h_z)
  ) (
    by
    apply polynomial_ring.ext_direct_iff.mpr
    rw [polynomial_ring.identity_is]
    rw [h_e]
  )



  -- {
  --   kz_is_zero := by
  --     simp_all
  --     (expose_names; exact polynomial_ring.ext_direct_iff.mpr h)
  --   ke_is_e := by
  --     simp_all
  --     (expose_names; exact polynomial_ring.ext_direct_iff.mpr h_1)
  -- }

theorem polynomial_ring_add {k : Type u} [R : ring k] [BEq k] [LawfulBEq k] (a b : reduced_polynomial k (· == R.zero)) :
  a ⊹ b = add_reduced_poly a b := by
  exact ext_direct k (· == R.zero) rfl

theorem polynomial_ring_mul {k : Type u} [R : ring k] [BEq k] [LawfulBEq k] (a b : reduced_polynomial k (· == R.zero)) :
  a ⋆ b = mul_reduced_poly a b := by
  exact ext_direct k (· == R.zero) rfl

theorem polynomial_ring_e {k : Type u} [R : ring k] [BEq k] [LawfulBEq k] :
  (polynomial_ring k).e.value = trim_utilities.tail (· == choose_zero.zero) [R.e]:= by
  rfl

def eval_polynomial'
  {base : Type v} [ring base]
  {target : Type u} [ring target]
  (eval_x : target) (f : base → target) (a : List base)
  : target
  :=
  match a with
  | [] => choose_zero.zero
  | xa :: a' => f xa ⊹ eval_x ⋆ (eval_polynomial' eval_x f a')

def eval_polynomial
  {base : Type v} [ring base]
  {target : Type u} [ring target]
  (eval_x : target) (f : ring_hom₁ base target) (a : List base)
  : target
  :=
  match a with
  | [] => choose_zero.zero
  | xa :: a' => f.original_function xa ⊹ eval_x ⋆ (eval_polynomial eval_x f a')


-- set_option trace.Meta.synthInstance true

@[simp]
theorem eval_polynomial_ignores_trim
  {base : Type v} [Rb : ring base] [BEq base] [LawfulBEq base]
  {target : Type u} [Rt : ring target]
  (eval_x : target) (f : ring_hom₁ base target)
  (x : List base) :
  eval_polynomial eval_x f (trim_utilities.tail (· == choose_zero.zero) x) = eval_polynomial eval_x f x
  := by
  match x with
  | [] => simp
  | xi :: x' =>
    rw [eval_polynomial]
    conv =>
      rhs
      rw [←eval_polynomial_ignores_trim]
      rfl
    rw [trim_utilities.tail]
    split
    simp_all [eval_polynomial]
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
  : eval_polynomial eval_x f (add_poly x y) = (eval_polynomial eval_x f x) ⊹ (eval_polynomial eval_x f y)
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
    rw [add_poly.cons]


theorem polynomial_left_scalar_action_is_mul
  {k : Type u} [BEq k] [LawfulBEq k]
  [A : additive_monoid k] [M : mul k]
  (s : k) (a : List k) :
  trim_utilities.tail (· == choose_zero.zero) (action.left s a) = trim_utilities.tail (· == choose_zero.zero) (mul_poly [s] a) := by
  rw [mul_poly]
  simp [shift]

theorem polynomial_right_scalar_action_is_mul
  {k : Type u} [BEq k] [LawfulBEq k]
  [A : commutative_additive_monoid k] [M : mul k]
  (a : List k) (s : k) :
  trim_utilities.tail (· == choose_zero.zero) (action.right a s) = trim_utilities.tail (· == choose_zero.zero) (mul_poly a [s]) := by
  rw [mul_poly.any_cons]
  rw [add_poly.trim]
  rw [shift.trim]
  simp [shift]
  rw [trim_utilities.tail.idempotent]

theorem eval_polynomial_mul
  {base : Type v} [ring base] [BEq base] [LawfulBEq base]
  {target : Type u} [ring target]
  (eval_x : target) (f : ring_hom₁ base target)
  (x y : List base)
  : eval_polynomial eval_x f (mul_poly x y) = (eval_polynomial eval_x f x) ⋆ (eval_polynomial eval_x f y)
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
    rw [mul_poly.any_cons]
    rw [mul_poly]
    rw [shift]
    rw [shift]
    rw [eval_polynomial_ignores_trim]
    rw [eval_polynomial_add]
    rw [eval_polynomial]
    rw [←eval_polynomial_ignores_trim]
    rw [action.right.cons_linear]
    rw [eval_polynomial_ignores_trim]
    rw [eval_polynomial_add]
    rw [eval_polynomial_add]
    rw [shift]
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
  : ring_hom₁ (reduced_polynomial base (· == choose_zero.zero)) target :=
  {
    original_function (x) := eval_polynomial eval_x f x.value
    map_add (a b) := by
      rw [polynomial_ring_add]
      rw [add_reduced_poly]
      simp_all
      rw [add_poly_safe]
      rw [←add_poly.trim]
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
      rw [mul_reduced_poly]
      simp
      rw [mul_poly_safe]
      simp [eval_polynomial_mul]
  }

def base_inclusion
  {base : Type v} [BEq base] [LawfulBEq base] [ring base]
  (x : base) : reduced_polynomial base  (· == choose_zero.zero):=
  {
    value := trim_utilities.tail (· == choose_zero.zero) [x]
    is_reduced := by exact trim_utilities.tail.idempotent (· == choose_zero.zero) [x]
  }

def inclusion_base_to_free_algebra
  {base : Type v} [BEq base] [LawfulBEq base] [ring base]
  : ring_hom₁ base (reduced_polynomial base (· == choose_zero.zero))
  :=
  {
    original_function := base_inclusion
    map_add := by
      intro a b
      apply ext_direct
      rw [base_inclusion, base_inclusion, base_inclusion, polynomial_ring_add, add_reduced_poly]
      simp_all
      if a == ⟨0⟩ then
        if b == ⟨0⟩ then
          simp_all
          rw [add_poly_safe]
          rw [trim_utilities.tail.nil]
          rw [add_poly.any_nil]
          rw [trim_utilities.tail.nil]
        else
          simp_all
          rw [add_poly_safe]
          rw [trim_utilities.tail.nil]
          rw [add_poly.nil_any]
          rw [trim_utilities.tail.idempotent]
          rw [trim_utilities.tail]
          simpa
      else
        if b == ⟨0⟩ then
          simp_all
          rw [add_poly_safe]
          rw [trim_utilities.tail.nil]
          rw [add_poly.any_nil]
          rw [trim_utilities.tail.idempotent]
          rw [trim_utilities.tail]
          simpa
        else
          rw [add_poly_safe]
          simp_all
          rw [add_poly, add_poly.any_nil, trim_utilities.tail]
          simp
    map_zero := by
      simp [base_inclusion]
      rfl
    map_e := by
      simp [base_inclusion]
      rfl
    map_mul := by
      intro a b
      apply ext_direct
      rw [base_inclusion, base_inclusion, base_inclusion, polynomial_ring_mul, mul_reduced_poly]
      simp_all
      rw [apply_ite (mul_poly_safe _), apply_ite (mul_poly_safe · _), apply_ite (mul_poly_safe · _),
        mul_poly_safe, mul_poly_safe, mul_poly_safe, mul_poly_safe]
      simp_all
      if a == ⟨0⟩ then
        simp_all
      else
        if b == ⟨0⟩ then
          simp_all
        else
          simp_all
          rw [mul_poly, shift, action.left, mul_poly, add_poly.any_zero,
            List.map, List.map, trim_utilities.tail, trim_utilities.tail.nil]
  }

instance free_algebra_over_ring {base : Type v} [ring base] [BEq base] [LawfulBEq base] : free_algebra base (reduced_polynomial base (· == choose_zero.zero)) :=
  {
    var := {
      value := trim_utilities.tail (· == choose_zero.zero) [choose_zero.zero, choose_e.e]
      is_reduced := by apply trim_utilities.tail.idempotent
    }
    induced_map f fx := eval_polynomial_ring_arrow f fx
    induced_map_is_valid := by
      intro target target_ring f fx
      rw [eval_polynomial_ring_arrow]
      simp [eval_polynomial]
      rw [f.map_e]
      simp
  }

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
  (k : Type u) [BEq k] [LawfulBEq k] [choose_zero k] (X : String) extends reduced_polynomial k (· == choose_zero.zero)

@[reducible, simp]
def silly_convert {k : Type u} [BEq k] [ring k] [LawfulBEq k] [choose_zero k] [ToString k] (x : reduced_polynomial k (· == choose_zero.zero)) (X : String) : polynomials_with_string_representation k X :=
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
def zero_polynomial : reduced_polynomial Int (· == 0) := {
  value := []
  is_reduced := by simp
}

@[simp]
def e_polynomial : reduced_polynomial Int (· == 0) := {
  value := [1]
  is_reduced := by simp [trim_utilities.tail]
}

@[simp]
def generator : reduced_polynomial Int (· == 0) := {
  value := [0, 1]
  is_reduced :=by simp_all [trim_utilities.tail]
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
def polynomial (k : Type u) [BEq k] [LawfulBEq k] [R : ring k] (X : String) := polynomials_with_string_representation k X


def var1 := "α"
def var2 := "β"

@[reducible]
def p1 : polynomial (polynomial Int var1) var2 := {
  value := [silly_convert generator var1]
  is_reduced := by
    simp [trim_utilities.tail, silly_convert]
    intro h
    have q := (ext_reverse_print Int var1) h
    simp at q
  }


@[reducible]
def p2 : polynomial (polynomial Int var1) var2 := {
  value := [silly_convert zero_polynomial var1, silly_convert e_polynomial var1]
  is_reduced := by
    exact
      trim_utilities.tail.head_reduced (fun x => x == ⟨0⟩) (silly_convert e_polynomial var1)
        (silly_convert zero_polynomial var1) [] rfl
}

def to_str := ("(" ++ (polynomial_has_string (polynomial Int var1) var2).toString · ++ ")")

@[reducible]
def mul_xy := (polynomials_with_string_representation_are_ring (polynomial Int var1) var2).mul

@[reducible]
def q := (p1 ⊹ p2)

def str := to_str q ++ " * " ++ to_str q ++ " * " ++ to_str q ++ " == " ++ to_str ( (q ⋆  q) ⋆ q )

#eval str

@[reducible]
def q3 :=  (q ⋆ q) ⋆ q

@[simp]
def to_print
  {base : Type v} [BEq base] [LawfulBEq base] [ring base] [ToString base] (X : String)
  : ring_hom₁ (reduced_polynomial base (· == choose_zero.zero)) (polynomials_with_string_representation base X)
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
  : ring_hom₁  (polynomials_with_string_representation base X) (reduced_polynomial base (· == choose_zero.zero))
  :=
  {
    original_function (x) := {
      value := x.value
      is_reduced := x.is_reduced
    }
    map_add := by
      intro a b
      exact polynomial_ring.ext_direct_iff.mpr rfl
    map_zero := by
      exact polynomial_ring.ext_direct_iff.mpr rfl
    map_e := by
      exact polynomial_ring.ext_direct_iff.mpr rfl
    map_mul := by
      intro a b
      exact polynomial_ring.ext_direct_iff.mpr rfl
  }

instance
  print_polynomial_algebra
  (base : Type) [ToString base] [ring base] [BEq base] [LawfulBEq base] (X : String)
  : free_algebra base (polynomials_with_string_representation base X) :=
  {
    var := {
      value := trim_utilities.tail (· == choose_zero.zero) [choose_zero.zero, choose_e.e]
      is_reduced := by apply trim_utilities.tail.idempotent
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

#eval eval_poly (a ⊹ b) (b ⋆ (b ⋆ b))

@[reducible]
def evaluated := eval_polynomial q (compose_ring_hom inclusion_base_to_free_algebra (to_print var2)) q3.value

#eval to_str q3 ++ " evaluated at " ++ var2 ++ " = " ++ to_str q ++ " is equal to " ++ to_str evaluated

@[reducible]
def mv (k : Type u) (n : Nat) : Type u :=
  match n with
  | 0 => k
  | n + 1 => List (mv k n)

@[simp]
def mv.from_list {k : Type u} {n : Nat} (a : List (mv k n)) : mv k (n + 1) := a
@[simp]
def mv.to_list  {k : Type u} {n : Nat} (a : mv k (n + 1)) : List (mv k n) := a

@[simp]
def mv.zero (k : Type u) [R : choose_zero k] (n : Nat) : mv k n :=
  match n with
  | 0 => R.zero
  | _ + 1 => []

-- def (· == ⟨0⟩) {k : Type u} [B : BEq k] [R : choose_zero k] {n : Nat} (a : mv k n) : Bool := by
--   match n with
--   | 0 => rw [mv] at a; apply a == R.zero
--   | _ + 1 => rw [mv] at a; apply a.isEmpty

@[reducible]
def mv.beq {k : Type u} [B : BEq k] {n : Nat} (a b : mv k n) : Bool := by
  match n with
  | 0 => apply B.beq a b
  | n + 1 =>
    let q : BEq (mv k n) := ⟨ mv.beq ⟩
    apply List.beq a b

instance mv.is_BEq (k : Type u) [B : BEq k] (n : Nat) : BEq (mv k n) where
  beq := mv.beq

@[reducible]
def mv.refl_beq  (k : Type u) [B : BEq k] [L : ReflBEq k] (n : Nat) (a : mv k n) : a == a := by
  match n with
  | 0 => apply L.rfl
  | q + 1 =>
    let prev := mv.refl_beq k q

    simp_all [mv]

    let list_eq : ReflBEq (mv k q) := {
      rfl := by
        apply mv.refl_beq k q
    }
    have temp : (mv.to_list a) == (mv.to_list a) := by
      exact ReflBEq.rfl

    apply temp

instance mv.is_ReflBEq (k : Type u) [B : BEq k] [L : ReflBEq k] (n : Nat) : ReflBEq (mv k n) where
  rfl := by apply mv.refl_beq

@[reducible]
def mv.eq_of_beq  (k : Type u) [B : BEq k] [L : LawfulBEq k] (n : Nat) (a b : mv k n) (h : a == b) : a = b := by
  match n with
  | 0 => apply L.eq_of_beq h
  | q + 1 =>
    let prev := mv.eq_of_beq k q

    simp_all [mv]

    let list_eq : LawfulBEq (mv k q) := {
      eq_of_beq := by
        apply mv.eq_of_beq k q
    }

    have temp : (mv.to_list a) == (mv.to_list b) := by
      apply h

    have temp_2 : (mv.to_list a) = (mv.to_list b) := by
      apply (List.lawfulBEq_iff.mpr list_eq).eq_of_beq temp

    apply temp_2

instance mv.is_LawfulBEq (k : Type u) [B : BEq k] [L : LawfulBEq k] (n : Nat) : LawfulBEq (mv k n) where
  eq_of_beq := by apply mv.eq_of_beq


def mv.beq_get (k : Type u) [B : BEq k] (n : Nat) (a b : mv k n) :
  (mv.is_BEq k n).beq a b = mv.beq a b := by
  rfl

def mv.e (k : Type u) [R : choose_e k] (n : Nat) : mv k n :=
  match n with
  | 0 => R.e
  | q + 1 => [mv.e k q]

instance mv.has_zero (k : Type u) (n : Nat) [Z : choose_zero k] [BEq k] : choose_zero (mv k n)  where
  zero := mv.zero k n

def mv.trim {k : Type u} [B : BEq k] [choose_zero k] {n : Nat} (a : mv k n) : mv k n :=
  match n with
  | 0 => a
  | _ + 1 => mv.from_list (trim_utilities.tail (· == ⟨0⟩) (a.map mv.trim))

structure mvr (k : Type u) [B : BEq k] [choose_zero k] (n : Nat)  where
  value : mv k n
  is_reduced : mv.trim value = value

@[simp]
theorem mv.zero.is_reduced  (k : Type u) (n : Nat) [Z : choose_zero k] [BEq k] :
  mv.trim (mv.zero k n) = (mv.zero k n) := by
  match n with
  | 0 => simp [trim]
  | q + 1 =>
    simp [trim]

def mvr.zero (k : Type u) (n : Nat) [Z : choose_zero k] [BEq k] : mvr k n := {
  value := mv.zero k n
  is_reduced := by apply mv.zero.is_reduced}

theorem mv.zero_is (k : Type u) [Z : choose_zero k] [BEq k] (n : Nat) : (mv.has_zero k n).zero = mv.zero k n := rfl

-- @[reducible]
instance mvr.has_zero (k : Type u) (n : Nat) [Z : choose_zero k] [BEq k] : choose_zero (mvr k n)  where
  zero := mvr.zero k n

theorem mvr.zero_is (k : Type u) [Z : choose_zero k] [BEq k] (n : Nat) : (mvr.has_zero k n).zero = mvr.zero k n := rfl

def mv.trim' {k : Type u} [B : BEq k] [choose_zero k] {n : Nat} (a : List (mv k n)) : List (mv k n) :=
  trim_utilities.tail ((· == ⟨0⟩)) (a.map mv.trim)

def mv.trim'' {k : Type u} [B : BEq k] [choose_zero k] {n : Nat} (a : mv k n) : mv k n :=
  match n with
  | 0 => a
  | _ + 1 =>
    match a with
    | [] => []
    | ha :: ta =>
      match mv.to_list (mv.trim ta) with
      | [] => if mv.trim ha == ⟨0⟩ then [] else mv.trim ha :: mv.to_list (mv.trim ta)
      | _ :: _ => mv.trim ha :: mv.to_list (mv.trim ta)

-- theorem mv.trim_is_mv.trim' {k : Type u} [B : BEq k] [choose_zero k] {n : Nat}  (a : mv k (n + 1))  :
--   mv.trim a = mv.from_list (mv.trim' ( mv.to_list a )) := by
--   rfl

theorem mv.trim_is_trim'' {k : Type u} [B : BEq k] [choose_zero k] {n : Nat}  (a : mv k n)  :
  mv.trim a = mv.trim'' a := by
  match n with
  | 0 => simp_all [mv.trim, mv.trim'']
  | q + 1 =>
    match a with
    | [] => simp_all [mv.trim, mv.trim'']
    | ha :: ta =>
      rw [mv.trim'']
      rw [mv.trim]
      rw [List.map]
      rw [trim_utilities.tail]
      split
      · case h_1 w ww =>
        rw [mv.trim]
        rw [ww]
        simp
      · case h_2 w ww =>
        split <;> simp_all
        · case h_1 z zz =>
          rw [mv.trim, mv.from_list] at zz
          contradiction
        · case h_2 z zz zzz zzzz =>
          congr

@[simp]
theorem mv.trim_scalar {k : Type u} [B : BEq k] [choose_zero k] (a : mv k 0)  :
  mv.trim a = a := by
  rfl


def mvr.beq
  (k : Type u) [B : BEq k] [choose_zero k] (n : Nat) (a b : mvr k n) := a.value == b.value

instance mvr.is_BEq (k : Type u) [B : BEq k] [choose_zero k] (n : Nat)
  : BEq (mvr k n) where
  beq := mvr.beq k n

def mvr.beq_iff (k : Type u) [B : BEq k] [choose_zero k] (n : Nat) (a b : mvr k n)
  : (a.value == b.value) ↔ a == b := by
  exact Bool.coe_iff_coe.mpr rfl


theorem mv.trim_1_is_trim {k : Type u} [B : BEq k] [L : LawfulBEq k] [Z: choose_zero k] (a : mv k 1)  :
  mv.trim a = (trim_utilities.tail (· == Z.zero) a) := by
  match a with
  | [] => simp_all [mv.trim]
  | ha :: ta =>
    have hi := mv.trim_1_is_trim ta
    have hi' := mv.trim_1_is_trim ta
    rw [mv.trim] at hi'
    rw [mv.trim, trim_utilities.tail]
    simp_all
    rw [trim_utilities.tail]
    split <;> split <;> simp_all
    · case h_1.isTrue w ww www =>
      apply eq_of_beq
      apply ReflBEq.rfl
    · case h_1.isFalse w ww www =>
      intro kkkk
      simp_all
      have refl_eq : (⟨0⟩ : mv k 0) == ⟨0⟩ := ReflBEq.rfl
      simp_all
      contradiction

def zero : mv Int 0 := by
  rw [mv]
  apply 0
def test_mv : mv Int 3 := [[[zero]], [], [[zero], [zero], [zero, zero], []], [], []]
#eval mv.trim test_mv


theorem recursive_reduction_is_stronger
  (k : Type u) [choose_zero k] [BEq k]  (n : Nat) (a : mv k (n + 1)) (h : mv.trim a = a)
  : trim_utilities.tail (· == ⟨0⟩) (mv.to_list a) = (mv.to_list a) := by
  rw [mv.to_list]
  rw [←h]
  rw [mv.trim]
  rw [mv.from_list]
  rw [trim_utilities.tail.idempotent]


theorem recursive_reduction_reduces_children
  (k : Type u) [choose_zero k] [BEq k]  (n : Nat) (a : mv k (n + 1)) (h : mv.trim a = a)
  : (∀ x ∈ (mv.to_list a), mv.trim x = x) := by
  intro x hx
  simp_all
  match a with
  | [] =>
    contradiction
  | ha :: ta =>
    rw [mv.trim] at h
    rw [List.mem_cons] at hx
    rw [List.map_cons] at h
    rw [trim_utilities.tail] at h
    rw [mv.from_list] at h
    cases hx
    · case inl q =>
      split at h
      · case h_1 w ww =>
        rw [q]
        split at h
        · case isTrue t =>
          contradiction
        · case isFalse t =>
          have wwww := List.cons.inj h
          apply wwww.left
      · case h_2 w ww =>
        rw [q]
        have wwww := (List.cons.inj h).left
        apply wwww
    · case inr q =>
      split at h
      · case h_1 w ww =>
        split at h
        · case isTrue t =>
          contradiction
        · case isFalse t =>
          have wwww := (List.cons.inj h).right
          rw [←wwww] at q
          contradiction
      · case h_2 w ww =>
        rcases List.cons.inj h with ⟨w1, w2⟩
        have hi := recursive_reduction_reduces_children k n ta w2
        apply hi
        rw [mv.to_list]
        apply q

theorem recursive_reduction_reduces_tail
  (k : Type u) [choose_zero k] [BEq k]  (n : Nat)
  (a : mv k (n + 1)) (h : mv.trim a = a)
  (ha : mv k n) (ta : List (mv k n))
  (a_structure : mv.to_list a = ha :: ta)
  : (mv.trim ta = (mv.from_list ta)) := by
  simp_all
  rw [mv.trim] at h
  rw [List.map] at h
  rw [mv.trim]
  rw [trim_utilities.tail] at h
  split at h
  · case h_1 w ww =>
    rw [ww]
    split at h
    · case isTrue g =>
      simp_all
    · case isFalse g =>
      simp_all
      apply (List.cons.inj h).right
  · case h_2 w ww =>
    apply (List.cons.inj h).right

theorem recursive_reduction_reduces_head
  (k : Type u) [choose_zero k] [BEq k]  (n : Nat)
  (a : mv k (n + 1)) (h : mv.trim a = a)
  (ha : mv k n) (ta : List (mv k n))
  (a_structure : mv.to_list a = ha :: ta)
  : (mv.trim ha = ha) := by
  have ha_mem : ha ∈ (ha :: ta) := by exact List.mem_cons_self
  apply recursive_reduction_reduces_children k n a h ha _
  rw [a_structure]
  apply ha_mem

def unwrap_mvr (k : Type u) [choose_zero k] [BEq k] (n : Nat)
  (a : mvr k (n + 1)) : List (mvr k n) := by
  rcases a with ⟨ av, hv ⟩
  match av with
  | [] => apply []
  | ha :: ta => apply {
      value := ha
      is_reduced := by
        apply recursive_reduction_reduces_children k n (ha :: ta) hv ha (List.mem_cons_self)
    } :: (
      unwrap_mvr k n {
        value := ta
        is_reduced := by apply recursive_reduction_reduces_tail k n (ha::ta) hv ha ta (by simp)
      }
    )
  termination_by a.value.length

theorem unwrap_preserves_elements (k : Type u) [choose_zero k] [BEq k] (n : Nat)
  (a : mvr k (n + 1)) :
  a.value = (unwrap_mvr k n a).map (mvr.value) := by
  rcases a with ⟨ av, hv ⟩
  match av with
  | [] => simp [unwrap_mvr]
  | ha :: ta =>
    rw [unwrap_mvr]
    simp
    congr 1

    have q := recursive_reduction_reduces_tail k n (ha :: ta) hv ha ta rfl
    rw [mv.from_list] at q

    have hi := unwrap_preserves_elements k n {
      value := ta
      is_reduced := by apply q
    }
    apply hi
  termination_by a.value.length


@[simp]
theorem trim_zero_mv (k : Type u) [choose_zero k] [BEq k] (n : Nat) :
  mv.trim (mv.zero k n) = mv.zero k n := by
  match n with
  | 0 => simp [mv.trim]
  | _ + 1 => simp[mv.zero, mv.trim]

theorem unwrap_is_reduced (k : Type u) [choose_zero k] [BEq k] (n : Nat)
  (a : mvr k (n + 1)) :
  trim_utilities.tail ((· == ⟨0⟩)) (unwrap_mvr k n a) = (unwrap_mvr k n a)
  := by
  match n with
  | 0 =>
    rcases a with ⟨ av, hv ⟩
    match av with
    | [] =>
      rw [unwrap_mvr]
      simp
    | ha :: ta =>
      have ta_reduced := recursive_reduction_reduces_tail k 0 (ha::ta) hv ha ta rfl
      have ha_reduced := recursive_reduction_reduces_head k 0 (ha :: ta) hv ha ta rfl
      have ta_reduced_weak := recursive_reduction_is_stronger k 0 ta ta_reduced
      have hi := unwrap_is_reduced k 0  {
        value := mv.from_list ta
        is_reduced := ta_reduced
      }
      rw[unwrap_mvr]
      simp_all
      rw [trim_utilities.tail]
      simp_all
      split <;> simp_all

      · case h_1 g gg =>
        have ggg := unwrap_preserves_elements k 0 {
          value := mv.from_list ta
          is_reduced := ta_reduced
        }
        simp at ggg
        rw [gg] at ggg
        simp_all
        rw [ggg] at hv
        simp [mv.trim] at hv
        apply hv
  | nn + 1 =>
    rcases a with ⟨ av, hv ⟩
    match av with
    | [] =>
      rw [unwrap_mvr]
      simp
    | ha :: ta =>
      rw [unwrap_mvr]
      have ta_reduced := recursive_reduction_reduces_tail k (nn + 1) (ha::ta) hv ha ta rfl
      have ha_reduced := recursive_reduction_reduces_head k (nn + 1) (ha :: ta) hv ha ta rfl
      have hi := unwrap_is_reduced k (nn + 1)  {
        value := mv.from_list ta
        is_reduced := ta_reduced
      }
      simp_all
      have ha_reduced_weak := recursive_reduction_is_stronger k nn ha ha_reduced
      have ta_reduced_weak := recursive_reduction_is_stronger k (nn + 1) ta ta_reduced

      rw [trim_utilities.tail]
      simp_all
      split <;> simp_all

      case h_1 g gg =>
        have ggg := unwrap_preserves_elements k (nn + 1) {
          value := mv.from_list ta
          is_reduced := ta_reduced
        }
        simp at ggg
        rw [gg] at ggg
        simp_all
        rw [ggg] at hv

        rw [mv.trim, List.map_cons, ha_reduced, List.map_nil, mv.from_list, trim_utilities.tail.singleton] at hv
        split at hv
        contradiction
        · case isFalse wwww =>
          exact eq_false_of_ne_true wwww
  termination_by a.value.length

def wrap_mvr (k : Type u) [choose_zero k] [BEq k] (n : Nat)
  (a : reduced_polynomial (mvr k n) ((· == ⟨0⟩)))
  : mv k (n + 1) := by
  rcases a with ⟨ va, ha ⟩
  match va with
  | [] => apply []
  | hva :: tva => apply hva.value :: wrap_mvr k n {
    value := tva
    is_reduced := by
      exact trim_utilities.tail.tail_reduced (· == ⟨0⟩) hva tva ha
  }



theorem wrap_is_nil_if (k : Type u) [choose_zero k] [BEq k] (n : Nat)
  (a : reduced_polynomial (mvr k n) ((· == ⟨0⟩)))
  (a' : List (mvr k n))
  (ha' : a.value = a')
  (h : wrap_mvr k n a = []) :
  a.value = [] := by
  rcases a with ⟨ va, ha ⟩
  rw [wrap_mvr] at h
  match va with
  | [] => rfl
  | hva :: tva => simp_all


def wrap_is_reduced (k : Type u) [choose_zero k] [BEq k] (n : Nat)
  (a : reduced_polynomial (mvr k n) ((· == ⟨0⟩))) :
  mv.trim (wrap_mvr k n a) = wrap_mvr k n a := by
  rcases a with ⟨ va, ha ⟩
  match n, va with
  | _, [] => simp_all [mv.trim, wrap_mvr]
  | 0, hva :: tva =>
    have hi := wrap_is_reduced k 0 {
      value := tva
      is_reduced := by exact
        trim_utilities.tail.tail_reduced (· == ⟨0⟩) hva tva ha
    }
    have tva_weak := recursive_reduction_is_stronger k 0 (wrap_mvr k 0 {
      value := tva
      is_reduced := by exact
        trim_utilities.tail.tail_reduced (· == ⟨0⟩) hva tva ha
    }) hi
    simp at tva_weak
    have ha' := ha
    rw [trim_utilities.tail] at ha'
    rw [wrap_mvr]
    simp
    rw [mv.trim_is_trim'']
    rw [mv.trim'']
    rw [hi]
    simp_all
    split
    · case h_1 w ww =>
      have tva_nil := wrap_is_nil_if k 0 {
        value := tva
        is_reduced := by exact
          trim_utilities.tail.tail_reduced (· == ⟨0⟩) hva tva ha
      } tva rfl ww
      simp_all
      assumption
    · case h_2 w ww =>
      rfl
  | n + 1, hva :: tva =>
    have hi := wrap_is_reduced k (n + 1) {
      value := tva
      is_reduced := by exact
        trim_utilities.tail.tail_reduced (· == ⟨0⟩) hva tva ha
    }
    have tva_weak := recursive_reduction_is_stronger k (n + 1) (wrap_mvr k (n + 1) {
      value := tva
      is_reduced := by exact
        trim_utilities.tail.tail_reduced (· == ⟨0⟩) hva tva ha
    }) hi
    have hva_weak := recursive_reduction_is_stronger k n hva.value hva.is_reduced
    simp at tva_weak hva_weak
    have ha' := ha
    rw [trim_utilities.tail] at ha'
    rw [wrap_mvr]
    simp
    rw [mv.trim_is_trim'']
    rw [mv.trim'']

    rw [hi]
    simp
    split
    · case h_1 w ww =>
      have tva_nil := wrap_is_nil_if k (n + 1) {
        value := tva
        is_reduced := by exact
          trim_utilities.tail.tail_reduced (· == ⟨0⟩) hva tva ha
      } tva rfl ww
      simp at tva_nil
      rw [ww, hva.is_reduced]
      simp_all
      assumption
    · case h_2 w ww =>
      rw [hva.is_reduced]


def unwrap_is_nil_if(k : Type u) [choose_zero k] [BEq k] (n : Nat)
  (a : mvr k (n + 1))
  (a' : List (mv k n))
  (ha' : a' = a.value)
  (h : unwrap_mvr k n a = [])
  : a.value = [] := by
  rcases a with ⟨va, ha⟩
  match va with
  | []  => simp
  | hva :: tva =>
    simp at ha'
    have hi := unwrap_is_nil_if k n {
      value := tva
      is_reduced := by
        apply recursive_reduction_reduces_tail k n (hva :: tva) ha hva tva rfl
    } tva rfl
    rw [unwrap_mvr] at h
    simp_all
  termination_by a'.length
  decreasing_by simp_all


def mvr_back (k : Type u) [choose_zero k] [BEq k] (n : Nat)
  (a : reduced_polynomial (mvr k n) ((· == ⟨0⟩)))
  : mvr k (n + 1) := {
    value := wrap_mvr k n a
    is_reduced := by apply wrap_is_reduced
  }

def mvr_forward
  (k : Type u) [choose_zero k] [BEq k] (n : Nat) (a : mvr k (n + 1)) :
  reduced_polynomial (mvr k n) ((· == ⟨0⟩)) :=
  {
    value := unwrap_mvr k n a
    is_reduced := by apply unwrap_is_reduced
  }

theorem mvr_forward_mvr_back
  (k : Type u) [choose_zero k] [BEq k] (n : Nat)
  (a : mvr k (n + 1))
  (a' : List (mv k n))
  (h : a' = a.value)
  :
  (mvr_back k n (mvr_forward k n a)) = a := by
  rcases a with ⟨va, ha⟩
  match va with
  | [] =>
    rw [mvr_back, mvr_forward]; simp; rw [wrap_mvr]
    simp; split <;> simp_all [unwrap_mvr]
  | hva :: tva =>
    have hi_tva := mvr_forward_mvr_back k n {
      value := tva
      is_reduced := by apply recursive_reduction_reduces_tail k n (hva::tva) ha hva tva (by simp)
    }
    rw [mvr_back, mvr_forward]
    rw [mvr_back, mvr_forward] at hi_tva
    simp_all
    rw [wrap_mvr]
    rw [wrap_mvr] at hi_tva
    simp_all
    split <;> simp_all
    · case h_1 m mm mmm mmmm =>
      have something_is_nil := unwrap_is_nil_if k n {
        value := hva :: tva
        is_reduced := ha
      } (hva :: tva) rfl mmmm
      contradiction
    · case h_2 m mm mmm mmmm w ww www =>
      simp_all
      rw [unwrap_mvr] at www
      simp at www
      rw [List.cons.injEq]
      and_intros
      have adsf := www.left
      exact
        (Eq.to_iff
              (congrFun (congrArg Eq (congrArg mvr.value (id (Eq.symm adsf))))
                hva)).mpr
          rfl
      have dfad := www.right
      symm at dfad
      simp_all
      split at hi_tva
      symm at hi_tva
      simp_all; rw [wrap_mvr]
      simp_all; rw [wrap_mvr]
      simpa
  termination_by a'.length
  decreasing_by simp_all

instance (k : Type u) [ring k] [BEq k] [LawfulBEq k] : ring (mv k 0) := by
  rw [mv]
  assumption

theorem mvr_back_mvr_forward (k : Type u) [choose_zero k] [BEq k] (n : Nat)
  (a : reduced_polynomial (mvr k n) ((· == ⟨0⟩)))
  (a' : List (mvr k n))
  (h : a' = a.value) :
  (mvr_forward k n (mvr_back k n a)) = a := by
  rcases a with ⟨va, ha⟩
  match va with
  | [] =>
    rw [mvr_back, mvr_forward]; simp; rw [unwrap_mvr]
    simp; split <;> simp_all [wrap_mvr]
  | hva :: tva =>
    have hi_tva := mvr_back_mvr_forward k n {
      value := tva
      is_reduced := by exact
        trim_utilities.tail.tail_reduced (· == ⟨0⟩) hva tva ha
    } tva rfl

    rw [mvr_back, mvr_forward]
    rw [mvr_back, mvr_forward] at hi_tva
    simp_all
    rw [unwrap_mvr]
    rw [unwrap_mvr] at hi_tva
    simp_all
    split
    · case h_1 m1 m2 m3 m4 m5 m6 =>
      simp_all
      rw [wrap_mvr] at m5
      simp at m5
    · case h_2 m1 m2 m3 m4 m5 m6 =>
      simp_all
      rw [wrap_mvr] at m5
      simp at m5
      rw [List.cons.injEq] at m5
      have q2 := m5.left
      have q3 := m5.right
      and_intros
      symm at q2
      simp [q2]
      symm at q3
      simp [q3]
      split at hi_tva <;> simp_all
      rw [unwrap_mvr]
      rw [unwrap_mvr]
      simp_all
  termination_by a'.length
  decreasing_by simp_all


def mv_rfl (k : Type u) [BEq k] [L : LawfulBEq k] (n : Nat) (a : mv k n) : a == a := by
  match n with
  | 0 =>
    rw [mv] at a
    apply L.rfl
  | q + 1 =>
    rw [mv.beq_get, mv.beq]
    let rfl_prev : ReflBEq (mv k q) := { rfl := by apply mv_rfl k q }
    have rfl_next := List.reflBEq_iff.mpr rfl_prev
    apply rfl_next.rfl

def mv_eq_of_beq (k : Type u) [BEq k] [L : LawfulBEq k] (n : Nat) (a b : mv k n) (h : a == b) : a = b := by
  match n with
  | 0 =>
    rw [mv] at a b
    apply L.eq_of_beq
    apply h
  | q + 1 =>
    rw [mv.beq_get, mv.beq] at h
    let rfl_prev : LawfulBEq (mv k q) := {
      rfl := by apply mv_rfl k q
      eq_of_beq := by apply mv_eq_of_beq
    }
    have rfl_next := List.lawfulBEq_iff.mpr rfl_prev
    apply rfl_next.eq_of_beq
    apply h

instance mv_lawful (k : Type u) [BEq k] [LawfulBEq k] (n : Nat) : LawfulBEq (mv k n) where
  rfl := by
    intro a
    apply mv_rfl
  eq_of_beq := by
    intro a b
    apply mv_eq_of_beq

@[reducible]
def ring_structure_0' (k : Type u) [R : ring k] [BEq k] [LawfulBEq k] : ring (mv k 0) := by
    rw [mv]
    apply R

-- set_option diagnostics true

@[reducible]
def transfer_ring
  (k : Type u) (k_z : k) (k_e : k) (R : ring_with_fixed_identities k k_z k_e)
  (t : Type v) (t_z : t) (t_e : t)
  (forward : t → k)
  (back : k → t)
  (hbf : ∀ x : t, back (forward x) = x)
  (hfb : ∀ x : k, forward (back x) = x)
  (hz : back k_z = t_z)
  (he : back k_e = t_e)
  : ring_with_fixed_identities t (t_z) (t_e) := {
  zero := back R.zero
  e := back R.e
  add x y := back (R.add (forward x) (forward y))
  add_zero_left := by
    simp_all
  add_zero_right := by
    simp_all
  add_is_assoc := by
    intro a b c
    simp_all
    rw [R.add_is_assoc]
  add_is_comm := by
    intro a b;
    rw [R.add_is_comm]
  mul x y := back (R.mul (forward x) (forward y))
  mul_e_right := by simp_all
  mul_e_left := by simp_all
  mul_is_assoc := by
    intro a b c
    simp_all
    rw [R.mul_is_assoc]
  mul_is_comm := by
    intro a b;
    rw [R.mul_is_comm]
  add_inverse x := back (R.add_inverse (forward x))
  add_inverse_is_inverse := by
    intro a
    simp
    rw [hfb, R.add_inverse_is_inverse]
  mul_is_linear_left := by
    intro a b c;
    simp_all
    rw [R.mul_is_linear_left]
  mul_is_linear_right := by
    intro a b c;
    simp_all
    rw [R.mul_is_linear_right]
  kz_is_zero := by
    rw [←hz]
    congr
    apply R.kz_is_zero
  ke_is_e := by
    rw [←he]
    congr
    apply R.ke_is_e
}

-- set_option diagnostics false

def k_to_mv (k : Type u) [BEq k] [LawfulBEq k] (x : k) : mv k 0 := x
def mv_to_k (k : Type u) [BEq k] [LawfulBEq k] (x : mv k 0) : k := x

@[reducible]
def ring_structure_0 (k : Type u) [R : ring k] [BEq k] [LawfulBEq k] :
  ring_with_fixed_identities (mv k 0) (k_to_mv k R.zero) (k_to_mv k R.e) := by
  apply transfer_ring k R.zero R.e (ring_has_fixed_identities k) (mv k 0) _ _ (
    k_to_mv k
  ) (
    mv_to_k k
  ) (
    by intro x; rfl
  ) (
    by intro x; rfl
  )
  simp[mv_to_k, k_to_mv]
  simp[mv_to_k, k_to_mv]

def mvr_to_mv_0 (k : Type u) [R : ring k] [BEq k] [LawfulBEq k] (x : mvr k 0) : mv k 0 := x.value
def mv_to_mvr_0 (k : Type u) [R : ring k] [BEq k] [LawfulBEq k] (x : mv k 0) : mvr k 0 := {
  value := x
  is_reduced := by rw [mv.trim]
}

@[reducible]
def ring_structure_0r (k : Type u) [R : ring k] [BEq k] [LawfulBEq k] :
  ring_with_fixed_identities (mvr k 0) (mv_to_mvr_0 k (mv.zero k 0)) (mv_to_mvr_0 k (mv.e k 0)):= by
  apply transfer_ring (mv k 0) (ring_structure_0 k).zero (ring_structure_0 k).e (ring_structure_0 k) (mvr k 0) _ _ (
    mvr_to_mv_0 k
  ) (
    mv_to_mvr_0 k
  ) (
    by intro x; rfl
  ) (
    by intro x; rfl
  )
  simp[mv_to_mvr_0, mv.zero]
  rfl
  simp[mv_to_mvr_0, mv.e]
  rfl




def mvr_rfl (k : Type u) [BEq k] [L : LawfulBEq k] [choose_zero k] (n : Nat) (a : mvr k n) : a == a := by
  apply (mvr.beq_iff k n a a).mp
  exact mv_rfl k n a.value

theorem mv.trim_idempotent_0 (k : Type u) [Z : choose_zero k] [BEq k] (a : mv k 0) :
  mv.trim (mv.trim a) = mv.trim a  := by
  rw [mv.trim]

theorem mv.trim_idempotent_1 (k : Type u) (q : Nat) [Z : choose_zero k] [BEq k] [LawfulBEq k] (a : mv k (q + 1)) :
  mv.trim (mv.trim a) = mv.trim a := by
  match q, a with
  | 0, [] =>
    simp_all [mv.trim]
  | 0, ta :: ha =>
    have hi_n := mv.trim_idempotent_0 k ta
    have hi_a := mv.trim_idempotent_1 k 0 ha
    have hi_n' := mv.trim_idempotent_0 k ta
    have hi_a' := mv.trim_idempotent_1 k 0 ha
    repeat rw [mv.trim]
    have help := mv.trim_scalar ta
    have help_2 := mv.trim_1_is_trim ha
    have help_2' := mv.trim_1_is_trim ha
    have help_3' := mv.trim_1_is_trim (trim_utilities.tail (· == Z.zero) ha)
    repeat rw [mv.trim] at help_2' help_3'

    simp_all

    simp_all [trim_utilities.tail]

    split <;> simp_all
    split <;> simp_all

    rw [trim_utilities.tail]
    split
    · case h_1 w1 w2 w3 w4 =>
      rw [help_3', trim_utilities.tail.idempotent] at w4
      contradiction
    · case h_2 w1 w2 w3 w4 =>
      rw [help_3', trim_utilities.tail.idempotent] at w4
      simp_all
      apply trim_utilities.tail.idempotent
  | _, [] => simp_all [mv.trim]
  | q' + 1, ta :: ha =>
    have hi_n := mv.trim_idempotent_1 k q' ta
    have hi_a := mv.trim_idempotent_1 k (q' + 1) ha
    have hi_n' := mv.trim_idempotent_1 k q' ta
    have hi_a' := mv.trim_idempotent_1 k (q' + 1) ha
    repeat rw [mv.trim]
    repeat rw [mv.trim] at hi_a' hi_n'

    simp
    simp_all [trim_utilities.tail]
    split
    split
    simp_all
    simp_all
    · case h_2 w ww =>
      simp_all [trim_utilities.tail]
  termination_by (q, a.length)


theorem mv.trim_idempotent
  (k : Type u) (q : Nat) [Z : choose_zero k] [BEq k] [LawfulBEq k]
  (a : mv k q) : mv.trim (mv.trim a) = mv.trim a := by
  match q with
  | 0 => exact mv.trim_idempotent_0 k a
  | _ + 1 => (expose_names; exact mv.trim_idempotent_1 k n a)


def mvr_e (k : Type u) (n : Nat)  [Z : choose_zero k] [Z : choose_e k] [BEq k] [LawfulBEq k] : mvr k n := {
    value := mv.trim (mv.e k n)
    is_reduced := by apply mv.trim_idempotent
  }

theorem mvr_ext
  (k : Type u) [BEq k] [choose_zero k]
  (n : Nat)
  (a b : mvr k n)
  (h : a.value = b.value)
  : a = b := by
  rcases a with ⟨va,ha⟩
  rcases b with ⟨vb,hb⟩
  simp_all


theorem mvr.eq_iff
  (k : Type u) [BEq k] [choose_zero k]
  (n : Nat)
  (a b : mvr k n) :
  a.value = b.value ↔ a = b := by
  rcases a with ⟨va,ha⟩
  rcases b with ⟨vb,hb⟩
  simp_all

theorem mvr_ext_inv
  (k : Type u) [BEq k] [choose_zero k]
  (n : Nat)
  (a b : mvr k n)
  (h : a = b)
  : a.value = b.value := by
  rcases a with ⟨va,ha⟩
  rcases b with ⟨vb,hb⟩
  simp_all

def mvr_eq_of_beq (k : Type u) [choose_zero k] [BEq k] [L : LawfulBEq k] (n : Nat) (a b : mvr k n) (h : a == b) : a = b := by
  let www := (mvr.beq_iff k n a b).mpr h
  have h : a.value = b.value := by
    exact beq_iff_eq.mp h
  apply mvr_ext
  apply h

instance mvr_lawful (k : Type u) [choose_zero k] [BEq k] [LawfulBEq k] (n : Nat) : LawfulBEq (mvr k n) where
  rfl := by
    intro a
    apply mv_rfl
  eq_of_beq := by
    intro a b
    apply mvr_eq_of_beq


-- def ring_structure_0r
-- set_option trace.Meta.synthInstance true


theorem reduce_mvr_e_singleton (k : Type u) [R : ring k] [BEq k] [LawfulBEq k] :
  (↓ₜfun x => x == ⟨0⟩) ((↓ₜ(· == ⟨0⟩)) [mvr_e k 0]) = (↓ₜ(· == ⟨0⟩)) [mvr_e k 0] := by
  simp [mvr_e, mv.e]
  rw [apply_ite (trim_utilities.tail _)]
  simp_all

-- @[reducible]
-- def mvr. (k : Type u) (r : ring k) [BEq k] [LawfulBEq k] (q : Nat) : mvr k (q + 1) := ⟨0⟩

-- @[reducible]
-- def ring_structure (k : Type u)

-- (kz : k) (ke : k) [Rk : ring_with_fixed_identities k kz ke]

-- [BEq k] [LawfulBEq k] (n : Nat)
--   :
--   ring_with_fixed_identities
--   (mvr k (n + 1))
--   (mvr.has_zero k (n + 1)).zero
--   (mvr_e k (n + 1))
--   := by
--   match n with
--   | 0 =>
--     let R' : ring_with_fixed_identities (mvr k 0) (mvr.zero k 0) (mvr_e k 0) := ring_structure_0r k
--     let RX1 := polynomial_ring (mvr k 0)
--     have QQ : ring_with_fixed_identities (reduced_polynomial (mvr k 0) fun x => x == ⟨0⟩) { value := [], is_reduced := by simp } { value := (↓ₜ(· == ⟨0⟩)) [mvr_e k 0], is_reduced := by exact reduce_mvr_e_singleton k  }
--     := {
--       zero := { value := [], is_reduced := by simp }
--       add := RX1.add
--       add_zero_left := RX1.add_zero_left
--       add_zero_right := RX1.add_zero_right
--       add_is_assoc := RX1.add_is_assoc
--       add_is_comm := RX1.add_is_comm
--       e := { value := trim_utilities.tail (· == ⟨0⟩) [⟨1⟩], is_reduced := by exact trim_utilities.tail.idempotent (fun x => x == ⟨0⟩) [⟨1⟩] }
--       mul := RX1.mul
--       mul_e_right := RX1.mul_e_right
--       mul_e_left := RX1.mul_e_left
--       mul_is_assoc := RX1.mul_is_assoc
--       mul_is_comm := RX1.mul_is_comm
--       add_inverse := RX1.add_inverse
--       add_inverse_is_inverse := RX1.add_inverse_is_inverse
--       mul_is_linear_left := RX1.mul_is_linear_left
--       mul_is_linear_right := RX1.mul_is_linear_right
--       kz_is_zero := by rfl
--       ke_is_e := by rfl
--     }
--     rw [] at QQ
--     apply transfer_ring
--       (reduced_polynomial (mvr k 0) (· == ⟨0⟩))
--       {
--         value := []
--         is_reduced := by exact trim_utilities.tail.nil fun x => x == mvr.zero k 0
--       }
--       {
--       value := trim_utilities.tail ((· == ⟨0⟩)) [mvr_e k 0]
--       is_reduced := by
--         simp_all [mvr_e, mv.e, trim_utilities.tail, mv.trim]
--         rw [apply_ite (trim_utilities.tail (· == ⟨0⟩)), trim_utilities.tail, trim_utilities.tail, trim_utilities.tail]
--         simp_all
--         split <;> rfl
--     } QQ _ _ _ (mvr_forward k 0) (mvr_back k 0)

--     exact fun x => mvr_forward_mvr_back k 0 x x.value rfl
--     exact fun x => mvr_back_mvr_forward k 0 x x.value rfl

--     · case hz =>
--       rw [mvr_back]
--       simp [mvr.zero_is, mvr.zero, mv.zero]
--       rw [wrap_mvr]

--     · case he ww =>
--       simp_all [mvr_e, mv.e, mvr_back]
--       split
--       · case isTrue w =>
--         rw [wrap_mvr]
--         simp_all [mv.trim]
--         have ss := eq_of_beq w
--         have s := (mvr.eq_iff k 0 _ _).mpr ss
--         simp at s
--         apply s
--       · case isFalse w =>
--         rw [Bool.not_eq_true] at w
--         have temp := not_eq_of_beq_eq_false w
--         simp_all [wrap_mvr, mv.trim]
--         -- rw [Bool.eq_false_iff]
--         intro s
--         apply temp
--         apply (mvr.eq_iff k 0 _ _).mp
--         apply s
--   | q + 1 =>

--     let Ri : ring_with_fixed_identities (mvr k (q + 1)) (mvr.zero k (q + 1)) (mvr_e k (q + 1)) := ring_structure k kz ke q

--     -- let R' : ring_with_fixed_identities (mvr k (q + 1)) (z k Rk.toring q) (mvr_e k (q + 1)) := {
--     --   zero := (z k Rk.toring q)
--     --   add_zero_left := by
--     --     intro a
--     --     let h := Ri.kz_is_zero
--     --     rw [h]
--     --     rw [mvr.zero_is]

--     --   add_zero_right := sorry
--     --   add_is_assoc := sorry
--     --   add_is_comm := sorry
--     --   add_inverse := sorry
--     --   add_inverse_is_inverse := sorry
--     --   mul_is_linear_left := sorry
--     --   mul_is_linear_right := sorry
--     -- }

--     let R_original := polynomial_ring (mvr k (q + 1))
--     -- HERE I WANT TO PUT R_original INTO R
--     -- let sss := @choose_zero.zero (mvr k (q + 1)) ({ value := [], is_reduced := sorry }).tochoose_zero : mvr k (q + 1)
--     let R : ring (reduced_polynomial (mvr k (q + 1)) (· == (mvr.has_zero k (q + 1)).zero)) := R_original

--     let QQ :
--       ring_with_fixed_identities
--       (reduced_polynomial (mvr k (q + 1)) (· == ⟨0⟩))
--       { value := [], is_reduced := by exact trim_utilities.tail.nil (· == ⟨0⟩) }
--       { value := (↓ₜ(· == ⟨0⟩)) [mvr_e k (q + 1)], is_reduced := by exact trim_utilities.tail.idempotent (· == ⟨0⟩) [mvr_e k (q + 1)] } :=
--     {
--       zero := R.zero
--       add := R.add
--       add_zero_left := R.add_zero_left
--       add_zero_right := R.add_zero_right
--       add_is_assoc := R.add_is_assoc
--       add_is_comm := R.add_is_comm
--       e := R.e
--       mul := R.mul
--       mul_e_right := R.mul_e_right
--       mul_e_left := R.mul_e_left
--       mul_is_assoc := R.mul_is_assoc
--       mul_is_comm := R.mul_is_comm
--       add_inverse := R.add_inverse
--       add_inverse_is_inverse := R.add_inverse_is_inverse
--       mul_is_linear_left := R.mul_is_linear_left
--       mul_is_linear_right := R.mul_is_linear_right
--       kz_is_zero := sorry
--       ke_is_e := sorry
--     }


--     apply transfer_ring
--       (reduced_polynomial (mvr k (q + 1)) (· == ⟨0⟩))
--       {
--         value := []
--         is_reduced := by exact trim_utilities.tail.nil fun x => x == mvr.zero k (q + 1)
--       }
--       {
--         value := trim_utilities.tail (· == ⟨0⟩) [mvr_e k (q + 1)]
--         is_reduced := by
--           exact trim_utilities.tail.idempotent _ [mvr_e k (q + 1)]
--       }
--       QQ
--       _ _ _
--       (mvr_forward k (q + 1)) (mvr_back k (q + 1))

--     exact fun x => mvr_forward_mvr_back k (q + 1) x x.value rfl
--     exact fun x => mvr_back_mvr_forward k (q + 1) x x.value rfl

--     · case hz =>
--       rw [mvr_back]
--       simp
--       rw [wrap_mvr]

--     · case he ww =>
--       simp_all [mvr_e, mv.e, mvr_back]
--       split
--       · case isTrue w =>
--         rw [wrap_mvr]
--         simp_all [mv.trim]
--         have ss := eq_of_beq w
--         have s := (mvr.eq_iff k (q + 1) _ _).mpr ss
--         simp at s
--         apply s
--       · case isFalse w =>
--         rw [Bool.not_eq_true] at w
--         have temp := not_eq_of_beq_eq_false w
--         simp_all [wrap_mvr, mv.trim]
--         -- rw [Bool.eq_false_iff]
--         intro s
--         apply w
--         split <;> (simp_all; apply w; rfl)

end polynomial_ring
