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

-- def mul_poly'
--   {k : Type u} [Z : choose_zero k] [A : add k] [M : mul k]
--   (a : List k) (b : List k) : List k
--   :=
--   match b with
--   | [] => []
--   | x :: b' =>
--     add_poly
--       (action.right a x)
--       (shift (mul_poly a b'))


-- @[simp]
-- def trim_opposite {k : Type u} [algebra.choose_zero k] [BEq k] (a : List k) : List k :=
--   (trim_utilities.head (. == algebra.choose_zero.zero) a)

-- prefix:100 "↓" => trim_utilities.tail (· == choose_zero.zero)


-- def respect_trim {k : Type u}  [BEq k] [LawfulBEq k] [Z : choose_zero k] (f : List k → List k)
--   := ∀ a, trim_utilities.tail (· == choose_zero.zero) (f a) = trim_utilities.tail (· == choose_zero.zero) (f (trim_utilities.tail (· == choose_zero.zero) a))

-- def respect_trim_2 {k : Type u}  [BEq k] [LawfulBEq k] [Z : choose_zero k] (f : List k → List k → List k)
--   := ∀ a, ∀ b, trim_utilities.tail (· == choose_zero.zero) (f a b) = trim_utilities.tail (· == choose_zero.zero) (f (trim_utilities.tail (· == choose_zero.zero) a) (trim_utilities.tail (· == choose_zero.zero) b))

-- def respect_trim_internal {k : Type u}  [BEq k] [LawfulBEq k] [Z : choose_zero k] (f : List k → List k)
--   := ∀ a, trim_opposite (f a) = trim_opposite (f (trim_opposite a))

-- theorem append_respects_trim_internal {k : Type u} [BEq k] [LawfulBEq k] [Z : choose_zero k] (a : List k) (x : k)
--   : trim_opposite (a ++ [x]) = trim_opposite ((trim_opposite a) ++ [x])
--   := by
--   simp
--   rw [trim_utilities.]
--   match a with
--   | [] => simp
--   | x :: a' =>
--     simp
--     split
--     · case h_1 hx =>
--       rw [beq_iff_eq] at hx
--       rw [hx]
--       rw [trim_zero_glue_generator_internal]
--       rw [append_respects_trim_internal]
--     · case isFalse hx =>
--       simp


theorem add_poly.cons {k : Type u} [BEq k] [LawfulBEq k] [A : add k]
  (xa xb : k) (a b : List k) :
  (A.add xa xb) :: (add_poly a b)
  = (add_poly (xa :: a) (xb :: b)) := by
  rw [add_poly]



-- theorem cons_respects_trim {k : Type u} [BEq k] [LawfulBEq k] [choose_zero k] (x : k) (a : List k)
--   : trim_utilities.tail (· == choose_zero.zero) (x :: a) = trim_utilities.tail (· == choose_zero.zero) (x :: trim_utilities.tail (· == choose_zero.zero) a)
--   := by

--   simp [trim_utilities.tail, trim_utilities.tail.idempotent]


-- theorem trim_zero_all
--   {k : Type u} [BEq k] [LawfulBEq k] [Z : choose_zero k] (a : List k) (ha : a.all (fun x ↦ (x == Z.zero)))
--   : trim_utilities.tail (· == choose_zero.zero) a = []
--   := by
--   match a with
--   | [] => simp
--   | xa :: a' =>
--     rw [cons_respects_trim]
--     have ha' : a'.all (fun x ↦ (x == Z.zero)) := by
--       rw [List.all_cons] at ha
--       simp_all
--       apply ha.right
--     conv =>
--       arg 2
--       arg 1
--       rw [trim_zero_all a' ha']
--     have hxa : xa == Z.zero := by
--       rw [List.all_cons] at ha
--       simp_all
--     rw [eq_of_beq hxa]
--     simp

-- theorem trim_internal_helper_not_all_zero
--   {k : Type u} [BEq k] [LawfulBEq k] [Z : choose_zero k]
--   (x : k) (a : List k)
--   (ha : ¬a.all (fun x ↦ x == Z.zero))
--   : trim_leading_zeros_internal (a ++ [x]) = trim_leading_zeros_internal a ++ [x] := by
--   simp at ha
--   match a with
--   | [] =>
--     simp_all
--   | xa :: a' =>
--     conv =>
--       lhs
--       rw [List.cons_append]
--       rw [trim_leading_zeros_internal]
--     if xa = Z.zero then
--       simp_all [trim_internal_helper_not_all_zero]
--     else
--       simp_all [trim_leading_zeros_internal]


-- theorem trim_internal_helper_all_zero {k : Type u} [BEq k] [LawfulBEq k] [Z : choose_zero k] (x : k) (a : List k)
--   (ha : a.all (fun x ↦ x == Z.zero))
--   : trim_leading_zeros_internal (a ++ [x]) = trim_leading_zeros_internal [x] := by
--   rw [trim_leading_zeros_internal]
--   rw [trim_leading_zeros_internal]
--   if h : x == Z.zero then
--     rw [trim_leading_zeros_internal.eq_def]
--     split
--     · case h_1 =>
--       simp_all
--     · case h_2 q1 q2 q3 q4 =>
--       rw [h]
--       have hq := List.cons_eq_append_iff.mp q4.symm
--       rcases hq with h1 | hq2
--       simp_all [trim_leading_zeros_internal]
--       rcases hq2 with ⟨ a', ⟨ ha'_l, ha'_r⟩ ⟩
--       have ha_f := List.all_eq_true.mp ha
--       have q2_is_zero : q2 == Z.zero := by
--         apply ha_f
--         rw [ha'_l]
--         exact List.mem_cons_self
--       rw [q2_is_zero]
--       rw [ha'_r]
--       rw [trim_internal_helper_all_zero]
--       simp_all [trim_leading_zeros_internal]
--       simp at ha
--       simp
--       intro element
--       intro element_in_a'
--       have a'_sub_a' : a' ⊆ a' := by exact List.subset_def.mpr fun {a} a_1 => a_1
--       have tmp := List.subset_cons_of_subset q2 a'_sub_a'
--       rw [←ha'_l] at tmp
--       apply ha
--       simp_all
--   else
--     rw [trim_leading_zeros_internal.eq_def]
--     split
--     · case h_1 =>
--       simp_all
--     · case h_2 q1 q2 q3 q4 =>
--       simp [h]
--       have hq := List.cons_eq_append_iff.mp q4.symm
--       rcases hq with h1 | hq2
--       simp_all [trim_leading_zeros_internal]
--       rcases hq2 with ⟨ a', ⟨ ha'_l, ha'_r⟩ ⟩
--       have ha_f := List.all_eq_true.mp ha
--       have q2_is_zero : q2 == Z.zero := by
--         apply ha_f
--         rw [ha'_l]
--         exact List.mem_cons_self
--       rw [q2_is_zero]
--       rw [ha'_r]
--       rw [trim_internal_helper_all_zero]
--       simp_all [trim_leading_zeros_internal]
--       simp at ha
--       simp
--       intro element
--       intro element_in_a'
--       have a'_sub_a' : a' ⊆ a' := by exact List.subset_def.mpr fun {a} a_1 => a_1
--       have tmp := List.subset_cons_of_subset q2 a'_sub_a'
--       rw [←ha'_l] at tmp
--       apply ha
--       simp_all
--   termination_by a

-- theorem trim_helper_all_zero {k : Type u} [BEq k] [LawfulBEq k] [Z : choose_zero k] (x : k) (a : List k)
--   (ha : a.all (· == choose_zero.zero))
--   : trim_utilities.tail (· == choose_zero.zero) (x :: a) = trim_utilities.tail (· == choose_zero.zero) [x] := by
--   apply trim_utilities.tail.nil_of_all_except_first (· == choose_zero.zero) x a ha


-- theorem trim_helper_not_all_zero {k : Type u} [BEq k] [LawfulBEq k] [Z : choose_zero k] (x : k) (a : List k)
--   (ha : ¬ a.all (fun x ↦ x == Z.zero))
--   : trim_utilities.tail (· == choose_zero.zero) (x :: a) = x :: trim_utilities.tail (· == choose_zero.zero) a := by
--   apply trim_utilities.tail.ignore_head (· == Z.zero) x a ha

-- @[simp]
-- theorem no_leading_zero_after_trimming_leading_zero {k : Type u} [BEq k] [LawfulBEq k]
--   [Z : choose_zero k]
--   (a : List k) (b :List k) (c : k) (h : trim_utilities.tail (· == choose_zero.zero) a = c :: b) :
--   ¬ c = Z.zero := by
--   simp_all
--   apply trim_utilities.
--   rw [trim_leading_zeros_internal.eq_def] at h
--   split at h
--   simp_all
--   split at h
--   apply no_leading_zero_after_trimming_leading_zero
--   assumption
--   simp_all

-- theorem reduced_iff_non_zero_tail {k : Type u} [BEq k] [LawfulBEq k] [Z : choose_zero k] (s : k) (a : List k)
--   :  trim_utilities.tail (· == choose_zero.zero) (a ++ [s]) = (a ++ [s]) ↔ ! (s == Z.zero) := by
--   simp
--   constructor
--   · case mp =>
--     intro h
--     have hh := trim_utilities.tail.if_reduced (· == Z.zero) s a h
--     simp_all
--   · case mpr =>
--     intro s_not_zero
--     apply trim_utilities.tail.reduced_if
--     simp_all


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

-- theorem add_poly.cons {k : Type u} [A : additive_monoid k] (x y : k) (a b : List k) :
--   (x ⊹ y) :: (add_poly a b) = add_poly (x :: a) (y :: b) := by
--   rw [add_poly]

-- set_option diagnostics true
-- set_option trace.profiler true
-- set_option maxHeartbeats 800000

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


def mv_polynomial (k : Type u) (n : Nat) : Type u :=
  match n with
  | 0 => k
  | n + 1 => List (mv_polynomial k n)

def mv_polynomial.from_list {k : Type u} {n : Nat} (a : List (mv_polynomial k n)) : mv_polynomial k (n + 1) := a

def mv_polynomial.zero (k : Type u) [R : choose_zero k] (n : Nat) : mv_polynomial k n :=
  match n with
  | 0 => R.zero
  | _ + 1 => []

def mv_polynomial.is_zero {k : Type u} [B : BEq k] [R : choose_zero k] {n : Nat} (a : mv_polynomial k n) : Bool := by
  match n with
  | 0 => rw [mv_polynomial] at a; apply a == R.zero
  | _ + 1 => rw [mv_polynomial] at a; apply a.isEmpty

def mv_polynomial.beq {k : Type u} [B : BEq k] {n : Nat} (a b : mv_polynomial k n) : Bool := by
  match n with
  | 0 => apply B.beq a b
  | n + 1 =>
    let q : BEq (mv_polynomial k n) := ⟨ mv_polynomial.beq ⟩
    apply List.beq a b

instance mv_polynomial.BEq (k : Type u) [B : BEq k] (n : Nat) : BEq (mv_polynomial k n) where
  beq := mv_polynomial.beq


def reduce_mv_polynomial {k : Type u} [B : BEq k] [choose_zero k] {n : Nat} (a : mv_polynomial k n) : mv_polynomial k n :=
  match n with
  | 0 => a
  | _ + 1 => mv_polynomial.from_list (trim_utilities.tail (mv_polynomial.is_zero) (a.map reduce_mv_polynomial))

structure reduced_mv_polynomial (k : Type u) [B : BEq k] [choose_zero k] (n : Nat)  where
  value : mv_polynomial k n
  is_reduced : reduce_mv_polynomial value = value

def reduced_mv_polynomial.is_zero
  {k : Type u} [B : BEq k] [R : choose_zero k] {n : Nat}
  (a : reduced_mv_polynomial k n) : Bool :=
  mv_polynomial.is_zero a.value

instance reduced_mv_polynomial.BEq (k : Type u) [B : BEq k] [choose_zero k] (n : Nat)
  : BEq (reduced_mv_polynomial k n) := {
    beq (a b : reduced_mv_polynomial k n) := by
      apply mv_polynomial.beq a.value b.value
  }




-- def reduced_mv_polynomial.from_reduced_polynomial
--   {k : Type u} [BEq k] [choose_zero k] (n : Nat)
--   (a : reduced_polynomial (reduced_mv_polynomial k n) (reduced_mv_polynomial.is_zero)) :
--   mv_polynomial k (n + 1)
--   := a.value.map (reduced_mv_polynomial.value)

-- instance reduced_mv_polynomial.ring (k : Type u) [BEq k] [LawfulBEq k] [ring k] (n : Nat) :
--   ring (reduced_mv_polynomial k n) :=
--   {
--     zero := _
--     add := _
--     add_zero_left := _
--     add_zero_right := _
--     add_is_assoc := _
--     add_is_comm := _
--     e := _
--     mul := _
--     mul_e_right := _
--     mul_e_left := _
--     mul_is_assoc := _
--     mul_is_comm := _
--     add_inverse := _
--     add_inverse_is_inverse := _
--     mul_is_linear_left := _
--     mul_is_linear_right := _
--   }


-- instance  (k : Type u) [BEq k] [LawfulBEq k] [ring k] (n : Nat)
--   : free_algebra (reduced_mv_polynomial k n) (reduced_mv_polynomial k (n + 1)) where



-- def var
--   (base : Type) [ring base] [ToString base] [BEq base] [LawfulBEq base]
--   (n : Nat) (i : Nat) : mv_polynomial base (n + 1) := by




-- def mul_nat_polynomial (a : List Nat) (b : List Nat) := mul_poly a b

-- #eval convert_polynomial_to_string Nat 0 (trim_utilities.tail (· == choose_zero.zero) (mul_nat_polynomial [1, 2, 1, 0] [1, 2, 1])) var1 0


end polynomial_ring
