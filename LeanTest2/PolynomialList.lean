import LeanTest2.Algebra
import LeanTest2.Trim
import LeanTest2.ReducedRing

namespace List_Polynomial

open algebra
open Reduced_Ring

structure uv (k : Type u) where
  data : List k

theorem uv.ext_iff
  (k : Type u)
  {p q : uv k} :
  p = q ↔ p.data = q.data := by
  constructor
  · intro h; simp [h]
  · intro h; cases p; cases q; simp at h; simp [h]

@[ext]
theorem uv.eq_if
  (k : Type u)
  {p q : uv k}
  (values_are_equal : p.data = q.data) :  p = q := by
  cases p;
  cases q;
  simp at values_are_equal
  simp [values_are_equal]

theorem uv.eq_then
  (k : Type u)
  {p q : uv k}
  (h : p = q) : p.data = q.data := by
  cases p;
  cases q;
  simp at h
  simp [h]

@[reducible, simp]
def uv.trim {k : Type u} (P : k → Bool) (a : uv k) : (uv k) where
  data := trim_utilities.tail P a.data


def List.add
  {k : Type u} [A : Additive k]
  (a : List k) (b : List k) : List k
  :=
  match a, b with
  | [], [] => []
  | [], b' => b'
  | a', [] => a'
  | xa :: a', xb :: b' => A.add xa xb :: (List.add a' b')

infix:90 "+₀" => List.add

theorem List.add_cons_cons {k : Type u} [A : Additive k]
  (xa xb : k) (a b : List k) :
  (List.add (xa :: a) (xb :: b)) = (A.add xa xb) :: (List.add a b) := by
  rw [List.add]

@[simp]
theorem List.add_nil_any
  {k : Type u} [A : Additive k]
  (a : List k)
  :
  List.add [] a = a
  := by
  match a with
  | [] => rw [List.add]
  | xa :: a'=>
    rw [List.add]
    apply List.cons_ne_nil

@[simp]
theorem List.add_any_nil
  {k : Type u} [A : Additive k]
  (a : List k)
  :
  List.add a [] = a
  := by
  match a with
  | [] => rw [add]
  | xa :: a'=>
    rw [add]
    apply List.cons_ne_nil

def List.shift
  {k : Type u} [Z : Pointed_Zero k] (a : List k) : List k
  :=
  Z.zero :: a

prefix:100 "σ" => List.shift

def List.action.left
  {k : Type u} [M : Multiplicative k]
  (s : k) (a : List k) : List k
  :=
  a.map (M.mul s)

infix:90 "∘→" => List.action.left

def List.action.right
  {k : Type u} [M : Multiplicative k]
  (a : List k) (s : k) : List k
  :=
  a.map (M.mul . s)

infix:90 "←∘" => List.action.right

@[simp]
theorem List.action.left.identity
  {k : Type u} [M : Multiplicative k]
  (a : List k)  (k_left_identity : k) (h_identity : is_left_identity M.mul k_left_identity)
  : action.left k_left_identity a = a
  := by
  rw [action.left]
  exact List.map_id'' h_identity a

@[simp]
theorem List.action.right.identity
  {k : Type u} [M : Multiplicative k]
  (a : List k)  (k_right_identity : k) (h_identity : is_right_identity M.mul k_right_identity)
  : action.right a k_right_identity = a
  := by
  rw [action.right]
  exact List.map_id'' h_identity a


@[simp]
theorem List.action.left.nil'
  {k : Type u} [M : Multiplicative k] (s : k)  : action.left s [] = [] := by  rfl

@[simp]
theorem List.action.right.nil'
  {k : Type u} [M : Multiplicative k] (s : k) : action.right [] s = [] := by rfl

def List.convolve
  {k : Type u} [Z : Pointed_Zero k] [A : Additive k] [M : Multiplicative k]
  (a : List k) (b : List k)  : List k
  :=
  match a with
  | [] => []
  | x :: a' =>
    List.add
      (action.left x b)
      (shift (convolve a' b))

infix:90 "*₀" => List.convolve

@[simp]
def uv.add
  {k : Type u} [A : Additive k]
  (a : uv k) (b : uv k) : uv k where
  data := List.add a.data b.data

def uv.mul
  {k : Type u} [Z : Pointed_Zero k] [A : Additive k] [A : Multiplicative k]
  (a : uv k) (b : uv k) : uv k where
  data := List.convolve a.data b.data


instance List.has_add (k : Type u) [A : Additive k] : Additive (List k) where
  add := List.add

instance uv.has_add (k : Type u) [A : Additive k] : Additive (uv k) where
  add := uv.add

@[simp]
theorem uv.add_rw
  {k : Type u} [A : Additive k]
  (a b : uv k) :
  (uv.has_add k).add a b = uv.add a b := rfl


instance uv.has_mul (k : Type u) [Z : Pointed_Zero k] [A : Additive k] [Multiplicative k] : Multiplicative (uv k) where
  mul := uv.mul

@[simp]
theorem uv.mul_rw
  {k : Type u} [Z : Pointed_Zero k] [A : Additive k] [Multiplicative k]  :
  (uv.has_mul k).mul = uv.mul := rfl

@[simp]
def uv.zero (k : Type u) : uv k where
  data := []

instance uv.has_zero (k : Type u) : Pointed_Zero (uv k) where
  zero := uv.zero k

@[simp]
theorem uv.zero_rw
  {k : Type u} :
  (uv.has_zero k).zero = uv.zero k := rfl

-- instance List.has_zero (k : Type u) : Pointed_Zero (List k) where
--   zero := []

-- instance List.has_e (k : Type u) [Z : Pointed_Multiplicative_Identity k] : Pointed_Multiplicative_Identity (List k) where
--   e := [Z.e]


def uv.e (k : Type u) [Z : Pointed_Multiplicative_Identity k]  : uv k where
  data := [Z.e]


instance uv.has_e (k : Type u) [Z : Pointed_Multiplicative_Identity k] : Pointed_Multiplicative_Identity (uv k) where
  e := uv.e k

@[simp]
theorem uv.e_rw (k : Type u) [Z : Pointed_Multiplicative_Identity k] :
  (uv.has_e k).e = uv.e k := by rfl

def uv.add_inverse {k : Type u} [R : Potential_Ring k] (a : uv k) : uv k where
  data := a.data.map R.add_inverse

-- class Zero_Predicate {k : Type u} [Pointed_Zero k] (P : k → Bool) where
--   map_zero : P zero

def List.reduce
  {k : Type u} (reduce : k → k) (P : k → Bool) (a : List k) : List k := trim_utilities.tail P (a.map reduce)

def uv.reduce {k : Type u}
  (reduce : k → k) (P : k → Bool) (a : uv k) : uv k where
  data := List.reduce reduce P a.data

@[simp]
theorem  List.reduce_nil {k : Type u} (reduce : k → k) (P : k → Bool) : List.reduce reduce P [] = [] := by
  rw [List.reduce, List.map]
  exact trim_utilities.tail.nil P

theorem List.reduce_idempotent {k : Type u}
  (reduce : k → k) (P : k → Bool) (h : (q : k) → reduce (reduce q) = reduce q) (a : List k)
  : List.reduce reduce P (List.reduce reduce P a) = List.reduce reduce P a
  := by
  match a with
  | [] => simp
  | ha :: ta =>
    have hi := List.reduce_idempotent reduce P h ta
    rw [List.reduce, List.reduce, List.map, trim_utilities.tail]
    rw [List.reduce, List.reduce] at hi
    split
    · case h_1 w ww =>
      rw [apply_ite (List.map reduce), List.map, List.map, List.map, h, apply_ite (trim_utilities.tail P)]
      simp
    · case h_2 w ww =>
      rw [List.map, trim_utilities.tail, hi]
      simp [h]

instance uv.reduce.is_zero {k : Type u}
  (reduce : k → k) (P : k → Bool)
  [R : Potential_Ring k]
  : Add_Zero_Reduction (uv.reduce reduce P) where
  add_any_zero (a) := by
    simp [uv.reduce, uv.add, uv.zero]
  add_zero_any (a) := by
    simp [uv.reduce, uv.add, uv.zero]

instance List.reduce.is_idempotent {k : Type u}
  (reduce : k → k) (P : k → Bool)
  [GR : Idempotent_Reduction reduce]
  : Idempotent_Reduction (List.reduce reduce P) where
  idempotent (a) := by
    apply List.reduce_idempotent
    exact fun q => Idempotent_Reduction.idempotent q

instance uv.reduce.is_idempotent {k : Type u}
  (reduce : k → k) (P : k → Bool)
  [GR : Idempotent_Reduction reduce]
  : Idempotent_Reduction (uv.reduce reduce P) where
  idempotent (a) := by
    rw [uv.reduce, uv.reduce]
    simp
    apply List.reduce_idempotent
    apply GR.idempotent





-- def List.reduce'
--   {k : Type u} (reduce : k → k) [IR : Idempotent_Reduction reduce] (P : k → Bool) (x : k) (a : List k) :
--   List.reduce reduce P (reduce x :: a) = List.reduce reduce P (x :: a) := by
--   rw [List.reduce, List.map, IR.idempotent, ←List.map, ←List.reduce]

theorem List.inverse_is_left_inverse
  (k : Type u) [R : Potential_Ring k]
  (reduce : k → k) [BR : Best_Reduction reduce]
  (P : k → Bool)
  (P_reduce : (a : k) → P (reduce a) = P a) (hP : P R.zero)
  (a : List k) :
  List.reduce reduce P (List.add (a.map R.add_inverse) a) = [] :=
  by
  match a with
  | [] =>
    simp
  | x :: a =>
    have hi := List.inverse_is_left_inverse k reduce P P_reduce hP a
    rw [List.map, add]
    rw [List.reduce, List.map, trim_utilities.tail.cons, ←List.map, ←List.reduce]
    rw [hi]
    rw [BR.add_add_inverse_self]
    rw [trim_utilities.tail.singleton, P_reduce, hP, List.map_nil]
    simp
    repeat assumption

theorem uv.inverse_is_left_inverse
  (k : Type u) [R : Potential_Ring k]
  (reduce : k → k) [BR : Best_Reduction reduce]
  (P : k → Bool)
  (P_reduce : (a : k) → P (reduce a) = P a) (hP : P R.zero)
  (a : uv k) :
  (uv.add (a.add_inverse) a).reduce reduce P = (uv.zero k) := by
    apply uv.eq_if
    simp [add_inverse, uv.reduce]
    rw [List.inverse_is_left_inverse k reduce P P_reduce hP]

@[simp]
theorem List.add_zero_any
  {k : Type u} [Additive k] [Z : Pointed_Zero k]
  (reduce : k → k)
  [AZR : Add_Zero_Reduction reduce]
  (P : k → Bool)
  (P_reduce : (a : k) → P (reduce a) = P a) (hP : P Z.zero)
  (a : List k)
  :
  List.reduce reduce P (List.add [Z.zero] a) = List.reduce reduce P a
  := by
  match a with
  | [] =>
    simpa [List.reduce, P_reduce]
  | xa :: a'=>
    rw [add, add_nil_any]
    rw [List.reduce, List.map]
    rw [trim_utilities.tail, ←P_reduce, AZR.add_zero_any, P_reduce]
    rw [List.reduce, List.map, trim_utilities.tail]

@[simp]
theorem List.add_any_zero
  {k : Type u} [Z : Pointed_Zero k] [Additive k]
  (reduce : k → k) [AZR : Add_Zero_Reduction reduce]
  (P : k → Bool)
  (P_reduce : (a : k) → P (reduce a) = P a) (hP : P Z.zero)
  (a : List k)
  :
  List.reduce reduce P (List.add a [Z.zero]) = List.reduce reduce P a
  := by
  match a with
  | [] =>
    simpa [List.reduce, P_reduce]
  | xa :: a'=>
    rw [add, add_any_nil]
    rw [List.reduce, List.map]
    rw [trim_utilities.tail, ←P_reduce, AZR.add_any_zero, P_reduce]
    rw [List.reduce, List.map, trim_utilities.tail]


theorem List.add_zero_zero
  {k : Type u} [A : Additive k]
  (reduce : k → k)
  (P : k → Bool)
  (P_reduce : (a : k) → P (reduce a) = P a)
  (addP : (a b : k) → (P a) → (P b) → (P (a ⊹ b)))
  (a : List k) (b: List k)
  (a_mem : ∀ x ∈ a, P (reduce x))
  (b_mem : ∀ x ∈ b, P (reduce x))
  : ∀ x ∈ (List.add a b), P (reduce x)
  := by
  match a, b with
  | [], _ =>
    simpa
  | _, [] =>
    simpa
  | ha :: ta, hb :: tb =>
    intro x
    have hi := List.add_zero_zero reduce P P_reduce addP ta tb (
      by intro q; intro q_mem; apply a_mem; exact List.mem_cons_of_mem ha q_mem
    ) (
      by intro q; intro q_mem; apply b_mem; exact List.mem_cons_of_mem hb q_mem
    )
    rw [List.add, List.mem_cons]
    intro x_mem
    cases x_mem
    · case inl x_mem_add =>
      rw [x_mem_add, P_reduce]
      apply addP
      rw [← P_reduce]
      apply a_mem
      apply List.mem_cons_self
      rw [← P_reduce]
      apply b_mem
      apply List.mem_cons_self
    · case inr x_mem_add =>
      apply hi x x_mem_add


theorem List.add_zero_zero' {k : Type u} [BEq k] [LawfulBEq k]
  [A : Additive k] [Z : Pointed_Zero k] (add_zero_any: ∀ x : k, A.add Z.zero x = x)
  (a : List k) (b: List k) (ha : ∀ x ∈ a, x = Z.zero) (hb : ∀ x ∈ b, x = Z.zero)
  : ∀ x ∈ (List.add a b), x = Z.zero
  := by
  have known := List.add_zero_zero (·) (· == Z.zero) (by intro q; rfl) (by simp[add_zero_any]) a b (by simpa) (by simpa)
  simp at known
  apply known

-- theorem add_poly.zero_any' {k : Type u} [BEq k] [LawfulBEq k]
--   [A : Additive k] [Z : Pointed_Zero k] (add_zero_any: ∀ x : k, A.add Z.zero x = x)
--   (a : List k) (b: List k) (ha : ∀ x ∈ a, x = Z.zero)
--   : trim_utilities.tail (· == Pointed_Zero.zero) (add_poly a b) = trim_utilities.tail (· == Pointed_Zero.zero) b := by
--   match a, b with
--   | [], [] => rw [add_poly]
--   | a', [] =>
--     rw [add_poly.any_nil]
--     rw [trim_utilities.tail.nil_of_all, trim_utilities.tail.nil]
--     intro x hx
--     rw [beq_iff_eq]
--     apply ha x hx
--   | [], b' =>
--     rw [add_poly.nil_any]
--   | xa :: a', xb :: b' =>
--     rw [add_poly]
--     rw [trim_utilities.tail.cons]
--     rw [zero_any']
--     have hxa := ha xa
--     rw [List.mem_cons] at hxa
--     rw [hxa (Or.intro_left _ rfl)]
--     rw [add_zero_any]
--     rw [←trim_utilities.tail.cons]
--     apply add_zero_any
--     intro xa'
--     have hxa' := ha xa'
--     rw [List.mem_cons] at hxa'
--     intro xa'_mem
--     exact (hxa' (Or.intro_right _ xa'_mem))

-- theorem add_poly.any_zero' {k : Type u} [BEq k] [LawfulBEq k]
--   [A : Additive k] [Z : Pointed_Zero k] (add_any_zero: ∀ x : k, A.add x Z.zero = x)
--   (a : List k) (b: List k) (hb : ∀ x ∈ b, x = Z.zero)
--   : trim_utilities.tail (· == Pointed_Zero.zero) (add_poly a b) = trim_utilities.tail (· == Pointed_Zero.zero) a := by
--   match a, b with
--   | [], [] => rw [add_poly]
--   | a', [] =>
--     rw [add_poly.any_nil]
--   | [], b' =>
--     rw [add_poly.nil_any]
--     rw [trim_utilities.tail.nil_of_all, trim_utilities.tail.nil]
--     intro x hx
--     rw [beq_iff_eq]
--     apply hb x hx
--   | xa :: a', xb :: b' =>
--     rw [add_poly]
--     rw [trim_utilities.tail.cons]
--     rw [any_zero']
--     have hxb := hb xb
--     rw [List.mem_cons] at hxb
--     rw [hxb (Or.intro_left _ rfl)]
--     rw [add_any_zero]
--     rw [←trim_utilities.tail.cons]
--     apply add_any_zero
--     intro xb'
--     have hxb' := hb xb'
--     rw [List.mem_cons] at hxb'
--     intro xa'_mem
--     exact (hxb' (Or.intro_right _ xa'_mem))



theorem List.reduce_cons
  {k : Type u}
  (reduce : k → k) [IR : Idempotent_Reduction reduce]
  (P : k → Bool)
  (x : k) (a : List k)
  :
  List.reduce reduce P (x :: a) = List.reduce reduce P (reduce x :: List.reduce reduce P (a)) := by
  rw [List.reduce, List.map, trim_utilities.tail.cons, List.reduce, List.map, IR.idempotent x]
  conv => rhs; rw [trim_utilities.tail.cons]
  rw [← List.reduce, ← List.reduce, List.reduce_idempotent]
  apply IR.idempotent

theorem List.shift_reduce
  {k : Type u} [Pointed_Zero k]
  (reduce : k → k) [IR : Idempotent_Reduction reduce]
  (P : k → Bool)
  (a : List k)
  : List.reduce reduce P (shift a)
  = List.reduce reduce P (shift (List.reduce reduce P a))
  := by
  rw [shift, shift, List.reduce_cons]
  conv => rhs; rw [List.reduce_cons];
  rw [List.reduce_idempotent]
  apply IR.idempotent

theorem List.reduce_alt {k : Type u}
  (reduce : k → k) (P : k → Bool) (a : List k) :
  List.reduce reduce P a = match a with
  | [] => []
  | ha :: ta => match List.reduce reduce P ta with
    | [] => if P (reduce ha) then [] else [reduce ha]
    | _ => reduce ha :: List.reduce reduce P ta
    := by
  match a with
  | [] => simp
  | ha :: ta => simp [List.reduce, trim_utilities.tail]; rfl

theorem List.reduce_alt' {k : Type u}
  (reduce : k → k) (P : k → Bool) (x : k) (a : List k) :
  List.reduce reduce P (x :: a)
  =
  if (List.reduce reduce P a) = [] then
    if P (reduce x) then [] else [reduce x]
  else reduce x :: List.reduce reduce P a
    := by
  simp [List.reduce, trim_utilities.tail];
  split <;> split <;> simp_all

theorem List.reduce_singleton {k : Type u}
  (reduce : k → k) (P : k → Bool) (x : k) :
  List.reduce reduce P [x] = if P (reduce x) then [] else [reduce x] := by simp [List.reduce]

theorem List.reduce_head {k : Type u}
  (reduce : k → k)  [IR : Idempotent_Reduction reduce] (P : k → Bool) (x : k) (a : List k) :
  List.reduce reduce P (x :: a) = List.reduce reduce P (reduce x :: a) :=by
  rw [List.reduce, List.reduce, List.map, List.map, IR.idempotent]

theorem List.reduce_tail {k : Type u}
  (reduce : k → k)  [IR : Idempotent_Reduction reduce] (P : k → Bool) (x : k) (a : List k) :
  List.reduce reduce P (x :: a) = List.reduce reduce P (x :: List.reduce reduce P a) :=by
  rw [List.reduce_alt', List.reduce_alt', List.reduce_idempotent]
  apply IR.idempotent

-- def uv.empty (k : Type u) (a : uv k) := a.data.isEmpty


theorem List.map_reduce_add {k : Type u} [Additive k]
  (reduce : k → k) [AR : Additive_Reduction reduce] [IR : Idempotent_Reduction reduce] (a b : List k):
  List.map reduce (List.add a b) = List.map reduce (List.add (List.map reduce a) (List.map reduce b)) := by
  match a, b with
  | [], _ => simp [IR.idempotent]
  | _, [] => simp [IR.idempotent]
  | ha :: ta, hb :: tb =>
    have hi := List.map_reduce_add reduce ta tb
    rw [List.add, List.map, List.map, List.map, List.add, List.map, AR.add]
    rw [hi]

theorem ite_apply {k : Type u} (p : Prop) [Decidable p] (f1 f2 : k → k) (a : k) :
  (if p then f1 else f2) a =  (if p then f1 a else f2 a) := by
  split <;> rfl

theorem List.reduce_nil_tail {k : Type u}
  (reduce : k → k)
  (P : k → Bool) (x : k) (a : List k) (h : List.reduce reduce P (x :: a) = []) :
  List.reduce reduce P (a) = [] := by
  rw [List.reduce_alt'] at h
  split at h <;> simp_all

theorem List.reduce_nil_head {k : Type u}
  (reduce : k → k)
  (P : k → Bool) (x : k) (a : List k) (h : List.reduce reduce P (x :: a) = []) :
  P (reduce x) := by
  rw [List.reduce_alt'] at h
  split at h <;> simp_all

theorem List.reduce_add_nil_any {k : Type u} [A : Additive k]
  (reduce : k → k)
  (P : k → Bool)
  (P_reduce : (a : k) → P (reduce a) = P a)
  [AZPR : Add_Zero_Predicate_Reduction reduce P]
  (a b : List k) (h : List.reduce reduce P a = []) :
  List.reduce reduce P (List.add a b) = List.reduce reduce P b := by
  match a with
  | [] => simp
  | ha :: ta =>
    have reduce_ta := List.reduce_nil_tail reduce P ha ta h
    have reduce_ha := List.reduce_nil_head reduce P ha ta h
    have reduce_ha' := List.reduce_nil_head reduce P ha ta h
    rw [P_reduce] at reduce_ha'
    match b with
    | [] => simpa
    | hb :: tb =>
      have add_ha_any := AZPR.add_zero_any ha hb reduce_ha'
      have hi := List.reduce_add_nil_any reduce P P_reduce ta tb reduce_ta
      rw [add]
      rw [List.reduce_alt', hi]
      rw [List.reduce_alt']
      split <;> simp_all

theorem List.reduce_add_any_nil {k : Type u} [A : Additive k]
  (reduce : k → k)
  (P : k → Bool)
  (P_reduce : (a : k) → P (reduce a) = P a)
  [AZPR : Add_Zero_Predicate_Reduction reduce P]
  (a b : List k) (h : List.reduce reduce P b = []) :
  List.reduce reduce P (List.add a b) = List.reduce reduce P a := by
  match b with
  | [] => simp
  | hb :: tb =>
    have reduce_tb := List.reduce_nil_tail reduce P hb tb h
    have reduce_hb := List.reduce_nil_head reduce P hb tb h
    have reduce_hb' := List.reduce_nil_head reduce P hb tb h
    rw [P_reduce] at reduce_hb'
    match a with
    | [] => simpa
    | ha :: ta =>
      have add_ha_any := AZPR.add_any_zero ha hb reduce_hb'
      have hi := List.reduce_add_any_nil reduce P P_reduce ta tb reduce_tb
      rw [add]
      rw [List.reduce_alt', hi]
      rw [List.reduce_alt']
      split <;> simp_all

theorem List.reduce_add
  {k : Type u} [A : Additive k]
  (reduce : k → k) [AR : Additive_Reduction reduce] [IR : Idempotent_Reduction reduce]
  (P : k → Bool)
  [PR : Predicated_Reduction reduce P]
  [AP : Additive_Predicate P]
  [AZPR : Add_Zero_Predicate_Reduction reduce P]
  (a : List k) (b : List k)
  : List.reduce reduce P (add (List.reduce reduce P a) (List.reduce reduce P b))
  = List.reduce reduce P (add a b)
  := by
  match a with
  | [] =>
    simp []
    apply List.reduce_idempotent
    apply IR.idempotent
  | ha :: ta =>
    match b with
    | [] => simp; apply List.reduce_idempotent; apply IR.idempotent
    | hb :: tb =>
      have hi := List.reduce_add reduce P ta tb
      simp [List.reduce_alt', List.add]
      -- rw [←hi]
      have hab := AP.add (reduce ha) (reduce hb)
      have hab' := AP.add (ha) (hb)
      rw [←AR.add]
      rw [apply_ite (List.add)]
      rw [apply_ite (List.add)]
      rw [ite_apply]
      rw [ite_apply]
      repeat rw [apply_ite (List.add _ ·)]
      rw [apply_ite (List.reduce reduce P)]
      rw [apply_ite (List.reduce reduce P)]
      rw [apply_ite (List.reduce reduce P)]
      rw [apply_ite (List.reduce reduce P)]
      rw [apply_ite (List.reduce reduce P)]
      rw [apply_ite (List.reduce reduce P)]
      rw [apply_ite (List.reduce reduce P)]
      rw [apply_ite (List.reduce reduce P)]
      simp [List.add, List.reduce_alt', IR.idempotent]
      if hta : List.reduce reduce P ta = [] then
        have add_nil := List.reduce_add_nil_any reduce P PR.erase ta tb hta
        rw [add_nil]
        if htb : List.reduce reduce P tb = [] then
          if hPa : P (reduce ha) then
            have hPa'  : P (reduce ha) := hPa
            rw [PR.erase] at hPa'
            have add_a := AZPR.add_zero_any ha hb hPa'
            if hPb : P (reduce hb) then
              simp_all
              rw [PR.erase]
              apply AP.add (reduce ha) (reduce hb) hPa hPb
            else
              rw [AR.add, add_a]
              simp [hPa, hPb, hta, htb]
          else
            if hPb : P (reduce hb) then
              have hPb'  : P (reduce hb) := hPb
              rw [PR.erase] at hPb'
              have add_b := AZPR.add_any_zero ha hb hPb'
              simp [hPa, hPb, hta, htb]
              rw [AR.add, add_b]
              simp
              exact eq_false_of_ne_true hPa
            else
              simp_all
        else
          if hPa : P (reduce ha) then
            have hPa'  : P (reduce ha) := hPa
            rw [PR.erase] at hPa'
            have add_a := AZPR.add_zero_any ha hb hPa'
            if hPb : P (reduce hb) then
              simp_all [AR.add]
            else
              rw [AR.add, add_a]
              rw [List.reduce_idempotent reduce P IR.idempotent]
              simp [hPa, hta, htb]
          else
            if hPb : P (reduce hb) then
              have hPb'  : P (reduce hb) := hPb
              rw [PR.erase] at hPb'
              have add_b := AZPR.add_any_zero ha hb hPb'
              simp [hPa, hta, htb]
              rw [AR.add, add_b]
              rw [List.reduce_idempotent reduce P IR.idempotent]
              simp
              intro reduce_tb
              rw [reduce_tb]
              simp
              exact eq_false_of_ne_true hPa
            else
              simp_all
      else
        if htb : List.reduce reduce P tb = [] then
          have add_nil := List.reduce_add_any_nil reduce P PR.erase ta tb htb
          rw [add_nil]
          if hPa : P (reduce ha) then
            have hPa'  : P (reduce ha) := hPa
            rw [PR.erase] at hPa'
            have add_a := AZPR.add_zero_any ha hb hPa'
            if hPb : P (reduce hb) then
              have hPb'  : P (reduce hb) := hPb
              rw [PR.erase] at hPb'
              have add_b := AZPR.add_any_zero ha hb hPb'
              simp [hPa, hPb, hta, htb]
              rw [List.reduce_idempotent reduce P IR.idempotent]
              rw [AR.add]
              rw [add_b]
              simpa
            else
              rw [AR.add, add_a]
              simp [hPb, hta, htb]
              rw [List.reduce_idempotent reduce P IR.idempotent]
              simp
          else
            if hPb : P (reduce hb) then
              have hPb'  : P (reduce hb) := hPb
              rw [PR.erase] at hPb'
              have add_b := AZPR.add_any_zero ha hb hPb'
              simp [hPa, hPb, hta, htb]
              rw [AR.add, add_b]
              rw [List.reduce_idempotent reduce P IR.idempotent]
              simp
            else
              simp_all
        else
          if hPa : P (reduce ha) then
            have hPa'  : P (reduce ha) := hPa
            rw [PR.erase] at hPa'
            have add_a := AZPR.add_zero_any ha hb hPa'
            if hPb : P (reduce hb) then
              simp_all [AR.add]
            else
              rw [AR.add, add_a]
              rw [List.reduce_idempotent reduce P IR.idempotent]
              simp [hta, htb]
              rw [hi]
          else
            if hPb : P (reduce hb) then
              have hPb'  : P (reduce hb) := hPb
              rw [PR.erase] at hPb'
              have add_b := AZPR.add_any_zero ha hb hPb'
              simp [hta, htb]
              rw [AR.add, add_b]
              rw [hi]
            else
              simp_all


instance uv.reduce_additive
  (k : Type u) [Additive k]
  (reduce : k → k)
  [AR : Additive_Reduction reduce] [IR : Idempotent_Reduction reduce]
  (P : k → Bool) [AP : Additive_Predicate P]
  [PR : Predicated_Reduction reduce P] [AZPR : Add_Zero_Predicate_Reduction reduce P]
  : Additive_Reduction (uv.reduce reduce P) where
  add (a b):= by
    rw [uv.reduce]
    apply uv.eq_if
    simp
    apply List.reduce_add


@[simp]
theorem List.convolve_nil_any
  {k : Type u} [Z : Pointed_Zero k] [A : Additive k] [M : Multiplicative k]
  (a : List k)
  :
  List.convolve [] a = []
  := by
  rw [List.convolve]

@[simp]
theorem List.convolve_any_nil
  {k : Type u}
  [Z : Pointed_Zero k] [A : Additive k] [M : Multiplicative k]
  (reduce : k → k) [IR : Idempotent_Reduction reduce]
  (P : k → Bool) [RP : Predicated_Reduction reduce P] [ZP : Zero_Predicate P]
  (a : List k)
  :
  List.reduce reduce P (List.convolve a []) = []
  := by
  match a with
  | [] => simp [List.convolve]
  | ha :: ta =>
    have hi := List.convolve_any_nil reduce P ta
    rw [List.convolve]
    rw [action.left]
    rw [List.map_nil]
    simp [shift]
    rw [List.reduce_cons]
    rw [hi]
    rw [List.reduce_singleton]
    rw [IR.idempotent]
    rw [RP.erase]
    simp



@[simp]
theorem List.action.right.nil
  {k : Type u}
  [M : Multiplicative k]
  (reduce : k → k)
  (P : k → Bool)
  (a : k)
  :
  List.reduce reduce P (List.action.right [] a) = []
  := by
  rw[action.right, List.map_nil, List.reduce_nil]


@[simp]
theorem List.action.left.nil
  {k : Type u}
  [M : Multiplicative k]
  (reduce : k → k)
  (P : k → Bool)
  (a : k)
  :
  List.reduce reduce P (action.left a []) = []
  := by
  rw [action.left, List.map_nil, List.reduce_nil]

theorem List.action.left.from_convolve
  {k : Type u}
  [Z : Pointed_Zero k] [A : Additive k] [M : Multiplicative k]
  (reduce : k → k)
  (P : k → Bool)
  [Add_Zero_Reduction reduce]
  (P_reduce : (a : k) → P (reduce a) = P a) (P_zero : P Z.zero)
  (s : k) (a : List k)
  :
  List.reduce reduce P (List.convolve [s] a)
  =
  List.reduce reduce P (List.action.left s a)
  := by
  rw [List.convolve]
  simp_all [shift]

theorem List.action.right.from_convolve
  {k : Type u}
  [Z : Pointed_Zero k] [A : Additive k] [M : Multiplicative k]
  (reduce : k → k)
  [IR : Idempotent_Reduction reduce] [Add_Zero_Reduction reduce] [Additive_Reduction reduce]
  (P : k → Bool)
  [ZP : Zero_Predicate P]
  [PR : Predicated_Reduction reduce P]
  [AP : Additive_Predicate P]
  [AZPR : Add_Zero_Predicate_Reduction reduce P]
  (a : List k) (s : k)
  :
  List.reduce reduce P (List.convolve a [s])
  =
  List.reduce reduce P (action.right a s)
  := by
  match a with
  | [] =>
    simp
  | xa :: a' =>
    rw [List.convolve]
    rw [action.left]
    rw [←List.reduce_add, List.shift_reduce, action.right.from_convolve, ←shift_reduce, ←reduce_add]
    rw [shift]
    simp
    rw [List.reduce_idempotent]
    rw [List.reduce_idempotent]
    rw [List.reduce_add]
    rw [←List.add]
    rw [action.right]
    rw [action.right]
    simp
    rw [List.add]
    simp
    rw [List.reduce_head]
    rw [AZPR.add_any_zero]
    rw [←List.reduce_head]
    apply ZP.zero_true
    exact fun q => Idempotent_Reduction.idempotent q
    exact fun q => Idempotent_Reduction.idempotent q

@[simp]
theorem List.action.left.reduced_identity
  {k : Type u} (reduce : k → k) [Idempotent_Reduction reduce]
  (P : k → Bool)
  [E : Pointed_Multiplicative_Identity k]
  [M : Multiplicative k] [MMIR : Mul_Multiplicative_Identity_Reduction reduce]
  (a : List k)
  : List.reduce reduce P (action.left E.e a) = List.reduce reduce P a
  := by
  match a with
  | [] => simp
  | ha :: ta =>
    rw [action.left, List.map, ←action.left]
    rw [List.reduce_tail, List.action.left.reduced_identity, ←List.reduce_tail]
    rw [List.reduce_head, MMIR.mul_e_any, ←List.reduce_head]

@[simp]
theorem List.action.right.reduced_identity
  {k : Type u} (reduce : k → k) [Idempotent_Reduction reduce]
  (P : k → Bool)
  [E : Pointed_Multiplicative_Identity k]
  [M : Multiplicative k] [MMIR : Mul_Multiplicative_Identity_Reduction reduce]
  (a : List k)
  : List.reduce reduce P (action.right a E.e) = List.reduce reduce P a
  := by
  match a with
  | [] => simp
  | ha :: ta =>
    rw [action.right, List.map, ←action.right]
    rw [List.reduce_tail, List.action.right.reduced_identity, ←List.reduce_tail]
    rw [List.reduce_head, MMIR.mul_any_e, ←List.reduce_head]

@[simp]
theorem List.convolve_e_any
  {k : Type u}
  [Z : Pointed_Zero k] [E : Pointed_Multiplicative_Identity k] [A : Additive k] [M : Multiplicative k]
  (reduce : k → k)
  [Idempotent_Reduction reduce]
  [MMIR : Mul_Multiplicative_Identity_Reduction reduce]
  (P : k → Bool)
  [Add_Zero_Reduction reduce]
  (P_reduce : (a : k) → P (reduce a) = P a) (P_zero : P Z.zero)
  (a : List k)
  :
  List.reduce reduce P (convolve [E.e] a)
  =
  List.reduce reduce P a
  := by
  rw [action.left.from_convolve reduce P P_reduce P_zero E.e a]
  rw [action.left.reduced_identity]
  repeat assumption

@[simp]
theorem List.convolve_any_e
  {k : Type u}
  [Z : Pointed_Zero k] [E : Pointed_Multiplicative_Identity k] [A : Additive k] [M : Multiplicative k]
  (reduce : k → k)
  (P : k → Bool)
  [Add_Zero_Reduction reduce]
  [IR : Idempotent_Reduction reduce] [Additive_Reduction reduce]
  [ZP : Zero_Predicate P]
  [PR : Predicated_Reduction reduce P]
  [AP : Additive_Predicate P]
  [AZPR : Add_Zero_Predicate_Reduction reduce P]
  [MMIR : Mul_Multiplicative_Identity_Reduction reduce]
  (a : List k)
  :
  List.reduce reduce P (List.convolve a [E.e])
  =
  List.reduce reduce P a
  := by
  rw [List.action.right.from_convolve reduce P a E.e ]
  rw [List.action.right.reduced_identity]
  repeat assumption

theorem List.add.singleton_any
  {k : Type u} [A : Additive k] (a : List k) (x : k) (y : k)
  : List.add [x] (y :: a) = (A.add x y) :: a := by
  simp [List.add]

theorem List.action.left.cons
  {k : Type u}
  [R : Ring k] (a : k) (x : k) (b : List k)  :
  List.add [R.mul a x] (shift (action.left a b))
  = action.left a (x :: b)
  := by
  rw [action.left, shift]
  rw [add.singleton_any]
  rw [action.left, List.map]
  simp

theorem List.action.left.cons_linear
  {k : Type u}
  [Z : Pointed_Zero k] [Pointed_Multiplicative_Identity k] [A : Additive k] [M : Multiplicative k]
  (reduce : k → k)
  (P : k → Bool) (P_zero : P Z.zero)
  [Idempotent_Reduction reduce]
  [AZPR : Add_Zero_Predicate_Reduction reduce P]
  (a : k) (x : k) (b : List k)  :
  List.reduce reduce P (List.add [M.mul a x] (shift (action.left a b)))
  = List.reduce reduce P (action.left a (x :: b))
  := by
  rw [action.left, shift]
  rw [add.singleton_any]
  rw [List.reduce_head, AZPR.add_any_zero, ← List.reduce_head]
  rw [action.left, List.map]
  apply P_zero


theorem List.action.right.cons_linear
  {k : Type u}
  [Z : Pointed_Zero k] [A : Additive k] [M : Multiplicative k]
  (reduce : k → k)
  (P : k → Bool) (P_zero : P Z.zero)
  [Idempotent_Reduction reduce]
  [AZPR : Add_Zero_Predicate_Reduction reduce P]
  (a : List k) (x : k) (b : k)  :
  List.reduce reduce P (List.add [M.mul x b] (shift (action.right a b)))
  = List.reduce reduce P (action.right (x :: a) b)
  := by
  rw [action.right, shift]
  rw [add.singleton_any]
  rw [List.reduce_head, AZPR.add_any_zero, ← List.reduce_head]
  rw [action.right, List.map]
  apply P_zero

theorem List.shift.add
  {k : Type u}
  [Z : Pointed_Zero k] [A : Additive k]
  (reduce : k → k)
  (P : k → Bool)
  [ZP : Zero_Predicate P]
  [Idempotent_Reduction reduce]
  [AZPR : Add_Zero_Predicate_Reduction reduce P]
  (a : List k) (b : List k) :
  List.reduce reduce P (List.shift (List.add a b)) = List.reduce reduce P (List.add (List.shift a) (List.shift b))
  := by
  rw [shift, shift, shift]
  rw [List.add]
  symm
  rw [List.reduce_head, AZPR.add_any_zero, ← List.reduce_head]
  apply ZP.zero_true

theorem List.add_shift_shift
  {k : Type u}
  [Z : Pointed_Zero k] [A : Additive k]
  (reduce : k → k)
  (P : k → Bool)
  [ZP : Zero_Predicate P]
  [Idempotent_Reduction reduce]
  [AZPR : Add_Zero_Predicate_Reduction reduce P]
  (a : List k) (b : List k) :
  List.reduce reduce P (add (shift a) (shift b)) = List.reduce reduce P (shift (add a b))
  :=
  by symm; apply shift.add reduce P a b


theorem List.add_commutative
  {k : Type u}
  [Z : Pointed_Zero k] [A : Additive k]
  (reduce : k → k)
  (P : k → Bool)
  [Idempotent_Reduction reduce]
  [CAR : Commutative_Additive_Reduction reduce]
  (a : List k) (b : List k):
  List.reduce reduce P (add a b) = List.reduce reduce P  (add b a) := by
  match a, b with
  | [], b => simp
  | a, [] => simp
  | xa :: a', xb :: b' =>
    rw [add, add, List.reduce_head, List.reduce_tail, CAR.add_commutative, List.add_commutative, ←List.reduce_tail, ←List.reduce_head]
    repeat assumption

#check Nat.add_assoc

theorem List.add_is_associative
  {k : Type u}
  [Z : Pointed_Zero k] [A : Additive k]
  (reduce : k → k)
  (P : k → Bool)
  [Idempotent_Reduction reduce]
  [CAR : Commutative_Additive_Reduction reduce]
  (a : List k) (b : List k) (c : List k):
  List.reduce reduce P (add (add a b) c) = List.reduce reduce P (add a (add b c)) := by
  match a, b, c with
  | [], b, c => simp
  | a, [], c => simp
  | a, b, [] => simp
  | xa :: a', xb :: b', xc :: c' =>
    have hi := List.add_is_associative reduce P a' b' c'
    repeat rw [add]
    rw [List.reduce_tail, hi, ← List.reduce_tail]
    rw [List.reduce_head, CAR.add_assoc, ←List.reduce_head]

instance uv.reduce_commutative
  {k : Type u}
  [Z : Pointed_Zero k]  [A : Additive k]
  (reduce : k → k)
  [Idempotent_Reduction reduce]
  [Commutative_Additive_Reduction reduce]
  (P : k → Bool)
  [AP : Additive_Predicate P]
  [PR : Predicated_Reduction reduce P]
  [Add_Zero_Predicate_Reduction reduce P]
  : Commutative_Additive_Reduction (uv.reduce reduce P)
  where
  add (a b) := by
    apply uv.eq_if
    simp
    apply List.reduce_add
  add_any_zero (a) := by
    apply uv.eq_if
    simp [uv.zero]
  add_zero_any (a) := by
    apply uv.eq_if
    simp [uv.zero]
  add_commutative (a b) := by
    apply uv.eq_if
    simp
    apply List.add_commutative
  add_assoc (a b c) := by
    apply uv.eq_if
    simp [uv.reduce]
    apply List.add_is_associative


theorem List.convolve_any_cons
  {k : Type u}
  [Z : Pointed_Zero k] [A : Additive k] [Pointed_Multiplicative_Identity k] [Multiplicative k]
  (reduce : k → k)
  [Idempotent_Reduction reduce]
  [Commutative_Additive_Reduction reduce]
  (P : k → Bool)
  [ZP : Zero_Predicate P]
  [PR : Predicated_Reduction reduce P]
  [AP : Additive_Predicate P]
  [AZPR : Add_Zero_Predicate_Reduction reduce P]
  (a : List k)
  (x : k)
  (b : List k)  :
  List.reduce reduce P (convolve a (x :: b))
  = List.reduce reduce P (add (action.right a x) (shift (convolve a b)))
  := by
  match a with
  | [] =>
    simp
    rw [shift, reduce_singleton, PR.erase, ZP.zero_true]
    rfl
  | x' :: a' =>
    rw[convolve]
    rw[
      ←List.reduce_add,
        ←action.left.cons_linear,
        shift_reduce,
          convolve_any_cons,
        ← shift_reduce,
      ←reduce_add
    ]
    rw [shift.add]
    rw [reduce_add]
    rw [reduce_add]
    rw [add_is_associative]

    rw [←reduce_add]
    conv in List.reduce reduce P (σ(_) +₀ (_ +₀ _)) =>
      rw [←add_is_associative]
      rw [←reduce_add]
      arg 3
      arg 1
      rw [add_commutative]
      rfl

    -- rw [reduce_add]
    conv in List.reduce reduce P (List.reduce reduce P (_ +₀ _) +₀ List.reduce reduce P (_)) =>
      rw [reduce_add]
      rfl

    rw [add_is_associative]
    conv in List.reduce reduce P ((σ(_) +₀ (σ(_) +₀ σ(_)))) =>
      rw [←reduce_add]
      rw [add_shift_shift]
      rw [←List.convolve]
      rw [reduce_add]
      rfl

    rw [reduce_add]
    rw [←add_is_associative]

    rw [←reduce_add, action.right.cons_linear, reduce_add]
    apply ZP.zero_true
    apply ZP.zero_true


theorem List.action.left_eq_right
  {k : Type u}
  [Z : Pointed_Zero k] [A : Additive k] [Pointed_Multiplicative_Identity k] [Multiplicative k]
  (reduce : k → k)
  [Idempotent_Reduction reduce]
  [CMR : Commutative_Multiplicative_Reduction reduce]
  (P : k → Bool)
  (a : List k) (s : k)
  : List.reduce reduce P (action.left s a) = List.reduce reduce P (action.right a s)
  := by
  match a with
  | [] => simp
  | ha :: ta =>
    have hi := List.action.left_eq_right reduce P ta s
    rw [action.left, action.right]
    rw [action.left, action.right] at hi
    rw [List.map, List.map]
    rw [List.reduce_tail, hi, ← List.reduce_tail]
    rw [List.reduce_head, CMR.mul_commutative, ← List.reduce_head]

theorem List.convolve_commutative
  {k : Type u}
  [Z : Pointed_Zero k] [A : Additive k] [Pointed_Multiplicative_Identity k] [Multiplicative k]
  (reduce : k → k)
  [Idempotent_Reduction reduce]
  [CMR : Commutative_Multiplicative_Reduction reduce]
  [CAR : Commutative_Additive_Reduction reduce]
  (P : k → Bool)
  [ZP : Zero_Predicate P]
  [AP : Additive_Predicate P]
  [Predicated_Reduction reduce P]
  [AZPR : Add_Zero_Predicate_Reduction reduce P]
  (a : List k) (b : List k)
  :
  List.reduce reduce P (convolve a b) = List.reduce reduce P (convolve b a)
  := by
  match a with
  | [] =>
    simp
  | x :: a' =>
    have hi := List.convolve_commutative reduce P a' b
    rw [convolve, convolve_any_cons]
    rw [←reduce_add, action.left_eq_right, reduce_add]
    rw [
      ←reduce_add,
        shift_reduce,
          hi,
        ← shift_reduce,
      reduce_add,
    ]

theorem List.action.left.left_linear
  {k : Type u}
  [R : Potential_Ring k]
  (reduce : k → k) (P : k → Bool)
  [BR : Best_Reduction reduce]
  (x y : k) (a : List k) :
  List.reduce reduce P (action.left (R.add x y) a)
  =
  List.reduce reduce P (add (action.left x a) (action.left y a))
  := by
  repeat rw [action.left]
  match a with
  | [] => simp
  | xa :: a' =>
    have hi := List.action.left.left_linear reduce P x y a'
    simp_all [action.left]
    rw [add]
    rw [reduce_head, BR.mul_add_any x y xa, ← reduce_head]
    rw [reduce_tail, hi, ← reduce_tail]


theorem List.action.left.right_linear
  {k : Type u}
  [R : Potential_Ring k]
  (reduce : k → k) (P : k → Bool)
  [BR : Best_Reduction reduce]
  (x : k) (a b : List k) :
  List.reduce reduce P (action.left x (add  a b) )
  =
  List.reduce reduce P (add (action.left x a) (action.left x b))
  := by
  repeat rw [action.left]
  match a, b with
  | [], _ => simp
  | _, [] => simp
  | xa :: a, xb :: b =>
    have hi := List.action.left.right_linear reduce P x a b
    simp_all [List.map_cons, add, action.left]
    rw [reduce_head, BR.mul_any_add x xa xb, ← reduce_head]
    rw [reduce_tail, hi, ← reduce_tail]

theorem List.convolve_add_any
  {k : Type u}
  [R : Potential_Ring k]
  (reduce : k → k) (P : k → Bool)
  [BR : Best_Reduction reduce]
  [PR : Predicated_Reduction reduce P]
  [AP : Additive_Predicate P]
  [ZP : Zero_Predicate P]
  [AZPR : Add_Zero_Predicate_Reduction reduce P]
  (a b c : List k) :
  List.reduce reduce P (add ( convolve a c ) ( convolve b c ) )
  =
  List.reduce reduce P (convolve ( add a b ) c)
  := by
  match a, b with
  | [], b => simp
  | a, [] => simp
  | xa :: a', xb :: b' =>
    have hi := List.convolve_add_any reduce P a' b'
    symm
    rw [add, convolve]
    rw [←reduce_add, shift_reduce, ←hi, ← shift_reduce, reduce_add]
    rw [
      ←reduce_add,
      action.left.left_linear,
      reduce_add
    ]
    rw [← reduce_add]
    rw [shift.add]
    rw[reduce_add]

    rw [
      Reduced_associative_switch
      (List.add)
      (List.reduce reduce P)
      (List.reduce_add reduce P) (List.add_commutative reduce P)
      (List.add_is_associative reduce P)
      (xa∘→c) (xb∘→c) (σ(a'*₀c)) (σ(b'*₀c))
      ]
    rw [←convolve]
    rw [←convolve]

theorem List.action.left.reduce_right
  {k : Type u}
  [R : Potential_Ring k]
  (reduce : k → k) (P : k → Bool)
  [BR : Best_Reduction reduce]
  [ZP : Zero_Predicate P]
  [AP : Additive_Predicate P]
  [MP : Multiplicative_Predicate P]
  [PR : Predicated_Reduction reduce P]
  (x : k) (a : List k) :
  List.reduce reduce P (action.left x ( List.reduce reduce P a))
  =
  List.reduce reduce P (action.left x a)
  := by
  match a with
  | [] => simp
  | ha :: ta =>
    have hi := List.action.left.reduce_right reduce P x ta
    simp_all [action.left, List.map, List.reduce_alt']
    repeat rw [apply_ite (List.map _), apply_ite (List.reduce _ _)]
    simp

    split
    · case isTrue w1 =>
      rw [←hi]
      rw [w1]
      simp
      split
      · case isTrue w2 =>
        rw [←BR.mul, PR.erase, MP.mul_right (reduce x) (reduce ha) w2]
        rfl
      · case isFalse w2 =>
        rw [List.reduce_singleton, ←BR.mul, BR.idempotent, BR.mul]
    · case isFalse w1 =>
      rw [List.reduce_tail, hi, ← List.reduce_tail]
      rw [List.reduce_alt']
      rw [←BR.mul, BR.idempotent, BR.mul]

theorem List.action.left.reduce_left
  {k : Type u}
  [R : Potential_Ring k]
  (reduce : k → k) (P : k → Bool)
  [BR : Best_Reduction reduce]
  [ZP : Zero_Predicate P]
  [AP : Additive_Predicate P]
  [MP : Multiplicative_Predicate P]
  [PR : Predicated_Reduction reduce P]
  (x : k) (a : List k) :
  List.reduce reduce P (action.left (reduce x) a)
  =
  List.reduce reduce P (action.left x a) := by
  match a with
  | [] => simp
  | ha :: ta =>
    have hi := List.action.left.reduce_left reduce P x ta
    simp_all [action.left]
    rw [reduce_tail, hi, ←reduce_tail]
    rw [reduce_head, ←BR.mul, BR.idempotent, BR.mul,← reduce_head]


theorem List.action.left.zero
  {k : Type u}
  [R : Potential_Ring k]
  (reduce : k → k) (P : k → Bool)
  [BR : Best_Reduction reduce]
  [ZP : Zero_Predicate P]
  [Add_Zero_Predicate_Reduction reduce P]
  [AP : Additive_Predicate P]
  [MP : Multiplicative_Predicate P]
  [PR : Predicated_Reduction reduce P]
  (x : k) (a : List k) (h : P x)
  :
  List.reduce reduce P (action.left x a) = [] := by
  match a with
  | [] =>
    rw [action.left]
    simp
  | ha :: ta =>
    have hi := List.action.left.zero reduce P x ta h
    simp_all [action.left]
    rw [← PR.erase] at h
    rw [reduce_alt', hi, ←BR.mul, PR.erase, MP.mul_left (reduce x) (reduce ha) h]
    rfl


theorem List.convolve_reduce_left
  {k : Type u}
  [R : Potential_Ring k]
  (reduce : k → k) (P : k → Bool)
  [BR : Best_Reduction reduce]
  [ZP : Zero_Predicate P]
  [AZPR : Add_Zero_Predicate_Reduction reduce P]
  [AP : Additive_Predicate P]
  [MP : Multiplicative_Predicate P]
  [PR : Predicated_Reduction reduce P]
  (a : List k) (b : List k)
  :
  List.reduce reduce P
    (convolve (List.reduce reduce P a) b)
  =
    List.reduce reduce P (convolve a b)
  := by
  match a with
  | [] => simp
  | xa :: a' =>
    let hi := List.convolve_reduce_left reduce P a' b
    rw [List.reduce_alt']
    rw [apply_ite (List.convolve · _), apply_ite (List.reduce _ _)]
    rw [apply_ite (List.convolve · _), apply_ite (List.reduce _ _)]
    simp
    simp_all [convolve]
    rw [shift]
    rw [add_any_zero reduce P _ ZP.zero_true]
    rw [←reduce_add, shift_reduce, hi, ← shift_reduce, reduce_add]
    split
    · case isTrue w1 =>
      split <;> (
        rw [←reduce_add, shift_reduce, ←hi, w1, convolve]; simp[shift];
        rw [List.reduce_singleton, PR.erase, ZP.zero_true]
      )
      · case isTrue w2 =>
        rw [PR.erase] at w2
        rw [action.left.zero reduce P xa b w2]
        simp
      · case isFalse w2 =>
        simp
        rw [List.reduce_idempotent]
        rw [action.left.reduce_left]
        apply BR.idempotent
    · case isFalse w1 =>
      rw [←reduce_add, action.left.reduce_left, reduce_add]
    apply PR.erase


theorem List.convolve_reduce_right
  {k : Type u}
  [R : Potential_Ring k]
  (reduce : k → k) (P : k → Bool)
  [BR : Best_Reduction reduce]
  [ZP : Zero_Predicate P]
  [AZPR : Add_Zero_Predicate_Reduction reduce P]
  [AP : Additive_Predicate P]
  [MP : Multiplicative_Predicate P]
  [PR : Predicated_Reduction reduce P]
  (a : List k) (b : List k)
  :
  List.reduce reduce P (convolve a (List.reduce reduce P b))
  =
  List.reduce reduce P (convolve a b)
  := by
  match a with
  | [] => simp
  | ha :: ta =>
    have hi := List.convolve_reduce_right reduce P ta b
    symm
    rw [
      convolve,
        ←reduce_add,
          ←action.left.reduce_right,
          shift_reduce,
            ← hi,
          ← shift_reduce,
        reduce_add,
      ← convolve
    ]

  theorem List.convolve_reduce
  {k : Type u}
  [R : Potential_Ring k]
  (reduce : k → k) (P : k → Bool)
  [BR : Best_Reduction reduce]
  [ZP : Zero_Predicate P]
  [AZPR : Add_Zero_Predicate_Reduction reduce P]
  [AP : Additive_Predicate P]
  [MP : Multiplicative_Predicate P]
  [PR : Predicated_Reduction reduce P]
  (a : List k) (b : List k)
  :
  List.reduce reduce P (convolve (List.reduce reduce P a) (List.reduce reduce P b))
  =
  List.reduce reduce P (convolve a b) := by
  rw [convolve_reduce_left, convolve_reduce_right]

theorem List.action.left.left_associative
  {k : Type u}
  [R : Potential_Ring k]
  (reduce : k → k) (P : k → Bool)
  [BR : Best_Reduction reduce]
  [ZP : Zero_Predicate P]
  [AZPR : Add_Zero_Predicate_Reduction reduce P]
  [AP : Additive_Predicate P]
  [MP : Multiplicative_Predicate P]
  [PR : Predicated_Reduction reduce P]
  (a b : k) (c : List k) :
  List.reduce reduce P (action.left (R.mul a b) c)
  =
  List.reduce reduce P (action.left a (action.left b c)) := by
  match c with
  | [] => simp [action.left]
  | hc :: tc =>
    have hi := List.action.left.left_associative reduce P a b tc
    rw [
      action.left,
        List.map,
          reduce_tail,
            ← action.left,
              hi,
            action.left,
          ←reduce_tail,
          reduce_head,
            BR.mul_assoc,
          ← reduce_head,
        ← List.map,
        action.left,
          ← List.map,
        ← action.left,
      ← action.left
    ]

theorem List.action.left.shift
  {k : Type u}
  [R : Potential_Ring k]
  (reduce : k → k) (P : k → Bool)
  [BR : Best_Reduction reduce]
  [ZP : Zero_Predicate P]
  [PR : Predicated_Reduction reduce P]
  (a : k) (b : List k) :
  List.reduce reduce P (shift (action.left a b))
  =
  List.reduce reduce P (action.left a (shift b)) := by
    simp [List.shift, action.left]
    rw [reduce_alt']
    rw [reduce_alt']
    rw [PR.erase, ZP.zero_true]
    simp
    rw [PR.erase]
    split <;> simp

theorem List.action.left.right_associative
  {k : Type u}
  [R : Potential_Ring k]
  (reduce : k → k) (P : k → Bool)
  [BR : Best_Reduction reduce]
  [ZP : Zero_Predicate P]
  [AZPR : Add_Zero_Predicate_Reduction reduce P]
  [AP : Additive_Predicate P]
  [MP : Multiplicative_Predicate P]
  [PR : Predicated_Reduction reduce P]
  (a : k) (b : List k) (c : List k) :
  List.reduce reduce P (convolve (action.left a b) c)
  =
  List.reduce reduce P (action.left a (convolve b c))
  := by
  match b with
  | [] =>
    simp_all [action.left]
  | hb :: tb =>
    have hi := List.action.left.right_associative reduce P a tb

    rw [
      action.left, List.map, ←action.left,
      convolve,
      ←reduce_add,
        shift_reduce,
          hi,
        ←shift_reduce,
      reduce_add
    ]

    symm
    rw[
      convolve,
      action.left.right_linear,
      ←reduce_add,
        ←action.left.left_associative,
      reduce_add
    ]
    rw [
      ←reduce_add,
      ←List.action.left.shift,
      reduce_add
    ]

theorem List.convolve_assoc
  {k : Type u}
  [R : Potential_Ring k]
  (reduce : k → k) (P : k → Bool)
  [BR : Best_Reduction reduce]
  [ZP : Zero_Predicate P]
  [AZPR : Add_Zero_Predicate_Reduction reduce P]
  [AP : Additive_Predicate P]
  [MP : Multiplicative_Predicate P]
  [PR : Predicated_Reduction reduce P]
  (a : List k) (b : List k) (c : List k) :
  List.reduce reduce P (convolve (convolve a b) c)
  =
  List.reduce reduce P (convolve a (convolve b c))
  := by
  match a with
  | [] => simp
  | x :: a' =>
    rw [convolve]
    -- rw [mul_poly]
    rw [←convolve_add_any]
    rw [shift, convolve, convolve]
    conv => rhs; rw [←reduce_add]
    conv => lhs; rw [←reduce_add]
    congr 2
    · case e_a.e_a =>
      rw [action.left.right_associative]
    · case e_a.e_b =>
      rw [
        ←reduce_add,
        action.left.zero,
        add_nil_any,
        shift_reduce,
          convolve_assoc,
        ← shift_reduce
      ]
      apply List.reduce_idempotent
      exact fun q => Idempotent_Reduction.idempotent q
      apply ZP.zero_true



-- FINAL STEPS


instance uv.is_Potential_Ring
  (k : Type u) [R : Potential_Ring k]
  : Potential_Ring (uv k) where
  add_inverse := uv.add_inverse

@[simp]
theorem uv.add_inverse_rw (k : Type u) [R : Potential_Ring k] : (uv.is_Potential_Ring k).add_inverse = uv.add_inverse := by rfl

instance uv.reduce.is_good
  {k : Type u}
  (reduce : k → k)
  (P : k → Bool)
  [Potential_Ring k]
  [Best_Reduction reduce]
  [AP : Additive_Predicate P]
  [Multiplicative_Predicate P]
  [ZP : Zero_Predicate P]
  [PR : Predicated_Reduction reduce P]
  [Add_Zero_Predicate_Reduction reduce P]
  : Good_Reduction (uv.reduce reduce P) where
  mul (a b) := by
    apply uv.eq_if
    simp [uv.reduce, uv.mul]
    rw [List.convolve_reduce]
  mul_assoc (a b c) := by
    apply uv.eq_if
    simp [uv.reduce, uv.mul]
    rw [List.convolve_assoc]
  mul_commutative (a b) := by
    apply uv.eq_if
    simp [uv.reduce, uv.mul]
    rw [List.convolve_commutative]
  mul_any_e (a) := by
    apply uv.eq_if
    simp [uv.reduce, uv.mul, uv.e]
  mul_e_any (a) := by
    apply uv.eq_if
    simp [uv.reduce, uv.mul, uv.e]
    rw [List.convolve_e_any]
    apply PR.erase
    apply ZP.zero_true

instance uv.reduce.is_best
  {k : Type u}
  (reduce : k → k)
  (P : k → Bool)
  [Potential_Ring k]
  [Best_Reduction reduce]
  [AP : Additive_Predicate P]
  [Multiplicative_Predicate P]
  [ZP : Zero_Predicate P]
  [PR : Predicated_Reduction reduce P]
  [Add_Zero_Predicate_Reduction reduce P]
  : Best_Reduction (uv.reduce reduce P) where
  add_any_zero := (uv.reduce.is_good reduce P).add_any_zero
  add_zero_any := (uv.reduce.is_good reduce P).add_zero_any
  add_commutative := (uv.reduce.is_good reduce P).add_commutative
  add_assoc := (uv.reduce.is_good reduce P).add_assoc
  mul_any_e := (uv.reduce.is_good reduce P).mul_any_e
  mul_e_any := (uv.reduce.is_good reduce P).mul_e_any
  mul_commutative := (uv.reduce.is_good reduce P).mul_commutative
  mul_assoc := (uv.reduce.is_good reduce P).mul_assoc
  mul_add_any (a b c) := by
    apply uv.eq_if
    simp [uv.reduce, uv.mul]
    rw [List.convolve_add_any]
  mul_any_add (a b c) := by
    conv => lhs ; rw [(uv.reduce.is_good reduce P).mul_commutative]
    conv =>
      rhs
      rw [←(uv.reduce.is_good reduce P).add]
      rw[(uv.reduce.is_good reduce P).mul_commutative]
      arg 3
      arg 2
      rw[(uv.reduce.is_good reduce P).mul_commutative]

    rw [(uv.reduce.is_good reduce P).add]
    apply uv.eq_if
    simp [uv.reduce, uv.mul]
    rw [←List.convolve_add_any]
  add_add_inverse_self (a) := by
    apply uv.eq_if
    simp [uv.reduce, uv.add, uv.add_inverse]
    rw [List.inverse_is_left_inverse]
    apply PR.erase
    apply ZP.zero_true

@[simp]
def uv.beq  (k : Type u) [BEq k] (a b : uv k) := a.data == b.data

instance uv.is_BEq (k : Type u) [BEq k]  : BEq (uv k) where
  beq (a b) := a.data == b.data

@[simp]
theorem uv.beq_rw (k : Type u) [BEq k] : (uv.is_BEq k).beq = uv.beq k := by rfl

instance uv.is_LawfulBEq (k : Type u) [BEq k] [LawfulBEq k]  : LawfulBEq (uv k) where
  rfl  := by
    intro a
    simp[uv.beq]
  eq_of_beq := by
    intro a b h
    simp_all [uv.beq]
    apply uv.eq_if
    exact h


instance uv_Container.respectful
  {k : Type u} [BEq k] [LawfulBEq k] [Potential_Ring k]
  (reduce : k → k) (P : k → Bool)
  [Potential_Ring k]
  [Best_Reduction reduce]
  [AP : Additive_Predicate P]
  [Multiplicative_Predicate P]
  [ZP : Zero_Predicate P]
  [PR : Predicated_Reduction reduce P]
  [Add_Zero_Predicate_Reduction reduce P]
  : Respectful_Predicate (fun (x : Reduced_Container (uv.reduce reduce P)) ↦ x == ⟨0⟩) where
  add (a b ha hb) := by
    have ha' := LawfulBEq.eq_of_beq ha
    rw [ha']
    have hb' := LawfulBEq.eq_of_beq hb
    rw [hb']
    apply beq_of_eq
    apply add_zero_any
  mul_left (a b h) := by
    have h' := LawfulBEq.eq_of_beq h
    rw [h']
    apply beq_of_eq
    apply mul_zero_any
  mul_right (a b h) := by
    have h' := LawfulBEq.eq_of_beq h
    rw [h']
    apply beq_of_eq
    apply mul_any_zero
  zero_true := by
    simp


structure Polynomial_Package where
  k : Type u
  ring_structure : Potential_Ring k
  reduce : k → k
  best_reduce : Best_Reduction reduce
  P : k → Bool
  P_respectful : Respectful_Predicate P
  PR : Predicated_Reduction reduce P
  AZPR : Add_Zero_Predicate_Reduction reduce P
  is_beq : BEq k
  is_lawful : LawfulBEq k


instance uv.reduce_azpr {k : Type u} [Additive k] [BEq k] [LawfulBEq k]
  (reduce : k → k) (P : k → Bool) : Add_Zero_Predicate_Reduction (uv.reduce reduce P) (· == ⟨0⟩) where
  add_any_zero (a b h) := by
    simp_all [uv.zero, uv.beq]
  add_zero_any := by
    simp_all [uv.zero, uv.beq]


def chain_of_container_containers
  {k : Type u} [ring : Potential_Ring k] [is_beq : BEq k] [law : LawfulBEq k]
  (reduce : k → k) (P : k → Bool)
  [BR : Best_Reduction reduce]
  [RP : Respectful_Predicate P]
  [PR : Predicated_Reduction reduce P]
  [AZPR  : Add_Zero_Predicate_Reduction reduce P]
  (n : Nat)
  : Polynomial_Package := match n with
  | 0 => {
    k := k
    reduce := reduce
    P := P
    is_beq := is_beq
    is_lawful := law
    ring_structure := ring
    best_reduce := BR
    P_respectful := RP
    PR := PR
    AZPR := AZPR
  }
  | x + 1 =>
    let prev := chain_of_container_containers reduce P x
    let _ : BEq prev.k := prev.is_beq
    let _ : Potential_Ring prev.k := prev.ring_structure
    let _ : Best_Reduction prev.reduce := prev.best_reduce
    let _ : Respectful_Predicate prev.P := prev.P_respectful
    let _ : Predicated_Reduction prev.reduce prev.P := prev.PR
    let _ : Add_Zero_Predicate_Reduction prev.reduce prev.P := prev.AZPR
    let _ : LawfulBEq prev.k := prev.is_lawful
    let _ : Ring (Reduced_Container (uv.reduce prev.reduce prev.P)) := Reduced_Container.is_ring _
    {
      k := Reduced_Container (uv.reduce prev.reduce prev.P)
      reduce := (.)
      P (a) := a == ⟨0⟩
      is_beq := Reduced_Container.is_BEq (uv.reduce prev.reduce prev.P)
      ring_structure := Ring_Potential _
      best_reduce := Ring_Identity_Best_Reduction (Reduced_Container (uv.reduce prev.reduce prev.P))
      P_respectful := Ring_Zero_Respectful (Reduced_Container (uv.reduce prev.reduce prev.P))
      PR := inferInstance
      AZPR := inferInstance
      is_lawful := inferInstance
    }

def List.eval_polynomial
  {base : Type v} [Ring base]
  {target : Type u} [Ring target]
  (eval_x : target) (f : Ring_hom₁ base target) (a : List base)
  : target
  :=
  match a with
  | [] => Pointed_Zero.zero
  | xa :: a' => f.original_function xa ⊹ eval_x ⋆ (eval_polynomial eval_x f a')


theorem List.eval_polynomial_reduce
  {base : Type v} [Rb : Ring base] [BEq base] [LawfulBEq base]
  {target : Type u} [Rt : Ring target]
  (eval_x : target) (f : Ring_hom₁ base target)
  (x : List base) :
  eval_polynomial eval_x f (List.reduce (·) (· == Pointed_Zero.zero) x) = eval_polynomial eval_x f x
  := by
  match x with
  | [] => simp
  | xi :: x' =>
    rw [eval_polynomial]
    conv =>
      rhs
      rw [←eval_polynomial_reduce]
      rfl
    simp [List.reduce, trim_utilities.tail]
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

theorem List.eval_polynomial_add
  {base : Type v} [Ring base] [BEq base] [LawfulBEq base]
  {target : Type u} [Ring target]
  (eval_x : target) (f : Ring_hom₁ base target)
  (x y : List base)
  : eval_polynomial eval_x f (add x y) = (eval_polynomial eval_x f x) ⊹ (eval_polynomial eval_x f y)
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
    rw [Additive_Monoid.add_is_assoc]
    conv =>
      rhs
      arg 2
      arg 2
      rw [Commutative_Additive_Monoid.add_is_comm]
    conv =>
      rhs
      arg 2
      rw [←Additive_Monoid.add_is_assoc]
    rw [←Ring.mul_is_linear_right]
    rw [←eval_polynomial_add]
    rw [←Additive_Monoid.add_is_assoc]
    rw [Commutative_Additive_Monoid.add_is_comm]
    rw [←Additive_Monoid.add_is_assoc]
    rw [←Additive_Monoid_hom₁.map_add]
    rw [←eval_polynomial]
    rw [Commutative_Additive_Monoid.add_is_comm]
    rw [add_cons_cons]

@[simp]
theorem List.eval_polynomial_nil
  {base : Type v} [Ring base] [BEq base] [LawfulBEq base]
  {target : Type u} [Ring target]
  (eval_x : target) (f : Ring_hom₁ base target)
  : eval_polynomial eval_x f ([]) = ⟨0⟩ :=by
  rw [eval_polynomial]

@[simp]
theorem List.eval_polynomial_shift
  {base : Type v} [Ring base] [BEq base] [LawfulBEq base]
  {target : Type u} [Ring target]
  (eval_x : target) (f : Ring_hom₁ base target) (x : List base)
  : eval_polynomial eval_x f (shift x) = eval_x ⋆ eval_polynomial eval_x f x :=by
  rw [shift, eval_polynomial]
  simp


@[simp]
theorem List.eval_polynomial_action_left
  {base : Type v} [B : Ring base] [BEq base] [LawfulBEq base]
  {target : Type u} [T : Ring target]
  (eval_x : target) (f : Ring_hom₁ base target) (s : base) (x : List base)
  : eval_polynomial eval_x f (action.left s x) = (f.original_function s) ⋆ eval_polynomial eval_x f x :=by
  match x with
  | [] =>
    simp
  | hx :: tx =>
    have hi := eval_polynomial_action_left eval_x f s tx
    rw [←action.left.cons, eval_polynomial_add]
    rw [eval_polynomial_shift]
    rw [hi]
    simp [eval_polynomial]
    rw [Ring.mul_is_linear_right]
    congr 1
    exact f.map_mul s hx
    repeat rw [←T.mul_is_assoc]
    congr 1
    apply T.mul_is_comm

theorem List.eval_polynomial_convolve
  {base : Type v} [Ring base] [BEq base] [LawfulBEq base]
  {target : Type u} [Ring target]
  (eval_x : target) (f : Ring_hom₁ base target)
  (x y : List base)
  :
  (eval_polynomial eval_x f x) ⋆ (eval_polynomial eval_x f y)
  = eval_polynomial eval_x f (convolve x y)
  := by
  match x with
  | [] => simp
  | hx :: tx =>
    have hi := List.eval_polynomial_convolve eval_x f tx y
    rw [eval_polynomial]
    rw [Ring.mul_is_linear_left]
    rw [Multiplicative_Monoid.mul_is_assoc]
    rw [hi]
    rw [convolve, eval_polynomial_add, eval_polynomial_shift]
    rw [eval_polynomial_action_left]

@[simp]
theorem List.eval_polynomial_scalar
  {base : Type v} [Ring base] [BEq base] [LawfulBEq base]
  {target : Type u} [Ring target]
  (eval_x : target) (f : Ring_hom₁ base target)
  (x : base):
  eval_polynomial eval_x f [x] = f.original_function x := by
  simp [eval_polynomial]

def List.eval_polynomial_arrow
  {base : Type v} [Ring base] [BEq base] [LawfulBEq base]
  {target : Type} [Ring target]
  (f : Ring_hom₁ base target) (eval_x : target)
  : Unreduced_Ring_Hom (uv base) target (uv.reduce (·) (· == ⟨0⟩)) where
  mapping (a) := List.eval_polynomial eval_x f a.data
  map_zero := by simp
  map_e := by simp [uv.e, f.map_e]
  map_add := by simp [eval_polynomial_add]
  map_mul := by simp [uv.mul, eval_polynomial_convolve]
  map_reduce := by simp [uv.reduce, eval_polynomial_reduce]

@[simp]
theorem List.eval_polynomial_arrow_valid
  {base : Type v} [Ring base] [BEq base] [LawfulBEq base]
  {target : Type} [Ring target]
  (f : Ring_hom₁ base target) (eval_x : target) (a : base):
  (eval_polynomial_arrow f eval_x).mapping {data := [a]} = f.original_function a := by
    simp [List.eval_polynomial_arrow, List.eval_polynomial_scalar]


  -- {
  --   original_function (x) := eval_polynomial eval_x f x.value.data
  --   map_add (a b) := by
  --     simp


  --     rw [Reduced_Container.eq_if]
  --     rw [eval_polynomial_add]
  --     rw [polynomial_Ring_add]
  --     rw [add_reduced_poly]
  --     simp_all
  --     rw [add_poly_safe]
  --     rw [←add_poly.trim]
  --     rw [eval_polynomial_ignores_trim]
  --     rw [eval_polynomial_add]
  --   map_zero := by
  --     simp [eval_polynomial]
  --   map_e := by
  --     rw [polynomial_Ring_e]
  --     rw [eval_polynomial_ignores_trim]
  --     rw [eval_polynomial]
  --     rw [eval_polynomial]
  --     simp_all
  --     apply f.map_e
  --   map_mul := by
  --     intro a b
  --     rw [polynomial_Ring_mul]
  --     rw [mul_reduced_poly]
  --     simp
  --     rw [mul_poly_safe]
  --     simp [eval_polynomial_mul]
  -- }

@[simp]
def base_inclusion
  {base : Type v} [BEq base] [LawfulBEq base] [Ring base]
  (x : base) : Reduced_Container (uv.reduce (·) (· == (⟨0⟩ : base))):=
  {
    value := uv.reduce (·) (· == (⟨0⟩ : base)) { data := [x] }
    reduced := by rw [(uv.reduce.is_idempotent (·) (· == (⟨0⟩ : base))).idempotent]
  }

def stupidity : ({data := x} : uv k).data = x := by rfl

@[simp]
theorem List.reduce_zero {base : Type v} [BEq base] [LawfulBEq base] [Ring base] :
  List.reduce (·) (· == (⟨0⟩ : base)) ([⟨0⟩]) = [] := by
  rw [reduce, trim_utilities.tail.eq_def]
  simp

def inclusion_base_to_free_algebra
  {base : Type v} [BEq base] [LawfulBEq base] [Ring base]
  : Ring_hom₁ base (Reduced_Container (uv.reduce (·) (· == (⟨0⟩ : base)))) where
  original_function := base_inclusion
  map_add (a b):= by
    apply Reduced_Container.eq_if
    apply uv.eq_if
    simp [uv.reduce, Reduced_Container.add, List.reduce_add, List.add]
  map_zero := by
    simp [base_inclusion, Reduced_Container.zero, uv.reduce, List.reduce]
  map_e := by
    simp [base_inclusion, Reduced_Container.e, uv.reduce, List.reduce]
    rfl
  map_mul (a b) := by
    apply Reduced_Container.eq_if
    apply uv.eq_if
    simp [uv.reduce, Reduced_Container.mul, uv.mul]
    if a == ⟨0⟩ then
      simp_all
    else
      if b == ⟨0⟩ then
        simp_all
      else
        simp_all
        rw [List.convolve_reduce (·) (· == (⟨0⟩ : base)), List.action.left.from_convolve (·) (· == (⟨0⟩ : base)), List.action.left, List.map, List.map]
        repeat simp


instance free_algebra_over_ring
  {base : Type v} [Ring base] [BEq base] [LawfulBEq base]
  : free_algebra base (Reduced_Container (uv.reduce (·) (· == (⟨0⟩ : base)))) :=
  {
    var := {
      value := (uv.reduce (·) (· == (⟨0⟩ : base))) { data := [⟨0⟩, ⟨1⟩] }
      reduced := by apply Idempotent_Reduction.idempotent
    }
    induced_map f fx := reduce_Unreduced_Ring_Hom (List.eval_polynomial_arrow f fx)
    induced_map_is_valid := by
      intro target target_ring f fx
      simp [reduce_Unreduced_Ring_Hom_valid]
      rw [List.eval_polynomial_arrow]
      rw [←List.shift]
      simp [f.map_e]
  }

structure Ring_Package where
  k : Type u
  ring_structure : Ring k
  is_beq : BEq k
  is_lawful : LawfulBEq k
  var_name : String

def mv
  (k : Type u) [ring : Ring k] [BEq k] [LawfulBEq k]
  (n : Nat) (var_name : String)
  : Ring_Package := match n with
  | 0 => {
    k := k
    ring_structure := inferInstance
    is_beq := inferInstance
    is_lawful := inferInstance
    var_name := var_name ++ n.toSubscriptString
  }
  | x + 1 =>
    let prev := mv k x var_name
    let _ : Ring prev.k := prev.ring_structure
    let _ : BEq prev.k := prev.is_beq
    let _ : LawfulBEq prev.k := prev.is_lawful
    {
      k := Reduced_Container (uv.reduce (·) (· == (⟨0⟩ : prev.k)))
      ring_structure := inferInstance
      is_beq := inferInstance
      is_lawful := inferInstance
      var_name := var_name ++ n.toSubscriptString
    }

instance mv.is_ring (k : Type u) [ring : Ring k] [BEq k] [LawfulBEq k] (n : Nat) (X : String)
  : Ring (mv k n X).k := by
  let _ := (mv k n X).ring_structure
  infer_instance

instance mv.is_beq (k : Type u) [ring : Ring k] [BEq k] [LawfulBEq k] (n : Nat) (X : String)
  : BEq (mv k n X).k := by
  let _ := (mv k n X).is_beq
  infer_instance

instance mv.is_lawful (k : Type u) [ring : Ring k] [BEq k] [LawfulBEq k] (n : Nat) (X : String)
  : LawfulBEq (mv k n X).k := by
  let _ := (mv k n X).is_lawful
  infer_instance

instance mv.is_iterative_algebra (k : Type u) [BEq k] [LawfulBEq k] [ring : Ring k] [BEq k] [LawfulBEq k] (n : Nat) (X : String)
  : free_algebra (mv k n X).k (mv k (n + 1) X).k := by
  rw [mv]
  apply free_algebra_over_ring



def monom_repr {k : Type u}
  [BEq k] [LawfulBEq k] [ToString k]
  (zero : k) (one : k) (power : Nat) (X: String) (x: k) (not_last : Bool)
  :=
  if x == zero then
    ""
  else
    (if power == 0 ∨ ¬x == one then ToString.toString x else "")
    ++
    (if power > 0 then X ++ Nat.toSuperscriptString power else "")
    ++
    if not_last then " + " else ""

def convert_polynomial_to_sequence
  (k : Type u)
  [BEq k] [LawfulBEq k] [ToString k] (zero : k) (one : k) (p : List k) (element : String) (power : Nat)
  : List String :=
  match p with
  | [] => []
  | [x] => [monom_repr zero one power element x False ]
  | x :: p' =>
    (monom_repr zero one power element x True)
    :: (convert_polynomial_to_sequence k zero one p' element (power + 1))

def concat_strings (a : List String) :=
  match a with
  | [] => ""
  | q :: a' => q ++ (concat_strings a')

def  convert_polynomial_to_string
  {k : Type u} [BEq k] [LawfulBEq k] [ToString k] (zero : k) (one : k) (p : List k) (element : String) (power : Nat) : String :=
  match convert_polynomial_to_sequence k zero one p element power with
  | [] => ""
  | [x] => x
  | a => "(" ++ concat_strings a ++ ")"
  -- List.toString p

def convert_mv_to_string
  {k : Type u} [R : Ring k] [TS : ToString k] [BEq k] [LawfulBEq k] {n : Nat} {X : String}
  (p : (mv k n X).k) : String := by
  match n with
  | 0 =>
    rw [mv] at p
    apply TS.toString p
  | prev_n + 1 =>
    rw [mv] at p
    let prev := mv k prev_n X
    let prev_R : Ring prev.k := prev.ring_structure
    let _ : BEq prev.k := prev.is_beq
    let _ : LawfulBEq prev.k := prev.is_lawful
    let _ : ToString (prev.k) := {
      toString (a) := convert_mv_to_string a
    }
    apply convert_polynomial_to_string prev_R.zero prev_R.e p.value.data (mv k n X).var_name 0


instance polynomial_has_string
  (k : Type u) [R : Ring k] [TS : ToString k] [BEq k] [LawfulBEq k] (n : Nat) (X : String)
  : ToString (mv k n X).k
  where
  toString (x) := convert_mv_to_string x

def mv_var (k : Type u) [ring : Ring k] [BEq k] [LawfulBEq k] (n : Nat) (i : Nat) (h : i <= n) (X : String)
  : (mv k (n + 1) X).k :=
  match n, i with
  | n, 0 => (mv.is_iterative_algebra k n X).var
  | 0, prev_i + 1 => by
    contradiction
  | prev_n + 1, prev_i + 1=> by
    rw [mv]
    simp
    apply Reduced_Container.mk (
      by
      have h : (prev_i <= prev_n) := by
        exact Nat.le_of_lt_succ h
      apply (uv.reduce (·) (· == ⟨0⟩)) (uv.mk [mv_var k prev_n prev_i h X])
    )
    apply (uv.reduce.is_idempotent (·) (· == ⟨0⟩)).idempotent


namespace Examples

@[simp]
def P_Int (a : Int) := a == 0
@[simp]
def reduce_Int (a : Int) := a

instance Int_Potential_Ring : Potential_Ring Int where
  add := Int.add
  mul := Int.mul
  e := 1
  zero := 0
  add_inverse := Int.neg


instance Z : Ring_to_String Int := {
  add := Int.add
  add_inverse := Int.neg
  mul := Int.mul
  e := 1
  zero := 0
  add_add_inverse_self := by
    simp
    intro a
    rw [Int.add_comm]
    rw [←Int.sub_self a]
    rfl
  add_is_comm :=by simp; apply Int.add_comm
  add_is_assoc := by simp; apply Int.add_assoc
  mul_is_comm := by simp; apply Int.mul_comm
  mul_is_assoc := by simp; apply Int.mul_assoc
  mul_e_any := by simp
  add_zero_any := by simp
  mul_any_e := by simp
  add_any_zero := by simp
  mul_is_linear_left :=
    by
    intro a b c
    apply Int.add_mul
  mul_is_linear_right := by
    intro a b c
    apply Int.mul_add
}



instance reduce_Int_best : Best_Reduction reduce_Int where
  add := by simp
  add_add_inverse_self := by
    intro a
    simp
    apply Int.add_left_neg
  idempotent := by simp
  add_any_zero := by apply Int.add_zero
  add_zero_any := by apply Int.zero_add
  add_commutative := by apply Int.add_comm
  add_assoc := by apply Int.add_assoc
  mul := by simp
  mul_any_e := by apply Int.mul_one
  mul_e_any := by apply Int.one_mul
  mul_commutative := by apply Int.mul_comm
  mul_assoc := by apply Int.mul_assoc
  mul_any_add := by apply Int.mul_add
  mul_add_any := by apply Int.add_mul

instance P_Int_Additive : Additive_Predicate P_Int where
  add := by simp; apply Int.add_zero

instance P_Int_Multiplicative : Multiplicative_Predicate P_Int where
  mul_left (a b h) := by simp_all; apply Int.zero_mul
  mul_right (a b h) := by simp_all; apply Int.mul_zero

instance P_Int_Zero : Zero_Predicate P_Int where
  zero_true := by simp; rfl

instance Int_Predicated_Reduction : Predicated_Reduction reduce_Int P_Int where
  erase (a) := by simp


instance Int_AZPR : Add_Zero_Predicate_Reduction reduce_Int P_Int where
  add_any_zero (a b c) := by simp_all; apply Int.add_zero
  add_zero_any (a b c) := by simp_all; apply Int.zero_add


@[reducible]
def IntX := Reduced_Container (uv.reduce reduce_Int P_Int)

def X_IntX : IntX where
  value := uv.reduce reduce_Int P_Int {
    data :=  [0, 1]
  }
  reduced := by
    rw [(uv.reduce.is_idempotent reduce_Int P_Int).idempotent]

#eval (((X_IntX) ⋆ (X_IntX) ⊹ (X_IntX)) ⋆ ((X_IntX) ⋆ (X_IntX) ⊹ (X_IntX))).value.data

def id_Int : Ring_hom₁ Int Int where
  original_function := (.)
  map_add (a b) := by rfl
  map_mul (a b) := by rfl
  map_zero := by rfl
  map_e := by rfl

#check reduce_Unreduced_Ring_Hom (List.eval_polynomial_arrow id_Int (1 : Int) )

def eval_at (x : Int) := reduce_Unreduced_Ring_Hom (List.eval_polynomial_arrow id_Int x)

#eval (eval_at 5) (X_IntX ⋆ X_IntX)

def P3 := mv Int 3 "α"

def X3 := mv_var Int 2 0 (by omega) "α"
def X2 := mv_var Int 2 1 (by omega) "α"
def X1 := mv_var Int 2 2 (by omega) "α"


#eval X1
#eval X2
#eval X3
#eval (X1  ⋆ X2) ⋆ X3
#eval (X1 ⊹ X2)
#eval (X1 ⊹ X3)
#eval (X2 ⊹ X3)
#eval X3 ⋆ (X2 ⊹ X3)
#eval X1 ⋆ (X2 ⊹ X3)
#eval (X1 ⊹ X3) ⋆ X2
#eval (X1 ⊹ X3) ⋆ X3
#eval (X1 ⊹ X3) ⋆ (X2 ⊹ X3)
#eval (X1 ⊹ X2) ⋆ (X1 ⊹ X3)
#eval (X1 ⊹ X2) ⋆ ((X1 ⊹ X3) ⋆ (X2 ⊹ X3))

end Examples

theorem a_decomposition {k : Type u} (a : List k) (x : k) : ∃ c, ∃ aq, x :: a = aq ++ [c] :=
    match a with
    | [] => ⟨ x, by simp ⟩
    | xa :: a' => by
      rcases a_decomposition a' xa with ⟨ tail, head, tail_is_okay ⟩
      rw [tail_is_okay]
      exists tail, (x :: head)

theorem add_inverse_preserves_zero {k : Type u} [BEq k] [LawfulBEq k] [R : Ring k] (x : k) : (· == R.zero) (x) ↔ (· == R.zero) (R.add_inverse x) := by
  constructor
  intro hx
  simp_all
  intro hx
  simp_all
  exact add_inverse_is_zero x hx

theorem add_inverse_is_reduced (k : Type u) [R : Ring k] [BEq k] [LawfulBEq k]
  (a : List k)
  (is_reduced : trim_utilities.tail (· == Pointed_Zero.zero) a = a)
  :
  trim_utilities.tail (· == Pointed_Zero.zero) (a.map R.add_inverse) = a.map R.add_inverse := by
  rw [trim_utilities.tail.map (· == Pointed_Zero.zero) a R.add_inverse add_inverse_preserves_zero]
  rw [is_reduced]


end List_Polynomial
