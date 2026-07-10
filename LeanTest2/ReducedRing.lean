import LeanTest2.Algebra
import LeanTest2.Trim


namespace Reduced_Ring

universe u v w
open algebra

class Idempotent_Reduction
  {k : Type u}
  (reduce: k → k) where
  idempotent (a : k) : reduce (reduce a) = reduce a


class Additive_Reduction
  {k : Type u} [Additive k]
  (reduce: k → k) where
    add (a b : k) : reduce (Additive.add (reduce a) (reduce b)) = reduce (Additive.add a b)

class Add_Zero_Reduction {k : Type u} [Pointed_Zero k] [A : Additive k]
  (reduce: k → k) where
  add_any_zero (a : k) : reduce (Additive.add a Pointed_Zero.zero) = reduce a
  add_zero_any (a : k) : reduce (Additive.add Pointed_Zero.zero a) = reduce a

attribute [simp] Add_Zero_Reduction.add_any_zero
attribute [simp] Add_Zero_Reduction.add_zero_any

class Add_Zero_Predicate_Reduction  {k : Type u} [A : Additive k]
  (reduce: k → k) (P: k → Bool) where
  add_any_zero (a b : k) (h : P b) : reduce (Additive.add a b) = reduce a
  add_zero_any (a b : k) (h : P a) : reduce (Additive.add a b) = reduce b

attribute [simp] Add_Zero_Predicate_Reduction.add_any_zero
attribute [simp] Add_Zero_Predicate_Reduction.add_zero_any

class Predicated_Reduction  {k : Type u} (reduce: k → k) (P: k → Bool) where
  erase (a) : P (reduce a) = P a

class Additive_Predicate {k : Type u} [Additive k] (P: k → Bool) where
  add (a b) (ha : P a) (hb : P b) : P (a ⊹ b)

class Multiplicative_Predicate {k : Type u} [Multiplicative k] (P: k → Bool) where
  mul_left (a b) (h : P a)  : P (a ⋆ b)
  mul_right (a b) (h : P b)  : P (a ⋆ b)

class Zero_Predicate {k : Type u} [Z : Pointed_Zero k] (P: k → Bool)  where
  zero_true : P Z.zero

class Respectful_Predicate {k : Type u}  [Additive k] [Multiplicative k][Z : Pointed_Zero k] [Z : Pointed_Zero k] (P: k → Bool)
  extends Additive_Predicate P, Multiplicative_Predicate P, Zero_Predicate P

attribute [simp] Zero_Predicate.zero_true

class Commutative_Additive_Reduction
  {k : Type u} [Pointed_Zero k]  [A : Additive k]
  (reduce: k → k) extends Additive_Reduction reduce, Add_Zero_Reduction reduce where
    add_commutative (a b : k) : reduce (Additive.add a b) = reduce (Additive.add b a)
    add_assoc (a b c : k) : reduce (A.add (A.add  a b) c) = reduce (A.add  a (A.add  b c))

-- theorem Reduced_associative_1

theorem Reduced_associative_switch
  {k : Type u}
  (addition : k → k → k)
  (reduce: k → k)
  (add : (a b : k) → reduce (addition (reduce a) (reduce b)) = reduce (addition a b))
  (add_commutative : (a b : k) → reduce (addition a b) = reduce (addition b a))
  (add_assoc : (a b c : k) → reduce (addition (addition  a b) c) = reduce (addition  a (addition  b c)))
  (a b c d : k) :
  reduce (addition (addition a b) (addition c d)) = reduce (addition (addition a c) (addition b d)) := by
    rw [add_assoc,←add,]
    conv in reduce (addition b _) =>
      rw [←add_assoc]
      rw [← add]
      arg 1; arg 1
      rw [add_commutative]
    conv => arg 1; arg 1; arg 2; rw [add]; rw [add_assoc]
    rw [add, ←add_assoc]



class Multiplicative_Reduction
  {k : Type u} [Multiplicative k]
  (reduce: k → k) where
  mul (a b : k) : reduce (Multiplicative.mul (reduce a) (reduce b)) = reduce (Multiplicative.mul a b)

class Mul_Multiplicative_Identity_Reduction
  {k : Type u} [Pointed_Multiplicative_Identity k]  [M : Multiplicative k]
  (reduce: k → k) where
  mul_any_e (a : k) : reduce (M.mul a Pointed_Multiplicative_Identity.e) = reduce a
  mul_e_any (a : k) : reduce (M.mul Pointed_Multiplicative_Identity.e a) = reduce a

class Commutative_Multiplicative_Reduction
  {k : Type u} [Pointed_Multiplicative_Identity k]  [M : Multiplicative k]
  (reduce: k → k) extends Multiplicative_Reduction reduce, Mul_Multiplicative_Identity_Reduction reduce where
  mul_commutative (a b : k) : reduce (M.mul a b) = reduce (M.mul b a)
  mul_assoc (a b c : k) : reduce (M.mul (M.mul  a b) c) = reduce (M.mul  a (M.mul  b c))

attribute [simp] Mul_Multiplicative_Identity_Reduction.mul_any_e
attribute [simp] Mul_Multiplicative_Identity_Reduction.mul_e_any

class Good_Reduction
  {k : Type u} [Pointed_Zero k] [Pointed_Multiplicative_Identity k] [Additive k] [Multiplicative k]
  (reduce: k → k)
  extends
    Idempotent_Reduction reduce,
    Commutative_Additive_Reduction reduce,
    Commutative_Multiplicative_Reduction reduce

structure Reduced_Container {k : Type u} (reduce : k → k) where
  value : k
  reduced : reduce value = value


theorem Reduced_Container.ext_iff
  (k : Type u) (reduce : k → k)
  {p q : Reduced_Container reduce} :
  p = q ↔ p.value = q.value := by
  constructor
  · intro h; simp [h]
  · intro h; cases p; cases q; simp at h; simp [h]

@[ext]
theorem Reduced_Container.eq_if
  (k : Type u) (reduce : k → k)
  {p q : Reduced_Container reduce}
  (values_are_equal : p.value = q.value) :  p = q := by
  cases p;
  cases q;
  simp at values_are_equal
  simp [values_are_equal]

theorem Reduced_Container.eq_then
  (k : Type u) (reduce : k → k)
  {p q : Reduced_Container reduce}
  (h : p = q) : p.value = q.value := by
  cases p;
  cases q;
  simp at h
  simp [h]

@[simp]
def Reduced_Container.beq (k : Type u) [BEq k] (reduce : k → k) (a b : Reduced_Container reduce)
  := a.value == b.value

instance Reduced_Container.is_BEq
  {k : Type u} (reduce : k → k) [BEq k]
  : BEq (Reduced_Container reduce) where
  beq := Reduced_Container.beq k reduce

@[simp]
instance Reduced_Container.beq_rw
  {k : Type u} (reduce : k → k) [BEq k]
  : (Reduced_Container.is_BEq reduce).beq = Reduced_Container.beq k reduce := by rfl

def Reduced_Container.beq_rfl {k : Type u} [BEq k] [R : ReflBEq k] (reduce : k → k)
  (a : Reduced_Container reduce)
  : (a == a) := by
  simp

instance Reduced_Container.is_ReflBEq
  {k : Type u} (reduce : k → k) [BEq k] [R : ReflBEq k]
  : ReflBEq (Reduced_Container reduce) where
  rfl := by intro a; apply Reduced_Container.beq_rfl reduce

instance Reduced_Container.is_LawfulBEq
  {k : Type u} (reduce : k → k) [BEq k] [R : LawfulBEq k]
  : LawfulBEq (Reduced_Container reduce) where
  eq_of_beq := by
    intro a b h
    simp_all
    apply Reduced_Container.eq_if
    apply h

def Reduced_Container.add
  {k : Type u} [A : Additive k]
  {reduce : k → k} [IR : Idempotent_Reduction reduce]
  (a b : Reduced_Container reduce) : Reduced_Container reduce where
  value := reduce (A.add a.value b.value)
  reduced := by rw [IR.idempotent]

def Reduced_Container.zero
  {k : Type u} [Pointed_Zero k]
  (reduce : k → k) [IR : Idempotent_Reduction reduce]
  : Reduced_Container reduce where
  value := reduce (Pointed_Zero.zero)
  reduced := by rw [IR.idempotent]

instance Reduced_Container.is_add_abelian
  {k : Type u} [Additive k] [Pointed_Zero k]
  (reduce : k → k) [IR : Idempotent_Reduction reduce] [CAR : Commutative_Additive_Reduction reduce] :
  Commutative_Additive_Monoid (Reduced_Container reduce) where
  add := Reduced_Container.add
  zero := Reduced_Container.zero reduce
  add_zero_any (a : Reduced_Container reduce) := by
    rw [add, zero]
    apply Reduced_Container.eq_if
    simp
    rw [←a.reduced]
    rw [CAR.add, CAR.add_zero_any]
  add_any_zero  (a : Reduced_Container reduce)  := by
    rw [add, zero]
    apply Reduced_Container.eq_if
    simp
    rw [←a.reduced]
    rw [CAR.add, CAR.add_any_zero]
  add_is_comm (a b) := by
    rw [add]
    apply Reduced_Container.eq_if
    simp
    rw [CAR.add_commutative]
    rfl
  add_is_assoc (a b c) := by
    rw[add, add, add, add]
    apply Reduced_Container.eq_if
    simp
    conv => lhs; rw [←c.reduced]
    rw [CAR.add, CAR.add_assoc]
    conv => rhs; rw[←a.reduced]
    rw [CAR.add]

@[simp]
theorem Reduced_Container.add_rw
  {k : Type u} [Additive k] [Pointed_Zero k]
  (reduce : k → k) [IR : Idempotent_Reduction reduce] [CAR : Commutative_Additive_Reduction reduce]
  (a b : Reduced_Container reduce) :
  (Reduced_Container.is_add_abelian reduce).add a b = Reduced_Container.add a b := rfl

@[simp]
theorem Reduced_Container.zero_rw
  {k : Type u} [Additive k] [Pointed_Zero k]
  (reduce : k → k) [IR : Idempotent_Reduction reduce] [CAR : Commutative_Additive_Reduction reduce]
  :
  (Reduced_Container.is_add_abelian reduce).zero = Reduced_Container.zero reduce := rfl

def Reduced_Container.mul
  {k : Type u} [M : Multiplicative k]
  {reduce : k → k} [IR : Idempotent_Reduction reduce]
  (a b : Reduced_Container reduce) : Reduced_Container reduce where
  value := reduce (M.mul a.value b.value)
  reduced := by rw [IR.idempotent]

def Reduced_Container.e
  {k : Type u} [Pointed_Multiplicative_Identity k]
  (reduce : k → k) [IR : Idempotent_Reduction reduce]
  : Reduced_Container reduce where
  value := reduce (Pointed_Multiplicative_Identity.e)
  reduced := by rw [IR.idempotent]

instance Reduced_Container.is_mul_abelian
  {k : Type u} [Multiplicative k] [Pointed_Multiplicative_Identity k]
  (reduce : k → k) [IR : Idempotent_Reduction reduce] [CMR : Commutative_Multiplicative_Reduction reduce] :
  Commutative_Multiplicative_Monoid (Reduced_Container reduce) where
  mul := Reduced_Container.mul
  e := Reduced_Container.e reduce
  mul_e_any (a : Reduced_Container reduce) := by
    rw [mul, e]
    apply Reduced_Container.eq_if
    simp
    rw [←a.reduced]
    rw [CMR.mul, CMR.mul_e_any]
  mul_any_e  (a : Reduced_Container reduce)  := by
    rw [mul, e]
    apply Reduced_Container.eq_if
    simp
    rw [←a.reduced]
    rw [CMR.mul, CMR.mul_any_e]
  mul_is_comm (a b) := by
    rw [mul]
    apply Reduced_Container.eq_if
    simp
    rw [CMR.mul_commutative]
    rfl
  mul_is_assoc (a b c) := by
    rw[mul, mul, mul, mul]
    apply Reduced_Container.eq_if
    simp
    conv => lhs; rw [←c.reduced]
    rw [CMR.mul, CMR.mul_assoc]
    conv => rhs; rw[←a.reduced]
    rw [CMR.mul]


@[simp]
theorem Reduced_Container.mul_rw
  {k : Type u} [Multiplicative k] [Pointed_Multiplicative_Identity k]
  (reduce : k → k) [IR : Idempotent_Reduction reduce] [CMR : Commutative_Multiplicative_Reduction reduce]
  (a b : Reduced_Container reduce) :
  (Reduced_Container.is_mul_abelian reduce).mul a b = Reduced_Container.mul a b := rfl

@[simp]
theorem Reduced_Container.e_rw
  {k : Type u} [Multiplicative k] [Pointed_Multiplicative_Identity k]
  (reduce : k → k) [IR : Idempotent_Reduction reduce] [CMR : Commutative_Multiplicative_Reduction reduce]
  :
  (Reduced_Container.is_mul_abelian reduce).e = Reduced_Container.e reduce := rfl

class Potential_Ring
  (k : Type u)
  extends Multiplicative k, Pointed_Multiplicative_Identity k, Additive k, Pointed_Zero k
  where
  add_inverse : k → k

instance Ring_Potential (k : Type u) [R : Ring k] : Potential_Ring k where
  add_inverse := R.add_inverse

class Best_Reduction {k : Type u} (reduce : k → k) [R : Potential_Ring k]
  extends Good_Reduction reduce where
  add_add_inverse_self (a : k) : reduce ((R.add_inverse a) ⊹ a) = reduce (R.zero)
  mul_any_add (a b c : k) : reduce (a ⋆ (b ⊹ c)) = reduce (a ⋆ b ⊹a ⋆ c)
  mul_add_any (a b c : k) : reduce ((a ⊹ b) ⋆ c) = reduce (a ⋆ c ⊹b ⋆ c)

instance Ring_Identity_Best_Reduction
  (k : Type u) [R : Ring k] : Best_Reduction ((·) : k → k) where
  add a b := by rfl
  idempotent a := by rfl
  add_add_inverse_self a := by apply R.add_add_inverse_self
  add_any_zero a := by simp
  add_assoc a b c := by apply R.add_is_assoc
  add_commutative a b := by apply R.add_is_comm
  add_zero_any a := by simp
  mul a b := by rfl
  mul_add_any a b c := by apply R.mul_is_linear_left
  mul_any_add a b c := by apply R.mul_is_linear_right
  mul_any_e a := by simp
  mul_e_any a := by simp
  mul_commutative a b := R.mul_is_comm a b
  mul_assoc a b c := R.mul_is_assoc a b c

instance Ring_Zero_Respectful
  (k : Type u) [BEq k] [LawfulBEq k] [R : Ring k] : Respectful_Predicate ((. == ⟨0⟩) : k → Bool) where
  add a b ha hb := by simp_all
  mul_left a b h := by simp_all
  mul_right a b h := by simp_all
  zero_true := by simp

instance Ring_Predicated_Reduction
  (k : Type u) [BEq k] [LawfulBEq k] [R : Ring k] : Predicated_Reduction (·) ((. == ⟨0⟩) : k → Bool) where
  erase a := by simp

instance Ring_AZPR
  (k : Type u) [BEq k] [LawfulBEq k] [R : Ring k] : Add_Zero_Predicate_Reduction (·) ((. == ⟨0⟩) : k → Bool) where
  add_any_zero := by simp
  add_zero_any a b h := by simp_all

def Reduced_Container.add_inverse
  {k : Type u} [Pointed_Zero k] (add_inverse : k → k)
  {reduce : k → k} [GR : Idempotent_Reduction reduce]
  (a : Reduced_Container reduce) : Reduced_Container reduce where
  value := reduce (add_inverse a.value)
  reduced := by rw [GR.idempotent]

instance Reduced_Container.is_ring
  {k : Type u} (reduce : k → k) [R : Potential_Ring k]
  [BR : Best_Reduction reduce]
  : Ring (Reduced_Container reduce) where
  add_inverse (a) := Reduced_Container.add_inverse R.add_inverse a
  add_add_inverse_self (a) := by
    simp
    apply Reduced_Container.eq_if
    rw [add_inverse, Reduced_Container.add]
    simp
    rw [←a.reduced, ←a.reduced, BR.add, BR.idempotent, BR.add_add_inverse_self]
    rw [Reduced_Container.zero]
  mul_is_linear_left (a b c) := by
    apply Reduced_Container.eq_if
    simp [add, mul]
    conv => lhs; rw [←c.reduced, BR.mul, BR.mul_add_any]
    rw [BR.add]
  mul_is_linear_right (a b c) := by
    apply Reduced_Container.eq_if
    simp [add, mul]
    conv => lhs; rw [←a.reduced, BR.mul, BR.mul_any_add]
    rw [BR.add]

theorem Reduced_left_inverse_is_right_inverse
  {k : Type _} (reduce : k → k)
  [R : Potential_Ring k]
  [BR : Best_Reduction reduce]
  (a : k):
  reduce (a ⊹(R.add_inverse a)) = reduce R.zero := by
  rw [BR.add_commutative]
  apply BR.add_add_inverse_self

@[simp]
theorem Reduced_mul_zero_any
  {k : Type _} (reduce : k → k)
  [R : Potential_Ring k]
  [BR : Best_Reduction reduce]
  (a : k)
  : reduce (R.mul R.zero a) = reduce R.zero
  := by
  rw [←BR.add_any_zero (R.mul R.zero a)]
  have ri := Reduced_left_inverse_is_right_inverse reduce (R.mul R.zero a)
  conv => lhs; rw [←BR.add, ← ri, BR.add]

  rw [←BR.add_assoc]
  rw [
    ←BR.add,
      ←BR.mul_add_any,
      ←BR.mul,
        BR.add_zero_any,
      BR.mul,
    BR.add
  ]
  apply ri


@[simp]
theorem Reduced_mul_any_zero
  {k : Type _} (reduce : k → k)
  [R : Potential_Ring k]
  [BR : Best_Reduction reduce]
  (a : k)
  : reduce (R.mul a R.zero) = reduce (R.zero)
  := by
  rw [BR.mul_commutative]
  apply Reduced_mul_zero_any


structure Unreduced_Ring_Hom
  (domain : Type _) [Potential_Ring domain]
  (codomain : Type _) [Potential_Ring codomain]
  (reduce : domain → domain) where
  mapping : domain → codomain
  map_e : mapping ⟨1⟩ = ⟨1⟩
  map_zero : mapping ⟨0⟩ = ⟨0⟩
  map_add (a b) : mapping (a ⊹ b) = (mapping a) ⊹ (mapping b)
  map_mul (a b) : mapping (a ⋆ b) = (mapping a) ⋆ (mapping b)
  map_reduce (a) : mapping (reduce a) = mapping (a)


attribute [simp] Unreduced_Ring_Hom.map_reduce
attribute [simp] Unreduced_Ring_Hom.map_e
attribute [simp] Unreduced_Ring_Hom.map_zero

def reduce_Unreduced_Ring_Hom
  {domain : Type _} [Potential_Ring domain]
  {codomain : Type _} [Ring codomain]
  {reduce : domain → domain}
  [BR : Best_Reduction reduce]
  (f : Unreduced_Ring_Hom domain codomain reduce)
  : Ring_hom₁ (Reduced_Container reduce) codomain where
  original_function (a) := f.mapping a.value
  map_zero := by simp [Reduced_Container.zero]
  map_e := by simp [Reduced_Container.e]
  map_add (x y) := by simp [Reduced_Container.add, f.map_add]
  map_mul (x y) := by simp [Reduced_Container.mul, f.map_mul]

theorem reduce_Unreduced_Ring_Hom_valid
  {domain : Type _} [Potential_Ring domain]
  {codomain : Type _} [Ring codomain]
  {reduce : domain → domain}
  [BR : Best_Reduction reduce]
  (f : Unreduced_Ring_Hom domain codomain reduce) (a : Reduced_Container reduce):
  (reduce_Unreduced_Ring_Hom f).original_function a = f.mapping a.value := by rfl

end Reduced_Ring
