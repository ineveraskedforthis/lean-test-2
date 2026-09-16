import LeanTest2.Category

namespace Algebra

structure RawGroup where
  G : Type _
  op : G → G → G
  identity : G
  inverse : G → G

structure AbstractGroup extends RawGroup where
  right_identity x : op x identity = x
  left_identity x : op identity x = x
  right_inverse x : op x (inverse x) = identity
  left_inverse x : op (inverse x) x = identity
  assoc x y z : op (op x y) z = op x (op y z)

attribute [simp] AbstractGroup.right_inverse
attribute [simp] AbstractGroup.left_inverse

structure Bijection (X Y : Type _) where
  forward : X → Y
  backward : Y → X
  forward_backward x : forward (backward x) = x
  backward_forward x : backward (forward x) = x

attribute [simp] Bijection.forward_backward
attribute [simp] Bijection.backward_forward

def BijectionCompose (f : Bijection X Y) (g : Bijection Y Z) : Bijection X Z where
  forward x := g.forward (f.forward x)
  backward x := f.backward (g.backward x)
  backward_forward x := by simp
  forward_backward x := by simp

def BijectionIdentity(X : Type _) : Bijection X X where
  forward x := x
  backward x := x
  backward_forward _ := rfl
  forward_backward _ := rfl

def BijectionInverse (f : Bijection X Y) : Bijection Y X where
  forward := f.backward
  backward := f.forward
  backward_forward := f.forward_backward
  forward_backward := f.backward_forward

theorem Bijection.cancel (x y : X) (f : Bijection X Y) (h : f.forward x = f.forward y) : x = y := by
  rw [←f.backward_forward x, ←f.backward_forward y, h]

def AbstractGroup.op_right_bijection (A : AbstractGroup) (g : A.G) : Bijection A.G A.G where
  forward x := A.op x g
  backward x := A.op x (A.inverse g)
  backward_forward x := by simp [A.assoc, A.right_identity]
  forward_backward x := by simp [A.assoc, A.right_identity]

def AbstractGroup.op_left_bijection (A : AbstractGroup) (g : A.G) : Bijection A.G A.G where
  forward x := A.op g x
  backward x := A.op (A.inverse g) x
  backward_forward x := by simp [←A.assoc, A.left_identity]
  forward_backward x := by simp [←A.assoc, A.left_identity]

structure AbstractGroupMorphism (A B : AbstractGroup)  where
  compute : A.G → B.G
  homo x y : compute (A.op x y) = B.op (compute x) (compute y)

def AbstractGroupMorphism.compose (f : AbstractGroupMorphism A B) (g : AbstractGroupMorphism B C) : AbstractGroupMorphism A C where
  compute x := x |> f.compute |> g.compute
  homo x y := by simp [AbstractGroupMorphism.homo]


def AbstractGroupMorphism.identity (A) : AbstractGroupMorphism A A where
  compute x := x
  homo x y := by rfl

structure AbstractGroupIsomorphism (A B : AbstractGroup) where
  forward : AbstractGroupMorphism A B
  backward : AbstractGroupMorphism B A
  forward_backward x : forward.compute (backward.compute x) = x
  backward_forward x : backward.compute (forward.compute x) = x



theorem AbstractGroup.identity_unique {A : AbstractGroup} (candidate : A.G) (a : A.G) (h : A.op candidate a = a) : candidate = A.identity := by
  rw [←A.right_identity candidate, ←A.right_inverse a, ←A.assoc, h]

theorem AbstractGroup.op_right {A : AbstractGroup} (a b c : A.G) (h : A.op a c = A.op b c) : a = b := by
  apply Bijection.cancel _ _ (AbstractGroup.op_right_bijection A c) _
  assumption
theorem AbstractGroup.op_left {A : AbstractGroup} (a b c : A.G) (h : A.op c a = A.op c b) : a = b := by
  apply Bijection.cancel _ _ (AbstractGroup.op_left_bijection A c) _
  assumption

theorem AbstractGroup.inverse_right_unique (A : AbstractGroup) (a : A.G) (candidate : A.G) (h : A.op a candidate = A.identity) : candidate = A.inverse a := by
  apply AbstractGroup.op_left _ _ (a)
  simp [h]


theorem AbstractGroupMorphism.forward_identity {A B : AbstractGroup} (f : AbstractGroupMorphism A B) : f.compute A.identity = B.identity := by
  apply AbstractGroup.identity_unique _ (f.compute A.identity)
  rw [←f.homo, A.left_identity]

theorem AbstractGroupMorphism.forward_inverse {A B : AbstractGroup} (f : AbstractGroupMorphism A B) (a : A.G) : f.compute (A.inverse a) = B.inverse (f.compute a) := by
  apply AbstractGroup.inverse_right_unique
  rw [←f.homo]
  simp [AbstractGroupMorphism.forward_identity]

def Group : Category.Category where
  Obj := AbstractGroup
  Mor := AbstractGroupMorphism
  compose := AbstractGroupMorphism.compose
  compose_identity := AbstractGroupMorphism.identity
  compose_identity_left := by simp [AbstractGroupMorphism.identity, AbstractGroupMorphism.compose]
  compose_identity_right := by simp [AbstractGroupMorphism.identity, AbstractGroupMorphism.compose]
  compose_assoc := by simp [AbstractGroupMorphism.compose]


structure ComputableGroup extends RawGroup where
  [dec : DecidableEq G]
  group_equality : G → G → Prop
  [equiv : Equivalence group_equality]
  op_eq (ha : group_equality a a') (hb : group_equality b b')  : group_equality (op a b) (op a' b')
  inverse_eq (ha : group_equality a a') : group_equality (inverse a) (inverse a')
  right_identity x : group_equality (op x identity) x
  left_identity x : group_equality (op identity x) x
  right_inverse x : group_equality (op x (inverse x)) identity
  left_inverse x : group_equality (op (inverse x) x) identity
  assoc x y z : group_equality (op (op x y) z) (op x (op y z))


def ComputableGroup.toAbstract (CG : ComputableGroup) : AbstractGroup where
  G := Quotient (Setoid.mk CG.group_equality CG.equiv)
  op := Quotient.lift₂ (fun a b => Quotient.mk _ (CG.op a b)) (by
    intro a a' b b' ha hb
    exact Quotient.sound (CG.op_eq ha hb)
  )
  inverse := Quotient.lift (fun a => Quotient.mk _ (CG.inverse a)) (by
    intro a a' ha
    exact Quotient.sound (CG.inverse_eq ha)
  )
  identity := Quotient.mk _ CG.identity
  right_identity x := by
    refine Quotient.inductionOn x ?_
    intro a
    exact Quotient.sound (CG.right_identity a)
  left_identity x := by
    refine Quotient.inductionOn x ?_
    intro a
    exact Quotient.sound (CG.left_identity a)
  right_inverse x := by
    refine Quotient.inductionOn x ?_
    intro a
    exact Quotient.sound (CG.right_inverse a)
  left_inverse x := by
    refine Quotient.inductionOn x ?_
    intro a
    exact Quotient.sound (CG.left_inverse a)
  assoc x y z := by
    refine Quotient.inductionOn x ?_
    intro a
    refine Quotient.inductionOn y ?_
    intro b
    refine Quotient.inductionOn z ?_
    intro c
    exact Quotient.sound (CG.assoc a b c)


structure ComputableGroupMap (A B : ComputableGroup)  where
  compute : A.G → B.G
  eq (x y : A.G) (h : A.group_equality x  y) : B.group_equality (compute x) (compute y)

structure ComputableGroupMorphism (A B : ComputableGroup)  where
  compute : A.G → B.G
  homo x y : B.group_equality (compute (A.op x y) ) (B.op (compute x) (compute y))
  eq (x y : A.G) (h : A.group_equality x  y) : B.group_equality (compute x) (compute y)

structure ComputableGroupBijection (A B : ComputableGroup) where
  forward : ComputableGroupMap A B
  backward : ComputableGroupMap B A
  forward_backward x : B.group_equality (forward.compute (backward.compute x))  x
  backward_forward x : A.group_equality (backward.compute  (forward.compute x)) x

structure ComputableGroupIsomorphism (A B : ComputableGroup) where
  forward : ComputableGroupMorphism A B
  backward : ComputableGroupMorphism B A
  forward_backward x : B.group_equality (forward.compute (backward.compute x))  x
  backward_forward x : A.group_equality (backward.compute  (forward.compute x)) x

def RawShiftRight {A : ComputableGroup} (g : A.G) (x : A.G) := A.op g x

theorem RawShiftRight.respect_group_equality {A : ComputableGroup} (g x y: A.G) (h : A.group_equality x y) :
  A.group_equality (RawShiftRight g x) (RawShiftRight g y) := by
  apply A.op_eq
  apply A.equiv.refl
  assumption

-- def ShiftRight {A : ComputableGroup} (g : A.G) : AbstractGroupMorphism (A.toAbstract )


-- def RawShiftRight.forward_backward {A : ComputableGroup} (g x : A.G) :
--   RawShiftRight (A.inverse g) (RawShiftRight g x)

-- def ComputableGroup.shift_right (A : ComputableGroup) (g : A.G) : ComputableGroupMap A A where
--   compute x := A.op x g
--   eq x y h := by
--     apply A.op_eq
--     assumption
--     apply A.equiv.refl

-- def ComputableGroup.shift_right_iso (A : ComputableGroup) (g : A.G) : ComputableGroupBijection A A where
--   forward := ComputableGroup.shift_right A g
--   backward := ComputableGroup.shift_right A (A.inverse g)
--   forward_backward x := by
--     simp [ComputableGroup.shift_right]



namespace Example


def S (X : Type _) : AbstractGroup where
  G := Bijection X X
  op x y := BijectionCompose x y
  identity := BijectionIdentity X
  inverse := BijectionInverse
  right_inverse x := by simp [BijectionCompose, BijectionIdentity, BijectionInverse]
  left_inverse x := by simp [BijectionCompose, BijectionIdentity, BijectionInverse]
  assoc a b c := by simp [BijectionCompose]
  right_identity x := by simp [BijectionIdentity, BijectionCompose]
  left_identity x := by simp [BijectionCompose, BijectionIdentity]

def C (n : Nat) (h : n > 0) : AbstractGroup where
  G := Fin n
  op x y := ⟨(Nat.add x y) % n, by apply Nat.mod_lt _ h ⟩
  identity := ⟨0, h⟩
  inverse x := ⟨(n - x) % n, by apply Nat.mod_lt _ h ⟩

  right_identity x := by simp; congr; apply Nat.mod_eq_of_lt x.isLt
  left_identity x := by simp; congr; apply Nat.mod_eq_of_lt x.isLt
  right_inverse x := by simp;
  left_inverse x := by simp
  assoc x := by simp [Nat.add_assoc]

end Example


end Algebra
