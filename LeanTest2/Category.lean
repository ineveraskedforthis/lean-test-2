import LeanTest2.Algebra

namespace Category

universe u v w


structure Category where
  Obj : Type u
  Mor : Obj → Obj → Type v
  compose {a b c : Obj} (x : Mor a b) (y : Mor b c) : Mor a c
  compose_identity (a : Obj) : Mor a a

  compose_identity_left (a : Obj) (b : Obj) (h : Mor a b) : compose (compose_identity a) h = h
  compose_identity_right (a : Obj) (b : Obj) (h : Mor a b) : compose h (compose_identity b) = h
  compose_assoc {a b c d : Obj} (h₁ : Mor a b) (h₂ : Mor b c) (h₃ : Mor c d) : compose (compose h₁ h₂) h₃ = compose h₁ (compose h₂ h₃)

-- attribute [simp] Category.compose_assoc

attribute [simp] Category.compose_identity_left
attribute [simp] Category.compose_identity_right

scoped notation:80 f:80 " ▸" C g:79  => Category.compose C f g

structure Functor (A B : Category) where
  obj : A.Obj → B.Obj
  mor {a b} (h : A.Mor a b) : B.Mor (obj a) (obj b)

  mor_compose : mor (A.compose h k) = B.compose (mor h) (mor k)
  mor_identity : mor (A.compose_identity a) = B.compose_identity (obj a)

-- ↻

attribute [simp] Functor.mor_identity

infix:100 " ↻ " => Functor.mor

structure Transformation (F G : Functor A B) where
  data (x : A.Obj) : B.Mor (F.obj x) (G.obj x)
  naturality {a b : A.Obj} (f : A.Mor a b) : B.compose (F.mor f) (data b) = B.compose (data a) (G.mor f)

infix:100 "ₐ " => Transformation.data


def FunctorCompose (F : Functor A B) (G : Functor B C) : Functor A C where
  obj x := G.obj (F.obj x)
  mor x := G.mor (F.mor x)

  mor_compose := by simp [F.mor_compose, G.mor_compose]
  mor_identity := by simp

infix:100 " ∘ᶠ " => FunctorCompose

def FunctorActionOnTransformation {G H : Functor A B} (τ : Transformation G H) (F : Functor B C)
  : Transformation (G ∘ᶠF) (H ∘ᶠF) where
  data x := F.mor (τ.data x)
  naturality f := by simp [FunctorCompose]; rw [←F.mor_compose, τ.naturality, F.mor_compose]

def TransformationConsumeFunctor {G H : Functor B C} (F : Functor A B) (τ : Transformation G H)
  : Transformation (F ∘ᶠG) (F ∘ᶠH) where
  data x := τ.data (F.obj x)
  naturality f := by simp [FunctorCompose]; rw [τ.naturality]


def TransformationCompose
  {F G H: Functor A B}
  (τ : Transformation F G)
  (μ : Transformation G H)
  : Transformation F H where
  data x := B.compose (τ.data x) (μ.data x)
  naturality (f) := by rw [←B.compose_assoc, τ.naturality, B.compose_assoc, μ.naturality, ←B.compose_assoc]

def TransformationIdentity (F : Functor A B) : Transformation F F where
  data x := B.compose_identity (F.obj x)
  naturality := by simp

structure Cocone (J : Type _) (C : Category) where
  c (j : J) : C.Obj
  obj : C.Obj
  i (j : J) : C.Mor (c j) obj

structure CoconeMor {J : Type _} {C : Category} (A B : Cocone J C) where
  c (j : J) : C.Mor (A.c j) (B.c j)
  obj : C.Mor A.obj B.obj

  i (j : J) : C.compose (c j) (B.i j) = C.compose (A.i j) obj

def CoconeId  {J : Type _} {C : Category}(A : Cocone J C) : CoconeMor A A where
  c (j : J) := C.compose_identity (A.c j)
  obj := C.compose_identity (A.obj)
  i (j : J) := by simp


def CoconeMorCompose {J : Type _} {T : Category} {A B C : Cocone J T} (s : CoconeMor A B) (t : CoconeMor B C) : CoconeMor A C where
  c (j : J) := T.compose (s.c j) (t.c j)
  obj := T.compose (s.obj) (t.obj)
  i (j : J) := by
    rw [T.compose_assoc, t.i j, ←T.compose_assoc, s.i j, T.compose_assoc]


def CoconeCategory (J : Type _) (Base : Category) : Category where
  Obj := Cocone J Base
  Mor (A B) := CoconeMor A B
  compose := CoconeMorCompose
  compose_identity (a) := CoconeId a

  compose_identity_left (a b h) := by simp [CoconeId, CoconeMorCompose]
  compose_identity_right (a b h) := by simp [CoconeId, CoconeMorCompose]
  compose_assoc (s t u) := by simp [CoconeMorCompose, Base.compose_assoc]

def FunctorCategory (S T : Category) : Category where
  Obj := Functor S T
  Mor (A B) := Transformation A B
  compose := TransformationCompose
  compose_identity := TransformationIdentity

  compose_identity_left := by simp [TransformationCompose, TransformationIdentity]
  compose_identity_right := by simp [TransformationCompose, TransformationIdentity]
  compose_assoc (s t u) := by simp [TransformationCompose, T.compose_assoc]

structure InitialObject (T : Category) where
  obj : T.Obj
  mor (a : T.Obj) : T.Mor obj a
  unique (a : T.Obj) (h : T.Mor obj a) : h = mor a

theorem InitialObject_iso (T : Category) (A B : InitialObject T) :
  T.compose (A.mor B.obj) (B.mor A.obj) = T.compose_identity A.obj := by
  rw [A.unique A.obj (T.compose_identity A.obj)]
  rw [A.unique A.obj (T.compose (A.mor B.obj) (B.mor A.obj))]



structure AdditiveCategory (T : Category) where
  add (x y : T.Obj) : algebra.AbelianGroup (T.Mor x y)

  add_compose (f h : T.Mor x y) (t : T.Mor y z) : T.compose (f ⊹ h) t = (T.compose f t) ⊹ (T.compose h t)
  compose_add (f : T.Mor x y) (h t : T.Mor y z) : T.compose f (h ⊹ t) = (T.compose f h) ⊹ (T.compose f t)

def End (C : Category) := FunctorCategory C C

end Category

namespace CategoryExample

open Category



structure NaturalFamily (T : Category) where
  F : Nat → (End T).Obj
  f : (i : Nat) → (End T).Mor (F i) (F (i + 1))


structure GoodNaturalFamily (T : Category) extends NaturalFamily T where
  θ (i j : Nat) : (End T).Mor (FunctorCompose (F (i + 1)) (F (j))) (FunctorCompose (F (i)) (F (j + 1)))
  χ (i j : Nat) : (End T).Mor (FunctorCompose (F i) (F j)) (FunctorCompose (F i) (F j))
  χ' (i j : Nat) : (End T).Mor (FunctorCompose (F i) (F j)) (FunctorCompose (F i) (F j))

  good (i j : Nat) :
    (End T).compose (θ i j) (FunctorActionOnTransformation (f i) (F (j + 1)))
    = (End T).compose (TransformationConsumeFunctor (F (i + 1)) (f j)) (χ (i + 1) (j + 1))

  χ_inverse (i j : Nat) : (End T).compose (χ i j) (χ' i j) = (End T).compose_identity _
  χ'_inverse (i j : Nat) : (End T).compose (χ' i j) (χ i j) = (End T).compose_identity _

variable {T : Category}
def T' := End T
variable (ι : NaturalFamily T)
variable (ι' : GoodNaturalFamily T)

def Start := ι.f

theorem ImportantEquality (i j : Nat)  :
  T'.compose (T'.compose (ι'.χ' (i +1) j) (TransformationConsumeFunctor (ι'.F (i + 1)) (ι'.f j))) (ι'.χ (i + 1) (j + 1))
  =
  T'.compose (T'.compose (ι'.χ' (i+1) j) (ι'.θ i j)) (FunctorActionOnTransformation (ι'.f i) (ι'.F (j + 1)))
  := by grind only [Category.compose_assoc, T'.eq_def, GoodNaturalFamily.good]

end CategoryExample
