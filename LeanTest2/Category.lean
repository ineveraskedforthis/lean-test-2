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

@[simp]
def IdentityFunctor (C : Category) : Functor C C where
  obj x := x
  mor f := f
  mor_compose := rfl
  mor_identity := rfl

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


def FunctorCategory (S T : Category) : Category where
  Obj := Functor S T
  Mor (A B) := Transformation A B
  compose := TransformationCompose
  compose_identity := TransformationIdentity

  compose_identity_left := by simp [TransformationCompose, TransformationIdentity]
  compose_identity_right := by simp [TransformationCompose, TransformationIdentity]
  compose_assoc (s t u) := by simp [TransformationCompose, T.compose_assoc]

structure IsInitialObject (T : Category) (obj : T.Obj) where
  mor (a : T.Obj) : T.Mor obj a
  unique (a : T.Obj) (h : T.Mor obj a) : h = mor a

-- structure InitialObject (T : Category) where
--   obj : T.Obj
--   mor (a : T.Obj) : T.Mor obj a
--   unique (a : T.Obj) (h : T.Mor obj a) : h = mor a

theorem InitialObject.iso (T : Category) (a b : T.Obj) (A : IsInitialObject T a) (B : IsInitialObject T b) :
  T.compose (A.mor b) (B.mor a) = T.compose_identity a := by
  rw [A.unique a (T.compose_identity a)]
  rw [A.unique a (T.compose (A.mor b) (B.mor a))]

@[simp]
theorem InitialObject.self (T : Category) (a : T.Obj) (A : IsInitialObject T a) :
  A.mor a = T.compose_identity a := by
  rw [A.unique a (T.compose_identity a)]

@[simp]
theorem InitialObject.compose {T : Category} {a b c: T.Obj} (A : IsInitialObject T a) (f : T.Mor b c) :
  T.compose (A.mor b) f = A.mor c := by
  induction A <;> simp_all

structure AdditiveCategory (T : Category) where
  add (x y : T.Obj) : algebra.AbelianGroup (T.Mor x y)

  add_compose (f h : T.Mor x y) (t : T.Mor y z) : T.compose (f ⊹ h) t = (T.compose f t) ⊹ (T.compose h t)
  compose_add (f : T.Mor x y) (h t : T.Mor y z) : T.compose f (h ⊹ t) = (T.compose f h) ⊹ (T.compose f t)

def End (C : Category) := FunctorCategory C C

def DiscreteFunctorCategory (J : Type _) (C : Category) : Category where
  Obj := (J → C.Obj)
  Mor a b  := (j : J) → C.Mor (a j) (b j)
  compose f g j := C.compose (f j) (g j)
  compose_identity a j := C.compose_identity (a j)
  compose_assoc s t u := by simp [C.compose_assoc]
  compose_identity_left := by simp
  compose_identity_right := by simp



-- @[simp]
-- def DiscreteFunctorCategory.Obj.ToFunction {J : Type _} {C : Category} (a : (DiscreteFunctorCategory J C).Obj) : J → C.Obj := a

-- @[simp]
-- def DiscreteFunctorCategory.Mor.ToFunction
--   {J : Type _} {C : Category} {a b : (DiscreteFunctorCategory J C).Obj}
--   (f : (DiscreteFunctorCategory J C).Mor a b) : (j : J) → C.Mor (a j) (b j) := f


-- def DiscretePointObject (J : Type _) (C : Category) (c : C.Obj) (_ : J) := c
-- def DiscretePointMor (J : Type _) (C : Category) (a b : C.Obj) (j : J) () := c

def Δ (J : Type _) (C : Category) : Functor C (DiscreteFunctorCategory J C) where
  obj c j := c
  mor f j := f
  mor_compose := by intros; rfl
  mor_identity := by intros; rfl



structure DiscreteCocone' (J : Type _) (C : Category) (F : (DiscreteFunctorCategory J C).Obj) where
  c : C.Obj
  data : (DiscreteFunctorCategory J C).Mor F ((Δ J C).obj c)

structure DiscreteCocone'Mor (J : Type _) (C : Category) (F : (DiscreteFunctorCategory J C).Obj) (a b : DiscreteCocone' J C F) where
  c : C.Mor a.c b.c
  valid : (DiscreteFunctorCategory J C).compose a.data ((Δ J C).mor c) = b.data

def DiscreteCocone'Category (J : Type _) (C : Category) (F : (DiscreteFunctorCategory J C).Obj) : Category where
  Obj := DiscreteCocone' J C F
  Mor := DiscreteCocone'Mor J C F
  compose x y := {
    c := C.compose x.c y.c
    valid := by
      have x_valid := x.valid
      have y_valid := y.valid
      simp_all [Δ, DiscreteFunctorCategory]
      ext j
      induction C <;> grind
    }
  compose_identity a := {
    c := C.compose_identity a.c
    valid := by simp
  }
  compose_identity_left a b := by simp
  compose_identity_right a b := by simp
  compose_assoc a b c := by simp [C.compose_assoc]

structure IsCoproduct  (J : Type _) (C : Category) (Γ : Functor (DiscreteFunctorCategory J C) C) where
  -- τ (F : (DiscreteFunctorCategory J C).Obj) : (DiscreteFunctorCategory J C).Mor F ((Δ J C).obj (Γ.obj F))
  τ : (End (DiscreteFunctorCategory J C)).Mor (IdentityFunctor (DiscreteFunctorCategory J C)) (FunctorCompose Γ (Δ J C))
  uni (F : (DiscreteFunctorCategory J C).Obj)
    : IsInitialObject (DiscreteCocone'Category J C F) {c :=(Γ.obj F), data := (τ.data F) }

def SingletonFunctorToObject (C : Category) : Functor (DiscreteFunctorCategory Unit C) C where
  obj a := a ()
  mor f := (f ())
  mor_compose := by intros; rfl
  mor_identity := by intros; rfl

@[simp]
theorem SingletonFunctorΔ
  (C : Category) :
  FunctorCompose (SingletonFunctorToObject C) (Δ Unit C) = IdentityFunctor (DiscreteFunctorCategory Unit C)
  := by  simp [SingletonFunctorToObject, Δ, FunctorCompose]

@[simp]
theorem ΔSingletonFunctor
  (C : Category) :
  FunctorCompose (Δ Unit C) (SingletonFunctorToObject C)  = IdentityFunctor C
  := by  simp [SingletonFunctorToObject, Δ, FunctorCompose]

theorem SingletonCoproduct_RightInverse
  (C : Category) (Γ : Functor (DiscreteFunctorCategory Unit C) C) (h : IsCoproduct Unit C Γ) (a : (DiscreteFunctorCategory Unit C).Obj)
  : C.compose (h.τ.data a ()) ((h.uni a).mor {c := a (), data _ := C.compose_identity (a ())}).c = C.compose_identity (a ()) :=
by
  have h_mor_main_property := ((h.uni a).mor {c := a (), data _ := C.compose_identity (a ())}).valid
  simp_all [Δ]
  apply congrFun h_mor_main_property ()

theorem SingletonCoproduct_LeftInverse
  (C : Category) (Γ : Functor (DiscreteFunctorCategory Unit C) C) (h : IsCoproduct Unit C Γ) (a : (DiscreteFunctorCategory Unit C).Obj)
  : C.compose ((h.uni a).mor {c := a (), data _ := C.compose_identity (a ())}).c (h.τ.data a ()) = C.compose_identity ((Γ.obj a)) :=
by
  let map_Γa_a := (h.uni a).mor {c := a (), data _ := C.compose_identity (a ())}
  let map_a_Γa
    : (DiscreteCocone'Category Unit C a).Mor
      { c := a (), data := fun x => C.compose_identity (a ()) }
      { c := Γ.obj a, data := h.τ ₐ a }
    := {
      c := cast (by
        simp [Δ, DiscreteFunctorCategory, FunctorCompose];
      ) (h.τ.data a ())
      valid := by
        simp [DiscreteFunctorCategory, Δ, cast]
        funext j
        cases j
        exact C.compose_identity_left (a PUnit.unit) (Γ.obj a) ((h.τ ₐ a) ())
    }
  let map_composed := (DiscreteCocone'Category Unit C a).compose map_Γa_a map_a_Γa
  let cone_Γ : (DiscreteCocone'Category Unit C _).Obj := {c :=(Γ.obj a), data := (h.τ.data a)}
  have cone_Γ_identity := InitialObject.self _ _ (h.uni a)
  have uniqueness := (h.uni a).unique _ map_composed
  have identity_lift :
    C.compose_identity (Γ.obj a)
    = ((DiscreteCocone'Category Unit C a).compose_identity { c := Γ.obj a, data := h.τ ₐ a }).c := by rfl
  have compose_lift :
    C.compose ((h.uni a).mor {c := a (), data _ := C.compose_identity (a ())}).c (h.τ.data a ())
    = map_composed.c := by rfl
  rw [identity_lift, ←cone_Γ_identity, compose_lift, uniqueness]



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
