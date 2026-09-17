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

theorem Category.equal_mor (T : Category) (A B C D : T.Obj) (h : A = B) (h' : C = D) : T.Mor A C = T.Mor B D := by
  simp_all

scoped notation:80 f:80 " ▸" C g:79  => Category.compose C f g

@[ext]
structure Functor (A B : Category) where
  obj : A.Obj → B.Obj
  mor {a b} (h : A.Mor a b) : B.Mor (obj a) (obj b)

  mor_compose : mor (A.compose h k) = B.compose (mor h) (mor k)
  mor_identity : mor (A.compose_identity a) = B.compose_identity (obj a)

infix:120 "⥤" => Functor

theorem Functor.ext'
    (F G : Functor A B)
    (h_obj : ∀ a, F.obj a = G.obj a)
    (h_mor : ∀ a b (f : A.Mor a b), HEq (F.mor f) (G.mor f)) :
    F = G
:= by
  cases F with | mk Fo Fm Fc Fi =>
  cases G with | mk Go Gm Gc Gi =>
  have ho : Fo = Go := funext h_obj
  subst ho
  ext <;> simp
  funext a b f
  apply eq_of_heq
  apply h_mor


attribute [simp] Functor.mor_identity

infix:100 " ↻ " => Functor.mor

@[ext]
structure Transformation (F G : Functor A B) where
  data (x : A.Obj) : B.Mor (F.obj x) (G.obj x)
  naturality {a b : A.Obj} (f : A.Mor a b) : B.compose (F.mor f) (data b) = B.compose (data a) (G.mor f)

infix:100 "ₐ " => Transformation.data

theorem Transformation.heq_ext'
    (S T : Category)
    (A B A' B' : Functor S T)
    (F : Transformation A B)
    (F' : Transformation A' B')
    (hA : A = A')
    (hB : B = B')
    (h : ∀ a, HEq (F.data a) (F'.data a))
:
    HEq F F'
:= by
  subst hA
  subst hB
  cases A with
  | mk Ao Am Ac Ai
  cases B with
  | mk Bo Bm Bc Bi
  cases F with
  | mk Fo Fn
  cases F' with
  | mk F'o F'n
  simp_all
  funext x
  apply h


theorem Transformation.if_eq
  {A B : Category}
  {F F' : Functor A B} (h h' : Transformation F F') (both_eq : h = h') (x : A.Obj)
:
  h.data x = h'.data x
:= by
  exact ((fun a => congrFun a x) ∘ congrArg data) both_eq


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

def TransformationCompose
  {F G H: Functor A B}
  (τ : Transformation F G)
  (μ : Transformation G H)
  : Transformation F H where
  data x := B.compose (τ.data x) (μ.data x)
  naturality (f) := by rw [←B.compose_assoc, τ.naturality, B.compose_assoc, μ.naturality, ←B.compose_assoc]

theorem TransformationCompose.apply
  {F G H: Functor A B}
  (τ : Transformation F G)
  (μ : Transformation G H)
  (q : A.Obj)
  :
  B.compose (τ.data q) (μ.data q) = (TransformationCompose τ μ).data q
  := rfl

theorem FunctorActionOnTransformation.compose
  {G H K : Functor A B}
  (τ : Transformation G H)
  (ε : Transformation H K)
  (F : Functor B C)
  : FunctorActionOnTransformation (TransformationCompose τ ε) F
    = TransformationCompose (FunctorActionOnTransformation τ F) (FunctorActionOnTransformation ε F)
  :=
by
  simp [TransformationCompose, FunctorActionOnTransformation, Functor.mor_compose]
  rfl

def TransformationIdentity (F : Functor A B) : Transformation F F where
  data x := B.compose_identity (F.obj x)
  naturality := by simp

theorem FunctorActionOnTransformation.identity
  {G : Functor A B}
  (F : Functor B C)
  : FunctorActionOnTransformation (TransformationIdentity G) F
    = TransformationIdentity (FunctorCompose G F)
  :=
by
  simp [TransformationIdentity, FunctorActionOnTransformation]
  rfl


def TransformationConsumeFunctor {G H : Functor B C} (F : Functor A B) (τ : Transformation G H)
  : Transformation (F ∘ᶠG) (F ∘ᶠH) where
  data x := τ.data (F.obj x)
  naturality f := by simp [FunctorCompose]; rw [τ.naturality]

theorem TransformationConsumeFunctor.compose
  {G H K: Functor B C}
  (F : Functor A B)
  (τ : Transformation G H)
  (η : Transformation H K)
  :
  TransformationConsumeFunctor F (TransformationCompose τ η)
  =
  TransformationCompose (TransformationConsumeFunctor F τ) (TransformationConsumeFunctor F η)
  :=
by
  simp [TransformationConsumeFunctor, TransformationCompose]
  rfl



def FunctorCategory (S T : Category) : Category where
  Obj := Functor S T
  Mor (A B) := Transformation A B
  compose := TransformationCompose
  compose_identity := TransformationIdentity

  compose_identity_left := by simp [TransformationCompose, TransformationIdentity]
  compose_identity_right := by simp [TransformationCompose, TransformationIdentity]
  compose_assoc (s t u) := by simp [TransformationCompose, T.compose_assoc]

infix:60 "∶" => FunctorCategory

@[simp, reducible]
def Identity {C : Category} (X : C.Obj) := C.compose_identity X

-- def Compose {C : A∶B} ()

notation  "𝟙" => Category.compose_identity

notation "𝟙ₜ" => TransformationIdentity

theorem FunctorActionOnTransformation.identity'
  {G : (A∶B).Obj}
  (F : B ⥤ C)
  : FunctorActionOnTransformation (𝟙 _ G) F
    = 𝟙ₜ (FunctorCompose G F)
  :=
by
  simp [FunctorActionOnTransformation, FunctorCategory]
  apply FunctorActionOnTransformation.identity

theorem TransformationConsumeFunctor.identity
  {G : B ⥤ C} (F : A ⥤ B)
  : TransformationConsumeFunctor F ((B∶C).compose_identity G) = (A∶C).compose_identity (FunctorCompose F G)
  := rfl

def FunctorComposition (A B C : Category) : Functor (A∶B) ((B∶C)∶(A∶C)) where
  obj F := {
    obj G := FunctorCompose F G
    mor τ := TransformationConsumeFunctor F τ
    mor_compose := by
      intro a b f c h
      apply TransformationConsumeFunctor.compose
    mor_identity := by
      intro G
      apply TransformationConsumeFunctor.identity
  }
  mor {S T} τ := {
    data G := FunctorActionOnTransformation τ G
    naturality := by
      intro H K η
      simp [TransformationConsumeFunctor, FunctorActionOnTransformation, FunctorCategory, TransformationCompose]
      funext x
      exact Eq.symm (η.naturality (τ ₐ x))
  }
  mor_compose := by
    intro F G τ H η
    simp [FunctorCategory, TransformationCompose]
    funext x
    apply FunctorActionOnTransformation.compose
  mor_identity := by
    intro a
    conv => lhs; arg 1; intro x; rw [FunctorActionOnTransformation.identity' x]
    rfl

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

structure DiscreteMor {J : Type u} (a b : J) : Type u where
  data : a = b

def Discrete (J : Type _) : Category where
  Obj := J
  Mor := DiscreteMor
  compose a b := {data := Eq.trans a.data b.data}
  compose_identity a := {data := rfl}
  compose_identity_left a b := by simp
  compose_identity_right a b := by simp
  compose_assoc a b := by simp

def ConstantFunctor (A B :Category) (i : B.Obj) : Functor A B where
  obj x := i
  mor f := B.compose_identity i
  mor_identity := rfl
  mor_compose := by simp

def ConstantTranformation (A B : Category) {i j : B.Obj} (f : B.Mor i j) : Transformation (ConstantFunctor A B i) (ConstantFunctor A B j) where
  data x := f
  naturality := by simp [ConstantFunctor]

def Δ (J : Category) (C : Category) : Functor C (FunctorCategory J C) where
  obj c := ConstantFunctor J C c
  mor f := ConstantTranformation J C f
  mor_compose := by intros; rfl
  mor_identity := by intros; rfl

structure Cocone (J : Category) (C : Category) (F : (FunctorCategory J C).Obj) where
  c : C.Obj
  data : (FunctorCategory J C).Mor F ((Δ J C).obj c)

def TrivialCocone (C : Category) (F : (FunctorCategory (Discrete Unit) C).Obj) : Cocone _ _ F where
  c := F.obj ()
  data := {
    data x := C.compose_identity (F.obj ())
    naturality := by
      intro a b f
      simp [Δ, ConstantFunctor]
      have p : f = (Discrete Unit).compose_identity () := by rfl
      have ha : a = () := by rfl
      have hb : b = () := by rfl
      subst ha hb
      rw [p]
      rw[@F.mor_identity ()]
  }

structure CoconeMor (J : Category) (C : Category) (F : (FunctorCategory J C).Obj) (a b : Cocone J C F) where
  c : C.Mor a.c b.c
  valid : (FunctorCategory J C).compose a.data ((Δ J C).mor c) = b.data

def CoconeCategory (J : Category) (C : Category) (F : (FunctorCategory J C).Obj) : Category where
  Obj := Cocone J C F
  Mor := CoconeMor J C F
  compose x y := {
    c := C.compose x.c y.c
    valid := by
      have x_valid := x.valid
      have y_valid := y.valid
      rw [←y_valid, ←x_valid, Category.compose_assoc, Functor.mor_compose]
    }
  compose_identity a := {
    c := C.compose_identity a.c
    valid := by simp
  }
  compose_identity_left a b := by simp
  compose_identity_right a b := by simp
  compose_assoc a b c := by simp [C.compose_assoc]

structure IsColimit  (J : Category) (C : Category) (Γ : Functor (FunctorCategory J C) C) where
  τ : (End (FunctorCategory J C)).Mor (IdentityFunctor (FunctorCategory J C)) (FunctorCompose Γ (Δ J C))
  uni (F : (FunctorCategory J C).Obj) : IsInitialObject (CoconeCategory J C F) {c :=(Γ.obj F), data := (τ.data F) }

def SingletonFunctorToObject (C : Category) : Functor (FunctorCategory (Discrete Unit) C) C where
  obj a := a.obj ()
  mor f := f.data ()
  mor_compose := by intros; rfl
  mor_identity := by intros; rfl



@[simp]
theorem SingletonFunctorΔ
  (C : Category) :
  FunctorCompose
  (SingletonFunctorToObject C)
  (Δ (Discrete Unit) C)
  = IdentityFunctor (FunctorCategory (Discrete Unit) C)
  :=
by
  apply Functor.ext' <;> simp
  · intro F
    simp [SingletonFunctorToObject, Δ, FunctorCompose, FunctorCategory, Discrete, ConstantFunctor]
    cases F with
    | mk Fo Fm Fc Fi
    apply Functor.ext' <;> simp
    intro a b f
    have h : f = (Discrete Unit).compose_identity a := by rfl
    rw [h]
    have h2 := @Fi a
    rw [h2]
  · intro a b f
    simp [SingletonFunctorToObject, Δ, FunctorCompose, FunctorCategory, Discrete, ConstantFunctor, ConstantTranformation]
    cases f with
    | mk transform_data naturality
    simp_all
    apply Transformation.heq_ext'
    · apply Functor.ext' <;> simp
      intro a b f
      have h : f = (Discrete Unit).compose_identity a := by rfl
      have ha : a = () := by rfl
      rw [h, ha]
      (expose_names; exact Eq.symm a_1.mor_identity)
    · apply Functor.ext' <;> simp
      intro a b f
      have h : f = (Discrete Unit).compose_identity a := by rfl
      have ha : a = () := by rfl
      rw [h, ha]
      (expose_names; exact Eq.symm b_1.mor_identity)
    · intro a
      exact heq_of_eq rfl



@[simp]
theorem ΔSingletonFunctor
  (C : Category) :
  FunctorCompose (Δ (Discrete Unit) C) (SingletonFunctorToObject C)  = IdentityFunctor C
:=
by
  apply Functor.ext' <;> simp
  · intro F
    simp [SingletonFunctorToObject, Δ, FunctorCompose, FunctorCategory, Discrete, ConstantFunctor]
  · intro a b f
    simp [SingletonFunctorToObject, Δ, FunctorCompose, FunctorCategory, Discrete, ConstantFunctor, ConstantTranformation]

theorem SingletonCoproduct_RightInverse
  (C : Category)
  (Γ : Functor (FunctorCategory (Discrete Unit) C) C)
  (h : IsColimit (Discrete Unit) C Γ)
  (a : Functor (Discrete Unit) C)
  :
    C.compose
    ((h.τ.data a).data ())
    ((h.uni a).mor (TrivialCocone _ a)).c
    =
    C.compose_identity (a.obj ()) :=
by
  have h_mor_main_property := ((h.uni a).mor (TrivialCocone _ a)).valid
  simp_all [Δ, ConstantTranformation, TrivialCocone, FunctorCategory, TransformationCompose]
  have t := Transformation.if_eq _ _ h_mor_main_property
  simp_all
  apply t


theorem SingletonCoproduct_LeftInverse
  (C : Category)
  (Γ : Functor (FunctorCategory (Discrete Unit) C) C)
  (h : IsColimit (Discrete Unit) C Γ)
  (a : (FunctorCategory (Discrete Unit) C).Obj)
  : C.compose
  ((h.uni a).mor (TrivialCocone _ a)).c
  ((h.τ.data a).data ())
  =
  C.compose_identity ((Γ.obj a)) :=
by
  let map_Γa_a := (h.uni a).mor (TrivialCocone _ a)
  let map_a_Γa
    : (CoconeCategory (Discrete Unit) C a).Mor
      (TrivialCocone _ a)
      { c := Γ.obj a, data := h.τ ₐ a }
    := {
      c := cast (by
        simp [Δ, FunctorCategory, FunctorCompose, ConstantFunctor, TrivialCocone];
      ) ((h.τ.data a).data ())
      valid := by
        simp [FunctorCategory, Δ, cast, ConstantTranformation, TrivialCocone, TransformationCompose, ConstantFunctor]
        ext j
        cases j
        exact C.compose_identity_left (a.obj PUnit.unit) (Γ.obj a) ((h.τ ₐ a)ₐ ())
    }
  let map_composed := (CoconeCategory (Discrete Unit) C a).compose map_Γa_a map_a_Γa
  let cone_Γ : (CoconeCategory (Discrete Unit) C _).Obj := {c :=(Γ.obj a), data := (h.τ.data a)}
  have cone_Γ_identity := InitialObject.self _ _ (h.uni a)
  have uniqueness := (h.uni a).unique _ map_composed
  have identity_lift :
    C.compose_identity (Γ.obj a)
    = ((CoconeCategory (Discrete Unit) C a).compose_identity { c := Γ.obj a, data := h.τ ₐ a }).c := by rfl
  have compose_lift :
    C.compose ((h.uni a).mor (TrivialCocone _ a)).c ((h.τ.data a).data ())
    = map_composed.c := by rfl
  rw [identity_lift, ←cone_Γ_identity, compose_lift, uniqueness]

def Switch
  {J Domain Codomain : Category}
  : Functor
    (FunctorCategory J (FunctorCategory Domain Codomain))
    (FunctorCategory Domain (FunctorCategory J  Codomain))
where
  obj x := {
    obj a := {
      obj b := (x.obj b).obj a,
      mor f := (x.mor f).data a
      mor_compose := by
        intro q w f e g
        simp [x.mor_compose]
        rfl
      mor_identity := by
        intro q
        rw [x.mor_identity]
        rfl
    }
    mor f := {
      data b := (x.obj b).mor f
      naturality := by
        intro q w s
        simp
        exact Eq.symm ((x ↻ s).naturality f)
    }
    mor_compose := by
      intro a b f_ab c f_bc
      simp [FunctorCategory, TransformationCompose]
      funext j
      exact (x.obj j).mor_compose
    mor_identity := by
      intro obj
      simp [FunctorCategory, TransformationIdentity]
  }
  mor {a b} ε  := {
    data q := {
      data i := (ε.data i).data q
      naturality := by
        intro i j s
        have ε_nat := ε.naturality s
        simp
        rw [TransformationCompose.apply (a.mor s) (ε.data j) q]
        rw [TransformationCompose.apply (ε.data i) (b.mor s) q]
        simp [FunctorCategory] at ε_nat
        rw [ε_nat]
    }
    naturality := by
      intro i j s
      simp [FunctorCategory]
      ext k
      simp [TransformationCompose]
      exact (ε ₐ k).naturality s
  }
  mor_compose := by
    intro a b f c h
    simp [FunctorCategory, FunctorCategory, TransformationCompose]
  mor_identity := by
    intro a
    simp [FunctorCategory, FunctorCategory, TransformationIdentity]


def ExtendFunctor
  (J Domain Codomain : Category)
  (Γ : Functor (FunctorCategory J Codomain) Codomain)
  :
  Functor (FunctorCategory J (FunctorCategory Domain Codomain)) (FunctorCategory Domain Codomain)
where
  obj x := FunctorCompose (Switch.obj x) Γ
  mor ε := FunctorActionOnTransformation (Switch.mor ε) Γ
  mor_compose := by
    intro a b f c h
    apply FunctorActionOnTransformation.compose (Switch.mor f) (Switch.mor h) Γ
  mor_identity := by
    intro a
    apply FunctorActionOnTransformation.identity

def Extend''
  (J D C : Category)
  :
  Functor
  (D∶(J∶C))
  (FunctorCategory ((J∶C)∶C) (D∶C))
  := FunctorComposition D (J∶C) C
def Extend'''
  (J D C : Category)
  :
  Functor
  (J∶(D∶C))
  (FunctorCategory ((J∶C)∶C) (D∶C))
  := FunctorCompose Switch (FunctorComposition D (J∶C) C)
def Extend'
  (J D C : Category)
  :
  Functor
  ((J∶C)∶C)
  (FunctorCategory (D∶(J∶C)) (D∶C))
  := Switch.obj (FunctorComposition D (J∶C) C)

def FunctorExtension
  (J D C : Category)
  :
  Functor
  ((J∶C)∶C)
  (FunctorCategory (J∶(D∶C)) (D∶C))
:= Switch.obj (FunctorCompose Switch (FunctorComposition D (J∶C) C))

def EndoExtension
  (D C : Category)
  : (C∶C) ⥤ (FunctorCategory (D∶C) (D∶C))
:= Switch.obj (FunctorComposition D C C)

-- def EndoSwitch
--   (A B C : Category)
--   : ((A∶(B∶C))∶(A∶(B∶C))) ⥤ ((B∶(A∶C))∶(B∶(A∶C)))
-- := sorry

-- def ColimitExtension
--   (J Domain Codomain : Category)
--   (Γ : Functor (FunctorCategory J Codomain) Codomain)
--   (h : IsColimit  J Codomain Γ)
--   :
--   IsColimit J (FunctorCategory Domain Codomain) ((FunctorExtension J Domain Codomain).obj Γ)
-- where
--   τ := cast _ ((FunctorCompose (EndoExtension (Domain) (J∶Codomain)) (EndoSwitch Domain J Codomain)).mor h.τ)


-- def ExtendColimit
--   (J Domain Codomain : Category)
--   (Γ : Functor (FunctorCategory J Codomain) Codomain)
--   (h : IsColimit  J Codomain Γ)
--   :
--   IsColimit J (FunctorCategory Domain Codomain) (ExtendFunctor J Domain Codomain Γ)
-- where
--   τ := {
--     data x := Switch.mor (TransformationConsumeFunctor (Switch.obj x) (h.τ))
--     naturality := by
--       intro a b f

--   }

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

-- variable (Γ : Functor (FunctorCategory Unit T) T) (hΓ : IsCoproduct Unit T Γ)

def Start := ι.f

theorem ImportantEquality (i j : Nat)  :
  T'.compose (T'.compose (ι'.χ' (i +1) j) (TransformationConsumeFunctor (ι'.F (i + 1)) (ι'.f j))) (ι'.χ (i + 1) (j + 1))
  =
  T'.compose (T'.compose (ι'.χ' (i+1) j) (ι'.θ i j)) (FunctorActionOnTransformation (ι'.f i) (ι'.F (j + 1)))
  := by grind only [Category.compose_assoc, T'.eq_def, GoodNaturalFamily.good]


-- def NaturalFamilyFunctor : (FunctorCategory Nat (End T)).Obj := ι.F

-- def NaturalFamilyShift

end CategoryExample
