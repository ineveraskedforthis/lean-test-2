import LeanTest2.Algebra

namespace Category

universe u v w u' v' w'


structure Category : Type max (u + 1) (v + 1) where
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
structure Functor (A : Category.{u, v}) (B : Category.{u', v'}) : Type max v' u' u v where
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
structure Transformation (F G : Functor.{u, v, u', v'} A B) : Type max u' v' u v where
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

@[simp]
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



def FunctorCategory (S : Category.{u, v}) (T : Category.{u', v'}) : Category.{max u v u' v', max u v u' v'} where
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

notation  " 𝟙" => Category.compose_identity

notation " 𝟙ₜ" => TransformationIdentity

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

def Associator {F : Functor A B} {G : Functor B C} {H : Functor C D} :
  Transformation (FunctorCompose (FunctorCompose F G) H) (FunctorCompose F (FunctorCompose G H)) where
  data q := D.compose_identity _
  naturality := by
    intro a b f
    simp [FunctorCompose]

macro "catsimp" : tactic => `(tactic|
  (simp [
      TransformationConsumeFunctor.identity,
      FunctorActionOnTransformation.identity',
      Identity,
      TransformationIdentity,
      FunctorCategory,
      TransformationConsumeFunctor,
      FunctorActionOnTransformation.identity,
      TransformationCompose,
      FunctorActionOnTransformation,
      IdentityFunctor,
      FunctorCompose,
      Functor.mor_compose,
      Associator,
      Transformation.naturality
  ] <;> try rfl)
)

structure Category2' : Type max max (u + 2) (v + 2) (w+1) where
  C : Category.{u, v}

  Cell {a b : C.Obj} : C.Mor a b → C.Mor a b → Type w

  cell_id {a b : C.Obj} (f : C.Mor a b) : Cell f f

  vcomp {x y : C.Obj} {a b c : C.Mor x y} (τ : Cell a b) (ε : Cell b c) : Cell a c
  hcomp {a b c : C.Obj} {f g : C.Mor a b} {h k : C.Mor b c} : Cell f g → Cell h k → Cell (C.compose f h) (C.compose g k)
  whisker_arg { a b c } {F G : C.Mor b c} (H : C.Mor a b) (τ : Cell F G) : Cell (C.compose H F) (C.compose H G)
  whisker_apply { a b c } {F G : C.Mor a b} (τ : Cell F G) (H : C.Mor b c) : Cell (C.compose F H) (C.compose G H)
  vcomp_assoc  (τ : Cell a b) (ε : Cell b c) (η : Cell c d) : vcomp (vcomp τ ε) η = vcomp τ (vcomp ε η)
  vcomp_id_right {F : C.Mor A B} (τ : Cell G F) : vcomp τ (cell_id F) = τ
  vcomp_id_left {G : C.Mor A B} (τ : Cell G F) : vcomp (cell_id G) τ = τ

  associator {a b c d : C.Obj} (G : C.Mor a b) (F : C.Mor b c) (H : C.Mor c d)
    : Cell (C.compose (C.compose G F) H) (C.compose G (C.compose F H))
  associator_is_id {a b c d : C.Obj} (G : C.Mor a b) (F : C.Mor b c) (H : C.Mor c d)
    : associator G F H ≍ cell_id (C.compose G (C.compose F H))

  hcomp_assoc {f g : C.Mor a b} {h k : C.Mor b c} {s t : C.Mor c d} (τ : Cell f g) (ε : Cell h k) (η : Cell s t) :
    vcomp  (hcomp (hcomp τ ε) η) (associator g k t) = vcomp (associator f h s) (hcomp τ (hcomp ε η))
  hcomp_id_id {f : C.Mor a b} {g : C.Mor b c} : hcomp (cell_id f) (cell_id g) = cell_id (C.compose f g)
  hcomp_id_left {F G : C.Mor A B} (τ : Cell F G) : hcomp (cell_id (C.compose_identity A)) τ = whisker_arg _ τ
  hcomp_id_right  {F G : C.Mor A B} (τ : Cell F G) : hcomp τ (cell_id (C.compose_identity B)) = whisker_apply τ _

  interchange : hcomp (vcomp τ ε) (vcomp η μ) = vcomp (hcomp τ η) (hcomp ε μ)

  whisker_arg_to_hcomp {a b c : C.Obj} (H : C.Mor a b) {Q W : C.Mor b c} (τ : Cell Q W) : whisker_arg H τ = hcomp (cell_id H) τ
  whisker_apply_to_hcomp   {a b c : C.Obj} {Q W : C.Mor a b} (τ : Cell Q W)  (H : C.Mor b c) : whisker_apply τ H = hcomp τ (cell_id H)




structure Category2 : Type max max (u + 2) (v + 2) (w+1) where
  C : Category.{u, v}

  Cell {a b : C.Obj} : C.Mor a b → C.Mor a b → Type w

  cell_id {a b : C.Obj} (f : C.Mor a b) : Cell f f

  vcomp {x y : C.Obj} {a b c : C.Mor x y} (τ : Cell a b) (ε : Cell b c) : Cell a c
  vcomp_assoc  (τ : Cell a b) (ε : Cell b c) (η : Cell c d) : vcomp (vcomp τ ε) η = vcomp τ (vcomp ε η)
  vcomp_id_right {F : C.Mor A B} (τ : Cell G F) : vcomp τ (cell_id F) = τ
  vcomp_id_left {G : C.Mor A B} (τ : Cell G F) : vcomp (cell_id G) τ = τ


  -- Use functor on the argument of transformation
  whisker_arg { a b c } {F G : C.Mor b c} (H : C.Mor a b) (τ : Cell F G) : Cell (C.compose H F) (C.compose H G)
  -- Apply functor to transformation
  whisker_apply { a b c } {F G : C.Mor a b} (τ : Cell F G) (H : C.Mor b c) : Cell (C.compose F H) (C.compose G H)

  --  id transformation is id tranformation on image of any functor
  whisker_arg_id { a b c } { f : C.Mor a b } { g : C.Mor b c } : whisker_arg f (cell_id g) = cell_id (C.compose f g)
  -- Functors map id tranformation to id transformation
  whisker_apply_id { a b c } { f : C.Mor a b } { g : C.Mor b c } : whisker_apply (cell_id f) g = cell_id (C.compose f g)

  -- Composition of transformations agree on images of functors
  vcomp_whisker_arg { a b c } { f : C.Mor a b } { g h i : C.Mor b c } ( η : Cell g h ) ( θ : Cell h i ) : vcomp (whisker_arg f η) (whisker_arg f θ) = whisker_arg f (vcomp η θ)
  -- Functors are functorial on transformations
  vcomp_whisker_apply  { a b c } { g h i : C.Mor a b } { f : C.Mor b c } ( η : Cell g h ) ( θ : Cell h i ) : vcomp (whisker_apply η f) (whisker_apply θ f) = whisker_apply (vcomp η θ) f

  -- Trivial associator: required because types of functor compositions are not trivailly equal
  associator {a b c d : C.Obj} (G : C.Mor a b) (F : C.Mor b c) (H : C.Mor c d)
    : Cell (C.compose (C.compose G F) H) (C.compose G (C.compose F H))
  associator_is_id {a b c d : C.Obj} (G : C.Mor a b) (F : C.Mor b c) (H : C.Mor c d)
    : associator G F H ≍ cell_id (C.compose G (C.compose F H))

  -- Associativity of adding functors to arguments of natural transformation
  whisker_arg_assoc { a b c d } { f : C.Mor a b } { g : C.Mor b c } { h i : C.Mor c d } ( η : Cell h i)
    : vcomp (whisker_arg (C.compose f g) η) (associator f g i) = vcomp (associator f g h) (whisker_arg f (whisker_arg g η))
  -- Associativity of applying functors
  whisker_apply_assoc { a b c d } { f g : C.Mor a b } { h : C.Mor b c } { i : C.Mor c d } ( η : Cell f g)
    : vcomp (associator f h i) (whisker_apply η (C.compose h i)) = vcomp (whisker_apply (whisker_apply η h) i) (associator g h i)
  -- Functors applied to the argument and to the natural transformation itself do not interfere with each other
  whisker_assoc { a b c d } { f : C.Mor a b } { g h : C.Mor b c } { i : C.Mor c d } ( η : Cell g h )
    : vcomp (associator f g i) (whisker_arg f (whisker_apply η i)) = vcomp (whisker_apply (whisker_arg f η) i) (associator f h i)

  --  Cells are natural transformations and commute between each other
  cell_natural { a b c } { f g : C.Mor a b} { h i : C.Mor b c } ( η : Cell f g ) ( θ : Cell h i )
    : vcomp (whisker_apply η h) (whisker_arg g θ) = vcomp (whisker_arg f θ) (whisker_apply η i)

def Cat2' : Category2'.{(max (u + 1) (v + 1)), max u v, max u v} where
  C := {
    Obj := Category.{u, v}
    Mor := Functor.{u, v, u, v}
    compose := FunctorCompose
    compose_identity := IdentityFunctor
    compose_identity_left := by simp [FunctorCompose]
    compose_identity_right := by simp [FunctorCompose]
    compose_assoc := by simp [FunctorCompose]
  }
  Cell := Transformation
  cell_id := TransformationIdentity
  vcomp := TransformationCompose
  hcomp
    {A B C} {F G : Functor A B} {F' G' : Functor B C}
    (τ : Transformation F G) (ε : Transformation F' G')
    := TransformationCompose (FunctorActionOnTransformation τ F') (TransformationConsumeFunctor G ε)
  whisker_arg := TransformationConsumeFunctor
  whisker_apply := FunctorActionOnTransformation

  associator G F H := Associator
  associator_is_id := by
    intro a b c d G F H
    simp [Associator]
    apply Transformation.heq_ext' <;> try rfl
    intro object
    rfl

  vcomp_assoc := by
    intro x y f b c d τ ε η
    simp [TransformationCompose]
    funext object
    apply y.compose_assoc
  vcomp_id_left := by
    intro A B F G τ
    simp [TransformationCompose, TransformationIdentity]
  vcomp_id_right := by
    intro A B F G τ
    simp [TransformationCompose, TransformationIdentity]

  hcomp_assoc := by
    intro a b c d f g h k s t τ ε η
    simp [TransformationCompose, Associator, FunctorActionOnTransformation, TransformationConsumeFunctor, FunctorCompose, Functor.mor_compose]
    funext object
    exact d.compose_assoc (s ↻ (h ↻ (τ ₐ object))) (s ↻ (ε ₐ g.obj object)) (η ₐ k.obj (g.obj object))
  hcomp_id_id := by
    intro a b c f g
    simp [TransformationCompose, TransformationConsumeFunctor, TransformationIdentity, FunctorActionOnTransformation]
    ext object
    exact c.compose_identity_left _ _ _
  hcomp_id_left := by
    intro a b c f g
    simp [TransformationCompose, TransformationConsumeFunctor, TransformationIdentity, FunctorActionOnTransformation]
    ext object
    simp
    exact b.compose_identity_left _ _ _
  hcomp_id_right := by
    intro a b c f g
    simp [TransformationCompose, TransformationConsumeFunctor, TransformationIdentity, FunctorActionOnTransformation]
    ext object
    simp
    exact b.compose_identity_right _ _ _

  interchange := by
    intro x y z w τ q ε t e r η a μ
    simp [TransformationCompose, TransformationConsumeFunctor, FunctorActionOnTransformation, Functor.mor_compose, FunctorCompose]
    ext object
    simp [t.compose_assoc]
    congr 1
    simp [←t.compose_assoc]
    congr 1
    exact η.naturality (ε ₐ object)

  whisker_apply_to_hcomp := by
    intro x y z w τ q H
    simp [
      FunctorActionOnTransformation, TransformationIdentity, TransformationCompose, TransformationConsumeFunctor
    ]
    ext X
    exact Eq.symm (z.compose_identity_right ((w ∘ᶠ H).obj X) ((τ ∘ᶠ H).obj X) (H ↻ (q ₐ X)))

  whisker_arg_to_hcomp := by
    intros
    simp [
      FunctorActionOnTransformation, TransformationIdentity, TransformationCompose, TransformationConsumeFunctor
    ]
    ext X;
    (expose_names;
      exact Eq.symm (c.compose_identity_left ((H ∘ᶠ Q).obj X) ((H ∘ᶠ W).obj X) (τ ₐ H.obj X)))

def Cat2 : Category2.{(max (u + 1) (v + 1)), max u v, max u v} where
  C := {
    Obj := Category.{u, v}
    Mor := Functor.{u, v, u, v}
    compose := FunctorCompose
    compose_identity := IdentityFunctor
    compose_identity_left := by simp [FunctorCompose]
    compose_identity_right := by simp [FunctorCompose]
    compose_assoc := by simp [FunctorCompose]
  }
  Cell := Transformation
  cell_id := TransformationIdentity
  vcomp := TransformationCompose
  whisker_arg := TransformationConsumeFunctor
  whisker_apply := FunctorActionOnTransformation

  associator G F H := Associator
  associator_is_id := by
    intro a b c d G F H
    simp [Associator]
    apply Transformation.heq_ext' <;> try rfl
    intro object
    rfl

  vcomp_assoc := by
    intro x y f b c d τ ε η
    simp [TransformationCompose]
    funext object
    apply y.compose_assoc
  vcomp_id_left := by catsimp
  vcomp_id_right := by catsimp
  whisker_arg_id := by catsimp
  whisker_apply_id := by catsimp
  vcomp_whisker_arg := by catsimp
  vcomp_whisker_apply := by catsimp;
  whisker_arg_assoc := by catsimp
  whisker_apply_assoc := by catsimp
  whisker_assoc := by catsimp
  cell_natural := by catsimp


-- def Composition (C : Cat2.C.Obj) (T : Cat2.C.Obj) (S : Cat2.C.Obj) : ((C∶T)∶((T∶S)∶(C∶S))).Obj := FunctorComposition C T S

-- macro "discharge" : tactic => `(tactic|
--   (try ext <;> simp [
--     TransformationCompose,
--     TransformationIdentity,
--     FunctorActionOnTransformation,
--     TransformationConsumeFunctor,
--     FunctorCompose,
--     Functor.mor_compose,
--     Functor.mor_identity,
--     Cat2.interchange,
--     Cat2.hcomp_id_left,
--     Cat2.hcomp_id_right
--     ] <;> try rfl
--   )
-- )


-- u v
-- Cat2.C.Obj -> u
-- Cat2.C.Mor -> v
-- Functor Cat2.C.Obj Cat2.C.Obj -> max u v


def ULiftCategory (A : Cat2.{u, v}.C.Obj) : Cat2.{max u u', max v v'}.C.Obj := {
  Obj := ULift.{u', u} A.Obj
  Mor a b := ULift.{v', v} (A.Mor a.down b.down)
  compose f g := ULift.up (A.compose f.down g.down)
  compose_identity a := ULift.up (A.compose_identity a.down)
  compose_identity_left a b h := by cases A <;> simp_all
  compose_identity_right := by cases A <;> simp_all
  compose_assoc := by simp [A.compose_assoc]
}

structure StrictFunctor2 (a : Category2.{u, v, w}) (b : Category2.{u', v', w'}) : Type max (u + 1) (v + 1) (w + 1) (u' + 1) (v' + 1) (w' + 1) where
  functor1 : Functor a.C b.C
  cell { α β : a.C.Obj } { f g : a.C.Mor α β } : a.Cell f g → b.Cell (functor1.mor f) (functor1.mor g)
  cell_vcomp { α β γ : a.C.Obj } { f g h : a.C.Mor α β } { τ : a.Cell f g } { ε : a.Cell g h } :
    cell (a.vcomp τ ε) = b.vcomp (cell τ) (cell ε)


def Exp (A : Cat2.{u, v}.C.Obj) (B : Cat2.{u', v'}.C.Obj) : Cat2.{max u u' v v', max u u' v v'}.C.Obj := {
  Obj := Cat2.{max u u', max v v'}.C.Mor (ULiftCategory A) (ULiftCategory B)
  Mor F G := Cat2.{max u u', max v v'}.Cell F G
  compose := Cat2.vcomp
  compose_identity := Cat2.cell_id
  compose_identity_left a b h := by exact Cat2.vcomp_id_left h
  compose_identity_right a b h := by exact Cat2.vcomp_id_right h
  compose_assoc := by exact Cat2.vcomp_assoc
}


macro "cat2simp" : tactic => `(tactic|
  (simp [
      -- ULiftCategory,
      Category2.associator_is_id,
      Category2.cell_natural,
      Category2.vcomp_assoc,
      Category2.vcomp_id_left,
      Category2.vcomp_id_right,
      Category2.vcomp_whisker_apply,
      Category2.vcomp_whisker_arg,
      Category2.whisker_apply_assoc,
      Category2.whisker_arg_assoc,
      Category2.whisker_assoc,
      Category2.whisker_apply_id,
      Category2.whisker_arg_id,
      Exp,
  ] <;> try rfl)
)


infix:120 " ⟶ " => Exp

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

def FunctorPostComposition (A B C : Category) (F : Functor B C) : Functor (A ∶ B) (A ∶ C) := {
  obj G := FunctorCompose G F
  mor τ := FunctorActionOnTransformation τ F
  mor_compose := by catsimp
  mor_identity := by catsimp
}


def Hom2 (a : Cat2.{u, v}.C.Obj) : StrictFunctor2 Cat2.{u, v} Cat2.{max u v, max u v} where
  functor1 := {
    obj d := FunctorCategory.{u, v, u, v} a d
    mor f := FunctorPostComposition _ _ _ f
    mor_compose := by intros; simp[FunctorPostComposition]; catsimp;
    mor_identity := by intros; simp[FunctorPostComposition]; catsimp;
  }
  cell { α β : Cat2.C.Obj } { f g : Cat2.C.Mor α β } τ := {
    data x := TransformationConsumeFunctor x τ
    naturality := by
      intros
      simp
      catsimp
      apply Transformation.ext
      simp
      funext
      apply τ.naturality
  }
  cell_vcomp := by intros; simp[FunctorPostComposition]; catsimp;

def TupleCategory (S : Category.{u, v}) (T : Category.{u', v'}) : Category := {
  Obj := S.Obj × T.Obj
  Mor a b := (S.Mor a.fst b.fst) × (T.Mor a.snd b.snd)
  compose f g := ⟨ S.compose f.fst g.fst, T.compose f.snd g.snd ⟩
  compose_identity a := ⟨ S.compose_identity a.fst, T.compose_identity a.snd ⟩
  compose_identity_left := by simp
  compose_identity_right := by simp
  compose_assoc := by simp [Category.compose_assoc]
}

def OpCategory (S : Category) : Category := {
  Obj := S.Obj
  Mor a b := S.Mor b a
  compose f g := S.compose g f
  compose_identity := S.compose_identity
  compose_identity_left := by simp
  compose_identity_right :=by simp
  compose_assoc := by simp[Category.compose_assoc]
}

-- def TupleCategory2 (S : Category2.{u, v, w}) (T : Category2.{u', v', w'}) : Category2 := {
--   C := TupleCategory S.C T.C
--   Cell f g := (S.Cell f.fst g.fst) × (T.Cell f.snd g.snd)
--   cell_id a := ⟨ (S.cell_id a.fst),  (T.cell_id a.snd) ⟩
--   vcomp f g := _
--   vcomp_assoc := _
--   vcomp_id_right := _
--   vcomp_id_left := _
--   whisker_arg := _
--   whisker_apply := _
--   whisker_arg_id := _
--   whisker_apply_id := _
--   vcomp_whisker_arg := _
--   vcomp_whisker_apply := _
--   associator := _
--   associator_is_id := _
--   whisker_arg_assoc := _
--   whisker_apply_assoc := _
--   whisker_assoc := _
--   cell_natural := _
-- }

-- def Cat2.Hom : StrictFunctor2 (TupleCategory (OpCategory a) b) Cat2

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

def TypeCat : Category := {
  Obj := Type _
  Mor a b := a → b
  compose f g := g ∘ f
  compose_identity _ a := a
  compose_identity_left _ _ _ := rfl
  compose_identity_right _ _ _ := rfl
  compose_assoc _ _ _ := rfl
}

def Category.Hom (S : Category.{u, v}) :
  Functor (TupleCategory (OpCategory S) S) TypeCat := {
    obj pair := S.Mor pair.fst pair.snd
    mor pair := fun input => S.compose (S.compose (pair.fst) input) pair.snd
    mor_compose := by intros; funext; simp [TupleCategory, OpCategory, TypeCat, Category.compose_assoc];
    mor_identity := by simp [TupleCategory, OpCategory, TypeCat]
  }

structure IsInitialObject (T : Category) (obj : T.Obj) where
  mor (a : T.Obj) : T.Mor obj a
  unique (a : T.Obj) (h : T.Mor obj a) : h = mor a

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



def ConstantFunctor (A B :Category) (i : B.Obj) : Functor A B where
  obj x := i
  mor f := B.compose_identity i
  mor_identity := rfl
  mor_compose := by simp

def ConstantTranformation (A B : Category) {i j : B.Obj} (f : B.Mor i j) : Transformation (ConstantFunctor A B i) (ConstantFunctor A B j) where
  data x := f
  naturality := by simp [ConstantFunctor]

def Δ (J : Category.{u, v}) (C : Category.{u', v'}) : Functor C (FunctorCategory J C) where
  obj c := ConstantFunctor J C c
  mor f := ConstantTranformation J C f
  mor_compose := by intros; rfl
  mor_identity := by intros; rfl

-- def Cocone' (J : Category) (C : Category) (F : (OpCategory (FunctorCategory J C)).Obj)
--   := (Category.Hom (FunctorCategory J C)).obj ⟨ F, (Δ J C).obj  ⟩

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

structure CoconeMor (J : Category.{u, v}) (C : Category.{u', v'}) (F : (FunctorCategory J C).Obj) (a b : Cocone J C F) : Type (max (max u v) (max u' v')) where
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
  : ( J∶(Domain∶Codomain)) ⥤ (Domain∶(J∶Codomain))
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

-- structure Switch2 : StrictFunctor2

-- def ExtendFunctor
--   (J Domain Codomain : Category)
--   (Γ : Functor (FunctorCategory J Codomain) Codomain)
--   :
--   Functor (FunctorCategory J (FunctorCategory Domain Codomain)) (FunctorCategory Domain Codomain)
-- where
--   obj x := FunctorCompose (Switch.obj x) Γ
--   mor ε := FunctorActionOnTransformation (Switch.mor ε) Γ
--   mor_compose := by
--     intro a b f c h
--     apply FunctorActionOnTransformation.compose (Switch.mor f) (Switch.mor h) Γ
--   mor_identity := by
--     intro a
--     apply FunctorActionOnTransformation.identity

-- def Extend''
--   (J D C : Category)
--   :
--   Functor
--   (D∶(J∶C))
--   (FunctorCategory ((J∶C)∶C) (D∶C))
--   := FunctorComposition D (J∶C) C
-- def Extend'''
--   (J D C : Category)
--   :
--   Functor
--   (J∶(D∶C))
--   (FunctorCategory ((J∶C)∶C) (D∶C))
--   := FunctorCompose Switch (FunctorComposition D (J∶C) C)
-- def Extend'
--   (J D C : Category)
--   :
--   Functor
--   ((J∶C)∶C)
--   (FunctorCategory (D∶(J∶C)) (D∶C))
--   := Switch.obj (FunctorComposition D (J∶C) C)

-- def FunctorExtension
--   (J D C : Category)
--   :
--   Functor
--   ((J∶C)∶C)
--   (FunctorCategory (J∶(D∶C)) (D∶C))
-- := Switch.obj (FunctorCompose Switch (FunctorComposition D (J∶C) C))

-- def EndoExtension
--   (D C : Category)
--   : (C∶C) ⥤ (FunctorCategory (D∶C) (D∶C))
-- := Switch.obj (FunctorComposition D C C)

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



-- #check Switch.mor

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
--       apply Transformation.ext
--       funext q
--       apply Transformation.ext
--       funext w

--   }

-- def test  (J D C : Category)
--   (F G : Functor (J∶C) (J∶C))
--   (τ : Transformation F G)
--   (x : Functor D (J∶C))
--   : Transformation (FunctorCompose x F) (FunctorCompose x G)
--   := TransformationConsumeFunctor x τ

-- def test2 (J D C : Category)
--   (F G : Functor (J∶C) (J∶C))
--   (x : Functor J (D∶C))
--   (τ : Transformation (FunctorCompose (Switch.obj x) F) (FunctorCompose (Switch.obj x) G))
--   :

macro "catsimp_extended" : tactic => `(tactic|
  (simp [
      Switch, Δ, ConstantTranformation, ConstantFunctor, FunctorPostComposition
  ] <;> try rfl)
)

def ApplyCocone
  (J D C : Category)
  (jdc : Functor J (D∶C))
  (d : D.Obj)
  :
  Functor (CoconeCategory J (D ∶ C) jdc) (CoconeCategory J C ((Switch.obj jdc).obj d))
  := {
    obj jdc_cocone := {
      c := jdc_cocone.c.obj d
      data := (Switch.mor jdc_cocone.data).data d
    }
    mor jdc_mor := {
      c := jdc_mor.c.data d
      valid := by
        catsimp_extended;
        catsimp;
        ext x
        simp
        have big_valid := jdc_mor.valid
        simp [Δ, ConstantTranformation, FunctorCategory, TransformationCompose] at big_valid
        rw [← big_valid]
        simp
        rfl
    }
    mor_compose := by
      intros;
      catsimp_extended;
    mor_identity := by
      intros;
      catsimp_extended;
  }


-- def ExtendColimit
--   (J D C : Category)
--   (Γ : Functor (FunctorCategory J C) C)
--   (h : IsColimit  J C Γ)
--   :
--   IsColimit J (FunctorCategory D C) (FunctorCompose Switch ((Hom2 D).functor1.mor Γ))
-- where
--   τ := FunctorActionOnTransformation (TransformationConsumeFunctor Switch ((Hom2 D).cell h.τ)) Switch
--   uni jdc := {
--     mor a := {
--       c := {
--         data d :=
--           let jc := (Switch.obj jdc).obj d
--           let test := (h.uni jc).mor
--           let fixed_cocone := (ApplyCocone J D C jdc d).obj a

--           sorry
--         naturality := _
--       }
--       valid := _
--     }
--     unique := _
--   }



-- def Hom2Δ (J D C : Cat2.C.Obj) (Γ : Functor (FunctorCategory J C) C) :
--   Transformation
--     ((Hom2 D).functor1 ↻ (Γ ∘ᶠ Δ J C))
--     ((Switch ∘ᶠ ((Hom2 D).functor1 ↻ Γ)) ∘ᶠ Δ J (D∶C))
--   := sorry

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
