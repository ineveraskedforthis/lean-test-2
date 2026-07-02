def hello := "world"

universe u v w


#check Nat


inductive tree (α : Type u) where
  | basic_node : List α → tree α
  | node : Nat → List (tree α) → tree α

def check_list {β : Type u} (p : β → Prop) (a : List β) : Prop := match a with
| [] => True
| x :: xs => p x ∧ check_list p xs

@[simp]
theorem check_list_nil {β : Type u}  (p : β → Prop) : check_list p [] = True := by rfl

@[simp]
def tree.valid_depth {k : Type u} (d : Nat) (a : tree k)  : Prop :=
  match a with
  | tree.basic_node _ => True
  | tree.node i l => match d with
    | 0 => False
    | d' + 1 => (i = d' + 1) ∧ (check_list (tree.valid_depth d') l)

@[simp]
def tree.implied_depth {k : Type u} (a : tree k) : Nat :=
  match a with
  | tree.basic_node _ => 0
  | tree.node i _ => i

-- theorem tree.valid_of_inner {k : Type u} (a : tree k) (h : a.valid_depth a.implied_depth) :
--   a.valid_depth a.implied_depth := by
--   match a with
--   | tree.basic_node _ => simp_all [valid_depth]
--   | tree.node i q =>
--     simp_all


def tree.first_depth_is {k : Type u} (a : tree k) (d : Nat) : Prop :=
  match a with
  | tree.basic_node _ => d = 0
  | tree.node _ x => match x with
    | [] => True
    | head :: _ =>
      match d with
      | 0 => False
      | d + 1 => head.first_depth_is d


def tree.any_depth_is {k : Type u}  (d : Nat) (a : tree k) : Prop :=
  match d with
  | 0 => match a with
    | tree.basic_node _ => True
    | tree.node _ _ => False
  | d + 1 =>
    match a with
    | tree.basic_node _ => False
    | tree.node _ x => check_list (tree.any_depth_is d) x

-- theorem tree.implied_is_first
--   {k : Type u} (d : Nat) (a : tree k) (h: a.valid_depth d)
--   : a.first_depth_is a.implied_depth :=
--   by
--   match a with
--   | tree.basic_node x =>
--     simp [first_depth_is, implied_depth]
--   | tree.node i x =>
--     match x with
--       | [] =>
--         simp_all [first_depth_is]
--       | head :: tail =>
--         match i with
--         | 0 =>
--           match d with
--           | 0 =>
--             simp_all
--           | d' + 1 =>
--             rw [implied_depth, first_depth_is]
--             rw [valid_depth] at h
--             have q := h.left
--             rw [←q, check_list] at h
--             simp_all
--             if
--         | i + 1 =>
--           simp_all [first_depth_is]
--           simp_all [valid_depth, check_list]

def tree.almost_empty  {k : Type u} (P : k → Bool) (a : tree k) := match a with
  | tree.basic_node x => x.all P
  | tree.node i x =>
    match x with
    | [] => true
    | head :: tail =>
      head.almost_empty P ∧ (tree.node i tail).almost_empty P

def example_of_recursive_list : tree Nat :=
  tree.node 2 [ tree.basic_node [1], tree.node 1 [ tree.basic_node [0] ], tree.basic_node [0, 0, 0] ]

theorem tree.subtree_of_valid  {k : Type u} (d : Nat) (a : tree k) (ha : a.valid_depth d) :
  match a with
  | tree.basic_node _ => True
  | tree.node 0 _ => False
  | tree.node (d' + 1) a' => check_list (tree.valid_depth d') a'
  := by
  split
  case h_1 =>
    simp
  case h_2 q qq qqq qqqq =>
    match d with
    | 0 => simp_all
    | d + 1 => simp_all
  case h_3 T q qq qqq qqqq  =>
    match qqq with
    | [] => simp
    | head :: tail =>
      match d with
      | 0 => simp_all
      | d + 1 => simp_all

#check Bool.and

def tree.BEq {k : Type u} [BEq k] (d : Nat) (a : tree k) (b : tree k) (ha : a.valid_depth d) (hb : b.valid_depth d) :=
  have qa := tree.subtree_of_valid d a ha
  have qb := tree.subtree_of_valid d a ha
  match a, b with
  | tree.basic_node a', tree.basic_node b' => a' == b'
  | tree.basic_node _, tree.node _ _ => false
  | tree.node _ _, tree.basic_node _ => false
  | tree.node da a', tree.node db b' => by
    if da == db then
      match a', b' with
      | [], [] => exact true
      | [], _ => exact false
      | _, [] => exact false
      | heada' :: taila' , headb' ::tailb' =>
        match d with
        | 0 =>
          rw [valid_depth] at ha
          contradiction
        | prev_d + 1 =>
          rw [valid_depth] at ha hb
          have da_eq := ha.left
          have db_eq := hb.left
          simp_all [check_list]
          apply
            (tree.BEq prev_d heada' headb' ha.left hb.left)
            && (tree.BEq (prev_d + 1) (tree.node (prev_d + 1) taila') (tree.node (prev_d + 1) tailb') _ _)
          rw [valid_depth]
          simp_all
          rw [valid_depth]
          simp_all
    else
      exact false
