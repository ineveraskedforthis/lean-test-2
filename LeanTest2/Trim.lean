namespace trim_utilities

universe u v w

def array {k : Type u} (P : k → Bool) (a : Array k) : Array k :=
  if h : a.size = 0 then a else (if P a.back then array P (a.pop) else a)
  termination_by a.size

def head {k : Type u} (P : k → Bool) (a : List k) : List k :=
  match a with
  | [] => []
  | x :: a' => if P x then head P a' else a


prefix:100 "↓ₕ" => head

theorem head.idempotent {k : Type u} (P : k → Bool) (a : List k) :
  head P (head P a) = head P a := by
  match a with
  | [] => simp [head]
  | x :: a' =>
    simp [head]
    rw [apply_ite (head P), head.idempotent, head]
    simp
    intro h1
    simp [h1]

def tail {k : Type u} (P : k → Bool) (a : List k) : List k :=
  match a with
  | [] => []
  | ax :: a => match tail P (a) with
    | [] => if P ax then [] else [ax]
    | _ => ax :: tail P (a)


prefix:100 "↓ₜ" => tail

theorem tail.idempotent {k : Type u} (P : k → Bool) (a : List k)
  : tail P (tail P a) = (tail P a) := by
  match a with
  | [] => simp [tail]
  | ax :: a =>
    simp [tail]
    split
    rw [apply_ite (tail P)]
    simp [tail]
    simp [tail, tail.idempotent]

theorem tail.nil_of_all {k : Type u} (P : k → Bool) (a : List k) (h : ∀ x ∈ a, P x) : tail P a = [] := by
  match a with
  | [] =>
    simp_all [tail]
  | list_head :: list_tail =>
    simp_all[tail]
    split
    · case h_1 =>
      rfl
    · case h_2 =>
      simp_all
      have q := nil_of_all P list_tail h.right
      contradiction

theorem tail.nil_of_all' {k : Type u} (P : k → Bool) (a : List k) (h : a.all P) : tail P a = [] := by
  simp_all [nil_of_all]

theorem tail.not_nil_of_not_all {k : Type u} (P : k → Bool) (a : List k) (h : ∃ x ∈ a, P x = false) : ¬ tail P a = [] := by
  match a with
  | [] => simp_all
  | ha :: ta =>
    simp_all [tail]
    cases h
    · case inl q =>
      simp_all
      split
      simp
      simp
    · case inr q =>
      have s := not_nil_of_not_all P ta q
      simp_all


theorem tail.not_nil_of_not_all' {k : Type u} (P : k → Bool) (a : List k) (h : ¬ a.all P) : ¬ tail P a = [] := by
  simp_all [not_nil_of_not_all]

theorem tail.ignore_head (P : k → Bool) (x : k)  (a : List k) (h : ¬ a.all P) : tail P (x :: a) = x :: tail P a := by
  simp_all [tail, not_nil_of_not_all' P a h]

theorem tail.nil_of_all_except_first {k : Type u} (P : k → Bool) (x : k) (a : List k) (h : a.all P) : tail P (x :: a) = tail P [x] := by
  simp_all
  simp [tail]
  split
  rfl
  have q := nil_of_all P a h
  simp_all


theorem tail.all {k : Type u} (P : k → Bool) (a : List k)
  (h : tail P a = []) : a.all P := by
  match a with
  | [] =>
    simp_all
  | list_head :: list_tail =>
    simp_all [tail]
    split at h

    if P list_head then
      simp_all
      have q := tail.all P list_tail
      simp at q
      apply q
      assumption
    else
      simp_all
    have q := List.cons_ne_nil list_head (tail P list_tail)
    contradiction

theorem tail.not_all_of_not_nil {k : Type u} (P : k → Bool) (a : List k)
  (h : ¬ (tail P a = [])) : ¬ a.all P := by
  match a with
  | [] => simp_all [tail]
  | qa :: ta =>
    simp_all [tail]
    split at h
    simp_all
    simp_all
    · case h_2 ww www =>
      have q := not_all_of_not_nil P ta www
      simp_all


@[simp]
theorem tail.P_singleton {k : Type u} (P : k → Bool) (z : k) (h : P z) : tail P [z] = [] := by
  simpa [tail]

def last_item {k : Type u} (x : k) (a  : List k) :=
  match a with
  | [] => x
  | q :: qq => last_item q qq

def everything_but_last {k : Type u} (x : k) (a  : List k) :=
  match a with
  | [] => []
  | q :: qq => x :: everything_but_last q qq

theorem disassemble {k : Type u} (x : k) (a  : List k) : x :: a = (everything_but_last x a) ++ [(last_item x a)] := by
  match a with
  | [] => simp [everything_but_last, last_item]
  | q :: qq =>
    simp [everything_but_last, last_item]
    apply disassemble

theorem append_singleton {k : Type u} (a  : List k) : a = [] ∨ ∃ a' : List k, ∃ x : k, a = a' ++ [x] := by
  match a with
  | [] => simp
  | y :: a'' =>
    apply Or.intro_right
    exact ⟨ (everything_but_last y a''), ⟨ last_item y a'', by rw [←disassemble] ⟩ ⟩

theorem append_singleton' {k : Type u} (y : k) (a  : List k) : ∃ a' : List k, ∃ x : k, y :: a = a' ++ [x] := by
  exact ⟨ (everything_but_last y a), ⟨ last_item y a, by rw [←disassemble] ⟩ ⟩


theorem append_singleton'' {k : Type u} (a  : List k) (y : k) : ∃ x : k, ∃ a' : List k, a ++ [y] = x :: a' := by
  match a with
  | [] => exact ⟨ y, ⟨ [], by simp ⟩  ⟩
  | q :: qq =>
    rw [List.cons_append]
    exact ⟨ q, ⟨ qq ++ [y], by simp ⟩  ⟩

@[simp]
theorem head.nil {k : Type u} (P : k → Bool) : head P [] = [] := by simp[head]
@[simp]
theorem tail.nil {k : Type u} (P : k → Bool) : tail P [] = [] := by simp[tail]

@[simp]
def head' {k : Type u} (P : k → Bool) (a : List k) (x : k) := match head P a with
  | [] => if P x then [] else [x]
  | _ => head P a ++ [x]

@[simp]
theorem head_is_head' {k : Type u} (P : k → Bool) (a : List k) (x : k) :
  head P (a ++ [x]) = head' P a x := by
  match a with
  | [] => simp [head, head']
  | a_head :: a_center =>
    simp [head, head']
    split
    case isTrue a_empty =>
      rw [head_is_head', head']
    case isFalse a_not_empty =>
      simp_all

theorem reverse' {k : Type u} (P : k → Bool) (a : List k) : tail P a = (head P a.reverse).reverse := by
  match a with
  | [] => simp [tail]
  | x :: a_tail_big =>
    have h := reverse' P a_tail_big
    match a_tail_big with
    | [] => simp [head, tail, apply_ite]
    | xx :: a_tail =>
      rcases append_singleton' xx a_tail with ⟨ q, ⟨ qq, qqq ⟩ ⟩
      rw [qqq]
      simp [head, tail]
      -- have termination :  q.length < a_tail.length + 1 := by
      rw [qqq] at h
      rw [h]
      rw [List.reverse_append]
      simp_all [head, apply_ite]
      intro pqq
      split
      case h_1 =>
        simp_all [apply_ite]
      case h_2 =>
        simp_all
  termination_by a.length

theorem tail.append_P_singleton {k : Type u} (P : k → Bool) (a : List k) (z : k) (h : P z) : tail P (a ++ [z]) = tail P a := by
  simp [reverse', head]
  rw [h]
  simp only [Bool.true_eq_false, false_implies]

@[simp]
theorem tail.nP_singleton {k : Type u} (P : k → Bool) (z : k) (h : !(P z)) : tail P [z] = [z] := by
  simp_all [tail]

@[simp]
theorem tail.singleton {k : Type u} (P : k → Bool) (x: k)
  : tail P [x] = if P x then [] else [x] := by
  simp [tail]


theorem head.leading_P {k : Type u} (P : k → Bool) (a : List k) (x : k) (b : List k) (h : head P a = x :: b) : ! P x := by
  match a with
  | [] => simp_all
  | q :: qa =>
    simp [head] at h
    split at h
    apply leading_P P qa x b h
    simp_all

theorem tail.leading_P {k : Type u} (P : k → Bool) (a : List k) (x : k) (b : List k) (h : tail P a = b ++ [x]) : ! P x :=by
  match a with
  | [] =>
    simp_all
  | q :: qa =>
    have hh := congrArg List.reverse h
    rw [List.reverse_append, List.reverse_singleton, List.singleton_append] at hh
    rw [reverse', List.reverse_reverse] at hh
    have hhh := head.leading_P P _ x b.reverse hh
    apply hhh


theorem head.if_reduced  {k : Type u} (P : k → Bool) (x : k) (a : List k) (h : head P (x :: a) = x :: a) : !P x := by
  apply leading_P P (x :: a) x a h

theorem tail.if_reduced  {k : Type u} (P : k → Bool) (a : List k) (x : k)  (h : tail P (a ++ [x]) = a ++ [x]) : !P x := by
  apply leading_P P (a ++ [x]) x a h

theorem head.reduced_if {k : Type u} (P : k → Bool) (a : List k) (z : k) (h : ! P z) : head P (z :: a) = z :: a := by
  simp_all [head]

theorem tail.reduced_if {k : Type u} (P : k → Bool) (a : List k) (z : k) (h : ! P z) : tail P (a ++ [z]) = a ++ [z] := by
  simp_all [reverse', head.reduced_if]

theorem tail.cons {k : Type u} (P : k → Bool) (a : List k) (z : k) :
  tail P (z :: a) = tail P (z :: tail P a) := by
  simp [tail, idempotent]

theorem tail.cons' {k : Type u} (P : k → Bool) (a : List k) (z : k) :
  tail P (z :: a) = if P z then tail P (z :: tail P a) else z :: tail P a := by
  split
  simp [tail, idempotent]
  simp [tail]
  split
  simp_all
  rfl

theorem tail.reduced_iff {k : Type u} (P : k → Bool) (s : k) (a : List k)
  :  trim_utilities.tail P (a ++ [s]) = (a ++ [s]) ↔ ! P s := by
  simp
  constructor
  · case mp =>
    intro h
    have hh := trim_utilities.tail.if_reduced P a s h
    simp_all
  · case mpr =>
    intro s_not_zero
    apply trim_utilities.tail.reduced_if
    simp_all

-- @[simp]
theorem tail.head_reduced
  {k : Type u} (P : k → Bool) (x : k) (x' : k) (a : List k)
  (h : trim_utilities.tail P (x :: a) = (x :: a)) :
  trim_utilities.tail P (x' :: (x :: a)) = (x' :: (x :: a)) := by
  rcases append_singleton' x a with ⟨ a', ⟨y, ha'y⟩ ⟩
  rw [ha'y] at h
  have ha := tail.if_reduced P a' y h
  rw [ha'y, ←List.cons_append]
  apply tail.reduced_if P (x' :: a') y ha

-- @[simp]
theorem tail.tail_reduced
  {k : Type u} (P : k → Bool) (x : k) (a : List k)
  (h : trim_utilities.tail P (x :: a) = (x :: a)) :
  trim_utilities.tail P a = a := by
  have a_decomposition := append_singleton a
  match a with
  | [] => simp
  | q :: qa =>
    simp_all
    rcases a_decomposition with ⟨ a', ⟨y, ha'y⟩ ⟩
    rw [ha'y, ←List.cons_append] at h
    have ha := tail.if_reduced P (x :: a') y h
    rw [ha'y]
    apply tail.reduced_if P a' y ha

theorem tail.map
  {k : Type u} (P : k → Bool) (a : List k) (f : k → k) (h : ∀ x : k, P x ↔ P (f x))
  : tail P (List.map f a) = List.map f  ( tail P a ) := by
  match a with
  | [] => simp
  | ha :: ta =>
    rw [List.map_cons]
    rw [tail]
    rw [tail]
    simp [(h ha)]
    split
    · case h_1 w ww =>
      rw [tail.map P ta f h] at ww
      have ww' := List.map_eq_nil_iff.mp ww
      split
      split
      · case h_1 =>
        simp
      · case h_2 t tt ttt =>
        contradiction
      rw [ww']
      simp
    · case h_2 w ww =>
      rw [tail.map P ta f h] at ww
      split
      · case h_1 b bb =>
        rw [bb] at ww
        contradiction
      · case h_2 b bb =>
        rw [List.map_cons]
        congr 1
        apply tail.map P ta f h



theorem tail.all_of_nil  {k : Type u} (P : k → Bool) (a : List k)  (h : tail P a = []) : ∀ x ∈ a, P x := by
  match a with
  | [] => simp
  | ha :: ta =>
    intro x hx
    rw [List.mem_cons] at hx
    rw [tail] at h
    split at h
    · case h_1 w ww =>
      have wq := tail.all_of_nil P ta ww x
      if P ha then
        simp_all
        cases hx
        · case inl m mm =>
          rw [mm, m]
        · case inr m mm =>
          apply wq mm
      else
        simp_all
    · case h_2 w ww =>
      contradiction



end trim_utilities
