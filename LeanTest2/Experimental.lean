def TotalDimension (dimensions : List Nat) : Nat :=
match dimensions with
  | [] => 1
  | a :: tail => a * TotalDimension tail



structure Data (dimensions : List Nat) where
  Raw : Vector Float (TotalDimension dimensions)
