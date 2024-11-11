universe u

inductive Value (α : Type u)
  | empty : Value α
  | char : α → Value α
  | left : Value α → Value α
  | right : Value α → Value α
  | seq : Value α → Value α → Value α
  | stars : List (Value α) → Value α

variable {α : Type u}

@[simp]
def Value.flat : Value α → List α
  | empty => []
  | char c => [c]
  | left v => v.flat
  | right v => v.flat
  | seq v₁ v₂ => v₁.flat ++ v₂.flat
  | stars [] => []
  | stars (v::vs) => v.flat ++ (stars vs).flat
