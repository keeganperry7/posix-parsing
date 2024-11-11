import Mathlib.Computability.RegularExpressions

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

open Value
open RegularExpression

inductive Inhab : Value α → RegularExpression α → Prop
  | empty : Inhab empty epsilon
  | char (c : α) : Inhab (char c) (char c)
  | left (v₁ : Value α) (r₁ r₂ : RegularExpression α) :
    Inhab v₁ r₁ →
    Inhab (left v₁) (plus r₁ r₂)
  | right (v₂ : Value α) (r₁ r₂ : RegularExpression α) :
    Inhab v₂ r₂ →
    Inhab (right v₂) (plus r₁ r₂)
  | seq (v₁ v₂ : Value α) (r₁ r₂ : RegularExpression α) :
    Inhab v₁ r₁ →
    Inhab v₂ r₂ →
    Inhab (seq v₁ v₂) (comp r₁ r₂)
  | star_nil (r : RegularExpression α) :
    Inhab (stars []) (star r)
  | stars (v : Value α) (vs : List (Value α)) (r : RegularExpression α) :
    Inhab v r →
    Inhab (stars vs) (star r) →
    Inhab (stars (v::vs)) (star r)

@[simp]
theorem inhab_zero (v : Value α) :
  ¬Inhab v zero := by
  intro h
  cases h

theorem inhab_left (v₁ : Value α) (r₁ r₂ : RegularExpression α) :
  Inhab (left v₁) (plus r₁ r₂) → Inhab v₁ r₁ := by
  intro h
  cases h with
  | left _ _ _ h =>
    exact h

theorem inhab_right (v₂ : Value α) (r₁ r₂ : RegularExpression α) :
  Inhab (right v₂) (plus r₁ r₂) → Inhab v₂ r₂ := by
  intro h
  cases h with
  | right _ _ _ h =>
    exact h

theorem inhab_seq (v₁ v₂ : Value α) (r₁ r₂ : RegularExpression α) :
  Inhab (seq v₁ v₂) (comp r₁ r₂) → Inhab v₁ r₁ ∧ Inhab v₂ r₂ := by
  intro h
  cases h with
  | seq _ _ _ _ h₁ h₂ => exact ⟨h₁, h₂⟩
