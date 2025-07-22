import RegexPosix.Regex
import Mathlib.Tactic.SplitIfs
import Mathlib.Data.Bool.Basic

universe u

inductive Value (α : Type u)
  | empty : Value α
  | char : α → Value α
  | left : Value α → Value α
  | right : Value α → Value α
  | seq : Value α → Value α → Value α
  | stars : List (Value α) → Value α
  deriving Repr

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
open Regex

inductive Inhab : Value α → Regex α → Prop
  | empty : Inhab empty epsilon
  | char (c : α) : Inhab (char c) (char c)
  | left {v₁ : Value α} {r₁ r₂ : Regex α} :
    Inhab v₁ r₁ →
    Inhab (left v₁) (plus r₁ r₂)
  | right {v₂ : Value α} {r₁ r₂ : Regex α} :
    Inhab v₂ r₂ →
    Inhab (right v₂) (plus r₁ r₂)
  | seq {v₁ v₂ : Value α} {r₁ r₂ : Regex α} :
    Inhab v₁ r₁ →
    Inhab v₂ r₂ →
    Inhab (seq v₁ v₂) (mul r₁ r₂)
  | star_nil {r : Regex α} :
    Inhab (stars []) (star r)
  | stars {v : Value α} {vs : List (Value α)} {r : Regex α} :
    Inhab v r →
    Inhab (stars vs) (star r) →
    Inhab (stars (v::vs)) (star r)

@[simp]
theorem inhab_zero {v : Value α} :
  ¬Inhab v emptyset := by
  intro h
  cases h

theorem inhab_left {v₁ : Value α} {r₁ r₂ : Regex α} :
  Inhab (left v₁) (plus r₁ r₂) → Inhab v₁ r₁ := by
  intro h
  cases h with
  | left h =>
    exact h

theorem inhab_right {v₂ : Value α} {r₁ r₂ : Regex α} :
  Inhab (right v₂) (plus r₁ r₂) → Inhab v₂ r₂ := by
  intro h
  cases h with
  | right h =>
    exact h

theorem inhab_seq {v₁ v₂ : Value α} {r₁ r₂ : Regex α} :
  Inhab (seq v₁ v₂) (mul r₁ r₂) → Inhab v₁ r₁ ∧ Inhab v₂ r₂ := by
  intro h
  cases h with
  | seq h₁ h₂ => exact ⟨h₁, h₂⟩

theorem inhab_seq_fst {v₁ v₂ : Value α} {r₁ r₂ : Regex α} :
  Inhab (seq v₁ v₂) (mul r₁ r₂) → Inhab v₁ r₁ := by
  intro h
  cases h with
  | seq h₁ _ => exact h₁

theorem inhab_seq_snd {v₁ v₂ : Value α} {r₁ r₂ : Regex α} :
  Inhab (seq v₁ v₂) (mul r₁ r₂) → Inhab v₂ r₂ := by
  intro h
  cases h with
  | seq _ h₂ => exact h₂

theorem inhab_stars_head {v : Value α} {vs : List (Value α)} {r : Regex α} :
  Inhab (stars (v::vs)) (star r) → Inhab v r := by
  intro h
  cases h with
  | stars h₁ _ => exact h₁

theorem inhab_stars_tail {v : Value α} {vs : List (Value α)} {r : Regex α} :
  Inhab (stars (v::vs)) (star r) → Inhab (stars vs) r.star := by
  intro h
  cases h with
  | stars _ h₂ => exact h₂

theorem  Inhab_not_nullable {r : Regex α} {v : Value α} (hn : ¬r.nullable) (hv : v.flat = []) :
  ¬Inhab v r := by
  intro h
  induction r generalizing v with
  | emptyset => nomatch h
  | epsilon => simp at hn
  | char =>
    cases h with
    | char => simp at hv
  | plus r₁ r₂ ih₁ ih₂ =>
    simp at hn
    cases h with
    | left h =>
      apply ih₁
      simp [hn]
      simp at hv
      exact hv
      exact h
    | right h =>
      apply ih₂
      simp [hn]
      simp at hv
      exact hv
      exact h
  | mul r₁ r₂ ih₁ ih₂ =>
    cases h with
    | seq h₁ h₂ =>
      simp at hv
      simp at hn
      apply ih₁
      intro hn₁
      apply ih₂
      simp [hn hn₁]
      exact hv.right
      exact h₂
      exact hv.left
      exact h₁
  | star r => simp at hn
