import Mathlib.Computability.RegularExpressions
import RegexPosix.Value

universe u

variable {α : Type u}

open RegularExpression
open Value

inductive POSIX : List α → RegularExpression α → Value α → Prop
  | epsilon : POSIX [] epsilon empty
  | char (c : α) : POSIX [c] (char c) (char c)
  | left (s : List α) (r₁ r₂ : RegularExpression α) (v : Value α) :
    POSIX s r₁ v →
    POSIX s (plus r₁ r₂) (left v)
  | right (s : List α) (r₁ r₂ : RegularExpression α) (v : Value α) :
    POSIX s r₂ v →
    s ∉ r₁.matches' →
    POSIX s (plus r₁ r₂) (right v)
  | mul (s₁ s₂ : List α) (r₁ r₂ : RegularExpression α) (v₁ v₂ : Value α) :
    POSIX s₁ r₁ v₁ →
    POSIX s₂ r₂ v₂ →
    ¬(∃ s₃ s₄, s₃ ≠ [] ∧ s₃ ++ s₄ = s₂ ∧ s₁ ++ s₃ ∈ r₁.matches' ∧ s₄ ∈ r₂.matches') →
    POSIX (s₁ ++ s₂) (comp r₁ r₂) (seq v₁ v₂)
  | star_nil (r : RegularExpression α) :
    POSIX [] (star r) (stars [])
  | stars (s₁ s₂ : List α) (r : RegularExpression α) (v : Value α) (vs : List (Value α)) :
    POSIX s₁ r v →
    POSIX s₂ (star r) (stars vs) →
    v.flat ≠ [] →
    ¬(∃ s₃ s₄, s₃ ≠ [] ∧ s₃ ++ s₄ = s₂ ∧ s₁ ++ s₃ ∈ r.matches' ∧ s₄ ∈ (star r).matches') →
    POSIX (s₁ ++ s₂) (star r) (stars (v::vs))

theorem correctness (s : List α) (r : RegularExpression α) (v : Value α) :
  POSIX s r v → s ∈ r.matches' ∧ v.flat = s := by
  intro h
  induction h with
  | epsilon => simp
  | char c =>
    simp
    ext
    rfl
  | left s r₁ r₂ v h ih =>
    simp
    exact ⟨Or.inl ih.left, ih.right⟩
  | right s r₁ r₂ v h hn ih =>
    simp
    exact ⟨Or.inr ih.left, ih.right⟩
  | mul s₁ s₂ r₁ r₂ v₁ v₂ h₁ h₂ hn ih₁ ih₂ =>
    simp
    refine ⟨⟨s₁, ih₁.left, s₂, ih₂.left, rfl⟩, ?_⟩
    rw [ih₁.right, ih₂.right]
  | star_nil r =>
    simp
    apply Language.nil_mem_kstar
  | stars  s₁ s₂ r v vs h₁ h₂ hn₁ hn₂ ih₁ ih₂ =>
    simp
    rw [ih₁.right, ih₂.right]
    simp
    sorry
