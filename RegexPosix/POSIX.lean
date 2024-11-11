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

theorem POSIX_epsilon (s : List α) (v : Value α) :
  POSIX s epsilon v → s = [] ∧ v = empty := by
  intro h
  cases h
  simp

theorem POSIX_char (s : List α) (c : α) (v : Value α) :
  POSIX s (char c) v → s = [c] ∧ v = Value.char c := by
  intro h
  cases h
  simp

-- Theorem 1 Part 1
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
    let ⟨L, hs₂, hL⟩ := ih₂.left
    use [s₁] ++ L
    simp
    exact ⟨hs₂, ih₁.left, hL⟩

-- Theorem 1 Part 2
theorem uniqueness (s : List α) (r : RegularExpression α) (v v' : Value α) :
  POSIX s r v ∧ POSIX s r v' → v = v' := by
  intro ⟨h₁, h₂⟩
  induction h₁ generalizing v' with
  | epsilon =>
    apply POSIX_epsilon at h₂
    rw [h₂.right]
  | char c =>
    apply POSIX_char at h₂
    rw [h₂.right]
  | left s r₁ r₂ v hv ih =>
    cases h₂ with
    | left _ _ _ v' hv' =>
      apply ih at hv'
      simp
      exact hv'
    | right _ _ _ v' hv' hn =>
      apply correctness at hv
      absurd hn
      exact hv.left
  | right s r₁ r₂ v hv hn ih =>
    cases h₂ with
    | left _ _ _ v' hv' =>
      apply correctness at hv'
      absurd hn
      exact hv'.left
    | right _ _ _ v' hv' _=>
      apply ih at hv'
      simp
      exact hv'
  | mul s₁ s₂ r₁ r₂ v₁ v₂ hv₁ hv₂ hn ih₁ ih₂ =>
    sorry
  | star_nil => sorry
  | stars => sorry
