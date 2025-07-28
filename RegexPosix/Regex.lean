import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.SimpRw

universe u

inductive Regex (α :  Type u) : Type u where
  | emptyset : Regex α
  | epsilon : Regex α
  | char : α → Regex α
  | plus : Regex α → Regex α → Regex α
  | mul : Regex α → Regex α → Regex α
  | star : Regex α → Regex α
  deriving Repr

namespace Regex

variable {α : Type u}

inductive Matches : List α → Regex α → Prop
  | epsilon : Matches [] epsilon
  | char {c : α} : Matches [c] (char c)
  | plus_left {s : List α} {r₁ r₂ : Regex α} :
    Matches s r₁ →
    Matches s (r₁.plus r₂)
  | plus_right {s : List α} {r₁ r₂ : Regex α} :
    Matches s r₂ →
    Matches s (r₁.plus r₂)
  | mul {s₁ s₂ s : List α} {r₁ r₂ : Regex α} :
    s₁ ++ s₂ = s →
    Matches s₁ r₁ →
    Matches s₂ r₂ →
    Matches s (r₁.mul r₂)
  | star_nil {r : Regex α} :
    Matches [] r.star
  | stars {s₁ s₂ s : List α} {r : Regex α} :
    s₁ ++ s₂ = s →
    Matches s₁ r →
    Matches s₂ r.star →
    Matches s r.star

theorem Matches_epsilon {s : List α} :
  Matches s epsilon ↔ s = [] := by
  constructor
  · intro h
    cases h
    rfl
  · intro h
    rw [h]
    exact Matches.epsilon

theorem Matches_char {c : α} {s : List α} :
  Matches s (char c) ↔ s = [c] := by
  constructor
  · intro h
    cases h
    rfl
  · intro h
    rw [h]
    exact Matches.char

theorem Matches_plus {s : List α} {r₁ r₂ : Regex α} :
  Matches s (r₁.plus r₂) ↔ Matches s r₁ ∨ Matches s r₂ := by
  constructor
  · intro h
    cases h with
    | plus_left h => exact Or.inl h
    | plus_right h => exact Or.inr h
  · intro h
    cases h with
    | inl h => exact Matches.plus_left h
    | inr h => exact Matches.plus_right h

theorem Matches_mul {s : List α} {r₁ r₂ : Regex α} :
  Matches s (r₁.mul r₂) ↔ ∃ s₁ s₂, s₁ ++ s₂ = s ∧ Matches s₁ r₁ ∧ Matches s₂ r₂ := by
  constructor
  · intro h
    cases h with
    | mul hs h₁ h₂ => exact ⟨_, _ , hs, h₁, h₂⟩
  · intro ⟨_, _, hs, h₁, h₂⟩
    exact Matches.mul hs h₁ h₂

theorem Matches_star {s : List α} {r : Regex α} :
  Matches s r.star ↔ s = [] ∨ (∃ s₁ s₂, s₁ ≠ [] ∧ s₁ ++ s₂ = s ∧ Matches s₁ r ∧ Matches s₂ r.star) := by
  generalize hr : r.star = r'
  constructor
  · intro h
    induction h with
    | epsilon => nomatch hr
    | char => nomatch hr
    | plus_left => nomatch hr
    | plus_right => nomatch hr
    | mul => nomatch hr
    | star_nil => exact Or.inl rfl
    | @stars s₁ s₂ s _ hs' h₁ h₂ ih₁ ih₂ =>
      simp at hr
      subst hr
      cases s₁ with
      | nil =>
        simp at hs'
        subst hs'
        exact ih₂ rfl
      | cons x xs =>
        exact Or.inr ⟨x::xs, s₂, by simp, hs', h₁, h₂⟩
  · intro h
    subst hr
    match h with
    | Or.inl h =>
      subst h
      exact Matches.star_nil
    | Or.inr ⟨s₁, s₂, _, hs, h₁, h₂⟩ =>
      exact Matches.stars hs h₁ h₂

@[simp]
def nullable : Regex α → Bool
  | emptyset => false
  | epsilon => true
  | char _ => false
  | plus r₁ r₂ => r₁.nullable || r₂.nullable
  | mul r₁ r₂ => r₁.nullable && r₂.nullable
  | star _ => true

theorem nullable_iff_matches_nil {r : Regex α} :
  r.nullable ↔ Matches [] r := by
  induction r with
  | emptyset => exact ⟨nofun, nofun⟩
  | epsilon =>
    simp only [nullable, true_iff]
    exact Matches.epsilon
  | char => exact ⟨nofun, nofun⟩
  | plus r₁ r₂ ih₁ ih₂ =>
    simp only [nullable, Bool.or_eq_true]
    rw [ih₁, ih₂, Matches_plus]
  | mul r₁ r₂ ih₁ ih₂ =>
    simp only [nullable, Bool.and_eq_true]
    rw [ih₁, ih₂, Matches_mul]
    constructor
    · intro ⟨h₁, h₂⟩
      exact ⟨[], [], (List.append_nil []), h₁, h₂⟩
    · intro ⟨s₁, s₂, hs, h₁, h₂⟩
      simp at hs
      rw [hs.left] at h₁
      rw [hs.right] at h₂
      exact ⟨h₁, h₂⟩
  | star r =>
    simp only [nullable, true_iff]
    exact Matches.star_nil

variable [DecidableEq α]

@[simp]
def deriv : Regex α → α → Regex α
  | emptyset, _ => emptyset
  | epsilon, _ => emptyset
  | char d, c => if c = d then epsilon else emptyset
  | plus r₁ r₂, c => (r₁.deriv c).plus (r₂.deriv c)
  | mul r₁ r₂, c =>
    if r₁.nullable
      then ((r₁.deriv c).mul r₂).plus (r₂.deriv c)
      else (r₁.deriv c).mul r₂
  | star r, c => (r.deriv c).mul r.star

theorem Matches_deriv {r : Regex α} {c : α} {s : List α} :
  Matches (c::s) r ↔ Matches s (r.deriv c) := by
  induction r generalizing s with
  | emptyset =>
    rw [deriv]
    constructor
    · intro h
      nomatch h
    · intro h
      nomatch h
  | epsilon =>
    rw [deriv]
    constructor
    · intro h
      nomatch h
    · intro h
      nomatch h
  | char c =>
    rw [Matches_char, deriv]
    rw [List.cons.injEq]
    constructor
    · intro ⟨hc, hs⟩
      rw [hc, hs]
      simp only [↓reduceIte]
      exact Matches.epsilon
    · intro h
      split at h
      · cases h
        refine ⟨?_, rfl⟩
        assumption
      · nomatch h
  | plus r₁ r₂ ih₁ ih₂ =>
    rw [deriv]
    rw [Matches_plus, Matches_plus]
    rw [ih₁, ih₂]
  | mul r₁ r₂ ih₁ ih₂ =>
    rw [deriv]
    split_ifs with hn
    · rw [Matches_plus, Matches_mul, Matches_mul]
      simp_rw [←ih₁, ←ih₂]
      constructor
      · intro ⟨s₁, s₂, hs, h₁, h₂⟩
        rw [List.append_eq_cons_iff] at hs
        match hs with
        | Or.inl hs =>
          rw [hs.right] at h₂
          exact Or.inr h₂
        | Or.inr ⟨as, hs₁, hs⟩ =>
          rw [hs₁] at h₁
          exact Or.inl ⟨as, s₂, hs.symm, h₁, h₂⟩
      · intro h
        match h with
        | Or.inl ⟨s₁, s₂, hs, h₁, h₂⟩ =>
          exact ⟨c::s₁, s₂, by simp [hs], h₁, h₂⟩
        | Or.inr h =>
          rw [nullable_iff_matches_nil] at hn
          exact ⟨[], c::s, by simp, hn, h⟩
    · rw [Matches_mul, Matches_mul]
      simp_rw [←ih₁]
      constructor
      · intro ⟨s₁, s₂, hs, h₁, h₂⟩
        rw [List.append_eq_cons_iff] at hs
        match hs with
        | Or.inl hs =>
          rw [hs.left] at h₁
          rw [nullable_iff_matches_nil] at hn
          exact absurd h₁ hn
        | Or.inr ⟨as, hs₁, hs⟩ =>
          rw [hs₁] at h₁
          exact ⟨as, s₂, hs.symm, h₁, h₂⟩
      · intro ⟨s₁, s₂, hs, h₁, h₂⟩
        exact ⟨c::s₁, s₂, by simp [hs], h₁, h₂⟩
  | star r ih =>
    rw [deriv]
    constructor
    · intro h
      rw [Matches_star] at h
      simp at h
      rcases h with ⟨s₁, hs₁, s₂, hs, h₁, h₂⟩
      cases s₁ with
      | nil => contradiction
      | cons x xs =>
        simp at hs
        rw [hs.left, ih] at h₁
        exact Matches.mul hs.right h₁ h₂
    · intro h
      cases h with
      | mul hs h₁ h₂ =>
        rw [←ih] at h₁
        rw [←hs, ←List.cons_append]
        exact Matches.stars rfl h₁ h₂

@[simp]
def derivs : Regex α → List α → Regex α
  | r, [] => r
  | r, c::s => (r.deriv c).derivs s

theorem Matches_derivs (r : Regex α) (s : List α) :
  Matches s r ↔ Matches [] (r.derivs s) := by
  induction s generalizing r with
  | nil => rfl
  | cons x xs ih =>
    rw [Matches_deriv, ih]
    rfl
