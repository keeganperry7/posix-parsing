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

inductive Parse : Regex α → Type u
  | empty : Parse epsilon
  | char (c : α) : Parse (char c)
  | left {r₁ r₂ : Regex α} :
    Parse r₁ →
    Parse (r₁.plus r₂)
  | right {r₁ r₂ : Regex α} :
    Parse r₂ →
    Parse (r₁.plus r₂)
  | seq {r₁ r₂ : Regex α} :
    Parse r₁ →
    Parse r₂ →
    Parse (r₁.mul r₂)
  | star_nil {r : Regex α} :
    Parse r.star
  | star_cons {r : Regex α} :
    Parse r →
    Parse r.star →
    Parse r.star

protected def Parse.repr [Repr α] {r : Regex α} (p : Parse r) (n : Nat) : Std.Format :=
  let _ : Std.ToFormat α := ⟨repr⟩
  match r, n with
  | Regex.epsilon, _ => "Empty"
  | Regex.char c, _ => "Char " ++ repr c
  | Regex.plus _ _, n =>
    match p with
    | Parse.left p => "Left (" ++ p.repr n ++ ")"
    | Parse.right p => "Right (" ++ p.repr n ++ ")"
  | Regex.mul _ _, n =>
    match p with
    | Parse.seq p₁ p₂ => "Seq (" ++ p₁.repr n ++ ") (" ++ p₂.repr n ++ ")"
  | Regex.star r, _ =>
    match p with
    | star_nil => "Stars []"
    | ps => "Stars [" ++ reprStars ps n ++ "]"
    where
      reprStars [Repr α] {r : Regex α} (p : Parse (star r)) (n : Nat) : Std.Format :=
        match p, n with
        | Parse.star_nil, _ => ""
        | Parse.star_cons p Parse.star_nil, n => p.repr n
        | Parse.star_cons p ps, n => p.repr n ++ ", " ++ reprStars ps n

instance [Repr α] {r : Regex α} : Repr (Parse r) where
  reprPrec := Parse.repr

@[simp]
def Parse.flat {r : Regex α} : Parse r → List α
  | empty => []
  | char c => [c]
  | left p => p.flat
  | right p => p.flat
  | seq p₁ p₂ => p₁.flat ++ p₂.flat
  | star_nil => []
  | star_cons p ps => p.flat ++ ps.flat

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

theorem Inhab.matches {r : Regex α} {v : Value α} :
  Inhab v r → r.Matches v.flat
  | empty => (Value.flat.eq_def _) ▸ Matches.epsilon
  | char c => (Value.flat.eq_def _) ▸ Matches.char
  | left h => (Value.flat.eq_def _) ▸ h.matches.left
  | right h => (Value.flat.eq_def _) ▸ h.matches.right
  | seq h₁ h₂ => (Value.flat.eq_def _) ▸ Matches.mul rfl h₁.matches h₂.matches
  | star_nil => (Value.flat.eq_def _) ▸ Matches.star_nil
  | stars h₁ h₂ => (Value.flat.eq_def _) ▸ Matches.stars rfl h₁.matches h₂.matches

theorem Parse.matches {r : Regex α} :
  (p : Parse r) → r.Matches p.flat
  | empty => Matches.epsilon
  | char c => Matches.char
  | left p => p.matches.left
  | right p => p.matches.right
  | seq p₁ p₂ => Matches.mul rfl p₁.matches p₂.matches
  | star_nil => Matches.star_nil
  | star_cons p ps => Matches.stars rfl p.matches ps.matches

theorem matches_inhab {r : Regex α} {s : List α} :
  r.Matches s → ∃ v, v.flat = s ∧ Inhab v r := by
  intro h
  induction h with
  | epsilon => exact ⟨Value.empty, by simp, Inhab.empty⟩
  | char => exact ⟨Value.char _, by simp, Inhab.char _⟩
  | left h ih =>
    rcases ih with ⟨v, hv, ih⟩
    exact ⟨v.left, by simp [hv], ih.left⟩
  | right h ih =>
    rcases ih with ⟨v, hv, ih⟩
    exact ⟨v.right, by simp [hv], ih.right⟩
  | mul hs h₁ h₂ ih₁ ih₂ =>
    rcases ih₁ with ⟨v₁, hv₁, ih₁⟩
    rcases ih₂ with ⟨v₂, hv₂, ih₂⟩
    exact ⟨v₁.seq v₂, by simp [hv₁, hv₂, hs], ih₁.seq ih₂⟩
  | star_nil => exact ⟨Value.stars [], by simp, Inhab.star_nil⟩
  | stars hs h₁ h₂ ih₁ ih₂ =>
    rcases ih₁ with ⟨v, hv, ih₁⟩
    rcases ih₂ with ⟨vs, hvs, ih₂⟩
    match vs with
    | Value.stars vs =>
      exact ⟨Value.stars (v::vs), by simp [hv, hvs, hs], Inhab.stars ih₁ ih₂⟩

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
