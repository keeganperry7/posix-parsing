import RegexPosix.Regex
import Mathlib.Tactic.SplitIfs
import Mathlib.Data.Bool.Basic

universe u

variable {α : Type u}

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

def Parse.cast {r₁ r₂ : Regex α} (h : r₁ = r₂) (p : Parse r₁) : Parse r₂ :=
  h ▸ p

def Parse.cast_rfl {r : Regex α} {p : Parse r} : p.cast rfl = p := rfl

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

theorem Parse.matches {r : Regex α} :
  (p : Parse r) → r.Matches p.flat
  | empty => Matches.epsilon
  | char c => Matches.char
  | left p => p.matches.left
  | right p => p.matches.right
  | seq p₁ p₂ => Matches.mul rfl p₁.matches p₂.matches
  | star_nil => Matches.star_nil
  | star_cons p ps => Matches.stars rfl p.matches ps.matches

theorem Matches.exists_parse {r : Regex α} {s : List α} :
  r.Matches s → ∃ p : Parse r, p.flat = s := by
  intro h
  induction h with
  | epsilon => exact ⟨Parse.empty, rfl⟩
  | char => exact ⟨Parse.char _, rfl⟩
  | left h ih =>
    rcases ih with ⟨p, hp⟩
    exact ⟨p.left, hp⟩
  | right h ih =>
    rcases ih with ⟨p, hp⟩
    exact ⟨p.right, hp⟩
  | mul hs h₁ h₂ ih₁ ih₂ =>
    subst hs
    rcases ih₁ with ⟨p₁, hp₁⟩
    rcases ih₂ with ⟨p₂, hp₂⟩
    exact ⟨p₁.seq p₂, congr_arg₂ (·++·) hp₁ hp₂⟩
  | star_nil => exact ⟨Parse.star_nil, rfl⟩
  | stars hs h₁ h₂ ih₁ ih₂ =>
    subst hs
    rcases ih₁ with ⟨p, hp⟩
    rcases ih₂ with ⟨ps, hps⟩
    exact ⟨p.star_cons ps, congr_arg₂ (·++·) hp hps⟩
