import RegexPosix.Value

open Value
open Regex

universe u

variable {α : Type u}

def Regex.mkeps : (r : Regex α) → r.nullable → (Σ' v : Value α, Inhab v r)
  | epsilon, _ => ⟨Value.empty, Inhab.empty⟩
  | plus r₁ r₂, hn =>
    if hn₁ : r₁.nullable
      then
        have ⟨v₁, h₁⟩ := mkeps r₁ hn₁
        ⟨Value.left v₁, Inhab.left h₁⟩
      else
        have hn₂ := (Bool.or_eq_true_iff.mp hn).resolve_left hn₁
        have ⟨v₂, h₂⟩ := mkeps r₂ hn₂
        ⟨Value.right v₂, Inhab.right h₂⟩
  | mul r₁ r₂, hn =>
    have ⟨v₁, h₁⟩ := mkeps r₁ (Bool.and_elim_left hn)
    have ⟨v₂, h₂⟩ := mkeps r₂ (Bool.and_elim_right hn)
    ⟨Value.seq v₁ v₂, Inhab.seq h₁ h₂⟩
  | star _, _ => ⟨Value.stars [], Inhab.star_nil⟩

theorem mkeps_flat {α : Type u} {r : Regex α} (hn : r.nullable) :
  (r.mkeps hn).fst.flat = [] := by
  induction r with
  | emptyset => simp at hn
  | epsilon =>
    simp only [mkeps, Value.flat]
  | char c => simp at hn
  | plus r₁ r₂ ih₁ ih₂ =>
    simp at hn
    simp [mkeps]
    split_ifs with hn'
    · rw [Value.flat, ih₁]
    · rw [Value.flat, ih₂]
  | mul r₁ r₂ ih₁ ih₂ =>
    simp at hn
    simp [mkeps]
    rw [ih₁, ih₂, and_self]
  | star r ih => simp [mkeps]

variable [DecidableEq α]

def inj : (r : Regex α) → (c : α) → (Σ' v : Value α, Inhab v (r.deriv c)) → (Σ' v : Value α, Inhab v r)
  | .char d, c, ⟨v, h⟩ => ⟨Value.char d, Inhab.char d⟩
  | .plus r₁ r₂, c, ⟨Value.left v₁, h₁⟩ =>
    have ⟨v₁, h₁⟩ := inj r₁ c ⟨v₁, inhab_left h₁⟩
    ⟨v₁.left, h₁.left⟩
  | .plus r₁ r₂, c, ⟨Value.right v₂, h₂⟩ =>
    have ⟨v₂, h₂⟩ := inj r₂ c ⟨v₂, inhab_right h₂⟩
    ⟨v₂.right, h₂.right⟩
  | .mul r₁ r₂, c, ⟨v, h⟩ => by
    rw [Regex.deriv] at h
    split_ifs at h with hn
    · match v with
      | Value.left (Value.seq v₁ v₂) =>
        have ⟨v₁, h₁⟩ := inj r₁ c ⟨v₁, inhab_seq_fst (inhab_left h)⟩
        exact ⟨v₁.seq v₂, h₁.seq (inhab_seq_snd (inhab_left h))⟩
      | Value.right v₂ =>
        have ⟨v₂, h₂⟩ := inj r₂ c ⟨v₂, inhab_right h⟩
        have ⟨v₁, h₁⟩ := r₁.mkeps hn
        exact ⟨v₁.seq v₂, h₁.seq h₂⟩
    · match v with
      | Value.seq v₁ v₂ =>
        have ⟨v₁, h₁⟩ := inj r₁ c ⟨v₁, inhab_seq_fst h⟩
        exact ⟨v₁.seq v₂, h₁.seq (inhab_seq_snd h)⟩
  | .star r, c, ⟨Value.seq v (Value.stars vs), h⟩ =>
    have ⟨v, hv⟩ := inj r c ⟨v, inhab_seq_fst h⟩
    ⟨Value.stars (v :: vs), Inhab.stars hv (inhab_seq_snd h)⟩

theorem inj_flat {r : Regex α} {c : α} {v : Value α} (hv : Inhab v (r.deriv c)) :
  (inj r c ⟨v, hv⟩).fst.flat = c::v.flat := by
  induction r generalizing v with
  | emptyset => nomatch hv
  | epsilon => nomatch hv
  | char d =>
    rw [deriv] at hv
    split_ifs at hv with hc
    · cases hv
      simp [inj, hc]
    · nomatch hv
  | plus r₁ r₂ ih₁ ih₂ =>
    cases hv with
    | left hv =>
      simp [inj, ih₁]
    | right hv =>
      simp [inj, ih₂]
  | mul r₁ r₂ ih₁ ih₂ =>
    rw [deriv] at hv
    split_ifs at hv with hn
    · match v with
      | Value.left (Value.seq v₁ v₂) =>
        simp [inj, hn, ih₁]
      | Value.right v₂ =>
        simp [inj, hn, ih₂]
        exact mkeps_flat _
    · match v with
      | Value.seq v₁ v₂ =>
        simp [inj, hn, ih₁]
  | star r ih =>
    match v with
    | Value.seq v (Value.stars vs) =>
      simp [inj, ih]

def injs : (r : Regex α) → (s : List α) → (Σ' v : Value α, Inhab v (r.derivs s)) → (Σ' v' : Value α, Inhab v' r)
  | _, [], h => h
  | r, c::s, h => inj r c (injs (r.deriv c) s h)

theorem injs_flat {r : Regex α} {s : List α} {v : Value α} (hv : Inhab v (r.derivs s)) :
  (injs r s ⟨v, hv⟩).fst.flat = s ++ v.flat := by
  induction s generalizing r with
  | nil => rfl
  | cons x xs ih =>
    simp [injs]
    rw [inj_flat, ih hv]

def Regex.parse : Regex α → List α → Option (Value α)
  | r, s =>
    let r' := r.derivs s
    if h : r'.nullable
      then some (injs r s (r'.mkeps h)).fst
      else none

theorem parse_flat {r : Regex α} {s : List α} {v : Value α} :
  r.parse s = some v → v.flat = s := by
  intro h
  simp [parse] at h
  rcases h with ⟨hn, h⟩
  rw [←h, injs_flat, mkeps_flat]
  exact List.append_nil s

theorem parse_matches_iff {r : Regex α} (s : List α) :
  (r.parse s).isSome ↔ r.Matches s := by
  induction s generalizing r with
  | nil =>
    rw [←nullable_iff_matches_nil]
    simp [parse]
  | cons x xs ih =>
    rw [Matches.deriv_iff, ←ih]
    simp [parse]
