import RegexPosix.Value
import Mathlib.Tactic.GeneralizeProofs

open Parse
open Regex

universe u

variable {α : Type u}

def mkeps : {r : Regex α} → r.nullable → Parse r
  | epsilon, _ => empty
  | plus r₁ _, hn =>
    if hn₁ : r₁.nullable
      then left (mkeps hn₁)
      else
        have hn₂ := (Bool.or_eq_true_iff.mp hn).resolve_left hn₁
        right (mkeps hn₂)
  | mul _ _, hn =>
    have ⟨hn₁, hn₂⟩ := Bool.and_eq_true_iff.mp hn
    seq (mkeps hn₁) (mkeps hn₂)
  | star _, _ => star_nil

theorem mkeps_flat {r : Regex α} {hn : r.nullable} :
  (mkeps hn).flat = [] := by
  fun_induction mkeps with
  | case1 => rfl
  | case2 r₁ r₂ hn hn₁ ih₁ =>
    simp only [Parse.flat, ih₁]
  | case3 r₁ r₂ hn hn₁ hn₂ ih₂ =>
    simp only [Parse.flat, ih₂]
  | case4 r₁ r₂ hn hn₁ hn₂ ih₁ ih₂ =>
    simp [ih₁, ih₂]
  | case5 => rfl

variable [DecidableEq α]

def inj : {r : Regex α} → (c : α) → Parse (r.deriv c) → Parse r
  | .char d, _c, _ => char d
  | .plus r₁ r₂, c, left p => left (inj c p)
  | .plus r₁ r₂, c, right p => right (inj c p)
  | .mul r₁ _, c, p =>
    if hn₁ : r₁.nullable
      then
        match p.cast (deriv_mul_nullable hn₁) with
        | left (seq p₁ p₂) => seq (inj c p₁) p₂
        | right p₂ => seq (mkeps hn₁) (inj c p₂)
      else
        match p.cast (deriv_mul_not_nullable hn₁) with
        | seq p₁ p₂ => seq (inj c p₁) p₂
  | .star r, c, seq p ps => star_cons (inj c p) ps

theorem inj_flat {r : Regex α} {c : α} {p : Parse (r.deriv c)} :
  (inj c p).flat = c::p.flat := by
  fun_induction inj with
  | case1 d c p =>
    generalize hr : (Regex.char d).deriv c = r' at p
    rw [Regex.deriv] at hr
    split_ifs at hr with hc
    · subst hr hc
      cases p
      simp only [flat]
    · subst hr
      nomatch p
  | case2 r₁ r₂ c p ih =>
    simp only [flat, ih]
  | case3 r₁ r₂ c p ih =>
    simp only [flat, ih]
  | case4 r₁ r₂ c hn p₁ p₂ p heq ih₁ =>
    generalize_proofs k at heq
    generalize hr : (r₁.mul r₂).deriv c = r' at *
    simp [deriv, hn] at hr
    subst hr heq
    simp [ih₁]
  | case5 r₁ r₂ c hn p₂ p heq ih₂ =>
    generalize_proofs k at heq
    generalize hr : (r₁.mul r₂).deriv c = r' at *
    simp [deriv, hn] at hr
    subst hr heq
    simp [mkeps_flat, ih₂]
  | case6 r₁ r₂ c hn p₁ p₂ p heq ih₁ =>
    generalize_proofs k at heq
    generalize hr : (r₁.mul r₂).deriv c = r' at *
    simp [deriv, hn] at hr
    subst hr heq
    simp [ih₁]
  | case7 r c p ps ih =>
    simp [ih]

def injs : {r : Regex α} → (s : List α) → (Parse (r.derivs s)) → Parse r
  | _, [], p => p
  | _, c::s, p => inj c (injs s p)

theorem injs_flat {r : Regex α} {s : List α} {p : Parse (r.derivs s)} :
  (injs s p).flat = s ++ p.flat := by
  induction s generalizing r with
  | nil => rfl
  | cons x xs ih =>
    simp [injs]
    rw [inj_flat, ih]

def Regex.parse : (r : Regex α) → List α → Option (Parse r)
  | r, s =>
    let r' := r.derivs s
    if h : r'.nullable
      then some (injs s (mkeps h))
      else none

theorem parse_flat {r : Regex α} {s : List α} {p : Parse r} :
  r.parse s = some p → p.flat = s := by
  intro h
  simp [parse] at h
  rcases h with ⟨hn, h⟩
  rw [←h, injs_flat, mkeps_flat]
  exact List.append_nil s
