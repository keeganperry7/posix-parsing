import PosixParsing.POSIX
import PosixParsing.Parser

open Regex
open Parse

universe u

variable {α : Type u}

theorem mkeps_posix {r : Regex α} {hn : r.nullable} :
  POSIX (mkeps hn) := by
  fun_induction mkeps with
  | case1 => exact POSIX.epsilon
  | case2 r₁ r₂ hn hn₁ ih₁ =>
    exact POSIX.left ih₁
  | case3 r₁ r₂ hn hn₁ hn₂ ih₂ =>
    refine POSIX.right ih₂ ?_
    rw [mkeps_flat]
    rw [←nullable_iff_matches_nil]
    exact hn₁
  | case4 r₁ r₂ hn hn₁ hn₂ ih₁ ih₂ =>
    exact POSIX.mul ih₁ ih₂ (by simp [mkeps_flat])
  | case5 r hn => exact POSIX.star_nil

variable [DecidableEq α]

theorem inj_posix {r : Regex α} {c : α} {p : Parse (r.deriv c)} (h : POSIX p) :
  POSIX (inj c p) := by
  fun_induction inj with
  | case1 d c p =>
    exact POSIX.char d
  | case2 r₁ r₂ c p ih₁ =>
    cases h with
    | left h =>
      exact POSIX.left (ih₁ h)
  | case3 r₁ r₂ c p ih₂ =>
    cases h with
    | right h hn =>
      refine POSIX.right (ih₂ h) ?_
      rw [inj_flat, Matches.deriv_iff]
      exact hn
  | case4 r₁ r₂ c hn₁ p₁ p₂ p heq ih₁ =>
    generalize_proofs k at heq
    generalize hr : (r₁.mul r₂).deriv c = r' at *
    subst k heq
    cases h with
    | left h =>
      cases h with
      | mul h₁ h₂ hs =>
        refine POSIX.mul (ih₁ h₁) h₂ ?_
        simp_rw [inj_flat, List.cons_append, Matches.deriv_iff]
        exact hs
  | case5 r₁ r₂ c hn₁ p₂ p heq ih₂ =>
    generalize_proofs k at heq
    generalize hr : (r₁.mul r₂).deriv c = r' at *
    subst k heq
    cases h with
    | right h hn =>
      refine POSIX.mul (mkeps_posix) (ih₂ h) ?_
      simp [inj_flat, mkeps_flat]
      intro x hx y hxy hr₁ hr₂
      rw [List.append_eq_cons_iff] at hxy
      simp [hx] at hxy
      rcases hxy with ⟨z, hx, hs⟩
      rw [hx, Matches.deriv_iff] at hr₁
      rw [hs] at hn
      exact absurd (Matches.mul rfl hr₁ hr₂) hn
  | case6 r₁ r₂ c hn₁ p₁ p₂ p heq ih₁ =>
    generalize_proofs k at heq
    generalize hr : (r₁.mul r₂).deriv c = r' at *
    simp [hn₁] at hr
    subst hr heq
    cases h with
    | mul h₁ h₂ hs =>
      refine POSIX.mul (ih₁ h₁) h₂ ?_
      simp_rw [inj_flat, List.cons_append, Matches.deriv_iff]
      exact hs
  | case7 r c p ps ih =>
    cases h with
    | mul h₁ h₂ hs =>
      refine POSIX.star_cons (ih h₁) h₂ (by simp [inj_flat]) ?_
      simp_rw [inj_flat, List.cons_append, Matches.deriv_iff]
      exact hs

theorem injs_posix {r : Regex α} {s : List α} {p : Parse (r.derivs s)} (h : POSIX p) :
  POSIX (injs s p) := by
  induction s generalizing r with
  | nil =>
    exact h
  | cons x xs ih =>
    rw [injs]
    exact inj_posix (ih h)

theorem matches_parse_posix_iff {r : Regex α} {s : List α} :
  r.Matches s ↔ ∃ p, r.parse s = some p ∧ POSIX p := by
  simp [parse]
  rw [Matches.derivs_iff, ←nullable_iff_matches_nil]
  constructor
  · intro h
    exact ⟨h, injs_posix mkeps_posix⟩
  · intro ⟨h, _⟩
    exact h

theorem parse_posix_iff (r : Regex α) (s : List α) (p : Parse r) :
  r.parse s = some p ↔ p.flat = s ∧ POSIX p := by
  constructor
  · intro h
    refine ⟨parse_flat h, ?_⟩
    simp [parse] at h
    rcases h with ⟨hn, h⟩
    rw [←h]
    exact injs_posix mkeps_posix
  · intro ⟨hv, h⟩
    subst hv
    rcases (matches_parse_posix_iff.mp h.matches) with ⟨v', h', h''⟩
    rw [POSIX.unique (parse_flat h') h'' h] at h'
    exact h'
