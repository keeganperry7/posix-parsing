import Mathlib.Computability.RegularExpressions
import RegexPosix.Value

universe u

open Value

namespace RegularExpression

variable {α : Type u}

@[simp]
def size : RegularExpression α → Nat
  | .zero => 1
  | .epsilon => 1
  | .char _ => 1
  | .plus r₁ r₂ => r₁.size + r₂.size + 1
  | .comp r₁ r₂ => r₁.size + r₂.size + 1
  | .star r => r.size + 1

variable [DecidableEq α]

def accept (r : RegularExpression α) (s : List α) (k : List α → (Σ' v : Value α, Inhab v r) → Option (Value α)) : Option (Value α) :=
  match r, s, k with
  | zero, _, _ => none
  | epsilon, cs, k => k cs ⟨Value.empty, Inhab.empty⟩
  | .char _, [], _ => none
  | .char c, c'::cs, k =>
    if c == c'
      then k cs ⟨Value.char c, Inhab.char c⟩
      else none
  | plus r₁ r₂, cs, k =>
    (accept r₁ cs (fun cs' v => k cs' ⟨Value.left v.fst, Inhab.left v.fst r₁ r₂ v.snd⟩)).or
    (accept r₂ cs (fun cs' v => k cs' ⟨Value.right v.fst, Inhab.right v.fst r₁ r₂ v.snd⟩))
  | comp r₁ r₂, cs, k =>
    accept r₁ cs (fun cs' v =>
      accept r₂ cs' (fun cs'' v' =>
        k cs'' ⟨Value.seq v.fst v'.fst, Inhab.seq v.fst v'.fst r₁ r₂ v.snd v'.snd⟩))
  | star r, cs, k =>
    (accept r cs (fun cs' v =>
      if cs'.length < cs.length then
        accept (star r) cs' (fun cs'' v' =>
          match v' with
          | ⟨Value.stars vs, hvs⟩ =>
            k cs'' ⟨Value.stars (v.fst::vs), Inhab.stars v.fst vs r v.snd hvs⟩)
      else k cs' ⟨Value.stars [v.fst], Inhab.stars v.fst [] r v.snd (Inhab.star_nil r)⟩
      )).or
    (k cs ⟨Value.stars [], Inhab.star_nil r⟩)
termination_by (r.size, s.length)

def greedy : RegularExpression α → List α → Option (Value α)
  | r, s => accept r s (fun cs v => match cs with | [] => v.fst | _ => none)

end RegularExpression
