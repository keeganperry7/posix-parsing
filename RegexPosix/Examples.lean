import RegexPosix.Parse

open Regex

/-- Implicit coercion to convert characters to regexes -/
instance : Coe Char (Regex Char) where
  coe := char

-- (a + aa)(ε + a)
def r₁ : Regex Char := (plus 'a' (mul 'a' 'a')).mul (plus epsilon 'a')
#eval r₁.parse "aa".toList

-- (a + aa)*
def r₂ : Regex Char := (plus 'a' (mul 'a' 'a')).star
#eval r₂.parse "aaa".toList

-- (a + b)*
def r₃ : Regex Char := (plus 'a' 'b').star
#eval r₃.parse "aaabbbabab".toList

-- ε*
def r₄ : Regex Char := epsilon.star
#eval r₄.parse []

-- (a*)*
def r₅ : Regex Char := star (star 'a')
#eval r₅.parse "aaa".toList

-- (a + ε + b)*b*
def r₆ : Regex Char := (plus 'a' (plus epsilon 'b')).star.mul (star 'b')
#eval r₆.parse "aaabbb".toList
