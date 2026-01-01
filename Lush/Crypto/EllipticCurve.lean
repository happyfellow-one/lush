import Lush.Crypto.BitOperations

namespace Lush.Crypto.EllipticCurve

abbrev fieldBase : Nat := 2^255 - 19
abbrev F := Fin fieldBase

@[simp] def q := 2^252 + 27742317777372353535851937790883648493
@[simp] def h := 8

def A : F := 486662

inductive E where
| infinity : E
| onCurve : (x y : F) → (y^2 = x^3 + A*x + x) → E
deriving DecidableEq, Repr

def eMulCurve
    (x₁ y₁ : F)
    (h₁ : y₁^2 = x₁^3 + A*x₁ + x₁)
    (x₂ y₂ : F)
    (h₂ : y₂^2 = x₂^3 + A*x₂ + x₂)
    : E :=
  if h1 : x₁ = x₂ ∧ y₁ = -y₂
  then .infinity
  else if h2 : x₁ = x₂ ∧ y₁ = y₂
  then
    let m := (3*x₁^2 + A + 1) / (2*y₁)
    let x₃ := m^2 - 2*x₁
    let y₃ := m*(x₃ - x₁) + y₁
    have h : y₃^2 = x₃^3 + A*x₃ + x₃ := by
      unfold x₃ y₃ m
      sorry
    .onCurve x₃ y₃ h
  else
    let m := (y₂ - y₁) / (x₂ - x₁)
    let x₃ := m^2 - x₁ - x₂
    let y₃ := m*(x₃ - x₁) + y₁
    .onCurve x₃ y₃ sorry

def eMul (a b : E) : E :=
  match a with
  | .infinity => b
  | .onCurve x y h =>
    match b with
    | .infinity => a
    | .onCurve x' y' h' => eMulCurve x y h x' y' h'

infix:65 " • " => eMul

example : E.infinity • E.infinity = E.infinity := by native_decide

end Lush.Crypto.EllipticCurve
