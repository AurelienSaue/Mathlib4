/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Gcd
/-!
# Basics for the Rational Numbers

## Summary

We define a rational number `q` as a structure `{ num, denom, pos, cop }`, where
- `num` is the numerator of `q`,
- `denom` is the denominator of `q`,
- `pos` is a proof that `denom > 0`, and
- `cop` is a proof `num` and `denom` are coprime.

We then define the expected (discrete) field structure on `ℚ` and prove basic lemmas about it.
Moreoever, we provide the expected casts from `ℕ` and `ℤ` into `ℚ`, i.e. `(↑n : ℚ) = n / 1`.

## Main Definitions

- `rat` is the structure encoding `ℚ`.
- `rat.mk n d` constructs a rational number `q = n / d` from `n d : ℤ`.

## Notations

- `/.` is infix notation for `rat.mk`.

## Tags

rat, rationals, field, ℚ, numerator, denominator, num, denom
-/

/-- `rat`, or `ℚ`, is the type of rational numbers. It is defined
  as the set of pairs ⟨n, d⟩ of integers such that `d` is positive and `n` and
  `d` are coprime. This representation is preferred to the quotient
  because without periodic reduction, the numerator and denominator can grow
  exponentially (for example, adding 1/2 to itself repeatedly). -/
structure Rat := mk' ::
(num : ℤ)
(denom : ℕ)
(pos : 0 < denom)
(cop : num.nat_abs.coprime denom)
notation "ℚ" => Rat

namespace Rat

/-- String representation of a rational numbers, used in `Repr`, `toString`, and
`has_to_format` instances. -/
protected def toString : ℚ → String
| ⟨n, d, _, _⟩ => if d = 1 then toString n else toString n ++ "/" ++ toString d

instance : Repr ℚ where
  reprPrec n _ := Rat.toString n
instance : ToString ℚ where
  toString n := Rat.toString n


-- instance : encodable ℚ := encodable.of_equiv (Σ n : ℤ, {d : ℕ // 0 < d ∧ n.nat_abs.coprime d})
--   ⟨λ ⟨a, b, c, d⟩, ⟨a, b, c, d⟩, λ⟨a, b, c, d⟩, ⟨a, b, c, d⟩,
--    λ ⟨a, b, c, d⟩, rfl, λ⟨a, b, c, d⟩, rfl⟩

/-- Embed an integer as a rational number -/
def ofInt (n : ℤ) : ℚ :=
⟨n, 1, Nat.one_pos, Nat.coprime_one_right _⟩

instance (n : ℕ) : OfNat ℚ n := ⟨ofInt n⟩

open Int Nat in
theorem neg_div : ∀ {a b : ℤ}, -a / b = -(a / b)
| ofNat 0,   ofNat m         => show ofNat (0/m) = -(ofNat (0/m)) by simp
| ofNat (succ m),   ofNat n   => by rfl
| ofNat 0,   negSucc m         => show - ofNat (0/succ m) = - -(ofNat (0/succ m)) by simp
| ofNat (succ m),   negSucc n =>
  show ofNat (succ m / succ n) = -(-ofNat (succ m / succ n)) by simp [Int.neg_neg]
| negSucc m, ofNat n   => show ofNat (succ m /n) = -(-ofNat (succ m / n)) by simp [Int.neg_neg]
| negSucc m, negSucc n => by rfl

/-- Form the quotient `n / d` where `n:ℤ` and `d:ℕ+` (not necessarily coprime) -/
def mkPnat (n : ℤ) (d : ℕ) (dpos : 0 < d): ℚ :=
let n' := n.natAbs
let g := n'.gcd d
let num := n / g
let denom := d / g
let pos : 0 < denom := by
  apply (Nat.le_div_iff_mul_le (Nat.gcd_pos_of_pos_right _ dpos)).2
  simp [← Nat.one_succ_zero]
  exact Nat.le_of_dvd dpos (Nat.gcd_dvd_right _ _)
let cop : (n/g).nat_abs.coprime denom := by
  have h : Int.nat_abs (n / g) = n' / g := by
    cases Int.nat_abs_eq n with
    | inl e =>
      rw [e]
      rfl
    | inr e =>
      rw [e, neg_div, Int.nat_abs_neg]
      rfl
  rw [h]
  exact Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_right _ dpos)
return ⟨num, denom, pos, cop⟩

/-- Form the quotient `n / d` where `n:ℤ` and `d:ℕ`. In the case `d = 0`, we
  define `n / 0 = 0` by convention. -/
def mkNat (n : ℤ) (d : ℕ) : ℚ :=
if d0 : d = 0 then 0 else mkPnat n d $ Nat.pos_of_ne_zero d0

/-- Form the quotient `n / d` where `n d : ℤ`. -/
def mk : ℤ → ℤ → ℚ
| n, (d : ℕ) => mkNat n d
| n ,-[1+ d] => mkNat (-n) (d.succ)

local infix:70 " /. " => Rat.mk


theorem mkNat_eq (n d) : mkNat n d = n /. d := rfl

@[simp] theorem mk_zero (n) : n /. 0 = 0 := rfl

@[simp] theorem zero_mk_pnat (d : ℕ) (dpos : 0 < d) : mkPnat 0 d dpos = 0 :=
by
  simp [mkPnat]; simp [*]; rfl

@[simp] theorem zero_mk_nat (n) : mkNat 0 n = 0 :=
by
  by_cases n = 0
  simp [mkNat, h]
  simp [mkNat, h]

@[simp] theorem zero_mk (n) : 0 /. n = 0 :=
by
  cases n with
  | ofNat x =>
    simp [mk]
  | negSucc x =>
    simp [mk]
    cc
end Rat
