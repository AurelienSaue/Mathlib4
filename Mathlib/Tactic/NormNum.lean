/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Lean.Elab.Tactic.Basic
import Mathlib.Algebra.Ring.Basic
def Lean.Expr.pp : Expr → MetaM Format := PrettyPrinter.ppExpr Name.anonymous []

namespace Lean

/--
  Return true if `e` is one of the following
  - A nat literal (numeral)
  - `Nat.zero`
  - `Nat.succ x` where `isNumeral x`
  - `OfNat.ofNat _ x _` where `isNumeral x` -/
partial def Expr.numeral? (e : Expr) : Option Nat :=
  if let some n := e.natLit? then n
  else
    let f := e.getAppFn
    if !f.isConst then none
    else
      let fName := f.constName!
      if fName == ``Nat.succ && e.getAppNumArgs == 1 then (numeral? e.appArg!).map Nat.succ
      else if fName == ``OfNat.ofNat && e.getAppNumArgs == 3 then numeral? (e.getArg! 1)
      else if fName == ``Nat.zero && e.getAppNumArgs == 0 then some 0
      else none

namespace Meta

def mkOfNatLit (u : Level) (α sα n : Expr) : Expr :=
  let inst := mkApp3 (mkConst ``Numeric.OfNat [u]) α n sα
  mkApp3 (mkConst ``OfNat.ofNat [u]) α n inst

def ofInt (α : Expr) : ℤ → MetaM Expr
| Int.ofNat n   => do mkNumeral α n
| Int.negSucc n => do
  let e ← mkNumeral α n.succ
  return ← mkAppM ``Neg.neg #[e]

namespace NormNum

theorem ofNat_add {α} [Semiring α] : (a b : α) → (a' b' c : Nat) →
  a = OfNat.ofNat a' → b = OfNat.ofNat b' → a' + b' = c → a + b = OfNat.ofNat c
| _, _, _, _, _, rfl, rfl, rfl => (Semiring.ofNat_add _ _).symm

theorem ofNat_mul {α} [Semiring α] : (a b : α) → (a' b' c : Nat) →
  a = OfNat.ofNat a' → b = OfNat.ofNat b' → a' * b' = c → a * b = OfNat.ofNat c
| _, _, _, _, _, rfl, rfl, rfl => (Semiring.ofNat_mul _ _).symm

theorem ofNat_pow {α} [Semiring α] : (a : α) → (n a' c : Nat) →
  a = OfNat.ofNat a' → a'^n = c → a ^ n = OfNat.ofNat c
| _, _, _, _, rfl, rfl => (Semiring.ofNat_pow _ _).symm

theorem congrNeg {α} [Ring α] (a b : α) : a = b → -a = -b := congrArg (-·)

partial def eval : Expr → MetaM (Expr × Expr × ℤ)
| e => e.withApp fun f args => do
  if f.isConstOf ``HAdd.hAdd then
    evalB ``NormNum.ofNat_add (·+·) args
  else if f.isConstOf ``HMul.hMul then
    evalB ``NormNum.ofNat_mul (·*·) args
  else if f.isConstOf ``HPow.hPow then
    evalPow ``NormNum.ofNat_pow (·^·) args
  else if f.isConstOf ``Neg.neg then
    if let #[_, α, a] ← args then
      let (a', pa, n) ← eval a
      let e ← mkAppM ``Neg.neg #[a']
      pure (e, ← mkAppM ``congrNeg #[a,a',pa], -n)
    else throwError "bloub"
  else if f.isConstOf ``OfNat.ofNat then
    let #[α,ln,_] ← args | throwError "bloub"
    let some n ← ln.natLit? | throwError "bloub"
    if n = 0 then
      let Level.succ u _ ← getLevel α | throwError "bloub"
      let nα ← synthInstance (mkApp (mkConst ``Numeric [u]) α)
      let sα ← synthInstance (mkApp (mkConst ``Semiring [u]) α)
      let e ← mkOfNatLit u α nα (mkRawNatLit 0)
      let p ← mkEqSymm (mkApp2 (mkConst ``Semiring.ofNat_zero [u]) α sα)
      return (e,p,n)
    else if n = 1 then
      let Level.succ u _ ← getLevel α | throwError "bloub"
      let nα ← synthInstance (mkApp (mkConst ``Numeric [u]) α)
      let sα ← synthInstance (mkApp (mkConst ``Semiring [u]) α)
      let e ← mkOfNatLit u α nα (mkRawNatLit 1)
      let p ← mkEqSymm (mkApp2 (mkConst ``Semiring.ofNat_one [u]) α sα)
      return (e,p,n)
    else pure (e, ← mkEqRefl e, n)
  -- else if f.isNatLit then pure (e, ← mkEqRefl e)
  else throwError "bloub"
where
  evalB (name : Name) (f : Nat → Nat → Nat)
    (args : Array Expr) : MetaM (Expr × Expr × ℤ) := do
    if let #[_, _, α, _, a, b] ← args then
      let Level.succ u _ ← getLevel α | throwError "bloub"
      let nα ← synthInstance (mkApp (mkConst ``Numeric [u]) α)
      let sα ← synthInstance (mkApp (mkConst ``Semiring [u]) α)
      let (a', pa, na) ← eval a
      let (b', pb, nb) ← eval b
      let la := Expr.getRevArg! a' 1
      let some na ← la.natLit? | throwError "bloub"
      let lb := Expr.getRevArg! b' 1
      let some nb ← lb.natLit? | throwError "fail"
      let lc := mkRawNatLit (f na nb)
      let c := mkOfNatLit u α nα lc
      pure (c, mkApp10 (mkConst name [u]) α sα a b la lb lc pa pb (← mkEqRefl lc), )
    else throwError "fail"
  evalPow (name : Name) (f : Nat → Nat → Nat)
    (args : Array Expr) : MetaM (Expr × Expr × ℤ) := do
    if let #[_, _, α, _, a, n] ← args then
      let Level.succ u _ ← getLevel α | throwError "fail"
      let nα ← synthInstance (mkApp (mkConst ``Numeric [u]) α)
      let sα ← synthInstance (mkApp (mkConst ``Semiring [u]) α)
      let (a', pa) ← eval a
      let la := Expr.getRevArg! a' 1
      let some na ← la.natLit? | throwError "fail"
      let some nn ← n.numeral? | throwError "fail"
      let lc := mkRawNatLit (f na nn)
      let c := mkOfNatLit u α nα lc
      pure (c, mkApp8 (mkConst name [u]) α sα a n la lc pa (← mkEqRefl lc))
    else throwError "fail"

partial def restore (e : Expr) : MetaM (Expr × Expr) := do
  e.withApp fun f args => do
    if f.isConstOf ``OfNat.ofNat then
      let #[α,ln,_] ← args | throwError "fail"
      let some n ← ln.natLit? | throwError "fail"
      if n = 0 then
        let Level.succ u _ ← getLevel α | throwError "fail"
        let sα ← synthInstance (mkApp (mkConst ``Semiring [u]) α)
        let nα ← synthInstance (mkApp2 (mkConst ``OfNat [u]) α (mkRawNatLit 0))
        let e' ←  mkApp3 (mkConst ``OfNat.ofNat [u]) α (mkRawNatLit 0) nα
        let p' ← mkApp2 (mkConst ``Semiring.ofNat_zero [u]) α sα
        return (e',p')
      else if n = 1 then
        let Level.succ u _ ← getLevel α | throwError "fail"
        let sα ← synthInstance (mkApp (mkConst ``Semiring [u]) α)
        let nα ← synthInstance (mkApp2 (mkConst ``OfNat [u]) α (mkRawNatLit 1))
        let e' ←  mkApp3 (mkConst ``OfNat.ofNat [u]) α (mkRawNatLit 1) nα
        let p' ← mkApp2 (mkConst ``Semiring.ofNat_one [u]) α sα
        return (e',p')
      else (e, ← mkEqRefl e)
    else if f.isConstOf ``Neg.neg then
      if let #[_, α, a] ← args then
        let (a', pa) ← eval a
        let e' ← mkAppM ``Neg.neg #[a']
        pure (e', ← mkAppM ``congrNeg #[a,a',pa])
      else throwError "fail"
    else (e, ← mkEqRefl e)

partial def derive (e : Expr) : MetaM (Expr × Expr) := do
  println! "1 {← e.pp}"
  let (e', p) ← eval e
  println! "yay"
  let (e'', p') ← restore e'
  return (e'', ← mkEqTrans p p')

end NormNum
end Meta

syntax (name := Parser.Tactic.normNum) "normNum" : tactic

open Meta Elab Tactic


@[tactic normNum] def Tactic.evalNormNum : Tactic := fun stx =>
  liftMetaTactic fun g => do
    let some (α, lhs, rhs) ← matchEq? (← getMVarType g) | throwError "fail"
    let (lhs2, lp) ← NormNum.eval lhs
    let (rhs2, rp) ← NormNum.eval rhs
    unless ← isDefEq lhs2 rhs2 do throwError "fail"
    let p ← mkEqTrans lp (← mkEqSymm rp)
    assignExprMVar g p
    pure []

end Lean
-- set_option pp.all true
variable (α) [Ring α]
example : - (1 + 0 : α) = -(1:α ):= by normNum
example : (- 2 : α) = (-2*1:α ):= by normNum
example : (0 + (2 + 3) + 1 : α) = 6 := by normNum
example : (70 * (33 + 2) : α) = 2450 := by normNum
example : (8 + 2 ^ 2 * 3 : α) = 20 := by normNum
