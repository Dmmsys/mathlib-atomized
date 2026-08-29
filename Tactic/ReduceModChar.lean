/-
Copyright (c) 2023 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public meta import Mathlib.Util.AtLocation
public import Mathlib.Data.ZMod.Basic -- shake: keep (Qq dependency)
public import Mathlib.RingTheory.Polynomial.Basic -- shake: keep (Qq dependency)
import all Mathlib.Tactic.NormNum.DivMod -- for accessing `evalIntMod.go`
public import Mathlib.Tactic.NormNum.PowMod
public import Mathlib.Tactic.ReduceModChar.Ext

/-!
# `reduce_mod_char` tactic

Define the `reduce_mod_char` tactic, which traverses expressions looking for numerals `n`,
such that the type of `n` is a ring of (positive) characteristic `p`, and reduces these
numerals modulo `p`, to lie between `0` and `p`.

## Implementation

The main entry point is `ReduceModChar.derive`, which uses `simp` to traverse expressions and
calls `matchAndNorm` on each subexpression.
The type of each subexpression is matched syntactically to determine if it is a ring with positive
characteristic in `typeToCharP`. Using syntactic matching should be faster than trying to infer
a `CharP` instance on each subexpression.
The actual reduction happens in `normIntNumeral`. This is written to be compatible with `norm_num`
so it can serve as a drop-in replacement for some `norm_num`-based routines (specifically, the
intended use is as an option for the `ring` tactic).

In addition to the main functionality, we call `normNeg` and `normNegCoeffMul` to replace negation
with multiplication by `p - 1`, and simp lemmas tagged `@[reduce_mod_char]` to clean up the
resulting expression: e.g. `1 * X + 0` becomes `X`.
-/

public meta section

open Lean Meta Simp
open Lean.Elab
open Tactic
open Qq

namespace Tactic

namespace ReduceModChar

open Mathlib.Meta.NormNum

variable {u : Level}

/--
lemma `CharP.isInt_of_mod` / 引理 `CharP.isInt_of_mod`

English:
lemma CharP.isInt_of_mod
  statement: {e' r : Int} {α : Type*} [Ring α] {n n' : Nat} (inst : CharP α n) {e : α}
  proof: ⟨by rw [he.out, CharP.intCast_eq_intCast_mod α n, show n = n' from hn.out, h₂.out, Int.cast_id]⟩

中文:
引理 特征p.is整数_of_mod
  结论: {e' r : 整数} {α : 类型} [环 α] {n n' : 自然数} (inst : 特征p α n) {e : α}
  证明: ⟨by rw [he.out, CharP.intCast_eq_intCast_mod α n, show n = n' from hn.out, h₂.out, Int.cast_id]⟩

Depends on / 依赖: CharP.intCast_eq_intCast_mod, Int.cast_id, cast_id, he.out, hn.out, intCast_eq_intCast_mod
-/
lemma CharP.isInt_of_mod {e' r : Int} {α : Type*} [Ring α] {n n' : Nat} (inst : CharP α n) {e : α}
    (he : IsInt e e') (hn : IsNat n n') (h₂ : IsInt (e' % n') r) : IsInt e r :=
  ⟨by rw [he.out, CharP.intCast_eq_intCast_mod α n, show n = n' from hn.out, h₂.out, Int.cast_id]⟩

/--
lemma `CharP.isNat_pow` / 引理 `CharP.isNat_pow`

English:
lemma CharP.isNat_pow
  given: {α} [Semiring α]
  statement: forall {f : α -> Nat -> α} {a : α} {a' b b' c n n' : Nat},

中文:
引理 特征p.is自然数_pow
  条件: {α} [半环 α]
  结论: 对任意 {f : α -> 自然数 -> α} {a : α} {a' b b' c n n' : 自然数},
-/
lemma CharP.isNat_pow {α} [Semiring α] : forall {f : α -> Nat -> α} {a : α} {a' b b' c n n' : Nat},
    CharP α n -> f = HPow.hPow -> IsNat a a' -> IsNat b b' -> IsNat n n' ->
    Nat.mod (Nat.pow a' b') n' = c -> IsNat (f a b) c
  | _, _, a, _, b, _, _, n, _, rfl, ⟨h⟩, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨by
    rw [h]; rw [Nat.cast_id]; rw [Nat.pow_eq]; rw [← Nat.cast_pow]; rw [CharP.natCast_eq_natCast_mod α n]
    rfl⟩

attribute [local instance] Mathlib.Meta.monadLiftOptionMetaM in
/--
Definition of `normBareNumeral` / `normBareNumeral` 的定义

English:
definition normBareNumeral
  signature: {α : Q(Type u)} (n n' : Q(Nat)) (pn : Q(IsNat «$n» «$n'»))
  body: do
  let ⟨ze, ne, pe⟩ ← Result.toInt _ (← Mathlib.Meta.NormNum.derive e)
let rr ← evalIntMod.go _ _ ze q(IsInt.raw_refl $ne) _
    .isNat q(instAddMonoidWithOne) _ q(isNat_natCast _ _ (IsNat.raw_refl $n'))
  let ⟨zr, nr, pr⟩ ← rr.toInt _
  return .isInt _ nr zr q(CharP.isInt_of_mod $instCharP $pe $pn $pr)

mutual

  /-- Given an expression of the form `a ^ b` in a ring of characteristic `n`, reduces `a`
  modulo `n` recursively and then calculates `a ^ b` using fast modular exponentiation. -/
  partial def normPow {α : Q(Type u)} (n n' : Q(Nat)) (pn : Q(IsNat «$n» «$n'»)) (e : Q($α))
      (_ : Q(Ring $α)) (instCharP : Q(CharP $α $n)) : MetaM (Result e) := do
    let .app (.app (f : Q($α -> Nat -> $α)) (a : Q($α))) (b : Q(Nat)) ← whnfR e | failure
    let .isNat sα na pa ← normIntNumeral' n n' pn a _ instCharP | failure
    let ⟨nb, pb⟩ ← Mathlib.Meta.NormNum.deriveNat b q(Nat.instAddMonoidWithOne)
guard ← withNewMCtxDepth isDefEq f q(HPow.hPow (α := $α))
haveI' : e =Q a ^ b := ⟨⟩
haveI' : f =Q HPow.hPow := ⟨⟩
    have ⟨c, r⟩ := evalNatPowMod na nb n'
    assumeInstancesCommute
    return .isNat sα c q(CharP.isNat_pow (f := $f) $instCharP (.refl $f) $pa $pb $pn $r)

  /-- If `e` is of the form `a ^ b`, reduce it using fast modular exponentiation, otherwise
  reduce it using `norm_num`. -/
  partial def normIntNumeral' {α : Q(Type u)} (n n' : Q(Nat)) (pn : Q(IsNat «$n» «$n'»))
      (e : Q($α)) (_ : Q(Ring $α)) (instCharP : Q(CharP $α $n)) : MetaM (Result e) :=
normPow n n' pn e _ instCharP > normBareNumeral n n' pn e _ instCharP

中文:
定义 normBareNumeral
  签名: {α : Q(类型u)} (n n' : Q(自然数)) (pn : Q(是自然数 «$n» «$n'»))
  定义体: do
  let ⟨ze, ne, pe⟩ ← Result.toInt _ (← Mathlib.Meta.NormNum.derive e)
let rr ← evalIntMod.go _ _ ze q(IsInt.raw_refl $ne) _
    .isNat q(instAddMonoidWithOne) _ q(isNat_natCast _ _ (IsNat.raw_refl $n'))
  let ⟨zr, nr, pr⟩ ← rr.toInt _
  return .isInt _ nr zr q(CharP.isInt_of_mod $instCharP $pe $pn $pr)

mutual

  /-- Given an expression of the form `a ^ b` in a ring of characteristic `n`, reduces `a`
  modulo `n` recursively and then calculates `a ^ b` using fast modular exponentiation. -/
  partial def normPow {α : Q(Type u)} (n n' : Q(Nat)) (pn : Q(IsNat «$n» «$n'»)) (e : Q($α))
      (_ : Q(Ring $α)) (instCharP : Q(CharP $α $n)) : MetaM (Result e) := do
    let .app (.app (f : Q($α -> Nat -> $α)) (a : Q($α))) (b : Q(Nat)) ← whnfR e | failure
    let .isNat sα na pa ← normIntNumeral' n n' pn a _ instCharP | failure
    let ⟨nb, pb⟩ ← Mathlib.Meta.NormNum.deriveNat b q(Nat.instAddMonoidWithOne)
guard ← withNewMCtxDepth isDefEq f q(HPow.hPow (α := $α))
haveI' : e =Q a ^ b := ⟨⟩
haveI' : f =Q HPow.hPow := ⟨⟩
    have ⟨c, r⟩ := evalNatPowMod na nb n'
    assumeInstancesCommute
    return .isNat sα c q(CharP.isNat_pow (f := $f) $instCharP (.refl $f) $pa $pb $pn $r)

  /-- If `e` is of the form `a ^ b`, reduce it using fast modular exponentiation, otherwise
  reduce it using `norm_num`. -/
  partial def normIntNumeral' {α : Q(Type u)} (n n' : Q(Nat)) (pn : Q(IsNat «$n» «$n'»))
      (e : Q($α)) (_ : Q(Ring $α)) (instCharP : Q(CharP $α $n)) : MetaM (Result e) :=
normPow n n' pn e _ instCharP > normBareNumeral n n' pn e _ instCharP
-/
def normBareNumeral {α : Q(Type u)} (n n' : Q(Nat)) (pn : Q(IsNat «$n» «$n'»))
    (e : Q($α)) (_ : Q(Ring $α)) (instCharP : Q(CharP $α $n)) : MetaM (Result e) := do
  let ⟨ze, ne, pe⟩ ← Result.toInt _ (← Mathlib.Meta.NormNum.derive e)
let rr ← evalIntMod.go _ _ ze q(IsInt.raw_refl $ne) _
    .isNat q(instAddMonoidWithOne) _ q(isNat_natCast _ _ (IsNat.raw_refl $n'))
  let ⟨zr, nr, pr⟩ ← rr.toInt _
  return .isInt _ nr zr q(CharP.isInt_of_mod $instCharP $pe $pn $pr)

mutual

  /-- Given an expression of the form `a ^ b` in a ring of characteristic `n`, reduces `a`
  modulo `n` recursively and then calculates `a ^ b` using fast modular exponentiation. -/
  partial def normPow {α : Q(Type u)} (n n' : Q(Nat)) (pn : Q(IsNat «$n» «$n'»)) (e : Q($α))
      (_ : Q(Ring $α)) (instCharP : Q(CharP $α $n)) : MetaM (Result e) := do
    let .app (.app (f : Q($α -> Nat -> $α)) (a : Q($α))) (b : Q(Nat)) ← whnfR e | failure
    let .isNat sα na pa ← normIntNumeral' n n' pn a _ instCharP | failure
    let ⟨nb, pb⟩ ← Mathlib.Meta.NormNum.deriveNat b q(Nat.instAddMonoidWithOne)
guard ← withNewMCtxDepth isDefEq f q(HPow.hPow (α := $α))
haveI' : e =Q a ^ b := ⟨⟩
haveI' : f =Q HPow.hPow := ⟨⟩
    have ⟨c, r⟩ := evalNatPowMod na nb n'
    assumeInstancesCommute
    return .isNat sα c q(CharP.isNat_pow (f := $f) $instCharP (.refl $f) $pa $pb $pn $r)

  /-- If `e` is of the form `a ^ b`, reduce it using fast modular exponentiation, otherwise
  reduce it using `norm_num`. -/
  partial def normIntNumeral' {α : Q(Type u)} (n n' : Q(Nat)) (pn : Q(IsNat «$n» «$n'»))
      (e : Q($α)) (_ : Q(Ring $α)) (instCharP : Q(CharP $α $n)) : MetaM (Result e) :=
normPow n n' pn e _ instCharP > normBareNumeral n n' pn e _ instCharP

end

/--
lemma `CharP.intCast_eq_mod` / 引理 `CharP.intCast_eq_mod`

English:
lemma CharP.intCast_eq_mod
  given: (R : Type _) [Ring R] (p : Nat) [CharP R p] (k : Int)
  proof: CharP.intCast_eq_intCast_mod R p

中文:
引理 特征p.intCast_eq_mod
  条件: (R : 类型 _) [环 R] (p : 自然数) [特征p R p] (k : 整数)
  证明: CharP.intCast_eq_intCast_mod R p

Depends on / 依赖: CharP.intCast_eq_intCast_mod, intCast_eq_intCast_mod
-/
lemma CharP.intCast_eq_mod (R : Type _) [Ring R] (p : Nat) [CharP R p] (k : Int) :
    (k : R) = (k % p : Int) :=
  CharP.intCast_eq_intCast_mod R p

/--
Definition of `normIntNumeral` / `normIntNumeral` 的定义

English:
definition normIntNumeral
  signature: {α : Q(Type u)} (n : Q(Nat)) (e : Q($α)) (_ : Q(Ring $α))
  body: do
  let ⟨n', pn⟩ ← deriveNat n q(Nat.instAddMonoidWithOne)
  normIntNumeral' n n' pn e _ instCharP

中文:
定义 norm整数Numeral
  签名: {α : Q(类型u)} (n : Q(自然数)) (e : Q($α)) (_ : Q(环 $α))
  定义体: do
  let ⟨n', pn⟩ ← deriveNat n q(Nat.instAddMonoidWithOne)
  normIntNumeral' n n' pn e _ instCharP
-/
partial def normIntNumeral {α : Q(Type u)} (n : Q(Nat)) (e : Q($α)) (_ : Q(Ring $α))
    (instCharP : Q(CharP $α $n)) : MetaM (Result e) := do
  let ⟨n', pn⟩ ← deriveNat n q(Nat.instAddMonoidWithOne)
  normIntNumeral' n n' pn e _ instCharP

/--
lemma `CharP.neg_eq_sub_one_mul` / 引理 `CharP.neg_eq_sub_one_mul`

English:
lemma CharP.neg_eq_sub_one_mul
  statement: {α : Type _} [Ring α] (n : Nat) (inst : CharP α n) (b : α)
  proof: by
  rw [← pa]; rw [← p.out]; rw [← neg_one_mul]
  simp

中文:
引理 特征p.neg_eq_sub_one_mul
  结论: {α : 类型 _} [环 α] (n : 自然数) (inst : 特征p α n) (b : α)
  证明: by
  rw [← pa]; rw [← p.out]; rw [← neg_one_mul]
  simp

Depends on / 依赖: neg_one_mul, p.out
-/
lemma CharP.neg_eq_sub_one_mul {α : Type _} [Ring α] (n : Nat) (inst : CharP α n) (b : α)
    (a : Nat) (a' : α) (p : IsNat (n - 1 : α) a) (pa : a = a') :
    -b = a' * b := by
  rw [← pa]; rw [← p.out]; rw [← neg_one_mul]
  simp

/-- Given an expression `(-e) : t` such that `t` is a ring of characteristic `n`,
simplify this to `(n - 1) * e`.

This should be called only when `normIntNumeral` fails, because `normIntNumeral` would otherwise
be more useful by evaluating `-e` mod `n` to an actual numeral.
-/
@[nolint unusedHavesSuffices] -- the `=Q` is necessary for type checking
/--
Definition of `normNeg` / `normNeg` 的定义

English:
definition normNeg
  signature: {α : Q(Type u)} (n : Q(Nat)) (e : Q($α)) (_instRing : Q(Ring $α))
  body: do
  let .app f (b : Q($α)) ← whnfR e | failure
guard ← withNewMCtxDepth isDefEq f q(Neg.neg (α := $α))
  let r ← (derive (α := α) q($n - 1))
  match r with
  | .isNat sα a p => do
have : instAddMonoidWithOne =Q sα := ⟨⟩
    let ⟨a', pa'⟩ ← mkOfNat α sα a
    let pf : Q(-$b = $a' * $b) := q(CharP.neg_eq_sub_one_mul $n $instCharP $b $a $a' $p $pa')
    return { expr := q($a' * $b), proof? := pf }
  | .isNegNat _ _ _ =>
    throwError "normNeg: nothing useful to do in negative characteristic"
  | _ => throwError "normNeg: evaluating `{n} - 1` should give an integer result"

中文:
定义 normNeg
  签名: {α : Q(类型u)} (n : Q(自然数)) (e : Q($α)) (_instRing : Q(环 $α))
  定义体: do
  let .app f (b : Q($α)) ← whnfR e | failure
guard ← withNewMCtxDepth isDefEq f q(Neg.neg (α := $α))
  let r ← (derive (α := α) q($n - 1))
  match r with
  | .isNat sα a p => do
have : instAddMonoidWithOne =Q sα := ⟨⟩
    let ⟨a', pa'⟩ ← mkOfNat α sα a
    let pf : Q(-$b = $a' * $b) := q(CharP.neg_eq_sub_one_mul $n $instCharP $b $a $a' $p $pa')
    return { expr := q($a' * $b), proof? := pf }
  | .isNegNat _ _ _ =>
    throwError "normNeg: nothing useful to do in negative characteristic"
  | _ => throwError "normNeg: evaluating `{n} - 1` should give an integer result"
-/
partial def normNeg {α : Q(Type u)} (n : Q(Nat)) (e : Q($α)) (_instRing : Q(Ring $α))
    (instCharP : Q(CharP $α $n)) :
    MetaM Simp.Result := do
  let .app f (b : Q($α)) ← whnfR e | failure
guard ← withNewMCtxDepth isDefEq f q(Neg.neg (α := $α))
  let r ← (derive (α := α) q($n - 1))
  match r with
  | .isNat sα a p => do
have : instAddMonoidWithOne =Q sα := ⟨⟩
    let ⟨a', pa'⟩ ← mkOfNat α sα a
    let pf : Q(-$b = $a' * $b) := q(CharP.neg_eq_sub_one_mul $n $instCharP $b $a $a' $p $pa')
    return { expr := q($a' * $b), proof? := pf }
  | .isNegNat _ _ _ =>
    throwError "normNeg: nothing useful to do in negative characteristic"
  | _ => throwError "normNeg: evaluating `{n} - 1` should give an integer result"

/--
lemma `CharP.neg_mul_eq_sub_one_mul` / 引理 `CharP.neg_mul_eq_sub_one_mul`

English:
lemma CharP.neg_mul_eq_sub_one_mul
  statement: {α : Type _} [Ring α] (n : Nat) (inst : CharP α n) (a b : α)
  proof: by
  rw [← pa]; rw [← p.out]; rw [← neg_one_mul]
  simp

中文:
引理 特征p.neg_mul_eq_sub_one_mul
  结论: {α : 类型 _} [环 α] (n : 自然数) (inst : 特征p α n) (a b : α)
  证明: by
  rw [← pa]; rw [← p.out]; rw [← neg_one_mul]
  simp

Depends on / 依赖: neg_one_mul, p.out
-/
lemma CharP.neg_mul_eq_sub_one_mul {α : Type _} [Ring α] (n : Nat) (inst : CharP α n) (a b : α)
    (na : Nat) (na' : α) (p : IsNat ((n - 1) * a : α) na) (pa : na = na') :
    -(a * b) = na' * b := by
  rw [← pa]; rw [← p.out]; rw [← neg_one_mul]
  simp

/-- Given an expression `-(a * b) : t` such that `t` is a ring of characteristic `n`,
and `a` is a numeral, simplify this to `((n - 1) * a) * b`. -/
@[nolint unusedHavesSuffices] -- the `=Q` is necessary for type checking
/--
Definition of `normNegCoeffMul` / `normNegCoeffMul` 的定义

English:
definition normNegCoeffMul
  signature: {α : Q(Type u)} (n : Q(Nat)) (e : Q($α)) (_instRing : Q(Ring $α))
  body: do
  let .app neg (.app (.app mul (a : Q($α))) (b : Q($α))) ← whnfR e | failure
guard ← withNewMCtxDepth isDefEq neg q(Neg.neg (α := $α))
guard ← withNewMCtxDepth isDefEq mul q(HMul.hMul (α := $α))
  let r ← (derive (α := α) q(($n - 1) * $a))
  match r with
  | .isNat sα na np => do
have : AddGroupWithOne.toAddMonoidWithOne =Q sα := ⟨⟩
    let ⟨na', npa'⟩ ← mkOfNat α sα na
    let pf : Q(-($a * $b) = $na' * $b) :=
      q(CharP.neg_mul_eq_sub_one_mul $n $instCharP $a $b $na $na' $np $npa')
    return { expr := q($na' * $b), proof? := pf }
  | .isNegNat _ _ _ =>
    throwError "normNegCoeffMul: nothing useful to do in negative characteristic"
  | _ => throwError "normNegCoeffMul: evaluating `{n} - 1` should give an integer result"

中文:
定义 normNegCoeffMul
  签名: {α : Q(类型u)} (n : Q(自然数)) (e : Q($α)) (_instRing : Q(环 $α))
  定义体: do
  let .app neg (.app (.app mul (a : Q($α))) (b : Q($α))) ← whnfR e | failure
guard ← withNewMCtxDepth isDefEq neg q(Neg.neg (α := $α))
guard ← withNewMCtxDepth isDefEq mul q(HMul.hMul (α := $α))
  let r ← (derive (α := α) q(($n - 1) * $a))
  match r with
  | .isNat sα na np => do
have : AddGroupWithOne.toAddMonoidWithOne =Q sα := ⟨⟩
    let ⟨na', npa'⟩ ← mkOfNat α sα na
    let pf : Q(-($a * $b) = $na' * $b) :=
      q(CharP.neg_mul_eq_sub_one_mul $n $instCharP $a $b $na $na' $np $npa')
    return { expr := q($na' * $b), proof? := pf }
  | .isNegNat _ _ _ =>
    throwError "normNegCoeffMul: nothing useful to do in negative characteristic"
  | _ => throwError "normNegCoeffMul: evaluating `{n} - 1` should give an integer result"
-/
partial def normNegCoeffMul {α : Q(Type u)} (n : Q(Nat)) (e : Q($α)) (_instRing : Q(Ring $α))
    (instCharP : Q(CharP $α $n)) :
    MetaM Simp.Result := do
  let .app neg (.app (.app mul (a : Q($α))) (b : Q($α))) ← whnfR e | failure
guard ← withNewMCtxDepth isDefEq neg q(Neg.neg (α := $α))
guard ← withNewMCtxDepth isDefEq mul q(HMul.hMul (α := $α))
  let r ← (derive (α := α) q(($n - 1) * $a))
  match r with
  | .isNat sα na np => do
have : AddGroupWithOne.toAddMonoidWithOne =Q sα := ⟨⟩
    let ⟨na', npa'⟩ ← mkOfNat α sα na
    let pf : Q(-($a * $b) = $na' * $b) :=
      q(CharP.neg_mul_eq_sub_one_mul $n $instCharP $a $b $na $na' $np $npa')
    return { expr := q($na' * $b), proof? := pf }
  | .isNegNat _ _ _ =>
    throwError "normNegCoeffMul: nothing useful to do in negative characteristic"
  | _ => throwError "normNegCoeffMul: evaluating `{n} - 1` should give an integer result"

/--
Inductive type `TypeToCharPResult` / 归纳类型 `TypeToCharPResult`

English:
inductive TypeToCharPResult
  parameters: (α : Q(Type u))
  constructors (2):
    - intLike: (n : Q(Nat)) (instRing : Q(Ring $α)) (instCharP : Q(CharP $α $n))
    - failure: 

中文:
归纳类型 TypeToCharPResult
  参数: (α : Q(类型u))
  构造子 (2 个):
    - intLike: (n : Q(自然数)) (instRing : Q(环 $α)) (instCharP : Q(特征p $α $n))
    - failure: 
-/
inductive TypeToCharPResult (α : Q(Type u))
  | intLike (n : Q(Nat)) (instRing : Q(Ring $α)) (instCharP : Q(CharP $α $n))
  | failure

instance {α : Q(Type u)} : Inhabited (TypeToCharPResult α) := ⟨.failure⟩

/--
Definition of `typeToCharP` / `typeToCharP` 的定义

English:
definition typeToCharP
  signature: (expensive := false) (t : Q(Type u))
  body: match Expr.getAppFnArgs t with
| (``ZMod, #[(n : Q(Nat))]) =>
  return .intLike n
    (q((ZMod.commRing _).toRing) : Q(Ring (ZMod $n)))
    (q(ZMod.charP _) : Q(CharP (ZMod $n) $n))
| (``Polynomial, #[(R : Q(Type u)), _]) => do match ← typeToCharP (expensive := expensive) R with
  | (.intLike n _ _) =>
    return .intLike n
      (q(Polynomial.ring) : Q(Ring (Polynomial $R)))
      (q(Polynomial.instCharP _) : Q(CharP (Polynomial $R) $n))
  | .failure => return .failure
| _ => if ! expensive then return .failure else do
  -- Fallback: run an expensive procedures to determine a characteristic,
  -- by looking for a `CharP` instance.
  withNewMCtxDepth do
    /- If we want to support semirings, here we could implement the `natLike` fallback. -/
    let .some instRing ← trySynthInstanceQ q(Ring $t) | return .failure

    let n ← mkFreshExprMVarQ q(Nat)
    let some instCharP ← findLocalDeclWithTypeQ? q(CharP $t $n) | return .failure

    return .intLike (← instantiateMVarsQ n) instRing instCharP

中文:
定义 typeToCharP
  签名: (expensive := false) (t : Q(类型u))
  定义体: match Expr.getAppFnArgs t with
| (``ZMod, #[(n : Q(Nat))]) =>
  return .intLike n
    (q((ZMod.commRing _).toRing) : Q(Ring (ZMod $n)))
    (q(ZMod.charP _) : Q(CharP (ZMod $n) $n))
| (``Polynomial, #[(R : Q(Type u)), _]) => do match ← typeToCharP (expensive := expensive) R with
  | (.intLike n _ _) =>
    return .intLike n
      (q(Polynomial.ring) : Q(Ring (Polynomial $R)))
      (q(Polynomial.instCharP _) : Q(CharP (Polynomial $R) $n))
  | .failure => return .failure
| _ => if ! expensive then return .failure else do
  -- Fallback: run an expensive procedures to determine a characteristic,
  -- by looking for a `CharP` instance.
  withNewMCtxDepth do
    /- If we want to support semirings, here we could implement the `natLike` fallback. -/
    let .some instRing ← trySynthInstanceQ q(Ring $t) | return .failure

    let n ← mkFreshExprMVarQ q(Nat)
    let some instCharP ← findLocalDeclWithTypeQ? q(CharP $t $n) | return .failure

    return .intLike (← instantiateMVarsQ n) instRing instCharP
-/
partial def typeToCharP (expensive := false) (t : Q(Type u)) : MetaM (TypeToCharPResult t) :=
match Expr.getAppFnArgs t with
| (``ZMod, #[(n : Q(Nat))]) =>
  return .intLike n
    (q((ZMod.commRing _).toRing) : Q(Ring (ZMod $n)))
    (q(ZMod.charP _) : Q(CharP (ZMod $n) $n))
| (``Polynomial, #[(R : Q(Type u)), _]) => do match ← typeToCharP (expensive := expensive) R with
  | (.intLike n _ _) =>
    return .intLike n
      (q(Polynomial.ring) : Q(Ring (Polynomial $R)))
      (q(Polynomial.instCharP _) : Q(CharP (Polynomial $R) $n))
  | .failure => return .failure
| _ => if ! expensive then return .failure else do
  -- Fallback: run an expensive procedures to determine a characteristic,
  -- by looking for a `CharP` instance.
  withNewMCtxDepth do
    /- If we want to support semirings, here we could implement the `natLike` fallback. -/
    let .some instRing ← trySynthInstanceQ q(Ring $t) | return .failure

    let n ← mkFreshExprMVarQ q(Nat)
    let some instCharP ← findLocalDeclWithTypeQ? q(CharP $t $n) | return .failure

    return .intLike (← instantiateMVarsQ n) instRing instCharP

/--
Definition of `matchAndNorm` / `matchAndNorm` 的定义

English:
definition matchAndNorm
  signature: (expensive := false) (e : Expr)
  body: do
  let α ← inferType e
  let u_succ : Level ← getLevel α
  let (.succ u) := u_succ | throwError "expected {α} to be a `Type _`, not `Sort {u_succ}`"
  have α : Q(Type u) := α
  match ← typeToCharP (expensive := expensive) α with
    | (.intLike n instRing instCharP) =>
      -- Handle the numeric expressions first, e.g. `-5` (which shouldn't become `-1 * 5`)
normIntNumeral n e instRing instCharP >>= Result.toSimpResult >
normNegCoeffMul n e instRing instCharP >-- `-(3 * X) → ((n - 1) * 3) * X`
      normNeg n e instRing instCharP -- `-X → (n - 1) * X`

    /- Here we could add a `natLike` result using only a `Semiring` instance.
    This would activate only the less-powerful procedures
    that cannot handle subtraction.
    -/

    | .failure =>
      throwError "inferred type `{α}` does not have a known characteristic"

中文:
定义 matchAndNorm
  签名: (expensive := false) (e : Expr)
  定义体: do
  let α ← inferType e
  let u_succ : Level ← getLevel α
  let (.succ u) := u_succ | throwError "expected {α} to be a `Type _`, not `Sort {u_succ}`"
  have α : Q(Type u) := α
  match ← typeToCharP (expensive := expensive) α with
    | (.intLike n instRing instCharP) =>
      -- Handle the numeric expressions first, e.g. `-5` (which shouldn't become `-1 * 5`)
normIntNumeral n e instRing instCharP >>= Result.toSimpResult >
normNegCoeffMul n e instRing instCharP >-- `-(3 * X) → ((n - 1) * 3) * X`
      normNeg n e instRing instCharP -- `-X → (n - 1) * X`

    /- Here we could add a `natLike` result using only a `Semiring` instance.
    This would activate only the less-powerful procedures
    that cannot handle subtraction.
    -/

    | .failure =>
      throwError "inferred type `{α}` does not have a known characteristic"
-/
partial def matchAndNorm (expensive := false) (e : Expr) : MetaM Simp.Result := do
  let α ← inferType e
  let u_succ : Level ← getLevel α
  let (.succ u) := u_succ | throwError "expected {α} to be a `Type _`, not `Sort {u_succ}`"
  have α : Q(Type u) := α
  match ← typeToCharP (expensive := expensive) α with
    | (.intLike n instRing instCharP) =>
      -- Handle the numeric expressions first, e.g. `-5` (which shouldn't become `-1 * 5`)
normIntNumeral n e instRing instCharP >>= Result.toSimpResult >
normNegCoeffMul n e instRing instCharP >-- `-(3 * X) → ((n - 1) * 3) * X`
      normNeg n e instRing instCharP -- `-X → (n - 1) * X`

    /- Here we could add a `natLike` result using only a `Semiring` instance.
    This would activate only the less-powerful procedures
    that cannot handle subtraction.
    -/

    | .failure =>
      throwError "inferred type `{α}` does not have a known characteristic"

-- We use a few `simp` lemmas to preprocess the expression and clean up subterms like `0 * X`.
attribute [reduce_mod_char] sub_eq_add_neg
attribute [reduce_mod_char] zero_add add_zero zero_mul mul_zero one_mul mul_one
attribute [reduce_mod_char] eq_self_iff_true -- For closing non-numeric goals, e.g. `X = X`

/--
Definition of `derive` / `derive` 的定义

English:
definition derive
  signature: (expensive := false) (e : Expr)
  body: do
  withTraceNode `Tactic.reduce_mod_char (fun _ => return m!"{e}") do
  let e ← instantiateMVars e

  let config : Simp.Config := {
    zeta := false
    beta := false
    eta := false
    proj := false
    iota := false
  }
  let congrTheorems ← Meta.getSimpCongrTheorems
  let ext? ← getSimpExtension? `reduce_mod_char
  let ext ← match ext? with
  | some ext => pure ext
  | none => throwError "internal error: reduce_mod_char not registered as simp extension"
  let ctx ← Simp.mkContext config (congrTheorems := congrTheorems)
    (simpTheorems := #[← ext.getTheorems])
  let discharge := Mathlib.Meta.NormNum.discharge
  let r : Simp.Result := {expr := e}
  let matchAndNorm : Simproc := fun e =>
      try return (Simp.Step.done (← matchAndNorm (expensive := expensive) e))
      catch _ => pure .continue
  let pre := Simp.preDefault #[] >> matchAndNorm
  let post := Simp.postDefault #[]
  let r ← r.mkEqTrans (← Simp.main r.expr ctx (methods := { pre, post, discharge? := discharge })).1

  return r

中文:
定义 derive
  签名: (expensive := false) (e : Expr)
  定义体: do
  withTraceNode `Tactic.reduce_mod_char (fun _ => return m!"{e}") do
  let e ← instantiateMVars e

  let config : Simp.Config := {
    zeta := false
    beta := false
    eta := false
    proj := false
    iota := false
  }
  let congrTheorems ← Meta.getSimpCongrTheorems
  let ext? ← getSimpExtension? `reduce_mod_char
  let ext ← match ext? with
  | some ext => pure ext
  | none => throwError "internal error: reduce_mod_char not registered as simp extension"
  let ctx ← Simp.mkContext config (congrTheorems := congrTheorems)
    (simpTheorems := #[← ext.getTheorems])
  let discharge := Mathlib.Meta.NormNum.discharge
  let r : Simp.Result := {expr := e}
  let matchAndNorm : Simproc := fun e =>
      try return (Simp.Step.done (← matchAndNorm (expensive := expensive) e))
      catch _ => pure .continue
  let pre := Simp.preDefault #[] >> matchAndNorm
  let post := Simp.postDefault #[]
  let r ← r.mkEqTrans (← Simp.main r.expr ctx (methods := { pre, post, discharge? := discharge })).1

  return r
-/
partial def derive (expensive := false) (e : Expr) : MetaM Simp.Result := do
  withTraceNode `Tactic.reduce_mod_char (fun _ => return m!"{e}") do
  let e ← instantiateMVars e

  let config : Simp.Config := {
    zeta := false
    beta := false
    eta := false
    proj := false
    iota := false
  }
  let congrTheorems ← Meta.getSimpCongrTheorems
  let ext? ← getSimpExtension? `reduce_mod_char
  let ext ← match ext? with
  | some ext => pure ext
  | none => throwError "internal error: reduce_mod_char not registered as simp extension"
  let ctx ← Simp.mkContext config (congrTheorems := congrTheorems)
    (simpTheorems := #[← ext.getTheorems])
  let discharge := Mathlib.Meta.NormNum.discharge
  let r : Simp.Result := {expr := e}
  let matchAndNorm : Simproc := fun e =>
      try return (Simp.Step.done (← matchAndNorm (expensive := expensive) e))
      catch _ => pure .continue
  let pre := Simp.preDefault #[] >> matchAndNorm
  let post := Simp.postDefault #[]
  let r ← r.mkEqTrans (← Simp.main r.expr ctx (methods := { pre, post, discharge? := discharge })).1

  return r

open Parser.Tactic

/--
The tactic `reduce_mod_char` looks for numeric expressions in characteristic `p`
and reduces these to lie between `0` and `p`.

For example:
```
example : (5 : ZMod 4) = 1 := by reduce_mod_char
example : (X ^ 2 - 3 * X + 4 : (ZMod 4)[X]) = X ^ 2 + X := by reduce_mod_char
```

It also handles negation, turning it into multiplication by `p - 1`,
and similarly subtraction.

This tactic uses the type of the subexpression to figure out if it is indeed of positive
characteristic, for improved performance compared to trying to synthesise a `CharP` instance.
The variant `reduce_mod_char!` also tries to use `CharP R n` hypotheses in the context.
(Limitations of the typeclass system mean the tactic can't search for a `CharP R n` instance if
`n` is not yet known; use `have : CharP R n := inferInstance; reduce_mod_char!` as a workaround.)
-/
syntax (name := reduce_mod_char) "reduce_mod_char" (location)? : tactic
@[tactic_alt reduce_mod_char]
syntax (name := reduce_mod_char!) "reduce_mod_char!" (location)? : tactic

open Mathlib.Tactic in
elab_rules : tactic
| `(tactic| reduce_mod_char $[$loc]?) => unsafe do
  let loc := expandOptLocation (Lean.mkOptionalNode loc)
  transformAtNondepPropLocation (derive (expensive := false) ·) "reduce_mod_char" loc
    (ifUnchanged := .silent)
| `(tactic| reduce_mod_char! $[$loc]?) => unsafe do
  let loc := expandOptLocation (Lean.mkOptionalNode loc)
  transformAtNondepPropLocation (derive (expensive := true) ·) "reduce_mod_char"
    loc (ifUnchanged := .silent)

end ReduceModChar

end Tactic
