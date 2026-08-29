/-
Copyright (c) 2020 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/
module

public meta import Mathlib.Data.Tree.Basic
public import Mathlib.Algebra.Field.Basic
public meta import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Data.Tree.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Util.SynthesizeUsing

/-!
# A tactic for canceling numeric denominators

This file defines tactics that cancel numeric denominators from field Expressions.

As an example, we want to transform a comparison `5*(a/3 + b/4) < c/3` into the equivalent
`5*(4*a + 3*b) < 4*c`.

## Implementation notes

The tooling here was originally written for `linarith`, not intended as an interactive tactic.
The interactive version has been split off because it is sometimes convenient to use on its own.
There are likely some rough edges to it.

Improving this tactic would be a good project for someone interested in learning tactic programming.
-/

public meta section

open Lean Parser Tactic Mathlib Meta NormNum Qq

initialize registerTraceClass `CancelDenoms

namespace Mathlib.Tactic.CancelDenoms


/--
theorem `mul_subst` / 定理 `mul_subst`

English:
theorem mul_subst
  statement: {α} [CommRing α] {n1 n2 k e1 e2 t1 t2 : α}
  proof: by
  rw [← h3]; rw [mul_comm n1]; rw [mul_assoc n2]; rw [← mul_assoc n1]; rw [h1]; rw [← mul_assoc n2]; rw [mul_comm n2]; rw [mul_assoc]; rw [h2]

中文:
定理 mul_subst
  结论: {α} [CommRing α] {n1 n2 k e1 e2 t1 t2 : α}
  证明: by
  rw [← h3]; rw [mul_comm n1]; rw [mul_assoc n2]; rw [← mul_assoc n1]; rw [h1]; rw [← mul_assoc n2]; rw [mul_comm n2]; rw [mul_assoc]; rw [h2]

Depends on / 依赖: mul_assoc, mul_comm
-/
theorem mul_subst {α} [CommRing α] {n1 n2 k e1 e2 t1 t2 : α}
    (h1 : n1 * e1 = t1) (h2 : n2 * e2 = t2) (h3 : n1 * n2 = k) : k * (e1 * e2) = t1 * t2 := by
  rw [← h3]; rw [mul_comm n1]; rw [mul_assoc n2]; rw [← mul_assoc n1]; rw [h1]; rw [← mul_assoc n2]; rw [mul_comm n2]; rw [mul_assoc]; rw [h2]

/--
theorem `div_subst` / 定理 `div_subst`

English:
theorem div_subst
  statement: {α} [Field α] {n1 n2 k e1 e2 t1 : α}
  proof: by
  rw [← h3]; rw [mul_assoc]; rw [mul_div_left_comm]; rw [h2]; rw [← mul_assoc]; rw [h1]; rw [mul_comm]; rw [one_mul]

中文:
定理 div_subst
  结论: {α} [Field α] {n1 n2 k e1 e2 t1 : α}
  证明: by
  rw [← h3]; rw [mul_assoc]; rw [mul_div_left_comm]; rw [h2]; rw [← mul_assoc]; rw [h1]; rw [mul_comm]; rw [one_mul]

Depends on / 依赖: mul_assoc, mul_comm, mul_div_left_comm, one_mul
-/
theorem div_subst {α} [Field α] {n1 n2 k e1 e2 t1 : α}
    (h1 : n1 * e1 = t1) (h2 : n2 / e2 = 1) (h3 : n1 * n2 = k) : k * (e1 / e2) = t1 := by
  rw [← h3]; rw [mul_assoc]; rw [mul_div_left_comm]; rw [h2]; rw [← mul_assoc]; rw [h1]; rw [mul_comm]; rw [one_mul]

/--
theorem `cancel_factors_eq_div` / 定理 `cancel_factors_eq_div`

English:
theorem cancel_factors_eq_div
  statement: {α} [Field α] {n e e' : α}
  proof: eq_div_of_mul_eq h2 by rwa [mul_comm] at h

中文:
定理 cancel_factors_eq_div
  结论: {α} [Field α] {n e e' : α}
  证明: eq_div_of_mul_eq h2 by rwa [mul_comm] at h

Depends on / 依赖: eq_div_of_mul_eq, mul_comm
-/
theorem cancel_factors_eq_div {α} [Field α] {n e e' : α}
    (h : n * e = e') (h2 : n != 0) : e = e' / n :=
eq_div_of_mul_eq h2 by rwa [mul_comm] at h

/--
theorem `add_subst` / 定理 `add_subst`

English:
theorem add_subst
  given: {α} [Ring α] {n e1 e2 t1 t2 : α} (h1 : n * e1 = t1) (h2 : n * e2 = t2)
  proof: by simp [left_distrib, *]

中文:
定理 add_subst
  条件: {α} [Ring α] {n e1 e2 t1 t2 : α} (h1 : n * e1 = t1) (h2 : n * e2 = t2)
  证明: by simp [left_distrib, *]

Depends on / 依赖: left_distrib
-/
theorem add_subst {α} [Ring α] {n e1 e2 t1 t2 : α} (h1 : n * e1 = t1) (h2 : n * e2 = t2) :
    n * (e1 + e2) = t1 + t2 := by simp [left_distrib, *]

/--
theorem `sub_subst` / 定理 `sub_subst`

English:
theorem sub_subst
  given: {α} [Ring α] {n e1 e2 t1 t2 : α} (h1 : n * e1 = t1) (h2 : n * e2 = t2)
  proof: by simp [left_distrib, *, sub_eq_add_neg]

中文:
定理 sub_subst
  条件: {α} [Ring α] {n e1 e2 t1 t2 : α} (h1 : n * e1 = t1) (h2 : n * e2 = t2)
  证明: by simp [left_distrib, *, sub_eq_add_neg]

Depends on / 依赖: left_distrib, sub_eq_add_neg
-/
theorem sub_subst {α} [Ring α] {n e1 e2 t1 t2 : α} (h1 : n * e1 = t1) (h2 : n * e2 = t2) :
    n * (e1 - e2) = t1 - t2 := by simp [left_distrib, *, sub_eq_add_neg]

/--
theorem `neg_subst` / 定理 `neg_subst`

English:
theorem neg_subst
  given: {α} [Ring α] {n e t : α} (h1 : n * e = t)
  statement: n * -e = -t
  proof: by simp [*]

中文:
定理 neg_subst
  条件: {α} [Ring α] {n e t : α} (h1 : n * e = t)
  结论: n * -e = -t
  证明: by simp [*]
-/
theorem neg_subst {α} [Ring α] {n e t : α} (h1 : n * e = t) : n * -e = -t := by simp [*]

/--
theorem `pow_subst` / 定理 `pow_subst`

English:
theorem pow_subst
  statement: {α} [CommRing α] {n e1 t1 k l : α} {e2 : Nat}
  proof: by
  rw [← h2]; rw [← h1]; rw [mul_pow]; rw [mul_assoc]

中文:
定理 pow_subst
  结论: {α} [CommRing α] {n e1 t1 k l : α} {e2 : 自然数}
  证明: by
  rw [← h2]; rw [← h1]; rw [mul_pow]; rw [mul_assoc]

Depends on / 依赖: mul_assoc, mul_pow
-/
theorem pow_subst {α} [CommRing α] {n e1 t1 k l : α} {e2 : Nat}
    (h1 : n * e1 = t1) (h2 : l * n ^ e2 = k) : k * (e1 ^ e2) = l * t1 ^ e2 := by
  rw [← h2]; rw [← h1]; rw [mul_pow]; rw [mul_assoc]

/--
theorem `inv_subst` / 定理 `inv_subst`

English:
theorem inv_subst
  given: {α} [Field α] {n k e : α} (h2 : e != 0) (h3 : n * e = k)
  proof: by rw [← div_eq_mul_inv, ← h3, mul_div_cancel_right₀ _ h2]

中文:
定理 inv_subst
  条件: {α} [Field α] {n k e : α} (h2 : e != 0) (h3 : n * e = k)
  证明: by rw [← div_eq_mul_inv, ← h3, mul_div_cancel_right₀ _ h2]

Depends on / 依赖: div_eq_mul_inv
-/
theorem inv_subst {α} [Field α] {n k e : α} (h2 : e != 0) (h3 : n * e = k) :
    k * (e ⁻¹) = n := by rw [← div_eq_mul_inv, ← h3, mul_div_cancel_right₀ _ h2]

/--
theorem `cancel_factors_lt` / 定理 `cancel_factors_lt`

English:
theorem cancel_factors_lt
  statement: {α} [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  proof: by
  rw [mul_lt_mul_iff_right₀]; rw [← ha]; rw [← hb]; rw [← mul_assoc]; rw [← mul_assoc]; rw [mul_comm bd]; rw [mul_lt_mul_iff_right₀]
  · exact mul_pos had hbd
  · exact one_div_pos.2 hgcd

中文:
定理 cancel_factors_lt
  结论: {α} [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  证明: by
  rw [mul_lt_mul_iff_right₀]; rw [← ha]; rw [← hb]; rw [← mul_assoc]; rw [← mul_assoc]; rw [mul_comm bd]; rw [mul_lt_mul_iff_right₀]
  · exact mul_pos had hbd
  · exact one_div_pos.2 hgcd

Depends on / 依赖: mul_assoc, mul_comm, mul_pos, one_div_pos
-/
theorem cancel_factors_lt {α} [Field α] [LinearOrder α] [IsStrictOrderedRing α]
    {a b ad bd a' b' gcd : α}
    (ha : ad * a = a') (hb : bd * b = b') (had : 0 < ad) (hbd : 0 < bd) (hgcd : 0 < gcd) :
    (a < b) = (1 / gcd * (bd * a') < 1 / gcd * (ad * b')) := by
  rw [mul_lt_mul_iff_right₀]; rw [← ha]; rw [← hb]; rw [← mul_assoc]; rw [← mul_assoc]; rw [mul_comm bd]; rw [mul_lt_mul_iff_right₀]
  · exact mul_pos had hbd
  · exact one_div_pos.2 hgcd

/--
theorem `cancel_factors_le` / 定理 `cancel_factors_le`

English:
theorem cancel_factors_le
  statement: {α} [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  proof: by
  rw [mul_le_mul_iff_right₀]; rw [← ha]; rw [← hb]; rw [← mul_assoc]; rw [← mul_assoc]; rw [mul_comm bd]; rw [mul_le_mul_iff_right₀]
  · exact mul_pos had hbd
  · exact one_div_pos.2 hgcd

中文:
定理 cancel_factors_le
  结论: {α} [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  证明: by
  rw [mul_le_mul_iff_right₀]; rw [← ha]; rw [← hb]; rw [← mul_assoc]; rw [← mul_assoc]; rw [mul_comm bd]; rw [mul_le_mul_iff_right₀]
  · exact mul_pos had hbd
  · exact one_div_pos.2 hgcd

Depends on / 依赖: mul_assoc, mul_comm, mul_pos, one_div_pos
-/
theorem cancel_factors_le {α} [Field α] [LinearOrder α] [IsStrictOrderedRing α]
    {a b ad bd a' b' gcd : α}
    (ha : ad * a = a') (hb : bd * b = b') (had : 0 < ad) (hbd : 0 < bd) (hgcd : 0 < gcd) :
    (a <= b) = (1 / gcd * (bd * a') <= 1 / gcd * (ad * b')) := by
  rw [mul_le_mul_iff_right₀]; rw [← ha]; rw [← hb]; rw [← mul_assoc]; rw [← mul_assoc]; rw [mul_comm bd]; rw [mul_le_mul_iff_right₀]
  · exact mul_pos had hbd
  · exact one_div_pos.2 hgcd

/--
theorem `cancel_factors_eq` / 定理 `cancel_factors_eq`

English:
theorem cancel_factors_eq
  statement: {α} [Field α] {a b ad bd a' b' gcd : α} (ha : ad * a = a')
  proof: by
  grind

中文:
定理 cancel_factors_eq
  结论: {α} [Field α] {a b ad bd a' b' gcd : α} (ha : ad * a = a')
  证明: by
  grind
-/
theorem cancel_factors_eq {α} [Field α] {a b ad bd a' b' gcd : α} (ha : ad * a = a')
    (hb : bd * b = b') (had : ad != 0) (hbd : bd != 0) (hgcd : gcd != 0) :
    (a = b) = (1 / gcd * (bd * a') = 1 / gcd * (ad * b')) := by
  grind

/--
theorem `cancel_factors_ne` / 定理 `cancel_factors_ne`

English:
theorem cancel_factors_ne
  statement: {α} [Field α] {a b ad bd a' b' gcd : α} (ha : ad * a = a')
  proof: by
  rw [eq_iff_iff]; rw [not_iff_not]; rw [cancel_factors_eq ha hb had hbd hgcd]

中文:
定理 cancel_factors_ne
  结论: {α} [Field α] {a b ad bd a' b' gcd : α} (ha : ad * a = a')
  证明: by
  rw [eq_iff_iff]; rw [not_iff_not]; rw [cancel_factors_eq ha hb had hbd hgcd]

Depends on / 依赖: cancel_factors_eq, eq_iff_iff, not_iff_not
-/
theorem cancel_factors_ne {α} [Field α] {a b ad bd a' b' gcd : α} (ha : ad * a = a')
    (hb : bd * b = b') (had : ad != 0) (hbd : bd != 0) (hgcd : gcd != 0) :
    (a != b) = (1 / gcd * (bd * a') != 1 / gcd * (ad * b')) := by
  rw [eq_iff_iff]; rw [not_iff_not]; rw [cancel_factors_eq ha hb had hbd hgcd]

/-! ### Computing cancellation factors -/

/--
Definition of `findCancelFactor` / `findCancelFactor` 的定义

English:
definition findCancelFactor
  signature: (e : Expr)
  body: match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, e1, e2]) | (``HSub.hSub, #[_, _, _, _, e1, e2]) =>
    let (v1, t1) := findCancelFactor e1
    let (v2, t2) := findCancelFactor e2
    let lcm := v1.lcm v2
    (lcm, .node lcm t1 t2)
  | (``HMul.hMul, #[_, _, _, _, e1, e2]) =>
    let (v1, t1

中文:
定义 findCancelFactor
  签名: (e : Expr)
  定义体: match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, e1, e2]) | (``HSub.hSub, #[_, _, _, _, e1, e2]) =>
    let (v1, t1) := findCancelFactor e1
    let (v2, t2) := findCancelFactor e2
    let lcm := v1.lcm v2
    (lcm, .node lcm t1 t2)
  | (``HMul.hMul, #[_, _, _, _, e1, e2]) =>
    let (v1, t1
-/
partial def findCancelFactor (e : Expr) : Nat × BinaryTree Nat :=
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, e1, e2]) | (``HSub.hSub, #[_, _, _, _, e1, e2]) =>
    let (v1, t1) := findCancelFactor e1
    let (v2, t2) := findCancelFactor e2
    let lcm := v1.lcm v2
    (lcm, .node lcm t1 t2)
  | (``HMul.hMul, #[_, _, _, _, e1, e2]) =>
    let (v1, t1) := findCancelFactor e1
    let (v2, t2) := findCancelFactor e2
    let pd := v1 * v2
    (pd, .node pd t1 t2)
  | (``HDiv.hDiv, #[_, _, _, _, e1, e2]) =>
    -- If e2 is a rational, then it's a natural number due to the simp lemmas in `deriveThms`.
    match e2.nat? with
    | some q =>
      let (v1, t1) := findCancelFactor e1
      let n := v1 * q
      (n, .node n t1 <| .node q .nil .nil)
    | none => (1, .node 1 .nil .nil)
  | (``Neg.neg, #[_, _, e]) => findCancelFactor e
  | (``HPow.hPow, #[_, Nat, _, _, e1, e2]) =>
    match e2.nat? with
    | some k =>
      let (v1, t1) := findCancelFactor e1
      let n := v1 ^ k
      (n, .node n t1 <| .node k .nil .nil)
    | none => (1, .node 1 .nil .nil)
  | (``Inv.inv, #[_, _, e]) =>
    match e.nat? with
    | some q => (q, .node q .nil <| .node q .nil .nil)
    | none => (1, .node 1 .nil .nil)
  | _ => (1, .node 1 .nil .nil)

/--
Definition of `synthesizeUsingNormNum` / `synthesizeUsingNormNum` 的定义

English:
definition synthesizeUsingNormNum
  signature: (type : Q(Prop))
  body: do
  try
    synthesizeUsingTactic' type (← `(tactic| norm_num))
  catch e =>
    throwError "Could not prove {type} using norm_num. {e.toMessageData}"

中文:
定义 synthesizeUsingNormNum
  签名: (type : Q(命题))
  定义体: do
  try
    synthesizeUsingTactic' type (← `(tactic| norm_num))
  catch e =>
    throwError "Could not prove {type} using norm_num. {e.toMessageData}"
-/
private def synthesizeUsingNormNum (type : Q(Prop)) : MetaM Q($type) := do
  try
    synthesizeUsingTactic' type (← `(tactic| norm_num))
  catch e =>
    throwError "Could not prove {type} using norm_num. {e.toMessageData}"

/--
Definition of `CancelResult` / `CancelResult` 的定义

English:
structure CancelResult
  parameters: {u : Level} {α : Q(Type u)} (mα : Q(Mul $α)) (e : Q($α)) (v : Q($α))
  axioms and operations (2):
    - cancelled : Q($α)
    - pf : Q($v * $e = $cancelled)

中文:
结构 CancelResult
  参数: {u : Level} {α : Q(类型u)} (mα : Q(Mul $α)) (e : Q($α)) (v : Q($α))
  公理与运算 (2 个):
    - cancelled : Q($α)
    - pf : Q($v * $e = $cancelled)
-/
structure CancelResult {u : Level} {α : Q(Type u)} (mα : Q(Mul $α)) (e : Q($α)) (v : Q($α)) where
  /-- An expression with denominators cancelled. -/
  cancelled : Q($α)
  /-- The proof that `cancelled` is valid. -/
  pf : Q($v * $e = $cancelled)

/--
Definition of `mkProdPrf` / `mkProdPrf` 的定义

English:
definition mkProdPrf
  signature: {u : Level} (α : Q(Type u)) (sα : Q(Field $α)) (v : Nat) (v' : Q($α))
  body: do
  let amwo : Q(AddMonoidWithOne $α) := q(inferInstance)
  trace[CancelDenoms] "mkProdPrf {e} {v}"
  match t, e with
  | .node _ lhs rhs, ~q($e1 + $e2) => do
    let ⟨v1, hv1⟩ ← mkProdPrf α sα v v' lhs e1
    let ⟨v2, hv2⟩ ← mkProdPrf α sα v v' rhs e2
    return ⟨q($v1 + $v2), q(CancelDenoms.add_s

中文:
定义 mkProdPrf
  签名: {u : Level} (α : Q(类型u)) (sα : Q(Field $α)) (v : 自然数) (v' : Q($α))
  定义体: do
  let amwo : Q(AddMonoidWithOne $α) := q(inferInstance)
  trace[CancelDenoms] "mkProdPrf {e} {v}"
  match t, e with
  | .node _ lhs rhs, ~q($e1 + $e2) => do
    let ⟨v1, hv1⟩ ← mkProdPrf α sα v v' lhs e1
    let ⟨v2, hv2⟩ ← mkProdPrf α sα v v' rhs e2
    return ⟨q($v1 + $v2), q(CancelDenoms.add_s
-/
partial def mkProdPrf {u : Level} (α : Q(Type u)) (sα : Q(Field $α)) (v : Nat) (v' : Q($α))
    (t : BinaryTree Nat) (e : Q($α)) : MetaM (CancelResult q(inferInstance) e v') := do
  let amwo : Q(AddMonoidWithOne $α) := q(inferInstance)
  trace[CancelDenoms] "mkProdPrf {e} {v}"
  match t, e with
  | .node _ lhs rhs, ~q($e1 + $e2) => do
    let ⟨v1, hv1⟩ ← mkProdPrf α sα v v' lhs e1
    let ⟨v2, hv2⟩ ← mkProdPrf α sα v v' rhs e2
    return ⟨q($v1 + $v2), q(CancelDenoms.add_subst $hv1 $hv2)⟩
  | .node _ lhs rhs, ~q($e1 - $e2) => do
    let ⟨v1, hv1⟩ ← mkProdPrf α sα v v' lhs e1
    let ⟨v2, hv2⟩ ← mkProdPrf α sα v v' rhs e2
    return ⟨q($v1 - $v2), q(CancelDenoms.sub_subst $hv1 $hv2)⟩
  | .node _ lhs@(.node ln _ _) rhs, ~q($e1 * $e2) => do
    trace[CancelDenoms] "recursing into mul"
    have ln' := (← mkOfNat α amwo <| mkRawNatLit ln).1
    have vln' := (← mkOfNat α amwo <| mkRawNatLit (v/ln)).1
    let ⟨v1, hv1⟩ ← mkProdPrf α sα ln ln' lhs e1
    let ⟨v2, hv2⟩ ← mkProdPrf α sα (v / ln) vln' rhs e2
    let npf ← synthesizeUsingNormNum q($ln' * $vln' = $v')
    return ⟨q($v1 * $v2), q(CancelDenoms.mul_subst $hv1 $hv2 $npf)⟩
  | .node _ lhs (.node rn _ _), ~q($e1 / $e2) => do
    -- Invariant: e2 is equal to the natural number rn
    have rn' := (← mkOfNat α amwo <| mkRawNatLit rn).1
    have vrn' := (← mkOfNat α amwo <| mkRawNatLit <| v / rn).1
    let ⟨v1, hv1⟩ ← mkProdPrf α sα (v / rn) vrn' lhs e1
    let npf ← synthesizeUsingNormNum q($rn' / $e2 = 1)
    let npf2 ← synthesizeUsingNormNum q($vrn' * $rn' = $v')
    return ⟨q($v1), q(CancelDenoms.div_subst $hv1 $npf $npf2)⟩
  | t, ~q(-$e) => do
    let ⟨v, hv⟩ ← mkProdPrf α sα v v' t e
    return ⟨q(-$v), q(CancelDenoms.neg_subst $hv)⟩
  | .node _ lhs@(.node k1 _ _) (.node k2 .nil .nil), ~q($e1 ^ $e2) => do
    have k1' := (← mkOfNat α amwo <| mkRawNatLit k1).1
    let ⟨v1, hv1⟩ ← mkProdPrf α sα k1 k1' lhs e1
    have l : Nat := v / (k1 ^ k2)
    have l' := (← mkOfNat α amwo <| mkRawNatLit l).1
    let npf ← synthesizeUsingNormNum q($l' * $k1' ^ $e2 = $v')
    return ⟨q($l' * $v1 ^ $e2), q(CancelDenoms.pow_subst $hv1 $npf)⟩
  | .node _ .nil (.node rn _ _), ~q($ei ⁻¹) => do
    have rn' := (← mkOfNat α amwo <| mkRawNatLit rn).1
    have vrn' := (← mkOfNat α amwo <| mkRawNatLit <| v / rn).1
have _ : rn' =Q ei := ⟨⟩
    let npf ← synthesizeUsingNormNum q($rn' != 0)
    let npf2 ← synthesizeUsingNormNum q($vrn' * $rn' = $v')
    return ⟨q($vrn'), q(CancelDenoms.inv_subst $npf $npf2)⟩
  | _, _ => do
    return ⟨q($v' * $e), q(rfl)⟩

/--
Definition of `deriveThms` / `deriveThms` 的定义

English:
definition deriveThms
  signature: : List Name
  body: [``div_div_eq_mul_div, ``div_neg]

中文:
定义 deriveThms
  签名: : List Name
  定义体: [``div_div_eq_mul_div, ``div_neg]

Depends on / 依赖: div_div_eq_mul_div, div_neg
-/
def deriveThms : List Name :=
  [``div_div_eq_mul_div, ``div_neg]

/--
theorem `derive_trans` / 定理 `derive_trans`

English:
theorem derive_trans
  given: {α} [Mul α] {a b c d : α} (h : a = b) (h' : c * b = d)
  statement: c * a = d
  proof: h ▸ h'

中文:
定理 derive_trans
  条件: {α} [Mul α] {a b c d : α} (h : a = b) (h' : c * b = d)
  结论: c * a = d
  证明: h ▸ h'
-/
theorem derive_trans {α} [Mul α] {a b c d : α} (h : a = b) (h' : c * b = d) : c * a = d := h ▸ h'

/--
theorem `derive_trans₂` / 定理 `derive_trans₂`

English:
theorem derive_trans₂
  given: {α} [Mul α] {a b c d e : α} (h : a = b) (h' : b = c) (h'' : d * c = e)
  proof: h ▸ h' ▸ h''

中文:
定理 derive_trans₂
  条件: {α} [Mul α] {a b c d e : α} (h : a = b) (h' : b = c) (h'' : d * c = e)
  证明: h ▸ h' ▸ h''
-/
theorem derive_trans₂ {α} [Mul α] {a b c d e : α} (h : a = b) (h' : b = c) (h'' : d * c = e) :
    d * a = e := h ▸ h' ▸ h''

/--
Definition of `derive` / `derive` 的定义

English:
definition derive
  signature: (e : Expr)
  body: do
  trace[CancelDenoms] "e = {e}"
  let eSimp ← simpOnlyNames (config := Simp.neutralConfig) deriveThms e
  trace[CancelDenoms] "e simplified = {eSimp.expr}"
  let eSimpNormNum ← Mathlib.Meta.NormNum.deriveSimp (← Simp.mkContext) false eSimp.expr
  trace[CancelDenoms] "e norm_num'd = {eSimpNormNum.

中文:
定义 derive
  签名: (e : Expr)
  定义体: do
  trace[CancelDenoms] "e = {e}"
  let eSimp ← simpOnlyNames (config := Simp.neutralConfig) deriveThms e
  trace[CancelDenoms] "e simplified = {eSimp.expr}"
  let eSimpNormNum ← Mathlib.Meta.NormNum.deriveSimp (← Simp.mkContext) false eSimp.expr
  trace[CancelDenoms] "e norm_num'd = {eSimpNormNum.
-/
def derive (e : Expr) : MetaM (Nat × Expr) := do
  trace[CancelDenoms] "e = {e}"
  let eSimp ← simpOnlyNames (config := Simp.neutralConfig) deriveThms e
  trace[CancelDenoms] "e simplified = {eSimp.expr}"
  let eSimpNormNum ← Mathlib.Meta.NormNum.deriveSimp (← Simp.mkContext) false eSimp.expr
  trace[CancelDenoms] "e norm_num'd = {eSimpNormNum.expr}"
  let (n, t) := findCancelFactor eSimpNormNum.expr
  let ⟨u, tp, e⟩ ← inferTypeQ' eSimpNormNum.expr
  let stp : Q(Field $tp) ← synthInstanceQ q(Field $tp)
  try
    have n' := (← mkOfNat tp q(inferInstance) <| mkRawNatLit <| n).1
    let r ← mkProdPrf tp stp n n' t e
    trace[CancelDenoms] "pf : {← inferType r.pf}"
    let pf' ←
      match eSimp.proof?, eSimpNormNum.proof? with
      | some pfSimp, some pfSimp' => mkAppM ``derive_trans₂ #[pfSimp, pfSimp', r.pf]
      | some pfSimp, none | none, some pfSimp => mkAppM ``derive_trans #[pfSimp, r.pf]
      | none, none => pure r.pf
    return (n, pf')
  catch E => do
    throwError "CancelDenoms.derive failed to normalize {e}.\n{E.toMessageData}"

/--
Definition of `findCompLemma` / `findCompLemma` 的定义

English:
definition findCompLemma
  signature: (e : Expr)
  body: do
  match (← whnfR e).getAppFnArgs with
  | (``LT.lt, #[_, _, a, b]) => return (a, b, ``cancel_factors_lt, true)
  | (``LE.le, #[_, _, a, b]) => return (a, b, ``cancel_factors_le, true)
  | (``Eq, #[_, a, b]) => return (a, b, ``cancel_factors_eq, false)
  -- `a ≠ b` reduces to `¬ a = b` under `whnf

中文:
定义 findCompLemma
  签名: (e : Expr)
  定义体: do
  match (← whnfR e).getAppFnArgs with
  | (``LT.lt, #[_, _, a, b]) => return (a, b, ``cancel_factors_lt, true)
  | (``LE.le, #[_, _, a, b]) => return (a, b, ``cancel_factors_le, true)
  | (``Eq, #[_, a, b]) => return (a, b, ``cancel_factors_eq, false)
  -- `a ≠ b` reduces to `¬ a = b` under `whnf
-/
def findCompLemma (e : Expr) : MetaM (Option (Expr × Expr × Name × Bool)) := do
  match (← whnfR e).getAppFnArgs with
  | (``LT.lt, #[_, _, a, b]) => return (a, b, ``cancel_factors_lt, true)
  | (``LE.le, #[_, _, a, b]) => return (a, b, ``cancel_factors_le, true)
  | (``Eq, #[_, a, b]) => return (a, b, ``cancel_factors_eq, false)
  -- `a ≠ b` reduces to `¬ a = b` under `whnf`
  | (``Not, #[p]) => match (← whnfR p).getAppFnArgs with
    | (``Eq, #[_, a, b]) => return (a, b, ``cancel_factors_ne, false)
    | _ => return none
  | (``GE.ge, #[_, _, a, b]) => return (b, a, ``cancel_factors_le, true)
  | (``GT.gt, #[_, _, a, b]) => return (b, a, ``cancel_factors_lt, true)
  | _ => return none

/--
Definition of `cancelDenominatorsInType` / `cancelDenominatorsInType` 的定义

English:
definition cancelDenominatorsInType
  signature: (h : Expr)
  body: do
  let some (lhs, rhs, lem, ord) ← findCompLemma h | throwError m!"cannot kill factors"
  let (al, lhs_p) ← derive lhs
  let ⟨u, α, _⟩ ← inferTypeQ' lhs
  let amwo ← synthInstanceQ q(AddMonoidWithOne $α)
  let (ar, rhs_p) ← derive rhs
  let gcd := al.gcd ar
  have al := (← mkOfNat α amwo <| mkRawN

中文:
定义 cancelDenominatorsInType
  签名: (h : Expr)
  定义体: do
  let some (lhs, rhs, lem, ord) ← findCompLemma h | throwError m!"cannot kill factors"
  let (al, lhs_p) ← derive lhs
  let ⟨u, α, _⟩ ← inferTypeQ' lhs
  let amwo ← synthInstanceQ q(AddMonoidWithOne $α)
  let (ar, rhs_p) ← derive rhs
  let gcd := al.gcd ar
  have al := (← mkOfNat α amwo <| mkRawN
-/
def cancelDenominatorsInType (h : Expr) : MetaM (Expr × Expr) := do
  let some (lhs, rhs, lem, ord) ← findCompLemma h | throwError m!"cannot kill factors"
  let (al, lhs_p) ← derive lhs
  let ⟨u, α, _⟩ ← inferTypeQ' lhs
  let amwo ← synthInstanceQ q(AddMonoidWithOne $α)
  let (ar, rhs_p) ← derive rhs
  let gcd := al.gcd ar
  have al := (← mkOfNat α amwo <| mkRawNatLit al).1
  have ar := (← mkOfNat α amwo <| mkRawNatLit ar).1
  have gcd := (← mkOfNat α amwo <| mkRawNatLit gcd).1
  let (al_cond, ar_cond, gcd_cond) ← if ord then do
      let _ ← synthInstanceQ q(Field $α)
      let _ ← synthInstanceQ q(LinearOrder $α)
      let _ ← synthInstanceQ q(IsStrictOrderedRing $α)
      let al_pos : Q(Prop) := q(0 < $al)
      let ar_pos : Q(Prop) := q(0 < $ar)
      let gcd_pos : Q(Prop) := q(0 < $gcd)
      pure (al_pos, ar_pos, gcd_pos)
    else do
      let _ ← synthInstanceQ q(Field $α)
      let al_ne : Q(Prop) := q($al != 0)
      let ar_ne : Q(Prop) := q($ar != 0)
      let gcd_ne : Q(Prop) := q($gcd != 0)
      pure (al_ne, ar_ne, gcd_ne)
  let al_cond ← synthesizeUsingNormNum al_cond
  let ar_cond ← synthesizeUsingNormNum ar_cond
  let gcd_cond ← synthesizeUsingNormNum gcd_cond
  let pf ← mkAppM lem #[lhs_p, rhs_p, al_cond, ar_cond, gcd_cond]
  let pf_tp ← inferType pf
  return ((← findCompLemma pf_tp).elim default (Prod.fst ∘ Prod.snd), pf)

end CancelDenoms

/--
`cancel_denoms` attempts to remove numerals from the denominators of fractions.
It works on propositions that are field-valued inequalities.

```lean
variable [LinearOrderedField α] (a b c : α)

example (h : a / 5 + b / 4 < c) : 4*a + 5*b < 20*c := by
  cancel_denoms at h
  exact h

example (h : a > 0) : a / 5 > 0 := by
  cancel_denoms
  exact h
```
-/
syntax (name := cancelDenoms) "cancel_denoms" (location)? : tactic

open Elab Tactic

/--
Definition of `cancelDenominatorsAt` / `cancelDenominatorsAt` 的定义

English:
definition cancelDenominatorsAt
  signature: (fvar : FVarId)
  body: do
  let t ← instantiateMVars (← fvar.getDecl).type
  let (new, eqPrf) ← CancelDenoms.cancelDenominatorsInType t
  liftMetaTactic' fun g => do
    let res ← g.replaceLocalDecl fvar new eqPrf
    return res.mvarId

中文:
定义 cancelDenominatorsAt
  签名: (fvar : FVarId)
  定义体: do
  let t ← instantiateMVars (← fvar.getDecl).type
  let (new, eqPrf) ← CancelDenoms.cancelDenominatorsInType t
  liftMetaTactic' fun g => do
    let res ← g.replaceLocalDecl fvar new eqPrf
    return res.mvarId
-/
private def cancelDenominatorsAt (fvar : FVarId) : TacticM Unit := do
  let t ← instantiateMVars (← fvar.getDecl).type
  let (new, eqPrf) ← CancelDenoms.cancelDenominatorsInType t
  liftMetaTactic' fun g => do
    let res ← g.replaceLocalDecl fvar new eqPrf
    return res.mvarId

/--
Definition of `cancelDenominatorsTarget` / `cancelDenominatorsTarget` 的定义

English:
definition cancelDenominatorsTarget
  signature: : TacticM Unit
  body: do
  let (new, eqPrf) ← CancelDenoms.cancelDenominatorsInType (← getMainTarget)
  liftMetaTactic' fun g => g.replaceTargetEq new eqPrf

中文:
定义 cancelDenominatorsTarget
  签名: : TacticM Unit
  定义体: do
  let (new, eqPrf) ← CancelDenoms.cancelDenominatorsInType (← getMainTarget)
  liftMetaTactic' fun g => g.replaceTargetEq new eqPrf
-/
private def cancelDenominatorsTarget : TacticM Unit := do
  let (new, eqPrf) ← CancelDenoms.cancelDenominatorsInType (← getMainTarget)
  liftMetaTactic' fun g => g.replaceTargetEq new eqPrf

/--
Definition of `cancelDenominators` / `cancelDenominators` 的定义

English:
definition cancelDenominators
  signature: (loc : Location)
  body: do
  withLocation loc cancelDenominatorsAt cancelDenominatorsTarget
    (fun _ => throwError "Failed to cancel any denominators")

@[tactic_alt cancelDenoms]

中文:
定义 cancelDenominators
  签名: (loc : Location)
  定义体: do
  withLocation loc cancelDenominatorsAt cancelDenominatorsTarget
    (fun _ => throwError "Failed to cancel any denominators")

@[tactic_alt cancelDenoms]
-/
private def cancelDenominators (loc : Location) : TacticM Unit := do
  withLocation loc cancelDenominatorsAt cancelDenominatorsTarget
    (fun _ => throwError "Failed to cancel any denominators")

@[tactic_alt cancelDenoms]
elab "cancel_denoms" loc?:(location)? : tactic => do
  cancelDenominators (expandOptLocation (Lean.mkOptionalNode loc?))
  Lean.Elab.Tactic.evalTactic (← `(tactic| try norm_num [← mul_assoc] $[$loc?]?))

end Mathlib.Tactic
