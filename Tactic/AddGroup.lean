/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import Mathlib.Tactic.Group

/-!
# `add_group` tactic

Normalizes expressions in the language of additive groups. The basic idea is to use the simplifier
to put everything into a sum of integer scalar multiples (`zsmul` which takes an integer and an
additive group element), then simplify the scalars using the `ring_nf` tactic. The process needs
to be repeated since `ring_nf` can normalize a scalar to zero, leading to a summand that can be
removed before collecting scalars again. The simplifier step also uses some extra lemmas to avoid
some `ring_nf` invocations.

Note: Unlike the multiplicative `group` tactic which uses `← zpow_neg_one` to convert `a⁻¹` to
`a ^ (-1 : ℤ)`, the additive version cannot use `← neg_one_zsmul` to convert `-a` to
`(-1 : ℤ) • a` because `(-1 : ℤ)` is itself `-(1 : ℤ)`, causing simp to loop (since `ℤ` is also
an `AddGroup`). Instead, we handle negation via `neg_add_rev` to distribute negation over sums,
`zsmul_neg`/`neg_zsmul` for `n • (-a)`, and custom trick lemmas for combining `-b` with adjacent
`zsmul` terms. We also use `neg_one_zsmul` in the forward direction to normalize `(-1) • b`
to `-b`.

For the same reason (`ℤ` is itself an `AddGroup`), `sub_eq_add_neg` is applied once as a
preprocessing step rather than being part of the main simp set: inside the loop it would also
rewrite the subtractions that `ring_nf` reintroduces in `ℤ` scalars (e.g. `k - n` in
`(k - n) • a`), and the two would undo each other forever. That cycle is harmless in goal mode,
where `fail_if_no_progress` compares goal types, but rewriting a hypothesis allocates a fresh
`fvarId` each round, which counts as progress, so `add_group at h` would never terminate.
Preprocessing loses no proving power because nothing in the loop ever creates a new subtraction
of group elements.

Other than this issue, the strategy parallels Thomas Browning and Patrick Massot's `group`
tactic.

## TODO

- Surface non-progress-related errors from `repeat`.
- Allow `add_group`s `ifUnchanged` behavior to be configurable.

## Tags

group theory, additive group
-/

public meta section

namespace Mathlib.Tactic.AddGroup

open Lean Meta Parser Tactic

-- The next six lemmas are not general purpose lemmas; they are intended for use only by
-- the `add_group` tactic, and so are prefixed with `_` to keep them out of autocomplete.
-- They handle the case where a negated element `-b` appears adjacent to a `zsmul` of the same
-- element, or adjacent to another negated copy.
-- This means we also want to convert `(-1) • b` to `-b` in order to apply these lemmas.
/-
**Mathlib.Tactic.AddGroup._zsmul_neg_trick** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Ta
ctic.AddGroup`。
形式化陈述：_zsmul_neg_trick {G : Type*} [AddGroup G] (b : G) (n : Int) : n • b + (-b)
 = (n + (-1)) • b
参数：b : G；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_one_zsmul`：∀ {G : Type u_1} [inst : SubNegMonoid G] (x : G), -1 • x 
= -x
· 使用定理 `add_zsmul`：∀ {G : Type u_3} [inst : AddGroup G] (a : G) (m n : ℤ), (m + 
n) • a = m • a + n • a
-/
theorem _zsmul_neg_trick {G : Type*} [AddGroup G] (b : G) (n : ℤ) :
    n • b + (-b) = (n + (-1)) • b := by
  rw [← neg_one_zsmul b, ← add_zsmul]
/-
**Mathlib.Tactic.AddGroup._neg_zsmul_trick** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Ta
ctic.AddGroup`。
形式化陈述：_neg_zsmul_trick {G : Type*} [AddGroup G] (b : G) (n : Int) : (-b) + n • b
 = ((-1) + n) • b
参数：b : G；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_one_zsmul`：∀ {G : Type u_1} [inst : SubNegMonoid G] (x : G), -1 • x 
= -x
· 使用定理 `add_zsmul`：∀ {G : Type u_3} [inst : AddGroup G] (a : G) (m n : ℤ), (m + 
n) • a = m • a + n • a
-/
theorem _neg_zsmul_trick {G : Type*} [AddGroup G] (b : G) (n : ℤ) :
    (-b) + n • b = ((-1) + n) • b := by
  rw [← neg_one_zsmul b, ← add_zsmul]
/-
**Mathlib.Tactic.AddGroup._neg_neg_trick** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.Tact
ic.AddGroup`。
形式化陈述：_neg_neg_trick {G : Type*} [AddGroup G] (b : G) : (-b) + (-b) = (-2 : Int)
 • b
参数：b : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_one_zsmul`：∀ {G : Type u_1} [inst : SubNegMonoid G] (x : G), -1 • x 
= -x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_zsmul`：∀ {G : Type u_3} [inst : AddGroup G] (a : G) (m n : ℤ), (m + 
n) • a = m • a + n • a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Mathlib.Meta.NormNum.IsInt.neg_to_eq`：∀ {α : Type u_1} [inst : Ring α] {
n : ℕ} {a a' : α}, Mathlib.Meta.NormNum.IsInt a (Int.negOfNat n) → ↑n = a' → a =
 -a'
· 使用定理 `Mathlib.Meta.NormNum.isInt_add`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HAdd.hAdd →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `neg_zsmul`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a : α) (n : ℤ)
, -n • a = -(n • a)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
theorem _neg_neg_trick {G : Type*} [AddGroup G] (b : G) :
    (-b) + (-b) = (-2 : ℤ) • b := by
  have h : -b = (-1 : ℤ) • b := (neg_one_zsmul b).symm
  rw [h, ← add_zsmul]; norm_num
/-
**Mathlib.Tactic.AddGroup._add_zsmul_neg_trick** 是 Mathlib 中的一个定理，位于命名空间 `Mathli
b.Tactic.AddGroup`。
形式化陈述：_add_zsmul_neg_trick {G : Type*} [AddGroup G] (a b : G) (n : Int) : a + n 
• b + (-b) = a + (n + (-1)) • b
参数：a b : G；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `Mathlib.Tactic.AddGroup._zsmul_neg_trick`：_zsmul_neg_trick {G : Type*} [
AddGroup G] (b : G) (n : Int) : n • b + (-b) = (n + (-1)) • b
-/
theorem _add_zsmul_neg_trick {G : Type*} [AddGroup G] (a b : G) (n : ℤ) :
    a + n • b + (-b) = a + (n + (-1)) • b := by
  rw [add_assoc, _zsmul_neg_trick]
/-
**Mathlib.Tactic.AddGroup._add_neg_zsmul_trick** 是 Mathlib 中的一个定理，位于命名空间 `Mathli
b.Tactic.AddGroup`。
形式化陈述：_add_neg_zsmul_trick {G : Type*} [AddGroup G] (a b : G) (n : Int) : a + (-
b) + n • b = a + ((-1) + n) • b
参数：a b : G；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `Mathlib.Tactic.AddGroup._neg_zsmul_trick`：_neg_zsmul_trick {G : Type*} [
AddGroup G] (b : G) (n : Int) : (-b) + n • b = ((-1) + n) • b
-/
theorem _add_neg_zsmul_trick {G : Type*} [AddGroup G] (a b : G) (n : ℤ) :
    a + (-b) + n • b = a + ((-1) + n) • b := by
  rw [add_assoc, _neg_zsmul_trick]
/-
**Mathlib.Tactic.AddGroup._add_neg_neg_trick** 是 Mathlib 中的一个定理，位于命名空间 `Mathlib.
Tactic.AddGroup`。
形式化陈述：_add_neg_neg_trick {G : Type*} [AddGroup G] (a b : G) : a + (-b) + (-b) = 
a + (-2 : Int) • b
参数：a b : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `Mathlib.Tactic.AddGroup._neg_neg_trick`：_neg_neg_trick {G : Type*} [AddG
roup G] (b : G) : (-b) + (-b) = (-2 : Int) • b
-/
theorem _add_neg_neg_trick {G : Type*} [AddGroup G] (a b : G) :
    a + (-b) + (-b) = a + (-2 : ℤ) • b := by
  rw [add_assoc, _neg_neg_trick]

/--
`add_group` normalizes expressions in additive groups without assuming commutativity. Unlike
`abel`, which does take advantage of commutativity, `add_group` instead only uses the additive
group axioms without any information about which group is manipulated. If the goal is an equality,
and after normalization the two sides are equal, `add_group` closes the goal.

`add_group at l1 l2 ...` normalizes at the given locations.

For additive commutative groups, use the `abel` tactic instead.
For multiplicative groups, use the `group` tactic instead.

Example:
```lean
example {G : Type} [AddGroup G] (a b c d : G) (h : c = (a + 2 • b) + (-(b + b) + (-a)) + d) :
    a + c + (-d) = a := by
  add_group at h -- normalizes `h` which becomes `h : c = d`
  rw [h]         -- the goal is now `a + d + (-d) = a`
  add_group      -- which is then normalized and closed
```
-/
syntax (name := addGroup) "add_group" (location)? : tactic

macro_rules
| `(tactic| add_group $[$loc]?) =>
  `(tactic| first
    | fail_if_no_progress
        simp -decide -failIfUnchanged only [sub_eq_add_neg] $[$loc]?
        repeat fail_if_no_progress
          (simp -decide -failIfUnchanged only
            [addCommutatorElement_def, add_zero, zero_add,
              neg_add_rev, neg_zero, zsmul_neg, ← neg_zsmul,
              ← natCast_zsmul, ← mul_zsmul',
              Int.natCast_add, Int.natCast_mul, neg_neg,
              zsmul_zero, zero_zsmul, one_zsmul, neg_one_zsmul,
              ← add_assoc,
              ← add_zsmul, ← add_one_zsmul, ← one_add_zsmul,
              Mathlib.Tactic.Group._zsmul_trick,
              Mathlib.Tactic.Group._zsmul_trick_one,
              Mathlib.Tactic.Group._zsmul_trick_one',
              _zsmul_neg_trick, _neg_zsmul_trick, _neg_neg_trick,
              _add_zsmul_neg_trick, _add_neg_zsmul_trick, _add_neg_neg_trick,
              add_neg_cancel_right, neg_add_cancel_right,
              tsub_self, sub_self, add_neg_cancel, neg_add_cancel]
            $[$loc]?
          <;> ring_nf (ifUnchanged := .silent) $[$loc]?)
    | fail "`add_group` made no progress")

end Mathlib.Tactic.AddGroup

/-!
We register `add_group` with the `hint` tactic.
-/

register_hint 900 add_group

