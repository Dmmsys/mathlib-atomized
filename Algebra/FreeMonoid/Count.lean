/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.FreeMonoid.Basic
public import Mathlib.Algebra.Group.TypeTags.Basic

/-!
# `List.count` as a bundled homomorphism

In this file we define `FreeMonoid.countP`, `FreeMonoid.count`, `FreeAddMonoid.countP`, and
`FreeAddMonoid.count`. These are `List.countP` and `List.count` bundled as multiplicative and
additive homomorphisms from `FreeMonoid` and `FreeAddMonoid`.

We do not use `to_additive` too much because it can't map `Multiplicative ℕ` to `ℕ`.
-/

@[expose] public section

variable {α : Type*} (p : α -> Prop) [DecidablePred p]

namespace FreeMonoid
/-- `List.countP` lifted to free monoids -/
@[to_additive /-- `List.countP` lifted to free additive monoids -/]
/--
Definition of `countP'` / `countP'` 的定义

English:
definition countP'
  signature: (l : FreeMonoid α)
  body: l.toList.countP p

@[to_additive]

中文:
定义 countP'
  签名: (l : 自由幺半群 α)
  定义体: l.toList.countP p

@[to_additive]

Depends on / 依赖: countP, l.toList.countP, toList
-/
def countP' (l : FreeMonoid α) : Nat := l.toList.countP p

@[to_additive]
/--
lemma `countP'_one` / 引理 `countP'_one`

English:
lemma countP'_one
  statement: (1 : FreeMonoid α).countP' p = 0
  proof: rfl

@[to_additive]

中文:
引理 countP'_one
  结论: (1 : 自由幺半群 α).countP' p = 0
  证明: rfl

@[to_additive]

Depends on / 依赖: StrongNormalizedGCDMonoid, StrongNormalizedGCDMonoid.normalize_gcd, normalize_gcd
-/
lemma countP'_one : (1 : FreeMonoid α).countP' p = 0 := rfl

@[to_additive]
/--
lemma `countP'_mul` / 引理 `countP'_mul`

English:
lemma countP'_mul
  given: (l₁ l₂ : FreeMonoid α)
  statement: (l₁ * l₂).countP' p = l₁.countP' p + l₂.countP' p
  proof: by
  dsimp [countP']
  simp only [List.countP_append]

中文:
引理 countP'_mul
  条件: (l₁ l₂ : 自由幺半群 α)
  结论: (l₁ * l₂).countP' p = l₁.countP' p + l₂.countP' p
  证明: by
  dsimp [countP']
  simp only [List.countP_append]
-/
lemma countP'_mul (l₁ l₂ : FreeMonoid α) : (l₁ * l₂).countP' p = l₁.countP' p + l₂.countP' p := by
  dsimp [countP']
  simp only [List.countP_append]

/--
Definition of `countP` / `countP` 的定义

English:
definition countP
  signature: : FreeMonoid α ->* Multiplicative Nat where
  body: .ofAdd ∘ FreeMonoid.countP' p
  map_one' := by
    simp [countP'_one p]
  map_mul' x y := by
    simp [countP'_mul p]

中文:
定义 countP
  签名: : 自由幺半群 α ->* Multiplicative 自然数 where
  定义体: .ofAdd ∘ FreeMonoid.countP' p
  map_one' := by
    simp [countP'_one p]
  map_mul' x y := by
    simp [countP'_mul p]

Depends on / 依赖: FreeMonoid, FreeMonoid.countP, countP
-/
def countP : FreeMonoid α ->* Multiplicative Nat where
  toFun := .ofAdd ∘ FreeMonoid.countP' p
  map_one' := by
    simp [countP'_one p]
  map_mul' x y := by
    simp [countP'_mul p]

/--
theorem `countP_apply` / 定理 `countP_apply`

English:
theorem countP_apply
  given: (l : FreeMonoid α)
  statement: l.countP p = .ofAdd (l.toList.countP p)
  proof: rfl

中文:
定理 countP_apply
  条件: (l : 自由幺半群 α)
  结论: l.countP p = .ofAdd (l.toList.countP p)
  证明: rfl

Depends on / 依赖: GCDMonoid, IsGCDMonoid
-/
theorem countP_apply (l : FreeMonoid α) : l.countP p = .ofAdd (l.toList.countP p) := rfl

/--
lemma `countP_of` / 引理 `countP_of`

English:
lemma countP_of
  given: (x : α)
  statement: (of x).countP p =
  proof: by
  rw [countP_apply]; rw [toList_of]; rw [List.countP_singleton]; rw [apply_ite (Multiplicative.ofAdd)]
  simp only [decide_eq_true_eq]

中文:
引理 countP_of
  条件: (x : α)
  结论: (of x).countP p =
  证明: by
  rw [countP_apply]; rw [toList_of]; rw [List.countP_singleton]; rw [apply_ite (Multiplicative.ofAdd)]
  simp only [decide_eq_true_eq]

Depends on / 依赖: List.countP_singleton, Multiplicative, Multiplicative.ofAdd, apply_ite, countP_apply, countP_singleton, decide_eq_true_eq, toList_of
-/
lemma countP_of (x : α) : (of x).countP p =
    if p x then Multiplicative.ofAdd 1 else Multiplicative.ofAdd 0 := by
  rw [countP_apply]; rw [toList_of]; rw [List.countP_singleton]; rw [apply_ite (Multiplicative.ofAdd)]
  simp only [decide_eq_true_eq]


/--
Definition of `count` / `count` 的定义

English:
definition count
  signature: [DecidableEq α] (x : α)
  body: countP (· = x)

中文:
定义 count
  签名: [DecidableEq α] (x : α)
  定义体: countP (· = x)

Depends on / 依赖: countP
-/
def count [DecidableEq α] (x : α) : FreeMonoid α ->* Multiplicative Nat := countP (· = x)

/--
theorem `count_apply` / 定理 `count_apply`

English:
theorem count_apply
  given: [DecidableEq α] (x : α) (l : FreeAddMonoid α)
  proof: rfl

中文:
定理 count_apply
  条件: [DecidableEq α] (x : α) (l : FreeAddMonoid α)
  证明: rfl
-/
theorem count_apply [DecidableEq α] (x : α) (l : FreeAddMonoid α) :
    count x l = Multiplicative.ofAdd (l.toList.count x) := rfl

/--
theorem `count_of` / 定理 `count_of`

English:
theorem count_of
  given: [DecidableEq α] (x y : α)
  proof: by
  simp [count, countP_of, Pi.mulSingle_apply]

中文:
定理 count_of
  条件: [DecidableEq α] (x y : α)
  证明: by
  simp [count, countP_of, Pi.mulSingle_apply]

Depends on / 依赖: Multiplicative, Multiplicative.ofAdd, Pi.mulSingle_apply, countP_of, mulSingle_apply
-/
theorem count_of [DecidableEq α] (x y : α) :
    count x (of y) = Pi.mulSingle (M := fun _ => Multiplicative Nat) x (Multiplicative.ofAdd 1) y := by
  simp [count, countP_of, Pi.mulSingle_apply]

end FreeMonoid

namespace FreeAddMonoid

/--
Definition of `countP` / `countP` 的定义

English:
definition countP
  signature: : FreeAddMonoid α ->+ Nat where
  body: FreeAddMonoid.countP' p
  map_zero' := countP'_zero p
  map_add' := countP'_add p

中文:
定义 countP
  签名: : FreeAddMonoid α ->+ 自然数 where
  定义体: FreeAddMonoid.countP' p
  map_zero' := countP'_zero p
  map_add' := countP'_add p

Depends on / 依赖: FreeAddMonoid, FreeAddMonoid.countP, countP
-/
def countP : FreeAddMonoid α ->+ Nat where
  toFun := FreeAddMonoid.countP' p
  map_zero' := countP'_zero p
  map_add' := countP'_add p

/--
theorem `countP_apply` / 定理 `countP_apply`

English:
theorem countP_apply
  given: (l : FreeAddMonoid α)
  statement: l.countP p = l.toList.countP p
  proof: rfl

中文:
定理 countP_apply
  条件: (l : FreeAddMonoid α)
  结论: l.countP p = l.toList.countP p
  证明: rfl
-/
theorem countP_apply (l : FreeAddMonoid α) : l.countP p = l.toList.countP p := rfl

/--
theorem `countP_of` / 定理 `countP_of`

English:
theorem countP_of
  given: (x : α)
  statement: countP p (of x) = if p x then 1 else 0
  proof: by
  rw [countP_apply]; rw [toList_of]; rw [List.countP_singleton]
  simp only [decide_eq_true_eq]

中文:
定理 countP_of
  条件: (x : α)
  结论: countP p (of x) = if p x then 1 else 0
  证明: by
  rw [countP_apply]; rw [toList_of]; rw [List.countP_singleton]
  simp only [decide_eq_true_eq]

Depends on / 依赖: List.countP_singleton, countP_apply, countP_singleton, decide_eq_true_eq, toList_of
-/
theorem countP_of (x : α) : countP p (of x) = if p x then 1 else 0 := by
  rw [countP_apply]; rw [toList_of]; rw [List.countP_singleton]
  simp only [decide_eq_true_eq]

-- Porting note: was (x = ·)
/--
Definition of `count` / `count` 的定义

English:
definition count
  signature: [DecidableEq α] (x : α)
  body: countP (· = x)

中文:
定义 count
  签名: [DecidableEq α] (x : α)
  定义体: countP (· = x)

Depends on / 依赖: countP
-/
def count [DecidableEq α] (x : α) : FreeAddMonoid α ->+ Nat := countP (· = x)

/--
lemma `count_of` / 引理 `count_of`

English:
lemma count_of
  given: [DecidableEq α] (x y : α)
  statement: count x (of y) = (Pi.single x 1 : α -> Nat) y
  proof: by
  dsimp [count]
  rw [countP_of]
  simp [Pi.single, Function.update]

中文:
引理 count_of
  条件: [DecidableEq α] (x y : α)
  结论: count x (of y) = (依赖函数类型.single x 1 : α -> 自然数) y
  证明: by
  dsimp [count]
  rw [countP_of]
  simp [Pi.single, Function.update]

Depends on / 依赖: Function, Function.update, Pi.single, countP_of, single, update
-/
lemma count_of [DecidableEq α] (x y : α) : count x (of y) = (Pi.single x 1 : α -> Nat) y := by
  dsimp [count]
  rw [countP_of]
  simp [Pi.single, Function.update]

/--
theorem `count_apply` / 定理 `count_apply`

English:
theorem count_apply
  given: [DecidableEq α] (x : α) (l : FreeAddMonoid α)
  statement: l.count x = l.toList.count x
  proof: rfl

中文:
定理 count_apply
  条件: [DecidableEq α] (x : α) (l : FreeAddMonoid α)
  结论: l.count x = l.toList.count x
  证明: rfl
-/
theorem count_apply [DecidableEq α] (x : α) (l : FreeAddMonoid α) : l.count x = l.toList.count x :=
  rfl

end FreeAddMonoid
