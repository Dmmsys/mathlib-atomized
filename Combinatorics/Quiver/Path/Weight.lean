/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Combinatorics.Quiver.Path
public import Mathlib.Algebra.Order.Ring.Defs


/-!
# Path weights in a Quiver

This file defines the weight of a path in a quiver. The weight of a path is the product of the
weights of its edges, where weights are taken from a monoid.

## Main definitions

* `Quiver.Path.weight`: The weight of a path, defined as the multiplicative product of the
  weights of its constituent edges.
* `Quiver.Path.weightOfEPs`: A convenience version of `weight` where the weight of an edge
  is determined by a function of its source and target vertices.

## Main results

* `Quiver.Path.weight_comp`: The weight of a composition of paths is the product of their weights.
* `Quiver.Path.weight_pos`: If all edge weights are positive, the path weight is positive.
* `Quiver.Path.weightOfEPs_nonneg`: If all edge weights are non-negative, so is the path weight.
-/

@[expose] public section

namespace Quiver.Path

variable {V : Type*} [Quiver V] {R : Type*}

section Weight

variable [Monoid R]

/-- The weight of a path is the product of the weights of its edges. -/
/-
**Quiver.Path.weight** 是 Mathlib 中的一个定义，位于命名空间 `Quiver.Path`。
形式化陈述：{V : Type u_1} →   [inst : Quiver V] → {R : Type u_2} → [Monoid R] → ({i j
 : V} → (i ⟶ j) → R) → {i j : V} → Quiver.Path i j → R
参数：{i j : V} → (i ⟶ j) → R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The weight of a path is the product of the weights of its edges.
-/
def weight (w : ∀ {i j : V}, (i ⟶ j) → R) : ∀ {i j : V}, Path i j → R
  | _, _, Path.nil => 1
  | _, _, Path.cons p e => weight w p * w e

/-- The additive weight of a path is the sum of the weights of its edges. -/
/-
**Quiver.Path.addWeight** 是 Mathlib 中的一个定义，位于命名空间 `Quiver.Path`。
形式化陈述：{V : Type u_1} →   [inst : Quiver V] → {R : Type u_3} → [AddMonoid R] → ({
i j : V} → (i ⟶ j) → R) → {i j : V} → Quiver.Path i j → R
参数：{i j : V} → (i ⟶ j) → R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The additive weight of a path is the sum of the weights of its edges.
-/
def addWeight {R : Type*} [AddMonoid R] (w : ∀ {i j : V}, (i ⟶ j) → R) : ∀ {i j : V}, Path i j → R
  | _, _, Path.nil => 0
  | _, _, Path.cons p e => addWeight w p + w e

attribute [to_additive existing addWeight] weight

/-- The weight of a path, where the weight of an edge is defined by a function on its endpoints. -/
@[to_additive addWeightOfEPs /-- The additive weight of a path, where the weight of an edge is
defined by a function on its endpoints. -/]
/-
**Quiver.Path.weightOfEPs** 是 Mathlib 中的一个定义，位于命名空间 `Quiver.Path`。
形式化陈述：weightOfEPs (w : V -> V -> R) : forall {i j : V}, Path i j -> R
参数：w : V -> V -> R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def weightOfEPs (w : V → V → R) : ∀ {i j : V}, Path i j → R :=
  weight (fun {i j} (_ : i ⟶ j) => w i j)

@[to_additive (attr := simp) addWeight_nil]
/-
**Quiver.Path.weight_nil** 是 Mathlib 中的一个引理，位于命名空间 `Quiver.Path`。
形式化陈述：weight_nil (w : forall {i j : V}, (i ⟶ j) -> R) (a : V) : weight w (Path.n
il : Path a a) = 1
参数：w : forall {i j : V}, (i ⟶ j) -> R；a : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Quiver.Path.weight.eq_1`：∀ {V : Type u_1} [inst : Quiver V] {R : Type u_
2} [inst_1 : Monoid R] (w : {i j : V} → (i ⟶ j) → R) (x : V),   Quiver.Path.weig
ht w Quiver.P…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma weight_nil (w : ∀ {i j : V}, (i ⟶ j) → R) (a : V) :
    weight w (Path.nil : Path a a) = 1 := by
  simp [weight]

@[to_additive (attr := simp) addWeight_cons]
/-
**Quiver.Path.weight_cons** 是 Mathlib 中的一个引理，位于命名空间 `Quiver.Path`。
形式化陈述：weight_cons (w : forall {i j : V}, (i ⟶ j) -> R) {a b c : V} (p : Path a b
) (e : b ⟶ c) : weight w (p.cons e) = weight w p * w e
参数：w : forall {i j : V}, (i ⟶ j) -> R；p : Path a b；e : b ⟶ c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Quiver.Path.weight.eq_2`：∀ {V : Type u_1} [inst : Quiver V] {R : Type u_
2} [inst_1 : Monoid R] (w : {i j : V} → (i ⟶ j) → R) (x x_1 b : V)   (p : Quiver
.Path x b) (e…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma weight_cons (w : ∀ {i j : V}, (i ⟶ j) → R) {a b c : V} (p : Path a b) (e : b ⟶ c) :
    weight w (p.cons e) = weight w p * w e := by
  simp [weight]

@[to_additive addWeightOfEPs_nil]
/-
**Quiver.Path.weightOfEPs_nil** 是 Mathlib 中的一个引理，位于命名空间 `Quiver.Path`。
形式化陈述：weightOfEPs_nil (w : V -> V -> R) (a : V) : weightOfEPs w (Path.nil : Path
 a a) = 1
参数：w : V -> V -> R；a : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Quiver.Path.weight_nil`：weight_nil (w : forall {i j : V}, (i ⟶ j) -> R) 
(a : V) : weight w (Path.nil : Path a a) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma weightOfEPs_nil (w : V → V → R) (a : V) :
    weightOfEPs w (Path.nil : Path a a) = 1 := by simp [weightOfEPs]

@[to_additive addWeightOfEPs_cons]
/-
**Quiver.Path.weightOfEPs_cons** 是 Mathlib 中的一个引理，位于命名空间 `Quiver.Path`。
形式化陈述：weightOfEPs_cons (w : V -> V -> R) {a b c : V} (p : Path a b) (e : b ⟶ c) 
: weightOfEPs w (p.cons e) = weightOfEPs w p * w b c
参数：w : V -> V -> R；p : Path a b；e : b ⟶ c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Quiver.Path.weight_cons`：weight_cons (w : forall {i j : V}, (i ⟶ j) -> R
) {a b c : V} (p : Path a b) (e : b ⟶ c) : weight w (p.cons e) = weight w p * w 
e
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma weightOfEPs_cons (w : V → V → R) {a b c : V} (p : Path a b) (e : b ⟶ c) :
    weightOfEPs w (p.cons e) = weightOfEPs w p * w b c := by unfold weightOfEPs; simp

@[to_additive (attr := simp) addWeight_comp]
/-
**Quiver.Path.weight_comp** 是 Mathlib 中的一个引理，位于命名空间 `Quiver.Path`。
形式化陈述：weight_comp (w : forall {i j : V}, (i ⟶ j) -> R) {a b c : V} (p : Path a b
) (q : Path b c) : weight w (p.comp q) = weight w p * weight w q
参数：w : forall {i j : V}, (i ⟶ j) -> R；p : Path a b；q : Path b c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Quiver.Path.weight_nil`：weight_nil (w : forall {i j : V}, (i ⟶ j) -> R) 
(a : V) : weight w (Path.nil : Path a a) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Quiver.Path.weight_cons`：weight_cons (w : forall {i j : V}, (i ⟶ j) -> R
) {a b c : V} (p : Path a b) (e : b ⟶ c) : weight w (p.cons e) = weight w p * w 
e
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
-/
lemma weight_comp (w : ∀ {i j : V}, (i ⟶ j) → R) {a b c : V} (p : Path a b) (q : Path b c) :
    weight w (p.comp q) = weight w p * weight w q := by
  induction q with
  | nil => simp
  | cons _ _ ih => simp [ih, mul_assoc]

@[to_additive addWeightOfEPs_comp]
/-
**Quiver.Path.weightOfEPs_comp** 是 Mathlib 中的一个引理，位于命名空间 `Quiver.Path`。
形式化陈述：weightOfEPs_comp (w : V -> V -> R) {a b c : V} (p : Path a b) (q : Path b 
c) : weightOfEPs w (p.comp q) = weightOfEPs w p * weightOfEPs w q
参数：w : V -> V -> R；p : Path a b；q : Path b c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Quiver.Path.weight_comp`：weight_comp (w : forall {i j : V}, (i ⟶ j) -> R
) {a b c : V} (p : Path a b) (q : Path b c) : weight w (p.comp q) = weight w p *
 weight w q
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma weightOfEPs_comp (w : V → V → R) {a b c : V} (p : Path a b) (q : Path b c) :
    weightOfEPs w (p.comp q) = weightOfEPs w p * weightOfEPs w q := by
  simp [weightOfEPs, weight_comp]

end Weight

section OrderedWeight

variable [Semiring R] [LinearOrder R] [IsStrictOrderedRing R]

/-- If all edge weights are positive, then the weight of any path is positive. -/
/-
**Quiver.Path.weight_pos** 是 Mathlib 中的一个引理，位于命名空间 `Quiver.Path`。
形式化陈述：weight_pos {w : forall {i j : V}, (i ⟶ j) -> R} (hw : forall {i j : V} (e 
: i ⟶ j), 0 < w e) {i j : V} (p : Path i j) : 0 < weight w p
参数：i ⟶ j；hw : forall {i j : V} (e : i ⟶ j), 0 < w e；p : Path i j。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Quiver.Path.weight_nil`：weight_nil (w : forall {i j : V}, (i ⟶ j) -> R) 
(a : V) : weight w (Path.nil : Path a a) = 1
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用引理 `Quiver.Path.weight_cons`：weight_cons (w : forall {i j : V}, (i ⟶ j) -> R
) {a b c : V} (p : Path a b) (e : b ⟶ c) : weight w (p.cons e) = weight w p * w 
e
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R

--- 原说明 ---
If all edge weights are positive, then the weight of any path is positive.
-/
lemma weight_pos {w : ∀ {i j : V}, (i ⟶ j) → R}
    (hw : ∀ {i j : V} (e : i ⟶ j), 0 < w e) {i j : V} (p : Path i j) :
    0 < weight w p := by
  induction p with
  | nil =>
      simp
  | cons p e ih =>
      have he : 0 < w e := hw e
      simpa [weight_cons] using mul_pos ih he

/-- If all edge weights are non-negative, then the weight of any path is non-negative. -/
/-
**Quiver.Path.weight_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `Quiver.Path`。
形式化陈述：weight_nonneg {w : forall {i j : V}, (i ⟶ j) -> R} (hw : forall {i j : V} 
(e : i ⟶ j), 0 <= w e) {i j : V} (p : Path i j) : 0 <= weight w p
参数：i ⟶ j；hw : forall {i j : V} (e : i ⟶ j), 0 <= w e；p : Path i j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Quiver.Path.weight_nil`：weight_nil (w : forall {i j : V}, (i ⟶ j) -> R) 
(a : V) : weight w (Path.nil : Path a a) = 1
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用引理 `Quiver.Path.weight_cons`：weight_cons (w : forall {i j : V}, (i ⟶ j) -> R
) {a b c : V} (p : Path a b) (e : b ⟶ c) : weight w (p.cons e) = weight w p * w 
e
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R

--- 原说明 ---
If all edge weights are non-negative, then the weight of any path is non-negativ
e.
-/
lemma weight_nonneg {w : ∀ {i j : V}, (i ⟶ j) → R}
    (hw : ∀ {i j : V} (e : i ⟶ j), 0 ≤ w e) {i j : V} (p : Path i j) :
    0 ≤ weight w p := by
  induction p with
  | nil =>
      simp
  | cons p e ih =>
      have he : 0 ≤ w e := hw e
      simpa [weight_cons] using mul_nonneg ih he

/-- If all edge weights (given by a function on vertices) are positive, so is the path weight. -/
/-
**Quiver.Path.weightOfEPs_pos** 是 Mathlib 中的一个引理，位于命名空间 `Quiver.Path`。
形式化陈述：weightOfEPs_pos {w : V -> V -> R} (hw : forall i j : V, 0 < w i j) {i j : 
V} (p : Path i j) : 0 < weightOfEPs w p
参数：hw : forall i j : V, 0 < w i j；p : Path i j。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Quiver.Path.weight_pos`：weight_pos {w : forall {i j : V}, (i ⟶ j) -> R} 
(hw : forall {i j : V} (e : i ⟶ j), 0 < w e) {i j : V} (p : Path i j) : 0 < weig
ht w p

--- 原说明 ---
If all edge weights (given by a function on vertices) are positive, so is the pa
th weight.
-/
lemma weightOfEPs_pos {w : V → V → R}
    (hw : ∀ i j : V, 0 < w i j) {i j : V} (p : Path i j) :
    0 < weightOfEPs w p := by
  apply weight_pos
  intro i j e
  exact hw _ _

/-- If all edge weights (given by a function on vertices) are non-negative,
so is the path weight. -/
/-
**Quiver.Path.weightOfEPs_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `Quiver.Path`。
形式化陈述：weightOfEPs_nonneg {w : V -> V -> R} (hw : forall i j : V, 0 <= w i j) {i 
j : V} (p : Path i j) : 0 <= weightOfEPs w p
参数：hw : forall i j : V, 0 <= w i j；p : Path i j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Quiver.Path.weight_nonneg`：weight_nonneg {w : forall {i j : V}, (i ⟶ j) 
-> R} (hw : forall {i j : V} (e : i ⟶ j), 0 <= w e) {i j : V} (p : Path i j) : 0
 <= weight w p

--- 原说明 ---
If all edge weights (given by a function on vertices) are non-negative,
so is the path weight.
-/
lemma weightOfEPs_nonneg {w : V → V → R}
    (hw : ∀ i j : V, 0 ≤ w i j) {i j : V} (p : Path i j) :
    0 ≤ weightOfEPs w p := by
  apply weight_nonneg
  intro i j e
  exact hw _ _

end OrderedWeight

end Quiver.Path

