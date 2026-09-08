/-
Copyright (c) 2020 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
module

public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.SetLike.Basic
public import Mathlib.Data.Sym.Basic
public import Mathlib.Data.Sym.Sym2.Init

/-!
# The symmetric square

This file defines the symmetric square, which is `α × α` modulo
swapping.  This is also known as the type of unordered pairs.

More generally, the symmetric square is the second symmetric power
(see `Data.Sym.Basic`). The equivalence is `Sym2.equivSym`.

From the point of view that an unordered pair is equivalent to a
multiset of cardinality two (see `Sym2.equivMultiset`), there is a
`Mem` instance `Sym2.Mem`, which is a `Prop`-valued membership
test.  Given `h : a ∈ z` for `z : Sym2 α`, then `Mem.other h` is the other
element of the pair, defined using `Classical.choice`.  If `α` has
decidable equality, then `h.other'` computably gives the other element.

The universal property of `Sym2` is provided as `Sym2.lift`, which
states that functions from `Sym2 α` are equivalent to symmetric
two-argument functions from `α`.

Recall that an undirected graph (allowing self loops, but no multiple
edges) is equivalent to a symmetric relation on the vertex type `α`.
Given a symmetric relation on `α`, the corresponding edge set is
constructed by `Sym2.fromRel` which is a special case of `Sym2.lift`.

## Notation

The element `Sym2.mk (a, b)` can be written as `s(a, b)` for short.

## Tags

symmetric square, unordered pairs, symmetric powers
-/

@[expose] public section

assert_not_exists MonoidWithZero

open List (Vector)
open Finset Function Sym

universe u

variable {α β γ : Type*}

namespace Sym2

/-- This is the relation capturing the notion of pairs equivalent up to permutations. -/
@[aesop (rule_sets := [Sym2]) [safe [constructors, cases], norm]]
/-
**Sym2.Rel** 是 Mathlib 中的一个归纳类型，位于命名空间 `Sym2`。
形式化陈述：(α : Type u) → α × α → α × α → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is the relation capturing the notion of pairs equivalent up to permutations
.
-/
inductive Rel (α : Type u) : α × α → α × α → Prop
  | refl (x y : α) : Rel _ (x, y) (x, y)
  | swap (x y : α) : Rel _ (x, y) (y, x)

attribute [refl] Rel.refl

@[symm]
/-
**Sym2.Rel.symm** 是 Mathlib 中的一个定理，位于命名空间 `Sym2.Rel`。
形式化陈述：∀ {α : Type u_1} {x y : α × α}, Sym2.Rel α x y → Sym2.Rel α y x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem Rel.symm {x y : α × α} : Rel α x y → Rel α y x := by aesop (rule_sets := [Sym2])

@[trans]
/-
**Sym2.Rel.trans** 是 Mathlib 中的一个定理，位于命名空间 `Sym2.Rel`。
形式化陈述：∀ {α : Type u_1} {x y z : α × α}, Sym2.Rel α x y → Sym2.Rel α y z → Sym2.R
el α x z
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem Rel.trans {x y z : α × α} (a : Rel α x y) (b : Rel α y z) : Rel α x z := by
  aesop (rule_sets := [Sym2])
/-
**Sym2.Rel.is_equivalence** 是 Mathlib 中的一个定理，位于命名空间 `Sym2.Rel`。
形式化陈述：∀ {α : Type u_1}, Equivalence (Sym2.Rel α)
参数：Sym2.Rel α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sym2.Rel.symm`：∀ {α : Type u_1} {x y : α × α}, Sym2.Rel α x y → Sym2.Rel
 α y x
· 使用定理 `Sym2.Rel.trans`：∀ {α : Type u_1} {x y z : α × α}, Sym2.Rel α x y → Sym2.
Rel α y z → Sym2.Rel α x z
-/
theorem Rel.is_equivalence : Equivalence (Rel α) :=
  { refl := fun (x, y) ↦ Rel.refl x y, symm := Rel.symm, trans := Rel.trans }

/-- One can use `attribute [local instance] Sym2.Rel.setoid` to temporarily
make `Quotient` functionality work for `α × α`. -/
@[instance_reducible]
/-
**Sym2.Rel.setoid** 是 Mathlib 中的一个定义，位于命名空间 `Sym2.Rel`。
形式化陈述：(α : Type u) → Setoid (α × α)
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Sym2.Rel.is_equivalence`：∀ {α : Type u_1}, Equivalence (Sym2.Rel α)

--- 原说明 ---
One can use `attribute [local instance] Sym2.Rel.setoid` to temporarily
make `Quotient` functionality work for `α × α`.
-/
def Rel.setoid (α : Type u) : Setoid (α × α) :=
  ⟨Rel α, Rel.is_equivalence⟩

@[simp, grind =]
/-
**Sym2.rel_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Sym2`。
形式化陈述：rel_iff' {p q : α × α} : Rel α p q ↔ p = q ∨ p = q.swap
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
-/
theorem rel_iff' {p q : α × α} : Rel α p q ↔ p = q ∨ p = q.swap := by
  aesop (rule_sets := [Sym2])
/-
**Sym2.rel_iff** 是 Mathlib 中的一个定理，位于命名空间 `Sym2`。
形式化陈述：rel_iff {x y z w : α} : Rel α (x, y) (z, w) ↔ x = z ∧ y = w ∨ x = w ∧ y = 
z
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem rel_iff {x y z w : α} : Rel α (x, y) (z, w) ↔ x = z ∧ y = w ∨ x = w ∧ y = z := by
  simp

end Sym2

/-- `Sym2 α` is the symmetric square of `α`, which, in other words, is the
type of unordered pairs.

It is equivalent in a natural way to multisets of cardinality 2 (see
`Sym2.equivMultiset`).
-/
/-
**Sym2** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：Sym2 (α : Type u)
参数：α : Type u。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Sym2 α` is the symmetric square of `α`, which, in other words, is the
type of unordered pairs.

It is equivalent in a natural way to multisets of cardinality 2 (see
`Sym2.equivMultiset`).
-/
abbrev Sym2 (α : Type u) := Quot (Sym2.Rel α)

/-- Constructor for `Sym2`. This is the quotient map `α × α → Sym2 α`. -/
/-
**Sym2.mk** 是 Mathlib 中的一个定义，位于命名空间 `Sym2`。
形式化陈述：{α : Type u_4} → α → α → Sym2 α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for `Sym2`. This is the quotient map `α × α → Sym2 α`.
-/
protected abbrev Sym2.mk {α : Type*} (a b : α) : Sym2 α := Quot.mk (Sym2.Rel α) (a, b)

/-- `s(x, y)` is an unordered pair,
which is to say a pair modulo the action of the symmetric group.

It is equal to `Sym2.mk (x, y)`. -/
notation3 "s(" x ", " y ")" => Sym2.mk x y

namespace Sym2

/-
**Sym2.sound** 是 Mathlib 中的一个定理，位于命名空间 `Sym2`。
形式化陈述：∀ {α : Type u_1} {a b c d : α}, Sym2.Rel α (a, b) (c, d) → s(a, b) = s(c, 
d)
参数：a, b；c, d；a, b；c, d。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem sound {a b c d : α} (h : Rel α (a, b) (c, d)) : s(a, b) = s(c, d) :=
  Quot.sound h
/-
**Sym2.exact** 是 Mathlib 中的一个定理，位于命名空间 `Sym2`。
形式化陈述：∀ {α : Type u_1} {a b c d : α}, s(a, b) = s(c, d) → Sym2.Rel α (a, b) (c, 
d)
参数：a, b；c, d；a, b；c, d。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.exact`：∀ {α : Sort u} {s : Setoid α} {a b : α}, ⟦a⟧ = ⟦b⟧ → a ≈
 b
-/
protected theorem exact {a b c d : α} (h : s(a, b) = s(c, d)) : Rel α (a, b) (c, d) :=
  Quotient.exact (s := Sym2.Rel.setoid α) h

@[simp, grind =]
/-
**Sym2.eq** 是 Mathlib 中的一个定理，位于命名空间 `Sym2`。
形式化陈述：∀ {α : Type u_1} {a b c d : α}, s(a, b) = s(c, d) ↔ Sym2.Rel α (a, b) (c, 
d)
参数：a, b；c, d；a, b；c, d。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.eq'`：∀ {α : Sort u_1} {s₁ : Setoid α} {a b : α}, Quotient.mk' a
 = Quotient.mk' b ↔ s₁ a b
-/
protected theorem eq {a b c d : α} : s(a, b) = s(c, d) ↔ Rel α (a, b) (c, d) :=
  Quotient.eq' (s₁ := Sym2.Rel.setoid α)

@[elab_as_elim, cases_eliminator, induction_eliminator]
/-
**Sym2.ind** 是 Mathlib 中的一个定理，位于命名空间 `Sym2`。
形式化陈述：∀ {α : Type u_1} {f : Sym2 α → Prop}, (∀ (x y : α), f s(x, y)) → ∀ (i : Sy
m2 α), f i
参数：∀ (x y : α), f s(x, y)；i : Sym2 α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem ind {f : Sym2 α → Prop} (h : ∀ x y, f s(x, y)) : ∀ i, f i :=
  Quot.ind <| Prod.rec <| h

@[elab_as_elim]
/-
**Sym2.inductionOn** 是 Mathlib 中的一个定理，位于命名空间 `Sym2`。
形式化陈述：∀ {α : Type u_1} {f : Sym2 α → Prop} (i : Sym2 α), (∀ (x y : α), f s(x, y)
) → f i
参数：i : Sym2 α；∀ (x y : α), f s(x, y)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sym2.ind`：∀ {α : Type u_1} {f : Sym2 α → Prop}, (∀ (x y : α), f s(x, y))
 → ∀ (i : Sym2 α), f i
-/
protected theorem inductionOn {f : Sym2 α → Prop} (i : Sym2 α) (hf : ∀ x y, f s(x, y)) : f i :=
  i.ind hf

@[elab_as_elim]
/-
**Sym2.inductionOn** 是 Mathlib 中的一个定理，位于命名空间 `Sym2`。
形式化陈述：∀ {α : Type u_1} {f : Sym2 α → Prop} (i : Sym2 α), (∀ (x y : α), f s(x, y)
) → f i
参数：i : Sym2 α；∀ (x y : α), f s(x, y)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sym2.ind`：∀ {α : Type u_1} {f : Sym2 α → Prop}, (∀ (x y : α), f s(x, y))
 → ∀ (i : Sym2 α), f i
-/
protected theorem inductionOn₂ {f : Sym2 α → Sym2 β → Prop} (i : Sym2 α) (j : Sym2 β)
    (hf : ∀ a₁ a₂ b₁ b₂, f s(a₁, a₂) s(b₁, b₂)) : f i j :=
  Quot.induction_on₂ i j <| by
    intro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩
    exact hf _ _ _ _

/-- Dependent recursion principle for `Sym2`. See `Quot.rec`. -/
@[elab_as_elim]
/-
**Sym2.rec** 是 Mathlib 中的一个定义，位于命名空间 `Sym2`。
形式化陈述：{α : Type u_1} →   {motive : Sym2 α → Sort u_4} →     (f : (a b : α) → mot
ive s(a, b)) →       (∀ (a b c d : α) (h : Sym2.Rel α (a, b) (c, d)), ⋯ ▸ f a b 
= f c d) → (z : Sym2 α) → motive z
参数：f : (a b : α) → motive s(a, b)；∀ (a b c d : α) (h : Sym2.Rel α (a, b) (c, d))
, ⋯ ▸ f a b = f c d；z : Sym2 α。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Sym2.sound`：∀ {α : Type u_1} {a b c d : α}, Sym2.Rel α (a, b) (c, d) → s
(a, b) = s(c, d)

--- 原说明 ---
Dependent recursion principle for `Sym2`. See `Quot.rec`.
-/
protected def rec {motive : Sym2 α → Sort*}
    (f : (a b : α) → motive s(a, b))
    (h : (a b c d : α) → (h : Rel α (a, b) (c, d)) → Eq.ndrec (f a b) (Sym2.sound h) = f c d)
    (z : Sym2 α) : motive z :=
  Quot.rec (fun (a, b) ↦ f a b) (fun (a, b) (c, d) ↦ h a b c d) z

/-- Dependent recursion principle for `Sym2`. See `Quot.recOn`. -/
@[elab_as_elim]
/-
**Sym2.recOn** 是 Mathlib 中的一个定义，位于命名空间 `Sym2`。
形式化陈述：{α : Type u_1} →   {motive : Sym2 α → Sort u_4} →     (z : Sym2 α) →      
 (f : (a b : α) → motive s(a, b)) → (∀ (a b c d : α) (h : Sym2.Rel α (a, b) (c, 
d)), ⋯ ▸ f a b = f c d) → motive z
参数：z : Sym2 α；f : (a b : α) → motive s(a, b)；∀ (a b c d : α) (h : Sym2.Rel α (a,
 b) (c, d)), ⋯ ▸ f a b = f c d。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Sym2.sound`：∀ {α : Type u_1} {a b c d : α}, Sym2.Rel α (a, b) (c, d) → s
(a, b) = s(c, d)

--- 原说明 ---
Dependent recursion principle for `Sym2`. See `Quot.recOn`.
-/
protected def recOn {motive : Sym2 α → Sort*} (z : Sym2 α)
    (f : (a b : α) → motive s(a, b))
    (h : (a b c d : α) → (h : Rel α (a, b) (c, d)) → Eq.ndrec (f a b) (Sym2.sound h) = f c d) :
    motive z :=
  Quot.recOn z (fun (a, b) ↦ f a b) (fun (a, b) (c, d) ↦ h a b c d)

/-- A dependent recursion principle for `Sym2` that uses heterogeneous equality. -/
@[elab_as_elim]
/-
**Sym2.hrec** 是 Mathlib 中的一个定义，位于命名空间 `Sym2`。
形式化陈述：{α : Type u_1} →   {motive : Sym2 α → Sort u_4} →     (f : (a b : α) → mot
ive s(a, b)) → (∀ (a b : α), f a b ≍ f b a) → (z : Sym2 α) → motive z
参数：f : (a b : α) → motive s(a, b)；∀ (a b : α), f a b ≍ f b a；z : Sym2 α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A dependent recursion principle for `Sym2` that uses heterogeneous equality.
-/
protected def hrec {motive : Sym2 α → Sort*}
    (f : (a b : α) → motive s(a, b))
    (h : (a b : α) → f a b ≍ f b a)
    (z : Sym2 α) : motive z :=
  Quot.hrecOn _ (fun (a, b) ↦ f a b) <| by
    simp only [rel_iff']
    rintro _ _ (rfl | rfl)
    exacts [HEq.rfl, h _ _]

/-- Dependent recursion principal for `Sym2` when the target is a `Subsingleton` type.
See `Quot.recOnSubsingleton`. -/
@[elab_as_elim]
/-
**Sym2.recOnSubsingleton** 是 Mathlib 中的一个定义，位于命名空间 `Sym2`。
形式化陈述：{α : Type u_1} →   {motive : Sym2 α → Sort u_4} →     [∀ (a b : α), Subsin
gleton (motive s(a, b))] → (z : Sym2 α) → ((a b : α) → motive s(a, b)) → motive 
z
参数：a b : α；motive s(a, b)；z : Sym2 α；(a b : α) → motive s(a, b)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Dependent recursion principal for `Sym2` when the target is a `Subsingleton` typ
e.
See `Quot.recOnSubsingleton`.
-/
protected abbrev recOnSubsingleton {motive : Sym2 α → Sort*}
    [(a b : α) → Subsingleton (motive s(a, b))]
    (z : Sym2 α) (f : (a b : α) → motive s(a, b)) : motive z :=
  Quot.recOnSubsingleton z fun (a, b) ↦ f a b
/-
**Sym2.mk_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Sym2`。
形式化陈述：mk_surjective : (Sym2.mk (α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.mk_surjective`：Quot.mk_surjective {r : α -> α -> Prop} : Function.S
urjective (Quot.mk r)
-/
theorem mk_surjective : (Sym2.mk (α := α)).uncurry.Surjective := Quot.mk_surjective
/-
**Sym2.** 是 Mathlib 中的一个定理，位于命名空间 `Sym2`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem «exists» {α : Sort _} {f : Sym2 α → Prop} :
    (∃ x : Sym2 α, f x) ↔ ∃ x y, f s(x, y) :=
  mk_surjective.exists.trans Prod.exists
/-
**Sym2.** 是 Mathlib 中的一个定理，位于命名空间 `Sym2`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem «forall» {α : Sort _} {f : Sym2 α → Prop} :
    (∀ x : Sym2 α, f x) ↔ ∀ x y, f s(x, y) :=
  mk_surjective.forall.trans Prod.forall
/-
**Sym2.eq_swap** 是 Mathlib 中的一个定理，位于命名空间 `Sym2`。
形式化陈述：eq_swap {a b : α} : s(a, b) = s(b, a)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eq_swap {a b : α} : s(a, b) = s(b, a) := Quot.sound (Rel.swap _ _)

@[deprecated (since := "2026-02-05")] alias mk_prod_swap_eq := eq_swap
/-
**Sym2.congr_right** 是 Mathlib 中的一个定理，位于命名空间 `Sym2`。
形式化陈述：congr_right {a b c : α} : s(a, b) = s(a, c) ↔ b = c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem congr_right {a b c : α} : s(a, b) = s(a, c) ↔ b = c := by
  simp +contextual
/-
**Sym2.congr_left** 是 Mathlib 中的一个定理，位于命名空间 `Sym2`。
形式化陈述：congr_left {a b c : α} : s(b, a) = s(c, a) ↔ b = c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem congr_left {a b c : α} : s(b, a) = s(c, a) ↔ b = c := by
  simp +contextual
/-
**Sym2.eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `Sym2`。
形式化陈述：eq_iff {x y z w : α} : s(x, y) = s(z, w) ↔ x = z ∧ y = w ∨ x = w ∧ y = z
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem eq_iff {x y z w : α} : s(x, y) = s(z, w) ↔ x = z ∧ y = w ∨ x = w ∧ y = z := by
  simp
/-
**Sym2.mk_eq_mk_iff** 是 Mathlib 中的一个定理，位于命名空间 `Sym2`。
形式化陈述：mk_eq_mk_iff {p q : α × α} : s(p.1, p.2) = s(q.1, q.2) ↔ p = q ∨ p = q.swa
p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Prod.mk.eta`：∀ {α : Type u_1} {β : Type u_2} {p : α × β}, (p.1, p.2) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mk_eq_mk_iff {p q : α × α} : s(p.1, p.2) = s(q.1, q.2) ↔ p = q ∨ p = q.swap := by
  simp

/-- The universal property of `Sym2`; symmetric functions of two arguments are equivalent to
functions from `Sym2`. Note that when `β` is `Prop`, it can sometimes be more convenient to use
`Sym2.fromRel` instead. -/
/-
**Sym2.lift** 是 Mathlib 中的一个定义，位于命名空间 `Sym2`。
形式化陈述：lift : { f : α -> α -> β // forall a₁ a₂, f a₁ a₂ = f a₂ a₁ } ≃ (Sym2 α ->
 β) where toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The universal property of `Sym2`; symmetric functions of two arguments are equiv
alent to
functions from `Sym2`. Note that when `β` is `Prop`, it can sometimes be more co
nvenient to use
`Sym2.fromRel` instead.
-/
def lift : { f : α → α → β // ∀ a₁ a₂, f a₁ a₂ = f a₂ a₁ } ≃ (Sym2 α → β) where
  toFun f :=
    Quot.lift (uncurry ↑f) <| by
      rintro _ _ ⟨⟩
      exacts [rfl, f.prop _ _]
  invFun F := ⟨fun a b ↦ F s(a, b), fun _ _ => congr_arg F eq_swap⟩
  right_inv _ := funext <| Sym2.ind fun _ _ => rfl

@[simp]
/-
**Sym2.lift_mk** 是 Mathlib 中的一个定理，位于命名空间 `Sym2`。
形式化陈述：lift_mk (f : { f : α -> α -> β // forall a₁ a₂, f a₁ a₂ = f a₂ a₁ }) (a b 
: α) : lift f s(a, b) = (f : α -> α -> β) a b
参数：f : { f : α -> α -> β // forall a₁ a₂, f a₁ a₂ = f a₂ a₁ }；a b : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lift_mk (f : { f : α → α → β // ∀ a₁ a₂, f a₁ a₂ = f a₂ a₁ }) (a b : α) :
    lift f s(a, b) = (f : α → α → β) a b :=
  rfl

@[simp]
/-
**Sym2.coe_lift_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Sym2`。
形式化陈述：coe_lift_symm_apply (F : Sym2 α -> β) (a₁ a₂ : α) : (lift.symm F : α -> α 
-> β) a₁ a₂ = F s(a₁, a₂)
参数：F : Sym2 α -> β；a₁ a₂ : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem coe_lift_symm_apply (F : Sym2 α → β) (a₁ a₂ : α) :
    (lift.symm F : α → α → β) a₁ a₂ = F s(a₁, a₂) :=
  rfl

/-- A two-argument version of `Sym2.lift`. -/
/-
**Sym2.lift** 是 Mathlib 中的一个定义，位于命名空间 `Sym2`。
形式化陈述：lift : { f : α -> α -> β // forall a₁ a₂, f a₁ a₂ = f a₂ a₁ } ≃ (Sym2 α ->
 β) where toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A two-argument version of `Sym2.lift`.
-/
def lift₂ :
    { f : α → α → β → β → γ //
        ∀ a₁ a₂ b₁ b₂, f a₁ a₂ b₁ b₂ = f a₂ a₁ b₁ b₂ ∧ f a₁ a₂ b₁ b₂ = f a₁ a₂ b₂ b₁ } ≃
      (Sym2 α → Sym2 β → γ) where
  toFun f :=
    Quotient.lift₂ (s₁ := Sym2.Rel.setoid α) (s₂ := Sym2.Rel.setoid β)
      (fun (a : α × α) (b : β × β) => f.1 a.1 a.2 b.1 b.2)
      (by
        rintro _ _ _ _ ⟨⟩ ⟨⟩
        exacts [rfl, (f.2 _ _ _ _).2, (f.2 _ _ _ _).1, (f.2 _ _ _ _).1.trans (f.2 _ _ _ _).2])
  invFun F :=
    ⟨fun a₁ a₂ b₁ b₂ => F s(a₁, a₂) s(b₁, b₂), fun a₁ a₂ b₁ b₂ => by
      constructor
      exacts [congr_arg₂ F eq_swap rfl, congr_arg₂ F rfl eq_swap]⟩
  right_inv _ := funext₂ fun a b => Sym2.inductionOn₂ a b fun _ _ _ _ => rfl

@[simp]
/-
**Sym2.lift** 是 Mathlib 中的一个定义，位于命名空间 `Sym2`。
形式化陈述：lift : { f : α -> α -> β // forall a₁ a₂, f a₁ a₂ = f a₂ a₁ } ≃ (Sym2 α ->
 β) where toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lift₂_mk
    (f :
    { f : α → α → β → β → γ //
      ∀ a₁ a₂ b₁ b₂, f a₁ a₂ b₁ b₂ = f a₂ a₁ b₁ b₂ ∧ f a₁ a₂ b₁ b₂ = f a₁ a₂ b₂ b₁ })
    (a₁ a₂ : α) (b₁ b₂ : β) : lift₂ f s(a₁, a₂) s(b₁, b₂) = (f : α → α → β → β → γ) a₁ a₂ b₁ b₂ :=
  rfl

@[simp]
/-
**Sym2.coe_lift** 是 Mathlib 中的一个定理，位于命名空间 `Sym2`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_lift₂_symm_apply (F : Sym2 α → Sym2 β → γ) (a₁ a₂ : α) (b₁ b₂ : β) :
    (lift₂.symm F : α → α → β → β → γ) a₁ a₂ b₁ b₂ = F s(a₁, a₂) s(b₁, b₂) :=
  rfl

/-- The functor `Sym2` is functorial, and this function constructs the induced maps.
-/
/-
**Sym2.map** 是 Mathlib 中的一个定义，位于命名空间 `Sym2`。
形式化陈述：map (f : α -> β) : Sym2 α -> Sym2 β
参数：f : α -> β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `Sym2` is functorial, and this function constructs the induced maps.
-/
def map (f : α → β) : Sym2 α → Sym2 β :=
  Quot.map (Prod.map f f)
    (by intro _ _ h; cases h <;> constructor)

@[simp]
/-
**Sym2.map_id** 是 Mathlib 中的一个定理，位于命名空间 `Sym2`。
形式化陈述：map_id : map (@id α) = id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem map_id : map (@id α) = id := by
  ext ⟨⟨x, y⟩⟩
  rfl
/-
**Sym2.map_comp** 是 Mathlib 中的一个定理，位于命名空间 `Sym2`。
形式化陈述：map_comp {g : β -> γ} {f : α -> β} : Sym2.map (g ∘ f) = Sym2.map g ∘ Sym2.
map f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem map_comp {g : β → γ} {f : α → β} : Sym2.map (g ∘ f) = Sym2.map g ∘ Sym2.map f := by
  ext ⟨⟨x, y⟩⟩
  rfl
/-
**Sym2.map_map** 是 Mathlib 中的一个定理，位于命名空间 `Sym2`。
形式化陈述：map_map {g : β -> γ} {f : α -> β} (x : Sym2 α) : map g (map f x) = map (g 
∘ f) x
参数：x : Sym2 α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sym2.ind`：∀ {α : Type u_1} {f : Sym2 α → Prop}, (∀ (x y : α), f s(x, y))
 → ∀ (i : Sym2 α), f i
-/
theorem map_map {g : β → γ} {f : α → β} (x : Sym2 α) : map g (map f x) = map (g ∘ f) x := by
  induction x; aesop

@[simp]
/-
**Sym2.map_mk** 是 Mathlib 中的一个定理，位于命名空间 `Sym2`。
形式化陈述：map_mk (f : α -> β) (a b : α) : map f s(a, b) = s(f a, f b)
参数：f : α -> β；a b : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_mk (f : α → β) (a b : α) : map f s(a, b) = s(f a, f b) := rfl

@[deprecated (since := "2026-02-05")] alias map_pair_eq := map_mk
/-
**Sym2.map.injective** 是 Mathlib 中的一个定理，位于命名空间 `Sym2.map`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, Function.Injective f → Functi
on.Injective (Sym2.map f)
参数：Sym2.map f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sym2.inductionOn₂`：∀ {α : Type u_1} {β : Type u_2} {f : Sym2 α → Sym2 β 
→ Prop} (i : Sym2 α) (j : Sym2 β),   (∀ (a₁ a₂ : α) (b₁ b₂ : β), f s(a₁, a₂) s(b
₁, b₂))…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
-/
theorem map.injective {f : α → β} (hinj : Injective f) : Injective (map f) := by
  intro z z'
  refine Sym2.inductionOn₂ z z' (fun x y x' y' => ?_)
  simp [hinj.eq_iff]

/-- `mk a` as an embedding. This is the symmetric version of `Function.Embedding.sectL`. -/
@[simps]
/-
**Sym2.mkEmbedding** 是 Mathlib 中的一个定义，位于命名空间 `Sym2`。
形式化陈述：mkEmbedding (a : α) : α ↪ Sym2 α where toFun b
参数：a : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`mk a` as an embedding. This is the symmetric version of `Function.Embedding.sec
tL`.
-/
def mkEmbedding (a : α) : α ↪ Sym2 α where
  toFun b := s(a, b)
  inj' b₁ b₁ h := by
    simp only [Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, true_and, Prod.swap_prod_mk] at h
    obtain rfl | ⟨rfl, rfl⟩ := h <;> rfl

/-- `Sym2.map` as an embedding. -/
@[simps]
/-
**Sym2._root_.Function.Embedding.sym2Map** 是 Mathlib 中的一个定义，位于命名空间 `Sym2`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Sym2.map` as an embedding.
-/
def _root_.Function.Embedding.sym2Map (f : α ↪ β) : Sym2 α ↪ Sym2 β where
  toFun := map f
  inj' := map.injective f.injective
/-
**Sym2.lift_comp_map** 是 Mathlib 中的一个引理，位于命名空间 `Sym2`。
形式化陈述：lift_comp_map {g : γ -> α} (f : {f : α -> α -> β // forall a₁ a₂, f a₁ a₂ 
= f a₂ a₁}) : lift f ∘ map g = lift ⟨fun (c₁ c₂ : γ) => f.val (g c₁) (g c₂), fun
 _ _ => f.prop _ _⟩
参数：f : {f : α -> α -> β // forall a₁ a₂, f a₁ a₂ = f a₂ a₁}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `Equiv.symm_apply_eq`：symm_apply_eq {α β} (e : α ≃ β) {x y} : e.symm x = 
y ↔ x = e y
-/
lemma lift_comp_map {g : γ → α} (f : {f : α → α → β // ∀ a₁ a₂, f a₁ a₂ = f a₂ a₁}) :
    lift f ∘ map g = lift ⟨fun (c₁ c₂ : γ) => f.val (g c₁) (g c₂), fun _ _ => f.prop _ _⟩ :=
  lift.symm_apply_eq.mp rfl
/-
**Sym2.lift_map_apply** 是 Mathlib 中的一个引理，位于命名空间 `Sym2`。
形式化陈述：lift_map_apply {g : γ -> α} (f : {f : α -> α -> β // forall a₁ a₂, f a₁ a₂
 = f a₂ a₁}) (p : Sym2 γ) : lift f (map g p) = lift ⟨fun (c₁ c₂ : γ) => f.val (g
 c₁) (g c₂), fun _ _ => f.prop _ _⟩ p
参数：f : {f : α -> α -> β // forall a₁ a₂, f a₁ a₂ = f a₂ a₁}；p : Sym2 γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Sym2.lift_comp_map`：lift_comp_map {g : γ -> α} (f : {f : α -> α -> β // 
forall a₁ a₂, f a₁ a₂ = f a₂ a₁}) : lift f ∘ map g = lift ⟨fun (c₁ c₂ : γ) => f.
val (g c…
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
-/
lemma lift_map_apply {g : γ → α} (f : {f : α → α → β // ∀ a₁ a₂, f a₁ a₂ = f a₂ a₁}) (p : Sym2 γ) :
    lift f (map g p) = lift ⟨fun (c₁ c₂ : γ) => f.val (g c₁) (g c₂), fun _ _ => f.prop _ _⟩ p := by
  conv_rhs => rw [← lift_comp_map, comp_apply]

section Membership

/-! ### Membership and set coercion -/


/-- This is a predicate that determines whether a given term is a member of a term of the
symmetric square.  From this point of view, the symmetric square is the subtype of
cardinality-two multisets on `α`.
-/
/-
**Sym2.Mem** 是 Mathlib 中的一个定义，位于命名空间 `Sym2`。
形式化陈述：{α : Type u_1} → α → Sym2 α → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is a predicate that determines whether a given term is a member of a term o
f the
symmetric square.  From this point of view, the symmetric square is the subtype 
of
cardinality-two multisets on `α`.
-/
protected def Mem (x : α) (z : Sym2 α) : Prop :=
  ∃ y : α, z = s(x, y)

@[aesop norm (rule_sets := [Sym2])]
/-
**Sym2.mem_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Sym2`。
形式化陈述：mem_iff' {a b c : α} : Sym2.Mem a s(b, c) ↔ a = b ∨ a = c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Sym2.eq_iff`：eq_iff {x y z w : α} : s(x, y) = s(z, w) ↔ x = z ∧ y = w ∨ 
x = w ∧ y = z
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `Sym2.eq_swap`：eq_swap {a b : α} : s(a, b) = s(b, a)
-/
theorem mem_iff' {a b c : α} : Sym2.Mem a s(b, c) ↔ a = b ∨ a = c :=
  { mp := by
      rintro ⟨_, h⟩
      rw [eq_iff] at h
      aesop
    mpr := by
      rintro (rfl | rfl)
      · exact ⟨_, rfl⟩
      rw [eq_swap]
      exact ⟨_, rfl⟩ }
/-
**Sym2.** 是 Mathlib 中的一个实例，位于命名空间 `Sym2`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SetLike (Sym2 α) α where
  coe z := { x | z.Mem x }
  coe_injective z z' h := by
    simp only [Set.ext_iff, Set.mem_ofPred_eq] at h
    obtain ⟨x, y⟩ := z
    obtain ⟨x', y'⟩ := z'
    have hx := h x; have hy := h y; have hx' := h x'; have hy' := h y'
    simp only [mem_iff'] at hx hy hx' hy'
    aesop
/-
**Sym2.** 是 Mathlib 中的一个实例，位于命名空间 `Sym2`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder (Sym2 α) := .ofSetLike (Sym2 α) α

@[simp]
/-
**Sym2.mem_iff_mem** 是 Mathlib 中的一个定理，位于命名空间 `Sym2`。
形式化陈述：mem_iff_mem {x : α} {z : Sym2 α} : Sym2.Mem x z ↔ x in z
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_iff_mem {x : α} {z : Sym2 α} : Sym2.Mem x z ↔ x ∈ z :=
  Iff.rfl
/-
**Sym2.mem_iff_exists** 是 Mathlib 中的一个定理，位于命名空间 `Sym2`。
形式化陈述：mem_iff_exists {x : α} {z : Sym2 α} : x in z ↔ exists y : α, z = s(x, y)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_iff_exists {x : α} {z : Sym2 α} : x ∈ z ↔ ∃ y : α, z = s(x, y) :=
  Iff.rfl

@[ext]
/-
**Sym2.ext** 是 Mathlib 中的一个定理，位于命名空间 `Sym2`。
形式化陈述：ext {p q : Sym2 α} (h : forall x, x in p ↔ x in q) : p = q
参数：h : forall x, x in p ↔ x in q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
-/
theorem ext {p q : Sym2 α} (h : ∀ x, x ∈ p ↔ x ∈ q) : p = q :=
  SetLike.ext h
/-
**Sym2.mem_mk_left** 是 Mathlib 中的一个定理，位于命名空间 `Sym2`。
形式化陈述：mem_mk_left (x y : α) : x in s(x, y)
参数：x y : α。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mem_mk_left (x y : α) : x ∈ s(x, y) :=
  ⟨y, rfl⟩
/-
**Sym2.mem_mk_right** 是 Mathlib 中的一个定理，位于命名空间 `Sym2`。
形式化陈述：mem_mk_right (x y : α) : y in s(x, y)
参数：x y : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sym2.mem_mk_left`：mem_mk_left (x y : α) : x in s(x, y)
· 使用定理 `Sym2.eq_swap`：eq_swap {a b : α} : s(a, b) = s(b, a)
-/
theorem mem_mk_right (x y : α) : y ∈ s(x, y) :=
  eq_swap ▸ mem_mk_left y x

@[simp, aesop norm (rule_sets := [Sym2]), grind =]
/-
**Sym2.mem_iff** 是 Mathlib 中的一个定理，位于命名空间 `Sym2`。
形式化陈述：mem_iff {a b c : α} : a in s(b, c) ↔ a = b ∨ a = c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sym2.mem_iff'`：mem_iff' {a b c : α} : Sym2.Mem a s(b, c) ↔ a = b ∨ a = c
-/
theorem mem_iff {a b c : α} : a ∈ s(b, c) ↔ a = b ∨ a = c :=
  mem_iff'
/-
**Sym2.out_fst_mem** 是 Mathlib 中的一个定理，位于命名空间 `Sym2`。
形式化陈述：out_fst_mem (e : Sym2 α) : e.out.1 in e
参数：e : Sym2 α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Sym2.mk.eq_1`：∀ {α : Type u_4} (a b : α), s(a, b) = Quot.mk (Sym2.Rel α)
 (a, b)
· 使用定理 `Quot.out_eq`：Quot.out_eq {r : α -> α -> Prop} (q : Quot r) : Quot.mk r q
.out = q
-/
theorem out_fst_mem (e : Sym2 α) : e.out.1 ∈ e :=
  ⟨e.out.2, by rw [Sym2.mk, e.out_eq]⟩
/-
**Sym2.out_snd_mem** 是 Mathlib 中的一个定理，位于命名空间 `Sym2`。
形式化陈述：out_snd_mem (e : Sym2 α) : e.out.2 in e
参数：e : Sym2 α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Sym2.eq_swap`：eq_swap {a b : α} : s(a, b) = s(b, a)
· 使用定理 `Sym2.mk.eq_1`：∀ {α : Type u_4} (a b : α), s(a, b) = Quot.mk (Sym2.Rel α)
 (a, b)
· 使用定理 `Quot.out_eq`：Quot.out_eq {r : α -> α -> Prop} (q : Quot r) : Quot.mk r q
.out = q
-/
theorem out_snd_mem (e : Sym2 α) : e.out.2 ∈ e :=
  ⟨e.out.1, by rw [eq_swap, Sym2.mk, e.out_eq]⟩
/-
**Sym2.ball** 是 Mathlib 中的一个定理，位于命名空间 `Sym2`。
形式化陈述：ball {p : α -> Prop} {a b : α} : (forall c in s(a, b), p c) ↔ p a ∧ p b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem ball {p : α → Prop} {a b : α} : (∀ c ∈ s(a, b), p c) ↔ p a ∧ p b := by
  simp
/-
**Sym2.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `Sym2`。
形式化陈述：∀ {α : Type u_1} {x y : α}, ↑s(x, y) = {x, y}
参数：x, y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma coe_mk {x y : α} : (s(x, y) : Set α) = {x, y} := by ext z; simp
/-
**Sym2.coe_map** 是 Mathlib 中的一个定理，位于命名空间 `Sym2`。
形式化陈述：coe_map (f : α -> β) (z : Sym2 α) : z.map f = f '' z
参数：f : α -> β；z : Sym2 α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sym2.ind`：∀ {α : Type u_1} {f : Sym2 α → Prop}, (∀ (x y : α), f s(x, y))
 → ∀ (i : Sym2 α), f i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Sym2.coe_mk`：∀ {α : Type u_1} {x y : α}, ↑s(x, y) = {x, y}
· 使用定理 `Set.image_pair`：image_pair (f : α -> β) (a b : α) : f '' {a, b} = {f a, 
f b}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem coe_map (f : α → β) (z : Sym2 α) : z.map f = f '' z := by
  cases z
  simp [Set.image_pair]

/-- Given an element of the unordered pair, give the other element using `Classical.choose`.
See also `Mem.other'` for the computable version.
-/
/-
**Sym2.Mem.other** 是 Mathlib 中的一个定义，位于命名空间 `Sym2.Mem`。
形式化陈述：{α : Type u_1} → {a : α} → {z : Sym2 α} → a ∈ z → α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an element of the unordered pair, give the other element using `Classical.
choose`.
See also `Mem.other'` for the computable version.
-/
noncomputable def Mem.other {a : α} {z : Sym2 α} (h : a ∈ z) : α :=
  Classical.choose h

@[simp]
/-
**Sym2.other_spec** 是 Mathlib 中的一个定理，位于命名空间 `Sym2`。
形式化陈述：other_spec {a : α} {z : Sym2 α} (h : a in z) : s(a, Mem.other h) = z
参数：h : a in z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem other_spec {a : α} {z : Sym2 α} (h : a ∈ z) : s(a, Mem.other h) = z :=
  (Classical.choose_spec h).symm
/-
**Sym2.other_mem** 是 Mathlib 中的一个定理，位于命名空间 `Sym2`。
形式化陈述：other_mem {a : α} {z : Sym2 α} (h : a in z) : Mem.other h in z
参数：h : a in z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Sym2.other_spec`：other_spec {a : α} {z : Sym2 α} (h : a in z) : s(a, Mem
.other h) = z
· 使用定理 `Sym2.mem_mk_right`：mem_mk_right (x y : α) : y in s(x, y)
-/
theorem other_mem {a : α} {z : Sym2 α} (h : a ∈ z) : Mem.other h ∈ z := by
  convert! mem_mk_right a <| Mem.other h
  rw [other_spec h]
/-
**Sym2.mem_and_mem_iff** 是 Mathlib 中的一个定理，位于命名空间 `Sym2`。
形式化陈述：mem_and_mem_iff {x y : α} {z : Sym2 α} (hne : x != y) : x in z ∧ y in z ↔ 
z = s(x, y)
参数：hne : x != y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sym2.ind`：∀ {α : Type u_1} {f : Sym2 α → Prop}, (∀ (x y : α), f s(x, y))
 → ∀ (i : Sym2 α), f i
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Sym2.mem_iff`：mem_iff {a b c : α} : a in s(b, c) ↔ a = b ∨ a = c
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
-/
theorem mem_and_mem_iff {x y : α} {z : Sym2 α} (hne : x ≠ y) : x ∈ z ∧ y ∈ z ↔ z = s(x, y) := by
  constructor
  · cases z
    rw [mem_iff, mem_iff]
    aesop
  · rintro rfl
    simp
/-
**Sym2.eq_of_ne_mem** 是 Mathlib 中的一个定理，位于命名空间 `Sym2`。
形式化陈述：eq_of_ne_mem {x y : α} {z z' : Sym2 α} (h : x != y) (h1 : x in z) (h2 : y 
in z) (h3 : x in z') (h4 : y in z') : z = z'
参数：h : x != y；h1 : x in z；h2 : y in z；h3 : x in z'；h4 : y in z'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Sym2.mem_and_mem_iff`：mem_and_mem_iff {x y : α} {z : Sym2 α} (hne : x !=
 y) : x in z ∧ y in z ↔ z = s(x, y)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem eq_of_ne_mem {x y : α} {z z' : Sym2 α} (h : x ≠ y) (h1 : x ∈ z) (h2 : y ∈ z) (h3 : x ∈ z')
    (h4 : y ∈ z') : z = z' :=
  ((mem_and_mem_iff h).mp ⟨h1, h2⟩).trans ((mem_and_mem_iff h).mp ⟨h3, h4⟩).symm
/-
**Sym2.Mem.decidable** 是 Mathlib 中的一个定义，位于命名空间 `Sym2.Mem`。
形式化陈述：{α : Type u_1} → [DecidableEq α] → (x : α) → (z : Sym2 α) → Decidable (x ∈
 z)
参数：x : α；z : Sym2 α；x ∈ z。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Sym2.mem_iff`：mem_iff {a b c : α} : a in s(b, c) ↔ a = b ∨ a = c
-/
instance Mem.decidable [DecidableEq α] (x : α) (z : Sym2 α) : Decidable (x ∈ z) :=
  z.recOnSubsingleton fun _ _ => decidable_of_iff' _ mem_iff

end Membership

@[simp]
/-
**Sym2.mem_map** 是 Mathlib 中的一个定理，位于命名空间 `Sym2`。
形式化陈述：mem_map {f : α -> β} {b : β} {z : Sym2 α} : b in Sym2.map f z ↔ exists a, 
a in z ∧ f a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sym2.ind`：∀ {α : Type u_1} {f : Sym2 α → Prop}, (∀ (x y : α), f s(x, y))
 → ∀ (i : Sym2 α), f i
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
-/
theorem mem_map {f : α → β} {b : β} {z : Sym2 α} : b ∈ Sym2.map f z ↔ ∃ a, a ∈ z ∧ f a = b := by
  cases z
  aesop

@[congr]
/-
**Sym2.map_congr** 是 Mathlib 中的一个定理，位于命名空间 `Sym2`。
形式化陈述：map_congr {f g : α -> β} {s : Sym2 α} (h : forall x in s, f x = g x) : map
 f s = map g s
参数：h : forall x in s, f x = g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sym2.ext`：ext {p q : Sym2 α} (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
theorem map_congr {f g : α → β} {s : Sym2 α} (h : ∀ x ∈ s, f x = g x) : map f s = map g s := by
  ext y
  simp only [mem_map]
  constructor <;>
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w, hw, by simp [hw, h]⟩

/-- Note: `Sym2.map_id` will not simplify `Sym2.map id z` due to `Sym2.map_congr`. -/
@[simp]
/-
**Sym2.map_id'** 是 Mathlib 中的一个定理，位于命名空间 `Sym2`。
形式化陈述：map_id' : (map fun x : α => x) = id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sym2.map_id`：map_id : map (@id α) = id

--- 原说明 ---
Note: `Sym2.map_id` will not simplify `Sym2.map id z` due to `Sym2.map_congr`.
-/
theorem map_id' : (map fun x : α => x) = id :=
  map_id

/--
Partial map. If `f : ∀ a, p a → β` is a partial function defined on `a : α` satisfying `p`,
then `pmap f s h` is essentially the same as `map f s` but is defined only when all members of `s`
satisfy `p`, using the proof to apply `f`.
-/
/-
**Sym2.pmap** 是 Mathlib 中的一个定义，位于命名空间 `Sym2`。
形式化陈述：pmap {P : α -> Prop} (f : forall a, P a -> β) (s : Sym2 α) : (forall a in 
s, P a) -> Sym2 β
参数：f : forall a, P a -> β；s : Sym2 α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Partial map. If `f : ∀ a, p a → β` is a partial function defined on `a : α` sati
sfying `p`,
then `pmap f s h` is essentially the same as `map f s` but is defined only when 
all members of `s`
satisfy `p`, using the proof to apply `f`.
-/
def pmap {P : α → Prop} (f : ∀ a, P a → β) (s : Sym2 α) : (∀ a ∈ s, P a) → Sym2 β :=
  let g (p : α × α) (H : ∀ a ∈ Sym2.mk p.1 p.2, P a) : Sym2 β :=
    s(f p.1 (H p.1 <| mem_mk_left _ _), f p.2 (H p.2 <| mem_mk_right _ _))
  Quot.recOn s g fun p q hpq => funext fun Hq => by
    rw [rel_iff'] at hpq
    have Hp : ∀ a ∈ s(p.1, p.2), P a := fun a hmem =>
      Hq a (Sym2.mk_eq_mk_iff.2 hpq ▸ hmem : a ∈ s(q.1, q.2))
    have h : ∀ {s₂ e H}, Eq.ndrec (motive := fun s => (∀ a ∈ s, P a) → Sym2 β) (g p) (b := s₂) e H =
      g p Hp := by
      rintro s₂ rfl _
      rfl
    refine h.trans (Quot.sound ?_)
    rw [rel_iff', Prod.mk.injEq, Prod.swap_prod_mk]
    apply hpq.imp <;> rintro rfl <;> simp
/-
**Sym2.forall_mem_pair** 是 Mathlib 中的一个定理，位于命名空间 `Sym2`。
形式化陈述：forall_mem_pair {P : α -> Prop} {a b : α} : (forall x in s(a, b), P x) ↔ P
 a ∧ P b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem forall_mem_pair {P : α → Prop} {a b : α} : (∀ x ∈ s(a, b), P x) ↔ P a ∧ P b := by
  simp only [mem_iff, forall_eq_or_imp, forall_eq]
/-
**Sym2.pair_eq_pmap** 是 Mathlib 中的一个引理，位于命名空间 `Sym2`。
形式化陈述：pair_eq_pmap {P : α -> Prop} (f : forall a, P a -> β) (a b : α) (h : P a) 
(h' : P b) : s(f a h, f b h') = pmap f s(a, b) (forall_mem_pair.mpr ⟨h, h'⟩)
参数：f : forall a, P a -> β；a b : α；h : P a；h' : P b。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma pair_eq_pmap {P : α → Prop} (f : ∀ a, P a → β) (a b : α) (h : P a) (h' : P b) :
    s(f a h, f b h') = pmap f s(a, b) (forall_mem_pair.mpr ⟨h, h'⟩) := rfl
/-
**Sym2.pmap_pair** 是 Mathlib 中的一个引理，位于命名空间 `Sym2`。
形式化陈述：pmap_pair {P : α -> Prop} (f : forall a, P a -> β) (a b : α) (h : forall x
 in s(a, b), P x) : pmap f s(a, b) h = s(f a (h a (mem_mk_left a b)), f b (h b (
mem_mk_right a b)))
参数：f : forall a, P a -> β；a b : α；h : forall x in s(a, b), P x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma pmap_pair {P : α → Prop} (f : ∀ a, P a → β) (a b : α) (h : ∀ x ∈ s(a, b), P x) :
    pmap f s(a, b) h = s(f a (h a (mem_mk_left a b)), f b (h b (mem_mk_right a b))) := rfl

@[simp]
/-
**Sym2.mem_pmap_iff** 是 Mathlib 中的一个引理，位于命名空间 `Sym2`。
形式化陈述：mem_pmap_iff {P : α -> Prop} (f : forall a, P a -> β) (z : Sym2 α) (h : fo
rall a in z, P a) (b : β) : b in z.pmap f h ↔ exists (a : α) (ha : a in z), b = 
f a (h a ha)
参数：f : forall a, P a -> β；z : Sym2 α；h : forall a in z, P a；b : β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sym2.mem_mk_left`：mem_mk_left (x y : α) : x in s(x, y)
· 使用定理 `Sym2.mem_mk_right`：mem_mk_right (x y : α) : y in s(x, y)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Sym2.pmap_pair`：pmap_pair {P : α -> Prop} (f : forall a, P a -> β) (a b 
: α) (h : forall x in s(a, b), P x) : pmap f s(a, b) h = s(f a (h a (mem_mk_left
 a b…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
-/
lemma mem_pmap_iff {P : α → Prop} (f : ∀ a, P a → β) (z : Sym2 α) (h : ∀ a ∈ z, P a) (b : β) :
    b ∈ z.pmap f h ↔ ∃ (a : α) (ha : a ∈ z), b = f a (h a ha) := by
  obtain ⟨x, y⟩ := z
  rw [pmap_pair f x y h]
  aesop
/-
**Sym2.pmap_eq_map** 是 Mathlib 中的一个引理，位于命名空间 `Sym2`。
形式化陈述：pmap_eq_map {P : α -> Prop} (f : α -> β) (z : Sym2 α) (h : forall a in z, 
P a) : z.pmap (fun a _ => f a) h = z.map f
参数：f : α -> β；z : Sym2 α；h : forall a in z, P a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sym2.ind`：∀ {α : Type u_1} {f : Sym2 α → Prop}, (∀ (x y : α), f s(x, y))
 → ∀ (i : Sym2 α), f i
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma pmap_eq_map {P : α → Prop} (f : α → β) (z : Sym2 α) (h : ∀ a ∈ z, P a) :
    z.pmap (fun a _ => f a) h = z.map f := by
  cases z; rfl
/-
**Sym2.map_pmap** 是 Mathlib 中的一个引理，位于命名空间 `Sym2`。
形式化陈述：map_pmap {Q : β -> Prop} (f : α -> β) (g : forall b, Q b -> γ) (z : Sym2 α
) (h : forall b in z.map f, Q b) : (z.map f).pmap g h = z.pmap (fun a ha => g (f
 a) (h (f a) (mem_map.mpr ⟨a, ha, rfl⟩))) (fun _ ha => ha)
参数：f : α -> β；g : forall b, Q b -> γ；z : Sym2 α；h : forall b in z.map f, Q b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sym2.ind`：∀ {α : Type u_1} {f : Sym2 α → Prop}, (∀ (x y : α), f s(x, y))
 → ∀ (i : Sym2 α), f i
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Sym2.mem_map`：mem_map {f : α -> β} {b : β} {z : Sym2 α} : b in Sym2.map 
f z ↔ exists a, a in z ∧ f a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma map_pmap {Q : β → Prop} (f : α → β) (g : ∀ b, Q b → γ) (z : Sym2 α) (h : ∀ b ∈ z.map f, Q b) :
    (z.map f).pmap g h =
    z.pmap (fun a ha => g (f a) (h (f a) (mem_map.mpr ⟨a, ha, rfl⟩))) (fun _ ha => ha) := by
  cases z; rfl
/-
**Sym2.pmap_map** 是 Mathlib 中的一个引理，位于命名空间 `Sym2`。
形式化陈述：pmap_map {P : α -> Prop} {Q : β -> Prop} (f : forall a, P a -> β) (g : β -
> γ) (z : Sym2 α) (h : forall a in z, P a) (h' : forall b in z.pmap f h, Q b) : 
(z.pmap f h).map g = z.pmap (fun a ha => g (f a (h a ha))) (fun _ ha => ha)
参数：f : forall a, P a -> β；g : β -> γ；z : Sym2 α；h : forall a in z, P a；h' : fora
ll b in z.pmap f h, Q b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sym2.ind`：∀ {α : Type u_1} {f : Sym2 α → Prop}, (∀ (x y : α), f s(x, y))
 → ∀ (i : Sym2 α), f i
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma pmap_map {P : α → Prop} {Q : β → Prop} (f : ∀ a, P a → β) (g : β → γ)
    (z : Sym2 α) (h : ∀ a ∈ z, P a) (h' : ∀ b ∈ z.pmap f h, Q b) :
    (z.pmap f h).map g = z.pmap (fun a ha => g (f a (h a ha))) (fun _ ha ↦ ha) := by
  cases z; rfl
/-
**Sym2.pmap_pmap** 是 Mathlib 中的一个引理，位于命名空间 `Sym2`。
形式化陈述：pmap_pmap {P : α -> Prop} {Q : β -> Prop} (f : forall a, P a -> β) (g : fo
rall b, Q b -> γ) (z : Sym2 α) (h : forall a in z, P a) (h' : forall b in z.pmap
 f h, Q b) : (z.pmap f h).pmap g h' = z.pmap (fun a ha => g (f a (h a ha)) (h' _
 ((mem_pmap_iff f z h _).mpr ⟨a, ha, rfl⟩))) (fun _ ha => ha)
参数：f : forall a, P a -> β；g : forall b, Q b -> γ；z : Sym2 α；h : forall a in z, P
 a；h' : forall b in z.pmap f h, Q b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sym2.ind`：∀ {α : Type u_1} {f : Sym2 α → Prop}, (∀ (x y : α), f s(x, y))
 → ∀ (i : Sym2 α), f i
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Sym2.mem_pmap_iff`：mem_pmap_iff {P : α -> Prop} (f : forall a, P a -> β)
 (z : Sym2 α) (h : forall a in z, P a) (b : β) : b in z.pmap f h ↔ exists (a : α
) (ha :…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma pmap_pmap {P : α → Prop} {Q : β → Prop} (f : ∀ a, P a → β) (g : ∀ b, Q b → γ)
    (z : Sym2 α) (h : ∀ a ∈ z, P a) (h' : ∀ b ∈ z.pmap f h, Q b) :
    (z.pmap f h).pmap g h' = z.pmap (fun a ha => g (f a (h a ha))
    (h' _ ((mem_pmap_iff f z h _).mpr ⟨a, ha, rfl⟩))) (fun _ ha ↦ ha) := by
  cases z; rfl

@[simp]
/-
**Sym2.pmap_subtype_map_subtypeVal** 是 Mathlib 中的一个引理，位于命名空间 `Sym2`。
形式化陈述：pmap_subtype_map_subtypeVal {P : α -> Prop} (s : Sym2 α) (h : forall a in 
s, P a) : (s.pmap Subtype.mk h).map Subtype.val = s
参数：s : Sym2 α；h : forall a in s, P a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sym2.ind`：∀ {α : Type u_1} {f : Sym2 α → Prop}, (∀ (x y : α), f s(x, y))
 → ∀ (i : Sym2 α), f i
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma pmap_subtype_map_subtypeVal {P : α → Prop} (s : Sym2 α) (h : ∀ a ∈ s, P a) :
    (s.pmap Subtype.mk h).map Subtype.val = s := by
  cases s; rfl

/--
"Attach" a proof `P a` that holds for all the elements of `s` to produce a new Sym2 object
with the same elements but in the type `{x // P x}`.
-/
/-
**Sym2.attachWith** 是 Mathlib 中的一个定义，位于命名空间 `Sym2`。
形式化陈述：attachWith {P : α -> Prop} (s : Sym2 α) (h : forall a in s, P a) : Sym2 {a
 // P a}
参数：s : Sym2 α；h : forall a in s, P a。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
"Attach" a proof `P a` that holds for all the elements of `s` to produce a new S
ym2 object
with the same elements but in the type `{x // P x}`.
-/
def attachWith {P : α → Prop} (s : Sym2 α) (h : ∀ a ∈ s, P a) : Sym2 {a // P a} :=
  pmap Subtype.mk s h

@[simp]
/-
**Sym2.attachWith_map_subtypeVal** 是 Mathlib 中的一个引理，位于命名空间 `Sym2`。
形式化陈述：attachWith_map_subtypeVal {s : Sym2 α} {P : α -> Prop} (h : forall a in s,
 P a) : (s.attachWith h).map Subtype.val = s
参数：h : forall a in s, P a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sym2.ind`：∀ {α : Type u_1} {f : Sym2 α → Prop}, (∀ (x y : α), f s(x, y))
 → ∀ (i : Sym2 α), f i
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma attachWith_map_subtypeVal {s : Sym2 α} {P : α → Prop} (h : ∀ a ∈ s, P a) :
    (s.attachWith h).map Subtype.val = s := by
  cases s; rfl

/-! ### Diagonal -/

variable {z : Sym2 α} {f : α → β}

/-- A type `α` is naturally included in the diagonal of `α × α`, and this function gives the image
of this diagonal in `Sym2 α`.
-/
/-
**Sym2.diag** 是 Mathlib 中的一个定义，位于命名空间 `Sym2`。
形式化陈述：diag (x : α) : Sym2 α
参数：x : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A type `α` is naturally included in the diagonal of `α × α`, and this function g
ives the image
of this diagonal in `Sym2 α`.
-/
def diag (x : α) : Sym2 α := s(x, x)
/-
**Sym2.diag_injective** 是 Mathlib 中的一个定理，位于命名空间 `Sym2`。
形式化陈述：diag_injective : Function.Injective (Sym2.diag : α -> Sym2 α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sym2.exact`：∀ {α : Type u_1} {a b c d : α}, s(a, b) = s(c, d) → Sym2.Rel
 α (a, b) (c, d)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem diag_injective : Function.Injective (Sym2.diag : α → Sym2 α) := fun x y h => by
  cases Sym2.exact h <;> rfl

/-- A predicate for testing whether an element of `Sym2 α` is on the diagonal.
-/
/-
**Sym2.IsDiag** 是 Mathlib 中的一个定义，位于命名空间 `Sym2`。
形式化陈述：IsDiag : Sym2 α -> Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A predicate for testing whether an element of `Sym2 α` is on the diagonal.
-/
def IsDiag : Sym2 α → Prop :=
  lift ⟨Eq, fun _ _ => propext eq_comm⟩

@[simp]
/-
**Sym2.mk_isDiag_iff** 是 Mathlib 中的一个定理，位于命名空间 `Sym2`。
形式化陈述：mk_isDiag_iff {x y : α} : IsDiag s(x, y) ↔ x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mk_isDiag_iff {x y : α} : IsDiag s(x, y) ↔ x = y :=
  Iff.rfl

@[deprecated (since := "2026-02-05")] alias isDiag_iff_proj_eq := mk_isDiag_iff
/-
**Sym2.IsDiag.map** 是 Mathlib 中的一个定理，位于命名空间 `Sym2.IsDiag`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {z : Sym2 α} {f : α → β}, z.IsDiag → (Sym2
.map f z).IsDiag
参数：Sym2.map f z。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sym2.ind`：∀ {α : Type u_1} {f : Sym2 α → Prop}, (∀ (x y : α), f s(x, y))
 → ∀ (i : Sym2 α), f i
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
protected lemma IsDiag.map : z.IsDiag → (z.map f).IsDiag := Sym2.ind (fun _ _ ↦ congr_arg f) z
/-
**Sym2.isDiag_map** 是 Mathlib 中的一个引理，位于命名空间 `Sym2`。
形式化陈述：isDiag_map (hf : Injective f) : (z.map f).IsDiag ↔ z.IsDiag
参数：hf : Injective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sym2.ind`：∀ {α : Type u_1} {f : Sym2 α → Prop}, (∀ (x y : α), f s(x, y))
 → ∀ (i : Sym2 α), f i
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
-/
lemma isDiag_map (hf : Injective f) : (z.map f).IsDiag ↔ z.IsDiag :=
  Sym2.ind (fun _ _ ↦ hf.eq_iff) z

@[simp]
/-
**Sym2.diag_isDiag** 是 Mathlib 中的一个定理，位于命名空间 `Sym2`。
形式化陈述：diag_isDiag (a : α) : IsDiag (diag a)
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem diag_isDiag (a : α) : IsDiag (diag a) :=
  Eq.refl a

@[simp, nontriviality]
/-
**Sym2.isDiag_of_subsingleton** 是 Mathlib 中的一个引理，位于命名空间 `Sym2`。
形式化陈述：isDiag_of_subsingleton [Subsingleton α] (z : Sym2 α) : z.IsDiag
参数：z : Sym2 α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sym2.ind`：∀ {α : Type u_1} {f : Sym2 α → Prop}, (∀ (x y : α), f s(x, y))
 → ∀ (i : Sym2 α), f i
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
lemma isDiag_of_subsingleton [Subsingleton α] (z : Sym2 α) : z.IsDiag := z.ind Subsingleton.elim

variable (z) in
/-- Computably extract the element when known to be diagonal. -/
/-
**Sym2.diagElem** 是 Mathlib 中的一个定义，位于命名空间 `Sym2`。
形式化陈述：diagElem : z.IsDiag -> α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Computably extract the element when known to be diagonal.
-/
def diagElem : z.IsDiag → α :=
  z.rec (fun a b _ => a) fun a b a' b' h => funext fun hx : a' = b' => by
    cases hx
    cases h <;> rfl

@[simp]
/-
**Sym2.diagElem_mk** 是 Mathlib 中的一个定理，位于命名空间 `Sym2`。
形式化陈述：diagElem_mk {a b : α} (h : IsDiag s(a, b)) : s(a, b).diagElem h = a
参数：h : IsDiag s(a, b)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem diagElem_mk {a b : α} (h : IsDiag s(a, b)) : s(a, b).diagElem h = a := rfl

@[simp]
/-
**Sym2.diag_diagElem** 是 Mathlib 中的一个定理，位于命名空间 `Sym2`。
形式化陈述：diag_diagElem (h : z.IsDiag) : diag (z.diagElem h) = z
参数：h : z.IsDiag。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sym2.ind`：∀ {α : Type u_1} {f : Sym2 α → Prop}, (∀ (x y : α), f s(x, y))
 → ∀ (i : Sym2 α), f i
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem diag_diagElem (h : z.IsDiag) : diag (z.diagElem h) = z := by
  cases z; cases h; rfl

/-- `Sym2.diagElem` and `Sym2.diag` as an equivalence. -/
@[simps]
/-
**Sym2.diagElemEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Sym2`。
形式化陈述：diagElemEquiv : { a : Sym2 α // a.IsDiag } ≃ α where toFun x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Sym2.diagElem` and `Sym2.diag` as an equivalence.
-/
def diagElemEquiv : { a : Sym2 α // a.IsDiag } ≃ α where
  toFun x := x.1.diagElem x.2
  invFun a := ⟨diag a, rfl⟩
  left_inv x := by ext; simp
  right_inv a := by simp [diag]

/-- The set of all `Sym2 α` elements on the diagonal. -/
/-
**Sym2.diagSet** 是 Mathlib 中的一个定义，位于命名空间 `Sym2`。
形式化陈述：diagSet : Set (Sym2 α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The set of all `Sym2 α` elements on the diagonal.
-/
def diagSet : Set (Sym2 α) := {z | z.IsDiag}
/-
**Sym2.mem_diagSet** 是 Mathlib 中的一个定理，位于命名空间 `Sym2`。
形式化陈述：∀ {α : Type u_1} {z : Sym2 α}, z ∈ Sym2.diagSet ↔ z.IsDiag
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma mem_diagSet : z ∈ diagSet ↔ z.IsDiag := .rfl
/-
**Sym2.range_diag** 是 Mathlib 中的一个定理，位于命名空间 `Sym2`。
形式化陈述：∀ {α : Type u_1}, Set.range Sym2.diag = Sym2.diagSet
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma range_diag : .range (diag : α → Sym2 α) = diagSet := by
  ext ⟨a, b⟩; simp [diag, eq_comm]
/-
**Sym2.diagSet_eq_setOfPred_isDiag** 是 Mathlib 中的一个定理，位于命名空间 `Sym2`。
形式化陈述：diagSet_eq_setOfPred_isDiag : diagSet = {z : Sym2 α | z.IsDiag}
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem diagSet_eq_setOfPred_isDiag : diagSet = {z : Sym2 α | z.IsDiag} := rfl

@[deprecated (since := "2026-07-09")]
alias diagSet_eq_setOf_isDiag := diagSet_eq_setOfPred_isDiag
/-
**Sym2.diagSet_eq_univ_of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Sym2`。
形式化陈述：diagSet_eq_univ_of_subsingleton [Subsingleton α] : @diagSet α = Set.univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem diagSet_eq_univ_of_subsingleton [Subsingleton α] : @diagSet α = Set.univ := by ext; simp
/-
**Sym2.IsDiag.decidablePred** 是 Mathlib 中的一个定义，位于命名空间 `Sym2.IsDiag`。
形式化陈述：(α : Type u) → [DecidableEq α] → DecidablePred Sym2.IsDiag
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Sym2.mk_isDiag_iff`：mk_isDiag_iff {x y : α} : IsDiag s(x, y) ↔ x = y
-/
instance IsDiag.decidablePred (α : Type u) [DecidableEq α] : DecidablePred (@IsDiag α) :=
  fun z => z.recOnSubsingleton fun _ _ => decidable_of_iff' _ mk_isDiag_iff
/-
**Sym2.decidablePred_mem_diagSet** 是 Mathlib 中的一个实例，位于命名空间 `Sym2`。
形式化陈述：decidablePred_mem_diagSet (α : Type u) [DecidableEq α] : DecidablePred (· 
in @diagSet α)
参数：α : Type u。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance decidablePred_mem_diagSet (α : Type u) [DecidableEq α] : DecidablePred (· ∈ @diagSet α) :=
  IsDiag.decidablePred _
/-
**Sym2.other_ne** 是 Mathlib 中的一个定理，位于命名空间 `Sym2`。
形式化陈述：other_ne {a : α} {z : Sym2 α} (hd : ¬IsDiag z) (h : a in z) : Mem.other h 
!= a
参数：hd : ¬IsDiag z；h : a in z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `Sym2.other_spec`：other_spec {a : α} {z : Sym2 α} (h : a in z) : s(a, Mem
.other h) = z
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem other_ne {a : α} {z : Sym2 α} (hd : ¬IsDiag z) (h : a ∈ z) : Mem.other h ≠ a := by
  contrapose hd
  have h' := Sym2.other_spec h
  rw [hd] at h'
  rw [← h']
  simp

section Relations

/-! ### Declarations about symmetric relations -/


variable {r r₁ r₂ : α → α → Prop}

/-- Symmetric relations define a set on `Sym2 α` by taking all those pairs
of elements that are related.
-/
/-
**Sym2.fromRel** 是 Mathlib 中的一个定义，位于命名空间 `Sym2`。
形式化陈述：fromRel (sym : Std.Symm r) : Set (Sym2 α)
参数：sym : Std.Symm r。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Symmetric relations define a set on `Sym2 α` by taking all those pairs
of elements that are related.
-/
def fromRel (sym : Std.Symm r) : Set (Sym2 α) :=
  Set.ofPred <| lift ⟨r, fun _ _ ↦ propext ⟨symm, symm⟩⟩

@[simp]
/-
**Sym2.fromRel_prop** 是 Mathlib 中的一个定理，位于命名空间 `Sym2`。
形式化陈述：fromRel_prop {sym : Std.Symm r} {a b : α} : s(a, b) in fromRel sym ↔ r a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem fromRel_prop {sym : Std.Symm r} {a b : α} : s(a, b) ∈ fromRel sym ↔ r a b :=
  Iff.rfl

@[deprecated (since := "2026-02-05")] alias fromRel_proj_prop := fromRel_prop
/-
**Sym2.fromRel_mono_iff** 是 Mathlib 中的一个定理，位于命名空间 `Sym2`。
形式化陈述：fromRel_mono_iff (sym₁ : Std.Symm r₁) (sym₂ : Std.Symm r₂) : fromRel sym₁ 
subseteq fromRel sym₂ ↔ r₁ <= r₂
参数：sym₁ : Std.Symm r₁；sym₂ : Std.Symm r₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sym2.ind`：∀ {α : Type u_1} {f : Sym2 α → Prop}, (∀ (x y : α), f s(x, y))
 → ∀ (i : Sym2 α), f i
-/
theorem fromRel_mono_iff (sym₁ : Std.Symm r₁) (sym₂ : Std.Symm r₂) :
    fromRel sym₁ ⊆ fromRel sym₂ ↔ r₁ ≤ r₂ :=
  ⟨fun hle a b ↦ @hle s(a, b), fun hle ↦ Sym2.ind hle⟩

@[gcongr]
alias ⟨_, fromRel_mono⟩ := fromRel_mono_iff
/-
**Sym2.mem_fromRel_comap** 是 Mathlib 中的一个定理，位于命名空间 `Sym2`。
形式化陈述：mem_fromRel_comap {r : β -> β -> Prop} (sym : Std.Symm r) (f : α -> β) (z 
: Sym2 α) : z in fromRel (sym.comap f) ↔ z.map f in fromRel sym
参数：sym : Std.Symm r；f : α -> β；z : Sym2 α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sym2.ind`：∀ {α : Type u_1} {f : Sym2 α → Prop}, (∀ (x y : α), f s(x, y))
 → ∀ (i : Sym2 α), f i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem mem_fromRel_comap {r : β → β → Prop} (sym : Std.Symm r) (f : α → β) (z : Sym2 α) :
    z ∈ fromRel (sym.comap f) ↔ z.map f ∈ fromRel sym := by
  cases z
  simp

set_option backward.isDefEq.respectTransparency false in
/-
**Sym2.fromRel_bot** 是 Mathlib 中的一个定理，位于命名空间 `Sym2`。
形式化陈述：fromRel_bot : fromRel (α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_of_forall_notMem`：eq_empty_of_forall_notMem (h : forall x, 
x ∉ s) : s = ∅
· 使用定理 `Pi.instSymmBotForallForallProp`：∀ (α : Type u_4), Std.Symm ⊥
· 使用定理 `Sym2.ind`：∀ {α : Type u_1} {f : Sym2 α → Prop}, (∀ (x y : α), f s(x, y))
 → ∀ (i : Sym2 α), f i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem fromRel_bot : fromRel (α := α) (r := ⊥) inferInstance = ∅ :=
  Set.eq_empty_of_forall_notMem <| Sym2.ind <| by simp

@[simp]
/-
**Sym2.fromRel_bot_iff** 是 Mathlib 中的一个定理，位于命名空间 `Sym2`。
形式化陈述：fromRel_bot_iff {sym : Std.Symm r} : fromRel sym = ∅ ↔ r = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `false_iff`：∀ (p : Prop), (False ↔ p) = ¬p
· 使用定理 `Sym2.fromRel_prop`：fromRel_prop {sym : Std.Symm r} {a b : α} : s(a, b) i
n fromRel sym ↔ r a b
· 使用定理 `Pi.instSymmBotForallForallProp`：∀ (α : Type u_4), Std.Symm ⊥
· 使用定理 `Sym2.fromRel_bot`：fromRel_bot : fromRel (α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem fromRel_bot_iff {sym : Std.Symm r} : fromRel sym = ∅ ↔ r = ⊥ := by
  refine ⟨fun h ↦ ?_, (· ▸ fromRel_bot)⟩
  ext x y
  simpa [h] using fromRel_prop (sym := sym)

set_option backward.isDefEq.respectTransparency false in
/-
**Sym2.fromRel_top** 是 Mathlib 中的一个定理，位于命名空间 `Sym2`。
形式化陈述：fromRel_top : fromRel (α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_univ_of_forall`：eq_univ_of_forall {s : Set α} : (forall x, x in s
) -> s = univ
· 使用定理 `Pi.instSymmTopForallForallProp`：∀ (α : Type u_4), Std.Symm ⊤
· 使用定理 `Sym2.ind`：∀ {α : Type u_1} {f : Sym2 α → Prop}, (∀ (x y : α), f s(x, y))
 → ∀ (i : Sym2 α), f i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem fromRel_top : fromRel (α := α) (r := ⊤) inferInstance = .univ :=
  Set.eq_univ_of_forall <| Sym2.ind <| by simp

@[simp]
/-
**Sym2.fromRel_top_iff** 是 Mathlib 中的一个定理，位于命名空间 `Sym2`。
形式化陈述：fromRel_top_iff {sym : Std.Symm r} : fromRel sym = .univ ↔ r = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `true_iff`：∀ (p : Prop), (True ↔ p) = p
· 使用定理 `Sym2.fromRel_prop`：fromRel_prop {sym : Std.Symm r} {a b : α} : s(a, b) i
n fromRel sym ↔ r a b
· 使用定理 `Pi.instSymmTopForallForallProp`：∀ (α : Type u_4), Std.Symm ⊤
· 使用定理 `Sym2.fromRel_top`：fromRel_top : fromRel (α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem fromRel_top_iff {sym : Std.Symm r} : fromRel sym = .univ ↔ r = ⊤ := by
  refine ⟨fun h ↦ ?_, (· ▸ fromRel_top)⟩
  ext x y
  simpa [h] using fromRel_prop (sym := sym)

set_option backward.isDefEq.respectTransparency false in
/-
**Sym2.fromRel_ne** 是 Mathlib 中的一个定理，位于命名空间 `Sym2`。
形式化陈述：fromRel_ne : fromRel (α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Function.instSymmSwapProp`：∀ {α : Sort u_1} (r : α → α → Prop) [Std.Symm
 r], Std.Symm (Function.swap r)
· 使用定理 `instSymmNe_mathlib`：∀ (α : Sort u_1), Std.Symm Ne
· 使用定理 `Sym2.ind`：∀ {α : Type u_1} {f : Sym2 α → Prop}, (∀ (x y : α), f s(x, y))
 → ∀ (i : Sym2 α), f i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem fromRel_ne : fromRel (α := α) (r := Ne) inferInstance = {z | ¬IsDiag z} := by
  ext z; exact z.ind (by simp)
/-
**Sym2.diagSet_eq_fromRel_eq** 是 Mathlib 中的一个引理，位于命名空间 `Sym2`。
形式化陈述：diagSet_eq_fromRel_eq : diagSet = fromRel (α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Equivalence.stdSymm`：Equivalence.stdSymm (h : Equivalence r) : Std.Symm 
r where symm _ _
· 使用定理 `eq_equivalence`：eq_equivalence {α : Sort*} : Equivalence (@Eq α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma diagSet_eq_fromRel_eq : diagSet = fromRel (α := α) eq_equivalence.stdSymm := by
  ext ⟨a, b⟩; simp

set_option backward.isDefEq.respectTransparency false in
/-
**Sym2.diagSet_compl_eq_fromRel_ne** 是 Mathlib 中的一个引理，位于命名空间 `Sym2`。
形式化陈述：diagSet_compl_eq_fromRel_ne : diagSetᶜ = fromRel (α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Function.instSymmSwapProp`：∀ {α : Sort u_1} (r : α → α → Prop) [Std.Symm
 r], Std.Symm (Function.swap r)
· 使用定理 `instSymmNe_mathlib`：∀ (α : Sort u_1), Std.Symm Ne
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma diagSet_compl_eq_fromRel_ne : diagSetᶜ = fromRel (α := α) (r := Ne) inferInstance := by
  ext ⟨a, b⟩; simp
/-
**Sym2.diagSet_subset_fromRel** 是 Mathlib 中的一个定理，位于命名空间 `Sym2`。
形式化陈述：∀ {α : Type u_1} {r : α → α → Prop} (hr : Std.Symm r), Sym2.diagSet ⊆ Sym2
.fromRel hr ↔ Std.Refl r
参数：hr : Std.Symm r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma diagSet_subset_fromRel (hr : Std.Symm r) : diagSet ⊆ fromRel hr ↔ Std.Refl r := by
  simp [Set.subset_def, Sym2.forall, refl_def]
/-
**Sym2.disjoint_diagSet_fromRel** 是 Mathlib 中的一个定理，位于命名空间 `Sym2`。
形式化陈述：∀ {α : Type u_1} {r : α → α → Prop} (hr : Std.Symm r), Disjoint Sym2.diagS
et (Sym2.fromRel hr) ↔ Std.Irrefl r
参数：hr : Std.Symm r；Sym2.fromRel hr。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma disjoint_diagSet_fromRel (hr : Std.Symm r) :
    Disjoint diagSet (fromRel hr) ↔ Std.Irrefl r := by
  simp [Set.disjoint_left, Sym2.forall, irrefl_def]
/-
**Sym2.fromRel_subset_compl_diagSet** 是 Mathlib 中的一个定理，位于命名空间 `Sym2`。
形式化陈述：∀ {α : Type u_1} {r : α → α → Prop} (hr : Std.Symm r), Sym2.fromRel hr ⊆ S
ym2.diagSetᶜ ↔ Std.Irrefl r
参数：hr : Std.Symm r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma fromRel_subset_compl_diagSet (hr : Std.Symm r) :
    fromRel hr ⊆ diagSetᶜ ↔ Std.Irrefl r := by simp [Set.subset_compl_iff_disjoint_left]
/-
**Sym2.fromRel_irrefl** 是 Mathlib 中的一个定理，位于命名空间 `Sym2`。
形式化陈述：fromRel_irrefl {sym : Std.Symm r} : Std.Irrefl r ↔ forall {z}, z in fromRe
l sym -> ¬IsDiag z where mp
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sym2.ind`：∀ {α : Type u_1} {f : Sym2 α → Prop}, (∀ (x y : α), f s(x, y))
 → ∀ (i : Sym2 α), f i
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Sym2.fromRel_prop`：fromRel_prop {sym : Std.Symm r} {a b : α} : s(a, b) i
n fromRel sym ↔ r a b
-/
theorem fromRel_irrefl {sym : Std.Symm r} : Std.Irrefl r ↔ ∀ {z}, z ∈ fromRel sym → ¬IsDiag z where
  mp := by intro ⟨h⟩; apply Sym2.ind; aesop
  mpr h := ⟨fun _ hr ↦ h (fromRel_prop.mpr hr) rfl⟩

@[deprecated (since := "2026-02-12")] alias fromRel_irreflexive := fromRel_irrefl
/-
**Sym2.mem_fromRel_irrefl_other_ne** 是 Mathlib 中的一个定理，位于命名空间 `Sym2`。
形式化陈述：mem_fromRel_irrefl_other_ne {sym : Std.Symm r} (irrefl : Std.Irrefl r) {a 
: α} {z : Sym2 α} (hz : z in fromRel sym) (h : a in z) : Mem.other h != a
参数：irrefl : Std.Irrefl r；hz : z in fromRel sym；h : a in z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sym2.other_ne`：other_ne {a : α} {z : Sym2 α} (hd : ¬IsDiag z) (h : a in 
z) : Mem.other h != a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Sym2.fromRel_irrefl`：fromRel_irrefl {sym : Std.Symm r} : Std.Irrefl r ↔ 
forall {z}, z in fromRel sym -> ¬IsDiag z where mp
-/
theorem mem_fromRel_irrefl_other_ne {sym : Std.Symm r} (irrefl : Std.Irrefl r) {a : α}
    {z : Sym2 α} (hz : z ∈ fromRel sym) (h : a ∈ z) : Mem.other h ≠ a :=
  other_ne (fromRel_irrefl.mp irrefl hz) h
/-
**Sym2.fromRel.decidablePred** 是 Mathlib 中的一个定义，位于命名空间 `Sym2.fromRel`。
形式化陈述：{α : Type u_1} →   {r : α → α → Prop} → (sym : Std.Symm r) → [h : Decidabl
eRel r] → DecidablePred fun x => x ∈ Sym2.fromRel sym
参数：sym : Std.Symm r。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance fromRel.decidablePred (sym : Std.Symm r) [h : DecidableRel r] :
    DecidablePred (· ∈ Sym2.fromRel sym) := fun z => z.recOnSubsingleton h
/-
**Sym2.fromRel_relationMap** 是 Mathlib 中的一个引理，位于命名空间 `Sym2`。
形式化陈述：fromRel_relationMap {r : α -> α -> Prop} (hr : Std.Symm r) (f : α -> β) : 
fromRel (hr.map f) = Sym2.map f '' Sym2.fromRel hr
参数：hr : Std.Symm r；f : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Std.Symm.map`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Prop} [Std.Sy
mm r] (f : α → β), Std.Symm (Relation.Map r f f)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `symm`：symm [Std.Symm r] : a ≺ b -> b ≺ a
-/
lemma fromRel_relationMap {r : α → α → Prop} (hr : Std.Symm r) (f : α → β) :
    fromRel (hr.map f) = Sym2.map f '' Sym2.fromRel hr := by
  ext ⟨a, b⟩
  simp only [fromRel_prop, Relation.Map, Set.mem_image, Sym2.exists, map_mk, Sym2.eq,
    rel_iff', Prod.mk.injEq, Prod.swap_prod_mk, and_or_left, exists_or, iff_self_or,
    forall_exists_index, and_imp]
  exact fun c d hcd hc hd ↦ ⟨d, c, symm hcd, hd, hc⟩

/-- Non-dependent recursor on members of a `fromRel` set -/
/-
**Sym2.fromRelNdrec** 是 Mathlib 中的一个定义，位于命名空间 `Sym2`。
形式化陈述：fromRelNdrec {motive : Sort*} {sym : Std.Symm r} (z : Sym2 α) (hz : z in f
romRel sym) (f : (a b : α) -> r a b -> motive) (h : forall (a b : α) (h : r a b)
, f a b h = f b a (symm h)) : motive
参数：z : Sym2 α；hz : z in fromRel sym；f : (a b : α) -> r a b -> motive；h : forall 
(a b : α) (h : r a b), f a b h = f b a (symm h)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `symm`：symm [Std.Symm r] : a ≺ b -> b ≺ a

--- 原说明 ---
Non-dependent recursor on members of a `fromRel` set
-/
def fromRelNdrec {motive : Sort*} {sym : Std.Symm r} (z : Sym2 α) (hz : z ∈ fromRel sym)
    (f : (a b : α) → r a b → motive) (h : ∀ (a b : α) (h : r a b), f a b h = f b a (symm h)) :
    motive :=
  z.hrec f (fun _ _ ↦ Function.hfunext (sym.iff .. |>.eq) fun _ _ _ ↦ heq_of_eq <| h ..) hz

@[simp]
/-
**Sym2.fromRelNdrec_mk** 是 Mathlib 中的一个定理，位于命名空间 `Sym2`。
形式化陈述：fromRelNdrec_mk {motive : Sort*} {sym : Std.Symm r} {a b : α} (hz : r a b)
 (f : (a b : α) -> r a b -> motive) (h : forall (a b : α) (h : r a b), f a b h =
 f b a (symm h)) : fromRelNdrec (sym
参数：hz : r a b；f : (a b : α) -> r a b -> motive；h : forall (a b : α) (h : r a b),
 f a b h = f b a (symm h)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `symm`：symm [Std.Symm r] : a ≺ b -> b ≺ a
-/
theorem fromRelNdrec_mk {motive : Sort*} {sym : Std.Symm r} {a b : α} (hz : r a b)
    (f : (a b : α) → r a b → motive) (h : ∀ (a b : α) (h : r a b), f a b h = f b a (symm h)) :
    fromRelNdrec (sym := sym) s(a, b) hz f h = f a b hz :=
  rfl

/-- The `fromRel` set of a symmetric relation `r` is equivalent to summing that set restricted to
fibers of a function `f`, given that `f` agrees on elements related by `r`. -/
@[simps]
/-
**Sym2._root_.Equiv.sigmaFiberFromRel** 是 Mathlib 中的一个定义，位于命名空间 `Sym2`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `fromRel` set of a symmetric relation `r` is equivalent to summing that set 
restricted to
fibers of a function `f`, given that `f` agrees on elements related by `r`.
-/
def _root_.Equiv.sigmaFiberFromRel (sym : Std.Symm r) {f : α → β} (hf : r ≤ Setoid.ker f) :
    fromRel sym ≃ Σ b : β, fromRel (α := { a // f a = b }) <| sym.comap (↑) where
  toFun z := z.val.fromRelNdrec z.prop
    (fun a₁ a₂ h ↦ ⟨f a₁, s(⟨a₁, rfl⟩, ⟨a₂, hf a₁ a₂ h |>.symm⟩), h⟩)
    fun a₁ a₂ h ↦ by
      rw! [hf a₁ a₂ h, eq_swap]
      rfl
  invFun z := ⟨z.snd.val.map (↑), mem_fromRel_comap sym .. |>.mp z.snd.prop⟩
  left_inv z := by
    rcases z with ⟨⟨a₁, a₂⟩, h⟩
    rfl
  right_inv z := by
    rcases z with ⟨b, ⟨⟨a₁, rfl⟩, ⟨a₂, ha₂⟩⟩, h⟩
    rfl

/-- For a relation homomorphism `r →r r'` where `r` is symmetric, the `fromRel` set of `r` is
equivalent to summing that set restricted to equivalence classes of `r'` using a `Subtype`,
`Quot` version -/
@[simps!]
/-
**Sym2._root_.Equiv.sigmaQuotFromRel** 是 Mathlib 中的一个定义，位于命名空间 `Sym2`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For a relation homomorphism `r →r r'` where `r` is symmetric, the `fromRel` set 
of `r` is
equivalent to summing that set restricted to equivalence classes of `r'` using a
 `Subtype`,
`Quot` version
-/
def _root_.Equiv.sigmaQuotFromRel (sym : Std.Symm r) {r' : β → β → Prop} (f : r →r r') :
    fromRel sym ≃ Σ q : Quot r', fromRel (α := { x // .mk r' (f x) = q }) <| sym.comap (↑) :=
  .sigmaFiberFromRel sym fun _ _ h ↦ Quot.sound <| f.map_rel h

/-- For a relation homomorphism `r →r r'` where `r` is symmetric, the `fromRel` set of `r` is
equivalent to summing that set restricted to equivalence classes of `r'` using a `Subtype`,
`Quotient` version -/
@[simps!]
/-
**Sym2._root_.Equiv.sigmaQuotientFromRel** 是 Mathlib 中的一个定义，位于命名空间 `Sym2`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For a relation homomorphism `r →r r'` where `r` is symmetric, the `fromRel` set 
of `r` is
equivalent to summing that set restricted to equivalence classes of `r'` using a
 `Subtype`,
`Quotient` version
-/
def _root_.Equiv.sigmaQuotientFromRel (sym : Std.Symm r) {r' : Setoid β} (f : r →r r') :
    fromRel sym ≃ Σ q : Quotient r', fromRel (α := { x // ⟦f x⟧ = q }) <| sym.comap (↑) :=
  .sigmaFiberFromRel sym fun _ _ h ↦ Quotient.sound <| f.map_rel h

/-- The inverse to `Sym2.fromRel`. Given a set on `Sym2 α`, give a symmetric relation on `α`
(see `Sym2.toRel_symm`). -/
/-
**Sym2.ToRel** 是 Mathlib 中的一个定义，位于命名空间 `Sym2`。
形式化陈述：ToRel (s : Set (Sym2 α)) (x y : α) : Prop
参数：s : Set (Sym2 α)；x y : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inverse to `Sym2.fromRel`. Given a set on `Sym2 α`, give a symmetric relatio
n on `α`
(see `Sym2.toRel_symm`).
-/
def ToRel (s : Set (Sym2 α)) (x y : α) : Prop :=
  s(x, y) ∈ s

@[simp]
/-
**Sym2.toRel_prop** 是 Mathlib 中的一个定理，位于命名空间 `Sym2`。
形式化陈述：toRel_prop (s : Set (Sym2 α)) (x y : α) : ToRel s x y ↔ s(x, y) in s
参数：s : Set (Sym2 α)；x y : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem toRel_prop (s : Set (Sym2 α)) (x y : α) : ToRel s x y ↔ s(x, y) ∈ s :=
  Iff.rfl
/-
**Sym2.toRel_symm** 是 Mathlib 中的一个实例，位于命名空间 `Sym2`。
形式化陈述：toRel_symm (s : Set (Sym2 α)) : Std.Symm (ToRel s) where symm x y
参数：s : Set (Sym2 α)。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Sym2.eq_swap`：eq_swap {a b : α} : s(a, b) = s(b, a)
-/
instance toRel_symm (s : Set (Sym2 α)) : Std.Symm (ToRel s) where
  symm x y := by simp [eq_swap]

@[deprecated (since := "2026-06-10")] alias toRel_symmetric := toRel_symm
/-
**Sym2.toRel_fromRel** 是 Mathlib 中的一个定理，位于命名空间 `Sym2`。
形式化陈述：toRel_fromRel (sym : Std.Symm r) : ToRel (fromRel sym) = r
参数：sym : Std.Symm r。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toRel_fromRel (sym : Std.Symm r) : ToRel (fromRel sym) = r :=
  rfl
/-
**Sym2.fromRel_toRel** 是 Mathlib 中的一个定理，位于命名空间 `Sym2`。
形式化陈述：fromRel_toRel (s : Set (Sym2 α)) : fromRel (toRel_symm s) = s
参数：s : Set (Sym2 α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Sym2.ind`：∀ {α : Type u_1} {f : Sym2 α → Prop}, (∀ (x y : α), f s(x, y))
 → ∀ (i : Sym2 α), f i
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem fromRel_toRel (s : Set (Sym2 α)) : fromRel (toRel_symm s) = s :=
  Set.ext fun z => Sym2.ind (fun _ _ => Iff.rfl) z
/-
**Sym2.toRel_mono_iff** 是 Mathlib 中的一个定理，位于命名空间 `Sym2`。
形式化陈述：toRel_mono_iff (s₁ s₂ : Set (Sym2 α)) : ToRel s₁ <= ToRel s₂ ↔ s₁ subseteq
 s₂
参数：s₁ s₂ : Set (Sym2 α)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sym2.ind`：∀ {α : Type u_1} {f : Sym2 α → Prop}, (∀ (x y : α), f s(x, y))
 → ∀ (i : Sym2 α), f i
-/
theorem toRel_mono_iff (s₁ s₂ : Set (Sym2 α)) : ToRel s₁ ≤ ToRel s₂ ↔ s₁ ⊆ s₂ :=
  ⟨(Sym2.ind ·), (@· s(·, ·))⟩

@[gcongr]
alias ⟨_, toRel_mono⟩ := toRel_mono_iff

variable (α) in
/-- `ToRel` induces an order embedding from `Sym2` sets to relations -/
/-
**Sym2.toRelOrderEmbedding** 是 Mathlib 中的一个定义，位于命名空间 `Sym2`。
形式化陈述：toRelOrderEmbedding : Set (Sym2 α) ↪o (α -> α -> Prop)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Sym2.toRel_mono_iff`：toRel_mono_iff (s₁ s₂ : Set (Sym2 α)) : ToRel s₁ <=
 ToRel s₂ ↔ s₁ subseteq s₂

--- 原说明 ---
`ToRel` induces an order embedding from `Sym2` sets to relations
-/
def toRelOrderEmbedding : Set (Sym2 α) ↪o (α → α → Prop) :=
  .ofMapLEIff ToRel toRel_mono_iff

set_option backward.isDefEq.respectTransparency false in
variable (α) in
/-- `fromRel`/`ToRel` induce an order isomorphism between symmetric relations and `Sym2` sets -/
@[simps]
/-
**Sym2.fromRelOrderIso** 是 Mathlib 中的一个定义，位于命名空间 `Sym2`。
形式化陈述：fromRelOrderIso : { r : α -> α -> Prop // Std.Symm r } ≃o Set (Sym2 α) whe
re toFun r
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`fromRel`/`ToRel` induce an order isomorphism between symmetric relations and `S
ym2` sets
-/
def fromRelOrderIso : { r : α → α → Prop // Std.Symm r } ≃o Set (Sym2 α) where
  toFun r := fromRel r.prop
  invFun s := ⟨ToRel s, toRel_symm s⟩
  left_inv r := by simp [toRel_fromRel]
  right_inv s := by simp [fromRel_toRel]
  map_rel_iff' {r₁ r₂} := by simpa using! fromRel_mono_iff ..

/-- `fromRel` induces an order embedding from symmetric relations to `Sym2` sets. -/
@[deprecated fromRelOrderIso (since := "2026-03-11")]
/-
**Sym2.fromRelOrderEmbedding** 是 Mathlib 中的一个定义，位于命名空间 `Sym2`。
形式化陈述：fromRelOrderEmbedding : { r : α -> α -> Prop // Std.Symm r } ↪o Set (Sym2 
α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`fromRel` induces an order embedding from symmetric relations to `Sym2` sets.
-/
def fromRelOrderEmbedding : { r : α → α → Prop // Std.Symm r } ↪o Set (Sym2 α) :=
  fromRelOrderIso α |>.toOrderEmbedding

@[simp]
/-
**Sym2.fromRel_eq_fromRel_iff_eq** 是 Mathlib 中的一个定理，位于命名空间 `Sym2`。
形式化陈述：fromRel_eq_fromRel_iff_eq {r₁ r₂ : α -> α -> Prop} (sym₁ : Std.Symm r₁) (s
ym₂ : Std.Symm r₂) : fromRel sym₁ = fromRel sym₂ ↔ r₁ = r₂
参数：sym₁ : Std.Symm r₁；sym₂ : Std.Symm r₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `RelIso.eq_iff_eq`：eq_iff_eq (f : r ≃r s) {a b} : f a = f b ↔ a = b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem fromRel_eq_fromRel_iff_eq {r₁ r₂ : α → α → Prop} (sym₁ : Std.Symm r₁) (sym₂ : Std.Symm r₂) :
    fromRel sym₁ = fromRel sym₂ ↔ r₁ = r₂ := by
  rw [← Subtype.mk.injEq r₁ sym₁ r₂ sym₂, ← fromRelOrderIso α |>.eq_iff_eq]
  rfl

@[deprecated (since := "2026-03-11")] alias fromRel_eq_fromRell_iff_eq := fromRel_eq_fromRel_iff_eq

end Relations

section ToMultiset

/-- Map an unordered pair to an unordered list. -/
/-
**Sym2.toMultiset** 是 Mathlib 中的一个定义，位于命名空间 `Sym2`。
形式化陈述：toMultiset {α : Type*} (z : Sym2 α) : Multiset α
参数：z : Sym2 α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Map an unordered pair to an unordered list.
-/
def toMultiset {α : Type*} (z : Sym2 α) : Multiset α := by
  refine Sym2.lift ?_ z
  use (Multiset.ofList [·, ·])
  simp [List.Perm.swap]

/-- Mapping an unordered pair to an unordered list produces a multiset of size `2`. -/
/-
**Sym2.card_toMultiset** 是 Mathlib 中的一个引理，位于命名空间 `Sym2`。
形式化陈述：card_toMultiset {α : Type*} (z : Sym2 α) : z.toMultiset.card = 2
参数：z : Sym2 α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sym2.ind`：∀ {α : Type u_1} {f : Sym2 α → Prop}, (∀ (x y : α), f s(x, y))
 → ∀ (i : Sym2 α), f i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Mapping an unordered pair to an unordered list produces a multiset of size `2`.
-/
lemma card_toMultiset {α : Type*} (z : Sym2 α) : z.toMultiset.card = 2 := by
  induction z
  simp [Sym2.toMultiset]

/-- The members of an unordered pair are members of the corresponding unordered list. -/
@[simp]
/-
**Sym2.mem_toMultiset** 是 Mathlib 中的一个定理，位于命名空间 `Sym2`。
形式化陈述：mem_toMultiset {α : Type*} {x : α} {z : Sym2 α} : x in (z.toMultiset : Mul
tiset α) ↔ x in z
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sym2.ind`：∀ {α : Type u_1} {f : Sym2 α → Prop}, (∀ (x y : α), f s(x, y))
 → ∀ (i : Sym2 α), f i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
The members of an unordered pair are members of the corresponding unordered list
.
-/
theorem mem_toMultiset {α : Type*} {x : α} {z : Sym2 α} :
    x ∈ (z.toMultiset : Multiset α) ↔ x ∈ z := by
  induction z
  simp [Sym2.toMultiset]

end ToMultiset

section ToFinset

variable [DecidableEq α]

/-- Map an unordered pair to a finite set. -/
/-
**Sym2.toFinset** 是 Mathlib 中的一个定义，位于命名空间 `Sym2`。
形式化陈述：toFinset (z : Sym2 α) : Finset α
参数：z : Sym2 α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Map an unordered pair to a finite set.
-/
def toFinset (z : Sym2 α) : Finset α := (z.toMultiset : Multiset α).toFinset

/-- The members of an unordered pair are members of the corresponding finite set. -/
@[simp]
/-
**Sym2.mem_toFinset** 是 Mathlib 中的一个定理，位于命名空间 `Sym2`。
形式化陈述：mem_toFinset {x : α} {z : Sym2 α} : x in z.toFinset ↔ x in z
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Sym2.mem_toMultiset`：mem_toMultiset {α : Type*} {x : α} {z : Sym2 α} : x
 in (z.toMultiset : Multiset α) ↔ x in z
· 使用定理 `Sym2.toFinset.eq_1`：∀ {α : Type u_1} [inst : DecidableEq α] (z : Sym2 α)
, z.toFinset = z.toMultiset.toFinset
· 使用定理 `Multiset.mem_toFinset`：mem_toFinset {a : α} {s : Multiset α} : a in s.to
Finset ↔ a in s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
The members of an unordered pair are members of the corresponding finite set.
-/
theorem mem_toFinset {x : α} {z : Sym2 α} : x ∈ z.toFinset ↔ x ∈ z := by
  rw [← Sym2.mem_toMultiset, Sym2.toFinset, Multiset.mem_toFinset]

@[simp]
/-
**Sym2.toFinset_ne_empty** 是 Mathlib 中的一个定理，位于命名空间 `Sym2`。
形式化陈述：toFinset_ne_empty (z : Sym2 α) : z.toFinset != ∅
参数：z : Sym2 α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ne_empty_of_mem`：ne_empty_of_mem {a : α} {s : Finset α} (h : a in
 s) : s != ∅
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Sym2.mem_toFinset`：mem_toFinset {x : α} {z : Sym2 α} : x in z.toFinset ↔
 x in z
· 使用定理 `Sym2.out_fst_mem`：out_fst_mem (e : Sym2 α) : e.out.1 in e
-/
theorem toFinset_ne_empty (z : Sym2 α) : z.toFinset ≠ ∅ := by
  exact Finset.ne_empty_of_mem (Sym2.mem_toFinset.mpr (Sym2.out_fst_mem _))
/-
**Sym2.toFinset_mk_eq** 是 Mathlib 中的一个引理，位于命名空间 `Sym2`。
形式化陈述：toFinset_mk_eq {x y : α} : s(x, y).toFinset = {x, y}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma toFinset_mk_eq {x y : α} : s(x, y).toFinset = {x, y} := by
  ext; simp [← Sym2.mem_toFinset, ← Sym2.mem_iff]

/-- Mapping an unordered pair on the diagonal to a finite set produces a finset of size `1`. -/
/-
**Sym2.card_toFinset_of_isDiag** 是 Mathlib 中的一个定理，位于命名空间 `Sym2`。
形式化陈述：card_toFinset_of_isDiag (z : Sym2 α) (h : z.IsDiag) : #(z : Sym2 α).toFins
et = 1
参数：z : Sym2 α；h : z.IsDiag。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sym2.ind`：∀ {α : Type u_1} {f : Sym2 α → Prop}, (∀ (x y : α), f s(x, y))
 → ∀ (i : Sym2 α), f i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Sym2.mk_isDiag_iff`：mk_isDiag_iff {x y : α} : IsDiag s(x, y) ↔ x = y
· 使用引理 `Sym2.toFinset_mk_eq`：toFinset_mk_eq {x y : α} : s(x, y).toFinset = {x, y
}
· 使用定理 `Finset.insert_eq_of_mem`：insert_eq_of_mem (h : a in s) : insert a s = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1

--- 原说明 ---
Mapping an unordered pair on the diagonal to a finite set produces a finset of s
ize `1`.
-/
theorem card_toFinset_of_isDiag (z : Sym2 α) (h : z.IsDiag) : #(z : Sym2 α).toFinset = 1 := by
  induction z
  rw [Sym2.mk_isDiag_iff] at h
  simp [Sym2.toFinset_mk_eq, h]

/-- Mapping an unordered pair off the diagonal to a finite set produces a finset of size `2`. -/
/-
**Sym2.card_toFinset_of_not_isDiag** 是 Mathlib 中的一个定理，位于命名空间 `Sym2`。
形式化陈述：card_toFinset_of_not_isDiag (z : Sym2 α) (h : ¬z.IsDiag) : #(z : Sym2 α).t
oFinset = 2
参数：z : Sym2 α；h : ¬z.IsDiag。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sym2.ind`：∀ {α : Type u_1} {f : Sym2 α → Prop}, (∀ (x y : α), f s(x, y))
 → ∀ (i : Sym2 α), f i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Sym2.toFinset_mk_eq`：toFinset_mk_eq {x y : α} : s(x, y).toFinset = {x, y
}
· 使用定理 `Finset.card_insert_of_notMem`：card_insert_of_notMem (h : a ∉ s) : #(inse
rt a s) = #s + 1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Sym2.mk_isDiag_iff`：mk_isDiag_iff {x y : α} : IsDiag s(x, y) ↔ x = y
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Mapping an unordered pair off the diagonal to a finite set produces a finset of 
size `2`.
-/
theorem card_toFinset_of_not_isDiag (z : Sym2 α) (h : ¬z.IsDiag) : #(z : Sym2 α).toFinset = 2 := by
  induction z
  rw [Sym2.mk_isDiag_iff] at h
  simp [Sym2.toFinset_mk_eq, h]

/-- Mapping an unordered pair to a finite set produces a finset of size `1` if the pair is on the
diagonal, else of size `2` if the pair is off the diagonal. -/
/-
**Sym2.card_toFinset** 是 Mathlib 中的一个定理，位于命名空间 `Sym2`。
形式化陈述：card_toFinset (z : Sym2 α) : #(z : Sym2 α).toFinset = if z.IsDiag then 1 e
lse 2
参数：z : Sym2 α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Sym2.card_toFinset_of_isDiag`：card_toFinset_of_isDiag (z : Sym2 α) (h : 
z.IsDiag) : #(z : Sym2 α).toFinset = 1
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Sym2.card_toFinset_of_not_isDiag`：card_toFinset_of_not_isDiag (z : Sym2 
α) (h : ¬z.IsDiag) : #(z : Sym2 α).toFinset = 2
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False

--- 原说明 ---
Mapping an unordered pair to a finite set produces a finset of size `1` if the p
air is on the
diagonal, else of size `2` if the pair is off the diagonal.
-/
theorem card_toFinset (z : Sym2 α) : #(z : Sym2 α).toFinset = if z.IsDiag then 1 else 2 := by
  by_cases h : z.IsDiag
  · simp [card_toFinset_of_isDiag z h, h]
  · simp [card_toFinset_of_not_isDiag z h, h]

end ToFinset

section SymEquiv

/-! ### Equivalence to the second symmetric power -/


attribute [local instance] List.Vector.Perm.isSetoid

set_option backward.privateInPublic true in
/-
**Sym2.fromVector** 是 Mathlib 中的一个定义，位于命名空间 `Sym2`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Equivalence to the second symmetric power
-/
private def fromVector : List.Vector α 2 → α × α
  | ⟨[a, b], _⟩ => (a, b)
/-
**Sym2.perm_card_two_iff** 是 Mathlib 中的一个定理，位于命名空间 `Sym2`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem perm_card_two_iff {a₁ b₁ a₂ b₂ : α} :
    [a₁, b₁].Perm [a₂, b₂] ↔ a₁ = a₂ ∧ b₁ = b₂ ∨ a₁ = b₂ ∧ b₁ = a₂ :=
  { mp := by
      simp only [← Multiset.coe_eq_coe, ← Multiset.cons_coe, Multiset.coe_nil, Multiset.cons_zero,
        Multiset.cons_eq_cons, Multiset.singleton_inj, ne_eq, Multiset.singleton_eq_cons_iff,
        exists_eq_right_right, and_true]
      tauto
    mpr := fun
        | .inl ⟨h₁, h₂⟩ | .inr ⟨h₁, h₂⟩ => by
          rw [h₁, h₂]
          first | done | constructor }

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The symmetric square is equivalent to length-2 vectors up to permutations. -/
/-
**Sym2.sym2EquivSym'** 是 Mathlib 中的一个定义，位于命名空间 `Sym2`。
形式化陈述：sym2EquivSym' : Equiv (Sym2 α) (Sym' α 2) where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The symmetric square is equivalent to length-2 vectors up to permutations.
-/
def sym2EquivSym' : Equiv (Sym2 α) (Sym' α 2) where
  toFun :=
    Quot.map (fun x : α × α => ⟨[x.1, x.2], rfl⟩)
      (by
        rintro _ _ ⟨_⟩
        · constructor; apply List.Perm.refl
        apply List.Perm.swap'
        rfl)
  invFun :=
    Quot.map fromVector
      (by
        rintro ⟨x, hx⟩ ⟨y, hy⟩ h
        rcases x with - | ⟨_, x⟩; · simp at hx
        rcases x with - | ⟨_, x⟩; · simp at hx
        rcases x with - | ⟨_, x⟩; swap
        · exfalso
          simp at hx
        rcases y with - | ⟨_, y⟩; · simp at hy
        rcases y with - | ⟨_, y⟩; · simp at hy
        rcases y with - | ⟨_, y⟩; swap
        · exfalso
          simp at hy
        rcases perm_card_two_iff.mp h with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
        · constructor
        apply Sym2.Rel.swap)
  left_inv := by apply Sym2.ind; aesop (add norm unfold [Sym2.fromVector])
  right_inv x := by
    refine x.recOnSubsingleton fun x => ?_
    obtain ⟨x, hx⟩ := x
    obtain - | ⟨-, x⟩ := x
    · simp at hx
    rcases x with - | ⟨_, x⟩
    · simp at hx
    rcases x with - | ⟨_, x⟩
    swap
    · exfalso
      simp at hx
    rfl

/-- The symmetric square is equivalent to the second symmetric power. -/
/-
**Sym2.equivSym** 是 Mathlib 中的一个定义，位于命名空间 `Sym2`。
形式化陈述：equivSym (α : Type*) : Sym2 α ≃ Sym α 2
参数：α : Type*。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The symmetric square is equivalent to the second symmetric power.
-/
def equivSym (α : Type*) : Sym2 α ≃ Sym α 2 :=
  Equiv.trans sym2EquivSym' symEquivSym'.symm

/-- The symmetric square is equivalent to multisets of cardinality
two. (This is currently a synonym for `equivSym`, but it's provided
in case the definition for `Sym` changes.) -/
/-
**Sym2.equivMultiset** 是 Mathlib 中的一个定义，位于命名空间 `Sym2`。
形式化陈述：equivMultiset (α : Type*) : Sym2 α ≃ { s : Multiset α // Multiset.card s =
 2 }
参数：α : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The symmetric square is equivalent to multisets of cardinality
two. (This is currently a synonym for `equivSym`, but it's provided
in case the definition for `Sym` changes.)
-/
def equivMultiset (α : Type*) : Sym2 α ≃ { s : Multiset α // Multiset.card s = 2 } :=
  equivSym α

end SymEquiv

section Decidable

/-- Given `[DecidableEq α]` and `[Fintype α]`, the following instance gives `Fintype (Sym2 α)`.
-/
/-
**Sym2.instDecidableRel** 是 Mathlib 中的一个实例，位于命名空间 `Sym2`。
形式化陈述：instDecidableRel [DecidableEq α] : DecidableRel (Rel α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `[DecidableEq α]` and `[Fintype α]`, the following instance gives `Fintype
 (Sym2 α)`.
-/
instance instDecidableRel [DecidableEq α] : DecidableRel (Rel α) :=
  fun _ _ => decidable_of_iff' _ rel_iff

section
attribute [local instance] Sym2.Rel.setoid

/-
**Sym2.instDecidableRel'** 是 Mathlib 中的一个实例，位于命名空间 `Sym2`。
形式化陈述：instDecidableRel' [DecidableEq α] : DecidableRel (HasEquiv.Equiv (α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instDecidableRel' [DecidableEq α] : DecidableRel (HasEquiv.Equiv (α := α × α)) :=
  instDecidableRel

end

/-
**Sym2.** 是 Mathlib 中的一个实例，位于命名空间 `Sym2`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DecidableEq α] : DecidableEq (Sym2 α) :=
  inferInstanceAs <| DecidableEq (Quotient (Sym2.Rel.setoid α))

/-! ### The other element of an element of the symmetric square -/

/-- Get the other element of the unordered pair using the decidable equality.
This is the computable version of `Mem.other`. -/
@[aesop norm unfold (rule_sets := [Sym2])]
/-
**Sym2.Mem.other'** 是 Mathlib 中的一个定义，位于命名空间 `Sym2.Mem`。
形式化陈述：{α : Type u_1} → [DecidableEq α] → {a : α} → {z : Sym2 α} → a ∈ z → α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Get the other element of the unordered pair using the decidable equality.
This is the computable version of `Mem.other`.
-/
def Mem.other' [DecidableEq α] {a : α} {z : Sym2 α} (h : a ∈ z) : α :=
  Sym2.rec (fun b c _ => if a = b then c else b) (by
    clear h z
    intro b c d e h
    ext hy
    have {f g h} : @Eq.ndrec (Sym2 α) s(b, c)
      (fun x => a ∈ x → α) (fun _ => if a = b then c else b) f g h =
        if a = b then c else b := by subst g; rfl
    aesop)
    z h

@[simp]
/-
**Sym2.other_spec'** 是 Mathlib 中的一个定理，位于命名空间 `Sym2`。
形式化陈述：other_spec' [DecidableEq α] {a : α} {z : Sym2 α} (h : a in z) : s(a, Mem.o
ther' h) = z
参数：h : a in z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sym2.ind`：∀ {α : Type u_1} {f : Sym2 α → Prop}, (∀ (x y : α), f s(x, y))
 → ∀ (i : Sym2 α), f i
· 使用定理 `Quot.indepCoherent`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r →
 Sort v} (f : (a : α) → motive (Quot.mk r a)),   (∀ (a b : α) (p : r a b), ⋯ ▸ f
 a = f b…
· 使用定理 `Quot.liftIndepPr1`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → 
Sort v} (f : (a : α) → motive (Quot.mk r a))   (h : ∀ (a b : α) (p : r a b), ⋯ ▸
 f a = …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
-/
theorem other_spec' [DecidableEq α] {a : α} {z : Sym2 α} (h : a ∈ z) : s(a, Mem.other' h) = z := by
  induction z
  aesop (add norm unfold [Sym2.rec, Quot.rec]) (rule_sets := [Sym2])

@[simp]
/-
**Sym2.other_eq_other'** 是 Mathlib 中的一个定理，位于命名空间 `Sym2`。
形式化陈述：other_eq_other' [DecidableEq α] {a : α} {z : Sym2 α} (h : a in z) : Mem.ot
her h = Mem.other' h
参数：h : a in z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Sym2.congr_right`：congr_right {a b c : α} : s(a, b) = s(a, c) ↔ b = c
· 使用定理 `Sym2.other_spec'`：other_spec' [DecidableEq α] {a : α} {z : Sym2 α} (h : 
a in z) : s(a, Mem.other' h) = z
· 使用定理 `Sym2.other_spec`：other_spec {a : α} {z : Sym2 α} (h : a in z) : s(a, Mem
.other h) = z
-/
theorem other_eq_other' [DecidableEq α] {a : α} {z : Sym2 α} (h : a ∈ z) :
    Mem.other h = Mem.other' h := by rw [← congr_right, other_spec' h, other_spec]
/-
**Sym2.other_mem'** 是 Mathlib 中的一个定理，位于命名空间 `Sym2`。
形式化陈述：other_mem' [DecidableEq α] {a : α} {z : Sym2 α} (h : a in z) : Mem.other' 
h in z
参数：h : a in z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Sym2.other_eq_other'`：other_eq_other' [DecidableEq α] {a : α} {z : Sym2 
α} (h : a in z) : Mem.other h = Mem.other' h
· 使用定理 `Sym2.other_mem`：other_mem {a : α} {z : Sym2 α} (h : a in z) : Mem.other 
h in z
-/
theorem other_mem' [DecidableEq α] {a : α} {z : Sym2 α} (h : a ∈ z) : Mem.other' h ∈ z := by
  rw [← other_eq_other']
  exact other_mem h
/-
**Sym2.other_invol'** 是 Mathlib 中的一个定理，位于命名空间 `Sym2`。
形式化陈述：other_invol' [DecidableEq α] {a : α} {z : Sym2 α} (ha : a in z) (hb : Mem.
other' ha in z) : Mem.other' hb = a
参数：ha : a in z；hb : Mem.other' ha in z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sym2.ind`：∀ {α : Type u_1} {f : Sym2 α → Prop}, (∀ (x y : α), f s(x, y))
 → ∀ (i : Sym2 α), f i
· 使用定理 `Quot.indepCoherent`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r →
 Sort v} (f : (a : α) → motive (Quot.mk r a)),   (∀ (a b : α) (p : r a b), ⋯ ▸ f
 a = f b…
· 使用定理 `Quot.liftIndepPr1`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → 
Sort v} (f : (a : α) → motive (Quot.mk r a))   (h : ∀ (a b : α) (p : r a b), ⋯ ▸
 f a = …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite.congr_simp`：∀ {α : Sort u} (c c_1 : Prop),   c = c_1 →     ∀ {h : De
cidable c} [h_1 : Decidable c_1] (t t_1 : α),       t = t_1 → ∀ (e e_1 : α), e =
 e_1…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem other_invol' [DecidableEq α] {a : α} {z : Sym2 α} (ha : a ∈ z) (hb : Mem.other' ha ∈ z) :
    Mem.other' hb = a := by
  induction z
  aesop (rule_sets := [Sym2]) (add norm unfold [Sym2.rec, Quot.rec])
/-
**Sym2.other_invol** 是 Mathlib 中的一个定理，位于命名空间 `Sym2`。
形式化陈述：other_invol {a : α} {z : Sym2 α} (ha : a in z) (hb : Mem.other ha in z) : 
Mem.other hb = a
参数：ha : a in z；hb : Mem.other ha in z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Sym2.other_eq_other'`：other_eq_other' [DecidableEq α] {a : α} {z : Sym2 
α} (h : a in z) : Mem.other h = Mem.other' h
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Sym2.other_invol'`：other_invol' [DecidableEq α] {a : α} {z : Sym2 α} (ha
 : a in z) (hb : Mem.other' ha in z) : Mem.other' hb = a
-/
theorem other_invol {a : α} {z : Sym2 α} (ha : a ∈ z) (hb : Mem.other ha ∈ z) :
    Mem.other hb = a := by
  classical
    rw [other_eq_other'] at hb ⊢
    convert! other_invol' ha hb using 2
    apply other_eq_other'
/-
**Sym2.filter_image_mk_isDiag** 是 Mathlib 中的一个定理，位于命名空间 `Sym2`。
形式化陈述：filter_image_mk_isDiag [DecidableEq α] (s : Finset α) : {x in (s ×ˢ s).ima
ge Sym2.mk.uncurry | x.IsDiag} = s.diag.image Sym2.mk.uncurry
参数：s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.image_diag`：image_diag [DecidableEq β] (f : α × α -> β) (s : Fins
et α) : s.diag.image f = s.image fun x => f (x, x)
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem filter_image_mk_isDiag [DecidableEq α] (s : Finset α) :
    {x ∈ (s ×ˢ s).image Sym2.mk.uncurry | x.IsDiag} = s.diag.image Sym2.mk.uncurry := by aesop
/-
**Sym2.filter_image_mk_not_isDiag** 是 Mathlib 中的一个定理，位于命名空间 `Sym2`。
形式化陈述：filter_image_mk_not_isDiag [DecidableEq α] (s : Finset α) : {x in (s ×ˢ s)
.image Sym2.mk.uncurry | ¬x.IsDiag} = s.offDiag.image Sym2.mk.uncurry
参数：s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
-/
theorem filter_image_mk_not_isDiag [DecidableEq α] (s : Finset α) :
    {x ∈ (s ×ˢ s).image Sym2.mk.uncurry | ¬x.IsDiag} = s.offDiag.image Sym2.mk.uncurry := by aesop

end Decidable

/-
**Sym2.** 是 Mathlib 中的一个实例，位于命名空间 `Sym2`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Subsingleton α] : Subsingleton (Sym2 α) :=
  (equivSym α).injective.subsingleton
/-
**Sym2.** 是 Mathlib 中的一个实例，位于命名空间 `Sym2`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Unique α] : Unique (Sym2 α) :=
  Unique.mk' _
/-
**Sym2.** 是 Mathlib 中的一个实例，位于命名空间 `Sym2`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsEmpty α] : IsEmpty (Sym2 α) :=
  (equivSym α).isEmpty
/-
**Sym2.** 是 Mathlib 中的一个实例，位于命名空间 `Sym2`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Nontrivial α] : Nontrivial (Sym2 α) :=
  diag_injective.nontrivial

-- TODO: use a sort order if available, https://github.com/leanprover-community/mathlib/issues/18166
/-
**Sym2.** 是 Mathlib 中的一个实例，位于命名空间 `Sym2`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
unsafe instance [Repr α] : Repr (Sym2 α) where
  reprPrec s _ := f!"s({repr s.unquot.1}, {repr s.unquot.2})"
/-
**Sym2.lift_smul_lift** 是 Mathlib 中的一个引理，位于命名空间 `Sym2`。
形式化陈述：lift_smul_lift {α R N} [SMul R N] (f : { f : α -> α -> R // forall a₁ a₂, 
f a₁ a₂ = f a₂ a₁ }) (g : { g : α -> α -> N // forall a₁ a₂, g a₁ a₂ = g a₂ a₁ }
) : lift f • lift g = lift ⟨f.val • g.val, fun _ _ => by rw [Pi.smul_apply']; rw
 [Pi.smul_apply']; rw [Pi.smul_apply']; rw [Pi.smul_apply']; rw [f.prop]; rw [g.
prop]⟩
参数：f : { f : α -> α -> R // forall a₁ a₂, f a₁ a₂ = f a₂ a₁ }；g : { g : α -> α -
> N // forall a₁ a₂, g a₁ a₂ = g a₂ a₁ }。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma lift_smul_lift {α R N} [SMul R N] (f : { f : α → α → R // ∀ a₁ a₂, f a₁ a₂ = f a₂ a₁ })
    (g : { g : α → α → N // ∀ a₁ a₂, g a₁ a₂ = g a₂ a₁ }) :
    lift f • lift g = lift ⟨f.val • g.val, fun _ _ => by
      rw [Pi.smul_apply', Pi.smul_apply', Pi.smul_apply', Pi.smul_apply', f.prop, g.prop]⟩ := by
  ext ⟨i, j⟩
  simp_all only [Pi.smul_apply', lift_mk]

/--
Multiplication as a function from `Sym2`.
-/
@[to_additive /-- Addition as a function from `Sym2`. -/]
/-
**Sym2.mul** 是 Mathlib 中的一个定义，位于命名空间 `Sym2`。
形式化陈述：mul {M} [CommMagma M] : Sym2 M -> M
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a

--- 原说明 ---
Multiplication as a function from `Sym2`.
-/
def mul {M} [CommMagma M] : Sym2 M → M := lift ⟨(· * ·), mul_comm⟩

@[to_additive (attr := simp)]
/-
**Sym2.mul_mk** 是 Mathlib 中的一个引理，位于命名空间 `Sym2`。
形式化陈述：mul_mk {M} [CommMagma M] (a b : M) : mul s(a, b) = a * b
参数：a b : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mul_mk {M} [CommMagma M] (a b : M) : mul s(a, b) = a * b := rfl

end Sym2

namespace Set

open Sym2

variable {s : Set α}

/--
For a set `s : Set α`, `s.sym2` is the set of all unordered pairs of elements from `s`.
-/
/-
**Set.sym2** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：sym2 (s : Set α) : Set (Sym2 α)
参数：s : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For a set `s : Set α`, `s.sym2` is the set of all unordered pairs of elements fr
om `s`.
-/
def sym2 (s : Set α) : Set (Sym2 α) := fromRel (r := fun x y ↦ x ∈ s ∧ y ∈ s) ⟨fun _ _ ↦ .symm⟩
/-
**Set.mk_mem_sym2_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} {s : Set α} {x y : α}, s(x, y) ∈ s.sym2 ↔ x ∈ s ∧ y ∈ s
参数：x, y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma mk_mem_sym2_iff {x y : α} : s(x, y) ∈ s.sym2 ↔ x ∈ s ∧ y ∈ s := Iff.rfl

@[deprecated (since := "2026-02-05")] alias mk'_mem_sym2_iff := mk_mem_sym2_iff
/-
**Set.mem_sym2_iff_subset** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：mem_sym2_iff_subset {z : Sym2 α} : z in s.sym2 ↔ (z : Set α) subseteq s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sym2.inductionOn`：∀ {α : Type u_1} {f : Sym2 α → Prop} (i : Sym2 α), (∀ 
(x y : α), f s(x, y)) → f i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Sym2.coe_mk`：∀ {α : Type u_1} {x y : α}, ↑s(x, y) = {x, y}
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mem_sym2_iff_subset {z : Sym2 α} : z ∈ s.sym2 ↔ (z : Set α) ⊆ s := by
  induction z using Sym2.inductionOn
  simp [pair_subset_iff]
/-
**Set.sym2_eq_mk_image** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：sym2_eq_mk_image : s.sym2 = (Sym2.mk.uncurry) '' s ×ˢ s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.image_uncurry_prod`：∀ {α : Type u_1} {β : Type u_3} {γ : Type u_5} (
f : α → β → γ) (s : Set α) (t : Set β),   Function.uncurry f '' s ×ˢ t = Set.ima
ge2 f s t
· 使用引理 `Set.image2_curry`：image2_curry (f : α × β -> γ) (s : Set α) (t : Set β) 
: image2 (fun a b => f (a, b)) s t = f '' s ×ˢ t
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
lemma sym2_eq_mk_image : s.sym2 = (Sym2.mk.uncurry) '' s ×ˢ s := by ext ⟨x, y⟩; aesop
/-
**Set.mk_preimage_sym2** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} {s : Set α}, Function.uncurry Sym2.mk ⁻¹' s.sym2 = s ×ˢ s
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma mk_preimage_sym2 : (Sym2.mk.uncurry) ⁻¹' s.sym2 = s ×ˢ s := rfl
/-
**Set.sym2_empty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1}, ∅.sym2 = ∅
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma sym2_empty : (∅ : Set α).sym2 = ∅ := by ext ⟨x, y⟩; simp
/-
**Set.sym2_univ** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1}, Set.univ.sym2 = Set.univ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma sym2_univ : (Set.univ : Set α).sym2 = Set.univ := by ext ⟨x, y⟩; simp
/-
**Set.sym2_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_1} (a : α), {a}.sym2 = {s(a, a)}
参数：a : α；a, a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma sym2_singleton (a : α) : ({a} : Set α).sym2 = {s(a, a)} := by ext ⟨x, y⟩; simp
/-
**Set.sym2_insert** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：sym2_insert (a : α) (s : Set α) : (insert a s).sym2 = (fun b => s(a, b)) '
' insert a s union s.sym2
参数：a : α；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
-/
lemma sym2_insert (a : α) (s : Set α) :
    (insert a s).sym2 = (fun b ↦ s(a, b)) '' insert a s ∪ s.sym2 := by
  ext ⟨x, y⟩; aesop
/-
**Set.sym2_preimage** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：sym2_preimage {f : α -> β} {s : Set β} : (f ⁻¹' s).sym2 = Sym2.map f ⁻¹' s
.sym2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma sym2_preimage {f : α → β} {s : Set β} : (f ⁻¹' s).sym2 = Sym2.map f ⁻¹' s.sym2 := by
  ext ⟨x, y⟩
  simp
/-
**Set.sym2_image** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：sym2_image {f : α -> β} {s : Set α} : (f '' s).sym2 = Sym2.map f '' s.sym2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.sym2_eq_mk_image`：sym2_eq_mk_image : s.sym2 = (Sym2.mk.uncurry) '' s
 ×ˢ s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.prod_image_image_eq`：prod_image_image_eq {m₁ : α -> γ} {m₂ : β -> δ}
 : (m₁ '' s) ×ˢ (m₂ '' t) = (fun p : α × β => (m₁ p.1, m₂ p.2)) '' s ×ˢ t
· 使用定理 `Set.image_image`：image_image (g : β -> γ) (f : α -> β) (s : Set α) : g '
' f '' s = (fun x => g (f x)) '' s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma sym2_image {f : α → β} {s : Set α} : (f '' s).sym2 = Sym2.map f '' s.sym2 := by
  simp_rw [sym2_eq_mk_image, prod_image_image_eq, image_image, uncurry, Sym2.map_mk]
/-
**Set.sym2_inter** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：sym2_inter (s t : Set α) : (s inter t).sym2 = s.sym2 inter t.sym2
参数：s t : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.preimage_injective`：preimage_injective : Injective (preimage f) ↔ Su
rjective f
· 使用定理 `Sym2.mk_surjective`：mk_surjective : (Sym2.mk (α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.prod_inter_prod`：prod_inter_prod : s₁ ×ˢ t₁ inter s₂ ×ˢ t₂ = (s₁ int
er s₂) ×ˢ (t₁ inter t₂)
-/
lemma sym2_inter (s t : Set α) : (s ∩ t).sym2 = s.sym2 ∩ t.sym2 :=
  preimage_injective.mpr Sym2.mk_surjective <| Set.prod_inter_prod.symm
/-
**Set.sym2_iInter** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：sym2_iInter {ι : Type*} (f : ι -> Set α) : (⋂ i, f i).sym2 = ⋂ i, (f i).sy
m2
参数：f : ι -> Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma sym2_iInter {ι : Type*} (f : ι → Set α) : (⋂ i, f i).sym2 = ⋂ i, (f i).sym2 := by
  ext ⟨x, y⟩; simp [forall_and]

end Set

