/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.Group.Submonoid.Operations
public import Mathlib.Data.DFinsupp.Sigma
public import Mathlib.Data.DFinsupp.Submonoid

/-!
# Direct sum

This file defines the direct sum of abelian groups, indexed by a discrete type.

## Notation

`⨁ i, β i` is the n-ary direct sum `DirectSum`.
This notation is in the `DirectSum` locale, accessible after `open DirectSum`.

## References

* https://en.wikipedia.org/wiki/Direct_sum
-/

@[expose] public section

open Function

universe u v w u₁

variable (ι : Type v) (β : ι → Type w)

/-- `DirectSum ι β` is the direct sum of a family of additive commutative monoids `β i`.

Note: `open DirectSum` will enable the notation `⨁ i, β i` for `DirectSum ι β`. -/
@[implicit_reducible]
/-
**DirectSum** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：DirectSum [forall i, AddCommMonoid (β i)] : Type _
参数：β i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`DirectSum ι β` is the direct sum of a family of additive commutative monoids `β
 i`.

Note: `open DirectSum` will enable the notation `⨁ i, β i` for `DirectSum ι β`.
-/
def DirectSum [∀ i, AddCommMonoid (β i)] : Type _ :=
  Π₀ i, β i

set_option backward.inferInstanceAs.wrap.data false in
deriving instance CoeFun for DirectSum

/-- `⨁ i, f i` is notation for `DirectSum _ f` and equals the direct sum of `fun i ↦ f i`.
Taking the direct sum over multiple arguments is possible, e.g. `⨁ (i) (j), f i j`. -/
scoped[DirectSum] notation3 "⨁ "(...)", "r:(scoped f => DirectSum _ f) => r

-- Porting note: The below recreates some of the lean3 notation, not fully yet
-- section
-- open Batteries.ExtendedBinder
-- syntax (name := bigdirectsum) "⨁ " extBinders ", " term : term
-- macro_rules (kind := bigdirectsum)
--   | `(⨁ $_:ident, $y:ident → $z:ident) => `(DirectSum _ (fun $y ↦ $z))
--   | `(⨁ $x:ident, $p) => `(DirectSum _ (fun $x ↦ $p))
--   | `(⨁ $_:ident : $t:ident, $p) => `(DirectSum _ (fun $t ↦ $p))
--   | `(⨁ ($x:ident) ($y:ident), $p) => `(DirectSum _ (fun $x ↦ fun $y ↦ $p))
-- end

namespace DirectSum

variable {ι β}

-- This instance exists to avoid nsmul and zsmul diamonds.
/-
**DirectSum.** 是 Mathlib 中的一个实例，位于命名空间 `DirectSum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R : Type u} [Semiring R] [∀ i, AddCommMonoid (β i)] [∀ i, Module R (β i)] :
    SMul R (⨁ i, β i) := inferInstanceAs <| SMul R (Π₀ (i : ι), β i)

deriving instance AddCommMonoid, Inhabited, DFunLike for DirectSum
/-
**DirectSum.** 是 Mathlib 中的一个实例，位于命名空间 `DirectSum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DecidableEq ι] [∀ i, AddCommMonoid (β i)] [∀ i, DecidableEq (β i)] :
    DecidableEq (DirectSum ι β) :=
  inferInstanceAs <| DecidableEq (Π₀ i, β i)

variable (β) in
/-- Coercion from a `DirectSum` to a pi type is an `AddMonoidHom`. -/
/-
**DirectSum.coeFnAddMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `DirectSum`。
形式化陈述：coeFnAddMonoidHom [forall i, AddCommMonoid (β i)] : (⨁ i, β i) ->+ (Π i, β
 i) where toFun x
参数：β i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Coercion from a `DirectSum` to a pi type is an `AddMonoidHom`.
-/
def coeFnAddMonoidHom [∀ i, AddCommMonoid (β i)] : (⨁ i, β i) →+ (Π i, β i) where
  toFun x := x
  __ := DFinsupp.coeFnAddMonoidHom

@[simp]
/-
**DirectSum.coeFnAddMonoidHom_apply** 是 Mathlib 中的一个引理，位于命名空间 `DirectSum`。
形式化陈述：coeFnAddMonoidHom_apply [forall i, AddCommMonoid (β i)] (v : ⨁ i, β i) : c
oeFnAddMonoidHom β v = v
参数：β i；v : ⨁ i, β i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coeFnAddMonoidHom_apply [∀ i, AddCommMonoid (β i)] (v : ⨁ i, β i) :
    coeFnAddMonoidHom β v = v :=
  rfl

section AddCommGroup

variable [∀ i, AddCommGroup (β i)]

/-
**DirectSum.** 是 Mathlib 中的一个实例，位于命名空间 `DirectSum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddCommGroup (DirectSum ι β) :=
  inferInstanceAs (AddCommGroup (Π₀ i, β i))

@[simp]
/-
**DirectSum.sub_apply** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：sub_apply (g₁ g₂ : ⨁ i, β i) (i : ι) : (g₁ - g₂) i = g₁ i - g₂ i
参数：g₁ g₂ : ⨁ i, β i；i : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sub_apply (g₁ g₂ : ⨁ i, β i) (i : ι) : (g₁ - g₂) i = g₁ i - g₂ i :=
  rfl

end AddCommGroup

variable [∀ i, AddCommMonoid (β i)]

/-
**DirectSum.ext** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：∀ {ι : Type v} {β : ι → Type w} [inst : (i : ι) → AddCommMonoid (β i)] {x 
y : DirectSum ι β},   (∀ (i : ι), x i = y i) → x = y
参数：i : ι；β i；∀ (i : ι), x i = y i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
@[ext] theorem ext {x y : DirectSum ι β} (w : ∀ i, x i = y i) : x = y :=
  DFunLike.ext _ _ w

@[simp]
/-
**DirectSum.zero_apply** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：zero_apply (i : ι) : (0 : ⨁ i, β i) i = 0
参数：i : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zero_apply (i : ι) : (0 : ⨁ i, β i) i = 0 :=
  rfl

@[simp]
/-
**DirectSum.add_apply** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：add_apply (g₁ g₂ : ⨁ i, β i) (i : ι) : (g₁ + g₂) i = g₁ i + g₂ i
参数：g₁ g₂ : ⨁ i, β i；i : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem add_apply (g₁ g₂ : ⨁ i, β i) (i : ι) : (g₁ + g₂) i = g₁ i + g₂ i :=
  rfl

@[simp]
/-
**DirectSum.sum_apply** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：sum_apply {α} (s : Finset α) (g : α -> ⨁ i, β i) (i : ι) : (∑ a in s, g a)
 i = ∑ a in s, g a i
参数：s : Finset α；g : α -> ⨁ i, β i；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.finsetSum_apply`：finsetSum_apply {α} [forall i, AddCommMonoid (
β i)] (s : Finset α) (g : α -> Π₀ i, β i) (i : ι) : (∑ a in s, g a) i = ∑ a in s
, g a i
-/
theorem sum_apply {α} (s : Finset α) (g : α → ⨁ i, β i) (i : ι) :
    (∑ a ∈ s, g a) i = ∑ a ∈ s, g a i :=
  DFinsupp.finsetSum_apply s g i

section DecidableEq

variable [DecidableEq ι]

variable (β)

/-- `mk β s x` is the element of `⨁ i, β i` that is zero outside `s`
and has coefficient `x i` for `i` in `s`. -/
/-
**DirectSum.mk** 是 Mathlib 中的一个定义，位于命名空间 `DirectSum`。
形式化陈述：mk (s : Finset ι) : (forall i : (↑s : Set ι), β i.1) ->+ ⨁ i, β i where to
Fun
参数：s : Finset ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`mk β s x` is the element of `⨁ i, β i` that is zero outside `s`
and has coefficient `x i` for `i` in `s`.
-/
def mk (s : Finset ι) : (∀ i : (↑s : Set ι), β i.1) →+ ⨁ i, β i where
  toFun := DFinsupp.mk s
  map_add' _ _ := DFinsupp.mk_add
  map_zero' := DFinsupp.mk_zero

/-- `of i` is the natural inclusion map from `β i` to `⨁ i, β i`. -/
/-
**DirectSum.of** 是 Mathlib 中的一个定义，位于命名空间 `DirectSum`。
形式化陈述：of (i : ι) : β i ->+ ⨁ i, β i
参数：i : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`of i` is the natural inclusion map from `β i` to `⨁ i, β i`.
-/
def of (i : ι) : β i →+ ⨁ i, β i :=
  DFinsupp.singleAddHom β i

variable {β}

@[simp]
/-
**DirectSum.of_eq_same** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：of_eq_same (i : ι) (x : β i) : (of _ i x) i = x
参数：i : ι；x : β i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.single_eq_same`：single_eq_same {i b} : (single i b : Π₀ i, β i)
 i = b
-/
theorem of_eq_same (i : ι) (x : β i) : (of _ i x) i = x :=
  DFinsupp.single_eq_same
/-
**DirectSum.of_eq_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：of_eq_of_ne (i j : ι) (x : β i) (h : j != i) : (of _ i x) j = 0
参数：i j : ι；x : β i；h : j != i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.single_eq_of_ne`：single_eq_of_ne {i i' b} (h : i' != i) : (sing
le i b : Π₀ i, β i) i' = 0
-/
theorem of_eq_of_ne (i j : ι) (x : β i) (h : j ≠ i) : (of _ i x) j = 0 :=
  DFinsupp.single_eq_of_ne h
/-
**DirectSum.of_apply** 是 Mathlib 中的一个引理，位于命名空间 `DirectSum`。
形式化陈述：of_apply {i : ι} (j : ι) (x : β i) : of β i x j = if h : i = j then Eq.rec
On h x else 0
参数：j : ι；x : β i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.single_apply`：single_apply {i i' b} : (single i b : Π₀ i, β i) 
i' = if h : i = i' then Eq.recOn h b else 0
-/
lemma of_apply {i : ι} (j : ι) (x : β i) : of β i x j = if h : i = j then Eq.recOn h x else 0 :=
  DFinsupp.single_apply
/-
**DirectSum.mk_apply_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：mk_apply_of_mem {s : Finset ι} {f : forall i : (↑s : Set ι), β i.val} {n :
 ι} (hn : n in s) : mk β s f n = f ⟨n, hn⟩
参数：↑s : Set ι；hn : n in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.mk_of_mem`：mk_of_mem (hi : i in s) : (mk s x : forall i, β i) i
 = x ⟨i, hi⟩
-/
theorem mk_apply_of_mem {s : Finset ι} {f : ∀ i : (↑s : Set ι), β i.val} {n : ι} (hn : n ∈ s) :
    mk β s f n = f ⟨n, hn⟩ :=
  DFinsupp.mk_of_mem hn
/-
**DirectSum.mk_apply_of_notMem** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：mk_apply_of_notMem {s : Finset ι} {f : forall i : (↑s : Set ι), β i.val} {
n : ι} (hn : n ∉ s) : mk β s f n = 0
参数：↑s : Set ι；hn : n ∉ s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.mk_of_notMem`：mk_of_notMem (hi : i ∉ s) : (mk s x : forall i, β
 i) i = 0
-/
theorem mk_apply_of_notMem {s : Finset ι} {f : ∀ i : (↑s : Set ι), β i.val} {n : ι} (hn : n ∉ s) :
    mk β s f n = 0 :=
  DFinsupp.mk_of_notMem hn

@[simp]
/-
**DirectSum.support_zero** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：support_zero [forall (i : ι) (x : β i), Decidable (x != 0)] : (0 : ⨁ i, β 
i).support = ∅
参数：i : ι；x : β i；x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.support_zero`：support_zero : (0 : Π₀ i, β i).support = ∅
-/
theorem support_zero [∀ (i : ι) (x : β i), Decidable (x ≠ 0)] : (0 : ⨁ i, β i).support = ∅ :=
  DFinsupp.support_zero

@[simp]
/-
**DirectSum.support_of** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：support_of [forall (i : ι) (x : β i), Decidable (x != 0)] (i : ι) (x : β i
) (h : x != 0) : (of _ i x).support = {i}
参数：i : ι；x : β i；x != 0；i : ι；x : β i；h : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.support_single`：support_single {i : ι} {b : β i} (hb : b != 0) 
: (single i b).support = {i}
-/
theorem support_of [∀ (i : ι) (x : β i), Decidable (x ≠ 0)] (i : ι) (x : β i) (h : x ≠ 0) :
    (of _ i x).support = {i} :=
  DFinsupp.support_single h
/-
**DirectSum.support_of_subset** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：support_of_subset [forall (i : ι) (x : β i), Decidable (x != 0)] {i : ι} {
b : β i} : (of _ i b).support subseteq {i}
参数：i : ι；x : β i；x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.support_single_subset`：support_single_subset {i : ι} {b : β i} 
: (single i b).support subseteq {i}
-/
theorem support_of_subset [∀ (i : ι) (x : β i), Decidable (x ≠ 0)] {i : ι} {b : β i} :
    (of _ i b).support ⊆ {i} :=
  DFinsupp.support_single_subset
/-
**DirectSum.sum_support_of** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：sum_support_of [forall (i : ι) (x : β i), Decidable (x != 0)] (x : ⨁ i, β 
i) : (∑ i in x.support, of β i (x i)) = x
参数：i : ι；x : β i；x != 0；x : ⨁ i, β i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.sum_single`：sum_single [forall i, AddCommMonoid (β i)] [forall 
(i) (x : β i), Decidable (x != 0)] {f : Π₀ i, β i} : f.sum single = f
-/
theorem sum_support_of [∀ (i : ι) (x : β i), Decidable (x ≠ 0)] (x : ⨁ i, β i) :
    (∑ i ∈ x.support, of β i (x i)) = x :=
  DFinsupp.sum_single
/-
**DirectSum.sum_univ_of** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：sum_univ_of [Fintype ι] (x : ⨁ i, β i) : ∑ i in Finset.univ, of β i (x i) 
= x
参数：x : ⨁ i, β i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirectSum.ext`：∀ {ι : Type v} {β : ι → Type w} [inst : (i : ι) → AddComm
Monoid (β i)] {x y : DirectSum ι β},   (∀ (i : ι), x i = y i) → x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `DirectSum.sum_apply`：sum_apply {α} (s : Finset α) (g : α -> ⨁ i, β i) (i
 : ι) : (∑ a in s, g a) i = ∑ a in s, g a i
· 使用引理 `DirectSum.of_apply`：of_apply {i : ι} (j : ι) (x : β i) : of β i x j = if
 h : i = j then Eq.recOn h x else 0
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `Finset.sum_dite_eq'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMono
id M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι)   (b : (x : ι) → x = a → M
), (∑ x ∈…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sum_univ_of [Fintype ι] (x : ⨁ i, β i) :
    ∑ i ∈ Finset.univ, of β i (x i) = x := by
  ext i
  simp [of_apply]
/-
**DirectSum.mk_injective** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：mk_injective (s : Finset ι) : Function.Injective (mk β s)
参数：s : Finset ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.mk_injective`：mk_injective (s : Finset ι) : Function.Injective 
(@mk ι β _ _ s)
-/
theorem mk_injective (s : Finset ι) : Function.Injective (mk β s) :=
  DFinsupp.mk_injective s
/-
**DirectSum.of_injective** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：of_injective (i : ι) : Function.Injective (of β i)
参数：i : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.single_injective`：single_injective {i} : Function.Injective (si
ngle i : β i -> Π₀ i, β i)
-/
theorem of_injective (i : ι) : Function.Injective (of β i) :=
  DFinsupp.single_injective

@[elab_as_elim]
/-
**DirectSum.induction_on** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：∀ {ι : Type v} {β : ι → Type w} [inst : (i : ι) → AddCommMonoid (β i)] [in
st_1 : DecidableEq ι]   {motive : (DirectSum ι fun i => β i) → Prop} (x : Direct
Sum ι fun i => β i),   motive 0 →     (∀ (i : ι) (x : β i), motive ((DirectSum.o
f β i) x)) →       (∀ (x y : DirectSum ι fun i => β i), motive x → motive y → mo
tive (x + y)) → motive x
参数：i : ι；β i；DirectSum ι fun i => β i；x : DirectSum ι fun i => β i；∀ (i : ι) (x 
: β i), motive ((DirectSum.of β i) x)；∀ (x y : DirectSum ι fun i => β i), motive
 x → motive y → motive (x + y)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.induction`：∀ {ι : Type u} {β : ι → Type v} [inst : DecidableEq 
ι] [inst_1 : (i : ι) → AddZeroClass (β i)]   {p : (Π₀ (i : ι), β i) → Prop} (f :
 Π₀ (i :…
-/
protected theorem induction_on {motive : (⨁ i, β i) → Prop} (x : ⨁ i, β i) (zero : motive 0)
    (of : ∀ (i : ι) (x : β i), motive (of β i x))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive x := by
  apply DFinsupp.induction x zero
  intro i b f h1 h2 ih
  solve_by_elim

/-- An alternative induction, where the addition assumption is restricted to singles. -/
@[elab_as_elim]
/-
**DirectSum.induction_on'** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：∀ {ι : Type v} {β : ι → Type w} [inst : (i : ι) → AddCommMonoid (β i)] [in
st_1 : DecidableEq ι]   {motive : (DirectSum ι fun i => β i) → Prop} (f : Direct
Sum ι fun i => β i),   motive 0 →     (∀ (i : ι) (b : β i) (f : DirectSum ι fun 
i => β i),         f i = 0 → b ≠ 0 → motive f → motive ((DirectSum.of β i) b + f
)) →       motive f
参数：i : ι；β i；DirectSum ι fun i => β i；f : DirectSum ι fun i => β i；∀ (i : ι) (b 
: β i) (f : DirectSum ι fun i => β i),         f i = 0 → b ≠ 0 → motive f → moti
ve ((DirectSum.of β i) b + f)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.induction`：∀ {ι : Type u} {β : ι → Type v} [inst : DecidableEq 
ι] [inst_1 : (i : ι) → AddZeroClass (β i)]   {p : (Π₀ (i : ι), β i) → Prop} (f :
 Π₀ (i :…

--- 原说明 ---
An alternative induction, where the addition assumption is restricted to singles
.
-/
protected theorem induction_on' {motive : (⨁ i, β i) → Prop} (f : ⨁ i, β i) (h0 : motive 0)
    (hadd : ∀ (i b) (f : ⨁ i, β i), f i = 0 → b ≠ 0 → motive f → motive (of β i b + f)) :
    motive f :=
  DFinsupp.induction f h0 hadd

/-- If two additive homomorphisms from `⨁ i, β i` are equal on each `of β i y`,
then they are equal. -/
/-
**DirectSum.addHom_ext** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：addHom_ext {γ : Type*} [AddZeroClass γ] ⦃f g : (⨁ i, β i) ->+ γ⦄ (H : fora
ll (i : ι) (y : β i), f (of _ i y) = g (of _ i y)) : f = g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.addHom_ext`：addHom_ext {γ : Type w} [AddZeroClass γ] ⦃f g : (Π₀
 i, β i) ->+ γ⦄ (H : forall (i : ι) (y : β i), f (single i y) = g (single i y)) 
: f = g

--- 原说明 ---
If two additive homomorphisms from `⨁ i, β i` are equal on each `of β i y`,
then they are equal.
-/
theorem addHom_ext {γ : Type*} [AddZeroClass γ] ⦃f g : (⨁ i, β i) →+ γ⦄
    (H : ∀ (i : ι) (y : β i), f (of _ i y) = g (of _ i y)) : f = g :=
  DFinsupp.addHom_ext H

/-- If two additive homomorphisms from `⨁ i, β i` are equal on each `of β i y`,
then they are equal.

See note [partially-applied ext lemmas]. -/
@[ext high]
/-
**DirectSum.addHom_ext'** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：addHom_ext' {γ : Type*} [AddZeroClass γ] ⦃f g : (⨁ i, β i) ->+ γ⦄ (H : for
all i : ι, f.comp (of _ i) = g.comp (of _ i)) : f = g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirectSum.addHom_ext`：addHom_ext {γ : Type*} [AddZeroClass γ] ⦃f g : (⨁ 
i, β i) ->+ γ⦄ (H : forall (i : ι) (y : β i), f (of _ i y) = g (of _ i y)) : f =
 g
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x

--- 原说明 ---
If two additive homomorphisms from `⨁ i, β i` are equal on each `of β i y`,
then they are equal.

See note [partially-applied ext lemmas].
-/
theorem addHom_ext' {γ : Type*} [AddZeroClass γ] ⦃f g : (⨁ i, β i) →+ γ⦄
    (H : ∀ i : ι, f.comp (of _ i) = g.comp (of _ i)) : f = g :=
  addHom_ext fun i => DFunLike.congr_fun <| H i

variable {γ : Type u₁} [AddCommMonoid γ]

section ToAddMonoid

variable (φ : ∀ i, β i →+ γ) (ψ : (⨁ i, β i) →+ γ)

-- Porting note: The elaborator is struggling with `liftAddHom`. Passing it `β` explicitly helps.
-- This applies to roughly the remainder of the file.

/-- `toAddMonoid φ` is the natural homomorphism from `⨁ i, β i` to `γ`
induced by a family `φ` of homomorphisms `β i → γ`. -/
/-
**DirectSum.toAddMonoid** 是 Mathlib 中的一个定义，位于命名空间 `DirectSum`。
形式化陈述：toAddMonoid : (⨁ i, β i) ->+ γ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`toAddMonoid φ` is the natural homomorphism from `⨁ i, β i` to `γ`
induced by a family `φ` of homomorphisms `β i → γ`.
-/
def toAddMonoid : (⨁ i, β i) →+ γ :=
  DFinsupp.liftAddHom (β := β) φ

@[simp]
/-
**DirectSum.toAddMonoid_of** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：toAddMonoid_of (i) (x : β i) : toAddMonoid φ (of β i x) = φ i x
参数：i；x : β i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.liftAddHom_apply_single`：liftAddHom_apply_single [forall i, Add
ZeroClass (β i)] [AddCommMonoid γ] (f : forall i, β i ->+ γ) (i : ι) (x : β i) :
 liftAddHom f (single …
-/
theorem toAddMonoid_of (i) (x : β i) : toAddMonoid φ (of β i x) = φ i x :=
  DFinsupp.liftAddHom_apply_single φ i x
/-
**DirectSum.toAddMonoid.unique** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum.toAddMonoid`
。
形式化陈述：∀ {ι : Type v} {β : ι → Type w} [inst : (i : ι) → AddCommMonoid (β i)] [in
st_1 : DecidableEq ι] {γ : Type u₁}   [inst_2 : AddCommMonoid γ] (ψ : (DirectSum
 ι fun i => β i) →+ γ) (f : DirectSum ι fun i => β i),   ψ f = (DirectSum.toAddM
onoid fun i => ψ.comp (DirectSum.of β i)) f
参数：i : ι；β i；ψ : (DirectSum ι fun i => β i) →+ γ；f : DirectSum ι fun i => β i；Di
rectSum.toAddMonoid fun i => ψ.comp (DirectSum.of β i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.addHom_ext'`：addHom_ext' {γ : Type w} [AddZeroClass γ] ⦃f g : (
Π₀ i, β i) ->+ γ⦄ (H : forall x, f.comp (singleAddHom β x) = g.comp (singleAddHo
m β x)) : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `DFinsupp.liftAddHom_apply`：∀ {ι : Type u} {γ : Type w} {β : ι → Type v} 
[inst : DecidableEq ι] [inst_1 : (i : ι) → AddZeroClass (β i)]   [inst_2 : AddCo
mmMonoid γ] (φ …
· 使用定理 `DFinsupp.sumAddHom_comp_single`：sumAddHom_comp_single [forall i, AddZero
Class (β i)] [AddCommMonoid γ] (f : forall i, β i ->+ γ) (i : ι) : (sumAddHom f)
.comp (singleAddHom …
-/
theorem toAddMonoid.unique (f : ⨁ i, β i) : ψ f = toAddMonoid (fun i => ψ.comp (of β i)) f := by
  congr
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): `ext` applies addHom_ext' here, which isn't what we want.
  apply DFinsupp.addHom_ext'
  intro
  simp [toAddMonoid]
  rfl
/-
**DirectSum.toAddMonoid_injective** 是 Mathlib 中的一个引理，位于命名空间 `DirectSum`。
形式化陈述：toAddMonoid_injective : Injective (toAddMonoid : (forall i, β i ->+ γ) -> 
(⨁ i, β i) ->+ γ)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddEquiv.injective`：∀ {M : Type u_4} {N : Type u_5} [inst : Add M] [inst
_1 : Add N] (e : M ≃+ N), Function.Injective ⇑e
-/
lemma toAddMonoid_injective : Injective (toAddMonoid : (∀ i, β i →+ γ) → (⨁ i, β i) →+ γ) :=
  DFinsupp.liftAddHom.injective
/-
**DirectSum.toAddMonoid_inj** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：∀ {ι : Type v} {β : ι → Type w} [inst : (i : ι) → AddCommMonoid (β i)] [in
st_1 : DecidableEq ι] {γ : Type u₁}   [inst_2 : AddCommMonoid γ] {f g : (i : ι) 
→ β i →+ γ}, DirectSum.toAddMonoid f = DirectSum.toAddMonoid g ↔ f = g
参数：i : ι；β i；i : ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用引理 `DirectSum.toAddMonoid_injective`：toAddMonoid_injective : Injective (toAd
dMonoid : (forall i, β i ->+ γ) -> (⨁ i, β i) ->+ γ)
-/
@[simp] lemma toAddMonoid_inj {f g : ∀ i, β i →+ γ} : toAddMonoid f = toAddMonoid g ↔ f = g :=
  toAddMonoid_injective.eq_iff

end ToAddMonoid

section FromAddMonoid

/-- `fromAddMonoid φ` is the natural homomorphism from `γ` to `⨁ i, β i`
induced by a family `φ` of homomorphisms `γ → β i`.

Note that this is not an isomorphism. Not every homomorphism `γ →+ ⨁ i, β i` arises in this way. -/
/-
**DirectSum.fromAddMonoid** 是 Mathlib 中的一个定义，位于命名空间 `DirectSum`。
形式化陈述：fromAddMonoid : (⨁ i, γ ->+ β i) ->+ γ ->+ ⨁ i, β i
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`fromAddMonoid φ` is the natural homomorphism from `γ` to `⨁ i, β i`
induced by a family `φ` of homomorphisms `γ → β i`.

Note that this is not an isomorphism. Not every homomorphism `γ →+ ⨁ i, β i` ari
ses in this way.
-/
def fromAddMonoid : (⨁ i, γ →+ β i) →+ γ →+ ⨁ i, β i :=
  toAddMonoid fun i => AddMonoidHom.compHom (of β i)

@[simp]
/-
**DirectSum.fromAddMonoid_of** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：fromAddMonoid_of (i : ι) (f : γ ->+ β i) : fromAddMonoid (of _ i f) = (of 
_ i).comp f
参数：i : ι；f : γ ->+ β i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DirectSum.fromAddMonoid.eq_1`：∀ {ι : Type v} {β : ι → Type w} [inst : (i
 : ι) → AddCommMonoid (β i)] [inst_1 : DecidableEq ι] {γ : Type u₁}   [inst_2 : 
AddCommMonoid γ], …
· 使用定理 `DirectSum.toAddMonoid_of`：toAddMonoid_of (i) (x : β i) : toAddMonoid φ (
of β i x) = φ i x
-/
theorem fromAddMonoid_of (i : ι) (f : γ →+ β i) : fromAddMonoid (of _ i f) = (of _ i).comp f := by
  rw [fromAddMonoid, toAddMonoid_of]
  rfl
/-
**DirectSum.fromAddMonoid_of_apply** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：fromAddMonoid_of_apply (i : ι) (f : γ ->+ β i) (x : γ) : fromAddMonoid (of
 _ i f) x = of _ i (f x)
参数：i : ι；f : γ ->+ β i；x : γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DirectSum.fromAddMonoid_of`：fromAddMonoid_of (i : ι) (f : γ ->+ β i) : f
romAddMonoid (of _ i f) = (of _ i).comp f
· 使用定理 `AddMonoidHom.coe_comp`：∀ {M : Type u_4} {N : Type u_5} {P : Type u_6} [i
nst : AddZero M] [inst_1 : AddZero N] [inst_2 : AddZero P] (g : N →+ P)   (f : M
 →+ N), ⇑(g…
· 使用定理 `Function.comp.eq_1`：∀ {α : Sort u} {β : Sort v} {δ : Sort w} (f : β → δ)
 (g : α → β) (x : α), (f ∘ g) x = f (g x)
-/
theorem fromAddMonoid_of_apply (i : ι) (f : γ →+ β i) (x : γ) :
    fromAddMonoid (of _ i f) x = of _ i (f x) := by
      rw [fromAddMonoid_of, AddMonoidHom.coe_comp, Function.comp]

end FromAddMonoid

variable (β)

-- TODO: generalize this to remove the assumption `S ⊆ T`.
/-- `setToSet β S T h` is the natural homomorphism `⨁ (i : S), β i → ⨁ (i : T), β i`,
where `h : S ⊆ T`. -/
/-
**DirectSum.setToSet** 是 Mathlib 中的一个定义，位于命名空间 `DirectSum`。
形式化陈述：setToSet (S T : Set ι) (H : S subseteq T) : (⨁ i : S, β i) ->+ ⨁ i : T, β 
i
参数：S T : Set ι；H : S subseteq T。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`setToSet β S T h` is the natural homomorphism `⨁ (i : S), β i → ⨁ (i : T), β i`
,
where `h : S ⊆ T`.
-/
def setToSet (S T : Set ι) (H : S ⊆ T) : (⨁ i : S, β i) →+ ⨁ i : T, β i :=
  toAddMonoid fun i => of (fun i : T => β i) ⟨↑i, H i.2⟩

end DecidableEq

/-
**DirectSum.unique** 是 Mathlib 中的一个实例，位于命名空间 `DirectSum`。
形式化陈述：unique [forall i, Subsingleton (β i)] : Unique (⨁ i, β i)
参数：β i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance unique [∀ i, Subsingleton (β i)] : Unique (⨁ i, β i) :=
  DFinsupp.unique

/-- A direct sum over an empty type is trivial. -/
/-
**DirectSum.uniqueOfIsEmpty** 是 Mathlib 中的一个实例，位于命名空间 `DirectSum`。
形式化陈述：uniqueOfIsEmpty [IsEmpty ι] : Unique (⨁ i, β i)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A direct sum over an empty type is trivial.
-/
instance uniqueOfIsEmpty [IsEmpty ι] : Unique (⨁ i, β i) :=
  DFinsupp.uniqueOfIsEmpty

/-- The natural equivalence between `⨁ _ : ι, M` and `M` when `Unique ι`. -/
/-
**DirectSum.id** 是 Mathlib 中的一个定义，位于命名空间 `DirectSum`。
形式化陈述：(M : Type v) →   (ι : optParam (Type u_1) PUnit.{u_1 + 1}) → [inst : AddCo
mmMonoid M] → [Unique ι] → (DirectSum ι fun x => M) ≃+ M
参数：Type u_1。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α

--- 原说明 ---
The natural equivalence between `⨁ _ : ι, M` and `M` when `Unique ι`.
-/
protected def id (M : Type v) (ι : Type* := PUnit) [AddCommMonoid M] [Unique ι] :
    (⨁ _ : ι, M) ≃+ M :=
  { DirectSum.toAddMonoid fun _ => AddMonoidHom.id M with
    toFun := DirectSum.toAddMonoid fun _ => AddMonoidHom.id M
    invFun := of (fun _ => M) default
    left_inv x :=
      DirectSum.induction_on x
        (by rw [map_zero, map_zero])
        (fun p x => by rw [Unique.default_eq p, toAddMonoid_of, AddMonoidHom.id_apply])
        (fun x y ihx ihy => by grind)
    right_inv _ := toAddMonoid_of _ _ _ }
/-
**DirectSum.id_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：∀ {M : Type v} {ι : Type u_1} [inst : AddCommMonoid M] [inst_1 : Unique ι]
 (x : M),   (DirectSum.id M ι).symm x = (DirectSum.of (fun i => M) default) x
参数：x : M；DirectSum.id M ι；DirectSum.of (fun i => M) default。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma id_symm_apply {M : Type v} {ι : Type*} [AddCommMonoid M] [Unique ι] (x : M) :
    (DirectSum.id M ι).symm x = of _ default x :=
  rfl
/-
**DirectSum.id_apply** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：∀ {M : Type v} {ι : Type u_1} [inst : AddCommMonoid M] [inst_1 : Unique ι]
 (x : DirectSum ι fun x => M),   (DirectSum.id M ι) x = x default
参数：x : DirectSum ι fun x => M；DirectSum.id M ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AddEquiv.eq_symm_apply`：∀ {M : Type u_4} {N : Type u_5} [inst : Add M] [
inst_1 : Add N] (e : M ≃+ N) {x : N} {y : M}, y = e.symm x ↔ e y = x
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `DirectSum.id_symm_apply`：∀ {M : Type v} {ι : Type u_1} [inst : AddCommMo
noid M] [inst_1 : Unique ι] (x : M),   (DirectSum.id M ι).symm x = (DirectSum.of
 (fun i => M)…
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `DirectSum.induction_on`：∀ {ι : Type v} {β : ι → Type w} [inst : (i : ι) 
→ AddCommMonoid (β i)] [inst_1 : DecidableEq ι]   {motive : (DirectSum ι fun i =
> β i) → Pro…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Unique.eq_default`：eq_default (a : α) : a = default
· 使用定理 `DirectSum.of_eq_same`：of_eq_same (i : ι) (x : β i) : (of _ i x) i = x
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
-/
@[simp] lemma id_apply {M : Type v} {ι : Type*} [AddCommMonoid M] [Unique ι] (x : ⨁ _ : ι, M) :
    DirectSum.id M ι x = x default := by
  rw [← AddEquiv.eq_symm_apply, id_symm_apply, eq_comm]
  induction x using DirectSum.induction_on <;> simp [Unique.eq_default, *]

section CongrLeft

variable {κ : Type*}

/-- Reindexing terms of a direct sum: change indexing type from `ι` to `κ` along an equivalence
`h : ι ≃ κ`. -/
/-
**DirectSum.equivCongrLeft** 是 Mathlib 中的一个定义，位于命名空间 `DirectSum`。
形式化陈述：equivCongrLeft (h : ι ≃ κ) : (⨁ i, β i) ≃+ ⨁ k, β (h.symm k)
参数：h : ι ≃ κ。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Reindexing terms of a direct sum: change indexing type from `ι` to `κ` along an 
equivalence
`h : ι ≃ κ`.
-/
def equivCongrLeft (h : ι ≃ κ) : (⨁ i, β i) ≃+ ⨁ k, β (h.symm k) :=
  { DFinsupp.equivCongrLeft h with map_add' := DFinsupp.comapDomain'_add _ h.right_inv }

@[simp]
/-
**DirectSum.equivCongrLeft_apply** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：equivCongrLeft_apply (h : ι ≃ κ) (f : ⨁ i, β i) (k : κ) : equivCongrLeft h
 f k = f (h.symm k)
参数：h : ι ≃ κ；f : ⨁ i, β i；k : κ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.comapDomain'_apply`：∀ {ι : Type u} {β : ι → Type v} {κ : Type u
_1} [inst : (i : ι) → Zero (β i)] (h : κ → ι) {h' : ι → κ}   (hh' : Function.Lef
tInverse h' h) (f…
· 使用定理 `Equiv.right_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Functio
n.RightInverse self.invFun self.toFun
-/
theorem equivCongrLeft_apply (h : ι ≃ κ) (f : ⨁ i, β i) (k : κ) :
    equivCongrLeft h f k = f (h.symm k) :=
  DFinsupp.comapDomain'_apply _ h.right_inv _ _

@[simp]
/-
**DirectSum.equivCongrLeft_of** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：equivCongrLeft_of [DecidableEq ι] [DecidableEq κ] (h : ι ≃ κ) (k : κ) (x :
 β (h.symm k)) : equivCongrLeft h (of β (h.symm k) x) = of (fun k => β (h.symm k
)) k x
参数：h : ι ≃ κ；k : κ；x : β (h.symm k)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `DFinsupp.comapDomain'_single`：∀ {ι : Type u} {β : ι → Type v} {κ : Type 
u_1} [inst : DecidableEq ι] [inst_1 : DecidableEq κ]   [inst_2 : (i : ι) → Zero 
(β i)] (h : κ → ι)…
· 使用定理 `Equiv.right_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Functio
n.RightInverse self.invFun self.toFun
-/
theorem equivCongrLeft_of [DecidableEq ι] [DecidableEq κ] (h : ι ≃ κ) (k : κ) (x : β (h.symm k)) :
    equivCongrLeft h (of β (h.symm k) x) = of (fun k ↦ β (h.symm k)) k x :=
  DFinsupp.comapDomain'_single h.symm h.right_inv _ _

end CongrLeft

section Option

variable {α : Option ι → Type w} [∀ i, AddCommMonoid (α i)]

/-- Isomorphism obtained by separating the term of index `none` of a direct sum over `Option ι`. -/
@[simps!]
/-
**DirectSum.addEquivProdDirectSum** 是 Mathlib 中的一个定义，位于命名空间 `DirectSum`。
形式化陈述：addEquivProdDirectSum : (⨁ i, α i) ≃+ α none × ⨁ i, α (some i)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Isomorphism obtained by separating the term of index `none` of a direct sum over
 `Option ι`.
-/
noncomputable def addEquivProdDirectSum : (⨁ i, α i) ≃+ α none × ⨁ i, α (some i) :=
  { DFinsupp.equivProdDFinsupp with map_add' := DFinsupp.equivProdDFinsupp_add }

end Option

section Sigma

variable [DecidableEq ι] {α : ι → Type u} {δ : ∀ i, α i → Type w} [∀ i j, AddCommMonoid (δ i j)]

/-- The natural map between `⨁ (i : Σ i, α i), δ i.1 i.2` and `⨁ i (j : α i), δ i j`. -/
/-
**DirectSum.sigmaCurry** 是 Mathlib 中的一个定义，位于命名空间 `DirectSum`。
形式化陈述：sigmaCurry : (⨁ i : Σ _i, _, δ i.1 i.2) ->+ ⨁ (i) (j), δ i j where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural map between `⨁ (i : Σ i, α i), δ i.1 i.2` and `⨁ i (j : α i), δ i j`
.
-/
def sigmaCurry : (⨁ i : Σ _i, _, δ i.1 i.2) →+ ⨁ (i) (j), δ i j where
  toFun := DFinsupp.sigmaCurry (δ := δ)
  map_zero' := DFinsupp.sigmaCurry_zero
  map_add' f g := DFinsupp.sigmaCurry_add f g

@[simp]
/-
**DirectSum.sigmaCurry_apply** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：sigmaCurry_apply (f : ⨁ i : Σ _i, _, δ i.1 i.2) (i : ι) (j : α i) : sigmaC
urry f i j = f ⟨i, j⟩
参数：f : ⨁ i : Σ _i, _, δ i.1 i.2；i : ι；j : α i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.sigmaCurry_apply`：sigmaCurry_apply [forall i j, Zero (δ i j)] (
f : Π₀ (i : Σ _, _), δ i.1 i.2) (i : ι) (j : α i) : sigmaCurry f i j = f ⟨i, j⟩
-/
theorem sigmaCurry_apply (f : ⨁ i : Σ _i, _, δ i.1 i.2) (i : ι) (j : α i) :
    sigmaCurry f i j = f ⟨i, j⟩ :=
  DFinsupp.sigmaCurry_apply (δ := δ) _ i j

@[simp]
/-
**DirectSum.sigmaCurry_of** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：sigmaCurry_of [forall i : ι, DecidableEq (α i)] (k : (i : ι) × α i) (x : δ
 k.1 k.2) : sigmaCurry (of (fun k => δ k.1 k.2) k x) = of (fun i' => ⨁ (j' : α i
'), δ i' j') k.1 (of (fun j' => δ k.1 j') k.2 x)
参数：α i；k : (i : ι) × α i；x : δ k.1 k.2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.sigmaCurry_single`：sigmaCurry_single [forall i, DecidableEq (α 
i)] [forall i j, Zero (δ i j)] (ij : Σ i, α i) (x : δ ij.1 ij.2) : sigmaCurry (s
ingle ij x) = si…
-/
theorem sigmaCurry_of [∀ i : ι, DecidableEq (α i)] (k : (i : ι) × α i) (x : δ k.1 k.2) :
    sigmaCurry (of (fun k ↦ δ k.1 k.2) k x) =
      of (fun i' ↦ ⨁ (j' : α i'), δ i' j') k.1 (of (fun j' ↦ δ k.1 j') k.2 x) :=
  DFinsupp.sigmaCurry_single k x

/-- The natural map between `⨁ i (j : α i), δ i j` and `Π₀ (i : Σ i, α i), δ i.1 i.2`, inverse of
`curry`. -/
/-
**DirectSum.sigmaUncurry** 是 Mathlib 中的一个定义，位于命名空间 `DirectSum`。
形式化陈述：sigmaUncurry : (⨁ (i) (j), δ i j) ->+ ⨁ i : Σ _i, _, δ i.1 i.2 where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural map between `⨁ i (j : α i), δ i j` and `Π₀ (i : Σ i, α i), δ i.1 i.2
`, inverse of
`curry`.
-/
def sigmaUncurry : (⨁ (i) (j), δ i j) →+ ⨁ i : Σ _i, _, δ i.1 i.2 where
  toFun := DFinsupp.sigmaUncurry
  map_zero' := DFinsupp.sigmaUncurry_zero
  map_add' := DFinsupp.sigmaUncurry_add

@[simp]
/-
**DirectSum.sigmaUncurry_apply** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：sigmaUncurry_apply (f : ⨁ (i) (j), δ i j) (i : ι) (j : α i) : sigmaUncurry
 f ⟨i, j⟩ = f i j
参数：f : ⨁ (i) (j), δ i j；i : ι；j : α i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.sigmaUncurry_apply`：sigmaUncurry_apply [forall i j, Zero (δ i j
)] (f : Π₀ (i) (j), δ i j) (i : ι) (j : α i) : sigmaUncurry f ⟨i, j⟩ = f i j
-/
theorem sigmaUncurry_apply (f : ⨁ (i) (j), δ i j) (i : ι) (j : α i) :
    sigmaUncurry f ⟨i, j⟩ = f i j :=
  DFinsupp.sigmaUncurry_apply f i j

/-- The natural map between `⨁ (i : Σ i, α i), δ i.1 i.2` and `⨁ i (j : α i), δ i j`. -/
/-
**DirectSum.sigmaCurryEquiv** 是 Mathlib 中的一个定义，位于命名空间 `DirectSum`。
形式化陈述：sigmaCurryEquiv : (⨁ i : Σ _i, _, δ i.1 i.2) ≃+ ⨁ (i) (j), δ i j
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural map between `⨁ (i : Σ i, α i), δ i.1 i.2` and `⨁ i (j : α i), δ i j`
.
-/
def sigmaCurryEquiv : (⨁ i : Σ _i, _, δ i.1 i.2) ≃+ ⨁ (i) (j), δ i j :=
  { sigmaCurry, DFinsupp.sigmaCurryEquiv with }

end Sigma

section SigmaFiber

variable {ι₁ ι₂ : Type v} [DecidableEq ι₂] (f : ι₁ → ι₂)
variable {β : ι₁ → Type w} [Π i, AddCommMonoid (β i)]

/-- The equivalence between a direct sum indexed by a type `ι₁` and the double sum indexed by a type
`ι₂` together with the fibres of a map `f : ι₁ → ι₂`. -/
/-
**DirectSum.sigmaFiberAddEquiv** 是 Mathlib 中的一个定义，位于命名空间 `DirectSum`。
形式化陈述：sigmaFiberAddEquiv : (⨁ i, β i) ≃+ ⨁ (j : ι₂) (i : { i : ι₁ // f i = j}), 
β ↑i
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The equivalence between a direct sum indexed by a type `ι₁` and the double sum i
ndexed by a type
`ι₂` together with the fibres of a map `f : ι₁ → ι₂`.
-/
def sigmaFiberAddEquiv : (⨁ i, β i) ≃+ ⨁ (j : ι₂) (i : { i : ι₁ // f i = j}), β ↑i :=
  (equivCongrLeft (Equiv.sigmaFiberEquiv f).symm).trans
    (sigmaCurryEquiv (δ := fun j ↦ (fun (i : { i : ι₁ // f i = j}) ↦ β i)))
/-
**DirectSum.sigmaFiberAddEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：sigmaFiberAddEquiv_apply (x : ⨁ i, β i) : sigmaFiberAddEquiv f x = sigmaCu
rry (equivCongrLeft (Equiv.sigmaFiberEquiv f).symm x)
参数：x : ⨁ i, β i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sigmaFiberAddEquiv_apply (x : ⨁ i, β i) :
    sigmaFiberAddEquiv f x = sigmaCurry (equivCongrLeft (Equiv.sigmaFiberEquiv f).symm x) := rfl

@[simp]
/-
**DirectSum.sigmaFiberAddEquiv_apply_apply** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`
。
形式化陈述：sigmaFiberAddEquiv_apply_apply (x : ⨁ i, β i) (j : ι₂) (i' : { i : ι₁ // f
 i = j}) : sigmaFiberAddEquiv f x j i' = x i'
参数：x : ⨁ i, β i；j : ι₂；i' : { i : ι₁ // f i = j}。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sigmaFiberAddEquiv_apply_apply (x : ⨁ i, β i) (j : ι₂) (i' : { i : ι₁ // f i = j}) :
    sigmaFiberAddEquiv f x j i' = x i' := rfl

@[simp]
/-
**DirectSum.sigmaFiberAddEquiv_of** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：sigmaFiberAddEquiv_of [DecidableEq ι₁] (i : ι₁) (x : β i) : sigmaFiberAddE
quiv f (of _ i x) = of _ (f i) (of _ ⟨i, rfl⟩ x)
参数：i : ι₁；x : β i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DirectSum.sigmaFiberAddEquiv_apply`：sigmaFiberAddEquiv_apply (x : ⨁ i, β
 i) : sigmaFiberAddEquiv f x = sigmaCurry (equivCongrLeft (Equiv.sigmaFiberEquiv
 f).symm x)
· 使用定理 `DirectSum.equivCongrLeft_of`：equivCongrLeft_of [DecidableEq ι] [Decidabl
eEq κ] (h : ι ≃ κ) (k : κ) (x : β (h.symm k)) : equivCongrLeft h (of β (h.symm k
) x) = of (fun k …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `DirectSum.sigmaCurry_of`：sigmaCurry_of [forall i : ι, DecidableEq (α i)]
 (k : (i : ι) × α i) (x : δ k.1 k.2) : sigmaCurry (of (fun k => δ k.1 k.2) k x) 
= of (fun i' …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sigmaFiberAddEquiv_of [DecidableEq ι₁] (i : ι₁) (x : β i) :
    sigmaFiberAddEquiv f (of _ i x) = of _ (f i) (of _ ⟨i, rfl⟩ x) :=
  let h := Equiv.sigmaFiberEquiv f
  let k : (j : ι₂) × {i₁ : ι₁ // f i₁ = j} := ⟨f i, ⟨i, rfl⟩⟩
  calc sigmaFiberAddEquiv f (of β (h k) x)
    _ = sigmaCurry (of (fun k : (j' : ι₂) × {i // f i = j'} ↦ β k.2) k x) := by
      rw [sigmaFiberAddEquiv_apply]
      exact congrArg sigmaCurry (equivCongrLeft_of (h := h.symm) _ _)
    _ = of _ k.1 (of _ k.2 x) := by simp

end SigmaFiber

/-- The canonical embedding from `⨁ i, A i` to `M` where `A` is a collection of `AddSubmonoid M`
indexed by `ι`.

When `S = Submodule _ M`, this is available as a `LinearMap`, `DirectSum.coe_linearMap`. -/
/-
**DirectSum.coeAddMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `DirectSum`。
形式化陈述：{ι : Type v} →   {M : Type u_1} →     {S : Type u_2} →       [DecidableEq 
ι] →         [inst : AddCommMonoid M] →           [inst_1 : SetLike S M] → [inst
_2 : AddSubmonoidClass S M] → (A : ι → S) → (DirectSum ι fun i => ↥(A i)) →+ M
参数：A : ι → S；DirectSum ι fun i => ↥(A i)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical embedding from `⨁ i, A i` to `M` where `A` is a collection of `Add
Submonoid M`
indexed by `ι`.

When `S = Submodule _ M`, this is available as a `LinearMap`, `DirectSum.coe_lin
earMap`.
-/
protected def coeAddMonoidHom {M S : Type*} [DecidableEq ι] [AddCommMonoid M] [SetLike S M]
    [AddSubmonoidClass S M] (A : ι → S) : (⨁ i, A i) →+ M :=
  toAddMonoid fun i => AddSubmonoidClass.subtype (A i)
/-
**DirectSum.coeAddMonoidHom_eq_dfinsuppSum** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`
。
形式化陈述：coeAddMonoidHom_eq_dfinsuppSum [DecidableEq ι] {M S : Type*} [DecidableEq 
M] [AddCommMonoid M] [SetLike S M] [AddSubmonoidClass S M] (A : ι -> S) (x : Dir
ectSum ι fun i => A i) : DirectSum.coeAddMonoidHom A x = DFinsupp.sum x fun i =>
 (fun x : A i => ↑x)
参数：A : ι -> S；x : DirectSum ι fun i => A i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.sumAddHom_apply`：sumAddHom_apply [forall i, AddZeroClass (β i)]
 [forall (i) (x : β i), Decidable (x != 0)] [AddCommMonoid γ] (φ : forall i, β i
 ->+ γ) (f : Π…
-/
theorem coeAddMonoidHom_eq_dfinsuppSum [DecidableEq ι]
    {M S : Type*} [DecidableEq M] [AddCommMonoid M]
    [SetLike S M] [AddSubmonoidClass S M] (A : ι → S) (x : DirectSum ι fun i => A i) :
    DirectSum.coeAddMonoidHom A x = DFinsupp.sum x fun i => (fun x : A i => ↑x) := by
  simp only [DirectSum.coeAddMonoidHom, toAddMonoid, DFinsupp.liftAddHom, AddEquiv.coe_mk]
  exact DFinsupp.sumAddHom_apply _ x

@[simp]
/-
**DirectSum.coeAddMonoidHom_of** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：coeAddMonoidHom_of {M S : Type*} [DecidableEq ι] [AddCommMonoid M] [SetLik
e S M] [AddSubmonoidClass S M] (A : ι -> S) (i : ι) (x : A i) : DirectSum.coeAdd
MonoidHom A (of (fun i => A i) i x) = x
参数：A : ι -> S；i : ι；x : A i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirectSum.toAddMonoid_of`：toAddMonoid_of (i) (x : β i) : toAddMonoid φ (
of β i x) = φ i x
-/
theorem coeAddMonoidHom_of {M S : Type*} [DecidableEq ι] [AddCommMonoid M] [SetLike S M]
    [AddSubmonoidClass S M] (A : ι → S) (i : ι) (x : A i) :
    DirectSum.coeAddMonoidHom A (of (fun i => A i) i x) = x :=
  toAddMonoid_of _ _ _
/-
**DirectSum.coe_of_apply** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：coe_of_apply {M S : Type*} [DecidableEq ι] [AddCommMonoid M] [SetLike S M]
 [AddSubmonoidClass S M] {A : ι -> S} (i j : ι) (x : A i) : (of (fun i => {x // 
x in A i}) i x j : M) = if i = j then x else 0
参数：i j : ι；x : A i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `Decidable.eq_or_ne`：Decidable.eq_or_ne {α : Sort*} (x y : α) [Decidable 
(x = y)] : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DirectSum.of_eq_same`：of_eq_same (i : ι) (x : β i) : (of _ i x) i = x
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `DirectSum.of_eq_of_ne`：of_eq_of_ne (i j : ι) (x : β i) (h : j != i) : (o
f _ i x) j = 0
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `ZeroMemClass.coe_zero`：∀ {A : Type u_3} {M₁ : Type u_4} [inst : SetLike 
A M₁] [inst_1 : Zero M₁] [hA : ZeroMemClass A M₁] (S' : A), ↑0 = 0
-/
theorem coe_of_apply {M S : Type*} [DecidableEq ι] [AddCommMonoid M] [SetLike S M]
    [AddSubmonoidClass S M] {A : ι → S} (i j : ι) (x : A i) :
    (of (fun i ↦ {x // x ∈ A i}) i x j : M) = if i = j then x else 0 := by
  obtain rfl | h := Decidable.eq_or_ne j i
  · rw [DirectSum.of_eq_same, if_pos rfl]
  · rw [DirectSum.of_eq_of_ne _ _ _ h, if_neg h.symm, ZeroMemClass.coe_zero, ZeroMemClass.coe_zero]

/-- The `DirectSum` formed by a collection of additive submonoids (or subgroups, or submodules) of
`M` is said to be internal if the canonical map `(⨁ i, A i) →+ M` is bijective.

For the alternate statement in terms of independence and spanning, see
`DirectSum.subgroup_isInternal_iff_iSupIndep_and_supr_eq_top` and
`DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top`. -/
/-
**DirectSum.IsInternal** 是 Mathlib 中的一个定义，位于命名空间 `DirectSum`。
形式化陈述：IsInternal {M S : Type*} [DecidableEq ι] [AddCommMonoid M] [SetLike S M] [
AddSubmonoidClass S M] (A : ι -> S) : Prop
参数：A : ι -> S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `DirectSum` formed by a collection of additive submonoids (or subgroups, or 
submodules) of
`M` is said to be internal if the canonical map `(⨁ i, A i) →+ M` is bijective.

For the alternate statement in terms of independence and spanning, see
`DirectSum.subgroup_isInternal_iff_iSupIndep_and_supr_eq_top` and
`DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top`.
-/
def IsInternal {M S : Type*} [DecidableEq ι] [AddCommMonoid M] [SetLike S M]
    [AddSubmonoidClass S M] (A : ι → S) : Prop :=
  Function.Bijective (DirectSum.coeAddMonoidHom A)
/-
**DirectSum.IsInternal.addSubmonoid_iSup_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `Direc
tSum.IsInternal`。
形式化陈述：∀ {ι : Type v} {M : Type u_1} [inst : DecidableEq ι] [inst_1 : AddCommMono
id M] (A : ι → AddSubmonoid M),   DirectSum.IsInternal A → iSup A = ⊤
参数：A : ι → AddSubmonoid M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubmonoid.instAddSubmonoidClass`：∀ {M : Type u_1} [inst : AddZeroClas
s M], AddSubmonoidClass (AddSubmonoid M) M
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddSubmonoid.iSup_eq_mrange_dfinsuppSumAddHom`：AddSubmonoid.iSup_eq_mran
ge_dfinsuppSumAddHom [AddCommMonoid γ] (S : ι -> AddSubmonoid γ) : iSup S = AddM
onoidHom.mrange (DFinsupp.sumAddHom…
· 使用定理 `AddMonoidHom.mrange_eq_top`：∀ {M : Type u_1} {N : Type u_2} [inst : AddZ
eroClass M] [inst_1 : AddZeroClass N] {F : Type u_4}   [inst_2 : FunLike F M N] 
[mc : AddMonoidH…
· 使用定理 `Function.Bijective.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → 
β}, Function.Bijective f → Function.Surjective f
-/
theorem IsInternal.addSubmonoid_iSup_eq_top {M : Type*} [DecidableEq ι] [AddCommMonoid M]
    (A : ι → AddSubmonoid M) (h : IsInternal A) : iSup A = ⊤ := by
  rw [AddSubmonoid.iSup_eq_mrange_dfinsuppSumAddHom, AddMonoidHom.mrange_eq_top]
  exact Function.Bijective.surjective h

variable {M S : Type*} [AddCommMonoid M] [SetLike S M] [AddSubmonoidClass S M]

set_option backward.isDefEq.respectTransparency false in
/-
**DirectSum.support_subset** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：support_subset [DecidableEq ι] [DecidableEq M] (A : ι -> S) (x : DirectSum
 ι fun i => A i) : (Function.support fun i => (x i : M)) subseteq ↑(DFinsupp.sup
port x)
参数：A : ι -> S；x : DirectSum ι fun i => A i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
-/
theorem support_subset [DecidableEq ι] [DecidableEq M] (A : ι → S) (x : DirectSum ι fun i => A i) :
    (Function.support fun i => (x i : M)) ⊆ ↑(DFinsupp.support x) := by
  intro m
  simp only [Function.mem_support, Finset.mem_coe, DFinsupp.mem_support_toFun, not_imp_not,
    ZeroMemClass.coe_eq_zero, imp_self]
/-
**DirectSum.hasFiniteSupport** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：hasFiniteSupport (A : ι -> S) (x : DirectSum ι fun i => A i) : (fun i => (
x i : M)).HasFiniteSupport
参数：A : ι -> S；x : DirectSum ι fun i => A i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
· 使用定理 `DirectSum.support_subset`：support_subset [DecidableEq ι] [DecidableEq M]
 (A : ι -> S) (x : DirectSum ι fun i => A i) : (Function.support fun i => (x i :
 M)) subseteq …
-/
theorem hasFiniteSupport (A : ι → S) (x : DirectSum ι fun i => A i) :
    (fun i => (x i : M)).HasFiniteSupport := by
  classical
  exact (DFinsupp.support x).finite_toSet.subset (DirectSum.support_subset _ x)

@[deprecated (since := "2026-03-03")] alias finite_support := hasFiniteSupport

section map

variable {ι : Type*} {α : ι → Type*} {β : ι → Type*} [∀ i, AddCommMonoid (α i)]
variable [∀ i, AddCommMonoid (β i)] (f : ∀ (i : ι), α i →+ β i)

/-- create a homomorphism from `⨁ i, α i` to `⨁ i, β i` by giving the component-wise map `f`. -/
/-
**DirectSum.map** 是 Mathlib 中的一个定义，位于命名空间 `DirectSum`。
形式化陈述：map : (⨁ i, α i) ->+ ⨁ i, β i
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
create a homomorphism from `⨁ i, α i` to `⨁ i, β i` by giving the component-wise
 map `f`.
-/
def map : (⨁ i, α i) →+ ⨁ i, β i := DFinsupp.mapRange.addMonoidHom f
/-
**DirectSum.map_of** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：∀ {ι : Type u_3} {α : ι → Type u_4} {β : ι → Type u_5} [inst : (i : ι) → A
ddCommMonoid (α i)]   [inst_1 : (i : ι) → AddCommMonoid (β i)] (f : (i : ι) → α 
i →+ β i) [inst_2 : DecidableEq ι] (i : ι) (x : α i),   (DirectSum.map f) ((Dire
ctSum.of α i) x) = (DirectSum.of β i) ((f i) x)
参数：i : ι；α i；i : ι；β i；f : (i : ι) → α i →+ β i；i : ι；x : α i；DirectSum.map f；(D
irectSum.of α i) x；DirectSum.of β i；(f i) x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.mapRange_single`：mapRange_single {f : forall i, β₁ i -> β₂ i} {
hf : forall i, f i 0 = 0} {i : ι} {b : β₁ i} : mapRange f hf (single i b) = sing
le i (f i b)
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
@[simp] lemma map_of [DecidableEq ι] (i : ι) (x : α i) : map f (of α i x) = of β i (f i x) :=
  DFinsupp.mapRange_single (hf := fun _ => map_zero _)
/-
**DirectSum.map_apply** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：∀ {ι : Type u_3} {α : ι → Type u_4} {β : ι → Type u_5} [inst : (i : ι) → A
ddCommMonoid (α i)]   [inst_1 : (i : ι) → AddCommMonoid (β i)] (f : (i : ι) → α 
i →+ β i) (i : ι) (x : DirectSum ι fun i => α i),   ((DirectSum.map f) x) i = (f
 i) (x i)
参数：i : ι；α i；i : ι；β i；f : (i : ι) → α i →+ β i；i : ι；x : DirectSum ι fun i => α
 i；(DirectSum.map f) x；f i；x i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.mapRange_apply`：mapRange_apply (f : forall i, β₁ i -> β₂ i) (hf
 : forall i, f i 0 = 0) (g : Π₀ i, β₁ i) (i : ι) : mapRange f hf g i = f i (g i)
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
@[simp] lemma map_apply (i : ι) (x : ⨁ i, α i) : map f x i = f i (x i) :=
  DFinsupp.mapRange_apply (hf := fun _ => map_zero _) _ _ _
/-
**DirectSum.map_id** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：∀ {ι : Type u_3} {α : ι → Type u_4} [inst : (i : ι) → AddCommMonoid (α i)]
,   (DirectSum.map fun i => AddMonoidHom.id (α i)) = AddMonoidHom.id (DirectSum 
ι fun i => α i)
参数：i : ι；α i；DirectSum.map fun i => AddMonoidHom.id (α i)；DirectSum ι fun i => α
 i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.mapRange.addMonoidHom_id`：∀ {ι : Type u} {β₂ : ι → Type v₂} [in
st : (i : ι) → AddZeroClass (β₂ i)],   (DFinsupp.mapRange.addMonoidHom fun i => 
AddMonoidHom.id (β₂ i))…
-/
@[simp] lemma map_id :
    (map (fun i ↦ AddMonoidHom.id (α i))) = AddMonoidHom.id (⨁ i, α i) :=
  DFinsupp.mapRange.addMonoidHom_id
/-
**DirectSum.map_comp** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：∀ {ι : Type u_3} {α : ι → Type u_4} {β : ι → Type u_5} [inst : (i : ι) → A
ddCommMonoid (α i)]   [inst_1 : (i : ι) → AddCommMonoid (β i)] (f : (i : ι) → α 
i →+ β i) {γ : ι → Type u_6}   [inst_2 : (i : ι) → AddCommMonoid (γ i)] (g : (i 
: ι) → β i →+ γ i),   (DirectSum.map fun i => (g i).comp (f i)) = (DirectSum.map
 g).comp (DirectSum.map f)
参数：i : ι；α i；i : ι；β i；f : (i : ι) → α i →+ β i；i : ι；γ i；g : (i : ι) → β i →+ γ
 i；DirectSum.map fun i => (g i).comp (f i)；DirectSum.map g；DirectSum.map f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.mapRange.addMonoidHom_comp`：∀ {ι : Type u} {β : ι → Type v} {β₁
 : ι → Type v₁} {β₂ : ι → Type v₂} [inst : (i : ι) → AddZeroClass (β i)]   [inst
_1 : (i : ι) → AddZeroCla…
-/
@[simp] lemma map_comp {γ : ι → Type*} [∀ i, AddCommMonoid (γ i)]
    (g : ∀ (i : ι), β i →+ γ i) :
    (map (fun i ↦ (g i).comp (f i))) = (map g).comp (map f) :=
  DFinsupp.mapRange.addMonoidHom_comp _ _
/-
**DirectSum.map_injective** 是 Mathlib 中的一个引理，位于命名空间 `DirectSum`。
形式化陈述：map_injective : Function.Injective (map f) ↔ forall i, Function.Injective 
(f i)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.mapRange_injective`：mapRange_injective (f : forall i, β₁ i -> β
₂ i) (hf : forall i, f i 0 = 0) : Function.Injective (mapRange f hf) ↔ forall i,
 Function.Injecti…
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
lemma map_injective : Function.Injective (map f) ↔ ∀ i, Function.Injective (f i) := by
  exact DFinsupp.mapRange_injective (hf := fun _ ↦ map_zero _)
/-
**DirectSum.map_surjective** 是 Mathlib 中的一个引理，位于命名空间 `DirectSum`。
形式化陈述：map_surjective : Function.Surjective (map f) ↔ (forall i, Function.Surject
ive (f i))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.mapRange_surjective`：mapRange_surjective (f : forall i, β₁ i ->
 β₂ i) (hf : forall i, f i 0 = 0) : Function.Surjective (mapRange f hf) ↔ forall
 i, Function.Surje…
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
lemma map_surjective : Function.Surjective (map f) ↔ (∀ i, Function.Surjective (f i)) := by
  exact DFinsupp.mapRange_surjective (hf := fun _ ↦ map_zero _)
/-
**DirectSum.map_eq_iff** 是 Mathlib 中的一个引理，位于命名空间 `DirectSum`。
形式化陈述：map_eq_iff (x y : ⨁ i, α i) : map f x = map f y ↔ forall i, f i (x i) = f 
i (y i)
参数：x y : ⨁ i, α i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `DirectSum.map_apply`：∀ {ι : Type u_3} {α : ι → Type u_4} {β : ι → Type u
_5} [inst : (i : ι) → AddCommMonoid (α i)]   [inst_1 : (i : ι) → AddCommMonoid (
β i)] (f …
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma map_eq_iff (x y : ⨁ i, α i) :
    map f x = map f y ↔ ∀ i, f i (x i) = f i (y i) := by
  simp_rw [DirectSum.ext_iff, map_apply]

end map

end DirectSum

set_option backward.isDefEq.respectTransparency false in
/-- The canonical isomorphism of a finite direct sum of additive commutative monoids
and the corresponding finite product. -/
/-
**DirectSum.addEquivProd** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：DirectSum.addEquivProd {ι : Type*} [Fintype ι] (G : ι -> Type*) [(i : ι) -
> AddCommMonoid (G i)] : DirectSum ι G ≃+ ((i : ι) -> G i)
参数：G : ι -> Type*；i : ι；G i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical isomorphism of a finite direct sum of additive commutative monoids
and the corresponding finite product.
-/
def DirectSum.addEquivProd {ι : Type*} [Fintype ι] (G : ι → Type*) [(i : ι) → AddCommMonoid (G i)] :
    DirectSum ι G ≃+ ((i : ι) → G i) :=
  ⟨DFinsupp.equivFunOnFintype, fun g h ↦ funext fun _ ↦ by
    simp only [DFinsupp.equivFunOnFintype, Equiv.toFun_as_coe, Equiv.coe_fn_mk,
      ← DFinsupp.add_apply, Pi.add_apply]⟩
