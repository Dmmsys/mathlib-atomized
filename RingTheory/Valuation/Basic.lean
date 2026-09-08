/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Johan Commelin, Patrick Massot, Filippo A. E. Nuccio
-/
module

public import Mathlib.Algebra.Order.GroupWithZero.Range
public import Mathlib.Algebra.Order.Hom.Monoid
public import Mathlib.Algebra.Order.Ring.Basic
public import Mathlib.Algebra.Ring.Torsion
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.Tactic.TFAE

/-!

# The basics of valuation theory.

The basic theory of valuations (non-archimedean norms) on a commutative ring,
following T. Wedhorn's unpublished notes “Adic Spaces” ([wedhorn_adic]).

The definition of a valuation we use here is Definition 1.22 of [wedhorn_adic].
A valuation on a ring `R` is a monoid homomorphism `v` to a linearly ordered
commutative monoid with zero, that in addition satisfies the following two axioms:
* `v 0 = 0`
* `∀ x y, v (x + y) ≤ max (v x) (v y)`

`Valuation R Γ₀` is the type of valuations `R → Γ₀`, with a coercion to the underlying
function. If `v` is a valuation from `R` to `Γ₀` then the induced group
homomorphism `Units(R) → Γ₀` is called `unit_map v`.

The equivalence "relation" `IsEquiv v₁ v₂ : Prop` defined in 1.27 of [wedhorn_adic] is not strictly
speaking a relation, because `v₁ : Valuation R Γ₁` and `v₂ : Valuation R Γ₂` might
not have the same type. This corresponds in ZFC to the set-theoretic difficulty
that the class of all valuations (as `Γ₀` varies) on a ring `R` is not a set.
The "relation" is however reflexive, symmetric and transitive in the obvious
sense. Note that we use 1.27(iii) of [wedhorn_adic] as the definition of equivalence.

## Main definitions

* `Valuation R Γ₀`, the type of valuations on `R` with values in `Γ₀`
* `Valuation.IsNontrivial` is the class of non-trivial valuations, namely those for which there
  is an element in the ring whose valuation is `≠ 0` and `≠ 1`.
* `Valuation.IsEquiv`, the heterogeneous equivalence relation on valuations
* `Valuation.supp`, the support of a valuation
* `orderMonoidIso` is the ordered isomorphism between the value groups of two equivalent valuations.

* `AddValuation R Γ₀`, the type of additive valuations on `R` with values in a
  linearly ordered additive commutative group with a top element, `Γ₀`.

## Implementation Details

`AddValuation R Γ₀` is implemented as `Valuation R (Multiplicative Γ₀)ᵒᵈ`.

## Notation

In the `WithZero` locale, `Mᵐ⁰` is a shorthand for `WithZero (Multiplicative M)`.

## TODO

If ever someone extends `Valuation`, we should fully comply with `DFunLike` by migrating the
boilerplate lemmas to `ValuationClass`.
-/

@[expose] public section

open Function Ideal

noncomputable section

variable {K F R : Type*} [DivisionRing K]

section

variable (F R) (Γ₀ : Type*) [LinearOrderedCommMonoidWithZero Γ₀] [Ring R]

/-- The type of `Γ₀`-valued valuations on `R`.

When you extend this structure, make sure to extend `ValuationClass`. -/
/-
**Valuation** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u_3) → (Γ₀ : Type u_4) → [LinearOrderedCommMonoidWithZero Γ₀] → 
[Ring R] → Type (max u_3 u_4)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of `Γ₀`-valued valuations on `R`.

When you extend this structure, make sure to extend `ValuationClass`.
-/
structure Valuation extends R →*₀ Γ₀ where
  /-- The valuation of a sum is less than or equal to the maximum of the valuations. -/
  map_add_le_max' : ∀ x y, toFun (x + y) ≤ max (toFun x) (toFun y)

/-- `ValuationClass F α β` states that `F` is a type of valuations.

You should also extend this typeclass when you extend `Valuation`. -/
/-
**ValuationClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_7) →   (R : outParam (Type u_5)) →     (Γ₀ : outParam (Type u_
6)) → [LinearOrderedCommMonoidWithZero Γ₀] → [Ring R] → [FunLike F R Γ₀] → Prop
参数：Type u_5；Type u_6。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ValuationClass F α β` states that `F` is a type of valuations.

You should also extend this typeclass when you extend `Valuation`.
-/
class ValuationClass (F) (R Γ₀ : outParam Type*) [LinearOrderedCommMonoidWithZero Γ₀] [Ring R]
    [FunLike F R Γ₀] : Prop
  extends MonoidWithZeroHomClass F R Γ₀ where
  /-- The valuation of a sum is less than or equal to the maximum of the valuations. -/
  map_add_le_max (f : F) (x y : R) : f (x + y) ≤ max (f x) (f y)

export ValuationClass (map_add_le_max)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [FunLike F R Γ₀] [ValuationClass F R Γ₀] : CoeTC F (Valuation R Γ₀) :=
  ⟨fun f =>
    { toFun := f
      map_one' := map_one f
      map_zero' := map_zero f
      map_mul' := map_mul f
      map_add_le_max' := map_add_le_max f }⟩

end

namespace Valuation

variable {Γ₀ : Type*} {Γ'₀ : Type*} {Γ''₀ : Type*}

section Basic

variable [Ring R]

section Monoid

variable [LinearOrderedCommMonoidWithZero Γ₀] [LinearOrderedCommMonoidWithZero Γ'₀]
  [LinearOrderedCommMonoidWithZero Γ''₀]

/-
**Valuation.toMonoidWithZeroHom_injective** 是 Mathlib 中的一个引理，位于命名空间 `Valuation`。
形式化陈述：toMonoidWithZeroHom_injective : (toMonoidWithZeroHom : Valuation R Γ₀ -> R
 ->*₀ Γ₀).Injective
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Valuation.map_add_le_max'`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : Line
arOrderedCommMonoidWithZero Γ₀] [inst_1 : Ring R] (self : Valuation R Γ₀)   (x y
 : R),   (↑self…
-/
lemma toMonoidWithZeroHom_injective :
    (toMonoidWithZeroHom : Valuation R Γ₀ → R →*₀ Γ₀).Injective := by
  rintro ⟨f, _⟩ g hfg; congr!
/-
**Valuation.** 是 Mathlib 中的一个实例，位于命名空间 `Valuation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FunLike (Valuation R Γ₀) R Γ₀ where
  coe f := f.toMonoidWithZeroHom
  coe_injective := DFunLike.coe_injective.comp toMonoidWithZeroHom_injective
/-
**Valuation.** 是 Mathlib 中的一个实例，位于命名空间 `Valuation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ValuationClass (Valuation R Γ₀) R Γ₀ where
  map_mul f := f.map_mul'
  map_one f := f.map_one'
  map_zero f := f.map_zero'
  map_add_le_max f := f.map_add_le_max'

@[simp]
/-
**Valuation.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`。
形式化陈述：coe_mk (f : R ->*₀ Γ₀) (h) : ⇑(Valuation.mk f h) = f
参数：f : R ->*₀ Γ₀；h。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mk (f : R →*₀ Γ₀) (h) : ⇑(Valuation.mk f h) = f := rfl
/-
**Valuation.toFun_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`。
形式化陈述：toFun_eq_coe (v : Valuation R Γ₀) : v.toFun = v
参数：v : Valuation R Γ₀。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toFun_eq_coe (v : Valuation R Γ₀) : v.toFun = v := rfl

@[simp]
/-
**Valuation.toMonoidWithZeroHom_coe_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`
。
形式化陈述：toMonoidWithZeroHom_coe_eq_coe (v : Valuation R Γ₀) : (v.toMonoidWithZeroH
om : R -> Γ₀) = v
参数：v : Valuation R Γ₀。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toMonoidWithZeroHom_coe_eq_coe (v : Valuation R Γ₀) :
    (v.toMonoidWithZeroHom : R → Γ₀) = v := rfl

@[ext]
/-
**Valuation.ext** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`。
形式化陈述：ext {v₁ v₂ : Valuation R Γ₀} (h : forall r, v₁ r = v₂ r) : v₁ = v₂
参数：h : forall r, v₁ r = v₂ r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext {v₁ v₂ : Valuation R Γ₀} (h : ∀ r, v₁ r = v₂ r) : v₁ = v₂ :=
  DFunLike.ext _ _ h

variable (v : Valuation R Γ₀)

@[simp]
/-
**Valuation.coe_ofClass** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`。
形式化陈述：coe_ofClass : ⇑(MonoidWithZeroHom.ofClass v) = v
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
-/
theorem coe_ofClass : ⇑(MonoidWithZeroHom.ofClass v) = v := rfl
/-
**Valuation.map_zero** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`。
形式化陈述：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : Ring R] [inst_1 : LinearOrderedCo
mmMonoidWithZero Γ₀] (v : Valuation R Γ₀),   v 0 = 0
参数：v : Valuation R Γ₀。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ZeroHom.map_zero'`：∀ {M : Type u_10} {N : Type u_11} [inst : Zero M] [in
st_1 : Zero N] (self : ZeroHom M N), self.toFun 0 = 0
-/
protected theorem map_zero : v 0 = 0 :=
  v.map_zero'
/-
**Valuation.map_one** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`。
形式化陈述：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : Ring R] [inst_1 : LinearOrderedCo
mmMonoidWithZero Γ₀] (v : Valuation R Γ₀),   v 1 = 1
参数：v : Valuation R Γ₀。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHom.map_one'`：∀ {α : Type u_7} {β : Type u_8} [inst : MulZ
eroOneClass α] [inst_1 : MulZeroOneClass β] (self : α →*₀ β),   (↑self).toFun 1 
= 1
-/
protected theorem map_one : v 1 = 1 :=
  v.map_one'
/-
**Valuation.map_mul** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`。
形式化陈述：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : Ring R] [inst_1 : LinearOrderedCo
mmMonoidWithZero Γ₀] (v : Valuation R Γ₀)   (x y : R), v (x * y) = v x * v y
参数：v : Valuation R Γ₀；x y : R；x * y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHom.map_mul'`：∀ {α : Type u_7} {β : Type u_8} [inst : MulZ
eroOneClass α] [inst_1 : MulZeroOneClass β] (self : α →*₀ β) (x y : α),   (↑self
).toFun (x * y) …
-/
protected theorem map_mul : ∀ x y, v (x * y) = v x * v y :=
  v.map_mul'

-- `simp`-normal form is `map_add'`
/-
**Valuation.map_add** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`。
形式化陈述：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : Ring R] [inst_1 : LinearOrderedCo
mmMonoidWithZero Γ₀] (v : Valuation R Γ₀)   (x y : R), v (x + y) ≤ max (v x) (v 
y)
参数：v : Valuation R Γ₀；x y : R；x + y；v x；v y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Valuation.map_add_le_max'`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : Line
arOrderedCommMonoidWithZero Γ₀] [inst_1 : Ring R] (self : Valuation R Γ₀)   (x y
 : R),   (↑self…
-/
protected theorem map_add : ∀ x y, v (x + y) ≤ max (v x) (v y) :=
  v.map_add_le_max'

@[simp]
/-
**Valuation.map_add'** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`。
形式化陈述：map_add' : forall x y, v (x + y) <= v x ∨ v (x + y) <= v y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `le_max_iff`：le_max_iff : a <= max b c ↔ a <= b ∨ a <= c
· 使用定理 `Valuation.map_add`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : Ring R] [ins
t_1 : LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation R Γ₀)   (x y : R), v (x
 + y) ≤…
-/
theorem map_add' : ∀ x y, v (x + y) ≤ v x ∨ v (x + y) ≤ v y := by
  intro x y
  rw [← le_max_iff]
  apply v.map_add
/-
**Valuation.map_add_le** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`。
形式化陈述：map_add_le {x y g} (hx : v x <= g) (hy : v y <= g) : v (x + y) <= g
参数：hx : v x <= g；hy : v y <= g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Valuation.map_add`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : Ring R] [ins
t_1 : LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation R Γ₀)   (x y : R), v (x
 + y) ≤…
· 使用定理 `max_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, a ≤ c → b ≤
 c → max a b ≤ c
-/
theorem map_add_le {x y g} (hx : v x ≤ g) (hy : v y ≤ g) : v (x + y) ≤ g :=
  le_trans (v.map_add x y) <| max_le hx hy
/-
**Valuation.map_add_lt** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`。
形式化陈述：map_add_lt {x y g} (hx : v x < g) (hy : v y < g) : v (x + y) < g
参数：hx : v x < g；hy : v y < g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `Valuation.map_add`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : Ring R] [ins
t_1 : LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation R Γ₀)   (x y : R), v (x
 + y) ≤…
· 使用定理 `max_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, b < a → c <
 a → max b c < a
-/
theorem map_add_lt {x y g} (hx : v x < g) (hy : v y < g) : v (x + y) < g :=
  lt_of_le_of_lt (v.map_add x y) <| max_lt hx hy
/-
**Valuation.map_sum_le** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`。
形式化陈述：map_sum_le {ι : Type*} {s : Finset ι} {f : ι -> R} {g : Γ₀} (hf : forall i
 in s, v (f i) <= g) : v (∑ i in s, f i) <= g
参数：hf : forall i in s, v (f i) <= g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Valuation.map_zero`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : Ring R] [in
st_1 : LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation R Γ₀),   v 0 = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `Valuation.map_add_le`：map_add_le {x y g} (hx : v x <= g) (hy : v y <= g)
 : v (x + y) <= g
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Finset.forall_mem_insert`：forall_mem_insert (a : α) (s : Finset α) (p : 
α -> Prop) : (forall x, x in insert a s -> p x) ↔ p a ∧ forall x, x in s -> p x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem map_sum_le {ι : Type*} {s : Finset ι} {f : ι → R} {g : Γ₀} (hf : ∀ i ∈ s, v (f i) ≤ g) :
    v (∑ i ∈ s, f i) ≤ g := by
  classical
  refine Finset.induction_on s (fun _ => v.map_zero ▸ zero_le) (fun a s has ih hf => ?_) hf
  rw [Finset.forall_mem_insert] at hf; rw [Finset.sum_insert has]
  exact v.map_add_le hf.1 (ih hf.2)
/-
**Valuation.map_sum_lt** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`。
形式化陈述：map_sum_lt {ι : Type*} {s : Finset ι} {f : ι -> R} {g : Γ₀} (hg : g != 0) 
(hf : forall i in s, v (f i) < g) : v (∑ i in s, f i) < g
参数：hg : g != 0；hf : forall i in s, v (f i) < g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `zero_lt_iff`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_1 : 
Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Valuation.map_zero`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : Ring R] [in
st_1 : LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation R Γ₀),   v 0 = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `Valuation.map_add_lt`：map_add_lt {x y g} (hx : v x < g) (hy : v y < g) :
 v (x + y) < g
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Finset.forall_mem_insert`：forall_mem_insert (a : α) (s : Finset α) (p : 
α -> Prop) : (forall x, x in insert a s -> p x) ↔ p a ∧ forall x, x in s -> p x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem map_sum_lt {ι : Type*} {s : Finset ι} {f : ι → R} {g : Γ₀} (hg : g ≠ 0)
    (hf : ∀ i ∈ s, v (f i) < g) : v (∑ i ∈ s, f i) < g := by
  classical
  refine
    Finset.induction_on s (fun _ => v.map_zero ▸ (zero_lt_iff.2 hg))
      (fun a s has ih hf => ?_) hf
  rw [Finset.forall_mem_insert] at hf; rw [Finset.sum_insert has]
  exact v.map_add_lt hf.1 (ih hf.2)
/-
**Valuation.map_sum_lt'** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`。
形式化陈述：map_sum_lt' {ι : Type*} {s : Finset ι} {f : ι -> R} {g : Γ₀} (hg : 0 < g) 
(hf : forall i in s, v (f i) < g) : v (∑ i in s, f i) < g
参数：hg : 0 < g；hf : forall i in s, v (f i) < g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Valuation.map_sum_lt`：map_sum_lt {ι : Type*} {s : Finset ι} {f : ι -> R}
 {g : Γ₀} (hg : g != 0) (hf : forall i in s, v (f i) < g) : v (∑ i in s, f i) < 
g
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
-/
theorem map_sum_lt' {ι : Type*} {s : Finset ι} {f : ι → R} {g : Γ₀} (hg : 0 < g)
    (hf : ∀ i ∈ s, v (f i) < g) : v (∑ i ∈ s, f i) < g :=
  v.map_sum_lt (ne_of_gt hg) hf
/-
**Valuation.map_pow** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`。
形式化陈述：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : Ring R] [inst_1 : LinearOrderedCo
mmMonoidWithZero Γ₀] (v : Valuation R Γ₀)   (x : R) (n : ℕ), v (x ^ n) = v x ^ n
参数：v : Valuation R Γ₀；x : R；n : ℕ；x ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.map_pow`：∀ {M : Type u_4} {N : Type u_5} [inst : Monoid M] [in
st_1 : Monoid N] (f : M →* N) (a : M) (n : ℕ), f (a ^ n) = f a ^ n
-/
protected theorem map_pow : ∀ (x) (n : ℕ), v (x ^ n) = v x ^ n :=
  v.toMonoidWithZeroHom.toMonoidHom.map_pow

-- The following definition is not an instance, because we have more than one `v` on a given `R`.
-- In addition, type class inference would not be able to infer `v`.
/-- A valuation gives a preorder on the underlying ring. -/
@[instance_reducible]
/-
**Valuation.toPreorder** 是 Mathlib 中的一个定义，位于命名空间 `Valuation`。
形式化陈述：toPreorder : Preorder R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A valuation gives a preorder on the underlying ring.
-/
def toPreorder : Preorder R :=
  Preorder.lift v

/-- If `v` is a valuation on a division ring then `v(x) = 0` iff `x = 0`. -/
/-
**Valuation.zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`。
形式化陈述：zero_iff [Nontrivial Γ₀] (v : Valuation K Γ₀) {x : K} : v x = 0 ↔ x = 0
参数：v : Valuation K Γ₀。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_eq_zero`：map_eq_zero : f a = 0 ↔ a = 0
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀

--- 原说明 ---
If `v` is a valuation on a division ring then `v(x) = 0` iff `x = 0`.
-/
theorem zero_iff [Nontrivial Γ₀] (v : Valuation K Γ₀) {x : K} : v x = 0 ↔ x = 0 :=
  map_eq_zero v
/-
**Valuation.ne_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`。
形式化陈述：ne_zero_iff [Nontrivial Γ₀] (v : Valuation K Γ₀) {x : K} : v x != 0 ↔ x !=
 0
参数：v : Valuation K Γ₀。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_ne_zero`：map_ne_zero : f a != 0 ↔ a != 0
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
-/
theorem ne_zero_iff [Nontrivial Γ₀] (v : Valuation K Γ₀) {x : K} : v x ≠ 0 ↔ x ≠ 0 :=
  map_ne_zero v
/-
**Valuation.pos_iff** 是 Mathlib 中的一个引理，位于命名空间 `Valuation`。
形式化陈述：pos_iff [Nontrivial Γ₀] (v : Valuation K Γ₀) {x : K} : 0 < v x ↔ x != 0
参数：v : Valuation K Γ₀。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_lt_iff`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_1 : 
Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Valuation.ne_zero_iff`：ne_zero_iff [Nontrivial Γ₀] (v : Valuation K Γ₀) 
{x : K} : v x != 0 ↔ x != 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma pos_iff [Nontrivial Γ₀] (v : Valuation K Γ₀) {x : K} : 0 < v x ↔ x ≠ 0 := by
  rw [zero_lt_iff, ne_zero_iff]
/-
**Valuation.unit_map_eq** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`。
形式化陈述：unit_map_eq (u : Rˣ) : (Units.map (v : R ->* Γ₀) u : Γ₀) = v u
参数：u : Rˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
-/
theorem unit_map_eq (u : Rˣ) : (Units.map (v : R →* Γ₀) u : Γ₀) = v u :=
  rfl
/-
**Valuation.ne_zero_of_unit** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`。
形式化陈述：ne_zero_of_unit [Nontrivial Γ₀] (v : Valuation K Γ₀) (x : Kˣ) : v x != (0 
: Γ₀)
参数：v : Valuation K Γ₀；x : Kˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Units.ne_zero`：ne_zero [Nontrivial M₀] (u : M₀ˣ) : (u : M₀) != 0
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
-/
theorem ne_zero_of_unit [Nontrivial Γ₀] (v : Valuation K Γ₀) (x : Kˣ) : v x ≠ (0 : Γ₀) := by
  simp only [ne_eq, Valuation.zero_iff, Units.ne_zero x, not_false_iff]
/-
**Valuation.ne_zero_of_isUnit** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`。
形式化陈述：ne_zero_of_isUnit [Nontrivial Γ₀] (v : Valuation K Γ₀) (x : K) (hx : IsUni
t x) : v x != (0 : Γ₀)
参数：v : Valuation K Γ₀；x : K；hx : IsUnit x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `Valuation.ne_zero_of_unit`：ne_zero_of_unit [Nontrivial Γ₀] (v : Valuatio
n K Γ₀) (x : Kˣ) : v x != (0 : Γ₀)
-/
theorem ne_zero_of_isUnit [Nontrivial Γ₀] (v : Valuation K Γ₀) (x : K) (hx : IsUnit x) :
    v x ≠ (0 : Γ₀) := by
  simpa [hx.choose_spec] using ne_zero_of_unit v hx.choose

/-- A ring homomorphism `S → R` induces a map `Valuation R Γ₀ → Valuation S Γ₀`. -/
/-
**Valuation.comap** 是 Mathlib 中的一个定义，位于命名空间 `Valuation`。
形式化陈述：comap {S : Type*} [Ring S] (f : S ->+* R) (v : Valuation R Γ₀) : Valuation
 S Γ₀
参数：f : S ->+* R；v : Valuation R Γ₀。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A ring homomorphism `S → R` induces a map `Valuation R Γ₀ → Valuation S Γ₀`.
-/
def comap {S : Type*} [Ring S] (f : S →+* R) (v : Valuation R Γ₀) : Valuation S Γ₀ :=
  { v.toMonoidWithZeroHom.comp f.toMonoidWithZeroHom with
    toFun := v ∘ f
    map_add_le_max' := fun x y => by simp }

@[simp]
/-
**Valuation.comap_apply** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`。
形式化陈述：comap_apply {S : Type*} [Ring S] (f : S ->+* R) (v : Valuation R Γ₀) (s : 
S) : v.comap f s = v (f s)
参数：f : S ->+* R；v : Valuation R Γ₀；s : S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comap_apply {S : Type*} [Ring S] (f : S →+* R) (v : Valuation R Γ₀) (s : S) :
    v.comap f s = v (f s) := rfl

@[simp]
/-
**Valuation.comap_id** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`。
形式化陈述：comap_id : v.comap (RingHom.id R) = v
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Valuation.ext`：ext {v₁ v₂ : Valuation R Γ₀} (h : forall r, v₁ r = v₂ r) 
: v₁ = v₂
-/
theorem comap_id : v.comap (RingHom.id R) = v :=
  ext fun _r => rfl
/-
**Valuation.comap_comp** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`。
形式化陈述：comap_comp {S₁ : Type*} {S₂ : Type*} [Ring S₁] [Ring S₂] (f : S₁ ->+* S₂) 
(g : S₂ ->+* R) : v.comap (g.comp f) = (v.comap g).comap f
参数：f : S₁ ->+* S₂；g : S₂ ->+* R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Valuation.ext`：ext {v₁ v₂ : Valuation R Γ₀} (h : forall r, v₁ r = v₂ r) 
: v₁ = v₂
-/
theorem comap_comp {S₁ : Type*} {S₂ : Type*} [Ring S₁] [Ring S₂] (f : S₁ →+* S₂) (g : S₂ →+* R) :
    v.comap (g.comp f) = (v.comap g).comap f :=
  ext fun _r => rfl

/-- A `≤`-preserving group homomorphism `Γ₀ → Γ'₀` induces a map `Valuation R Γ₀ → Valuation R Γ'₀`.
-/
/-
**Valuation.map** 是 Mathlib 中的一个定义，位于命名空间 `Valuation`。
形式化陈述：map (f : Γ₀ ->*₀ Γ'₀) (hf : Monotone f) (v : Valuation R Γ₀) : Valuation R
 Γ'₀
参数：f : Γ₀ ->*₀ Γ'₀；hf : Monotone f；v : Valuation R Γ₀。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `≤`-preserving group homomorphism `Γ₀ → Γ'₀` induces a map `Valuation R Γ₀ → V
aluation R Γ'₀`.
-/
def map (f : Γ₀ →*₀ Γ'₀) (hf : Monotone f) (v : Valuation R Γ₀) : Valuation R Γ'₀ :=
  { MonoidWithZeroHom.comp f v.toMonoidWithZeroHom with
    toFun := f ∘ v
    map_add_le_max' := fun r s =>
      calc
        f (v (r + s)) ≤ f (max (v r) (v s)) := hf (v.map_add r s)
        _ = max (f (v r)) (f (v s)) := hf.map_max
         }

@[simp]
/-
**Valuation.map_apply** 是 Mathlib 中的一个引理，位于命名空间 `Valuation`。
形式化陈述：map_apply (f : Γ₀ ->*₀ Γ'₀) (hf : Monotone f) (v : Valuation R Γ₀) (r : R)
 : v.map f hf r = f (v r)
参数：f : Γ₀ ->*₀ Γ'₀；hf : Monotone f；v : Valuation R Γ₀；r : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map_apply (f : Γ₀ →*₀ Γ'₀) (hf : Monotone f) (v : Valuation R Γ₀) (r : R) :
    v.map f hf r = f (v r) := rfl

/-- Two valuations on `R` are defined to be equivalent if they induce the same preorder on `R`. -/
/-
**Valuation.IsEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Valuation`。
形式化陈述：IsEquiv (v₁ : Valuation R Γ₀) (v₂ : Valuation R Γ'₀) : Prop
参数：v₁ : Valuation R Γ₀；v₂ : Valuation R Γ'₀。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Two valuations on `R` are defined to be equivalent if they induce the same preor
der on `R`.
-/
def IsEquiv (v₁ : Valuation R Γ₀) (v₂ : Valuation R Γ'₀) : Prop :=
  ∀ r s, v₁ r ≤ v₁ s ↔ v₂ r ≤ v₂ s

@[simp]
/-
**Valuation.map_neg** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`。
形式化陈述：map_neg (x : R) : v (-x) = v x
参数：x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.map_neg`：∀ {R : Type u_1} {M : Type u_2} [inst : Ring R] [inst
_1 : Monoid M] [IsMulTorsionFree M] (f : R →* M) (x : R),   f (-x) = f x
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsMulTorsionFree`：∀ {α : Type u_1} [in
st : LinearOrderedCommMonoidWithZero α], IsMulTorsionFree α
-/
theorem map_neg (x : R) : v (-x) = v x :=
  v.toMonoidWithZeroHom.toMonoidHom.map_neg x
/-
**Valuation.map_sub_swap** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`。
形式化陈述：map_sub_swap (x y : R) : v (x - y) = v (y - x)
参数：x y : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MonoidHom.map_sub_swap`：map_sub_swap (x y : R) : f (x - y) = f (y - x)
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsMulTorsionFree`：∀ {α : Type u_1} [in
st : LinearOrderedCommMonoidWithZero α], IsMulTorsionFree α
-/
theorem map_sub_swap (x y : R) : v (x - y) = v (y - x) :=
  v.toMonoidWithZeroHom.toMonoidHom.map_sub_swap x y
/-
**Valuation.map_sub** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`。
形式化陈述：map_sub (x y : R) : v (x - y) <= max (v x) (v y)
参数：x y : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Valuation.map_add`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : Ring R] [ins
t_1 : LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation R Γ₀)   (x y : R), v (x
 + y) ≤…
· 使用定理 `Valuation.map_neg`：map_neg (x : R) : v (-x) = v x
-/
theorem map_sub (x y : R) : v (x - y) ≤ max (v x) (v y) :=
  calc
    v (x - y) = v (x + -y) := by rw [sub_eq_add_neg]
    _ ≤ max (v x) (v <| -y) := v.map_add _ _
    _ = max (v x) (v y) := by rw [map_neg]
/-
**Valuation.map_sub_le** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`。
形式化陈述：map_sub_le {x y g} (hx : v x <= g) (hy : v y <= g) : v (x - y) <= g
参数：hx : v x <= g；hy : v y <= g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Valuation.map_add_le`：map_add_le {x y g} (hx : v x <= g) (hy : v y <= g)
 : v (x + y) <= g
· 使用定理 `Eq.trans_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ c →
 a ≤ c
· 使用定理 `Valuation.map_neg`：map_neg (x : R) : v (-x) = v x
-/
theorem map_sub_le {x y g} (hx : v x ≤ g) (hy : v y ≤ g) : v (x - y) ≤ g := by
  rw [sub_eq_add_neg]
  exact v.map_add_le hx <| (v.map_neg y).trans_le hy
/-
**Valuation.map_sub_lt** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`。
形式化陈述：map_sub_lt {x y : R} {g : Γ₀} (hx : v x < g) (hy : v y < g) : v (x - y) < 
g
参数：hx : v x < g；hy : v y < g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Valuation.map_add_lt`：map_add_lt {x y g} (hx : v x < g) (hy : v y < g) :
 v (x + y) < g
· 使用定理 `Eq.trans_lt`：∀ {α : Type u_1} {a b c : α} [inst : LT α], a = b → b < c →
 a < c
· 使用定理 `Valuation.map_neg`：map_neg (x : R) : v (-x) = v x
-/
theorem map_sub_lt {x y : R} {g : Γ₀} (hx : v x < g) (hy : v y < g) : v (x - y) < g := by
  rw [sub_eq_add_neg]
  exact v.map_add_lt hx <| (v.map_neg y).trans_lt hy

variable {x y : R}

@[simp]
/-
**Valuation.le_one_of_subsingleton** 是 Mathlib 中的一个引理，位于命名空间 `Valuation`。
形式化陈述：le_one_of_subsingleton [Subsingleton R] (v : Valuation R Γ₀) {x : R} : v x
 <= 1
参数：v : Valuation R Γ₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Valuation.map_one`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : Ring R] [ins
t_1 : LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation R Γ₀),   v 1 = 1
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
lemma le_one_of_subsingleton [Subsingleton R] (v : Valuation R Γ₀) {x : R} :
    v x ≤ 1 := by
  rw [Subsingleton.elim x 1, Valuation.map_one]
/-
**Valuation.map_add_of_distinct_val** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`。
形式化陈述：map_add_of_distinct_val (h : v x != v y) : v (x + y) = max (v x) (v y)
参数：h : v x != v y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Valuation.map_sub`：map_sub (x y : R) : v (x - y) <= max (v x) (v y)
· 使用定理 `max_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, b < a → c <
 a → max b c < a
· 使用定理 `max_eq_left_of_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, b 
< a → max a b = a
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `max_comm`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), max a b = m
ax b a
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `Ne.lt_or_gt`：Ne.lt_or_gt (h : a != b) : a < b ∨ b < a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Classical.or_iff_not_imp_right`：∀ {a b : Prop}, a ∨ b ↔ ¬b → a
· 使用定理 `le_iff_eq_or_lt`：le_iff_eq_or_lt : a <= b ↔ a = b ∨ a < b
· 使用定理 `Valuation.map_add`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : Ring R] [ins
t_1 : LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation R Γ₀)   (x y : R), v (x
 + y) ≤…
-/
theorem map_add_of_distinct_val (h : v x ≠ v y) : v (x + y) = max (v x) (v y) := by
  suffices ¬v (x + y) < max (v x) (v y) from
    or_iff_not_imp_right.1 (le_iff_eq_or_lt.1 (v.map_add x y)) this
  intro h'
  wlog vyx : v y < v x generalizing x y
  · refine this h.symm ?_ (h.lt_or_gt.resolve_right vyx)
    rwa [add_comm, max_comm]
  rw [max_eq_left_of_lt vyx] at h'
  apply lt_irrefl (v x)
  calc
    v x = v (x + y - y) := by simp
    _ ≤ max (v <| x + y) (v y) := map_sub _ _ _
    _ < v x := max_lt h' vyx
/-
**Valuation.map_add_eq_of_lt_right** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`。
形式化陈述：map_add_eq_of_lt_right (h : v x < v y) : v (x + y) = v y
参数：h : v x < v y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Valuation.map_add_of_distinct_val`：map_add_of_distinct_val (h : v x != v
 y) : v (x + y) = max (v x) (v y)
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `max_eq_right_iff`：∀ {α : Type u} [inst : LinearOrder α] {a b : α}, max a
 b = b ↔ a ≤ b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem map_add_eq_of_lt_right (h : v x < v y) : v (x + y) = v y :=
  (v.map_add_of_distinct_val h.ne).trans (max_eq_right_iff.mpr h.le)
/-
**Valuation.map_add_eq_of_lt_left** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`。
形式化陈述：map_add_eq_of_lt_left (h : v y < v x) : v (x + y) = v x
参数：h : v y < v x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Valuation.map_add_eq_of_lt_right`：map_add_eq_of_lt_right (h : v x < v y)
 : v (x + y) = v y
-/
theorem map_add_eq_of_lt_left (h : v y < v x) : v (x + y) = v x := by
  rw [add_comm]; exact map_add_eq_of_lt_right _ h
/-
**Valuation.map_sub_eq_of_lt_right** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`。
形式化陈述：map_sub_eq_of_lt_right (h : v x < v y) : v (x - y) = v y
参数：h : v x < v y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Valuation.map_add_eq_of_lt_right`：map_add_eq_of_lt_right (h : v x < v y)
 : v (x + y) = v y
· 使用定理 `Valuation.map_neg`：map_neg (x : R) : v (-x) = v x
-/
theorem map_sub_eq_of_lt_right (h : v x < v y) : v (x - y) = v y := by
  rw [sub_eq_add_neg, map_add_eq_of_lt_right, map_neg]
  rwa [map_neg]
/-
**Valuation.map_sum_eq_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`。
形式化陈述：map_sum_eq_of_lt {ι : Type*} [DecidableEq ι] {s : Finset ι} {f : ι -> R} {
j : ι} (hj : j in s) (hf : forall i in s \ {j}, v (f i) < v (f j)) : v (∑ i in s
, f i) = v (f j)
参数：hj : j in s；hf : forall i in s \ {j}, v (f i) < v (f j)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.sum_eq_add_sum_sdiff_singleton_of_mem`：∀ {ι : Type u_1} {M : Type
 u_3} [inst : AddCommMonoid M] [inst_1 : DecidableEq ι] {s : Finset ι} {i : ι}, 
  i ∈ s → ∀ (f : ι → M), ∑ x ∈ s, …
· 使用定理 `Valuation.map_add_eq_of_lt_left`：map_add_eq_of_lt_left (h : v y < v x) :
 v (x + y) = v x
· 使用定理 `Valuation.map_sum_lt`：map_sum_lt {ι : Type*} {s : Finset ι} {f : ι -> R}
 {g : Γ₀} (hg : g != 0) (hf : forall i in s, v (f i) < g) : v (∑ i in s, f i) < 
g
-/
theorem map_sum_eq_of_lt {ι : Type*} [DecidableEq ι] {s : Finset ι} {f : ι → R} {j : ι}
    (hj : j ∈ s) (hf : ∀ i ∈ s \ {j}, v (f i) < v (f j)) :
    v (∑ i ∈ s, f i) = v (f j) := by
  rcases eq_or_ne (v (f j)) 0 with h0 | h0
  · aesop
  rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem hj]
  exact map_add_eq_of_lt_left _ (map_sum_lt _ h0 hf)
/-
**Valuation.map_sub_eq_of_lt_left** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`。
形式化陈述：map_sub_eq_of_lt_left (h : v y < v x) : v (x - y) = v x
参数：h : v y < v x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Valuation.map_add_eq_of_lt_left`：map_add_eq_of_lt_left (h : v y < v x) :
 v (x + y) = v x
· 使用定理 `Valuation.map_neg`：map_neg (x : R) : v (-x) = v x
-/
theorem map_sub_eq_of_lt_left (h : v y < v x) : v (x - y) = v x := by
  rw [sub_eq_add_neg, map_add_eq_of_lt_left]
  rwa [map_neg]
/-
**Valuation.map_eq_of_sub_lt** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`。
形式化陈述：map_eq_of_sub_lt (h : v (y - x) < v x) : v y = v x
参数：h : v (y - x) < v x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Valuation.map_add_of_distinct_val`：map_add_of_distinct_val (h : v x != v
 y) : v (x + y) = max (v x) (v y)
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `max_eq_right`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a ≤ b →
 max a b = b
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem map_eq_of_sub_lt (h : v (y - x) < v x) : v y = v x := by
  have := Valuation.map_add_of_distinct_val v (ne_of_gt h).symm
  rw [max_eq_right (le_of_lt h)] at this
  simpa using this
/-
**Valuation.map_sub_of_left_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `Valuation`。
形式化陈述：map_sub_of_left_eq_zero (hx : v x = 0) : v (x - y) = v y
参数：hx : v x = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `max_self`：∀ {α : Type u_1} [inst : LinearOrder α] (a : α), max a a = a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Valuation.map_sub`：map_sub (x y : R) : v (x - y) <= max (v x) (v y)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Valuation.map_sub_eq_of_lt_right`：map_sub_eq_of_lt_right (h : v x < v y)
 : v (x - y) = v y
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_sub_of_left_eq_zero (hx : v x = 0) : v (x - y) = v y := by
  by_cases hy : v y = 0
  · simpa [*] using map_sub v x y
  · simp [*, map_sub_eq_of_lt_right, zero_lt_iff]
/-
**Valuation.map_sub_of_right_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `Valuation`。
形式化陈述：map_sub_of_right_eq_zero (hy : v y = 0) : v (x - y) = v x
参数：hy : v y = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Valuation.map_sub_swap`：map_sub_swap (x y : R) : v (x - y) = v (y - x)
· 使用引理 `Valuation.map_sub_of_left_eq_zero`：map_sub_of_left_eq_zero (hx : v x = 0
) : v (x - y) = v y
-/
lemma map_sub_of_right_eq_zero (hy : v y = 0) : v (x - y) = v x := by
  rw [map_sub_swap, map_sub_of_left_eq_zero v hy]
/-
**Valuation.map_add_of_left_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `Valuation`。
形式化陈述：map_add_of_left_eq_zero (hx : v x = 0) : v (x + y) = v y
参数：hx : v x = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用引理 `Valuation.map_sub_of_left_eq_zero`：map_sub_of_left_eq_zero (hx : v x = 0
) : v (x - y) = v y
· 使用定理 `Valuation.map_neg`：map_neg (x : R) : v (-x) = v x
-/
lemma map_add_of_left_eq_zero (hx : v x = 0) : v (x + y) = v y := by
  rw [← sub_neg_eq_add, map_sub_of_left_eq_zero v hx, map_neg]
/-
**Valuation.map_add_of_right_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `Valuation`。
形式化陈述：map_add_of_right_eq_zero (hy : v y = 0) : v (x + y) = v x
参数：hy : v y = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用引理 `Valuation.map_add_of_left_eq_zero`：map_add_of_left_eq_zero (hx : v x = 0
) : v (x + y) = v y
-/
lemma map_add_of_right_eq_zero (hy : v y = 0) : v (x + y) = v x := by
  rw [add_comm, map_add_of_left_eq_zero v hy]
/-
**Valuation.map_one_add_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`。
形式化陈述：map_one_add_of_lt (h : v x < 1) : v (1 + x) = 1
参数：h : v x < 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Valuation.map_one`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : Ring R] [ins
t_1 : LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation R Γ₀),   v 1 = 1
· 使用定理 `Valuation.map_add_eq_of_lt_left`：map_add_eq_of_lt_left (h : v y < v x) :
 v (x + y) = v x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem map_one_add_of_lt (h : v x < 1) : v (1 + x) = 1 := by
  rw [← v.map_one] at h
  simpa only [v.map_one] using v.map_add_eq_of_lt_left h
/-
**Valuation.map_one_sub_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`。
形式化陈述：map_one_sub_of_lt (h : v x < 1) : v (1 - x) = 1
参数：h : v x < 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Valuation.map_one`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : Ring R] [ins
t_1 : LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation R Γ₀),   v 1 = 1
· 使用定理 `Valuation.map_add_eq_of_lt_left`：map_add_eq_of_lt_left (h : v y < v x) :
 v (x + y) = v x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Valuation.map_neg`：map_neg (x : R) : v (-x) = v x
-/
theorem map_one_sub_of_lt (h : v x < 1) : v (1 - x) = 1 := by
  rw [← v.map_one, ← v.map_neg] at h
  rw [sub_eq_add_neg 1 x]
  simpa only [v.map_one, v.map_neg] using v.map_add_eq_of_lt_left h
/-
**Valuation.OrderMonoidWithZeroHom.ofClass_monotone** 是 Mathlib 中的一个定理，位于命名空间 `V
aluation.OrderMonoidWithZeroHom`。
形式化陈述：∀ {F : Type u_1} {α : Type u_2} {β : Type u_3} [inst : LinearOrderedCommMo
noidWithZero α]   [inst_1 : LinearOrderedCommMonoidWithZero β] [inst_2 : FunLike
 F α β] [inst_3 : MonoidWithZeroHomClass F α β] {f : F},   Monotone ⇑f → Monoton
e ⇑(MonoidWithZeroHom.ofClass f)
参数：MonoidWithZeroHom.ofClass f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma OrderMonoidWithZeroHom.ofClass_monotone {F : Type u_1} {α : Type u_2} {β : Type u_3}
    [LinearOrderedCommMonoidWithZero α] [LinearOrderedCommMonoidWithZero β] [FunLike F α β]
    [MonoidWithZeroHomClass F α β] {f : F} (hf : Monotone f) :
    Monotone (MonoidWithZeroHom.ofClass f) := hf

/-- An ordered monoid isomorphism `Γ₀ ≃ Γ'₀` induces an equivalence
`Valuation R Γ₀ ≃ Valuation R Γ'₀`. -/
/-
**Valuation.congr** 是 Mathlib 中的一个定义，位于命名空间 `Valuation`。
形式化陈述：congr (f : Γ₀ ≃*o Γ'₀) : Valuation R Γ₀ ≃ Valuation R Γ'₀ where toFun
参数：f : Γ₀ ≃*o Γ'₀。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An ordered monoid isomorphism `Γ₀ ≃ Γ'₀` induces an equivalence
`Valuation R Γ₀ ≃ Valuation R Γ'₀`.
-/
def congr (f : Γ₀ ≃*o Γ'₀) : Valuation R Γ₀ ≃ Valuation R Γ'₀ where
  toFun := map (.ofClass f) (OrderMonoidWithZeroHom.ofClass_monotone f.toOrderIso.monotone)
  invFun := map (.ofClass f.symm)
    (OrderMonoidWithZeroHom.ofClass_monotone f.symm.toOrderIso.monotone)
  left_inv _ := by ext; simp
  right_inv _ := by ext; simp

section One

variable [Nontrivial R] [NoZeroDivisors R] [DecidablePred fun x : R ↦ x = 0]

variable (R Γ₀) in
/-- The trivial valuation, sending everything to 1 other than 0. -/
/-
**Valuation.one** 是 Mathlib 中的一个定义，位于命名空间 `Valuation`。
形式化陈述：(R : Type u_3) →   (Γ₀ : Type u_4) →     [inst : Ring R] →       [inst_1 :
 LinearOrderedCommMonoidWithZero Γ₀] →         [Nontrivial R] → [NoZeroDivisors 
R] → [DecidablePred fun x => x = 0] → One (Valuation R Γ₀)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The trivial valuation, sending everything to 1 other than 0.
-/
protected instance one : One (Valuation R Γ₀) where
  one :=
  { __ : R →*₀ Γ₀ := 1
    map_add_le_max' x y := by
      simp only [ZeroHom.toFun_eq_coe, MonoidWithZeroHom.toZeroHom_coe,
        MonoidWithZeroHom.one_apply_def, le_sup_iff]
      split_ifs <;> simp_all }
/-
**Valuation.one_apply_def** 是 Mathlib 中的一个引理，位于命名空间 `Valuation`。
形式化陈述：one_apply_def (x : R) : (1 : Valuation R Γ₀) x = if x = 0 then 0 else 1
参数：x : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma one_apply_def (x : R) : (1 : Valuation R Γ₀) x = if x = 0 then 0 else 1 := rfl
/-
**Valuation.toMonoidWithZeroHom_one** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`。
形式化陈述：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : Ring R] [inst_1 : LinearOrderedCo
mmMonoidWithZero Γ₀] [inst_2 : Nontrivial R]   [inst_3 : NoZeroDivisors R] [inst
_4 : DecidablePred fun x => x = 0], Valuation.toMonoidWithZeroHom 1 = 1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toMonoidWithZeroHom_one : (1 : Valuation R Γ₀).toMonoidWithZeroHom = 1 := rfl
/-
**Valuation.one_apply_of_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Valuation`。
形式化陈述：one_apply_of_ne_zero {x : R} (hx : x != 0) : (1 : Valuation R Γ₀) x = 1
参数：hx : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
lemma one_apply_of_ne_zero {x : R} (hx : x ≠ 0) : (1 : Valuation R Γ₀) x = 1 := if_neg hx

@[simp]
/-
**Valuation.one_apply_eq_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `Valuation`。
形式化陈述：one_apply_eq_zero_iff [Nontrivial Γ₀] {x : R} : (1 : Valuation R Γ₀) x = 0
 ↔ x = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MonoidWithZeroHom.one_apply_eq_zero_iff`：one_apply_eq_zero_iff {M₀ N₀ : 
Type*} [MulZeroOneClass M₀] [MulZeroOneClass N₀] [DecidablePred fun x : M₀ => x 
= 0] [Nontrivial M₀] [NoZeroD…
-/
lemma one_apply_eq_zero_iff [Nontrivial Γ₀] {x : R} : (1 : Valuation R Γ₀) x = 0 ↔ x = 0 :=
  MonoidWithZeroHom.one_apply_eq_zero_iff
/-
**Valuation.one_apply_le_one** 是 Mathlib 中的一个引理，位于命名空间 `Valuation`。
形式化陈述：one_apply_le_one (x : R) : (1 : Valuation R Γ₀) x <= 1
参数：x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Valuation.one_apply_def`：one_apply_def (x : R) : (1 : Valuation R Γ₀) x 
= if x = 0 then 0 else 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
lemma one_apply_le_one (x : R) : (1 : Valuation R Γ₀) x ≤ 1 := by
  rw [one_apply_def]
  split_ifs <;> simp_all

@[simp]
/-
**Valuation.one_apply_lt_one_iff** 是 Mathlib 中的一个引理，位于命名空间 `Valuation`。
形式化陈述：one_apply_lt_one_iff [Nontrivial Γ₀] {x : R} : (1 : Valuation R Γ₀) x < 1 
↔ x = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Valuation.one_apply_def`：one_apply_def (x : R) : (1 : Valuation R Γ₀) x 
= if x = 0 then 0 else 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `instZeroLEOneClassOfIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α] [inst
_1 : Zero α] [inst_2 : One α] [IsBotZeroClass α], ZeroLEOneClass α
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
-/
lemma one_apply_lt_one_iff [Nontrivial Γ₀] {x : R} : (1 : Valuation R Γ₀) x < 1 ↔ x = 0 := by
  rw [one_apply_def]
  split_ifs <;> simp_all

@[simp]
/-
**Valuation.one_apply_eq_one_iff** 是 Mathlib 中的一个引理，位于命名空间 `Valuation`。
形式化陈述：one_apply_eq_one_iff [Nontrivial Γ₀] {x : R} : (1 : Valuation R Γ₀) x = 1 
↔ x != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MonoidWithZeroHom.one_apply_eq_one_iff`：one_apply_eq_one_iff {M₀ N₀ : Ty
pe*} [MulZeroOneClass M₀] [MulZeroOneClass N₀] [DecidablePred fun x : M₀ => x = 
0] [Nontrivial M₀] [NoZeroDi…
-/
lemma one_apply_eq_one_iff [Nontrivial Γ₀] {x : R} : (1 : Valuation R Γ₀) x = 1 ↔ x ≠ 0 :=
  MonoidWithZeroHom.one_apply_eq_one_iff

end One

end Monoid

section Group

variable [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation R Γ₀) {x y : R}

/-
**Valuation.map_inv** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`。
形式化陈述：map_inv {R : Type*} [DivisionRing R] (v : Valuation R Γ₀) : forall x, v x⁻
¹ = (v x)⁻¹
参数：v : Valuation R Γ₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_inv₀`：map_inv₀ : f a⁻¹ = (f a)⁻¹
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
-/
theorem map_inv {R : Type*} [DivisionRing R] (v : Valuation R Γ₀) : ∀ x, v x⁻¹ = (v x)⁻¹ :=
  map_inv₀ _
/-
**Valuation.map_div** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`。
形式化陈述：map_div {R : Type*} [DivisionRing R] (v : Valuation R Γ₀) : forall x y, v 
(x / y) = v x / v y
参数：v : Valuation R Γ₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_div₀`：map_div₀ : f (a / b) = f a / f b
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
-/
theorem map_div {R : Type*} [DivisionRing R] (v : Valuation R Γ₀) : ∀ x y, v (x / y) = v x / v y :=
  map_div₀ _
/-
**Valuation.one_lt_val_iff** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`。
形式化陈述：one_lt_val_iff (v : Valuation K Γ₀) {x : K} (h : x != 0) : 1 < v x ↔ v x⁻¹
 < 1
参数：v : Valuation K Γ₀；h : x != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_inv₀`：map_inv₀ : f a⁻¹ = (f a)⁻¹
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用引理 `inv_lt_one₀`：inv_lt_one₀ (ha : 0 < a) : a⁻¹ < 1 ↔ 1 < a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Valuation.pos_iff`：pos_iff [Nontrivial Γ₀] (v : Valuation K Γ₀) {x : K} 
: 0 < v x ↔ x != 0
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem one_lt_val_iff (v : Valuation K Γ₀) {x : K} (h : x ≠ 0) : 1 < v x ↔ v x⁻¹ < 1 := by
  simp [inv_lt_one₀ (v.pos_iff.2 h)]
/-
**Valuation.one_le_val_iff** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`。
形式化陈述：one_le_val_iff (v : Valuation K Γ₀) {x : K} (h : x != 0) : 1 <= v x ↔ v x⁻
¹ <= 1
参数：v : Valuation K Γ₀；h : x != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_inv₀`：map_inv₀ : f a⁻¹ = (f a)⁻¹
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用引理 `inv_le_one₀`：inv_le_one₀ (ha : 0 < a) : a⁻¹ <= 1 ↔ 1 <= a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Valuation.pos_iff`：pos_iff [Nontrivial Γ₀] (v : Valuation K Γ₀) {x : K} 
: 0 < v x ↔ x != 0
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem one_le_val_iff (v : Valuation K Γ₀) {x : K} (h : x ≠ 0) : 1 ≤ v x ↔ v x⁻¹ ≤ 1 := by
  simp [inv_le_one₀ (v.pos_iff.2 h)]
/-
**Valuation.val_lt_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`。
形式化陈述：val_lt_one_iff (v : Valuation K Γ₀) {x : K} (h : x != 0) : v x < 1 ↔ 1 < v
 x⁻¹
参数：v : Valuation K Γ₀；h : x != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_inv₀`：map_inv₀ : f a⁻¹ = (f a)⁻¹
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用引理 `one_lt_inv₀`：one_lt_inv₀ (ha : 0 < a) : 1 < a⁻¹ ↔ a < 1
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Valuation.pos_iff`：pos_iff [Nontrivial Γ₀] (v : Valuation K Γ₀) {x : K} 
: 0 < v x ↔ x != 0
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem val_lt_one_iff (v : Valuation K Γ₀) {x : K} (h : x ≠ 0) : v x < 1 ↔ 1 < v x⁻¹ := by
  simp [one_lt_inv₀ (v.pos_iff.2 h)]
/-
**Valuation.val_le_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`。
形式化陈述：val_le_one_iff (v : Valuation K Γ₀) {x : K} (h : x != 0) : v x <= 1 ↔ 1 <=
 v x⁻¹
参数：v : Valuation K Γ₀；h : x != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_inv₀`：map_inv₀ : f a⁻¹ = (f a)⁻¹
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用引理 `one_le_inv₀`：one_le_inv₀ (ha : 0 < a) : 1 <= a⁻¹ ↔ a <= 1
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Valuation.pos_iff`：pos_iff [Nontrivial Γ₀] (v : Valuation K Γ₀) {x : K} 
: 0 < v x ↔ x != 0
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem val_le_one_iff (v : Valuation K Γ₀) {x : K} (h : x ≠ 0) : v x ≤ 1 ↔ 1 ≤ v x⁻¹ := by
  simp [one_le_inv₀ (v.pos_iff.2 h)]
/-
**Valuation.val_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`。
形式化陈述：val_eq_one_iff (v : Valuation K Γ₀) {x : K} : v x = 1 ↔ v x⁻¹ = 1
参数：v : Valuation K Γ₀。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_inv₀`：map_inv₀ : f a⁻¹ = (f a)⁻¹
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem val_eq_one_iff (v : Valuation K Γ₀) {x : K} : v x = 1 ↔ v x⁻¹ = 1 := by
  simp
/-
**Valuation.val_le_one_or_val_inv_lt_one** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`。
形式化陈述：val_le_one_or_val_inv_lt_one (v : Valuation K Γ₀) (x : K) : v x <= 1 ∨ v x
⁻¹ < 1
参数：v : Valuation K Γ₀；x : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `instZeroLEOneClassOfIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α] [inst
_1 : Zero α] [inst_2 : One α] [IsBotZeroClass α], ZeroLEOneClass α
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Valuation.one_lt_val_iff`：one_lt_val_iff (v : Valuation K Γ₀) {x : K} (h
 : x != 0) : 1 < v x ↔ v x⁻¹ < 1
-/
theorem val_le_one_or_val_inv_lt_one (v : Valuation K Γ₀) (x : K) : v x ≤ 1 ∨ v x⁻¹ < 1 := by
  obtain rfl | h := eq_or_ne x 0
  · simp
  · simp only [← one_lt_val_iff v h, le_or_gt]

/--
This theorem is a weaker version of `Valuation.val_le_one_or_val_inv_lt_one`, but more symmetric
in `x` and `x⁻¹`.
-/
/-
**Valuation.val_le_one_or_val_inv_le_one** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`。
形式化陈述：val_le_one_or_val_inv_le_one (v : Valuation K Γ₀) (x : K) : v x <= 1 ∨ v x
⁻¹ <= 1
参数：v : Valuation K Γ₀；x : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Valuation.one_le_val_iff`：one_le_val_iff (v : Valuation K Γ₀) {x : K} (h
 : x != 0) : 1 <= v x ↔ v x⁻¹ <= 1

--- 原说明 ---
This theorem is a weaker version of `Valuation.val_le_one_or_val_inv_lt_one`, bu
t more symmetric
in `x` and `x⁻¹`.
-/
theorem val_le_one_or_val_inv_le_one (v : Valuation K Γ₀) (x : K) : v x ≤ 1 ∨ v x⁻¹ ≤ 1 := by
  by_cases h : x = 0
  · simp only [h, map_zero, zero_le, inv_zero, or_self]
  · simp only [← one_le_val_iff v h, le_total]

/-- The subgroup of elements whose valuation is less than or equal to a certain value. -/
/-
**Valuation.leAddSubgroup** 是 Mathlib 中的一个定义，位于命名空间 `Valuation`。
形式化陈述：leAddSubgroup (v : Valuation R Γ₀) (γ : Γ₀) : AddSubgroup R where carrier
参数：v : Valuation R Γ₀；γ : Γ₀。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The subgroup of elements whose valuation is less than or equal to a certain valu
e.
-/
def leAddSubgroup (v : Valuation R Γ₀) (γ : Γ₀) : AddSubgroup R where
  carrier := { x | v x ≤ γ }
  zero_mem' := by simp
  add_mem' {x y} x_in y_in := (v.map_add x y).trans (max_le x_in y_in)
  neg_mem' x_in := by rwa [Set.mem_ofPred, map_neg]

@[simp]
/-
**Valuation.mem_leAddSubgroup_iff** 是 Mathlib 中的一个引理，位于命名空间 `Valuation`。
形式化陈述：mem_leAddSubgroup_iff {v : Valuation R Γ₀} {γ : Γ₀} {x : R} : x in v.leAdd
Subgroup γ ↔ v x <= γ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_leAddSubgroup_iff {v : Valuation R Γ₀} {γ : Γ₀} {x : R} :
    x ∈ v.leAddSubgroup γ ↔ v x ≤ γ :=
  Iff.rfl
/-
**Valuation.leAddSubgroup_monotone** 是 Mathlib 中的一个引理，位于命名空间 `Valuation`。
形式化陈述：leAddSubgroup_monotone (v : Valuation R Γ₀) : Monotone v.leAddSubgroup
参数：v : Valuation R Γ₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans'`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, b ≤ a → 
c ≤ b → c ≤ a
-/
lemma leAddSubgroup_monotone (v : Valuation R Γ₀) : Monotone v.leAddSubgroup :=
  fun _ _ h _ ↦ h.trans'

open MonoidWithZeroHom MonoidWithZeroHom.ValueGroup₀

/-- The restriction of a valuation so that it takes values in its `valueGroup₀`. -/
/-
**Valuation.restrict** 是 Mathlib 中的一个定义，位于命名空间 `Valuation`。
形式化陈述：restrict : Valuation R (ValueGroup₀ (.ofClass v)) where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The restriction of a valuation so that it takes values in its `valueGroup₀`.
-/
def restrict : Valuation R (ValueGroup₀ (.ofClass v)) where
  __ := restrict₀ (.ofClass v)
  map_add_le_max' x y := by
    by_cases H : v x ≠ 0 ∨ v y ≠ 0
    · rcases H with h | h
      all_goals simp only [ZeroHom.toFun_eq_coe, toZeroHom_coe, restrict₀_apply, coe_ofClass, h,
        reduceDIte, le_sup_iff]
      all_goals split_ifs with H
      · simp [H]
      · simp only [H, ↓reduceDIte, WithZero.coe_le_coe, Subtype.mk_le_mk, ← Units.val_le_val,
          Units.val_mk0]
        split_ifs with hy
        · simpa [hy] using map_add_le _ (le_rfl (a := v x)) (hy ▸ zero_le)
        · simp [hy, ← Units.val_le_val]
      · simp [H]
      · simp only [H, ↓reduceDIte, WithZero.coe_le_coe, Subtype.mk_le_mk]
        split_ifs with hx
        · simpa [hx, ← Units.val_le_val] using map_add_le _ (hx ▸ zero_le) (le_rfl (a := v y))
        · simp [hx, ← Units.val_le_val]
    · simp only [ne_eq, not_or, Decidable.not_not] at H
      simp only [ZeroHom.toFun_eq_coe, toZeroHom_coe, restrict₀_apply,
        MonoidWithZeroHom.coe_ofClass, H, ↓reduceDIte, max_self, nonpos_iff_eq_zero]
      replace H : v (x + y) = 0 :=
        le_antisymm (map_add_le _ (le_of_eq H.1) (le_of_eq H.2)) zero_le
      simp [H]
/-
**Valuation.restrict_def** 是 Mathlib 中的一个引理，位于命名空间 `Valuation`。
形式化陈述：restrict_def (x : R) : v.restrict x = restrict₀ (.ofClass v) x
参数：x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
-/
lemma restrict_def (x : R) : v.restrict x = restrict₀ (.ofClass v) x := rfl

@[simp]
/-
**Valuation.embedding_restrict** 是 Mathlib 中的一个引理，位于命名空间 `Valuation`。
形式化陈述：embedding_restrict (x : R) : embedding (v.restrict x) = v x
参数：x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MonoidWithZeroHom.ValueGroup₀.embedding_restrict₀`：embedding_restrict₀ (
a : A) : ValueGroup₀.embedding (restrict₀ f a) = f a
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
-/
lemma embedding_restrict (x : R) : embedding (v.restrict x) = v x :=
  embedding_restrict₀ x
/-
**Valuation.restrict_lt_iff_lt_embedding** 是 Mathlib 中的一个引理，位于命名空间 `Valuation`。
形式化陈述：restrict_lt_iff_lt_embedding {x : R} {g : ValueGroup₀ (.ofClass v)} : v.re
strict x < g ↔ v x < embedding g
参数：.ofClass v。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `StrictMono.lt_iff_lt`：StrictMono.lt_iff_lt (hf : StrictMono f) {a b : α}
 : f a < f b ↔ a < b
· 使用引理 `MonoidWithZeroHom.ValueGroup₀.embedding_strictMono`：embedding_strictMono
 : StrictMono (embedding (f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Valuation.embedding_restrict`：embedding_restrict (x : R) : embedding (v.
restrict x) = v x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma restrict_lt_iff_lt_embedding {x : R} {g : ValueGroup₀ (.ofClass v)} :
    v.restrict x < g ↔ v x < embedding g :=
  embedding_strictMono.lt_iff_lt.symm.trans (by simp)
/-
**Valuation.restrict_le_iff_le_embedding** 是 Mathlib 中的一个引理，位于命名空间 `Valuation`。
形式化陈述：restrict_le_iff_le_embedding {x : R} {g : ValueGroup₀ (.ofClass v)} : v.re
strict x <= g ↔ v x <= embedding g
参数：.ofClass v。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `StrictMono.le_iff_le`：StrictMono.le_iff_le (hf : StrictMono f) {a b : α}
 : f a <= f b ↔ a <= b
· 使用引理 `MonoidWithZeroHom.ValueGroup₀.embedding_strictMono`：embedding_strictMono
 : StrictMono (embedding (f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Valuation.embedding_restrict`：embedding_restrict (x : R) : embedding (v.
restrict x) = v x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma restrict_le_iff_le_embedding {x : R} {g : ValueGroup₀ (.ofClass v)} :
    v.restrict x ≤ g ↔ v x ≤ embedding g :=
  embedding_strictMono.le_iff_le.symm.trans (by simp)
/-
**Valuation.restrict_eq_mk** 是 Mathlib 中的一个引理，位于命名空间 `Valuation`。
形式化陈述：restrict_eq_mk {x : R} (hx : v x != 0) : v.restrict x = (valueGroup.mk (.o
fClass v) 1 x (by simp) hx : ValueGroup₀ (.ofClass v))
参数：hx : v x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_false`：∀ {p : Prop}, p = False → ¬p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `Units.mk0.congr_simp`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] (a a_1
 : G₀) (e_a : a = a_1) (ha : a ≠ 0), Units.mk0 a ha = Units.mk0 a_1 ⋯
· 使用定理 `Units.mk0_one`：mk0_one (h
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MonoidWithZeroHom.ValueGroup₀.restrict₀_apply`：∀ {A : Type u_1} {B : Typ
e u_2} [inst : MonoidWithZero A] [inst_1 : GroupWithZero B] (f : A →*₀ B) (a : A
),   (MonoidWithZeroHom.ValueGroup₀…
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma restrict_eq_mk {x : R} (hx : v x ≠ 0) : v.restrict x =
    (valueGroup.mk (.ofClass v) 1 x (by simp) hx : ValueGroup₀ (.ofClass v)) := by
  simp [restrict_def, restrict₀_apply, valueGroup.mk, hx]

@[simp]
/-
**Valuation.restrict_pos_iff** 是 Mathlib 中的一个引理，位于命名空间 `Valuation`。
形式化陈述：restrict_pos_iff (x : R) : 0 < v.restrict x ↔ 0 < v x
参数：x : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonoidWithZeroHom.ValueGroup₀.restrict₀_apply`：∀ {A : Type u_1} {B : Typ
e u_2} [inst : MonoidWithZero A] [inst_1 : GroupWithZero B] (f : A →*₀ B) (a : A
),   (MonoidWithZeroHom.ValueGroup₀…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `false_iff`：∀ (p : Prop), (False ↔ p) = ¬p
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `WithZero.instIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α], IsBotZeroCl
ass (WithZero α)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `true_iff`：∀ (p : Prop), (True ↔ p) = p
-/
lemma restrict_pos_iff (x : R) : 0 < v.restrict x ↔ 0 < v x := by
  simp only [restrict_def, restrict₀_apply]
  split_ifs with h <;> simpa [zero_lt_iff]

@[simp]
/-
**Valuation.restrict_lt_iff** 是 Mathlib 中的一个引理，位于命名空间 `Valuation`。
形式化陈述：restrict_lt_iff {x y : R} : v.restrict x < v.restrict y ↔ v x < v y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Valuation.restrict_lt_iff_lt_embedding`：restrict_lt_iff_lt_embedding {x 
: R} {g : ValueGroup₀ (.ofClass v)} : v.restrict x < g ↔ v x < embedding g
· 使用引理 `Valuation.embedding_restrict`：embedding_restrict (x : R) : embedding (v.
restrict x) = v x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma restrict_lt_iff {x y : R} : v.restrict x < v.restrict y ↔ v x < v y := by
  rw [restrict_lt_iff_lt_embedding, embedding_restrict]

@[simp]
/-
**Valuation.restrict_le_iff** 是 Mathlib 中的一个引理，位于命名空间 `Valuation`。
形式化陈述：restrict_le_iff {x y : R} : v.restrict x <= v.restrict y ↔ v x <= v y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Valuation.restrict_le_iff_le_embedding`：restrict_le_iff_le_embedding {x 
: R} {g : ValueGroup₀ (.ofClass v)} : v.restrict x <= g ↔ v x <= embedding g
· 使用引理 `Valuation.embedding_restrict`：embedding_restrict (x : R) : embedding (v.
restrict x) = v x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma restrict_le_iff {x y : R} : v.restrict x ≤ v.restrict y ↔ v x ≤ v y := by
  rw [restrict_le_iff_le_embedding, embedding_restrict]

@[simp]
/-
**Valuation.restrict_inj** 是 Mathlib 中的一个引理，位于命名空间 `Valuation`。
形式化陈述：restrict_inj {x y : R} : v.restrict x = v.restrict y ↔ v x = v y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用引理 `MonoidWithZeroHom.ValueGroup₀.embedding_inj`：embedding_inj {a b : ValueG
roup₀ f} : embedding a = embedding b ↔ a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Valuation.embedding_restrict`：embedding_restrict (x : R) : embedding (v.
restrict x) = v x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma restrict_inj {x y : R} : v.restrict x = v.restrict y ↔ v x = v y :=
  embedding_inj.symm.trans (by simp)
/-
**Valuation.isEquiv_restrict** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`。
形式化陈述：isEquiv_restrict : v.IsEquiv v.restrict
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用引理 `Valuation.restrict_le_iff`：restrict_le_iff {x y : R} : v.restrict x <= v
.restrict y ↔ v x <= v y
-/
theorem isEquiv_restrict : v.IsEquiv v.restrict := fun _ _ ↦ v.restrict_le_iff.symm

@[simp]
/-
**Valuation.restrict_lt_one_iff** 是 Mathlib 中的一个引理，位于命名空间 `Valuation`。
形式化陈述：restrict_lt_one_iff {x : R} : v.restrict x < 1 ↔ v x < 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Valuation.restrict_lt_iff_lt_embedding`：restrict_lt_iff_lt_embedding {x 
: R} {g : ValueGroup₀ (.ofClass v)} : v.restrict x < g ↔ v x < embedding g
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma restrict_lt_one_iff {x : R} : v.restrict x < 1 ↔ v x < 1 := by
  rw [restrict_lt_iff_lt_embedding, map_one]

@[simp]
/-
**Valuation.restrict_le_one_iff** 是 Mathlib 中的一个引理，位于命名空间 `Valuation`。
形式化陈述：restrict_le_one_iff {x : R} : v.restrict x <= 1 ↔ v x <= 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Valuation.restrict_le_iff_le_embedding`：restrict_le_iff_le_embedding {x 
: R} {g : ValueGroup₀ (.ofClass v)} : v.restrict x <= g ↔ v x <= embedding g
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma restrict_le_one_iff {x : R} : v.restrict x ≤ 1 ↔ v x ≤ 1 := by
  rw [restrict_le_iff_le_embedding, map_one]

@[simp]
/-
**Valuation.restrict_eq_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `Valuation`。
形式化陈述：restrict_eq_zero_iff {x : R} : v.restrict x = 0 ↔ v x = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma restrict_eq_zero_iff {x : R} : v.restrict x = 0 ↔ v x = 0 := by
  simp [restrict_def, restrict₀_eq_zero_iff]

@[simp]
/-
**Valuation.restrict_eq_one_iff** 是 Mathlib 中的一个引理，位于命名空间 `Valuation`。
形式化陈述：restrict_eq_one_iff {x : R} : v.restrict x = 1 ↔ v x = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma restrict_eq_one_iff {x : R} : v.restrict x = 1 ↔ v x = 1 := by
  simp [restrict_def, restrict₀_eq_one_iff]
/-
**Valuation.exists_div_eq_of_unit** 是 Mathlib 中的一个引理，位于命名空间 `Valuation`。
形式化陈述：exists_div_eq_of_unit (γ : (ValueGroup₀ (.ofClass v))ˣ) : exists r s, 0 < 
v r ∧ 0 < v s ∧ v.restrict r / v.restrict s = γ.1
参数：γ : (ValueGroup₀ (.ofClass v))ˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `Units.ne_zero`：ne_zero [Nontrivial M₀] (u : M₀ˣ) : (u : M₀) != 0
· 使用定理 `WithZero.instNontrivial`：∀ {α : Type u} [Nonempty α], Nontrivial (WithZe
ro α)
· 使用定理 `One.instNonempty`：∀ {α : Type u} [One α], Nonempty α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MonoidWithZeroHom.mem_valueGroup_iff_of_comm`：mem_valueGroup_iff_of_comm
 {y : Bˣ} : y in valueGroup f ↔ exists a, f a != 0 ∧ exists x, f a * y = f x
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Valuation.restrict_pos_iff`：restrict_pos_iff (x : R) : 0 < v.restrict x 
↔ 0 < v x
· 使用引理 `Valuation.restrict_def`：restrict_def (x : R) : v.restrict x = restrict₀ 
(.ofClass v) x
· 使用定理 `WithZero.pos_iff_ne_zero`：∀ {α : Type u_1} [inst : LT α] {x : WithZero α
}, 0 < x ↔ x ≠ 0
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用引理 `MonoidWithZeroHom.ValueGroup₀.restrict₀_eq_zero_iff`：restrict₀_eq_zero_i
ff {a : A} : restrict₀ f a = 0 ↔ f a = 0
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `GroupWithZero.noZeroDivisors`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀
], NoZeroDivisors G₀
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `zero_lt_iff`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_1 : 
Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用引理 `div_eq_iff`：div_eq_iff (hb : b != 0) : a / b = c ↔ a = c * b
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
（共 39 条，此处仅展示前 30 条）
-/
lemma exists_div_eq_of_unit (γ : (ValueGroup₀ (.ofClass v))ˣ) :
    ∃ r s, 0 < v r ∧ 0 < v s ∧ v.restrict r / v.restrict s = γ.1 := by
  set u := WithZero.unzero (Units.ne_zero γ) with hu_def
  obtain ⟨a, ⟨ha, x, hax⟩⟩ := (mem_valueGroup_iff_of_comm _).mp u.2
  have hx : 0 < v x := by
    rw [← restrict_pos_iff, restrict_def, WithZero.pos_iff_ne_zero, ne_eq, restrict₀_eq_zero_iff]
    aesop
  use x, a, hx, zero_lt_iff.mpr ha
  have ha0 : v.restrict a ≠ 0 := by simpa using ha
  rw [div_eq_iff ha0, mul_comm, ← embedding_strictMono.injective.eq_iff, map_mul,
    embedding_restrict, embedding_restrict]
  rw [← MonoidWithZeroHom.coe_ofClass, ← hax]
  congr
  rw [← WithZero.coe_unzero (Units.ne_zero γ)]
  exact Eq.refl ..
/-
**Valuation.IsEquiv.restrict** 是 Mathlib 中的一个定理，位于命名空间 `Valuation.IsEquiv`。
形式化陈述：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : Ring R] [inst_1 : LinearOrderedCo
mmGroupWithZero Γ₀] (v : Valuation R Γ₀)   {Γ₀' : Type u_7} [inst_2 : LinearOrde
redCommGroupWithZero Γ₀'] {w : Valuation R Γ₀'},   v.IsEquiv w → v.restrict.IsEq
uiv w.restrict
参数：v : Valuation R Γ₀。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
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
lemma IsEquiv.restrict {Γ₀' : Type*} [LinearOrderedCommGroupWithZero Γ₀']
    {w : Valuation R Γ₀'} (h : v.IsEquiv w) : v.restrict.IsEquiv w.restrict := by
  simp only [IsEquiv] at h ⊢
  simp [h]

/-- The subgroup of elements whose valuation is less than a certain unit. -/
/-
**Valuation.ltAddSubgroup** 是 Mathlib 中的一个定义，位于命名空间 `Valuation`。
形式化陈述：{R : Type u_3} →   {Γ₀ : Type u_4} →     [inst : Ring R] → [inst_1 : Linea
rOrderedCommGroupWithZero Γ₀] → Valuation R Γ₀ → Γ₀ˣ → AddSubgroup R
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The subgroup of elements whose valuation is less than a certain unit.
-/
@[simps] def ltAddSubgroup (v : Valuation R Γ₀) (γ : Γ₀ˣ) : AddSubgroup R where
  carrier := { x | v x < γ }
  zero_mem' := by simp
  add_mem' {x y} x_in y_in := lt_of_le_of_lt (v.map_add x y) (max_lt x_in y_in)
  neg_mem' x_in := by rwa [Set.mem_ofPred, map_neg]
/-
**Valuation.mem_ltAddSubgroup_iff** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`。
形式化陈述：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : Ring R] [inst_1 : LinearOrderedCo
mmGroupWithZero Γ₀] {v : Valuation R Γ₀}   {γ : Γ₀ˣ} {x : R}, x ∈ v.ltAddSubgrou
p γ ↔ v x < ↑γ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma mem_ltAddSubgroup_iff {v : Valuation R Γ₀} {γ x} :
    x ∈ ltAddSubgroup v γ ↔ v x < γ :=
  Iff.rfl
/-
**Valuation.ltAddSubgroup_monotone** 是 Mathlib 中的一个引理，位于命名空间 `Valuation`。
形式化陈述：ltAddSubgroup_monotone (v : Valuation R Γ₀) : Monotone v.ltAddSubgroup
参数：v : Valuation R Γ₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt'`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, b ≤ a
 → c < b → c < a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Units.val_le_val`：val_le_val [Monoid α] [Preorder α] {a b : αˣ} : (a : α
) <= b ↔ a <= b
-/
lemma ltAddSubgroup_monotone (v : Valuation R Γ₀) : Monotone v.ltAddSubgroup :=
  fun _ _ h _ ↦ (Units.val_le_val.mpr h).trans_lt'
/-
**Valuation.ltAddSubgroup_le_leAddSubgroup** 是 Mathlib 中的一个引理，位于命名空间 `Valuation`
。
形式化陈述：ltAddSubgroup_le_leAddSubgroup (v : Valuation R Γ₀) (γ : Γ₀ˣ) : v.ltAddSub
group γ <= v.leAddSubgroup γ
参数：v : Valuation R Γ₀；γ : Γ₀ˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
lemma ltAddSubgroup_le_leAddSubgroup (v : Valuation R Γ₀) (γ : Γ₀ˣ) :
    v.ltAddSubgroup γ ≤ v.leAddSubgroup γ :=
  fun _ h ↦ h.le

@[simp]
/-
**Valuation.leAddSubgroup_zero** 是 Mathlib 中的一个引理，位于命名空间 `Valuation`。
形式化陈述：leAddSubgroup_zero {K : Type*} [Field K] (v : Valuation K Γ₀) : v.leAddSub
group 0 = ⊥
参数：v : Valuation K Γ₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroup.ext`：∀ {G : Type u_1} [inst : AddGroup G] {H K : AddSubgroup
 G}, (∀ (x : G), x ∈ H ↔ x ∈ K) → H = K
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma leAddSubgroup_zero {K : Type*} [Field K] (v : Valuation K Γ₀) :
    v.leAddSubgroup 0 = ⊥ := by
  ext; simp

end Group

end Basic

section IsNontrivial

variable [Ring R] [LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation R Γ₀)

/-- A valuation on a ring is nontrivial if there exists an element with valuation
not equal to `0` or `1`. -/
/-
**Valuation.IsNontrivial** 是 Mathlib 中的一个归纳类型，位于命名空间 `Valuation`。
形式化陈述：{R : Type u_3} →   {Γ₀ : Type u_4} → [inst : Ring R] → [inst_1 : LinearOrd
eredCommMonoidWithZero Γ₀] → Valuation R Γ₀ → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A valuation on a ring is nontrivial if there exists an element with valuation
not equal to `0` or `1`.
-/
class IsNontrivial : Prop where
  exists_val_nontrivial : ∃ x : R, v x ≠ 0 ∧ v x ≠ 1
/-
**Valuation.IsNontrivial.nontrivial_codomain** 是 Mathlib 中的一个定理，位于命名空间 `Valuatio
n.IsNontrivial`。
形式化陈述：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : Ring R] [inst_1 : LinearOrderedCo
mmMonoidWithZero Γ₀] (v : Valuation R Γ₀)   [hv : v.IsNontrivial], Nontrivial Γ₀
参数：v : Valuation R Γ₀。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Valuation.IsNontrivial.exists_val_nontrivial`：∀ {R : Type u_3} {Γ₀ : Typ
e u_4} {inst : Ring R} {inst_1 : LinearOrderedCommMonoidWithZero Γ₀} {v : Valuat
ion R Γ₀}   [self : v.IsNontrivial…
-/
lemma IsNontrivial.nontrivial_codomain [hv : IsNontrivial v] :
    Nontrivial Γ₀ := by
  obtain ⟨x, hx0, hx1⟩ := hv.exists_val_nontrivial
  exact ⟨v x, 1, hx1⟩
/-
**Valuation.not_isNontrivial_one** 是 Mathlib 中的一个引理，位于命名空间 `Valuation`。
形式化陈述：not_isNontrivial_one [IsDomain R] [DecidablePred fun x : R => x = 0] : ¬(1
 : Valuation R Γ₀).IsNontrivial
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Valuation.one_apply_of_ne_zero`：one_apply_of_ne_zero {x : R} (hx : x != 
0) : (1 : Valuation R Γ₀) x = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma not_isNontrivial_one [IsDomain R] [DecidablePred fun x : R ↦ x = 0] :
    ¬(1 : Valuation R Γ₀).IsNontrivial := by
  rintro ⟨⟨x, hx, hx'⟩⟩
  rcases eq_or_ne x 0 with rfl | hx0 <;>
  simp_all [one_apply_of_ne_zero]
/-
**Valuation.** 是 Mathlib 中的一个实例，位于命名空间 `Valuation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] {v : Valuation R Γ₀}
    [hv : v.IsNontrivial] : Nontrivial (MonoidWithZeroHom.valueMonoid (.ofClass v)) := by
  obtain ⟨x, h0, h1⟩ := hv.exists_val_nontrivial
  rw [Submonoid.nontrivial_iff_exists_ne_one]
  use (Units.mk0 (v x) h0), (MonoidWithZeroHom.ofClass v).mem_valueMonoid (Set.mem_range_self x)
  simpa [Units.ext_iff]
/-
**Valuation.** 是 Mathlib 中的一个实例，位于命名空间 `Valuation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] {v : Valuation R Γ₀}
    [hv : v.IsNontrivial] : Nontrivial (MonoidWithZeroHom.valueGroup (.ofClass v)) := by
  obtain ⟨x, h0, h1⟩ := hv.exists_val_nontrivial
  rw [Subgroup.nontrivial_iff_exists_ne_one]
  use (Units.mk0 (v x) h0), (MonoidWithZeroHom.ofClass v).mem_valueGroup (Set.mem_range_self x)
  simpa [Units.ext_iff]

section Field

variable {K : Type*} [DivisionRing K] {w : Valuation K Γ₀}

/-- For fields, being nontrivial is equivalent to the existence of a unit with valuation
not equal to `1`. -/
/-
**Valuation.isNontrivial_iff_exists_unit** 是 Mathlib 中的一个引理，位于命名空间 `Valuation`。
形式化陈述：isNontrivial_iff_exists_unit : w.IsNontrivial ↔ exists x : Kˣ, w x != 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Valuation.ne_zero_iff`：ne_zero_iff [Nontrivial Γ₀] (v : Valuation K Γ₀) 
{x : K} : v x != 0 ↔ x != 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Units.ne_zero`：ne_zero [Nontrivial M₀] (u : M₀ˣ) : (u : M₀) != 0
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K

--- 原说明 ---
For fields, being nontrivial is equivalent to the existence of a unit with valua
tion
not equal to `1`.
-/
lemma isNontrivial_iff_exists_unit :
    w.IsNontrivial ↔ ∃ x : Kˣ, w x ≠ 1 :=
  ⟨fun ⟨x, hx0, hx1⟩ ↦
    have : Nontrivial Γ₀ := ⟨w x, 0, hx0⟩
    ⟨Units.mk0 x (w.ne_zero_iff.mp hx0), hx1⟩,
    fun ⟨x, hx⟩ ↦
    have : Nontrivial Γ₀ := ⟨w x, 1, hx⟩
    ⟨x, w.ne_zero_iff.mpr (Units.ne_zero x), hx⟩⟩
/-
**Valuation.IsNontrivial.exists_lt_one** 是 Mathlib 中的一个定理，位于命名空间 `Valuation.IsNo
ntrivial`。
形式化陈述：∀ {K : Type u_7} [inst : DivisionRing K] {Γ₀ : Type u_8} [inst_1 : LinearO
rderedCommGroupWithZero Γ₀]   {v : Valuation K Γ₀} [hv : v.IsNontrivial], ∃ x, x
 ≠ 0 ∧ v x < 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Valuation.isNontrivial_iff_exists_unit`：isNontrivial_iff_exists_unit : w
.IsNontrivial ↔ exists x : Kˣ, w x != 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ne_iff_lt_or_gt`：ne_iff_lt_or_gt : a != b ↔ a < b ∨ b < a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
lemma IsNontrivial.exists_lt_one {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    {v : Valuation K Γ₀} [hv : v.IsNontrivial] :
    ∃ x ≠ 0, v x < 1 := by
  obtain ⟨x, hx⟩ := isNontrivial_iff_exists_unit.mp hv
  rw [ne_iff_lt_or_gt] at hx
  rcases hx with hx | hx
  · use x
    simp [hx]
  · use x⁻¹
    simp [-map_inv₀, ← one_lt_val_iff, hx]
/-
**Valuation.isNontrivial_iff_exists_lt_one** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`
。
形式化陈述：isNontrivial_iff_exists_lt_one {Γ₀ : Type*} [LinearOrderedCommGroupWithZer
o Γ₀] (v : Valuation K Γ₀) : v.IsNontrivial ↔ exists x != 0, v x < 1
参数：v : Valuation K Γ₀。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Valuation.IsNontrivial.exists_lt_one`：∀ {K : Type u_7} [inst : DivisionR
ing K] {Γ₀ : Type u_8} [inst_1 : LinearOrderedCommGroupWithZero Γ₀]   {v : Valua
tion K Γ₀} [hv : v.IsNontr…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem isNontrivial_iff_exists_lt_one {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation K Γ₀) : v.IsNontrivial ↔ ∃ x ≠ 0, v x < 1 :=
  ⟨fun h ↦ by simpa using h.exists_lt_one (v := v), fun ⟨x, hx0, hx1⟩ ↦ ⟨x, by simp [hx0, hx1.ne]⟩⟩
/-
**Valuation.IsNontrivial.exists_one_lt** 是 Mathlib 中的一个定理，位于命名空间 `Valuation.IsNo
ntrivial`。
形式化陈述：∀ {K : Type u_7} [inst : DivisionRing K] {Γ₀ : Type u_8} [inst_1 : LinearO
rderedCommGroupWithZero Γ₀]   {v : Valuation K Γ₀} [hv : v.IsNontrivial], ∃ x, 1
 < v x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Valuation.IsNontrivial.exists_lt_one`：∀ {K : Type u_7} [inst : DivisionR
ing K] {Γ₀ : Type u_8} [inst_1 : LinearOrderedCommGroupWithZero Γ₀]   {v : Valua
tion K Γ₀} [hv : v.IsNontr…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_inv₀`：map_inv₀ : f a⁻¹ = (f a)⁻¹
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用引理 `one_lt_inv₀`：one_lt_inv₀ (ha : 0 < a) : 1 < a⁻¹ ↔ a < 1
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `zero_lt_iff`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_1 : 
Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
lemma IsNontrivial.exists_one_lt {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    {v : Valuation K Γ₀} [hv : v.IsNontrivial] :
    ∃ x, 1 < v x := by
  obtain ⟨x, h0, h1⟩ := hv.exists_lt_one
  use x⁻¹
  simp [one_lt_inv₀ (zero_lt_iff.mpr (by simp [h0] : v x ≠ 0)), h1]
/-
**Valuation.IsNontrivial_iff_exists_one_lt** 是 Mathlib 中的一个引理，位于命名空间 `Valuation`
。
形式化陈述：IsNontrivial_iff_exists_one_lt {Γ₀ : Type*} [LinearOrderedCommGroupWithZer
o Γ₀] {v : Valuation K Γ₀} : v.IsNontrivial ↔ exists x, 1 < v x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Valuation.IsNontrivial.exists_one_lt`：∀ {K : Type u_7} [inst : DivisionR
ing K] {Γ₀ : Type u_8} [inst_1 : LinearOrderedCommGroupWithZero Γ₀]   {v : Valua
tion K Γ₀} [hv : v.IsNontr…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma IsNontrivial_iff_exists_one_lt {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    {v : Valuation K Γ₀} : v.IsNontrivial ↔ ∃ x, 1 < v x :=
  ⟨fun h ↦ by simpa using h.exists_one_lt (v := v), fun ⟨x, hx1⟩ ↦ ⟨x, by aesop⟩⟩

end Field

end IsNontrivial

section IsTrivialOn

variable [LinearOrderedCommMonoidWithZero Γ₀]

/-- A valuation on an `A`-algebra `B` is trivial on constants if the nonzero elements of the
  base ring `A` are mapped to `1`.

  This is true, for example, when `A` is a finite field.
  See `Valuation.FiniteField.instIsTrivialOn`. -/
/-
**Valuation.IsTrivialOn** 是 Mathlib 中的一个归纳类型，位于命名空间 `Valuation`。
形式化陈述：{Γ₀ : Type u_4} →   [inst : LinearOrderedCommMonoidWithZero Γ₀] →     {B :
 Type u_7} →       (A : Type u_8) → [inst_1 : CommSemiring A] → [inst_2 : Ring B
] → [Algebra A B] → Valuation B Γ₀ → Prop
参数：A : Type u_8。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A valuation on an `A`-algebra `B` is trivial on constants if the nonzero element
s of the
  base ring `A` are mapped to `1`.

  This is true, for example, when `A` is a finite field.
  See `Valuation.FiniteField.instIsTrivialOn`.
-/
class IsTrivialOn {B : Type*} (A : Type*) [CommSemiring A] [Ring B] [Algebra A B]
    (v : Valuation B Γ₀) where
  eq_one : ∀ a : A, a ≠ 0 → v (algebraMap A B a) = 1

attribute [grind =>] Valuation.IsTrivialOn.eq_one

variable {B : Type*} {A : Type*} [CommSemiring A] [Ring B] [Algebra A B] (v : Valuation B Γ₀)
  [v.IsTrivialOn A]

@[simp]
/-
**Valuation.IsTrivialOn.valuation_algebraMap_le_one** 是 Mathlib 中的一个定理，位于命名空间 `V
aluation.IsTrivialOn`。
形式化陈述：∀ {Γ₀ : Type u_4} [inst : LinearOrderedCommMonoidWithZero Γ₀] {B : Type u_
7} {A : Type u_8} [inst_1 : CommSemiring A]   [inst_2 : Ring B] [inst_3 : Algebr
a A B] (v : Valuation B Γ₀) [Valuation.IsTrivialOn A v] (a : A),   v ((algebraMa
p A B) a) ≤ 1
参数：v : Valuation B Γ₀；a : A；(algebraMap A B) a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsTrivialOn.valuation_algebraMap_le_one (a : A) : v (algebraMap A B a) ≤ 1 := by
  by_cases a = 0 <;> grind [zero_le]

end IsTrivialOn

namespace IsEquiv

variable [Ring R] [LinearOrderedCommMonoidWithZero Γ₀] [LinearOrderedCommMonoidWithZero Γ'₀]
  [LinearOrderedCommMonoidWithZero Γ''₀]
  {v : Valuation R Γ₀} {v₁ : Valuation R Γ₀} {v₂ : Valuation R Γ'₀} {v₃ : Valuation R Γ''₀}

@[refl]
/-
**Valuation.IsEquiv.refl** 是 Mathlib 中的一个定理，位于命名空间 `Valuation.IsEquiv`。
形式化陈述：refl : v.IsEquiv v
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.refl`：∀ (a : Prop), a ↔ a
-/
theorem refl : v.IsEquiv v := fun _ _ => Iff.refl _

@[symm]
/-
**Valuation.IsEquiv.symm** 是 Mathlib 中的一个定理，位于命名空间 `Valuation.IsEquiv`。
形式化陈述：symm (h : v₁.IsEquiv v₂) : v₂.IsEquiv v₁
参数：h : v₁.IsEquiv v₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
-/
theorem symm (h : v₁.IsEquiv v₂) : v₂.IsEquiv v₁ := fun _ _ => Iff.symm (h _ _)

@[trans]
/-
**Valuation.IsEquiv.trans** 是 Mathlib 中的一个定理，位于命名空间 `Valuation.IsEquiv`。
形式化陈述：trans (h₁₂ : v₁.IsEquiv v₂) (h₂₃ : v₂.IsEquiv v₃) : v₁.IsEquiv v₃
参数：h₁₂ : v₁.IsEquiv v₂；h₂₃ : v₂.IsEquiv v₃。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
-/
theorem trans (h₁₂ : v₁.IsEquiv v₂) (h₂₃ : v₂.IsEquiv v₃) : v₁.IsEquiv v₃ := fun _ _ =>
  Iff.trans (h₁₂ _ _) (h₂₃ _ _)
/-
**Valuation.IsEquiv.of_eq** 是 Mathlib 中的一个定理，位于命名空间 `Valuation.IsEquiv`。
形式化陈述：of_eq {v' : Valuation R Γ₀} (h : v = v') : v.IsEquiv v'
参数：h : v = v'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Valuation.IsEquiv.refl`：refl : v.IsEquiv v
-/
theorem of_eq {v' : Valuation R Γ₀} (h : v = v') : v.IsEquiv v' := by subst h; rfl
/-
**Valuation.IsEquiv.map** 是 Mathlib 中的一个定理，位于命名空间 `Valuation.IsEquiv`。
形式化陈述：map {v' : Valuation R Γ₀} (f : Γ₀ ->*₀ Γ'₀) (hf : Monotone f) (inf : Injec
tive f) (h : v.IsEquiv v') : (v.map f hf).IsEquiv (v'.map f hf)
参数：f : Γ₀ ->*₀ Γ'₀；hf : Monotone f；inf : Injective f；h : v.IsEquiv v'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.strictMono_of_injective`：Monotone.strictMono_of_injective (h₁ :
 Monotone f) (h₂ : Injective f) : StrictMono f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `StrictMono.le_iff_le`：StrictMono.le_iff_le (hf : StrictMono f) {a b : α}
 : f a <= f b ↔ a <= b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem map {v' : Valuation R Γ₀} (f : Γ₀ →*₀ Γ'₀) (hf : Monotone f) (inf : Injective f)
    (h : v.IsEquiv v') : (v.map f hf).IsEquiv (v'.map f hf) :=
  let H : StrictMono f := hf.strictMono_of_injective inf
  fun r s =>
  calc
    f (v r) ≤ f (v s) ↔ v r ≤ v s := by rw [H.le_iff_le]
    _ ↔ v' r ≤ v' s := h r s
    _ ↔ f (v' r) ≤ f (v' s) := by rw [H.le_iff_le]

/-- `comap` preserves equivalence. -/
/-
**Valuation.IsEquiv.comap** 是 Mathlib 中的一个定理，位于命名空间 `Valuation.IsEquiv`。
形式化陈述：comap {S : Type*} [Ring S] (f : S ->+* R) (h : v₁.IsEquiv v₂) : (v₁.comap 
f).IsEquiv (v₂.comap f)
参数：f : S ->+* R；h : v₁.IsEquiv v₂。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`comap` preserves equivalence.
-/
theorem comap {S : Type*} [Ring S] (f : S →+* R) (h : v₁.IsEquiv v₂) :
    (v₁.comap f).IsEquiv (v₂.comap f) := fun r s => h (f r) (f s)
/-
**Valuation.IsEquiv.eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `Valuation.IsEquiv`。
形式化陈述：eq_iff (h : v₁.IsEquiv v₂) {r s : R} : v₁ r = v₁ s ↔ v₂ r = v₂ s
参数：h : v₁.IsEquiv v₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_congr`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∧ b ↔ c ∧ d)
-/
theorem eq_iff (h : v₁.IsEquiv v₂) {r s : R} : v₁ r = v₁ s ↔ v₂ r = v₂ s := by
  simpa only [le_antisymm_iff] using and_congr (h r s) (h s r)
@[deprecated (since := "2026-03-05")] alias val_eq := eq_iff
/-
**Valuation.IsEquiv.eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Valuation.IsEquiv`。
形式化陈述：eq_zero (h : v₁.IsEquiv v₂) {r : R} : v₁ r = 0 ↔ v₂ r = 0
参数：h : v₁.IsEquiv v₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Valuation.IsEquiv.eq_iff`：eq_iff (h : v₁.IsEquiv v₂) {r s : R} : v₁ r = 
v₁ s ↔ v₂ r = v₂ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Valuation.map_zero`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : Ring R] [in
st_1 : LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation R Γ₀),   v 0 = 0
-/
theorem eq_zero (h : v₁.IsEquiv v₂) {r : R} : v₁ r = 0 ↔ v₂ r = 0 := by
  have : v₁ r = v₁ 0 ↔ v₂ r = v₂ 0 := h.eq_iff
  rwa [v₁.map_zero, v₂.map_zero] at this
/-
**Valuation.IsEquiv.ofClass_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `Valuation.IsEquiv
`。
形式化陈述：ofClass_eq_zero (h : v₁.IsEquiv v₂) {r : R} : (MonoidWithZeroHom.ofClass v
₁) r = 0 ↔ (MonoidWithZeroHom.ofClass v₂) r = 0
参数：h : v₁.IsEquiv v₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Valuation.IsEquiv.eq_zero`：eq_zero (h : v₁.IsEquiv v₂) {r : R} : v₁ r = 
0 ↔ v₂ r = 0
-/
lemma ofClass_eq_zero (h : v₁.IsEquiv v₂) {r : R} : (MonoidWithZeroHom.ofClass v₁) r = 0 ↔
  (MonoidWithZeroHom.ofClass v₂) r = 0 := eq_zero h

@[deprecated "use `(eq_zero _).ne` instead." (since := "2026-01-05")]
/-
**Valuation.IsEquiv.ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Valuation.IsEquiv`。
形式化陈述：ne_zero (h : v₁.IsEquiv v₂) {r : R} : v₁ r != 0 ↔ v₂ r != 0
参数：h : v₁.IsEquiv v₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.ne`：∀ {α : Sort u_1} {β : Sort u_2} {a b : α} {c d : β}, (a = b ↔ c 
= d) → (a ≠ b ↔ c ≠ d)
· 使用定理 `Valuation.IsEquiv.eq_zero`：eq_zero (h : v₁.IsEquiv v₂) {r : R} : v₁ r = 
0 ↔ v₂ r = 0
-/
theorem ne_zero (h : v₁.IsEquiv v₂) {r : R} : v₁ r ≠ 0 ↔ v₂ r ≠ 0 :=
  (eq_zero h).ne
/-
**Valuation.IsEquiv.pos_iff** 是 Mathlib 中的一个引理，位于命名空间 `Valuation.IsEquiv`。
形式化陈述：pos_iff (h : v₁.IsEquiv v₂) {x : R} : 0 < v₁ x ↔ 0 < v₂ x
参数：h : v₁.IsEquiv v₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_lt_iff`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_1 : 
Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Iff.ne`：∀ {α : Sort u_1} {β : Sort u_2} {a b : α} {c d : β}, (a = b ↔ c 
= d) → (a ≠ b ↔ c ≠ d)
· 使用定理 `Valuation.IsEquiv.eq_zero`：eq_zero (h : v₁.IsEquiv v₂) {r : R} : v₁ r = 
0 ↔ v₂ r = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma pos_iff (h : v₁.IsEquiv v₂) {x : R} : 0 < v₁ x ↔ 0 < v₂ x := by
  rw [zero_lt_iff, zero_lt_iff, h.eq_zero.ne]
/-
**Valuation.IsEquiv.le_iff_le** 是 Mathlib 中的一个引理，位于命名空间 `Valuation.IsEquiv`。
形式化陈述：le_iff_le (h : v₁.IsEquiv v₂) {x y : R} : v₁ x <= v₁ y ↔ v₂ x <= v₂ y
参数：h : v₁.IsEquiv v₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma le_iff_le (h : v₁.IsEquiv v₂) {x y : R} :
    v₁ x ≤ v₁ y ↔ v₂ x ≤ v₂ y := h x y
/-
**Valuation.IsEquiv.lt_iff_lt** 是 Mathlib 中的一个引理，位于命名空间 `Valuation.IsEquiv`。
形式化陈述：lt_iff_lt (h : v₁.IsEquiv v₂) {x y : R} : v₁ x < v₁ y ↔ v₂ x < v₂ y
参数：h : v₁.IsEquiv v₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `le_iff_le_iff_lt_iff_lt`：le_iff_le_iff_lt_iff_lt {β} [LinearOrder α] [Li
nearOrder β] {a b : α} {c d : β} : (a <= b ↔ c <= d) ↔ (b < a ↔ d < c)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma lt_iff_lt (h : v₁.IsEquiv v₂) {x y : R} :
    v₁ x < v₁ y ↔ v₂ x < v₂ y := by
  rw [← le_iff_le_iff_lt_iff_lt, h]
/-
**Valuation.IsEquiv.le_one_iff_le_one** 是 Mathlib 中的一个引理，位于命名空间 `Valuation.IsEqu
iv`。
形式化陈述：le_one_iff_le_one (h : v₁.IsEquiv v₂) {x : R} : v₁ x <= 1 ↔ v₂ x <= 1
参数：h : v₁.IsEquiv v₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Valuation.map_one`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : Ring R] [ins
t_1 : LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation R Γ₀),   v 1 = 1
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma le_one_iff_le_one (h : v₁.IsEquiv v₂) {x : R} :
    v₁ x ≤ 1 ↔ v₂ x ≤ 1 := by
  rw [← v₁.map_one, h, map_one]
/-
**Valuation.IsEquiv.one_le_iff_one_le** 是 Mathlib 中的一个引理，位于命名空间 `Valuation.IsEqu
iv`。
形式化陈述：one_le_iff_one_le (h : v₁.IsEquiv v₂) {x : R} : 1 <= v₁ x ↔ 1 <= v₂ x
参数：h : v₁.IsEquiv v₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Valuation.map_one`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : Ring R] [ins
t_1 : LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation R Γ₀),   v 1 = 1
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma one_le_iff_one_le (h : v₁.IsEquiv v₂) {x : R} :
    1 ≤ v₁ x ↔ 1 ≤ v₂ x := by
  rw [← v₁.map_one, h, map_one]
/-
**Valuation.IsEquiv.eq_one_iff_eq_one** 是 Mathlib 中的一个引理，位于命名空间 `Valuation.IsEqu
iv`。
形式化陈述：eq_one_iff_eq_one (h : v₁.IsEquiv v₂) {x : R} : v₁ x = 1 ↔ v₂ x = 1
参数：h : v₁.IsEquiv v₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Valuation.map_one`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : Ring R] [ins
t_1 : LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation R Γ₀),   v 1 = 1
· 使用定理 `Valuation.IsEquiv.eq_iff`：eq_iff (h : v₁.IsEquiv v₂) {r s : R} : v₁ r = 
v₁ s ↔ v₂ r = v₂ s
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma eq_one_iff_eq_one (h : v₁.IsEquiv v₂) {x : R} :
    v₁ x = 1 ↔ v₂ x = 1 := by
  rw [← v₁.map_one, h.eq_iff, map_one]
/-
**Valuation.IsEquiv.lt_one_iff_lt_one** 是 Mathlib 中的一个引理，位于命名空间 `Valuation.IsEqu
iv`。
形式化陈述：lt_one_iff_lt_one (h : v₁.IsEquiv v₂) {x : R} : v₁ x < 1 ↔ v₂ x < 1
参数：h : v₁.IsEquiv v₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Valuation.map_one`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : Ring R] [ins
t_1 : LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation R Γ₀),   v 1 = 1
· 使用引理 `Valuation.IsEquiv.lt_iff_lt`：lt_iff_lt (h : v₁.IsEquiv v₂) {x y : R} : v
₁ x < v₁ y ↔ v₂ x < v₂ y
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma lt_one_iff_lt_one (h : v₁.IsEquiv v₂) {x : R} :
    v₁ x < 1 ↔ v₂ x < 1 := by
  rw [← v₁.map_one, h.lt_iff_lt, map_one]
/-
**Valuation.IsEquiv.one_lt_iff_one_lt** 是 Mathlib 中的一个引理，位于命名空间 `Valuation.IsEqu
iv`。
形式化陈述：one_lt_iff_one_lt (h : v₁.IsEquiv v₂) {x : R} : 1 < v₁ x ↔ 1 < v₂ x
参数：h : v₁.IsEquiv v₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Valuation.map_one`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : Ring R] [ins
t_1 : LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation R Γ₀),   v 1 = 1
· 使用引理 `Valuation.IsEquiv.lt_iff_lt`：lt_iff_lt (h : v₁.IsEquiv v₂) {x y : R} : v
₁ x < v₁ y ↔ v₂ x < v₂ y
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma one_lt_iff_one_lt (h : v₁.IsEquiv v₂) {x : R} :
    1 < v₁ x ↔ 1 < v₂ x := by
  rw [← v₁.map_one, h.lt_iff_lt, map_one]
/-
**Valuation.IsEquiv.isTrivialOn** 是 Mathlib 中的一个定理，位于命名空间 `Valuation.IsEquiv`。
形式化陈述：isTrivialOn {A : Type*} [CommSemiring A] [Algebra A R] (h : v₁.IsEquiv v₂)
 (h₁ : IsTrivialOn A v₁) : IsTrivialOn A v₂ where eq_one _ ha
参数：h : v₁.IsEquiv v₂；h₁ : IsTrivialOn A v₁。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Valuation.IsEquiv.eq_one_iff_eq_one`：eq_one_iff_eq_one (h : v₁.IsEquiv v
₂) {x : R} : v₁ x = 1 ↔ v₂ x = 1
· 使用定理 `Valuation.IsTrivialOn.eq_one`：∀ {Γ₀ : Type u_4} {inst : LinearOrderedCom
mMonoidWithZero Γ₀} {B : Type u_7} {A : Type u_8} {inst_1 : CommSemiring A}   {i
nst_2 : Ring B} {i…
-/
theorem isTrivialOn {A : Type*} [CommSemiring A] [Algebra A R] (h : v₁.IsEquiv v₂)
    (h₁ : IsTrivialOn A v₁) : IsTrivialOn A v₂ where
  eq_one _ ha := h.eq_one_iff_eq_one.mp (IsTrivialOn.eq_one _ ha)
/-
**Valuation.IsEquiv.isTrivialOn_iff** 是 Mathlib 中的一个定理，位于命名空间 `Valuation.IsEquiv
`。
形式化陈述：isTrivialOn_iff {A : Type*} [CommSemiring A] [Algebra A R] (h : v₁.IsEquiv
 v₂) : IsTrivialOn A v₁ ↔ IsTrivialOn A v₂
参数：h : v₁.IsEquiv v₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Valuation.IsEquiv.isTrivialOn`：isTrivialOn {A : Type*} [CommSemiring A] 
[Algebra A R] (h : v₁.IsEquiv v₂) (h₁ : IsTrivialOn A v₁) : IsTrivialOn A v₂ whe
re eq_one _ ha
· 使用定理 `Valuation.IsEquiv.symm`：symm (h : v₁.IsEquiv v₂) : v₂.IsEquiv v₁
-/
theorem isTrivialOn_iff {A : Type*} [CommSemiring A] [Algebra A R] (h : v₁.IsEquiv v₂) :
    IsTrivialOn A v₁ ↔ IsTrivialOn A v₂ :=
  ⟨fun h₁ ↦ h.isTrivialOn h₁, fun h₂ ↦ h.symm.isTrivialOn h₂⟩

end IsEquiv

section LinearOrderedCommMonoidWithZero

variable [Ring R] [LinearOrderedCommMonoidWithZero Γ₀] [LinearOrderedCommMonoidWithZero Γ'₀]
  {v : Valuation R Γ₀} {v' : Valuation R Γ'₀}

/-
**Valuation.isEquiv_map_self_of_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`
。
形式化陈述：isEquiv_map_self_of_strictMono (f : Γ₀ ->*₀ Γ'₀) (H : StrictMono f) : IsEq
uiv (v.map f H.monotone) v
参数：f : Γ₀ ->*₀ Γ'₀；H : StrictMono f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.monotone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictMono f → Monotone f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `StrictMono.le_iff_le`：StrictMono.le_iff_le (hf : StrictMono f) {a b : α}
 : f a <= f b ↔ a <= b
-/
theorem isEquiv_map_self_of_strictMono (f : Γ₀ →*₀ Γ'₀) (H : StrictMono f) :
    IsEquiv (v.map f H.monotone) v := fun _x _y =>
  ⟨H.le_iff_le.mp, fun h => H.monotone h⟩
/-
**Valuation.isEquiv_iff_val_lt_val** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`。
形式化陈述：isEquiv_iff_val_lt_val : v.IsEquiv v' ↔ forall {x y : R}, v x < v y ↔ v' x
 < v' y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
-/
theorem isEquiv_iff_val_lt_val : v.IsEquiv v' ↔ ∀ {x y : R}, v x < v y ↔ v' x < v' y := by
  simp only [IsEquiv, le_iff_le_iff_lt_iff_lt]
  exact forall_comm
/-
**Valuation.isNontrivial_of_isEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`。
形式化陈述：isNontrivial_of_isEquiv (h : v.IsEquiv v') (hv : v.IsNontrivial) : v'.IsNo
ntrivial
参数：h : v.IsEquiv v'；hv : v.IsNontrivial。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Valuation.IsEquiv.eq_zero`：eq_zero (h : v₁.IsEquiv v₂) {r : R} : v₁ r = 
0 ↔ v₂ r = 0
· 使用引理 `Valuation.IsEquiv.eq_one_iff_eq_one`：eq_one_iff_eq_one (h : v₁.IsEquiv v
₂) {x : R} : v₁ x = 1 ↔ v₂ x = 1
-/
theorem isNontrivial_of_isEquiv (h : v.IsEquiv v') (hv : v.IsNontrivial) : v'.IsNontrivial := by
  obtain ⟨x, hx⟩ := hv
  use x
  simpa [← Valuation.IsEquiv.eq_one_iff_eq_one h, ← Valuation.IsEquiv.eq_zero h]
/-
**Valuation.IsEquiv.isNontrivial_iff** 是 Mathlib 中的一个定理，位于命名空间 `Valuation.IsEqui
v`。
形式化陈述：∀ {R : Type u_3} {Γ₀ : Type u_4} {Γ'₀ : Type u_5} [inst : Ring R] [inst_1 
: LinearOrderedCommMonoidWithZero Γ₀]   [inst_2 : LinearOrderedCommMonoidWithZer
o Γ'₀] {v : Valuation R Γ₀} {v' : Valuation R Γ'₀},   v.IsEquiv v' → (v.IsNontri
vial ↔ v'.IsNontrivial)
参数：v.IsNontrivial ↔ v'.IsNontrivial。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Valuation.isNontrivial_of_isEquiv`：isNontrivial_of_isEquiv (h : v.IsEqui
v v') (hv : v.IsNontrivial) : v'.IsNontrivial
· 使用定理 `Valuation.IsEquiv.symm`：symm (h : v₁.IsEquiv v₂) : v₂.IsEquiv v₁
-/
theorem IsEquiv.isNontrivial_iff (h : v.IsEquiv v') :
    v.IsNontrivial ↔ v'.IsNontrivial :=
  ⟨fun hv ↦ isNontrivial_of_isEquiv h hv, fun hv ↦ isNontrivial_of_isEquiv h.symm hv⟩

end LinearOrderedCommMonoidWithZero

section LinearOrderedCommGroupWithZero

variable [LinearOrderedCommGroupWithZero Γ₀] [LinearOrderedCommGroupWithZero Γ'₀]
  [LinearOrderedCommGroupWithZero Γ''₀]

section Ring

variable [Ring R] {v : Valuation R Γ₀} {w : Valuation R Γ'₀} {u : Valuation R Γ''₀}

namespace IsEquiv

open MonoidWithZeroHom MonoidWithZeroHom.ValueGroup₀

/-- An equivalence of valuations `v.IsEquiv w` induces the following map from `ValueGroup₀ v` to
`ValueGroup₀ w`: given `x : ValueGroup₀ v` and nonzero `a b : R` such that `(v a) * x = (v b)`,
`valueGroup₀Fun x` is defined as `(w b) * (w a)⁻¹`. -/
/-
**Valuation.IsEquiv.valueGroup** 是 Mathlib 中的一个定义，位于命名空间 `Valuation.IsEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An equivalence of valuations `v.IsEquiv w` induces the following map from `Value
Group₀ v` to
`ValueGroup₀ w`: given `x : ValueGroup₀ v` and nonzero `a b : R` such that `(v a
) * x = (v b)`,
`valueGroup₀Fun x` is defined as `(w b) * (w a)⁻¹`.
-/
noncomputable def valueGroup₀Fun (h : v.IsEquiv w) (x : ValueGroup₀ (.ofClass v)) :
    ValueGroup₀ (.ofClass w) :=
  if hx : x = 0 then 0 else
    haveI c := (x.zero_or_exists_mk'.resolve_left hx).choose
    valueGroup.mk (.ofClass w) c.1.1 c.1.2 (h.eq_zero.ne.mp c.2.1) (h.eq_zero.ne.mp c.2.2)
/-
**Valuation.IsEquiv.valueGroup** 是 Mathlib 中的一个定理，位于命名空间 `Valuation.IsEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem valueGroup₀Fun_spec (h : v.IsEquiv w) {r s : R} (hr : (MonoidWithZeroHom.ofClass v) r ≠ 0)
    (hs : (MonoidWithZeroHom.ofClass v) s ≠ 0)
    (hr' : (MonoidWithZeroHom.ofClass w) r ≠ 0 := h.ofClass_eq_zero.ne.1 hr)
    (hs' : (MonoidWithZeroHom.ofClass w) s ≠ 0 := h.ofClass_eq_zero.ne.1 hs) :
    valueGroup₀Fun h (valueGroup.mk (.ofClass v) r s hr hs) =
      valueGroup.mk (.ofClass w) r s hr' hs' := by
  rw [valueGroup₀Fun, dif_neg (by simp)]
  generalize_proofs _ _ _ _ H _
  have c_spec := H.choose_spec
  simp only [MonoidWithZeroHom.coe_ofClass, ne_eq, WithZero.coe_inj, valueGroup.mk_inj] at c_spec ⊢
  rwa [← h.eq_iff, eq_comm]
/-
**Valuation.IsEquiv.valueGroup** 是 Mathlib 中的一个定理，位于命名空间 `Valuation.IsEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem valueGroup₀Fun_zero (h : v.IsEquiv w) : valueGroup₀Fun h 0 = 0 := by simp [valueGroup₀Fun]

/-- The isomorphism between the `ValueGroup₀`'s of two equivalent valuations. -/
/-
**Valuation.IsEquiv.orderMonoidIso** 是 Mathlib 中的一个定义，位于命名空间 `Valuation.IsEquiv`
。
形式化陈述：orderMonoidIso (h : v.IsEquiv w) : ValueGroup₀ (.ofClass v) ≃*o ValueGroup
₀ (.ofClass w) where toFun
参数：h : v.IsEquiv w。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism between the `ValueGroup₀`'s of two equivalent valuations.
-/
noncomputable def orderMonoidIso (h : v.IsEquiv w) :
    ValueGroup₀ (.ofClass v) ≃*o ValueGroup₀ (.ofClass w) where
  toFun := valueGroup₀Fun h
  invFun := valueGroup₀Fun h.symm
  map_mul' x y := by
    obtain _ | ⟨r₁, s₁, hr₁, hs₁, rfl⟩ := x.zero_or_exists_mk
    · simp_all [valueGroup₀Fun_zero]
    obtain _ | ⟨r₂, s₂, hr₂, hs₂, rfl⟩ := y.zero_or_exists_mk
    · simp_all [valueGroup₀Fun_zero]
    simp [← WithZero.coe_mul, valueGroup.mk_mul, valueGroup₀Fun_spec h]
  left_inv x := by
    obtain _ | ⟨r₁, s₁, hr₁, hs₁, rfl⟩ := x.zero_or_exists_mk
    · simp_all [valueGroup₀Fun_zero]
    rw [valueGroup₀Fun_spec h, valueGroup₀Fun_spec h.symm]
  right_inv x := by
    obtain _ | ⟨r₁, s₁, hr₁, hs₁, rfl⟩ := x.zero_or_exists_mk
    · simp_all [valueGroup₀Fun_zero]
    rw [valueGroup₀Fun_spec h.symm, valueGroup₀Fun_spec h]
  map_le_map_iff' {x} {y} := by
    simp only [valueGroup₀Fun, ne_eq]
    split_ifs with hx0 hy0 hy0
    · simp [hx0, hy0]
    · simp [hx0]
    · simp [hx0, hy0]
    · generalize_proofs _ _ _ _ hx _ _ hy
      conv_rhs => rw [hx.choose_spec, hy.choose_spec]
      simp only [valueGroup.mk, WithZero.coe_le_coe, Subtype.mk_le_mk]
      nth_rw 2 [mul_comm]
      rw [le_mul_inv_iff_mul_le, mul_assoc, mul_comm, ← le_mul_inv_iff_mul_le, inv_inv]
      nth_rw 4 [mul_comm]
      conv_rhs =>
        rw [le_mul_inv_iff_mul_le, mul_assoc, mul_comm, ← le_mul_inv_iff_mul_le, inv_inv]
      generalize_proofs _ hx' hx20 hy' hy10 hx10 hy20
      rw [← Units.mk0_mul _ _ (mul_ne_zero hx10 hy20), ← Units.mk0_mul _ _ (mul_ne_zero hx20 hy10),
        ← Units.mk0_mul, ← Units.mk0_mul]
      · simp only [← Units.val_le_val]
        repeat rw [Units.val_mk0]
        simp only [MonoidWithZeroHom.coe_ofClass, ← map_mul w, ← h.le_iff_le]
        simp
      · simpa only [MonoidWithZeroHom.coe_ofClass, ← map_mul v, ne_eq, h.eq_zero, map_mul w]
          using mul_ne_zero hx10 hy20
      · simpa only [MonoidWithZeroHom.coe_ofClass, ← map_mul v, ne_eq, h.eq_zero, map_mul w]
          using mul_ne_zero hx20 hy10

@[simp]
/-
**Valuation.IsEquiv.orderMonoidIso_spec** 是 Mathlib 中的一个定理，位于命名空间 `Valuation.IsE
quiv`。
形式化陈述：orderMonoidIso_spec (h : v.IsEquiv w) (a : R) : h.orderMonoidIso (v.restri
ct a) = w.restrict a
参数：h : v.IsEquiv w；a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `Valuation.IsEquiv.restrict`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : Rin
g R] [inst_1 : LinearOrderedCommGroupWithZero Γ₀] (v : Valuation R Γ₀)   {Γ₀' : 
Type u_7} [inst_…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Valuation.restrict_eq_zero_iff`：restrict_eq_zero_iff {x : R} : v.restric
t x = 0 ↔ v x = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `MulEquivClass.toMonoidWithZeroHomClass`：∀ {F : Type u_1} {α : Type u_2} 
{β : Type u_3} [inst : EquivLike F α β] [inst_1 : MulZeroOneClass α]   [inst_2 :
 MulZeroOneClass β] [MulEqui…
· 使用定理 `OrderMonoidIso.instMulEquivClass`：∀ {α : Type u_2} {β : Type u_3} [inst 
: Preorder α] [inst_1 : Preorder β] [inst_2 : Mul α] [inst_3 : Mul β],   MulEqui
vClass (α ≃*o β) α β
· 使用定理 `Eq.comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Valuation.IsEquiv.eq_zero`：eq_zero (h : v₁.IsEquiv v₂) {r : R} : v₁ r = 
0 ↔ v₂ r = 0
· 使用引理 `Valuation.restrict_eq_mk`：restrict_eq_mk {x : R} (hx : v x != 0) : v.res
trict x = (valueGroup.mk (.ofClass v) 1 x (by simp) hx : ValueGroup₀ (.ofClass v
))
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Iff.ne`：∀ {α : Sort u_1} {β : Sort u_2} {a b : α} {c d : β}, (a = b ↔ c 
= d) → (a ≠ b ↔ c ≠ d)
· 使用引理 `Valuation.IsEquiv.ofClass_eq_zero`：ofClass_eq_zero (h : v₁.IsEquiv v₂) {
r : R} : (MonoidWithZeroHom.ofClass v₁) r = 0 ↔ (MonoidWithZeroHom.ofClass v₂) r
 = 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Valuation.IsEquiv.symm`：symm (h : v₁.IsEquiv v₂) : v₂.IsEquiv v₁
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Valuation.IsEquiv.valueGroup₀Fun_spec`：valueGroup₀Fun_spec (h : v.IsEqui
v w) {r s : R} (hr : (MonoidWithZeroHom.ofClass v) r != 0) (hs : (MonoidWithZero
Hom.ofClass v) s != 0) (hr'…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem orderMonoidIso_spec (h : v.IsEquiv w) (a : R) :
    h.orderMonoidIso (v.restrict a) = w.restrict a := by
  have h_res := h.restrict
  by_cases ha : v a = 0
  · rw [← restrict_eq_zero_iff] at ha
    rwa [ha, map_zero, Eq.comm, ← h_res.eq_zero]
  · rw [(v.restrict_eq_mk ha)]
    simp [orderMonoidIso, valueGroup₀Fun_spec h (hs := ha),
      w.restrict_eq_mk ((eq_zero h.symm).ne.mpr ha)]
/-
**Valuation.IsEquiv.orderMonoidIso_spec** 是 Mathlib 中的一个定理，位于命名空间 `Valuation.IsE
quiv`。
形式化陈述：orderMonoidIso_spec (h : v.IsEquiv w) (a : R) : h.orderMonoidIso (v.restri
ct a) = w.restrict a
参数：h : v.IsEquiv w；a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `Valuation.IsEquiv.restrict`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : Rin
g R] [inst_1 : LinearOrderedCommGroupWithZero Γ₀] (v : Valuation R Γ₀)   {Γ₀' : 
Type u_7} [inst_…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Valuation.restrict_eq_zero_iff`：restrict_eq_zero_iff {x : R} : v.restric
t x = 0 ↔ v x = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `MulEquivClass.toMonoidWithZeroHomClass`：∀ {F : Type u_1} {α : Type u_2} 
{β : Type u_3} [inst : EquivLike F α β] [inst_1 : MulZeroOneClass α]   [inst_2 :
 MulZeroOneClass β] [MulEqui…
· 使用定理 `OrderMonoidIso.instMulEquivClass`：∀ {α : Type u_2} {β : Type u_3} [inst 
: Preorder α] [inst_1 : Preorder β] [inst_2 : Mul α] [inst_3 : Mul β],   MulEqui
vClass (α ≃*o β) α β
· 使用定理 `Eq.comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Valuation.IsEquiv.eq_zero`：eq_zero (h : v₁.IsEquiv v₂) {r : R} : v₁ r = 
0 ↔ v₂ r = 0
· 使用引理 `Valuation.restrict_eq_mk`：restrict_eq_mk {x : R} (hx : v x != 0) : v.res
trict x = (valueGroup.mk (.ofClass v) 1 x (by simp) hx : ValueGroup₀ (.ofClass v
))
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Iff.ne`：∀ {α : Sort u_1} {β : Sort u_2} {a b : α} {c d : β}, (a = b ↔ c 
= d) → (a ≠ b ↔ c ≠ d)
· 使用引理 `Valuation.IsEquiv.ofClass_eq_zero`：ofClass_eq_zero (h : v₁.IsEquiv v₂) {
r : R} : (MonoidWithZeroHom.ofClass v₁) r = 0 ↔ (MonoidWithZeroHom.ofClass v₂) r
 = 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Valuation.IsEquiv.symm`：symm (h : v₁.IsEquiv v₂) : v₂.IsEquiv v₁
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Valuation.IsEquiv.valueGroup₀Fun_spec`：valueGroup₀Fun_spec (h : v.IsEqui
v w) {r s : R} (hr : (MonoidWithZeroHom.ofClass v) r != 0) (hs : (MonoidWithZero
Hom.ofClass v) s != 0) (hr'…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma orderMonoidIso_spec₀ (h : v.IsEquiv w) (a : R) :
    h.orderMonoidIso (restrict₀ (.ofClass v) a) = restrict₀ (.ofClass w) a :=
  orderMonoidIso_spec h a
/-
**Valuation.IsEquiv.orderMonoidIso_symm** 是 Mathlib 中的一个定理，位于命名空间 `Valuation.IsE
quiv`。
形式化陈述：orderMonoidIso_symm (h : v.IsEquiv w) (h' : w.IsEquiv v) : h.orderMonoidIs
o.symm = h'.orderMonoidIso
参数：h : v.IsEquiv w；h' : w.IsEquiv v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
-/
theorem orderMonoidIso_symm (h : v.IsEquiv w) (h' : w.IsEquiv v) :
    h.orderMonoidIso.symm = h'.orderMonoidIso := by
  rfl

@[simp]
/-
**Valuation.IsEquiv.orderMonoidIso_eq_refl** 是 Mathlib 中的一个定理，位于命名空间 `Valuation.
IsEquiv`。
形式化陈述：orderMonoidIso_eq_refl (h : v.IsEquiv v) : h.orderMonoidIso = .refl _
参数：h : v.IsEquiv v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderMonoidIso.ext`：ext (h : forall a, f a = g a) : f = g
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `MonoidWithZeroHom.ValueGroup₀.zero_or_exists_mk`：zero_or_exists_mk (x : 
ValueGroup₀ f) : x = 0 ∨ exists r s hr hs, x = valueGroup.mk f r s hr hs
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `MulEquivClass.toMonoidWithZeroHomClass`：∀ {F : Type u_1} {α : Type u_2} 
{β : Type u_3} [inst : EquivLike F α β] [inst_1 : MulZeroOneClass α]   [inst_2 :
 MulZeroOneClass β] [MulEqui…
· 使用定理 `OrderMonoidIso.instMulEquivClass`：∀ {α : Type u_2} {β : Type u_3} [inst 
: Preorder α] [inst_1 : Preorder β] [inst_2 : Mul α] [inst_3 : Mul β],   MulEqui
vClass (α ≃*o β) α β
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Iff.ne`：∀ {α : Sort u_1} {β : Sort u_2} {a b : α} {c d : β}, (a = b ↔ c 
= d) → (a ≠ b ↔ c ≠ d)
· 使用引理 `Valuation.IsEquiv.ofClass_eq_zero`：ofClass_eq_zero (h : v₁.IsEquiv v₂) {
r : R} : (MonoidWithZeroHom.ofClass v₁) r = 0 ↔ (MonoidWithZeroHom.ofClass v₂) r
 = 0
· 使用定理 `Valuation.IsEquiv.valueGroup₀Fun_spec`：valueGroup₀Fun_spec (h : v.IsEqui
v w) {r s : R} (hr : (MonoidWithZeroHom.ofClass v) r != 0) (hs : (MonoidWithZero
Hom.ofClass v) s != 0) (hr'…
-/
theorem orderMonoidIso_eq_refl (h : v.IsEquiv v) :
    h.orderMonoidIso = .refl _ := by
  ext x
  obtain (rfl | ⟨x, y, _, _, rfl⟩) := x.zero_or_exists_mk
  · simp
  · simp [orderMonoidIso, valueGroup₀Fun_spec h]

@[simp]
/-
**Valuation.IsEquiv.orderMonoidIso_trans** 是 Mathlib 中的一个定理，位于命名空间 `Valuation.Is
Equiv`。
形式化陈述：orderMonoidIso_trans (h : v.IsEquiv w) (h' : w.IsEquiv u) : h.orderMonoidI
so.trans h'.orderMonoidIso = (h.trans h').orderMonoidIso
参数：h : v.IsEquiv w；h' : w.IsEquiv u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderMonoidIso.ext`：ext (h : forall a, f a = g a) : f = g
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `Valuation.IsEquiv.trans`：trans (h₁₂ : v₁.IsEquiv v₂) (h₂₃ : v₂.IsEquiv v
₃) : v₁.IsEquiv v₃
· 使用定理 `MonoidWithZeroHom.ValueGroup₀.zero_or_exists_mk`：zero_or_exists_mk (x : 
ValueGroup₀ f) : x = 0 ∨ exists r s hr hs, x = valueGroup.mk f r s hr hs
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `MulEquivClass.toMonoidWithZeroHomClass`：∀ {F : Type u_1} {α : Type u_2} 
{β : Type u_3} [inst : EquivLike F α β] [inst_1 : MulZeroOneClass α]   [inst_2 :
 MulZeroOneClass β] [MulEqui…
· 使用定理 `OrderMonoidIso.instMulEquivClass`：∀ {α : Type u_2} {β : Type u_3} [inst 
: Preorder α] [inst_1 : Preorder β] [inst_2 : Mul α] [inst_3 : Mul β],   MulEqui
vClass (α ≃*o β) α β
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Iff.ne`：∀ {α : Sort u_1} {β : Sort u_2} {a b : α} {c d : β}, (a = b ↔ c 
= d) → (a ≠ b ↔ c ≠ d)
· 使用引理 `Valuation.IsEquiv.ofClass_eq_zero`：ofClass_eq_zero (h : v₁.IsEquiv v₂) {
r : R} : (MonoidWithZeroHom.ofClass v₁) r = 0 ↔ (MonoidWithZeroHom.ofClass v₂) r
 = 0
· 使用定理 `Valuation.IsEquiv.valueGroup₀Fun_spec`：valueGroup₀Fun_spec (h : v.IsEqui
v w) {r s : R} (hr : (MonoidWithZeroHom.ofClass v) r != 0) (hs : (MonoidWithZero
Hom.ofClass v) s != 0) (hr'…
-/
theorem orderMonoidIso_trans (h : v.IsEquiv w) (h' : w.IsEquiv u) :
    h.orderMonoidIso.trans h'.orderMonoidIso = (h.trans h').orderMonoidIso := by
  ext x
  obtain (rfl | ⟨x, y, _, _, rfl⟩) := x.zero_or_exists_mk
  · simp
  · simp [orderMonoidIso, valueGroup₀Fun_spec h, valueGroup₀Fun_spec h',
      valueGroup₀Fun_spec (trans h h')]

end IsEquiv

end Ring

section DivisionRing

variable {v : Valuation K Γ₀} {v' : Valuation K Γ'₀}

/-
**Valuation.isEquiv_of_val_le_one** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`。
形式化陈述：isEquiv_of_val_le_one (h : forall x, v x <= 1 ↔ v' x <= 1) : v.IsEquiv v'
参数：h : forall x, v x <= 1 ↔ v' x <= 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `div_le_one₀`：div_le_one₀ (hb : 0 < b) : a / b <= 1 ↔ a <= b
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `LinearOrderedCommMonoidWithZero.toMulPosStrictMono`：∀ {α : Type u_1} [in
st : LinearOrderedCommMonoidWithZero α], MulPosStrictMono α
· 使用定理 `zero_lt_iff`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_1 : 
Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `Valuation.ne_zero_iff`：ne_zero_iff [Nontrivial Γ₀] (v : Valuation K Γ₀) 
{x : K} : v x != 0 ↔ x != 0
· 使用定理 `Valuation.map_div`：map_div {R : Type*} [DivisionRing R] (v : Valuation R
 Γ₀) : forall x y, v (x / y) = v x / v y
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isEquiv_of_val_le_one (h : ∀ x, v x ≤ 1 ↔ v' x ≤ 1) : v.IsEquiv v' := by
  intro x y
  obtain rfl | hy := eq_or_ne y 0
  · simp
  · rw [← div_le_one₀, ← v.map_div, h, v'.map_div, div_le_one₀] <;>
      rwa [zero_lt_iff, ne_zero_iff]
/-
**Valuation.isEquiv_iff_val_le_one** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`。
形式化陈述：isEquiv_iff_val_le_one : v.IsEquiv v' ↔ forall {x}, v x <= 1 ↔ v' x <= 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Valuation.IsEquiv.le_one_iff_le_one`：le_one_iff_le_one (h : v₁.IsEquiv v
₂) {x : R} : v₁ x <= 1 ↔ v₂ x <= 1
· 使用定理 `Valuation.isEquiv_of_val_le_one`：isEquiv_of_val_le_one (h : forall x, v 
x <= 1 ↔ v' x <= 1) : v.IsEquiv v'
-/
theorem isEquiv_iff_val_le_one : v.IsEquiv v' ↔ ∀ {x}, v x ≤ 1 ↔ v' x ≤ 1 :=
  ⟨IsEquiv.le_one_iff_le_one, isEquiv_of_val_le_one⟩
/-
**Valuation.isEquiv_iff_val_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`。
形式化陈述：isEquiv_iff_val_eq_one : v.IsEquiv v' ↔ forall {x}, v x = 1 ↔ v' x = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Valuation.IsEquiv.eq_one_iff_eq_one`：eq_one_iff_eq_one (h : v₁.IsEquiv v
₂) {x : R} : v₁ x = 1 ↔ v₂ x = 1
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Valuation.isEquiv_of_val_le_one`：isEquiv_of_val_le_one (h : forall x, v 
x <= 1 ↔ v' x <= 1) : v.IsEquiv v'
· 使用引理 `lt_or_eq_of_le`：lt_or_eq_of_le : a <= b -> a < b ∨ a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Valuation.map_one`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : Ring R] [ins
t_1 : LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation R Γ₀),   v 1 = 1
· 使用定理 `Valuation.map_add_eq_of_lt_left`：map_add_eq_of_lt_left (h : v y < v x) :
 v (x + y) = v x
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `neg_add_cancel_left`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), -a 
+ (a + b) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Valuation.map_add`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : Ring R] [ins
t_1 : LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation R Γ₀)   (x y : R), v (x
 + y) ≤…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Valuation.map_neg`：map_neg (x : R) : v (-x) = v x
· 使用定理 `max_self`：∀ {α : Type u_1} [inst : LinearOrder α] (a : α), max a a = a
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
-/
theorem isEquiv_iff_val_eq_one : v.IsEquiv v' ↔ ∀ {x}, v x = 1 ↔ v' x = 1 := by
  constructor
  · intro h x
    rw [h.eq_one_iff_eq_one]
  · intro h
    apply isEquiv_of_val_le_one
    intro x
    constructor
    · intro hx
      rcases lt_or_eq_of_le hx with hx' | hx'
      · have : v (1 + x) = 1 := by
          rw [← v.map_one]
          apply map_add_eq_of_lt_left
          simpa
        rw [h] at this
        rw [show x = -1 + (1 + x) by simp]
        refine le_trans (v'.map_add _ _) ?_
        simp [this]
      · rw [h] at hx'
        exact le_of_eq hx'
    · intro hx
      rcases lt_or_eq_of_le hx with hx' | hx'
      · have : v' (1 + x) = 1 := by
          rw [← v'.map_one]
          apply map_add_eq_of_lt_left
          simpa
        rw [← h] at this
        rw [show x = -1 + (1 + x) by simp]
        refine le_trans (v.map_add _ _) ?_
        simp [this]
      · rw [← h] at hx'
        exact le_of_eq hx'
/-
**Valuation.isEquiv_iff_val_lt_one** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`。
形式化陈述：isEquiv_iff_val_lt_one : v.IsEquiv v' ↔ forall {x}, v x < 1 ↔ v' x < 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Valuation.IsEquiv.lt_one_iff_lt_one`：lt_one_iff_lt_one (h : v₁.IsEquiv v
₂) {x : R} : v₁ x < 1 ↔ v₂ x < 1
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Valuation.isEquiv_iff_val_eq_one`：isEquiv_iff_val_eq_one : v.IsEquiv v' 
↔ forall {x}, v x = 1 ↔ v' x = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Valuation.zero_iff`：zero_iff [Nontrivial Γ₀] (v : Valuation K Γ₀) {x : K
} : v x = 0 ↔ x = 0
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `ne_iff_lt_or_gt`：ne_iff_lt_or_gt : a != b ↔ a < b ∨ b < a
· 使用定理 `Eq.not_lt`：∀ {α : Type u_2} [inst : Preorder α] {a b : α}, a = b → ¬a < 
b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_inv₀`：map_inv₀ : f a⁻¹ = (f a)⁻¹
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `inv_eq_iff_eq_inv`：inv_eq_iff_eq_inv : a⁻¹ = b ↔ a = b⁻¹
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `Valuation.one_lt_val_iff`：one_lt_val_iff (v : Valuation K Γ₀) {x : K} (h
 : x != 0) : 1 < v x ↔ v x⁻¹ < 1
-/
theorem isEquiv_iff_val_lt_one : v.IsEquiv v' ↔ ∀ {x}, v x < 1 ↔ v' x < 1 := by
  constructor
  · intro h x
    rw [h.lt_one_iff_lt_one]
  · rw [isEquiv_iff_val_eq_one]
    intro h x
    by_cases hx : x = 0
    · simp only [(zero_iff _).2 hx, zero_ne_one]
    constructor
    · intro hh
      by_contra h_1
      cases ne_iff_lt_or_gt.1 h_1 with
      | inl h_2 => simpa [hh, lt_self_iff_false] using h.2 h_2
      | inr h_2 =>
          rw [← inv_one, ← inv_eq_iff_eq_inv, ← map_inv₀] at hh
          exact hh.not_lt (h.2 ((one_lt_val_iff v' hx).1 h_2))
    · intro hh
      by_contra h_1
      cases ne_iff_lt_or_gt.1 h_1 with
      | inl h_2 => simpa [hh, lt_self_iff_false] using h.1 h_2
      | inr h_2 =>
        rw [← inv_one, ← inv_eq_iff_eq_inv, ← map_inv₀] at hh
        exact hh.not_lt (h.1 ((one_lt_val_iff v hx).1 h_2))
/-
**Valuation.isEquiv_iff_val_sub_one_lt_one** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`
。
形式化陈述：isEquiv_iff_val_sub_one_lt_one : v.IsEquiv v' ↔ forall {x}, v (x - 1) < 1 
↔ v' (x - 1) < 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Valuation.isEquiv_iff_val_lt_one`：isEquiv_iff_val_lt_one : v.IsEquiv v' 
↔ forall {x}, v x < 1 ↔ v' x < 1
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
-/
theorem isEquiv_iff_val_sub_one_lt_one :
    v.IsEquiv v' ↔ ∀ {x}, v (x - 1) < 1 ↔ v' (x - 1) < 1 := by
  rw [isEquiv_iff_val_lt_one]
  exact (Equiv.subRight 1).surjective.forall

alias ⟨IsEquiv.val_sub_one_lt_one_iff, _⟩ := isEquiv_iff_val_sub_one_lt_one

variable (v v') in
/-
**Valuation.isEquiv_tfae** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`。
形式化陈述：isEquiv_tfae : [ v.IsEquiv v', forall {x y}, v x < v y ↔ v' x < v' y, fora
ll {x}, v x <= 1 ↔ v' x <= 1, forall {x}, v x = 1 ↔ v' x = 1, forall {x}, v x < 
1 ↔ v' x < 1, forall {x}, v (x - 1) < 1 ↔ v' (x - 1) < 1 ].TFAE
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Valuation.isEquiv_iff_val_lt_val`：isEquiv_iff_val_lt_val : v.IsEquiv v' 
↔ forall {x y : R}, v x < v y ↔ v' x < v' y
· 使用定理 `Valuation.isEquiv_iff_val_le_one`：isEquiv_iff_val_le_one : v.IsEquiv v' 
↔ forall {x}, v x <= 1 ↔ v' x <= 1
· 使用定理 `Valuation.isEquiv_iff_val_eq_one`：isEquiv_iff_val_eq_one : v.IsEquiv v' 
↔ forall {x}, v x = 1 ↔ v' x = 1
· 使用定理 `Valuation.isEquiv_iff_val_lt_one`：isEquiv_iff_val_lt_one : v.IsEquiv v' 
↔ forall {x}, v x < 1 ↔ v' x < 1
· 使用定理 `Valuation.isEquiv_iff_val_sub_one_lt_one`：isEquiv_iff_val_sub_one_lt_one
 : v.IsEquiv v' ↔ forall {x}, v (x - 1) < 1 ↔ v' (x - 1) < 1
· 使用定理 `List.tfae_of_cycle`：tfae_of_cycle {a b} {l : List Prop} (h_chain : List.
IsChain (· -> ·) (a :: b :: l)) (h_last : getLastD l b -> a) : TFAE (a :: b :: l
)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem isEquiv_tfae :
    [ v.IsEquiv v',
      ∀ {x y}, v x < v y ↔ v' x < v' y,
      ∀ {x}, v x ≤ 1 ↔ v' x ≤ 1,
      ∀ {x}, v x = 1 ↔ v' x = 1,
      ∀ {x}, v x < 1 ↔ v' x < 1,
      ∀ {x}, v (x - 1) < 1 ↔ v' (x - 1) < 1 ].TFAE := by
  tfae_have 1 ↔ 2 := isEquiv_iff_val_lt_val
  tfae_have 1 ↔ 3 := isEquiv_iff_val_le_one
  tfae_have 1 ↔ 4 := isEquiv_iff_val_eq_one
  tfae_have 1 ↔ 5 := isEquiv_iff_val_lt_one
  tfae_have 1 ↔ 6 := isEquiv_iff_val_sub_one_lt_one
  tfae_finish

end DivisionRing

end LinearOrderedCommGroupWithZero

section Supp

variable [CommRing R] [LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation R Γ₀)

/-- The support of a valuation `v : R → Γ₀` is the ideal of `R` where `v` vanishes. -/
/-
**Valuation.supp** 是 Mathlib 中的一个定义，位于命名空间 `Valuation`。
形式化陈述：supp : Ideal R where carrier
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The support of a valuation `v : R → Γ₀` is the ideal of `R` where `v` vanishes.
-/
def supp : Ideal R where
  carrier := { x | v x = 0 }
  zero_mem' := map_zero v
  add_mem' {x y} hx hy := le_zero_iff.mp <|
    calc
      v (x + y) ≤ max (v x) (v y) := v.map_add x y
      _ ≤ 0 := max_le (le_zero_iff.mpr hx) (le_zero_iff.mpr hy)
  smul_mem' c x hx :=
    calc
      v (c * x) = v c * v x := map_mul v c x
      _ = v c * 0 := congr_arg _ hx
      _ = 0 := mul_zero _

@[simp]
/-
**Valuation.mem_supp_iff** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`。
形式化陈述：mem_supp_iff (x : R) : x in supp v ↔ v x = 0
参数：x : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_supp_iff (x : R) : x ∈ supp v ↔ v x = 0 :=
  Iff.rfl

/-- The support of a valuation is a prime ideal. -/
/-
**Valuation.** 是 Mathlib 中的一个实例，位于命名空间 `Valuation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The support of a valuation is a prime ideal.
-/
instance [Nontrivial Γ₀] [NoZeroDivisors Γ₀] : Ideal.IsPrime (supp v) :=
  ⟨fun h =>
    one_ne_zero (α := Γ₀) <|
      calc
        1 = v 1 := v.map_one.symm
        _ = 0 := by rw [← mem_supp_iff, h]; exact Submodule.mem_top,
   fun {x y} hxy => by
    simp only [mem_supp_iff] at hxy ⊢
    rw [v.map_mul x y] at hxy
    exact eq_zero_or_eq_zero_of_mul_eq_zero hxy⟩
/-
**Valuation.map_add_supp** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`。
形式化陈述：map_add_supp (a : R) {s : R} (h : s in supp v) : v (a + s) = v a
参数：a : R；h : s in supp v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Valuation.map_add`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : Ring R] [ins
t_1 : LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation R Γ₀)   (x y : R), v (x
 + y) ≤…
· 使用定理 `max_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, a ≤ c → b ≤
 c → max a b ≤ c
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `add_neg_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b + -b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.neg_mem_iff`：∀ {α : Type u} [inst : Ring α] (I : Ideal α) {a : α},
 -a ∈ I ↔ a ∈ I
-/
theorem map_add_supp (a : R) {s : R} (h : s ∈ supp v) : v (a + s) = v a := by
  have aux : ∀ a s, v s = 0 → v (a + s) ≤ v a := by
    intro a' s' h'
    refine le_trans (v.map_add a' s') (max_le le_rfl ?_)
    simp [h']
  apply le_antisymm (aux a s h)
  calc
    v a = v (a + s + -s) := by simp
    _ ≤ v (a + s) := aux (a + s) (-s) (by rwa [← Ideal.neg_mem_iff] at h)
/-
**Valuation.comap_supp** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`。
形式化陈述：comap_supp {S : Type*} [CommRing S] (f : S ->+* R) : supp (v.comap f) = Id
eal.comap f v.supp
参数：f : S ->+* R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.ext`：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Valuation.mem_supp_iff`：mem_supp_iff (x : R) : x in supp v ↔ v x = 0
· 使用定理 `Ideal.mem_comap`：mem_comap [RingHomClass F R S] {x} : x in comap f K ↔ f
 x in K
· 使用定理 `Valuation.comap_apply`：comap_apply {S : Type*} [Ring S] (f : S ->+* R) (
v : Valuation R Γ₀) (s : S) : v.comap f s = v (f s)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem comap_supp {S : Type*} [CommRing S] (f : S →+* R) :
    supp (v.comap f) = Ideal.comap f v.supp :=
  Ideal.ext fun x => by rw [mem_supp_iff, Ideal.mem_comap, mem_supp_iff, comap_apply]

end Supp

end Valuation

section AddMonoid

variable (R) [Ring R] (Γ₀ : Type*) [LinearOrderedAddCommMonoidWithTop Γ₀]

/-- The type of `Γ₀`-valued additive valuations on `R`. -/
/-
**AddValuation** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：AddValuation
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of `Γ₀`-valued additive valuations on `R`.
-/
def AddValuation :=
  Valuation R (Multiplicative Γ₀ᵒᵈ)

end AddMonoid

namespace AddValuation

variable {Γ₀ : Type*} {Γ'₀ : Type*}

section Basic

section Monoid
variable [Ring R] [LinearOrderedAddCommMonoidWithTop Γ₀] [LinearOrderedAddCommMonoidWithTop Γ'₀]
  (v : AddValuation R Γ₀)

/-
**AddValuation.** 是 Mathlib 中的一个实例，位于命名空间 `AddValuation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FunLike (AddValuation R Γ₀) R Γ₀ :=
  inferInstanceAs <| FunLike (Valuation R <| Multiplicative Γ₀ᵒᵈ) R <| Multiplicative Γ₀ᵒᵈ

section

variable (f : R → Γ₀) (h0 : f 0 = ⊤) (h1 : f 1 = 0)
variable (hadd : ∀ x y, min (f x) (f y) ≤ f (x + y)) (hmul : ∀ x y, f (x * y) = f x + f y)

/-- An alternate constructor of `AddValuation`, that doesn't reference `Multiplicative Γ₀ᵒᵈ` -/
/-
**AddValuation.of** 是 Mathlib 中的一个定义，位于命名空间 `AddValuation`。
形式化陈述：of : AddValuation R Γ₀ where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An alternate constructor of `AddValuation`, that doesn't reference `Multiplicati
ve Γ₀ᵒᵈ`
-/
def of : AddValuation R Γ₀ where
  toFun := f
  map_one' := h1
  map_zero' := h0
  map_add_le_max' := hadd
  map_mul' := hmul

variable {h0} {h1} {hadd} {hmul} {r : R}

@[simp]
/-
**AddValuation.of_apply** 是 Mathlib 中的一个定理，位于命名空间 `AddValuation`。
形式化陈述：of_apply : (of f h0 h1 hadd hmul) r = f r
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem of_apply : (of f h0 h1 hadd hmul) r = f r := rfl

/-- The `Valuation` associated to an `AddValuation` (useful if the latter is constructed using
`AddValuation.of`). -/
/-
**AddValuation.toValuation** 是 Mathlib 中的一个定义，位于命名空间 `AddValuation`。
形式化陈述：toValuation : AddValuation R Γ₀ ≃ Valuation R (Multiplicative Γ₀ᵒᵈ)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
The `Valuation` associated to an `AddValuation` (useful if the latter is constru
cted using
`AddValuation.of`).
-/
def toValuation : AddValuation R Γ₀ ≃ Valuation R (Multiplicative Γ₀ᵒᵈ) :=
  Equiv.refl _

/-- The `AddValuation` associated to a `Valuation`.
-/
/-
**AddValuation.ofValuation** 是 Mathlib 中的一个定义，位于命名空间 `AddValuation`。
形式化陈述：ofValuation : Valuation R (Multiplicative Γ₀ᵒᵈ) ≃ AddValuation R Γ₀
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
The `AddValuation` associated to a `Valuation`.
-/
def ofValuation : Valuation R (Multiplicative Γ₀ᵒᵈ) ≃ AddValuation R Γ₀ :=
  Equiv.refl _

@[simp]
/-
**AddValuation.ofValuation_symm_eq** 是 Mathlib 中的一个引理，位于命名空间 `AddValuation`。
形式化陈述：ofValuation_symm_eq : ofValuation.symm = toValuation (R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma ofValuation_symm_eq : ofValuation.symm = toValuation (R := R) (Γ₀ := Γ₀) := rfl

@[simp]
/-
**AddValuation.toValuation_symm_eq** 是 Mathlib 中的一个引理，位于命名空间 `AddValuation`。
形式化陈述：toValuation_symm_eq : toValuation.symm = ofValuation (R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma toValuation_symm_eq : toValuation.symm = ofValuation (R := R) (Γ₀ := Γ₀) := rfl

@[simp]
/-
**AddValuation.ofValuation_toValuation** 是 Mathlib 中的一个引理，位于命名空间 `AddValuation`。
形式化陈述：ofValuation_toValuation : ofValuation (toValuation v) = v
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofValuation_toValuation : ofValuation (toValuation v) = v := rfl

@[simp]
/-
**AddValuation.toValuation_ofValuation** 是 Mathlib 中的一个引理，位于命名空间 `AddValuation`。
形式化陈述：toValuation_ofValuation (v : Valuation R (Multiplicative Γ₀ᵒᵈ)) : toValuat
ion (ofValuation v) = v
参数：v : Valuation R (Multiplicative Γ₀ᵒᵈ)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toValuation_ofValuation (v : Valuation R (Multiplicative Γ₀ᵒᵈ)) :
    toValuation (ofValuation v) = v := rfl

@[simp]
/-
**AddValuation.toValuation_apply** 是 Mathlib 中的一个定理，位于命名空间 `AddValuation`。
形式化陈述：toValuation_apply (r : R) : toValuation v r = Multiplicative.ofAdd (OrderD
ual.toDual (v r))
参数：r : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toValuation_apply (r : R) :
    toValuation v r = Multiplicative.ofAdd (OrderDual.toDual (v r)) :=
  rfl

@[simp]
/-
**AddValuation.ofValuation_apply** 是 Mathlib 中的一个定理，位于命名空间 `AddValuation`。
形式化陈述：ofValuation_apply (v : Valuation R (Multiplicative Γ₀ᵒᵈ)) (r : R) : ofValu
ation v r = OrderDual.ofDual (Multiplicative.toAdd (v r))
参数：v : Valuation R (Multiplicative Γ₀ᵒᵈ)；r : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofValuation_apply (v : Valuation R (Multiplicative Γ₀ᵒᵈ)) (r : R) :
    ofValuation v r = OrderDual.ofDual (Multiplicative.toAdd (v r)) :=
  rfl

end

@[simp]
/-
**AddValuation.map_zero** 是 Mathlib 中的一个定理，位于命名空间 `Padic`。
形式化陈述：AddValuation.map_zero : addValuationDef (0 : Rat_[p]) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Valuation.map_zero`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : Ring R] [in
st_1 : LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation R Γ₀),   v 0 = 0
-/
theorem map_zero : v 0 = (⊤ : Γ₀) :=
  Valuation.map_zero v

@[simp]
/-
**AddValuation.map_one** 是 Mathlib 中的一个定理，位于命名空间 `Padic`。
形式化陈述：AddValuation.map_one : addValuationDef (1 : Rat_[p]) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Valuation.map_one`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : Ring R] [ins
t_1 : LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation R Γ₀),   v 1 = 1
-/
theorem map_one : v 1 = (0 : Γ₀) :=
  Valuation.map_one v

@[simp]
/-
**AddValuation.map_mul** 是 Mathlib 中的一个定理，位于命名空间 `Padic`。
形式化陈述：AddValuation.map_mul (x y : Rat_[p]) : addValuationDef (x * y : Rat_[p]) =
 addValuationDef x + addValuationDef y
参数：x y : Rat_[p]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Valuation.map_mul`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : Ring R] [ins
t_1 : LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation R Γ₀)   (x y : R), v (x
 * y) =…
-/
theorem map_mul : ∀ (x y : R), v (x * y) = v x + v y :=
  Valuation.map_mul v

-- `simp`-normal form is `map_add'`
/-
**AddValuation.map_add** 是 Mathlib 中的一个定理，位于命名空间 `Padic`。
形式化陈述：AddValuation.map_add (x y : Rat_[p]) : min (addValuationDef x) (addValuati
onDef y) <= addValuationDef (x + y : Rat_[p])
参数：x y : Rat_[p]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Valuation.map_add`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : Ring R] [ins
t_1 : LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation R Γ₀)   (x y : R), v (x
 + y) ≤…
-/
theorem map_add : ∀ (x y : R), min (v x) (v y) ≤ v (x + y) :=
  Valuation.map_add v

@[simp]
/-
**AddValuation.map_add'** 是 Mathlib 中的一个定理，位于命名空间 `AddValuation`。
形式化陈述：map_add' : forall (x y : R), v x <= v (x + y) ∨ v y <= v (x + y)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `min_le_iff`：∀ {α : Type u} [inst : LinearOrder α] {a b c : α}, min b c ≤
 a ↔ b ≤ a ∨ c ≤ a
· 使用定理 `AddValuation.map_add`：AddValuation.map_add (x y : Rat_[p]) : min (addVal
uationDef x) (addValuationDef y) <= addValuationDef (x + y : Rat_[p])
-/
theorem map_add' : ∀ (x y : R), v x ≤ v (x + y) ∨ v y ≤ v (x + y) := by
  intro x y
  rw [← min_le_iff]
  apply map_add
/-
**AddValuation.map_le_add** 是 Mathlib 中的一个定理，位于命名空间 `AddValuation`。
形式化陈述：map_le_add {x y : R} {g : Γ₀} (hx : g <= v x) (hy : g <= v y) : g <= v (x 
+ y)
参数：hx : g <= v x；hy : g <= v y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Valuation.map_add_le`：map_add_le {x y g} (hx : v x <= g) (hy : v y <= g)
 : v (x + y) <= g
-/
theorem map_le_add {x y : R} {g : Γ₀} (hx : g ≤ v x) (hy : g ≤ v y) : g ≤ v (x + y) :=
  Valuation.map_add_le v hx hy
/-
**AddValuation.map_lt_add** 是 Mathlib 中的一个定理，位于命名空间 `AddValuation`。
形式化陈述：map_lt_add {x y : R} {g : Γ₀} (hx : g < v x) (hy : g < v y) : g < v (x + y
)
参数：hx : g < v x；hy : g < v y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Valuation.map_add_lt`：map_add_lt {x y g} (hx : v x < g) (hy : v y < g) :
 v (x + y) < g
-/
theorem map_lt_add {x y : R} {g : Γ₀} (hx : g < v x) (hy : g < v y) : g < v (x + y) :=
  Valuation.map_add_lt v hx hy
/-
**AddValuation.map_le_sum** 是 Mathlib 中的一个定理，位于命名空间 `AddValuation`。
形式化陈述：map_le_sum {ι : Type*} {s : Finset ι} {f : ι -> R} {g : Γ₀} (hf : forall i
 in s, g <= v (f i)) : g <= v (∑ i in s, f i)
参数：hf : forall i in s, g <= v (f i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Valuation.map_sum_le`：map_sum_le {ι : Type*} {s : Finset ι} {f : ι -> R}
 {g : Γ₀} (hf : forall i in s, v (f i) <= g) : v (∑ i in s, f i) <= g
-/
theorem map_le_sum {ι : Type*} {s : Finset ι} {f : ι → R} {g : Γ₀} (hf : ∀ i ∈ s, g ≤ v (f i)) :
    g ≤ v (∑ i ∈ s, f i) :=
  v.map_sum_le hf
/-
**AddValuation.map_lt_sum** 是 Mathlib 中的一个定理，位于命名空间 `AddValuation`。
形式化陈述：map_lt_sum {ι : Type*} {s : Finset ι} {f : ι -> R} {g : Γ₀} (hg : g != ⊤) 
(hf : forall i in s, g < v (f i)) : g < v (∑ i in s, f i)
参数：hg : g != ⊤；hf : forall i in s, g < v (f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Valuation.map_sum_lt`：map_sum_lt {ι : Type*} {s : Finset ι} {f : ι -> R}
 {g : Γ₀} (hg : g != 0) (hf : forall i in s, v (f i) < g) : v (∑ i in s, f i) < 
g
-/
theorem map_lt_sum {ι : Type*} {s : Finset ι} {f : ι → R} {g : Γ₀} (hg : g ≠ ⊤)
    (hf : ∀ i ∈ s, g < v (f i)) : g < v (∑ i ∈ s, f i) :=
  v.map_sum_lt hg hf
/-
**AddValuation.map_lt_sum'** 是 Mathlib 中的一个定理，位于命名空间 `AddValuation`。
形式化陈述：map_lt_sum' {ι : Type*} {s : Finset ι} {f : ι -> R} {g : Γ₀} (hg : g < ⊤) 
(hf : forall i in s, g < v (f i)) : g < v (∑ i in s, f i)
参数：hg : g < ⊤；hf : forall i in s, g < v (f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Valuation.map_sum_lt'`：map_sum_lt' {ι : Type*} {s : Finset ι} {f : ι -> 
R} {g : Γ₀} (hg : 0 < g) (hf : forall i in s, v (f i) < g) : v (∑ i in s, f i) <
 g
-/
theorem map_lt_sum' {ι : Type*} {s : Finset ι} {f : ι → R} {g : Γ₀} (hg : g < ⊤)
    (hf : ∀ i ∈ s, g < v (f i)) : g < v (∑ i ∈ s, f i) :=
  v.map_sum_lt' hg hf

@[simp]
/-
**AddValuation.map_pow** 是 Mathlib 中的一个定理，位于命名空间 `AddValuation`。
形式化陈述：map_pow : forall (x : R) (n : Nat), v (x ^ n) = n • (v x)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Valuation.map_pow`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : Ring R] [ins
t_1 : LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation R Γ₀)   (x : R) (n : ℕ)
, v (x …
-/
theorem map_pow : ∀ (x : R) (n : ℕ), v (x ^ n) = n • (v x) :=
  Valuation.map_pow v

@[ext]
/-
**AddValuation.ext** 是 Mathlib 中的一个定理，位于命名空间 `AddValuation`。
形式化陈述：ext {v₁ v₂ : AddValuation R Γ₀} (h : forall r, v₁ r = v₂ r) : v₁ = v₂
参数：h : forall r, v₁ r = v₂ r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Valuation.ext`：ext {v₁ v₂ : Valuation R Γ₀} (h : forall r, v₁ r = v₂ r) 
: v₁ = v₂
-/
theorem ext {v₁ v₂ : AddValuation R Γ₀} (h : ∀ r, v₁ r = v₂ r) : v₁ = v₂ :=
  Valuation.ext h

-- The following definition is not an instance, because we have more than one `v` on a given `R`.
-- In addition, type class inference would not be able to infer `v`.
/-- A valuation gives a preorder on the underlying ring. -/
@[instance_reducible]
/-
**AddValuation.toPreorder** 是 Mathlib 中的一个定义，位于命名空间 `AddValuation`。
形式化陈述：toPreorder : Preorder R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A valuation gives a preorder on the underlying ring.
-/
def toPreorder : Preorder R :=
  Preorder.lift v

/-- If `v` is an additive valuation on a division ring then `v(x) = ⊤` iff `x = 0`. -/
@[simp]
/-
**AddValuation.top_iff** 是 Mathlib 中的一个定理，位于命名空间 `AddValuation`。
形式化陈述：top_iff [Nontrivial Γ₀] (v : AddValuation K Γ₀) {x : K} : v x = (⊤ : Γ₀) ↔
 x = 0
参数：v : AddValuation K Γ₀。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Valuation.zero_iff`：zero_iff [Nontrivial Γ₀] (v : Valuation K Γ₀) {x : K
} : v x = 0 ↔ x = 0
· 使用定理 `OrderDual.instNontrivial`：∀ {α : Type u_1} [h : Nontrivial α], Nontrivia
l αᵒᵈ

--- 原说明 ---
If `v` is an additive valuation on a division ring then `v(x) = ⊤` iff `x = 0`.
-/
theorem top_iff [Nontrivial Γ₀] (v : AddValuation K Γ₀) {x : K} : v x = (⊤ : Γ₀) ↔ x = 0 :=
  v.zero_iff
/-
**AddValuation.ne_top_iff** 是 Mathlib 中的一个定理，位于命名空间 `AddValuation`。
形式化陈述：ne_top_iff [Nontrivial Γ₀] (v : AddValuation K Γ₀) {x : K} : v x != (⊤ : Γ
₀) ↔ x != 0
参数：v : AddValuation K Γ₀。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Valuation.ne_zero_iff`：ne_zero_iff [Nontrivial Γ₀] (v : Valuation K Γ₀) 
{x : K} : v x != 0 ↔ x != 0
· 使用定理 `OrderDual.instNontrivial`：∀ {α : Type u_1} [h : Nontrivial α], Nontrivia
l αᵒᵈ
-/
theorem ne_top_iff [Nontrivial Γ₀] (v : AddValuation K Γ₀) {x : K} : v x ≠ (⊤ : Γ₀) ↔ x ≠ 0 :=
  v.ne_zero_iff

/-- A ring homomorphism `S → R` induces a map `AddValuation R Γ₀ → AddValuation S Γ₀`. -/
/-
**AddValuation.comap** 是 Mathlib 中的一个定义，位于命名空间 `AddValuation`。
形式化陈述：comap {S : Type*} [Ring S] (f : S ->+* R) (v : AddValuation R Γ₀) : AddVal
uation S Γ₀
参数：f : S ->+* R；v : AddValuation R Γ₀。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A ring homomorphism `S → R` induces a map `AddValuation R Γ₀ → AddValuation S Γ₀
`.
-/
def comap {S : Type*} [Ring S] (f : S →+* R) (v : AddValuation R Γ₀) : AddValuation S Γ₀ :=
  Valuation.comap f v

@[simp]
/-
**AddValuation.comap_id** 是 Mathlib 中的一个定理，位于命名空间 `AddValuation`。
形式化陈述：comap_id : v.comap (RingHom.id R) = v
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Valuation.comap_id`：comap_id : v.comap (RingHom.id R) = v
-/
theorem comap_id : v.comap (RingHom.id R) = v :=
  Valuation.comap_id v
/-
**AddValuation.comap_comp** 是 Mathlib 中的一个定理，位于命名空间 `AddValuation`。
形式化陈述：comap_comp {S₁ : Type*} {S₂ : Type*} [Ring S₁] [Ring S₂] (f : S₁ ->+* S₂) 
(g : S₂ ->+* R) : v.comap (g.comp f) = (v.comap g).comap f
参数：f : S₁ ->+* S₂；g : S₂ ->+* R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Valuation.comap_comp`：comap_comp {S₁ : Type*} {S₂ : Type*} [Ring S₁] [Ri
ng S₂] (f : S₁ ->+* S₂) (g : S₂ ->+* R) : v.comap (g.comp f) = (v.comap g).comap
 f
-/
theorem comap_comp {S₁ : Type*} {S₂ : Type*} [Ring S₁] [Ring S₂] (f : S₁ →+* S₂) (g : S₂ →+* R) :
    v.comap (g.comp f) = (v.comap g).comap f :=
  Valuation.comap_comp v f g

/-- A `≤`-preserving, `⊤`-preserving group homomorphism `Γ₀ → Γ'₀` induces a map
  `AddValuation R Γ₀ → AddValuation R Γ'₀`.
-/
/-
**AddValuation.map** 是 Mathlib 中的一个定义，位于命名空间 `AddValuation`。
形式化陈述：map (f : Γ₀ ->+ Γ'₀) (ht : f ⊤ = ⊤) (hf : Monotone f) (v : AddValuation R 
Γ₀) : AddValuation R Γ'₀
参数：f : Γ₀ ->+ Γ'₀；ht : f ⊤ = ⊤；hf : Monotone f；v : AddValuation R Γ₀。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `≤`-preserving, `⊤`-preserving group homomorphism `Γ₀ → Γ'₀` induces a map
  `AddValuation R Γ₀ → AddValuation R Γ'₀`.
-/
def map (f : Γ₀ →+ Γ'₀) (ht : f ⊤ = ⊤) (hf : Monotone f) (v : AddValuation R Γ₀) :
    AddValuation R Γ'₀ :=
  @Valuation.map R (Multiplicative Γ₀ᵒᵈ) (Multiplicative Γ'₀ᵒᵈ) _ _ _
    { toFun := f
      map_mul' := f.map_add
      map_one' := f.map_zero
      map_zero' := ht } (fun _ _ h => hf h) v

@[simp]
/-
**AddValuation.map_apply** 是 Mathlib 中的一个引理，位于命名空间 `AddValuation`。
形式化陈述：map_apply (f : Γ₀ ->+ Γ'₀) (ht : f ⊤ = ⊤) (hf : Monotone f) (v : AddValuat
ion R Γ₀) (r : R) : v.map f ht hf r = f (v r)
参数：f : Γ₀ ->+ Γ'₀；ht : f ⊤ = ⊤；hf : Monotone f；v : AddValuation R Γ₀；r : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map_apply (f : Γ₀ →+ Γ'₀) (ht : f ⊤ = ⊤) (hf : Monotone f) (v : AddValuation R Γ₀) (r : R) :
    v.map f ht hf r = f (v r) := rfl

/-- Two additive valuations on `R` are defined to be equivalent if they induce the same
  preorder on `R`. -/
/-
**AddValuation.IsEquiv** 是 Mathlib 中的一个定义，位于命名空间 `AddValuation`。
形式化陈述：IsEquiv (v₁ : AddValuation R Γ₀) (v₂ : AddValuation R Γ'₀) : Prop
参数：v₁ : AddValuation R Γ₀；v₂ : AddValuation R Γ'₀。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Two additive valuations on `R` are defined to be equivalent if they induce the s
ame
  preorder on `R`.
-/
def IsEquiv (v₁ : AddValuation R Γ₀) (v₂ : AddValuation R Γ'₀) : Prop :=
  Valuation.IsEquiv v₁ v₂

@[simp]
/-
**AddValuation.map_neg** 是 Mathlib 中的一个定理，位于命名空间 `AddValuation`。
形式化陈述：map_neg (x : R) : v (-x) = v x
参数：x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Valuation.map_neg`：map_neg (x : R) : v (-x) = v x
-/
theorem map_neg (x : R) : v (-x) = v x :=
  Valuation.map_neg v x
/-
**AddValuation.map_sub_swap** 是 Mathlib 中的一个定理，位于命名空间 `AddValuation`。
形式化陈述：map_sub_swap (x y : R) : v (x - y) = v (y - x)
参数：x y : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Valuation.map_sub_swap`：map_sub_swap (x y : R) : v (x - y) = v (y - x)
-/
theorem map_sub_swap (x y : R) : v (x - y) = v (y - x) :=
  Valuation.map_sub_swap v x y
/-
**AddValuation.map_sub** 是 Mathlib 中的一个定理，位于命名空间 `AddValuation`。
形式化陈述：map_sub (x y : R) : min (v x) (v y) <= v (x - y)
参数：x y : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Valuation.map_sub`：map_sub (x y : R) : v (x - y) <= max (v x) (v y)
-/
theorem map_sub (x y : R) : min (v x) (v y) ≤ v (x - y) :=
  Valuation.map_sub v x y
/-
**AddValuation.map_le_sub** 是 Mathlib 中的一个定理，位于命名空间 `AddValuation`。
形式化陈述：map_le_sub {x y : R} {g : Γ₀} (hx : g <= v x) (hy : g <= v y) : g <= v (x 
- y)
参数：hx : g <= v x；hy : g <= v y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Valuation.map_sub_le`：map_sub_le {x y g} (hx : v x <= g) (hy : v y <= g)
 : v (x - y) <= g
-/
theorem map_le_sub {x y : R} {g : Γ₀} (hx : g ≤ v x) (hy : g ≤ v y) : g ≤ v (x - y) :=
  Valuation.map_sub_le v hx hy

variable {x y : R}
/-
**AddValuation.map_add_of_distinct_val** 是 Mathlib 中的一个定理，位于命名空间 `AddValuation`。
形式化陈述：map_add_of_distinct_val (h : v x != v y) : v (x + y) = @Min.min Γ₀ _ (v x)
 (v y)
参数：h : v x != v y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Valuation.map_add_of_distinct_val`：map_add_of_distinct_val (h : v x != v
 y) : v (x + y) = max (v x) (v y)
-/
theorem map_add_of_distinct_val (h : v x ≠ v y) : v (x + y) = @Min.min Γ₀ _ (v x) (v y) :=
  Valuation.map_add_of_distinct_val v h
/-
**AddValuation.map_add_eq_of_lt_left** 是 Mathlib 中的一个定理，位于命名空间 `AddValuation`。
形式化陈述：map_add_eq_of_lt_left {x y : R} (h : v x < v y) : v (x + y) = v x
参数：h : v x < v y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddValuation.map_add_of_distinct_val`：map_add_of_distinct_val (h : v x !
= v y) : v (x + y) = @Min.min Γ₀ _ (v x) (v y)
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用引理 `min_eq_left`：min_eq_left (h : a <= b) : min a b = a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem map_add_eq_of_lt_left {x y : R} (h : v x < v y) :
    v (x + y) = v x := by
  rw [map_add_of_distinct_val _ h.ne, min_eq_left h.le]
/-
**AddValuation.map_add_eq_of_lt_right** 是 Mathlib 中的一个定理，位于命名空间 `AddValuation`。
形式化陈述：map_add_eq_of_lt_right {x y : R} (hx : v y < v x) : v (x + y) = v y
参数：hx : v y < v x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddValuation.map_add_eq_of_lt_left`：map_add_eq_of_lt_left {x y : R} (h :
 v x < v y) : v (x + y) = v x
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
theorem map_add_eq_of_lt_right {x y : R} (hx : v y < v x) :
    v (x + y) = v y := add_comm y x ▸ map_add_eq_of_lt_left v hx
/-
**AddValuation.map_sub_eq_of_lt_left** 是 Mathlib 中的一个定理，位于命名空间 `AddValuation`。
形式化陈述：map_sub_eq_of_lt_left {x y : R} (hx : v x < v y) : v (x - y) = v x
参数：hx : v x < v y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `AddValuation.map_add_eq_of_lt_left`：map_add_eq_of_lt_left {x y : R} (h :
 v x < v y) : v (x + y) = v x
· 使用定理 `AddValuation.map_neg`：map_neg (x : R) : v (-x) = v x
-/
theorem map_sub_eq_of_lt_left {x y : R} (hx : v x < v y) :
    v (x - y) = v x := by
  rw [sub_eq_add_neg]
  apply map_add_eq_of_lt_left
  rwa [map_neg]
/-
**AddValuation.map_sub_eq_of_lt_right** 是 Mathlib 中的一个定理，位于命名空间 `AddValuation`。
形式化陈述：map_sub_eq_of_lt_right {x y : R} (hx : v y < v x) : v (x - y) = v y
参数：hx : v y < v x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddValuation.map_sub_eq_of_lt_left`：map_sub_eq_of_lt_left {x y : R} (hx 
: v x < v y) : v (x - y) = v x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AddValuation.map_sub_swap`：map_sub_swap (x y : R) : v (x - y) = v (y - x
)
-/
theorem map_sub_eq_of_lt_right {x y : R} (hx : v y < v x) :
    v (x - y) = v y := map_sub_swap v x y ▸ map_sub_eq_of_lt_left v hx
/-
**AddValuation.map_eq_of_lt_sub** 是 Mathlib 中的一个定理，位于命名空间 `AddValuation`。
形式化陈述：map_eq_of_lt_sub (h : v x < v (y - x)) : v y = v x
参数：h : v x < v (y - x)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Valuation.map_eq_of_sub_lt`：map_eq_of_sub_lt (h : v (y - x) < v x) : v y
 = v x
-/
theorem map_eq_of_lt_sub (h : v x < v (y - x)) : v y = v x :=
  Valuation.map_eq_of_sub_lt v h

end Monoid

section Group

variable [LinearOrderedAddCommGroupWithTop Γ₀] [Ring R] (v : AddValuation R Γ₀) {x y : R}

@[simp]
/-
**AddValuation.map_inv** 是 Mathlib 中的一个定理，位于命名空间 `AddValuation`。
形式化陈述：map_inv (v : AddValuation K Γ₀) {x : K} : v x⁻¹ = -(v x)
参数：v : AddValuation K Γ₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_inv₀`：map_inv₀ : f a⁻¹ = (f a)⁻¹
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
-/
theorem map_inv (v : AddValuation K Γ₀) {x : K} : v x⁻¹ = -(v x) :=
  map_inv₀ (toValuation v) x

@[simp]
/-
**AddValuation.map_div** 是 Mathlib 中的一个定理，位于命名空间 `AddValuation`。
形式化陈述：map_div (v : AddValuation K Γ₀) {x y : K} : v (x / y) = v x - v y
参数：v : AddValuation K Γ₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_div₀`：map_div₀ : f (a / b) = f a / f b
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
-/
theorem map_div (v : AddValuation K Γ₀) {x y : K} : v (x / y) = v x - v y :=
  map_div₀ (toValuation v) x y

end Group

end Basic

namespace IsEquiv

variable [LinearOrderedAddCommMonoidWithTop Γ₀] [LinearOrderedAddCommMonoidWithTop Γ'₀]
  [Ring R]
  {Γ''₀ : Type*} [LinearOrderedAddCommMonoidWithTop Γ''₀]
  {v : AddValuation R Γ₀} {v₁ : AddValuation R Γ₀}
  {v₂ : AddValuation R Γ'₀} {v₃ : AddValuation R Γ''₀}

@[refl]
/-
**AddValuation.IsEquiv.refl** 是 Mathlib 中的一个定理，位于命名空间 `AddValuation.IsEquiv`。
形式化陈述：refl : v.IsEquiv v
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Valuation.IsEquiv.refl`：refl : v.IsEquiv v
-/
theorem refl : v.IsEquiv v :=
  Valuation.IsEquiv.refl

@[symm]
/-
**AddValuation.IsEquiv.symm** 是 Mathlib 中的一个定理，位于命名空间 `AddValuation.IsEquiv`。
形式化陈述：symm (h : v₁.IsEquiv v₂) : v₂.IsEquiv v₁
参数：h : v₁.IsEquiv v₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Valuation.IsEquiv.symm`：symm (h : v₁.IsEquiv v₂) : v₂.IsEquiv v₁
-/
theorem symm (h : v₁.IsEquiv v₂) : v₂.IsEquiv v₁ :=
  Valuation.IsEquiv.symm h

@[trans]
/-
**AddValuation.IsEquiv.trans** 是 Mathlib 中的一个定理，位于命名空间 `AddValuation.IsEquiv`。
形式化陈述：trans (h₁₂ : v₁.IsEquiv v₂) (h₂₃ : v₂.IsEquiv v₃) : v₁.IsEquiv v₃
参数：h₁₂ : v₁.IsEquiv v₂；h₂₃ : v₂.IsEquiv v₃。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Valuation.IsEquiv.trans`：trans (h₁₂ : v₁.IsEquiv v₂) (h₂₃ : v₂.IsEquiv v
₃) : v₁.IsEquiv v₃
-/
theorem trans (h₁₂ : v₁.IsEquiv v₂) (h₂₃ : v₂.IsEquiv v₃) : v₁.IsEquiv v₃ :=
  Valuation.IsEquiv.trans h₁₂ h₂₃
/-
**AddValuation.IsEquiv.of_eq** 是 Mathlib 中的一个定理，位于命名空间 `AddValuation.IsEquiv`。
形式化陈述：of_eq {v' : AddValuation R Γ₀} (h : v = v') : v.IsEquiv v'
参数：h : v = v'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Valuation.IsEquiv.of_eq`：of_eq {v' : Valuation R Γ₀} (h : v = v') : v.Is
Equiv v'
-/
theorem of_eq {v' : AddValuation R Γ₀} (h : v = v') : v.IsEquiv v' :=
  Valuation.IsEquiv.of_eq h
/-
**AddValuation.IsEquiv.map** 是 Mathlib 中的一个定理，位于命名空间 `AddValuation.IsEquiv`。
形式化陈述：map {v' : AddValuation R Γ₀} (f : Γ₀ ->+ Γ'₀) (ht : f ⊤ = ⊤) (hf : Monoton
e f) (inf : Injective f) (h : v.IsEquiv v') : (v.map f ht hf).IsEquiv (v'.map f 
ht hf)
参数：f : Γ₀ ->+ Γ'₀；ht : f ⊤ = ⊤；hf : Monotone f；inf : Injective f；h : v.IsEquiv v
'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Valuation.IsEquiv.map`：map {v' : Valuation R Γ₀} (f : Γ₀ ->*₀ Γ'₀) (hf :
 Monotone f) (inf : Injective f) (h : v.IsEquiv v') : (v.map f hf).IsEquiv (v'.m
ap f hf)
· 使用定理 `AddMonoidHom.map_zero`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M
] [inst_1 : AddZero N] (f : M →+ N), f 0 = 0
· 使用定理 `AddMonoidHom.map_add`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M]
 [inst_1 : AddZero N] (f : M →+ N) (a b : M), f (a + b) = f a + f b
-/
theorem map {v' : AddValuation R Γ₀} (f : Γ₀ →+ Γ'₀) (ht : f ⊤ = ⊤) (hf : Monotone f)
    (inf : Injective f) (h : v.IsEquiv v') : (v.map f ht hf).IsEquiv (v'.map f ht hf) :=
  @Valuation.IsEquiv.map R (Multiplicative Γ₀ᵒᵈ) (Multiplicative Γ'₀ᵒᵈ) _ _ _ _ _
    { toFun := f
      map_mul' := f.map_add
      map_one' := f.map_zero
      map_zero' := ht } (fun _x _y h => hf h) inf h

/-- `comap` preserves equivalence. -/
/-
**AddValuation.IsEquiv.comap** 是 Mathlib 中的一个定理，位于命名空间 `AddValuation.IsEquiv`。
形式化陈述：comap {S : Type*} [Ring S] (f : S ->+* R) (h : v₁.IsEquiv v₂) : (v₁.comap 
f).IsEquiv (v₂.comap f)
参数：f : S ->+* R；h : v₁.IsEquiv v₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Valuation.IsEquiv.comap`：comap {S : Type*} [Ring S] (f : S ->+* R) (h : 
v₁.IsEquiv v₂) : (v₁.comap f).IsEquiv (v₂.comap f)

--- 原说明 ---
`comap` preserves equivalence.
-/
theorem comap {S : Type*} [Ring S] (f : S →+* R) (h : v₁.IsEquiv v₂) :
    (v₁.comap f).IsEquiv (v₂.comap f) :=
  Valuation.IsEquiv.comap f h
/-
**AddValuation.IsEquiv.val_eq** 是 Mathlib 中的一个定理，位于命名空间 `AddValuation.IsEquiv`。
形式化陈述：val_eq (h : v₁.IsEquiv v₂) {r s : R} : v₁ r = v₁ s ↔ v₂ r = v₂ s
参数：h : v₁.IsEquiv v₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Valuation.IsEquiv.eq_iff`：eq_iff (h : v₁.IsEquiv v₂) {r s : R} : v₁ r = 
v₁ s ↔ v₂ r = v₂ s
-/
theorem val_eq (h : v₁.IsEquiv v₂) {r s : R} : v₁ r = v₁ s ↔ v₂ r = v₂ s :=
  Valuation.IsEquiv.eq_iff h
/-
**AddValuation.IsEquiv.ne_top** 是 Mathlib 中的一个定理，位于命名空间 `AddValuation.IsEquiv`。
形式化陈述：ne_top (h : v₁.IsEquiv v₂) {r : R} : v₁ r != (⊤ : Γ₀) ↔ v₂ r != (⊤ : Γ'₀)
参数：h : v₁.IsEquiv v₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.ne`：∀ {α : Sort u_1} {β : Sort u_2} {a b : α} {c d : β}, (a = b ↔ c 
= d) → (a ≠ b ↔ c ≠ d)
· 使用定理 `Valuation.IsEquiv.eq_zero`：eq_zero (h : v₁.IsEquiv v₂) {r : R} : v₁ r = 
0 ↔ v₂ r = 0
-/
theorem ne_top (h : v₁.IsEquiv v₂) {r : R} : v₁ r ≠ (⊤ : Γ₀) ↔ v₂ r ≠ (⊤ : Γ'₀) :=
  (Valuation.IsEquiv.eq_zero h).ne

end IsEquiv

section Supp

variable [LinearOrderedAddCommMonoidWithTop Γ₀] [CommRing R] (v : AddValuation R Γ₀)

/-- The support of an additive valuation `v : R → Γ₀` is the ideal of `R` where `v x = ⊤` -/
/-
**AddValuation.supp** 是 Mathlib 中的一个定义，位于命名空间 `AddValuation`。
形式化陈述：supp : Ideal R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The support of an additive valuation `v : R → Γ₀` is the ideal of `R` where `v x
 = ⊤`
-/
def supp : Ideal R :=
  Valuation.supp v

@[simp]
/-
**AddValuation.mem_supp_iff** 是 Mathlib 中的一个定理，位于命名空间 `AddValuation`。
形式化陈述：mem_supp_iff (x : R) : x in supp v ↔ v x = (⊤ : Γ₀)
参数：x : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Valuation.mem_supp_iff`：mem_supp_iff (x : R) : x in supp v ↔ v x = 0
-/
theorem mem_supp_iff (x : R) : x ∈ supp v ↔ v x = (⊤ : Γ₀) :=
  Valuation.mem_supp_iff v x
/-
**AddValuation.map_add_supp** 是 Mathlib 中的一个定理，位于命名空间 `AddValuation`。
形式化陈述：map_add_supp (a : R) {s : R} (h : s in supp v) : v (a + s) = v a
参数：a : R；h : s in supp v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Valuation.map_add_supp`：map_add_supp (a : R) {s : R} (h : s in supp v) :
 v (a + s) = v a
-/
theorem map_add_supp (a : R) {s : R} (h : s ∈ supp v) : v (a + s) = v a :=
  Valuation.map_add_supp v a h

end Supp

end AddValuation

namespace Valuation

variable {K Γ₀ : Type*} [Ring R] [LinearOrderedCommMonoidWithZero Γ₀]

/-- The `AddValuation` associated to a `Valuation`. -/
/-
**Valuation.toAddValuation** 是 Mathlib 中的一个定义，位于命名空间 `Valuation`。
形式化陈述：toAddValuation : Valuation R Γ₀ ≃ AddValuation R (Additive Γ₀)ᵒᵈ
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
The `AddValuation` associated to a `Valuation`.
-/
def toAddValuation : Valuation R Γ₀ ≃ AddValuation R (Additive Γ₀)ᵒᵈ :=
  .trans (congr
    { toFun := fun x ↦ .ofAdd <| .toDual <| .toDual <| .ofMul x
      invFun := fun x ↦ x.toAdd.ofDual.ofDual.toMul
      map_mul' := fun _x _y ↦ rfl
      map_le_map_iff' := .rfl }) (AddValuation.ofValuation (R := R) (Γ₀ := (Additive Γ₀)ᵒᵈ))

/-- The `Valuation` associated to a `AddValuation`.
-/
/-
**Valuation.ofAddValuation** 是 Mathlib 中的一个定义，位于命名空间 `Valuation`。
形式化陈述：ofAddValuation : AddValuation R (Additive Γ₀)ᵒᵈ ≃ Valuation R Γ₀
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
The `Valuation` associated to a `AddValuation`.
-/
def ofAddValuation : AddValuation R (Additive Γ₀)ᵒᵈ ≃ Valuation R Γ₀ :=
  AddValuation.toValuation.trans <| congr <|
    { toFun := fun x ↦ x.toAdd.ofDual.ofDual.toMul
      invFun := fun x ↦ .ofAdd <| .toDual <| .toDual <| .ofMul x
      map_mul' := fun _x _y ↦ rfl
      map_le_map_iff' := .rfl }

@[simp]
/-
**Valuation.ofAddValuation_symm_eq** 是 Mathlib 中的一个引理，位于命名空间 `Valuation`。
形式化陈述：ofAddValuation_symm_eq : ofAddValuation.symm = toAddValuation (R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma ofAddValuation_symm_eq : ofAddValuation.symm = toAddValuation (R := R) (Γ₀ := Γ₀) := rfl

@[simp]
/-
**Valuation.toAddValuation_symm_eq** 是 Mathlib 中的一个引理，位于命名空间 `Valuation`。
形式化陈述：toAddValuation_symm_eq : toAddValuation.symm = ofAddValuation (R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma toAddValuation_symm_eq : toAddValuation.symm = ofAddValuation (R := R) (Γ₀ := Γ₀) := rfl

@[simp]
/-
**Valuation.ofAddValuation_toAddValuation** 是 Mathlib 中的一个引理，位于命名空间 `Valuation`。
形式化陈述：ofAddValuation_toAddValuation (v : Valuation R Γ₀) : ofAddValuation (toAdd
Valuation v) = v
参数：v : Valuation R Γ₀。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofAddValuation_toAddValuation (v : Valuation R Γ₀) : ofAddValuation (toAddValuation v) = v :=
  rfl

@[simp]
/-
**Valuation.toValuation_ofValuation** 是 Mathlib 中的一个引理，位于命名空间 `Valuation`。
形式化陈述：toValuation_ofValuation (v : AddValuation R (Additive Γ₀)ᵒᵈ) : toAddValuat
ion (ofAddValuation v) = v
参数：v : AddValuation R (Additive Γ₀)ᵒᵈ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toValuation_ofValuation (v : AddValuation R (Additive Γ₀)ᵒᵈ) :
    toAddValuation (ofAddValuation v) = v := rfl

@[simp]
/-
**Valuation.toAddValuation_apply** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`。
形式化陈述：toAddValuation_apply (v : Valuation R Γ₀) (r : R) : toAddValuation v r = O
rderDual.toDual (Additive.ofMul (v r))
参数：v : Valuation R Γ₀；r : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toAddValuation_apply (v : Valuation R Γ₀) (r : R) :
    toAddValuation v r = OrderDual.toDual (Additive.ofMul (v r)) :=
  rfl

@[simp]
/-
**Valuation.ofAddValuation_apply** 是 Mathlib 中的一个定理，位于命名空间 `Valuation`。
形式化陈述：ofAddValuation_apply (v : AddValuation R (Additive Γ₀)ᵒᵈ) (r : R) : ofAddV
aluation v r = Additive.toMul (OrderDual.ofDual (v r))
参数：v : AddValuation R (Additive Γ₀)ᵒᵈ；r : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofAddValuation_apply (v : AddValuation R (Additive Γ₀)ᵒᵈ) (r : R) :
    ofAddValuation v r = Additive.toMul (OrderDual.ofDual (v r)) :=
  rfl
/-
**Valuation.** 是 Mathlib 中的一个实例，位于命名空间 `Valuation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (v : Valuation R Γ₀) : CommMonoidWithZero (MonoidHom.mrange (.ofClass v : R →*₀ _)) :=
  inferInstanceAs (CommMonoidWithZero (MonoidHom.mrange (MonoidWithZeroHom.ofClass v)))

@[simp]
/-
**Valuation.val_mrange_zero** 是 Mathlib 中的一个引理，位于命名空间 `Valuation`。
形式化陈述：val_mrange_zero (v : Valuation R Γ₀) : ((0 : MonoidHom.mrange (.ofClass v 
: R ->*₀ _)) : Γ₀) = 0
参数：v : Valuation R Γ₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
-/
lemma val_mrange_zero (v : Valuation R Γ₀) :
    ((0 : MonoidHom.mrange (.ofClass v : R →*₀ _)) : Γ₀) = 0 :=
  rfl
/-
**Valuation.** 是 Mathlib 中的一个实例，位于命名空间 `Valuation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {Γ₀} [LinearOrderedCommGroupWithZero Γ₀] [DivisionRing K] (v : Valuation K Γ₀) :
    CommGroupWithZero (MonoidHom.mrange (.ofClass v : K →*₀ _)) :=
  inferInstanceAs (CommGroupWithZero (MonoidHom.mrange (MonoidWithZeroHom.ofClass v)))

end Valuation

