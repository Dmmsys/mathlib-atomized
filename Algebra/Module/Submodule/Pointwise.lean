/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Jujian Zhang
-/
module

public import Mathlib.Algebra.GroupWithZero.Subgroup
public import Mathlib.Algebra.Order.Group.Action
public import Mathlib.Algebra.Module.Submodule.Range

/-! # Pointwise instances on `Submodule`s

This file provides:

* `Submodule.pointwiseNeg`

and the actions

* `Submodule.pointwiseDistribMulAction`
* `Submodule.pointwiseMulActionWithZero`

which matches the action of `Set.mulActionSet`.

This file also provides:
* `Submodule.pointwiseSetSMulSubmodule`: for `R`-module `M`, a `s : Set R` can act on
  `N : Submodule R M` by defining `s • N` to be the smallest submodule containing all `a • n`
  where `a ∈ s` and `n ∈ N`.

These actions are available in the `Pointwise` locale.

## Implementation notes

For an `R`-module `M`, the action of a subset of `R` acting on a submodule of `M` introduced in
section `set_acting_on_submodules` does not have a counterpart in the files
`Mathlib/Algebra/Group/Submonoid/Pointwise.lean` and
`Mathlib/Algebra/GroupWithZero/Submonoid/Pointwise.lean`.

Other than section `DistribMulAction`, most of the lemmas in this file are direct copies of
lemmas from the file `Mathlib/Algebra/Group/Submonoid/Pointwise.lean`.
-/

@[expose] public section

assert_not_exists Ideal

variable {α : Type*} {R : Type*} {M : Type*}

open scoped Pointwise

namespace Submodule

section Neg

section Semiring

variable [Semiring R] [AddCommGroup M] [Module R M]

/-- The submodule with every element negated. Note if `R` is a ring and not just a semiring, this
is a no-op, as shown by `Submodule.neg_eq_self`.

Recall that When `R` is the semiring corresponding to the nonnegative elements of `R'`,
`Submodule R' M` is the type of cones of `M`. This instance reflects such cones about `0`.

This is available as an instance in the `Pointwise` locale. -/
@[instance_reducible]
/-
**Submodule.pointwiseNeg** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：{R : Type u_2} →   {M : Type u_3} → [inst : Semiring R] → [inst_1 : AddCom
mGroup M] → [inst_2 : _root_.Module R M] → Neg (Submodule R M)
参数：Submodule R M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The submodule with every element negated. Note if `R` is a ring and not just a s
emiring, this
is a no-op, as shown by `Submodule.neg_eq_self`.

Recall that When `R` is the semiring corresponding to the nonnegative elements o
f `R'`,
`Submodule R' M` is the type of cones of `M`. This instance reflects such cones 
about `0`.

This is available as an instance in the `Pointwise` locale.
-/
protected def pointwiseNeg : Neg (Submodule R M) where
  neg p :=
    { -p.toAddSubmonoid with
      smul_mem' := fun r m hm => Set.mem_neg.2 <| smul_neg r m ▸ p.smul_mem r <| Set.mem_neg.1 hm }

scoped[Pointwise] attribute [instance] Submodule.pointwiseNeg

open scoped Pointwise

@[simp]
/-
**Submodule.coe_set_neg** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：coe_set_neg (S : Submodule R M) : ↑(-S) = -(S : Set M)
参数：S : Submodule R M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_set_neg (S : Submodule R M) : ↑(-S) = -(S : Set M) :=
  rfl

@[simp]
/-
**Submodule.neg_toAddSubmonoid** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：neg_toAddSubmonoid (S : Submodule R M) : (-S).toAddSubmonoid = -S.toAddSub
monoid
参数：S : Submodule R M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem neg_toAddSubmonoid (S : Submodule R M) : (-S).toAddSubmonoid = -S.toAddSubmonoid :=
  rfl

@[simp]
/-
**Submodule.mem_neg** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：mem_neg {g : M} {S : Submodule R M} : g in -S ↔ -g in S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_neg {g : M} {S : Submodule R M} : g ∈ -S ↔ -g ∈ S :=
  Iff.rfl

/-- `Submodule.pointwiseNeg` is involutive.

This is available as an instance in the `Pointwise` locale. -/
@[instance_reducible]
/-
**Submodule.involutivePointwiseNeg** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：{R : Type u_2} →   {M : Type u_3} →     [inst : Semiring R] → [inst_1 : Ad
dCommGroup M] → [inst_2 : _root_.Module R M] → InvolutiveNeg (Submodule R M)
参数：Submodule R M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Submodule.pointwiseNeg` is involutive.

This is available as an instance in the `Pointwise` locale.
-/
protected def involutivePointwiseNeg : InvolutiveNeg (Submodule R M) where
  neg_neg _S := SetLike.coe_injective <| neg_neg _

scoped[Pointwise] attribute [instance] Submodule.involutivePointwiseNeg

@[simp]
/-
**Submodule.neg_le_neg** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：neg_le_neg {S T : Submodule R M} : -S <= -T ↔ S <= T
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `SetLike.coe_subset_coe`：∀ {A : Type u_1} {B : Type u_2} [inst : SetLike 
A B] [inst_1 : LE A] [IsConcreteLE A B] {S T : A}, ↑S ⊆ ↑T ↔ S ≤ T
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `Set.neg_subset_neg`：∀ {α : Type u_2} [inst : InvolutiveNeg α] {s t : Set
 α}, -s ⊆ -t ↔ s ⊆ t
-/
theorem neg_le_neg {S T : Submodule R M} : -S ≤ -T ↔ S ≤ T :=
  SetLike.coe_subset_coe.symm.trans Set.neg_subset_neg
/-
**Submodule.neg_le** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：neg_le {S T : Submodule R M} : -S <= T ↔ S <= -T
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `SetLike.coe_subset_coe`：∀ {A : Type u_1} {B : Type u_2} [inst : SetLike 
A B] [inst_1 : LE A] [IsConcreteLE A B] {S T : A}, ↑S ⊆ ↑T ↔ S ≤ T
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `Set.neg_subset`：∀ {α : Type u_2} [inst : InvolutiveNeg α] {s t : Set α},
 -s ⊆ t ↔ s ⊆ -t
-/
theorem neg_le {S T : Submodule R M} : -S ≤ T ↔ S ≤ -T :=
  SetLike.coe_subset_coe.symm.trans Set.neg_subset
/-
**Submodule.neg_eq_self_iff_neg_le** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：neg_eq_self_iff_neg_le {S : Submodule R M} : -S = S ↔ -S <= S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用引理 `antisymm`：antisymm [Std.Antisymm r] : a ≺ b -> b ≺ a -> a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.neg_le`：neg_le {S T : Submodule R M} : -S <= T ↔ S <= -T
-/
theorem neg_eq_self_iff_neg_le {S : Submodule R M} : -S = S ↔ -S ≤ S :=
  ⟨le_of_eq, fun h => antisymm h <| neg_le.mp h⟩

/-- `Submodule.pointwiseNeg` as an order isomorphism. -/
/-
**Submodule.negOrderIso** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：negOrderIso : Submodule R M ≃o Submodule R M where toEquiv
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.neg_le_neg`：neg_le_neg {S T : Submodule R M} : -S <= -T ↔ S <=
 T

--- 原说明 ---
`Submodule.pointwiseNeg` as an order isomorphism.
-/
def negOrderIso : Submodule R M ≃o Submodule R M where
  toEquiv := Equiv.neg _
  map_rel_iff' := @neg_le_neg _ _ _ _ _

@[simp]
/-
**Submodule.neg_inf** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：neg_inf (S T : Submodule R M) : -(S ⊓ T) = -S ⊓ -T
参数：S T : Submodule R M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem neg_inf (S T : Submodule R M) : -(S ⊓ T) = -S ⊓ -T := rfl

@[simp]
/-
**Submodule.neg_sup** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：neg_sup (S T : Submodule R M) : -(S ⊔ T) = -S ⊔ -T
参数：S T : Submodule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.map_sup`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSup
 α] [inst_1 : SemilatticeSup β] (f : α ≃o β) (x y : α),   f (x ⊔ y) = f x ⊔ f y
-/
theorem neg_sup (S T : Submodule R M) : -(S ⊔ T) = -S ⊔ -T :=
  (negOrderIso : Submodule R M ≃o Submodule R M).map_sup S T

@[simp]
/-
**Submodule.neg_bot** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：neg_bot : -(⊥ : Submodule R M) = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.neg_singleton`：∀ {α : Type u_2} [inst : InvolutiveNeg α] (a : α), -{
a} = {-a}
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
-/
theorem neg_bot : -(⊥ : Submodule R M) = ⊥ :=
  SetLike.coe_injective <| (Set.neg_singleton 0).trans <| congr_arg _ neg_zero

@[simp]
/-
**Submodule.neg_top** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：neg_top : -(⊤ : Submodule R M) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.neg_univ`：∀ {α : Type u_2} [inst : Neg α], -Set.univ = Set.univ
-/
theorem neg_top : -(⊤ : Submodule R M) = ⊤ :=
  SetLike.coe_injective <| Set.neg_univ

@[simp]
/-
**Submodule.neg_iInf** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：neg_iInf {ι : Sort*} (S : ι -> Submodule R M) : (-⨅ i, S i) = ⨅ i, -S i
参数：S : ι -> Submodule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.map_iInf`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} [inst 
: CompleteLattice α] [inst_1 : CompleteLattice β] (f : α ≃o β)   (x : ι → α), f 
(⨅ i, x…
-/
theorem neg_iInf {ι : Sort*} (S : ι → Submodule R M) : (-⨅ i, S i) = ⨅ i, -S i :=
  (negOrderIso : Submodule R M ≃o Submodule R M).map_iInf _

@[simp]
/-
**Submodule.neg_iSup** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：neg_iSup {ι : Sort*} (S : ι -> Submodule R M) : (-⨆ i, S i) = ⨆ i, -S i
参数：S : ι -> Submodule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.map_iSup`：OrderIso.map_iSup [CompleteLattice β] (f : α ≃o β) (x
 : ι -> α) : f (⨆ i, x i) = ⨆ i, f (x i)
-/
theorem neg_iSup {ι : Sort*} (S : ι → Submodule R M) : (-⨆ i, S i) = ⨆ i, -S i :=
  (negOrderIso : Submodule R M ≃o Submodule R M).map_iSup _

variable {S : Type*} [Semiring S] [SMul S R] [Module S M] [IsScalarTower S R M]
/-
**Submodule.neg_restrictScalars** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：∀ {R : Type u_2} {M : Type u_3} [inst : Semiring R] [inst_1 : AddCommGroup
 M] [inst_2 : _root_.Module R M]   {S : Type u_4} [inst_3 : Semiring S] [inst_4 
: SMul S R] [inst_5 : _root_.Module S M] [inst_6 : IsScalarTower S R M]   (p : S
ubmodule R M), -Submodule.restrictScalars S p = Submodule.restrictScalars S (-p)
参数：p : Submodule R M；-p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] theorem neg_restrictScalars (p : Submodule R M) :
  -(restrictScalars S p) = restrictScalars S (-p) := by ext; simp

end Semiring

open scoped Pointwise

@[simp]
/-
**Submodule.neg_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：neg_eq_self [Ring R] [AddCommGroup M] [Module R M] (p : Submodule R M) : -
p = p
参数：p : Submodule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `Submodule.neg_mem_iff`：∀ {R : Type u} {M : Type v} [inst : Ring R] [inst
_1 : AddCommGroup M] {module_M : _root_.Module R M} (p : Submodule R M)   {x : M
}, -x ∈ p ↔…
-/
theorem neg_eq_self [Ring R] [AddCommGroup M] [Module R M] (p : Submodule R M) : -p = p :=
  ext fun _ => p.neg_mem_iff

end Neg

variable [Semiring R] [AddCommMonoid M] [Module R M]

/-
**Submodule.pointwiseZero** 是 Mathlib 中的一个实例，位于命名空间 `Submodule`。
形式化陈述：pointwiseZero : Zero (Submodule R M) where zero
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance pointwiseZero : Zero (Submodule R M) where
  zero := ⊥
/-
**Submodule.pointwiseAdd** 是 Mathlib 中的一个实例，位于命名空间 `Submodule`。
形式化陈述：pointwiseAdd : Add (Submodule R M) where add
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance pointwiseAdd : Add (Submodule R M) where
  add := (· ⊔ ·)
/-
**Submodule.pointwiseAddCommMonoid** 是 Mathlib 中的一个实例，位于命名空间 `Submodule`。
形式化陈述：pointwiseAddCommMonoid : AddCommMonoid (Submodule R M) where add_assoc
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance pointwiseAddCommMonoid : AddCommMonoid (Submodule R M) where
  add_assoc := sup_assoc
  zero_add := bot_sup_eq
  add_zero := sup_bot_eq
  add_comm := sup_comm
  nsmul := nsmulRec

@[simp]
/-
**Submodule.add_eq_sup** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：add_eq_sup (p q : Submodule R M) : p + q = p ⊔ q
参数：p q : Submodule R M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem add_eq_sup (p q : Submodule R M) : p + q = p ⊔ q :=
  rfl

@[simp]
/-
**Submodule.zero_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：zero_eq_bot : (0 : Submodule R M) = ⊥
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zero_eq_bot : (0 : Submodule R M) = ⊥ :=
  rfl
/-
**Submodule.** 是 Mathlib 中的一个实例，位于命名空间 `Submodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsOrderedAddMonoid (Submodule R M) where
  add_le_add_left _ _ := sup_le_sup_right
/-
**Submodule.** 是 Mathlib 中的一个实例，位于命名空间 `Submodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CanonicallyOrderedAdd (Submodule R M) where
  exists_add_of_le {_a b} h := ⟨b, (sup_eq_right.2 h).symm⟩
  le_add_self _ _ := le_sup_right
  le_self_add := fun _a _b => le_sup_left

section

variable [Monoid α] [DistribMulAction α M] [SMulCommClass α R M]

/-- The action on a submodule corresponding to applying the action to every element.

This is available as an instance in the `Pointwise` locale. -/
@[instance_reducible]
/-
**Submodule.pointwiseDistribMulAction** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：{α : Type u_1} →   {R : Type u_2} →     {M : Type u_3} →       [inst : Sem
iring R] →         [inst_1 : AddCommMonoid M] →           [inst_2 : _root_.Modul
e R M] →             [inst_3 : Monoid α] →               [inst_4 : DistribMulAct
ion α M] → [SMulCommClass α R M] → DistribMulAction α (Submodule R M)
参数：Submodule R M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The action on a submodule corresponding to applying the action to every element.

This is available as an instance in the `Pointwise` locale.
-/
protected def pointwiseDistribMulAction : DistribMulAction α (Submodule R M) where
  smul a S := S.map (DistribSMul.toLinearMap R M a : M →ₗ[R] M)
  one_smul S :=
    (congr_arg (fun f : Module.End R M => S.map f) (LinearMap.ext <| one_smul α)).trans S.map_id
  mul_smul _a₁ _a₂ S :=
    (congr_arg (fun f : Module.End R M => S.map f) (LinearMap.ext <| mul_smul _ _)).trans
      (S.map_comp _ _)
  smul_zero _a := map_bot _
  smul_add _a _S₁ _S₂ := map_sup _ _ _

scoped[Pointwise] attribute [instance] Submodule.pointwiseDistribMulAction
/-
**Submodule.pointwise_smul_def** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：pointwise_smul_def {a : α} {S : Submodule R M} : a • S = S.map (DistribSMu
l.toLinearMap R M a)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pointwise_smul_def {a : α} {S : Submodule R M} :
    a • S = S.map (DistribSMul.toLinearMap R M a) := rfl

open scoped Pointwise

@[simp, norm_cast]
/-
**Submodule.coe_pointwise_smul** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：coe_pointwise_smul (a : α) (S : Submodule R M) : ↑(a • S) = a • (S : Set M
)
参数：a : α；S : Submodule R M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_pointwise_smul (a : α) (S : Submodule R M) : ↑(a • S) = a • (S : Set M) :=
  rfl

@[simp]
/-
**Submodule.pointwise_smul_toAddSubmonoid** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：pointwise_smul_toAddSubmonoid (a : α) (S : Submodule R M) : (a • S).toAddS
ubmonoid = a • S.toAddSubmonoid
参数：a : α；S : Submodule R M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pointwise_smul_toAddSubmonoid (a : α) (S : Submodule R M) :
    (a • S).toAddSubmonoid = a • S.toAddSubmonoid :=
  rfl

@[simp]
/-
**Submodule.pointwise_smul_toAddSubgroup** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：pointwise_smul_toAddSubgroup {R M : Type*} [Ring R] [AddCommGroup M] [Dist
ribMulAction α M] [Module R M] [SMulCommClass α R M] (a : α) (S : Submodule R M)
 : (a • S).toAddSubgroup = a • S.toAddSubgroup
参数：a : α；S : Submodule R M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pointwise_smul_toAddSubgroup {R M : Type*} [Ring R] [AddCommGroup M] [DistribMulAction α M]
    [Module R M] [SMulCommClass α R M] (a : α) (S : Submodule R M) :
    (a • S).toAddSubgroup = a • S.toAddSubgroup :=
  rfl
/-
**Submodule.mem_smul_pointwise_iff_exists** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：mem_smul_pointwise_iff_exists (m : M) (a : α) (S : Submodule R M) : m in a
 • S ↔ exists b in S, a • b = m
参数：m : M；a : α；S : Submodule R M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_smul_set`：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β] {t :
 Set β} {a : α} {x : β}, x ∈ a • t ↔ ∃ y ∈ t, a • y = x
-/
theorem mem_smul_pointwise_iff_exists (m : M) (a : α) (S : Submodule R M) :
    m ∈ a • S ↔ ∃ b ∈ S, a • b = m :=
  Set.mem_smul_set
/-
**Submodule.smul_mem_pointwise_smul** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：smul_mem_pointwise_smul (m : M) (a : α) (S : Submodule R M) : m in S -> a 
• m in a • S
参数：m : M；a : α；S : Submodule R M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.smul_mem_smul_set`：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β]
 {s : Set β} {a : α} {b : β}, b ∈ s → a • b ∈ a • s
-/
theorem smul_mem_pointwise_smul (m : M) (a : α) (S : Submodule R M) : m ∈ S → a • m ∈ a • S :=
  (Set.smul_mem_smul_set : _ → _ ∈ a • (S : Set M))
/-
**Submodule.** 是 Mathlib 中的一个实例，位于命名空间 `Submodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CovariantClass α (Submodule R M) HSMul.hSMul LE.le :=
  ⟨fun _ _ => map_mono⟩

/-- See also `Submodule.smul_bot`. -/
@[simp]
/-
**Submodule.smul_bot'** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：smul_bot' (a : α) : a • (⊥ : Submodule R M) = ⊥
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.map_bot`：map_bot (f : M ->ₛₗ[σ₁₂] M₂) : map f ⊥ = ⊥

--- 原说明 ---
See also `Submodule.smul_bot`.
-/
theorem smul_bot' (a : α) : a • (⊥ : Submodule R M) = ⊥ :=
  map_bot _

/-- See also `Submodule.smul_sup`. -/
/-
**Submodule.smul_sup'** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：smul_sup' (a : α) (S T : Submodule R M) : a • (S ⊔ T) = a • S ⊔ a • T
参数：a : α；S T : Submodule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.map_sup`：map_sup (f : M ->ₛₗ[σ₁₂] M₂) : map f (p ⊔ p') = map f
 p ⊔ map f p'

--- 原说明 ---
See also `Submodule.smul_sup`.
-/
theorem smul_sup' (a : α) (S T : Submodule R M) : a • (S ⊔ T) = a • S ⊔ a • T :=
  map_sup _ _ _

/-- See also `Submodule.smul_iSup`. -/
/-
**Submodule.smul_iSup'** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：smul_iSup' (a : α) {ι : Sort*} (f : ι -> Submodule R M) : a • ⨆ i, f i = ⨆
 i, a • f i
参数：a : α；f : ι -> Submodule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.map_iSup`：map_iSup {ι : Sort*} (f : M ->ₛₗ[σ₁₂] M₂) (p : ι -> 
Submodule R M) : map f (⨆ i, p i) = ⨆ i, map f (p i)

--- 原说明 ---
See also `Submodule.smul_iSup`.
-/
theorem smul_iSup' (a : α) {ι : Sort*} (f : ι → Submodule R M) :
    a • ⨆ i, f i = ⨆ i, a • f i :=
  map_iSup _ _
/-
**Submodule.pointwiseCentralScalar** 是 Mathlib 中的一个实例，位于命名空间 `Submodule`。
形式化陈述：pointwiseCentralScalar [DistribMulAction αᵐᵒᵖ M] [SMulCommClass αᵐᵒᵖ R M] 
[IsCentralScalar α M] : IsCentralScalar α (Submodule R M)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `IsCentralScalar.op_smul_eq_smul`：∀ {M : Type u_9} {α : Type u_10} {inst 
: SMul M α} {inst_1 : SMul Mᵐᵒᵖ α} [self : IsCentralScalar M α] (m : M) (a : α),
   MulOpposite.op m •…
-/
instance pointwiseCentralScalar [DistribMulAction αᵐᵒᵖ M] [SMulCommClass αᵐᵒᵖ R M]
    [IsCentralScalar α M] : IsCentralScalar α (Submodule R M) :=
  ⟨fun _a S => (congr_arg fun f : Module.End R M => S.map f) <| LinearMap.ext <| op_smul_eq_smul _⟩

@[simp]
/-
**Submodule.smul_le_self_of_tower** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：smul_le_self_of_tower {α : Type*} [Monoid α] [SMul α R] [DistribMulAction 
α M] [SMulCommClass α R M] [IsScalarTower α R M] (a : α) (S : Submodule R M) : a
 • S <= S
参数：a : α；S : Submodule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.smul_of_tower_mem`：smul_of_tower_mem [SMul S R] [SMul S M] [Is
ScalarTower S R M] (r : S) (h : x in p) : r • x in p
-/
theorem smul_le_self_of_tower {α : Type*} [Monoid α] [SMul α R] [DistribMulAction α M]
    [SMulCommClass α R M] [IsScalarTower α R M] (a : α) (S : Submodule R M) : a • S ≤ S := by
  rintro y ⟨x, hx, rfl⟩
  exact smul_of_tower_mem _ a hx

end

section

variable [Semiring α] [Module α M] [SMulCommClass α R M]

/-- The action on a submodule corresponding to applying the action to every element.

This is available as an instance in the `Pointwise` locale.

This is a stronger version of `Submodule.pointwiseDistribMulAction`. Note that `add_smul` does
not hold so this cannot be stated as a `Module`. -/
@[instance_reducible]
/-
**Submodule.pointwiseMulActionWithZero** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：{α : Type u_1} →   {R : Type u_2} →     {M : Type u_3} →       [inst : Sem
iring R] →         [inst_1 : AddCommMonoid M] →           [inst_2 : _root_.Modul
e R M] →             [inst_3 : Semiring α] →               [inst_4 : _root_.Modu
le α M] → [SMulCommClass α R M] → MulActionWithZero α (Submodule R M)
参数：Submodule R M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The action on a submodule corresponding to applying the action to every element.

This is available as an instance in the `Pointwise` locale.

This is a stronger version of `Submodule.pointwiseDistribMulAction`. Note that `
add_smul` does
not hold so this cannot be stated as a `Module`.
-/
protected def pointwiseMulActionWithZero : MulActionWithZero α (Submodule R M) :=
  { Submodule.pointwiseDistribMulAction with
    zero_smul := fun S =>
      (congr_arg (fun f : M →ₗ[R] M => S.map f) (LinearMap.ext <| zero_smul α)).trans S.map_zero }

scoped[Pointwise] attribute [instance] Submodule.pointwiseMulActionWithZero

end

/-!
### Sets acting on Submodules

Let `R` be a (semi)ring and `M` an `R`-module. Let `S` be a monoid which acts on `M` distributively,
then subsets of `S` can act on submodules of `M`.
For subset `s ⊆ S` and submodule `N ≤ M`, we define `s • N` to be the smallest submodule containing
all `r • n` where `r ∈ s` and `n ∈ N`.

#### Results
For arbitrary monoids `S` acting distributively on `M`, there is an induction principle for `s • N`:
To prove `P` holds for all `s • N`, it is enough
to prove:
- for all `r ∈ s` and `n ∈ N`, `P (r • n)`;
- for all `r` and `m ∈ s • N`, `P (r • n)`;
- for all `m₁, m₂`, `P m₁` and `P m₂` implies `P (m₁ + m₂)`;
- `P 0`.

To invoke this induction principle, use `induction x, hx using Submodule.set_smul_inductionOn` where
`x : M` and `hx : x ∈ s • N`

#### Notes
- If we assume the addition on subsets of `R` is the `⊔` and subtraction `⊓` i.e. use `SetSemiring`,
  then this action actually gives a module structure on submodules of `M` over subsets of `R`.
- If we generalize so that `r • N` makes sense for all `r : S`, then `Submodule.singleton_set_smul`
  and `Submodule.singleton_set_smul` can be generalized as well.
-/

section DistribMulAction

variable {S : Type*} [Monoid S]
variable [DistribMulAction S M]

/--
Let `s ⊆ R` be a set and `N ≤ M` be a submodule, then `s • N` is the smallest submodule containing
all `r • n` where `r ∈ s` and `n ∈ N`.
-/
@[instance_reducible]
/-
**Submodule.pointwiseSetSMul** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：{R : Type u_2} →   {M : Type u_3} →     [inst : Semiring R] →       [inst_
1 : AddCommMonoid M] →         [inst_2 : _root_.Module R M] →           {S : Typ
e u_4} → [inst_3 : Monoid S] → [DistribMulAction S M] → SMul (Set S) (Submodule 
R M)
参数：Set S；Submodule R M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `s ⊆ R` be a set and `N ≤ M` be a submodule, then `s • N` is the smallest su
bmodule containing
all `r • n` where `r ∈ s` and `n ∈ N`.
-/
protected def pointwiseSetSMul : SMul (Set S) (Submodule R M) where
  smul s N := sInf { p | ∀ ⦃r : S⦄ ⦃n : M⦄, r ∈ s → n ∈ N → r • n ∈ p }

scoped[Pointwise] attribute [instance] Submodule.pointwiseSetSMul

variable (sR : Set R) (s : Set S) (N : Submodule R M)
/-
**Submodule.mem_set_smul_def** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：mem_set_smul_def (x : M) : x in s • N ↔ x in sInf { p : Submodule R M | fo
rall ⦃r : S⦄ {n : M}, r in s -> n in N -> r • n in p }
参数：x : M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_set_smul_def (x : M) :
    x ∈ s • N ↔
    x ∈ sInf { p : Submodule R M | ∀ ⦃r : S⦄ {n : M}, r ∈ s → n ∈ N → r • n ∈ p } := Iff.rfl

variable {s N} in
@[aesop safe]
/-
**Submodule.mem_set_smul_of_mem_mem** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：mem_set_smul_of_mem_mem {r : S} {m : M} (mem1 : r in s) (mem2 : m in N) : 
r • m in s • N
参数：mem1 : r in s；mem2 : m in N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Submodule.mem_set_smul_def`：mem_set_smul_def (x : M) : x in s • N ↔ x in
 sInf { p : Submodule R M | forall ⦃r : S⦄ {n : M}, r in s -> n in N -> r • n in
 p }
· 使用定理 `Submodule.mem_sInf`：mem_sInf {S : Set (Submodule R M)} {x : M} : x in sI
nf S ↔ forall p in S, x in p
-/
lemma mem_set_smul_of_mem_mem {r : S} {m : M} (mem1 : r ∈ s) (mem2 : m ∈ N) :
    r • m ∈ s • N := by
  rw [mem_set_smul_def, mem_sInf]
  exact fun _ h => h mem1 mem2
/-
**Submodule.set_smul_le** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：set_smul_le (p : Submodule R M) (closed_under_smul : forall ⦃r : S⦄ ⦃n : M
⦄, r in s -> n in N -> r • n in p) : s • N <= p
参数：p : Submodule R M；closed_under_smul : forall ⦃r : S⦄ ⦃n : M⦄, r in s -> n in 
N -> r • n in p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sInf_le`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, a ∈ s → sInf s ≤ a
-/
lemma set_smul_le (p : Submodule R M)
    (closed_under_smul : ∀ ⦃r : S⦄ ⦃n : M⦄, r ∈ s → n ∈ N → r • n ∈ p) :
    s • N ≤ p :=
  sInf_le closed_under_smul
/-
**Submodule.set_smul_le_iff** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：set_smul_le_iff (p : Submodule R M) : s • N <= p ↔ forall ⦃r : S⦄ ⦃n : M⦄,
 r in s -> n in N -> r • n in p
参数：p : Submodule R M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Submodule.mem_set_smul_of_mem_mem`：mem_set_smul_of_mem_mem {r : S} {m : 
M} (mem1 : r in s) (mem2 : m in N) : r • m in s • N
· 使用引理 `Submodule.set_smul_le`：set_smul_le (p : Submodule R M) (closed_under_smu
l : forall ⦃r : S⦄ ⦃n : M⦄, r in s -> n in N -> r • n in p) : s • N <= p
-/
lemma set_smul_le_iff (p : Submodule R M) :
    s • N ≤ p ↔
    ∀ ⦃r : S⦄ ⦃n : M⦄, r ∈ s → n ∈ N → r • n ∈ p := by
  fconstructor
  · intro h r n hr hn
    exact h <| mem_set_smul_of_mem_mem hr hn
  · apply set_smul_le
/-
**Submodule.set_smul_eq_of_le** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：set_smul_eq_of_le (p : Submodule R M) (closed_under_smul : forall ⦃r : S⦄ 
⦃n : M⦄, r in s -> n in N -> r • n in p) (le : p <= s • N) : s • N = p
参数：p : Submodule R M；closed_under_smul : forall ⦃r : S⦄ ⦃n : M⦄, r in s -> n in 
N -> r • n in p；le : p <= s • N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `Submodule.set_smul_le`：set_smul_le (p : Submodule R M) (closed_under_smu
l : forall ⦃r : S⦄ ⦃n : M⦄, r in s -> n in N -> r • n in p) : s • N <= p
-/
lemma set_smul_eq_of_le (p : Submodule R M)
    (closed_under_smul : ∀ ⦃r : S⦄ ⦃n : M⦄, r ∈ s → n ∈ N → r • n ∈ p)
    (le : p ≤ s • N) :
    s • N = p :=
  le_antisymm (set_smul_le s N p closed_under_smul) le
/-
**Submodule.** 是 Mathlib 中的一个实例，位于命名空间 `Submodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CovariantClass (Set S) (Submodule R M) HSMul.hSMul LE.le :=
  ⟨fun _ _ _ le => set_smul_le _ _ _ fun _ _ hr hm => mem_set_smul_of_mem_mem (mem1 := hr)
    (mem2 := le hm)⟩
/-
**Submodule.set_smul_mono_left** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：set_smul_mono_left {s t : Set S} (le : s <= t) : s • N <= t • N
参数：le : s <= t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Submodule.set_smul_le`：set_smul_le (p : Submodule R M) (closed_under_smu
l : forall ⦃r : S⦄ ⦃n : M⦄, r in s -> n in N -> r • n in p) : s • N <= p
· 使用引理 `Submodule.mem_set_smul_of_mem_mem`：mem_set_smul_of_mem_mem {r : S} {m : 
M} (mem1 : r in s) (mem2 : m in N) : r • m in s • N
-/
lemma set_smul_mono_left {s t : Set S} (le : s ≤ t) :
    s • N ≤ t • N :=
  set_smul_le _ _ _ fun _ _ hr hm => mem_set_smul_of_mem_mem (mem1 := le hr)
    (mem2 := hm)
/-
**Submodule.set_smul_le_of_le_le** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：set_smul_le_of_le_le {s t : Set S} {p q : Submodule R M} (le_set : s <= t)
 (le_submodule : p <= q) : s • p <= t • q
参数：le_set : s <= t；le_submodule : p <= q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用引理 `Submodule.set_smul_mono_left`：set_smul_mono_left {s t : Set S} (le : s <
= t) : s • N <= t • N
· 使用定理 `smul_mono_right`：smul_mono_right [SMul M α] [Preorder α] [CovariantClass
 M α HSMul.hSMul LE.le] (m : M) : Monotone (HSMul.hSMul m : α -> α)
· 使用定理 `Submodule.instCovariantClassSetHSMulLe`：∀ {R : Type u_2} {M : Type u_3} 
[inst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {S
 : Type u_4} [inst_3 : Monoi…
-/
lemma set_smul_le_of_le_le {s t : Set S} {p q : Submodule R M}
    (le_set : s ≤ t) (le_submodule : p ≤ q) : s • p ≤ t • q :=
  le_trans (set_smul_mono_left _ le_set) <| smul_mono_right _ le_submodule
/-
**Submodule.set_smul_eq_iSup** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：set_smul_eq_iSup [SMulCommClass S R M] (s : Set S) (N : Submodule R M) : s
 • N = ⨆ (a in s), a • N
参数：s : Set S；N : Submodule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Submodule.map_le_iff_le_comap`：map_le_iff_le_comap {f : M ->ₛₗ[σ₁₂] M₂} 
{p : Submodule R M} {q : Submodule R₂ M₂} : map f p <= q ↔ p <= comap f q
· 使用定理 `csInf_Ici`：csInf_Ici {α : Type*} [ConditionallyCompletePartialOrderInf α
] {a : α} : sInf (Ici a) = a
-/
lemma set_smul_eq_iSup [SMulCommClass S R M] (s : Set S) (N : Submodule R M) :
    s • N = ⨆ (a ∈ s), a • N := by
  refine Eq.trans (congrArg sInf ?_) csInf_Ici
  simp_rw [← Set.Ici_def, iSup_le_iff, @forall_comm M]
  exact Set.ext fun _ => forall₂_congr (fun _ _ => Iff.symm map_le_iff_le_comap)

variable {s N} in
/--
Induction principle for set acting on submodules. To prove `P` holds for all `s • N`, it is enough
to prove:
- for all `r ∈ s` and `n ∈ N`, `P (r • n)`;
- for all `r` and `m ∈ s • N`, `P (r • n)`;
- for all `m₁, m₂`, `P m₁` and `P m₂` implies `P (m₁ + m₂)`;
- `P 0`.

To invoke this induction principle, use `induction x, hx using Submodule.set_smul_inductionOn` where
`x : M` and `hx : x ∈ s • N`
-/
@[elab_as_elim]
/-
**Submodule.set_smul_inductionOn** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：set_smul_inductionOn {motive : (x : M) -> (_ : x in s • N) -> Prop} (x : M
) (hx : x in s • N) (smul₀ : forall ⦃r : S⦄ ⦃n : M⦄ (mem₁ : r in s) (mem₂ : n in
 N), motive (r • n) (mem_set_smul_of_mem_mem mem₁ mem₂)) (smul₁ : forall (r : R)
 ⦃m : M⦄ (mem : m in s • N), motive m mem -> motive (r • m) (Submodule.smul_mem 
_ r mem)) -- (add : forall ⦃m₁ m₂ : M⦄ (mem₁ : m₁ in s • N) (mem₂ : m₂ in s • N)
, motive m₁ mem₁ -> motive m₂ mem₂ -> motive (m₁ + m₂) (Submodule.add_mem _ mem₁
 mem₂)) (zero : motive 0 (
参数：x : M；_ : x in s • N；x : M；hx : x in s • N；smul₀ : forall ⦃r : S⦄ ⦃n : M⦄ (me
m₁ : r in s) (mem₂ : n in N), motive (r • n) (mem_set_smul_of_mem_mem mem₁ mem₂)
；smul₁ : forall (r : R) ⦃m : M⦄ (mem : m in s • N), motive m mem -> motive (r • 
m) (Submodule.smul_mem _ r mem)；add : forall ⦃m₁ m₂ : M⦄ (mem₁ : m₁ in s • N) (m
em₂ : m₂ in s • N), motive m₁ mem₁ -> motive m₂ mem₂ -> motive (m₁ + m₂) (Submod
ule.add_mem _ mem₁ mem₂)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Submodule.mem_set_smul_of_mem_mem`：mem_set_smul_of_mem_mem {r : S} {m : 
M} (mem1 : r in s) (mem2 : m in N) : r • m in s • N
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用定理 `Submodule.add_mem`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [inst
_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodule R M) {x y 
: M}, x…
· 使用定理 `Submodule.zero_mem`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [ins
t_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodule R M), 0 ∈
 p
· 使用引理 `Submodule.set_smul_le`：set_smul_le (p : Submodule R M) (closed_under_smu
l : forall ⦃r : S⦄ ⦃n : M⦄, r in s -> n in N -> r • n in p) : s • N <= p

--- 原说明 ---
Induction principle for set acting on submodules. To prove `P` holds for all `s 
• N`, it is enough
to prove:
- for all `r ∈ s` and `n ∈ N`, `P (r • n)`;
- for all `r` and `m ∈ s • N`, `P (r • n)`;
- for all `m₁, m₂`, `P m₁` and `P m₂` implies `P (m₁ + m₂)`;
- `P 0`.

To invoke this induction principle, use `induction x, hx using Submodule.set_smu
l_inductionOn` where
`x : M` and `hx : x ∈ s • N`
-/
lemma set_smul_inductionOn {motive : (x : M) → (_ : x ∈ s • N) → Prop}
    (x : M)
    (hx : x ∈ s • N)
    (smul₀ : ∀ ⦃r : S⦄ ⦃n : M⦄ (mem₁ : r ∈ s) (mem₂ : n ∈ N),
      motive (r • n) (mem_set_smul_of_mem_mem mem₁ mem₂))
    (smul₁ : ∀ (r : R) ⦃m : M⦄ (mem : m ∈ s • N),
      motive m mem → motive (r • m) (Submodule.smul_mem _ r mem)) --
    (add : ∀ ⦃m₁ m₂ : M⦄ (mem₁ : m₁ ∈ s • N) (mem₂ : m₂ ∈ s • N),
      motive m₁ mem₁ → motive m₂ mem₂ → motive (m₁ + m₂) (Submodule.add_mem _ mem₁ mem₂))
    (zero : motive 0 (Submodule.zero_mem _)) :
    motive x hx :=
  let ⟨_, h⟩ := set_smul_le s N
    { carrier := { m | ∃ (mem : m ∈ s • N), motive m mem },
      zero_mem' := ⟨Submodule.zero_mem _, zero⟩
      add_mem' := fun ⟨mem, h⟩ ⟨mem', h'⟩ ↦ ⟨_, add mem mem' h h'⟩
      smul_mem' := fun r _ ⟨mem, h⟩ ↦ ⟨_, smul₁ r mem h⟩ }
    (fun _ _ mem mem' ↦ ⟨mem_set_smul_of_mem_mem mem mem', smul₀ mem mem'⟩) hx
  h
/-
**Submodule.empty_set_smul** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：∀ {R : Type u_2} {M : Type u_3} [inst : Semiring R] [inst_1 : AddCommMonoi
d M] [inst_2 : _root_.Module R M]   {S : Type u_4} [inst_3 : Monoid S] [inst_4 :
 DistribMulAction S M] (N : Submodule R M), ∅ • N = ⊥
参数：N : Submodule R M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.mem_sInf`：mem_sInf {S : Set (Submodule R M)} {x : M} : x in sI
nf S ↔ forall p in S, x in p
· 使用引理 `Submodule.mem_set_smul_def`：mem_set_smul_def (x : M) : x in s • N ↔ x in
 sInf { p : Submodule R M | forall ⦃r : S⦄ {n : M}, r in s -> n in N -> r • n in
 p }
· 使用定理 `Submodule.zero_mem`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [ins
t_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodule R M), 0 ∈
 p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
@[simp] lemma empty_set_smul : (∅ : Set S) • N = ⊥ := by
  ext
  fconstructor
  · intro hx
    rw [mem_set_smul_def, Submodule.mem_sInf] at hx
    exact hx ⊥ (fun r _ hr ↦ hr.elim)
  · rintro rfl; exact Submodule.zero_mem _
/-
**Submodule.set_smul_bot** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：∀ {R : Type u_2} {M : Type u_3} [inst : Semiring R] [inst_1 : AddCommMonoi
d M] [inst_2 : _root_.Module R M]   {S : Type u_4} [inst_3 : Monoid S] [inst_4 :
 DistribMulAction S M] (s : Set S), s • ⊥ = ⊥
参数：s : Set S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用引理 `Submodule.set_smul_inductionOn`：set_smul_inductionOn {motive : (x : M) -
> (_ : x in s • N) -> Prop} (x : M) (hx : x in s • N) (smul₀ : forall ⦃r : S⦄ ⦃n
 : M⦄ (mem₁ : r in s…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
@[simp] lemma set_smul_bot : s • (⊥ : Submodule R M) = ⊥ :=
  eq_bot_iff.mpr fun x hx ↦ by induction x, hx using set_smul_inductionOn <;> aesop
/-
**Submodule.singleton_set_smul** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：singleton_set_smul [SMulCommClass S R M] (r : S) : ({r} : Set S) • N = r •
 N
参数：r : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Submodule.set_smul_eq_of_le`：set_smul_eq_of_le (p : Submodule R M) (clos
ed_under_smul : forall ⦃r : S⦄ ⦃n : M⦄, r in s -> n in N -> r • n in p) (le : p 
<= s • N) : s • N…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Submodule.mem_set_smul_def`：mem_set_smul_def (x : M) : x in s • N ↔ x in
 sInf { p : Submodule R M | forall ⦃r : S⦄ {n : M}, r in s -> n in N -> r • n in
 p }
· 使用定理 `Submodule.mem_sInf`：mem_sInf {S : Set (Submodule R M)} {x : M} : x in sI
nf S ↔ forall p in S, x in p
-/
lemma singleton_set_smul [SMulCommClass S R M] (r : S) : ({r} : Set S) • N = r • N := by
  apply set_smul_eq_of_le
  · rintro _ m rfl hm; exact ⟨m, hm, rfl⟩
  · rintro _ ⟨m, hm, rfl⟩
    rw [mem_set_smul_def, Submodule.mem_sInf]
    intro _ hp; exact hp rfl hm
/-
**Submodule.mem_singleton_set_smul** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：mem_singleton_set_smul [SMulCommClass R S M] (r : S) (x : M) : x in ({r} :
 Set S) • N ↔ exists (m : M), m in N ∧ x = r • m
参数：r : S；x : M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Submodule.set_smul_inductionOn`：set_smul_inductionOn {motive : (x : M) -
> (_ : x in s • N) -> Prop} (x : M) (hx : x in s • N) (smul₀ : forall ⦃r : S⦄ ⦃n
 : M⦄ (mem₁ : r in s…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SMulMemClass.smul_mem`：∀ {S : Type u_1} {R : outParam (Type u_2)} {M : T
ype u_3} {inst : SMul R M} {inst_1 : SetLike S M}   [self : SMulMemClass S R M] 
{s : S} (r …
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.add_mem`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [inst
_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodule R M) {x y 
: M}, x…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Submodule.zero_mem`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [ins
t_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodule R M), 0 ∈
 p
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用引理 `Submodule.mem_set_smul_of_mem_mem`：mem_set_smul_of_mem_mem {r : S} {m : 
M} (mem1 : r in s) (mem2 : m in N) : r • m in s • N
-/
lemma mem_singleton_set_smul [SMulCommClass R S M] (r : S) (x : M) :
    x ∈ ({r} : Set S) • N ↔ ∃ (m : M), m ∈ N ∧ x = r • m := by
  fconstructor
  · intro hx
    induction x, hx using Submodule.set_smul_inductionOn with
    | smul₀ => aesop
    | @smul₁ t n mem h =>
      rcases h with ⟨n, hn, rfl⟩
      exact ⟨t • n, by aesop, smul_comm _ _ _⟩
    | add mem₁ mem₂ h₁ h₂ =>
      rcases h₁ with ⟨m₁, h₁, rfl⟩
      rcases h₂ with ⟨m₂, h₂, rfl⟩
      exact ⟨m₁ + m₂, Submodule.add_mem _ h₁ h₂, by simp⟩
    | zero => exact ⟨0, Submodule.zero_mem _, by simp⟩
  · aesop
/-
**Submodule.smul_inductionOn_pointwise** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：smul_inductionOn_pointwise [SMulCommClass S R M] {a : S} {p : (x : M) -> x
 in a • N -> Prop} (smul₀ : forall (s : M) (hs : s in N), p (a • s) (Submodule.s
mul_mem_pointwise_smul _ _ _ hs)) (smul₁ : forall (r : R) (m : M) (mem : m in a 
• N), p m mem -> p (r • m) (Submodule.smul_mem _ _ mem)) (add : forall (x y : M)
 (hx : x in a • N) (hy : y in a • N), p x hx -> p y hy -> p (x + y) (Submodule.a
dd_mem _ hx hy)) (zero : p 0 (Submodule.zero_mem _)) {x : M} (hx : x in a • N) :
 p x hx
参数：x : M；smul₀ : forall (s : M) (hs : s in N), p (a • s) (Submodule.smul_mem_poi
ntwise_smul _ _ _ hs)；smul₁ : forall (r : R) (m : M) (mem : m in a • N), p m mem
 -> p (r • m) (Submodule.smul_mem _ _ mem)；add : forall (x y : M) (hx : x in a •
 N) (hy : y in a • N), p x hx -> p y hy -> p (x + y) (Submodule.add_mem _ hx hy)
；zero : p 0 (Submodule.zero_mem _)；hx : x in a • N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.smul_mem_pointwise_smul`：smul_mem_pointwise_smul (m : M) (a : 
α) (S : Submodule R M) : m in S -> a • m in a • S
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用定理 `Submodule.add_mem`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [inst
_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodule R M) {x y 
: M}, x…
· 使用定理 `Submodule.zero_mem`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [ins
t_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodule R M), 0 ∈
 p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Submodule.singleton_set_smul`：singleton_set_smul [SMulCommClass S R M] (
r : S) : ({r} : Set S) • N = r • N
· 使用引理 `Submodule.set_smul_inductionOn`：set_smul_inductionOn {motive : (x : M) -
> (_ : x in s • N) -> Prop} (x : M) (hx : x in s • N) (smul₀ : forall ⦃r : S⦄ ⦃n
 : M⦄ (mem₁ : r in s…
· 使用定理 `Eq.substr`：∀ {α : Sort u} {p : α → Prop} {a b : α}, b = a → p a → p b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Submodule.mem_set_smul_of_mem_mem`：mem_set_smul_of_mem_mem {r : S} {m : 
M} (mem1 : r in s) (mem2 : m in N) : r • m in s • N
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
-/
lemma smul_inductionOn_pointwise [SMulCommClass S R M] {a : S} {p : (x : M) → x ∈ a • N → Prop}
    (smul₀ : ∀ (s : M) (hs : s ∈ N), p (a • s) (Submodule.smul_mem_pointwise_smul _ _ _ hs))
    (smul₁ : ∀ (r : R) (m : M) (mem : m ∈ a • N), p m mem → p (r • m) (Submodule.smul_mem _ _ mem))
    (add : ∀ (x y : M) (hx : x ∈ a • N) (hy : y ∈ a • N),
      p x hx → p y hy → p (x + y) (Submodule.add_mem _ hx hy))
    (zero : p 0 (Submodule.zero_mem _)) {x : M} (hx : x ∈ a • N) :
    p x hx := by
  simp_all only [← Submodule.singleton_set_smul]
  let p' (x : M) (hx : x ∈ ({a} : Set S) • N) : Prop :=
    p x (by rwa [← Submodule.singleton_set_smul])
  refine Submodule.set_smul_inductionOn (motive := p') _ (N.singleton_set_smul a ▸ hx)
      (fun r n hr hn ↦ ?_) smul₁ add zero
  · push _ ∈ _ at hr
    subst hr
    exact smul₀ n hn
/-
**Submodule.sup_set_smul** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：sup_set_smul (s t : Set S) : (s ⊔ t) • N = s • N ⊔ t • N
参数：s t : Set S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Submodule.set_smul_eq_of_le`：set_smul_eq_of_le (p : Submodule R M) (clos
ed_under_smul : forall ⦃r : S⦄ ⦃n : M⦄, r in s -> n in N -> r • n in p) (le : p 
<= s • N) : s • N…
· 使用定理 `Submodule.mem_sup_left`：mem_sup_left {S T : Submodule R M} : forall {x :
 M}, x in S -> x in S ⊔ T
· 使用引理 `Submodule.mem_set_smul_of_mem_mem`：mem_set_smul_of_mem_mem {r : S} {m : 
M} (mem1 : r in s) (mem2 : m in N) : r • m in s • N
· 使用定理 `Submodule.mem_sup_right`：mem_sup_right {S T : Submodule R M} : forall {x
 : M}, x in T -> x in S ⊔ T
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用引理 `Submodule.set_smul_mono_left`：set_smul_mono_left {s t : Set S} (le : s <
= t) : s • N <= t • N
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
-/
lemma sup_set_smul (s t : Set S) :
    (s ⊔ t) • N = s • N ⊔ t • N :=
  set_smul_eq_of_le _ _ _
    (by rintro _ _ (hr | hr) hn
        · exact Submodule.mem_sup_left (mem_set_smul_of_mem_mem hr hn)
        · exact Submodule.mem_sup_right (mem_set_smul_of_mem_mem hr hn))
    (sup_le (set_smul_mono_left _ le_sup_left) (set_smul_mono_left _ le_sup_right))

end DistribMulAction

section Group

variable {R G M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [Group G] [DistribMulAction G M] [SMulCommClass G R M]
    {S : Submodule R M}

open MulAction

/-
**Submodule.stabilizer_coe** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：stabilizer_coe : stabilizer G S = stabilizer G (S : Set M)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.ext`：ext {H K : Subgroup G} (h : forall x, x in H ↔ x in K) : H
 = K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulAction.mem_stabilizer_iff`：mem_stabilizer_iff {a : α} {g : G} : g in 
stabilizer G a ↔ g • a = a
· 使用定理 `SetLike.ext'_iff`：∀ {A : Type u_1} {B : Type u_2} [i : SetLike A B] {p q
 : A}, p = q ↔ ↑p = ↑q
· 使用定理 `Submodule.coe_pointwise_smul`：coe_pointwise_smul (a : α) (S : Submodule 
R M) : ↑(a • S) = a • (S : Set M)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma stabilizer_coe :
    stabilizer G S = stabilizer G (S : Set M) := by
  ext
  rw [mem_stabilizer_iff, SetLike.ext'_iff, coe_pointwise_smul,
    ← mem_stabilizer_iff]
/-
**Submodule.mem_stabilizer_submodule_iff_map_eq** 是 Mathlib 中的一个定理，位于命名空间 `Submo
dule`。
形式化陈述：mem_stabilizer_submodule_iff_map_eq {e : G} : e in stabilizer G S ↔ S.map 
(DistribSMul.toLinearMap R M e) = S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_stabilizer_submodule_iff_map_eq {e : G} :
    e ∈ stabilizer G S ↔ S.map (DistribSMul.toLinearMap R M e) = S := by
  rfl

end Group

end Submodule

