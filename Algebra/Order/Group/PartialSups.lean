/-
Copyright (c) 2025 Lua Viana Reis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lua Viana Reis
-/
module

public import Mathlib.Algebra.Order.Group.OrderIso
public import Mathlib.Order.PartialSups

/-!
# Results about `partialSups` of functions taking values in a `Group`
-/

public section

variable {α ι : Type*}

variable [SemilatticeSup α] [Group α] [Preorder ι] [LocallyFiniteOrderBot ι]

@[to_additive]
/-
**partialSups_const_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：partialSups_const_mul [MulLeftMono α] (f : ι -> α) (c : α) (i : ι) : parti
alSups (c * f ·) i = c * partialSups f i
参数：f : ι -> α；c : α；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `map_partialSups`：map_partialSups {F : Type*} [FunLike F α β] [SupHomClas
s F α β] (f : F) (g : ι -> α) (i : ι) : partialSups (fun j => f (g j)) i = f (pa
rtial…
· 使用定理 `OrderIsoClass.toSupHomClass`：∀ {F : Type u_1} {α : Type u_2} {β : Type u
_3} [inst : EquivLike F α β] [inst_1 : SemilatticeSup α]   [inst_2 : Semilattice
Sup β] [OrderIsoC…
· 使用定理 `OrderIso.instOrderIsoClass`：∀ {α : Type u_2} {β : Type u_3} [inst : LE α
] [inst_1 : LE β], OrderIsoClass (α ≃o β) α β
-/
lemma partialSups_const_mul [MulLeftMono α] (f : ι → α) (c : α) (i : ι) :
    partialSups (c * f ·) i = c * partialSups f i := map_partialSups (OrderIso.mulLeft _) ..

@[to_additive]
/-
**partialSups_mul_const** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：partialSups_mul_const [MulRightMono α] (f : ι -> α) (c : α) (i : ι) : part
ialSups (f · * c) i = partialSups f i * c
参数：f : ι -> α；c : α；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `map_partialSups`：map_partialSups {F : Type*} [FunLike F α β] [SupHomClas
s F α β] (f : F) (g : ι -> α) (i : ι) : partialSups (fun j => f (g j)) i = f (pa
rtial…
· 使用定理 `OrderIsoClass.toSupHomClass`：∀ {F : Type u_1} {α : Type u_2} {β : Type u
_3} [inst : EquivLike F α β] [inst_1 : SemilatticeSup α]   [inst_2 : Semilattice
Sup β] [OrderIsoC…
· 使用定理 `OrderIso.instOrderIsoClass`：∀ {α : Type u_2} {β : Type u_3} [inst : LE α
] [inst_1 : LE β], OrderIsoClass (α ≃o β) α β
-/
lemma partialSups_mul_const [MulRightMono α] (f : ι → α) (c : α) (i : ι) :
    partialSups (f · * c) i = partialSups f i * c := map_partialSups (OrderIso.mulRight _) ..
