/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Embedding
public import Mathlib.Algebra.Order.Interval.Set.Monoid
public import Mathlib.Order.Interval.Finset.Defs

/-!
# Algebraic properties of finset intervals

This file provides results about the interaction of algebra with `Finset.Ixx`.
-/

public section

open Function OrderDual

variable {ι α : Type*}

namespace Finset
variable [AddCommMonoid α] [PartialOrder α] [IsOrderedCancelAddMonoid α]
  [ExistsAddOfLE α] [LocallyFiniteOrder α]

/-
**Finset.map_add_left_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : AddCommMonoid α] [inst_1 : PartialOrder α] [inst_
2 : IsOrderedCancelAddMonoid α]   [ExistsAddOfLE α] [inst_4 : LocallyFiniteOrder
 α] (a b c : α),   Finset.map (addLeftEmbedding c) (Finset.Icc a b) = Finset.Icc
 (c + a) (c + b)
参数：a b c : α；addLeftEmbedding c；Finset.Icc a b；c + a；c + b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.coe_inj`：coe_inj {s₁ s₂ : Finset α} : (s₁ : Set α) = s₂ ↔ s₁ = s₂
· 使用定理 `Finset.coe_map`：coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) =
 f '' s
· 使用定理 `Finset.coe_Icc`：coe_Icc (a b : α) : (Icc a b : Set α) = Set.Icc a b
· 使用定理 `Set.image_const_add_Icc`：image_const_add_Icc : (fun x => a + x) '' Icc b
 c = Icc (a + b) (a + c)
-/
@[simp] lemma map_add_left_Icc (a b c : α) :
    (Icc a b).map (addLeftEmbedding c) = Icc (c + a) (c + b) := by
  rw [← coe_inj, coe_map, coe_Icc, coe_Icc]
  exact Set.image_const_add_Icc _ _ _
/-
**Finset.map_add_right_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : AddCommMonoid α] [inst_1 : PartialOrder α] [inst_
2 : IsOrderedCancelAddMonoid α]   [ExistsAddOfLE α] [inst_4 : LocallyFiniteOrder
 α] (a b c : α),   Finset.map (addRightEmbedding c) (Finset.Icc a b) = Finset.Ic
c (a + c) (b + c)
参数：a b c : α；addRightEmbedding c；Finset.Icc a b；a + c；b + c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `IsCancelAdd.toIsLeftCancelAdd`：∀ {G : Type u} {inst : Add G} [self : IsC
ancelAdd G], IsLeftCancelAdd G
· 使用定理 `IsOrderedCancelAddMonoid.toIsCancelAdd`：∀ {α : Type u_1} [inst : AddComm
Monoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], IsCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLT`：∀ {α : Type u_1} [inst : Ad
dCommMonoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], AddLeftRe
flectLT α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.coe_inj`：coe_inj {s₁ s₂ : Finset α} : (s₁ : Set α) = s₂ ↔ s₁ = s₂
· 使用定理 `Finset.coe_map`：coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) =
 f '' s
· 使用定理 `Finset.coe_Icc`：coe_Icc (a b : α) : (Icc a b : Set α) = Set.Icc a b
· 使用定理 `Set.image_add_const_Icc`：image_add_const_Icc : (fun x => x + a) '' Icc b
 c = Icc (b + a) (c + a)
-/
@[simp] lemma map_add_right_Icc (a b c : α) :
    (Icc a b).map (addRightEmbedding c) = Icc (a + c) (b + c) := by
  rw [← coe_inj, coe_map, coe_Icc, coe_Icc]
  exact Set.image_add_const_Icc _ _ _
/-
**Finset.map_add_left_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : AddCommMonoid α] [inst_1 : PartialOrder α] [inst_
2 : IsOrderedCancelAddMonoid α]   [ExistsAddOfLE α] [inst_4 : LocallyFiniteOrder
 α] (a b c : α),   Finset.map (addLeftEmbedding c) (Finset.Ico a b) = Finset.Ico
 (c + a) (c + b)
参数：a b c : α；addLeftEmbedding c；Finset.Ico a b；c + a；c + b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.coe_inj`：coe_inj {s₁ s₂ : Finset α} : (s₁ : Set α) = s₂ ↔ s₁ = s₂
· 使用定理 `Finset.coe_map`：coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) =
 f '' s
· 使用定理 `Finset.coe_Ico`：coe_Ico (a b : α) : (Ico a b : Set α) = Set.Ico a b
· 使用定理 `Set.image_const_add_Ico`：image_const_add_Ico : (fun x => a + x) '' Ico b
 c = Ico (a + b) (a + c)
-/
@[simp] lemma map_add_left_Ico (a b c : α) :
    (Ico a b).map (addLeftEmbedding c) = Ico (c + a) (c + b) := by
  rw [← coe_inj, coe_map, coe_Ico, coe_Ico]
  exact Set.image_const_add_Ico _ _ _
/-
**Finset.map_add_right_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : AddCommMonoid α] [inst_1 : PartialOrder α] [inst_
2 : IsOrderedCancelAddMonoid α]   [ExistsAddOfLE α] [inst_4 : LocallyFiniteOrder
 α] (a b c : α),   Finset.map (addRightEmbedding c) (Finset.Ico a b) = Finset.Ic
o (a + c) (b + c)
参数：a b c : α；addRightEmbedding c；Finset.Ico a b；a + c；b + c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `IsCancelAdd.toIsLeftCancelAdd`：∀ {G : Type u} {inst : Add G} [self : IsC
ancelAdd G], IsLeftCancelAdd G
· 使用定理 `IsOrderedCancelAddMonoid.toIsCancelAdd`：∀ {α : Type u_1} [inst : AddComm
Monoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], IsCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLT`：∀ {α : Type u_1} [inst : Ad
dCommMonoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], AddLeftRe
flectLT α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.coe_inj`：coe_inj {s₁ s₂ : Finset α} : (s₁ : Set α) = s₂ ↔ s₁ = s₂
· 使用定理 `Finset.coe_map`：coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) =
 f '' s
· 使用定理 `Finset.coe_Ico`：coe_Ico (a b : α) : (Ico a b : Set α) = Set.Ico a b
· 使用定理 `Set.image_add_const_Ico`：image_add_const_Ico : (fun x => x + a) '' Ico b
 c = Ico (b + a) (c + a)
-/
@[simp] lemma map_add_right_Ico (a b c : α) :
    (Ico a b).map (addRightEmbedding c) = Ico (a + c) (b + c) := by
  rw [← coe_inj, coe_map, coe_Ico, coe_Ico]
  exact Set.image_add_const_Ico _ _ _
/-
**Finset.map_add_left_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : AddCommMonoid α] [inst_1 : PartialOrder α] [inst_
2 : IsOrderedCancelAddMonoid α]   [ExistsAddOfLE α] [inst_4 : LocallyFiniteOrder
 α] (a b c : α),   Finset.map (addLeftEmbedding c) (Finset.Ioc a b) = Finset.Ioc
 (c + a) (c + b)
参数：a b c : α；addLeftEmbedding c；Finset.Ioc a b；c + a；c + b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.coe_inj`：coe_inj {s₁ s₂ : Finset α} : (s₁ : Set α) = s₂ ↔ s₁ = s₂
· 使用定理 `Finset.coe_map`：coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) =
 f '' s
· 使用定理 `Finset.coe_Ioc`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrder α] (b a : α), ↑(Finset.Ioc b a) = Set.Ioc b a
· 使用定理 `Set.image_const_add_Ioc`：image_const_add_Ioc : (fun x => a + x) '' Ioc b
 c = Ioc (a + b) (a + c)
-/
@[simp] lemma map_add_left_Ioc (a b c : α) :
    (Ioc a b).map (addLeftEmbedding c) = Ioc (c + a) (c + b) := by
  rw [← coe_inj, coe_map, coe_Ioc, coe_Ioc]
  exact Set.image_const_add_Ioc _ _ _
/-
**Finset.map_add_right_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : AddCommMonoid α] [inst_1 : PartialOrder α] [inst_
2 : IsOrderedCancelAddMonoid α]   [ExistsAddOfLE α] [inst_4 : LocallyFiniteOrder
 α] (a b c : α),   Finset.map (addRightEmbedding c) (Finset.Ioc a b) = Finset.Io
c (a + c) (b + c)
参数：a b c : α；addRightEmbedding c；Finset.Ioc a b；a + c；b + c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `IsCancelAdd.toIsLeftCancelAdd`：∀ {G : Type u} {inst : Add G} [self : IsC
ancelAdd G], IsLeftCancelAdd G
· 使用定理 `IsOrderedCancelAddMonoid.toIsCancelAdd`：∀ {α : Type u_1} [inst : AddComm
Monoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], IsCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLT`：∀ {α : Type u_1} [inst : Ad
dCommMonoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], AddLeftRe
flectLT α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.coe_inj`：coe_inj {s₁ s₂ : Finset α} : (s₁ : Set α) = s₂ ↔ s₁ = s₂
· 使用定理 `Finset.coe_map`：coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) =
 f '' s
· 使用定理 `Finset.coe_Ioc`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrder α] (b a : α), ↑(Finset.Ioc b a) = Set.Ioc b a
· 使用定理 `Set.image_add_const_Ioc`：image_add_const_Ioc : (fun x => x + a) '' Ioc b
 c = Ioc (b + a) (c + a)
-/
@[simp] lemma map_add_right_Ioc (a b c : α) :
    (Ioc a b).map (addRightEmbedding c) = Ioc (a + c) (b + c) := by
  rw [← coe_inj, coe_map, coe_Ioc, coe_Ioc]
  exact Set.image_add_const_Ioc _ _ _
/-
**Finset.map_add_left_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : AddCommMonoid α] [inst_1 : PartialOrder α] [inst_
2 : IsOrderedCancelAddMonoid α]   [ExistsAddOfLE α] [inst_4 : LocallyFiniteOrder
 α] (a b c : α),   Finset.map (addLeftEmbedding c) (Finset.Ioo a b) = Finset.Ioo
 (c + a) (c + b)
参数：a b c : α；addLeftEmbedding c；Finset.Ioo a b；c + a；c + b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.coe_inj`：coe_inj {s₁ s₂ : Finset α} : (s₁ : Set α) = s₂ ↔ s₁ = s₂
· 使用定理 `Finset.coe_map`：coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) =
 f '' s
· 使用定理 `Finset.coe_Ioo`：coe_Ioo (a b : α) : (Ioo a b : Set α) = Set.Ioo a b
· 使用定理 `Set.image_const_add_Ioo`：image_const_add_Ioo : (fun x => a + x) '' Ioo b
 c = Ioo (a + b) (a + c)
-/
@[simp] lemma map_add_left_Ioo (a b c : α) :
    (Ioo a b).map (addLeftEmbedding c) = Ioo (c + a) (c + b) := by
  rw [← coe_inj, coe_map, coe_Ioo, coe_Ioo]
  exact Set.image_const_add_Ioo _ _ _
/-
**Finset.map_add_right_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : AddCommMonoid α] [inst_1 : PartialOrder α] [inst_
2 : IsOrderedCancelAddMonoid α]   [ExistsAddOfLE α] [inst_4 : LocallyFiniteOrder
 α] (a b c : α),   Finset.map (addRightEmbedding c) (Finset.Ioo a b) = Finset.Io
o (a + c) (b + c)
参数：a b c : α；addRightEmbedding c；Finset.Ioo a b；a + c；b + c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `IsCancelAdd.toIsLeftCancelAdd`：∀ {G : Type u} {inst : Add G} [self : IsC
ancelAdd G], IsLeftCancelAdd G
· 使用定理 `IsOrderedCancelAddMonoid.toIsCancelAdd`：∀ {α : Type u_1} [inst : AddComm
Monoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], IsCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLT`：∀ {α : Type u_1} [inst : Ad
dCommMonoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], AddLeftRe
flectLT α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.coe_inj`：coe_inj {s₁ s₂ : Finset α} : (s₁ : Set α) = s₂ ↔ s₁ = s₂
· 使用定理 `Finset.coe_map`：coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) =
 f '' s
· 使用定理 `Finset.coe_Ioo`：coe_Ioo (a b : α) : (Ioo a b : Set α) = Set.Ioo a b
· 使用定理 `Set.image_add_const_Ioo`：image_add_const_Ioo : (fun x => x + a) '' Ioo b
 c = Ioo (b + a) (c + a)
-/
@[simp] lemma map_add_right_Ioo (a b c : α) :
    (Ioo a b).map (addRightEmbedding c) = Ioo (a + c) (b + c) := by
  rw [← coe_inj, coe_map, coe_Ioo, coe_Ioo]
  exact Set.image_add_const_Ioo _ _ _

variable [DecidableEq α]
/-
**Finset.image_add_left_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : AddCommMonoid α] [inst_1 : PartialOrder α] [IsOrd
eredCancelAddMonoid α] [ExistsAddOfLE α]   [inst_4 : LocallyFiniteOrder α] [inst
_5 : DecidableEq α] (a b c : α),   Finset.image (fun x => c + x) (Finset.Icc a b
) = Finset.Icc (c + a) (c + b)
参数：a b c : α；fun x => c + x；Finset.Icc a b；c + a；c + b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.map_add_left_Icc`：∀ {α : Type u_2} [inst : AddCommMonoid α] [inst
_1 : PartialOrder α] [inst_2 : IsOrderedCancelAddMonoid α]   [ExistsAddOfLE α] [
inst_4 : Loca…
· 使用定理 `Finset.map_eq_image`：map_eq_image (f : α ↪ β) (s : Finset α) : s.map f =
 s.image f
· 使用定理 `add_right_injective`：∀ {G : Type u_1} [inst : Add G] [IsLeftCancelAdd G]
 (a : G), Function.Injective fun x => a + x
· 使用定理 `addLeftEmbedding.eq_1`：∀ {G : Type u_1} [inst : Add G] [inst_1 : IsLeftC
ancelAdd G] (g : G),   addLeftEmbedding g = { toFun := fun h => g + h, inj' := ⋯
 }
· 使用定理 `Function.Embedding.coeFn_mk`：coeFn_mk {α β} (f : α -> β) (i) : (@mk _ _ 
f i : α -> β) = f
-/
@[simp] lemma image_add_left_Icc (a b c : α) : (Icc a b).image (c + ·) = Icc (c + a) (c + b) := by
  rw [← map_add_left_Icc, map_eq_image, addLeftEmbedding, Embedding.coeFn_mk]
/-
**Finset.image_add_left_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : AddCommMonoid α] [inst_1 : PartialOrder α] [IsOrd
eredCancelAddMonoid α] [ExistsAddOfLE α]   [inst_4 : LocallyFiniteOrder α] [inst
_5 : DecidableEq α] (a b c : α),   Finset.image (fun x => c + x) (Finset.Ico a b
) = Finset.Ico (c + a) (c + b)
参数：a b c : α；fun x => c + x；Finset.Ico a b；c + a；c + b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.map_add_left_Ico`：∀ {α : Type u_2} [inst : AddCommMonoid α] [inst
_1 : PartialOrder α] [inst_2 : IsOrderedCancelAddMonoid α]   [ExistsAddOfLE α] [
inst_4 : Loca…
· 使用定理 `Finset.map_eq_image`：map_eq_image (f : α ↪ β) (s : Finset α) : s.map f =
 s.image f
· 使用定理 `add_right_injective`：∀ {G : Type u_1} [inst : Add G] [IsLeftCancelAdd G]
 (a : G), Function.Injective fun x => a + x
· 使用定理 `addLeftEmbedding.eq_1`：∀ {G : Type u_1} [inst : Add G] [inst_1 : IsLeftC
ancelAdd G] (g : G),   addLeftEmbedding g = { toFun := fun h => g + h, inj' := ⋯
 }
· 使用定理 `Function.Embedding.coeFn_mk`：coeFn_mk {α β} (f : α -> β) (i) : (@mk _ _ 
f i : α -> β) = f
-/
@[simp] lemma image_add_left_Ico (a b c : α) : (Ico a b).image (c + ·) = Ico (c + a) (c + b) := by
  rw [← map_add_left_Ico, map_eq_image, addLeftEmbedding, Embedding.coeFn_mk]
/-
**Finset.image_add_left_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : AddCommMonoid α] [inst_1 : PartialOrder α] [IsOrd
eredCancelAddMonoid α] [ExistsAddOfLE α]   [inst_4 : LocallyFiniteOrder α] [inst
_5 : DecidableEq α] (a b c : α),   Finset.image (fun x => c + x) (Finset.Ioc a b
) = Finset.Ioc (c + a) (c + b)
参数：a b c : α；fun x => c + x；Finset.Ioc a b；c + a；c + b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.map_add_left_Ioc`：∀ {α : Type u_2} [inst : AddCommMonoid α] [inst
_1 : PartialOrder α] [inst_2 : IsOrderedCancelAddMonoid α]   [ExistsAddOfLE α] [
inst_4 : Loca…
· 使用定理 `Finset.map_eq_image`：map_eq_image (f : α ↪ β) (s : Finset α) : s.map f =
 s.image f
· 使用定理 `add_right_injective`：∀ {G : Type u_1} [inst : Add G] [IsLeftCancelAdd G]
 (a : G), Function.Injective fun x => a + x
· 使用定理 `addLeftEmbedding.eq_1`：∀ {G : Type u_1} [inst : Add G] [inst_1 : IsLeftC
ancelAdd G] (g : G),   addLeftEmbedding g = { toFun := fun h => g + h, inj' := ⋯
 }
· 使用定理 `Function.Embedding.coeFn_mk`：coeFn_mk {α β} (f : α -> β) (i) : (@mk _ _ 
f i : α -> β) = f
-/
@[simp] lemma image_add_left_Ioc (a b c : α) : (Ioc a b).image (c + ·) = Ioc (c + a) (c + b) := by
  rw [← map_add_left_Ioc, map_eq_image, addLeftEmbedding, Embedding.coeFn_mk]
/-
**Finset.image_add_left_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : AddCommMonoid α] [inst_1 : PartialOrder α] [IsOrd
eredCancelAddMonoid α] [ExistsAddOfLE α]   [inst_4 : LocallyFiniteOrder α] [inst
_5 : DecidableEq α] (a b c : α),   Finset.image (fun x => c + x) (Finset.Ioo a b
) = Finset.Ioo (c + a) (c + b)
参数：a b c : α；fun x => c + x；Finset.Ioo a b；c + a；c + b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.map_add_left_Ioo`：∀ {α : Type u_2} [inst : AddCommMonoid α] [inst
_1 : PartialOrder α] [inst_2 : IsOrderedCancelAddMonoid α]   [ExistsAddOfLE α] [
inst_4 : Loca…
· 使用定理 `Finset.map_eq_image`：map_eq_image (f : α ↪ β) (s : Finset α) : s.map f =
 s.image f
· 使用定理 `add_right_injective`：∀ {G : Type u_1} [inst : Add G] [IsLeftCancelAdd G]
 (a : G), Function.Injective fun x => a + x
· 使用定理 `addLeftEmbedding.eq_1`：∀ {G : Type u_1} [inst : Add G] [inst_1 : IsLeftC
ancelAdd G] (g : G),   addLeftEmbedding g = { toFun := fun h => g + h, inj' := ⋯
 }
· 使用定理 `Function.Embedding.coeFn_mk`：coeFn_mk {α β} (f : α -> β) (i) : (@mk _ _ 
f i : α -> β) = f
-/
@[simp] lemma image_add_left_Ioo (a b c : α) : (Ioo a b).image (c + ·) = Ioo (c + a) (c + b) := by
  rw [← map_add_left_Ioo, map_eq_image, addLeftEmbedding, Embedding.coeFn_mk]
/-
**Finset.image_add_right_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : AddCommMonoid α] [inst_1 : PartialOrder α] [IsOrd
eredCancelAddMonoid α] [ExistsAddOfLE α]   [inst_4 : LocallyFiniteOrder α] [inst
_5 : DecidableEq α] (a b c : α),   Finset.image (fun x => x + c) (Finset.Icc a b
) = Finset.Icc (a + c) (b + c)
参数：a b c : α；fun x => x + c；Finset.Icc a b；a + c；b + c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `IsCancelAdd.toIsLeftCancelAdd`：∀ {G : Type u} {inst : Add G} [self : IsC
ancelAdd G], IsLeftCancelAdd G
· 使用定理 `IsOrderedCancelAddMonoid.toIsCancelAdd`：∀ {α : Type u_1} [inst : AddComm
Monoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], IsCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLT`：∀ {α : Type u_1} [inst : Ad
dCommMonoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], AddLeftRe
flectLT α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.map_add_right_Icc`：∀ {α : Type u_2} [inst : AddCommMonoid α] [ins
t_1 : PartialOrder α] [inst_2 : IsOrderedCancelAddMonoid α]   [ExistsAddOfLE α] 
[inst_4 : Loca…
· 使用定理 `Finset.map_eq_image`：map_eq_image (f : α ↪ β) (s : Finset α) : s.map f =
 s.image f
· 使用定理 `add_left_injective`：∀ {G : Type u_1} [inst : Add G] [IsRightCancelAdd G]
 (a : G), Function.Injective fun x => x + a
· 使用定理 `addRightEmbedding.eq_1`：∀ {G : Type u_1} [inst : Add G] [inst_1 : IsRigh
tCancelAdd G] (g : G),   addRightEmbedding g = { toFun := fun h => h + g, inj' :
= ⋯ }
· 使用定理 `Function.Embedding.coeFn_mk`：coeFn_mk {α β} (f : α -> β) (i) : (@mk _ _ 
f i : α -> β) = f
-/
@[simp] lemma image_add_right_Icc (a b c : α) : (Icc a b).image (· + c) = Icc (a + c) (b + c) := by
  rw [← map_add_right_Icc, map_eq_image, addRightEmbedding, Embedding.coeFn_mk]
/-
**Finset.image_add_right_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : AddCommMonoid α] [inst_1 : PartialOrder α] [IsOrd
eredCancelAddMonoid α] [ExistsAddOfLE α]   [inst_4 : LocallyFiniteOrder α] [inst
_5 : DecidableEq α] (a b c : α),   Finset.image (fun x => x + c) (Finset.Ico a b
) = Finset.Ico (a + c) (b + c)
参数：a b c : α；fun x => x + c；Finset.Ico a b；a + c；b + c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `IsCancelAdd.toIsLeftCancelAdd`：∀ {G : Type u} {inst : Add G} [self : IsC
ancelAdd G], IsLeftCancelAdd G
· 使用定理 `IsOrderedCancelAddMonoid.toIsCancelAdd`：∀ {α : Type u_1} [inst : AddComm
Monoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], IsCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLT`：∀ {α : Type u_1} [inst : Ad
dCommMonoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], AddLeftRe
flectLT α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.map_add_right_Ico`：∀ {α : Type u_2} [inst : AddCommMonoid α] [ins
t_1 : PartialOrder α] [inst_2 : IsOrderedCancelAddMonoid α]   [ExistsAddOfLE α] 
[inst_4 : Loca…
· 使用定理 `Finset.map_eq_image`：map_eq_image (f : α ↪ β) (s : Finset α) : s.map f =
 s.image f
· 使用定理 `add_left_injective`：∀ {G : Type u_1} [inst : Add G] [IsRightCancelAdd G]
 (a : G), Function.Injective fun x => x + a
· 使用定理 `addRightEmbedding.eq_1`：∀ {G : Type u_1} [inst : Add G] [inst_1 : IsRigh
tCancelAdd G] (g : G),   addRightEmbedding g = { toFun := fun h => h + g, inj' :
= ⋯ }
· 使用定理 `Function.Embedding.coeFn_mk`：coeFn_mk {α β} (f : α -> β) (i) : (@mk _ _ 
f i : α -> β) = f
-/
@[simp] lemma image_add_right_Ico (a b c : α) : (Ico a b).image (· + c) = Ico (a + c) (b + c) := by
  rw [← map_add_right_Ico, map_eq_image, addRightEmbedding, Embedding.coeFn_mk]
/-
**Finset.image_add_right_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : AddCommMonoid α] [inst_1 : PartialOrder α] [IsOrd
eredCancelAddMonoid α] [ExistsAddOfLE α]   [inst_4 : LocallyFiniteOrder α] [inst
_5 : DecidableEq α] (a b c : α),   Finset.image (fun x => x + c) (Finset.Ioc a b
) = Finset.Ioc (a + c) (b + c)
参数：a b c : α；fun x => x + c；Finset.Ioc a b；a + c；b + c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `IsCancelAdd.toIsLeftCancelAdd`：∀ {G : Type u} {inst : Add G} [self : IsC
ancelAdd G], IsLeftCancelAdd G
· 使用定理 `IsOrderedCancelAddMonoid.toIsCancelAdd`：∀ {α : Type u_1} [inst : AddComm
Monoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], IsCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLT`：∀ {α : Type u_1} [inst : Ad
dCommMonoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], AddLeftRe
flectLT α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.map_add_right_Ioc`：∀ {α : Type u_2} [inst : AddCommMonoid α] [ins
t_1 : PartialOrder α] [inst_2 : IsOrderedCancelAddMonoid α]   [ExistsAddOfLE α] 
[inst_4 : Loca…
· 使用定理 `Finset.map_eq_image`：map_eq_image (f : α ↪ β) (s : Finset α) : s.map f =
 s.image f
· 使用定理 `add_left_injective`：∀ {G : Type u_1} [inst : Add G] [IsRightCancelAdd G]
 (a : G), Function.Injective fun x => x + a
· 使用定理 `addRightEmbedding.eq_1`：∀ {G : Type u_1} [inst : Add G] [inst_1 : IsRigh
tCancelAdd G] (g : G),   addRightEmbedding g = { toFun := fun h => h + g, inj' :
= ⋯ }
· 使用定理 `Function.Embedding.coeFn_mk`：coeFn_mk {α β} (f : α -> β) (i) : (@mk _ _ 
f i : α -> β) = f
-/
@[simp] lemma image_add_right_Ioc (a b c : α) : (Ioc a b).image (· + c) = Ioc (a + c) (b + c) := by
  rw [← map_add_right_Ioc, map_eq_image, addRightEmbedding, Embedding.coeFn_mk]
/-
**Finset.image_add_right_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : AddCommMonoid α] [inst_1 : PartialOrder α] [IsOrd
eredCancelAddMonoid α] [ExistsAddOfLE α]   [inst_4 : LocallyFiniteOrder α] [inst
_5 : DecidableEq α] (a b c : α),   Finset.image (fun x => x + c) (Finset.Ioo a b
) = Finset.Ioo (a + c) (b + c)
参数：a b c : α；fun x => x + c；Finset.Ioo a b；a + c；b + c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `IsCancelAdd.toIsLeftCancelAdd`：∀ {G : Type u} {inst : Add G} [self : IsC
ancelAdd G], IsLeftCancelAdd G
· 使用定理 `IsOrderedCancelAddMonoid.toIsCancelAdd`：∀ {α : Type u_1} [inst : AddComm
Monoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], IsCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLT`：∀ {α : Type u_1} [inst : Ad
dCommMonoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], AddLeftRe
flectLT α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.map_add_right_Ioo`：∀ {α : Type u_2} [inst : AddCommMonoid α] [ins
t_1 : PartialOrder α] [inst_2 : IsOrderedCancelAddMonoid α]   [ExistsAddOfLE α] 
[inst_4 : Loca…
· 使用定理 `Finset.map_eq_image`：map_eq_image (f : α ↪ β) (s : Finset α) : s.map f =
 s.image f
· 使用定理 `add_left_injective`：∀ {G : Type u_1} [inst : Add G] [IsRightCancelAdd G]
 (a : G), Function.Injective fun x => x + a
· 使用定理 `addRightEmbedding.eq_1`：∀ {G : Type u_1} [inst : Add G] [inst_1 : IsRigh
tCancelAdd G] (g : G),   addRightEmbedding g = { toFun := fun h => h + g, inj' :
= ⋯ }
· 使用定理 `Function.Embedding.coeFn_mk`：coeFn_mk {α β} (f : α -> β) (i) : (@mk _ _ 
f i : α -> β) = f
-/
@[simp] lemma image_add_right_Ioo (a b c : α) : (Ioo a b).image (· + c) = Ioo (a + c) (b + c) := by
  rw [← map_add_right_Ioo, map_eq_image, addRightEmbedding, Embedding.coeFn_mk]

end Finset

