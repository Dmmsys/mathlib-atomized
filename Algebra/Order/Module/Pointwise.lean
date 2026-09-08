/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Pointwise.Set.Scalar
public import Mathlib.Algebra.Order.Module.Field
public import Mathlib.Order.Bounds.OrderIso
public import Mathlib.Order.GaloisConnection.Basic

/-!
# Bounds on scalar multiplication of set

This file proves order properties of pointwise operations of sets.
-/

public section

open scoped Pointwise

variable {α β : Type*}

section PosSMulMono
variable [SMul α β] [Preorder α] [Preorder β] [Zero α] [PosSMulMono α β] {a : α} {s : Set β}

/-
**smul_lowerBounds_subset_lowerBounds_smul_of_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `
`。
形式化陈述：smul_lowerBounds_subset_lowerBounds_smul_of_nonneg (ha : 0 <= a) : a • low
erBounds s subseteq lowerBounds (a • s)
参数：ha : 0 <= a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.image_lowerBounds_subset_lowerBounds_image`：∀ {α : Type u} {β :
 Type v} [inst : Preorder α] [inst_1 : Preorder β] {f : α → β},   Monotone f → ∀
 {s : Set α}, f '' lowerBounds s ⊆ lowerB…
· 使用引理 `monotone_smul_left_of_nonneg`：monotone_smul_left_of_nonneg [PosSMulMono 
α β] (ha : 0 <= a) : Monotone ((a • ·) : β -> β)
-/
lemma smul_lowerBounds_subset_lowerBounds_smul_of_nonneg (ha : 0 ≤ a) :
    a • lowerBounds s ⊆ lowerBounds (a • s) :=
  (monotone_smul_left_of_nonneg ha).image_lowerBounds_subset_lowerBounds_image
/-
**smul_upperBounds_subset_upperBounds_smul_of_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `
`。
形式化陈述：smul_upperBounds_subset_upperBounds_smul_of_nonneg (ha : 0 <= a) : a • upp
erBounds s subseteq upperBounds (a • s)
参数：ha : 0 <= a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.image_upperBounds_subset_upperBounds_image`：image_upperBounds_s
ubset_upperBounds_image : f '' upperBounds s subseteq upperBounds (f '' s)
· 使用引理 `monotone_smul_left_of_nonneg`：monotone_smul_left_of_nonneg [PosSMulMono 
α β] (ha : 0 <= a) : Monotone ((a • ·) : β -> β)
-/
lemma smul_upperBounds_subset_upperBounds_smul_of_nonneg (ha : 0 ≤ a) :
    a • upperBounds s ⊆ upperBounds (a • s) :=
  (monotone_smul_left_of_nonneg ha).image_upperBounds_subset_upperBounds_image
/-
**BddBelow.smul_of_nonneg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：BddBelow.smul_of_nonneg (hs : BddBelow s) (ha : 0 <= a) : BddBelow (a • s)
参数：hs : BddBelow s；ha : 0 <= a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.map_bddBelow`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [
inst_1 : Preorder β] {f : α → β},   Monotone f → ∀ {s : Set α}, BddBelow s → Bdd
Below (f ''…
· 使用引理 `monotone_smul_left_of_nonneg`：monotone_smul_left_of_nonneg [PosSMulMono 
α β] (ha : 0 <= a) : Monotone ((a • ·) : β -> β)
-/
lemma BddBelow.smul_of_nonneg (hs : BddBelow s) (ha : 0 ≤ a) : BddBelow (a • s) :=
  (monotone_smul_left_of_nonneg ha).map_bddBelow hs
/-
**BddAbove.smul_of_nonneg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：BddAbove.smul_of_nonneg (hs : BddAbove s) (ha : 0 <= a) : BddAbove (a • s)
参数：hs : BddAbove s；ha : 0 <= a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.map_bddAbove`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [
inst_1 : Preorder β] {f : α → β},   Monotone f → ∀ {s : Set α}, BddAbove s → Bdd
Above (f ''…
· 使用引理 `monotone_smul_left_of_nonneg`：monotone_smul_left_of_nonneg [PosSMulMono 
α β] (ha : 0 <= a) : Monotone ((a • ·) : β -> β)
-/
lemma BddAbove.smul_of_nonneg (hs : BddAbove s) (ha : 0 ≤ a) : BddAbove (a • s) :=
  (monotone_smul_left_of_nonneg ha).map_bddAbove hs

end PosSMulMono


section
variable [Preorder α] [Preorder β] [GroupWithZero α] [Zero β] [MulActionWithZero α β]
  [PosSMulMono α β] [PosSMulReflectLE α β] {s : Set β} {a : α}

/-
**lowerBounds_smul_of_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [inst_1 : Preorder β] 
[inst_2 : GroupWithZero α] [inst_3 : Zero β]   [inst_4 : MulActionWithZero α β] 
[PosSMulMono α β] [PosSMulReflectLE α β] {s : Set β} {a : α},   0 < a → lowerBou
nds (a • s) = a • lowerBounds s
参数：a • s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.lowerBounds_image`：lowerBounds_image {s : Set α} : lowerBounds 
(f '' s) = f '' lowerBounds s
-/
@[simp] lemma lowerBounds_smul_of_pos (ha : 0 < a) : lowerBounds (a • s) = a • lowerBounds s :=
  (OrderIso.smulRight ha).lowerBounds_image
/-
**upperBounds_smul_of_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [inst_1 : Preorder β] 
[inst_2 : GroupWithZero α] [inst_3 : Zero β]   [inst_4 : MulActionWithZero α β] 
[PosSMulMono α β] [PosSMulReflectLE α β] {s : Set β} {a : α},   0 < a → upperBou
nds (a • s) = a • upperBounds s
参数：a • s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.upperBounds_image`：upperBounds_image {s : Set α} : upperBounds 
(f '' s) = f '' upperBounds s
-/
@[simp] lemma upperBounds_smul_of_pos (ha : 0 < a) : upperBounds (a • s) = a • upperBounds s :=
  (OrderIso.smulRight ha).upperBounds_image
/-
**bddBelow_smul_iff_of_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [inst_1 : Preorder β] 
[inst_2 : GroupWithZero α] [inst_3 : Zero β]   [inst_4 : MulActionWithZero α β] 
[PosSMulMono α β] [PosSMulReflectLE α β] {s : Set β} {a : α},   0 < a → (BddBelo
w (a • s) ↔ BddBelow s)
参数：BddBelow (a • s) ↔ BddBelow s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.bddBelow_image`：∀ {α : Type u} {β : Type v} [inst : Preorder α]
 [inst_1 : Preorder β] (e : α ≃o β) {s : Set α},   BddBelow (⇑e '' s) ↔ BddBelow
 s
-/
@[simp] lemma bddBelow_smul_iff_of_pos (ha : 0 < a) : BddBelow (a • s) ↔ BddBelow s :=
  (OrderIso.smulRight ha).bddBelow_image
/-
**bddAbove_smul_iff_of_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [inst_1 : Preorder β] 
[inst_2 : GroupWithZero α] [inst_3 : Zero β]   [inst_4 : MulActionWithZero α β] 
[PosSMulMono α β] [PosSMulReflectLE α β] {s : Set β} {a : α},   0 < a → (BddAbov
e (a • s) ↔ BddAbove s)
参数：BddAbove (a • s) ↔ BddAbove s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.bddAbove_image`：bddAbove_image (e : α ≃o β) {s : Set α} : BddAb
ove (e '' s) ↔ BddAbove s
-/
@[simp] lemma bddAbove_smul_iff_of_pos (ha : 0 < a) : BddAbove (a • s) ↔ BddAbove s :=
  (OrderIso.smulRight ha).bddAbove_image

end

section OrderedRing

variable [Ring α] [PartialOrder α] [IsOrderedRing α]
  [AddCommGroup β] [PartialOrder β] [IsOrderedAddMonoid β]
  [Module α β] [PosSMulMono α β] {s : Set β} {a : α}

/-
**smul_lowerBounds_subset_upperBounds_smul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smul_lowerBounds_subset_upperBounds_smul (ha : a <= 0) : a • lowerBounds s
 subseteq upperBounds (a • s)
参数：ha : a <= 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Antitone.image_lowerBounds_subset_upperBounds_image`：image_lowerBounds_s
ubset_upperBounds_image : f '' lowerBounds s subseteq upperBounds (f '' s)
· 使用引理 `antitone_smul_left`：antitone_smul_left (ha : a <= 0) : Antitone ((a • ·)
 : β -> β)
-/
lemma smul_lowerBounds_subset_upperBounds_smul (ha : a ≤ 0) :
    a • lowerBounds s ⊆ upperBounds (a • s) :=
  (antitone_smul_left ha).image_lowerBounds_subset_upperBounds_image
/-
**smul_upperBounds_subset_lowerBounds_smul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smul_upperBounds_subset_lowerBounds_smul (ha : a <= 0) : a • upperBounds s
 subseteq lowerBounds (a • s)
参数：ha : a <= 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Antitone.image_upperBounds_subset_lowerBounds_image`：∀ {α : Type u} {β :
 Type v} [inst : Preorder α] [inst_1 : Preorder β] {f : α → β},   Antitone f → ∀
 {s : Set α}, f '' upperBounds s ⊆ lowerB…
· 使用引理 `antitone_smul_left`：antitone_smul_left (ha : a <= 0) : Antitone ((a • ·)
 : β -> β)
-/
lemma smul_upperBounds_subset_lowerBounds_smul (ha : a ≤ 0) :
    a • upperBounds s ⊆ lowerBounds (a • s) :=
  (antitone_smul_left ha).image_upperBounds_subset_lowerBounds_image
/-
**BddBelow.smul_of_nonpos** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：BddBelow.smul_of_nonpos (ha : a <= 0) (hs : BddBelow s) : BddAbove (a • s)
参数：ha : a <= 0；hs : BddBelow s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Antitone.map_bddBelow`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [
inst_1 : Preorder β] {f : α → β},   Antitone f → ∀ {s : Set α}, BddBelow s → Bdd
Above (f ''…
· 使用引理 `antitone_smul_left`：antitone_smul_left (ha : a <= 0) : Antitone ((a • ·)
 : β -> β)
-/
lemma BddBelow.smul_of_nonpos (ha : a ≤ 0) (hs : BddBelow s) : BddAbove (a • s) :=
  (antitone_smul_left ha).map_bddBelow hs
/-
**BddAbove.smul_of_nonpos** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：BddAbove.smul_of_nonpos (ha : a <= 0) (hs : BddAbove s) : BddBelow (a • s)
参数：ha : a <= 0；hs : BddAbove s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Antitone.map_bddAbove`：map_bddAbove : BddAbove s -> BddBelow (f '' s)
· 使用引理 `antitone_smul_left`：antitone_smul_left (ha : a <= 0) : Antitone ((a • ·)
 : β -> β)
-/
lemma BddAbove.smul_of_nonpos (ha : a ≤ 0) (hs : BddAbove s) : BddBelow (a • s) :=
  (antitone_smul_left ha).map_bddAbove hs

end OrderedRing

section LinearOrderedField
variable [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  [AddCommGroup β] [PartialOrder β] [IsOrderedAddMonoid β]
  [Module α β] [PosSMulMono α β] {s : Set β}
  {a : α}

/-
**lowerBounds_smul_of_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Field α] [inst_1 : LinearOrder α] 
[IsStrictOrderedRing α]   [inst_3 : AddCommGroup β] [inst_4 : PartialOrder β] [I
sOrderedAddMonoid β] [inst_6 : _root_.Module α β]   [PosSMulMono α β] {s : Set β
} {a : α}, a < 0 → lowerBounds (a • s) = a • upperBounds s
参数：a • s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.upperBounds_image`：upperBounds_image {s : Set α} : upperBounds 
(f '' s) = f '' upperBounds s
-/
@[simp] lemma lowerBounds_smul_of_neg (ha : a < 0) : lowerBounds (a • s) = a • upperBounds s :=
  (OrderIso.smulRightDual β ha).upperBounds_image
/-
**upperBounds_smul_of_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Field α] [inst_1 : LinearOrder α] 
[IsStrictOrderedRing α]   [inst_3 : AddCommGroup β] [inst_4 : PartialOrder β] [I
sOrderedAddMonoid β] [inst_6 : _root_.Module α β]   [PosSMulMono α β] {s : Set β
} {a : α}, a < 0 → upperBounds (a • s) = a • lowerBounds s
参数：a • s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.lowerBounds_image`：lowerBounds_image {s : Set α} : lowerBounds 
(f '' s) = f '' lowerBounds s
-/
@[simp] lemma upperBounds_smul_of_neg (ha : a < 0) : upperBounds (a • s) = a • lowerBounds s :=
  (OrderIso.smulRightDual β ha).lowerBounds_image
/-
**bddBelow_smul_iff_of_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Field α] [inst_1 : LinearOrder α] 
[IsStrictOrderedRing α]   [inst_3 : AddCommGroup β] [inst_4 : PartialOrder β] [I
sOrderedAddMonoid β] [inst_6 : _root_.Module α β]   [PosSMulMono α β] {s : Set β
} {a : α}, a < 0 → (BddBelow (a • s) ↔ BddAbove s)
参数：BddBelow (a • s) ↔ BddAbove s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.bddAbove_image`：bddAbove_image (e : α ≃o β) {s : Set α} : BddAb
ove (e '' s) ↔ BddAbove s
-/
@[simp] lemma bddBelow_smul_iff_of_neg (ha : a < 0) : BddBelow (a • s) ↔ BddAbove s :=
  (OrderIso.smulRightDual β ha).bddAbove_image
/-
**bddAbove_smul_iff_of_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Field α] [inst_1 : LinearOrder α] 
[IsStrictOrderedRing α]   [inst_3 : AddCommGroup β] [inst_4 : PartialOrder β] [I
sOrderedAddMonoid β] [inst_6 : _root_.Module α β]   [PosSMulMono α β] {s : Set β
} {a : α}, a < 0 → (BddAbove (a • s) ↔ BddBelow s)
参数：BddAbove (a • s) ↔ BddBelow s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.bddBelow_image`：∀ {α : Type u} {β : Type v} [inst : Preorder α]
 [inst_1 : Preorder β] (e : α ≃o β) {s : Set α},   BddBelow (⇑e '' s) ↔ BddBelow
 s
-/
@[simp] lemma bddAbove_smul_iff_of_neg (ha : a < 0) : BddAbove (a • s) ↔ BddBelow s :=
  (OrderIso.smulRightDual β ha).bddBelow_image

end LinearOrderedField

