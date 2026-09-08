/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Order.Interval.Finset.Basic
public import Mathlib.Order.Interval.Multiset

/-!
# Algebraic properties of multiset intervals

This file provides results about the interaction of algebra with `Multiset.Ixx`.
-/

public section

variable {α : Type*}

namespace Multiset
variable [AddCommMonoid α] [PartialOrder α] [IsOrderedCancelAddMonoid α]
  [ExistsAddOfLE α] [LocallyFiniteOrder α]

/-
**Multiset.map_add_left_Icc** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：map_add_left_Icc (a b c : α) : (Icc a b).map (c + ·) = Icc (c + a) (c + b)
参数：a b c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.Icc.eq_1`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : Locall
yFiniteOrder α] (a b : α), Multiset.Icc a b = (Finset.Icc a b).val
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.image_add_left_Icc`：∀ {α : Type u_2} [inst : AddCommMonoid α] [in
st_1 : PartialOrder α] [IsOrderedCancelAddMonoid α] [ExistsAddOfLE α]   [inst_4 
: LocallyFinite…
· 使用定理 `Finset.image_val`：image_val (f : α -> β) (s : Finset α) : (image f s).1 
= (s.1.map f).dedup
· 使用定理 `Multiset.Nodup.dedup`：∀ {α : Type u_1} [inst : DecidableEq α] {s : Multi
set α}, s.Nodup → s.dedup = s
· 使用定理 `Multiset.Nodup.map`：∀ {α : Type u_1} {β : Type v} {f : α → β} {s : Multi
set α}, Function.Injective f → s.Nodup → (Multiset.map f s).Nodup
· 使用定理 `add_right_injective`：∀ {G : Type u_1} [inst : Add G] [IsLeftCancelAdd G]
 (a : G), Function.Injective fun x => a + x
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `Finset.nodup`：∀ {α : Type u_4} (self : Finset α), self.val.Nodup
-/
lemma map_add_left_Icc (a b c : α) : (Icc a b).map (c + ·) = Icc (c + a) (c + b) := by
  classical rw [Icc, Icc, ← Finset.image_add_left_Icc, Finset.image_val,
      ((Finset.nodup _).map <| add_right_injective c).dedup]
/-
**Multiset.map_add_left_Ico** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：map_add_left_Ico (a b c : α) : (Ico a b).map (c + ·) = Ico (c + a) (c + b)
参数：a b c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.Ico.eq_1`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : Locall
yFiniteOrder α] (a b : α), Multiset.Ico a b = (Finset.Ico a b).val
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.image_add_left_Ico`：∀ {α : Type u_2} [inst : AddCommMonoid α] [in
st_1 : PartialOrder α] [IsOrderedCancelAddMonoid α] [ExistsAddOfLE α]   [inst_4 
: LocallyFinite…
· 使用定理 `Finset.image_val`：image_val (f : α -> β) (s : Finset α) : (image f s).1 
= (s.1.map f).dedup
· 使用定理 `Multiset.Nodup.dedup`：∀ {α : Type u_1} [inst : DecidableEq α] {s : Multi
set α}, s.Nodup → s.dedup = s
· 使用定理 `Multiset.Nodup.map`：∀ {α : Type u_1} {β : Type v} {f : α → β} {s : Multi
set α}, Function.Injective f → s.Nodup → (Multiset.map f s).Nodup
· 使用定理 `add_right_injective`：∀ {G : Type u_1} [inst : Add G] [IsLeftCancelAdd G]
 (a : G), Function.Injective fun x => a + x
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `Finset.nodup`：∀ {α : Type u_4} (self : Finset α), self.val.Nodup
-/
lemma map_add_left_Ico (a b c : α) : (Ico a b).map (c + ·) = Ico (c + a) (c + b) := by
  classical rw [Ico, Ico, ← Finset.image_add_left_Ico, Finset.image_val,
      ((Finset.nodup _).map <| add_right_injective c).dedup]
/-
**Multiset.map_add_left_Ioc** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：map_add_left_Ioc (a b c : α) : (Ioc a b).map (c + ·) = Ioc (c + a) (c + b)
参数：a b c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.Ioc.eq_1`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : Locall
yFiniteOrder α] (a b : α), Multiset.Ioc a b = (Finset.Ioc a b).val
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.image_add_left_Ioc`：∀ {α : Type u_2} [inst : AddCommMonoid α] [in
st_1 : PartialOrder α] [IsOrderedCancelAddMonoid α] [ExistsAddOfLE α]   [inst_4 
: LocallyFinite…
· 使用定理 `Finset.image_val`：image_val (f : α -> β) (s : Finset α) : (image f s).1 
= (s.1.map f).dedup
· 使用定理 `Multiset.Nodup.dedup`：∀ {α : Type u_1} [inst : DecidableEq α] {s : Multi
set α}, s.Nodup → s.dedup = s
· 使用定理 `Multiset.Nodup.map`：∀ {α : Type u_1} {β : Type v} {f : α → β} {s : Multi
set α}, Function.Injective f → s.Nodup → (Multiset.map f s).Nodup
· 使用定理 `add_right_injective`：∀ {G : Type u_1} [inst : Add G] [IsLeftCancelAdd G]
 (a : G), Function.Injective fun x => a + x
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `Finset.nodup`：∀ {α : Type u_4} (self : Finset α), self.val.Nodup
-/
lemma map_add_left_Ioc (a b c : α) : (Ioc a b).map (c + ·) = Ioc (c + a) (c + b) := by
  classical rw [Ioc, Ioc, ← Finset.image_add_left_Ioc, Finset.image_val,
      ((Finset.nodup _).map <| add_right_injective c).dedup]
/-
**Multiset.map_add_left_Ioo** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：map_add_left_Ioo (a b c : α) : (Ioo a b).map (c + ·) = Ioo (c + a) (c + b)
参数：a b c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.Ioo.eq_1`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : Locall
yFiniteOrder α] (a b : α), Multiset.Ioo a b = (Finset.Ioo a b).val
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.image_add_left_Ioo`：∀ {α : Type u_2} [inst : AddCommMonoid α] [in
st_1 : PartialOrder α] [IsOrderedCancelAddMonoid α] [ExistsAddOfLE α]   [inst_4 
: LocallyFinite…
· 使用定理 `Finset.image_val`：image_val (f : α -> β) (s : Finset α) : (image f s).1 
= (s.1.map f).dedup
· 使用定理 `Multiset.Nodup.dedup`：∀ {α : Type u_1} [inst : DecidableEq α] {s : Multi
set α}, s.Nodup → s.dedup = s
· 使用定理 `Multiset.Nodup.map`：∀ {α : Type u_1} {β : Type v} {f : α → β} {s : Multi
set α}, Function.Injective f → s.Nodup → (Multiset.map f s).Nodup
· 使用定理 `add_right_injective`：∀ {G : Type u_1} [inst : Add G] [IsLeftCancelAdd G]
 (a : G), Function.Injective fun x => a + x
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `Finset.nodup`：∀ {α : Type u_4} (self : Finset α), self.val.Nodup
-/
lemma map_add_left_Ioo (a b c : α) : (Ioo a b).map (c + ·) = Ioo (c + a) (c + b) := by
  classical rw [Ioo, Ioo, ← Finset.image_add_left_Ioo, Finset.image_val,
      ((Finset.nodup _).map <| add_right_injective c).dedup]
/-
**Multiset.map_add_right_Icc** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：map_add_right_Icc (a b c : α) : ((Icc a b).map fun x => x + c) = Icc (a + 
c) (b + c)
参数：a b c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用引理 `Multiset.map_add_left_Icc`：map_add_left_Icc (a b c : α) : (Icc a b).map 
(c + ·) = Icc (c + a) (c + b)
-/
lemma map_add_right_Icc (a b c : α) : ((Icc a b).map fun x => x + c) = Icc (a + c) (b + c) := by
  simp_rw [add_comm _ c]
  exact map_add_left_Icc _ _ _
/-
**Multiset.map_add_right_Ico** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：map_add_right_Ico (a b c : α) : ((Ico a b).map fun x => x + c) = Ico (a + 
c) (b + c)
参数：a b c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用引理 `Multiset.map_add_left_Ico`：map_add_left_Ico (a b c : α) : (Ico a b).map 
(c + ·) = Ico (c + a) (c + b)
-/
lemma map_add_right_Ico (a b c : α) : ((Ico a b).map fun x => x + c) = Ico (a + c) (b + c) := by
  simp_rw [add_comm _ c]
  exact map_add_left_Ico _ _ _
/-
**Multiset.map_add_right_Ioc** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：map_add_right_Ioc (a b c : α) : ((Ioc a b).map fun x => x + c) = Ioc (a + 
c) (b + c)
参数：a b c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用引理 `Multiset.map_add_left_Ioc`：map_add_left_Ioc (a b c : α) : (Ioc a b).map 
(c + ·) = Ioc (c + a) (c + b)
-/
lemma map_add_right_Ioc (a b c : α) : ((Ioc a b).map fun x => x + c) = Ioc (a + c) (b + c) := by
  simp_rw [add_comm _ c]
  exact map_add_left_Ioc _ _ _
/-
**Multiset.map_add_right_Ioo** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：map_add_right_Ioo (a b c : α) : ((Ioo a b).map fun x => x + c) = Ioo (a + 
c) (b + c)
参数：a b c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用引理 `Multiset.map_add_left_Ioo`：map_add_left_Ioo (a b c : α) : (Ioo a b).map 
(c + ·) = Ioo (c + a) (c + b)
-/
lemma map_add_right_Ioo (a b c : α) : ((Ioo a b).map fun x => x + c) = Ioo (a + c) (b + c) := by
  simp_rw [add_comm _ c]
  exact map_add_left_Ioo _ _ _

end Multiset

