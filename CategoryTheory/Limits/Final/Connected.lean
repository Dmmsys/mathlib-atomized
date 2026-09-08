/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.CategoryTheory.Discrete.StructuredArrow

/-!
# Characterization of connected categories using initial/final functors

A category `C` is connected iff the constant functor `C ⥤ Discrete PUnit`
is final (or initial).

We deduce that the projection `C × D ⥤ C` is final (or initial) if `D` is connected.

-/

public section

universe w v v' u u'

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {T : Type w} [Unique T]

/-
**CategoryTheory.isConnected_iff_final_of_unique** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory`。
形式化陈述：isConnected_iff_final_of_unique (F : C ⥤ Discrete T) : IsConnected C ↔ F.F
inal
参数：F : C ⥤ Discrete T。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.isConnected_iff_of_equivalence`：isConnected_iff_of_equiva
lence {K : Type u₂} [Category.{v₂} K] (e : J ≌ K) : IsConnected J ↔ IsConnected 
K
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `CategoryTheory.Functor.Final.out`：∀ {C : Type u₁} {inst : CategoryTheory
.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Category.{v₂, u₂} D
}   {F : CategoryTheor…
-/
lemma isConnected_iff_final_of_unique (F : C ⥤ Discrete T) :
    IsConnected C ↔ F.Final := by
  rw [← isConnected_iff_of_equivalence
    (Discrete.structuredArrowEquivalenceOfUnique F default)]
  refine ⟨fun _ ↦ ⟨?_⟩, fun _ ↦ inferInstance⟩
  rintro ⟨d⟩
  obtain rfl := Subsingleton.elim d default
  infer_instance
/-
**CategoryTheory.isConnected_iff_initial_of_unique** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory`。
形式化陈述：isConnected_iff_initial_of_unique (F : C ⥤ Discrete T) : IsConnected C ↔ F
.Initial
参数：F : C ⥤ Discrete T。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.isConnected_iff_of_equivalence`：isConnected_iff_of_equiva
lence {K : Type u₂} [Category.{v₂} K] (e : J ≌ K) : IsConnected J ↔ IsConnected 
K
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `CategoryTheory.Functor.Initial.out`：∀ {C : Type u₁} {inst : CategoryTheo
ry.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Category.{v₂, u₂}
 D}   {F : CategoryTheor…
-/
lemma isConnected_iff_initial_of_unique (F : C ⥤ Discrete T) :
    IsConnected C ↔ F.Initial := by
  rw [← isConnected_iff_of_equivalence
    (Discrete.costructuredArrowEquivalenceOfUnique F default)]
  refine ⟨fun _ ↦ ⟨?_⟩, fun _ ↦ inferInstance⟩
  rintro ⟨d⟩
  obtain rfl := Subsingleton.elim d default
  infer_instance
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (F : C ⥤ Discrete T) [IsConnected C] : F.Final := by
  rwa [← isConnected_iff_final_of_unique F]
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (F : C ⥤ Discrete T) [IsConnected C] : F.Initial := by
  rwa [← isConnected_iff_initial_of_unique F]
/-
**CategoryTheory.final_fst** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
形式化陈述：final_fst [IsConnected D] : (Prod.fst C D).Final
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance final_fst [IsConnected D] : (Prod.fst C D).Final :=
  inferInstanceAs (Functor.prod (𝟭 C) ((Functor.const _).obj (Discrete.mk .unit)) ⋙
    (prod.rightUnitorEquivalence.{0} C).functor).Final
/-
**CategoryTheory.final_snd** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
形式化陈述：final_snd [IsConnected C] : (Prod.snd C D).Final
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance final_snd [IsConnected C] : (Prod.snd C D).Final :=
  inferInstanceAs ((Prod.braiding C D).functor ⋙ Prod.fst D C).Final
/-
**CategoryTheory.initial_fst** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
形式化陈述：initial_fst [IsConnected D] : (Prod.fst C D).Initial
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance initial_fst [IsConnected D] : (Prod.fst C D).Initial :=
  inferInstanceAs (Functor.prod (𝟭 C) ((Functor.const _).obj (Discrete.mk .unit)) ⋙
    (prod.rightUnitorEquivalence.{0} C).functor).Initial
/-
**CategoryTheory.initial_snd** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
形式化陈述：initial_snd [IsConnected C] : (Prod.snd C D).Initial
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance initial_snd [IsConnected C] : (Prod.snd C D).Initial :=
  inferInstanceAs ((Prod.braiding C D).functor ⋙ Prod.fst D C).Initial

end CategoryTheory

