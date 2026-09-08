/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.LimitsOfShape
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic

/-!
# Preservation of limits, as a property of objects in the functor category

We make the typeclass `PreservesLimitsOfShape K` (resp. `PreservesFiniteLimits`)
a property of objects in the functor category `J ⥤ C`, and show that
it is stable under colimits of shape `K'` when they
commute to limits of shape `K` (resp. to finite limits).

-/

public section

namespace CategoryTheory

open Limits

variable {J J' C D : Type*} (K K' : Type*)
  [Category* K] [Category* K'] [Category* J] [Category* J'] [Category* C] [Category* D]

namespace ObjectProperty

variable {K} in
/-- The property of objects in the functor category `J ⥤ C`
which preserves the limit of a functor `F : K ⥤ J`. -/
/-
**CategoryTheory.ObjectProperty.preservesLimit** 是 Mathlib 中的一个缩写定义，位于命名空间 `Cate
goryTheory.ObjectProperty`。
形式化陈述：preservesLimit (F : K ⥤ J) : ObjectProperty (J ⥤ C)
参数：F : K ⥤ J。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The property of objects in the functor category `J ⥤ C`
which preserves the limit of a functor `F : K ⥤ J`.
-/
abbrev preservesLimit (F : K ⥤ J) : ObjectProperty (J ⥤ C) := PreservesLimit F

@[simp]
/-
**CategoryTheory.ObjectProperty.preservesLimit_iff** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.ObjectProperty`。
形式化陈述：preservesLimit_iff (F : K ⥤ J) (G : J ⥤ C) : preservesLimit F G ↔ Preserve
sLimit F G
参数：F : K ⥤ J；G : J ⥤ C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma preservesLimit_iff (F : K ⥤ J) (G : J ⥤ C) :
    preservesLimit F G ↔ PreservesLimit F G := Iff.rfl
/-
**CategoryTheory.ObjectProperty.congr_preservesLimit** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.ObjectProperty`。
形式化陈述：congr_preservesLimit {F F' : K ⥤ J} (e : F ≅ F') : preservesLimit (C
参数：e : F ≅ F'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Limits.preservesLimit_of_iso_diagram`：preservesLimit_of_i
so_diagram {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂) [PreservesLimit K₁ F] : Pre
servesLimit K₂ F where preserves {c} t
-/
lemma congr_preservesLimit {F F' : K ⥤ J} (e : F ≅ F') :
    preservesLimit (C := C) F = preservesLimit (C := C) F' := by
  ext G
  simp_rw [preservesLimit_iff]
  exact ⟨fun h ↦ preservesLimit_of_iso_diagram _ e,
    fun h ↦ preservesLimit_of_iso_diagram _ e.symm⟩
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (F : K ⥤ J) : (preservesLimit (C := C) F).IsClosedUnderIsomorphisms where
  of_iso e _ := preservesLimit_of_natIso _ e

variable {K} in
/-- The property of objects in the functor category `J ⥤ C`
which preserves the colimit of a functor `F : K ⥤ J`. -/
/-
**CategoryTheory.ObjectProperty.preservesColimit** 是 Mathlib 中的一个缩写定义，位于命名空间 `Ca
tegoryTheory.ObjectProperty`。
形式化陈述：preservesColimit (F : K ⥤ J) : ObjectProperty (J ⥤ C)
参数：F : K ⥤ J。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The property of objects in the functor category `J ⥤ C`
which preserves the colimit of a functor `F : K ⥤ J`.
-/
abbrev preservesColimit (F : K ⥤ J) : ObjectProperty (J ⥤ C) := PreservesColimit F

@[simp]
/-
**CategoryTheory.ObjectProperty.preservesColimit_iff** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.ObjectProperty`。
形式化陈述：preservesColimit_iff (F : K ⥤ J) (G : J ⥤ C) : preservesColimit F G ↔ Pres
ervesColimit F G
参数：F : K ⥤ J；G : J ⥤ C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma preservesColimit_iff (F : K ⥤ J) (G : J ⥤ C) :
    preservesColimit F G ↔ PreservesColimit F G := Iff.rfl
/-
**CategoryTheory.ObjectProperty.congr_preservesColimit** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.ObjectProperty`。
形式化陈述：congr_preservesColimit {F F' : K ⥤ J} (e : F ≅ F') : preservesColimit (C
参数：e : F ≅ F'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Limits.preservesColimit_of_iso_diagram`：preservesColimit_
of_iso_diagram {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂) [PreservesColimit K₁ F]
 : PreservesColimit K₂ F where preserves {c…
-/
lemma congr_preservesColimit {F F' : K ⥤ J} (e : F ≅ F') :
    preservesColimit (C := C) F = preservesColimit (C := C) F' := by
  ext G
  simp_rw [preservesColimit_iff]
  exact ⟨fun h ↦ preservesColimit_of_iso_diagram _ e,
    fun h ↦ preservesColimit_of_iso_diagram _ e.symm⟩
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (F : K ⥤ J) : (preservesColimit (C := C) F).IsClosedUnderIsomorphisms where
  of_iso e _ := preservesColimit_of_natIso _ e

/-- The property of objects in the functor category `J ⥤ C`
which preserves limits of shape `K`. -/
/-
**CategoryTheory.ObjectProperty.preservesLimitsOfShape** 是 Mathlib 中的一个缩写定义，位于命名
空间 `CategoryTheory.ObjectProperty`。
形式化陈述：preservesLimitsOfShape : ObjectProperty (J ⥤ C)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The property of objects in the functor category `J ⥤ C`
which preserves limits of shape `K`.
-/
abbrev preservesLimitsOfShape : ObjectProperty (J ⥤ C) := PreservesLimitsOfShape K

@[simp]
/-
**CategoryTheory.ObjectProperty.preservesLimitsOfShape_iff** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：preservesLimitsOfShape_iff (F : J ⥤ C) : preservesLimitsOfShape K F ↔ Pres
ervesLimitsOfShape K F
参数：F : J ⥤ C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma preservesLimitsOfShape_iff (F : J ⥤ C) :
    preservesLimitsOfShape K F ↔ PreservesLimitsOfShape K F := Iff.rfl
/-
**CategoryTheory.ObjectProperty.preservesLimitsOfShape_eq_iSup** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：preservesLimitsOfShape_eq_iSup : preservesLimitsOfShape (J
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iInf_apply`：∀ {α : Type u_8} {β : α → Type u_9} {ι : Sort u_10} [inst : 
(i : α) → InfSet (β i)] {f : ι → (a : α) → β a} {a : α},   (⨅ i, f i) a = ⨅ i, f
…
· 使用定理 `iInf_Prop_eq`：iInf_Prop_eq {p : ι -> Prop} : ⨅ i, p i = forall i, p i
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
-/
lemma preservesLimitsOfShape_eq_iSup :
    preservesLimitsOfShape (J := J) (C := C) K =
      ⨅ (F : K ⥤ J), preservesLimit F := by
  ext G
  simp only [preservesLimitsOfShape_iff, iInf_apply, preservesLimit_iff, iInf_Prop_eq]
  exact ⟨fun _ ↦ inferInstance, fun _ ↦ ⟨inferInstance⟩⟩

variable (J C) {K K'} in
/-
**CategoryTheory.ObjectProperty.congr_preservesLimitsOfShape** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：congr_preservesLimitsOfShape (e : K ≌ K') : preservesLimitsOfShape (J
参数：e : K ≌ K'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Limits.preservesLimitsOfShape_of_equiv`：preservesLimitsOf
Shape_of_equiv {J' : Type w₂} [Category.{w₂'} J'] (e : J ≌ J') (F : C ⥤ D) [Pres
ervesLimitsOfShape J F] : PreservesLimitsOf…
-/
lemma congr_preservesLimitsOfShape (e : K ≌ K') :
    preservesLimitsOfShape (J := J) (C := C) K = preservesLimitsOfShape K' := by
  ext G
  simp only [preservesLimitsOfShape_iff]
  exact ⟨fun _ ↦ preservesLimitsOfShape_of_equiv e _,
    fun _ ↦ preservesLimitsOfShape_of_equiv e.symm _⟩
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (preservesLimitsOfShape (J := J) (C := C) K).IsClosedUnderIsomorphisms := by
  rw [preservesLimitsOfShape_eq_iSup]
  infer_instance

/-- The property of objects in the functor category `J ⥤ C`
which preserves colimits of shape `K`. -/
/-
**CategoryTheory.ObjectProperty.preservesColimitsOfShape** 是 Mathlib 中的一个缩写定义，位于
命名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：preservesColimitsOfShape : ObjectProperty (J ⥤ C)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The property of objects in the functor category `J ⥤ C`
which preserves colimits of shape `K`.
-/
abbrev preservesColimitsOfShape : ObjectProperty (J ⥤ C) := PreservesColimitsOfShape K

@[simp]
/-
**CategoryTheory.ObjectProperty.preservesColimitsOfShape_iff** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：preservesColimitsOfShape_iff (F : J ⥤ C) : preservesColimitsOfShape K F ↔ 
PreservesColimitsOfShape K F
参数：F : J ⥤ C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma preservesColimitsOfShape_iff (F : J ⥤ C) :
    preservesColimitsOfShape K F ↔ PreservesColimitsOfShape K F := Iff.rfl
/-
**CategoryTheory.ObjectProperty.preservesColimitsOfShape_eq_iSup** 是 Mathlib 中的一
个引理，位于命名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：preservesColimitsOfShape_eq_iSup : preservesColimitsOfShape (J
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iInf_apply`：∀ {α : Type u_8} {β : α → Type u_9} {ι : Sort u_10} [inst : 
(i : α) → InfSet (β i)] {f : ι → (a : α) → β a} {a : α},   (⨅ i, f i) a = ⨅ i, f
…
· 使用定理 `iInf_Prop_eq`：iInf_Prop_eq {p : ι -> Prop} : ⨅ i, p i = forall i, p i
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
-/
lemma preservesColimitsOfShape_eq_iSup :
    preservesColimitsOfShape (J := J) (C := C) K =
      ⨅ (F : K ⥤ J), preservesColimit F := by
  ext G
  simp only [preservesColimitsOfShape_iff, iInf_apply, preservesColimit_iff, iInf_Prop_eq]
  exact ⟨fun _ ↦ inferInstance, fun _ ↦ ⟨inferInstance⟩⟩

variable (J C) {K K'} in
/-
**CategoryTheory.ObjectProperty.congr_preservesColimitsOfShape** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：congr_preservesColimitsOfShape (e : K ≌ K') : preservesColimitsOfShape (J
参数：e : K ≌ K'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Limits.preservesColimitsOfShape_of_equiv`：preservesColimi
tsOfShape_of_equiv {J' : Type w₂} [Category.{w₂'} J'] (e : J ≌ J') (F : C ⥤ D) [
PreservesColimitsOfShape J F] : PreservesColi…
-/
lemma congr_preservesColimitsOfShape (e : K ≌ K') :
    preservesColimitsOfShape (J := J) (C := C) K = preservesColimitsOfShape K' := by
  ext G
  simp only [preservesColimitsOfShape_iff]
  exact ⟨fun _ ↦ preservesColimitsOfShape_of_equiv e _,
    fun _ ↦ preservesColimitsOfShape_of_equiv e.symm _⟩
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (preservesColimitsOfShape (J := J) (C := C) K).IsClosedUnderIsomorphisms := by
  rw [preservesColimitsOfShape_eq_iSup]
  infer_instance

/-- The property of objects in the functor category `J ⥤ C`
which preserves finite limits. -/
/-
**CategoryTheory.ObjectProperty.preservesFiniteLimits** 是 Mathlib 中的一个缩写定义，位于命名空
间 `CategoryTheory.ObjectProperty`。
形式化陈述：preservesFiniteLimits : ObjectProperty (J ⥤ C)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The property of objects in the functor category `J ⥤ C`
which preserves finite limits.
-/
abbrev preservesFiniteLimits : ObjectProperty (J ⥤ C) := PreservesFiniteLimits

@[simp]
/-
**CategoryTheory.ObjectProperty.preservesFiniteLimits_iff** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：preservesFiniteLimits_iff (F : J ⥤ C) : preservesFiniteLimits F ↔ Preserve
sFiniteLimits F
参数：F : J ⥤ C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma preservesFiniteLimits_iff (F : J ⥤ C) :
    preservesFiniteLimits F ↔ PreservesFiniteLimits F := Iff.rfl
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (preservesFiniteLimits (J := J) (C := C)).IsClosedUnderIsomorphisms where
  of_iso e _ := preservesFiniteLimits_of_natIso e

/-- The property of objects in the functor category `J ⥤ C`
which preserves finite colimits. -/
/-
**CategoryTheory.ObjectProperty.preservesFiniteColimits** 是 Mathlib 中的一个缩写定义，位于命
名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：preservesFiniteColimits : ObjectProperty (J ⥤ C)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The property of objects in the functor category `J ⥤ C`
which preserves finite colimits.
-/
abbrev preservesFiniteColimits : ObjectProperty (J ⥤ C) := PreservesFiniteColimits
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (preservesFiniteColimits (J := J) (C := C)).IsClosedUnderIsomorphisms where
  of_iso e _ := preservesFiniteColimits_of_natIso e

@[simp]
/-
**CategoryTheory.ObjectProperty.preservesFiniteColimits_iff** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：preservesFiniteColimits_iff (F : J ⥤ C) : preservesFiniteColimits F ↔ Pres
ervesFiniteColimits F
参数：F : J ⥤ C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma preservesFiniteColimits_iff (F : J ⥤ C) :
    preservesFiniteColimits F ↔ PreservesFiniteColimits F := Iff.rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasColimitsOfShape K' C]
    [PreservesLimitsOfShape K (colim (J := K') (C := C))] :
    (preservesLimitsOfShape K : ObjectProperty (J ⥤ C)).IsClosedUnderColimitsOfShape K' where
  colimitsOfShape_le := by
    rintro G ⟨h⟩
    have := h.prop_diag_obj
    have : PreservesLimitsOfShape K h.diag.flip := ⟨fun {F} ↦ ⟨fun {c} hc ↦
      ⟨evaluationJointlyReflectsLimits _
        (fun k' ↦ isLimitOfPreserves (h.diag.obj k') hc)⟩⟩⟩
    let e : h.diag.flip ⋙ colim ≅ G :=
      NatIso.ofComponents
        (fun j ↦ (colimit.isColimit (h.diag.flip.obj j)).coconePointUniqueUpToIso
          (isColimitOfPreserves ((evaluation _ _).obj j) h.isColimit))
    exact preservesLimitsOfShape_of_natIso e
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasColimitsOfShape K' C] [HasExactColimitsOfShape K' C] :
    ObjectProperty.IsClosedUnderColimitsOfShape
      (preservesFiniteLimits : ObjectProperty (J ⥤ C)) K' where
  colimitsOfShape_le := by
    rintro G ⟨h⟩
    have := h.prop_diag_obj
    exact ⟨fun K _ _ ↦ (preservesLimitsOfShape K).prop_of_isColimit h.isColimit inferInstance⟩

end ObjectProperty

end CategoryTheory

