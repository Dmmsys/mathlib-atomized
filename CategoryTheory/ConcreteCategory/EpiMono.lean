/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Images
public import Mathlib.CategoryTheory.MorphismProperty.Concrete
public import Mathlib.CategoryTheory.Types.Basic

/-!
# Epi and mono in concrete categories

In this file, we relate epimorphisms and monomorphisms in a concrete category `C`
to surjective and injective morphisms, and we show that if `C` has
strong epi mono factorizations and is such that `forget C` preserves
both epi and mono, then any morphism in `C` can be factored in a
functorial manner as a composition of a surjective morphism followed
by an injective morphism.

-/

@[expose] public section

universe w v v' u u'

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {FC : C → C → Type*} {CC : C → Type w}
variable [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory.{w} C FC]

open Limits MorphismProperty

namespace ConcreteCategory

section

/-
**CategoryTheory.ConcreteCategory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Con
creteCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [(forget C).PreservesMonomorphisms] {X Y : C} (f : X ⟶ Y) [Mono f] :
    Mono (↾f) := Functor.map_mono (forget C) f
/-
**CategoryTheory.ConcreteCategory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Con
creteCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [(forget C).PreservesEpimorphisms] {X Y : C} (f : X ⟶ Y) [Epi f] :
    Epi (↾f) := Functor.map_epi (forget C) f

/-- In any concrete category, injective morphisms are monomorphisms. -/
/-
**CategoryTheory.ConcreteCategory.mono_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.ConcreteCategory`。
形式化陈述：mono_of_injective {X Y : C} (f : X ⟶ Y) (i : Function.Injective f) : Mono 
f
参数：f : X ⟶ Y；i : Function.Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.mono_of_mono_map`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.reflectsMonomorphisms_of_faithful`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTh
eory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.instFaithfulForget`：∀ (C : Type u_1) [inst : CategoryTheo
ry.Category.{v_1, u_1} C] {FC : outParam (C → C → Type u_2)}   {CC : outParam (C
 → Type w)} [inst_1 : o…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.mono_iff_injective`：mono_iff_injective {X Y : Type u} (f 
: X ⟶ Y) : Mono f ↔ Function.Injective f

--- 原说明 ---
In any concrete category, injective morphisms are monomorphisms.
-/
theorem mono_of_injective {X Y : C} (f : X ⟶ Y) (i : Function.Injective f) :
    Mono f :=
  (forget C).mono_of_mono_map ((mono_iff_injective ((forget C).map f)).2 i)
/-
**CategoryTheory.ConcreteCategory.forget** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry.ConcreteCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance forget₂_preservesMonomorphisms (C : Type u) (D : Type u')
    [Category.{v} C] [Category.{v'} D]
    {FC : C → C → Type*} {CC : C → Type w}
    [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)]
    [ConcreteCategory C FC]
    {FD : D → D → Type*} {CD : D → Type w}
    [∀ X Y, FunLike (FD X Y) (CD X) (CD Y)]
    [ConcreteCategory D FD]
    [HasForget₂ C D] [(forget C).PreservesMonomorphisms] :
    (forget₂ C D).PreservesMonomorphisms :=
  have : (forget₂ C D ⋙ forget D).PreservesMonomorphisms := by
    simp only [HasForget₂.forget_comp]
    infer_instance
  Functor.preservesMonomorphisms_of_preserves_of_reflects _ (forget D)
/-
**CategoryTheory.ConcreteCategory.forget** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry.ConcreteCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance forget₂_preservesEpimorphisms (C : Type u) (D : Type u')
    [Category.{v} C] [Category.{v'} D]
    {FC : C → C → Type*} {CC : C → Type w}
    [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)]
    [ConcreteCategory C FC]
    {FD : D → D → Type*} {CD : D → Type w}
    [∀ X Y, FunLike (FD X Y) (CD X) (CD Y)]
    [ConcreteCategory D FD]
    [HasForget₂ C D] [(forget C).PreservesEpimorphisms] :
    (forget₂ C D).PreservesEpimorphisms :=
  have : (forget₂ C D ⋙ forget D).PreservesEpimorphisms := by
    simp only [HasForget₂.forget_comp]
    infer_instance
  Functor.preservesEpimorphisms_of_preserves_of_reflects _ (forget D)

variable (C)
/-
**CategoryTheory.ConcreteCategory.surjective_le_epimorphisms** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.ConcreteCategory`。
形式化陈述：surjective_le_epimorphisms : MorphismProperty.surjective C <= epimorphisms
 C
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.epi_of_epi_map`：epi_of_epi_map (F : C ⥤ D) [Refle
ctsEpimorphisms F] {X Y : C} {f : X ⟶ Y} (h : Epi (F.map f)) : Epi f
· 使用定理 `CategoryTheory.Functor.reflectsEpimorphisms_of_faithful`：∀ {C : Type u₁}
 [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryThe
ory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.instFaithfulForget`：∀ (C : Type u_1) [inst : CategoryTheo
ry.Category.{v_1, u_1} C] {FC : outParam (C → C → Type u_2)}   {CC : outParam (C
 → Type w)} [inst_1 : o…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.epi_iff_surjective`：epi_iff_surjective {X Y : Type u} (f 
: X ⟶ Y) : Epi f ↔ Function.Surjective f
-/
lemma surjective_le_epimorphisms :
    MorphismProperty.surjective C ≤ epimorphisms C :=
  fun _ _ _ hf => (forget C).epi_of_epi_map ((epi_iff_surjective _).2 hf)
/-
**CategoryTheory.ConcreteCategory.injective_le_monomorphisms** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.ConcreteCategory`。
形式化陈述：injective_le_monomorphisms : MorphismProperty.injective C <= monomorphisms
 C
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.mono_of_mono_map`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.reflectsMonomorphisms_of_faithful`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTh
eory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.instFaithfulForget`：∀ (C : Type u_1) [inst : CategoryTheo
ry.Category.{v_1, u_1} C] {FC : outParam (C → C → Type u_2)}   {CC : outParam (C
 → Type w)} [inst_1 : o…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.mono_iff_injective`：mono_iff_injective {X Y : Type u} (f 
: X ⟶ Y) : Mono f ↔ Function.Injective f
-/
lemma injective_le_monomorphisms :
    MorphismProperty.injective C ≤ monomorphisms C :=
  fun _ _ _ hf => (forget C).mono_of_mono_map ((mono_iff_injective _).2 hf)
/-
**CategoryTheory.ConcreteCategory.surjective_eq_epimorphisms_iff** 是 Mathlib 中的一
个引理，位于命名空间 `CategoryTheory.ConcreteCategory`。
形式化陈述：surjective_eq_epimorphisms_iff : MorphismProperty.surjective C = epimorphi
sms C ↔ (forget C).PreservesEpimorphisms
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.epi_iff_surjective`：epi_iff_surjective {X Y : Type u} (f 
: X ⟶ Y) : Epi f ↔ Function.Surjective f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `CategoryTheory.ConcreteCategory.surjective_le_epimorphisms`：surjective_l
e_epimorphisms : MorphismProperty.surjective C <= epimorphisms C
· 使用定理 `CategoryTheory.ConcreteCategory.instEpiOfHomCoeHomOfPreservesEpimorphism
sForget`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {FC : C → C → 
Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → FunLike (FC X Y) …
-/
lemma surjective_eq_epimorphisms_iff :
    MorphismProperty.surjective C = epimorphisms C ↔ (forget C).PreservesEpimorphisms := by
  constructor
  · intro h
    constructor
    rintro _ _ f (hf : epimorphisms C f)
    rw [epi_iff_surjective]
    rw [← h] at hf
    exact hf
  · intro
    apply le_antisymm (surjective_le_epimorphisms C)
    intro _ _ f hf
    have : Epi f := hf
    change Function.Surjective ((forget C).map f)
    rw [← epi_iff_surjective]
    infer_instance
/-
**CategoryTheory.ConcreteCategory.injective_eq_monomorphisms_iff** 是 Mathlib 中的一
个引理，位于命名空间 `CategoryTheory.ConcreteCategory`。
形式化陈述：injective_eq_monomorphisms_iff : MorphismProperty.injective C = monomorphi
sms C ↔ (forget C).PreservesMonomorphisms
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.mono_iff_injective`：mono_iff_injective {X Y : Type u} (f 
: X ⟶ Y) : Mono f ↔ Function.Injective f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `CategoryTheory.ConcreteCategory.injective_le_monomorphisms`：injective_le
_monomorphisms : MorphismProperty.injective C <= monomorphisms C
· 使用定理 `CategoryTheory.ConcreteCategory.instMonoOfHomCoeHomOfPreservesMonomorphi
smsForget`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {FC : C → C 
→ Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → FunLike (FC X Y) …
-/
lemma injective_eq_monomorphisms_iff :
    MorphismProperty.injective C = monomorphisms C ↔ (forget C).PreservesMonomorphisms := by
  constructor
  · intro h
    constructor
    rintro _ _ f (hf : monomorphisms C f)
    rw [mono_iff_injective]
    rw [← h] at hf
    exact hf
  · intro
    apply le_antisymm (injective_le_monomorphisms C)
    intro _ _ f hf
    have : Mono f := hf
    change Function.Injective ((forget C).map f)
    rw [← mono_iff_injective]
    infer_instance
/-
**CategoryTheory.ConcreteCategory.injective_eq_monomorphisms** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.ConcreteCategory`。
形式化陈述：injective_eq_monomorphisms [(forget C).PreservesMonomorphisms] : MorphismP
roperty.injective C = monomorphisms C
参数：forget C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ConcreteCategory.injective_eq_monomorphisms_iff`：injectiv
e_eq_monomorphisms_iff : MorphismProperty.injective C = monomorphisms C ↔ (forge
t C).PreservesMonomorphisms
-/
lemma injective_eq_monomorphisms [(forget C).PreservesMonomorphisms] :
    MorphismProperty.injective C = monomorphisms C := by
  rw [injective_eq_monomorphisms_iff]
  infer_instance
/-
**CategoryTheory.ConcreteCategory.surjective_eq_epimorphisms** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.ConcreteCategory`。
形式化陈述：surjective_eq_epimorphisms [(forget C).PreservesEpimorphisms] : MorphismPr
operty.surjective C = epimorphisms C
参数：forget C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ConcreteCategory.surjective_eq_epimorphisms_iff`：surjecti
ve_eq_epimorphisms_iff : MorphismProperty.surjective C = epimorphisms C ↔ (forge
t C).PreservesEpimorphisms
-/
lemma surjective_eq_epimorphisms [(forget C).PreservesEpimorphisms] :
    MorphismProperty.surjective C = epimorphisms C := by
  rw [surjective_eq_epimorphisms_iff]
  infer_instance

variable [HasStrongEpiMonoFactorisations C] [(forget C).PreservesMonomorphisms]
  [(forget C).PreservesEpimorphisms]

/-- A concrete category with strong epi mono factorizations and such that
the forget functor preserves mono and epi admits functorial surjective/injective
factorizations. -/
/-
**CategoryTheory.ConcreteCategory.functorialSurjectiveInjectiveFactorizationData
** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.ConcreteCategory`。
形式化陈述：functorialSurjectiveInjectiveFactorizationData : FunctorialSurjectiveInjec
tiveFactorizationData C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A concrete category with strong epi mono factorizations and such that
the forget functor preserves mono and epi admits functorial surjective/injective
factorizations.
-/
noncomputable def functorialSurjectiveInjectiveFactorizationData :
    FunctorialSurjectiveInjectiveFactorizationData C :=
  (functorialEpiMonoFactorizationData C).ofLE
    (by rw [surjective_eq_epimorphisms])
    (by rw [injective_eq_monomorphisms])
/-
**CategoryTheory.ConcreteCategory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Con
creteCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) : HasFunctorialSurjectiveInjectiveFactorization C where
  nonempty_functorialFactorizationData :=
    ⟨functorialSurjectiveInjectiveFactorizationData C⟩

end

section

open CategoryTheory.Limits

/-
**CategoryTheory.ConcreteCategory.injective_of_mono_of_preservesPullback** 是 Mat
hlib 中的一个定理，位于命名空间 `CategoryTheory.ConcreteCategory`。
形式化陈述：injective_of_mono_of_preservesPullback {X Y : C} (f : X ⟶ Y) [Mono f] [Pre
servesLimitsOfShape WalkingCospan (forget C)] : Function.Injective f
参数：f : X ⟶ Y；forget C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.mono_iff_injective`：mono_iff_injective {X Y : Type u} (f 
: X ⟶ Y) : Mono f ↔ Function.Injective f
· 使用定理 `CategoryTheory.ConcreteCategory.instMonoOfHomCoeHomOfPreservesMonomorphi
smsForget`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {FC : C → C 
→ Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → FunLike (FC X Y) …
· 使用定理 `CategoryTheory.preservesMonomorphisms_of_preservesLimitsOfShape`：∀ {C : 
Type u₁} {D : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
-/
theorem injective_of_mono_of_preservesPullback {X Y : C} (f : X ⟶ Y) [Mono f]
    [PreservesLimitsOfShape WalkingCospan (forget C)] : Function.Injective f :=
  (mono_iff_injective ((forget C).map f)).mp inferInstance
/-
**CategoryTheory.ConcreteCategory.mono_iff_injective_of_preservesPullback** 是 Ma
thlib 中的一个定理，位于命名空间 `CategoryTheory.ConcreteCategory`。
形式化陈述：mono_iff_injective_of_preservesPullback {X Y : C} (f : X ⟶ Y) [PreservesLi
mitsOfShape WalkingCospan (forget C)] : Mono f ↔ Function.Injective f
参数：f : X ⟶ Y；forget C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `CategoryTheory.Functor.mono_map_iff_mono`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.preservesMonomorphisms_of_preservesLimitsOfShape`：∀ {C : 
Type u₁} {D : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.reflectsMonomorphisms_of_faithful`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTh
eory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.instFaithfulForget`：∀ (C : Type u_1) [inst : CategoryTheo
ry.Category.{v_1, u_1} C] {FC : outParam (C → C → Type u_2)}   {CC : outParam (C
 → Type w)} [inst_1 : o…
· 使用定理 `CategoryTheory.mono_iff_injective`：mono_iff_injective {X Y : Type u} (f 
: X ⟶ Y) : Mono f ↔ Function.Injective f
-/
theorem mono_iff_injective_of_preservesPullback {X Y : C} (f : X ⟶ Y)
    [PreservesLimitsOfShape WalkingCospan (forget C)] : Mono f ↔ Function.Injective f :=
  ((forget C).mono_map_iff_mono _).symm.trans (mono_iff_injective _)

/-- In any concrete category, surjective morphisms are epimorphisms. -/
/-
**CategoryTheory.ConcreteCategory.epi_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.ConcreteCategory`。
形式化陈述：epi_of_surjective {X Y : C} (f : X ⟶ Y) (s : Function.Surjective f) : Epi 
f
参数：f : X ⟶ Y；s : Function.Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.epi_of_epi_map`：epi_of_epi_map (F : C ⥤ D) [Refle
ctsEpimorphisms F] {X Y : C} {f : X ⟶ Y} (h : Epi (F.map f)) : Epi f
· 使用定理 `CategoryTheory.Functor.reflectsEpimorphisms_of_faithful`：∀ {C : Type u₁}
 [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryThe
ory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.instFaithfulForget`：∀ (C : Type u_1) [inst : CategoryTheo
ry.Category.{v_1, u_1} C] {FC : outParam (C → C → Type u_2)}   {CC : outParam (C
 → Type w)} [inst_1 : o…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.epi_iff_surjective`：epi_iff_surjective {X Y : Type u} (f 
: X ⟶ Y) : Epi f ↔ Function.Surjective f

--- 原说明 ---
In any concrete category, surjective morphisms are epimorphisms.
-/
theorem epi_of_surjective {X Y : C} (f : X ⟶ Y) (s : Function.Surjective f) :
    Epi f :=
  (forget C).epi_of_epi_map ((epi_iff_surjective ((forget C).map f)).2 s)
/-
**CategoryTheory.ConcreteCategory.surjective_of_epi_of_preservesPushout** 是 Math
lib 中的一个定理，位于命名空间 `CategoryTheory.ConcreteCategory`。
形式化陈述：surjective_of_epi_of_preservesPushout {X Y : C} (f : X ⟶ Y) [Epi f] [Prese
rvesColimitsOfShape WalkingSpan (forget C)] : Function.Surjective f
参数：f : X ⟶ Y；forget C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.epi_iff_surjective`：epi_iff_surjective {X Y : Type u} (f 
: X ⟶ Y) : Epi f ↔ Function.Surjective f
· 使用定理 `CategoryTheory.ConcreteCategory.instEpiOfHomCoeHomOfPreservesEpimorphism
sForget`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {FC : C → C → 
Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → FunLike (FC X Y) …
· 使用定理 `CategoryTheory.preservesEpimorphisms_of_preservesColimitsOfShape`：∀ {C :
 Type u₁} {D : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Ca
tegoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
-/
theorem surjective_of_epi_of_preservesPushout {X Y : C} (f : X ⟶ Y) [Epi f]
    [PreservesColimitsOfShape WalkingSpan (forget C)] : Function.Surjective f :=
  (epi_iff_surjective ((forget C).map f)).mp inferInstance
/-
**CategoryTheory.ConcreteCategory.epi_iff_surjective_of_preservesPushout** 是 Mat
hlib 中的一个定理，位于命名空间 `CategoryTheory.ConcreteCategory`。
形式化陈述：epi_iff_surjective_of_preservesPushout {X Y : C} (f : X ⟶ Y) [PreservesCol
imitsOfShape WalkingSpan (forget C)] : Epi f ↔ Function.Surjective f
参数：f : X ⟶ Y；forget C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `CategoryTheory.Functor.epi_map_iff_epi`：epi_map_iff_epi [hF₁ : Preserves
Epimorphisms F] [hF₂ : ReflectsEpimorphisms F] : Epi (F.map f) ↔ Epi f
· 使用定理 `CategoryTheory.preservesEpimorphisms_of_preservesColimitsOfShape`：∀ {C :
 Type u₁} {D : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Ca
tegoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.reflectsEpimorphisms_of_faithful`：∀ {C : Type u₁}
 [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryThe
ory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.instFaithfulForget`：∀ (C : Type u_1) [inst : CategoryTheo
ry.Category.{v_1, u_1} C] {FC : outParam (C → C → Type u_2)}   {CC : outParam (C
 → Type w)} [inst_1 : o…
· 使用定理 `CategoryTheory.epi_iff_surjective`：epi_iff_surjective {X Y : Type u} (f 
: X ⟶ Y) : Epi f ↔ Function.Surjective f
-/
theorem epi_iff_surjective_of_preservesPushout {X Y : C} (f : X ⟶ Y)
    [PreservesColimitsOfShape WalkingSpan (forget C)] : Epi f ↔ Function.Surjective f :=
  ((forget C).epi_map_iff_epi _).symm.trans (epi_iff_surjective _)
/-
**CategoryTheory.ConcreteCategory.bijective_of_isIso** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.ConcreteCategory`。
形式化陈述：bijective_of_isIso {X Y : C} (f : X ⟶ Y) [IsIso f] : Function.Bijective f
参数：f : X ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.bijective_iff_isIso_ofHom`：bijective_iff_isIso_ofHom {X Y
 : Type u} (f : X -> Y) : Function.Bijective f ↔ IsIso (ofHom f)
-/
theorem bijective_of_isIso {X Y : C} (f : X ⟶ Y) [IsIso f] :
    Function.Bijective f := by
  rw [bijective_iff_isIso_ofHom]
  infer_instance

/-- If the forgetful functor of a concrete category reflects isomorphisms, being an isomorphism
is equivalent to being bijective. -/
/-
**CategoryTheory.ConcreteCategory.isIso_iff_bijective** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.ConcreteCategory`。
形式化陈述：isIso_iff_bijective [(forget C).ReflectsIsomorphisms] {X Y : C} (f : X ⟶ Y
) : IsIso f ↔ Function.Bijective f
参数：forget C；f : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.bijective_iff_isIso_ofHom`：bijective_iff_isIso_ofHom {X Y
 : Type u} (f : X -> Y) : Function.Bijective f ↔ IsIso (ofHom f)
· 使用定理 `CategoryTheory.isIso_of_reflects_iso`：isIso_of_reflects_iso {A B : C} (f
 : A ⟶ B) (F : C ⥤ D) [IsIso (F.map f)] [F.ReflectsIsomorphisms] : IsIso f

--- 原说明 ---
If the forgetful functor of a concrete category reflects isomorphisms, being an 
isomorphism
is equivalent to being bijective.
-/
theorem isIso_iff_bijective [(forget C).ReflectsIsomorphisms]
    {X Y : C} (f : X ⟶ Y) : IsIso f ↔ Function.Bijective f := by
  rw [bijective_iff_isIso_ofHom]
  refine ⟨fun _ ↦ inferInstance, fun h ↦ ?_⟩
  have : IsIso ((forget C).map f) := h
  exact isIso_of_reflects_iso f (forget C)

end

end ConcreteCategory

end CategoryTheory

