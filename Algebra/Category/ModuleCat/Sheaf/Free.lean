/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.CategoryTheory.Limits.Preserves.SigmaConst

/-!
# Free sheaves of modules

In this file, we construct the functor
`SheafOfModules.freeFunctor : Type u ⥤ SheafOfModules.{u} R` which sends
a type `I` to the coproduct of copies indexed by `I` of `unit R`.

## TODO

* In case the category `C` has a terminal object `X`, promote `freeHomEquiv`
  into an adjunction between `freeFunctor` and the evaluation functor at `X`.
  (Alternatively, assuming specific universe parameters, we could show that
  `freeFunctor` is a left adjoint to `SheafOfModules.sectionsFunctor`.)

-/

@[expose] public section

universe u v₁ v₂ u₁ u₂
open CategoryTheory Limits

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

namespace SheafOfModules

/-- The free sheaf of modules on a certain type `I`. -/
/-
**SheafOfModules.free** 是 Mathlib 中的一个定义，位于命名空间 `SheafOfModules`。
形式化陈述：free (I : Type u) : SheafOfModules.{u} R
参数：I : Type u。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The free sheaf of modules on a certain type `I`.
-/
noncomputable def free (I : Type u) : SheafOfModules.{u} R := ∐ (fun (_ : I) ↦ unit R)

/-- The inclusions `unit R ⟶ free I`. -/
/-
**SheafOfModules.** 是 Mathlib 中的一个定义，位于命名空间 `SheafOfModules`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusions `unit R ⟶ free I`.
-/
noncomputable def ιFree {I : Type u} (i : I) : unit R ⟶ free I :=
  Sigma.ι (fun (_ : I) ↦ unit R) i

/-- The tautological cofan with point `free I : SheafOfModules R`. -/
/-
**SheafOfModules.freeCofan** 是 Mathlib 中的一个定义，位于命名空间 `SheafOfModules`。
形式化陈述：freeCofan (I : Type u) : Cofan (fun (_ : I) => unit R)
参数：I : Type u。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The tautological cofan with point `free I : SheafOfModules R`.
-/
noncomputable def freeCofan (I : Type u) : Cofan (fun (_ : I) ↦ unit R) :=
  Cofan.mk (P := free I) ιFree

@[simp]
/-
**SheafOfModules.freeCofan_inj** 是 Mathlib 中的一个引理，位于命名空间 `SheafOfModules`。
形式化陈述：freeCofan_inj {I : Type u} (i : I) : (freeCofan (R
参数：i : I。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma freeCofan_inj {I : Type u} (i : I) :
    (freeCofan (R := R) I).inj i = ιFree i := rfl

/-- `free I` is the colimit of copies of `unit R` indexed by `I`. -/
/-
**SheafOfModules.isColimitFreeCofan** 是 Mathlib 中的一个定义，位于命名空间 `SheafOfModules`。
形式化陈述：isColimitFreeCofan (I : Type u) : IsColimit (freeCofan (R
参数：I : Type u。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`free I` is the colimit of copies of `unit R` indexed by `I`.
-/
noncomputable def isColimitFreeCofan (I : Type u) :
    IsColimit (freeCofan (R := R) I) :=
  coproductIsCoproduct _

set_option backward.isDefEq.respectTransparency false in
/-- The data of a morphism `free I ⟶ M` from a free sheaf of modules is
equivalent to the data of a family `I → M.sections` of sections of `M`. -/
/-
**SheafOfModules.freeHomEquiv** 是 Mathlib 中的一个定义，位于命名空间 `SheafOfModules`。
形式化陈述：freeHomEquiv (M : SheafOfModules.{u} R) {I : Type u} : (free I ⟶ M) ≃ (I -
> M.sections) where toFun f i
参数：M : SheafOfModules.{u} R。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The data of a morphism `free I ⟶ M` from a free sheaf of modules is
equivalent to the data of a family `I → M.sections` of sections of `M`.
-/
noncomputable def freeHomEquiv (M : SheafOfModules.{u} R) {I : Type u} :
    (free I ⟶ M) ≃ (I → M.sections) where
  toFun f i := M.unitHomEquiv (ιFree i ≫ f)
  invFun s := Cofan.IsColimit.desc (isColimitFreeCofan I) (fun i ↦ M.unitHomEquiv.symm (s i))
  left_inv s := Cofan.IsColimit.hom_ext (isColimitFreeCofan I) _ _
    (fun i ↦ by simp [← freeCofan_inj])
  right_inv f := by ext1 i; simp [← freeCofan_inj]
/-
**SheafOfModules.freeHomEquiv_comp_apply** 是 Mathlib 中的一个引理，位于命名空间 `SheafOfModul
es`。
形式化陈述：freeHomEquiv_comp_apply {M N : SheafOfModules.{u} R} {I : Type u} (f : fre
e I ⟶ M) (p : M ⟶ N) (i : I) : N.freeHomEquiv (f ≫ p) i = sectionsMap p (M.freeH
omEquiv f i)
参数：f : free I ⟶ M；p : M ⟶ N；i : I。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma freeHomEquiv_comp_apply {M N : SheafOfModules.{u} R} {I : Type u}
    (f : free I ⟶ M) (p : M ⟶ N) (i : I) :
    N.freeHomEquiv (f ≫ p) i = sectionsMap p (M.freeHomEquiv f i) := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**SheafOfModules.freeHomEquiv_symm_comp** 是 Mathlib 中的一个引理，位于命名空间 `SheafOfModule
s`。
形式化陈述：freeHomEquiv_symm_comp {M N : SheafOfModules.{u} R} {I : Type u} (s : I ->
 M.sections) (p : M ⟶ N) : M.freeHomEquiv.symm s ≫ p = N.freeHomEquiv.symm (fun 
i => sectionsMap p (s i))
参数：s : I -> M.sections；p : M ⟶ N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `PresheafOfModules.sections_ext`：sections_ext {M : PresheafOfModules.{v} 
R} (s t : M.sections) (h : forall (X : Cᵒᵖ), s.val X = t.val X) : s = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `PresheafOfModules.sectionsMap_coe`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {R : CategoryTheory.Functor Cᵒᵖ RingCat}   {M N : Preshea
fOfModules R} (f : M ⟶ …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma freeHomEquiv_symm_comp {M N : SheafOfModules.{u} R} {I : Type u} (s : I → M.sections)
    (p : M ⟶ N) :
    M.freeHomEquiv.symm s ≫ p = N.freeHomEquiv.symm (fun i ↦ sectionsMap p (s i)) :=
  N.freeHomEquiv.injective (by ext; simp [freeHomEquiv_comp_apply])

/-- The tautological section of `free I : SheafOfModules R` corresponding to `i : I`. -/
/-
**SheafOfModules.freeSection** 是 Mathlib 中的一个缩写定义，位于命名空间 `SheafOfModules`。
形式化陈述：freeSection {I : Type u} (i : I) : (free (R
参数：i : I。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The tautological section of `free I : SheafOfModules R` corresponding to `i : I`
.
-/
noncomputable abbrev freeSection {I : Type u} (i : I) : (free (R := R) I).sections :=
  (free (R := R) I).freeHomEquiv (𝟙 (free I)) i
/-
**SheafOfModules.freeHomEquiv_apply** 是 Mathlib 中的一个引理，位于命名空间 `SheafOfModules`。
形式化陈述：freeHomEquiv_apply {M : SheafOfModules.{u} R} {I : Type u} (f : free I ⟶ M
) (i : I) : freeHomEquiv M f i = sectionsMap f (freeSection i)
参数：f : free I ⟶ M；i : I。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma freeHomEquiv_apply {M : SheafOfModules.{u} R} {I : Type u}
    (f : free I ⟶ M) (i : I) :
    freeHomEquiv M f i = sectionsMap f (freeSection i) :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply** 是 Mathlib 中的一个引理，位于命名空间 
`SheafOfModules`。
形式化陈述：unitHomEquiv_symm_freeHomEquiv_apply {I : Type u} {M : SheafOfModules.{u} 
R} (f : free I ⟶ M) (i : I) : M.unitHomEquiv.symm (M.freeHomEquiv f i) = ιFree i
 ≫ f
参数：f : free I ⟶ M；i : I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma unitHomEquiv_symm_freeHomEquiv_apply
    {I : Type u} {M : SheafOfModules.{u} R} (f : free I ⟶ M) (i : I) :
    M.unitHomEquiv.symm (M.freeHomEquiv f i) = ιFree i ≫ f := by
  simp [freeHomEquiv]

section

variable {I J : Type u} (f : I → J)

/-- The morphism of presheaves of `R`-modules `free I ⟶ free J` induced by
a map `f : I → J`. -/
/-
**SheafOfModules.freeMap** 是 Mathlib 中的一个定义，位于命名空间 `SheafOfModules`。
形式化陈述：freeMap : free (R
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The morphism of presheaves of `R`-modules `free I ⟶ free J` induced by
a map `f : I → J`.
-/
noncomputable def freeMap : free (R := R) I ⟶ free J :=
  (freeHomEquiv _).symm (fun i ↦ freeSection (f i))

@[simp]
/-
**SheafOfModules.freeHomEquiv_freeMap** 是 Mathlib 中的一个引理，位于命名空间 `SheafOfModules`
。
形式化陈述：freeHomEquiv_freeMap : (freeHomEquiv _ (freeMap (R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
-/
lemma freeHomEquiv_freeMap :
    (freeHomEquiv _ (freeMap (R := R) f)) = freeSection.comp f :=
  (freeHomEquiv _).symm.injective (by simp; rfl)

@[simp]
/-
**SheafOfModules.sectionMap_freeMap_freeSection** 是 Mathlib 中的一个定理，位于命名空间 `Sheaf
OfModules`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {J : CategoryT
heory.GrothendieckTopology C}   {R : CategoryTheory.Sheaf J RingCat} [inst_1 : C
ategoryTheory.HasWeakSheafify J AddCommGrpCat]   [inst_2 : J.WEqualsLocallyBijec
tive AddCommGrpCat] {I J_1 : Type u} (f : I → J_1) (i : I),   SheafOfModules.sec
tionsMap (SheafOfModules.freeMap f) (SheafOfModules.freeSection i) =     SheafOf
Modules.freeSection (f i)
参数：f : I → J_1；i : I；SheafOfModules.freeMap f；SheafOfModules.freeSection i；f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `SheafOfModules.freeHomEquiv_freeMap`：freeHomEquiv_freeMap : (freeHomEqui
v _ (freeMap (R
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma sectionMap_freeMap_freeSection (i : I) :
    sectionsMap (freeMap (R := R) f) (freeSection i) = freeSection (f i) := by
  simp [← freeHomEquiv_comp_apply]
/-
**SheafOfModules.sectionsMap_freeHomEquiv_symm_freeSection** 是 Mathlib 中的一个定理，位于
命名空间 `SheafOfModules`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {J : CategoryT
heory.GrothendieckTopology C}   {R : CategoryTheory.Sheaf J RingCat} [inst_1 : C
ategoryTheory.HasWeakSheafify J AddCommGrpCat]   [inst_2 : J.WEqualsLocallyBijec
tive AddCommGrpCat] {I : Type u} {M : SheafOfModules R} (f : I → M.sections) (i 
: I),   SheafOfModules.sectionsMap (M.freeHomEquiv.symm f) (SheafOfModules.freeS
ection i) = f i
参数：f : I → M.sections；i : I；M.freeHomEquiv.symm f；SheafOfModules.freeSection i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
-/
lemma sectionsMap_freeHomEquiv_symm_freeSection
    {M : SheafOfModules.{u} R} (f : I → M.sections) (i : I) :
    sectionsMap ((freeHomEquiv M).symm f) (freeSection i) = f i := by
  obtain ⟨f, rfl⟩ := (freeHomEquiv M).surjective f
  cat_disch

@[reassoc (attr := simp)]
/-
**SheafOfModules.** 是 Mathlib 中的一个引理，位于命名空间 `SheafOfModules`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ιFree_freeMap (i : I) :
    ιFree (R := R) i ≫ freeMap f = ιFree (f i) := by
  rw [← unitHomEquiv_symm_freeHomEquiv_apply, freeHomEquiv_freeMap]
  dsimp [freeSection]
  rw [unitHomEquiv_symm_freeHomEquiv_apply, Category.comp_id]

end

/-- The functor `Type u ⥤ SheafOfModules.{u} R` which sends a type `I` to
`free I` which is a coproduct indexed by `I` of copies of `R` (thought of as a
presheaf of modules over itself). -/
/-
**SheafOfModules.freeFunctor** 是 Mathlib 中的一个定义，位于命名空间 `SheafOfModules`。
形式化陈述：freeFunctor : Type u ⥤ SheafOfModules.{u} R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `Type u ⥤ SheafOfModules.{u} R` which sends a type `I` to
`free I` which is a coproduct indexed by `I` of copies of `R` (thought of as a
presheaf of modules over itself).
-/
noncomputable def freeFunctor : Type u ⥤ SheafOfModules.{u} R :=
  sigmaConst.obj (unit R)

@[simp]
/-
**SheafOfModules.freeFunctor_obj** 是 Mathlib 中的一个引理，位于命名空间 `SheafOfModules`。
形式化陈述：freeFunctor_obj (X : Type u) : (freeFunctor (R
参数：X : Type u。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma freeFunctor_obj (X : Type u) :
    (freeFunctor (R := R)).obj X = free X := rfl

@[simp]
/-
**SheafOfModules.freeFunctor_map** 是 Mathlib 中的一个引理，位于命名空间 `SheafOfModules`。
形式化陈述：freeFunctor_map {X Y : Type u} (f : X ⟶ Y) : dsimp% (freeFunctor (R
参数：f : X ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Cofan.IsColimit.hom_ext`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] {I : Type u_1} {F : I → C} {c : CategoryTheory.L
imits.Cofan F}   (hc : CategoryTheo…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.Sigma.ι_desc`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {β : Type w} {f : β → C}   [inst_1 : CategoryTheory.Limits.
HasCoproduct f] {P : C} …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `SheafOfModules.ιFree_freeMap`：ιFree_freeMap (i : I) : ιFree (R
-/
lemma freeFunctor_map {X Y : Type u} (f : X ⟶ Y) :
    dsimp% (freeFunctor (R := R)).map f = freeMap f :=
  Cofan.IsColimit.hom_ext (isColimitFreeCofan _) _ _
    (fun i ↦ (Sigma.ι_desc _ _).trans (ιFree_freeMap f i).symm)
/-
**SheafOfModules.** 是 Mathlib 中的一个实例，位于命名空间 `SheafOfModules`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PreservesColimitsOfSize.{v₂, u₂} (freeFunctor (R := R)) :=
  inferInstanceAs (PreservesColimitsOfSize.{v₂, u₂} (sigmaConst.obj _))

section

variable (I J : Type u)

/-- A binary coproduct of free sheaves of modules is the free sheaf
of modules on the sum type. -/
/-
**SheafOfModules.freeSumIso** 是 Mathlib 中的一个定义，位于命名空间 `SheafOfModules`。
形式化陈述：freeSumIso : free I ⨿ free J ≅ free (R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A binary coproduct of free sheaves of modules is the free sheaf
of modules on the sum type.
-/
noncomputable def freeSumIso : free I ⨿ free J ≅ free (R := R) (I ⊕ J) :=
  IsColimit.coconePointUniqueUpToIso
    (coprodIsCoprod (free (R := R) I) (free J))
    (mapIsColimitOfPreservesOfIsColimit (freeFunctor (R := R)) _ _
      (Types.binaryCoproductColimit I J))

@[reassoc (attr := simp)]
/-
**SheafOfModules.inl_freeSumIso_hom** 是 Mathlib 中的一个引理，位于命名空间 `SheafOfModules`。
形式化陈述：inl_freeSumIso_hom : coprod.inl ≫ (freeSumIso (R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.hasFiniteCoproducts_of_hasFiniteColimits`：∀ (C : T
ype u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFinit
eColimits C],   CategoryTheory.Limits.HasFiniteCopro…
· 使用定理 `CategoryTheory.Limits.hasFiniteColimits_of_hasColimitsOfSize₀`：∀ (C : Ty
pe u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasColimi
tsOfSize.{0, 0, v, u} C],   CategoryTheory.Limits.H…
· 使用定理 `SheafOfModules.instHasColimitsOfSizeOfPresheafOfModulesObjFunctorOpposit
eRingCatIsSheaf`：∀ {C : Type u'} [inst : CategoryTheory.Category.{v', u'} C] {J 
: CategoryTheory.GrothendieckTopology C}   (R : CategoryTheory.Sheaf J RingCa…
· 使用定理 `PresheafOfModules.hasColimitsOfSize`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] (R : CategoryTheory.Functor Cᵒᵖ RingCat)   [CategoryThe
ory.Limits.HasColimitsOfS…
· 使用定理 `AddCommGrpCat.hasColimitsOfSize`：∀ [UnivLE.{u, w}], CategoryTheory.Limit
s.HasColimitsOfSize.{v, u, w, w + 1} AddCommGrpCat
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `SheafOfModules.freeFunctor_map`：freeFunctor_map {X Y : Type u} (f : X ⟶ 
Y) : dsimp% (freeFunctor (R
· 使用定理 `CategoryTheory.Limits.IsColimit.comp_coconePointUniqueUpToIso_hom`：∀ {J 
: Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : C
ategoryTheory.Category.{v₃, u₃} C]   {F : CategoryTheor…
-/
lemma inl_freeSumIso_hom :
    coprod.inl ≫ (freeSumIso (R := R) I J).hom = freeMap Sum.inl := by
  rw [← dsimp% freeFunctor_map (↾(Sum.inl : I → I ⊕ J))]
  exact IsColimit.comp_coconePointUniqueUpToIso_hom
    (coprodIsCoprod (free (R := R) I) (free J)) _ (.mk .left)

@[reassoc (attr := simp)]
/-
**SheafOfModules.inr_freeSumIso_hom** 是 Mathlib 中的一个引理，位于命名空间 `SheafOfModules`。
形式化陈述：inr_freeSumIso_hom : coprod.inr ≫ (freeSumIso (R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.hasFiniteCoproducts_of_hasFiniteColimits`：∀ (C : T
ype u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFinit
eColimits C],   CategoryTheory.Limits.HasFiniteCopro…
· 使用定理 `CategoryTheory.Limits.hasFiniteColimits_of_hasColimitsOfSize₀`：∀ (C : Ty
pe u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasColimi
tsOfSize.{0, 0, v, u} C],   CategoryTheory.Limits.H…
· 使用定理 `SheafOfModules.instHasColimitsOfSizeOfPresheafOfModulesObjFunctorOpposit
eRingCatIsSheaf`：∀ {C : Type u'} [inst : CategoryTheory.Category.{v', u'} C] {J 
: CategoryTheory.GrothendieckTopology C}   (R : CategoryTheory.Sheaf J RingCa…
· 使用定理 `PresheafOfModules.hasColimitsOfSize`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] (R : CategoryTheory.Functor Cᵒᵖ RingCat)   [CategoryThe
ory.Limits.HasColimitsOfS…
· 使用定理 `AddCommGrpCat.hasColimitsOfSize`：∀ [UnivLE.{u, w}], CategoryTheory.Limit
s.HasColimitsOfSize.{v, u, w, w + 1} AddCommGrpCat
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `SheafOfModules.freeFunctor_map`：freeFunctor_map {X Y : Type u} (f : X ⟶ 
Y) : dsimp% (freeFunctor (R
· 使用定理 `CategoryTheory.Limits.IsColimit.comp_coconePointUniqueUpToIso_hom`：∀ {J 
: Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : C
ategoryTheory.Category.{v₃, u₃} C]   {F : CategoryTheor…
-/
lemma inr_freeSumIso_hom :
    coprod.inr ≫ (freeSumIso (R := R) I J).hom = freeMap Sum.inr := by
  rw [← dsimp% freeFunctor_map (↾(Sum.inr : J → I ⊕ J))]
  exact IsColimit.comp_coconePointUniqueUpToIso_hom
    (coprodIsCoprod (free (R := R) I) (free J)) _ (.mk .right)

end

section

variable {C' : Type u₂} [Category.{v₂} C'] {J' : GrothendieckTopology C'} {S : Sheaf J' RingCat.{u}}
  [HasSheafify J' AddCommGrpCat.{u}] [J'.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (F : SheafOfModules.{u} R ⥤ SheafOfModules.{u} S) (I : Type u)

/-- Let `F` be a functor from the category of sheaves of `R`-modules to sheaves of `S`-modules.
Then a morphism `η : unit S ⟶ F.obj (unit R)` induces a morphism from `free (R := S) I` to
`F.obj (free I)`. See also `mapFreeIso` for the iso version. -/
/-
**SheafOfModules.mapFree** 是 Mathlib 中的一个定义，位于命名空间 `SheafOfModules`。
形式化陈述：mapFree (η : unit S ⟶ F.obj (unit R)) : free (R
参数：η : unit S ⟶ F.obj (unit R)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instHasWeakSheafifyOfHasSheafify`：∀ {C : Type u₁} [inst :
 CategoryTheory.Category.{v₁, u₁} C] (J : CategoryTheory.GrothendieckTopology C)
 (A : Type u₂)   [inst_1 : CategoryTh…

--- 原说明 ---
Let `F` be a functor from the category of sheaves of `R`-modules to sheaves of `
S`-modules.
Then a morphism `η : unit S ⟶ F.obj (unit R)` induces a morphism from `free (R :
= S) I` to
`F.obj (free I)`. See also `mapFreeIso` for the iso version.
-/
noncomputable def mapFree (η : unit S ⟶ F.obj (unit R)) : free (R := S) I ⟶ F.obj (free I) :=
  (isColimitFreeCofan I).map (F.mapCocone (freeCofan I)) (Discrete.natTrans fun _ ↦ η)

@[reassoc (attr := simp)]
/-
**SheafOfModules.** 是 Mathlib 中的一个引理，位于命名空间 `SheafOfModules`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ιFree_mapFree (η : unit S ⟶ F.obj (unit R)) (i : I) :
    ιFree i ≫ mapFree F I η = η ≫ F.map (ιFree i) :=
  IsColimit.ι_map (isColimitFreeCofan I) (F.mapCocone (freeCofan I))
    (Discrete.natTrans fun _ ↦ η) (Discrete.mk i)

variable [PreservesColimitsOfShape (Discrete I) F]

/-- Let `F` be a functor from the category of sheaves of `R`-modules to sheaves of `S`-modules.
If `F` preserves coproducts and `unit S ≅ F.obj (unit R)`, then `F` preserves free sheaves of
modules. -/
/-
**SheafOfModules.mapFreeIso** 是 Mathlib 中的一个定义，位于命名空间 `SheafOfModules`。
形式化陈述：mapFreeIso (η : unit S ≅ F.obj (unit R)) : free (R
参数：η : unit S ≅ F.obj (unit R)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instHasWeakSheafifyOfHasSheafify`：∀ {C : Type u₁} [inst :
 CategoryTheory.Category.{v₁, u₁} C] (J : CategoryTheory.GrothendieckTopology C)
 (A : Type u₂)   [inst_1 : CategoryTh…

--- 原说明 ---
Let `F` be a functor from the category of sheaves of `R`-modules to sheaves of `
S`-modules.
If `F` preserves coproducts and `unit S ≅ F.obj (unit R)`, then `F` preserves fr
ee sheaves of
modules.
-/
noncomputable def mapFreeIso (η : unit S ≅ F.obj (unit R)) : free (R := S) I ≅ F.obj (free I) :=
  (isColimitFreeCofan I).coconePointsIsoOfNatIso (isColimitOfPreserves F (isColimitFreeCofan I))
    (Discrete.natIso fun _ ↦ η)
/-
**SheafOfModules.mapFreeIso_hom** 是 Mathlib 中的一个引理，位于命名空间 `SheafOfModules`。
形式化陈述：mapFreeIso_hom (η : unit S ≅ F.obj (unit R)) : (mapFreeIso F I η).hom = ma
pFree F I η.hom
参数：η : unit S ≅ F.obj (unit R)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instHasWeakSheafifyOfHasSheafify`：∀ {C : Type u₁} [inst :
 CategoryTheory.Category.{v₁, u₁} C] (J : CategoryTheory.GrothendieckTopology C)
 (A : Type u₂)   [inst_1 : CategoryTh…
-/
lemma mapFreeIso_hom (η : unit S ≅ F.obj (unit R)) :
    (mapFreeIso F I η).hom = mapFree F I η.hom := rfl

@[reassoc (attr := simp)]
/-
**SheafOfModules.** 是 Mathlib 中的一个引理，位于命名空间 `SheafOfModules`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ιFree_mapFreeIso_hom (η : unit S ≅ F.obj (unit R)) (i : I) :
    ιFree i ≫ (mapFreeIso F I η).hom = η.hom ≫ F.map (ιFree i) :=
  ιFree_mapFree _ _ _ _

@[deprecated (since := "2026-04-21")] alias ιFree_mapFree_inv := ιFree_mapFreeIso_hom

@[reassoc (attr := simp)]
/-
**SheafOfModules.map_** 是 Mathlib 中的一个引理，位于命名空间 `SheafOfModules`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map_ιFree_mapFreeIso_inv (η : unit S ≅ F.obj (unit R)) (i : I) :
    F.map (ιFree i) ≫ (mapFreeIso F I η).inv = η.inv ≫ ιFree i :=
  IsColimit.ι_map (isColimitOfPreserves F (isColimitFreeCofan I)) (freeCofan I)
    (Discrete.natTrans fun _ ↦ η.inv) (Discrete.mk i)

@[deprecated (since := "2026-04-21")] alias map_ιFree_mapFree_hom := map_ιFree_mapFreeIso_inv

end

end SheafOfModules

