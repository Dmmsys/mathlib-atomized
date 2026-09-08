/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts

/-!
# Pushforward of sheaves of modules

Assume that categories `C` and `D` are equipped with Grothendieck topologies, and
that `F : C ⥤ D` is a continuous functor.
Then, if `φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R` is
a morphism of sheaves of rings, we construct the pushforward functor
`pushforward φ : SheafOfModules.{v} R ⥤ SheafOfModules.{v} S`, and
we show that they interact with the composition of morphisms similarly as pseudofunctors.

-/

@[expose] public section

universe w v' u' v v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄ u

open CategoryTheory Functor Limits

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {D' : Type u₃} [Category.{v₃} D'] {D'' : Type u₄} [Category.{v₄} D'']
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
  {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
  [Functor.IsContinuous F J K]
  (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)

/-- The pushforward of sheaves of modules that is induced by a continuous functor `F`
and a morphism of sheaves of rings `φ : S ⟶ (F.sheafPushforwardContinuous RingCat J K).obj R`. -/
@[simps map_val, simps -isSimp obj_val]
/-
**SheafOfModules.pushforward** 是 Mathlib 中的一个定义，位于命名空间 `SheafOfModules`。
形式化陈述：pushforward : SheafOfModules.{v} R ⥤ SheafOfModules.{v} S where obj M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pushforward of sheaves of modules that is induced by a continuous functor `F
`
and a morphism of sheaves of rings `φ : S ⟶ (F.sheafPushforwardContinuous RingCa
t J K).obj R`.
-/
noncomputable def pushforward : SheafOfModules.{v} R ⥤ SheafOfModules.{v} S where
  obj M :=
    { val := (PresheafOfModules.pushforward φ.hom).obj M.val
      isSheaf := ((F.sheafPushforwardContinuous _ J K).obj ⟨_, M.isSheaf⟩).property }
  map f :=
    { val := (PresheafOfModules.pushforward φ.hom).map f.val }
/-
**SheafOfModules.forget** 是 Mathlib 中的一个定义，位于命名空间 `SheafOfModules`。
形式化陈述：forget : SheafOfModules.{v} R ⥤ PresheafOfModules R.obj where obj F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma forget₂_map_pushforward_obj_val_map {U V : Cᵒᵖ} (f : U ⟶ V) (M) :
    (forget₂ _ Ab).map (((pushforward.{v} φ).obj M).val.map f) =
      M.val.presheaf.map (F.map f.unop).op :=
  rfl

variable (R) in
/-- The restriction functor from sheaves of `R`-modules to sheaves of `R.over X`-modules
for some `X : D`. -/
/-
**SheafOfModules.overFunctor** 是 Mathlib 中的一个定义，位于命名空间 `SheafOfModules`。
形式化陈述：overFunctor (X : D) : SheafOfModules.{v} R ⥤ SheafOfModules.{v} (R.over X)
参数：X : D。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.instIsContinuousOverForgetOver`：∀ {C
 : Type u} [inst : CategoryTheory.Category.{v, u} C] (J : CategoryTheory.Grothen
dieckTopology C) (X : C),   (CategoryTheory.Over.forget …

--- 原说明 ---
The restriction functor from sheaves of `R`-modules to sheaves of `R.over X`-mod
ules
for some `X : D`.
-/
noncomputable def overFunctor (X : D) :
    SheafOfModules.{v} R ⥤ SheafOfModules.{v} (R.over X) :=
  pushforward (𝟙 _)

/-- Given `M : SheafOfModules R` and `X : D`, this is the restriction of `M`
over the sheaf of rings `R.over X` on the category `Over X`. -/
/-
**SheafOfModules.over** 是 Mathlib 中的一个缩写定义，位于命名空间 `SheafOfModules`。
形式化陈述：over (M : SheafOfModules.{v} R) (X : D) : SheafOfModules.{v} (R.over X)
参数：M : SheafOfModules.{v} R；X : D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `M : SheafOfModules R` and `X : D`, this is the restriction of `M`
over the sheaf of rings `R.over X` on the category `Over X`.
-/
noncomputable abbrev over (M : SheafOfModules.{v} R) (X : D) : SheafOfModules.{v} (R.over X) :=
  (overFunctor R X).obj M

/-- Given a map `f : M ⟶ N` between sheaves of modules over `R`, this is the restriction
to the map `M.over X ⟶ N.over X` between sheaves of modules over `R.over X`. -/
/-
**SheafOfModules.Hom.over** 是 Mathlib 中的一个定义，位于命名空间 `SheafOfModules.Hom`。
形式化陈述：{D : Type u₂} →   [inst : CategoryTheory.Category.{v₂, u₂} D] →     {K : C
ategoryTheory.GrothendieckTopology D} →       {R : CategoryTheory.Sheaf K RingCa
t} → {M N : SheafOfModules R} → (M ⟶ N) → (X : D) → M.over X ⟶ N.over X
参数：M ⟶ N；X : D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a map `f : M ⟶ N` between sheaves of modules over `R`, this is the restric
tion
to the map `M.over X ⟶ N.over X` between sheaves of modules over `R.over X`.
-/
noncomputable abbrev Hom.over {M N : SheafOfModules.{v} R} (f : M ⟶ N) (X : D) :
    M.over X ⟶ N.over X :=
  (overFunctor R X).map f

variable (R) in
/-- If `f : X ⟶ Y`, this is the pushforward of sheaves of modules along `Over.map f`. -/
/-
**SheafOfModules.overMap** 是 Mathlib 中的一个定义，位于命名空间 `SheafOfModules`。
形式化陈述：overMap {X Y : D} (f : X ⟶ Y) : SheafOfModules.{v} (R.over Y) ⥤ SheafOfMod
ules.{v} (R.over X)
参数：f : X ⟶ Y。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.instIsContinuousOverMapOver`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] (J : CategoryTheory.Grothendie
ckTopology C) {X Y : C}   (f : X ⟶ Y), (CategoryTheor…

--- 原说明 ---
If `f : X ⟶ Y`, this is the pushforward of sheaves of modules along `Over.map f`
.
-/
noncomputable def overMap {X Y : D} (f : X ⟶ Y) :
    SheafOfModules.{v} (R.over Y) ⥤ SheafOfModules.{v} (R.over X) :=
  pushforward (F := Over.map f) (Sheaf.pushforwardOverMapIso R f).inv

variable (R) in
/-- First restricting to `Over Y` and then extending to `Over X` is the same as restricting to
`Over X`. -/
/-
**SheafOfModules.overFunctorMap** 是 Mathlib 中的一个定义，位于命名空间 `SheafOfModules`。
形式化陈述：overFunctorMap {X Y : D} (f : X ⟶ Y) : overFunctor.{v} R Y ⋙ overMap.{v} R
 f ≅ overFunctor.{v} R X
参数：f : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
First restricting to `Over Y` and then extending to `Over X` is the same as rest
ricting to
`Over X`.
-/
noncomputable def overFunctorMap {X Y : D} (f : X ⟶ Y) :
    overFunctor.{v} R Y ⋙ overMap.{v} R f ≅ overFunctor.{v} R X :=
  NatIso.ofComponents
    fun M ↦ (SheafOfModules.fullyFaithfulForget _).preimageIso <|
      PresheafOfModules.isoMk (fun U ↦ Iso.refl _)

/-- The pushforward of `R.over Y` along `Over.map f` is isomorphic to `R.over X`. -/
@[simps! +dsimpLhs]
/-
**SheafOfModules.overMapUnitIso** 是 Mathlib 中的一个定义，位于命名空间 `SheafOfModules`。
形式化陈述：overMapUnitIso {X Y : D} (f : X ⟶ Y) : (overMap.{u} R f).obj (.unit (R.ove
r Y)) ≅ .unit (R.over X)
参数：f : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pushforward of `R.over Y` along `Over.map f` is isomorphic to `R.over X`.
-/
noncomputable def overMapUnitIso {X Y : D} (f : X ⟶ Y) :
    (overMap.{u} R f).obj (.unit (R.over Y)) ≅ .unit (R.over X) :=
  Iso.refl _

variable (R) in
/-- If `f : X ⟶ Y`, this is the pushforward of sheaves of modules along `Over.pullback f`. -/
/-
**SheafOfModules.overPullback** 是 Mathlib 中的一个定义，位于命名空间 `SheafOfModules`。
形式化陈述：overPullback [Limits.HasPullbacks D] {X Y : D} (f : X ⟶ Y) : SheafOfModule
s.{v} (R.over X) ⥤ SheafOfModules.{v} (R.over Y)
参数：f : X ⟶ Y。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.instIsContinuousOverPullbackOver`：∀ 
{C : Type u} [inst : CategoryTheory.Category.{v, u} C] (J : CategoryTheory.Groth
endieckTopology C)   [inst_1 : CategoryTheory.Limits.HasPu…

--- 原说明 ---
If `f : X ⟶ Y`, this is the pushforward of sheaves of modules along `Over.pullba
ck f`.
-/
noncomputable def overPullback [Limits.HasPullbacks D] {X Y : D} (f : X ⟶ Y) :
    SheafOfModules.{v} (R.over X) ⥤ SheafOfModules.{v} (R.over Y) :=
  pushforward (F := Over.pullback f) (Sheaf.toPushforwardOverPullback R f)

section

variable (R) in
/-- The pushforward functor by the identity morphism identifies to
the identify functor of the category of sheaves of modules. -/
/-
**SheafOfModules.pushforwardId** 是 Mathlib 中的一个定义，位于命名空间 `SheafOfModules`。
形式化陈述：pushforwardId : pushforward.{v} (S
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pushforward functor by the identity morphism identifies to
the identify functor of the category of sheaves of modules.
-/
noncomputable def pushforwardId :
    pushforward.{v} (S := R) (F := 𝟭 _) (𝟙 R) ≅ 𝟭 _ :=
  Iso.refl _

/-- Pushforwards along equal morphisms of sheaves of rings are isomorphic. -/
noncomputable
/-
**SheafOfModules.pushforwardCongr** 是 Mathlib 中的一个定义，位于命名空间 `SheafOfModules`。
形式化陈述：pushforwardCongr {φ ψ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K)
.obj R} (e : φ = ψ) : pushforward.{v} φ ≅ pushforward.{v} ψ
参数：F.sheafPushforwardContinuous RingCat.{u} J K；e : φ = ψ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def pushforwardCongr {φ ψ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R} (e : φ = ψ) :
    pushforward.{v} φ ≅ pushforward.{v} ψ :=
  NatIso.ofComponents (fun X ↦ (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun U ↦ (ModuleCat.restrictScalarsCongr (by subst e; rfl)).app _)
      fun _ _ _ ↦ by subst e; rfl)) fun _ ↦ by subst e; rfl
/-
**SheafOfModules.pushforwardCongr_symm** 是 Mathlib 中的一个定理，位于命名空间 `SheafOfModules
`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {J : CategoryTheory.Grothendieck
Topology C} {K : CategoryTheory.GrothendieckTopology D}   {F : CategoryTheory.Fu
nctor C D} {S : CategoryTheory.Sheaf J RingCat} {R : CategoryTheory.Sheaf K Ring
Cat}   [inst_2 : F.IsContinuous J K] {φ ψ : S ⟶ (F.sheafPushforwardContinuous Ri
ngCat J K).obj R} (e : φ = ψ),   (SheafOfModules.pushforwardCongr e).symm = Shea
fOfModules.pushforwardCongr ⋯
参数：F.sheafPushforwardContinuous RingCat J K；e : φ = ψ；SheafOfModules.pushforward
Congr e。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma pushforwardCongr_symm
    {φ ψ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R} (e : φ = ψ) :
  (pushforwardCongr e).symm = pushforwardCongr e.symm := rfl
/-
**SheafOfModules.pushforwardCongr_hom_app_val_app** 是 Mathlib 中的一个定理，位于命名空间 `She
afOfModules`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {J : CategoryTheory.Grothendieck
Topology C} {K : CategoryTheory.GrothendieckTopology D}   {F : CategoryTheory.Fu
nctor C D} {S : CategoryTheory.Sheaf J RingCat} {R : CategoryTheory.Sheaf K Ring
Cat}   [inst_2 : F.IsContinuous J K] {φ ψ : S ⟶ (F.sheafPushforwardContinuous Ri
ngCat J K).obj R} (e : φ = ψ)   (M : SheafOfModules R) (U : Cᵒᵖ) (x : ↑(((SheafO
fModules.pushforward φ).obj M).val.obj U)),   (CategoryTheory.ConcreteCategory.h
om (((SheafOfModules.pushforwardCongr e).hom.app M).val.app U)) x = x
参数：F.sheafPushforwardContinuous RingCat J K；e : φ = ψ；M : SheafOfModules R；U : C
ᵒᵖ；x : ↑(((SheafOfModules.pushforward φ).obj M).val.obj U)；CategoryTheory.Concre
teCategory.hom (((SheafOfModules.pushforwardCongr e).hom.app M).val.app U)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma pushforwardCongr_hom_app_val_app
    {φ ψ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R} (e : φ = ψ) (M U x) :
  ((pushforwardCongr e).hom.app M).val.app U x = x := rfl
/-
**SheafOfModules.pushforwardCongr_inv_app_val_app** 是 Mathlib 中的一个定理，位于命名空间 `She
afOfModules`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {J : CategoryTheory.Grothendieck
Topology C} {K : CategoryTheory.GrothendieckTopology D}   {F : CategoryTheory.Fu
nctor C D} {S : CategoryTheory.Sheaf J RingCat} {R : CategoryTheory.Sheaf K Ring
Cat}   [inst_2 : F.IsContinuous J K] {φ ψ : S ⟶ (F.sheafPushforwardContinuous Ri
ngCat J K).obj R} (e : φ = ψ)   (M : SheafOfModules R) (U : Cᵒᵖ) (x : ↑(((SheafO
fModules.pushforward ψ).obj M).val.obj U)),   (CategoryTheory.ConcreteCategory.h
om (((SheafOfModules.pushforwardCongr e).inv.app M).val.app U)) x = x
参数：F.sheafPushforwardContinuous RingCat J K；e : φ = ψ；M : SheafOfModules R；U : C
ᵒᵖ；x : ↑(((SheafOfModules.pushforward ψ).obj M).val.obj U)；CategoryTheory.Concre
teCategory.hom (((SheafOfModules.pushforwardCongr e).inv.app M).val.app U)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma pushforwardCongr_inv_app_val_app
    {φ ψ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R} (e : φ = ψ) (M U x) :
  ((pushforwardCongr e).inv.app M).val.app U x = x := rfl

section

variable {K' : GrothendieckTopology D'} {K'' : GrothendieckTopology D''}
  {G : D ⥤ D'} {R' : Sheaf K' RingCat.{u}}
  [Functor.IsContinuous G K K']
  (ψ : R ⟶ (G.sheafPushforwardContinuous RingCat.{u} K K').obj R')

/-- The composition of two pushforward functors on categories of sheaves of modules
identify to the pushforward for the composition. -/
/-
**SheafOfModules.pushforwardComp** 是 Mathlib 中的一个定义，位于命名空间 `SheafOfModules`。
形式化陈述：pushforwardComp : haveI : Functor.IsContinuous (F ⋙ G) J K'
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The composition of two pushforward functors on categories of sheaves of modules
identify to the pushforward for the composition.
-/
noncomputable def pushforwardComp :
    haveI : Functor.IsContinuous (F ⋙ G) J K' := Functor.isContinuous_comp _ _ _ K _
    pushforward.{v} ψ ⋙ pushforward.{v} φ ≅
      pushforward.{v} (F := F ⋙ G) (φ ≫ (F.sheafPushforwardContinuous RingCat.{u} J K).map ψ) :=
  Iso.refl _

-- Not a simp because the type of the LHS is dsimp-able
/-
**SheafOfModules.pushforwardComp_hom_app_val_app** 是 Mathlib 中的一个引理，位于命名空间 `Shea
fOfModules`。
形式化陈述：pushforwardComp_hom_app_val_app (M U x) : ((pushforwardComp φ ψ).hom.app M
).val.app U x = x
参数：M U x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.isContinuous_comp`：isContinuous_comp (F₁ : C ⥤ D)
 (F₂ : D ⥤ E) (J : GrothendieckTopology C) (K : GrothendieckTopology D) (L : Gro
thendieckTopology E) [Functor.…
-/
lemma pushforwardComp_hom_app_val_app (M U x) :
  ((pushforwardComp φ ψ).hom.app M).val.app U x = x := rfl

-- Not a simp because the type of the LHS is dsimp-able
/-
**SheafOfModules.pushforwardComp_inv_app_val_app** 是 Mathlib 中的一个引理，位于命名空间 `Shea
fOfModules`。
形式化陈述：pushforwardComp_inv_app_val_app (M U x) : ((pushforwardComp φ ψ).inv.app M
).val.app U x = x
参数：M U x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.isContinuous_comp`：isContinuous_comp (F₁ : C ⥤ D)
 (F₂ : D ⥤ E) (J : GrothendieckTopology C) (K : GrothendieckTopology D) (L : Gro
thendieckTopology E) [Functor.…
-/
lemma pushforwardComp_inv_app_val_app (M U x) :
  ((pushforwardComp φ ψ).inv.app M).val.app U x = x := rfl

variable {G' : D' ⥤ D''} {R'' : Sheaf K'' RingCat.{u}}
  [Functor.IsContinuous G' K' K'']
  [Functor.IsContinuous (G ⋙ G') K K'']
  [(F ⋙ G).IsContinuous J K']
  (ψ' : R' ⟶ (G'.sheafPushforwardContinuous RingCat.{u} K' K'').obj R'')
/-
**SheafOfModules.pushforward_assoc** 是 Mathlib 中的一个引理，位于命名空间 `SheafOfModules`。
形式化陈述：pushforward_assoc : (pushforward ψ').isoWhiskerLeft (pushforwardComp φ ψ) 
≪≫ pushforwardComp (F
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用引理 `CategoryTheory.Functor.isContinuous_comp`：isContinuous_comp (F₁ : C ⥤ D)
 (F₂ : D ⥤ E) (J : GrothendieckTopology C) (K : GrothendieckTopology D) (L : Gro
thendieckTopology E) [Functor.…
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `SheafOfModules.hom_ext`：hom_ext {X Y : SheafOfModules.{v} R} {f g : X ⟶ 
Y} (h : f.val = g.val) : f = g
· 使用引理 `PresheafOfModules.hom_ext`：hom_ext {f g : M₁ ⟶ M₂} (h : forall (X : Cᵒᵖ)
, f.app X = g.app X) : f = g
· 使用引理 `ModuleCat.hom_ext`：hom_ext {M N : ModuleCat.{v} R} {f g : M ⟶ N} (hf : f
.hom = g.hom) : f = g
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
-/
lemma pushforward_assoc :
    (pushforward ψ').isoWhiskerLeft (pushforwardComp φ ψ) ≪≫
      pushforwardComp (F := F ⋙ G)
        (φ ≫ (F.sheafPushforwardContinuous RingCat.{u} J K).map ψ) ψ' =
    ((pushforward ψ').associator (pushforward ψ) (pushforward φ)).symm ≪≫
      isoWhiskerRight (pushforwardComp ψ ψ') (pushforward φ) ≪≫
      pushforwardComp (G := G ⋙ G') φ (ψ ≫
        (G.sheafPushforwardContinuous RingCat.{u} K K').map ψ') := by ext; rfl

end

/-
**SheafOfModules.pushforward_comp_id** 是 Mathlib 中的一个引理，位于命名空间 `SheafOfModules`。
形式化陈述：pushforward_comp_id : pushforwardComp.{v} (F
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用引理 `CategoryTheory.Functor.isContinuous_comp`：isContinuous_comp (F₁ : C ⥤ D)
 (F₂ : D ⥤ E) (J : GrothendieckTopology C) (K : GrothendieckTopology D) (L : Gro
thendieckTopology E) [Functor.…
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `SheafOfModules.hom_ext`：hom_ext {X Y : SheafOfModules.{v} R} {f g : X ⟶ 
Y} (h : f.val = g.val) : f = g
· 使用引理 `PresheafOfModules.hom_ext`：hom_ext {f g : M₁ ⟶ M₂} (h : forall (X : Cᵒᵖ)
, f.app X = g.app X) : f = g
· 使用引理 `ModuleCat.hom_ext`：hom_ext {M N : ModuleCat.{v} R} {f g : M ⟶ N} (hf : f
.hom = g.hom) : f = g
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
-/
lemma pushforward_comp_id :
    pushforwardComp.{v} (F := 𝟭 C) (𝟙 S) φ =
      isoWhiskerLeft (pushforward.{v} φ) (pushforwardId S) ≪≫ rightUnitor _ := by ext; rfl
/-
**SheafOfModules.pushforward_id_comp** 是 Mathlib 中的一个引理，位于命名空间 `SheafOfModules`。
形式化陈述：pushforward_id_comp : pushforwardComp.{v} (G
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用引理 `CategoryTheory.Functor.isContinuous_comp`：isContinuous_comp (F₁ : C ⥤ D)
 (F₂ : D ⥤ E) (J : GrothendieckTopology C) (K : GrothendieckTopology D) (L : Gro
thendieckTopology E) [Functor.…
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `SheafOfModules.hom_ext`：hom_ext {X Y : SheafOfModules.{v} R} {f g : X ⟶ 
Y} (h : f.val = g.val) : f = g
· 使用引理 `PresheafOfModules.hom_ext`：hom_ext {f g : M₁ ⟶ M₂} (h : forall (X : Cᵒᵖ)
, f.app X = g.app X) : f = g
· 使用引理 `ModuleCat.hom_ext`：hom_ext {M N : ModuleCat.{v} R} {f g : M ⟶ N} (hf : f
.hom = g.hom) : f = g
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
-/
lemma pushforward_id_comp :
    pushforwardComp.{v} (G := 𝟭 _) φ (𝟙 R) =
      isoWhiskerRight (pushforwardId R) (pushforward.{v} φ) ≪≫ leftUnitor _ := by ext; rfl

end

section NatTrans

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {F G H : C ⥤ D} {T : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
  [Functor.IsContinuous F J K]
  [Functor.IsContinuous G J K]
  [Functor.IsContinuous H J K]
  (φ : T ⟶ (G.sheafPushforwardContinuous RingCat.{u} J K).obj S)

/-- A natural transformation gives a natural transformation between the pushforward functors. -/
noncomputable
/-
**SheafOfModules.pushforwardNatTrans** 是 Mathlib 中的一个定义，位于命名空间 `SheafOfModules`。
形式化陈述：pushforwardNatTrans (α : F ⟶ G) : pushforward.{v} φ ⟶ pushforward.{v} (φ ≫
 (Functor.sheafPushforwardContinuousNatTrans α _ _ _).app S) where app X
参数：α : F ⟶ G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def pushforwardNatTrans (α : F ⟶ G) :
    pushforward.{v} φ ⟶
      pushforward.{v} (φ ≫ (Functor.sheafPushforwardContinuousNatTrans α _ _ _).app S) where
  app X :=
  { val.app U := (ModuleCat.restrictScalars (φ.hom.app U).hom).map (X.val.map (α.app U.unop).op)
    val.naturality {U V} i := by
      ext x
      dsimp
      change (X.val.presheaf.map (G.map i.unop).op ≫ X.val.presheaf.map (α.app V.unop).op) _ =
        (X.val.presheaf.map (α.app U.unop).op ≫ X.val.presheaf.map (F.map i.unop).op) _
      simp only [← CategoryTheory.Functor.map_comp, ← op_comp, α.naturality] }
  naturality {X Y} f := by
    ext U x
    exact congr($(f.val.naturality (α.app U.unop).op) x).symm
/-
**SheafOfModules.pushforwardNatTrans_app_val_app** 是 Mathlib 中的一个定理，位于命名空间 `Shea
fOfModules`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {J : CategoryTheory.Grothendieck
Topology C} {K : CategoryTheory.GrothendieckTopology D}   {F G : CategoryTheory.
Functor C D} {T : CategoryTheory.Sheaf J RingCat} {S : CategoryTheory.Sheaf K Ri
ngCat}   [inst_2 : F.IsContinuous J K] [inst_3 : G.IsContinuous J K] (φ : T ⟶ (G
.sheafPushforwardContinuous RingCat J K).obj S)   (α : F ⟶ G) (M : SheafOfModule
s S) (U : Cᵒᵖ) (x : ↑(((SheafOfModules.pushforward φ).obj M).val.obj U)),   (Cat
egoryTheory.ConcreteCategory.hom (((SheafOfModules.pushforwardNatTrans φ α).app 
M).val.app U)) x =     (CategoryTheory.ConcreteCategory.hom (M.val.map (α.app (O
pposite.unop U)).op)) x
参数：φ : T ⟶ (G.sheafPushforwardContinuous RingCat J K).obj S；α : F ⟶ G；M : SheafO
fModules S；U : Cᵒᵖ；x : ↑(((SheafOfModules.pushforward φ).obj M).val.obj U)；Categ
oryTheory.ConcreteCategory.hom (((SheafOfModules.pushforwardNatTrans φ α).app M)
.val.app U)；CategoryTheory.ConcreteCategory.hom (M.val.map (α.app (Opposite.unop
 U)).op)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma pushforwardNatTrans_app_val_app (α : F ⟶ G) (M U x) :
    ((pushforwardNatTrans φ α).app M).val.app U x = M.val.map (α.app U.unop).op x := rfl

@[simp]
/-
**SheafOfModules.pushforwardNatTrans_id** 是 Mathlib 中的一个引理，位于命名空间 `SheafOfModule
s`。
形式化陈述：pushforwardNatTrans_id : pushforwardNatTrans φ (𝟙 G) = (pushforwardCongr (
by cat_disch)).hom
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `SheafOfModules.hom_ext`：hom_ext {X Y : SheafOfModules.{v} R} {f g : X ⟶ 
Y} (h : f.val = g.val) : f = g
· 使用引理 `PresheafOfModules.hom_ext`：hom_ext {f g : M₁ ⟶ M₂} (h : forall (X : Cᵒᵖ)
, f.app X = g.app X) : f = g
· 使用引理 `ModuleCat.hom_ext`：hom_ext {M N : ModuleCat.{v} R} {f g : M ⟶ N} (hf : f
.hom = g.hom) : f = g
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `PresheafOfModules.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Categor
y.{v₁, u₁} C] {R : CategoryTheory.Functor Cᵒᵖ RingCat}   (self : PresheafOfModul
es R) (X : Cᵒᵖ…
· 使用定理 `ModuleCat.restrictScalarsId'_inv_app`：∀ {R : Type u₁} [inst : Ring R] (f
 : R →+* R) (hf : f = RingHom.id R) (X : ModuleCat R),   (ModuleCat.restrictScal
arsId' f hf).inv.app X = (…
-/
lemma pushforwardNatTrans_id :
    pushforwardNatTrans φ (𝟙 G) = (pushforwardCongr (by cat_disch)).hom := by cat_disch

@[simp]
/-
**SheafOfModules.pushforwardNatTrans_comp** 是 Mathlib 中的一个引理，位于命名空间 `SheafOfModu
les`。
形式化陈述：pushforwardNatTrans_comp (α : F ⟶ G) (β : G ⟶ H) (φ : T ⟶ (H.sheafPushforw
ardContinuous RingCat.{u} J K).obj S) : pushforwardNatTrans φ (α ≫ β) = pushforw
ardNatTrans φ β ≫ pushforwardNatTrans _ α ≫ (pushforwardCongr (by cat_disch)).ho
m
参数：α : F ⟶ G；β : G ⟶ H；φ : T ⟶ (H.sheafPushforwardContinuous RingCat.{u} J K).ob
j S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `SheafOfModules.hom_ext`：hom_ext {X Y : SheafOfModules.{v} R} {f g : X ⟶ 
Y} (h : f.val = g.val) : f = g
· 使用引理 `PresheafOfModules.hom_ext`：hom_ext {f g : M₁ ⟶ M₂} (h : forall (X : Cᵒᵖ)
, f.app X = g.app X) : f = g
· 使用引理 `ModuleCat.hom_ext`：hom_ext {M N : ModuleCat.{v} R} {f g : M ⟶ N} (hf : f
.hom = g.hom) : f = g
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `PresheafOfModules.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.Categ
ory.{v₁, u₁} C] {R : CategoryTheory.Functor Cᵒᵖ RingCat}   (self : PresheafOfMod
ules R) {X Y Z :…
· 使用定理 `ModuleCat.restrictScalarsComp'_inv_app`：∀ {R₁ : Type u₁} {R₂ : Type u₂} 
{R₃ : Type u₃} [inst : Ring R₁] [inst_1 : Ring R₂] [inst_2 : Ring R₃] (f : R₁ →+
* R₂)   (g : R₂ →+* R₃) (gf …
· 使用引理 `PresheafOfModules.comp_app`：comp_app {M₁ M₂ M₃ : PresheafOfModules R} (f
 : M₁ ⟶ M₂) (g : M₂ ⟶ M₃) (X : Cᵒᵖ) : (f ≫ g).app X = f.app X ≫ g.app X
-/
lemma pushforwardNatTrans_comp (α : F ⟶ G) (β : G ⟶ H)
    (φ : T ⟶ (H.sheafPushforwardContinuous RingCat.{u} J K).obj S) :
    pushforwardNatTrans φ (α ≫ β) = pushforwardNatTrans φ β ≫ pushforwardNatTrans _ α ≫
      (pushforwardCongr (by cat_disch)).hom := by cat_disch

@[simp]
/-
**SheafOfModules.pushforwardNatTrans_app_val_app_apply** 是 Mathlib 中的一个引理，位于命名空间
 `SheafOfModules`。
形式化陈述：pushforwardNatTrans_app_val_app_apply (α : F ⟶ G) (X U x) : ((pushforwardN
atTrans φ α).app X).val.app U x = X.val.map (α.app U.unop).op x
参数：α : F ⟶ G；X U x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma pushforwardNatTrans_app_val_app_apply (α : F ⟶ G) (X U x) :
    ((pushforwardNatTrans φ α).app X).val.app U x = X.val.map (α.app U.unop).op x := rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A natural isomorphism gives a natural isomorphism between the pushforward functors. -/
@[simps]
/-
**SheafOfModules.pushforwardNatIso** 是 Mathlib 中的一个定义，位于命名空间 `SheafOfModules`。
形式化陈述：pushforwardNatIso (α : F ≅ G) : pushforward.{v} φ ≅ pushforward.{v} (φ ≫ (
Functor.sheafPushforwardContinuousNatTrans α.hom _ _ _).app S) where hom
参数：α : F ≅ G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A natural isomorphism gives a natural isomorphism between the pushforward functo
rs.
-/
noncomputable def pushforwardNatIso (α : F ≅ G) :
    pushforward.{v} φ ≅
      pushforward.{v} (φ ≫ (Functor.sheafPushforwardContinuousNatTrans α.hom _ _ _).app S) where
  hom := pushforwardNatTrans _ α.hom
  inv := pushforwardNatTrans _ α.inv ≫
    (pushforwardCongr (by ext : 3; simp [← Functor.map_comp, ← op_comp])).hom
  hom_inv_id := by
    ext X U x
    suffices X.val.presheaf.map (α.hom.app U.unop).op ≫
      X.val.presheaf.map (α.inv.app U.unop).op = 𝟙 _ from congr($this x)
    simp only [← Functor.map_comp, ← op_comp,
      Iso.inv_hom_id_app, op_id, CategoryTheory.Functor.map_id]
  inv_hom_id := by
    ext X U x
    suffices X.val.presheaf.map (α.inv.app U.unop).op ≫
      X.val.presheaf.map (α.hom.app U.unop).op = 𝟙 _ from congr($this x)
    simp only [← Functor.map_comp, ← op_comp,
      Iso.hom_inv_id_app, op_id, CategoryTheory.Functor.map_id]

/-- More flexible variant of `SheafOfModules.pushforwardNatIso`. -/
@[simps!]
noncomputable
/-
**SheafOfModules.pushforwardCongr** 是 Mathlib 中的一个定义，位于命名空间 `SheafOfModules`。
形式化陈述：pushforwardCongr {φ ψ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K)
.obj R} (e : φ = ψ) : pushforward.{v} φ ≅ pushforward.{v} ψ
参数：F.sheafPushforwardContinuous RingCat.{u} J K；e : φ = ψ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def pushforwardCongr₂ {ψ : T ⟶ (F.sheafPushforwardContinuous RingCat J K).obj S} (e : F ≅ G)
    (he : φ ≫ (Functor.sheafPushforwardContinuousNatTrans e.hom _ _ _).app S = ψ) :
    pushforward.{v} φ ≅ pushforward.{v} ψ :=
  pushforwardNatIso _ e ≪≫ pushforwardCongr he

end NatTrans

section Adjunction

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D} {G : D ⥤ C}
  {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
  [Functor.IsContinuous F J K]
  [Functor.IsContinuous G K J]
  (adj : F ⊣ G)
  (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)
  (ψ : R ⟶ (G.sheafPushforwardContinuous RingCat.{u} K J).obj S)
  (H₁ : Functor.whiskerRight (NatTrans.op adj.counit) R.obj = ψ.hom ≫ G.op.whiskerLeft φ.hom)
  (H₂ : φ.hom ≫ F.op.whiskerLeft ψ.hom ≫
    Functor.whiskerRight (NatTrans.op adj.unit) S.obj = 𝟙 S.obj)

set_option backward.isDefEq.respectTransparency false in
/-- If `F ⊣ G`, then the pushforwards along `F` and `G` are also adjoint. -/
noncomputable
/-
**SheafOfModules.pushforwardPushforwardAdj** 是 Mathlib 中的一个定义，位于命名空间 `SheafOfMod
ules`。
形式化陈述：pushforwardPushforwardAdj : pushforward.{v} φ ⊣ pushforward.{v} ψ where un
it
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.isContinuous_comp`：isContinuous_comp (F₁ : C ⥤ D)
 (F₂ : D ⥤ E) (J : GrothendieckTopology C) (K : GrothendieckTopology D) (L : Gro
thendieckTopology E) [Functor.…
-/
def pushforwardPushforwardAdj : pushforward.{v} φ ⊣ pushforward.{v} ψ where
  unit :=
    letI := CategoryTheory.Functor.isContinuous_comp G F K J K
    (pushforwardId _).inv ≫ pushforwardNatTrans (𝟙 _) adj.counit ≫
      (pushforwardCongr (by ext1; simpa)).hom ≫ (pushforwardComp _ _).inv
  counit :=
    letI := CategoryTheory.Functor.isContinuous_comp F G J K J
    (pushforwardComp _ _).hom ≫ pushforwardNatTrans _ adj.unit ≫
      (pushforwardCongr (by ext1; simpa)).hom ≫ (pushforwardId _).hom
  left_triangle_components X := by
    ext U x
    change (X.val.presheaf.map (adj.counit.app (F.obj U.unop)).op ≫
      X.val.presheaf.map (F.map (adj.unit.app U.unop)).op) _ = _
    dsimp only [id_obj]
    rw [← Functor.map_comp, ← op_comp, adj.left_triangle_components]
    simp
  right_triangle_components X := by
    ext U x
    change (X.val.presheaf.map (G.map (adj.counit.app U.unop)).op ≫
      X.val.presheaf.map (adj.unit.app (G.obj U.unop)).op) _ = _
    rw [← Functor.map_comp, ← op_comp, adj.right_triangle_components]
    simp

-- Not a simp because the type of the LHS is dsimp-able
/-
**SheafOfModules.pushforwardPushforwardAdj_unit_app_val_app** 是 Mathlib 中的一个引理，位
于命名空间 `SheafOfModules`。
形式化陈述：pushforwardPushforwardAdj_unit_app_val_app (M U x) : ((pushforwardPushforw
ardAdj adj φ ψ H₁ H₂).unit.app M).val.app U x = M.val.map (adj.counit.app U.unop
).op x
参数：M U x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma pushforwardPushforwardAdj_unit_app_val_app (M U x) :
    ((pushforwardPushforwardAdj adj φ ψ H₁ H₂).unit.app M).val.app U x =
      M.val.map (adj.counit.app U.unop).op x := rfl

-- Not a simp because the type of the LHS is dsimp-able
/-
**SheafOfModules.pushforwardPushforwardAdj_counit_app_val_app** 是 Mathlib 中的一个引理
，位于命名空间 `SheafOfModules`。
形式化陈述：pushforwardPushforwardAdj_counit_app_val_app (M U x) : ((pushforwardPushfo
rwardAdj adj φ ψ H₁ H₂).counit.app M).val.app U x = M.val.map (adj.unit.app U.un
op).op x
参数：M U x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma pushforwardPushforwardAdj_counit_app_val_app (M U x) :
    ((pushforwardPushforwardAdj adj φ ψ H₁ H₂).counit.app M).val.app U x =
      M.val.map (adj.unit.app U.unop).op x := rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**SheafOfModules.isLeftAdjoint_pushforward_of_isIso** 是 Mathlib 中的一个实例，位于命名空间 `S
heafOfModules`。
形式化陈述：isLeftAdjoint_pushforward_of_isIso [F.IsCocontinuous J K] [IsIso φ] [F.IsL
eftAdjoint] : (pushforward.{u} φ).IsLeftAdjoint
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instIsContinuousRightAdjointOfIsCocontinuous`：∀ {C : Type
 u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {D : Type u_2}   [inst_1 : C
ategoryTheory.Category.{v_2, u_2} D] (J : Categor…
· 使用引理 `CategoryTheory.Adjunction.isLeftAdjoint`：isLeftAdjoint (adj : F ⊣ G) : F
.IsLeftAdjoint
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ObjectProperty.instIsIsoHomFullSubcategory`：∀ {C : Type u
} [inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.ObjectProperty C
} {X Y : P.FullSubcategory}   (f : X ⟶ Y) [Cate…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.map_inv`：map_inv (F : C ⥤ D) {X Y : C} (f : X ⟶ Y
) [IsIso f] : F.map (inv f) = inv (F.map f)
· 使用引理 `CategoryTheory.ObjectProperty.hom_inv`：hom_inv {X Y : P.FullSubcategory}
 (f : X ⟶ Y) [IsIso f] : (inv f).hom = inv f.hom
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Adjunction.sheafPushforwardContinuous_unit_app_hom_app`：∀
 {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1
 : CategoryTheory.Category.{v₂, u₂} D]   {E : Type u₃} [ins…
· 使用定理 `CategoryTheory.NatIso.isIso_app_of_isIso`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.NatIso.isIso_inv_app`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.IsIso.inv_hom_id`：inv_hom_id (f : X ⟶ Y) [I : IsIso f] : 
inv f ≫ f = 𝟙 Y
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `CategoryTheory.IsIso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y) [I : CategoryTheory.IsIso f] {Z : 
C}   (h : Y ⟶ Z), CategoryT…
· 使用定理 `CategoryTheory.Adjunction.left_triangle_components`：∀ {C : Type u₁} [ins
t : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.C
ategory.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.IsIso.hom_inv_id`：hom_inv_id (f : X ⟶ Y) [I : IsIso f] : 
f ≫ inv f = 𝟙 X
-/
instance isLeftAdjoint_pushforward_of_isIso [F.IsCocontinuous J K] [IsIso φ] [F.IsLeftAdjoint] :
    (pushforward.{u} φ).IsLeftAdjoint := by
  let adj := Adjunction.ofIsLeftAdjoint F
  let shAdj := adj.sheafPushforwardContinuous (E := RingCat.{u}) J K
  let ψ : R ⟶ (F.rightAdjoint.sheafPushforwardContinuous RingCat.{u} K J).obj S :=
    shAdj.unit.app R ≫ (F.rightAdjoint.sheafPushforwardContinuous _ _ _).map (inv φ)
  refine (SheafOfModules.pushforwardPushforwardAdj adj φ ψ ?_ ?_).isLeftAdjoint
  · ext U : 2
    simp [ψ, shAdj]
  · ext U : 2
    have := (inv φ).hom.naturality
    dsimp at this
    simp only [ObjectProperty.hom_inv, NatIso.isIso_inv_app, sheafPushforwardContinuous_obj_obj_obj,
      IsIso.eq_inv_comp] at this
    simp [ψ, shAdj, ← this, ← Functor.map_comp_assoc, ← op_comp]

noncomputable section

open CategoryTheory Limits

variable {C : Type u'} [Category.{v'} C] [HasBinaryProducts C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}

set_option backward.defeqAttrib.useBackward true in
/-- The canonical morphism from `R` to the pushforward of its restriction to `Over x`. -/
/-
**SheafOfModules.pushforwardOver** 是 Mathlib 中的一个定义，位于命名空间 `SheafOfModules`。
形式化陈述：pushforwardOver (x : C) : R ⟶ ((Over.star x).sheafPushforwardContinuous Ri
ngCat J (J.over x)).obj (R.over x)
参数：x : C。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.instIsContinuousOverStarOver`：∀ {C :
 Type u'} [inst : CategoryTheory.Category.{v_1, u'} C] [inst_1 : CategoryTheory.
Limits.HasBinaryProducts C]   {J : CategoryTheory.Grot…

--- 原说明 ---
The canonical morphism from `R` to the pushforward of its restriction to `Over x
`.
-/
def pushforwardOver (x : C) :
    R ⟶ ((Over.star x).sheafPushforwardContinuous RingCat J (J.over x)).obj (R.over x) :=
  ⟨{app U := R.obj.map Limits.prod.snd.op
    naturality U V f := by simp [← Functor.map_comp, ← op_comp]; rfl }⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The adjunction between restriction to `Over x` and pushforward along `Over.star x`. -/
/-
**SheafOfModules.overPushforwardOverAdj** 是 Mathlib 中的一个定义，位于命名空间 `SheafOfModule
s`。
形式化陈述：overPushforwardOverAdj (x : C) : pushforward.{w} (𝟙 (R.over x)) ⊣ pushforw
ard.{w} (pushforwardOver x)
参数：x : C。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.instIsContinuousOverForgetOver`：∀ {C
 : Type u} [inst : CategoryTheory.Category.{v, u} C] (J : CategoryTheory.Grothen
dieckTopology C) (X : C),   (CategoryTheory.Over.forget …
· 使用定理 `CategoryTheory.GrothendieckTopology.instIsContinuousOverStarOver`：∀ {C :
 Type u'} [inst : CategoryTheory.Category.{v_1, u'} C] [inst_1 : CategoryTheory.
Limits.HasBinaryProducts C]   {J : CategoryTheory.Grot…

--- 原说明 ---
The adjunction between restriction to `Over x` and pushforward along `Over.star 
x`.
-/
def overPushforwardOverAdj (x : C) :
    pushforward.{w} (𝟙 (R.over x)) ⊣ pushforward.{w} (pushforwardOver x) := by
  refine pushforwardPushforwardAdj (Over.forgetAdjStar x) (𝟙 (R.over x)) _ ?_ ?_
  · ext y : 2
    simp [pushforwardOver]
  · ext y : 2
    simp [pushforwardOver, ← Functor.map_comp, ← op_comp]
/-
**SheafOfModules.** 是 Mathlib 中的一个实例，位于命名空间 `SheafOfModules`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (x : C) : IsLeftAdjoint (pushforward.{w} (𝟙 (R.over x))) where
  exists_rightAdjoint := ⟨_, Nonempty.intro (overPushforwardOverAdj x)⟩

variable (R) in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The adjunction between pushforward along `Over.map` and pushforward along `Over.pullback`. -/
/-
**SheafOfModules.overMapPushforwardAdj** 是 Mathlib 中的一个定义，位于命名空间 `SheafOfModules
`。
形式化陈述：overMapPushforwardAdj [HasPullbacks C] {X Y : C} (f : X ⟶ Y) : overMap R f
 ⊣ overPullback R f
参数：f : X ⟶ Y。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.instIsContinuousOverMapOver`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] (J : CategoryTheory.Grothendie
ckTopology C) {X Y : C}   (f : X ⟶ Y), (CategoryTheor…
· 使用定理 `CategoryTheory.GrothendieckTopology.instIsContinuousOverPullbackOver`：∀ 
{C : Type u} [inst : CategoryTheory.Category.{v, u} C] (J : CategoryTheory.Groth
endieckTopology C)   [inst_1 : CategoryTheory.Limits.HasPu…

--- 原说明 ---
The adjunction between pushforward along `Over.map` and pushforward along `Over.
pullback`.
-/
def overMapPushforwardAdj [HasPullbacks C] {X Y : C} (f : X ⟶ Y) :
    overMap R f ⊣ overPullback R f := by
  refine pushforwardPushforwardAdj (Over.mapPullbackAdj f) _ _ ?_ ?_
  · ext
    simp [Sheaf.pushforwardOverMapIso]
  · ext
    simp [← Functor.map_comp, ← op_comp, Sheaf.pushforwardOverMapIso]
/-
**SheafOfModules.** 是 Mathlib 中的一个实例，位于命名空间 `SheafOfModules`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasPullbacks C] {X Y : C} (f : X ⟶ Y) : (overMap R f).IsLeftAdjoint :=
  (overMapPushforwardAdj R f).isLeftAdjoint

end

end Adjunction

section Equivalence

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} (eqv : C ≌ D)
  {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
  [Functor.IsContinuous eqv.functor J K]
  [Functor.IsContinuous eqv.inverse K J]
  (φ : S ⟶ (eqv.functor.sheafPushforwardContinuous RingCat.{u} J K).obj R)
  (ψ : R ⟶ (eqv.inverse.sheafPushforwardContinuous RingCat.{u} K J).obj S)
  (H₁ : Functor.whiskerRight (NatTrans.op eqv.counit) R.obj =
    ψ.hom ≫ eqv.inverse.op.whiskerLeft φ.hom)
  (H₂ : φ.hom ≫ eqv.functor.op.whiskerLeft ψ.hom ≫
    Functor.whiskerRight (NatTrans.op eqv.unit) S.obj = 𝟙 S.obj)

/-- If `e : C ≌ D`, then the pushforwards along `e.functor` and `e.inverse` forms an equivalence. -/
noncomputable
/-
**SheafOfModules.pushforwardPushforwardEquivalence** 是 Mathlib 中的一个定义，位于命名空间 `Sh
eafOfModules`。
形式化陈述：pushforwardPushforwardEquivalence : SheafOfModules R ≌ SheafOfModules S wh
ere functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def pushforwardPushforwardEquivalence : SheafOfModules R ≌ SheafOfModules S where
  functor := pushforward.{v} φ
  inverse := pushforward.{v} ψ
  unitIso :=
    letI := CategoryTheory.Functor.isContinuous_comp eqv.inverse eqv.functor K J K
    (pushforwardId _).symm ≪≫ pushforwardNatIso _ eqv.counitIso ≪≫
      pushforwardCongr (by ext1; simpa) ≪≫ (pushforwardComp _ _).symm
  counitIso :=
    letI := CategoryTheory.Functor.isContinuous_comp eqv.functor eqv.inverse J K J
    pushforwardComp _ _ ≪≫ pushforwardNatIso _ eqv.unitIso ≪≫
      pushforwardCongr (by ext1; simpa) ≪≫ pushforwardId _
  functor_unitIso_comp :=
    (pushforwardPushforwardAdj eqv.toAdjunction φ ψ H₁ H₂).left_triangle_components

-- Not a simp because the type of the LHS is dsimp-able
/-
**SheafOfModules.pushforwardPushforwardEquivalence_unit_app_val_app** 是 Mathlib 
中的一个引理，位于命名空间 `SheafOfModules`。
形式化陈述：pushforwardPushforwardEquivalence_unit_app_val_app (M U x) : ((pushforward
PushforwardEquivalence eqv φ ψ H₁ H₂).unit.app M).val.app U x = M.val.map (eqv.c
ounit.app U.unop).op x
参数：M U x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma pushforwardPushforwardEquivalence_unit_app_val_app (M U x) :
    ((pushforwardPushforwardEquivalence eqv φ ψ H₁ H₂).unit.app M).val.app U x =
      M.val.map (eqv.counit.app U.unop).op x := rfl

-- Not a simp because the type of the LHS is dsimp-able
/-
**SheafOfModules.pushforwardPushforwardEquivalence_counit_app_val_app** 是 Mathli
b 中的一个引理，位于命名空间 `SheafOfModules`。
形式化陈述：pushforwardPushforwardEquivalence_counit_app_val_app (M U x) : ((pushforwa
rdPushforwardEquivalence eqv φ ψ H₁ H₂).counit.app M).val.app U x = M.val.map (e
qv.unit.app U.unop).op x
参数：M U x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma pushforwardPushforwardEquivalence_counit_app_val_app (M U x) :
    ((pushforwardPushforwardEquivalence eqv φ ψ H₁ H₂).counit.app M).val.app U x =
      M.val.map (eqv.unit.app U.unop).op x := rfl

end Equivalence

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Pushforward commutes with `SheafOfModules.forgetToSheafModuleCat` -/
/-
**SheafOfModules.pushforwardCompForgetToSheafModuleCat** 是 Mathlib 中的一个定义，位于命名空间
 `SheafOfModules`。
形式化陈述：pushforwardCompForgetToSheafModuleCat (X : Cᵒᵖ) (hX : Limits.IsInitial X) 
(hX' : Limits.IsInitial (F.op.obj X)) : SheafOfModules.pushforward φ ⋙ SheafOfMo
dules.forgetToSheafModuleCat _ X hX ≅ SheafOfModules.forgetToSheafModuleCat _ _ 
hX' ⋙ sheafCompose K (ModuleCat.restrictScalars <| (φ.hom.app _).hom) ⋙ F.sheafP
ushforwardContinuous _ J K
参数：X : Cᵒᵖ；hX : Limits.IsInitial X；hX' : Limits.IsInitial (F.op.obj X)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Pushforward commutes with `SheafOfModules.forgetToSheafModuleCat`
-/
noncomputable def pushforwardCompForgetToSheafModuleCat
    (X : Cᵒᵖ) (hX : Limits.IsInitial X) (hX' : Limits.IsInitial (F.op.obj X)) :
    SheafOfModules.pushforward φ ⋙ SheafOfModules.forgetToSheafModuleCat _ X hX ≅
    SheafOfModules.forgetToSheafModuleCat _ _ hX' ⋙
      sheafCompose K (ModuleCat.restrictScalars <| (φ.hom.app _).hom) ⋙
        F.sheafPushforwardContinuous _ J K := by
  refine NatIso.ofComponents (fun M ↦ ObjectProperty.isoMk _ ?_) ?_
  · refine NatIso.ofComponents (fun U ↦ ?_) ?_
    · refine (ModuleCat.restrictScalarsComp'App _ _ _ ?_ _).symm ≪≫
        (ModuleCat.restrictScalarsComp _ _).app _
      rw [← RingCat.hom_comp, ← RingCat.hom_comp, φ.hom.naturality]
      dsimp
      rw [hX'.hom_ext (hX'.to (Opposite.op (F.obj (Opposite.unop U)))) _]
    · cat_disch
  · cat_disch

end SheafOfModules

