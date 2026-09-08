/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Final.Type

/-!
# Pullbacks of free sheaves of modules

Let `S` (resp.`R`) be a sheaf of rings on a category `C` (resp. `D`)
equipped with a Grothendieck topology `J` (resp. `K`).
Let `F : C ⥤ D` be a continuous functor.
Let `φ` be a morphism from `S` to the direct image of `R`.

We introduce `unitToPushforwardObjUnit φ` which is the morphism
in the category `SheafOfModules S` which corresponds to `φ`, and
show that the adjoint morphism
`pullbackObjUnitToUnit φ : (pullback.{u} φ).obj (unit S) ⟶ unit R`
is an isomorphism when `F` is a final functor.
More generally, the functor `pullback φ` sends the free sheaf
of modules `free I` to `free I`, see `pullbackObjFreeIso` and
`freeFunctorCompPullbackIso`.
-/

@[expose] public section

universe v v₁ v₂ u₁ u₂ u

open CategoryTheory Limits

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
  {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
  [Functor.IsContinuous F J K]
  (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)

/-- The canonical map from the (global) sections of a sheaf of modules
to the (global) sections of its pushforward. -/
@[simps]
/-
**SheafOfModules.pushforwardSections** 是 Mathlib 中的一个定义，位于命名空间 `SheafOfModules`。
形式化陈述：pushforwardSections {M : SheafOfModules.{v} R} (s : M.sections) : ((pushfo
rward φ).obj M).sections where val _
参数：s : M.sections。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical map from the (global) sections of a sheaf of modules
to the (global) sections of its pushforward.
-/
def pushforwardSections {M : SheafOfModules.{v} R} (s : M.sections) :
    ((pushforward φ).obj M).sections where
  val _ := s.val _
  property _ := s.property _

variable (M) in
/-
**SheafOfModules.bijective_pushforwardSections** 是 Mathlib 中的一个引理，位于命名空间 `SheafO
fModules`。
形式化陈述：bijective_pushforwardSections [F.Final] : Function.Bijective (pushforwardS
ections φ (M
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.bijective_sectionsPrecomp`：bijective_sectionsPrec
omp (F : C ⥤ D) (P : D ⥤ Type w) [F.Initial] : Function.Bijective (F.sectionsPre
comp (P
-/
lemma bijective_pushforwardSections [F.Final] :
    Function.Bijective (pushforwardSections φ (M := M)) :=
  Functor.bijective_sectionsPrecomp _ _

/-- The canonical morphism `unit S ⟶ (pushforward.{u} φ).obj (unit R)`
of sheaves of modules corresponding to a continuous map between ringed sites. -/
/-
**SheafOfModules.unitToPushforwardObjUnit** 是 Mathlib 中的一个定义，位于命名空间 `SheafOfModu
les`。
形式化陈述：unitToPushforwardObjUnit : unit S ⟶ (pushforward.{u} φ).obj (unit R) where
 val.app X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical morphism `unit S ⟶ (pushforward.{u} φ).obj (unit R)`
of sheaves of modules corresponding to a continuous map between ringed sites.
-/
noncomputable def unitToPushforwardObjUnit : unit S ⟶ (pushforward.{u} φ).obj (unit R) where
  val.app X := ModuleCat.homMk ((forget₂ RingCat AddCommGrpCat).map (φ.hom.app X)) (fun r ↦ by
    ext m
    exact ((φ.hom.app X).hom.map_mul _ _).symm)
  val.naturality f := by
    ext
    exact ConcreteCategory.congr_hom (φ.hom.naturality f) _
/-
**SheafOfModules.unitToPushforwardObjUnit_val_app_apply** 是 Mathlib 中的一个引理，位于命名空
间 `SheafOfModules`。
形式化陈述：unitToPushforwardObjUnit_val_app_apply {X : Cᵒᵖ} (a : S.obj.obj X) : (unit
ToPushforwardObjUnit φ).val.app X a = φ.hom.app X a
参数：a : S.obj.obj X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma unitToPushforwardObjUnit_val_app_apply {X : Cᵒᵖ} (a : S.obj.obj X) :
    (unitToPushforwardObjUnit φ).val.app X a = φ.hom.app X a := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**SheafOfModules.pushforwardSections_unitHomEquiv** 是 Mathlib 中的一个引理，位于命名空间 `She
afOfModules`。
形式化陈述：pushforwardSections_unitHomEquiv {M : SheafOfModules.{u} R} (f : unit R ⟶ 
M) : pushforwardSections φ (M.unitHomEquiv f) = ((pushforward φ).obj M).unitHomE
quiv (unitToPushforwardObjUnit φ ≫ (pushforward φ).map f)
参数：f : unit R ⟶ M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `PresheafOfModules.sections_ext`：sections_ext {M : PresheafOfModules.{v} 
R} (s t : M.sections) (h : forall (X : Cᵒᵖ), s.val X = t.val X) : s = t
· 使用引理 `SheafOfModules.unitToPushforwardObjUnit_val_app_apply`：unitToPushforward
ObjUnit_val_app_apply {X : Cᵒᵖ} (a : S.obj.obj X) : (unitToPushforwardObjUnit φ)
.val.app X a = φ.hom.app X a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SheafOfModules.pushforwardSections_coe`：∀ {C : Type u₁} [inst : Category
Theory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂,
 u₂} D]   {J : CategoryTheor…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `SheafOfModules.pushforward_map_val`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {J : CategoryTheor…
· 使用引理 `PresheafOfModules.comp_app`：comp_app {M₁ M₂ M₃ : PresheafOfModules R} (f
 : M₁ ⟶ M₂) (g : M₂ ⟶ M₃) (X : Cᵒᵖ) : (f ≫ g).app X = f.app X ≫ g.app X
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
lemma pushforwardSections_unitHomEquiv
    {M : SheafOfModules.{u} R} (f : unit R ⟶ M) :
    pushforwardSections φ (M.unitHomEquiv f) =
      ((pushforward φ).obj M).unitHomEquiv
        (unitToPushforwardObjUnit φ ≫ (pushforward φ).map f) := by
  ext X
  have := unitToPushforwardObjUnit_val_app_apply φ (X := X) 1
  simp [this, map_one]
  rfl

variable [(pushforward.{u} φ).IsRightAdjoint]

/-- The canonical morphism `(pullback.{u} φ).obj (unit S) ⟶ unit R`
of sheaves of modules corresponding to a continuous map between ringed sites. -/
/-
**SheafOfModules.pullbackObjUnitToUnit** 是 Mathlib 中的一个定义，位于命名空间 `SheafOfModules
`。
形式化陈述：pullbackObjUnitToUnit : (pullback.{u} φ).obj (unit S) ⟶ unit R
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The canonical morphism `(pullback.{u} φ).obj (unit S) ⟶ unit R`
of sheaves of modules corresponding to a continuous map between ringed sites.
-/
noncomputable def pullbackObjUnitToUnit :
    (pullback.{u} φ).obj (unit S) ⟶ unit R :=
  ((pullbackPushforwardAdjunction.{u} φ).homEquiv _ _).symm (unitToPushforwardObjUnit φ)

@[simp]
/-
**SheafOfModules.pullbackPushforwardAdjunction_homEquiv_symm_unitToPushforwardOb
jUnit** 是 Mathlib 中的一个引理，位于命名空间 `SheafOfModules`。
形式化陈述：pullbackPushforwardAdjunction_homEquiv_symm_unitToPushforwardObjUnit : ((p
ullbackPushforwardAdjunction.{u} φ).homEquiv _ _).symm (unitToPushforwardObjUnit
 φ) = pullbackObjUnitToUnit φ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma pullbackPushforwardAdjunction_homEquiv_symm_unitToPushforwardObjUnit :
    ((pullbackPushforwardAdjunction.{u} φ).homEquiv _ _).symm (unitToPushforwardObjUnit φ) =
      pullbackObjUnitToUnit φ := rfl

@[simp]
/-
**SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit** 
是 Mathlib 中的一个引理，位于命名空间 `SheafOfModules`。
形式化陈述：pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit : (pullbackPu
shforwardAdjunction.{u} φ).homEquiv _ _ (pullbackObjUnitToUnit φ) = unitToPushfo
rwardObjUnit φ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
-/
lemma pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit :
    (pullbackPushforwardAdjunction.{u} φ).homEquiv _ _ (pullbackObjUnitToUnit φ) =
      unitToPushforwardObjUnit φ :=
  Equiv.apply_symm_apply _ _
/-
**SheafOfModules.** 是 Mathlib 中的一个实例，位于命名空间 `SheafOfModules`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [F.Final] : IsIso (pullbackObjUnitToUnit φ) := by
  rw [isIso_iff_coyoneda_map_bijective]
  intro M
  rw [← ((pullbackPushforwardAdjunction.{u} φ).homEquiv _ _).bijective.of_comp_iff',
    ← (unitHomEquiv _).bijective.of_comp_iff']
  convert! (bijective_pushforwardSections φ M).comp (unitHomEquiv _).bijective
  ext f : 1
  dsimp
  rw [pushforwardSections_unitHomEquiv, EmbeddingLike.apply_eq_iff_eq,
    Adjunction.homEquiv_naturality_right,
    pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit]

variable [HasWeakSheafify J AddCommGrpCat.{u}] [HasWeakSheafify K AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{u}] [F.Final]

/-- The pullback of a free sheaf of modules is a free sheaf of modules. -/
/-
**SheafOfModules.pullbackObjFreeIso** 是 Mathlib 中的一个定义，位于命名空间 `SheafOfModules`。
形式化陈述：pullbackObjFreeIso (I : Type u) : (pullback φ).obj (free I) ≅ free I
参数：I : Type u。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal`：∀ {C : Type u₁} [i
nst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory
.Category.{v₂, u₂} D]   {J : CategoryTheor…

--- 原说明 ---
The pullback of a free sheaf of modules is a free sheaf of modules.
-/
noncomputable def pullbackObjFreeIso (I : Type u) :
    (pullback φ).obj (free I) ≅ free I :=
  (asIso (sigmaComparison _ _)).symm ≪≫
    Sigma.mapIso (fun _ ↦ asIso (pullbackObjUnitToUnit φ))

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**SheafOfModules.pullback_map_** 是 Mathlib 中的一个引理，位于命名空间 `SheafOfModules`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma pullback_map_ιFree_comp_pullbackObjFreeIso_hom {I : Type u} (i : I) :
    (pullback φ).map (ιFree i) ≫ (pullbackObjFreeIso φ I).hom =
      pullbackObjUnitToUnit φ ≫ ιFree i := by
  simp [pullbackObjFreeIso, ιFree]

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/-
**SheafOfModules.pullbackObjFreeIso_hom_naturality** 是 Mathlib 中的一个引理，位于命名空间 `Sh
eafOfModules`。
形式化陈述：pullbackObjFreeIso_hom_naturality {I J : Type u} (f : I -> J) : (pullback 
φ).map (freeMap f) ≫ (pullbackObjFreeIso φ J).hom = (pullbackObjFreeIso φ I).hom
 ≫ freeMap f
参数：f : I -> J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Cofan.IsColimit.hom_ext`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] {I : Type u_1} {F : I → C} {c : CategoryTheory.L
imits.Cofan F}   (hc : CategoryTheo…
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Functor.instPreservesColimitsOfShapeOfIsLeftAdjoint`：∀ {J
 : Type u_1} {C : Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_1,
 u_1} J]   [inst_1 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `SheafOfModules.instIsLeftAdjointPullback`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {J : CategoryTheor…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `SheafOfModules.ιFree_freeMap`：ιFree_freeMap (i : I) : ιFree (R
· 使用引理 `SheafOfModules.pullback_map_ιFree_comp_pullbackObjFreeIso_hom`：pullback_
map_ιFree_comp_pullbackObjFreeIso_hom {I : Type u} (i : I) : (pullback φ).map (ι
Free i) ≫ (pullbackObjFreeIso φ I).hom = pullbackOb…
· 使用定理 `SheafOfModules.pullback_map_ιFree_comp_pullbackObjFreeIso_hom_assoc`：∀ {
C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 :
 CategoryTheory.Category.{v₂, u₂} D]   {J : CategoryTheor…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma pullbackObjFreeIso_hom_naturality {I J : Type u} (f : I → J) :
    (pullback φ).map (freeMap f) ≫ (pullbackObjFreeIso φ J).hom =
      (pullbackObjFreeIso φ I).hom ≫ freeMap f :=
  Cofan.IsColimit.hom_ext (isColimitCofanMkObjOfIsColimit (pullback φ) _ _
    (isColimitFreeCofan (R := S) I)) _ _ (fun i ↦ by simp [← Functor.map_comp_assoc])

set_option backward.defeqAttrib.useBackward true in
/-- The canonical isomorphism `freeFunctor ⋙ pullback φ ≅ freeFunctor` for a
continuous map between ringed sites, when the underlying functor between the sites
is final. -/
/-
**SheafOfModules.freeFunctorCompPullbackIso** 是 Mathlib 中的一个定义，位于命名空间 `SheafOfMo
dules`。
形式化陈述：freeFunctorCompPullbackIso : freeFunctor ⋙ pullback φ ≅ freeFunctor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical isomorphism `freeFunctor ⋙ pullback φ ≅ freeFunctor` for a
continuous map between ringed sites, when the underlying functor between the sit
es
is final.
-/
noncomputable def freeFunctorCompPullbackIso : freeFunctor ⋙ pullback φ ≅ freeFunctor :=
  NatIso.ofComponents (fun X ↦ pullbackObjFreeIso φ X)

end SheafOfModules

