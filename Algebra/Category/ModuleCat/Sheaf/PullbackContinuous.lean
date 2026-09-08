/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pullback
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous

/-!
# Pullback of sheaves of modules

Let `S` and `R` be sheaves of rings over sites `(C, J)` and `(D, K)` respectively.
Let `F : C ⥤ D` be a continuous functor between these sites, and
let `φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R` be a morphism
of sheaves of rings.

In this file, we define the pullback functor for sheaves of modules
`pullback.{v} φ : SheafOfModules.{v} S ⥤ SheafOfModules.{v} R`
that is left adjoint to `pushforward.{v} φ`. We show that it exists
under suitable assumptions, and prove that the pullback of (pre)sheaves of
modules commutes with the sheafification.

From the compatibility of `pushforward` with respect to composition, we deduce
similar pseudofunctor-like properties of the `pullback` functors.

-/

@[expose] public section

universe v v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄ u

open CategoryTheory Functor

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {D' : Type u₃} [Category.{v₃} D'] {D'' : Type u₄} [Category.{v₄} D'']
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
  {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
  [Functor.IsContinuous F J K]
  (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)

section

variable [(pushforward.{v} φ).IsRightAdjoint]

/-- The pullback functor `SheafOfModules S ⥤ SheafOfModules R` induced by
a morphism of sheaves of rings `S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R`,
defined as the left adjoint functor to the pushforward, when it exists. -/
/-
**SheafOfModules.pullback** 是 Mathlib 中的一个定义，位于命名空间 `SheafOfModules`。
形式化陈述：pullback : SheafOfModules.{v} S ⥤ SheafOfModules.{v} R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pullback functor `SheafOfModules S ⥤ SheafOfModules R` induced by
a morphism of sheaves of rings `S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J 
K).obj R`,
defined as the left adjoint functor to the pushforward, when it exists.
-/
noncomputable def pullback : SheafOfModules.{v} S ⥤ SheafOfModules.{v} R :=
  (pushforward.{v} φ).leftAdjoint

/-- Given a continuous functor between sites `F`, and a morphism of sheaves of rings
`S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R`, this is the adjunction
between the corresponding pullback and pushforward functors on the categories
of sheaves of modules. -/
/-
**SheafOfModules.pullbackPushforwardAdjunction** 是 Mathlib 中的一个定义，位于命名空间 `SheafO
fModules`。
形式化陈述：pullbackPushforwardAdjunction : pullback.{v} φ ⊣ pushforward.{v} φ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a continuous functor between sites `F`, and a morphism of sheaves of rings
`S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R`, this is the adjuncti
on
between the corresponding pullback and pushforward functors on the categories
of sheaves of modules.
-/
noncomputable def pullbackPushforwardAdjunction : pullback.{v} φ ⊣ pushforward.{v} φ :=
  Adjunction.ofIsRightAdjoint (pushforward φ)
/-
**SheafOfModules.** 是 Mathlib 中的一个实例，位于命名空间 `SheafOfModules`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (pullback.{v} φ).IsLeftAdjoint :=
  (pullbackPushforwardAdjunction φ).isLeftAdjoint

end

section

variable [(PresheafOfModules.pushforward.{v} φ.hom).IsRightAdjoint]
  [HasWeakSheafify K AddCommGrpCat.{v}] [K.WEqualsLocallyBijective AddCommGrpCat.{v}]

namespace PullbackConstruction

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Construction of a left adjoint to the functor `pushforward.{v} φ` by using the
pullback of presheaves of modules and the sheafification. -/
/-
**SheafOfModules.PullbackConstruction.adjunction** 是 Mathlib 中的一个定义，位于命名空间 `Shea
fOfModules.PullbackConstruction`。
形式化陈述：adjunction : (forget S ⋙ PresheafOfModules.pullback.{v} φ.hom ⋙ PresheafOf
Modules.sheafification (R₀
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Construction of a left adjoint to the functor `pushforward.{v} φ` by using the
pullback of presheaves of modules and the sheafification.
-/
noncomputable def adjunction :
    (forget S ⋙ PresheafOfModules.pullback.{v} φ.hom ⋙
      PresheafOfModules.sheafification (R₀ := R.obj) (𝟙 R.obj)) ⊣ pushforward.{v} φ :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun F G ↦
        ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv _ _).trans
            (((PresheafOfModules.pullbackPushforwardAdjunction φ.hom).homEquiv F.val G.val).trans
              ((fullyFaithfulForget S).homEquiv (Y := (pushforward φ).obj G)).symm)
      homEquiv_naturality_left_symm := by
        intros
        dsimp [Functor.FullyFaithful.homEquiv]
        -- these erw seem difficult to remove
        erw [Adjunction.homEquiv_naturality_left_symm,
          Adjunction.homEquiv_naturality_left_symm]
        dsimp [pushforward_obj_val]
        simp only [Functor.map_comp, Category.assoc]
      homEquiv_naturality_right := by
        tauto }

end PullbackConstruction

/-
**SheafOfModules.** 是 Mathlib 中的一个实例，位于命名空间 `SheafOfModules`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (pushforward.{v} φ).IsRightAdjoint :=
  (PullbackConstruction.adjunction.{v} φ).isRightAdjoint

/-- The pullback functor on sheaves of modules can be described as a composition
of the forget functor to presheaves, the pullback on presheaves of modules, and
the sheafification functor. -/
/-
**SheafOfModules.pullbackIso** 是 Mathlib 中的一个定义，位于命名空间 `SheafOfModules`。
形式化陈述：pullbackIso : pullback.{v} φ ≅ forget S ⋙ PresheafOfModules.pullback.{v} φ
.hom ⋙ PresheafOfModules.sheafification (R₀
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SheafOfModules.instIsRightAdjointPushforward`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Categor
y.{v₂, u₂} D]   {J : CategoryTheor…

--- 原说明 ---
The pullback functor on sheaves of modules can be described as a composition
of the forget functor to presheaves, the pullback on presheaves of modules, and
the sheafification functor.
-/
noncomputable def pullbackIso :
    pullback.{v} φ ≅
      forget S ⋙ PresheafOfModules.pullback.{v} φ.hom ⋙
        PresheafOfModules.sheafification (R₀ := R.obj) (𝟙 R.obj) :=
  Adjunction.leftAdjointUniq (pullbackPushforwardAdjunction φ)
    (PullbackConstruction.adjunction φ)

section

variable [HasWeakSheafify J AddCommGrpCat.{v}] [J.WEqualsLocallyBijective AddCommGrpCat.{v}]

/-- The pullback of (pre)sheaves of modules commutes with the sheafification. -/
/-
**SheafOfModules.sheafificationCompPullback** 是 Mathlib 中的一个定义，位于命名空间 `SheafOfMo
dules`。
形式化陈述：sheafificationCompPullback : PresheafOfModules.sheafification (𝟙 S.obj) ⋙ 
pullback.{v} φ ≅ PresheafOfModules.pullback.{v} φ.hom ⋙ PresheafOfModules.sheafi
fication (R₀
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SheafOfModules.instIsRightAdjointPushforward`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Categor
y.{v₂, u₂} D]   {J : CategoryTheor…

--- 原说明 ---
The pullback of (pre)sheaves of modules commutes with the sheafification.
-/
noncomputable def sheafificationCompPullback :
    PresheafOfModules.sheafification (𝟙 S.obj) ⋙ pullback.{v} φ ≅
      PresheafOfModules.pullback.{v} φ.hom ⋙
        PresheafOfModules.sheafification (R₀ := R.obj) (𝟙 R.obj) :=
  Adjunction.leftAdjointUniq
    ((PresheafOfModules.sheafificationAdjunction (𝟙 S.obj)).comp
      (pullbackPushforwardAdjunction φ))
    ((PresheafOfModules.pullbackPushforwardAdjunction φ.hom).comp
      (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)))

end

end


/-
**SheafOfModules.** 是 Mathlib 中的一个实例，位于命名空间 `SheafOfModules`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (pushforward.{v} (F := 𝟭 C) (𝟙 S)).IsRightAdjoint :=
  Functor.isRightAdjoint_of_iso (pushforwardId S).symm

variable (S) in
/-- The pullback by the identity morphism identifies to the identity functor of the
category of sheaves of modules. -/
/-
**SheafOfModules.pullbackId** 是 Mathlib 中的一个定义，位于命名空间 `SheafOfModules`。
形式化陈述：pullbackId : pullback.{v} (F
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SheafOfModules.instIsRightAdjointPushforwardIdSheafRingCat`：∀ {C : Type 
u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {J : CategoryTheory.Grothendieck
Topology C}   {S : CategoryTheory.Sheaf J RingCa…

--- 原说明 ---
The pullback by the identity morphism identifies to the identity functor of the
category of sheaves of modules.
-/
noncomputable def pullbackId : pullback.{v} (F := 𝟭 C) (𝟙 S) ≅ 𝟭 _ :=
  ((pullbackPushforwardAdjunction.{v} (F := 𝟭 C) (𝟙 S))).leftAdjointIdIso (pushforwardId S)

variable (S) in
@[simp]
/-
**SheafOfModules.conjugateEquiv_pullbackId_hom** 是 Mathlib 中的一个引理，位于命名空间 `SheafO
fModules`。
形式化陈述：conjugateEquiv_pullbackId_hom : conjugateEquiv .id (pullbackPushforwardAdj
unction.{v} _) (pullbackId S).hom = (pushforwardId S).inv
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Adjunction.conjugateEquiv_leftAdjointIdIso_hom`：conjugate
Equiv_leftAdjointIdIso_hom : conjugateEquiv .id adj (leftAdjointIdIso adj e).hom
 = e.inv
· 使用定理 `SheafOfModules.instIsRightAdjointPushforwardIdSheafRingCat`：∀ {C : Type 
u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {J : CategoryTheory.Grothendieck
Topology C}   {S : CategoryTheory.Sheaf J RingCa…
-/
lemma conjugateEquiv_pullbackId_hom :
    conjugateEquiv .id (pullbackPushforwardAdjunction.{v} _) (pullbackId S).hom =
      (pushforwardId S).inv :=
  Adjunction.conjugateEquiv_leftAdjointIdIso_hom _ _

variable [(pushforward.{v} φ).IsRightAdjoint]

section

variable {K' : GrothendieckTopology D'} {K'' : GrothendieckTopology D''}
  {G : D ⥤ D'} {R' : Sheaf K' RingCat.{u}}
  [Functor.IsContinuous G K K']
  [Functor.IsContinuous (F ⋙ G) J K']
  (ψ : R ⟶ (G.sheafPushforwardContinuous RingCat.{u} K K').obj R')

variable [(pushforward.{v} ψ).IsRightAdjoint]

/-
**SheafOfModules.** 是 Mathlib 中的一个实例，位于命名空间 `SheafOfModules`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (pushforward.{v} (F := F ⋙ G)
    (φ ≫ (F.sheafPushforwardContinuous RingCat.{u} J K).map ψ)).IsRightAdjoint :=
  Functor.isRightAdjoint_of_iso (pushforwardComp.{v} φ ψ)

/-- The composition of two pullback functors on sheaves of modules identifies
to the pullback for the composition. -/
/-
**SheafOfModules.pullbackComp** 是 Mathlib 中的一个定义，位于命名空间 `SheafOfModules`。
形式化陈述：pullbackComp : pullback.{v} φ ⋙ pullback.{v} ψ ≅ pullback.{v} (F
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SheafOfModules.instIsRightAdjointPushforwardCompSheafRingCatMapSheafPush
forwardContinuous`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {
D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {D' : Type u₃} [in…

--- 原说明 ---
The composition of two pullback functors on sheaves of modules identifies
to the pullback for the composition.
-/
noncomputable def pullbackComp :
    pullback.{v} φ ⋙ pullback.{v} ψ ≅
      pullback.{v} (F := F ⋙ G) (φ ≫ (F.sheafPushforwardContinuous RingCat.{u} J K).map ψ) :=
  Adjunction.leftAdjointCompIso
    (pullbackPushforwardAdjunction.{v} φ) (pullbackPushforwardAdjunction.{v} ψ)
    (pullbackPushforwardAdjunction.{v} (F := F ⋙ G)
      (φ ≫ (F.sheafPushforwardContinuous RingCat.{u} J K).map ψ))
    (pushforwardComp φ ψ)

@[simp]
/-
**SheafOfModules.conjugateEquiv_pullbackComp_inv** 是 Mathlib 中的一个引理，位于命名空间 `Shea
fOfModules`。
形式化陈述：conjugateEquiv_pullbackComp_inv : conjugateEquiv ((pullbackPushforwardAdju
nction.{v} φ).comp (pullbackPushforwardAdjunction.{v} ψ)) (pullbackPushforwardAd
junction.{v} _) (pullbackComp.{v} φ ψ).inv = (pushforwardComp.{v} φ ψ).hom
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Adjunction.conjugateEquiv_leftAdjointCompIso_inv`：conjuga
teEquiv_leftAdjointCompIso_inv (e₀₁₂ : G₂₁ ⋙ G₁₀ ≅ G₂₀) : conjugateEquiv (adj₀₁.
comp adj₁₂) adj₀₂ (leftAdjointCompIso adj₀₁ adj₁₂ adj…
· 使用定理 `SheafOfModules.instIsRightAdjointPushforwardCompSheafRingCatMapSheafPush
forwardContinuous`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {
D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {D' : Type u₃} [in…
-/
lemma conjugateEquiv_pullbackComp_inv :
    conjugateEquiv ((pullbackPushforwardAdjunction.{v} φ).comp
      (pullbackPushforwardAdjunction.{v} ψ))
    (pullbackPushforwardAdjunction.{v} _) (pullbackComp.{v} φ ψ).inv =
    (pushforwardComp.{v} φ ψ).hom :=
  Adjunction.conjugateEquiv_leftAdjointCompIso_inv _ _ _ _

variable {G' : D' ⥤ D''} {R'' : Sheaf K'' RingCat.{u}}
  [Functor.IsContinuous G' K' K'']
  [Functor.IsContinuous (G ⋙ G') K K'']
  [Functor.IsContinuous ((F ⋙ G) ⋙ G') J K'']
  [Functor.IsContinuous (F ⋙ G ⋙ G') J K'']
  (ψ' : R' ⟶ (G'.sheafPushforwardContinuous RingCat.{u} K' K'').obj R'')

variable [(pushforward.{v} ψ').IsRightAdjoint]
/-
**SheafOfModules.pullback_assoc** 是 Mathlib 中的一个引理，位于命名空间 `SheafOfModules`。
形式化陈述：pullback_assoc : isoWhiskerLeft _ (pullbackComp.{v} ψ ψ') ≪≫ pullbackComp.
{v} (G
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Adjunction.leftAdjointCompIso_assoc`：leftAdjointCompIso_a
ssoc (e₀₁₂ : G₂₁ ⋙ G₁₀ ≅ G₂₀) (e₁₂₃ : G₃₂ ⋙ G₂₁ ≅ G₃₁) (e₀₁₃ : G₃₁ ⋙ G₁₀ ≅ G₃₀) 
(e₀₂₃ : G₃₂ ⋙ G₂₀ ≅ G₃₀) (h : isoWhisker…
· 使用定理 `SheafOfModules.instIsRightAdjointPushforwardCompSheafRingCatMapSheafPush
forwardContinuous`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {
D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {D' : Type u₃} [in…
· 使用引理 `SheafOfModules.pushforward_assoc`：pushforward_assoc : (pushforward ψ').i
soWhiskerLeft (pushforwardComp φ ψ) ≪≫ pushforwardComp (F
-/
lemma pullback_assoc :
    isoWhiskerLeft _ (pullbackComp.{v} ψ ψ') ≪≫
      pullbackComp.{v} (G := G ⋙ G') φ
        (ψ ≫ (G.sheafPushforwardContinuous RingCat.{u} K K').map ψ') =
    (associator _ _ _).symm ≪≫ isoWhiskerRight (pullbackComp.{v} φ ψ) _ ≪≫
      pullbackComp.{v} (F := F ⋙ G)
        (φ ≫ (F.sheafPushforwardContinuous RingCat.{u} J K).map ψ) ψ' :=
  Adjunction.leftAdjointCompIso_assoc _ _ _ _ _ _ _ _ _ _ (pushforward_assoc φ ψ ψ')

end

/-
**SheafOfModules.pullback_id_comp** 是 Mathlib 中的一个引理，位于命名空间 `SheafOfModules`。
形式化陈述：pullback_id_comp : pullbackComp.{v} (F
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Adjunction.leftAdjointCompIso_id_comp`：leftAdjointCompIso
_id_comp {F₀₀' : C₀ ⥤ C₀} {F₀'₁ : C₀ ⥤ C₁} {G₀'₀ : C₀ ⥤ C₀} {G₁₀' : C₁ ⥤ C₀} (ad
j₀₀' : F₀₀' ⊣ G₀'₀) (adj₀'₁ : F₀'₁ ⊣ G₁₀')…
· 使用定理 `SheafOfModules.instIsRightAdjointPushforwardIdSheafRingCat`：∀ {C : Type 
u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {J : CategoryTheory.Grothendieck
Topology C}   {S : CategoryTheory.Sheaf J RingCa…
· 使用引理 `SheafOfModules.pushforward_comp_id`：pushforward_comp_id : pushforwardCom
p.{v} (F
-/
lemma pullback_id_comp :
    pullbackComp.{v} (F := 𝟭 C) (𝟙 S) φ =
      isoWhiskerRight (pullbackId S) (pullback φ) ≪≫ Functor.leftUnitor _ :=
  Adjunction.leftAdjointCompIso_id_comp _ _ _ _ (pushforward_comp_id φ)
/-
**SheafOfModules.pullback_comp_id** 是 Mathlib 中的一个引理，位于命名空间 `SheafOfModules`。
形式化陈述：pullback_comp_id : pullbackComp.{v} (G
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Adjunction.leftAdjointCompIso_comp_id`：leftAdjointCompIso
_comp_id {F₀₁ : C₀ ⥤ C₁} {F₁₁' : C₁ ⥤ C₁} {G₁₀ : C₁ ⥤ C₀} {G₁'₁ : C₁ ⥤ C₁} (adj₀
₁ : F₀₁ ⊣ G₁₀) (adj₁₁' : F₁₁' ⊣ G₁'₁) (e₀₁…
· 使用定理 `SheafOfModules.instIsRightAdjointPushforwardIdSheafRingCat`：∀ {C : Type 
u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {J : CategoryTheory.Grothendieck
Topology C}   {S : CategoryTheory.Sheaf J RingCa…
· 使用引理 `SheafOfModules.pushforward_id_comp`：pushforward_id_comp : pushforwardCom
p.{v} (G
-/
lemma pullback_comp_id :
    pullbackComp.{v} (G := 𝟭 _) φ (𝟙 R) =
      isoWhiskerLeft _ (pullbackId R) ≪≫ Functor.rightUnitor _ :=
  Adjunction.leftAdjointCompIso_comp_id _ _ _ _ (pushforward_id_comp φ)

end SheafOfModules

