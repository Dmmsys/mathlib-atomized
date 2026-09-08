/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import Mathlib.CategoryTheory.Adjunction.PartialAdjoint
public import Mathlib.CategoryTheory.Adjunction.CompositionIso

/-!
# Pullback of presheaves of modules

Let `F : C ⥤ D` be a functor, `R : Dᵒᵖ ⥤ RingCat` and `S : Cᵒᵖ ⥤ RingCat` be presheaves
of rings, and `φ : S ⟶ F.op ⋙ R` be a morphism of presheaves of rings,
we introduce the pullback functor `pullback : PresheafOfModules S ⥤ PresheafOfModules R`
as the left adjoint of `pushforward : PresheafOfModules R ⥤ PresheafOfModules S`.
The existence of this left adjoint functor is obtained under suitable universe assumptions.

From the compatibility of `pushforward` with respect to composition, we deduce
similar pseudofunctor-like properties of the `pullback` functors.

-/

@[expose] public section

universe v v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄ u

open CategoryTheory Limits Opposite Functor

namespace PresheafOfModules

section

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {F : C ⥤ D} {R : Dᵒᵖ ⥤ RingCat.{u}} {S : Cᵒᵖ ⥤ RingCat.{u}} (φ : S ⟶ F.op ⋙ R)
  [(pushforward.{v} φ).IsRightAdjoint]

/-- The pullback functor `PresheafOfModules S ⥤ PresheafOfModules R` induced by
a morphism of presheaves of rings `S ⟶ F.op ⋙ R`, defined as the left adjoint
functor to the pushforward, when it exists. -/
/-
**PresheafOfModules.pullback** 是 Mathlib 中的一个定义，位于命名空间 `PresheafOfModules`。
形式化陈述：pullback : PresheafOfModules.{v} S ⥤ PresheafOfModules.{v} R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pullback functor `PresheafOfModules S ⥤ PresheafOfModules R` induced by
a morphism of presheaves of rings `S ⟶ F.op ⋙ R`, defined as the left adjoint
functor to the pushforward, when it exists.
-/
noncomputable def pullback : PresheafOfModules.{v} S ⥤ PresheafOfModules.{v} R :=
  (pushforward.{v} φ).leftAdjoint

/-- Given a morphism of presheaves of rings `S ⟶ F.op ⋙ R`, this is the adjunction
between associated pullback and pushforward functors on the categories
of presheaves of modules. -/
/-
**PresheafOfModules.pullbackPushforwardAdjunction** 是 Mathlib 中的一个定义，位于命名空间 `Pre
sheafOfModules`。
形式化陈述：pullbackPushforwardAdjunction : pullback.{v} φ ⊣ pushforward.{v} φ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a morphism of presheaves of rings `S ⟶ F.op ⋙ R`, this is the adjunction
between associated pullback and pushforward functors on the categories
of presheaves of modules.
-/
noncomputable def pullbackPushforwardAdjunction : pullback.{v} φ ⊣ pushforward.{v} φ :=
  Adjunction.ofIsRightAdjoint (pushforward φ)

/-- Given a morphism of presheaves of rings `φ : S ⟶ F.op ⋙ R`, this is the property
that the (partial) left adjoint functor of `pushforward φ` is defined
on a certain object `M : PresheafOfModules S`. -/
/-
**PresheafOfModules.pullbackObjIsDefined** 是 Mathlib 中的一个缩写定义，位于命名空间 `PresheafOf
Modules`。
形式化陈述：pullbackObjIsDefined : ObjectProperty (PresheafOfModules.{v} S)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a morphism of presheaves of rings `φ : S ⟶ F.op ⋙ R`, this is the property
that the (partial) left adjoint functor of `pushforward φ` is defined
on a certain object `M : PresheafOfModules S`.
-/
abbrev pullbackObjIsDefined : ObjectProperty (PresheafOfModules.{v} S) :=
  (pushforward φ).leftAdjointObjIsDefined

end

section

variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {F : C ⥤ D} {R : Dᵒᵖ ⥤ RingCat.{u}} {S : Cᵒᵖ ⥤ RingCat.{u}} (φ : S ⟶ F.op ⋙ R)

/-- Given a morphism of presheaves of rings `φ : S ⟶ F.op ⋙ R`, where `F : C ⥤ D`,
`S : Cᵒᵖ ⥤ RingCat`, `R : Dᵒᵖ ⥤ RingCat` and `X : C`, the (partial) left adjoint
functor of `pushforward φ` is defined on the object `(free S).obj (yoneda.obj X)`:
this object shall be mapped to `(free R).obj (yoneda.obj (F.obj X))`. -/
/-
**PresheafOfModules.pushforwardCompCoyonedaFreeYonedaCorepresentableBy** 是 Mathl
ib 中的一个定义，位于命名空间 `PresheafOfModules`。
形式化陈述：pushforwardCompCoyonedaFreeYonedaCorepresentableBy (X : C) : (pushforward 
φ ⋙ coyoneda.obj (op ((free S).obj (yoneda.obj X)))).CorepresentableBy ((free R)
.obj (yoneda.obj (F.obj X))) where homEquiv {M}
参数：X : C。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Given a morphism of presheaves of rings `φ : S ⟶ F.op ⋙ R`, where `F : C ⥤ D`,
`S : Cᵒᵖ ⥤ RingCat`, `R : Dᵒᵖ ⥤ RingCat` and `X : C`, the (partial) left adjoint
functor of `pushforward φ` is defined on the object `(free S).obj (yoneda.obj X)
`:
this object shall be mapped to `(free R).obj (yoneda.obj (F.obj X))`.
-/
noncomputable def pushforwardCompCoyonedaFreeYonedaCorepresentableBy (X : C) :
    (pushforward φ ⋙ coyoneda.obj (op ((free S).obj (yoneda.obj X)))).CorepresentableBy
      ((free R).obj (yoneda.obj (F.obj X))) where
  homEquiv {M} := freeYonedaEquiv.trans
    (freeYonedaEquiv (M := (pushforward φ).obj M)).symm
  homEquiv_comp {M N} g f := freeYonedaEquiv.injective (by
    dsimp
    erw [Equiv.apply_symm_apply, freeYonedaEquiv_comp]
    conv_rhs => erw [freeYonedaEquiv_comp]
    erw [Equiv.apply_symm_apply]
    rfl)
/-
**PresheafOfModules.pullbackObjIsDefined_free_yoneda** 是 Mathlib 中的一个引理，位于命名空间 `
PresheafOfModules`。
形式化陈述：pullbackObjIsDefined_free_yoneda (X : C) : pullbackObjIsDefined φ ((free S
).obj (yoneda.obj X))
参数：X : C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.CorepresentableBy.isCorepresentable`：∀ {C : Type 
u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {F : CategoryTheory.Functor C (T
ype v)} {X : C}   (e : F.CorepresentableBy X), F…
-/
lemma pullbackObjIsDefined_free_yoneda (X : C) :
    pullbackObjIsDefined φ ((free S).obj (yoneda.obj X)) :=
  (pushforwardCompCoyonedaFreeYonedaCorepresentableBy φ X).isCorepresentable
/-
**PresheafOfModules.pullbackObjIsDefined_eq_top** 是 Mathlib 中的一个引理，位于命名空间 `Presh
eafOfModules`。
形式化陈述：pullbackObjIsDefined_eq_top : pullbackObjIsDefined.{u} φ = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用引理 `CategoryTheory.Functor.leftAdjointObjIsDefined_of_isColimit`：leftAdjoint
ObjIsDefined_of_isColimit {J : Type*} [Category* J] {R : J ⥤ C} {c : Cocone R} (
hc : IsColimit c) [HasColimitsOfShape J D] (h : f…
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `PresheafOfModules.hasColimitsOfShape`：∀ {C : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} C] (R : CategoryTheory.Functor Cᵒᵖ RingCat) (J : Type u₂)
   [inst_1 : CategoryTheor…
· 使用定理 `AddCommGrpCat.hasColimitsOfShape`：∀ {J : Type u} [inst : CategoryTheory.
Category.{v, u} J] [Small.{w, u} J],   CategoryTheory.Limits.HasColimitsOfShape 
J AddCommGrpCat
· 使用引理 `CategoryTheory.Functor.leftAdjointObjIsDefined_colimit`：leftAdjointObjIs
Defined_colimit {J : Type*} [Category* J] (R : J ⥤ C) [HasColimit R] [HasColimit
sOfShape J D] (h : forall (j : J), F.leftAdj…
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用引理 `PresheafOfModules.pullbackObjIsDefined_free_yoneda`：pullbackObjIsDefined
_free_yoneda (X : C) : pullbackObjIsDefined φ ((free S).obj (yoneda.obj X))
-/
lemma pullbackObjIsDefined_eq_top :
    pullbackObjIsDefined.{u} φ = ⊤ := by
  ext M
  simp only [Pi.top_apply, Prop.top_eq_true, iff_true]
  apply leftAdjointObjIsDefined_of_isColimit
    M.isColimitFreeYonedaCoproductsCokernelCofork
  rintro (_ | _)
  all_goals
    apply leftAdjointObjIsDefined_colimit _
      (fun _ ↦ pullbackObjIsDefined_free_yoneda _ _)
/-
**PresheafOfModules.** 是 Mathlib 中的一个实例，位于命名空间 `PresheafOfModules`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (pushforward.{u} φ).IsRightAdjoint :=
  isRightAdjoint_of_leftAdjointObjIsDefined_eq_top
    (pullbackObjIsDefined_eq_top φ)

end

section

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E] {E' : Type u₄} [Category.{v₄} E']

variable {F : C ⥤ D} {R : Dᵒᵖ ⥤ RingCat.{u}} {S : Cᵒᵖ ⥤ RingCat.{u}} (φ : S ⟶ F.op ⋙ R)
  {G : D ⥤ E} {T : Eᵒᵖ ⥤ RingCat.{u}} (ψ : R ⟶ G.op ⋙ T)

/-
**PresheafOfModules.** 是 Mathlib 中的一个实例，位于命名空间 `PresheafOfModules`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (pushforward.{v} (F := 𝟭 C) (𝟙 S)).IsRightAdjoint :=
  isRightAdjoint_of_iso (pushforwardId.{v} S).symm

variable (S) in
/-- The pullback by the identity morphism identifies to the identity functor of the
category of presheaves of modules. -/
/-
**PresheafOfModules.pullbackId** 是 Mathlib 中的一个定义，位于命名空间 `PresheafOfModules`。
形式化陈述：pullbackId : pullback.{v} (F
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `PresheafOfModules.instIsRightAdjointPushforwardIdFunctorOppositeRingCat`
：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {S : CategoryTheory
.Functor Cᵒᵖ RingCat},   (PresheafOfModules.pushforward (Cate…

--- 原说明 ---
The pullback by the identity morphism identifies to the identity functor of the
category of presheaves of modules.
-/
noncomputable def pullbackId : pullback.{v} (F := 𝟭 C) (𝟙 S) ≅ 𝟭 _ :=
  ((pullbackPushforwardAdjunction.{v} (F := 𝟭 C) (𝟙 S))).leftAdjointIdIso (pushforwardId S)

variable [(pushforward.{v} φ).IsRightAdjoint]

section

variable [(pushforward.{v} ψ).IsRightAdjoint]

/-
**PresheafOfModules.** 是 Mathlib 中的一个实例，位于命名空间 `PresheafOfModules`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (pushforward.{v} (F := F ⋙ G) (φ ≫ whiskerLeft F.op ψ)).IsRightAdjoint :=
  isRightAdjoint_of_iso (pushforwardComp.{v} φ ψ)

/-- The composition of two pullback functors on presheaves of modules identifies
to the pullback for the composition. -/
/-
**PresheafOfModules.pullbackComp** 是 Mathlib 中的一个定义，位于命名空间 `PresheafOfModules`。
形式化陈述：pullbackComp : pullback.{v} φ ⋙ pullback.{v} ψ ≅ pullback.{v} (F
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `PresheafOfModules.instIsRightAdjointPushforwardCompFunctorOppositeRingCa
tWhiskerLeftOp`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D :
 Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {E : Type u₃} [ins…

--- 原说明 ---
The composition of two pullback functors on presheaves of modules identifies
to the pullback for the composition.
-/
noncomputable def pullbackComp :
    pullback.{v} φ ⋙ pullback.{v} ψ ≅
      pullback.{v} (F := F ⋙ G) (φ ≫ whiskerLeft F.op ψ) :=
  Adjunction.leftAdjointCompIso
    (pullbackPushforwardAdjunction.{v} φ) (pullbackPushforwardAdjunction.{v} ψ)
    (pullbackPushforwardAdjunction.{v} (F := F ⋙ G) (φ ≫ whiskerLeft F.op ψ))
    (pushforwardComp φ ψ)

variable {T' : E'ᵒᵖ ⥤ RingCat.{u}} {G' : E ⥤ E'} (ψ' : T ⟶ G'.op ⋙ T')
  [(pushforward.{v} ψ').IsRightAdjoint]
/-
**PresheafOfModules.pullback_assoc** 是 Mathlib 中的一个引理，位于命名空间 `PresheafOfModules`
。
形式化陈述：pullback_assoc : isoWhiskerLeft _ (pullbackComp.{v} ψ ψ') ≪≫ pullbackComp.
{v} (G
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Adjunction.leftAdjointCompIso_assoc`：leftAdjointCompIso_a
ssoc (e₀₁₂ : G₂₁ ⋙ G₁₀ ≅ G₂₀) (e₁₂₃ : G₃₂ ⋙ G₂₁ ≅ G₃₁) (e₀₁₃ : G₃₁ ⋙ G₁₀ ≅ G₃₀) 
(e₀₂₃ : G₃₂ ⋙ G₂₀ ≅ G₃₀) (h : isoWhisker…
· 使用定理 `PresheafOfModules.instIsRightAdjointPushforwardCompFunctorOppositeRingCa
tWhiskerLeftOp`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D :
 Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {E : Type u₃} [ins…
· 使用引理 `PresheafOfModules.pushforward_assoc`：pushforward_assoc : (pushforward ψ'
).isoWhiskerLeft (pushforwardComp φ ψ) ≪≫ pushforwardComp (F
-/
lemma pullback_assoc :
    isoWhiskerLeft _ (pullbackComp.{v} ψ ψ') ≪≫
      pullbackComp.{v} (G := G ⋙ G') φ (ψ ≫ whiskerLeft G.op ψ') =
    (associator _ _ _).symm ≪≫ isoWhiskerRight (pullbackComp.{v} φ ψ) _ ≪≫
        pullbackComp.{v} (F := F ⋙ G) (φ ≫ whiskerLeft F.op ψ) ψ' :=
  Adjunction.leftAdjointCompIso_assoc _ _ _ _ _ _ _ _ _ _ (pushforward_assoc φ ψ ψ')

end

/-
**PresheafOfModules.pullback_id_comp** 是 Mathlib 中的一个引理，位于命名空间 `PresheafOfModule
s`。
形式化陈述：pullback_id_comp : pullbackComp.{v} (F
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Adjunction.leftAdjointCompIso_id_comp`：leftAdjointCompIso
_id_comp {F₀₀' : C₀ ⥤ C₀} {F₀'₁ : C₀ ⥤ C₁} {G₀'₀ : C₀ ⥤ C₀} {G₁₀' : C₁ ⥤ C₀} (ad
j₀₀' : F₀₀' ⊣ G₀'₀) (adj₀'₁ : F₀'₁ ⊣ G₁₀')…
· 使用定理 `PresheafOfModules.instIsRightAdjointPushforwardIdFunctorOppositeRingCat`
：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {S : CategoryTheory
.Functor Cᵒᵖ RingCat},   (PresheafOfModules.pushforward (Cate…
· 使用引理 `PresheafOfModules.pushforward_comp_id`：pushforward_comp_id : pushforward
Comp.{v} (F
-/
lemma pullback_id_comp :
    pullbackComp.{v} (F := 𝟭 C) (𝟙 S) φ =
      isoWhiskerRight (pullbackId S) (pullback φ) ≪≫ Functor.leftUnitor _ :=
  Adjunction.leftAdjointCompIso_id_comp _ _ _ _ (pushforward_comp_id φ)
/-
**PresheafOfModules.pullback_comp_id** 是 Mathlib 中的一个引理，位于命名空间 `PresheafOfModule
s`。
形式化陈述：pullback_comp_id : pullbackComp.{v} (G
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Adjunction.leftAdjointCompIso_comp_id`：leftAdjointCompIso
_comp_id {F₀₁ : C₀ ⥤ C₁} {F₁₁' : C₁ ⥤ C₁} {G₁₀ : C₁ ⥤ C₀} {G₁'₁ : C₁ ⥤ C₁} (adj₀
₁ : F₀₁ ⊣ G₁₀) (adj₁₁' : F₁₁' ⊣ G₁'₁) (e₀₁…
· 使用定理 `PresheafOfModules.instIsRightAdjointPushforwardIdFunctorOppositeRingCat`
：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {S : CategoryTheory
.Functor Cᵒᵖ RingCat},   (PresheafOfModules.pushforward (Cate…
· 使用引理 `PresheafOfModules.pushforward_id_comp`：pushforward_id_comp : pushforward
Comp.{v} (G
-/
lemma pullback_comp_id :
    pullbackComp.{v} (G := 𝟭 _) φ (𝟙 R) =
      isoWhiskerLeft _ (pullbackId R) ≪≫ Functor.rightUnitor _ :=
  Adjunction.leftAdjointCompIso_comp_id _ _ _ _ (pushforward_id_comp φ)

end

end PresheafOfModules

