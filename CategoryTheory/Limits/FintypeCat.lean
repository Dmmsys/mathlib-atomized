/-
Copyright (c) 2023 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.FintypeCat
public import Mathlib.CategoryTheory.Limits.Creates
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.CategoryTheory.Limits.Types.Products
public import Mathlib.Data.Finite.Prod
public import Mathlib.Data.Finite.Sigma

/-!
# (Co)limits in the category of finite types

We show that finite (co)limits exist in `FintypeCat` and that they are preserved by the natural
inclusion `FintypeCat.incl`.
-/

@[expose] public section

open CategoryTheory Limits Functor

universe u

namespace CategoryTheory.Limits.FintypeCat

/-
**CategoryTheory.Limits.FintypeCat.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Li
mits.FintypeCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {J : Type} [SmallCategory J] (K : J ⥤ FintypeCat.{u}) (j : J) :
    Finite ((K ⋙ FintypeCat.incl.{u}).obj j) := by
  simp only [comp_obj, FintypeCat.incl_obj]
  infer_instance

/-- Any functor from a finite category to `Type*` that only involves finite objects,
has a finite limit. -/
/-
**CategoryTheory.Limits.FintypeCat.finiteLimitOfFiniteDiagram** 是 Mathlib 中的一个实例
，位于命名空间 `CategoryTheory.Limits.FintypeCat`。
形式化陈述：finiteLimitOfFiniteDiagram {J : Type} [SmallCategory J] [FinCategory J] (K
 : J ⥤ Type*) [forall j, Finite (K.obj j)] : Fintype (limit K)
参数：K : J ⥤ Type*；K.obj j。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Any functor from a finite category to `Type*` that only involves finite objects,
has a finite limit.
-/
noncomputable instance finiteLimitOfFiniteDiagram {J : Type} [SmallCategory J] [FinCategory J]
    (K : J ⥤ Type*) [∀ j, Finite (K.obj j)] : Fintype (limit K) := by
  have : Fintype (sections K) := Fintype.ofFinite (sections K)
  exact Fintype.ofEquiv (sections K) (Types.limitEquivSections K).symm
/-
**CategoryTheory.Limits.FintypeCat.inclusionCreatesFiniteLimits** 是 Mathlib 中的一个
实例，位于命名空间 `CategoryTheory.Limits.FintypeCat`。
形式化陈述：inclusionCreatesFiniteLimits {J : Type} [SmallCategory J] [FinCategory J] 
: CreatesLimitsOfShape J FintypeCat.incl.{u} where CreatesLimit {K}
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `FintypeCat.instFullIncl`：FintypeCat.incl.Full
· 使用定理 `FintypeCat.instFaithfulIncl`：FintypeCat.incl.Faithful
-/
noncomputable instance inclusionCreatesFiniteLimits {J : Type} [SmallCategory J] [FinCategory J] :
    CreatesLimitsOfShape J FintypeCat.incl.{u} where
  CreatesLimit {K} := createsLimitOfFullyFaithfulOfIso
    (FintypeCat.of <| limit <| K ⋙ FintypeCat.incl) (Iso.refl _)

/-- Help typeclass inference to infer creation of finite limits for the forgetful functor. -/
/-
**CategoryTheory.Limits.FintypeCat.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Li
mits.FintypeCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Help typeclass inference to infer creation of finite limits for the forgetful fu
nctor.
-/
noncomputable instance {J : Type} [SmallCategory J] [FinCategory J] :
    CreatesLimitsOfShape J (forget FintypeCat) :=
  FintypeCat.inclusionCreatesFiniteLimits
/-
**CategoryTheory.Limits.FintypeCat.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Li
mits.FintypeCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {J : Type} [SmallCategory J] [FinCategory J] : HasLimitsOfShape J FintypeCat.{u} where
  has_limit F := hasLimit_of_created F FintypeCat.incl
/-
**CategoryTheory.Limits.FintypeCat.hasFiniteLimits** 是 Mathlib 中的一个实例，位于命名空间 `Ca
tegoryTheory.Limits.FintypeCat`。
形式化陈述：hasFiniteLimits : HasFiniteLimits FintypeCat.{u} where out _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.FintypeCat.instHasLimitsOfShapeFintypeCatOfFinCate
gory`：∀ {J : Type} [inst : CategoryTheory.SmallCategory J] [CategoryTheory.FinCa
tegory J],   CategoryTheory.Limits.HasLimitsOfShape J FintypeCat
-/
instance hasFiniteLimits : HasFiniteLimits FintypeCat.{u} where
  out _ := inferInstance
/-
**CategoryTheory.Limits.FintypeCat.inclusion_preservesFiniteLimits** 是 Mathlib 中
的一个实例，位于命名空间 `CategoryTheory.Limits.FintypeCat`。
形式化陈述：inclusion_preservesFiniteLimits : PreservesFiniteLimits FintypeCat.incl.{u
} where preservesFiniteLimits _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.preservesLimitOfShape_of_createsLimitsOfShape_and_hasLimi
tsOfShape`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type
 u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `CategoryTheory.Limits.Types.hasLimitsOfShape`：∀ {J : Type v} [inst : Cat
egoryTheory.Category.{w, v} J] [Small.{u, v} J],   CategoryTheory.Limits.HasLimi
tsOfShape J (Type u)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
-/
noncomputable instance inclusion_preservesFiniteLimits :
    PreservesFiniteLimits FintypeCat.incl.{u} where
  preservesFiniteLimits _ :=
    preservesLimitOfShape_of_createsLimitsOfShape_and_hasLimitsOfShape FintypeCat.incl

/-- Help typeclass inference to infer preservation of finite limits for the forgetful functor. -/
/-
**CategoryTheory.Limits.FintypeCat.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Li
mits.FintypeCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Help typeclass inference to infer preservation of finite limits for the forgetfu
l functor.
-/
noncomputable instance : PreservesFiniteLimits (forget FintypeCat) :=
  FintypeCat.inclusion_preservesFiniteLimits

/-- The categorical product of a finite family in `FintypeCat` is equivalent to the product
as types. -/
/-
**CategoryTheory.Limits.FintypeCat.productEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Limits.FintypeCat`。
形式化陈述：productEquiv {ι : Type*} [Finite ι] (X : ι -> FintypeCat.{u}) : (∏ᶜ X : Fi
ntypeCat) ≃ forall i, X i
参数：X : ι -> FintypeCat.{u}。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The categorical product of a finite family in `FintypeCat` is equivalent to the 
product
as types.
-/
noncomputable def productEquiv {ι : Type*} [Finite ι] (X : ι → FintypeCat.{u}) :
    (∏ᶜ X : FintypeCat) ≃ ∀ i, X i :=
  have : Fintype ι := Fintype.ofFinite _
  haveI : Small.{u} ι :=
    ⟨ULift (Fin (Fintype.card ι)), ⟨(Fintype.equivFin ι).trans Equiv.ulift.symm⟩⟩
  let is₁ : FintypeCat.incl.obj (∏ᶜ fun i ↦ X i) ≅ (∏ᶜ fun i ↦ X i) :=
    PreservesProduct.iso FintypeCat.incl (fun i ↦ X i)
  let is₂ : (∏ᶜ fun i ↦ X i : Type _) ≅ (Shrink.{u} (∀ i, X i)) :=
    Types.Small.productIso (fun i ↦ X i)
  let e : (∀ i, X i) ≃ Shrink.{u} (∀ i, X i) := equivShrink _
  (equivEquivIso.symm is₁).trans ((equivEquivIso.symm is₂).trans e.symm)

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**CategoryTheory.Limits.FintypeCat.productEquiv_apply** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Limits.FintypeCat`。
形式化陈述：productEquiv_apply {ι : Type*} [Finite ι] (X : ι -> FintypeCat.{u}) (x : (
∏ᶜ X : FintypeCat)) (i : ι) : productEquiv X x i = Pi.π X i x
参数：X : ι -> FintypeCat.{u}；x : (∏ᶜ X : FintypeCat)；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.hasFiniteProducts_of_hasFiniteLimits`：∀ (C : Type 
u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFiniteLim
its C],   CategoryTheory.Limits.HasFiniteProduct…
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.Types.Small.productIso_hom_comp_eval_apply`：∀ {J :
 Type v} (F : J → Type u) [inst : Small.{u, v} J] (j : J) (x : ∏ᶜ F),   (equivSh
rink ((j : J) → F j)).symm       ((CategoryTheory.Conc…
· 使用定理 `CategoryTheory.Limits.piComparison_comp_π_apply`：∀ {β : Type w} {C : Typ
e u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u₂}   [inst_1 : Categor
yTheory.Category.{v₂, u₂} D] (G : Cat…
· 使用定理 `CategoryTheory.Limits.hasFiniteLimits_of_hasLimits`：∀ (C : Type u) [inst
 : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasLimits C],   Cate
goryTheory.Limits.HasFiniteLimits C
· 使用定理 `CategoryTheory.Limits.Types.hasLimitsOfSize`：∀ [UnivLE.{v, u}], Category
Theory.Limits.HasLimitsOfSize.{w, v, u, u + 1} (Type u)
-/
lemma productEquiv_apply {ι : Type*} [Finite ι] (X : ι → FintypeCat.{u})
    (x : (∏ᶜ X : FintypeCat)) (i : ι) : productEquiv X x i = Pi.π X i x := by
  simpa [productEquiv, equivEquivIso, equivIsoIso, Iso.toEquiv] using!
    piComparison_comp_π_apply FintypeCat.incl X i x

@[simp]
/-
**CategoryTheory.Limits.FintypeCat.productEquiv_symm_comp_** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.Limits.FintypeCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma productEquiv_symm_comp_π_apply {ι : Type*} [Finite ι] (X : ι → FintypeCat.{u})
    (x : ∀ i, X i) (i : ι) : Pi.π X i ((productEquiv X).symm x) = x i := by
  rw [← productEquiv_apply, Equiv.apply_symm_apply]
/-
**CategoryTheory.Limits.FintypeCat.nonempty_pi_of_nonempty** 是 Mathlib 中的一个实例，位于
命名空间 `CategoryTheory.Limits.FintypeCat`。
形式化陈述：nonempty_pi_of_nonempty {ι : Type*} [Finite ι] (X : ι -> FintypeCat.{u}) [
forall i, Nonempty (X i)] : Nonempty (∏ᶜ X : FintypeCat.{u})
参数：X : ι -> FintypeCat.{u}；X i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.hasFiniteProducts_of_hasFiniteLimits`：∀ (C : Type 
u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFiniteLim
its C],   CategoryTheory.Limits.HasFiniteProduct…
· 使用定理 `Equiv.nonempty_congr`：nonempty_congr (e : α ≃ β) : Nonempty α ↔ Nonempty
 β
· 使用定理 `Pi.instNonempty`：∀ {α : Sort u} {β : α → Sort v} [∀ (a : α), Nonempty (β
 a)], Nonempty ((a : α) → β a)
-/
instance nonempty_pi_of_nonempty {ι : Type*} [Finite ι] (X : ι → FintypeCat.{u})
    [∀ i, Nonempty (X i)] : Nonempty (∏ᶜ X : FintypeCat.{u}) :=
  (Equiv.nonempty_congr <| productEquiv X).mpr inferInstance

/-- The colimit type of a functor from a finite category to Types that only
involves finite objects is finite. -/
/-
**CategoryTheory.Limits.FintypeCat.finite_colimitType** 是 Mathlib 中的一个实例，位于命名空间 
`CategoryTheory.Limits.FintypeCat`。
形式化陈述：finite_colimitType {J : Type*} [SmallCategory J] [FinCategory J] (K : J ⥤ 
Type u) [forall j, Finite (K.obj j)] : Finite K.ColimitType
参数：K : J ⥤ Type u；K.obj j。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.instSigma`：∀ {α : Type u_1} {β : α → Type u_2} [Finite α] [∀ (a :
 α), Finite (β a)], Finite ((a : α) × β a)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α

--- 原说明 ---
The colimit type of a functor from a finite category to Types that only
involves finite objects is finite.
-/
instance finite_colimitType {J : Type*} [SmallCategory J] [FinCategory J]
    (K : J ⥤ Type u) [∀ j, Finite (K.obj j)] : Finite K.ColimitType :=
  Quot.finite _

/-- Any functor from a finite category to `Type*` that only involves finite objects,
has a finite colimit. -/
/-
**CategoryTheory.Limits.FintypeCat.finite_of_isColimit** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Limits.FintypeCat`。
形式化陈述：finite_of_isColimit {J : Type*} [SmallCategory J] [FinCategory J] {K : J ⥤
 Type u} [forall j, Finite (K.obj j)] {c : Cocone K} (hc : IsColimit c) : Finite
 c.pt
参数：K.obj j；hc : IsColimit c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_equiv`：Finite.of_equiv (α : Sort*) [h : Finite α] (f : α ≃ β) 
: Finite β
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.Limits.Types.isColimit_iff_coconeTypesIsColimit`：isColimi
t_iff_coconeTypesIsColimit {F : J ⥤ Type u} (c : Cocone F) : Nonempty (IsColimit
 c) ↔ (F.coconeTypesEquiv.symm c).IsColimit

--- 原说明 ---
Any functor from a finite category to `Type*` that only involves finite objects,
has a finite colimit.
-/
lemma finite_of_isColimit {J : Type*} [SmallCategory J] [FinCategory J]
    {K : J ⥤ Type u} [∀ j, Finite (K.obj j)] {c : Cocone K} (hc : IsColimit c) :
    Finite c.pt :=
  Finite.of_equiv _ ((Types.isColimit_iff_coconeTypesIsColimit c).1 ⟨hc⟩).equiv

/-- Any functor from a finite category to `Type*` that only involves finite objects,
has a finite colimit. -/
/-
**CategoryTheory.Limits.FintypeCat.finiteColimitOfFiniteDiagram** 是 Mathlib 中的一个
实例，位于命名空间 `CategoryTheory.Limits.FintypeCat`。
形式化陈述：finiteColimitOfFiniteDiagram {J : Type} [SmallCategory J] [FinCategory J] 
(K : J ⥤ Type*) [forall j, Finite (K.obj j)] : Fintype (colimit K)
参数：K : J ⥤ Type*；K.obj j。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any functor from a finite category to `Type*` that only involves finite objects,
has a finite colimit.
-/
noncomputable instance finiteColimitOfFiniteDiagram {J : Type} [SmallCategory J] [FinCategory J]
    (K : J ⥤ Type*) [∀ j, Finite (K.obj j)] : Fintype (colimit K) := by
  have : Finite (colimit K) := finite_of_isColimit (colimit.isColimit K)
  apply Fintype.ofFinite
/-
**CategoryTheory.Limits.FintypeCat.inclusionCreatesFiniteColimits** 是 Mathlib 中的
一个实例，位于命名空间 `CategoryTheory.Limits.FintypeCat`。
形式化陈述：inclusionCreatesFiniteColimits {J : Type} [SmallCategory J] [FinCategory J
] : CreatesColimitsOfShape J FintypeCat.incl.{u} where CreatesColimit {K}
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `FintypeCat.instFullIncl`：FintypeCat.incl.Full
· 使用定理 `FintypeCat.instFaithfulIncl`：FintypeCat.incl.Faithful
-/
noncomputable instance inclusionCreatesFiniteColimits {J : Type} [SmallCategory J] [FinCategory J] :
    CreatesColimitsOfShape J FintypeCat.incl.{u} where
  CreatesColimit {K} := createsColimitOfFullyFaithfulOfIso
    (FintypeCat.of <| colimit <| K ⋙ FintypeCat.incl) (Iso.refl _)

/-- Help typeclass inference to infer creation of finite colimits for the forgetful functor. -/
/-
**CategoryTheory.Limits.FintypeCat.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Li
mits.FintypeCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Help typeclass inference to infer creation of finite colimits for the forgetful 
functor.
-/
noncomputable instance {J : Type} [SmallCategory J] [FinCategory J] :
    CreatesColimitsOfShape J (forget FintypeCat) :=
  FintypeCat.inclusionCreatesFiniteColimits
/-
**CategoryTheory.Limits.FintypeCat.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Li
mits.FintypeCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {J : Type} [SmallCategory J] [FinCategory J] : HasColimitsOfShape J FintypeCat.{u} where
  has_colimit F := hasColimit_of_created F FintypeCat.incl
/-
**CategoryTheory.Limits.FintypeCat.hasFiniteColimits** 是 Mathlib 中的一个实例，位于命名空间 `
CategoryTheory.Limits.FintypeCat`。
形式化陈述：hasFiniteColimits : HasFiniteColimits FintypeCat.{u} where out _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.FintypeCat.instHasColimitsOfShapeFintypeCatOfFinCa
tegory`：∀ {J : Type} [inst : CategoryTheory.SmallCategory J] [CategoryTheory.Fin
Category J],   CategoryTheory.Limits.HasColimitsOfShape J FintypeCat
-/
instance hasFiniteColimits : HasFiniteColimits FintypeCat.{u} where
  out _ := inferInstance
/-
**CategoryTheory.Limits.FintypeCat.inclusion_preservesFiniteColimits** 是 Mathlib
 中的一个实例，位于命名空间 `CategoryTheory.Limits.FintypeCat`。
形式化陈述：inclusion_preservesFiniteColimits : PreservesFiniteColimits FintypeCat.inc
l.{u} where preservesFiniteColimits _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.preservesColimitOfShape_of_createsColimitsOfShape_and_has
ColimitsOfShape`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D 
: Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `CategoryTheory.Limits.Types.hasColimitsOfShape`：∀ {J : Type v} [inst : C
ategoryTheory.Category.{w, v} J] [Small.{u, v} J],   CategoryTheory.Limits.HasCo
limitsOfShape J (Type u)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
-/
noncomputable instance inclusion_preservesFiniteColimits :
    PreservesFiniteColimits FintypeCat.incl.{u} where
  preservesFiniteColimits _ :=
    preservesColimitOfShape_of_createsColimitsOfShape_and_hasColimitsOfShape FintypeCat.incl

/-- Help typeclass inference to infer preservation of finite colimits for the forgetful functor. -/
/-
**CategoryTheory.Limits.FintypeCat.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Li
mits.FintypeCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Help typeclass inference to infer preservation of finite colimits for the forget
ful functor.
-/
noncomputable instance : PreservesFiniteColimits (forget FintypeCat) :=
  FintypeCat.inclusion_preservesFiniteColimits
/-
**CategoryTheory.Limits.FintypeCat.jointly_surjective** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Limits.FintypeCat`。
形式化陈述：jointly_surjective {J : Type*} [SmallCategory J] [FinCategory J] (F : J ⥤ 
FintypeCat.{u}) (t : Cocone F) (h : IsColimit t) (x : t.pt) : exists j y, t.ι.ap
p j y = x
参数：F : J ⥤ FintypeCat.{u}；t : Cocone F；h : IsColimit t；x : t.pt。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.preservesColimitsOfShapeOfPreservesFiniteColimits`
：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst
_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.Types.jointly_surjective`：jointly_surjective (F : 
J ⥤ Type u) {t : Cocone F} (h : IsColimit t) (x : t.pt) : exists (j : J) (y : F.
obj j), t.ι.app j y = x
-/
lemma jointly_surjective {J : Type*} [SmallCategory J] [FinCategory J]
    (F : J ⥤ FintypeCat.{u}) (t : Cocone F) (h : IsColimit t) (x : t.pt) :
    ∃ j y, t.ι.app j y = x :=
  let hs := isColimitOfPreserves FintypeCat.incl.{u} h
  Types.jointly_surjective (F ⋙ FintypeCat.incl) hs x

end CategoryTheory.Limits.FintypeCat

