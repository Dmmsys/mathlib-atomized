/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, Filippo A. E. Nuccio, Riccardo Brasca
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Sites.Canonical
public import Mathlib.CategoryTheory.Sites.Coherent.Basic
public import Mathlib.CategoryTheory.Sites.Preserves
/-!

# Sheaves for the extensive topology

This file characterises sheaves for the extensive topology.

## Main result

* `isSheaf_iff_preservesFiniteProducts`: In a finitary extensive category, the sheaves for the
  extensive topology are precisely those preserving finite products.
-/

public section

universe w

namespace CategoryTheory

open Limits Presieve Opposite

variable {C : Type*} [Category* C] {D : Type*} [Category* D]

variable [FinitaryPreExtensive C]

/-- A presieve is *extensive* if it is finite and its arrows induce an isomorphism from the
coproduct to the target. -/
/-
**CategoryTheory.Presieve.Extensive** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory.
Presieve`。
形式化陈述：{C : Type u_1} → [inst : CategoryTheory.Category.{v_1, u_1} C] → {X : C} →
 CategoryTheory.Presieve X → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A presieve is *extensive* if it is finite and its arrows induce an isomorphism f
rom the
coproduct to the target.
-/
class Presieve.Extensive {X : C} (R : Presieve X) : Prop where
  /-- `R` consists of a finite collection of arrows that together induce an isomorphism from the
  coproduct of their sources. -/
  arrows_nonempty_isColimit : ∃ (α : Type) (_ : Finite α) (Z : α → C) (π : (a : α) → (Z a ⟶ X)),
    R = Presieve.ofArrows Z π ∧ Nonempty (IsColimit (Cofan.mk X π))
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X : C} (S : Presieve X) [S.Extensive] : S.HasPairwisePullbacks where
  has_pullbacks := by
    obtain ⟨_, _, _, _, rfl, ⟨hc⟩⟩ := Presieve.Extensive.arrows_nonempty_isColimit (R := S)
    intro _ _ _ _ _ hg
    cases hg
    apply FinitaryPreExtensive.hasPullbacks_of_is_coproduct hc

/--
A finite-product-preserving presheaf is a sheaf for the extensive topology on a category which is
`FinitaryPreExtensive`.
-/
/-
**CategoryTheory.isSheafFor_extensive_of_preservesFiniteProducts** 是 Mathlib 中的一
个定理，位于命名空间 `CategoryTheory`。
形式化陈述：isSheafFor_extensive_of_preservesFiniteProducts {X : C} (S : Presieve X) [
S.Extensive] (F : Cᵒᵖ ⥤ Type w) [PreservesFiniteProducts F] : S.IsSheafFor F
参数：S : Presieve X；F : Cᵒᵖ ⥤ Type w。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Presieve.Extensive.arrows_nonempty_isColimit`：∀ {C : Type
 u_1} {inst : CategoryTheory.Category.{v_1, u_1} C} {X : C} {R : CategoryTheory.
Presieve X}   [self : R.Extensive],   ∃ α,     ∃ …
· 使用定理 `CategoryTheory.instHasPairwisePullbacksOfExtensive`：∀ {C : Type u_1} [in
st : CategoryTheory.Category.{v_1, u_1} C] [CategoryTheory.FinitaryPreExtensive 
C] {X : C}   (S : CategoryTheory.Presiev…
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `CategoryTheory.Presieve.isSheafFor_of_preservesProduct`：isSheafFor_of_pr
eservesProduct [PreservesLimit (Discrete.functor (fun x => op (X x))) F] : (ofAr
rows X c.inj).IsSheafFor F
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.instPreservesLimitsOfShapeDiscreteOfFiniteOfPreser
vesFiniteProducts`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {
D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
A finite-product-preserving presheaf is a sheaf for the extensive topology on a 
category which is
`FinitaryPreExtensive`.
-/
theorem isSheafFor_extensive_of_preservesFiniteProducts {X : C} (S : Presieve X) [S.Extensive]
    (F : Cᵒᵖ ⥤ Type w) [PreservesFiniteProducts F] : S.IsSheafFor F := by
  obtain ⟨α, _, Z, π, rfl, ⟨hc⟩⟩ := Extensive.arrows_nonempty_isColimit (R := S)
  have : (ofArrows Z (Cofan.mk X π).inj).HasPairwisePullbacks :=
    (inferInstance : (ofArrows Z π).HasPairwisePullbacks)
  cases nonempty_fintype α
  exact isSheafFor_of_preservesProduct F _ hc
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {α : Type} [Finite α] (Z : α → C) : (ofArrows Z (fun i ↦ Sigma.ι Z i)).Extensive :=
  ⟨⟨α, inferInstance, Z, (fun i ↦ Sigma.ι Z i), rfl, ⟨coproductIsCoproduct _⟩⟩⟩

/-- Every Yoneda-presheaf is a sheaf for the extensive topology. -/
/-
**CategoryTheory.extensiveTopology.isSheaf_yoneda_obj** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.extensiveTopology`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.FinitaryPreExtensive C] (W : C),   CategoryTheory.Presieve.IsSheaf
 (CategoryTheory.extensiveTopology C) (CategoryTheory.yoneda.obj W)
参数：W : C；CategoryTheory.extensiveTopology C；CategoryTheory.yoneda.obj W。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.extensiveTopology.eq_1`：∀ (C : Type u_1) [inst : Category
Theory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.FinitaryPreExtensive C], 
  CategoryTheory.extensiveT…
· 使用定理 `CategoryTheory.Presieve.isSheaf_coverage`：isSheaf_coverage (K : Coverage
 C) (P : Cᵒᵖ ⥤ Type*) : Presieve.IsSheaf K.toGrothendieck P ↔ (forall {X : C} (R
 : Presieve X), R in K X -> Pr…
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.FinitaryPreExtensive.hasFiniteCoproducts`：∀ {C : Type u} 
{inst : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.FinitaryPreExte
nsive C],   CategoryTheory.Limits.HasFiniteCo…
· 使用定理 `CategoryTheory.isSheafFor_extensive_of_preservesFiniteProducts`：isSheafF
or_extensive_of_preservesFiniteProducts {X : C} (S : Presieve X) [S.Extensive] (
F : Cᵒᵖ ⥤ Type w) [PreservesFiniteProducts F] : S.Is…
· 使用定理 `CategoryTheory.Limits.instPreservesFiniteProductsOfPreservesFiniteLimits
`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [ins
t_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.PreservesLimits.preservesFiniteLimits`：∀ {C : Type
 u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Categor
yTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.yoneda_preservesLimits`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] (X : C),   CategoryTheory.Limits.PreservesLimitsOfSize.{
t, w, v, v, u, v + 1} (Cate…

--- 原说明 ---
Every Yoneda-presheaf is a sheaf for the extensive topology.
-/
theorem extensiveTopology.isSheaf_yoneda_obj (W : C) : Presieve.IsSheaf (extensiveTopology C)
    (yoneda.obj W) := by
  rw [extensiveTopology, isSheaf_coverage]
  intro X R ⟨Y, α, Z, π, hR, hi⟩
  have : IsIso (Sigma.desc (Cofan.inj (Cofan.mk X π))) := hi
  have : R.Extensive := ⟨Y, α, Z, π, hR, ⟨Cofan.isColimitOfIsIsoSigmaDesc (Cofan.mk X π)⟩⟩
  exact isSheafFor_extensive_of_preservesFiniteProducts _ _

/-- The extensive topology on a finitary pre-extensive category is subcanonical. -/
/-
**CategoryTheory.extensiveTopology.subcanonical** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.extensiveTopology`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.FinitaryPreExtensive C],   (CategoryTheory.extensiveTopology C).Su
bcanonical
参数：CategoryTheory.extensiveTopology C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.Subcanonical.of_isSheaf_yoneda_obj`：
of_isSheaf_yoneda_obj (J : GrothendieckTopology C) (h : forall X, Presieve.IsShe
af J (yoneda.obj X)) : Subcanonical J where le_canonical
· 使用定理 `CategoryTheory.extensiveTopology.isSheaf_yoneda_obj`：∀ {C : Type u_1} [i
nst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.FinitaryPre
Extensive C] (W : C),   CategoryTheory.Pr…

--- 原说明 ---
The extensive topology on a finitary pre-extensive category is subcanonical.
-/
instance extensiveTopology.subcanonical : (extensiveTopology C).Subcanonical :=
  GrothendieckTopology.Subcanonical.of_isSheaf_yoneda_obj _ isSheaf_yoneda_obj

variable [FinitaryExtensive C]

/--
A presheaf of sets on a category which is `FinitaryExtensive` is a sheaf iff it preserves finite
products.
-/
/-
**CategoryTheory.Presieve.isSheaf_iff_preservesFiniteProducts** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.Presieve`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.FinitaryPreExtensive C]   [CategoryTheory.FinitaryExtensive C] (F 
: CategoryTheory.Functor Cᵒᵖ (Type w)),   CategoryTheory.Presieve.IsSheaf (Categ
oryTheory.extensiveTopology C) F ↔     CategoryTheory.Limits.PreservesFiniteProd
ucts F
参数：F : CategoryTheory.Functor Cᵒᵖ (Type w)；CategoryTheory.extensiveTopology C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.FinitaryExtensive.hasFiniteCoproducts`：∀ {C : Type u} {in
st : CategoryTheory.Category.{v, u} C} [self : CategoryTheory.FinitaryExtensive 
C],   CategoryTheory.Limits.HasFiniteCopro…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用引理 `CategoryTheory.Presieve.preservesProduct_of_isSheafFor`：preservesProduct
_of_isSheafFor (hF' : (ofArrows X c.inj).IsSheafFor F) : PreservesLimit (Discret
e.functor (fun x => op (X x))) F
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Presieve.isSheaf_coverage`：isSheaf_coverage (K : Coverage
 C) (P : Cᵒᵖ ⥤ Type*) : Presieve.IsSheaf K.toGrothendieck P ↔ (forall {X : C} (R
 : Presieve X), R in K X -> Pr…
· 使用定理 `CategoryTheory.extensiveTopology.eq_1`：∀ (C : Type u_1) [inst : Category
Theory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.FinitaryPreExtensive C], 
  CategoryTheory.extensiveT…
· 使用定理 `CategoryTheory.Limits.Sigma.hom_ext`：∀ {β : Type w} {C : Type u} [inst :
 CategoryTheory.Category.{v, u} C] {f : β → C}   [inst_1 : CategoryTheory.Limits
.HasCoproduct f] {X : C} …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.FinitaryExtensive.isPullback_initial_to_sigma_ι`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Finita
ryExtensive C] {ι : Type u_1}   [inst_2 : Finite ι] …
· 使用定理 `CategoryTheory.Limits.instIsIsoDescι`：∀ {β : Type w} {C : Type u} [inst 
: CategoryTheory.Category.{v, u} C] {f : β → C}   [inst_1 : CategoryTheory.Limit
s.HasCoproduct f],   Categ…
· 使用引理 `CategoryTheory.Limits.preservesLimit_of_iso_diagram`：preservesLimit_of_i
so_diagram {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂) [PreservesLimit K₁ F] : Pre
servesLimit K₂ F where preserves {c} t
· 使用定理 `CategoryTheory.isSheafFor_extensive_of_preservesFiniteProducts`：isSheafF
or_extensive_of_preservesFiniteProducts {X : C} (S : Presieve X) [S.Extensive] (
F : Cᵒᵖ ⥤ Type w) [PreservesFiniteProducts F] : S.Is…

--- 原说明 ---
A presheaf of sets on a category which is `FinitaryExtensive` is a sheaf iff it 
preserves finite
products.
-/
theorem Presieve.isSheaf_iff_preservesFiniteProducts (F : Cᵒᵖ ⥤ Type w) :
    Presieve.IsSheaf (extensiveTopology C) F ↔ PreservesFiniteProducts F := by
  refine ⟨fun hF ↦ ⟨fun n ↦ ⟨fun {K} ↦ ?_⟩⟩, fun hF ↦ ?_⟩
  · rw [extensiveTopology, isSheaf_coverage] at hF
    let Z : Fin n → C := fun i ↦ unop (K.obj ⟨i⟩)
    have : (ofArrows Z (Cofan.mk (∐ Z) (Sigma.ι Z)).inj).HasPairwisePullbacks :=
      inferInstanceAs (ofArrows Z (Sigma.ι Z)).HasPairwisePullbacks
    have : ∀ (i : Fin n), Mono (Cofan.inj (Cofan.mk (∐ Z) (Sigma.ι Z)) i) :=
      inferInstanceAs <| ∀ (i : Fin n), Mono (Sigma.ι Z i)
    let i : K ≅ Discrete.functor (fun i ↦ op (Z i)) := Discrete.natIsoFunctor
    let _ : PreservesLimit (Discrete.functor (fun i ↦ op (Z i))) F :=
        Presieve.preservesProduct_of_isSheafFor F ?_ initialIsInitial _ (coproductIsCoproduct Z)
        (FinitaryExtensive.isPullback_initial_to_sigma_ι Z)
        (hF (Presieve.ofArrows Z (fun i ↦ Sigma.ι Z i)) ?_)
    · exact preservesLimit_of_iso_diagram F i.symm
    · apply hF
      refine ⟨Empty, inferInstance, Empty.elim, IsEmpty.elim inferInstance, rfl, ⟨default,?_, ?_⟩⟩
      · ext b
        cases b
      · simp only [eq_iff_true_of_subsingleton]
    · exact ⟨Fin n, inferInstance, Z, (fun i ↦ Sigma.ι Z i), rfl, instIsIsoDescι⟩
  · rw [extensiveTopology, Presieve.isSheaf_coverage]
    intro X R ⟨Y, α, Z, π, hR, hi⟩
    have : IsIso (Sigma.desc (Cofan.inj (Cofan.mk X π))) := hi
    have : R.Extensive := ⟨Y, α, Z, π, hR, ⟨Cofan.isColimitOfIsIsoSigmaDesc (Cofan.mk X π)⟩⟩
    exact isSheafFor_extensive_of_preservesFiniteProducts R F

/--
A presheaf on a category which is `FinitaryExtensive` is a sheaf iff it preserves finite products.
-/
/-
**CategoryTheory.Presheaf.isSheaf_iff_preservesFiniteProducts** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.Presheaf`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {D : Type u
_2}   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : CategoryTheory.F
initaryPreExtensive C]   [CategoryTheory.FinitaryExtensive C] (F : CategoryTheor
y.Functor Cᵒᵖ D),   CategoryTheory.Presheaf.IsSheaf (CategoryTheory.extensiveTop
ology C) F ↔     CategoryTheory.Limits.PreservesFiniteProducts F
参数：F : CategoryTheory.Functor Cᵒᵖ D；CategoryTheory.extensiveTopology C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.instPreservesLimitsOfShapeDiscreteOfFiniteOfPreser
vesFiniteProducts`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {
D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Presieve.isSheaf_iff_preservesFiniteProducts`：∀ {C : Type
 u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Fin
itaryPreExtensive C]   [CategoryTheory.FinitaryEx…
· 使用定理 `CategoryTheory.Presheaf.IsSheaf.eq_1`：∀ {C : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} C] {A : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u
₂} A]   (J : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.comp_preservesLimitsOfShape`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Ca
tegory.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `CategoryTheory.coyonedaPreservesLimitsOfShape`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] (J : Type w) [inst_1 : CategoryTheory.Category.{
t, w} J]   (X : Cᵒᵖ), CategoryTheor…

--- 原说明 ---
A presheaf on a category which is `FinitaryExtensive` is a sheaf iff it preserve
s finite products.
-/
theorem Presheaf.isSheaf_iff_preservesFiniteProducts (F : Cᵒᵖ ⥤ D) :
    IsSheaf (extensiveTopology C) F ↔ PreservesFiniteProducts F := by
  constructor
  · intro h
    rw [IsSheaf] at h
    refine ⟨fun n ↦ ⟨fun {K} ↦ ⟨fun {c} hc ↦ ?_⟩⟩⟩
    constructor
    apply coyonedaJointlyReflectsLimits
    intro ⟨E⟩
    specialize h E
    rw [Presieve.isSheaf_iff_preservesFiniteProducts] at h
    exact isLimitOfPreserves (F.comp (coyoneda.obj ⟨E⟩)) hc
  · intro _ E
    rw [Presieve.isSheaf_iff_preservesFiniteProducts]
    exact ⟨inferInstance⟩
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (F : Sheaf (extensiveTopology C) D) : PreservesFiniteProducts F.obj :=
  (Presheaf.isSheaf_iff_preservesFiniteProducts F.obj).mp F.property

end CategoryTheory

