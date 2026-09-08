/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Dagur Asgeirsson, Filippo A. E. Nuccio, Riccardo Brasca
-/
module

public import Mathlib.CategoryTheory.Extensive
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.Topology.Category.CompHausLike.Basic
/-!

# Explicit limits and colimits

This file collects some constructions of explicit limits and colimits in `CompHausLike P`,
which may be useful due to their definitional properties.

## Main definitions

* `HasExplicitFiniteCoproducts`: A typeclass describing the property that forming all finite
  disjoint unions is stable under the property `P`.
  - Given this property, we deduce that `CompHausLike P` has finite coproducts and the inclusion
    functors to other `CompHausLike P'` and to `TopCat` preserve them.

* `HasExplicitPullbacks`: A typeclass describing the property that forming all "explicit pullbacks"
  is stable under the property `P`. Here, explicit pullbacks are defined as a subset of the product.
  - Given this property, we deduce that `CompHausLike P` has pullbacks and the inclusion
    functors to other `CompHausLike P'` and to `TopCat` preserve them.
  - We also define a variant `HasExplicitPullbacksOfInclusions` which is says that explicit
    pullbacks along inclusion maps into finite disjoint unions exist. `Stonean` has this property
    but not the stronger one.

## Main results

* Given `[HasExplicitPullbacksOfInclusions P]` (which is implied by `[HasExplicitPullbacks P]`),
  we provide an instance `FinitaryExtensive (CompHausLike P)`.
-/

@[expose] public section

open CategoryTheory Limits Topology

namespace CompHausLike

universe w u

section FiniteCoproducts

variable {P : TopCat.{max u w} → Prop} {α : Type w} [Finite α] (X : α → CompHausLike P)

/--
A typeclass describing the property that forming the disjoint union is stable under the
property `P`.
-/
/-
**CompHausLike.HasExplicitFiniteCoproduct** 是 Mathlib 中的一个缩写定义，位于命名空间 `CompHausL
ike`。
形式化陈述：HasExplicitFiniteCoproduct
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A typeclass describing the property that forming the disjoint union is stable un
der the
property `P`.
-/
abbrev HasExplicitFiniteCoproduct := HasProp P (Σ (a : α), X a)

variable [HasExplicitFiniteCoproduct X]

/--
The coproduct of a finite family of objects in `CompHaus`, constructed as the disjoint
union with its usual topology.
-/
/-
**CompHausLike.finiteCoproduct** 是 Mathlib 中的一个缩写定义，位于命名空间 `CompHausLike`。
形式化陈述：finiteCoproduct : CompHausLike P
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The coproduct of a finite family of objects in `CompHaus`, constructed as the di
sjoint
union with its usual topology.
-/
abbrev finiteCoproduct : CompHausLike P := CompHausLike.of P (Σ (a : α), X a)

/--
The inclusion of one of the factors into the explicit finite coproduct.
-/
/-
**CompHausLike.finiteCoproduct.** 是 Mathlib 中的一个定义，位于命名空间 `CompHausLike`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion of one of the factors into the explicit finite coproduct.
-/
def finiteCoproduct.ι (a : α) : X a ⟶ finiteCoproduct X :=
  ofHom _
  { toFun := fun x ↦ ⟨a, x⟩
    continuous_toFun := continuous_sigmaMk (σ := fun a ↦ X a) }

/--
To construct a morphism from the explicit finite coproduct, it suffices to
specify a morphism from each of its factors.
This is essentially the universal property of the coproduct.
-/
/-
**CompHausLike.finiteCoproduct.desc** 是 Mathlib 中的一个定义，位于命名空间 `CompHausLike.fini
teCoproduct`。
形式化陈述：{P : TopCat → Prop} →   {α : Type w} →     [inst : Finite α] →       (X : 
α → CompHausLike P) →         [inst_1 : CompHausLike.HasExplicitFiniteCoproduct 
X] →           {B : CompHausLike P} → ((a : α) → X a ⟶ B) → (CompHausLike.finite
Coproduct X ⟶ B)
参数：X : α → CompHausLike P；(a : α) → X a ⟶ B；CompHausLike.finiteCoproduct X ⟶ B。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CompHausLike.is_compact`：∀ {P : TopCat → Prop} (self : CompHausLike P), 
CompactSpace ↑self.toTop
· 使用定理 `CompHausLike.is_hausdorff`：∀ {P : TopCat → Prop} (self : CompHausLike P)
, T2Space ↑self.toTop
· 使用定理 `CompHausLike.instHasPropCarrierToTop`：∀ (P : TopCat → Prop) (X : CompHau
sLike P), CompHausLike.HasProp P ↑X.toTop

--- 原说明 ---
To construct a morphism from the explicit finite coproduct, it suffices to
specify a morphism from each of its factors.
This is essentially the universal property of the coproduct.
-/
def finiteCoproduct.desc {B : CompHausLike P} (e : (a : α) → (X a ⟶ B)) :
    finiteCoproduct X ⟶ B :=
  ofHom _
  { toFun := fun ⟨a, x⟩ ↦ e a x
    continuous_toFun := by
      apply continuous_sigma
      intro a; exact (e a).hom.hom.continuous }

@[reassoc (attr := simp)]
/-
**CompHausLike.finiteCoproduct.** 是 Mathlib 中的一个引理，位于命名空间 `CompHausLike`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma finiteCoproduct.ι_desc {B : CompHausLike P} (e : (a : α) → (X a ⟶ B)) (a : α) :
    finiteCoproduct.ι X a ≫ finiteCoproduct.desc X e = e a := rfl
/-
**CompHausLike.finiteCoproduct.hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `CompHausLike.f
initeCoproduct`。
形式化陈述：∀ {P : TopCat → Prop} {α : Type w} [inst : Finite α] (X : α → CompHausLike
 P)   [inst_1 : CompHausLike.HasExplicitFiniteCoproduct X] {B : CompHausLike P} 
(f g : CompHausLike.finiteCoproduct X ⟶ B),   (∀ (a : α),       CategoryTheory.C
ategoryStruct.comp (CompHausLike.finiteCoproduct.ι X a) f =         CategoryTheo
ry.CategoryStruct.comp (CompHausLike.finiteCoproduct.ι X a) g) →     f = g
参数：X : α → CompHausLike P；f g : CompHausLike.finiteCoproduct X ⟶ B；∀ (a : α),   
    CategoryTheory.CategoryStruct.comp (CompHausLike.finiteCoproduct.ι X a) f = 
        CategoryTheory.CategoryStruct.comp (CompHausLike.finiteCoproduct.ι X a) 
g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ConcreteCategory.ext`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y
 : C) → FunLike (FC X Y) …
· 使用定理 `ContinuousMap.ext`：ext {f g : C(X, Y)} (h : forall a, f a = g a) : f = g
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma finiteCoproduct.hom_ext {B : CompHausLike P} (f g : finiteCoproduct X ⟶ B)
    (h : ∀ a : α, finiteCoproduct.ι X a ≫ f = finiteCoproduct.ι X a ≫ g) : f = g := by
  ext ⟨a, x⟩
  specialize h a
  apply_fun (fun q ↦ q x) at h
  exact h

/-- The coproduct cocone associated to the explicit finite coproduct. -/
/-
**CompHausLike.finiteCoproduct.cofan** 是 Mathlib 中的一个定义，位于命名空间 `CompHausLike.fin
iteCoproduct`。
形式化陈述：{P : TopCat → Prop} →   {α : Type w} →     [Finite α] → (X : α → CompHausL
ike P) → [CompHausLike.HasExplicitFiniteCoproduct X] → CategoryTheory.Limits.Cof
an X
参数：X : α → CompHausLike P。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The coproduct cocone associated to the explicit finite coproduct.
-/
abbrev finiteCoproduct.cofan : Limits.Cofan X :=
  Cofan.mk (finiteCoproduct X) (finiteCoproduct.ι X)

/-- The explicit finite coproduct cocone is a colimit cocone. -/
/-
**CompHausLike.finiteCoproduct.isColimit** 是 Mathlib 中的一个定义，位于命名空间 `CompHausLike
.finiteCoproduct`。
形式化陈述：{P : TopCat → Prop} →   {α : Type w} →     [inst : Finite α] →       (X : 
α → CompHausLike P) →         [inst_1 : CompHausLike.HasExplicitFiniteCoproduct 
X] →           CategoryTheory.Limits.IsColimit (CompHausLike.finiteCoproduct.cof
an X)
参数：X : α → CompHausLike P；CompHausLike.finiteCoproduct.cofan X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The explicit finite coproduct cocone is a colimit cocone.
-/
def finiteCoproduct.isColimit : Limits.IsColimit (finiteCoproduct.cofan X) :=
  Cofan.IsColimit.mk _
    (fun s ↦ desc _ fun a ↦ s.inj a)
    (fun _ _ ↦ ι_desc _ _ _)
    fun _ _ hm ↦ finiteCoproduct.hom_ext _ _ _ fun a ↦
      (ConcreteCategory.hom_ext _ _ fun t ↦ ConcreteCategory.congr_hom (hm a) t)
/-
**CompHausLike.finiteCoproduct.** 是 Mathlib 中的一个引理，位于命名空间 `CompHausLike`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma finiteCoproduct.ι_injective (a : α) : Function.Injective (finiteCoproduct.ι X a) := by
  intro x y hxy
  exact eq_of_heq (Sigma.ext_iff.mp hxy).2
/-
**CompHausLike.finiteCoproduct.** 是 Mathlib 中的一个引理，位于命名空间 `CompHausLike`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma finiteCoproduct.ι_jointly_surjective (R : finiteCoproduct X) :
    ∃ (a : α) (r : X a), R = finiteCoproduct.ι X a r := ⟨R.fst, R.snd, rfl⟩
/-
**CompHausLike.finiteCoproduct.** 是 Mathlib 中的一个引理，位于命名空间 `CompHausLike`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma finiteCoproduct.ι_desc_apply {B : CompHausLike P} {π : (a : α) → X a ⟶ B} (a : α) :
    ∀ x, finiteCoproduct.desc X π (finiteCoproduct.ι X a x) = π a x := by
  tauto
/-
**CompHausLike.** 是 Mathlib 中的一个实例，位于命名空间 `CompHausLike`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasCoproduct X where
  exists_colimit := ⟨finiteCoproduct.cofan X, finiteCoproduct.isColimit X⟩

/-
This linter complains that the universes `u` and `w` only occur together, but `w` appears by itself
in the indexing type of the coproduct. In almost all cases, `w` will be either `0` or `u`, but we
want to allow both possibilities.
-/
set_option linter.checkUnivs false in
variable (P) in
/--
A typeclass describing the property that forming all finite disjoint unions is stable under the
property `P`.
-/
/-
**CompHausLike.HasExplicitFiniteCoproducts** 是 Mathlib 中的一个归纳类型，位于命名空间 `CompHaus
Like`。
形式化陈述：(TopCat → Prop) → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A typeclass describing the property that forming all finite disjoint unions is s
table under the
property `P`.
-/
class HasExplicitFiniteCoproducts : Prop where
  hasProp {α : Type w} [Finite α] (X : α → CompHausLike.{max u w} P) : HasExplicitFiniteCoproduct X

attribute [instance] HasExplicitFiniteCoproducts.hasProp
/-
**CompHausLike.** 是 Mathlib 中的一个实例，位于命名空间 `CompHausLike`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasExplicitFiniteCoproducts.{w} P] (α : Type w) [Finite α] :
    HasColimitsOfShape (Discrete α) (CompHausLike P) where
  has_colimit _ := hasColimit_of_iso Discrete.natIsoFunctor
/-
**CompHausLike.** 是 Mathlib 中的一个实例，位于命名空间 `CompHausLike`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasExplicitFiniteCoproducts.{w} P] : HasFiniteCoproducts (CompHausLike.{max u w} P) where
  out n := by
    let α := ULift.{w} (Fin n)
    let e : Discrete α ≌ Discrete (Fin n) := Discrete.equivalence Equiv.ulift
    exact hasColimitsOfShape_of_equivalence e

variable {P : TopCat.{u} → Prop} [HasExplicitFiniteCoproducts.{0} P]
/-
**CompHausLike.** 是 Mathlib 中的一个示例，位于命名空间 `CompHausLike`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : HasFiniteCoproducts (CompHausLike.{u} P) := inferInstance

/-- The inclusion maps into the explicit finite coproduct are open embeddings. -/
/-
**CompHausLike.finiteCoproduct.isOpenEmbedding_** 是 Mathlib 中的一个引理，位于命名空间 `CompH
ausLike`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion maps into the explicit finite coproduct are open embeddings.
-/
lemma finiteCoproduct.isOpenEmbedding_ι (a : α) :
    IsOpenEmbedding (finiteCoproduct.ι X a) :=
  .sigmaMk (σ := fun a ↦ X a)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The inclusion maps into the abstract finite coproduct are open embeddings. -/
/-
**CompHausLike.Sigma.isOpenEmbedding_** 是 Mathlib 中的一个引理，位于命名空间 `CompHausLike`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion maps into the abstract finite coproduct are open embeddings.
-/
lemma Sigma.isOpenEmbedding_ι (a : α) :
    IsOpenEmbedding (Sigma.ι X a) := by
  refine IsOpenEmbedding.of_comp _ (homeoOfIso ((colimit.isColimit _).coconePointUniqueUpToIso
    (finiteCoproduct.isColimit X))).isOpenEmbedding ?_
  convert! finiteCoproduct.isOpenEmbedding_ι X a
  ext x
  change (Sigma.ι X a ≫ _) x = _
  simp

/-- The functor to `TopCat` preserves finite coproducts if they exist. -/
/-
**CompHausLike.** 是 Mathlib 中的一个实例，位于命名空间 `CompHausLike`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor to `TopCat` preserves finite coproducts if they exist.
-/
instance (P) [HasExplicitFiniteCoproducts.{0} P] :
    PreservesFiniteCoproducts (compHausLikeToTop P) := by
  refine ⟨fun n ↦ ⟨fun {F} ↦ ?_⟩⟩
  suffices PreservesColimit (Discrete.functor (F.obj ∘ Discrete.mk)) (compHausLikeToTop P) from
    preservesColimit_of_iso_diagram _ Discrete.natIsoFunctor.symm
  exact preservesColimit_of_preserves_colimit_cocone (CompHausLike.finiteCoproduct.isColimit _)
    ((isColimitMapCoconeCofanMkEquiv _ _ _).2 (TopCat.sigmaCofanIsColimit _))

/-- The functor to another `CompHausLike` preserves finite coproducts if they exist. -/
/-
**CompHausLike.** 是 Mathlib 中的一个实例，位于命名空间 `CompHausLike`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor to another `CompHausLike` preserves finite coproducts if they exist.
-/
noncomputable instance {P' : TopCat.{u} → Prop}
    (h : ∀ (X : CompHausLike P), P X.toTop → P' X.toTop) :
    PreservesFiniteCoproducts (toCompHausLike h) := by
  have : PreservesFiniteCoproducts (toCompHausLike h ⋙ compHausLikeToTop P') :=
    inferInstanceAs (PreservesFiniteCoproducts (compHausLikeToTop _))
  exact preservesFiniteCoproducts_of_reflects_of_preserves (toCompHausLike h) (compHausLikeToTop P')

end FiniteCoproducts

section Pullbacks

variable {P : TopCat.{u} → Prop} {X Y B : CompHausLike P} (f : X ⟶ B) (g : Y ⟶ B)

/--
A typeclass describing the property that an explicit pullback is stable under the property `P`.
-/
/-
**CompHausLike.HasExplicitPullback** 是 Mathlib 中的一个缩写定义，位于命名空间 `CompHausLike`。
形式化陈述：HasExplicitPullback
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A typeclass describing the property that an explicit pullback is stable under th
e property `P`.
-/
abbrev HasExplicitPullback := HasProp P { xy : X × Y | f xy.fst = g xy.snd }

variable [HasExplicitPullback f g] -- (hP : P (TopCat.of { xy : X × Y | f xy.fst = g xy.snd }))

/--
The pullback of two morphisms `f,g` in `CompHaus`, constructed explicitly as the set of
pairs `(x,y)` such that `f x = g y`, with the topology induced by the product.
-/
/-
**CompHausLike.pullback** 是 Mathlib 中的一个定义，位于命名空间 `CompHausLike`。
形式化陈述：pullback : CompHausLike P
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pullback of two morphisms `f,g` in `CompHaus`, constructed explicitly as the
 set of
pairs `(x,y)` such that `f x = g y`, with the topology induced by the product.
-/
def pullback : CompHausLike P :=
  letI set := { xy : X × Y | f xy.fst = g xy.snd }
  haveI : CompactSpace set :=
    isCompact_iff_compactSpace.mp (isClosed_eq (f.hom.hom.continuous.comp continuous_fst)
      (g.hom.hom.continuous.comp continuous_snd)).isCompact
  CompHausLike.of P set

/--
The projection from the pullback to the first component.
-/
/-
**CompHausLike.pullback.fst** 是 Mathlib 中的一个定义，位于命名空间 `CompHausLike.pullback`。
形式化陈述：{P : TopCat → Prop} →   {X Y B : CompHausLike P} →     (f : X ⟶ B) → (g : 
Y ⟶ B) → [inst : CompHausLike.HasExplicitPullback f g] → CompHausLike.pullback f
 g ⟶ X
参数：f : X ⟶ B；g : Y ⟶ B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The projection from the pullback to the first component.
-/
def pullback.fst : pullback f g ⟶ X :=
  ConcreteCategory.ofHom
  { toFun := fun ⟨⟨x, _⟩, _⟩ ↦ x
    continuous_toFun := Continuous.comp continuous_fst continuous_subtype_val }

/--
The projection from the pullback to the second component.
-/
/-
**CompHausLike.pullback.snd** 是 Mathlib 中的一个定义，位于命名空间 `CompHausLike.pullback`。
形式化陈述：{P : TopCat → Prop} →   {X Y B : CompHausLike P} →     (f : X ⟶ B) → (g : 
Y ⟶ B) → [inst : CompHausLike.HasExplicitPullback f g] → CompHausLike.pullback f
 g ⟶ Y
参数：f : X ⟶ B；g : Y ⟶ B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The projection from the pullback to the second component.
-/
def pullback.snd : pullback f g ⟶ Y :=
  ConcreteCategory.ofHom
  { toFun := fun ⟨⟨_,y⟩,_⟩ ↦ y
    continuous_toFun := Continuous.comp continuous_snd continuous_subtype_val }

@[reassoc]
/-
**CompHausLike.pullback.condition** 是 Mathlib 中的一个定理，位于命名空间 `CompHausLike.pullba
ck`。
形式化陈述：∀ {P : TopCat → Prop} {X Y B : CompHausLike P} (f : X ⟶ B) (g : Y ⟶ B) [in
st : CompHausLike.HasExplicitPullback f g],   CategoryTheory.CategoryStruct.comp
 (CompHausLike.pullback.fst f g) f =     CategoryTheory.CategoryStruct.comp (Com
pHausLike.pullback.snd f g) g
参数：f : X ⟶ B；g : Y ⟶ B；CompHausLike.pullback.fst f g；CompHausLike.pullback.snd f
 g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ConcreteCategory.ext`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y
 : C) → FunLike (FC X Y) …
· 使用定理 `ContinuousMap.ext`：ext {f g : C(X, Y)} (h : forall a, f a = g a) : f = g
-/
lemma pullback.condition : pullback.fst f g ≫ f = pullback.snd f g ≫ g := by
  ext ⟨_, h⟩; exact h

/--
Construct a morphism to the explicit pullback given morphisms to the factors
which are compatible with the maps to the base.
This is essentially the universal property of the pullback.
-/
/-
**CompHausLike.pullback.lift** 是 Mathlib 中的一个定义，位于命名空间 `CompHausLike.pullback`。
形式化陈述：{P : TopCat → Prop} →   {X Y B : CompHausLike P} →     (f : X ⟶ B) →      
 (g : Y ⟶ B) →         [inst : CompHausLike.HasExplicitPullback f g] →          
 {Z : CompHausLike P} →             (a : Z ⟶ X) →               (b : Z ⟶ Y) →   
              CategoryTheory.CategoryStruct.comp a f = CategoryTheory.CategorySt
ruct.comp b g →                   (Z ⟶ CompHausLike.pullback f g)
参数：f : X ⟶ B；g : Y ⟶ B；a : Z ⟶ X；b : Z ⟶ Y；Z ⟶ CompHausLike.pullback f g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a morphism to the explicit pullback given morphisms to the factors
which are compatible with the maps to the base.
This is essentially the universal property of the pullback.
-/
def pullback.lift {Z : CompHausLike P} (a : Z ⟶ X) (b : Z ⟶ Y) (w : a ≫ f = b ≫ g) :
    Z ⟶ pullback f g :=
  ConcreteCategory.ofHom
  { toFun := fun z ↦ ⟨⟨a z, b z⟩, by apply_fun (fun q ↦ q z) at w; exact w⟩
    continuous_toFun := by fun_prop }

@[reassoc (attr := simp)]
/-
**CompHausLike.pullback.lift_fst** 是 Mathlib 中的一个定理，位于命名空间 `CompHausLike.pullbac
k`。
形式化陈述：∀ {P : TopCat → Prop} {X Y B : CompHausLike P} (f : X ⟶ B) (g : Y ⟶ B) [in
st : CompHausLike.HasExplicitPullback f g]   {Z : CompHausLike P} (a : Z ⟶ X) (b
 : Z ⟶ Y)   (w : CategoryTheory.CategoryStruct.comp a f = CategoryTheory.Categor
yStruct.comp b g),   CategoryTheory.CategoryStruct.comp (CompHausLike.pullback.l
ift f g a b w) (CompHausLike.pullback.fst f g) = a
参数：f : X ⟶ B；g : Y ⟶ B；a : Z ⟶ X；b : Z ⟶ Y；w : CategoryTheory.CategoryStruct.com
p a f = CategoryTheory.CategoryStruct.comp b g；CompHausLike.pullback.lift f g a 
b w；CompHausLike.pullback.fst f g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma pullback.lift_fst {Z : CompHausLike P} (a : Z ⟶ X) (b : Z ⟶ Y) (w : a ≫ f = b ≫ g) :
    pullback.lift f g a b w ≫ pullback.fst f g = a := rfl

@[reassoc (attr := simp)]
/-
**CompHausLike.pullback.lift_snd** 是 Mathlib 中的一个定理，位于命名空间 `CompHausLike.pullbac
k`。
形式化陈述：∀ {P : TopCat → Prop} {X Y B : CompHausLike P} (f : X ⟶ B) (g : Y ⟶ B) [in
st : CompHausLike.HasExplicitPullback f g]   {Z : CompHausLike P} (a : Z ⟶ X) (b
 : Z ⟶ Y)   (w : CategoryTheory.CategoryStruct.comp a f = CategoryTheory.Categor
yStruct.comp b g),   CategoryTheory.CategoryStruct.comp (CompHausLike.pullback.l
ift f g a b w) (CompHausLike.pullback.snd f g) = b
参数：f : X ⟶ B；g : Y ⟶ B；a : Z ⟶ X；b : Z ⟶ Y；w : CategoryTheory.CategoryStruct.com
p a f = CategoryTheory.CategoryStruct.comp b g；CompHausLike.pullback.lift f g a 
b w；CompHausLike.pullback.snd f g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma pullback.lift_snd {Z : CompHausLike P} (a : Z ⟶ X) (b : Z ⟶ Y) (w : a ≫ f = b ≫ g) :
    pullback.lift f g a b w ≫ pullback.snd f g = b := rfl
/-
**CompHausLike.pullback.hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `CompHausLike.pullback
`。
形式化陈述：∀ {P : TopCat → Prop} {X Y B : CompHausLike P} (f : X ⟶ B) (g : Y ⟶ B) [in
st : CompHausLike.HasExplicitPullback f g]   {Z : CompHausLike P} (a b : Z ⟶ Com
pHausLike.pullback f g),   CategoryTheory.CategoryStruct.comp a (CompHausLike.pu
llback.fst f g) =       CategoryTheory.CategoryStruct.comp b (CompHausLike.pullb
ack.fst f g) →     CategoryTheory.CategoryStruct.comp a (CompHausLike.pullback.s
nd f g) =         CategoryTheory.CategoryStruct.comp b (CompHausLike.pullback.sn
d f g) →       a = b
参数：f : X ⟶ B；g : Y ⟶ B；a b : Z ⟶ CompHausLike.pullback f g；CompHausLike.pullback
.fst f g；CompHausLike.pullback.fst f g；CompHausLike.pullback.snd f g；CompHausLik
e.pullback.snd f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ConcreteCategory.ext`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y
 : C) → FunLike (FC X Y) …
· 使用定理 `ContinuousMap.ext`：ext {f g : C(X, Y)} (h : forall a, f a = g a) : f = g
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma pullback.hom_ext {Z : CompHausLike P} (a b : Z ⟶ pullback f g)
    (hfst : a ≫ pullback.fst f g = b ≫ pullback.fst f g)
    (hsnd : a ≫ pullback.snd f g = b ≫ pullback.snd f g) : a = b := by
  ext z
  apply_fun (fun q ↦ q z) at hfst hsnd
  apply Subtype.ext
  apply Prod.ext
  · exact hfst
  · exact hsnd

/--
The pullback cone whose cone point is the explicit pullback.
-/
@[simps! pt π]
/-
**CompHausLike.pullback.cone** 是 Mathlib 中的一个定义，位于命名空间 `CompHausLike.pullback`。
形式化陈述：{P : TopCat → Prop} →   {X Y B : CompHausLike P} →     (f : X ⟶ B) → (g : 
Y ⟶ B) → [CompHausLike.HasExplicitPullback f g] → CategoryTheory.Limits.Pullback
Cone f g
参数：f : X ⟶ B；g : Y ⟶ B。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CompHausLike.pullback.condition`：∀ {P : TopCat → Prop} {X Y B : CompHaus
Like P} (f : X ⟶ B) (g : Y ⟶ B) [inst : CompHausLike.HasExplicitPullback f g],  
 CategoryTheory.Categ…

--- 原说明 ---
The pullback cone whose cone point is the explicit pullback.
-/
def pullback.cone : Limits.PullbackCone f g :=
  Limits.PullbackCone.mk (pullback.fst f g) (pullback.snd f g) (pullback.condition f g)

/--
The explicit pullback cone is a limit cone.
-/
@[simps! lift]
/-
**CompHausLike.pullback.isLimit** 是 Mathlib 中的一个定义，位于命名空间 `CompHausLike.pullback
`。
形式化陈述：{P : TopCat → Prop} →   {X Y B : CompHausLike P} →     (f : X ⟶ B) →      
 (g : Y ⟶ B) →         [inst : CompHausLike.HasExplicitPullback f g] → CategoryT
heory.Limits.IsLimit (CompHausLike.pullback.cone f g)
参数：f : X ⟶ B；g : Y ⟶ B；CompHausLike.pullback.cone f g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The explicit pullback cone is a limit cone.
-/
def pullback.isLimit : Limits.IsLimit (pullback.cone f g) :=
  Limits.PullbackCone.isLimitAux _
    (fun s ↦ pullback.lift f g s.fst s.snd s.condition)
    (fun _ ↦ pullback.lift_fst _ _ _ _ _)
    (fun _ ↦ pullback.lift_snd _ _ _ _ _)
    (fun _ _ hm ↦ pullback.hom_ext _ _ _ _ (hm .left) (hm .right))
/-
**CompHausLike.** 是 Mathlib 中的一个实例，位于命名空间 `CompHausLike`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasLimit (cospan f g) where
  exists_limit := ⟨⟨pullback.cone f g, pullback.isLimit f g⟩⟩

/-- The functor to `TopCat` creates pullbacks if they exist. -/
/-
**CompHausLike.** 是 Mathlib 中的一个实例，位于命名空间 `CompHausLike`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor to `TopCat` creates pullbacks if they exist.
-/
noncomputable instance : CreatesLimit (cospan f g) (compHausLikeToTop P) :=
  createsLimitOfFullyFaithfulOfIso (pullback f g)
    ((((TopCat.pullbackConeIsLimit f.hom g.hom).conePointUniqueUpToIso
    (limit.isLimit _)) ≪≫ Limits.lim.mapIso (by rfl ≪≫ (diagramIsoCospan _).symm)))

/-- The functor to `TopCat` preserves pullbacks. -/
/-
**CompHausLike.** 是 Mathlib 中的一个实例，位于命名空间 `CompHausLike`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor to `TopCat` preserves pullbacks.
-/
noncomputable instance : PreservesLimit (cospan f g) (compHausLikeToTop P) :=
  preservesLimit_of_createsLimit_and_hasLimit _ _

/-- The functor to another `CompHausLike` preserves pullbacks. -/
/-
**CompHausLike.** 是 Mathlib 中的一个实例，位于命名空间 `CompHausLike`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor to another `CompHausLike` preserves pullbacks.
-/
noncomputable instance {P' : TopCat → Prop}
    (h : ∀ (X : CompHausLike P), P X.toTop → P' X.toTop) :
    PreservesLimit (cospan f g) (toCompHausLike h) := by
  have : PreservesLimit (cospan f g) (toCompHausLike h ⋙ compHausLikeToTop P') :=
    inferInstanceAs (PreservesLimit _ (compHausLikeToTop _))
  exact preservesLimit_of_reflects_of_preserves (toCompHausLike h) (compHausLikeToTop P')

variable (P) in
/--
A typeclass describing the property that forming all explicit pullbacks is stable under the
property `P`.
-/
/-
**CompHausLike.HasExplicitPullbacks** 是 Mathlib 中的一个归纳类型，位于命名空间 `CompHausLike`。
形式化陈述：(TopCat → Prop) → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A typeclass describing the property that forming all explicit pullbacks is stabl
e under the
property `P`.
-/
class HasExplicitPullbacks : Prop where
  hasProp {X Y B : CompHausLike P} (f : X ⟶ B) (g : Y ⟶ B) : HasExplicitPullback f g

attribute [instance] HasExplicitPullbacks.hasProp
/-
**CompHausLike.** 是 Mathlib 中的一个实例，位于命名空间 `CompHausLike`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasExplicitPullbacks P] : HasPullbacks (CompHausLike P) where
  has_limit F := hasLimit_of_iso (diagramIsoCospan F).symm

variable (P) in
/--
A typeclass describing the property that explicit pullbacks along inclusion maps into disjoint
unions is stable under the property `P`.
-/
/-
**CompHausLike.HasExplicitPullbacksOfInclusions** 是 Mathlib 中的一个归纳类型，位于命名空间 `Com
pHausLike`。
形式化陈述：(P : TopCat → Prop) → [CompHausLike.HasExplicitFiniteCoproducts P] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A typeclass describing the property that explicit pullbacks along inclusion maps
 into disjoint
unions is stable under the property `P`.
-/
class HasExplicitPullbacksOfInclusions [HasExplicitFiniteCoproducts.{0} P] : Prop where
  hasProp : ∀ {X Y Z : CompHausLike P} (f : Z ⟶ X ⨿ Y), HasExplicitPullback coprod.inl f

attribute [instance] HasExplicitPullbacksOfInclusions.hasProp
/-
**CompHausLike.** 是 Mathlib 中的一个实例，位于命名空间 `CompHausLike`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasExplicitPullbacks P] [HasExplicitFiniteCoproducts.{0} P] :
    HasExplicitPullbacksOfInclusions P where
  hasProp _ := inferInstance

end Pullbacks

section FiniteCoproducts

variable {P : TopCat.{u} → Prop} [HasExplicitFiniteCoproducts.{0} P]

/-
**CompHausLike.** 是 Mathlib 中的一个实例，位于命名空间 `CompHausLike`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasExplicitPullbacksOfInclusions P] : HasPullbacksOfInclusions (CompHausLike P) where
  hasPullbackInl _ := inferInstance
/-
**CompHausLike.hasPullbacksOfInclusions** 是 Mathlib 中的一个定理，位于命名空间 `CompHausLike`
。
形式化陈述：hasPullbacksOfInclusions (hP' : forall ⦃X Y B : CompHausLike.{u} P⦄ (f : X
 ⟶ B) (g : Y ⟶ B) (_ : IsOpenEmbedding f), HasExplicitPullback f g) : HasExplici
tPullbacksOfInclusions P
参数：hP' : forall ⦃X Y B : CompHausLike.{u} P⦄ (f : X ⟶ B) (g : Y ⟶ B) (_ : IsOpen
Embedding f), HasExplicitPullback f g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CompHausLike.instHasColimitsOfShapeDiscreteOfHasExplicitFiniteCoproducts
OfFinite`：∀ {P : TopCat → Prop} [CompHausLike.HasExplicitFiniteCoproducts P] (α 
: Type w) [Finite α],   CategoryTheory.Limits.HasColimitsOfShape (Cate…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CompHausLike.Sigma.isOpenEmbedding_ι`：∀ {P : TopCat → Prop} {α : Type w}
 [inst : Finite α] (X : α → CompHausLike P)   [inst_1 : CompHausLike.HasExplicit
FiniteCoproduct X] (a : α)…
· 使用定理 `CompHausLike.HasExplicitFiniteCoproducts.hasProp`：∀ {P : TopCat → Prop} 
[self : CompHausLike.HasExplicitFiniteCoproducts P] {α : Type w} [Finite α]   (X
 : α → CompHausLike P), CompHausLike.H…
-/
theorem hasPullbacksOfInclusions
    (hP' : ∀ ⦃X Y B : CompHausLike.{u} P⦄ (f : X ⟶ B) (g : Y ⟶ B)
      (_ : IsOpenEmbedding f), HasExplicitPullback f g) :
    HasExplicitPullbacksOfInclusions P :=
  { hasProp := by
      intro _ _ _ f
      apply hP'
      exact Sigma.isOpenEmbedding_ι _ _ }

/-- The functor to `TopCat` preserves pullbacks of inclusions if they exist. -/
/-
**CompHausLike.** 是 Mathlib 中的一个实例，位于命名空间 `CompHausLike`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor to `TopCat` preserves pullbacks of inclusions if they exist.
-/
noncomputable instance [HasExplicitPullbacksOfInclusions P] :
    PreservesPullbacksOfInclusions (compHausLikeToTop P) :=
  { preservesPullbackInl := by
      intro X Y Z f
      infer_instance }
/-
**CompHausLike.** 是 Mathlib 中的一个实例，位于命名空间 `CompHausLike`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasExplicitPullbacksOfInclusions P] : FinitaryExtensive (CompHausLike P) :=
  finitaryExtensive_of_preserves_and_reflects (compHausLikeToTop P)
/-
**CompHausLike.finitaryExtensive** 是 Mathlib 中的一个定理，位于命名空间 `CompHausLike`。
形式化陈述：finitaryExtensive (hP' : forall ⦃X Y B : CompHausLike.{u} P⦄ (f : X ⟶ B) (
g : Y ⟶ B) (_ : IsOpenEmbedding f), HasExplicitPullback f g) : FinitaryExtensive
 (CompHausLike P)
参数：hP' : forall ⦃X Y B : CompHausLike.{u} P⦄ (f : X ⟶ B) (g : Y ⟶ B) (_ : IsOpen
Embedding f), HasExplicitPullback f g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CompHausLike.hasPullbacksOfInclusions`：hasPullbacksOfInclusions (hP' : f
orall ⦃X Y B : CompHausLike.{u} P⦄ (f : X ⟶ B) (g : Y ⟶ B) (_ : IsOpenEmbedding 
f), HasExplicitPullback f g…
· 使用定理 `CategoryTheory.finitaryExtensive_of_preserves_and_reflects`：finitaryExte
nsive_of_preserves_and_reflects (F : C ⥤ D) [FinitaryExtensive D] [HasFiniteCopr
oducts C] [HasPullbacksOfInclusions C] [Preserve…
· 使用定理 `CompHausLike.instHasFiniteCoproductsOfHasExplicitFiniteCoproducts`：∀ {P 
: TopCat → Prop} [CompHausLike.HasExplicitFiniteCoproducts P],   CategoryTheory.
Limits.HasFiniteCoproducts (CompHausLike P)
· 使用定理 `CompHausLike.instHasPullbacksOfInclusionsOfHasExplicitPullbacksOfInclusi
ons`：∀ {P : TopCat → Prop} [inst : CompHausLike.HasExplicitFiniteCoproducts P]  
 [CompHausLike.HasExplicitPullbacksOfInclusions P], CategoryTheor…
· 使用定理 `CompHausLike.instPreservesPullbacksOfInclusionsTopCatCompHausLikeToTopOf
HasExplicitPullbacksOfInclusions`：∀ {P : TopCat → Prop} [inst : CompHausLike.Has
ExplicitFiniteCoproducts P]   [CompHausLike.HasExplicitPullbacksOfInclusions P],
   CategoryThe…
· 使用定理 `CategoryTheory.Limits.ReflectsFiniteLimits.reflects`：∀ {C : Type u₁} {in
st : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.
Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.instReflectsFiniteLimitsOfReflectsLimits`：∀ {C : T
ype u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Cate
goryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CompHausLike.instFullTopCatCompHausLikeToTop`：∀ (P : TopCat → Prop), (Co
mpHausLike.compHausLikeToTop P).Full
· 使用定理 `CompHausLike.instFaithfulTopCatCompHausLikeToTop`：∀ (P : TopCat → Prop),
 (CompHausLike.compHausLikeToTop P).Faithful
· 使用定理 `CategoryTheory.Limits.instPreservesColimitsOfShapeDiscreteOfFiniteOfPres
ervesFiniteCoproducts`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} 
C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTh
eor…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CompHausLike.instPreservesFiniteCoproductsTopCatCompHausLikeToTopOfHasEx
plicitFiniteCoproducts`：∀ (P : TopCat → Prop) [CompHausLike.HasExplicitFiniteCop
roducts P],   CategoryTheory.Limits.PreservesFiniteCoproducts (CompHausLike.comp
Haus…
· 使用定理 `CategoryTheory.Limits.ReflectsFiniteColimits.reflects`：∀ {C : Type u₁} {
inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheor
y.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.instReflectsFiniteColimitsOfReflectsColimits`：∀ {C
 : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : 
CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
-/
theorem finitaryExtensive (hP' : ∀ ⦃X Y B : CompHausLike.{u} P⦄ (f : X ⟶ B) (g : Y ⟶ B)
    (_ : IsOpenEmbedding f), HasExplicitPullback f g) :
      FinitaryExtensive (CompHausLike P) :=
  have := hasPullbacksOfInclusions hP'
  finitaryExtensive_of_preserves_and_reflects (compHausLikeToTop P)

end FiniteCoproducts

section Terminal

variable {P : TopCat.{u} → Prop}

/-- A one-element space is terminal in `CompHaus` -/
/-
**CompHausLike.isTerminalPUnit** 是 Mathlib 中的一个定义，位于命名空间 `CompHausLike`。
形式化陈述：isTerminalPUnit [HasProp P PUnit.{u + 1}] : IsTerminal (CompHausLike.of P 
PUnit.{u + 1})
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instCompactSpace`：∀ {X : Type u} [inst : TopologicalSpace X] [Indiscrete
Topology X], CompactSpace X
· 使用定理 `instIndiscreteTopologyPUnit`：IndiscreteTopology PUnit.{u_1 + 1}
· 使用定理 `DiscreteTopology.toT2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X]
 [DiscreteTopology X], T2Space X
· 使用定理 `instDiscreteTopologyPUnit`：DiscreteTopology PUnit.{u_1 + 1}
· 使用定理 `CompHausLike.is_compact`：∀ {P : TopCat → Prop} (self : CompHausLike P), 
CompactSpace ↑self.toTop
· 使用定理 `CompHausLike.is_hausdorff`：∀ {P : TopCat → Prop} (self : CompHausLike P)
, T2Space ↑self.toTop
· 使用定理 `CompHausLike.instHasPropCarrierToTop`：∀ (P : TopCat → Prop) (X : CompHau
sLike P), CompHausLike.HasProp P ↑X.toTop

--- 原说明 ---
A one-element space is terminal in `CompHaus`
-/
def isTerminalPUnit [HasProp P PUnit.{u + 1}] :
    IsTerminal (CompHausLike.of P PUnit.{u + 1}) :=
  haveI : ∀ X, Unique (X ⟶ CompHausLike.of P PUnit.{u + 1}) := fun _ ↦
    ⟨⟨ofHom _ ⟨fun _ ↦ PUnit.unit, continuous_const⟩⟩, fun _ ↦ rfl⟩
  Limits.IsTerminal.ofUnique _

end Terminal

end CompHausLike

