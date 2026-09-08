/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.Topology.Sets.Opens
public import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-!
# Opens and Over categories

In this file, given a topological space `X`, and `U : Opens X`,
we show that the category `Over U` (whose objects are the
`V : Opens X` equipped with a morphism `V ⟶ U`) is equivalent
to the category `Opens U`.
This equivalence is bi-continuous, and thus induces an equivalence of sheaf categories.

-/

@[expose] public section

universe u

open CategoryTheory Topology

namespace TopologicalSpace

variable {X : Type u} [TopologicalSpace X] (U : Opens X) {A : Type*} [Category* A]

namespace Opens

set_option backward.defeqAttrib.useBackward true in
/-- If `X` is a topological space and `U : Opens X`,
then the category `Over U` is equivalent to `Opens ↥U`. -/
@[simps!]
/-
**TopologicalSpace.Opens.overEquivalence** 是 Mathlib 中的一个定义，位于命名空间 `TopologicalS
pace.Opens`。
形式化陈述：overEquivalence : Over U ≌ Opens ↥U where functor.obj V
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `X` is a topological space and `U : Opens X`,
then the category `Over U` is equivalent to `Opens ↥U`.
-/
def overEquivalence : Over U ≌ Opens ↥U where
  functor.obj V := ⟨_, IsOpen.preimage (continuous_subtype_val) V.left.isOpen⟩
  functor.map f := homOfLE (Set.preimage_mono (f := Subtype.val) (leOfHom f.left))
  inverse.obj W :=
    Over.mk (Y := ⟨_, (U.isOpenEmbedding'.isOpen_iff_image_isOpen).1 W.isOpen⟩)
      (homOfLE (fun _ _ ↦ by aesop))
  inverse.map f := Over.homMk (homOfLE (Set.image_mono (leOfHom f)))
  unitIso := NatIso.ofComponents (fun V ↦ Over.isoMk (eqToIso (by
    ext x
    dsimp
    simp only [SetLike.mem_coe, Set.mem_image, Set.mem_preimage,
      Subtype.exists, exists_and_left, exists_prop, exists_eq_right_right, iff_self_and]
    apply leOfHom V.hom)))
  counitIso := NatIso.ofComponents (fun V ↦ eqToIso (by aesop))

variable {U} in
/-
**TopologicalSpace.Opens.mem_overEquivalence_functor_obj** 是 Mathlib 中的一个定理，位于命名
空间 `TopologicalSpace.Opens`。
形式化陈述：∀ {X : Type u} [inst : TopologicalSpace X] {U : TopologicalSpace.Opens X} 
{V : CategoryTheory.Over U} {x : ↥U},   x ∈ U.overEquivalence.functor.obj V ↔ ↑x
 ∈ V.left
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma mem_overEquivalence_functor_obj {V : Over U} {x : U} :
  x ∈ U.overEquivalence.functor.obj V ↔ x.1 ∈ V.left := .rfl

section grothendieckTopology

/-
**TopologicalSpace.Opens.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace.Opens`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : U.overEquivalence.functor.IsDenseSubsite
    ((Opens.grothendieckTopology X).over U) (Opens.grothendieckTopology U) where
  functorPushforward_mem_iff {V S} := by
    simp only [Opens.mem_grothendieckTopology, Sieve.mem_functorPushforward_functor]
    constructor
    · intro H x hxV
      obtain ⟨W, f, hW, hxW⟩ := H ⟨x, V.hom.le hxV⟩ hxV
      exact ⟨_, ((U.overEquivalence.symm.toAdjunction.homEquiv _ _ ).symm f).left,
        ⟨_, _, 𝟙 _, hW, rfl⟩, _, hxW, rfl⟩
    · intro H x hxV
      obtain ⟨W, f, ⟨W', hW'V, hWW', hSW'V, rfl⟩, hxW⟩ := H x hxV
      exact ⟨_, U.overEquivalence.functor.map hW'V,
        S.downward_closed hSW'V (U.overEquivalence.unitInv.app W'), hWW'.le hxW⟩
/-
**TopologicalSpace.Opens.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace.Opens`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : U.overEquivalence.symm.inverse.IsDenseSubsite
      ((Opens.grothendieckTopology X).over U) (Opens.grothendieckTopology U) :=
  inferInstanceAs (U.overEquivalence.functor.IsDenseSubsite ..)
/-
**TopologicalSpace.Opens.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace.Opens`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : U.overEquivalence.inverse.IsDenseSubsite
      (Opens.grothendieckTopology U) ((Opens.grothendieckTopology X).over U) :=
  inferInstanceAs (U.overEquivalence.symm.functor.IsDenseSubsite ..)

/-- Sheaves on the over category of `U` are equivalent to sheaves on `U` as a topological space. -/
/-
**TopologicalSpace.Opens.sheafEquivOver** 是 Mathlib 中的一个定义，位于命名空间 `TopologicalSp
ace.Opens`。
形式化陈述：{X : Type u} →   [inst : TopologicalSpace X] →     (U : TopologicalSpace.O
pens X) →       {A : Type u_1} →         [inst_1 : CategoryTheory.Category.{v_1,
 u_1} A] →           CategoryTheory.Sheaf ((Opens.grothendieckTopology X).over U
) A ≌             CategoryTheory.Sheaf (Opens.grothendieckTopology ↥U) A
参数：U : TopologicalSpace.Opens X；(Opens.grothendieckTopology X).over U；Opens.grot
hendieckTopology ↥U。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.Opens.instIsDenseSubsiteSubtypeMemOverGrothendieckTopol
ogyOverInverseOverEquivalence`：∀ {X : Type u} [inst : TopologicalSpace X] (U : T
opologicalSpace.Opens X),   CategoryTheory.Functor.IsDenseSubsite (Opens.grothen
dieckTopolo…

--- 原说明 ---
Sheaves on the over category of `U` are equivalent to sheaves on `U` as a topolo
gical space.
-/
@[simps!] def sheafEquivOver :
    Sheaf ((Opens.grothendieckTopology X).over U) A ≌ Sheaf (Opens.grothendieckTopology U) A :=
  U.overEquivalence.sheafCongr
    ((Opens.grothendieckTopology X).over U) (Opens.grothendieckTopology U) A

/-- `overPullback` and `sheafRestrict` are isomorphic under `sheafEquivOver`. -/
/-
**TopologicalSpace.Opens.overPullbackSheafEquivOver** 是 Mathlib 中的一个定义，位于命名空间 `T
opologicalSpace.Opens`。
形式化陈述：overPullbackSheafEquivOver {X : TopCat} (U : Opens X) : (Opens.grothendiec
kTopology X).overPullback A U ⋙ U.sheafEquivOver.functor ≅ U.sheafRestrict
参数：U : Opens X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`overPullback` and `sheafRestrict` are isomorphic under `sheafEquivOver`.
-/
def overPullbackSheafEquivOver {X : TopCat} (U : Opens X) :
    (Opens.grothendieckTopology X).overPullback A U ⋙ U.sheafEquivOver.functor ≅
      U.sheafRestrict := .refl _
/-
**TopologicalSpace.Opens.** 是 Mathlib 中的一个实例，位于命名空间 `TopologicalSpace.Opens`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X : TopCat} (U : Opens X)
    [((Opens.grothendieckTopology X).overPullback A U).IsRightAdjoint] :
    (U.sheafRestrict (C := A)).IsRightAdjoint :=
  Functor.isRightAdjoint_of_iso U.overPullbackSheafEquivOver

/-- `overPullback` and `sheafRestrict` are isomorphic under `sheafEquivOver`. -/
/-
**TopologicalSpace.Opens.sheafRestrictSheafEquivOver** 是 Mathlib 中的一个定义，位于命名空间 `
TopologicalSpace.Opens`。
形式化陈述：sheafRestrictSheafEquivOver {X : TopCat} (U : Opens X) : U.sheafRestrict ⋙
 U.sheafEquivOver.inverse ≅ (Opens.grothendieckTopology X).overPullback A U
参数：U : Opens X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`overPullback` and `sheafRestrict` are isomorphic under `sheafEquivOver`.
-/
def sheafRestrictSheafEquivOver {X : TopCat} (U : Opens X) :
    U.sheafRestrict ⋙ U.sheafEquivOver.inverse ≅
      (Opens.grothendieckTopology X).overPullback A U :=
  U.overPullbackSheafEquivOver.isoCompInverse.symm

end grothendieckTopology

end Opens

end TopologicalSpace

