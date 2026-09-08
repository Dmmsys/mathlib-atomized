/-
Copyright (c) 2024 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Shapes.Reflexive
public import Mathlib.CategoryTheory.Monad.Equalizer
public import Mathlib.CategoryTheory.Monad.Limits

/-!
# Comonadicity theorems

We prove comonadicity theorems which can establish a given functor is comonadic. In particular, we
show three versions of Beck's comonadicity theorem, and the coreflexive (crude)
comonadicity theorem:

`F` is a comonadic left adjoint if it has a right adjoint, and:

* `C` has, `F` preserves and reflects `F`-split equalizers, see
  `CategoryTheory.Monad.comonadicOfHasPreservesReflectsFSplitEqualizers`
* `F` creates `F`-split coequalizers, see
  `CategoryTheory.Monad.comonadicOfCreatesFSplitEqualizers`
  (The converse of this is also shown, see
  `CategoryTheory.Monad.createsFSplitEqualizersOfComonadic`)
* `C` has and `F` preserves `F`-split equalizers, and `F` reflects isomorphisms, see
  `CategoryTheory.Monad.comonadicOfHasPreservesFSplitEqualizersOfReflectsIsomorphisms`
* `C` has and `F` preserves coreflexive equalizers, and `F` reflects isomorphisms, see
  `CategoryTheory.Monad.comonadicOfHasPreservesCoreflexiveEqualizersOfReflectsIsomorphisms`

This file has been adapted from `Mathlib/CategoryTheory/Monad/Monadicity.lean`.
Please try to keep them in sync.

## Tags

Beck, comonadicity, descent

-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

namespace Comonad

open Limits

noncomputable section

-- Hide the implementation details in this namespace.
namespace ComonadicityInternal

variable {C : Type u₁} {D : Type u₂}
variable [Category.{v₁} C] [Category.{v₁} D]
variable {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)

set_option backward.isDefEq.respectTransparency false in
/-- The "main pair" for a coalgebra `(A, α)` is the pair of morphisms `(G α, η_GA)`. It is always a
coreflexive pair, and will be used to construct the left adjoint to the comparison functor and show
it is an equivalence.
-/
/-
**CategoryTheory.Comonad.ComonadicityInternal.main_pair_coreflexive** 是 Mathlib 
中的一个实例，位于命名空间 `CategoryTheory.Comonad.ComonadicityInternal`。
形式化陈述：main_pair_coreflexive (A : adj.toComonad.Coalgebra) : IsCoreflexivePair (G
.map A.a) (adj.unit.app (G.obj A.A))
参数：A : adj.toComonad.Coalgebra。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsCoreflexivePair.mk'`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {A B : C} {f g : A ⟶ B} (s : B ⟶ A),   CategoryTheory.Cat
egoryStruct.comp f s = Cat…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `CategoryTheory.Comonad.Coalgebra.counit`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {G : CategoryTheory.Comonad C} (self : G.Coalgebra)
,   CategoryTheory.CategorySt…
· 使用定理 `CategoryTheory.Adjunction.right_triangle_components`：∀ {C : Type u₁} [in
st : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.
Category.{v₂, u₂} D]   {F : CategoryTheor…

--- 原说明 ---
The "main pair" for a coalgebra `(A, α)` is the pair of morphisms `(G α, η_GA)`.
 It is always a
coreflexive pair, and will be used to construct the left adjoint to the comparis
on functor and show
it is an equivalence.
-/
instance main_pair_coreflexive (A : adj.toComonad.Coalgebra) :
    IsCoreflexivePair (G.map A.a) (adj.unit.app (G.obj A.A)) := by
  apply IsCoreflexivePair.mk' (G.map (adj.counit.app _)) _ _
  · rw [← G.map_comp, ← G.map_id]
    exact congr_arg G.map A.counit
  · rw [adj.right_triangle_components]
    rfl

/-- The "main pair" for a coalgebra `(A, α)` is the pair of morphisms `(G α, η_GA)`. It is always a
`G`-cosplit pair, and will be used to construct the right adjoint to the comparison functor and show
it is an equivalence.
-/
/-
**CategoryTheory.Comonad.ComonadicityInternal.main_pair_F_cosplit** 是 Mathlib 中的
一个实例，位于命名空间 `CategoryTheory.Comonad.ComonadicityInternal`。
形式化陈述：main_pair_F_cosplit (A : adj.toComonad.Coalgebra) : F.IsCosplitPair (G.map
 A.a) (adj.unit.app (G.obj A.A)) where splittable
参数：A : adj.toComonad.Coalgebra。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The "main pair" for a coalgebra `(A, α)` is the pair of morphisms `(G α, η_GA)`.
 It is always a
`G`-cosplit pair, and will be used to construct the right adjoint to the compari
son functor and show
it is an equivalence.
-/
instance main_pair_F_cosplit (A : adj.toComonad.Coalgebra) :
    F.IsCosplitPair (G.map A.a)
      (adj.unit.app (G.obj A.A)) where
  splittable := ⟨_, _, ⟨beckSplitEqualizer A⟩⟩

/-- The object function for the right adjoint to the comparison functor. -/
/-
**CategoryTheory.Comonad.ComonadicityInternal.comparisonRightAdjointObj** 是 Math
lib 中的一个定义，位于命名空间 `CategoryTheory.Comonad.ComonadicityInternal`。
形式化陈述：comparisonRightAdjointObj (A : adj.toComonad.Coalgebra) [HasEqualizer (G.m
ap A.a) (adj.unit.app _)] : C
参数：A : adj.toComonad.Coalgebra；G.map A.a；adj.unit.app _。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The object function for the right adjoint to the comparison functor.
-/
def comparisonRightAdjointObj (A : adj.toComonad.Coalgebra)
    [HasEqualizer (G.map A.a) (adj.unit.app _)] : C :=
  equalizer (G.map A.a) (adj.unit.app _)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
We have a bijection of homsets which will be used to construct the right adjoint to the comparison
functor.
-/
@[simps!]
/-
**CategoryTheory.Comonad.ComonadicityInternal.comparisonRightAdjointHomEquiv** 是
 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Comonad.ComonadicityInternal`。
形式化陈述：comparisonRightAdjointHomEquiv (A : adj.toComonad.Coalgebra) (B : C) [HasE
qualizer (G.map A.a) (adj.unit.app (G.obj A.A))] : ((comparison adj).obj B ⟶ A) 
≃ (B ⟶ comparisonRightAdjointObj adj A) where toFun f
参数：A : adj.toComonad.Coalgebra；B : C；G.map A.a；adj.unit.app (G.obj A.A)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
We have a bijection of homsets which will be used to construct the right adjoint
 to the comparison
functor.
-/
def comparisonRightAdjointHomEquiv (A : adj.toComonad.Coalgebra) (B : C)
    [HasEqualizer (G.map A.a) (adj.unit.app (G.obj A.A))] :
    ((comparison adj).obj B ⟶ A) ≃ (B ⟶ comparisonRightAdjointObj adj A) where
      toFun f := by
        refine equalizer.lift (adj.homEquiv _ _ f.f) ?_
        simp only [Adjunction.toComonad_coe, Functor.comp_obj, Adjunction.homEquiv_unit,
          Category.assoc, ← G.map_comp, ← f.h, comparison_obj_A, comparison_obj_a]
        rw [Functor.comp_map, Functor.map_comp, Adjunction.unit_naturality_assoc,
          Adjunction.unit_naturality]
      invFun f := by
        refine ⟨(adj.homEquiv _ _).symm (f ≫ (equalizer.ι _ _)), (adj.homEquiv _ _).injective ?_⟩
        simp only [Adjunction.toComonad_coe, Functor.comp_obj, comparison_obj_A, comparison_obj_a,
          Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc,
          Functor.comp_map, Adjunction.homEquiv_unit, Adjunction.unit_naturality_assoc,
          Adjunction.unit_naturality, Adjunction.right_triangle_components_assoc]
        congr 1
        exact (equalizer.condition _ _).symm
      left_inv f := by aesop
      right_inv f := by apply equalizer.hom_ext; simp

set_option backward.isDefEq.respectTransparency false in
/-- Construct the adjunction to the comparison functor.
-/
/-
**CategoryTheory.Comonad.ComonadicityInternal.rightAdjointComparison** 是 Mathlib
 中的一个定义，位于命名空间 `CategoryTheory.Comonad.ComonadicityInternal`。
形式化陈述：rightAdjointComparison [forall A : adj.toComonad.Coalgebra, HasEqualizer (
G.map A.a) (adj.unit.app (G.obj A.A))] : adj.toComonad.Coalgebra ⥤ C
参数：G.map A.a；adj.unit.app (G.obj A.A)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct the adjunction to the comparison functor.
-/
def rightAdjointComparison
    [∀ A : adj.toComonad.Coalgebra, HasEqualizer (G.map A.a)
      (adj.unit.app (G.obj A.A))] :
    adj.toComonad.Coalgebra ⥤ C := by
  refine
    Adjunction.rightAdjointOfEquiv (F := comparison adj)
      (G_obj := fun A => comparisonRightAdjointObj adj A) (fun A B => ?_) ?_
  · apply comparisonRightAdjointHomEquiv
  · intro A B B' g h
    apply equalizer.hom_ext
    simp [Adjunction.homEquiv_unit]

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- Provided we have the appropriate equalizers, we have an adjunction to the comparison functor.
-/
@[simps! counit]
/-
**CategoryTheory.Comonad.ComonadicityInternal.comparisonAdjunction** 是 Mathlib 中
的一个定义，位于命名空间 `CategoryTheory.Comonad.ComonadicityInternal`。
形式化陈述：comparisonAdjunction [forall A : adj.toComonad.Coalgebra, HasEqualizer (G.
map A.a) (adj.unit.app (G.obj A.A))] : comparison adj ⊣ rightAdjointComparison a
dj
参数：G.map A.a；adj.unit.app (G.obj A.A)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Provided we have the appropriate equalizers, we have an adjunction to the compar
ison functor.
-/
def comparisonAdjunction
    [∀ A : adj.toComonad.Coalgebra, HasEqualizer (G.map A.a)
      (adj.unit.app (G.obj A.A))] :
    comparison adj ⊣ rightAdjointComparison adj :=
  Adjunction.adjunctionOfEquivRight _ _

variable {adj}
/-
**CategoryTheory.Comonad.ComonadicityInternal.comparisonAdjunction_counit_f_aux*
* 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Comonad.ComonadicityInternal`。
形式化陈述：comparisonAdjunction_counit_f_aux [forall A : adj.toComonad.Coalgebra, Has
Equalizer (G.map A.a) (adj.unit.app (G.obj A.A))] (A : adj.toComonad.Coalgebra) 
: ((comparisonAdjunction adj).counit.app A).f = (adj.homEquiv _ A.A).symm (equal
izer.ι (G.map A.a) (adj.unit.app (G.obj A.A)))
参数：G.map A.a；adj.unit.app (G.obj A.A)；A : adj.toComonad.Coalgebra。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
-/
theorem comparisonAdjunction_counit_f_aux
    [∀ A : adj.toComonad.Coalgebra, HasEqualizer (G.map A.a)
      (adj.unit.app (G.obj A.A))]
    (A : adj.toComonad.Coalgebra) :
    ((comparisonAdjunction adj).counit.app A).f =
      (adj.homEquiv _ A.A).symm (equalizer.ι (G.map A.a) (adj.unit.app (G.obj A.A))) :=
  congr_arg (adj.homEquiv _ _).symm (Category.id_comp _)

set_option backward.isDefEq.respectTransparency.types false in
/-- This is a fork which is helpful for establishing comonadicity: the morphism from this fork to
the Beck equalizer is the counit for the adjunction on the comparison functor.
-/
@[simps! pt]
/-
**CategoryTheory.Comonad.ComonadicityInternal.counitFork** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.Comonad.ComonadicityInternal`。
形式化陈述：counitFork (A : adj.toComonad.Coalgebra) [HasEqualizer (G.map A.a) (adj.un
it.app (G.obj A.A))] : Fork (F.map (G.map A.a)) (F.map (adj.unit.app (G.obj A.A)
))
参数：A : adj.toComonad.Coalgebra；G.map A.a；adj.unit.app (G.obj A.A)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is a fork which is helpful for establishing comonadicity: the morphism from
 this fork to
the Beck equalizer is the counit for the adjunction on the comparison functor.
-/
def counitFork (A : adj.toComonad.Coalgebra)
    [HasEqualizer (G.map A.a) (adj.unit.app (G.obj A.A))] :
    Fork (F.map (G.map A.a)) (F.map (adj.unit.app (G.obj A.A))) :=
  Fork.ofι (F.map (equalizer.ι (G.map A.a) (adj.unit.app (G.obj A.A))))
    (by rw [← F.map_comp, equalizer.condition, F.map_comp])

@[simp]
/-
**CategoryTheory.Comonad.ComonadicityInternal.unitFork_** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.Comonad.ComonadicityInternal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem unitFork_ι (A : adj.toComonad.Coalgebra)
    [HasEqualizer (G.map A.a) (adj.unit.app (G.obj A.A))] :
    (counitFork A).ι = F.map (equalizer.ι (G.map A.a) (adj.unit.app (G.obj A.A))) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Comonad.ComonadicityInternal.comparisonAdjunction_counit_f** 是 
Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Comonad.ComonadicityInternal`。
形式化陈述：comparisonAdjunction_counit_f [forall A : adj.toComonad.Coalgebra, HasEqua
lizer (G.map A.a) (adj.unit.app (G.obj A.A))] (A : adj.toComonad.Coalgebra) : ((
comparisonAdjunction adj).counit.app A).f = (beckEqualizer A).lift (counitFork A
)
参数：G.map A.a；adj.unit.app (G.obj A.A)；A : adj.toComonad.Coalgebra。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Comonad.ComonadicityInternal.comparisonAdjunction_counit`
：∀ {C : Type u₁} {D : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst
_1 : CategoryTheory.Category.{v₁, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Comonad.ComonadicityInternal.comparisonRightAdjointHomEqu
iv_symm_apply_f`：∀ {C : Type u₁} {D : Type u₂} [inst : CategoryTheory.Category.{
v₁, u₁} C] [inst_1 : CategoryTheory.Category.{v₁, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Adjunction.homEquiv_counit`：∀ {C : Type u₁} [inst : Categ
oryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{
v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Adjunction.toComonad_ε`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, 
u₂} D]   {L : CategoryTheor…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem comparisonAdjunction_counit_f
    [∀ A : adj.toComonad.Coalgebra, HasEqualizer (G.map A.a)
      (adj.unit.app (G.obj A.A))]
    (A : adj.toComonad.Coalgebra) :
    ((comparisonAdjunction adj).counit.app A).f = (beckEqualizer A).lift (counitFork A) := by
  simp [Adjunction.homEquiv_counit]

variable (adj)

/-- The fork which describes the unit of the adjunction: the morphism from this fork to the
equalizer of this pair is the unit.
-/
@[simps!]
/-
**CategoryTheory.Comonad.ComonadicityInternal.unitFork** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.Comonad.ComonadicityInternal`。
形式化陈述：unitFork (B : C) : Fork (G.map (F.map (adj.unit.app B))) (adj.unit.app (G.
obj (F.obj B)))
参数：B : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The fork which describes the unit of the adjunction: the morphism from this fork
 to the
equalizer of this pair is the unit.
-/
def unitFork (B : C) :
    Fork (G.map (F.map (adj.unit.app B)))
      (adj.unit.app (G.obj (F.obj B))) :=
  Fork.ofι (adj.unit.app B) (adj.unit_naturality _)

set_option backward.isDefEq.respectTransparency.types false in
variable {adj} in
/-- The counit fork is a limit provided `F` preserves it. -/
/-
**CategoryTheory.Comonad.ComonadicityInternal.counitLimitOfPreservesEqualizer** 
是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Comonad.ComonadicityInternal`。
形式化陈述：counitLimitOfPreservesEqualizer (A : adj.toComonad.Coalgebra) [HasEqualize
r (G.map A.a) (adj.unit.app (G.obj A.A))] [PreservesLimit (parallelPair (G.map A
.a) (adj.unit.app (G.obj A.A))) F] : IsLimit (counitFork (G
参数：A : adj.toComonad.Coalgebra；G.map A.a；adj.unit.app (G.obj A.A)；parallelPair (
G.map A.a) (adj.unit.app (G.obj A.A))。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The counit fork is a limit provided `F` preserves it.
-/
def counitLimitOfPreservesEqualizer (A : adj.toComonad.Coalgebra)
    [HasEqualizer (G.map A.a) (adj.unit.app (G.obj A.A))]
    [PreservesLimit (parallelPair (G.map A.a) (adj.unit.app (G.obj A.A))) F] :
    IsLimit (counitFork (G := G) A) :=
  isLimitOfHasEqualizerOfPreservesLimit F _ _

/-- The unit fork is a limit provided `F` coreflects it. -/
/-
**CategoryTheory.Comonad.ComonadicityInternal.unitEqualizerOfCoreflectsEqualizer
** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Comonad.ComonadicityInternal`。
形式化陈述：unitEqualizerOfCoreflectsEqualizer (B : C) [ReflectsLimit (parallelPair (G
.map (F.map (adj.unit.app B))) (adj.unit.app (G.obj (F.obj B)))) F] : IsLimit (u
nitFork (adj
参数：B : C；parallelPair (G.map (F.map (adj.unit.app B))) (adj.unit.app (G.obj (F.o
bj B)))。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The unit fork is a limit provided `F` coreflects it.
-/
def unitEqualizerOfCoreflectsEqualizer (B : C)
    [ReflectsLimit (parallelPair (G.map (F.map (adj.unit.app B)))
      (adj.unit.app (G.obj (F.obj B)))) F] :
    IsLimit (unitFork (adj := adj) B) :=
  isLimitOfIsLimitForkMap F _ (beckEqualizer ((comparison adj).obj B))
/-
**CategoryTheory.Comonad.ComonadicityInternal.** 是 Mathlib 中的一个实例，位于命名空间 `Catego
ryTheory.Comonad.ComonadicityInternal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance
    [∀ A : adj.toComonad.Coalgebra, HasEqualizer (G.map A.a) (adj.unit.app (G.obj A.A))]
    (B : C) : HasLimit (parallelPair
      (G.map (F.map (NatTrans.app adj.unit B)))
      (NatTrans.app adj.unit (G.obj (F.obj B)))) :=
  inferInstanceAs <| HasEqualizer
    (G.map ((comparison adj).obj B).a)
    (adj.unit.app (G.obj ((comparison adj).obj B).A))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Comonad.ComonadicityInternal.comparisonAdjunction_unit_app** 是 
Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Comonad.ComonadicityInternal`。
形式化陈述：comparisonAdjunction_unit_app [forall A : adj.toComonad.Coalgebra, HasEqua
lizer (G.map A.a) (adj.unit.app (G.obj A.A))] (B : C) : (comparisonAdjunction ad
j).unit.app B = limit.lift _ (unitFork adj B)
参数：G.map A.a；adj.unit.app (G.obj A.A)；B : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.equalizer.hom_ext`：∀ {C : Type u} {X Y : C} [inst 
: CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   [inst_1 : CategoryTheory.Lim
its.HasEqualizer f g] {W : C}…
· 使用定理 `CategoryTheory.Comonad.ComonadicityInternal.instHasLimitWalkingParallelP
airParallelPairMapAppUnitObjOfHasEqualizerAA`：∀ {C : Type u₁} {D : Type u₂} [ins
t : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Category.{v₁, u
₂} D]   {F : CategoryTheor…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Adjunction.homEquiv_unit`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.equalizer.lift.congr_simp`：∀ {C : Type u} {X Y : C
} [inst : CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   [inst_1 : CategoryTh
eory.Limits.HasEqualizer f g] {W : C}…
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem comparisonAdjunction_unit_app
    [∀ A : adj.toComonad.Coalgebra, HasEqualizer (G.map A.a) (adj.unit.app (G.obj A.A))] (B : C) :
    (comparisonAdjunction adj).unit.app B = limit.lift _ (unitFork adj B) := by
  apply equalizer.hom_ext
  change
    equalizer.lift ((adj.homEquiv B _) (𝟙 _)) _ ≫ equalizer.ι _ _ =
      equalizer.lift _ _ ≫ equalizer.ι _ _
  simp [Adjunction.homEquiv_unit]

end ComonadicityInternal

open CategoryTheory Adjunction Comonad ComonadicityInternal

variable {C : Type u₁} {D : Type u₂}
variable [Category.{v₁} C] [Category.{v₁} D]
variable {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)

set_option backward.defeqAttrib.useBackward true in
variable (G) in
/--
If `F` is comonadic, it creates limits of `F`-cosplit pairs. This is the "boring" direction of
Beck's comonadicity theorem, the converse is given in `comonadicOfCreatesFSplitEqualizers`.
-/
@[instance_reducible]
/-
**CategoryTheory.Comonad.createsFSplitEqualizersOfComonadic** 是 Mathlib 中的一个定义，位
于命名空间 `CategoryTheory.Comonad`。
形式化陈述：createsFSplitEqualizersOfComonadic [ComonadicLeftAdjoint F] ⦃A B⦄ (f g : A
 ⟶ B) [F.IsCosplitPair f g] : CreatesLimit (parallelPair f g) F
参数：f g : A ⟶ B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F` is comonadic, it creates limits of `F`-cosplit pairs. This is the "boring
" direction of
Beck's comonadicity theorem, the converse is given in `comonadicOfCreatesFSplitE
qualizers`.
-/
def createsFSplitEqualizersOfComonadic [ComonadicLeftAdjoint F] ⦃A B⦄ (f g : A ⟶ B)
    [F.IsCosplitPair f g] : CreatesLimit (parallelPair f g) F := by
  apply +allowSynthFailures comonadicCreatesLimitOfPreservesLimit
  all_goals
    apply @preservesLimit_of_iso_diagram _ _ _ _ _ _ _ _ _ (diagramIsoParallelPair.{v₁} _).symm ?_
    dsimp
    infer_instance

section BeckComonadicity

/-- Dual to `Monad.HasCoequalizerOfIsSplitPair`. -/
/-
**CategoryTheory.Comonad.HasEqualizerOfIsCosplitPair** 是 Mathlib 中的一个归纳类型，位于命名空间
 `CategoryTheory.Comonad`。
形式化陈述：{C : Type u₁} →   {D : Type u₂} →     [inst : CategoryTheory.Category.{v₁,
 u₁} C] →       [inst_1 : CategoryTheory.Category.{v₁, u₂} D] → CategoryTheory.F
unctor C D → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Dual to `Monad.HasCoequalizerOfIsSplitPair`.
-/
class HasEqualizerOfIsCosplitPair (F : C ⥤ D) : Prop where
  /-- If `f, g` is an `F`-cosplit pair, then they have an equalizer. -/
  out : ∀ {A B} (f g : A ⟶ B) [F.IsCosplitPair f g], HasEqualizer f g
/-
**CategoryTheory.Comonad.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Comonad`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasEqualizerOfIsCosplitPair F] : ∀ (A : Coalgebra adj.toComonad),
    HasEqualizer (G.map A.a)
      (adj.unit.app (G.obj A.A)) :=
  fun _ => HasEqualizerOfIsCosplitPair.out F _ _

/-- Dual to `Monad.PreservesColimitOfIsSplitPair`. -/
/-
**CategoryTheory.Comonad.PreservesLimitOfIsCosplitPair** 是 Mathlib 中的一个归纳类型，位于命名
空间 `CategoryTheory.Comonad`。
形式化陈述：{C : Type u₁} →   {D : Type u₂} →     [inst : CategoryTheory.Category.{v₁,
 u₁} C] →       [inst_1 : CategoryTheory.Category.{v₁, u₂} D] → CategoryTheory.F
unctor C D → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Dual to `Monad.PreservesColimitOfIsSplitPair`.
-/
class PreservesLimitOfIsCosplitPair (F : C ⥤ D) where
  /-- If `f, g` is an `F`-cosplit pair, then `F` preserves limits of `parallelPair f g`. -/
  out : ∀ {A B} (f g : A ⟶ B) [F.IsCosplitPair f g], PreservesLimit (parallelPair f g) F
/-
**CategoryTheory.Comonad.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Comonad`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {A B} (f g : A ⟶ B) [F.IsCosplitPair f g] [PreservesLimitOfIsCosplitPair F] :
    PreservesLimit (parallelPair f g) F := PreservesLimitOfIsCosplitPair.out f g
/-
**CategoryTheory.Comonad.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Comonad`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [PreservesLimitOfIsCosplitPair F] : ∀ (A : Coalgebra adj.toComonad),
    PreservesLimit (parallelPair (G.map A.a) (NatTrans.app adj.unit (G.obj A.A))) F :=
  fun _ => PreservesLimitOfIsCosplitPair.out _ _

/-- Dual to `Monad.ReflectsColimitOfIsSplitPair`. -/
/-
**CategoryTheory.Comonad.ReflectsLimitOfIsCosplitPair** 是 Mathlib 中的一个归纳类型，位于命名空
间 `CategoryTheory.Comonad`。
形式化陈述：{C : Type u₁} →   {D : Type u₂} →     [inst : CategoryTheory.Category.{v₁,
 u₁} C] →       [inst_1 : CategoryTheory.Category.{v₁, u₂} D] → CategoryTheory.F
unctor C D → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Dual to `Monad.ReflectsColimitOfIsSplitPair`.
-/
class ReflectsLimitOfIsCosplitPair (F : C ⥤ D) where
  /-- If `f, g` is an `F`-cosplit pair, then `F` reflects limits for `parallelPair f g`. -/
  out : ∀ {A B} (f g : A ⟶ B) [F.IsCosplitPair f g], ReflectsLimit (parallelPair f g) F
/-
**CategoryTheory.Comonad.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Comonad`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {A B} (f g : A ⟶ B) [F.IsCosplitPair f g] [ReflectsLimitOfIsCosplitPair F] :
    ReflectsLimit (parallelPair f g) F := ReflectsLimitOfIsCosplitPair.out f g
/-
**CategoryTheory.Comonad.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Comonad`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [ReflectsLimitOfIsCosplitPair F] : ∀ (A : Coalgebra adj.toComonad),
    ReflectsLimit (parallelPair (G.map A.a)
      (NatTrans.app adj.unit (G.obj A.A))) F :=
  fun _ => ReflectsLimitOfIsCosplitPair.out _ _

set_option backward.isDefEq.respectTransparency.types false in
/-- To show `F` is a comonadic left adjoint, we can show it preserves and reflects `F`-split
equalizers, and `C` has them.
-/
@[instance_reducible]
/-
**CategoryTheory.Comonad.comonadicOfHasPreservesReflectsFSplitEqualizers** 是 Mat
hlib 中的一个定义，位于命名空间 `CategoryTheory.Comonad`。
形式化陈述：comonadicOfHasPreservesReflectsFSplitEqualizers [HasEqualizerOfIsCosplitPa
ir F] [PreservesLimitOfIsCosplitPair F] [ReflectsLimitOfIsCosplitPair F] : Comon
adicLeftAdjoint F where R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
To show `F` is a comonadic left adjoint, we can show it preserves and reflects `
F`-split
equalizers, and `C` has them.
-/
def comonadicOfHasPreservesReflectsFSplitEqualizers [HasEqualizerOfIsCosplitPair F]
    [PreservesLimitOfIsCosplitPair F] [ReflectsLimitOfIsCosplitPair F] :
    ComonadicLeftAdjoint F where
  R := G
  adj := adj
  eqv := by
    have : ∀ (X : Coalgebra adj.toComonad), IsIso ((comparisonAdjunction adj).counit.app X) := by
      intro X
      apply @isIso_of_reflects_iso _ _ _ _ _ _ _ (Comonad.forget adj.toComonad) ?_ _
      · change IsIso ((comparisonAdjunction adj).counit.app X).f
        rw [comparisonAdjunction_counit_f]
        change
          IsIso
            (IsLimit.conePointUniqueUpToIso (beckEqualizer X)
                (counitLimitOfPreservesEqualizer X)).inv
        exact (IsLimit.conePointUniqueUpToIso _ _).isIso_inv
    have : ∀ (Y : C), IsIso ((comparisonAdjunction adj).unit.app Y) := by
      intro Y
      rw [comparisonAdjunction_unit_app]
      change IsIso (IsLimit.conePointUniqueUpToIso _ ?_).inv
      · infer_instance
      apply @unitEqualizerOfCoreflectsEqualizer _ _ _ _ _ _ _ _ ?_
      let _ :
        F.IsCosplitPair (G.map (F.map (adj.unit.app Y)))
          (adj.unit.app (G.obj (F.obj Y))) :=
        ComonadicityInternal.main_pair_F_cosplit _ ((comparison adj).obj Y)
      infer_instance
    exact (comparisonAdjunction adj).toEquivalence.symm.isEquivalence_inverse

/-- Dual to `Monad.CreatesColimitOfIsSplitPair`. -/
/-
**CategoryTheory.Comonad.CreatesLimitOfIsCosplitPair** 是 Mathlib 中的一个归纳类型，位于命名空间
 `CategoryTheory.Comonad`。
形式化陈述：{C : Type u₁} →   {D : Type u₂} →     [inst : CategoryTheory.Category.{v₁,
 u₁} C] →       [inst_1 : CategoryTheory.Category.{v₁, u₂} D] → CategoryTheory.F
unctor C D → Type (max (max u₁ u₂) v₁)
参数：max (max u₁ u₂) v₁。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Dual to `Monad.CreatesColimitOfIsSplitPair`.
-/
class CreatesLimitOfIsCosplitPair (F : C ⥤ D) where
  /-- If `f, g` is an `F`-cosplit pair, then `F` creates limits of `parallelPair f g`. -/
  out : ∀ {A B} (f g : A ⟶ B) [F.IsCosplitPair f g], CreatesLimit (parallelPair f g) F
/-
**CategoryTheory.Comonad.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Comonad`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {A B} (f g : A ⟶ B) [F.IsCosplitPair f g] [CreatesLimitOfIsCosplitPair F] :
    CreatesLimit (parallelPair f g) F := CreatesLimitOfIsCosplitPair.out f g
/-
**CategoryTheory.Comonad.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Comonad`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CreatesLimitOfIsCosplitPair F] : ∀ (A : Coalgebra adj.toComonad),
    CreatesLimit (parallelPair (G.map A.a)
      (NatTrans.app adj.unit (G.obj A.A))) F :=
  fun _ => CreatesLimitOfIsCosplitPair.out _ _

/--
Beck's comonadicity theorem. If `F` has a right adjoint and creates equalizers of `F`-cosplit pairs,
then it is comonadic.
This is the converse of `createsFSplitEqualizersOfComonadic`.
-/
@[instance_reducible]
/-
**CategoryTheory.Comonad.comonadicOfCreatesFSplitEqualizers** 是 Mathlib 中的一个定义，位
于命名空间 `CategoryTheory.Comonad`。
形式化陈述：comonadicOfCreatesFSplitEqualizers [CreatesLimitOfIsCosplitPair F] : Comon
adicLeftAdjoint F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Beck's comonadicity theorem. If `F` has a right adjoint and creates equalizers o
f `F`-cosplit pairs,
then it is comonadic.
This is the converse of `createsFSplitEqualizersOfComonadic`.
-/
def comonadicOfCreatesFSplitEqualizers [CreatesLimitOfIsCosplitPair F] :
    ComonadicLeftAdjoint F := by
  have I {A B} (f g : A ⟶ B) [F.IsCosplitPair f g] : HasLimit (parallelPair f g ⋙ F) := by
    rw [hasLimit_iff_of_iso (diagramIsoParallelPair _)]
    exact inferInstanceAs <| HasEqualizer (F.map f) (F.map g)
  have : HasEqualizerOfIsCosplitPair F := ⟨fun _ _ => hasLimit_of_created (parallelPair _ _) F⟩
  have : PreservesLimitOfIsCosplitPair F := ⟨by intros; infer_instance⟩
  have : ReflectsLimitOfIsCosplitPair F := ⟨by intros; infer_instance⟩
  exact comonadicOfHasPreservesReflectsFSplitEqualizers adj

/-- An alternate version of Beck's comonadicity theorem. If `F` reflects isomorphisms, preserves
equalizers of `F`-cosplit pairs and `C` has equalizers of `F`-cosplit pairs, then it is comonadic.
-/
@[instance_reducible]
/-
**CategoryTheory.Comonad.comonadicOfHasPreservesFSplitEqualizersOfReflectsIsomor
phisms** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Comonad`。
形式化陈述：comonadicOfHasPreservesFSplitEqualizersOfReflectsIsomorphisms [F.ReflectsI
somorphisms] [HasEqualizerOfIsCosplitPair F] [PreservesLimitOfIsCosplitPair F] :
 ComonadicLeftAdjoint F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An alternate version of Beck's comonadicity theorem. If `F` reflects isomorphism
s, preserves
equalizers of `F`-cosplit pairs and `C` has equalizers of `F`-cosplit pairs, the
n it is comonadic.
-/
def comonadicOfHasPreservesFSplitEqualizersOfReflectsIsomorphisms [F.ReflectsIsomorphisms]
    [HasEqualizerOfIsCosplitPair F] [PreservesLimitOfIsCosplitPair F] :
    ComonadicLeftAdjoint F := by
  have : ReflectsLimitOfIsCosplitPair F := ⟨fun f g _ => by
    have := HasEqualizerOfIsCosplitPair.out F f g
    apply reflectsLimit_of_reflectsIsomorphisms⟩
  apply comonadicOfHasPreservesReflectsFSplitEqualizers adj

end BeckComonadicity

section CoreflexiveComonadicity

variable [HasCoreflexiveEqualizers C] [F.ReflectsIsomorphisms]

/-- Dual to `Monad.PreservesColimitOfIsReflexivePair`. -/
/-
**CategoryTheory.Comonad.PreservesLimitOfIsCoreflexivePair** 是 Mathlib 中的一个归纳类型，
位于命名空间 `CategoryTheory.Comonad`。
形式化陈述：{C : Type u₁} →   {D : Type u₂} →     [inst : CategoryTheory.Category.{v₁,
 u₁} C] →       [inst_1 : CategoryTheory.Category.{v₁, u₂} D] → CategoryTheory.F
unctor C D → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Dual to `Monad.PreservesColimitOfIsReflexivePair`.
-/
class PreservesLimitOfIsCoreflexivePair (F : C ⥤ D) where
  /-- `f, g` is a coreflexive pair, then `F` preserves limits of `parallelPair f g`. -/
  out : ∀ ⦃A B⦄ (f g : A ⟶ B) [IsCoreflexivePair f g], PreservesLimit (parallelPair f g) F
/-
**CategoryTheory.Comonad.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Comonad`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {A B} (f g : A ⟶ B) [IsCoreflexivePair f g] [PreservesLimitOfIsCoreflexivePair F] :
    PreservesLimit (parallelPair f g) F := PreservesLimitOfIsCoreflexivePair.out f g
/-
**CategoryTheory.Comonad.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Comonad`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [PreservesLimitOfIsCoreflexivePair F] : ∀ X : Coalgebra adj.toComonad,
    PreservesLimit (parallelPair (G.map X.a)
      (NatTrans.app adj.unit (G.obj X.A))) F :=
  fun _ => PreservesLimitOfIsCoreflexivePair.out _ _

variable [PreservesLimitOfIsCoreflexivePair F]

set_option backward.isDefEq.respectTransparency.types false in
/-- Coreflexive (crude) comonadicity theorem. If `F` has a right adjoint, `C` has and `F` preserves
coreflexive equalizers and `F` reflects isomorphisms, then `F` is comonadic.
-/
@[instance_reducible]
/-
**CategoryTheory.Comonad.comonadicOfHasPreservesCoreflexiveEqualizersOfReflectsI
somorphisms** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Comonad`。
形式化陈述：comonadicOfHasPreservesCoreflexiveEqualizersOfReflectsIsomorphisms : Comon
adicLeftAdjoint F where R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Coreflexive (crude) comonadicity theorem. If `F` has a right adjoint, `C` has an
d `F` preserves
coreflexive equalizers and `F` reflects isomorphisms, then `F` is comonadic.
-/
def comonadicOfHasPreservesCoreflexiveEqualizersOfReflectsIsomorphisms :
    ComonadicLeftAdjoint F where
  R := G
  adj := adj
  eqv := by
    have : ∀ (X : adj.toComonad.Coalgebra), IsIso ((comparisonAdjunction adj).counit.app X) := by
      intro X
      apply
        @isIso_of_reflects_iso _ _ _ _ _ _ _ (Comonad.forget adj.toComonad) ?_ _
      · change IsIso ((comparisonAdjunction adj).counit.app X).f
        rw [comparisonAdjunction_counit_f]
        exact (IsLimit.conePointUniqueUpToIso (beckEqualizer X)
          (counitLimitOfPreservesEqualizer X)).isIso_inv
    have : ∀ (Y : C), IsIso ((comparisonAdjunction adj).unit.app Y) := by
      intro Y
      rw [comparisonAdjunction_unit_app]
      change IsIso (IsLimit.conePointUniqueUpToIso _ ?_).inv
      · infer_instance
      have : IsCoreflexivePair (G.map (F.map (adj.unit.app Y)))
          (adj.unit.app (G.obj (F.obj Y))) := by
        apply IsCoreflexivePair.mk' (G.map (adj.counit.app _)) _ _
        · rw [← G.map_comp, ← G.map_id]
          exact congr_arg G.map (adj.left_triangle_components Y)
        · rw [← G.map_id]
          simp
      apply @unitEqualizerOfCoreflectsEqualizer _ _ _ _ _ _ _ _ ?_
      apply reflectsLimit_of_reflectsIsomorphisms
    exact (comparisonAdjunction adj).toEquivalence.symm.isEquivalence_inverse

end CoreflexiveComonadicity

end

end Comonad

end CategoryTheory

