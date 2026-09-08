/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Shapes.Reflexive
public import Mathlib.CategoryTheory.Monad.Coequalizer
public import Mathlib.CategoryTheory.Monad.Limits

/-!
# Monadicity theorems

We prove monadicity theorems which can establish a given functor is monadic. In particular, we
show three versions of Beck's monadicity theorem, and the reflexive (crude) monadicity theorem:

`G` is a monadic right adjoint if it has a left adjoint, and:

* `D` has, `G` preserves and reflects `G`-split coequalizers, see
  `CategoryTheory.Monad.monadicOfHasPreservesReflectsGSplitCoequalizers`
* `G` creates `G`-split coequalizers, see
  `CategoryTheory.Monad.monadicOfCreatesGSplitCoequalizers`
  (The converse of this is also shown, see
  `CategoryTheory.Monad.createsGSplitCoequalizersOfMonadic`)
* `D` has and `G` preserves `G`-split coequalizers, and `G` reflects isomorphisms, see
  `CategoryTheory.Monad.monadicOfHasPreservesGSplitCoequalizersOfReflectsIsomorphisms`
* `D` has and `G` preserves reflexive coequalizers, and `G` reflects isomorphisms, see
  `CategoryTheory.Monad.monadicOfHasPreservesReflexiveCoequalizersOfReflectsIsomorphisms`

This file has been adapted to `Mathlib/CategoryTheory/Monad/Comonadicity.lean`.
Please try to keep them in sync.

## Tags

Beck, monadicity, descent

-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

namespace Monad

open Limits

noncomputable section

-- Hide the implementation details in this namespace.
namespace MonadicityInternal

variable {C : Type u₁} {D : Type u₂}
variable [Category.{v₁} C] [Category.{v₁} D]
variable {G : D ⥤ C} {F : C ⥤ D} (adj : F ⊣ G)

set_option backward.isDefEq.respectTransparency false in
/-- The "main pair" for an algebra `(A, α)` is the pair of morphisms `(F α, ε_FA)`. It is always a
reflexive pair, and will be used to construct the left adjoint to the comparison functor and show it
is an equivalence.
-/
/-
**CategoryTheory.Monad.MonadicityInternal.main_pair_reflexive** 是 Mathlib 中的一个实例
，位于命名空间 `CategoryTheory.Monad.MonadicityInternal`。
形式化陈述：main_pair_reflexive (A : adj.toMonad.Algebra) : IsReflexivePair (F.map A.a
) (adj.counit.app (F.obj A.A))
参数：A : adj.toMonad.Algebra。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsReflexivePair.mk'`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {A B : C} {f g : A ⟶ B} (s : B ⟶ A),   CategoryTheory.Categ
oryStruct.comp s f = Cat…
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
· 使用定理 `CategoryTheory.Monad.Algebra.unit`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {T : CategoryTheory.Monad C} (self : T.Algebra),   Catego
ryTheory.CategoryStruct…
· 使用定理 `CategoryTheory.Adjunction.left_triangle_components`：∀ {C : Type u₁} [ins
t : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.C
ategory.{v₂, u₂} D]   {F : CategoryTheor…

--- 原说明 ---
The "main pair" for an algebra `(A, α)` is the pair of morphisms `(F α, ε_FA)`. 
It is always a
reflexive pair, and will be used to construct the left adjoint to the comparison
 functor and show it
is an equivalence.
-/
instance main_pair_reflexive (A : adj.toMonad.Algebra) :
    IsReflexivePair (F.map A.a) (adj.counit.app (F.obj A.A)) := by
  apply IsReflexivePair.mk' (F.map (adj.unit.app _)) _ _
  · rw [← F.map_comp, ← F.map_id]
    exact congr_arg F.map A.unit
  · dsimp
    rw [adj.left_triangle_components]

/-- The "main pair" for an algebra `(A, α)` is the pair of morphisms `(F α, ε_FA)`. It is always a
`G`-split pair, and will be used to construct the left adjoint to the comparison functor and show it
is an equivalence.
-/
/-
**CategoryTheory.Monad.MonadicityInternal.main_pair_G_split** 是 Mathlib 中的一个实例，位
于命名空间 `CategoryTheory.Monad.MonadicityInternal`。
形式化陈述：main_pair_G_split (A : adj.toMonad.Algebra) : G.IsSplitPair (F.map A.a) (a
dj.counit.app (F.obj A.A)) where splittable
参数：A : adj.toMonad.Algebra。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The "main pair" for an algebra `(A, α)` is the pair of morphisms `(F α, ε_FA)`. 
It is always a
`G`-split pair, and will be used to construct the left adjoint to the comparison
 functor and show it
is an equivalence.
-/
instance main_pair_G_split (A : adj.toMonad.Algebra) :
    G.IsSplitPair (F.map A.a)
      (adj.counit.app (F.obj A.A)) where
  splittable := ⟨_, _, ⟨beckSplitCoequalizer A⟩⟩

/-- The object function for the left adjoint to the comparison functor. -/
/-
**CategoryTheory.Monad.MonadicityInternal.comparisonLeftAdjointObj** 是 Mathlib 中
的一个定义，位于命名空间 `CategoryTheory.Monad.MonadicityInternal`。
形式化陈述：comparisonLeftAdjointObj (A : adj.toMonad.Algebra) [HasCoequalizer (F.map 
A.a) (adj.counit.app _)] : D
参数：A : adj.toMonad.Algebra；F.map A.a；adj.counit.app _。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The object function for the left adjoint to the comparison functor.
-/
def comparisonLeftAdjointObj (A : adj.toMonad.Algebra)
    [HasCoequalizer (F.map A.a) (adj.counit.app _)] : D :=
  coequalizer (F.map A.a) (adj.counit.app _)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
We have a bijection of homsets which will be used to construct the left adjoint to the comparison
functor.
-/
@[simps!]
/-
**CategoryTheory.Monad.MonadicityInternal.comparisonLeftAdjointHomEquiv** 是 Math
lib 中的一个定义，位于命名空间 `CategoryTheory.Monad.MonadicityInternal`。
形式化陈述：comparisonLeftAdjointHomEquiv (A : adj.toMonad.Algebra) (B : D) [HasCoequa
lizer (F.map A.a) (adj.counit.app (F.obj A.A))] : (comparisonLeftAdjointObj adj 
A ⟶ B) ≃ (A ⟶ (comparison adj).obj B)
参数：A : adj.toMonad.Algebra；B : D；F.map A.a；adj.counit.app (F.obj A.A)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We have a bijection of homsets which will be used to construct the left adjoint 
to the comparison
functor.
-/
def comparisonLeftAdjointHomEquiv (A : adj.toMonad.Algebra) (B : D)
    [HasCoequalizer (F.map A.a) (adj.counit.app (F.obj A.A))] :
    (comparisonLeftAdjointObj adj A ⟶ B) ≃ (A ⟶ (comparison adj).obj B) :=
  calc
    (comparisonLeftAdjointObj adj A ⟶ B) ≃ { f : F.obj A.A ⟶ B // _ } :=
      Cofork.IsColimit.homIso (colimit.isColimit _) B
    _ ≃ { g : A.A ⟶ G.obj B // G.map (F.map g) ≫ G.map (adj.counit.app B) = A.a ≫ g } := by
      refine (adj.homEquiv _ _).subtypeEquiv ?_
      intro f
      rw [← (adj.homEquiv _ _).injective.eq_iff, Adjunction.homEquiv_naturality_left,
        adj.homEquiv_unit, adj.homEquiv_unit, G.map_comp]
      dsimp
      rw [adj.right_triangle_components_assoc, ← G.map_comp, F.map_comp, Category.assoc,
        adj.counit_naturality, adj.left_triangle_components_assoc]
      apply eq_comm
    _ ≃ (A ⟶ (comparison adj).obj B) :=
      { toFun := fun g =>
          { f := _
            h := g.prop }
        invFun := fun f => ⟨f.f, f.h⟩ }

set_option backward.isDefEq.respectTransparency false in
/-- Construct the adjunction to the comparison functor.
-/
/-
**CategoryTheory.Monad.MonadicityInternal.leftAdjointComparison** 是 Mathlib 中的一个
定义，位于命名空间 `CategoryTheory.Monad.MonadicityInternal`。
形式化陈述：leftAdjointComparison [forall A : adj.toMonad.Algebra, HasCoequalizer (F.m
ap A.a) (adj.counit.app (F.obj A.A))] : adj.toMonad.Algebra ⥤ D
参数：F.map A.a；adj.counit.app (F.obj A.A)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct the adjunction to the comparison functor.
-/
def leftAdjointComparison
    [∀ A : adj.toMonad.Algebra, HasCoequalizer (F.map A.a)
      (adj.counit.app (F.obj A.A))] :
    adj.toMonad.Algebra ⥤ D := by
  refine
    Adjunction.leftAdjointOfEquiv (G := comparison adj)
      (F_obj := fun A => comparisonLeftAdjointObj adj A) (fun A B => ?_) ?_
  · apply comparisonLeftAdjointHomEquiv
  · intro A B B' g h
    ext1
    simp [Cofork.IsColimit.homIso, Adjunction.homEquiv_unit]

/-- Provided we have the appropriate coequalizers, we have an adjunction to the comparison functor.
-/
@[simps! counit]
/-
**CategoryTheory.Monad.MonadicityInternal.comparisonAdjunction** 是 Mathlib 中的一个定
义，位于命名空间 `CategoryTheory.Monad.MonadicityInternal`。
形式化陈述：comparisonAdjunction [forall A : adj.toMonad.Algebra, HasCoequalizer (F.ma
p A.a) (adj.counit.app (F.obj A.A))] : leftAdjointComparison adj ⊣ comparison ad
j
参数：F.map A.a；adj.counit.app (F.obj A.A)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Provided we have the appropriate coequalizers, we have an adjunction to the comp
arison functor.
-/
def comparisonAdjunction
    [∀ A : adj.toMonad.Algebra, HasCoequalizer (F.map A.a)
      (adj.counit.app (F.obj A.A))] :
    leftAdjointComparison adj ⊣ comparison adj :=
  Adjunction.adjunctionOfEquivLeft _ _

variable {adj}
/-
**CategoryTheory.Monad.MonadicityInternal.comparisonAdjunction_unit_f_aux** 是 Ma
thlib 中的一个定理，位于命名空间 `CategoryTheory.Monad.MonadicityInternal`。
形式化陈述：comparisonAdjunction_unit_f_aux [forall A : adj.toMonad.Algebra, HasCoequa
lizer (F.map A.a) (adj.counit.app (F.obj A.A))] (A : adj.toMonad.Algebra) : ((co
mparisonAdjunction adj).unit.app A).f = adj.homEquiv A.A _ (coequalizer.π (F.map
 A.a) (adj.counit.app (F.obj A.A)))
参数：F.map A.a；adj.counit.app (F.obj A.A)；A : adj.toMonad.Algebra。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
theorem comparisonAdjunction_unit_f_aux
    [∀ A : adj.toMonad.Algebra, HasCoequalizer (F.map A.a)
      (adj.counit.app (F.obj A.A))]
    (A : adj.toMonad.Algebra) :
    ((comparisonAdjunction adj).unit.app A).f =
      adj.homEquiv A.A _
        (coequalizer.π (F.map A.a) (adj.counit.app (F.obj A.A))) :=
  congr_arg (adj.homEquiv _ _) (Category.comp_id _)

set_option backward.isDefEq.respectTransparency.types false in
/-- This is a cofork which is helpful for establishing monadicity: the morphism from the Beck
coequalizer to this cofork is the unit for the adjunction on the comparison functor.
-/
@[simps! pt]
/-
**CategoryTheory.Monad.MonadicityInternal.unitCofork** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Monad.MonadicityInternal`。
形式化陈述：unitCofork (A : adj.toMonad.Algebra) [HasCoequalizer (F.map A.a) (adj.coun
it.app (F.obj A.A))] : Cofork (G.map (F.map A.a)) (G.map (adj.counit.app (F.obj 
A.A)))
参数：A : adj.toMonad.Algebra；F.map A.a；adj.counit.app (F.obj A.A)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is a cofork which is helpful for establishing monadicity: the morphism from
 the Beck
coequalizer to this cofork is the unit for the adjunction on the comparison func
tor.
-/
def unitCofork (A : adj.toMonad.Algebra)
    [HasCoequalizer (F.map A.a) (adj.counit.app (F.obj A.A))] :
    Cofork (G.map (F.map A.a)) (G.map (adj.counit.app (F.obj A.A))) :=
  Cofork.ofπ (G.map (coequalizer.π (F.map A.a) (adj.counit.app (F.obj A.A))))
    (by rw [← G.map_comp, coequalizer.condition, G.map_comp])

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**CategoryTheory.Monad.MonadicityInternal.unitCofork_** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.Monad.MonadicityInternal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem unitCofork_π (A : adj.toMonad.Algebra)
    [HasCoequalizer (F.map A.a) (adj.counit.app (F.obj A.A))] :
    (unitCofork A).π = G.map (coequalizer.π (F.map A.a) (adj.counit.app (F.obj A.A))) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Monad.MonadicityInternal.comparisonAdjunction_unit_f** 是 Mathli
b 中的一个定理，位于命名空间 `CategoryTheory.Monad.MonadicityInternal`。
形式化陈述：comparisonAdjunction_unit_f [forall A : adj.toMonad.Algebra, HasCoequalize
r (F.map A.a) (adj.counit.app (F.obj A.A))] (A : adj.toMonad.Algebra) : ((compar
isonAdjunction adj).unit.app A).f = (beckCoequalizer A).desc (unitCofork A)
参数：F.map A.a；adj.counit.app (F.obj A.A)；A : adj.toMonad.Algebra。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Cofork.IsColimit.hom_ext`：∀ {C : Type u} {X Y : C}
 [inst : CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y} {s : CategoryTheory.Lim
its.Cofork f g}   (hs : CategoryTheo…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.Cofork.IsColimit.π_desc`：∀ {C : Type u} {X Y : C} 
[inst : CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   {s t : CategoryTheory.
Limits.Cofork f g} (hs : CategoryTh…
· 使用定理 `CategoryTheory.Monad.MonadicityInternal.comparisonAdjunction_unit_f_aux`
：comparisonAdjunction_unit_f_aux [forall A : adj.toMonad.Algebra, HasCoequalizer
 (F.map A.a) (adj.counit.app (F.obj A.A))] (A : adj.toMonad.A…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Adjunction.homEquiv_naturality_left`：homEquiv_naturality_
left (f : X' ⟶ X) (g : F.obj X ⟶ Y) : (adj.homEquiv X' Y) (F.map f ≫ g) = f ≫ (a
dj.homEquiv X Y) g
· 使用定理 `CategoryTheory.Limits.coequalizer.condition`：∀ {C : Type u} {X Y : C} [i
nst : CategoryTheory.Category.{v, u} C] (f g : X ⟶ Y)   [inst_1 : CategoryTheory
.Limits.HasCoequalizer f g],   Ca…
· 使用定理 `CategoryTheory.Adjunction.homEquiv_naturality_right`：homEquiv_naturality
_right (f : F.obj X ⟶ Y) (g : Y ⟶ Y') : (adj.homEquiv X Y') (f ≫ g) = (adj.homEq
uiv X Y) f ≫ G.map g
· 使用定理 `CategoryTheory.Adjunction.homEquiv_unit`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Adjunction.right_triangle_components_assoc`：∀ {C : Type u
₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryT
heory.Category.{v₂, u₂} D]   {F : CategoryTheor…
-/
theorem comparisonAdjunction_unit_f
    [∀ A : adj.toMonad.Algebra, HasCoequalizer (F.map A.a)
      (adj.counit.app (F.obj A.A))]
    (A : adj.toMonad.Algebra) :
    ((comparisonAdjunction adj).unit.app A).f = (beckCoequalizer A).desc (unitCofork A) := by
  apply Limits.Cofork.IsColimit.hom_ext (beckCoequalizer A)
  rw [Cofork.IsColimit.π_desc]
  dsimp only [beckCofork_π, unitCofork_π]
  rw [comparisonAdjunction_unit_f_aux, ← adj.homEquiv_naturality_left A.a, coequalizer.condition,
    adj.homEquiv_naturality_right, adj.homEquiv_unit, Category.assoc]
  apply adj.right_triangle_components_assoc

variable (adj)

/-- The cofork which describes the counit of the adjunction: the morphism from the coequalizer of
this pair to this morphism is the counit.
-/
@[simps!]
/-
**CategoryTheory.Monad.MonadicityInternal.counitCofork** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.Monad.MonadicityInternal`。
形式化陈述：counitCofork (B : D) : Cofork (F.map (G.map (adj.counit.app B))) (adj.coun
it.app (F.obj (G.obj B)))
参数：B : D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cofork which describes the counit of the adjunction: the morphism from the c
oequalizer of
this pair to this morphism is the counit.
-/
def counitCofork (B : D) :
    Cofork (F.map (G.map (adj.counit.app B)))
      (adj.counit.app (F.obj (G.obj B))) :=
  Cofork.ofπ (adj.counit.app B) (adj.counit_naturality _)

set_option backward.isDefEq.respectTransparency.types false in
variable {adj} in
/-- The unit cofork is a colimit provided `G` preserves it. -/
/-
**CategoryTheory.Monad.MonadicityInternal.unitColimitOfPreservesCoequalizer** 是 
Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Monad.MonadicityInternal`。
形式化陈述：unitColimitOfPreservesCoequalizer (A : adj.toMonad.Algebra) [HasCoequalize
r (F.map A.a) (adj.counit.app (F.obj A.A))] [PreservesColimit (parallelPair (F.m
ap A.a) (adj.counit.app (F.obj A.A))) G] : IsColimit (unitCofork (G
参数：A : adj.toMonad.Algebra；F.map A.a；adj.counit.app (F.obj A.A)；parallelPair (F.
map A.a) (adj.counit.app (F.obj A.A))。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The unit cofork is a colimit provided `G` preserves it.
-/
def unitColimitOfPreservesCoequalizer (A : adj.toMonad.Algebra)
    [HasCoequalizer (F.map A.a) (adj.counit.app (F.obj A.A))]
    [PreservesColimit (parallelPair (F.map A.a) (adj.counit.app (F.obj A.A))) G] :
    IsColimit (unitCofork (G := G) A) :=
  isColimitOfHasCoequalizerOfPreservesColimit G _ _

/-- The counit cofork is a colimit provided `G` reflects it. -/
/-
**CategoryTheory.Monad.MonadicityInternal.counitCoequalizerOfReflectsCoequalizer
** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Monad.MonadicityInternal`。
形式化陈述：counitCoequalizerOfReflectsCoequalizer (B : D) [ReflectsColimit (parallelP
air (F.map (G.map (adj.counit.app B))) (adj.counit.app (F.obj (G.obj B)))) G] : 
IsColimit (counitCofork (adj
参数：B : D；parallelPair (F.map (G.map (adj.counit.app B))) (adj.counit.app (F.obj 
(G.obj B)))。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The counit cofork is a colimit provided `G` reflects it.
-/
def counitCoequalizerOfReflectsCoequalizer (B : D)
    [ReflectsColimit (parallelPair (F.map (G.map (adj.counit.app B)))
      (adj.counit.app (F.obj (G.obj B)))) G] :
    IsColimit (counitCofork (adj := adj) B) :=
  isColimitOfIsColimitCoforkMap G _ (beckCoequalizer ((comparison adj).obj B))
/-
**CategoryTheory.Monad.MonadicityInternal.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTh
eory.Monad.MonadicityInternal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance
    [∀ A : adj.toMonad.Algebra, HasCoequalizer (F.map A.a) (adj.counit.app (F.obj A.A))]
    (B : D) : HasColimit (parallelPair
      (F.map (G.map (NatTrans.app adj.counit B)))
      (NatTrans.app adj.counit (F.obj (G.obj B)))) :=
  inferInstanceAs <| HasCoequalizer
    (F.map ((comparison adj).obj B).a)
    (adj.counit.app (F.obj ((comparison adj).obj B).A))

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Monad.MonadicityInternal.comparisonAdjunction_counit_app** 是 Ma
thlib 中的一个定理，位于命名空间 `CategoryTheory.Monad.MonadicityInternal`。
形式化陈述：comparisonAdjunction_counit_app [forall A : adj.toMonad.Algebra, HasCoequa
lizer (F.map A.a) (adj.counit.app (F.obj A.A))] (B : D) : (comparisonAdjunction 
adj).counit.app B = colimit.desc _ (counitCofork adj B)
参数：F.map A.a；adj.counit.app (F.obj A.A)；B : D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.coequalizer.hom_ext`：∀ {C : Type u} {X Y : C} [ins
t : CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   [inst_1 : CategoryTheory.L
imits.HasCoequalizer f g] {W : …
· 使用定理 `CategoryTheory.Monad.MonadicityInternal.instHasColimitWalkingParallelPai
rParallelPairMapAppCounitObjOfHasCoequalizerAA`：∀ {C : Type u₁} {D : Type u₂} [i
nst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Category.{v₁,
 u₂} D]   {G : CategoryTheor…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Adjunction.homEquiv_counit`：∀ {C : Type u₁} [inst : Categ
oryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{
v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Limits.coequalizer.desc.congr_simp`：∀ {C : Type u} {X Y :
 C} [inst : CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   [inst_1 : Category
Theory.Limits.HasCoequalizer f g] {W : …
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem comparisonAdjunction_counit_app
    [∀ A : adj.toMonad.Algebra, HasCoequalizer (F.map A.a) (adj.counit.app (F.obj A.A))] (B : D) :
    (comparisonAdjunction adj).counit.app B = colimit.desc _ (counitCofork adj B) := by
  apply coequalizer.hom_ext
  change
    coequalizer.π _ _ ≫ coequalizer.desc ((adj.homEquiv _ B).symm (𝟙 _)) _ =
      coequalizer.π _ _ ≫ coequalizer.desc _ _
  simp [Adjunction.homEquiv_counit]

end MonadicityInternal

open MonadicityInternal

variable {C : Type u₁} {D : Type u₂}
variable [Category.{v₁} C] [Category.{v₁} D]
variable {G : D ⥤ C} {F : C ⥤ D} (adj : F ⊣ G)

set_option backward.defeqAttrib.useBackward true in
variable (G) in
/--
If `G` is monadic, it creates colimits of `G`-split pairs. This is the "boring" direction of Beck's
monadicity theorem, the converse is given in `monadicOfCreatesGSplitCoequalizers`.
-/
@[instance_reducible]
/-
**CategoryTheory.Monad.createsGSplitCoequalizersOfMonadic** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.Monad`。
形式化陈述：createsGSplitCoequalizersOfMonadic [MonadicRightAdjoint G] ⦃A B⦄ (f g : A 
⟶ B) [G.IsSplitPair f g] : CreatesColimit (parallelPair f g) G
参数：f g : A ⟶ B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `G` is monadic, it creates colimits of `G`-split pairs. This is the "boring" 
direction of Beck's
monadicity theorem, the converse is given in `monadicOfCreatesGSplitCoequalizers
`.
-/
def createsGSplitCoequalizersOfMonadic [MonadicRightAdjoint G] ⦃A B⦄ (f g : A ⟶ B)
    [G.IsSplitPair f g] : CreatesColimit (parallelPair f g) G := by
  apply +allowSynthFailures monadicCreatesColimitOfPreservesColimit
    -- Porting note: oddly +allowSynthFailures had no effect here and below
  all_goals
    apply @preservesColimit_of_iso_diagram _ _ _ _ _ _ _ _ _ (diagramIsoParallelPair.{v₁} _).symm ?_
    dsimp
    infer_instance

section BeckMonadicity

-- Porting note: added these to replace parametric instances https://github.com/leanprover/lean4/issues/2311
-- When this is fixed the proofs below that struggle with instances should be reviewed.
-- [∀ ⦃A B⦄ (f g : A ⟶ B) [G.IsSplitPair f g], HasCoequalizer f g]
/-- Typeclass expressing that for all `G`-split pairs `f,g`, `f` and `g` have a coequalizer. -/
/-
**CategoryTheory.Monad.HasCoequalizerOfIsSplitPair** 是 Mathlib 中的一个类，位于命名空间 `Cat
egoryTheory.Monad`。
形式化陈述：HasCoequalizerOfIsSplitPair (G : D ⥤ C) : Prop where out : forall {A B} (f
 g : A ⟶ B) [G.IsSplitPair f g], HasCoequalizer f g  -- Porting note: cannot fin
d synth order -- instance {A B} (f g : A ⟶ B) [G.IsSplitPair f g] [HasCoequalize
rOfIsSplitPair G] : -- HasCoequalizer f g
参数：G : D ⥤ C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typeclass expressing that for all `G`-split pairs `f,g`, `f` and `g` have a coeq
ualizer.
-/
class HasCoequalizerOfIsSplitPair (G : D ⥤ C) : Prop where
  out : ∀ {A B} (f g : A ⟶ B) [G.IsSplitPair f g], HasCoequalizer f g

-- Porting note: cannot find synth order
-- instance {A B} (f g : A ⟶ B) [G.IsSplitPair f g] [HasCoequalizerOfIsSplitPair G] :
--     HasCoequalizer f g := HasCoequalizerOfIsSplitPair.out f g
/-
**CategoryTheory.Monad.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Monad`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasCoequalizerOfIsSplitPair G] : ∀ (A : Algebra adj.toMonad),
    HasCoequalizer (F.map A.a)
      (adj.counit.app (F.obj A.A)) :=
  fun _ => HasCoequalizerOfIsSplitPair.out G _ _

-- Porting note: added these to replace parametric instances https://github.com/leanprover/lean4/issues/2311
-- [∀ ⦃A B⦄ (f g : A ⟶ B) [G.IsSplitPair f g], PreservesColimit (parallelPair f g) G]
/-- Typeclass expressing that for all `G`-split pairs `f,g`, `G` preserves colimits of
`parallelPair f g`. -/
/-
**CategoryTheory.Monad.PreservesColimitOfIsSplitPair** 是 Mathlib 中的一个归纳类型，位于命名空间
 `CategoryTheory.Monad`。
形式化陈述：{C : Type u₁} →   {D : Type u₂} →     [inst : CategoryTheory.Category.{v₁,
 u₁} C] →       [inst_1 : CategoryTheory.Category.{v₁, u₂} D] → CategoryTheory.F
unctor D C → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typeclass expressing that for all `G`-split pairs `f,g`, `G` preserves colimits 
of
`parallelPair f g`.
-/
class PreservesColimitOfIsSplitPair (G : D ⥤ C) where
  out : ∀ {A B} (f g : A ⟶ B) [G.IsSplitPair f g], PreservesColimit (parallelPair f g) G
/-
**CategoryTheory.Monad.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Monad`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {A B} (f g : A ⟶ B) [G.IsSplitPair f g] [PreservesColimitOfIsSplitPair G] :
    PreservesColimit (parallelPair f g) G := PreservesColimitOfIsSplitPair.out f g
/-
**CategoryTheory.Monad.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Monad`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [PreservesColimitOfIsSplitPair G] : ∀ (A : Algebra adj.toMonad),
    PreservesColimit (parallelPair (F.map A.a) (NatTrans.app adj.counit (F.obj A.A))) G :=
  fun _ => PreservesColimitOfIsSplitPair.out _ _

-- Porting note: added these to replace parametric instances https://github.com/leanprover/lean4/issues/2311
-- [∀ ⦃A B⦄ (f g : A ⟶ B) [G.IsSplitPair f g], ReflectsColimit (parallelPair f g) G] :
/-- Typeclass expressing that for all `G`-split pairs `f,g`, `G` reflects colimits for
`parallelPair f g`. -/
/-
**CategoryTheory.Monad.ReflectsColimitOfIsSplitPair** 是 Mathlib 中的一个归纳类型，位于命名空间 
`CategoryTheory.Monad`。
形式化陈述：{C : Type u₁} →   {D : Type u₂} →     [inst : CategoryTheory.Category.{v₁,
 u₁} C] →       [inst_1 : CategoryTheory.Category.{v₁, u₂} D] → CategoryTheory.F
unctor D C → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typeclass expressing that for all `G`-split pairs `f,g`, `G` reflects colimits f
or
`parallelPair f g`.
-/
class ReflectsColimitOfIsSplitPair (G : D ⥤ C) where
  out : ∀ {A B} (f g : A ⟶ B) [G.IsSplitPair f g], ReflectsColimit (parallelPair f g) G
/-
**CategoryTheory.Monad.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Monad`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {A B} (f g : A ⟶ B) [G.IsSplitPair f g] [ReflectsColimitOfIsSplitPair G] :
    ReflectsColimit (parallelPair f g) G := ReflectsColimitOfIsSplitPair.out f g
/-
**CategoryTheory.Monad.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Monad`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [ReflectsColimitOfIsSplitPair G] : ∀ (A : Algebra adj.toMonad),
    ReflectsColimit (parallelPair (F.map A.a)
      (NatTrans.app adj.counit (F.obj A.A))) G :=
  fun _ => ReflectsColimitOfIsSplitPair.out _ _

set_option backward.isDefEq.respectTransparency.types false in
/-- To show `G` is a monadic right adjoint, we can show it preserves and reflects `G`-split
coequalizers, and `D` has them.
-/
@[instance_reducible]
/-
**CategoryTheory.Monad.monadicOfHasPreservesReflectsGSplitCoequalizers** 是 Mathl
ib 中的一个定义，位于命名空间 `CategoryTheory.Monad`。
形式化陈述：monadicOfHasPreservesReflectsGSplitCoequalizers [HasCoequalizerOfIsSplitPa
ir G] [PreservesColimitOfIsSplitPair G] [ReflectsColimitOfIsSplitPair G] : Monad
icRightAdjoint G where L
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
To show `G` is a monadic right adjoint, we can show it preserves and reflects `G
`-split
coequalizers, and `D` has them.
-/
def monadicOfHasPreservesReflectsGSplitCoequalizers [HasCoequalizerOfIsSplitPair G]
    [PreservesColimitOfIsSplitPair G] [ReflectsColimitOfIsSplitPair G] :
    MonadicRightAdjoint G where
  L := F
  adj := adj
  eqv := by
    have : ∀ (X : Algebra adj.toMonad), IsIso ((comparisonAdjunction adj).unit.app X) := by
      intro X
      apply @isIso_of_reflects_iso _ _ _ _ _ _ _ (Monad.forget adj.toMonad) ?_ _
      · change IsIso ((comparisonAdjunction adj).unit.app X).f
        rw [comparisonAdjunction_unit_f]
        change
          IsIso
            (IsColimit.coconePointUniqueUpToIso (beckCoequalizer X)
                (unitColimitOfPreservesCoequalizer X)).hom
        exact (IsColimit.coconePointUniqueUpToIso _ _).isIso_hom
    have : ∀ (Y : D), IsIso ((comparisonAdjunction adj).counit.app Y) := by
      intro Y
      rw [comparisonAdjunction_counit_app]
      -- Porting note: passing instances through
      change IsIso (IsColimit.coconePointUniqueUpToIso _ ?_).hom
      · infer_instance
      -- Porting note: passing instances through
      apply @counitCoequalizerOfReflectsCoequalizer _ _ _ _ _ _ _ _ ?_
      let _ :
        G.IsSplitPair (F.map (G.map (adj.counit.app Y)))
          (adj.counit.app (F.obj (G.obj Y))) :=
        MonadicityInternal.main_pair_G_split _ ((comparison adj).obj Y)
      infer_instance
    exact (comparisonAdjunction adj).toEquivalence.isEquivalence_inverse

-- Porting note: added these to replace parametric instances https://github.com/leanprover/lean4/issues/2311
-- [∀ ⦃A B⦄ (f g : A ⟶ B) [G.IsSplitPair f g], CreatesColimit (parallelPair f g) G] :
/-- Typeclass expressing that for all `G`-split pairs `f,g`, `G` creates colimits of
`parallelPair f g`. -/
/-
**CategoryTheory.Monad.CreatesColimitOfIsSplitPair** 是 Mathlib 中的一个归纳类型，位于命名空间 `
CategoryTheory.Monad`。
形式化陈述：{C : Type u₁} →   {D : Type u₂} →     [inst : CategoryTheory.Category.{v₁,
 u₁} C] →       [inst_1 : CategoryTheory.Category.{v₁, u₂} D] → CategoryTheory.F
unctor D C → Type (max (max u₁ u₂) v₁)
参数：max (max u₁ u₂) v₁。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typeclass expressing that for all `G`-split pairs `f,g`, `G` creates colimits of
`parallelPair f g`.
-/
class CreatesColimitOfIsSplitPair (G : D ⥤ C) where
  /-- For all `G`-split pairs `f,g`, `G` creates colimits of `parallelPair f g`. -/
  out : ∀ {A B} (f g : A ⟶ B) [G.IsSplitPair f g], CreatesColimit (parallelPair f g) G
/-
**CategoryTheory.Monad.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Monad`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {A B} (f g : A ⟶ B) [G.IsSplitPair f g] [CreatesColimitOfIsSplitPair G] :
    CreatesColimit (parallelPair f g) G := CreatesColimitOfIsSplitPair.out f g
/-
**CategoryTheory.Monad.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Monad`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CreatesColimitOfIsSplitPair G] : ∀ (A : Algebra adj.toMonad),
    CreatesColimit (parallelPair (F.map A.a)
      (NatTrans.app adj.counit (F.obj A.A))) G :=
  fun _ => CreatesColimitOfIsSplitPair.out _ _

/--
**Beck's monadicity theorem**: if `G` has a left adjoint and creates coequalizers of `G`-split
pairs, then it is monadic.
This is the converse of `createsGSplitCoequalizersOfMonadic`.
-/
@[instance_reducible]
/-
**CategoryTheory.Monad.monadicOfCreatesGSplitCoequalizers** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.Monad`。
形式化陈述：monadicOfCreatesGSplitCoequalizers [CreatesColimitOfIsSplitPair G] : Monad
icRightAdjoint G
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
**Beck's monadicity theorem**: if `G` has a left adjoint and creates coequalizer
s of `G`-split
pairs, then it is monadic.
This is the converse of `createsGSplitCoequalizersOfMonadic`.
-/
def monadicOfCreatesGSplitCoequalizers [CreatesColimitOfIsSplitPair G] :
    MonadicRightAdjoint G := by
  have I {A B} (f g : A ⟶ B) [G.IsSplitPair f g] : HasColimit (parallelPair f g ⋙ G) := by
    rw [hasColimit_iff_of_iso (diagramIsoParallelPair.{v₁} _)]
    exact inferInstanceAs <| HasCoequalizer (G.map f) (G.map g)
  have : HasCoequalizerOfIsSplitPair G := ⟨fun _ _ => hasColimit_of_created (parallelPair _ _) G⟩
  have : PreservesColimitOfIsSplitPair G := ⟨by intros; infer_instance⟩
  have : ReflectsColimitOfIsSplitPair G := ⟨by intros; infer_instance⟩
  exact monadicOfHasPreservesReflectsGSplitCoequalizers adj

/-- An alternate version of **Beck's monadicity theorem**: if `G` reflects isomorphisms, preserves
coequalizers of `G`-split pairs and `C` has coequalizers of `G`-split pairs, then it is monadic.
-/
@[instance_reducible]
/-
**CategoryTheory.Monad.monadicOfHasPreservesGSplitCoequalizersOfReflectsIsomorph
isms** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Monad`。
形式化陈述：monadicOfHasPreservesGSplitCoequalizersOfReflectsIsomorphisms [G.ReflectsI
somorphisms] [HasCoequalizerOfIsSplitPair G] [PreservesColimitOfIsSplitPair G] :
 MonadicRightAdjoint G
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An alternate version of **Beck's monadicity theorem**: if `G` reflects isomorphi
sms, preserves
coequalizers of `G`-split pairs and `C` has coequalizers of `G`-split pairs, the
n it is monadic.
-/
def monadicOfHasPreservesGSplitCoequalizersOfReflectsIsomorphisms [G.ReflectsIsomorphisms]
    [HasCoequalizerOfIsSplitPair G] [PreservesColimitOfIsSplitPair G] :
    MonadicRightAdjoint G := by
  have : ReflectsColimitOfIsSplitPair G := ⟨fun f g _ => by
    have := HasCoequalizerOfIsSplitPair.out G f g
    apply reflectsColimit_of_reflectsIsomorphisms⟩
  apply monadicOfHasPreservesReflectsGSplitCoequalizers adj

end BeckMonadicity

section ReflexiveMonadicity

variable [HasReflexiveCoequalizers D] [G.ReflectsIsomorphisms]

-- Porting note: added these to replace parametric instances https://github.com/leanprover/lean4/issues/2311
-- [∀ ⦃A B⦄ (f g : A ⟶ B) [G.IsReflexivePair f g], PreservesColimit (parallelPair f g) G] :
/-- Typeclass expressing that for all reflexive pairs `f,g`, `G` preserves colimits of
`parallelPair f g`. -/
/-
**CategoryTheory.Monad.PreservesColimitOfIsReflexivePair** 是 Mathlib 中的一个归纳类型，位于
命名空间 `CategoryTheory.Monad`。
形式化陈述：{C : Type u₁} →   {D : Type u₂} →     [inst : CategoryTheory.Category.{v₁,
 u₁} C] →       [inst_1 : CategoryTheory.Category.{v₁, u₂} D] → CategoryTheory.F
unctor C D → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typeclass expressing that for all reflexive pairs `f,g`, `G` preserves colimits 
of
`parallelPair f g`.
-/
class PreservesColimitOfIsReflexivePair (G : C ⥤ D) where
  out : ∀ ⦃A B⦄ (f g : A ⟶ B) [IsReflexivePair f g], PreservesColimit (parallelPair f g) G
/-
**CategoryTheory.Monad.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Monad`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {A B} (f g : A ⟶ B) [IsReflexivePair f g] [PreservesColimitOfIsReflexivePair G] :
    PreservesColimit (parallelPair f g) G := PreservesColimitOfIsReflexivePair.out f g
/-
**CategoryTheory.Monad.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Monad`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [PreservesColimitOfIsReflexivePair G] : ∀ X : Algebra adj.toMonad,
    PreservesColimit (parallelPair (F.map X.a)
      (NatTrans.app adj.counit (F.obj X.A))) G :=
  fun _ => PreservesColimitOfIsReflexivePair.out _ _

variable [PreservesColimitOfIsReflexivePair G]

set_option backward.isDefEq.respectTransparency.types false in
/-- Reflexive (crude) monadicity theorem. If `G` has a right adjoint, `D` has and `G` preserves
reflexive coequalizers and `G` reflects isomorphisms, then `G` is monadic.
-/
@[instance_reducible]
/-
**CategoryTheory.Monad.monadicOfHasPreservesReflexiveCoequalizersOfReflectsIsomo
rphisms** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Monad`。
形式化陈述：monadicOfHasPreservesReflexiveCoequalizersOfReflectsIsomorphisms : Monadic
RightAdjoint G where L
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reflexive (crude) monadicity theorem. If `G` has a right adjoint, `D` has and `G
` preserves
reflexive coequalizers and `G` reflects isomorphisms, then `G` is monadic.
-/
def monadicOfHasPreservesReflexiveCoequalizersOfReflectsIsomorphisms : MonadicRightAdjoint G where
  L := F
  adj := adj
  eqv := by
    have : ∀ (X : Algebra adj.toMonad), IsIso ((comparisonAdjunction adj).unit.app X) := by
      intro X
      apply
        @isIso_of_reflects_iso _ _ _ _ _ _ _ (Monad.forget adj.toMonad) ?_ _
      · change IsIso ((comparisonAdjunction adj).unit.app X).f
        rw [comparisonAdjunction_unit_f]
        exact (IsColimit.coconePointUniqueUpToIso (beckCoequalizer X)
          (unitColimitOfPreservesCoequalizer X)).isIso_hom
    have : ∀ (Y : D), IsIso ((comparisonAdjunction adj).counit.app Y) := by
      intro Y
      rw [comparisonAdjunction_counit_app]
      -- Porting note: passing instances through
      change IsIso (IsColimit.coconePointUniqueUpToIso _ ?_).hom
      · infer_instance
      -- Porting note: passing instances through
      apply @counitCoequalizerOfReflectsCoequalizer _ _ _ _ _ _ _ _ ?_
      apply reflectsColimit_of_reflectsIsomorphisms
    exact (comparisonAdjunction adj).toEquivalence.isEquivalence_inverse

end ReflexiveMonadicity

end

end Monad

end CategoryTheory

