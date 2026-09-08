/-
Copyright (c) 2022 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic

/-!
# Transport rigid structures over a monoidal equivalence.
-/

@[expose] public section


namespace CategoryTheory

open MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
  (F : C ⥤ D) [F.Monoidal]

/-- Given candidate data for an exact pairing,
which is sent by a faithful monoidal functor to an exact pairing,
the equations holds automatically. -/
@[instance_reducible]
/-
**CategoryTheory.ExactPairing.ofFaithful** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.ExactPairing`。
形式化陈述：{C : Type u_1} →   {D : Type u_2} →     [inst : CategoryTheory.Category.{v
_1, u_1} C] →       [inst_1 : CategoryTheory.Category.{v_2, u_2} D] →         [i
nst_2 : CategoryTheory.MonoidalCategory C] →           [inst_3 : CategoryTheory.
MonoidalCategory D] →             (F : CategoryTheory.Functor C D) →            
   [inst_4 : F.Monoidal] →                 [F.Faithful] →                   {X Y
 : C} →                     (eval :                         CategoryTheory.Monoi
dalCategoryStruct.tensorObj Y X ⟶                           CategoryTheory.Monoi
dalCategoryStruct.tensorUnit C) →                       (coeval :               
            CategoryTheory.MonoidalCategoryStruct.tensorUnit C ⟶                
             CategoryTheory.MonoidalCategoryStruct.tensorObj X Y) →             
            [inst_6 : CategoryTheory.ExactPairing (F.obj X) (F.obj Y)] →        
                   F.map eval =                               CategoryTheory.Cat
egoryStruct.comp (CategoryTheory.Functor.OplaxMonoidal.δ F Y X)                 
                (CategoryTheory.CategoryStruct.comp (ε_ (F.obj X) (F.obj Y))    
                               (CategoryTheory.Functor.LaxMonoidal.ε F)) →      
                       F.map coeval =                                 CategoryTh
eory.CategoryStruct.comp (CategoryTheory.Functor.OplaxMonoidal.η F)             
                      (CategoryTheory.CategoryStruct.comp (η_ (F.obj X) (F.obj Y
))                                     (CategoryTheory.Functor.LaxMonoidal.μ F X
 Y)) →                               CategoryTheory.ExactPairing X Y
参数：F : CategoryTheory.Functor C D；eval :                         CategoryTheory.
MonoidalCategoryStruct.tensorObj Y X ⟶                           CategoryTheory.
MonoidalCategoryStruct.tensorUnit C；coeval :                           CategoryT
heory.MonoidalCategoryStruct.tensorUnit C ⟶                             Category
Theory.MonoidalCategoryStruct.tensorObj X Y；F.obj X；F.obj Y；CategoryTheory.Funct
or.OplaxMonoidal.δ F Y X；CategoryTheory.CategoryStruct.comp (ε_ (F.obj X) (F.obj
 Y))                                   (CategoryTheory.Functor.LaxMonoidal.ε F)；
CategoryTheory.Functor.OplaxMonoidal.η F；CategoryTheory.CategoryStruct.comp (η_ 
(F.obj X) (F.obj Y))                                     (CategoryTheory.Functor
.LaxMonoidal.μ F X Y)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given candidate data for an exact pairing,
which is sent by a faithful monoidal functor to an exact pairing,
the equations holds automatically.
-/
def ExactPairing.ofFaithful [F.Faithful] {X Y : C} (eval : Y ⊗ X ⟶ 𝟙_ C)
    (coeval : 𝟙_ C ⟶ X ⊗ Y) [ExactPairing (F.obj X) (F.obj Y)]
    (map_eval : F.map eval = (δ F _ _) ≫ ε_ _ _ ≫ ε F)
    (map_coeval : F.map coeval = (η F) ≫ η_ _ _ ≫ μ F _ _) : ExactPairing X Y where
  evaluation' := eval
  coevaluation' := coeval
  evaluation_coevaluation' :=
    F.map_injective <| by
      simp [map_eval, map_coeval, Functor.Monoidal.map_whiskerLeft,
        Functor.Monoidal.map_whiskerRight]
  coevaluation_evaluation' :=
    F.map_injective <| by
      simp [map_eval, map_coeval, Functor.Monoidal.map_whiskerLeft,
        Functor.Monoidal.map_whiskerRight]

/-- Given a pair of objects which are sent by a fully faithful functor to a pair of objects
with an exact pairing, we get an exact pairing.
-/
@[instance_reducible]
/-
**CategoryTheory.ExactPairing.ofFullyFaithful** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.ExactPairing`。
形式化陈述：{C : Type u_1} →   {D : Type u_2} →     [inst : CategoryTheory.Category.{v
_1, u_1} C] →       [inst_1 : CategoryTheory.Category.{v_2, u_2} D] →         [i
nst_2 : CategoryTheory.MonoidalCategory C] →           [inst_3 : CategoryTheory.
MonoidalCategory D] →             (F : CategoryTheory.Functor C D) →            
   [F.Monoidal] →                 [F.Full] →                   [F.Faithful] →   
                  (X Y : C) → [CategoryTheory.ExactPairing (F.obj X) (F.obj Y)] 
→ CategoryTheory.ExactPairing X Y
参数：F : CategoryTheory.Functor C D；X Y : C；F.obj X；F.obj Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a pair of objects which are sent by a fully faithful functor to a pair of 
objects
with an exact pairing, we get an exact pairing.
-/
noncomputable def ExactPairing.ofFullyFaithful [F.Full] [F.Faithful] (X Y : C)
    [ExactPairing (F.obj X) (F.obj Y)] : ExactPairing X Y :=
  .ofFaithful F (F.preimage (δ F _ _ ≫ ε_ _ _ ≫ (ε F)))
    (F.preimage (η F ≫ η_ _ _ ≫ μ F _ _)) (by simp) (by simp)

variable {F}
variable {G : D ⥤ C} (adj : F ⊣ G) [F.IsEquivalence]

noncomputable section

/-- Pull back a left dual along an equivalence. -/
@[instance_reducible]
/-
**CategoryTheory.hasLeftDualOfEquivalence** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory`。
形式化陈述：hasLeftDualOfEquivalence (X : C) [HasLeftDual (F.obj X)] : HasLeftDual X w
here leftDual
参数：X : C；F.obj X。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsEquivalence.full`：∀ {C : Type u₁} {inst : Categ
oryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Category.{
v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.IsEquivalence.faithful`：∀ {C : Type u₁} {inst : C
ategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Catego
ry.{v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
Pull back a left dual along an equivalence.
-/
def hasLeftDualOfEquivalence (X : C) [HasLeftDual (F.obj X)] :
    HasLeftDual X where
  leftDual := G.obj (ᘁ(F.obj X))
  exact := by
    letI := exactPairingCongrLeft (X := F.obj (G.obj ᘁ(F.obj X)))
      (X' := ᘁ(F.obj X)) (Y := F.obj X) (adj.toEquivalence.counitIso.app ᘁ(F.obj X))
    apply ExactPairing.ofFullyFaithful F

/-- Pull back a right dual along an equivalence. -/
@[instance_reducible]
/-
**CategoryTheory.hasRightDualOfEquivalence** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory`。
形式化陈述：hasRightDualOfEquivalence (X : C) [HasRightDual (F.obj X)] : HasRightDual 
X where rightDual
参数：X : C；F.obj X。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsEquivalence.full`：∀ {C : Type u₁} {inst : Categ
oryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Category.{
v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.IsEquivalence.faithful`：∀ {C : Type u₁} {inst : C
ategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Catego
ry.{v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
Pull back a right dual along an equivalence.
-/
def hasRightDualOfEquivalence (X : C) [HasRightDual (F.obj X)] :
    HasRightDual X where
  rightDual := G.obj ((F.obj X)ᘁ)
  exact := by
    letI := exactPairingCongrRight (X := F.obj X) (Y := F.obj (G.obj (F.obj X)ᘁ))
      (Y' := (F.obj X)ᘁ) (adj.toEquivalence.counitIso.app (F.obj X)ᘁ)
    apply ExactPairing.ofFullyFaithful F

/-- Pull back a left rigid structure along an equivalence. -/
@[instance_reducible]
/-
**CategoryTheory.leftRigidCategoryOfEquivalence** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory`。
形式化陈述：leftRigidCategoryOfEquivalence [LeftRigidCategory D] : LeftRigidCategory C
 where leftDual X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Pull back a left rigid structure along an equivalence.
-/
def leftRigidCategoryOfEquivalence [LeftRigidCategory D] :
    LeftRigidCategory C where leftDual X := hasLeftDualOfEquivalence adj X

/-- Pull back a right rigid structure along an equivalence. -/
@[instance_reducible]
/-
**CategoryTheory.rightRigidCategoryOfEquivalence** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory`。
形式化陈述：rightRigidCategoryOfEquivalence [RightRigidCategory D] : RightRigidCategor
y C where rightDual X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Pull back a right rigid structure along an equivalence.
-/
def rightRigidCategoryOfEquivalence [RightRigidCategory D] :
    RightRigidCategory C where rightDual X := hasRightDualOfEquivalence adj X

/-- Pull back a rigid structure along an equivalence. -/
@[instance_reducible]
/-
**CategoryTheory.rigidCategoryOfEquivalence** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory`。
形式化陈述：rigidCategoryOfEquivalence [RigidCategory D] : RigidCategory C where leftD
ual X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Pull back a rigid structure along an equivalence.
-/
def rigidCategoryOfEquivalence [RigidCategory D] : RigidCategory C where
  leftDual X := hasLeftDualOfEquivalence adj X
  rightDual X := hasRightDualOfEquivalence adj X

end

end CategoryTheory

