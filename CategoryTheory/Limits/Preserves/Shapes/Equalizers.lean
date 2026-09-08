/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.SplitCoequalizer
public import Mathlib.CategoryTheory.Limits.Shapes.SplitEqualizer
public import Mathlib.CategoryTheory.Limits.Preserves.Basic

/-!
# Preserving (co)equalizers

Constructions to relate the notions of preserving (co)equalizers and reflecting (co)equalizers
to concrete (co)forks.

In particular, we show that `equalizerComparison f g G` is an isomorphism iff `G` preserves
the limit of the parallel pair `f,g`, as well as the dual result.
-/

@[expose] public section


noncomputable section

universe w v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable (G : C ⥤ D)

namespace CategoryTheory.Limits

section Equalizers

variable {X Y Z : C} {f g : X ⟶ Y} {h : Z ⟶ X} (w : h ≫ f = h ≫ g)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The map of a fork is a limit iff the fork consisting of the mapped morphisms is a limit. This
essentially lets us commute `Fork.ofι` with `Functor.mapCone`.
-/
/-
**CategoryTheory.Limits.isLimitMapConeForkEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Limits`。
形式化陈述：isLimitMapConeForkEquiv : IsLimit (G.mapCone (Fork.ofι h w)) ≃ IsLimit (Fo
rk.ofι (G.map h) (by simp only [← G.map_comp, w]) : Fork (G.map f) (G.map g))
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The map of a fork is a limit iff the fork consisting of the mapped morphisms is 
a limit. This
essentially lets us commute `Fork.ofι` with `Functor.mapCone`.
-/
def isLimitMapConeForkEquiv :
    IsLimit (G.mapCone (Fork.ofι h w)) ≃
      IsLimit (Fork.ofι (G.map h) (by simp only [← G.map_comp, w]) : Fork (G.map f) (G.map g)) :=
  (IsLimit.postcomposeHomEquiv (diagramIsoParallelPair _) _).symm.trans
    (IsLimit.equivIsoLimit (Fork.ext (Iso.refl _) (by simp [Fork.ι])))

/-- The property of preserving equalizers expressed in terms of forks. -/
/-
**CategoryTheory.Limits.isLimitForkMapOfIsLimit** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Limits`。
形式化陈述：isLimitForkMapOfIsLimit [PreservesLimit (parallelPair f g) G] (l : IsLimit
 (Fork.ofι h w)) : IsLimit (Fork.ofι (G.map h) (by simp only [← G.map_comp, w]) 
: Fork (G.map f) (G.map g))
参数：parallelPair f g；l : IsLimit (Fork.ofι h w)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The property of preserving equalizers expressed in terms of forks.
-/
def isLimitForkMapOfIsLimit [PreservesLimit (parallelPair f g) G] (l : IsLimit (Fork.ofι h w)) :
    IsLimit (Fork.ofι (G.map h) (by simp only [← G.map_comp, w]) : Fork (G.map f) (G.map g)) :=
  isLimitMapConeForkEquiv G w (isLimitOfPreserves G l)

/-- The property of reflecting equalizers expressed in terms of forks. -/
/-
**CategoryTheory.Limits.isLimitOfIsLimitForkMap** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Limits`。
形式化陈述：isLimitOfIsLimitForkMap [ReflectsLimit (parallelPair f g) G] (l : IsLimit 
(Fork.ofι (G.map h) (by simp only [← G.map_comp, w]) : Fork (G.map f) (G.map g))
) : IsLimit (Fork.ofι h w)
参数：parallelPair f g；l : IsLimit (Fork.ofι (G.map h) (by simp only [← G.map_comp,
 w]) : Fork (G.map f) (G.map g))。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The property of reflecting equalizers expressed in terms of forks.
-/
def isLimitOfIsLimitForkMap [ReflectsLimit (parallelPair f g) G]
    (l : IsLimit (Fork.ofι (G.map h) (by simp only [← G.map_comp, w]) : Fork (G.map f) (G.map g))) :
    IsLimit (Fork.ofι h w) :=
  isLimitOfReflects G ((isLimitMapConeForkEquiv G w).symm l)

variable (f g)
variable [HasEqualizer f g]

/--
If `G` preserves equalizers and `C` has them, then the fork constructed of the mapped morphisms of
a fork is a limit.
-/
/-
**CategoryTheory.Limits.isLimitOfHasEqualizerOfPreservesLimit** 是 Mathlib 中的一个定义
，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：isLimitOfHasEqualizerOfPreservesLimit [PreservesLimit (parallelPair f g) G
] : IsLimit (Fork.ofι (G.map (equalizer.ι f g)) (by simp only [← G.map_comp]; rw
 [equalizer.condition]) : Fork (G.map f) (G.map g))
参数：parallelPair f g。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.equalizer.condition`：∀ {C : Type u} {X Y : C} [ins
t : CategoryTheory.Category.{v, u} C] (f g : X ⟶ Y)   [inst_1 : CategoryTheory.L
imits.HasEqualizer f g],   Cate…

--- 原说明 ---
If `G` preserves equalizers and `C` has them, then the fork constructed of the m
apped morphisms of
a fork is a limit.
-/
def isLimitOfHasEqualizerOfPreservesLimit [PreservesLimit (parallelPair f g) G] :
    IsLimit (Fork.ofι
      (G.map (equalizer.ι f g)) (by simp only [← G.map_comp]; rw [equalizer.condition]) :
      Fork (G.map f) (G.map g)) :=
  isLimitForkMapOfIsLimit G _ (equalizerIsEqualizer f g)

variable [HasEqualizer (G.map f) (G.map g)]

/-- If the equalizer comparison map for `G` at `(f,g)` is an isomorphism, then `G` preserves the
equalizer of `(f,g)`.
-/
/-
**CategoryTheory.Limits.PreservesEqualizer.of_iso_comparison** 是 Mathlib 中的一个定理，
位于命名空间 `CategoryTheory.Limits.PreservesEqualizer`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (G : CategoryTheory.Functor C D)
 {X Y : C} (f g : X ⟶ Y) [inst_2 : CategoryTheory.Limits.HasEqualizer f g]   [in
st_3 : CategoryTheory.Limits.HasEqualizer (G.map f) (G.map g)]   [i : CategoryTh
eory.IsIso (CategoryTheory.Limits.equalizerComparison f g G)],   CategoryTheory.
Limits.PreservesLimit (CategoryTheory.Limits.parallelPair f g) G
参数：G : CategoryTheory.Functor C D；f g : X ⟶ Y；G.map f；G.map g；CategoryTheory.Lim
its.equalizerComparison f g G；CategoryTheory.Limits.parallelPair f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimit_of_preserves_limit_cone`：preservesL
imit_of_preserves_limit_cone {F : C ⥤ D} {t : Cone K} (h : IsLimit t) (hF : IsLi
mit (F.mapCone t)) : PreservesLimit K F where pres…
· 使用定理 `CategoryTheory.Limits.equalizer.condition`：∀ {C : Type u} {X Y : C} [ins
t : CategoryTheory.Category.{v, u} C] (f g : X ⟶ Y)   [inst_1 : CategoryTheory.L
imits.HasEqualizer f g],   Cate…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
If the equalizer comparison map for `G` at `(f,g)` is an isomorphism, then `G` p
reserves the
equalizer of `(f,g)`.
-/
lemma PreservesEqualizer.of_iso_comparison [i : IsIso (equalizerComparison f g G)] :
    PreservesLimit (parallelPair f g) G := by
  apply preservesLimit_of_preserves_limit_cone (equalizerIsEqualizer f g)
  apply (isLimitMapConeForkEquiv _ _).symm _
  exact @IsLimit.ofPointIso _ _ _ _ _ _ _ (limit.isLimit (parallelPair (G.map f) (G.map g))) i

variable [PreservesLimit (parallelPair f g) G]

/--
If `G` preserves the equalizer of `(f,g)`, then the equalizer comparison map for `G` at `(f,g)` is
an isomorphism.
-/
/-
**CategoryTheory.Limits.PreservesEqualizer.iso** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Limits.PreservesEqualizer`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         (G : Cat
egoryTheory.Functor C D) →           {X Y : C} →             (f g : X ⟶ Y) →    
           [inst_2 : CategoryTheory.Limits.HasEqualizer f g] →                 [
inst_3 : CategoryTheory.Limits.HasEqualizer (G.map f) (G.map g)] →              
     [CategoryTheory.Limits.PreservesLimit (CategoryTheory.Limits.parallelPair f
 g) G] →                     G.obj (CategoryTheory.Limits.equalizer f g) ≅ Categ
oryTheory.Limits.equalizer (G.map f) (G.map g)
参数：G : CategoryTheory.Functor C D；f g : X ⟶ Y；G.map f；G.map g；CategoryTheory.Lim
its.parallelPair f g；CategoryTheory.Limits.equalizer f g；G.map f；G.map g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `G` preserves the equalizer of `(f,g)`, then the equalizer comparison map for
 `G` at `(f,g)` is
an isomorphism.
-/
def PreservesEqualizer.iso : G.obj (equalizer f g) ≅ equalizer (G.map f) (G.map g) :=
  IsLimit.conePointUniqueUpToIso (isLimitOfHasEqualizerOfPreservesLimit G f g) (limit.isLimit _)

@[simp]
/-
**CategoryTheory.Limits.PreservesEqualizer.iso_hom** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Limits.PreservesEqualizer`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (G : CategoryTheory.Functor C D)
 {X Y : C} (f g : X ⟶ Y) [inst_2 : CategoryTheory.Limits.HasEqualizer f g]   [in
st_3 : CategoryTheory.Limits.HasEqualizer (G.map f) (G.map g)]   [inst_4 : Categ
oryTheory.Limits.PreservesLimit (CategoryTheory.Limits.parallelPair f g) G],   (
CategoryTheory.Limits.PreservesEqualizer.iso G f g).hom = CategoryTheory.Limits.
equalizerComparison f g G
参数：G : CategoryTheory.Functor C D；f g : X ⟶ Y；G.map f；G.map g；CategoryTheory.Lim
its.parallelPair f g；CategoryTheory.Limits.PreservesEqualizer.iso G f g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem PreservesEqualizer.iso_hom :
    (PreservesEqualizer.iso G f g).hom = equalizerComparison f g G :=
  rfl

@[simp]
/-
**CategoryTheory.Limits.PreservesEqualizer.iso_inv_** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem PreservesEqualizer.iso_inv_ι :
    (PreservesEqualizer.iso G f g).inv ≫ G.map (equalizer.ι f g) =
      equalizer.ι (G.map f) (G.map g) := by
  rw [← Iso.cancel_iso_hom_left (PreservesEqualizer.iso G f g), ← Category.assoc, Iso.hom_inv_id]
  simp
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsIso (equalizerComparison f g G) := by
  rw [← PreservesEqualizer.iso_hom]
  infer_instance

end Equalizers

section Coequalizers

variable {X Y Z : C} {f g : X ⟶ Y} {h : Y ⟶ Z} (w : f ≫ h = g ≫ h)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The map of a cofork is a colimit iff the cofork consisting of the mapped morphisms is a colimit.
This essentially lets us commute `Cofork.ofπ` with `Functor.mapCocone`.
-/
/-
**CategoryTheory.Limits.isColimitMapCoconeCoforkEquiv** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.Limits`。
形式化陈述：isColimitMapCoconeCoforkEquiv : IsColimit (G.mapCocone (Cofork.ofπ h w)) ≃
 IsColimit (Cofork.ofπ (G.map h) (by simp only [← G.map_comp, w]) : Cofork (G.ma
p f) (G.map g))
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The map of a cofork is a colimit iff the cofork consisting of the mapped morphis
ms is a colimit.
This essentially lets us commute `Cofork.ofπ` with `Functor.mapCocone`.
-/
def isColimitMapCoconeCoforkEquiv :
    IsColimit (G.mapCocone (Cofork.ofπ h w)) ≃
      IsColimit
        (Cofork.ofπ (G.map h) (by simp only [← G.map_comp, w]) : Cofork (G.map f) (G.map g)) :=
  (IsColimit.precomposeInvEquiv (diagramIsoParallelPair _) _).symm.trans <|
    IsColimit.equivIsoColimit <|
      Cofork.ext (Iso.refl _) <| by
        dsimp only [Cofork.π, Cofork.ofπ_ι_app]
        dsimp; rw [Category.comp_id, Category.id_comp]

/-- The property of preserving coequalizers expressed in terms of coforks. -/
/-
**CategoryTheory.Limits.isColimitCoforkMapOfIsColimit** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.Limits`。
形式化陈述：isColimitCoforkMapOfIsColimit [PreservesColimit (parallelPair f g) G] (l :
 IsColimit (Cofork.ofπ h w)) : IsColimit (Cofork.ofπ (G.map h) (by simp only [← 
G.map_comp, w]) : Cofork (G.map f) (G.map g))
参数：parallelPair f g；l : IsColimit (Cofork.ofπ h w)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The property of preserving coequalizers expressed in terms of coforks.
-/
def isColimitCoforkMapOfIsColimit [PreservesColimit (parallelPair f g) G]
    (l : IsColimit (Cofork.ofπ h w)) :
    IsColimit
      (Cofork.ofπ (G.map h) (by simp only [← G.map_comp, w]) : Cofork (G.map f) (G.map g)) :=
  isColimitMapCoconeCoforkEquiv G w (isColimitOfPreserves G l)

/-- The property of reflecting coequalizers expressed in terms of coforks. -/
/-
**CategoryTheory.Limits.isColimitOfIsColimitCoforkMap** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.Limits`。
形式化陈述：isColimitOfIsColimitCoforkMap [ReflectsColimit (parallelPair f g) G] (l : 
IsColimit (Cofork.ofπ (G.map h) (by simp only [← G.map_comp, w]) : Cofork (G.map
 f) (G.map g))) : IsColimit (Cofork.ofπ h w)
参数：parallelPair f g；l : IsColimit (Cofork.ofπ (G.map h) (by simp only [← G.map_c
omp, w]) : Cofork (G.map f) (G.map g))。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The property of reflecting coequalizers expressed in terms of coforks.
-/
def isColimitOfIsColimitCoforkMap [ReflectsColimit (parallelPair f g) G]
    (l :
      IsColimit
        (Cofork.ofπ (G.map h) (by simp only [← G.map_comp, w]) : Cofork (G.map f) (G.map g))) :
    IsColimit (Cofork.ofπ h w) :=
  isColimitOfReflects G ((isColimitMapCoconeCoforkEquiv G w).symm l)

variable (f g)
variable [HasCoequalizer f g]

/--
If `G` preserves coequalizers and `C` has them, then the cofork constructed of the mapped morphisms
of a cofork is a colimit.
-/
/-
**CategoryTheory.Limits.isColimitOfHasCoequalizerOfPreservesColimit** 是 Mathlib 
中的一个定义，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：isColimitOfHasCoequalizerOfPreservesColimit [PreservesColimit (parallelPai
r f g) G] : IsColimit (Cofork.ofπ (G.map (coequalizer.π f g)) (by simp only [← G
.map_comp]; rw [coequalizer.condition]) : Cofork (G.map f) (G.map g))
参数：parallelPair f g。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.coequalizer.condition`：∀ {C : Type u} {X Y : C} [i
nst : CategoryTheory.Category.{v, u} C] (f g : X ⟶ Y)   [inst_1 : CategoryTheory
.Limits.HasCoequalizer f g],   Ca…

--- 原说明 ---
If `G` preserves coequalizers and `C` has them, then the cofork constructed of t
he mapped morphisms
of a cofork is a colimit.
-/
def isColimitOfHasCoequalizerOfPreservesColimit [PreservesColimit (parallelPair f g) G] :
    IsColimit (Cofork.ofπ (G.map (coequalizer.π f g)) (by
      simp only [← G.map_comp]; rw [coequalizer.condition]) : Cofork (G.map f) (G.map g)) :=
  isColimitCoforkMapOfIsColimit G _ (coequalizerIsCoequalizer f g)

variable [HasCoequalizer (G.map f) (G.map g)]

/-- If the coequalizer comparison map for `G` at `(f,g)` is an isomorphism, then `G` preserves the
coequalizer of `(f,g)`.
-/
/-
**CategoryTheory.Limits.of_iso_comparison** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.Limits`。
形式化陈述：of_iso_comparison [i : IsIso (coequalizerComparison f g G)] : PreservesCol
imit (parallelPair f g) G
参数：coequalizerComparison f g G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesColimit_of_preserves_colimit_cocone`：pres
ervesColimit_of_preserves_colimit_cocone {F : C ⥤ D} {t : Cocone K} (h : IsColim
it t) (hF : IsColimit (F.mapCocone t)) : PreservesColimi…
· 使用定理 `CategoryTheory.Limits.coequalizer.condition`：∀ {C : Type u} {X Y : C} [i
nst : CategoryTheory.Category.{v, u} C] (f g : X ⟶ Y)   [inst_1 : CategoryTheory
.Limits.HasCoequalizer f g],   Ca…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
If the coequalizer comparison map for `G` at `(f,g)` is an isomorphism, then `G`
 preserves the
coequalizer of `(f,g)`.
-/
lemma of_iso_comparison [i : IsIso (coequalizerComparison f g G)] :
    PreservesColimit (parallelPair f g) G := by
  apply preservesColimit_of_preserves_colimit_cocone (coequalizerIsCoequalizer f g)
  apply (isColimitMapCoconeCoforkEquiv _ _).symm _
  exact
    @IsColimit.ofPointIso _ _ _ _ _ _ _ (colimit.isColimit (parallelPair (G.map f) (G.map g))) i

variable [PreservesColimit (parallelPair f g) G]

/--
If `G` preserves the coequalizer of `(f,g)`, then the coequalizer comparison map for `G` at `(f,g)`
is an isomorphism.
-/
/-
**CategoryTheory.Limits.PreservesCoequalizer.iso** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Limits.PreservesCoequalizer`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} →       [inst_1 : CategoryTheory.Category.{v₂, u₂} D] →         (G : Cat
egoryTheory.Functor C D) →           {X Y : C} →             (f g : X ⟶ Y) →    
           [inst_2 : CategoryTheory.Limits.HasCoequalizer f g] →                
 [inst_3 : CategoryTheory.Limits.HasCoequalizer (G.map f) (G.map g)] →          
         [CategoryTheory.Limits.PreservesColimit (CategoryTheory.Limits.parallel
Pair f g) G] →                     CategoryTheory.Limits.coequalizer (G.map f) (
G.map g) ≅                       G.obj (CategoryTheory.Limits.coequalizer f g)
参数：G : CategoryTheory.Functor C D；f g : X ⟶ Y；G.map f；G.map g；CategoryTheory.Lim
its.parallelPair f g；G.map f；G.map g；CategoryTheory.Limits.coequalizer f g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `G` preserves the coequalizer of `(f,g)`, then the coequalizer comparison map
 for `G` at `(f,g)`
is an isomorphism.
-/
def PreservesCoequalizer.iso : coequalizer (G.map f) (G.map g) ≅ G.obj (coequalizer f g) :=
  IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
    (isColimitOfHasCoequalizerOfPreservesColimit G f g)

@[simp]
/-
**CategoryTheory.Limits.PreservesCoequalizer.iso_hom** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.Limits.PreservesCoequalizer`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (G : CategoryTheory.Functor C D)
 {X Y : C} (f g : X ⟶ Y) [inst_2 : CategoryTheory.Limits.HasCoequalizer f g]   [
inst_3 : CategoryTheory.Limits.HasCoequalizer (G.map f) (G.map g)]   [inst_4 : C
ategoryTheory.Limits.PreservesColimit (CategoryTheory.Limits.parallelPair f g) G
],   (CategoryTheory.Limits.PreservesCoequalizer.iso G f g).hom = CategoryTheory
.Limits.coequalizerComparison f g G
参数：G : CategoryTheory.Functor C D；f g : X ⟶ Y；G.map f；G.map g；CategoryTheory.Lim
its.parallelPair f g；CategoryTheory.Limits.PreservesCoequalizer.iso G f g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem PreservesCoequalizer.iso_hom :
    (PreservesCoequalizer.iso G f g).hom = coequalizerComparison f g G :=
  rfl
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsIso (coequalizerComparison f g G) := by
  rw [← PreservesCoequalizer.iso_hom]
  infer_instance
/-
**CategoryTheory.Limits.map_** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance map_π_epi : Epi (G.map (coequalizer.π f g)) :=
  ⟨fun {W} h k => by
    rw [← ι_comp_coequalizerComparison]
    have : Epi (coequalizer.π (G.map f) (G.map g) ≫ coequalizerComparison f g G) := by
      apply epi_comp
    apply (cancel_epi _).1⟩

@[reassoc]
/-
**CategoryTheory.Limits.map_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_π_preserves_coequalizer_inv :
    G.map (coequalizer.π f g) ≫ (PreservesCoequalizer.iso G f g).inv =
      coequalizer.π (G.map f) (G.map g) := by
  rw [← ι_comp_coequalizerComparison_assoc, ← PreservesCoequalizer.iso_hom, Iso.hom_inv_id,
    comp_id]

@[reassoc]
/-
**CategoryTheory.Limits.map_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_π_preserves_coequalizer_inv_desc {W : D} (k : G.obj Y ⟶ W)
    (wk : G.map f ≫ k = G.map g ≫ k) : G.map (coequalizer.π f g) ≫
      (PreservesCoequalizer.iso G f g).inv ≫ coequalizer.desc k wk = k := by
  rw [← Category.assoc, map_π_preserves_coequalizer_inv, coequalizer.π_desc]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**CategoryTheory.Limits.map_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_π_preserves_coequalizer_inv_colimMap {X' Y' : D} (f' g' : X' ⟶ Y')
    [HasCoequalizer f' g'] (p : G.obj X ⟶ X') (q : G.obj Y ⟶ Y') (wf : G.map f ≫ q = p ≫ f')
    (wg : G.map g ≫ q = p ≫ g') :
    G.map (coequalizer.π f g) ≫
        (PreservesCoequalizer.iso G f g).inv ≫
          colimMap (parallelPairHom (G.map f) (G.map g) f' g' p q wf wg) =
      q ≫ coequalizer.π f' g' := by
  rw [← Category.assoc, map_π_preserves_coequalizer_inv, ι_colimMap, parallelPairHom_app_one]

@[reassoc]
/-
**CategoryTheory.Limits.map_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_π_preserves_coequalizer_inv_colimMap_desc {X' Y' : D} (f' g' : X' ⟶ Y')
    [HasCoequalizer f' g'] (p : G.obj X ⟶ X') (q : G.obj Y ⟶ Y') (wf : G.map f ≫ q = p ≫ f')
    (wg : G.map g ≫ q = p ≫ g') {Z' : D} (h : Y' ⟶ Z') (wh : f' ≫ h = g' ≫ h) :
    G.map (coequalizer.π f g) ≫
        (PreservesCoequalizer.iso G f g).inv ≫
          colimMap (parallelPairHom (G.map f) (G.map g) f' g' p q wf wg) ≫ coequalizer.desc h wh =
      q ≫ h := by
  slice_lhs 1 3 => rw [map_π_preserves_coequalizer_inv_colimMap]
  slice_lhs 2 3 => rw [coequalizer.π_desc]

/-- Any functor preserves coequalizers of split pairs. -/
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any functor preserves coequalizers of split pairs.
-/
instance (priority := 1) preservesSplitCoequalizers (f g : X ⟶ Y) [HasSplitCoequalizer f g] :
    PreservesColimit (parallelPair f g) G := by
  apply
    preservesColimit_of_preserves_colimit_cocone
      (HasSplitCoequalizer.isSplitCoequalizer f g).isCoequalizer
  apply
    (isColimitMapCoconeCoforkEquiv G _).symm
      ((HasSplitCoequalizer.isSplitCoequalizer f g).map G).isCoequalizer
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 1) preservesSplitEqualizers (f g : X ⟶ Y) [HasSplitEqualizer f g] :
    PreservesLimit (parallelPair f g) G := by
  apply
    preservesLimit_of_preserves_limit_cone
      (HasSplitEqualizer.isSplitEqualizer f g).isEqualizer
  apply
    (isLimitMapConeForkEquiv G _).symm
      ((HasSplitEqualizer.isSplitEqualizer f g).map G).isEqualizer

end Coequalizers

end CategoryTheory.Limits

