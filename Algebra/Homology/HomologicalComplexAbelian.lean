/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-! # THe category of homological complexes is abelian

If `C` is an abelian category, then `HomologicalComplex C c` is an abelian
category for any complex shape `c : ComplexShape ι`.

We also obtain that a short complex in `HomologicalComplex C c`
is exact (resp. short exact) iff degreewise it is so.

-/

public section

open CategoryTheory Category Limits

namespace HomologicalComplex

variable {C ι : Type*} {c : ComplexShape ι} [Category* C]

section

variable [Abelian C]

/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : IsNormalEpiCategory (HomologicalComplex C c) := ⟨fun p _ =>
  ⟨NormalEpi.mk _ (kernel.ι p) (kernel.condition _)
    (isColimitOfEval _ _ (fun _ =>
      Abelian.isColimitMapCoconeOfCokernelCoforkOfπ _ _))⟩⟩
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : IsNormalMonoCategory (HomologicalComplex C c) := ⟨fun p _ =>
  ⟨NormalMono.mk _ (cokernel.π p) (cokernel.condition _)
    (isLimitOfEval _ _ (fun _ =>
      Abelian.isLimitMapConeOfKernelForkOfι _ _))⟩⟩
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : Abelian (HomologicalComplex C c) where

variable (S : ShortComplex (HomologicalComplex C c))
/-
**HomologicalComplex.exact_of_degreewise_exact** 是 Mathlib 中的一个引理，位于命名空间 `Homolo
gicalComplex`。
形式化陈述：exact_of_degreewise_exact (hS : forall (i : ι), (S.map (eval C c i)).Exact
) : S.Exact
参数：hS : forall (i : ι), (S.map (eval C c i)).Exact。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex.instPreservesZeroMorphismsEval`：∀ {ι : Type u_1} (V :
 Type u) [inst : CategoryTheory.Category.{v, u} V]   [inst_1 : CategoryTheory.Li
mits.HasZeroMorphisms V] (c : ComplexSh…
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.IsZero.iff_id_eq_zero`：iff_id_eq_zero (X : C) : Is
Zero X ↔ 𝟙 X = 0
· 使用引理 `HomologicalComplex.hom_ext`：hom_ext {C D : HomologicalComplex V c} (f g 
: C ⟶ D) (h : forall i, f.f i = g.f i) : f = g
· 使用定理 `CategoryTheory.Limits.IsZero.eq_of_src`：eq_of_src (hX : IsZero X) (f g :
 X ⟶ Y) : f = g
· 使用定理 `CategoryTheory.Limits.IsZero.of_iso`：of_iso (hY : IsZero Y) (e : X ≅ Y) 
: IsZero X
· 使用定理 `CategoryTheory.Functor.PreservesHomology.preservesLeftHomologyOf`：∀ {C :
 Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_
1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Functor.preservesHomologyOfExact`：∀ {C : Type u_1} {D : T
ype u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheor
y.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `HomologicalComplex.instPreservesFiniteLimitsEvalOfHasFiniteLimits`：∀ {C 
: Type u_1} {ι : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C] {c : Co
mplexShape ι}   [inst_1 : CategoryTheory.Limits.HasZero…
· 使用定理 `CategoryTheory.Abelian.hasFiniteLimits`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.Has
FiniteLimits C
· 使用定理 `HomologicalComplex.instPreservesFiniteColimitsEvalOfHasFiniteColimits`：∀
 {C : Type u_1} {ι : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C] {c 
: ComplexShape ι}   [inst_1 : CategoryTheory.Limits.HasZero…
· 使用定理 `CategoryTheory.Abelian.hasFiniteColimits`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.H
asFiniteColimits C
· 使用定理 `CategoryTheory.Functor.PreservesHomology.preservesRightHomologyOf`：∀ {C 
: Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst
_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
-/
lemma exact_of_degreewise_exact (hS : ∀ (i : ι), (S.map (eval C c i)).Exact) :
    S.Exact := by
  simp only [ShortComplex.exact_iff_isZero_homology] at hS ⊢
  rw [IsZero.iff_id_eq_zero]
  ext i
  apply (IsZero.of_iso (hS i) (S.mapHomologyIso (eval C c i)).symm).eq_of_src
/-
**HomologicalComplex.shortExact_of_degreewise_shortExact** 是 Mathlib 中的一个引理，位于命名
空间 `HomologicalComplex`。
形式化陈述：shortExact_of_degreewise_shortExact (hS : forall (i : ι), (S.map (eval C c
 i)).ShortExact) : S.ShortExact where mono_f
参数：hS : forall (i : ι), (S.map (eval C c i)).ShortExact。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex.instPreservesZeroMorphismsEval`：∀ {ι : Type u_1} (V :
 Type u) [inst : CategoryTheory.Category.{v, u} V]   [inst_1 : CategoryTheory.Li
mits.HasZeroMorphisms V] (c : ComplexSh…
· 使用引理 `HomologicalComplex.exact_of_degreewise_exact`：exact_of_degreewise_exact 
(hS : forall (i : ι), (S.map (eval C c i)).Exact) : S.Exact
· 使用定理 `CategoryTheory.ShortComplex.ShortExact.exact`：∀ {C : Type u_1} [inst : C
ategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorp
hisms C]   {S : CategoryTheory.Sho…
· 使用引理 `HomologicalComplex.mono_of_mono_f`：mono_of_mono_f {K L : HomologicalComp
lex V c} (φ : K ⟶ L) (hφ : forall i, Mono (φ.f i)) : Mono φ where right_cancella
tion g h eq
· 使用定理 `CategoryTheory.ShortComplex.ShortExact.mono_f`：∀ {C : Type u_1} [inst : 
CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMor
phisms C]   {S : CategoryTheory.Sho…
· 使用引理 `HomologicalComplex.epi_of_epi_f`：epi_of_epi_f {K L : HomologicalComplex 
V c} (φ : K ⟶ L) (hφ : forall i, Epi (φ.f i)) : Epi φ where left_cancellation g 
h eq
· 使用定理 `CategoryTheory.ShortComplex.ShortExact.epi_g`：∀ {C : Type u_1} [inst : C
ategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorp
hisms C]   {S : CategoryTheory.Sho…
-/
lemma shortExact_of_degreewise_shortExact
    (hS : ∀ (i : ι), (S.map (eval C c i)).ShortExact) :
    S.ShortExact where
  mono_f := mono_of_mono_f _ (fun i => (hS i).mono_f)
  epi_g := epi_of_epi_f _ (fun i => (hS i).epi_g)
  exact := exact_of_degreewise_exact S (fun i => (hS i).exact)
/-
**HomologicalComplex.exact_iff_degreewise_exact** 是 Mathlib 中的一个引理，位于命名空间 `Homol
ogicalComplex`。
形式化陈述：exact_iff_degreewise_exact : S.Exact ↔ forall (i : ι), (S.map (eval C c i)
).Exact
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex.instPreservesZeroMorphismsEval`：∀ {ι : Type u_1} (V :
 Type u) [inst : CategoryTheory.Category.{v, u} V]   [inst_1 : CategoryTheory.Li
mits.HasZeroMorphisms V] (c : ComplexSh…
· 使用定理 `CategoryTheory.ShortComplex.Exact.map`：∀ {C : Type u_1} {D : Type u_2} [
inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Category
.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Functor.PreservesHomology.preservesLeftHomologyOf`：∀ {C :
 Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_
1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Functor.preservesHomologyOfExact`：∀ {C : Type u_1} {D : T
ype u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheor
y.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `HomologicalComplex.instPreservesFiniteLimitsEvalOfHasFiniteLimits`：∀ {C 
: Type u_1} {ι : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C] {c : Co
mplexShape ι}   [inst_1 : CategoryTheory.Limits.HasZero…
· 使用定理 `CategoryTheory.Abelian.hasFiniteLimits`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.Has
FiniteLimits C
· 使用定理 `HomologicalComplex.instPreservesFiniteColimitsEvalOfHasFiniteColimits`：∀
 {C : Type u_1} {ι : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C] {c 
: ComplexShape ι}   [inst_1 : CategoryTheory.Limits.HasZero…
· 使用定理 `CategoryTheory.Abelian.hasFiniteColimits`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.H
asFiniteColimits C
· 使用定理 `CategoryTheory.Functor.PreservesHomology.preservesRightHomologyOf`：∀ {C 
: Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst
_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用引理 `HomologicalComplex.exact_of_degreewise_exact`：exact_of_degreewise_exact 
(hS : forall (i : ι), (S.map (eval C c i)).Exact) : S.Exact
-/
lemma exact_iff_degreewise_exact :
    S.Exact ↔ ∀ (i : ι), (S.map (eval C c i)).Exact := by
  constructor
  · intro hS i
    exact hS.map (eval C c i)
  · exact exact_of_degreewise_exact S
/-
**HomologicalComplex.shortExact_iff_degreewise_shortExact** 是 Mathlib 中的一个引理，位于命
名空间 `HomologicalComplex`。
形式化陈述：shortExact_iff_degreewise_shortExact : S.ShortExact ↔ forall (i : ι), (S.m
ap (eval C c i)).ShortExact
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HomologicalComplex.instPreservesZeroMorphismsEval`：∀ {ι : Type u_1} (V :
 Type u) [inst : CategoryTheory.Category.{v, u} V]   [inst_1 : CategoryTheory.Li
mits.HasZeroMorphisms V] (c : ComplexSh…
· 使用定理 `CategoryTheory.ShortComplex.ShortExact.mono_f`：∀ {C : Type u_1} [inst : 
CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMor
phisms C]   {S : CategoryTheory.Sho…
· 使用定理 `CategoryTheory.ShortComplex.ShortExact.epi_g`：∀ {C : Type u_1} [inst : C
ategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorp
hisms C]   {S : CategoryTheory.Sho…
· 使用定理 `CategoryTheory.ShortComplex.ShortExact.map`：∀ {C : Type u_1} {D : Type u
_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Cat
egory.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Functor.PreservesHomology.preservesLeftHomologyOf`：∀ {C :
 Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_
1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Functor.preservesHomologyOfExact`：∀ {C : Type u_1} {D : T
ype u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheor
y.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `HomologicalComplex.instPreservesFiniteLimitsEvalOfHasFiniteLimits`：∀ {C 
: Type u_1} {ι : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C] {c : Co
mplexShape ι}   [inst_1 : CategoryTheory.Limits.HasZero…
· 使用定理 `CategoryTheory.Abelian.hasFiniteLimits`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.Has
FiniteLimits C
· 使用定理 `HomologicalComplex.instPreservesFiniteColimitsEvalOfHasFiniteColimits`：∀
 {C : Type u_1} {ι : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C] {c 
: ComplexShape ι}   [inst_1 : CategoryTheory.Limits.HasZero…
· 使用定理 `CategoryTheory.Abelian.hasFiniteColimits`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.H
asFiniteColimits C
· 使用定理 `CategoryTheory.Functor.PreservesHomology.preservesRightHomologyOf`：∀ {C 
: Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst
_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Functor.map_mono`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.instPreservesMonomorphisms`：∀ {C : Type u_1} {D :
 Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryThe
ory.Category.{v_2, u_2} D] (F : Categor…
· 使用定理 `HomologicalComplex.instHasZeroObject`：∀ {ι : Type u_1} {V : Type u} [ins
t : CategoryTheory.Category.{v, u} V]   [inst_1 : CategoryTheory.Limits.HasZeroM
orphisms V] {c : ComplexSh…
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `CategoryTheory.Functor.instPreservesEpimorphisms`：∀ {C : Type u_1} {D : 
Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheo
ry.Category.{v_2, u_2} D] (F : Categor…
· 使用引理 `HomologicalComplex.shortExact_of_degreewise_shortExact`：shortExact_of_de
greewise_shortExact (hS : forall (i : ι), (S.map (eval C c i)).ShortExact) : S.S
hortExact where mono_f
-/
lemma shortExact_iff_degreewise_shortExact :
    S.ShortExact ↔ ∀ (i : ι), (S.map (eval C c i)).ShortExact := by
  constructor
  · intro hS i
    have := hS.mono_f
    have := hS.epi_g
    exact hS.map (eval C c i)
  · exact shortExact_of_degreewise_shortExact S

end

section

variable [HasZeroMorphisms C] [HasZeroObject C] [DecidableEq ι]

/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (i j : ι) (I : C) [Injective I] :
    Injective (((single C c i).obj I).X j) := by
  by_cases hij : j = i
  · subst hij
    simp only [single_obj_X_self]
    infer_instance
  · exact (isZero_single_obj_X _ _ _ _ hij).injective
/-
**HomologicalComplex.** 是 Mathlib 中的一个实例，位于命名空间 `HomologicalComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (i j : ι) (P : C) [Projective P] :
    Projective (((single C c i).obj P).X j) := by
  by_cases hij : j = i
  · subst hij
    simp only [single_obj_X_self]
    infer_instance
  · exact (isZero_single_obj_X _ _ _ _ hij).projective

end

end HomologicalComplex

namespace CategoryTheory

open Limits

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
variable {D : Type*} [Category* D] [HasZeroMorphisms D]

variable (F : C ⥤ D) {ι : Type*} (c : ComplexShape ι)

/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [F.PreservesZeroMorphisms] {J : Type*} [Category* J] [HasLimitsOfShape J C]
    [PreservesLimitsOfShape J F] : PreservesLimitsOfShape J (F.mapHomologicalComplex c) :=
  HomologicalComplex.preservesLimitsOfShape_of_eval _ (fun i ↦
    inferInstanceAs <| PreservesLimitsOfShape J <| HomologicalComplex.eval C c i ⋙ F)
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [F.PreservesZeroMorphisms] {J : Type*} [Category* J] [HasColimitsOfShape J C]
    [PreservesColimitsOfShape J F] : PreservesColimitsOfShape J (F.mapHomologicalComplex c) :=
  HomologicalComplex.preservesColimitsOfShape_of_eval _ (fun i ↦
    inferInstanceAs <| PreservesColimitsOfShape J <| HomologicalComplex.eval C c i ⋙ F)
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasFiniteLimits C] [F.PreservesZeroMorphisms] [PreservesFiniteLimits F] :
    PreservesFiniteLimits (F.mapHomologicalComplex c) :=
  ⟨by intros; infer_instance⟩
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasFiniteColimits C] [F.PreservesZeroMorphisms] [PreservesFiniteColimits F] :
    PreservesFiniteColimits (F.mapHomologicalComplex c) :=
  ⟨by intros; infer_instance⟩

end CategoryTheory

