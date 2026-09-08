/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Functor.ReflectsIso.Jointly
public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.Algebra.Homology.QuasiIso

/-!
# Exactness properties of functors which jointly reflect isomorphisms

Let `Fᵢ : C ⥤ Dᵢ` be a family of exact functors between abelian categories.
Assume that they jointly reflect isomorphisms. We show that a short complex in `C`
is exact (resp. short exact) iff it is so after applying the functor `Fᵢ`.
Similar results are obtained for the detection of quasi-isomorphisms
between short complexes or homological complexes in `C`.
(Corresponding results for a single functor are
`HomologicalComplex.quasiIsoAt_map_iff_of_preservesHomology` and
`HomologicalComplex.quasiIso_map_iff_of_preservesHomology` in the files
`Mathlib/Algebra/Homology/QuasiIso.lean` and
`ShortComplex.quasiIso_map_iff_of_preservesLeftHomology`
`Mathlib/Algebra/Homology/ShortComplex/PreservesHomology.lean`.)

-/

public section

namespace CategoryTheory

open Category Limits ZeroObject

variable {C : Type*} [Category* C] {I : Type*} {D : I → Type*} [∀ i, Category* (D i)]
  {F : ∀ i, C ⥤ D i}

namespace JointlyReflectIsomorphisms

variable (hP : JointlyReflectIsomorphisms F)

include hP

section

variable [HasZeroMorphisms C] [∀ i, HasZeroMorphisms (D i)]
  [∀ i, (F i).PreservesZeroMorphisms]

/-
**CategoryTheory.JointlyReflectIsomorphisms.isZero_iff** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.JointlyReflectIsomorphisms`。
形式化陈述：isZero_iff [HasZeroObject C] {X : C} : IsZero X ↔ forall (i : I), IsZero (
(F i).obj X)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.map_isZero`：map_isZero (F : C ⥤ D) [PreservesZero
Morphisms F] {X : C} (hX : IsZero X) : IsZero (F.obj X)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.JointlyReflectIsomorphisms.isIso_iff`：isIso_iff {X Y : C}
 (f : X ⟶ Y) : IsIso f ↔ forall i, IsIso ((F i).map f)
· 使用引理 `CategoryTheory.Limits.IsZero.isIso`：isIso (hX : IsZero X) (hY : IsZero Y
) (f : X ⟶ Y) : IsIso f
· 使用定理 `CategoryTheory.Limits.isZero_zero`：isZero_zero : IsZero (0 : C)
· 使用定理 `CategoryTheory.Limits.IsZero.of_iso`：of_iso (hY : IsZero Y) (e : X ≅ Y) 
: IsZero X
-/
lemma isZero_iff [HasZeroObject C] {X : C} :
    IsZero X ↔ ∀ (i : I), IsZero ((F i).obj X) := by
  refine ⟨fun hX _ ↦ Functor.map_isZero _ hX, fun hX ↦ ?_⟩
  let φ : 0 ⟶ X := 0
  have : IsIso φ := by
    rw [hP.isIso_iff]
    exact fun i ↦ (Functor.map_isZero _ (isZero_zero _)).isIso (hX i) _
  exact (isZero_zero C).of_iso (asIso φ).symm

variable [CategoryWithHomology C] [∀ i, (F i).PreservesHomology]
/-
**CategoryTheory.JointlyReflectIsomorphisms.exact_iff** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.JointlyReflectIsomorphisms`。
形式化陈述：exact_iff [HasZeroObject C] (S : ShortComplex C) : S.Exact ↔ forall (i : I
), (S.map (F i)).Exact
参数：S : ShortComplex C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ShortComplex.Exact.map`：∀ {C : Type u_1} {D : Type u_2} [
inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Category
.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Functor.PreservesHomology.preservesLeftHomologyOf`：∀ {C :
 Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_
1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Functor.PreservesHomology.preservesRightHomologyOf`：∀ {C 
: Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst
_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.JointlyReflectIsomorphisms.isZero_iff`：isZero_iff [HasZer
oObject C] {X : C} : IsZero X ↔ forall (i : I), IsZero ((F i).obj X)
· 使用定理 `CategoryTheory.Limits.IsZero.of_iso`：of_iso (hY : IsZero Y) (e : X ≅ Y) 
: IsZero X
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
-/
lemma exact_iff [HasZeroObject C] (S : ShortComplex C) :
    S.Exact ↔ ∀ (i : I), (S.map (F i)).Exact := by
  refine ⟨fun hS i ↦ hS.map _, fun hS ↦ ?_⟩
  simp only [ShortComplex.exact_iff_isZero_homology] at hS ⊢
  rw [hP.isZero_iff]
  exact fun i ↦ (hS i).of_iso (S.mapHomologyIso (F i)).symm
/-
**CategoryTheory.JointlyReflectIsomorphisms.exactAt_iff** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.JointlyReflectIsomorphisms`。
形式化陈述：exactAt_iff [HasZeroObject C] {α : Type*} {c : ComplexShape α} (K : Homolo
gicalComplex C c) (a : α) : K.ExactAt a ↔ forall (i : I), (((F i).mapHomological
Complex c).obj K).ExactAt a
参数：K : HomologicalComplex C c；a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.JointlyReflectIsomorphisms.exact_iff`：exact_iff [HasZeroO
bject C] (S : ShortComplex C) : S.Exact ↔ forall (i : I), (S.map (F i)).Exact
-/
lemma exactAt_iff [HasZeroObject C] {α : Type*} {c : ComplexShape α}
    (K : HomologicalComplex C c) (a : α) :
    K.ExactAt a ↔ ∀ (i : I), (((F i).mapHomologicalComplex c).obj K).ExactAt a :=
  hP.exact_iff _

end

section

variable [Abelian C] [∀ i, Abelian (D i)] [CategoryWithHomology C]
  [∀ i, PreservesFiniteLimits (F i)] [∀ i, PreservesFiniteColimits (F i)]

/-
**CategoryTheory.JointlyReflectIsomorphisms.shortExact_iff** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.JointlyReflectIsomorphisms`。
形式化陈述：shortExact_iff (S : ShortComplex C) : S.ShortExact ↔ forall (i : I), (S.ma
p (F i)).ShortExact
参数：S : ShortComplex C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_preserves_terminal_obje
ct`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [i
nst_1 : CategoryTheory.Category.{v₂, u₂} D]   [CategoryTheory.Li…
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.PreservesFiniteLimits.preservesFiniteLimits`：∀ {C 
: Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : C
ategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
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
· 使用定理 `CategoryTheory.Functor.PreservesHomology.preservesRightHomologyOf`：∀ {C 
: Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst
_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Functor.map_mono`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.instPreservesMonomorphisms`：∀ {C : Type u_1} {D :
 Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryThe
ory.Category.{v_2, u_2} D] (F : Categor…
· 使用定理 `CategoryTheory.Functor.instPreservesEpimorphisms`：∀ {C : Type u_1} {D : 
Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheo
ry.Category.{v_2, u_2} D] (F : Categor…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.JointlyReflectMonomorphisms.mono_iff`：∀ {C : Type u_1} [i
nst : CategoryTheory.Category.{u_4, u_1} C] {I : Type u_2} {D : I → Type u_3}   
[inst_1 : (i : I) → CategoryTheory.Catego…
· 使用引理 `CategoryTheory.JointlyReflectIsomorphisms.jointlyReflectMonomorphisms`：j
ointlyReflectMonomorphisms [forall i, PreservesLimitsOfShape WalkingCospan (F i)
] [HasPullbacks C] : JointlyReflectMonomorphisms F where mo…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePullbacks_of_hasFiniteLimits`：∀ (C : 
Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFini
teLimits C],   CategoryTheory.Limits.HasFiniteWidePul…
· 使用定理 `CategoryTheory.Abelian.hasFiniteLimits`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.Has
FiniteLimits C
· 使用定理 `CategoryTheory.JointlyReflectEpimorphisms.epi_iff`：∀ {C : Type u_1} [ins
t : CategoryTheory.Category.{u_4, u_1} C] {I : Type u_2} {D : I → Type u_3}   [i
nst_1 : (i : I) → CategoryTheory.Catego…
· 使用引理 `CategoryTheory.JointlyReflectIsomorphisms.jointlyReflectEpimorphisms`：jo
intlyReflectEpimorphisms [forall i, PreservesColimitsOfShape WalkingSpan (F i)] 
[HasPushouts C] : JointlyReflectEpimorphisms F where epi f…
· 使用定理 `CategoryTheory.Limits.PreservesFiniteColimits.preservesFiniteColimits`：∀
 {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1
 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePushouts_of_has_finite_limits`：∀ (C :
 Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFin
iteColimits C],   CategoryTheory.Limits.HasFiniteWideP…
· 使用定理 `CategoryTheory.Abelian.hasFiniteColimits`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.H
asFiniteColimits C
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `CategoryTheory.JointlyReflectIsomorphisms.exact_iff`：exact_iff [HasZeroO
bject C] (S : ShortComplex C) : S.Exact ↔ forall (i : I), (S.map (F i)).Exact
· 使用定理 `CategoryTheory.ShortComplex.ShortExact.exact`：∀ {C : Type u_1} [inst : C
ategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorp
hisms C]   {S : CategoryTheory.Sho…
-/
lemma shortExact_iff (S : ShortComplex C) :
    S.ShortExact ↔ ∀ (i : I), (S.map (F i)).ShortExact := by
  refine ⟨fun hS i ↦ ?_, fun hS ↦ ?_⟩
  · have := hS.mono_f
    have := hS.epi_g
    exact hS.map (F i)
  · have : Mono S.f := by
      rw [hP.jointlyReflectMonomorphisms.mono_iff]
      exact fun i ↦ (hS i).mono_f
    have : Epi S.g := by
      rw [hP.jointlyReflectEpimorphisms.epi_iff]
      exact fun i ↦ (hS i).epi_g
    exact { exact := (hP.exact_iff S).2 (fun i ↦ (hS i).exact) }
/-
**CategoryTheory.JointlyReflectIsomorphisms.shortComplexQuasiIso_iff** 是 Mathlib
 中的一个引理，位于命名空间 `CategoryTheory.JointlyReflectIsomorphisms`。
形式化陈述：shortComplexQuasiIso_iff {S₁ S₂ : ShortComplex C} (f : S₁ ⟶ S₂) : ShortCom
plex.QuasiIso f ↔ forall (i : I), ShortComplex.QuasiIso ((F i).mapShortComplex.m
ap f)
参数：f : S₁ ⟶ S₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_preserves_terminal_obje
ct`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [i
nst_1 : CategoryTheory.Category.{v₂, u₂} D]   [CategoryTheory.Li…
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.PreservesFiniteLimits.preservesFiniteLimits`：∀ {C 
: Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : C
ategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.PreservesHomology.preservesLeftHomologyOf`：∀ {C :
 Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_
1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Functor.preservesHomologyOfExact`：∀ {C : Type u_1} {D : T
ype u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheor
y.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Functor.PreservesHomology.preservesRightHomologyOf`：∀ {C 
: Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst
_1 : CategoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.JointlyReflectIsomorphisms.isIso_iff`：isIso_iff {X Y : C}
 (f : X ⟶ Y) : IsIso f ↔ forall i, IsIso ((F i).map f)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用定理 `CategoryTheory.MorphismProperty.arrow_mk_iso_iff`：arrow_mk_iso_iff (P : 
MorphismProperty C) [RespectsIso P] {W X Y Z : C} {f : W ⟶ X} {g : Y ⟶ Z} (e : A
rrow.mk f ≅ Arrow.mk g) : P f ↔ P g
· 使用定理 `CategoryTheory.MorphismProperty.RespectsIso.isomorphisms`：∀ (C : Type u)
 [inst : CategoryTheory.Category.{v, u} C], (CategoryTheory.MorphismProperty.iso
morphisms C).RespectsIso
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
-/
lemma shortComplexQuasiIso_iff {S₁ S₂ : ShortComplex C} (f : S₁ ⟶ S₂) :
    ShortComplex.QuasiIso f ↔
      ∀ (i : I), ShortComplex.QuasiIso ((F i).mapShortComplex.map f) := by
  refine ⟨fun hf i ↦ inferInstance, fun hf ↦ ?_⟩
  simp only [ShortComplex.quasiIso_iff] at hf ⊢
  rw [hP.isIso_iff]
  exact fun i ↦ ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff
    (((Functor.mapArrowFunctor _ _).mapIso (ShortComplex.homologyFunctorIso (F i))).app
      (Arrow.mk f))).1 (hf i)

section

variable {α : Type*} {c : ComplexShape α} {K L : HomologicalComplex C c}

/-
**CategoryTheory.JointlyReflectIsomorphisms.quasiIsoAt_iff** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.JointlyReflectIsomorphisms`。
形式化陈述：quasiIsoAt_iff (f : K ⟶ L) (a : α) : QuasiIsoAt f a ↔ forall (i : I), Quas
iIsoAt (((F i).mapHomologicalComplex c).map f) a
参数：f : K ⟶ L；a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_preserves_terminal_obje
ct`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [i
nst_1 : CategoryTheory.Category.{v₂, u₂} D]   [CategoryTheory.Li…
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.PreservesFiniteLimits.preservesFiniteLimits`：∀ {C 
: Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : C
ategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `quasiIsoAt_iff'`：quasiIsoAt_iff' (f : K ⟶ L) (i j k : ι) (hi : c.prev j 
= i) (hk : c.next j = k) [K.HasHomology j] [L.HasHomology j] [(K.sc' i j k).HasH
omolo…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用引理 `CategoryTheory.JointlyReflectIsomorphisms.shortComplexQuasiIso_iff`：shor
tComplexQuasiIso_iff {S₁ S₂ : ShortComplex C} (f : S₁ ⟶ S₂) : ShortComplex.Quasi
Iso f ↔ forall (i : I), ShortComplex.QuasiIso ((F i).map…
-/
lemma quasiIsoAt_iff (f : K ⟶ L) (a : α) :
    QuasiIsoAt f a ↔ ∀ (i : I), QuasiIsoAt (((F i).mapHomologicalComplex c).map f) a := by
  simpa only [quasiIsoAt_iff' _ _ _ _ rfl rfl] using!
    hP.shortComplexQuasiIso_iff _
/-
**CategoryTheory.JointlyReflectIsomorphisms.quasiIso_iff** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.JointlyReflectIsomorphisms`。
形式化陈述：quasiIso_iff (f : K ⟶ L) : QuasiIso f ↔ forall (i : I), QuasiIso (((F i).m
apHomologicalComplex c).map f)
参数：f : K ⟶ L。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_preserves_terminal_obje
ct`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [i
nst_1 : CategoryTheory.Category.{v₂, u₂} D]   [CategoryTheory.Li…
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.PreservesFiniteLimits.preservesFiniteLimits`：∀ {C 
: Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : C
ategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用引理 `CategoryTheory.JointlyReflectIsomorphisms.quasiIsoAt_iff`：quasiIsoAt_iff
 (f : K ⟶ L) (a : α) : QuasiIsoAt f a ↔ forall (i : I), QuasiIsoAt (((F i).mapHo
mologicalComplex c).map f) a
-/
lemma quasiIso_iff (f : K ⟶ L) :
    QuasiIso f ↔ ∀ (i : I), QuasiIso (((F i).mapHomologicalComplex c).map f) := by
  simp only [_root_.quasiIso_iff, hP.quasiIsoAt_iff]
  tauto

end

end

end JointlyReflectIsomorphisms

end CategoryTheory

