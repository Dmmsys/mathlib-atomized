/-
Copyright (c) 2026 Brian Nugent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Nugent
-/
module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Balanced
public import Mathlib.Topology.Sheaves.Limits
public import Mathlib.Topology.Sheaves.Skyscraper

/-!
# Sheaves over Abelian categories

We provide instances for categories of sheaves over Abelian categories.

## Main Results

* `TopCat.Sheaf.exact_iff_stalkFunctor_map_exact`: A complex of sheaves over a concrete abelian
  category is exact if and only if it is exact on stalks.

-/

public section

universe u v v₁ v₂

open TopologicalSpace CategoryTheory Limits

namespace TopCat

variable {X : TopCat.{u}}

section

variable {C : Type v₁} [Category.{v₂} C] [HasSheafify (Opens.grothendieckTopology X) C] [Abelian C]

/-
**TopCat.** 是 Mathlib 中的一个实例，位于命名空间 `TopCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : Abelian (Presheaf C X) := inferInstanceAs (Abelian (_ ⥤ _))

namespace Sheaf

/-
**TopCat.Sheaf.** 是 Mathlib 中的一个实例，位于命名空间 `TopCat.Sheaf`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : Abelian (Sheaf C X) :=
  inferInstanceAs (Abelian (CategoryTheory.Sheaf _ _))
/-
**TopCat.Sheaf.** 是 Mathlib 中的一个实例，位于命名空间 `TopCat.Sheaf`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (Sheaf.forget C X).Additive where
/-
**TopCat.Sheaf.** 是 Mathlib 中的一个实例，位于命名空间 `TopCat.Sheaf`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {D : Type*} [Category.{u} D] [Abelian D] [IsGrothendieckAbelian.{u} D]
    [HasSheafify (Opens.grothendieckTopology X) D] : IsGrothendieckAbelian.{u} (Sheaf D X) :=
  inferInstanceAs (IsGrothendieckAbelian (CategoryTheory.Sheaf _ _))

end Sheaf

end

set_option backward.isDefEq.respectTransparency false in
/-- The stalk functor is additive -/
/-
**TopCat.** 是 Mathlib 中的一个实例，位于命名空间 `TopCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The stalk functor is additive
-/
instance (p₀ : X) {C : Type v} [Category.{u} C] [Abelian C] [HasColimits C] :
    (Presheaf.stalkFunctor C p₀).Additive := by
  dsimp [Presheaf.stalkFunctor]
  have : ((Functor.whiskeringLeft _ _ C).obj (OpenNhds.inclusion p₀).op).Additive := ⟨by cat_disch⟩
  infer_instance

namespace Sheaf

open Presheaf

variable {C : Type v} [Category.{u} C] [HasColimits C] [HasLimits C]
  {FC : C → C → Type*} {CC : C → Type u} [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)]
  [instCC : ConcreteCategory C FC] [PreservesFilteredColimits (CategoryTheory.forget C)]
  [PreservesLimits (CategoryTheory.forget C)] [Abelian C]
  {X : TopCat.{u}} (p₀ : X)

/-
**TopCat.Sheaf.** 是 Mathlib 中的一个实例，位于命名空间 `TopCat.Sheaf`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Limits.PreservesFiniteLimits (forget C X ⋙ stalkFunctor C p₀) :=
  have : (forget C X ⋙ stalkFunctor C p₀).PreservesHomology := by
    simp only [(forget C X ⋙ stalkFunctor C p₀).exact_tfae.out 2 0]
    intro S h
    have := ((forget C X ⋙ stalkFunctor C p₀).preservesFiniteColimits_tfae.out 3 0).mp
      (inferInstance : (PreservesFiniteColimits _))
    refine ShortComplex.ShortExact.mk' (this S h).left ?_ (this S h).right
    have := h.2
    exact Functor.map_mono (forget C X ⋙ stalkFunctor C p₀) _
  (forget C X ⋙ stalkFunctor C p₀).preservesFiniteLimits_of_preservesHomology

open ZeroObject

include instCC in
/-- A sheaf is zero if and only if its stalks are all zero. -/
/-
**TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero** 是 Mathlib 中的一个引理，位于命名空间 `Top
Cat.Sheaf`。
形式化陈述：isZero_iff_stalkFunctor_obj_isZero (F : Sheaf C X) : IsZero F ↔ forall x :
 X, IsZero ((forget C X ⋙ stalkFunctor C x).obj F)
参数：F : Sheaf C X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.map_isZero`：map_isZero (F : C ⥤ D) [PreservesZero
Morphisms F] {X : C} (hX : IsZero X) : IsZero (F.obj X)
· 使用定理 `CategoryTheory.instHasSheafifyOfPreservesLimitsForgetOfHasFiniteLimitsOf
SmallOppositeCover`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (J 
: CategoryTheory.GrothendieckTopology C) (D : Type w)   [inst_1 : CategoryTheory
…
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.instHasLimitsOfShapeOfHasLimitsOfSize`：∀ {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTh
eory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.hasColimitsOfShape_of_has_filtered_colimits`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C]   [CategoryTheory.Limits.Has
FilteredColimitsOfSize.{w', w, v, u} C] (I : Type w)   …
· 使用定理 `CategoryTheory.Limits.hasFilteredColimitsOfSize_of_hasColimitsOfSize`：∀ 
{C : Type u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.Ha
sColimitsOfSize.{w', w, v, u} C],   CategoryTheory.Limits.…
· 使用定理 `CategoryTheory.isCofiltered_of_directed_ge_nonempty`：∀ (α : Type u) [ins
t : Preorder α] [IsCodirectedOrder α] [Nonempty α], CategoryTheory.IsCofiltered 
α
· 使用定理 `SemilatticeInf.instIsCodirectedOrder`：∀ {α : Type u_1} [inst : Semilatti
ceInf α], IsCodirectedOrder α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `CategoryTheory.Limits.PreservesFilteredColimitsOfSize.preserves_filtered
_colimits`：∀ {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type
 u₂} {inst_1 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.reflectsIsomorphisms_of_reflectsMonomorphisms_of_reflects
Epimorphisms`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {D 
: Type u_2}   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [CategoryThe…
· 使用定理 `CategoryTheory.balanced_of_strongMonoCategory`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] [CategoryTheory.StrongMonoCategory C],   Categor
yTheory.Balanced C
· 使用定理 `CategoryTheory.strongMonoCategory_of_regularMonoCategory`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] [CategoryTheory.IsRegularMonoCateg
ory C],   CategoryTheory.StrongMonoCategory C
· 使用定理 `CategoryTheory.regularMonoCategoryOfNormalMonoCategory`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Limits.HasZ
eroMorphisms C]   [CategoryTheory.IsNormalMo…
· 使用定理 `CategoryTheory.Abelian.toIsNormalMonoCategory`：∀ {C : Type u} {inst : Ca
tegoryTheory.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryThe
ory.IsNormalMonoCategory C
· 使用定理 `CategoryTheory.Functor.reflectsMonomorphisms_of_faithful`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTh
eory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.instFaithfulForget`：∀ (C : Type u_1) [inst : CategoryTheo
ry.Category.{v_1, u_1} C] {FC : outParam (C → C → Type u_2)}   {CC : outParam (C
 → Type w)} [inst_1 : o…
· 使用定理 `CategoryTheory.Functor.reflectsEpimorphisms_of_faithful`：∀ {C : Type u₁}
 [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryThe
ory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfSize.preservesLimitsOfShape`：∀ {C
 : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : 
CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.hasFiniteLimits_of_hasCountableLimits`：∀ (C : Type
 u_1) [inst : CategoryTheory.Category.{v_1, u_1} C] [CategoryTheory.Limits.HasCo
untableLimits C],   CategoryTheory.Limits.HasFini…
· 使用定理 `CategoryTheory.Limits.hasCountableLimits_of_hasLimits`：∀ (C : Type u_1) 
[inst : CategoryTheory.Category.{v_1, u_1} C] [CategoryTheory.Limits.HasLimits C
],   CategoryTheory.Limits.HasCountableLimi…
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `TopCat.Sheaf.instAdditivePresheafForget`：∀ {X : TopCat} {C : Type v₁} [i
nst : CategoryTheory.Category.{v₂, v₁} C]   [inst_1 : CategoryTheory.HasSheafify
 (Opens.grothendieckTopology …
· 使用定理 `TopCat.instAdditivePresheafStalkFunctor`：∀ {X : TopCat} (p₀ : ↑X) {C : T
ype v} [inst : CategoryTheory.Category.{u, v} C] [inst_1 : CategoryTheory.Abelia
n C]   [inst_2 : CategoryTheo…
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `CategoryTheory.Limits.isZero_zero`：isZero_zero : IsZero (0 : C)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso`：isIso_iff_stalkFunctor_m
ap_iso {F G : Sheaf C X} (f : F ⟶ G) : IsIso f ↔ forall x : X, IsIso ((stalkFunc
tor C x).map f.1)
· 使用定理 `CategoryTheory.Limits.isIso_of_source_target_iso_zero`：isIso_of_source_t
arget_iso_zero {X Y : C} (f : X ⟶ Y) (i : X ≅ 0) (j : Y ≅ 0) : IsIso f
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
A sheaf is zero if and only if its stalks are all zero.
-/
lemma isZero_iff_stalkFunctor_obj_isZero (F : Sheaf C X) :
    IsZero F ↔ ∀ x : X, IsZero ((forget C X ⋙ stalkFunctor C x).obj F) := by
  refine ⟨fun h _ => Functor.map_isZero _ h, ?_⟩
  intro h
  let f : F ⟶ 0 := (isZero_zero (Sheaf C X)).from_ F
  have : IsIso f := by
    rw [Presheaf.isIso_iff_stalkFunctor_map_iso]
    exact fun x => isIso_of_source_target_iso_zero _ (h x).isoZero
      ((forget C X ⋙ stalkFunctor C x).map_isZero (isZero_zero _)).isoZero
  exact (isZero_zero _).of_iso (asIso f)

include instCC in
/-- Exactness can be checked on stalks for complexes of sheaves. -/
/-
**TopCat.Sheaf.exact_iff_stalkFunctor_map_exact** 是 Mathlib 中的一个定理，位于命名空间 `TopCa
t.Sheaf`。
形式化陈述：exact_iff_stalkFunctor_map_exact (S : ShortComplex (Sheaf C X)) : S.Exact 
↔ forall x : X, (S.map (forget C X ⋙ stalkFunctor C x)).Exact
参数：S : ShortComplex (Sheaf C X)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instHasSheafifyOfPreservesLimitsForgetOfHasFiniteLimitsOf
SmallOppositeCover`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (J 
: CategoryTheory.GrothendieckTopology C) (D : Type w)   [inst_1 : CategoryTheory
…
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.instHasLimitsOfShapeOfHasLimitsOfSize`：∀ {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTh
eory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.hasColimitsOfShape_of_has_filtered_colimits`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C]   [CategoryTheory.Limits.Has
FilteredColimitsOfSize.{w', w, v, u} C] (I : Type w)   …
· 使用定理 `CategoryTheory.Limits.hasFilteredColimitsOfSize_of_hasColimitsOfSize`：∀ 
{C : Type u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.Ha
sColimitsOfSize.{w', w, v, u} C],   CategoryTheory.Limits.…
· 使用定理 `CategoryTheory.isCofiltered_of_directed_ge_nonempty`：∀ (α : Type u) [ins
t : Preorder α] [IsCodirectedOrder α] [Nonempty α], CategoryTheory.IsCofiltered 
α
· 使用定理 `SemilatticeInf.instIsCodirectedOrder`：∀ {α : Type u_1} [inst : Semilatti
ceInf α], IsCodirectedOrder α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `CategoryTheory.Limits.PreservesFilteredColimitsOfSize.preserves_filtered
_colimits`：∀ {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type
 u₂} {inst_1 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.reflectsIsomorphisms_of_reflectsMonomorphisms_of_reflects
Epimorphisms`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {D 
: Type u_2}   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] [CategoryThe…
· 使用定理 `CategoryTheory.balanced_of_strongMonoCategory`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] [CategoryTheory.StrongMonoCategory C],   Categor
yTheory.Balanced C
· 使用定理 `CategoryTheory.strongMonoCategory_of_regularMonoCategory`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] [CategoryTheory.IsRegularMonoCateg
ory C],   CategoryTheory.StrongMonoCategory C
· 使用定理 `CategoryTheory.regularMonoCategoryOfNormalMonoCategory`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Limits.HasZ
eroMorphisms C]   [CategoryTheory.IsNormalMo…
· 使用定理 `CategoryTheory.Abelian.toIsNormalMonoCategory`：∀ {C : Type u} {inst : Ca
tegoryTheory.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryThe
ory.IsNormalMonoCategory C
· 使用定理 `CategoryTheory.Functor.reflectsMonomorphisms_of_faithful`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTh
eory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.instFaithfulForget`：∀ (C : Type u_1) [inst : CategoryTheo
ry.Category.{v_1, u_1} C] {FC : outParam (C → C → Type u_2)}   {CC : outParam (C
 → Type w)} [inst_1 : o…
· 使用定理 `CategoryTheory.Functor.reflectsEpimorphisms_of_faithful`：∀ {C : Type u₁}
 [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryThe
ory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfSize.preservesLimitsOfShape`：∀ {C
 : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : 
CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.hasFiniteLimits_of_hasCountableLimits`：∀ (C : Type
 u_1) [inst : CategoryTheory.Category.{v_1, u_1} C] [CategoryTheory.Limits.HasCo
untableLimits C],   CategoryTheory.Limits.HasFini…
· 使用定理 `CategoryTheory.Limits.hasCountableLimits_of_hasLimits`：∀ (C : Type u_1) 
[inst : CategoryTheory.Category.{v_1, u_1} C] [CategoryTheory.Limits.HasLimits C
],   CategoryTheory.Limits.HasCountableLimi…
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `TopCat.Sheaf.instAdditivePresheafForget`：∀ {X : TopCat} {C : Type v₁} [i
nst : CategoryTheory.Category.{v₂, v₁} C]   [inst_1 : CategoryTheory.HasSheafify
 (Opens.grothendieckTopology …
· 使用定理 `TopCat.instAdditivePresheafStalkFunctor`：∀ {X : TopCat} (p₀ : ↑X) {C : T
ype v} [inst : CategoryTheory.Category.{u, v} C] [inst_1 : CategoryTheory.Abelia
n C]   [inst_2 : CategoryTheo…
· 使用定理 `CategoryTheory.Functor.instAdditiveComp`：∀ {C : Type u_1} {D : Type u_2}
 [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Catego
ry.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用引理 `CategoryTheory.Functor.exact_tfae`：exact_tfae : List.TFAE [ forall (S : 
ShortComplex C), S.ShortExact -> (S.map F).ShortExact, forall (S : ShortComplex 
C), S.Exact -> (S.map F…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.Functor.preservesHomologyOfExact`：∀ {C : Type u_1} {D : T
ype u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheor
y.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `TopCat.Sheaf.instPreservesFiniteLimitsCompPresheafForgetStalkFunctor`：∀ 
{C : Type v} [inst : CategoryTheory.Category.{u, v} C] [inst_1 : CategoryTheory.
Limits.HasColimits C]   [CategoryTheory.Limits.HasLimits C…
（共 46 条，此处仅展示前 30 条）

--- 原说明 ---
Exactness can be checked on stalks for complexes of sheaves.
-/
theorem exact_iff_stalkFunctor_map_exact (S : ShortComplex (Sheaf C X)) :
    S.Exact ↔ ∀ x : X, (S.map (forget C X ⋙ stalkFunctor C x)).Exact := by
  constructor
  · intro h x
    have := (forget C X ⋙ stalkFunctor C x).exact_tfae.out 2 1
    exact this.mp inferInstance S h
  intro h
  simp_rw [ShortComplex.exact_iff_isZero_homology] at h
  rw [ShortComplex.exact_iff_isZero_homology, isZero_iff_stalkFunctor_obj_isZero S.homology]
  exact fun x => (h x).of_iso
    (ShortComplex.mapHomologyIso S (forget C X ⋙ stalkFunctor C x)).symm

end Sheaf

end TopCat

