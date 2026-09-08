/-
Copyright (c) 2026 Brian Nugent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Nugent
-/

module

public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.Topology.Sheaves.AddCommGrpCat
public import Mathlib.Topology.Sheaves.LocallySurjective

/-!
# Flasque Sheaves

We define and prove basic properties about flasque sheaves on topological spaces.

## Main definition

* `TopCat.Sheaf.IsFlasque`: A sheaf is flasque if all of the restriction morphisms are epimorphisms.

## Main results

* `TopCat.Sheaf.IsFlasque.epi_of_shortExact`: Given a short exact sequence of sheaves,
  `0 ⟶ 𝓕 ⟶ 𝓖 ⟶ 𝓗 ⟶ 0`, if `𝓕` is flasque then `𝓖(U) ⟶ 𝓗(U)` is surjective, for any open `U`.

* `TopCat.Sheaf.IsFlasque.of_shortExact_of_isFlasque₁₂ `: Given a short exact sequence of
  sheaves, `0 ⟶ 𝓕 ⟶ 𝓖 ⟶ 𝓗 ⟶ 0`, if `𝓕` and `𝓖` are flasque, then `𝓗` is flasque.

-/

public section

universe u v w

open TopCat TopologicalSpace Opposite CategoryTheory Presheaf Limits
open scoped AlgebraicGeometry

variable {X : TopCat.{u}}

namespace TopCat

namespace Presheaf

variable {C : Type v} [Category.{w} C] (F : Presheaf C X)

/-- A sheaf is flasque if all of the restriction morphisms are epimorphisms. -/
/-
**TopCat.Presheaf.IsFlasque** 是 Mathlib 中的一个归纳类型，位于命名空间 `TopCat.Presheaf`。
形式化陈述：{X : TopCat} → {C : Type v} → [inst : CategoryTheory.Category.{w, v} C] → 
TopCat.Presheaf C X → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A sheaf is flasque if all of the restriction morphisms are epimorphisms.
-/
class IsFlasque : Prop where
  epi : ∀ {U V : (Opens X)ᵒᵖ} (i : U ⟶ V), Epi (F.map i)

namespace IsFlasque

attribute [instance low] IsFlasque.epi

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**TopCat.Presheaf.IsFlasque.pushforward_isFlasque** 是 Mathlib 中的一个实例，位于命名空间 `Top
Cat.Presheaf.IsFlasque`。
形式化陈述：pushforward_isFlasque {Y : TopCat.{u}} [IsFlasque F] (f : X ⟶ Y) : IsFlasq
ue (f _* F) where epi {U V} i
参数：f : X ⟶ Y。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `TopCat.Presheaf.IsFlasque.epi`：∀ {X : TopCat} {C : Type v} {inst : Categ
oryTheory.Category.{w, v} C} {F : TopCat.Presheaf C X} [self : F.IsFlasque]   {U
 V : (TopologicalSp…
-/
instance pushforward_isFlasque {Y : TopCat.{u}} [IsFlasque F] (f : X ⟶ Y) :
    IsFlasque (f _* F) where
  epi {U V} i := by
    simp only [pushforward_obj_obj, pushforward_obj_map]
    infer_instance

end IsFlasque

end Presheaf

namespace Sheaf

/-- A sheaf is flasque if it is flasque as a presheaf -/
/-
**TopCat.Sheaf.IsFlasque** 是 Mathlib 中的一个缩写定义，位于命名空间 `TopCat.Sheaf`。
形式化陈述：IsFlasque {C : Type v} [Category.{w} C] (F : Sheaf C X)
参数：F : Sheaf C X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A sheaf is flasque if it is flasque as a presheaf
-/
abbrev IsFlasque {C : Type v} [Category.{w} C] (F : Sheaf C X) := Presheaf.IsFlasque F.obj

namespace IsFlasque

/-
**TopCat.Sheaf.IsFlasque.pushforward_isFlasque** 是 Mathlib 中的一个实例，位于命名空间 `TopCat
.Sheaf.IsFlasque`。
形式化陈述：pushforward_isFlasque {C : Type v} [Category.{w} C] {Y : TopCat.{u}} (F : 
Sheaf C X) [IsFlasque F] (f : X ⟶ Y) : IsFlasque ((pushforward C f).obj F)
参数：F : Sheaf C X；f : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance pushforward_isFlasque {C : Type v} [Category.{w} C] {Y : TopCat.{u}} (F : Sheaf C X)
    [IsFlasque F] (f : X ⟶ Y) : IsFlasque ((pushforward C f).obj F) :=
  Presheaf.IsFlasque.pushforward_isFlasque F.1 f

variable {U : Opens X} {F G : Sheaf AddCommGrpCat X} (g : F ⟶ G) (s : G.obj.obj (op U))

/-- Given a morphism of sheaves `g: F ⟶ G` and a section `s` of `G(U)`, `Under g s` is comprised of
an open `V` and a section of `F(V)` that maps to `s |_ V` via `g`. -/
/-
**TopCat.Sheaf.IsFlasque.Under** 是 Mathlib 中的一个缩写定义，位于命名空间 `TopCat.Sheaf.IsFlasq
ue`。
形式化陈述：Under
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a morphism of sheaves `g: F ⟶ G` and a section `s` of `G(U)`, `Under g s` 
is comprised of
an open `V` and a section of `F(V)` that maps to `s |_ V` via `g`.
-/
abbrev Under := StructuredArrow ⟨op U, s⟩ (Functor.whiskerRight g.hom
  (CategoryTheory.forget AddCommGrpCat.{u})).mapElements

set_option backward.isDefEq.respectTransparency.types false in
/- The next lemma proves that the relation `fun x y ↦ Nonempty (y ⟶ x)` on `Under g s`
satisfies the requirements for applying Zorn's lemma -/
/-
**TopCat.Sheaf.IsFlasque.structured_arrows_elements_sheaf_chains_bounded** 是 Mat
hlib 中的一个引理，位于命名空间 `TopCat.Sheaf.IsFlasque`。
形式化陈述：structured_arrows_elements_sheaf_chains_bounded (c : Set (Under g s)) (h :
 IsChain (fun x y => Nonempty (y ⟶ x)) c) : exists ub, forall a in c, Nonempty (
ub ⟶ a)
参数：c : Set (Under g s)；h : IsChain (fun x y => Nonempty (y ⟶ x)) c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopCat.Sheaf.existsUnique_gluing`：∀ {C : Type u_1} [inst : CategoryTheor
y.Category.{v_1, u_1} C] {FC : C → C → Type u_2} {CC : C → Type u_3}   [inst_1 :
 (X Y : C) → FunLike (…
· 使用定理 `AddCommGrpCat.hasLimits`：CategoryTheory.Limits.HasLimits AddCommGrpCat
· 使用定理 `AddCommGrpCat.forget_reflects_isos`：(CategoryTheory.forget AddCommGrpCat
).ReflectsIsomorphisms
· 使用定理 `AddCommGrpCat.forget_preservesLimits`：CategoryTheory.Limits.PreservesLim
its (CategoryTheory.forget AddCommGrpCat)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.CategoryOfElements.map_snd`：map_snd {F : C ⥤ Type w} {p q
 : F.Elements} (f : p ⟶ q) : (F.map f.val) p.2 = q.2
· 使用定理 `CategoryTheory.Functor.map_comp_apply`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, 
u₂} D]   (self : CategoryTh…
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `CategoryTheory.leOfHom`：leOfHom {x y : X} (h : x ⟶ y) : x <= y
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
· 使用定理 `TopCat.Sheaf.eq_app_of_locally_eq`：∀ {C : Type u_1} [inst : CategoryTheo
ry.Category.{v_1, u_1} C] {FC : C → C → Type u_2} {CC : C → Type u_3}   [inst_1 
: (X Y : C) → FunLike (…

--- 原说明 ---
The next lemma proves that the relation `fun x y ↦ Nonempty (y ⟶ x)` on `Under g
 s`
satisfies the requirements for applying Zorn's lemma
-/
lemma structured_arrows_elements_sheaf_chains_bounded (c : Set (Under g s))
    (h : IsChain (fun x y ↦ Nonempty (y ⟶ x)) c) : ∃ ub, ∀ a ∈ c, Nonempty (ub ⟶ a) := by
  let f : c → (Opens X) := fun x => x.1.right.1.unop
  obtain ⟨t, ht, _⟩ : ∃! s_1, IsGluing F.obj f (fun x => x.val.right.2) s_1 := by
    refine Sheaf.existsUnique_gluing F _ _ (fun i j ↦ ?_)
    obtain (rfl | h₁ | h₁) : i = j ∨ Nonempty (i.val ⟶ j.val) ∨ Nonempty (j.val ⟶ i.val) := by
      grind [Subtype.ext_iff, h i.property j.property]
    · rfl
    all_goals
      rw [← CategoryOfElements.map_snd h₁.some.2]
      dsimp
      rw [← Functor.map_comp_apply]
      rfl
  have le₁ : iSup f ≤ U := iSup_le <| fun j => leOfHom j.1.hom.1.unop
  have le₂ : ∀ i, i ∈ c → unop i.right.1 ≤ iSup f := fun i hi ↦ le_iSup f ⟨i, hi⟩
  use StructuredArrow.mk (CategoryOfElements.homMk _ _ (homOfLE le₁).op (eq_app_of_locally_eq ht
      (fun i ↦ leOfHom i.1.hom.1.unop) (fun i ↦ (CategoryOfElements.map_snd i.1.hom).symm)).symm :
      ⟨op U, s⟩ ⟶ (Functor.whiskerRight g.hom
      (CategoryTheory.forget AddCommGrpCat)).mapElements.obj ⟨op (iSup f), t⟩)
  exact fun i hi => Nonempty.intro (StructuredArrow.homMk (CategoryOfElements.homMk _ _
    (homOfLE (le₂ i hi)).op (ht ⟨i, hi⟩)) (by cat_disch))

set_option backward.isDefEq.respectTransparency false in
/-- Given a short exact sequence of sheaves, `0 ⟶ 𝓕 ⟶ 𝓖 ⟶ 𝓗 ⟶ 0`, if `𝓕` is flasque then
`𝓖(U) ⟶ 𝓗(U)` is surjective, for any open `U`. -/
/-
**TopCat.Sheaf.IsFlasque.epi_of_shortExact** 是 Mathlib 中的一个定理，位于命名空间 `TopCat.She
af.IsFlasque`。
形式化陈述：epi_of_shortExact {S : ShortComplex (Sheaf AddCommGrpCat X)} (hS : S.Short
Exact) [IsFlasque S.X₁] : Epi (S.g.1.app (op U))
参数：Sheaf AddCommGrpCat X；hS : S.ShortExact。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instHasSheafifyOfPreservesLimitsForgetOfHasFiniteLimitsOf
SmallOppositeCover`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (J 
: CategoryTheory.GrothendieckTopology C) (D : Type w)   [inst_1 : CategoryTheory
…
· 使用定理 `AddCommGrpCat.hasLimit`：∀ {J : Type v} [inst : CategoryTheory.Category.{
w, v} J] (F : CategoryTheory.Functor J AddCommGrpCat)   [Small.{u, max u v} ↑(F.
comp (Catego…
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `AddCommGrpCat.hasColimitsOfShape`：∀ {J : Type u} [inst : CategoryTheory.
Category.{v, u} J] [Small.{w, u} J],   CategoryTheory.Limits.HasColimitsOfShape 
J AddCommGrpCat
· 使用定理 `CategoryTheory.Limits.PreservesFilteredColimitsOfSize.preserves_filtered
_colimits`：∀ {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type
 u₂} {inst_1 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits`：Categor
yTheory.Limits.PreservesFilteredColimits (CategoryTheory.forget AddCommGrpCat)
· 使用定理 `CategoryTheory.isCofiltered_of_directed_ge_nonempty`：∀ (α : Type u) [ins
t : Preorder α] [IsCodirectedOrder α] [Nonempty α], CategoryTheory.IsCofiltered 
α
· 使用定理 `SemilatticeInf.instIsCodirectedOrder`：∀ {α : Type u_1} [inst : Semilatti
ceInf α], IsCodirectedOrder α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `AddCommGrpCat.forget_reflects_isos`：(CategoryTheory.forget AddCommGrpCat
).ReflectsIsomorphisms
· 使用定理 `AddCommGrpCat.forget_preservesLimitsOfShape`：∀ {J : Type v} [inst : Cate
goryTheory.Category.{w, v} J] [Small.{u, v} J],   CategoryTheory.Limits.Preserve
sLimitsOfShape J (CategoryTheory.…
· 使用定理 `AddCommGrpCat.forget_preservesLimits`：CategoryTheory.Limits.PreservesLim
its (CategoryTheory.forget AddCommGrpCat)
· 使用定理 `CategoryTheory.Limits.hasFiniteLimits_of_hasCountableLimits`：∀ (C : Type
 u_1) [inst : CategoryTheory.Category.{v_1, u_1} C] [CategoryTheory.Limits.HasCo
untableLimits C],   CategoryTheory.Limits.HasFini…
· 使用定理 `CategoryTheory.Limits.hasCountableLimits_of_hasLimits`：∀ (C : Type u_1) 
[inst : CategoryTheory.Category.{v_1, u_1} C] [CategoryTheory.Limits.HasLimits C
],   CategoryTheory.Limits.HasCountableLimi…
· 使用定理 `AddCommGrpCat.hasLimits`：CategoryTheory.Limits.HasLimits AddCommGrpCat
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `AddCommGrpCat.epi_iff_surjective`：∀ {A B : AddCommGrpCat} (f : A ⟶ B), C
ategoryTheory.Epi f ↔ Function.Surjective ⇑(CategoryTheory.ConcreteCategory.hom 
f)
· 使用定理 `exists_maximal_of_chains_bounded`：exists_maximal_of_chains_bounded (h : 
forall c, IsChain r c -> exists ub, forall a in c, a ≺ ub) (trans : forall {a b 
c}, a ≺ b -> b ≺ c -> …
· 使用引理 `TopCat.Sheaf.IsFlasque.structured_arrows_elements_sheaf_chains_bounded`：
structured_arrows_elements_sheaf_chains_bounded (c : Set (Under g s)) (h : IsCha
in (fun x y => Nonempty (y ⟶ x)) c) : exists ub, forall a in…
· 使用定理 `CategoryTheory.leOfHom`：leOfHom {x y : X} (h : x ⟶ y) : x <= y
· 使用定理 `CategoryTheory.CategoryOfElements.map_snd`：map_snd {F : C ⥤ Type w} {p q
 : F.Elements} (f : p ⟶ q) : (F.map f.val) p.2 = q.2
· 使用定理 `TopCat.Sheaf.isLocallySurjective_iff_epi`：TopCat.Sheaf.isLocallySurjecti
ve_iff_epi {X : TopCat.{v}} {C : Type u} [Category.{v} C] {FC : C -> C -> Type*}
 {CC : C -> Type v} [forall X …
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
· 使用定理 `CategoryTheory.hasSheafCompose_of_preservesMulticospan`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {A : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} A]   {B : Type u₃} [ins…
· 使用定理 `CategoryTheory.preservesLimit_of_createsLimit_and_hasLimit`：∀ {C : Type 
u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Category
Theory.Category.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `CategoryTheory.GrothendieckTopology.instWEqualsLocallyBijectiveOfHasWeak
SheafifyOfHasSheafComposeOfPreservesSheafificationOfReflectsIsomorphismsForget`：
∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (J : CategoryTheory.Gro
thendieckTopology C) {D : Type w}   [inst_1 : CategoryTheory…
· 使用定理 `CategoryTheory.instHasWeakSheafifyOfHasSheafify`：∀ {C : Type u₁} [inst :
 CategoryTheory.Category.{v₁, u₁} C] (J : CategoryTheory.GrothendieckTopology C)
 (A : Type u₂)   [inst_1 : CategoryTh…
（共 77 条，此处仅展示前 30 条）

--- 原说明 ---
Given a short exact sequence of sheaves, `0 ⟶ 𝓕 ⟶ 𝓖 ⟶ 𝓗 ⟶ 0`, if `𝓕` is flasque 
then
`𝓖(U) ⟶ 𝓗(U)` is surjective, for any open `U`.
-/
theorem epi_of_shortExact {S : ShortComplex (Sheaf AddCommGrpCat X)} (hS : S.ShortExact)
    [IsFlasque S.X₁] : Epi (S.g.1.app (op U)) := by
  refine (AddCommGrpCat.epi_iff_surjective _).mpr (fun s ↦ ?_)
  -- We want to find a preimage of `s` by `S.g`.
  -- We apply Zorn's lemma to obtain a term `t` of `Under S.g s` that is maximal.
  obtain ⟨t, ht⟩ := exists_maximal_of_chains_bounded
    (structured_arrows_elements_sheaf_chains_bounded S.g s)
    (fun ⟨f⟩ ⟨g⟩ ↦ ⟨g ≫ f⟩)
  have tle : t.right.1.unop ≤ U := leOfHom t.hom.1.unop
  have tcomp : s |_ t.right.1.unop = S.g.hom.app t.right.1 t.right.2 :=
      CategoryOfElements.map_snd t.hom
  -- We get a section `t.right.2` of `S.g` defined on an open subset `t.right.1.unop` of `U`,
  -- that is sent to the restriction of `s` by `S.g`.
  have : U ≤ t.right.1.unop := by
  -- Prove that the set of definition of `t.right.2` contains `U`.
    intro x hx
    have := (isLocallySurjective_iff_epi S.g).mpr hS.epi_g
    -- We use local surjectivity to find a section `t₁` of `S.X₂` on a neighborhood `W` of `x`
    -- that maps to `s |_ W` by `S.g`.
    obtain ⟨W, Wle, ⟨t₁, ht₁⟩, hW⟩ := (isLocallySurjective_iff S.g.hom).mp this U s x hx
    --`t.right.2` and `t₁` need not agree on their overlap so we need to deal with their
    -- difference `t₂`
    let t₂ := t.right.2 |_ (t.right.1.unop ⊓ W) - t₁ |_ (t.right.1.unop ⊓ W)
    have : (S.g.hom.app (op (t.right.1.unop ⊓ W))) t₂ = 0 := by
      simp [map_restrict, ← tcomp, restrict_restrict, ht₁, t₂]
    -- Since `S` is exact and `t₂` maps to zero, we can lift it to a section `t₃` of `S.X₁`
    obtain ⟨t₃, ht₃⟩ := Sheaf.sections_exact_of_left_exact hS.1 hS.2 t₂ this
    -- Using that `S.X₁` is flasque, we can lift `t₃` to a section on `W`.
    obtain ⟨t₄, (ht₄ : t₄ |_ (t.right.1.unop ⊓ W) = t₃)⟩ := (AddCommGrpCat.epi_iff_surjective
      (S.X₁.obj.map (homOfLE inf_le_right).op)).mp inferInstance t₃
    let f : Fin 2 → Opens X := ![t.right.1.unop, W]
    let sf : (i : Fin 2) → S.X₂.obj.obj (op (f i))
    | 0 => t.right.2
    | 1 => t₁ + (S.f.hom.app (op W)) t₄
    have : sf 0 |_ (t.right.1.unop ⊓ W) = sf 1 |_ (t.right.1.unop ⊓ W) := by
      dsimp [sf, f]
      simp only [restrict_sum, ← map_restrict, ht₄, ht₃, t₂, add_sub_cancel]
    -- We glue `t.right.2` and `t₁ + (S.f.hom.app (op W)) t₄` together to form `t₅`
    obtain ⟨t₅, ht₅, _⟩ : ∃! t₅, IsGluing S.X₂.obj f sf t₅ := by
      apply Sheaf.existsUnique_gluing
      simp only [IsCompatible, Fin.forall_fin_two]
      refine ⟨⟨rfl, this⟩, Eq.symm ?_, rfl⟩
      apply_fun (fun s ↦ restrictOpen s (W ⊓ t.right.1.unop) (le_of_eq (inf_comm _ _))) at this
      rw [restrict_restrict, restrict_restrict] at this
      exact this
    have le : iSup f ≤ U := iSup_le_iff.mpr (Fin.forall_fin_two.mpr ⟨tle, Wle⟩)
    -- We upgrade `t₅` to an object in `Under S.g s` that is defined on `t.right.1.unop ⊔ W`.
    let t₆ : Under S.g s :=
      StructuredArrow.mk (S := ⟨op U, s⟩)
        (T := (Functor.whiskerRight S.g.hom (CategoryTheory.forget AddCommGrpCat)).mapElements)
        (Y := ⟨op (iSup f), t₅⟩) <| CategoryOfElements.homMk _ _ (homOfLE le).op (by
          refine (eq_app_of_locally_eq ht₅ (by rw [Fin.forall_fin_two]; exact ⟨tle, Wle⟩) ?_).symm
          rw [Fin.forall_fin_two]
          refine ⟨tcomp.symm, ?_⟩
          simp only [Fin.isValue, map_add, homOfLE_leOfHom, sf, f]
          have : (S.f.hom.app (op W) ≫ S.g.hom.app (op W)) = 0 := by
            rw [← NatTrans.comp_app, ← ObjectProperty.FullSubcategory.comp_hom, S.zero]
            rfl
          simp [← CategoryTheory.comp_apply, this, ht₁]
          rfl)
    -- We prove that `t₆` is bigger than `t` for the preorder used on `Under S.g s`.
    have : Nonempty (t₆ ⟶ t) := Nonempty.intro (StructuredArrow.homMk (CategoryOfElements.homMk _ _
      (homOfLE (le_iSup f 0)).op (ht₅ 0)) (by cat_disch))
    exact leOfHom ((ht t₆) this).some.right.1.unop ((le_iSup f 1) hW)
  exact ⟨t.right.2 |_ U, by simp [map_restrict, ← tcomp, restrict_restrict]⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- Given a short exact sequence of sheaves, `0 ⟶ 𝓕 ⟶ 𝓖 ⟶ 𝓗 ⟶ 0`, if `𝓕` and `𝓖` are flasque,
then `𝓗` is flasque. -/
/-
**TopCat.Sheaf.IsFlasque.of_shortExact_of_isFlasque** 是 Mathlib 中的一个定理，位于命名空间 `T
opCat.Sheaf.IsFlasque`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a short exact sequence of sheaves, `0 ⟶ 𝓕 ⟶ 𝓖 ⟶ 𝓗 ⟶ 0`, if `𝓕` and `𝓖` are
 flasque,
then `𝓗` is flasque.
-/
theorem of_shortExact_of_isFlasque₁₂ {S : ShortComplex (Sheaf AddCommGrpCat X)}
    (hS : S.ShortExact) [IsFlasque S.X₁] [IsFlasque S.X₂] : IsFlasque S.X₃ where
  epi {U V} i := by
    have : Epi (S.g.1.app U ≫ S.X₃.obj.map i) := by
      rw [← S.g.hom.naturality i]
      exact CategoryTheory.epi_comp' inferInstance (epi_of_shortExact hS)
    exact CategoryTheory.epi_of_epi (S.g.1.app U) (S.X₃.obj.map i)

end TopCat.Sheaf.IsFlasque

set_option backward.defeqAttrib.useBackward true in
/--
If the unique map from `A` to the terminal object is an epimorphism, then the skyscraper sheaf
valued in `A` supported at an arbitrary point is a flasque sheaf.
-/
/-
**isFlasque_skyscraperSheaf_of_epi_from** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {X : TopCat} (p₀ : ↑X) [inst : (U : TopologicalSpace.Opens ↑X) → Decidab
le (p₀ ∈ U)] {C : Type u_1}   [inst_1 : CategoryTheory.Category.{v_1, u_1} C] (A
 : C) [inst_2 : CategoryTheory.Limits.HasTerminal C]   [CategoryTheory.Epi (Cate
goryTheory.Limits.terminalIsTerminal.from A)], (skyscraperSheaf p₀ A).IsFlasque
参数：p₀ : ↑X；U : TopologicalSpace.Opens ↑X；p₀ ∈ U；A : C；CategoryTheory.Limits.term
inalIsTerminal.from A；skyscraperSheaf p₀ A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `CategoryTheory.instEffectiveEpiOfIsIso`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],  
 CategoryTheory.EffectiveEpi…
· 使用定理 `CategoryTheory.instIsIsoEqToHom`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {X Y : C} (h : X = Y),   CategoryTheory.IsIso (CategoryTheo
ry.eqToHom h)
· 使用引理 `CategoryTheory.Limits.isIso_of_isTerminal`：isIso_of_isTerminal {X Y : C}
 (hX : IsTerminal X) (hY : IsTerminal Y) (f : X ⟶ Y) : IsIso f

--- 原说明 ---
If the unique map from `A` to the terminal object is an epimorphism, then the sk
yscraper sheaf
valued in `A` supported at an arbitrary point is a flasque sheaf.
-/
theorem isFlasque_skyscraperSheaf_of_epi_from {X : TopCat} (p₀ : ↑X)
    [(U : Opens ↑X) → Decidable (p₀ ∈ U)] {C : Type*} [Category* C] (A : C) [HasTerminal C]
    [Epi <| terminalIsTerminal.from A] :
    (skyscraperSheaf p₀ A).IsFlasque where
  epi {U V} r := by
    by_cases h1 : p₀ ∈ unop U
    · by_cases h2 : p₀ ∈ unop V
      · simp_all only [skyscraperSheaf_obj_obj, skyscraperSheaf_obj_map, ↓reduceDIte]
        infer_instance
      · simp
        grind
    · have h2 : p₀ ∉ unop V := fun hV => h1 (r.unop.le hV)
      have := isIso_of_isTerminal (isTerminalSkyscraperSheafObjObjOfNotMem h1)
        (isTerminalSkyscraperSheafObjObjOfNotMem h2) ((skyscraperSheaf p₀ A).obj.map r)
      infer_instance

/--
If the target category has a zero object, then any skyscraper sheaf valued in this category is a
flasque sheaf.
-/
/-
**isFlasque_skyscraperSheaf_of_hasZeroObject** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {X : TopCat} (p₀ : ↑X) [inst : (U : TopologicalSpace.Opens ↑X) → Decidab
le (p₀ ∈ U)] {C : Type u_1}   [inst_1 : CategoryTheory.Category.{v_1, u_1} C] (A
 : C) [inst_2 : CategoryTheory.Limits.HasZeroObject C],   (skyscraperSheaf p₀ A)
.IsFlasque
参数：p₀ : ↑X；U : TopologicalSpace.Opens ↑X；p₀ ∈ U；A : C；skyscraperSheaf p₀ A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isFlasque_skyscraperSheaf_of_epi_from`：∀ {X : TopCat} (p₀ : ↑X) [inst : 
(U : TopologicalSpace.Opens ↑X) → Decidable (p₀ ∈ U)] {C : Type u_1}   [inst_1 :
 CategoryTheory.Category.{v…
· 使用定理 `CategoryTheory.Limits.HasZeroObject.hasTerminal`：∀ {C : Type u} [inst : 
CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasZeroObject C],   Cat
egoryTheory.Limits.HasTerminal C
· 使用定理 `CategoryTheory.instEpiFromTerminalIsTerminal`：∀ {C : Type u_1} [inst : C
ategoryTheory.Category.{v_1, u_1} C] (A : C) [inst_1 : CategoryTheory.Limits.Has
ZeroObject C],   CategoryTheory.Ep…

--- 原说明 ---
If the target category has a zero object, then any skyscraper sheaf valued in th
is category is a
flasque sheaf.
-/
theorem isFlasque_skyscraperSheaf_of_hasZeroObject {X : TopCat} (p₀ : ↑X)
    [(U : Opens ↑X) → Decidable (p₀ ∈ U)] {C : Type*} [Category* C] (A : C) [HasZeroObject C] :
    (skyscraperSheaf p₀ A).IsFlasque := isFlasque_skyscraperSheaf_of_epi_from p₀ A
