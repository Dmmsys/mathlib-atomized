/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Joël Riou
-/
module

public import Mathlib.CategoryTheory.Sites.Subsheaf
public import Mathlib.CategoryTheory.Sites.CompatibleSheafification
public import Mathlib.CategoryTheory.Sites.LocallyInjective
public import Mathlib.CategoryTheory.ShrinkYoneda
/-!

# Locally surjective morphisms

## Main definitions

- `IsLocallySurjective` : A morphism of presheaves valued in a concrete category is locally
  surjective with respect to a Grothendieck topology if every section in the target is locally
  in the set-theoretic image, i.e. the image sheaf coincides with the target.

## Main results

- `Presheaf.isLocallySurjective_toSheafify`: `toSheafify` is locally surjective.
- `Sheaf.isLocallySurjective_iff_epi`: a morphism of sheaves of types is locally
  surjective iff it is epi.

-/

@[expose] public section


universe w v u v' u' w'

open Opposite CategoryTheory CategoryTheory.GrothendieckTopology CategoryTheory.Functor Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

variable {A : Type u'} [Category.{v'} A] {FA : A -> A -> Type*} {CA : A -> Type w'}
variable [forall X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{w'} A FA]

namespace Presheaf

/-- Given `f : F ⟶ G`, a morphism between presieves, and `s : G.obj (op U)`, this is the sieve
of `U` consisting of the `i : V ⟶ U` such that `s` restricted along `i` is in the image of `f`. -/
@[simps -isSimp]
/--
Definition of `imageSieve` / `imageSieve` 的定义

English:
definition imageSieve
  signature: {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G) {U : C} (s : ToType (G.obj (op U)))
  body: exists t : ToType (F.obj (op V)), f.app _ t = G.map i.op s
  downward_closed := by
    rintro V W i ⟨t, ht⟩ j
    refine ⟨F.map j.op t, ?_⟩
    rw [op_comp]; rw [G.map_comp]; rw [ConcreteCategory.comp_apply]; rw [← ht]; rw [NatTrans.naturality_apply f]

中文:
定义 imageSieve
  签名: {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G) {U : C} (s : ToType (G.obj (op U)))
  定义体: exists t : ToType (F.obj (op V)), f.app _ t = G.map i.op s
  downward_closed := by
    rintro V W i ⟨t, ht⟩ j
    refine ⟨F.map j.op t, ?_⟩
    rw [op_comp]; rw [G.map_comp]; rw [ConcreteCategory.comp_apply]; rw [← ht]; rw [NatTrans.naturality_apply f]

Depends on / 依赖: F.obj, G.map, ToType, f.app, i.op
-/
def imageSieve {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G) {U : C} (s : ToType (G.obj (op U))) : Sieve U where
  arrows V i := exists t : ToType (F.obj (op V)), f.app _ t = G.map i.op s
  downward_closed := by
    rintro V W i ⟨t, ht⟩ j
    refine ⟨F.map j.op t, ?_⟩
    rw [op_comp]; rw [G.map_comp]; rw [ConcreteCategory.comp_apply]; rw [← ht]; rw [NatTrans.naturality_apply f]

/--
lemma `pullback_imageSieve` / 引理 `pullback_imageSieve`

English:
lemma pullback_imageSieve
  proof: by
  ext W g
  simp [imageSieve]

中文:
引理 pullback_imageSieve
  证明: by
  ext W g
  simp [imageSieve]

Depends on / 依赖: imageSieve
-/
lemma pullback_imageSieve
    {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G) {U : C} (s : ToType (G.obj (op U)))
    {V : C} (g : V ⟶ U) :
    (imageSieve f s).pullback g = imageSieve f (G.map g.op s) := by
  ext W g
  simp [imageSieve]

/--
theorem `imageSieve_eq_sieveOfSection` / 定理 `imageSieve_eq_sieveOfSection`

English:
theorem imageSieve_eq_sieveOfSection
  statement: {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G) {U : C}
  proof: rfl

中文:
定理 imageSieve_eq_sieveOfSection
  结论: {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G) {U : C}
  证明: rfl
-/
theorem imageSieve_eq_sieveOfSection {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G) {U : C}
    (s : ToType (G.obj (op U))) :
    imageSieve f s = (Subfunctor.range (whiskerRight f (forget A))).sieveOfSection s :=
  rfl

/--
theorem `imageSieve_whisker_forget` / 定理 `imageSieve_whisker_forget`

English:
theorem imageSieve_whisker_forget
  given: {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G) {U : C} (s : ToType (G.obj (op U)))
  proof: rfl

中文:
定理 imageSieve_whisker_forget
  条件: {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G) {U : C} (s : ToType (G.obj (op U)))
  证明: rfl
-/
theorem imageSieve_whisker_forget {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G) {U : C} (s : ToType (G.obj (op U))) :
    imageSieve (whiskerRight f (forget A)) s = imageSieve f s :=
  rfl

/--
theorem `imageSieve_app` / 定理 `imageSieve_app`

English:
theorem imageSieve_app
  given: {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G) {U : C} (s : ToType (F.obj (op U)))
  proof: by
  ext V i
  simp only [Sieve.top_apply, iff_true, imageSieve_apply]
  exact ⟨F.map i.op s, NatTrans.naturality_apply f i.op s⟩

中文:
定理 imageSieve_app
  条件: {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G) {U : C} (s : ToType (F.obj (op U)))
  证明: by
  ext V i
  simp only [Sieve.top_apply, iff_true, imageSieve_apply]
  exact ⟨F.map i.op s, NatTrans.naturality_apply f i.op s⟩

Depends on / 依赖: F.map, NatTrans, NatTrans.naturality_apply, Sieve.top_apply, i.op, iff_true, imageSieve_apply, naturality_apply, top_apply
-/
theorem imageSieve_app {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G) {U : C} (s : ToType (F.obj (op U))) :
    imageSieve f (f.app _ s) = ⊤ := by
  ext V i
  simp only [Sieve.top_apply, iff_true, imageSieve_apply]
  exact ⟨F.map i.op s, NatTrans.naturality_apply f i.op s⟩

/--
Definition of `localPreimage` / `localPreimage` 的定义

English:
definition localPreimage
  signature: {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G) {U : Cᵒᵖ} (s : ToType (G.obj U))
  body: hg.choose

@[simp]

中文:
定义 localPreimage
  签名: {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G) {U : Cᵒᵖ} (s : ToType (G.obj U))
  定义体: hg.choose

@[simp]

Depends on / 依赖: hg.choose
-/
noncomputable def localPreimage {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G) {U : Cᵒᵖ} (s : ToType (G.obj U))
    {V : C} (g : V ⟶ U.unop) (hg : imageSieve f s g) :
    ToType (F.obj (op V)) :=
  hg.choose

@[simp]
/--
lemma `app_localPreimage` / 引理 `app_localPreimage`

English:
lemma app_localPreimage
  statement: {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G) {U : Cᵒᵖ} (s : ToType (G.obj U))
  proof: hg.choose_spec

中文:
引理 app_localPreimage
  结论: {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G) {U : Cᵒᵖ} (s : ToType (G.obj U))
  证明: hg.choose_spec

Depends on / 依赖: choose_spec, hg.choose_spec
-/
lemma app_localPreimage {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G) {U : Cᵒᵖ} (s : ToType (G.obj U))
    {V : C} (g : V ⟶ U.unop) (hg : imageSieve f s g) :
    f.app _ (localPreimage f s g hg) = G.map g.op s :=
  hg.choose_spec

/--
Definition of `IsLocallySurjective` / `IsLocallySurjective` 的定义

English:
class IsLocallySurjective
  parameters: {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G)
  axioms and operations (1):
    - imageSieve_mem({U : C} (s : ToType (G.obj (op U)))) : imageSieve f s in J U

中文:
类 是LocallySurjective
  参数: {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G)
  公理与运算 (1 个):
    - imageSieve_mem({U : C} (s : ToType (G.obj (op U)))) : imageSieve f s in J U
-/
class IsLocallySurjective {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G) : Prop where
  imageSieve_mem {U : C} (s : ToType (G.obj (op U))) : imageSieve f s in J U

/--
lemma `imageSieve_mem` / 引理 `imageSieve_mem`

English:
lemma imageSieve_mem
  statement: {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G) [IsLocallySurjective J f] {U : Cᵒᵖ}
  proof: IsLocallySurjective.imageSieve_mem _

中文:
引理 imageSieve_mem
  结论: {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G) [是LocallySurjective J f] {U : Cᵒᵖ}
  证明: IsLocallySurjective.imageSieve_mem _

Depends on / 依赖: IsLocallySurjective, IsLocallySurjective.imageSieve_mem, imageSieve_mem
-/
lemma imageSieve_mem {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G) [IsLocallySurjective J f] {U : Cᵒᵖ}
    (s : ToType (G.obj U)) : imageSieve f s in J U.unop :=
  IsLocallySurjective.imageSieve_mem _

instance {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G) [IsLocallySurjective J f] :
    IsLocallySurjective J (whiskerRight f (forget A)) where
  imageSieve_mem s := imageSieve_mem J f s

/--
theorem `isLocallySurjective_iff_range_sheafify_eq_top` / 定理 `isLocallySurjective_iff_range_sheafify_eq_top`

English:
theorem isLocallySurjective_iff_range_sheafify_eq_top
  given: {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G)
  proof: by
  simp only [Subfunctor.ext_iff, funext_iff, Set.ext_iff, Subfunctor.top_obj,
    Set.top_eq_univ, Set.mem_univ, iff_true]
  exact ⟨fun H _ => H.imageSieve_mem, fun H => ⟨H _⟩⟩

中文:
定理 isLocallySurjective_iff_range_sheafify_eq_top
  条件: {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G)
  证明: by
  simp only [Subfunctor.ext_iff, funext_iff, Set.ext_iff, Subfunctor.top_obj,
    Set.top_eq_univ, Set.mem_univ, iff_true]
  exact ⟨fun H _ => H.imageSieve_mem, fun H => ⟨H _⟩⟩

Depends on / 依赖: H.imageSieve_mem, Set.ext_iff, Set.mem_univ, Set.top_eq_univ, Subfunctor, Subfunctor.ext_iff, Subfunctor.top_obj, ext_iff, funext_iff, iff_true, imageSieve_mem, mem_univ, top_eq_univ, top_obj
-/
theorem isLocallySurjective_iff_range_sheafify_eq_top {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G) :
    IsLocallySurjective J f ↔ (Subfunctor.range (whiskerRight f (forget A))).sheafify J = ⊤ := by
  simp only [Subfunctor.ext_iff, funext_iff, Set.ext_iff, Subfunctor.top_obj,
    Set.top_eq_univ, Set.mem_univ, iff_true]
  exact ⟨fun H _ => H.imageSieve_mem, fun H => ⟨H _⟩⟩

/--
theorem `isLocallySurjective_iff_range_sheafify_eq_top'` / 定理 `isLocallySurjective_iff_range_sheafify_eq_top'`

English:
theorem isLocallySurjective_iff_range_sheafify_eq_top'
  given: {F G : Cᵒᵖ ⥤ Type w} (f : F ⟶ G)
  proof: by
  apply isLocallySurjective_iff_range_sheafify_eq_top

中文:
定理 isLocallySurjective_iff_range_sheafify_eq_top'
  条件: {F G : Cᵒᵖ ⥤ 类型 w} (f : F ⟶ G)
  证明: by
  apply isLocallySurjective_iff_range_sheafify_eq_top

Depends on / 依赖: isLocallySurjective_iff_range_sheafify_eq_top
-/
theorem isLocallySurjective_iff_range_sheafify_eq_top' {F G : Cᵒᵖ ⥤ Type w} (f : F ⟶ G) :
    IsLocallySurjective J f ↔ (Subfunctor.range f).sheafify J = ⊤ := by
  apply isLocallySurjective_iff_range_sheafify_eq_top

/--
theorem `isLocallySurjective_iff_whisker_forget` / 定理 `isLocallySurjective_iff_whisker_forget`

English:
theorem isLocallySurjective_iff_whisker_forget
  given: {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G)
  proof: by
  simp only [isLocallySurjective_iff_range_sheafify_eq_top]
  rfl

中文:
定理 isLocallySurjective_iff_whisker_forget
  条件: {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G)
  证明: by
  simp only [isLocallySurjective_iff_range_sheafify_eq_top]
  rfl

Depends on / 依赖: isLocallySurjective_iff_range_sheafify_eq_top
-/
theorem isLocallySurjective_iff_whisker_forget {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G) :
    IsLocallySurjective J f ↔ IsLocallySurjective J (whiskerRight f (forget A)) := by
  simp only [isLocallySurjective_iff_range_sheafify_eq_top]
  rfl

/--
theorem `isLocallySurjective_of_surjective` / 定理 `isLocallySurjective_of_surjective`

English:
theorem isLocallySurjective_of_surjective
  statement: {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G)
  proof: by
    obtain ⟨t, rfl⟩ := H _ s
    rw [imageSieve_app]
    exact J.top_mem _

中文:
定理 isLocallySurjective_of_surjective
  结论: {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G)
  证明: by
    obtain ⟨t, rfl⟩ := H _ s
    rw [imageSieve_app]
    exact J.top_mem _

Depends on / 依赖: J.top_mem, imageSieve_app, top_mem
-/
theorem isLocallySurjective_of_surjective {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G)
    (H : forall U, Function.Surjective (f.app U)) : IsLocallySurjective J f where
  imageSieve_mem {U} s := by
    obtain ⟨t, rfl⟩ := H _ s
    rw [imageSieve_app]
    exact J.top_mem _

/--
Instance `isLocallySurjective_of_iso` / 实例 `isLocallySurjective_of_iso`

English:
instance isLocallySurjective_of_iso
  signature: {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G) [IsIso f]
  body: by
  apply isLocallySurjective_of_surjective
  intro U
  apply Function.Bijective.surjective
  rw [bijective_iff_isIso_ofHom]
  infer_instance

中文:
实例 isLocallySurjective_of_iso
  签名: {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G) [是同构 f]
  定义体: by
  apply isLocallySurjective_of_surjective
  intro U
  apply Function.Bijective.surjective
  rw [bijective_iff_isIso_ofHom]
  infer_instance

Depends on / 依赖: Bijective, Function, Function.Bijective.surjective, bijective_iff_isIso_ofHom, infer_instance, isLocallySurjective_of_surjective, surjective
-/
instance isLocallySurjective_of_iso {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G) [IsIso f] :
    IsLocallySurjective J f := by
  apply isLocallySurjective_of_surjective
  intro U
  apply Function.Bijective.surjective
  rw [bijective_iff_isIso_ofHom]
  infer_instance

/--
Instance `isLocallySurjective_comp` / 实例 `isLocallySurjective_comp`

English:
instance isLocallySurjective_comp
  signature: {F₁ F₂ F₃ : Cᵒᵖ ⥤ A} (f₁ : F₁ ⟶ F₂) (f₂ : F₂ ⟶ F₃)
  body: by
    have : (Sieve.bind (imageSieve f₂ s) fun _ _ h => imageSieve f₁ h.choose) <=
        imageSieve (f₁ ≫ f₂) s := by
      rintro V i ⟨W, i, j, H, ⟨t', ht'⟩, rfl⟩
      refine ⟨t', ?_⟩
      rw [op_comp]; rw [F₃.map_comp]; rw [NatTrans.comp_app]; rw [ConcreteCategory.comp_apply]; rw [ConcreteCat

中文:
实例 isLocallySurjective_comp
  签名: {F₁ F₂ F₃ : Cᵒᵖ ⥤ A} (f₁ : F₁ ⟶ F₂) (f₂ : F₂ ⟶ F₃)
  定义体: by
    have : (Sieve.bind (imageSieve f₂ s) fun _ _ h => imageSieve f₁ h.choose) <=
        imageSieve (f₁ ≫ f₂) s := by
      rintro V i ⟨W, i, j, H, ⟨t', ht'⟩, rfl⟩
      refine ⟨t', ?_⟩
      rw [op_comp]; rw [F₃.map_comp]; rw [NatTrans.comp_app]; rw [ConcreteCategory.comp_apply]; rw [ConcreteCat

Depends on / 依赖: ConcreteCategory, ConcreteCategory.comp_apply, H.choose_spec, J.bind_covering, J.superset_covering, NatTrans, NatTrans.comp_app, NatTrans.naturality_apply, Sieve.bind, bind_covering, choose_spec, comp_app, comp_apply, h.choose, imageSieve, imageSieve_mem, intros, map_comp, naturality_apply, op_comp
-/
instance isLocallySurjective_comp {F₁ F₂ F₃ : Cᵒᵖ ⥤ A} (f₁ : F₁ ⟶ F₂) (f₂ : F₂ ⟶ F₃)
    [IsLocallySurjective J f₁] [IsLocallySurjective J f₂] :
    IsLocallySurjective J (f₁ ≫ f₂) where
  imageSieve_mem s := by
    have : (Sieve.bind (imageSieve f₂ s) fun _ _ h => imageSieve f₁ h.choose) <=
        imageSieve (f₁ ≫ f₂) s := by
      rintro V i ⟨W, i, j, H, ⟨t', ht'⟩, rfl⟩
      refine ⟨t', ?_⟩
      rw [op_comp]; rw [F₃.map_comp]; rw [NatTrans.comp_app]; rw [ConcreteCategory.comp_apply]; rw [ConcreteCategory.comp_apply]; rw [ht']; rw [NatTrans.naturality_apply]; rw [H.choose_spec]
    apply J.superset_covering this
    apply J.bind_covering
    · apply imageSieve_mem
    · intros; apply imageSieve_mem

/--
lemma `isLocallySurjective_of_isLocallySurjective` / 引理 `isLocallySurjective_of_isLocallySurjective`

English:
lemma isLocallySurjective_of_isLocallySurjective
  proof: by
    refine J.superset_covering ?_ (imageSieve_mem J (f₁ ≫ f₂) x)
    intro Y g hg
    exact ⟨f₁.app _ (localPreimage (f₁ ≫ f₂) x g hg),
      by simpa using app_localPreimage (f₁ ≫ f₂) x g hg⟩

中文:
引理 isLocallySurjective_of_isLocallySurjective
  证明: by
    refine J.superset_covering ?_ (imageSieve_mem J (f₁ ≫ f₂) x)
    intro Y g hg
    exact ⟨f₁.app _ (localPreimage (f₁ ≫ f₂) x g hg),
      by simpa using app_localPreimage (f₁ ≫ f₂) x g hg⟩

Depends on / 依赖: J.superset_covering, app_localPreimage, imageSieve_mem, localPreimage, superset_covering
-/
lemma isLocallySurjective_of_isLocallySurjective
    {F₁ F₂ F₃ : Cᵒᵖ ⥤ A} (f₁ : F₁ ⟶ F₂) (f₂ : F₂ ⟶ F₃)
    [IsLocallySurjective J (f₁ ≫ f₂)] :
    IsLocallySurjective J f₂ where
  imageSieve_mem {X} x := by
    refine J.superset_covering ?_ (imageSieve_mem J (f₁ ≫ f₂) x)
    intro Y g hg
    exact ⟨f₁.app _ (localPreimage (f₁ ≫ f₂) x g hg),
      by simpa using app_localPreimage (f₁ ≫ f₂) x g hg⟩

/--
lemma `isLocallySurjective_of_isLocallySurjective_fac` / 引理 `isLocallySurjective_of_isLocallySurjective_fac`

English:
lemma isLocallySurjective_of_isLocallySurjective_fac
  proof: by
  subst fac
  exact isLocallySurjective_of_isLocallySurjective J f₁ f₂

中文:
引理 isLocallySurjective_of_isLocallySurjective_fac
  证明: by
  subst fac
  exact isLocallySurjective_of_isLocallySurjective J f₁ f₂

Depends on / 依赖: isLocallySurjective_of_isLocallySurjective
-/
lemma isLocallySurjective_of_isLocallySurjective_fac
    {F₁ F₂ F₃ : Cᵒᵖ ⥤ A} {f₁ : F₁ ⟶ F₂} {f₂ : F₂ ⟶ F₃} {f₃ : F₁ ⟶ F₃} (fac : f₁ ≫ f₂ = f₃)
    [IsLocallySurjective J f₃] : IsLocallySurjective J f₂ := by
  subst fac
  exact isLocallySurjective_of_isLocallySurjective J f₁ f₂

/--
lemma `isLocallySurjective_iff_of_fac` / 引理 `isLocallySurjective_iff_of_fac`

English:
lemma isLocallySurjective_iff_of_fac
  proof: by
  constructor
  · intro
    exact isLocallySurjective_of_isLocallySurjective_fac J fac
  · intro
    rw [← fac]
    infer_instance

中文:
引理 isLocallySurjective_iff_of_fac
  证明: by
  constructor
  · intro
    exact isLocallySurjective_of_isLocallySurjective_fac J fac
  · intro
    rw [← fac]
    infer_instance

Depends on / 依赖: infer_instance, isLocallySurjective_of_isLocallySurjective_fac
-/
lemma isLocallySurjective_iff_of_fac
    {F₁ F₂ F₃ : Cᵒᵖ ⥤ A} {f₁ : F₁ ⟶ F₂} {f₂ : F₂ ⟶ F₃} {f₃ : F₁ ⟶ F₃} (fac : f₁ ≫ f₂ = f₃)
    [IsLocallySurjective J f₁] :
    IsLocallySurjective J f₃ ↔ IsLocallySurjective J f₂ := by
  constructor
  · intro
    exact isLocallySurjective_of_isLocallySurjective_fac J fac
  · intro
    rw [← fac]
    infer_instance

/--
lemma `comp_isLocallySurjective_iff` / 引理 `comp_isLocallySurjective_iff`

English:
lemma comp_isLocallySurjective_iff
  proof: isLocallySurjective_iff_of_fac J rfl

中文:
引理 comp_isLocallySurjective_iff
  证明: isLocallySurjective_iff_of_fac J rfl

Depends on / 依赖: isLocallySurjective_iff_of_fac
-/
lemma comp_isLocallySurjective_iff
    {F₁ F₂ F₃ : Cᵒᵖ ⥤ A} (f₁ : F₁ ⟶ F₂) (f₂ : F₂ ⟶ F₃)
    [IsLocallySurjective J f₁] :
    IsLocallySurjective J (f₁ ≫ f₂) ↔ IsLocallySurjective J f₂ :=
  isLocallySurjective_iff_of_fac J rfl

variable {J} in
/--
lemma `isLocallySurjective_of_le` / 引理 `isLocallySurjective_of_le`

English:
lemma isLocallySurjective_of_le
  statement: {K : GrothendieckTopology C} (hJK : J <= K) {F G : Cᵒᵖ ⥤ A}
  proof: by apply hJK; exact h.1 _

中文:
引理 isLocallySurjective_of_le
  结论: {K : Grothendieck拓扑 C} (hJK : J <= K) {F G : Cᵒᵖ ⥤ A}
  证明: by apply hJK; exact h.1 _
-/
lemma isLocallySurjective_of_le {K : GrothendieckTopology C} (hJK : J <= K) {F G : Cᵒᵖ ⥤ A}
    (f : F ⟶ G) (h : IsLocallySurjective J f) : IsLocallySurjective K f where
  imageSieve_mem s := by apply hJK; exact h.1 _

/--
lemma `isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective` / 引理 `isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective`

English:
lemma isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective
  proof: by
    let S := imageSieve f₁ x₁ ⊓ imageSieve f₁ x₂
    have hS : S in J X.unop := by
      apply J.intersection_covering
      all_goals apply imageSieve_mem
    let T : forall ⦃Y : C⦄ (f : Y ⟶ X.unop) (_ : S f), Sieve Y := fun Y f hf =>
      equalizerSieve (localPreimage f₁ x₁ f hf.1) (localPreim

中文:
引理 isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective
  证明: by
    let S := imageSieve f₁ x₁ ⊓ imageSieve f₁ x₂
    have hS : S in J X.unop := by
      apply J.intersection_covering
      all_goals apply imageSieve_mem
    let T : forall ⦃Y : C⦄ (f : Y ⟶ X.unop) (_ : S f), Sieve Y := fun Y f hf =>
      equalizerSieve (localPreimage f₁ x₁ f hf.1) (localPreim

Depends on / 依赖: J.intersection_covering, J.superset_covering, J.transitive, Sieve.bind, Sieve.le_pullback_bind, X.unop, all_goals, congr_arg, equalizerSieve, imageSieve, imageSieve_mem, intersection_covering, le_pullback_bind, localPreimage, superset_covering, transitive
-/
lemma isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective
    {F₁ F₂ F₃ : Cᵒᵖ ⥤ A} (f₁ : F₁ ⟶ F₂) (f₂ : F₂ ⟶ F₃)
    [IsLocallyInjective J (f₁ ≫ f₂)] [IsLocallySurjective J f₁] :
    IsLocallyInjective J f₂ where
  equalizerSieve_mem {X} x₁ x₂ h := by
    let S := imageSieve f₁ x₁ ⊓ imageSieve f₁ x₂
    have hS : S in J X.unop := by
      apply J.intersection_covering
      all_goals apply imageSieve_mem
    let T : forall ⦃Y : C⦄ (f : Y ⟶ X.unop) (_ : S f), Sieve Y := fun Y f hf =>
      equalizerSieve (localPreimage f₁ x₁ f hf.1) (localPreimage f₁ x₂ f hf.2)
    refine J.superset_covering ?_ (J.transitive hS (Sieve.bind S.1 T) ?_)
    · rintro Y f ⟨Z, a, g, hg, ha, rfl⟩
      simpa using congr_arg (f₁.app _) ha
    · intro Y f hf
      apply J.superset_covering (Sieve.le_pullback_bind _ _ _ hf)
      apply equalizerSieve_mem J (f₁ ≫ f₂)
      dsimp
      rw [ConcreteCategory.comp_apply]; rw [ConcreteCategory.comp_apply]; rw [app_localPreimage]; rw [app_localPreimage]; rw [NatTrans.naturality_apply]; rw [NatTrans.naturality_apply]; rw [h]

/--
lemma `isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective_fac` / 引理 `isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective_fac`

English:
lemma isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective_fac
  proof: by
  subst fac
  exact isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective J f₁ f₂

中文:
引理 isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective_fac
  证明: by
  subst fac
  exact isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective J f₁ f₂

Depends on / 依赖: isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective
-/
lemma isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective_fac
    {F₁ F₂ F₃ : Cᵒᵖ ⥤ A} {f₁ : F₁ ⟶ F₂} {f₂ : F₂ ⟶ F₃} (f₃ : F₁ ⟶ F₃) (fac : f₁ ≫ f₂ = f₃)
    [IsLocallyInjective J f₃] [IsLocallySurjective J f₁] :
    IsLocallyInjective J f₂ := by
  subst fac
  exact isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective J f₁ f₂

/--
lemma `isLocallySurjective_of_isLocallySurjective_of_isLocallyInjective` / 引理 `isLocallySurjective_of_isLocallySurjective_of_isLocallyInjective`

English:
lemma isLocallySurjective_of_isLocallySurjective_of_isLocallyInjective
  proof: by
    let S := imageSieve (f₁ ≫ f₂) (f₂.app _ x)
    let T : forall ⦃Y : C⦄ (f : Y ⟶ X) (_ : S f), Sieve Y := fun Y f hf =>
      equalizerSieve (f₁.app _ (localPreimage (f₁ ≫ f₂) (f₂.app _ x) f hf)) (F₂.map f.op x)
    refine J.superset_covering ?_ (J.transitive (imageSieve_mem J (f₁ ≫ f₂) (f₂.app

中文:
引理 isLocallySurjective_of_isLocallySurjective_of_isLocallyInjective
  证明: by
    let S := imageSieve (f₁ ≫ f₂) (f₂.app _ x)
    let T : forall ⦃Y : C⦄ (f : Y ⟶ X) (_ : S f), Sieve Y := fun Y f hf =>
      equalizerSieve (f₁.app _ (localPreimage (f₁ ≫ f₂) (f₂.app _ x) f hf)) (F₂.map f.op x)
    refine J.superset_covering ?_ (J.transitive (imageSieve_mem J (f₁ ≫ f₂) (f₂.app

Depends on / 依赖: J.superset_covering, J.transitive, Sieve.bind, Sieve.le_pullback_bind, a.op, equalizerSieve, f.op, imageSieve, imageSieve_mem, le_pullback_bind, localPreimage, superset_covering, transitive
-/
lemma isLocallySurjective_of_isLocallySurjective_of_isLocallyInjective
    {F₁ F₂ F₃ : Cᵒᵖ ⥤ A} (f₁ : F₁ ⟶ F₂) (f₂ : F₂ ⟶ F₃)
    [IsLocallySurjective J (f₁ ≫ f₂)] [IsLocallyInjective J f₂] :
    IsLocallySurjective J f₁ where
  imageSieve_mem {X} x := by
    let S := imageSieve (f₁ ≫ f₂) (f₂.app _ x)
    let T : forall ⦃Y : C⦄ (f : Y ⟶ X) (_ : S f), Sieve Y := fun Y f hf =>
      equalizerSieve (f₁.app _ (localPreimage (f₁ ≫ f₂) (f₂.app _ x) f hf)) (F₂.map f.op x)
    refine J.superset_covering ?_ (J.transitive (imageSieve_mem J (f₁ ≫ f₂) (f₂.app _ x))
      (Sieve.bind S.1 T) ?_)
    · rintro Y _ ⟨Z, a, g, hg, ha, rfl⟩
      exact ⟨F₁.map a.op (localPreimage (f₁ ≫ f₂) _ _ hg), by simpa using! ha⟩
    · intro Y f hf
      apply J.superset_covering (Sieve.le_pullback_bind _ _ _ hf)
      apply equalizerSieve_mem J f₂
      rw [NatTrans.naturality_apply]; rw [← app_localPreimage (f₁ ≫ f₂) _ _ hf]; rw [NatTrans.comp_app]; rw [ConcreteCategory.comp_apply]

/--
lemma `isLocallySurjective_of_isLocallySurjective_of_isLocallyInjective_fac` / 引理 `isLocallySurjective_of_isLocallySurjective_of_isLocallyInjective_fac`

English:
lemma isLocallySurjective_of_isLocallySurjective_of_isLocallyInjective_fac
  proof: by
  subst fac
  exact isLocallySurjective_of_isLocallySurjective_of_isLocallyInjective J f₁ f₂

中文:
引理 isLocallySurjective_of_isLocallySurjective_of_isLocallyInjective_fac
  证明: by
  subst fac
  exact isLocallySurjective_of_isLocallySurjective_of_isLocallyInjective J f₁ f₂

Depends on / 依赖: isLocallySurjective_of_isLocallySurjective_of_isLocallyInjective
-/
lemma isLocallySurjective_of_isLocallySurjective_of_isLocallyInjective_fac
    {F₁ F₂ F₃ : Cᵒᵖ ⥤ A} {f₁ : F₁ ⟶ F₂} {f₂ : F₂ ⟶ F₃} (f₃ : F₁ ⟶ F₃) (fac : f₁ ≫ f₂ = f₃)
    [IsLocallySurjective J f₃] [IsLocallyInjective J f₂] :
    IsLocallySurjective J f₁ := by
  subst fac
  exact isLocallySurjective_of_isLocallySurjective_of_isLocallyInjective J f₁ f₂

/--
lemma `comp_isLocallyInjective_iff` / 引理 `comp_isLocallyInjective_iff`

English:
lemma comp_isLocallyInjective_iff
  proof: by
  constructor
  · intro
    exact isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective J f₁ f₂
  · intro
    infer_instance

中文:
引理 comp_isLocallyInjective_iff
  证明: by
  constructor
  · intro
    exact isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective J f₁ f₂
  · intro
    infer_instance

Depends on / 依赖: infer_instance, isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective
-/
lemma comp_isLocallyInjective_iff
    {F₁ F₂ F₃ : Cᵒᵖ ⥤ A} (f₁ : F₁ ⟶ F₂) (f₂ : F₂ ⟶ F₃)
    [IsLocallyInjective J f₁] [IsLocallySurjective J f₁] :
    IsLocallyInjective J (f₁ ≫ f₂) ↔ IsLocallyInjective J f₂ := by
  constructor
  · intro
    exact isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective J f₁ f₂
  · intro
    infer_instance

/--
lemma `isLocallySurjective_comp_iff` / 引理 `isLocallySurjective_comp_iff`

English:
lemma isLocallySurjective_comp_iff
  proof: by
  constructor
  · intro
    exact isLocallySurjective_of_isLocallySurjective_of_isLocallyInjective J f₁ f₂
  · intro
    infer_instance

中文:
引理 isLocallySurjective_comp_iff
  证明: by
  constructor
  · intro
    exact isLocallySurjective_of_isLocallySurjective_of_isLocallyInjective J f₁ f₂
  · intro
    infer_instance

Depends on / 依赖: infer_instance, isLocallySurjective_of_isLocallySurjective_of_isLocallyInjective
-/
lemma isLocallySurjective_comp_iff
    {F₁ F₂ F₃ : Cᵒᵖ ⥤ A} (f₁ : F₁ ⟶ F₂) (f₂ : F₂ ⟶ F₃)
    [IsLocallyInjective J f₂] [IsLocallySurjective J f₂] :
    IsLocallySurjective J (f₁ ≫ f₂) ↔ IsLocallySurjective J f₁ := by
  constructor
  · intro
    exact isLocallySurjective_of_isLocallySurjective_of_isLocallyInjective J f₁ f₂
  · intro
    infer_instance

instance {F₁ F₂ : Cᵒᵖ ⥤ Type w} (f : F₁ ⟶ F₂) :
    IsLocallySurjective J (Subfunctor.toRangeSheafify J f) where
  imageSieve_mem {X} := by
    rintro ⟨s, hs⟩
    refine J.superset_covering ?_ hs
    rintro Y g ⟨t, ht⟩
    exact ⟨t, Subtype.ext ht⟩

/--
Definition of `sheafificationIsoImagePresheaf` / `sheafificationIsoImagePresheaf` 的定义

English:
definition sheafificationIsoImagePresheaf
  signature: (F : Cᵒᵖ ⥤ Type (max u v))
  body: J.sheafifyLift (Subfunctor.toRangeSheafify J _)
      ((isSheaf_iff_isSheaf_of_type J _).mpr <|
Subfunctor.sheafify_isSheaf _
(isSheaf_iff_isSheaf_of_type J _).mp GrothendieckTopology.sheafify_isSheaf J _)
  inv := Subfunctor.ι _
  hom_inv_id :=
    J.sheafify_hom_ext _ _ (J.sheafify_isSheaf _) (by 

中文:
定义 sheafificationIsoImagePresheaf
  签名: (F : Cᵒᵖ ⥤ 类型 (最大值 u v))
  定义体: J.sheafifyLift (Subfunctor.toRangeSheafify J _)
      ((isSheaf_iff_isSheaf_of_type J _).mpr <|
Subfunctor.sheafify_isSheaf _
(isSheaf_iff_isSheaf_of_type J _).mp GrothendieckTopology.sheafify_isSheaf J _)
  inv := Subfunctor.ι _
  hom_inv_id :=
    J.sheafify_hom_ext _ _ (J.sheafify_isSheaf _) (by 

Depends on / 依赖: Category, Category.assoc, Category.comp_id, Category.id_comp, Eq.trans, GrothendieckTopology, GrothendieckTopology.sheafify_isSheaf, J.sh, J.sheafifyLift, J.sheafify_hom_ext, J.sheafify_isSheaf, Subfunctor, Subfunctor.sheafify_isSheaf, Subfunctor.toRangeSheafify, cancel_mono, comp_id, hom_inv_id, id_comp, inv_hom_id, isSheaf_iff_isSheaf_of_type
-/
noncomputable def sheafificationIsoImagePresheaf (F : Cᵒᵖ ⥤ Type (max u v)) :
    J.sheafify F ≅ ((Subfunctor.range (J.toSheafify F)).sheafify J).toFunctor where
  hom :=
    J.sheafifyLift (Subfunctor.toRangeSheafify J _)
      ((isSheaf_iff_isSheaf_of_type J _).mpr <|
Subfunctor.sheafify_isSheaf _
(isSheaf_iff_isSheaf_of_type J _).mp GrothendieckTopology.sheafify_isSheaf J _)
  inv := Subfunctor.ι _
  hom_inv_id :=
    J.sheafify_hom_ext _ _ (J.sheafify_isSheaf _) (by simp [Subfunctor.toRangeSheafify])
  inv_hom_id := by
    rw [← cancel_mono (Subfunctor.ι _)]; rw [Category.id_comp]; rw [Category.assoc]
    refine Eq.trans ?_ (Category.comp_id _)
    congr 1
    exact J.sheafify_hom_ext _ _ (J.sheafify_isSheaf _) (by simp [Subfunctor.toRangeSheafify])

section

open GrothendieckTopology.Plus

/--
Instance `isLocallySurjective_toPlus` / 实例 `isLocallySurjective_toPlus`

English:
instance isLocallySurjective_toPlus
  signature: (P : Cᵒᵖ ⥤ Type (max u v))
  body: by
    obtain ⟨S, x, rfl⟩ := exists_rep x
    refine J.superset_covering (fun Y f hf => ⟨x.1 ⟨Y, f, hf⟩, ?_⟩) S.2
    rw [toPlus_eq_mk]; rw [res_mk_eq_mk_pullback]; rw [eq_mk_iff_exists]
    refine ⟨S.pullback f, homOfLE le_top, 𝟙 _, ?_⟩
    ext ⟨Z, g, hg⟩
    simpa using!
      x.2 { fst.hf := hf, 

中文:
实例 isLocallySurjective_toPlus
  签名: (P : Cᵒᵖ ⥤ 类型 (最大值 u v))
  定义体: by
    obtain ⟨S, x, rfl⟩ := exists_rep x
    refine J.superset_covering (fun Y f hf => ⟨x.1 ⟨Y, f, hf⟩, ?_⟩) S.2
    rw [toPlus_eq_mk]; rw [res_mk_eq_mk_pullback]; rw [eq_mk_iff_exists]
    refine ⟨S.pullback f, homOfLE le_top, 𝟙 _, ?_⟩
    ext ⟨Z, g, hg⟩
    simpa using!
      x.2 { fst.hf := hf, 

Depends on / 依赖: J.superset_covering, S.pullback, downward_closed, eq_mk_iff_exists, exists_rep, fst.hf, homOfLE, le_top, pullback, res_mk_eq_mk_pullback, snd.hf, superset_covering, toPlus_eq_mk
-/
instance isLocallySurjective_toPlus (P : Cᵒᵖ ⥤ Type (max u v)) :
    IsLocallySurjective J (J.toPlus P) where
  imageSieve_mem x := by
    obtain ⟨S, x, rfl⟩ := exists_rep x
    refine J.superset_covering (fun Y f hf => ⟨x.1 ⟨Y, f, hf⟩, ?_⟩) S.2
    rw [toPlus_eq_mk]; rw [res_mk_eq_mk_pullback]; rw [eq_mk_iff_exists]
    refine ⟨S.pullback f, homOfLE le_top, 𝟙 _, ?_⟩
    ext ⟨Z, g, hg⟩
    simpa using!
      x.2 { fst.hf := hf, snd.hf := S.1.downward_closed hf g, r.g₁ := g, r.g₂ := 𝟙 Z, .. }

set_option backward.isDefEq.respectTransparency false in
/--
Instance `isLocallySurjective_toSheafify` / 实例 `isLocallySurjective_toSheafify`

English:
instance isLocallySurjective_toSheafify
  signature: (P : Cᵒᵖ ⥤ Type (max u v))
  body: by
  dsimp [GrothendieckTopology.toSheafify]
  rw [GrothendieckTopology.plusMap_toPlus]
  infer_instance

中文:
实例 isLocallySurjective_toSheafify
  签名: (P : Cᵒᵖ ⥤ 类型 (最大值 u v))
  定义体: by
  dsimp [GrothendieckTopology.toSheafify]
  rw [GrothendieckTopology.plusMap_toPlus]
  infer_instance

Depends on / 依赖: GrothendieckTopology, GrothendieckTopology.plusMap_toPlus, GrothendieckTopology.toSheafify, infer_instance, plusMap_toPlus, toSheafify
-/
instance isLocallySurjective_toSheafify (P : Cᵒᵖ ⥤ Type (max u v)) :
    IsLocallySurjective J (J.toSheafify P) := by
  dsimp [GrothendieckTopology.toSheafify]
  rw [GrothendieckTopology.plusMap_toPlus]
  infer_instance

/--
Instance `isLocallySurjective_toSheafify'` / 实例 `isLocallySurjective_toSheafify'`

English:
instance isLocallySurjective_toSheafify'
  signature: {D : Type*} [Category* D] {FD : D -> D -> Type*}
  body: by
  rw [isLocallySurjective_iff_whisker_forget]; rw [← sheafComposeIso_hom_fac]; rw [← toSheafify_plusPlusIsoSheafify_hom]
  infer_instance

中文:
实例 isLocallySurjective_toSheafify'
  签名: {D : 类型} [范畴* D] {FD : D -> D -> 类型}
  定义体: by
  rw [isLocallySurjective_iff_whisker_forget]; rw [← sheafComposeIso_hom_fac]; rw [← toSheafify_plusPlusIsoSheafify_hom]
  infer_instance

Depends on / 依赖: infer_instance, isLocallySurjective_iff_whisker_forget, sheafComposeIso_hom_fac, toSheafify_plusPlusIsoSheafify_hom
-/
instance isLocallySurjective_toSheafify' {D : Type*} [Category* D] {FD : D -> D -> Type*}
    {CD : D -> Type (max u v)} [forall X Y, FunLike (FD X Y) (CD X) (CD Y)]
    [ConcreteCategory.{max u v} D FD]
    (P : Cᵒᵖ ⥤ D) [HasWeakSheafify J D] [J.HasSheafCompose (forget D)]
    [J.PreservesSheafification (forget D)] :
    IsLocallySurjective J (toSheafify J P) := by
  rw [isLocallySurjective_iff_whisker_forget]; rw [← sheafComposeIso_hom_fac]; rw [← toSheafify_plusPlusIsoSheafify_hom]
  infer_instance

end

end Presheaf

namespace Sheaf

variable {J}
variable {F₁ F₂ F₃ : Sheaf J A} (φ : F₁ ⟶ F₂) (ψ : F₂ ⟶ F₃)

/--
Definition of `IsLocallySurjective` / `IsLocallySurjective` 的定义

English:
abbreviation IsLocallySurjective
  body: Presheaf.IsLocallySurjective J φ.hom

中文:
缩写 是LocallySurjective
  定义体: Presheaf.IsLocallySurjective J φ.hom

Depends on / 依赖: IsLocallySurjective, Presheaf, Presheaf.IsLocallySurjective
-/
abbrev IsLocallySurjective := Presheaf.IsLocallySurjective J φ.hom

/--
lemma `isLocallySurjective_sheafToPresheaf_map_iff` / 引理 `isLocallySurjective_sheafToPresheaf_map_iff`

English:
lemma isLocallySurjective_sheafToPresheaf_map_iff
  proof: by rfl

中文:
引理 isLocallySurjective_sheafToPresheaf_map_iff
  证明: by rfl
-/
lemma isLocallySurjective_sheafToPresheaf_map_iff :
    Presheaf.IsLocallySurjective J ((sheafToPresheaf J A).map φ) ↔ IsLocallySurjective φ := by rfl

/--
Instance `isLocallySurjective_comp` / 实例 `isLocallySurjective_comp`

English:
instance isLocallySurjective_comp
  signature: [IsLocallySurjective φ] [IsLocallySurjective ψ]
  body: Presheaf.isLocallySurjective_comp J φ.hom ψ.hom

中文:
实例 isLocallySurjective_comp
  签名: [是LocallySurjective φ] [是LocallySurjective ψ]
  定义体: Presheaf.isLocallySurjective_comp J φ.hom ψ.hom

Depends on / 依赖: Presheaf, Presheaf.isLocallySurjective_comp, isLocallySurjective_comp
-/
instance isLocallySurjective_comp [IsLocallySurjective φ] [IsLocallySurjective ψ] :
    IsLocallySurjective (φ ≫ ψ) :=
  Presheaf.isLocallySurjective_comp J φ.hom ψ.hom

/--
Instance `isLocallySurjective_of_iso` / 实例 `isLocallySurjective_of_iso`

English:
instance isLocallySurjective_of_iso
  signature: [IsIso φ]
  body: by
  have : IsIso φ.hom := (inferInstance : IsIso ((sheafToPresheaf J A).map φ))
  infer_instance

中文:
实例 isLocallySurjective_of_iso
  签名: [是同构 φ]
  定义体: by
  have : IsIso φ.hom := (inferInstance : IsIso ((sheafToPresheaf J A).map φ))
  infer_instance

Depends on / 依赖: infer_instance, sheafToPresheaf
-/
instance isLocallySurjective_of_iso [IsIso φ] : IsLocallySurjective φ := by
  have : IsIso φ.hom := (inferInstance : IsIso ((sheafToPresheaf J A).map φ))
  infer_instance

set_option backward.isDefEq.respectTransparency false in
instance {F G : Sheaf J (Type w)} (f : F ⟶ G) :
    IsLocallySurjective (Sheaf.toImage f) := by
  dsimp [Sheaf.toImage]
  infer_instance

variable [J.HasSheafCompose (forget A)]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsLocallySurjective
  signature: φ] :
  body: (Presheaf.isLocallySurjective_iff_whisker_forget J φ.hom).1 inferInstance

中文:
实例 [是LocallySurjective
  签名: φ] :
  定义体: (Presheaf.isLocallySurjective_iff_whisker_forget J φ.hom).1 inferInstance

Depends on / 依赖: Presheaf, Presheaf.isLocallySurjective_iff_whisker_forget, isLocallySurjective_iff_whisker_forget
-/
instance [IsLocallySurjective φ] :
    IsLocallySurjective ((sheafCompose J (forget A)).map φ) :=
  (Presheaf.isLocallySurjective_iff_whisker_forget J φ.hom).1 inferInstance

/--
theorem `isLocallySurjective_iff_isIso` / 定理 `isLocallySurjective_iff_isIso`

English:
theorem isLocallySurjective_iff_isIso
  given: {F G : Sheaf J (Type w)} (f : F ⟶ G)
  proof: by
  dsimp only [IsLocallySurjective]
  rw [Sheaf.imageι]; rw [Presheaf.isLocallySurjective_iff_range_sheafify_eq_top']; rw [Subfunctor.eq_top_iff_isIso]
  exact isIso_iff_of_reflects_iso (f := Sheaf.imageι f) (F := sheafToPresheaf J (Type w))

中文:
定理 isLocallySurjective_iff_isIso
  条件: {F G : 层 J (类型 w)} (f : F ⟶ G)
  证明: by
  dsimp only [IsLocallySurjective]
  rw [Sheaf.imageι]; rw [Presheaf.isLocallySurjective_iff_range_sheafify_eq_top']; rw [Subfunctor.eq_top_iff_isIso]
  exact isIso_iff_of_reflects_iso (f := Sheaf.imageι f) (F := sheafToPresheaf J (Type w))

Depends on / 依赖: IsLocallySurjective, Presheaf, Presheaf.isLocallySurjective_iff_range_sheafify_eq_top, Sheaf.image, Subfunctor, Subfunctor.eq_top_iff_isIso, eq_top_iff_isIso, isIso_iff_of_reflects_iso, isLocallySurjective_iff_range_sheafify_eq_top, sheafToPresheaf
-/
theorem isLocallySurjective_iff_isIso {F G : Sheaf J (Type w)} (f : F ⟶ G) :
    IsLocallySurjective f ↔ IsIso (Sheaf.imageι f) := by
  dsimp only [IsLocallySurjective]
  rw [Sheaf.imageι]; rw [Presheaf.isLocallySurjective_iff_range_sheafify_eq_top']; rw [Subfunctor.eq_top_iff_isIso]
  exact isIso_iff_of_reflects_iso (f := Sheaf.imageι f) (F := sheafToPresheaf J (Type w))

/--
Instance `epi_of_isLocallySurjective'` / 实例 `epi_of_isLocallySurjective'`

English:
instance epi_of_isLocallySurjective'
  signature: {F₁ F₂ : Sheaf J (Type w)} (φ : F₁ ⟶ F₂)
  body: by
    ext X x
    apply (((isSheaf_iff_isSheaf_of_type _ _).1 Z.2).isSeparated _
      (Presheaf.imageSieve_mem J φ.hom x)).ext
    rintro Y f ⟨s : F₁.obj.obj (op Y), hs : φ.hom.app _ s = F₂.obj.map f.op x⟩
    dsimp
    have h₁ := ConcreteCategory.congr_hom (f₁.hom.naturality f.op) x
    have h₂ :

中文:
实例 epi_of_isLocallySurjective'
  签名: {F₁ F₂ : 层 J (类型 w)} (φ : F₁ ⟶ F₂)
  定义体: by
    ext X x
    apply (((isSheaf_iff_isSheaf_of_type _ _).1 Z.2).isSeparated _
      (Presheaf.imageSieve_mem J φ.hom x)).ext
    rintro Y f ⟨s : F₁.obj.obj (op Y), hs : φ.hom.app _ s = F₂.obj.map f.op x⟩
    dsimp
    have h₁ := ConcreteCategory.congr_hom (f₁.hom.naturality f.op) x
    have h₂ :

Depends on / 依赖: ConcreteCategory, ConcreteCategory.congr_hom, Presheaf, Presheaf.imageSieve_mem, congr_app, congr_hom, congr_map, f.op, hom.app, hom.naturality, imageSieve_mem, isSeparated, isSheaf_iff_isSheaf_of_type, naturality, obj.map, obj.obj, sheafToPresheaf
-/
instance epi_of_isLocallySurjective' {F₁ F₂ : Sheaf J (Type w)} (φ : F₁ ⟶ F₂)
    [IsLocallySurjective φ] : Epi φ where
  left_cancellation {Z} f₁ f₂ h := by
    ext X x
    apply (((isSheaf_iff_isSheaf_of_type _ _).1 Z.2).isSeparated _
      (Presheaf.imageSieve_mem J φ.hom x)).ext
    rintro Y f ⟨s : F₁.obj.obj (op Y), hs : φ.hom.app _ s = F₂.obj.map f.op x⟩
    dsimp
    have h₁ := ConcreteCategory.congr_hom (f₁.hom.naturality f.op) x
    have h₂ := ConcreteCategory.congr_hom (f₂.hom.naturality f.op) x
    dsimp at h₁ h₂
    rw [← h₁]; rw [← h₂]; rw [← hs]
    exact ConcreteCategory.congr_hom (congr_app ((sheafToPresheaf J _).congr_map h) (op Y)) s

/--
Instance `epi_of_isLocallySurjective` / 实例 `epi_of_isLocallySurjective`

English:
instance epi_of_isLocallySurjective
  signature: [IsLocallySurjective φ]
  body: (sheafCompose J (forget A)).epi_of_epi_map inferInstance

中文:
实例 epi_of_isLocallySurjective
  签名: [是LocallySurjective φ]
  定义体: (sheafCompose J (forget A)).epi_of_epi_map inferInstance

Depends on / 依赖: epi_of_epi_map, forget, sheafCompose
-/
instance epi_of_isLocallySurjective [IsLocallySurjective φ] : Epi φ :=
  (sheafCompose J (forget A)).epi_of_epi_map inferInstance

/--
lemma `isLocallySurjective_iff_epi` / 引理 `isLocallySurjective_iff_epi`

English:
lemma isLocallySurjective_iff_epi
  statement: {F G : Sheaf J (Type w)} (φ : F ⟶ G)
  proof: by
  constructor
  · intro
    infer_instance
  · intro
    have := epi_of_epi_fac (Sheaf.toImage_ι φ)
    rw [isLocallySurjective_iff_isIso φ]
    apply isIso_of_mono_of_epi

中文:
引理 isLocallySurjective_iff_epi
  结论: {F G : 层 J (类型 w)} (φ : F ⟶ G)
  证明: by
  constructor
  · intro
    infer_instance
  · intro
    have := epi_of_epi_fac (Sheaf.toImage_ι φ)
    rw [isLocallySurjective_iff_isIso φ]
    apply isIso_of_mono_of_epi

Depends on / 依赖: Sheaf.toImage_, epi_of_epi_fac, infer_instance, isIso_of_mono_of_epi, isLocallySurjective_iff_isIso
-/
lemma isLocallySurjective_iff_epi {F G : Sheaf J (Type w)} (φ : F ⟶ G)
    [HasSheafify J (Type w)] :
    IsLocallySurjective φ ↔ Epi φ := by
  constructor
  · intro
    infer_instance
  · intro
    have := epi_of_epi_fac (Sheaf.toImage_ι φ)
    rw [isLocallySurjective_iff_isIso φ]
    apply isIso_of_mono_of_epi

end Sheaf

namespace Presieve.FamilyOfElements

variable {R R' : Cᵒᵖ ⥤ Type w} (φ : R ⟶ R') {X : Cᵒᵖ} (r' : R'.obj X)

/--
Definition of `localPreimage` / `localPreimage` 的定义

English:
definition localPreimage
  signature: :
  body: fun _ f hf => Presheaf.localPreimage φ r' f hf

中文:
定义 localPreimage
  签名: :
  定义体: fun _ f hf => Presheaf.localPreimage φ r' f hf

Depends on / 依赖: Presheaf, Presheaf.localPreimage, localPreimage
-/
noncomputable def localPreimage :
    FamilyOfElements R (Presheaf.imageSieve φ r').arrows :=
  fun _ f hf => Presheaf.localPreimage φ r' f hf

/--
lemma `isAmalgamation_map_localPreimage` / 引理 `isAmalgamation_map_localPreimage`

English:
lemma isAmalgamation_map_localPreimage
  proof: fun _ f hf => (Presheaf.app_localPreimage φ r' f hf).symm

中文:
引理 isAmalgamation_map_localPreimage
  证明: fun _ f hf => (Presheaf.app_localPreimage φ r' f hf).symm

Depends on / 依赖: Presheaf, Presheaf.app_localPreimage, app_localPreimage
-/
lemma isAmalgamation_map_localPreimage :
    ((localPreimage φ r').map φ).IsAmalgamation r' :=
  fun _ f hf => (Presheaf.app_localPreimage φ r' f hf).symm

end Presieve.FamilyOfElements

namespace Presheaf

variable {S : C} {ι : Type*} [Small.{w} ι] {X : ι -> C} (f : forall i, X i ⟶ S)

variable [LocallySmall.{w} C]

/--
lemma `imageSieve_cofanIsColimitDesc_shrinkYoneda_map` / 引理 `imageSieve_cofanIsColimitDesc_shrinkYoneda_map`

English:
lemma imageSieve_cofanIsColimitDesc_shrinkYoneda_map
  proof: by
  ext V v
  simp only [Sieve.pullback_apply, Sieve.generate_apply]
  refine ⟨fun hv => ?_, ?_⟩
  · obtain ⟨w, hw⟩ := hv
    obtain ⟨⟨i⟩, a, rfl⟩ := Types.jointly_surjective_of_isColimit
      (isColimitOfPreserves ((evaluation _ _).obj (op V)) hc) w
    obtain ⟨a : V ⟶ X i, rfl⟩ := shrinkYonedaOb

中文:
引理 imageSieve_cofanIsColimitDesc_shrinkYoneda_map
  证明: by
  ext V v
  simp only [Sieve.pullback_apply, Sieve.generate_apply]
  refine ⟨fun hv => ?_, ?_⟩
  · obtain ⟨w, hw⟩ := hv
    obtain ⟨⟨i⟩, a, rfl⟩ := Types.jointly_surjective_of_isColimit
      (isColimitOfPreserves ((evaluation _ _).obj (op V)) hc) w
    obtain ⟨a : V ⟶ X i, rfl⟩ := shrinkYonedaOb
-/
lemma imageSieve_cofanIsColimitDesc_shrinkYoneda_map
    {c : Cofan (fun i => shrinkYoneda.{w}.obj (X i))} (hc : IsColimit c)
    {U : C} (g : U ⟶ S) :
    Presheaf.imageSieve
      (Cofan.IsColimit.desc hc (fun i => shrinkYoneda.{w}.map (f i))) (U := U)
        (shrinkYonedaObjObjEquiv.symm g) = Sieve.pullback g (Sieve.ofArrows X f) := by
  ext V v
  simp only [Sieve.pullback_apply, Sieve.generate_apply]
  refine ⟨fun hv => ?_, ?_⟩
  · obtain ⟨w, hw⟩ := hv
    obtain ⟨⟨i⟩, a, rfl⟩ := Types.jointly_surjective_of_isColimit
      (isColimitOfPreserves ((evaluation _ _).obj (op V)) hc) w
    obtain ⟨a : V ⟶ X i, rfl⟩ := shrinkYonedaObjObjEquiv.symm.surjective a
    refine ⟨_, a, _, ⟨i⟩, shrinkYonedaObjObjEquiv.symm.injective ?_⟩
    rw [← shrinkYoneda_map_app_shrinkYonedaObjObjEquiv_symm]
    convert! hw using 1
    · exact (ConcreteCategory.congr_hom (NatTrans.congr_app
        ((Cofan.IsColimit.fac hc (fun i => shrinkYoneda.{w}.map (f i))) i) (op V))
          (shrinkYonedaObjObjEquiv.symm a)).symm
    · exact (shrinkYoneda_obj_map_shrinkYonedaObjObjEquiv_symm v.op g).symm
  · rintro ⟨_, a, _, ⟨i⟩, fac⟩
    refine ⟨(c.inj i).app (op V) (shrinkYonedaObjObjEquiv.symm a),
      (ConcreteCategory.congr_hom (NatTrans.congr_app
      ((Cofan.IsColimit.fac hc (fun i => shrinkYoneda.{w}.map (f i))) i) (op V))
        (shrinkYonedaObjObjEquiv.symm a)).trans ?_⟩
    rw [shrinkYoneda_map_app_shrinkYonedaObjObjEquiv_symm a (f i)]; rw [fac]
    exact (shrinkYoneda_obj_map_shrinkYonedaObjObjEquiv_symm v.op g).symm

end Presheaf

namespace GrothendieckTopology

/--
lemma `ofArrows_mem_iff_isLocallySurjective_cofanIsColimitDesc_shrinkYoneda_map` / 引理 `ofArrows_mem_iff_isLocallySurjective_cofanIsColimitDesc_shrinkYoneda_map`

English:
lemma ofArrows_mem_iff_isLocallySurjective_cofanIsColimitDesc_shrinkYoneda_map
  proof: by
  refine ⟨fun hf => ⟨fun {U u} => ?_⟩, fun hf => ?_⟩
  · obtain ⟨u, rfl⟩ := shrinkYonedaObjObjEquiv.symm.surjective u
    replace hf := J.pullback_stable u hf
    rwa [← Presheaf.imageSieve_cofanIsColimitDesc_shrinkYoneda_map f hc u] at hf
  · rw [← Sieve.pullback_id (S := Sieve.ofArrows X f),
  

中文:
引理 ofArrows_mem_iff_isLocallySurjective_cofanIsColimitDesc_shrinkYoneda_map
  证明: by
  refine ⟨fun hf => ⟨fun {U u} => ?_⟩, fun hf => ?_⟩
  · obtain ⟨u, rfl⟩ := shrinkYonedaObjObjEquiv.symm.surjective u
    replace hf := J.pullback_stable u hf
    rwa [← Presheaf.imageSieve_cofanIsColimitDesc_shrinkYoneda_map f hc u] at hf
  · rw [← Sieve.pullback_id (S := Sieve.ofArrows X f),
  

Depends on / 依赖: Cofan.IsColimit.desc, IsColimit, J.pullback_stable, Presheaf, Presheaf.imageSieve_cofanIsColimitDesc_shrinkYoneda_map, Presheaf.imageSieve_mem, Sieve.ofArrows, Sieve.pullback_id, imageSieve_cofanIsColimitDesc_shrinkYoneda_map, imageSieve_mem, ofArrows, pullback_id, pullback_stable, replace, shrinkYoneda, shrinkYonedaObjObjEquiv, shrinkYonedaObjObjEquiv.symm, shrinkYonedaObjObjEquiv.symm.surjective, surjective
-/
lemma ofArrows_mem_iff_isLocallySurjective_cofanIsColimitDesc_shrinkYoneda_map
    [LocallySmall.{w} C] {S : C} {ι : Type*} [Small.{w} ι] {X : ι -> C}
    (f : forall i, X i ⟶ S)
    {c : Cofan (fun i => shrinkYoneda.{w}.obj (X i))} (hc : IsColimit c) :
    Sieve.ofArrows _ f in J S ↔
      Presheaf.IsLocallySurjective J
        (Cofan.IsColimit.desc hc (fun i => shrinkYoneda.{w}.map (f i))) := by
  refine ⟨fun hf => ⟨fun {U u} => ?_⟩, fun hf => ?_⟩
  · obtain ⟨u, rfl⟩ := shrinkYonedaObjObjEquiv.symm.surjective u
    replace hf := J.pullback_stable u hf
    rwa [← Presheaf.imageSieve_cofanIsColimitDesc_shrinkYoneda_map f hc u] at hf
  · rw [← Sieve.pullback_id (S := Sieve.ofArrows X f),
      ← Presheaf.imageSieve_cofanIsColimitDesc_shrinkYoneda_map f hc (𝟙 S)]
    exact Presheaf.imageSieve_mem J (Cofan.IsColimit.desc hc (fun i => shrinkYoneda.{w}.map (f i)))
      (shrinkYonedaObjObjEquiv.symm (𝟙 S))

set_option backward.isDefEq.respectTransparency false in
/--
lemma `ofArrows_mem_iff_isLocallySurjective_cofanIsColimitDesc_uliftYoneda_map` / 引理 `ofArrows_mem_iff_isLocallySurjective_cofanIsColimitDesc_uliftYoneda_map`

English:
lemma ofArrows_mem_iff_isLocallySurjective_cofanIsColimitDesc_uliftYoneda_map
  proof: by
  let e : Discrete.functor (fun i => uliftYoneda.{w}.obj (X i)) ≅
      Discrete.functor (fun i => shrinkYoneda.{max w v}.obj (X i)) :=
    Discrete.natIso (fun i => uliftYonedaIsoShrinkYoneda.{w}.app (X i.as))
  let hc' := (IsColimit.precomposeInvEquiv e _).2 hc
  rw [ofArrows_mem_iff_isLocallyS

中文:
引理 ofArrows_mem_iff_isLocallySurjective_cofanIsColimitDesc_uliftYoneda_map
  证明: by
  let e : Discrete.functor (fun i => uliftYoneda.{w}.obj (X i)) ≅
      Discrete.functor (fun i => shrinkYoneda.{max w v}.obj (X i)) :=
    Discrete.natIso (fun i => uliftYonedaIsoShrinkYoneda.{w}.app (X i.as))
  let hc' := (IsColimit.precomposeInvEquiv e _).2 hc
  rw [ofArrows_mem_iff_isLocallyS

Depends on / 依赖: Cofan.IsColimit.desc, Discrete, Discrete.functor, Discrete.natIso, IsColimit, IsColimit.precomposeInvEquiv, functor, i.as, natIso, ofArrows_mem_iff_isLocallySurjective_cofanIsColimitDesc_shrinkYoneda_map, precomposeInvEquiv, shrinkYoned, shrinkYoneda, uliftYoneda, uliftYoneda.map, uliftYonedaIsoShrinkYoneda, uliftYonedaIsoShrinkYoneda.hom.app
-/
lemma ofArrows_mem_iff_isLocallySurjective_cofanIsColimitDesc_uliftYoneda_map
    {S : C} {ι : Type*} [Small.{max w v} ι] {X : ι -> C}
    (f : forall i, X i ⟶ S)
    {c : Cofan (fun i => uliftYoneda.{w}.obj (X i))} (hc : IsColimit c) :
    Sieve.ofArrows _ f in J S ↔
      Presheaf.IsLocallySurjective J
        (Cofan.IsColimit.desc hc (fun i => uliftYoneda.{w}.map (f i))) := by
  let e : Discrete.functor (fun i => uliftYoneda.{w}.obj (X i)) ≅
      Discrete.functor (fun i => shrinkYoneda.{max w v}.obj (X i)) :=
    Discrete.natIso (fun i => uliftYonedaIsoShrinkYoneda.{w}.app (X i.as))
  let hc' := (IsColimit.precomposeInvEquiv e _).2 hc
  rw [ofArrows_mem_iff_isLocallySurjective_cofanIsColimitDesc_shrinkYoneda_map.{max w v} J f hc']
  have :
      Cofan.IsColimit.desc hc (fun i => uliftYoneda.map (f i)) ≫
        uliftYonedaIsoShrinkYoneda.hom.app _ =
      Cofan.IsColimit.desc hc' (fun i => shrinkYoneda.map (f i)) :=
    Cofan.IsColimit.hom_ext hc _ _ (fun i => by
      rw [Cofan.IsColimit.fac_assoc]; rw [NatTrans.naturality]; rw [← Cofan.IsColimit.fac hc' (fun i => shrinkYoneda.map (f i)) i]
      simp [Cofan.inj, e])
  rw [← this]; rw [Presheaf.isLocallySurjective_comp_iff J]

/--
lemma `ofArrows_mem_iff_isLocallySurjective_sigmaDesc_shrinkYoneda_map` / 引理 `ofArrows_mem_iff_isLocallySurjective_sigmaDesc_shrinkYoneda_map`

English:
lemma ofArrows_mem_iff_isLocallySurjective_sigmaDesc_shrinkYoneda_map
  statement: [LocallySmall.{w} C]
  proof: ofArrows_mem_iff_isLocallySurjective_cofanIsColimitDesc_shrinkYoneda_map J f
    (coproductIsCoproduct _)

中文:
引理 ofArrows_mem_iff_isLocallySurjective_sigmaDesc_shrinkYoneda_map
  结论: [LocallySmall.{w} C]
  证明: ofArrows_mem_iff_isLocallySurjective_cofanIsColimitDesc_shrinkYoneda_map J f
    (coproductIsCoproduct _)

Depends on / 依赖: coproductIsCoproduct, ofArrows_mem_iff_isLocallySurjective_cofanIsColimitDesc_shrinkYoneda_map
-/
lemma ofArrows_mem_iff_isLocallySurjective_sigmaDesc_shrinkYoneda_map [LocallySmall.{w} C]
    {S : C} {ι : Type*} [Small.{w} ι] {X : ι -> C} (f : forall i, X i ⟶ S) :
    Sieve.ofArrows _ f in J S ↔
      Presheaf.IsLocallySurjective J (Sigma.desc (fun i => shrinkYoneda.{w}.map (f i))) :=
  ofArrows_mem_iff_isLocallySurjective_cofanIsColimitDesc_shrinkYoneda_map J f
    (coproductIsCoproduct _)

/--
lemma `ofArrows_mem_iff_isLocallySurjective_sigmaDesc_uliftYoneda_map` / 引理 `ofArrows_mem_iff_isLocallySurjective_sigmaDesc_uliftYoneda_map`

English:
lemma ofArrows_mem_iff_isLocallySurjective_sigmaDesc_uliftYoneda_map
  proof: ofArrows_mem_iff_isLocallySurjective_cofanIsColimitDesc_uliftYoneda_map J f
    (coproductIsCoproduct _)

中文:
引理 ofArrows_mem_iff_isLocallySurjective_sigmaDesc_uliftYoneda_map
  证明: ofArrows_mem_iff_isLocallySurjective_cofanIsColimitDesc_uliftYoneda_map J f
    (coproductIsCoproduct _)

Depends on / 依赖: coproductIsCoproduct, ofArrows_mem_iff_isLocallySurjective_cofanIsColimitDesc_uliftYoneda_map
-/
lemma ofArrows_mem_iff_isLocallySurjective_sigmaDesc_uliftYoneda_map
    {S : C} {ι : Type*} [Small.{max w v} ι] {X : ι -> C} (f : forall i, X i ⟶ S) :
    Sieve.ofArrows _ f in J S ↔
      Presheaf.IsLocallySurjective J (Sigma.desc (fun i => uliftYoneda.{w}.map (f i))) :=
  ofArrows_mem_iff_isLocallySurjective_cofanIsColimitDesc_uliftYoneda_map J f
    (coproductIsCoproduct _)

end GrothendieckTopology

end CategoryTheory
