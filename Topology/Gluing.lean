/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.CategoryTheory.GlueData
public import Mathlib.Topology.Category.TopCat.Limits.Pullbacks
public import Mathlib.Topology.Category.TopCat.Opens
public import Mathlib.CategoryTheory.Elementwise
public import Mathlib.CategoryTheory.Limits.Types.Coequalizers
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-!
# Gluing Topological spaces

Given a family of gluing data (see `Mathlib/CategoryTheory/GlueData.lean`), we can then glue them
together.

The construction should be "sealed" and considered as a black box, while only using the API
provided.

## Main definitions

* `TopCat.GlueData`: A structure containing the family of gluing data.
* `CategoryTheory.GlueData.glued`: The glued topological space.
    This is defined as the multicoequalizer of `∐ V i j ⇉ ∐ U i`, so that the general colimit API
    can be used.
* `CategoryTheory.GlueData.ι`: The immersion `ι i : U i ⟶ glued` for each `i : ι`.
* `TopCat.GlueData.Rel`: A relation on `Σ i, D.U i` defined by `⟨i, x⟩ ~ ⟨j, y⟩` iff
    `⟨i, x⟩ = ⟨j, y⟩` or `t i j x = y`. See `TopCat.GlueData.ι_eq_iff_rel`.
* `TopCat.GlueData.mk`: A constructor of `GlueData` whose conditions are stated in terms of
  elements rather than subobjects and pullbacks.
* `TopCat.GlueData.ofOpenSubsets`: Given a family of open sets, we may glue them into a new
  topological space. This new space embeds into the original space, and is homeomorphic to it if
  the given family is an open cover (`TopCat.GlueData.openCoverGlueHomeo`).

## Main results

* `TopCat.GlueData.isOpen_iff`: A set in `glued` is open iff its preimage along each `ι i` is
    open.
* `TopCat.GlueData.ι_jointly_surjective`: The `ι i`s are jointly surjective.
* `TopCat.GlueData.rel_equiv`: `Rel` is an equivalence relation.
* `TopCat.GlueData.ι_eq_iff_rel`: `ι i x = ι j y ↔ ⟨i, x⟩ ~ ⟨j, y⟩`.
* `TopCat.GlueData.image_inter`: The intersection of the images of `U i` and `U j` in `glued` is
    `V i j`.
* `TopCat.GlueData.preimage_range`: The preimage of the image of `U i` in `U j` is `V i j`.
* `TopCat.GlueData.preimage_image_eq_image`: The preimage of the image of some `U ⊆ U i` is
    given by XXX.
* `TopCat.GlueData.ι_isOpenEmbedding`: Each of the `ι i`s are open embeddings.

-/

@[expose] public section

noncomputable section

open CategoryTheory TopologicalSpace Topology

universe v u

open CategoryTheory.Limits

namespace TopCat

/-- A family of gluing data consists of
1. An index type `J`
2. An object `U i` for each `i : J`.
3. An object `V i j` for each `i j : J`.
  (Note that this is `J × J → TopCat` rather than `J → J → TopCat` to connect to the
  limits library easier.)
4. An open embedding `f i j : V i j ⟶ U i` for each `i j : ι`.
5. A transition map `t i j : V i j ⟶ V j i` for each `i j : ι`.

such that
6. `f i i` is an isomorphism.
7. `t i i` is the identity.
8. `V i j ×[U i] V i k ⟶ V i j ⟶ V j i` factors through `V j k ×[U j] V j i ⟶ V j i` via some
    `t' : V i j ×[U i] V i k ⟶ V j k ×[U j] V j i`.
    (This merely means that `V i j ∩ V i k ⊆ t i j ⁻¹' (V j i ∩ V j k)`.)
9. `t' i j k ≫ t' j k i ≫ t' k i j = 𝟙 _`.

We can then glue the topological spaces `U i` together by identifying `V i j` with `V j i`, such
that the `U i`'s are open subspaces of the glued space.

Most of the times it would be easier to use the constructor `TopCat.GlueData.mk'` where the
conditions are stated in a less categorical way.
-/
/-
**TopCat.GlueData** 是 Mathlib 中的一个结构，位于命名空间 `TopCat`。
形式化陈述：GlueData extends CategoryTheory.GlueData TopCat where f_open : forall i j,
 IsOpenEmbedding (f i j) f_mono i j
继承自：CategoryTheory.GlueData TopCat。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A family of gluing data consists of
1. An index type `J`
2. An object `U i` for each `i : J`.
3. An object `V i j` for each `i j : J`.
  (Note that this is `J × J → TopCat` rather than `J → J → TopCat` to connect to
 the
  limits library easier.)
4. An open embedding `f i j : V i j ⟶ U i` for each `i j : ι`.
5. A transition map `t i j : V i j ⟶ V j i` for each `i j : ι`.

such that
6. `f i i` is an isomorphism.
7. `t i i` is the identity.
8. `V i j ×[U i] V i k ⟶ V i j ⟶ V j i` factors through `V j k ×[U j] V j i ⟶ V 
j i` via some
    `t' : V i j ×[U i] V i k ⟶ V j k ×[U j] V j i`.
    (This merely means that `V i j ∩ V i k ⊆ t i j ⁻¹' (V j i ∩ V j k)`.)
9. `t' i j k ≫ t' j k i ≫ t' k i j = 𝟙 _`.

We can then glue the topological spaces `U i` together by identifying `V i j` wi
th `V j i`, such
that the `U i`'s are open subspaces of the glued space.

Most of the times it would be easier to use the constructor `TopCat.GlueData.mk'
` where the
conditions are stated in a less categorical way.
-/
structure GlueData extends CategoryTheory.GlueData TopCat where
  f_open : ∀ i j, IsOpenEmbedding (f i j)
  f_mono i j := (TopCat.mono_iff_injective _).mpr (f_open i j).isEmbedding.injective

namespace GlueData

variable (D : GlueData.{u})

local notation "𝖣" => D.toGlueData

/-
**TopCat.GlueData.** 是 Mathlib 中的一个定理，位于命名空间 `TopCat.GlueData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem π_surjective : Function.Surjective 𝖣.π :=
  (TopCat.epi_iff_surjective 𝖣.π).mp inferInstance

set_option backward.isDefEq.respectTransparency false in
/-
**TopCat.GlueData.isOpen_iff** 是 Mathlib 中的一个定理，位于命名空间 `TopCat.GlueData`。
形式化陈述：isOpen_iff (U : Set 𝖣.glued) : IsOpen U ↔ forall i, IsOpen (𝖣.ι i ⁻¹' U)
参数：U : Set 𝖣.glued。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.WalkingMultispan.instSmallOfLOfR`：∀ {J : CategoryT
heory.Limits.MultispanShape} [Small.{t, w} J.L] [Small.{t, w'} J.R],   Small.{t,
 max w' w} (CategoryTheory.Limits.WalkingMul…
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.Multicoequalizer.ι_sigmaπ`：ι_sigmaπ (b) : Sigma.ι 
I.right b ≫ sigmaπ I = π I b
· 使用定理 `CategoryTheory.Limits.Multicoequalizer.instHasCoequalizerFstSigmaMapSndS
igmaMap`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {J : CategoryT
heory.Limits.MultispanShape}   (I : CategoryTheory.Limits.MultispanIn…
· 使用定理 `Homeomorph.isOpen_preimage`：isOpen_preimage (h : X ≃ₜ Y) {s : Set Y} : I
sOpen (h ⁻¹' s) ↔ IsOpen s
· 使用定理 `TopCat.coequalizer_isOpen_iff`：coequalizer_isOpen_iff (U : Set ((coequal
izer f g :) : Type u)) : IsOpen U ↔ IsOpen (coequalizer.π f g ⁻¹' U)
· 使用定理 `TopCat.colimit_isOpen_iff`：colimit_isOpen_iff (F : J ⥤ TopCat.{u}) [HasC
olimit F] (U : Set ((colimit F : _) : Type u)) : IsOpen U ↔ forall j, IsOpen (co
limit.ι F j ⁻¹'…
-/
theorem isOpen_iff (U : Set 𝖣.glued) : IsOpen U ↔ ∀ i, IsOpen (𝖣.ι i ⁻¹' U) := by
  delta CategoryTheory.GlueData.ι
  simp_rw [← Multicoequalizer.ι_sigmaπ 𝖣.diagram]
  rw [← (homeoOfIso (Multicoequalizer.isoCoequalizer 𝖣.diagram).symm).isOpen_preimage]
  rw [coequalizer_isOpen_iff, colimit_isOpen_iff.{u}]
  tauto
/-
**TopCat.GlueData.** 是 Mathlib 中的一个定理，位于命名空间 `TopCat.GlueData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ι_jointly_surjective (x : 𝖣.glued) : ∃ (i : _) (y : D.U i), 𝖣.ι i y = x :=
  𝖣.ι_jointly_surjective (forget TopCat) x

/-- An equivalence relation on `Σ i, D.U i` that holds iff `𝖣.ι i x = 𝖣.ι j y`.
See `TopCat.GlueData.ι_eq_iff_rel`.
-/
/-
**TopCat.GlueData.Rel** 是 Mathlib 中的一个定义，位于命名空间 `TopCat.GlueData`。
形式化陈述：Rel (a b : Σ i, ((D.U i : TopCat) : Type _)) : Prop
参数：a b : Σ i, ((D.U i : TopCat) : Type _)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An equivalence relation on `Σ i, D.U i` that holds iff `𝖣.ι i x = 𝖣.ι j y`.
See `TopCat.GlueData.ι_eq_iff_rel`.
-/
def Rel (a b : Σ i, ((D.U i : TopCat) : Type _)) : Prop :=
  ∃ x : D.V (a.1, b.1), D.f _ _ x = a.2 ∧ D.f _ _ (D.t _ _ x) = b.2
/-
**TopCat.GlueData.rel_equiv** 是 Mathlib 中的一个定理，位于命名空间 `TopCat.GlueData`。
形式化陈述：rel_equiv : Equivalence D.Rel
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GlueData.f_id`：∀ {C : Type u₁} [inst : CategoryTheory.Cat
egory.{v, u₁} C] (self : CategoryTheory.GlueData C) (i : self.J),   CategoryTheo
ry.IsIso (self.f i…
· 使用定理 `CategoryTheory.IsIso.inv_hom_id_apply`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y) [I : CategoryTheory.IsIso f]   {F 
: C → C → Type uF} {carrier…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.GlueData.t_id`：∀ {C : Type u₁} [inst : CategoryTheory.Cat
egory.{v, u₁} C] (self : CategoryTheory.GlueData C) (i : self.J),   self.t i i =
 CategoryTheory.Ca…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.GlueData.t_inv_apply`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v, u₁} C] (D : CategoryTheory.GlueData C) (i j : D.J)   {F : C → C
 → Type uF} {carrier : C …
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePullbacks_of_hasFiniteLimits`：∀ (C : 
Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFini
teLimits C],   CategoryTheory.Limits.HasFiniteWidePul…
· 使用定理 `CategoryTheory.Limits.hasFiniteLimits_of_hasLimits`：∀ (C : Type u) [inst
 : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasLimits C],   Cate
goryTheory.Limits.HasFiniteLimits C
· 使用定理 `TopCat.pullbackIsoProdSubtype_inv_fst_apply`：pullbackIsoProdSubtype_inv_
fst_apply (f : X ⟶ Z) (g : Y ⟶ Z) (x : { p : X × Y // f p.1 = g p.2 }) : pullbac
k.fst f g ((pullbackIsoProdSubtyp…
· 使用定理 `TopCat.pullbackIsoProdSubtype_inv_snd_apply`：pullbackIsoProdSubtype_inv_
snd_apply (f : X ⟶ Z) (g : Y ⟶ Z) (x : { p : X × Y // f p.1 = g p.2 }) : pullbac
k.snd f g ((pullbackIsoProdSubtyp…
· 使用定理 `CategoryTheory.GlueData.f_hasPullback`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v, u₁} C] (self : CategoryTheory.GlueData C) (i j k : self.J),  
 CategoryTheory.Limits.HasP…
· 使用定理 `CategoryTheory.GlueData.t'`：t'_iij (i j : D.J) : D.t' i i j = (pullbackS
ymmetry _ _).hom
· 使用定理 `CategoryTheory.GlueData.t_fac_assoc`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v, u₁} C] (self : CategoryTheory.GlueData C) (i j k : self.J) {Z :
 C}   (h : self.V (j, i) …
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…
· 使用定理 `CategoryTheory.Epi.left_cancellation`：∀ {C : Type u} {inst : CategoryThe
ory.Category.{v, u} C} {X Y : C} {f : X ⟶ Y} [self : CategoryTheory.Epi f] {Z : 
C}   (g h : Y ⟶ Z), Catego…
· 使用定理 `CategoryTheory.StrongEpi.epi`：∀ {C : Type u} {inst : CategoryTheory.Cate
gory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongEpi f],   Cate
goryTheory.Epi f
· 使用定理 `CategoryTheory.strongEpi_of_isIso`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] {P Q : C} (f : P ⟶ Q) [CategoryTheory.IsIso f],   CategoryTh
eory.StrongEpi f
· 使用定理 `CategoryTheory.GlueData.t'_isIso`：∀ {C : Type u₁} [inst : CategoryTheory
.Category.{v, u₁} C] (D : CategoryTheory.GlueData C) (i j k : D.J),   CategoryTh
eory.IsIso (D.t' i j k…
· 使用定理 `CategoryTheory.GlueData.cocycle_assoc`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v, u₁} C] (self : CategoryTheory.GlueData C) (i j k : self.J) {Z
 : C}   (h : CategoryTheory…
· 使用定理 `CategoryTheory.GlueData.t_inv_assoc`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v, u₁} C] (D : CategoryTheory.GlueData C) (i j : D.J) {Z : C}   (h
 : D.V (i, j) ⟶ Z),   Cat…
· 使用定理 `CategoryTheory.congr_fun`：∀ {C : Type u_1} [inst : CategoryTheory.Catego
ry.{v_1, u_1} C] {FC : outParam (C → C → Type u_2)}   {CC : outParam (C → Type w
)} [inst_1 : o…
-/
theorem rel_equiv : Equivalence D.Rel :=
  ⟨fun x => ⟨inv (D.f _ _) x.2, IsIso.inv_hom_id_apply (D.f x.fst x.fst) _,
    by simp [IsIso.inv_hom_id_apply (D.f x.fst x.fst)]⟩, by
    rintro a b ⟨x, e₁, e₂⟩
    exact ⟨D.t _ _ x, e₂, by rw [← e₁, D.t_inv_apply]⟩, by
    rintro ⟨i, a⟩ ⟨j, b⟩ ⟨k, c⟩ ⟨x, e₁, e₂⟩
    rintro ⟨y, e₃, e₄⟩
    let z := (pullbackIsoProdSubtype (D.f j i) (D.f j k)).inv ⟨⟨_, _⟩, e₂.trans e₃.symm⟩
    have eq₁ : (D.t j i) ((pullback.fst _ _ : _ /-(D.f j k)-/ ⟶ D.V (j, i)) z) = x := by
      dsimp only [coe_of, z]
      rw [pullbackIsoProdSubtype_inv_fst_apply, D.t_inv_apply]
    have eq₂ : (pullback.snd _ _ : _ ⟶ D.V _) z = y := pullbackIsoProdSubtype_inv_snd_apply _ _ _
    clear_value z
    use (pullback.fst _ _ : _ ⟶ D.V (i, k)) (D.t' _ _ _ z)
    dsimp +instances only at *
    subst eq₁ eq₂ e₁ e₃ e₄
    have h₁ : D.t' j i k ≫ pullback.fst _ _ ≫ D.f i k = pullback.fst _ _ ≫ D.t j i ≫ D.f i j := by
      rw [← 𝖣.t_fac_assoc]; congr 1; exact pullback.condition
    have h₂ : D.t' j i k ≫ pullback.fst _ _ ≫ D.t i k ≫ D.f k i =
        pullback.snd _ _ ≫ D.t j k ≫ D.f k j := by
      rw [← 𝖣.t_fac_assoc]
      apply @Epi.left_cancellation _ _ _ _ (D.t' k j i)
      rw [𝖣.cocycle_assoc, 𝖣.t_fac_assoc, 𝖣.t_inv_assoc]
      exact pullback.condition.symm
    exact ⟨CategoryTheory.congr_fun h₁ z, CategoryTheory.congr_fun h₂ z⟩⟩

open CategoryTheory.Limits.WalkingParallelPair

set_option backward.isDefEq.respectTransparency false in
/-
**TopCat.GlueData.eqvGen_of_** 是 Mathlib 中的一个定理，位于命名空间 `TopCat.GlueData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eqvGen_of_π_eq
    {x y : ↑(∐ D.U)} (h : 𝖣.π x = 𝖣.π y) :
    Relation.EqvGen
      (Function.Coequalizer.Rel 𝖣.diagram.fstSigmaMap 𝖣.diagram.sndSigmaMap) x y := by
  delta GlueData.π Multicoequalizer.sigmaπ at h
  replace h : coequalizer.π D.diagram.fstSigmaMap D.diagram.sndSigmaMap x =
      coequalizer.π D.diagram.fstSigmaMap D.diagram.sndSigmaMap y :=
    (TopCat.mono_iff_injective (Multicoequalizer.isoCoequalizer 𝖣.diagram).inv).mp
    inferInstance h
  let diagram := parallelPair 𝖣.diagram.fstSigmaMap 𝖣.diagram.sndSigmaMap ⋙ forget _
  have : colimit.ι diagram one x = colimit.ι diagram one y := by
    dsimp only [coequalizer.π] at h
    rw [← ι_preservesColimitIso_hom, ConcreteCategory.forget_map_eq_ofHom, types_comp_apply]
    simp_all
  have :
    (colimit.ι diagram _ ≫ colim.map _ ≫ (colimit.isoColimitCocone _).hom) _ =
      (colimit.ι diagram _ ≫ colim.map _ ≫ (colimit.isoColimitCocone _).hom) _ :=
    (congr_arg
        (colim.map (diagramIsoParallelPair diagram).hom ≫
          (colimit.isoColimitCocone (Types.coequalizerColimit _ _)).hom)
        this :
      _)
  simp only [eqToHom_refl, colimit.ι_map_assoc, diagramIsoParallelPair_hom_app,
    colimit.isoColimitCocone_ι_hom, Category.id_comp] at this
  exact Quot.eq.1 this

set_option backward.isDefEq.respectTransparency.types false in
/-
**TopCat.GlueData.** 是 Mathlib 中的一个定理，位于命名空间 `TopCat.GlueData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ι_eq_iff_rel (i j : D.J) (x : D.U i) (y : D.U j) :
    𝖣.ι i x = 𝖣.ι j y ↔ D.Rel ⟨i, x⟩ ⟨j, y⟩ := by
  constructor
  · delta GlueData.ι
    simp_rw [← Multicoequalizer.ι_sigmaπ]
    intro h
    rw [←
      show _ = Sigma.mk i x from ConcreteCategory.congr_hom (sigmaIsoSigma.{_, u} D.U).inv_hom_id _]
    rw [←
      show _ = Sigma.mk j y from ConcreteCategory.congr_hom (sigmaIsoSigma.{_, u} D.U).inv_hom_id _]
    change InvImage D.Rel (sigmaIsoSigma.{_, u} D.U).hom _ _
    rw [← (InvImage.equivalence _ _ D.rel_equiv).eqvGen_iff]
    refine Relation.EqvGen.mono ?_ _ _ (D.eqvGen_of_π_eq h :)
    rintro _ _ ⟨x⟩
    obtain ⟨⟨⟨i, j⟩, y⟩, rfl⟩ :=
      (ConcreteCategory.bijective_of_isIso (sigmaIsoSigma.{u, u} _).inv).2 x
    unfold InvImage MultispanIndex.fstSigmaMap MultispanIndex.sndSigmaMap
    rw [sigmaIsoSigma_inv_apply]
    -- `rw [← ConcreteCategory.comp_apply]` succeeds but rewrites the wrong expression
    erw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, colimit.ι_desc_assoc,
      ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, colimit.ι_desc_assoc]
      -- previous line now `erw` after https://github.com/leanprover-community/mathlib4/pull/13170
    erw [sigmaIsoSigma_hom_ι_apply, sigmaIsoSigma_hom_ι_apply]
    exact ⟨y, ⟨rfl, rfl⟩⟩
  · rintro ⟨z, e₁, e₂⟩
    dsimp only at *
    -- Porting note: there were `subst e₁` and `subst e₂`, instead of the `rw`
    rw [← e₁, ← e₂] at *
    rw [D.glue_condition_apply]
/-
**TopCat.GlueData.** 是 Mathlib 中的一个定理，位于命名空间 `TopCat.GlueData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ι_injective (i : D.J) : Function.Injective (𝖣.ι i) := by
  intro x y h
  rcases (D.ι_eq_iff_rel _ _ _ _).mp h with ⟨_, e₁, e₂⟩
  · dsimp only at *
    -- Porting note: there were `cases e₁` and `cases e₂`, instead of the `rw`
    rw [← e₁, ← e₂]
    simp
/-
**TopCat.GlueData.** 是 Mathlib 中的一个实例，位于命名空间 `TopCat.GlueData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance ι_mono (i : D.J) : Mono (𝖣.ι i) :=
  (TopCat.mono_iff_injective _).mpr (D.ι_injective _)
/-
**TopCat.GlueData.image_inter** 是 Mathlib 中的一个定理，位于命名空间 `TopCat.GlueData`。
形式化陈述：image_inter (i j : D.J) : Set.range (𝖣.ι i) inter Set.range (𝖣.ι j) = Set.
range (D.f i j ≫ 𝖣.ι _)
参数：i j : D.J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.WalkingMultispan.instSmallOfLOfR`：∀ {J : CategoryT
heory.Limits.MultispanShape} [Small.{t, w} J.L] [Small.{t, w'} J.R],   Small.{t,
 max w' w} (CategoryTheory.Limits.WalkingMul…
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `TopCat.GlueData.ι_eq_iff_rel`：ι_eq_iff_rel (i j : D.J) (x : D.U i) (y : 
D.U j) : 𝖣.ι i x = 𝖣.ι j y ↔ D.Rel ⟨i, x⟩ ⟨j, y⟩
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.GlueData.glue_condition_apply`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v, u₁} C] (D : CategoryTheory.GlueData C)   [inst_1 : Cat
egoryTheory.Limits.HasMulticoequal…
-/
theorem image_inter (i j : D.J) :
    Set.range (𝖣.ι i) ∩ Set.range (𝖣.ι j) = Set.range (D.f i j ≫ 𝖣.ι _) := by
  ext x
  constructor
  · rintro ⟨⟨x₁, eq₁⟩, ⟨x₂, eq₂⟩⟩
    obtain ⟨y, e₁, -⟩ := (D.ι_eq_iff_rel _ _ _ _).mp (eq₁.trans eq₂.symm)
    · subst eq₁
      exact ⟨y, by simp [e₁]⟩
  · rintro ⟨x, hx⟩
    refine ⟨⟨D.f i j x, hx⟩, ⟨D.f j i (D.t _ _ x), ?_⟩⟩
    rw [D.glue_condition_apply]
    exact hx
/-
**TopCat.GlueData.preimage_range** 是 Mathlib 中的一个定理，位于命名空间 `TopCat.GlueData`。
形式化陈述：preimage_range (i j : D.J) : 𝖣.ι j ⁻¹' Set.range (𝖣.ι i) = Set.range (D.f 
j i)
参数：i j : D.J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.WalkingMultispan.instSmallOfLOfR`：∀ {J : CategoryT
heory.Limits.MultispanShape} [Small.{t, w} J.L] [Small.{t, w'} J.R],   Small.{t,
 max w' w} (CategoryTheory.Limits.WalkingMul…
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.preimage_image_eq`：preimage_image_eq {f : α -> β} (s : Set α) (h : I
njective f) : f ⁻¹' f '' s = s
· 使用定理 `TopCat.GlueData.ι_injective`：ι_injective (i : D.J) : Function.Injective 
(𝖣.ι i)
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Set.image_comp`：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g
 '' a = f '' g '' a
· 使用定理 `TopCat.coe_comp`：∀ {X Y Z : TopCat} (f : X ⟶ Y) (g : Y ⟶ Z),   ⇑(Categor
yTheory.ConcreteCategory.hom (CategoryTheory.CategoryStruct.comp f g)) =     ⇑(C
atego…
· 使用定理 `TopCat.GlueData.image_inter`：image_inter (i j : D.J) : Set.range (𝖣.ι i)
 inter Set.range (𝖣.ι j) = Set.range (D.f i j ≫ 𝖣.ι _)
· 使用定理 `Set.preimage_range_inter`：preimage_range_inter {f : α -> β} {s : Set β} 
: f ⁻¹' (range f inter s) = f ⁻¹' s
-/
theorem preimage_range (i j : D.J) : 𝖣.ι j ⁻¹' Set.range (𝖣.ι i) = Set.range (D.f j i) := by
  rw [← Set.preimage_image_eq (Set.range (D.f j i)) (D.ι_injective j), ← Set.image_univ, ←
    Set.image_univ, ← Set.image_comp, ← coe_comp, Set.image_univ, Set.image_univ, ← image_inter,
    Set.preimage_range_inter]
/-
**TopCat.GlueData.preimage_image_eq_image** 是 Mathlib 中的一个定理，位于命名空间 `TopCat.Glue
Data`。
形式化陈述：preimage_image_eq_image (i j : D.J) (U : Set (𝖣.U i)) : 𝖣.ι j ⁻¹' 𝖣.ι i ''
 U = D.f _ _ '' (D.t j i ≫ D.f _ _) ⁻¹' U
参数：i j : D.J；U : Set (𝖣.U i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.WalkingMultispan.instSmallOfLOfR`：∀ {J : CategoryT
heory.Limits.MultispanShape} [Small.{t, w} J.L] [Small.{t, w'} J.R],   Small.{t,
 max w' w} (CategoryTheory.Limits.WalkingMul…
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.preimage_image_eq`：preimage_image_eq {f : α -> β} (s : Set α) (h : I
njective f) : f ⁻¹' f '' s = s
· 使用定理 `TopCat.GlueData.ι_injective`：ι_injective (i : D.J) : Function.Injective 
(𝖣.ι i)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `CategoryTheory.GlueData.glue_condition_apply`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v, u₁} C] (D : CategoryTheory.GlueData C)   [inst_1 : Cat
egoryTheory.Limits.HasMulticoequal…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Set.image_preimage_eq_inter_range`：image_preimage_eq_inter_range {f : α 
-> β} {t : Set β} : f '' f ⁻¹' t = t inter range f
· 使用定理 `Set.inter_eq_self_of_subset_left`：inter_eq_self_of_subset_left {s t : Se
t α} : s subseteq t -> s inter t = s
· 使用定理 `TopCat.GlueData.preimage_range`：preimage_range (i j : D.J) : 𝖣.ι j ⁻¹' S
et.range (𝖣.ι i) = Set.range (D.f j i)
· 使用定理 `Set.preimage_mono`：preimage_mono {s t : Set β} (h : s subseteq t) : f ⁻¹
' s subseteq f ⁻¹' t
· 使用定理 `Set.image_subset_range`：image_subset_range (f : α -> β) (s) : f '' s sub
seteq range f
-/
theorem preimage_image_eq_image (i j : D.J) (U : Set (𝖣.U i)) :
    𝖣.ι j ⁻¹' 𝖣.ι i '' U = D.f _ _ '' (D.t j i ≫ D.f _ _) ⁻¹' U := by
  have : D.f _ _ ⁻¹' 𝖣.ι j ⁻¹' 𝖣.ι i '' U = (D.t j i ≫ D.f _ _) ⁻¹' U := by
    ext x
    conv_rhs => rw [← Set.preimage_image_eq U (D.ι_injective _)]
    simp
  rw [← this, Set.image_preimage_eq_inter_range]
  symm
  apply Set.inter_eq_self_of_subset_left
  rw [← D.preimage_range i j]
  exact Set.preimage_mono (Set.image_subset_range _ _)
/-
**TopCat.GlueData.preimage_image_eq_image'** 是 Mathlib 中的一个定理，位于命名空间 `TopCat.Glu
eData`。
形式化陈述：preimage_image_eq_image' (i j : D.J) (U : Set (𝖣.U i)) : 𝖣.ι j ⁻¹' 𝖣.ι i '
' U = (D.t i j ≫ D.f _ _) '' D.f _ _ ⁻¹' U
参数：i j : D.J；U : Set (𝖣.U i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.WalkingMultispan.instSmallOfLOfR`：∀ {J : CategoryT
heory.Limits.MultispanShape} [Small.{t, w} J.L] [Small.{t, w'} J.R],   Small.{t,
 max w' w} (CategoryTheory.Limits.WalkingMul…
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TopCat.coe_comp`：∀ {X Y Z : TopCat} (f : X ⟶ Y) (g : Y ⟶ Z),   ⇑(Categor
yTheory.ConcreteCategory.hom (CategoryTheory.CategoryStruct.comp f g)) =     ⇑(C
atego…
· 使用定理 `Set.image_comp`：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g
 '' a = f '' g '' a
· 使用定理 `Set.eq_preimage_iff_image_eq`：eq_preimage_iff_image_eq {f : α -> β} (hf 
: Bijective f) {s t} : s = f ⁻¹' t ↔ f '' s = t
· 使用定理 `CategoryTheory.bijective_iff_isIso_ofHom`：bijective_iff_isIso_ofHom {X Y
 : Type u} (f : X -> Y) : Function.Bijective f ↔ IsIso (ofHom f)
· 使用定理 `Set.preimage_preimage`：preimage_preimage {g : β -> γ} {f : α -> β} {s : 
Set γ} : f ⁻¹' g ⁻¹' s = (fun x => g (f x)) ⁻¹' s
· 使用定理 `CategoryTheory.GlueData.t_inv_assoc`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v, u₁} C] (D : CategoryTheory.GlueData C) (i j : D.J) {Z : C}   (h
 : D.V (i, j) ⟶ Z),   Cat…
· 使用定理 `TopCat.GlueData.preimage_image_eq_image`：preimage_image_eq_image (i j : 
D.J) (U : Set (𝖣.U i)) : 𝖣.ι j ⁻¹' 𝖣.ι i '' U = D.f _ _ '' (D.t j i ≫ D.f _ _) ⁻
¹' U
-/
theorem preimage_image_eq_image' (i j : D.J) (U : Set (𝖣.U i)) :
    𝖣.ι j ⁻¹' 𝖣.ι i '' U = (D.t i j ≫ D.f _ _) '' D.f _ _ ⁻¹' U := by
  convert! D.preimage_image_eq_image i j U using 1
  rw [coe_comp, coe_comp, Set.image_comp]
  congr! 1
  rw [← Set.eq_preimage_iff_image_eq, Set.preimage_preimage]
  · change _ = (D.t i j ≫ D.t j i ≫ _) ⁻¹' _
    rw [𝖣.t_inv_assoc]
  rw [bijective_iff_isIso_ofHom]
  apply (forget TopCat).map_isIso
/-
**TopCat.GlueData.open_image_open** 是 Mathlib 中的一个定理，位于命名空间 `TopCat.GlueData`。
形式化陈述：open_image_open (i : D.J) (U : Opens (𝖣.U i)) : IsOpen (𝖣.ι i '' U)
参数：i : D.J；U : Opens (𝖣.U i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.WalkingMultispan.instSmallOfLOfR`：∀ {J : CategoryT
heory.Limits.MultispanShape} [Small.{t, w} J.L] [Small.{t, w'} J.R],   Small.{t,
 max w' w} (CategoryTheory.Limits.WalkingMul…
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TopCat.GlueData.isOpen_iff`：isOpen_iff (U : Set 𝖣.glued) : IsOpen U ↔ fo
rall i, IsOpen (𝖣.ι i ⁻¹' U)
· 使用定理 `TopCat.GlueData.preimage_image_eq_image`：preimage_image_eq_image (i j : 
D.J) (U : Set (𝖣.U i)) : 𝖣.ι j ⁻¹' 𝖣.ι i '' U = D.f _ _ '' (D.t j i ≫ D.f _ _) ⁻
¹' U
· 使用定理 `Topology.IsOpenEmbedding.isOpenMap`：∀ {X : Type u_1} {Y : Type u_2} {f :
 X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.Is
OpenEmbedding f → IsOpen…
· 使用定理 `TopCat.GlueData.f_open`：∀ (self : TopCat.GlueData) (i j : self.J), Topol
ogy.IsOpenEmbedding ⇑(CategoryTheory.ConcreteCategory.hom (self.f i j))
· 使用定理 `Continuous.isOpen_preimage`：∀ {X : Type u} {Y : Type v} [inst : Topologi
calSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   Continuous f → ∀ (s : S
et Y), IsOpen s …
· 使用定理 `ContinuousMap.continuous_toFun`：∀ {X : Type u_1} {Y : Type u_2} [inst : 
TopologicalSpace X] [inst_1 : TopologicalSpace Y] (self : C(X, Y)),   Continuous
 self.toFun
· 使用定理 `TopologicalSpace.Opens.isOpen`：∀ {α : Type u_2} [inst : TopologicalSpace
 α] (U : TopologicalSpace.Opens α), IsOpen ↑U
-/
theorem open_image_open (i : D.J) (U : Opens (𝖣.U i)) : IsOpen (𝖣.ι i '' U) := by
  rw [isOpen_iff]
  intro j
  rw [preimage_image_eq_image]
  apply (D.f_open _ _).isOpenMap
  apply (D.t j i ≫ D.f i j).hom.continuous_toFun.isOpen_preimage
  exact U.isOpen
/-
**TopCat.GlueData.** 是 Mathlib 中的一个定理，位于命名空间 `TopCat.GlueData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ι_isOpenEmbedding (i : D.J) : IsOpenEmbedding (𝖣.ι i) :=
  .of_continuous_injective_isOpenMap (𝖣.ι i).hom.continuous_toFun (D.ι_injective i) fun U h =>
    D.open_image_open i ⟨U, h⟩

/-- A family of gluing data consists of
1. An index type `J`
2. A bundled topological space `U i` for each `i : J`.
3. An open set `V i j ⊆ U i` for each `i j : J`.
4. A transition map `t i j : V i j ⟶ V j i` for each `i j : ι`.

such that
6. `V i i = U i`.
7. `t i i` is the identity.
8. For each `x ∈ V i j ∩ V i k`, `t i j x ∈ V j k`.
9. `t j k (t i j x) = t i k x`.

We can then glue the topological spaces `U i` together by identifying `V i j` with `V j i`.
-/
/-
**TopCat.GlueData.MkCore** 是 Mathlib 中的一个归纳类型，位于命名空间 `TopCat.GlueData`。
形式化陈述：Type (u + 1)
参数：u + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A family of gluing data consists of
1. An index type `J`
2. A bundled topological space `U i` for each `i : J`.
3. An open set `V i j ⊆ U i` for each `i j : J`.
4. A transition map `t i j : V i j ⟶ V j i` for each `i j : ι`.

such that
6. `V i i = U i`.
7. `t i i` is the identity.
8. For each `x ∈ V i j ∩ V i k`, `t i j x ∈ V j k`.
9. `t j k (t i j x) = t i k x`.

We can then glue the topological spaces `U i` together by identifying `V i j` wi
th `V j i`.
-/
structure MkCore where
  /-- The index type `J` -/
  {J : Type u}
  /-- For each `i : J`, a bundled topological space `U i` -/
  U : J → TopCat.{u}
  /-- For each `i j : J`, an open set `V i j ⊆ U i` -/
  V : ∀ i, J → Opens (U i)
  /-- For each `i j : ι`, a transition map `t i j : V i j ⟶ V j i` -/
  t : ∀ i j, (Opens.toTopCat _).obj (V i j) ⟶ (Opens.toTopCat _).obj (V j i)
  V_id : ∀ i, V i i = ⊤
  t_id : ∀ i, ⇑(t i i) = id
  t_inter : ∀ ⦃i j⦄ (k) (x : V i j), ↑x ∈ V i k → (((↑) : (V j i) → (U j)) (t i j x)) ∈ V j k
  cocycle :
    ∀ (i j k) (x : V i j) (h : ↑x ∈ V i k),
      (((↑) : (V k j) → (U k)) (t j k ⟨_, t_inter k x h⟩)) = ((↑) : (V k i) → (U k)) (t i k ⟨x, h⟩)
/-
**TopCat.GlueData.MkCore.t_inv** 是 Mathlib 中的一个定理，位于命名空间 `TopCat.GlueData.MkCore
`。
形式化陈述：∀ (h : TopCat.GlueData.MkCore) (i j : h.J) (x : ↥(h.V j i)),   (CategoryTh
eory.ConcreteCategory.hom (h.t i j)) ((CategoryTheory.ConcreteCategory.hom (h.t 
j i)) x) = x
参数：h : TopCat.GlueData.MkCore；i j : h.J；x : ↥(h.V j i)；CategoryTheory.ConcreteCa
tegory.hom (h.t i j)；(CategoryTheory.ConcreteCategory.hom (h.t j i)) x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopCat.GlueData.MkCore.t_inter`：∀ (self : TopCat.GlueData.MkCore) ⦃i j :
 self.J⦄ (k : self.J) (x : ↥(self.V i j)),   ↑x ∈ self.V i k → ↑((CategoryTheory
.ConcreteCategory.ho…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TopCat.GlueData.MkCore.V_id`：∀ (self : TopCat.GlueData.MkCore) (i : self
.J), self.V i i = ⊤
· 使用定理 `TopCat.GlueData.MkCore.cocycle`：∀ (self : TopCat.GlueData.MkCore) (i j k
 : self.J) (x : ↥(self.V i j)) (h : ↑x ∈ self.V i k),   ↑((CategoryTheory.Concre
teCategory.hom (self…
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `TopCat.GlueData.MkCore.t_id`：∀ (self : TopCat.GlueData.MkCore) (i : self
.J), ⇑(CategoryTheory.ConcreteCategory.hom (self.t i i)) = id
-/
theorem MkCore.t_inv (h : MkCore) (i j : h.J) (x : h.V j i) : h.t i j ((h.t j i) x) = x := by
  have := h.cocycle j i j x ?_
  · rw [h.t_id] at this
    · convert! Subtype.ext this
  rw [h.V_id]
  trivial
/-
**TopCat.GlueData.** 是 Mathlib 中的一个实例，位于命名空间 `TopCat.GlueData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (h : MkCore.{u}) (i j : h.J) : IsIso (h.t i j) := by
  use h.t j i; constructor <;> ext1; exacts [h.t_inv _ _ _, h.t_inv _ _ _]

/-- (Implementation) the restricted transition map to be fed into `TopCat.GlueData`. -/
/-
**TopCat.GlueData.MkCore.t'** 是 Mathlib 中的一个定义，位于命名空间 `TopCat.GlueData.MkCore`。
形式化陈述：(h : TopCat.GlueData.MkCore) →   (i j k : h.J) →     CategoryTheory.Limits
.pullback (h.V i j).inclusion' (h.V i k).inclusion' ⟶       CategoryTheory.Limit
s.pullback (h.V j k).inclusion' (h.V j i).inclusion'
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(Implementation) the restricted transition map to be fed into `TopCat.GlueData`.
-/
def MkCore.t' (h : MkCore.{u}) (i j k : h.J) :
    pullback (h.V i j).inclusion' (h.V i k).inclusion' ⟶
      pullback (h.V j k).inclusion' (h.V j i).inclusion' := by
  refine (pullbackIsoProdSubtype _ _).hom ≫ ofHom ⟨?_, ?_⟩ ≫ (pullbackIsoProdSubtype _ _).inv
  · intro x
    refine ⟨⟨⟨(h.t i j x.1.1).1, ?_⟩, h.t i j x.1.1⟩, rfl⟩
    rcases x with ⟨⟨⟨x, hx⟩, ⟨x', hx'⟩⟩, rfl : x = x'⟩
    exact h.t_inter _ ⟨x, hx⟩ hx'
  fun_prop

set_option backward.isDefEq.respectTransparency false in
/-- This is a constructor of `TopCat.GlueData` whose arguments are in terms of elements and
intersections rather than subobjects and pullbacks. Please refer to `TopCat.GlueData.MkCore` for
details. -/
/-
**TopCat.GlueData.mk'** 是 Mathlib 中的一个定义，位于命名空间 `TopCat.GlueData`。
形式化陈述：mk' (h : MkCore.{u}) : TopCat.GlueData where J
参数：h : MkCore.{u}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is a constructor of `TopCat.GlueData` whose arguments are in terms of eleme
nts and
intersections rather than subobjects and pullbacks. Please refer to `TopCat.Glue
Data.MkCore` for
details.
-/
def mk' (h : MkCore.{u}) : TopCat.GlueData where
  J := h.J
  U := h.U
  V i := (Opens.toTopCat _).obj (h.V i.1 i.2)
  f i j := (h.V i j).inclusion'
  f_id i := (h.V_id i).symm ▸ (Opens.inclusionTopIso (h.U i)).isIso_hom
  f_open := fun i j : h.J => (h.V i j).isOpenEmbedding
  t := h.t
  t_id i := by ext; rw [h.t_id]; rfl
  t' := h.t'
  t_fac i j k := by
    delta MkCore.t'
    rw [Category.assoc, Category.assoc, pullbackIsoProdSubtype_inv_snd, ← Iso.eq_inv_comp,
      pullbackIsoProdSubtype_inv_fst_assoc]
    ext ⟨⟨⟨x, hx⟩, ⟨x', hx'⟩⟩, rfl : x = x'⟩
    rfl
  cocycle i j k := by
    delta MkCore.t'
    simp_rw [← Category.assoc]
    rw [Iso.comp_inv_eq]
    simp only [Iso.inv_hom_id_assoc, Category.assoc, Category.id_comp]
    rw [← Iso.eq_inv_comp, Iso.inv_hom_id]
    ext1 ⟨⟨⟨x, hx⟩, ⟨x', hx'⟩⟩, rfl : x = x'⟩
    dsimp only [Opens.coe_inclusion', hom_comp, hom_ofHom, ContinuousMap.comp_assoc,
      ContinuousMap.comp_apply, ContinuousMap.coe_mk, hom_id, ContinuousMap.id_apply]
    rw [Subtype.mk_eq_mk, Prod.mk_inj, Subtype.mk_eq_mk, Subtype.ext_iff, and_self_iff]
    convert! congr_arg Subtype.val (h.t_inv k i ⟨x, hx'⟩) using 3
    refine Subtype.ext ?_
    exact h.cocycle i j k ⟨x, hx⟩ hx'
  f_mono _ _ := (TopCat.mono_iff_injective _).mpr fun _ _ h => Subtype.ext h

variable {α : Type u} [TopologicalSpace α] {J : Type u} (U : J → Opens α)

/-- We may construct a glue data from a family of open sets. -/
@[simps! toGlueData_J toGlueData_U toGlueData_V toGlueData_t toGlueData_f]
/-
**TopCat.GlueData.ofOpenSubsets** 是 Mathlib 中的一个定义，位于命名空间 `TopCat.GlueData`。
形式化陈述：ofOpenSubsets : TopCat.GlueData.{u}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We may construct a glue data from a family of open sets.
-/
def ofOpenSubsets : TopCat.GlueData.{u} :=
  mk'.{u}
    { J
      U := fun i => (Opens.toTopCat <| TopCat.of α).obj (U i)
      V := fun _ j => (Opens.map <| Opens.inclusion' _).obj (U j)
      t := fun i j => ofHom ⟨fun x => ⟨⟨x.1.1, x.2⟩, x.1.2⟩, by fun_prop⟩
      V_id := fun i => by simp
      t_id := fun i => by ext; rfl
      t_inter := fun _ _ _ _ hx => hx
      cocycle := fun _ _ _ _ _ => rfl }

/-- The canonical map from the glue of a family of open subsets `α` into `α`.
This map is an open embedding (`fromOpenSubsetsGlue_isOpenEmbedding`),
and its range is `⋃ i, (U i : Set α)` (`range_fromOpenSubsetsGlue`).
-/
/-
**TopCat.GlueData.fromOpenSubsetsGlue** 是 Mathlib 中的一个定义，位于命名空间 `TopCat.GlueData
`。
形式化陈述：fromOpenSubsetsGlue : (ofOpenSubsets U).toGlueData.glued ⟶ TopCat.of α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical map from the glue of a family of open subsets `α` into `α`.
This map is an open embedding (`fromOpenSubsetsGlue_isOpenEmbedding`),
and its range is `⋃ i, (U i : Set α)` (`range_fromOpenSubsetsGlue`).
-/
def fromOpenSubsetsGlue : (ofOpenSubsets U).toGlueData.glued ⟶ TopCat.of α :=
  Multicoequalizer.desc _ _ (fun _ => Opens.inclusion' _) (by rintro ⟨i, j⟩; ext x; rfl)

@[simp, elementwise nosimp]
/-
**TopCat.GlueData.** 是 Mathlib 中的一个定理，位于命名空间 `TopCat.GlueData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ι_fromOpenSubsetsGlue (i : J) :
    (ofOpenSubsets U).toGlueData.ι i ≫ fromOpenSubsetsGlue U = Opens.inclusion' _ :=
  Multicoequalizer.π_desc _ _ _ _ _

set_option backward.isDefEq.respectTransparency.types false in
/-
**TopCat.GlueData.fromOpenSubsetsGlue_injective** 是 Mathlib 中的一个定理，位于命名空间 `TopCa
t.GlueData`。
形式化陈述：fromOpenSubsetsGlue_injective : Function.Injective (fromOpenSubsetsGlue U)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.WalkingMultispan.instSmallOfLOfR`：∀ {J : CategoryT
heory.Limits.MultispanShape} [Small.{t, w} J.L] [Small.{t, w'} J.R],   Small.{t,
 max w' w} (CategoryTheory.Limits.WalkingMul…
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `TopCat.GlueData.ι_jointly_surjective`：ι_jointly_surjective (x : 𝖣.glued)
 : exists (i : _) (y : D.U i), 𝖣.ι i y = x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TopCat.GlueData.ι_eq_iff_rel`：ι_eq_iff_rel (i j : D.J) (x : D.U i) (y : 
D.U j) : 𝖣.ι i x = 𝖣.ι j y ↔ D.Rel ⟨i, x⟩ ⟨j, y⟩
· 使用定理 `TopCat.GlueData.ι_fromOpenSubsetsGlue_apply`：∀ {α : Type u} [inst : Topo
logicalSpace α] {J : Type u} (U : J → TopologicalSpace.Opens α) (i : J)   (x : ↑
((TopCat.GlueData.ofOpenSubsets U…
-/
theorem fromOpenSubsetsGlue_injective : Function.Injective (fromOpenSubsetsGlue U) := by
  intro x y e
  obtain ⟨i, ⟨x, hx⟩, rfl⟩ := (ofOpenSubsets U).ι_jointly_surjective x
  obtain ⟨j, ⟨y, hy⟩, rfl⟩ := (ofOpenSubsets U).ι_jointly_surjective y
  rw [ι_fromOpenSubsetsGlue_apply, ι_fromOpenSubsetsGlue_apply] at e
  subst e
  rw [(ofOpenSubsets U).ι_eq_iff_rel]
  exact ⟨⟨⟨x, hx⟩, hy⟩, rfl, rfl⟩

set_option backward.isDefEq.respectTransparency false in
/-
**TopCat.GlueData.fromOpenSubsetsGlue_isOpenMap** 是 Mathlib 中的一个定理，位于命名空间 `TopCa
t.GlueData`。
形式化陈述：fromOpenSubsetsGlue_isOpenMap : IsOpenMap (fromOpenSubsetsGlue U)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.WalkingMultispan.instSmallOfLOfR`：∀ {J : CategoryT
heory.Limits.MultispanShape} [Small.{t, w} J.L] [Small.{t, w'} J.R],   Small.{t,
 max w' w} (CategoryTheory.Limits.WalkingMul…
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isOpen_iff_forall_mem_open`：isOpen_iff_forall_mem_open : IsOpen s ↔ fora
ll x in s, exists t, t subseteq s ∧ IsOpen t ∧ x in t
· 使用定理 `TopCat.GlueData.ι_jointly_surjective`：ι_jointly_surjective (x : 𝖣.glued)
 : exists (i : _) (y : D.U i), 𝖣.ι i y = x
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_preimage_eq_inter_range`：image_preimage_eq_inter_range {f : α 
-> β} {t : Set β} : f '' f ⁻¹' t = t inter range f
· 使用定理 `Topology.IsOpenEmbedding.isOpenMap`：∀ {X : Type u_1} {Y : Type u_2} {f :
 X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.Is
OpenEmbedding f → IsOpen…
· 使用定理 `TopologicalSpace.Opens.isOpenEmbedding`：isOpenEmbedding {X : TopCat.{u}}
 (U : Opens X) : IsOpenEmbedding (inclusion' U)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `TopCat.GlueData.ι_fromOpenSubsetsGlue`：ι_fromOpenSubsetsGlue (i : J) : (
ofOpenSubsets U).toGlueData.ι i ≫ fromOpenSubsetsGlue U = Opens.inclusion' _
· 使用定理 `TopCat.coe_comp`：∀ {X Y Z : TopCat} (f : X ⟶ Y) (g : Y ⟶ Z),   ⇑(Categor
yTheory.ConcreteCategory.hom (CategoryTheory.CategoryStruct.comp f g)) =     ⇑(C
atego…
· 使用定理 `Set.preimage_comp`：preimage_comp {s : Set γ} : g ∘ f ⁻¹' s = f ⁻¹' g ⁻¹'
 s
· 使用定理 `Set.preimage_image_eq`：preimage_image_eq {f : α -> β} (s : Set α) (h : I
njective f) : f ⁻¹' f '' s = s
· 使用定理 `TopCat.GlueData.fromOpenSubsetsGlue_injective`：fromOpenSubsetsGlue_injec
tive : Function.Injective (fromOpenSubsetsGlue U)
· 使用定理 `TopCat.GlueData.isOpen_iff`：isOpen_iff (U : Set 𝖣.glued) : IsOpen U ↔ fo
rall i, IsOpen (𝖣.ι i ⁻¹' U)
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `TopCat.GlueData.ι_fromOpenSubsetsGlue_apply`：∀ {α : Type u} [inst : Topo
logicalSpace α] {J : Type u} (U : J → TopologicalSpace.Opens α) (i : J)   (x : ↑
((TopCat.GlueData.ofOpenSubsets U…
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
-/
theorem fromOpenSubsetsGlue_isOpenMap : IsOpenMap (fromOpenSubsetsGlue U) := by
  intro s hs
  rw [(ofOpenSubsets U).isOpen_iff] at hs
  rw [isOpen_iff_forall_mem_open]
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨i, ⟨x, hx'⟩, rfl⟩ := (ofOpenSubsets U).ι_jointly_surjective x
  use fromOpenSubsetsGlue U '' s ∩ Set.range (@Opens.inclusion' (TopCat.of α) (U i))
  use Set.inter_subset_left
  constructor
  · rw [← Set.image_preimage_eq_inter_range]
    apply (Opens.isOpenEmbedding (X := TopCat.of α) (U i)).isOpenMap
    convert! hs i using 1
    rw [← ι_fromOpenSubsetsGlue, coe_comp, Set.preimage_comp]
    congr! 1
    exact Set.preimage_image_eq _ (fromOpenSubsetsGlue_injective U)
  · refine ⟨Set.mem_image_of_mem _ hx, ?_⟩
    rw [ι_fromOpenSubsetsGlue_apply]
    exact Set.mem_range_self (f := (Opens.inclusion' _).hom) ⟨x, hx'⟩
/-
**TopCat.GlueData.fromOpenSubsetsGlue_isOpenEmbedding** 是 Mathlib 中的一个定理，位于命名空间 
`TopCat.GlueData`。
形式化陈述：fromOpenSubsetsGlue_isOpenEmbedding : IsOpenEmbedding (fromOpenSubsetsGlue
 U)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap`：∀ {X : Type 
u_1} {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [inst_1 : Topologica
lSpace Y],   Continuous f → Function.Injective f…
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.WalkingMultispan.instSmallOfLOfR`：∀ {J : CategoryT
heory.Limits.MultispanShape} [Small.{t, w} J.L] [Small.{t, w'} J.R],   Small.{t,
 max w' w} (CategoryTheory.Limits.WalkingMul…
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `ContinuousMap.continuous_toFun`：∀ {X : Type u_1} {Y : Type u_2} [inst : 
TopologicalSpace X] [inst_1 : TopologicalSpace Y] (self : C(X, Y)),   Continuous
 self.toFun
· 使用定理 `TopCat.GlueData.fromOpenSubsetsGlue_injective`：fromOpenSubsetsGlue_injec
tive : Function.Injective (fromOpenSubsetsGlue U)
· 使用定理 `TopCat.GlueData.fromOpenSubsetsGlue_isOpenMap`：fromOpenSubsetsGlue_isOpe
nMap : IsOpenMap (fromOpenSubsetsGlue U)
-/
theorem fromOpenSubsetsGlue_isOpenEmbedding : IsOpenEmbedding (fromOpenSubsetsGlue U) :=
  .of_continuous_injective_isOpenMap (ContinuousMap.continuous_toFun _)
    (fromOpenSubsetsGlue_injective U) (fromOpenSubsetsGlue_isOpenMap U)

set_option backward.isDefEq.respectTransparency.types false in
/-
**TopCat.GlueData.range_fromOpenSubsetsGlue** 是 Mathlib 中的一个定理，位于命名空间 `TopCat.Gl
ueData`。
形式化陈述：range_fromOpenSubsetsGlue : Set.range (fromOpenSubsetsGlue U) = ⋃ i, (U i 
: Set α)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.WalkingMultispan.instSmallOfLOfR`：∀ {J : CategoryT
heory.Limits.MultispanShape} [Small.{t, w} J.L] [Small.{t, w'} J.R],   Small.{t,
 max w' w} (CategoryTheory.Limits.WalkingMul…
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `TopCat.GlueData.ι_jointly_surjective`：ι_jointly_surjective (x : 𝖣.glued)
 : exists (i : _) (y : D.U i), 𝖣.ι i y = x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TopCat.GlueData.ι_fromOpenSubsetsGlue_apply`：∀ {α : Type u} [inst : Topo
logicalSpace α] {J : Type u} (U : J → TopologicalSpace.Opens α) (i : J)   (x : ↑
((TopCat.GlueData.ofOpenSubsets U…
· 使用定理 `Set.subset_iUnion`：subset_iUnion : forall (s : ι -> Set β) (i : ι), s i 
subseteq ⋃ i, s i
-/
theorem range_fromOpenSubsetsGlue : Set.range (fromOpenSubsetsGlue U) = ⋃ i, (U i : Set α) := by
  ext
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨i, ⟨x, hx'⟩, rfl⟩ := (ofOpenSubsets U).ι_jointly_surjective x
    rw [ι_fromOpenSubsetsGlue_apply]
    exact Set.subset_iUnion _ i hx'
  · rintro ⟨_, ⟨i, rfl⟩, hx⟩
    rename_i x
    exact ⟨(ofOpenSubsets U).toGlueData.ι i ⟨x, hx⟩, ι_fromOpenSubsetsGlue_apply _ _ _⟩

/-- The gluing of an open cover is homeomorphic to the original space. -/
/-
**TopCat.GlueData.openCoverGlueHomeo** 是 Mathlib 中的一个定义，位于命名空间 `TopCat.GlueData`
。
形式化陈述：openCoverGlueHomeo (h : ⋃ i, (U i : Set α) = Set.univ) : (ofOpenSubsets U)
.toGlueData.glued ≃ₜ α
参数：h : ⋃ i, (U i : Set α) = Set.univ。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `TopCat.GlueData.fromOpenSubsetsGlue_isOpenMap`：fromOpenSubsetsGlue_isOpe
nMap : IsOpenMap (fromOpenSubsetsGlue U)

--- 原说明 ---
The gluing of an open cover is homeomorphic to the original space.
-/
def openCoverGlueHomeo (h : ⋃ i, (U i : Set α) = Set.univ) :
    (ofOpenSubsets U).toGlueData.glued ≃ₜ α :=
  Equiv.toHomeomorphOfContinuousOpen
    (Equiv.ofBijective (fromOpenSubsetsGlue U)
      ⟨fromOpenSubsetsGlue_injective U,
        Set.range_eq_univ.mp ((range_fromOpenSubsetsGlue U).symm ▸ h)⟩)
    (fromOpenSubsetsGlue U).hom.2 (fromOpenSubsetsGlue_isOpenMap U)

end GlueData

end TopCat

