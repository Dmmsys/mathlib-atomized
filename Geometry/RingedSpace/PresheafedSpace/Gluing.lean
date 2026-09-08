/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Topology.Gluing
public import Mathlib.Geometry.RingedSpace.OpenImmersion
public import Mathlib.Geometry.RingedSpace.LocallyRingedSpace.HasColimits

/-!
# Gluing structured spaces

Given a family of gluing data of structured spaces (presheafed spaces, sheafed spaces, or locally
ringed spaces), we may glue them together.

The construction should be "sealed" and considered as a black box, while only using the API
provided.

## Main definitions

* `AlgebraicGeometry.PresheafedSpace.GlueData`: A structure containing the family of gluing data.
* `CategoryTheory.GlueData.glued`: The glued presheafed space.
  This is defined as the multicoequalizer of `∐ V i j ⇉ ∐ U i`, so that the general colimit API
  can be used.
* `CategoryTheory.GlueData.ι`: The immersion `ι i : U i ⟶ glued` for each `i : J`.

## Main results

* `AlgebraicGeometry.PresheafedSpace.GlueData.ιIsOpenImmersion`: The map `ι i : U i ⟶ glued`
  is an open immersion for each `i : J`.
* `AlgebraicGeometry.PresheafedSpace.GlueData.ι_jointly_surjective` : The underlying maps of
  `ι i : U i ⟶ glued` are jointly surjective.
* `AlgebraicGeometry.PresheafedSpace.GlueData.vPullbackConeIsLimit` : `V i j` is the pullback
  (intersection) of `U i` and `U j` over the glued space.

Analogous results are also provided for `SheafedSpace` and `LocallyRingedSpace`.

## Implementation details

Almost the whole file is dedicated to showing that `ι i` is an open immersion. The fact that
this is an open embedding of topological spaces follows from `Mathlib/Topology/Gluing.lean`, and it
remains to construct `Γ(𝒪_{U_i}, U) ⟶ Γ(𝒪_X, ι i '' U)` for each `U ⊆ U i`.
Since `Γ(𝒪_X, ι i '' U)` is the limit of `diagram_over_open`, the components of the structure
sheaves of the spaces in the gluing diagram, we need to construct a map
`ιInvApp_π_app : Γ(𝒪_{U_i}, U) ⟶ Γ(𝒪_V, U_V)` for each `V` in the gluing diagram.

We will refer to ![this diagram](https://i.imgur.com/P0phrwr.png) in the following docstrings.
The `X` is the glued space, and the dotted arrow is a partial inverse guaranteed by the fact
that it is an open immersion. The map `Γ(𝒪_{U_i}, U) ⟶ Γ(𝒪_{U_j}, _)` is given by the composition
of the red arrows, and the map `Γ(𝒪_{U_i}, U) ⟶ Γ(𝒪_{V_{jk}}, _)` is given by the composition of the
blue arrows. To lift this into a map from `Γ(𝒪_X, ι i '' U)`, we also need to show that these
commute with the maps in the diagram (the green arrows), which is just a lengthy diagram-chasing.

-/

@[expose] public section


noncomputable section

open TopologicalSpace CategoryTheory Opposite Topology

open CategoryTheory.Limits AlgebraicGeometry.PresheafedSpace

open AlgebraicGeometry.PresheafedSpace.IsOpenImmersion

open CategoryTheory.GlueData

namespace AlgebraicGeometry

universe v u

variable (C : Type u) [Category.{v} C]

namespace PresheafedSpace

/-- A family of gluing data consists of
1. An index type `J`
2. A presheafed space `U i` for each `i : J`.
3. A presheafed space `V i j` for each `i j : J`.
   (Note that this is `J × J → PresheafedSpace C` rather than `J → J → PresheafedSpace C` to
   connect to the limits library more easily.)
4. An open immersion `f i j : V i j ⟶ U i` for each `i j : J`.
5. A transition map `t i j : V i j ⟶ V j i` for each `i j : J`.

such that
6. `f i i` is an isomorphism.
7. `t i i` is the identity.
8. `V i j ×[U i] V i k ⟶ V i j ⟶ V j i` factors through `V j k ×[U j] V j i ⟶ V j i` via some
   `t' : V i j ×[U i] V i k ⟶ V j k ×[U j] V j i`.
9. `t' i j k ≫ t' j k i ≫ t' k i j = 𝟙 _`.

We can then glue the spaces `U i` together by identifying `V i j` with `V j i`, such
that the `U i`'s are open subspaces of the glued space.
-/
/-
**AlgebraicGeometry.PresheafedSpace.GlueData** 是 Mathlib 中的一个归纳类型，位于命名空间 `Algebr
aicGeometry.PresheafedSpace`。
形式化陈述：(C : Type u) → [CategoryTheory.Category.{v, u} C] → Type (max u (v + 1))
参数：v + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A family of gluing data consists of
1. An index type `J`
2. A presheafed space `U i` for each `i : J`.
3. A presheafed space `V i j` for each `i j : J`.
   (Note that this is `J × J → PresheafedSpace C` rather than `J → J → Presheafe
dSpace C` to
   connect to the limits library more easily.)
4. An open immersion `f i j : V i j ⟶ U i` for each `i j : J`.
5. A transition map `t i j : V i j ⟶ V j i` for each `i j : J`.

such that
6. `f i i` is an isomorphism.
7. `t i i` is the identity.
8. `V i j ×[U i] V i k ⟶ V i j ⟶ V j i` factors through `V j k ×[U j] V j i ⟶ V 
j i` via some
   `t' : V i j ×[U i] V i k ⟶ V j k ×[U j] V j i`.
9. `t' i j k ≫ t' j k i ≫ t' k i j = 𝟙 _`.

We can then glue the spaces `U i` together by identifying `V i j` with `V j i`, 
such
that the `U i`'s are open subspaces of the glued space.
-/
structure GlueData extends CategoryTheory.GlueData (PresheafedSpace.{v, u, v} C) where
  f_open : ∀ i j, IsOpenImmersion (f i j)

attribute [instance] GlueData.f_open

namespace GlueData

variable {C}
variable (D : GlueData.{v, u} C)

local notation "𝖣" => D.toGlueData

local notation "π₁ " i ", " j ", " k => pullback.fst (D.f i j) (D.f i k)

local notation "π₂ " i ", " j ", " k => pullback.snd (D.f i j) (D.f i k)

set_option quotPrecheck false
local notation "π₁⁻¹ " i ", " j ", " k =>
  (PresheafedSpace.IsOpenImmersion.pullbackFstOfRight (D.f i j) (D.f i k)).invApp

set_option quotPrecheck false
local notation "π₂⁻¹ " i ", " j ", " k =>
  (PresheafedSpace.IsOpenImmersion.pullbackSndOfLeft (D.f i j) (D.f i k)).invApp

/-- The glue data of topological spaces associated to a family of glue data of PresheafedSpaces. -/
/-
**AlgebraicGeometry.PresheafedSpace.GlueData.toTopGlueData** 是 Mathlib 中的一个缩写定义，
位于命名空间 `AlgebraicGeometry.PresheafedSpace.GlueData`。
形式化陈述：toTopGlueData : TopCat.GlueData
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The glue data of topological spaces associated to a family of glue data of Presh
eafedSpaces.
-/
abbrev toTopGlueData : TopCat.GlueData :=
  { f_open := fun i j => (D.f_open i j).base_open
    toGlueData := 𝖣.mapGlueData (forget C) }

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.PresheafedSpace.GlueData.** 是 Mathlib 中的一个定理，位于命名空间 `Algebra
icGeometry.PresheafedSpace.GlueData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ι_isOpenEmbedding [HasLimits C] (i : D.J) : IsOpenEmbedding (𝖣.ι i).base := by
  rw [← show _ = (𝖣.ι i).base from 𝖣.ι_gluedIso_inv (PresheafedSpace.forget _) _, TopCat.coe_comp]
  exact (TopCat.homeoOfIso (𝖣.gluedIso (PresheafedSpace.forget _)).symm).isOpenEmbedding.comp
      (D.toTopGlueData.ι_isOpenEmbedding i)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.PresheafedSpace.GlueData.pullback_base** 是 Mathlib 中的一个定理，位于
命名空间 `AlgebraicGeometry.PresheafedSpace.GlueData`。
形式化陈述：pullback_base (i j k : D.J) (S : Set (D.V (i, j)).carrier) : (π₂ i, j, k) 
'' (π₁ i, j, k) ⁻¹' S = D.f i k ⁻¹' D.f i j '' S
参数：i j k : D.J；S : Set (D.V (i, j)).carrier。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.PresheafedSpace.GlueData.f_open`：∀ {C : Type u} [inst 
: CategoryTheory.Category.{v, u} C] (self : AlgebraicGeometry.PresheafedSpace.Gl
ueData C)   (i j : self.J), AlgebraicGe…
· 使用定理 `CategoryTheory.GlueData.instHasPullbackMapF`：∀ {C : Type u₁} [inst : Cat
egoryTheory.Category.{v, u₁} C] {C' : Type u₂} [inst_1 : CategoryTheory.Category
.{v, u₂} C']   (D : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.PreservesPullback.iso_hom_fst`：∀ {C : Type u₁} [in
st : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.
Category.{v₂, u₂} D]   (G : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.PreservesPullback.iso_hom_snd`：∀ {C : Type u₁} [in
st : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.
Category.{v₂, u₂} D]   (G : CategoryTheor…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `TopCat.coe_comp`：∀ {X Y Z : TopCat} (f : X ⟶ Y) (g : Y ⟶ Z),   ⇑(Categor
yTheory.ConcreteCategory.hom (CategoryTheory.CategoryStruct.comp f g)) =     ⇑(C
atego…
· 使用定理 `Set.image_comp`：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g
 '' a = f '' g '' a
· 使用定理 `Set.preimage_comp`：preimage_comp {s : Set γ} : g ∘ f ⁻¹' s = f ⁻¹' g ⁻¹'
 s
· 使用定理 `Set.image_preimage_eq`：image_preimage_eq {f : α -> β} (s : Set β) (h : S
urjective f) : f '' f ⁻¹' s = s
· 使用定理 `TopCat.epi_iff_surjective`：epi_iff_surjective {X Y : TopCat.{u}} (f : X 
⟶ Y) : Epi f ↔ Function.Surjective f
· 使用定理 `CategoryTheory.instEffectiveEpiOfIsIso`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],  
 CategoryTheory.EffectiveEpi…
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
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
· 使用定理 `TopCat.pullback_snd_image_fst_preimage`：pullback_snd_image_fst_preimage 
(f : X ⟶ Z) (g : Y ⟶ Z) (U : Set X) : (pullback.snd f g) '' (pullback.fst f g) ⁻
¹' U = g ⁻¹' f '' U
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pullback_base (i j k : D.J) (S : Set (D.V (i, j)).carrier) :
    (π₂ i, j, k) '' (π₁ i, j, k) ⁻¹' S = D.f i k ⁻¹' D.f i j '' S := by
  have eq₁ : _ = (π₁ i, j, k).base := PreservesPullback.iso_hom_fst (forget C) _ _
  have eq₂ : _ = (π₂ i, j, k).base := PreservesPullback.iso_hom_snd (forget C) _ _
  rw [← eq₁, ← eq₂, TopCat.coe_comp, Set.image_comp, TopCat.coe_comp, Set.preimage_comp,
    Set.image_preimage_eq]
  · simp only [forget_obj, forget_map, TopCat.pullback_snd_image_fst_preimage]
  rw [← TopCat.epi_iff_surjective]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- The red and the blue arrows in ![this diagram](https://i.imgur.com/0GiBUh6.png) commute. -/
@[simp, reassoc]
/-
**AlgebraicGeometry.PresheafedSpace.GlueData.f_invApp_f_app** 是 Mathlib 中的一个定理，位
于命名空间 `AlgebraicGeometry.PresheafedSpace.GlueData`。
形式化陈述：f_invApp_f_app (i j k : D.J) (U : Opens (D.V (i, j)).carrier) : (D.f_open 
i j).invApp _ U ≫ (D.f i k).c.app _ = (π₁ i, j, k).c.app (op U) ≫ (π₂⁻¹ i, j, k)
 (unop _) ≫ (D.V _).presheaf.map (eqToHom (by delta IsOpenImmersion.opensFunctor
 IsOpenEmbedding.functor dsimp only [Functor.op, IsOpenMap.functor, Opens.map, u
nop_op] congr apply pullback_base))
参数：i j k : D.J；U : Opens (D.V (i, j)).carrier。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.PresheafedSpace.GlueData.f_open`：∀ {C : Type u} [inst 
: CategoryTheory.Category.{v, u} C] (self : AlgebraicGeometry.PresheafedSpace.Gl
ueData C)   (i j : self.J), AlgebraicGe…
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…
· 使用定理 `AlgebraicGeometry.PresheafedSpace.congr_app`：congr_app {X Y : Presheafed
Space C} {α β : X ⟶ Y} (h : α = β) (U) : α.c.app U = β.c.app U ≫ X.presheaf.map 
(eqToHom (by subst h; rfl))
· 使用定理 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.instIsIsoInvApp`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : AlgebraicGeometry.Pre
sheafedSpace C} (f : X ⟶ Y)   [H : AlgebraicGeometry.Pr…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.instEffectiveEpiOfIsIso`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],  
 CategoryTheory.EffectiveEpi…
· 使用定理 `CategoryTheory.IsIso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y) [I : CategoryTheory.IsIso f] {Z : 
C}   (h : Y ⟶ Z), CategoryT…
· 使用定理 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.inv_invApp`：inv_invApp
 (U : Opens X) : inv (H.invApp _ U) = f.c.app (op (opensFunctor f |>.obj U)) ≫ X
.presheaf.map (eqToHom (by simp [Opens.map_def, Se…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.NatTrans.naturality_assoc`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
· 使用定理 `CategoryTheory.Functor.map_comp_assoc`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v_1, u₁} C] {D : Type u₂}   [inst_1 : CategoryTheory.Category.{v
_2, u₂} D] (F : CategoryThe…
· 使用定理 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.inv_naturality_assoc`：
∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : AlgebraicGeometr
y.PresheafedSpace C} (f : X ⟶ Y)   [H : AlgebraicGeometry.Pr…
· 使用定理 `Set.image_preimage_subset`：image_preimage_subset (f : α -> β) (s : Set β
) : f '' f ⁻¹' s subseteq s
· 使用定理 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.app_invApp_assoc`：∀ {C
 : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : AlgebraicGeometry.Pr
esheafedSpace C} (f : X ⟶ Y)   [H : AlgebraicGeometry.Pr…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…

--- 原说明 ---
The red and the blue arrows in ![this diagram](https://i.imgur.com/0GiBUh6.png) 
commute.
-/
theorem f_invApp_f_app (i j k : D.J) (U : Opens (D.V (i, j)).carrier) :
    (D.f_open i j).invApp _ U ≫ (D.f i k).c.app _ =
      (π₁ i, j, k).c.app (op U) ≫
        (π₂⁻¹ i, j, k) (unop _) ≫
          (D.V _).presheaf.map
            (eqToHom
              (by
                delta IsOpenImmersion.opensFunctor IsOpenEmbedding.functor
                dsimp only [Functor.op, IsOpenMap.functor, Opens.map, unop_op]
                congr
                apply pullback_base)) := by
  have := PresheafedSpace.congr_app (@pullback.condition _ _ _ _ _ (D.f i j) (D.f i k) _)
  dsimp only [comp_c_app] at this
  rw [← cancel_epi (inv ((D.f_open i j).invApp _ U)), IsIso.inv_hom_id_assoc,
    IsOpenImmersion.inv_invApp]
  simp_rw [Category.assoc]
  erw [(π₁ i, j, k).c.naturality_assoc, reassoc_of% this, ← Functor.map_comp_assoc,
    IsOpenImmersion.inv_naturality_assoc, IsOpenImmersion.app_invApp_assoc, ←
    (D.V (i, k)).presheaf.map_comp, ← (D.V (i, k)).presheaf.map_comp]
  convert! (Category.comp_id _).symm
  erw [(D.V (i, k)).presheaf.map_id]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- We can prove the `eq` along with the lemma. Thus this is bundled together here, and the
lemma itself is separated below.
-/
/-
**AlgebraicGeometry.PresheafedSpace.GlueData.snd_invApp_t_app'** 是 Mathlib 中的一个定
理，位于命名空间 `AlgebraicGeometry.PresheafedSpace.GlueData`。
形式化陈述：snd_invApp_t_app' (i j k : D.J) (U : Opens (pullback (D.f i j) (D.f i k)).
carrier) : exists eq, (π₂⁻¹ i, j, k) U ≫ (D.t k i).c.app _ ≫ (D.V (k, i)).preshe
af.map (eqToHom eq) = (D.t' k i j).c.app _ ≫ (π₁⁻¹ k, j, i) (unop _)
参数：i j k : D.J；U : Opens (pullback (D.f i j) (D.f i k)).carrier。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.PresheafedSpace.GlueData.f_open`：∀ {C : Type u} [inst 
: CategoryTheory.Category.{v, u} C] (self : AlgebraicGeometry.PresheafedSpace.Gl
ueData C)   (i j : self.J), AlgebraicGe…
· 使用定理 `CategoryTheory.GlueData.f_hasPullback`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v, u₁} C] (self : CategoryTheory.GlueData C) (i j k : self.J),  
 CategoryTheory.Limits.HasP…
· 使用定理 `CategoryTheory.GlueData.t'`：t'_iij (i j : D.J) : D.t' i i j = (pullbackS
ymmetry _ _).hom
· 使用定理 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.base_open`：∀ {C : Type
 u} {inst : CategoryTheory.Category.{v, u} C} {X Y : AlgebraicGeometry.Presheafe
dSpace C} {f : X ⟶ Y}   [self : AlgebraicGeometry…
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
· 使用定理 `ContinuousMap.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y] (f : C(X, Y)), Continuous ⇑f
· 使用定理 `TopologicalSpace.Opens.isOpen`：∀ {α : Type u_2} [inst : TopologicalSpace
 α] (U : TopologicalSpace.Opens α), IsOpen ↑U
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.GlueData.t_fac`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v, u₁} C] (self : CategoryTheory.GlueData C) (i j k : self.J),   Categor
yTheory.CategoryStr…
· 使用定理 `CategoryTheory.GlueData.t'_isIso`：∀ {C : Type u₁} [inst : CategoryTheory
.Category.{v, u₁} C] (D : CategoryTheory.GlueData C) (i j k : D.J),   CategoryTh
eory.IsIso (D.t' i j k…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsIso.inv_comp_eq`：inv_comp_eq (α : X ⟶ Y) [IsIso α] {f :
 X ⟶ Z} {g : Y ⟶ Z} : inv α ≫ f = g ↔ f = α ≫ g
· 使用定理 `Set.image_comp`：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g
 '' a = f '' g '' a
· 使用定理 `Set.preimage_image_eq`：preimage_image_eq {f : α -> β} (s : Set α) (h : I
njective f) : f ⁻¹' f '' s = s
· 使用定理 `Function.HasLeftInverse.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : 
α → β}, Function.HasLeftInverse f → Function.Injective f
· 使用定理 `CategoryTheory.ConcreteCategory.comp_apply`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (
C → Type w)}   {inst_1 : outPara…
· 使用定理 `AlgebraicGeometry.PresheafedSpace.comp_base`：comp_base {X Y Z : Presheaf
edSpace C} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).base = f.base ≫ g.base
· 使用定理 `CategoryTheory.GlueData.t_inv`：t_inv (i j : D.J) : D.t i j ≫ D.t j i = 𝟙
 _
· 使用定理 `AlgebraicGeometry.PresheafedSpace.id_base`：id_base (X : PresheafedSpace 
C) : (𝟙 X : X ⟶ X).base = 𝟙 (X : TopCat)
· 使用定理 `CategoryTheory.ConcreteCategory.id_apply`：∀ {C : Type u} {inst : Categor
yTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (C 
→ Type w)}   {inst_1 : outPara…
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `Set.image_eq_preimage_of_inverse`：image_eq_preimage_of_inverse {f : α ->
 β} {g : β -> α} (h₁ : LeftInverse g f) (h₂ : RightInverse g f) : image f = prei
mage g
· 使用定理 `CategoryTheory.IsIso.inv_hom_id`：inv_hom_id (f : X ⟶ Y) [I : IsIso f] : 
inv f ≫ f = 𝟙 Y
· 使用定理 `CategoryTheory.IsIso.hom_inv_id`：hom_inv_id (f : X ⟶ Y) [I : IsIso f] : 
f ≫ inv f = 𝟙 X
· 使用定理 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.instIsIsoInvApp`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : AlgebraicGeometry.Pre
sheafedSpace C} (f : X ⟶ Y)   [H : AlgebraicGeometry.Pr…
· 使用定理 `CategoryTheory.IsIso.eq_inv_comp`：eq_inv_comp (α : X ⟶ Y) [IsIso α] {f :
 X ⟶ Z} {g : Y ⟶ Z} : g = inv α ≫ f ↔ α ≫ g = f
· 使用定理 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.inv_invApp`：inv_invApp
 (U : Opens X) : inv (H.invApp _ U) = f.c.app (op (opensFunctor f |>.obj U)) ≫ X
.presheaf.map (eqToHom (by simp [Opens.map_def, Se…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.NatTrans.naturality_assoc`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
（共 47 条，此处仅展示前 30 条）

--- 原说明 ---
We can prove the `eq` along with the lemma. Thus this is bundled together here, 
and the
lemma itself is separated below.
-/
theorem snd_invApp_t_app' (i j k : D.J) (U : Opens (pullback (D.f i j) (D.f i k)).carrier) :
    ∃ eq,
      (π₂⁻¹ i, j, k) U ≫ (D.t k i).c.app _ ≫ (D.V (k, i)).presheaf.map (eqToHom eq) =
        (D.t' k i j).c.app _ ≫ (π₁⁻¹ k, j, i) (unop _) := by
  fconstructor
  -- Porting note: I don't know what the magic was in Lean3 proof, it just skipped the proof of `eq`
  · delta IsOpenImmersion.opensFunctor IsOpenEmbedding.functor
    dsimp only [Functor.op, Opens.map_def, IsOpenMap.functor, unop_op, Opens.coe_mk]
    congr 2
    have := (𝖣.t_fac k i j).symm
    rw [← IsIso.inv_comp_eq] at this
    replace this := (congr_arg ((PresheafedSpace.Hom.base ·)) this).symm
    replace this := congr_arg (TopCat.Hom.hom ·) this
    replace this := congr_arg (ContinuousMap.toFun ·) this
    dsimp at this
    rw [this, Set.image_comp, Set.image_comp, Set.preimage_image_eq]
    swap
    · refine Function.HasLeftInverse.injective ⟨(D.t i k).base, fun x => ?_⟩
      rw [← ConcreteCategory.comp_apply, ← comp_base, D.t_inv, id_base, ConcreteCategory.id_apply]
    refine congr_arg (_ '' ·) ?_
    refine congr_fun ?_ _
    refine Set.image_eq_preimage_of_inverse ?_ ?_
    · intro x
      rw [← ConcreteCategory.comp_apply, ← comp_base, IsIso.inv_hom_id, id_base,
        ConcreteCategory.id_apply]
    · intro x
      rw [← ConcreteCategory.comp_apply, ← comp_base, IsIso.hom_inv_id, id_base,
        ConcreteCategory.id_apply]
  · rw [← IsIso.eq_inv_comp, IsOpenImmersion.inv_invApp, Category.assoc,
      (D.t' k i j).c.naturality_assoc]
    simp_rw [← Category.assoc]
    dsimp
    rw [← comp_c_app, congr_app (D.t_fac k i j), comp_c_app]
    dsimp
    simp_rw [Category.assoc]
    rw [IsOpenImmersion.inv_naturality, IsOpenImmersion.inv_naturality_assoc,
      IsOpenImmersion.app_inv_app'_assoc]
    · simp_rw [← (𝖣.V (k, i)).presheaf.map_comp]; rfl
    rintro x ⟨y, -, eq⟩
    replace eq := ConcreteCategory.congr_arg (𝖣.t i k).base eq
    change ((π₂ i, j, k) ≫ D.t i k).base y = (D.t k i ≫ D.t i k).base x at eq
    rw [𝖣.t_inv, id_base, TopCat.id_app] at eq
    subst eq
    use (inv (D.t' k i j)).base y
    change (inv (D.t' k i j) ≫ π₁ k, i, j).base y = _
    congr 3
    rw [IsIso.inv_comp_eq, 𝖣.t_fac_assoc, 𝖣.t_inv, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in -- Needed in ιInvApp
/-- The red and the blue arrows in ![this diagram](https://i.imgur.com/q6X1GJ9.png) commute. -/
@[simp, reassoc]
/-
**AlgebraicGeometry.PresheafedSpace.GlueData.snd_invApp_t_app** 是 Mathlib 中的一个定理
，位于命名空间 `AlgebraicGeometry.PresheafedSpace.GlueData`。
形式化陈述：snd_invApp_t_app (i j k : D.J) (U : Opens (pullback (D.f i j) (D.f i k)).c
arrier) : (π₂⁻¹ i, j, k) U ≫ (D.t k i).c.app _ = (D.t' k i j).c.app _ ≫ (π₁⁻¹ k,
 j, i) (unop _) ≫ (D.V (k, i)).presheaf.map (eqToHom (D.snd_invApp_t_app' i j k 
U).choose.symm)
参数：i j k : D.J；U : Opens (pullback (D.f i j) (D.f i k)).carrier。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.PresheafedSpace.GlueData.f_open`：∀ {C : Type u} [inst 
: CategoryTheory.Category.{v, u} C] (self : AlgebraicGeometry.PresheafedSpace.Gl
ueData C)   (i j : self.J), AlgebraicGe…
· 使用定理 `CategoryTheory.GlueData.f_hasPullback`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v, u₁} C] (self : CategoryTheory.GlueData C) (i j k : self.J),  
 CategoryTheory.Limits.HasP…
· 使用定理 `CategoryTheory.GlueData.t'`：t'_iij (i j : D.J) : D.t' i i j = (pullbackS
ymmetry _ _).hom
· 使用定理 `AlgebraicGeometry.PresheafedSpace.GlueData.snd_invApp_t_app'`：snd_invApp
_t_app' (i j k : D.J) (U : Opens (pullback (D.f i j) (D.f i k)).carrier) : exist
s eq, (π₂⁻¹ i, j, k) U ≫ (D.t k i).c.app _ ≫ (D.V …
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `CategoryTheory.eqToHom_map`：eqToHom_map (F : C ⥤ D) {X Y : C} (p : X = Y
) : F.map (eqToHom p) = eqToHom (congr_arg F.obj p)
· 使用定理 `CategoryTheory.eqToHom_trans`：eqToHom_trans {X Y Z : C} (p : X = Y) (q :
 Y = Z) : eqToHom p ≫ eqToHom q = eqToHom (p.trans q)
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The red and the blue arrows in ![this diagram](https://i.imgur.com/q6X1GJ9.png) 
commute.
-/
theorem snd_invApp_t_app (i j k : D.J) (U : Opens (pullback (D.f i j) (D.f i k)).carrier) :
    (π₂⁻¹ i, j, k) U ≫ (D.t k i).c.app _ =
      (D.t' k i j).c.app _ ≫
        (π₁⁻¹ k, j, i) (unop _) ≫
          (D.V (k, i)).presheaf.map (eqToHom (D.snd_invApp_t_app' i j k U).choose.symm) := by
  have e := (D.snd_invApp_t_app' i j k U).choose_spec
  replace e := reassoc_of% e
  rw [← e]
  simp [eqToHom_map]

variable [HasLimits C]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.PresheafedSpace.GlueData.** 是 Mathlib 中的一个定理，位于命名空间 `Algebra
icGeometry.PresheafedSpace.GlueData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ι_image_preimage_eq (i j : D.J) (U : Opens (D.U i).carrier) :
    (Opens.map (𝖣.ι j).base).obj ((D.ι_isOpenEmbedding i).functor.obj U) =
      (opensFunctor (D.f j i)).obj
        ((Opens.map (𝖣.t j i).base).obj ((Opens.map (𝖣.f i j).base).obj U)) := by
  ext1
  dsimp only [Opens.map_coe, IsOpenMap.coe_functor_obj]
  rw [← show _ = (𝖣.ι i).base from 𝖣.ι_gluedIso_inv (PresheafedSpace.forget _) i, ←
    show _ = (𝖣.ι j).base from 𝖣.ι_gluedIso_inv (PresheafedSpace.forget _) j]
  rw [TopCat.coe_comp, TopCat.coe_comp, Set.image_comp, Set.preimage_comp, Set.preimage_image_eq]
  · refine Eq.trans (D.toTopGlueData.preimage_image_eq_image' _ _ _) ?_
    dsimp
    rw [Set.image_comp]
    refine congr_arg (_ '' ·) ?_
    rw [Set.eq_preimage_iff_image_eq, ← Set.image_comp]
    swap
    · exact CategoryTheory.ConcreteCategory.bijective_of_isIso (C := TopCat) _
    change (D.t i j ≫ D.t j i).base '' _ = _
    rw [𝖣.t_inv]
    simp
  · rw [← TopCat.mono_iff_injective]
    infer_instance

/-- (Implementation). The map `Γ(𝒪_{U_i}, U) ⟶ Γ(𝒪_{U_j}, 𝖣.ι j ⁻¹' 𝖣.ι i '' U)` -/
/-
**AlgebraicGeometry.PresheafedSpace.GlueData.opensImagePreimageMap** 是 Mathlib 中
的一个定义，位于命名空间 `AlgebraicGeometry.PresheafedSpace.GlueData`。
形式化陈述：opensImagePreimageMap (i j : D.J) (U : Opens (D.U i).carrier) : (D.U i).pr
esheaf.obj (op U) ⟶ (D.U j).presheaf.obj (op <| (Opens.map (𝖣.ι j).base).obj ((D
.ι_isOpenEmbedding i).functor.obj U))
参数：i j : D.J；U : Opens (D.U i).carrier。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.PresheafedSpace.GlueData.ι_isOpenEmbedding`：ι_isOpenEm
bedding [HasLimits C] (i : D.J) : IsOpenEmbedding (𝖣.ι i).base
· 使用定理 `AlgebraicGeometry.PresheafedSpace.GlueData.f_open`：∀ {C : Type u} [inst 
: CategoryTheory.Category.{v, u} C] (self : AlgebraicGeometry.PresheafedSpace.Gl
ueData C)   (i j : self.J), AlgebraicGe…
· 使用定理 `AlgebraicGeometry.PresheafedSpace.GlueData.ι_image_preimage_eq`：ι_image_
preimage_eq (i j : D.J) (U : Opens (D.U i).carrier) : (Opens.map (𝖣.ι j).base).o
bj ((D.ι_isOpenEmbedding i).functor.obj U) = (opensF…

--- 原说明 ---
(Implementation). The map `Γ(𝒪_{U_i}, U) ⟶ Γ(𝒪_{U_j}, 𝖣.ι j ⁻¹' 𝖣.ι i '' U)`
-/
def opensImagePreimageMap (i j : D.J) (U : Opens (D.U i).carrier) :
    (D.U i).presheaf.obj (op U) ⟶
    (D.U j).presheaf.obj (op <|
      (Opens.map (𝖣.ι j).base).obj ((D.ι_isOpenEmbedding i).functor.obj U)) :=
  (D.f i j).c.app (op U) ≫
    (D.t j i).c.app _ ≫
      (D.f_open j i).invApp _ (unop _) ≫
        (𝖣.U j).presheaf.map (eqToHom (D.ι_image_preimage_eq i j U)).op

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.PresheafedSpace.GlueData.opensImagePreimageMap_app'** 是 Math
lib 中的一个定理，位于命名空间 `AlgebraicGeometry.PresheafedSpace.GlueData`。
形式化陈述：opensImagePreimageMap_app' (i j k : D.J) (U : Opens (D.U i).carrier) : exi
sts eq, D.opensImagePreimageMap i j U ≫ (D.f j k).c.app _ = ((π₁ j, i, k) ≫ D.t 
j i ≫ D.f i j).c.app (op U) ≫ (π₂⁻¹ j, i, k) (unop _) ≫ (D.V (j, k)).presheaf.ma
p (eqToHom eq)
参数：i j k : D.J；U : Opens (D.U i).carrier。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.PresheafedSpace.GlueData.f_open`：∀ {C : Type u} [inst 
: CategoryTheory.Category.{v, u} C] (self : AlgebraicGeometry.PresheafedSpace.Gl
ueData C)   (i j : self.J), AlgebraicGe…
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `AlgebraicGeometry.PresheafedSpace.instHasColimitsOfShape`：∀ {J : Type u'
} [inst : CategoryTheory.Category.{v', u'} J] {C : Type u} [inst_1 : CategoryThe
ory.Category.{v, u} C]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.WalkingMultispan.instSmallOfLOfR`：∀ {J : CategoryT
heory.Limits.MultispanShape} [Small.{t, w} J.L] [Small.{t, w'} J.R],   Small.{t,
 max w' w} (CategoryTheory.Limits.WalkingMul…
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `TopCat.instHasLimitsOfShapePresheaf`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {J : Type w} [inst_1 : CategoryTheory.Category.{v_1, w} J]
   [CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Limits.instHasLimitsOfShapeOfHasLimitsOfSize`：∀ {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTh
eory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `AlgebraicGeometry.PresheafedSpace.GlueData.ι_isOpenEmbedding`：ι_isOpenEm
bedding [HasLimits C] (i : D.J) : IsOpenEmbedding (𝖣.ι i).base
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.PresheafedSpace.GlueData.ι_image_preimage_eq`：ι_image_
preimage_eq (i j : D.J) (U : Opens (D.U i).carrier) : (Opens.map (𝖣.ι j).base).o
bj ((D.ι_isOpenEmbedding i).functor.obj U) = (opensF…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `AlgebraicGeometry.PresheafedSpace.GlueData.f_invApp_f_app_assoc`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] (D : AlgebraicGeometry.Preshea
fedSpace.GlueData C)   (i j k : D.J) (U : Topological…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `AlgebraicGeometry.PresheafedSpace.comp_c_app`：comp_c_app {X Y Z : Preshe
afedSpace C} (α : X ⟶ Y) (β : Y ⟶ Z) (U) : (α ≫ β).c.app U = β.c.app U ≫ α.c.app
 (op ((Opens.map β.base).obj (unop…
· 使用定理 `CategoryTheory.eqToHom_map`：eqToHom_map (F : C ⥤ D) {X Y : C} (p : X = Y
) : F.map (eqToHom p) = eqToHom (congr_arg F.obj p)
· 使用定理 `CategoryTheory.eqToHom_op`：eqToHom_op {X Y : C} (h : X = Y) : (eqToHom h
).op = eqToHom (congr_arg op h.symm)
· 使用定理 `CategoryTheory.eqToHom_trans`：eqToHom_trans {X Y Z : C} (p : X = Y) (q :
 Y = Z) : eqToHom p ≫ eqToHom q = eqToHom (p.trans q)
-/
theorem opensImagePreimageMap_app' (i j k : D.J) (U : Opens (D.U i).carrier) :
    ∃ eq,
      D.opensImagePreimageMap i j U ≫ (D.f j k).c.app _ =
        ((π₁ j, i, k) ≫ D.t j i ≫ D.f i j).c.app (op U) ≫
          (π₂⁻¹ j, i, k) (unop _) ≫ (D.V (j, k)).presheaf.map (eqToHom eq) := by
  constructor
  · delta opensImagePreimageMap
    simp_rw [Category.assoc]
    rw [(D.f j k).c.naturality, f_invApp_f_app_assoc]
    · erw [← (D.V (j, k)).presheaf.map_comp]
      · simp_rw [← Category.assoc]
        erw [← comp_c_app, ← comp_c_app]
        · simp_rw [Category.assoc]
          dsimp only [Functor.op, unop_op, Quiver.Hom.unop_op]
          rw [eqToHom_map (Opens.map _), eqToHom_op, eqToHom_trans]
          congr

/-- The red and the blue arrows in ![this diagram](https://i.imgur.com/mBzV1Rx.png) commute. -/
/-
**AlgebraicGeometry.PresheafedSpace.GlueData.opensImagePreimageMap_app** 是 Mathl
ib 中的一个定理，位于命名空间 `AlgebraicGeometry.PresheafedSpace.GlueData`。
形式化陈述：opensImagePreimageMap_app (i j k : D.J) (U : Opens (D.U i).carrier) : D.op
ensImagePreimageMap i j U ≫ (D.f j k).c.app _ = ((π₁ j, i, k) ≫ D.t j i ≫ D.f i 
j).c.app (op U) ≫ (π₂⁻¹ j, i, k) (unop _) ≫ (D.V (j, k)).presheaf.map (eqToHom (
opensImagePreimageMap_app' D i j k U).choose)
参数：i j k : D.J；U : Opens (D.U i).carrier。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `AlgebraicGeometry.PresheafedSpace.GlueData.f_open`：∀ {C : Type u} [inst 
: CategoryTheory.Category.{v, u} C] (self : AlgebraicGeometry.PresheafedSpace.Gl
ueData C)   (i j : self.J), AlgebraicGe…
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `AlgebraicGeometry.PresheafedSpace.instHasColimitsOfShape`：∀ {J : Type u'
} [inst : CategoryTheory.Category.{v', u'} J] {C : Type u} [inst_1 : CategoryThe
ory.Category.{v, u} C]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.WalkingMultispan.instSmallOfLOfR`：∀ {J : CategoryT
heory.Limits.MultispanShape} [Small.{t, w} J.L] [Small.{t, w'} J.R],   Small.{t,
 max w' w} (CategoryTheory.Limits.WalkingMul…
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `TopCat.instHasLimitsOfShapePresheaf`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {J : Type w} [inst_1 : CategoryTheory.Category.{v_1, w} J]
   [CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Limits.instHasLimitsOfShapeOfHasLimitsOfSize`：∀ {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTh
eory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `AlgebraicGeometry.PresheafedSpace.GlueData.ι_isOpenEmbedding`：ι_isOpenEm
bedding [HasLimits C] (i : D.J) : IsOpenEmbedding (𝖣.ι i).base
· 使用定理 `AlgebraicGeometry.PresheafedSpace.GlueData.opensImagePreimageMap_app'`：o
pensImagePreimageMap_app' (i j k : D.J) (U : Opens (D.U i).carrier) : exists eq,
 D.opensImagePreimageMap i j U ≫ (D.f j k).c.app _ = ((π₁ j…

--- 原说明 ---
The red and the blue arrows in ![this diagram](https://i.imgur.com/mBzV1Rx.png) 
commute.
-/
theorem opensImagePreimageMap_app (i j k : D.J) (U : Opens (D.U i).carrier) :
    D.opensImagePreimageMap i j U ≫ (D.f j k).c.app _ =
      ((π₁ j, i, k) ≫ D.t j i ≫ D.f i j).c.app (op U) ≫
        (π₂⁻¹ j, i, k) (unop _) ≫
          (D.V (j, k)).presheaf.map (eqToHom (opensImagePreimageMap_app' D i j k U).choose) :=
  (opensImagePreimageMap_app' D i j k U).choose_spec

set_option backward.isDefEq.respectTransparency false in
-- This is proved separately since `reassoc` somehow timeouts.
/-
**AlgebraicGeometry.PresheafedSpace.GlueData.opensImagePreimageMap_app_assoc** 是
 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.PresheafedSpace.GlueData`。
形式化陈述：opensImagePreimageMap_app_assoc (i j k : D.J) (U : Opens (D.U i).carrier) 
{X' : C} (f' : _ ⟶ X') : D.opensImagePreimageMap i j U ≫ (D.f j k).c.app _ ≫ f' 
= ((π₁ j, i, k) ≫ D.t j i ≫ D.f i j).c.app (op U) ≫ (π₂⁻¹ j, i, k) (unop _) ≫ (D
.V (j, k)).presheaf.map (eqToHom (opensImagePreimageMap_app' D i j k U).choose) 
≫ f'
参数：i j k : D.J；U : Opens (D.U i).carrier；f' : _ ⟶ X'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `AlgebraicGeometry.PresheafedSpace.instHasColimitsOfShape`：∀ {J : Type u'
} [inst : CategoryTheory.Category.{v', u'} J] {C : Type u} [inst_1 : CategoryThe
ory.Category.{v, u} C]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.WalkingMultispan.instSmallOfLOfR`：∀ {J : CategoryT
heory.Limits.MultispanShape} [Small.{t, w} J.L] [Small.{t, w'} J.R],   Small.{t,
 max w' w} (CategoryTheory.Limits.WalkingMul…
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `TopCat.instHasLimitsOfShapePresheaf`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {J : Type w} [inst_1 : CategoryTheory.Category.{v_1, w} J]
   [CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Limits.instHasLimitsOfShapeOfHasLimitsOfSize`：∀ {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTh
eory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `AlgebraicGeometry.PresheafedSpace.GlueData.ι_isOpenEmbedding`：ι_isOpenEm
bedding [HasLimits C] (i : D.J) : IsOpenEmbedding (𝖣.ι i).base
· 使用定理 `AlgebraicGeometry.PresheafedSpace.GlueData.f_open`：∀ {C : Type u} [inst 
: CategoryTheory.Category.{v, u} C] (self : AlgebraicGeometry.PresheafedSpace.Gl
ueData C)   (i j : self.J), AlgebraicGe…
· 使用定理 `AlgebraicGeometry.PresheafedSpace.GlueData.opensImagePreimageMap_app'`：o
pensImagePreimageMap_app' (i j k : D.J) (U : Opens (D.U i).carrier) : exists eq,
 D.opensImagePreimageMap i j U ≫ (D.f j k).c.app _ = ((π₁ j…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.PresheafedSpace.GlueData.opensImagePreimageMap_app`：op
ensImagePreimageMap_app (i j k : D.J) (U : Opens (D.U i).carrier) : D.opensImage
PreimageMap i j U ≫ (D.f j k).c.app _ = ((π₁ j, i, k) ≫ D.…
-/
theorem opensImagePreimageMap_app_assoc (i j k : D.J) (U : Opens (D.U i).carrier) {X' : C}
    (f' : _ ⟶ X') :
    D.opensImagePreimageMap i j U ≫ (D.f j k).c.app _ ≫ f' =
      ((π₁ j, i, k) ≫ D.t j i ≫ D.f i j).c.app (op U) ≫
        (π₂⁻¹ j, i, k) (unop _) ≫
          (D.V (j, k)).presheaf.map
            (eqToHom (opensImagePreimageMap_app' D i j k U).choose) ≫ f' := by
  simpa only [Category.assoc] using congr_arg (· ≫ f') (opensImagePreimageMap_app D i j k U)

/-- (Implementation) Given an open subset of one of the spaces `U ⊆ Uᵢ`, the sheaf component of
the image `ι '' U` in the glued space is the limit of this diagram. -/
/-
**AlgebraicGeometry.PresheafedSpace.GlueData.diagramOverOpen** 是 Mathlib 中的一个缩写定
义，位于命名空间 `AlgebraicGeometry.PresheafedSpace.GlueData`。
形式化陈述：diagramOverOpen {i : D.J} (U : Opens (D.U i).carrier) : (WalkingMultispan 
(.prod D.J))ᵒᵖ ⥤ C
参数：U : Opens (D.U i).carrier。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.PresheafedSpace.GlueData.ι_isOpenEmbedding`：ι_isOpenEm
bedding [HasLimits C] (i : D.J) : IsOpenEmbedding (𝖣.ι i).base

--- 原说明 ---
(Implementation) Given an open subset of one of the spaces `U ⊆ Uᵢ`, the sheaf c
omponent of
the image `ι '' U` in the glued space is the limit of this diagram.
-/
abbrev diagramOverOpen {i : D.J} (U : Opens (D.U i).carrier) :
    (WalkingMultispan (.prod D.J))ᵒᵖ ⥤ C :=
  componentwiseDiagram 𝖣.diagram.multispan ((D.ι_isOpenEmbedding i).functor.obj U)

/-- (Implementation)
The projection from the limit of `diagram_over_open` to a component of `D.U j`. -/
/-
**AlgebraicGeometry.PresheafedSpace.GlueData.diagramOverOpen** 是 Mathlib 中的一个缩写定
义，位于命名空间 `AlgebraicGeometry.PresheafedSpace.GlueData`。
形式化陈述：diagramOverOpen {i : D.J} (U : Opens (D.U i).carrier) : (WalkingMultispan 
(.prod D.J))ᵒᵖ ⥤ C
参数：U : Opens (D.U i).carrier。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.PresheafedSpace.GlueData.ι_isOpenEmbedding`：ι_isOpenEm
bedding [HasLimits C] (i : D.J) : IsOpenEmbedding (𝖣.ι i).base

--- 原说明 ---
(Implementation)
The projection from the limit of `diagram_over_open` to a component of `D.U j`.
-/
abbrev diagramOverOpenπ {i : D.J} (U : Opens (D.U i).carrier) (j : D.J) :=
  limit.π (D.diagramOverOpen U) (op (WalkingMultispan.right j))

set_option backward.isDefEq.respectTransparency false in
/-- (Implementation) We construct the map `Γ(𝒪_{U_i}, U) ⟶ Γ(𝒪_V, U_V)` for each `V` in the gluing
diagram. We will lift these maps into `ιInvApp`. -/
/-
**AlgebraicGeometry.PresheafedSpace.GlueData.** 是 Mathlib 中的一个定义，位于命名空间 `Algebra
icGeometry.PresheafedSpace.GlueData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(Implementation) We construct the map `Γ(𝒪_{U_i}, U) ⟶ Γ(𝒪_V, U_V)` for each `V`
 in the gluing
diagram. We will lift these maps into `ιInvApp`.
-/
def ιInvAppπApp {i : D.J} (U : Opens (D.U i).carrier) (j) :
    (𝖣.U i).presheaf.obj (op U) ⟶ (D.diagramOverOpen U).obj (op j) := by
  rcases j with (⟨j, k⟩ | j)
  · refine
      D.opensImagePreimageMap i j U ≫ (D.f j k).c.app _ ≫ (D.V (j, k)).presheaf.map (eqToHom ?_)
    rw [Functor.op_obj]
    congr 1; ext1
    dsimp only [Functor.op_obj, Opens.map_coe, unop_op, IsOpenMap.coe_functor_obj]
    rw [Set.preimage_preimage]
    change (D.f j k ≫ 𝖣.ι j).base ⁻¹' _ = _
    congr 4
    exact colimit.w 𝖣.diagram.multispan (WalkingMultispan.Hom.fst (j, k))
  · exact D.opensImagePreimageMap i j U

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- (Implementation) The natural map `Γ(𝒪_{U_i}, U) ⟶ Γ(𝒪_X, 𝖣.ι i '' U)`.
This forms the inverse of `(𝖣.ι i).c.app (op U)`. -/
/-
**AlgebraicGeometry.PresheafedSpace.GlueData.** 是 Mathlib 中的一个定义，位于命名空间 `Algebra
icGeometry.PresheafedSpace.GlueData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(Implementation) The natural map `Γ(𝒪_{U_i}, U) ⟶ Γ(𝒪_X, 𝖣.ι i '' U)`.
This forms the inverse of `(𝖣.ι i).c.app (op U)`.
-/
def ιInvApp {i : D.J} (U : Opens (D.U i).carrier) :
    (D.U i).presheaf.obj (op U) ⟶ limit (D.diagramOverOpen U) :=
  limit.lift (D.diagramOverOpen U)
    { pt := (D.U i).presheaf.obj (op U)
      π :=
        { app := fun j => D.ιInvAppπApp U (unop j)
          naturality := fun {X Y} f' => by
            induction X with | op X => ?_
            induction Y with | op Y => ?_
            let f : Y ⟶ X := f'.unop; have : f' = f.op := rfl; clear_value f; subst this
            rcases f with (_ | ⟨j, k⟩ | ⟨j, k⟩)
            · simp
            · simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp]
              congr 1
            simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp]
            -- It remains to show that the blue is equal to red + green in the original diagram.
            -- The proof strategy is illustrated in ![this diagram](https://i.imgur.com/mBzV1Rx.png)
            -- where we prove red = pink = light-blue = green = blue.
            change
              D.opensImagePreimageMap i j U ≫
                  (D.f j k).c.app _ ≫ (D.V (j, k)).presheaf.map (eqToHom _) =
                D.opensImagePreimageMap _ _ _ ≫
                  ((D.f k j).c.app _ ≫ (D.t j k).c.app _) ≫ (D.V (j, k)).presheaf.map (eqToHom _)
            rw [opensImagePreimageMap_app_assoc]
            simp_rw [Category.assoc]
            rw [opensImagePreimageMap_app_assoc, (D.t j k).c.naturality_assoc,
                snd_invApp_t_app_assoc,
                ← PresheafedSpace.comp_c_app_assoc]
            -- light-blue = green is relatively easy since the part that differs does not involve
            -- partial inverses.
            have :
              D.t' j k i ≫ (π₁ k, i, j) ≫ D.t k i ≫ 𝖣.f i k =
                (pullbackSymmetry _ _).hom ≫ (π₁ j, i, k) ≫ D.t j i ≫ D.f i j := by
              rw [← 𝖣.t_fac_assoc, 𝖣.t'_comp_eq_pullbackSymmetry_assoc,
                pullbackSymmetry_hom_comp_snd_assoc, pullback.condition, 𝖣.t_fac_assoc]
            rw [congr_app this,
                PresheafedSpace.comp_c_app_assoc (pullbackSymmetry _ _).hom]
            simp_rw [Category.assoc]
            congr 1
            rw [← IsIso.eq_inv_comp, IsOpenImmersion.inv_invApp, Category.assoc,
              NatTrans.naturality_assoc]
            simp_rw [Functor.op_obj]
            rw [← PresheafedSpace.comp_c_app_assoc, congr_app (pullbackSymmetry_hom_comp_snd _ _)]
            simp_rw [Category.assoc, Functor.op_obj, comp_base, Opens.map_comp_obj,
              TopCat.Presheaf.pushforward_obj_map]
            rw [IsOpenImmersion.inv_naturality_assoc, IsOpenImmersion.inv_naturality_assoc,
              IsOpenImmersion.inv_naturality_assoc, IsOpenImmersion.app_invApp_assoc]
            repeat rw [← (D.V (j, k)).presheaf.map_comp]
            rfl } }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- `ιInvApp` is the left inverse of `D.ι i` on `U`. -/
/-
**AlgebraicGeometry.PresheafedSpace.GlueData.** 是 Mathlib 中的一个定理，位于命名空间 `Algebra
icGeometry.PresheafedSpace.GlueData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ιInvApp` is the left inverse of `D.ι i` on `U`.
-/
theorem ιInvApp_π {i : D.J} (U : Opens (D.U i).carrier) :
    ∃ eq, D.ιInvApp U ≫ D.diagramOverOpenπ U i = (D.U i).presheaf.map (eqToHom eq) := by
  fconstructor
  -- Porting note: I don't know what the magic was in Lean3 proof, it just skipped the proof of `eq`
  · congr; ext1; change _ = _ ⁻¹' _ '' _; ext1 x
    simp only [SetLike.mem_coe, unop_op, Set.mem_preimage, Set.mem_image]
    refine ⟨fun h => ⟨_, h, rfl⟩, ?_⟩
    rintro ⟨y, h1, h2⟩
    convert! h1 using 1
    delta ι Multicoequalizer.π at h2
    apply_fun (D.ι _).base
    · exact h2.symm
    · have := D.ι_gluedIso_inv (PresheafedSpace.forget _) i
      dsimp at this
      rw [← this, TopCat.coe_comp]
      refine Function.Injective.comp ?_ (TopCat.GlueData.ι_injective D.toTopGlueData i)
      rw [← TopCat.mono_iff_injective]
      infer_instance
  delta ιInvApp
  rw [limit.lift_π]
  change D.opensImagePreimageMap i i U = _
  dsimp [opensImagePreimageMap]
  rw [congr_app (D.t_id _), id_c_app, ← Functor.map_comp]
  erw [IsOpenImmersion.inv_naturality_assoc, IsOpenImmersion.app_inv_app'_assoc]
  · simp only [eqToHom_op, ← Functor.map_comp]
    rfl
  · rw [Set.range_eq_univ.mpr _]
    · simp
    · rw [← TopCat.epi_iff_surjective]
      infer_instance

/-- The `eqToHom` given by `ιInvApp_π`. -/
/-
**AlgebraicGeometry.PresheafedSpace.GlueData.** 是 Mathlib 中的一个缩写定义，位于命名空间 `Algeb
raicGeometry.PresheafedSpace.GlueData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `eqToHom` given by `ιInvApp_π`.
-/
abbrev ιInvAppπEqMap {i : D.J} (U : Opens (D.U i).carrier) :=
  (D.U i).presheaf.map (eqToIso (D.ιInvApp_π U).choose).inv

set_option backward.isDefEq.respectTransparency false in
/-- `ιInvApp` is the right inverse of `D.ι i` on `U`. -/
/-
**AlgebraicGeometry.PresheafedSpace.GlueData.** 是 Mathlib 中的一个定理，位于命名空间 `Algebra
icGeometry.PresheafedSpace.GlueData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ιInvApp` is the right inverse of `D.ι i` on `U`.
-/
theorem π_ιInvApp_π (i j : D.J) (U : Opens (D.U i).carrier) :
    D.diagramOverOpenπ U i ≫ D.ιInvAppπEqMap U ≫ D.ιInvApp U ≫ D.diagramOverOpenπ U j =
      D.diagramOverOpenπ U j := by
  rw [← @cancel_mono
          (f := (componentwiseDiagram 𝖣.diagram.multispan _).map
            (Quiver.Hom.op (WalkingMultispan.Hom.snd (i, j))) ≫ 𝟙 _) ..]
  · simp_rw [Category.assoc]
    rw [limit.w_assoc]
    erw [limit.lift_π_assoc]
    rw [Category.comp_id, Category.comp_id]
    change _ ≫ _ ≫ (_ ≫ _) ≫ _ = _
    rw [congr_app (D.t_id _), id_c_app]
    simp_rw [Category.assoc]
    rw [← Functor.map_comp_assoc]
    -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11224): change `rw` to `erw`
    erw [IsOpenImmersion.inv_naturality_assoc]
    erw [IsOpenImmersion.app_invApp_assoc]
    iterate 3 rw [← Functor.map_comp_assoc]
    rw [NatTrans.naturality_assoc]
    erw [← (D.V (i, j)).presheaf.map_comp]
    convert!
      limit.w (componentwiseDiagram 𝖣.diagram.multispan _)
        (Quiver.Hom.op (WalkingMultispan.Hom.fst (i, j)))
  · rw [Category.comp_id]
    apply +allowSynthFailures mono_comp
    change Mono ((_ ≫ D.f j i).c.app _)
    rw [comp_c_app]
    apply +allowSynthFailures mono_comp
    · erw [D.ι_image_preimage_eq i j U]
      infer_instance
    · have : IsIso (D.t i j).c := by apply c_isIso_of_iso
      infer_instance

set_option backward.isDefEq.respectTransparency.types false in
/-- `ιInvApp` is the inverse of `D.ι i` on `U`. -/
/-
**AlgebraicGeometry.PresheafedSpace.GlueData.** 是 Mathlib 中的一个定理，位于命名空间 `Algebra
icGeometry.PresheafedSpace.GlueData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ιInvApp` is the inverse of `D.ι i` on `U`.
-/
theorem π_ιInvApp_eq_id (i : D.J) (U : Opens (D.U i).carrier) :
    D.diagramOverOpenπ U i ≫ D.ιInvAppπEqMap U ≫ D.ιInvApp U = 𝟙 _ := by
  ext j
  induction j with | op j => ?_
  rcases j with (⟨j, k⟩ | ⟨j⟩)
  · rw [← limit.w (componentwiseDiagram 𝖣.diagram.multispan _)
        (Quiver.Hom.op (WalkingMultispan.Hom.fst (j, k))),
      ← Category.assoc, Category.id_comp]
    congr 1
    simp_rw [Category.assoc]
    apply π_ιInvApp_π
  · simp_rw [Category.assoc]
    rw [Category.id_comp]
    apply π_ιInvApp_π

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.PresheafedSpace.GlueData.componentwise_diagram_** 是 Mathlib 
中的一个实例，位于命名空间 `AlgebraicGeometry.PresheafedSpace.GlueData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance componentwise_diagram_π_isIso (i : D.J) (U : Opens (D.U i).carrier) :
    IsIso (D.diagramOverOpenπ U i) := by
  use D.ιInvAppπEqMap U ≫ D.ιInvApp U
  constructor
  · apply π_ιInvApp_eq_id
  · rw [Category.assoc, (D.ιInvApp_π _).choose_spec]
    exact Iso.inv_hom_id ((D.U i).presheaf.mapIso (eqToIso _))

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.PresheafedSpace.GlueData.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra
icGeometry.PresheafedSpace.GlueData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance ιIsOpenImmersion (i : D.J) : IsOpenImmersion (𝖣.ι i) where
  base_open := D.ι_isOpenEmbedding i
  c_iso U := by erw [← colimitPresheafObjIsoComponentwiseLimit_hom_π]; infer_instance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The following diagram is a pullback, i.e. `Vᵢⱼ` is the intersection of `Uᵢ` and `Uⱼ` in `X`.

```
Vᵢⱼ ⟶ Uᵢ
 |      |
 ↓      ↓
 Uⱼ ⟶ X
```
-/
/-
**AlgebraicGeometry.PresheafedSpace.GlueData.vPullbackConeIsLimit** 是 Mathlib 中的
一个定义，位于命名空间 `AlgebraicGeometry.PresheafedSpace.GlueData`。
形式化陈述：vPullbackConeIsLimit (i j : D.J) : IsLimit (𝖣.vPullbackCone i j)
参数：i j : D.J。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.PresheafedSpace.GlueData.f_open`：∀ {C : Type u} [inst 
: CategoryTheory.Category.{v, u} C] (self : AlgebraicGeometry.PresheafedSpace.Gl
ueData C)   (i j : self.J), AlgebraicGe…

--- 原说明 ---
The following diagram is a pullback, i.e. `Vᵢⱼ` is the intersection of `Uᵢ` and 
`Uⱼ` in `X`.

```
Vᵢⱼ ⟶ Uᵢ
 |      |
 ↓      ↓
 Uⱼ ⟶ X
```
-/
def vPullbackConeIsLimit (i j : D.J) : IsLimit (𝖣.vPullbackCone i j) :=
  PullbackCone.isLimitAux' _ fun s => by
    refine ⟨?_, ?_, ?_, ?_⟩
    · refine PresheafedSpace.IsOpenImmersion.lift (D.f i j) s.fst ?_
      erw [← D.toTopGlueData.preimage_range j i]
      have :
        s.fst.base ≫ D.toTopGlueData.ι i =
          s.snd.base ≫ D.toTopGlueData.ι j := by
        rw [← 𝖣.ι_gluedIso_hom (PresheafedSpace.forget _) _, ←
          𝖣.ι_gluedIso_hom (PresheafedSpace.forget _) _]
        have := congr_arg PresheafedSpace.Hom.base s.condition
        rw [comp_base, comp_base] at this
        replace this := reassoc_of% this
        exact this _
      simp only [mapGlueData_U, forget_obj]
      rw [← Set.image_subset_iff, ← Set.image_univ, ← Set.image_comp, Set.image_univ,
        ← TopCat.coe_comp, this, TopCat.coe_comp, ← Set.image_univ, Set.image_comp]
      exact Set.image_subset_range _ _
    · apply IsOpenImmersion.lift_fac
    · rw [← cancel_mono (𝖣.ι j), Category.assoc, ← (𝖣.vPullbackCone i j).condition]
      conv_rhs => rw [← s.condition]
      erw [IsOpenImmersion.lift_fac_assoc]
    · intro m e₁ _
      rw [← cancel_mono (D.f i j)]
      simp only [lift_fac]
      tauto
/-
**AlgebraicGeometry.PresheafedSpace.GlueData.** 是 Mathlib 中的一个定理，位于命名空间 `Algebra
icGeometry.PresheafedSpace.GlueData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ι_jointly_surjective (x : 𝖣.glued) : ∃ (i : D.J) (y : D.U i), (𝖣.ι i).base y = x :=
  𝖣.ι_jointly_surjective (PresheafedSpace.forget _ ⋙ CategoryTheory.forget TopCat) x

end GlueData

end PresheafedSpace

namespace SheafedSpace

/-- A family of gluing data consists of
1. An index type `J`
2. A sheafed space `U i` for each `i : J`.
3. A sheafed space `V i j` for each `i j : J`.
   (Note that this is `J × J → SheafedSpace C` rather than `J → J → SheafedSpace C` to
   connect to the limits library more easily.)
4. An open immersion `f i j : V i j ⟶ U i` for each `i j : J`.
5. A transition map `t i j : V i j ⟶ V j i` for each `i j : J`.

such that
6. `f i i` is an isomorphism.
7. `t i i` is the identity.
8. `V i j ×[U i] V i k ⟶ V i j ⟶ V j i` factors through `V j k ×[U j] V j i ⟶ V j i` via some
   `t' : V i j ×[U i] V i k ⟶ V j k ×[U j] V j i`.
9. `t' i j k ≫ t' j k i ≫ t' k i j = 𝟙 _`.

We can then glue the spaces `U i` together by identifying `V i j` with `V j i`, such
that the `U i`'s are open subspaces of the glued space.
-/
/-
**AlgebraicGeometry.SheafedSpace.GlueData** 是 Mathlib 中的一个归纳类型，位于命名空间 `Algebraic
Geometry.SheafedSpace`。
形式化陈述：(C : Type u) → [CategoryTheory.Category.{v, u} C] → Type (max u (v + 1))
参数：v + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A family of gluing data consists of
1. An index type `J`
2. A sheafed space `U i` for each `i : J`.
3. A sheafed space `V i j` for each `i j : J`.
   (Note that this is `J × J → SheafedSpace C` rather than `J → J → SheafedSpace
 C` to
   connect to the limits library more easily.)
4. An open immersion `f i j : V i j ⟶ U i` for each `i j : J`.
5. A transition map `t i j : V i j ⟶ V j i` for each `i j : J`.

such that
6. `f i i` is an isomorphism.
7. `t i i` is the identity.
8. `V i j ×[U i] V i k ⟶ V i j ⟶ V j i` factors through `V j k ×[U j] V j i ⟶ V 
j i` via some
   `t' : V i j ×[U i] V i k ⟶ V j k ×[U j] V j i`.
9. `t' i j k ≫ t' j k i ≫ t' k i j = 𝟙 _`.

We can then glue the spaces `U i` together by identifying `V i j` with `V j i`, 
such
that the `U i`'s are open subspaces of the glued space.
-/
structure GlueData extends CategoryTheory.GlueData (SheafedSpace.{u, v, v} C) where
  f_open : ∀ i j, SheafedSpace.IsOpenImmersion (f i j)

attribute [instance] GlueData.f_open

namespace GlueData

variable {C}
variable (D : GlueData C)

local notation "𝖣" => D.toGlueData

/-- The glue data of presheafed spaces associated to a family of glue data of sheafed spaces. -/
/-
**AlgebraicGeometry.SheafedSpace.GlueData.toPresheafedSpaceGlueData** 是 Mathlib 
中的一个缩写定义，位于命名空间 `AlgebraicGeometry.SheafedSpace.GlueData`。
形式化陈述：toPresheafedSpaceGlueData : PresheafedSpace.GlueData C
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.SheafedSpace.GlueData.f_open`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] (self : AlgebraicGeometry.SheafedSpace.GlueData
 C)   (i j : self.J), AlgebraicGeome…

--- 原说明 ---
The glue data of presheafed spaces associated to a family of glue data of sheafe
d spaces.
-/
abbrev toPresheafedSpaceGlueData : PresheafedSpace.GlueData C :=
  { f_open := D.f_open
    toGlueData := 𝖣.mapGlueData forgetToPresheafedSpace }

variable [HasLimits C]

/-- The gluing as sheafed spaces is isomorphic to the gluing as presheafed spaces. -/
/-
**AlgebraicGeometry.SheafedSpace.GlueData.isoPresheafedSpace** 是 Mathlib 中的一个缩写定
义，位于命名空间 `AlgebraicGeometry.SheafedSpace.GlueData`。
形式化陈述：isoPresheafedSpace : 𝖣.glued.toPresheafedSpace ≅ D.toPresheafedSpaceGlueDa
ta.toGlueData.glued
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The gluing as sheafed spaces is isomorphic to the gluing as presheafed spaces.
-/
abbrev isoPresheafedSpace :
    𝖣.glued.toPresheafedSpace ≅ D.toPresheafedSpaceGlueData.toGlueData.glued :=
  𝖣.gluedIso forgetToPresheafedSpace
/-
**AlgebraicGeometry.SheafedSpace.GlueData.** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicG
eometry.SheafedSpace.GlueData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ι_isoPresheafedSpace_inv (i : D.J) :
    D.toPresheafedSpaceGlueData.toGlueData.ι i ≫ D.isoPresheafedSpace.inv = (𝖣.ι i).hom :=
  𝖣.ι_gluedIso_inv _ _

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.SheafedSpace.GlueData.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicG
eometry.SheafedSpace.GlueData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance ιIsOpenImmersion (i : D.J) : IsOpenImmersion (𝖣.ι i) := by
  dsimp [IsOpenImmersion]
  rw [← D.ι_isoPresheafedSpace_inv]
  have := D.toPresheafedSpaceGlueData.ιIsOpenImmersion i
  infer_instance
/-
**AlgebraicGeometry.SheafedSpace.GlueData.** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicG
eometry.SheafedSpace.GlueData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ι_jointly_surjective (x : 𝖣.glued) : ∃ (i : D.J) (y : D.U i), (𝖣.ι i).hom.base y = x :=
  𝖣.ι_jointly_surjective (SheafedSpace.forget _ ⋙ CategoryTheory.forget TopCat) x

/-- The following diagram is a pullback, i.e. `Vᵢⱼ` is the intersection of `Uᵢ` and `Uⱼ` in `X`.

```
Vᵢⱼ ⟶ Uᵢ
 |      |
 ↓      ↓
 Uⱼ ⟶ X
```
-/
/-
**AlgebraicGeometry.SheafedSpace.GlueData.vPullbackConeIsLimit** 是 Mathlib 中的一个定
义，位于命名空间 `AlgebraicGeometry.SheafedSpace.GlueData`。
形式化陈述：vPullbackConeIsLimit (i j : D.J) : IsLimit (𝖣.vPullbackCone i j)
参数：i j : D.J。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The following diagram is a pullback, i.e. `Vᵢⱼ` is the intersection of `Uᵢ` and 
`Uⱼ` in `X`.

```
Vᵢⱼ ⟶ Uᵢ
 |      |
 ↓      ↓
 Uⱼ ⟶ X
```
-/
def vPullbackConeIsLimit (i j : D.J) : IsLimit (𝖣.vPullbackCone i j) :=
  𝖣.vPullbackConeIsLimitOfMap forgetToPresheafedSpace i j
    (D.toPresheafedSpaceGlueData.vPullbackConeIsLimit _ _)

end GlueData

end SheafedSpace

namespace LocallyRingedSpace

/-- A family of gluing data consists of
1. An index type `J`
2. A locally ringed space `U i` for each `i : J`.
3. A locally ringed space `V i j` for each `i j : J`.
   (Note that this is `J × J → LocallyRingedSpace` rather than `J → J → LocallyRingedSpace` to
   connect to the limits library more easily.)
4. An open immersion `f i j : V i j ⟶ U i` for each `i j : J`.
5. A transition map `t i j : V i j ⟶ V j i` for each `i j : J`.

such that
6. `f i i` is an isomorphism.
7. `t i i` is the identity.
8. `V i j ×[U i] V i k ⟶ V i j ⟶ V j i` factors through `V j k ×[U j] V j i ⟶ V j i` via some
   `t' : V i j ×[U i] V i k ⟶ V j k ×[U j] V j i`.
9. `t' i j k ≫ t' j k i ≫ t' k i j = 𝟙 _`.

We can then glue the spaces `U i` together by identifying `V i j` with `V j i`, such
that the `U i`'s are open subspaces of the glued space.
-/
/-
**AlgebraicGeometry.LocallyRingedSpace.GlueData** 是 Mathlib 中的一个归纳类型，位于命名空间 `Alg
ebraicGeometry.LocallyRingedSpace`。
形式化陈述：Type (u_1 + 1)
参数：u_1 + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A family of gluing data consists of
1. An index type `J`
2. A locally ringed space `U i` for each `i : J`.
3. A locally ringed space `V i j` for each `i j : J`.
   (Note that this is `J × J → LocallyRingedSpace` rather than `J → J → LocallyR
ingedSpace` to
   connect to the limits library more easily.)
4. An open immersion `f i j : V i j ⟶ U i` for each `i j : J`.
5. A transition map `t i j : V i j ⟶ V j i` for each `i j : J`.

such that
6. `f i i` is an isomorphism.
7. `t i i` is the identity.
8. `V i j ×[U i] V i k ⟶ V i j ⟶ V j i` factors through `V j k ×[U j] V j i ⟶ V 
j i` via some
   `t' : V i j ×[U i] V i k ⟶ V j k ×[U j] V j i`.
9. `t' i j k ≫ t' j k i ≫ t' k i j = 𝟙 _`.

We can then glue the spaces `U i` together by identifying `V i j` with `V j i`, 
such
that the `U i`'s are open subspaces of the glued space.
-/
structure GlueData extends CategoryTheory.GlueData LocallyRingedSpace where
  f_open : ∀ i j, LocallyRingedSpace.IsOpenImmersion (f i j)

attribute [instance] GlueData.f_open

namespace GlueData

variable (D : GlueData.{u})

local notation "𝖣" => D.toGlueData

/-- The glue data of ringed spaces associated to a family of glue data of locally ringed spaces. -/
/-
**AlgebraicGeometry.LocallyRingedSpace.GlueData.toSheafedSpaceGlueData** 是 Mathl
ib 中的一个缩写定义，位于命名空间 `AlgebraicGeometry.LocallyRingedSpace.GlueData`。
形式化陈述：toSheafedSpaceGlueData : SheafedSpace.GlueData CommRingCat
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.LocallyRingedSpace.GlueData.f_open`：∀ (self : Algebrai
cGeometry.LocallyRingedSpace.GlueData) (i j : self.J),   AlgebraicGeometry.Local
lyRingedSpace.IsOpenImmersion (self.f i j)

--- 原说明 ---
The glue data of ringed spaces associated to a family of glue data of locally ri
nged spaces.
-/
abbrev toSheafedSpaceGlueData : SheafedSpace.GlueData CommRingCat :=
  { f_open := D.f_open
    toGlueData := 𝖣.mapGlueData forgetToSheafedSpace }

/-- The gluing as locally ringed spaces is isomorphic to the gluing as ringed spaces. -/
/-
**AlgebraicGeometry.LocallyRingedSpace.GlueData.isoSheafedSpace** 是 Mathlib 中的一个
缩写定义，位于命名空间 `AlgebraicGeometry.LocallyRingedSpace.GlueData`。
形式化陈述：isoSheafedSpace : 𝖣.glued.toSheafedSpace ≅ D.toSheafedSpaceGlueData.toGlue
Data.glued
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The gluing as locally ringed spaces is isomorphic to the gluing as ringed spaces
.
-/
abbrev isoSheafedSpace : 𝖣.glued.toSheafedSpace ≅ D.toSheafedSpaceGlueData.toGlueData.glued :=
  𝖣.gluedIso forgetToSheafedSpace

@[reassoc]
/-
**AlgebraicGeometry.LocallyRingedSpace.GlueData.** 是 Mathlib 中的一个定理，位于命名空间 `Alge
braicGeometry.LocallyRingedSpace.GlueData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ι_isoSheafedSpace_inv (i : D.J) :
    D.toSheafedSpaceGlueData.toGlueData.ι i ≫ D.isoSheafedSpace.inv =
      (𝖣.ι i).toShHom :=
  𝖣.ι_gluedIso_inv forgetToSheafedSpace i
/-
**AlgebraicGeometry.LocallyRingedSpace.GlueData.** 是 Mathlib 中的一个实例，位于命名空间 `Alge
braicGeometry.LocallyRingedSpace.GlueData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance ι_isOpenImmersion (i : D.J) : IsOpenImmersion (𝖣.ι i) := by
  dsimp [IsOpenImmersion]
  rw [← D.ι_isoSheafedSpace_inv]
  -- Porting note: the next lines were a single `apply_instance`
  apply +allowSynthFailures PresheafedSpace.IsOpenImmersion.comp
  exact (D.toSheafedSpaceGlueData).ιIsOpenImmersion i
/-
**AlgebraicGeometry.LocallyRingedSpace.GlueData.** 是 Mathlib 中的一个实例，位于命名空间 `Alge
braicGeometry.LocallyRingedSpace.GlueData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (i j k : D.J) : PreservesLimit (cospan (𝖣.f i j) (𝖣.f i k)) forgetToSheafedSpace :=
  inferInstance
/-
**AlgebraicGeometry.LocallyRingedSpace.GlueData.** 是 Mathlib 中的一个定理，位于命名空间 `Alge
braicGeometry.LocallyRingedSpace.GlueData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ι_jointly_surjective (x : 𝖣.glued) : ∃ (i : D.J) (y : D.U i), (𝖣.ι i).base y = x :=
  𝖣.ι_jointly_surjective
    ((LocallyRingedSpace.forgetToSheafedSpace.{u} ⋙ SheafedSpace.forget CommRingCat.{u}) ⋙
      forget TopCat.{u}) x

/-- The following diagram is a pullback, i.e. `Vᵢⱼ` is the intersection of `Uᵢ` and `Uⱼ` in `X`.
```
Vᵢⱼ ⟶ Uᵢ
 |      |
 ↓      ↓
 Uⱼ ⟶ X
```
-/
/-
**AlgebraicGeometry.LocallyRingedSpace.GlueData.vPullbackConeIsLimit** 是 Mathlib
 中的一个定义，位于命名空间 `AlgebraicGeometry.LocallyRingedSpace.GlueData`。
形式化陈述：vPullbackConeIsLimit (i j : D.J) : IsLimit (𝖣.vPullbackCone i j)
参数：i j : D.J。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.LocallyRingedSpace.GlueData.instPreservesLimitSheafedS
paceCommRingCatWalkingCospanCospanFForgetToSheafedSpace`：∀ (D : AlgebraicGeometr
y.LocallyRingedSpace.GlueData) (i j k : D.J),   CategoryTheory.Limits.PreservesL
imit (CategoryTheory.Limits.cospan (D…

--- 原说明 ---
The following diagram is a pullback, i.e. `Vᵢⱼ` is the intersection of `Uᵢ` and 
`Uⱼ` in `X`.
```
Vᵢⱼ ⟶ Uᵢ
 |      |
 ↓      ↓
 Uⱼ ⟶ X
```
-/
def vPullbackConeIsLimit (i j : D.J) : IsLimit (𝖣.vPullbackCone i j) :=
  𝖣.vPullbackConeIsLimitOfMap forgetToSheafedSpace i j
    (D.toSheafedSpaceGlueData.vPullbackConeIsLimit _ _)

end GlueData

end LocallyRingedSpace

end AlgebraicGeometry

