/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.RingTheory.Flat.Rank

/-!
# Rank of a finite flat morphism of schemes

In this file we define the rank `AlgebraicGeometry.Scheme.Hom.finrank` of a finite flat morphism of
schemes `f : X ⟶ Y`. It is locally constant and is characterized by the condition that the rank of
`Spec S ⟶ Spec R` at some prime `p` of `R` is the rank of `S` as an `R`-algebra at `p`.

## Main definitions

- `AlgebraicGeometry.Scheme.Hom.finrank`: For a morphism `f : X ⟶ Y` of schemes, the function
  `Y → ℕ` sending `y` to the rank of `f_* 𝒪_X` over `𝒪_Y` at `y`. Instead of talking about
  sheaves, we define it by choosing an open neighbourhood of `y`.
  This is sometimes also called the degree of a morphism in the literature.

## Main results

- `AlgebraicGeometry.Scheme.Hom.isLocallyConstant_finrank`: The rank function of a finite flat
  locally finitely presented morphism is locally constant.
- `AlgebraicGeometry.Scheme.Hom.one_le_finrank_iff_surjective`: The rank function is at least `1`
  everywhere if and only if the morphism is surjective.
- `AlgebraicGeometry.Scheme.Hom.isIso_iff_finrank_eq`: A finite flat locally finitely presented
  morphism is an isomorphism if and only if its rank is constant equal to `1`.

## TODO

- Relate `Hom.finrank f y` to the rank of `f_* 𝒪_X` over `𝒪_Y` at `y` when the API for
  locally free sheaves of modules is developed.
-/

public section

open CategoryTheory Limits TopologicalSpace TensorProduct

universe u

namespace AlgebraicGeometry

noncomputable section

variable {X S Y T : Scheme.{u}} (f : X ⟶ S)

/-- The rank of a morphism `f : X ⟶ S` of schemes at a point `s : S`, when `S` is affine.
This is used as an auxiliary definition to define `AlgebraicGeometry.finrank`. -/
/-
**AlgebraicGeometry.IsAffine.finrank** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeometr
y`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The rank of a morphism `f : X ⟶ S` of schemes at a point `s : S`, when `S` is af
fine.
This is used as an auxiliary definition to define `AlgebraicGeometry.finrank`.
-/
private def IsAffine.finrank [IsAffine S] (f : X ⟶ S) (s : S) : ℕ :=
  f.appTop.hom.finrank (S.isoSpec.hom s)
/-
**AlgebraicGeometry.IsAffine.finrank_of_isPullback** 是 Mathlib 中的一个引理，位于命名空间 `Al
gebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma IsAffine.finrank_of_isPullback [IsAffine S] [IsAffine T]
    (f' : Y ⟶ T) (g' : Y ⟶ X) (g : T ⟶ S) (h : IsPullback g' f' f g) [Flat f] [IsFinite f]
    (s : S) (t : T) (hs : g t = s) :
    IsAffine.finrank f' t = IsAffine.finrank f s := by
  subst hs
  have : IsAffine X := isAffine_of_isAffineHom f
  have : IsPushout f.appTop g.appTop g'.appTop f'.appTop := isPushout_appTop_of_isPullback h
  dsimp [finrank]
  rw [CommRingCat.finrank_eq_of_isPushout this f.flat_appTop f.finite_appTop (T.isoSpec.hom t),
    ← Scheme.Hom.comp_apply, ← Scheme.isoSpec_hom_naturality]
  rfl
/-
**AlgebraicGeometry.IsAffine.finrank_snd** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeo
metry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma IsAffine.finrank_snd [IsAffine S] [IsAffine T]
    (g : T ⟶ S) [Flat f] [IsFinite f] (x : T) :
    IsAffine.finrank (pullback.snd f g) x = IsAffine.finrank f (g x) :=
  finrank_of_isPullback f _ _ _ (.of_hasPullback _ _) _ _ rfl
/-
**AlgebraicGeometry.IsAffine.finrank_comp_left_of_isIso** 是 Mathlib 中的一个引理，位于命名空
间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma IsAffine.finrank_comp_left_of_isIso [IsAffine S]
    (f : X ⟶ Y) (g : Y ⟶ S) [IsIso f] [IsFinite g] [Flat g] :
    IsAffine.finrank (f ≫ g) = IsAffine.finrank g := by
  ext z
  apply finrank_of_isPullback g (f ≫ g) f (𝟙 _) _ _ _ rfl
  exact IsPullback.of_horiz_isIso (by simp)

/-- The rank of a morphism `f : X ⟶ S` of schemes at a point `s : S`. When `f` is finite,
flat and locally of finite presentation, this is a locally constant function (see
`AlgebraicGeometry.isLocallyConstant_finrank`). -/
@[stacks 02KA "second part"]
/-
**AlgebraicGeometry.Scheme.Hom.finrank** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeome
try.Scheme.Hom`。
形式化陈述：{X S : AlgebraicGeometry.Scheme} → (X ⟶ S) → ↥S → ℕ
参数：X ⟶ S。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The rank of a morphism `f : X ⟶ S` of schemes at a point `s : S`. When `f` is fi
nite,
flat and locally of finite presentation, this is a locally constant function (se
e
`AlgebraicGeometry.isLocallyConstant_finrank`).
-/
def Scheme.Hom.finrank {X S : Scheme.{u}} (f : X ⟶ S) (s : S) : ℕ :=
  IsAffine.finrank (pullback.snd f (S.affineOpenCover.f <| S.affineOpenCover.idx s))
    (S.affineOpenCover.covers s).choose
/-
**AlgebraicGeometry.Scheme.Hom.finrank_eq_finrank_snd_of_isAffine** 是 Mathlib 中的
一个引理，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma Scheme.Hom.finrank_eq_finrank_snd_of_isAffine (g : T ⟶ S) [IsAffine T] (t : T)
    [Flat f] [IsFinite f] :
    f.finrank (g t) = IsAffine.finrank (pullback.snd f g) t := by
  let i := S.affineOpenCover.f (S.affineOpenCover.idx (g t))
  obtain ⟨y, hyl, hyr⟩ := Scheme.Pullback.exists_preimage_pullback
    (S.affineOpenCover.covers <| g t).choose t (S.affineOpenCover.covers <| g t).choose_spec
  obtain ⟨R, u, hu, z, rfl⟩ := (pullback i g).exists_Spec_apply_eq y
  trans IsAffine.finrank (pullback.snd (pullback.snd f g) (u ≫ pullback.snd _ _)) z
  · refine (IsAffine.finrank_of_isPullback _ _ ?_ ?_ ?_ _ _ ?_).symm
    · exact pullback.map _ _ _ _ (pullback.fst f g) (u ≫ pullback.fst _ _) g
        pullback.condition.symm (by simp [← pullback.condition]; rfl)
    · exact u ≫ pullback.fst _ _
    · apply IsPullback.map_fst_comp_fst_snd_comp_fst
    · exact hyl
  · simp_rw [← hyr]
    exact IsAffine.finrank_snd (pullback.snd f g) (u ≫ pullback.snd _ _) z
/-
**AlgebraicGeometry.Scheme.Hom.finrank_eq_of_isAffine** 是 Mathlib 中的一个引理，位于命名空间 
`AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma Scheme.Hom.finrank_eq_of_isAffine [IsAffine S] [Flat f] [IsFinite f] (s : S) :
    f.finrank s = IsAffine.finrank f s := by
  rw [show s = (𝟙 S : S ⟶ S) s from rfl, finrank_eq_finrank_snd_of_isAffine,
    IsAffine.finrank_snd]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**AlgebraicGeometry.Scheme.Hom.finrank_SpecMap_eq_finrank** 是 Mathlib 中的一个定理，位于命
名空间 `AlgebraicGeometry.Scheme.Hom`。
形式化陈述：∀ {R S : CommRingCat} {f : R ⟶ S},   (CommRingCat.Hom.hom f).Finite →     
(CommRingCat.Hom.hom f).Flat →       AlgebraicGeometry.Scheme.Hom.finrank (Algeb
raicGeometry.Spec.map f) = (CommRingCat.Hom.hom f).finrank
参数：CommRingCat.Hom.hom f；CommRingCat.Hom.hom f；AlgebraicGeometry.Spec.map f；Comm
RingCat.Hom.hom f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Hom.finite_appTop`：∀ {X Y : AlgebraicGeometry.S
cheme} (f : X ⟶ Y) [AlgebraicGeometry.IsAffine Y] [AlgebraicGeometry.IsFinite f]
,   (CommRingCat.Hom.hom (Algebr…
· 使用定理 `AlgebraicGeometry.Scheme.Hom.flat_appTop`：∀ {X Y : AlgebraicGeometry.Sch
eme} (f : X ⟶ Y) [AlgebraicGeometry.IsAffine X] [AlgebraicGeometry.IsAffine Y]  
 [AlgebraicGeometry.Flat f], (…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.AlgebraicGeometry.Morphisms.FlatRank.0.AlgebraicGeometr
y.Scheme.Hom.finrank_eq_of_isAffine`：∀ {X S : AlgebraicGeometry.Scheme} (f : X ⟶
 S) [inst : AlgebraicGeometry.IsAffine S] [AlgebraicGeometry.Flat f]   [Algebrai
cGeometry.IsFinit…
· 使用定理 `_private.Mathlib.AlgebraicGeometry.Morphisms.FlatRank.0.AlgebraicGeometr
y.IsAffine.finrank.eq_1`：∀ {X S : AlgebraicGeometry.Scheme} [inst : AlgebraicGeo
metry.IsAffine S] (f : X ⟶ S) (s : ↥S),   AlgebraicGeometry.IsAffine.finrank✝ f 
s =  …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `AlgebraicGeometry.Scheme.ΓSpecIso_naturality`：ΓSpecIso_naturality {R S :
 CommRingCat.{u}} (f : R ⟶ S) : (Spec.map f).appTop ≫ (ΓSpecIso S).hom = (ΓSpecI
so R).hom ≫ f
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `RingHom.finrank_comp_right_of_bijective`：RingHom.finrank_comp_right_of_b
ijective {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] (f : R ->+* S) (
g : S ->+* T) (hg : Function.…
· 使用定理 `CategoryTheory.ConcreteCategory.bijective_of_isIso`：bijective_of_isIso {
X Y : C} (f : X ⟶ Y) [IsIso f] : Function.Bijective f
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `RingHom.Finite.comp`：comp {g : B ->+* C} {f : A ->+* B} (hg : g.Finite) 
(hf : f.Finite) : (g.comp f).Finite
· 使用定理 `RingHom.Finite.of_surjective`：of_surjective (f : A ->+* B) (hf : Surject
ive f) : f.Finite
· 使用定理 `Function.Bijective.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → 
β}, Function.Bijective f → Function.Surjective f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用引理 `RingHom.Flat.comp`：comp {f : R ->+* S} {g : S ->+* T} (hf : f.Flat) (hg 
: g.Flat) : Flat (g.comp f)
· 使用引理 `RingHom.Flat.of_bijective`：of_bijective {f : R ->+* S} (hf : Function.Bi
jective f) : Flat f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AlgebraicGeometry.Scheme.isoSpec_Spec_hom`：∀ (R : CommRingCat),   (Algeb
raicGeometry.Spec R).isoSpec.hom = AlgebraicGeometry.Spec.map (AlgebraicGeometry
.Scheme.ΓSpecIso R).hom
· 使用定理 `AlgebraicGeometry.SpecMap_ΓSpecIso_hom`：SpecMap_ΓSpecIso_hom (R : CommRi
ngCat.{u}) : Spec.map ((Scheme.ΓSpecIso R).hom) = (Spec R).toSpecΓ
· 使用定理 `AlgebraicGeometry.toSpecΓ_SpecMap_ΓSpecIso_inv`：toSpecΓ_SpecMap_ΓSpecIso
_inv (R : CommRingCat.{u}) : (Spec R).toSpecΓ ≫ Spec.map (Scheme.ΓSpecIso R).inv
 = 𝟙 _
· 使用引理 `RingHom.finrank_comp_left_of_bijective`：RingHom.finrank_comp_left_of_bij
ective {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] (f : R ->+* S) (g 
: S ->+* T) (hf : Function.B…
-/
lemma Scheme.Hom.finrank_SpecMap_eq_finrank {R S : CommRingCat.{u}} {f : R ⟶ S} (hf₁ : f.hom.Finite)
    (hf₂ : f.hom.Flat) :
    finrank (Spec.map f) = f.hom.finrank := by
  simp only [← IsFinite.SpecMap_iff, ← Flat.SpecMap_iff] at hf₁ hf₂
  have hf₁ : (Spec.map f).appTop.hom.Finite := (Spec.map f).finite_appTop
  have hf₂ : (Spec.map f).appTop.hom.Flat := (Spec.map f).flat_appTop
  ext
  rw [finrank_eq_of_isAffine, IsAffine.finrank]
  have : f = (Scheme.ΓSpecIso R).inv ≫ (Spec.map f).appTop ≫ (Scheme.ΓSpecIso S).hom := by simp
  conv_rhs => rw [this]
  dsimp
  rw [RingHom.finrank_comp_right_of_bijective _ _ (ConcreteCategory.bijective_of_isIso _)]
  · rw [RingHom.finrank_comp_left_of_bijective _ _ (ConcreteCategory.bijective_of_isIso _) hf₁ hf₂]
  · exact .comp (.of_surjective _ (ConcreteCategory.bijective_of_isIso _).surjective) hf₁
  · exact .comp hf₂ (.of_bijective (ConcreteCategory.bijective_of_isIso _))
  · simp [isoSpec_Spec_hom, SpecMap_ΓSpecIso_hom, ← AlgebraicGeometry.Spec.map_apply,
      ← Scheme.Hom.comp_apply, toSpecΓ_SpecMap_ΓSpecIso_inv]
/-
**AlgebraicGeometry.Scheme.Hom.finrank_SpecMap_algebraMap** 是 Mathlib 中的一个定理，位于命
名空间 `AlgebraicGeometry.Scheme.Hom`。
形式化陈述：∀ (R S : Type u) [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algeb
ra R S] [Module.Finite R S] [Module.Flat R S]   (x : PrimeSpectrum R),   Algebra
icGeometry.Scheme.Hom.finrank (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (al
gebraMap R S))) x =     Module.rankAtStalk S x
参数：R S : Type u；x : PrimeSpectrum R；AlgebraicGeometry.Spec.map (CommRingCat.ofHo
m (algebraMap R S))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.Hom.finrank_SpecMap_eq_finrank`：∀ {R S : CommRi
ngCat} {f : R ⟶ S},   (CommRingCat.Hom.hom f).Finite →     (CommRingCat.Hom.hom 
f).Flat →       AlgebraicGeometry.Scheme.Hom.…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.ConcreteCategory.hom_ofHom`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (C
 → Type w)}   {inst_1 : outPara…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `RingHom.finrank_algebraMap`：RingHom.finrank_algebraMap : (algebraMap R S
).finrank = Module.rankAtStalk (R
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Scheme.Hom.finrank_SpecMap_algebraMap (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S] [Module.Flat R S] (x : PrimeSpectrum R) :
    finrank (Spec.map (CommRingCat.ofHom <| algebraMap R S)) x = Module.rankAtStalk S x := by
  rw [finrank_SpecMap_eq_finrank]
  · simp
  · simpa [RingHom.finite_algebraMap]
  · simpa [RingHom.flat_algebraMap_iff]

variable (f : X ⟶ Y) [Flat f] [IsFinite f]

@[simp]
/-
**AlgebraicGeometry.Scheme.Hom.finrank_comp_left_of_isIso** 是 Mathlib 中的一个定理，位于命
名空间 `AlgebraicGeometry.Scheme.Hom`。
形式化陈述：∀ {X S Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) (g : Y ⟶ S) [CategoryTheo
ry.IsIso f] [AlgebraicGeometry.Flat g]   [AlgebraicGeometry.IsFinite g],   Algeb
raicGeometry.Scheme.Hom.finrank (CategoryTheory.CategoryStruct.comp f g) = Algeb
raicGeometry.Scheme.Hom.finrank g
参数：f : X ⟶ Y；g : Y ⟶ S；CategoryTheory.CategoryStruct.comp f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.pullbackRightPullbackFstIso_inv_snd_snd`：pullbackR
ightPullbackFstIso_inv_snd_snd : (pullbackRightPullbackFstIso f g f').inv ≫ pull
back.snd _ _ ≫ pullback.snd _ _ = pullback.snd _ _
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `_private.Mathlib.AlgebraicGeometry.Morphisms.FlatRank.0.AlgebraicGeometr
y.Scheme.Hom.finrank.eq_1`：∀ {X S : AlgebraicGeometry.Scheme} (f : X ⟶ S) (s : ↥
S),   AlgebraicGeometry.Scheme.Hom.finrank f s =     AlgebraicGeometry.IsAffine.
finrank…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `_private.Mathlib.AlgebraicGeometry.Morphisms.FlatRank.0.AlgebraicGeometr
y.IsAffine.finrank_comp_left_of_isIso`：∀ {X S Y : AlgebraicGeometry.Scheme} [ins
t : AlgebraicGeometry.IsAffine S] (f : X ⟶ Y) (g : Y ⟶ S)   [CategoryTheory.IsIs
o f] [AlgebraicGeom…
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `AlgebraicGeometry.IsFinite.instSndScheme`：∀ {X Y Z : AlgebraicGeometry.S
cheme} (f : X ⟶ Z) (g : Y ⟶ Z) [AlgebraicGeometry.IsFinite f],   AlgebraicGeomet
ry.IsFinite (CategoryTheory.Li…
· 使用定理 `AlgebraicGeometry.Flat.instSndScheme`：∀ {X Y Z : AlgebraicGeometry.Schem
e} (f : X ⟶ Z) (g : Y ⟶ Z) [AlgebraicGeometry.Flat f],   AlgebraicGeometry.Flat 
(CategoryTheory.Limits.pul…
-/
lemma Scheme.Hom.finrank_comp_left_of_isIso (f : X ⟶ Y) (g : Y ⟶ S)
    [IsIso f] [Flat g] [IsFinite g] :
    finrank (f ≫ g) = finrank g := by
  ext z
  let e : pullback (f ≫ g) (S.affineOpenCover.f (S.affineOpenCover.idx z)) ≅
      pullback g (S.affineOpenCover.f (S.affineOpenCover.idx z)) :=
    (pullbackRightPullbackFstIso g (S.affineOpenCover.f (S.affineOpenCover.idx z)) f).symm ≪≫
      asIso (pullback.snd f (pullback.fst g (S.affineOpenCover.f _)))
  have : e.hom ≫ pullback.snd _ _ = pullback.snd _ _ := by simp [e]
  rw [finrank, finrank, ← this, IsAffine.finrank_comp_left_of_isIso]
/-
**AlgebraicGeometry.Scheme.Hom.finrank_pullback_snd** 是 Mathlib 中的一个定理，位于命名空间 `A
lgebraicGeometry.Scheme.Hom`。
形式化陈述：∀ {X Y Z : AlgebraicGeometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z) [AlgebraicGeo
metry.Flat f] [AlgebraicGeometry.IsFinite f]   (y : ↥Y),   AlgebraicGeometry.Sch
eme.Hom.finrank (CategoryTheory.Limits.pullback.snd f g) y =     AlgebraicGeomet
ry.Scheme.Hom.finrank f (g y)
参数：f : X ⟶ Z；g : Y ⟶ Z；y : ↥Y；CategoryTheory.Limits.pullback.snd f g；g y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `AlgebraicGeometry.Scheme.exists_Spec_apply_eq`：∀ {X : AlgebraicGeometry.
Scheme} (x : ↥X), ∃ R f, ∃ (_ : AlgebraicGeometry.IsOpenImmersion f), ∃ y, f y =
 x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.Scheme.Hom.comp_apply`：comp_apply {X Y Z : Scheme} (f 
: X ⟶ Y) (g : Y ⟶ Z) (x : X) : (f ≫ g) x = g (f x)
· 使用定理 `_private.Mathlib.AlgebraicGeometry.Morphisms.FlatRank.0.AlgebraicGeometr
y.Scheme.Hom.finrank_eq_finrank_snd_of_isAffine`：∀ {X S T : AlgebraicGeometry.Sc
heme} (f : X ⟶ S) (g : T ⟶ S) [inst : AlgebraicGeometry.IsAffine T] (t : ↥T)   [
AlgebraicGeometry.Flat f] [Al…
· 使用定理 `AlgebraicGeometry.Flat.instSndScheme`：∀ {X Y Z : AlgebraicGeometry.Schem
e} (f : X ⟶ Z) (g : Y ⟶ Z) [AlgebraicGeometry.Flat f],   AlgebraicGeometry.Flat 
(CategoryTheory.Limits.pul…
· 使用定理 `AlgebraicGeometry.IsFinite.instSndScheme`：∀ {X Y Z : AlgebraicGeometry.S
cheme} (f : X ⟶ Z) (g : Y ⟶ Z) [AlgebraicGeometry.IsFinite f],   AlgebraicGeomet
ry.IsFinite (CategoryTheory.Li…
· 使用定理 `CategoryTheory.Limits.pullbackLeftPullbackSndIso_hom_snd`：pullbackLeftPu
llbackSndIso_hom_snd : (pullbackLeftPullbackSndIso f g g').hom ≫ pullback.snd _ 
_ = pullback.snd _ _
· 使用定理 `_private.Mathlib.AlgebraicGeometry.Morphisms.FlatRank.0.AlgebraicGeometr
y.Scheme.Hom.finrank_eq_of_isAffine`：∀ {X S : AlgebraicGeometry.Scheme} (f : X ⟶
 S) [inst : AlgebraicGeometry.IsAffine S] [AlgebraicGeometry.Flat f]   [Algebrai
cGeometry.IsFinit…
· 使用定理 `AlgebraicGeometry.Flat.instOfIsOpenImmersion`：∀ {X Y : AlgebraicGeometry
.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.IsOpenImmersion f], AlgebraicGeometry.Fl
at f
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.of_isIso`：∀ {Y Z : AlgebraicGeometry.S
cheme} (g : Y ⟶ Z) [CategoryTheory.IsIso g], AlgebraicGeometry.IsOpenImmersion g
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `AlgebraicGeometry.IsFinite.instCompScheme`：∀ {X Y : AlgebraicGeometry.Sc
heme} (f : X ⟶ Y) {Z : AlgebraicGeometry.Scheme} (g : Y ⟶ Z) [AlgebraicGeometry.
IsFinite f]   [AlgebraicGeometr…
· 使用定理 `AlgebraicGeometry.IsFinite.instOfIsClosedImmersion`：∀ {X Y : AlgebraicGe
ometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.IsClosedImmersion f], AlgebraicGeo
metry.IsFinite f
· 使用定理 `AlgebraicGeometry.IsClosedImmersion.instOfIsIsoScheme`：∀ {X Y : Algebrai
cGeometry.Scheme} (f : X ⟶ Y) [CategoryTheory.IsIso f], AlgebraicGeometry.IsClos
edImmersion f
· 使用定理 `AlgebraicGeometry.Scheme.Hom.finrank_comp_left_of_isIso`：∀ {X S Y : Alge
braicGeometry.Scheme} (f : X ⟶ Y) (g : Y ⟶ S) [CategoryTheory.IsIso f] [Algebrai
cGeometry.Flat g]   [AlgebraicGeometry.IsFini…
-/
lemma Scheme.Hom.finrank_pullback_snd {Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
    [Flat f] [IsFinite f] (y : Y) :
    finrank (pullback.snd f g) y = finrank f (g y) := by
  obtain ⟨R, i, _, y', rfl⟩ := Y.exists_Spec_apply_eq y
  rw [← Scheme.Hom.comp_apply, finrank_eq_finrank_snd_of_isAffine,
    finrank_eq_finrank_snd_of_isAffine, ← pullbackLeftPullbackSndIso_hom_snd f g i,
    ← finrank_eq_of_isAffine, ← finrank_eq_of_isAffine, finrank_comp_left_of_isIso]
/-
**AlgebraicGeometry.Scheme.Hom.finrank_of_isPullback** 是 Mathlib 中的一个定理，位于命名空间 `
AlgebraicGeometry.Scheme.Hom`。
形式化陈述：∀ {P X Y Z : AlgebraicGeometry.Scheme} (fst : P ⟶ X) (snd : P ⟶ Y) (f : X 
⟶ Z) (g : Y ⟶ Z),   CategoryTheory.IsPullback fst snd f g →     ∀ [AlgebraicGeom
etry.Flat f] [AlgebraicGeometry.IsFinite f] (y : ↥Y),       AlgebraicGeometry.Sc
heme.Hom.finrank snd y = AlgebraicGeometry.Scheme.Hom.finrank f (g y)
参数：fst : P ⟶ X；snd : P ⟶ Y；f : X ⟶ Z；g : Y ⟶ Z；y : ↥Y；g y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.IsPullback.isoPullback_hom_snd`：isoPullback_hom_snd (h : 
IsPullback fst snd f g) [HasPullback f g] : h.isoPullback.hom ≫ pullback.snd _ _
 = snd
· 使用定理 `AlgebraicGeometry.Scheme.Hom.finrank_comp_left_of_isIso`：∀ {X S Y : Alge
braicGeometry.Scheme} (f : X ⟶ Y) (g : Y ⟶ S) [CategoryTheory.IsIso f] [Algebrai
cGeometry.Flat g]   [AlgebraicGeometry.IsFini…
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `AlgebraicGeometry.Flat.instSndScheme`：∀ {X Y Z : AlgebraicGeometry.Schem
e} (f : X ⟶ Z) (g : Y ⟶ Z) [AlgebraicGeometry.Flat f],   AlgebraicGeometry.Flat 
(CategoryTheory.Limits.pul…
· 使用定理 `AlgebraicGeometry.IsFinite.instSndScheme`：∀ {X Y Z : AlgebraicGeometry.S
cheme} (f : X ⟶ Z) (g : Y ⟶ Z) [AlgebraicGeometry.IsFinite f],   AlgebraicGeomet
ry.IsFinite (CategoryTheory.Li…
· 使用定理 `AlgebraicGeometry.Scheme.Hom.finrank_pullback_snd`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z) [AlgebraicGeometry.Flat f] [AlgebraicGeo
metry.IsFinite f]   (y : ↥Y),   Algebra…
-/
lemma Scheme.Hom.finrank_of_isPullback {P X Y Z : Scheme.{u}} (fst : P ⟶ X) (snd : P ⟶ Y)
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : IsPullback fst snd f g) [Flat f] [IsFinite f] (y : Y) :
    finrank snd y = finrank f (g y) := by
  rw [← h.isoPullback_hom_snd, finrank_comp_left_of_isIso, finrank_pullback_snd]
/-
**AlgebraicGeometry.Scheme.Hom.finrank_pullback_fst** 是 Mathlib 中的一个定理，位于命名空间 `A
lgebraicGeometry.Scheme.Hom`。
形式化陈述：∀ {X Y Z : AlgebraicGeometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z) [AlgebraicGeo
metry.Flat f] [AlgebraicGeometry.IsFinite f]   (y : ↥Y),   AlgebraicGeometry.Sch
eme.Hom.finrank (CategoryTheory.Limits.pullback.fst g f) y =     AlgebraicGeomet
ry.Scheme.Hom.finrank f (g y)
参数：f : X ⟶ Z；g : Y ⟶ Z；y : ↥Y；CategoryTheory.Limits.pullback.fst g f；g y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Hom.finrank_of_isPullback`：∀ {P X Y Z : Algebra
icGeometry.Scheme} (fst : P ⟶ X) (snd : P ⟶ Y) (f : X ⟶ Z) (g : Y ⟶ Z),   Catego
ryTheory.IsPullback fst snd f g →     ∀ …
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `CategoryTheory.IsPullback.flip`：flip (h : IsPullback fst snd f g) : IsPu
llback snd fst g f
· 使用定理 `CategoryTheory.IsPullback.of_hasPullback`：of_hasPullback (f : X ⟶ Z) (g 
: Y ⟶ Z) [HasPullback f g] : IsPullback (pullback.fst f g) (pullback.snd f g) f 
g
-/
lemma Scheme.Hom.finrank_pullback_fst {Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
    [Flat f] [IsFinite f] (y : Y) :
    finrank (pullback.fst g f) y = finrank f (g y) :=
  finrank_of_isPullback (pullback.snd g f) _ _ _ (.flip <| .of_hasPullback _ _) y

set_option backward.isDefEq.respectTransparency.types false in
nonrec lemma Scheme.Hom.one_le_finrank_map (x : X) : 1 ≤ finrank f (f x) := by
  wlog hY : ∃ R, Y = Spec R
  · obtain ⟨R, g, hg, y, hy⟩ := Y.exists_Spec_apply_eq (f x)
    rw [← hy, ← finrank_pullback_snd]
    obtain ⟨z, hzl, hzr⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := g) x y hy.symm
    rw [hzr.symm]
    refine this _ _ ⟨_, rfl⟩
  obtain ⟨R, rfl⟩ := hY
  wlog hX : ∃ S, X = Spec S
  · have _ : IsAffine X := isAffine_of_isAffineHom f
    have heq : f x = (X.isoSpec.inv ≫ f) (X.isoSpec.hom x) := by simp
    rw [← finrank_comp_left_of_isIso X.isoSpec.inv, heq]
    exact this _ _ _ ⟨_, rfl⟩
  obtain ⟨S, rfl⟩ := hX
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  simp only [IsFinite.SpecMap_iff, Flat.SpecMap_iff] at *
  rw [finrank_SpecMap_eq_finrank ‹_› ‹_›]
  algebraize [φ.hom]
  rw [← RingHom.algebraMap_toAlgebra φ.hom, RingHom.finrank_algebraMap, Nat.add_one_le_iff,
    PrimeSpectrum.rankAtStalk_pos_iff_mem_range_comap]
  use x
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- A finite flat locally finitely presented morphism is surjective if and only if its rank
function is at least `1` everywhere. -/
nonrec lemma Scheme.Hom.one_le_finrank_iff_surjective : 1 ≤ finrank f ↔ Surjective f := by
  refine ⟨fun h ↦ ?_, fun _ ↦ ?_⟩
  · wlog hY : ∃ R, Y = Spec R
    · rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @Surjective) Y.affineCover]
      intro i
      dsimp only [Scheme.Cover.pullbackHom]
      refine this _ (fun y ↦ ?_) ⟨_, rfl⟩
      rw [finrank_pullback_snd]
      exact h _
    obtain ⟨R, rfl⟩ := hY
    wlog hX : ∃ S, X = Spec S
    · have _ : IsAffine X := isAffine_of_isAffineHom f
      rw [← MorphismProperty.cancel_left_of_respectsIso @Surjective X.isoSpec.inv]
      refine this _ _ (fun x ↦ ?_) ⟨_, rfl⟩
      rw [finrank_comp_left_of_isIso]
      exact h x
    obtain ⟨S, rfl⟩ := hX
    obtain ⟨φ, rfl⟩ := Spec.map_surjective f
    constructor
    intro x
    specialize h x
    simp only [IsFinite.SpecMap_iff, Flat.SpecMap_iff] at *
    rw [finrank_SpecMap_eq_finrank ‹_› ‹_›] at h
    algebraize [φ.hom]
    exact (PrimeSpectrum.rankAtStalk_pos_iff_mem_range_comap _).mp h
  · intro y
    obtain ⟨x, rfl⟩ := f.surjective y
    exact one_le_finrank_map f x

/-- The rank of a finite flat locally finitely presented morphism is locally constant. -/
nonrec lemma Scheme.Hom.isLocallyConstant_finrank [LocallyOfFinitePresentation f] :
    IsLocallyConstant (finrank f) := by
  wlog hY : ∃ R, Y = Spec R
  · rw [IsLocallyConstant.iff_exists_open]
    intro y
    obtain ⟨R, g, _, x, rfl⟩ := Y.exists_Spec_apply_eq y
    simp_rw [IsLocallyConstant.iff_exists_open] at this
    obtain ⟨U, hU, hxU, H⟩ := this (pullback.snd f g) ⟨_, rfl⟩ x
    refine ⟨g ''ᵁ ⟨U, hU⟩, (g ''ᵁ ⟨U, hU⟩).2, ⟨x, hxU, rfl⟩, fun y ↦ ?_⟩
    rintro ⟨y', (hyU : y' ∈ U), (rfl : g y' = y)⟩
    rw [← finrank_pullback_snd _ g, ← finrank_pullback_snd _ g]
    exact H y' hyU
  obtain ⟨R, rfl⟩ := hY
  wlog hX : ∃ S, X = Spec S
  · have _ : IsAffine X := isAffine_of_isAffineHom f
    rw [← finrank_comp_left_of_isIso X.isoSpec.inv]
    exact this _ _ ⟨_, rfl⟩
  obtain ⟨S, rfl⟩ := hX
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  simp only [Flat.SpecMap_iff, IsFinite.SpecMap_iff, LocallyOfFinitePresentation.SpecMap_iff] at *
  rw [finrank_SpecMap_eq_finrank ‹_› ‹_›]
  algebraize [φ.hom]
  have := Module.FinitePresentation.of_finite_of_finitePresentation
  exact Module.isLocallyConstant_rankAtStalk

set_option backward.isDefEq.respectTransparency false in
/-- The rank of an isomorphism is `1`. -/
/-
**AlgebraicGeometry.Scheme.Hom.finrank_eq_one_of_isIso** 是 Mathlib 中的一个定理，位于命名空间
 `AlgebraicGeometry.Scheme.Hom`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [CategoryTheory.IsIso f], A
lgebraicGeometry.Scheme.Hom.finrank f = 1
参数：f : X ⟶ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `AlgebraicGeometry.Scheme.exists_Spec_apply_eq`：∀ {X : AlgebraicGeometry.
Scheme} (x : ↥X), ∃ R f, ∃ (_ : AlgebraicGeometry.IsOpenImmersion f), ∃ y, f y =
 x
· 使用引理 `PrimeSpectrum.nontrivial`：nontrivial (p : PrimeSpectrum R) : Nontrivial 
R
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.Scheme.Hom.finrank_pullback_snd`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z) [AlgebraicGeometry.Flat f] [AlgebraicGeo
metry.IsFinite f]   (y : ↥Y),   Algebra…
· 使用定理 `AlgebraicGeometry.Flat.instOfIsOpenImmersion`：∀ {X Y : AlgebraicGeometry
.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.IsOpenImmersion f], AlgebraicGeometry.Fl
at f
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.of_isIso`：∀ {Y Z : AlgebraicGeometry.S
cheme} (g : Y ⟶ Z) [CategoryTheory.IsIso g], AlgebraicGeometry.IsOpenImmersion g
· 使用定理 `AlgebraicGeometry.IsFinite.instOfIsClosedImmersion`：∀ {X Y : AlgebraicGe
ometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.IsClosedImmersion f], AlgebraicGeo
metry.IsFinite f
· 使用定理 `AlgebraicGeometry.IsClosedImmersion.instOfIsIsoScheme`：∀ {X Y : Algebrai
cGeometry.Scheme} (f : X ⟶ Y) [CategoryTheory.IsIso f], AlgebraicGeometry.IsClos
edImmersion f
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `AlgebraicGeometry.Scheme.Hom.finrank_comp_left_of_isIso`：∀ {X S Y : Alge
braicGeometry.Scheme} (f : X ⟶ Y) (g : Y ⟶ S) [CategoryTheory.IsIso f] [Algebrai
cGeometry.Flat g]   [AlgebraicGeometry.IsFini…
· 使用定理 `AlgebraicGeometry.Spec.map_id`：∀ (R : CommRingCat),   AlgebraicGeometry.
Spec.map (CategoryTheory.CategoryStruct.id R) =     CategoryTheory.CategoryStruc
t.id (AlgebraicGeom…
· 使用定理 `AlgebraicGeometry.Scheme.Hom.finrank_SpecMap_eq_finrank`：∀ {R S : CommRi
ngCat} {f : R ⟶ S},   (CommRingCat.Hom.hom f).Finite →     (CommRingCat.Hom.hom 
f).Flat →       AlgebraicGeometry.Scheme.Hom.…
· 使用定理 `RingHom.Finite.id`：id : Finite (RingHom.id A)
· 使用引理 `RingHom.Flat.id`：id : RingHom.Flat (RingHom.id R)
· 使用引理 `CommRingCat.hom_id`：hom_id {R : CommRingCat} : (𝟙 R : R ⟶ R).hom = RingH
om.id R
· 使用引理 `Pi.one_apply`：one_apply (i : ι) : (1 : forall i, M i) i = 1
· 使用定理 `Algebra.algebraMap_self`：∀ {R : Type u} [inst : CommSemiring R], algebra
Map R R = RingHom.id R
· 使用引理 `RingHom.finrank_algebraMap`：RingHom.finrank_algebraMap : (algebraMap R S
).finrank = Module.rankAtStalk (R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `Module.rankAtStalk_eq_finrank_of_free`：rankAtStalk_eq_finrank_of_free [M
odule.Free R M] : rankAtStalk (R
· 使用定理 `Module.finrank_self`：finrank_self : finrank R R = 1
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The rank of an isomorphism is `1`.
-/
lemma Scheme.Hom.finrank_eq_one_of_isIso (f : X ⟶ Y) [IsIso f] : finrank f = 1 := by
  ext y
  obtain ⟨R, g, _, y, rfl⟩ := Y.exists_Spec_apply_eq y
  have : Nontrivial R := y.nontrivial
  rw [← finrank_pullback_snd, ← Category.comp_id (pullback.snd f g), finrank_comp_left_of_isIso,
    ← Spec.map_id, finrank_SpecMap_eq_finrank, CommRingCat.hom_id, Pi.one_apply,
    ← Algebra.algebraMap_self, RingHom.finrank_algebraMap]
  · simp
  · exact RingHom.Finite.id R
  · exact RingHom.Flat.id ↑R

set_option backward.defeqAttrib.useBackward true in
/-- A finite flat locally finitely presented morphism is an isomorphism if and only if
its rank is constant equal to `1`. -/
nonrec lemma Scheme.Hom.isIso_iff_finrank_eq : IsIso f ↔ finrank f = 1 := by
  refine ⟨fun h ↦ finrank_eq_one_of_isIso f, fun h ↦ ?_⟩
  wlog hY : ∃ R, Y = Spec R
  · rw [← MorphismProperty.isomorphisms.iff,
      IsZariskiLocalAtTarget.iff_of_openCover (P := .isomorphisms Scheme) Y.affineCover]
    intro i
    dsimp [Scheme.Cover.pullbackHom]
    refine this _ ?_ ⟨_, rfl⟩
    ext y
    rw [finrank_pullback_snd, h, Pi.one_apply, Pi.one_apply]
  obtain ⟨R, rfl⟩ := hY
  wlog hX : ∃ S, X = Spec S
  · have _ : IsAffine X := isAffine_of_isAffineHom f
    rw [← isIso_comp_left_iff X.isoSpec.inv]
    refine this _ _ ?_ ⟨_, rfl⟩
    rw [finrank_comp_left_of_isIso, h]
  obtain ⟨S, rfl⟩ := hX
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  simp only [IsFinite.SpecMap_iff, Flat.SpecMap_iff] at *
  algebraize [φ.hom]
  have : IsIso φ := by
    rw [ConcreteCategory.isIso_iff_bijective]
    apply Module.algebraMap_bijective_of_rankAtStalk
    rwa [finrank_SpecMap_eq_finrank ‹_› ‹_›] at h
  infer_instance

end

end AlgebraicGeometry

