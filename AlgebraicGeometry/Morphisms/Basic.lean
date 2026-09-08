/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.MorphismProperty.Local
public import Mathlib.Data.List.TFAE

/-!
# Properties of morphisms between Schemes

We provide the basic framework for talking about properties of morphisms between Schemes.

A `MorphismProperty Scheme` is a predicate on morphisms between schemes. For properties local at
the target, its behaviour is entirely determined by its definition on morphisms into affine schemes,
which we call an `AffineTargetMorphismProperty`. In this file, we provide API lemmas for properties
local at the target, and special support for those properties whose `AffineTargetMorphismProperty`
takes on a simpler form. We also provide API lemmas for properties local at the source.
The main interfaces of the API are the typeclasses `IsZariskiLocalAtTarget`,
`IsZariskiLocalAtSource` and `HasAffineProperty`, which we describe in detail below.

## `IsZariskiLocalAtTarget`

- `AlgebraicGeometry.IsZariskiLocalAtTarget`: We say that `IsZariskiLocalAtTarget P` for
  `P : MorphismProperty Scheme` if
  1. `P` respects isomorphisms.
  2. `P` holds for `f ∣_ U` for an open cover `U` of `Y` if and only if `P` holds for `f`.

For a morphism property `P` local at the target and `f : X ⟶ Y`, we provide these API lemmas:

- `AlgebraicGeometry.IsZariskiLocalAtTarget.of_isPullback`:
    `P` is preserved under pullback along open immersions.
- `AlgebraicGeometry.IsZariskiLocalAtTarget.restrict`:
    `P f → P (f ∣_ U)` for an open `U` of `Y`.
- `AlgebraicGeometry.IsZariskiLocalAtTarget.iff_of_iSup_eq_top`:
    `P f ↔ ∀ i, P (f ∣_ U i)` for a family `U` of open sets covering `Y`.
- `AlgebraicGeometry.IsZariskiLocalAtTarget.iff_of_openCover`:
    `P f ↔ ∀ i, P (𝒰.pullbackHom f i)` for `𝒰 : Y.OpenCover`.

## `IsZariskiLocalAtSource`

- `AlgebraicGeometry.IsZariskiLocalAtSource`: We say that `IsZariskiLocalAtSource P` for
  `P : MorphismProperty Scheme` if
  1. `P` respects isomorphisms.
  2. `P` holds for `𝒰.f i ≫ f` for an open cover `𝒰` of `X` iff `P` holds for `f : X ⟶ Y`.

For a morphism property `P` local at the source and `f : X ⟶ Y`, we provide these API lemmas:

- `AlgebraicGeometry.IsZariskiLocalAtSource.comp`:
    `P` is preserved under composition with open immersions at the source.
- `AlgebraicGeometry.IsZariskiLocalAtSource.iff_of_iSup_eq_top`:
    `P f ↔ ∀ i, P ((U i).ι ≫ f)` for a family `U` of open sets covering `X`.
- `AlgebraicGeometry.IsZariskiLocalAtSource.iff_of_openCover`:
    `P f ↔ ∀ i, P (𝒰.f i ≫ f)` for `𝒰 : X.OpenCover`.
- `AlgebraicGeometry.IsZariskiLocalAtSource.of_isOpenImmersion`: If `P` contains identities then `P`
    holds for open immersions.

## `AffineTargetMorphismProperty`

- `AlgebraicGeometry.AffineTargetMorphismProperty`:
    The type of predicates on `f : X ⟶ Y` with `Y` affine.
- `AlgebraicGeometry.AffineTargetMorphismProperty.IsLocal`: We say that `P.IsLocal` if `P`
    satisfies the assumptions of the affine communication lemma
    (`AlgebraicGeometry.of_affine_open_cover`). That is,
    1. `P` respects isomorphisms.
    2. If `P` holds for `f : X ⟶ Y`, then `P` holds for `f ∣_ Y.basicOpen r` for any
      global section `r`.
    3. If `P` holds for `f ∣_ Y.basicOpen r` for all `r` in a spanning set of the global sections,
      then `P` holds for `f`.

## `HasAffineProperty`

- `AlgebraicGeometry.HasAffineProperty`:
  `HasAffineProperty P Q` is a type class asserting that `P` is local at the target,
  and over affine schemes, it is equivalent to `Q : AffineTargetMorphismProperty`.

For `HasAffineProperty P Q` and `f : X ⟶ Y`, we provide these API lemmas:

- `AlgebraicGeometry.HasAffineProperty.of_isPullback`:
    `P` is preserved under pullback along open immersions from affine schemes.
- `AlgebraicGeometry.HasAffineProperty.restrict`:
    `P f → Q (f ∣_ U)` for affine `U` of `Y`.
- `AlgebraicGeometry.HasAffineProperty.iff_of_iSup_eq_top`:
    `P f ↔ ∀ i, Q (f ∣_ U i)` for a family `U` of affine open sets covering `Y`.
- `AlgebraicGeometry.HasAffineProperty.iff_of_openCover`:
    `P f ↔ ∀ i, Q (𝒰.pullbackHom f i)` for affine open covers `𝒰` of `Y`.
- `AlgebraicGeometry.HasAffineProperty.isStableUnderBaseChange`:
    If `Q` is stable under affine base change, then `P` is stable under arbitrary base change.

## Implementation details

The properties `IsZariskiLocalAtTarget` and `IsZariskiLocalAtSource` are defined as abbreviations
for the respective local property of morphism properties defined generally for categories equipped
with a `Precoverage`.
-/

@[expose] public section


universe u v

open TopologicalSpace CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

namespace AlgebraicGeometry

/-- A property is Zariski-local at target if it is local at target in the Zariski topology. -/
/-
**AlgebraicGeometry.IsZariskiLocalAtTarget** 是 Mathlib 中的一个缩写定义，位于命名空间 `Algebrai
cGeometry`。
形式化陈述：IsZariskiLocalAtTarget (P : MorphismProperty Scheme.{u})
参数：P : MorphismProperty Scheme.{u}。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A property is Zariski-local at target if it is local at target in the Zariski to
pology.
-/
abbrev IsZariskiLocalAtTarget (P : MorphismProperty Scheme.{u}) :=
  P.IsLocalAtTarget Scheme.zariskiPrecoverage

namespace IsZariskiLocalAtTarget

/--
`P` is local at the target if
1. `P` respects isomorphisms.
2. If `P` holds for `f : X ⟶ Y`, then `P` holds for `f ∣_ U` for any `U`.
3. If `P` holds for `f ∣_ U` for an open cover `U` of `Y`, then `P` holds for `f`.
-/
/-
**AlgebraicGeometry.IsZariskiLocalAtTarget.mk'** 是 Mathlib 中的一个定理，位于命名空间 `Algebr
aicGeometry.IsZariskiLocalAtTarget`。
形式化陈述：∀ {P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme} [P.Respec
tsIso],   (∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) (U : Y.Opens), P f → P
 (f ∣_ U)) →     (∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) {ι : Type u} (U
 : ι → Y.Opens),         iSup U = ⊤ → (∀ (i : ι), P (f ∣_ U i)) → P f) →       A
lgebraicGeometry.IsZariskiLocalAtTarget P
参数：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) (U : Y.Opens), P f → P (f ∣_ U
)；∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) {ι : Type u} (U : ι → Y.Opens),
         iSup U = ⊤ → (∀ (i : ι), P (f ∣_ U i)) → P f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.IsLocalAtTarget.mk_of_iff_of_zeroHyperco
ver`：mk_of_iff_of_zeroHypercover [K.HasPullbacks] [P.RespectsIso] (H : forall {X
 Y : C} (f : X ⟶ Y) (𝒰 : Precoverage.ZeroHypercover.{max u v} K Y…
· 使用定理 `AlgebraicGeometry.Scheme.instHasPullbacksPrecoverageOfHasPullbacks`：∀ (P
 : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme) [P.HasPullbacks],  
 (AlgebraicGeometry.Scheme.precoverage P).HasPullbacks
· 使用定理 `AlgebraicGeometry.Scheme.instHasPullbacksIsOpenImmersion`：AlgebraicGeome
try.IsOpenImmersion.HasPullbacks
· 使用定理 `CategoryTheory.Precoverage.ZeroHypercover.instHasPullbackFOfHasPullbacks
Presieve₀_1`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} 
(E : CategoryTheory.PreZeroHypercover X) (f : Y ⟶ X)   [E.presieve₀.HasPu…
· 使用定理 `CategoryTheory.Precoverage.ZeroHypercover.instHasPullbacksPresieve₀OfHas
Pullbacks`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (K : Categor
yTheory.Precoverage C) [K.HasPullbacks] {X Y : C}   (E : K.ZeroHypercov…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AlgebraicGeometry.Scheme.instIsOpenImmersionF`：∀ {X : AlgebraicGeometry.
Scheme} (𝒰 : X.OpenCover) (i : 𝒰.I₀), AlgebraicGeometry.IsOpenImmersion (𝒰.f i)
· 使用定理 `CategoryTheory.MorphismProperty.arrow_mk_iso_iff`：arrow_mk_iso_iff (P : 
MorphismProperty C) [RespectsIso P] {W X Y Z : C} {f : W ⟶ X} {g : Y ⟶ Z} (e : A
rrow.mk f ≅ Arrow.mk g) : P f ↔ P g
· 使用定理 `AlgebraicGeometry.Scheme.OpenCover.iSup_opensRange`：∀ {X : AlgebraicGeom
etry.Scheme} (𝒰 : X.OpenCover), ⨆ i, AlgebraicGeometry.Scheme.Hom.opensRange (𝒰.
f i) = ⊤
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `AlgebraicGeometry.Scheme.instJointlySurjectivePrecoverage`：∀ {P : Catego
ryTheory.MorphismProperty AlgebraicGeometry.Scheme},   AlgebraicGeometry.Scheme.
JointlySurjective (AlgebraicGeometry.Scheme.pre…

--- 原说明 ---
`P` is local at the target if
1. `P` respects isomorphisms.
2. If `P` holds for `f : X ⟶ Y`, then `P` holds for `f ∣_ U` for any `U`.
3. If `P` holds for `f ∣_ U` for an open cover `U` of `Y`, then `P` holds for `f
`.
-/
protected lemma mk' {P : MorphismProperty Scheme} [P.RespectsIso]
    (restrict : ∀ {X Y : Scheme} (f : X ⟶ Y) (U : Y.Opens), P f → P (f ∣_ U))
    (of_sSup_eq_top :
      ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) {ι : Type u} (U : ι → Y.Opens), iSup U = ⊤ →
        (∀ i, P (f ∣_ U i)) → P f) :
    IsZariskiLocalAtTarget P := by
  refine .mk_of_iff_of_zeroHypercover fun {X Y} f 𝒰 ↦ ?_
  refine ⟨fun hf i ↦ (P.arrow_mk_iso_iff (morphismRestrictOpensRange _ _)).mp (restrict _ _ hf),
    fun h ↦ ?_⟩
  refine of_sSup_eq_top f _ (Scheme.OpenCover.iSup_opensRange <| .ulift 𝒰) ?_
  exact fun i ↦ (P.arrow_mk_iso_iff (morphismRestrictOpensRange f _)).mpr (h _)

variable {P : MorphismProperty Scheme.{u}} [IsZariskiLocalAtTarget P]
  {X Y : Scheme.{u}} {f : X ⟶ Y} (𝒰 : Y.OpenCover)
/-
**AlgebraicGeometry.IsZariskiLocalAtTarget.of_isPullback** 是 Mathlib 中的一个引理，位于命名
空间 `AlgebraicGeometry.IsZariskiLocalAtTarget`。
形式化陈述：of_isPullback {UX UY : Scheme.{u}} {iY : UY ⟶ Y} [IsOpenImmersion iY] {iX 
: UX ⟶ X} {f' : UX ⟶ UY} (h : IsPullback iX f' f iY) (H : P f) : P f'
参数：h : IsPullback iX f' f iY；H : P f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.IsLocalAtTarget.of_isPullback`：of_isPull
back {X' : C} (i : 𝒰.I₀) {fst : X' ⟶ X} {snd : X' ⟶ 𝒰.X i} (h : IsPullback fst s
nd f (𝒰.f i)) (hf : P f) : P snd
-/
lemma of_isPullback {UX UY : Scheme.{u}} {iY : UY ⟶ Y} [IsOpenImmersion iY]
    {iX : UX ⟶ X} {f' : UX ⟶ UY} (h : IsPullback iX f' f iY) (H : P f) : P f' :=
  MorphismProperty.IsLocalAtTarget.of_isPullback (Y.affineCover.add iY) .none h H
/-
**AlgebraicGeometry.IsZariskiLocalAtTarget.restrict** 是 Mathlib 中的一个定理，位于命名空间 `A
lgebraicGeometry.IsZariskiLocalAtTarget`。
形式化陈述：restrict (hf : P f) (U : Y.Opens) : P (f ∣_ U)
参数：hf : P f；U : Y.Opens。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.IsZariskiLocalAtTarget.of_isPullback`：of_isPullback {U
X UY : Scheme.{u}} {iY : UY ⟶ Y} [IsOpenImmersion iY] {iX : UX ⟶ X} {f' : UX ⟶ U
Y} (h : IsPullback iX f' f iY) (H : P f) : P…
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι`：∀ {X : AlgebraicGeo
metry.Scheme} (U : X.Opens), AlgebraicGeometry.IsOpenImmersion U.ι
· 使用定理 `CategoryTheory.IsPullback.flip`：flip (h : IsPullback fst snd f g) : IsPu
llback snd fst g f
· 使用定理 `AlgebraicGeometry.isPullback_morphismRestrict`：isPullback_morphismRestri
ct {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) : IsPullback (f ∣_ U) (f ⁻¹ᵁ U).
ι U.ι f
-/
theorem restrict (hf : P f) (U : Y.Opens) : P (f ∣_ U) :=
  of_isPullback (isPullback_morphismRestrict f U).flip hf

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.IsZariskiLocalAtTarget.of_iSup_eq_top** 是 Mathlib 中的一个引理，位于命
名空间 `AlgebraicGeometry.IsZariskiLocalAtTarget`。
形式化陈述：of_iSup_eq_top {ι} (U : ι -> Y.Opens) (hU : iSup U = ⊤) (H : forall i, P (
f ∣_ U i)) : P f
参数：U : ι -> Y.Opens；hU : iSup U = ⊤；H : forall i, P (f ∣_ U i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `TopologicalSpace.Opens.ext`：ext {U V : Opens α} (h : (U : Set α) = V) : 
U = V
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `isOpen_iUnion`：isOpen_iUnion {f : ι -> Set X} (h : forall i, IsOpen (f i
)) : IsOpen (⋃ i, f i)
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用定理 `Set.iUnion_coe_set`：iUnion_coe_set {α β : Type*} (s : Set α) (f : s -> S
et β) : ⋃ i, f i = ⋃ i in s, f ⟨i, ‹i in s›⟩
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iUnion_exists`：iUnion_exists {p : ι -> Prop} {f : Exists p -> Set α}
 : ⋃ x, f x = ⋃ (i) (h : p i), f ⟨i, h⟩
· 使用定理 `Set.iUnion_iUnion_eq'`：iUnion_iUnion_eq' {f : ι -> α} {g : α -> Set β} :
 ⋃ (x) (y) (_ : f y = x), g x = ⋃ y, g (f y)
· 使用定理 `TopologicalSpace.Opens.iSup_mk`：iSup_mk {ι} (s : ι -> Set α) (h : forall
 i, IsOpen (s i)) : (⨆ i, ⟨s i, h i⟩ : Opens α) = ⟨⋃ i, s i, isOpen_iUnion h⟩
· 使用定理 `TopologicalSpace.Opens.mk.congr_simp`：∀ {α : Type u_2} [inst : Topologic
alSpace α] (carrier carrier_1 : Set α) (e_carrier : carrier = carrier_1)   (is_o
pen' : IsOpen carrier), { …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `TopologicalSpace.Opens.coe_iSup`：coe_iSup {ι} (s : ι -> Opens α) : ((⨆ i
, s i : Opens α) : Set α) = ⋃ i, s i
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `CategoryTheory.Precoverage.ZeroHypercover.instHasPullbackFOfHasPullbacks
Presieve₀_1`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} 
(E : CategoryTheory.PreZeroHypercover X) (f : Y ⟶ X)   [E.presieve₀.HasPu…
· 使用定理 `CategoryTheory.Precoverage.ZeroHypercover.instHasPullbacksPresieve₀OfHas
Pullbacks`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (K : Categor
yTheory.Precoverage C) [K.HasPullbacks] {X Y : C}   (E : K.ZeroHypercov…
· 使用定理 `AlgebraicGeometry.Scheme.instHasPullbacksPrecoverageOfHasPullbacks`：∀ (P
 : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme) [P.HasPullbacks],  
 (AlgebraicGeometry.Scheme.precoverage P).HasPullbacks
· 使用定理 `AlgebraicGeometry.Scheme.instHasPullbacksIsOpenImmersion`：AlgebraicGeome
try.IsOpenImmersion.HasPullbacks
· 使用定理 `CategoryTheory.MorphismProperty.iff_of_zeroHypercover_target`：∀ {C : Typ
e u} [inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.MorphismPrope
rty C}   {K : CategoryTheory.Precoverage C} [P.IsL…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AlgebraicGeometry.Scheme.instIsOpenImmersionF`：∀ {X : AlgebraicGeometry.
Scheme} (𝒰 : X.OpenCover) (i : 𝒰.I₀), AlgebraicGeometry.IsOpenImmersion (𝒰.f i)
· 使用定理 `CategoryTheory.MorphismProperty.arrow_mk_iso_iff`：arrow_mk_iso_iff (P : 
MorphismProperty C) [RespectsIso P] {W X Y Z : C} {f : W ⟶ X} {g : Y ⟶ Z} (e : A
rrow.mk f ≅ Arrow.mk g) : P f ↔ P g
· 使用定理 `CategoryTheory.MorphismProperty.IsLocalAtTarget.toRespects`：∀ {C : Type 
u} {inst : CategoryTheory.Category.{v, u} C} {P : CategoryTheory.MorphismPropert
y C}   (K : CategoryTheory.Precoverage C) [self …
（共 32 条，此处仅展示前 30 条）
-/
lemma of_iSup_eq_top {ι} (U : ι → Y.Opens) (hU : iSup U = ⊤)
    (H : ∀ i, P (f ∣_ U i)) : P f := by
  refine (P.iff_of_zeroHypercover_target
    (Y.openCoverOfIsOpenCover (s := Set.range U) Subtype.val (by ext; simp [← hU]))).mpr fun i ↦ ?_
  obtain ⟨_, i, rfl⟩ := i
  refine (P.arrow_mk_iso_iff (morphismRestrictOpensRange f _)).mp ?_
  change P (f ∣_ (U i).ι.opensRange)
  rw [Scheme.Opens.opensRange_ι]
  exact H i
/-
**AlgebraicGeometry.IsZariskiLocalAtTarget.iff_of_iSup_eq_top** 是 Mathlib 中的一个定理
，位于命名空间 `AlgebraicGeometry.IsZariskiLocalAtTarget`。
形式化陈述：iff_of_iSup_eq_top {ι} (U : ι -> Y.Opens) (hU : iSup U = ⊤) : P f ↔ forall
 i, P (f ∣_ U i)
参数：U : ι -> Y.Opens；hU : iSup U = ⊤。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.IsZariskiLocalAtTarget.restrict`：restrict (hf : P f) (
U : Y.Opens) : P (f ∣_ U)
· 使用引理 `AlgebraicGeometry.IsZariskiLocalAtTarget.of_iSup_eq_top`：of_iSup_eq_top 
{ι} (U : ι -> Y.Opens) (hU : iSup U = ⊤) (H : forall i, P (f ∣_ U i)) : P f
-/
theorem iff_of_iSup_eq_top {ι} (U : ι → Y.Opens) (hU : iSup U = ⊤) :
    P f ↔ ∀ i, P (f ∣_ U i) :=
  ⟨fun H _ ↦ restrict H _, of_iSup_eq_top U hU⟩
/-
**AlgebraicGeometry.IsZariskiLocalAtTarget.of_openCover** 是 Mathlib 中的一个引理，位于命名空
间 `AlgebraicGeometry.IsZariskiLocalAtTarget`。
形式化陈述：of_openCover (H : forall i, P (𝒰.pullbackHom f i)) : P f
参数：H : forall i, P (𝒰.pullbackHom f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.instIsStableUnderBaseChangePrecoverageOfIsJoint
lySurjectivePreservingOfIsStableUnderBaseChange`：∀ (P : CategoryTheory.MorphismP
roperty AlgebraicGeometry.Scheme)   [AlgebraicGeometry.Scheme.IsJointlySurjectiv
ePreserving P] [P.IsStableUnd…
· 使用定理 `AlgebraicGeometry.Scheme.instIsJointlySurjectivePreservingIsOpenImmersio
n`：AlgebraicGeometry.Scheme.IsJointlySurjectivePreserving AlgebraicGeometry.IsOp
enImmersion
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用引理 `AlgebraicGeometry.IsZariskiLocalAtTarget.of_iSup_eq_top`：of_iSup_eq_top 
{ι} (U : ι -> Y.Opens) (hU : iSup U = ⊤) (H : forall i, P (f ∣_ U i)) : P f
· 使用定理 `AlgebraicGeometry.Scheme.instIsOpenImmersionF`：∀ {X : AlgebraicGeometry.
Scheme} (𝒰 : X.OpenCover) (i : 𝒰.I₀), AlgebraicGeometry.IsOpenImmersion (𝒰.f i)
· 使用定理 `AlgebraicGeometry.Scheme.OpenCover.iSup_opensRange`：∀ {X : AlgebraicGeom
etry.Scheme} (𝒰 : X.OpenCover), ⨆ i, AlgebraicGeometry.Scheme.Hom.opensRange (𝒰.
f i) = ⊤
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.MorphismProperty.arrow_mk_iso_iff`：arrow_mk_iso_iff (P : 
MorphismProperty C) [RespectsIso P] {W X Y Z : C} {f : W ⟶ X} {g : Y ⟶ Z} (e : A
rrow.mk f ≅ Arrow.mk g) : P f ↔ P g
· 使用定理 `CategoryTheory.MorphismProperty.IsLocalAtTarget.toRespects`：∀ {C : Type 
u} {inst : CategoryTheory.Category.{v, u} C} {P : CategoryTheory.MorphismPropert
y C}   (K : CategoryTheory.Precoverage C) [self …
-/
lemma of_openCover (H : ∀ i, P (𝒰.pullbackHom f i)) : P f := by
  apply of_iSup_eq_top (fun i ↦ (𝒰.f i).opensRange) 𝒰.iSup_opensRange
  exact fun i ↦ (P.arrow_mk_iso_iff (morphismRestrictOpensRange f _)).mpr (H i)
/-
**AlgebraicGeometry.IsZariskiLocalAtTarget.iff_of_openCover** 是 Mathlib 中的一个定理，位
于命名空间 `AlgebraicGeometry.IsZariskiLocalAtTarget`。
形式化陈述：iff_of_openCover (𝒰 : Y.OpenCover) : P f ↔ forall i, P (𝒰.pullbackHom f i)
参数：𝒰 : Y.OpenCover。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.instIsStableUnderBaseChangePrecoverageOfIsJoint
lySurjectivePreservingOfIsStableUnderBaseChange`：∀ (P : CategoryTheory.MorphismP
roperty AlgebraicGeometry.Scheme)   [AlgebraicGeometry.Scheme.IsJointlySurjectiv
ePreserving P] [P.IsStableUnd…
· 使用定理 `AlgebraicGeometry.Scheme.instIsJointlySurjectivePreservingIsOpenImmersio
n`：AlgebraicGeometry.Scheme.IsJointlySurjectivePreserving AlgebraicGeometry.IsOp
enImmersion
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用引理 `AlgebraicGeometry.IsZariskiLocalAtTarget.of_isPullback`：of_isPullback {U
X UY : Scheme.{u}} {iY : UY ⟶ Y} [IsOpenImmersion iY] {iX : UX ⟶ X} {f' : UX ⟶ U
Y} (h : IsPullback iX f' f iY) (H : P f) : P…
· 使用定理 `AlgebraicGeometry.Scheme.instIsOpenImmersionF`：∀ {X : AlgebraicGeometry.
Scheme} (𝒰 : X.OpenCover) (i : 𝒰.I₀), AlgebraicGeometry.IsOpenImmersion (𝒰.f i)
· 使用定理 `CategoryTheory.IsPullback.of_hasPullback`：of_hasPullback (f : X ⟶ Z) (g 
: Y ⟶ Z) [HasPullback f g] : IsPullback (pullback.fst f g) (pullback.snd f g) f 
g
· 使用引理 `AlgebraicGeometry.IsZariskiLocalAtTarget.of_openCover`：of_openCover (H :
 forall i, P (𝒰.pullbackHom f i)) : P f
-/
theorem iff_of_openCover (𝒰 : Y.OpenCover) :
    P f ↔ ∀ i, P (𝒰.pullbackHom f i) :=
  ⟨fun H _ ↦ of_isPullback (.of_hasPullback _ _) H, of_openCover _⟩

set_option backward.defeqAttrib.useBackward true in
/-
**AlgebraicGeometry.IsZariskiLocalAtTarget.of_range_subset_iSup** 是 Mathlib 中的一个
引理，位于命名空间 `AlgebraicGeometry.IsZariskiLocalAtTarget`。
形式化陈述：of_range_subset_iSup [P.RespectsRight @IsOpenImmersion] {ι : Type*} (U : ι
 -> Y.Opens) (H : Set.range f subseteq (⨆ i, U i : Y.Opens)) (hf : forall i, P (
f ∣_ U i)) : P f
参数：U : ι -> Y.Opens；H : Set.range f subseteq (⨆ i, U i : Y.Opens)；hf : forall i,
 P (f ∣_ U i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι`：∀ {X : AlgebraicGeo
metry.Scheme} (U : X.Opens), AlgebraicGeometry.IsOpenImmersion U.ι
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `AlgebraicGeometry.Scheme.Opens.range_ι`：range_ι : Set.range U.ι = U
· 使用定理 `TopologicalSpace.Opens.coe_iSup`：coe_iSup {ι} (s : ι -> Opens α) : ((⨆ i
, s i : Opens α) : Set α) = ⋃ i, s i
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.lift_fac`：lift_fac (H' : Set.range g s
ubseteq Set.range f) : lift f g H' ≫ f = g
· 使用定理 `CategoryTheory.MorphismProperty.RespectsRight.postcomp`：∀ {C : Type u} {
inst : CategoryTheory.CategoryStruct.{v, u} C} {P Q : CategoryTheory.MorphismPro
perty C}   [self : P.RespectsRight Q] {X Y Z…
· 使用定理 `AlgebraicGeometry.IsZariskiLocalAtTarget.iff_of_iSup_eq_top`：iff_of_iSup
_eq_top {ι} (U : ι -> Y.Opens) (hU : iSup U = ⊤) : P f ↔ forall i, P (f ∣_ U i)
· 使用引理 `AlgebraicGeometry.Scheme.Hom.image_injective`：image_injective : Function
.Injective (f ''ᵁ ·)
· 使用引理 `AlgebraicGeometry.Scheme.Hom.image_iSup`：image_iSup {ι : Sort*} (s : ι -
> X.Opens) : (f ''ᵁ ⨆ (i : ι), s i) = ⨆ (i : ι), f ''ᵁ s i
· 使用引理 `AlgebraicGeometry.Scheme.Hom.image_top_eq_opensRange`：image_top_eq_opens
Range : f ''ᵁ ⊤ = f.opensRange
· 使用引理 `AlgebraicGeometry.Scheme.Opens.opensRange_ι`：opensRange_ι : U.ι.opensRan
ge = U
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `AlgebraicGeometry.Scheme.Hom.image_preimage_eq_opensRange_inf`：image_pre
image_eq_opensRange_inf (U : Y.Opens) : f ''ᵁ f ⁻¹ᵁ U = f.opensRange ⊓ U
· 使用定理 `inf_of_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, b ≤
 a → a ⊓ b = b
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `AlgebraicGeometry.morphismRestrict_ι`：morphismRestrict_ι {X Y : Scheme.{
u}} (f : X ⟶ Y) (U : Y.Opens) : f ∣_ U ≫ U.ι = (f ⁻¹ᵁ U).ι ≫ f
· 使用定理 `AlgebraicGeometry.Scheme.isoOfEq_hom_ι_assoc`：∀ (X : AlgebraicGeometry.S
cheme) {U V : X.Opens} (e : U = V) {Z : AlgebraicGeometry.Scheme} (h : X ⟶ Z),  
 CategoryTheory.CategoryStruct.com…
· 使用定理 `AlgebraicGeometry.Scheme.Opens.isoOfLE_hom_ι`：∀ {X : AlgebraicGeometry.S
cheme} {U V : X.Opens} (hUV : U ≤ V),   CategoryTheory.CategoryStruct.comp (Alge
braicGeometry.Scheme.Opens.isoOfLE…
· 使用定理 `AlgebraicGeometry.morphismRestrict_ι_assoc`：∀ {X Y : AlgebraicGeometry.S
cheme} (f : X ⟶ Y) (U : Y.Opens) {Z : AlgebraicGeometry.Scheme} (h : Y ⟶ Z),   C
ategoryTheory.CategoryStruct.com…
· 使用定理 `CategoryTheory.MorphismProperty.arrow_mk_iso_iff`：arrow_mk_iso_iff (P : 
MorphismProperty C) [RespectsIso P] {W X Y Z : C} {f : W ⟶ X} {g : Y ⟶ Z} (e : A
rrow.mk f ≅ Arrow.mk g) : P f ↔ P g
· 使用定理 `CategoryTheory.MorphismProperty.IsLocalAtTarget.toRespects`：∀ {C : Type 
u} {inst : CategoryTheory.Category.{v, u} C} {P : CategoryTheory.MorphismPropert
y C}   (K : CategoryTheory.Precoverage C) [self …
-/
lemma of_range_subset_iSup [P.RespectsRight @IsOpenImmersion] {ι : Type*} (U : ι → Y.Opens)
    (H : Set.range f ⊆ (⨆ i, U i : Y.Opens)) (hf : ∀ i, P (f ∣_ U i)) : P f := by
  let g : X ⟶ (⨆ i, U i : Y.Opens) := IsOpenImmersion.lift (Scheme.Opens.ι _) f (by simpa using H)
  rw [← IsOpenImmersion.lift_fac (⨆ i, U i).ι f (by simpa using H)]
  apply MorphismProperty.RespectsRight.postcomp (Q := @IsOpenImmersion) _ inferInstance
  rw [iff_of_iSup_eq_top (P := P) (U := fun i : ι ↦ (⨆ i, U i).ι ⁻¹ᵁ U i)]
  · intro i
    have heq : g ⁻¹ᵁ (⨆ i, U i).ι ⁻¹ᵁ U i = f ⁻¹ᵁ U i := by
      change (g ≫ (⨆ i, U i).ι) ⁻¹ᵁ U i = _
      simp [g]
    let e : Arrow.mk (g ∣_ (⨆ i, U i).ι ⁻¹ᵁ U i) ≅ Arrow.mk (f ∣_ U i) :=
        Arrow.isoMk (X.isoOfEq heq) (Scheme.Opens.isoOfLE (le_iSup U i)) <| by
      simp [← CategoryTheory.cancel_mono (U i).ι, g]
    rw [P.arrow_mk_iso_iff e]
    exact hf i
  apply (⨆ i, U i).ι.image_injective
  dsimp
  rw [Scheme.Hom.image_iSup, Scheme.Hom.image_top_eq_opensRange, Scheme.Opens.opensRange_ι]
  simp [Scheme.Hom.image_preimage_eq_opensRange_inf, le_iSup U]
/-
**AlgebraicGeometry.IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict** 是
 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry.IsZariskiLocalAtTarget`。
形式化陈述：of_forall_exists_morphismRestrict (H : forall x, exists U : Y.Opens, x in 
U ∧ P (f ∣_ U)) : P f
参数：H : forall x, exists U : Y.Opens, x in U ∧ P (f ∣_ U)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.IsZariskiLocalAtTarget.of_iSup_eq_top`：of_iSup_eq_top 
{ι} (U : ι -> Y.Opens) (hU : iSup U = ⊤) (H : forall i, P (f ∣_ U i)) : P f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `top_le_iff`：top_le_iff : ⊤ <= a ↔ a = ⊤
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
lemma of_forall_exists_morphismRestrict (H : ∀ x, ∃ U : Y.Opens, x ∈ U ∧ P (f ∣_ U)) : P f := by
  choose U hxU hU using H
  refine IsZariskiLocalAtTarget.of_iSup_eq_top U (top_le_iff.mp fun x _ ↦ ?_) hU
  simpa using ⟨x, hxU x⟩
/-
**AlgebraicGeometry.IsZariskiLocalAtTarget.of_forall_source_exists_preimage** 是 
Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry.IsZariskiLocalAtTarget`。
形式化陈述：of_forall_source_exists_preimage [P.RespectsRight IsOpenImmersion] [P.HasO
fPostcompProperty IsOpenImmersion] (f : X ⟶ Y) (hX : forall x, exists (U : Y.Ope
ns), f x in U ∧ P ((f ⁻¹ᵁ U).ι ≫ f)) : P f
参数：f : X ⟶ Y；hX : forall x, exists (U : Y.Opens), f x in U ∧ P ((f ⁻¹ᵁ U).ι ≫ f)
。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.IsZariskiLocalAtTarget.of_range_subset_iSup`：of_range_
subset_iSup [P.RespectsRight @IsOpenImmersion] {ι : Type*} (U : ι -> Y.Opens) (H
 : Set.range f subseteq (⨆ i, U i : Y.Opens)) (hf :…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TopologicalSpace.Opens.coe_iSup`：coe_iSup {ι} (s : ι -> Opens α) : ((⨆ i
, s i : Opens α) : Set α) = ⋃ i, s i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `CategoryTheory.MorphismProperty.of_postcomp`：of_postcomp [W.HasOfPostcom
pProperty W'] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hg : W' g) (hfg : W (f ≫ g)) 
: W f
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι`：∀ {X : AlgebraicGeo
metry.Scheme} (U : X.Opens), AlgebraicGeometry.IsOpenImmersion U.ι
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AlgebraicGeometry.morphismRestrict_ι`：morphismRestrict_ι {X Y : Scheme.{
u}} (f : X ⟶ Y) (U : Y.Opens) : f ∣_ U ≫ U.ι = (f ⁻¹ᵁ U).ι ≫ f
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
lemma of_forall_source_exists_preimage
    [P.RespectsRight IsOpenImmersion] [P.HasOfPostcompProperty IsOpenImmersion]
    (f : X ⟶ Y) (hX : ∀ x, ∃ (U : Y.Opens), f x ∈ U ∧ P ((f ⁻¹ᵁ U).ι ≫ f)) :
    P f := by
  choose U h₁ h₂ using hX
  apply IsZariskiLocalAtTarget.of_range_subset_iSup U
  · rintro y ⟨x, rfl⟩
    simp only [Opens.coe_iSup, Set.mem_iUnion, SetLike.mem_coe]
    exact ⟨x, h₁ x⟩
  · intro x
    exact P.of_postcomp (f ∣_ U x) (U x).ι (inferInstance : IsOpenImmersion _) (by simp [h₂])

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.IsZariskiLocalAtTarget.coprodMap** 是 Mathlib 中的一个引理，位于命名空间 `
AlgebraicGeometry.IsZariskiLocalAtTarget`。
形式化陈述：coprodMap {X Y X' Y' : Scheme.{u}} (f : X ⟶ X') (g : Y ⟶ Y') (hf : P f) (h
g : P g) : P (coprod.map f g)
参数：f : X ⟶ X'；g : Y ⟶ Y'；hf : P f；hg : P g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.IsZariskiLocalAtTarget.of_openCover`：of_openCover (H :
 forall i, P (𝒰.pullbackHom f i)) : P f
· 使用定理 `AlgebraicGeometry.Scheme.IsLocallyDirected.instHasColimit`：∀ {J : Type w
} [inst : CategoryTheory.Category.{v, w} J] (F : CategoryTheory.Functor J Algebr
aicGeometry.Scheme)   [∀ {i j : J} (f : i ⟶ j),…
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.of_isIso`：∀ {Y Z : AlgebraicGeometry.S
cheme} (g : Y ⟶ Z) [CategoryTheory.IsIso g], AlgebraicGeometry.IsOpenImmersion g
· 使用定理 `CategoryTheory.Discrete.instIsIso`：∀ {I : Type u₁} {i j : CategoryTheory
.Discrete I} (f : i ⟶ j), CategoryTheory.IsIso f
· 使用定理 `CategoryTheory.instIsLocallyDirectedDiscrete`：∀ {J : Type u_1} (F : Cate
goryTheory.Functor (CategoryTheory.Discrete J) (Type u_2)), F.IsLocallyDirected
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `AlgebraicGeometry.Scheme.instIsStableUnderBaseChangePrecoverageOfIsJoint
lySurjectivePreservingOfIsStableUnderBaseChange`：∀ (P : CategoryTheory.MorphismP
roperty AlgebraicGeometry.Scheme)   [AlgebraicGeometry.Scheme.IsJointlySurjectiv
ePreserving P] [P.IsStableUnd…
· 使用定理 `AlgebraicGeometry.Scheme.instIsJointlySurjectivePreservingIsOpenImmersio
n`：AlgebraicGeometry.Scheme.IsJointlySurjectivePreserving AlgebraicGeometry.IsOp
enImmersion
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `CategoryTheory.IsPullback.flip`：flip (h : IsPullback fst snd f g) : IsPu
llback snd fst g f
· 使用引理 `AlgebraicGeometry.isPullback_inl_inl_coprodMap`：isPullback_inl_inl_copro
dMap {X Y X' Y' : Scheme.{u}} (f : X ⟶ X') (g : Y ⟶ Y') : IsPullback f coprod.in
l coprod.inl (coprod.map f g)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.MorphismProperty.cancel_left_of_respectsIso`：cancel_left_
of_respectsIso (P : MorphismProperty C) [hP : RespectsIso P] {X Y Z : C} (f : X 
⟶ Y) (g : Y ⟶ Z) [IsIso f] : P (f ≫ g) ↔ P g
· 使用定理 `CategoryTheory.MorphismProperty.IsLocalAtTarget.toRespects`：∀ {C : Type 
u} {inst : CategoryTheory.Category.{v, u} C} {P : CategoryTheory.MorphismPropert
y C}   (K : CategoryTheory.Precoverage C) [self …
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.IsPullback.isoPullback_hom_snd`：isoPullback_hom_snd (h : 
IsPullback fst snd f g) [HasPullback f g] : h.isoPullback.hom ≫ pullback.snd _ _
 = snd
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `AlgebraicGeometry.isPullback_inr_inr_coprodMap`：isPullback_inr_inr_copro
dMap {X Y X' Y' : Scheme.{u}} (f : X ⟶ X') (g : Y ⟶ Y') : IsPullback g coprod.in
r coprod.inr (coprod.map f g)
-/
lemma coprodMap {X Y X' Y' : Scheme.{u}} (f : X ⟶ X') (g : Y ⟶ Y') (hf : P f) (hg : P g) :
    P (coprod.map f g) := by
  refine IsZariskiLocalAtTarget.of_openCover (coprodOpenCover.{_, 0} _ _) ?_
  rintro (⟨⟨⟩⟩ | ⟨⟨⟩⟩)
  · rw [← MorphismProperty.cancel_left_of_respectsIso P
      (isPullback_inl_inl_coprodMap f g).flip.isoPullback.hom]
    convert! hf
    simp [Scheme.Cover.pullbackHom, coprodOpenCover]
  · rw [← MorphismProperty.cancel_left_of_respectsIso P
      (isPullback_inr_inr_coprodMap f g).flip.isoPullback.hom]
    convert! hg
    simp [Scheme.Cover.pullbackHom, coprodOpenCover]

end IsZariskiLocalAtTarget

/-- A property is Zariski-local at source if it is local at source in the Zariski topology. -/
/-
**AlgebraicGeometry.IsZariskiLocalAtSource** 是 Mathlib 中的一个缩写定义，位于命名空间 `Algebrai
cGeometry`。
形式化陈述：IsZariskiLocalAtSource (P : MorphismProperty Scheme.{u})
参数：P : MorphismProperty Scheme.{u}。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A property is Zariski-local at source if it is local at source in the Zariski to
pology.
-/
abbrev IsZariskiLocalAtSource (P : MorphismProperty Scheme.{u}) :=
  P.IsLocalAtSource Scheme.zariskiPrecoverage

namespace IsZariskiLocalAtSource

set_option backward.defeqAttrib.useBackward true in
/--
`P` is local at the source if
1. `P` respects isomorphisms.
2. If `P` holds for `f : X ⟶ Y`, then `P` holds for `U.ι ≫ f` for any `U`.
3. If `P` holds for `U.ι ≫ f` for an open cover `U` of `X`, then `P` holds for `f`.
-/
/-
**AlgebraicGeometry.IsZariskiLocalAtSource.mk'** 是 Mathlib 中的一个定理，位于命名空间 `Algebr
aicGeometry.IsZariskiLocalAtSource`。
形式化陈述：∀ {P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme} [P.Respec
tsIso],   (∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) (U : X.Opens), P f → P
 (CategoryTheory.CategoryStruct.comp U.ι f)) →     (∀ {X Y : AlgebraicGeometry.S
cheme} (f : X ⟶ Y) {ι : Type u} (U : ι → X.Opens),         iSup U = ⊤ → (∀ (i : 
ι), P (CategoryTheory.CategoryStruct.comp (U i).ι f)) → P f) →       AlgebraicGe
ometry.IsZariskiLocalAtSource P
参数：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) (U : X.Opens), P f → P (Catego
ryTheory.CategoryStruct.comp U.ι f)；∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ 
Y) {ι : Type u} (U : ι → X.Opens),         iSup U = ⊤ → (∀ (i : ι), P (CategoryT
heory.CategoryStruct.comp (U i).ι f)) → P f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.IsLocalAtSource.mk_of_iff_of_zeroHyperco
ver`：mk_of_iff_of_zeroHypercover [P.RespectsIso] (H : forall {X Y : C} (f : X ⟶ 
Y) (𝒰 : Precoverage.ZeroHypercover.{max u v} K X), P f ↔ forall i…
· 使用定理 `AlgebraicGeometry.Scheme.instIsOpenImmersionF`：∀ {X : AlgebraicGeometry.
Scheme} (𝒰 : X.OpenCover) (i : 𝒰.I₀), AlgebraicGeometry.IsOpenImmersion (𝒰.f i)
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι`：∀ {X : AlgebraicGeo
metry.Scheme} (U : X.Opens), AlgebraicGeometry.IsOpenImmersion U.ι
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `AlgebraicGeometry.Scheme.Opens.opensRange_ι`：opensRange_ι : U.ι.opensRan
ge = U
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq_hom_fac`：isoOfRangeEq_hom
_fac {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) [IsOpenImmersion f] [IsOpenImm
ersion g] (e : Set.range f = Set.range g) : …
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.MorphismProperty.cancel_left_of_respectsIso`：cancel_left_
of_respectsIso (P : MorphismProperty C) [hP : RespectsIso P] {X Y Z : C} (f : X 
⟶ Y) (g : Y ⟶ Z) [IsIso f] : P (f ≫ g) ↔ P g
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `AlgebraicGeometry.Scheme.OpenCover.iSup_opensRange`：∀ {X : AlgebraicGeom
etry.Scheme} (𝒰 : X.OpenCover), ⨆ i, AlgebraicGeometry.Scheme.Hom.opensRange (𝒰.
f i) = ⊤
· 使用定理 `AlgebraicGeometry.Scheme.instJointlySurjectivePrecoverage`：∀ {P : Catego
ryTheory.MorphismProperty AlgebraicGeometry.Scheme},   AlgebraicGeometry.Scheme.
JointlySurjective (AlgebraicGeometry.Scheme.pre…
· 使用引理 `AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq_inv_fac`：isoOfRangeEq_inv
_fac {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) [IsOpenImmersion f] [IsOpenImm
ersion g] (e : Set.range f = Set.range g) : …
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv

--- 原说明 ---
`P` is local at the source if
1. `P` respects isomorphisms.
2. If `P` holds for `f : X ⟶ Y`, then `P` holds for `U.ι ≫ f` for any `U`.
3. If `P` holds for `U.ι ≫ f` for an open cover `U` of `X`, then `P` holds for `
f`.
-/
protected lemma mk' {P : MorphismProperty Scheme} [P.RespectsIso]
    (restrict : ∀ {X Y : Scheme} (f : X ⟶ Y) (U : X.Opens), P f → P (U.ι ≫ f))
    (of_sSup_eq_top :
      ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) {ι : Type u} (U : ι → X.Opens), iSup U = ⊤ →
        (∀ i, P ((U i).ι ≫ f)) → P f) :
    IsZariskiLocalAtSource P := by
  refine .mk_of_iff_of_zeroHypercover fun {X Y} f 𝒰 ↦ ⟨fun hf i ↦ ?_, fun hf ↦ ?_⟩
  · rw [← IsOpenImmersion.isoOfRangeEq_hom_fac (𝒰.f i) (Scheme.Opens.ι _)
      (congr_arg Opens.carrier (𝒰.f i).opensRange.opensRange_ι.symm), Category.assoc,
      P.cancel_left_of_respectsIso]
    exact restrict _ _ hf
  · refine of_sSup_eq_top f _ (Scheme.OpenCover.iSup_opensRange <| .ulift 𝒰) fun i ↦ ?_
    dsimp
    rw [← IsOpenImmersion.isoOfRangeEq_inv_fac (𝒰.f _) (Scheme.Opens.ι _)
      (congr_arg Opens.carrier (𝒰.f _).opensRange.opensRange_ι.symm), Category.assoc,
      P.cancel_left_of_respectsIso]
    exact hf _

variable {P : MorphismProperty Scheme.{u}} [IsZariskiLocalAtSource P]
variable {X Y : Scheme.{u}} {f : X ⟶ Y} (𝒰 : X.OpenCover)
/-
**AlgebraicGeometry.IsZariskiLocalAtSource.comp** 是 Mathlib 中的一个引理，位于命名空间 `Algeb
raicGeometry.IsZariskiLocalAtSource`。
形式化陈述：comp {UX : Scheme.{u}} (H : P f) (i : UX ⟶ X) [IsOpenImmersion i] : P (i ≫
 f)
参数：H : P f；i : UX ⟶ X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.MorphismProperty.iff_of_zeroHypercover_source`：∀ {C : Typ
e u} [inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.MorphismPrope
rty C}   {K : CategoryTheory.Precoverage C} [P.IsL…
-/
lemma comp {UX : Scheme.{u}} (H : P f) (i : UX ⟶ X) [IsOpenImmersion i] :
    P (i ≫ f) :=
  (P.iff_of_zeroHypercover_source (X.affineCover.add i)).mp H .none

/-- If `P` is local at the source, then it respects composition on the left with open immersions. -/
/-
**AlgebraicGeometry.IsZariskiLocalAtSource.respectsLeft_isOpenImmersion** 是 Math
lib 中的一个实例，位于命名空间 `AlgebraicGeometry.IsZariskiLocalAtSource`。
形式化陈述：respectsLeft_isOpenImmersion {P : MorphismProperty Scheme} [IsZariskiLocal
AtSource P] : P.RespectsLeft @IsOpenImmersion where precomp i _ _ hf
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.IsZariskiLocalAtSource.comp`：comp {UX : Scheme.{u}} (H
 : P f) (i : UX ⟶ X) [IsOpenImmersion i] : P (i ≫ f)

--- 原说明 ---
If `P` is local at the source, then it respects composition on the left with ope
n immersions.
-/
instance respectsLeft_isOpenImmersion {P : MorphismProperty Scheme}
    [IsZariskiLocalAtSource P] : P.RespectsLeft @IsOpenImmersion where
  precomp i _ _ hf := IsZariskiLocalAtSource.comp hf i
/-
**AlgebraicGeometry.IsZariskiLocalAtSource.of_iSup_eq_top** 是 Mathlib 中的一个引理，位于命
名空间 `AlgebraicGeometry.IsZariskiLocalAtSource`。
形式化陈述：of_iSup_eq_top {ι} (U : ι -> X.Opens) (hU : iSup U = ⊤) (H : forall i, P (
(U i).ι ≫ f)) : P f
参数：U : ι -> X.Opens；hU : iSup U = ⊤；H : forall i, P ((U i).ι ≫ f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `TopologicalSpace.Opens.ext`：ext {U V : Opens α} (h : (U : Set α) = V) : 
U = V
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `isOpen_iUnion`：isOpen_iUnion {f : ι -> Set X} (h : forall i, IsOpen (f i
)) : IsOpen (⋃ i, f i)
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用定理 `Set.iUnion_coe_set`：iUnion_coe_set {α β : Type*} (s : Set α) (f : s -> S
et β) : ⋃ i, f i = ⋃ i in s, f ⟨i, ‹i in s›⟩
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iUnion_exists`：iUnion_exists {p : ι -> Prop} {f : Exists p -> Set α}
 : ⋃ x, f x = ⋃ (i) (h : p i), f ⟨i, h⟩
· 使用定理 `Set.iUnion_iUnion_eq'`：iUnion_iUnion_eq' {f : ι -> α} {g : α -> Set β} :
 ⋃ (x) (y) (_ : f y = x), g x = ⋃ y, g (f y)
· 使用定理 `TopologicalSpace.Opens.iSup_mk`：iSup_mk {ι} (s : ι -> Set α) (h : forall
 i, IsOpen (s i)) : (⨆ i, ⟨s i, h i⟩ : Opens α) = ⟨⋃ i, s i, isOpen_iUnion h⟩
· 使用定理 `TopologicalSpace.Opens.mk.congr_simp`：∀ {α : Type u_2} [inst : Topologic
alSpace α] (carrier carrier_1 : Set α) (e_carrier : carrier = carrier_1)   (is_o
pen' : IsOpen carrier), { …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `TopologicalSpace.Opens.coe_iSup`：coe_iSup {ι} (s : ι -> Opens α) : ((⨆ i
, s i : Opens α) : Set α) = ⋃ i, s i
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `CategoryTheory.MorphismProperty.iff_of_zeroHypercover_source`：∀ {C : Typ
e u} [inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.MorphismPrope
rty C}   {K : CategoryTheory.Precoverage C} [P.IsL…
-/
lemma of_iSup_eq_top {ι} (U : ι → X.Opens) (hU : iSup U = ⊤)
    (H : ∀ i, P ((U i).ι ≫ f)) : P f := by
  refine (P.iff_of_zeroHypercover_source
    (X.openCoverOfIsOpenCover (s := Set.range U) Subtype.val (by ext; simp [← hU]))).mpr fun i ↦ ?_
  obtain ⟨_, i, rfl⟩ := i
  exact H i
/-
**AlgebraicGeometry.IsZariskiLocalAtSource.iff_of_iSup_eq_top** 是 Mathlib 中的一个定理
，位于命名空间 `AlgebraicGeometry.IsZariskiLocalAtSource`。
形式化陈述：iff_of_iSup_eq_top {ι} (U : ι -> X.Opens) (hU : iSup U = ⊤) : P f ↔ forall
 i, P ((U i).ι ≫ f)
参数：U : ι -> X.Opens；hU : iSup U = ⊤。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.IsZariskiLocalAtSource.comp`：comp {UX : Scheme.{u}} (H
 : P f) (i : UX ⟶ X) [IsOpenImmersion i] : P (i ≫ f)
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι`：∀ {X : AlgebraicGeo
metry.Scheme} (U : X.Opens), AlgebraicGeometry.IsOpenImmersion U.ι
· 使用引理 `AlgebraicGeometry.IsZariskiLocalAtSource.of_iSup_eq_top`：of_iSup_eq_top 
{ι} (U : ι -> X.Opens) (hU : iSup U = ⊤) (H : forall i, P ((U i).ι ≫ f)) : P f
-/
theorem iff_of_iSup_eq_top {ι} (U : ι → X.Opens) (hU : iSup U = ⊤) :
    P f ↔ ∀ i, P ((U i).ι ≫ f) :=
  ⟨fun H _ ↦ comp H _, of_iSup_eq_top U hU⟩
/-
**AlgebraicGeometry.IsZariskiLocalAtSource.of_openCover** 是 Mathlib 中的一个引理，位于命名空
间 `AlgebraicGeometry.IsZariskiLocalAtSource`。
形式化陈述：of_openCover (H : forall i, P (𝒰.f i ≫ f)) : P f
参数：H : forall i, P (𝒰.f i ≫ f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.IsZariskiLocalAtSource.of_iSup_eq_top`：of_iSup_eq_top 
{ι} (U : ι -> X.Opens) (hU : iSup U = ⊤) (H : forall i, P ((U i).ι ≫ f)) : P f
· 使用定理 `AlgebraicGeometry.Scheme.instIsOpenImmersionF`：∀ {X : AlgebraicGeometry.
Scheme} (𝒰 : X.OpenCover) (i : 𝒰.I₀), AlgebraicGeometry.IsOpenImmersion (𝒰.f i)
· 使用定理 `AlgebraicGeometry.Scheme.OpenCover.iSup_opensRange`：∀ {X : AlgebraicGeom
etry.Scheme} (𝒰 : X.OpenCover), ⨆ i, AlgebraicGeometry.Scheme.Hom.opensRange (𝒰.
f i) = ⊤
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι`：∀ {X : AlgebraicGeo
metry.Scheme} (U : X.Opens), AlgebraicGeometry.IsOpenImmersion U.ι
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `AlgebraicGeometry.Scheme.Opens.opensRange_ι`：opensRange_ι : U.ι.opensRan
ge = U
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq_inv_fac`：isoOfRangeEq_inv
_fac {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) [IsOpenImmersion f] [IsOpenImm
ersion g] (e : Set.range f = Set.range g) : …
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.MorphismProperty.cancel_left_of_respectsIso`：cancel_left_
of_respectsIso (P : MorphismProperty C) [hP : RespectsIso P] {X Y Z : C} (f : X 
⟶ Y) (g : Y ⟶ Z) [IsIso f] : P (f ≫ g) ↔ P g
· 使用定理 `CategoryTheory.MorphismProperty.IsLocalAtSource.toRespects`：∀ {C : Type 
u} {inst : CategoryTheory.Category.{v, u} C} {P : CategoryTheory.MorphismPropert
y C}   (K : CategoryTheory.Precoverage C) [self …
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
-/
lemma of_openCover (H : ∀ i, P (𝒰.f i ≫ f)) : P f := by
  refine of_iSup_eq_top (fun i ↦ (𝒰.f i).opensRange) 𝒰.iSup_opensRange fun i ↦ ?_
  rw [← IsOpenImmersion.isoOfRangeEq_inv_fac (𝒰.f i) (Scheme.Opens.ι _)
    (congr_arg Opens.carrier (𝒰.f i).opensRange.opensRange_ι.symm), Category.assoc,
    P.cancel_left_of_respectsIso]
  exact H i
/-
**AlgebraicGeometry.IsZariskiLocalAtSource.iff_of_openCover** 是 Mathlib 中的一个定理，位
于命名空间 `AlgebraicGeometry.IsZariskiLocalAtSource`。
形式化陈述：iff_of_openCover : P f ↔ forall i, P (𝒰.f i ≫ f)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.IsZariskiLocalAtSource.comp`：comp {UX : Scheme.{u}} (H
 : P f) (i : UX ⟶ X) [IsOpenImmersion i] : P (i ≫ f)
· 使用定理 `AlgebraicGeometry.Scheme.instIsOpenImmersionF`：∀ {X : AlgebraicGeometry.
Scheme} (𝒰 : X.OpenCover) (i : 𝒰.I₀), AlgebraicGeometry.IsOpenImmersion (𝒰.f i)
· 使用引理 `AlgebraicGeometry.IsZariskiLocalAtSource.of_openCover`：of_openCover (H :
 forall i, P (𝒰.f i ≫ f)) : P f
-/
theorem iff_of_openCover :
    P f ↔ ∀ i, P (𝒰.f i ≫ f) :=
  ⟨fun H _ ↦ comp H _, of_openCover _⟩

variable (f) in
/-
**AlgebraicGeometry.IsZariskiLocalAtSource.of_isOpenImmersion** 是 Mathlib 中的一个引理
，位于命名空间 `AlgebraicGeometry.IsZariskiLocalAtSource`。
形式化陈述：of_isOpenImmersion [P.ContainsIdentities] [IsOpenImmersion f] : P f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.IsZariskiLocalAtSource.comp`：comp {UX : Scheme.{u}} (H
 : P f) (i : UX ⟶ X) [IsOpenImmersion i] : P (i ≫ f)
· 使用引理 `CategoryTheory.MorphismProperty.id_mem`：id_mem (W : MorphismProperty C) 
[W.ContainsIdentities] (X : C) : W (𝟙 X)
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
lemma of_isOpenImmersion [P.ContainsIdentities] [IsOpenImmersion f] : P f :=
  Category.comp_id f ▸ comp (P.id_mem Y) f

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.IsZariskiLocalAtSource.isZariskiLocalAtTarget** 是 Mathlib 中的
一个引理，位于命名空间 `AlgebraicGeometry.IsZariskiLocalAtSource`。
形式化陈述：isZariskiLocalAtTarget [P.IsMultiplicative] (hP : forall {X Y Z : Scheme.{
u}} (f : X ⟶ Y) (g : Y ⟶ Z) [IsOpenImmersion g], P (f ≫ g) -> P f) : IsZariskiLo
calAtTarget P
参数：hP : forall {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [IsOpenImmersion g],
 P (f ≫ g) -> P f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.IsLocalAtTarget.mk_of_iff_of_zeroHyperco
ver`：mk_of_iff_of_zeroHypercover [K.HasPullbacks] [P.RespectsIso] (H : forall {X
 Y : C} (f : X ⟶ Y) (𝒰 : Precoverage.ZeroHypercover.{max u v} K Y…
· 使用定理 `AlgebraicGeometry.Scheme.instHasPullbacksPrecoverageOfHasPullbacks`：∀ (P
 : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme) [P.HasPullbacks],  
 (AlgebraicGeometry.Scheme.precoverage P).HasPullbacks
· 使用定理 `AlgebraicGeometry.Scheme.instHasPullbacksIsOpenImmersion`：AlgebraicGeome
try.IsOpenImmersion.HasPullbacks
· 使用定理 `CategoryTheory.MorphismProperty.IsLocalAtSource.toRespects`：∀ {C : Type 
u} {inst : CategoryTheory.Category.{v, u} C} {P : CategoryTheory.MorphismPropert
y C}   (K : CategoryTheory.Precoverage C) [self …
· 使用定理 `CategoryTheory.Precoverage.ZeroHypercover.instHasPullbackFOfHasPullbacks
Presieve₀_1`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} 
(E : CategoryTheory.PreZeroHypercover X) (f : Y ⟶ X)   [E.presieve₀.HasPu…
· 使用定理 `CategoryTheory.Precoverage.ZeroHypercover.instHasPullbacksPresieve₀OfHas
Pullbacks`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (K : Categor
yTheory.Precoverage C) [K.HasPullbacks] {X Y : C}   (E : K.ZeroHypercov…
· 使用定理 `AlgebraicGeometry.Scheme.instIsOpenImmersionF`：∀ {X : AlgebraicGeometry.
Scheme} (𝒰 : X.OpenCover) (i : 𝒰.I₀), AlgebraicGeometry.IsOpenImmersion (𝒰.f i)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…
· 使用引理 `AlgebraicGeometry.IsZariskiLocalAtSource.comp`：comp {UX : Scheme.{u}} (H
 : P f) (i : UX ⟶ X) [IsOpenImmersion i] : P (i ≫ f)
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.instFstScheme`：∀ {X Y Z : AlgebraicGeo
metry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z) [H : AlgebraicGeometry.IsOpenImmersion f],
   AlgebraicGeometry.IsOpenImmersion …
· 使用定理 `AlgebraicGeometry.Scheme.instIsStableUnderBaseChangePrecoverageOfIsJoint
lySurjectivePreservingOfIsStableUnderBaseChange`：∀ (P : CategoryTheory.MorphismP
roperty AlgebraicGeometry.Scheme)   [AlgebraicGeometry.Scheme.IsJointlySurjectiv
ePreserving P] [P.IsStableUnd…
· 使用定理 `AlgebraicGeometry.Scheme.instIsJointlySurjectivePreservingIsOpenImmersio
n`：AlgebraicGeometry.Scheme.IsJointlySurjectivePreserving AlgebraicGeometry.IsOp
enImmersion
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `CategoryTheory.MorphismProperty.iff_of_zeroHypercover_source`：∀ {C : Typ
e u} [inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.MorphismPrope
rty C}   {K : CategoryTheory.Precoverage C} [P.IsL…
· 使用定理 `AlgebraicGeometry.Scheme.Cover.pullbackHom_map`：∀ {P : CategoryTheory.Mo
rphismProperty AlgebraicGeometry.Scheme} [inst : P.IsStableUnderBaseChange]   [i
nst_1 : AlgebraicGeometry.Scheme.IsJ…
· 使用引理 `CategoryTheory.MorphismProperty.comp_mem`：comp_mem (W : MorphismProperty
 C) [W.IsStableUnderComposition] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : W f) 
(hg : W g) : W (f ≫ g)
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toIsStableUnderComposit
ion`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheor
y.MorphismProperty C}   [self : W.IsMultiplicative], W.IsStableUn…
· 使用引理 `AlgebraicGeometry.IsZariskiLocalAtSource.of_isOpenImmersion`：of_isOpenIm
mersion [P.ContainsIdentities] [IsOpenImmersion f] : P f
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toContainsIdentities`：∀
 {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheory.Morp
hismProperty C}   [self : W.IsMultiplicative], W.ContainsId…
-/
lemma isZariskiLocalAtTarget [P.IsMultiplicative]
    (hP : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [IsOpenImmersion g], P (f ≫ g) → P f) :
    IsZariskiLocalAtTarget P := by
  refine .mk_of_iff_of_zeroHypercover fun {X Y} f 𝒰 ↦ ⟨fun hf i ↦ ?_, fun h ↦ ?_⟩
  · apply hP _ (𝒰.f i)
    rw [← pullback.condition]
    exact IsZariskiLocalAtSource.comp hf _
  · rw [P.iff_of_zeroHypercover_source (𝒰.pullback₁ f)]
    intro i
    rw [← Scheme.Cover.pullbackHom_map]
    exact P.comp_mem _ _ (h i) (of_isOpenImmersion _)

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.IsZariskiLocalAtSource.sigmaDesc** 是 Mathlib 中的一个引理，位于命名空间 `
AlgebraicGeometry.IsZariskiLocalAtSource`。
形式化陈述：sigmaDesc {X : Scheme.{u}} {ι : Type v} [Small.{u} ι] {Y : ι -> Scheme.{u}
} {f : forall i, Y i ⟶ X} (hf : forall i, P (f i)) : P (Sigma.desc f)
参数：hf : forall i, P (f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.IsLocallyDirected.instHasColimit`：∀ {J : Type w
} [inst : CategoryTheory.Category.{v, w} J] (F : CategoryTheory.Functor J Algebr
aicGeometry.Scheme)   [∀ {i j : J} (f : i ⟶ j),…
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.of_isIso`：∀ {Y Z : AlgebraicGeometry.S
cheme} (g : Y ⟶ Z) [CategoryTheory.IsIso g], AlgebraicGeometry.IsOpenImmersion g
· 使用定理 `CategoryTheory.Discrete.instIsIso`：∀ {I : Type u₁} {i j : CategoryTheory
.Discrete I} (f : i ⟶ j), CategoryTheory.IsIso f
· 使用定理 `CategoryTheory.instIsLocallyDirectedDiscrete`：∀ {J : Type u_1} (F : Cate
goryTheory.Functor (CategoryTheory.Discrete J) (Type u_2)), F.IsLocallyDirected
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.IsZariskiLocalAtSource.iff_of_openCover`：iff_of_openCo
ver : P f ↔ forall i, P (𝒰.f i ≫ f)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AlgebraicGeometry.Scheme.IsLocallyDirected.openCover_f`：∀ {J : Type w} [
inst : CategoryTheory.Category.{v, w} J] (F : CategoryTheory.Functor J Algebraic
Geometry.Scheme)   [inst_1 : ∀ {i j : J} (f …
· 使用定理 `CategoryTheory.Limits.colimit.ι_desc`：∀ {J : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} 
C]   {F : CategoryTheory.F…
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
lemma sigmaDesc {X : Scheme.{u}} {ι : Type v} [Small.{u} ι] {Y : ι → Scheme.{u}}
    {f : ∀ i, Y i ⟶ X} (hf : ∀ i, P (f i)) : P (Sigma.desc f) := by
  rw [IsZariskiLocalAtSource.iff_of_openCover (P := P) (Scheme.IsLocallyDirected.openCover _)]
  exact fun i ↦ by simp [hf]

section IsZariskiLocalAtSourceAndTarget

/-- If `P` is local at the source and the target, then restriction on both source and target
preserves `P`. -/
/-
**AlgebraicGeometry.IsZariskiLocalAtSource.resLE** 是 Mathlib 中的一个引理，位于命名空间 `Alge
braicGeometry.IsZariskiLocalAtSource`。
形式化陈述：resLE [IsZariskiLocalAtTarget P] {U : Y.Opens} {V : X.Opens} (e : V <= f ⁻
¹ᵁ U) (hf : P f) : P (f.resLE U V e)
参数：e : V <= f ⁻¹ᵁ U；hf : P f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.IsZariskiLocalAtSource.comp`：comp {UX : Scheme.{u}} (H
 : P f) (i : UX ⟶ X) [IsOpenImmersion i] : P (i ≫ f)
· 使用定理 `AlgebraicGeometry.IsZariskiLocalAtTarget.restrict`：restrict (hf : P f) (
U : Y.Opens) : P (f ∣_ U)
· 使用定理 `AlgebraicGeometry.instIsOpenImmersionHomOfLE`：∀ (X : AlgebraicGeometry.S
cheme) {U V : X.Opens} (e : U ≤ V), AlgebraicGeometry.IsOpenImmersion (X.homOfLE
 e)

--- 原说明 ---
If `P` is local at the source and the target, then restriction on both source an
d target
preserves `P`.
-/
lemma resLE [IsZariskiLocalAtTarget P] {U : Y.Opens} {V : X.Opens}
    (e : V ≤ f ⁻¹ᵁ U)
    (hf : P f) : P (f.resLE U V e) :=
  IsZariskiLocalAtSource.comp (IsZariskiLocalAtTarget.restrict hf U) _

/-- If `P` is local at the source, local at the target and is stable under post-composition with
open immersions, then `P` can be checked locally around points. -/
/-
**AlgebraicGeometry.IsZariskiLocalAtSource.iff_exists_resLE** 是 Mathlib 中的一个引理，位
于命名空间 `AlgebraicGeometry.IsZariskiLocalAtSource`。
形式化陈述：iff_exists_resLE [IsZariskiLocalAtTarget P] [P.RespectsRight @IsOpenImmers
ion] : P f ↔ forall x : X, exists (U : Y.Opens) (V : X.Opens) (_ : x in V.1) (e 
: V <= f ⁻¹ᵁ U), P (f.resLE U V e)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `AlgebraicGeometry.IsZariskiLocalAtSource.resLE`：resLE [IsZariskiLocalAtT
arget P] {U : Y.Opens} {V : X.Opens} (e : V <= f ⁻¹ᵁ U) (hf : P f) : P (f.resLE 
U V e)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.IsZariskiLocalAtSource.iff_of_iSup_eq_top`：iff_of_iSup
_eq_top {ι} (U : ι -> X.Opens) (hU : iSup U = ⊤) : P f ↔ forall i, P ((U i).ι ≫ 
f)
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `AlgebraicGeometry.Scheme.Hom.resLE_comp_ι`：resLE_comp_ι : f.resLE U V e 
≫ U.ι = V.ι ≫ f
· 使用定理 `CategoryTheory.MorphismProperty.RespectsRight.postcomp`：∀ {C : Type u} {
inst : CategoryTheory.CategoryStruct.{v, u} C} {P Q : CategoryTheory.MorphismPro
perty C}   [self : P.RespectsRight Q] {X Y Z…
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι`：∀ {X : AlgebraicGeo
metry.Scheme} (U : X.Opens), AlgebraicGeometry.IsOpenImmersion U.ι
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
If `P` is local at the source, local at the target and is stable under post-comp
osition with
open immersions, then `P` can be checked locally around points.
-/
lemma iff_exists_resLE [IsZariskiLocalAtTarget P]
    [P.RespectsRight @IsOpenImmersion] :
    P f ↔ ∀ x : X, ∃ (U : Y.Opens) (V : X.Opens) (_ : x ∈ V.1) (e : V ≤ f ⁻¹ᵁ U),
      P (f.resLE U V e) := by
  refine ⟨fun hf x ↦ ⟨⊤, ⊤, trivial, by simp, resLE _ hf⟩, fun hf ↦ ?_⟩
  choose U V hxU e hf using hf
  rw [IsZariskiLocalAtSource.iff_of_iSup_eq_top (fun x : X ↦ V x) (P := P)]
  · intro x
    rw [← Scheme.Hom.resLE_comp_ι _ (e x)]
    exact MorphismProperty.RespectsRight.postcomp (Q := @IsOpenImmersion) _ inferInstance _ (hf x)
  · rw [eq_top_iff]
    rintro x -
    simp only [Opens.mem_iSup]
    use x, hxU x

end IsZariskiLocalAtSourceAndTarget

end IsZariskiLocalAtSource

/-- An `AffineTargetMorphismProperty` is a class of morphisms from an arbitrary scheme into an
affine scheme. -/
/-
**AlgebraicGeometry.AffineTargetMorphismProperty** 是 Mathlib 中的一个定义，位于命名空间 `Alge
braicGeometry`。
形式化陈述：AffineTargetMorphismProperty
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An `AffineTargetMorphismProperty` is a class of morphisms from an arbitrary sche
me into an
affine scheme.
-/
def AffineTargetMorphismProperty :=
  ∀ ⦃X Y : Scheme⦄ (_ : X ⟶ Y) [IsAffine Y], Prop

namespace AffineTargetMorphismProperty

@[ext]
/-
**AlgebraicGeometry.AffineTargetMorphismProperty.ext** 是 Mathlib 中的一个引理，位于命名空间 `
AlgebraicGeometry.AffineTargetMorphismProperty`。
形式化陈述：ext {P Q : AffineTargetMorphismProperty} (H : forall ⦃X Y : Scheme⦄ (f : X
 ⟶ Y) [IsAffine Y], P f ↔ Q f) : P = Q
参数：H : forall ⦃X Y : Scheme⦄ (f : X ⟶ Y) [IsAffine Y], P f ↔ Q f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
lemma ext {P Q : AffineTargetMorphismProperty}
    (H : ∀ ⦃X Y : Scheme⦄ (f : X ⟶ Y) [IsAffine Y], P f ↔ Q f) : P = Q := by
  delta AffineTargetMorphismProperty; ext; exact H _

/-- The restriction of a `MorphismProperty Scheme` to morphisms with affine target. -/
/-
**AlgebraicGeometry.AffineTargetMorphismProperty.of** 是 Mathlib 中的一个定义，位于命名空间 `A
lgebraicGeometry.AffineTargetMorphismProperty`。
形式化陈述：of (P : MorphismProperty Scheme) : AffineTargetMorphismProperty
参数：P : MorphismProperty Scheme。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The restriction of a `MorphismProperty Scheme` to morphisms with affine target.
-/
def of (P : MorphismProperty Scheme) : AffineTargetMorphismProperty :=
  fun _ _ f _ ↦ P f

/-- An `AffineTargetMorphismProperty` can be extended to a `MorphismProperty` such that it
*never* holds when the target is not affine -/
/-
**AlgebraicGeometry.AffineTargetMorphismProperty.toProperty** 是 Mathlib 中的一个定义，位
于命名空间 `AlgebraicGeometry.AffineTargetMorphismProperty`。
形式化陈述：toProperty (P : AffineTargetMorphismProperty) : MorphismProperty Scheme
参数：P : AffineTargetMorphismProperty。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An `AffineTargetMorphismProperty` can be extended to a `MorphismProperty` such t
hat it
*never* holds when the target is not affine
-/
def toProperty (P : AffineTargetMorphismProperty) :
    MorphismProperty Scheme := fun _ _ f => ∃ h, @P _ _ f h
/-
**AlgebraicGeometry.AffineTargetMorphismProperty.toProperty_apply** 是 Mathlib 中的
一个定理，位于命名空间 `AlgebraicGeometry.AffineTargetMorphismProperty`。
形式化陈述：toProperty_apply (P : AffineTargetMorphismProperty) {X Y : Scheme} (f : X 
⟶ Y) [i : IsAffine Y] : P.toProperty f ↔ P f
参数：P : AffineTargetMorphismProperty；f : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem toProperty_apply (P : AffineTargetMorphismProperty)
    {X Y : Scheme} (f : X ⟶ Y) [i : IsAffine Y] : P.toProperty f ↔ P f := by
  delta AffineTargetMorphismProperty.toProperty; simp [*]
/-
**AlgebraicGeometry.AffineTargetMorphismProperty.cancel_left_of_respectsIso** 是 
Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.AffineTargetMorphismProperty`。
形式化陈述：cancel_left_of_respectsIso (P : AffineTargetMorphismProperty) [P.toPropert
y.RespectsIso] {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso f] [IsAffine Z] :
 P (f ≫ g) ↔ P g
参数：P : AffineTargetMorphismProperty；f : X ⟶ Y；g : Y ⟶ Z。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.AffineTargetMorphismProperty.toProperty_apply`：toPrope
rty_apply (P : AffineTargetMorphismProperty) {X Y : Scheme} (f : X ⟶ Y) [i : IsA
ffine Y] : P.toProperty f ↔ P f
· 使用定理 `CategoryTheory.MorphismProperty.cancel_left_of_respectsIso`：cancel_left_
of_respectsIso (P : MorphismProperty C) [hP : RespectsIso P] {X Y Z : C} (f : X 
⟶ Y) (g : Y ⟶ Z) [IsIso f] : P (f ≫ g) ↔ P g
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem cancel_left_of_respectsIso
    (P : AffineTargetMorphismProperty) [P.toProperty.RespectsIso]
    {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso f] [IsAffine Z] : P (f ≫ g) ↔ P g := by
  rw [← P.toProperty_apply, ← P.toProperty_apply, P.toProperty.cancel_left_of_respectsIso]
/-
**AlgebraicGeometry.AffineTargetMorphismProperty.cancel_right_of_respectsIso** 是
 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.AffineTargetMorphismProperty`。
形式化陈述：cancel_right_of_respectsIso (P : AffineTargetMorphismProperty) [P.toProper
ty.RespectsIso] {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso g] [IsAffine Z] 
[IsAffine Y] : P (f ≫ g) ↔ P f
参数：P : AffineTargetMorphismProperty；f : X ⟶ Y；g : Y ⟶ Z。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.AffineTargetMorphismProperty.toProperty_apply`：toPrope
rty_apply (P : AffineTargetMorphismProperty) {X Y : Scheme} (f : X ⟶ Y) [i : IsA
ffine Y] : P.toProperty f ↔ P f
· 使用定理 `CategoryTheory.MorphismProperty.cancel_right_of_respectsIso`：cancel_righ
t_of_respectsIso (P : MorphismProperty C) [hP : RespectsIso P] {X Y Z : C} (f : 
X ⟶ Y) (g : Y ⟶ Z) [IsIso g] : P (f ≫ g) ↔ P f
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem cancel_right_of_respectsIso
    (P : AffineTargetMorphismProperty) [P.toProperty.RespectsIso]
    {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso g] [IsAffine Z] [IsAffine Y] :
    P (f ≫ g) ↔ P f := by rw [← P.toProperty_apply, ← P.toProperty_apply,
      P.toProperty.cancel_right_of_respectsIso]

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.AffineTargetMorphismProperty.arrow_mk_iso_iff** 是 Mathlib 中的
一个定理，位于命名空间 `AlgebraicGeometry.AffineTargetMorphismProperty`。
形式化陈述：arrow_mk_iso_iff (P : AffineTargetMorphismProperty) [P.toProperty.Respects
Iso] {X Y X' Y' : Scheme} {f : X ⟶ Y} {f' : X' ⟶ Y'} (e : Arrow.mk f ≅ Arrow.mk 
f') {h : IsAffine Y} : letI : IsAffine Y'
参数：P : AffineTargetMorphismProperty；e : Arrow.mk f ≅ Arrow.mk f'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.IsAffine.of_isIso`：∀ {X Y : AlgebraicGeometry.Scheme} 
(f : X ⟶ Y) [CategoryTheory.IsIso f] [h : AlgebraicGeometry.IsAffine Y],   Algeb
raicGeometry.IsAffine X
· 使用定理 `CategoryTheory.Arrow.isIso_right`：∀ {T : Type u} [inst : CategoryTheory.
Category.{v, u} T] {f g : CategoryTheory.Arrow T} (sq : g ⟶ f)   [CategoryTheory
.IsIso sq], CategoryTh…
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.AffineTargetMorphismProperty.toProperty_apply`：toPrope
rty_apply (P : AffineTargetMorphismProperty) {X Y : Scheme} (f : X ⟶ Y) [i : IsA
ffine Y] : P.toProperty f ↔ P f
· 使用定理 `CategoryTheory.MorphismProperty.arrow_mk_iso_iff`：arrow_mk_iso_iff (P : 
MorphismProperty C) [RespectsIso P] {W X Y Z : C} {f : W ⟶ X} {g : Y ⟶ Z} (e : A
rrow.mk f ≅ Arrow.mk g) : P f ↔ P g
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem arrow_mk_iso_iff
    (P : AffineTargetMorphismProperty) [P.toProperty.RespectsIso]
    {X Y X' Y' : Scheme} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (e : Arrow.mk f ≅ Arrow.mk f') {h : IsAffine Y} :
    letI : IsAffine Y' := .of_isIso (Y := Y) e.inv.right
    P f ↔ P f' := by
  rw [← P.toProperty_apply, ← P.toProperty_apply, P.toProperty.arrow_mk_iso_iff e]
/-
**AlgebraicGeometry.AffineTargetMorphismProperty.respectsIso_mk** 是 Mathlib 中的一个
定理，位于命名空间 `AlgebraicGeometry.AffineTargetMorphismProperty`。
形式化陈述：respectsIso_mk {P : AffineTargetMorphismProperty} (h₁ : forall {X Y Z} (e 
: X ≅ Y) (f : Y ⟶ Z) [IsAffine Z], P f -> P (e.hom ≫ f)) (h₂ : forall {X Y Z} (e
 : Y ≅ Z) (f : X ⟶ Y) [IsAffine Y], P f -> @P _ _ (f ≫ e.hom) (.of_isIso e.inv))
 : P.toProperty.RespectsIso
参数：h₁ : forall {X Y Z} (e : X ≅ Y) (f : Y ⟶ Z) [IsAffine Z], P f -> P (e.hom ≫ f
)；h₂ : forall {X Y Z} (e : Y ≅ Z) (f : X ⟶ Y) [IsAffine Y], P f -> @P _ _ (f ≫ e
.hom) (.of_isIso e.inv)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.IsAffine.of_isIso`：∀ {X Y : AlgebraicGeometry.Scheme} 
(f : X ⟶ Y) [CategoryTheory.IsIso f] [h : AlgebraicGeometry.IsAffine Y],   Algeb
raicGeometry.IsAffine X
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `CategoryTheory.MorphismProperty.RespectsIso.mk`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] (P : CategoryTheory.MorphismProperty C),   (∀ {
X Y Z : C} (e : X ≅ Y) (f : Y ⟶ Z), …
-/
theorem respectsIso_mk {P : AffineTargetMorphismProperty}
    (h₁ : ∀ {X Y Z} (e : X ≅ Y) (f : Y ⟶ Z) [IsAffine Z], P f → P (e.hom ≫ f))
    (h₂ : ∀ {X Y Z} (e : Y ≅ Z) (f : X ⟶ Y) [IsAffine Y],
      P f → @P _ _ (f ≫ e.hom) (.of_isIso e.inv)) :
    P.toProperty.RespectsIso := by
  apply MorphismProperty.RespectsIso.mk
  · rintro X Y Z e f ⟨a, h⟩; exact ⟨a, h₁ e f h⟩
  · rintro X Y Z e f ⟨a, h⟩; exact ⟨.of_isIso e.inv, h₂ e f h⟩
/-
**AlgebraicGeometry.AffineTargetMorphismProperty.respectsIso_of** 是 Mathlib 中的一个
实例，位于命名空间 `AlgebraicGeometry.AffineTargetMorphismProperty`。
形式化陈述：respectsIso_of (P : MorphismProperty Scheme) [P.RespectsIso] : (of P).toPr
operty.RespectsIso
参数：P : MorphismProperty Scheme。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.AffineTargetMorphismProperty.respectsIso_mk`：respectsI
so_mk {P : AffineTargetMorphismProperty} (h₁ : forall {X Y Z} (e : X ≅ Y) (f : Y
 ⟶ Z) [IsAffine Z], P f -> P (e.hom ≫ f)) (h₂ : for…
· 使用定理 `CategoryTheory.MorphismProperty.RespectsIso.precomp`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C] (P : CategoryTheory.MorphismProperty C) [P
.RespectsIso]   {X Y Z : C} (e : X ⟶ Y) […
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.MorphismProperty.RespectsIso.postcomp`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] (P : CategoryTheory.MorphismProperty C) [
P.RespectsIso]   {X Y Z : C} (e : Y ⟶ Z) […
-/
instance respectsIso_of
    (P : MorphismProperty Scheme) [P.RespectsIso] :
    (of P).toProperty.RespectsIso := by
  apply respectsIso_mk
  · intro _ _ _ _ _ _; apply MorphismProperty.RespectsIso.precomp
  · intro _ _ _ _ _ _; apply MorphismProperty.RespectsIso.postcomp

/-- We say that `P : AffineTargetMorphismProperty` is a local property if
1. `P` respects isomorphisms.
2. If `P` holds for `f : X ⟶ Y`, then `P` holds for `f ∣_ Y.basicOpen r` for any
  global section `r`.
3. If `P` holds for `f ∣_ Y.basicOpen r` for all `r` in a spanning set of the global sections,
  then `P` holds for `f`.
-/
/-
**AlgebraicGeometry.AffineTargetMorphismProperty.IsLocal** 是 Mathlib 中的一个归纳类型，位于
命名空间 `AlgebraicGeometry.AffineTargetMorphismProperty`。
形式化陈述：AlgebraicGeometry.AffineTargetMorphismProperty → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say that `P : AffineTargetMorphismProperty` is a local property if
1. `P` respects isomorphisms.
2. If `P` holds for `f : X ⟶ Y`, then `P` holds for `f ∣_ Y.basicOpen r` for any
  global section `r`.
3. If `P` holds for `f ∣_ Y.basicOpen r` for all `r` in a spanning set of the gl
obal sections,
  then `P` holds for `f`.
-/
class IsLocal (P : AffineTargetMorphismProperty) : Prop where
  /-- `P` as a morphism property respects isomorphisms -/
  respectsIso : P.toProperty.RespectsIso
  /-- `P` is stable under restriction to a basic open set of global sections. -/
  to_basicOpen :
    ∀ {X Y : Scheme} [IsAffine Y] (f : X ⟶ Y) (r : Γ(Y, ⊤)), P f → P (f ∣_ Y.basicOpen r)
  /-- `P` for `f` if `P` holds for `f` restricted to basic sets of a spanning set of the global
  sections -/
  of_basicOpenCover :
    ∀ {X Y : Scheme} [IsAffine Y] (f : X ⟶ Y) (s : Finset Γ(Y, ⊤))
      (_ : Ideal.span (s : Set Γ(Y, ⊤)) = ⊤), (∀ r : s, P (f ∣_ Y.basicOpen r.1)) → P f

attribute [instance] AffineTargetMorphismProperty.IsLocal.respectsIso

open AffineTargetMorphismProperty in
/-
**AlgebraicGeometry.AffineTargetMorphismProperty.** 是 Mathlib 中的一个实例，位于命名空间 `Alg
ebraicGeometry.AffineTargetMorphismProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (P : MorphismProperty Scheme) [IsZariskiLocalAtTarget P] :
    (of P).IsLocal where
  respectsIso := inferInstance
  to_basicOpen _ _ H := IsZariskiLocalAtTarget.restrict H _
  of_basicOpenCover {_ Y} _ _ _ hs := IsZariskiLocalAtTarget.of_iSup_eq_top _
    ((isAffineOpen_top Y).iSup_basicOpen_eq_self_iff.mpr hs)

/-- A `P : AffineTargetMorphismProperty` is stable under base change if `P` holds for `Y ⟶ S`
implies that `P` holds for `X ×ₛ Y ⟶ X` with `X` and `S` affine schemes. -/
/-
**AlgebraicGeometry.AffineTargetMorphismProperty.IsStableUnderBaseChange** 是 Mat
hlib 中的一个定义，位于命名空间 `AlgebraicGeometry.AffineTargetMorphismProperty`。
形式化陈述：IsStableUnderBaseChange (P : AffineTargetMorphismProperty) : Prop
参数：P : AffineTargetMorphismProperty。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `P : AffineTargetMorphismProperty` is stable under base change if `P` holds fo
r `Y ⟶ S`
implies that `P` holds for `X ×ₛ Y ⟶ X` with `X` and `S` affine schemes.
-/
def IsStableUnderBaseChange (P : AffineTargetMorphismProperty) : Prop :=
  ∀ ⦃Z X Y S : Scheme⦄ [IsAffine S] [IsAffine X] {f : X ⟶ S} {g : Y ⟶ S}
    {f' : Z ⟶ Y} {g' : Z ⟶ X}, IsPullback g' f' f g → P g → P g'
/-
**AlgebraicGeometry.AffineTargetMorphismProperty.IsStableUnderBaseChange.mk** 是 
Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.AffineTargetMorphismProperty.IsStableUn
derBaseChange`。
形式化陈述：∀ (P : AlgebraicGeometry.AffineTargetMorphismProperty) [P.toProperty.Respe
ctsIso],   (∀ ⦃X Y S : AlgebraicGeometry.Scheme⦄ [inst : AlgebraicGeometry.IsAff
ine S] [inst_1 : AlgebraicGeometry.IsAffine X]       (f : X ⟶ S) (g : Y ⟶ S), P 
g → P (CategoryTheory.Limits.pullback.fst f g)) →     P.IsStableUnderBaseChange
参数：P : AlgebraicGeometry.AffineTargetMorphismProperty；∀ ⦃X Y S : AlgebraicGeomet
ry.Scheme⦄ [inst : AlgebraicGeometry.IsAffine S] [inst_1 : AlgebraicGeometry.IsA
ffine X]       (f : X ⟶ S) (g : Y ⟶ S), P g → P (CategoryTheory.Limits.pullback.
fst f g)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.AffineTargetMorphismProperty.cancel_left_of_respectsIs
o`：cancel_left_of_respectsIso (P : AffineTargetMorphismProperty) [P.toProperty.R
espectsIso] {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso f] …
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `CategoryTheory.IsPullback.isoPullback_inv_fst`：isoPullback_inv_fst (h : 
IsPullback fst snd f g) [HasPullback f g] : h.isoPullback.inv ≫ fst = pullback.f
st _ _
-/
lemma IsStableUnderBaseChange.mk (P : AffineTargetMorphismProperty) [P.toProperty.RespectsIso]
    (H : ∀ ⦃X Y S : Scheme⦄ [IsAffine S] [IsAffine X] (f : X ⟶ S) (g : Y ⟶ S),
      P g → P (pullback.fst f g)) : P.IsStableUnderBaseChange := by
  intro Z X Y S _ _ f g f' g' h hg
  rw [← P.cancel_left_of_respectsIso h.isoPullback.inv, h.isoPullback_inv_fst]
  exact H f g hg

end AffineTargetMorphismProperty

section targetAffineLocally

/-- For a `P : AffineTargetMorphismProperty`, `targetAffineLocally P` holds for
`f : X ⟶ Y` whenever `P` holds for the restriction of `f` on every affine open subset of `Y`. -/
/-
**AlgebraicGeometry.targetAffineLocally** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeom
etry`。
形式化陈述：AlgebraicGeometry.AffineTargetMorphismProperty → CategoryTheory.MorphismPr
operty AlgebraicGeometry.Scheme
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.instIsAffineToSchemeValOpensMemSetAffineOpens`：∀ {Y : 
AlgebraicGeometry.Scheme} (U : ↑Y.affineOpens), AlgebraicGeometry.IsAffine ↑↑U

--- 原说明 ---
For a `P : AffineTargetMorphismProperty`, `targetAffineLocally P` holds for
`f : X ⟶ Y` whenever `P` holds for the restriction of `f` on every affine open s
ubset of `Y`.
-/
def targetAffineLocally (P : AffineTargetMorphismProperty) : MorphismProperty Scheme :=
  fun {X Y : Scheme} (f : X ⟶ Y) => ∀ U : Y.affineOpens, P (f ∣_ U)
/-
**AlgebraicGeometry.of_targetAffineLocally_of_isPullback** 是 Mathlib 中的一个定理，位于命名
空间 `AlgebraicGeometry`。
形式化陈述：∀ {P : AlgebraicGeometry.AffineTargetMorphismProperty} [P.IsLocal] {X Y UX
 UY : AlgebraicGeometry.Scheme}   [inst : AlgebraicGeometry.IsAffine UY] {f : X 
⟶ Y} {iY : UY ⟶ Y} [AlgebraicGeometry.IsOpenImmersion iY] {iX : UX ⟶ X}   {f' : 
UX ⟶ UY}, CategoryTheory.IsPullback iX f' f iY → AlgebraicGeometry.targetAffineL
ocally P f → P f'
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.AffineTargetMorphismProperty.cancel_left_of_respectsIs
o`：cancel_left_of_respectsIso (P : AffineTargetMorphismProperty) [P.toProperty.R
espectsIso] {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso f] …
· 使用定理 `AlgebraicGeometry.AffineTargetMorphismProperty.IsLocal.respectsIso`：∀ {P
 : AlgebraicGeometry.AffineTargetMorphismProperty} [self : P.IsLocal], P.toPrope
rty.RespectsIso
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `CategoryTheory.IsPullback.isoPullback_inv_snd`：isoPullback_inv_snd (h : 
IsPullback fst snd f g) [HasPullback f g] : h.isoPullback.inv ≫ snd = pullback.s
nd _ _
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AlgebraicGeometry.instIsAffineToSchemeValOpensMemSetAffineOpens`：∀ {Y : 
AlgebraicGeometry.Scheme} (U : ↑Y.affineOpens), AlgebraicGeometry.IsAffine ↑↑U
· 使用定理 `AlgebraicGeometry.isAffineOpen_opensRange`：isAffineOpen_opensRange {X Y 
: Scheme} [IsAffine X] (f : X ⟶ Y) [H : IsOpenImmersion f] : IsAffineOpen f.open
sRange
· 使用定理 `AlgebraicGeometry.IsAffine.of_isIso`：∀ {X Y : AlgebraicGeometry.Scheme} 
(f : X ⟶ Y) [CategoryTheory.IsIso f] [h : AlgebraicGeometry.IsAffine Y],   Algeb
raicGeometry.IsAffine X
· 使用定理 `CategoryTheory.Arrow.isIso_right`：∀ {T : Type u} [inst : CategoryTheory.
Category.{v, u} T] {f g : CategoryTheory.Arrow T} (sq : g ⟶ f)   [CategoryTheory
.IsIso sq], CategoryTh…
· 使用定理 `AlgebraicGeometry.AffineTargetMorphismProperty.arrow_mk_iso_iff`：arrow_m
k_iso_iff (P : AffineTargetMorphismProperty) [P.toProperty.RespectsIso] {X Y X' 
Y' : Scheme} {f : X ⟶ Y} {f' : X' ⟶ Y'} (e : Arrow.mk…
-/
theorem of_targetAffineLocally_of_isPullback
    {P : AffineTargetMorphismProperty} [P.IsLocal]
    {X Y UX UY : Scheme.{u}} [IsAffine UY] {f : X ⟶ Y} {iY : UY ⟶ Y} [IsOpenImmersion iY]
    {iX : UX ⟶ X} {f' : UX ⟶ UY} (h : IsPullback iX f' f iY) (hf : targetAffineLocally P f) :
    P f' := by
  rw [← P.cancel_left_of_respectsIso h.isoPullback.inv, h.isoPullback_inv_snd]
  exact (P.arrow_mk_iso_iff
    (morphismRestrictOpensRange f _)).mp (hf ⟨_, isAffineOpen_opensRange iY⟩)

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (P : AffineTargetMorphismProperty) [P.toProperty.RespectsIso] :
    (targetAffineLocally P).RespectsIso := by
  apply MorphismProperty.RespectsIso.mk
  · introv H U
    rw [morphismRestrict_comp, P.cancel_left_of_respectsIso]
    exact H U
  · introv H
    rintro ⟨U, hU : IsAffineOpen U⟩; dsimp
    have : IsAffine _ := hU.preimage_of_isIso e.hom
    rw [morphismRestrict_comp, P.cancel_right_of_respectsIso]
    exact H ⟨(Opens.map e.hom.base).obj U, hU.preimage_of_isIso e.hom⟩

/--
`HasAffineProperty P Q` is a type class asserting that `P` is local at the target, and over affine
schemes, it is equivalent to `Q : AffineTargetMorphismProperty`.
To make the proofs easier, we state it instead as
1. `Q` is local at the target
2. `P f` if and only if `∀ U, Q (f ∣_ U)` ranging over all affine opens of the target of `f`.

See `HasAffineProperty.iff`.
-/
/-
**AlgebraicGeometry.HasAffineProperty** 是 Mathlib 中的一个归纳类型，位于命名空间 `AlgebraicGeom
etry`。
形式化陈述：CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme →   outParam Alge
braicGeometry.AffineTargetMorphismProperty → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`HasAffineProperty P Q` is a type class asserting that `P` is local at the targe
t, and over affine
schemes, it is equivalent to `Q : AffineTargetMorphismProperty`.
To make the proofs easier, we state it instead as
1. `Q` is local at the target
2. `P f` if and only if `∀ U, Q (f ∣_ U)` ranging over all affine opens of the t
arget of `f`.

See `HasAffineProperty.iff`.
-/
class HasAffineProperty (P : MorphismProperty Scheme)
    (Q : outParam AffineTargetMorphismProperty) : Prop where
  isLocal_affineProperty : Q.IsLocal
  eq_targetAffineLocally' : P = targetAffineLocally Q

namespace HasAffineProperty

variable (P : MorphismProperty Scheme) {Q} [HasAffineProperty P Q]
variable {X Y : Scheme.{u}} {f : X ⟶ Y}

/-
**AlgebraicGeometry.HasAffineProperty.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeome
try.HasAffineProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (Q : AffineTargetMorphismProperty) [Q.IsLocal] :
    HasAffineProperty (targetAffineLocally Q) Q :=
  ⟨inferInstance, rfl⟩
/-
**AlgebraicGeometry.HasAffineProperty.eq_targetAffineLocally** 是 Mathlib 中的一个定理，
位于命名空间 `AlgebraicGeometry.HasAffineProperty`。
形式化陈述：∀ (P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme) {Q : Alge
braicGeometry.AffineTargetMorphismProperty}   [AlgebraicGeometry.HasAffineProper
ty P Q], P = AlgebraicGeometry.targetAffineLocally Q
参数：P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.HasAffineProperty.eq_targetAffineLocally'`：∀ {P : Cate
goryTheory.MorphismProperty AlgebraicGeometry.Scheme}   {Q : outParam AlgebraicG
eometry.AffineTargetMorphismProperty} [self : Alg…
-/
lemma eq_targetAffineLocally : P = targetAffineLocally Q := eq_targetAffineLocally'

/-- Every property local at the target can be associated with an affine target property.
This is not an instance as the associated property can often take on simpler forms. -/
/-
**AlgebraicGeometry.HasAffineProperty.of_isZariskiLocalAtTarget** 是 Mathlib 中的一个
定理，位于命名空间 `AlgebraicGeometry.HasAffineProperty`。
形式化陈述：∀ (P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme) [Algebrai
cGeometry.IsZariskiLocalAtTarget P],   AlgebraicGeometry.HasAffineProperty P (Al
gebraicGeometry.AffineTargetMorphismProperty.of P)
参数：P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme；AlgebraicGeometr
y.AffineTargetMorphismProperty.of P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.AffineTargetMorphismProperty.instIsLocalOfOfIsZariskiL
ocalAtTarget`：∀ (P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme) [
AlgebraicGeometry.IsZariskiLocalAtTarget P],   (AlgebraicGeometry.AffineTa…
· 使用引理 `CategoryTheory.MorphismProperty.ext`：ext (W W' : MorphismProperty C) (h 
: forall ⦃X Y : C⦄ (f : X ⟶ Y), W f ↔ W' f) : W = W'
· 使用定理 `AlgebraicGeometry.instIsAffineToSchemeValOpensMemSetAffineOpens`：∀ {Y : 
AlgebraicGeometry.Scheme} (U : ↑Y.affineOpens), AlgebraicGeometry.IsAffine ↑↑U
· 使用定理 `AlgebraicGeometry.IsZariskiLocalAtTarget.restrict`：restrict (hf : P f) (
U : Y.Opens) : P (f ∣_ U)
· 使用引理 `CategoryTheory.MorphismProperty.of_zeroHypercover_target`：of_zeroHyperco
ver_target {P : MorphismProperty C} {K : Precoverage C} [K.HasPullbacks] [P.IsLo
calAtTarget K] {X Y : C} {f : X ⟶ Y} (𝒰 : Prec…
· 使用定理 `AlgebraicGeometry.Scheme.instHasPullbacksPrecoverageOfHasPullbacks`：∀ (P
 : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme) [P.HasPullbacks],  
 (AlgebraicGeometry.Scheme.precoverage P).HasPullbacks
· 使用定理 `AlgebraicGeometry.Scheme.instHasPullbacksIsOpenImmersion`：AlgebraicGeome
try.IsOpenImmersion.HasPullbacks
· 使用定理 `CategoryTheory.Precoverage.instSmallOfSmall`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] (J : CategoryTheory.Precoverage C) [J.Small] {S : 
C}   (E : J.ZeroHypercover S), E.…
· 使用定理 `AlgebraicGeometry.Scheme.instSmallPrecoverage`：∀ {P : CategoryTheory.Mor
phismProperty AlgebraicGeometry.Scheme}, (AlgebraicGeometry.Scheme.precoverage P
).Small
· 使用定理 `AlgebraicGeometry.of_targetAffineLocally_of_isPullback`：∀ {P : Algebraic
Geometry.AffineTargetMorphismProperty} [P.IsLocal] {X Y UX UY : AlgebraicGeometr
y.Scheme}   [inst : AlgebraicGeometry.IsAffi…
· 使用定理 `CategoryTheory.Precoverage.ZeroHypercover.instHasPullbackFOfHasPullbacks
Presieve₀_1`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} 
(E : CategoryTheory.PreZeroHypercover X) (f : Y ⟶ X)   [E.presieve₀.HasPu…
· 使用定理 `CategoryTheory.Precoverage.ZeroHypercover.instHasPullbacksPresieve₀OfHas
Pullbacks`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (K : Categor
yTheory.Precoverage C) [K.HasPullbacks] {X Y : C}   (E : K.ZeroHypercov…
· 使用定理 `AlgebraicGeometry.Scheme.isAffine_affineCover`：∀ (X : AlgebraicGeometry.
Scheme) (i : X.affineCover.I₀), AlgebraicGeometry.IsAffine (X.affineCover.X i)
· 使用定理 `AlgebraicGeometry.Scheme.instIsOpenImmersionF`：∀ {X : AlgebraicGeometry.
Scheme} (𝒰 : X.OpenCover) (i : 𝒰.I₀), AlgebraicGeometry.IsOpenImmersion (𝒰.f i)
· 使用定理 `CategoryTheory.IsPullback.of_hasPullback`：of_hasPullback (f : X ⟶ Z) (g 
: Y ⟶ Z) [HasPullback f g] : IsPullback (pullback.fst f g) (pullback.snd f g) f 
g

--- 原说明 ---
Every property local at the target can be associated with an affine target prope
rty.
This is not an instance as the associated property can often take on simpler for
ms.
-/
lemma of_isZariskiLocalAtTarget (P : MorphismProperty Scheme.{u})
    [IsZariskiLocalAtTarget P] :
    HasAffineProperty P (AffineTargetMorphismProperty.of P) where
  isLocal_affineProperty := inferInstance
  eq_targetAffineLocally' := by
    ext X Y f
    constructor
    · intro hf ⟨U, hU⟩
      exact IsZariskiLocalAtTarget.restrict hf _
    · intro hf
      exact P.of_zeroHypercover_target Y.affineCover
        fun i ↦ of_targetAffineLocally_of_isPullback (.of_hasPullback _ _) hf
/-
**AlgebraicGeometry.HasAffineProperty.copy** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicG
eometry.HasAffineProperty`。
形式化陈述：∀ {P P' : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme}   {Q Q
' : AlgebraicGeometry.AffineTargetMorphismProperty} [AlgebraicGeometry.HasAffine
Property P Q],   P = P' → Q = Q' → AlgebraicGeometry.HasAffineProperty P' Q'
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.HasAffineProperty.isLocal_affineProperty`：∀ (P : Categ
oryTheory.MorphismProperty AlgebraicGeometry.Scheme)   {Q : outParam AlgebraicGe
ometry.AffineTargetMorphismProperty} [self : Alg…
· 使用定理 `AlgebraicGeometry.HasAffineProperty.eq_targetAffineLocally`：∀ (P : Categ
oryTheory.MorphismProperty AlgebraicGeometry.Scheme) {Q : AlgebraicGeometry.Affi
neTargetMorphismProperty}   [AlgebraicGeometry.H…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma copy {P P'} {Q Q'} [HasAffineProperty P Q]
    (e : P = P') (e' : Q = Q') : HasAffineProperty P' Q' where
  isLocal_affineProperty := e' ▸ isLocal_affineProperty P
  eq_targetAffineLocally' := e' ▸ e.symm ▸ eq_targetAffineLocally P

variable {P}
/-
**AlgebraicGeometry.HasAffineProperty.of_isPullback** 是 Mathlib 中的一个定理，位于命名空间 `A
lgebraicGeometry.HasAffineProperty`。
形式化陈述：∀ {P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme} {Q : Alge
braicGeometry.AffineTargetMorphismProperty}   [AlgebraicGeometry.HasAffineProper
ty P Q] {X Y : AlgebraicGeometry.Scheme} {f : X ⟶ Y}   {UX UY : AlgebraicGeometr
y.Scheme} [inst : AlgebraicGeometry.IsAffine UY] {iY : UY ⟶ Y}   [AlgebraicGeome
try.IsOpenImmersion iY] {iX : UX ⟶ X} {f' : UX ⟶ UY}, CategoryTheory.IsPullback 
iX f' f iY → P f → Q f'
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.of_targetAffineLocally_of_isPullback`：∀ {P : Algebraic
Geometry.AffineTargetMorphismProperty} [P.IsLocal] {X Y UX UY : AlgebraicGeometr
y.Scheme}   [inst : AlgebraicGeometry.IsAffi…
· 使用定理 `AlgebraicGeometry.HasAffineProperty.isLocal_affineProperty`：∀ (P : Categ
oryTheory.MorphismProperty AlgebraicGeometry.Scheme)   {Q : outParam AlgebraicGe
ometry.AffineTargetMorphismProperty} [self : Alg…
· 使用定理 `AlgebraicGeometry.HasAffineProperty.eq_targetAffineLocally`：∀ (P : Categ
oryTheory.MorphismProperty AlgebraicGeometry.Scheme) {Q : AlgebraicGeometry.Affi
neTargetMorphismProperty}   [AlgebraicGeometry.H…
-/
theorem of_isPullback {UX UY : Scheme.{u}} [IsAffine UY] {iY : UY ⟶ Y} [IsOpenImmersion iY]
    {iX : UX ⟶ X} {f' : UX ⟶ UY} (h : IsPullback iX f' f iY) (hf : P f) :
    Q f' :=
  letI := isLocal_affineProperty P
  of_targetAffineLocally_of_isPullback h (eq_targetAffineLocally (P := P) ▸ hf)
/-
**AlgebraicGeometry.HasAffineProperty.restrict** 是 Mathlib 中的一个定理，位于命名空间 `Algebr
aicGeometry.HasAffineProperty`。
形式化陈述：∀ {P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme} {Q : Alge
braicGeometry.AffineTargetMorphismProperty}   [AlgebraicGeometry.HasAffineProper
ty P Q] {X Y : AlgebraicGeometry.Scheme} {f : X ⟶ Y},   P f → ∀ (U : ↑Y.affineOp
ens), Q (f ∣_ ↑U)
参数：U : ↑Y.affineOpens；f ∣_ ↑U。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.HasAffineProperty.of_isPullback`：∀ {P : CategoryTheory
.MorphismProperty AlgebraicGeometry.Scheme} {Q : AlgebraicGeometry.AffineTargetM
orphismProperty}   [AlgebraicGeometry.H…
· 使用定理 `AlgebraicGeometry.instIsAffineToSchemeValOpensMemSetAffineOpens`：∀ {Y : 
AlgebraicGeometry.Scheme} (U : ↑Y.affineOpens), AlgebraicGeometry.IsAffine ↑↑U
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι`：∀ {X : AlgebraicGeo
metry.Scheme} (U : X.Opens), AlgebraicGeometry.IsOpenImmersion U.ι
· 使用定理 `CategoryTheory.IsPullback.flip`：flip (h : IsPullback fst snd f g) : IsPu
llback snd fst g f
· 使用定理 `AlgebraicGeometry.isPullback_morphismRestrict`：isPullback_morphismRestri
ct {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) : IsPullback (f ∣_ U) (f ⁻¹ᵁ U).
ι U.ι f
-/
theorem restrict (hf : P f) (U : Y.affineOpens) :
    Q (f ∣_ U) :=
  of_isPullback (isPullback_morphismRestrict f U).flip hf
/-
**AlgebraicGeometry.HasAffineProperty.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeome
try.HasAffineProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 900) : P.RespectsIso := by
  let := isLocal_affineProperty P
  rw [eq_targetAffineLocally P]
  infer_instance
/-
**AlgebraicGeometry.HasAffineProperty.of_iSup_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `
AlgebraicGeometry.HasAffineProperty`。
形式化陈述：∀ {P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme} {Q : Alge
braicGeometry.AffineTargetMorphismProperty}   [AlgebraicGeometry.HasAffineProper
ty P Q] {X Y : AlgebraicGeometry.Scheme} {f : X ⟶ Y} {ι : Sort u_1}   (U : ι → ↑
Y.affineOpens), ⨆ i, ↑(U i) = ⊤ → (∀ (i : ι), Q (f ∣_ ↑(U i))) → P f
参数：U : ι → ↑Y.affineOpens；U i；∀ (i : ι), Q (f ∣_ ↑(U i))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.instIsAffineToSchemeValOpensMemSetAffineOpens`：∀ {Y : 
AlgebraicGeometry.Scheme} (U : ↑Y.affineOpens), AlgebraicGeometry.IsAffine ↑↑U
· 使用定理 `AlgebraicGeometry.HasAffineProperty.isLocal_affineProperty`：∀ (P : Categ
oryTheory.MorphismProperty AlgebraicGeometry.Scheme)   {Q : outParam AlgebraicGe
ometry.AffineTargetMorphismProperty} [self : Alg…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.HasAffineProperty.eq_targetAffineLocally`：∀ (P : Categ
oryTheory.MorphismProperty AlgebraicGeometry.Scheme) {Q : AlgebraicGeometry.Affi
neTargetMorphismProperty}   [AlgebraicGeometry.H…
· 使用定理 `AlgebraicGeometry.of_affine_open_cover`：of_affine_open_cover {X : Scheme
} {P : X.affineOpens -> Prop} {ι} (U : ι -> X.affineOpens) (iSup_U : (⨆ i, U i :
 X.Opens) = ⊤) (V : X.affine…
· 使用定理 `AlgebraicGeometry.IsAffineOpen.instIsAffineToSchemeBasicOpen`：∀ {X : Alg
ebraicGeometry.Scheme} [AlgebraicGeometry.IsAffine X] (r : ↑(X.presheaf.obj (Opp
osite.op ⊤))),   AlgebraicGeometry.IsAffine ↑(X.ba…
· 使用定理 `AlgebraicGeometry.AffineTargetMorphismProperty.IsLocal.to_basicOpen`：∀ {
P : AlgebraicGeometry.AffineTargetMorphismProperty} [self : P.IsLocal] {X Y : Al
gebraicGeometry.Scheme}   [inst : AlgebraicGeometry.IsAff…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `TopologicalSpace.Opens.isOpenEmbedding`：isOpenEmbedding {X : TopCat.{u}}
 (U : Opens X) : IsOpenEmbedding (inclusion' U)
· 使用定理 `TopologicalSpace.Opens.isOpenEmbedding_obj_top`：isOpenEmbedding_obj_top 
{X : TopCat.{u}} (U : Opens X) : U.isOpenEmbedding.functor.obj ⊤ = U
· 使用定理 `AlgebraicGeometry.IsAffine.of_isIso`：∀ {X Y : AlgebraicGeometry.Scheme} 
(f : X ⟶ Y) [CategoryTheory.IsIso f] [h : AlgebraicGeometry.IsAffine Y],   Algeb
raicGeometry.IsAffine X
· 使用定理 `CategoryTheory.Arrow.isIso_right`：∀ {T : Type u} [inst : CategoryTheory.
Category.{v, u} T] {f g : CategoryTheory.Arrow T} (sq : g ⟶ f)   [CategoryTheory
.IsIso sq], CategoryTh…
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `AlgebraicGeometry.AffineTargetMorphismProperty.arrow_mk_iso_iff`：arrow_m
k_iso_iff (P : AffineTargetMorphismProperty) [P.toProperty.RespectsIso] {X Y X' 
Y' : Scheme} {f : X ⟶ Y} {f' : X' ⟶ Y'} (e : Arrow.mk…
· 使用定理 `AlgebraicGeometry.AffineTargetMorphismProperty.IsLocal.respectsIso`：∀ {P
 : AlgebraicGeometry.AffineTargetMorphismProperty} [self : P.IsLocal], P.toPrope
rty.RespectsIso
· 使用定理 `AlgebraicGeometry.AffineTargetMorphismProperty.IsLocal.of_basicOpenCover
`：∀ {P : AlgebraicGeometry.AffineTargetMorphismProperty} [self : P.IsLocal] {X Y
 : AlgebraicGeometry.Scheme}   [inst : AlgebraicGeometry.IsAff…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι`：∀ {X : AlgebraicGeo
metry.Scheme} (U : X.Opens), AlgebraicGeometry.IsOpenImmersion U.ι
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.Scheme.Opens.topIso_inv`：∀ {X : AlgebraicGeometry.Sche
me} (U : X.Opens), U.topIso.inv = X.presheaf.map (CategoryTheory.eqToHom ⋯).op
· 使用定理 `CategoryTheory.eqToHom_op`：eqToHom_op {X Y : C} (h : X = Y) : (eqToHom h
).op = eqToHom (congr_arg op h.symm)
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Ideal.map_top`：map_top : map f ⊤ = ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.mem_image`：mem_image : b in s.image f ↔ exists a in s, f a = b
-/
theorem of_iSup_eq_top
    {ι} (U : ι → Y.affineOpens) (hU : ⨆ i, (U i : Y.Opens) = ⊤)
    (hU' : ∀ i, Q (f ∣_ U i)) :
    P f := by
  let := isLocal_affineProperty P
  rw [eq_targetAffineLocally P]
  classical
  intro V
  induction V using of_affine_open_cover U hU with
  | basicOpen U r h =>
    have := AffineTargetMorphismProperty.IsLocal.to_basicOpen (f ∣_ U.1) (U.1.topIso.inv r) h
    exact (Q.arrow_mk_iso_iff
      (morphismRestrictRestrictBasicOpen f _ r)).mp this
  | openCover U s hs H =>
    apply AffineTargetMorphismProperty.IsLocal.of_basicOpenCover _
      (s.image (Scheme.Opens.topIso _).inv) (by simp [← Ideal.map_span, hs, Ideal.map_top])
    intro ⟨r, hr⟩
    obtain ⟨r, hr', rfl⟩ := Finset.mem_image.mp hr
    exact (Q.arrow_mk_iso_iff
      (morphismRestrictRestrictBasicOpen f _ r).symm).mp (H ⟨r, hr'⟩)
  | hU i => exact hU' i
/-
**AlgebraicGeometry.HasAffineProperty.iff_of_iSup_eq_top** 是 Mathlib 中的一个定理，位于命名
空间 `AlgebraicGeometry.HasAffineProperty`。
形式化陈述：∀ {P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme} {Q : Alge
braicGeometry.AffineTargetMorphismProperty}   [AlgebraicGeometry.HasAffineProper
ty P Q] {X Y : AlgebraicGeometry.Scheme} {f : X ⟶ Y} {ι : Sort u_1}   (U : ι → ↑
Y.affineOpens), ⨆ i, ↑(U i) = ⊤ → (P f ↔ ∀ (i : ι), Q (f ∣_ ↑(U i)))
参数：U : ι → ↑Y.affineOpens；U i；P f ↔ ∀ (i : ι), Q (f ∣_ ↑(U i))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.instIsAffineToSchemeValOpensMemSetAffineOpens`：∀ {Y : 
AlgebraicGeometry.Scheme} (U : ↑Y.affineOpens), AlgebraicGeometry.IsAffine ↑↑U
· 使用定理 `AlgebraicGeometry.HasAffineProperty.restrict`：∀ {P : CategoryTheory.Morp
hismProperty AlgebraicGeometry.Scheme} {Q : AlgebraicGeometry.AffineTargetMorphi
smProperty}   [AlgebraicGeometry.H…
· 使用定理 `AlgebraicGeometry.HasAffineProperty.of_iSup_eq_top`：∀ {P : CategoryTheor
y.MorphismProperty AlgebraicGeometry.Scheme} {Q : AlgebraicGeometry.AffineTarget
MorphismProperty}   [AlgebraicGeometry.H…
-/
theorem iff_of_iSup_eq_top
    {ι} (U : ι → Y.affineOpens) (hU : ⨆ i, (U i : Y.Opens) = ⊤) :
    P f ↔ ∀ i, Q (f ∣_ U i) :=
  ⟨fun H _ ↦ restrict H _, fun H ↦ HasAffineProperty.of_iSup_eq_top U hU H⟩
/-
**AlgebraicGeometry.HasAffineProperty.of_openCover** 是 Mathlib 中的一个定理，位于命名空间 `Al
gebraicGeometry.HasAffineProperty`。
形式化陈述：∀ {P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme} {Q : Alge
braicGeometry.AffineTargetMorphismProperty}   [AlgebraicGeometry.HasAffineProper
ty P Q] {X Y : AlgebraicGeometry.Scheme} {f : X ⟶ Y} (𝒰 : Y.OpenCover)   [inst :
 ∀ (i : 𝒰.I₀), AlgebraicGeometry.IsAffine (𝒰.X i)],   (∀ (i : 𝒰.toPreZeroHyperco
ver.1), Q (AlgebraicGeometry.Scheme.Cover.pullbackHom 𝒰 f i)) → P f
参数：𝒰 : Y.OpenCover；i : 𝒰.I₀；𝒰.X i；∀ (i : 𝒰.toPreZeroHypercover.1), Q (AlgebraicG
eometry.Scheme.Cover.pullbackHom 𝒰 f i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.instIsStableUnderBaseChangePrecoverageOfIsJoint
lySurjectivePreservingOfIsStableUnderBaseChange`：∀ (P : CategoryTheory.MorphismP
roperty AlgebraicGeometry.Scheme)   [AlgebraicGeometry.Scheme.IsJointlySurjectiv
ePreserving P] [P.IsStableUnd…
· 使用定理 `AlgebraicGeometry.Scheme.instIsJointlySurjectivePreservingIsOpenImmersio
n`：AlgebraicGeometry.Scheme.IsJointlySurjectivePreserving AlgebraicGeometry.IsOp
enImmersion
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `AlgebraicGeometry.HasAffineProperty.of_iSup_eq_top`：∀ {P : CategoryTheor
y.MorphismProperty AlgebraicGeometry.Scheme} {Q : AlgebraicGeometry.AffineTarget
MorphismProperty}   [AlgebraicGeometry.H…
· 使用定理 `AlgebraicGeometry.Scheme.instIsOpenImmersionF`：∀ {X : AlgebraicGeometry.
Scheme} (𝒰 : X.OpenCover) (i : 𝒰.I₀), AlgebraicGeometry.IsOpenImmersion (𝒰.f i)
· 使用定理 `AlgebraicGeometry.isAffineOpen_opensRange`：isAffineOpen_opensRange {X Y 
: Scheme} [IsAffine X] (f : X ⟶ Y) [H : IsOpenImmersion f] : IsAffineOpen f.open
sRange
· 使用定理 `AlgebraicGeometry.Scheme.OpenCover.iSup_opensRange`：∀ {X : AlgebraicGeom
etry.Scheme} (𝒰 : X.OpenCover), ⨆ i, AlgebraicGeometry.Scheme.Hom.opensRange (𝒰.
f i) = ⊤
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `AlgebraicGeometry.instIsAffineToSchemeValOpensMemSetAffineOpens`：∀ {Y : 
AlgebraicGeometry.Scheme} (U : ↑Y.affineOpens), AlgebraicGeometry.IsAffine ↑↑U
· 使用定理 `AlgebraicGeometry.IsAffine.of_isIso`：∀ {X Y : AlgebraicGeometry.Scheme} 
(f : X ⟶ Y) [CategoryTheory.IsIso f] [h : AlgebraicGeometry.IsAffine Y],   Algeb
raicGeometry.IsAffine X
· 使用定理 `CategoryTheory.Arrow.isIso_right`：∀ {T : Type u} [inst : CategoryTheory.
Category.{v, u} T] {f g : CategoryTheory.Arrow T} (sq : g ⟶ f)   [CategoryTheory
.IsIso sq], CategoryTh…
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `AlgebraicGeometry.AffineTargetMorphismProperty.arrow_mk_iso_iff`：arrow_m
k_iso_iff (P : AffineTargetMorphismProperty) [P.toProperty.RespectsIso] {X Y X' 
Y' : Scheme} {f : X ⟶ Y} {f' : X' ⟶ Y'} (e : Arrow.mk…
· 使用定理 `AlgebraicGeometry.AffineTargetMorphismProperty.IsLocal.respectsIso`：∀ {P
 : AlgebraicGeometry.AffineTargetMorphismProperty} [self : P.IsLocal], P.toPrope
rty.RespectsIso
· 使用定理 `AlgebraicGeometry.HasAffineProperty.isLocal_affineProperty`：∀ (P : Categ
oryTheory.MorphismProperty AlgebraicGeometry.Scheme)   {Q : outParam AlgebraicGe
ometry.AffineTargetMorphismProperty} [self : Alg…
-/
theorem of_openCover
    (𝒰 : Y.OpenCover) [∀ i, IsAffine (𝒰.X i)] (h𝒰 : ∀ i, Q (𝒰.pullbackHom f i)) :
    P f :=
  letI := isLocal_affineProperty P
  of_iSup_eq_top
    (fun i ↦ ⟨_, isAffineOpen_opensRange (𝒰.f i)⟩) 𝒰.iSup_opensRange
    (fun i ↦ (Q.arrow_mk_iso_iff (morphismRestrictOpensRange f _)).mpr (h𝒰 i))
/-
**AlgebraicGeometry.HasAffineProperty.iff_of_openCover** 是 Mathlib 中的一个定理，位于命名空间
 `AlgebraicGeometry.HasAffineProperty`。
形式化陈述：∀ {P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme} {Q : Alge
braicGeometry.AffineTargetMorphismProperty}   [AlgebraicGeometry.HasAffineProper
ty P Q] {X Y : AlgebraicGeometry.Scheme} {f : X ⟶ Y} (𝒰 : Y.OpenCover)   [inst :
 ∀ (i : 𝒰.I₀), AlgebraicGeometry.IsAffine (𝒰.X i)],   P f ↔ ∀ (i : 𝒰.toPreZeroHy
percover.1), Q (AlgebraicGeometry.Scheme.Cover.pullbackHom 𝒰 f i)
参数：𝒰 : Y.OpenCover；i : 𝒰.I₀；𝒰.X i；i : 𝒰.toPreZeroHypercover.1；AlgebraicGeometry.
Scheme.Cover.pullbackHom 𝒰 f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.HasAffineProperty.isLocal_affineProperty`：∀ (P : Categ
oryTheory.MorphismProperty AlgebraicGeometry.Scheme)   {Q : outParam AlgebraicGe
ometry.AffineTargetMorphismProperty} [self : Alg…
· 使用定理 `AlgebraicGeometry.Scheme.instIsStableUnderBaseChangePrecoverageOfIsJoint
lySurjectivePreservingOfIsStableUnderBaseChange`：∀ (P : CategoryTheory.MorphismP
roperty AlgebraicGeometry.Scheme)   [AlgebraicGeometry.Scheme.IsJointlySurjectiv
ePreserving P] [P.IsStableUnd…
· 使用定理 `AlgebraicGeometry.Scheme.instIsJointlySurjectivePreservingIsOpenImmersio
n`：AlgebraicGeometry.Scheme.IsJointlySurjectivePreserving AlgebraicGeometry.IsOp
enImmersion
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `AlgebraicGeometry.Scheme.instIsOpenImmersionF`：∀ {X : AlgebraicGeometry.
Scheme} (𝒰 : X.OpenCover) (i : 𝒰.I₀), AlgebraicGeometry.IsOpenImmersion (𝒰.f i)
· 使用定理 `AlgebraicGeometry.isAffineOpen_opensRange`：isAffineOpen_opensRange {X Y 
: Scheme} [IsAffine X] (f : X ⟶ Y) [H : IsOpenImmersion f] : IsAffineOpen f.open
sRange
· 使用定理 `AlgebraicGeometry.instIsAffineToSchemeValOpensMemSetAffineOpens`：∀ {Y : 
AlgebraicGeometry.Scheme} (U : ↑Y.affineOpens), AlgebraicGeometry.IsAffine ↑↑U
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.HasAffineProperty.iff_of_iSup_eq_top`：∀ {P : CategoryT
heory.MorphismProperty AlgebraicGeometry.Scheme} {Q : AlgebraicGeometry.AffineTa
rgetMorphismProperty}   [AlgebraicGeometry.H…
· 使用定理 `AlgebraicGeometry.Scheme.OpenCover.iSup_opensRange`：∀ {X : AlgebraicGeom
etry.Scheme} (𝒰 : X.OpenCover), ⨆ i, AlgebraicGeometry.Scheme.Hom.opensRange (𝒰.
f i) = ⊤
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `AlgebraicGeometry.AffineTargetMorphismProperty.arrow_mk_iso_iff`：arrow_m
k_iso_iff (P : AffineTargetMorphismProperty) [P.toProperty.RespectsIso] {X Y X' 
Y' : Scheme} {f : X ⟶ Y} {f' : X' ⟶ Y'} (e : Arrow.mk…
· 使用定理 `AlgebraicGeometry.AffineTargetMorphismProperty.IsLocal.respectsIso`：∀ {P
 : AlgebraicGeometry.AffineTargetMorphismProperty} [self : P.IsLocal], P.toPrope
rty.RespectsIso
-/
theorem iff_of_openCover (𝒰 : Y.OpenCover) [∀ i, IsAffine (𝒰.X i)] :
    P f ↔ ∀ i, Q (𝒰.pullbackHom f i) := by
  let := isLocal_affineProperty P
  rw [iff_of_iSup_eq_top (P := P)
    (fun i ↦ ⟨_, isAffineOpen_opensRange _⟩) 𝒰.iSup_opensRange]
  exact forall_congr' fun i ↦ Q.arrow_mk_iso_iff
    (morphismRestrictOpensRange f _)
/-
**AlgebraicGeometry.HasAffineProperty.iff_of_isAffine** 是 Mathlib 中的一个定理，位于命名空间 
`AlgebraicGeometry.HasAffineProperty`。
形式化陈述：∀ {P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme} {Q : Alge
braicGeometry.AffineTargetMorphismProperty}   [AlgebraicGeometry.HasAffineProper
ty P Q] {X Y : AlgebraicGeometry.Scheme} {f : X ⟶ Y}   [inst : AlgebraicGeometry
.IsAffine Y], P f ↔ Q f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.HasAffineProperty.isLocal_affineProperty`：∀ (P : Categ
oryTheory.MorphismProperty AlgebraicGeometry.Scheme)   {Q : outParam AlgebraicGe
ometry.AffineTargetMorphismProperty} [self : Alg…
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toContainsIdentities`：∀
 {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheory.Morp
hismProperty C}   [self : W.IsMultiplicative], W.ContainsId…
· 使用定理 `AlgebraicGeometry.Scheme.instIsStableUnderBaseChangePrecoverageOfIsJoint
lySurjectivePreservingOfIsStableUnderBaseChange`：∀ (P : CategoryTheory.MorphismP
roperty AlgebraicGeometry.Scheme)   [AlgebraicGeometry.Scheme.IsJointlySurjectiv
ePreserving P] [P.IsStableUnd…
· 使用定理 `AlgebraicGeometry.Scheme.instIsJointlySurjectivePreservingIsOpenImmersio
n`：AlgebraicGeometry.Scheme.IsJointlySurjectivePreserving AlgebraicGeometry.IsOp
enImmersion
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `AlgebraicGeometry.instIsAffineXSchemeCoverOfIsIsoIsOpenImmersionId`：∀ {X
 : AlgebraicGeometry.Scheme} [AlgebraicGeometry.IsAffine X]   (i : (AlgebraicGeo
metry.Scheme.coverOfIsIso (CategoryTheory.CategoryStruct…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.HasAffineProperty.iff_of_openCover`：∀ {P : CategoryThe
ory.MorphismProperty AlgebraicGeometry.Scheme} {Q : AlgebraicGeometry.AffineTarg
etMorphismProperty}   [AlgebraicGeometry.H…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…
· 使用定理 `AlgebraicGeometry.AffineTargetMorphismProperty.cancel_left_of_respectsIs
o`：cancel_left_of_respectsIso (P : AffineTargetMorphismProperty) [P.toProperty.R
espectsIso] {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso f] …
· 使用定理 `AlgebraicGeometry.AffineTargetMorphismProperty.IsLocal.respectsIso`：∀ {P
 : AlgebraicGeometry.AffineTargetMorphismProperty} [self : P.IsLocal], P.toPrope
rty.RespectsIso
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem iff_of_isAffine [IsAffine Y] : P f ↔ Q f := by
  let := isLocal_affineProperty P
  rw [iff_of_openCover (P := P) (Scheme.coverOfIsIso.{0} (𝟙 Y))]
  trans Q (pullback.snd f (𝟙 _))
  · exact ⟨fun H => H PUnit.unit, fun H _ => H⟩
  rw [← Category.comp_id (pullback.snd _ _), ← pullback.condition,
    Q.cancel_left_of_respectsIso]

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.HasAffineProperty.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeome
try.HasAffineProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 900) : IsZariskiLocalAtTarget P := by
  let := isLocal_affineProperty P
  apply IsZariskiLocalAtTarget.mk'
  · rw [eq_targetAffineLocally P]
    intro X Y f U H V
    rw [Q.arrow_mk_iso_iff (morphismRestrictRestrict f _ _)]
    exact H ⟨_, V.2.image_of_isOpenImmersion (Y.ofRestrict _)⟩
  · rintro X Y f ι U hU H
    let 𝒰 := Y.openCoverOfIsOpenCover U hU
    apply of_openCover 𝒰.affineRefinement.openCover
    rintro ⟨i, j⟩
    have : P (𝒰.pullbackHom f i) := by
      refine (P.arrow_mk_iso_iff
        (morphismRestrictEq _ ?_ ≪≫ morphismRestrictOpensRange f (𝒰.f i))).mp (H i)
      exact (Scheme.Opens.opensRange_ι _).symm
    rw [← Q.cancel_left_of_respectsIso (𝒰.pullbackCoverAffineRefinementObjIso f _).inv,
      𝒰.pullbackCoverAffineRefinementObjIso_inv_pullbackHom]
    exact of_isPullback (.of_hasPullback _ _) this

open AffineTargetMorphismProperty in
/-
**AlgebraicGeometry.HasAffineProperty.iff** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGe
ometry.HasAffineProperty`。
形式化陈述：∀ {P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme} {Q : Alge
braicGeometry.AffineTargetMorphismProperty},   AlgebraicGeometry.HasAffineProper
ty P Q ↔     AlgebraicGeometry.IsZariskiLocalAtTarget P ∧ Q = AlgebraicGeometry.
AffineTargetMorphismProperty.of P
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.HasAffineProperty.instIsZariskiLocalAtTarget`：∀ {P : C
ategoryTheory.MorphismProperty AlgebraicGeometry.Scheme} {Q : AlgebraicGeometry.
AffineTargetMorphismProperty}   [AlgebraicGeometry.H…
· 使用引理 `AlgebraicGeometry.AffineTargetMorphismProperty.ext`：ext {P Q : AffineTar
getMorphismProperty} (H : forall ⦃X Y : Scheme⦄ (f : X ⟶ Y) [IsAffine Y], P f ↔ 
Q f) : P = Q
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `AlgebraicGeometry.HasAffineProperty.iff_of_isAffine`：∀ {P : CategoryTheo
ry.MorphismProperty AlgebraicGeometry.Scheme} {Q : AlgebraicGeometry.AffineTarge
tMorphismProperty}   [AlgebraicGeometry.H…
· 使用定理 `AlgebraicGeometry.HasAffineProperty.of_isZariskiLocalAtTarget`：∀ (P : Ca
tegoryTheory.MorphismProperty AlgebraicGeometry.Scheme) [AlgebraicGeometry.IsZar
iskiLocalAtTarget P],   AlgebraicGeometry.HasAffine…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
protected theorem iff {P : MorphismProperty Scheme} {Q : AffineTargetMorphismProperty} :
    HasAffineProperty P Q ↔ IsZariskiLocalAtTarget P ∧ Q = of P :=
  ⟨fun _ ↦ ⟨inferInstance, ext fun _ _ _ ↦ iff_of_isAffine.symm⟩,
    fun ⟨_, e⟩ ↦ e ▸ of_isZariskiLocalAtTarget P⟩

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.HasAffineProperty.pullback_fst_of_right** 是 Mathlib 中的一个定理，位
于命名空间 `AlgebraicGeometry.HasAffineProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem pullback_fst_of_right (hP' : Q.IsStableUnderBaseChange)
    {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [IsAffine S] (H : Q g) :
    P (pullback.fst f g) := by
  let := isLocal_affineProperty P
  rw [iff_of_openCover (P := P) X.affineCover]
  intro i
  let e := pullbackSymmetry _ _ ≪≫ pullbackRightPullbackFstIso f g (X.affineCover.f i)
  have : e.hom ≫ pullback.fst _ _ = X.affineCover.pullbackHom (pullback.fst _ _) i := by
    simp [e, Scheme.Cover.pullbackHom]
  rw [← this, Q.cancel_left_of_respectsIso]
  apply hP' (.of_hasPullback _ _)
  exact H

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.HasAffineProperty.isStableUnderBaseChange** 是 Mathlib 中的一个定理
，位于命名空间 `AlgebraicGeometry.HasAffineProperty`。
形式化陈述：∀ {P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme} {Q : Alge
braicGeometry.AffineTargetMorphismProperty}   [AlgebraicGeometry.HasAffineProper
ty P Q], Q.IsStableUnderBaseChange → P.IsStableUnderBaseChange
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsStableUnderBaseChange.mk'`：∀ {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.MorphismProper
ty C} [P.RespectsIso],   (∀ (X Y S : C) (f : X ⟶ …
· 使用定理 `CategoryTheory.MorphismProperty.IsLocalAtTarget.toRespects`：∀ {C : Type 
u} {inst : CategoryTheory.Category.{v, u} C} {P : CategoryTheory.MorphismPropert
y C}   (K : CategoryTheory.Precoverage C) [self …
· 使用定理 `AlgebraicGeometry.HasAffineProperty.instIsZariskiLocalAtTarget`：∀ {P : C
ategoryTheory.MorphismProperty AlgebraicGeometry.Scheme} {Q : AlgebraicGeometry.
AffineTargetMorphismProperty}   [AlgebraicGeometry.H…
· 使用定理 `AlgebraicGeometry.Scheme.instIsStableUnderBaseChangePrecoverageOfIsJoint
lySurjectivePreservingOfIsStableUnderBaseChange`：∀ (P : CategoryTheory.MorphismP
roperty AlgebraicGeometry.Scheme)   [AlgebraicGeometry.Scheme.IsJointlySurjectiv
ePreserving P] [P.IsStableUnd…
· 使用定理 `AlgebraicGeometry.Scheme.instIsJointlySurjectivePreservingIsOpenImmersio
n`：AlgebraicGeometry.Scheme.IsJointlySurjectivePreserving AlgebraicGeometry.IsOp
enImmersion
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `CategoryTheory.Precoverage.ZeroHypercover.instHasPullbackFOfHasPullbacks
Presieve₀_1`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} 
(E : CategoryTheory.PreZeroHypercover X) (f : Y ⟶ X)   [E.presieve₀.HasPu…
· 使用定理 `CategoryTheory.Precoverage.ZeroHypercover.instHasPullbacksPresieve₀OfHas
Pullbacks`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (K : Categor
yTheory.Precoverage C) [K.HasPullbacks] {X Y : C}   (E : K.ZeroHypercov…
· 使用定理 `AlgebraicGeometry.Scheme.instHasPullbacksPrecoverageOfHasPullbacks`：∀ (P
 : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme) [P.HasPullbacks],  
 (AlgebraicGeometry.Scheme.precoverage P).HasPullbacks
· 使用定理 `AlgebraicGeometry.Scheme.instHasPullbacksIsOpenImmersion`：AlgebraicGeome
try.IsOpenImmersion.HasPullbacks
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MorphismProperty.iff_of_zeroHypercover_target`：∀ {C : Typ
e u} [inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.MorphismPrope
rty C}   {K : CategoryTheory.Precoverage C} [P.IsL…
· 使用定理 `CategoryTheory.Limits.hasPullback_symmetry`：hasPullback_symmetry [HasPul
lback f g] : HasPullback g f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.pullback.map_isIso`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {W X Y Z S T : C} (f₁ : W ⟶ S) (f₂ : X ⟶ S)   [inst_1
 : CategoryTheory.Limits.HasPu…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.pullbackRightPullbackFstIso_inv_fst`：pullbackRight
PullbackFstIso_inv_fst : (pullbackRightPullbackFstIso f g f').inv ≫ pullback.fst
 f' (pullback.fst f g) = pullback.fst (f' ≫ f) …
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PullbackCone.mk_π_app`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {W : C} (fst :
 W ⟶ X)   (snd : W ⟶ Y)   (eq :  …
· 使用定理 `CategoryTheory.Limits.pullbackRightPullbackFstIso_hom_fst`：pullbackRight
PullbackFstIso_hom_fst : (pullbackRightPullbackFstIso f g f').hom ≫ pullback.fst
 (f' ≫ f) g = pullback.fst f' (pullback.fst f g…
· 使用定理 `CategoryTheory.Limits.pullbackSymmetry_hom_comp_fst`：pullbackSymmetry_ho
m_comp_fst [HasPullback f g] : (pullbackSymmetry f g).hom ≫ pullback.fst g f = p
ullback.snd f g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.MorphismProperty.cancel_left_of_respectsIso`：cancel_left_
of_respectsIso (P : MorphismProperty C) [hP : RespectsIso P] {X Y Z : C} (f : X 
⟶ Y) (g : Y ⟶ Z) [IsIso f] : P (f ≫ g) ↔ P g
（共 40 条，此处仅展示前 30 条）
-/
theorem isStableUnderBaseChange (hP' : Q.IsStableUnderBaseChange) :
    P.IsStableUnderBaseChange :=
  MorphismProperty.IsStableUnderBaseChange.mk'
    (fun X Y S f g _ H => by
      rw [P.iff_of_zeroHypercover_target (S.affineCover.pullback₁ f)]
      intro i
      let e : pullback (pullback.fst f g) ((S.affineCover.pullback₁ f).f i) ≅
          _ := by
        refine pullbackSymmetry _ _ ≪≫ pullbackRightPullbackFstIso f g _ ≪≫ ?_ ≪≫
          (pullbackRightPullbackFstIso (S.affineCover.f i) g
            (pullback.snd f (S.affineCover.f i))).symm
        exact asIso
          (pullback.map _ _ _ _ (𝟙 _) (𝟙 _) (𝟙 _) (by simpa using! pullback.condition) (by simp))
      have : e.hom ≫ pullback.fst _ _ =
          pullback.snd (pullback.fst f g) ((S.affineCover.pullback₁ f).f i) := by
        simp [e]
      rw [← this, P.cancel_left_of_respectsIso]
      apply HasAffineProperty.pullback_fst_of_right hP'
      let := isLocal_affineProperty P
      rw [← pullbackSymmetry_hom_comp_snd, Q.cancel_left_of_respectsIso]
      apply of_isPullback (.of_hasPullback _ _) H)
/-
**AlgebraicGeometry.HasAffineProperty.isZariskiLocalAtSource** 是 Mathlib 中的一个定理，
位于命名空间 `AlgebraicGeometry.HasAffineProperty`。
形式化陈述：∀ {P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme} {Q : Alge
braicGeometry.AffineTargetMorphismProperty}   [AlgebraicGeometry.HasAffineProper
ty P Q],   (∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [inst : AlgebraicGeom
etry.IsAffine Y] (𝒰 : X.OpenCover),       Q f ↔ ∀ (i : 𝒰.I₀), Q (CategoryTheory.
CategoryStruct.comp (𝒰.f i) f)) →     AlgebraicGeometry.IsZariskiLocalAtSource P
参数：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [inst : AlgebraicGeometry.IsAf
fine Y] (𝒰 : X.OpenCover),       Q f ↔ ∀ (i : 𝒰.I₀), Q (CategoryTheory.CategoryS
truct.comp (𝒰.f i) f)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.IsLocalAtSource.mk_of_small`：mk_of_small
 [P.RespectsIso] [Precoverage.Small.{w} K] (h₁ : forall {X Y : C} {f : X ⟶ Y} (𝒰
 : Precoverage.ZeroHypercover.{max u v} K X), P f…
· 使用定理 `CategoryTheory.MorphismProperty.IsLocalAtTarget.toRespects`：∀ {C : Type 
u} {inst : CategoryTheory.Category.{v, u} C} {P : CategoryTheory.MorphismPropert
y C}   (K : CategoryTheory.Precoverage C) [self …
· 使用定理 `AlgebraicGeometry.HasAffineProperty.instIsZariskiLocalAtTarget`：∀ {P : C
ategoryTheory.MorphismProperty AlgebraicGeometry.Scheme} {Q : AlgebraicGeometry.
AffineTargetMorphismProperty}   [AlgebraicGeometry.H…
· 使用定理 `AlgebraicGeometry.Scheme.instSmallPrecoverage`：∀ {P : CategoryTheory.Mor
phismProperty AlgebraicGeometry.Scheme}, (AlgebraicGeometry.Scheme.precoverage P
).Small
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `AlgebraicGeometry.IsZariskiLocalAtTarget.iff_of_iSup_eq_top`：iff_of_iSup
_eq_top {ι} (U : ι -> Y.Opens) (hU : iSup U = ⊤) : P f ↔ forall i, P (f ∣_ U i)
· 使用定理 `AlgebraicGeometry.iSup_affineOpens_eq_top`：iSup_affineOpens_eq_top (X : 
Scheme) : ⨆ i : X.affineOpens, (i : X.Opens) = ⊤
· 使用定理 `AlgebraicGeometry.instIsAffineToSchemeValOpensMemSetAffineOpens`：∀ {Y : 
AlgebraicGeometry.Scheme} (U : ↑Y.affineOpens), AlgebraicGeometry.IsAffine ↑↑U
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.morphismRestrict_comp`：morphismRestrict_comp {X Y Z : 
Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (U : Opens Z) : (f ≫ g) ∣_ U = f ∣_ g ⁻¹ᵁ U 
≫ g ∣_ U
· 使用定理 `AlgebraicGeometry.Scheme.instIsOpenImmersionF`：∀ {X : AlgebraicGeometry.
Scheme} (𝒰 : X.OpenCover) (i : 𝒰.I₀), AlgebraicGeometry.IsOpenImmersion (𝒰.f i)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
lemma isZariskiLocalAtSource
    (H : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffine Y] (𝒰 : Scheme.OpenCover.{u} X),
        Q f ↔ ∀ i, Q (𝒰.f i ≫ f)) : IsZariskiLocalAtSource P := by
  refine .mk_of_small (fun {X Y f} 𝒰 hf ↦ ?_) (fun {X Y f} 𝒰 hf ↦ ?_) <;>
  simp_rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top _ (iSup_affineOpens_eq_top Y),
      HasAffineProperty.iff_of_isAffine, morphismRestrict_comp] at hf ⊢
  · intro i U
    let 𝒰' : X.OpenCover := (Scheme.Cover.ulift 𝒰).add (𝒰.f i)
    exact (H (f ∣_ U.1) (𝒰'.restrict _)).mp (hf _) none
  · intro U
    rw [H (f ∣_ U.1) (Scheme.OpenCover.restrict 𝒰 _)]
    intro i
    exact hf _ _

end HasAffineProperty

end targetAffineLocally

open MorphismProperty

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.hasOfPostcompProperty_isOpenImmersion_of_morphismRestrict** 
是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry`。
形式化陈述：∀ (P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme) [P.Respec
tsIso],   (∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) (U : Y.Opens), P f → P
 (f ∣_ U)) →     P.HasOfPostcompProperty AlgebraicGeometry.IsOpenImmersion
参数：P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme；∀ {X Y : Algebra
icGeometry.Scheme} (f : X ⟶ Y) (U : Y.Opens), P f → P (f ∣_ U)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.Scheme.Hom.preimage_opensRange`：preimage_opensRange {X
 Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] : f ⁻¹ᵁ f.opensRange = ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι`：∀ {X : AlgebraicGeo
metry.Scheme} (U : X.Opens), AlgebraicGeometry.IsOpenImmersion U.ι
· 使用引理 `AlgebraicGeometry.Scheme.Opens.range_ι`：range_ι : Set.range U.ι = U
· 使用定理 `AlgebraicGeometry.Scheme.Hom.coe_opensRange`：∀ {X Y : AlgebraicGeometry.
Scheme} (f : X ⟶ Y) [H : AlgebraicGeometry.IsOpenImmersion f],   ↑(AlgebraicGeom
etry.Scheme.Hom.opensRange f) = S…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq_hom_fac`：isoOfRangeEq_hom
_fac {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) [IsOpenImmersion f] [IsOpenImm
ersion g] (e : Set.range f = Set.range g) : …
· 使用定理 `AlgebraicGeometry.morphismRestrict_ι`：morphismRestrict_ι {X Y : Scheme.{
u}} (f : X ⟶ Y) (U : Y.Opens) : f ∣_ U ≫ U.ι = (f ⁻¹ᵁ U).ι ≫ f
· 使用定理 `AlgebraicGeometry.Scheme.isoOfEq_inv_ι_assoc`：∀ (X : AlgebraicGeometry.S
cheme) {U V : X.Opens} (e : U = V) {Z : AlgebraicGeometry.Scheme} (h : X ⟶ Z),  
 CategoryTheory.CategoryStruct.com…
· 使用定理 `AlgebraicGeometry.Scheme.toIso_inv_ι_assoc`：∀ (X : AlgebraicGeometry.Sch
eme) {Z : AlgebraicGeometry.Scheme} (h : X ⟶ Z),   CategoryTheory.CategoryStruct
.comp X.topIso.inv (CategoryTheo…
· 使用定理 `CategoryTheory.MorphismProperty.cancel_left_of_respectsIso`：cancel_left_
of_respectsIso (P : MorphismProperty C) [hP : RespectsIso P] {X Y Z : C} (f : X 
⟶ Y) (g : Y ⟶ Z) [IsIso f] : P (f ≫ g) ↔ P g
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `CategoryTheory.MorphismProperty.cancel_right_of_respectsIso`：cancel_righ
t_of_respectsIso (P : MorphismProperty C) [hP : RespectsIso P] {X Y Z : C} (f : 
X ⟶ Y) (g : Y ⟶ Z) [IsIso g] : P (f ≫ g) ↔ P f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
-/
lemma hasOfPostcompProperty_isOpenImmersion_of_morphismRestrict (P : MorphismProperty Scheme)
    [P.RespectsIso] (H : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens), P f → P (f ∣_ U)) :
    P.HasOfPostcompProperty @IsOpenImmersion where
  of_postcomp {X Y Z} f g hg hfg := by
    have : (f ≫ g) ⁻¹ᵁ g.opensRange = ⊤ := by simp
    have : f = X.topIso.inv ≫ (X.isoOfEq this).inv ≫ (f ≫ g) ∣_ g.opensRange ≫
        (IsOpenImmersion.isoOfRangeEq g.opensRange.ι g (by simp)).hom := by
      simp [← cancel_mono g]
    simp_rw [this, cancel_left_of_respectsIso (P := P), cancel_right_of_respectsIso (P := P)]
    exact H _ _ hfg
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (P : MorphismProperty Scheme) [P.IsStableUnderBaseChange] :
    P.HasOfPostcompProperty @IsOpenImmersion :=
  HasOfPostcompProperty.of_le P (.monomorphisms Scheme) (fun _ _ f _ ↦ inferInstanceAs (Mono f))

end AlgebraicGeometry

