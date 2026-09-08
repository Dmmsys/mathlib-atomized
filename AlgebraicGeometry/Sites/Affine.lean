/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten, Joël Riou
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Small
public import Mathlib.CategoryTheory.Sites.DenseSubsite.OneHypercoverDense

/-!
# Small affine site induced by a morphism property

Let `P` be a morphism property of schemes and `S` be a scheme. In this file we study the small
affine `P`-site of `S`: its objects are rings `R` with a structure morphism `Spec R ⟶ S` that
satisfies `P`.

We don't make a separate definition for this site, but use
`CategoryTheory.MorphismProperty.CostructuredArrow P ⊤ Scheme.Spec S`.

Under suitable assumptions on `P`, the lemmas here can be used to show that the small affine
`P`-site has the same category of sheaves as the general small `P`-site. If `P` implies
finitely generated, the small affine `P`-site is essentially small, so in particular
this can be used to show that the `P`-site admits sheafification. For an example,
see the file `Mathlib.AlgebraicGeometry.Sites.AffineEtale`.
-/

@[expose] public section

universe u

open CategoryTheory Opposite Limits MorphismProperty

namespace AlgebraicGeometry.Scheme

variable {S : Scheme.{u}}

/-- Construct an object of affine `P`-schemes over `S` by giving a morphism `Spec R ⟶ S`. -/
@[simps! hom left]
/-
**AlgebraicGeometry.Scheme.affineOverMk** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeom
etry.Scheme`。
形式化陈述：affineOverMk {P : MorphismProperty Scheme.{u}} {R : CommRingCat.{u}} (f : 
Spec R ⟶ S) (hf : P f) : P.CostructuredArrow ⊤ Scheme.Spec S
参数：f : Spec R ⟶ S；hf : P f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct an object of affine `P`-schemes over `S` by giving a morphism `Spec R 
⟶ S`.
-/
noncomputable def affineOverMk {P : MorphismProperty Scheme.{u}} {R : CommRingCat.{u}}
    (f : Spec R ⟶ S) (hf : P f) :
    P.CostructuredArrow ⊤ Scheme.Spec S :=
  .mk ⊤ f hf

variable (P : MorphismProperty Scheme.{u}) [P.IsMultiplicative] [IsZariskiLocalAtSource P]
  [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The `Spec` functor from affine `P`-schemes over `S` to `P`-schemes over `S` is dense
if `P` is local at the source. -/
/-
**AlgebraicGeometry.Scheme.isCoverDense_toOver_Spec** 是 Mathlib 中的一个实例，位于命名空间 `A
lgebraicGeometry.Scheme`。
形式化陈述：isCoverDense_toOver_Spec : (CostructuredArrow.toOver P Scheme.Spec S).IsCo
verDense (S.smallGrothendieckTopology P) where is_cover U
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.instTop`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C], ⊤.IsMultiplicative
· 使用定理 `AlgebraicGeometry.Scheme.isJointlySurjectivePreserving`：∀ (P : CategoryT
heory.MorphismProperty AlgebraicGeometry.Scheme),   AlgebraicGeometry.Scheme.IsJ
ointlySurjectivePreserving P
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.Scheme.mem_smallGrothendieckTopology`：mem_smallGrothen
dieckTopology [P.HasOfPostcompProperty P] (X : P.Over ⊤ S) (R : Sieve X) : R in 
S.smallGrothendieckTopology P X ↔ exists (𝒰 …
· 使用定理 `CategoryTheory.MorphismProperty.IsLocalAtSource.toRespects`：∀ {C : Type 
u} {inst : CategoryTheory.Category.{v, u} C} {P : CategoryTheory.MorphismPropert
y C}   (K : CategoryTheory.Precoverage C) [self …
· 使用定理 `AlgebraicGeometry.Scheme.instJointlySurjectivePrecoverage`：∀ {P : Catego
ryTheory.MorphismProperty AlgebraicGeometry.Scheme},   AlgebraicGeometry.Scheme.
JointlySurjective (AlgebraicGeometry.Scheme.pre…
· 使用引理 `AlgebraicGeometry.IsZariskiLocalAtSource.of_isOpenImmersion`：of_isOpenIm
mersion [P.ContainsIdentities] [IsOpenImmersion f] : P f
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toContainsIdentities`：∀
 {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheory.Morp
hismProperty C}   [self : W.IsMultiplicative], W.ContainsId…
· 使用定理 `AlgebraicGeometry.Scheme.instIsOpenImmersionF`：∀ {X : AlgebraicGeometry.
Scheme} (𝒰 : X.OpenCover) (i : 𝒰.I₀), AlgebraicGeometry.IsOpenImmersion (𝒰.f i)
· 使用引理 `CategoryTheory.MorphismProperty.comp_mem`：comp_mem (W : MorphismProperty
 C) [W.IsStableUnderComposition] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : W f) 
(hg : W g) : W (f ≫ g)
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toIsStableUnderComposit
ion`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheor
y.MorphismProperty C}   [self : W.IsMultiplicative], W.IsStableUn…
· 使用定理 `AlgebraicGeometry.Scheme.Cover.map_prop`：∀ {X : AlgebraicGeometry.Scheme
} {P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme}   (𝒰 : Algebrai
cGeometry.Scheme.Cover (Algeb…
· 使用定理 `CategoryTheory.MorphismProperty.Comma.prop`：∀ {A : Type u_1} [inst : Cat
egoryTheory.Category.{v_1, u_1} A] {B : Type u_2}   [inst_1 : CategoryTheory.Cat
egory.{v_2, u_2} B] {T : Type u_…
· 使用定理 `CategoryTheory.Sieve.coverByImage.eq_1`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] {D : Type u_2}   [inst_1 : CategoryTheory.Categor
y.{v_2, u_2} D] (G : Categor…
· 使用定理 `AlgebraicGeometry.Scheme.local_affine`：∀ (self : AlgebraicGeometry.Schem
e) (x : ↑self.toTopCat),   ∃ U R, Nonempty (self.restrict ⋯ ≅ AlgebraicGeometry.
Spec.toLocallyRingedSpace.o…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `trivial`：True

--- 原说明 ---
The `Spec` functor from affine `P`-schemes over `S` to `P`-schemes over `S` is d
ense
if `P` is local at the source.
-/
instance isCoverDense_toOver_Spec :
    (CostructuredArrow.toOver P Scheme.Spec S).IsCoverDense (S.smallGrothendieckTopology P) where
  is_cover U := by
    rw [Scheme.mem_smallGrothendieckTopology]
    let 𝒰 : Cover.{u} (precoverage P) U.left :=
      U.left.affineCover.changeProp
      (fun _ ↦ IsZariskiLocalAtSource.of_isOpenImmersion _)
    let _ (i : 𝒰.I₀) : (𝒰.X i).Over S := ⟨𝒰.f i ≫ U.hom⟩
    let _ : Cover.Over S 𝒰 := { isOver_map _ := ⟨rfl⟩ }
    refine ⟨𝒰, inferInstance,
      fun i ↦ P.comp_mem _ _ (𝒰.map_prop i) U.prop, fun X f ⟨i⟩ ↦ ?_⟩
    rw [Sieve.coverByImage]
    exact ⟨⟨affineOverMk (𝒰.f i ≫ U.hom) (P.comp_mem _ _ (𝒰.map_prop i) U.prop),
      CostructuredArrow.homMk (𝟙 _) ⟨⟩ rfl, Over.homMk (𝒰.f i) (by simp) trivial,
      by cat_disch⟩⟩

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.Scheme.isOneHypercoverDense_toOver_Spec** 是 Mathlib 中的一个实例，位
于命名空间 `AlgebraicGeometry.Scheme`。
形式化陈述：isOneHypercoverDense_toOver_Spec : Functor.IsOneHypercoverDense.{u} (Costr
ucturedArrow.toOver P Scheme.Spec S) ((CostructuredArrow.toOver P Scheme.Spec S)
.inducedTopology (S.smallGrothendieckTopology P)) (S.smallGrothendieckTopology P
)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsOneHypercoverDense.of_hasPullbacks`：∀ {C₀ : Typ
e u₀} {C : Type u} [inst : CategoryTheory.Category.{v₀, u₀} C₀] [inst_1 : Catego
ryTheory.Category.{v, u} C]   {F : CategoryTheory…
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.instTop`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C], ⊤.IsMultiplicative
· 使用定理 `CategoryTheory.Functor.instIsDenseSubsiteInducedTopologyOfIsCoverDense`：
∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {D : Type u_2}   
[inst_1 : CategoryTheory.Category.{v_2, u_2} D] (G : Categor…
· 使用定理 `CategoryTheory.Functor.locallyCoverDense_of_isCoverDense`：∀ {C : Type u_
1} [inst : CategoryTheory.Category.{v_1, u_1} C] {D : Type u_2}   [inst_1 : Cate
goryTheory.Category.{v_2, u_2} D] (G : Categor…
· 使用定理 `CategoryTheory.Functor.IsLocallyFull.of_full`：∀ {C : Type uC} [inst : Ca
tegoryTheory.Category.{vC, uC} C] {D : Type uD} [inst_1 : CategoryTheory.Categor
y.{vD, uD} D]   {K : CategoryTheor…
· 使用定理 `CategoryTheory.MorphismProperty.instFullCostructuredArrowTopOverToOver`：
∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{u_3, u_1} C]   
[inst_1 : CategoryTheory.Category.{u_4, u_2} D] (P : Categor…
· 使用定理 `AlgebraicGeometry.Spec.full`：AlgebraicGeometry.Scheme.Spec.Full
· 使用定理 `CategoryTheory.Functor.IsLocallyFaithful.of_faithful`：∀ {C : Type uC} [i
nst : CategoryTheory.Category.{vC, uC} C] {D : Type uD} [inst_1 : CategoryTheory
.Category.{vD, uD} D]   {K : CategoryTheor…
· 使用定理 `CategoryTheory.MorphismProperty.instFaithfulCostructuredArrowTopOverToOv
er`：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{u_3, u_1} C
]   [inst_1 : CategoryTheory.Category.{u_4, u_2} D] (P : Categor…
· 使用定理 `AlgebraicGeometry.Spec.faithful`：AlgebraicGeometry.Scheme.Spec.Faithful
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toIsStableUnderComposit
ion`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheor
y.MorphismProperty C}   [self : W.IsMultiplicative], W.IsStableUn…
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullbacks`：CategoryTheory.Limit
s.HasPullbacks AlgebraicGeometry.Scheme
· 使用定理 `CategoryTheory.Limits.PreservesFiniteLimits.preservesFiniteLimits`：∀ {C 
: Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : C
ategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.PreservesLimits.preservesFiniteLimits`：∀ {C : Type
 u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Categor
yTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `AlgebraicGeometry.Scheme.instJointlySurjectivePrecoverage`：∀ {P : Catego
ryTheory.MorphismProperty AlgebraicGeometry.Scheme},   AlgebraicGeometry.Scheme.
JointlySurjective (AlgebraicGeometry.Scheme.pre…
· 使用引理 `AlgebraicGeometry.IsZariskiLocalAtSource.of_isOpenImmersion`：of_isOpenIm
mersion [P.ContainsIdentities] [IsOpenImmersion f] : P f
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toContainsIdentities`：∀
 {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheory.Morp
hismProperty C}   [self : W.IsMultiplicative], W.ContainsId…
· 使用定理 `AlgebraicGeometry.Scheme.instIsOpenImmersionF`：∀ {X : AlgebraicGeometry.
Scheme} (𝒰 : X.OpenCover) (i : 𝒰.I₀), AlgebraicGeometry.IsOpenImmersion (𝒰.f i)
· 使用定理 `AlgebraicGeometry.Scheme.isJointlySurjectivePreserving`：∀ (P : CategoryT
heory.MorphismProperty AlgebraicGeometry.Scheme),   AlgebraicGeometry.Scheme.IsJ
ointlySurjectivePreserving P
· 使用引理 `CategoryTheory.MorphismProperty.comp_mem`：comp_mem (W : MorphismProperty
 C) [W.IsStableUnderComposition] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : W f) 
(hg : W g) : W (f ≫ g)
· 使用定理 `AlgebraicGeometry.Scheme.AffineOpenCover.instIsOpenImmersionF`：∀ {X : Al
gebraicGeometry.Scheme} (𝒰 : X.AffineOpenCover) (j : 𝒰.I₀), AlgebraicGeometry.Is
OpenImmersion (𝒰.f j)
· 使用定理 `CategoryTheory.MorphismProperty.Comma.prop`：∀ {A : Type u_1} [inst : Cat
egoryTheory.Category.{v_1, u_1} A] {B : Type u_2}   [inst_1 : CategoryTheory.Cat
egory.{v_2, u_2} B] {T : Type u_…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.Scheme.mem_smallGrothendieckTopology`：mem_smallGrothen
dieckTopology [P.HasOfPostcompProperty P] (X : P.Over ⊤ S) (R : Sieve X) : R in 
S.smallGrothendieckTopology P X ↔ exists (𝒰 …
· 使用定理 `CategoryTheory.MorphismProperty.IsLocalAtSource.toRespects`：∀ {C : Type 
u} {inst : CategoryTheory.Category.{v, u} C} {P : CategoryTheory.MorphismPropert
y C}   (K : CategoryTheory.Precoverage C) [self …
· 使用定理 `AlgebraicGeometry.Scheme.Cover.map_prop`：∀ {X : AlgebraicGeometry.Scheme
} {P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme}   (𝒰 : Algebrai
cGeometry.Scheme.Cover (Algeb…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `CategoryTheory.Sieve.mem_ofArrows_iff`：mem_ofArrows_iff {W : C} (g : W ⟶
 X) : ofArrows Y f g ↔ exists (i : I) (a : W ⟶ Y i), g = a ≫ f i
-/
instance isOneHypercoverDense_toOver_Spec :
    Functor.IsOneHypercoverDense.{u} (CostructuredArrow.toOver P Scheme.Spec S)
      ((CostructuredArrow.toOver P Scheme.Spec S).inducedTopology (S.smallGrothendieckTopology P))
      (S.smallGrothendieckTopology P) :=
  Functor.IsOneHypercoverDense.of_hasPullbacks fun X ↦ by
    let 𝒰 := affineOpenCover X.left
    let 𝒱 : Cover (precoverage P) X.left :=
      𝒰.openCover.changeProp (fun _ ↦ IsZariskiLocalAtSource.of_isOpenImmersion _)
    let _ (i : 𝒱.I₀) : (𝒱.X i).Over S := ⟨𝒰.f i ≫ X.hom⟩
    let : Cover.Over S 𝒱 := { isOver_map _ := ⟨rfl⟩ }
    refine ⟨𝒰.I₀, fun i ↦ affineOverMk (𝒰.f i ≫ X.hom)
      (P.comp_mem _ _ (IsZariskiLocalAtSource.of_isOpenImmersion (𝒰.f i)) X.prop),
      fun i ↦ CostructuredArrow.homMk (𝒰.f i) (by simp), ?_⟩
    rw [Scheme.mem_smallGrothendieckTopology]
    exact ⟨𝒱, inferInstance, fun i ↦ P.comp_mem _ _ (𝒱.map_prop i) X.prop,
      fun _ _ ⟨i⟩ ↦ (Sieve.mem_ofArrows_iff ..).mpr ⟨i, 𝟙 _, by cat_disch⟩⟩

end AlgebraicGeometry.Scheme

