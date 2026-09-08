/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten, Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Equalizer

/-!

# Separated morphisms

A morphism of schemes is separated if its diagonal morphism is a closed immersion.

## Main definitions
- `AlgebraicGeometry.IsSeparated`: The class of separated morphisms.
- `AlgebraicGeometry.Scheme.IsSeparated`: The class of separated schemes.
- `AlgebraicGeometry.IsSeparated.hasAffineProperty`:
  A morphism is separated iff the preimage of affine opens are separated schemes.
-/

public section


noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

open scoped AlgebraicGeometry

namespace AlgebraicGeometry

variable {W X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- A morphism is separated if the diagonal map is a closed immersion. -/
@[mk_iff]
/-
**AlgebraicGeometry.IsSeparated** 是 Mathlib 中的一个类，位于命名空间 `AlgebraicGeometry`。
形式化陈述：IsSeparated : Prop where /-- A morphism is separated if the diagonal map i
s a closed immersion. -/ isClosedImmersion_diagonal : IsClosedImmersion (pullbac
k.diagonal f)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism is separated if the diagonal map is a closed immersion.
-/
class IsSeparated : Prop where
  /-- A morphism is separated if the diagonal map is a closed immersion. -/
  isClosedImmersion_diagonal : IsClosedImmersion (pullback.diagonal f) := by infer_instance

@[deprecated (since := "2026-01-20")]
alias IsSeparated.diagonal_isClosedImmersion := IsSeparated.isClosedImmersion_diagonal

namespace IsSeparated

attribute [instance] diagonal_isClosedImmersion

/-
**AlgebraicGeometry.IsSeparated.isSeparated_eq_diagonal_isClosedImmersion** 是 Ma
thlib 中的一个定理，位于命名空间 `AlgebraicGeometry.IsSeparated`。
形式化陈述：isSeparated_eq_diagonal_isClosedImmersion : @IsSeparated = MorphismPropert
y.diagonal @IsClosedImmersion
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullbacks`：CategoryTheory.Limit
s.HasPullbacks AlgebraicGeometry.Scheme
· 使用定理 `AlgebraicGeometry.isSeparated_iff`：∀ {X Y : AlgebraicGeometry.Scheme} (f
 : X ⟶ Y),   AlgebraicGeometry.IsSeparated f ↔     autoParam (AlgebraicGeometry.
IsClosedImmersion (Cate…
-/
theorem isSeparated_eq_diagonal_isClosedImmersion :
    @IsSeparated = MorphismProperty.diagonal @IsClosedImmersion := by
  ext
  exact isSeparated_iff _

/-- Monomorphisms are separated. -/
/-
**AlgebraicGeometry.IsSeparated.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Is
Separated`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Monomorphisms are separated.
-/
instance (priority := 900) isSeparated_of_mono [Mono f] : IsSeparated f where

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.IsSeparated.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Is
Separated`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MorphismProperty.RespectsIso @IsSeparated := by
  rw [isSeparated_eq_diagonal_isClosedImmersion]
  infer_instance
/-
**AlgebraicGeometry.IsSeparated.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Is
Separated`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 900) [IsSeparated f] : QuasiSeparated f where

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.IsSeparated.stableUnderComposition** 是 Mathlib 中的一个实例，位于命名空间
 `AlgebraicGeometry.IsSeparated`。
形式化陈述：stableUnderComposition : MorphismProperty.IsStableUnderComposition @IsSepa
rated
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullbacks`：CategoryTheory.Limit
s.HasPullbacks AlgebraicGeometry.Scheme
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.IsSeparated.isSeparated_eq_diagonal_isClosedImmersion`
：isSeparated_eq_diagonal_isClosedImmersion : @IsSeparated = MorphismProperty.dia
gonal @IsClosedImmersion
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toIsStableUnderComposit
ion`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheor
y.MorphismProperty C}   [self : W.IsMultiplicative], W.IsStableUn…
· 使用定理 `AlgebraicGeometry.IsClosedImmersion.instIsMultiplicativeScheme`：Category
Theory.MorphismProperty.IsMultiplicative @AlgebraicGeometry.IsClosedImmersion
· 使用定理 `AlgebraicGeometry.IsClosedImmersion.isStableUnderBaseChange`：CategoryThe
ory.MorphismProperty.IsStableUnderBaseChange @AlgebraicGeometry.IsClosedImmersio
n
-/
instance stableUnderComposition : MorphismProperty.IsStableUnderComposition @IsSeparated := by
  rw [isSeparated_eq_diagonal_isClosedImmersion]
  infer_instance
/-
**AlgebraicGeometry.IsSeparated.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Is
Separated`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsSeparated f] [IsSeparated g] : IsSeparated (f ≫ g) :=
  stableUnderComposition.comp_mem f g inferInstance inferInstance
/-
**AlgebraicGeometry.IsSeparated.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Is
Separated`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MorphismProperty.IsMultiplicative @IsSeparated where
  id_mem _ := inferInstance

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.IsSeparated.isStableUnderBaseChange** 是 Mathlib 中的一个实例，位于命名空
间 `AlgebraicGeometry.IsSeparated`。
形式化陈述：isStableUnderBaseChange : MorphismProperty.IsStableUnderBaseChange @IsSepa
rated
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullbacks`：CategoryTheory.Limit
s.HasPullbacks AlgebraicGeometry.Scheme
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.IsSeparated.isSeparated_eq_diagonal_isClosedImmersion`
：isSeparated_eq_diagonal_isClosedImmersion : @IsSeparated = MorphismProperty.dia
gonal @IsClosedImmersion
· 使用定理 `CategoryTheory.MorphismProperty.IsStableUnderBaseChange.diagonal`：∀ {C :
 Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limi
ts.HasPullbacks C]   {P : CategoryTheory.MorphismPrope…
· 使用定理 `AlgebraicGeometry.IsClosedImmersion.isStableUnderBaseChange`：CategoryThe
ory.MorphismProperty.IsStableUnderBaseChange @AlgebraicGeometry.IsClosedImmersio
n
-/
instance isStableUnderBaseChange : MorphismProperty.IsStableUnderBaseChange @IsSeparated := by
  rw [isSeparated_eq_diagonal_isClosedImmersion]
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.IsSeparated.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Is
Separated`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsZariskiLocalAtTarget @IsSeparated := by
  rw [isSeparated_eq_diagonal_isClosedImmersion]
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.IsSeparated.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Is
Separated`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [IsSeparated g] :
    IsSeparated (pullback.fst f g) :=
  MorphismProperty.pullback_fst f g inferInstance

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.IsSeparated.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Is
Separated`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [IsSeparated f] :
    IsSeparated (pullback.snd f g) :=
  MorphismProperty.pullback_snd f g inferInstance
/-
**AlgebraicGeometry.IsSeparated.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Is
Separated`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (f : X ⟶ Y) (V : Y.Opens) [IsSeparated f] : IsSeparated (f ∣_ V) :=
  IsZariskiLocalAtTarget.restrict ‹_› V
/-
**AlgebraicGeometry.IsSeparated.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Is
Separated`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (f : X ⟶ Y) (U : X.Opens) (V : Y.Opens) (e) [IsSeparated f] :
    IsSeparated (f.resLE V U e) := by
  delta Scheme.Hom.resLE; infer_instance
/-
**AlgebraicGeometry.IsSeparated.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Is
Separated`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (R S : CommRingCat.{u}) (f : R ⟶ S) : IsSeparated (Spec.map f) := by
  constructor
  let := f.hom.toAlgebra
  change IsClosedImmersion
    (Limits.pullback.diagonal (Spec.map (CommRingCat.ofHom (algebraMap R S))))
  rw [diagonal_SpecMap, MorphismProperty.cancel_right_of_respectsIso @IsClosedImmersion]
  exact .spec_of_surjective _ fun x ↦ ⟨.tmul R 1 x,
    (Algebra.TensorProduct.lmul'_apply_tmul (R := R) (S := S) 1 x).trans (one_mul x)⟩

set_option backward.isDefEq.respectTransparency.types false in
@[instance 100]
/-
**AlgebraicGeometry.IsSeparated.of_isAffineHom** 是 Mathlib 中的一个引理，位于命名空间 `Algebr
aicGeometry.IsSeparated`。
形式化陈述：of_isAffineHom [h : IsAffineHom f] : IsSeparated f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AlgebraicGeometry.HasAffineProperty.iff_of_isAffine`：∀ {P : CategoryTheo
ry.MorphismProperty AlgebraicGeometry.Scheme} {Q : AlgebraicGeometry.AffineTarge
tMorphismProperty}   [AlgebraicGeometry.H…
· 使用定理 `AlgebraicGeometry.instHasAffinePropertyIsAffineHomIsAffine`：AlgebraicGeo
metry.HasAffineProperty @AlgebraicGeometry.IsAffineHom fun X x x_1 x_2 => Algebr
aicGeometry.IsAffine X
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MorphismProperty.arrow_mk_iso_iff`：arrow_mk_iso_iff (P : 
MorphismProperty C) [RespectsIso P] {W X Y Z : C} {f : W ⟶ X} {g : Y ⟶ Z} (e : A
rrow.mk f ≅ Arrow.mk g) : P f ↔ P g
· 使用定理 `AlgebraicGeometry.IsSeparated.instRespectsIsoScheme`：CategoryTheory.Morp
hismProperty.RespectsIso @AlgebraicGeometry.IsSeparated
· 使用定理 `AlgebraicGeometry.IsSeparated.instMap`：∀ (R S : CommRingCat) (f : R ⟶ S)
, AlgebraicGeometry.IsSeparated (AlgebraicGeometry.Spec.map f)
· 使用定理 `AlgebraicGeometry.IsZariskiLocalAtTarget.iff_of_iSup_eq_top`：iff_of_iSup
_eq_top {ι} (U : ι -> Y.Opens) (hU : iSup U = ⊤) : P f ↔ forall i, P (f ∣_ U i)
· 使用定理 `AlgebraicGeometry.IsSeparated.instIsZariskiLocalAtTarget`：AlgebraicGeome
try.IsZariskiLocalAtTarget @AlgebraicGeometry.IsSeparated
· 使用定理 `AlgebraicGeometry.iSup_affineOpens_eq_top`：iSup_affineOpens_eq_top (X : 
Scheme) : ⨆ i : X.affineOpens, (i : X.Opens) = ⊤
· 使用定理 `AlgebraicGeometry.IsZariskiLocalAtTarget.restrict`：restrict (hf : P f) (
U : Y.Opens) : P (f ∣_ U)
· 使用定理 `AlgebraicGeometry.HasAffineProperty.instIsZariskiLocalAtTarget`：∀ {P : C
ategoryTheory.MorphismProperty AlgebraicGeometry.Scheme} {Q : AlgebraicGeometry.
AffineTargetMorphismProperty}   [AlgebraicGeometry.H…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma of_isAffineHom [h : IsAffineHom f] : IsSeparated f := by
  wlog hY : IsAffine Y
  · rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @IsSeparated) _
      (iSup_affineOpens_eq_top Y)]
    intro U
    have H : IsAffineHom (f ∣_ U) := IsZariskiLocalAtTarget.restrict h U
    exact this _ U.2
  have : IsAffine X := HasAffineProperty.iff_of_isAffine.mp h
  rw [MorphismProperty.arrow_mk_iso_iff @IsSeparated (arrowIsoSpecΓOfIsAffine f)]
  infer_instance
/-
**AlgebraicGeometry.IsSeparated.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Is
Separated`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {S T : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (i : S ⟶ T) [IsSeparated i] :
    IsClosedImmersion (pullback.mapDesc f g i) :=
  MorphismProperty.of_isPullback (pullback_map_diagonal_isPullback f g i)
    inferInstance

set_option backward.isDefEq.respectTransparency false in
/-- Given `f : X ⟶ Y` and `g : Y ⟶ Z` such that `g` is separated, the induced map
`X ⟶ X ×[Z] Y` is a closed immersion. -/
/-
**AlgebraicGeometry.IsSeparated.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Is
Separated`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `f : X ⟶ Y` and `g : Y ⟶ Z` such that `g` is separated, the induced map
`X ⟶ X ×[Z] Y` is a closed immersion.
-/
instance [IsSeparated g] :
    IsClosedImmersion (pullback.lift (𝟙 _) f (Category.id_comp (f ≫ g))) := by
  rw [← MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion (pullback.fst f (𝟙 Y))]
  rw [← MorphismProperty.cancel_right_of_respectsIso @IsClosedImmersion _
    (pullback.congrHom rfl (Category.id_comp g)).inv]
  convert (inferInstance : IsClosedImmersion (pullback.mapDesc f (𝟙 _) g))
  ext : 1 <;> simp [pullback.condition]

end IsSeparated

section of_injective

open Scheme Pullback

variable (𝒰 : Y.OpenCover) (𝒱 : ∀ i, (pullback f (𝒰.f i)).OpenCover)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.Scheme.Pullback.diagonalCoverDiagonalRange_eq_top_of_injecti
ve** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.Scheme.Pullback`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) (𝒰 : Y.OpenCover)   (𝒱 : (i
 : 𝒰.I₀) → (CategoryTheory.Limits.pullback f (𝒰.f i)).OpenCover),   Function.Inj
ective ⇑f → AlgebraicGeometry.Scheme.Pullback.diagonalCoverDiagonalRange f 𝒰 𝒱 =
 ⊤
参数：f : X ⟶ Y；𝒰 : Y.OpenCover；𝒱 : (i : 𝒰.I₀) → (CategoryTheory.Limits.pullback f 
(𝒰.f i)).OpenCover。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `top_le_iff`：top_le_iff : ⊤ <= a ↔ a = ⊤
· 使用定理 `AlgebraicGeometry.Scheme.instIsStableUnderBaseChangePrecoverageOfIsJoint
lySurjectivePreservingOfIsStableUnderBaseChange`：∀ (P : CategoryTheory.MorphismP
roperty AlgebraicGeometry.Scheme)   [AlgebraicGeometry.Scheme.IsJointlySurjectiv
ePreserving P] [P.IsStableUnd…
· 使用定理 `AlgebraicGeometry.Scheme.instIsJointlySurjectivePreservingIsOpenImmersio
n`：AlgebraicGeometry.Scheme.IsJointlySurjectivePreserving AlgebraicGeometry.IsOp
enImmersion
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `isOpen_iUnion`：isOpen_iUnion {f : ι -> Set X} (h : forall i, IsOpen (f i
)) : IsOpen (⋃ i, f i)
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TopologicalSpace.Opens.iSup_mk`：iSup_mk {ι} (s : ι -> Set α) (h : forall
 i, IsOpen (s i)) : (⨆ i, ⟨s i, h i⟩ : Opens α) = ⟨⋃ i, s i, isOpen_iUnion h⟩
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `AlgebraicGeometry.Scheme.Hom.comp_apply`：comp_apply {X Y Z : Scheme} (f 
: X ⟶ Y) (g : Y ⟶ Z) (x : X) : (f ≫ g) x = g (f x)
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…
· 使用定理 `AlgebraicGeometry.Scheme.instJointlySurjectivePrecoverage`：∀ {P : Catego
ryTheory.MorphismProperty AlgebraicGeometry.Scheme},   AlgebraicGeometry.Scheme.
JointlySurjective (AlgebraicGeometry.Scheme.pre…
· 使用定理 `AlgebraicGeometry.Scheme.Cover.covers`：∀ {K : CategoryTheory.Precoverage
 AlgebraicGeometry.Scheme} {X : AlgebraicGeometry.Scheme}   [inst : AlgebraicGeo
metry.Scheme.JointlySurject…
· 使用引理 `AlgebraicGeometry.Scheme.Pullback.exists_preimage_pullback`：exists_preim
age_pullback (x : X) (y : Y) (h : f x = g y) : exists z : ↑(pullback f g), pullb
ack.fst f g z = x ∧ pullback.snd f g z = y
· 使用引理 `AlgebraicGeometry.Scheme.Pullback.diagonalCover_map`：diagonalCover_map (
I) : (diagonalCover f 𝒰 𝒱).f I = pullback.map _ _ _ _ ((𝒱 I.fst).f _ ≫ pullback.
fst _ _) ((𝒱 I.fst).f _ ≫ pullback.fst _ …
· 使用引理 `AlgebraicGeometry.Scheme.Pullback.range_map`：range_map {X' Y' S' : Schem
e.{u}} (f' : X' ⟶ S') (g' : Y' ⟶ S') (i₁ : X ⟶ X') (i₂ : Y ⟶ Y') (i₃ : S ⟶ S') (
e₁ : f ≫ i₃ = i₁ ≫ f') (e₂ : g ≫ …
· 使用定理 `AlgebraicGeometry.Scheme.instIsOpenImmersionF`：∀ {X : AlgebraicGeometry.
Scheme} (𝒰 : X.OpenCover) (i : 𝒰.I₀), AlgebraicGeometry.IsOpenImmersion (𝒰.f i)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
lemma Scheme.Pullback.diagonalCoverDiagonalRange_eq_top_of_injective
    (hf : Function.Injective f) :
    diagonalCoverDiagonalRange f 𝒰 𝒱 = ⊤ := by
  rw [← top_le_iff]
  rintro x -
  simp only [diagonalCoverDiagonalRange, openCoverOfBase_I₀, openCoverOfBase_X,
    openCoverOfLeftRight_I₀, Opens.iSup_mk, Opens.carrier_eq_coe, Hom.coe_opensRange, Opens.mem_mk,
    Set.mem_iUnion, Set.mem_range, Sigma.exists]
  have H : pullback.fst f f x = pullback.snd f f x :=
    hf (by rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition])
  let i := 𝒰.idx (f (pullback.fst f f x))
  obtain ⟨y : 𝒰.X i, hy : 𝒰.f i y = f _⟩ :=
    𝒰.covers (f (pullback.fst f f x))
  obtain ⟨z, hz₁, hz₂⟩ := exists_preimage_pullback _ _ hy.symm
  let j := (𝒱 i).idx z
  obtain ⟨w : (𝒱 i).X j, hy : (𝒱 i).f j w = z⟩ := (𝒱 i).covers z
  refine ⟨i, j, ?_⟩
  simp_rw [diagonalCover_map]
  change x ∈ Set.range _
  simp only [diagonalCover, openCoverOfBase_I₀,
    Precoverage.ZeroHypercover.pullback₁_toPreZeroHypercover, PreZeroHypercover.pullback₁_X,
    Precoverage.ZeroHypercover.bind_toPreZeroHypercover, openCoverOfBase_X,
    PreZeroHypercover.bind_X, openCoverOfLeftRight_I₀, openCoverOfLeftRight_X]
  rw [range_map]
  simp [← H, ← hz₁, ← hy]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.Scheme.Pullback.range_diagonal_subset_diagonalCoverDiagonalR
ange** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.Scheme.Pullback`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) (𝒰 : Y.OpenCover)   (𝒱 : (i
 : 𝒰.I₀) → (CategoryTheory.Limits.pullback f (𝒰.f i)).OpenCover),   Set.range ⇑(
CategoryTheory.Limits.pullback.diagonal f) ⊆     ↑(AlgebraicGeometry.Scheme.Pull
back.diagonalCoverDiagonalRange f 𝒰 𝒱)
参数：f : X ⟶ Y；𝒰 : Y.OpenCover；𝒱 : (i : 𝒰.I₀) → (CategoryTheory.Limits.pullback f 
(𝒰.f i)).OpenCover；CategoryTheory.Limits.pullback.diagonal f；AlgebraicGeometry.S
cheme.Pullback.diagonalCoverDiagonalRange f 𝒰 𝒱。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `AlgebraicGeometry.Scheme.instIsStableUnderBaseChangePrecoverageOfIsJoint
lySurjectivePreservingOfIsStableUnderBaseChange`：∀ (P : CategoryTheory.MorphismP
roperty AlgebraicGeometry.Scheme)   [AlgebraicGeometry.Scheme.IsJointlySurjectiv
ePreserving P] [P.IsStableUnd…
· 使用定理 `AlgebraicGeometry.Scheme.instIsJointlySurjectivePreservingIsOpenImmersio
n`：AlgebraicGeometry.Scheme.IsJointlySurjectivePreserving AlgebraicGeometry.IsOp
enImmersion
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isOpen_iUnion`：isOpen_iUnion {f : ι -> Set X} (h : forall i, IsOpen (f i
)) : IsOpen (⋃ i, f i)
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用定理 `TopologicalSpace.Opens.iSup_mk`：iSup_mk {ι} (s : ι -> Set α) (h : forall
 i, IsOpen (s i)) : (⨆ i, ⟨s i, h i⟩ : Opens α) = ⟨⋃ i, s i, isOpen_iUnion h⟩
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `AlgebraicGeometry.Scheme.instJointlySurjectivePrecoverage`：∀ {P : Catego
ryTheory.MorphismProperty AlgebraicGeometry.Scheme},   AlgebraicGeometry.Scheme.
JointlySurjective (AlgebraicGeometry.Scheme.pre…
· 使用定理 `AlgebraicGeometry.Scheme.Cover.covers`：∀ {K : CategoryTheory.Precoverage
 AlgebraicGeometry.Scheme} {X : AlgebraicGeometry.Scheme}   [inst : AlgebraicGeo
metry.Scheme.JointlySurject…
· 使用引理 `AlgebraicGeometry.Scheme.Pullback.exists_preimage_pullback`：exists_preim
age_pullback (x : X) (y : Y) (h : f x = g y) : exists z : ↑(pullback f g), pullb
ack.fst f g z = x ∧ pullback.snd f g z = y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.Scheme.Hom.comp_apply`：comp_apply {X Y Z : Scheme} (f 
: X ⟶ Y) (g : Y ⟶ Z) (x : X) : (f ≫ g) x = g (f x)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Limits.pullback.hom_ext`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categor
yTheory.Limits.HasPullback f…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.limit.lift_π_assoc`：∀ {J : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v,
 u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.pullback.diagonal_fst_assoc`：∀ {C : Type u_1} [ins
t : CategoryTheory.Category.{v_1, u_1} C] {X Y : C} (f : X ⟶ Y)   [inst_1 : Cate
goryTheory.Limits.HasPullback f f] {Z :…
· 使用定理 `CategoryTheory.Limits.pullback.diagonal_fst`：diagonal_fst : diagonal f ≫
 pullback.fst _ _ = 𝟙 _
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.pullback.diagonal_snd_assoc`：∀ {C : Type u_1} [ins
t : CategoryTheory.Category.{v_1, u_1} C] {X Y : C} (f : X ⟶ Y)   [inst_1 : Cate
goryTheory.Limits.HasPullback f f] {Z :…
· 使用定理 `CategoryTheory.Limits.pullback.diagonal_snd`：diagonal_snd : diagonal f ≫
 pullback.snd _ _ = 𝟙 _
-/
lemma Scheme.Pullback.range_diagonal_subset_diagonalCoverDiagonalRange :
    Set.range (pullback.diagonal f) ⊆ diagonalCoverDiagonalRange f 𝒰 𝒱 := by
  rintro _ ⟨x, rfl⟩
  simp only [diagonalCoverDiagonalRange, openCoverOfBase_I₀, openCoverOfBase_X,
    openCoverOfLeftRight_I₀, Opens.iSup_mk, Opens.carrier_eq_coe, Hom.coe_opensRange, Opens.coe_mk,
    Set.mem_iUnion, Set.mem_range, Sigma.exists]
  let i := 𝒰.idx (f x)
  obtain ⟨y : 𝒰.X i, hy : 𝒰.f i y = f x⟩ := 𝒰.covers (f x)
  obtain ⟨z, hz₁, hz₂⟩ := exists_preimage_pullback _ _ hy.symm
  let j := (𝒱 i).idx z
  obtain ⟨w : (𝒱 i).X j, hy : (𝒱 i).f j w = z⟩ := (𝒱 i).covers z
  refine ⟨i, j, pullback.diagonal ((𝒱 i).f j ≫ pullback.snd f (𝒰.f i)) w, ?_⟩
  rw [← hz₁, ← hy, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply]
  simp only [diagonalCover, openCoverOfBase_I₀,
    Precoverage.ZeroHypercover.pullback₁_toPreZeroHypercover, PreZeroHypercover.pullback₁_X,
    Cover.pullbackHom, Precoverage.ZeroHypercover.bind_toPreZeroHypercover, openCoverOfBase_X,
    PreZeroHypercover.bind_X, openCoverOfLeftRight_I₀, openCoverOfLeftRight_X,
    PreZeroHypercover.bind_f, openCoverOfLeftRight_f, openCoverOfBase_f, Hom.comp_base,
    TopCat.hom_comp, ContinuousMap.comp_apply, ContinuousMap.comp_assoc]
  simp_rw [← Scheme.Hom.comp_apply]
  congr 5
  apply pullback.hom_ext <;> simp

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.isClosedImmersion_diagonal_restrict_diagonalCoverDiagonalRan
ge** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry`。
形式化陈述：isClosedImmersion_diagonal_restrict_diagonalCoverDiagonalRange [forall i, 
IsAffine (𝒰.X i)] [forall i j, IsAffine ((𝒱 i).X j)] : IsClosedImmersion (pullba
ck.diagonal f ∣_ diagonalCoverDiagonalRange f 𝒰 𝒱)
参数：𝒰.X i；(𝒱 i).X j。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `AlgebraicGeometry.Scheme.instIsStableUnderBaseChangePrecoverageOfIsJoint
lySurjectivePreservingOfIsStableUnderBaseChange`：∀ (P : CategoryTheory.MorphismP
roperty AlgebraicGeometry.Scheme)   [AlgebraicGeometry.Scheme.IsJointlySurjectiv
ePreserving P] [P.IsStableUnd…
· 使用定理 `AlgebraicGeometry.Scheme.instIsJointlySurjectivePreservingIsOpenImmersio
n`：AlgebraicGeometry.Scheme.IsJointlySurjectivePreserving AlgebraicGeometry.IsOp
enImmersion
· 使用定理 `AlgebraicGeometry.Scheme.instIsOpenImmersionF`：∀ {X : AlgebraicGeometry.
Scheme} (𝒰 : X.OpenCover) (i : 𝒰.I₀), AlgebraicGeometry.IsOpenImmersion (𝒰.f i)
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι`：∀ {X : AlgebraicGeo
metry.Scheme} (U : X.Opens), AlgebraicGeometry.IsOpenImmersion U.ι
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.Scheme.Hom.image_preimage_eq_opensRange_inf`：image_pre
image_eq_opensRange_inf (U : Y.Opens) : f ''ᵁ f ⁻¹ᵁ U = f.opensRange ⊓ U
· 使用定理 `inf_eq_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
= b ↔ b ≤ a
· 使用引理 `AlgebraicGeometry.Scheme.Opens.opensRange_ι`：opensRange_ι : U.ι.opensRan
ge = U
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `TopologicalSpace.Opens.map_iSup`：map_iSup (f : X ⟶ Y) {ι : Type*} (U : ι
 -> Opens Y) : (map f).obj (iSup U) = iSup ((map f).obj ∘ U)
· 使用引理 `AlgebraicGeometry.Scheme.Opens.ι_preimage_self`：ι_preimage_self : U.ι ⁻¹
ᵁ U = ⊤
· 使用定理 `AlgebraicGeometry.IsZariskiLocalAtTarget.iff_of_iSup_eq_top`：iff_of_iSup
_eq_top {ι} (U : ι -> Y.Opens) (hU : iSup U = ⊤) : P f ↔ forall i, P (f ∣_ U i)
· 使用定理 `AlgebraicGeometry.IsClosedImmersion.isZariskiLocalAtTarget`：AlgebraicGeo
metry.IsZariskiLocalAtTarget @AlgebraicGeometry.IsClosedImmersion
· 使用定理 `CategoryTheory.MorphismProperty.arrow_mk_iso_iff`：arrow_mk_iso_iff (P : 
MorphismProperty C) [RespectsIso P] {W X Y Z : C} {f : W ⟶ X} {g : Y ⟶ Z} (e : A
rrow.mk f ≅ Arrow.mk g) : P f ↔ P g
· 使用定理 `AlgebraicGeometry.IsSeparated.diagonal_isClosedImmersion`：∀ {X Y : Algeb
raicGeometry.Scheme} {f : X ⟶ Y} [self : AlgebraicGeometry.IsSeparated f],   Alg
ebraicGeometry.IsClosedImmersion (CategoryTheo…
· 使用引理 `AlgebraicGeometry.IsSeparated.of_isAffineHom`：of_isAffineHom [h : IsAffi
neHom f] : IsSeparated f
· 使用定理 `AlgebraicGeometry.isAffineHom_of_isAffine`：∀ {X Y : AlgebraicGeometry.Sc
heme} (f : X ⟶ Y) [AlgebraicGeometry.IsAffine X] [AlgebraicGeometry.IsAffine Y],
   AlgebraicGeometry.IsAffineHo…
-/
lemma isClosedImmersion_diagonal_restrict_diagonalCoverDiagonalRange
    [∀ i, IsAffine (𝒰.X i)] [∀ i j, IsAffine ((𝒱 i).X j)] :
    IsClosedImmersion (pullback.diagonal f ∣_ diagonalCoverDiagonalRange f 𝒰 𝒱) := by
  let U : (Σ i, (𝒱 i).I₀) → (diagonalCoverDiagonalRange f 𝒰 𝒱).toScheme.Opens := fun i ↦
    (diagonalCoverDiagonalRange f 𝒰 𝒱).ι ⁻¹ᵁ ((diagonalCover f 𝒰 𝒱).f ⟨i.1, i.2, i.2⟩).opensRange
  have hU (i) : (diagonalCoverDiagonalRange f 𝒰 𝒱).ι ''ᵁ U i =
      ((diagonalCover f 𝒰 𝒱).f ⟨i.1, i.2, i.2⟩).opensRange := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, inf_eq_right, Opens.opensRange_ι]
    exact le_iSup (fun i : Σ i, (𝒱 i).I₀ ↦ ((diagonalCover f 𝒰 𝒱).f ⟨i.1, i.2, i.2⟩).opensRange) i
  have hf : iSup U = ⊤ := (TopologicalSpace.Opens.map_iSup _ _).symm.trans
    (diagonalCoverDiagonalRange f 𝒰 𝒱).ι_preimage_self
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @IsClosedImmersion) _ hf]
  intro i
  rw [MorphismProperty.arrow_mk_iso_iff (P := @IsClosedImmersion) (morphismRestrictRestrict _ _ _),
    MorphismProperty.arrow_mk_iso_iff (P := @IsClosedImmersion) (morphismRestrictEq _ (hU i)),
    MorphismProperty.arrow_mk_iso_iff (P := @IsClosedImmersion) (diagonalRestrictIsoDiagonal ..)]
  infer_instance

@[stacks 0DVA]
/-
**AlgebraicGeometry.isSeparated_of_injective** 是 Mathlib 中的一个引理，位于命名空间 `Algebrai
cGeometry`。
形式化陈述：isSeparated_of_injective (hf : Function.Injective f) : IsSeparated f
参数：hf : Function.Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用引理 `AlgebraicGeometry.IsZariskiLocalAtTarget.of_iSup_eq_top`：of_iSup_eq_top 
{ι} (U : ι -> Y.Opens) (hU : iSup U = ⊤) (H : forall i, P (f ∣_ U i)) : P f
· 使用定理 `AlgebraicGeometry.IsClosedImmersion.isZariskiLocalAtTarget`：AlgebraicGeo
metry.IsZariskiLocalAtTarget @AlgebraicGeometry.IsClosedImmersion
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ciSup_unique`：ciSup_unique [Unique ι] {s : ι -> α} : ⨆ i, s i = s defaul
t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.diagonalCoverDiagonalRange_eq_top_of_i
njective`：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) (𝒰 : Y.OpenCover)   (𝒱 
: (i : 𝒰.I₀) → (CategoryTheory.Limits.pullback f (𝒰.f i)).OpenCover), …
· 使用引理 `AlgebraicGeometry.isClosedImmersion_diagonal_restrict_diagonalCoverDiago
nalRange`：isClosedImmersion_diagonal_restrict_diagonalCoverDiagonalRange [forall
 i, IsAffine (𝒰.X i)] [forall i j, IsAffine ((𝒱 i).X j)] : IsClosedImm…
· 使用定理 `AlgebraicGeometry.Scheme.isAffine_affineCover`：∀ (X : AlgebraicGeometry.
Scheme) (i : X.affineCover.I₀), AlgebraicGeometry.IsAffine (X.affineCover.X i)
-/
lemma isSeparated_of_injective (hf : Function.Injective f) :
    IsSeparated f := by
  constructor
  let 𝒰 := Y.affineCover
  let 𝒱 (i) := (pullback f (𝒰.f i)).affineCover
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (fun i : PUnit.{0} ↦ ⊤) (by simp) fun _ ↦ ?_
  rw [← diagonalCoverDiagonalRange_eq_top_of_injective f 𝒰 𝒱 hf]
  exact isClosedImmersion_diagonal_restrict_diagonalCoverDiagonalRange f 𝒰 𝒱

end of_injective

/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MorphismProperty.HasOfPostcompProperty @IsClosedImmersion @IsSeparated :=
  MorphismProperty.hasOfPostcompProperty_iff_le_diagonal.mpr
    fun _ _ _ _ ↦ inferInstanceAs (IsClosedImmersion _)
/-
**AlgebraicGeometry.IsClosedImmersion.of_comp** 是 Mathlib 中的一个定理，位于命名空间 `Algebra
icGeometry.IsClosedImmersion`。
形式化陈述：∀ {X Y Z : AlgebraicGeometry.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)   [AlgebraicG
eometry.IsClosedImmersion (CategoryTheory.CategoryStruct.comp f g)] [AlgebraicGe
ometry.IsSeparated g],   AlgebraicGeometry.IsClosedImmersion f
参数：f : X ⟶ Y；g : Y ⟶ Z；CategoryTheory.CategoryStruct.comp f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.of_postcomp`：of_postcomp [W.HasOfPostcom
pProperty W'] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hg : W' g) (hfg : W (f ≫ g)) 
: W f
· 使用定理 `AlgebraicGeometry.instHasOfPostcompPropertySchemeIsClosedImmersionIsSepa
rated`：CategoryTheory.MorphismProperty.HasOfPostcompProperty @AlgebraicGeometry.
IsClosedImmersion   @AlgebraicGeometry.IsSeparated
-/
lemma IsClosedImmersion.of_comp [IsClosedImmersion (f ≫ g)] [IsSeparated g] :
    IsClosedImmersion f := MorphismProperty.of_postcomp _ _ g ‹_› ‹_›

variable {f g} in
/-
**AlgebraicGeometry.IsClosedImmersion.comp_iff** 是 Mathlib 中的一个定理，位于命名空间 `Algebr
aicGeometry.IsClosedImmersion`。
形式化陈述：∀ {X Y Z : AlgebraicGeometry.Scheme} {f : X ⟶ Y} {g : Y ⟶ Z} [AlgebraicGeo
metry.IsClosedImmersion g],   AlgebraicGeometry.IsClosedImmersion (CategoryTheor
y.CategoryStruct.comp f g) ↔ AlgebraicGeometry.IsClosedImmersion f
参数：CategoryTheory.CategoryStruct.comp f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.IsClosedImmersion.of_comp`：∀ {X Y Z : AlgebraicGeometr
y.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)   [AlgebraicGeometry.IsClosedImmersion (Catego
ryTheory.CategoryStruct.comp f g)…
· 使用定理 `AlgebraicGeometry.IsSeparated.isSeparated_of_mono`：∀ {X Y : AlgebraicGeo
metry.Scheme} (f : X ⟶ Y) [CategoryTheory.Mono f], AlgebraicGeometry.IsSeparated
 f
· 使用定理 `AlgebraicGeometry.IsPreimmersion.instMonoScheme`：∀ {X Y : AlgebraicGeome
try.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.IsPreimmersion f], CategoryTheory.Mon
o f
· 使用定理 `AlgebraicGeometry.IsClosedImmersion.instIsPreimmersion`：∀ {X Y : Algebra
icGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.IsClosedImmersion f],   Algebr
aicGeometry.IsPreimmersion f
-/
lemma IsClosedImmersion.comp_iff [IsClosedImmersion g] :
    IsClosedImmersion (f ≫ g) ↔ IsClosedImmersion f :=
  ⟨fun _ ↦ .of_comp f g, fun _ ↦ inferInstance⟩
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {I J : X.IdealSheafData} (h : I ≤ J) : IsClosedImmersion (I.inclusion h) := by
  have : IsClosedImmersion (I.inclusion h ≫ I.subschemeι) := by
    simp only [Scheme.IdealSheafData.inclusion_subschemeι]
    infer_instance
  exact .of_comp _ I.subschemeι
/-
**AlgebraicGeometry.IsSeparated.of_comp** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeom
etry.IsSeparated`。
形式化陈述：∀ {X Y Z : AlgebraicGeometry.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)   [AlgebraicG
eometry.IsSeparated (CategoryTheory.CategoryStruct.comp f g)], AlgebraicGeometry
.IsSeparated f
参数：f : X ⟶ Y；g : Y ⟶ Z；CategoryTheory.CategoryStruct.comp f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `AlgebraicGeometry.IsSeparated.diagonal_isClosedImmersion`：∀ {X Y : Algeb
raicGeometry.Scheme} {f : X ⟶ Y} [self : AlgebraicGeometry.IsSeparated f],   Alg
ebraicGeometry.IsClosedImmersion (CategoryTheo…
· 使用定理 `AlgebraicGeometry.IsClosedImmersion.of_comp`：∀ {X Y Z : AlgebraicGeometr
y.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)   [AlgebraicGeometry.IsClosedImmersion (Catego
ryTheory.CategoryStruct.comp f g)…
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullbacks`：CategoryTheory.Limit
s.HasPullbacks AlgebraicGeometry.Scheme
· 使用定理 `CategoryTheory.IsPullback.instHasPullbackFst`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {P X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_
1 : CategoryTheory.Limits.HasPullb…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.pullback.diagonal_comp`：∀ {C : Type u_1} [inst : C
ategoryTheory.Category.{v_1, u_1} C] {X Y Z : C}   [inst_1 : CategoryTheory.Limi
ts.HasPullbacks C] (f : X ⟶ Y) (g …
· 使用定理 `AlgebraicGeometry.IsSeparated.instCompScheme`：∀ {X Y Z : AlgebraicGeomet
ry.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [AlgebraicGeometry.IsSeparated f]   [Algebrai
cGeometry.IsSeparated g], Algebrai…
· 使用定理 `AlgebraicGeometry.IsSeparated.isSeparated_of_mono`：∀ {X Y : AlgebraicGeo
metry.Scheme} (f : X ⟶ Y) [CategoryTheory.Mono f], AlgebraicGeometry.IsSeparated
 f
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.of_isIso`：∀ {Y Z : AlgebraicGeometry.S
cheme} (g : Y ⟶ Z) [CategoryTheory.IsIso g], AlgebraicGeometry.IsOpenImmersion g
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `AlgebraicGeometry.IsSeparated.instSndScheme`：∀ {X Y S : AlgebraicGeometr
y.Scheme} (f : X ⟶ S) (g : Y ⟶ S) [AlgebraicGeometry.IsSeparated f],   Algebraic
Geometry.IsSeparated (CategoryThe…
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.instStrongMonoOfIsRegularMono`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsRegula
rMono f],   CategoryTheory.StrongM…
· 使用定理 `CategoryTheory.instIsRegularMonoOfIsSplitMono`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsSplit
Mono f],   CategoryTheory.IsRegular…
· 使用定理 `CategoryTheory.Limits.pullback.instIsSplitMonoDiagonal`：∀ {C : Type u_1}
 [inst : CategoryTheory.Category.{v_1, u_1} C] {X Y : C} (f : X ⟶ Y)   [inst_1 :
 CategoryTheory.Limits.HasPullback f f],   C…
-/
lemma IsSeparated.of_comp [IsSeparated (f ≫ g)] : IsSeparated f := by
  have : IsClosedImmersion (pullback.diagonal (f ≫ g)) := inferInstance
  rw [pullback.diagonal_comp] at this
  exact ⟨@IsClosedImmersion.of_comp _ _ _ _ _ this inferInstance⟩

variable {f g} in
/-
**AlgebraicGeometry.IsSeparated.comp_iff** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeo
metry.IsSeparated`。
形式化陈述：∀ {X Y Z : AlgebraicGeometry.Scheme} {f : X ⟶ Y} {g : Y ⟶ Z} [AlgebraicGeo
metry.IsSeparated g],   AlgebraicGeometry.IsSeparated (CategoryTheory.CategorySt
ruct.comp f g) ↔ AlgebraicGeometry.IsSeparated f
参数：CategoryTheory.CategoryStruct.comp f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.IsSeparated.of_comp`：∀ {X Y Z : AlgebraicGeometry.Sche
me} (f : X ⟶ Y) (g : Y ⟶ Z)   [AlgebraicGeometry.IsSeparated (CategoryTheory.Cat
egoryStruct.comp f g)], Alg…
· 使用定理 `AlgebraicGeometry.IsSeparated.instCompScheme`：∀ {X Y Z : AlgebraicGeomet
ry.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [AlgebraicGeometry.IsSeparated f]   [Algebrai
cGeometry.IsSeparated g], Algebrai…
-/
lemma IsSeparated.comp_iff [IsSeparated g] : IsSeparated (f ≫ g) ↔ IsSeparated f :=
  ⟨fun _ ↦ .of_comp f g, fun _ ↦ inferInstance⟩
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MorphismProperty.HasOfPostcompProperty @IsSeparated ⊤ where
  of_postcomp f g _ _ := .of_comp f g
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MorphismProperty.HasOfPostcompProperty @IsAffineHom @IsSeparated :=
  MorphismProperty.hasOfPostcompProperty_iff_le_diagonal.mpr
    fun _ _ _ _ ↦ inferInstanceAs (IsAffineHom _)
/-
**AlgebraicGeometry.IsAffineHom.of_comp** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeom
etry.IsAffineHom`。
形式化陈述：∀ {X Y Z : AlgebraicGeometry.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)   [AlgebraicG
eometry.IsAffineHom (CategoryTheory.CategoryStruct.comp f g)] [AlgebraicGeometry
.IsSeparated g],   AlgebraicGeometry.IsAffineHom f
参数：f : X ⟶ Y；g : Y ⟶ Z；CategoryTheory.CategoryStruct.comp f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.of_postcomp`：of_postcomp [W.HasOfPostcom
pProperty W'] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hg : W' g) (hfg : W (f ≫ g)) 
: W f
· 使用定理 `AlgebraicGeometry.instHasOfPostcompPropertySchemeIsAffineHomIsSeparated`
：CategoryTheory.MorphismProperty.HasOfPostcompProperty @AlgebraicGeometry.IsAffi
neHom @AlgebraicGeometry.IsSeparated
-/
lemma IsAffineHom.of_comp [IsAffineHom (f ≫ g)] [IsSeparated g] :
    IsAffineHom f := MorphismProperty.of_postcomp _ _ g ‹_› ‹_›

variable {f g} in
/-
**AlgebraicGeometry.IsAffineHom.comp_iff** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeo
metry.IsAffineHom`。
形式化陈述：∀ {X Y Z : AlgebraicGeometry.Scheme} {f : X ⟶ Y} {g : Y ⟶ Z} [AlgebraicGeo
metry.IsAffineHom g],   AlgebraicGeometry.IsAffineHom (CategoryTheory.CategorySt
ruct.comp f g) ↔ AlgebraicGeometry.IsAffineHom f
参数：CategoryTheory.CategoryStruct.comp f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.IsAffineHom.of_comp`：∀ {X Y Z : AlgebraicGeometry.Sche
me} (f : X ⟶ Y) (g : Y ⟶ Z)   [AlgebraicGeometry.IsAffineHom (CategoryTheory.Cat
egoryStruct.comp f g)] [Alg…
· 使用引理 `AlgebraicGeometry.IsSeparated.of_isAffineHom`：of_isAffineHom [h : IsAffi
neHom f] : IsSeparated f
· 使用定理 `AlgebraicGeometry.instIsAffineHomCompScheme`：∀ {X Y Z : AlgebraicGeometr
y.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [AlgebraicGeometry.IsAffineHom f]   [Algebraic
Geometry.IsAffineHom g], Algebrai…
-/
lemma IsAffineHom.comp_iff [IsAffineHom g] : IsAffineHom (f ≫ g) ↔ IsAffineHom f :=
  ⟨fun _ ↦ .of_comp f g, fun _ ↦ inferInstance⟩

set_option backward.isDefEq.respectTransparency false in
@[stacks 01KM]
/-
**AlgebraicGeometry.isClosedImmersion_equalizer_** 是 Mathlib 中的一个实例，位于命名空间 `Alge
braicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance isClosedImmersion_equalizer_ι_left {S : Scheme} {X Y : Over S} [IsSeparated Y.hom]
    (f g : X ⟶ Y) : IsClosedImmersion (equalizer.ι f g).left := by
  refine MorphismProperty.of_isPullback
    ((Limits.isPullback_equalizer_prod f g).map (Over.forget _)).flip ?_
  rw [← MorphismProperty.cancel_right_of_respectsIso @IsClosedImmersion _
    (Over.prodLeftIsoPullback Y Y).hom]
  convert! (inferInstance : IsClosedImmersion (pullback.diagonal Y.hom))
  ext1 <;> simp [← Over.comp_left]

set_option backward.isDefEq.respectTransparency false in
/--
Suppose `X` is a reduced scheme and that `f g : X ⟶ Y` agree over some separated `Y ⟶ Z`.
Then `f = g` if `ι ≫ f = ι ≫ g` for some dominant `ι`.
-/
/-
**AlgebraicGeometry.ext_of_isDominant_of_isSeparated** 是 Mathlib 中的一个引理，位于命名空间 `
AlgebraicGeometry`。
形式化陈述：ext_of_isDominant_of_isSeparated [IsReduced X] {f g : X ⟶ Y} (s : Y ⟶ Z) [
IsSeparated s] (h : f ≫ s = g ≫ s) (ι : W ⟶ X) [IsDominant ι] (hU : ι ≫ f = ι ≫ 
g) : f = g
参数：s : Y ⟶ Z；h : f ≫ s = g ≫ s；ι : W ⟶ X；hU : ι ≫ f = ι ≫ g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Over.instHasEqualizers`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {B : C} [CategoryTheory.Limits.HasEqualizers C],   Categ
oryTheory.Limits.HasEqualiz…
· 使用定理 `CategoryTheory.Limits.hasLimitsOfShape_of_hasFiniteLimits`：∀ (C : Type u
) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFiniteLimi
ts C] (J : Type w)   [inst_2 : CategoryTheory.S…
· 使用定理 `AlgebraicGeometry.instHasFiniteLimitsScheme`：CategoryTheory.Limits.HasFi
niteLimits AlgebraicGeometry.Scheme
· 使用定理 `AlgebraicGeometry.IsDominant.of_comp`：∀ {X Y Z : AlgebraicGeometry.Schem
e} (f : X ⟶ Y) (g : Y ⟶ Z)   [H : AlgebraicGeometry.IsDominant (CategoryTheory.C
ategoryStruct.comp f g)], …
· 使用定理 `CategoryTheory.Over.OverMorphism.ext`：∀ {T : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} T] {X : T} {U V : CategoryTheory.Over X} {f g : U ⟶ V},  
 CategoryTheory.Over.Hom.l…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Over.comp_left`：comp_left (a b c : Over X) (f : a ⟶ b) (g
 : b ⟶ c) : (f ≫ g).left = f.left ≫ g.left
· 使用定理 `CategoryTheory.Limits.equalizer.lift_ι`：∀ {C : Type u} {X Y : C} [inst :
 CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   [inst_1 : CategoryTheory.Limi
ts.HasEqualizer f g] {W : C}…
· 使用引理 `AlgebraicGeometry.surjective_of_isDominant_of_isClosed_range`：surjective
_of_isDominant_of_isClosed_range (f : X ⟶ Y) [IsDominant f] (hf : IsClosed (Set.
range f)) : Surjective f
· 使用定理 `Topology.IsClosedEmbedding.isClosed_range`：∀ {X : Type u_1} {Y : Type u_
2} [tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.I
sClosedEmbedding f → IsClosed (…
· 使用定理 `AlgebraicGeometry.Scheme.Hom.isClosedEmbedding`：∀ {X Y : AlgebraicGeomet
ry.Scheme} (f : X ⟶ Y) [self : AlgebraicGeometry.IsClosedImmersion f],   Topolog
y.IsClosedEmbedding ⇑f
· 使用定理 `AlgebraicGeometry.isIso_of_isClosedImmersion_of_surjective`：∀ {X Y : Alg
ebraicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.IsClosedImmersion f] [Alge
braicGeometry.Surjective f]   [AlgebraicGeometry…
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.instEffectiveEpiOfIsIso`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],  
 CategoryTheory.EffectiveEpi…
· 使用定理 `CategoryTheory.Limits.equalizer.condition`：∀ {C : Type u} {X Y : C} [ins
t : CategoryTheory.Category.{v, u} C] (f g : X ⟶ Y)   [inst_1 : CategoryTheory.L
imits.HasEqualizer f g],   Cate…

--- 原说明 ---
Suppose `X` is a reduced scheme and that `f g : X ⟶ Y` agree over some separated
 `Y ⟶ Z`.
Then `f = g` if `ι ≫ f = ι ≫ g` for some dominant `ι`.
-/
lemma ext_of_isDominant_of_isSeparated [IsReduced X] {f g : X ⟶ Y}
    (s : Y ⟶ Z) [IsSeparated s] (h : f ≫ s = g ≫ s)
    (ι : W ⟶ X) [IsDominant ι] (hU : ι ≫ f = ι ≫ g) : f = g := by
  let X' : Over Z := Over.mk (f ≫ s)
  let Y' : Over Z := Over.mk s
  let U' : Over Z := Over.mk (ι ≫ f ≫ s)
  let f' : X' ⟶ Y' := Over.homMk f
  let g' : X' ⟶ Y' := Over.homMk g
  let ι' : U' ⟶ X' := Over.homMk ι
  have : IsSeparated Y'.hom := ‹_›
  have : IsDominant (equalizer.ι f' g').left := by
    apply +allowSynthFailures IsDominant.of_comp (equalizer.lift ι' ?_).left
    · rwa [← Over.comp_left, equalizer.lift_ι]
    · ext1; exact hU
  have : Surjective (equalizer.ι f' g').left :=
    surjective_of_isDominant_of_isClosed_range _ (Scheme.Hom.isClosedEmbedding _).isClosed_range
  have := isIso_of_isClosedImmersion_of_surjective (Y := X) (equalizer.ι f' g').left
  rw [← cancel_epi (equalizer.ι f' g').left]
  exact congr($(equalizer.condition f' g').left)
/-
**AlgebraicGeometry.ext_of_fromSpecResidueField_eq** 是 Mathlib 中的一个引理，位于命名空间 `Al
gebraicGeometry`。
形式化陈述：ext_of_fromSpecResidueField_eq (f g : X ⟶ Y) (i : Y ⟶ Z) [IsSeparated i] [
IsReduced X] (S : Set X) (hS' : Dense S) (H : forall x in S, X.fromSpecResidueFi
eld x ≫ f = X.fromSpecResidueField x ≫ g) (H' : f ≫ i = g ≫ i) : f = g
参数：f g : X ⟶ Y；i : Y ⟶ Z；S : Set X；hS' : Dense S；H : forall x in S, X.fromSpecRe
sidueField x ≫ f = X.fromSpecResidueField x ≫ g；H' : f ≫ i = g ≫ i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.hasLimitsOfShape_of_hasFiniteLimits`：∀ (C : Type u
) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFiniteLimi
ts C] (J : Type w)   [inst_2 : CategoryTheory.S…
· 使用定理 `AlgebraicGeometry.instHasFiniteLimitsScheme`：CategoryTheory.Limits.HasFi
niteLimits AlgebraicGeometry.Scheme
· 使用定理 `Dense.mono`：Dense.mono (h : s₁ subseteq s₂) (hd : Dense s₁) : Dense s₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.Scheme.Hom.comp_apply`：comp_apply {X Y Z : Scheme} (f 
: X ⟶ Y) (g : Y ⟶ Z) (x : X) : (f ≫ g) x = g (f x)
· 使用定理 `CategoryTheory.Limits.equalizer.lift_ι`：∀ {C : Type u} {X Y : C} [inst :
 CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   [inst_1 : CategoryTheory.Limi
ts.HasEqualizer f g] {W : C}…
· 使用引理 `AlgebraicGeometry.Scheme.fromSpecResidueField_apply`：fromSpecResidueFiel
d_apply (x : X.carrier) (s : Spec (X.residueField x)) : X.fromSpecResidueField x
 s = x
· 使用引理 `AlgebraicGeometry.ext_of_isDominant_of_isSeparated`：ext_of_isDominant_of
_isSeparated [IsReduced X] {f g : X ⟶ Y} (s : Y ⟶ Z) [IsSeparated s] (h : f ≫ s 
= g ≫ s) (ι : W ⟶ X) [IsDominant ι] (hU …
· 使用定理 `CategoryTheory.Limits.equalizer.condition`：∀ {C : Type u} {X Y : C} [ins
t : CategoryTheory.Category.{v, u} C] (f g : X ⟶ Y)   [inst_1 : CategoryTheory.L
imits.HasEqualizer f g],   Cate…
-/
lemma ext_of_fromSpecResidueField_eq (f g : X ⟶ Y) (i : Y ⟶ Z) [IsSeparated i] [IsReduced X]
    (S : Set X) (hS' : Dense S)
    (H : ∀ x ∈ S, X.fromSpecResidueField x ≫ f = X.fromSpecResidueField x ≫ g)
    (H' : f ≫ i = g ≫ i) : f = g := by
  suffices IsDominant (equalizer.ι f g) from
    ext_of_isDominant_of_isSeparated i H' (equalizer.ι f g) (equalizer.condition _ _)
  refine ⟨.mono (fun x hx ↦ ⟨equalizer.lift _ (H _ hx) default, ?_⟩) hS'⟩
  rw [← Scheme.Hom.comp_apply, equalizer.lift_ι, Scheme.fromSpecResidueField_apply]

variable (S) in
/--
Suppose `X` is a reduced `S`-scheme and `Y` is a separated `S`-scheme.
For any `S`-morphisms `f g : X ⟶ Y`, `f = g` if `ι ≫ f = ι ≫ g` for some dominant `ι`.
-/
/-
**AlgebraicGeometry.ext_of_isDominant_of_isSeparated'** 是 Mathlib 中的一个引理，位于命名空间 
`AlgebraicGeometry`。
形式化陈述：ext_of_isDominant_of_isSeparated' [X.Over S] [Y.Over S] [IsReduced X] [IsS
eparated (Y ↘ S)] {f g : X ⟶ Y} [f.IsOver S] [g.IsOver S] {W} (ι : W ⟶ X) [IsDom
inant ι] (hU : ι ≫ f = ι ≫ g) : f = g
参数：Y ↘ S；ι : W ⟶ X；hU : ι ≫ f = ι ≫ g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.ext_of_isDominant_of_isSeparated`：ext_of_isDominant_of
_isSeparated [IsReduced X] {f g : X ⟶ Y} (s : Y ⟶ Z) [IsSeparated s] (h : f ≫ s 
= g ≫ s) (ι : W ⟶ X) [IsDominant ι] (hU …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.comp_over`：comp_over [OverClass X S] [OverClass Y S] [Hom
IsOver f S] : f ≫ Y ↘ S = X ↘ S
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Suppose `X` is a reduced `S`-scheme and `Y` is a separated `S`-scheme.
For any `S`-morphisms `f g : X ⟶ Y`, `f = g` if `ι ≫ f = ι ≫ g` for some dominan
t `ι`.
-/
lemma ext_of_isDominant_of_isSeparated' [X.Over S] [Y.Over S] [IsReduced X] [IsSeparated (Y ↘ S)]
    {f g : X ⟶ Y} [f.IsOver S] [g.IsOver S] {W} (ι : W ⟶ X) [IsDominant ι]
    (hU : ι ≫ f = ι ≫ g) : f = g :=
  ext_of_isDominant_of_isSeparated (Y ↘ S) (by simp) ι hU

namespace Scheme

/-- A scheme `X` is separated if it is separated over `⊤_ Scheme`. -/
@[mk_iff]
/-
**AlgebraicGeometry.Scheme.IsSeparated** 是 Mathlib 中的一个归纳类型，位于命名空间 `AlgebraicGeo
metry.Scheme`。
形式化陈述：AlgebraicGeometry.Scheme → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A scheme `X` is separated if it is separated over `⊤_ Scheme`.
-/
protected class IsSeparated (X : Scheme.{u}) : Prop where
  isSeparated_terminal_from : IsSeparated (terminal.from X)

attribute [instance] IsSeparated.isSeparated_terminal_from

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.Scheme.isSeparated_iff_isClosedImmersion_prod_lift** 是 Mathl
ib 中的一个引理，位于命名空间 `AlgebraicGeometry.Scheme`。
形式化陈述：isSeparated_iff_isClosedImmersion_prod_lift {X : Scheme.{u}} : X.IsSeparat
ed ↔ IsClosedImmersion (prod.lift (𝟙 X) (𝟙 X))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.CartesianMonoidalCategory.instHasFiniteProducts`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.CartesianMonoid
alCategory C],   CategoryTheory.Limits.HasFiniteProd…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `AlgebraicGeometry.instHasTerminalScheme`：CategoryTheory.Limits.HasTermin
al AlgebraicGeometry.Scheme
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.isSeparated_iff`：∀ (X : AlgebraicGeometry.Schem
e), X.IsSeparated ↔ AlgebraicGeometry.IsSeparated (CategoryTheory.Limits.termina
l.from X)
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `AlgebraicGeometry.isSeparated_iff`：∀ {X Y : AlgebraicGeometry.Scheme} (f
 : X ⟶ Y),   AlgebraicGeometry.IsSeparated f ↔     autoParam (AlgebraicGeometry.
IsClosedImmersion (Cate…
· 使用定理 `iff_iff_eq`：∀ {a b : Prop}, (a ↔ b) ↔ a = b
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullbacks`：CategoryTheory.Limit
s.HasPullbacks AlgebraicGeometry.Scheme
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.MorphismProperty.cancel_right_of_respectsIso`：cancel_righ
t_of_respectsIso (P : MorphismProperty C) [hP : RespectsIso P] {X Y Z : C} (f : 
X ⟶ Y) (g : Y ⟶ Z) [IsIso g] : P (f ≫ g) ↔ P f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.Limits.pullback.hom_ext`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categor
yTheory.Limits.HasPullback f…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Limits.pullback.diagonal_fst`：diagonal_fst : diagonal f ≫
 pullback.fst _ _ = 𝟙 _
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `prodIsoPullback_hom_fst`：prodIsoPullback_hom_fst [HasTerminal C] [HasPul
lbacks C] (X Y : C) [HasBinaryProduct X Y] : (prodIsoPullback X Y).hom ≫ pullbac
k.fst _ _ = p…
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.pullback.diagonal_snd`：diagonal_snd : diagonal f ≫
 pullback.snd _ _ = 𝟙 _
· 使用引理 `prodIsoPullback_hom_snd`：prodIsoPullback_hom_snd [HasTerminal C] [HasPul
lbacks C] (X Y : C) [HasBinaryProduct X Y] : (prodIsoPullback X Y).hom ≫ pullbac
k.snd _ _ = p…
-/
lemma isSeparated_iff_isClosedImmersion_prod_lift {X : Scheme.{u}} :
    X.IsSeparated ↔ IsClosedImmersion (prod.lift (𝟙 X) (𝟙 X)) := by
  rw [isSeparated_iff, AlgebraicGeometry.isSeparated_iff, iff_iff_eq,
    ← MorphismProperty.cancel_right_of_respectsIso @IsClosedImmersion _ (prodIsoPullback X X).hom]
  congr
  ext : 1 <;> simp
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [X.IsSeparated] : IsClosedImmersion (prod.lift (𝟙 X) (𝟙 X)) := by
  rwa [← isSeparated_iff_isClosedImmersion_prod_lift]
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 900) {X : Scheme.{u}} [IsAffine X] : X.IsSeparated := ⟨inferInstance⟩
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) {X : Scheme.{u}} [X.IsSeparated] : QuasiSeparatedSpace X :=
  quasiSeparatedSpace_of_quasiSeparated (terminal.from X)
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 900) [X.IsSeparated] : IsSeparated f := by
  apply +allowSynthFailures @IsSeparated.of_comp (g := terminal.from Y)
  rw [terminal.comp_from]
  infer_instance
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (f g : X ⟶ Y) [Y.IsSeparated] : IsClosedImmersion (Limits.equalizer.ι f g) :=
  MorphismProperty.of_isPullback (isPullback_equalizer_prod f g).flip inferInstance

end Scheme

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.IsSeparated.hasAffineProperty** 是 Mathlib 中的一个定理，位于命名空间 `Alg
ebraicGeometry.IsSeparated`。
形式化陈述：AlgebraicGeometry.HasAffineProperty @AlgebraicGeometry.IsSeparated fun X x
 x_1 x_2 => X.IsSeparated
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `AlgebraicGeometry.instHasTerminalScheme`：CategoryTheory.Limits.HasTermin
al AlgebraicGeometry.Scheme
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.isSeparated_iff`：∀ (X : AlgebraicGeometry.Schem
e), X.IsSeparated ↔ AlgebraicGeometry.IsSeparated (CategoryTheory.Limits.termina
l.from X)
· 使用定理 `CategoryTheory.Limits.terminal.comp_from`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Limits.HasTerminal C] {P 
Q : C}   (f : P ⟶ Q),   Catego…
· 使用定理 `AlgebraicGeometry.IsSeparated.comp_iff`：∀ {X Y Z : AlgebraicGeometry.Sch
eme} {f : X ⟶ Y} {g : Y ⟶ Z} [AlgebraicGeometry.IsSeparated g],   AlgebraicGeome
try.IsSeparated (CategoryThe…
· 使用定理 `AlgebraicGeometry.Scheme.IsSeparated.isSeparated_terminal_from`：∀ {X : A
lgebraicGeometry.Scheme} [self : X.IsSeparated],   AlgebraicGeometry.IsSeparated
 (CategoryTheory.Limits.terminal.from X)
· 使用定理 `AlgebraicGeometry.Scheme.instIsSeparatedOfIsAffine`：∀ {X : AlgebraicGeom
etry.Scheme} [AlgebraicGeometry.IsAffine X], X.IsSeparated
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `AlgebraicGeometry.HasAffineProperty.of_isZariskiLocalAtTarget`：∀ (P : Ca
tegoryTheory.MorphismProperty AlgebraicGeometry.Scheme) [AlgebraicGeometry.IsZar
iskiLocalAtTarget P],   AlgebraicGeometry.HasAffine…
· 使用定理 `AlgebraicGeometry.IsSeparated.instIsZariskiLocalAtTarget`：AlgebraicGeome
try.IsZariskiLocalAtTarget @AlgebraicGeometry.IsSeparated
-/
instance IsSeparated.hasAffineProperty :
    HasAffineProperty @IsSeparated fun X _ _ _ ↦ X.IsSeparated := by
  convert! HasAffineProperty.of_isZariskiLocalAtTarget @IsSeparated with X Y f hY
  rw [Scheme.isSeparated_iff, ← terminal.comp_from f, IsSeparated.comp_iff]
  rfl

/--
Suppose `f g : X ⟶ Y` where `X` is a reduced scheme and `Y` is a separated scheme.
Then `f = g` if `ι ≫ f = ι ≫ g` for some dominant `ι`.

Also see `ext_of_isDominant_of_isSeparated` for the general version over arbitrary bases.
-/
/-
**AlgebraicGeometry.ext_of_isDominant** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeomet
ry`。
形式化陈述：ext_of_isDominant [IsReduced X] {f g : X ⟶ Y} [Y.IsSeparated] (ι : W ⟶ X) 
[IsDominant ι] (hU : ι ≫ f = ι ≫ g) : f = g
参数：ι : W ⟶ X；hU : ι ≫ f = ι ≫ g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.ext_of_isDominant_of_isSeparated`：ext_of_isDominant_of
_isSeparated [IsReduced X] {f g : X ⟶ Y} (s : Y ⟶ Z) [IsSeparated s] (h : f ≫ s 
= g ≫ s) (ι : W ⟶ X) [IsDominant ι] (hU …
· 使用定理 `AlgebraicGeometry.instHasTerminalScheme`：CategoryTheory.Limits.HasTermin
al AlgebraicGeometry.Scheme
· 使用定理 `AlgebraicGeometry.Scheme.IsSeparated.isSeparated_terminal_from`：∀ {X : A
lgebraicGeometry.Scheme} [self : X.IsSeparated],   AlgebraicGeometry.IsSeparated
 (CategoryTheory.Limits.terminal.from X)
· 使用定理 `CategoryTheory.Limits.terminal.hom_ext`：∀ {C : Type u₁} [inst : Category
Theory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Limits.HasTerminal C] {P : 
C}   (f g : P ⟶ ⊤_ C), f = g

--- 原说明 ---
Suppose `f g : X ⟶ Y` where `X` is a reduced scheme and `Y` is a separated schem
e.
Then `f = g` if `ι ≫ f = ι ≫ g` for some dominant `ι`.

Also see `ext_of_isDominant_of_isSeparated` for the general version over arbitra
ry bases.
-/
lemma ext_of_isDominant [IsReduced X] {f g : X ⟶ Y} [Y.IsSeparated]
    (ι : W ⟶ X) [IsDominant ι] (hU : ι ≫ f = ι ≫ g) : f = g :=
  ext_of_isDominant_of_isSeparated (Limits.terminal.from _) (Limits.terminal.hom_ext _ _) ι hU

end AlgebraicGeometry

