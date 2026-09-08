/-
Copyright (c) 2024 Christian Merten, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten, Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!

# Proper morphisms

A morphism of schemes is proper if it is separated, universally closed and (locally) of finite type.
Note that we don't require quasi-compact, since this is implied by universally closed.

## Main results
- `AlgebraicGeometry.isField_of_universallyClosed`:
  If `X` is an integral scheme that is universally closed over `Spec K`, then `Γ(X, ⊤)` is a field.
- `AlgebraicGeometry.finite_appTop_of_universallyClosed`:
  If `X` is an integral scheme that is universally closed and of finite type over `Spec K`,
  then `Γ(X, ⊤)` is finite dimensional over `K`.

-/

public section


noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {X Y Z S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- A morphism is proper if it is separated, universally closed and locally of finite type. -/
@[mk_iff]
/-
**AlgebraicGeometry.IsProper** 是 Mathlib 中的一个归纳类型，位于命名空间 `AlgebraicGeometry`。
形式化陈述：{X Y : AlgebraicGeometry.Scheme} → (X ⟶ Y) → Prop
参数：X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism is proper if it is separated, universally closed and locally of finit
e type.
-/
class IsProper : Prop extends IsSeparated f, UniversallyClosed f, LocallyOfFiniteType f where
/-
**AlgebraicGeometry.isProper_eq** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry`。
形式化陈述：isProper_eq : @IsProper = (@IsSeparated ⊓ @UniversallyClosed : MorphismPro
perty Scheme) ⊓ @LocallyOfFiniteType
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.isProper_iff`：∀ {X Y : AlgebraicGeometry.Scheme} (f : 
X ⟶ Y),   AlgebraicGeometry.IsProper f ↔     AlgebraicGeometry.IsSeparated f ∧ A
lgebraicGeometry.Uni…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `and_assoc`：∀ {a b c : Prop}, (a ∧ b) ∧ c ↔ a ∧ b ∧ c
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isProper_eq : @IsProper =
    (@IsSeparated ⊓ @UniversallyClosed : MorphismProperty Scheme) ⊓ @LocallyOfFiniteType := by
  ext X Y f
  rw [isProper_iff, ← and_assoc]
  rfl

namespace IsProper

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.IsProper.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.IsPro
per`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MorphismProperty.RespectsIso @IsProper := by
  rw [isProper_eq]
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.IsProper.stableUnderComposition** 是 Mathlib 中的一个实例，位于命名空间 `A
lgebraicGeometry.IsProper`。
形式化陈述：stableUnderComposition : MorphismProperty.IsStableUnderComposition @IsProp
er
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.isProper_eq`：isProper_eq : @IsProper = (@IsSeparated ⊓
 @UniversallyClosed : MorphismProperty Scheme) ⊓ @LocallyOfFiniteType
· 使用定理 `CategoryTheory.MorphismProperty.IsStableUnderComposition.inf`：∀ {C : Typ
e u} [inst : CategoryTheory.Category.{v, u} C] {P Q : CategoryTheory.MorphismPro
perty C}   [P.IsStableUnderComposition] [Q.IsStabl…
· 使用定理 `AlgebraicGeometry.instIsStableUnderCompositionSchemeLocallyOfFiniteType`
：CategoryTheory.MorphismProperty.IsStableUnderComposition @AlgebraicGeometry.Loc
allyOfFiniteType
-/
instance stableUnderComposition : MorphismProperty.IsStableUnderComposition @IsProper := by
  rw [isProper_eq]
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.IsProper.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.IsPro
per`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MorphismProperty.IsMultiplicative @IsProper := by
  rw [isProper_eq]
  infer_instance
/-
**AlgebraicGeometry.IsProper.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.IsPro
per`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsProper f] [IsProper g] : IsProper (f ≫ g) where
/-
**AlgebraicGeometry.IsProper.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.IsPro
per`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 900) [IsFinite f] : IsProper f where

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.IsProper.isStableUnderBaseChange** 是 Mathlib 中的一个实例，位于命名空间 `
AlgebraicGeometry.IsProper`。
形式化陈述：isStableUnderBaseChange : MorphismProperty.IsStableUnderBaseChange @IsProp
er
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.isProper_eq`：isProper_eq : @IsProper = (@IsSeparated ⊓
 @UniversallyClosed : MorphismProperty Scheme) ⊓ @LocallyOfFiniteType
· 使用定理 `CategoryTheory.MorphismProperty.IsStableUnderBaseChange.inf`：∀ {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C] {P Q : CategoryTheory.MorphismProp
erty C}   [P.IsStableUnderBaseChange] [Q.IsStable…
-/
instance isStableUnderBaseChange : MorphismProperty.IsStableUnderBaseChange @IsProper := by
  rw [isProper_eq]
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.IsProper.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.IsPro
per`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsZariskiLocalAtTarget @IsProper := by
  rw [isProper_eq]
  infer_instance
/-
**AlgebraicGeometry.IsProper.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.IsPro
per`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (f : X ⟶ S) (g : Y ⟶ S) [IsProper g] : IsProper (Limits.pullback.fst f g) where
/-
**AlgebraicGeometry.IsProper.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.IsPro
per`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (f : X ⟶ S) (g : Y ⟶ S) [IsProper f] : IsProper (Limits.pullback.snd f g) where
/-
**AlgebraicGeometry.IsProper.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.IsPro
per`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (f : X ⟶ Y) (V : Y.Opens) [IsProper f] : IsProper (f ∣_ V) where

end IsProper

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.IsFinite.eq_isProper_inf_isAffineHom** 是 Mathlib 中的一个定理，位于命名
空间 `AlgebraicGeometry.IsFinite`。
形式化陈述：@AlgebraicGeometry.IsFinite = @AlgebraicGeometry.IsProper ⊓ @AlgebraicGeom
etry.IsAffineHom
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inf_eq_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b =
 a ↔ a ≤ b
· 使用引理 `AlgebraicGeometry.IsSeparated.of_isAffineHom`：of_isAffineHom [h : IsAffi
neHom f] : IsSeparated f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
· 使用引理 `AlgebraicGeometry.isProper_eq`：isProper_eq : @IsProper = (@IsSeparated ⊓
 @UniversallyClosed : MorphismProperty Scheme) ⊓ @LocallyOfFiniteType
· 使用定理 `inf_assoc`：∀ {α : Type u} [inst : SemilatticeInf α] (a b c : α), a ⊓ b ⊓
 c = a ⊓ (b ⊓ c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `AlgebraicGeometry.IsFinite.eq_inf`：eq_inf : @IsFinite = (@IsIntegralHom 
⊓ @LocallyOfFiniteType : MorphismProperty Scheme)
· 使用引理 `AlgebraicGeometry.IsIntegralHom.eq_universallyClosed_inf_isAffineHom`：eq
_universallyClosed_inf_isAffineHom : @IsIntegralHom = (@UniversallyClosed ⊓ @IsA
ffineHom : MorphismProperty Scheme)
· 使用定理 `inf_left_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b c : α), a ⊓
 (b ⊓ c) = b ⊓ (a ⊓ c)
-/
lemma IsFinite.eq_isProper_inf_isAffineHom :
    @IsFinite = (@IsProper ⊓ @IsAffineHom : MorphismProperty _) := by
  have : (@IsAffineHom ⊓ @IsSeparated : MorphismProperty _) = @IsAffineHom :=
    inf_eq_left.mpr fun _ _ _ _ ↦ inferInstance
  rw [inf_comm, isProper_eq, inf_assoc, ← inf_assoc, this, eq_inf,
    IsIntegralHom.eq_universallyClosed_inf_isAffineHom, inf_assoc, inf_left_comm]

variable {f} in
/-
**AlgebraicGeometry.IsFinite.iff_isProper_and_isAffineHom** 是 Mathlib 中的一个定理，位于命
名空间 `AlgebraicGeometry.IsFinite`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} {f : X ⟶ Y},   AlgebraicGeometry.IsFini
te f ↔ AlgebraicGeometry.IsProper f ∧ AlgebraicGeometry.IsAffineHom f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.IsFinite.eq_isProper_inf_isAffineHom`：@AlgebraicGeomet
ry.IsFinite = @AlgebraicGeometry.IsProper ⊓ @AlgebraicGeometry.IsAffineHom
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma IsFinite.iff_isProper_and_isAffineHom :
    IsFinite f ↔ IsProper f ∧ IsAffineHom f := by
  rw [eq_isProper_inf_isAffineHom]
  rfl
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) [IsFinite f] : IsProper f :=
  (IsFinite.iff_isProper_and_isAffineHom.mp ‹_›).1
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MorphismProperty.HasOfPostcompProperty @UniversallyClosed @IsSeparated :=
  MorphismProperty.hasOfPostcompProperty_iff_le_diagonal.mpr
    fun _ _ _ _ ↦ inferInstanceAs (UniversallyClosed _)

@[stacks 01W6 "(1)"]
/-
**AlgebraicGeometry.UniversallyClosed.of_comp_of_isSeparated** 是 Mathlib 中的一个定理，
位于命名空间 `AlgebraicGeometry.UniversallyClosed`。
形式化陈述：∀ {X Y Z : AlgebraicGeometry.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)   [AlgebraicG
eometry.UniversallyClosed (CategoryTheory.CategoryStruct.comp f g)] [AlgebraicGe
ometry.IsSeparated g],   AlgebraicGeometry.UniversallyClosed f
参数：f : X ⟶ Y；g : Y ⟶ Z；CategoryTheory.CategoryStruct.comp f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.of_postcomp`：of_postcomp [W.HasOfPostcom
pProperty W'] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hg : W' g) (hfg : W (f ≫ g)) 
: W f
· 使用定理 `AlgebraicGeometry.instHasOfPostcompPropertySchemeUniversallyClosedIsSepa
rated`：CategoryTheory.MorphismProperty.HasOfPostcompProperty @AlgebraicGeometry.
UniversallyClosed   @AlgebraicGeometry.IsSeparated
-/
lemma UniversallyClosed.of_comp_of_isSeparated [UniversallyClosed (f ≫ g)] [IsSeparated g] :
    UniversallyClosed f :=
  MorphismProperty.of_postcomp _ _ g ‹_› ‹_›
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MorphismProperty.HasOfPostcompProperty @IsProper @IsSeparated :=
  MorphismProperty.hasOfPostcompProperty_iff_le_diagonal.mpr
    fun _ _ _ _ ↦ inferInstanceAs (IsProper _)
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [UniversallyClosed f] : UniversallyClosed f.toImage :=
  have : UniversallyClosed (f.toImage ≫ f.imageι) := by simpa
  .of_comp_of_isSeparated _ f.imageι

@[stacks 01W6 "(2)"]
/-
**AlgebraicGeometry.IsProper.of_comp** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometr
y.IsProper`。
形式化陈述：∀ {X Y Z : AlgebraicGeometry.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)   [AlgebraicG
eometry.IsProper (CategoryTheory.CategoryStruct.comp f g)] [AlgebraicGeometry.Is
Separated g],   AlgebraicGeometry.IsProper f
参数：f : X ⟶ Y；g : Y ⟶ Z；CategoryTheory.CategoryStruct.comp f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.of_postcomp`：of_postcomp [W.HasOfPostcom
pProperty W'] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hg : W' g) (hfg : W (f ≫ g)) 
: W f
· 使用定理 `AlgebraicGeometry.instHasOfPostcompPropertySchemeIsProperIsSeparated`：Ca
tegoryTheory.MorphismProperty.HasOfPostcompProperty @AlgebraicGeometry.IsProper 
@AlgebraicGeometry.IsSeparated
-/
lemma IsProper.of_comp [IsProper (f ≫ g)] [IsSeparated g] : IsProper f :=
  MorphismProperty.of_postcomp _ _ g ‹_› ‹_›
/-
**AlgebraicGeometry.IsProper.comp_iff** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeomet
ry.IsProper`。
形式化陈述：∀ {X Y Z : AlgebraicGeometry.Scheme} {f : X ⟶ Y} {g : Y ⟶ Z} [AlgebraicGeo
metry.IsProper g],   AlgebraicGeometry.IsProper (CategoryTheory.CategoryStruct.c
omp f g) ↔ AlgebraicGeometry.IsProper f
参数：CategoryTheory.CategoryStruct.comp f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.IsProper.of_comp`：∀ {X Y Z : AlgebraicGeometry.Scheme}
 (f : X ⟶ Y) (g : Y ⟶ Z)   [AlgebraicGeometry.IsProper (CategoryTheory.CategoryS
truct.comp f g)] [Algebr…
· 使用定理 `AlgebraicGeometry.IsProper.toIsSeparated`：∀ {X Y : AlgebraicGeometry.Sch
eme} {f : X ⟶ Y} [self : AlgebraicGeometry.IsProper f], AlgebraicGeometry.IsSepa
rated f
· 使用定理 `AlgebraicGeometry.IsProper.instCompScheme`：∀ {X Y Z : AlgebraicGeometry.
Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [AlgebraicGeometry.IsProper f]   [AlgebraicGeome
try.IsProper g], AlgebraicGeome…
-/
lemma IsProper.comp_iff {f : X ⟶ Y} {g : Y ⟶ Z} [IsProper g] :
    IsProper (f ≫ g) ↔ IsProper f :=
  ⟨fun _ ↦ .of_comp f g, fun _ ↦ inferInstance⟩

section GlobalSection

variable (K : Type u) [Field K]

set_option backward.isDefEq.respectTransparency.types false in
/-- If `f : X ⟶ Y` is universally closed and `Y` is affine,
then the map on global sections is integral. -/
/-
**AlgebraicGeometry.isIntegral_appTop_of_universallyClosed** 是 Mathlib 中的一个定理，位于
命名空间 `AlgebraicGeometry`。
形式化陈述：isIntegral_appTop_of_universallyClosed (f : X ⟶ Y) [UniversallyClosed f] [
IsAffine Y] : f.appTop.hom.IsIntegral
参数：f : X ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AlgebraicGeometry.quasiCompact_iff_compactSpace`：quasiCompact_iff_compac
tSpace (f : X ⟶ Y) [QuasiSeparatedSpace Y] [CompactSpace Y] : QuasiCompact f ↔ C
ompactSpace X
· 使用定理 `AlgebraicGeometry.Scheme.compactSpace_of_isAffine`：∀ (X : AlgebraicGeome
try.Scheme) [AlgebraicGeometry.IsAffine X], CompactSpace ↥X
· 使用定理 `AlgebraicGeometry.instQuasiCompactOfUniversallyClosed`：∀ {X Y : Algebrai
cGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.UniversallyClosed f], Algebraic
Geometry.QuasiCompact f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.Scheme.toSpecΓ_naturality`：∀ {X Y : AlgebraicGeometry.
Scheme} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.comp f Y.toSpecΓ =     Cate
goryTheory.CategoryStruct.comp X.…
· 使用定理 `CategoryTheory.MorphismProperty.cancel_right_of_respectsIso`：cancel_righ
t_of_respectsIso (P : MorphismProperty C) [hP : RespectsIso P] {X Y Z : C} (f : 
X ⟶ Y) (g : Y ⟶ Z) [IsIso g] : P (f ≫ g) ↔ P f
· 使用定理 `CategoryTheory.MorphismProperty.IsLocalAtTarget.toRespects`：∀ {C : Type 
u} {inst : CategoryTheory.Category.{v, u} C} {P : CategoryTheory.MorphismPropert
y C}   (K : CategoryTheory.Precoverage C) [self …
· 使用定理 `AlgebraicGeometry.IsAffine.affine`：∀ {X : AlgebraicGeometry.Scheme} [sel
f : AlgebraicGeometry.IsAffine X], CategoryTheory.IsIso X.toSpecΓ
· 使用定理 `AlgebraicGeometry.UniversallyClosed.of_comp_of_isSeparated`：∀ {X Y Z : A
lgebraicGeometry.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)   [AlgebraicGeometry.Universall
yClosed (CategoryTheory.CategoryStruct.comp f g)…
· 使用定理 `AlgebraicGeometry.IsSeparated.instMap`：∀ (R S : CommRingCat) (f : R ⟶ S)
, AlgebraicGeometry.IsSeparated (AlgebraicGeometry.Spec.map f)
· 使用引理 `AlgebraicGeometry.IsIntegralHom.SpecMap_iff`：SpecMap_iff {R S : CommRing
Cat} {φ : R ⟶ S} : IsIntegralHom (Spec.map φ) ↔ φ.hom.IsIntegral
· 使用引理 `AlgebraicGeometry.IsIntegralHom.iff_universallyClosed_and_isAffineHom`：i
ff_universallyClosed_and_isAffineHom {X Y : Scheme.{u}} {f : X ⟶ Y} : IsIntegral
Hom f ↔ UniversallyClosed f ∧ IsAffineHom f
· 使用定理 `AlgebraicGeometry.UniversallyClosed.of_comp_surjective`：∀ {X Y Z : Algeb
raicGeometry.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)   [AlgebraicGeometry.UniversallyClo
sed (CategoryTheory.CategoryStruct.comp f g)…
· 使用定理 `AlgebraicGeometry.Surjective.of_universallyClosed_of_isDominant`：∀ {X Y 
: AlgebraicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.UniversallyClosed f] 
[AlgebraicGeometry.IsDominant f],   AlgebraicGeometry…
· 使用定理 `AlgebraicGeometry.instIsDominantToSpecΓOfCompactSpaceCarrierCarrierCommR
ingCat`：∀ {X : AlgebraicGeometry.Scheme} [CompactSpace ↥X], AlgebraicGeometry.Is
Dominant X.toSpecΓ
· 使用定理 `AlgebraicGeometry.isAffineHom_of_isAffine`：∀ {X Y : AlgebraicGeometry.Sc
heme} (f : X ⟶ Y) [AlgebraicGeometry.IsAffine X] [AlgebraicGeometry.IsAffine Y],
   AlgebraicGeometry.IsAffineHo…

--- 原说明 ---
If `f : X ⟶ Y` is universally closed and `Y` is affine,
then the map on global sections is integral.
-/
theorem isIntegral_appTop_of_universallyClosed (f : X ⟶ Y) [UniversallyClosed f] [IsAffine Y] :
    f.appTop.hom.IsIntegral := by
  have : CompactSpace X := (quasiCompact_iff_compactSpace f).mp inferInstance
  have : UniversallyClosed (X.toSpecΓ ≫ Spec.map f.appTop) := by
    rwa [← Scheme.toSpecΓ_naturality,
      MorphismProperty.cancel_right_of_respectsIso (P := @UniversallyClosed)]
  have : UniversallyClosed X.toSpecΓ := .of_comp_of_isSeparated _ (Spec.map f.appTop)
  rw [← IsIntegralHom.SpecMap_iff, IsIntegralHom.iff_universallyClosed_and_isAffineHom]
  exact ⟨.of_comp_surjective X.toSpecΓ _, inferInstance⟩

/-- If `X` is an integral scheme that is universally closed over `Spec K`,
then `Γ(X, ⊤)` is a field. -/
/-
**AlgebraicGeometry.isField_of_universallyClosed** 是 Mathlib 中的一个定理，位于命名空间 `Alge
braicGeometry`。
形式化陈述：isField_of_universallyClosed (f : X ⟶ (Spec <| .of K)) [IsIntegral X] [Uni
versallyClosed f] : IsField Γ(X, ⊤)
参数：f : X ⟶ (Spec <| .of K)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `RingHom.isIntegral_respectsIso`：isIntegral_respectsIso : RespectsIso fun
 f => f.IsIntegral
· 使用定理 `AlgebraicGeometry.isIntegral_appTop_of_universallyClosed`：isIntegral_app
Top_of_universallyClosed (f : X ⟶ Y) [UniversallyClosed f] [IsAffine Y] : f.appT
op.hom.IsIntegral
· 使用定理 `isField_of_isIntegral_of_isField'`：isField_of_isIntegral_of_isField' [Co
mmRing R] [CommRing S] [IsDomain S] [Algebra R S] [Algebra.IsIntegral R S] (hR :
 IsField R) : IsField S…
· 使用定理 `AlgebraicGeometry.instIsDomainCarrierObjOppositeOpensCarrierCarrierCommR
ingCatPresheafOpOpensTopOfIsIntegral`：∀ (X : AlgebraicGeometry.Scheme) [Algebrai
cGeometry.IsIntegral X], IsDomain ↑(X.presheaf.obj (Opposite.op ⊤))
· 使用定理 `Field.toIsField`：Field.toIsField (R : Type u) [Field R] : IsField R

--- 原说明 ---
If `X` is an integral scheme that is universally closed over `Spec K`,
then `Γ(X, ⊤)` is a field.
-/
theorem isField_of_universallyClosed (f : X ⟶ (Spec <| .of K))
    [IsIntegral X] [UniversallyClosed f] : IsField Γ(X, ⊤) := by
  let F := (Scheme.ΓSpecIso _).inv ≫ f.appTop
  have : F.hom.IsIntegral := by
    apply RingHom.isIntegral_respectsIso.2 (e := (Scheme.ΓSpecIso _).symm.commRingCatIsoToRingEquiv)
    exact isIntegral_appTop_of_universallyClosed f
  algebraize [F.hom]
  exact isField_of_isIntegral_of_isField' (Field.toIsField K)

/-- If `X` is an integral scheme that is universally closed and of finite type over `Spec K`,
then `Γ(X, ⊤)` is a finite field extension over `K`. -/
/-
**AlgebraicGeometry.finite_appTop_of_universallyClosed** 是 Mathlib 中的一个定理，位于命名空间
 `AlgebraicGeometry`。
形式化陈述：finite_appTop_of_universallyClosed (f : X ⟶ (Spec <| .of K)) [IsIntegral X
] [UniversallyClosed f] [LocallyOfFiniteType f] : f.appTop.hom.Finite
参数：f : X ⟶ (Spec <| .of K)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.IsIntegral.nonempty`：∀ {X : AlgebraicGeometry.Scheme} 
[self : AlgebraicGeometry.IsIntegral X], Nonempty ↥X
· 使用定理 `TopologicalSpace.IsTopologicalBasis.exists_subset_of_mem_open`：∀ {α : Ty
pe u} [t : TopologicalSpace α] {b : Set (Set α)},   TopologicalSpace.IsTopologic
alBasis b → ∀ {a : α} {u : Set α}, a ∈ u → IsOpen u…
· 使用定理 `AlgebraicGeometry.Scheme.isBasis_affineOpens`：∀ (X : AlgebraicGeometry.S
cheme), TopologicalSpace.Opens.IsBasis X.affineOpens
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `isOpen_univ`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen Set.univ
· 使用定理 `MulEquiv.isField`：∀ {A : Type u_1} {B : Type u_2} [inst : Semiring A] [i
nst_1 : Semiring B], IsField B → ∀ (e : A ≃* B), IsField A
· 使用定理 `Field.toIsField`：Field.toIsField (R : Type u) [Field R] : IsField R
· 使用定理 `AlgebraicGeometry.isField_of_universallyClosed`：isField_of_universallyCl
osed (f : X ⟶ (Spec <| .of K)) [IsIntegral X] [UniversallyClosed f] : IsField Γ(
X, ⊤)
· 使用定理 `RingHom.finite_of_algHom_finiteType_of_isJacobsonRing`：∀ {K : Type u_1} 
{L : Type u_2} {A : Type u_3} [inst : CommRing K] [inst_1 : Field L] [inst_2 : C
ommRing A]   [IsJacobsonRing K] [IsNoetheri…
· 使用定理 `instIsJacobsonRingOfKrullDimLEOfNatNat`：∀ {R : Type u_1} [inst : CommRin
g R] [Ring.KrullDimLE 0 R], IsJacobsonRing R
· 使用定理 `IsArtinianRing.instKrullDimLEOfNatNat`：∀ (R : Type u_1) [inst : CommRing
 R] [IsArtinianRing R], Ring.KrullDimLE 0 R
· 使用定理 `IsSimpleModule.instIsNoetherian`：∀ (R : Type u_2) [inst : Ring R] {M : T
ype u_4} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimpleModul
e R M], IsNoetherian …
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `AlgebraicGeometry.Scheme.component_nontrivial`：∀ (X : AlgebraicGeometry.
Scheme) (U : X.Opens) [Nonempty ↥↑U], Nontrivial ↑(X.presheaf.obj (Opposite.op U
))
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `AlgebraicGeometry.Scheme.Hom.finiteType_appLE`：∀ {X Y : AlgebraicGeometr
y.Scheme} (f : X ⟶ Y) [self : AlgebraicGeometry.LocallyOfFiniteType f] {U : Y.Op
ens},   AlgebraicGeometry.IsAffineO…
· 使用定理 `AlgebraicGeometry.isAffineOpen_top`：isAffineOpen_top (X : Scheme) [IsAff
ine X] : IsAffineOpen (⊤ : X.Opens)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p

--- 原说明 ---
If `X` is an integral scheme that is universally closed and of finite type over 
`Spec K`,
then `Γ(X, ⊤)` is a finite field extension over `K`.
-/
theorem finite_appTop_of_universallyClosed (f : X ⟶ (Spec <| .of K))
    [IsIntegral X] [UniversallyClosed f] [LocallyOfFiniteType f] :
    f.appTop.hom.Finite := by
  have x : X := Nonempty.some inferInstance
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let := ((Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.toMulEquiv.isField
    (Field.toIsField K)).toField
  let := (isField_of_universallyClosed K f).toField
  have : Nonempty U := ⟨⟨x, hxU⟩⟩
  apply RingHom.finite_of_algHom_finiteType_of_isJacobsonRing (A := Γ(X, U))
    (g := (X.presheaf.map (homOfLE le_top).op).hom)
  exact f.finiteType_appLE (isAffineOpen_top _) hU (by simp)

end GlobalSection

end AlgebraicGeometry

