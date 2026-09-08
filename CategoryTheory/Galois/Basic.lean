/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Group.TransferInstance
public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
public import Mathlib.CategoryTheory.Limits.FintypeCat
public import Mathlib.CategoryTheory.Limits.MonoCoprod
public import Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory
public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
public import Mathlib.CategoryTheory.Limits.Types.Equalizers
public import Mathlib.CategoryTheory.SingleObj
public import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Definition and basic properties of Galois categories

We define the notion of a Galois category and a fiber functor as in SGA1, following
the definitions in Lenstra's notes (see below for a reference).

## Main definitions

* `PreGaloisCategory` : defining properties of Galois categories not involving a fiber functor
* `FiberFunctor`      : a fiber functor from a `PreGaloisCategory` to `FintypeCat`
* `GaloisCategory`    : a `PreGaloisCategory` that admits a `FiberFunctor`
* `IsConnected`       : an object of a category is connected if it is not initial
                        and does not have non-trivial subobjects

Any fiber functor `F` induces an equivalence with the category of finite, discrete `Aut F`-types.
This is proven in `Mathlib/CategoryTheory/Galois/Equivalence.lean`.

## Implementation details

We mostly follow Def 3.1 in Lenstra's notes. In axiom (G3)
we omit the factorisation of morphisms into epimorphisms and monomorphisms
as this is not needed for the proof of the fundamental theorem on Galois categories
(and then follows from it).

## References

* [lenstraGSchemes]: H. W. Lenstra. Galois theory for schemes.

-/

@[expose] public section

universe u₁ u₂ v₁ v₂ w t

namespace CategoryTheory

open Limits CategoryTheory.Functor

/-!
A category `C` is a PreGalois category if it satisfies all properties
of a Galois category in the sense of SGA1 that do not involve a fiber functor.
A Galois category should furthermore admit a fiber functor.

The only difference between `[PreGaloisCategory C] (F : C ⥤ FintypeCat) [FiberFunctor F]` and
`[GaloisCategory C]` is that the former fixes one fiber functor `F`.
-/

/-- Definition of a (Pre)Galois category. Lenstra, Def 3.1, (G1)-(G3) -/
/-
**CategoryTheory.PreGaloisCategory** 是 Mathlib 中的一个类，位于命名空间 `CategoryTheory`。
形式化陈述：PreGaloisCategory (C : Type u₁) [Category.{u₂, u₁} C] : Prop where /-- `C`
 has a terminal object (G1). -/ hasTerminal : HasTerminal C
参数：C : Type u₁。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Definition of a (Pre)Galois category. Lenstra, Def 3.1, (G1)-(G3)
-/
class PreGaloisCategory (C : Type u₁) [Category.{u₂, u₁} C] : Prop where
  /-- `C` has a terminal object (G1). -/
  hasTerminal : HasTerminal C := by infer_instance
  /-- `C` has pullbacks (G1). -/
  hasPullbacks : HasPullbacks C := by infer_instance
  /-- `C` has finite coproducts (G2). -/
  hasFiniteCoproducts : HasFiniteCoproducts C := by infer_instance
  /-- `C` has quotients by finite groups (G2). -/
  hasQuotientsByFiniteGroups (G : Type u₂) [Group G] [Finite G] :
    HasColimitsOfShape (SingleObj G) C := by infer_instance
  /-- Every monomorphism in `C` induces an isomorphism on a direct summand (G3). -/
  monoInducesIsoOnDirectSummand {X Y : C} (i : X ⟶ Y) [Mono i] : ∃ (Z : C) (u : Z ⟶ Y),
    Nonempty (IsColimit (BinaryCofan.mk i u))

namespace PreGaloisCategory

/-- Definition of a fiber functor from a Galois category. Lenstra, Def 3.1, (G4)-(G6) -/
/-
**CategoryTheory.PreGaloisCategory.FiberFunctor** 是 Mathlib 中的一个类，位于命名空间 `Catego
ryTheory.PreGaloisCategory`。
形式化陈述：FiberFunctor {C : Type u₁} [Category.{u₂, u₁} C] [PreGaloisCategory C] (F 
: C ⥤ FintypeCat.{w}) where /-- `F` preserves terminal objects (G4). -/ preserve
sTerminalObjects : PreservesLimitsOfShape (CategoryTheory.Discrete PEmpty.{1}) F
参数：F : C ⥤ FintypeCat.{w}；G4。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Definition of a fiber functor from a Galois category. Lenstra, Def 3.1, (G4)-(G6
)
-/
class FiberFunctor {C : Type u₁} [Category.{u₂, u₁} C] [PreGaloisCategory C]
    (F : C ⥤ FintypeCat.{w}) where
  /-- `F` preserves terminal objects (G4). -/
  preservesTerminalObjects : PreservesLimitsOfShape (CategoryTheory.Discrete PEmpty.{1}) F := by
    infer_instance
  /-- `F` preserves pullbacks (G4). -/
  preservesPullbacks : PreservesLimitsOfShape WalkingCospan F := by infer_instance
  /-- `F` preserves finite coproducts (G5). -/
  preservesFiniteCoproducts : PreservesFiniteCoproducts F := by infer_instance
  /-- `F` preserves epimorphisms (G5). -/
  preservesEpis : Functor.PreservesEpimorphisms F := by infer_instance
  /-- `F` preserves quotients by finite groups (G5). -/
  preservesQuotientsByFiniteGroups (G : Type u₂) [Group G] [Finite G] :
    PreservesColimitsOfShape (SingleObj G) F := by infer_instance
  /-- `F` reflects isomorphisms (G6). -/
  reflectsIsos : F.ReflectsIsomorphisms := by infer_instance

/-- An object of a category `C` is connected if it is not initial
and has no non-trivial subobjects. Lenstra, 3.12. -/
/-
**CategoryTheory.PreGaloisCategory.IsConnected** 是 Mathlib 中的一个归纳类型，位于命名空间 `Cate
goryTheory.PreGaloisCategory`。
形式化陈述：{C : Type u₁} → [CategoryTheory.Category.{u₂, u₁} C] → C → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An object of a category `C` is connected if it is not initial
and has no non-trivial subobjects. Lenstra, 3.12.
-/
class IsConnected {C : Type u₁} [Category.{u₂, u₁} C] (X : C) : Prop where
  /-- `X` is not an initial object. -/
  notInitial : IsInitial X → False
  /-- `X` has no non-trivial subobjects. -/
  noTrivialComponent (Y : C) (i : Y ⟶ X) [Mono i] : (IsInitial Y → False) → IsIso i

/-- A functor is said to preserve connectedness if whenever `X : C` is connected,
also `F.obj X` is connected. -/
/-
**CategoryTheory.PreGaloisCategory.PreservesIsConnected** 是 Mathlib 中的一个归纳类型，位于命
名空间 `CategoryTheory.PreGaloisCategory`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{u₂, u₁} C] →     {D : T
ype v₁} → [inst_1 : CategoryTheory.Category.{v₂, v₁} D] → CategoryTheory.Functor
 C D → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor is said to preserve connectedness if whenever `X : C` is connected,
also `F.obj X` is connected.
-/
class PreservesIsConnected {C : Type u₁} [Category.{u₂, u₁} C] {D : Type v₁}
    [Category.{v₂, v₁} D] (F : C ⥤ D) : Prop where
  /-- `F.obj X` is connected if `X` is connected. -/
  preserves : ∀ {X : C} [IsConnected X], IsConnected (F.obj X)

section
variable {C : Type u₁} [Category.{u₂, u₁} C] [PreGaloisCategory C]

attribute [instance] hasTerminal hasPullbacks hasFiniteCoproducts hasQuotientsByFiniteGroups

/-
**CategoryTheory.PreGaloisCategory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Pr
eGaloisCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasFiniteLimits C := hasFiniteLimits_of_hasTerminal_and_pullbacks
/-
**CategoryTheory.PreGaloisCategory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Pr
eGaloisCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasBinaryProducts C := hasBinaryProducts_of_hasTerminal_and_pullbacks C
/-
**CategoryTheory.PreGaloisCategory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Pr
eGaloisCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasEqualizers C := hasEqualizers_of_hasPullbacks_and_binary_products

-- A `PreGaloisCategory` has quotients by finite groups in arbitrary universes. -/
/-
**CategoryTheory.PreGaloisCategory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Pr
eGaloisCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`F.obj X` is connected if `X` is connected. - /
  preserves : ∀ {X : C} [IsConnected X], IsConnected (F.obj X)

section
variable {C : Type u₁} [Category.{u₂, u₁} C] [PreGaloisCategory C]

attribute [instance] hasTerminal hasPullbacks hasFiniteCoproducts hasQuotientsBy
FiniteGroups

instance : HasFiniteLimits C := hasFiniteLimits_of_hasTerminal_and_pullbacks

instance : HasBinaryProducts C := hasBinaryProducts_of_hasTerminal_and_pullbacks
 C

instance : HasEqualizers C := hasEqualizers_of_hasPullbacks_and_binary_products

-- A `PreGaloisCategory` has quotients by finite groups in arbitrary universes.
-/
instance {G : Type*} [Group G] [Finite G] : HasColimitsOfShape (SingleObj G) C := by
  obtain ⟨G', hg, hf, ⟨e⟩⟩ := Finite.exists_type_univ_nonempty_mulEquiv G
  exact Limits.hasColimitsOfShape_of_equivalence e.toSingleObjEquiv.symm

end

namespace FiberFunctor

variable {C : Type u₁} [Category.{u₂, u₁} C] {F : C ⥤ FintypeCat.{w}} [PreGaloisCategory C]
  [FiberFunctor F]

attribute [instance] preservesTerminalObjects preservesPullbacks preservesEpis
  preservesFiniteCoproducts reflectsIsos preservesQuotientsByFiniteGroups

/-
**CategoryTheory.PreGaloisCategory.FiberFunctor.** 是 Mathlib 中的一个实例，位于命名空间 `Cate
goryTheory.PreGaloisCategory.FiberFunctor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : ReflectsLimitsOfShape (Discrete PEmpty.{1}) F :=
  reflectsLimitsOfShape_of_reflectsIsomorphisms
/-
**CategoryTheory.PreGaloisCategory.FiberFunctor.** 是 Mathlib 中的一个实例，位于命名空间 `Cate
goryTheory.PreGaloisCategory.FiberFunctor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : ReflectsColimitsOfShape (Discrete PEmpty.{1}) F :=
  reflectsColimitsOfShape_of_reflectsIsomorphisms
/-
**CategoryTheory.PreGaloisCategory.FiberFunctor.** 是 Mathlib 中的一个实例，位于命名空间 `Cate
goryTheory.PreGaloisCategory.FiberFunctor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : PreservesFiniteLimits F :=
  preservesFiniteLimits_of_preservesTerminal_and_pullbacks F

/-- Fiber functors preserve quotients by finite groups in arbitrary universes. -/
/-
**CategoryTheory.PreGaloisCategory.FiberFunctor.** 是 Mathlib 中的一个实例，位于命名空间 `Cate
goryTheory.PreGaloisCategory.FiberFunctor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Fiber functors preserve quotients by finite groups in arbitrary universes.
-/
instance {G : Type*} [Group G] [Finite G] :
    PreservesColimitsOfShape (SingleObj G) F := by
  choose G' hg hf he using Finite.exists_type_univ_nonempty_mulEquiv G
  exact Limits.preservesColimitsOfShape_of_equiv he.some.toSingleObjEquiv.symm F

/-- Fiber functors reflect monomorphisms. -/
/-
**CategoryTheory.PreGaloisCategory.FiberFunctor.** 是 Mathlib 中的一个实例，位于命名空间 `Cate
goryTheory.PreGaloisCategory.FiberFunctor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Fiber functors reflect monomorphisms.
-/
instance : ReflectsMonomorphisms F := ReflectsMonomorphisms.mk <| by
  intro X Y f _
  have : IsIso (pullback.fst (F.map f) (F.map f)) :=
    isIso_fst_of_mono (F.map f)
  have : IsIso (F.map (pullback.fst f f)) := by
    rw [← PreservesPullback.iso_hom_fst]
    exact IsIso.comp_isIso
  have : IsIso (pullback.fst f f) := isIso_of_reflects_iso (pullback.fst _ _) F
  exact (pullback.diagonal_isKernelPair f).mono_of_isIso_fst

/-- Fiber functors are faithful. -/
/-
**CategoryTheory.PreGaloisCategory.FiberFunctor.** 是 Mathlib 中的一个实例，位于命名空间 `Cate
goryTheory.PreGaloisCategory.FiberFunctor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Fiber functors are faithful.
-/
instance : F.Faithful where
  map_injective {X Y} f g h := by
    have : IsIso (equalizer.ι (F.map f) (F.map g)) := equalizer.ι_of_eq h
    have : IsIso (F.map (equalizer.ι f g)) := by
      rw [← equalizerComparison_comp_π f g F]
      exact IsIso.comp_isIso
    have : IsIso (equalizer.ι f g) := isIso_of_reflects_iso _ F
    exact eq_of_epi_equalizer

section

/-- If `F` is a fiber functor and `E` is an equivalence between categories of finite types,
then `F ⋙ E` is again a fiber functor. -/
/-
**CategoryTheory.PreGaloisCategory.FiberFunctor.comp_right** 是 Mathlib 中的一个实例，位于
命名空间 `CategoryTheory.PreGaloisCategory.FiberFunctor`。
形式化陈述：comp_right (E : FintypeCat.{w} ⥤ FintypeCat.{t}) [E.IsEquivalence] : Fiber
Functor (F ⋙ E) where preservesQuotientsByFiniteGroups _
参数：E : FintypeCat.{w} ⥤ FintypeCat.{t}。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.comp_preservesLimitsOfShape`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Ca
tegory.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `CategoryTheory.PreGaloisCategory.FiberFunctor.preservesTerminalObjects`：
∀ {C : Type u₁} {inst : CategoryTheory.Category.{u₂, u₁} C} {inst_1 : CategoryTh
eory.PreGaloisCategory C}   {F : CategoryTheory.Functor C Fi…
· 使用定理 `CategoryTheory.Functor.instPreservesLimitsOfShapeOfIsRightAdjoint`：∀ {J 
: Type u_1} {C : Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_1, 
u_1} J]   [inst_1 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `CategoryTheory.Functor.isRightAdjoint_of_isEquivalence`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.PreGaloisCategory.FiberFunctor.preservesPullbacks`：∀ {C :
 Type u₁} {inst : CategoryTheory.Category.{u₂, u₁} C} {inst_1 : CategoryTheory.P
reGaloisCategory C}   {F : CategoryTheory.Functor C Fi…
· 使用定理 `CategoryTheory.PreGaloisCategory.FiberFunctor.preservesFiniteCoproducts`
：∀ {C : Type u₁} {inst : CategoryTheory.Category.{u₂, u₁} C} {inst_1 : CategoryT
heory.PreGaloisCategory C}   {F : CategoryTheory.Functor C Fi…
· 使用定理 `CategoryTheory.Limits.instPreservesFiniteCoproductsOfPreservesFiniteColi
mits`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.PreservesColimits.preservesFiniteColimits`：∀ {C : 
Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.instPreservesColimitsOfSizeOfIsLeftAdjoint`：∀ {C 
: Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_2, u_2} C]   [inst
_1 : CategoryTheory.Category.{v_3, u_3} D] (F : Categor…
· 使用定理 `CategoryTheory.Functor.isLeftAdjoint_of_isEquivalence`：∀ {C : Type u₁} [
inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheor
y.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.preservesEpimorphisms_comp`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Ca
tegory.{v₂, u₂} D]   {E : Type u₃} [ins…
· 使用定理 `CategoryTheory.PreGaloisCategory.FiberFunctor.preservesEpis`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{u₂, u₁} C} {inst_1 : CategoryTheory.PreGal
oisCategory C}   {F : CategoryTheory.Functor C Fi…
· 使用定理 `CategoryTheory.preservesEpimorphisms_of_preservesColimitsOfShape`：∀ {C :
 Type u₁} {D : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Ca
tegoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.instPreservesColimitsOfShapeOfIsLeftAdjoint`：∀ {J
 : Type u_1} {C : Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_1,
 u_1} J]   [inst_1 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `CategoryTheory.Limits.comp_preservesColimitsOfShape`：∀ {C : Type u₁} [in
st : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.
Category.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `CategoryTheory.PreGaloisCategory.FiberFunctor.instPreservesColimitsOfSha
peFintypeCatSingleObjOfFinite`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{
u₂, u₁} C] {F : CategoryTheory.Functor C FintypeCat}   [inst_1 : CategoryTheory.
PreGaloisCa…
· 使用定理 `CategoryTheory.PreGaloisCategory.FiberFunctor.reflectsIsos`：∀ {C : Type 
u₁} {inst : CategoryTheory.Category.{u₂, u₁} C} {inst_1 : CategoryTheory.PreGalo
isCategory C}   {F : CategoryTheory.Functor C Fi…
· 使用定理 `CategoryTheory.reflectsIsomorphisms_of_full_and_faithful`：∀ {C : Type u_
1} [inst : CategoryTheory.Category.{v_1, u_1} C] {D : Type u_2}   [inst_1 : Cate
goryTheory.Category.{v_2, u_2} D] (F : Categor…
· 使用定理 `CategoryTheory.Functor.IsEquivalence.full`：∀ {C : Type u₁} {inst : Categ
oryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Category.{
v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.IsEquivalence.faithful`：∀ {C : Type u₁} {inst : C
ategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Catego
ry.{v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
If `F` is a fiber functor and `E` is an equivalence between categories of finite
 types,
then `F ⋙ E` is again a fiber functor.
-/
instance comp_right (E : FintypeCat.{w} ⥤ FintypeCat.{t}) [E.IsEquivalence] :
    FiberFunctor (F ⋙ E) where
  preservesQuotientsByFiniteGroups _ := comp_preservesColimitsOfShape F E

end

end FiberFunctor

variable {C : Type u₁} [Category.{u₂, u₁} C]
  (F : C ⥤ FintypeCat.{w})

/-- The canonical action of `Aut F` on the fiber of each object. -/
/-
**CategoryTheory.PreGaloisCategory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Pr
eGaloisCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical action of `Aut F` on the fiber of each object.
-/
instance (X : C) : MulAction (Aut F) (F.obj X) where
  smul σ x := σ.hom.app X x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
/-
**CategoryTheory.PreGaloisCategory.mulAction_def** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.PreGaloisCategory`。
形式化陈述：mulAction_def {X : C} (σ : Aut F) (x : F.obj X) : σ • x = σ.hom.app X x
参数：σ : Aut F；x : F.obj X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mulAction_def {X : C} (σ : Aut F) (x : F.obj X) :
    σ • x = σ.hom.app X x :=
  rfl
/-
**CategoryTheory.PreGaloisCategory.mulAction_naturality** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.PreGaloisCategory`。
形式化陈述：mulAction_naturality {X Y : C} (σ : Aut F) (f : X ⟶ Y) (x : F.obj X) : σ •
 F.map f x = F.map f (σ • x)
参数：σ : Aut F；f : X ⟶ Y；x : F.obj X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.naturality_apply`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {D : Type u_1} [inst_1 : CategoryTheory.Category.{v_1
, u_1} D]   {FD : outParam (D …
-/
lemma mulAction_naturality {X Y : C} (σ : Aut F) (f : X ⟶ Y) (x : F.obj X) :
    σ • F.map f x = F.map f (σ • x) :=
  NatTrans.naturality_apply σ.hom f x

/-- An object that is neither initial or connected has a non-trivial subobject. -/
/-
**CategoryTheory.PreGaloisCategory.has_non_trivial_subobject_of_not_isConnected_
of_not_initial** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.PreGaloisCategory`。
形式化陈述：has_non_trivial_subobject_of_not_isConnected_of_not_initial (X : C) (hc : 
¬ IsConnected X) (hi : IsInitial X -> False) : exists (Y : C) (v : Y ⟶ X), (IsIn
itial Y -> False) ∧ Mono v ∧ (¬ IsIso v)
参数：X : C；hc : ¬ IsConnected X；hi : IsInitial X -> False。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)

--- 原说明 ---
An object that is neither initial or connected has a non-trivial subobject.
-/
lemma has_non_trivial_subobject_of_not_isConnected_of_not_initial (X : C) (hc : ¬ IsConnected X)
    (hi : IsInitial X → False) :
    ∃ (Y : C) (v : Y ⟶ X), (IsInitial Y → False) ∧ Mono v ∧ (¬ IsIso v) := by
  contrapose! hc
  exact ⟨hi, fun Y i hm hni ↦ hc Y i hni hm⟩

/-- The cardinality of the fiber is preserved under isomorphisms. -/
/-
**CategoryTheory.PreGaloisCategory.card_fiber_eq_of_iso** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.PreGaloisCategory`。
形式化陈述：card_fiber_eq_of_iso {X Y : C} (i : X ≅ Y) : Nat.card (F.obj X) = Nat.card
 (F.obj Y)
参数：i : X ≅ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.card_eq_of_bijective`：card_eq_of_bijective (f : α -> β) (hf : Functi
on.Bijective f) : Nat.card α = Nat.card β
· 使用定理 `Equiv.bijective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijec
tive ⇑e

--- 原说明 ---
The cardinality of the fiber is preserved under isomorphisms.
-/
lemma card_fiber_eq_of_iso {X Y : C} (i : X ≅ Y) : Nat.card (F.obj X) = Nat.card (F.obj Y) := by
  have e : F.obj X ≃ F.obj Y := Iso.toEquiv (mapIso (F ⋙ FintypeCat.incl) i)
  exact Nat.card_eq_of_bijective e (Equiv.bijective e)

variable [PreGaloisCategory C] [FiberFunctor F]

/-- An object is initial if and only if its fiber is empty. -/
/-
**CategoryTheory.PreGaloisCategory.initial_iff_fiber_empty** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.PreGaloisCategory`。
形式化陈述：initial_iff_fiber_empty (X : C) : Nonempty (IsInitial X) ↔ IsEmpty (F.obj 
X)
参数：X : C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.nonempty_congr`：nonempty_congr (e : α ≃ β) : Nonempty α ↔ Nonempty
 β
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.instPreservesColimitsOfShapeDiscreteOfFiniteOfPres
ervesFiniteCoproducts`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} 
C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTh
eor…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.PreGaloisCategory.FiberFunctor.preservesFiniteCoproducts`
：∀ {C : Type u₁} {inst : CategoryTheory.Category.{u₂, u₁} C} {inst_1 : CategoryT
heory.PreGaloisCategory C}   {F : CategoryTheory.Functor C Fi…
· 使用定理 `CategoryTheory.Limits.reflectsColimit_of_reflectsColimitsOfShape`：∀ {C :
 Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Ca
tegoryTheory.Category.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `CategoryTheory.PreGaloisCategory.FiberFunctor.instReflectsColimitsOfShap
eFintypeCatDiscretePEmpty`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{u₂, 
u₁} C] {F : CategoryTheory.Functor C FintypeCat}   [inst_1 : CategoryTheory.PreG
aloisCa…
· 使用引理 `CategoryTheory.Limits.Concrete.initial_iff_empty_of_preserves_of_reflect
s`：initial_iff_empty_of_preserves_of_reflects [PreservesColimit (Functor.empty.{
0} C) (forget C)] [ReflectsColimit (Functor.empty.{0} C) (forge…
· 使用定理 `CategoryTheory.preservesColimit_of_createsColimit_and_hasColimit`：∀ {C :
 Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Ca
tegoryTheory.Category.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.CreatesColimit.toReflectsColimit`：∀ {C : Type u₁} {inst :
 CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Cate
gory.{v₂, u₂} D}   {J : Type w} {inst…

--- 原说明 ---
An object is initial if and only if its fiber is empty.
-/
lemma initial_iff_fiber_empty (X : C) : Nonempty (IsInitial X) ↔ IsEmpty (F.obj X) := by
  rw [(IsInitial.isInitialIffObj F X).nonempty_congr]
  exact Concrete.initial_iff_empty_of_preserves_of_reflects (F.obj X)

/-- An object is not initial if and only if its fiber is nonempty. -/
/-
**CategoryTheory.PreGaloisCategory.not_initial_iff_fiber_nonempty** 是 Mathlib 中的
一个引理，位于命名空间 `CategoryTheory.PreGaloisCategory`。
形式化陈述：not_initial_iff_fiber_nonempty (X : C) : (IsInitial X -> False) ↔ Nonempty
 (F.obj X)
参数：X : C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_isEmpty_iff`：not_isEmpty_iff : ¬IsEmpty α ↔ Nonempty α
· 使用定理 `Nonempty.elim`：∀ {α : Sort u} {p : Prop}, Nonempty α → (∀ (a : α), p) → 
p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `CategoryTheory.PreGaloisCategory.initial_iff_fiber_empty`：initial_iff_fi
ber_empty (X : C) : Nonempty (IsInitial X) ↔ IsEmpty (F.obj X)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b

--- 原说明 ---
An object is not initial if and only if its fiber is nonempty.
-/
lemma not_initial_iff_fiber_nonempty (X : C) : (IsInitial X → False) ↔ Nonempty (F.obj X) := by
  rw [← not_isEmpty_iff]
  refine ⟨fun h he ↦ ?_, fun h hin ↦ h <| (initial_iff_fiber_empty F X).mp ⟨hin⟩⟩
  exact Nonempty.elim ((initial_iff_fiber_empty F X).mpr he) h

/-- An object whose fiber is inhabited is not initial. -/
/-
**CategoryTheory.PreGaloisCategory.not_initial_of_inhabited** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.PreGaloisCategory`。
形式化陈述：not_initial_of_inhabited {X : C} (x : F.obj X) (h : IsInitial X) : False
参数：x : F.obj X；h : IsInitial X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsEmpty.false`：∀ {α : Sort u} [self : IsEmpty α] (a : α), False
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `CategoryTheory.PreGaloisCategory.initial_iff_fiber_empty`：initial_iff_fi
ber_empty (X : C) : Nonempty (IsInitial X) ↔ IsEmpty (F.obj X)

--- 原说明 ---
An object whose fiber is inhabited is not initial.
-/
lemma not_initial_of_inhabited {X : C} (x : F.obj X) (h : IsInitial X) : False :=
  ((initial_iff_fiber_empty F X).mp ⟨h⟩).false x

/-- The fiber of a connected object is nonempty. -/
/-
**CategoryTheory.PreGaloisCategory.nonempty_fiber_of_isConnected** 是 Mathlib 中的一
个实例，位于命名空间 `CategoryTheory.PreGaloisCategory`。
形式化陈述：nonempty_fiber_of_isConnected (X : C) [IsConnected X] : Nonempty (F.obj X)
参数：X : C。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `CategoryTheory.PreGaloisCategory.initial_iff_fiber_empty`：initial_iff_fi
ber_empty (X : C) : Nonempty (IsInitial X) ↔ IsEmpty (F.obj X)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_nonempty_iff`：not_nonempty_iff : ¬Nonempty α ↔ IsEmpty α
· 使用定理 `CategoryTheory.PreGaloisCategory.IsConnected.notInitial`：∀ {C : Type u₁}
 {inst : CategoryTheory.Category.{u₂, u₁} C} {X : C}   [self : CategoryTheory.Pr
eGaloisCategory.IsConnected X] (a : CategoryT…

--- 原说明 ---
The fiber of a connected object is nonempty.
-/
instance nonempty_fiber_of_isConnected (X : C) [IsConnected X] : Nonempty (F.obj X) := by
  by_contra h
  have ⟨hin⟩ : Nonempty (IsInitial X) := (initial_iff_fiber_empty F X).mpr (not_nonempty_iff.mp h)
  exact IsConnected.notInitial hin

/-- The fiber of the equalizer of `f g : X ⟶ Y` is equivalent to the set of agreement of `f`
and `g`. -/
/-
**CategoryTheory.PreGaloisCategory.fiberEqualizerEquiv** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.PreGaloisCategory`。
形式化陈述：fiberEqualizerEquiv {X Y : C} (f g : X ⟶ Y) : F.obj (equalizer f g) ≃ { x 
: F.obj X // F.map f x = F.map g x }
参数：f g : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The fiber of the equalizer of `f g : X ⟶ Y` is equivalent to the set of agreemen
t of `f`
and `g`.
-/
noncomputable def fiberEqualizerEquiv {X Y : C} (f g : X ⟶ Y) :
    F.obj (equalizer f g) ≃ { x : F.obj X // F.map f x = F.map g x } :=
  (PreservesEqualizer.iso (F ⋙ FintypeCat.incl) f g ≪≫
    Types.equalizerIso (F.map f).hom (F.map g).hom).toEquiv

@[simp]
/-
**CategoryTheory.PreGaloisCategory.fiberEqualizerEquiv_symm_** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.PreGaloisCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma fiberEqualizerEquiv_symm_ι_apply {X Y : C} {f g : X ⟶ Y} (x : F.obj X)
    (h : F.map f x = F.map g x) :
    F.map (equalizer.ι f g) ((fiberEqualizerEquiv F f g).symm ⟨x, h⟩) = x := by
  simp only [fiberEqualizerEquiv, Functor.comp_map]
  change ((Types.equalizerIso _ _).inv ≫ _ ≫ (F ⋙ FintypeCat.incl).map (equalizer.ι f g)) _ = _
  erw [PreservesEqualizer.iso_inv_ι, Types.equalizerIso_inv_comp_ι]
  rfl

/-- The fiber of the pullback is the fiber product of the fibers. -/
/-
**CategoryTheory.PreGaloisCategory.fiberPullbackEquiv** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.PreGaloisCategory`。
形式化陈述：fiberPullbackEquiv {X A B : C} (f : A ⟶ X) (g : B ⟶ X) : F.obj (pullback f
 g) ≃ { p : F.obj A × F.obj B // F.map f p.1 = F.map g p.2 }
参数：f : A ⟶ X；g : B ⟶ X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The fiber of the pullback is the fiber product of the fibers.
-/
noncomputable def fiberPullbackEquiv {X A B : C} (f : A ⟶ X) (g : B ⟶ X) :
    F.obj (pullback f g) ≃ { p : F.obj A × F.obj B // F.map f p.1 = F.map g p.2 } :=
  Iso.toEquiv (PreservesPullback.iso (F ⋙ FintypeCat.incl) f g ≪≫
    Types.pullbackIsoPullback (F.map f).hom (F.map g).hom)

@[simp]
/-
**CategoryTheory.PreGaloisCategory.fiberPullbackEquiv_symm_fst_apply** 是 Mathlib
 中的一个引理，位于命名空间 `CategoryTheory.PreGaloisCategory`。
形式化陈述：fiberPullbackEquiv_symm_fst_apply {X A B : C} {f : A ⟶ X} {g : B ⟶ X} (a :
 F.obj A) (b : F.obj B) (h : F.map f a = F.map g b) : F.map (pullback.fst f g) (
(fiberPullbackEquiv F f g).symm ⟨(a, b), h⟩) = a
参数：a : F.obj A；b : F.obj B；h : F.map f a = F.map g b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.PreGaloisCategory.hasPullbacks`：∀ {C : Type u₁} {inst : C
ategoryTheory.Category.{u₂, u₁} C} [self : CategoryTheory.PreGaloisCategory C], 
  CategoryTheory.Limits.HasPullback…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.PreservesPullback.iso_inv_fst`：∀ {C : Type u₁} [in
st : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.
Category.{v₂, u₂} D]   (G : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.Types.pullbackIsoPullback_inv_fst`：∀ {X Y Z : Type
 u} (f : X ⟶ Z) (g : Y ⟶ Z),   CategoryTheory.CategoryStruct.comp (CategoryTheor
y.Limits.Types.pullbackIsoPullback f g).inv  …
-/
lemma fiberPullbackEquiv_symm_fst_apply {X A B : C} {f : A ⟶ X} {g : B ⟶ X}
    (a : F.obj A) (b : F.obj B) (h : F.map f a = F.map g b) :
    F.map (pullback.fst f g) ((fiberPullbackEquiv F f g).symm ⟨(a, b), h⟩) = a := by
  simp only [fiberPullbackEquiv, Functor.comp_map, Iso.toEquiv_symm_fun]
  change ((Types.pullbackIsoPullback _ _).inv ≫ _ ≫
    (F ⋙ FintypeCat.incl).map (pullback.fst f g)) _ = _
  erw [PreservesPullback.iso_inv_fst, Types.pullbackIsoPullback_inv_fst]
  rfl

@[simp]
/-
**CategoryTheory.PreGaloisCategory.fiberPullbackEquiv_symm_snd_apply** 是 Mathlib
 中的一个引理，位于命名空间 `CategoryTheory.PreGaloisCategory`。
形式化陈述：fiberPullbackEquiv_symm_snd_apply {X A B : C} {f : A ⟶ X} {g : B ⟶ X} (a :
 F.obj A) (b : F.obj B) (h : F.map f a = F.map g b) : F.map (pullback.snd f g) (
(fiberPullbackEquiv F f g).symm ⟨(a, b), h⟩) = b
参数：a : F.obj A；b : F.obj B；h : F.map f a = F.map g b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.PreGaloisCategory.hasPullbacks`：∀ {C : Type u₁} {inst : C
ategoryTheory.Category.{u₂, u₁} C} [self : CategoryTheory.PreGaloisCategory C], 
  CategoryTheory.Limits.HasPullback…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.PreservesPullback.iso_inv_snd`：∀ {C : Type u₁} [in
st : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.
Category.{v₂, u₂} D]   (G : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.Types.pullbackIsoPullback_inv_snd`：∀ {X Y Z : Type
 u} (f : X ⟶ Z) (g : Y ⟶ Z),   CategoryTheory.CategoryStruct.comp (CategoryTheor
y.Limits.Types.pullbackIsoPullback f g).inv  …
-/
lemma fiberPullbackEquiv_symm_snd_apply {X A B : C} {f : A ⟶ X} {g : B ⟶ X}
    (a : F.obj A) (b : F.obj B) (h : F.map f a = F.map g b) :
    F.map (pullback.snd f g) ((fiberPullbackEquiv F f g).symm ⟨(a, b), h⟩) = b := by
  simp only [fiberPullbackEquiv, Functor.comp_map, Iso.toEquiv_symm_fun]
  change ((Types.pullbackIsoPullback _ _).inv ≫ _ ≫
    (F ⋙ FintypeCat.incl).map (pullback.snd f g)) _ = _
  erw [PreservesPullback.iso_inv_snd, Types.pullbackIsoPullback_inv_snd]
  rfl

/-- The fiber of the binary product is the binary product of the fibers. -/
/-
**CategoryTheory.PreGaloisCategory.fiberBinaryProductEquiv** 是 Mathlib 中的一个定义，位于
命名空间 `CategoryTheory.PreGaloisCategory`。
形式化陈述：fiberBinaryProductEquiv (X Y : C) : F.obj (X ⨯ Y) ≃ F.obj X × F.obj Y
参数：X Y : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The fiber of the binary product is the binary product of the fibers.
-/
noncomputable def fiberBinaryProductEquiv (X Y : C) :
    F.obj (X ⨯ Y) ≃ F.obj X × F.obj Y :=
  (PreservesLimitPair.iso (F ⋙ FintypeCat.incl) X Y ≪≫
  Types.binaryProductIso (F.obj X) (F.obj Y)).toEquiv

@[simp]
/-
**CategoryTheory.PreGaloisCategory.fiberBinaryProductEquiv_symm_fst_apply** 是 Ma
thlib 中的一个引理，位于命名空间 `CategoryTheory.PreGaloisCategory`。
形式化陈述：fiberBinaryProductEquiv_symm_fst_apply {X Y : C} (x : F.obj X) (y : F.obj 
Y) : F.map prod.fst ((fiberBinaryProductEquiv F X Y).symm (x, y)) = x
参数：x : F.obj X；y : F.obj Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.PreGaloisCategory.instHasBinaryProducts`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{u₂, u₁} C] [CategoryTheory.PreGaloisCategory C]
,   CategoryTheory.Limits.HasBinaryProducts …
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.PreservesLimitPair.iso_inv_fst`：∀ {C : Type u₁} [i
nst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory
.Category.{v₂, u₂} D]   (G : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.Types.binaryProductIso_inv_comp_fst`：binaryProduct
Iso_inv_comp_fst (X Y : Type u) : (binaryProductIso X Y).inv ≫ Limits.prod.fst =
 ↾_root_.Prod.fst
-/
lemma fiberBinaryProductEquiv_symm_fst_apply {X Y : C} (x : F.obj X) (y : F.obj Y) :
    F.map prod.fst ((fiberBinaryProductEquiv F X Y).symm (x, y)) = x := by
  simp only [fiberBinaryProductEquiv]
  change ((Types.binaryProductIso _ _).inv ≫ _ ≫ (F ⋙ FintypeCat.incl).map prod.fst) _ = _
  erw [PreservesLimitPair.iso_inv_fst, Types.binaryProductIso_inv_comp_fst]
  rfl

@[simp]
/-
**CategoryTheory.PreGaloisCategory.fiberBinaryProductEquiv_symm_snd_apply** 是 Ma
thlib 中的一个引理，位于命名空间 `CategoryTheory.PreGaloisCategory`。
形式化陈述：fiberBinaryProductEquiv_symm_snd_apply {X Y : C} (x : F.obj X) (y : F.obj 
Y) : F.map prod.snd ((fiberBinaryProductEquiv F X Y).symm (x, y)) = y
参数：x : F.obj X；y : F.obj Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.PreGaloisCategory.instHasBinaryProducts`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{u₂, u₁} C] [CategoryTheory.PreGaloisCategory C]
,   CategoryTheory.Limits.HasBinaryProducts …
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.PreservesLimitPair.iso_inv_snd`：∀ {C : Type u₁} [i
nst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory
.Category.{v₂, u₂} D]   (G : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.Types.binaryProductIso_inv_comp_snd`：binaryProduct
Iso_inv_comp_snd (X Y : Type u) : (binaryProductIso X Y).inv ≫ Limits.prod.snd =
 ↾_root_.Prod.snd
-/
lemma fiberBinaryProductEquiv_symm_snd_apply {X Y : C} (x : F.obj X) (y : F.obj Y) :
    F.map prod.snd ((fiberBinaryProductEquiv F X Y).symm (x, y)) = y := by
  simp only [fiberBinaryProductEquiv]
  change ((Types.binaryProductIso _ _).inv ≫ _ ≫ (F ⋙ FintypeCat.incl).map prod.snd) _ = _
  erw [PreservesLimitPair.iso_inv_snd, Types.binaryProductIso_inv_comp_snd]
  rfl

/-- The evaluation map is injective for connected objects. -/
/-
**CategoryTheory.PreGaloisCategory.evaluation_injective_of_isConnected** 是 Mathl
ib 中的一个引理，位于命名空间 `CategoryTheory.PreGaloisCategory`。
形式化陈述：evaluation_injective_of_isConnected (A X : C) [IsConnected A] (a : F.obj A
) : Function.Injective (fun (f : A ⟶ X) => F.map f a)
参数：A X : C；a : F.obj A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.PreGaloisCategory.instHasEqualizers`：∀ {C : Type u₁} [ins
t : CategoryTheory.Category.{u₂, u₁} C] [CategoryTheory.PreGaloisCategory C],   
CategoryTheory.Limits.HasEqualizers C
· 使用定理 `CategoryTheory.PreGaloisCategory.IsConnected.noTrivialComponent`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{u₂, u₁} C} {X : C}   [self : CategoryT
heory.PreGaloisCategory.IsConnected X] (Y : C) (i : Y…
· 使用定理 `CategoryTheory.Limits.equalizer.ι_mono`：∀ {C : Type u} {X Y : C} [inst :
 CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   [inst_1 : CategoryTheory.Limi
ts.HasEqualizer f g], Catego…
· 使用引理 `CategoryTheory.PreGaloisCategory.not_initial_of_inhabited`：not_initial_o
f_inhabited {X : C} (x : F.obj X) (h : IsInitial X) : False
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `CategoryTheory.Limits.eq_of_epi_equalizer`：eq_of_epi_equalizer [HasEqual
izer f g] [Epi (equalizer.ι f g)] : f = g
· 使用定理 `CategoryTheory.instEffectiveEpiOfIsIso`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],  
 CategoryTheory.EffectiveEpi…

--- 原说明 ---
The evaluation map is injective for connected objects.
-/
lemma evaluation_injective_of_isConnected (A X : C) [IsConnected A] (a : F.obj A) :
    Function.Injective (fun (f : A ⟶ X) ↦ F.map f a) := by
  intro f g (h : F.map f a = F.map g a)
  have : IsIso (equalizer.ι f g) := by
    apply IsConnected.noTrivialComponent _ (equalizer.ι f g)
    exact not_initial_of_inhabited F ((fiberEqualizerEquiv F f g).symm ⟨a, h⟩)
  exact eq_of_epi_equalizer

/-- The evaluation map on automorphisms is injective for connected objects. -/
/-
**CategoryTheory.PreGaloisCategory.evaluation_aut_injective_of_isConnected** 是 M
athlib 中的一个引理，位于命名空间 `CategoryTheory.PreGaloisCategory`。
形式化陈述：evaluation_aut_injective_of_isConnected (A : C) [IsConnected A] (a : F.obj
 A) : Function.Injective (fun f : Aut A => F.map (f.hom) a)
参数：A : C；a : F.obj A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用引理 `CategoryTheory.PreGaloisCategory.evaluation_injective_of_isConnected`：ev
aluation_injective_of_isConnected (A X : C) [IsConnected A] (a : F.obj A) : Func
tion.Injective (fun (f : A ⟶ X) => F.map f a)
· 使用引理 `CategoryTheory.Aut.ext`：ext {X : C} {φ₁ φ₂ : Aut X} (h : φ₁.hom = φ₂.hom
) : φ₁ = φ₂

--- 原说明 ---
The evaluation map on automorphisms is injective for connected objects.
-/
lemma evaluation_aut_injective_of_isConnected (A : C) [IsConnected A] (a : F.obj A) :
    Function.Injective (fun f : Aut A ↦ F.map (f.hom) a) := by
  change Function.Injective ((fun f : A ⟶ A ↦ F.map f a) ∘ (fun f : Aut A ↦ f.hom))
  apply Function.Injective.comp
  · exact evaluation_injective_of_isConnected F A A a
  · exact @Aut.ext _ _ A

/-- A morphism from an object `X` with non-empty fiber to a connected object `A` is an
epimorphism. -/
/-
**CategoryTheory.PreGaloisCategory.epi_of_nonempty_of_isConnected** 是 Mathlib 中的
一个引理，位于命名空间 `CategoryTheory.PreGaloisCategory`。
形式化陈述：epi_of_nonempty_of_isConnected {X A : C} [IsConnected A] [h : Nonempty (F.
obj X)] (f : X ⟶ A) : Epi f
参数：F.obj X；f : X ⟶ A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.PreGaloisCategory.evaluation_injective_of_isConnected`：ev
aluation_injective_of_isConnected (A X : C) [IsConnected A] (a : F.obj A) : Func
tion.Injective (fun (f : A ⟶ X) => F.map f a)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用定理 `CategoryTheory.ConcreteCategory.congr_hom`：congr_hom {X Y : C} {f g : X 
⟶ Y} (h : f = g) (x : ToType X) : f x = g x
· 使用定理 `CategoryTheory.Functor.congr_map`：congr_map (F : C ⥤ D) {X Y : C} {f g :
 X ⟶ Y} (h : f = g) : F.map f = F.map g

--- 原说明 ---
A morphism from an object `X` with non-empty fiber to a connected object `A` is 
an
epimorphism.
-/
lemma epi_of_nonempty_of_isConnected {X A : C} [IsConnected A] [h : Nonempty (F.obj X)]
    (f : X ⟶ A) : Epi f := Epi.mk <| fun {Z} u v huv ↦ by
  apply evaluation_injective_of_isConnected F A Z (F.map f (Classical.arbitrary _))
  simpa using ConcreteCategory.congr_hom (F.congr_map huv) _

/-- An epimorphism induces a surjective map on fibers. -/
/-
**CategoryTheory.PreGaloisCategory.surjective_on_fiber_of_epi** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.PreGaloisCategory`。
形式化陈述：surjective_on_fiber_of_epi {X Y : C} (f : X ⟶ Y) [Epi f] : Function.Surjec
tive (F.map f)
参数：f : X ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.surjective_of_epi`：surjective_of_epi {X Y : Type u} (f : 
X ⟶ Y) [hf : Epi f] : Function.Surjective f
· 使用定理 `CategoryTheory.preservesEpimorphisms_of_preservesColimitsOfShape`：∀ {C :
 Type u₁} {D : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Ca
tegoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.PreservesFiniteColimits.preservesFiniteColimits`：∀
 {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1
 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.PreGaloisCategory.FiberFunctor.preservesEpis`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{u₂, u₁} C} {inst_1 : CategoryTheory.PreGal
oisCategory C}   {F : CategoryTheory.Functor C Fi…

--- 原说明 ---
An epimorphism induces a surjective map on fibers.
-/
lemma surjective_on_fiber_of_epi {X Y : C} (f : X ⟶ Y) [Epi f] : Function.Surjective (F.map f) :=
  surjective_of_epi (FintypeCat.incl.map (F.map f))

/-- A morphism from an object with non-empty fiber to a connected object is surjective on fibers. -/
/-
**CategoryTheory.PreGaloisCategory.surjective_of_nonempty_fiber_of_isConnected**
 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.PreGaloisCategory`。
形式化陈述：surjective_of_nonempty_fiber_of_isConnected {X A : C} [Nonempty (F.obj X)]
 [IsConnected A] (f : X ⟶ A) : Function.Surjective (F.map f)
参数：F.obj X；f : X ⟶ A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.PreGaloisCategory.epi_of_nonempty_of_isConnected`：epi_of_
nonempty_of_isConnected {X A : C} [IsConnected A] [h : Nonempty (F.obj X)] (f : 
X ⟶ A) : Epi f
· 使用引理 `CategoryTheory.PreGaloisCategory.surjective_on_fiber_of_epi`：surjective_
on_fiber_of_epi {X Y : C} (f : X ⟶ Y) [Epi f] : Function.Surjective (F.map f)

--- 原说明 ---
A morphism from an object with non-empty fiber to a connected object is surjecti
ve on fibers.
-/
lemma surjective_of_nonempty_fiber_of_isConnected {X A : C} [Nonempty (F.obj X)]
    [IsConnected A] (f : X ⟶ A) :
    Function.Surjective (F.map f) := by
  have : Epi f := epi_of_nonempty_of_isConnected F f
  exact surjective_on_fiber_of_epi F f

/-- If `X : ι → C` is a finite family of objects with non-empty fiber, then
also `∏ᶜ X` has non-empty fiber. -/
/-
**CategoryTheory.PreGaloisCategory.nonempty_fiber_pi_of_nonempty_of_finite** 是 M
athlib 中的一个实例，位于命名空间 `CategoryTheory.PreGaloisCategory`。
形式化陈述：nonempty_fiber_pi_of_nonempty_of_finite {ι : Type*} [Finite ι] (X : ι -> C
) [forall i, Nonempty (F.obj (X i))] : Nonempty (F.obj (∏ᶜ X))
参数：X : ι -> C；F.obj (X i)。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.hasFiniteProducts_of_hasFiniteLimits`：∀ (C : Type 
u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFiniteLim
its C],   CategoryTheory.Limits.HasFiniteProduct…
· 使用定理 `CategoryTheory.PreGaloisCategory.instHasFiniteLimits`：∀ {C : Type u₁} [i
nst : CategoryTheory.Category.{u₂, u₁} C] [CategoryTheory.PreGaloisCategory C], 
  CategoryTheory.Limits.HasFiniteLimits C
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.instPreservesLimitsOfShapeDiscreteOfFiniteOfPreser
vesFiniteProducts`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {
D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.instPreservesFiniteProductsOfPreservesFiniteLimits
`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [ins
t_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.PreGaloisCategory.FiberFunctor.instPreservesFiniteLimitsF
intypeCat`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{u₂, u₁} C] {F : Cate
goryTheory.Functor C FintypeCat}   [inst_1 : CategoryTheory.PreGaloisCa…
· 使用定理 `Nonempty.elim`：∀ {α : Sort u} {p : Prop}, Nonempty α → (∀ (a : α), p) → 
p

--- 原说明 ---
If `X : ι → C` is a finite family of objects with non-empty fiber, then
also `∏ᶜ X` has non-empty fiber.
-/
instance nonempty_fiber_pi_of_nonempty_of_finite {ι : Type*} [Finite ι] (X : ι → C)
    [∀ i, Nonempty (F.obj (X i))] : Nonempty (F.obj (∏ᶜ X)) := by
  cases nonempty_fintype ι
  let f (i : ι) : FintypeCat.{w} := F.obj (X i)
  let i : F.obj (∏ᶜ X) ≅ ∏ᶜ f := PreservesProduct.iso F _
  exact Nonempty.elim inferInstance fun x : (∏ᶜ f : FintypeCat.{w}) ↦ ⟨i.inv x⟩

section CardFiber

open ConcreteCategory

attribute [local instance] FintypeCat.fintype in
/-- A mono between objects with equally sized fibers is an iso. -/
/-
**CategoryTheory.PreGaloisCategory.isIso_of_mono_of_eq_card_fiber** 是 Mathlib 中的
一个引理，位于命名空间 `CategoryTheory.PreGaloisCategory`。
形式化陈述：isIso_of_mono_of_eq_card_fiber {X Y : C} (f : X ⟶ Y) [Mono f] (h : Nat.car
d (F.obj X) = Nat.card (F.obj Y)) : IsIso f
参数：f : X ⟶ Y；h : Nat.card (F.obj X) = Nat.card (F.obj Y)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.ConcreteCategory.isIso_iff_bijective`：isIso_iff_bijective
 [(forget C).ReflectsIsomorphisms] {X Y : C} (f : X ⟶ Y) : IsIso f ↔ Function.Bi
jective f
· 使用定理 `CategoryTheory.reflectsIsomorphisms_of_full_and_faithful`：∀ {C : Type u_
1} [inst : CategoryTheory.Category.{v_1, u_1} C] {D : Type u_2}   [inst_1 : Cate
goryTheory.Category.{v_2, u_2} D] (F : Categor…
· 使用定理 `FintypeCat.instFullForgetFunObjFinite`：(CategoryTheory.forget FintypeCat
).Full
· 使用定理 `CategoryTheory.instFaithfulForget`：∀ (C : Type u_1) [inst : CategoryTheo
ry.Category.{v_1, u_1} C] {FC : outParam (C → C → Type u_2)}   {CC : outParam (C
 → Type w)} [inst_1 : o…
· 使用定理 `Fintype.bijective_iff_injective_and_card`：bijective_iff_injective_and_ca
rd (f : α -> β) : Bijective f ↔ Injective f ∧ card α = card β
· 使用定理 `CategoryTheory.ConcreteCategory.injective_of_mono_of_preservesPullback`：
injective_of_mono_of_preservesPullback {X Y : C} (f : X ⟶ Y) [Mono f] [Preserves
LimitsOfShape WalkingCospan (forget C)] : Function.Injective…
· 使用定理 `CategoryTheory.Functor.map_mono`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (F : CategoryTheor…
· 使用定理 `CategoryTheory.preservesMonomorphisms_of_preservesLimitsOfShape`：∀ {C : 
Type u₁} {D : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.PreGaloisCategory.FiberFunctor.preservesPullbacks`：∀ {C :
 Type u₁} {inst : CategoryTheory.Category.{u₂, u₁} C} {inst_1 : CategoryTheory.P
reGaloisCategory C}   {F : CategoryTheory.Functor C Fi…
· 使用定理 `CategoryTheory.Limits.PreservesFiniteLimits.preservesFiniteLimits`：∀ {C 
: Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : C
ategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.FintypeCat.instPreservesFiniteLimitsFintypeCatForg
etFunObjFinite`：CategoryTheory.Limits.PreservesFiniteLimits (CategoryTheory.forg
et FintypeCat)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.isIso_of_reflects_iso`：isIso_of_reflects_iso {A B : C} (f
 : A ⟶ B) (F : C ⥤ D) [IsIso (F.map f)] [F.ReflectsIsomorphisms] : IsIso f
· 使用定理 `CategoryTheory.PreGaloisCategory.FiberFunctor.reflectsIsos`：∀ {C : Type 
u₁} {inst : CategoryTheory.Category.{u₂, u₁} C} {inst_1 : CategoryTheory.PreGalo
isCategory C}   {F : CategoryTheory.Functor C Fi…

--- 原说明 ---
A mono between objects with equally sized fibers is an iso.
-/
lemma isIso_of_mono_of_eq_card_fiber {X Y : C} (f : X ⟶ Y) [Mono f]
    (h : Nat.card (F.obj X) = Nat.card (F.obj Y)) : IsIso f := by
  have : IsIso (F.map f) := by
    apply (ConcreteCategory.isIso_iff_bijective (F.map f)).mpr
    apply (Fintype.bijective_iff_injective_and_card (F.map f)).mpr
    refine ⟨injective_of_mono_of_preservesPullback (F.map f), ?_⟩
    simp only [← Nat.card_eq_fintype_card, h]
  exact isIso_of_reflects_iso f F

/-- Along a mono that is not an iso, the cardinality of the fiber strictly increases. -/
/-
**CategoryTheory.PreGaloisCategory.lt_card_fiber_of_mono_of_notIso** 是 Mathlib 中
的一个引理，位于命名空间 `CategoryTheory.PreGaloisCategory`。
形式化陈述：lt_card_fiber_of_mono_of_notIso {X Y : C} (f : X ⟶ Y) [Mono f] (h : ¬ IsIs
o f) : Nat.card (F.obj X) < Nat.card (F.obj Y)
参数：f : X ⟶ Y；h : ¬ IsIso f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用引理 `CategoryTheory.PreGaloisCategory.isIso_of_mono_of_eq_card_fiber`：isIso_o
f_mono_of_eq_card_fiber {X Y : C} (f : X ⟶ Y) [Mono f] (h : Nat.card (F.obj X) =
 Nat.card (F.obj Y)) : IsIso f
· 使用定理 `Nat.le_antisymm`：∀ {n m : ℕ}, n ≤ m → m ≤ n → n = m
· 使用引理 `Nat.card_le_card_of_injective`：card_le_card_of_injective {α : Type u} {β
 : Type v} [Finite β] (f : α -> β) (hf : Injective f) : Nat.card α <= Nat.card β
· 使用定理 `FintypeCat.instFiniteObj`：∀ {X : FintypeCat}, Finite X.obj
· 使用定理 `CategoryTheory.ConcreteCategory.injective_of_mono_of_preservesPullback`：
injective_of_mono_of_preservesPullback {X Y : C} (f : X ⟶ Y) [Mono f] [Preserves
LimitsOfShape WalkingCospan (forget C)] : Function.Injective…
· 使用定理 `CategoryTheory.Functor.map_mono`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (F : CategoryTheor…
· 使用定理 `CategoryTheory.preservesMonomorphisms_of_preservesLimitsOfShape`：∀ {C : 
Type u₁} {D : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.PreGaloisCategory.FiberFunctor.preservesPullbacks`：∀ {C :
 Type u₁} {inst : CategoryTheory.Category.{u₂, u₁} C} {inst_1 : CategoryTheory.P
reGaloisCategory C}   {F : CategoryTheory.Functor C Fi…
· 使用定理 `CategoryTheory.Limits.PreservesFiniteLimits.preservesFiniteLimits`：∀ {C 
: Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : C
ategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.FintypeCat.instPreservesFiniteLimitsFintypeCatForg
etFunObjFinite`：CategoryTheory.Limits.PreservesFiniteLimits (CategoryTheory.forg
et FintypeCat)

--- 原说明 ---
Along a mono that is not an iso, the cardinality of the fiber strictly increases
.
-/
lemma lt_card_fiber_of_mono_of_notIso {X Y : C} (f : X ⟶ Y) [Mono f]
    (h : ¬ IsIso f) : Nat.card (F.obj X) < Nat.card (F.obj Y) := by
  by_contra hlt
  apply h
  apply isIso_of_mono_of_eq_card_fiber F f
  simp only [not_lt] at hlt
  exact Nat.le_antisymm
    (Nat.card_le_card_of_injective (F.map f) (injective_of_mono_of_preservesPullback (F.map f))) hlt

/-- The cardinality of the fiber of a not-initial object is non-zero. -/
/-
**CategoryTheory.PreGaloisCategory.non_zero_card_fiber_of_not_initial** 是 Mathli
b 中的一个引理，位于命名空间 `CategoryTheory.PreGaloisCategory`。
形式化陈述：non_zero_card_fiber_of_not_initial (X : C) (h : IsInitial X -> False) : Na
t.card (F.obj X) != 0
参数：X : C；h : IsInitial X -> False。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nonempty.elim`：∀ {α : Sort u} {p : Prop}, Nonempty α → (∀ (a : α), p) → 
p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.PreGaloisCategory.initial_iff_fiber_empty`：initial_iff_fi
ber_empty (X : C) : Nonempty (IsInitial X) ↔ IsEmpty (F.obj X)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finite.card_eq_zero_iff`：card_eq_zero_iff [Finite α] : Nat.card α = 0 ↔ 
IsEmpty α
· 使用定理 `FintypeCat.instFiniteObj`：∀ {X : FintypeCat}, Finite X.obj

--- 原说明 ---
The cardinality of the fiber of a not-initial object is non-zero.
-/
lemma non_zero_card_fiber_of_not_initial (X : C) (h : IsInitial X → False) :
    Nat.card (F.obj X) ≠ 0 := by
  intro hzero
  refine Nonempty.elim ?_ h
  rw [initial_iff_fiber_empty F]
  exact Finite.card_eq_zero_iff.mp hzero

/-- The cardinality of the fiber of a coproduct is the sum of the cardinalities of the fibers. -/
/-
**CategoryTheory.PreGaloisCategory.card_fiber_coprod_eq_sum** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.PreGaloisCategory`。
形式化陈述：card_fiber_coprod_eq_sum (X Y : C) : Nat.card (F.obj (X ⨿ Y)) = Nat.card (
F.obj X) + Nat.card (F.obj Y)
参数：X Y : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.PreGaloisCategory.hasFiniteCoproducts`：∀ {C : Type u₁} {i
nst : CategoryTheory.Category.{u₂, u₁} C} [self : CategoryTheory.PreGaloisCatego
ry C],   CategoryTheory.Limits.HasFiniteCo…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.instPreservesColimitsOfShapeDiscreteOfFiniteOfPres
ervesFiniteCoproducts`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} 
C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTh
eor…
· 使用定理 `CategoryTheory.PreGaloisCategory.FiberFunctor.preservesFiniteCoproducts`
：∀ {C : Type u₁} {inst : CategoryTheory.Category.{u₂, u₁} C} {inst_1 : CategoryT
heory.PreGaloisCategory C}   {F : CategoryTheory.Functor C Fi…
· 使用定理 `CategoryTheory.preservesColimit_of_createsColimit_and_hasColimit`：∀ {C :
 Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Ca
tegoryTheory.Category.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.card_sum`：card_sum [Finite α] [Finite β] : Nat.card (α oplus β) = Na
t.card α + Nat.card β
· 使用定理 `FintypeCat.instFiniteObj`：∀ {X : FintypeCat}, Finite X.obj
· 使用定理 `Nat.card_eq_of_bijective`：card_eq_of_bijective (f : α -> β) (hf : Functi
on.Bijective f) : Nat.card α = Nat.card β
· 使用定理 `Equiv.bijective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijec
tive ⇑e

--- 原说明 ---
The cardinality of the fiber of a coproduct is the sum of the cardinalities of t
he fibers.
-/
lemma card_fiber_coprod_eq_sum (X Y : C) :
    Nat.card (F.obj (X ⨿ Y)) = Nat.card (F.obj X) + Nat.card (F.obj Y) := by
  let e : F.obj (X ⨿ Y) ≃ F.obj X ⊕ F.obj Y := Iso.toEquiv
    <| (PreservesColimitPair.iso (F ⋙ FintypeCat.incl) X Y).symm.trans
    <| Types.binaryCoproductIso (FintypeCat.incl.obj (F.obj X)) (FintypeCat.incl.obj (F.obj Y))
  rw [← Nat.card_sum]
  exact Nat.card_eq_of_bijective e.toFun (Equiv.bijective e)

/-- The cardinality of morphisms `A ⟶ X` is smaller than the cardinality of
the fiber of the target if the source is connected. -/
/-
**CategoryTheory.PreGaloisCategory.card_hom_le_card_fiber_of_connected** 是 Mathl
ib 中的一个引理，位于命名空间 `CategoryTheory.PreGaloisCategory`。
形式化陈述：card_hom_le_card_fiber_of_connected (A X : C) [IsConnected A] : Nat.card (
A ⟶ X) <= Nat.card (F.obj X)
参数：A X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.card_le_card_of_injective`：card_le_card_of_injective {α : Type u} {β
 : Type v} [Finite β] (f : α -> β) (hf : Injective f) : Nat.card α <= Nat.card β
· 使用定理 `FintypeCat.instFiniteObj`：∀ {X : FintypeCat}, Finite X.obj
· 使用引理 `CategoryTheory.PreGaloisCategory.evaluation_injective_of_isConnected`：ev
aluation_injective_of_isConnected (A X : C) [IsConnected A] (a : F.obj A) : Func
tion.Injective (fun (f : A ⟶ X) => F.map f a)

--- 原说明 ---
The cardinality of morphisms `A ⟶ X` is smaller than the cardinality of
the fiber of the target if the source is connected.
-/
lemma card_hom_le_card_fiber_of_connected (A X : C) [IsConnected A] :
    Nat.card (A ⟶ X) ≤ Nat.card (F.obj X) := by
  apply Nat.card_le_card_of_injective
  exact evaluation_injective_of_isConnected F A X (Classical.arbitrary _)

/-- If `A` is connected, the cardinality of `Aut A` is smaller than the cardinality of the
fiber of `A`. -/
/-
**CategoryTheory.PreGaloisCategory.card_aut_le_card_fiber_of_connected** 是 Mathl
ib 中的一个引理，位于命名空间 `CategoryTheory.PreGaloisCategory`。
形式化陈述：card_aut_le_card_fiber_of_connected (A : C) [IsConnected A] : Nat.card (Au
t A) <= Nat.card (F.obj A)
参数：A : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.card_le_card_of_injective`：card_le_card_of_injective {α : Type u} {β
 : Type v} [Finite β] (f : α -> β) (hf : Injective f) : Nat.card α <= Nat.card β
· 使用定理 `FintypeCat.instFiniteObj`：∀ {X : FintypeCat}, Finite X.obj
· 使用引理 `CategoryTheory.PreGaloisCategory.evaluation_aut_injective_of_isConnected
`：evaluation_aut_injective_of_isConnected (A : C) [IsConnected A] (a : F.obj A) 
: Function.Injective (fun f : Aut A => F.map (f.hom) a)

--- 原说明 ---
If `A` is connected, the cardinality of `Aut A` is smaller than the cardinality 
of the
fiber of `A`.
-/
lemma card_aut_le_card_fiber_of_connected (A : C) [IsConnected A] :
    Nat.card (Aut A) ≤ Nat.card (F.obj A) := by
  have h : Nonempty (F.obj A) := inferInstance
  obtain ⟨a⟩ := h
  apply Nat.card_le_card_of_injective
  exact evaluation_aut_injective_of_isConnected _ _ a

end CardFiber

end PreGaloisCategory

/-- A `PreGaloisCategory` is a `GaloisCategory` if it admits a fiber functor. -/
/-
**CategoryTheory.GaloisCategory** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：(C : Type u₁) → [CategoryTheory.Category.{u₂, u₁} C] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `PreGaloisCategory` is a `GaloisCategory` if it admits a fiber functor.
-/
class GaloisCategory (C : Type u₁) [Category.{u₂, u₁} C] : Prop
    extends PreGaloisCategory C where
  hasFiberFunctor : ∃ F : C ⥤ FintypeCat.{u₂}, Nonempty (PreGaloisCategory.FiberFunctor F)

namespace PreGaloisCategory

variable (C : Type u₁) [Category.{u₂, u₁} C] [GaloisCategory C]

/-- Arbitrarily choose a fiber functor for a Galois category using choice. -/
/-
**CategoryTheory.PreGaloisCategory.GaloisCategory.getFiberFunctor** 是 Mathlib 中的
一个定义，位于命名空间 `CategoryTheory.PreGaloisCategory.GaloisCategory`。
形式化陈述：(C : Type u₁) →   [inst : CategoryTheory.Category.{u₂, u₁} C] → [CategoryT
heory.GaloisCategory C] → CategoryTheory.Functor C FintypeCat
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GaloisCategory.toPreGaloisCategory`：∀ {C : Type u₁} {inst
 : CategoryTheory.Category.{u₂, u₁} C} [self : CategoryTheory.GaloisCategory C],
   CategoryTheory.PreGaloisCategory C
· 使用定理 `CategoryTheory.GaloisCategory.hasFiberFunctor`：∀ {C : Type u₁} {inst : C
ategoryTheory.Category.{u₂, u₁} C} [self : CategoryTheory.GaloisCategory C],   ∃
 F, Nonempty (CategoryTheory.PreGal…

--- 原说明 ---
Arbitrarily choose a fiber functor for a Galois category using choice.
-/
noncomputable def GaloisCategory.getFiberFunctor : C ⥤ FintypeCat.{u₂} :=
  Classical.choose <| @GaloisCategory.hasFiberFunctor C _ _

/-- The arbitrarily chosen fiber functor `GaloisCategory.getFiberFunctor` is a fiber functor. -/
/-
**CategoryTheory.PreGaloisCategory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Pr
eGaloisCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The arbitrarily chosen fiber functor `GaloisCategory.getFiberFunctor` is a fiber
 functor.
-/
noncomputable instance : FiberFunctor (GaloisCategory.getFiberFunctor C) :=
  Classical.choice <| Classical.choose_spec (@GaloisCategory.hasFiberFunctor C _ _)

variable {C}

/-- In a `GaloisCategory` the set of morphisms out of a connected object is finite. -/
/-
**CategoryTheory.PreGaloisCategory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Pr
eGaloisCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In a `GaloisCategory` the set of morphisms out of a connected object is finite.
-/
instance (A X : C) [IsConnected A] : Finite (A ⟶ X) := by
  let F := GaloisCategory.getFiberFunctor C
  obtain ⟨a⟩ := nonempty_fiber_of_isConnected F A
  apply Finite.of_injective (fun f ↦ F.map f a)
  exact evaluation_injective_of_isConnected F A X a

/-- In a `GaloisCategory` the set of automorphism of a connected object is finite. -/
/-
**CategoryTheory.PreGaloisCategory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Pr
eGaloisCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In a `GaloisCategory` the set of automorphism of a connected object is finite.
-/
instance (A : C) [IsConnected A] : Finite (Aut A) := by
  let F := GaloisCategory.getFiberFunctor C
  obtain ⟨a⟩ := nonempty_fiber_of_isConnected F A
  apply Finite.of_injective (fun f ↦ F.map f.hom a)
  exact evaluation_aut_injective_of_isConnected F A a

/-- Coproduct inclusions are monic in Galois categories. -/
/-
**CategoryTheory.PreGaloisCategory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Pr
eGaloisCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Coproduct inclusions are monic in Galois categories.
-/
instance : MonoCoprod C := by
  let F := GaloisCategory.getFiberFunctor C
  exact MonoCoprod.monoCoprod_of_preservesCoprod_of_reflectsMono F

end PreGaloisCategory

end CategoryTheory

