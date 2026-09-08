/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.CochainComplexPlus
public import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import Mathlib.Algebra.Homology.Precylinder
public import Mathlib.CategoryTheory.Localization.OfQuotient
public import Mathlib.CategoryTheory.Shift.SingleFunctorsLift

/-!
# The triangulated subcategory of bounded below cochain complexes up to homotopy

In this file, we introduce the triangulated full subcategory `HomotopyCategory.Plus C`
of `HomotopyCategory C (.up ℤ)` consisting of bounded below cochain complexes.

-/

@[expose] public section

open CategoryTheory Limits ZeroObject Pretriangulated HomotopicalAlgebra

variable (C D : Type*) [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  (A : Type*) [Category* A] [Abelian A]

namespace CochainComplex

open HomologicalComplex

variable {C} [HasBinaryBiproducts C]

set_option backward.defeqAttrib.useBackward true in
/-
**CochainComplex.plus_cylinder** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex`。
形式化陈述：plus_cylinder (K : CochainComplex C Int) (hK : CochainComplex.plus C K) : 
CochainComplex.plus C (cylinder K)
参数：K : CochainComplex C Int；hK : CochainComplex.plus C K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `CategoryTheory.Limits.HasBinaryBiproducts.has_binary_biproduct`：∀ {C : T
ype uC} {inst : CategoryTheory.Category.{uC', uC} C} {inst_1 : CategoryTheory.Li
mits.HasZeroMorphisms C}   [self : CategoryTheory.Li…
· 使用定理 `CochainComplex.instHasHomotopyCofiberOfHasBinaryBiproductXHAddOfNat`：∀ {
C : Type u_1} [inst : CategoryTheory.Category.{v, u_1} C] [inst_1 : CategoryTheo
ry.Preadditive C] {ι : Type u_3}   [inst_2 : AddRightCanc…
· 使用定理 `HomologicalComplex.instHasBinaryBiproduct`：∀ {C : Type u_1} {ι : Type u_
2} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadd
itive C]   {c : ComplexShape ι}…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CochainComplex.isStrictlyGE_iff`：isStrictlyGE_iff (n : Int) : K.IsStrict
lyGE n ↔ forall (i : Int) (_ : i < n
· 使用引理 `HomologicalComplex.homotopyCofiber.isZero_X`：isZero_X (i : ι) (hG : IsZe
ro (G.X i)) (hF : forall (j : ι), c.Rel i j -> IsZero (F.X j)) : IsZero (X φ i)
· 使用定理 `CategoryTheory.Limits.IsZero.of_iso`：of_iso (hY : IsZero Y) (e : X ≅ Y) 
: IsZero X
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `HomologicalComplex.instPreservesZeroMorphismsEval`：∀ {ι : Type u_1} (V :
 Type u) [inst : CategoryTheory.Category.{v, u} V]   [inst_1 : CategoryTheory.Li
mits.HasZeroMorphisms V] (c : ComplexSh…
· 使用定理 `HomologicalComplex.instPreservesBinaryBiproductEval`：∀ {C : Type u_1} {ι
 : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryThe
ory.Preadditive C]   {c : ComplexShape ι}…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用引理 `CochainComplex.isZero_of_isStrictlyGE`：isZero_of_isStrictlyGE (n i : Int
) (hi : i < n
-/
lemma plus_cylinder (K : CochainComplex C ℤ) (hK : CochainComplex.plus C K) :
    CochainComplex.plus C (cylinder K) := by
  obtain ⟨n, hn⟩ := hK
  refine ⟨n - 1, ?_⟩
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  dsimp [cylinder]
  refine homotopyCofiber.isZero_X _ _ ?_ (fun j hj ↦ ?_)
  · refine IsZero.of_iso ?_ ((HomologicalComplex.eval C (.up ℤ) i).mapBiprod _ _)
    simpa using K.isZero_of_isStrictlyGE n i
  · simp only [ComplexShape.up_Rel] at hj
    exact K.isZero_of_isStrictlyGE n _ (by lia)
/-
**CochainComplex.plus_pathObject** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex`。
形式化陈述：plus_pathObject (K : CochainComplex C Int) (hK : CochainComplex.plus C K) 
: CochainComplex.plus C (pathObject K)
参数：K : CochainComplex C Int；hK : CochainComplex.plus C K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `CategoryTheory.Limits.HasBinaryBiproducts.has_binary_biproduct`：∀ {C : T
ype uC} {inst : CategoryTheory.Category.{uC', uC} C} {inst_1 : CategoryTheory.Li
mits.HasZeroMorphisms C}   [self : CategoryTheory.Li…
· 使用定理 `HomologicalComplex.instHasHomotopyFiberOfHasBinaryBiproducts`：∀ {C : Typ
e u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Pr
eadditive C] {α : Type u_2}   {c : ComplexShape α}…
· 使用定理 `HomologicalComplex.instHasBinaryBiproduct`：∀ {C : Type u_1} {ι : Type u_
2} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadd
itive C]   {c : ComplexShape ι}…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CochainComplex.isStrictlyGE_iff`：isStrictlyGE_iff (n : Int) : K.IsStrict
lyGE n ↔ forall (i : Int) (_ : i < n
· 使用引理 `HomologicalComplex.pathObject.isZero_X`：isZero_X (i : α) (h₁ : IsZero (K
.X i)) (h₂ : forall (j : α), c.Rel j i -> IsZero (K.X j)) : IsZero (K.pathObject
.X i)
· 使用引理 `CochainComplex.isZero_of_isStrictlyGE`：isZero_of_isStrictlyGE (n i : Int
) (hi : i < n
· 使用定理 `ComplexShape.up_Rel`：∀ (α : Type u_2) [inst : Add α] [inst_1 : IsRightCa
ncelAdd α] [inst_2 : One α] (i j : α),   (ComplexShape.up α).Rel i j = (i + 1 = 
j)
-/
lemma plus_pathObject (K : CochainComplex C ℤ) (hK : CochainComplex.plus C K) :
    CochainComplex.plus C (pathObject K) := by
  obtain ⟨n, hn⟩ := hK
  refine ⟨n - 1, ?_⟩
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  refine pathObject.isZero_X _ _ (K.isZero_of_isStrictlyGE n i)
    (fun j hj ↦ ?_)
  simp only [ComplexShape.up_Rel] at hj
  exact K.isZero_of_isStrictlyGE n j
/-
**CochainComplex.isStrictlyGE_mappingCone** 是 Mathlib 中的一个引理，位于命名空间 `CochainComp
lex`。
形式化陈述：isStrictlyGE_mappingCone {K L : CochainComplex C Int} (f : K ⟶ L) (n₁ n₂ n
 : Int) [K.IsStrictlyGE n₁] [L.IsStrictlyGE n₂] (hn₁ : n < n₁
参数：f : K ⟶ L；n₁ n₂ n : Int。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `CochainComplex.instHasHomotopyCofiberOfHasBinaryBiproductXHAddOfNat`：∀ {
C : Type u_1} [inst : CategoryTheory.Category.{v, u_1} C] [inst_1 : CategoryTheo
ry.Preadditive C] {ι : Type u_3}   [inst_2 : AddRightCanc…
· 使用定理 `CategoryTheory.Limits.HasBinaryBiproducts.has_binary_biproduct`：∀ {C : T
ype uC} {inst : CategoryTheory.Category.{uC', uC} C} {inst_1 : CategoryTheory.Li
mits.HasZeroMorphisms C}   [self : CategoryTheory.Li…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CochainComplex.isStrictlyGE_iff`：isStrictlyGE_iff (n : Int) : K.IsStrict
lyGE n ↔ forall (i : Int) (_ : i < n
· 使用引理 `CochainComplex.isZero_of_isStrictlyGE`：isZero_of_isStrictlyGE (n i : Int
) (hi : i < n
-/
lemma isStrictlyGE_mappingCone {K L : CochainComplex C ℤ} (f : K ⟶ L)
    (n₁ n₂ n : ℤ) [K.IsStrictlyGE n₁] [L.IsStrictlyGE n₂] (hn₁ : n < n₁ := by lia)
    (hn₂ : n ≤ n₂ := by lia) :
    (mappingCone f).IsStrictlyGE n := by
  rw [isStrictlyGE_iff]
  intro i hi
  simp at hi
  simp only [mappingCone.isZero_X_iff]
  exact ⟨K.isZero_of_isStrictlyGE n₁ _, L.isZero_of_isStrictlyGE n₂ _⟩

/-- The pre-cylinder object attached to `K : Plus C`. -/
/-
**CochainComplex.Plus.precylinder** 是 Mathlib 中的一个定义，位于命名空间 `CochainComplex.Plus
`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     [in
st_1 : CategoryTheory.Preadditive C] →       [CategoryTheory.Limits.HasBinaryBip
roducts C] → (K : CochainComplex.Plus C) → HomotopicalAlgebra.Precylinder K
参数：K : CochainComplex.Plus C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pre-cylinder object attached to `K : Plus C`.
-/
noncomputable abbrev Plus.precylinder (K : Plus C) : Precylinder K :=
  K.obj.precylinder.toFullSubcategory (K.obj.plus_cylinder K.property)

/-- The pre-path object attached to `K : Plus C`. -/
/-
**CochainComplex.Plus.prepathObject** 是 Mathlib 中的一个定义，位于命名空间 `CochainComplex.Pl
us`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     [in
st_1 : CategoryTheory.Preadditive C] →       [CategoryTheory.Limits.HasBinaryBip
roducts C] → (K : CochainComplex.Plus C) → HomotopicalAlgebra.PrepathObject K
参数：K : CochainComplex.Plus C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pre-path object attached to `K : Plus C`.
-/
noncomputable abbrev Plus.prepathObject (K : Plus C) : PrepathObject K :=
  K.obj.prepathObject.toFullSubcategory (K.obj.plus_pathObject K.property)

end CochainComplex

namespace HomotopyCategory

/-- The property of objects in `HomotopyCategory C (.up ℤ)` whose
underlying cochain complex is bounded below. (Note: this property of
objects is not closed under isomorphisms.) -/
/-
**HomotopyCategory.plus** 是 Mathlib 中的一个定义，位于命名空间 `HomotopyCategory`。
形式化陈述：plus : ObjectProperty (HomotopyCategory C (.up Int))
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The property of objects in `HomotopyCategory C (.up ℤ)` whose
underlying cochain complex is bounded below. (Note: this property of
objects is not closed under isomorphisms.)
-/
def plus : ObjectProperty (HomotopyCategory C (.up ℤ)) :=
  (CochainComplex.plus C).strictMap (quotient _ _)

variable {C} in
@[simp]
/-
**HomotopyCategory.plus_quotient_obj_iff** 是 Mathlib 中的一个引理，位于命名空间 `HomotopyCate
gory`。
形式化陈述：plus_quotient_obj_iff (K : CochainComplex C Int) : plus C ((quotient _ _).
obj K) ↔ CochainComplex.plus C K
参数：K : CochainComplex C Int。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
lemma plus_quotient_obj_iff (K : CochainComplex C ℤ) :
    plus C ((quotient _ _).obj K) ↔ CochainComplex.plus C K := by
  refine ⟨?_, fun h ↦ ⟨_, h⟩⟩
  simp only [plus, ObjectProperty.strictMap_iff]
  rintro ⟨L, h, hL⟩
  obtain rfl : L = K := congr_arg Quotient.as hL
  exact h
/-
**HomotopyCategory.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopyCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasZeroObject C] : (plus C).ContainsZero where
  exists_zero :=
    ⟨(HomotopyCategory.quotient _ _).obj 0, Functor.map_isZero _ (isZero_zero _), by
      simp only [plus_quotient_obj_iff]
      exact ⟨0, inferInstance⟩⟩
/-
**HomotopyCategory.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopyCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (plus C).IsStableUnderShift ℤ where
  isStableUnderShiftBy n :=
    { le_shift K hK := by
        obtain ⟨K : CochainComplex _ _, rfl⟩ := K.quotient_obj_surjective
        simp only [plus_quotient_obj_iff] at hK
        obtain ⟨q, _⟩ := hK
        rw [ObjectProperty.prop_shift_iff, shift_quotient_obj,
          plus_quotient_obj_iff]
        exact ⟨q - n, K.isStrictlyGE_shift q n (q - n) (by lia)⟩ }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**HomotopyCategory.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopyCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasZeroObject C] [HasBinaryBiproducts C] :
    (plus C).IsTriangulatedClosed₃ where
  ext₃' T hT h₁ h₂ := by
    obtain ⟨n₁, _⟩ : (CochainComplex.plus C) T.obj₁.as := by
      rwa [← plus_quotient_obj_iff]
    obtain ⟨n₂, _⟩ : (CochainComplex.plus C) T.obj₂.as := by
      rwa [← plus_quotient_obj_iff]
    obtain ⟨f : T.obj₁.as ⟶ T.obj₂.as, hf⟩ := (quotient _ _).map_surjective T.mor₁
    refine ⟨_, ?_,
      ⟨Triangle.π₃.mapIso (isoTriangleOfIso₁₂ T _ hT (mappingCone_triangleh_distinguished f)
        (Iso.refl _) (Iso.refl _) ?_)⟩⟩
    · dsimp
      simp only [plus_quotient_obj_iff]
      exact ⟨min (n₁ - 1) n₂, CochainComplex.isStrictlyGE_mappingCone f n₁ n₂ _
        (by simp) (by simp)⟩
    · simp [hf]
/-
**HomotopyCategory.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopyCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasZeroObject C] [HasBinaryBiproducts C] : (plus C).IsTriangulated where
  toIsTriangulatedClosed₂ := .of_isTriangulatedClosed₃

/-- The homotopy category of bounded below cochain complexes. -/
/-
**HomotopyCategory.Plus** 是 Mathlib 中的一个缩写定义，位于命名空间 `HomotopyCategory`。
形式化陈述：Plus
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The homotopy category of bounded below cochain complexes.
-/
abbrev Plus := (plus C).FullSubcategory

namespace Plus

/-- The inclusion of the homotopy category of bounded below cochain complexes
in the homotopy category category of all cochain complexes. -/
/-
**HomotopyCategory.Plus.** 是 Mathlib 中的一个缩写定义，位于命名空间 `HomotopyCategory.Plus`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion of the homotopy category of bounded below cochain complexes
in the homotopy category category of all cochain complexes.
-/
abbrev ι : Plus C ⥤ HomotopyCategory C (.up ℤ) := (plus C).ι

/-- The inclusion functor
`HomotopyCategory.ι C : HomotopyCategory.Plus C ⥤ HomotopyCategory C (.up ℤ)` is fully faithful. -/
/-
**HomotopyCategory.Plus.fullyFaithful** 是 Mathlib 中的一个缩写定义，位于命名空间 `HomotopyCateg
ory.Plus`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion functor
`HomotopyCategory.ι C : HomotopyCategory.Plus C ⥤ HomotopyCategory C (.up ℤ)` is
 fully faithful.
-/
abbrev fullyFaithfulι : (ι C).FullyFaithful := ObjectProperty.fullyFaithfulι _

/-- The class of quasi-isomorphisms in the homotopy category of bounded below cochain
complexes. -/
/-
**HomotopyCategory.Plus.quasiIso** 是 Mathlib 中的一个定义，位于命名空间 `HomotopyCategory.Plu
s`。
形式化陈述：quasiIso : MorphismProperty (Plus A)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C

--- 原说明 ---
The class of quasi-isomorphisms in the homotopy category of bounded below cochai
n
complexes.
-/
def quasiIso : MorphismProperty (Plus A) :=
  (HomotopyCategory.quasiIso A _).inverseImage (ι A)
deriving MorphismProperty.IsMultiplicative
/-
**HomotopyCategory.Plus.quasiIso_iff** 是 Mathlib 中的一个引理，位于命名空间 `HomotopyCategory
.Plus`。
形式化陈述：quasiIso_iff {K L : Plus A} (f : K ⟶ L) : quasiIso A f ↔ (HomotopyCategory
.quasiIso A _) f.hom
参数：f : K ⟶ L。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma quasiIso_iff {K L : Plus A} (f : K ⟶ L) :
    quasiIso A f ↔ (HomotopyCategory.quasiIso A _) f.hom := Iff.rfl
/-
**HomotopyCategory.Plus.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopyCategory.Plus`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (quasiIso A).IsCompatibleWithShift ℤ where
  condition a := by
    ext X Y f
    simp only [quasiIso_iff, ← MorphismProperty.IsCompatibleWithShift.iff
      (HomotopyCategory.quasiIso _ _) f.hom a]
    exact (HomotopyCategory.quasiIso _ _).arrow_mk_iso_iff
      (Arrow.isoOfNatIso ((ι A).commShiftIso a) (Arrow.mk f))
/-
**HomotopyCategory.Plus.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopyCategory.Plus`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (quasiIso A).RespectsIso := by
  dsimp only [quasiIso]
  infer_instance

/-- The full and essentially surjective functor
`CochainComplex.Plus C ⥤ HomotopyCategory.Plus C`. -/
@[simps!]
/-
**HomotopyCategory.Plus.quotient** 是 Mathlib 中的一个定义，位于命名空间 `HomotopyCategory.Plu
s`。
形式化陈述：quotient : CochainComplex.Plus C ⥤ Plus C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The full and essentially surjective functor
`CochainComplex.Plus C ⥤ HomotopyCategory.Plus C`.
-/
def quotient : CochainComplex.Plus C ⥤ Plus C :=
  ObjectProperty.lift _
    (CochainComplex.Plus.ι C ⋙ HomotopyCategory.quotient C (.up ℤ)) (by
      rintro ⟨K, h⟩
      simpa [plus_quotient_obj_iff])

/-- The functor
`HomotopyCategory.Plus.quotient C : CochainComplex.Plus C ⥤ HomotopyCategory.Plus C`
is induced by the functor `HomotopyCategory.quotient C (.up ℤ)` from `CochainComplex C ℤ`
to `HomotopyCategory C (.up ℤ)`. -/
/-
**HomotopyCategory.Plus.quotientComp** 是 Mathlib 中的一个定义，位于命名空间 `HomotopyCategory
.Plus`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor
`HomotopyCategory.Plus.quotient C : CochainComplex.Plus C ⥤ HomotopyCategory.Plu
s C`
is induced by the functor `HomotopyCategory.quotient C (.up ℤ)` from `CochainCom
plex C ℤ`
to `HomotopyCategory C (.up ℤ)`.
-/
def quotientCompιIso :
    quotient C ⋙ ι C ≅ CochainComplex.Plus.ι C ⋙ HomotopyCategory.quotient C (.up ℤ) :=
  ObjectProperty.liftCompιIso ..

variable {C} in
/-
**HomotopyCategory.Plus.quotient_obj_surjective** 是 Mathlib 中的一个引理，位于命名空间 `Homot
opyCategory.Plus`。
形式化陈述：quotient_obj_surjective : Function.Surjective (quotient C).obj
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HomotopyCategory.quotient_obj_surjective`：quotient_obj_surjective (X : H
omotopyCategory V c) : exists (K : HomologicalComplex V c), (quotient _ _).obj K
 = X
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `HomotopyCategory.plus_quotient_obj_iff`：plus_quotient_obj_iff (K : Cocha
inComplex C Int) : plus C ((quotient _ _).obj K) ↔ CochainComplex.plus C K
· 使用定理 `CategoryTheory.ObjectProperty.FullSubcategory.property`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.ObjectProperty C}  
 (self : P.FullSubcategory), P self.obj
· 使用定理 `CategoryTheory.ObjectProperty.FullSubcategory.ext`：∀ {C : Type u} {inst 
: CategoryTheory.Category.{v, u} C} {P : CategoryTheory.ObjectProperty C}   {x y
 : P.FullSubcategory}, x.obj = y.obj → …
-/
lemma quotient_obj_surjective : Function.Surjective (quotient C).obj :=
  fun K ↦ by
    obtain ⟨L, hL⟩ := HomotopyCategory.quotient_obj_surjective K.obj
    refine ⟨⟨L, ?_⟩, by ext; exact hL⟩
    rw [← HomotopyCategory.plus_quotient_obj_iff, hL]
    exact K.property
/-
**HomotopyCategory.Plus.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopyCategory.Plus`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (quotient C).EssSurj where
  mem_essImage K := by
    obtain ⟨L, rfl⟩ := quotient_obj_surjective K
    exact ⟨L, ⟨Iso.refl _⟩⟩
/-
**HomotopyCategory.Plus.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopyCategory.Plus`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (quotient C).Full := by dsimp [quotient]; infer_instance

section

variable [HasZeroObject C] [HasBinaryBiproducts C]

set_option backward.isDefEq.respectTransparency.types false in
open HomologicalComplex in
set_option backward.defeqAttrib.useBackward true in
/-
**HomotopyCategory.Plus.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopyCategory.Plus`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance :
    (quotient C).IsLocalization
      ((homotopyEquivalences C (.up ℤ)).inverseImage (CochainComplex.Plus.ι C)) :=
  Functor.isLocalization_of_essSurj_of_full_of_exists_cylinders _ _
    (fun _ _ f hf ↦ by
      simpa [← isIso_iff_of_reflects_iso _ (HomotopyCategory.Plus.ι C),
        ← inverseImage_quotient_isomorphisms] using! hf) (by
    rintro K L f₀ f₁ hf
    obtain ⟨f₀, rfl⟩ := ObjectProperty.homMk_surjective f₀
    obtain ⟨f₁, rfl⟩ := ObjectProperty.homMk_surjective f₁
    replace hf := homotopyOfEq f₀ f₁ ((HomotopyCategory.Plus.ι _).congr_map hf)
    exact ⟨K.precylinder, Precylinder.LeftHomotopy.fullSubcategoryEquiv.symm
      { h := cylinder.desc _ _ hf }, ⟨cylinder.homotopyEquiv _ (fun n ↦ ⟨n - 1, by simp⟩), rfl⟩⟩)

/-- The collection of all single functors `C ⥤ HomotopyCategory.Plus C` for `n : ℤ`
along with their compatibilities with shifts. -/
/-
**HomotopyCategory.Plus.singleFunctors** 是 Mathlib 中的一个定义，位于命名空间 `HomotopyCatego
ry.Plus`。
形式化陈述：singleFunctors : SingleFunctors C (Plus C) Int
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `HomotopyCategory.instIsStableUnderShiftIntUpPlus`：∀ (C : Type u_1) [inst
 : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C]
,   (HomotopyCategory.plus C).IsStable…

--- 原说明 ---
The collection of all single functors `C ⥤ HomotopyCategory.Plus C` for `n : ℤ`
along with their compatibilities with shifts.
-/
noncomputable def singleFunctors : SingleFunctors C (Plus C) ℤ :=
  SingleFunctors.lift (HomotopyCategory.singleFunctors C) (ι C)
    (fun n ↦ (plus C).lift (singleFunctor C n)
    (fun X ↦ by
      rw [← quotient_obj_singleFunctors_obj, plus_quotient_obj_iff]
      exact ⟨n, inferInstance⟩))
    (fun _ ↦ Iso.refl _)

/-- The single functor `C ⥤ HomotopyCategory.Plus C`. -/
/-
**HomotopyCategory.Plus.singleFunctor** 是 Mathlib 中的一个缩写定义，位于命名空间 `HomotopyCateg
ory.Plus`。
形式化陈述：singleFunctor (n : Int) : C ⥤ Plus C
参数：n : Int。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `HomotopyCategory.instIsStableUnderShiftIntUpPlus`：∀ (C : Type u_1) [inst
 : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C]
,   (HomotopyCategory.plus C).IsStable…

--- 原说明 ---
The single functor `C ⥤ HomotopyCategory.Plus C`.
-/
noncomputable abbrev singleFunctor (n : ℤ) : C ⥤ Plus C :=
  (singleFunctors C).functor n

/-- The single functor `C ⥤ HomotopyCategory.Plus C` is induced by
`HomotopyCategory.singleFunctor C n : C ⥤ HomotopyCategory C (.up ℤ)`. -/
/-
**HomotopyCategory.Plus.singleFunctorComp** 是 Mathlib 中的一个定义，位于命名空间 `HomotopyCat
egory.Plus`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The single functor `C ⥤ HomotopyCategory.Plus C` is induced by
`HomotopyCategory.singleFunctor C n : C ⥤ HomotopyCategory C (.up ℤ)`.
-/
noncomputable def singleFunctorCompιIso (n : ℤ) :
    singleFunctor C n ⋙ ι C ≅ HomotopyCategory.singleFunctor C n :=
  Iso.refl _

set_option backward.isDefEq.respectTransparency.types false in
/-
**HomotopyCategory.Plus.** 是 Mathlib 中的一个实例，位于命名空间 `HomotopyCategory.Plus`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (n : ℤ) : (singleFunctor C n).Additive := by
  dsimp [singleFunctor, singleFunctors]
  infer_instance

end

end Plus

end HomotopyCategory

namespace CategoryTheory

namespace Functor

variable {C D}
variable (F : C ⥤ D) [F.Additive]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The functor between bounded below homotopy categories that is induced
by an additive functor. -/
/-
**CategoryTheory.Functor.mapHomotopyCategoryPlus** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Functor`。
形式化陈述：mapHomotopyCategoryPlus : HomotopyCategory.Plus C ⥤ HomotopyCategory.Plus 
D
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor between bounded below homotopy categories that is induced
by an additive functor.
-/
def mapHomotopyCategoryPlus : HomotopyCategory.Plus C ⥤ HomotopyCategory.Plus D :=
  (HomotopyCategory.plus D).lift
    (HomotopyCategory.Plus.ι C ⋙ F.mapHomotopyCategory (ComplexShape.up ℤ)) (by
      rintro ⟨X, hX⟩
      obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
      dsimp
      simp only [HomotopyCategory.plus_quotient_obj_iff] at hX ⊢
      obtain ⟨n, _⟩ := hX
      exact ⟨n, inferInstanceAs (CochainComplex.IsStrictlyGE
        ((F.mapHomologicalComplex _).obj K) n)⟩)
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance :
    F.mapHomotopyCategoryPlus.CommShift ℤ :=
  inferInstanceAs (((HomotopyCategory.plus D).lift (HomotopyCategory.Plus.ι C ⋙
    F.mapHomotopyCategory (.up ℤ)) _).CommShift ℤ)

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasZeroObject C] [HasBinaryBiproducts C] [HasZeroObject D] [HasBinaryBiproducts D] :
    (F.mapHomotopyCategoryPlus).IsTriangulated := by
  dsimp only [mapHomotopyCategoryPlus]
  infer_instance
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Full F] [Faithful F] : Full F.mapHomotopyCategoryPlus where
  map_surjective f :=
    ⟨ObjectProperty.homMk ((F.mapHomotopyCategory _).preimage f.hom), by
      ext
      exact (F.mapHomotopyCategory _).map_preimage f.hom⟩
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Full F] [Faithful F] : Faithful F.mapHomotopyCategoryPlus where
  map_injective h := by
    ext
    exact (F.mapHomotopyCategory _).map_injective ((ObjectProperty.ι _).congr_map h)

/-- Given additive functors that are related by an isomorphism `F ⋙ G ≅ H`, this is
the corresponding isomorphism on the corresponding functor between
the bounded below homotopy categories. -/
/-
**CategoryTheory.Functor.mapHomotopyCategoryPlusCompIso** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory.Functor`。
形式化陈述：mapHomotopyCategoryPlusCompIso {E : Type*} [Category* E] [Preadditive E] {
F : C ⥤ D} {G : D ⥤ E} {H : C ⥤ E} (e : F ⋙ G ≅ H) [F.Additive] [G.Additive] [H.
Additive] : F.mapHomotopyCategoryPlus ⋙ G.mapHomotopyCategoryPlus ≅ H.mapHomotop
yCategoryPlus
参数：e : F ⋙ G ≅ H。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given additive functors that are related by an isomorphism `F ⋙ G ≅ H`, this is
the corresponding isomorphism on the corresponding functor between
the bounded below homotopy categories.
-/
def mapHomotopyCategoryPlusCompIso {E : Type*} [Category* E] [Preadditive E]
    {F : C ⥤ D} {G : D ⥤ E} {H : C ⥤ E} (e : F ⋙ G ≅ H)
    [F.Additive] [G.Additive] [H.Additive] :
    F.mapHomotopyCategoryPlus ⋙ G.mapHomotopyCategoryPlus ≅ H.mapHomotopyCategoryPlus :=
  ((HomotopyCategory.plus _).fullyFaithfulι.whiskeringRight _).preimageIso
    (isoWhiskerLeft (HomotopyCategory.Plus.ι C)
      (mapHomotopyCategoryCompIso e (.up ℤ)))

end Functor

end CategoryTheory

