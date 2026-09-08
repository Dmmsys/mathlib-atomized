/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle

/-!
# The Ext class of a short exact sequence

In this file, given a short exact short complex `S : ShortComplex C`
in an abelian category, we construct the associated class in
`Ext S.X₃ S.X₁ 1`.

-/

@[expose] public section

assert_not_exists TwoSidedIdeal

universe w' w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

open Localization Limits ZeroObject DerivedCategory Pretriangulated Abelian

namespace ShortComplex

variable (S : ShortComplex C)

/-
**CategoryTheory.ShortComplex.ext_mk** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.S
hortComplex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ext_mk₀_f_comp_ext_mk₀_g : (Ext.mk₀ S.f).comp (Ext.mk₀ S.g) (zero_add 0) = 0 := by simp

namespace ShortExact

variable {S}
variable (hS : S.ShortExact)

section

local notation "W" => HomologicalComplex.quasiIso C (ComplexShape.up ℤ)
local notation "S'" => S.map (CochainComplex.singleFunctor C 0)
local notation "hS'" => hS.map_of_exact (HomologicalComplex.single _ _ _)
local notation "K" => CochainComplex.mappingCone (ShortComplex.f S')
local notation "qis" => CochainComplex.mappingCone.descShortComplex S'
local notation "hqis" => CochainComplex.mappingCone.quasiIso_descShortComplex hS'
local notation "δ" => Triangle.mor₃ (CochainComplex.mappingCone.triangle (ShortComplex.f S'))

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.ShortComplex.ShortExact.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.ShortComplex.ShortExact`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasSmallLocalizedShiftedHom.{w} W ℤ (S').X₃ (S').X₁ := by
  dsimp
  infer_instance

set_option backward.defeqAttrib.useBackward true in
set_option backward.privateInPublic true in
include hS in
/-
**CategoryTheory.ShortComplex.ShortExact.hasSmallLocalizedHom_S'_X** 是 Mathlib 中
的一个引理，位于命名空间 `CategoryTheory.ShortComplex.ShortExact`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma hasSmallLocalizedHom_S'_X₃_K :
    HasSmallLocalizedHom.{w} W (S').X₃ K := by
  rw [Localization.hasSmallLocalizedHom_iff_target W (S').X₃ qis hqis]
  dsimp
  apply Localization.hasSmallLocalizedHom_of_hasSmallLocalizedShiftedHom₀ (M := ℤ)

set_option backward.privateInPublic true in
include hS in
/-
**CategoryTheory.ShortComplex.ShortExact.hasSmallLocalizedShiftedHom_K_S'_X** 是 
Mathlib 中的一个引理，位于命名空间 `CategoryTheory.ShortComplex.ShortExact`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma hasSmallLocalizedShiftedHom_K_S'_X₁ :
    HasSmallLocalizedShiftedHom.{w} W ℤ K (S').X₁ := by
  rw [Localization.hasSmallLocalizedShiftedHom_iff_source.{w} W ℤ qis hqis (S').X₁]
  infer_instance

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The class in `Ext S.X₃ S.X₁ 1` that is attached to a short exact
short complex `S` in an abelian category. -/
/-
**CategoryTheory.ShortComplex.ShortExact.extClass** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.ShortComplex.ShortExact`。
形式化陈述：extClass : Ext.{w} S.X₃ S.X₁ 1
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `_private.Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass.0.Categor
yTheory.ShortComplex.ShortExact.hasSmallLocalizedHom_S'_X₃_K`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C] [Cate
goryTheory.HasExt C]   {S : CategoryTheory…
· 使用定理 `_private.Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass.0.Categor
yTheory.ShortComplex.ShortExact.hasSmallLocalizedShiftedHom_K_S'_X₁`：∀ {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C
] [CategoryTheory.HasExt C]   {S : CategoryTheory…
· 使用定理 `CategoryTheory.Abelian.hasBinaryBiproducts`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   CategoryTheo
ry.Limits.HasBinaryBiproducts C

--- 原说明 ---
The class in `Ext S.X₃ S.X₁ 1` that is attached to a short exact
short complex `S` in an abelian category.
-/
noncomputable def extClass : Ext.{w} S.X₃ S.X₁ 1 := by
  have := hS.hasSmallLocalizedHom_S'_X₃_K
  have := hS.hasSmallLocalizedShiftedHom_K_S'_X₁
  change SmallHom W (S').X₃ ((S').X₁⟦(1 : ℤ)⟧)
  exact (SmallHom.mkInv qis hqis).comp (SmallHom.mk W δ)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CategoryTheory.ShortComplex.ShortExact.extClass_hom** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.ShortComplex.ShortExact`。
形式化陈述：extClass_hom [HasDerivedCategory.{w'} C] : hS.extClass.hom = hS.singleδ
该定理/引理给出了一组等式。
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
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用定理 `DerivedCategory.instIsLocalizationCochainComplexIntQQuasiIsoUp`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelia
n C]   [inst_2 : HasDerivedCategory C], DerivedCateg…
· 使用定理 `CategoryTheory.Localization.instHasSmallLocalizedHomObjShiftFunctor`：∀ {
C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] (W : CategoryTheory.Mor
phismProperty C) {M : Type w'}   [inst_1 : AddMonoid M] […
· 使用定理 `_private.Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass.0.Categor
yTheory.ShortComplex.ShortExact.hasSmallLocalizedHom_S'_X₃_K`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C] [Cate
goryTheory.HasExt C]   {S : CategoryTheory…
· 使用定理 `_private.Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass.0.Categor
yTheory.ShortComplex.ShortExact.hasSmallLocalizedShiftedHom_K_S'_X₁`：∀ {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C
] [CategoryTheory.HasExt C]   {S : CategoryTheory…
· 使用定理 `CategoryTheory.Abelian.hasBinaryBiproducts`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   CategoryTheo
ry.Limits.HasBinaryBiproducts C
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Localization.SmallHom.equiv_comp`：equiv_comp (L : C ⥤ D) 
[L.IsLocalization W] {X Y Z : C} [HasSmallLocalizedHom.{w} W X Y] [HasSmallLocal
izedHom.{w} W Y Z] [HasSmallLocalized…
· 使用引理 `CategoryTheory.Localization.SmallHom.equiv_mkInv`：equiv_mkInv (L : C ⥤ D
) [L.IsLocalization W] {X Y : C} (f : Y ⟶ X) (hf : W f) [HasSmallLocalizedHom.{w
} W X Y] : equiv.{w} W L (mkInv f hf) …
· 使用引理 `CategoryTheory.Localization.SmallHom.equiv_mk`：equiv_mk (L : C ⥤ D) [L.I
sLocalization W] {X Y : C} [HasSmallLocalizedHom.{w} W X Y] (f : X ⟶ Y) : equiv.
{w} W L (mk W f) = L.map f
· 使用引理 `CochainComplex.mappingCone.quasiIso_descShortComplex`：quasiIso_descShort
Complex : QuasiIso (descShortComplex S) where quasiIsoAt n
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用引理 `DerivedCategory.singleFunctorsPostcompQIso_hom_hom`：singleFunctorsPostco
mpQIso_hom_hom (n : Int) : (singleFunctorsPostcompQIso C).hom.hom n = 𝟙 _
· 使用引理 `DerivedCategory.singleFunctorsPostcompQIso_inv_hom`：singleFunctorsPostco
mpQIso_inv_hom (n : Int) : (singleFunctorsPostcompQIso C).inv.hom n = 𝟙 _
· 使用定理 `CategoryTheory.NatTrans.id_app`：id_app (F : C ⥤ D) (X : C) : (𝟙 F : F ⟶ 
F).app X = 𝟙 (F.obj X)
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
lemma extClass_hom [HasDerivedCategory.{w'} C] : hS.extClass.hom = hS.singleδ := by
  change SmallShiftedHom.equiv W Q hS.extClass = _
  dsimp [extClass, SmallShiftedHom.equiv]
  erw [SmallHom.equiv_comp]
  rw [SmallHom.equiv_mkInv, SmallHom.equiv_mk]
  dsimp [-Q_obj_single_obj, singleδ, triangleOfSESδ]
  rw [Category.assoc, Category.assoc, Category.assoc,
    singleFunctorsPostcompQIso_hom_hom, singleFunctorsPostcompQIso_inv_hom,
    NatTrans.id_app, Category.id_comp, NatTrans.id_app]
  simp only [SingleFunctors.postcomp, Functor.comp_obj]
  unfold CochainComplex.singleFunctors
  rw [Functor.map_id, Category.comp_id]
  rfl

end

@[simp]
/-
**CategoryTheory.ShortComplex.ShortExact.comp_extClass** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.ShortComplex.ShortExact`。
形式化陈述：comp_extClass : (Ext.mk₀ S.g).comp hS.extClass (zero_add 1) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Abelian.Ext.ext`：ext {n : Nat} {α β : Ext X Y n} (h : α.h
om = β.hom) : α = β
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `CategoryTheory.Abelian.Ext.comp_hom`：comp_hom {a b : Nat} (α : Ext X Y a
) (β : Ext Y Z b) {c : Nat} (h : a + b = c) : (α.comp β h).hom = α.hom.comp β.ho
m (by lia)
· 使用定理 `CategoryTheory.ShiftedHom.comp.congr_simp`：∀ {C : Type u_1} [inst : Cate
goryTheory.Category.{v_1, u_1} C] {M : Type u_4} [inst_1 : AddMonoid M]   [inst_
2 : CategoryTheory.HasShift C M…
· 使用引理 `CategoryTheory.Abelian.Ext.mk₀_hom`：mk₀_hom [HasDerivedCategory.{w'} C] 
(f : X ⟶ Y) : (mk₀ f).hom = ShiftedHom.mk₀ _ (by simp) ((singleFunctor C 0).map 
f)
· 使用引理 `CategoryTheory.ShortComplex.ShortExact.extClass_hom`：extClass_hom [HasDe
rivedCategory.{w'} C] : hS.extClass.hom = hS.singleδ
· 使用引理 `CategoryTheory.ShiftedHom.mk₀_comp`：mk₀_comp (m₀ : M) (hm₀ : m₀ = 0) (f 
: X ⟶ Y) {a : M} (g : ShiftedHom Y Z a) : (mk₀ m₀ hm₀ f).comp g (by rw [hm₀, add
_zero]) = f ≫ g
· 使用引理 `CategoryTheory.Abelian.Ext.zero_hom`：zero_hom : (0 : Ext X Y n).hom = 0
· 使用定理 `CategoryTheory.Pretriangulated.comp_distTriang_mor_zero₂₃`：comp_distTria
ng_mor_zero₂₃ (T : Triangle C) (H : T in distTriang C) : T.mor₂ ≫ T.mor₃ = 0
· 使用定理 `DerivedCategory.instHasZeroObject`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 : HasDerivedCa
tegory C], CategoryTheo…
· 使用定理 `DerivedCategory.instAdditiveShiftFunctorInt`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 : Ha
sDerivedCategory C] (n : ℤ), (Cat…
· 使用引理 `CategoryTheory.ShortComplex.ShortExact.singleTriangle_distinguished`：sin
gleTriangle_distinguished : hS.singleTriangle in distTriang (DerivedCategory C)
-/
lemma comp_extClass : (Ext.mk₀ S.g).comp hS.extClass (zero_add 1) = 0 := by
  let := HasDerivedCategory.standard C
  ext
  simp only [Ext.comp_hom, Ext.mk₀_hom, extClass_hom, Ext.zero_hom,
    ShiftedHom.mk₀_comp]
  exact comp_distTriang_mor_zero₂₃ _ hS.singleTriangle_distinguished

@[simp]
/-
**CategoryTheory.ShortComplex.ShortExact.comp_extClass_assoc** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.ShortComplex.ShortExact`。
形式化陈述：comp_extClass_assoc {Y : C} {n : Nat} (γ : Ext S.X₁ Y n) {n' : Nat} (h : 1
 + n = n') : (Ext.mk₀ S.g).comp (hS.extClass.comp γ h) (zero_add n') = 0
参数：γ : Ext S.X₁ Y n；h : 1 + n = n'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Abelian.Ext.comp_assoc`：comp_assoc {a₁ a₂ a₃ a₁₂ a₂₃ a : 
Nat} (α : Ext X Y a₁) (β : Ext Y Z a₂) (γ : Ext Z T a₃) (h₁₂ : a₁ + a₂ = a₁₂) (h
₂₃ : a₂ + a₃ = a₂₃) (h : a₁…
· 使用引理 `CategoryTheory.ShortComplex.ShortExact.comp_extClass`：comp_extClass : (E
xt.mk₀ S.g).comp hS.extClass (zero_add 1) = 0
· 使用引理 `CategoryTheory.Abelian.Ext.zero_comp`：zero_comp {m : Nat} (β : Ext Y Z m
) (p : Nat) (h : n + m = p) : (0 : Ext X Y n).comp β h = 0
-/
lemma comp_extClass_assoc {Y : C} {n : ℕ} (γ : Ext S.X₁ Y n) {n' : ℕ} (h : 1 + n = n') :
    (Ext.mk₀ S.g).comp (hS.extClass.comp γ h) (zero_add n') = 0 := by
  rw [← Ext.comp_assoc (a₁₂ := 1) _ _ _ (by lia) (by lia) (by lia),
    comp_extClass, Ext.zero_comp]

@[simp]
/-
**CategoryTheory.ShortComplex.ShortExact.extClass_comp** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.ShortComplex.ShortExact`。
形式化陈述：extClass_comp : hS.extClass.comp (Ext.mk₀ S.f) (add_zero 1) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Abelian.Ext.ext`：ext {n : Nat} {α β : Ext X Y n} (h : α.h
om = β.hom) : α = β
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `CategoryTheory.Abelian.Ext.comp_hom`：comp_hom {a b : Nat} (α : Ext X Y a
) (β : Ext Y Z b) {c : Nat} (h : a + b = c) : (α.comp β h).hom = α.hom.comp β.ho
m (by lia)
· 使用定理 `CategoryTheory.ShiftedHom.comp.congr_simp`：∀ {C : Type u_1} [inst : Cate
goryTheory.Category.{v_1, u_1} C] {M : Type u_4} [inst_1 : AddMonoid M]   [inst_
2 : CategoryTheory.HasShift C M…
· 使用引理 `CategoryTheory.ShortComplex.ShortExact.extClass_hom`：extClass_hom [HasDe
rivedCategory.{w'} C] : hS.extClass.hom = hS.singleδ
· 使用引理 `CategoryTheory.Abelian.Ext.mk₀_hom`：mk₀_hom [HasDerivedCategory.{w'} C] 
(f : X ⟶ Y) : (mk₀ f).hom = ShiftedHom.mk₀ _ (by simp) ((singleFunctor C 0).map 
f)
· 使用引理 `CategoryTheory.ShiftedHom.comp_mk₀`：comp_mk₀ {a : M} (f : ShiftedHom X Y
 a) (m₀ : M) (hm₀ : m₀ = 0) (g : Y ⟶ Z) : f.comp (mk₀ m₀ hm₀ g) (by rw [hm₀, zer
o_add]) = f ≫ g⟦a⟧'
· 使用引理 `CategoryTheory.Abelian.Ext.zero_hom`：zero_hom : (0 : Ext X Y n).hom = 0
· 使用定理 `CategoryTheory.Pretriangulated.comp_distTriang_mor_zero₃₁`：comp_distTria
ng_mor_zero₃₁ (T : Triangle C) (H : T in distTriang C) : T.mor₃ ≫ T.mor₁⟦1⟧' = 0
· 使用定理 `DerivedCategory.instHasZeroObject`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 : HasDerivedCa
tegory C], CategoryTheo…
· 使用定理 `DerivedCategory.instAdditiveShiftFunctorInt`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 : Ha
sDerivedCategory C] (n : ℤ), (Cat…
· 使用引理 `CategoryTheory.ShortComplex.ShortExact.singleTriangle_distinguished`：sin
gleTriangle_distinguished : hS.singleTriangle in distTriang (DerivedCategory C)
-/
lemma extClass_comp : hS.extClass.comp (Ext.mk₀ S.f) (add_zero 1) = 0 := by
  let := HasDerivedCategory.standard C
  ext
  simp only [Ext.comp_hom, Ext.mk₀_hom, extClass_hom, Ext.zero_hom,
    ShiftedHom.comp_mk₀]
  exact comp_distTriang_mor_zero₃₁ _ hS.singleTriangle_distinguished

@[simp]
/-
**CategoryTheory.ShortComplex.ShortExact.extClass_comp_assoc** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.ShortComplex.ShortExact`。
形式化陈述：extClass_comp_assoc {Y : C} {n : Nat} (γ : Ext S.X₂ Y n) {n' : Nat} {h : 1
 + n = n'} : hS.extClass.comp ((Ext.mk₀ S.f).comp γ (zero_add n)) h = 0
参数：γ : Ext S.X₂ Y n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Abelian.Ext.comp_assoc`：comp_assoc {a₁ a₂ a₃ a₁₂ a₂₃ a : 
Nat} (α : Ext X Y a₁) (β : Ext Y Z a₂) (γ : Ext Z T a₃) (h₁₂ : a₁ + a₂ = a₁₂) (h
₂₃ : a₂ + a₃ = a₂₃) (h : a₁…
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用引理 `CategoryTheory.ShortComplex.ShortExact.extClass_comp`：extClass_comp : hS
.extClass.comp (Ext.mk₀ S.f) (add_zero 1) = 0
· 使用引理 `CategoryTheory.Abelian.Ext.zero_comp`：zero_comp {m : Nat} (β : Ext Y Z m
) (p : Nat) (h : n + m = p) : (0 : Ext X Y n).comp β h = 0
-/
lemma extClass_comp_assoc {Y : C} {n : ℕ} (γ : Ext S.X₂ Y n) {n' : ℕ} {h : 1 + n = n'} :
    hS.extClass.comp ((Ext.mk₀ S.f).comp γ (zero_add n)) h = 0 := by
  rw [← Ext.comp_assoc (a₁₂ := 1) _ _ _ (by lia) (by lia) (by lia),
    extClass_comp, Ext.zero_comp]
/-
**CategoryTheory.ShortComplex.ShortExact.extClass_naturality** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.ShortComplex.ShortExact`。
形式化陈述：extClass_naturality {S₁ S₂ : ShortComplex C} (h₁ : S₁.ShortExact) (h₂ : S₂
.ShortExact) (f : S₁ ⟶ S₂) : h₁.extClass.comp (Ext.mk₀ f.τ₁) (add_zero 1) = (Ext
.mk₀ f.τ₃).comp h₂.extClass (zero_add 1)
参数：h₁ : S₁.ShortExact；h₂ : S₂.ShortExact；f : S₁ ⟶ S₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Abelian.Ext.ext`：ext {n : Nat} {α β : Ext X Y n} (h : α.h
om = β.hom) : α = β
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `CategoryTheory.Abelian.Ext.comp_hom`：comp_hom {a b : Nat} (α : Ext X Y a
) (β : Ext Y Z b) {c : Nat} (h : a + b = c) : (α.comp β h).hom = α.hom.comp β.ho
m (by lia)
· 使用定理 `CategoryTheory.ShiftedHom.comp.congr_simp`：∀ {C : Type u_1} [inst : Cate
goryTheory.Category.{v_1, u_1} C] {M : Type u_4} [inst_1 : AddMonoid M]   [inst_
2 : CategoryTheory.HasShift C M…
· 使用引理 `CategoryTheory.ShortComplex.ShortExact.extClass_hom`：extClass_hom [HasDe
rivedCategory.{w'} C] : hS.extClass.hom = hS.singleδ
· 使用引理 `CategoryTheory.Abelian.Ext.mk₀_hom`：mk₀_hom [HasDerivedCategory.{w'} C] 
(f : X ⟶ Y) : (mk₀ f).hom = ShiftedHom.mk₀ _ (by simp) ((singleFunctor C 0).map 
f)
· 使用引理 `CategoryTheory.ShiftedHom.comp_mk₀`：comp_mk₀ {a : M} (f : ShiftedHom X Y
 a) (m₀ : M) (hm₀ : m₀ = 0) (g : Y ⟶ Z) : f.comp (mk₀ m₀ hm₀ g) (by rw [hm₀, zer
o_add]) = f ≫ g⟦a⟧'
· 使用引理 `CategoryTheory.ShiftedHom.mk₀_comp`：mk₀_comp (m₀ : M) (hm₀ : m₀ = 0) (f 
: X ⟶ Y) {a : M} (g : ShiftedHom Y Z a) : (mk₀ m₀ hm₀ f).comp g (by rw [hm₀, add
_zero]) = f ≫ g
· 使用定理 `CategoryTheory.ShortComplex.ShortExact.singleTriangle_mor₃`：∀ {C : Type 
u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]
   [inst_2 : HasDerivedCategory C] {S : Category…
· 使用定理 `CategoryTheory.ShortComplex.ShortExact.singleTriangle.map_hom₁`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelia
n C]   [inst_2 : HasDerivedCategory C] {S₁ S₂ : Cate…
· 使用定理 `CategoryTheory.ShortComplex.ShortExact.singleTriangle.map_hom₃`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelia
n C]   [inst_2 : HasDerivedCategory C] {S₁ S₂ : Cate…
· 使用定理 `CategoryTheory.Pretriangulated.TriangleMorphism.comm₃`：∀ {C : Type u} [i
nst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.HasShift C ℤ]  
 {T₁ T₂ : CategoryTheory.Pretriangulated.Tr…
-/
lemma extClass_naturality {S₁ S₂ : ShortComplex C}
    (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact) (f : S₁ ⟶ S₂) :
    h₁.extClass.comp (Ext.mk₀ f.τ₁) (add_zero 1) =
      (Ext.mk₀ f.τ₃).comp h₂.extClass (zero_add 1) := by
  let := HasDerivedCategory.standard C
  ext
  simpa [ShiftedHom.comp_mk₀, ShiftedHom.mk₀_comp] using! (singleTriangle.map h₁ h₂ f).comm₃

end ShortExact

end ShortComplex

end CategoryTheory

