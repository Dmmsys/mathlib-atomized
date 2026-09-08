/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.TStructure
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.Injective.Extend

/-!
# Computing `Ext` using an injective resolution

Given an injective resolution `R` of an object `Y` in an abelian category `C`,
we provide an API in order to construct elements in `Ext X Y n` in terms
of the complex `R.cocomplex` and to make computations in the `Ext`-group.

-/

@[expose] public section

universe w v u

open CategoryTheory CochainComplex HomComplex Abelian Localization

namespace CategoryTheory.InjectiveResolution

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  {X Y : C} (R : InjectiveResolution Y) {n : ℕ}

/-
**CategoryTheory.InjectiveResolution.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.
InjectiveResolution`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : R.cochainComplex.IsKInjective := isKInjective_of_injective _ 0

/-- If `R` is an injective resolution of `Y`, then `Ext X Y n` identifies
to the type of cohomology classes of degree `n` from `(singleFunctor C 0).obj X`
to `R.cochainComplex`. -/
/-
**CategoryTheory.InjectiveResolution.extEquivCohomologyClass** 是 Mathlib 中的一个定义，
位于命名空间 `CategoryTheory.InjectiveResolution`。
形式化陈述：extEquivCohomologyClass : Ext X Y n ≃ CohomologyClass ((singleFunctor C 0)
.obj X) R.cochainComplex n
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `CategoryTheory.InjectiveResolution.instIsKInjectiveCochainComplex`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abe
lian C] {Y : C}   (R : CategoryTheory.InjectiveResoluti…

--- 原说明 ---
If `R` is an injective resolution of `Y`, then `Ext X Y n` identifies
to the type of cohomology classes of degree `n` from `(singleFunctor C 0).obj X`
to `R.cochainComplex`.
-/
noncomputable def extEquivCohomologyClass :
    Ext X Y n ≃ CohomologyClass ((singleFunctor C 0).obj X) R.cochainComplex n :=
  (SmallShiftedHom.postcompEquiv.{w} R.ι'
      (by rw [HomologicalComplex.mem_quasiIso_iff]; infer_instance)).trans
    CochainComplex.HomComplex.CohomologyClass.equivOfIsKInjective.{w}.symm

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.InjectiveResolution.extEquivCohomologyClass_symm_mk_hom** 是 Mat
hlib 中的一个引理，位于命名空间 `CategoryTheory.InjectiveResolution`。
形式化陈述：extEquivCohomologyClass_symm_mk_hom [HasDerivedCategory C] (x : Cocycle ((
singleFunctor C 0).obj X) R.cochainComplex n) : (R.extEquivCohomologyClass.symm 
(.mk x)).hom = (ShiftedHom.mk₀ _ rfl ((DerivedCategory.singleFunctorIsoCompQ C 0
).hom.app X)).comp ((ShiftedHom.map (Cocycle.equivHomShift.symm x) DerivedCatego
ry.Q).comp (.mk₀ _ rfl (inv (DerivedCategory.Q.map R.ι') ≫ (DerivedCategory.sing
leFunctorIsoCompQ C 0).inv.app Y)) (zero_add _)) (add_zero _)
参数：x : Cocycle ((singleFunctor C 0).obj X) R.cochainComplex n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `DerivedCategory.instIsIsoMapCochainComplexIntQOfQuasiIso`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]  
 [inst_2 : HasDerivedCategory C] {K L : Cochai…
· 使用定理 `CategoryTheory.InjectiveResolution.instQuasiIsoIntι'`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C] {X : 
C}   (R : CategoryTheory.InjectiveResoluti…
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `CategoryTheory.categoryWithHomology_of_abelian`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C],   Category
Theory.CategoryWithHomology C
· 使用定理 `DerivedCategory.instIsLocalizationCochainComplexIntQQuasiIsoUp`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelia
n C]   [inst_2 : HasDerivedCategory C], DerivedCateg…
· 使用定理 `CochainComplex.instIsCompatibleWithShiftHomologicalComplexIntUpQuasiIso`
：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : Catego
ryTheory.Preadditive C]   [inst_2 : CategoryTheory.CategoryWi…
· 使用定理 `CategoryTheory.HasExt.instHasSmallLocalizedShiftedHomHomologicalComplexI
ntUpQuasiIsoOfIsGEOfIsLEOfNat`：∀ (C : Type u) [inst : CategoryTheory.Category.{v
, u} C] [inst_1 : CategoryTheory.Abelian C] [CategoryTheory.HasExt C]   (K L : C
ochainCompl…
· 使用定理 `HomologicalComplex.instIsSupportedOfIsStrictlySupported`：∀ {ι : Type u_1
} {ι' : Type u_2} {c : ComplexShape ι} {c' : ComplexShape ι'} {C : Type u_3}   [
inst : CategoryTheory.Category.{v_1, u_3} C] …
· 使用定理 `CochainComplex.instIsStrictlyGEObjIntSingleFunctor`：∀ {C : Type u_1} [in
st : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive 
C]   [inst_2 : CategoryTheory.Limits.Has…
· 使用定理 `CochainComplex.instIsStrictlyLEObjIntSingleFunctor`：∀ {C : Type u_1} [in
st : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive 
C]   [inst_2 : CategoryTheory.Limits.Has…
· 使用定理 `CategoryTheory.InjectiveResolution.instIsStrictlyGECochainComplexOfNatIn
t_1`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Category
Theory.Limits.HasZeroObject C]   [inst_2 : CategoryTheory.Preaddi…
· 使用定理 `CategoryTheory.InjectiveResolution.instIsLECochainComplexOfNatInt`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abe
lian C] {X : C}   (R : CategoryTheory.InjectiveResoluti…
· 使用定理 `CategoryTheory.Localization.inverts`：inverts : W.IsInvertedBy L
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `CategoryTheory.Localization.SmallShiftedHom.equiv_comp`：equiv_comp [HasS
mallLocalizedShiftedHom.{w} W M X Y] [HasSmallLocalizedShiftedHom.{w} W M Y Z] [
HasSmallLocalizedShiftedHom.{w} W M X Z] [Ha…
· 使用定理 `CategoryTheory.ShiftedHom.comp.congr_simp`：∀ {C : Type u_1} [inst : Cate
goryTheory.Category.{v_1, u_1} C] {M : Type u_4} [inst_1 : AddMonoid M]   [inst_
2 : CategoryTheory.HasShift C M…
· 使用引理 `CochainComplex.HomComplex.CohomologyClass.equiv_toSmallShiftedHom_mk`：eq
uiv_toSmallShiftedHom_mk [HasDerivedCategory C] (x : Cocycle K L n) : SmallShift
edHom.equiv _ DerivedCategory.Q (mk x).toSmallShiftedHom =…
· 使用引理 `CategoryTheory.Localization.SmallShiftedHom.equiv_mk₀Inv`：equiv_mk₀Inv [
HasSmallLocalizedShiftedHom.{w} W M Y X] [W.RespectsIso] (m₀ : M) (hm₀ : m₀ = 0)
 (f : X ⟶ Y) (hf : W f) : equiv W L (mk₀Inv m₀…
· 使用引理 `CategoryTheory.ShiftedHom.mk₀_id_comp`：mk₀_id_comp (m₀ : M) (hm₀ : m₀ = 
0) {a : M} (f : ShiftedHom X Y a) : (mk₀ m₀ hm₀ (𝟙 X)).comp f (by rw [hm₀, add_z
ero]) = f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
（共 31 条，此处仅展示前 30 条）
-/
lemma extEquivCohomologyClass_symm_mk_hom [HasDerivedCategory C]
    (x : Cocycle ((singleFunctor C 0).obj X) R.cochainComplex n) :
    (R.extEquivCohomologyClass.symm (.mk x)).hom =
      (ShiftedHom.mk₀ _ rfl ((DerivedCategory.singleFunctorIsoCompQ C 0).hom.app X)).comp
        ((ShiftedHom.map (Cocycle.equivHomShift.symm x) DerivedCategory.Q).comp
        (.mk₀ _ rfl (inv (DerivedCategory.Q.map R.ι') ≫
          (DerivedCategory.singleFunctorIsoCompQ C 0).inv.app Y)) (zero_add _)) (add_zero _) := by
  change SmallShiftedHom.equiv _ _ ((CohomologyClass.mk x).toSmallShiftedHom.comp _ _) = _
  simp only [SmallShiftedHom.equiv_comp, CohomologyClass.equiv_toSmallShiftedHom_mk,
    SmallShiftedHom.equiv_mk₀Inv, isoOfHom, asIso_inv,
    DerivedCategory.singleFunctorIsoCompQ, Iso.refl_hom, NatTrans.id_app, Iso.refl_inv,
    ShiftedHom.mk₀_id_comp]
  congr
  cat_disch

set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**CategoryTheory.InjectiveResolution.extEquivCohomologyClass_symm_add** 是 Mathli
b 中的一个引理，位于命名空间 `CategoryTheory.InjectiveResolution`。
形式化陈述：extEquivCohomologyClass_symm_add (x y : CohomologyClass ((singleFunctor C 
0).obj X) R.cochainComplex n) : R.extEquivCohomologyClass.symm (x + y) = R.extEq
uivCohomologyClass.symm x + R.extEquivCohomologyClass.symm y
参数：x y : CohomologyClass ((singleFunctor C 0).obj X) R.cochainComplex n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用引理 `CochainComplex.HomComplex.CohomologyClass.mk_surjective`：mk_surjective :
 Function.Surjective (mk : Cocycle K L n -> _)
· 使用引理 `CategoryTheory.Abelian.Ext.ext`：ext {n : Nat} {α β : Ext X Y n} (h : α.h
om = β.hom) : α = β
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `DerivedCategory.instIsIsoMapCochainComplexIntQOfQuasiIso`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]  
 [inst_2 : HasDerivedCategory C] {K L : Cochai…
· 使用定理 `CategoryTheory.InjectiveResolution.instQuasiIsoIntι'`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C] {X : 
C}   (R : CategoryTheory.InjectiveResoluti…
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.InjectiveResolution.extEquivCohomologyClass_symm_mk_hom`：
extEquivCohomologyClass_symm_mk_hom [HasDerivedCategory C] (x : Cocycle ((single
Functor C 0).obj X) R.cochainComplex n) : (R.extEquivCohomol…
· 使用定理 `CategoryTheory.ShiftedHom.comp.congr_simp`：∀ {C : Type u_1} [inst : Cate
goryTheory.Category.{v_1, u_1} C] {M : Type u_4} [inst_1 : AddMonoid M]   [inst_
2 : CategoryTheory.HasShift C M…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
· 使用定理 `CategoryTheory.Functor.map_add`：map_add {X Y : C} {f g : X ⟶ Y} : F.map 
(f + g) = F.map f + F.map g
· 使用定理 `DerivedCategory.instAdditiveCochainComplexIntQ`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 :
 HasDerivedCategory C], DerivedCateg…
· 使用定理 `CategoryTheory.Preadditive.add_comp`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C)   (f f' 
: P ⟶ Q) (g : Q ⟶ R),   C…
· 使用引理 `CategoryTheory.ShiftedHom.add_comp`：add_comp {a b c : M} (α₁ α₂ : Shifte
dHom X Y a) (β : ShiftedHom Y Z b) (h : b + a = c) : (α₁ + α₂).comp β h = α₁.com
p β h + α₂.comp β h
· 使用引理 `CategoryTheory.ShiftedHom.comp_add`：comp_add [forall (a : M), (shiftFunc
tor C a).Additive] {a b c : M} (α : ShiftedHom X Y a) (β₁ β₂ : ShiftedHom Y Z b)
 (h : b + a = c) : α.com…
· 使用定理 `DerivedCategory.instAdditiveShiftFunctorInt`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C]   [inst_2 : Ha
sDerivedCategory C] (n : ℤ), (Cat…
· 使用引理 `CategoryTheory.Abelian.Ext.add_hom`：add_hom (α β : Ext X Y n) : (α + β).
hom = α.hom + β.hom
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma extEquivCohomologyClass_symm_add
    (x y : CohomologyClass ((singleFunctor C 0).obj X) R.cochainComplex n) :
    R.extEquivCohomologyClass.symm (x + y) =
      R.extEquivCohomologyClass.symm x + R.extEquivCohomologyClass.symm y := by
  have := HasDerivedCategory.standard C
  obtain ⟨x, rfl⟩ := x.mk_surjective
  obtain ⟨y, rfl⟩ := y.mk_surjective
  ext
  simp [← CohomologyClass.mk_add, extEquivCohomologyClass_symm_mk_hom, ShiftedHom.map]

/-- If `R` is an injective resolution of `Y`, then `Ext X Y n` identifies
to the group of cohomology classes of degree `n` from `(singleFunctor C 0).obj X`
to `R.cochainComplex`. -/
@[simps!]
/-
**CategoryTheory.InjectiveResolution.extAddEquivCohomologyClass** 是 Mathlib 中的一个
定义，位于命名空间 `CategoryTheory.InjectiveResolution`。
形式化陈述：extAddEquivCohomologyClass : Ext X Y n ≃+ CohomologyClass ((singleFunctor 
C 0).obj X) R.cochainComplex n
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
If `R` is an injective resolution of `Y`, then `Ext X Y n` identifies
to the group of cohomology classes of degree `n` from `(singleFunctor C 0).obj X
`
to `R.cochainComplex`.
-/
noncomputable def extAddEquivCohomologyClass :
    Ext X Y n ≃+ CohomologyClass ((singleFunctor C 0).obj X) R.cochainComplex n :=
  AddEquiv.symm
    { toEquiv := (R.extEquivCohomologyClass (X := X) (Y := Y) (n := n)).symm
      map_add' := by simp }

@[simp]
/-
**CategoryTheory.InjectiveResolution.extEquivCohomologyClass_symm_sub** 是 Mathli
b 中的一个引理，位于命名空间 `CategoryTheory.InjectiveResolution`。
形式化陈述：extEquivCohomologyClass_symm_sub (x y : CohomologyClass ((singleFunctor C 
0).obj X) R.cochainComplex n) : R.extEquivCohomologyClass.symm (x - y) = R.extEq
uivCohomologyClass.symm x - R.extEquivCohomologyClass.symm y
参数：x y : CohomologyClass ((singleFunctor C 0).obj X) R.cochainComplex n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `AddEquiv.map_sub`：∀ {G : Type u_7} {H : Type u_8} [inst : AddGroup G] [i
nst_1 : SubtractionMonoid H] (h : G ≃+ H) (x y : G),   h (x - y) = h x - h y
-/
lemma extEquivCohomologyClass_symm_sub
    (x y : CohomologyClass ((singleFunctor C 0).obj X) R.cochainComplex n) :
    R.extEquivCohomologyClass.symm (x - y) =
      R.extEquivCohomologyClass.symm x - R.extEquivCohomologyClass.symm y :=
  R.extAddEquivCohomologyClass.symm.map_sub _ _

@[simp]
/-
**CategoryTheory.InjectiveResolution.extEquivCohomologyClass_symm_neg** 是 Mathli
b 中的一个引理，位于命名空间 `CategoryTheory.InjectiveResolution`。
形式化陈述：extEquivCohomologyClass_symm_neg (x : CohomologyClass ((singleFunctor C 0)
.obj X) R.cochainComplex n) : R.extEquivCohomologyClass.symm (-x) = -R.extEquivC
ohomologyClass.symm x
参数：x : CohomologyClass ((singleFunctor C 0).obj X) R.cochainComplex n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `AddEquiv.map_neg`：∀ {G : Type u_7} {H : Type u_8} [inst : AddGroup G] [i
nst_1 : SubtractionMonoid H] (h : G ≃+ H) (x : G), h (-x) = -h x
-/
lemma extEquivCohomologyClass_symm_neg
    (x : CohomologyClass ((singleFunctor C 0).obj X) R.cochainComplex n) :
    R.extEquivCohomologyClass.symm (-x) =
      -R.extEquivCohomologyClass.symm x :=
  R.extAddEquivCohomologyClass.symm.map_neg _

@[simp]
/-
**CategoryTheory.InjectiveResolution.extEquivCohomologyClass_symm_zero** 是 Mathl
ib 中的一个引理，位于命名空间 `CategoryTheory.InjectiveResolution`。
形式化陈述：extEquivCohomologyClass_symm_zero : (R.extEquivCohomologyClass (X
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `AddEquiv.map_zero`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZeroClass 
M] [inst_1 : AddZeroClass N] (h : M ≃+ N), h 0 = 0
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
lemma extEquivCohomologyClass_symm_zero :
    (R.extEquivCohomologyClass (X := X) (n := n)).symm 0 = 0 :=
  R.extAddEquivCohomologyClass.symm.map_zero

@[simp]
/-
**CategoryTheory.InjectiveResolution.extEquivCohomologyClass_add** 是 Mathlib 中的一
个引理，位于命名空间 `CategoryTheory.InjectiveResolution`。
形式化陈述：extEquivCohomologyClass_add (x y : Ext X Y n) : R.extEquivCohomologyClass 
(x + y) = R.extEquivCohomologyClass x + R.extEquivCohomologyClass y
参数：x y : Ext X Y n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `AddEquiv.map_add`：∀ {M : Type u_4} {N : Type u_5} [inst : Add M] [inst_1
 : Add N] (f : M ≃+ N) (x y : M), f (x + y) = f x + f y
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
lemma extEquivCohomologyClass_add (x y : Ext X Y n) :
    R.extEquivCohomologyClass (x + y) =
      R.extEquivCohomologyClass x + R.extEquivCohomologyClass y :=
  R.extAddEquivCohomologyClass.map_add _ _

@[simp]
/-
**CategoryTheory.InjectiveResolution.extEquivCohomologyClass_sub** 是 Mathlib 中的一
个引理，位于命名空间 `CategoryTheory.InjectiveResolution`。
形式化陈述：extEquivCohomologyClass_sub (x y : Ext X Y n) : R.extEquivCohomologyClass 
(x - y) = R.extEquivCohomologyClass x - R.extEquivCohomologyClass y
参数：x y : Ext X Y n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `AddEquiv.map_sub`：∀ {G : Type u_7} {H : Type u_8} [inst : AddGroup G] [i
nst_1 : SubtractionMonoid H] (h : G ≃+ H) (x y : G),   h (x - y) = h x - h y
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
lemma extEquivCohomologyClass_sub (x y : Ext X Y n) :
    R.extEquivCohomologyClass (x - y) =
      R.extEquivCohomologyClass x - R.extEquivCohomologyClass y :=
  R.extAddEquivCohomologyClass.map_sub _ _

@[simp]
/-
**CategoryTheory.InjectiveResolution.extEquivCohomologyClass_neg** 是 Mathlib 中的一
个引理，位于命名空间 `CategoryTheory.InjectiveResolution`。
形式化陈述：extEquivCohomologyClass_neg (x : Ext X Y n) : R.extEquivCohomologyClass (-
x) = -R.extEquivCohomologyClass x
参数：x : Ext X Y n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `AddEquiv.map_neg`：∀ {G : Type u_7} {H : Type u_8} [inst : AddGroup G] [i
nst_1 : SubtractionMonoid H] (h : G ≃+ H) (x : G), h (-x) = -h x
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
lemma extEquivCohomologyClass_neg (x : Ext X Y n) :
    R.extEquivCohomologyClass (-x) =
      -R.extEquivCohomologyClass x :=
  R.extAddEquivCohomologyClass.map_neg _

variable (X n) in
@[simp]
/-
**CategoryTheory.InjectiveResolution.extEquivCohomologyClass_zero** 是 Mathlib 中的
一个引理，位于命名空间 `CategoryTheory.InjectiveResolution`。
形式化陈述：extEquivCohomologyClass_zero : R.extEquivCohomologyClass (0 : Ext X Y n) =
 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `AddEquiv.map_zero`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZeroClass 
M] [inst_1 : AddZeroClass N] (h : M ≃+ N), h 0 = 0
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
lemma extEquivCohomologyClass_zero :
    R.extEquivCohomologyClass (0 : Ext X Y n) = 0 :=
  R.extAddEquivCohomologyClass.map_zero

/-- Given an injective resolution `R` of an object `Y` of an abelian category,
this is a constructor for elements in `Ext X Y n` which takes as an input
a "cocycle" `f : X ⟶ R.cocomplex.X n`. -/
/-
**CategoryTheory.InjectiveResolution.extMk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.InjectiveResolution`。
形式化陈述：extMk {n : Nat} (f : X ⟶ R.cocomplex.X n) (m : Nat) (hm : n + 1 = m) (hf :
 f ≫ R.cocomplex.d n m = 0) : Ext X Y n
参数：f : X ⟶ R.cocomplex.X n；m : Nat；hm : n + 1 = m；hf : f ≫ R.cocomplex.d n m = 0
。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Given an injective resolution `R` of an object `Y` of an abelian category,
this is a constructor for elements in `Ext X Y n` which takes as an input
a "cocycle" `f : X ⟶ R.cocomplex.X n`.
-/
noncomputable def extMk {n : ℕ} (f : X ⟶ R.cocomplex.X n) (m : ℕ) (hm : n + 1 = m)
    (hf : f ≫ R.cocomplex.d n m = 0) :
    Ext X Y n :=
  R.extEquivCohomologyClass.symm
    (.mk (Cocycle.fromSingleMk (f ≫ (R.cochainComplexXIso n n rfl).inv) (zero_add _)
      m (by lia) (by simp [cochainComplex_d _ _ _ n m rfl rfl, reassoc_of% hf])))

@[simp]
/-
**CategoryTheory.InjectiveResolution.extEquivCohomologyClass_extMk** 是 Mathlib 中
的一个引理，位于命名空间 `CategoryTheory.InjectiveResolution`。
形式化陈述：extEquivCohomologyClass_extMk {n : Nat} (f : X ⟶ R.cocomplex.X n) (m : Nat
) (hm : n + 1 = m) (hf : f ≫ R.cocomplex.d n m = 0) : R.extEquivCohomologyClass 
(R.extMk f m hm hf) = (.mk (Cocycle.fromSingleMk (f ≫ (R.cochainComplexXIso n n 
rfl).inv) (zero_add _) m (by lia) (by simp [cochainComplex_d _ _ _ n m rfl rfl, 
reassoc_of% hf])))
参数：f : X ⟶ R.cocomplex.X n；m : Nat；hm : n + 1 = m；hf : f ≫ R.cocomplex.d n m = 0
。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma extEquivCohomologyClass_extMk {n : ℕ} (f : X ⟶ R.cocomplex.X n) (m : ℕ) (hm : n + 1 = m)
    (hf : f ≫ R.cocomplex.d n m = 0) :
    R.extEquivCohomologyClass (R.extMk f m hm hf) =
      (.mk (Cocycle.fromSingleMk (f ≫ (R.cochainComplexXIso n n rfl).inv) (zero_add _)
        m (by lia) (by simp [cochainComplex_d _ _ _ n m rfl rfl, reassoc_of% hf]))) := by
  simp [extMk]
/-
**CategoryTheory.InjectiveResolution.add_extMk** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.InjectiveResolution`。
形式化陈述：add_extMk {n : Nat} (f g : X ⟶ R.cocomplex.X n) (m : Nat) (hm : n + 1 = m)
 (hf : f ≫ R.cocomplex.d n m = 0) (hg : g ≫ R.cocomplex.d n m = 0) : R.extMk f m
 hm hf + R.extMk g m hm hg = R.extMk (f + g) m hm (by simp [hf, hg])
参数：f g : X ⟶ R.cocomplex.X n；m : Nat；hm : n + 1 = m；hf : f ≫ R.cocomplex.d n m =
 0；hg : g ≫ R.cocomplex.d n m = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `CategoryTheory.Preadditive.add_comp`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C)   (f f' 
: P ⟶ Q) (g : Q ⟶ R),   C…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CochainComplex.HomComplex.Cocycle.fromSingleMk.congr_simp`：∀ {C : Type u
} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive
 C]   [inst_2 : CategoryTheory.Limits.HasZeroOb…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `CategoryTheory.InjectiveResolution.cochainComplex_d`：cochainComplex_d (n
₁ n₂ : Int) (k₁ k₂ : Nat) (h₁ : k₁ = n₁) (h₂ : k₂ = n₂) : R.cochainComplex.d n₁ 
n₂ = (cochainComplexXIso _ _ _ h₁).hom ≫ …
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CochainComplex.HomComplex.Cocycle.fromSingleMk_add`：fromSingleMk_add {p 
q : Int} (f g : X ⟶ K.X q) {n : Int} (h : p + n = q) (q' : Int) (hq' : q + 1 = q
') (hf : f ≫ K.d q q' = 0) (hg : g ≫ K.d…
· 使用引理 `CategoryTheory.InjectiveResolution.extEquivCohomologyClass_symm_add`：ext
EquivCohomologyClass_symm_add (x y : CohomologyClass ((singleFunctor C 0).obj X)
 R.cochainComplex n) : R.extEquivCohomologyClass.symm (x …
-/
lemma add_extMk {n : ℕ} (f g : X ⟶ R.cocomplex.X n) (m : ℕ) (hm : n + 1 = m)
    (hf : f ≫ R.cocomplex.d n m = 0) (hg : g ≫ R.cocomplex.d n m = 0) :
    R.extMk f m hm hf + R.extMk g m hm hg =
      R.extMk (f + g) m hm (by simp [hf, hg]) := by
  simp only [extMk, Preadditive.add_comp]
  rw [Cocycle.fromSingleMk_add _ _ _ _ _
    (by simp [cochainComplex_d _ _ _ n m rfl rfl, reassoc_of% hf])
    (by simp [cochainComplex_d _ _ _ n m rfl rfl, reassoc_of% hg])]
  simp
/-
**CategoryTheory.InjectiveResolution.sub_extMk** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.InjectiveResolution`。
形式化陈述：sub_extMk {n : Nat} (f g : X ⟶ R.cocomplex.X n) (m : Nat) (hm : n + 1 = m)
 (hf : f ≫ R.cocomplex.d n m = 0) (hg : g ≫ R.cocomplex.d n m = 0) : R.extMk f m
 hm hf - R.extMk g m hm hg = R.extMk (f - g) m hm (by simp [hf, hg])
参数：f g : X ⟶ R.cocomplex.X n；m : Nat；hm : n + 1 = m；hf : f ≫ R.cocomplex.d n m =
 0；hg : g ≫ R.cocomplex.d n m = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `CategoryTheory.Preadditive.sub_comp`：sub_comp : (f - f') ≫ g = f ≫ g - f
' ≫ g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CochainComplex.HomComplex.Cocycle.fromSingleMk.congr_simp`：∀ {C : Type u
} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive
 C]   [inst_2 : CategoryTheory.Limits.HasZeroOb…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `CategoryTheory.InjectiveResolution.cochainComplex_d`：cochainComplex_d (n
₁ n₂ : Int) (k₁ k₂ : Nat) (h₁ : k₁ = n₁) (h₂ : k₂ = n₂) : R.cochainComplex.d n₁ 
n₂ = (cochainComplexXIso _ _ _ h₁).hom ≫ …
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CochainComplex.HomComplex.Cocycle.fromSingleMk_sub`：fromSingleMk_sub {p 
q : Int} (f g : X ⟶ K.X q) {n : Int} (h : p + n = q) (q' : Int) (hq' : q + 1 = q
') (hf : f ≫ K.d q q' = 0) (hg : g ≫ K.d…
· 使用引理 `CategoryTheory.InjectiveResolution.extEquivCohomologyClass_symm_sub`：ext
EquivCohomologyClass_symm_sub (x y : CohomologyClass ((singleFunctor C 0).obj X)
 R.cochainComplex n) : R.extEquivCohomologyClass.symm (x …
-/
lemma sub_extMk {n : ℕ} (f g : X ⟶ R.cocomplex.X n) (m : ℕ) (hm : n + 1 = m)
    (hf : f ≫ R.cocomplex.d n m = 0) (hg : g ≫ R.cocomplex.d n m = 0) :
    R.extMk f m hm hf - R.extMk g m hm hg =
      R.extMk (f - g) m hm (by simp [hf, hg]) := by
  dsimp [extMk]
  simp only [Preadditive.sub_comp]
  rw [Cocycle.fromSingleMk_sub _ _ _ _ _
    (by simp [cochainComplex_d _ _ _ n m rfl rfl, reassoc_of% hf])
    (by simp [cochainComplex_d _ _ _ n m rfl rfl, reassoc_of% hg])]
  simp
/-
**CategoryTheory.InjectiveResolution.neg_extMk** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.InjectiveResolution`。
形式化陈述：neg_extMk {n : Nat} (f : X ⟶ R.cocomplex.X n) (m : Nat) (hm : n + 1 = m) (
hf : f ≫ R.cocomplex.d n m = 0) : -R.extMk f m hm hf = R.extMk (-f) m hm (by sim
p [hf])
参数：f : X ⟶ R.cocomplex.X n；m : Nat；hm : n + 1 = m；hf : f ≫ R.cocomplex.d n m = 0
。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `CategoryTheory.Preadditive.neg_comp`：neg_comp : (-f) ≫ g = -f ≫ g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CochainComplex.HomComplex.Cocycle.fromSingleMk.congr_simp`：∀ {C : Type u
} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive
 C]   [inst_2 : CategoryTheory.Limits.HasZeroOb…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `CategoryTheory.InjectiveResolution.cochainComplex_d`：cochainComplex_d (n
₁ n₂ : Int) (k₁ k₂ : Nat) (h₁ : k₁ = n₁) (h₂ : k₂ = n₂) : R.cochainComplex.d n₁ 
n₂ = (cochainComplexXIso _ _ _ h₁).hom ≫ …
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CochainComplex.HomComplex.Cocycle.fromSingleMk_neg`：fromSingleMk_neg {p 
q : Int} (f : X ⟶ K.X q) {n : Int} (h : p + n = q) (q' : Int) (hq' : q + 1 = q')
 (hf : f ≫ K.d q q' = 0) : fromSingleMk …
· 使用引理 `CategoryTheory.InjectiveResolution.extEquivCohomologyClass_symm_neg`：ext
EquivCohomologyClass_symm_neg (x : CohomologyClass ((singleFunctor C 0).obj X) R
.cochainComplex n) : R.extEquivCohomologyClass.symm (-x) …
-/
lemma neg_extMk {n : ℕ} (f : X ⟶ R.cocomplex.X n) (m : ℕ) (hm : n + 1 = m)
    (hf : f ≫ R.cocomplex.d n m = 0) :
    -R.extMk f m hm hf = R.extMk (-f) m hm (by simp [hf]) := by
  dsimp [extMk]
  simp only [Preadditive.neg_comp]
  rw [Cocycle.fromSingleMk_neg _ _ _ _
    (by simp [cochainComplex_d _ _ _ n m rfl rfl, reassoc_of% hf])]
  simp

@[simp]
/-
**CategoryTheory.InjectiveResolution.extMk_zero** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.InjectiveResolution`。
形式化陈述：extMk_zero {n : Nat} (m : Nat) (hm : n + 1 = m) : R.extMk (0 : X ⟶ R.cocom
plex.X n) m hm (by simp) = 0
参数：m : Nat；hm : n + 1 = m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `CochainComplex.HomComplex.Cocycle.fromSingleMk.congr_simp`：∀ {C : Type u
} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive
 C]   [inst_2 : CategoryTheory.Limits.HasZeroOb…
· 使用引理 `CochainComplex.HomComplex.Cocycle.fromSingleMk_zero`：fromSingleMk_zero {
p q : Int} {n : Int} (h : p + n = q) (q' : Int) (hq' : q + 1 = q') : fromSingleM
k (0 : X ⟶ K.X q) h q' hq' (by simp) = 0
· 使用引理 `CategoryTheory.InjectiveResolution.extEquivCohomologyClass_symm_zero`：ex
tEquivCohomologyClass_symm_zero : (R.extEquivCohomologyClass (X
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma extMk_zero {n : ℕ} (m : ℕ) (hm : n + 1 = m) :
    R.extMk (0 : X ⟶ R.cocomplex.X n) m hm (by simp) = 0 := by
  simp [extMk]
/-
**CategoryTheory.InjectiveResolution.extMk_hom** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.InjectiveResolution`。
形式化陈述：extMk_hom [HasDerivedCategory C] {n : Nat} (f : X ⟶ R.cocomplex.X n) (m : 
Nat) (hm : n + 1 = m) (hf : f ≫ R.cocomplex.d n m = 0) : (R.extMk f m hm hf).hom
 = (ShiftedHom.mk₀ _ rfl ((DerivedCategory.singleFunctorIsoCompQ C 0).hom.app X)
).comp ((ShiftedHom.map (Cocycle.equivHomShift.symm (Cocycle.fromSingleMk (f ≫ (
R.cochainComplexXIso n n rfl).inv) (zero_add _) m (by lia) (by simp [cochainComp
lex_d _ _ _ n m rfl rfl, reassoc_of% hf]))) _).comp (.mk₀ _ rfl (inv (DerivedCat
egory.Q.map R.ι') ≫ (Deriv
参数：f : X ⟶ R.cocomplex.X n；m : Nat；hm : n + 1 = m；hf : f ≫ R.cocomplex.d n m = 0
。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用引理 `CategoryTheory.InjectiveResolution.extEquivCohomologyClass_symm_mk_hom`：
extEquivCohomologyClass_symm_mk_hom [HasDerivedCategory C] (x : Cocycle ((single
Functor C 0).obj X) R.cochainComplex n) : (R.extEquivCohomol…
-/
lemma extMk_hom
    [HasDerivedCategory C] {n : ℕ} (f : X ⟶ R.cocomplex.X n) (m : ℕ) (hm : n + 1 = m)
    (hf : f ≫ R.cocomplex.d n m = 0) :
    (R.extMk f m hm hf).hom =
    (ShiftedHom.mk₀ _ rfl ((DerivedCategory.singleFunctorIsoCompQ C 0).hom.app X)).comp
      ((ShiftedHom.map (Cocycle.equivHomShift.symm
        (Cocycle.fromSingleMk (f ≫ (R.cochainComplexXIso n n rfl).inv) (zero_add _) m
          (by lia) (by simp [cochainComplex_d _ _ _ n m rfl rfl, reassoc_of% hf]))) _).comp
            (.mk₀ _ rfl (inv (DerivedCategory.Q.map R.ι') ≫
              (DerivedCategory.singleFunctorIsoCompQ C 0).inv.app Y))
                (zero_add _)) (add_zero _) :=
  extEquivCohomologyClass_symm_mk_hom _ _
/-
**CategoryTheory.InjectiveResolution.extMk_eq_zero_iff** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.InjectiveResolution`。
形式化陈述：extMk_eq_zero_iff (f : X ⟶ R.cocomplex.X n) (m : Nat) (hm : n + 1 = m) (hf
 : f ≫ R.cocomplex.d n m = 0) (p : Nat) (hp : p + 1 = n) : R.extMk f m hm hf = 0
 ↔ exists (g : X ⟶ R.cocomplex.X p), g ≫ R.cocomplex.d p n = f
参数：f : X ⟶ R.cocomplex.X n；m : Nat；hm : n + 1 = m；hf : f ≫ R.cocomplex.d n m = 0
；p : Nat；hp : p + 1 = n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.apply_eq_iff_eq`：apply_eq_iff_eq (f : α ≃ β) {x y : α} : f x = f y
 ↔ x = y
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `CategoryTheory.InjectiveResolution.extEquivCohomologyClass_extMk`：extEqu
ivCohomologyClass_extMk {n : Nat} (f : X ⟶ R.cocomplex.X n) (m : Nat) (hm : n + 
1 = m) (hf : f ≫ R.cocomplex.d n m = 0) : R.extEquivCo…
· 使用引理 `CategoryTheory.InjectiveResolution.extEquivCohomologyClass_zero`：extEqui
vCohomologyClass_zero : R.extEquivCohomologyClass (0 : Ext X Y n) = 0
· 使用引理 `CochainComplex.HomComplex.Cocycle.fromSingleMk_mem_coboundaries_iff`：fro
mSingleMk_mem_coboundaries_iff {p q : Int} (f : X ⟶ K.X q) {n : Int} (h : p + n 
= q) (q' : Int) (hq' : q + 1 = q') (hf : f ≫ K.d q q' = 0…
· 使用引理 `CategoryTheory.InjectiveResolution.cochainComplex_d`：cochainComplex_d (n
₁ n₂ : Int) (k₁ k₂ : Nat) (h₁ : k₁ = n₁) (h₂ : k₂ = n₂) : R.cochainComplex.d n₁ 
n₂ = (cochainComplexXIso _ _ _ h₁).hom ≫ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.instStrongMonoOfIsRegularMono`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsRegula
rMono f],   CategoryTheory.StrongM…
· 使用定理 `CategoryTheory.instIsRegularMonoOfIsSplitMono`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsSplit
Mono f],   CategoryTheory.IsRegular…
· 使用定理 `CategoryTheory.IsSplitMono.of_iso`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) [CategoryTheory.IsIso f],   Categor
yTheory.IsSplitMono f
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
-/
lemma extMk_eq_zero_iff (f : X ⟶ R.cocomplex.X n) (m : ℕ) (hm : n + 1 = m)
    (hf : f ≫ R.cocomplex.d n m = 0)
    (p : ℕ) (hp : p + 1 = n) :
    R.extMk f m hm hf = 0 ↔
      ∃ (g : X ⟶ R.cocomplex.X p), g ≫ R.cocomplex.d p n = f := by
  simp only [← R.extEquivCohomologyClass.apply_eq_iff_eq,
    extEquivCohomologyClass_extMk, extEquivCohomologyClass_zero,
    CohomologyClass.mk_eq_zero_iff]
  rw [Cocycle.fromSingleMk_mem_coboundaries_iff _ _ _ _ _ p (by lia),
    R.cochainComplex_d _ _ _ _ rfl rfl]
  exact ⟨fun ⟨g, hg⟩ ↦ ⟨g ≫ (R.cochainComplexXIso p p rfl).hom,
      by simp only [← cancel_mono (R.cochainComplexXIso n n rfl).inv, Category.assoc, hg]⟩,
    fun ⟨g, hg⟩ ↦ ⟨g ≫ (R.cochainComplexXIso p p rfl).inv, by simp [← hg]⟩⟩
/-
**CategoryTheory.InjectiveResolution.extMk_surjective** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.InjectiveResolution`。
形式化陈述：extMk_surjective (α : Ext X Y n) (m : Nat) (hm : n + 1 = m) : exists (f : 
X ⟶ R.cocomplex.X n) (hf : f ≫ R.cocomplex.d n m = 0), R.extMk f m hm hf = α
参数：α : Ext X Y n；m : Nat；hm : n + 1 = m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用引理 `CochainComplex.HomComplex.CohomologyClass.mk_surjective`：mk_surjective :
 Function.Surjective (mk : Cocycle K L n -> _)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CochainComplex.HomComplex.Cocycle.fromSingleMk_surjective`：fromSingleMk_
surjective {p n : Int} (α : Cocycle ((singleFunctor C p).obj X) K n) (q : Int) (
h : p + n = q) (q' : Int) (hq' : q + 1 = q') : …
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.instStrongMonoOfIsRegularMono`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsRegula
rMono f],   CategoryTheory.StrongM…
· 使用定理 `CategoryTheory.instIsRegularMonoOfIsSplitMono`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsSplit
Mono f],   CategoryTheory.IsRegular…
· 使用定理 `CategoryTheory.IsSplitMono.of_iso`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) [CategoryTheory.IsIso f],   Categor
yTheory.IsSplitMono f
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用引理 `CategoryTheory.InjectiveResolution.cochainComplex_d`：cochainComplex_d (n
₁ n₂ : Int) (k₁ k₂ : Nat) (h₁ : k₁ = n₁) (h₂ : k₂ = n₂) : R.cochainComplex.d n₁ 
n₂ = (cochainComplexXIso _ _ _ h₁).hom ≫ …
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CochainComplex.HomComplex.Cocycle.fromSingleMk.congr_simp`：∀ {C : Type u
} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive
 C]   [inst_2 : CategoryTheory.Limits.HasZeroOb…
-/
lemma extMk_surjective (α : Ext X Y n) (m : ℕ) (hm : n + 1 = m) :
    ∃ (f : X ⟶ R.cocomplex.X n) (hf : f ≫ R.cocomplex.d n m = 0),
      R.extMk f m hm hf = α := by
  obtain ⟨x, rfl⟩ := R.extEquivCohomologyClass.symm.surjective α
  obtain ⟨x, rfl⟩ := x.mk_surjective
  obtain ⟨f, hf, rfl⟩ := Cocycle.fromSingleMk_surjective x n (by simp) m (by lia)
  exact ⟨f ≫ (R.cochainComplexXIso n n rfl).hom,
    by simpa [R.cochainComplex_d _ _ _ _ rfl rfl,
      ← cancel_mono (R.cochainComplexXIso m m rfl).inv] using hf, by simp [extMk]⟩
/-
**CategoryTheory.InjectiveResolution.mk** 是 Mathlib 中的一个ctor，位于命名空间 `CategoryThe
ory.InjectiveResolution`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Limits.HasZeroObject C] →       [inst_2 : CategoryTheory.Limits.
HasZeroMorphisms C] →         {Z : C} →           (cocomplex : CochainComplex C 
ℕ) →             autoParam (∀ (n : ℕ), CategoryTheory.Injective (cocomplex.X n))
                 CategoryTheory.InjectiveResolution.injective._autoParam →      
         [hasHomology : ∀ (i : ℕ), HomologicalComplex.HasHomology cocomplex i] →
                 (ι : (CochainComplex.single₀ C).obj Z ⟶ cocomplex) →           
        autoParam (QuasiIso ι) CategoryTheory.InjectiveResolution.quasiIso._auto
Param →                     CategoryTheory.InjectiveResolution Z
参数：cocomplex : CochainComplex C ℕ；∀ (n : ℕ), CategoryTheory.Injective (cocomplex
.X n)；i : ℕ；ι : (CochainComplex.single₀ C).obj Z ⟶ cocomplex；QuasiIso ι。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mk₀_comp_extMk {n : ℕ} (f : X ⟶ R.cocomplex.X n) (m : ℕ) (hm : n + 1 = m)
    (hf : f ≫ R.cocomplex.d n m = 0) {X' : C} (g : X' ⟶ X) :
    (Ext.mk₀ g).comp (R.extMk f m hm hf) (zero_add _) =
      R.extMk (g ≫ f) m hm (by simp [hf]) := by
  have := HasDerivedCategory.standard C
  ext
  simp only [extMk, Ext.comp_hom, Int.cast_ofNat_Int, Ext.mk₀_hom,
    extEquivCohomologyClass_symm_mk_hom, Category.assoc]
  rw [Cocycle.fromSingleMk_precomp g _ (zero_add _) _ (by lia) (by
      simp [cochainComplex_d _ _ _ n m rfl rfl, reassoc_of% hf]),
    Cocycle.equivHomShift_symm_precomp, ← ShiftedHom.mk₀_comp 0 rfl,
    ShiftedHom.map_comp,
    ShiftedHom.comp_assoc _ _ _ (add_zero _) (zero_add _) (by simp),
    ← ShiftedHom.comp_assoc _ _ _ (add_zero _) (add_zero (n : ℤ)) (by simp)]
  simp

variable {R} in
/-
**CategoryTheory.InjectiveResolution.extMk_comp_mk** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.InjectiveResolution`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma extMk_comp_mk₀ {n : ℕ} (f : X ⟶ R.cocomplex.X n) (m : ℕ) (hm : n + 1 = m)
    (hf : f ≫ R.cocomplex.d n m = 0)
    {Y' : C} {R' : InjectiveResolution Y'} {g : Y ⟶ Y'} (φ : Hom R R' g) :
    (R.extMk f m hm hf).comp (Ext.mk₀ g) (add_zero _) =
      R'.extMk (f ≫ φ.hom.f n) m hm (by simp [reassoc_of% hf]) := by
  have := HasDerivedCategory.standard C
  ext
  have : (f ≫ φ.hom.f n) ≫ (R'.cochainComplexXIso n n (by lia)).inv =
      (f ≫ (R.cochainComplexXIso n n (by lia)).inv) ≫ φ.hom'.f n := by
    simp [φ.hom'_f n n rfl]
  simp only [Ext.comp_hom, extMk_hom, Ext.mk₀_hom, this]
  rw [Cocycle.fromSingleMk_postcomp _ (zero_add _) _ (by lia)
      (by simp [R.cochainComplex_d _ _ _ _ rfl rfl, reassoc_of% hf]),
    Cocycle.equivHomShift_symm_postcomp,
    ← ShiftedHom.comp_mk₀ _ 0 rfl, ShiftedHom.map_comp,
    ShiftedHom.comp_assoc _ _ _ _ (zero_add _) (by simp),
    ShiftedHom.comp_assoc _ _ _ _ (zero_add _) (by simp),
    ShiftedHom.comp_assoc _ _ _ _ (zero_add _) (by simp),
    ShiftedHom.map_mk₀, ShiftedHom.mk₀_comp_mk₀, ShiftedHom.mk₀_comp_mk₀]
  congr 3
  rw [Category.assoc, ← NatTrans.naturality, ← Category.assoc, ← Category.assoc]
  congr 1
  simpa only [IsIso.eq_comp_inv, Category.assoc, IsIso.inv_comp_eq,
    Functor.map_comp] using! DerivedCategory.Q.congr_map φ.ι'_comp_hom'.symm

end CategoryTheory.InjectiveResolution

