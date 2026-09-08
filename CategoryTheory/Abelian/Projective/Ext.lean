/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.TStructure
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import Mathlib.Algebra.Homology.HomotopyCategory.KProjective
public import Mathlib.CategoryTheory.Abelian.Projective.Extend

/-!
# Computing `Ext` using a projective resolution

Given a projective resolution `R` of an object `X` in an abelian category `C`,
we provide an API in order to construct elements in `Ext X Y n` in terms
of the complex `R.complex` and to make computations in the `Ext`-group.

## TODO
* Functoriality in `X`: this would involve a morphism `X ⟶ X'`, projective
  resolutions `R` and `R'` of `X` and `X'`, a lift of `X ⟶ X'` as a morphism
  of cochain complexes `R.complex ⟶ R'.complex`; in this context,
  we should be able to compute the precomposition of an element
  `R.extMk f m hm hf : Ext X' Y n` by `X ⟶ X'`.

-/

@[expose] public section

universe w v u

open CategoryTheory CochainComplex HomComplex Abelian Localization

namespace CategoryTheory.ProjectiveResolution

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  {X Y : C} (R : ProjectiveResolution X) {n : ℕ}

/-
**CategoryTheory.ProjectiveResolution.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory
.ProjectiveResolution`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : R.cochainComplex.IsKProjective := isKProjective_of_projective _ 0

/-- If `R` is a projective resolution of `X`, then `Ext X Y n` identifies
to the type of cohomology classes of degree `n` from `R.cochainComplex`
to `(singleFunctor C 0).obj Y`. -/
/-
**CategoryTheory.ProjectiveResolution.extEquivCohomologyClass** 是 Mathlib 中的一个定义
，位于命名空间 `CategoryTheory.ProjectiveResolution`。
形式化陈述：extEquivCohomologyClass : Ext X Y n ≃ CohomologyClass R.cochainComplex ((s
ingleFunctor C 0).obj Y) n
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
· 使用定理 `CategoryTheory.ProjectiveResolution.instIsKProjectiveCochainComplex`：∀ {
C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.A
belian C] {X : C}   (R : CategoryTheory.ProjectiveResolut…

--- 原说明 ---
If `R` is a projective resolution of `X`, then `Ext X Y n` identifies
to the type of cohomology classes of degree `n` from `R.cochainComplex`
to `(singleFunctor C 0).obj Y`.
-/
noncomputable def extEquivCohomologyClass :
    Ext X Y n ≃ CohomologyClass R.cochainComplex ((singleFunctor C 0).obj Y) n :=
  (SmallShiftedHom.precompEquiv.{w} R.π'
    ((by rw [HomologicalComplex.mem_quasiIso_iff]; infer_instance))).trans
      CochainComplex.HomComplex.CohomologyClass.equivOfIsKProjective.{w}.symm

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.ProjectiveResolution.extEquivCohomologyClass_symm_mk_hom** 是 Ma
thlib 中的一个引理，位于命名空间 `CategoryTheory.ProjectiveResolution`。
形式化陈述：extEquivCohomologyClass_symm_mk_hom [HasDerivedCategory C] (x : Cocycle R.
cochainComplex ((singleFunctor C 0).obj Y) n) : (R.extEquivCohomologyClass.symm 
(.mk x)).hom = (ShiftedHom.mk₀ _ rfl ((DerivedCategory.singleFunctorIsoCompQ C 0
).hom.app X ≫ inv (DerivedCategory.Q.map R.π'))).comp ((ShiftedHom.map (Cocycle.
equivHomShift.symm x) DerivedCategory.Q).comp (.mk₀ _ rfl ((DerivedCategory.sing
leFunctorIsoCompQ C 0).inv.app Y)) (zero_add _)) (add_zero _)
参数：x : Cocycle R.cochainComplex ((singleFunctor C 0).obj Y) n。
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
· 使用定理 `CategoryTheory.ProjectiveResolution.instQuasiIsoIntπ'`：∀ {C : Type u} [i
nst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C] {X :
 C}   (R : CategoryTheory.ProjectiveResolut…
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
· 使用定理 `CategoryTheory.ProjectiveResolution.instIsGECochainComplexOfNatInt`：∀ {C
 : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Ab
elian C] {X : C}   (R : CategoryTheory.ProjectiveResolut…
· 使用定理 `HomologicalComplex.instIsSupportedOfIsStrictlySupported`：∀ {ι : Type u_1
} {ι' : Type u_2} {c : ComplexShape ι} {c' : ComplexShape ι'} {C : Type u_3}   [
inst : CategoryTheory.Category.{v_1, u_3} C] …
· 使用定理 `CategoryTheory.ProjectiveResolution.instIsStrictlyLECochainComplexOfNatI
nt`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryT
heory.Limits.HasZeroObject C]   [inst_2 : CategoryTheory.Preaddi…
· 使用定理 `CochainComplex.instIsStrictlyGEObjIntSingleFunctor`：∀ {C : Type u_1} [in
st : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive 
C]   [inst_2 : CategoryTheory.Limits.Has…
· 使用定理 `CochainComplex.instIsStrictlyLEObjIntSingleFunctor`：∀ {C : Type u_1} [in
st : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive 
C]   [inst_2 : CategoryTheory.Limits.Has…
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
· 使用引理 `CategoryTheory.Localization.SmallShiftedHom.equiv_mk₀Inv`：equiv_mk₀Inv [
HasSmallLocalizedShiftedHom.{w} W M Y X] [W.RespectsIso] (m₀ : M) (hm₀ : m₀ = 0)
 (f : X ⟶ Y) (hf : W f) : equiv W L (mk₀Inv m₀…
· 使用引理 `CochainComplex.HomComplex.CohomologyClass.equiv_toSmallShiftedHom_mk`：eq
uiv_toSmallShiftedHom_mk [HasDerivedCategory C] (x : Cocycle K L n) : SmallShift
edHom.equiv _ DerivedCategory.Q (mk x).toSmallShiftedHom =…
· 使用定理 `CategoryTheory.ShiftedHom.mk₀.congr_simp`：∀ {C : Type u_1} [inst : Categ
oryTheory.Category.{v_1, u_1} C] {M : Type u_4} [inst_1 : AddMonoid M]   [inst_2
 : CategoryTheory.HasShift C M…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
（共 32 条，此处仅展示前 30 条）
-/
lemma extEquivCohomologyClass_symm_mk_hom [HasDerivedCategory C]
    (x : Cocycle R.cochainComplex ((singleFunctor C 0).obj Y) n) :
    (R.extEquivCohomologyClass.symm (.mk x)).hom =
    (ShiftedHom.mk₀ _ rfl ((DerivedCategory.singleFunctorIsoCompQ C 0).hom.app X ≫
      inv (DerivedCategory.Q.map R.π'))).comp
        ((ShiftedHom.map (Cocycle.equivHomShift.symm x) DerivedCategory.Q).comp
          (.mk₀ _ rfl ((DerivedCategory.singleFunctorIsoCompQ C 0).inv.app Y))
            (zero_add _)) (add_zero _) := by
  change SmallShiftedHom.equiv _ _ (.comp _ (CohomologyClass.mk x).toSmallShiftedHom _) = _
  simp only [SmallShiftedHom.equiv_comp, SmallShiftedHom.equiv_mk₀Inv, isoOfHom, asIso_inv,
    CohomologyClass.equiv_toSmallShiftedHom_mk,
    DerivedCategory.singleFunctorIsoCompQ, Iso.refl_hom, NatTrans.id_app, Category.id_comp,
    Iso.refl_inv]
  congr
  exact (ShiftedHom.comp_mk₀_id ..).symm

@[simp]
/-
**CategoryTheory.ProjectiveResolution.extEquivCohomologyClass_symm_add** 是 Mathl
ib 中的一个引理，位于命名空间 `CategoryTheory.ProjectiveResolution`。
形式化陈述：extEquivCohomologyClass_symm_add (x y : CohomologyClass R.cochainComplex (
(singleFunctor C 0).obj Y) n) : R.extEquivCohomologyClass.symm (x + y) = R.extEq
uivCohomologyClass.symm x + R.extEquivCohomologyClass.symm y
参数：x y : CohomologyClass R.cochainComplex ((singleFunctor C 0).obj Y) n。
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
· 使用定理 `CategoryTheory.ProjectiveResolution.instQuasiIsoIntπ'`：∀ {C : Type u} [i
nst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C] {X :
 C}   (R : CategoryTheory.ProjectiveResolut…
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ProjectiveResolution.extEquivCohomologyClass_symm_mk_hom`
：extEquivCohomologyClass_symm_mk_hom [HasDerivedCategory C] (x : Cocycle R.cocha
inComplex ((singleFunctor C 0).obj Y) n) : (R.extEquivCohomol…
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
    (x y : CohomologyClass R.cochainComplex ((singleFunctor C 0).obj Y) n) :
    R.extEquivCohomologyClass.symm (x + y) =
      R.extEquivCohomologyClass.symm x + R.extEquivCohomologyClass.symm y := by
  have := HasDerivedCategory.standard C
  obtain ⟨x, rfl⟩ := x.mk_surjective
  obtain ⟨y, rfl⟩ := y.mk_surjective
  ext
  simp [← CohomologyClass.mk_add, extEquivCohomologyClass_symm_mk_hom, ShiftedHom.map]

/-- If `R` is a projective resolution of `X`, then `Ext X Y n` identifies
to the type of cohomology classes of degree `n` from `R.cochainComplex`
to `(singleFunctor C 0).obj Y`. -/
@[simps!]
/-
**CategoryTheory.ProjectiveResolution.extAddEquivCohomologyClass** 是 Mathlib 中的一
个定义，位于命名空间 `CategoryTheory.ProjectiveResolution`。
形式化陈述：extAddEquivCohomologyClass : Ext X Y n ≃+ CohomologyClass R.cochainComplex
 ((singleFunctor C 0).obj Y) n
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
If `R` is a projective resolution of `X`, then `Ext X Y n` identifies
to the type of cohomology classes of degree `n` from `R.cochainComplex`
to `(singleFunctor C 0).obj Y`.
-/
noncomputable def extAddEquivCohomologyClass :
    Ext X Y n ≃+ CohomologyClass R.cochainComplex ((singleFunctor C 0).obj Y) n :=
  AddEquiv.symm
    { toEquiv := R.extEquivCohomologyClass.symm
      map_add' := by simp }

@[simp]
/-
**CategoryTheory.ProjectiveResolution.extEquivCohomologyClass_symm_sub** 是 Mathl
ib 中的一个引理，位于命名空间 `CategoryTheory.ProjectiveResolution`。
形式化陈述：extEquivCohomologyClass_symm_sub (x y : CohomologyClass R.cochainComplex (
(singleFunctor C 0).obj Y) n) : R.extEquivCohomologyClass.symm (x - y) = R.extEq
uivCohomologyClass.symm x - R.extEquivCohomologyClass.symm y
参数：x y : CohomologyClass R.cochainComplex ((singleFunctor C 0).obj Y) n。
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
    (x y : CohomologyClass R.cochainComplex ((singleFunctor C 0).obj Y) n) :
    R.extEquivCohomologyClass.symm (x - y) =
      R.extEquivCohomologyClass.symm x - R.extEquivCohomologyClass.symm y :=
  R.extAddEquivCohomologyClass.symm.map_sub _ _

@[simp]
/-
**CategoryTheory.ProjectiveResolution.extEquivCohomologyClass_symm_neg** 是 Mathl
ib 中的一个引理，位于命名空间 `CategoryTheory.ProjectiveResolution`。
形式化陈述：extEquivCohomologyClass_symm_neg (x : CohomologyClass R.cochainComplex ((s
ingleFunctor C 0).obj Y) n) : R.extEquivCohomologyClass.symm (-x) = -R.extEquivC
ohomologyClass.symm x
参数：x : CohomologyClass R.cochainComplex ((singleFunctor C 0).obj Y) n。
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
    (x : CohomologyClass R.cochainComplex ((singleFunctor C 0).obj Y) n) :
    R.extEquivCohomologyClass.symm (-x) =
      -R.extEquivCohomologyClass.symm x :=
  R.extAddEquivCohomologyClass.symm.map_neg _

@[simp]
/-
**CategoryTheory.ProjectiveResolution.extEquivCohomologyClass_symm_zero** 是 Math
lib 中的一个引理，位于命名空间 `CategoryTheory.ProjectiveResolution`。
形式化陈述：extEquivCohomologyClass_symm_zero : (R.extEquivCohomologyClass (Y
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
    (R.extEquivCohomologyClass (Y := Y) (n := n)).symm 0 = 0 :=
  R.extAddEquivCohomologyClass.symm.map_zero

@[simp]
/-
**CategoryTheory.ProjectiveResolution.extEquivCohomologyClass_add** 是 Mathlib 中的
一个引理，位于命名空间 `CategoryTheory.ProjectiveResolution`。
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
**CategoryTheory.ProjectiveResolution.extEquivCohomologyClass_sub** 是 Mathlib 中的
一个引理，位于命名空间 `CategoryTheory.ProjectiveResolution`。
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
**CategoryTheory.ProjectiveResolution.extEquivCohomologyClass_neg** 是 Mathlib 中的
一个引理，位于命名空间 `CategoryTheory.ProjectiveResolution`。
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
**CategoryTheory.ProjectiveResolution.extEquivCohomologyClass_zero** 是 Mathlib 中
的一个引理，位于命名空间 `CategoryTheory.ProjectiveResolution`。
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

/-- Given a projective resolution `R` of an object `X` of an abelian category,
this is a constructor for elements in `Ext X Y n` which takes as an input
a "cocycle" `f : R.cocomplex.X n ⟶ Y`. -/
/-
**CategoryTheory.ProjectiveResolution.extMk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.ProjectiveResolution`。
形式化陈述：extMk {n : Nat} (f : R.complex.X n ⟶ Y) (m : Nat) (hm : n + 1 = m) (hf : R
.complex.d m n ≫ f = 0) : Ext X Y n
参数：f : R.complex.X n ⟶ Y；m : Nat；hm : n + 1 = m；hf : R.complex.d m n ≫ f = 0。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Given a projective resolution `R` of an object `X` of an abelian category,
this is a constructor for elements in `Ext X Y n` which takes as an input
a "cocycle" `f : R.cocomplex.X n ⟶ Y`.
-/
noncomputable def extMk {n : ℕ} (f : R.complex.X n ⟶ Y) (m : ℕ) (hm : n + 1 = m)
    (hf : R.complex.d m n ≫ f = 0) :
    Ext X Y n :=
  R.extEquivCohomologyClass.symm
    (.mk (Cocycle.toSingleMk ((R.cochainComplexXIso (-n) n rfl).hom ≫ f) (by simp)
      (-m) (by lia) (by simpa [cochainComplex_d _ _ _ m n rfl rfl])))

@[simp]
/-
**CategoryTheory.ProjectiveResolution.extEquivCohomologyClass_extMk** 是 Mathlib 
中的一个引理，位于命名空间 `CategoryTheory.ProjectiveResolution`。
形式化陈述：extEquivCohomologyClass_extMk {n : Nat} (f : R.complex.X n ⟶ Y) (m : Nat) 
(hm : n + 1 = m) (hf : R.complex.d m n ≫ f = 0) : R.extEquivCohomologyClass (R.e
xtMk f m hm hf) = (.mk (Cocycle.toSingleMk ((R.cochainComplexXIso (-n) n rfl).ho
m ≫ f) (by simp) (-m) (by lia) (by simpa [cochainComplex_d _ _ _ m n rfl rfl])))
参数：f : R.complex.X n ⟶ Y；m : Nat；hm : n + 1 = m；hf : R.complex.d m n ≫ f = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma extEquivCohomologyClass_extMk {n : ℕ} (f : R.complex.X n ⟶ Y) (m : ℕ) (hm : n + 1 = m)
    (hf : R.complex.d m n ≫ f = 0) :
    R.extEquivCohomologyClass (R.extMk f m hm hf) =
      (.mk (Cocycle.toSingleMk ((R.cochainComplexXIso (-n) n rfl).hom ≫ f) (by simp)
        (-m) (by lia) (by simpa [cochainComplex_d _ _ _ m n rfl rfl]))) := by
  simp [extMk]
/-
**CategoryTheory.ProjectiveResolution.add_extMk** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.ProjectiveResolution`。
形式化陈述：add_extMk {n : Nat} (f g : R.complex.X n ⟶ Y) (m : Nat) (hm : n + 1 = m) (
hf : R.complex.d m n ≫ f = 0) (hg : R.complex.d m n ≫ g = 0) : R.extMk f m hm hf
 + R.extMk g m hm hg = R.extMk (f + g) m hm (by simp [hf, hg])
参数：f g : R.complex.X n ⟶ Y；m : Nat；hm : n + 1 = m；hf : R.complex.d m n ≫ f = 0；h
g : R.complex.d m n ≫ g = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `CategoryTheory.Preadditive.comp_add`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C) (f : P ⟶
 Q)   (g g' : Q ⟶ R),   C…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CochainComplex.HomComplex.Cocycle.toSingleMk.congr_simp`：∀ {C : Type u} 
[inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C
]   [inst_2 : CategoryTheory.Limits.HasZeroOb…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `CategoryTheory.ProjectiveResolution.cochainComplex_d`：cochainComplex_d (
n₁ n₂ : Int) (k₁ k₂ : Nat) (h₁ : -k₁ = n₁
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用引理 `CochainComplex.HomComplex.Cocycle.toSingleMk_add`：toSingleMk_add {p q : 
Int} (f g : K.X p ⟶ X) {n : Int} (h : p + n = q) (p' : Int) (hp' : p' + 1 = p) (
hf : K.d p' p ≫ f = 0) (hg : K.d p' p …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `CategoryTheory.ProjectiveResolution.extEquivCohomologyClass_symm_add`：ex
tEquivCohomologyClass_symm_add (x y : CohomologyClass R.cochainComplex ((singleF
unctor C 0).obj Y) n) : R.extEquivCohomologyClass.symm (x …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma add_extMk {n : ℕ} (f g : R.complex.X n ⟶ Y) (m : ℕ) (hm : n + 1 = m)
    (hf : R.complex.d m n ≫ f = 0) (hg : R.complex.d m n ≫ g = 0) :
    R.extMk f m hm hf + R.extMk g m hm hg =
      R.extMk (f + g) m hm (by simp [hf, hg]) := by
  simp only [extMk, Preadditive.comp_add]
  rw [Cocycle.toSingleMk_add _ _ _ _ _
    (by simpa [cochainComplex_d _ _ _ m n rfl rfl])
    (by simpa [cochainComplex_d _ _ _ m n rfl rfl])]
  simp
/-
**CategoryTheory.ProjectiveResolution.sub_extMk** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.ProjectiveResolution`。
形式化陈述：sub_extMk {n : Nat} (f g : R.complex.X n ⟶ Y) (m : Nat) (hm : n + 1 = m) (
hf : R.complex.d m n ≫ f = 0) (hg : R.complex.d m n ≫ g = 0) : R.extMk f m hm hf
 - R.extMk g m hm hg = R.extMk (f - g) m hm (by simp [hf, hg])
参数：f g : R.complex.X n ⟶ Y；m : Nat；hm : n + 1 = m；hf : R.complex.d m n ≫ f = 0；h
g : R.complex.d m n ≫ g = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `CategoryTheory.Preadditive.comp_sub`：comp_sub : f ≫ (g - g') = f ≫ g - f
 ≫ g'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CochainComplex.HomComplex.Cocycle.toSingleMk.congr_simp`：∀ {C : Type u} 
[inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C
]   [inst_2 : CategoryTheory.Limits.HasZeroOb…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `CategoryTheory.ProjectiveResolution.cochainComplex_d`：cochainComplex_d (
n₁ n₂ : Int) (k₁ k₂ : Nat) (h₁ : -k₁ = n₁
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用引理 `CochainComplex.HomComplex.Cocycle.toSingleMk_sub`：toSingleMk_sub {p q : 
Int} (f g : K.X p ⟶ X) {n : Int} (h : p + n = q) (p' : Int) (hp' : p' + 1 = p) (
hf : K.d p' p ≫ f = 0) (hg : K.d p' p …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `CategoryTheory.ProjectiveResolution.extEquivCohomologyClass_symm_sub`：ex
tEquivCohomologyClass_symm_sub (x y : CohomologyClass R.cochainComplex ((singleF
unctor C 0).obj Y) n) : R.extEquivCohomologyClass.symm (x …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma sub_extMk {n : ℕ} (f g : R.complex.X n ⟶ Y) (m : ℕ) (hm : n + 1 = m)
    (hf : R.complex.d m n ≫ f = 0) (hg : R.complex.d m n ≫ g = 0) :
    R.extMk f m hm hf - R.extMk g m hm hg =
      R.extMk (f - g) m hm (by simp [hf, hg]) := by
  simp only [extMk, Preadditive.comp_sub]
  rw [Cocycle.toSingleMk_sub _ _ _ _ _
    (by simpa [cochainComplex_d _ _ _ m n rfl rfl])
    (by simpa [cochainComplex_d _ _ _ m n rfl rfl])]
  simp
/-
**CategoryTheory.ProjectiveResolution.neg_extMk** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.ProjectiveResolution`。
形式化陈述：neg_extMk {n : Nat} (f : R.complex.X n ⟶ Y) (m : Nat) (hm : n + 1 = m) (hf
 : R.complex.d m n ≫ f = 0) : -R.extMk f m hm hf = R.extMk (-f) m hm (by simp [h
f])
参数：f : R.complex.X n ⟶ Y；m : Nat；hm : n + 1 = m；hf : R.complex.d m n ≫ f = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `CategoryTheory.Preadditive.comp_neg`：comp_neg : f ≫ (-g) = -f ≫ g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CochainComplex.HomComplex.Cocycle.toSingleMk.congr_simp`：∀ {C : Type u} 
[inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C
]   [inst_2 : CategoryTheory.Limits.HasZeroOb…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `CategoryTheory.ProjectiveResolution.cochainComplex_d`：cochainComplex_d (
n₁ n₂ : Int) (k₁ k₂ : Nat) (h₁ : -k₁ = n₁
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用引理 `CochainComplex.HomComplex.Cocycle.toSingleMk_neg`：toSingleMk_neg {p q : 
Int} (f : K.X p ⟶ X) {n : Int} (h : p + n = q) (p' : Int) (hp' : p' + 1 = p) (hf
 : K.d p' p ≫ f = 0) : toSingleMk (-f)…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `CategoryTheory.ProjectiveResolution.extEquivCohomologyClass_symm_neg`：ex
tEquivCohomologyClass_symm_neg (x : CohomologyClass R.cochainComplex ((singleFun
ctor C 0).obj Y) n) : R.extEquivCohomologyClass.symm (-x) …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma neg_extMk {n : ℕ} (f : R.complex.X n ⟶ Y) (m : ℕ) (hm : n + 1 = m)
    (hf : R.complex.d m n ≫ f = 0) :
    -R.extMk f m hm hf =
      R.extMk (-f) m hm (by simp [hf]) := by
  simp only [extMk, Preadditive.comp_neg]
  rw [Cocycle.toSingleMk_neg _ _ _ _
    (by simpa [cochainComplex_d _ _ _ m n rfl rfl])]
  simp

@[simp]
/-
**CategoryTheory.ProjectiveResolution.extMk_zero** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.ProjectiveResolution`。
形式化陈述：extMk_zero {n : Nat} (m : Nat) (hm : n + 1 = m) : R.extMk (0 : R.complex.X
 n ⟶ Y) m hm (by simp) = 0
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
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `CochainComplex.HomComplex.Cocycle.toSingleMk.congr_simp`：∀ {C : Type u} 
[inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C
]   [inst_2 : CategoryTheory.Limits.HasZeroOb…
· 使用引理 `CochainComplex.HomComplex.Cocycle.toSingleMk_zero`：toSingleMk_zero {p q 
: Int} {n : Int} (h : p + n = q) (p' : Int) (hp' : p' + 1 = p) : toSingleMk (0 :
 K.X p ⟶ X) h p' hp' (by simp) = 0
· 使用引理 `CategoryTheory.ProjectiveResolution.extEquivCohomologyClass_symm_zero`：e
xtEquivCohomologyClass_symm_zero : (R.extEquivCohomologyClass (Y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma extMk_zero {n : ℕ} (m : ℕ) (hm : n + 1 = m) :
    R.extMk (0 : R.complex.X n ⟶ Y) m hm (by simp) = 0 := by
  simp [extMk]
/-
**CategoryTheory.ProjectiveResolution.extMk_hom** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.ProjectiveResolution`。
形式化陈述：extMk_hom [HasDerivedCategory C] {n : Nat} (f : R.complex.X n ⟶ Y) (m : Na
t) (hm : n + 1 = m) (hf : R.complex.d m n ≫ f = 0) : (R.extMk f m hm hf).hom = (
ShiftedHom.mk₀ _ rfl ((DerivedCategory.singleFunctorIsoCompQ C 0).hom.app X ≫ in
v (DerivedCategory.Q.map R.π'))).comp ((ShiftedHom.map (Cocycle.equivHomShift.sy
mm (Cocycle.toSingleMk ((R.cochainComplexXIso (-n) n rfl).hom ≫ f) (by simp) (-m
) (by lia) (by simpa [cochainComplex_d _ _ _ _ _ rfl rfl]))) _).comp (.mk₀ _ rfl
 ((DerivedCategory.singleF
参数：f : R.complex.X n ⟶ Y；m : Nat；hm : n + 1 = m；hf : R.complex.d m n ≫ f = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用引理 `CategoryTheory.ProjectiveResolution.extEquivCohomologyClass_symm_mk_hom`
：extEquivCohomologyClass_symm_mk_hom [HasDerivedCategory C] (x : Cocycle R.cocha
inComplex ((singleFunctor C 0).obj Y) n) : (R.extEquivCohomol…
-/
lemma extMk_hom
    [HasDerivedCategory C] {n : ℕ} (f : R.complex.X n ⟶ Y) (m : ℕ) (hm : n + 1 = m)
    (hf : R.complex.d m n ≫ f = 0) :
    (R.extMk f m hm hf).hom =
    (ShiftedHom.mk₀ _ rfl ((DerivedCategory.singleFunctorIsoCompQ C 0).hom.app X ≫
      inv (DerivedCategory.Q.map R.π'))).comp
        ((ShiftedHom.map (Cocycle.equivHomShift.symm
          (Cocycle.toSingleMk ((R.cochainComplexXIso (-n) n rfl).hom ≫ f) (by simp) (-m)
            (by lia) (by simpa [cochainComplex_d _ _ _ _ _ rfl rfl]))) _).comp
              (.mk₀ _ rfl ((DerivedCategory.singleFunctorIsoCompQ C 0).inv.app Y))
                (zero_add _)) (add_zero _) :=
  extEquivCohomologyClass_symm_mk_hom _ _
/-
**CategoryTheory.ProjectiveResolution.extMk_eq_zero_iff** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.ProjectiveResolution`。
形式化陈述：extMk_eq_zero_iff (f : R.complex.X n ⟶ Y) (m : Nat) (hm : n + 1 = m) (hf :
 R.complex.d m n ≫ f = 0) (p : Nat) (hp : p + 1 = n) : R.extMk f m hm hf = 0 ↔ e
xists (g : R.complex.X p ⟶ Y), R.complex.d n p ≫ g = f
参数：f : R.complex.X n ⟶ Y；m : Nat；hm : n + 1 = m；hf : R.complex.d m n ≫ f = 0；p :
 Nat；hp : p + 1 = n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Abelian.hasZeroObject`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasZe
roObject C
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
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
· 使用引理 `CategoryTheory.ProjectiveResolution.extEquivCohomologyClass_extMk`：extEq
uivCohomologyClass_extMk {n : Nat} (f : R.complex.X n ⟶ Y) (m : Nat) (hm : n + 1
 = m) (hf : R.complex.d m n ≫ f = 0) : R.extEquivCohomo…
· 使用引理 `CategoryTheory.ProjectiveResolution.extEquivCohomologyClass_zero`：extEqu
ivCohomologyClass_zero : R.extEquivCohomologyClass (0 : Ext X Y n) = 0
· 使用引理 `CochainComplex.HomComplex.Cocycle.toSingleMk_mem_coboundaries_iff`：toSin
gleMk_mem_coboundaries_iff {p q : Int} (f : K.X p ⟶ X) {n : Int} (h : p + n = q)
 (p' : Int) (hp' : p' + 1 = p) (hf : K.d p' p ≫ f = 0) …
· 使用引理 `CategoryTheory.ProjectiveResolution.cochainComplex_d`：cochainComplex_d (
n₁ n₂ : Int) (k₁ k₂ : Nat) (h₁ : -k₁ = n₁
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.instEffectiveEpiOfIsIso`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],  
 CategoryTheory.EffectiveEpi…
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
-/
lemma extMk_eq_zero_iff (f : R.complex.X n ⟶ Y) (m : ℕ) (hm : n + 1 = m)
    (hf : R.complex.d m n ≫ f = 0)
    (p : ℕ) (hp : p + 1 = n) :
    R.extMk f m hm hf = 0 ↔
      ∃ (g : R.complex.X p ⟶ Y), R.complex.d n p ≫ g = f := by
  simp only [← R.extEquivCohomologyClass.apply_eq_iff_eq,
    extEquivCohomologyClass_extMk, extEquivCohomologyClass_zero,
    CohomologyClass.mk_eq_zero_iff]
  rw [Cocycle.toSingleMk_mem_coboundaries_iff _ _ _ _ _ (-p) (by lia),
    R.cochainComplex_d _ _ _ _ rfl rfl]
  refine ⟨fun ⟨g, hg⟩ ↦ ⟨(R.cochainComplexXIso (-p) p rfl).inv ≫ g, ?_⟩,
    fun ⟨g, hg⟩ ↦ ⟨(R.cochainComplexXIso (-p) p rfl).hom ≫ g, by simpa⟩⟩
  rw [← cancel_epi (R.cochainComplexXIso (-n) n rfl).hom]
  simpa [Category.assoc] using hg
/-
**CategoryTheory.ProjectiveResolution.extMk_surjective** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.ProjectiveResolution`。
形式化陈述：extMk_surjective (α : Ext X Y n) (m : Nat) (hm : n + 1 = m) : exists (f : 
R.complex.X n ⟶ Y) (hf : R.complex.d m n ≫ f = 0), R.extMk f m hm hf = α
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
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CochainComplex.HomComplex.Cocycle.toSingleMk_surjective`：toSingleMk_surj
ective {q n : Int} (α : Cocycle K ((singleFunctor C q).obj X) n) (p : Int) (h : 
p + n = q) (p' : Int) (hp' : p' + 1 = p) : ex…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.instEffectiveEpiOfIsIso`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],  
 CategoryTheory.EffectiveEpi…
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用引理 `CategoryTheory.ProjectiveResolution.cochainComplex_d`：cochainComplex_d (
n₁ n₂ : Int) (k₁ k₂ : Nat) (h₁ : -k₁ = n₁
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `CochainComplex.HomComplex.Cocycle.toSingleMk.congr_simp`：∀ {C : Type u} 
[inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C
]   [inst_2 : CategoryTheory.Limits.HasZeroOb…
-/
lemma extMk_surjective (α : Ext X Y n) (m : ℕ) (hm : n + 1 = m) :
    ∃ (f : R.complex.X n ⟶ Y) (hf : R.complex.d m n ≫ f = 0),
      R.extMk f m hm hf = α := by
  obtain ⟨x, rfl⟩ := R.extEquivCohomologyClass.symm.surjective α
  obtain ⟨x, rfl⟩ := x.mk_surjective
  obtain ⟨f, hf, rfl⟩ := Cocycle.toSingleMk_surjective x (-n) (by simp) (-m) (by lia)
  refine ⟨(R.cochainComplexXIso (-n) n rfl).inv ≫ f, ?_, by simp [extMk]⟩
  rw [← cancel_epi (R.cochainComplexXIso (-m) m rfl).hom]
  simpa [R.cochainComplex_d _ _ _ _ rfl rfl] using hf
/-
**CategoryTheory.ProjectiveResolution.extMk_comp_mk** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.ProjectiveResolution`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma extMk_comp_mk₀ {n : ℕ} (f : R.complex.X n ⟶ Y) (m : ℕ) (hm : n + 1 = m)
    (hf : R.complex.d m n ≫ f = 0) {Y' : C} (g : Y ⟶ Y') :
    (R.extMk f m hm hf).comp (Ext.mk₀ g) (add_zero _) =
      R.extMk (f ≫ g) m hm (by simp [reassoc_of% hf]) := by
  have := HasDerivedCategory.standard C
  ext
  simp only [extMk, Ext.comp_hom, Int.cast_ofNat_Int, Ext.mk₀_hom,
    extEquivCohomologyClass_symm_mk_hom]
  simp only [← Category.assoc]
  rw [Cocycle.toSingleMk_postcomp _ _ _ _
      (by simpa [cochainComplex_d _ _ _ m n rfl rfl]) g,
    Cocycle.equivHomShift_symm_postcomp,
    ← ShiftedHom.comp_mk₀ _ 0 rfl,
    ShiftedHom.map_comp, ShiftedHom.map_mk₀,
    ShiftedHom.comp_assoc _ _ _ (add_zero _) (zero_add _) (by simp),
    ShiftedHom.comp_assoc _ _ _ (zero_add _) (zero_add _) (by simp),
    ShiftedHom.comp_assoc _ _ _ (zero_add _) (zero_add _) (by simp),
    ShiftedHom.mk₀_comp_mk₀, ShiftedHom.mk₀_comp_mk₀, ← NatTrans.naturality]
  dsimp

variable {R} in
/-
**CategoryTheory.ProjectiveResolution.mk** 是 Mathlib 中的一个ctor，位于命名空间 `CategoryTh
eory.ProjectiveResolution`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Limits.HasZeroObject C] →       [inst_2 : CategoryTheory.Limits.
HasZeroMorphisms C] →         {Z : C} →           (complex : ChainComplex C ℕ) →
             autoParam (∀ (n : ℕ), CategoryTheory.Projective (complex.X n))     
            CategoryTheory.ProjectiveResolution.projective._autoParam →         
      [hasHomology : ∀ (i : ℕ), HomologicalComplex.HasHomology complex i] →     
            (π : complex ⟶ (ChainComplex.single₀ C).obj Z) →                   a
utoParam (QuasiIso π) CategoryTheory.ProjectiveResolution.quasiIso._autoParam → 
                    CategoryTheory.ProjectiveResolution Z
参数：complex : ChainComplex C ℕ；∀ (n : ℕ), CategoryTheory.Projective (complex.X n)
；i : ℕ；π : complex ⟶ (ChainComplex.single₀ C).obj Z；QuasiIso π。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mk₀_comp_extMk {n : ℕ} (f : R.complex.X n ⟶ Y) (m : ℕ) (hm : n + 1 = m)
    (hf : R.complex.d m n ≫ f = 0)
    {X' : C} {R' : ProjectiveResolution X'} {g : X' ⟶ X} (φ : Hom R' R g) :
    (Ext.mk₀ g).comp (R.extMk f m hm hf) (zero_add _) =
      R'.extMk (φ.hom.f n ≫ f) m hm (by simp [← φ.hom.comm_assoc, hf]) := by
  have := HasDerivedCategory.standard C
  ext
  have : (R'.cochainComplexXIso (-n) n (by lia)).hom ≫ φ.hom.f n =
      φ.hom'.f (-n) ≫ (R.cochainComplexXIso (-n) n (by lia)).hom := by
    simp [φ.hom'_f _ _ rfl]
  simp only [Ext.comp_hom, extMk_hom, Ext.mk₀_hom, reassoc_of% this]
  rw [Cocycle.toSingleMk_precomp _ _ _ (by lia)
    (by simpa [R.cochainComplex_d _ _ _ _ rfl rfl]),
    Cocycle.equivHomShift_symm_precomp,
    ← ShiftedHom.mk₀_comp 0 rfl, ShiftedHom.map_comp,
    ← ShiftedHom.comp_assoc _ _ _ (zero_add _) _ (by simp),
    ← ShiftedHom.comp_assoc _ _ _ (add_zero _) _ (by simp),
    ← ShiftedHom.comp_assoc _ _ _ (add_zero _) _ (by simp),
    ← ShiftedHom.comp_assoc _ _ _ (zero_add _) _ (by simp),
    ShiftedHom.map_mk₀, ShiftedHom.mk₀_comp_mk₀, ShiftedHom.mk₀_comp_mk₀]
  congr 3
  simp [← Functor.map_comp_assoc, ← Functor.map_comp]

end CategoryTheory.ProjectiveResolution

