/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Preimmersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.CategoryTheory.Adjunction.Opposites

/-!
# Subscheme associated to an ideal sheaf

We construct the subscheme associated to an ideal sheaf.

## Main definition
* `AlgebraicGeometry.Scheme.IdealSheafData.subscheme`: The subscheme associated to an ideal sheaf.
* `AlgebraicGeometry.Scheme.IdealSheafData.subschemeι`: The inclusion from the subscheme.
* `AlgebraicGeometry.Scheme.Hom.image`: The scheme-theoretic image of a morphism.
* `AlgebraicGeometry.Scheme.kerAdjunction`:
  The adjunction between taking kernels and taking the associated subscheme.

## Note

Some instances are in `Mathlib/AlgebraicGeometry/Morphisms/ClosedImmersion` and
`Mathlib/AlgebraicGeometry/Morphisms/Separated` because they need more API to prove.

-/

@[expose] public section

open CategoryTheory TopologicalSpace PrimeSpectrum Limits

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}}

variable (I : IdealSheafData X)

/-- `Spec (𝒪ₓ(U)/I(U))`, the object to be glued into the closed subscheme. -/
noncomputable
/-
**AlgebraicGeometry.Scheme.IdealSheafData.glueDataObj** 是 Mathlib 中的一个定义，位于命名空间 
`AlgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：glueDataObj (U : X.affineOpens) : Scheme
参数：U : X.affineOpens。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def glueDataObj (U : X.affineOpens) : Scheme :=
  Spec <| .of <| Γ(X, U) ⧸ I.ideal U

/-- `Spec (𝒪ₓ(U)/I(U)) ⟶ Spec (𝒪ₓ(U)) = U`, the closed immersion into `U`. -/
noncomputable
/-
**AlgebraicGeometry.Scheme.IdealSheafData.glueDataObj** 是 Mathlib 中的一个定义，位于命名空间 
`AlgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：glueDataObj (U : X.affineOpens) : Scheme
参数：U : X.affineOpens。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def glueDataObjι (U : X.affineOpens) : I.glueDataObj U ⟶ U.1 :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk _)) ≫ U.2.isoSpec.inv

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.Scheme.IdealSheafData.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicG
eometry.Scheme.IdealSheafData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (U : X.affineOpens) : IsPreimmersion (I.glueDataObjι U) :=
  have : IsPreimmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.ideal U)))) :=
    .mk_SpecMap
      (isClosedEmbedding_comap_of_surjective _ _ Ideal.Quotient.mk_surjective).isEmbedding
      (RingHom.surjectiveOnStalks_of_surjective Ideal.Quotient.mk_surjective)
  .comp _ _

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.Scheme.IdealSheafData.glueDataObj** 是 Mathlib 中的一个定义，位于命名空间 
`AlgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：glueDataObj (U : X.affineOpens) : Scheme
参数：U : X.affineOpens。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma glueDataObjι_ι (U : X.affineOpens) : I.glueDataObjι U ≫ U.1.ι =
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk _)) ≫ U.2.fromSpec := by
  rw [glueDataObjι, Category.assoc]; rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.Scheme.IdealSheafData.ker_glueDataObj** 是 Mathlib 中的一个引理，位于命
名空间 `AlgebraicGeometry.Scheme.IdealSheafData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ker_glueDataObjι_appTop (U : X.affineOpens) :
    RingHom.ker (I.glueDataObjι U).appTop.hom = (I.ideal U).comap U.1.topIso.hom.hom := by
  let φ : Γ(X, U) ⟶ CommRingCat.of (Γ(X, U) ⧸ I.ideal U) :=
    CommRingCat.ofHom (Ideal.Quotient.mk (I.ideal U))
  rw [← Ideal.mk_ker (I := I.ideal _)]
  change RingHom.ker (Spec.map φ ≫ _).appTop.hom = (RingHom.ker φ.hom).comap _
  rw [← RingHom.ker_equiv_comp _ (Scheme.ΓSpecIso _).commRingCatIsoToRingEquiv, RingHom.comap_ker,
    RingEquiv.toRingHom_eq_coe, Iso.commRingCatIsoToRingEquiv_toRingHom, ← CommRingCat.hom_comp,
    ← CommRingCat.hom_comp]
  congr 2
  simp only [Scheme.Hom.comp_app, TopologicalSpace.Opens.map_top, Category.assoc,
    Scheme.ΓSpecIso_naturality, Scheme.Opens.topIso_hom]
  rw [← Scheme.Hom.appTop, U.2.isoSpec_inv_appTop, Category.assoc, Iso.inv_hom_id_assoc]
  simp only [Scheme.Opens.topIso_hom]

set_option backward.isDefEq.respectTransparency.types false in
open scoped Set.Notation in
/-
**AlgebraicGeometry.Scheme.IdealSheafData.range_glueDataObj** 是 Mathlib 中的一个引理，位
于命名空间 `AlgebraicGeometry.Scheme.IdealSheafData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma range_glueDataObjι (U : X.affineOpens) :
    Set.range (I.glueDataObjι U) =
      U.2.isoSpec.inv '' PrimeSpectrum.zeroLocus (I.ideal U) := by
  simp only [glueDataObjι, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
  erw [range_comap_of_surjective]
  swap; · exact Ideal.Quotient.mk_surjective
  simp
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.Scheme.IdealSheafData.range_glueDataObj** 是 Mathlib 中的一个引理，位
于命名空间 `AlgebraicGeometry.Scheme.IdealSheafData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma range_glueDataObjι_ι (U : X.affineOpens) :
    Set.range (I.glueDataObjι U ≫ U.1.ι) = X.zeroLocus (U := U) (I.ideal U) ∩ U := by
  simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, range_glueDataObjι]
  rw [← Set.image_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base, IsAffineOpen.isoSpec_inv_ι,
    IsAffineOpen.fromSpec_image_zeroLocus]

/-- The underlying space of `Spec (𝒪ₓ(U)/I(U))` is homeomorphic to its image in `X`. -/
noncomputable
/-
**AlgebraicGeometry.Scheme.IdealSheafData.glueDataObjCarrierIso** 是 Mathlib 中的一个
定义，位于命名空间 `AlgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：glueDataObjCarrierIso (U : X.affineOpens) : (I.glueDataObj U).carrier ≅ To
pCat.of ↑(X.zeroLocus (U
参数：U : X.affineOpens。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.Scheme.IdealSheafData.range_glueDataObjι_ι`：range_glue
DataObjι_ι (U : X.affineOpens) : Set.range (I.glueDataObjι U ≫ U.1.ι) = X.zeroLo
cus (U
-/
def glueDataObjCarrierIso (U : X.affineOpens) :
    (I.glueDataObj U).carrier ≅ TopCat.of ↑(X.zeroLocus (U := U) (I.ideal U) ∩ U) :=
  TopCat.isoOfHomeo ((I.glueDataObjι U ≫ U.1.ι).isEmbedding.toHomeomorph.trans
    (.setCongr (I.range_glueDataObjι_ι U)))

/-- The open immersion `Spec Γ(𝒪ₓ/I, U) ⟶ Spec Γ(𝒪ₓ/I, V)` if `U ≤ V`. -/
noncomputable
/-
**AlgebraicGeometry.Scheme.IdealSheafData.glueDataObjMap** 是 Mathlib 中的一个定义，位于命名
空间 `AlgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：glueDataObjMap {U V : X.affineOpens} (h : U <= V) : I.glueDataObj U ⟶ I.gl
ueDataObj V
参数：h : U <= V。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.Scheme.IdealSheafData.ideal_le_comap_ideal`：ideal_le_c
omap_ideal {U V : X.affineOpens} (h : U <= V) : I.ideal V <= (I.ideal U).comap (
X.presheaf.map (homOfLE h).op).hom
-/
def glueDataObjMap {U V : X.affineOpens} (h : U ≤ V) : I.glueDataObj U ⟶ I.glueDataObj V :=
  Spec.map (CommRingCat.ofHom (Ideal.quotientMap _ _ (I.ideal_le_comap_ideal h)))
/-
**AlgebraicGeometry.Scheme.IdealSheafData.isLocalization_away** 是 Mathlib 中的一个引理
，位于命名空间 `AlgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：isLocalization_away {U V : X.affineOpens} (h : U <= V) (f : Γ(X, V.1)) (hU
 : U = X.affineBasicOpen f) : letI
参数：h : U <= V；f : Γ(X, V.1)；hU : U = X.affineBasicOpen f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用引理 `AlgebraicGeometry.Scheme.IdealSheafData.ideal_le_comap_ideal`：ideal_le_c
omap_ideal {U V : X.affineOpens} (h : U <= V) : I.ideal V <= (I.ideal U).comap (
X.presheaf.map (homOfLE h).op).hom
· 使用定理 `AlgebraicGeometry.IsAffineOpen.isLocalization_of_eq_basicOpen`：isLocaliz
ation_of_eq_basicOpen {V : X.Opens} (i : V ⟶ U) (e : V = X.basicOpen f) : @IsLoc
alization.Away _ _ f Γ(X, V) _ (X.presheaf.map i.op…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `IsLocalization.of_surjective`：of_surjective {R' S' : Type*} [CommRing R'
] [CommRing S'] [Algebra R' S'] (f : R ->+* R') (hf : Function.Surjective f) (g 
: S ->+* S') (hg :…
· 使用定理 `Ideal.Quotient.mk_surjective`：mk_surjective : Function.Surjective (mk I)
· 使用定理 `Ideal.quotientMap_comp_mk`：quotientMap_comp_mk {J : Ideal R} {I : Ideal 
S} [I.IsTwoSided] [J.IsTwoSided] {f : R ->+* S} (H : J <= I.comap f) : (quotient
Map I f H).comp…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Ideal.mk_ker`：mk_ker {I : Ideal R} [I.IsTwoSided] : ker (Quotient.mk I) 
= I
· 使用引理 `AlgebraicGeometry.Scheme.IdealSheafData.map_ideal'`：map_ideal' {U V : X.
affineOpens} (h : Opposite.op V.1 ⟶ .op U.1) : (I.ideal V).map (X.presheaf.map h
).hom = I.ideal U
-/
lemma isLocalization_away {U V : X.affineOpens}
    (h : U ≤ V) (f : Γ(X, V.1)) (hU : U = X.affineBasicOpen f) :
      letI := (Ideal.quotientMap _ _ (I.ideal_le_comap_ideal h)).toAlgebra
      IsLocalization.Away (Ideal.Quotient.mk (I.ideal V) f) (Γ(X, U) ⧸ (I.ideal U)) := by
  let := (Ideal.quotientMap _ _ (I.ideal_le_comap_ideal h)).toAlgebra
  let := (X.presheaf.map (homOfLE (X := X.Opens) h).op).hom.toAlgebra
  have : IsLocalization.Away f Γ(X, U) := by
    subst hU; exact V.2.isLocalization_of_eq_basicOpen _ _ rfl
  simp only [IsLocalization.Away, ← Submonoid.map_powers]
  refine IsLocalization.of_surjective _ _ _ Ideal.Quotient.mk_surjective _
    Ideal.Quotient.mk_surjective ?_ ?_
  · simp [RingHom.algebraMap_toAlgebra, Ideal.quotientMap_comp_mk]; rfl
  · simp only [Ideal.mk_ker, RingHom.algebraMap_toAlgebra, I.map_ideal', le_refl]
/-
**AlgebraicGeometry.Scheme.IdealSheafData.isOpenImmersion_glueDataObjMap** 是 Mat
hlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：isOpenImmersion_glueDataObjMap {V : X.affineOpens} (f : Γ(X, V.1)) : IsOpe
nImmersion (I.glueDataObjMap (X.affineBasicOpen_le f))
参数：f : Γ(X, V.1)。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `AlgebraicGeometry.Scheme.affineBasicOpen_le`：∀ (X : AlgebraicGeometry.Sc
heme) {V : ↑X.affineOpens} (f : ↑(X.presheaf.obj (Opposite.op ↑V))), X.affineBas
icOpen f ≤ V
· 使用引理 `AlgebraicGeometry.Scheme.IdealSheafData.ideal_le_comap_ideal`：ideal_le_c
omap_ideal {U V : X.affineOpens} (h : U <= V) : I.ideal V <= (I.ideal U).comap (
X.presheaf.map (homOfLE h).op).hom
· 使用引理 `AlgebraicGeometry.Scheme.IdealSheafData.isLocalization_away`：isLocalizat
ion_away {U V : X.affineOpens} (h : U <= V) (f : Γ(X, V.1)) (hU : U = X.affineBa
sicOpen f) : letI
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.of_isLocalization`：∀ {R S : Type u_1} 
[inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] (f : R) [IsLoca
lization.Away f S],   AlgebraicGeometry.I…
-/
instance isOpenImmersion_glueDataObjMap {V : X.affineOpens} (f : Γ(X, V.1)) :
    IsOpenImmersion (I.glueDataObjMap (X.affineBasicOpen_le f)) := by
  let := (Ideal.quotientMap _ _ (I.ideal_le_comap_ideal (X.affineBasicOpen_le f))).toAlgebra
  have := I.isLocalization_away (X.affineBasicOpen_le f) f rfl
  exact IsOpenImmersion.of_isLocalization (Ideal.Quotient.mk _ f)
/-
**AlgebraicGeometry.Scheme.IdealSheafData.opensRange_glueDataObjMap** 是 Mathlib 
中的一个引理，位于命名空间 `AlgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：opensRange_glueDataObjMap {V : X.affineOpens} (f : Γ(X, V.1)) : (I.glueDat
aObjMap (X.affineBasicOpen_le f)).opensRange = (I.glueDataObjι V) ⁻¹ᵁ (V.1.ι ⁻¹ᵁ
 X.basicOpen f)
参数：f : Γ(X, V.1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `AlgebraicGeometry.Scheme.affineBasicOpen_le`：∀ (X : AlgebraicGeometry.Sc
heme) {V : ↑X.affineOpens} (f : ↑(X.presheaf.obj (Opposite.op ↑V))), X.affineBas
icOpen f ≤ V
· 使用引理 `AlgebraicGeometry.Scheme.IdealSheafData.ideal_le_comap_ideal`：ideal_le_c
omap_ideal {U V : X.affineOpens} (h : U <= V) : I.ideal V <= (I.ideal U).comap (
X.presheaf.map (homOfLE h).op).hom
· 使用引理 `AlgebraicGeometry.Scheme.IdealSheafData.isLocalization_away`：isLocalizat
ion_away {U V : X.affineOpens} (h : U <= V) (f : Γ(X, V.1)) (hU : U = X.affineBa
sicOpen f) : letI
· 使用定理 `TopologicalSpace.Opens.ext`：ext {U V : Opens α} (h : (U : Set α) = V) : 
U = V
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `PrimeSpectrum.localization_away_comap_range`：localization_away_comap_ran
ge (S : Type v) [CommSemiring S] [Algebra R S] (r : R) [IsLocalization.Away r S]
 : Set.range (comap (algebraMap R…
· 使用引理 `PrimeSpectrum.continuous_comap`：continuous_comap (f : R ->+* S) : Contin
uous (comap f)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `PrimeSpectrum.comap_basicOpen`：comap_basicOpen (f : R ->+* S) (x : R) : 
TopologicalSpace.Opens.comap ⟨comap f, continuous_comap f⟩ (basicOpen x) = basic
Open (f x)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `AlgebraicGeometry.IsAffineOpen.fromSpec_preimage_basicOpen`：fromSpec_pre
image_basicOpen : hU.fromSpec ⁻¹ᵁ X.basicOpen f = PrimeSpectrum.basicOpen f
· 使用引理 `AlgebraicGeometry.Scheme.Hom.comp_preimage`：comp_preimage {X Y Z : Schem
e.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (U) : (f ≫ g) ⁻¹ᵁ U = f ⁻¹ᵁ g ⁻¹ᵁ U
· 使用引理 `AlgebraicGeometry.Scheme.IdealSheafData.glueDataObjι_ι`：glueDataObjι_ι (
U : X.affineOpens) : I.glueDataObjι U ≫ U.1.ι = Spec.map (CommRingCat.ofHom (Ide
al.Quotient.mk _)) ≫ U.2.fromSpec
-/
lemma opensRange_glueDataObjMap {V : X.affineOpens} (f : Γ(X, V.1)) :
      (I.glueDataObjMap (X.affineBasicOpen_le f)).opensRange =
        (I.glueDataObjι V) ⁻¹ᵁ (V.1.ι ⁻¹ᵁ X.basicOpen f) := by
  let := (Ideal.quotientMap _ _ (I.ideal_le_comap_ideal (X.affineBasicOpen_le f))).toAlgebra
  let f' : Γ(X, V) ⧸ I.ideal V := Ideal.Quotient.mk _ f
  have := I.isLocalization_away (X.affineBasicOpen_le f) f rfl
  ext1
  refine (localization_away_comap_range _ f').trans ?_
  rw [← comap_basicOpen, ← V.2.fromSpec_preimage_basicOpen,
    ← Scheme.Hom.comp_preimage, glueDataObjι_ι]
  rfl

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.Scheme.IdealSheafData.glueDataObjMap_glueDataObj** 是 Mathlib
 中的一个引理，位于命名空间 `AlgebraicGeometry.Scheme.IdealSheafData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma glueDataObjMap_glueDataObjι {U V : X.affineOpens} (h : U ≤ V) :
    I.glueDataObjMap h ≫ I.glueDataObjι V = I.glueDataObjι U ≫ X.homOfLE h := by
  rw [glueDataObjMap, glueDataObjι, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp,
    Ideal.quotientMap_comp_mk, CommRingCat.ofHom_comp, Spec.map_comp_assoc, glueDataObjι,
    Category.assoc]
  congr 1
  rw [Iso.eq_inv_comp, IsAffineOpen.isoSpec_hom, CommRingCat.ofHom_hom]
  erw [Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_assoc U.1 V.1 h]
  rw [← IsAffineOpen.isoSpec_hom V.2, Iso.hom_inv_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.Scheme.IdealSheafData.ideal_le_ker_glueDataObj** 是 Mathlib 中
的一个引理，位于命名空间 `AlgebraicGeometry.Scheme.IdealSheafData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ideal_le_ker_glueDataObjι (U V : X.affineOpens) :
    I.ideal V ≤ RingHom.ker (U.1.ι.app V.1 ≫ (I.glueDataObjι U).app _).hom := by
  intro x hx
  apply (I.glueDataObj U).IsSheaf.section_ext
  intro p hp
  obtain ⟨f, g, hfg, hf⟩ := exists_basicOpen_le_affine_inter U.2 V.2 (I.glueDataObjι U p).1
      ⟨(I.glueDataObjι U p).2, hp⟩
  refine ⟨(I.glueDataObjι U ⁻¹ᵁ U.1.ι ⁻¹ᵁ X.basicOpen f),
    fun x hx ↦ X.basicOpen_le g (hfg ▸ hx), hf, ?_⟩
  have := Hom.isIso_app (I.glueDataObjMap (X.affineBasicOpen_le f))
    (I.glueDataObjι U ⁻¹ᵁ U.1.ι ⁻¹ᵁ X.basicOpen f) (by rw [opensRange_glueDataObjMap])
  apply ((ConcreteCategory.isIso_iff_bijective _).mp this).1
  simp only [map_zero, ← RingHom.comp_apply,
    ← CommRingCat.hom_comp, Category.assoc]
  simp only [Scheme.Hom.app_eq_appLE, homOfLE_leOfHom, Scheme.Hom.map_appLE,
    Scheme.Hom.appLE_comp_appLE, Category.assoc, glueDataObjMap_glueDataObjι_assoc]
  rw [Scheme.Hom.appLE]
  have H : (X.homOfLE (X.basicOpen_le f) ≫ U.1.ι) ⁻¹ᵁ V.1 = ⊤ := by
    simp only [Scheme.homOfLE_ι, ← top_le_iff]
    exact fun x _ ↦ (hfg.trans_le (X.basicOpen_le g)) x.2
  simp only [Scheme.Hom.comp_app, Scheme.Opens.ι_app, Scheme.homOfLE_app, ← Functor.map_comp_assoc,
    Scheme.Hom.app_eq _ H, Scheme.Opens.toScheme_presheaf_map, ← Functor.map_comp, Category.assoc]
  simp only [CommRingCat.hom_comp, RingHom.comp_apply]
  convert RingHom.map_zero _
  rw [← RingHom.mem_ker, ker_glueDataObjι_appTop, ← Ideal.mem_comap, Ideal.comap_comap,
    ← CommRingCat.hom_comp]
  simp only [homOfLE_leOfHom, Scheme.Hom.comp_base,
    TopologicalSpace.Opens.map_comp_obj, eqToHom_op, eqToHom_unop, ← Functor.map_comp,
    Scheme.Opens.topIso_hom, Category.assoc]
  exact I.ideal_le_comap_ideal (U := X.affineBasicOpen f) (V := V)
    (hfg.trans_le (X.basicOpen_le g)) hx

/-- (Implementation) The intersections `Spec Γ(𝒪ₓ/I, U) ∩ V` useful for gluing. -/
noncomputable
/-
**AlgebraicGeometry.Scheme.IdealSheafData.glueDataObjPullback** 是 Mathlib 中的一个缩写
定义，位于命名空间 `AlgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：glueDataObjPullback (U V : X.affineOpens) : Scheme
参数：U V : X.affineOpens。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
abbrev glueDataObjPullback (U V : X.affineOpens) : Scheme :=
  pullback (I.glueDataObjι U) (X.homOfLE (U := U.1 ⊓ V.1) inf_le_left)

set_option backward.isDefEq.respectTransparency false in
/-- (Implementation) Transition maps in the glue data for `𝒪ₓ/I`. -/
/-
**AlgebraicGeometry.Scheme.IdealSheafData.glueDataT** 是 Mathlib 中的一个定义，位于命名空间 `A
lgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：glueDataT (U V : X.affineOpens) : I.glueDataObjPullback U V ⟶ I.glueDataOb
jPullback V U
参数：U V : X.affineOpens。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(Implementation) Transition maps in the glue data for `𝒪ₓ/I`.
-/
noncomputable def glueDataT (U V : X.affineOpens) :
    I.glueDataObjPullback U V ⟶ I.glueDataObjPullback V U := by
  letI F := pullback.snd (I.glueDataObjι U) (X.homOfLE (inf_le_left (b := V.1)))
  refine pullback.lift ((F ≫ X.homOfLE inf_le_right ≫
    V.2.isoSpec.hom).liftQuotient _ ?_) (F ≫ X.homOfLE (by simp)) ?_
  · intro x hx
    simp only [Hom.comp_app, Hom.comp_base, TopologicalSpace.Opens.map_comp_obj,
      TopologicalSpace.Opens.map_top, homOfLE_app, homOfLE_leOfHom, Category.assoc, RingHom.mem_ker]
    convert_to (U.1.ι.app V.1 ≫ (F ≫ X.homOfLE inf_le_left).appLE (U.1.ι ⁻¹ᵁ V.1) ⊤
      (by rw [← Scheme.Hom.comp_preimage, Category.assoc, X.homOfLE_ι]
          exact fun x _ ↦ by simpa using (F x).2.2)).hom x = 0 using 3
    · simp only [homOfLE_leOfHom, Opens.ι_app, Hom.comp_appLE, homOfLE_app]
      have H : ⊤ ≤ X.homOfLE (inf_le_left (b := V.1)) ⁻¹ᵁ U.1.ι ⁻¹ᵁ V.1 := by
        rw [← Scheme.Hom.comp_preimage, X.homOfLE_ι]; exact fun x _ ↦ by simpa using x.2.2
      rw [← F.map_appLE (show ⊤ ≤ F ⁻¹ᵁ ⊤ from le_rfl) (homOfLE H).op]
      simp only [homOfLE_leOfHom, Opens.toScheme_presheaf_map, Quiver.Hom.unop_op,
        Hom.opensFunctor_map_homOfLE, ← Functor.map_comp_assoc, IsAffineOpen.isoSpec_hom_appTop,
        Opens.topIso_inv, eqToHom_op, homOfLE_leOfHom, Category.assoc,
        Iso.inv_hom_id_assoc, F.app_eq_appLE]
      rfl
    · have : (U.1.ι.app V.1 ≫ (I.glueDataObjι U).app (U.1.ι ⁻¹ᵁ V.1)).hom x = 0 :=
        I.ideal_le_ker_glueDataObjι U V hx
      simp_rw [F, ← pullback.condition]
      simp only [Scheme.Opens.ι_app, CommRingCat.hom_comp, RingHom.coe_comp,
        Function.comp_apply, Scheme.Hom.appLE, Scheme.Hom.comp_app, Category.assoc] at this ⊢
      simp only [this, map_zero]
  · conv_lhs => enter [2]; rw [glueDataObjι]
    rw [Scheme.Hom.liftQuotient_comp_assoc, Category.assoc, Category.assoc, Iso.hom_inv_id,
      Category.comp_id, Category.assoc, X.homOfLE_homOfLE]

@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.Scheme.IdealSheafData.glueDataT_snd** 是 Mathlib 中的一个引理，位于命名空
间 `AlgebraicGeometry.Scheme.IdealSheafData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma glueDataT_snd (U V : X.affineOpens) :
    I.glueDataT U V ≫ pullback.snd _ _ = pullback.snd _ _ ≫ X.homOfLE (by simp) :=
  pullback.lift_snd _ _ _

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.Scheme.IdealSheafData.glueDataT_fst** 是 Mathlib 中的一个引理，位于命名空
间 `AlgebraicGeometry.Scheme.IdealSheafData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma glueDataT_fst (U V : X.affineOpens) :
    I.glueDataT U V ≫ pullback.fst _ _ ≫ glueDataObjι _ _ =
      pullback.snd _ _ ≫ X.homOfLE inf_le_right := by
  refine (pullback.lift_fst_assoc _ _ _ _).trans ?_
  conv_lhs => enter [2]; rw [glueDataObjι]
  rw [Scheme.Hom.liftQuotient_comp_assoc, Category.assoc, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

/-- (Implementation) `t'` in the glue data for `𝒪ₓ/I`. -/
noncomputable
/-
**AlgebraicGeometry.Scheme.IdealSheafData.glueDataT'Aux** 是 Mathlib 中的一个定义，位于命名空
间 `AlgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：{X : AlgebraicGeometry.Scheme} →   (I : X.IdealSheafData) →     (U V W U₀ 
: ↑X.affineOpens) →       ↑U ⊓ ↑W ≤ ↑U₀ →         (CategoryTheory.Limits.pullbac
k (CategoryTheory.Limits.pullback.fst (I.glueDataObjι U) (X.homOfLE ⋯))         
    (CategoryTheory.Limits.pullback.fst (I.glueDataObjι U) (X.homOfLE ⋯)) ⟶     
      I.glueDataObjPullback V U₀)
参数：I : X.IdealSheafData；U V W U₀ : ↑X.affineOpens；CategoryTheory.Limits.pullback
 (CategoryTheory.Limits.pullback.fst (I.glueDataObjι U) (X.homOfLE ⋯))          
   (CategoryTheory.Limits.pullback.fst (I.glueDataObjι U) (X.homOfLE ⋯)) ⟶      
     I.glueDataObjPullback V U₀。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def glueDataT'Aux (U V W U₀ : X.affineOpens) (hU₀ : U.1 ⊓ W ≤ U₀) :
    pullback
      (pullback.fst _ _ : I.glueDataObjPullback U V ⟶ _)
      (pullback.fst _ _ : I.glueDataObjPullback U W ⟶ _) ⟶ I.glueDataObjPullback V U₀ :=
  pullback.lift
    (pullback.fst _ _ ≫ I.glueDataT U V ≫ pullback.fst _ _)
    (IsOpenImmersion.lift (V.1 ⊓ U₀.1).ι
      (pullback.fst _ _ ≫ pullback.fst _ _ ≫ I.glueDataObjι U ≫ U.1.ι) (by
      simp only [Scheme.Opens.range_ι, TopologicalSpace.Opens.coe_inf, Set.subset_inter_iff]
      constructor
      · rw [pullback.condition_assoc (f := I.glueDataObjι U), X.homOfLE_ι,
          ← Category.assoc, Scheme.Hom.comp_base, TopCat.coe_comp]
        exact (Set.range_comp_subset_range _ _).trans (by simp)
      · rw [pullback.condition_assoc, pullback.condition_assoc, X.homOfLE_ι,
          ← Category.assoc, Scheme.Hom.comp_base, TopCat.coe_comp]
        exact (Set.range_comp_subset_range _ _).trans (by simpa using! hU₀))) (by
      rw [← cancel_mono (Scheme.Opens.ι _)]
      simp [pullback.condition_assoc])

@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.Scheme.IdealSheafData.glueDataT'Aux_fst** 是 Mathlib 中的一个引理，位
于命名空间 `AlgebraicGeometry.Scheme.IdealSheafData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma glueDataT'Aux_fst (U V W U₀ : X.affineOpens) (hU₀ : U.1 ⊓ W ≤ U₀) :
    I.glueDataT'Aux U V W U₀ hU₀ ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ I.glueDataT U V ≫ pullback.fst _ _ := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.Scheme.IdealSheafData.glueDataT'Aux_snd_** 是 Mathlib 中的一个引理，
位于命名空间 `AlgebraicGeometry.Scheme.IdealSheafData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma glueDataT'Aux_snd_ι (U V W U₀ : X.affineOpens) (hU₀ : U.1 ⊓ W ≤ U₀) :
    I.glueDataT'Aux U V W U₀ hU₀ ≫ pullback.snd _ _ ≫ (V.1 ⊓ U₀.1).ι =
      pullback.fst _ _ ≫ pullback.fst _ _ ≫ I.glueDataObjι U ≫ U.1.ι :=
  (pullback.lift_snd_assoc _ _ _ _).trans (IsOpenImmersion.lift_fac _ _ _)

set_option backward.isDefEq.respectTransparency false in
/-- (Implementation) The glue data for `𝒪ₓ/I`. -/
@[simps]
noncomputable
/-
**AlgebraicGeometry.Scheme.IdealSheafData.glueData** 是 Mathlib 中的一个定义，位于命名空间 `Al
gebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：glueData : Scheme.GlueData where J
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def glueData : Scheme.GlueData where
  J := X.affineOpens
  U := I.glueDataObj
  V ij := I.glueDataObjPullback ij.1 ij.2
  f i j := pullback.fst _ _
  f_id i :=
    have : IsIso (X.homOfLE (inf_le_left (a := i.1) (b := i.1))) :=
      ⟨X.homOfLE (by simp), by simp, by simp⟩
    inferInstance
  t i j := I.glueDataT i j
  t_id i := by
    apply pullback.hom_ext
    · rw [← cancel_mono (glueDataObjι _ _)]
      simp [pullback.condition]
    · simp
  t' i j k := pullback.lift
    (I.glueDataT'Aux _ _ _ _ inf_le_right) (I.glueDataT'Aux _ _ _ _ inf_le_left) (by simp)
  t_fac i j k := by
    apply pullback.hom_ext
    · rw [← cancel_mono (glueDataObjι _ _)]
      simp
    · rw [← cancel_mono (Scheme.Opens.ι _)]
      simp [pullback.condition_assoc]
  cocycle i j k := by
    dsimp only
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · rw [← cancel_mono (glueDataObjι _ _), ← cancel_mono (Scheme.Opens.ι _)]
        simp only [Category.assoc, limit.lift_π, PullbackCone.mk_π_app,
          glueDataT'Aux_fst, limit.lift_π_assoc, cospan_left, glueDataT_fst, Scheme.homOfLE_ι,
          glueDataT'Aux_snd_ι, glueDataT'Aux_fst_assoc, glueDataT_fst_assoc, Category.id_comp]
        rw [pullback.condition_assoc (f := I.glueDataObjι i)]
        simp
      · rw [← cancel_mono (Scheme.Opens.ι _)]
        simp [pullback.condition_assoc]
    · apply pullback.hom_ext
      · rw [← cancel_mono (glueDataObjι _ _), ← cancel_mono (Scheme.Opens.ι _)]
        simp only [Category.assoc, limit.lift_π, PullbackCone.mk_π_app,
          glueDataT'Aux_fst, limit.lift_π_assoc, cospan_left, glueDataT_fst, Scheme.homOfLE_ι,
          glueDataT'Aux_snd_ι, glueDataT'Aux_fst_assoc, glueDataT_fst_assoc, Category.id_comp]
        rw [← pullback.condition_assoc, pullback.condition_assoc (f := I.glueDataObjι i),
          X.homOfLE_ι]
      · rw [← cancel_mono (Scheme.Opens.ι _)]
        simp only [Category.assoc, limit.lift_π, PullbackCone.mk_π_app,
          glueDataT'Aux_snd_ι, limit.lift_π_assoc, cospan_left, glueDataT'Aux_fst_assoc,
          glueDataT_fst_assoc, Scheme.homOfLE_ι, Category.id_comp]
        rw [pullback.condition_assoc, pullback.condition_assoc, X.homOfLE_ι]
  f_open i j := inferInstance

set_option backward.defeqAttrib.useBackward true in
/-- (Implementation) The map from `Spec(𝒪ₓ/I)` to `X`. See `IdealSheafData.subschemeι` instead. -/
noncomputable
/-
**AlgebraicGeometry.Scheme.IdealSheafData.gluedTo** 是 Mathlib 中的一个定义，位于命名空间 `Alg
ebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：gluedTo : I.glueData.glued ⟶ X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def gluedTo : I.glueData.glued ⟶ X :=
  Multicoequalizer.desc _ _ (fun i ↦ I.glueDataObjι i ≫ i.1.ι)
    (by simp [GlueData.diagram, pullback.condition_assoc])

@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.Scheme.IdealSheafData.** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicG
eometry.Scheme.IdealSheafData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma ι_gluedTo (U : X.affineOpens) :
    I.glueData.ι U ≫ I.gluedTo = I.glueDataObjι U ≫ U.1.ι :=
  Multicoequalizer.π_desc _ _ _ _ _

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.Scheme.IdealSheafData.glueDataObjMap_** 是 Mathlib 中的一个引理，位于命
名空间 `AlgebraicGeometry.Scheme.IdealSheafData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma glueDataObjMap_ι (U V : X.affineOpens) (h : U ≤ V) :
    I.glueDataObjMap h ≫ I.glueData.ι V = I.glueData.ι U := by
  have : IsIso (X.homOfLE inf_le_left : (U.1 ⊓ V.1).toScheme ⟶ U) :=
    ⟨X.homOfLE (by simpa), by simp, by simp⟩
  have H : inv (X.homOfLE inf_le_left : (U.1 ⊓ V.1).toScheme ⟶ U) = X.homOfLE (by simpa) := by
    rw [eq_comm, ← hom_comp_eq_id]; simp
  have := I.glueData.glue_condition U V
  simp only [glueData_J, glueData_V, glueData_t, glueData_U, glueData_f] at this
  rw [← IsIso.inv_comp_eq] at this
  rw [← Category.id_comp (I.glueData.ι U), ← this]
  simp_rw [← Category.assoc]
  congr 1
  rw [← cancel_mono (glueDataObjι _ _)]
  simp [pullback_inv_fst_snd_of_right_isIso_assoc, H]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.Scheme.IdealSheafData.gluedTo_injective** 是 Mathlib 中的一个引理，位
于命名空间 `AlgebraicGeometry.Scheme.IdealSheafData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma gluedTo_injective :
    Function.Injective I.gluedTo := by
  intro a b e
  obtain ⟨ia, a : I.glueDataObj ia, rfl⟩ :=
    I.glueData.toGlueData.ι_jointly_surjective forget a
  obtain ⟨ib, b : I.glueDataObj ib, rfl⟩ :=
    I.glueData.toGlueData.ι_jointly_surjective forget b
  change I.glueData.ι ia a = I.glueData.ι ib b
  have : (I.glueDataObjι ia a).1 = (I.glueDataObjι ib b).1 := by
    have : (I.glueData.ι ia ≫ I.gluedTo) a = (I.glueData.ι ib ≫ I.gluedTo) b := e
    rwa [ι_gluedTo, ι_gluedTo] at this
  obtain ⟨f, g, hfg, H⟩ := exists_basicOpen_le_affine_inter ia.2 ib.2
    (I.glueDataObjι ia a).1
      ⟨(I.glueDataObjι ia a).2, this ▸ (I.glueDataObjι ib b).2⟩
  have hmem (W) (hW : W = X.affineBasicOpen g) :
      b ∈ Set.range (I.glueDataObjMap (hW.trans_le (X.affineBasicOpen_le g))) := by
    subst hW
    refine (I.opensRange_glueDataObjMap g).ge ?_
    change (I.glueDataObjι ib b).1 ∈ X.basicOpen g
    rwa [← this, ← hfg]
  obtain ⟨a, rfl⟩ := (I.opensRange_glueDataObjMap f).ge H
  obtain ⟨b, rfl⟩ := hmem (X.affineBasicOpen f) (Subtype.ext hfg)
  simp only [glueData_U, ← Scheme.Hom.comp_apply, glueDataObjMap_glueDataObjι] at this ⊢
  simp only [Scheme.affineBasicOpen_coe, Scheme.Hom.comp_base, TopCat.comp_app,
    Scheme.homOfLE_apply, SetLike.coe_eq_coe] at this
  obtain rfl := (I.glueDataObjι (X.affineBasicOpen f)).isEmbedding.injective this
  simp only [glueDataObjMap_ι]
/-
**AlgebraicGeometry.Scheme.IdealSheafData.range_glueDataObj** 是 Mathlib 中的一个引理，位
于命名空间 `AlgebraicGeometry.Scheme.IdealSheafData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma range_glueDataObjι_ι_eq_support_inter (U : X.affineOpens) :
    Set.range (I.glueDataObjι U ≫ U.1.ι) = (I.support : Set X) ∩ U :=
  (I.range_glueDataObjι_ι U).trans (I.coe_support_inter U).symm

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.Scheme.IdealSheafData.range_gluedTo** 是 Mathlib 中的一个引理，位于命名空
间 `AlgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：range_gluedTo : Set.range I.gluedTo = I.support
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_antisymm`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Pa
rtialOrder α] {a b : α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.range_subset_iff`：range_subset_iff : range f subseteq s ↔ forall y, 
f y in s
· 使用定理 `AlgebraicGeometry.Scheme.GlueData.instHasMulticoequalizerDiagram`：∀ (D :
 AlgebraicGeometry.Scheme.GlueData), CategoryTheory.Limits.HasMulticoequalizer D
.diagram
· 使用定理 `CategoryTheory.GlueData.ι_jointly_surjective`：ι_jointly_surjective (F : 
C ⥤ Type v) [PreservesColimit D.diagram.multispan F] [forall i j k : D.J, Preser
vesLimit (cospan (D.f i j) (D.f i …
· 使用定理 `AlgebraicGeometry.Scheme.GlueData.instPreservesColimitWalkingMultispanPr
odJMultispanDiagramForget`：∀ (D : AlgebraicGeometry.Scheme.GlueData),   Category
Theory.Limits.PreservesColimit D.diagram.multispan AlgebraicGeometry.Scheme.forg
et
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.instPreservesLimitSchemeWalkingCospanC
ospanForget_1`：∀ {X Y Z : AlgebraicGeometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z) [H :
 AlgebraicGeometry.IsOpenImmersion f],   CategoryTheory.Limits.PreservesLim…
· 使用定理 `AlgebraicGeometry.Scheme.GlueData.f_open`：∀ (self : AlgebraicGeometry.Sc
heme.GlueData) (i j : self.J), AlgebraicGeometry.IsOpenImmersion (self.f i j)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme.0.AlgebraicGeome
try.Scheme.IdealSheafData.ι_gluedTo`：∀ {X : AlgebraicGeometry.Scheme} (I : X.Ide
alSheafData) (U : ↑X.affineOpens),   CategoryTheory.CategoryStruct.comp (I.glueD
ata.ι U) I.gluedT…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用引理 `AlgebraicGeometry.Scheme.IdealSheafData.range_glueDataObjι_ι_eq_support_
inter`：range_glueDataObjι_ι_eq_support_inter (U : X.affineOpens) : Set.range (I.
glueDataObjι U ≫ U.1.ι) = (I.support : Set X) inter U
· 使用定理 `TopologicalSpace.IsTopologicalBasis.exists_subset_of_mem_open`：∀ {α : Ty
pe u} [t : TopologicalSpace α] {b : Set (Set α)},   TopologicalSpace.IsTopologic
alBasis b → ∀ {a : α} {u : Set α}, a ∈ u → IsOpen u…
· 使用定理 `AlgebraicGeometry.Scheme.isBasis_affineOpens`：∀ (X : AlgebraicGeometry.S
cheme), TopologicalSpace.Opens.IsBasis X.affineOpens
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `isOpen_univ`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen Set.univ
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma range_gluedTo : Set.range I.gluedTo = I.support := by
  refine subset_antisymm (Set.range_subset_iff.mpr fun x ↦ ?_) ?_
  · obtain ⟨ix, x : I.glueDataObj ix, rfl⟩ :=
      I.glueData.toGlueData.ι_jointly_surjective forget x
    change (I.glueData.ι _ ≫ I.gluedTo) x ∈ I.support
    rw [ι_gluedTo]
    exact ((I.range_glueDataObjι_ι_eq_support_inter ix).le ⟨_, rfl⟩).1
  · intro x hx
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    obtain ⟨y, rfl⟩ := (I.range_glueDataObjι_ι_eq_support_inter ⟨U, hU⟩).ge ⟨hx, hxU⟩
    rw [← ι_gluedTo]
    exact ⟨_, rfl⟩

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.Scheme.IdealSheafData.range_glueData_** 是 Mathlib 中的一个引理，位于命
名空间 `AlgebraicGeometry.Scheme.IdealSheafData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma range_glueData_ι (U : X.affineOpens) :
    Set.range (Scheme.Hom.toLRSHom' (X := I.glueDataObj U) <|
      I.glueData.ι U).base = (I.gluedTo ⁻¹ᵁ U : Set I.glueData.glued) := by
  simp only [TopologicalSpace.Opens.map_coe]
  apply I.gluedTo_injective.image_injective
  rw [← Set.range_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base, ι_gluedTo,
    range_glueDataObjι_ι, Set.image_preimage_eq_inter_range, range_gluedTo,
    ← coe_support_inter, Set.inter_comm]

set_option backward.isDefEq.respectTransparency false in
/-- (Implementation) identifying `Spec(Γ(X, U)/I(U))` with its image in `Spec(𝒪ₓ/I)`. -/
private noncomputable
/-
**AlgebraicGeometry.Scheme.IdealSheafData.glueDataObjIso** 是 Mathlib 中的一个定义，位于命名
空间 `AlgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：glueDataObjIso (U : X.affineOpens) : I.glueDataObj U ≅ I.gluedTo ⁻¹ᵁ U
参数：U : X.affineOpens。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def glueDataObjIso (U : X.affineOpens) :
    I.glueDataObj U ≅ I.gluedTo ⁻¹ᵁ U :=
  IsOpenImmersion.isoOfRangeEq (I.glueData.ι U) (Scheme.Opens.ι _) (by
    simp only [Scheme.Opens.range_ι, TopologicalSpace.Opens.map_coe, range_glueData_ι])

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.Scheme.IdealSheafData.glueDataObjIso_hom_** 是 Mathlib 中的一个引理
，位于命名空间 `AlgebraicGeometry.Scheme.IdealSheafData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma glueDataObjIso_hom_ι (U : X.affineOpens) :
    (I.glueDataObjIso U).hom ≫ (I.gluedTo ⁻¹ᵁ U).ι = I.glueData.ι U :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.Scheme.IdealSheafData.glueDataObjIso_hom_restrict** 是 Mathli
b 中的一个引理，位于命名空间 `AlgebraicGeometry.Scheme.IdealSheafData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma glueDataObjIso_hom_restrict (U : X.affineOpens) :
    (I.glueDataObjIso U).hom ≫ I.gluedTo ∣_ ↑U = I.glueDataObjι U := by
  rw [← cancel_mono U.1.ι]; simp

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.Scheme.IdealSheafData.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicG
eometry.Scheme.IdealSheafData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsPreimmersion I.gluedTo := by
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @IsPreimmersion)
    _ (iSup_affineOpens_eq_top X)]
  intro U
  rw [← MorphismProperty.cancel_left_of_respectsIso @IsPreimmersion (I.glueDataObjIso U).hom,
    glueDataObjIso_hom_restrict]
  infer_instance
/-
**AlgebraicGeometry.Scheme.IdealSheafData.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicG
eometry.Scheme.IdealSheafData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private instance : QuasiCompact I.gluedTo :=
  ⟨fun _ _ ↦ (Topology.IsClosedEmbedding.isProperMap
    ⟨I.gluedTo.isEmbedding, I.range_gluedTo ▸ I.support.isClosed⟩).isCompact_preimage⟩

/-- (Implementation) The underlying space of `Spec(𝒪ₓ/I)` is homeomorphic to the support of `I`. -/
noncomputable
/-
**AlgebraicGeometry.Scheme.IdealSheafData.gluedHomeo** 是 Mathlib 中的一个定义，位于命名空间 `
AlgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：gluedHomeo : I.glueData.glued ≃ₜ I.support
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.Scheme.IdealSheafData.range_gluedTo`：range_gluedTo : S
et.range I.gluedTo = I.support
-/
def gluedHomeo : I.glueData.glued ≃ₜ I.support :=
  I.gluedTo.isEmbedding.toHomeomorph.trans (.setCongr I.range_gluedTo)

/-- The subscheme associated to an ideal sheaf. -/
/-
**AlgebraicGeometry.Scheme.IdealSheafData.subscheme** 是 Mathlib 中的一个定义，位于命名空间 `A
lgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：subscheme : Scheme
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The subscheme associated to an ideal sheaf.
-/
noncomputable def subscheme : Scheme :=
  I.glueData.glued.restrict
    (f := TopCat.ofHom (toContinuousMap I.gluedHomeo.symm))
    I.gluedHomeo.symm.isOpenEmbedding

set_option backward.isDefEq.respectTransparency false in
/-- (Implementation) The isomorphism between the subscheme and the glued scheme. -/
noncomputable
/-
**AlgebraicGeometry.Scheme.IdealSheafData.subschemeIso** 是 Mathlib 中的一个定义，位于命名空间
 `AlgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：subschemeIso : I.subscheme ≅ I.glueData.glued
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def subschemeIso : I.subscheme ≅ I.glueData.glued :=
  letI F := I.glueData.glued.ofRestrict (f := TopCat.ofHom (toContinuousMap I.gluedHomeo.symm))
    I.gluedHomeo.symm.isOpenEmbedding
  have : Epi F.base := ConcreteCategory.epi_of_surjective _ I.gluedHomeo.symm.surjective
  letI := IsOpenImmersion.isIso F
  asIso F

set_option backward.isDefEq.respectTransparency.types false in
/-- The inclusion from the subscheme associated to an ideal sheaf. -/
noncomputable
/-
**AlgebraicGeometry.Scheme.IdealSheafData.subscheme** 是 Mathlib 中的一个定义，位于命名空间 `A
lgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：subscheme : Scheme
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def subschemeι : I.subscheme ⟶ X :=
  (I.subschemeIso.hom ≫ I.gluedTo).copyBase Subtype.val <| by
    ext x
    change (I.gluedHomeo (I.gluedHomeo.symm x)).1 = x.1
    rw [I.gluedHomeo.apply_symm_apply]
/-
**AlgebraicGeometry.Scheme.IdealSheafData.subscheme** 是 Mathlib 中的一个定义，位于命名空间 `A
lgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：subscheme : Scheme
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma subschemeι_apply (x : I.subscheme) : I.subschemeι x = x.1 := rfl
/-
**AlgebraicGeometry.Scheme.IdealSheafData.subscheme** 是 Mathlib 中的一个定义，位于命名空间 `A
lgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：subscheme : Scheme
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma subschemeι_def : I.subschemeι = I.subschemeIso.hom ≫ I.gluedTo :=
  Scheme.Hom.copyBase_eq _ _ _

/-- See `AlgebraicGeometry.Morphisms.ClosedImmersion` for the closed immersion version. -/
/-
**AlgebraicGeometry.Scheme.IdealSheafData.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicG
eometry.Scheme.IdealSheafData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See `AlgebraicGeometry.Morphisms.ClosedImmersion` for the closed immersion versi
on.
-/
instance : IsPreimmersion I.subschemeι := by
  rw [subschemeι_def]
  infer_instance
/-
**AlgebraicGeometry.Scheme.IdealSheafData.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicG
eometry.Scheme.IdealSheafData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : QuasiCompact I.subschemeι := by
  rw [subschemeι_def]
  infer_instance

@[simp]
/-
**AlgebraicGeometry.Scheme.IdealSheafData.range_subscheme** 是 Mathlib 中的一个引理，位于命
名空间 `AlgebraicGeometry.Scheme.IdealSheafData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma range_subschemeι : Set.range I.subschemeι = I.support := by
  simp [← range_gluedTo, I.subschemeι_def, Set.range_comp]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**AlgebraicGeometry.Scheme.IdealSheafData.opensRange_glueData_** 是 Mathlib 中的一个引
理，位于命名空间 `AlgebraicGeometry.Scheme.IdealSheafData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma opensRange_glueData_ι_subschemeIso_inv (U : X.affineOpens) :
    (I.glueData.ι U ≫ I.subschemeIso.inv).opensRange = I.subschemeι ⁻¹ᵁ U := by
  ext1
  simp [Set.range_comp, I.range_glueData_ι, subschemeι_def, ← coe_homeoOfIso_symm,
    ← homeoOfIso_symm, ← Homeomorph.coe_symm_toEquiv, Equiv.image_symm_eq_preimage]

set_option backward.isDefEq.respectTransparency false in
/-- The subscheme associated to an ideal sheaf `I` is covered by `Spec(Γ(X, U)/I(U))`. -/
noncomputable
/-
**AlgebraicGeometry.Scheme.IdealSheafData.subschemeCover** 是 Mathlib 中的一个定义，位于命名
空间 `AlgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：subschemeCover : I.subscheme.AffineOpenCover where I₀
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.instJointlySurjectivePrecoverage`：∀ {P : Catego
ryTheory.MorphismProperty AlgebraicGeometry.Scheme},   AlgebraicGeometry.Scheme.
JointlySurjective (AlgebraicGeometry.Scheme.pre…
· 使用定理 `AlgebraicGeometry.iSup_affineOpens_eq_top`：iSup_affineOpens_eq_top (X : 
Scheme) : ⨆ i : X.affineOpens, (i : X.Opens) = ⊤
-/
def subschemeCover : I.subscheme.AffineOpenCover where
  I₀ := X.affineOpens
  X U := .of <| Γ(X, U) ⧸ I.ideal U
  f U := I.glueData.ι U ≫ I.subschemeIso.inv
  idx x := (X.openCoverOfIsOpenCover _ (iSup_affineOpens_eq_top X)).idx x.1
  covers x := by
    let U := (X.openCoverOfIsOpenCover _ (iSup_affineOpens_eq_top X)).idx x.1
    obtain ⟨⟨y, hy : y ∈ U.1⟩, rfl : y = x.1⟩ :=
      (X.openCoverOfIsOpenCover _ (iSup_affineOpens_eq_top X)).covers x.1
    exact (I.opensRange_glueData_ι_subschemeIso_inv U).ge hy

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**AlgebraicGeometry.Scheme.IdealSheafData.opensRange_subschemeCover_map** 是 Math
lib 中的一个引理，位于命名空间 `AlgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：opensRange_subschemeCover_map (U : X.affineOpens) : (I.subschemeCover.f U)
.opensRange = I.subschemeι ⁻¹ᵁ U
参数：U : X.affineOpens。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme.0.AlgebraicGeome
try.Scheme.IdealSheafData.opensRange_glueData_ι_subschemeIso_inv`：∀ {X : Algebra
icGeometry.Scheme} (I : X.IdealSheafData) (U : ↑X.affineOpens),   AlgebraicGeome
try.Scheme.Hom.opensRange (CategoryTheory.Cate…
-/
lemma opensRange_subschemeCover_map (U : X.affineOpens) :
    (I.subschemeCover.f U).opensRange = I.subschemeι ⁻¹ᵁ U :=
  I.opensRange_glueData_ι_subschemeIso_inv U

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**AlgebraicGeometry.Scheme.IdealSheafData.subschemeCover_map_subscheme** 是 Mathl
ib 中的一个引理，位于命名空间 `AlgebraicGeometry.Scheme.IdealSheafData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma subschemeCover_map_subschemeι (U : X.affineOpens) :
    I.subschemeCover.f U ≫ I.subschemeι = I.glueDataObjι U ≫ U.1.ι := by
  simp [subschemeCover, subschemeι_def]

set_option backward.isDefEq.respectTransparency false in
/-- `Γ(𝒪ₓ/I, U) ≅ 𝒪ₓ(U)/I(U)`. -/
noncomputable
/-
**AlgebraicGeometry.Scheme.IdealSheafData.subschemeObjIso** 是 Mathlib 中的一个定义，位于命
名空间 `AlgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：subschemeObjIso (U : X.affineOpens) : Γ(I.subscheme, I.subschemeι ⁻¹ᵁ U) ≅
 .of (Γ(X, U) ⧸ I.ideal U)
参数：U : X.affineOpens。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def subschemeObjIso (U : X.affineOpens) :
    Γ(I.subscheme, I.subschemeι ⁻¹ᵁ U) ≅ .of (Γ(X, U) ⧸ I.ideal U) :=
  I.subscheme.presheaf.mapIso (eqToIso (by simp)).op ≪≫
    (I.subschemeCover.f U).appIso _ ≪≫ Scheme.ΓSpecIso (.of (Γ(X, U) ⧸ I.ideal U))

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.Scheme.IdealSheafData.subscheme** 是 Mathlib 中的一个定义，位于命名空间 `A
lgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：subscheme : Scheme
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma subschemeι_app (U : X.affineOpens) : I.subschemeι.app U =
    CommRingCat.ofHom (Ideal.Quotient.mk (I.ideal U)) ≫
    (I.subschemeObjIso U).inv := by
  have := I.subschemeCover_map_subschemeι U
  simp only [glueDataObjι, Category.assoc, IsAffineOpen.isoSpec_inv_ι] at this
  replace this := Scheme.Hom.congr_app this U
  simp only [Hom.comp_base, TopologicalSpace.Opens.map_comp_obj, Hom.comp_app,
    IsAffineOpen.fromSpec_app_self, eqToHom_op, Category.assoc, Hom.naturality_assoc,
    TopologicalSpace.Opens.map_top, ← ΓSpecIso_inv_naturality_assoc] at this
  simp_rw [← Category.assoc, ← IsIso.comp_inv_eq] at this
  simp only [← this, ← Functor.map_inv, inv_eqToHom, Category.assoc, eqToHom_unop,
    ← Functor.map_comp, IsIso.Iso.inv_inv, subschemeObjIso, Iso.trans_inv, Functor.mapIso_inv,
    Iso.op_inv, eqToIso.inv, eqToHom_op, Iso.hom_inv_id_assoc, Hom.appIso_inv_naturality_assoc,
      Functor.op_map, unop_comp, unop_inv, Quiver.Hom.unop_op,
    Hom.app_appIso_inv_assoc, TopologicalSpace.Opens.carrier_eq_coe, TopologicalSpace.Opens.map_coe,
    homOfLE_leOfHom]
  convert! (Category.comp_id _).symm
  exact CategoryTheory.Functor.map_id _ _
/-
**AlgebraicGeometry.Scheme.IdealSheafData.subscheme** 是 Mathlib 中的一个定义，位于命名空间 `A
lgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：subscheme : Scheme
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma subschemeι_app_surjective (U : X.affineOpens) :
    Function.Surjective (I.subschemeι.app U) := by
  rw [I.subschemeι_app U]
  exact (I.subschemeObjIso U).commRingCatIsoToRingEquiv.symm.surjective.comp
    Ideal.Quotient.mk_surjective

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.Scheme.IdealSheafData.ker_subscheme** 是 Mathlib 中的一个引理，位于命名空
间 `AlgebraicGeometry.Scheme.IdealSheafData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ker_subschemeι_app (U : X.affineOpens) :
    RingHom.ker (I.subschemeι.app U).hom = I.ideal U := by
  rw [subschemeι_app]
  let e : CommRingCat.of (Γ(X, U) ⧸ I.ideal U) ≅ Γ(I.subscheme, I.subschemeι ⁻¹ᵁ U) :=
    (Scheme.ΓSpecIso _).symm ≪≫ ((I.subschemeCover.f U).appIso _).symm ≪≫
      I.subscheme.presheaf.mapIso (eqToIso (by simp)).op
  change RingHom.ker (e.commRingCatIsoToRingEquiv.toRingHom.comp
    (Ideal.Quotient.mk (I.ideal U))) = _
  rw [RingHom.ker_equiv_comp, Ideal.mk_ker]

@[simp]
/-
**AlgebraicGeometry.Scheme.IdealSheafData.ker_subscheme** 是 Mathlib 中的一个引理，位于命名空
间 `AlgebraicGeometry.Scheme.IdealSheafData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ker_subschemeι : I.subschemeι.ker = I := by
  ext; simp [ker_subschemeι_app]
/-
**AlgebraicGeometry.Scheme.IdealSheafData.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicG
eometry.Scheme.IdealSheafData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsEmpty (⊤ : X.IdealSheafData).subscheme := by
  rw [← (subschemeι _).ker_eq_top_iff_isEmpty, ker_subschemeι]

/-- Given `I ≤ J`, this is the map `Spec(Γ(X, U)/J(U)) ⟶ Spec(Γ(X, U)/I(U))`. -/
noncomputable
/-
**AlgebraicGeometry.Scheme.IdealSheafData.glueDataObjHom** 是 Mathlib 中的一个定义，位于命名
空间 `AlgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：glueDataObjHom {I J : IdealSheafData X} (h : I <= J) (U) : J.glueDataObj U
 ⟶ I.glueDataObj U
参数：h : I <= J；U。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def glueDataObjHom {I J : IdealSheafData X} (h : I ≤ J) (U) :
    J.glueDataObj U ⟶ I.glueDataObj U :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (h U)))

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.Scheme.IdealSheafData.glueDataObjHom_** 是 Mathlib 中的一个引理，位于命
名空间 `AlgebraicGeometry.Scheme.IdealSheafData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma glueDataObjHom_ι {I J : IdealSheafData X} (h : I ≤ J) (U) :
    glueDataObjHom h U ≫ I.glueDataObjι U = J.glueDataObjι U := by
  rw [glueDataObjHom, glueDataObjι, glueDataObjι, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp,
    Ideal.Quotient.factor_comp_mk]

@[simp]
/-
**AlgebraicGeometry.Scheme.IdealSheafData.glueDataObjHom_id** 是 Mathlib 中的一个引理，位
于命名空间 `AlgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：glueDataObjHom_id {I : IdealSheafData X} (U) : glueDataObjHom (le_refl I) 
U = 𝟙 _
参数：U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `AlgebraicGeometry.IsPreimmersion.instMonoScheme`：∀ {X Y : AlgebraicGeome
try.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.IsPreimmersion f], CategoryTheory.Mon
o f
· 使用定理 `AlgebraicGeometry.Scheme.IdealSheafData.instIsPreimmersionGlueDataObjι`：
∀ {X : AlgebraicGeometry.Scheme} (I : X.IdealSheafData) (U : ↑X.affineOpens),   
AlgebraicGeometry.IsPreimmersion (I.glueDataObjι U)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `AlgebraicGeometry.Scheme.IdealSheafData.glueDataObjHom_ι`：glueDataObjHom
_ι {I J : IdealSheafData X} (h : I <= J) (U) : glueDataObjHom h U ≫ I.glueDataOb
jι U = J.glueDataObjι U
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma glueDataObjHom_id {I : IdealSheafData X} (U) :
    glueDataObjHom (le_refl I) U = 𝟙 _ := by
  rw [← cancel_mono (I.glueDataObjι U)]
  simp

@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.Scheme.IdealSheafData.glueDataObjHom_comp** 是 Mathlib 中的一个引理
，位于命名空间 `AlgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：glueDataObjHom_comp {I J K : IdealSheafData X} (hIJ : I <= J) (hJK : J <= 
K) (U) : glueDataObjHom hJK U ≫ glueDataObjHom hIJ U = glueDataObjHom (hIJ.trans
 hJK) U
参数：hIJ : I <= J；hJK : J <= K；U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `AlgebraicGeometry.IsPreimmersion.instMonoScheme`：∀ {X Y : AlgebraicGeome
try.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.IsPreimmersion f], CategoryTheory.Mon
o f
· 使用定理 `AlgebraicGeometry.Scheme.IdealSheafData.instIsPreimmersionGlueDataObjι`：
∀ {X : AlgebraicGeometry.Scheme} (I : X.IdealSheafData) (U : ↑X.affineOpens),   
AlgebraicGeometry.IsPreimmersion (I.glueDataObjι U)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `AlgebraicGeometry.Scheme.IdealSheafData.glueDataObjHom_ι`：glueDataObjHom
_ι {I J : IdealSheafData X} (h : I <= J) (U) : glueDataObjHom h U ≫ I.glueDataOb
jι U = J.glueDataObjι U
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma glueDataObjHom_comp {I J K : IdealSheafData X} (hIJ : I ≤ J) (hJK : J ≤ K) (U) :
    glueDataObjHom hJK U ≫ glueDataObjHom hIJ U = glueDataObjHom (hIJ.trans hJK) U := by
  rw [← cancel_mono (I.glueDataObjι U)]
  simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The inclusion of ideal sheaf induces an inclusion of subschemes -/
noncomputable
/-
**AlgebraicGeometry.Scheme.IdealSheafData.inclusion** 是 Mathlib 中的一个定义，位于命名空间 `A
lgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：inclusion {I J : IdealSheafData X} (h : I <= J) : J.subscheme ⟶ I.subschem
e
参数：h : I <= J。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def inclusion {I J : IdealSheafData X} (h : I ≤ J) :
    J.subscheme ⟶ I.subscheme :=
  J.subschemeCover.openCover.glueMorphisms (fun U ↦ glueDataObjHom h U ≫ I.subschemeCover.f U)
  (by
    intro U V
    simp only [← cancel_mono I.subschemeι, AffineOpenCover.openCover_X, glueDataObjHom_ι_assoc,
      AffineOpenCover.openCover_f, Category.assoc, subschemeCover_map_subschemeι]
    rw [← subschemeCover_map_subschemeι, pullback.condition_assoc, subschemeCover_map_subschemeι])

@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.Scheme.IdealSheafData.subSchemeCover_map_inclusion** 是 Mathl
ib 中的一个引理，位于命名空间 `AlgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：subSchemeCover_map_inclusion {I J : IdealSheafData X} (h : I <= J) (U) : J
.subschemeCover.f U ≫ inclusion h = glueDataObjHom h U ≫ I.subschemeCover.f U
参数：h : I <= J；U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Cover.ι_glueMorphisms`：ι_glueMorphisms (𝒰 : Ope
nCover.{v} X) {Y : Scheme} (f : forall x, 𝒰.X x ⟶ Y) (hf : forall x y, pullback.
fst (𝒰.f x) (𝒰.f y) ≫ f x = pullback…
-/
lemma subSchemeCover_map_inclusion {I J : IdealSheafData X} (h : I ≤ J) (U) :
    J.subschemeCover.f U ≫ inclusion h = glueDataObjHom h U ≫ I.subschemeCover.f U :=
  J.subschemeCover.openCover.ι_glueMorphisms _ _ _

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.Scheme.IdealSheafData.inclusion_subscheme** 是 Mathlib 中的一个引理
，位于命名空间 `AlgebraicGeometry.Scheme.IdealSheafData`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma inclusion_subschemeι {I J : IdealSheafData X} (h : I ≤ J) :
    inclusion h ≫ I.subschemeι = J.subschemeι :=
  J.subschemeCover.openCover.hom_ext _ _ fun _ ↦ by simp

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp, reassoc]
/-
**AlgebraicGeometry.Scheme.IdealSheafData.inclusion_id** 是 Mathlib 中的一个引理，位于命名空间
 `AlgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：inclusion_id (I : IdealSheafData X) : inclusion le_rfl = 𝟙 I.subscheme
参数：I : IdealSheafData X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Cover.hom_ext`：hom_ext (𝒰 : OpenCover.{v} X) {Y
 : Scheme} (f₁ f₂ : X ⟶ Y) (h : forall x, 𝒰.f x ≫ f₁ = 𝒰.f x ≫ f₂) : f₁ = f₂
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.Scheme.IdealSheafData.subSchemeCover_map_inclusion`：su
bSchemeCover_map_inclusion {I J : IdealSheafData X} (h : I <= J) (U) : J.subsche
meCover.f U ≫ inclusion h = glueDataObjHom h U ≫ I.subsche…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `AlgebraicGeometry.Scheme.IdealSheafData.glueDataObjHom_id`：glueDataObjHo
m_id {I : IdealSheafData X} (U) : glueDataObjHom (le_refl I) U = 𝟙 _
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inclusion_id (I : IdealSheafData X) :
    inclusion le_rfl = 𝟙 I.subscheme :=
  I.subschemeCover.openCover.hom_ext _ _ fun _ ↦ by simp

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.Scheme.IdealSheafData.inclusion_comp** 是 Mathlib 中的一个引理，位于命名
空间 `AlgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：inclusion_comp {I J K : IdealSheafData X} (h₁ : I <= J) (h₂ : J <= K) : in
clusion h₂ ≫ inclusion h₁ = inclusion (h₁.trans h₂)
参数：h₁ : I <= J；h₂ : J <= K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Cover.hom_ext`：hom_ext (𝒰 : OpenCover.{v} X) {Y
 : Scheme} (f₁ f₂ : X ⟶ Y) (h : forall x, 𝒰.f x ≫ f₁ = 𝒰.f x ≫ f₂) : f₁ = f₂
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AlgebraicGeometry.Scheme.AffineOpenCover.openCover_f`：∀ {X : AlgebraicGe
ometry.Scheme} (𝒰 : X.AffineOpenCover) (j : 𝒰.I₀), 𝒰.openCover.f j = 𝒰.f j
· 使用定理 `AlgebraicGeometry.Scheme.IdealSheafData.subSchemeCover_map_inclusion_ass
oc`：∀ {X : AlgebraicGeometry.Scheme} {I J : X.IdealSheafData} (h : I ≤ J) (U : J
.subschemeCover.I₀)   {Z : AlgebraicGeometry.Scheme} (h_1 : I.su…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `AlgebraicGeometry.Scheme.IdealSheafData.subSchemeCover_map_inclusion`：su
bSchemeCover_map_inclusion {I J : IdealSheafData X} (h : I <= J) (U) : J.subsche
meCover.f U ≫ inclusion h = glueDataObjHom h U ≫ I.subsche…
· 使用定理 `AlgebraicGeometry.Scheme.IdealSheafData.glueDataObjHom_comp_assoc`：∀ {X 
: AlgebraicGeometry.Scheme} {I J K : X.IdealSheafData} (hIJ : I ≤ J) (hJK : J ≤ 
K) (U : ↑X.affineOpens)   {Z : AlgebraicGeometry.Scheme…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inclusion_comp {I J K : IdealSheafData X} (h₁ : I ≤ J) (h₂ : J ≤ K) :
    inclusion h₂ ≫ inclusion h₁ = inclusion (h₁.trans h₂) :=
  K.subschemeCover.openCover.hom_ext _ _ fun _ ↦ by simp

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The functor taking an ideal sheaf to its associated subscheme. -/
@[simps]
noncomputable
/-
**AlgebraicGeometry.Scheme.IdealSheafData.subschemeFunctor** 是 Mathlib 中的一个定义，位于
命名空间 `AlgebraicGeometry.Scheme.IdealSheafData`。
形式化陈述：subschemeFunctor (Y : Scheme.{u}) : (IdealSheafData Y)ᵒᵖ ⥤ Over Y where ob
j I
参数：Y : Scheme.{u}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def subschemeFunctor (Y : Scheme.{u}) : (IdealSheafData Y)ᵒᵖ ⥤ Over Y where
  obj I := .mk I.unop.subschemeι
  map {I J} h := Over.homMk (IdealSheafData.inclusion h.unop.le)

end IdealSheafData

noncomputable section image

open Limits

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.affineOpens)

/-- The scheme-theoretic image of a morphism. -/
/-
**AlgebraicGeometry.Scheme.Hom.image** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeometr
y.Scheme.Hom`。
形式化陈述：{X Y : AlgebraicGeometry.Scheme} → (X ⟶ Y) → AlgebraicGeometry.Scheme
参数：X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The scheme-theoretic image of a morphism.
-/
abbrev Hom.image : Scheme.{u} := f.ker.subscheme

/-- The embedding from the scheme-theoretic image to the codomain. -/
/-
**AlgebraicGeometry.Scheme.Hom.image** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeometr
y.Scheme.Hom`。
形式化陈述：{X Y : AlgebraicGeometry.Scheme} → (X ⟶ Y) → AlgebraicGeometry.Scheme
参数：X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The embedding from the scheme-theoretic image to the codomain.
-/
abbrev Hom.imageι : f.image ⟶ Y := f.ker.subschemeι

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.Scheme.ideal_ker_le_ker_** 是 Mathlib 中的一个引理，位于命名空间 `Algebrai
cGeometry.Scheme`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ideal_ker_le_ker_ΓSpecIso_inv_comp :
    f.ker.ideal U ≤ RingHom.ker ((ΓSpecIso Γ(Y, ↑U)).inv ≫
      (pullback.snd f U.1.ι ≫ U.1.toSpecΓ).appTop).hom := by
  let e : Γ(X, f ⁻¹ᵁ ↑U) ≅ Γ(Limits.pullback (C := Scheme) f U.1.ι, ⊤) :=
    X.presheaf.mapIso (eqToIso (by simp [Scheme.Hom.opensRange_pullbackFst])).op
      ≪≫ (Limits.pullback.fst (C := Scheme) f U.1.ι).appIso ⊤
  have he : f.app U ≫ e.hom =
      (ΓSpecIso Γ(Y, ↑U)).inv ≫ (pullback.snd f U.1.ι ≫ U.1.toSpecΓ).appTop := by
    rw [← (Iso.inv_comp_eq _).mpr U.2.isoSpec_inv_appTop, Category.assoc, Iso.eq_inv_comp]
    simp only [Opens.topIso_hom, eqToHom_op, Hom.app_eq_appLE, Iso.trans_hom, Functor.mapIso_hom,
      Iso.op_hom, eqToIso.hom, Hom.appIso_hom, Hom.appLE_map, Hom.map_appLE, Hom.appLE_comp_appLE,
      Opens.map_top, e, pullback.condition, IsAffineOpen.toSpecΓ_isoSpec_inv, Category.assoc]
    rw [Hom.comp_appLE, Opens.ι_app]
    exact Hom.map_appLE _ _ (homOfLE le_top).op
  rw [← he]
  refine (IdealSheafData.ideal_ofIdeals_le _ _).trans_eq
    (RingHom.ker_equiv_comp _ e.commRingCatIsoToRingEquiv).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- (Implementation): Use `Hom.toImage` instead which has better def-eqs. -/
noncomputable
/-
**AlgebraicGeometry.Scheme.Hom.toImageAux** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGe
ometry.Scheme.Hom`。
形式化陈述：{X Y : AlgebraicGeometry.Scheme} → (f : X ⟶ Y) → X ⟶ AlgebraicGeometry.Sch
eme.Hom.image f
参数：f : X ⟶ Y。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.instIsStableUnderBaseChangePrecoverageOfIsJoint
lySurjectivePreservingOfIsStableUnderBaseChange`：∀ (P : CategoryTheory.MorphismP
roperty AlgebraicGeometry.Scheme)   [AlgebraicGeometry.Scheme.IsJointlySurjectiv
ePreserving P] [P.IsStableUnd…
· 使用定理 `AlgebraicGeometry.Scheme.instIsJointlySurjectivePreservingIsOpenImmersio
n`：AlgebraicGeometry.Scheme.IsJointlySurjectivePreserving AlgebraicGeometry.IsOp
enImmersion
· 使用定理 `AlgebraicGeometry.iSup_affineOpens_eq_top`：iSup_affineOpens_eq_top (X : 
Scheme) : ⨆ i : X.affineOpens, (i : X.Opens) = ⊤
-/
def Hom.toImageAux : X ⟶ f.image :=
  Cover.glueMorphisms ((Y.openCoverOfIsOpenCover _ (iSup_affineOpens_eq_top Y)).pullback₁ f)
    (fun U ↦ (pullback.snd f U.1.ι ≫ U.1.toSpecΓ).liftQuotient _
      (by exact ideal_ker_le_ker_ΓSpecIso_inv_comp f U) ≫ f.ker.subschemeCover.f U) (by
    intro U V
    rw [← cancel_mono f.imageι]
    simp [IdealSheafData.glueDataObjι, Scheme.Hom.liftQuotient_comp_assoc,
      ← pullback.condition, ← pullback.condition_assoc])

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.Scheme.Hom.toImageAux_spec** 是 Mathlib 中的一个定理，位于命名空间 `Algebr
aicGeometry.Scheme.Hom`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y),   CategoryTheory.CategoryS
truct.comp (AlgebraicGeometry.Scheme.Hom.toImageAux f)       (AlgebraicGeometry.
Scheme.Hom.imageι f) =     f
参数：f : X ⟶ Y；AlgebraicGeometry.Scheme.Hom.toImageAux f；AlgebraicGeometry.Scheme.
Hom.imageι f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Cover.hom_ext`：hom_ext (𝒰 : OpenCover.{v} X) {Y
 : Scheme} (f₁ f₂ : X ⟶ Y) (h : forall x, 𝒰.f x ≫ f₁ = 𝒰.f x ≫ f₂) : f₁ = f₂
· 使用定理 `AlgebraicGeometry.Scheme.instIsStableUnderBaseChangePrecoverageOfIsJoint
lySurjectivePreservingOfIsStableUnderBaseChange`：∀ (P : CategoryTheory.MorphismP
roperty AlgebraicGeometry.Scheme)   [AlgebraicGeometry.Scheme.IsJointlySurjectiv
ePreserving P] [P.IsStableUnd…
· 使用定理 `AlgebraicGeometry.Scheme.instIsJointlySurjectivePreservingIsOpenImmersio
n`：AlgebraicGeometry.Scheme.IsJointlySurjectivePreserving AlgebraicGeometry.IsOp
enImmersion
· 使用定理 `AlgebraicGeometry.iSup_affineOpens_eq_top`：iSup_affineOpens_eq_top (X : 
Scheme) : ⨆ i : X.affineOpens, (i : X.Opens) = ⊤
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.Cover.ι_glueMorphisms_assoc`：∀ {X : AlgebraicGe
ometry.Scheme} (𝒰 : X.OpenCover) {Y : AlgebraicGeometry.Scheme} (f : (x : 𝒰.I₀) 
→ 𝒰.X x ⟶ Y)   (hf :     ∀ (x y : 𝒰.I₀),  …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `AlgebraicGeometry.Scheme.IdealSheafData.subschemeCover_map_subschemeι`：s
ubschemeCover_map_subschemeι (U : X.affineOpens) : I.subschemeCover.f U ≫ I.subs
chemeι = I.glueDataObjι U ≫ U.1.ι
· 使用定理 `AlgebraicGeometry.Scheme.Hom.liftQuotient_comp_assoc`：∀ {X : AlgebraicGe
ometry.Scheme} {A : CommRingCat} (f : X.Hom (AlgebraicGeometry.Spec A)) (I : Ide
al ↑A)   (hI :     I ≤       RingHom.ker  …
· 使用引理 `AlgebraicGeometry.IsAffineOpen.toSpecΓ_fromSpec`：toSpecΓ_fromSpec : U.to
SpecΓ ≫ hU.fromSpec = U.ι
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Hom.toImageAux_spec :
    f.toImageAux ≫ f.imageι = f := by
  apply Cover.hom_ext ((Y.openCoverOfIsOpenCover _ (iSup_affineOpens_eq_top Y)).pullback₁ f)
  intro U
  simp only [Hom.toImageAux, Cover.ι_glueMorphisms_assoc]
  simp [IdealSheafData.glueDataObjι, Scheme.Hom.liftQuotient_comp_assoc, pullback.condition]

/-- The morphism from the domain to the scheme-theoretic image. -/
noncomputable
/-
**AlgebraicGeometry.Scheme.Hom.toImage** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeome
try.Scheme.Hom`。
形式化陈述：{X Y : AlgebraicGeometry.Scheme} → (f : X ⟶ Y) → X ⟶ AlgebraicGeometry.Sch
eme.Hom.image f
参数：f : X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def Hom.toImage : X ⟶ f.image :=
  f.toImageAux.copyBase (fun x ↦ ⟨f x, f.range_subset_ker_support ⟨x, rfl⟩⟩)
    (funext fun x ↦ Subtype.ext congr($f.toImageAux_spec x))

@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.Scheme.Hom.toImage_image** 是 Mathlib 中的一个引理，位于命名空间 `Algebrai
cGeometry.Scheme`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Hom.toImage_imageι :
    f.toImage ≫ f.imageι = f := by
  convert f.toImageAux_spec
  exact Scheme.Hom.copyBase_eq _ _ _
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [QuasiCompact f] : IsDominant f.toImage where
  denseRange := by
    rw [denseRange_iff_closure_range, f.imageι.isEmbedding.closure_eq_preimage_closure_image,
      ← Set.univ_subset_iff, ← Set.image_subset_iff, Set.image_univ,
      IdealSheafData.range_subschemeι, Hom.support_ker, ← Set.range_comp,
      ← TopCat.coe_comp, ← Scheme.Hom.comp_base, f.toImage_imageι]
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [QuasiCompact f] : QuasiCompact f.toImage :=
  have : QuasiCompact (f.toImage ≫ f.imageι) := by simpa
  .of_comp _ f.imageι
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsIso (IdealSheafData.subschemeι ⊥ : _ ⟶ X) :=
  ⟨Scheme.Hom.toImage (𝟙 X) ≫ IdealSheafData.inclusion bot_le,
    by simp [← cancel_mono (IdealSheafData.subschemeι _)], by simp⟩
/-
**AlgebraicGeometry.Scheme.isIso_subscheme** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicG
eometry.Scheme`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isIso_subschemeι_iff_eq_bot (I : X.IdealSheafData) : IsIso I.subschemeι ↔ I = ⊥ :=
  ⟨fun h ↦ by simp [← I.ker_subschemeι], fun h ↦ h ▸ inferInstance⟩

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.Scheme.Hom.toImage_app** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicG
eometry.Scheme.Hom`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) (U : ↑Y.affineOpens),   Alg
ebraicGeometry.Scheme.Hom.app (AlgebraicGeometry.Scheme.Hom.toImage f)       ((T
opologicalSpace.Opens.map (AlgebraicGeometry.Scheme.Hom.imageι f).base).obj ↑U) 
=     CategoryTheory.CategoryStruct.comp ((AlgebraicGeometry.Scheme.Hom.ker f).s
ubschemeObjIso U).hom       (CommRingCat.ofHom         (Ideal.Quotient.lift ((Al
gebraicGeometry.Scheme.Hom.ker f).ideal U)           (CommRingCat.Hom.hom (Algeb
raicGeometry.Scheme.Hom.app f ↑U)) ⋯))
参数：f : X ⟶ Y；U : ↑Y.affineOpens；AlgebraicGeometry.Scheme.Hom.toImage f；(Topologi
calSpace.Opens.map (AlgebraicGeometry.Scheme.Hom.imageι f).base).obj ↑U；(Algebra
icGeometry.Scheme.Hom.ker f).subschemeObjIso U；CommRingCat.ofHom         (Ideal.
Quotient.lift ((AlgebraicGeometry.Scheme.Hom.ker f).ideal U)           (CommRing
Cat.Hom.hom (AlgebraicGeometry.Scheme.Hom.app f ↑U)) ⋯)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ConcreteCategory.epi_of_surjective`：epi_of_surjective {X 
Y : C} (f : X ⟶ Y) (s : Function.Surjective f) : Epi f
· 使用引理 `AlgebraicGeometry.Scheme.IdealSheafData.subschemeι_app_surjective`：subsc
hemeι_app_surjective (U : X.affineOpens) : Function.Surjective (I.subschemeι.app
 U)
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用引理 `AlgebraicGeometry.Scheme.IdealSheafData.ideal_ofIdeals_le`：ideal_ofIdeal
s_le (I : forall U : X.affineOpens, Ideal Γ(X, U)) : (ofIdeals I).ideal <= I
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `AlgebraicGeometry.Scheme.Hom.comp_app`：comp_app {X Y Z : Scheme} (f : X 
⟶ Y) (g : Y ⟶ Z) (U) : (f ≫ g).app U = g.app U ≫ f.app _
· 使用定理 `AlgebraicGeometry.Scheme.Hom.toImage_imageι`：∀ {X Y : AlgebraicGeometry.
Scheme} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.comp (AlgebraicGeometry.Sch
eme.Hom.toImage f) (AlgebraicGeom…
· 使用定理 `AlgebraicGeometry.Scheme.Hom.congr_app`：congr_app {X Y : Scheme} {f g : 
X ⟶ Y} (e : f = g) (U) : f.app U = g.app U ≫ X.presheaf.map (eqToHom (by subst e
; rfl)).op
· 使用引理 `AlgebraicGeometry.Scheme.IdealSheafData.subschemeι_app`：subschemeι_app (
U : X.affineOpens) : I.subschemeι.app U = CommRingCat.ofHom (Ideal.Quotient.mk (
I.ideal U)) ≫ (I.subschemeObjIso U).inv
· 使用定理 `CategoryTheory.instIsIsoEqToHom`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {X Y : C} (h : X = Y),   CategoryTheory.IsIso (CategoryTheo
ry.eqToHom h)
· 使用定理 `CategoryTheory.IsIso.eq_comp_inv`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {X Y Z : C} (α : Y ⟶ X) [inst_1 : CategoryTheory.IsIso α]   {
f : Z ⟶ X} {g : Z ⟶ Y}…
· 使用定理 `CategoryTheory.Functor.map_inv`：map_inv (F : C ⥤ D) {X Y : C} (f : X ⟶ Y
) [IsIso f] : F.map (inv f) = inv (F.map f)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `CategoryTheory.eqToHom_op`：eqToHom_op {X Y : C} (h : X = Y) : (eqToHom h
).op = eqToHom (congr_arg op h.symm)
· 使用定理 `CategoryTheory.inv.congr_simp`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (f f_1 : X ⟶ Y) (e_f : f = f_1)   [I : CategoryTheory.
IsIso f], CategoryT…
· 使用定理 `CategoryTheory.inv_eqToHom`：inv_eqToHom {X Y : C} (h : X = Y) : inv (eqT
oHom h) = eqToHom h.symm
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
· 使用引理 `CommRingCat.ofHom_comp`：ofHom_comp {R S T : Type u} [CommRing R] [CommRi
ng S] [CommRing T] (f : R ->+* S) (g : S ->+* T) : ofHom (g.comp f) = ofHom f ≫ 
ofHom g
· 使用引理 `Ideal.Quotient.lift_comp_mk`：lift_comp_mk (f : R ->+* S) (H : forall a :
 R, a in I -> f a = 0) : (lift I f H).comp (mk I) = f
· 使用引理 `CommRingCat.ofHom_hom`：ofHom_hom {R S : CommRingCat} (f : R ⟶ S) : ofHom
 (Hom.hom f) = f
· 使用定理 `CategoryTheory.eqToHom_refl`：eqToHom_refl {C : Type u₁} [CategoryStruct.
{v₁} C] (X : C) (p : X = X) : eqToHom p = 𝟙 X
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
lemma Hom.toImage_app :
    f.toImage.app (f.imageι ⁻¹ᵁ U) =
      (f.ker.subschemeObjIso U).hom ≫ CommRingCat.ofHom
        (Ideal.Quotient.lift _ (f.app U.1).hom (IdealSheafData.ideal_ofIdeals_le _ _)) := by
  have := ConcreteCategory.epi_of_surjective _ (f.ker.subschemeι_app_surjective U)
  rw [← cancel_epi (f.ker.subschemeι.app U), ← Scheme.Hom.comp_app,
    Scheme.Hom.congr_app f.toImage_imageι, f.ker.subschemeι_app,
    ← IsIso.eq_comp_inv, ← Functor.map_inv]
  simp only [Hom.comp_base, Opens.map_comp_obj, Category.assoc,
    Iso.inv_hom_id_assoc, eqToHom_op, inv_eqToHom]
  rw [← reassoc_of% CommRingCat.ofHom_comp, Ideal.Quotient.lift_comp_mk, CommRingCat.ofHom_hom,
    eqToHom_refl, CategoryTheory.Functor.map_id]
  exact (Category.comp_id _).symm

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.Scheme.Hom.toImage_app_injective** 是 Mathlib 中的一个定理，位于命名空间 `
AlgebraicGeometry.Scheme.Hom`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) (U : ↑Y.affineOpens) [Algeb
raicGeometry.QuasiCompact f],   Function.Injective     ⇑(CategoryTheory.Concrete
Category.hom         (AlgebraicGeometry.Scheme.Hom.app (AlgebraicGeometry.Scheme
.Hom.toImage f)           ((TopologicalSpace.Opens.map (AlgebraicGeometry.Scheme
.Hom.imageι f).base).obj ↑U)))
参数：f : X ⟶ Y；U : ↑Y.affineOpens；CategoryTheory.ConcreteCategory.hom         (Alg
ebraicGeometry.Scheme.Hom.app (AlgebraicGeometry.Scheme.Hom.toImage f)          
 ((TopologicalSpace.Opens.map (AlgebraicGeometry.Scheme.Hom.imageι f).base).obj 
↑U))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用引理 `AlgebraicGeometry.Scheme.IdealSheafData.ideal_ofIdeals_le`：ideal_ofIdeal
s_le (I : forall U : X.affineOpens, Ideal Γ(X, U)) : (ofIdeals I).ideal <= I
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.Hom.toImage_app`：∀ {X Y : AlgebraicGeometry.Sch
eme} (f : X ⟶ Y) (U : ↑Y.affineOpens),   AlgebraicGeometry.Scheme.Hom.app (Algeb
raicGeometry.Scheme.Hom.toImag…
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `RingHom.lift_injective_of_ker_le_ideal`：lift_injective_of_ker_le_ideal (
I : Ideal R) [I.IsTwoSided] {f : R ->+* S} (H : forall a : R, a in I -> f a = 0)
 (hI : ker f <= I) : Functio…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AlgebraicGeometry.Scheme.Hom.ker_apply`：∀ {X Y : AlgebraicGeometry.Schem
e} (f : X.Hom Y) [AlgebraicGeometry.QuasiCompact f] (U : ↑Y.affineOpens),   f.ke
r.ideal U = RingHom.ker (Com…
· 使用定理 `RingEquiv.injective`：∀ {R : Type u_4} {S : Type u_5} [inst : Mul R] [ins
t_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S] (e : R ≃+* S),   Function.Injecti
ve ⇑e
-/
lemma Hom.toImage_app_injective [QuasiCompact f] :
    Function.Injective (f.toImage.app (f.imageι ⁻¹ᵁ U)) := by
  simp only [f.toImage_app U, CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp]
  exact (RingHom.lift_injective_of_ker_le_ideal _ _ (by simp)).comp
    (f.ker.subschemeObjIso U).commRingCatIsoToRingEquiv.injective
/-
**AlgebraicGeometry.Scheme.Hom.stalkFunctor_toImage_injective** 是 Mathlib 中的一个定理
，位于命名空间 `AlgebraicGeometry.Scheme.Hom`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.QuasiCom
pact f]   (x : ↥(AlgebraicGeometry.Scheme.Hom.image f)),   Function.Injective   
  ⇑(CategoryTheory.ConcreteCategory.hom         ((TopCat.Presheaf.stalkFunctor C
ommRingCat x).map (AlgebraicGeometry.Scheme.Hom.toImage f).c))
参数：f : X ⟶ Y；x : ↥(AlgebraicGeometry.Scheme.Hom.image f)；CategoryTheory.Concrete
Category.hom         ((TopCat.Presheaf.stalkFunctor CommRingCat x).map (Algebrai
cGeometry.Scheme.Hom.toImage f).c)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `TopCat.Presheaf.stalkFunctor_map_injective_of_isBasis`：stalkFunctor_map_
injective_of_isBasis {F G : X.Presheaf C} {α : F ⟶ G} (hα : forall U in B, Funct
ion.Injective (α.app (op U))) (x : X) : Fun…
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
· 使用定理 `Topology.IsInducing.continuous`：∀ {X : Type u_1} {Y : Type u_2} {f : X →
 Y} [inst : TopologicalSpace Y] [inst_1 : TopologicalSpace X],   Topology.IsIndu
cing f → Continuous …
· 使用定理 `Topology.IsEmbedding.isInducing`：∀ {X : Type u_1} {Y : Type u_2} {f : X 
→ Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.IsEmb
edding f → Topology.I…
· 使用定理 `AlgebraicGeometry.Scheme.Hom.isEmbedding`：∀ {X Y : AlgebraicGeometry.Sch
eme} (f : X ⟶ Y) [self : AlgebraicGeometry.IsPreimmersion f], Topology.IsEmbeddi
ng ⇑f
· 使用定理 `AlgebraicGeometry.Scheme.IdealSheafData.instIsPreimmersionSubschemeι`：∀ 
{X : AlgebraicGeometry.Scheme} (I : X.IdealSheafData), AlgebraicGeometry.IsPreim
mersion I.subschemeι
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用定理 `TopologicalSpace.Opens.IsBasis.of_isInducing`：∀ {α : Type u_2} {β : Type
 u_3} [inst : TopologicalSpace α] [inst_1 : TopologicalSpace β]   {B : Set (Topo
logicalSpace.Opens β)},   Topologi…
· 使用定理 `AlgebraicGeometry.Scheme.isBasis_affineOpens`：∀ (X : AlgebraicGeometry.S
cheme), TopologicalSpace.Opens.IsBasis X.affineOpens
· 使用定理 `AlgebraicGeometry.Scheme.Hom.toImage_app_injective`：∀ {X Y : AlgebraicGe
ometry.Scheme} (f : X ⟶ Y) (U : ↑Y.affineOpens) [AlgebraicGeometry.QuasiCompact 
f],   Function.Injective     ⇑(CategoryT…
-/
lemma Hom.stalkFunctor_toImage_injective [QuasiCompact f] (x) :
    Function.Injective ((TopCat.Presheaf.stalkFunctor _ x).map f.toImage.c) := by
  apply TopCat.Presheaf.stalkFunctor_map_injective_of_isBasis
    (hB := (Y.isBasis_affineOpens.of_isInducing f.imageι.isEmbedding.isInducing))
  rintro _ ⟨U, hU, rfl⟩
  exact f.toImage_app_injective ⟨U, hU⟩

set_option backward.defeqAttrib.useBackward true in
open IdealSheafData in
/-- The adjunction between `Y.IdealSheafData` and `(Over Y)ᵒᵖ` given by taking kernels. -/
@[simps]
noncomputable
/-
**AlgebraicGeometry.Scheme.kerAdjunction** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeo
metry.Scheme`。
形式化陈述：(Y : AlgebraicGeometry.Scheme) → (AlgebraicGeometry.Scheme.IdealSheafData.
subschemeFunctor Y).rightOp ⊣ Y.kerFunctor
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def kerAdjunction (Y : Scheme.{u}) : (subschemeFunctor Y).rightOp ⊣ Y.kerFunctor where
  unit.app I := eqToHom (by simp)
  counit.app f := (Over.homMk f.unop.hom.toImage f.unop.hom.toImage_imageι).op
  counit.naturality _ _ _ := Quiver.Hom.unop_inj (by ext1; simp [← cancel_mono (subschemeι _)])
  left_triangle_components I := Quiver.Hom.unop_inj (by ext1; simp [← cancel_mono (subschemeι _)])

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (IdealSheafData.subschemeFunctor Y).Full :=
  have : IsIso Y.kerAdjunction.rightOp.counit := by
    simp [NatTrans.isIso_iff_isIso_app, CategoryTheory.instIsIsoEqToHom]
  Y.kerAdjunction.rightOp.fullyFaithfulROfIsIsoCounit.full

end image

end Scheme

end AlgebraicGeometry

