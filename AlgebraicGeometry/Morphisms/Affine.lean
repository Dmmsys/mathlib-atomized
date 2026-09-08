/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!

# Affine morphisms of schemes

A morphism of schemes `f : X ⟶ Y` is affine if the preimage
of an arbitrary affine open subset of `Y` is affine.

It is equivalent to ask only that `Y` is covered by affine opens whose preimage is affine.

## Main results

- `AlgebraicGeometry.IsAffineHom`: The class of affine morphisms.
- `AlgebraicGeometry.isAffineOpen_of_isAffineOpen_basicOpen`:
  If `s` is a spanning set of `Γ(X, U)`, such that each `X.basicOpen i` is affine,
  then `U` is also affine.
- `AlgebraicGeometry.isAffineHom_isStableUnderBaseChange`:
  Affine morphisms are stable under base change.

We also provide the instance `HasAffineProperty @IsAffineHom fun X _ _ _ ↦ IsAffine X`.

-/

public section

universe v u

open CategoryTheory Limits TopologicalSpace Opposite

namespace AlgebraicGeometry

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- A morphism of schemes `X ⟶ Y` is affine if
the preimage of any affine open subset of `Y` is affine. -/
@[mk_iff]
/-
**AlgebraicGeometry.IsAffineHom** 是 Mathlib 中的一个归纳类型，位于命名空间 `AlgebraicGeometry`。
形式化陈述：{X Y : AlgebraicGeometry.Scheme} → (X ⟶ Y) → Prop
参数：X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism of schemes `X ⟶ Y` is affine if
the preimage of any affine open subset of `Y` is affine.
-/
class IsAffineHom {X Y : Scheme} (f : X ⟶ Y) : Prop where
  isAffine_preimage : ∀ U : Y.Opens, IsAffineOpen U → IsAffineOpen (f ⁻¹ᵁ U)
/-
**AlgebraicGeometry.IsAffineOpen.preimage** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGe
ometry.IsAffineOpen`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} {U : Y.Opens},   AlgebraicGeometry.IsAf
fineOpen U →     ∀ (f : X ⟶ Y) [AlgebraicGeometry.IsAffineHom f],       Algebrai
cGeometry.IsAffineOpen ((TopologicalSpace.Opens.map f.base).obj U)
参数：f : X ⟶ Y；(TopologicalSpace.Opens.map f.base).obj U。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.IsAffineHom.isAffine_preimage`：∀ {X Y : AlgebraicGeome
try.Scheme} {f : X ⟶ Y} [self : AlgebraicGeometry.IsAffineHom f] (U : Y.Opens), 
  AlgebraicGeometry.IsAffineOpen U → …
-/
lemma IsAffineOpen.preimage {X Y : Scheme} {U : Y.Opens} (hU : IsAffineOpen U)
    (f : X ⟶ Y) [IsAffineHom f] :
    IsAffineOpen (f ⁻¹ᵁ U) :=
  IsAffineHom.isAffine_preimage _ hU
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 900) [IsIso f] : IsAffineHom f :=
  ⟨fun _ hU ↦ hU.preimage_of_isIso f⟩
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 900) [IsAffineHom f] : QuasiCompact f :=
  quasiCompact_iff_forall_isAffineOpen.mpr fun _ hU ↦ (hU.preimage f).isCompact
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsAffineHom f] [IsAffineHom g] : IsAffineHom (f ≫ g) := by
  constructor
  intro U hU
  rw [Scheme.Hom.comp_base, Opens.map_comp_obj]
  apply IsAffineHom.isAffine_preimage
  apply IsAffineHom.isAffine_preimage
  exact hU
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MorphismProperty.IsMultiplicative @IsAffineHom where
  id_mem := inferInstance
  comp_mem _ _ _ _ := inferInstance
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X : Scheme} (r : Γ(X, ⊤)) :
    IsAffineHom (X.basicOpen r).ι := by
  constructor
  intro U hU
  fapply (Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion (X.basicOpen r).ι).mp
  convert! hU.basicOpen (X.presheaf.map (homOfLE le_top).op r)
  rw [X.basicOpen_res]
  ext1
  refine Set.image_preimage_eq_inter_range.trans ?_
  simp
/-
**AlgebraicGeometry.isRetrocompact_basicOpen** 是 Mathlib 中的一个引理，位于命名空间 `Algebrai
cGeometry`。
形式化陈述：isRetrocompact_basicOpen (s : Γ(X, ⊤)) : IsRetrocompact (X
参数：s : Γ(X, ⊤)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `IsRetrocompact_iff_isSpectralMap_subtypeVal`：IsRetrocompact_iff_isSpectr
alMap_subtypeVal : IsRetrocompact s ↔ IsSpectralMap (Subtype.val : s -> X)
· 使用定理 `AlgebraicGeometry.Scheme.Hom.isSpectralMap`：∀ {X Y : AlgebraicGeometry.S
cheme} (f : X ⟶ Y) [AlgebraicGeometry.QuasiCompact f], IsSpectralMap ⇑f
· 使用定理 `AlgebraicGeometry.instQuasiCompactOfIsAffineHom`：∀ {X Y : AlgebraicGeome
try.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.IsAffineHom f], AlgebraicGeometry.Qua
siCompact f
· 使用定理 `AlgebraicGeometry.instIsAffineHomιBasicOpen`：∀ {X : AlgebraicGeometry.Sc
heme} (r : ↑(X.presheaf.obj (Opposite.op ⊤))),   AlgebraicGeometry.IsAffineHom (
X.basicOpen r).ι
-/
lemma isRetrocompact_basicOpen (s : Γ(X, ⊤)) : IsRetrocompact (X := X) (X.basicOpen s) :=
  IsRetrocompact_iff_isSpectralMap_subtypeVal.mpr (X.basicOpen s).ι.isSpectralMap

/-- Superseded by `isAffine_of_isAffineOpen_basicOpen`. -/
/-
**AlgebraicGeometry.isAffine_of_isAffineOpen_basicOpen_aux** 是 Mathlib 中的一个引理，位于
命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Superseded by `isAffine_of_isAffineOpen_basicOpen`.
-/
private lemma isAffine_of_isAffineOpen_basicOpen_aux (s : Set Γ(X, ⊤))
    (hs : Ideal.span s = ⊤) (hs₂ : ∀ i ∈ s, IsAffineOpen (X.basicOpen i)) :
    QuasiSeparatedSpace X := by
  rw [quasiSeparatedSpace_iff_forall_affineOpens]
  intro U V
  obtain ⟨s', hs', e⟩ := (Ideal.span_eq_top_iff_finite _).mp hs
  rw [← Set.inter_univ (_ ∩ _), ← Opens.coe_top, ← iSup_basicOpen_of_span_eq_top _ _ e,
    ← iSup_subtype'', Opens.coe_iSup, Set.inter_iUnion]
  apply isCompact_iUnion
  intro i
  rw [Set.inter_inter_distrib_right]
  refine (hs₂ i (hs' i.2)).isQuasiSeparated _ _ Set.inter_subset_right
    (U.1.2.inter (X.basicOpen _).2) ?_ Set.inter_subset_right (V.1.2.inter (X.basicOpen _).2) ?_
  · rw [← Opens.coe_inf, ← X.basicOpen_res _ (homOfLE le_top).op]
    exact (U.2.basicOpen _).isCompact
  · rw [← Opens.coe_inf, ← X.basicOpen_res _ (homOfLE le_top).op]
    exact (V.2.basicOpen _).isCompact

set_option backward.isDefEq.respectTransparency false in
@[stacks 01QF]
/-
**AlgebraicGeometry.isAffine_of_isAffineOpen_basicOpen** 是 Mathlib 中的一个引理，位于命名空间
 `AlgebraicGeometry`。
形式化陈述：isAffine_of_isAffineOpen_basicOpen (s : Set Γ(X, ⊤)) (hs : Ideal.span s = 
⊤) (hs₂ : forall i in s, IsAffineOpen (X.basicOpen i)) : IsAffine X
参数：s : Set Γ(X, ⊤)；hs : Ideal.span s = ⊤；hs₂ : forall i in s, IsAffineOpen (X.ba
sicOpen i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.AlgebraicGeometry.Morphisms.Affine.0.AlgebraicGeometry.
isAffine_of_isAffineOpen_basicOpen_aux`：∀ {X : AlgebraicGeometry.Scheme} (s : Se
t ↑(X.presheaf.obj (Opposite.op ⊤))),   Ideal.span s = ⊤ → (∀ i ∈ s, AlgebraicGe
ometry.IsAffineOpen …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.span_eq_top_iff_finite`：span_eq_top_iff_finite (s : Set α) : span 
s = ⊤ ↔ exists s' : Finset α, ↑s' subseteq s ∧ span (s' : Set α) = ⊤
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isCompact_univ_iff`：isCompact_univ_iff : IsCompact (univ : Set X) ↔ Comp
actSpace X
· 使用定理 `TopologicalSpace.Opens.coe_top`：coe_top : ((⊤ : Opens α) : Set α) = Set.
univ
· 使用引理 `AlgebraicGeometry.iSup_basicOpen_of_span_eq_top`：iSup_basicOpen_of_span_
eq_top {X : Scheme} (U) (s : Set Γ(X, U)) (hs : Ideal.span s = ⊤) : (⨆ i in s, X
.basicOpen i) = U
· 使用定理 `isOpen_iUnion`：isOpen_iUnion {f : ι -> Set X} (h : forall i, IsOpen (f i
)) : IsOpen (⋃ i, f i)
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `TopologicalSpace.Opens.iSup_mk`：iSup_mk {ι} (s : ι -> Set α) (h : forall
 i, IsOpen (s i)) : (⨆ i, ⟨s i, h i⟩ : Opens α) = ⟨⋃ i, s i, isOpen_iUnion h⟩
· 使用定理 `TopologicalSpace.Opens.mk.congr_simp`：∀ {α : Type u_2} [inst : Topologic
alSpace α] (carrier carrier_1 : Set α) (e_carrier : carrier = carrier_1)   (is_o
pen' : IsOpen carrier), { …
· 使用定理 `Finset.isCompact_biUnion`：Finset.isCompact_biUnion (s : Finset ι) {f : ι
 -> Set X} (hf : forall i in s, IsCompact (f i)) : IsCompact (⋃ i in s, f i)
· 使用定理 `AlgebraicGeometry.IsAffineOpen.isCompact`：∀ {X : AlgebraicGeometry.Schem
e} {U : X.Opens}, AlgebraicGeometry.IsAffineOpen U → IsCompact ↑U
· 使用定理 `AlgebraicGeometry.HasAffineProperty.of_iSup_eq_top`：∀ {P : CategoryTheor
y.MorphismProperty AlgebraicGeometry.Scheme} {Q : AlgebraicGeometry.AffineTarget
MorphismProperty}   [AlgebraicGeometry.H…
· 使用定理 `AlgebraicGeometry.instHasAffinePropertyIsomorphismsSchemeAndIsAffineIsIs
oCommRingCatAppTop`：AlgebraicGeometry.HasAffineProperty (CategoryTheory.Morphism
Property.isomorphisms AlgebraicGeometry.Scheme)   fun X x f x_1 => AlgebraicGeom
…
· 使用定理 `AlgebraicGeometry.IsAffineOpen.basicOpen`：basicOpen : IsAffineOpen (X.ba
sicOpen f)
· 使用定理 `AlgebraicGeometry.isAffineOpen_top`：isAffineOpen_top (X : Scheme) [IsAff
ine X] : IsAffineOpen (⊤ : X.Opens)
· 使用定理 `AlgebraicGeometry.instIsAffineObjOppositeCommRingCatSchemeSpec`：∀ (R : C
ommRingCatᵒᵖ), AlgebraicGeometry.IsAffine (AlgebraicGeometry.Scheme.Spec.obj R)
· 使用引理 `PrimeSpectrum.iSup_basicOpen_eq_top_iff`：iSup_basicOpen_eq_top_iff {ι : 
Type*} {f : ι -> R} : (⨆ i : ι, PrimeSpectrum.basicOpen (f i)) = ⊤ ↔ Ideal.span 
(Set.range f) = ⊤
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `Set.ofPred_mem_eq`：∀ {α : Type u} {s : Set α}, {x | x ∈ s} = s
· 使用定理 `AlgebraicGeometry.Scheme.toSpecΓ_preimage_basicOpen`：∀ (X : AlgebraicGeo
metry.Scheme) (r : ↑(X.presheaf.obj (Opposite.op ⊤))),   (TopologicalSpace.Opens
.map X.toSpecΓ.base).obj (PrimeSpectrum.b…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι`：∀ {X : AlgebraicGeo
metry.Scheme} (U : X.Opens), AlgebraicGeometry.IsOpenImmersion U.ι
（共 41 条，此处仅展示前 30 条）
-/
lemma isAffine_of_isAffineOpen_basicOpen (s : Set Γ(X, ⊤))
    (hs : Ideal.span s = ⊤) (hs₂ : ∀ i ∈ s, IsAffineOpen (X.basicOpen i)) :
    IsAffine X := by
  have : QuasiSeparatedSpace X := isAffine_of_isAffineOpen_basicOpen_aux s hs hs₂
  have : CompactSpace X := by
    obtain ⟨s', hs', e⟩ := (Ideal.span_eq_top_iff_finite _).mp hs
    rw [← isCompact_univ_iff, ← Opens.coe_top, ← iSup_basicOpen_of_span_eq_top _ _ e]
    simp only [Finset.mem_coe, Opens.iSup_mk, Opens.carrier_eq_coe, Opens.coe_mk]
    apply s'.isCompact_biUnion
    exact fun i hi ↦ (hs₂ _ (hs' hi)).isCompact
  constructor
  refine HasAffineProperty.of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme)
    (fun i : s ↦ ⟨PrimeSpectrum.basicOpen i.1, ?_⟩) ?_ (fun i ↦ ⟨?_, ?_⟩)
  · change IsAffineOpen _
    simp only [← basicOpen_eq_of_affine]
    exact (isAffineOpen_top (Scheme.Spec.obj (op _))).basicOpen _
  · rw [PrimeSpectrum.iSup_basicOpen_eq_top_iff, Subtype.range_coe_subtype, Set.ofPred_mem_eq, hs]
  · rw [Scheme.toSpecΓ_preimage_basicOpen]
    exact hs₂ _ i.2
  · simp only [Opens.map_top, morphismRestrict_app]
    refine IsIso.comp_isIso' ?_ inferInstance
    convert! isIso_ΓSpec_adjunction_unit_app_basicOpen i.1 using 0
    exact congr(IsIso ((ΓSpec.adjunction.unit.app X).app $(by simp)))

set_option backward.isDefEq.respectTransparency false in
/--
If `s` is a spanning set of `Γ(X, U)`, such that each `X.basicOpen i` is affine, then `U` is also
affine.
-/
/-
**AlgebraicGeometry.isAffineOpen_of_isAffineOpen_basicOpen** 是 Mathlib 中的一个引理，位于
命名空间 `AlgebraicGeometry`。
形式化陈述：isAffineOpen_of_isAffineOpen_basicOpen (U) (s : Set Γ(X, U)) (hs : Ideal.s
pan s = ⊤) (hs₂ : forall i in s, IsAffineOpen (X.basicOpen i)) : IsAffineOpen U
参数：U；s : Set Γ(X, U)；hs : Ideal.span s = ⊤；hs₂ : forall i in s, IsAffineOpen (X.
basicOpen i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.isAffine_of_isAffineOpen_basicOpen`：isAffine_of_isAffi
neOpen_basicOpen (s : Set Γ(X, ⊤)) (hs : Ideal.span s = ⊤) (hs₂ : forall i in s,
 IsAffineOpen (X.basicOpen i)) : IsAffine …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.map_span`：map_span (s : Set R) : map f (span s) = span (f '' s)
· 使用定理 `Ideal.map_top`：map_top : map f ⊤ = ⊤
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι`：∀ {X : AlgebraicGeo
metry.Scheme} (U : X.Opens), AlgebraicGeometry.IsOpenImmersion U.ι
· 使用定理 `AlgebraicGeometry.Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion`：∀ {X Y
 : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [H : AlgebraicGeometry.IsOpenImmersion 
f] {U : X.Opens},   AlgebraicGeometry.IsAffineOpen ((A…
· 使用定理 `AlgebraicGeometry.Scheme.image_basicOpen`：image_basicOpen {U : X.Opens} 
(r : Γ(X, U)) : f ''ᵁ X.basicOpen r = Y.basicOpen ((f.appIso U).inv r)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `AlgebraicGeometry.Scheme.Opens.ι_appIso`：ι_appIso (V) : U.ι.appIso V = I
so.refl _
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AlgebraicGeometry.Scheme.Opens.topIso_inv`：∀ {X : AlgebraicGeometry.Sche
me} (U : X.Opens), U.topIso.inv = X.presheaf.map (CategoryTheory.eqToHom ⋯).op
· 使用定理 `CategoryTheory.eqToHom_op`：eqToHom_op {X Y : C} (h : X = Y) : (eqToHom h
).op = eqToHom (congr_arg op h.symm)
· 使用定理 `RingHomCompTriple.comp_apply`：comp_apply [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]
 {x : R₁} : σ₂₃ (σ₁₂ x) = σ₁₃ x
· 使用定理 `AlgebraicGeometry.Scheme.basicOpen_res_eq`：basicOpen_res_eq (i : op U ⟶ 
op V) [IsIso i] : X.basicOpen (X.presheaf.map i f) = X.basicOpen f
· 使用定理 `CategoryTheory.instIsIsoEqToHom`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {X Y : C} (h : X = Y),   CategoryTheory.IsIso (CategoryTheo
ry.eqToHom h)

--- 原说明 ---
If `s` is a spanning set of `Γ(X, U)`, such that each `X.basicOpen i` is affine,
 then `U` is also
affine.
-/
lemma isAffineOpen_of_isAffineOpen_basicOpen (U) (s : Set Γ(X, U))
    (hs : Ideal.span s = ⊤) (hs₂ : ∀ i ∈ s, IsAffineOpen (X.basicOpen i)) :
    IsAffineOpen U := by
  apply isAffine_of_isAffineOpen_basicOpen (U.topIso.inv '' s)
  · rw [← Ideal.map_span U.topIso.inv.hom, hs, Ideal.map_top]
  · rintro _ ⟨j, hj, rfl⟩
    rw [← (Scheme.Opens.ι _).isAffineOpen_iff_of_isOpenImmersion, Scheme.image_basicOpen]
    simpa [Scheme.Opens.toScheme_presheaf_obj] using hs₂ j hj
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasAffineProperty @IsAffineHom fun X _ _ _ ↦ IsAffine X where
  isLocal_affineProperty := by
    constructor
    · apply AffineTargetMorphismProperty.respectsIso_mk
      · rintro X Y Z e _ _ H
        have : IsAffine _ := H
        exact .of_isIso e.hom
      · exact fun _ _ _ ↦ id
    · intro X Y _ f r H
      have : IsAffine X := H
      change IsAffineOpen _
      rw [Scheme.preimage_basicOpen]
      exact (isAffineOpen_top X).basicOpen _
    · intro X Y _ f S hS hS'
      apply_fun Ideal.map (f.appTop).hom at hS
      rw [Ideal.map_span, Ideal.map_top] at hS
      apply isAffine_of_isAffineOpen_basicOpen _ hS
      have : ∀ i : S, IsAffineOpen (f ⁻¹ᵁ Y.basicOpen i.1) := hS'
      simpa [Scheme.preimage_basicOpen] using! this
  eq_targetAffineLocally' := by
    ext X Y f
    simp only [targetAffineLocally, Scheme.affineOpens, Set.coe_ofPred, Set.mem_ofPred_eq,
      Subtype.forall, isAffineHom_iff]
    rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.isAffineHom_isStableUnderBaseChange** 是 Mathlib 中的一个实例，位于命名空
间 `AlgebraicGeometry`。
形式化陈述：isAffineHom_isStableUnderBaseChange : MorphismProperty.IsStableUnderBaseCh
ange @IsAffineHom
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.HasAffineProperty.isStableUnderBaseChange`：∀ {P : Cate
goryTheory.MorphismProperty AlgebraicGeometry.Scheme} {Q : AlgebraicGeometry.Aff
ineTargetMorphismProperty}   [AlgebraicGeometry.H…
· 使用定理 `AlgebraicGeometry.instHasAffinePropertyIsAffineHomIsAffine`：AlgebraicGeo
metry.HasAffineProperty @AlgebraicGeometry.IsAffineHom fun X x x_1 x_2 => Algebr
aicGeometry.IsAffine X
· 使用定理 `AlgebraicGeometry.HasAffineProperty.isLocal_affineProperty`：∀ (P : Categ
oryTheory.MorphismProperty AlgebraicGeometry.Scheme)   {Q : outParam AlgebraicGe
ometry.AffineTargetMorphismProperty} [self : Alg…
· 使用定理 `AlgebraicGeometry.AffineTargetMorphismProperty.IsStableUnderBaseChange.m
k`：∀ (P : AlgebraicGeometry.AffineTargetMorphismProperty) [P.toProperty.Respects
Iso],   (∀ ⦃X Y S : AlgebraicGeometry.Scheme⦄ [inst : Algebraic…
· 使用定理 `AlgebraicGeometry.AffineTargetMorphismProperty.IsLocal.respectsIso`：∀ {P
 : AlgebraicGeometry.AffineTargetMorphismProperty} [self : P.IsLocal], P.toPrope
rty.RespectsIso
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
-/
instance isAffineHom_isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange @IsAffineHom := by
  apply HasAffineProperty.isStableUnderBaseChange
  let := HasAffineProperty.isLocal_affineProperty
  apply AffineTargetMorphismProperty.IsStableUnderBaseChange.mk
  introv X hX H
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) isAffineHom_of_isAffine [IsAffine X] [IsAffine Y] : IsAffineHom f :=
  (HasAffineProperty.iff_of_isAffine (P := @IsAffineHom)).mpr inferInstance

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.isAffine_of_isAffineHom** 是 Mathlib 中的一个引理，位于命名空间 `Algebraic
Geometry`。
形式化陈述：isAffine_of_isAffineHom [IsAffineHom f] [IsAffine Y] : IsAffine X
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AlgebraicGeometry.HasAffineProperty.iff_of_isAffine`：∀ {P : CategoryTheo
ry.MorphismProperty AlgebraicGeometry.Scheme} {Q : AlgebraicGeometry.AffineTarge
tMorphismProperty}   [AlgebraicGeometry.H…
· 使用定理 `AlgebraicGeometry.instHasAffinePropertyIsAffineHomIsAffine`：AlgebraicGeo
metry.HasAffineProperty @AlgebraicGeometry.IsAffineHom fun X x x_1 x_2 => Algebr
aicGeometry.IsAffine X
-/
lemma isAffine_of_isAffineHom [IsAffineHom f] [IsAffine Y] : IsAffine X :=
  (HasAffineProperty.iff_of_isAffine (P := @IsAffineHom) (f := f)).mp inferInstance

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.isAffineHom_of_forall_exists_isAffineOpen** 是 Mathlib 中的一个引理
，位于命名空间 `AlgebraicGeometry`。
形式化陈述：isAffineHom_of_forall_exists_isAffineOpen (H : forall x : Y, exists U : Y.
Opens, x in U ∧ IsAffineOpen U ∧ IsAffineOpen (f ⁻¹ᵁ U)) : IsAffineHom f
参数：H : forall x : Y, exists U : Y.Opens, x in U ∧ IsAffineOpen U ∧ IsAffineOpen 
(f ⁻¹ᵁ U)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.HasAffineProperty.iff_of_iSup_eq_top`：∀ {P : CategoryT
heory.MorphismProperty AlgebraicGeometry.Scheme} {Q : AlgebraicGeometry.AffineTa
rgetMorphismProperty}   [AlgebraicGeometry.H…
· 使用定理 `AlgebraicGeometry.instHasAffinePropertyIsAffineHomIsAffine`：AlgebraicGeo
metry.HasAffineProperty @AlgebraicGeometry.IsAffineHom fun X x x_1 x_2 => Algebr
aicGeometry.IsAffine X
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `top_le_iff`：top_le_iff : ⊤ <= a ↔ a = ⊤
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
lemma isAffineHom_of_forall_exists_isAffineOpen
    (H : ∀ x : Y, ∃ U : Y.Opens, x ∈ U ∧ IsAffineOpen U ∧ IsAffineOpen (f ⁻¹ᵁ U)) :
    IsAffineHom f := by
  choose U hxU hU hfU using H
  rw [HasAffineProperty.iff_of_iSup_eq_top (P := @IsAffineHom) fun i ↦ ⟨U i, hU i⟩]
  · exact hfU
  · exact top_le_iff.mp (fun x _ ↦ by simpa using ⟨x, hxU x⟩)

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [IsAffineHom f] [IsAffine Y] :
    IsAffine (pullback f g) :=
  letI : IsAffineHom (pullback.snd f g) := MorphismProperty.pullback_snd _ _ ‹_›
  isAffine_of_isAffineHom (pullback.snd f g)

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [IsAffineHom g] [IsAffine X] :
    IsAffine (pullback f g) :=
  letI : IsAffineHom (pullback.fst f g) := MorphismProperty.pullback_fst _ _ ‹_›
  isAffine_of_isAffineHom (pullback.fst f g)
/-
**AlgebraicGeometry.IsAffine.of_isPullback** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicG
eometry.IsAffine`。
形式化陈述：∀ {X Y Z P : AlgebraicGeometry.Scheme} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X 
⟶ Z} {g : Y ⟶ Z}   [AlgebraicGeometry.IsAffine X] [AlgebraicGeometry.IsAffineHom
 g],   CategoryTheory.IsPullback fst snd f g → AlgebraicGeometry.IsAffine P
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.IsAffine.of_isIso`：∀ {X Y : AlgebraicGeometry.Scheme} 
(f : X ⟶ Y) [CategoryTheory.IsIso f] [h : AlgebraicGeometry.IsAffine Y],   Algeb
raicGeometry.IsAffine X
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `AlgebraicGeometry.instIsAffinePullbackSchemeOfIsAffineHom_1`：∀ {X Y S : 
AlgebraicGeometry.Scheme} (f : X ⟶ S) (g : Y ⟶ S) [AlgebraicGeometry.IsAffineHom
 g]   [AlgebraicGeometry.IsAffine X], AlgebraicGe…
-/
lemma IsAffine.of_isPullback {P : Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    [IsAffine X] [IsAffineHom g] (h : IsPullback fst snd f g) :
    IsAffine P :=
  .of_isIso h.isoPullback.hom
/-
**AlgebraicGeometry.isPushout_appTop_of_isPullback** 是 Mathlib 中的一个引理，位于命名空间 `Al
gebraicGeometry`。
形式化陈述：isPushout_appTop_of_isPullback {P : Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ Y
} {f : X ⟶ Z} {g : Y ⟶ Z} [IsAffine X] [IsAffine Y] [IsAffine Z] (h : IsPullback
 fst snd f g) : IsPushout f.appTop g.appTop fst.appTop snd.appTop
参数：h : IsPullback fst snd f g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.IsAffine.of_isPullback`：∀ {X Y Z P : AlgebraicGeometry
.Scheme} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}   [AlgebraicGeometr
y.IsAffine X] [AlgebraicGeomet…
· 使用定理 `AlgebraicGeometry.isAffineHom_of_isAffine`：∀ {X Y : AlgebraicGeometry.Sc
heme} (f : X ⟶ Y) [AlgebraicGeometry.IsAffine X] [AlgebraicGeometry.IsAffine Y],
   AlgebraicGeometry.IsAffineHo…
· 使用定理 `CategoryTheory.IsPullback.of_map_of_faithful`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Categor
y.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.CreatesLimit.toReflectsLimit`：∀ {C : Type u₁} {inst : Cat
egoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Category
.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.IsPushout.flip`：flip (h : IsPushout f g inl inr) : IsPush
out g f inr inl
· 使用定理 `CategoryTheory.IsPullback.unop`：unop {P X Y Z : Cᵒᵖ} {fst : P ⟶ X} {snd 
: P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g) : IsPushout g.unop
 f.unop snd.unop fst…
· 使用定理 `CategoryTheory.IsPullback.map`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (F : CategoryTheor…
· 使用定理 `CategoryTheory.preservesLimit_of_createsLimit_and_hasLimit`：∀ {C : Type 
u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Category
Theory.Category.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `AlgebraicGeometry.AffineScheme.instIsEquivalenceOppositeCommRingCatRight
OpΓ`：AlgebraicGeometry.AffineScheme.Γ.rightOp.IsEquivalence
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePushouts_of_has_finite_limits`：∀ (C :
 Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFin
iteColimits C],   CategoryTheory.Limits.HasFiniteWideP…
· 使用定理 `CategoryTheory.Limits.hasFiniteColimits_of_hasColimits`：∀ (C : Type u) [
inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasColimits C], 
  CategoryTheory.Limits.HasFiniteColimits C
-/
lemma isPushout_appTop_of_isPullback {P : Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z}
    {g : Y ⟶ Z} [IsAffine X] [IsAffine Y] [IsAffine Z] (h : IsPullback fst snd f g) :
    IsPushout f.appTop g.appTop fst.appTop snd.appTop := by
  have : IsAffine P := .of_isPullback h
  have : IsPullback (AffineScheme.ofHom fst) (AffineScheme.ofHom snd) (AffineScheme.ofHom f)
      (AffineScheme.ofHom g) :=
    IsPullback.of_map_of_faithful AffineScheme.forgetToScheme.{u} h
  exact (IsPullback.map AffineScheme.Γ.rightOp this).unop.flip

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {U V X : Scheme.{u}} (f : U ⟶ X) (g : V ⟶ X) [IsAffineHom f] [IsAffineHom g] :
    IsAffineHom (coprod.desc f g) := by
  refine ⟨fun W hW ↦ ?_⟩
  have : IsAffine (f ⁻¹ᵁ W).toScheme := hW.preimage f
  have : IsAffine (g ⁻¹ᵁ W).toScheme := hW.preimage g
  let i : (f ⁻¹ᵁ W).toScheme ⨿ (g ⁻¹ᵁ W).toScheme ⟶ U ⨿ V := coprod.map (f ⁻¹ᵁ W).ι (g ⁻¹ᵁ W).ι
  convert! isAffineOpen_opensRange i
  apply le_antisymm
  · intro x hx
    obtain ⟨(x | x), rfl⟩ := (coprodMk U V).surjective x
    · replace hx : f x ∈ W := by simpa [← Scheme.Hom.comp_apply] using hx
      exact ⟨coprodMk _ _ (.inl ⟨x, hx⟩), by simp [i, ← Scheme.Hom.comp_apply]⟩
    · replace hx : g x ∈ W := by simpa [← Scheme.Hom.comp_apply] using hx
      exact ⟨coprodMk _ _ (.inr ⟨x, hx⟩), by simp [i, ← Scheme.Hom.comp_apply]⟩
  · rintro _ ⟨x, rfl⟩
    obtain ⟨(⟨x, hx⟩ | ⟨x, hx⟩), rfl⟩ := (coprodMk _ _).surjective x
    · simpa [← Scheme.Hom.comp_apply, i] using hx
    · simpa [← Scheme.Hom.comp_apply, i] using hx

/-- If the underlying map of a morphism is inducing and has closed range, then it is affine. -/
@[stacks 04DE]
/-
**AlgebraicGeometry.isAffineHom_of_isInducing** 是 Mathlib 中的一个引理，位于命名空间 `Algebra
icGeometry`。
形式化陈述：isAffineHom_of_isInducing (hf₁ : Topology.IsInducing f) (hf₂ : IsClosed (S
et.range f)) : IsAffineHom f
参数：hf₁ : Topology.IsInducing f；hf₂ : IsClosed (Set.range f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.isAffineHom_of_forall_exists_isAffineOpen`：isAffineHom
_of_forall_exists_isAffineOpen (H : forall x : Y, exists U : Y.Opens, x in U ∧ I
sAffineOpen U ∧ IsAffineOpen (f ⁻¹ᵁ U)) : IsAffin…
· 使用定理 `TopologicalSpace.IsTopologicalBasis.exists_subset_of_mem_open`：∀ {α : Ty
pe u} [t : TopologicalSpace α] {b : Set (Set α)},   TopologicalSpace.IsTopologic
alBasis b → ∀ {a : α} {u : Set α}, a ∈ u → IsOpen u…
· 使用定理 `AlgebraicGeometry.Scheme.isBasis_affineOpens`：∀ (X : AlgebraicGeometry.S
cheme), TopologicalSpace.Opens.IsBasis X.affineOpens
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `isOpen_univ`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen Set.univ
· 使用定理 `TopologicalSpace.Opens.isOpen`：∀ {α : Type u_2} [inst : TopologicalSpace
 α] (U : TopologicalSpace.Opens α), IsOpen ↑U
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Topology.IsInducing.isOpen_iff`：isOpen_iff (hf : IsInducing f) {s : Set 
X} : IsOpen s ↔ exists t, IsOpen t ∧ f ⁻¹' t = s
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
· 使用定理 `TopologicalSpace.Opens.ext`：ext {U V : Opens α} (h : (U : Set α) = V) : 
U = V
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.IsAffineOpen.exists_basicOpen_le`：exists_basicOpen_le 
{V : X.Opens} (x : V) (h : ↑x in U) : exists f : Γ(X, U), X.basicOpen f <= V ∧ ↑
x in X.basicOpen f
· 使用定理 `AlgebraicGeometry.IsAffineOpen.basicOpen`：basicOpen : IsAffineOpen (X.ba
sicOpen f)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `AlgebraicGeometry.Scheme.preimage_basicOpen`：preimage_basicOpen {X Y : S
cheme.{u}} (f : X ⟶ Y) {U : Y.Opens} (r : Γ(Y, U)) : f ⁻¹ᵁ Y.basicOpen r = X.bas
icOpen (f.app U r)
· 使用引理 `AlgebraicGeometry.Scheme.Hom.naturality`：naturality (i : op U' ⟶ op U) :
 Y.presheaf.map i ≫ f.app U = f.app U' ≫ X.presheaf.map ((Opens.map f.base).map 
i.unop).op
· 使用定理 `AlgebraicGeometry.Scheme.basicOpen_res`：basicOpen_res (i : op U ⟶ op V) 
: X.basicOpen (X.presheaf.map i f) = V ⊓ X.basicOpen f
· 使用定理 `IsClosed.isOpen_compl`：∀ {X : Type u} {inst : TopologicalSpace X} {s : S
et X} [self : IsClosed s], IsOpen sᶜ
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Set.preimage_eq_empty_iff`：preimage_eq_empty_iff {s : Set β} : f ⁻¹' s =
 ∅ ↔ Disjoint s (range f)
· 使用引理 `Set.subset_compl_iff_disjoint_right`：subset_compl_iff_disjoint_right : s
 subseteq tᶜ ↔ Disjoint s t
· 使用定理 `AlgebraicGeometry.isAffineOpen_bot`：isAffineOpen_bot (X : Scheme) : IsAf
fineOpen (⊥ : X.Opens)

--- 原说明 ---
If the underlying map of a morphism is inducing and has closed range, then it is
 affine.
-/
lemma isAffineHom_of_isInducing
    (hf₁ : Topology.IsInducing f)
    (hf₂ : IsClosed (Set.range f)) :
    IsAffineHom f := by
  apply isAffineHom_of_forall_exists_isAffineOpen
  intro y
  by_cases hy : y ∈ Set.range f
  · obtain ⟨x, rfl⟩ := hy
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hxU (f ⁻¹ᵁ U).isOpen
    obtain ⟨U', hU'U, rfl⟩ : ∃ U' : Y.Opens, U' ≤ U ∧ f ⁻¹ᵁ U' = V := by
      obtain ⟨U', hU', e⟩ := hf₁.isOpen_iff.mp V.2
      exact ⟨⟨U', hU'⟩ ⊓ U, inf_le_right, Opens.ext (by simpa [e] using hVU)⟩
    obtain ⟨r, hrU', hxr⟩ := hU.exists_basicOpen_le ⟨f x, hxV⟩ hxU
    refine ⟨_, hxr, hU.basicOpen r, ?_⟩
    convert hV.basicOpen (f.app _ (Y.presheaf.map (homOfLE hU'U).op r))
    simp only [Scheme.preimage_basicOpen, ← CommRingCat.comp_apply, f.naturality]
    simpa using ((Opens.map f.base).map (homOfLE hrU')).le
  · obtain ⟨_, ⟨U, hU, rfl⟩, hyU, hU'⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open hy hf₂.isOpen_compl
    rw [Set.subset_compl_iff_disjoint_right, ← Set.preimage_eq_empty_iff] at hU'
    refine ⟨U, hyU, hU, ?_⟩
    convert isAffineOpen_bot _
    exact Opens.ext hU'
/-
**AlgebraicGeometry.IsAffineOpen.isCompact_pullback_inf** 是 Mathlib 中的一个定理，位于命名空
间 `AlgebraicGeometry.IsAffineOpen`。
形式化陈述：∀ {X Y Z : AlgebraicGeometry.Scheme} {f : X ⟶ Z} {g : Y ⟶ Z} {U : X.Opens}
,   AlgebraicGeometry.IsAffineOpen U →     ∀ {V : Y.Opens},       IsCompact ↑V →
         ∀ {W : Z.Opens},           AlgebraicGeometry.IsAffineOpen W →          
   U ≤ (TopologicalSpace.Opens.map f.base).obj W →               V ≤ (Topologica
lSpace.Opens.map g.base).obj W →                 IsCompact                   (↑(
(TopologicalSpace.Opens.map (CategoryTheory.Limits.pullback.fst f g).base).obj U
) ⊓                     ↑((TopologicalSpace.Opens.map (CategoryTheory.Limits.pul
lback.snd f g).base).obj V))
参数：TopologicalSpace.Opens.map f.base；TopologicalSpace.Opens.map g.base；↑((Topolo
gicalSpace.Opens.map (CategoryTheory.Limits.pullback.fst f g).base).obj U) ⊓    
                 ↑((TopologicalSpace.Opens.map (CategoryTheory.Limits.pullback.s
nd f g).base).obj V)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isCompact_iff_compactSpace`：isCompact_iff_compactSpace : IsCompact s ↔ C
ompactSpace s
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι`：∀ {X : AlgebraicGeo
metry.Scheme} (U : X.Opens), AlgebraicGeometry.IsOpenImmersion U.ι
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用引理 `AlgebraicGeometry.Scheme.Opens.range_ι`：range_ι : Set.range U.ι = U
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `AlgebraicGeometry.Scheme.Hom.resLE_comp_ι`：resLE_comp_ι : f.resLE U V e 
≫ U.ι = V.ι ≫ f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.lift_fac`：lift_fac (H' : Set.range g s
ubseteq Set.range f) : lift f g H' ≫ f = g
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `AlgebraicGeometry.Scheme.Pullback.range_map`：range_map {X' Y' S' : Schem
e.{u}} (f' : X' ⟶ S') (g' : Y' ⟶ S') (i₁ : X ⟶ X') (i₂ : Y ⟶ Y') (i₃ : S ⟶ S') (
e₁ : f ≫ i₃ = i₁ ≫ f') (e₂ : g ≫ …
· 使用定理 `isCompact_range`：isCompact_range [CompactSpace X] {f : X -> Y} (hf : Con
tinuous f) : IsCompact (range f)
· 使用定理 `AlgebraicGeometry.instCompactSpaceCarrierCarrierCommRingCatPullbackSchem
eOfQuasiCompact_1`：∀ {X Y Z : AlgebraicGeometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z) 
[AlgebraicGeometry.QuasiCompact g] [CompactSpace ↥X],   CompactSpace ↥(Category…
· 使用定理 `AlgebraicGeometry.quasiCompact_of_compactSpace`：∀ {X Y : AlgebraicGeomet
ry.Scheme} (f : X ⟶ Y) [CompactSpace ↥X] [QuasiSeparatedSpace ↥Y],   AlgebraicGe
ometry.QuasiCompact f
· 使用定理 `AlgebraicGeometry.Scheme.compactSpace_of_isAffine`：∀ (X : AlgebraicGeome
try.Scheme) [AlgebraicGeometry.IsAffine X], CompactSpace ↥X
· 使用定理 `AlgebraicGeometry.Scheme.Hom.continuous`：∀ {X Y : AlgebraicGeometry.Sche
me} (f : X ⟶ Y), Continuous ⇑f
-/
lemma IsAffineOpen.isCompact_pullback_inf {X Y Z : Scheme.{u}} {f : X ⟶ Z} {g : Y ⟶ Z}
    {U : X.Opens} (hU : IsAffineOpen U) {V : Y.Opens} (hV : IsCompact (V : Set Y))
    {W : Z.Opens} (hW : IsAffineOpen W) (hUW : U ≤ f ⁻¹ᵁ W) (hVW : V ≤ g ⁻¹ᵁ W) :
    IsCompact (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V : Set ↑(pullback f g)) := by
  have : IsAffine U.toScheme := hU
  have : IsAffine W.toScheme := hW
  have : CompactSpace V := isCompact_iff_compactSpace.mp hV
  let f' : U.toScheme ⟶ W := f.resLE _ _ hUW
  let q : Scheme.Opens.toScheme V ⟶ W :=
    IsOpenImmersion.lift W.ι (Scheme.Opens.ι _ ≫ g) <| by simpa [Set.range_comp]
  let p : pullback f' q ⟶ pullback f g :=
    pullback.map _ _ _ _ U.ι (Scheme.Opens.ι _) W.ι (by simp [f']) (by simp [q])
  convert! isCompact_range p.continuous
  simp [p, Scheme.Pullback.range_map]

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.isIso_morphismRestrict_iff_isIso_app** 是 Mathlib 中的一个引理，位于命名
空间 `AlgebraicGeometry`。
形式化陈述：isIso_morphismRestrict_iff_isIso_app [IsAffineHom f] {U : Y.Opens} (hU : I
sAffineOpen U) : IsIso (f ∣_ U) ↔ IsIso (f.app U)
参数：hU : IsAffineOpen U。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `AlgebraicGeometry.HasAffineProperty.iff_of_isAffine`：∀ {P : CategoryTheo
ry.MorphismProperty AlgebraicGeometry.Scheme} {Q : AlgebraicGeometry.AffineTarge
tMorphismProperty}   [AlgebraicGeometry.H…
· 使用定理 `AlgebraicGeometry.instHasAffinePropertyIsomorphismsSchemeAndIsAffineIsIs
oCommRingCatAppTop`：AlgebraicGeometry.HasAffineProperty (CategoryTheory.Morphism
Property.isomorphisms AlgebraicGeometry.Scheme)   fun X x f x_1 => AlgebraicGeom
…
· 使用定理 `and_iff_right`：∀ {a b : Prop}, a → (a ∧ b ↔ b)
· 使用定理 `AlgebraicGeometry.IsAffineOpen.preimage`：∀ {X Y : AlgebraicGeometry.Sche
me} {U : Y.Opens},   AlgebraicGeometry.IsAffineOpen U →     ∀ (f : X ⟶ Y) [Algeb
raicGeometry.IsAffineHom f], …
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.Scheme.Hom.app_eq_appLE`：app_eq_appLE {U : Y.Opens} : 
f.app U = f.appLE U _ le_rfl
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι`：∀ {X : AlgebraicGeo
metry.Scheme} (U : X.Opens), AlgebraicGeometry.IsOpenImmersion U.ι
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `AlgebraicGeometry.image_morphismRestrict_preimage`：image_morphismRestric
t_preimage {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (V : Opens U) : (f ⁻¹ᵁ U
).ι ''ᵁ ((f ∣_ U) ⁻¹ᵁ V) = f ⁻¹ᵁ (U.ι '…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AlgebraicGeometry.morphismRestrict_app'`：morphismRestrict_app' {X Y : Sc
heme.{u}} (f : X ⟶ Y) (U : Y.Opens) (V : Opens U) : (f ∣_ U).app V = f.appLE _ _
 (image_morphismRestrict_prei…
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `AlgebraicGeometry.Scheme.Hom.image_top_eq_opensRange`：image_top_eq_opens
Range : f ''ᵁ ⊤ = f.opensRange
· 使用引理 `AlgebraicGeometry.Scheme.Opens.opensRange_ι`：opensRange_ι : U.ι.opensRan
ge = U
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma isIso_morphismRestrict_iff_isIso_app [IsAffineHom f] {U : Y.Opens} (hU : IsAffineOpen U) :
    IsIso (f ∣_ U) ↔ IsIso (f.app U) := by
  have : IsAffine U := hU
  refine (HasAffineProperty.iff_of_isAffine (P := .isomorphisms _)).trans <|
    (and_iff_right (hU.preimage f)).trans ?_
  rw [Scheme.Hom.app_eq_appLE]
  simp only [morphismRestrict_app', TopologicalSpace.Opens.map_top]
  congr! <;> simp [Scheme.Opens.toScheme_presheaf_obj]

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.diagonal_isAffine_iff_forall_isAffineOpen_inf** 是 Mathlib 中的
一个定理，位于命名空间 `AlgebraicGeometry`。
形式化陈述：diagonal_isAffine_iff_forall_isAffineOpen_inf [IsAffine Y] (f : X ⟶ Y) : A
ffineTargetMorphismProperty.diagonal (fun X _ _ _ => IsAffine X) f ↔ forall (U V
 : X.Opens), IsAffineOpen U -> IsAffineOpen V -> IsAffineOpen (U ⊓ V)
参数：f : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
· 使用引理 `AlgebraicGeometry.IsOpenImmersion.isPullback`：isPullback {U V X Y : Sche
me.{u}} (g : U ⟶ V) (iU : U ⟶ X) (iV : V ⟶ Y) (f : X ⟶ Y) [IsOpenImmersion iU] [
IsOpenImmersion iV] (H : iU ≫ f = …
· 使用定理 `AlgebraicGeometry.instIsOpenImmersionHomOfLE`：∀ (X : AlgebraicGeometry.S
cheme) {U V : X.Opens} (e : U ≤ V), AlgebraicGeometry.IsOpenImmersion (X.homOfLE
 e)
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι`：∀ {X : AlgebraicGeo
metry.Scheme} (U : X.Opens), AlgebraicGeometry.IsOpenImmersion U.ι
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.homOfLE_ι`：∀ (X : AlgebraicGeometry.Scheme) {U 
V : X.Opens} (e : U ≤ V), CategoryTheory.CategoryStruct.comp (X.homOfLE e) V.ι =
 U.ι
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `TopologicalSpace.Opens.ext`：ext {U V : Opens α} (h : (U : Set α) = V) : 
U = V
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `AlgebraicGeometry.Scheme.Opens.opensRange_ι`：opensRange_ι : U.ι.opensRan
ge = U
· 使用定理 `AlgebraicGeometry.Scheme.opensRange_homOfLE`：∀ {X : AlgebraicGeometry.Sc
heme} {U V : X.Opens} (e : U ≤ V),   AlgebraicGeometry.Scheme.Hom.opensRange (X.
homOfLE e) = (TopologicalSpace.Op…
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `AlgebraicGeometry.IsAffine.of_isIso`：∀ {X Y : AlgebraicGeometry.Scheme} 
(f : X ⟶ Y) [CategoryTheory.IsIso f] [h : AlgebraicGeometry.IsAffine Y],   Algeb
raicGeometry.IsAffine X
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.comp`：∀ {X Y Z : AlgebraicGeometry.Sch
eme} (f : X ⟶ Y) (g : Y ⟶ Z) [AlgebraicGeometry.IsOpenImmersion f]   [AlgebraicG
eometry.IsOpenImmersion g], …
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.instFstScheme`：∀ {X Y Z : AlgebraicGeo
metry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z) [H : AlgebraicGeometry.IsOpenImmersion f],
   AlgebraicGeometry.IsOpenImmersion …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.range_pullback_to_base_of_left`：range_
pullback_to_base_of_left : Set.range (pullback.fst f g ≫ f) = Set.range f inter 
Set.range g
· 使用定理 `AlgebraicGeometry.isAffineOpen_opensRange`：isAffineOpen_opensRange {X Y 
: Scheme} [IsAffine X] (f : X ⟶ Y) [H : IsOpenImmersion f] : IsAffineOpen f.open
sRange
-/
theorem diagonal_isAffine_iff_forall_isAffineOpen_inf [IsAffine Y] (f : X ⟶ Y) :
    AffineTargetMorphismProperty.diagonal (fun X _ _ _ ↦ IsAffine X) f ↔
      ∀ (U V : X.Opens), IsAffineOpen U → IsAffineOpen V → IsAffineOpen (U ⊓ V) := by
  delta AffineTargetMorphismProperty.diagonal
  constructor
  · intro H U V hU hV
    dsimp at H
    have : IsAffine _ := hU
    have : IsAffine _ := hV
    let g : pullback U.ι V.ι ⟶ X := pullback.fst _ _ ≫ U.ι
    have := IsOpenImmersion.isPullback (X.homOfLE inf_le_left) (X.homOfLE inf_le_right)
      U.ι V.ι (by simp) (by ext; simp)
    exact .of_isIso this.isoPullback.hom
  · introv H h₁ h₂
    have : IsAffineOpen (pullback.fst f₁ f₂ ≫ f₁).opensRange := by
      convert! H _ _ (isAffineOpen_opensRange f₁) (isAffineOpen_opensRange f₂)
      exact Opens.ext (IsOpenImmersion.range_pullback_to_base_of_left _ _)
    change IsAffine _ at this
    exact .of_isIso (pullback.fst f₁ f₂ ≫ f₁).isoOpensRange.hom

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.isAffineHom_diagonal_iff** 是 Mathlib 中的一个定理，位于命名空间 `Algebrai
cGeometry`。
形式化陈述：isAffineHom_diagonal_iff {f : X ⟶ Y} : IsAffineHom (pullback.diagonal f) ↔
 forall (U : Y.Opens), IsAffineOpen U -> forall V₁ <= f ⁻¹ᵁ U, forall V₂ <= f ⁻¹
ᵁ U, IsAffineOpen V₁ -> IsAffineOpen V₂ -> IsAffineOpen (V₁ ⊓ V₂)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullbacks`：CategoryTheory.Limit
s.HasPullbacks AlgebraicGeometry.Scheme
· 使用定理 `Eq.to_iff`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.HasAffineProperty.eq_targetAffineLocally`：∀ (P : Categ
oryTheory.MorphismProperty AlgebraicGeometry.Scheme) {Q : AlgebraicGeometry.Affi
neTargetMorphismProperty}   [AlgebraicGeometry.H…
· 使用定理 `AlgebraicGeometry.instHasAffinePropertyDiagonalSchemeDiagonal`：∀ (P : Ca
tegoryTheory.MorphismProperty AlgebraicGeometry.Scheme) {Q : AlgebraicGeometry.A
ffineTargetMorphismProperty}   [AlgebraicGeometry.H…
· 使用定理 `AlgebraicGeometry.instHasAffinePropertyIsAffineHomIsAffine`：AlgebraicGeo
metry.HasAffineProperty @AlgebraicGeometry.IsAffineHom fun X x x_1 x_2 => Algebr
aicGeometry.IsAffine X
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AlgebraicGeometry.instIsAffineToSchemeValOpensMemSetAffineOpens`：∀ {Y : 
AlgebraicGeometry.Scheme} (U : ↑Y.affineOpens), AlgebraicGeometry.IsAffine ↑↑U
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι`：∀ {X : AlgebraicGeo
metry.Scheme} (U : X.Opens), AlgebraicGeometry.IsOpenImmersion U.ι
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion`：∀ {X Y
 : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [H : AlgebraicGeometry.IsOpenImmersion 
f] {U : X.Opens},   AlgebraicGeometry.IsAffineOpen ((A…
· 使用定理 `Equiv.forall_congr_left`：∀ {α : Sort u} {β : Sort v} {p : α → Prop} (e :
 α ≃ β), (∀ (a : α), p a) ↔ ∀ (b : β), p (e.symm b)
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.opensEquiv_symm_apply`：∀ {X Y : Algebr
aicGeometry.Scheme} (f : X ⟶ Y) [inst : AlgebraicGeometry.IsOpenImmersion f]   (
U : { U // U ≤ AlgebraicGeometry.Scheme.Hom.o…
· 使用引理 `AlgebraicGeometry.Scheme.Hom.image_preimage_eq_opensRange_inf`：image_pre
image_eq_opensRange_inf (U : Y.Opens) : f ''ᵁ f ⁻¹ᵁ U = f.opensRange ⊓ U
· 使用引理 `AlgebraicGeometry.Scheme.Opens.opensRange_ι`：opensRange_ι : U.ι.opensRan
ge = U
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `pi_congr`：∀ {α : Sort u} {β β' : α → Sort v}, (∀ (a : α), β a = β' a) → 
((a : α) → β a) = ((a : α) → β' a)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inf_eq_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
= b ↔ b ≤ a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isAffineHom_diagonal_iff {f : X ⟶ Y} :
    IsAffineHom (pullback.diagonal f) ↔
      ∀ (U : Y.Opens), IsAffineOpen U → ∀ V₁ ≤ f ⁻¹ᵁ U, ∀ V₂ ≤ f ⁻¹ᵁ U,
        IsAffineOpen V₁ → IsAffineOpen V₂ → IsAffineOpen (V₁ ⊓ V₂) := by
  refine congr($(HasAffineProperty.eq_targetAffineLocally
    (.diagonal @IsAffineHom)) f).to_iff.trans ?_
  simp only [targetAffineLocally, diagonal_isAffine_iff_forall_isAffineOpen_inf,
    (IsOpenImmersion.opensEquiv (f ⁻¹ᵁ _).ι).forall_congr_left, Scheme.affineOpens,
    Subtype.forall, Set.mem_ofPred_eq, Scheme.Opens.opensRange_ι, ← Scheme.Hom.preimage_inf,
    IsOpenImmersion.opensEquiv_symm_apply, Scheme.Hom.image_preimage_eq_opensRange_inf,
    ← Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion (Scheme.Opens.ι _)]
  congr! with U hU V₁ hV₁ V₂ hV₂
  rw [inf_eq_right.mpr hV₁, inf_eq_right.mpr hV₂, inf_eq_right.mpr (inf_le_left.trans hV₁)]

/-- If `X ⟶ Spec ℤ` has affine diagonal (in particular when `X` is separated), then intersections
of affine opens of `X` are also affine. -/
/-
**AlgebraicGeometry.IsAffineOpen.inf** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometr
y.IsAffineOpen`。
形式化陈述：∀ {X : AlgebraicGeometry.Scheme}   [AlgebraicGeometry.IsAffineHom (Categor
yTheory.Limits.pullback.diagonal (CategoryTheory.Limits.terminal.from X))]   {U 
V : X.Opens},   AlgebraicGeometry.IsAffineOpen U → AlgebraicGeometry.IsAffineOpe
n V → AlgebraicGeometry.IsAffineOpen (U ⊓ V)
参数：CategoryTheory.Limits.pullback.diagonal (CategoryTheory.Limits.terminal.from 
X)；U ⊓ V。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.instHasTerminalScheme`：CategoryTheory.Limits.HasTermin
al AlgebraicGeometry.Scheme
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AlgebraicGeometry.isAffineHom_diagonal_iff`：isAffineHom_diagonal_iff {f 
: X ⟶ Y} : IsAffineHom (pullback.diagonal f) ↔ forall (U : Y.Opens), IsAffineOpe
n U -> forall V₁ <= f ⁻¹ᵁ U, for…
· 使用定理 `AlgebraicGeometry.isAffineOpen_top`：isAffineOpen_top (X : Scheme) [IsAff
ine X] : IsAffineOpen (⊤ : X.Opens)
· 使用定理 `AlgebraicGeometry.instIsAffineTerminalScheme`：AlgebraicGeometry.IsAffine
 (⊤_ AlgebraicGeometry.Scheme)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p

--- 原说明 ---
If `X ⟶ Spec ℤ` has affine diagonal (in particular when `X` is separated), then 
intersections
of affine opens of `X` are also affine.
-/
lemma IsAffineOpen.inf [IsAffineHom (pullback.diagonal (terminal.from X))]
    {U V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) : IsAffineOpen (U ⊓ V) :=
  isAffineHom_diagonal_iff.mp ‹_› ⊤ (isAffineOpen_top _) U (by simp) V (by simp) hU hV
/-
**AlgebraicGeometry.IsAffineOpen.iInf** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeomet
ry.IsAffineOpen`。
形式化陈述：∀ {X : AlgebraicGeometry.Scheme}   [AlgebraicGeometry.IsAffineHom (Categor
yTheory.Limits.pullback.diagonal (CategoryTheory.Limits.terminal.from X))]   {ι 
: Sort u_1} [Finite ι] [Nonempty ι] {U : ι → X.Opens},   (∀ (i : ι), AlgebraicGe
ometry.IsAffineOpen (U i)) → AlgebraicGeometry.IsAffineOpen (⨅ i, U i)
参数：CategoryTheory.Limits.pullback.diagonal (CategoryTheory.Limits.terminal.from 
X)；∀ (i : ι), AlgebraicGeometry.IsAffineOpen (U i)；⨅ i, U i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.instHasTerminalScheme`：CategoryTheory.Limits.HasTermin
al AlgebraicGeometry.Scheme
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `InfClosed.iInf_mem_of_nonempty`：∀ {ι : Sort u_1} {α : Type u_3} [inst : 
ConditionallyCompleteLattice α] {f : ι → α} {s : Set α} [Finite ι] [Nonempty ι],
   InfClosed s → (∀ …
· 使用定理 `AlgebraicGeometry.IsAffineOpen.inf`：∀ {X : AlgebraicGeometry.Scheme}   [
AlgebraicGeometry.IsAffineHom (CategoryTheory.Limits.pullback.diagonal (Category
Theory.Limits.terminal.f…
-/
lemma IsAffineOpen.iInf [IsAffineHom (pullback.diagonal (terminal.from X))]
    {ι : Sort*} [Finite ι] [Nonempty ι] {U : ι → X.Opens} (hU : ∀ i, IsAffineOpen (U i)) :
      IsAffineOpen (⨅ i, U i) :=
  InfClosed.iInf_mem_of_nonempty (s := Set.ofPred IsAffineOpen) (fun _ h _ h' ↦ h.inf h') hU
/-
**AlgebraicGeometry.IsAffineOpen.biInf** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeome
try.IsAffineOpen`。
形式化陈述：∀ {X : AlgebraicGeometry.Scheme}   [AlgebraicGeometry.IsAffineHom (Categor
yTheory.Limits.pullback.diagonal (CategoryTheory.Limits.terminal.from X))]   {ι 
: Type u_1} (s : Set ι),   s.Finite →     s.Nonempty →       ∀ {U : ι → X.Opens}
,         (∀ i ∈ s, AlgebraicGeometry.IsAffineOpen (U i)) → AlgebraicGeometry.Is
AffineOpen (⨅ i ∈ s, U i)
参数：CategoryTheory.Limits.pullback.diagonal (CategoryTheory.Limits.terminal.from 
X)；s : Set ι；∀ i ∈ s, AlgebraicGeometry.IsAffineOpen (U i)；⨅ i ∈ s, U i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.instHasTerminalScheme`：CategoryTheory.Limits.HasTermin
al AlgebraicGeometry.Scheme
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `InfClosed.biInf_mem_of_nonempty`：∀ {α : Type u_3} [inst : CompleteLattic
e α] {s : Set α} {ι : Type u_5} {t : Set ι} {f : ι → α},   InfClosed s → t.Finit
e → t.Nonempty → (∀ i…
· 使用定理 `AlgebraicGeometry.IsAffineOpen.inf`：∀ {X : AlgebraicGeometry.Scheme}   [
AlgebraicGeometry.IsAffineHom (CategoryTheory.Limits.pullback.diagonal (Category
Theory.Limits.terminal.f…
-/
lemma IsAffineOpen.biInf [IsAffineHom (pullback.diagonal (terminal.from X))]
    {ι : Type*} (s : Set ι) (hs : s.Finite) (hs' : s.Nonempty) {U : ι → X.Opens}
    (hU : ∀ i ∈ s, IsAffineOpen (U i)) : IsAffineOpen (⨅ i ∈ s, U i) :=
  InfClosed.biInf_mem_of_nonempty (s := Set.ofPred IsAffineOpen) (fun _ h _ h' ↦ h.inf h') hs hs' hU

end AlgebraicGeometry

