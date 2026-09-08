/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.Cover.MorphismProperty

/-!
# Open covers of schemes

This file provides the basic API for open covers of schemes.

## Main definition
- `AlgebraicGeometry.Scheme.OpenCover`: The type of open covers of a scheme `X`,
  consisting of a family of open immersions into `X`,
  and for each `x : X` an open immersion (indexed by `f x`) that covers `x`.
- `AlgebraicGeometry.Scheme.affineCover`: `X.affineCover` is a choice of an affine cover of `X`.
- `AlgebraicGeometry.Scheme.AffineOpenCover`: The type of affine open covers of a scheme `X`.
-/

@[expose] public section


noncomputable section

open TopologicalSpace CategoryTheory Opposite CategoryTheory.Limits

universe v v₁ v₂ u

namespace AlgebraicGeometry

namespace Scheme

/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MorphismProperty.HasPullbacks IsOpenImmersion where
  hasPullback _ _ := inferInstance

/-- An open cover of a scheme `X` is a cover where all component maps are open immersions. -/
/-
**AlgebraicGeometry.Scheme.OpenCover** 是 Mathlib 中的一个缩写定义，位于命名空间 `AlgebraicGeome
try.Scheme`。
形式化陈述：OpenCover (X : Scheme.{u}) : Type _
参数：X : Scheme.{u}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An open cover of a scheme `X` is a cover where all component maps are open immer
sions.
-/
abbrev OpenCover (X : Scheme.{u}) : Type _ := Cover.{v} (precoverage @IsOpenImmersion) X

variable {X Y Z : Scheme.{u}} (𝒰 : OpenCover X) (f : X ⟶ Z) (g : Y ⟶ Z)
variable [∀ x, HasPullback (𝒰.f x ≫ f) g]
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (i : 𝒰.I₀) : IsOpenImmersion (𝒰.f i) := 𝒰.map_prop i
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {𝒱 : OpenCover X} (f : 𝒰 ⟶ 𝒱) (i : 𝒰.I₀) : IsOpenImmersion (f.h₀ i) :=
  have : IsOpenImmersion (f.h₀ i ≫ 𝒱.f (f.s₀ i)) := by rw [f.w₀]; infer_instance
  .of_comp _ (𝒱.f _)

set_option backward.isDefEq.respectTransparency false in
/-- The affine cover of a scheme. -/
/-
**AlgebraicGeometry.Scheme.affineCover** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeome
try.Scheme`。
形式化陈述：affineCover (X : Scheme.{u}) : OpenCover X
参数：X : Scheme.{u}。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.local_affine`：∀ (self : AlgebraicGeometry.Schem
e) (x : ↑self.toTopCat),   ∃ U R, Nonempty (self.restrict ⋯ ≅ AlgebraicGeometry.
Spec.toLocallyRingedSpace.o…

--- 原说明 ---
The affine cover of a scheme.
-/
def affineCover (X : Scheme.{u}) : OpenCover X := by
  choose U R h using X.local_affine
  let e (x) := (h x).some
  exact
  { I₀ := X
    X x := Spec (R x)
    f x := ⟨(e x).inv ≫ X.toLocallyRingedSpace.ofRestrict _⟩
    mem₀ := by
      rw [presieve₀_mem_precoverage_iff]
      refine ⟨fun x ↦ ⟨x, ⟨(e x).hom.base ⟨x, (U x).2⟩, ?_⟩⟩, inferInstance⟩
      change ((((e x).hom ≫ (e x).inv).base ≫ (X.ofRestrict _).base)) ⟨x, _⟩ = x
      cat_disch }
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited X.OpenCover :=
  ⟨X.affineCover⟩
/-
**AlgebraicGeometry.Scheme.OpenCover.iSup_opensRange** 是 Mathlib 中的一个定理，位于命名空间 `
AlgebraicGeometry.Scheme.OpenCover`。
形式化陈述：∀ {X : AlgebraicGeometry.Scheme} (𝒰 : X.OpenCover), ⨆ i, AlgebraicGeometry
.Scheme.Hom.opensRange (𝒰.f i) = ⊤
参数：𝒰 : X.OpenCover；𝒰.f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.Opens.ext`：ext {U V : Opens α} (h : (U : Set α) = V) : 
U = V
· 使用定理 `AlgebraicGeometry.Scheme.instIsOpenImmersionF`：∀ {X : AlgebraicGeometry.
Scheme} (𝒰 : X.OpenCover) (i : 𝒰.I₀), AlgebraicGeometry.IsOpenImmersion (𝒰.f i)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TopologicalSpace.Opens.coe_iSup`：coe_iSup {ι} (s : ι -> Opens α) : ((⨆ i
, s i : Opens α) : Set α) = ⋃ i, s i
· 使用定理 `AlgebraicGeometry.Scheme.Cover.iUnion_range`：∀ {K : CategoryTheory.Preco
verage AlgebraicGeometry.Scheme} [AlgebraicGeometry.Scheme.JointlySurjective K] 
  {X : AlgebraicGeometry.Scheme} …
· 使用定理 `AlgebraicGeometry.Scheme.instJointlySurjectivePrecoverage`：∀ {P : Catego
ryTheory.MorphismProperty AlgebraicGeometry.Scheme},   AlgebraicGeometry.Scheme.
JointlySurjective (AlgebraicGeometry.Scheme.pre…
-/
theorem OpenCover.iSup_opensRange {X : Scheme.{u}} (𝒰 : Scheme.OpenCover.{v} X) :
    ⨆ i, (𝒰.f i).opensRange = ⊤ :=
  Opens.ext <| by rw [Opens.coe_iSup]; exact 𝒰.iUnion_range

/-- The ranges of the maps in a scheme-theoretic open cover are a topological open cover. -/
/-
**AlgebraicGeometry.Scheme.OpenCover.isOpenCover_opensRange** 是 Mathlib 中的一个定理，位
于命名空间 `AlgebraicGeometry.Scheme.OpenCover`。
形式化陈述：∀ {X : AlgebraicGeometry.Scheme} (𝒰 : X.OpenCover),   TopologicalSpace.IsO
penCover fun i => AlgebraicGeometry.Scheme.Hom.opensRange (𝒰.f i)
参数：𝒰 : X.OpenCover；𝒰.f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `TopologicalSpace.IsOpenCover.mk`：mk (h : iSup u = ⊤) : IsOpenCover u
· 使用定理 `AlgebraicGeometry.Scheme.instIsOpenImmersionF`：∀ {X : AlgebraicGeometry.
Scheme} (𝒰 : X.OpenCover) (i : 𝒰.I₀), AlgebraicGeometry.IsOpenImmersion (𝒰.f i)
· 使用定理 `AlgebraicGeometry.Scheme.OpenCover.iSup_opensRange`：∀ {X : AlgebraicGeom
etry.Scheme} (𝒰 : X.OpenCover), ⨆ i, AlgebraicGeometry.Scheme.Hom.opensRange (𝒰.
f i) = ⊤

--- 原说明 ---
The ranges of the maps in a scheme-theoretic open cover are a topological open c
over.
-/
lemma OpenCover.isOpenCover_opensRange {X : Scheme.{u}} (𝒰 : OpenCover.{v} X) :
    IsOpenCover fun i ↦ (𝒰.f i).opensRange :=
  .mk 𝒰.iSup_opensRange

/-- Every open cover of a quasi-compact scheme can be refined into a finite subcover.
-/
@[simps! X f]
/-
**AlgebraicGeometry.Scheme.OpenCover.finiteSubcover** 是 Mathlib 中的一个定义，位于命名空间 `A
lgebraicGeometry.Scheme.OpenCover`。
形式化陈述：{X : AlgebraicGeometry.Scheme} → X.OpenCover → [H : CompactSpace ↥X] → X.O
penCover
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.instJointlySurjectivePrecoverage`：∀ {P : Catego
ryTheory.MorphismProperty AlgebraicGeometry.Scheme},   AlgebraicGeometry.Scheme.
JointlySurjective (AlgebraicGeometry.Scheme.pre…

--- 原说明 ---
Every open cover of a quasi-compact scheme can be refined into a finite subcover
.
-/
def OpenCover.finiteSubcover {X : Scheme.{u}} (𝒰 : OpenCover.{v} X) [H : CompactSpace X] :
    OpenCover X := by
  have :=
    @CompactSpace.elim_nhds_subcover _ _ H (fun x : X => Set.range (𝒰.f (𝒰.idx x)))
      fun x => (IsOpenImmersion.isOpen_range (𝒰.f (𝒰.idx x))).mem_nhds (𝒰.covers x)
  let t := this.choose
  have h : ∀ x : X, ∃ y : t, x ∈ Set.range (𝒰.f (𝒰.idx y)) := by
    intro x
    have h' : x ∈ (⊤ : Set X) := trivial
    rw [← Classical.choose_spec this, Set.mem_iUnion] at h'
    rcases h' with ⟨y, _, ⟨hy, rfl⟩, hy'⟩
    exact ⟨⟨y, hy⟩, hy'⟩
  exact
    { I₀ := t
      X := fun x => 𝒰.X (𝒰.idx x.1)
      f := fun x => 𝒰.f (𝒰.idx x.1)
      mem₀ := by
        rw [presieve₀_mem_precoverage_iff]
        exact ⟨h, inferInstance⟩ }
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [H : CompactSpace X] : Fintype 𝒰.finiteSubcover.I₀ := by
  delta OpenCover.finiteSubcover; infer_instance
/-
**AlgebraicGeometry.Scheme.OpenCover.compactSpace** 是 Mathlib 中的一个定理，位于命名空间 `Alg
ebraicGeometry.Scheme.OpenCover`。
形式化陈述：∀ {X : AlgebraicGeometry.Scheme} (𝒰 : X.OpenCover) [Finite 𝒰.I₀] [H : ∀ (i
 : 𝒰.I₀), CompactSpace ↥(𝒰.X i)],   CompactSpace ↥X
参数：𝒰 : X.OpenCover；i : 𝒰.I₀；𝒰.X i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isCompact_univ_iff`：isCompact_univ_iff : IsCompact (univ : Set X) ↔ Comp
actSpace X
· 使用定理 `AlgebraicGeometry.Scheme.Cover.iUnion_range`：∀ {K : CategoryTheory.Preco
verage AlgebraicGeometry.Scheme} [AlgebraicGeometry.Scheme.JointlySurjective K] 
  {X : AlgebraicGeometry.Scheme} …
· 使用定理 `AlgebraicGeometry.Scheme.instJointlySurjectivePrecoverage`：∀ {P : Catego
ryTheory.MorphismProperty AlgebraicGeometry.Scheme},   AlgebraicGeometry.Scheme.
JointlySurjective (AlgebraicGeometry.Scheme.pre…
· 使用定理 `isCompact_iUnion`：isCompact_iUnion {ι : Sort*} {f : ι -> Set X} [Finite 
ι] (h : forall i, IsCompact (f i)) : IsCompact (⋃ i, f i)
· 使用定理 `isCompact_iff_compactSpace`：isCompact_iff_compactSpace : IsCompact s ↔ C
ompactSpace s
· 使用定理 `Homeomorph.compactSpace`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolog
icalSpace X] [inst_1 : TopologicalSpace Y] [CompactSpace X] (h : X ≃ₜ Y),   Comp
actSpace Y
· 使用定理 `Topology.IsOpenEmbedding.isOpen_range`：∀ {X : Type u_1} {Y : Type u_2} [
tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsOpe
nEmbedding f → IsOpen (Set.…
· 使用定理 `AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.base_open`：∀ {C : Type
 u} {inst : CategoryTheory.Category.{v, u} C} {X Y : AlgebraicGeometry.Presheafe
dSpace C} {f : X ⟶ Y}   [self : AlgebraicGeometry…
· 使用定理 `AlgebraicGeometry.Scheme.Cover.map_prop`：∀ {X : AlgebraicGeometry.Scheme
} {P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme}   (𝒰 : Algebrai
cGeometry.Scheme.Cover (Algeb…
· 使用定理 `TopologicalSpace.Opens.isOpenEmbedding`：isOpenEmbedding {X : TopCat.{u}}
 (U : Opens X) : IsOpenEmbedding (inclusion' U)
· 使用定理 `AlgebraicGeometry.Scheme.instIsOpenImmersionF`：∀ {X : AlgebraicGeometry.
Scheme} (𝒰 : X.OpenCover) (i : 𝒰.I₀), AlgebraicGeometry.IsOpenImmersion (𝒰.f i)
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.ofRestrict`：∀ {U : TopCat} (X : Algebr
aicGeometry.Scheme) {f : U ⟶ TopCat.of ↥X}   (h : Topology.IsOpenEmbedding ⇑(Cat
egoryTheory.ConcreteCategory.hom f…
· 使用定理 `Subtype.range_coe`：range_coe {s : Set α} : range ((↑) : s -> α) = s
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
-/
theorem OpenCover.compactSpace {X : Scheme.{u}} (𝒰 : X.OpenCover) [Finite 𝒰.I₀]
    [H : ∀ i, CompactSpace (𝒰.X i)] : CompactSpace X := by
  cases nonempty_fintype 𝒰.I₀
  rw [← isCompact_univ_iff, ← 𝒰.iUnion_range]
  apply isCompact_iUnion
  intro i
  rw [isCompact_iff_compactSpace]
  exact
    @Homeomorph.compactSpace _ _ _ _ (H i)
      (TopCat.homeoOfIso
        (asIso
          (IsOpenImmersion.isoOfRangeEq (𝒰.f i)
            (X.ofRestrict (Opens.isOpenEmbedding ⟨_, (𝒰.map_prop i).base_open.isOpen_range⟩))
            Subtype.range_coe.symm).hom.base))
/--
An affine open cover of `X` consists of a family of open immersions into `X` from
spectra of rings.
-/
/-
**AlgebraicGeometry.Scheme.AffineOpenCover** 是 Mathlib 中的一个缩写定义，位于命名空间 `Algebrai
cGeometry.Scheme`。
形式化陈述：AffineOpenCover (X : Scheme.{u}) : Type _
参数：X : Scheme.{u}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An affine open cover of `X` consists of a family of open immersions into `X` fro
m
spectra of rings.
-/
abbrev AffineOpenCover (X : Scheme.{u}) : Type _ :=
  AffineCover.{v} @IsOpenImmersion X

namespace AffineOpenCover

/-
**AlgebraicGeometry.Scheme.AffineOpenCover.** 是 Mathlib 中的一个实例，位于命名空间 `Algebraic
Geometry.Scheme.AffineOpenCover`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X : Scheme.{u}} (𝒰 : X.AffineOpenCover) (j : 𝒰.I₀) : IsOpenImmersion (𝒰.f j) :=
  𝒰.map_prop j

/-- The open cover associated to an affine open cover. -/
@[simps! I₀ X f]
/-
**AlgebraicGeometry.Scheme.AffineOpenCover.openCover** 是 Mathlib 中的一个定义，位于命名空间 `
AlgebraicGeometry.Scheme.AffineOpenCover`。
形式化陈述：openCover {X : Scheme.{u}} (𝒰 : X.AffineOpenCover) : X.OpenCover
参数：𝒰 : X.AffineOpenCover。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The open cover associated to an affine open cover.
-/
def openCover {X : Scheme.{u}} (𝒰 : X.AffineOpenCover) : X.OpenCover :=
  AffineCover.cover 𝒰

end AffineOpenCover

set_option backward.isDefEq.respectTransparency false in
/-- A choice of an affine open cover of a scheme. -/
@[simps]
/-
**AlgebraicGeometry.Scheme.affineOpenCover** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicG
eometry.Scheme`。
形式化陈述：affineOpenCover (X : Scheme.{u}) : X.AffineOpenCover where X
参数：X : Scheme.{u}。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.local_affine`：∀ (self : AlgebraicGeometry.Schem
e) (x : ↑self.toTopCat),   ∃ U R, Nonempty (self.restrict ⋯ ≅ AlgebraicGeometry.
Spec.toLocallyRingedSpace.o…

--- 原说明 ---
A choice of an affine open cover of a scheme.
-/
def affineOpenCover (X : Scheme.{u}) : X.AffineOpenCover where
  X := _
  I₀ := X.affineCover.I₀
  f := X.affineCover.f
  idx x := (X.affineCover.exists_eq x).choose
  covers x := (X.affineCover.exists_eq x).choose_spec

@[simp]
/-
**AlgebraicGeometry.Scheme.openCover_affineOpenCover** 是 Mathlib 中的一个引理，位于命名空间 `
AlgebraicGeometry.Scheme`。
形式化陈述：openCover_affineOpenCover (X : Scheme.{u}) : X.affineOpenCover.openCover =
 X.affineCover
参数：X : Scheme.{u}。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma openCover_affineOpenCover (X : Scheme.{u}) : X.affineOpenCover.openCover = X.affineCover :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Given any open cover `𝓤`, this is an affine open cover which refines it.
The morphism in the category of open covers which proves that this is indeed a refinement, see
`AlgebraicGeometry.Scheme.OpenCover.fromAffineRefinement`.
-/
/-
**AlgebraicGeometry.Scheme.OpenCover.affineRefinement** 是 Mathlib 中的一个定义，位于命名空间 
`AlgebraicGeometry.Scheme.OpenCover`。
形式化陈述：{X : AlgebraicGeometry.Scheme} → X.OpenCover → X.AffineOpenCover
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.instIsStableUnderCompositionPrecoverageOfIsStab
leUnderComposition`：∀ (P : CategoryTheory.MorphismProperty AlgebraicGeometry.Sch
eme) [P.IsStableUnderComposition],   (AlgebraicGeometry.Scheme.precoverage P).Is
…
· 使用定理 `AlgebraicGeometry.Scheme.instJointlySurjectivePrecoverage`：∀ {P : Catego
ryTheory.MorphismProperty AlgebraicGeometry.Scheme},   AlgebraicGeometry.Scheme.
JointlySurjective (AlgebraicGeometry.Scheme.pre…

--- 原说明 ---
Given any open cover `𝓤`, this is an affine open cover which refines it.
The morphism in the category of open covers which proves that this is indeed a r
efinement, see
`AlgebraicGeometry.Scheme.OpenCover.fromAffineRefinement`.
-/
def OpenCover.affineRefinement {X : Scheme.{u}} (𝓤 : X.OpenCover) : X.AffineOpenCover where
  X := _
  I₀ := (𝓤.bind fun j => (𝓤.X j).affineCover).I₀
  f := (𝓤.bind fun j => (𝓤.X j).affineCover).f
  idx := Cover.idx (𝓤.bind fun j => (𝓤.X j).affineCover)
  covers := Cover.covers (𝓤.bind fun j => (𝓤.X j).affineCover)

set_option backward.isDefEq.respectTransparency false in
/-- The pullback of the affine refinement is the pullback of the affine cover. -/
/-
**AlgebraicGeometry.Scheme.OpenCover.pullbackCoverAffineRefinementObjIso** 是 Mat
hlib 中的一个定义，位于命名空间 `AlgebraicGeometry.Scheme.OpenCover`。
形式化陈述：{X Y : AlgebraicGeometry.Scheme} →   (f : X ⟶ Y) →     (𝒰 : Y.OpenCover) →
       (i : (CategoryTheory.Precoverage.ZeroHypercover.pullback₁ f 𝒰.affineRefin
ement.openCover).I₀) →         (CategoryTheory.Precoverage.ZeroHypercover.pullba
ck₁ f 𝒰.affineRefinement.openCover).X i ≅           (CategoryTheory.Precoverage.
ZeroHypercover.pullback₁ (AlgebraicGeometry.Scheme.Cover.pullbackHom 𝒰 f i.fst) 
                (𝒰.X i.fst).affineCover).X             i.snd
参数：f : X ⟶ Y；𝒰 : Y.OpenCover；i : (CategoryTheory.Precoverage.ZeroHypercover.pull
back₁ f 𝒰.affineRefinement.openCover).I₀；CategoryTheory.Precoverage.ZeroHypercov
er.pullback₁ f 𝒰.affineRefinement.openCover；CategoryTheory.Precoverage.ZeroHyper
cover.pullback₁ (AlgebraicGeometry.Scheme.Cover.pullbackHom 𝒰 f i.fst)          
       (𝒰.X i.fst).affineCover。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.instIsStableUnderBaseChangePrecoverageOfIsJoint
lySurjectivePreservingOfIsStableUnderBaseChange`：∀ (P : CategoryTheory.MorphismP
roperty AlgebraicGeometry.Scheme)   [AlgebraicGeometry.Scheme.IsJointlySurjectiv
ePreserving P] [P.IsStableUnd…
· 使用定理 `AlgebraicGeometry.Scheme.instIsJointlySurjectivePreservingIsOpenImmersio
n`：AlgebraicGeometry.Scheme.IsJointlySurjectivePreserving AlgebraicGeometry.IsOp
enImmersion

--- 原说明 ---
The pullback of the affine refinement is the pullback of the affine cover.
-/
def OpenCover.pullbackCoverAffineRefinementObjIso (f : X ⟶ Y) (𝒰 : Y.OpenCover) (i) :
    (𝒰.affineRefinement.openCover.pullback₁ f).X i ≅
      ((𝒰.X i.1).affineCover.pullback₁ (𝒰.pullbackHom f i.1)).X i.2 :=
  pullbackSymmetry _ _ ≪≫ (pullbackRightPullbackFstIso _ _ _).symm ≪≫
    pullbackSymmetry _ _ ≪≫ asIso (pullback.map _ _ _ _ (pullbackSymmetry _ _).hom (𝟙 _) (𝟙 _)
      (by simp [Cover.pullbackHom]) (by simp))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**AlgebraicGeometry.Scheme.OpenCover.pullbackCoverAffineRefinementObjIso_inv_map
** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.Scheme.OpenCover`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) (𝒰 : Y.OpenCover)   (i : (C
ategoryTheory.Precoverage.ZeroHypercover.pullback₁ f 𝒰.affineRefinement.openCove
r).I₀),   CategoryTheory.CategoryStruct.comp (AlgebraicGeometry.Scheme.OpenCover
.pullbackCoverAffineRefinementObjIso f 𝒰 i).inv       ((CategoryTheory.Precovera
ge.ZeroHypercover.pullback₁ f 𝒰.affineRefinement.openCover).f i) =     CategoryT
heory.CategoryStruct.comp       ((CategoryTheory.Precoverage.ZeroHypercover.pull
back₁ (AlgebraicGeometry.Scheme.Cover.pullbackHom 𝒰 f i.fst)             (𝒰.X i.
fst).affineCover).f         i.snd)       ((CategoryTheory.Precoverage.ZeroHyperc
over.pullback₁ f 𝒰).f i.fst)
参数：f : X ⟶ Y；𝒰 : Y.OpenCover；i : (CategoryTheory.Precoverage.ZeroHypercover.pull
back₁ f 𝒰.affineRefinement.openCover).I₀；AlgebraicGeometry.Scheme.OpenCover.pull
backCoverAffineRefinementObjIso f 𝒰 i；(CategoryTheory.Precoverage.ZeroHypercover
.pullback₁ f 𝒰.affineRefinement.openCover).f i；(CategoryTheory.Precoverage.ZeroH
ypercover.pullback₁ (AlgebraicGeometry.Scheme.Cover.pullbackHom 𝒰 f i.fst)      
       (𝒰.X i.fst).affineCover).f         i.snd；(CategoryTheory.Precoverage.Zero
Hypercover.pullback₁ f 𝒰).f i.fst。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.instIsStableUnderBaseChangePrecoverageOfIsJoint
lySurjectivePreservingOfIsStableUnderBaseChange`：∀ (P : CategoryTheory.MorphismP
roperty AlgebraicGeometry.Scheme)   [AlgebraicGeometry.Scheme.IsJointlySurjectiv
ePreserving P] [P.IsStableUnd…
· 使用定理 `AlgebraicGeometry.Scheme.instIsJointlySurjectivePreservingIsOpenImmersio
n`：AlgebraicGeometry.Scheme.IsJointlySurjectivePreserving AlgebraicGeometry.IsOp
enImmersion
· 使用定理 `AlgebraicGeometry.Scheme.instIsOpenImmersionF`：∀ {X : AlgebraicGeometry.
Scheme} (𝒰 : X.OpenCover) (i : 𝒰.I₀), AlgebraicGeometry.IsOpenImmersion (𝒰.f i)
· 使用定理 `CategoryTheory.Limits.hasPullback_symmetry`：hasPullback_symmetry [HasPul
lback f g] : HasPullback g f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.pullbackSymmetry_inv_comp_fst`：pullbackSymmetry_in
v_comp_fst [HasPullback f g] : (pullbackSymmetry f g).inv ≫ pullback.fst f g = p
ullback.snd g f
· 使用定理 `CategoryTheory.Limits.limit.lift_π_assoc`：∀ {J : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v,
 u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.pullbackSymmetry_hom_comp_fst`：pullbackSymmetry_ho
m_comp_fst [HasPullback f g] : (pullbackSymmetry f g).hom ≫ pullback.fst g f = p
ullback.snd f g
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `CategoryTheory.Limits.pullbackRightPullbackFstIso_hom_snd`：pullbackRight
PullbackFstIso_hom_snd : (pullbackRightPullbackFstIso f g f').hom ≫ pullback.snd
 _ _ = pullback.snd f' (pullback.fst f g) ≫ pul…
· 使用定理 `CategoryTheory.Limits.pullbackSymmetry_inv_comp_snd_assoc`：∀ {C : Type u
} [inst : CategoryTheory.Category.{v, u} C] {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) 
  [inst_1 : CategoryTheory.Limits.HasPullback f…
-/
lemma OpenCover.pullbackCoverAffineRefinementObjIso_inv_map (f : X ⟶ Y) (𝒰 : Y.OpenCover) (i) :
    (𝒰.pullbackCoverAffineRefinementObjIso f i).inv ≫
      (𝒰.affineRefinement.openCover.pullback₁ f).f i =
      ((𝒰.X i.1).affineCover.pullback₁ (𝒰.pullbackHom f i.1)).f i.2 ≫
        (𝒰.pullback₁ f).f i.1 := by
  simp only [Precoverage.ZeroHypercover.pullback₁_toPreZeroHypercover,
    PreZeroHypercover.pullback₁_X, AffineOpenCover.openCover_X, AffineOpenCover.openCover_f,
    pullbackCoverAffineRefinementObjIso, Iso.trans_inv, asIso_inv, Iso.symm_inv, Category.assoc,
    PreZeroHypercover.pullback₁_f, pullbackSymmetry_inv_comp_fst, IsIso.inv_comp_eq,
    limit.lift_π_assoc, PullbackCone.mk_pt, cospan_left, PullbackCone.mk_π_app,
    pullbackSymmetry_hom_comp_fst]
  convert!
    pullbackSymmetry_inv_comp_snd_assoc ((𝒰.X i.1).affineCover.f i.2) (pullback.fst _ _) _ using 2
  exact pullbackRightPullbackFstIso_hom_snd _ _ _

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**AlgebraicGeometry.Scheme.OpenCover.pullbackCoverAffineRefinementObjIso_inv_pul
lbackHom** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.Scheme.OpenCover`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) (𝒰 : Y.OpenCover)   (i : (C
ategoryTheory.Precoverage.ZeroHypercover.pullback₁ f 𝒰.affineRefinement.openCove
r).I₀),   CategoryTheory.CategoryStruct.comp (AlgebraicGeometry.Scheme.OpenCover
.pullbackCoverAffineRefinementObjIso f 𝒰 i).inv       (AlgebraicGeometry.Scheme.
Cover.pullbackHom 𝒰.affineRefinement.openCover f i) =     AlgebraicGeometry.Sche
me.Cover.pullbackHom (𝒰.X i.fst).affineCover       (AlgebraicGeometry.Scheme.Cov
er.pullbackHom 𝒰 f i.fst) i.snd
参数：f : X ⟶ Y；𝒰 : Y.OpenCover；i : (CategoryTheory.Precoverage.ZeroHypercover.pull
back₁ f 𝒰.affineRefinement.openCover).I₀；AlgebraicGeometry.Scheme.OpenCover.pull
backCoverAffineRefinementObjIso f 𝒰 i；AlgebraicGeometry.Scheme.Cover.pullbackHom
 𝒰.affineRefinement.openCover f i；𝒰.X i.fst；AlgebraicGeometry.Scheme.Cover.pullb
ackHom 𝒰 f i.fst。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.instIsStableUnderBaseChangePrecoverageOfIsJoint
lySurjectivePreservingOfIsStableUnderBaseChange`：∀ (P : CategoryTheory.MorphismP
roperty AlgebraicGeometry.Scheme)   [AlgebraicGeometry.Scheme.IsJointlySurjectiv
ePreserving P] [P.IsStableUnd…
· 使用定理 `AlgebraicGeometry.Scheme.instIsJointlySurjectivePreservingIsOpenImmersio
n`：AlgebraicGeometry.Scheme.IsJointlySurjectivePreserving AlgebraicGeometry.IsOp
enImmersion
· 使用定理 `AlgebraicGeometry.Scheme.instIsOpenImmersionF`：∀ {X : AlgebraicGeometry.
Scheme} (𝒰 : X.OpenCover) (i : 𝒰.I₀), AlgebraicGeometry.IsOpenImmersion (𝒰.f i)
· 使用定理 `CategoryTheory.Limits.hasPullback_symmetry`：hasPullback_symmetry [HasPul
lback f g] : HasPullback g f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.pullbackSymmetry_inv_comp_snd`：pullbackSymmetry_in
v_comp_snd [HasPullback f g] : (pullbackSymmetry f g).inv ≫ pullback.snd f g = p
ullback.fst g f
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PullbackCone.mk_π_app`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {W : C} (fst :
 W ⟶ X)   (snd : W ⟶ Y)   (eq :  …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `CategoryTheory.Limits.pullbackRightPullbackFstIso_hom_fst`：pullbackRight
PullbackFstIso_hom_fst : (pullbackRightPullbackFstIso f g f').hom ≫ pullback.fst
 (f' ≫ f) g = pullback.fst f' (pullback.fst f g…
· 使用定理 `CategoryTheory.Limits.pullbackSymmetry_inv_comp_fst`：pullbackSymmetry_in
v_comp_fst [HasPullback f g] : (pullbackSymmetry f g).inv ≫ pullback.fst f g = p
ullback.snd g f
-/
lemma OpenCover.pullbackCoverAffineRefinementObjIso_inv_pullbackHom
    (f : X ⟶ Y) (𝒰 : Y.OpenCover) (i) :
    (𝒰.pullbackCoverAffineRefinementObjIso f i).inv ≫
      𝒰.affineRefinement.openCover.pullbackHom f i =
      (𝒰.X i.1).affineCover.pullbackHom (𝒰.pullbackHom f i.1) i.2 := by
  simp only [Cover.pullbackHom, pullbackCoverAffineRefinementObjIso, Iso.trans_inv, asIso_inv,
    Iso.symm_inv, Category.assoc, pullbackSymmetry_inv_comp_snd, IsIso.inv_comp_eq, limit.lift_π,
    PullbackCone.mk_π_app, Category.comp_id]
  convert! pullbackSymmetry_inv_comp_fst ((𝒰.X i.1).affineCover.f i.2) (pullback.fst _ _)
  exact pullbackRightPullbackFstIso_hom_fst _ _ _

/-- A family of elements spanning the unit ideal of `R` gives an affine open cover of `Spec R`. -/
@[simps]
noncomputable
/-
**AlgebraicGeometry.Scheme.affineOpenCoverOfSpanRangeEqTop** 是 Mathlib 中的一个定义，位于
命名空间 `AlgebraicGeometry.Scheme`。
形式化陈述：affineOpenCoverOfSpanRangeEqTop {R : CommRingCat} {ι : Type*} (s : ι -> R)
 (hs : Ideal.span (Set.range s) = ⊤) : (Spec R).AffineOpenCover where I₀
参数：s : ι -> R；hs : Ideal.span (Set.range s) = ⊤。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def affineOpenCoverOfSpanRangeEqTop {R : CommRingCat} {ι : Type*} (s : ι → R)
    (hs : Ideal.span (Set.range s) = ⊤) : (Spec R).AffineOpenCover where
  I₀ := ι
  X i := .of (Localization.Away (s i))
  f i := Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (s i))))
  idx x := by
    have : ∃ i, s i ∉ x.asIdeal := by
      by_contra! h; apply x.2.ne_top; rwa [← top_le_iff, ← hs, Ideal.span_le, Set.range_subset_iff]
    exact this.choose
  covers x := by
    generalize_proofs H
    let i := H.choose
    have := PrimeSpectrum.localization_away_comap_range (Localization.Away (s i)) (s i)
    exact (eq_iff_iff.mp congr(x ∈ $this)).mpr H.choose_spec

/-- Given any open cover `𝓤`, this is an affine open cover which refines it. -/
/-
**AlgebraicGeometry.Scheme.OpenCover.fromAffineRefinement** 是 Mathlib 中的一个定义，位于命
名空间 `AlgebraicGeometry.Scheme.OpenCover`。
形式化陈述：{X : AlgebraicGeometry.Scheme} → (𝓤 : X.OpenCover) → 𝓤.affineRefinement.op
enCover ⟶ 𝓤
参数：𝓤 : X.OpenCover。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given any open cover `𝓤`, this is an affine open cover which refines it.
-/
def OpenCover.fromAffineRefinement {X : Scheme.{u}} (𝓤 : X.OpenCover) :
    𝓤.affineRefinement.openCover ⟶ 𝓤 where
  s₀ j := j.fst
  h₀ j := (𝓤.X j.fst).affineCover.f _

/-- If two global sections agree after restriction to each member of an open cover, then
they agree globally. -/
/-
**AlgebraicGeometry.Scheme.OpenCover.ext_elem** 是 Mathlib 中的一个定理，位于命名空间 `Algebra
icGeometry.Scheme.OpenCover`。
形式化陈述：∀ {X : AlgebraicGeometry.Scheme} {U : X.Opens} (f g : ↑(X.presheaf.obj (Op
posite.op U))) (𝒰 : X.OpenCover),   (∀ (i : 𝒰.I₀),       (CategoryTheory.Concret
eCategory.hom (AlgebraicGeometry.Scheme.Hom.app (𝒰.f i) U)) f =         (Categor
yTheory.ConcreteCategory.hom (AlgebraicGeometry.Scheme.Hom.app (𝒰.f i) U)) g) → 
    f = g
参数：f g : ↑(X.presheaf.obj (Opposite.op U))；𝒰 : X.OpenCover；∀ (i : 𝒰.I₀),       (
CategoryTheory.ConcreteCategory.hom (AlgebraicGeometry.Scheme.Hom.app (𝒰.f i) U)
) f =         (CategoryTheory.ConcreteCategory.hom (AlgebraicGeometry.Scheme.Hom
.app (𝒰.f i) U)) g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopCat.Sheaf.eq_of_locally_eq'`：∀ {C : Type u_1} [inst : CategoryTheory.
Category.{v_1, u_1} C] {FC : C → C → Type u_2} {CC : C → Type u_3}   [inst_1 : (
X Y : C) → FunLike (…
· 使用定理 `AlgebraicGeometry.Scheme.instJointlySurjectivePrecoverage`：∀ {P : Catego
ryTheory.MorphismProperty AlgebraicGeometry.Scheme},   AlgebraicGeometry.Scheme.
JointlySurjective (AlgebraicGeometry.Scheme.pre…
· 使用定理 `AlgebraicGeometry.Scheme.instIsOpenImmersionF`：∀ {X : AlgebraicGeometry.
Scheme} (𝒰 : X.OpenCover) (i : 𝒰.I₀), AlgebraicGeometry.IsOpenImmersion (𝒰.f i)
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `isOpen_iUnion`：isOpen_iUnion {f : ι -> Set X} (h : forall i, IsOpen (f i
)) : IsOpen (⋃ i, f i)
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AlgebraicGeometry.Scheme.Hom.coe_opensRange`：∀ {X Y : AlgebraicGeometry.
Scheme} (f : X ⟶ Y) [H : AlgebraicGeometry.IsOpenImmersion f],   ↑(AlgebraicGeom
etry.Scheme.Hom.opensRange f) = S…
· 使用定理 `TopologicalSpace.Opens.iSup_mk`：iSup_mk {ι} (s : ι -> Set α) (h : forall
 i, IsOpen (s i)) : (⨆ i, ⟨s i, h i⟩ : Opens α) = ⟨⋃ i, s i, isOpen_iUnion h⟩
· 使用定理 `TopologicalSpace.Opens.mk.congr_simp`：∀ {α : Type u_2} [inst : Topologic
alSpace α] (carrier carrier_1 : Set α) (e_carrier : carrier = carrier_1)   (is_o
pen' : IsOpen carrier), { …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `AlgebraicGeometry.Scheme.Cover.covers`：∀ {K : CategoryTheory.Precoverage
 AlgebraicGeometry.Scheme} {X : AlgebraicGeometry.Scheme}   [inst : AlgebraicGeo
metry.Scheme.JointlySurject…
· 使用定理 `RingEquiv.injective`：∀ {R : Type u_4} {S : Type u_5} [inst : Mul R] [ins
t_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S] (e : R ≃+* S),   Function.Injecti
ve ⇑e
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `AlgebraicGeometry.IsOpenImmersion.map_ΓIso_inv`：map_ΓIso_inv {X Y : Sche
me.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (U : Y.Opens) : Y.presheaf.map (homOfLE 
inf_le_right).op ≫ (ΓIso f U).inv = …

--- 原说明 ---
If two global sections agree after restriction to each member of an open cover, 
then
they agree globally.
-/
lemma OpenCover.ext_elem {X : Scheme.{u}} {U : X.Opens} (f g : Γ(X, U)) (𝒰 : X.OpenCover)
    (h : ∀ i : 𝒰.I₀, (𝒰.f i).app U f = (𝒰.f i).app U g) : f = g := by
  fapply TopCat.Sheaf.eq_of_locally_eq' X.sheaf
    (fun i ↦ (𝒰.f (𝒰.idx i)).opensRange ⊓ U) _ (fun _ ↦ homOfLE inf_le_right)
  · intro x hx
    simp only [Opens.iSup_mk, Opens.carrier_eq_coe, Opens.coe_inf, Hom.coe_opensRange, Opens.mem_mk,
      Set.mem_iUnion, Set.mem_inter_iff, Set.mem_range, SetLike.mem_coe, exists_and_right]
    refine ⟨?_, hx⟩
    simpa using ⟨_, 𝒰.covers x⟩
  · intro x
    replace h := h (𝒰.idx x)
    rw [← IsOpenImmersion.map_ΓIso_inv] at h
    exact (IsOpenImmersion.ΓIso (𝒰.f (𝒰.idx x)) U).commRingCatIsoToRingEquiv.symm.injective h

/-- If the restriction of a global section to each member of an open cover is zero, then it is
globally zero. -/
/-
**AlgebraicGeometry.Scheme.zero_of_zero_cover** 是 Mathlib 中的一个引理，位于命名空间 `Algebra
icGeometry.Scheme`。
形式化陈述：zero_of_zero_cover {X : Scheme.{u}} {U : X.Opens} (s : Γ(X, U)) (𝒰 : X.Ope
nCover) (h : forall i : 𝒰.I₀, (𝒰.f i).app U s = 0) : s = 0
参数：s : Γ(X, U)；𝒰 : X.OpenCover；h : forall i : 𝒰.I₀, (𝒰.f i).app U s = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.OpenCover.ext_elem`：∀ {X : AlgebraicGeometry.Sc
heme} {U : X.Opens} (f g : ↑(X.presheaf.obj (Opposite.op U))) (𝒰 : X.OpenCover),
   (∀ (i : 𝒰.I₀),       (Category…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…

--- 原说明 ---
If the restriction of a global section to each member of an open cover is zero, 
then it is
globally zero.
-/
lemma zero_of_zero_cover {X : Scheme.{u}} {U : X.Opens} (s : Γ(X, U)) (𝒰 : X.OpenCover)
    (h : ∀ i : 𝒰.I₀, (𝒰.f i).app U s = 0) : s = 0 :=
  𝒰.ext_elem s 0 (fun i ↦ by rw [map_zero]; exact h i)

/-- If a global section is nilpotent on each member of a finite open cover, then `f` is
nilpotent. -/
/-
**AlgebraicGeometry.Scheme.isNilpotent_of_isNilpotent_cover** 是 Mathlib 中的一个引理，位
于命名空间 `AlgebraicGeometry.Scheme`。
形式化陈述：isNilpotent_of_isNilpotent_cover {X : Scheme.{u}} {U : X.Opens} (s : Γ(X, 
U)) (𝒰 : X.OpenCover) [Finite 𝒰.I₀] (h : forall i : 𝒰.I₀, IsNilpotent ((𝒰.f i).a
pp U s)) : IsNilpotent s
参数：s : Γ(X, U)；𝒰 : X.OpenCover；h : forall i : 𝒰.I₀, IsNilpotent ((𝒰.f i).app U s
)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.le_sup`：le_sup {b : β} (hb : b in s) : f b <= s.sup f
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用引理 `AlgebraicGeometry.Scheme.zero_of_zero_cover`：zero_of_zero_cover {X : Sch
eme.{u}} {U : X.Opens} (s : Γ(X, U)) (𝒰 : X.OpenCover) (h : forall i : 𝒰.I₀, (𝒰.
f i).app U s = 0) : s = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `pow_eq_zero_of_le`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀] {a : M₀}
 {m n : ℕ}, m ≤ n → a ^ m = 0 → a ^ n = 0
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
If a global section is nilpotent on each member of a finite open cover, then `f`
 is
nilpotent.
-/
lemma isNilpotent_of_isNilpotent_cover {X : Scheme.{u}} {U : X.Opens} (s : Γ(X, U))
    (𝒰 : X.OpenCover) [Finite 𝒰.I₀] (h : ∀ i : 𝒰.I₀, IsNilpotent ((𝒰.f i).app U s)) :
    IsNilpotent s := by
  choose fn hfn using h
  have : Fintype 𝒰.I₀ := Fintype.ofFinite 𝒰.I₀
  /- the maximum of all `fn i` (exists, because `𝒰.I₀` is finite) -/
  let N : ℕ := Finset.sup Finset.univ fn
  have hfnleN (i : 𝒰.I₀) : fn i ≤ N := Finset.le_sup (Finset.mem_univ i)
  use N
  apply zero_of_zero_cover (𝒰 := 𝒰)
  on_goal 1 => intro i; simp only [map_pow]
  -- This closes both remaining goals at once.
  exact pow_eq_zero_of_le (hfnleN i) (hfn i)

section deprecated

/-- The basic open sets form an affine open cover of `Spec R`. -/
/-
**AlgebraicGeometry.Scheme.affineBasisCoverOfAffine** 是 Mathlib 中的一个定义，位于命名空间 `A
lgebraicGeometry.Scheme`。
形式化陈述：affineBasisCoverOfAffine (R : CommRingCat.{u}) : OpenCover (Spec R) where 
I₀
参数：R : CommRingCat.{u}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The basic open sets form an affine open cover of `Spec R`.
-/
def affineBasisCoverOfAffine (R : CommRingCat.{u}) : OpenCover (Spec R) where
  I₀ := R
  X r := Spec <| .of <| Localization.Away r
  f r := Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ⟨1, ?_⟩, AlgebraicGeometry.Scheme.isOpenImmersion_SpecMap_localizationAway⟩
    rw [Set.range_eq_univ.mpr ((TopCat.epi_iff_surjective _).mp _)]
    · exact trivial
    · infer_instance

/-- We may bind the basic open sets of an open affine cover to form an affine cover that is also
a basis. -/
/-
**AlgebraicGeometry.Scheme.affineBasisCover** 是 Mathlib 中的一个定义，位于命名空间 `Algebraic
Geometry.Scheme`。
形式化陈述：affineBasisCover (X : Scheme.{u}) : OpenCover X
参数：X : Scheme.{u}。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.instIsStableUnderCompositionPrecoverageOfIsStab
leUnderComposition`：∀ (P : CategoryTheory.MorphismProperty AlgebraicGeometry.Sch
eme) [P.IsStableUnderComposition],   (AlgebraicGeometry.Scheme.precoverage P).Is
…
· 使用定理 `AlgebraicGeometry.Scheme.local_affine`：∀ (self : AlgebraicGeometry.Schem
e) (x : ↑self.toTopCat),   ∃ U R, Nonempty (self.restrict ⋯ ≅ AlgebraicGeometry.
Spec.toLocallyRingedSpace.o…

--- 原说明 ---
We may bind the basic open sets of an open affine cover to form an affine cover 
that is also
a basis.
-/
def affineBasisCover (X : Scheme.{u}) : OpenCover X :=
  X.affineCover.bind fun _ => affineBasisCoverOfAffine _

/-- The coordinate ring of a component in the `affine_basis_cover`. -/
/-
**AlgebraicGeometry.Scheme.affineBasisCoverRing** 是 Mathlib 中的一个定义，位于命名空间 `Algeb
raicGeometry.Scheme`。
形式化陈述：affineBasisCoverRing (X : Scheme.{u}) (i : X.affineBasisCover.I₀) : CommRi
ngCat
参数：X : Scheme.{u}；i : X.affineBasisCover.I₀。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.local_affine`：∀ (self : AlgebraicGeometry.Schem
e) (x : ↑self.toTopCat),   ∃ U R, Nonempty (self.restrict ⋯ ≅ AlgebraicGeometry.
Spec.toLocallyRingedSpace.o…

--- 原说明 ---
The coordinate ring of a component in the `affine_basis_cover`.
-/
def affineBasisCoverRing (X : Scheme.{u}) (i : X.affineBasisCover.I₀) : CommRingCat :=
  CommRingCat.of <| @Localization.Away (X.local_affine i.1).choose_spec.choose _ i.2
/-
**AlgebraicGeometry.Scheme.affineBasisCover_obj** 是 Mathlib 中的一个定理，位于命名空间 `Algeb
raicGeometry.Scheme`。
形式化陈述：affineBasisCover_obj (X : Scheme.{u}) (i : X.affineBasisCover.I₀) : X.affi
neBasisCover.X i = Spec (X.affineBasisCoverRing i)
参数：X : Scheme.{u}；i : X.affineBasisCover.I₀。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem affineBasisCover_obj (X : Scheme.{u}) (i : X.affineBasisCover.I₀) :
    X.affineBasisCover.X i = Spec (X.affineBasisCoverRing i) :=
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.Scheme.affineBasisCover_map_range** 是 Mathlib 中的一个定理，位于命名空间 
`AlgebraicGeometry.Scheme`。
形式化陈述：affineBasisCover_map_range (X : Scheme.{u}) (x : X) (r : (X.local_affine x
).choose_spec.choose) : Set.range (X.affineBasisCover.f ⟨x, r⟩) = (X.affineCover
.f x) '' (PrimeSpectrum.basicOpen r).1
参数：X : Scheme.{u}；x : X；r : (X.local_affine x).choose_spec.choose。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.OpenNhds.isOpenEmbedding`：isOpenEmbedding {x : X} (U : 
OpenNhds x) : IsOpenEmbedding U.1.inclusion'
· 使用定理 `AlgebraicGeometry.Scheme.local_affine`：∀ (self : AlgebraicGeometry.Schem
e) (x : ↑self.toTopCat),   ∃ U R, Nonempty (self.restrict ⋯ ≅ AlgebraicGeometry.
Spec.toLocallyRingedSpace.o…
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `PrimeSpectrum.localization_away_comap_range`：localization_away_comap_ran
ge (S : Type v) [CommSemiring S] [Algebra R S] (r : R) [IsLocalization.Away r S]
 : Set.range (comap (algebraMap R…
-/
theorem affineBasisCover_map_range (X : Scheme.{u}) (x : X)
    (r : (X.local_affine x).choose_spec.choose) :
    Set.range (X.affineBasisCover.f ⟨x, r⟩) =
      (X.affineCover.f x) '' (PrimeSpectrum.basicOpen r).1 := by
  simp only [affineBasisCover, Precoverage.ZeroHypercover.bind_toPreZeroHypercover, Set.range_comp,
    PreZeroHypercover.bind_f, Hom.comp_base, TopCat.hom_comp, ContinuousMap.coe_comp]
  congr
  exact (PrimeSpectrum.localization_away_comap_range (Localization.Away r) r :)

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.Scheme.affineBasisCover_is_basis** 是 Mathlib 中的一个定理，位于命名空间 `
AlgebraicGeometry.Scheme`。
形式化陈述：affineBasisCover_is_basis (X : Scheme.{u}) : TopologicalSpace.IsTopologica
lBasis {x : Set X | exists a : X.affineBasisCover.I₀, x = Set.range (X.affineBas
isCover.f a)}
参数：X : Scheme.{u}。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds`：isTopologicalBasi
s_of_isOpen_of_nhds {s : Set (Set α)} (h_open : forall u in s, IsOpen u) (h_nhds
 : forall (a : α) (u : Set α), a in u -> Is…
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.isOpen_range`：∀ {X Y : AlgebraicGeomet
ry.Scheme} (f : X ⟶ Y) [H : AlgebraicGeometry.IsOpenImmersion f], IsOpen (Set.ra
nge ⇑f)
· 使用定理 `AlgebraicGeometry.Scheme.instIsOpenImmersionF`：∀ {X : AlgebraicGeometry.
Scheme} (𝒰 : X.OpenCover) (i : 𝒰.I₀), AlgebraicGeometry.IsOpenImmersion (𝒰.f i)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.Scheme.instJointlySurjectivePrecoverage`：∀ {P : Catego
ryTheory.MorphismProperty AlgebraicGeometry.Scheme},   AlgebraicGeometry.Scheme.
JointlySurjective (AlgebraicGeometry.Scheme.pre…
· 使用定理 `AlgebraicGeometry.Scheme.Cover.covers`：∀ {K : CategoryTheory.Precoverage
 AlgebraicGeometry.Scheme} {X : AlgebraicGeometry.Scheme}   [inst : AlgebraicGeo
metry.Scheme.JointlySurject…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.local_affine`：∀ (self : AlgebraicGeometry.Schem
e) (x : ↑self.toTopCat),   ∃ U R, Nonempty (self.restrict ⋯ ≅ AlgebraicGeometry.
Spec.toLocallyRingedSpace.o…
· 使用定理 `TopologicalSpace.IsTopologicalBasis.exists_subset_of_mem_open`：∀ {α : Ty
pe u} [t : TopologicalSpace α] {b : Set (Set α)},   TopologicalSpace.IsTopologic
alBasis b → ∀ {a : α} {u : Set α}, a ∈ u → IsOpen u…
· 使用定理 `PrimeSpectrum.isBasis_basic_opens`：isBasis_basic_opens : TopologicalSpac
e.Opens.IsBasis (Set.range (@basicOpen R _))
· 使用定理 `Continuous.isOpen_preimage`：∀ {X : Type u} {Y : Type v} [inst : Topologi
calSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   Continuous f → ∀ (s : S
et Y), IsOpen s …
· 使用定理 `AlgebraicGeometry.Scheme.Hom.continuous`：∀ {X Y : AlgebraicGeometry.Sche
me} (f : X ⟶ Y), Continuous ⇑f
· 使用定理 `TopologicalSpace.OpenNhds.isOpenEmbedding`：isOpenEmbedding {x : X} (U : 
OpenNhds x) : IsOpenEmbedding U.1.inclusion'
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `AlgebraicGeometry.Scheme.affineBasisCover_map_range`：affineBasisCover_ma
p_range (X : Scheme.{u}) (x : X) (r : (X.local_affine x).choose_spec.choose) : S
et.range (X.affineBasisCover.f ⟨x, r⟩) = …
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
-/
theorem affineBasisCover_is_basis (X : Scheme.{u}) :
    TopologicalSpace.IsTopologicalBasis
      {x : Set X |
        ∃ a : X.affineBasisCover.I₀, x = Set.range (X.affineBasisCover.f a)} := by
  apply TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds
  · rintro _ ⟨a, rfl⟩
    exact IsOpenImmersion.isOpen_range (X.affineBasisCover.f a)
  · rintro a U haU hU
    rcases X.affineCover.covers a with ⟨x, e⟩
    let U' := (X.affineCover.f (X.affineCover.idx a)) ⁻¹' U
    have hxU' : x ∈ U' := by rw [← e] at haU; exact haU
    rcases PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hxU'
        ((X.affineCover.f (X.affineCover.idx a)).continuous.isOpen_preimage _
          hU) with
      ⟨_, ⟨_, ⟨s, rfl⟩, rfl⟩, hxV, hVU⟩
    refine ⟨_, ⟨⟨_, s⟩, rfl⟩, ?_, ?_⟩ <;> rw [affineBasisCover_map_range]
    · exact ⟨x, hxV, e⟩
    · rw [Set.image_subset_iff]; exact hVU

end deprecated

end Scheme

end AlgebraicGeometry

