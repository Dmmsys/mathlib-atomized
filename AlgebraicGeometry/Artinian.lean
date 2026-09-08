/-
Copyright (c) 2025 Brian Nugent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Nugent
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.RingTheory.HopkinsLevitzki

/-!
# Artinian and Locally Artinian Schemes

We define and prove basic properties about Artinian and locally Artinian Schemes.

## Main definitions

* `AlgebraicGeometry.IsLocallyArtinian`: A scheme is locally Artinian if for all open affines,
  the section ring is an Artinian ring.

* `AlgebraicGeometry.IsArtinianScheme`: A scheme is Artinian if it is locally Artinian and
  quasi-compact.

## Main results

* `AlgebraicGeometry.IsLocallyArtinian.iff_isLocallyNoetherian_and_discreteTopology`: A scheme is
  locally Artinian if and only if it is LocallyNoetherian and it has the discrete topology.

* `AlgebraicGeometry.IsArtinianScheme.iff_isNoetherian_and_discreteTopology`: A scheme is Artinian
  if and only if it is Noetherian and has the discrete topology.

* `AlgebraicGeometry.IsArtinianScheme.finite`: An Artinian scheme is finite.

* `AlgebraicGeometry.Scheme.isArtinianScheme_Spec`: A commutative ring R is Artinian if and only if
  Spec R is Artinian.

-/

public section

noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- A scheme `X` is locally Artinian if `𝒪ₓ(U)` is Artinian for all affine `U`. -/
/-
**AlgebraicGeometry.IsLocallyArtinian** 是 Mathlib 中的一个类，位于命名空间 `AlgebraicGeometr
y`。
形式化陈述：IsLocallyArtinian (X : Scheme) : Prop where isArtinianRing_presheaf_obj : 
forall (U : X.affineOpens), IsArtinianRing Γ(X, U)
参数：X : Scheme。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A scheme `X` is locally Artinian if `𝒪ₓ(U)` is Artinian for all affine `U`.
-/
class IsLocallyArtinian (X : Scheme) : Prop where
  isArtinianRing_presheaf_obj : ∀ (U : X.affineOpens),
    IsArtinianRing Γ(X, U) := by infer_instance

attribute [instance] IsLocallyArtinian.isArtinianRing_presheaf_obj
/-
**AlgebraicGeometry.IsLocallyArtinian.isLocallyNoetherian** 是 Mathlib 中的一个定理，位于命
名空间 `AlgebraicGeometry.IsLocallyArtinian`。
形式化陈述：∀ {X : AlgebraicGeometry.Scheme} [h : AlgebraicGeometry.IsLocallyArtinian 
X], AlgebraicGeometry.IsLocallyNoetherian X
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsNoetherianRingOfIsArtinianRing`：∀ (R : Type u_2) [inst : Ring R] [
IsArtinianRing R], IsNoetherianRing R
· 使用定理 `AlgebraicGeometry.IsLocallyArtinian.isArtinianRing_presheaf_obj`：∀ {X : 
AlgebraicGeometry.Scheme} [self : AlgebraicGeometry.IsLocallyArtinian X] (U : ↑X
.affineOpens),   IsArtinianRing ↑(X.presheaf.obj (Opp…
-/
instance IsLocallyArtinian.isLocallyNoetherian [h : IsLocallyArtinian X] :
    IsLocallyNoetherian X where
/-
**AlgebraicGeometry.IsLocallyArtinian.isArtinianRing_of_isAffine** 是 Mathlib 中的一
个定理，位于命名空间 `AlgebraicGeometry.IsLocallyArtinian`。
形式化陈述：∀ {X : AlgebraicGeometry.Scheme} [h : AlgebraicGeometry.IsLocallyArtinian 
X] [AlgebraicGeometry.IsAffine X],   IsArtinianRing ↑(X.presheaf.obj (Opposite.o
p ⊤))
参数：X.presheaf.obj (Opposite.op ⊤)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.IsLocallyArtinian.isArtinianRing_presheaf_obj`：∀ {X : 
AlgebraicGeometry.Scheme} [self : AlgebraicGeometry.IsLocallyArtinian X] (U : ↑X
.affineOpens),   IsArtinianRing ↑(X.presheaf.obj (Opp…
· 使用定理 `AlgebraicGeometry.isAffineOpen_top`：isAffineOpen_top (X : Scheme) [IsAff
ine X] : IsAffineOpen (⊤ : X.Opens)
-/
instance IsLocallyArtinian.isArtinianRing_of_isAffine [h : IsLocallyArtinian X] [IsAffine X] :
    IsArtinianRing Γ(X, ⊤) :=
  h.1 ⟨⊤, isAffineOpen_top X⟩
/-
**AlgebraicGeometry.IsLocallyArtinian.of_topologicalKrullDim_le_zero** 是 Mathlib
 中的一个定理，位于命名空间 `AlgebraicGeometry.IsLocallyArtinian`。
形式化陈述：∀ {X : AlgebraicGeometry.Scheme} [AlgebraicGeometry.IsLocallyNoetherian X]
,   topologicalKrullDim ↥X ≤ 0 → AlgebraicGeometry.IsLocallyArtinian X
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.IsLocallyNoetherian.component_noetherian`：∀ {X : Algeb
raicGeometry.Scheme} [self : AlgebraicGeometry.IsLocallyNoetherian X] (U : ↑X.af
fineOpens),   IsNoetherianRing ↑(X.presheaf.obj …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isArtinianRing_iff_krullDimLE_zero`：isArtinianRing_iff_krullDimLE_zero {
R : Type*} [CommRing R] [IsNoetherianRing R] : IsArtinianRing R ↔ Ring.KrullDimL
E 0 R
· 使用定理 `Ring.KrullDimLE.eq_1`：∀ (n : ℕ) (R : Type u_1) [inst : CommSemiring R], 
Ring.KrullDimLE n R = Order.KrullDimLE n (PrimeSpectrum R)
· 使用定理 `Order.krullDimLE_iff`：∀ (n : ℕ) (α : Type u_1) [inst : Preorder α], Orde
r.KrullDimLE n α ↔ Order.krullDim α ≤ ↑n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ringKrullDim.eq_1`：∀ (R : Type u_1) [inst : CommSemiring R], ringKrullDi
m R = Order.krullDim (PrimeSpectrum R)
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim`：PrimeSpectrum.topolog
icalKrullDim_eq_ringKrullDim [CommSemiring R] : topologicalKrullDim (PrimeSpectr
um R) = ringKrullDim R
· 使用定理 `IsHomeomorph.topologicalKrullDim_eq`：IsHomeomorph.topologicalKrullDim_eq
 (f : X -> Y) (h : IsHomeomorph f) : topologicalKrullDim X = topologicalKrullDim
 Y
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `Homeomorph.isHomeomorph`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolog
icalSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y), IsHomeomorph ⇑h
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `topologicalKrullDim_subspace_le`：topologicalKrullDim_subspace_le (X : Ty
pe*) [TopologicalSpace X] (Y : Set X) : topologicalKrullDim Y <= topologicalKrul
lDim X
-/
lemma IsLocallyArtinian.of_topologicalKrullDim_le_zero
    [IsLocallyNoetherian X] (h : topologicalKrullDim X ≤ 0) : IsLocallyArtinian X where
  isArtinianRing_presheaf_obj U := by
    have _ : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian U
    rw [isArtinianRing_iff_krullDimLE_zero, Ring.KrullDimLE, Order.krullDimLE_iff, ← ringKrullDim,
      Nat.cast_zero, ← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim Γ(X, U)]
    change topologicalKrullDim (Spec Γ(X, U)) ≤ 0
    rw [← IsHomeomorph.topologicalKrullDim_eq _ U.2.isoSpec.hom.homeomorph.isHomeomorph]
    exact (topologicalKrullDim_subspace_le X U).trans h
/-
**AlgebraicGeometry.IsLocallyArtinian.of_isLocallyNoetherian_of_discreteTopology
** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.IsLocallyArtinian`。
形式化陈述：∀ {X : AlgebraicGeometry.Scheme} [AlgebraicGeometry.IsLocallyNoetherian X]
 [DiscreteTopology ↥X],   AlgebraicGeometry.IsLocallyArtinian X
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.IsLocallyArtinian.of_topologicalKrullDim_le_zero`：∀ {X
 : AlgebraicGeometry.Scheme} [AlgebraicGeometry.IsLocallyNoetherian X],   topolo
gicalKrullDim ↥X ≤ 0 → AlgebraicGeometry.IsLocallyArtini…
· 使用定理 `topologicalKrullDim_zero_of_discreteTopology`：topologicalKrullDim_zero_o
f_discreteTopology (X : Type*) [TopologicalSpace X] [DiscreteTopology X] : topol
ogicalKrullDim X <= 0
-/
theorem IsLocallyArtinian.of_isLocallyNoetherian_of_discreteTopology
    [IsLocallyNoetherian X] [DiscreteTopology X] :
    IsLocallyArtinian X :=
  .of_topologicalKrullDim_le_zero (topologicalKrullDim_zero_of_discreteTopology X)

/-- See `isLocallyArtinian_of_isImmersion`. -/
/-
**AlgebraicGeometry.IsLocallyArtinian.of_isOpenImmersion** 是 Mathlib 中的一个引理，位于命名
空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See `isLocallyArtinian_of_isImmersion`.
-/
private lemma IsLocallyArtinian.of_isOpenImmersion [IsOpenImmersion f] [IsLocallyArtinian Y] :
    IsLocallyArtinian X where
  isArtinianRing_presheaf_obj U :=
    have : IsArtinianRing ↑Γ(Y, f ''ᵁ ↑U) :=
      IsLocallyArtinian.isArtinianRing_presheaf_obj ⟨_, U.2.image_of_isOpenImmersion f⟩
    (f.appIso U).commRingCatIsoToRingEquiv.surjective.isArtinianRing
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsLocallyArtinian X] {U : X.Opens} : IsLocallyArtinian U := .of_isOpenImmersion U.ι
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsLocallyArtinian X] {U : X.OpenCover} (i) : IsLocallyArtinian (U.X i) :=
  .of_isOpenImmersion (U.f i)

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) IsLocallyArtinian.discreteTopology [IsLocallyArtinian X] :
    DiscreteTopology X := by
  apply discreteTopology_iff_isOpen_singleton.mpr
  intro x
  obtain ⟨W, hW1, hW2, _⟩ := exists_isAffineOpen_mem_and_subset (TopologicalSpace.Opens.mem_top x)
  have : IsArtinianRing Γ(X, W) := IsLocallyArtinian.isArtinianRing_presheaf_obj ⟨_, hW1⟩
  have : DiscreteTopology (Spec Γ(X, W)) := inferInstanceAs (DiscreteTopology (PrimeSpectrum _))
  have : DiscreteTopology W := hW1.isoSpec.hom.homeomorph.symm.discreteTopology
  simpa using (isOpen_discrete ({⟨x, hW2⟩} : Set W)).trans W.2

@[deprecated (since := "2026-01-14")]
alias IsLocallyArtinian.discreteTopology_of_isAffine := IsLocallyArtinian.discreteTopology
/-
**AlgebraicGeometry.IsLocallyArtinian.iff_isLocallyNoetherian_and_discreteTopolo
gy** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.IsLocallyArtinian`。
形式化陈述：∀ {X : AlgebraicGeometry.Scheme},   AlgebraicGeometry.IsLocallyArtinian X 
↔ AlgebraicGeometry.IsLocallyNoetherian X ∧ DiscreteTopology ↥X
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.IsLocallyArtinian.isLocallyNoetherian`：∀ {X : Algebrai
cGeometry.Scheme} [h : AlgebraicGeometry.IsLocallyArtinian X], AlgebraicGeometry
.IsLocallyNoetherian X
· 使用定理 `AlgebraicGeometry.IsLocallyArtinian.discreteTopology`：∀ {X : AlgebraicGe
ometry.Scheme} [AlgebraicGeometry.IsLocallyArtinian X], DiscreteTopology ↥X
· 使用定理 `AlgebraicGeometry.IsLocallyArtinian.of_isLocallyNoetherian_of_discreteTo
pology`：∀ {X : AlgebraicGeometry.Scheme} [AlgebraicGeometry.IsLocallyNoetherian 
X] [DiscreteTopology ↥X],   AlgebraicGeometry.IsLocallyArtinian X
-/
theorem IsLocallyArtinian.iff_isLocallyNoetherian_and_discreteTopology :
    IsLocallyArtinian X ↔ IsLocallyNoetherian X ∧ DiscreteTopology X :=
  ⟨fun _ ↦ ⟨inferInstance, inferInstance⟩, fun ⟨_, _⟩ ↦ .of_isLocallyNoetherian_of_discreteTopology⟩

-- This can be extended to locally quasi-finite morphisms.
/-
**AlgebraicGeometry.IsLocallyArtinian.of_isImmersion** 是 Mathlib 中的一个定理，位于命名空间 `
AlgebraicGeometry.IsLocallyArtinian`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.IsImmers
ion f]   [AlgebraicGeometry.IsLocallyArtinian Y], AlgebraicGeometry.IsLocallyArt
inian X
参数：f : X ⟶ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `AlgebraicGeometry.IsLocallyArtinian.iff_isLocallyNoetherian_and_discrete
Topology`：∀ {X : AlgebraicGeometry.Scheme},   AlgebraicGeometry.IsLocallyArtinia
n X ↔ AlgebraicGeometry.IsLocallyNoetherian X ∧ DiscreteTopology ↥X
· 使用定理 `AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian`：∀ {X Y : Alge
braicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.LocallyOfFiniteType f]   [A
lgebraicGeometry.IsLocallyNoetherian Y], Algebr…
· 使用定理 `AlgebraicGeometry.IsImmersion.instLocallyOfFiniteType`：∀ {X Y : Algebrai
cGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.IsImmersion f],   AlgebraicGeom
etry.LocallyOfFiniteType f
· 使用定理 `AlgebraicGeometry.IsLocallyArtinian.isLocallyNoetherian`：∀ {X : Algebrai
cGeometry.Scheme} [h : AlgebraicGeometry.IsLocallyArtinian X], AlgebraicGeometry
.IsLocallyNoetherian X
· 使用定理 `Topology.IsEmbedding.discreteTopology`：∀ {X : Type u_1} {Y : Type u_2} {
f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   [Discrete
Topology Y], Topology.IsEmb…
· 使用定理 `AlgebraicGeometry.IsLocallyArtinian.discreteTopology`：∀ {X : AlgebraicGe
ometry.Scheme} [AlgebraicGeometry.IsLocallyArtinian X], DiscreteTopology ↥X
· 使用定理 `AlgebraicGeometry.Scheme.Hom.isEmbedding`：∀ {X Y : AlgebraicGeometry.Sch
eme} (f : X ⟶ Y) [self : AlgebraicGeometry.IsPreimmersion f], Topology.IsEmbeddi
ng ⇑f
· 使用定理 `AlgebraicGeometry.IsImmersion.toIsPreimmersion`：∀ {X Y : AlgebraicGeomet
ry.Scheme} {f : X ⟶ Y} [self : AlgebraicGeometry.IsImmersion f],   AlgebraicGeom
etry.IsPreimmersion f
-/
theorem IsLocallyArtinian.of_isImmersion [IsImmersion f] [IsLocallyArtinian Y] :
    IsLocallyArtinian X :=
  iff_isLocallyNoetherian_and_discreteTopology.mpr
    ⟨LocallyOfFiniteType.isLocallyNoetherian f, f.isEmbedding.discreteTopology⟩

/-- A commutative ring `R` is Artinian if and only if `Spec R` is an Artinian scheme. -/
/-
**AlgebraicGeometry.Scheme.isLocallyArtinianScheme_Spec** 是 Mathlib 中的一个定理，位于命名空
间 `AlgebraicGeometry.Scheme`。
形式化陈述：∀ {R : CommRingCat}, AlgebraicGeometry.IsLocallyArtinian (AlgebraicGeometr
y.Spec R) ↔ IsArtinianRing ↑R
参数：AlgebraicGeometry.Spec R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquiv.isArtinianRing`：RingEquiv.isArtinianRing {R S} [Semiring R] [S
emiring S] (f : R ≃+* S) [IsArtinianRing R] : IsArtinianRing S
· 使用定理 `AlgebraicGeometry.IsLocallyArtinian.isArtinianRing_of_isAffine`：∀ {X : A
lgebraicGeometry.Scheme} [h : AlgebraicGeometry.IsLocallyArtinian X] [AlgebraicG
eometry.IsAffine X],   IsArtinianRing ↑(X.presheaf.o…
· 使用定理 `AlgebraicGeometry.IsLocallyArtinian.of_topologicalKrullDim_le_zero`：∀ {X
 : AlgebraicGeometry.Scheme} [AlgebraicGeometry.IsLocallyNoetherian X],   topolo
gicalKrullDim ↥X ≤ 0 → AlgebraicGeometry.IsLocallyArtini…
· 使用定理 `AlgebraicGeometry.instIsLocallyNoetherianSpecOfIsNoetherianRingCarrier`：
∀ {R : CommRingCat} [IsNoetherianRing ↑R], AlgebraicGeometry.IsLocallyNoetherian
 (AlgebraicGeometry.Spec R)
· 使用定理 `instIsNoetherianRingOfIsArtinianRing`：∀ (R : Type u_2) [inst : Ring R] [
IsArtinianRing R], IsNoetherianRing R
· 使用定理 `topologicalKrullDim_zero_of_discreteTopology`：topologicalKrullDim_zero_o
f_discreteTopology (X : Type*) [TopologicalSpace X] [DiscreteTopology X] : topol
ogicalKrullDim X <= 0
· 使用定理 `IsArtinianRing.instDiscreteTopologyPrimeSpectrum`：∀ (R : Type u_1) [inst
 : CommRing R] [IsArtinianRing R], DiscreteTopology (PrimeSpectrum R)

--- 原说明 ---
A commutative ring `R` is Artinian if and only if `Spec R` is an Artinian scheme
.
-/
@[simp] theorem Scheme.isLocallyArtinianScheme_Spec {R : CommRingCat} :
    IsLocallyArtinian (Spec R) ↔ IsArtinianRing R where
  mp _ := (AlgebraicGeometry.Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.isArtinianRing
  mpr _ := .of_topologicalKrullDim_le_zero
    (topologicalKrullDim_zero_of_discreteTopology (PrimeSpectrum _))
/-
**AlgebraicGeometry.isLocallyArtinian_iff_openCover** 是 Mathlib 中的一个定理，位于命名空间 `A
lgebraicGeometry`。
形式化陈述：isLocallyArtinian_iff_openCover (𝒰 : X.OpenCover) : IsLocallyArtinian X ↔ 
forall (i : 𝒰.I₀), IsLocallyArtinian (𝒰.X i)
参数：𝒰 : X.OpenCover。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.instIsLocallyArtinianXScheme`：∀ {X : AlgebraicGeometry
.Scheme} [AlgebraicGeometry.IsLocallyArtinian X] {U : X.OpenCover} (i : U.I₀),  
 AlgebraicGeometry.IsLocallyArtinian…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `AlgebraicGeometry.IsLocallyArtinian.iff_isLocallyNoetherian_and_discrete
Topology`：∀ {X : AlgebraicGeometry.Scheme},   AlgebraicGeometry.IsLocallyArtinia
n X ↔ AlgebraicGeometry.IsLocallyNoetherian X ∧ DiscreteTopology ↥X
· 使用定理 `AlgebraicGeometry.isLocallyNoetherian_iff_openCover`：isLocallyNoetherian
_iff_openCover (𝒰 : Scheme.OpenCover X) : IsLocallyNoetherian X ↔ forall (i : 𝒰.
I₀), IsLocallyNoetherian (𝒰.X i)
· 使用定理 `AlgebraicGeometry.IsLocallyArtinian.isLocallyNoetherian`：∀ {X : Algebrai
cGeometry.Scheme} [h : AlgebraicGeometry.IsLocallyArtinian X], AlgebraicGeometry
.IsLocallyNoetherian X
· 使用定理 `discreteTopology_iff_isOpen_singleton`：discreteTopology_iff_isOpen_singl
eton [TopologicalSpace α] : DiscreteTopology α ↔ (forall a : α, IsOpen ({a} : Se
t α))
· 使用定理 `AlgebraicGeometry.Scheme.Cover.exists_eq`：∀ {K : CategoryTheory.Precover
age AlgebraicGeometry.Scheme} {X : AlgebraicGeometry.Scheme}   [AlgebraicGeometr
y.Scheme.JointlySurjective K] …
· 使用定理 `AlgebraicGeometry.Scheme.instJointlySurjectivePrecoverage`：∀ {P : Catego
ryTheory.MorphismProperty AlgebraicGeometry.Scheme},   AlgebraicGeometry.Scheme.
JointlySurjective (AlgebraicGeometry.Scheme.pre…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用定理 `Topology.IsOpenEmbedding.isOpenMap`：∀ {X : Type u_1} {Y : Type u_2} {f :
 X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.Is
OpenEmbedding f → IsOpen…
· 使用定理 `AlgebraicGeometry.Scheme.Hom.isOpenEmbedding`：isOpenEmbedding : IsOpenEm
bedding f
· 使用定理 `AlgebraicGeometry.Scheme.instIsOpenImmersionF`：∀ {X : AlgebraicGeometry.
Scheme} (𝒰 : X.OpenCover) (i : 𝒰.I₀), AlgebraicGeometry.IsOpenImmersion (𝒰.f i)
· 使用定理 `isOpen_discrete`：isOpen_discrete (s : Set α) : IsOpen s
· 使用定理 `AlgebraicGeometry.IsLocallyArtinian.discreteTopology`：∀ {X : AlgebraicGe
ometry.Scheme} [AlgebraicGeometry.IsLocallyArtinian X], DiscreteTopology ↥X
-/
theorem isLocallyArtinian_iff_openCover (𝒰 : X.OpenCover) :
    IsLocallyArtinian X ↔ ∀ (i : 𝒰.I₀), IsLocallyArtinian (𝒰.X i) := by
  refine ⟨fun h ↦ inferInstance, fun H ↦ ?_⟩
  refine IsLocallyArtinian.iff_isLocallyNoetherian_and_discreteTopology.mpr ⟨?_, ?_⟩
  · exact (isLocallyNoetherian_iff_openCover 𝒰).mpr inferInstance
  · refine discreteTopology_iff_isOpen_singleton.mpr fun x ↦ ?_
    obtain ⟨i, x, rfl⟩ := 𝒰.exists_eq x
    simpa using (𝒰.f i).isOpenEmbedding.isOpenMap _ (isOpen_discrete {x})

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.isLocallyArtinian_iff_of_isOpenCover** 是 Mathlib 中的一个定理，位于命名
空间 `AlgebraicGeometry`。
形式化陈述：isLocallyArtinian_iff_of_isOpenCover {ι : Type*} {U : ι -> X.Opens} (hU : 
TopologicalSpace.IsOpenCover U) (hU' : forall i, IsAffineOpen (U i)) : IsLocally
Artinian X ↔ forall i, IsArtinianRing Γ(X, U i)
参数：hU : TopologicalSpace.IsOpenCover U；hU' : forall i, IsAffineOpen (U i)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.IsLocallyArtinian.isArtinianRing_presheaf_obj`：∀ {X : 
AlgebraicGeometry.Scheme} [self : AlgebraicGeometry.IsLocallyArtinian X] (U : ↑X
.affineOpens),   IsArtinianRing ↑(X.presheaf.obj (Opp…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.isLocallyArtinian_iff_openCover`：isLocallyArtinian_iff
_openCover (𝒰 : X.OpenCover) : IsLocallyArtinian X ↔ forall (i : 𝒰.I₀), IsLocall
yArtinian (𝒰.X i)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `AlgebraicGeometry.IsLocallyArtinian.of_isImmersion`：∀ {X Y : AlgebraicGe
ometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.IsImmersion f]   [AlgebraicGeometr
y.IsLocallyArtinian Y], AlgebraicGeometr…
· 使用定理 `AlgebraicGeometry.IsImmersion.instOfIsClosedImmersion`：∀ {X Y : Algebrai
cGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.IsClosedImmersion f], Algebraic
Geometry.IsImmersion f
· 使用定理 `AlgebraicGeometry.IsClosedImmersion.instOfIsIsoScheme`：∀ {X Y : Algebrai
cGeometry.Scheme} (f : X ⟶ Y) [CategoryTheory.IsIso f], AlgebraicGeometry.IsClos
edImmersion f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
-/
theorem isLocallyArtinian_iff_of_isOpenCover {ι : Type*} {U : ι → X.Opens}
    (hU : TopologicalSpace.IsOpenCover U) (hU' : ∀ i, IsAffineOpen (U i)) :
    IsLocallyArtinian X ↔ ∀ i, IsArtinianRing Γ(X, U i) := by
  refine ⟨fun _ _ ↦ IsLocallyArtinian.isArtinianRing_presheaf_obj ⟨_, hU' _⟩, fun H ↦ ?_⟩
  rw [isLocallyArtinian_iff_openCover (X.openCoverOfIsOpenCover U hU)]
  have : ∀ i, IsLocallyArtinian (Spec Γ(X, U i)) := by simpa
  exact fun i ↦ .of_isImmersion (hU' _).isoSpec.hom
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) {X : Scheme} [IsEmpty X] : IsLocallyArtinian X where

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) {X : Scheme} [DiscreteTopology X] [IsReduced X] :
    IsLocallyArtinian X := by
  wlog hX : Subsingleton X generalizing X
  · let 𝒰 : X.OpenCover := X.openCoverOfIsOpenCover
      (fun x : X ↦ ⟨{x}, isOpen_discrete _⟩) (.mk (by ext; simp))
    have inst (i : _) : DiscreteTopology (𝒰.X i) := (𝒰.f i).isOpenEmbedding.discreteTopology
    have inst (i : _) : IsReduced (𝒰.X i) := isReduced_of_isOpenImmersion (𝒰.f i)
    exact (isLocallyArtinian_iff_openCover 𝒰).mpr
      fun i ↦ this (inferInstanceAs (Subsingleton ({i} : Set X)))
  cases isEmpty_or_nonempty X
  · infer_instance
  have : IsIntegral X := (isIntegral_iff_irreducibleSpace_and_isReduced _).mpr
    ⟨⟨inferInstance⟩, inferInstance⟩
  let := (isField_of_isIntegral_of_subsingleton X).toField
  have : IsLocallyArtinian (Spec Γ(X, ⊤)) := Scheme.isLocallyArtinianScheme_Spec.mpr inferInstance
  exact .of_isImmersion X.isoSpec.hom

/-- A scheme is Artinian if it is locally Artinian and quasi-compact -/
@[mk_iff]
/-
**AlgebraicGeometry.IsArtinianScheme** 是 Mathlib 中的一个归纳类型，位于命名空间 `AlgebraicGeome
try`。
形式化陈述：AlgebraicGeometry.Scheme → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A scheme is Artinian if it is locally Artinian and quasi-compact
-/
class IsArtinianScheme (X : Scheme.{u}) : Prop extends IsLocallyArtinian X, CompactSpace X

/-- The underlying type of an Artinian Scheme is finite -/
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The underlying type of an Artinian Scheme is finite
-/
instance (priority := low) IsArtinianScheme.finite [IsArtinianScheme X] :
    Finite X := finite_of_compact_of_discrete
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) IsArtinianScheme.isNoetherianScheme [IsArtinianScheme X] :
    IsNoetherian X where

/-- A scheme is Artinian if and only if it is Noetherian and has the discrete topology. -/
/-
**AlgebraicGeometry.IsArtinianScheme.iff_isNoetherian_and_discreteTopology** 是 M
athlib 中的一个定理，位于命名空间 `AlgebraicGeometry.IsArtinianScheme`。
形式化陈述：∀ {X : AlgebraicGeometry.Scheme},   AlgebraicGeometry.IsArtinianScheme X ↔
 AlgebraicGeometry.IsNoetherian X ∧ DiscreteTopology ↥X
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p

--- 原说明 ---
A scheme is Artinian if and only if it is Noetherian and has the discrete topolo
gy.
-/
theorem IsArtinianScheme.iff_isNoetherian_and_discreteTopology :
    IsArtinianScheme X ↔ IsNoetherian X ∧ DiscreteTopology X := by
  aesop (add simp [isArtinianScheme_iff, isNoetherian_iff,
    IsLocallyArtinian.iff_isLocallyNoetherian_and_discreteTopology])
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R : CommRingCat} [IsArtinianRing R] :
    IsArtinianScheme (Spec R) :=
  IsArtinianScheme.iff_isNoetherian_and_discreteTopology.mpr
    ⟨inferInstance, inferInstanceAs (DiscreteTopology (PrimeSpectrum R))⟩

/-- Spec of a field is artinian. -/
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Spec of a field is artinian.
-/
instance (priority := low) {X : Scheme} [Subsingleton X] [IsReduced X] :
    IsArtinianScheme X where

/-- A commutative ring `R` is Artinian if and only if `Spec R` is an Artinian scheme -/
/-
**AlgebraicGeometry.Scheme.isArtinianScheme_Spec** 是 Mathlib 中的一个定理，位于命名空间 `Alge
braicGeometry.Scheme`。
形式化陈述：∀ {R : CommRingCat}, AlgebraicGeometry.IsArtinianScheme (AlgebraicGeometry
.Spec R) ↔ IsArtinianRing ↑R
参数：AlgebraicGeometry.Spec R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `AlgebraicGeometry.Scheme.compactSpace_of_isAffine`：∀ (X : AlgebraicGeome
try.Scheme) [AlgebraicGeometry.IsAffine X], CompactSpace ↥X
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A commutative ring `R` is Artinian if and only if `Spec R` is an Artinian scheme
-/
theorem Scheme.isArtinianScheme_Spec {R : CommRingCat} :
    IsArtinianScheme (Spec R) ↔ IsArtinianRing R := by
  simp [isArtinianScheme_iff, (inferInstance : CompactSpace (Spec R))]

end AlgebraicGeometry

