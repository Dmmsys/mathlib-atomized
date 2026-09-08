/-
Copyright (c) 2024 Geno Racklin Asher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geno Racklin Asher
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.RingTheory.Localization.Submodule
public import Mathlib.RingTheory.Spectrum.Prime.Noetherian

/-!
# Noetherian and Locally Noetherian Schemes

We introduce the concept of (locally) Noetherian schemes,
giving definitions, equivalent conditions, and basic properties.

## Main definitions

* `AlgebraicGeometry.IsLocallyNoetherian`: A scheme is locally Noetherian
  if the components of the structure sheaf at each affine open are Noetherian rings.

* `AlgebraicGeometry.IsNoetherian`: A scheme is Noetherian if it is locally Noetherian
  and quasi-compact as a topological space.

## Main results

* `AlgebraicGeometry.isLocallyNoetherian_iff_of_affine_openCover`: A scheme is locally Noetherian
  if and only if it is covered by affine opens whose sections are Noetherian rings.

* `AlgebraicGeometry.IsLocallyNoetherian.quasiSeparatedSpace`: A locally Noetherian scheme is
  quasi-separated.

* `AlgebraicGeometry.isNoetherian_iff_of_finite_affine_openCover`: A scheme is Noetherian
  if and only if it is covered by finitely many affine opens whose sections are Noetherian rings.

* `AlgebraicGeometry.IsNoetherian.noetherianSpace`: A Noetherian scheme is
  topologically a Noetherian space.

## References

* [Stacks: Noetherian Schemes](https://stacks.math.columbia.edu/tag/01OU)
* [Robin Hartshorne, *Algebraic Geometry*][Har77]

-/

public section

universe u v

open Opposite AlgebraicGeometry Localization IsLocalization TopologicalSpace CategoryTheory

namespace AlgebraicGeometry

/-- A scheme `X` is locally Noetherian if `𝒪ₓ(U)` is Noetherian for all affine `U`. -/
/-
**AlgebraicGeometry.IsLocallyNoetherian** 是 Mathlib 中的一个类，位于命名空间 `AlgebraicGeome
try`。
形式化陈述：IsLocallyNoetherian (X : Scheme) : Prop where component_noetherian : foral
l (U : X.affineOpens), IsNoetherianRing Γ(X, U)
参数：X : Scheme。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A scheme `X` is locally Noetherian if `𝒪ₓ(U)` is Noetherian for all affine `U`.
-/
class IsLocallyNoetherian (X : Scheme) : Prop where
  component_noetherian : ∀ (U : X.affineOpens),
    IsNoetherianRing Γ(X, U) := by infer_instance

section localizationProps

variable {R : Type u} [CommRing R] (S : Finset R) (hS : Ideal.span (α := R) S = ⊤)
  (hN : ∀ s : S, IsNoetherianRing (Away (M := R) s))

include hS hN in
/-- Let `R` be a ring, and `f i` a finite collection of elements of `R` generating the unit ideal.
If the localization of `R` at each `f i` is Noetherian, so is `R`.

We follow the proof given in [Har77], Proposition II.3.2 -/
/-
**AlgebraicGeometry.isNoetherianRing_of_away** 是 Mathlib 中的一个定理，位于命名空间 `Algebrai
cGeometry`。
形式化陈述：isNoetherianRing_of_away : IsNoetherianRing R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `monotone_stabilizes_iff_noetherian`：monotone_stabilizes_iff_noetherian :
 (forall f : Nat ->o Submodule R M, exists n, forall m, n <= m -> f n = f m) ↔ I
sNoetherian R M
· 使用定理 `Nat.sInf_mem`：sInf_mem {s : Set Nat} (h : s.Nonempty) : sInf s in s
· 使用定理 `Ideal.map_mono`：map_mono (h : I <= J) : map f I <= map f J
· 使用定理 `OrderHom.monotone`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [
inst_1 : Preorder β] (f : α →o β), Monotone ⇑f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.le_sup`：le_sup {b : β} (hb : b in s) : f b <= s.sup f
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsLocalization.ideal_eq_iInf_under_map_away`：ideal_eq_iInf_under_map_awa
y {S : Finset R} (hS : Ideal.span (α
· 使用定理 `iInf_subtype'`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α
] {p : ι → Prop} {f : (i : ι) → p i → α},   ⨅ i, ⨅ (h : p i), f i h = ⨅ x, f ↑x 
⋯
· 使用定理 `iInf_congr`：∀ {α : Type u_1} {ι : Sort u_4} [inst : InfSet α] {f g : ι →
 α}, (∀ (i : ι), f i = g i) → ⨅ i, f i = ⨅ i, g i
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.le_trans`：∀ {n m k : ℕ}, n ≤ m → m ≤ k → n ≤ k

--- 原说明 ---
Let `R` be a ring, and `f i` a finite collection of elements of `R` generating t
he unit ideal.
If the localization of `R` at each `f i` is Noetherian, so is `R`.

We follow the proof given in [Har77], Proposition II.3.2
-/
theorem isNoetherianRing_of_away : IsNoetherianRing R := by
  apply monotone_stabilizes_iff_noetherian.mp
  intro I
  let floc s := algebraMap R (Away (M := R) s)
  let suitableN s :=
    { n : ℕ | ∀ m : ℕ, n ≤ m → (Ideal.map (floc s) (I n)) = (Ideal.map (floc s) (I m)) }
  let minN s := sInf (suitableN s)
  have hSuit : ∀ s : S, minN s ∈ suitableN s := by
    intro s
    apply Nat.sInf_mem
    let f : ℕ →o Ideal (Away (M := R) s) :=
      ⟨fun n ↦ Ideal.map (floc s) (I n), fun _ _ h ↦ Ideal.map_mono (I.monotone h)⟩
    exact monotone_stabilizes_iff_noetherian.mpr (hN s) f
  let N := Finset.sup S minN
  use N
  have hN : ∀ s : S, minN s ≤ N := fun s => Finset.le_sup s.prop
  intro n hn
  rw [IsLocalization.ideal_eq_iInf_under_map_away hS (I N),
      IsLocalization.ideal_eq_iInf_under_map_away hS (I n),
      iInf_subtype', iInf_subtype']
  apply iInf_congr
  intro s
  congr 1
  rw [← hSuit s N (hN s)]
  exact hSuit s n <| Nat.le_trans (hN s) hn

end localizationProps

variable {X : Scheme}

/-- If a scheme `X` has a cover by affine opens whose sections are Noetherian rings,
then `X` is locally Noetherian. -/
/-
**AlgebraicGeometry.isLocallyNoetherian_of_affine_cover** 是 Mathlib 中的一个定理，位于命名空
间 `AlgebraicGeometry`。
形式化陈述：isLocallyNoetherian_of_affine_cover {ι} {S : ι -> X.affineOpens} (hS : (⨆ 
i, S i : X.Opens) = ⊤) (hS' : forall i, IsNoetherianRing Γ(X, S i)) : IsLocallyN
oetherian X
参数：hS : (⨆ i, S i : X.Opens) = ⊤；hS' : forall i, IsNoetherianRing Γ(X, S i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.of_affine_open_cover`：of_affine_open_cover {X : Scheme
} {P : X.affineOpens -> Prop} {ι} (U : ι -> X.affineOpens) (iSup_U : (⨆ i, U i :
 X.Opens) = ⊤) (V : X.affine…
· 使用定理 `AlgebraicGeometry.IsAffineOpen.isLocalization_basicOpen`：isLocalization_
basicOpen : IsLocalization.Away f Γ(X, X.basicOpen f)
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `IsLocalization.isNoetherianRing`：isNoetherianRing (h : IsNoetherianRing 
R) : IsNoetherianRing S
· 使用定理 `AlgebraicGeometry.isNoetherianRing_of_away`：isNoetherianRing_of_away : I
sNoetherianRing R
· 使用定理 `isNoetherianRing_of_ringEquiv`：isNoetherianRing_of_ringEquiv (R) [Semiri
ng R] {S} [Semiring S] (f : R ≃+* S) [IsNoetherianRing R] : IsNoetherianRing S

--- 原说明 ---
If a scheme `X` has a cover by affine opens whose sections are Noetherian rings,
then `X` is locally Noetherian.
-/
theorem isLocallyNoetherian_of_affine_cover {ι} {S : ι → X.affineOpens}
    (hS : (⨆ i, S i : X.Opens) = ⊤)
    (hS' : ∀ i, IsNoetherianRing Γ(X, S i)) : IsLocallyNoetherian X := by
  refine ⟨fun U => ?_⟩
  induction U using of_affine_open_cover S hS with
  | basicOpen U f hN =>
    have := U.prop.isLocalization_basicOpen f
    exact IsLocalization.isNoetherianRing (.powers f) Γ(X, X.basicOpen f) hN
  | openCover U s _ hN =>
    apply isNoetherianRing_of_away s ‹_›
    intro ⟨f, hf⟩
    have : IsNoetherianRing Γ(X, X.basicOpen f) := hN ⟨f, hf⟩
    have := U.prop.isLocalization_basicOpen f
    have hEq := IsLocalization.algEquiv (.powers f) (Localization.Away f) Γ(X, X.basicOpen f)
    exact isNoetherianRing_of_ringEquiv Γ(X, X.basicOpen f) hEq.symm.toRingEquiv
  | hU => exact hS' _

/-- A scheme is locally Noetherian if and only if it is covered by affine opens whose sections
are Noetherian rings.

See [Har77], Proposition II.3.2. -/
/-
**AlgebraicGeometry.isLocallyNoetherian_iff_of_iSup_eq_top** 是 Mathlib 中的一个定理，位于
命名空间 `AlgebraicGeometry`。
形式化陈述：isLocallyNoetherian_iff_of_iSup_eq_top {ι} {S : ι -> X.affineOpens} (hS : 
(⨆ i, S i : X.Opens) = ⊤) : IsLocallyNoetherian X ↔ forall i, IsNoetherianRing Γ
(X, S i)
参数：hS : (⨆ i, S i : X.Opens) = ⊤。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.IsLocallyNoetherian.component_noetherian`：∀ {X : Algeb
raicGeometry.Scheme} [self : AlgebraicGeometry.IsLocallyNoetherian X] (U : ↑X.af
fineOpens),   IsNoetherianRing ↑(X.presheaf.obj …
· 使用定理 `AlgebraicGeometry.isLocallyNoetherian_of_affine_cover`：isLocallyNoetheri
an_of_affine_cover {ι} {S : ι -> X.affineOpens} (hS : (⨆ i, S i : X.Opens) = ⊤) 
(hS' : forall i, IsNoetherianRing Γ(X, S i)…

--- 原说明 ---
A scheme is locally Noetherian if and only if it is covered by affine opens whos
e sections
are Noetherian rings.

See [Har77], Proposition II.3.2.
-/
theorem isLocallyNoetherian_iff_of_iSup_eq_top {ι} {S : ι → X.affineOpens}
    (hS : (⨆ i, S i : X.Opens) = ⊤) :
    IsLocallyNoetherian X ↔ ∀ i, IsNoetherianRing Γ(X, S i) :=
  ⟨fun _ i => IsLocallyNoetherian.component_noetherian (S i),
   isLocallyNoetherian_of_affine_cover hS⟩

/-- A version of `isLocallyNoetherian_iff_of_iSup_eq_top` using `Scheme.OpenCover`. -/
/-
**AlgebraicGeometry.isLocallyNoetherian_iff_of_affine_openCover** 是 Mathlib 中的一个
定理，位于命名空间 `AlgebraicGeometry`。
形式化陈述：isLocallyNoetherian_iff_of_affine_openCover (𝒰 : Scheme.OpenCover.{v, u} X
) [forall i, IsAffine (𝒰.X i)] : IsLocallyNoetherian X ↔ forall (i : 𝒰.I₀), IsNo
etherianRing Γ(𝒰.X i, ⊤)
参数：𝒰 : Scheme.OpenCover.{v, u} X；𝒰.X i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.instIsOpenImmersionF`：∀ {X : AlgebraicGeometry.
Scheme} (𝒰 : X.OpenCover) (i : 𝒰.I₀), AlgebraicGeometry.IsOpenImmersion (𝒰.f i)
· 使用定理 `AlgebraicGeometry.isAffineOpen_opensRange`：isAffineOpen_opensRange {X Y 
: Scheme} [IsAffine X] (f : X ⟶ Y) [H : IsOpenImmersion f] : IsAffineOpen f.open
sRange
· 使用定理 `AlgebraicGeometry.IsLocallyNoetherian.component_noetherian`：∀ {X : Algeb
raicGeometry.Scheme} [self : AlgebraicGeometry.IsLocallyNoetherian X] (U : ↑X.af
fineOpens),   IsNoetherianRing ↑(X.presheaf.obj …
· 使用定理 `isNoetherianRing_of_ringEquiv`：isNoetherianRing_of_ringEquiv (R) [Semiri
ng R] {S} [Semiring S] (f : R ≃+* S) [IsNoetherianRing R] : IsNoetherianRing S
· 使用定理 `AlgebraicGeometry.isLocallyNoetherian_of_affine_cover`：isLocallyNoetheri
an_of_affine_cover {ι} {S : ι -> X.affineOpens} (hS : (⨆ i, S i : X.Opens) = ⊤) 
(hS' : forall i, IsNoetherianRing Γ(X, S i)…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.Scheme.OpenCover.iSup_opensRange`：∀ {X : AlgebraicGeom
etry.Scheme} (𝒰 : X.OpenCover), ⨆ i, AlgebraicGeometry.Scheme.Hom.opensRange (𝒰.
f i) = ⊤

--- 原说明 ---
A version of `isLocallyNoetherian_iff_of_iSup_eq_top` using `Scheme.OpenCover`.
-/
theorem isLocallyNoetherian_iff_of_affine_openCover (𝒰 : Scheme.OpenCover.{v, u} X)
    [∀ i, IsAffine (𝒰.X i)] :
    IsLocallyNoetherian X ↔ ∀ (i : 𝒰.I₀), IsNoetherianRing Γ(𝒰.X i, ⊤) := by
  constructor
  · intro h i
    let U := Scheme.Hom.opensRange (𝒰.f i)
    have := h.component_noetherian ⟨U, isAffineOpen_opensRange _⟩
    apply isNoetherianRing_of_ringEquiv (R := Γ(X, U))
    apply CategoryTheory.Iso.commRingCatIsoToRingEquiv
    exact (IsOpenImmersion.ΓIsoTop (𝒰.f i)).symm
  · intro hCNoeth
    let fS i : X.affineOpens := ⟨Scheme.Hom.opensRange (𝒰.f i), isAffineOpen_opensRange _⟩
    apply isLocallyNoetherian_of_affine_cover (S := fS)
    · rw [← Scheme.OpenCover.iSup_opensRange 𝒰]
    intro i
    apply isNoetherianRing_of_ringEquiv (R := Γ(𝒰.X i, ⊤))
    apply CategoryTheory.Iso.commRingCatIsoToRingEquiv
    exact IsOpenImmersion.ΓIsoTop (𝒰.f i)

-- Also see `LocallyOfFiniteType.isLocallyNoetherian`.
/-
**AlgebraicGeometry.isLocallyNoetherian_of_isOpenImmersion** 是 Mathlib 中的一个引理，位于
命名空间 `AlgebraicGeometry`。
形式化陈述：isLocallyNoetherian_of_isOpenImmersion {Y : Scheme} (f : X ⟶ Y) [IsOpenImm
ersion f] [IsLocallyNoetherian Y] : IsLocallyNoetherian X where component_noethe
rian U
参数：f : X ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.IsLocallyNoetherian.component_noetherian`：∀ {X : Algeb
raicGeometry.Scheme} [self : AlgebraicGeometry.IsLocallyNoetherian X] (U : ↑X.af
fineOpens),   IsNoetherianRing ↑(X.presheaf.obj …
· 使用定理 `AlgebraicGeometry.IsAffineOpen.image_of_isOpenImmersion`：image_of_isOpen
Immersion (f : X ⟶ Y) [H : IsOpenImmersion f] : IsAffineOpen (f ''ᵁ U)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `isNoetherianRing_of_surjective`：isNoetherianRing_of_surjective (R) [Semi
ring R] (S) [Semiring S] (f : R ->+* S) (hf : Function.Surjective f) [H : IsNoet
herianRing R] : IsNo…
· 使用定理 `RingEquiv.surjective`：∀ {R : Type u_4} {S : Type u_5} [inst : Mul R] [in
st_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S] (e : R ≃+* S),   Function.Surjec
tive ⇑e
-/
lemma isLocallyNoetherian_of_isOpenImmersion {Y : Scheme} (f : X ⟶ Y) [IsOpenImmersion f]
    [IsLocallyNoetherian Y] : IsLocallyNoetherian X where
  component_noetherian U :=
    have : IsNoetherianRing ↑Γ(Y, f ''ᵁ ↑U) :=
      IsLocallyNoetherian.component_noetherian ⟨_, U.2.image_of_isOpenImmersion f⟩
    isNoetherianRing_of_surjective _ _ _ (f.appIso U).commRingCatIsoToRingEquiv.surjective
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {U : X.Opens} [IsLocallyNoetherian X] : IsLocallyNoetherian U :=
  isLocallyNoetherian_of_isOpenImmersion U.ι
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {U : X.OpenCover} (i) [IsLocallyNoetherian X] : IsLocallyNoetherian (U.X i) :=
  isLocallyNoetherian_of_isOpenImmersion (U.f i)

set_option backward.isDefEq.respectTransparency.types false in
/-- If `𝒰` is an open cover of a scheme `X`, then `X` is locally Noetherian if and only if
`𝒰.X i` are all locally Noetherian. -/
/-
**AlgebraicGeometry.isLocallyNoetherian_iff_openCover** 是 Mathlib 中的一个定理，位于命名空间 
`AlgebraicGeometry`。
形式化陈述：isLocallyNoetherian_iff_openCover (𝒰 : Scheme.OpenCover X) : IsLocallyNoet
herian X ↔ forall (i : 𝒰.I₀), IsLocallyNoetherian (𝒰.X i)
参数：𝒰 : Scheme.OpenCover X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.instIsLocallyNoetherianXScheme`：∀ {X : AlgebraicGeomet
ry.Scheme} {U : X.OpenCover} (i : U.I₀) [AlgebraicGeometry.IsLocallyNoetherian X
],   AlgebraicGeometry.IsLocallyNoethe…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.isLocallyNoetherian_iff_of_affine_openCover`：isLocally
Noetherian_iff_of_affine_openCover (𝒰 : Scheme.OpenCover.{v, u} X) [forall i, Is
Affine (𝒰.X i)] : IsLocallyNoetherian X ↔ forall (i…
· 使用定理 `AlgebraicGeometry.Scheme.isAffine_affineOpenCover`：∀ (X : AlgebraicGeome
try.Scheme) (𝒰 : X.AffineOpenCover) (i : 𝒰.I₀), AlgebraicGeometry.IsAffine (𝒰.op
enCover.X i)
· 使用定理 `isNoetherianRing_of_ringEquiv`：isNoetherianRing_of_ringEquiv (R) [Semiri
ng R] {S} [Semiring S] (f : R ≃+* S) [IsNoetherianRing R] : IsNoetherianRing S
· 使用定理 `AlgebraicGeometry.Scheme.instIsOpenImmersionF`：∀ {X : AlgebraicGeometry.
Scheme} (𝒰 : X.OpenCover) (i : 𝒰.I₀), AlgebraicGeometry.IsOpenImmersion (𝒰.f i)
· 使用定理 `AlgebraicGeometry.IsLocallyNoetherian.component_noetherian`：∀ {X : Algeb
raicGeometry.Scheme} [self : AlgebraicGeometry.IsLocallyNoetherian X] (U : ↑X.af
fineOpens),   IsNoetherianRing ↑(X.presheaf.obj …
· 使用定理 `AlgebraicGeometry.isAffineOpen_opensRange`：isAffineOpen_opensRange {X Y 
: Scheme} [IsAffine X] (f : X ⟶ Y) [H : IsOpenImmersion f] : IsAffineOpen f.open
sRange
· 使用定理 `AlgebraicGeometry.Scheme.isAffine_affineCover`：∀ (X : AlgebraicGeometry.
Scheme) (i : X.affineCover.I₀), AlgebraicGeometry.IsAffine (X.affineCover.X i)

--- 原说明 ---
If `𝒰` is an open cover of a scheme `X`, then `X` is locally Noetherian if and o
nly if
`𝒰.X i` are all locally Noetherian.
-/
theorem isLocallyNoetherian_iff_openCover (𝒰 : Scheme.OpenCover X) :
    IsLocallyNoetherian X ↔ ∀ (i : 𝒰.I₀), IsLocallyNoetherian (𝒰.X i) := by
  refine ⟨fun _ ↦ inferInstance, ?_⟩
  · rw [isLocallyNoetherian_iff_of_affine_openCover (𝒰 := 𝒰.affineRefinement.openCover)]
    intro h i
    exact @isNoetherianRing_of_ringEquiv _ _ _ _
      (IsOpenImmersion.ΓIsoTop (PreZeroHypercover.f _ i.2)).symm.commRingCatIsoToRingEquiv
      (IsLocallyNoetherian.component_noetherian ⟨_, isAffineOpen_opensRange _⟩)

/-- If `R` is a Noetherian ring, `Spec R` is a Noetherian topological space. -/
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `R` is a Noetherian ring, `Spec R` is a Noetherian topological space.
-/
instance {R : CommRingCat} [IsNoetherianRing R] :
    NoetherianSpace (Spec R) := by
  convert! PrimeSpectrum.instNoetherianSpace (R := R)
/-
**AlgebraicGeometry.noetherianSpace_of_isAffine** 是 Mathlib 中的一个引理，位于命名空间 `Algeb
raicGeometry`。
形式化陈述：noetherianSpace_of_isAffine [IsAffine X] [IsNoetherianRing Γ(X, ⊤)] : Noet
herianSpace X
参数：X, ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `TopologicalSpace.noetherianSpace_iff_of_homeomorph`：noetherianSpace_iff_
of_homeomorph (f : α ≃ₜ β) : NoetherianSpace α ↔ NoetherianSpace β
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `AlgebraicGeometry.instNoetherianSpaceCarrierCarrierCommRingCatSpecOfIsNo
etherianRingCarrier`：∀ {R : CommRingCat} [IsNoetherianRing ↑R], TopologicalSpace
.NoetherianSpace ↥(AlgebraicGeometry.Spec R)
-/
lemma noetherianSpace_of_isAffine [IsAffine X] [IsNoetherianRing Γ(X, ⊤)] :
    NoetherianSpace X :=
  (noetherianSpace_iff_of_homeomorph X.isoSpec.inv.homeomorph).mp inferInstance
/-
**AlgebraicGeometry.noetherianSpace_of_isAffineOpen** 是 Mathlib 中的一个引理，位于命名空间 `A
lgebraicGeometry`。
形式化陈述：noetherianSpace_of_isAffineOpen (U : X.Opens) (hU : IsAffineOpen U) [IsNoe
therianRing Γ(X, U)] : NoetherianSpace U
参数：U : X.Opens；hU : IsAffineOpen U；X, U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isNoetherianRing_of_ringEquiv`：isNoetherianRing_of_ringEquiv (R) [Semiri
ng R] {S} [Semiring S] (f : R ≃+* S) [IsNoetherianRing R] : IsNoetherianRing S
· 使用引理 `AlgebraicGeometry.noetherianSpace_of_isAffine`：noetherianSpace_of_isAffi
ne [IsAffine X] [IsNoetherianRing Γ(X, ⊤)] : NoetherianSpace X
-/
lemma noetherianSpace_of_isAffineOpen (U : X.Opens) (hU : IsAffineOpen U)
    [IsNoetherianRing Γ(X, U)] :
    NoetherianSpace U := by
  have : IsNoetherianRing Γ(U, ⊤) := isNoetherianRing_of_ringEquiv _
    (Scheme.restrictFunctorΓ.app (op U)).symm.commRingCatIsoToRingEquiv
  exact @noetherianSpace_of_isAffine _ hU _
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R : CommRingCat} [IsNoetherianRing R] : IsLocallyNoetherian (Spec R) :=
  isLocallyNoetherian_of_affine_cover (S := fun _ : Unit ↦ ⟨⊤, isAffineOpen_top (Spec R)⟩) (by simp)
    fun _ ↦ isNoetherianRing_of_ringEquiv R (Scheme.ΓSpecIso R).symm.commRingCatIsoToRingEquiv

@[simp]
/-
**AlgebraicGeometry.isLocallyNoetherian_Spec** 是 Mathlib 中的一个定理，位于命名空间 `Algebrai
cGeometry`。
形式化陈述：isLocallyNoetherian_Spec {R : CommRingCat} : IsLocallyNoetherian (Spec R) 
↔ IsNoetherianRing R where mp _
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.isAffineOpen_top`：isAffineOpen_top (X : Scheme) [IsAff
ine X] : IsAffineOpen (⊤ : X.Opens)
· 使用定理 `AlgebraicGeometry.IsLocallyNoetherian.component_noetherian`：∀ {X : Algeb
raicGeometry.Scheme} [self : AlgebraicGeometry.IsLocallyNoetherian X] (U : ↑X.af
fineOpens),   IsNoetherianRing ↑(X.presheaf.obj …
· 使用定理 `isNoetherianRing_of_ringEquiv`：isNoetherianRing_of_ringEquiv (R) [Semiri
ng R] {S} [Semiring S] (f : R ≃+* S) [IsNoetherianRing R] : IsNoetherianRing S
· 使用定理 `AlgebraicGeometry.instIsLocallyNoetherianSpecOfIsNoetherianRingCarrier`：
∀ {R : CommRingCat} [IsNoetherianRing ↑R], AlgebraicGeometry.IsLocallyNoetherian
 (AlgebraicGeometry.Spec R)
-/
theorem isLocallyNoetherian_Spec {R : CommRingCat} :
    IsLocallyNoetherian (Spec R) ↔ IsNoetherianRing R where
  mp _ :=
    have := IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top (Spec R)⟩
    isNoetherianRing_of_ringEquiv _ (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv
  mpr _ := inferInstance

/-- Any open immersion `Z ⟶ X` with `X` locally Noetherian is quasi-compact. -/
@[stacks 01OX]
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any open immersion `Z ⟶ X` with `X` locally Noetherian is quasi-compact.
-/
instance (priority := 100) {Z : Scheme} [IsLocallyNoetherian X]
    {f : Z ⟶ X} [IsOpenImmersion f] : QuasiCompact f := by
  apply quasiCompact_iff_forall_isAffineOpen.mpr
  intro U hU
  rw [Opens.map_coe, ← Set.preimage_inter_range]
  apply f.isOpenEmbedding.isInducing.isCompact_preimage'
  · apply (noetherianSpace_set_iff _).mp
    · convert! noetherianSpace_of_isAffineOpen U hU
      apply IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    · exact Set.inter_subset_left
  · exact Set.inter_subset_right

set_option backward.isDefEq.respectTransparency.types false in
/-- A locally Noetherian scheme is quasi-separated. -/
@[stacks 01OY]
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A locally Noetherian scheme is quasi-separated.
-/
instance (priority := 100) IsLocallyNoetherian.quasiSeparatedSpace [IsLocallyNoetherian X] :
    QuasiSeparatedSpace X := by
  apply quasiSeparatedSpace_iff_forall_affineOpens.mpr
  intro U V
  have hInd := U.2.fromSpec.isOpenEmbedding.isInducing
  apply (hInd.isCompact_preimage_iff ?_).mp
  · rw [← Set.preimage_inter_range, IsAffineOpen.range_fromSpec, Set.inter_comm]
    apply hInd.isCompact_preimage'
    · apply (noetherianSpace_set_iff _).mp
      · convert! noetherianSpace_of_isAffineOpen U.1 U.2
        apply IsLocallyNoetherian.component_noetherian
      · exact Set.inter_subset_left
    · rw [IsAffineOpen.range_fromSpec]
      exact Set.inter_subset_left
  · rw [IsAffineOpen.range_fromSpec]
    exact Set.inter_subset_left

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian** 是 Mathlib 中的一个定理，位
于命名空间 `AlgebraicGeometry.LocallyOfFiniteType`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.LocallyO
fFiniteType f]   [AlgebraicGeometry.IsLocallyNoetherian Y], AlgebraicGeometry.Is
LocallyNoetherian X
参数：f : X ⟶ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `AlgebraicGeometry.Spec.map_surjective`：∀ {R S : CommRingCat}, Function.S
urjective AlgebraicGeometry.Spec.map
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AlgebraicGeometry.HasRingHomProperty.Spec_iff`：Spec_iff {R S : CommRingC
at.{u}} {φ : R ⟶ S} : P (Spec.map φ) ↔ Q φ.hom
· 使用定理 `AlgebraicGeometry.instHasRingHomPropertyLocallyOfFiniteTypeFiniteType`：A
lgebraicGeometry.HasRingHomProperty @AlgebraicGeometry.LocallyOfFiniteType fun {
R S} [CommRing R] [CommRing S] =>   RingHom.FiniteType
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Algebra.FiniteType.isNoetherianRing`：isNoetherianRing (R S : Type*) [Com
mRing R] [CommRing S] [Algebra R S] [h : Algebra.FiniteType R S] [IsNoetherianRi
ng R] : IsNoetherianRing …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `AlgebraicGeometry.isLocallyNoetherian_iff_openCover`：isLocallyNoetherian
_iff_openCover (𝒰 : Scheme.OpenCover X) : IsLocallyNoetherian X ↔ forall (i : 𝒰.
I₀), IsLocallyNoetherian (𝒰.X i)
· 使用定理 `AlgebraicGeometry.instLocallyOfFiniteTypeOfLocallyOfFinitePresentation`：
∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [hf : AlgebraicGeometry.LocallyOf
FinitePresentation f],   AlgebraicGeometry.LocallyOfFiniteTy…
· 使用定理 `AlgebraicGeometry.locallyOfFinitePresentation_of_isOpenImmersion`：∀ {X Y
 : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.IsOpenImmersion f], 
  AlgebraicGeometry.LocallyOfFinitePresentation f
· 使用定理 `AlgebraicGeometry.Scheme.instIsOpenImmersionF`：∀ {X : AlgebraicGeometry.
Scheme} (𝒰 : X.OpenCover) (i : 𝒰.I₀), AlgebraicGeometry.IsOpenImmersion (𝒰.f i)
· 使用定理 `AlgebraicGeometry.Scheme.local_affine`：∀ (self : AlgebraicGeometry.Schem
e) (x : ↑self.toTopCat),   ∃ U R, Nonempty (self.restrict ⋯ ≅ AlgebraicGeometry.
Spec.toLocallyRingedSpace.o…
· 使用定理 `AlgebraicGeometry.Scheme.instIsStableUnderBaseChangePrecoverageOfIsJoint
lySurjectivePreservingOfIsStableUnderBaseChange`：∀ (P : CategoryTheory.MorphismP
roperty AlgebraicGeometry.Scheme)   [AlgebraicGeometry.Scheme.IsJointlySurjectiv
ePreserving P] [P.IsStableUnd…
· 使用定理 `AlgebraicGeometry.Scheme.instIsJointlySurjectivePreservingIsOpenImmersio
n`：AlgebraicGeometry.Scheme.IsJointlySurjectivePreserving AlgebraicGeometry.IsOp
enImmersion
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `AlgebraicGeometry.instLocallyOfFiniteTypeSndScheme`：∀ {X Y S : Algebraic
Geometry.Scheme} (f : X ⟶ S) (g : Y ⟶ S) [AlgebraicGeometry.LocallyOfFiniteType 
f],   AlgebraicGeometry.LocallyOfFiniteT…
· 使用定理 `AlgebraicGeometry.instIsLocallyNoetherianXScheme`：∀ {X : AlgebraicGeomet
ry.Scheme} {U : X.OpenCover} (i : U.I₀) [AlgebraicGeometry.IsLocallyNoetherian X
],   AlgebraicGeometry.IsLocallyNoethe…
-/
theorem LocallyOfFiniteType.isLocallyNoetherian
    {X Y : Scheme} (f : X ⟶ Y) [LocallyOfFiniteType f]
    [IsLocallyNoetherian Y] : IsLocallyNoetherian X := by
  change id (IsLocallyNoetherian X) -- avoid wlog hypotheses confusing the instance synthesizer
  wlog hY : ∃ R, Y = Spec R
  · exact (isLocallyNoetherian_iff_openCover (Y.affineCover.pullback₁ f)).mpr fun i ↦
      this (Limits.pullback.snd f (Y.affineCover.f i)) ⟨_, rfl⟩
  wlog hX : ∃ S, X = Spec S
  · exact (isLocallyNoetherian_iff_openCover X.affineCover).mpr
      fun i ↦ this (X.affineCover.f i ≫ f) hY ⟨_, rfl⟩
  obtain ⟨R, rfl⟩ := hY
  obtain ⟨S, rfl⟩ := hX
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  have : φ.hom.FiniteType := HasRingHomProperty.Spec_iff.mp ‹_›
  algebraize [φ.hom]
  simp_all [Algebra.FiniteType.isNoetherianRing R]
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S)
    [IsLocallyNoetherian Y] [LocallyOfFiniteType f] :
    IsLocallyNoetherian (Limits.pullback f g) :=
  LocallyOfFiniteType.isLocallyNoetherian (Limits.pullback.snd _ _)
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S)
    [IsLocallyNoetherian X] [LocallyOfFiniteType g] :
    IsLocallyNoetherian (Limits.pullback f g) :=
  LocallyOfFiniteType.isLocallyNoetherian (Limits.pullback.fst _ _)
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) {X Y : Scheme} (f : X ⟶ Y)
    [IsLocallyNoetherian Y] [LocallyOfFiniteType f] :
    LocallyOfFinitePresentation f := by
  refine ⟨fun {U hU V hV} hUV ↦ ?_⟩
  let := (f.appLE U V hUV).hom.toAlgebra
  have : IsNoetherianRing Γ(Y, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  exact Algebra.FinitePresentation.of_finiteType.mp (f.finiteType_appLE hU hV hUV)
/-
**AlgebraicGeometry.LocallyOfFinitePresentation.iff_locallyOfFiniteType** 是 Math
lib 中的一个定理，位于命名空间 `AlgebraicGeometry.LocallyOfFinitePresentation`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} {f : X ⟶ Y} [AlgebraicGeometry.IsLocall
yNoetherian Y],   AlgebraicGeometry.LocallyOfFinitePresentation f ↔ AlgebraicGeo
metry.LocallyOfFiniteType f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.instLocallyOfFiniteTypeOfLocallyOfFinitePresentation`：
∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [hf : AlgebraicGeometry.LocallyOf
FinitePresentation f],   AlgebraicGeometry.LocallyOfFiniteTy…
· 使用定理 `AlgebraicGeometry.instLocallyOfFinitePresentationOfIsLocallyNoetherianOf
LocallyOfFiniteType`：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGe
ometry.IsLocallyNoetherian Y]   [AlgebraicGeometry.LocallyOfFiniteType f], Algeb
r…
-/
lemma LocallyOfFinitePresentation.iff_locallyOfFiniteType {X Y : Scheme} {f : X ⟶ Y}
    [IsLocallyNoetherian Y] : LocallyOfFinitePresentation f ↔ LocallyOfFiniteType f :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ inferInstance⟩

/-- A scheme `X` is Noetherian if it is locally Noetherian and compact. -/
@[mk_iff]
/-
**AlgebraicGeometry.IsNoetherian** 是 Mathlib 中的一个归纳类型，位于命名空间 `AlgebraicGeometry`
。
形式化陈述：AlgebraicGeometry.Scheme → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A scheme `X` is Noetherian if it is locally Noetherian and compact.
-/
class IsNoetherian (X : Scheme) : Prop extends IsLocallyNoetherian X, CompactSpace X

/-- A scheme is Noetherian if and only if it is covered by finitely many affine opens whose
sections are Noetherian rings. -/
/-
**AlgebraicGeometry.isNoetherian_iff_of_finite_iSup_eq_top** 是 Mathlib 中的一个定理，位于
命名空间 `AlgebraicGeometry`。
形式化陈述：isNoetherian_iff_of_finite_iSup_eq_top {ι} [Finite ι] {S : ι -> X.affineOp
ens} (hS : (⨆ i, S i : X.Opens) = ⊤) : IsNoetherian X ↔ forall i, IsNoetherianRi
ng Γ(X, S i)
参数：hS : (⨆ i, S i : X.Opens) = ⊤。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AlgebraicGeometry.isLocallyNoetherian_iff_of_iSup_eq_top`：isLocallyNoeth
erian_iff_of_iSup_eq_top {ι} {S : ι -> X.affineOpens} (hS : (⨆ i, S i : X.Opens)
 = ⊤) : IsLocallyNoetherian X ↔ forall i, IsNo…
· 使用定理 `AlgebraicGeometry.IsNoetherian.toIsLocallyNoetherian`：∀ {X : AlgebraicGe
ometry.Scheme} [self : AlgebraicGeometry.IsNoetherian X], AlgebraicGeometry.IsLo
callyNoetherian X
· 使用定理 `AlgebraicGeometry.isLocallyNoetherian_of_affine_cover`：isLocallyNoetheri
an_of_affine_cover {ι} {S : ι -> X.affineOpens} (hS : (⨆ i, S i : X.Opens) = ⊤) 
(hS' : forall i, IsNoetherianRing Γ(X, S i)…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `TopologicalSpace.Opens.coe_top`：coe_top : ((⊤ : Opens α) : Set α) = Set.
univ
· 使用定理 `isOpen_iUnion`：isOpen_iUnion {f : ι -> Set X} (h : forall i, IsOpen (f i
)) : IsOpen (⋃ i, f i)
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用定理 `TopologicalSpace.Opens.iSup_mk`：iSup_mk {ι} (s : ι -> Set α) (h : forall
 i, IsOpen (s i)) : (⨆ i, ⟨s i, h i⟩ : Opens α) = ⟨⋃ i, s i, isOpen_iUnion h⟩
· 使用定理 `isCompact_iUnion`：isCompact_iUnion {ι : Sort*} {f : ι -> Set X} [Finite 
ι] (h : forall i, IsCompact (f i)) : IsCompact (⋃ i, f i)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isCompact_iff_isCompact_univ`：isCompact_iff_isCompact_univ : IsCompact s
 ↔ IsCompact (univ : Set s)
· 使用定理 `CompactSpace.isCompact_univ`：∀ {X : Type u_1} {inst : TopologicalSpace X
} [self : CompactSpace X], IsCompact Set.univ
· 使用引理 `AlgebraicGeometry.noetherianSpace_of_isAffineOpen`：noetherianSpace_of_is
AffineOpen (U : X.Opens) (hU : IsAffineOpen U) [IsNoetherianRing Γ(X, U)] : Noet
herianSpace U
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `TopologicalSpace.NoetherianSpace.compactSpace`：∀ (α : Type u_1) [inst : 
TopologicalSpace α] [h : TopologicalSpace.NoetherianSpace α], CompactSpace α

--- 原说明 ---
A scheme is Noetherian if and only if it is covered by finitely many affine open
s whose
sections are Noetherian rings.
-/
theorem isNoetherian_iff_of_finite_iSup_eq_top {ι} [Finite ι] {S : ι → X.affineOpens}
    (hS : (⨆ i, S i : X.Opens) = ⊤) :
    IsNoetherian X ↔ ∀ i, IsNoetherianRing Γ(X, S i) := by
  constructor
  · intro h i
    apply (isLocallyNoetherian_iff_of_iSup_eq_top hS).mp
    exact h.toIsLocallyNoetherian
  · intro h
    convert! IsNoetherian.mk
    · exact isLocallyNoetherian_of_affine_cover hS h
    · constructor
      rw [← Opens.coe_top, ← hS, Opens.iSup_mk]
      apply isCompact_iUnion
      intro i
      apply isCompact_iff_isCompact_univ.mpr
      convert! CompactSpace.isCompact_univ
      have : NoetherianSpace (S i) := by
        apply noetherianSpace_of_isAffineOpen (S i).1 (S i).2
      apply NoetherianSpace.compactSpace (S i)

/-- A version of `isNoetherian_iff_of_finite_iSup_eq_top` using `Scheme.OpenCover`. -/
/-
**AlgebraicGeometry.isNoetherian_iff_of_finite_affine_openCover** 是 Mathlib 中的一个
定理，位于命名空间 `AlgebraicGeometry`。
形式化陈述：isNoetherian_iff_of_finite_affine_openCover {𝒰 : Scheme.OpenCover.{v, u} X
} [Finite 𝒰.I₀] [forall i, IsAffine (𝒰.X i)] : IsNoetherian X ↔ forall (i : 𝒰.I₀
), IsNoetherianRing Γ(𝒰.X i, ⊤)
参数：𝒰.X i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AlgebraicGeometry.isLocallyNoetherian_iff_of_affine_openCover`：isLocally
Noetherian_iff_of_affine_openCover (𝒰 : Scheme.OpenCover.{v, u} X) [forall i, Is
Affine (𝒰.X i)] : IsLocallyNoetherian X ↔ forall (i…
· 使用定理 `AlgebraicGeometry.IsNoetherian.toIsLocallyNoetherian`：∀ {X : AlgebraicGe
ometry.Scheme} [self : AlgebraicGeometry.IsNoetherian X], AlgebraicGeometry.IsLo
callyNoetherian X
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `AlgebraicGeometry.Scheme.OpenCover.compactSpace`：∀ {X : AlgebraicGeometr
y.Scheme} (𝒰 : X.OpenCover) [Finite 𝒰.I₀] [H : ∀ (i : 𝒰.I₀), CompactSpace ↥(𝒰.X 
i)],   CompactSpace ↥X
· 使用定理 `AlgebraicGeometry.Scheme.compactSpace_of_isAffine`：∀ (X : AlgebraicGeome
try.Scheme) [AlgebraicGeometry.IsAffine X], CompactSpace ↥X

--- 原说明 ---
A version of `isNoetherian_iff_of_finite_iSup_eq_top` using `Scheme.OpenCover`.
-/
theorem isNoetherian_iff_of_finite_affine_openCover {𝒰 : Scheme.OpenCover.{v, u} X}
    [Finite 𝒰.I₀] [∀ i, IsAffine (𝒰.X i)] :
    IsNoetherian X ↔ ∀ (i : 𝒰.I₀), IsNoetherianRing Γ(𝒰.X i, ⊤) := by
  constructor
  · intro h i
    apply (isLocallyNoetherian_iff_of_affine_openCover _).mp
    exact h.toIsLocallyNoetherian
  · intro hNoeth
    convert! IsNoetherian.mk
    · exact (isLocallyNoetherian_iff_of_affine_openCover _).mpr hNoeth
    · exact Scheme.OpenCover.compactSpace 𝒰

set_option backward.isDefEq.respectTransparency.types false in
/-- A Noetherian scheme has a Noetherian underlying topological space. -/
@[stacks 01OZ]
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A Noetherian scheme has a Noetherian underlying topological space.
-/
instance (priority := 100) IsNoetherian.noetherianSpace [IsNoetherian X] :
    NoetherianSpace X := by
  apply TopologicalSpace.noetherian_univ_iff.mp
  let 𝒰 := X.affineCover.finiteSubcover
  rw [← 𝒰.iUnion_range]
  suffices ∀ i : 𝒰.I₀, NoetherianSpace (Set.range <| (𝒰.f i)) by
    apply NoetherianSpace.iUnion
  intro i
  have : IsAffine (𝒰.X i) := by
    rw [X.affineCover.finiteSubcover_X]
    apply Scheme.isAffine_affineCover
  let U : X.affineOpens := ⟨Scheme.Hom.opensRange (𝒰.f i), isAffineOpen_opensRange _⟩
  convert! noetherianSpace_of_isAffineOpen U.1 U.2
  apply IsLocallyNoetherian.component_noetherian

/-- Any morphism of schemes `f : X ⟶ Y` with `X` Noetherian is quasi-compact. -/
@[stacks 01P0]
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any morphism of schemes `f : X ⟶ Y` with `X` Noetherian is quasi-compact.
-/
instance (priority := 100) quasiCompact_of_noetherianSpace_source {X Y : Scheme}
    [NoetherianSpace X] (f : X ⟶ Y) : QuasiCompact f :=
  ⟨fun _ _ _ => NoetherianSpace.isCompact _⟩

/-- If `R` is a Noetherian ring, `Spec R` is a Noetherian scheme. -/
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `R` is a Noetherian ring, `Spec R` is a Noetherian scheme.
-/
instance {R : CommRingCat} [IsNoetherianRing R] : IsNoetherian (Spec R) where
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R} [CommRing R] [IsNoetherianRing R] :
    IsNoetherian <| Spec <| .of R := by
  suffices IsNoetherianRing (CommRingCat.of R) by infer_instance
  assumption
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsLocallyNoetherian X] {x : X} : IsNoetherianRing (X.presheaf.stalk x) := by
  obtain ⟨U, hU, hU2, hU3⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) (by simp)
  have := AlgebraicGeometry.IsAffineOpen.isLocalization_stalk hU ⟨x, hU2⟩
  exact @IsLocalization.isNoetherianRing _ _ (hU.primeIdealOf ⟨x, hU2⟩).asIdeal.primeCompl
        (X.presheaf.stalk x) _ (X.presheaf.algebra_section_stalk ⟨x, hU2⟩)
        this (IsLocallyNoetherian.component_noetherian ⟨U, hU⟩)

/-- `R` is a Noetherian ring if and only if `Spec R` is a Noetherian scheme. -/
@[simp]
/-
**AlgebraicGeometry.isNoetherian_Spec** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeomet
ry`。
形式化陈述：isNoetherian_Spec {R : CommRingCat} : IsNoetherian (Spec R) ↔ IsNoetherian
Ring R
该定理/引理刻画了左右两侧的等价关系。
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
`R` is a Noetherian ring if and only if `Spec R` is a Noetherian scheme.
-/
theorem isNoetherian_Spec {R : CommRingCat} :
    IsNoetherian (Spec R) ↔ IsNoetherianRing R := by
  simp [AlgebraicGeometry.isNoetherian_iff, (inferInstance : CompactSpace (Spec R))]

/-- A Noetherian scheme has a finite number of irreducible components. -/
@[stacks 0BA8]
/-
**AlgebraicGeometry.finite_irreducibleComponents_of_isNoetherian** 是 Mathlib 中的一
个定理，位于命名空间 `AlgebraicGeometry`。
形式化陈述：finite_irreducibleComponents_of_isNoetherian [IsNoetherian X] : (irreducib
leComponents X).Finite
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.NoetherianSpace.finite_irreducibleComponents`：∀ {α : Ty
pe u_1} [inst : TopologicalSpace α] [TopologicalSpace.NoetherianSpace α], (irred
ucibleComponents α).Finite
· 使用定理 `AlgebraicGeometry.IsNoetherian.noetherianSpace`：∀ {X : AlgebraicGeometry
.Scheme} [AlgebraicGeometry.IsNoetherian X], TopologicalSpace.NoetherianSpace ↥X

--- 原说明 ---
A Noetherian scheme has a finite number of irreducible components.
-/
theorem finite_irreducibleComponents_of_isNoetherian [IsNoetherian X] :
    (irreducibleComponents X).Finite := NoetherianSpace.finite_irreducibleComponents

end AlgebraicGeometry

