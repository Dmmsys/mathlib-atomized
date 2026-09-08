/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Fangming Li
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Preimmersion

/-!
# Stalks of a Scheme

## Main definitions and results

- `AlgebraicGeometry.Scheme.fromSpecStalk`: The canonical morphism `Spec 𝒪_{X, x} ⟶ X`.
- `AlgebraicGeometry.Scheme.range_fromSpecStalk`: The range of the map `Spec 𝒪_{X, x} ⟶ X` is
  exactly the `y`s that specialize to `x`.
- `AlgebraicGeometry.SpecToEquivOfLocalRing`:
  Given a local ring `R` and scheme `X`, morphisms `Spec R ⟶ X` corresponds to pairs
  `(x, f)` where `x : X` and `f : 𝒪_{X, x} ⟶ R` is a local ring homomorphism.
-/

@[expose] public section

namespace AlgebraicGeometry

open CategoryTheory Opposite TopologicalSpace IsLocalRing

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {U V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)

section fromSpecStalk

/--
A morphism from `Spec(O_x)` to `X`, which is defined with the help of an affine open
neighborhood `U` of `x`.
-/
/-
**AlgebraicGeometry.IsAffineOpen.fromSpecStalk** 是 Mathlib 中的一个定义，位于命名空间 `Algebr
aicGeometry.IsAffineOpen`。
形式化陈述：{X : AlgebraicGeometry.Scheme} →   {U : X.Opens} →     AlgebraicGeometry.I
sAffineOpen U → {x : ↥X} → x ∈ U → (AlgebraicGeometry.Spec (X.presheaf.stalk x) 
⟶ X)
参数：AlgebraicGeometry.Spec (X.presheaf.stalk x) ⟶ X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism from `Spec(O_x)` to `X`, which is defined with the help of an affine 
open
neighborhood `U` of `x`.
-/
noncomputable def IsAffineOpen.fromSpecStalk
    {X : Scheme} {U : X.Opens} (hU : IsAffineOpen U) {x : X} (hxU : x ∈ U) :
    Spec (X.presheaf.stalk x) ⟶ X :=
  Spec.map (X.presheaf.germ _ x hxU) ≫ hU.fromSpec

/--
The morphism from `Spec(O_x)` to `X` given by `IsAffineOpen.fromSpec` does not depend on the affine
open neighborhood of `x` we choose.
-/
/-
**AlgebraicGeometry.IsAffineOpen.fromSpecStalk_eq** 是 Mathlib 中的一个定理，位于命名空间 `Alg
ebraicGeometry.IsAffineOpen`。
形式化陈述：∀ {X : AlgebraicGeometry.Scheme} {U V : X.Opens} (hU : AlgebraicGeometry.I
sAffineOpen U)   (hV : AlgebraicGeometry.IsAffineOpen V) (x : ↥X) (hxU : x ∈ U) 
(hxV : x ∈ V),   hU.fromSpecStalk hxU = hV.fromSpecStalk hxV
参数：hU : AlgebraicGeometry.IsAffineOpen U；hV : AlgebraicGeometry.IsAffineOpen V；x
 : ↥X；hxU : x ∈ U；hxV : x ∈ V。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `TopologicalSpace.Opens.isBasis_iff_nbhd`：isBasis_iff_nbhd {B : Set (Open
s α)} : IsBasis B ↔ forall {U : Opens α} {x}, x in U -> exists U' in B, x in U' 
∧ U' <= U
· 使用定理 `AlgebraicGeometry.Scheme.isBasis_affineOpens`：∀ (X : AlgebraicGeometry.S
cheme), TopologicalSpace.Opens.IsBasis X.affineOpens
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.IsAffineOpen.map_fromSpec`：map_fromSpec {V : X.Opens} 
(hV : IsAffineOpen V) (f : op U ⟶ op V) : Spec.map (X.presheaf.map f) ≫ hU.fromS
pec = hV.fromSpec
· 使用定理 `AlgebraicGeometry.Spec.map_comp_assoc`：∀ {R S T : CommRingCat} (f : R ⟶ 
S) (g : S ⟶ T) {Z : AlgebraicGeometry.Scheme} (h : AlgebraicGeometry.Spec R ⟶ Z)
,   CategoryTheory.Category…
· 使用定理 `TopCat.Presheaf.germ_res`：germ_res (F : X.Presheaf C) {U V : Opens X} (i
 : U ⟶ V) (x : X) (hx : x in U) : F.map i.op ≫ F.germ U x hx = F.germ V x (i.le 
hx)
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b

--- 原说明 ---
The morphism from `Spec(O_x)` to `X` given by `IsAffineOpen.fromSpec` does not d
epend on the affine
open neighborhood of `x` we choose.
-/
theorem IsAffineOpen.fromSpecStalk_eq (x : X) (hxU : x ∈ U) (hxV : x ∈ V) :
    hU.fromSpecStalk hxU = hV.fromSpecStalk hxV := by
  obtain ⟨U', h₁, h₂, h₃ : U' ≤ U ⊓ V⟩ :=
    Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens (show x ∈ U ⊓ V from ⟨hxU, hxV⟩)
  transitivity fromSpecStalk h₁ h₂
  · delta fromSpecStalk
    rw [← hU.map_fromSpec h₁ (homOfLE <| h₃.trans inf_le_left).op, ← Spec.map_comp_assoc,
      TopCat.Presheaf.germ_res]
  · delta fromSpecStalk
    rw [← hV.map_fromSpec h₁ (homOfLE <| h₃.trans inf_le_right).op, ← Spec.map_comp_assoc,
      TopCat.Presheaf.germ_res]

/--
If `x` is a point of `X`, this is the canonical morphism from `Spec(O_x)` to `X`.
-/
/-
**AlgebraicGeometry.Scheme.fromSpecStalk** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeo
metry.Scheme`。
形式化陈述：(X : AlgebraicGeometry.Scheme) → (x : ↥X) → AlgebraicGeometry.Spec (X.pres
heaf.stalk x) ⟶ X
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.instJointlySurjectivePrecoverage`：∀ {P : Catego
ryTheory.MorphismProperty AlgebraicGeometry.Scheme},   AlgebraicGeometry.Scheme.
JointlySurjective (AlgebraicGeometry.Scheme.pre…

--- 原说明 ---
If `x` is a point of `X`, this is the canonical morphism from `Spec(O_x)` to `X`
.
-/
noncomputable def Scheme.fromSpecStalk (X : Scheme) (x : X) :
    Spec (X.presheaf.stalk x) ⟶ X :=
  (isAffineOpen_opensRange (X.affineCover.f (X.affineCover.idx x))).fromSpecStalk
    (X.affineCover.covers x)

@[simps over] noncomputable
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : Scheme.{u}) (x : X) : (Spec (X.presheaf.stalk x)).Over X := ⟨X.fromSpecStalk x⟩

noncomputable
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : Scheme.{u}) (x : X) : (Spec (X.presheaf.stalk x)).CanonicallyOver X where

@[simp]
/-
**AlgebraicGeometry.IsAffineOpen.fromSpecStalk_eq_fromSpecStalk** 是 Mathlib 中的一个
定理，位于命名空间 `AlgebraicGeometry.IsAffineOpen`。
形式化陈述：∀ {X : AlgebraicGeometry.Scheme} {U : X.Opens} (hU : AlgebraicGeometry.IsA
ffineOpen U) {x : ↥X} (hxU : x ∈ U),   hU.fromSpecStalk hxU = X.fromSpecStalk x
参数：hU : AlgebraicGeometry.IsAffineOpen U；hxU : x ∈ U。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.IsAffineOpen.fromSpecStalk_eq`：∀ {X : AlgebraicGeometr
y.Scheme} {U V : X.Opens} (hU : AlgebraicGeometry.IsAffineOpen U)   (hV : Algebr
aicGeometry.IsAffineOpen V) (x : ↥X) …
· 使用定理 `AlgebraicGeometry.Scheme.instJointlySurjectivePrecoverage`：∀ {P : Catego
ryTheory.MorphismProperty AlgebraicGeometry.Scheme},   AlgebraicGeometry.Scheme.
JointlySurjective (AlgebraicGeometry.Scheme.pre…
-/
theorem IsAffineOpen.fromSpecStalk_eq_fromSpecStalk {x : X} (hxU : x ∈ U) :
    hU.fromSpecStalk hxU = X.fromSpecStalk x := fromSpecStalk_eq ..
/-
**AlgebraicGeometry.IsAffineOpen.fromSpecStalk_isPreimmersion** 是 Mathlib 中的一个定理
，位于命名空间 `AlgebraicGeometry.IsAffineOpen`。
形式化陈述：∀ {X : AlgebraicGeometry.Scheme} {U : TopologicalSpace.Opens ↥X} (hU : Alg
ebraicGeometry.IsAffineOpen U) (x : ↥X)   (hx : x ∈ U), AlgebraicGeometry.IsPrei
mmersion (hU.fromSpecStalk hx)
参数：hU : AlgebraicGeometry.IsAffineOpen U；x : ↥X；hx : x ∈ U；hU.fromSpecStalk hx。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.IsPreimmersion.of_isLocalization`：of_isLocalization {R
 S : Type u} [CommRing R] (M : Submonoid R) [CommRing S] [Algebra R S] [IsLocali
zation M S] : IsPreimmersion (Spec.map (…
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `AlgebraicGeometry.IsAffineOpen.isLocalization_stalk`：isLocalization_stal
k (x : U) : IsLocalization.AtPrime (X.presheaf.stalk x) (hU.primeIdealOf x).asId
eal
· 使用定理 `AlgebraicGeometry.IsPreimmersion.instOfIsOpenImmersion`：∀ {X Y : Algebra
icGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.IsOpenImmersion f], AlgebraicG
eometry.IsPreimmersion f
-/
instance IsAffineOpen.fromSpecStalk_isPreimmersion {X : Scheme.{u}} {U : Opens X}
    (hU : IsAffineOpen U) (x : X) (hx : x ∈ U) : IsPreimmersion (hU.fromSpecStalk hx) := by
  dsimp [IsAffineOpen.fromSpecStalk]
  have : IsPreimmersion (Spec.map (X.presheaf.germ U x hx)) :=
    letI : Algebra Γ(X, U) (X.presheaf.stalk x) := (X.presheaf.germ U x hx).hom.toAlgebra
    haveI := hU.isLocalization_stalk ⟨x, hx⟩
    IsPreimmersion.of_isLocalization (R := Γ(X, U)) (S := X.presheaf.stalk x)
      (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
  apply IsPreimmersion.comp
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X : Scheme.{u}} (x : X) : IsPreimmersion (X.fromSpecStalk x) :=
  IsAffineOpen.fromSpecStalk_isPreimmersion _ _ _

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.IsAffineOpen.fromSpecStalk_closedPoint** 是 Mathlib 中的一个定理，位于
命名空间 `AlgebraicGeometry.IsAffineOpen`。
形式化陈述：∀ {X : AlgebraicGeometry.Scheme} {U : TopologicalSpace.Opens ↥X} (hU : Alg
ebraicGeometry.IsAffineOpen U) {x : ↥X}   (hxU : x ∈ U), (hU.fromSpecStalk hxU) 
(IsLocalRing.closedPoint ↑(X.presheaf.stalk x)) = x
参数：hU : AlgebraicGeometry.IsAffineOpen U；hxU : x ∈ U；hU.fromSpecStalk hxU；IsLoca
lRing.closedPoint ↑(X.presheaf.stalk x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.LocallyRingedSpace.instIsLocalRingCarrierStalkCommRing
CatPresheaf`：∀ (X : AlgebraicGeometry.LocallyRingedSpace) (x : ↑X.toTopCat), IsL
ocalRing ↑(X.presheaf.stalk x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.IsAffineOpen.fromSpecStalk.eq_1`：∀ {X : AlgebraicGeome
try.Scheme} {U : X.Opens} (hU : AlgebraicGeometry.IsAffineOpen U) {x : ↥X} (hxU 
: x ∈ U),   hU.fromSpecStalk hxU =     …
· 使用定理 `AlgebraicGeometry.Scheme.Hom.comp_apply`：comp_apply {X Y Z : Scheme} (f 
: X ⟶ Y) (g : Y ⟶ Z) (x : X) : (f ≫ g) x = g (f x)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.IsAffineOpen.primeIdealOf_eq_map_closedPoint`：primeIde
alOf_eq_map_closedPoint (x : U) : hU.primeIdealOf x = Spec.map (X.presheaf.germ 
_ x x.2) (closedPoint _)
· 使用定理 `AlgebraicGeometry.IsAffineOpen.fromSpec_primeIdealOf`：fromSpec_primeIdea
lOf (x : U) : hU.fromSpec (hU.primeIdealOf x) = x.1
-/
lemma IsAffineOpen.fromSpecStalk_closedPoint {U : Opens X} (hU : IsAffineOpen U)
    {x : X} (hxU : x ∈ U) :
    hU.fromSpecStalk hxU (closedPoint (X.presheaf.stalk x)) = x := by
  rw [IsAffineOpen.fromSpecStalk, Scheme.Hom.comp_apply]
  rw [← hU.primeIdealOf_eq_map_closedPoint ⟨x, hxU⟩, hU.fromSpec_primeIdealOf ⟨x, hxU⟩]

namespace Scheme

@[simp]
/-
**AlgebraicGeometry.Scheme.fromSpecStalk_closedPoint** 是 Mathlib 中的一个引理，位于命名空间 `
AlgebraicGeometry.Scheme`。
形式化陈述：fromSpecStalk_closedPoint {x : X} : X.fromSpecStalk x (closedPoint (X.pres
heaf.stalk x)) = x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.IsAffineOpen.fromSpecStalk_closedPoint`：∀ {X : Algebra
icGeometry.Scheme} {U : TopologicalSpace.Opens ↥X} (hU : AlgebraicGeometry.IsAff
ineOpen U) {x : ↥X}   (hxU : x ∈ U), (hU.fromS…
· 使用定理 `AlgebraicGeometry.Scheme.instJointlySurjectivePrecoverage`：∀ {P : Catego
ryTheory.MorphismProperty AlgebraicGeometry.Scheme},   AlgebraicGeometry.Scheme.
JointlySurjective (AlgebraicGeometry.Scheme.pre…
-/
lemma fromSpecStalk_closedPoint {x : X} :
    X.fromSpecStalk x (closedPoint (X.presheaf.stalk x)) = x :=
  IsAffineOpen.fromSpecStalk_closedPoint _ _

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.Scheme.fromSpecStalk_app** 是 Mathlib 中的一个引理，位于命名空间 `Algebrai
cGeometry.Scheme`。
形式化陈述：fromSpecStalk_app {x : X} (hxU : x in U) : (X.fromSpecStalk x).app U = X.p
resheaf.germ U x hxU ≫ (ΓSpecIso (X.presheaf.stalk x)).inv ≫ (Spec (X.presheaf.s
talk x)).presheaf.map (homOfLE le_top).op
参数：hxU : x in U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `TopologicalSpace.IsTopologicalBasis.exists_subset_of_mem_open`：∀ {α : Ty
pe u} [t : TopologicalSpace α] {b : Set (Set α)},   TopologicalSpace.IsTopologic
alBasis b → ∀ {a : α} {u : Set α}, a ∈ u → IsOpen u…
· 使用定理 `AlgebraicGeometry.Scheme.isBasis_affineOpens`：∀ (X : AlgebraicGeometry.S
cheme), TopologicalSpace.Opens.IsBasis X.affineOpens
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.IsAffineOpen.fromSpecStalk_eq_fromSpecStalk`：∀ {X : Al
gebraicGeometry.Scheme} {U : X.Opens} (hU : AlgebraicGeometry.IsAffineOpen U) {x
 : ↥X} (hxU : x ∈ U),   hU.fromSpecStalk hxU = X.fr…
· 使用定理 `AlgebraicGeometry.IsAffineOpen.fromSpecStalk.eq_1`：∀ {X : AlgebraicGeome
try.Scheme} {U : X.Opens} (hU : AlgebraicGeometry.IsAffineOpen U) {x : ↥X} (hxU 
: x ∈ U),   hU.fromSpecStalk hxU =     …
· 使用定理 `AlgebraicGeometry.Scheme.Hom.comp_app`：comp_app {X Y Z : Scheme} (f : X 
⟶ Y) (g : Y ⟶ Z) (U) : (f ≫ g).app U = g.app U ≫ f.app _
· 使用引理 `AlgebraicGeometry.IsAffineOpen.fromSpec_app_of_le`：fromSpec_app_of_le (V
 : X.Opens) (h : U <= V) : hU.fromSpec.app V = X.presheaf.map (homOfLE h).op ≫ (
Scheme.ΓSpecIso Γ(X, U)).inv ≫ (Spec _)…
· 使用定理 `TopCat.Presheaf.germ_res`：germ_res (F : X.Presheaf C) {U V : Opens X} (i
 : U ⟶ V) (x : X) (hx : x in U) : F.map i.op ≫ F.germ U x hx = F.germ V x (i.le 
hx)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `TopCat.Presheaf.germ_res'_assoc`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] [inst_1 : CategoryTheory.Limits.HasColimits C] {X : TopCat}   
(F : TopCat.Presheaf …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TopCat.Presheaf.germ_res'`：germ_res' (F : X.Presheaf C) {U V : Opens X} 
(i : op V ⟶ op U) (x : X) (hx : x in U) : F.map i ≫ F.germ U x hx = F.germ V x (
i.unop.le hx)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma fromSpecStalk_app {x : X} (hxU : x ∈ U) :
    (X.fromSpecStalk x).app U =
      X.presheaf.germ U x hxU ≫
        (ΓSpecIso (X.presheaf.stalk x)).inv ≫
          (Spec (X.presheaf.stalk x)).presheaf.map (homOfLE le_top).op := by
  obtain ⟨_, ⟨V : X.Opens, hV, rfl⟩, hxV, hVU⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    hxU U.2
  rw [← hV.fromSpecStalk_eq_fromSpecStalk hxV, IsAffineOpen.fromSpecStalk, Scheme.Hom.comp_app,
    hV.fromSpec_app_of_le _ hVU, ← X.presheaf.germ_res (homOfLE hVU) x hxV]
  simp [Category.assoc, ← ΓSpecIso_inv_naturality_assoc]
/-
**AlgebraicGeometry.Scheme.fromSpecStalk_appTop** 是 Mathlib 中的一个引理，位于命名空间 `Algeb
raicGeometry.Scheme`。
形式化陈述：fromSpecStalk_appTop {x : X} : (X.fromSpecStalk x).appTop = X.presheaf.ger
m ⊤ x trivial ≫ (ΓSpecIso (X.presheaf.stalk x)).inv ≫ (Spec (X.presheaf.stalk x)
).presheaf.map (homOfLE le_top).op
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.Scheme.fromSpecStalk_app`：fromSpecStalk_app {x : X} (h
xU : x in U) : (X.fromSpecStalk x).app U = X.presheaf.germ U x hxU ≫ (ΓSpecIso (
X.presheaf.stalk x)).inv ≫ (Spec…
· 使用定理 `trivial`：True
-/
lemma fromSpecStalk_appTop {x : X} :
    (X.fromSpecStalk x).appTop =
      X.presheaf.germ ⊤ x trivial ≫
        (ΓSpecIso (X.presheaf.stalk x)).inv ≫
          (Spec (X.presheaf.stalk x)).presheaf.map (homOfLE le_top).op :=
  fromSpecStalk_app ..

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.Scheme.SpecMap_stalkSpecializes_fromSpecStalk** 是 Mathlib 中的
一个引理，位于命名空间 `AlgebraicGeometry.Scheme`。
形式化陈述：SpecMap_stalkSpecializes_fromSpecStalk {x y : X} (h : x ⤳ y) : Spec.map (X
.presheaf.stalkSpecializes h) ≫ X.fromSpecStalk y = X.fromSpecStalk x
参数：h : x ⤳ y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.IsTopologicalBasis.exists_subset_of_mem_open`：∀ {α : Ty
pe u} [t : TopologicalSpace α] {b : Set (Set α)},   TopologicalSpace.IsTopologic
alBasis b → ∀ {a : α} {u : Set α}, a ∈ u → IsOpen u…
· 使用定理 `AlgebraicGeometry.Scheme.isBasis_affineOpens`：∀ (X : AlgebraicGeometry.S
cheme), TopologicalSpace.Opens.IsBasis X.affineOpens
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `isOpen_univ`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen Set.univ
· 使用定理 `Specializes.mem_open`：Specializes.mem_open (h : x ⤳ y) (hs : IsOpen s) (
hy : y in s) : x in s
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.IsAffineOpen.fromSpecStalk_eq_fromSpecStalk`：∀ {X : Al
gebraicGeometry.Scheme} {U : X.Opens} (hU : AlgebraicGeometry.IsAffineOpen U) {x
 : ↥X} (hxU : x ∈ U),   hU.fromSpecStalk hxU = X.fr…
· 使用定理 `AlgebraicGeometry.IsAffineOpen.fromSpecStalk.eq_1`：∀ {X : AlgebraicGeome
try.Scheme} {U : X.Opens} (hU : AlgebraicGeometry.IsAffineOpen U) {x : ↥X} (hxU 
: x ∈ U),   hU.fromSpecStalk hxU =     …
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `AlgebraicGeometry.Spec.map_comp`：∀ {R S T : CommRingCat} (f : R ⟶ S) (g 
: S ⟶ T),   AlgebraicGeometry.Spec.map (CategoryTheory.CategoryStruct.comp f g) 
=     CategoryTheory.…
· 使用定理 `TopologicalSpace.Opens.isOpen`：∀ {α : Type u_2} [inst : TopologicalSpace
 α] (U : TopologicalSpace.Opens α), IsOpen ↑U
· 使用定理 `TopCat.Presheaf.germ_stalkSpecializes`：germ_stalkSpecializes (F : X.Pres
heaf C) {U : Opens X} {y : X} (hy : y in U) {x : X} (h : x ⤳ y) : F.germ U y hy 
≫ F.stalkSpecializes h = F.…
-/
lemma SpecMap_stalkSpecializes_fromSpecStalk {x y : X} (h : x ⤳ y) :
    Spec.map (X.presheaf.stalkSpecializes h) ≫ X.fromSpecStalk y = X.fromSpecStalk x := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  have hxU : x ∈ U := h.mem_open U.2 hyU
  rw [← hU.fromSpecStalk_eq_fromSpecStalk hyU, ← hU.fromSpecStalk_eq_fromSpecStalk hxU,
    IsAffineOpen.fromSpecStalk, IsAffineOpen.fromSpecStalk, ← Category.assoc, ← Spec.map_comp,
    TopCat.Presheaf.germ_stalkSpecializes]
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {x y : X} (h : x ⤳ y) : (Spec.map (X.presheaf.stalkSpecializes h)).IsOver X where

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.Scheme.SpecMap_stalkMap_fromSpecStalk** 是 Mathlib 中的一个引理，位于命
名空间 `AlgebraicGeometry.Scheme`。
形式化陈述：SpecMap_stalkMap_fromSpecStalk {x} : Spec.map (f.stalkMap x) ≫ Y.fromSpecS
talk _ = X.fromSpecStalk x ≫ f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.IsTopologicalBasis.exists_subset_of_mem_open`：∀ {α : Ty
pe u} [t : TopologicalSpace α] {b : Set (Set α)},   TopologicalSpace.IsTopologic
alBasis b → ∀ {a : α} {u : Set α}, a ∈ u → IsOpen u…
· 使用定理 `AlgebraicGeometry.Scheme.isBasis_affineOpens`：∀ (X : AlgebraicGeometry.S
cheme), TopologicalSpace.Opens.IsBasis X.affineOpens
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `isOpen_univ`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen Set.univ
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.IsAffineOpen.fromSpecStalk_eq_fromSpecStalk`：∀ {X : Al
gebraicGeometry.Scheme} {U : X.Opens} (hU : AlgebraicGeometry.IsAffineOpen U) {x
 : ↥X} (hxU : x ∈ U),   hU.fromSpecStalk hxU = X.fr…
· 使用定理 `AlgebraicGeometry.IsAffineOpen.fromSpecStalk.eq_1`：∀ {X : AlgebraicGeome
try.Scheme} {U : X.Opens} (hU : AlgebraicGeometry.IsAffineOpen U) {x : ↥X} (hxU 
: x ∈ U),   hU.fromSpecStalk hxU =     …
· 使用定理 `AlgebraicGeometry.Spec.map_comp_assoc`：∀ {R S T : CommRingCat} (f : R ⟶ 
S) (g : S ⟶ T) {Z : AlgebraicGeometry.Scheme} (h : AlgebraicGeometry.Spec R ⟶ Z)
,   CategoryTheory.Category…
· 使用引理 `AlgebraicGeometry.Scheme.Hom.germ_stalkMap`：germ_stalkMap (U : Y.Opens) 
(x : X) (hx : f x in U) : Y.presheaf.germ U (f x) hx ≫ f.stalkMap x = f.app U ≫ 
X.presheaf.germ (f ⁻¹ᵁ U) x hx
· 使用定理 `TopCat.Presheaf.germ_res`：germ_res (F : X.Presheaf C) {U V : Opens X} (i
 : U ⟶ V) (x : X) (hx : x in U) : F.map i.op ≫ F.germ U x hx = F.germ V x (i.le 
hx)
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用引理 `AlgebraicGeometry.Scheme.Hom.app_eq_appLE`：app_eq_appLE {U : Y.Opens} : 
f.app U = f.appLE U _ le_rfl
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `AlgebraicGeometry.Scheme.Hom.appLE_map`：appLE_map (e : V <= f ⁻¹ᵁ U) (i 
: op V ⟶ op V') : f.appLE U V e ≫ X.presheaf.map i = f.appLE U V' (i.unop.le.tra
ns e)
· 使用引理 `AlgebraicGeometry.IsAffineOpen.SpecMap_appLE_fromSpec`：SpecMap_appLE_fro
mSpec (f : X ⟶ Y) {V : X.Opens} {U : Y.Opens} (hU : IsAffineOpen U) (hV : IsAffi
neOpen V) (i : V <= f ⁻¹ᵁ U) : Spec.map (f.…
-/
lemma SpecMap_stalkMap_fromSpecStalk {x} :
    Spec.map (f.stalkMap x) ≫ Y.fromSpecStalk _ = X.fromSpecStalk x ≫ f := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    hxU (f ⁻¹ᵁ U).2
  rw [← hU.fromSpecStalk_eq_fromSpecStalk hxU, ← hV.fromSpecStalk_eq_fromSpecStalk hxV,
    IsAffineOpen.fromSpecStalk, ← Spec.map_comp_assoc, Scheme.Hom.germ_stalkMap f _ x hxU,
    IsAffineOpen.fromSpecStalk, Spec.map_comp_assoc, ← X.presheaf.germ_res (homOfLE hVU) x hxV,
    Spec.map_comp_assoc, Category.assoc, ← Spec.map_comp_assoc (f.app _),
      Hom.app_eq_appLE, Hom.appLE_map, IsAffineOpen.SpecMap_appLE_fromSpec]
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [X.Over Y] {x} : Spec.map ((X ↘ Y).stalkMap x) |>.IsOver Y where

@[stacks 01J7]
/-
**AlgebraicGeometry.Scheme.range_fromSpecStalk** 是 Mathlib 中的一个引理，位于命名空间 `Algebr
aicGeometry.Scheme`。
形式化陈述：range_fromSpecStalk {x : X} : Set.range (X.fromSpecStalk x) = { y | y ⤳ x 
}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Specializes.trans`：Specializes.trans : x ⤳ y -> y ⤳ z -> x ⤳ z
· 使用定理 `AlgebraicGeometry.LocallyRingedSpace.instIsLocalRingCarrierStalkCommRing
CatPresheaf`：∀ (X : AlgebraicGeometry.LocallyRingedSpace) (x : ↑X.toTopCat), IsL
ocalRing ↑(X.presheaf.stalk x)
· 使用定理 `Specializes.map`：Specializes.map (h : x ⤳ y) (hf : Continuous f) : f x ⤳
 f y
· 使用定理 `IsLocalRing.specializes_closedPoint`：specializes_closedPoint (x : PrimeS
pectrum R) : x ⤳ closedPoint R
· 使用定理 `AlgebraicGeometry.Scheme.Hom.continuous`：∀ {X Y : AlgebraicGeometry.Sche
me} (f : X ⟶ Y), Continuous ⇑f
· 使用定理 `specializes_of_eq`：specializes_of_eq (e : x = y) : x ⤳ y
· 使用引理 `AlgebraicGeometry.Scheme.fromSpecStalk_closedPoint`：fromSpecStalk_closed
Point {x : X} : X.fromSpecStalk x (closedPoint (X.presheaf.stalk x)) = x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `AlgebraicGeometry.Scheme.SpecMap_stalkSpecializes_fromSpecStalk`：SpecMap
_stalkSpecializes_fromSpecStalk {x y : X} (h : x ⤳ y) : Spec.map (X.presheaf.sta
lkSpecializes h) ≫ X.fromSpecStalk y = X.fromSpecStal…
-/
lemma range_fromSpecStalk {x : X} :
    Set.range (X.fromSpecStalk x) = { y | y ⤳ x } := by
  ext y
  constructor
  · rintro ⟨y, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint y).map (X.fromSpecStalk x).continuous).trans
      (specializes_of_eq fromSpecStalk_closedPoint)
  · rintro (hy : y ⤳ x)
    have := fromSpecStalk_closedPoint (x := y)
    rw [← SpecMap_stalkSpecializes_fromSpecStalk hy] at this
    exact ⟨_, this⟩

set_option backward.isDefEq.respectTransparency false in
/-- The canonical map `Spec 𝒪_{X, x} ⟶ U` given `x ∈ U ⊆ X`. -/
noncomputable
/-
**AlgebraicGeometry.Scheme.Opens.fromSpecStalkOfMem** 是 Mathlib 中的一个定义，位于命名空间 `A
lgebraicGeometry.Scheme.Opens`。
形式化陈述：{X : AlgebraicGeometry.Scheme} → (U : X.Opens) → (x : ↥X) → x ∈ U → (Algeb
raicGeometry.Spec (X.presheaf.stalk x) ⟶ ↑U)
参数：U : X.Opens；x : ↥X；AlgebraicGeometry.Spec (X.presheaf.stalk x) ⟶ ↑U。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def Opens.fromSpecStalkOfMem {X : Scheme.{u}} (U : X.Opens) (x : X) (hxU : x ∈ U) :
    Spec (X.presheaf.stalk x) ⟶ U :=
  Spec.map (inv (U.ι.stalkMap ⟨x, hxU⟩)) ≫ U.toScheme.fromSpecStalk ⟨x, hxU⟩

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.Scheme.Opens.fromSpecStalkOfMem_** 是 Mathlib 中的一个引理，位于命名空间 `
AlgebraicGeometry.Scheme`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Opens.fromSpecStalkOfMem_ι {X : Scheme.{u}} (U : X.Opens) (x : X) (hxU : x ∈ U) :
    U.fromSpecStalkOfMem x hxU ≫ U.ι = X.fromSpecStalk x := by
  simp only [Opens.fromSpecStalkOfMem, Spec.map_inv, Category.assoc, IsIso.inv_comp_eq]
  exact (Scheme.SpecMap_stalkMap_fromSpecStalk U.ι (x := ⟨x, hxU⟩)).symm
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X : Scheme.{u}} (U : X.Opens) (x : X) (hxU : x ∈ U) :
    (U.fromSpecStalkOfMem x hxU).IsOver X where

@[reassoc]
/-
**AlgebraicGeometry.Scheme.fromSpecStalk_toSpec** 是 Mathlib 中的一个引理，位于命名空间 `Algeb
raicGeometry.Scheme`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma fromSpecStalk_toSpecΓ (X : Scheme.{u}) (x : X) :
    X.fromSpecStalk x ≫ X.toSpecΓ = Spec.map (X.presheaf.germ ⊤ x trivial) := by
  rw [Scheme.toSpecΓ_naturality, ← SpecMap_ΓSpecIso_hom, ← Spec.map_comp,
    Scheme.fromSpecStalk_appTop]
  simp

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.Scheme.Opens.fromSpecStalkOfMem_toSpec** 是 Mathlib 中的一个引理，位于
命名空间 `AlgebraicGeometry.Scheme`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Opens.fromSpecStalkOfMem_toSpecΓ {X : Scheme.{u}} (U : X.Opens) (x : X) (hxU : x ∈ U) :
    U.fromSpecStalkOfMem x hxU ≫ U.toSpecΓ = Spec.map (X.presheaf.germ U x hxU) := by
  rw [fromSpecStalkOfMem, Opens.toSpecΓ, Category.assoc, fromSpecStalk_toSpecΓ_assoc,
    ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  rw [IsIso.comp_inv_eq, Iso.inv_comp_eq]
  erw [Hom.germ_stalkMap U.ι U ⟨x, hxU⟩]
  rw [Opens.ι_app, Opens.topIso_hom, ← Functor.map_comp_assoc]
  exact (U.toScheme.presheaf.germ_res (homOfLE le_top) ⟨x, hxU⟩ (U := U.ι ⁻¹ᵁ U) hxU).symm

end Scheme

section Spec

variable (R : CommRingCat) (x)

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.Spec.fromSpecStalk_eq** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGe
ometry.Spec`。
形式化陈述：∀ (R : CommRingCat) (x : ↥(AlgebraicGeometry.Spec R)),   (AlgebraicGeometr
y.Spec R).fromSpecStalk x =     AlgebraicGeometry.Spec.map       (CategoryTheory
.CategoryStruct.comp (AlgebraicGeometry.Scheme.ΓSpecIso R).inv         ((Algebra
icGeometry.Spec R).presheaf.germ ⊤ x trivial))
参数：R : CommRingCat；x : ↥(AlgebraicGeometry.Spec R)；AlgebraicGeometry.Spec R；Cate
goryTheory.CategoryStruct.comp (AlgebraicGeometry.Scheme.ΓSpecIso R).inv        
 ((AlgebraicGeometry.Spec R).presheaf.germ ⊤ x trivial)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True
· 使用定理 `AlgebraicGeometry.isAffineOpen_top`：isAffineOpen_top (X : Scheme) [IsAff
ine X] : IsAffineOpen (⊤ : X.Opens)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.IsAffineOpen.fromSpecStalk_eq_fromSpecStalk`：∀ {X : Al
gebraicGeometry.Scheme} {U : X.Opens} (hU : AlgebraicGeometry.IsAffineOpen U) {x
 : ↥X} (hxU : x ∈ U),   hU.fromSpecStalk hxU = X.fr…
· 使用定理 `AlgebraicGeometry.IsAffineOpen.fromSpecStalk.eq_1`：∀ {X : AlgebraicGeome
try.Scheme} {U : X.Opens} (hU : AlgebraicGeometry.IsAffineOpen U) {x : ↥X} (hxU 
: x ∈ U),   hU.fromSpecStalk hxU =     …
· 使用引理 `AlgebraicGeometry.IsAffineOpen.fromSpec_top`：fromSpec_top [IsAffine X] :
 (isAffineOpen_top X).fromSpec = X.isoSpec.inv
· 使用定理 `AlgebraicGeometry.Scheme.isoSpec_Spec_inv`：∀ (R : CommRingCat),   (Algeb
raicGeometry.Spec R).isoSpec.inv = AlgebraicGeometry.Spec.map (AlgebraicGeometry
.Scheme.ΓSpecIso R).inv
· 使用定理 `AlgebraicGeometry.Spec.map_comp`：∀ {R S T : CommRingCat} (f : R ⟶ S) (g 
: S ⟶ T),   AlgebraicGeometry.Spec.map (CategoryTheory.CategoryStruct.comp f g) 
=     CategoryTheory.…
-/
lemma Spec.fromSpecStalk_eq :
    (Spec R).fromSpecStalk x =
      Spec.map ((Scheme.ΓSpecIso R).inv ≫ (Spec R).presheaf.germ ⊤ x trivial) := by
  rw [← (isAffineOpen_top (Spec R)).fromSpecStalk_eq_fromSpecStalk (x := x) trivial,
    IsAffineOpen.fromSpecStalk, IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv,
    ← Spec.map_comp]

-- This is not a simp lemma to respect the abstraction boundaries
/-- A variant of `Spec.fromSpecStalk_eq` that breaks abstraction boundaries. -/
/-
**AlgebraicGeometry.Spec.fromSpecStalk_eq'** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicG
eometry.Spec`。
形式化陈述：∀ (R : CommRingCat) (x : ↥(AlgebraicGeometry.Spec R)),   (AlgebraicGeometr
y.Spec R).fromSpecStalk x =     AlgebraicGeometry.Spec.map (AlgebraicGeometry.St
ructureSheaf.toStalk (↑R) x)
参数：R : CommRingCat；x : ↥(AlgebraicGeometry.Spec R)；AlgebraicGeometry.Spec R；Alge
braicGeometry.StructureSheaf.toStalk (↑R) x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Spec.fromSpecStalk_eq`：∀ (R : CommRingCat) (x : ↥(Alge
braicGeometry.Spec R)),   (AlgebraicGeometry.Spec R).fromSpecStalk x =     Algeb
raicGeometry.Spec.map       (…

--- 原说明 ---
A variant of `Spec.fromSpecStalk_eq` that breaks abstraction boundaries.
-/
lemma Spec.fromSpecStalk_eq' : (Spec R).fromSpecStalk x = Spec.map (StructureSheaf.toStalk R _) :=
  Spec.fromSpecStalk_eq _ _

@[deprecated (since := "2026-02-05")] alias Scheme.Spec_fromSpecStalk := Spec.fromSpecStalk_eq
@[deprecated (since := "2026-02-05")] alias Scheme.Spec_fromSpecStalk' := Spec.fromSpecStalk_eq'

end Spec

end fromSpecStalk

variable (R : CommRingCat.{u}) [IsLocalRing R]

section stalkClosedPointIso

/-- For a local ring `(R, 𝔪)`,
this is the isomorphism between the stalk of `Spec R` at `𝔪` and `R`. -/
noncomputable
/-
**AlgebraicGeometry.stalkClosedPointIso** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeom
etry`。
形式化陈述：stalkClosedPointIso : (Spec R).presheaf.stalk (closedPoint R) ≅ R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def stalkClosedPointIso :
    (Spec R).presheaf.stalk (closedPoint R) ≅ R :=
  Spec.stalkIso _ _ ≪≫ (IsLocalization.atUnits R
      (closedPoint R).asIdeal.primeCompl fun _ ↦ not_not.mp).toRingEquiv.toCommRingCatIso.symm

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.stalkClosedPointIso_inv** 是 Mathlib 中的一个引理，位于命名空间 `Algebraic
Geometry`。
形式化陈述：stalkClosedPointIso_inv : (stalkClosedPointIso R).inv = StructureSheaf.toS
talk R _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CommRingCat.hom_ext`：hom_ext {R S : CommRingCat} {f g : R ⟶ S} (hf : f.h
om = g.hom) : f = g
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `AlgEquiv.commutes`：commutes : forall r : R, e (algebraMap R A₁ r) = alge
braMap R A₂ r
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
-/
lemma stalkClosedPointIso_inv :
    (stalkClosedPointIso R).inv = StructureSheaf.toStalk R _ := by
  ext x
  exact (StructureSheaf.stalkIso _ _).commutes _

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ΓSpecIso_hom_stalkClosedPointIso_inv :
    (Scheme.ΓSpecIso R).hom ≫ (stalkClosedPointIso R).inv =
      (Spec R).presheaf.germ ⊤ (closedPoint _) trivial := by
  rw [stalkClosedPointIso_inv, ← Iso.eq_inv_comp]
  rfl

@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.germ_stalkClosedPointIso_hom** 是 Mathlib 中的一个引理，位于命名空间 `Alge
braicGeometry`。
形式化陈述：germ_stalkClosedPointIso_hom : (Spec R).presheaf.germ ⊤ (closedPoint _) tr
ivial ≫ (stalkClosedPointIso R).hom = (Scheme.ΓSpecIso R).hom
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `AlgebraicGeometry.ΓSpecIso_hom_stalkClosedPointIso_inv`：ΓSpecIso_hom_sta
lkClosedPointIso_inv : (Scheme.ΓSpecIso R).hom ≫ (stalkClosedPointIso R).inv = (
Spec R).presheaf.germ ⊤ (closedPoint _) triv…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
lemma germ_stalkClosedPointIso_hom :
    (Spec R).presheaf.germ ⊤ (closedPoint _) trivial ≫ (stalkClosedPointIso R).hom =
      (Scheme.ΓSpecIso R).hom := by
  rw [← ΓSpecIso_hom_stalkClosedPointIso_inv, Category.assoc, Iso.inv_hom_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.Spec_stalkClosedPointIso** 是 Mathlib 中的一个引理，位于命名空间 `Algebrai
cGeometry`。
形式化陈述：Spec_stalkClosedPointIso : Spec.map (stalkClosedPointIso R).inv = (Spec R)
.fromSpecStalk (closedPoint R)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.stalkClosedPointIso_inv`：stalkClosedPointIso_inv : (st
alkClosedPointIso R).inv = StructureSheaf.toStalk R _
· 使用定理 `AlgebraicGeometry.Spec.fromSpecStalk_eq'`：∀ (R : CommRingCat) (x : ↥(Alg
ebraicGeometry.Spec R)),   (AlgebraicGeometry.Spec R).fromSpecStalk x =     Alge
braicGeometry.Spec.map (Algebr…
-/
lemma Spec_stalkClosedPointIso :
    Spec.map (stalkClosedPointIso R).inv = (Spec R).fromSpecStalk (closedPoint R) := by
  rw [stalkClosedPointIso_inv, Spec.fromSpecStalk_eq']

end stalkClosedPointIso

section stalkClosedPointTo

variable {R} (f : Spec R ⟶ X)

namespace Scheme

/--
Given a local ring `(R, 𝔪)` and a morphism `f : Spec R ⟶ X`,
they induce a (local) ring homomorphism `φ : 𝒪_{X, f 𝔪} ⟶ R`.

This is inverse to `φ ↦ Spec.map φ ≫ X.fromSpecStalk (f 𝔪)`. See `SpecToEquivOfLocalRing`.
-/
noncomputable
/-
**AlgebraicGeometry.Scheme.stalkClosedPointTo** 是 Mathlib 中的一个定义，位于命名空间 `Algebra
icGeometry.Scheme`。
形式化陈述：stalkClosedPointTo : X.presheaf.stalk (f (closedPoint R)) ⟶ R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def stalkClosedPointTo :
    X.presheaf.stalk (f (closedPoint R)) ⟶ R :=
  f.stalkMap (closedPoint R) ≫ (stalkClosedPointIso R).hom

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.Scheme.isLocalHom_stalkClosedPointTo** 是 Mathlib 中的一个实例，位于命名
空间 `AlgebraicGeometry.Scheme`。
形式化陈述：isLocalHom_stalkClosedPointTo : IsLocalHom (stalkClosedPointTo f).hom
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance isLocalHom_stalkClosedPointTo :
    IsLocalHom (stalkClosedPointTo f).hom :=
  inferInstanceAs <| IsLocalHom (f.stalkMap (closedPoint R) ≫ (stalkClosedPointIso R).hom).hom

/-- Copy of `isLocalHom_stalkClosedPointTo` which unbundles the comm ring.

Useful for use in combination with `CommRingCat.of K` for a field `K`.
-/
/-
**AlgebraicGeometry.Scheme.isLocalHom_stalkClosedPointTo'** 是 Mathlib 中的一个实例，位于命
名空间 `AlgebraicGeometry.Scheme`。
形式化陈述：isLocalHom_stalkClosedPointTo' {R : Type u} [CommRing R] [IsLocalRing R] (
f : Spec (.of R) ⟶ X) : IsLocalHom (stalkClosedPointTo f).hom
参数：f : Spec (.of R) ⟶ X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Copy of `isLocalHom_stalkClosedPointTo` which unbundles the comm ring.

Useful for use in combination with `CommRingCat.of K` for a field `K`.
-/
instance isLocalHom_stalkClosedPointTo' {R : Type u} [CommRing R] [IsLocalRing R]
    (f : Spec (.of R) ⟶ X) :
    IsLocalHom (stalkClosedPointTo f).hom :=
  isLocalHom_stalkClosedPointTo f
/-
**AlgebraicGeometry.Scheme.preimage_eq_top_of_closedPoint_mem** 是 Mathlib 中的一个引理
，位于命名空间 `AlgebraicGeometry.Scheme`。
形式化陈述：preimage_eq_top_of_closedPoint_mem {U : Opens X} (hU : f (closedPoint R) i
n U) : f ⁻¹ᵁ U = ⊤
参数：hU : f (closedPoint R) in U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `IsLocalRing.closed_point_mem_iff`：closed_point_mem_iff {U : TopologicalS
pace.Opens (PrimeSpectrum R)} : closedPoint R in U ↔ U = ⊤
-/
lemma preimage_eq_top_of_closedPoint_mem
    {U : Opens X} (hU : f (closedPoint R) ∈ U) : f ⁻¹ᵁ U = ⊤ :=
  IsLocalRing.closed_point_mem_iff.mp hU

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.Scheme.stalkClosedPointTo_comp** 是 Mathlib 中的一个引理，位于命名空间 `Al
gebraicGeometry.Scheme`。
形式化陈述：stalkClosedPointTo_comp (g : X ⟶ Y) : stalkClosedPointTo (f ≫ g) = g.stalk
Map _ ≫ stalkClosedPointTo f
参数：g : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.stalkClosedPointTo.eq_1`：∀ {X : AlgebraicGeomet
ry.Scheme} {R : CommRingCat} [inst : IsLocalRing ↑R] (f : AlgebraicGeometry.Spec
 R ⟶ X),   AlgebraicGeometry.Scheme.st…
· 使用引理 `AlgebraicGeometry.Scheme.Hom.stalkMap_comp`：stalkMap_comp {X Y Z : Schem
e.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) : (f ≫ g : X ⟶ Z).stalkMap x = g.stalkMap
 (f x) ≫ f.stalkMap x
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
-/
lemma stalkClosedPointTo_comp (g : X ⟶ Y) :
    stalkClosedPointTo (f ≫ g) = g.stalkMap _ ≫ stalkClosedPointTo f := by
  rw [stalkClosedPointTo, Scheme.Hom.stalkMap_comp]
  exact Category.assoc _ _ _

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.Scheme.germ_stalkClosedPointTo_Spec** 是 Mathlib 中的一个引理，位于命名空
间 `AlgebraicGeometry.Scheme`。
形式化陈述：germ_stalkClosedPointTo_Spec {R S : CommRingCat} [IsLocalRing S] (φ : R ⟶ 
S) : (Spec R).presheaf.germ ⊤ _ trivial ≫ stalkClosedPointTo (Spec.map φ) = (ΓSp
ecIso R).hom ≫ φ
参数：φ : R ⟶ S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.stalkClosedPointTo.eq_1`：∀ {X : AlgebraicGeomet
ry.Scheme} {R : CommRingCat} [inst : IsLocalRing ↑R] (f : AlgebraicGeometry.Spec
 R ⟶ X),   AlgebraicGeometry.Scheme.st…
· 使用定理 `AlgebraicGeometry.Scheme.Hom.germ_stalkMap_assoc`：∀ {X Y : AlgebraicGeom
etry.Scheme} (f : X ⟶ Y) (U : Y.Opens) (x : ↥X) (hx : f x ∈ U) {Z : CommRingCat}
   (h : X.presheaf.stalk x ⟶ Z),   Cat…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Iso.inv_comp_eq`：inv_comp_eq (α : X ≅ Y) {f : X ⟶ Z} {g :
 Y ⟶ Z} : α.inv ≫ f = g ↔ f = α.hom ≫ g
· 使用定理 `AlgebraicGeometry.Scheme.ΓSpecIso_inv_naturality_assoc`：∀ {R S : CommRin
gCat} (f : R ⟶ S) {Z : CommRingCat} (h : (AlgebraicGeometry.Spec S).presheaf.obj
 (Opposite.op ⊤) ⟶ Z),   CategoryTheory.Cate…
· 使用引理 `AlgebraicGeometry.germ_stalkClosedPointIso_hom`：germ_stalkClosedPointIso
_hom : (Spec R).presheaf.germ ⊤ (closedPoint _) trivial ≫ (stalkClosedPointIso R
).hom = (Scheme.ΓSpecIso R).hom
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
lemma germ_stalkClosedPointTo_Spec {R S : CommRingCat} [IsLocalRing S] (φ : R ⟶ S) :
    (Spec R).presheaf.germ ⊤ _ trivial ≫ stalkClosedPointTo (Spec.map φ) =
      (ΓSpecIso R).hom ≫ φ := by
  rw [stalkClosedPointTo, Scheme.Hom.germ_stalkMap_assoc, ← Iso.inv_comp_eq,
    ← ΓSpecIso_inv_naturality_assoc]
  simp_rw [Opens.map_top]
  rw [germ_stalkClosedPointIso_hom, Iso.inv_hom_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
/-
**AlgebraicGeometry.Scheme.germ_stalkClosedPointTo** 是 Mathlib 中的一个引理，位于命名空间 `Al
gebraicGeometry.Scheme`。
形式化陈述：germ_stalkClosedPointTo (U : Opens X) (hU : f (closedPoint R) in U) : X.pr
esheaf.germ U _ hU ≫ stalkClosedPointTo f = f.app U ≫ ((Spec R).presheaf.mapIso 
(eqToIso (preimage_eq_top_of_closedPoint_mem f hU).symm).op ≪≫ ΓSpecIso R).hom
参数：U : Opens X；hU : f (closedPoint R) in U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `AlgebraicGeometry.Scheme.preimage_eq_top_of_closedPoint_mem`：preimage_eq
_top_of_closedPoint_mem {U : Opens X} (hU : f (closedPoint R) in U) : f ⁻¹ᵁ U = 
⊤
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.stalkClosedPointTo.eq_1`：∀ {X : AlgebraicGeomet
ry.Scheme} {R : CommRingCat} [inst : IsLocalRing ↑R] (f : AlgebraicGeometry.Spec
 R ⟶ X),   AlgebraicGeometry.Scheme.st…
· 使用定理 `AlgebraicGeometry.Scheme.Hom.germ_stalkMap_assoc`：∀ {X Y : AlgebraicGeom
etry.Scheme} (f : X ⟶ Y) (U : Y.Opens) (x : ↥X) (hx : f x ∈ U) {Z : CommRingCat}
   (h : X.presheaf.stalk x ⟶ Z),   Cat…
· 使用定理 `CategoryTheory.Iso.trans_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y Z : C} (α : X ≅ Y) (β : Y ≅ Z),   (α ≪≫ β).hom = CategoryThe
ory.CategoryStruct…
· 使用定理 `CategoryTheory.Iso.eq_comp_inv`：eq_comp_inv (α : X ≅ Y) {f : Z ⟶ Y} {g :
 Z ⟶ X} : g = f ≫ α.inv ↔ g ≫ α.hom = f
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `trivial`：True
· 使用引理 `AlgebraicGeometry.ΓSpecIso_hom_stalkClosedPointIso_inv`：ΓSpecIso_hom_sta
lkClosedPointIso_inv : (Scheme.ΓSpecIso R).hom ≫ (stalkClosedPointIso R).inv = (
Spec R).presheaf.germ ⊤ (closedPoint _) triv…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Iso.op_hom`：∀ {C : Type u₁} [inst : CategoryTheory.Catego
ry.{v₁, u₁} C] {X Y : C} (α : X ≅ Y), α.op.hom = α.hom.op
· 使用定理 `TopCat.Presheaf.germ_res`：germ_res (F : X.Presheaf C) {U V : Opens X} (i
 : U ⟶ V) (x : X) (hx : x in U) : F.map i.op ≫ F.germ U x hx = F.germ V x (i.le 
hx)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma germ_stalkClosedPointTo (U : Opens X) (hU : f (closedPoint R) ∈ U) :
    X.presheaf.germ U _ hU ≫ stalkClosedPointTo f = f.app U ≫
      ((Spec R).presheaf.mapIso (eqToIso (preimage_eq_top_of_closedPoint_mem f hU).symm).op ≪≫
        ΓSpecIso R).hom := by
  rw [stalkClosedPointTo, Scheme.Hom.germ_stalkMap_assoc, Iso.trans_hom]
  congr 1
  rw [← Iso.eq_comp_inv, Category.assoc, ΓSpecIso_hom_stalkClosedPointIso_inv]
  simp only [Functor.mapIso_hom, Iso.op_hom, eqToIso.hom,
    TopCat.Presheaf.germ_res]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**AlgebraicGeometry.Scheme.germ_stalkClosedPointTo_Spec_fromSpecStalk** 是 Mathli
b 中的一个引理，位于命名空间 `AlgebraicGeometry.Scheme`。
形式化陈述：germ_stalkClosedPointTo_Spec_fromSpecStalk {x : X} (f : X.presheaf.stalk x
 ⟶ R) [IsLocalHom f.hom] (U : Opens X) (hU) : X.presheaf.germ U _ hU ≫ stalkClos
edPointTo (Spec.map f ≫ X.fromSpecStalk x) = X.presheaf.germ U x (by simpa using
 hU) ≫ f
参数：f : X.presheaf.stalk x ⟶ R；U : Opens X；hU。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.Hom.comp_apply`：comp_apply {X Y Z : Scheme} (f 
: X ⟶ Y) (g : Y ⟶ Z) (x : X) : (f ≫ g) x = g (f x)
· 使用定理 `AlgebraicGeometry.LocallyRingedSpace.instIsLocalRingCarrierStalkCommRing
CatPresheaf`：∀ (X : AlgebraicGeometry.LocallyRingedSpace) (x : ↑X.toTopCat), IsL
ocalRing ↑(X.presheaf.stalk x)
· 使用定理 `AlgebraicGeometry.Spec_closedPoint`：∀ {R S : CommRingCat} [inst : IsLoca
lRing ↑R] [inst_1 : IsLocalRing ↑S] {f : R ⟶ S}   [IsLocalHom (CommRingCat.Hom.h
om f)],   (AlgebraicGeom…
· 使用引理 `AlgebraicGeometry.Scheme.fromSpecStalk_closedPoint`：fromSpecStalk_closed
Point {x : X} : X.fromSpecStalk x (closedPoint (X.presheaf.stalk x)) = x
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `AlgebraicGeometry.Scheme.preimage_eq_top_of_closedPoint_mem`：preimage_eq
_top_of_closedPoint_mem {U : Opens X} (hU : f (closedPoint R) in U) : f ⁻¹ᵁ U = 
⊤
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `AlgebraicGeometry.Scheme.germ_stalkClosedPointTo`：germ_stalkClosedPointT
o (U : Opens X) (hU : f (closedPoint R) in U) : X.presheaf.germ U _ hU ≫ stalkCl
osedPointTo f = f.app U ≫ ((Spec R).pr…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `AlgebraicGeometry.Scheme.fromSpecStalk_app`：fromSpecStalk_app {x : X} (h
xU : x in U) : (X.fromSpecStalk x).app U = X.presheaf.germ U x hxU ≫ (ΓSpecIso (
X.presheaf.stalk x)).inv ≫ (Spec…
· 使用引理 `AlgebraicGeometry.Scheme.Hom.app_eq_appLE`：app_eq_appLE {U : Y.Opens} : 
f.app U = f.appLE U _ le_rfl
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `AlgebraicGeometry.Scheme.Hom.appLE_map_assoc`：∀ {X Y : AlgebraicGeometry
.Scheme} (f : X ⟶ Y) {U : Y.Opens} {V V' : X.Opens}   (e : V ≤ (TopologicalSpace
.Opens.map f.base).obj U) (i : Opp…
· 使用定理 `AlgebraicGeometry.Scheme.Hom.map_appLE_assoc`：∀ {X Y : AlgebraicGeometry
.Scheme} (f : X ⟶ Y) {U U' : Y.Opens} {V : X.Opens}   (e : V ≤ (TopologicalSpace
.Opens.map f.base).obj U) (i : Opp…
· 使用引理 `AlgebraicGeometry.Scheme.ΓSpecIso_naturality`：ΓSpecIso_naturality {R S :
 CommRingCat.{u}} (f : R ⟶ S) : (Spec.map f).appTop ≫ (ΓSpecIso S).hom = (ΓSpecI
so R).hom ≫ f
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
-/
lemma germ_stalkClosedPointTo_Spec_fromSpecStalk
    {x : X} (f : X.presheaf.stalk x ⟶ R) [IsLocalHom f.hom] (U : Opens X) (hU) :
    X.presheaf.germ U _ hU ≫ stalkClosedPointTo (Spec.map f ≫ X.fromSpecStalk x) =
      X.presheaf.germ U x (by simpa using hU) ≫ f := by
  have : (Spec.map f ≫ X.fromSpecStalk x) (closedPoint R) = x := by
    rw [Hom.comp_apply, Spec_closedPoint, fromSpecStalk_closedPoint]
  have : x ∈ U := this ▸ hU
  simp only [germ_stalkClosedPointTo, Hom.comp_app,
    fromSpecStalk_app (X := X) (x := x) this, Category.assoc, Iso.trans_hom, Functor.mapIso_hom,
      (Spec.map f).app_eq_appLE, Hom.appLE_map_assoc, Hom.map_appLE_assoc]
  simp_rw [← Opens.map_top (Spec.map f).base]
  rw [← (Spec.map f).app_eq_appLE, ΓSpecIso_naturality, Iso.inv_hom_id_assoc]

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.Scheme.stalkClosedPointTo_fromSpecStalk** 是 Mathlib 中的一个引理，位
于命名空间 `AlgebraicGeometry.Scheme`。
形式化陈述：stalkClosedPointTo_fromSpecStalk (x : X) : stalkClosedPointTo (X.fromSpecS
talk x) = (X.presheaf.stalkCongr (by rw [fromSpecStalk_closedPoint]; rfl)).hom
参数：x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopCat.Presheaf.stalk_hom_ext`：stalk_hom_ext (F : X.Presheaf C) {x} {Y :
 C} {f₁ f₂ : F.stalk x ⟶ Y} (ih : forall (U : Opens X) (hxU : x in U), F.germ U 
x hxU ≫ f₁ = F.germ…
· 使用定理 `AlgebraicGeometry.LocallyRingedSpace.instIsLocalRingCarrierStalkCommRing
CatPresheaf`：∀ (X : AlgebraicGeometry.LocallyRingedSpace) (x : ↑X.toTopCat), IsL
ocalRing ↑(X.presheaf.stalk x)
· 使用定理 `Specializes.mem_open`：Specializes.mem_open (h : x ⤳ y) (hs : IsOpen s) (
hy : y in s) : x in s
· 使用定理 `TopologicalSpace.Opens.isOpen`：∀ {α : Type u_2} [inst : TopologicalSpace
 α] (U : TopologicalSpace.Opens α), IsOpen ↑U
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `TopCat.Presheaf.stalkCongr_hom`：∀ {C : Type u} [inst : CategoryTheory.Ca
tegory.{v, u} C] [inst_1 : CategoryTheory.Limits.HasColimits C] {X : TopCat}   (
F : TopCat.Presheaf …
· 使用定理 `TopCat.Presheaf.germ_stalkSpecializes`：germ_stalkSpecializes (F : X.Pres
heaf C) {U : Opens X} {y : X} (hy : y in U) {x : X} (h : x ⤳ y) : F.germ U y hy 
≫ F.stalkSpecializes h = F.…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AlgebraicGeometry.Spec.map_id`：∀ (R : CommRingCat),   AlgebraicGeometry.
Spec.map (CategoryTheory.CategoryStruct.id R) =     CategoryTheory.CategoryStruc
t.id (AlgebraicGeom…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `isLocalHom_of_isIso`：isLocalHom_of_isIso {R S : CommRingCat} (f : R ⟶ S)
 [IsIso f] : IsLocalHom f.hom
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `AlgebraicGeometry.Scheme.germ_stalkClosedPointTo_Spec_fromSpecStalk`：ger
m_stalkClosedPointTo_Spec_fromSpecStalk {x : X} (f : X.presheaf.stalk x ⟶ R) [Is
LocalHom f.hom] (U : Opens X) (hU) : X.presheaf.germ U _ …
-/
lemma stalkClosedPointTo_fromSpecStalk (x : X) :
    stalkClosedPointTo (X.fromSpecStalk x) =
      (X.presheaf.stalkCongr (by rw [fromSpecStalk_closedPoint]; rfl)).hom := by
  refine TopCat.Presheaf.stalk_hom_ext _ fun U hxU ↦ ?_
  simp only [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.germ_stalkSpecializes]
  have : X.fromSpecStalk x = Spec.map (𝟙 (X.presheaf.stalk x)) ≫ X.fromSpecStalk x := by simp
  convert! germ_stalkClosedPointTo_Spec_fromSpecStalk (𝟙 (X.presheaf.stalk x)) U hxU

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
/-
**AlgebraicGeometry.Scheme.Spec_stalkClosedPointTo_fromSpecStalk** 是 Mathlib 中的一
个引理，位于命名空间 `AlgebraicGeometry.Scheme`。
形式化陈述：Spec_stalkClosedPointTo_fromSpecStalk : Spec.map (stalkClosedPointTo f) ≫ 
X.fromSpecStalk _ = f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.IsTopologicalBasis.exists_subset_of_mem_open`：∀ {α : Ty
pe u} [t : TopologicalSpace α] {b : Set (Set α)},   TopologicalSpace.IsTopologic
alBasis b → ∀ {a : α} {u : Set α}, a ∈ u → IsOpen u…
· 使用定理 `AlgebraicGeometry.Scheme.isBasis_affineOpens`：∀ (X : AlgebraicGeometry.S
cheme), TopologicalSpace.Opens.IsBasis X.affineOpens
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `isOpen_univ`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen Set.univ
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用引理 `AlgebraicGeometry.Scheme.preimage_eq_top_of_closedPoint_mem`：preimage_eq
_top_of_closedPoint_mem {U : Opens X} (hU : f (closedPoint R) in U) : f ⁻¹ᵁ U = 
⊤
· 使用定理 `AlgebraicGeometry.isAffineOpen_top`：isAffineOpen_top (X : Scheme) [IsAff
ine X] : IsAffineOpen (⊤ : X.Opens)
· 使用引理 `AlgebraicGeometry.IsAffineOpen.SpecMap_appLE_fromSpec`：SpecMap_appLE_fro
mSpec (f : X ⟶ Y) {V : X.Opens} {U : Y.Opens} (hU : IsAffineOpen U) (hV : IsAffi
neOpen V) (i : V <= f ⁻¹ᵁ U) : Spec.map (f.…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.IsAffineOpen.fromSpecStalk_eq_fromSpecStalk`：∀ {X : Al
gebraicGeometry.Scheme} {U : X.Opens} (hU : AlgebraicGeometry.IsAffineOpen U) {x
 : ↥X} (hxU : x ∈ U),   hU.fromSpecStalk hxU = X.fr…
· 使用定理 `AlgebraicGeometry.IsAffineOpen.fromSpecStalk.eq_1`：∀ {X : AlgebraicGeome
try.Scheme} {U : X.Opens} (hU : AlgebraicGeometry.IsAffineOpen U) {x : ↥X} (hxU 
: x ∈ U),   hU.fromSpecStalk hxU =     …
· 使用定理 `AlgebraicGeometry.Spec.map_comp_assoc`：∀ {R S T : CommRingCat} (f : R ⟶ 
S) (g : S ⟶ T) {Z : AlgebraicGeometry.Scheme} (h : AlgebraicGeometry.Spec R ⟶ Z)
,   CategoryTheory.Category…
· 使用引理 `AlgebraicGeometry.Scheme.germ_stalkClosedPointTo`：germ_stalkClosedPointT
o (U : Opens X) (hU : f (closedPoint R) in U) : X.presheaf.germ U _ hU ≫ stalkCl
osedPointTo f = f.app U ≫ ((Spec R).pr…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `AlgebraicGeometry.Scheme.Hom.app_eq_appLE`：app_eq_appLE {U : Y.Opens} : 
f.app U = f.appLE U _ le_rfl
· 使用定理 `CategoryTheory.Iso.op_hom`：∀ {C : Type u₁} [inst : CategoryTheory.Catego
ry.{v₁, u₁} C] {X Y : C} (α : X ≅ Y), α.op.hom = α.hom.op
· 使用定理 `AlgebraicGeometry.Scheme.Hom.appLE_map_assoc`：∀ {X Y : AlgebraicGeometry
.Scheme} (f : X ⟶ Y) {U : Y.Opens} {V V' : X.Opens}   (e : V ≤ (TopologicalSpace
.Opens.map f.base).obj U) (i : Opp…
· 使用定理 `AlgebraicGeometry.Scheme.isoSpec_Spec_hom`：∀ (R : CommRingCat),   (Algeb
raicGeometry.Spec R).isoSpec.hom = AlgebraicGeometry.Spec.map (AlgebraicGeometry
.Scheme.ΓSpecIso R).hom
· 使用定理 `CategoryTheory.Iso.eq_inv_comp`：eq_inv_comp (α : X ≅ Y) {f : X ⟶ Z} {g :
 Y ⟶ Z} : g = α.inv ≫ f ↔ α.hom ≫ g = f
· 使用引理 `AlgebraicGeometry.IsAffineOpen.fromSpec_top`：fromSpec_top [IsAffine X] :
 (isAffineOpen_top X).fromSpec = X.isoSpec.inv
-/
lemma Spec_stalkClosedPointTo_fromSpecStalk :
    Spec.map (stalkClosedPointTo f) ≫ X.fromSpecStalk _ = f := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (f (closedPoint R))) isOpen_univ
  have := IsAffineOpen.SpecMap_appLE_fromSpec f hU (isAffineOpen_top _)
    (preimage_eq_top_of_closedPoint_mem f hxU).ge
  rw [IsAffineOpen.fromSpec_top, Iso.eq_inv_comp, isoSpec_Spec_hom] at this
  rw [← hU.fromSpecStalk_eq_fromSpecStalk hxU, IsAffineOpen.fromSpecStalk, ← Spec.map_comp_assoc,
    germ_stalkClosedPointTo]
  simpa only [Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, Category.assoc,
    Hom.app_eq_appLE, Hom.appLE_map_assoc, Spec.map_comp_assoc]

end Scheme

end stalkClosedPointTo

variable {R}

omit [IsLocalRing R] in
/-- useful lemma for applications of `SpecToEquivOfLocalRing` -/
/-
**AlgebraicGeometry.SpecToEquivOfLocalRing_eq_iff** 是 Mathlib 中的一个引理，位于命名空间 `Alg
ebraicGeometry`。
形式化陈述：SpecToEquivOfLocalRing_eq_iff {f₁ f₂ : Σ x, { f : X.presheaf.stalk x ⟶ R /
/ IsLocalHom f.hom }} : f₁ = f₂ ↔ exists h₁ : f₁.1 = f₂.1, f₁.2.1 = (X.presheaf.
stalkCongr (by rw [h₁]; rfl)).hom ≫ f₂.2.1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TopCat.Presheaf.stalkCongr_hom`：∀ {C : Type u} [inst : CategoryTheory.Ca
tegory.{v, u} C] [inst_1 : CategoryTheory.Limits.HasColimits C] {X : TopCat}   (
F : TopCat.Presheaf …
· 使用定理 `TopCat.Presheaf.stalkSpecializes_refl`：stalkSpecializes_refl (F : X.Pres
heaf C) (x : X) : F.stalkSpecializes (specializes_refl x) = 𝟙 _
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩

--- 原说明 ---
useful lemma for applications of `SpecToEquivOfLocalRing`
-/
lemma SpecToEquivOfLocalRing_eq_iff
    {f₁ f₂ : Σ x, { f : X.presheaf.stalk x ⟶ R // IsLocalHom f.hom }} :
    f₁ = f₂ ↔ ∃ h₁ : f₁.1 = f₂.1, f₁.2.1 =
      (X.presheaf.stalkCongr (by rw [h₁]; rfl)).hom ≫ f₂.2.1 := by
  constructor
  · rintro rfl; simp
  · obtain ⟨x₁, ⟨f₁, h₁⟩⟩ := f₁
    obtain ⟨x₂, ⟨f₂, h₂⟩⟩ := f₂
    rintro ⟨rfl : x₁ = x₂, e : f₁ = _⟩
    simp [e]

variable (X R)

set_option backward.isDefEq.respectTransparency.types false in
/--
Given a local ring `R` and scheme `X`, morphisms `Spec R ⟶ X` corresponds to pairs
`(x, f)` where `x : X` and `f : 𝒪_{X, x} ⟶ R` is a local ring homomorphism.
-/
@[simps]
noncomputable
/-
**AlgebraicGeometry.SpecToEquivOfLocalRing** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicG
eometry`。
形式化陈述：SpecToEquivOfLocalRing : (Spec R ⟶ X) ≃ Σ x, { f : X.presheaf.stalk x ⟶ R 
// IsLocalHom f.hom } where toFun f
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.Scheme.Spec_stalkClosedPointTo_fromSpecStalk`：Spec_sta
lkClosedPointTo_fromSpecStalk : Spec.map (stalkClosedPointTo f) ≫ X.fromSpecStal
k _ = f
-/
def SpecToEquivOfLocalRing :
    (Spec R ⟶ X) ≃ Σ x, { f : X.presheaf.stalk x ⟶ R // IsLocalHom f.hom } where
  toFun f := ⟨f (closedPoint R), Scheme.stalkClosedPointTo f, inferInstance⟩
  invFun xf := Spec.map xf.2.1 ≫ X.fromSpecStalk xf.1
  left_inv := Scheme.Spec_stalkClosedPointTo_fromSpecStalk
  right_inv xf := by
    obtain ⟨x, ⟨f, hf⟩⟩ := xf
    symm
    refine SpecToEquivOfLocalRing_eq_iff.mpr ⟨?_, ?_⟩
    · simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply, Spec_closedPoint,
        Scheme.fromSpecStalk_closedPoint]
    · refine TopCat.Presheaf.stalk_hom_ext _ fun U hxU ↦ ?_
      simp only [Scheme.germ_stalkClosedPointTo_Spec_fromSpecStalk,
        TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.germ_stalkSpecializes_assoc]

end AlgebraicGeometry

