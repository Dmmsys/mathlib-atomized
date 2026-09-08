/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.RingHom.LocallyStandardSmooth
public import Mathlib.RingTheory.Smooth.Flat
public import Mathlib.RingTheory.Smooth.Field

/-!

# Smooth morphisms

In this file we define smooth morphisms. The main definitions are:

- `AlgebraicGeometry.Smooth`: A morphism of schemes `f : X ⟶ Y` is smooth if for each affine `U ⊆ Y`
  and `V ⊆ f ⁻¹' U`, the induced map `Γ(Y, U) ⟶ Γ(X, V)` is smooth.

- `AlgebraicGeometry.SmoothOfRelativeDimension`: A morphism of schemes `f : X ⟶ Y` is smooth of
  relative dimension `n` if for each `x : X` there exists an affine open neighborhood `V` of `x`
  and an affine open neighborhood `U` of `f.base x` with `V ≤ f ⁻¹ᵁ U` such that the induced
  map `Γ(Y, U) ⟶ Γ(X, V)` is standard smooth (of relative dimension `n`).

## Main results

- `AlgebraicGeometry.Smooth.iff_forall_exists_isStandardSmooth`: A morphism of schemes is smooth
  if and only if for each `x : X` there exists an affine open neighborhood `V` of `x`
  and an affine open neighborhood `U` of `f.base x` with `V ≤ f ⁻¹ᵁ U` such that the induced
  map `Γ(Y, U) ⟶ Γ(X, V)` is standard smooth.

## Notes

This contribution was created as part of the AIM workshop "Formalizing algebraic geometry" in
June 2024.

-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe t w v u

namespace AlgebraicGeometry

open RingHom

variable (n m : ℕ) {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- A morphism of schemes `f : X ⟶ Y` is smooth if for each affine `U ⊆ Y` and
`V ⊆ f ⁻¹' U`, The induced map `Γ(Y, U) ⟶ Γ(X, V)` is smooth. -/
@[mk_iff]
/-
**AlgebraicGeometry.Smooth** 是 Mathlib 中的一个类，位于命名空间 `AlgebraicGeometry`。
形式化陈述：Smooth (f : X ⟶ Y) : Prop where smooth_appLE (f) : forall {U : Y.Opens} (_
 : IsAffineOpen U) {V : X.Opens} (_ : IsAffineOpen V) (e : V <= f ⁻¹ᵁ U), (f.app
LE U V e).hom.Smooth  alias Scheme.Hom.smooth_appLE
参数：f : X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism of schemes `f : X ⟶ Y` is smooth if for each affine `U ⊆ Y` and
`V ⊆ f ⁻¹' U`, The induced map `Γ(Y, U) ⟶ Γ(X, V)` is smooth.
-/
class Smooth (f : X ⟶ Y) : Prop where
  smooth_appLE (f) :
    ∀ {U : Y.Opens} (_ : IsAffineOpen U) {V : X.Opens} (_ : IsAffineOpen V) (e : V ≤ f ⁻¹ᵁ U),
      (f.appLE U V e).hom.Smooth

alias Scheme.Hom.smooth_appLE := Smooth.smooth_appLE

@[deprecated (since := "2026-02-09")] alias IsSmooth := Smooth

/-- The property of scheme morphisms `Smooth` is associated with the ring
homomorphism property `Smooth`. -/
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The property of scheme morphisms `Smooth` is associated with the ring
homomorphism property `Smooth`.
-/
instance : HasRingHomProperty @Smooth RingHom.Smooth where
  isLocal_ringHomProperty := RingHom.Smooth.propertyIsLocal
  eq_affineLocally' := by
    ext X Y f
    rw [smooth_iff, affineLocally_iff_forall_isAffineOpen]

/--
A morphism of schemes is smooth if and only if for each `x : X` there exists an affine open
neighborhood `V` of `x` and an affine open neighborhood `U` of `f.base x` with `V ≤ f ⁻¹ᵁ U`
such that the induced map `Γ(Y, U) ⟶ Γ(X, V)` is standard smooth.
-/
/-
**AlgebraicGeometry.Smooth.iff_forall_exists_isStandardSmooth** 是 Mathlib 中的一个定理
，位于命名空间 `AlgebraicGeometry.Smooth`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y),   AlgebraicGeometry.Smooth
 f ↔     ∀ (x : ↥X),       ∃ U,         ∃ (_ : AlgebraicGeometry.IsAffineOpen U)
,           ∃ V,             ∃ (_ : AlgebraicGeometry.IsAffineOpen V) (_ : x ∈ V
) (e : V ≤ (TopologicalSpace.Opens.map f.base).obj U),               (CommRingCa
t.Hom.hom (AlgebraicGeometry.Scheme.Hom.appLE f U V e)).IsStandardSmooth
参数：f : X ⟶ Y；x : ↥X；_ : AlgebraicGeometry.IsAffineOpen U；_ : AlgebraicGeometry.I
sAffineOpen V；_ : x ∈ V；e : V ≤ (TopologicalSpace.Opens.map f.base).obj U；CommRi
ngCat.Hom.hom (AlgebraicGeometry.Scheme.Hom.appLE f U V e)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.smooth_iff_locally_isStandardSmooth`：smooth_iff_locally_isStanda
rdSmooth : Smooth f ↔ Locally IsStandardSmooth f
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `AlgebraicGeometry.instHasRingHomPropertySmoothSmooth`：AlgebraicGeometry.
HasRingHomProperty @AlgebraicGeometry.Smooth fun {R S} [CommRing R] [CommRing S]
 => RingHom.Smooth
· 使用引理 `AlgebraicGeometry.HasRingHomProperty.iff_exists_appLE_locally`：iff_exist
s_appLE_locally (hQ : RingHom.StableUnderCompositionWithLocalizationAwaySource Q
) (hQi : RespectsIso Q) [HasRingHomProperty P (Loca…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `RingHom.isStandardSmooth_stableUnderCompositionWithLocalizationAway`：isS
tandardSmooth_stableUnderCompositionWithLocalizationAway : StableUnderCompositio
nWithLocalizationAway IsStandardSmooth
· 使用引理 `RingHom.isStandardSmooth_respectsIso`：isStandardSmooth_respectsIso : Res
pectsIso @IsStandardSmooth
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `pi_congr`：∀ {α : Sort u} {β β' : α → Sort v}, (∀ (a : α), β a = β' a) → 
((a : α) → β a) = ((a : α) → β' a)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯

--- 原说明 ---
A morphism of schemes is smooth if and only if for each `x : X` there exists an 
affine open
neighborhood `V` of `x` and an affine open neighborhood `U` of `f.base x` with `
V ≤ f ⁻¹ᵁ U`
such that the induced map `Γ(Y, U) ⟶ Γ(X, V)` is standard smooth.
-/
lemma Smooth.iff_forall_exists_isStandardSmooth (f : X ⟶ Y) :
    Smooth f ↔
      ∀ (x : X), ∃ (U : Y.Opens) (_ : IsAffineOpen U) (V : X.Opens) (_ : IsAffineOpen V) (_ : x ∈ V)
        (e : V ≤ f ⁻¹ᵁ U), (f.appLE U V e).hom.IsStandardSmooth := by
  have : HasRingHomProperty @Smooth.{u} (Locally IsStandardSmooth) := by
    convert! (inferInstance : HasRingHomProperty (@Smooth.{u}) RingHom.Smooth)
    ext f
    rw [RingHom.smooth_iff_locally_isStandardSmooth]
  rw [HasRingHomProperty.iff_exists_appLE_locally (P := @Smooth)]
  · congr!
    simp [Subtype.exists]
    grind [Scheme.affineOpens]
  · exact isStandardSmooth_stableUnderCompositionWithLocalizationAway.left
  · exact isStandardSmooth_respectsIso
/-
**AlgebraicGeometry.Smooth.exists_isStandardSmooth** 是 Mathlib 中的一个定理，位于命名空间 `Al
gebraicGeometry.Smooth`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.Smooth f
] (x : ↥X),   ∃ U,     ∃ (_ : AlgebraicGeometry.IsAffineOpen U),       ∃ V,     
    ∃ (_ : AlgebraicGeometry.IsAffineOpen V) (_ : x ∈ V) (e : V ≤ (TopologicalSp
ace.Opens.map f.base).obj U),           (CommRingCat.Hom.hom (AlgebraicGeometry.
Scheme.Hom.appLE f U V e)).IsStandardSmooth
参数：f : X ⟶ Y；x : ↥X；_ : AlgebraicGeometry.IsAffineOpen U；_ : AlgebraicGeometry.I
sAffineOpen V；_ : x ∈ V；e : V ≤ (TopologicalSpace.Opens.map f.base).obj U；CommRi
ngCat.Hom.hom (AlgebraicGeometry.Scheme.Hom.appLE f U V e)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AlgebraicGeometry.Smooth.iff_forall_exists_isStandardSmooth`：∀ {X Y : Al
gebraicGeometry.Scheme} (f : X ⟶ Y),   AlgebraicGeometry.Smooth f ↔     ∀ (x : ↥
X),       ∃ U,         ∃ (_ : AlgebraicGeometry.I…
-/
lemma Smooth.exists_isStandardSmooth (f : X ⟶ Y) [Smooth f] (x : X) :
    ∃ (U : Y.Opens) (_ : IsAffineOpen U) (V : X.Opens) (_ : IsAffineOpen V) (_ : x ∈ V)
        (e : V ≤ f ⁻¹ᵁ U), (f.appLE U V e).hom.IsStandardSmooth :=
  (iff_forall_exists_isStandardSmooth f).mp ‹_› x

/-- Being smooth is stable under composition. -/
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Being smooth is stable under composition.
-/
instance : MorphismProperty.IsStableUnderComposition @Smooth :=
  HasRingHomProperty.stableUnderComposition Smooth.stableUnderComposition

/-- The composition of smooth morphisms is smooth. -/
/-
**AlgebraicGeometry.smooth_comp** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
形式化陈述：smooth_comp {Z : Scheme.{u}} (g : Y ⟶ Z) [Smooth f] [Smooth g] : Smooth (f
 ≫ g)
参数：g : Y ⟶ Z。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.comp_mem`：comp_mem (W : MorphismProperty
 C) [W.IsStableUnderComposition] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : W f) 
(hg : W g) : W (f ≫ g)
· 使用定理 `AlgebraicGeometry.instIsStableUnderCompositionSchemeSmooth`：CategoryTheo
ry.MorphismProperty.IsStableUnderComposition @AlgebraicGeometry.Smooth

--- 原说明 ---
The composition of smooth morphisms is smooth.
-/
instance smooth_comp {Z : Scheme.{u}} (g : Y ⟶ Z) [Smooth f] [Smooth g] :
    Smooth (f ≫ g) :=
  MorphismProperty.comp_mem _ f g ‹Smooth f› ‹Smooth g›
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) [Smooth f] : Flat f where
  flat_appLE {_} hU {_} hV e := (f.smooth_appLE hU hV e).flat

/-- Smooth is stable under base change. -/
/-
**AlgebraicGeometry.smooth_isStableUnderBaseChange** 是 Mathlib 中的一个实例，位于命名空间 `Al
gebraicGeometry`。
形式化陈述：smooth_isStableUnderBaseChange : MorphismProperty.IsStableUnderBaseChange 
@Smooth
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.HasRingHomProperty.isStableUnderBaseChange`：isStableUn
derBaseChange (hP : RingHom.IsStableUnderBaseChange Q) : P.IsStableUnderBaseChan
ge
· 使用定理 `AlgebraicGeometry.instHasRingHomPropertySmoothSmooth`：AlgebraicGeometry.
HasRingHomProperty @AlgebraicGeometry.Smooth fun {R S} [CommRing R] [CommRing S]
 => RingHom.Smooth
· 使用引理 `RingHom.Smooth.isStableUnderBaseChange`：isStableUnderBaseChange : IsStab
leUnderBaseChange Smooth

--- 原说明 ---
Smooth is stable under base change.
-/
instance smooth_isStableUnderBaseChange : MorphismProperty.IsStableUnderBaseChange @Smooth :=
  HasRingHomProperty.isStableUnderBaseChange Smooth.isStableUnderBaseChange
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MorphismProperty.Respects @Smooth @IsOpenImmersion :=
  HasRingHomProperty.respects_isOpenImmersion
    (RingHom.Smooth.stableUnderComposition.stableUnderCompositionWithLocalizationAway
      RingHom.Smooth.holdsForLocalizationAway).1

@[deprecated (since := "2026-02-09")]
alias isSmooth_isStableUnderBaseChange := smooth_isStableUnderBaseChange

/--
A morphism of schemes `f : X ⟶ Y` is smooth of relative dimension `n` if for each `x : X` there
exists an affine open neighborhood `V` of `x` and an affine open neighborhood `U` of
`f.base x` with `V ≤ f ⁻¹ᵁ U` such that the induced map `Γ(Y, U) ⟶ Γ(X, V)` is
standard smooth of relative dimension `n`.
-/
@[mk_iff]
/-
**AlgebraicGeometry.SmoothOfRelativeDimension** 是 Mathlib 中的一个归纳类型，位于命名空间 `Algeb
raicGeometry`。
形式化陈述：ℕ → {X Y : AlgebraicGeometry.Scheme} → (X ⟶ Y) → Prop
参数：X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism of schemes `f : X ⟶ Y` is smooth of relative dimension `n` if for eac
h `x : X` there
exists an affine open neighborhood `V` of `x` and an affine open neighborhood `U
` of
`f.base x` with `V ≤ f ⁻¹ᵁ U` such that the induced map `Γ(Y, U) ⟶ Γ(X, V)` is
standard smooth of relative dimension `n`.
-/
class SmoothOfRelativeDimension : Prop where
  exists_isStandardSmoothOfRelativeDimension : ∀ (x : X), ∃ (U : Y.Opens) (_ : IsAffineOpen U)
    (V : X.Opens) (_ : IsAffineOpen V) (_ : x ∈ V) (e : V ≤ f ⁻¹ᵁ U),
    IsStandardSmoothOfRelativeDimension n (f.appLE U V e).hom

@[deprecated (since := "2026-02-09")] alias IsSmoothOfRelativeDimension := SmoothOfRelativeDimension

/-- If `f` is smooth of any relative dimension, it is smooth. -/
/-
**AlgebraicGeometry.SmoothOfRelativeDimension.smooth** 是 Mathlib 中的一个定理，位于命名空间 `
AlgebraicGeometry.SmoothOfRelativeDimension`。
形式化陈述：∀ (n : ℕ) {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.
SmoothOfRelativeDimension n f],   AlgebraicGeometry.Smooth f
参数：n : ℕ；f : X ⟶ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Smooth.iff_forall_exists_isStandardSmooth`：∀ {X Y : Al
gebraicGeometry.Scheme} (f : X ⟶ Y),   AlgebraicGeometry.Smooth f ↔     ∀ (x : ↥
X),       ∃ U,         ∃ (_ : AlgebraicGeometry.I…
· 使用定理 `AlgebraicGeometry.SmoothOfRelativeDimension.exists_isStandardSmoothOfRel
ativeDimension`：∀ {n : ℕ} {X Y : AlgebraicGeometry.Scheme} {f : X ⟶ Y} [self : A
lgebraicGeometry.SmoothOfRelativeDimension n f]   (x : ↥X),   ∃ U,     ∃ (_ …
· 使用定理 `RingHom.IsStandardSmoothOfRelativeDimension.isStandardSmooth`：∀ (n : ℕ) 
{R : Type u} {S : Type v} [inst : CommRing R] [inst_1 : CommRing S] (f : R →+* S
),   RingHom.IsStandardSmoothOfRelativeDimension n…

--- 原说明 ---
If `f` is smooth of any relative dimension, it is smooth.
-/
lemma SmoothOfRelativeDimension.smooth [SmoothOfRelativeDimension n f] : Smooth f := by
  rw [Smooth.iff_forall_exists_isStandardSmooth]
  intro x
  obtain ⟨U, hU, V, hV, hx, e, hf⟩ := exists_isStandardSmoothOfRelativeDimension (n := n) (f := f) x
  exact ⟨U, hU, V, hV, hx, e, hf.isStandardSmooth⟩

@[deprecated (since := "2026-02-09")]
alias IsSmoothOfRelativeDimension.isSmooth := SmoothOfRelativeDimension.smooth

/-- The property of scheme morphisms `SmoothOfRelativeDimension n` is associated with the ring
homomorphism property `Locally (IsStandardSmoothOfRelativeDimension n)`. -/
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The property of scheme morphisms `SmoothOfRelativeDimension n` is associated wit
h the ring
homomorphism property `Locally (IsStandardSmoothOfRelativeDimension n)`.
-/
instance : HasRingHomProperty (@SmoothOfRelativeDimension n)
    (Locally (IsStandardSmoothOfRelativeDimension n)) := by
  apply HasRingHomProperty.locally_of_iff
  · exact (isStandardSmoothOfRelativeDimension_localizationPreserves n).away
  · exact isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway n
  · intro X Y f
    rw [smoothOfRelativeDimension_iff]
    congr!
    simp [Subtype.exists]
    grind [Scheme.affineOpens]

/-- Smooth of relative dimension `n` is stable under base change. -/
/-
**AlgebraicGeometry.smoothOfRelativeDimension_isStableUnderBaseChange** 是 Mathli
b 中的一个引理，位于命名空间 `AlgebraicGeometry`。
形式化陈述：smoothOfRelativeDimension_isStableUnderBaseChange : MorphismProperty.IsSta
bleUnderBaseChange (@SmoothOfRelativeDimension n)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.HasRingHomProperty.isStableUnderBaseChange`：isStableUn
derBaseChange (hP : RingHom.IsStableUnderBaseChange Q) : P.IsStableUnderBaseChan
ge
· 使用定理 `AlgebraicGeometry.instHasRingHomPropertySmoothOfRelativeDimensionLocally
IsStandardSmoothOfRelativeDimension`：∀ (n : ℕ),   AlgebraicGeometry.HasRingHomPr
operty (@AlgebraicGeometry.SmoothOfRelativeDimension n)     fun {R S} [CommRing 
R] [CommRing S] =…
· 使用引理 `RingHom.locally_isStableUnderBaseChange`：locally_isStableUnderBaseChange
 (hPi : RespectsIso P) (hPb : IsStableUnderBaseChange P) : IsStableUnderBaseChan
ge (Locally P)
· 使用引理 `RingHom.isStandardSmoothOfRelativeDimension_respectsIso`：isStandardSmoot
hOfRelativeDimension_respectsIso : RespectsIso (@IsStandardSmoothOfRelativeDimen
sion n) where left {R S T _ _ _} f e hf
· 使用引理 `RingHom.isStandardSmoothOfRelativeDimension_isStableUnderBaseChange`：isS
tandardSmoothOfRelativeDimension_isStableUnderBaseChange : IsStableUnderBaseChan
ge (@IsStandardSmoothOfRelativeDimension n)

--- 原说明 ---
Smooth of relative dimension `n` is stable under base change.
-/
lemma smoothOfRelativeDimension_isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension n) :=
  HasRingHomProperty.isStableUnderBaseChange <| locally_isStableUnderBaseChange
    isStandardSmoothOfRelativeDimension_respectsIso
    (isStandardSmoothOfRelativeDimension_isStableUnderBaseChange n)

@[deprecated (since := "2026-02-09")]
alias isSmoothOfRelativeDimension_isStableUnderBaseChange :=
  smoothOfRelativeDimension_isStableUnderBaseChange

/-- Open immersions are smooth of relative dimension `0`. -/
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Open immersions are smooth of relative dimension `0`.
-/
instance (priority := 900) [IsOpenImmersion f] : SmoothOfRelativeDimension 0 f :=
  HasRingHomProperty.of_isOpenImmersion
    (locally_holdsForLocalizationAway <|
      isStandardSmoothOfRelativeDimension_holdsForLocalizationAway).containsIdentities

/-- Open immersions are smooth. -/
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Open immersions are smooth.
-/
instance (priority := 900) [IsOpenImmersion f] : Smooth f :=
  SmoothOfRelativeDimension.smooth 0 f

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [Smooth g] :
    Smooth (pullback.fst f g) :=
  MorphismProperty.pullback_fst f g inferInstance

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [Smooth f] :
    Smooth (pullback.snd f g) :=
  MorphismProperty.pullback_snd f g inferInstance

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (f : X ⟶ Y) (V : Y.Opens) [Smooth f] : Smooth (f ∣_ V) :=
  IsZariskiLocalAtTarget.restrict ‹_› V
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (f : X ⟶ Y) (U : X.Opens) (V : Y.Opens) (e) [Smooth f] :
    Smooth (f.resLE V U e) := by
  delta Scheme.Hom.resLE; infer_instance

/-- If `f` is smooth of relative dimension `n` and `g` is smooth of relative dimension
`m`, then `f ≫ g` is smooth of relative dimension `n + m`. -/
/-
**AlgebraicGeometry.smoothOfRelativeDimension_comp** 是 Mathlib 中的一个实例，位于命名空间 `Al
gebraicGeometry`。
形式化陈述：smoothOfRelativeDimension_comp {Z : Scheme.{u}} (g : Y ⟶ Z) [hf : SmoothOf
RelativeDimension n f] [hg : SmoothOfRelativeDimension m g] : SmoothOfRelativeDi
mension (n + m) (f ≫ g) where exists_isStandardSmoothOfRelativeDimension x
参数：g : Y ⟶ Z。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.SmoothOfRelativeDimension.exists_isStandardSmoothOfRel
ativeDimension`：∀ {n : ℕ} {X Y : AlgebraicGeometry.Scheme} {f : X ⟶ Y} [self : A
lgebraicGeometry.SmoothOfRelativeDimension n f]   (x : ↥X),   ∃ U,     ∃ (_ …
· 使用引理 `AlgebraicGeometry.exists_basicOpen_le_appLE_of_appLE_of_isAffine`：exists
_basicOpen_le_appLE_of_appLE_of_isAffine (hPa : StableUnderCompositionWithLocali
zationAwayTarget P) (hPl : LocalizationAwayPreserves P…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `RingHom.isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLo
calizationAway`：isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLo
calizationAway : StableUnderCompositionWithLocalizationAway (IsStandardSmoot…
· 使用定理 `RingHom.LocalizationPreserves.away`：RingHom.LocalizationPreserves.away (
H : RingHom.LocalizationPreserves @P) : RingHom.LocalizationAwayPreserves P
· 使用引理 `RingHom.isStandardSmoothOfRelativeDimension_localizationPreserves`：isSta
ndardSmoothOfRelativeDimension_localizationPreserves : LocalizationPreserves (Is
StandardSmoothOfRelativeDimension n)
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用引理 `AlgebraicGeometry.Scheme.Hom.preimage_mono`：preimage_mono {U U' : Y.Open
s} (hUU' : U <= U') : f ⁻¹ᵁ U <= f ⁻¹ᵁ U'
· 使用定理 `AlgebraicGeometry.Scheme.basicOpen_le`：basicOpen_le : X.basicOpen f <= U
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.algebraMap_toAlgebra`：RingHom.algebraMap_toAlgebra {R S} [CommSe
miring R] [CommSemiring S] (i : R ->+* S) : @algebraMap R S _ _ i.toAlgebra = i
· 使用引理 `CommRingCat.ofHom_hom`：ofHom_hom {R S : CommRingCat} (f : R ⟶ S) : ofHom
 (Hom.hom f) = f
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `AlgebraicGeometry.Scheme.Hom.appLE_map_assoc`：∀ {X Y : AlgebraicGeometry
.Scheme} (f : X ⟶ Y) {U : Y.Opens} {V V' : X.Opens}   (e : V ≤ (TopologicalSpace
.Opens.map f.base).obj U) (i : Opp…
· 使用定理 `AlgebraicGeometry.Scheme.Hom.appLE_comp_appLE`：appLE_comp_appLE {X Y Z :
 Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) (U V W e₁ e₂) : g.appLE U V e₁ ≫ f.appLE V W e₂
 = (f ≫ g).appLE U W (e₂.trans ((Op…
· 使用定理 `AlgebraicGeometry.IsAffineOpen.basicOpen`：basicOpen : IsAffineOpen (X.ba
sicOpen f)
· 使用定理 `RingHom.IsStandardSmoothOfRelativeDimension.comp`：∀ {n m : ℕ} {R : Type 
u} {S : Type v} [inst : CommRing R] [inst_1 : CommRing S] {T : Type u_1} [inst_2
 : CommRing T]   {g : S →+* T} {f : R …
· 使用定理 `AlgebraicGeometry.IsAffineOpen.isLocalization_basicOpen`：isLocalization_
basicOpen : IsLocalization.Away f Γ(X, X.basicOpen f)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If `f` is smooth of relative dimension `n` and `g` is smooth of relative dimensi
on
`m`, then `f ≫ g` is smooth of relative dimension `n + m`.
-/
instance smoothOfRelativeDimension_comp {Z : Scheme.{u}} (g : Y ⟶ Z)
    [hf : SmoothOfRelativeDimension n f] [hg : SmoothOfRelativeDimension m g] :
    SmoothOfRelativeDimension (n + m) (f ≫ g) where
  exists_isStandardSmoothOfRelativeDimension x := by
    obtain ⟨U₂, hU₂, V₂, hV₂, hfx₂, e₂, hf₂⟩ := hg.exists_isStandardSmoothOfRelativeDimension (f x)
    obtain ⟨U₁', hU₁', V₁', hV₁', hx₁', e₁', hf₁'⟩ :=
      hf.exists_isStandardSmoothOfRelativeDimension x
    obtain ⟨r, s, hx₁, e₁, hf₁⟩ := exists_basicOpen_le_appLE_of_appLE_of_isAffine
      (isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway n).right
      (isStandardSmoothOfRelativeDimension_localizationPreserves n).away
      x ⟨V₂, hV₂⟩ ⟨U₁', hU₁'⟩ ⟨V₁', hV₁'⟩ ⟨V₁', hV₁'⟩ hx₁' hx₁' e₁' hf₁' hfx₂
    have e : X.basicOpen s ≤ (f ≫ g) ⁻¹ᵁ U₂ :=
      le_trans e₁ <| f.preimage_mono <| le_trans (Y.basicOpen_le r) e₂
    have heq : (f ≫ g).appLE U₂ (X.basicOpen s) e = g.appLE U₂ V₂ e₂ ≫
        CommRingCat.ofHom (algebraMap Γ(Y, V₂) Γ(Y, Y.basicOpen r)) ≫
          f.appLE (Y.basicOpen r) (X.basicOpen s) e₁ := by
      rw [RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom,
        g.appLE_map_assoc, Scheme.Hom.appLE_comp_appLE]
    refine ⟨U₂, hU₂, X.basicOpen s, hV₁'.basicOpen s, hx₁, e, heq ▸ ?_⟩
    apply IsStandardSmoothOfRelativeDimension.comp ?_ hf₂
    have : IsLocalization.Away r Γ(Y, Y.basicOpen r) := hV₂.isLocalization_basicOpen r
    exact (isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway n).left
      _ r _ hf₁
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {Z : Scheme.{u}} (g : Y ⟶ Z) [SmoothOfRelativeDimension 0 f]
    [SmoothOfRelativeDimension 0 g] :
    SmoothOfRelativeDimension 0 (f ≫ g) :=
  inferInstanceAs <| SmoothOfRelativeDimension (0 + 0) (f ≫ g)

/-- Smooth of relative dimension `0` is multiplicative. -/
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Smooth of relative dimension `0` is multiplicative.
-/
instance : MorphismProperty.IsMultiplicative (@SmoothOfRelativeDimension 0) where
  id_mem _ := inferInstance
  comp_mem _ _ _ _ := inferInstance

/-- Smooth morphisms are locally of finite presentation. -/
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Smooth morphisms are locally of finite presentation.
-/
instance (priority := 100) [hf : Smooth f] : LocallyOfFinitePresentation f := by
  rw [HasRingHomProperty.eq_affineLocally @LocallyOfFinitePresentation]
  rw [HasRingHomProperty.eq_affineLocally @Smooth] at hf
  exact affineLocally_le (fun hf ↦ hf.finitePresentation) f hf
/-
**AlgebraicGeometry.formallySmooth_stalkMap_iff** 是 Mathlib 中的一个引理，位于命名空间 `Algeb
raicGeometry`。
形式化陈述：formallySmooth_stalkMap_iff {f : X ⟶ Y} {x : X} (U : Y.Opens) (hU : IsAffi
neOpen U) (V : X.Opens) (hV : IsAffineOpen V) (hVU : V <= f ⁻¹ᵁ U) (hx : x in V)
 : letI
参数：U : Y.Opens；hU : IsAffineOpen U；V : X.Opens；hV : IsAffineOpen V；hVU : V <= f 
⁻¹ᵁ U；hx : x in V。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.IsAffineOpen.comap_primeIdealOf_appLE`：comap_primeIdea
lOf_appLE {f : X ⟶ Y} {x : X} (U : Y.Opens) (hU : IsAffineOpen U) (V : X.Opens) 
(hV : IsAffineOpen V) (hVU : V <= f ⁻¹ᵁ U) (h…
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用引理 `RingHom.formallySmooth_algebraMap`：formallySmooth_algebraMap [Algebra R 
S] : (algebraMap R S).FormallySmooth ↔ Algebra.FormallySmooth R S
· 使用定理 `RingHom.RespectsIso.arrow_mk_iso_iff`：∀ {P : {R S : Type u} → [inst : Co
mmRing R] → [inst_1 : CommRing S] → (R →+* S) → Prop},   (RingHom.RespectsIso fu
n {R S} [CommRing R] [Comm…
· 使用定理 `RingHom.FormallySmooth.respectsIso`：RingHom.RespectsIso @RingHom.Formall
ySmooth
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Algebra.FormallySmooth.iff_restrictScalars`：∀ {R : Type u} {A : Type v} 
{B : Type u_1} [inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A] 
  [inst_3 : CommRing B] [inst_4 …
· 使用定理 `Localization.AtPrime.instIsScalarTowerOfIsLiesOverAlgebra`：∀ {R : Type u
_1} [inst : CommSemiring R] {A : Type u_4} {B : Type u_5} [inst_1 : CommSemiring
 A]   [inst_2 : CommSemiring B] [inst_3 : Algeb…
· 使用定理 `Localization.AtPrime.instIsLiesOverAlgebra`：∀ {A : Type u_4} {B : Type u
_5} [inst : CommSemiring A] [inst_1 : CommSemiring B] [inst_2 : Algebra A B] (p 
: Ideal A)   [inst_3 : p.IsPrime…
· 使用定理 `Algebra.FormallyEtale.instLocalization`：∀ {R : Type u_2} {S : Type u_3} 
[inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   [Algebra.Form
allyEtale R S] (M : Submonoi…
· 使用定理 `Algebra.Etale.formallyEtale`：∀ {R : Type u} {A : Type v} {inst : CommRin
g R} {inst_1 : CommRing A} {inst_2 : Algebra R A} [self : Algebra.Etale R A],   
Algebra.FormallyE…
· 使用定理 `Algebra.Etale.inst`：∀ {R : Type u} [inst : CommRing R], Algebra.Etale R 
R
-/
lemma formallySmooth_stalkMap_iff {f : X ⟶ Y} {x : X} (U : Y.Opens)
      (hU : IsAffineOpen U) (V : X.Opens) (hV : IsAffineOpen V) (hVU : V ≤ f ⁻¹ᵁ U)
      (hx : x ∈ V) :
    letI := (f.appLE U V hVU).hom.toAlgebra
    (f.stalkMap x).hom.FormallySmooth ↔
      hV.primeIdealOf ⟨x, hx⟩ ∈ Algebra.smoothLocus Γ(Y, U) Γ(X, V) := by
  let := (f.appLE U V hVU).hom.toAlgebra
  let p := (hU.primeIdealOf ⟨f x, hVU hx⟩).asIdeal
  let q := (hV.primeIdealOf ⟨x, hx⟩).asIdeal
  have : q.LiesOver p :=
    ⟨congr($(IsAffineOpen.comap_primeIdealOf_appLE U hU V hV hVU hx).1).symm⟩
  let := Localization.AtPrime.algebraOfLiesOver p q
  trans Algebra.FormallySmooth (Localization.AtPrime p) (Localization.AtPrime q)
  · rw [← formallySmooth_algebraMap]
    exact RingHom.FormallySmooth.respectsIso.arrow_mk_iso_iff
      (IsAffineOpen.arrowStalkMapIso f U hU V hV hVU hx)
  · exact Algebra.FormallySmooth.iff_restrictScalars.symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.exists_smooth_of_formallySmooth_stalk** 是 Mathlib 中的一个引理，位于命
名空间 `AlgebraicGeometry`。
形式化陈述：exists_smooth_of_formallySmooth_stalk (f : X ⟶ Y) [LocallyOfFinitePresenta
tion f] (x : X) (H : (f.stalkMap x).hom.FormallySmooth) : exists (U : Y.Opens) (
_ : IsAffineOpen U) (V : X.Opens) (_ : IsAffineOpen V) (hVU : V <= f ⁻¹ᵁ U), x i
n V ∧ (f.appLE U V hVU).hom.Smooth
参数：f : X ⟶ Y；x : X；H : (f.stalkMap x).hom.FormallySmooth。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.IsTopologicalBasis.exists_subset_of_mem_open`：∀ {α : Ty
pe u} [t : TopologicalSpace α] {b : Set (Set α)},   TopologicalSpace.IsTopologic
alBasis b → ∀ {a : α} {u : Set α}, a ∈ u → IsOpen u…
· 使用定理 `AlgebraicGeometry.Scheme.isBasis_affineOpens`：∀ (X : AlgebraicGeometry.S
cheme), TopologicalSpace.Opens.IsBasis X.affineOpens
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `isOpen_univ`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen Set.univ
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
· 使用定理 `AlgebraicGeometry.Scheme.Hom.continuous`：∀ {X Y : AlgebraicGeometry.Sche
me} (f : X ⟶ Y), Continuous ⇑f
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用定理 `AlgebraicGeometry.Scheme.Hom.finitePresentation_appLE`：∀ {X Y : Algebrai
cGeometry.Scheme} (f : X ⟶ Y) [self : AlgebraicGeometry.LocallyOfFinitePresentat
ion f] {U : Y.Opens},   AlgebraicGeometry.I…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `AlgebraicGeometry.formallySmooth_stalkMap_iff`：formallySmooth_stalkMap_i
ff {f : X ⟶ Y} {x : X} (U : Y.Opens) (hU : IsAffineOpen U) (V : X.Opens) (hV : I
sAffineOpen V) (hVU : V <= f ⁻¹ᵁ U)…
· 使用定理 `Algebra.IsSmoothAt.exists_notMem_smooth`：∀ (R : Type u_1) {A : Type u_2}
 [inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A]   [Algebra.Fin
itePresentation R A] (p : Ide…
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `AlgebraicGeometry.IsAffineOpen.basicOpen`：basicOpen : IsAffineOpen (X.ba
sicOpen f)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `AlgebraicGeometry.Scheme.basicOpen_le`：basicOpen_le : X.basicOpen f <= U
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.IsAffineOpen.toSpecΓ_fromSpec`：toSpecΓ_fromSpec : U.to
SpecΓ ≫ hU.fromSpec = U.ι
· 使用引理 `AlgebraicGeometry.IsAffineOpen.isoSpec_hom`：isoSpec_hom : hU.isoSpec.hom
 = U.toSpecΓ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.Scheme.Hom.comp_apply`：comp_apply {X Y Z : Scheme} (f 
: X ⟶ Y) (g : Y ⟶ Z) (x : X) : (f ≫ g) x = g (f x)
· 使用引理 `AlgebraicGeometry.Scheme.Hom.mem_preimage`：mem_preimage {x : X} {U : Ope
ns Y} : x in f ⁻¹ᵁ U ↔ f x in U
· 使用定理 `AlgebraicGeometry.IsAffineOpen.fromSpec_preimage_basicOpen`：fromSpec_pre
image_basicOpen : hU.fromSpec ⁻¹ᵁ X.basicOpen f = PrimeSpectrum.basicOpen f
· 使用定理 `AlgebraicGeometry.IsAffineOpen.primeIdealOf.eq_1`：∀ {X : AlgebraicGeomet
ry.Scheme} {U : X.Opens} (hU : AlgebraicGeometry.IsAffineOpen U) (x : ↥U),   hU.
primeIdealOf x = hU.isoSpec.hom x
· 使用定理 `PrimeSpectrum.mem_basicOpen`：mem_basicOpen (f : R) (x : PrimeSpectrum R)
 : x in basicOpen f ↔ f ∉ x.asIdeal
· 使用定理 `AlgebraicGeometry.IsAffineOpen.isLocalization_basicOpen`：isLocalization_
basicOpen : IsLocalization.Away f Γ(X, X.basicOpen f)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsScalarTower.algebraMap_apply`：algebraMap_apply (x : R) : algebraMap R 
A x = algebraMap S A (algebraMap R S x)
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
（共 41 条，此处仅展示前 30 条）
-/
lemma exists_smooth_of_formallySmooth_stalk
    (f : X ⟶ Y) [LocallyOfFinitePresentation f]
    (x : X) (H : (f.stalkMap x).hom.FormallySmooth) :
    ∃ (U : Y.Opens) (_ : IsAffineOpen U) (V : X.Opens) (_ : IsAffineOpen V) (hVU : V ≤ f ⁻¹ᵁ U),
      x ∈ V ∧ (f.appLE U V hVU).hom.Smooth := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxU (U.2.preimage f.continuous)
  have := f.finitePresentation_appLE hU hV hVU
  algebraize [(f.appLE U V hVU).hom]
  have : Algebra.IsSmoothAt _ _ := (formallySmooth_stalkMap_iff U hU V hV hVU hxV).mp H
  obtain ⟨r, hrx, hr⟩ := Algebra.IsSmoothAt.exists_notMem_smooth Γ(Y, U)
    (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
  refine ⟨_, hU, _, hV.basicOpen r, (X.basicOpen_le r).trans hVU, ?_, ?_⟩
  · rwa [← PrimeSpectrum.mem_basicOpen, IsAffineOpen.primeIdealOf,
      ← hV.fromSpec_preimage_basicOpen, Scheme.Hom.mem_preimage, ← Scheme.Hom.comp_apply,
      IsAffineOpen.isoSpec_hom, IsAffineOpen.toSpecΓ_fromSpec] at hrx
  · have := hV.isLocalization_basicOpen r
    rw [← RingHom.smooth_algebraMap] at hr
    convert!
      RingHom.Smooth.propertyIsLocal.respectsIso.1 _
        (IsLocalization.algEquiv (.powers r) _ Γ(X, X.basicOpen r)).toRingEquiv hr
    ext
    dsimp
    simp only [IsScalarTower.algebraMap_apply Γ(Y, U) Γ(X, V) (Localization _),
      IsLocalization.map_eq]
    simp only [algebraMap_toAlgebra, RingHomCompTriple.comp_apply, ← ConcreteCategory.comp_apply,
      Scheme.Hom.appLE_map]
/-
**AlgebraicGeometry.Scheme.Hom.isOpen_smoothLocus** 是 Mathlib 中的一个定理，位于命名空间 `Alg
ebraicGeometry.Scheme.Hom`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.LocallyO
fFinitePresentation f],   IsOpen {x | (CommRingCat.Hom.hom (AlgebraicGeometry.Sc
heme.Hom.stalkMap f x)).FormallySmooth}
参数：f : X ⟶ Y；CommRingCat.Hom.hom (AlgebraicGeometry.Scheme.Hom.stalkMap f x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isOpen_iff_forall_mem_open`：isOpen_iff_forall_mem_open : IsOpen s ↔ fora
ll x in s, exists t, t subseteq s ∧ IsOpen t ∧ x in t
· 使用引理 `AlgebraicGeometry.exists_smooth_of_formallySmooth_stalk`：exists_smooth_o
f_formallySmooth_stalk (f : X ⟶ Y) [LocallyOfFinitePresentation f] (x : X) (H : 
(f.stalkMap x).hom.FormallySmooth) : exists (…
· 使用引理 `AlgebraicGeometry.formallySmooth_stalkMap_iff`：formallySmooth_stalkMap_i
ff {f : X ⟶ Y} {x : X} (U : Y.Opens) (hU : IsAffineOpen U) (V : X.Opens) (hV : I
sAffineOpen V) (hVU : V <= f ⁻¹ᵁ U)…
· 使用定理 `Algebra.FormallySmooth.instLocalization`：∀ {R : Type u_4} {A : Type u_5}
 [inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A]   [Algebra.For
mallySmooth R A] (M : Submono…
· 使用定理 `Algebra.Smooth.formallySmooth`：∀ {R : Type u_4} {inst : CommRing R} {A :
 Type u} {inst_1 : CommRing A} {inst_2 : Algebra R A}   [self : Algebra.Smooth R
 A], Algebra.Formal…
· 使用定理 `RingHom.Smooth.toAlgebra`：∀ {R : Type u_1} {S : Type u_2} [inst : CommRi
ng R] [inst_1 : CommRing S] {f : R →+* S}, f.Smooth → Algebra.Smooth R S
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
-/
lemma Scheme.Hom.isOpen_smoothLocus [LocallyOfFinitePresentation f] :
    IsOpen { x | (f.stalkMap x).hom.FormallySmooth } := by
  refine isOpen_iff_forall_mem_open.mpr fun x hx ↦ ?_
  obtain ⟨U, hU, V, hV, hVU, hxV, H⟩ := exists_smooth_of_formallySmooth_stalk f x hx
  algebraize [(f.appLE U V hVU).hom]
  exact ⟨V, fun y hy ↦ (formallySmooth_stalkMap_iff U hU V hV hVU hy).mpr
    (inferInstanceAs (Algebra.IsSmoothAt _ _)), V.2, hxV⟩

/-- The set of points smooth over a base, as a `Scheme.Opens`. -/
/-
**AlgebraicGeometry.Scheme.Hom.smoothLocus** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicG
eometry.Scheme.Hom`。
形式化陈述：{X Y : AlgebraicGeometry.Scheme} → (f : X ⟶ Y) → [AlgebraicGeometry.Locall
yOfFinitePresentation f] → X.Opens
参数：f : X ⟶ Y。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Hom.isOpen_smoothLocus`：∀ {X Y : AlgebraicGeome
try.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.LocallyOfFinitePresentation f],   IsO
pen {x | (CommRingCat.Hom.hom (Algebr…

--- 原说明 ---
The set of points smooth over a base, as a `Scheme.Opens`.
-/
def Scheme.Hom.smoothLocus (f : X ⟶ Y) [LocallyOfFinitePresentation f] : X.Opens :=
  ⟨{ x | (f.stalkMap x).hom.FormallySmooth }, f.isOpen_smoothLocus⟩
/-
**AlgebraicGeometry.Scheme.Hom.mem_smoothLocus** 是 Mathlib 中的一个定理，位于命名空间 `Algebr
aicGeometry.Scheme.Hom`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} {f : X ⟶ Y} [inst : AlgebraicGeometry.L
ocallyOfFinitePresentation f] {x : ↥X},   x ∈ AlgebraicGeometry.Scheme.Hom.smoot
hLocus f ↔     (CommRingCat.Hom.hom (AlgebraicGeometry.Scheme.Hom.stalkMap f x))
.FormallySmooth
参数：CommRingCat.Hom.hom (AlgebraicGeometry.Scheme.Hom.stalkMap f x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma Scheme.Hom.mem_smoothLocus {f : X ⟶ Y} [LocallyOfFinitePresentation f] {x : X} :
    x ∈ f.smoothLocus ↔ (f.stalkMap x).hom.FormallySmooth := .rfl
/-
**AlgebraicGeometry.Scheme.Hom.smoothLocus_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `Alg
ebraicGeometry.Scheme.Hom`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [inst : AlgebraicGeometry.S
mooth f],   AlgebraicGeometry.Scheme.Hom.smoothLocus f = ⊤
参数：f : X ⟶ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.instLocallyOfFinitePresentationOfSmooth`：∀ {X Y : Alge
braicGeometry.Scheme} (f : X ⟶ Y) [hf : AlgebraicGeometry.Smooth f],   Algebraic
Geometry.LocallyOfFinitePresentation f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `top_le_iff`：top_le_iff : ⊤ <= a ↔ a = ⊤
· 使用定理 `TopologicalSpace.IsTopologicalBasis.exists_subset_of_mem_open`：∀ {α : Ty
pe u} [t : TopologicalSpace α] {b : Set (Set α)},   TopologicalSpace.IsTopologic
alBasis b → ∀ {a : α} {u : Set α}, a ∈ u → IsOpen u…
· 使用定理 `AlgebraicGeometry.Scheme.isBasis_affineOpens`：∀ (X : AlgebraicGeometry.S
cheme), TopologicalSpace.Opens.IsBasis X.affineOpens
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `isOpen_univ`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen Set.univ
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
· 使用定理 `AlgebraicGeometry.Scheme.Hom.continuous`：∀ {X Y : AlgebraicGeometry.Sche
me} (f : X ⟶ Y), Continuous ⇑f
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用定理 `AlgebraicGeometry.Scheme.Hom.smooth_appLE`：∀ {X Y : AlgebraicGeometry.Sc
heme} (f : X ⟶ Y) [self : AlgebraicGeometry.Smooth f] {U : Y.Opens},   Algebraic
Geometry.IsAffineOpen U →     ∀…
· 使用定理 `AlgebraicGeometry.Scheme.Hom.mem_smoothLocus`：∀ {X Y : AlgebraicGeometry
.Scheme} {f : X ⟶ Y} [inst : AlgebraicGeometry.LocallyOfFinitePresentation f] {x
 : ↥X},   x ∈ AlgebraicGeometry.Sc…
· 使用引理 `AlgebraicGeometry.formallySmooth_stalkMap_iff`：formallySmooth_stalkMap_i
ff {f : X ⟶ Y} {x : X} (U : Y.Opens) (hU : IsAffineOpen U) (V : X.Opens) (hV : I
sAffineOpen V) (hVU : V <= f ⁻¹ᵁ U)…
· 使用定理 `Algebra.FormallySmooth.instLocalization`：∀ {R : Type u_4} {A : Type u_5}
 [inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A]   [Algebra.For
mallySmooth R A] (M : Submono…
· 使用定理 `Algebra.Smooth.formallySmooth`：∀ {R : Type u_4} {inst : CommRing R} {A :
 Type u} {inst_1 : CommRing A} {inst_2 : Algebra R A}   [self : Algebra.Smooth R
 A], Algebra.Formal…
· 使用定理 `RingHom.Smooth.toAlgebra`：∀ {R : Type u_1} {S : Type u_2} [inst : CommRi
ng R] [inst_1 : CommRing S] {f : R →+* S}, f.Smooth → Algebra.Smooth R S
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
-/
lemma Scheme.Hom.smoothLocus_eq_top (f : X ⟶ Y) [Smooth f] :
    f.smoothLocus = ⊤ := by
  rw [← top_le_iff]
  rintro x -
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxU (U.2.preimage f.continuous)
  have := f.smooth_appLE hU hV hVU
  algebraize [(f.appLE U V hVU).hom]
  rw [Scheme.Hom.mem_smoothLocus, formallySmooth_stalkMap_iff U hU V hV hVU hxV]
  exact inferInstanceAs (Algebra.IsSmoothAt _ _)

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.Scheme.Hom.smoothLocus_eq_top_iff** 是 Mathlib 中的一个定理，位于命名空间 
`AlgebraicGeometry.Scheme.Hom`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} {f : X ⟶ Y} [inst : AlgebraicGeometry.L
ocallyOfFinitePresentation f],   AlgebraicGeometry.Scheme.Hom.smoothLocus f = ⊤ 
↔ AlgebraicGeometry.Smooth f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `AlgebraicGeometry.IsZariskiLocalAtSource.iff_exists_resLE`：iff_exists_re
sLE [IsZariskiLocalAtTarget P] [P.RespectsRight @IsOpenImmersion] : P f ↔ forall
 x : X, exists (U : Y.Opens) (V : X.Opens) (_ :…
· 使用定理 `AlgebraicGeometry.HasRingHomProperty.instIsZariskiLocalAtSource`：∀ {P : 
CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme}   {Q : {R S : Type u} 
→ [inst : CommRing R] → [inst_1 : CommRing S] → (R →+…
· 使用定理 `AlgebraicGeometry.instHasRingHomPropertySmoothSmooth`：AlgebraicGeometry.
HasRingHomProperty @AlgebraicGeometry.Smooth fun {R S} [CommRing R] [CommRing S]
 => RingHom.Smooth
· 使用定理 `AlgebraicGeometry.HasRingHomProperty.instIsZariskiLocalAtTarget`：∀ (P : 
CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme)   {Q : {R S : Type u} 
→ [inst : CommRing R] → [inst_1 : CommRing S] → (R →+…
· 使用定理 `CategoryTheory.MorphismProperty.Respects.toRespectsRight`：∀ {C : Type u}
 {inst : CategoryTheory.CategoryStruct.{v, u} C} {P Q : CategoryTheory.MorphismP
roperty C}   [self : P.Respects Q], P.Respects…
· 使用定理 `AlgebraicGeometry.instRespectsSchemeSmoothIsOpenImmersion`：CategoryTheor
y.MorphismProperty.Respects (@AlgebraicGeometry.Smooth) AlgebraicGeometry.IsOpen
Immersion
· 使用引理 `AlgebraicGeometry.exists_smooth_of_formallySmooth_stalk`：exists_smooth_o
f_formallySmooth_stalk (f : X ⟶ Y) [LocallyOfFinitePresentation f] (x : X) (H : 
(f.stalkMap x).hom.FormallySmooth) : exists (…
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.HasRingHomProperty.iff_of_isAffine`：iff_of_isAffine [I
sAffine X] [IsAffine Y] : P f ↔ Q (f.appTop).hom
· 使用定理 `RingHom.RespectsIso.arrow_mk_iso_iff`：∀ {P : {R S : Type u} → [inst : Co
mmRing R] → [inst_1 : CommRing S] → (R →+* S) → Prop},   (RingHom.RespectsIso fu
n {R S} [CommRing R] [Comm…
· 使用定理 `RingHom.PropertyIsLocal.respectsIso`：RingHom.PropertyIsLocal.respectsIso
 (hP : RingHom.PropertyIsLocal @P) : RingHom.RespectsIso @P
· 使用引理 `RingHom.Smooth.propertyIsLocal`：propertyIsLocal : PropertyIsLocal Smooth
 where localizationAwayPreserves
· 使用定理 `AlgebraicGeometry.Scheme.Hom.smoothLocus_eq_top`：∀ {X Y : AlgebraicGeome
try.Scheme} (f : X ⟶ Y) [inst : AlgebraicGeometry.Smooth f],   AlgebraicGeometry
.Scheme.Hom.smoothLocus f = ⊤
-/
lemma Scheme.Hom.smoothLocus_eq_top_iff {f : X ⟶ Y} [LocallyOfFinitePresentation f] :
    f.smoothLocus = ⊤ ↔ Smooth f := by
  refine ⟨fun H ↦ ?_, fun _ ↦ f.smoothLocus_eq_top⟩
  refine IsZariskiLocalAtSource.iff_exists_resLE.mpr fun x ↦ ?_
  obtain ⟨U, hU, V, hV, hVU, hxV, H⟩ :=
    exists_smooth_of_formallySmooth_stalk f _ (H.ge (Set.mem_univ x))
  refine ⟨U, V, hxV, hVU, ?_⟩
  have : IsAffine _ := hU
  have : IsAffine _ := hV
  rw [HasRingHomProperty.iff_of_isAffine (P := @Smooth)]
  exact (RingHom.Smooth.propertyIsLocal.respectsIso.arrow_mk_iso_iff
    (arrowResLEAppIso f U V hVU)).mpr H
/-
**AlgebraicGeometry.Scheme.Hom.preimage_smoothLocus_eq** 是 Mathlib 中的一个定理，位于命名空间
 `AlgebraicGeometry.Scheme.Hom`。
形式化陈述：∀ {X Y U : AlgebraicGeometry.Scheme} (f : U ⟶ X) (g : X ⟶ Y) [inst : Algeb
raicGeometry.IsOpenImmersion f]   [inst_1 : AlgebraicGeometry.LocallyOfFinitePre
sentation g],   (TopologicalSpace.Opens.map f.base).obj (AlgebraicGeometry.Schem
e.Hom.smoothLocus g) =     AlgebraicGeometry.Scheme.Hom.smoothLocus (CategoryThe
ory.CategoryStruct.comp f g)
参数：f : U ⟶ X；g : X ⟶ Y；TopologicalSpace.Opens.map f.base；AlgebraicGeometry.Schem
e.Hom.smoothLocus g；CategoryTheory.CategoryStruct.comp f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.Opens.ext`：ext {U V : Opens α} (h : (U : Set α) = V) : 
U = V
· 使用定理 `AlgebraicGeometry.locallyOfFinitePresentation_of_isOpenImmersion`：∀ {X Y
 : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.IsOpenImmersion f], 
  AlgebraicGeometry.LocallyOfFinitePresentation f
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `RingHom.RespectsIso.cancel_right_isIso`：∀ {P : {R S : Type u} → [inst : 
CommRing R] → [inst_1 : CommRing S] → (R →+* S) → Prop},   RingHom.RespectsIso P
 →     ∀ {R S T : CommRingCa…
· 使用定理 `RingHom.FormallySmooth.respectsIso`：RingHom.RespectsIso @RingHom.Formall
ySmooth
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.instIsIsoCommRingCatStalkMap`：∀ {X Y :
 AlgebraicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.IsOpenImmersion f] (x 
: ↥X),   CategoryTheory.IsIso (AlgebraicGeometry.Sch…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CommRingCat.hom_comp`：hom_comp {R S T : CommRingCat} (f : R ⟶ S) (g : S 
⟶ T) : (f ≫ g).hom = g.hom.comp f.hom
· 使用引理 `AlgebraicGeometry.Scheme.Hom.stalkMap_comp`：stalkMap_comp {X Y Z : Schem
e.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) : (f ≫ g : X ⟶ Z).stalkMap x = g.stalkMap
 (f x) ≫ f.stalkMap x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma Scheme.Hom.preimage_smoothLocus_eq {U : Scheme.{u}}
    (f : U ⟶ X) (g : X ⟶ Y) [IsOpenImmersion f] [LocallyOfFinitePresentation g] :
    f ⁻¹ᵁ g.smoothLocus = (f ≫ g).smoothLocus := by
  ext x
  refine (RingHom.FormallySmooth.respectsIso.cancel_right_isIso _ (f.stalkMap x)).symm.trans ?_
  rw [← CommRingCat.hom_comp, ← stalkMap_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.Scheme.Hom.genericPoint_mem_smoothLocus_of_perfectField** 是 
Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.Scheme.Hom`。
形式化陈述：∀ {X : AlgebraicGeometry.Scheme} {K : Type u} [inst : Field K] [PerfectFie
ld K]   [inst_2 : AlgebraicGeometry.IsIntegral X] (f : X ⟶ AlgebraicGeometry.Spe
c (CommRingCat.of K))   [inst_3 : AlgebraicGeometry.LocallyOfFinitePresentation 
f],   genericPoint ↥X ∈ AlgebraicGeometry.Scheme.Hom.smoothLocus f
参数：f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of K)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.instQuasiSoberCarrierCarrierCommRingCat`：∀ (X : Algebr
aicGeometry.Scheme), QuasiSober ↥X
· 使用定理 `AlgebraicGeometry.LocallyOfFiniteType.stalkMap`：∀ {X Y : AlgebraicGeomet
ry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.LocallyOfFiniteType f] (x : ↥X),   (Co
mmRingCat.Hom.hom (AlgebraicGeometry…
· 使用定理 `AlgebraicGeometry.instLocallyOfFiniteTypeOfLocallyOfFinitePresentation`：
∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [hf : AlgebraicGeometry.LocallyOf
FinitePresentation f],   AlgebraicGeometry.LocallyOfFiniteTy…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.Hom.mem_smoothLocus`：∀ {X Y : AlgebraicGeometry
.Scheme} {f : X ⟶ Y} [inst : AlgebraicGeometry.LocallyOfFinitePresentation f] {x
 : ↥X},   x ∈ AlgebraicGeometry.Sc…
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `AlgebraicGeometry.StructureSheaf.IsLocalization.to_stalk`：∀ (R : Type u)
 [inst : CommRing R] (p : PrimeSpectrum R),   IsLocalization.AtPrime (↑((Algebra
icGeometry.Spec.structureSheaf R).presheaf.sta…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.IsAlgebraic.of_injective`：Algebra.IsAlgebraic.of_injective (f : 
A ->ₐ[R] B) (hf : Function.Injective f) [Algebra.IsAlgebraic R B] : Algebra.IsAl
gebraic R A
· 使用定理 `AlgEquiv.injective`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [ins
t : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Al
gebra R …
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `MulEquiv.isField`：∀ {A : Type u_1} {B : Type u_2} [inst : Semiring A] [i
nst_1 : Semiring B], IsField B → ∀ (e : A ≃* B), IsField A
· 使用定理 `Field.toIsField`：Field.toIsField (R : Type u) [Field R] : IsField R
· 使用定理 `Algebra.IsAlgebraic.perfectField`：Algebra.IsAlgebraic.perfectField (K : 
Type*) {L : Type*} [Field K] [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] [
PerfectField K] : Perf…
· 使用定理 `Algebra.FormallySmooth.of_perfectField`：∀ {K : Type u_1} {L : Type u_2} 
[inst : Field L] [inst_1 : Field K] [inst_2 : Algebra K L] [PerfectField K]   [A
lgebra.EssFiniteType K L], A…
-/
lemma Scheme.Hom.genericPoint_mem_smoothLocus_of_perfectField
    {K : Type u} [Field K] [PerfectField K] [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [LocallyOfFinitePresentation f] : genericPoint X ∈ f.smoothLocus := by
  have := LocallyOfFiniteType.stalkMap f (genericPoint X)
  rw [Scheme.Hom.mem_smoothLocus]
  algebraize [(f.stalkMap (genericPoint X)).hom]
  let K' := (Spec.structureSheaf K).presheaf.stalk (f (genericPoint X))
  let e : K ≃ₐ[K] K' := IsLocalization.atUnits _ (f (genericPoint X)).asIdeal.primeCompl
      (fun x hx ↦ by aesop (add simp IsUnit.mem_submonoid_iff))
  have : Algebra.IsAlgebraic K K' :=
    .of_injective e.symm.toAlgHom e.symm.injective
  let : Field K' := (e.toRingEquiv.symm.isField (Field.toIsField K)).toField
  let : Field ((Spec (.of K)).presheaf.stalk (f (genericPoint X))) := this
  have : PerfectField ((Spec (.of K)).presheaf.stalk (f (genericPoint X))) :=
    Algebra.IsAlgebraic.perfectField (K := K)
      (L := (Spec.structureSheaf K).presheaf.stalk (f (genericPoint X)))
  exact Algebra.FormallySmooth.of_perfectField

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.Scheme.Hom.dense_smoothLocus_of_perfectField** 是 Mathlib 中的一
个定理，位于命名空间 `AlgebraicGeometry.Scheme.Hom`。
形式化陈述：∀ {X : AlgebraicGeometry.Scheme} {K : Type u} [inst : Field K] [PerfectFie
ld K] [AlgebraicGeometry.IsReduced X]   (f : X ⟶ AlgebraicGeometry.Spec (CommRin
gCat.of K)) [inst_3 : AlgebraicGeometry.LocallyOfFinitePresentation f],   Dense 
↑(AlgebraicGeometry.Scheme.Hom.smoothLocus f)
参数：f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of K)；AlgebraicGeometry.Scheme.Ho
m.smoothLocus f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian`：∀ {X Y : Alge
braicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.LocallyOfFiniteType f]   [A
lgebraicGeometry.IsLocallyNoetherian Y], Algebr…
· 使用定理 `AlgebraicGeometry.instLocallyOfFiniteTypeOfLocallyOfFinitePresentation`：
∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [hf : AlgebraicGeometry.LocallyOf
FinitePresentation f],   AlgebraicGeometry.LocallyOfFiniteTy…
· 使用定理 `AlgebraicGeometry.instIsLocallyNoetherianSpecOfIsNoetherianRingCarrier`：
∀ {R : CommRingCat} [IsNoetherianRing ↑R], AlgebraicGeometry.IsLocallyNoetherian
 (AlgebraicGeometry.Spec R)
· 使用定理 `IsSimpleModule.instIsNoetherian`：∀ (R : Type u_2) [inst : Ring R] {M : T
ype u_4} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimpleModul
e R M], IsNoetherian …
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dense_iff_closure_eq`：dense_iff_closure_eq : Dense s ↔ closure s = univ
· 使用定理 `Set.eq_univ_iff_forall`：eq_univ_iff_forall {s : Set α} : s = univ ↔ fora
ll x, x in s
· 使用定理 `Set.sUnion_eq_biUnion`：sUnion_eq_biUnion {s : Set (Set α)} : ⋃₀ s = ⋃ (i
 : Set α) (_ : i in s), i
· 使用定理 `isOpen_compl_iff`：∀ {X : Type u} {s : Set X} [inst : TopologicalSpace X]
, IsOpen sᶜ ↔ IsClosed s
· 使用定理 `Set.Finite.isClosed_biUnion`：Set.Finite.isClosed_biUnion {s : Set α} {f 
: α -> Set X} (hs : s.Finite) (h : forall i in s, IsClosed (f i)) : IsClosed (⋃ 
i in s, f i)
· 使用定理 `Set.Finite.sdiff`：∀ {α : Type u} {s t : Set α}, s.Finite → (s \ t).Finit
e
· 使用定理 `TopologicalSpace.NoetherianSpace.finite_irreducibleComponents`：∀ {α : Ty
pe u_1} [inst : TopologicalSpace α] [TopologicalSpace.NoetherianSpace α], (irred
ucibleComponents α).Finite
· 使用定理 `AlgebraicGeometry.IsNoetherian.noetherianSpace`：∀ {X : AlgebraicGeometry
.Scheme} [AlgebraicGeometry.IsNoetherian X], TopologicalSpace.NoetherianSpace ↥X
· 使用定理 `isClosed_of_mem_irreducibleComponents`：isClosed_of_mem_irreducibleCompon
ents (s) (H : s in irreducibleComponents X) : IsClosed s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `closure_sUnion_irreducibleComponents_sdiff_singleton`：closure_sUnion_irr
educibleComponents_sdiff_singleton (hX : (irreducibleComponents X).Finite) (Z : 
Set X) (hZ : Z in irreducibleComponents X)…
· 使用定理 `irreducibleComponent_mem_irreducibleComponents`：irreducibleComponent_mem
_irreducibleComponents (x : X) : irreducibleComponent x in irreducibleComponents
 X
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isIrreducible_iff_irreducibleSpace`：isIrreducible_iff_irreducibleSpace :
 IsIrreducible s ↔ IrreducibleSpace s
· 使用定理 `isIrreducible_iff_closure`：isIrreducible_iff_closure : IsIrreducible (cl
osure s) ↔ IsIrreducible s
· 使用定理 `isIrreducible_irreducibleComponent`：isIrreducible_irreducibleComponent {
x : X} : IsIrreducible (irreducibleComponent x)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.isIntegral_of_irreducibleSpace_of_isReduced`：isIntegra
l_of_irreducibleSpace_of_isReduced [IsReduced X] [H : IrreducibleSpace X] : IsIn
tegral X
· 使用定理 `AlgebraicGeometry.instIsReducedToScheme`：∀ {X : AlgebraicGeometry.Scheme
} {U : X.Opens} [AlgebraicGeometry.IsReduced X], AlgebraicGeometry.IsReduced ↑U
· 使用定理 `AlgebraicGeometry.instQuasiSoberCarrierCarrierCommRingCat`：∀ (X : Algebr
aicGeometry.Scheme), QuasiSober ↥X
· 使用定理 `AlgebraicGeometry.locallyOfFinitePresentation_of_isOpenImmersion`：∀ {X Y
 : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.IsOpenImmersion f], 
  AlgebraicGeometry.LocallyOfFinitePresentation f
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι`：∀ {X : AlgebraicGeo
metry.Scheme} (U : X.Opens), AlgebraicGeometry.IsOpenImmersion U.ι
· 使用定理 `AlgebraicGeometry.Scheme.Hom.genericPoint_mem_smoothLocus_of_perfectFiel
d`：∀ {X : AlgebraicGeometry.Scheme} {K : Type u} [inst : Field K] [PerfectField 
K]   [inst_2 : AlgebraicGeometry.IsIntegral X] (f : X ⟶ Algebra…
（共 54 条，此处仅展示前 30 条）
-/
lemma Scheme.Hom.dense_smoothLocus_of_perfectField
    {K : Type u} [Field K] [PerfectField K] [IsReduced X]
    (f : X ⟶ Spec (.of K)) [LocallyOfFinitePresentation f] : Dense (f.smoothLocus : Set X) := by
  wlog H : CompactSpace X generalizing X
  · rw [dense_iff_closure_eq, Set.eq_univ_iff_forall]
    intro x
    obtain ⟨_, ⟨U : X.Opens, hU, rfl⟩, hxU, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    have := this (U.ι ≫ f) (isCompact_iff_compactSpace.mp hU.isCompact) ⟨x, hxU⟩
    rwa [← preimage_smoothLocus_eq, Scheme.Hom.coe_preimage,
      ← U.ι.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage U.ι.continuous,
      Set.mem_preimage, U.ι_apply] at this
  have : IsNoetherian X := { __ := LocallyOfFiniteType.isLocallyNoetherian f }
  rw [dense_iff_closure_eq, Set.eq_univ_iff_forall]
  intro x
  let U : X.Opens :=
    ⟨(⋃₀ (irreducibleComponents X \ {irreducibleComponent x}))ᶜ, by
      rw [Set.sUnion_eq_biUnion, isOpen_compl_iff]
      exact TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.sdiff.isClosed_biUnion
        fun W hW ↦ isClosed_of_mem_irreducibleComponents W hW.1⟩
  have hU : closure U = irreducibleComponent x :=
    closure_sUnion_irreducibleComponents_sdiff_singleton
      TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
      _ (irreducibleComponent_mem_irreducibleComponents x)
  have : AlgebraicGeometry.IsIntegral U :=
    have : IrreducibleSpace U := isIrreducible_iff_irreducibleSpace.mp
      (isIrreducible_iff_closure.mp (hU ▸ isIrreducible_irreducibleComponent))
    isIntegral_of_irreducibleSpace_of_isReduced _
  have : U.ι (genericPoint U) ∈ f.smoothLocus := by
    have := (U.ι ≫ f).genericPoint_mem_smoothLocus_of_perfectField
    rwa [← preimage_smoothLocus_eq, Scheme.Hom.mem_preimage] at this
  exact (((genericPoint_spec U).image U.ι.continuous).specializes (y := x)
    (by rw [Set.image_univ, U.range_ι, hU]; exact mem_irreducibleComponent)).mem_closed
    isClosed_closure (subset_closure this)

end AlgebraicGeometry

