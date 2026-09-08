/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten, Andrew Yang
-/
module

public import Mathlib.CategoryTheory.Sites.Hypercover.Zero
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Equalizer
public import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# Locality conditions on morphism properties

In this file we define locality conditions on morphism properties in a category. Let `K` be a
precoverage in a category `C` and `P` be a morphism property on `C` that respects isomorphisms.

We say that

- `P` is local at the target if for every `f : X ⟶ Y`, `P` holds for `f` if and only if it holds
  for the restrictions of `f` to `Uᵢ` for a
  `K`-cover `{Uᵢ}` of `Y`.
- `P` is local at the source if for every `f : X ⟶ Y`, `P` holds for `f` if and only if it holds
  for the restrictions of `f` to `Uᵢ` for a `K`-cover `{Uᵢ}` of `X`.

## TODOs

- Define source and target local closure of a morphism property.
-/

public section

universe w v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C]

namespace MorphismProperty

variable (K : Precoverage C)

/--
A property of morphisms `P` in `C` is local at the target with respect to the precoverage `K` if
it respects isomorphisms, and:
`P` holds for `f : X ⟶ Y` if and only if it holds for the restrictions of `f` to `Uᵢ` for a
`0`-hypercover `{Uᵢ}` of `Y` in the precoverage `K`.
-/
/-
**CategoryTheory.MorphismProperty.IsLocalAtTarget** 是 Mathlib 中的一个归纳类型，位于命名空间 `C
ategoryTheory.MorphismProperty`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] → CategoryTheor
y.MorphismProperty C → CategoryTheory.Precoverage C → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A property of morphisms `P` in `C` is local at the target with respect to the pr
ecoverage `K` if
it respects isomorphisms, and:
`P` holds for `f : X ⟶ Y` if and only if it holds for the restrictions of `f` to
 `Uᵢ` for a
`0`-hypercover `{Uᵢ}` of `Y` in the precoverage `K`.
-/
class IsLocalAtTarget (P : MorphismProperty C) (K : Precoverage C) extends RespectsIso P where
  /-- If `P` holds for `f : X ⟶ Y`, it also holds for `f` restricted to `Uᵢ` for any
  `K`-cover `R` of `Y`. -/
  pullbackSnd {X Y : C} {f : Y ⟶ X} {R : Presieve X} {U : C} {g : U ⟶ X} (hR : R ∈ K X)
    (hg : R g) (hf : P f) [HasPullback f g] :
    P (pullback.snd f g)
  /-- If `P` holds for `f` restricted to `Uᵢ` for all `i`, it also holds for `f : X ⟶ Y` for any
  `K`-cover `R` of `Y`. -/
  of_forall_pullbackSnd {X Y : C} {f : Y ⟶ X} {R : Presieve X} (hR : R ∈ K X)
    (h : ∀ {U : C} {g : U ⟶ X} [HasPullback f g], R g → P (pullback.snd f g)) :
    P f

namespace IsLocalAtTarget

variable {P : MorphismProperty C} {K L : Precoverage C}

/-
**CategoryTheory.MorphismProperty.IsLocalAtTarget.mk_of_iff** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.MorphismProperty.IsLocalAtTarget`。
形式化陈述：mk_of_iff [P.RespectsIso] (H : forall ⦃X Y : C⦄ ⦃f : X ⟶ Y⦄ ⦃R : Presieve 
Y⦄, R in K Y -> (P f ↔ forall {U : C} (g : U ⟶ Y) [HasPullback f g], R g -> P (p
ullback.snd f g))) : P.IsLocalAtTarget K where pullbackSnd
参数：H : forall ⦃X Y : C⦄ ⦃f : X ⟶ Y⦄ ⦃R : Presieve Y⦄, R in K Y -> (P f ↔ forall 
{U : C} (g : U ⟶ Y) [HasPullback f g], R g -> P (pullback.snd f g))。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mk_of_iff [P.RespectsIso]
    (H : ∀ ⦃X Y : C⦄ ⦃f : X ⟶ Y⦄ ⦃R : Presieve Y⦄, R ∈ K Y →
      (P f ↔ ∀ {U : C} (g : U ⟶ Y) [HasPullback f g], R g → P (pullback.snd f g))) :
    P.IsLocalAtTarget K where
  pullbackSnd := by grind
  of_forall_pullbackSnd := by grind
/-
**CategoryTheory.MorphismProperty.IsLocalAtTarget.iff_of_forall_pullbackSnd** 是 
Mathlib 中的一个引理，位于命名空间 `CategoryTheory.MorphismProperty.IsLocalAtTarget`。
形式化陈述：iff_of_forall_pullbackSnd [P.IsLocalAtTarget K] {X Y : C} {R : Presieve Y}
 (hR : R in K Y) {f : X ⟶ Y} : P f ↔ forall {U : C} (g : U ⟶ Y) [HasPullback f g
], R g -> P (pullback.snd f g)
参数：hR : R in K Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma iff_of_forall_pullbackSnd [P.IsLocalAtTarget K] {X Y : C} {R : Presieve Y} (hR : R ∈ K Y)
    {f : X ⟶ Y} :
    P f ↔ ∀ {U : C} (g : U ⟶ Y) [HasPullback f g], R g → P (pullback.snd f g) := by
  grind [IsLocalAtTarget]
/-
**CategoryTheory.MorphismProperty.IsLocalAtTarget.mk_of_iff_of_zeroHypercover** 
是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.MorphismProperty.IsLocalAtTarget`。
形式化陈述：mk_of_iff_of_zeroHypercover [K.HasPullbacks] [P.RespectsIso] (H : forall {
X Y : C} (f : X ⟶ Y) (𝒰 : Precoverage.ZeroHypercover.{max u v} K Y), P f ↔ foral
l i, P (pullback.snd f (𝒰.f i))) : P.IsLocalAtTarget K
参数：H : forall {X Y : C} (f : X ⟶ Y) (𝒰 : Precoverage.ZeroHypercover.{max u v} K 
Y), P f ↔ forall i, P (pullback.snd f (𝒰.f i))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Precoverage.ZeroHypercover.instHasPullbackFOfHasPullbacks
Presieve₀_1`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} 
(E : CategoryTheory.PreZeroHypercover X) (f : Y ⟶ X)   [E.presieve₀.HasPu…
· 使用定理 `CategoryTheory.Precoverage.ZeroHypercover.instHasPullbacksPresieve₀OfHas
Pullbacks`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (K : Categor
yTheory.Precoverage C) [K.HasPullbacks] {X Y : C}   (E : K.ZeroHypercov…
· 使用引理 `CategoryTheory.MorphismProperty.IsLocalAtTarget.mk_of_iff`：mk_of_iff [P.
RespectsIso] (H : forall ⦃X Y : C⦄ ⦃f : X ⟶ Y⦄ ⦃R : Presieve Y⦄, R in K Y -> (P 
f ↔ forall {U : C} (g : U ⟶ Y) [HasPullback f g…
· 使用定理 `CategoryTheory.Presieve.exists_eq_preZeroHypercover`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C] {S : C} (R : CategoryTheory.Presieve S), ∃
 E, R = E.presieve₀
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Presieve.HasPullbacks.hasPullback`：∀ {C : Type u₁} {inst 
: CategoryTheory.Category.{v₁, u₁} C} {X : C} {R : CategoryTheory.Presieve X} {Y
 : C} (f : Y ⟶ X)   [self : R.HasPullb…
· 使用定理 `CategoryTheory.Precoverage.hasPullbacks_of_mem`：∀ {C : Type u} {inst : C
ategoryTheory.Category.{v, u} C} {J : CategoryTheory.Precoverage C} [self : J.Ha
sPullbacks]   {X Y : C} {R : Categor…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
lemma mk_of_iff_of_zeroHypercover [K.HasPullbacks] [P.RespectsIso]
    (H : ∀ {X Y : C} (f : X ⟶ Y) (𝒰 : Precoverage.ZeroHypercover.{max u v} K Y),
      P f ↔ ∀ i, P (pullback.snd f (𝒰.f i))) :
    P.IsLocalAtTarget K := by
  refine mk_of_iff fun X Y f R hR ↦ ?_
  obtain ⟨𝒰, rfl⟩ := R.exists_eq_preZeroHypercover
  rw [H _ ⟨𝒰, hR⟩]
  have _ (i) : HasPullback (𝒰.f i) f := (Precoverage.hasPullbacks_of_mem _ hR).hasPullback ⟨i⟩
  refine ⟨fun h U g hfg ↦ ?_, fun h i ↦ h _ ⟨i⟩⟩
  rintro ⟨i⟩
  exact h i
/-
**CategoryTheory.MorphismProperty.IsLocalAtTarget.mk_of_small** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.MorphismProperty.IsLocalAtTarget`。
形式化陈述：mk_of_small [K.HasPullbacks] [P.RespectsIso] [Precoverage.Small.{w} K] (h₁
 : forall {X Y : C} {f : X ⟶ Y} (𝒰 : Precoverage.ZeroHypercover.{max u v} K Y), 
P f -> forall i, P (pullback.snd f (𝒰.f i))) (h₂ : forall {X Y : C} {f : X ⟶ Y} 
(𝒰 : Precoverage.ZeroHypercover.{w} K Y), (forall i, P (pullback.snd f (𝒰.f i)))
 -> P f) : P.IsLocalAtTarget K
参数：h₁ : forall {X Y : C} {f : X ⟶ Y} (𝒰 : Precoverage.ZeroHypercover.{max u v} K
 Y), P f -> forall i, P (pullback.snd f (𝒰.f i))；h₂ : forall {X Y : C} {f : X ⟶ 
Y} (𝒰 : Precoverage.ZeroHypercover.{w} K Y), (forall i, P (pullback.snd f (𝒰.f i
))) -> P f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Precoverage.ZeroHypercover.instHasPullbackFOfHasPullbacks
Presieve₀_1`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} 
(E : CategoryTheory.PreZeroHypercover X) (f : Y ⟶ X)   [E.presieve₀.HasPu…
· 使用定理 `CategoryTheory.Precoverage.ZeroHypercover.instHasPullbacksPresieve₀OfHas
Pullbacks`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (K : Categor
yTheory.Precoverage C) [K.HasPullbacks] {X Y : C}   (E : K.ZeroHypercov…
· 使用引理 `CategoryTheory.MorphismProperty.IsLocalAtTarget.mk_of_iff_of_zeroHyperco
ver`：mk_of_iff_of_zeroHypercover [K.HasPullbacks] [P.RespectsIso] (H : forall {X
 Y : C} (f : X ⟶ Y) (𝒰 : Precoverage.ZeroHypercover.{max u v} K Y…
· 使用定理 `CategoryTheory.Precoverage.instSmallOfSmall`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] (J : CategoryTheory.Precoverage C) [J.Small] {S : 
C}   (E : J.ZeroHypercover S), E.…
-/
lemma mk_of_small [K.HasPullbacks] [P.RespectsIso] [Precoverage.Small.{w} K]
    (h₁ : ∀ {X Y : C} {f : X ⟶ Y} (𝒰 : Precoverage.ZeroHypercover.{max u v} K Y),
        P f → ∀ i, P (pullback.snd f (𝒰.f i)))
    (h₂ : ∀ {X Y : C} {f : X ⟶ Y} (𝒰 : Precoverage.ZeroHypercover.{w} K Y),
        (∀ i, P (pullback.snd f (𝒰.f i))) → P f) :
    P.IsLocalAtTarget K :=
  .mk_of_iff_of_zeroHypercover fun _ 𝒰 ↦ ⟨fun hf _ ↦ h₁ 𝒰 hf _,
    fun h ↦ h₂ 𝒰.restrictIndexOfSmall fun _ ↦ h _⟩
/-
**CategoryTheory.MorphismProperty.IsLocalAtTarget.mk_of_isStableUnderBaseChange*
* 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.MorphismProperty.IsLocalAtTarget`。
形式化陈述：mk_of_isStableUnderBaseChange [K.HasPullbacks] [P.IsStableUnderBaseChange]
 (H : forall {X Y : C} (f : X ⟶ Y) (𝒰 : Precoverage.ZeroHypercover.{max u v} K Y
), (forall (i : 𝒰.I₀), P (pullback.snd f (𝒰.f i))) -> P f) : P.IsLocalAtTarget K
参数：H : forall {X Y : C} (f : X ⟶ Y) (𝒰 : Precoverage.ZeroHypercover.{max u v} K 
Y), (forall (i : 𝒰.I₀), P (pullback.snd f (𝒰.f i))) -> P f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Precoverage.ZeroHypercover.instHasPullbackFOfHasPullbacks
Presieve₀_1`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} 
(E : CategoryTheory.PreZeroHypercover X) (f : Y ⟶ X)   [E.presieve₀.HasPu…
· 使用定理 `CategoryTheory.Precoverage.ZeroHypercover.instHasPullbacksPresieve₀OfHas
Pullbacks`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (K : Categor
yTheory.Precoverage C) [K.HasPullbacks] {X Y : C}   (E : K.ZeroHypercov…
· 使用引理 `CategoryTheory.MorphismProperty.IsLocalAtTarget.mk_of_iff_of_zeroHyperco
ver`：mk_of_iff_of_zeroHypercover [K.HasPullbacks] [P.RespectsIso] (H : forall {X
 Y : C} (f : X ⟶ Y) (𝒰 : Precoverage.ZeroHypercover.{max u v} K Y…
· 使用定理 `CategoryTheory.MorphismProperty.IsStableUnderBaseChange.respectsIso`：∀ {
C : Type u} [inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.Morphi
smProperty C}   [P.IsStableUnderBaseChange], P.RespectsIs…
· 使用定理 `CategoryTheory.MorphismProperty.pullback_snd`：pullback_snd {X Y S : C} (
f : X ⟶ S) (g : Y ⟶ S) [HasPullback f g] [P.IsStableUnderBaseChangeAlong g] (H :
 P f) : P (pullback.snd f g)
· 使用定理 `CategoryTheory.MorphismProperty.instIsStableUnderBaseChangeAlongOfIsStab
leUnderBaseChange`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (P :
 CategoryTheory.MorphismProperty C)   [P.IsStableUnderBaseChange] {X Y : C} (f …
-/
lemma mk_of_isStableUnderBaseChange [K.HasPullbacks] [P.IsStableUnderBaseChange]
    (H : ∀ {X Y : C} (f : X ⟶ Y) (𝒰 : Precoverage.ZeroHypercover.{max u v} K Y),
      (∀ (i : 𝒰.I₀), P (pullback.snd f (𝒰.f i))) → P f) :
    P.IsLocalAtTarget K :=
  .mk_of_iff_of_zeroHypercover fun _ 𝒰 ↦ ⟨fun hf _ ↦ P.pullback_snd _ _ hf, fun h ↦ H _ 𝒰 h⟩
/-
**CategoryTheory.MorphismProperty.IsLocalAtTarget.of_le** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.MorphismProperty.IsLocalAtTarget`。
形式化陈述：of_le [IsLocalAtTarget P L] (hle : K <= L) : IsLocalAtTarget P K where pul
lbackSnd h i hf
参数：hle : K <= L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsLocalAtTarget.toRespects`：∀ {C : Type 
u} {inst : CategoryTheory.Category.{v, u} C} {P : CategoryTheory.MorphismPropert
y C}   (K : CategoryTheory.Precoverage C) [self …
· 使用定理 `CategoryTheory.MorphismProperty.IsLocalAtTarget.pullbackSnd`：∀ {C : Type
 u} {inst : CategoryTheory.Category.{v, u} C} {P : CategoryTheory.MorphismProper
ty C}   {K : CategoryTheory.Precoverage C} [self …
· 使用定理 `CategoryTheory.MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd`：∀
 {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {P : CategoryTheory.Morp
hismProperty C}   {K : CategoryTheory.Precoverage C} [self …
-/
lemma of_le [IsLocalAtTarget P L] (hle : K ≤ L) : IsLocalAtTarget P K where
  pullbackSnd h i hf := pullbackSnd (hle _ h) i hf
  of_forall_pullbackSnd hR h := of_forall_pullbackSnd (hle _ hR) h
/-
**CategoryTheory.MorphismProperty.IsLocalAtTarget.top** 是 Mathlib 中的一个实例，位于命名空间 
`CategoryTheory.MorphismProperty.IsLocalAtTarget`。
形式化陈述：top : IsLocalAtTarget (⊤ : MorphismProperty C) K where pullbackSnd
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.instRespectsIsoTop`：∀ {C : Type u} [inst
 : CategoryTheory.Category.{v, u} C], ⊤.RespectsIso
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
instance top : IsLocalAtTarget (⊤ : MorphismProperty C) K where
  pullbackSnd := by simp
  of_forall_pullbackSnd := by simp

variable [IsLocalAtTarget P K] {X Y : C} {f : X ⟶ Y} (𝒰 : Precoverage.ZeroHypercover.{w} K Y)
/-
**CategoryTheory.MorphismProperty.IsLocalAtTarget.of_isPullback** 是 Mathlib 中的一个
引理，位于命名空间 `CategoryTheory.MorphismProperty.IsLocalAtTarget`。
形式化陈述：of_isPullback {X' : C} (i : 𝒰.I₀) {fst : X' ⟶ X} {snd : X' ⟶ 𝒰.X i} (h : I
sPullback fst snd f (𝒰.f i)) (hf : P f) : P snd
参数：i : 𝒰.I₀；h : IsPullback fst snd f (𝒰.f i)；hf : P f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.IsPullback.hasPullback`：hasPullback (h : IsPullback fst s
nd f g) : HasPullback f g where exists_limit
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.MorphismProperty.cancel_left_of_respectsIso`：cancel_left_
of_respectsIso (P : MorphismProperty C) [hP : RespectsIso P] {X Y Z : C} (f : X 
⟶ Y) (g : Y ⟶ Z) [IsIso f] : P (f ≫ g) ↔ P g
· 使用定理 `CategoryTheory.MorphismProperty.IsLocalAtTarget.toRespects`：∀ {C : Type 
u} {inst : CategoryTheory.Category.{v, u} C} {P : CategoryTheory.MorphismPropert
y C}   (K : CategoryTheory.Precoverage C) [self …
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `CategoryTheory.IsPullback.isoPullback_inv_snd`：isoPullback_inv_snd (h : 
IsPullback fst snd f g) [HasPullback f g] : h.isoPullback.inv ≫ snd = pullback.s
nd _ _
· 使用定理 `CategoryTheory.MorphismProperty.IsLocalAtTarget.pullbackSnd`：∀ {C : Type
 u} {inst : CategoryTheory.Category.{v, u} C} {P : CategoryTheory.MorphismProper
ty C}   {K : CategoryTheory.Precoverage C} [self …
· 使用定理 `CategoryTheory.Precoverage.ZeroHypercover.mem₀`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] {J : CategoryTheory.Precoverage C} {S : C}   (s
elf : J.ZeroHypercover S), self.pres…
-/
lemma of_isPullback {X' : C} (i : 𝒰.I₀) {fst : X' ⟶ X} {snd : X' ⟶ 𝒰.X i}
    (h : IsPullback fst snd f (𝒰.f i)) (hf : P f) :
    P snd := by
  have : HasPullback f (𝒰.f i) := h.hasPullback
  rw [← P.cancel_left_of_respectsIso h.isoPullback.inv, h.isoPullback_inv_snd]
  exact pullbackSnd 𝒰.mem₀ ⟨i⟩ hf
/-
**CategoryTheory.MorphismProperty.IsLocalAtTarget.of_zeroHypercover** 是 Mathlib 
中的一个引理，位于命名空间 `CategoryTheory.MorphismProperty.IsLocalAtTarget`。
形式化陈述：of_zeroHypercover [K.HasPullbacks] (h : forall (i : 𝒰.I₀), P (pullback.snd
 f (𝒰.f i))) : P f
参数：h : forall (i : 𝒰.I₀), P (pullback.snd f (𝒰.f i))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Precoverage.ZeroHypercover.instHasPullbackFOfHasPullbacks
Presieve₀_1`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} 
(E : CategoryTheory.PreZeroHypercover X) (f : Y ⟶ X)   [E.presieve₀.HasPu…
· 使用定理 `CategoryTheory.Precoverage.ZeroHypercover.instHasPullbacksPresieve₀OfHas
Pullbacks`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (K : Categor
yTheory.Precoverage C) [K.HasPullbacks] {X Y : C}   (E : K.ZeroHypercov…
· 使用定理 `CategoryTheory.MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd`：∀
 {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {P : CategoryTheory.Morp
hismProperty C}   {K : CategoryTheory.Precoverage C} [self …
· 使用定理 `CategoryTheory.Precoverage.ZeroHypercover.mem₀`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] {J : CategoryTheory.Precoverage C} {S : C}   (s
elf : J.ZeroHypercover S), self.pres…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
lemma of_zeroHypercover [K.HasPullbacks] (h : ∀ (i : 𝒰.I₀), P (pullback.snd f (𝒰.f i))) :
    P f :=
  of_forall_pullbackSnd 𝒰.mem₀ (by rintro _ _ _ ⟨i⟩; exact h _)
/-
**CategoryTheory.MorphismProperty.IsLocalAtTarget.iff_of_zeroHypercover** 是 Math
lib 中的一个引理，位于命名空间 `CategoryTheory.MorphismProperty.IsLocalAtTarget`。
形式化陈述：iff_of_zeroHypercover [K.HasPullbacks] : P f ↔ forall i, P (pullback.snd f
 (𝒰.f i))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Precoverage.ZeroHypercover.instHasPullbackFOfHasPullbacks
Presieve₀_1`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} 
(E : CategoryTheory.PreZeroHypercover X) (f : Y ⟶ X)   [E.presieve₀.HasPu…
· 使用定理 `CategoryTheory.Precoverage.ZeroHypercover.instHasPullbacksPresieve₀OfHas
Pullbacks`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (K : Categor
yTheory.Precoverage C) [K.HasPullbacks] {X Y : C}   (E : K.ZeroHypercov…
· 使用定理 `CategoryTheory.MorphismProperty.IsLocalAtTarget.pullbackSnd`：∀ {C : Type
 u} {inst : CategoryTheory.Category.{v, u} C} {P : CategoryTheory.MorphismProper
ty C}   {K : CategoryTheory.Precoverage C} [self …
· 使用定理 `CategoryTheory.Precoverage.ZeroHypercover.mem₀`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] {J : CategoryTheory.Precoverage C} {S : C}   (s
elf : J.ZeroHypercover S), self.pres…
· 使用引理 `CategoryTheory.MorphismProperty.IsLocalAtTarget.of_zeroHypercover`：of_ze
roHypercover [K.HasPullbacks] (h : forall (i : 𝒰.I₀), P (pullback.snd f (𝒰.f i))
) : P f
-/
lemma iff_of_zeroHypercover [K.HasPullbacks] : P f ↔ ∀ i, P (pullback.snd f (𝒰.f i)) :=
  ⟨fun hf _ ↦ pullbackSnd 𝒰.mem₀ ⟨_⟩ hf, fun h ↦ of_zeroHypercover _ h⟩
/-
**CategoryTheory.MorphismProperty.IsLocalAtTarget.inf** 是 Mathlib 中的一个实例，位于命名空间 
`CategoryTheory.MorphismProperty.IsLocalAtTarget`。
形式化陈述：inf (P Q : MorphismProperty C) [IsLocalAtTarget P K] [IsLocalAtTarget Q K]
 : IsLocalAtTarget (P ⊓ Q) K where pullbackSnd hR i h
参数：P Q : MorphismProperty C。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.RespectsIso.inf`：∀ {C : Type u} [inst : 
CategoryTheory.Category.{v, u} C] (P Q : CategoryTheory.MorphismProperty C) [P.R
espectsIso]   [Q.RespectsIso], (P ⊓ Q…
· 使用定理 `CategoryTheory.MorphismProperty.IsLocalAtTarget.toRespects`：∀ {C : Type 
u} {inst : CategoryTheory.Category.{v, u} C} {P : CategoryTheory.MorphismPropert
y C}   (K : CategoryTheory.Precoverage C) [self …
· 使用定理 `CategoryTheory.MorphismProperty.IsLocalAtTarget.pullbackSnd`：∀ {C : Type
 u} {inst : CategoryTheory.Category.{v, u} C} {P : CategoryTheory.MorphismProper
ty C}   {K : CategoryTheory.Precoverage C} [self …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `CategoryTheory.MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd`：∀
 {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {P : CategoryTheory.Morp
hismProperty C}   {K : CategoryTheory.Precoverage C} [self …
-/
instance inf (P Q : MorphismProperty C) [IsLocalAtTarget P K] [IsLocalAtTarget Q K] :
    IsLocalAtTarget (P ⊓ Q) K where
  pullbackSnd hR i h := ⟨pullbackSnd hR i h.1, pullbackSnd hR i h.2⟩
  of_forall_pullbackSnd hR h :=
    ⟨of_forall_pullbackSnd hR fun i ↦ (h i).1, of_forall_pullbackSnd hR fun i ↦ (h i).2⟩

end IsLocalAtTarget

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.MorphismProperty.of_zeroHypercover_target** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：of_zeroHypercover_target {P : MorphismProperty C} {K : Precoverage C} [K.H
asPullbacks] [P.IsLocalAtTarget K] {X Y : C} {f : X ⟶ Y} (𝒰 : Precoverage.ZeroHy
percover.{w} K Y) [Precoverage.ZeroHypercover.Small.{v} 𝒰] (h : forall i, P (pul
lback.snd f (𝒰.f i))) : P f
参数：𝒰 : Precoverage.ZeroHypercover.{w} K Y；h : forall i, P (pullback.snd f (𝒰.f i
))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Precoverage.ZeroHypercover.instHasPullbackFOfHasPullbacks
Presieve₀_1`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} 
(E : CategoryTheory.PreZeroHypercover X) (f : Y ⟶ X)   [E.presieve₀.HasPu…
· 使用定理 `CategoryTheory.Precoverage.ZeroHypercover.instHasPullbacksPresieve₀OfHas
Pullbacks`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (K : Categor
yTheory.Precoverage C) [K.HasPullbacks] {X Y : C}   (E : K.ZeroHypercov…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.MorphismProperty.IsLocalAtTarget.iff_of_zeroHypercover`：i
ff_of_zeroHypercover [K.HasPullbacks] : P f ↔ forall i, P (pullback.snd f (𝒰.f i
))
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma of_zeroHypercover_target {P : MorphismProperty C} {K : Precoverage C} [K.HasPullbacks]
    [P.IsLocalAtTarget K] {X Y : C} {f : X ⟶ Y} (𝒰 : Precoverage.ZeroHypercover.{w} K Y)
    [Precoverage.ZeroHypercover.Small.{v} 𝒰] (h : ∀ i, P (pullback.snd f (𝒰.f i))) :
    P f := by
  rw [IsLocalAtTarget.iff_of_zeroHypercover (P := P) 𝒰.restrictIndexOfSmall]
  simp [h]

alias iff_of_zeroHypercover_target := IsLocalAtTarget.iff_of_zeroHypercover

/--
A property of morphisms `P` in `C` is local at the source with respect to the precoverage `K` if
it respects isomorphisms, and:
`P` holds for `f : X ⟶ Y` if and only if it holds for the restrictions of `f` to `Uᵢ` for a
`0`-hypercover `{Uᵢ}` of `X` in the precoverage `K`.
-/
/-
**CategoryTheory.MorphismProperty.IsLocalAtSource** 是 Mathlib 中的一个归纳类型，位于命名空间 `C
ategoryTheory.MorphismProperty`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] → CategoryTheor
y.MorphismProperty C → CategoryTheory.Precoverage C → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A property of morphisms `P` in `C` is local at the source with respect to the pr
ecoverage `K` if
it respects isomorphisms, and:
`P` holds for `f : X ⟶ Y` if and only if it holds for the restrictions of `f` to
 `Uᵢ` for a
`0`-hypercover `{Uᵢ}` of `X` in the precoverage `K`.
-/
class IsLocalAtSource (P : MorphismProperty C) (K : Precoverage C) extends RespectsIso P where
  /-- If `P` holds for `f : X ⟶ Y`, it also holds for `𝒰.f i ≫ f` for any `K`-cover `R` of `X`. -/
  comp {X Y : C} {f : X ⟶ Y} {R : Presieve X} (hR : R ∈ K X) {U : C} (g : U ⟶ X) (hg : R g)
    (hf : P f) : P (g ≫ f)
  /-- If `P` holds for `𝒰.f i ≫ f` for all `i`, it holds for `f : X ⟶ Y` for any `K`-cover
  `R` of X. -/
  of_forall_comp {X Y : C} {f : X ⟶ Y} {R : Presieve X} (hR : R ∈ K X) :
    (∀ ⦃U : C⦄ ⦃g : U ⟶ X⦄, R g → P (g ≫ f)) → P f

namespace IsLocalAtSource

variable {P : MorphismProperty C} {K L : Precoverage C}

/-
**CategoryTheory.MorphismProperty.IsLocalAtSource.mk_of_iff** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.MorphismProperty.IsLocalAtSource`。
形式化陈述：mk_of_iff [P.RespectsIso] (H : forall {X Y : C} {f : X ⟶ Y} {R : Presieve 
X}, R in K X -> (P f ↔ forall ⦃U : C⦄ ⦃g : U ⟶ X⦄, R g -> P (g ≫ f))) : P.IsLoca
lAtSource K where comp hR _ _ hg hf
参数：H : forall {X Y : C} {f : X ⟶ Y} {R : Presieve X}, R in K X -> (P f ↔ forall 
⦃U : C⦄ ⦃g : U ⟶ X⦄, R g -> P (g ≫ f))。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mk_of_iff [P.RespectsIso]
    (H : ∀ {X Y : C} {f : X ⟶ Y} {R : Presieve X}, R ∈ K X →
      (P f ↔ ∀ ⦃U : C⦄ ⦃g : U ⟶ X⦄, R g → P (g ≫ f))) :
    P.IsLocalAtSource K where
  comp hR _ _ hg hf := by grind
  of_forall_comp hR h := by grind
/-
**CategoryTheory.MorphismProperty.IsLocalAtSource.mk_of_iff_of_zeroHypercover** 
是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.MorphismProperty.IsLocalAtSource`。
形式化陈述：mk_of_iff_of_zeroHypercover [P.RespectsIso] (H : forall {X Y : C} (f : X ⟶
 Y) (𝒰 : Precoverage.ZeroHypercover.{max u v} K X), P f ↔ forall i, P (𝒰.f i ≫ f
)) : P.IsLocalAtSource K
参数：H : forall {X Y : C} (f : X ⟶ Y) (𝒰 : Precoverage.ZeroHypercover.{max u v} K 
X), P f ↔ forall i, P (𝒰.f i ≫ f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.IsLocalAtSource.mk_of_iff`：mk_of_iff [P.
RespectsIso] (H : forall {X Y : C} {f : X ⟶ Y} {R : Presieve X}, R in K X -> (P 
f ↔ forall ⦃U : C⦄ ⦃g : U ⟶ X⦄, R g -> P (g ≫ f…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Precoverage.mem_iff_exists_zeroHypercover`：mem_iff_exists
_zeroHypercover {X : C} {R : Presieve X} : R in J X ↔ exists (𝒰 : ZeroHypercover
.{max u v} J X), R = Presieve.ofArrows 𝒰.X 𝒰.f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
lemma mk_of_iff_of_zeroHypercover [P.RespectsIso]
    (H : ∀ {X Y : C} (f : X ⟶ Y) (𝒰 : Precoverage.ZeroHypercover.{max u v} K X),
        P f ↔ ∀ i, P (𝒰.f i ≫ f)) :
    P.IsLocalAtSource K := by
  refine .mk_of_iff fun {X Y} f R hR ↦ ?_
  rw [Precoverage.mem_iff_exists_zeroHypercover] at hR
  obtain ⟨𝒰, rfl⟩ := hR
  rw [H _ 𝒰]
  refine ⟨fun h U g ↦ ?_, fun h i ↦ h ⟨i⟩⟩
  rintro ⟨i⟩
  apply h
/-
**CategoryTheory.MorphismProperty.IsLocalAtSource.mk_of_small** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.MorphismProperty.IsLocalAtSource`。
形式化陈述：mk_of_small [P.RespectsIso] [Precoverage.Small.{w} K] (h₁ : forall {X Y : 
C} {f : X ⟶ Y} (𝒰 : Precoverage.ZeroHypercover.{max u v} K X), P f -> forall i, 
P (𝒰.f i ≫ f)) (h₂ : forall {X Y : C} {f : X ⟶ Y} (𝒰 : Precoverage.ZeroHypercove
r.{w} K X), (forall i, P (𝒰.f i ≫ f)) -> P f) : P.IsLocalAtSource K
参数：h₁ : forall {X Y : C} {f : X ⟶ Y} (𝒰 : Precoverage.ZeroHypercover.{max u v} K
 X), P f -> forall i, P (𝒰.f i ≫ f)；h₂ : forall {X Y : C} {f : X ⟶ Y} (𝒰 : Preco
verage.ZeroHypercover.{w} K X), (forall i, P (𝒰.f i ≫ f)) -> P f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.IsLocalAtSource.mk_of_iff_of_zeroHyperco
ver`：mk_of_iff_of_zeroHypercover [P.RespectsIso] (H : forall {X Y : C} (f : X ⟶ 
Y) (𝒰 : Precoverage.ZeroHypercover.{max u v} K X), P f ↔ forall i…
· 使用定理 `CategoryTheory.Precoverage.instSmallOfSmall`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] (J : CategoryTheory.Precoverage C) [J.Small] {S : 
C}   (E : J.ZeroHypercover S), E.…
-/
lemma mk_of_small [P.RespectsIso] [Precoverage.Small.{w} K]
    (h₁ : ∀ {X Y : C} {f : X ⟶ Y} (𝒰 : Precoverage.ZeroHypercover.{max u v} K X),
        P f → ∀ i, P (𝒰.f i ≫ f))
    (h₂ : ∀ {X Y : C} {f : X ⟶ Y} (𝒰 : Precoverage.ZeroHypercover.{w} K X),
        (∀ i, P (𝒰.f i ≫ f)) → P f) :
    P.IsLocalAtSource K :=
  .mk_of_iff_of_zeroHypercover fun _ 𝒰 ↦ ⟨fun hf _ ↦ h₁ 𝒰 hf _,
    fun h ↦ h₂ 𝒰.restrictIndexOfSmall fun _ ↦ h _⟩
/-
**CategoryTheory.MorphismProperty.IsLocalAtSource.of_le** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.MorphismProperty.IsLocalAtSource`。
形式化陈述：of_le [IsLocalAtSource P L] (hle : K <= L) : IsLocalAtSource P K where com
p hR _ _
参数：hle : K <= L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsLocalAtSource.toRespects`：∀ {C : Type 
u} {inst : CategoryTheory.Category.{v, u} C} {P : CategoryTheory.MorphismPropert
y C}   (K : CategoryTheory.Precoverage C) [self …
· 使用定理 `CategoryTheory.MorphismProperty.IsLocalAtSource.comp`：∀ {C : Type u} {in
st : CategoryTheory.Category.{v, u} C} {P : CategoryTheory.MorphismProperty C}  
 {K : CategoryTheory.Precoverage C} [self …
· 使用定理 `CategoryTheory.MorphismProperty.IsLocalAtSource.of_forall_comp`：∀ {C : T
ype u} {inst : CategoryTheory.Category.{v, u} C} {P : CategoryTheory.MorphismPro
perty C}   {K : CategoryTheory.Precoverage C} [self …
-/
lemma of_le [IsLocalAtSource P L] (hle : K ≤ L) : IsLocalAtSource P K where
  comp hR _ _ := comp (hle _ hR) _
  of_forall_comp hR h := of_forall_comp (hle _ hR) h
/-
**CategoryTheory.MorphismProperty.IsLocalAtSource.top** 是 Mathlib 中的一个实例，位于命名空间 
`CategoryTheory.MorphismProperty.IsLocalAtSource`。
形式化陈述：top : IsLocalAtSource (⊤ : MorphismProperty C) K where comp
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.instRespectsIsoTop`：∀ {C : Type u} [inst
 : CategoryTheory.Category.{v, u} C], ⊤.RespectsIso
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
instance top : IsLocalAtSource (⊤ : MorphismProperty C) K where
  comp := by simp
  of_forall_comp := by simp

variable [IsLocalAtSource P K] {X Y : C} {f : X ⟶ Y} (𝒰 : Precoverage.ZeroHypercover.{w} K X)
/-
**CategoryTheory.MorphismProperty.IsLocalAtSource.of_zeroHypercover** 是 Mathlib 
中的一个引理，位于命名空间 `CategoryTheory.MorphismProperty.IsLocalAtSource`。
形式化陈述：of_zeroHypercover (h : forall i, P (𝒰.f i ≫ f)) : P f
参数：h : forall i, P (𝒰.f i ≫ f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsLocalAtSource.of_forall_comp`：∀ {C : T
ype u} {inst : CategoryTheory.Category.{v, u} C} {P : CategoryTheory.MorphismPro
perty C}   {K : CategoryTheory.Precoverage C} [self …
· 使用定理 `CategoryTheory.Precoverage.ZeroHypercover.mem₀`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] {J : CategoryTheory.Precoverage C} {S : C}   (s
elf : J.ZeroHypercover S), self.pres…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
lemma of_zeroHypercover (h : ∀ i, P (𝒰.f i ≫ f)) : P f :=
  of_forall_comp 𝒰.mem₀ fun U g ↦ by rintro ⟨i⟩; exact h _
/-
**CategoryTheory.MorphismProperty.IsLocalAtSource.iff_of_zeroHypercover** 是 Math
lib 中的一个引理，位于命名空间 `CategoryTheory.MorphismProperty.IsLocalAtSource`。
形式化陈述：iff_of_zeroHypercover : P f ↔ forall i, P (𝒰.f i ≫ f)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsLocalAtSource.comp`：∀ {C : Type u} {in
st : CategoryTheory.Category.{v, u} C} {P : CategoryTheory.MorphismProperty C}  
 {K : CategoryTheory.Precoverage C} [self …
· 使用定理 `CategoryTheory.Precoverage.ZeroHypercover.mem₀`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] {J : CategoryTheory.Precoverage C} {S : C}   (s
elf : J.ZeroHypercover S), self.pres…
· 使用定理 `CategoryTheory.MorphismProperty.IsLocalAtSource.of_forall_comp`：∀ {C : T
ype u} {inst : CategoryTheory.Category.{v, u} C} {P : CategoryTheory.MorphismPro
perty C}   {K : CategoryTheory.Precoverage C} [self …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
lemma iff_of_zeroHypercover : P f ↔ ∀ i, P (𝒰.f i ≫ f) :=
  ⟨fun hf i ↦ comp 𝒰.mem₀ _ ⟨i⟩ hf,
    fun h ↦ of_forall_comp 𝒰.mem₀ fun U g ↦ by rintro ⟨i⟩; exact h _⟩
/-
**CategoryTheory.MorphismProperty.IsLocalAtSource.inf** 是 Mathlib 中的一个实例，位于命名空间 
`CategoryTheory.MorphismProperty.IsLocalAtSource`。
形式化陈述：inf (P Q : MorphismProperty C) [IsLocalAtSource P K] [IsLocalAtSource Q K]
 : IsLocalAtSource (P ⊓ Q) K where comp hR _ _ hg hf
参数：P Q : MorphismProperty C。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.RespectsIso.inf`：∀ {C : Type u} [inst : 
CategoryTheory.Category.{v, u} C] (P Q : CategoryTheory.MorphismProperty C) [P.R
espectsIso]   [Q.RespectsIso], (P ⊓ Q…
· 使用定理 `CategoryTheory.MorphismProperty.IsLocalAtSource.toRespects`：∀ {C : Type 
u} {inst : CategoryTheory.Category.{v, u} C} {P : CategoryTheory.MorphismPropert
y C}   (K : CategoryTheory.Precoverage C) [self …
· 使用定理 `CategoryTheory.MorphismProperty.IsLocalAtSource.comp`：∀ {C : Type u} {in
st : CategoryTheory.Category.{v, u} C} {P : CategoryTheory.MorphismProperty C}  
 {K : CategoryTheory.Precoverage C} [self …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `CategoryTheory.MorphismProperty.IsLocalAtSource.of_forall_comp`：∀ {C : T
ype u} {inst : CategoryTheory.Category.{v, u} C} {P : CategoryTheory.MorphismPro
perty C}   {K : CategoryTheory.Precoverage C} [self …
-/
instance inf (P Q : MorphismProperty C) [IsLocalAtSource P K] [IsLocalAtSource Q K] :
    IsLocalAtSource (P ⊓ Q) K where
  comp hR _ _ hg hf := ⟨comp hR _ hg hf.left, comp hR _ hg hf.right⟩
  of_forall_comp hR h :=
    ⟨of_forall_comp hR fun _ _ hg ↦ (h hg).1, of_forall_comp hR fun _ _ hg ↦ (h hg).2⟩

end IsLocalAtSource

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.MorphismProperty.of_zeroHypercover_source** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.MorphismProperty`。
形式化陈述：of_zeroHypercover_source {P : MorphismProperty C} {K : Precoverage C} [P.I
sLocalAtSource K] {X Y : C} {f : X ⟶ Y} (𝒰 : Precoverage.ZeroHypercover.{w} K X)
 [Precoverage.ZeroHypercover.Small.{v} 𝒰] (h : forall i, P (𝒰.f i ≫ f)) : P f
参数：𝒰 : Precoverage.ZeroHypercover.{w} K X；h : forall i, P (𝒰.f i ≫ f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.MorphismProperty.IsLocalAtSource.iff_of_zeroHypercover`：i
ff_of_zeroHypercover : P f ↔ forall i, P (𝒰.f i ≫ f)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma of_zeroHypercover_source {P : MorphismProperty C} {K : Precoverage C}
    [P.IsLocalAtSource K] {X Y : C} {f : X ⟶ Y} (𝒰 : Precoverage.ZeroHypercover.{w} K X)
    [Precoverage.ZeroHypercover.Small.{v} 𝒰] (h : ∀ i, P (𝒰.f i ≫ f)) :
    P f := by
  rw [IsLocalAtSource.iff_of_zeroHypercover (P := P) 𝒰.restrictIndexOfSmall]
  simp [h]

alias iff_of_zeroHypercover_source := IsLocalAtSource.iff_of_zeroHypercover

end MorphismProperty

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Let `J` be a precoverage for which isomorphisms are local at the target. Let
`f, g : X ⟶ Y` be two morphisms over `S` and `𝒰` a `J`-cover of `S`.
If for all `i`, the maps `X ×[S] Uᵢ ⟶ Y ×[S] Uᵢ` are equal, then
`f` and `g` are equal. -/
/-
**CategoryTheory.eq_of_zeroHypercover_target** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory`。
形式化陈述：eq_of_zeroHypercover_target [HasEqualizers C] [HasPullbacks C] {X Y S : C}
 {f g : X ⟶ Y} {s : X ⟶ S} {t : Y ⟶ S} (hf : f ≫ t = s) (hg : g ≫ t = s) {J : Pr
ecoverage C} (𝒰 : Precoverage.ZeroHypercover.{w} J S) [J.IsStableUnderBaseChange
] [(MorphismProperty.isomorphisms C).IsLocalAtTarget J] (H : forall i, pullback.
map s (𝒰.f i) t (𝒰.f i) f (𝟙 (𝒰.X i)) (𝟙 S) (by simp [hf]) (by simp) = pullback.
map s (𝒰.f i) t (𝒰.f i) g (𝟙 (𝒰.X i)) (𝟙 S) (by simp [hg]) (by simp)) : f = g
参数：hf : f ≫ t = s；hg : g ≫ t = s；𝒰 : Precoverage.ZeroHypercover.{w} J S；Morphism
Property.isomorphisms C；H : forall i, pullback.map s (𝒰.f i) t (𝒰.f i) f (𝟙 (𝒰.X
 i)) (𝟙 S) (by simp [hf]) (by simp) = pullback.map s (𝒰.f i) t (𝒰.f i) g (𝟙 (𝒰.X
 i)) (𝟙 S) (by simp [hg]) (by simp)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Precoverage.ZeroHypercover.instHasPullbackFOfHasPullbacks
Presieve₀_1`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} 
(E : CategoryTheory.PreZeroHypercover X) (f : Y ⟶ X)   [E.presieve₀.HasPu…
· 使用定理 `CategoryTheory.Precoverage.ZeroHypercover.instHasPullbacksPresieve₀OfHas
Pullbacks`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (K : Categor
yTheory.Precoverage C) [K.HasPullbacks] {X Y : C}   (E : K.ZeroHypercov…
· 使用定理 `CategoryTheory.Precoverage.instHasPullbacksOfHasPullbacks`：∀ {C : Type u
} [inst : CategoryTheory.Category.{v, u} C] (J : CategoryTheory.Precoverage C)  
 [CategoryTheory.Limits.HasPullbacks C], J.HasP…
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MorphismProperty.iff_of_zeroHypercover_target`：∀ {C : Typ
e u} [inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.MorphismPrope
rty C}   {K : CategoryTheory.Precoverage C} [P.IsL…
· 使用定理 `CategoryTheory.IsPullback.instHasPullbackFst`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {P X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_
1 : CategoryTheory.Limits.HasPullb…
· 使用定理 `CategoryTheory.Limits.pullback.hom_ext`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categor
yTheory.Limits.HasPullback f…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `CategoryTheory.Limits.equalizerPullbackMapIso_inv_ι_fst`：equalizerPullba
ckMapIso_inv_ι_fst : (equalizerPullbackMapIso hf hg v).inv ≫ equalizer.ι _ _ ≫ p
ullback.fst _ _ = pullback.fst _ _ ≫ equalize…
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.Limits.equalizerPullbackMapIso_inv_ι_snd`：equalizerPullba
ckMapIso_inv_ι_snd : (equalizerPullbackMapIso hf hg v).inv ≫ equalizer.ι _ _ ≫ p
ullback.snd _ _ = pullback.snd _ _ ≫ pullback…
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `CategoryTheory.Limits.equalizer.ι_of_eq`：∀ {C : Type u} {X Y : C} [inst 
: CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y}   [inst_1 : CategoryTheory.Lim
its.HasEqualizer f g],   f = …
· 使用定理 `CategoryTheory.Limits.eq_of_epi_equalizer`：eq_of_epi_equalizer [HasEqual
izer f g] [Epi (equalizer.ι f g)] : f = g
· 使用定理 `CategoryTheory.instEffectiveEpiOfIsIso`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],  
 CategoryTheory.EffectiveEpi…

--- 原说明 ---
Let `J` be a precoverage for which isomorphisms are local at the target. Let
`f, g : X ⟶ Y` be two morphisms over `S` and `𝒰` a `J`-cover of `S`.
If for all `i`, the maps `X ×[S] Uᵢ ⟶ Y ×[S] Uᵢ` are equal, then
`f` and `g` are equal.
-/
lemma eq_of_zeroHypercover_target [HasEqualizers C] [HasPullbacks C] {X Y S : C} {f g : X ⟶ Y}
    {s : X ⟶ S} {t : Y ⟶ S} (hf : f ≫ t = s) (hg : g ≫ t = s) {J : Precoverage C}
    (𝒰 : Precoverage.ZeroHypercover.{w} J S) [J.IsStableUnderBaseChange]
    [(MorphismProperty.isomorphisms C).IsLocalAtTarget J]
    (H : ∀ i,
      pullback.map s (𝒰.f i) t (𝒰.f i) f (𝟙 (𝒰.X i)) (𝟙 S) (by simp [hf]) (by simp) =
        pullback.map s (𝒰.f i) t (𝒰.f i) g (𝟙 (𝒰.X i)) (𝟙 S) (by simp [hg]) (by simp)) :
    f = g := by
  suffices IsIso (equalizer.ι f g) from Limits.eq_of_epi_equalizer
  change MorphismProperty.isomorphisms C _
  rw [(MorphismProperty.isomorphisms C).iff_of_zeroHypercover_target (𝒰.pullback₁ s)]
  intro i
  have : pullback.snd (equalizer.ι f g) (pullback.fst s (𝒰.f i)) =
      (equalizerPullbackMapIso hf hg _).inv ≫ equalizer.ι _ _ := by
    ext <;> simp [pullback.condition]
  simpa [this] using equalizer.ι_of_eq (H i)

end CategoryTheory

