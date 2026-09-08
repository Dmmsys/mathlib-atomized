/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Sites.MorphismProperty
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Grothendieck topology defined by a morphism property

Given a multiplicative morphism property `P` that is stable under base change, we define the
associated (pre)topology on the category of schemes, where coverings are given
by jointly surjective families of morphisms satisfying `P`.

## Implementation details

The pretopology is obtained from the precoverage `AlgebraicGeometry.Scheme.precoverage` defined in
`Mathlib.AlgebraicGeometry.Sites.MorphismProperty`. The definition is postponed to this file,
because the former does not have `HasPullbacks Scheme`.
-/

@[expose] public section

universe v u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

/--
The pretopology on the category of schemes defined by covering families where the components
satisfy `P`.
-/
/-
**AlgebraicGeometry.Scheme.pretopology** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeome
try.Scheme`。
形式化陈述：pretopology (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange] 
[P.IsMultiplicative] : Pretopology Scheme.{u}
参数：P : MorphismProperty Scheme.{u}。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullbacks`：CategoryTheory.Limit
s.HasPullbacks AlgebraicGeometry.Scheme

--- 原说明 ---
The pretopology on the category of schemes defined by covering families where th
e components
satisfy `P`.
-/
def pretopology (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    [P.IsMultiplicative] : Pretopology Scheme.{u} :=
  (precoverage P).toPretopology

/-- The Grothendieck topology on the category of schemes induced by the pretopology defined by
`P`-covers. -/
/-
**AlgebraicGeometry.Scheme.grothendieckTopology** 是 Mathlib 中的一个缩写定义，位于命名空间 `Alg
ebraicGeometry.Scheme`。
形式化陈述：grothendieckTopology (P : MorphismProperty Scheme.{u}) : GrothendieckTopol
ogy Scheme.{u}
参数：P : MorphismProperty Scheme.{u}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Grothendieck topology on the category of schemes induced by the pretopology 
defined by
`P`-covers.
-/
abbrev grothendieckTopology (P : MorphismProperty Scheme.{u}) :
    GrothendieckTopology Scheme.{u} :=
  (precoverage P).toGrothendieck
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : jointlySurjectivePrecoverage.IsStableUnderBaseChange :=
  isStableUnderBaseChange_comap_jointlySurjectivePrecoverage _
    fun f g _ ↦ pullbackComparison_forget_surjective f g

/-- The pretopology on the category of schemes defined by jointly surjective families. -/
/-
**AlgebraicGeometry.Scheme.jointlySurjectivePretopology** 是 Mathlib 中的一个定义，位于命名空
间 `AlgebraicGeometry.Scheme`。
形式化陈述：jointlySurjectivePretopology : Pretopology Scheme.{u}
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullbacks`：CategoryTheory.Limit
s.HasPullbacks AlgebraicGeometry.Scheme
· 使用定理 `CategoryTheory.Precoverage.instHasIsosComap`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {D : Type u_1} [inst_1 : CategoryTheory.Category.{
v_1, u_1} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Types.instHasIsosJointlySurjectivePrecoverage`：CategoryTh
eory.Types.jointlySurjectivePrecoverage.HasIsos
· 使用定理 `AlgebraicGeometry.Scheme.instIsStableUnderBaseChangeJointlySurjectivePre
coverage`：AlgebraicGeometry.Scheme.jointlySurjectivePrecoverage.IsStableUnderBas
eChange
· 使用定理 `CategoryTheory.Precoverage.instIsStableUnderCompositionComap`：∀ {C : Typ
e u} [inst : CategoryTheory.Category.{v, u} C] {D : Type u_1} [inst_1 : Category
Theory.Category.{v_1, u_1} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Types.instIsStableUnderCompositionJointlySurjectivePrecov
erage`：CategoryTheory.Types.jointlySurjectivePrecoverage.IsStableUnderCompositio
n

--- 原说明 ---
The pretopology on the category of schemes defined by jointly surjective familie
s.
-/
def jointlySurjectivePretopology : Pretopology Scheme.{u} :=
  jointlySurjectivePrecoverage.toPretopology

variable {P : MorphismProperty Scheme.{u}}

@[grind ←]
/-
**AlgebraicGeometry.Scheme.Cover.mem_grothendieckTopology** 是 Mathlib 中的一个定理，位于命
名空间 `AlgebraicGeometry.Scheme.Cover`。
形式化陈述：∀ {P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme} {X : Alge
braicGeometry.Scheme}   (𝒰 : AlgebraicGeometry.Scheme.Cover (AlgebraicGeometry.S
cheme.precoverage P) X),   CategoryTheory.Sieve.ofArrows 𝒰.X 𝒰.f ∈ (AlgebraicGeo
metry.Scheme.grothendieckTopology P) X
参数：𝒰 : AlgebraicGeometry.Scheme.Cover (AlgebraicGeometry.Scheme.precoverage P) X
；AlgebraicGeometry.Scheme.grothendieckTopology P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Precoverage.generate_mem_toGrothendieck`：generate_mem_toG
rothendieck {X : C} {R : Presieve X} (hR : R in J X) : Sieve.generate R in J.toG
rothendieck X
· 使用定理 `CategoryTheory.Precoverage.ZeroHypercover.mem₀`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] {J : CategoryTheory.Precoverage C} {S : C}   (s
elf : J.ZeroHypercover S), self.pres…
-/
lemma Cover.mem_grothendieckTopology {X : Scheme.{u}} (𝒰 : X.Cover (precoverage P)) :
    Sieve.ofArrows 𝒰.X 𝒰.f ∈ grothendieckTopology P X :=
  Precoverage.generate_mem_toGrothendieck 𝒰.mem₀
/-
**AlgebraicGeometry.Scheme.bot_mem_grothendieckTopology** 是 Mathlib 中的一个引理，位于命名空
间 `AlgebraicGeometry.Scheme`。
形式化陈述：bot_mem_grothendieckTopology (X : Scheme.{u}) [IsEmpty X] : ⊥ in grothendi
eckTopology P X
参数：X : Scheme.{u}。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Sieve.generate_bot`：generate_bot : generate (⊥ : Presieve
 X) = ⊥
· 使用引理 `CategoryTheory.Precoverage.generate_mem_toGrothendieck`：generate_mem_toG
rothendieck {X : C} {R : Presieve X} (hR : R in J X) : Sieve.generate R in J.toG
rothendieck X
· 使用引理 `AlgebraicGeometry.Scheme.bot_mem_precoverage`：bot_mem_precoverage (X : S
cheme.{u}) [IsEmpty X] : ⊥ in Scheme.precoverage P X
-/
lemma bot_mem_grothendieckTopology (X : Scheme.{u}) [IsEmpty X] : ⊥ ∈ grothendieckTopology P X := by
  rw [← Sieve.generate_bot]
  exact Precoverage.generate_mem_toGrothendieck (bot_mem_precoverage _ X)

variable [P.IsStableUnderBaseChange] [P.IsMultiplicative]

@[grind ←]
/-
**AlgebraicGeometry.Scheme.Cover.mem_pretopology** 是 Mathlib 中的一个定理，位于命名空间 `Alge
braicGeometry.Scheme.Cover`。
形式化陈述：∀ {P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme} [inst : P
.IsStableUnderBaseChange]   [inst_1 : P.IsMultiplicative] {X : AlgebraicGeometry
.Scheme}   {𝒰 : AlgebraicGeometry.Scheme.Cover (AlgebraicGeometry.Scheme.precove
rage P) X},   CategoryTheory.Presieve.ofArrows 𝒰.X 𝒰.f ∈ (AlgebraicGeometry.Sche
me.pretopology P).coverings X
参数：AlgebraicGeometry.Scheme.precoverage P；AlgebraicGeometry.Scheme.pretopology P
。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Precoverage.ZeroHypercover.mem₀`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] {J : CategoryTheory.Precoverage C} {S : C}   (s
elf : J.ZeroHypercover S), self.pres…
-/
lemma Cover.mem_pretopology {X : Scheme.{u}} {𝒰 : X.Cover (precoverage P)} :
    Presieve.ofArrows 𝒰.X 𝒰.f ∈ pretopology P X :=
  𝒰.mem₀
/-
**AlgebraicGeometry.Scheme.mem_pretopology_iff** 是 Mathlib 中的一个引理，位于命名空间 `Algebr
aicGeometry.Scheme`。
形式化陈述：mem_pretopology_iff {X : Scheme.{u}} {R : Presieve X} : R in pretopology P
 X ↔ exists (𝒰 : Cover.{u + 1} (precoverage P) X), R = Presieve.ofArrows 𝒰.X 𝒰.f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Precoverage.mem_iff_exists_zeroHypercover`：mem_iff_exists
_zeroHypercover {X : C} {R : Presieve X} : R in J X ↔ exists (𝒰 : ZeroHypercover
.{max u v} J X), R = Presieve.ofArrows 𝒰.X 𝒰.f
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullbacks`：CategoryTheory.Limit
s.HasPullbacks AlgebraicGeometry.Scheme
-/
lemma mem_pretopology_iff {X : Scheme.{u}} {R : Presieve X} :
    R ∈ pretopology P X ↔ ∃ (𝒰 : Cover.{u + 1} (precoverage P) X),
    R = Presieve.ofArrows 𝒰.X 𝒰.f :=
  Precoverage.mem_iff_exists_zeroHypercover

alias ⟨exists_cover_of_mem_pretopology, _⟩ := mem_pretopology_iff
/-
**AlgebraicGeometry.Scheme.mem_grothendieckTopology_iff** 是 Mathlib 中的一个引理，位于命名空
间 `AlgebraicGeometry.Scheme`。
形式化陈述：mem_grothendieckTopology_iff {X : Scheme.{u}} {S : Sieve X} : S in grothen
dieckTopology P X ↔ exists (𝒰 : Cover.{u} (precoverage P) X), Presieve.ofArrows 
𝒰.X 𝒰.f <= S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.instIsStableUnderCompositionPrecoverageOfIsStab
leUnderComposition`：∀ (P : CategoryTheory.MorphismProperty AlgebraicGeometry.Sch
eme) [P.IsStableUnderComposition],   (AlgebraicGeometry.Scheme.precoverage P).Is
…
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toIsStableUnderComposit
ion`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheor
y.MorphismProperty C}   [self : W.IsMultiplicative], W.IsStableUn…
· 使用定理 `AlgebraicGeometry.Scheme.instIsStableUnderBaseChangePrecoverageOfIsJoint
lySurjectivePreservingOfIsStableUnderBaseChange`：∀ (P : CategoryTheory.MorphismP
roperty AlgebraicGeometry.Scheme)   [AlgebraicGeometry.Scheme.IsJointlySurjectiv
ePreserving P] [P.IsStableUnd…
· 使用定理 `AlgebraicGeometry.Scheme.isJointlySurjectivePreserving`：∀ (P : CategoryT
heory.MorphismProperty AlgebraicGeometry.Scheme),   AlgebraicGeometry.Scheme.IsJ
ointlySurjectivePreserving P
· 使用定理 `AlgebraicGeometry.Scheme.instHasPullbacksPrecoverageOfHasPullbacks`：∀ (P
 : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme) [P.HasPullbacks],  
 (AlgebraicGeometry.Scheme.precoverage P).HasPullbacks
· 使用定理 `CategoryTheory.MorphismProperty.instHasPullbacksOfHasPullbacks`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheory.MorphismPro
perty C)   [CategoryTheory.Limits.HasPullbacks C], P…
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullbacks`：CategoryTheory.Limit
s.HasPullbacks AlgebraicGeometry.Scheme
· 使用定理 `AlgebraicGeometry.Scheme.instHasIsosPrecoverageOfContainsIdentitiesOfRes
pectsIso`：∀ (P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme) [P.Co
ntainsIdentities] [P.RespectsIso],   (AlgebraicGeometry.Scheme.precove…
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toContainsIdentities`：∀
 {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheory.Morp
hismProperty C}   [self : W.IsMultiplicative], W.ContainsId…
· 使用定理 `CategoryTheory.MorphismProperty.instRespectsOfRespectsLeftOfRespectsRigh
t`：∀ {C : Type u} [inst : CategoryTheory.CategoryStruct.{v, u} C] (P Q : Categor
yTheory.MorphismProperty C)   [P.RespectsLeft Q] [P.RespectsRig…
· 使用定理 `CategoryTheory.MorphismProperty.Respects.toRespectsLeft`：∀ {C : Type u} 
{inst : CategoryTheory.CategoryStruct.{v, u} C} {P Q : CategoryTheory.MorphismPr
operty C}   [self : P.Respects Q], P.Respects…
· 使用定理 `CategoryTheory.MorphismProperty.IsStableUnderBaseChange.respectsIso`：∀ {
C : Type u} [inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.Morphi
smProperty C}   [P.IsStableUnderBaseChange], P.RespectsIs…
· 使用定理 `CategoryTheory.MorphismProperty.Respects.toRespectsRight`：∀ {C : Type u}
 {inst : CategoryTheory.CategoryStruct.{v, u} C} {P Q : CategoryTheory.MorphismP
roperty C}   [self : P.Respects Q], P.Respects…
· 使用引理 `CategoryTheory.Precoverage.mem_iff_exists_zeroHypercover`：mem_iff_exists
_zeroHypercover {X : C} {R : Presieve X} : R in J X ↔ exists (𝒰 : ZeroHypercover
.{max u v} J X), R = Presieve.ofArrows 𝒰.X 𝒰.f
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `AlgebraicGeometry.Scheme.instJointlySurjectivePrecoverage`：∀ {P : Catego
ryTheory.MorphismProperty AlgebraicGeometry.Scheme},   AlgebraicGeometry.Scheme.
JointlySurjective (AlgebraicGeometry.Scheme.pre…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.Scheme.Cover.mem_pretopology`：∀ {P : CategoryTheory.Mo
rphismProperty AlgebraicGeometry.Scheme} [inst : P.IsStableUnderBaseChange]   [i
nst_1 : P.IsMultiplicative] {X : Alg…
-/
lemma mem_grothendieckTopology_iff {X : Scheme.{u}} {S : Sieve X} :
    S ∈ grothendieckTopology P X ↔
      ∃ (𝒰 : Cover.{u} (precoverage P) X), Presieve.ofArrows 𝒰.X 𝒰.f ≤ S := by
  simp_rw [grothendieckTopology, Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition]
  refine ⟨fun ⟨R, hR, hle⟩ ↦ ?_, fun ⟨𝒰, hle⟩ ↦ ⟨.ofArrows 𝒰.X 𝒰.f, 𝒰.mem_pretopology, hle⟩⟩
  rw [Precoverage.mem_iff_exists_zeroHypercover] at hR
  obtain ⟨(𝒰 : Scheme.Cover _ _), rfl⟩ := hR
  use 𝒰.ulift, le_trans (fun Y g ⟨i⟩ ↦ .mk _) hle

alias ⟨exists_cover_of_mem_grothendieckTopology, _⟩ := mem_grothendieckTopology_iff

section

/-- The jointly surjective topology on `Scheme` is defined by the same condition as the jointly
surjective pretopology. -/
/-
**AlgebraicGeometry.Scheme.jointlySurjectiveTopology** 是 Mathlib 中的一个定义，位于命名空间 `
AlgebraicGeometry.Scheme`。
形式化陈述：jointlySurjectiveTopology : GrothendieckTopology Scheme.{u}
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullbacks`：CategoryTheory.Limit
s.HasPullbacks AlgebraicGeometry.Scheme

--- 原说明 ---
The jointly surjective topology on `Scheme` is defined by the same condition as 
the jointly
surjective pretopology.
-/
def jointlySurjectiveTopology : GrothendieckTopology Scheme.{u} :=
  jointlySurjectivePretopology.toGrothendieck.copy
    (fun X ↦ {s | ↑s ∈ jointlySurjectivePretopology X}) <|
    funext fun _ ↦ Set.ext fun s ↦
      ⟨fun ⟨_, hp, hps⟩ x ↦ let ⟨Y, u, hu, hmem⟩ := hp x;
        ⟨Y, u, Presieve.map_monotone hps _ _ hu, hmem⟩,
      fun hs ↦ ⟨s, hs, le_rfl⟩⟩
/-
**AlgebraicGeometry.Scheme.mem_jointlySurjectiveTopology_iff_jointlySurjectivePr
etopology** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.Scheme`。
形式化陈述：mem_jointlySurjectiveTopology_iff_jointlySurjectivePretopology {X : Scheme
.{u}} {s : Sieve X} : s in jointlySurjectiveTopology X ↔ ↑s in jointlySurjective
Pretopology X
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_jointlySurjectiveTopology_iff_jointlySurjectivePretopology
    {X : Scheme.{u}} {s : Sieve X} :
    s ∈ jointlySurjectiveTopology X ↔ ↑s ∈ jointlySurjectivePretopology X :=
  Iff.rfl
/-
**AlgebraicGeometry.Scheme.jointlySurjectiveTopology_eq_toGrothendieck_jointlySu
rjectivePretopology** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry.Scheme`。
形式化陈述：jointlySurjectiveTopology_eq_toGrothendieck_jointlySurjectivePretopology :
 jointlySurjectiveTopology.{u} = jointlySurjectivePretopology.toGrothendieck
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.copy_eq`：copy_eq {J : GrothendieckTo
pology C} {s : forall X : C, Set (Sieve X)} {h : J.sieves = s} : J.copy s h = J
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullbacks`：CategoryTheory.Limit
s.HasPullbacks AlgebraicGeometry.Scheme
-/
lemma jointlySurjectiveTopology_eq_toGrothendieck_jointlySurjectivePretopology :
    jointlySurjectiveTopology.{u} = jointlySurjectivePretopology.toGrothendieck :=
  GrothendieckTopology.copy_eq

variable (P)

/--
The pretopology defined by `P`-covers agrees with the
intersection of the pretopology of surjective families with the pretopology defined by `P`.
-/
/-
**AlgebraicGeometry.Scheme.pretopology_eq_inf** 是 Mathlib 中的一个引理，位于命名空间 `Algebra
icGeometry.Scheme`。
形式化陈述：pretopology_eq_inf : pretopology P = jointlySurjectivePretopology ⊓ P.pret
opology
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullbacks`：CategoryTheory.Limit
s.HasPullbacks AlgebraicGeometry.Scheme

--- 原说明 ---
The pretopology defined by `P`-covers agrees with the
intersection of the pretopology of surjective families with the pretopology defi
ned by `P`.
-/
lemma pretopology_eq_inf : pretopology P = jointlySurjectivePretopology ⊓ P.pretopology := rfl

/--
The Grothendieck topology defined by `P`-covers agrees with the Grothendieck
topology induced by the intersection of the pretopology of surjective families with
the pretopology defined by `P`.
-/
/-
**AlgebraicGeometry.Scheme.grothendieckTopology_eq_inf** 是 Mathlib 中的一个引理，位于命名空间
 `AlgebraicGeometry.Scheme`。
形式化陈述：grothendieckTopology_eq_inf : grothendieckTopology P = (jointlySurjectiveP
retopology ⊓ P.pretopology).toGrothendieck
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullbacks`：CategoryTheory.Limit
s.HasPullbacks AlgebraicGeometry.Scheme
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.grothendieckTopology.eq_1`：∀ (P : CategoryTheor
y.MorphismProperty AlgebraicGeometry.Scheme),   AlgebraicGeometry.Scheme.grothen
dieckTopology P = (AlgebraicGeometry.Sch…
· 使用定理 `AlgebraicGeometry.Scheme.instHasIsosPrecoverageOfContainsIdentitiesOfRes
pectsIso`：∀ (P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme) [P.Co
ntainsIdentities] [P.RespectsIso],   (AlgebraicGeometry.Scheme.precove…
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toContainsIdentities`：∀
 {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheory.Morp
hismProperty C}   [self : W.IsMultiplicative], W.ContainsId…
· 使用定理 `CategoryTheory.MorphismProperty.instRespectsOfRespectsLeftOfRespectsRigh
t`：∀ {C : Type u} [inst : CategoryTheory.CategoryStruct.{v, u} C] (P Q : Categor
yTheory.MorphismProperty C)   [P.RespectsLeft Q] [P.RespectsRig…
· 使用定理 `CategoryTheory.MorphismProperty.Respects.toRespectsLeft`：∀ {C : Type u} 
{inst : CategoryTheory.CategoryStruct.{v, u} C} {P Q : CategoryTheory.MorphismPr
operty C}   [self : P.Respects Q], P.Respects…
· 使用定理 `CategoryTheory.MorphismProperty.IsStableUnderBaseChange.respectsIso`：∀ {
C : Type u} [inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.Morphi
smProperty C}   [P.IsStableUnderBaseChange], P.RespectsIs…
· 使用定理 `CategoryTheory.MorphismProperty.Respects.toRespectsRight`：∀ {C : Type u}
 {inst : CategoryTheory.CategoryStruct.{v, u} C} {P Q : CategoryTheory.MorphismP
roperty C}   [self : P.Respects Q], P.Respects…
· 使用定理 `AlgebraicGeometry.Scheme.instIsStableUnderBaseChangePrecoverageOfIsJoint
lySurjectivePreservingOfIsStableUnderBaseChange`：∀ (P : CategoryTheory.MorphismP
roperty AlgebraicGeometry.Scheme)   [AlgebraicGeometry.Scheme.IsJointlySurjectiv
ePreserving P] [P.IsStableUnd…
· 使用定理 `AlgebraicGeometry.Scheme.isJointlySurjectivePreserving`：∀ (P : CategoryT
heory.MorphismProperty AlgebraicGeometry.Scheme),   AlgebraicGeometry.Scheme.IsJ
ointlySurjectivePreserving P
· 使用定理 `AlgebraicGeometry.Scheme.instIsStableUnderCompositionPrecoverageOfIsStab
leUnderComposition`：∀ (P : CategoryTheory.MorphismProperty AlgebraicGeometry.Sch
eme) [P.IsStableUnderComposition],   (AlgebraicGeometry.Scheme.precoverage P).Is
…
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toIsStableUnderComposit
ion`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheor
y.MorphismProperty C}   [self : W.IsMultiplicative], W.IsStableUn…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Precoverage.toGrothendieck_toPretopology_eq_toGrothendiec
k`：toGrothendieck_toPretopology_eq_toGrothendieck [IsStableUnderComposition J] [
IsStableUnderBaseChange J] [Limits.HasPullbacks C] [HasIsos J] …

--- 原说明 ---
The Grothendieck topology defined by `P`-covers agrees with the Grothendieck
topology induced by the intersection of the pretopology of surjective families w
ith
the pretopology defined by `P`.
-/
lemma grothendieckTopology_eq_inf :
    grothendieckTopology P = (jointlySurjectivePretopology ⊓ P.pretopology).toGrothendieck := by
  rw [grothendieckTopology, ← Precoverage.toGrothendieck_toPretopology_eq_toGrothendieck]
  rfl

end

section

variable {P Q : MorphismProperty Scheme.{u}}

/-
**AlgebraicGeometry.Scheme.grothendieckTopology_monotone** 是 Mathlib 中的一个引理，位于命名
空间 `AlgebraicGeometry.Scheme`。
形式化陈述：grothendieckTopology_monotone (hPQ : P <= Q) : grothendieckTopology P <= g
rothendieckTopology Q
参数：hPQ : P <= Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Precoverage.toGrothendieck_mono`：∀ {C : Type u_3} [inst :
 CategoryTheory.Category.{u_2, u_3} C] {J K : CategoryTheory.Precoverage C},   J
 ≤ K → J.toGrothendieck ≤ K.toGrothe…
· 使用引理 `AlgebraicGeometry.Scheme.precoverage_mono`：precoverage_mono {P Q : Morph
ismProperty Scheme.{u}} (h : P <= Q) : precoverage P <= precoverage Q
-/
lemma grothendieckTopology_monotone (hPQ : P ≤ Q) :
    grothendieckTopology P ≤ grothendieckTopology Q :=
  Precoverage.toGrothendieck_mono (precoverage_mono hPQ)

variable [P.IsMultiplicative] [P.IsStableUnderBaseChange]
  [Q.IsMultiplicative] [Q.IsStableUnderBaseChange]
/-
**AlgebraicGeometry.Scheme.pretopology_monotone** 是 Mathlib 中的一个引理，位于命名空间 `Algeb
raicGeometry.Scheme`。
形式化陈述：pretopology_monotone (hPQ : P <= Q) : pretopology P <= pretopology Q
参数：hPQ : P <= Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.Scheme.precoverage_mono`：precoverage_mono {P Q : Morph
ismProperty Scheme.{u}} (h : P <= Q) : precoverage P <= precoverage Q
-/
lemma pretopology_monotone (hPQ : P ≤ Q) : pretopology P ≤ pretopology Q :=
  precoverage_mono hPQ

end

end AlgebraicGeometry.Scheme

