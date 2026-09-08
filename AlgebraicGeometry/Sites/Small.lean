/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Cover.Over
public import Mathlib.AlgebraicGeometry.Sites.Pretopology
public import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology
public import Mathlib.CategoryTheory.Sites.Over

/-!
# Small sites

In this file we define the small sites associated to morphism properties and give
generating pretopologies.

## Main definitions

- `AlgebraicGeometry.Scheme.overGrothendieckTopology`: the Grothendieck topology on `Over S`
  obtained by localizing the topology on `Scheme` induced by `P` at `S`.
- `AlgebraicGeometry.Scheme.overPretopology`: the pretopology on `Over S` defined by
  `P`-coverings of `S`-schemes. The induced topology agrees with
  `AlgebraicGeometry.Scheme.overGrothendieckTopology`.
- `AlgebraicGeometry.Scheme.smallGrothendieckTopology`: the by the inclusion
  `P.Over ⊤ S ⥤ Over S` induced topology on `P.Over ⊤ S`.
- `AlgebraicGeometry.Scheme.smallPretopology`: the pretopology on `P.Over ⊤ S` defined by
  `P`-coverings of `S`-schemes with `P`. The induced topology agrees
  with `AlgebraicGeometry.Scheme.smallGrothendieckTopology`.

-/

@[expose] public section

universe v u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

variable {P Q : MorphismProperty Scheme.{u}} {S : Scheme.{u}}
  [P.IsStableUnderBaseChange]

/-- The presieve defined by a `P`-cover of `S`-schemes. -/
/-
**AlgebraicGeometry.Scheme.Cover.toPresieveOver** 是 Mathlib 中的一个定义，位于命名空间 `Algeb
raicGeometry.Scheme.Cover`。
形式化陈述：{P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme} →   {S : Al
gebraicGeometry.Scheme} →     [inst : P.IsStableUnderBaseChange] →       {X : Ca
tegoryTheory.Over S} →         (𝒰 : AlgebraicGeometry.Scheme.Cover (AlgebraicGeo
metry.Scheme.precoverage P) X.left) →           [AlgebraicGeometry.Scheme.Cover.
Over S 𝒰] → CategoryTheory.Presieve X
参数：𝒰 : AlgebraicGeometry.Scheme.Cover (AlgebraicGeometry.Scheme.precoverage P) X
.left。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.isJointlySurjectivePreserving`：∀ (P : CategoryT
heory.MorphismProperty AlgebraicGeometry.Scheme),   AlgebraicGeometry.Scheme.IsJ
ointlySurjectivePreserving P

--- 原说明 ---
The presieve defined by a `P`-cover of `S`-schemes.
-/
def Cover.toPresieveOver {X : Over S} (𝒰 : Cover.{u} (precoverage P) X.left) [𝒰.Over S] :
    Presieve X :=
  Presieve.ofArrows (fun i ↦ (𝒰.X i).asOver S) (fun i ↦ (𝒰.f i).asOver S)

set_option backward.isDefEq.respectTransparency.types false in
/-- The presieve defined by a `P`-cover of `S`-schemes with `Q`. -/
/-
**AlgebraicGeometry.Scheme.Cover.toPresieveOverProp** 是 Mathlib 中的一个定义，位于命名空间 `A
lgebraicGeometry.Scheme.Cover`。
形式化陈述：{P Q : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme} →   {S : 
AlgebraicGeometry.Scheme} →     [inst : P.IsStableUnderBaseChange] →       {X : 
Q.Over ⊤ S} →         (𝒰 : AlgebraicGeometry.Scheme.Cover (AlgebraicGeometry.Sch
eme.precoverage P) X.left) →           [inst_1 : AlgebraicGeometry.Scheme.Cover.
Over S 𝒰] → (∀ (j : 𝒰.I₀), Q (𝒰.X j ↘ S)) → CategoryTheory.Presieve X
参数：𝒰 : AlgebraicGeometry.Scheme.Cover (AlgebraicGeometry.Scheme.precoverage P) X
.left；∀ (j : 𝒰.I₀), Q (𝒰.X j ↘ S)。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.isJointlySurjectivePreserving`：∀ (P : CategoryT
heory.MorphismProperty AlgebraicGeometry.Scheme),   AlgebraicGeometry.Scheme.IsJ
ointlySurjectivePreserving P
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.instTop`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C], ⊤.IsMultiplicative

--- 原说明 ---
The presieve defined by a `P`-cover of `S`-schemes with `Q`.
-/
def Cover.toPresieveOverProp {X : Q.Over ⊤ S} (𝒰 : Cover.{u} (precoverage P) X.left) [𝒰.Over S]
    (h : ∀ j, Q (𝒰.X j ↘ S)) : Presieve X :=
  Presieve.ofArrows (fun i ↦ (𝒰.X i).asOverProp S (h i)) (fun i ↦ (𝒰.f i).asOverProp S)

set_option backward.defeqAttrib.useBackward true in
/-
**AlgebraicGeometry.Scheme.Cover.overEquiv_generate_toPresieveOver_eq_ofArrows**
 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.Scheme.Cover`。
形式化陈述：∀ {P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme} {S : Alge
braicGeometry.Scheme}   [inst : P.IsStableUnderBaseChange] {X : CategoryTheory.O
ver S}   (𝒰 : AlgebraicGeometry.Scheme.Cover (AlgebraicGeometry.Scheme.precovera
ge P) X.left)   [inst_1 : AlgebraicGeometry.Scheme.Cover.Over S 𝒰],   (CategoryT
heory.Sieve.overEquiv X) (CategoryTheory.Sieve.generate 𝒰.toPresieveOver) =     
CategoryTheory.Sieve.ofArrows 𝒰.X 𝒰.f
参数：𝒰 : AlgebraicGeometry.Scheme.Cover (AlgebraicGeometry.Scheme.precoverage P) X
.left；CategoryTheory.Sieve.overEquiv X；CategoryTheory.Sieve.generate 𝒰.toPresiev
eOver。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.isJointlySurjectivePreserving`：∀ (P : CategoryT
heory.MorphismProperty AlgebraicGeometry.Scheme),   AlgebraicGeometry.Scheme.IsJ
ointlySurjectivePreserving P
· 使用定理 `CategoryTheory.Sieve.ext`：∀ {C : Type u₁} [inst : CategoryTheory.Categor
y.{v₁, u₁} C] {X : C} {R S : CategoryTheory.Sieve X},   (∀ ⦃Y : C⦄ (f : Y ⟶ X), 
R.arrows f ↔ S…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用引理 `CategoryTheory.comp_over`：comp_over [OverClass X S] [OverClass Y S] [Hom
IsOver f S] : f ≫ Y ↘ S = X ↘ S
· 使用定理 `AlgebraicGeometry.Scheme.Cover.Over.isOver_map`：∀ {S : AlgebraicGeometry
.Scheme} {P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme}   {inst 
: P.IsStableUnderBaseChange} {inst_1…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Over.OverMorphism.ext`：∀ {T : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} T] {X : T} {U V : CategoryTheory.Over X} {f g : U ⟶ V},  
 CategoryTheory.Over.Hom.l…
-/
lemma Cover.overEquiv_generate_toPresieveOver_eq_ofArrows {X : Over S}
    (𝒰 : Cover.{u} (precoverage P) X.left)
    [𝒰.Over S] : Sieve.overEquiv X (Sieve.generate 𝒰.toPresieveOver) =
      Sieve.ofArrows 𝒰.X 𝒰.f := by
  ext V f
  simp only [Sieve.overEquiv_iff, Sieve.generate_apply]
  constructor
  · rintro ⟨U, h, g, ⟨k⟩, hcomp⟩
    exact ⟨𝒰.X k, h.left, 𝒰.f k, ⟨k⟩, congrArg CommaMorphism.left hcomp⟩
  · rintro ⟨U, h, g, ⟨k⟩, hcomp⟩
    have : 𝒰.f k ≫ X.hom = 𝒰.X k ↘ S := comp_over (𝒰.f k) S
    refine ⟨(𝒰.X k).asOver S, Over.homMk h (by simp [← hcomp, this]), (𝒰.f k).asOver S, ⟨k⟩, ?_⟩
    ext : 1
    simpa
/-
**AlgebraicGeometry.Scheme.Cover.toPresieveOver_le_arrows_iff** 是 Mathlib 中的一个定理
，位于命名空间 `AlgebraicGeometry.Scheme.Cover`。
形式化陈述：∀ {P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme} {S : Alge
braicGeometry.Scheme}   [inst : P.IsStableUnderBaseChange] {X : CategoryTheory.O
ver S} (R : CategoryTheory.Sieve X)   (𝒰 : AlgebraicGeometry.Scheme.Cover (Algeb
raicGeometry.Scheme.precoverage P) X.left)   [inst_1 : AlgebraicGeometry.Scheme.
Cover.Over S 𝒰],   𝒰.toPresieveOver ≤ R.arrows ↔ CategoryTheory.Presieve.ofArrow
s 𝒰.X 𝒰.f ≤ ((CategoryTheory.Sieve.overEquiv X) R).arrows
参数：R : CategoryTheory.Sieve X；𝒰 : AlgebraicGeometry.Scheme.Cover (AlgebraicGeome
try.Scheme.precoverage P) X.left；(CategoryTheory.Sieve.overEquiv X) R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.isJointlySurjectivePreserving`：∀ (P : CategoryT
heory.MorphismProperty AlgebraicGeometry.Scheme),   AlgebraicGeometry.Scheme.IsJ
ointlySurjectivePreserving P
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `GaloisConnection.le_iff_le`：le_iff_le {a : α} {b : β} : l a <= b ↔ a <= 
u b
· 使用定理 `GaloisInsertion.gc`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] 
[inst_1 : Preorder β] {l : α → β} {u : β → α}   (self : GaloisInsertion l u), Ga
loisConn…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `RelIso.map_rel_iff`：map_rel_iff (f : r ≃r s) {a b} : s (f a) (f b) ↔ r a
 b
· 使用定理 `AlgebraicGeometry.Scheme.Cover.overEquiv_generate_toPresieveOver_eq_ofAr
rows`：∀ {P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme} {S : Alge
braicGeometry.Scheme}   [inst : P.IsStableUnderBaseChange] {X : Ca…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma Cover.toPresieveOver_le_arrows_iff {X : Over S} (R : Sieve X)
    (𝒰 : Cover.{u} (precoverage P) X.left) [𝒰.Over S] :
    𝒰.toPresieveOver ≤ R.arrows ↔
      Presieve.ofArrows 𝒰.X 𝒰.f ≤ (Sieve.overEquiv X R).arrows := by
  simp_rw [← Sieve.giGenerate.gc.le_iff_le, ← (Sieve.overEquiv X).map_rel_iff]
  rw [overEquiv_generate_toPresieveOver_eq_ofArrows]

variable [P.IsMultiplicative] [P.RespectsIso]

variable (P Q S)

set_option backward.isDefEq.respectTransparency false in
/-- The pretopology on `Over S` induced by `P` where coverings are given by `P`-covers
of `S`-schemes. -/
/-
**AlgebraicGeometry.Scheme.overPretopology** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicG
eometry.Scheme`。
形式化陈述：overPretopology : Pretopology (Over S) where coverings Y
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Over.instHasPullbacks`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {B : C} [CategoryTheory.Limits.HasPullbacks C],   Categor
yTheory.Limits.HasPullback…
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullbacks`：CategoryTheory.Limit
s.HasPullbacks AlgebraicGeometry.Scheme
· 使用定理 `AlgebraicGeometry.Scheme.isJointlySurjectivePreserving`：∀ (P : CategoryT
heory.MorphismProperty AlgebraicGeometry.Scheme),   AlgebraicGeometry.Scheme.IsJ
ointlySurjectivePreserving P

--- 原说明 ---
The pretopology on `Over S` induced by `P` where coverings are given by `P`-cove
rs
of `S`-schemes.
-/
def overPretopology : Pretopology (Over S) where
  coverings Y := {R | ∃ (𝒰 : Cover.{u} (precoverage P) Y.left) (_ : 𝒰.Over S), R = 𝒰.toPresieveOver}
  has_isos {X Y} f _ := ⟨coverOfIsIso f.left, inferInstance, (Presieve.ofArrows_pUnit _).symm⟩
  pullbacks := by
    rintro Y X f _ ⟨𝒰, h, rfl⟩
    refine ⟨𝒰.pullbackCoverOver' S f.left, inferInstance, ?_⟩
    simpa [Cover.toPresieveOver] using!
      (Presieve.ofArrows_pullback f (fun i ↦ (𝒰.X i).asOver S) (fun i ↦ (𝒰.f i).asOver S)).symm
  transitive := by
    rintro X _ T ⟨𝒰, h, rfl⟩ H
    choose V h hV using H
    refine ⟨𝒰.bind (fun j => V ((𝒰.f j).asOver S) ⟨j⟩), inferInstance, ?_⟩
    convert!
      Presieve.ofArrows_bind _ (fun j ↦ (𝒰.f j).asOver S) _ (fun Y f H j ↦ ((V f H).X j).asOver S)
        (fun Y f H j ↦ ((V f H).f j).asOver S)
    apply hV

/-- The topology on `Over S` induced from the topology on `Scheme` defined by `P`.
This agrees with the topology induced by `S.overPretopology P`, see
`AlgebraicGeometry.Scheme.overGrothendieckTopology_eq_toGrothendieck_overPretopology`. -/
/-
**AlgebraicGeometry.Scheme.overGrothendieckTopology** 是 Mathlib 中的一个缩写定义，位于命名空间 
`AlgebraicGeometry.Scheme`。
形式化陈述：overGrothendieckTopology : GrothendieckTopology (Over S)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The topology on `Over S` induced from the topology on `Scheme` defined by `P`.
This agrees with the topology induced by `S.overPretopology P`, see
`AlgebraicGeometry.Scheme.overGrothendieckTopology_eq_toGrothendieck_overPretopo
logy`.
-/
abbrev overGrothendieckTopology : GrothendieckTopology (Over S) :=
  (Scheme.grothendieckTopology P).over S
/-
**AlgebraicGeometry.Scheme.overGrothendieckTopology_eq_toGrothendieck_overPretop
ology** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry.Scheme`。
形式化陈述：overGrothendieckTopology_eq_toGrothendieck_overPretopology : S.overGrothen
dieckTopology P = (S.overPretopology P).toGrothendieck
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.ext`：ext {J₁ J₂ : GrothendieckTopolo
gy C} (h : (J₁ : forall X : C, Set (Sieve X)) = J₂) : J₁ = J₂
· 使用定理 `CategoryTheory.Over.instHasPullbacks`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {B : C} [CategoryTheory.Limits.HasPullbacks C],   Categor
yTheory.Limits.HasPullback…
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullbacks`：CategoryTheory.Limit
s.HasPullbacks AlgebraicGeometry.Scheme
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.GrothendieckTopology.mem_over_iff`：mem_over_iff {X : C} {
Y : Over X} (S : Sieve Y) : S in (J.over X) Y ↔ Sieve.overEquiv _ S in J Y.left
· 使用定理 `AlgebraicGeometry.Scheme.exists_cover_of_mem_grothendieckTopology`：∀ {P 
: CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme} [P.IsStableUnderBase
Change] [P.IsMultiplicative]   {X : AlgebraicGeometry.S…
· 使用定理 `AlgebraicGeometry.Scheme.isJointlySurjectivePreserving`：∀ (P : CategoryT
heory.MorphismProperty AlgebraicGeometry.Scheme),   AlgebraicGeometry.Scheme.IsJ
ointlySurjectivePreserving P
· 使用定理 `AlgebraicGeometry.Scheme.Cover.toPresieveOver_le_arrows_iff`：∀ {P : Cate
goryTheory.MorphismProperty AlgebraicGeometry.Scheme} {S : AlgebraicGeometry.Sch
eme}   [inst : P.IsStableUnderBaseChange] {X : Ca…
· 使用引理 `AlgebraicGeometry.Scheme.mem_grothendieckTopology_iff`：mem_grothendieckT
opology_iff {X : Scheme.{u}} {S : Sieve X} : S in grothendieckTopology P X ↔ exi
sts (𝒰 : Cover.{u} (precoverage P) X), Pres…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma overGrothendieckTopology_eq_toGrothendieck_overPretopology :
    S.overGrothendieckTopology P = (S.overPretopology P).toGrothendieck := by
  ext X R
  rw [GrothendieckTopology.mem_over_iff]
  constructor
  · intro hR
    obtain ⟨𝒰, hle⟩ := exists_cover_of_mem_grothendieckTopology hR
    rw [mem_grothendieckTopology_iff] at hR
    let (i : 𝒰.I₀) : (𝒰.X i).Over S := { hom := 𝒰.f i ≫ X.hom }
    let : 𝒰.Over S :=
      { over := inferInstance
        isOver_map := fun i ↦ ⟨rfl⟩ }
    use 𝒰.toPresieveOver, ⟨𝒰, inferInstance, rfl⟩
    rwa [Cover.toPresieveOver_le_arrows_iff]
  · rintro ⟨T, ⟨𝒰, h, rfl⟩, hT⟩
    rw [mem_grothendieckTopology_iff]
    use 𝒰
    rwa [Cover.toPresieveOver_le_arrows_iff] at hT

variable {S}
/-
**AlgebraicGeometry.Scheme.mem_overGrothendieckTopology** 是 Mathlib 中的一个引理，位于命名空
间 `AlgebraicGeometry.Scheme`。
形式化陈述：mem_overGrothendieckTopology (X : Over S) (R : Sieve X) : R in S.overGroth
endieckTopology P X ↔ exists (𝒰 : Cover.{u} (precoverage P) X.left) (_ : 𝒰.Over 
S), 𝒰.toPresieveOver <= R.arrows
参数：X : Over S；R : Sieve X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.isJointlySurjectivePreserving`：∀ (P : CategoryT
heory.MorphismProperty AlgebraicGeometry.Scheme),   AlgebraicGeometry.Scheme.IsJ
ointlySurjectivePreserving P
· 使用定理 `CategoryTheory.Over.instHasPullbacks`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {B : C} [CategoryTheory.Limits.HasPullbacks C],   Categor
yTheory.Limits.HasPullback…
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullbacks`：CategoryTheory.Limit
s.HasPullbacks AlgebraicGeometry.Scheme
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.Scheme.overGrothendieckTopology_eq_toGrothendieck_over
Pretopology`：overGrothendieckTopology_eq_toGrothendieck_overPretopology : S.over
GrothendieckTopology P = (S.overPretopology P).toGrothendieck
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma mem_overGrothendieckTopology (X : Over S) (R : Sieve X) :
    R ∈ S.overGrothendieckTopology P X ↔
      ∃ (𝒰 : Cover.{u} (precoverage P) X.left) (_ : 𝒰.Over S), 𝒰.toPresieveOver ≤ R.arrows := by
  rw [overGrothendieckTopology_eq_toGrothendieck_overPretopology]
  constructor
  · rintro ⟨T, ⟨𝒰, h, rfl⟩, hle⟩
    use 𝒰, h
  · rintro ⟨𝒰, h𝒰, hle⟩
    exact ⟨𝒰.toPresieveOver, ⟨𝒰, h𝒰, rfl⟩, hle⟩

variable [Q.IsStableUnderComposition]

variable (S) {P Q} in
/-
**AlgebraicGeometry.Scheme.locallyCoverDense_of_le** 是 Mathlib 中的一个引理，位于命名空间 `Al
gebraicGeometry.Scheme`。
形式化陈述：locallyCoverDense_of_le (hPQ : P <= Q) : (MorphismProperty.Over.forget Q ⊤
 S).LocallyCoverDense (overGrothendieckTopology P S) where functorPushforward_fu
nctorPullback_mem X
参数：hPQ : P <= Q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.instTop`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C], ⊤.IsMultiplicative
· 使用定理 `AlgebraicGeometry.Scheme.isJointlySurjectivePreserving`：∀ (P : CategoryT
heory.MorphismProperty AlgebraicGeometry.Scheme),   AlgebraicGeometry.Scheme.IsJ
ointlySurjectivePreserving P
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.Scheme.mem_overGrothendieckTopology`：mem_overGrothendi
eckTopology (X : Over S) (R : Sieve X) : R in S.overGrothendieckTopology P X ↔ e
xists (𝒰 : Cover.{u} (precoverage P) X.left…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.comp_over`：comp_over [OverClass X S] [OverClass Y S] [Hom
IsOver f S] : f ≫ Y ↘ S = X ↘ S
· 使用定理 `AlgebraicGeometry.Scheme.Cover.Over.isOver_map`：∀ {S : AlgebraicGeometry
.Scheme} {P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme}   {inst 
: P.IsStableUnderBaseChange} {inst_1…
· 使用引理 `CategoryTheory.MorphismProperty.comp_mem`：comp_mem (W : MorphismProperty
 C) [W.IsStableUnderComposition] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : W f) 
(hg : W g) : W (f ≫ g)
· 使用定理 `AlgebraicGeometry.Scheme.Cover.map_prop`：∀ {X : AlgebraicGeometry.Scheme
} {P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme}   (𝒰 : Algebrai
cGeometry.Scheme.Cover (Algeb…
· 使用定理 `CategoryTheory.MorphismProperty.Comma.prop`：∀ {A : Type u_1} [inst : Cat
egoryTheory.Category.{v_1, u_1} A] {B : Type u_2}   [inst_1 : CategoryTheory.Cat
egory.{v_2, u_2} B] {T : Type u_…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
lemma locallyCoverDense_of_le (hPQ : P ≤ Q) :
    (MorphismProperty.Over.forget Q ⊤ S).LocallyCoverDense (overGrothendieckTopology P S) where
  functorPushforward_functorPullback_mem X := by
    intro ⟨T, hT⟩
    rw [mem_overGrothendieckTopology] at hT ⊢
    obtain ⟨𝒰, h, hle⟩ := hT
    use 𝒰, h
    rintro - - ⟨i⟩
    have p : Q (𝒰.X i ↘ S) := by
      rw [← comp_over (𝒰.f i) S]
      exact Q.comp_mem _ _ (hPQ _ <| 𝒰.map_prop i) X.prop
    use (𝒰.X i).asOverProp S p, MorphismProperty.Over.homMk (𝒰.f i) (comp_over (𝒰.f i) S), 𝟙 _
    exact ⟨hle _ _ ⟨i⟩, rfl⟩
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (MorphismProperty.Over.forget P ⊤ S).LocallyCoverDense (overGrothendieckTopology P S) :=
  locallyCoverDense_of_le S le_rfl

variable (S) {Q} in
/-- If `P` and `Q` are morphism properties with `P ≤ Q`, this is the Grothendieck topology
induced via the forgetful functor `Q.Over ⊤ S ⥤ Over S` by the topology defined by `P`. -/
/-
**AlgebraicGeometry.Scheme.smallGrothendieckTopology** 是 Mathlib 中的一个缩写定义，位于命名空间
 `AlgebraicGeometry.Scheme`。
形式化陈述：smallGrothendieckTopology : GrothendieckTopology (Q.Over ⊤ S)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.instTop`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C], ⊤.IsMultiplicative

--- 原说明 ---
If `P` and `Q` are morphism properties with `P ≤ Q`, this is the Grothendieck to
pology
induced via the forgetful functor `Q.Over ⊤ S ⥤ Over S` by the topology defined 
by `P`.
-/
abbrev smallGrothendieckTopology : GrothendieckTopology (Q.Over ⊤ S) :=
  (MorphismProperty.Over.forget Q ⊤ S).restrictedTopology (S.overGrothendieckTopology P)

@[deprecated (since := "2026-05-28")]
alias smallGrothendieckTopologyOfLE := smallGrothendieckTopology

variable [Q.IsStableUnderBaseChange] [Q.HasOfPostcompProperty Q]

set_option backward.isDefEq.respectTransparency false in
/-- The pretopology defined on the subcategory of `S`-schemes satisfying `Q` where coverings
are given by `P`-coverings in `S`-schemes satisfying `Q`.
The most common case is `P = Q`. In this case, this is simply surjective families
in `S`-schemes with `P`. -/
/-
**AlgebraicGeometry.Scheme.smallPretopology** 是 Mathlib 中的一个定义，位于命名空间 `Algebraic
Geometry.Scheme`。
形式化陈述：smallPretopology : Pretopology (Q.Over ⊤ S) where coverings Y
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.instTop`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C], ⊤.IsMultiplicative
· 使用定理 `AlgebraicGeometry.Scheme.isJointlySurjectivePreserving`：∀ (P : CategoryT
heory.MorphismProperty AlgebraicGeometry.Scheme),   AlgebraicGeometry.Scheme.IsJ
ointlySurjectivePreserving P

--- 原说明 ---
The pretopology defined on the subcategory of `S`-schemes satisfying `Q` where c
overings
are given by `P`-coverings in `S`-schemes satisfying `Q`.
The most common case is `P = Q`. In this case, this is simply surjective familie
s
in `S`-schemes with `P`.
-/
def smallPretopology : Pretopology (Q.Over ⊤ S) where
  coverings Y :=
    {R | ∃ (𝒰 : Cover.{u} (precoverage P) Y.left) (_ : 𝒰.Over S) (h : ∀ j : 𝒰.I₀, Q (𝒰.X j ↘ S)),
      R = 𝒰.toPresieveOverProp h}
  has_isos {X Y} f := ⟨coverOfIsIso f.left, inferInstance, fun _ ↦ Y.prop,
    (Presieve.ofArrows_pUnit _).symm⟩
  pullbacks := by
    rintro Y X f _ ⟨𝒰, h, p, rfl⟩
    refine ⟨𝒰.pullbackCoverOverProp' S f.left (Q := Q) Y.prop X.prop p, inferInstance, ?_, ?_⟩
    · intro j
      apply MorphismProperty.Comma.prop
    · exact (Presieve.ofArrows_pullback f (fun i ↦ ⟨(𝒰.X i).asOver S, p i⟩)
        (fun i ↦ ⟨(𝒰.f i).asOver S, trivial, trivial⟩)).symm
  transitive := by
    rintro X _ T ⟨𝒰, h, p, rfl⟩ H
    choose V h pV hV using H
    let 𝒱j (j : 𝒰.I₀) : (Cover (precoverage P) ((𝒰.X j).asOverProp S (p j)).left) :=
      V ((𝒰.f j).asOverProp S) ⟨j⟩
    refine ⟨𝒰.bind (fun j ↦ 𝒱j j), inferInstance, fun j ↦ pV _ _ _, ?_⟩
    convert!
      Presieve.ofArrows_bind _ (fun j ↦ ((𝒰.f j).asOverProp S)) _
        (fun Y f H j ↦ ((V f H).X j).asOverProp S (pV _ _ _))
        (fun Y f H j ↦ ((V f H).f j).asOverProp S)
    apply hV

set_option backward.isDefEq.respectTransparency false in
variable (S) {P Q} in
/-
**AlgebraicGeometry.Scheme.smallGrothendieckTopology_eq_toGrothendieck_smallPret
opology** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry.Scheme`。
形式化陈述：smallGrothendieckTopology_eq_toGrothendieck_smallPretopology (hPQ : P <= Q
) : S.smallGrothendieckTopology P = (S.smallPretopology P Q).toGrothendieck
参数：hPQ : P <= Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.ext`：ext {J₁ J₂ : GrothendieckTopolo
gy C} (h : (J₁ : forall X : C, Set (Sieve X)) = J₂) : J₁ = J₂
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.instTop`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C], ⊤.IsMultiplicative
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullbacks`：CategoryTheory.Limit
s.HasPullbacks AlgebraicGeometry.Scheme
· 使用定理 `CategoryTheory.Limits.PreservesFiniteLimits.preservesFiniteLimits`：∀ {C 
: Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : C
ategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.PreservesLimits.preservesFiniteLimits`：∀ {C : Type
 u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Categor
yTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用引理 `AlgebraicGeometry.Scheme.locallyCoverDense_of_le`：locallyCoverDense_of_l
e (hPQ : P <= Q) : (MorphismProperty.Over.forget Q ⊤ S).LocallyCoverDense (overG
rothendieckTopology P S) where functor…
· 使用定理 `AlgebraicGeometry.Scheme.isJointlySurjectivePreserving`：∀ (P : CategoryT
heory.MorphismProperty AlgebraicGeometry.Scheme),   AlgebraicGeometry.Scheme.IsJ
ointlySurjectivePreserving P
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Functor.IsLocallyFull.of_full`：∀ {C : Type uC} [inst : Ca
tegoryTheory.Category.{vC, uC} C] {D : Type uD} [inst_1 : CategoryTheory.Categor
y.{vD, uD} D]   {K : CategoryTheor…
· 使用定理 `CategoryTheory.MorphismProperty.instFullOverTopOverForget`：∀ {T : Type u
_1} [inst : CategoryTheory.Category.{v_1, u_1} T] (P : CategoryTheory.MorphismPr
operty T) (X : T),   (CategoryTheory.MorphismPr…
· 使用定理 `CategoryTheory.Functor.IsLocallyFaithful.of_faithful`：∀ {C : Type uC} [i
nst : CategoryTheory.Category.{vC, uC} C] {D : Type uD} [inst_1 : CategoryTheory
.Category.{vD, uD} D]   {K : CategoryTheor…
· 使用定理 `CategoryTheory.MorphismProperty.instFaithfulOverOverForget`：∀ {T : Type 
u_1} [inst : CategoryTheory.Category.{v_1, u_1} T] (P Q : CategoryTheory.Morphis
mProperty T) (X : T)   [inst_1 : Q.IsMultiplicat…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.comp_over`：comp_over [OverClass X S] [OverClass Y S] [Hom
IsOver f S] : f ≫ Y ↘ S = X ↘ S
· 使用定理 `AlgebraicGeometry.Scheme.Cover.Over.isOver_map`：∀ {S : AlgebraicGeometry
.Scheme} {P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme}   {inst 
: P.IsStableUnderBaseChange} {inst_1…
· 使用引理 `CategoryTheory.MorphismProperty.comp_mem`：comp_mem (W : MorphismProperty
 C) [W.IsStableUnderComposition] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : W f) 
(hg : W g) : W (f ≫ g)
· 使用定理 `AlgebraicGeometry.Scheme.Cover.map_prop`：∀ {X : AlgebraicGeometry.Scheme
} {P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme}   (𝒰 : Algebrai
cGeometry.Scheme.Cover (Algeb…
· 使用定理 `CategoryTheory.MorphismProperty.Comma.prop`：∀ {A : Type u_1} [inst : Cat
egoryTheory.Category.{v_1, u_1} A] {B : Type u_2}   [inst_1 : CategoryTheory.Cat
egory.{v_2, u_2} B] {T : Type u_…
· 使用引理 `CategoryTheory.Sieve.mem_functorPushforward_iff_of_full_of_faithful`：mem
_functorPushforward_iff_of_full_of_faithful [F.Full] [F.Faithful] {X Y : C} (R :
 Sieve X) (f : Y ⟶ X) : (R.arrows.functorPushforward F) (…
· 使用定理 `CategoryTheory.Sieve.functorPushforward_apply`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Catego
ry.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
lemma smallGrothendieckTopology_eq_toGrothendieck_smallPretopology (hPQ : P ≤ Q) :
    S.smallGrothendieckTopology P = (S.smallPretopology P Q).toGrothendieck := by
  ext X R
  have : (MorphismProperty.Over.forget Q ⊤ S).LocallyCoverDense (overGrothendieckTopology P S) :=
    locallyCoverDense_of_le S hPQ
  simp only [smallGrothendieckTopology, Functor.mem_restrictedTopology_iff,
    mem_overGrothendieckTopology, Pretopology.mem_toGrothendieck]
  constructor
  · intro ⟨𝒰, h, le⟩
    have hj (j : 𝒰.I₀) : Q (𝒰.X j ↘ S) := by
      rw [← comp_over (𝒰.f j)]
      exact Q.comp_mem _ _ (hPQ _ <| 𝒰.map_prop _) X.prop
    refine ⟨𝒰.toPresieveOverProp hj, ?_, ?_⟩
    · use 𝒰, h, hj
    · rintro - - ⟨i⟩
      let fi : (𝒰.X i).asOverProp S (hj i) ⟶ X := (𝒰.f i).asOverProp S
      have : R.functorPushforward _ ((MorphismProperty.Over.forget Q ⊤ S).map fi) := le _ _ ⟨i⟩
      rwa [Sieve.functorPushforward_apply,
        Sieve.mem_functorPushforward_iff_of_full_of_faithful] at this
  · rintro ⟨T, ⟨𝒰, h, p, rfl⟩, le⟩
    use 𝒰, h
    rintro - - ⟨i⟩
    exact ⟨(𝒰.X i).asOverProp S (p i), (𝒰.f i).asOverProp S, 𝟙 _, le _ _ ⟨i⟩, rfl⟩

@[deprecated (since := "2026-05-28")]
alias smallGrothendieckTopologyOfLE_eq_toGrothendieck_smallPretopology :=
  smallGrothendieckTopology_eq_toGrothendieck_smallPretopology

variable {P Q}

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.Scheme.mem_toGrothendieck_smallPretopology** 是 Mathlib 中的一个引
理，位于命名空间 `AlgebraicGeometry.Scheme`。
形式化陈述：mem_toGrothendieck_smallPretopology (X : Q.Over ⊤ S) (R : Sieve X) : R in 
(S.smallPretopology P Q).toGrothendieck X ↔ forall x : X.left, exists (Y : Q.Ove
r ⊤ S) (f : Y ⟶ X) (y : Y.left), R f ∧ P f.left ∧ f.left y = x
参数：X : Q.Over ⊤ S；R : Sieve X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.instTop`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C], ⊤.IsMultiplicative
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullbacks`：CategoryTheory.Limit
s.HasPullbacks AlgebraicGeometry.Scheme
· 使用定理 `CategoryTheory.Limits.PreservesFiniteLimits.preservesFiniteLimits`：∀ {C 
: Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : C
ategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.PreservesLimits.preservesFiniteLimits`：∀ {C : Type
 u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Categor
yTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Pretopology.mem_toGrothendieck`：mem_toGrothendieck (K : P
retopology C) (X S) : S in toGrothendieck K X ↔ exists R in K X, R <= (S : Presi
eve X)
· 使用定理 `AlgebraicGeometry.Scheme.isJointlySurjectivePreserving`：∀ (P : CategoryT
heory.MorphismProperty AlgebraicGeometry.Scheme),   AlgebraicGeometry.Scheme.IsJ
ointlySurjectivePreserving P
· 使用定理 `AlgebraicGeometry.Scheme.instJointlySurjectivePrecoverage`：∀ {P : Catego
ryTheory.MorphismProperty AlgebraicGeometry.Scheme},   AlgebraicGeometry.Scheme.
JointlySurjective (AlgebraicGeometry.Scheme.pre…
· 使用定理 `AlgebraicGeometry.Scheme.Cover.covers`：∀ {K : CategoryTheory.Precoverage
 AlgebraicGeometry.Scheme} {X : AlgebraicGeometry.Scheme}   [inst : AlgebraicGeo
metry.Scheme.JointlySurject…
· 使用定理 `AlgebraicGeometry.Scheme.Cover.Over.isOver_map`：∀ {S : AlgebraicGeometry
.Scheme} {P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme}   {inst 
: P.IsStableUnderBaseChange} {inst_1…
· 使用定理 `CategoryTheory.MorphismProperty.Comma.prop`：∀ {A : Type u_1} [inst : Cat
egoryTheory.Category.{v_1, u_1} A] {B : Type u_2}   [inst_1 : CategoryTheory.Cat
egory.{v_2, u_2} B] {T : Type u_…
· 使用定理 `AlgebraicGeometry.Scheme.Cover.map_prop`：∀ {X : AlgebraicGeometry.Scheme
} {P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme}   (𝒰 : Algebrai
cGeometry.Scheme.Cover (Algeb…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `AlgebraicGeometry.Scheme.presieve₀_mem_precoverage_iff`：presieve₀_mem_pr
ecoverage_iff (E : PreZeroHypercover X) : E.presieve₀ in precoverage P X ↔ (fora
ll x, exists i, x in Set.range (E.f i)) ∧ fo…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `CategoryTheory.instHomIsOverLeft`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {S : C} {X Y : CategoryTheory.Over S} (f : X ⟶ Y),   Category
Theory.HomIsOver (Cate…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
lemma mem_toGrothendieck_smallPretopology (X : Q.Over ⊤ S) (R : Sieve X) :
    R ∈ (S.smallPretopology P Q).toGrothendieck X ↔
      ∀ x : X.left, ∃ (Y : Q.Over ⊤ S) (f : Y ⟶ X) (y : Y.left),
        R f ∧ P f.left ∧ f.left y = x := by
  rw [Pretopology.mem_toGrothendieck]
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨T, ⟨𝒰, h, p, rfl⟩, hle⟩
    intro x
    obtain ⟨y, hy⟩ := 𝒰.covers x
    refine ⟨(𝒰.X (𝒰.idx x)).asOverProp S (p _), (𝒰.f (𝒰.idx x)).asOverProp S, y, hle _ _ ?_,
      𝒰.map_prop _, hy⟩
    use 𝒰.idx x
  · choose Y f y hf hP hy using h
    let 𝒰 : X.left.Cover (precoverage P) :=
      { I₀ := X.left,
        X := fun i ↦ (Y i).left
        f := fun i ↦ (f i).left
        mem₀ := by
          rw [presieve₀_mem_precoverage_iff]
          refine ⟨fun x ↦ ⟨x, y x, hy x⟩, hP⟩ }
    let : 𝒰.Over S :=
      { over := fun i ↦ inferInstance
        isOver_map := fun i ↦ inferInstance }
    refine ⟨𝒰.toPresieveOverProp fun i ↦ MorphismProperty.Comma.prop _, ?_, ?_⟩
    · use 𝒰, inferInstance, fun i ↦ MorphismProperty.Comma.prop _
    · rintro - - ⟨i⟩
      exact hf i

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.Scheme.mem_smallGrothendieckTopology** 是 Mathlib 中的一个引理，位于命名
空间 `AlgebraicGeometry.Scheme`。
形式化陈述：mem_smallGrothendieckTopology [P.HasOfPostcompProperty P] (X : P.Over ⊤ S)
 (R : Sieve X) : R in S.smallGrothendieckTopology P X ↔ exists (𝒰 : Cover.{u} (p
recoverage P) X.left) (_ : 𝒰.Over S) (h : forall j, P (𝒰.X j ↘ S)), 𝒰.toPresieve
OverProp h <= R.arrows
参数：X : P.Over ⊤ S；R : Sieve X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.instTop`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C], ⊤.IsMultiplicative
· 使用定理 `AlgebraicGeometry.Scheme.isJointlySurjectivePreserving`：∀ (P : CategoryT
heory.MorphismProperty AlgebraicGeometry.Scheme),   AlgebraicGeometry.Scheme.IsJ
ointlySurjectivePreserving P
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toIsStableUnderComposit
ion`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheor
y.MorphismProperty C}   [self : W.IsMultiplicative], W.IsStableUn…
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullbacks`：CategoryTheory.Limit
s.HasPullbacks AlgebraicGeometry.Scheme
· 使用定理 `CategoryTheory.Limits.PreservesFiniteLimits.preservesFiniteLimits`：∀ {C 
: Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : C
ategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.PreservesLimits.preservesFiniteLimits`：∀ {C : Type
 u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Categor
yTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.Scheme.smallGrothendieckTopology_eq_toGrothendieck_sma
llPretopology`：smallGrothendieckTopology_eq_toGrothendieck_smallPretopology (hPQ
 : P <= Q) : S.smallGrothendieckTopology P = (S.smallPretopology P Q).toGro…
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma mem_smallGrothendieckTopology [P.HasOfPostcompProperty P] (X : P.Over ⊤ S) (R : Sieve X) :
    R ∈ S.smallGrothendieckTopology P X ↔
      ∃ (𝒰 : Cover.{u} (precoverage P) X.left) (_ : 𝒰.Over S) (h : ∀ j, P (𝒰.X j ↘ S)),
          𝒰.toPresieveOverProp h ≤ R.arrows := by
  rw [smallGrothendieckTopology_eq_toGrothendieck_smallPretopology _ le_rfl]
  constructor
  · rintro ⟨T, ⟨𝒰, h, p, rfl⟩, hle⟩
    use 𝒰, h, p
  · rintro ⟨𝒰, h𝒰, p, hle⟩
    exact ⟨𝒰.toPresieveOverProp p, ⟨𝒰, h𝒰, p, rfl⟩, hle⟩

end AlgebraicGeometry.Scheme

