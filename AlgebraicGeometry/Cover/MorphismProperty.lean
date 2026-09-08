/-
Copyright (c) 2024 Christian Merten, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten, Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.Sites.MorphismProperty
public import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# Covers of schemes

This file provides the basic API for covers of schemes. A cover of a scheme `X` with respect to
a morphism property `P` is a jointly surjective indexed family of scheme morphisms with
target `X` all satisfying `P`.

## Implementation details

The definition on the pullback of a cover along a morphism depends on results that
are developed later in the import tree. Hence in this file, they have additional assumptions
that will be automatically satisfied in later files. The motivation here is that we already
know that these assumptions are satisfied for open immersions and hence the cover API for open
immersions can be used to deduce these assumptions in the general case.

-/

@[expose] public section


noncomputable section

open TopologicalSpace CategoryTheory Opposite CategoryTheory.Limits

universe v v₁ v₂ u

namespace AlgebraicGeometry

namespace Scheme

variable (K : Precoverage Scheme.{u})

/-- A coverage `K` on `Scheme` is called jointly surjective if every covering family in `K`
is jointly surjective. -/
/-
**AlgebraicGeometry.Scheme.JointlySurjective** 是 Mathlib 中的一个归纳类型，位于命名空间 `Algebr
aicGeometry.Scheme`。
形式化陈述：CategoryTheory.Precoverage AlgebraicGeometry.Scheme → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A coverage `K` on `Scheme` is called jointly surjective if every covering family
 in `K`
is jointly surjective.
-/
class JointlySurjective (K : Precoverage Scheme.{u}) : Prop where
  exists_eq {X : Scheme.{u}} (S : Presieve X) (hS : S ∈ K X) (x : X) :
    ∃ (Y : Scheme.{u}) (g : Y ⟶ X), S g ∧ x ∈ Set.range g

/-- A cover of `X` in the coverage `K` is a `0`-hypercover for `K`. -/
/-
**AlgebraicGeometry.Scheme.Cover** 是 Mathlib 中的一个缩写定义，位于命名空间 `AlgebraicGeometry.
Scheme`。
形式化陈述：Cover (K : Precoverage Scheme.{u})
参数：K : Precoverage Scheme.{u}。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A cover of `X` in the coverage `K` is a `0`-hypercover for `K`.
-/
abbrev Cover (K : Precoverage Scheme.{u}) := Precoverage.ZeroHypercover.{v} K

variable {K}

variable {X Y Z : Scheme.{u}} (𝒰 : X.Cover K) (f : X ⟶ Z) (g : Y ⟶ Z)
variable [∀ x, HasPullback (𝒰.f x ≫ f) g]
/-
**AlgebraicGeometry.Scheme.Cover.exists_eq** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicG
eometry.Scheme.Cover`。
形式化陈述：∀ {K : CategoryTheory.Precoverage AlgebraicGeometry.Scheme} {X : Algebraic
Geometry.Scheme}   [AlgebraicGeometry.Scheme.JointlySurjective K] (𝒰 : Algebraic
Geometry.Scheme.Cover K X) (x : ↥X), ∃ i y, (𝒰.f i) y = x
参数：𝒰 : AlgebraicGeometry.Scheme.Cover K X；x : ↥X；𝒰.f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.JointlySurjective.exists_eq`：∀ {K : CategoryThe
ory.Precoverage AlgebraicGeometry.Scheme} [self : AlgebraicGeometry.Scheme.Joint
lySurjective K]   {X : AlgebraicGeometry.S…
· 使用定理 `CategoryTheory.Precoverage.ZeroHypercover.mem₀`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] {J : CategoryTheory.Precoverage C} {S : C}   (s
elf : J.ZeroHypercover S), self.pres…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
lemma Cover.exists_eq [JointlySurjective K] (𝒰 : X.Cover K) (x : X) :
    ∃ i y, 𝒰.f i y = x := by
  obtain ⟨Y, g, ⟨i⟩, y, hy⟩ := JointlySurjective.exists_eq 𝒰.presieve₀ 𝒰.mem₀ x
  use i, y

/-- A choice of an index `i` such that `x` is in the range of `𝒰.f i`. -/
/-
**AlgebraicGeometry.Scheme.Cover.idx** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeometr
y.Scheme.Cover`。
形式化陈述：{K : CategoryTheory.Precoverage AlgebraicGeometry.Scheme} →   {X : Algebra
icGeometry.Scheme} →     [AlgebraicGeometry.Scheme.JointlySurjective K] → (𝒰 : A
lgebraicGeometry.Scheme.Cover K X) → ↥X → 𝒰.I₀
参数：𝒰 : AlgebraicGeometry.Scheme.Cover K X。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Cover.exists_eq`：∀ {K : CategoryTheory.Precover
age AlgebraicGeometry.Scheme} {X : AlgebraicGeometry.Scheme}   [AlgebraicGeometr
y.Scheme.JointlySurjective K] …

--- 原说明 ---
A choice of an index `i` such that `x` is in the range of `𝒰.f i`.
-/
def Cover.idx [JointlySurjective K] (𝒰 : X.Cover K) (x : X) : 𝒰.I₀ :=
  (𝒰.exists_eq x).choose
/-
**AlgebraicGeometry.Scheme.Cover.covers** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeom
etry.Scheme.Cover`。
形式化陈述：∀ {K : CategoryTheory.Precoverage AlgebraicGeometry.Scheme} {X : Algebraic
Geometry.Scheme}   [inst : AlgebraicGeometry.Scheme.JointlySurjective K] (𝒰 : Al
gebraicGeometry.Scheme.Cover K X) (x : ↥X),   x ∈ Set.range ⇑(𝒰.f (𝒰.idx x))
参数：𝒰 : AlgebraicGeometry.Scheme.Cover K X；x : ↥X；𝒰.f (𝒰.idx x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `AlgebraicGeometry.Scheme.Cover.exists_eq`：∀ {K : CategoryTheory.Precover
age AlgebraicGeometry.Scheme} {X : AlgebraicGeometry.Scheme}   [AlgebraicGeometr
y.Scheme.JointlySurjective K] …
-/
lemma Cover.covers [JointlySurjective K] (𝒰 : X.Cover K) (x : X) :
    x ∈ Set.range (𝒰.f (𝒰.idx x)) :=
  (𝒰.exists_eq x).choose_spec
/-
**AlgebraicGeometry.Scheme.Cover.iUnion_range** 是 Mathlib 中的一个定理，位于命名空间 `Algebra
icGeometry.Scheme.Cover`。
形式化陈述：∀ {K : CategoryTheory.Precoverage AlgebraicGeometry.Scheme} [AlgebraicGeom
etry.Scheme.JointlySurjective K]   {X : AlgebraicGeometry.Scheme} (𝒰 : Algebraic
Geometry.Scheme.Cover K X), ⋃ i, Set.range ⇑(𝒰.f i) = Set.univ
参数：𝒰 : AlgebraicGeometry.Scheme.Cover K X；𝒰.f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.eq_univ_iff_forall`：eq_univ_iff_forall {s : Set α} : s = univ ↔ fora
ll x, x in s
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用定理 `AlgebraicGeometry.Scheme.Cover.exists_eq`：∀ {K : CategoryTheory.Precover
age AlgebraicGeometry.Scheme} {X : AlgebraicGeometry.Scheme}   [AlgebraicGeometr
y.Scheme.JointlySurjective K] …
-/
theorem Cover.iUnion_range [JointlySurjective K] {X : Scheme.{u}} (𝒰 : X.Cover K) :
    ⋃ i, Set.range (𝒰.f i) = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  intro x
  rw [Set.mem_iUnion]
  exact 𝒰.exists_eq x
/-
**AlgebraicGeometry.Scheme.Cover.nonempty_of_nonempty** 是 Mathlib 中的一个定理，位于命名空间 
`AlgebraicGeometry.Scheme.Cover`。
形式化陈述：∀ {K : CategoryTheory.Precoverage AlgebraicGeometry.Scheme} {X : Algebraic
Geometry.Scheme}   [AlgebraicGeometry.Scheme.JointlySurjective K] [Nonempty ↥X] 
(𝒰 : AlgebraicGeometry.Scheme.Cover K X), Nonempty 𝒰.I₀
参数：𝒰 : AlgebraicGeometry.Scheme.Cover K X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Cover.exists_eq`：∀ {K : CategoryTheory.Precover
age AlgebraicGeometry.Scheme} {X : AlgebraicGeometry.Scheme}   [AlgebraicGeometr
y.Scheme.JointlySurjective K] …
-/
instance Cover.nonempty_of_nonempty [JointlySurjective K] [Nonempty X] (𝒰 : X.Cover K) :
    Nonempty 𝒰.I₀ := by
  obtain ⟨i, _⟩ := 𝒰.exists_eq ‹Nonempty X›.some
  use i

section MorphismProperty

variable {P Q : MorphismProperty Scheme.{u}}

/-
**AlgebraicGeometry.Scheme.presieve** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry
.Scheme`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma presieve₀_mem_precoverage_iff (E : PreZeroHypercover X) :
    E.presieve₀ ∈ precoverage P X ↔ (∀ x, ∃ i, x ∈ Set.range (E.f i)) ∧ ∀ i, P (E.f i) := by
  simp

@[grind ←]
/-
**AlgebraicGeometry.Scheme.Cover.map_prop** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGe
ometry.Scheme.Cover`。
形式化陈述：∀ {X : AlgebraicGeometry.Scheme} {P : CategoryTheory.MorphismProperty Alge
braicGeometry.Scheme}   (𝒰 : AlgebraicGeometry.Scheme.Cover (AlgebraicGeometry.S
cheme.precoverage P) X) (i : 𝒰.I₀), P (𝒰.f i)
参数：𝒰 : AlgebraicGeometry.Scheme.Cover (AlgebraicGeometry.Scheme.precoverage P) X
；i : 𝒰.I₀；𝒰.f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `CategoryTheory.Precoverage.ZeroHypercover.mem₀`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] {J : CategoryTheory.Precoverage C} {S : C}   (s
elf : J.ZeroHypercover S), self.pres…
-/
lemma Cover.map_prop (𝒰 : X.Cover (precoverage P)) (i : 𝒰.I₀) : P (𝒰.f i) :=
  𝒰.mem₀.2 ⟨i⟩

/-- Given a family of schemes with morphisms to `X` satisfying `P` that jointly
cover `X`, `Cover.mkOfCovers` is an associated `P`-cover of `X`. -/
@[simps!]
/-
**AlgebraicGeometry.Scheme.Cover.mkOfCovers** 是 Mathlib 中的一个定义，位于命名空间 `Algebraic
Geometry.Scheme.Cover`。
形式化陈述：{X : AlgebraicGeometry.Scheme} →   {P : CategoryTheory.MorphismProperty Al
gebraicGeometry.Scheme} →     (J : Type u_1) →       (obj : J → AlgebraicGeometr
y.Scheme) →         (map : (j : J) → obj j ⟶ X) →           (∀ (x : ↥X), ∃ j y, 
(map j) y = x) →             autoParam (∀ (j : J), P (map j)) AlgebraicGeometry.
Scheme.Cover.mkOfCovers._auto_1 →               AlgebraicGeometry.Scheme.Cover (
AlgebraicGeometry.Scheme.precoverage P) X
参数：J : Type u_1；obj : J → AlgebraicGeometry.Scheme；map : (j : J) → obj j ⟶ X；∀ (
x : ↥X), ∃ j y, (map j) y = x；∀ (j : J), P (map j)；AlgebraicGeometry.Scheme.prec
overage P。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a family of schemes with morphisms to `X` satisfying `P` that jointly
cover `X`, `Cover.mkOfCovers` is an associated `P`-cover of `X`.
-/
def Cover.mkOfCovers (J : Type*) (obj : J → Scheme.{u}) (map : (j : J) → obj j ⟶ X)
    (covers : ∀ x, ∃ j y, map j y = x)
    (map_prop : ∀ j, P (map j) := by infer_instance) : X.Cover (precoverage P) where
  I₀ := J
  X := obj
  f := map
  mem₀ := by
    simp_rw [presieve₀_mem_precoverage_iff, Set.mem_range]
    grind

/-- An isomorphism `X ⟶ Y` is a `P`-cover of `Y`. -/
@[simps! I₀ X f]
/-
**AlgebraicGeometry.Scheme.coverOfIsIso** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeom
etry.Scheme`。
形式化陈述：coverOfIsIso [P.ContainsIdentities] [P.RespectsIso] {X Y : Scheme.{u}} (f 
: X ⟶ Y) [IsIso f] : Cover.{v} (precoverage P) Y
参数：f : X ⟶ Y。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.of_isIso`：of_isIso (P : MorphismProperty
 C) [P.ContainsIdentities] [P.RespectsIso] {X Y : C} (f : X ⟶ Y) [IsIso f] : P f

--- 原说明 ---
An isomorphism `X ⟶ Y` is a `P`-cover of `Y`.
-/
def coverOfIsIso [P.ContainsIdentities] [P.RespectsIso] {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIso f] : Cover.{v} (precoverage P) Y :=
  .mkOfCovers PUnit (fun _ ↦ X)
    (fun _ ↦ f)
    (fun x ↦ ⟨⟨⟩, inv f x, by simp [← Hom.comp_apply]⟩)
    (fun _ ↦ P.of_isIso f)
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : JointlySurjective (precoverage P) where
  exists_eq {X} R := fun ⟨hR, _⟩ x ↦ by
    rw [jointlySurjectivePrecoverage, Presieve.mem_comap_jointlySurjectivePrecoverage_iff] at hR
    obtain ⟨Y, g, hg, heq⟩ := hR x
    use Y, g, hg
    exact heq

/-- Turn a `K`-cover into a `Q`-cover by showing that the components satisfy `Q`. -/
/-
**AlgebraicGeometry.Scheme.Cover.changeProp** 是 Mathlib 中的一个定义，位于命名空间 `Algebraic
Geometry.Scheme.Cover`。
形式化陈述：{K : CategoryTheory.Precoverage AlgebraicGeometry.Scheme} →   {X : Algebra
icGeometry.Scheme} →     {Q : CategoryTheory.MorphismProperty AlgebraicGeometry.
Scheme} →       [AlgebraicGeometry.Scheme.JointlySurjective K] →         (𝒰 : Al
gebraicGeometry.Scheme.Cover K X) →           (∀ (j : 𝒰.I₀), Q (𝒰.f j)) → Algebr
aicGeometry.Scheme.Cover (AlgebraicGeometry.Scheme.precoverage Q) X
参数：𝒰 : AlgebraicGeometry.Scheme.Cover K X；∀ (j : 𝒰.I₀), Q (𝒰.f j)；AlgebraicGeome
try.Scheme.precoverage Q。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn a `K`-cover into a `Q`-cover by showing that the components satisfy `Q`.
-/
def Cover.changeProp [JointlySurjective K] (𝒰 : X.Cover K) (h : ∀ j, Q (𝒰.f j)) :
    X.Cover (precoverage Q) where
  I₀ := 𝒰.I₀
  X := 𝒰.X
  f := 𝒰.f
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    exact ⟨𝒰.exists_eq, h⟩

/-- We construct a cover from another, by providing the needed fields and showing that the
provided fields are isomorphic with the original cover. -/
@[simps I₀ X f]
/-
**AlgebraicGeometry.Scheme.Cover.copy** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeomet
ry.Scheme.Cover`。
形式化陈述：{P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme} →   [P.Resp
ectsIso] →     {X : AlgebraicGeometry.Scheme} →       (𝒰 : AlgebraicGeometry.Sch
eme.Cover (AlgebraicGeometry.Scheme.precoverage P) X) →         (J : Type u_1) →
           (obj : J → AlgebraicGeometry.Scheme) →             (map : (i : J) → o
bj i ⟶ X) →               (e₁ : J ≃ 𝒰.I₀) →                 (e₂ : (i : J) → obj 
i ≅ 𝒰.X (e₁ i)) →                   (∀ (i : J), map i = CategoryTheory.CategoryS
truct.comp (e₂ i).hom (𝒰.f (e₁ i))) →                     AlgebraicGeometry.Sche
me.Cover (AlgebraicGeometry.Scheme.precoverage P) X
参数：𝒰 : AlgebraicGeometry.Scheme.Cover (AlgebraicGeometry.Scheme.precoverage P) X
；J : Type u_1；obj : J → AlgebraicGeometry.Scheme；map : (i : J) → obj i ⟶ X；e₁ : 
J ≃ 𝒰.I₀；e₂ : (i : J) → obj i ≅ 𝒰.X (e₁ i)；∀ (i : J), map i = CategoryTheory.Cat
egoryStruct.comp (e₂ i).hom (𝒰.f (e₁ i))；AlgebraicGeometry.Scheme.precoverage P。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We construct a cover from another, by providing the needed fields and showing th
at the
provided fields are isomorphic with the original cover.
-/
def Cover.copy [P.RespectsIso] {X : Scheme.{u}} (𝒰 : X.Cover (precoverage P))
    (J : Type*) (obj : J → Scheme)
    (map : ∀ i, obj i ⟶ X) (e₁ : J ≃ 𝒰.I₀) (e₂ : ∀ i, obj i ≅ 𝒰.X (e₁ i))
    (h : ∀ i, map i = (e₂ i).hom ≫ 𝒰.f (e₁ i)) : X.Cover (precoverage P) where
  I₀ := J
  X := obj
  f := map
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, ?_⟩
    · obtain ⟨i, y, rfl⟩ := 𝒰.exists_eq x
      obtain ⟨i, rfl⟩ := e₁.surjective i
      use i, (e₂ i).inv y
      simp [h]
    · simp_rw [h, MorphismProperty.cancel_left_of_respectsIso]
      intro i
      exact 𝒰.map_prop _

-- `respectTransparency false` is needed for `simps!`.
-- Consider making implicit-reducible:
-- `Precoverage.ZeroHypercover.bind`, `Cover.mkOfCovers`, `coverOfIso`
set_option backward.isDefEq.respectTransparency false in
/-- The pushforward of a cover along an isomorphism. -/
@[simps! I₀ X f, implicit_reducible]
/-
**AlgebraicGeometry.Scheme.Cover.pushforwardIso** 是 Mathlib 中的一个定义，位于命名空间 `Algeb
raicGeometry.Scheme.Cover`。
形式化陈述：{P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme} →   [P.Resp
ectsIso] →     [P.ContainsIdentities] →       [P.IsStableUnderComposition] →    
     {X Y : AlgebraicGeometry.Scheme} →           AlgebraicGeometry.Scheme.Cover
 (AlgebraicGeometry.Scheme.precoverage P) X →             (f : X ⟶ Y) →         
      [CategoryTheory.IsIso f] → AlgebraicGeometry.Scheme.Cover (AlgebraicGeomet
ry.Scheme.precoverage P) Y
参数：AlgebraicGeometry.Scheme.precoverage P；f : X ⟶ Y；AlgebraicGeometry.Scheme.pre
coverage P。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.instIsStableUnderCompositionPrecoverageOfIsStab
leUnderComposition`：∀ (P : CategoryTheory.MorphismProperty AlgebraicGeometry.Sch
eme) [P.IsStableUnderComposition],   (AlgebraicGeometry.Scheme.precoverage P).Is
…
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The pushforward of a cover along an isomorphism.
-/
def Cover.pushforwardIso [P.RespectsIso] [P.ContainsIdentities] [P.IsStableUnderComposition]
    {X Y : Scheme.{u}} (𝒰 : Cover.{v} (precoverage P) X) (f : X ⟶ Y) [IsIso f] :
    Cover.{v} (precoverage P) Y :=
  Cover.copy ((coverOfIsIso.{v, u} f).bind fun _ => 𝒰) 𝒰.I₀ _ _
    ((Equiv.punitProd _).symm.trans (Equiv.sigmaEquivProd PUnit 𝒰.I₀).symm) (fun _ => Iso.refl _)
    fun _ => (Category.id_comp _).symm

/-- Adding map satisfying `P` into a cover gives another cover. -/
@[simps toPreZeroHypercover]
nonrec def Cover.add {X Y : Scheme.{u}} (𝒰 : X.Cover (precoverage P)) (f : Y ⟶ X)
    (hf : P f := by infer_instance) : X.Cover (precoverage P) where
  __ := 𝒰.toPreZeroHypercover.add f
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ⟨some <| 𝒰.idx x, 𝒰.covers x⟩, ?_⟩
    rintro (i | i) <;> simp [hf, 𝒰.map_prop]

/-- The family of morphisms from the pullback cover to the original cover. -/
/-
**AlgebraicGeometry.Scheme.Cover.pullbackHom** 是 Mathlib 中的一个定义，位于命名空间 `Algebrai
cGeometry.Scheme.Cover`。
形式化陈述：{P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme} →   [inst :
 P.IsStableUnderBaseChange] →     [inst_1 : AlgebraicGeometry.Scheme.IsJointlySu
rjectivePreserving P] →       {X W : AlgebraicGeometry.Scheme} →         (𝒰 : Al
gebraicGeometry.Scheme.Cover (AlgebraicGeometry.Scheme.precoverage P) X) →      
     (f : W ⟶ X) →             (i : 𝒰.toPreZeroHypercover.1) →               [in
st_2 : ∀ (x : 𝒰.I₀), CategoryTheory.Limits.HasPullback f (𝒰.f x)] →             
    (CategoryTheory.Precoverage.ZeroHypercover.pullback₁ f 𝒰).X i ⟶ 𝒰.X i
参数：𝒰 : AlgebraicGeometry.Scheme.Cover (AlgebraicGeometry.Scheme.precoverage P) X
；f : W ⟶ X；i : 𝒰.toPreZeroHypercover.1；x : 𝒰.I₀；𝒰.f x；CategoryTheory.Precoverage
.ZeroHypercover.pullback₁ f 𝒰。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The family of morphisms from the pullback cover to the original cover.
-/
def Cover.pullbackHom [P.IsStableUnderBaseChange] [IsJointlySurjectivePreserving P]
    {X W : Scheme.{u}} (𝒰 : X.Cover (precoverage P)) (f : W ⟶ X) (i) [∀ x, HasPullback f (𝒰.f x)] :
    (𝒰.pullback₁ f).X i ⟶ 𝒰.X i :=
  pullback.snd f (𝒰.f i)

@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.Scheme.Cover.pullbackHom_map** 是 Mathlib 中的一个定理，位于命名空间 `Alge
braicGeometry.Scheme.Cover`。
形式化陈述：∀ {P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme} [inst : P
.IsStableUnderBaseChange]   [inst_1 : AlgebraicGeometry.Scheme.IsJointlySurjecti
vePreserving P] {X W : AlgebraicGeometry.Scheme}   (𝒰 : AlgebraicGeometry.Scheme
.Cover (AlgebraicGeometry.Scheme.precoverage P) X) (f : W ⟶ X)   [inst_2 : ∀ (x 
: 𝒰.I₀), CategoryTheory.Limits.HasPullback f (𝒰.f x)] (i : 𝒰.toPreZeroHypercover
.1),   CategoryTheory.CategoryStruct.comp (𝒰.pullbackHom f i) (𝒰.f i) =     Cate
goryTheory.CategoryStruct.comp ((CategoryTheory.Precoverage.ZeroHypercover.pullb
ack₁ f 𝒰).f i) f
参数：𝒰 : AlgebraicGeometry.Scheme.Cover (AlgebraicGeometry.Scheme.precoverage P) X
；f : W ⟶ X；x : 𝒰.I₀；𝒰.f x；i : 𝒰.toPreZeroHypercover.1；𝒰.pullbackHom f i；𝒰.f i；(C
ategoryTheory.Precoverage.ZeroHypercover.pullback₁ f 𝒰).f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…
-/
lemma Cover.pullbackHom_map [P.IsStableUnderBaseChange] [IsJointlySurjectivePreserving P]
    {X W : Scheme.{u}} (𝒰 : X.Cover (precoverage P)) (f : W ⟶ X)
    [∀ (x : 𝒰.I₀), HasPullback f (𝒰.f x)] (i) :
    𝒰.pullbackHom f i ≫ 𝒰.f i = (𝒰.pullback₁ f).f i ≫ f := pullback.condition.symm

/--
An affine cover of `X` consists of a jointly surjective family of maps into `X` from
spectra of rings.

Note: The `map_prop` field is equipped with a default argument `by infer_instance`. In general
this causes worse error messages, but in practice `P` is mostly defined via `class`.
-/
/-
**AlgebraicGeometry.Scheme.AffineCover** 是 Mathlib 中的一个结构，位于命名空间 `AlgebraicGeome
try.Scheme`。
形式化陈述：AffineCover (P : MorphismProperty Scheme.{u}) (S : Scheme.{u}) where /-- i
ndex set of an affine cover of a scheme `S` -/ I₀ : Type v /-- the ring associat
ed to a component of an affine cover -/ X (j : I₀) : CommRingCat.{u} /-- the com
ponents map to `S` -/ f (j : I₀) : Spec (X j) ⟶ S /-- given a point of `x : S`, 
`idx x` is the index of the component which contains `x` -/ idx (x : S) : I₀ /--
 the components cover `S` -/ covers (x : S) : x in Set.range (f (idx x)) /-- the
 component maps satisfy `P
参数：P : MorphismProperty Scheme.{u}；S : Scheme.{u}。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An affine cover of `X` consists of a jointly surjective family of maps into `X` 
from
spectra of rings.

Note: The `map_prop` field is equipped with a default argument `by infer_instanc
e`. In general
this causes worse error messages, but in practice `P` is mostly defined via `cla
ss`. -/
-/
structure AffineCover (P : MorphismProperty Scheme.{u}) (S : Scheme.{u}) where
  /-- index set of an affine cover of a scheme `S` -/
  I₀ : Type v
  /-- the ring associated to a component of an affine cover -/
  X (j : I₀) : CommRingCat.{u}
  /-- the components map to `S` -/
  f (j : I₀) : Spec (X j) ⟶ S
  /-- given a point of `x : S`, `idx x` is the index of the component which contains `x` -/
  idx (x : S) : I₀
  /-- the components cover `S` -/
  covers (x : S) : x ∈ Set.range (f (idx x))
  /-- the component maps satisfy `P` -/
  map_prop (j : I₀) : P (f j) := by infer_instance

/-- The cover associated to an affine cover. -/
@[simps]
/-
**AlgebraicGeometry.Scheme.AffineCover.cover** 是 Mathlib 中的一个定义，位于命名空间 `Algebrai
cGeometry.Scheme.AffineCover`。
形式化陈述：{P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme} →   {X : Al
gebraicGeometry.Scheme} →     AlgebraicGeometry.Scheme.AffineCover P X → Algebra
icGeometry.Scheme.Cover (AlgebraicGeometry.Scheme.precoverage P) X
参数：AlgebraicGeometry.Scheme.precoverage P。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cover associated to an affine cover.
-/
def AffineCover.cover {X : Scheme.{u}} (𝒰 : X.AffineCover P) :
    X.Cover (precoverage P) where
  I₀ := 𝒰.I₀
  X j := Spec (𝒰.X j)
  f := 𝒰.f
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, 𝒰.map_prop⟩
    obtain ⟨y, hy⟩ := 𝒰.covers x
    use 𝒰.idx x, y

/-- Any `v`-cover `𝒰` induces a `u`-cover indexed by the points of `X`. -/
@[simps!]
/-
**AlgebraicGeometry.Scheme.Cover.ulift** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeome
try.Scheme.Cover`。
形式化陈述：{X : AlgebraicGeometry.Scheme} →   {P : CategoryTheory.MorphismProperty Al
gebraicGeometry.Scheme} →     AlgebraicGeometry.Scheme.Cover (AlgebraicGeometry.
Scheme.precoverage P) X →       AlgebraicGeometry.Scheme.Cover (AlgebraicGeometr
y.Scheme.precoverage P) X
参数：AlgebraicGeometry.Scheme.precoverage P；AlgebraicGeometry.Scheme.precoverage P
。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.instJointlySurjectivePrecoverage`：∀ {P : Catego
ryTheory.MorphismProperty AlgebraicGeometry.Scheme},   AlgebraicGeometry.Scheme.
JointlySurjective (AlgebraicGeometry.Scheme.pre…

--- 原说明 ---
Any `v`-cover `𝒰` induces a `u`-cover indexed by the points of `X`.
-/
def Cover.ulift (𝒰 : Cover.{v} (precoverage P) X) : Cover.{u} (precoverage P) X where
  I₀ := X
  X x := 𝒰.X (𝒰.idx x)
  f x := 𝒰.f _
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, fun i ↦ 𝒰.map_prop _⟩
    use x, (𝒰.exists_eq x).choose_spec.choose, (𝒰.exists_eq x).choose_spec.choose_spec
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Precoverage.Small.{u} (precoverage P) where
  zeroHypercoverSmall {S} 𝒰 := ⟨S, Cover.idx 𝒰, (Cover.ulift 𝒰).mem₀⟩

section category

/--
A morphism between covers `𝒰 ⟶ 𝒱` indicates that `𝒰` is a refinement of `𝒱`.
Since covers of schemes are indexed, the definition also involves a map on the
indexing types.
This is implemented as an `abbrev` for `CategoryTheory.Precoverage.ZeroHypercover.Hom`.
-/
/-
**AlgebraicGeometry.Scheme.Cover.Hom** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeometr
y.Scheme.Cover`。
形式化陈述：{K : CategoryTheory.Precoverage AlgebraicGeometry.Scheme} →   {X : Algebra
icGeometry.Scheme} →     AlgebraicGeometry.Scheme.Cover K X → AlgebraicGeometry.
Scheme.Cover K X → Type (max u v)
参数：max u v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism between covers `𝒰 ⟶ 𝒱` indicates that `𝒰` is a refinement of `𝒱`.
Since covers of schemes are indexed, the definition also involves a map on the
indexing types.
This is implemented as an `abbrev` for `CategoryTheory.Precoverage.ZeroHypercove
r.Hom`.
-/
abbrev Cover.Hom {X : Scheme.{u}} (𝒰 𝒱 : Cover.{v} K X) :=
  Precoverage.ZeroHypercover.Hom K 𝒰 𝒱

@[deprecated (since := "2026-01-13")] alias Cover.Hom.idx := PreZeroHypercover.Hom.s₀

@[deprecated (since := "2026-01-13")] alias Cover.Hom.app := PreZeroHypercover.Hom.h₀

@[deprecated (since := "2026-01-13")] alias Cover.Hom.w := PreZeroHypercover.Hom.w₀

@[deprecated (since := "2026-01-13")] alias Cover.Hom.id := PreZeroHypercover.Hom.id

@[deprecated (since := "2026-01-13")] alias Cover.Hom.comp := PreZeroHypercover.Hom.comp

@[deprecated (since := "2026-01-13")] alias Cover.id_idx_apply := PreZeroHypercover.id_s₀

@[deprecated (since := "2026-01-13")] alias Cover.id_app := PreZeroHypercover.id_h₀

@[deprecated (since := "2026-01-13")] alias Cover.comp_idx_apply := PreZeroHypercover.comp_s₀

@[deprecated (since := "2026-01-13")] alias Cover.comp_app := PreZeroHypercover.comp_h₀

end category

end MorphismProperty

end Scheme

end AlgebraicGeometry

