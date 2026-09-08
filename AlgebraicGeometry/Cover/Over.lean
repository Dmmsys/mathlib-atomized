/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.CategoryTheory.Limits.MorphismProperty

/-!

# Covers of schemes over a base

In this file we define the typeclass `Cover.Over`. For a cover `𝒰` of an `S`-scheme `X`,
the datum `𝒰.Over S` contains `S`-scheme structures on the components of `𝒰` and asserts
that the component maps are morphisms of `S`-schemes.

We provide instances of `𝒰.Over S` for standard constructions on covers.

-/

@[expose] public section

universe v u

noncomputable section

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

variable {P : MorphismProperty Scheme.{u}} (S : Scheme.{u})

/-- Bundle an `S`-scheme with `P` into an object of `P.Over ⊤ S`. -/
/-
**AlgebraicGeometry.Scheme.asOverProp** 是 Mathlib 中的一个缩写定义，位于命名空间 `AlgebraicGeom
etry.Scheme`。
形式化陈述：asOverProp (X : Scheme.{u}) (S : Scheme.{u}) [X.Over S] (h : P (X ↘ S)) : 
P.Over ⊤ S
参数：X : Scheme.{u}；S : Scheme.{u}；h : P (X ↘ S)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Bundle an `S`-scheme with `P` into an object of `P.Over ⊤ S`.
-/
abbrev asOverProp (X : Scheme.{u}) (S : Scheme.{u}) [X.Over S] (h : P (X ↘ S)) : P.Over ⊤ S :=
  ⟨X.asOver S, h⟩

/-- Bundle an `S`-morphism of `S`-scheme with `P` into a morphism in `P.Over ⊤ S`. -/
/-
**AlgebraicGeometry.Scheme.Hom.asOverProp** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGe
ometry.Scheme.Hom`。
形式化陈述：{P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme} →   {X Y : 
AlgebraicGeometry.Scheme} →     (f : X.Hom Y) →       (S : AlgebraicGeometry.Sch
eme) →         [inst : X.Over S] →           [inst_1 : Y.Over S] →             [
f.IsOver S] → {hX : P (X ↘ S)} → {hY : P (Y ↘ S)} → X.asOverProp S hX ⟶ Y.asOver
Prop S hY
参数：f : X.Hom Y；S : AlgebraicGeometry.Scheme；X ↘ S；Y ↘ S。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True

--- 原说明 ---
Bundle an `S`-morphism of `S`-scheme with `P` into a morphism in `P.Over ⊤ S`.
-/
abbrev Hom.asOverProp {X Y : Scheme.{u}} (f : X.Hom Y) (S : Scheme.{u}) [X.Over S] [Y.Over S]
    [f.IsOver S] {hX : P (X ↘ S)} {hY : P (Y ↘ S)} : X.asOverProp S hX ⟶ Y.asOverProp S hY :=
  ⟨f.asOver S, trivial, trivial⟩

/-- A `P`-cover of a scheme `X` over `S` is a cover, where the components are over `S` and the
component maps commute with the structure morphisms. -/
/-
**AlgebraicGeometry.Scheme.Cover.Over** 是 Mathlib 中的一个归纳类型，位于命名空间 `AlgebraicGeom
etry.Scheme.Cover`。
形式化陈述：(S : AlgebraicGeometry.Scheme) →   {P : CategoryTheory.MorphismProperty Al
gebraicGeometry.Scheme} →     [P.IsStableUnderBaseChange] →       [AlgebraicGeom
etry.Scheme.IsJointlySurjectivePreserving P] →         {X : AlgebraicGeometry.Sc
heme} →           [X.Over S] → AlgebraicGeometry.Scheme.Cover (AlgebraicGeometry
.Scheme.precoverage P) X → Type (max u u_1)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `P`-cover of a scheme `X` over `S` is a cover, where the components are over `
S` and the
component maps commute with the structure morphisms.
-/
protected class Cover.Over {P : MorphismProperty Scheme.{u}} [P.IsStableUnderBaseChange]
    [IsJointlySurjectivePreserving P] {X : Scheme.{u}} [X.Over S]
    (𝒰 : X.Cover (precoverage P)) where
  over (j : 𝒰.I₀) : (𝒰.X j).Over S := by infer_instance
  isOver_map (j : 𝒰.I₀) : (𝒰.f j).IsOver S := by infer_instance

attribute [instance_reducible] Cover.Over.over
attribute [instance] Cover.Over.over Cover.Over.isOver_map

variable [P.IsStableUnderBaseChange] [IsJointlySurjectivePreserving P]
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [P.ContainsIdentities] [P.RespectsIso] {X Y : Scheme.{u}} (f : X ⟶ Y) [X.Over S] [Y.Over S]
    [f.IsOver S] [IsIso f] : (coverOfIsIso (P := P) f).Over S where
  over _ := inferInstanceAs <| X.Over S
  isOver_map _ := inferInstanceAs <| f.IsOver S

section

variable {X W : Scheme.{u}} (𝒰 : X.Cover (precoverage P)) (f : W ⟶ X) [W.Over S] [X.Over S]
  [𝒰.Over S] [f.IsOver S]

set_option backward.isDefEq.respectTransparency false in
/-- The pullback of a cover of `S`-schemes along a morphism of `S`-schemes. This is not
definitionally equal to `AlgebraicGeometry.Scheme.Cover.pullback₁`, as here we take
the pullback in `Over S`, whose underlying scheme is only isomorphic but not equal to the
pullback in `Scheme`. -/
@[simps]
/-
**AlgebraicGeometry.Scheme.Cover.pullbackCoverOver** 是 Mathlib 中的一个定义，位于命名空间 `Al
gebraicGeometry.Scheme.Cover`。
形式化陈述：{P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme} →   (S : Al
gebraicGeometry.Scheme) →     [inst : P.IsStableUnderBaseChange] →       [inst_1
 : AlgebraicGeometry.Scheme.IsJointlySurjectivePreserving P] →         {X W : Al
gebraicGeometry.Scheme} →           (𝒰 : AlgebraicGeometry.Scheme.Cover (Algebra
icGeometry.Scheme.precoverage P) X) →             (f : W ⟶ X) →               [i
nst_2 : W.Over S] →                 [inst_3 : X.Over S] →                   [Alg
ebraicGeometry.Scheme.Cover.Over S 𝒰] →                     [AlgebraicGeometry.S
cheme.Hom.IsOver f S] →                       AlgebraicGeometry.Scheme.Cover (Al
gebraicGeometry.Scheme.precoverage P) W
参数：S : AlgebraicGeometry.Scheme；𝒰 : AlgebraicGeometry.Scheme.Cover (AlgebraicGeo
metry.Scheme.precoverage P) X；f : W ⟶ X；AlgebraicGeometry.Scheme.precoverage P。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Cover.Over.isOver_map`：∀ {S : AlgebraicGeometry
.Scheme} {P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme}   {inst 
: P.IsStableUnderBaseChange} {inst_1…

--- 原说明 ---
The pullback of a cover of `S`-schemes along a morphism of `S`-schemes. This is 
not
definitionally equal to `AlgebraicGeometry.Scheme.Cover.pullback₁`, as here we t
ake
the pullback in `Over S`, whose underlying scheme is only isomorphic but not equ
al to the
pullback in `Scheme`.
-/
def Cover.pullbackCoverOver : W.Cover (precoverage P) where
  I₀ := 𝒰.I₀
  X x := (pullback (f.asOver S) ((𝒰.f x).asOver S)).left
  f x := (pullback.fst (f.asOver S) ((𝒰.f x).asOver S)).left
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, fun j ↦ ?_⟩
    · obtain ⟨i, hy⟩ := Cover.exists_eq (𝒰.pullback₁ f) x
      use i
      exact (mem_range_iff_of_surjective ((𝒰.pullback₁ f).f i) _
        ((PreservesPullback.iso (Over.forget S) (f.asOver S) ((𝒰.f _).asOver S)).inv)
        (PreservesPullback.iso_inv_fst _ _ _) x).mp hy
    · dsimp only
      rw [← Over.forget_map, ← PreservesPullback.iso_hom_fst, P.cancel_left_of_respectsIso]
      exact P.pullback_fst _ _ (𝒰.map_prop j)
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (j : 𝒰.I₀) : ((𝒰.pullbackCoverOver S f).X j).Over S where
  hom := (pullback (f.asOver S) ((𝒰.f j).asOver S)).hom

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (𝒰.pullbackCoverOver S f).Over S where
  isOver_map j := { comp_over := by exact Over.w (pullback.fst (f.asOver S) ((𝒰.f j).asOver S)) }

set_option backward.isDefEq.respectTransparency false in
/-- A variant of `AlgebraicGeometry.Scheme.Cover.pullbackCoverOver` with the arguments in the
fiber products flipped. -/
@[simps]
/-
**AlgebraicGeometry.Scheme.Cover.pullbackCoverOver'** 是 Mathlib 中的一个定义，位于命名空间 `A
lgebraicGeometry.Scheme.Cover`。
形式化陈述：{P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme} →   (S : Al
gebraicGeometry.Scheme) →     [inst : P.IsStableUnderBaseChange] →       [inst_1
 : AlgebraicGeometry.Scheme.IsJointlySurjectivePreserving P] →         {X W : Al
gebraicGeometry.Scheme} →           (𝒰 : AlgebraicGeometry.Scheme.Cover (Algebra
icGeometry.Scheme.precoverage P) X) →             (f : W ⟶ X) →               [i
nst_2 : W.Over S] →                 [inst_3 : X.Over S] →                   [Alg
ebraicGeometry.Scheme.Cover.Over S 𝒰] →                     [AlgebraicGeometry.S
cheme.Hom.IsOver f S] →                       AlgebraicGeometry.Scheme.Cover (Al
gebraicGeometry.Scheme.precoverage P) W
参数：S : AlgebraicGeometry.Scheme；𝒰 : AlgebraicGeometry.Scheme.Cover (AlgebraicGeo
metry.Scheme.precoverage P) X；f : W ⟶ X；AlgebraicGeometry.Scheme.precoverage P。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Cover.Over.isOver_map`：∀ {S : AlgebraicGeometry
.Scheme} {P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme}   {inst 
: P.IsStableUnderBaseChange} {inst_1…

--- 原说明 ---
A variant of `AlgebraicGeometry.Scheme.Cover.pullbackCoverOver` with the argumen
ts in the
fiber products flipped.
-/
def Cover.pullbackCoverOver' : W.Cover (precoverage P) where
  I₀ := 𝒰.I₀
  X x := (pullback ((𝒰.f x).asOver S) (f.asOver S)).left
  f x := (pullback.snd ((𝒰.f x).asOver S) (f.asOver S)).left
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, fun j ↦ ?_⟩
    · obtain ⟨i, hy⟩ := Cover.exists_eq (𝒰.pullback₂ f) x
      use i
      exact (mem_range_iff_of_surjective ((𝒰.pullback₂ f).f _) _
        ((PreservesPullback.iso (Over.forget S) ((𝒰.f _).asOver S) (f.asOver S)).inv)
        (PreservesPullback.iso_inv_snd _ _ _) x).mp hy
    · dsimp only
      rw [← Over.forget_map, ← PreservesPullback.iso_hom_snd, P.cancel_left_of_respectsIso]
      exact P.pullback_snd _ _ (𝒰.map_prop j)
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (j : 𝒰.I₀) : ((𝒰.pullbackCoverOver' S f).X j).Over S where
  hom := (pullback ((𝒰.f j).asOver S) (f.asOver S)).hom

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (𝒰.pullbackCoverOver' S f).Over S where
  isOver_map j := { comp_over := by exact Over.w (pullback.snd ((𝒰.f j).asOver S) (f.asOver S)) }

variable {Q : MorphismProperty Scheme.{u}} [Q.HasOfPostcompProperty Q]
  [Q.IsStableUnderBaseChange] [Q.IsStableUnderComposition]

variable (hX : Q (X ↘ S)) (hW : Q (W ↘ S)) (hQ : ∀ j, Q (𝒰.X j ↘ S))

set_option backward.isDefEq.respectTransparency false in
/-- The pullback of a cover of `S`-schemes with `Q` along a morphism of `S`-schemes. This is not
definitionally equal to `AlgebraicGeometry.Scheme.Cover.pullbackCover`, as here we take
the pullback in `Q.Over ⊤ S`, whose underlying scheme is only isomorphic but not equal to the
pullback in `Scheme`. -/
@[simps -isSimp]
/-
**AlgebraicGeometry.Scheme.Cover.pullbackCoverOverProp** 是 Mathlib 中的一个定义，位于命名空间
 `AlgebraicGeometry.Scheme.Cover`。
形式化陈述：{P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme} →   (S : Al
gebraicGeometry.Scheme) →     [inst : P.IsStableUnderBaseChange] →       [inst_1
 : AlgebraicGeometry.Scheme.IsJointlySurjectivePreserving P] →         {X W : Al
gebraicGeometry.Scheme} →           (𝒰 : AlgebraicGeometry.Scheme.Cover (Algebra
icGeometry.Scheme.precoverage P) X) →             (f : W ⟶ X) →               [i
nst_2 : W.Over S] →                 [inst_3 : X.Over S] →                   [ins
t_4 : AlgebraicGeometry.Scheme.Cover.Over S 𝒰] →                     [AlgebraicG
eometry.Scheme.Hom.IsOver f S] →                       {Q : CategoryTheory.Morph
ismProperty AlgebraicGeometry.Scheme} →                         [Q.HasOfPostcomp
Property Q] →                           [Q.IsStableUnderBaseChange] →           
                  [Q.IsStableUnderComposition] →                               Q
 (X ↘ S) →                                 Q (W ↘ S) →                          
         (∀ (j : 𝒰.I₀), Q (𝒰.X j ↘ S)) →                                     Alg
ebraicGeometry.Scheme.Cover (AlgebraicGeometry.Scheme.precoverage P) W
参数：S : AlgebraicGeometry.Scheme；𝒰 : AlgebraicGeometry.Scheme.Cover (AlgebraicGeo
metry.Scheme.precoverage P) X；f : W ⟶ X；X ↘ S；W ↘ S；∀ (j : 𝒰.I₀), Q (𝒰.X j ↘ S)；
AlgebraicGeometry.Scheme.precoverage P。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.instTop`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C], ⊤.IsMultiplicative
· 使用定理 `AlgebraicGeometry.Scheme.Cover.Over.isOver_map`：∀ {S : AlgebraicGeometry
.Scheme} {P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme}   {inst 
: P.IsStableUnderBaseChange} {inst_1…

--- 原说明 ---
The pullback of a cover of `S`-schemes with `Q` along a morphism of `S`-schemes.
 This is not
definitionally equal to `AlgebraicGeometry.Scheme.Cover.pullbackCover`, as here 
we take
the pullback in `Q.Over ⊤ S`, whose underlying scheme is only isomorphic but not
 equal to the
pullback in `Scheme`.
-/
def Cover.pullbackCoverOverProp : W.Cover (precoverage P) where
  I₀ := 𝒰.I₀
  X x := (pullback (f.asOverProp (hX := hW) (hY := hX) S)
    ((𝒰.f x).asOverProp (hX := hQ x) (hY := hX) S)).left
  f x := (pullback.fst (f.asOverProp S) ((𝒰.f x).asOverProp S)).left
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, fun j ↦ ?_⟩
    · obtain ⟨i, hy⟩ := Cover.exists_eq (𝒰.pullback₁ f) x
      use i
      exact (mem_range_iff_of_surjective ((𝒰.pullback₁ f).f i) _
        ((PreservesPullback.iso (MorphismProperty.Over.forget Q _ _ ⋙ Over.forget S)
          (f.asOverProp S) ((𝒰.f _).asOverProp S)).inv)
        (PreservesPullback.iso_inv_fst _ _ _) x).mp hy
    · simp only [← CategoryTheory.Over.forget_map]
      rw [MorphismProperty.Comma.toCommaMorphism_eq_hom,
        ← MorphismProperty.Comma.forget_map, ← Functor.comp_map]
      rw [← PreservesPullback.iso_hom_fst, P.cancel_left_of_respectsIso]
      exact P.pullback_fst _ _ (𝒰.map_prop j)
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (j : 𝒰.I₀) : ((𝒰.pullbackCoverOverProp S f hX hW hQ).X j).Over S where
  hom := (pullback (f.asOverProp (hX := hW) (hY := hX) S)
    ((𝒰.f j).asOverProp (hX := hQ j) (hY := hX) S)).hom

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (𝒰.pullbackCoverOverProp S f hX hW hQ).Over S where
  isOver_map j :=
    { comp_over := by exact (pullback.fst (f.asOverProp S) ((𝒰.f j).asOverProp S)).w }

set_option backward.isDefEq.respectTransparency false in
/-- A variant of `AlgebraicGeometry.Scheme.Cover.pullbackCoverOverProp` with the arguments in the
fiber products flipped. -/
@[simps -isSimp]
/-
**AlgebraicGeometry.Scheme.Cover.pullbackCoverOverProp'** 是 Mathlib 中的一个定义，位于命名空
间 `AlgebraicGeometry.Scheme.Cover`。
形式化陈述：{P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme} →   (S : Al
gebraicGeometry.Scheme) →     [inst : P.IsStableUnderBaseChange] →       [inst_1
 : AlgebraicGeometry.Scheme.IsJointlySurjectivePreserving P] →         {X W : Al
gebraicGeometry.Scheme} →           (𝒰 : AlgebraicGeometry.Scheme.Cover (Algebra
icGeometry.Scheme.precoverage P) X) →             (f : W ⟶ X) →               [i
nst_2 : W.Over S] →                 [inst_3 : X.Over S] →                   [ins
t_4 : AlgebraicGeometry.Scheme.Cover.Over S 𝒰] →                     [AlgebraicG
eometry.Scheme.Hom.IsOver f S] →                       {Q : CategoryTheory.Morph
ismProperty AlgebraicGeometry.Scheme} →                         [Q.HasOfPostcomp
Property Q] →                           [Q.IsStableUnderBaseChange] →           
                  [Q.IsStableUnderComposition] →                               Q
 (X ↘ S) →                                 Q (W ↘ S) →                          
         (∀ (j : 𝒰.I₀), Q (𝒰.X j ↘ S)) →                                     Alg
ebraicGeometry.Scheme.Cover (AlgebraicGeometry.Scheme.precoverage P) W
参数：S : AlgebraicGeometry.Scheme；𝒰 : AlgebraicGeometry.Scheme.Cover (AlgebraicGeo
metry.Scheme.precoverage P) X；f : W ⟶ X；X ↘ S；W ↘ S；∀ (j : 𝒰.I₀), Q (𝒰.X j ↘ S)；
AlgebraicGeometry.Scheme.precoverage P。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.instTop`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C], ⊤.IsMultiplicative
· 使用定理 `AlgebraicGeometry.Scheme.Cover.Over.isOver_map`：∀ {S : AlgebraicGeometry
.Scheme} {P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme}   {inst 
: P.IsStableUnderBaseChange} {inst_1…

--- 原说明 ---
A variant of `AlgebraicGeometry.Scheme.Cover.pullbackCoverOverProp` with the arg
uments in the
fiber products flipped.
-/
def Cover.pullbackCoverOverProp' : W.Cover (precoverage P) where
  I₀ := 𝒰.I₀
  X x := (pullback ((𝒰.f x).asOverProp (hX := hQ x) (hY := hX) S)
    (f.asOverProp (hX := hW) (hY := hX) S)).left
  f x := (pullback.snd ((𝒰.f x).asOverProp S) (f.asOverProp S)).left
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, fun j ↦ ?_⟩
    · obtain ⟨i, hy⟩ := Cover.exists_eq (𝒰.pullback₂ f) x
      use i
      exact (mem_range_iff_of_surjective ((𝒰.pullback₂ f).f i) _
        ((PreservesPullback.iso (MorphismProperty.Over.forget Q _ _ ⋙ Over.forget S)
          ((𝒰.f _).asOverProp S) (f.asOverProp S)).inv)
        (PreservesPullback.iso_inv_snd _ _ _) x).mp hy
    · simp only [← CategoryTheory.Over.forget_map]
      rw [MorphismProperty.Comma.toCommaMorphism_eq_hom,
        ← MorphismProperty.Comma.forget_map, ← Functor.comp_map]
      rw [← PreservesPullback.iso_hom_snd, P.cancel_left_of_respectsIso]
      exact P.pullback_snd _ _ (𝒰.map_prop j)
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (j : 𝒰.I₀) : ((𝒰.pullbackCoverOverProp' S f hX hW hQ).X j).Over S where
  hom := (pullback ((𝒰.f j).asOverProp (hX := hQ j) (hY := hX) S)
    (f.asOverProp (hX := hW) (hY := hX) S)).hom

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (𝒰.pullbackCoverOverProp' S f hX hW hQ).Over S where
  isOver_map j :=
    { comp_over := by exact (pullback.snd ((𝒰.f j).asOverProp S) (f.asOverProp S)).w }

end

variable [P.IsStableUnderComposition]
variable {X : Scheme.{u}} (𝒰 : X.Cover (precoverage P)) (𝒱 : ∀ x, (𝒰.X x).Cover (precoverage P))
  [X.Over S] [𝒰.Over S] [∀ x, (𝒱 x).Over S]

/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (j : (𝒰.bind 𝒱).I₀) : ((𝒰.bind 𝒱).X j).Over S :=
  inferInstanceAs <| ((𝒱 j.1).X j.2).Over S

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X : Scheme.{u}} (𝒰 : X.Cover (precoverage P)) (𝒱 : ∀ x, (𝒰.X x).Cover (precoverage P))
    [X.Over S] [𝒰.Over S] [∀ x, (𝒱 x).Over S] : Cover.Over S (𝒰.bind 𝒱) where
  over := fun ⟨i, j⟩ ↦ inferInstanceAs <| ((𝒱 i).X j).Over S
  isOver_map := fun ⟨i, j⟩ ↦ { comp_over := by simp; rfl }

end AlgebraicGeometry.Scheme

