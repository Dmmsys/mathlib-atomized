/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Sites.Precoverage
public import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# 0-hypercovers

Given a coverage `J` on a category `C`, we define the type
of `0`-hypercovers of an object `S : C`. They consist of a covering family
of morphisms `X i ⟶ S` indexed by a type `I₀` such that the induced presieve is in `J`.

We define this with respect to a coverage and not to a Grothendieck topology, because this
yields more control over the components of the cover.
-/

@[expose] public section

universe w'' w' w v u

namespace CategoryTheory

open Category Limits

variable {C : Type u} [Category.{v} C]

/-- The categorical data that is involved in a `0`-hypercover of an object `S`. This
consists of a family of morphisms `f i : X i ⟶ S` for `i : I₀`. -/
@[ext]
/--
Definition of `PreZeroHypercover` / `PreZeroHypercover` 的定义

English:
structure PreZeroHypercover
  parameters: (S : C)
  axioms and operations (3):
    - I₀ : Type w
    - X((i : I₀)) : C
    - f((i : I₀)) : X i ⟶ S

中文:
结构 PreZeroHypercover
  参数: (S : C)
  公理与运算 (3 个):
    - I₀ : 类型 w
    - X((i : I₀)) : C
    - f((i : I₀)) : X i ⟶ S
-/
structure PreZeroHypercover (S : C) where
  /-- the index type of the covering of `S` -/
  I₀ : Type w
  /-- the objects in the covering of `S` -/
  X (i : I₀) : C
  /-- the morphisms in the covering of `S` -/
  f (i : I₀) : X i ⟶ S

namespace PreZeroHypercover

variable {S T : C} (E : PreZeroHypercover.{w} S) (F : PreZeroHypercover.{w'} S)

/--
Definition of `HasPullbacks` / `HasPullbacks` 的定义

English:
abbreviation HasPullbacks
  body: forall (i₁ i₂ : E.I₀), HasPullback (E.f i₁) (E.f i₂)

中文:
缩写 有Pullbacks
  定义体: forall (i₁ i₂ : E.I₀), HasPullback (E.f i₁) (E.f i₂)

Depends on / 依赖: HasPullback
-/
abbrev HasPullbacks := forall (i₁ i₂ : E.I₀), HasPullback (E.f i₁) (E.f i₂)

/--
Definition of `presieve₀` / `presieve₀` 的定义

English:
abbreviation presieve₀
  signature: : Presieve S
  body: .ofArrows _ E.f

@[simp]

中文:
缩写 presieve₀
  签名: : Presieve S
  定义体: .ofArrows _ E.f

@[simp]

Depends on / 依赖: ofArrows
-/
abbrev presieve₀ : Presieve S := .ofArrows _ E.f

@[simp]
/--
lemma `presieve₀_f` / 引理 `presieve₀_f`

English:
lemma presieve₀_f
  given: (i : E.I₀)
  statement: E.presieve₀ (E.f i)
  proof: ⟨i⟩

grind_pattern presieve₀_f => E.presieve₀ (E.f i)

中文:
引理 presieve₀_f
  条件: (i : E.I₀)
  结论: E.presieve₀ (E.f i)
  证明: ⟨i⟩

grind_pattern presieve₀_f => E.presieve₀ (E.f i)
-/
lemma presieve₀_f (i : E.I₀) : E.presieve₀ (E.f i) := ⟨i⟩

grind_pattern presieve₀_f => E.presieve₀ (E.f i)

/--
Definition of `sieve₀` / `sieve₀` 的定义

English:
abbreviation sieve₀
  signature: : Sieve S
  body: .ofArrows _ E.f

中文:
缩写 sieve₀
  签名: : 筛 S
  定义体: .ofArrows _ E.f

Depends on / 依赖: ofArrows
-/
abbrev sieve₀ : Sieve S := .ofArrows _ E.f

/--
lemma `sieve₀_f` / 引理 `sieve₀_f`

English:
lemma sieve₀_f
  given: (i : E.I₀)
  statement: E.sieve₀ (E.f i)
  proof: ⟨_, 𝟙 _, E.f i, ⟨i⟩, by simp⟩

grind_pattern sieve₀_f => E.sieve₀ (E.f i)

中文:
引理 sieve₀_f
  条件: (i : E.I₀)
  结论: E.sieve₀ (E.f i)
  证明: ⟨_, 𝟙 _, E.f i, ⟨i⟩, by simp⟩

grind_pattern sieve₀_f => E.sieve₀ (E.f i)
-/
lemma sieve₀_f (i : E.I₀) : E.sieve₀ (E.f i) := ⟨_, 𝟙 _, E.f i, ⟨i⟩, by simp⟩

grind_pattern sieve₀_f => E.sieve₀ (E.f i)

/-- The pre-`0`-hypercover defined by a single morphism. -/
@[simps]
/--
Definition of `singleton` / `singleton` 的定义

English:
definition singleton
  signature: (f : S ⟶ T)
  body: PUnit
  X _ := S
  f _ := f

@[simp]

中文:
定义 singleton
  签名: (f : S ⟶ T)
  定义体: PUnit
  X _ := S
  f _ := f

@[simp]
-/
def singleton (f : S ⟶ T) : PreZeroHypercover.{w} T where
  I₀ := PUnit
  X _ := S
  f _ := f

@[simp]
/--
lemma `presieve₀_singleton` / 引理 `presieve₀_singleton`

English:
lemma presieve₀_singleton
  given: (f : S ⟶ T)
  statement: (singleton f).presieve₀ = .singleton f
  proof: by
  simp [singleton, presieve₀, Presieve.ofArrows_pUnit]

中文:
引理 presieve₀_singleton
  条件: (f : S ⟶ T)
  结论: (singleton f).presieve₀ = .singleton f
  证明: by
  simp [singleton, presieve₀, Presieve.ofArrows_pUnit]

Depends on / 依赖: Presieve, Presieve.ofArrows_pUnit, ofArrows_pUnit, singleton
-/
lemma presieve₀_singleton (f : S ⟶ T) : (singleton f).presieve₀ = .singleton f := by
  simp [singleton, presieve₀, Presieve.ofArrows_pUnit]

instance (f : S ⟶ T) : Unique (PreZeroHypercover.singleton f).I₀ :=
inferInstanceAs Unique PUnit

variable (S) in
/-- The empty pre-`0`-hypercover. -/
@[simps]
/--
Definition of `empty` / `empty` 的定义

English:
definition empty
  signature: : PreZeroHypercover.{w} S where
  body: PEmpty
  X := PEmpty.elim
  f i := i.elim

中文:
定义 empty
  签名: : PreZeroHypercover.{w} S where
  定义体: PEmpty
  X := PEmpty.elim
  f i := i.elim

Depends on / 依赖: PEmpty
-/
def empty : PreZeroHypercover.{w} S where
  I₀ := PEmpty
  X := PEmpty.elim
  f i := i.elim

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsEmpty (empty S).I₀
  body: inferInstanceAs IsEmpty PEmpty

@[simp]

中文:
实例 :
  签名: 是空 (empty S).I₀
  定义体: inferInstanceAs IsEmpty PEmpty

@[simp]

Depends on / 依赖: IsEmpty, PEmpty
-/
instance : IsEmpty (empty S).I₀ := inferInstanceAs IsEmpty PEmpty

@[simp]
/--
lemma `presieve₀_empty` / 引理 `presieve₀_empty`

English:
lemma presieve₀_empty
  statement: (empty.{w} S).presieve₀ = ⊥
  proof: by
  grind

中文:
引理 presieve₀_empty
  结论: (empty.{w} S).presieve₀ = ⊥
  证明: by
  grind
-/
lemma presieve₀_empty : (empty.{w} S).presieve₀ = ⊥ := by
  grind

/-- Pullback of a pre-`0`-hypercover along a morphism. The components are `pullback f (E.f i)`. -/
@[simps]
noncomputable
/--
Definition of `pullback₁` / `pullback₁` 的定义

English:
definition pullback₁
  signature: (f : S ⟶ T) (E : PreZeroHypercover.{w} T) [forall i, HasPullback f (E.f i)]
  body: E.I₀
  X i := pullback f (E.f i)
  f _ := pullback.fst _ _

中文:
定义 pullback₁
  签名: (f : S ⟶ T) (E : PreZeroHypercover.{w} T) [对任意 i, HasPullback f (E.f i)]
  定义体: E.I₀
  X i := pullback f (E.f i)
  f _ := pullback.fst _ _
-/
def pullback₁ (f : S ⟶ T) (E : PreZeroHypercover.{w} T) [forall i, HasPullback f (E.f i)] :
    PreZeroHypercover.{w} S where
  I₀ := E.I₀
  X i := pullback f (E.f i)
  f _ := pullback.fst _ _

/-- Pullback of a pre-`0`-hypercover along a morphism. The components are `pullback (E.f i) f`. -/
@[simps]
noncomputable
/--
Definition of `pullback₂` / `pullback₂` 的定义

English:
definition pullback₂
  signature: (f : S ⟶ T) (E : PreZeroHypercover.{w} T) [forall i, HasPullback (E.f i) f]
  body: E.I₀
  X i := pullback (E.f i) f
  f _ := pullback.snd _ _

中文:
定义 pullback₂
  签名: (f : S ⟶ T) (E : PreZeroHypercover.{w} T) [对任意 i, HasPullback (E.f i) f]
  定义体: E.I₀
  X i := pullback (E.f i) f
  f _ := pullback.snd _ _
-/
def pullback₂ (f : S ⟶ T) (E : PreZeroHypercover.{w} T) [forall i, HasPullback (E.f i) f] :
    PreZeroHypercover.{w} S where
  I₀ := E.I₀
  X i := pullback (E.f i) f
  f _ := pullback.snd _ _

/--
lemma `presieve₀_pullback₁` / 引理 `presieve₀_pullback₁`

English:
lemma presieve₀_pullback₁
  given: (f : S ⟶ T) (E : PreZeroHypercover.{w} T) [forall i, HasPullback (E.f i) f]
  proof: by
  refine le_antisymm ?_ ?_
  · rintro - - ⟨i⟩
    use _, _, i
  · rintro W g ⟨-, -, ⟨i⟩⟩
    use i

中文:
引理 presieve₀_pullback₁
  条件: (f : S ⟶ T) (E : PreZeroHypercover.{w} T) [对任意 i, HasPullback (E.f i) f]
  证明: by
  refine le_antisymm ?_ ?_
  · rintro - - ⟨i⟩
    use _, _, i
  · rintro W g ⟨-, -, ⟨i⟩⟩
    use i

Depends on / 依赖: le_antisymm
-/
lemma presieve₀_pullback₁ (f : S ⟶ T) (E : PreZeroHypercover.{w} T) [forall i, HasPullback (E.f i) f] :
    presieve₀ (E.pullback₂ f) = E.presieve₀.pullbackArrows f := by
  refine le_antisymm ?_ ?_
  · rintro - - ⟨i⟩
    use _, _, i
  · rintro W g ⟨-, -, ⟨i⟩⟩
    use i

/-- If `{Uᵢ}` covers `X`, this is the pre-`0`-hypercover of `X ×[Z] Y` given by `{Uᵢ ×[Z] Y}`. -/
@[simps]
/--
Definition of `pullbackCoverOfLeft` / `pullbackCoverOfLeft` 的定义

English:
definition pullbackCoverOfLeft
  signature: {X : C} (E : PreZeroHypercover X) {Y Z : C}
  body: E.I₀
  X i := pullback (E.f i ≫ f) g
  f i := pullback.map _ _ _ _ (E.f i) (𝟙 Y) (𝟙 Z) (by simp) (by simp)

中文:
定义 pullbackCoverOfLeft
  签名: {X : C} (E : PreZeroHypercover X) {Y Z : C}
  定义体: E.I₀
  X i := pullback (E.f i ≫ f) g
  f i := pullback.map _ _ _ _ (E.f i) (𝟙 Y) (𝟙 Z) (by simp) (by simp)
-/
noncomputable def pullbackCoverOfLeft {X : C} (E : PreZeroHypercover X) {Y Z : C}
    (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] [forall i, HasPullback (E.f i ≫ f) g] :
    PreZeroHypercover (pullback f g) where
  I₀ := E.I₀
  X i := pullback (E.f i ≫ f) g
  f i := pullback.map _ _ _ _ (E.f i) (𝟙 Y) (𝟙 Z) (by simp) (by simp)

/-- If `{Uᵢ}` covers `Y`, this is the pre-`0`-hypercover of `X ×[Z] Y` given by `{X ×[Z] Uᵢ}`. -/
@[simps]
/--
Definition of `pullbackCoverOfRight` / `pullbackCoverOfRight` 的定义

English:
definition pullbackCoverOfRight
  signature: {Y : C} (E : PreZeroHypercover.{w} Y) {X Z : C}
  body: E.I₀
  X i := pullback f (E.f i ≫ g)
  f i := pullback.map _ _ _ _ (𝟙 X) (E.f i) (𝟙 Z) (by simp) (by simp)

中文:
定义 pullbackCoverOfRight
  签名: {Y : C} (E : PreZeroHypercover.{w} Y) {X Z : C}
  定义体: E.I₀
  X i := pullback f (E.f i ≫ g)
  f i := pullback.map _ _ _ _ (𝟙 X) (E.f i) (𝟙 Z) (by simp) (by simp)

Depends on / 依赖: DecidableRel
-/
noncomputable def pullbackCoverOfRight {Y : C} (E : PreZeroHypercover.{w} Y) {X Z : C}
    (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] [forall i, HasPullback f (E.f i ≫ g)] :
    PreZeroHypercover.{w} (pullback f g) where
  I₀ := E.I₀
  X i := pullback f (E.f i ≫ g)
  f i := pullback.map _ _ _ _ (𝟙 X) (E.f i) (𝟙 Z) (by simp) (by simp)

/-- Refining each component of a pre-`0`-hypercover yields a refined pre-`0`-hypercover of the
base. -/
@[simps]
/--
Definition of `bind` / `bind` 的定义

English:
definition bind
  signature: (E : PreZeroHypercover.{w} T) (F : forall i, PreZeroHypercover.{w'} (E.X i))
  body: Σ (i : E.I₀), (F i).I₀
  X ij := (F ij.1).X ij.2
  f ij := (F ij.1).f ij.2 ≫ E.f ij.1

中文:
定义 bind
  签名: (E : PreZeroHypercover.{w} T) (F : 对任意 i, PreZeroHypercover.{w'} (E.X i))
  定义体: Σ (i : E.I₀), (F i).I₀
  X ij := (F ij.1).X ij.2
  f ij := (F ij.1).f ij.2 ≫ E.f ij.1

Depends on / 依赖: DecidableRel, G.Adj, H.Adj
-/
def bind (E : PreZeroHypercover.{w} T) (F : forall i, PreZeroHypercover.{w'} (E.X i)) :
    PreZeroHypercover.{max w w'} T where
  I₀ := Σ (i : E.I₀), (F i).I₀
  X ij := (F ij.1).X ij.2
  f ij := (F ij.1).f ij.2 ≫ E.f ij.1

/-- Restrict the indexing type to `ι` by precomposing with a function `ι → E.I₀`. -/
@[simps]
/--
Definition of `restrictIndex` / `restrictIndex` 的定义

English:
definition restrictIndex
  signature: (E : PreZeroHypercover.{w} T) {ι : Type w'} (f : ι -> E.I₀)
  body: ι
  X := E.X ∘ f
  f i := E.f (f i)

@[simp]

中文:
定义 restrictIndex
  签名: (E : PreZeroHypercover.{w} T) {ι : 类型 w'} (f : ι -> E.I₀)
  定义体: ι
  X := E.X ∘ f
  f i := E.f (f i)

@[simp]

Depends on / 依赖: DecidableRel, G.Adj, H.Adj
-/
def restrictIndex (E : PreZeroHypercover.{w} T) {ι : Type w'} (f : ι -> E.I₀) :
    PreZeroHypercover.{w'} T where
  I₀ := ι
  X := E.X ∘ f
  f i := E.f (f i)

@[simp]
/--
lemma `presieve₀_restrictIndex_equiv` / 引理 `presieve₀_restrictIndex_equiv`

English:
lemma presieve₀_restrictIndex_equiv
  given: {ι : Type w'} (e : ι ≃ E.I₀)
  proof: by
  refine le_antisymm (fun Y g ⟨i⟩ => ⟨e i⟩) fun Y g ⟨i⟩ => ?_
  obtain ⟨i, rfl⟩ := e.surjective i
  exact ⟨i⟩

@[simp]

中文:
引理 presieve₀_restrictIndex_equiv
  条件: {ι : 类型 w'} (e : ι ≃ E.I₀)
  证明: by
  refine le_antisymm (fun Y g ⟨i⟩ => ⟨e i⟩) fun Y g ⟨i⟩ => ?_
  obtain ⟨i, rfl⟩ := e.surjective i
  exact ⟨i⟩

@[simp]

Depends on / 依赖: e.surjective, le_antisymm, surjective
-/
lemma presieve₀_restrictIndex_equiv {ι : Type w'} (e : ι ≃ E.I₀) :
    (E.restrictIndex e).presieve₀ = E.presieve₀ := by
  refine le_antisymm (fun Y g ⟨i⟩ => ⟨e i⟩) fun Y g ⟨i⟩ => ?_
  obtain ⟨i, rfl⟩ := e.surjective i
  exact ⟨i⟩

@[simp]
/--
lemma `presieve₀_restrictIndex_le` / 引理 `presieve₀_restrictIndex_le`

English:
lemma presieve₀_restrictIndex_le
  given: {ι : Type*} (f : ι -> E.I₀)
  proof: by
  rw [Presieve.ofArrows_le_iff]
  intro i
  exact .mk _

中文:
引理 presieve₀_restrictIndex_le
  条件: {ι : 类型} (f : ι -> E.I₀)
  证明: by
  rw [Presieve.ofArrows_le_iff]
  intro i
  exact .mk _

Depends on / 依赖: DecidableRel, Presieve, Presieve.ofArrows_le_iff, ofArrows_le_iff
-/
lemma presieve₀_restrictIndex_le {ι : Type*} (f : ι -> E.I₀) :
    (E.restrictIndex f).presieve₀ <= E.presieve₀ := by
  rw [Presieve.ofArrows_le_iff]
  intro i
  exact .mk _

/-- Replace the indexing type of a pre-`0`-hypercover. -/
@[simps!]
/--
Definition of `reindex` / `reindex` 的定义

English:
definition reindex
  signature: (E : PreZeroHypercover.{w} T) {ι : Type w'} (e : ι ≃ E.I₀)
  body: E.restrictIndex e

@[simp]

中文:
定义 reindex
  签名: (E : PreZeroHypercover.{w} T) {ι : 类型 w'} (e : ι ≃ E.I₀)
  定义体: E.restrictIndex e

@[simp]

Depends on / 依赖: DecidableRel, E.restrictIndex, G.Adj, restrictIndex
-/
def reindex (E : PreZeroHypercover.{w} T) {ι : Type w'} (e : ι ≃ E.I₀) :
    PreZeroHypercover.{w'} T :=
  E.restrictIndex e

@[simp]
/--
lemma `presieve₀_reindex` / 引理 `presieve₀_reindex`

English:
lemma presieve₀_reindex
  given: {ι : Type w'} (e : ι ≃ E.I₀)
  statement: (E.reindex e).presieve₀ = E.presieve₀
  proof: by
  simp [reindex]

#adaptation_note

中文:
引理 presieve₀_reindex
  条件: {ι : 类型 w'} (e : ι ≃ E.I₀)
  结论: (E.reindex e).presieve₀ = E.presieve₀
  证明: by
  simp [reindex]

#adaptation_note

Depends on / 依赖: reindex
-/
lemma presieve₀_reindex {ι : Type w'} (e : ι ≃ E.I₀) : (E.reindex e).presieve₀ = E.presieve₀ := by
  simp [reindex]

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- Pairwise intersection of two pre-`0`-hypercovers. -/
@[simps!]
noncomputable
/--
Definition of `inter` / `inter` 的定义

English:
definition inter
  signature: (E : PreZeroHypercover.{w} T) (F : PreZeroHypercover.{w'} T)
  body: (E.bind (fun i => F.pullback₁ (E.f i))).reindex (Equiv.sigmaEquivProd _ _).symm

中文:
定义 inter
  签名: (E : PreZeroHypercover.{w} T) (F : PreZeroHypercover.{w'} T)
  定义体: (E.bind (fun i => F.pullback₁ (E.f i))).reindex (Equiv.sigmaEquivProd _ _).symm

Depends on / 依赖: E.bind, Equiv.sigmaEquivProd, F.pullback, reindex, sigmaEquivProd
-/
def inter (E : PreZeroHypercover.{w} T) (F : PreZeroHypercover.{w'} T)
    [forall i j, HasPullback (E.f i) (F.f j)] :
    PreZeroHypercover.{max w w'} T :=
  (E.bind (fun i => F.pullback₁ (E.f i))).reindex (Equiv.sigmaEquivProd _ _).symm

/--
lemma `inter_def` / 引理 `inter_def`

English:
lemma inter_def
  given: [forall i j, HasPullback (E.f i) (F.f j)]
  proof: rfl

中文:
引理 inter_def
  条件: [对任意 i j, HasPullback (E.f i) (F.f j)]
  证明: rfl
-/
lemma inter_def [forall i j, HasPullback (E.f i) (F.f j)] :
    E.inter F = (E.bind (fun i => F.pullback₁ (E.f i))).reindex (Equiv.sigmaEquivProd _ _).symm :=
  rfl

/-- Disjoint union of two pre-`0`-hypercovers. -/
@[simps I₀, simps -isSimp X f]
/--
Definition of `sum` / `sum` 的定义

English:
definition sum
  signature: {X : C} (E : PreZeroHypercover.{w} X) (F : PreZeroHypercover.{w'} X)
  body: E.I₀ oplus F.I₀
  X := Sum.elim E.X F.X
  f
    | .inl i => E.f i
    | .inr i => F.f i

中文:
定义 求和
  签名: {X : C} (E : PreZeroHypercover.{w} X) (F : PreZeroHypercover.{w'} X)
  定义体: E.I₀ oplus F.I₀
  X := Sum.elim E.X F.X
  f
    | .inl i => E.f i
    | .inr i => F.f i
-/
def sum {X : C} (E : PreZeroHypercover.{w} X) (F : PreZeroHypercover.{w'} X) :
    PreZeroHypercover.{max w w'} X where
  I₀ := E.I₀ oplus F.I₀
  X := Sum.elim E.X F.X
  f
    | .inl i => E.f i
    | .inr i => F.f i

/--
lemma `sum_X_inl` / 引理 `sum_X_inl`

English:
lemma sum_X_inl
  given: (i : E.I₀)
  statement: (E.sum F).X (.inl i) = E.X i
  proof: rfl

中文:
引理 sum_X_inl
  条件: (i : E.I₀)
  结论: (E.求和 F).X (.inl i) = E.X i
  证明: rfl
-/
@[simp] lemma sum_X_inl (i : E.I₀) : (E.sum F).X (.inl i) = E.X i := rfl

/--
lemma `sum_X_inr` / 引理 `sum_X_inr`

English:
lemma sum_X_inr
  given: (i : F.I₀)
  statement: (E.sum F).X (.inr i) = F.X i
  proof: rfl

中文:
引理 sum_X_inr
  条件: (i : F.I₀)
  结论: (E.求和 F).X (.inr i) = F.X i
  证明: rfl
-/
@[simp] lemma sum_X_inr (i : F.I₀) : (E.sum F).X (.inr i) = F.X i := rfl

/--
lemma `sum_f_inl` / 引理 `sum_f_inl`

English:
lemma sum_f_inl
  given: (i : E.I₀)
  statement: (E.sum F).f (.inl i) = E.f i
  proof: rfl

中文:
引理 sum_f_inl
  条件: (i : E.I₀)
  结论: (E.求和 F).f (.inl i) = E.f i
  证明: rfl
-/
@[simp] lemma sum_f_inl (i : E.I₀) : (E.sum F).f (.inl i) = E.f i := rfl

/--
lemma `sum_f_inr` / 引理 `sum_f_inr`

English:
lemma sum_f_inr
  given: (i : F.I₀)
  statement: (E.sum F).f (.inr i) = F.f i
  proof: rfl

@[simp]

中文:
引理 sum_f_inr
  条件: (i : F.I₀)
  结论: (E.求和 F).f (.inr i) = F.f i
  证明: rfl

@[simp]
-/
@[simp] lemma sum_f_inr (i : F.I₀) : (E.sum F).f (.inr i) = F.f i := rfl

@[simp]
/--
lemma `presieve₀_sum` / 引理 `presieve₀_sum`

English:
lemma presieve₀_sum
  statement: (E.sum F).presieve₀ = E.presieve₀ ⊔ F.presieve₀
  proof: by
  rw [presieve₀]; rw [presieve₀]; rw [presieve₀]
  apply le_antisymm
  · intro Z g ⟨i⟩
    cases i
    · exact Or.inl (.mk _)
    · exact Or.inr (.mk _)
  · rintro Z g (⟨⟨i⟩⟩ | ⟨⟨i⟩⟩)
    · exact ⟨Sum.inl i⟩
    · exact ⟨Sum.inr i⟩

中文:
引理 presieve₀_sum
  结论: (E.求和 F).presieve₀ = E.presieve₀ ⊔ F.presieve₀
  证明: by
  rw [presieve₀]; rw [presieve₀]; rw [presieve₀]
  apply le_antisymm
  · intro Z g ⟨i⟩
    cases i
    · exact Or.inl (.mk _)
    · exact Or.inr (.mk _)
  · rintro Z g (⟨⟨i⟩⟩ | ⟨⟨i⟩⟩)
    · exact ⟨Sum.inl i⟩
    · exact ⟨Sum.inr i⟩

Depends on / 依赖: Or.inl, Or.inr, Sum.inl, Sum.inr, le_antisymm
-/
lemma presieve₀_sum : (E.sum F).presieve₀ = E.presieve₀ ⊔ F.presieve₀ := by
  rw [presieve₀]; rw [presieve₀]; rw [presieve₀]
  apply le_antisymm
  · intro Z g ⟨i⟩
    cases i
    · exact Or.inl (.mk _)
    · exact Or.inr (.mk _)
  · rintro Z g (⟨⟨i⟩⟩ | ⟨⟨i⟩⟩)
    · exact ⟨Sum.inl i⟩
    · exact ⟨Sum.inr i⟩

/-- Add a morphism to a pre-`0`-hypercover. -/
@[simps! I₀]
/--
Definition of `add` / `add` 的定义

English:
definition add
  signature: (E : PreZeroHypercover.{w} S) {T : C} (f : T ⟶ S)
  body: (E.sum (.singleton f)).reindex (Equiv.optionEquivSumPUnit.{0} E.I₀)

中文:
定义 add
  签名: (E : PreZeroHypercover.{w} S) {T : C} (f : T ⟶ S)
  定义体: (E.sum (.singleton f)).reindex (Equiv.optionEquivSumPUnit.{0} E.I₀)

Depends on / 依赖: E.sum, Equiv.optionEquivSumPUnit, optionEquivSumPUnit, reindex, singleton
-/
def add (E : PreZeroHypercover.{w} S) {T : C} (f : T ⟶ S) : PreZeroHypercover.{w} S :=
  (E.sum (.singleton f)).reindex (Equiv.optionEquivSumPUnit.{0} E.I₀)

/--
lemma `add_X_some` / 引理 `add_X_some`

English:
lemma add_X_some
  given: {T : C} (f : T ⟶ S) (i : E.I₀)
  statement: (E.add f).X (some i) = E.X i
  proof: rfl

中文:
引理 add_X_some
  条件: {T : C} (f : T ⟶ S) (i : E.I₀)
  结论: (E.add f).X (some i) = E.X i
  证明: rfl
-/
@[simp] lemma add_X_some {T : C} (f : T ⟶ S) (i : E.I₀) : (E.add f).X (some i) = E.X i := rfl

/--
lemma `add_X_none` / 引理 `add_X_none`

English:
lemma add_X_none
  given: {T : C} (f : T ⟶ S)
  statement: (E.add f).X none = T
  proof: rfl

中文:
引理 add_X_none
  条件: {T : C} (f : T ⟶ S)
  结论: (E.add f).X none = T
  证明: rfl
-/
@[simp] lemma add_X_none {T : C} (f : T ⟶ S) : (E.add f).X none = T := rfl

/--
lemma `add_f_some` / 引理 `add_f_some`

English:
lemma add_f_some
  given: {T : C} (f : T ⟶ S) (i : E.I₀)
  statement: (E.add f).f (some i) = E.f i
  proof: rfl

中文:
引理 add_f_some
  条件: {T : C} (f : T ⟶ S) (i : E.I₀)
  结论: (E.add f).f (some i) = E.f i
  证明: rfl
-/
@[simp] lemma add_f_some {T : C} (f : T ⟶ S) (i : E.I₀) : (E.add f).f (some i) = E.f i := rfl

/--
lemma `add_f_nome` / 引理 `add_f_nome`

English:
lemma add_f_nome
  given: {T : C} (f : T ⟶ S)
  statement: (E.add f).f none = f
  proof: rfl

中文:
引理 add_f_nome
  条件: {T : C} (f : T ⟶ S)
  结论: (E.add f).f none = f
  证明: rfl
-/
@[simp] lemma add_f_nome {T : C} (f : T ⟶ S) : (E.add f).f none = f := rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `presieve₀_add` / 引理 `presieve₀_add`

English:
lemma presieve₀_add
  given: {T : C} (f : T ⟶ S)
  proof: by
  simp [add, presieve₀_reindex, presieve₀_sum]

中文:
引理 presieve₀_add
  条件: {T : C} (f : T ⟶ S)
  证明: by
  simp [add, presieve₀_reindex, presieve₀_sum]
-/
@[simp] lemma presieve₀_add {T : C} (f : T ⟶ S) :
    (E.add f).presieve₀ = E.presieve₀ ⊔ .singleton f := by
  simp [add, presieve₀_reindex, presieve₀_sum]

/-- The single object pre-`0`-hypercover obtained from taking the coproduct of the components. -/
@[simps I₀ X, simps -isSimp f, implicit_reducible]
/--
Definition of `sigmaOfIsColimit` / `sigmaOfIsColimit` 的定义

English:
definition sigmaOfIsColimit
  signature: (E : PreZeroHypercover.{w} S) {c : Cofan E.X} (hc : IsColimit c)
  body: PUnit
  X _ := c.pt
  f _ := Cofan.IsColimit.desc hc E.f

@[reassoc (attr := simp)]

中文:
定义 sigmaOfIsColimit
  签名: (E : PreZeroHypercover.{w} S) {c : Cofan E.X} (hc : 是余极限 c)
  定义体: PUnit
  X _ := c.pt
  f _ := Cofan.IsColimit.desc hc E.f

@[reassoc (attr := simp)]
-/
def sigmaOfIsColimit (E : PreZeroHypercover.{w} S) {c : Cofan E.X} (hc : IsColimit c) :
    PreZeroHypercover.{w} S where
  I₀ := PUnit
  X _ := c.pt
  f _ := Cofan.IsColimit.desc hc E.f

@[reassoc (attr := simp)]
/--
lemma `inj_sigmaOfIsColimit_f` / 引理 `inj_sigmaOfIsColimit_f`

English:
lemma inj_sigmaOfIsColimit_f
  statement: (E : PreZeroHypercover.{w} S) {c : Cofan E.X} (hc : IsColimit c)
  proof: by
  simp [PreZeroHypercover.sigmaOfIsColimit]

@[simp]

中文:
引理 inj_sigmaOfIsColimit_f
  结论: (E : PreZeroHypercover.{w} S) {c : Cofan E.X} (hc : 是余极限 c)
  证明: by
  simp [PreZeroHypercover.sigmaOfIsColimit]

@[simp]

Depends on / 依赖: PreZeroHypercover, PreZeroHypercover.sigmaOfIsColimit, sigmaOfIsColimit
-/
lemma inj_sigmaOfIsColimit_f (E : PreZeroHypercover.{w} S) {c : Cofan E.X} (hc : IsColimit c)
    (i : E.I₀) (r : PUnit) :
    c.inj i ≫ (E.sigmaOfIsColimit hc).f r = E.f i := by
  simp [PreZeroHypercover.sigmaOfIsColimit]

@[simp]
/--
lemma `presieve₀_sigmaOfIsColimit` / 引理 `presieve₀_sigmaOfIsColimit`

English:
lemma presieve₀_sigmaOfIsColimit
  given: (E : PreZeroHypercover.{w} S) {c : Cofan E.X} (hc : IsColimit c)
  proof: Presieve.ofArrows_pUnit _

中文:
引理 presieve₀_sigmaOfIsColimit
  条件: (E : PreZeroHypercover.{w} S) {c : Cofan E.X} (hc : 是余极限 c)
  证明: Presieve.ofArrows_pUnit _

Depends on / 依赖: Presieve, Presieve.ofArrows_pUnit, ofArrows_pUnit
-/
lemma presieve₀_sigmaOfIsColimit (E : PreZeroHypercover.{w} S) {c : Cofan E.X} (hc : IsColimit c) :
    (E.sigmaOfIsColimit hc).presieve₀ = Presieve.singleton (Cofan.IsColimit.desc hc E.f) :=
  Presieve.ofArrows_pUnit _

section Category

variable {E : PreZeroHypercover.{w} S} {F : PreZeroHypercover.{w'} S}

/-- A morphism of pre-`0`-hypercovers of `S` is a family of refinement morphisms commuting
with the structure morphisms of `E` and `F`. -/
@[ext]
/--
Definition of `Hom` / `Hom` 的定义

English:
structure Hom
  parameters: (E : PreZeroHypercover.{w} S) (F : PreZeroHypercover.{w'} S)
  axioms and operations (3):
    - s₀((i : E.I₀)) : F.I₀
    - h₀((i : E.I₀)) : E.X i ⟶ F.X (s₀ i)
    - w₀((i : E.I₀)) : h₀ i ≫ F.f (s₀ i) = E.f i  [default: by cat_disch]

中文:
结构 态射
  参数: (E : PreZeroHypercover.{w} S) (F : PreZeroHypercover.{w'} S)
  公理与运算 (3 个):
    - s₀((i : E.I₀)) : F.I₀
    - h₀((i : E.I₀)) : E.X i ⟶ F.X (s₀ i)
    - w₀((i : E.I₀)) : h₀ i ≫ F.f (s₀ i) = E.f i  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
structure Hom (E : PreZeroHypercover.{w} S) (F : PreZeroHypercover.{w'} S) where
  /-- The map between indexing types of the coverings of `S` -/
  s₀ (i : E.I₀) : F.I₀
  /-- The refinement morphisms between objects in the coverings of `S`. -/
  h₀ (i : E.I₀) : E.X i ⟶ F.X (s₀ i)
  w₀ (i : E.I₀) : h₀ i ≫ F.f (s₀ i) = E.f i := by cat_disch

attribute [reassoc (attr := simp)] Hom.w₀

/-- The identity refinement of a pre-`0`-hypercover. -/
@[simps]
/--
Definition of `Hom.id` / `Hom.id` 的定义

English:
definition Hom.id
  signature: (E : PreZeroHypercover S)
  body: _root_.id
  h₀ _ := 𝟙 _

中文:
定义 态射.id
  签名: (E : PreZeroHypercover S)
  定义体: _root_.id
  h₀ _ := 𝟙 _
-/
def Hom.id (E : PreZeroHypercover S) : Hom E E where
  s₀ := _root_.id
  h₀ _ := 𝟙 _

variable {G : PreZeroHypercover S}

/-- Composition of refinement morphisms of pre-`0`-hypercovers. -/
@[simps]
/--
Definition of `Hom.comp` / `Hom.comp` 的定义

English:
definition Hom.comp
  signature: (f : E.Hom F) (g : F.Hom G)
  body: g.s₀ ∘ f.s₀
  h₀ i := f.h₀ i ≫ g.h₀ _

中文:
定义 态射.comp
  签名: (f : E.态射 F) (g : F.态射 G)
  定义体: g.s₀ ∘ f.s₀
  h₀ i := f.h₀ i ≫ g.h₀ _
-/
def Hom.comp (f : E.Hom F) (g : F.Hom G) : E.Hom G where
  s₀ := g.s₀ ∘ f.s₀
  h₀ i := f.h₀ i ≫ g.h₀ _

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simps! id_s₀ id_h₀ comp_s₀ comp_h₀]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category (PreZeroHypercover S)
  body: Hom
  id E := Hom.id E
  comp f g := f.comp g

中文:
实例 :
  签名: 范畴 (PreZeroHypercover S)
  定义体: Hom
  id E := Hom.id E
  comp f g := f.comp g
-/
instance : Category (PreZeroHypercover S) where
  Hom := Hom
  id E := Hom.id E
  comp f g := f.comp g

/--
lemma `Hom.ext'` / 引理 `Hom.ext'`

English:
lemma Hom.ext'
  statement: {E : PreZeroHypercover.{w} S} {F : PreZeroHypercover.{w'} S}
  proof: by
  cases f
  cases g
  simp only at hs
  cat_disch

中文:
引理 态射.ext'
  结论: {E : PreZeroHypercover.{w} S} {F : PreZeroHypercover.{w'} S}
  证明: by
  cases f
  cases g
  simp only at hs
  cat_disch
-/
lemma Hom.ext' {E : PreZeroHypercover.{w} S} {F : PreZeroHypercover.{w'} S}
    {f g : E.Hom F} (hs : f.s₀ = g.s₀) (hh : forall i, f.h₀ i = g.h₀ i ≫ eqToHom (by rw [hs])) :
    f = g := by
  cases f
  cases g
  simp only at hs
  cat_disch

/--
lemma `Hom.ext'_iff` / 引理 `Hom.ext'_iff`

English:
lemma Hom.ext'_iff
  statement: {E : PreZeroHypercover.{w} S} {F : PreZeroHypercover.{w'} S}
  proof: ⟨fun h => h ▸ by simp, fun ⟨hs, hh⟩ => Hom.ext' hs hh⟩

中文:
引理 态射.ext'_iff
  结论: {E : PreZeroHypercover.{w} S} {F : PreZeroHypercover.{w'} S}
  证明: ⟨fun h => h ▸ by simp, fun ⟨hs, hh⟩ => Hom.ext' hs hh⟩
-/
lemma Hom.ext'_iff {E : PreZeroHypercover.{w} S} {F : PreZeroHypercover.{w'} S}
    {f g : E.Hom F} :
    f = g ↔ exists (hs : f.s₀ = g.s₀), forall i, f.h₀ i = g.h₀ i ≫ eqToHom (by rw [hs]) :=
  ⟨fun h => h ▸ by simp, fun ⟨hs, hh⟩ => Hom.ext' hs hh⟩

set_option backward.defeqAttrib.useBackward true in
/-- Constructor for isomorphisms of pre-`0`-hypercovers. -/
@[simps]
/--
Definition of `isoMk` / `isoMk` 的定义

English:
definition isoMk
  signature: {S : C} {E F : PreZeroHypercover.{w} S}
  body: s₀
  hom.h₀ i := (h₀ i).hom
  inv.s₀ := s₀.symm
  inv.h₀ i := eqToHom (by simp) ≫ (h₀ _).inv
  inv.w₀ i := by
    obtain ⟨i, rfl⟩ := s₀.surjective i
    simp only [← cancel_epi (h₀ i).hom, w₀, Category.assoc, Equiv.symm_apply_apply,
      eqToHom_iso_hom_naturality_assoc, Iso.hom_inv_id_assoc]
    r

中文:
定义 isoMk
  签名: {S : C} {E F : PreZeroHypercover.{w} S}
  定义体: s₀
  hom.h₀ i := (h₀ i).hom
  inv.s₀ := s₀.symm
  inv.h₀ i := eqToHom (by simp) ≫ (h₀ _).inv
  inv.w₀ i := by
    obtain ⟨i, rfl⟩ := s₀.surjective i
    simp only [← cancel_epi (h₀ i).hom, w₀, Category.assoc, Equiv.symm_apply_apply,
      eqToHom_iso_hom_naturality_assoc, Iso.hom_inv_id_assoc]
    r

Depends on / 依赖: Category, Category.assoc, CategoryTheory, CategoryTheory.eqToHom_naturality, Equiv.symm_apply_apply, Hom.ext, Iso.hom_inv_id_assoc, cancel_epi, cat_disch, eqToHom, eqToHom_iso_hom_naturality_assoc, eqToHom_naturality, hom.h, hom.s, hom_inv_id, hom_inv_id_assoc, inv.h, inv.s, inv.w, inv_hom_id
-/
def isoMk {S : C} {E F : PreZeroHypercover.{w} S}
    (s₀ : E.I₀ ≃ F.I₀) (h₀ : forall i, E.X i ≅ F.X (s₀ i))
    (w₀ : forall i, (h₀ i).hom ≫ F.f _ = E.f _ := by cat_disch) :
    E ≅ F where
  hom.s₀ := s₀
  hom.h₀ i := (h₀ i).hom
  inv.s₀ := s₀.symm
  inv.h₀ i := eqToHom (by simp) ≫ (h₀ _).inv
  inv.w₀ i := by
    obtain ⟨i, rfl⟩ := s₀.surjective i
    simp only [← cancel_epi (h₀ i).hom, w₀, Category.assoc, Equiv.symm_apply_apply,
      eqToHom_iso_hom_naturality_assoc, Iso.hom_inv_id_assoc]
    rw [← CategoryTheory.eqToHom_naturality _ (by simp)]
    simp
  hom_inv_id := Hom.ext' (by ext; simp) (fun i => by simp)
  inv_hom_id := Hom.ext' (by ext; simp) (fun i => by simp)

@[simp]
/--
lemma `hom_inv_s₀_apply` / 引理 `hom_inv_s₀_apply`

English:
lemma hom_inv_s₀_apply
  given: {E F : PreZeroHypercover.{w} S} (e : E ≅ F) (i : E.I₀)
  proof: congr($(e.hom_inv_id).s₀ i)

@[simp]

中文:
引理 hom_inv_s₀_apply
  条件: {E F : PreZeroHypercover.{w} S} (e : E ≅ F) (i : E.I₀)
  证明: congr($(e.hom_inv_id).s₀ i)

@[simp]

Depends on / 依赖: e.hom_inv_id, hom_inv_id
-/
lemma hom_inv_s₀_apply {E F : PreZeroHypercover.{w} S} (e : E ≅ F) (i : E.I₀) :
    e.inv.s₀ (e.hom.s₀ i) = i :=
  congr($(e.hom_inv_id).s₀ i)

@[simp]
/--
lemma `inv_hom_s₀_apply` / 引理 `inv_hom_s₀_apply`

English:
lemma inv_hom_s₀_apply
  given: {E F : PreZeroHypercover.{w} S} (e : E ≅ F) (i : F.I₀)
  proof: congr($(e.inv_hom_id).s₀ i)

中文:
引理 inv_hom_s₀_apply
  条件: {E F : PreZeroHypercover.{w} S} (e : E ≅ F) (i : F.I₀)
  证明: congr($(e.inv_hom_id).s₀ i)

Depends on / 依赖: e.inv_hom_id, inv_hom_id
-/
lemma inv_hom_s₀_apply {E F : PreZeroHypercover.{w} S} (e : E ≅ F) (i : F.I₀) :
    e.hom.s₀ (e.inv.s₀ i) = i :=
  congr($(e.inv_hom_id).s₀ i)

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/--
lemma `hom_inv_h₀` / 引理 `hom_inv_h₀`

English:
lemma hom_inv_h₀
  given: {E F : PreZeroHypercover.{w} S} (e : E ≅ F) (i : E.I₀)
  proof: by
  obtain ⟨hs, hh⟩ := Hom.ext'_iff.mp e.hom_inv_id
  simpa using hh i

中文:
引理 hom_inv_h₀
  条件: {E F : PreZeroHypercover.{w} S} (e : E ≅ F) (i : E.I₀)
  证明: by
  obtain ⟨hs, hh⟩ := Hom.ext'_iff.mp e.hom_inv_id
  simpa using hh i

Depends on / 依赖: Hom.ext, _iff, _iff.mp, e.hom_inv_id, hom_inv_id
-/
lemma hom_inv_h₀ {E F : PreZeroHypercover.{w} S} (e : E ≅ F) (i : E.I₀) :
    e.hom.h₀ i ≫ e.inv.h₀ (e.hom.s₀ i) = eqToHom (by simp) := by
  obtain ⟨hs, hh⟩ := Hom.ext'_iff.mp e.hom_inv_id
  simpa using hh i

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/--
lemma `inv_hom_h₀` / 引理 `inv_hom_h₀`

English:
lemma inv_hom_h₀
  given: {E F : PreZeroHypercover.{w} S} (e : E ≅ F) (i : F.I₀)
  proof: by
  obtain ⟨hs, hh⟩ := Hom.ext'_iff.mp e.inv_hom_id
  simpa using hh i

中文:
引理 inv_hom_h₀
  条件: {E F : PreZeroHypercover.{w} S} (e : E ≅ F) (i : F.I₀)
  证明: by
  obtain ⟨hs, hh⟩ := Hom.ext'_iff.mp e.inv_hom_id
  simpa using hh i

Depends on / 依赖: Hom.ext, _iff, _iff.mp, e.inv_hom_id, inv_hom_id
-/
lemma inv_hom_h₀ {E F : PreZeroHypercover.{w} S} (e : E ≅ F) (i : F.I₀) :
    e.inv.h₀ i ≫ e.hom.h₀ (e.inv.s₀ i) = eqToHom (by simp) := by
  obtain ⟨hs, hh⟩ := Hom.ext'_iff.mp e.inv_hom_id
  simpa using hh i

instance {E F : PreZeroHypercover.{w} S} (e : E ≅ F) (i : E.I₀) :
    IsIso (e.hom.h₀ i) := by
  use e.inv.h₀ (e.hom.s₀ i) ≫ eqToHom (by simp)
  rw [hom_inv_h₀_assoc]; rw [eqToHom_trans]; rw [eqToHom_refl]; rw [Category.assoc]; rw [← eqToHom_naturality _ (by simp)]; rw [inv_hom_h₀_assoc]
  simp

instance {E F : PreZeroHypercover.{w} S} (e : E ≅ F) (i : F.I₀) :
    IsIso (e.inv.h₀ i) :=
  .of_isIso_fac_right (inv_hom_h₀ e i)

@[reassoc (attr := simp)]
/--
lemma `inv_hom_h₀_comp_f` / 引理 `inv_hom_h₀_comp_f`

English:
lemma inv_hom_h₀_comp_f
  given: {E F : PreZeroHypercover.{w} S} (e : E ≅ F) (i : E.I₀)
  proof: by simp

@[reassoc (attr := simp)]

中文:
引理 inv_hom_h₀_comp_f
  条件: {E F : PreZeroHypercover.{w} S} (e : E ≅ F) (i : E.I₀)
  证明: by simp

@[reassoc (attr := simp)]
-/
lemma inv_hom_h₀_comp_f {E F : PreZeroHypercover.{w} S} (e : E ≅ F) (i : E.I₀) :
    inv (e.hom.h₀ i) ≫ E.f i = F.f _ := by simp

@[reassoc (attr := simp)]
/--
lemma `inv_inv_h₀_comp_f` / 引理 `inv_inv_h₀_comp_f`

English:
lemma inv_inv_h₀_comp_f
  given: {E F : PreZeroHypercover.{w} S} (e : E ≅ F) (i : F.I₀)
  proof: by simp

中文:
引理 inv_inv_h₀_comp_f
  条件: {E F : PreZeroHypercover.{w} S} (e : E ≅ F) (i : F.I₀)
  证明: by simp
-/
lemma inv_inv_h₀_comp_f {E F : PreZeroHypercover.{w} S} (e : E ≅ F) (i : F.I₀) :
    inv (e.inv.h₀ i) ≫ F.f i = E.f _ := by simp

/--
lemma `Hom.sieve₀_le_sieve₀` / 引理 `Hom.sieve₀_le_sieve₀`

English:
lemma Hom.sieve₀_le_sieve₀
  given: {E F : PreZeroHypercover S} (f : E.Hom F)
  statement: E.sieve₀ <= F.sieve₀
  proof: by
  rw [Sieve.generate_le_iff]; rw [Presieve.ofArrows_le_iff]
  intro i
  rw [← f.w₀ i]
  apply Sieve.downward_closed
  exact Sieve.le_generate _ _ _ ⟨f.s₀ i⟩

中文:
引理 态射.sieve₀_le_sieve₀
  条件: {E F : PreZeroHypercover S} (f : E.态射 F)
  结论: E.sieve₀ <= F.sieve₀
  证明: by
  rw [Sieve.generate_le_iff]; rw [Presieve.ofArrows_le_iff]
  intro i
  rw [← f.w₀ i]
  apply Sieve.downward_closed
  exact Sieve.le_generate _ _ _ ⟨f.s₀ i⟩

Depends on / 依赖: Presieve, Presieve.ofArrows_le_iff, Sieve.downward_closed, Sieve.generate_le_iff, Sieve.le_generate, downward_closed, generate_le_iff, le_generate, ofArrows_le_iff
-/
lemma Hom.sieve₀_le_sieve₀ {E F : PreZeroHypercover S} (f : E.Hom F) : E.sieve₀ <= F.sieve₀ := by
  rw [Sieve.generate_le_iff]; rw [Presieve.ofArrows_le_iff]
  intro i
  rw [← f.w₀ i]
  apply Sieve.downward_closed
  exact Sieve.le_generate _ _ _ ⟨f.s₀ i⟩

/--
lemma `sieve₀_eq_of_iso` / 引理 `sieve₀_eq_of_iso`

English:
lemma sieve₀_eq_of_iso
  given: {E F : PreZeroHypercover S} (e : E ≅ F)
  statement: E.sieve₀ = F.sieve₀
  proof: le_antisymm e.hom.sieve₀_le_sieve₀ e.inv.sieve₀_le_sieve₀

中文:
引理 sieve₀_eq_of_iso
  条件: {E F : PreZeroHypercover S} (e : E ≅ F)
  结论: E.sieve₀ = F.sieve₀
  证明: le_antisymm e.hom.sieve₀_le_sieve₀ e.inv.sieve₀_le_sieve₀

Depends on / 依赖: e.hom.sieve, e.inv.sieve, le_antisymm
-/
lemma sieve₀_eq_of_iso {E F : PreZeroHypercover S} (e : E ≅ F) : E.sieve₀ = F.sieve₀ :=
  le_antisymm e.hom.sieve₀_le_sieve₀ e.inv.sieve₀_le_sieve₀

/-- The equivalence on index types induced by an isomorphism of pre-`0`-hypercovers. -/
@[simps]
/--
Definition of `equivOfIso` / `equivOfIso` 的定义

English:
definition equivOfIso
  signature: {E F : PreZeroHypercover.{w} S} (e : E ≅ F)
  body: e.hom.s₀
  invFun := e.inv.s₀
  left_inv _ := by simp
  right_inv _ := by simp

中文:
定义 equivOfIso
  签名: {E F : PreZeroHypercover.{w} S} (e : E ≅ F)
  定义体: e.hom.s₀
  invFun := e.inv.s₀
  left_inv _ := by simp
  right_inv _ := by simp

Depends on / 依赖: e.hom.s
-/
def equivOfIso {E F : PreZeroHypercover.{w} S} (e : E ≅ F) : E.I₀ ≃ F.I₀ where
  toFun := e.hom.s₀
  invFun := e.inv.s₀
  left_inv _ := by simp
  right_inv _ := by simp

/--
lemma `mem_of_iso` / 引理 `mem_of_iso`

English:
lemma mem_of_iso
  statement: {K : Precoverage C} [K.IsStableUnderComposition] [K.HasIsos] {X : C}
  proof: by
  have : F.presieve₀ =
      Presieve.ofArrows (fun (i : Σ (_ : F.I₀), Unit) => _) (fun i => e.inv.h₀ i.1 ≫ E.f _) := by
    simp only [Hom.w₀]
    refine le_antisymm ?_ ?_
    · rw [Presieve.ofArrows_le_iff]
      intro i
      exact .mk (⟨i, ⟨⟩⟩ : Σ (_ : F.I₀), Unit)
    · simp [Presieve.ofArro

中文:
引理 mem_of_iso
  结论: {K : Precoverage C} [K.是StableUnderComposition] [K.有是os] {X : C}
  证明: by
  have : F.presieve₀ =
      Presieve.ofArrows (fun (i : Σ (_ : F.I₀), Unit) => _) (fun i => e.inv.h₀ i.1 ≫ E.f _) := by
    simp only [Hom.w₀]
    refine le_antisymm ?_ ?_
    · rw [Presieve.ofArrows_le_iff]
      intro i
      exact .mk (⟨i, ⟨⟩⟩ : Σ (_ : F.I₀), Unit)
    · simp [Presieve.ofArro

Depends on / 依赖: E.presieve, F.presieve, Hom.w, K.comp_mem_coverings, PreZeroHypercover, PreZeroHypercover.equivOfIso, Presieve, Presieve.ofArrows, Presieve.ofArrows_le_iff, Presieve.ofArrows_pUnit, comp_mem_coverings, e.inv.h, e.inv.s, e.symm, equivOfIso, le_antisymm, ofArrows, ofArrows_le_iff, ofArrows_pUnit
-/
lemma mem_of_iso {K : Precoverage C} [K.IsStableUnderComposition] [K.HasIsos] {X : C}
    {E F : PreZeroHypercover.{w} X} (e : E ≅ F) (hE : E.presieve₀ in K X) :
    F.presieve₀ in K X := by
  have : F.presieve₀ =
      Presieve.ofArrows (fun (i : Σ (_ : F.I₀), Unit) => _) (fun i => e.inv.h₀ i.1 ≫ E.f _) := by
    simp only [Hom.w₀]
    refine le_antisymm ?_ ?_
    · rw [Presieve.ofArrows_le_iff]
      intro i
      exact .mk (⟨i, ⟨⟩⟩ : Σ (_ : F.I₀), Unit)
    · simp [Presieve.ofArrows_le_iff]
  rw [this]
  refine K.comp_mem_coverings (fun i => E.f (e.inv.s₀ i)) ?_ (fun i (k : Unit) => e.inv.h₀ i) ?_
  · rwa [← E.presieve₀_reindex (PreZeroHypercover.equivOfIso e.symm)] at hE
  · intro i
    rw [Presieve.ofArrows_pUnit]
    exact K.mem_coverings_of_isIso _

/--
lemma `mem_iff_of_iso` / 引理 `mem_iff_of_iso`

English:
lemma mem_iff_of_iso
  statement: {K : Precoverage C} [K.IsStableUnderComposition] [K.HasIsos] {X : C}
  proof: ⟨fun h => PreZeroHypercover.mem_of_iso e h, fun h => PreZeroHypercover.mem_of_iso e.symm h⟩

中文:
引理 mem_iff_of_iso
  结论: {K : Precoverage C} [K.是StableUnderComposition] [K.有是os] {X : C}
  证明: ⟨fun h => PreZeroHypercover.mem_of_iso e h, fun h => PreZeroHypercover.mem_of_iso e.symm h⟩

Depends on / 依赖: PreZeroHypercover, PreZeroHypercover.mem_of_iso, e.symm, mem_of_iso
-/
lemma mem_iff_of_iso {K : Precoverage C} [K.IsStableUnderComposition] [K.HasIsos] {X : C}
    {E F : PreZeroHypercover.{w} X} (e : E ≅ F) :
    E.presieve₀ in K X ↔ F.presieve₀ in K X :=
  ⟨fun h => PreZeroHypercover.mem_of_iso e h, fun h => PreZeroHypercover.mem_of_iso e.symm h⟩

/-- Compose a pre-`0`-hypercover with a morphism on the right. -/
@[simps]
/--
Definition of `pushforward` / `pushforward` 的定义

English:
definition pushforward
  signature: {X Y : C} (f : X ⟶ Y) (E : PreZeroHypercover.{w} X)
  body: E.I₀
  X := E.X
  f i := E.f i ≫ f

中文:
定义 pushforward
  签名: {X Y : C} (f : X ⟶ Y) (E : PreZeroHypercover.{w} X)
  定义体: E.I₀
  X := E.X
  f i := E.f i ≫ f
-/
def pushforward {X Y : C} (f : X ⟶ Y) (E : PreZeroHypercover.{w} X) :
    PreZeroHypercover.{w} Y where
  I₀ := E.I₀
  X := E.X
  f i := E.f i ≫ f

/--
lemma `presieve₀_pushforward` / 引理 `presieve₀_pushforward`

English:
lemma presieve₀_pushforward
  given: {X Y : C} (f : X ⟶ Y) (E : PreZeroHypercover.{w} X)
  proof: by
  simp [presieve₀, Presieve.pushforward_ofArrows, pushforward]

中文:
引理 presieve₀_pushforward
  条件: {X Y : C} (f : X ⟶ Y) (E : PreZeroHypercover.{w} X)
  证明: by
  simp [presieve₀, Presieve.pushforward_ofArrows, pushforward]

Depends on / 依赖: Presieve, Presieve.pushforward_ofArrows, pushforward, pushforward_ofArrows
-/
lemma presieve₀_pushforward {X Y : C} (f : X ⟶ Y) (E : PreZeroHypercover.{w} X) :
    (E.pushforward f).presieve₀ = E.presieve₀.pushforward f := by
  simp [presieve₀, Presieve.pushforward_ofArrows, pushforward]

set_option backward.isDefEq.respectTransparency false in
/-- Pushforward along a morphism is the same as refining the singleton pre-`0`-hypercover. -/
@[simps!]
/--
Definition of `pushforwardIsoBind` / `pushforwardIsoBind` 的定义

English:
definition pushforwardIsoBind
  signature: {X Y : C} (f : X ⟶ Y) (E : PreZeroHypercover.{w} X)
  body: isoMk ((Equiv.uniqueSigma fun i => E.I₀).symm) (fun _ => Iso.refl _)

中文:
定义 pushforwardIsoBind
  签名: {X Y : C} (f : X ⟶ Y) (E : PreZeroHypercover.{w} X)
  定义体: isoMk ((Equiv.uniqueSigma fun i => E.I₀).symm) (fun _ => Iso.refl _)

Depends on / 依赖: Equiv.uniqueSigma, Iso.refl, uniqueSigma
-/
def pushforwardIsoBind {X Y : C} (f : X ⟶ Y) (E : PreZeroHypercover.{w} X) :
    E.pushforward f ≅ (singleton f).bind fun _ => E :=
  isoMk ((Equiv.uniqueSigma fun i => E.I₀).symm) (fun _ => Iso.refl _)

end Category

section Functoriality

variable {D : Type*} [Category* D] {F : C ⥤ D}

/-- The image of a pre-`0`-hypercover under a functor. -/
@[simps]
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (F : C ⥤ D) (E : PreZeroHypercover.{w} S)
  body: E.I₀
  X i := F.obj (E.X i)
  f i := F.map (E.f i)

中文:
定义 map
  签名: (F : C ⥤ D) (E : PreZeroHypercover.{w} S)
  定义体: E.I₀
  X i := F.obj (E.X i)
  f i := F.map (E.f i)
-/
def map (F : C ⥤ D) (E : PreZeroHypercover.{w} S) : PreZeroHypercover.{w} (F.obj S) where
  I₀ := E.I₀
  X i := F.obj (E.X i)
  f i := F.map (E.f i)

/--
lemma `presieve₀_map` / 引理 `presieve₀_map`

English:
lemma presieve₀_map
  statement: (E.map F).presieve₀ = E.presieve₀.map F
  proof: (Presieve.map_ofArrows _).symm

中文:
引理 presieve₀_map
  结论: (E.map F).presieve₀ = E.presieve₀.map F
  证明: (Presieve.map_ofArrows _).symm

Depends on / 依赖: Presieve, Presieve.map_ofArrows, map_ofArrows
-/
lemma presieve₀_map : (E.map F).presieve₀ = E.presieve₀.map F :=
  (Presieve.map_ofArrows _).symm

/--
lemma `sieve₀_map` / 引理 `sieve₀_map`

English:
lemma sieve₀_map
  statement: (E.map F).sieve₀ = E.sieve₀.functorPushforward F
  proof: by
  simp [← Sieve.generate_map_eq_functorPushforward, Presieve.map_ofArrows, map]

中文:
引理 sieve₀_map
  结论: (E.map F).sieve₀ = E.sieve₀.functorPushforward F
  证明: by
  simp [← Sieve.generate_map_eq_functorPushforward, Presieve.map_ofArrows, map]

Depends on / 依赖: Presieve, Presieve.map_ofArrows, Sieve.generate_map_eq_functorPushforward, generate_map_eq_functorPushforward, map_ofArrows
-/
lemma sieve₀_map : (E.map F).sieve₀ = E.sieve₀.functorPushforward F := by
  simp [← Sieve.generate_map_eq_functorPushforward, Presieve.map_ofArrows, map]

end Functoriality

set_option backward.isDefEq.respectTransparency false in
/-- Pullback symmetry isomorphism. -/
@[simps]
/--
Definition of `pullbackIso` / `pullbackIso` 的定义

English:
definition pullbackIso
  signature: {S T : C} (f : S ⟶ T) (E : PreZeroHypercover.{w} T)
  body: id
  hom.h₀ i := (pullbackSymmetry _ _).hom
  inv.s₀ := id
  inv.h₀ i := (pullbackSymmetry _ _).inv
  hom_inv_id := by
    apply Hom.ext (by rfl)
    simp only [heq_eq_eq]
    ext i
    simp
  inv_hom_id := by
    apply Hom.ext (by rfl)
    simp only [heq_eq_eq]
    ext i
    simp

中文:
定义 pullbackIso
  签名: {S T : C} (f : S ⟶ T) (E : PreZeroHypercover.{w} T)
  定义体: id
  hom.h₀ i := (pullbackSymmetry _ _).hom
  inv.s₀ := id
  inv.h₀ i := (pullbackSymmetry _ _).inv
  hom_inv_id := by
    apply Hom.ext (by rfl)
    simp only [heq_eq_eq]
    ext i
    simp
  inv_hom_id := by
    apply Hom.ext (by rfl)
    simp only [heq_eq_eq]
    ext i
    simp
-/
noncomputable def pullbackIso {S T : C} (f : S ⟶ T) (E : PreZeroHypercover.{w} T)
    [forall (i : E.I₀), HasPullback f (E.f i)] [forall (i : E.I₀), HasPullback (E.f i) f] :
    E.pullback₁ f ≅ E.pullback₂ f where
  hom.s₀ := id
  hom.h₀ i := (pullbackSymmetry _ _).hom
  inv.s₀ := id
  inv.h₀ i := (pullbackSymmetry _ _).inv
  hom_inv_id := by
    apply Hom.ext (by rfl)
    simp only [heq_eq_eq]
    ext i
    simp
  inv_hom_id := by
    apply Hom.ext (by rfl)
    simp only [heq_eq_eq]
    ext i
    simp

section

variable (F : PreZeroHypercover.{w'} S) {G : PreZeroHypercover.{w''} S}

/-- The left inclusion into the disjoint union. -/
@[simps]
/--
Definition of `sumInl` / `sumInl` 的定义

English:
definition sumInl
  signature: : E.Hom (E.sum F) where
  body: Sum.inl
  h₀ _ := 𝟙 _

中文:
定义 sumInl
  签名: : E.态射 (E.求和 F) where
  定义体: Sum.inl
  h₀ _ := 𝟙 _

Depends on / 依赖: Sum.inl
-/
def sumInl : E.Hom (E.sum F) where
  s₀ := Sum.inl
  h₀ _ := 𝟙 _

/-- The right inclusion into the disjoint union. -/
@[simps]
/--
Definition of `sumInr` / `sumInr` 的定义

English:
definition sumInr
  signature: : F.Hom (E.sum F) where
  body: Sum.inr
  h₀ _ := 𝟙 _

中文:
定义 sumInr
  签名: : F.态射 (E.求和 F) where
  定义体: Sum.inr
  h₀ _ := 𝟙 _

Depends on / 依赖: Sum.inr
-/
def sumInr : F.Hom (E.sum F) where
  s₀ := Sum.inr
  h₀ _ := 𝟙 _

variable {E F} in
/-- To give a refinement of the disjoint union, it suffices to give refinements of both
components. -/
@[simps]
/--
Definition of `sumLift` / `sumLift` 的定义

English:
definition sumLift
  signature: (f : E.Hom G) (g : F.Hom G)
  body: Sum.elim f.s₀ g.s₀
  h₀
    | .inl i => f.h₀ i
    | .inr i => g.h₀ i

中文:
定义 sumLift
  签名: (f : E.态射 G) (g : F.态射 G)
  定义体: Sum.elim f.s₀ g.s₀
  h₀
    | .inl i => f.h₀ i
    | .inr i => g.h₀ i

Depends on / 依赖: Sum.elim
-/
def sumLift (f : E.Hom G) (g : F.Hom G) : (E.sum F).Hom G where
  s₀ := Sum.elim f.s₀ g.s₀
  h₀
    | .inl i => f.h₀ i
    | .inr i => g.h₀ i

variable [forall (i : E.I₀) (j : F.I₀), HasPullback (E.f i) (F.f j)]

set_option backward.isDefEq.respectTransparency.types false in
/-- First projection from the intersection of two pre-`0`-hypercovers. -/
@[simps]
noncomputable
/--
Definition of `interFst` / `interFst` 的定义

English:
definition interFst
  signature: : Hom (inter E F) E where
  body: i.1
  h₀ _ := pullback.fst _ _

中文:
定义 interFst
  签名: : 态射 (inter E F) E where
  定义体: i.1
  h₀ _ := pullback.fst _ _
-/
def interFst : Hom (inter E F) E where
  s₀ i := i.1
  h₀ _ := pullback.fst _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Second projection from the intersection of two pre-`0`-hypercovers. -/
@[simps]
noncomputable
/--
Definition of `interSnd` / `interSnd` 的定义

English:
definition interSnd
  signature: : Hom (inter E F) F where
  body: i.2
  h₀ _ := pullback.snd _ _
  w₀ i := by simp [← pullback.condition]

中文:
定义 interSnd
  签名: : 态射 (inter E F) F where
  定义体: i.2
  h₀ _ := pullback.snd _ _
  w₀ i := by simp [← pullback.condition]
-/
def interSnd : Hom (inter E F) F where
  s₀ i := i.2
  h₀ _ := pullback.snd _ _
  w₀ i := by simp [← pullback.condition]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
variable {E F} in
/-- Universal property of the intersection of two pre-`0`-hypercovers. -/
@[simps]
noncomputable
/--
Definition of `interLift` / `interLift` 的定义

English:
definition interLift
  signature: (f : G.Hom E) (g : G.Hom F)
  body: ⟨f.s₀ i, g.s₀ i⟩
  h₀ i := pullback.lift (f.h₀ i) (g.h₀ i) (by simp)

中文:
定义 interLift
  签名: (f : G.态射 E) (g : G.态射 F)
  定义体: ⟨f.s₀ i, g.s₀ i⟩
  h₀ i := pullback.lift (f.h₀ i) (g.h₀ i) (by simp)
-/
def interLift (f : G.Hom E) (g : G.Hom F) :
    G.Hom (E.inter F) where
  s₀ i := ⟨f.s₀ i, g.s₀ i⟩
  h₀ i := pullback.lift (f.h₀ i) (g.h₀ i) (by simp)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The refinement given by restricting the indexing type. -/
@[simps]
/--
Definition of `restrictIndexHom` / `restrictIndexHom` 的定义

English:
definition restrictIndexHom
  signature: {ι : Type w'} (f : ι -> E.I₀)
  body: f
  h₀ _ := 𝟙 _

中文:
定义 restrictIndexHom
  签名: {ι : 类型 w'} (f : ι -> E.I₀)
  定义体: f
  h₀ _ := 𝟙 _
-/
def restrictIndexHom {ι : Type w'} (f : ι -> E.I₀) : (E.restrictIndex f).Hom E where
  s₀ := f
  h₀ _ := 𝟙 _

end

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- If `{Uᵢ}` covers `X`, the pre-`0`-hypercover `{Uᵢ ×[Z] Y}` of `X ×[Z] Y` is isomorphic
to the pullback of `{Uᵢ}` along the first projection. -/
noncomputable
/--
Definition of `pullbackCoverOfLeftIsoPullback₁` / `pullbackCoverOfLeftIsoPullback₁` 的定义

English:
definition pullbackCoverOfLeftIsoPullback₁
  signature: {X : C} (E : PreZeroHypercover X) {Y Z : C}
  body: PreZeroHypercover.isoMk (.refl _)
    (fun _ => (pullbackRightPullbackFstIso _ _ _).symm ≪≫ pullbackSymmetry _ _)

中文:
定义 pullbackCoverOfLeftIsoPullback₁
  签名: {X : C} (E : PreZeroHypercover X) {Y Z : C}
  定义体: PreZeroHypercover.isoMk (.refl _)
    (fun _ => (pullbackRightPullbackFstIso _ _ _).symm ≪≫ pullbackSymmetry _ _)

Depends on / 依赖: PreZeroHypercover, PreZeroHypercover.isoMk, pullbackRightPullbackFstIso, pullbackSymmetry
-/
def pullbackCoverOfLeftIsoPullback₁ {X : C} (E : PreZeroHypercover X) {Y Z : C}
    (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] [forall i, HasPullback (pullback.fst f g) (E.f i)]
    [forall i, HasPullback (E.f i) (pullback.fst f g)] :
    E.pullbackCoverOfLeft f g ≅ pullback₁ (pullback.fst f g) E :=
  PreZeroHypercover.isoMk (.refl _)
    (fun _ => (pullbackRightPullbackFstIso _ _ _).symm ≪≫ pullbackSymmetry _ _)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- If `{Uᵢ}` covers `Y`, the pre-`0`-hypercover `{X ×[Z] Uᵢ}` of `X ×[Z] Y` is isomorphic
to the pullback of `{Uᵢ}` along the second projection. -/
noncomputable
/--
Definition of `pullbackCoverOfRightIsoPullback₂` / `pullbackCoverOfRightIsoPullback₂` 的定义

English:
definition pullbackCoverOfRightIsoPullback₂
  signature: {Y : C} (E : PreZeroHypercover Y) {X Z : C}
  body: PreZeroHypercover.isoMk (.refl _)
    (fun _ => (pullbackLeftPullbackSndIso _ _ _).symm ≪≫ pullbackSymmetry _ _)

中文:
定义 pullbackCoverOfRightIsoPullback₂
  签名: {Y : C} (E : PreZeroHypercover Y) {X Z : C}
  定义体: PreZeroHypercover.isoMk (.refl _)
    (fun _ => (pullbackLeftPullbackSndIso _ _ _).symm ≪≫ pullbackSymmetry _ _)

Depends on / 依赖: PreZeroHypercover, PreZeroHypercover.isoMk, pullbackLeftPullbackSndIso, pullbackSymmetry
-/
def pullbackCoverOfRightIsoPullback₂ {Y : C} (E : PreZeroHypercover Y) {X Z : C}
    (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] [forall (i : E.I₀), HasPullback (E.f i) (pullback.snd f g)]
    [forall i, HasPullback (pullback.snd f g) (E.f i)] :
    E.pullbackCoverOfRight f g ≅ pullback₂ (pullback.snd f g) E :=
  PreZeroHypercover.isoMk (.refl _)
    (fun _ => (pullbackLeftPullbackSndIso _ _ _).symm ≪≫ pullbackSymmetry _ _)

end PreZeroHypercover

/-- The pre-`0`-hypercover associated to a presieve `R`. It is indexed by the morphisms in `R`. -/
@[simps -isSimp]
/--
Definition of `Presieve.preZeroHypercover` / `Presieve.preZeroHypercover` 的定义

English:
definition Presieve.preZeroHypercover
  signature: {S : C} (R : Presieve S)
  body: R.uncurry
  X i := i.1.1
  f i := i.1.2

@[simp]

中文:
定义 Presieve.preZeroHypercover
  签名: {S : C} (R : Presieve S)
  定义体: R.uncurry
  X i := i.1.1
  f i := i.1.2

@[simp]

Depends on / 依赖: R.uncurry, uncurry
-/
def Presieve.preZeroHypercover {S : C} (R : Presieve S) : PreZeroHypercover.{max u v} S where
  I₀ := R.uncurry
  X i := i.1.1
  f i := i.1.2

@[simp]
/--
lemma `Presieve.presieve₀_preZeroHypercover` / 引理 `Presieve.presieve₀_preZeroHypercover`

English:
lemma Presieve.presieve₀_preZeroHypercover
  given: {S : C} (R : Presieve S)
  proof: by
  refine le_antisymm ?_ ?_
  · rintro - - ⟨i⟩
    exact i.2
  · intro Y f h
    let i : R.uncurry := ⟨⟨Y, f⟩, h⟩
    exact .mk i

中文:
引理 Presieve.presieve₀_preZeroHypercover
  条件: {S : C} (R : Presieve S)
  证明: by
  refine le_antisymm ?_ ?_
  · rintro - - ⟨i⟩
    exact i.2
  · intro Y f h
    let i : R.uncurry := ⟨⟨Y, f⟩, h⟩
    exact .mk i

Depends on / 依赖: R.uncurry, le_antisymm, uncurry
-/
lemma Presieve.presieve₀_preZeroHypercover {S : C} (R : Presieve S) :
    R.preZeroHypercover.presieve₀ = R := by
  refine le_antisymm ?_ ?_
  · rintro - - ⟨i⟩
    exact i.2
  · intro Y f h
    let i : R.uncurry := ⟨⟨Y, f⟩, h⟩
    exact .mk i

/--
lemma `Presieve.exists_eq_preZeroHypercover` / 引理 `Presieve.exists_eq_preZeroHypercover`

English:
lemma Presieve.exists_eq_preZeroHypercover
  given: {S : C} (R : Presieve S)
  proof: ⟨R.preZeroHypercover, by simp⟩

中文:
引理 Presieve.存在_eq_preZeroHypercover
  条件: {S : C} (R : Presieve S)
  证明: ⟨R.preZeroHypercover, by simp⟩

Depends on / 依赖: R.preZeroHypercover, preZeroHypercover
-/
lemma Presieve.exists_eq_preZeroHypercover {S : C} (R : Presieve S) :
    exists (E : PreZeroHypercover.{max u v} S), R = E.presieve₀ :=
  ⟨R.preZeroHypercover, by simp⟩

/-- The deduplication of a pre-`0`-hypercover `E` in universe `w` to a pre-`0`-hypercover in
universe `max u v`. This is indexed by the morphisms of `E`. -/
@[simps! -isSimp]
/--
Definition of `PreZeroHypercover.shrink` / `PreZeroHypercover.shrink` 的定义

English:
definition PreZeroHypercover.shrink
  signature: {S : C} (E : PreZeroHypercover.{w} S)
  body: E.presieve₀.preZeroHypercover

@[simp]

中文:
定义 PreZeroHypercover.shrink
  签名: {S : C} (E : PreZeroHypercover.{w} S)
  定义体: E.presieve₀.preZeroHypercover

@[simp]

Depends on / 依赖: E.presieve, preZeroHypercover
-/
def PreZeroHypercover.shrink {S : C} (E : PreZeroHypercover.{w} S) :
    PreZeroHypercover.{max u v} S :=
  E.presieve₀.preZeroHypercover

@[simp]
/--
lemma `PreZeroHypercover.presieve₀_shrink` / 引理 `PreZeroHypercover.presieve₀_shrink`

English:
lemma PreZeroHypercover.presieve₀_shrink
  given: {S : C} (E : PreZeroHypercover.{w} S)
  proof: E.presieve₀.presieve₀_preZeroHypercover

中文:
引理 PreZeroHypercover.presieve₀_shrink
  条件: {S : C} (E : PreZeroHypercover.{w} S)
  证明: E.presieve₀.presieve₀_preZeroHypercover

Depends on / 依赖: E.presieve
-/
lemma PreZeroHypercover.presieve₀_shrink {S : C} (E : PreZeroHypercover.{w} S) :
    E.shrink.presieve₀ = E.presieve₀ :=
  E.presieve₀.presieve₀_preZeroHypercover

/--
lemma `PreZeroHypercover.shrink_eq_shrink_of_presieve₀_eq_presieve₀` / 引理 `PreZeroHypercover.shrink_eq_shrink_of_presieve₀_eq_presieve₀`

English:
lemma PreZeroHypercover.shrink_eq_shrink_of_presieve₀_eq_presieve₀
  statement: {S : C}
  proof: by
  rw [shrink]; rw [shrink]; rw [h]

中文:
引理 PreZeroHypercover.shrink_eq_shrink_of_presieve₀_eq_presieve₀
  结论: {S : C}
  证明: by
  rw [shrink]; rw [shrink]; rw [h]

Depends on / 依赖: shrink
-/
lemma PreZeroHypercover.shrink_eq_shrink_of_presieve₀_eq_presieve₀ {S : C}
    {E F : PreZeroHypercover.{w} S} (h : E.presieve₀ = F.presieve₀) :
    E.shrink = F.shrink := by
  rw [shrink]; rw [shrink]; rw [h]

/--
lemma `PreZeroHypercover.presieve₀_eq_presieve₀_iff` / 引理 `PreZeroHypercover.presieve₀_eq_presieve₀_iff`

English:
lemma PreZeroHypercover.presieve₀_eq_presieve₀_iff
  given: {S : C} {E F : PreZeroHypercover.{w} S}
  proof: by
  refine ⟨fun h => shrink_eq_shrink_of_presieve₀_eq_presieve₀ h, fun h => ?_⟩
  rw [← E.presieve₀_shrink]; rw [← F.presieve₀_shrink]; rw [h]

中文:
引理 PreZeroHypercover.presieve₀_eq_presieve₀_iff
  条件: {S : C} {E F : PreZeroHypercover.{w} S}
  证明: by
  refine ⟨fun h => shrink_eq_shrink_of_presieve₀_eq_presieve₀ h, fun h => ?_⟩
  rw [← E.presieve₀_shrink]; rw [← F.presieve₀_shrink]; rw [h]

Depends on / 依赖: E.presieve, F.presieve
-/
lemma PreZeroHypercover.presieve₀_eq_presieve₀_iff {S : C} {E F : PreZeroHypercover.{w} S} :
    E.presieve₀ = F.presieve₀ ↔ E.shrink = F.shrink := by
  refine ⟨fun h => shrink_eq_shrink_of_presieve₀_eq_presieve₀ h, fun h => ?_⟩
  rw [← E.presieve₀_shrink]; rw [← F.presieve₀_shrink]; rw [h]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `PreZeroHypercover.toShrink` / `PreZeroHypercover.toShrink` 的定义

English:
definition PreZeroHypercover.toShrink
  signature: {S : C} (E : PreZeroHypercover.{w} S)
  body: ⟨⟨_, E.f i⟩, .mk i⟩
  h₀ i := 𝟙 _

中文:
定义 PreZeroHypercover.toShrink
  签名: {S : C} (E : PreZeroHypercover.{w} S)
  定义体: ⟨⟨_, E.f i⟩, .mk i⟩
  h₀ i := 𝟙 _
-/
def PreZeroHypercover.toShrink {S : C} (E : PreZeroHypercover.{w} S) : E.Hom E.shrink where
  s₀ i := ⟨⟨_, E.f i⟩, .mk i⟩
  h₀ i := 𝟙 _

/-- The deduplication of `E` refines `E`. -/
noncomputable
/--
Definition of `PreZeroHypercover.fromShrink` / `PreZeroHypercover.fromShrink` 的定义

English:
definition PreZeroHypercover.fromShrink
  signature: {S : C} (E : PreZeroHypercover.{w} S)
  body: (Presieve.ofArrows_surj _ _ i.2).choose
  h₀ i := eqToHom (Presieve.ofArrows_surj _ _ i.2).choose_spec.1.symm
  w₀ i := (Presieve.ofArrows_surj _ _ i.2).choose_spec.2.symm

中文:
定义 PreZeroHypercover.fromShrink
  签名: {S : C} (E : PreZeroHypercover.{w} S)
  定义体: (Presieve.ofArrows_surj _ _ i.2).choose
  h₀ i := eqToHom (Presieve.ofArrows_surj _ _ i.2).choose_spec.1.symm
  w₀ i := (Presieve.ofArrows_surj _ _ i.2).choose_spec.2.symm

Depends on / 依赖: Presieve, Presieve.ofArrows_surj, ofArrows_surj
-/
def PreZeroHypercover.fromShrink {S : C} (E : PreZeroHypercover.{w} S) : E.shrink.Hom E where
  s₀ i := (Presieve.ofArrows_surj _ _ i.2).choose
  h₀ i := eqToHom (Presieve.ofArrows_surj _ _ i.2).choose_spec.1.symm
  w₀ i := (Presieve.ofArrows_surj _ _ i.2).choose_spec.2.symm

section

/--
Definition of `Precoverage.RespectsIso` / `Precoverage.RespectsIso` 的定义

English:
class Precoverage.RespectsIso
  parameters: (J : Precoverage C)
  axioms and operations (1):
    - of_iso({S : C} {E F : PreZeroHypercover.{max u v} S} (e : E ≅ F)) : E.presieve₀ in J S -> F.presieve₀ in J S

中文:
类 Precoverage.RespectsIso
  参数: (J : Precoverage C)
  公理与运算 (1 个):
    - of_iso({S : C} {E F : PreZeroHypercover.{最大值 u v} S} (e : E ≅ F)) : E.presieve₀ in J S -> F.presieve₀ in J S
-/
class Precoverage.RespectsIso (J : Precoverage C) : Prop where
  of_iso {S : C} {E F : PreZeroHypercover.{max u v} S} (e : E ≅ F) :
    E.presieve₀ in J S -> F.presieve₀ in J S

variable {J : Precoverage C}

/--
lemma `Precoverage.RespectsIso.of_forall_exists_iso` / 引理 `Precoverage.RespectsIso.of_forall_exists_iso`

English:
lemma Precoverage.RespectsIso.of_forall_exists_iso
  statement: [J.RespectsIso] {S : C} {R T : Presieve S}
  proof: by
  choose YR eR hTeg using hRT
  choose YT eT hReg using hTR
  let E : PreZeroHypercover S :=
    { I₀ := R.uncurry oplus T.uncurry
      X i := i.elim (fun j => j.1.1) (fun j => YT _ j.2)
      f i :=
        match i with
        | .inl i => by exact i.1.2
        | .inr i => by exact (eT _ i.2).

中文:
引理 Precoverage.RespectsIso.of_对任意_存在_iso
  结论: [J.RespectsIso] {S : C} {R T : Presieve S}
  证明: by
  choose YR eR hTeg using hRT
  choose YT eT hReg using hTR
  let E : PreZeroHypercover S :=
    { I₀ := R.uncurry oplus T.uncurry
      X i := i.elim (fun j => j.1.1) (fun j => YT _ j.2)
      f i :=
        match i with
        | .inl i => by exact i.1.2
        | .inr i => by exact (eT _ i.2).

Depends on / 依赖: PreZeroHypercover, R.uncurry, T.uncurry, i.elim, uncurry
-/
lemma Precoverage.RespectsIso.of_forall_exists_iso [J.RespectsIso] {S : C} {R T : Presieve S}
    (hRT : forall ⦃Z : C⦄ (g : Z ⟶ S), R g -> exists (Y : C) (e : Y ≅ Z), T (e.hom ≫ g))
    (hTR : forall ⦃Z : C⦄ (g : Z ⟶ S), T g -> exists (Y : C) (e : Y ≅ Z), R (e.hom ≫ g))
    (hR : R in J S) :
    T in J S := by
  choose YR eR hTeg using hRT
  choose YT eT hReg using hTR
  let E : PreZeroHypercover S :=
    { I₀ := R.uncurry oplus T.uncurry
      X i := i.elim (fun j => j.1.1) (fun j => YT _ j.2)
      f i :=
        match i with
        | .inl i => by exact i.1.2
        | .inr i => by exact (eT _ i.2).hom ≫ i.1.2 }
  let F : PreZeroHypercover S :=
    { I₀ := R.uncurry oplus T.uncurry
      X i := i.elim (fun j => YR _ j.2) (fun j => j.1.1)
      f i :=
        match i with
        | .inl i => by exact (eR _ i.2).hom ≫ i.1.2
        | .inr i => by exact i.1.2 }
  let e : E ≅ F := by
    refine PreZeroHypercover.isoMk (Equiv.refl _) (fun i => ?_) (fun i => ?_)
    · match i with
      | .inl i => dsimp [E, F]; symm; exact eR _ _
      | .inr i => dsimp [E, F]; apply eT
    · cases i <;> simp [E, F]
  have hER : E.presieve₀ = R := by
    refine le_antisymm ?_ fun Y g hg => .mk (Sum.inl (⟨⟨Y, g⟩, hg⟩ : R.uncurry))
    rintro - - ⟨i⟩
    match i with
    | .inl i => exact i.2
    | .inr i => apply hReg
  have hFT : F.presieve₀ = T := by
    refine le_antisymm ?_ fun Y g hg => .mk (Sum.inr (⟨⟨Y, g⟩, hg⟩ : T.uncurry))
    rintro - - ⟨i⟩
    match i with
    | .inl i => apply hTeg
    | .inr i => exact i.2
  rw [← hFT]
  apply RespectsIso.of_iso e
  rwa [hER]

/--
lemma `PreZeroHypercover.presieve₀_mem_of_iso` / 引理 `PreZeroHypercover.presieve₀_mem_of_iso`

English:
lemma PreZeroHypercover.presieve₀_mem_of_iso
  statement: [J.RespectsIso] {S : C} {E F : PreZeroHypercover.{w} S}
  proof: by
  refine Precoverage.RespectsIso.of_forall_exists_iso ?_ ?_ hE
  · intro Z _ ⟨i⟩
    use F.X (e.hom.s₀ i), (asIso (e.hom.h₀ i)).symm
    simp
  · intro Z _ ⟨i⟩
    use E.X (e.inv.s₀ i), (asIso (e.inv.h₀ i)).symm
    simp

中文:
引理 PreZeroHypercover.presieve₀_mem_of_iso
  结论: [J.RespectsIso] {S : C} {E F : PreZeroHypercover.{w} S}
  证明: by
  refine Precoverage.RespectsIso.of_forall_exists_iso ?_ ?_ hE
  · intro Z _ ⟨i⟩
    use F.X (e.hom.s₀ i), (asIso (e.hom.h₀ i)).symm
    simp
  · intro Z _ ⟨i⟩
    use E.X (e.inv.s₀ i), (asIso (e.inv.h₀ i)).symm
    simp

Depends on / 依赖: Precoverage, Precoverage.RespectsIso.of_forall_exists_iso, RespectsIso, e.hom.h, e.hom.s, e.inv.h, e.inv.s, of_forall_exists_iso
-/
lemma PreZeroHypercover.presieve₀_mem_of_iso [J.RespectsIso] {S : C} {E F : PreZeroHypercover.{w} S}
    (e : E ≅ F) (hE : E.presieve₀ in J S) : F.presieve₀ in J S := by
  refine Precoverage.RespectsIso.of_forall_exists_iso ?_ ?_ hE
  · intro Z _ ⟨i⟩
    use F.X (e.hom.s₀ i), (asIso (e.hom.h₀ i)).symm
    simp
  · intro Z _ ⟨i⟩
    use E.X (e.inv.s₀ i), (asIso (e.inv.h₀ i)).symm
    simp

/--
lemma `PreZeroHypercover.presieve₀_mem_iff_of_iso` / 引理 `PreZeroHypercover.presieve₀_mem_iff_of_iso`

English:
lemma PreZeroHypercover.presieve₀_mem_iff_of_iso
  statement: [J.RespectsIso] {S : C}
  proof: ⟨fun h => E.presieve₀_mem_of_iso e h, fun h => F.presieve₀_mem_of_iso e.symm h⟩

中文:
引理 PreZeroHypercover.presieve₀_mem_iff_of_iso
  结论: [J.RespectsIso] {S : C}
  证明: ⟨fun h => E.presieve₀_mem_of_iso e h, fun h => F.presieve₀_mem_of_iso e.symm h⟩

Depends on / 依赖: E.presieve, F.presieve, Sym2.mem_iff, and_congr_right, e.symm, mem_iff
-/
lemma PreZeroHypercover.presieve₀_mem_iff_of_iso [J.RespectsIso] {S : C}
    {E F : PreZeroHypercover.{w} S} (e : E ≅ F) :
    E.presieve₀ in J S ↔ F.presieve₀ in J S :=
  ⟨fun h => E.presieve₀_mem_of_iso e h, fun h => F.presieve₀_mem_of_iso e.symm h⟩

end

namespace Precoverage

variable {J : Precoverage C}

/--
Definition of `ZeroHypercover` / `ZeroHypercover` 的定义

English:
structure ZeroHypercover
  parameters: (J : Precoverage C) (S : C)
  extends: PreZeroHypercover.{w} S
  axioms and operations (1):
    - mem₀ : toPreZeroHypercover.presieve₀ in J S

中文:
结构 ZeroHypercover
  参数: (J : Precoverage C) (S : C)
  继承: PreZeroHypercover.{w} S
  公理与运算 (1 个):
    - mem₀ : toPreZeroHypercover.presieve₀ in J S

Depends on / 依赖: Sym2.mem_mk_left, and_iff_left, mem_mk_left
-/
structure ZeroHypercover (J : Precoverage C) (S : C) extends PreZeroHypercover.{w} S where
  mem₀ : toPreZeroHypercover.presieve₀ in J S

namespace ZeroHypercover

variable {S T : C}

/-- The `0`-hypercover defined by a single covering morphism. -/
@[simps toPreZeroHypercover]
/--
Definition of `singleton` / `singleton` 的定义

English:
definition singleton
  signature: (f : S ⟶ T) (hf : Presieve.singleton f in J T)
  body: PreZeroHypercover.singleton f
  mem₀ := by
    simpa [PreZeroHypercover.presieve₀, PreZeroHypercover.singleton, Presieve.ofArrows_pUnit]

中文:
定义 singleton
  签名: (f : S ⟶ T) (hf : Presieve.singleton f in J T)
  定义体: PreZeroHypercover.singleton f
  mem₀ := by
    simpa [PreZeroHypercover.presieve₀, PreZeroHypercover.singleton, Presieve.ofArrows_pUnit]

Depends on / 依赖: PreZeroHypercover, PreZeroHypercover.singleton, Sym2.mem_mk_right, and_iff_left, mem_mk_right, singleton
-/
def singleton (f : S ⟶ T) (hf : Presieve.singleton f in J T) :
    J.ZeroHypercover T where
  __ := PreZeroHypercover.singleton f
  mem₀ := by
    simpa [PreZeroHypercover.presieve₀, PreZeroHypercover.singleton, Presieve.ofArrows_pUnit]

/-- Pullback of a `0`-hypercover along a morphism. The components are `pullback f (E.f i)`. -/
@[simps toPreZeroHypercover]
noncomputable
/--
Definition of `pullback₁` / `pullback₁` 的定义

English:
definition pullback₁
  signature: [J.IsStableUnderBaseChange] (f : S ⟶ T) (E : ZeroHypercover.{w} J T)
  body: E.toPreZeroHypercover.pullback₁ f
  mem₀ := J.mem_coverings_of_isPullback E.f E.mem₀ f _
    (fun _ => pullback.snd _ _) fun i => IsPullback.of_hasPullback f (E.f i)

中文:
定义 pullback₁
  签名: [J.是StableUnderBaseChange] (f : S ⟶ T) (E : ZeroHypercover.{w} J T)
  定义体: E.toPreZeroHypercover.pullback₁ f
  mem₀ := J.mem_coverings_of_isPullback E.f E.mem₀ f _
    (fun _ => pullback.snd _ _) fun i => IsPullback.of_hasPullback f (E.f i)

Depends on / 依赖: E.toPreZeroHypercover.pullback, toPreZeroHypercover
-/
def pullback₁ [J.IsStableUnderBaseChange] (f : S ⟶ T) (E : ZeroHypercover.{w} J T)
    [forall i, HasPullback f (E.f i)] : J.ZeroHypercover S where
  __ := E.toPreZeroHypercover.pullback₁ f
  mem₀ := J.mem_coverings_of_isPullback E.f E.mem₀ f _
    (fun _ => pullback.snd _ _) fun i => IsPullback.of_hasPullback f (E.f i)

/-- Pullback of a `0`-hypercover along a morphism. The components are `pullback (E.f i) f`. -/
@[simps toPreZeroHypercover]
noncomputable
/--
Definition of `pullback₂` / `pullback₂` 的定义

English:
definition pullback₂
  signature: [J.IsStableUnderBaseChange] (f : S ⟶ T) (E : ZeroHypercover.{w} J T)
  body: E.toPreZeroHypercover.pullback₂ f
  mem₀ := J.mem_coverings_of_isPullback E.f E.mem₀ f _
    (fun _ => pullback.fst _ _) fun i => (IsPullback.of_hasPullback (E.f i) f).flip

中文:
定义 pullback₂
  签名: [J.是StableUnderBaseChange] (f : S ⟶ T) (E : ZeroHypercover.{w} J T)
  定义体: E.toPreZeroHypercover.pullback₂ f
  mem₀ := J.mem_coverings_of_isPullback E.f E.mem₀ f _
    (fun _ => pullback.fst _ _) fun i => (IsPullback.of_hasPullback (E.f i) f).flip

Depends on / 依赖: E.toPreZeroHypercover.pullback, toPreZeroHypercover
-/
def pullback₂ [J.IsStableUnderBaseChange] (f : S ⟶ T) (E : ZeroHypercover.{w} J T)
    [forall i, HasPullback (E.f i) f] : J.ZeroHypercover S where
  __ := E.toPreZeroHypercover.pullback₂ f
  mem₀ := J.mem_coverings_of_isPullback E.f E.mem₀ f _
    (fun _ => pullback.fst _ _) fun i => (IsPullback.of_hasPullback (E.f i) f).flip

/-- Refining each component of a `0`-hypercover yields a refined `0`-hypercover of the base. -/
@[simps toPreZeroHypercover]
/--
Definition of `bind` / `bind` 的定义

English:
definition bind
  signature: [J.IsStableUnderComposition] (E : ZeroHypercover.{w} J T)
  body: E.toPreZeroHypercover.bind (fun i => (F i).toPreZeroHypercover)
  mem₀ :=
    comp_mem_coverings (f := E.f) (g := fun i j => (F i).f j) E.mem₀ (fun i => (F i).mem₀)

中文:
定义 bind
  签名: [J.是StableUnderComposition] (E : ZeroHypercover.{w} J T)
  定义体: E.toPreZeroHypercover.bind (fun i => (F i).toPreZeroHypercover)
  mem₀ :=
    comp_mem_coverings (f := E.f) (g := fun i j => (F i).f j) E.mem₀ (fun i => (F i).mem₀)

Depends on / 依赖: E.toPreZeroHypercover.bind, toPreZeroHypercover
-/
def bind [J.IsStableUnderComposition] (E : ZeroHypercover.{w} J T)
    (F : forall i, ZeroHypercover.{w'} J (E.X i)) :
    ZeroHypercover.{max w w'} J T where
  __ := E.toPreZeroHypercover.bind (fun i => (F i).toPreZeroHypercover)
  mem₀ :=
    comp_mem_coverings (f := E.f) (g := fun i j => (F i).f j) E.mem₀ (fun i => (F i).mem₀)

set_option backward.isDefEq.respectTransparency.types false in
/-- Pairwise intersection of two `0`-hypercovers. -/
@[simps toPreZeroHypercover]
noncomputable
/--
Definition of `inter` / `inter` 的定义

English:
definition inter
  signature: [J.IsStableUnderBaseChange] [J.IsStableUnderComposition] (E : ZeroHypercover.{w} J T)
  body: E.toPreZeroHypercover.inter F.toPreZeroHypercover
  mem₀ := by
    rw [PreZeroHypercover.inter_def]; rw [PreZeroHypercover.presieve₀_reindex]
    exact (E.bind (fun i => F.pullback₁ (E.f i))).mem₀

中文:
定义 inter
  签名: [J.是StableUnderBaseChange] [J.是StableUnderComposition] (E : ZeroHypercover.{w} J T)
  定义体: E.toPreZeroHypercover.inter F.toPreZeroHypercover
  mem₀ := by
    rw [PreZeroHypercover.inter_def]; rw [PreZeroHypercover.presieve₀_reindex]
    exact (E.bind (fun i => F.pullback₁ (E.f i))).mem₀

Depends on / 依赖: E.toPreZeroHypercover.inter, F.toPreZeroHypercover, toPreZeroHypercover
-/
def inter [J.IsStableUnderBaseChange] [J.IsStableUnderComposition] (E : ZeroHypercover.{w} J T)
    (F : ZeroHypercover.{w'} J T) [forall i j, HasPullback (E.f i) (F.f j)] :
    ZeroHypercover.{max w w'} J T where
  __ := E.toPreZeroHypercover.inter F.toPreZeroHypercover
  mem₀ := by
    rw [PreZeroHypercover.inter_def]; rw [PreZeroHypercover.presieve₀_reindex]
    exact (E.bind (fun i => F.pullback₁ (E.f i))).mem₀

/-- Replace the indexing type of a `0`-hypercover. -/
@[simps toPreZeroHypercover]
/--
Definition of `reindex` / `reindex` 的定义

English:
definition reindex
  signature: (E : ZeroHypercover.{w} J T) {ι : Type w'} (e : ι ≃ E.I₀)
  body: E.toPreZeroHypercover.reindex e
  mem₀ := by simp [E.mem₀]

中文:
定义 reindex
  签名: (E : ZeroHypercover.{w} J T) {ι : 类型 w'} (e : ι ≃ E.I₀)
  定义体: E.toPreZeroHypercover.reindex e
  mem₀ := by simp [E.mem₀]

Depends on / 依赖: E.toPreZeroHypercover.reindex, reindex, toPreZeroHypercover
-/
def reindex (E : ZeroHypercover.{w} J T) {ι : Type w'} (e : ι ≃ E.I₀) :
    ZeroHypercover.{w'} J T where
  __ := E.toPreZeroHypercover.reindex e
  mem₀ := by simp [E.mem₀]

/-- Disjoint union of two `0`-hypercovers. -/
@[simps toPreZeroHypercover]
/--
Definition of `sum` / `sum` 的定义

English:
definition sum
  signature: [J.IsStableUnderSup] (E : ZeroHypercover.{w} J S) (F : ZeroHypercover.{w'} J S)
  body: E.toPreZeroHypercover.sum F.toPreZeroHypercover
  mem₀ := by
    rw [PreZeroHypercover.presieve₀_sum]
    exact J.sup_mem_coverings E.mem₀ F.mem₀

中文:
定义 求和
  签名: [J.是StableUnderSup] (E : ZeroHypercover.{w} J S) (F : ZeroHypercover.{w'} J S)
  定义体: E.toPreZeroHypercover.sum F.toPreZeroHypercover
  mem₀ := by
    rw [PreZeroHypercover.presieve₀_sum]
    exact J.sup_mem_coverings E.mem₀ F.mem₀

Depends on / 依赖: E.toPreZeroHypercover.sum, F.toPreZeroHypercover, toPreZeroHypercover
-/
def sum [J.IsStableUnderSup] (E : ZeroHypercover.{w} J S) (F : ZeroHypercover.{w'} J S) :
    ZeroHypercover.{max w w'} J S where
  __ := E.toPreZeroHypercover.sum F.toPreZeroHypercover
  mem₀ := by
    rw [PreZeroHypercover.presieve₀_sum]
    exact J.sup_mem_coverings E.mem₀ F.mem₀

/-- Add a single morphism to a `0`-hypercover. -/
@[simps toPreZeroHypercover]
/--
Definition of `add` / `add` 的定义

English:
definition add
  signature: (E : ZeroHypercover.{w} J S) {T : C} (f : T ⟶ S)
  body: E.toPreZeroHypercover.add f
  mem₀ := by rwa [PreZeroHypercover.presieve₀_add]

中文:
定义 add
  签名: (E : ZeroHypercover.{w} J S) {T : C} (f : T ⟶ S)
  定义体: E.toPreZeroHypercover.add f
  mem₀ := by rwa [PreZeroHypercover.presieve₀_add]

Depends on / 依赖: E.toPreZeroHypercover.add, toPreZeroHypercover
-/
def add (E : ZeroHypercover.{w} J S) {T : C} (f : T ⟶ S)
    (hf : E.presieve₀ ⊔ Presieve.singleton f in J S) :
    ZeroHypercover.{w} J S where
  __ := E.toPreZeroHypercover.add f
  mem₀ := by rwa [PreZeroHypercover.presieve₀_add]

/-- If `L` is a finer precoverage than `K`, any `0`-hypercover wrt. `K` is in particular
a `0`-hypercover wrt. to `L`. -/
@[simps toPreZeroHypercover]
/--
Definition of `weaken` / `weaken` 的定义

English:
definition weaken
  signature: {K L : Precoverage C} {X : C} (E : Precoverage.ZeroHypercover K X) (h : K <= L)
  body: E
  mem₀ := h _ E.mem₀

中文:
定义 weaken
  签名: {K L : Precoverage C} {X : C} (E : Precoverage.ZeroHypercover K X) (h : K <= L)
  定义体: E
  mem₀ := h _ E.mem₀
-/
def weaken {K L : Precoverage C} {X : C} (E : Precoverage.ZeroHypercover K X) (h : K <= L) :
    Precoverage.ZeroHypercover L X where
  __ := E
  mem₀ := h _ E.mem₀

/-- Compose a `0`-hypercover with a morphism on the right. -/
@[simps toPreZeroHypercover]
/--
Definition of `pushforward` / `pushforward` 的定义

English:
definition pushforward
  signature: [J.IsStableUnderComposition] [J.HasIsos] {X Y : C} (f : X ⟶ Y)
  body: E.toPreZeroHypercover.pushforward f
  mem₀ := by
    rw [PreZeroHypercover.mem_iff_of_iso (E.pushforwardIsoBind _)]
    exact ((ZeroHypercover.singleton f hf).bind _).mem₀

中文:
定义 pushforward
  签名: [J.是StableUnderComposition] [J.有是os] {X Y : C} (f : X ⟶ Y)
  定义体: E.toPreZeroHypercover.pushforward f
  mem₀ := by
    rw [PreZeroHypercover.mem_iff_of_iso (E.pushforwardIsoBind _)]
    exact ((ZeroHypercover.singleton f hf).bind _).mem₀

Depends on / 依赖: E.toPreZeroHypercover.pushforward, pushforward, toPreZeroHypercover
-/
def pushforward [J.IsStableUnderComposition] [J.HasIsos] {X Y : C} (f : X ⟶ Y)
    (hf : .singleton f in J _) (E : ZeroHypercover.{w} J X) :
    ZeroHypercover.{w} J Y where
  __ := E.toPreZeroHypercover.pushforward f
  mem₀ := by
    rw [PreZeroHypercover.mem_iff_of_iso (E.pushforwardIsoBind _)]
    exact ((ZeroHypercover.singleton f hf).bind _).mem₀

instance (K : Precoverage C) [K.HasPullbacks] {X Y : C} (E : K.ZeroHypercover X) (f : Y ⟶ X) :
    E.presieve₀.HasPullbacks f :=
  K.hasPullbacks_of_mem _ E.mem₀

instance {X Y : C} (E : PreZeroHypercover X) (f : Y ⟶ X) [E.presieve₀.HasPullbacks f]
    (i : E.I₀) : HasPullback (E.f i) f :=
  E.presieve₀.hasPullback f ⟨i⟩

instance {X Y : C} (E : PreZeroHypercover X) (f : Y ⟶ X) [E.presieve₀.HasPullbacks f]
    (i : E.I₀) : HasPullback f (E.f i) :=
  hasPullback_symmetry (E.f i) f

variable (J) in
/--
Definition of `Hom` / `Hom` 的定义

English:
abbreviation Hom
  signature: (E : ZeroHypercover.{w} J S) (F : ZeroHypercover.{w'} J S)
  body: E.toPreZeroHypercover.Hom F.toPreZeroHypercover

中文:
缩写 态射
  签名: (E : ZeroHypercover.{w} J S) (F : ZeroHypercover.{w'} J S)
  定义体: E.toPreZeroHypercover.Hom F.toPreZeroHypercover

Depends on / 依赖: E.toPreZeroHypercover.Hom, F.toPreZeroHypercover, toPreZeroHypercover
-/
abbrev Hom (E : ZeroHypercover.{w} J S) (F : ZeroHypercover.{w'} J S) :=
  E.toPreZeroHypercover.Hom F.toPreZeroHypercover

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simps! id_s₀ id_h₀ comp_s₀ comp_h₀]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category (ZeroHypercover.{w} J S)
  body: Hom J
  id _ := PreZeroHypercover.Hom.id _
  comp := PreZeroHypercover.Hom.comp

中文:
实例 :
  签名: 范畴 (ZeroHypercover.{w} J S)
  定义体: Hom J
  id _ := PreZeroHypercover.Hom.id _
  comp := PreZeroHypercover.Hom.comp
-/
instance : Category (ZeroHypercover.{w} J S) where
  Hom := Hom J
  id _ := PreZeroHypercover.Hom.id _
  comp := PreZeroHypercover.Hom.comp

set_option backward.isDefEq.respectTransparency.types false in
/-- An isomorphism in `0`-hypercovers is an isomorphism of the underlying pre-`0`-hypercovers. -/
@[simps]
/--
Definition of `isoMk` / `isoMk` 的定义

English:
definition isoMk
  signature: {E F : ZeroHypercover.{w} J S} (e : E.toPreZeroHypercover ≅ F.toPreZeroHypercover)
  body: e.hom
  inv := e.inv
  hom_inv_id := e.hom_inv_id
  inv_hom_id := e.inv_hom_id

中文:
定义 isoMk
  签名: {E F : ZeroHypercover.{w} J S} (e : E.toPreZeroHypercover ≅ F.toPreZeroHypercover)
  定义体: e.hom
  inv := e.inv
  hom_inv_id := e.hom_inv_id
  inv_hom_id := e.inv_hom_id

Depends on / 依赖: e.hom
-/
def isoMk {E F : ZeroHypercover.{w} J S} (e : E.toPreZeroHypercover ≅ F.toPreZeroHypercover) :
    E ≅ F where
  hom := e.hom
  inv := e.inv
  hom_inv_id := e.hom_inv_id
  inv_hom_id := e.inv_hom_id

section Functoriality

variable {D : Type*} [Category* D] {F : C ⥤ D} {K : Precoverage D}

/-- The image of a `0`-hypercover under a functor. -/
@[simps toPreZeroHypercover]
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (F : C ⥤ D) (E : ZeroHypercover.{w} J S) (h : J <= K.comap F)
  body: E.toPreZeroHypercover.map F
  mem₀ := by
    rw [PreZeroHypercover.presieve₀_map]; rw [← mem_comap_iff]
    exact h _ E.mem₀

中文:
定义 map
  签名: (F : C ⥤ D) (E : ZeroHypercover.{w} J S) (h : J <= K.comap F)
  定义体: E.toPreZeroHypercover.map F
  mem₀ := by
    rw [PreZeroHypercover.presieve₀_map]; rw [← mem_comap_iff]
    exact h _ E.mem₀

Depends on / 依赖: E.toPreZeroHypercover.map, toPreZeroHypercover
-/
def map (F : C ⥤ D) (E : ZeroHypercover.{w} J S) (h : J <= K.comap F) :
    ZeroHypercover.{w} K (F.obj S) where
  __ := E.toPreZeroHypercover.map F
  mem₀ := by
    rw [PreZeroHypercover.presieve₀_map]; rw [← mem_comap_iff]
    exact h _ E.mem₀

end Functoriality

/--
lemma `presieve₀_mem_of_iso` / 引理 `presieve₀_mem_of_iso`

English:
lemma presieve₀_mem_of_iso
  statement: [J.RespectsIso] {S : C} {E : J.ZeroHypercover S}
  proof: E.toPreZeroHypercover.presieve₀_mem_of_iso e E.mem₀

中文:
引理 presieve₀_mem_of_iso
  结论: [J.RespectsIso] {S : C} {E : J.ZeroHypercover S}
  证明: E.toPreZeroHypercover.presieve₀_mem_of_iso e E.mem₀

Depends on / 依赖: E.mem, E.toPreZeroHypercover.presieve, toPreZeroHypercover
-/
lemma presieve₀_mem_of_iso [J.RespectsIso] {S : C} {E : J.ZeroHypercover S}
    {F : PreZeroHypercover.{w} S} (e : E.toPreZeroHypercover ≅ F) :
    F.presieve₀ in J S :=
  E.toPreZeroHypercover.presieve₀_mem_of_iso e E.mem₀

/--
Definition of `Small` / `Small` 的定义

English:
class Small
  parameters: (E : ZeroHypercover.{w} J S)
  axioms and operations (1):
    - exists_restrictIndex_mem((E)) : exists (ι : Type w') (f : ι -> E.I₀), (E.restrictIndex f).presieve₀ in J S

中文:
类 Small
  参数: (E : ZeroHypercover.{w} J S)
  公理与运算 (1 个):
    - exists_restrictIndex_mem((E)) : 存在 (ι : 类型 w') (f : ι -> E.I₀), (E.restrictIndex f).presieve₀ in J S
-/
protected class Small (E : ZeroHypercover.{w} J S) where
  exists_restrictIndex_mem (E) : exists (ι : Type w') (f : ι -> E.I₀), (E.restrictIndex f).presieve₀ in J S

instance (E : ZeroHypercover.{w} J S) [Small.{w'} E.I₀] : ZeroHypercover.Small.{w'} E where
  exists_restrictIndex_mem := ⟨_, (equivShrink E.I₀).symm, by simp [E.mem₀]⟩

/--
Definition of `Small.Index` / `Small.Index` 的定义

English:
definition Small.Index
  signature: (E : ZeroHypercover.{w} J S) [ZeroHypercover.Small.{w'} E]
  body: (Small.exists_restrictIndex_mem E).choose

中文:
定义 Small.Index
  签名: (E : ZeroHypercover.{w} J S) [ZeroHypercover.Small.{w'} E]
  定义体: (Small.exists_restrictIndex_mem E).choose

Depends on / 依赖: Small.exists_restrictIndex_mem, exists_restrictIndex_mem
-/
def Small.Index (E : ZeroHypercover.{w} J S) [ZeroHypercover.Small.{w'} E] : Type w' :=
  (Small.exists_restrictIndex_mem E).choose

/--
Definition of `Small.restrictFun` / `Small.restrictFun` 的定义

English:
definition Small.restrictFun
  signature: (E : ZeroHypercover.{w} J S) [ZeroHypercover.Small.{w'} E]
  body: (Small.exists_restrictIndex_mem E).choose_spec.choose

中文:
定义 Small.restrictFun
  签名: (E : ZeroHypercover.{w} J S) [ZeroHypercover.Small.{w'} E]
  定义体: (Small.exists_restrictIndex_mem E).choose_spec.choose

Depends on / 依赖: Small.exists_restrictIndex_mem, choose_spec, choose_spec.choose, exists_restrictIndex_mem
-/
noncomputable def Small.restrictFun (E : ZeroHypercover.{w} J S) [ZeroHypercover.Small.{w'} E] :
    Index E -> E.I₀ :=
  (Small.exists_restrictIndex_mem E).choose_spec.choose

/--
lemma `Small.mem₀` / 引理 `Small.mem₀`

English:
lemma Small.mem₀
  given: (E : ZeroHypercover.{w} J S) [ZeroHypercover.Small.{w'} E]
  proof: (Small.exists_restrictIndex_mem E).choose_spec.choose_spec

中文:
引理 Small.mem₀
  条件: (E : ZeroHypercover.{w} J S) [ZeroHypercover.Small.{w'} E]
  证明: (Small.exists_restrictIndex_mem E).choose_spec.choose_spec

Depends on / 依赖: Small.exists_restrictIndex_mem, choose_spec, choose_spec.choose_spec, exists_restrictIndex_mem
-/
lemma Small.mem₀ (E : ZeroHypercover.{w} J S) [ZeroHypercover.Small.{w'} E] :
    (E.restrictIndex <| Small.restrictFun E).presieve₀ in J S :=
  (Small.exists_restrictIndex_mem E).choose_spec.choose_spec

instance (E : ZeroHypercover.{w} J S) : ZeroHypercover.Small.{max u v} E where
  exists_restrictIndex_mem := by
    obtain ⟨ι, Y, f, h⟩ := E.presieve₀.exists_eq_ofArrows
    have (Z : C) (g : Z ⟶ S) (hg : Presieve.ofArrows Y f g) :
        exists (j : E.I₀) (h : Z = E.X j), g = eqToHom h ≫ E.f j := by
      obtain ⟨j⟩ : E.presieve₀ g := by rwa [h]
      use j, rfl
      simp
    choose j h₁ h₂ using this
    refine ⟨ι, fun i => j _ _ (.mk i), ?_⟩
    convert! E.mem₀
    exact le_antisymm (fun Z g ⟨i⟩ => ⟨_⟩) (h ▸ fun Z g ⟨i⟩ => .mk' i (h₁ _ _ _) (h₂ _ _ _))

/-- Restrict a `w'`-small `0`-hypercover to a `w'`-`0`-hypercover. -/
@[simps toPreZeroHypercover]
noncomputable
/--
Definition of `restrictIndexOfSmall` / `restrictIndexOfSmall` 的定义

English:
definition restrictIndexOfSmall
  signature: (E : ZeroHypercover.{w} J S) [ZeroHypercover.Small.{w'} E]
  body: E.toPreZeroHypercover.restrictIndex (Small.restrictFun E)
  mem₀ := Small.mem₀ E

中文:
定义 restrictIndexOfSmall
  签名: (E : ZeroHypercover.{w} J S) [ZeroHypercover.Small.{w'} E]
  定义体: E.toPreZeroHypercover.restrictIndex (Small.restrictFun E)
  mem₀ := Small.mem₀ E

Depends on / 依赖: E.toPreZeroHypercover.restrictIndex, Small.restrictFun, restrictFun, restrictIndex, toPreZeroHypercover
-/
def restrictIndexOfSmall (E : ZeroHypercover.{w} J S) [ZeroHypercover.Small.{w'} E] :
    ZeroHypercover.{w'} J S where
  __ := E.toPreZeroHypercover.restrictIndex (Small.restrictFun E)
  mem₀ := Small.mem₀ E

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
instance (E : ZeroHypercover.{w} J S) [ZeroHypercover.Small.{w'} E] {T : C} (f : T ⟶ S)
    [IsStableUnderBaseChange J] [forall (i : E.I₀), HasPullback f (E.f i)] :
    ZeroHypercover.Small.{w'} (E.pullback₁ f) := by
  use Small.Index E, Small.restrictFun E
  have _ (i) : HasPullback f (E.restrictIndexOfSmall.f i) := by dsimp; infer_instance
  exact ((restrictIndexOfSmall.{w'} E).pullback₁ f).mem₀

end ZeroHypercover

/--
lemma `mem_iff_exists_zeroHypercover` / 引理 `mem_iff_exists_zeroHypercover`

English:
lemma mem_iff_exists_zeroHypercover
  given: {X : C} {R : Presieve X}
  proof: by
  refine ⟨fun hR => ?_, fun ⟨𝒰, hR⟩ => hR ▸ 𝒰.mem₀⟩
  obtain ⟨ι, Y, f, rfl⟩ := R.exists_eq_ofArrows
  use ⟨⟨ι, Y, f⟩, hR⟩

中文:
引理 mem_iff_存在_zeroHypercover
  条件: {X : C} {R : Presieve X}
  证明: by
  refine ⟨fun hR => ?_, fun ⟨𝒰, hR⟩ => hR ▸ 𝒰.mem₀⟩
  obtain ⟨ι, Y, f, rfl⟩ := R.exists_eq_ofArrows
  use ⟨⟨ι, Y, f⟩, hR⟩

Depends on / 依赖: R.exists_eq_ofArrows, exists_eq_ofArrows
-/
lemma mem_iff_exists_zeroHypercover {X : C} {R : Presieve X} :
    R in J X ↔ exists (𝒰 : ZeroHypercover.{max u v} J X), R = Presieve.ofArrows 𝒰.X 𝒰.f := by
  refine ⟨fun hR => ?_, fun ⟨𝒰, hR⟩ => hR ▸ 𝒰.mem₀⟩
  obtain ⟨ι, Y, f, rfl⟩ := R.exists_eq_ofArrows
  use ⟨⟨ι, Y, f⟩, hR⟩

/--
lemma `le_of_zeroHypercover` / 引理 `le_of_zeroHypercover`

English:
lemma le_of_zeroHypercover
  statement: {J K : Precoverage C}
  proof: by
  intro X R hR
  obtain ⟨E, rfl⟩ := R.exists_eq_preZeroHypercover
  exact h (E := ⟨E, hR⟩)

中文:
引理 le_of_zeroHypercover
  结论: {J K : Precoverage C}
  证明: by
  intro X R hR
  obtain ⟨E, rfl⟩ := R.exists_eq_preZeroHypercover
  exact h (E := ⟨E, hR⟩)

Depends on / 依赖: R.exists_eq_preZeroHypercover, exists_eq_preZeroHypercover
-/
lemma le_of_zeroHypercover {J K : Precoverage C}
    (h : forall ⦃X : C⦄ ⦃E : ZeroHypercover.{max u v} J X⦄, E.presieve₀ in K X) :
    J <= K := by
  intro X R hR
  obtain ⟨E, rfl⟩ := R.exists_eq_preZeroHypercover
  exact h (E := ⟨E, hR⟩)

/--
Definition of `Small` / `Small` 的定义

English:
class Small
  parameters: (J : Precoverage C)
  axioms and operations (1):
    - zeroHypercoverSmall : forall {S : C} (E : ZeroHypercover.{max u v} J S), ZeroHypercover.Small.{w'} E

中文:
类 Small
  参数: (J : Precoverage C)
  公理与运算 (1 个):
    - zeroHypercoverSmall : 对任意 {S : C} (E : ZeroHypercover.{最大值 u v} J S), ZeroHypercover.Small.{w'} E
-/
class Small (J : Precoverage C) : Prop where
  zeroHypercoverSmall : forall {S : C} (E : ZeroHypercover.{max u v} J S), ZeroHypercover.Small.{w'} E

instance (K : Precoverage C) : Small.{max u v} K where
  zeroHypercoverSmall := inferInstance

instance (J : Precoverage C) [Small.{w} J] {S : C} (E : ZeroHypercover.{w'} J S) :
    ZeroHypercover.Small.{w} E := by
  have : ZeroHypercover.Small.{w} (ZeroHypercover.restrictIndexOfSmall.{max u v} E) :=
    Small.zeroHypercoverSmall _
  let E' := ZeroHypercover.restrictIndexOfSmall.{w}
    (ZeroHypercover.restrictIndexOfSmall.{max u v} E)
  use E'.I₀, ZeroHypercover.Small.restrictFun _ ∘ ZeroHypercover.Small.restrictFun _
  exact E'.mem₀

instance {D : Type*} [Category* D] {F : C ⥤ D} (J : Precoverage D) [Small.{w} J] :
    Small.{w} (J.comap F) where
  zeroHypercoverSmall {X} E := by
    refine ⟨(E.map F le_rfl).restrictIndexOfSmall.I₀, ZeroHypercover.Small.restrictFun _, ?_⟩
    simpa using! (E.map F le_rfl).restrictIndexOfSmall.mem₀

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `Small.inf` / 引理 `Small.inf`

English:
lemma Small.inf
  statement: {J K : Precoverage C} [Small.{w} J]
  proof: by
    refine ⟨(E.weaken (inf_le_left)).restrictIndexOfSmall.I₀,
        ZeroHypercover.Small.restrictFun _, ⟨?_, ?_⟩⟩
    · exact (E.weaken (inf_le_left)).restrictIndexOfSmall.mem₀
    · exact of_le (by simp) E.mem₀.2

中文:
引理 Small.下确界
  结论: {J K : Precoverage C} [Small.{w} J]
  证明: by
    refine ⟨(E.weaken (inf_le_left)).restrictIndexOfSmall.I₀,
        ZeroHypercover.Small.restrictFun _, ⟨?_, ?_⟩⟩
    · exact (E.weaken (inf_le_left)).restrictIndexOfSmall.mem₀
    · exact of_le (by simp) E.mem₀.2

Depends on / 依赖: E.mem, E.weaken, ZeroHypercover, ZeroHypercover.Small.restrictFun, inf_le_left, of_le, restrictFun, restrictIndexOfSmall, restrictIndexOfSmall.I, restrictIndexOfSmall.mem, weaken
-/
lemma Small.inf {J K : Precoverage C} [Small.{w} J]
    (of_le : forall ⦃X : C⦄ ⦃R S : Presieve X⦄, R <= S -> S in K X -> R in K X) :
    Small.{w} (J ⊓ K) where
  zeroHypercoverSmall {S} E := by
    refine ⟨(E.weaken (inf_le_left)).restrictIndexOfSmall.I₀,
        ZeroHypercover.Small.restrictFun _, ⟨?_, ?_⟩⟩
    · exact (E.weaken (inf_le_left)).restrictIndexOfSmall.mem₀
    · exact of_le (by simp) E.mem₀.2

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsStableUnderBaseChange
  signature: J] : RespectsIso J where
  body: by
    refine J.mem_coverings_of_isPullback (fun i => E.f (e.inv.s₀ i)) ?_ (𝟙 S) _ (fun i => ?_) ?_
    · convert! h
      exact Presieve.ofArrows_comp_eq_of_surjective _ (fun i => ⟨e.hom.s₀ i, by simp⟩)
    · exact e.inv.h₀ i
    · intro i
      exact CategoryTheory.IsPullback.of_vert_isIso (by sim

中文:
实例 [是StableUnderBaseChange
  签名: J] : RespectsIso J where
  定义体: by
    refine J.mem_coverings_of_isPullback (fun i => E.f (e.inv.s₀ i)) ?_ (𝟙 S) _ (fun i => ?_) ?_
    · convert! h
      exact Presieve.ofArrows_comp_eq_of_surjective _ (fun i => ⟨e.hom.s₀ i, by simp⟩)
    · exact e.inv.h₀ i
    · intro i
      exact CategoryTheory.IsPullback.of_vert_isIso (by sim

Depends on / 依赖: CategoryTheory, CategoryTheory.IsPullback.of_vert_isIso, IsPullback, J.mem_coverings_of_isPullback, Presieve, Presieve.ofArrows_comp_eq_of_surjective, convert, e.hom.s, e.inv.h, e.inv.s, mem_coverings_of_isPullback, ofArrows_comp_eq_of_surjective, of_vert_isIso
-/
instance [IsStableUnderBaseChange J] : RespectsIso J where
  of_iso {S E F} e h := by
    refine J.mem_coverings_of_isPullback (fun i => E.f (e.inv.s₀ i)) ?_ (𝟙 S) _ (fun i => ?_) ?_
    · convert! h
      exact Presieve.ofArrows_comp_eq_of_surjective _ (fun i => ⟨e.hom.s₀ i, by simp⟩)
    · exact e.inv.h₀ i
    · intro i
      exact CategoryTheory.IsPullback.of_vert_isIso (by simp)

namespace ZeroHypercover

variable [J.IsStableUnderBaseChange]

/-- If `{Uᵢ}` covers `X`, this is the `0`-hypercover of `X ×[Z] Y` given by `{Uᵢ ×[Z] Y}`. -/
@[simps toPreZeroHypercover]
/--
Definition of `pullbackCoverOfLeft` / `pullbackCoverOfLeft` 的定义

English:
definition pullbackCoverOfLeft
  signature: {X : C} (E : J.ZeroHypercover X) {Y Z : C}
  body: E.toPreZeroHypercover.pullbackCoverOfLeft f g
  mem₀ := (E.pullback₁ (pullback.fst f g)).presieve₀_mem_of_iso
    (E.pullbackCoverOfLeftIsoPullback₁ _ _).symm

中文:
定义 pullbackCoverOfLeft
  签名: {X : C} (E : J.ZeroHypercover X) {Y Z : C}
  定义体: E.toPreZeroHypercover.pullbackCoverOfLeft f g
  mem₀ := (E.pullback₁ (pullback.fst f g)).presieve₀_mem_of_iso
    (E.pullbackCoverOfLeftIsoPullback₁ _ _).symm

Depends on / 依赖: E.toPreZeroHypercover.pullbackCoverOfLeft, pullbackCoverOfLeft, toPreZeroHypercover
-/
noncomputable def pullbackCoverOfLeft {X : C} (E : J.ZeroHypercover X) {Y Z : C}
    (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] [forall i, HasPullback (E.f i) (pullback.fst f g)] :
    J.ZeroHypercover (pullback f g) where
  __ := E.toPreZeroHypercover.pullbackCoverOfLeft f g
  mem₀ := (E.pullback₁ (pullback.fst f g)).presieve₀_mem_of_iso
    (E.pullbackCoverOfLeftIsoPullback₁ _ _).symm

/-- If `{Uᵢ}` covers `Y`, this is the `0`-hypercover of `X ×[Z] Y` given by `{X ×[Z] Uᵢ}`. -/
@[simps toPreZeroHypercover]
/--
Definition of `pullbackCoverOfRight` / `pullbackCoverOfRight` 的定义

English:
definition pullbackCoverOfRight
  signature: {Y : C} (E : J.ZeroHypercover Y) {X Z : C}
  body: E.toPreZeroHypercover.pullbackCoverOfRight f g
  mem₀ := (E.pullback₂ (pullback.snd f g)).presieve₀_mem_of_iso
    (E.pullbackCoverOfRightIsoPullback₂ _ _).symm

中文:
定义 pullbackCoverOfRight
  签名: {Y : C} (E : J.ZeroHypercover Y) {X Z : C}
  定义体: E.toPreZeroHypercover.pullbackCoverOfRight f g
  mem₀ := (E.pullback₂ (pullback.snd f g)).presieve₀_mem_of_iso
    (E.pullbackCoverOfRightIsoPullback₂ _ _).symm

Depends on / 依赖: E.toPreZeroHypercover.pullbackCoverOfRight, pullbackCoverOfRight, toPreZeroHypercover
-/
noncomputable def pullbackCoverOfRight {Y : C} (E : J.ZeroHypercover Y) {X Z : C}
    (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] [forall i, HasPullback (E.f i) (pullback.snd f g)] :
    J.ZeroHypercover (pullback f g) where
  __ := E.toPreZeroHypercover.pullbackCoverOfRight f g
  mem₀ := (E.pullback₂ (pullback.snd f g)).presieve₀_mem_of_iso
    (E.pullbackCoverOfRightIsoPullback₂ _ _).symm

end ZeroHypercover

end Precoverage

end CategoryTheory
