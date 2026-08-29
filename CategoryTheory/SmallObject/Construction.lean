/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.AlgebraicTopology.RelativeCellComplex.AttachCells

/-!
# Construction for the small object argument

Given a family of morphisms `f i : A i ⟶ B i` in a category `C`,
we define a functor
`SmallObject.functor f : Arrow S ⥤ Arrow S` which sends
an object given by arrow `πX : X ⟶ S` to the pushout `functorObj f πX`:
```
∐ functorObjSrcFamily f πX ⟶ X

            | |
            | |
            v v

∐ functorObjTgtFamily f πX ⟶ functorObj f πX
```
where the morphism on the left is a coproduct (of copies of maps `f i`)
indexed by a type `FunctorObjIndex f πX` which parametrizes the
diagrams of the form
```
A i ⟶ X
 | |
 | |
 v v
B i ⟶ S
```

The morphism `ιFunctorObj f πX : X ⟶ functorObj f πX` is part of
a natural transformation `SmallObject.ε f : 𝟭 (Arrow C) ⟶ functor f S`.
The main idea in this construction is that for any commutative square
as above, there may not exist a lifting `B i ⟶ X`, but the construction
provides a tautological morphism `B i ⟶ functorObj f πX`
(see `SmallObject.ιFunctorObj_extension`).

## References
- https://ncatlab.org/nlab/show/small+object+argument

-/

@[expose] public section
universe t w v u

namespace CategoryTheory

open Category Limits HomotopicalAlgebra

namespace SmallObject

variable {C : Type u} [Category.{v} C] {I : Type w} {A B : I -> C} (f : forall i, A i ⟶ B i)

section

variable {S X : C} (πX : X ⟶ S)

/--
Definition of `FunctorObjIndex` / `FunctorObjIndex` 的定义

English:
structure FunctorObjIndex
  parameters: where
  axioms and operations (4):
    - i : I
    - t : A i ⟶ X
    - b : B i ⟶ S
    - w : t ≫ πX = f i ≫ b

中文:
结构 FunctorObjIndex
  参数: where
  公理与运算 (4 个):
    - i : I
    - t : A i ⟶ X
    - b : B i ⟶ S
    - w : t ≫ πX = f i ≫ b

Depends on / 依赖: FunctorObjIndex, FunctorObjIndex.w
-/
structure FunctorObjIndex where
  /-- an element in the index type -/
  i : I
  /-- the top morphism in the square -/
  t : A i ⟶ X
  /-- the bottom morphism in the square -/
  b : B i ⟶ S
  w : t ≫ πX = f i ≫ b

attribute [reassoc (attr := simp)] FunctorObjIndex.w

variable [HasColimitsOfShape (Discrete (FunctorObjIndex f πX)) C]

/--
Definition of `functorObjSrcFamily` / `functorObjSrcFamily` 的定义

English:
abbreviation functorObjSrcFamily
  signature: (x : FunctorObjIndex f πX)
  body: A x.i

中文:
缩写 functorObjSrcFamily
  签名: (x : FunctorObjIndex f πX)
  定义体: A x.i
-/
abbrev functorObjSrcFamily (x : FunctorObjIndex f πX) : C := A x.i

/--
Definition of `functorObjTgtFamily` / `functorObjTgtFamily` 的定义

English:
abbreviation functorObjTgtFamily
  signature: (x : FunctorObjIndex f πX)
  body: B x.i

中文:
缩写 functorObjTgtFamily
  签名: (x : FunctorObjIndex f πX)
  定义体: B x.i
-/
abbrev functorObjTgtFamily (x : FunctorObjIndex f πX) : C := B x.i

/--
Definition of `functorObjLeftFamily` / `functorObjLeftFamily` 的定义

English:
abbreviation functorObjLeftFamily
  signature: (x : FunctorObjIndex f πX)
  body: f x.i

中文:
缩写 functorObjLeftFamily
  签名: (x : FunctorObjIndex f πX)
  定义体: f x.i
-/
abbrev functorObjLeftFamily (x : FunctorObjIndex f πX) :
    functorObjSrcFamily f πX x ⟶ functorObjTgtFamily f πX x := f x.i

/--
Definition of `functorObjTop` / `functorObjTop` 的定义

English:
abbreviation functorObjTop
  signature: : ∐ functorObjSrcFamily f πX ⟶ X
  body: Limits.Sigma.desc (fun x => x.t)

中文:
缩写 functorObjTop
  签名: : ∐ functorObjSrcFamily f πX ⟶ X
  定义体: Limits.Sigma.desc (fun x => x.t)

Depends on / 依赖: Limits, Limits.Sigma.desc
-/
noncomputable abbrev functorObjTop : ∐ functorObjSrcFamily f πX ⟶ X :=
  Limits.Sigma.desc (fun x => x.t)

/--
Definition of `functorObjLeft` / `functorObjLeft` 的定义

English:
abbreviation functorObjLeft
  signature: :
  body: Limits.Sigma.map (functorObjLeftFamily f πX)

中文:
缩写 functorObjLeft
  签名: :
  定义体: Limits.Sigma.map (functorObjLeftFamily f πX)

Depends on / 依赖: Limits, Limits.Sigma.map, functorObjLeftFamily
-/
noncomputable abbrev functorObjLeft :
    ∐ functorObjSrcFamily f πX ⟶ ∐ functorObjTgtFamily f πX :=
  Limits.Sigma.map (functorObjLeftFamily f πX)

variable [HasPushout (functorObjTop f πX) (functorObjLeft f πX)]

/--
Definition of `functorObj` / `functorObj` 的定义

English:
abbreviation functorObj
  signature: : C
  body: pushout (functorObjTop f πX) (functorObjLeft f πX)

中文:
缩写 functorObj
  签名: : C
  定义体: pushout (functorObjTop f πX) (functorObjLeft f πX)

Depends on / 依赖: functorObjLeft, functorObjTop, pushout
-/
noncomputable abbrev functorObj : C :=
  pushout (functorObjTop f πX) (functorObjLeft f πX)

/--
Definition of `ιFunctorObj` / `ιFunctorObj` 的定义

English:
abbreviation ιFunctorObj
  signature: : X ⟶ functorObj f πX
  body: pushout.inl _ _

中文:
缩写 ιFunctorObj
  签名: : X ⟶ functorObj f πX
  定义体: pushout.inl _ _

Depends on / 依赖: pushout, pushout.inl
-/
noncomputable abbrev ιFunctorObj : X ⟶ functorObj f πX := pushout.inl _ _

/--
Definition of `ρFunctorObj` / `ρFunctorObj` 的定义

English:
abbreviation ρFunctorObj
  signature: : ∐ functorObjTgtFamily f πX ⟶ functorObj f πX
  body: pushout.inr _ _

@[reassoc]

中文:
缩写 ρFunctorObj
  签名: : ∐ functorObjTgtFamily f πX ⟶ functorObj f πX
  定义体: pushout.inr _ _

@[reassoc]

Depends on / 依赖: pushout, pushout.inr
-/
noncomputable abbrev ρFunctorObj : ∐ functorObjTgtFamily f πX ⟶ functorObj f πX := pushout.inr _ _

@[reassoc]
/--
lemma `functorObj_comm` / 引理 `functorObj_comm`

English:
lemma functorObj_comm
  proof: pushout.condition

中文:
引理 functorObj_comm
  证明: pushout.condition

Depends on / 依赖: condition, pushout, pushout.condition
-/
lemma functorObj_comm :
    functorObjTop f πX ≫ ιFunctorObj f πX = functorObjLeft f πX ≫ ρFunctorObj f πX :=
  pushout.condition

/--
lemma `functorObj_isPushout` / 引理 `functorObj_isPushout`

English:
lemma functorObj_isPushout
  proof: IsPushout.of_hasPushout _ _

中文:
引理 functorObj_isPushout
  证明: IsPushout.of_hasPushout _ _

Depends on / 依赖: IsPushout, IsPushout.of_hasPushout, of_hasPushout
-/
lemma functorObj_isPushout :
    IsPushout (functorObjTop f πX) (functorObjLeft f πX) (ιFunctorObj f πX) (ρFunctorObj f πX) :=
  IsPushout.of_hasPushout _ _

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `FunctorObjIndex.comm` / 引理 `FunctorObjIndex.comm`

English:
lemma FunctorObjIndex.comm
  given: (x : FunctorObjIndex f πX)
  proof: by
  simpa using (Sigma.ι (functorObjSrcFamily f πX) x ≫= functorObj_comm f πX).symm

中文:
引理 FunctorObjIndex.comm
  条件: (x : FunctorObjIndex f πX)
  证明: by
  simpa using (Sigma.ι (functorObjSrcFamily f πX) x ≫= functorObj_comm f πX).symm

Depends on / 依赖: functorObjSrcFamily, functorObj_comm
-/
lemma FunctorObjIndex.comm (x : FunctorObjIndex f πX) :
    f x.i ≫ Sigma.ι (functorObjTgtFamily f πX) x ≫ ρFunctorObj f πX = x.t ≫ ιFunctorObj f πX := by
  simpa using (Sigma.ι (functorObjSrcFamily f πX) x ≫= functorObj_comm f πX).symm

/--
Definition of `π'FunctorObj` / `π'FunctorObj` 的定义

English:
abbreviation π'FunctorObj
  signature: : ∐ functorObjTgtFamily f πX ⟶ S
  body: Sigma.desc (fun x => x.b)

中文:
缩写 π'FunctorObj
  签名: : ∐ functorObjTgtFamily f πX ⟶ S
  定义体: Sigma.desc (fun x => x.b)

Depends on / 依赖: Sigma.desc
-/
noncomputable abbrev π'FunctorObj : ∐ functorObjTgtFamily f πX ⟶ S := Sigma.desc (fun x => x.b)

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `πFunctorObj` / `πFunctorObj` 的定义

English:
definition πFunctorObj
  signature: : functorObj f πX ⟶ S
  body: pushout.desc πX (π'FunctorObj f πX) (by ext; simp [π'FunctorObj])

中文:
定义 πFunctorObj
  签名: : functorObj f πX ⟶ S
  定义体: pushout.desc πX (π'FunctorObj f πX) (by ext; simp [π'FunctorObj])

Depends on / 依赖: FunctorObj, pushout, pushout.desc
-/
noncomputable def πFunctorObj : functorObj f πX ⟶ S :=
  pushout.desc πX (π'FunctorObj f πX) (by ext; simp [π'FunctorObj])

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `ρFunctorObj_π` / 引理 `ρFunctorObj_π`

English:
lemma ρFunctorObj_π
  statement: ρFunctorObj f πX ≫ πFunctorObj f πX = π'FunctorObj f πX
  proof: by
  simp [πFunctorObj]

中文:
引理 ρFunctorObj_π
  结论: ρFunctorObj f πX ≫ πFunctorObj f πX = π'FunctorObj f πX
  证明: by
  simp [πFunctorObj]
-/
lemma ρFunctorObj_π : ρFunctorObj f πX ≫ πFunctorObj f πX = π'FunctorObj f πX := by
  simp [πFunctorObj]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `ιFunctorObj_πFunctorObj` / 引理 `ιFunctorObj_πFunctorObj`

English:
lemma ιFunctorObj_πFunctorObj
  statement: ιFunctorObj f πX ≫ πFunctorObj f πX = πX
  proof: by
  simp [ιFunctorObj, πFunctorObj]

中文:
引理 ιFunctorObj_πFunctorObj
  结论: ιFunctorObj f πX ≫ πFunctorObj f πX = πX
  证明: by
  simp [ιFunctorObj, πFunctorObj]
-/
lemma ιFunctorObj_πFunctorObj : ιFunctorObj f πX ≫ πFunctorObj f πX = πX := by
  simp [ιFunctorObj, πFunctorObj]

set_option backward.defeqAttrib.useBackward true in
/-- The morphism `ιFunctorObj f πX : X ⟶ functorObj f πX` is obtained by
attaching `f`-cells. -/
@[simps]
/--
Definition of `attachCellsιFunctorObj` / `attachCellsιFunctorObj` 的定义

English:
definition attachCellsιFunctorObj
  signature: :
  body: FunctorObjIndex f πX
  π x := x.i
  isColimit₁ := coproductIsCoproduct _
  isColimit₂ := coproductIsCoproduct _
  m := functorObjLeft f πX
  g₁ := functorObjTop f πX
  g₂ := ρFunctorObj f πX
  isPushout := IsPushout.of_hasPushout (functorObjTop f πX) (functorObjLeft f πX)
  cofan₁ := _
  cofan₂ := _

中文:
定义 attachCellsιFunctorObj
  签名: :
  定义体: FunctorObjIndex f πX
  π x := x.i
  isColimit₁ := coproductIsCoproduct _
  isColimit₂ := coproductIsCoproduct _
  m := functorObjLeft f πX
  g₁ := functorObjTop f πX
  g₂ := ρFunctorObj f πX
  isPushout := IsPushout.of_hasPushout (functorObjTop f πX) (functorObjLeft f πX)
  cofan₁ := _
  cofan₂ := _

Depends on / 依赖: FunctorObjIndex
-/
noncomputable def attachCellsιFunctorObj :
    AttachCells.{max v w} f (ιFunctorObj f πX) where
  ι := FunctorObjIndex f πX
  π x := x.i
  isColimit₁ := coproductIsCoproduct _
  isColimit₂ := coproductIsCoproduct _
  m := functorObjLeft f πX
  g₁ := functorObjTop f πX
  g₂ := ρFunctorObj f πX
  isPushout := IsPushout.of_hasPushout (functorObjTop f πX) (functorObjLeft f πX)
  cofan₁ := _
  cofan₂ := _

section Small

variable [LocallySmall.{t} C] [Small.{t} I]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Small.{t} (FunctorObjIndex f πX)
  body: by
  let φ (x : FunctorObjIndex f πX) :
    Σ (i : Shrink.{t} I),
      Shrink.{t} ((A ((equivShrink _).symm i) ⟶ X) ×
        (B ((equivShrink _).symm i) ⟶ S)) :=
        ⟨equivShrink _ x.i, equivShrink _
          ⟨eqToHom (by simp) ≫ x.t, eqToHom (by simp) ≫ x.b⟩⟩
  have hφ : Function.Injective φ := by
    rintro ⟨i₁, t₁, b₁, _⟩ ⟨i₂, t₂, b₂, _⟩ h
    obtain rfl : i₁ = i₂ := by simpa [φ] using congr_arg Sigma.fst h
    simpa [cancel_epi, φ] using h
  exact small_of_injective hφ

中文:
实例 :
  签名: Small.{t} (FunctorObjIndex f πX)
  定义体: by
  let φ (x : FunctorObjIndex f πX) :
    Σ (i : Shrink.{t} I),
      Shrink.{t} ((A ((equivShrink _).symm i) ⟶ X) ×
        (B ((equivShrink _).symm i) ⟶ S)) :=
        ⟨equivShrink _ x.i, equivShrink _
          ⟨eqToHom (by simp) ≫ x.t, eqToHom (by simp) ≫ x.b⟩⟩
  have hφ : Function.Injective φ := by
    rintro ⟨i₁, t₁, b₁, _⟩ ⟨i₂, t₂, b₂, _⟩ h
    obtain rfl : i₁ = i₂ := by simpa [φ] using congr_arg Sigma.fst h
    simpa [cancel_epi, φ] using h
  exact small_of_injective hφ

Depends on / 依赖: DecidableRel, Function, Function.Injective, FunctorObjIndex, H.Adj, Injective, Shrink, Sigma.fst, cancel_epi, congr_arg, eqToHom, equivShrink, small_of_injective
-/
instance : Small.{t} (FunctorObjIndex f πX) := by
  let φ (x : FunctorObjIndex f πX) :
    Σ (i : Shrink.{t} I),
      Shrink.{t} ((A ((equivShrink _).symm i) ⟶ X) ×
        (B ((equivShrink _).symm i) ⟶ S)) :=
        ⟨equivShrink _ x.i, equivShrink _
          ⟨eqToHom (by simp) ≫ x.t, eqToHom (by simp) ≫ x.b⟩⟩
  have hφ : Function.Injective φ := by
    rintro ⟨i₁, t₁, b₁, _⟩ ⟨i₂, t₂, b₂, _⟩ h
    obtain rfl : i₁ = i₂ := by simpa [φ] using congr_arg Sigma.fst h
    simpa [cancel_epi, φ] using h
  exact small_of_injective hφ

set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Small.{t} (attachCellsιFunctorObj f πX).ι
  body: by
  dsimp
  infer_instance

中文:
实例 :
  签名: Small.{t} (attachCellsιFunctorObj f πX).ι
  定义体: by
  dsimp
  infer_instance

Depends on / 依赖: infer_instance
-/
instance : Small.{t} (attachCellsιFunctorObj f πX).ι := by
  dsimp
  infer_instance

/--
Definition of `attachCellsιFunctorObjOfSmall` / `attachCellsιFunctorObjOfSmall` 的定义

English:
definition attachCellsιFunctorObjOfSmall
  signature: :
  body: (attachCellsιFunctorObj f πX).reindex (equivShrink.{t} _).symm

中文:
定义 attachCellsιFunctorObjOfSmall
  签名: :
  定义体: (attachCellsιFunctorObj f πX).reindex (equivShrink.{t} _).symm

Depends on / 依赖: equivShrink, reindex
-/
noncomputable def attachCellsιFunctorObjOfSmall :
    AttachCells.{t} f (ιFunctorObj f πX) :=
  (attachCellsιFunctorObj f πX).reindex (equivShrink.{t} _).symm

end Small

section

variable {S T X Y : C} {πX : X ⟶ S} {πY : Y ⟶ T} (τ : Arrow.mk πX ⟶ Arrow.mk πY)
  [HasColimitsOfShape (Discrete (FunctorObjIndex f πX)) C]
  [HasColimitsOfShape (Discrete (FunctorObjIndex f πY)) C]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `functorMapSrc` / `functorMapSrc` 的定义

English:
definition functorMapSrc
  signature: :
  body: Sigma.map' (fun x => FunctorObjIndex.mk x.i (x.t ≫ τ.left) (x.b ≫ τ.right) (by simp))
    (fun _ => 𝟙 _)

中文:
定义 functorMapSrc
  签名: :
  定义体: Sigma.map' (fun x => FunctorObjIndex.mk x.i (x.t ≫ τ.left) (x.b ≫ τ.right) (by simp))
    (fun _ => 𝟙 _)

Depends on / 依赖: FunctorObjIndex, FunctorObjIndex.mk, Sigma.map
-/
noncomputable def functorMapSrc :
    ∐ (functorObjSrcFamily f πX) ⟶ ∐ functorObjSrcFamily f πY :=
  Sigma.map' (fun x => FunctorObjIndex.mk x.i (x.t ≫ τ.left) (x.b ≫ τ.right) (by simp))
    (fun _ => 𝟙 _)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `ι_functorMapSrc` / 引理 `ι_functorMapSrc`

English:
lemma ι_functorMapSrc
  statement: (i : I) (t : A i ⟶ X) (b : B i ⟶ S) (w : t ≫ πX = f i ≫ b)
  proof: by
  subst hb' ht'
  simp [functorMapSrc]

中文:
引理 ι_functorMapSrc
  结论: (i : I) (t : A i ⟶ X) (b : B i ⟶ S) (w : t ≫ πX = f i ≫ b)
  证明: by
  subst hb' ht'
  simp [functorMapSrc]
-/
lemma ι_functorMapSrc (i : I) (t : A i ⟶ X) (b : B i ⟶ S) (w : t ≫ πX = f i ≫ b)
    (b' : B i ⟶ T) (hb' : b ≫ τ.right = b')
    (t' : A i ⟶ Y) (ht' : t ≫ τ.left = t') :
    Sigma.ι _ (FunctorObjIndex.mk i t b w) ≫ functorMapSrc f τ =
      Sigma.ι (functorObjSrcFamily f πY)
        (FunctorObjIndex.mk i t' b' (by
          have := τ.w
          dsimp at this
          rw [← hb']; rw [← reassoc_of% w]; rw [← ht']; rw [assoc]; rw [this])) := by
  subst hb' ht'
  simp [functorMapSrc]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `functorMapSrc_functorObjTop` / 引理 `functorMapSrc_functorObjTop`

English:
lemma functorMapSrc_functorObjTop
  proof: by
  ext ⟨i, t, b, w⟩
  simp [ι_functorMapSrc_assoc f τ i t b w _ rfl]

中文:
引理 functorMapSrc_functorObjTop
  证明: by
  ext ⟨i, t, b, w⟩
  simp [ι_functorMapSrc_assoc f τ i t b w _ rfl]
-/
lemma functorMapSrc_functorObjTop :
    functorMapSrc f τ ≫ functorObjTop f πY = functorObjTop f πX ≫ τ.left := by
  ext ⟨i, t, b, w⟩
  simp [ι_functorMapSrc_assoc f τ i t b w _ rfl]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `functorMapTgt` / `functorMapTgt` 的定义

English:
definition functorMapTgt
  signature: :
  body: Sigma.map' (fun x => FunctorObjIndex.mk x.i (x.t ≫ τ.left) (x.b ≫ τ.right) (by simp))
    (fun _ => 𝟙 _)

中文:
定义 functorMapTgt
  签名: :
  定义体: Sigma.map' (fun x => FunctorObjIndex.mk x.i (x.t ≫ τ.left) (x.b ≫ τ.right) (by simp))
    (fun _ => 𝟙 _)

Depends on / 依赖: FunctorObjIndex, FunctorObjIndex.mk, Sigma.map
-/
noncomputable def functorMapTgt :
    ∐ functorObjTgtFamily f πX ⟶ ∐ functorObjTgtFamily f πY :=
  Sigma.map' (fun x => FunctorObjIndex.mk x.i (x.t ≫ τ.left) (x.b ≫ τ.right) (by simp))
    (fun _ => 𝟙 _)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `ι_functorMapTgt` / 引理 `ι_functorMapTgt`

English:
lemma ι_functorMapTgt
  statement: (i : I) (t : A i ⟶ X) (b : B i ⟶ S) (w : t ≫ πX = f i ≫ b)
  proof: by
  subst hb' ht'
  simp [functorMapTgt]

中文:
引理 ι_functorMapTgt
  结论: (i : I) (t : A i ⟶ X) (b : B i ⟶ S) (w : t ≫ πX = f i ≫ b)
  证明: by
  subst hb' ht'
  simp [functorMapTgt]
-/
lemma ι_functorMapTgt (i : I) (t : A i ⟶ X) (b : B i ⟶ S) (w : t ≫ πX = f i ≫ b)
    (b' : B i ⟶ T) (hb' : b ≫ τ.right = b')
    (t' : A i ⟶ Y) (ht' : t ≫ τ.left = t') :
    Sigma.ι _ (FunctorObjIndex.mk i t b w) ≫ functorMapTgt f τ =
      Sigma.ι (functorObjTgtFamily f πY)
        (FunctorObjIndex.mk i t' b' (by
          have := τ.w
          dsimp at this
          rw [← hb']; rw [← reassoc_of% w]; rw [← ht']; rw [assoc]; rw [this])) := by
  subst hb' ht'
  simp [functorMapTgt]

/--
lemma `functorMap_comm` / 引理 `functorMap_comm`

English:
lemma functorMap_comm
  proof: by
  ext ⟨i, t, b, w⟩
  simp [ι_functorMapTgt f τ i t b w _ rfl, ι_functorMapSrc_assoc f τ i t b w _ rfl]

中文:
引理 functorMap_comm
  证明: by
  ext ⟨i, t, b, w⟩
  simp [ι_functorMapTgt f τ i t b w _ rfl, ι_functorMapSrc_assoc f τ i t b w _ rfl]
-/
lemma functorMap_comm :
    functorObjLeft f πX ≫ functorMapTgt f τ =
      functorMapSrc f τ ≫ functorObjLeft f πY := by
  ext ⟨i, t, b, w⟩
  simp [ι_functorMapTgt f τ i t b w _ rfl, ι_functorMapSrc_assoc f τ i t b w _ rfl]

variable [HasPushout (functorObjTop f πX) (functorObjLeft f πX)]
  [HasPushout (functorObjTop f πY) (functorObjLeft f πY)]

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `functorMap` / `functorMap` 的定义

English:
definition functorMap
  signature: : functorObj f πX ⟶ functorObj f πY
  body: pushout.map _ _ _ _ τ.left (functorMapTgt f τ) (functorMapSrc f τ) (by simp)
    (functorMap_comm f τ)

中文:
定义 functorMap
  签名: : functorObj f πX ⟶ functorObj f πY
  定义体: pushout.map _ _ _ _ τ.left (functorMapTgt f τ) (functorMapSrc f τ) (by simp)
    (functorMap_comm f τ)

Depends on / 依赖: functorMapSrc, functorMapTgt, functorMap_comm, pushout, pushout.map
-/
noncomputable def functorMap : functorObj f πX ⟶ functorObj f πY :=
  pushout.map _ _ _ _ τ.left (functorMapTgt f τ) (functorMapSrc f τ) (by simp)
    (functorMap_comm f τ)

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `functorMap_π` / 引理 `functorMap_π`

English:
lemma functorMap_π
  statement: functorMap f τ ≫ πFunctorObj f πY = πFunctorObj f πX ≫ τ.right
  proof: by
  ext ⟨i, t, b, w⟩
  · simp [functorMap]
  · simp [functorMap, ι_functorMapTgt_assoc f τ i t b w _ rfl]

中文:
引理 functorMap_π
  结论: functorMap f τ ≫ πFunctorObj f πY = πFunctorObj f πX ≫ τ.right
  证明: by
  ext ⟨i, t, b, w⟩
  · simp [functorMap]
  · simp [functorMap, ι_functorMapTgt_assoc f τ i t b w _ rfl]

Depends on / 依赖: functorMap
-/
lemma functorMap_π : functorMap f τ ≫ πFunctorObj f πY = πFunctorObj f πX ≫ τ.right := by
  ext ⟨i, t, b, w⟩
  · simp [functorMap]
  · simp [functorMap, ι_functorMapTgt_assoc f τ i t b w _ rfl]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
variable (X) in
@[simp]
/--
lemma `functorMap_id` / 引理 `functorMap_id`

English:
lemma functorMap_id
  statement: functorMap f (𝟙 (Arrow.mk πX)) = 𝟙 _
  proof: by
  ext ⟨i, t, b, w⟩
  · simp [functorMap]
  · simp [functorMap,
      ι_functorMapTgt_assoc f (𝟙 (Arrow.mk πX)) i t b w b (by simp) t (by simp)]

中文:
引理 functorMap_id
  结论: functorMap f (𝟙 (箭头.mk πX)) = 𝟙 _
  证明: by
  ext ⟨i, t, b, w⟩
  · simp [functorMap]
  · simp [functorMap,
      ι_functorMapTgt_assoc f (𝟙 (Arrow.mk πX)) i t b w b (by simp) t (by simp)]

Depends on / 依赖: Arrow.mk, functorMap
-/
lemma functorMap_id : functorMap f (𝟙 (Arrow.mk πX)) = 𝟙 _ := by
  ext ⟨i, t, b, w⟩
  · simp [functorMap]
  · simp [functorMap,
      ι_functorMapTgt_assoc f (𝟙 (Arrow.mk πX)) i t b w b (by simp) t (by simp)]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `ιFunctorObj_naturality` / 引理 `ιFunctorObj_naturality`

English:
lemma ιFunctorObj_naturality
  proof: by
  simp [ιFunctorObj, functorMap]

中文:
引理 ιFunctorObj_naturality
  证明: by
  simp [ιFunctorObj, functorMap]

Depends on / 依赖: functorMap
-/
lemma ιFunctorObj_naturality :
    ιFunctorObj f πX ≫ functorMap f τ = τ.left ≫ ιFunctorObj f πY := by
  simp [ιFunctorObj, functorMap]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `ιFunctorObj_extension` / 引理 `ιFunctorObj_extension`

English:
lemma ιFunctorObj_extension
  statement: {i : I} (t : A i ⟶ X) (b : B i ⟶ S)
  proof: ⟨Sigma.ι (functorObjTgtFamily f πX) (FunctorObjIndex.mk i t b sq.w) ≫
    ρFunctorObj f πX, (FunctorObjIndex.mk i t b _).comm, by simp⟩

中文:
引理 ιFunctorObj_extension
  结论: {i : I} (t : A i ⟶ X) (b : B i ⟶ S)
  证明: ⟨Sigma.ι (functorObjTgtFamily f πX) (FunctorObjIndex.mk i t b sq.w) ≫
    ρFunctorObj f πX, (FunctorObjIndex.mk i t b _).comm, by simp⟩

Depends on / 依赖: FunctorObjIndex, FunctorObjIndex.mk, functorObjTgtFamily, sq.w
-/
lemma ιFunctorObj_extension {i : I} (t : A i ⟶ X) (b : B i ⟶ S)
    (sq : CommSq t (f i) πX b) :
    exists (l : B i ⟶ functorObj f πX), f i ≫ l = t ≫ ιFunctorObj f πX ∧
      l ≫ πFunctorObj f πX = b :=
  ⟨Sigma.ι (functorObjTgtFamily f πX) (FunctorObjIndex.mk i t b sq.w) ≫
    ρFunctorObj f πX, (FunctorObjIndex.mk i t b _).comm, by simp⟩

/--
lemma `ιFunctorObj_extension'` / 引理 `ιFunctorObj_extension'`

English:
lemma ιFunctorObj_extension'
  statement: {X' S' Z' : C} (πX' : X' ⟶ S') (ι' : X' ⟶ Z') (πZ' : Z' ⟶ S')
  proof: by
  obtain ⟨l, hl₁, hl₂⟩ :=
    ιFunctorObj_extension f (πX := πX) (i := i) (t ≫ eX.hom) (b ≫ eS.hom) ⟨by
      rw [assoc]; rw [← ιFunctorObj_πFunctorObj f πX]; rw [← reassoc_of% commι]; rw [← commπ]; rw [reassoc_of% fac']; rw [reassoc_of% fac]⟩
  refine ⟨l ≫ eZ.inv, ?_, ?_⟩
  · rw [reassoc_of% hl₁, ← reassoc_of% commι, eZ.hom_inv_id, comp_id]
  · rw [← cancel_mono eS.hom, assoc, assoc, commπ, eZ.inv_hom_id_assoc, hl₂]

中文:
引理 ιFunctorObj_extension'
  结论: {X' S' Z' : C} (πX' : X' ⟶ S') (ι' : X' ⟶ Z') (πZ' : Z' ⟶ S')
  证明: by
  obtain ⟨l, hl₁, hl₂⟩ :=
    ιFunctorObj_extension f (πX := πX) (i := i) (t ≫ eX.hom) (b ≫ eS.hom) ⟨by
      rw [assoc]; rw [← ιFunctorObj_πFunctorObj f πX]; rw [← reassoc_of% commι]; rw [← commπ]; rw [reassoc_of% fac']; rw [reassoc_of% fac]⟩
  refine ⟨l ≫ eZ.inv, ?_, ?_⟩
  · rw [reassoc_of% hl₁, ← reassoc_of% commι, eZ.hom_inv_id, comp_id]
  · rw [← cancel_mono eS.hom, assoc, assoc, commπ, eZ.inv_hom_id_assoc, hl₂]

Depends on / 依赖: cancel_mono, comp_id, eS.hom, eX.hom, eZ.hom_inv_id, eZ.inv, eZ.inv_hom_id_assoc, hom_inv_id, inv_hom_id_assoc, reassoc_of
-/
lemma ιFunctorObj_extension' {X' S' Z' : C} (πX' : X' ⟶ S') (ι' : X' ⟶ Z') (πZ' : Z' ⟶ S')
    (fac' : ι' ≫ πZ' = πX') (eX : X' ≅ X) (eS : S' ≅ S) (eZ : Z' ≅ functorObj f πX)
    (commι : ι' ≫ eZ.hom = eX.hom ≫ ιFunctorObj f πX)
    (commπ : πZ' ≫ eS.hom = eZ.hom ≫ πFunctorObj f πX)
    {i : I} (t : A i ⟶ X') (b : B i ⟶ S') (fac : t ≫ πX' = f i ≫ b) :
    exists (l : B i ⟶ Z'), f i ≫ l = t ≫ ι' ∧ l ≫ πZ' = b := by
  obtain ⟨l, hl₁, hl₂⟩ :=
    ιFunctorObj_extension f (πX := πX) (i := i) (t ≫ eX.hom) (b ≫ eS.hom) ⟨by
      rw [assoc]; rw [← ιFunctorObj_πFunctorObj f πX]; rw [← reassoc_of% commι]; rw [← commπ]; rw [reassoc_of% fac']; rw [reassoc_of% fac]⟩
  refine ⟨l ≫ eZ.inv, ?_, ?_⟩
  · rw [reassoc_of% hl₁, ← reassoc_of% commι, eZ.hom_inv_id, comp_id]
  · rw [← cancel_mono eS.hom, assoc, assoc, commπ, eZ.inv_hom_id_assoc, hl₂]

end

variable [HasPushouts C]
  [forall {X S : C} (πX : X ⟶ S), HasColimitsOfShape (Discrete (FunctorObjIndex f πX)) C]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The functor `Arrow C ⥤ Arrow C` that is constructed in order to apply the small
object argument to a family of morphisms `f i : A i ⟶ B i`, see the introduction
of the file `Mathlib/CategoryTheory/SmallObject/Construction.lean` -/
@[simps! obj map]
/--
Definition of `functor` / `functor` 的定义

English:
definition functor
  signature: : Arrow C ⥤ Arrow C where
  body: Arrow.mk (πFunctorObj f π.hom)
  map {π₁ π₂} τ := Arrow.homMk (functorMap f τ) τ.right
  map_id g := by
    ext
    · apply functorMap_id
    · dsimp
  map_comp {π₁ π₂ π₃} τ τ' := by
    ext
    · dsimp
      simp only [functorMap, Arrow.comp_left, Arrow.mk_left]
      ext ⟨i, t, b, w⟩
      · simp
      · simp [ι_functorMapTgt_assoc f τ i t b w _ rfl _ rfl,
          ι_functorMapTgt_assoc f (τ ≫ τ') i t b w _ rfl _ rfl,
          ι_functorMapTgt_assoc f τ' i (t ≫ τ.left) (b ≫ τ.right)
            (by simp [reassoc_of% w]) (b ≫ τ.right ≫ τ'.right) (by simp)
            (t ≫ (τ ≫ τ').left) (by simp)]
    · dsimp

中文:
定义 functor
  签名: : 箭头 C ⥤ 箭头 C where
  定义体: Arrow.mk (πFunctorObj f π.hom)
  map {π₁ π₂} τ := Arrow.homMk (functorMap f τ) τ.right
  map_id g := by
    ext
    · apply functorMap_id
    · dsimp
  map_comp {π₁ π₂ π₃} τ τ' := by
    ext
    · dsimp
      simp only [functorMap, Arrow.comp_left, Arrow.mk_left]
      ext ⟨i, t, b, w⟩
      · simp
      · simp [ι_functorMapTgt_assoc f τ i t b w _ rfl _ rfl,
          ι_functorMapTgt_assoc f (τ ≫ τ') i t b w _ rfl _ rfl,
          ι_functorMapTgt_assoc f τ' i (t ≫ τ.left) (b ≫ τ.right)
            (by simp [reassoc_of% w]) (b ≫ τ.right ≫ τ'.right) (by simp)
            (t ≫ (τ ≫ τ').left) (by simp)]
    · dsimp

Depends on / 依赖: Arrow.mk
-/
noncomputable def functor : Arrow C ⥤ Arrow C where
  obj π := Arrow.mk (πFunctorObj f π.hom)
  map {π₁ π₂} τ := Arrow.homMk (functorMap f τ) τ.right
  map_id g := by
    ext
    · apply functorMap_id
    · dsimp
  map_comp {π₁ π₂ π₃} τ τ' := by
    ext
    · dsimp
      simp only [functorMap, Arrow.comp_left, Arrow.mk_left]
      ext ⟨i, t, b, w⟩
      · simp
      · simp [ι_functorMapTgt_assoc f τ i t b w _ rfl _ rfl,
          ι_functorMapTgt_assoc f (τ ≫ τ') i t b w _ rfl _ rfl,
          ι_functorMapTgt_assoc f τ' i (t ≫ τ.left) (b ≫ τ.right)
            (by simp [reassoc_of% w]) (b ≫ τ.right ≫ τ'.right) (by simp)
            (t ≫ (τ ≫ τ').left) (by simp)]
    · dsimp

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The canonical natural transformation `𝟭 (Arrow C) ⟶ functor f`. -/
@[simps app]
/--
Definition of `ε` / `ε` 的定义

English:
definition ε
  signature: : 𝟭 (Arrow C) ⟶ functor f where
  body: Arrow.homMk (ιFunctorObj f π.hom) (𝟙 _)

中文:
定义 ε
  签名: : 𝟭 (箭头 C) ⟶ functor f where
  定义体: Arrow.homMk (ιFunctorObj f π.hom) (𝟙 _)

Depends on / 依赖: Arrow.homMk
-/
noncomputable def ε : 𝟭 (Arrow C) ⟶ functor f where
  app π := Arrow.homMk (ιFunctorObj f π.hom) (𝟙 _)

end

end SmallObject

end CategoryTheory
