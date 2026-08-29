/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products
public import Mathlib.CategoryTheory.Sites.Coverage
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.Hypercover.Zero

/-!
# 1-hypercovers

Given a Grothendieck topology `J` on a category `C`, we define the type of
`1`-hypercovers of an object `S : C`. They consist of a covering family
of morphisms `X i ⟶ S` indexed by a type `I₀` and, for each tuple `(i₁, i₂)`
of elements of `I₀`, a "covering `Y j` of the fibre product of `X i₁` and
`X i₂` over `S`", a condition which is phrased here without assuming that
the fibre product actually exists.

The definition `OneHypercover.isLimitMultifork` shows that if `E` is a
`1`-hypercover of `S`, and `F` is a sheaf, then `F.obj (op S)`
identifies to the multiequalizer of suitable maps
`F.obj (op (E.X i)) ⟶ F.obj (op (E.Y j))`.

-/

@[expose] public section

universe w'' w' w v u

namespace CategoryTheory

open Category Limits

variable {C : Type u} [Category.{v} C] {A : Type*} [Category* A]

/--
Definition of `PreOneHypercover` / `PreOneHypercover` 的定义

English:
structure PreOneHypercover
  parameters: (S : C)
  extends: PreZeroHypercover.{w} S
  axioms and operations (5):
    - I₁((i₁ i₂ : I₀)) : Type w
    - Y(⦃i₁ i₂) : I₀⦄ (j : I₁ i₁ i₂) : C
    - p₁(⦃i₁ i₂) : I₀⦄ (j : I₁ i₁ i₂) : Y j ⟶ X i₁
    - p₂(⦃i₁ i₂) : I₀⦄ (j : I₁ i₁ i₂) : Y j ⟶ X i₂
    - w(⦃i₁ i₂) : I₀⦄ (j : I₁ i₁ i₂) : p₁ j ≫ f i₁ = p₂ j ≫ f i₂

中文:
结构 PreOneHypercover
  参数: (S : C)
  继承: PreZeroHypercover.{w} S
  公理与运算 (5 个):
    - I₁((i₁ i₂ : I₀)) : Type w
    - Y(⦃i₁ i₂) : I₀⦄ (j : I₁ i₁ i₂) : C
    - p₁(⦃i₁ i₂) : I₀⦄ (j : I₁ i₁ i₂) : Y j ⟶ X i₁
    - p₂(⦃i₁ i₂) : I₀⦄ (j : I₁ i₁ i₂) : Y j ⟶ X i₂
    - w(⦃i₁ i₂) : I₀⦄ (j : I₁ i₁ i₂) : p₁ j ≫ f i₁ = p₂ j ≫ f i₂
-/
structure PreOneHypercover (S : C) extends PreZeroHypercover.{w} S where
  /-- the index type of the coverings of the fibre products -/
  I₁ (i₁ i₂ : I₀) : Type w
  /-- the objects in the coverings of the fibre products -/
  Y ⦃i₁ i₂ : I₀⦄ (j : I₁ i₁ i₂) : C
  /-- the first projection `Y j ⟶ X i₁` -/
  p₁ ⦃i₁ i₂ : I₀⦄ (j : I₁ i₁ i₂) : Y j ⟶ X i₁
  /-- the second projection `Y j ⟶ X i₂` -/
  p₂ ⦃i₁ i₂ : I₀⦄ (j : I₁ i₁ i₂) : Y j ⟶ X i₂
  w ⦃i₁ i₂ : I₀⦄ (j : I₁ i₁ i₂) : p₁ j ≫ f i₁ = p₂ j ≫ f i₂

namespace PreOneHypercover

variable {S : C} (E : PreOneHypercover.{w} S)

/-- Given an object `W` equipped with morphisms `p₁ : W ⟶ E.X i₁`, `p₂ : W ⟶ E.X i₂`,
this is the sieve of `W` which consists of morphisms `g : Z ⟶ W` such that there exists `j`
and `h : Z ⟶ E.Y j` such that `g ≫ p₁ = h ≫ E.p₁ j` and `g ≫ p₂ = h ≫ E.p₂ j`.
See lemmas `sieve₁_eq_pullback_sieve₁'` and `sieve₁'_eq_sieve₁` for equational lemmas
regarding this sieve. -/
@[simps]
/--
Definition of `sieve₁` / `sieve₁` 的定义

English:
definition sieve₁
  signature: {i₁ i₂ : E.I₀} {W : C} (p₁ : W ⟶ E.X i₁) (p₂ : W ⟶ E.X i₂)
  body: exists (j : E.I₁ i₁ i₂) (h : Z ⟶ E.Y j), g ≫ p₁ = h ≫ E.p₁ j ∧ g ≫ p₂ = h ≫ E.p₂ j
  downward_closed := by
    rintro Z Z' g ⟨j, h, fac₁, fac₂⟩ φ
    exact ⟨j, φ ≫ h, by simpa using φ ≫= fac₁, by simpa using φ ≫= fac₂⟩

中文:
定义 sieve₁
  签名: {i₁ i₂ : E.I₀} {W : C} (p₁ : W ⟶ E.X i₁) (p₂ : W ⟶ E.X i₂)
  定义体: exists (j : E.I₁ i₁ i₂) (h : Z ⟶ E.Y j), g ≫ p₁ = h ≫ E.p₁ j ∧ g ≫ p₂ = h ≫ E.p₂ j
  downward_closed := by
    rintro Z Z' g ⟨j, h, fac₁, fac₂⟩ φ
    exact ⟨j, φ ≫ h, by simpa using φ ≫= fac₁, by simpa using φ ≫= fac₂⟩
-/
def sieve₁ {i₁ i₂ : E.I₀} {W : C} (p₁ : W ⟶ E.X i₁) (p₂ : W ⟶ E.X i₂) : Sieve W where
  arrows Z g := exists (j : E.I₁ i₁ i₂) (h : Z ⟶ E.Y j), g ≫ p₁ = h ≫ E.p₁ j ∧ g ≫ p₂ = h ≫ E.p₂ j
  downward_closed := by
    rintro Z Z' g ⟨j, h, fac₁, fac₂⟩ φ
    exact ⟨j, φ ≫ h, by simpa using φ ≫= fac₁, by simpa using φ ≫= fac₂⟩

/--
lemma `pullback_sieve₁` / 引理 `pullback_sieve₁`

English:
lemma pullback_sieve₁
  statement: {i₁ i₂ : E.I₀} {W : C} (p₁ : W ⟶ E.X i₁) (p₂ : W ⟶ E.X i₂)
  proof: by
  refine le_antisymm ?_ ?_ <;>
  · intro Z g ⟨k, u, hu₁, hu₂⟩
    cat_disch

中文:
引理 pullback_sieve₁
  结论: {i₁ i₂ : E.I₀} {W : C} (p₁ : W ⟶ E.X i₁) (p₂ : W ⟶ E.X i₂)
  证明: by
  refine le_antisymm ?_ ?_ <;>
  · intro Z g ⟨k, u, hu₁, hu₂⟩
    cat_disch

Depends on / 依赖: cat_disch, le_antisymm
-/
lemma pullback_sieve₁ {i₁ i₂ : E.I₀} {W : C} (p₁ : W ⟶ E.X i₁) (p₂ : W ⟶ E.X i₂)
    {T : C} (f : T ⟶ W) :
    Sieve.pullback f (E.sieve₁ p₁ p₂) = E.sieve₁ (f ≫ p₁) (f ≫ p₂) := by
  refine le_antisymm ?_ ?_ <;>
  · intro Z g ⟨k, u, hu₁, hu₂⟩
    cat_disch

section

variable {i₁ i₂ : E.I₀} [HasPullback (E.f i₁) (E.f i₂)]

/--
Definition of `toPullback` / `toPullback` 的定义

English:
abbreviation toPullback
  signature: (j : E.I₁ i₁ i₂)
  body: pullback.lift (E.p₁ j) (E.p₂ j) (E.w j)

@[reassoc (attr := simp)]

中文:
缩写 toPullback
  签名: (j : E.I₁ i₁ i₂)
  定义体: pullback.lift (E.p₁ j) (E.p₂ j) (E.w j)

@[reassoc (attr := simp)]

Depends on / 依赖: pullback, pullback.lift
-/
noncomputable abbrev toPullback (j : E.I₁ i₁ i₂) : E.Y j ⟶ pullback (E.f i₁) (E.f i₂) :=
  pullback.lift (E.p₁ j) (E.p₂ j) (E.w j)

@[reassoc (attr := simp)]
/--
lemma `toPullback_fst` / 引理 `toPullback_fst`

English:
lemma toPullback_fst
  given: (k : E.I₁ i₁ i₂)
  statement: E.toPullback k ≫ pullback.fst _ _ = E.p₁ k
  proof: by
  rw [pullback.lift_fst]

@[reassoc (attr := simp)]

中文:
引理 toPullback_fst
  条件: (k : E.I₁ i₁ i₂)
  结论: E.toPullback k ≫ pullback.fst _ _ = E.p₁ k
  证明: by
  rw [pullback.lift_fst]

@[reassoc (attr := simp)]

Depends on / 依赖: lift_fst, pullback, pullback.lift_fst
-/
lemma toPullback_fst (k : E.I₁ i₁ i₂) : E.toPullback k ≫ pullback.fst _ _ = E.p₁ k := by
  rw [pullback.lift_fst]

@[reassoc (attr := simp)]
/--
lemma `toPullback_snd` / 引理 `toPullback_snd`

English:
lemma toPullback_snd
  given: (k : E.I₁ i₁ i₂)
  statement: E.toPullback k ≫ pullback.snd _ _ = E.p₂ k
  proof: by
  rw [pullback.lift_snd]

中文:
引理 toPullback_snd
  条件: (k : E.I₁ i₁ i₂)
  结论: E.toPullback k ≫ pullback.snd _ _ = E.p₂ k
  证明: by
  rw [pullback.lift_snd]

Depends on / 依赖: lift_snd, pullback, pullback.lift_snd
-/
lemma toPullback_snd (k : E.I₁ i₁ i₂) : E.toPullback k ≫ pullback.snd _ _ = E.p₂ k := by
  rw [pullback.lift_snd]

variable (i₁ i₂) in
/--
Definition of `sieve₁'` / `sieve₁'` 的定义

English:
definition sieve₁'
  signature: : Sieve (pullback (E.f i₁) (E.f i₂))
  body: Sieve.ofArrows _ (fun (j : E.I₁ i₁ i₂) => E.toPullback j)

中文:
定义 sieve₁'
  签名: : Sieve (pullback (E.f i₁) (E.f i₂))
  定义体: Sieve.ofArrows _ (fun (j : E.I₁ i₁ i₂) => E.toPullback j)
-/
noncomputable def sieve₁' : Sieve (pullback (E.f i₁) (E.f i₂)) :=
  Sieve.ofArrows _ (fun (j : E.I₁ i₁ i₂) => E.toPullback j)

set_option backward.isDefEq.respectTransparency false in
/--
lemma `sieve₁_eq_pullback_sieve₁'` / 引理 `sieve₁_eq_pullback_sieve₁'`

English:
lemma sieve₁_eq_pullback_sieve₁'
  statement: {W : C} (p₁ : W ⟶ E.X i₁) (p₂ : W ⟶ E.X i₂)
  proof: by
  ext Z g
  constructor
  · rintro ⟨j, h, fac₁, fac₂⟩
    exact ⟨_, h, _, ⟨j⟩, by cat_disch⟩
  · rintro ⟨_, h, w, ⟨j⟩, fac⟩
    exact ⟨j, h, by simpa using fac.symm =≫ pullback.fst _ _,
      by simpa using fac.symm =≫ pullback.snd _ _⟩

中文:
引理 sieve₁_eq_pullback_sieve₁'
  结论: {W : C} (p₁ : W ⟶ E.X i₁) (p₂ : W ⟶ E.X i₂)
  证明: by
  ext Z g
  constructor
  · rintro ⟨j, h, fac₁, fac₂⟩
    exact ⟨_, h, _, ⟨j⟩, by cat_disch⟩
  · rintro ⟨_, h, w, ⟨j⟩, fac⟩
    exact ⟨j, h, by simpa using fac.symm =≫ pullback.fst _ _,
      by simpa using fac.symm =≫ pullback.snd _ _⟩

Depends on / 依赖: cat_disch, fac.symm, pullback, pullback.fst, pullback.snd
-/
lemma sieve₁_eq_pullback_sieve₁' {W : C} (p₁ : W ⟶ E.X i₁) (p₂ : W ⟶ E.X i₂)
    (w : p₁ ≫ E.f i₁ = p₂ ≫ E.f i₂) :
    E.sieve₁ p₁ p₂ = (E.sieve₁' i₁ i₂).pullback (pullback.lift _ _ w) := by
  ext Z g
  constructor
  · rintro ⟨j, h, fac₁, fac₂⟩
    exact ⟨_, h, _, ⟨j⟩, by cat_disch⟩
  · rintro ⟨_, h, w, ⟨j⟩, fac⟩
    exact ⟨j, h, by simpa using fac.symm =≫ pullback.fst _ _,
      by simpa using fac.symm =≫ pullback.snd _ _⟩

variable (i₁ i₂) in
/--
lemma `sieve₁'_eq_sieve₁` / 引理 `sieve₁'_eq_sieve₁`

English:
lemma sieve₁'_eq_sieve₁
  statement: E.sieve₁' i₁ i₂ = E.sieve₁ (pullback.fst _ _) (pullback.snd _ _)
  proof: by
  rw [← Sieve.pullback_id (S := E.sieve₁' i₁ i₂)]; rw [sieve₁_eq_pullback_sieve₁' _ _ _ pullback.condition]
  congr
  cat_disch

中文:
引理 sieve₁'_eq_sieve₁
  结论: E.sieve₁' i₁ i₂ = E.sieve₁ (pullback.fst _ _) (pullback.snd _ _)
  证明: by
  rw [← Sieve.pullback_id (S := E.sieve₁' i₁ i₂)]; rw [sieve₁_eq_pullback_sieve₁' _ _ _ pullback.condition]
  congr
  cat_disch
-/
lemma sieve₁'_eq_sieve₁ : E.sieve₁' i₁ i₂ = E.sieve₁ (pullback.fst _ _) (pullback.snd _ _) := by
  rw [← Sieve.pullback_id (S := E.sieve₁' i₁ i₂)]; rw [sieve₁_eq_pullback_sieve₁' _ _ _ pullback.condition]
  congr
  cat_disch

end

/--
Definition of `I₁'` / `I₁'` 的定义

English:
abbreviation I₁'
  signature: : Type w
  body: Sigma (fun (i : E.I₀ × E.I₀) => E.I₁ i.1 i.2)

中文:
缩写 I₁'
  签名: : Type w
  定义体: Sigma (fun (i : E.I₀ × E.I₀) => E.I₁ i.1 i.2)
-/
abbrev I₁' : Type w := Sigma (fun (i : E.I₀ × E.I₀) => E.I₁ i.1 i.2)

/--
Definition of `Y'` / `Y'` 的定义

English:
definition Y'
  signature: (i : E.I₁')
  body: E.Y i.2

@[simp]

中文:
定义 Y'
  签名: (i : E.I₁')
  定义体: E.Y i.2

@[simp]
-/
def Y' (i : E.I₁') : C := E.Y i.2

@[simp]
/--
lemma `Y'_apply` / 引理 `Y'_apply`

English:
lemma Y'_apply
  given: (i : E.I₁')
  statement: E.Y' i = E.Y i.2
  proof: rfl

中文:
引理 Y'_apply
  条件: (i : E.I₁')
  结论: E.Y' i = E.Y i.2
  证明: rfl
-/
lemma Y'_apply (i : E.I₁') : E.Y' i = E.Y i.2 := rfl

/-- The shape of the multiforks attached to `E : PreOneHypercover S`. -/
@[simps]
/--
Definition of `multicospanShape` / `multicospanShape` 的定义

English:
definition multicospanShape
  signature: : MulticospanShape where
  body: E.I₀
  R := E.I₁'
  fst j := j.1.1
  snd j := j.1.2

中文:
定义 multicospanShape
  签名: : MulticospanShape where
  定义体: E.I₀
  R := E.I₁'
  fst j := j.1.1
  snd j := j.1.2
-/
def multicospanShape : MulticospanShape where
  L := E.I₀
  R := E.I₁'
  fst j := j.1.1
  snd j := j.1.2

/-- The diagram of the multifork attached to a presheaf
`F : Cᵒᵖ ⥤ A`, `S : C` and `E : PreOneHypercover S`. -/
@[simps]
/--
Definition of `multicospanIndex` / `multicospanIndex` 的定义

English:
definition multicospanIndex
  signature: (F : Cᵒᵖ ⥤ A)
  body: F.obj (Opposite.op (E.X i))
  right j := F.obj (Opposite.op (E.Y j.2))
  fst j := F.map ((E.p₁ j.2).op)
  snd j := F.map ((E.p₂ j.2).op)

中文:
定义 multicospanIndex
  签名: (F : Cᵒᵖ ⥤ A)
  定义体: F.obj (Opposite.op (E.X i))
  right j := F.obj (Opposite.op (E.Y j.2))
  fst j := F.map ((E.p₁ j.2).op)
  snd j := F.map ((E.p₂ j.2).op)

Depends on / 依赖: F.obj, Opposite, Opposite.op
-/
def multicospanIndex (F : Cᵒᵖ ⥤ A) : MulticospanIndex E.multicospanShape A where
  left i := F.obj (Opposite.op (E.X i))
  right j := F.obj (Opposite.op (E.Y j.2))
  fst j := F.map ((E.p₁ j.2).op)
  snd j := F.map ((E.p₂ j.2).op)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `multifork` / `multifork` 的定义

English:
definition multifork
  signature: (F : Cᵒᵖ ⥤ A)
  body: Multifork.ofι _ (F.obj (Opposite.op S)) (fun i₀ => F.map (E.f i₀).op) (by
    rintro ⟨⟨i₁, i₂⟩, (j : E.I₁ i₁ i₂)⟩
    dsimp
    simp only [← F.map_comp, ← op_comp, E.w])

@[simp]

中文:
定义 multifork
  签名: (F : Cᵒᵖ ⥤ A)
  定义体: Multifork.ofι _ (F.obj (Opposite.op S)) (fun i₀ => F.map (E.f i₀).op) (by
    rintro ⟨⟨i₁, i₂⟩, (j : E.I₁ i₁ i₂)⟩
    dsimp
    simp only [← F.map_comp, ← op_comp, E.w])

@[simp]

Depends on / 依赖: F.map, F.map_comp, F.obj, Multifork, Multifork.of, Opposite, Opposite.op, map_comp, op_comp
-/
def multifork (F : Cᵒᵖ ⥤ A) :
    Multifork (E.multicospanIndex F) :=
  Multifork.ofι _ (F.obj (Opposite.op S)) (fun i₀ => F.map (E.f i₀).op) (by
    rintro ⟨⟨i₁, i₂⟩, (j : E.I₁ i₁ i₂)⟩
    dsimp
    simp only [← F.map_comp, ← op_comp, E.w])

@[simp]
/--
lemma `multifork_ι` / 引理 `multifork_ι`

English:
lemma multifork_ι
  given: (F : Cᵒᵖ ⥤ A) (i : E.I₀)
  statement: (E.multifork F).ι i = F.map (E.f i).op
  proof: rfl

中文:
引理 multifork_ι
  条件: (F : Cᵒᵖ ⥤ A) (i : E.I₀)
  结论: (E.multifork F).ι i = F.map (E.f i).op
  证明: rfl
-/
lemma multifork_ι (F : Cᵒᵖ ⥤ A) (i : E.I₀) : (E.multifork F).ι i = F.map (E.f i).op := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The fork associated to a pre-`0`-hypercover induced by taking the coproduct of the
components. -/
@[simps! pt]
/--
Definition of `forkOfIsColimit` / `forkOfIsColimit` 的定义

English:
definition forkOfIsColimit
  signature: {c : Cofan E.X} (hc : IsColimit c) {d : Cofan E.Y'} (hd : IsColimit d)
  body: .ofι (F.map (Cofan.IsColimit.desc hc E.f).op) by
    simp_rw [← Functor.map_comp, ← op_comp]
    congr 2
    exact Cofan.IsColimit.hom_ext hd _ _ (by simp [E.w])

中文:
定义 forkOfIsColimit
  签名: {c : Cofan E.X} (hc : IsColimit c) {d : Cofan E.Y'} (hd : IsColimit d)
  定义体: .ofι (F.map (Cofan.IsColimit.desc hc E.f).op) by
    simp_rw [← Functor.map_comp, ← op_comp]
    congr 2
    exact Cofan.IsColimit.hom_ext hd _ _ (by simp [E.w])

Depends on / 依赖: Cofan.IsColimit.desc, Cofan.IsColimit.hom_ext, F.map, Functor, Functor.map_comp, IsColimit, hom_ext, map_comp, op_comp, simp_rw
-/
def forkOfIsColimit {c : Cofan E.X} (hc : IsColimit c) {d : Cofan E.Y'} (hd : IsColimit d)
    (F : Cᵒᵖ ⥤ A) :
    Fork (F.map (Cofan.IsColimit.desc hd fun _ => E.p₁ _ ≫ c.inj _).op)
      (F.map (Cofan.IsColimit.desc hd fun _ => E.p₂ _ ≫ c.inj _).op) :=
.ofι (F.map (Cofan.IsColimit.desc hc E.f).op) by
    simp_rw [← Functor.map_comp, ← op_comp]
    congr 2
    exact Cofan.IsColimit.hom_ext hd _ _ (by simp [E.w])

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/--
lemma `forkOfIsColimit_ι_map_inj` / 引理 `forkOfIsColimit_ι_map_inj`

English:
lemma forkOfIsColimit_ι_map_inj
  statement: {c : Cofan E.X} (hc : IsColimit c) {d : Cofan E.Y'}
  proof: by
  simp [forkOfIsColimit, ← Functor.map_comp, ← op_comp]

中文:
引理 forkOfIsColimit_ι_map_inj
  结论: {c : Cofan E.X} (hc : IsColimit c) {d : Cofan E.Y'}
  证明: by
  simp [forkOfIsColimit, ← Functor.map_comp, ← op_comp]

Depends on / 依赖: Functor, Functor.map_comp, forkOfIsColimit, map_comp, op_comp
-/
lemma forkOfIsColimit_ι_map_inj {c : Cofan E.X} (hc : IsColimit c) {d : Cofan E.Y'}
    (hd : IsColimit d) (F : Cᵒᵖ ⥤ A) (i : E.I₀) :
    (E.forkOfIsColimit hc hd F).ι ≫ F.map (c.inj i).op = F.map (E.f i).op := by
  simp [forkOfIsColimit, ← Functor.map_comp, ← op_comp]

open Opposite

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `isLimitMultiforkEquivIsLimitFork` / `isLimitMultiforkEquivIsLimitFork` 的定义

English:
definition isLimitMultiforkEquivIsLimitFork
  body: by
  letI c' : Fan (E.multicospanIndex F).left := Fan.mk _ fun i => F.map (c.inj i).op
  letI hc' : IsLimit c' := isLimitFanMkObjOfIsLimit _ _ (fun i : E.I₀ => _) (Cofan.IsColimit.op hc)
  letI d' : Fan (E.multicospanIndex F).right := Fan.mk _ fun i => F.map (d.inj i).op
  letI hd' : IsLimit d' := i

中文:
定义 isLimitMultiforkEquivIsLimitFork
  定义体: by
  letI c' : Fan (E.multicospanIndex F).left := Fan.mk _ fun i => F.map (c.inj i).op
  letI hc' : IsLimit c' := isLimitFanMkObjOfIsLimit _ _ (fun i : E.I₀ => _) (Cofan.IsColimit.op hc)
  letI d' : Fan (E.multicospanIndex F).right := Fan.mk _ fun i => F.map (d.inj i).op
  letI hd' : IsLimit d' := i

Depends on / 依赖: Cofan.IsColimit.op, E.multicospanIndex, F.map, Fan.mk, Fork.isLimitEquivOfIs, IsColimit, IsLimit, IsLimit.ofConeEquiv, c.inj, d.inj, isLimitEquivOfIs, isLimitFanMkObjOfIsLimit, multicospanIndex, multiforkEquivPiForkOfIsLimit, ofConeEquiv, symm.trans
-/
noncomputable def isLimitMultiforkEquivIsLimitFork
    {c : Cofan E.X} (hc : IsColimit c) {d : Cofan E.Y'} (hd : IsColimit d) (F : Cᵒᵖ ⥤ A)
    [PreservesLimit (Discrete.functor fun i => Opposite.op (E.X i)) F]
    [PreservesLimit (Discrete.functor fun i => Opposite.op (E.Y' i)) F] :
    IsLimit (E.multifork F) ≃ IsLimit (E.forkOfIsColimit hc hd F) := by
  letI c' : Fan (E.multicospanIndex F).left := Fan.mk _ fun i => F.map (c.inj i).op
  letI hc' : IsLimit c' := isLimitFanMkObjOfIsLimit _ _ (fun i : E.I₀ => _) (Cofan.IsColimit.op hc)
  letI d' : Fan (E.multicospanIndex F).right := Fan.mk _ fun i => F.map (d.inj i).op
  letI hd' : IsLimit d' := isLimitFanMkObjOfIsLimit _ _ (fun i : E.I₁' => _) (Cofan.IsColimit.op hd)
  refine (IsLimit.ofConeEquiv <|
    (E.multicospanIndex F).multiforkEquivPiForkOfIsLimit hc' hd').symm.trans ?_
  refine Fork.isLimitEquivOfIsos _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_
  · refine Fan.IsLimit.hom_ext hd' _ _ fun i => ?_
    simp only [multicospanShape_L, multicospanIndex_right, multicospanShape_R, Iso.refl_hom,
      Y'_apply, id_comp, comp_id]
    rw [MulticospanIndex.fstPiMapOfIsLimit_proj]
    simp [c', d', ← F.map_comp, ← op_comp]
  · refine Fan.IsLimit.hom_ext hd' _ _ fun i => ?_
    simp only [multicospanShape_L, multicospanIndex_right, multicospanShape_R, Iso.refl_hom,
      Y'_apply, id_comp, comp_id]
    rw [MulticospanIndex.sndPiMapOfIsLimit_proj]
    simp [c', d', ← F.map_comp, ← op_comp]
  · refine Fan.IsLimit.hom_ext hc' _ _ fun i => ?_
    simp
    simp [c']

set_option backward.isDefEq.respectTransparency false in
/-- The single object pre-`1`-hypercover obtained from taking coproducts of the components. -/
@[simps toPreZeroHypercover Y]
/--
Definition of `sigmaOfIsColimit` / `sigmaOfIsColimit` 的定义

English:
definition sigmaOfIsColimit
  signature: {c : Cofan E.X} (hc : IsColimit c) {d : Cofan E.Y'} (hd : IsColimit d)
  body: E.toPreZeroHypercover.sigmaOfIsColimit hc
  I₁ _ _ := PUnit
  Y _ _ _ := d.pt
  p₁ _ _ _ := Cofan.IsColimit.desc hd fun i => E.p₁ _ ≫ c.inj _
  p₂ _ _ _ := Cofan.IsColimit.desc hd fun i => E.p₂ _ ≫ c.inj _
  w _ _ _ := Cofan.IsColimit.hom_ext hd _ _ (by simp [E.w])

中文:
定义 sigmaOfIsColimit
  签名: {c : Cofan E.X} (hc : IsColimit c) {d : Cofan E.Y'} (hd : IsColimit d)
  定义体: E.toPreZeroHypercover.sigmaOfIsColimit hc
  I₁ _ _ := PUnit
  Y _ _ _ := d.pt
  p₁ _ _ _ := Cofan.IsColimit.desc hd fun i => E.p₁ _ ≫ c.inj _
  p₂ _ _ _ := Cofan.IsColimit.desc hd fun i => E.p₂ _ ≫ c.inj _
  w _ _ _ := Cofan.IsColimit.hom_ext hd _ _ (by simp [E.w])

Depends on / 依赖: E.toPreZeroHypercover.sigmaOfIsColimit, sigmaOfIsColimit, toPreZeroHypercover
-/
def sigmaOfIsColimit {c : Cofan E.X} (hc : IsColimit c) {d : Cofan E.Y'} (hd : IsColimit d) :
    PreOneHypercover.{w} S where
  __ := E.toPreZeroHypercover.sigmaOfIsColimit hc
  I₁ _ _ := PUnit
  Y _ _ _ := d.pt
  p₁ _ _ _ := Cofan.IsColimit.desc hd fun i => E.p₁ _ ≫ c.inj _
  p₂ _ _ _ := Cofan.IsColimit.desc hd fun i => E.p₂ _ ≫ c.inj _
  w _ _ _ := Cofan.IsColimit.hom_ext hd _ _ (by simp [E.w])

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `p₁_sigmaOfIsColimit` / 引理 `p₁_sigmaOfIsColimit`

English:
lemma p₁_sigmaOfIsColimit
  statement: {c : Cofan E.X} (hc : IsColimit c) {d : Cofan E.Y'} (hd : IsColimit d)
  proof: by
  simp [sigmaOfIsColimit]

中文:
引理 p₁_sigmaOfIsColimit
  结论: {c : Cofan E.X} (hc : IsColimit c) {d : Cofan E.Y'} (hd : IsColimit d)
  证明: by
  simp [sigmaOfIsColimit]

Depends on / 依赖: sigmaOfIsColimit
-/
lemma p₁_sigmaOfIsColimit {c : Cofan E.X} (hc : IsColimit c) {d : Cofan E.Y'} (hd : IsColimit d)
    (i : E.I₁') {a b : PUnit} (r : (E.sigmaOfIsColimit hc hd).I₁ a b) :
    d.inj i ≫ (E.sigmaOfIsColimit hc hd).p₁ r = E.p₁ _ ≫ c.inj _ := by
  simp [sigmaOfIsColimit]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `p₂_sigmaOfIsColimit` / 引理 `p₂_sigmaOfIsColimit`

English:
lemma p₂_sigmaOfIsColimit
  statement: {c : Cofan E.X} (hc : IsColimit c) {d : Cofan E.Y'} (hd : IsColimit d)
  proof: by
  simp [sigmaOfIsColimit]

中文:
引理 p₂_sigmaOfIsColimit
  结论: {c : Cofan E.X} (hc : IsColimit c) {d : Cofan E.Y'} (hd : IsColimit d)
  证明: by
  simp [sigmaOfIsColimit]

Depends on / 依赖: sigmaOfIsColimit
-/
lemma p₂_sigmaOfIsColimit {c : Cofan E.X} (hc : IsColimit c) {d : Cofan E.Y'} (hd : IsColimit d)
    (i : E.I₁') {a b : PUnit} (r : (E.sigmaOfIsColimit hc hd).I₁ a b) :
    d.inj i ≫ (E.sigmaOfIsColimit hc hd).p₂ r = E.p₂ _ ≫ c.inj _ := by
  simp [sigmaOfIsColimit]

instance {c : Cofan E.X} (hc : IsColimit c) {d : Cofan E.Y'} (hd : IsColimit d) :
    Unique (E.sigmaOfIsColimit hc hd).multicospanShape.L :=
inferInstanceAs Unique PUnit

instance {c : Cofan E.X} (hc : IsColimit c) {d : Cofan E.Y'} (hd : IsColimit d) :
    Unique (E.sigmaOfIsColimit hc hd).multicospanShape.R where
  default := ⟨(⟨⟩, ⟨⟩), ⟨⟩⟩
  uniq _ := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- If `E` is a pre-`1`-hypercover and `F` a presheaf, the induced equalizer of
the single object covering obtained from `E` by taking coproducts is limiting
if and only if the induced multiequalizer of `E` is limiting. -/
noncomputable
/--
Definition of `isLimitSigmaOfIsColimitEquiv` / `isLimitSigmaOfIsColimitEquiv` 的定义

English:
definition isLimitSigmaOfIsColimitEquiv
  signature: {c : Cofan E.X} (hc : IsColimit c) {d : Cofan E.Y'}
  body: by
  refine (Multifork.isLimitEquivOfIsos _ _ ?_ ?_ ?_ ?_ ?_ ?_).trans
    (IsLimit.ofConeEquiv <| (MulticospanIndex.multiforkOfParallelHomsEquivFork
      (E.sigmaOfIsColimit hc hd).multicospanShape _ _).symm) |>.trans
      (E.isLimitMultiforkEquivIsLimitFork hc hd F).symm
  · exact .refl _
  · ex

中文:
定义 isLimitSigmaOfIsColimitEquiv
  签名: {c : Cofan E.X} (hc : IsColimit c) {d : Cofan E.Y'}
  定义体: by
  refine (Multifork.isLimitEquivOfIsos _ _ ?_ ?_ ?_ ?_ ?_ ?_).trans
    (IsLimit.ofConeEquiv <| (MulticospanIndex.multiforkOfParallelHomsEquivFork
      (E.sigmaOfIsColimit hc hd).multicospanShape _ _).symm) |>.trans
      (E.isLimitMultiforkEquivIsLimitFork hc hd F).symm
  · exact .refl _
  · ex

Depends on / 依赖: E.isLimitMultiforkEquivIsLimitFork, E.sigmaOfIsColimit, IsLimit, IsLimit.ofConeEquiv, MulticospanIndex, MulticospanIndex.multiforkOfParallelHomsEquivFork, Multifork, Multifork.isLimitEquivOfIsos, all_goals, cat_disch, isLimitEquivOfIsos, isLimitMultiforkEquivIsLimitFork, multicospanShape, multiforkOfParallelHomsEquivFork, ofConeEquiv, sigmaOfIsColimit
-/
def isLimitSigmaOfIsColimitEquiv {c : Cofan E.X} (hc : IsColimit c) {d : Cofan E.Y'}
    (hd : IsColimit d) (F : Cᵒᵖ ⥤ A)
    [PreservesLimit (Discrete.functor fun i => Opposite.op (E.X i)) F]
    [PreservesLimit (Discrete.functor fun i => Opposite.op (E.Y' i)) F] :
    IsLimit ((E.sigmaOfIsColimit hc hd).multifork F) ≃ IsLimit (E.multifork F) := by
  refine (Multifork.isLimitEquivOfIsos _ _ ?_ ?_ ?_ ?_ ?_ ?_).trans
    (IsLimit.ofConeEquiv <| (MulticospanIndex.multiforkOfParallelHomsEquivFork
      (E.sigmaOfIsColimit hc hd).multicospanShape _ _).symm) |>.trans
      (E.isLimitMultiforkEquivIsLimitFork hc hd F).symm
  · exact .refl _
  · exact fun _ => .refl _
  · exact fun _ => .refl _
  all_goals cat_disch

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The trivial pre-`1`-hypercover of `S` with a single component `S`. -/
@[simps toPreZeroHypercover I₁ Y p₁ p₂]
/--
Definition of `trivial` / `trivial` 的定义

English:
definition trivial
  signature: (S : C)
  body: PreZeroHypercover.singleton (𝟙 S)
  I₁ _ _ := PUnit
  Y _ _ _ := S
  p₁ _ _ _ := 𝟙 _
  p₂ _ _ _ := 𝟙 _
  w _ _ _ := by simp

中文:
定义 trivial
  签名: (S : C)
  定义体: PreZeroHypercover.singleton (𝟙 S)
  I₁ _ _ := PUnit
  Y _ _ _ := S
  p₁ _ _ _ := 𝟙 _
  p₂ _ _ _ := 𝟙 _
  w _ _ _ := by simp

Depends on / 依赖: PreZeroHypercover, PreZeroHypercover.singleton, singleton
-/
def trivial (S : C) : PreOneHypercover.{w} S where
  __ := PreZeroHypercover.singleton (𝟙 S)
  I₁ _ _ := PUnit
  Y _ _ _ := S
  p₁ _ _ _ := 𝟙 _
  p₂ _ _ _ := 𝟙 _
  w _ _ _ := by simp

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `sieve₀_trivial` / 引理 `sieve₀_trivial`

English:
lemma sieve₀_trivial
  given: (S : C)
  statement: (trivial S).sieve₀ = ⊤
  proof: by
  rw [PreZeroHypercover.sieve₀]; rw [Sieve.ofArrows]; rw [← PreZeroHypercover.presieve₀]
  simp

中文:
引理 sieve₀_trivial
  条件: (S : C)
  结论: (trivial S).sieve₀ = ⊤
  证明: by
  rw [PreZeroHypercover.sieve₀]; rw [Sieve.ofArrows]; rw [← PreZeroHypercover.presieve₀]
  simp

Depends on / 依赖: PreZeroHypercover, PreZeroHypercover.presieve, PreZeroHypercover.sieve, Sieve.ofArrows, ofArrows
-/
lemma sieve₀_trivial (S : C) : (trivial S).sieve₀ = ⊤ := by
  rw [PreZeroHypercover.sieve₀]; rw [Sieve.ofArrows]; rw [← PreZeroHypercover.presieve₀]
  simp

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
lemma `sieve₁_trivial` / 引理 `sieve₁_trivial`

English:
lemma sieve₁_trivial
  given: {S : C} {W : C} {p : W ⟶ S}
  proof: by ext; simp

中文:
引理 sieve₁_trivial
  条件: {S : C} {W : C} {p : W ⟶ S}
  证明: by ext; simp
-/
lemma sieve₁_trivial {S : C} {W : C} {p : W ⟶ S} :
    (trivial S).sieve₁ (i₁ := ⟨⟩) (i₂ := ⟨⟩) p p = ⊤ := by ext; simp

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Nonempty (PreOneHypercover.{w} S)
  body: ⟨trivial S⟩

中文:
实例 :
  签名: Nonempty (PreOneHypercover.{w} S)
  定义体: ⟨trivial S⟩
-/
instance : Nonempty (PreOneHypercover.{w} S) := ⟨trivial S⟩

section

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Intersection of two pre-`1`-hypercovers. -/
@[simps toPreZeroHypercover I₁ Y p₁ p₂]
noncomputable
/--
Definition of `inter` / `inter` 的定义

English:
definition inter
  signature: (E F : PreOneHypercover S) [forall i j, HasPullback (E.f i) (F.f j)]
  body: E.toPreZeroHypercover.inter F.toPreZeroHypercover
  I₁ i j := E.I₁ i.1 j.1 × F.I₁ i.2 j.2
  Y i j k := pullback (E.p₁ k.1 ≫ E.f _) (F.p₁ k.2 ≫ F.f _)
  p₁ i j k := pullback.map _ _ _ _ (E.p₁ _) (F.p₁ _) (𝟙 S) (by simp) (by simp)
  p₂ i j k := pullback.map _ _ _ _ (E.p₂ _) (F.p₂ _) (𝟙 S) (by simp [E.

中文:
定义 inter
  签名: (E F : PreOneHypercover S) [对任意 i j, HasPullback (E.f i) (F.f j)]
  定义体: E.toPreZeroHypercover.inter F.toPreZeroHypercover
  I₁ i j := E.I₁ i.1 j.1 × F.I₁ i.2 j.2
  Y i j k := pullback (E.p₁ k.1 ≫ E.f _) (F.p₁ k.2 ≫ F.f _)
  p₁ i j k := pullback.map _ _ _ _ (E.p₁ _) (F.p₁ _) (𝟙 S) (by simp) (by simp)
  p₂ i j k := pullback.map _ _ _ _ (E.p₂ _) (F.p₂ _) (𝟙 S) (by simp [E.

Depends on / 依赖: E.toPreZeroHypercover.inter, F.toPreZeroHypercover, toPreZeroHypercover
-/
def inter (E F : PreOneHypercover S) [forall i j, HasPullback (E.f i) (F.f j)]
    [forall (i j : E.I₀) (k : E.I₁ i j) (a b : F.I₀) (l : F.I₁ a b),
      HasPullback (E.p₁ k ≫ E.f i) (F.p₁ l ≫ F.f a)] :
    PreOneHypercover S where
  __ := E.toPreZeroHypercover.inter F.toPreZeroHypercover
  I₁ i j := E.I₁ i.1 j.1 × F.I₁ i.2 j.2
  Y i j k := pullback (E.p₁ k.1 ≫ E.f _) (F.p₁ k.2 ≫ F.f _)
  p₁ i j k := pullback.map _ _ _ _ (E.p₁ _) (F.p₁ _) (𝟙 S) (by simp) (by simp)
  p₂ i j k := pullback.map _ _ _ _ (E.p₂ _) (F.p₂ _) (𝟙 S) (by simp [E.w]) (by simp [F.w])
  w := by simp [E.w]

variable {E} {F : PreOneHypercover S}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `sieve₁_inter` / 引理 `sieve₁_inter`

English:
lemma sieve₁_inter
  statement: [HasPullbacks C] {i j : E.I₀ × F.I₀} {W : C}
  proof: by
  ext Y f
  let p : W ⟶ pullback ((inter E F).f i) ((inter E F).f j) :=
    pullback.lift p₁ p₂ w
  refine ⟨fun ⟨k, a, h₁, h₂⟩ => ?_, fun ⟨Z, a, b, ⟨k, e, h₁, h₂⟩, ⟨l, u, u₁, u₂⟩, hab⟩ => ?_⟩
  · refine ⟨pullback p ((E.inter F).toPullback k), pullback.lift f a ?_,
        pullback.fst _ _, ?_, ?_

中文:
引理 sieve₁_inter
  结论: [HasPullbacks C] {i j : E.I₀ × F.I₀} {W : C}
  证明: by
  ext Y f
  let p : W ⟶ pullback ((inter E F).f i) ((inter E F).f j) :=
    pullback.lift p₁ p₂ w
  refine ⟨fun ⟨k, a, h₁, h₂⟩ => ?_, fun ⟨Z, a, b, ⟨k, e, h₁, h₂⟩, ⟨l, u, u₁, u₂⟩, hab⟩ => ?_⟩
  · refine ⟨pullback p ((E.inter F).toPullback k), pullback.lift f a ?_,
        pullback.fst _ _, ?_, ?_

Depends on / 依赖: E.inter, hom_ext, pullbac, pullback, pullback.fst, pullback.hom_ext, pullback.lift, pullback.snd, toPullback
-/
lemma sieve₁_inter [HasPullbacks C] {i j : E.I₀ × F.I₀} {W : C}
    {p₁ : W ⟶ pullback (E.f i.1) (F.f i.2)}
    {p₂ : W ⟶ pullback (E.f j.1) (F.f j.2)}
    (w : p₁ ≫ pullback.fst _ _ ≫ E.f _ = p₂ ≫ pullback.fst _ _ ≫ E.f _) :
    (inter E F).sieve₁ p₁ p₂ = Sieve.bind
      (E.sieve₁ (p₁ ≫ pullback.fst _ _) (p₂ ≫ pullback.fst _ _))
      (fun _ f _ => (F.sieve₁ (p₁ ≫ pullback.snd _ _) (p₂ ≫ pullback.snd _ _)).pullback f) := by
  ext Y f
  let p : W ⟶ pullback ((inter E F).f i) ((inter E F).f j) :=
    pullback.lift p₁ p₂ w
  refine ⟨fun ⟨k, a, h₁, h₂⟩ => ?_, fun ⟨Z, a, b, ⟨k, e, h₁, h₂⟩, ⟨l, u, u₁, u₂⟩, hab⟩ => ?_⟩
  · refine ⟨pullback p ((E.inter F).toPullback k), pullback.lift f a ?_,
        pullback.fst _ _, ?_, ?_, ?_⟩
    · apply pullback.hom_ext
      · apply pullback.hom_ext <;> simp [p, h₁, toPullback]
      · apply pullback.hom_ext <;> simp [p, h₂, toPullback]
    · refine ⟨k.1, pullback.snd _ _ ≫ pullback.fst _ _, ?_, ?_⟩
      · have : p₁ ≫ pullback.fst (E.f i.1) (F.f i.2) = p ≫ pullback.fst _ _ ≫ pullback.fst _ _ := by
          simp [p]
        simp [this, pullback.condition_assoc, toPullback]
      · have : p₂ ≫ pullback.fst (E.f j.1) (F.f j.2) = p ≫ pullback.snd _ _ ≫ pullback.fst _ _ := by
          simp [p]
        simp [this, pullback.condition_assoc, toPullback]
    · exact ⟨k.2, a ≫ pullback.snd _ _, by simp [reassoc_of% h₁], by simp [reassoc_of% h₂]⟩
    · simp
  · subst hab
    refine ⟨(k, l), pullback.lift (a ≫ e) u ?_, ?_, ?_⟩
    · simp only [Category.assoc] at u₁
      simp [← reassoc_of% h₁, w, ← reassoc_of% u₁, ← pullback.condition]
    · apply pullback.hom_ext
      · simp [h₁]
      · simpa using u₁
    · apply pullback.hom_ext
      · simp [h₂]
      · simpa using u₂

end

section Category

/-- A morphism of pre-`1`-hypercovers of `S` is a family of refinement morphisms commuting
with the structure morphisms of `E` and `F`. -/
@[ext]
/--
Definition of `Hom` / `Hom` 的定义

English:
structure Hom
  parameters: (E F : PreOneHypercover S)
  axioms and operations (4):
    - s₁({i j : E.I₀} (k : E.I₁ i j)) : F.I₁ (s₀ i) (s₀ j)
    - h₁({i j : E.I₀} (k : E.I₁ i j)) : E.Y k ⟶ F.Y (s₁ k)
    - w₁₁({i j : E.I₀} (k : E.I₁ i j)) : h₁ k ≫ F.p₁ (s₁ k) = E.p₁ k ≫ h₀ i  [default: by cat_disch]
    - w₁₂({i j : E.I₀} (k : E.I₁ i j)) : h₁ k ≫ F.p₂ (s₁ k) = E.p₂ k ≫ h₀ j  [default: by cat_disch]

中文:
结构 Hom
  参数: (E F : PreOneHypercover S)
  公理与运算 (4 个):
    - s₁({i j : E.I₀} (k : E.I₁ i j)) : F.I₁ (s₀ i) (s₀ j)
    - h₁({i j : E.I₀} (k : E.I₁ i j)) : E.Y k ⟶ F.Y (s₁ k)
    - w₁₁({i j : E.I₀} (k : E.I₁ i j)) : h₁ k ≫ F.p₁ (s₁ k) = E.p₁ k ≫ h₀ i  [默认: by cat_disch]
    - w₁₂({i j : E.I₀} (k : E.I₁ i j)) : h₁ k ≫ F.p₂ (s₁ k) = E.p₂ k ≫ h₀ j  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
structure Hom (E F : PreOneHypercover S) extends
    E.toPreZeroHypercover.Hom F.toPreZeroHypercover where
  /-- The map between indexing types of the coverings of the fibre products over `S`. -/
  s₁ {i j : E.I₀} (k : E.I₁ i j) : F.I₁ (s₀ i) (s₀ j)
  /-- The refinement morphisms between objects in the coverings of the fibre products over `S`. -/
  h₁ {i j : E.I₀} (k : E.I₁ i j) : E.Y k ⟶ F.Y (s₁ k)
  w₁₁ {i j : E.I₀} (k : E.I₁ i j) : h₁ k ≫ F.p₁ (s₁ k) = E.p₁ k ≫ h₀ i := by cat_disch
  w₁₂ {i j : E.I₀} (k : E.I₁ i j) : h₁ k ≫ F.p₂ (s₁ k) = E.p₂ k ≫ h₀ j := by cat_disch

attribute [reassoc] Hom.w₁₁ Hom.w₁₂

set_option backward.defeqAttrib.useBackward true in
/-- The identity refinement of a pre-`1`-hypercover. -/
@[simps!]
/--
Definition of `Hom.id` / `Hom.id` 的定义

English:
definition Hom.id
  signature: (E : PreOneHypercover S)
  body: PreZeroHypercover.Hom.id _
  s₁ := _root_.id
  h₁ _ := 𝟙 _

中文:
定义 Hom.id
  签名: (E : PreOneHypercover S)
  定义体: PreZeroHypercover.Hom.id _
  s₁ := _root_.id
  h₁ _ := 𝟙 _
-/
def Hom.id (E : PreOneHypercover S) : Hom E E where
  __ := PreZeroHypercover.Hom.id _
  s₁ := _root_.id
  h₁ _ := 𝟙 _

variable {E : PreOneHypercover.{w} S} {F : PreOneHypercover.{w'} S}
  {G : PreOneHypercover S}

set_option backward.defeqAttrib.useBackward true in
/-- Composition of refinement morphisms of pre-`1`-hypercovers. -/
@[simps!]
/--
Definition of `Hom.comp` / `Hom.comp` 的定义

English:
definition Hom.comp
  signature: (f : E.Hom F) (g : F.Hom G)
  body: PreZeroHypercover.Hom.comp _ _
  s₁ := g.s₁ ∘ f.s₁
  h₁ i := f.h₁ i ≫ g.h₁ _
  w₁₁ := by simp [w₁₁, w₁₁_assoc]
  w₁₂ := by simp [w₁₂, w₁₂_assoc]

中文:
定义 Hom.comp
  签名: (f : E.Hom F) (g : F.Hom G)
  定义体: PreZeroHypercover.Hom.comp _ _
  s₁ := g.s₁ ∘ f.s₁
  h₁ i := f.h₁ i ≫ g.h₁ _
  w₁₁ := by simp [w₁₁, w₁₁_assoc]
  w₁₂ := by simp [w₁₂, w₁₂_assoc]
-/
def Hom.comp (f : E.Hom F) (g : F.Hom G) : E.Hom G where
  __ := PreZeroHypercover.Hom.comp _ _
  s₁ := g.s₁ ∘ f.s₁
  h₁ i := f.h₁ i ≫ g.h₁ _
  w₁₁ := by simp [w₁₁, w₁₁_assoc]
  w₁₂ := by simp [w₁₂, w₁₂_assoc]

/-- The induced index map `E.I₁' → F.I₁'` from a refinement morphism `E ⟶ F`. -/
@[simp]
/--
Definition of `Hom.s₁'` / `Hom.s₁'` 的定义

English:
definition Hom.s₁'
  signature: (f : E.Hom F) (k : E.I₁')
  body: ⟨⟨f.s₀ k.1.1, f.s₀ k.1.2⟩, f.s₁ k.2⟩

中文:
定义 Hom.s₁'
  签名: (f : E.Hom F) (k : E.I₁')
  定义体: ⟨⟨f.s₀ k.1.1, f.s₀ k.1.2⟩, f.s₁ k.2⟩
-/
def Hom.s₁' (f : E.Hom F) (k : E.I₁') : F.I₁' :=
  ⟨⟨f.s₀ k.1.1, f.s₀ k.1.2⟩, f.s₁ k.2⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simps! id_s₀ id_s₁ id_h₀ id_h₁ comp_s₀ comp_s₁ comp_h₀ comp_h₁]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category (PreOneHypercover S)
  body: Hom
  id E := Hom.id E
  comp f g := f.comp g

中文:
实例 :
  签名: Category (PreOneHypercover S)
  定义体: Hom
  id E := Hom.id E
  comp f g := f.comp g
-/
instance : Category (PreOneHypercover S) where
  Hom := Hom
  id E := Hom.id E
  comp f g := f.comp g

set_option backward.isDefEq.respectTransparency.types false in
/-- The forgetful functor from pre-`1`-hypercovers to pre-`0`-hypercovers. -/
@[simps]
/--
Definition of `oneToZero` / `oneToZero` 的定义

English:
definition oneToZero
  signature: : PreOneHypercover.{w} S ⥤ PreZeroHypercover.{w} S where
  body: f.1
  map f := f.1

中文:
定义 oneToZero
  签名: : PreOneHypercover.{w} S ⥤ PreZeroHypercover.{w} S where
  定义体: f.1
  map f := f.1
-/
def oneToZero : PreOneHypercover.{w} S ⥤ PreZeroHypercover.{w} S where
  obj f := f.1
  map f := f.1

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `Hom.mapMultiforkOfIsLimit` / `Hom.mapMultiforkOfIsLimit` 的定义

English:
definition Hom.mapMultiforkOfIsLimit
  signature: (f : E.Hom F) (P : Cᵒᵖ ⥤ A) {c : Multifork (E.multicospanIndex P)}
  body: Multifork.IsLimit.lift hc (fun a => d.ι (f.s₀ a) ≫ P.map (f.h₀ a).op) by
    intro (k : E.I₁')
    simp only [multicospanIndex_right, multicospanShape_fst, multicospanIndex_left,
      multicospanIndex_fst, assoc, multicospanShape_snd, multicospanIndex_snd]
    have heq := d.condition (f.s₁' k)
    

中文:
定义 Hom.mapMultiforkOfIsLimit
  签名: (f : E.Hom F) (P : Cᵒᵖ ⥤ A) {c : Multifork (E.multicospanIndex P)}
  定义体: Multifork.IsLimit.lift hc (fun a => d.ι (f.s₀ a) ≫ P.map (f.h₀ a).op) by
    intro (k : E.I₁')
    simp only [multicospanIndex_right, multicospanShape_fst, multicospanIndex_left,
      multicospanIndex_fst, assoc, multicospanShape_snd, multicospanIndex_snd]
    have heq := d.condition (f.s₁' k)
    

Depends on / 依赖: Functor, Functor.map_comp, Hom.s, Hom.w, IsLimit, Multifork, Multifork.IsLimit.lift, P.map, condition, d.condition, map_comp, multicospanIndex_fst, multicospanIndex_left, multicospanIndex_right, multicospanIndex_snd, multicospanShape_fst, multicospanShape_snd, op_comp
-/
def Hom.mapMultiforkOfIsLimit (f : E.Hom F) (P : Cᵒᵖ ⥤ A) {c : Multifork (E.multicospanIndex P)}
    (hc : IsLimit c) (d : Multifork (F.multicospanIndex P)) :
    d.pt ⟶ c.pt :=
Multifork.IsLimit.lift hc (fun a => d.ι (f.s₀ a) ≫ P.map (f.h₀ a).op) by
    intro (k : E.I₁')
    simp only [multicospanIndex_right, multicospanShape_fst, multicospanIndex_left,
      multicospanIndex_fst, assoc, multicospanShape_snd, multicospanIndex_snd]
    have heq := d.condition (f.s₁' k)
    simp only [Hom.s₁', multicospanIndex_right, multicospanShape_fst, multicospanIndex_left,
      multicospanIndex_fst, multicospanShape_snd, multicospanIndex_snd] at heq
    rw [← Functor.map_comp]; rw [← op_comp]; rw [← Hom.w₁₁]; rw [← Functor.map_comp]; rw [← op_comp]; rw [← Hom.w₁₂]
    rw [op_comp]; rw [Functor.map_comp]; rw [reassoc_of% heq]; rw [op_comp]; rw [Functor.map_comp]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `Hom.mapMultiforkOfIsLimit_ι` / 引理 `Hom.mapMultiforkOfIsLimit_ι`

English:
lemma Hom.mapMultiforkOfIsLimit_ι
  proof: by
  simp [mapMultiforkOfIsLimit]

中文:
引理 Hom.mapMultiforkOfIsLimit_ι
  证明: by
  simp [mapMultiforkOfIsLimit]

Depends on / 依赖: mapMultiforkOfIsLimit
-/
lemma Hom.mapMultiforkOfIsLimit_ι
    (f : E.Hom F) (P : Cᵒᵖ ⥤ A) {c : Multifork (E.multicospanIndex P)} (hc : IsLimit c)
    (d : Multifork (F.multicospanIndex P)) (a : E.I₀) :
    f.mapMultiforkOfIsLimit P hc d ≫ c.ι a = d.ι (f.s₀ a) ≫ P.map (f.h₀ a).op := by
  simp [mapMultiforkOfIsLimit]

section

variable (f : E.Hom F) (P : Cᵒᵖ ⥤ A)
  {c : Multifork (E.multicospanIndex P)} (hc : IsLimit c) {d : Multifork (F.multicospanIndex P)}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `Hom.mapMultiforkOfIsLimit_id` / 引理 `Hom.mapMultiforkOfIsLimit_id`

English:
lemma Hom.mapMultiforkOfIsLimit_id
  given: (d : Multifork (E.multicospanIndex P))
  proof: by
  apply Multifork.IsLimit.hom_ext hc
  simp

中文:
引理 Hom.mapMultiforkOfIsLimit_id
  条件: (d : Multifork (E.multicospanIndex P))
  证明: by
  apply Multifork.IsLimit.hom_ext hc
  simp

Depends on / 依赖: IsLimit, Multifork, Multifork.IsLimit.hom_ext, hom_ext
-/
lemma Hom.mapMultiforkOfIsLimit_id (d : Multifork (E.multicospanIndex P)) :
    (Hom.id E).mapMultiforkOfIsLimit P hc d = Multifork.IsLimit.lift hc d.ι d.condition := by
  apply Multifork.IsLimit.hom_ext hc
  simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `Hom.mapMultiforkOfIsLimit_comp` / 引理 `Hom.mapMultiforkOfIsLimit_comp`

English:
lemma Hom.mapMultiforkOfIsLimit_comp
  statement: (g : F.Hom G) (t : Multifork (G.multicospanIndex P))
  proof: by
  apply Multifork.IsLimit.hom_ext hc
  simp

中文:
引理 Hom.mapMultiforkOfIsLimit_comp
  结论: (g : F.Hom G) (t : Multifork (G.multicospanIndex P))
  证明: by
  apply Multifork.IsLimit.hom_ext hc
  simp

Depends on / 依赖: IsLimit, Multifork, Multifork.IsLimit.hom_ext, hom_ext
-/
lemma Hom.mapMultiforkOfIsLimit_comp (g : F.Hom G) (t : Multifork (G.multicospanIndex P))
    (hd : IsLimit d) :
    (f.comp g).mapMultiforkOfIsLimit P hc t =
      g.mapMultiforkOfIsLimit P hd t ≫ f.mapMultiforkOfIsLimit P hc d := by
  apply Multifork.IsLimit.hom_ext hc
  simp

end

section

variable {S : C} {E : PreOneHypercover.{w} S} {F : PreOneHypercover.{w'} S}
  {i i' j j' : E.I₀} (hii' : i = i') (hjj' : j = j')

/--
Definition of `congrIndexOneOfEq` / `congrIndexOneOfEq` 的定义

English:
definition congrIndexOneOfEq
  signature: {E : PreOneHypercover.{w} S} {i i' j j' : E.I₀}
  body: hii' ▸ hjj' ▸ Equiv.refl _

@[simp]

中文:
定义 congrIndexOneOfEq
  签名: {E : PreOneHypercover.{w} S} {i i' j j' : E.I₀}
  定义体: hii' ▸ hjj' ▸ Equiv.refl _

@[simp]

Depends on / 依赖: Equiv.refl
-/
def congrIndexOneOfEq {E : PreOneHypercover.{w} S} {i i' j j' : E.I₀}
    (hii' : i = i') (hjj' : j = j') :
    E.I₁ i j ≃ E.I₁ i' j' :=
  hii' ▸ hjj' ▸ Equiv.refl _

@[simp]
/--
lemma `congrIndexOneOfEq_refl` / 引理 `congrIndexOneOfEq_refl`

English:
lemma congrIndexOneOfEq_refl
  given: (i j : E.I₀)
  proof: by
  simp [congrIndexOneOfEq]

@[simp]

中文:
引理 congrIndexOneOfEq_refl
  条件: (i j : E.I₀)
  证明: by
  simp [congrIndexOneOfEq]

@[simp]

Depends on / 依赖: congrIndexOneOfEq
-/
lemma congrIndexOneOfEq_refl (i j : E.I₀) :
    E.congrIndexOneOfEq rfl rfl = Equiv.refl (E.I₁ i j) := by
  simp [congrIndexOneOfEq]

@[simp]
/--
lemma `congrIndexOneOfEq_trans` / 引理 `congrIndexOneOfEq_trans`

English:
lemma congrIndexOneOfEq_trans
  statement: {i'' j'' : E.I₀} (hii'' : i' = i'') (hjj'' : j' = j'')
  proof: by
  subst hii' hjj'
  simp

中文:
引理 congrIndexOneOfEq_trans
  结论: {i'' j'' : E.I₀} (hii'' : i' = i'') (hjj'' : j' = j'')
  证明: by
  subst hii' hjj'
  simp
-/
lemma congrIndexOneOfEq_trans {i'' j'' : E.I₀} (hii'' : i' = i'') (hjj'' : j' = j'')
    (k : E.I₁ i j) :
    E.congrIndexOneOfEq hii'' hjj'' (E.congrIndexOneOfEq hii' hjj' k) =
      E.congrIndexOneOfEq (hii'.trans hii'') (hjj'.trans hjj'') k := by
  subst hii' hjj'
  simp

/--
lemma `congrIndexOneOfEq_naturality` / 引理 `congrIndexOneOfEq_naturality`

English:
lemma congrIndexOneOfEq_naturality
  statement: (u₀ : E.I₀ -> F.I₀) (u₁ : forall ⦃i j⦄, E.I₁ i j -> F.I₁ (u₀ i) (u₀ j))
  proof: by
  subst hii' hjj'
  simp

中文:
引理 congrIndexOneOfEq_naturality
  结论: (u₀ : E.I₀ -> F.I₀) (u₁ : 对任意 ⦃i j⦄, E.I₁ i j -> F.I₁ (u₀ i) (u₀ j))
  证明: by
  subst hii' hjj'
  simp
-/
lemma congrIndexOneOfEq_naturality (u₀ : E.I₀ -> F.I₀) (u₁ : forall ⦃i j⦄, E.I₁ i j -> F.I₁ (u₀ i) (u₀ j))
    (k : E.I₁ i j) :
    u₁ (E.congrIndexOneOfEq hii' hjj' k) =
      F.congrIndexOneOfEq (congrArg u₀ hii') (congrArg u₀ hjj') (u₁ k) := by
  subst hii' hjj'
  simp

/--
lemma `congrIndexOneOfEq_congrFun` / 引理 `congrIndexOneOfEq_congrFun`

English:
lemma congrIndexOneOfEq_congrFun
  proof: by
  subst h₀
  simp [h₁]

@[ext (iff := false)]

中文:
引理 congrIndexOneOfEq_congrFun
  证明: by
  subst h₀
  simp [h₁]

@[ext (iff := false)]
-/
lemma congrIndexOneOfEq_congrFun
    {u₀ v₀ : E.I₀ -> F.I₀}
    {u₁ : forall ⦃i j⦄, E.I₁ i j -> F.I₁ (u₀ i) (u₀ j)}
    {v₁ : forall ⦃i j⦄, E.I₁ i j -> F.I₁ (v₀ i) (v₀ j)}
    (h₀ : u₀ = v₀)
    (h₁ : forall (i j : E.I₀) (k : E.I₁ i j),
      u₁ k = F.congrIndexOneOfEq (by simp [h₀]) (by simp [h₀]) (v₁ k))
    {i j : E.I₀} (k : E.I₁ i j) :
    F.congrIndexOneOfEq (congrFun h₀.symm _) (congrFun h₀.symm _) (v₁ k) = u₁ k := by
  subst h₀
  simp [h₁]

@[ext (iff := false)]
/--
lemma `I₁'.ext` / 引理 `I₁'.ext`

English:
lemma I₁'.ext
  statement: {a b : E.I₁'} (left : a.1.1 = b.1.1) (right : a.1.2 = b.1.2)
  proof: by
  obtain ⟨⟨i, j⟩, k⟩ := a
  obtain ⟨⟨i', j'⟩, k'⟩ := b
  dsimp at left right
  subst left right
  simpa using h

中文:
引理 I₁'.ext
  结论: {a b : E.I₁'} (left : a.1.1 = b.1.1) (right : a.1.2 = b.1.2)
  证明: by
  obtain ⟨⟨i, j⟩, k⟩ := a
  obtain ⟨⟨i', j'⟩, k'⟩ := b
  dsimp at left right
  subst left right
  simpa using h
-/
lemma I₁'.ext {a b : E.I₁'} (left : a.1.1 = b.1.1) (right : a.1.2 = b.1.2)
    (h : E.congrIndexOneOfEq left right a.2 = b.2) :
    a = b := by
  obtain ⟨⟨i, j⟩, k⟩ := a
  obtain ⟨⟨i', j'⟩, k'⟩ := b
  dsimp at left right
  subst left right
  simpa using h

/--
Definition of `congrIndexOneOfEqIso` / `congrIndexOneOfEqIso` 的定义

English:
definition congrIndexOneOfEqIso
  signature: {E : PreOneHypercover S} {i i' j j' : E.I₀}
  body: eqToIso (by subst hii' hjj'; simp)

中文:
定义 congrIndexOneOfEqIso
  签名: {E : PreOneHypercover S} {i i' j j' : E.I₀}
  定义体: eqToIso (by subst hii' hjj'; simp)

Depends on / 依赖: eqToIso
-/
def congrIndexOneOfEqIso {E : PreOneHypercover S} {i i' j j' : E.I₀}
    (hii' : i = i') (hjj' : j = j') (k : E.I₁ i j) :
    E.Y (E.congrIndexOneOfEq hii' hjj' k) ≅ E.Y k :=
  eqToIso (by subst hii' hjj'; simp)

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `congrIndexOneOfEqIso_refl` / 引理 `congrIndexOneOfEqIso_refl`

English:
lemma congrIndexOneOfEqIso_refl
  given: {i j : E.I₀} (k : E.I₁ i j)
  proof: by
  simp [congrIndexOneOfEqIso]

中文:
引理 congrIndexOneOfEqIso_refl
  条件: {i j : E.I₀} (k : E.I₁ i j)
  证明: by
  simp [congrIndexOneOfEqIso]

Depends on / 依赖: congrIndexOneOfEqIso
-/
lemma congrIndexOneOfEqIso_refl {i j : E.I₀} (k : E.I₁ i j) :
    E.congrIndexOneOfEqIso rfl rfl k = Iso.refl _ := by
  simp [congrIndexOneOfEqIso]

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/--
lemma `congrIndexOneOfEqIso_hom_p₁` / 引理 `congrIndexOneOfEqIso_hom_p₁`

English:
lemma congrIndexOneOfEqIso_hom_p₁
  given: (k : E.I₁ i j)
  proof: by
  subst hii' hjj'
  simp [congrIndexOneOfEqIso, congrIndexOneOfEq]

中文:
引理 congrIndexOneOfEqIso_hom_p₁
  条件: (k : E.I₁ i j)
  证明: by
  subst hii' hjj'
  simp [congrIndexOneOfEqIso, congrIndexOneOfEq]

Depends on / 依赖: congrIndexOneOfEq, congrIndexOneOfEqIso
-/
lemma congrIndexOneOfEqIso_hom_p₁ (k : E.I₁ i j) :
    (E.congrIndexOneOfEqIso hii' hjj' k).hom ≫ E.p₁ _ = E.p₁ _ ≫ eqToHom (by rw [hii']) := by
  subst hii' hjj'
  simp [congrIndexOneOfEqIso, congrIndexOneOfEq]

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/--
lemma `congrIndexOneOfEqIso_inv_p₁` / 引理 `congrIndexOneOfEqIso_inv_p₁`

English:
lemma congrIndexOneOfEqIso_inv_p₁
  given: (k : E.I₁ i j)
  proof: by
  subst hii' hjj'
  simp [congrIndexOneOfEqIso, congrIndexOneOfEq]

中文:
引理 congrIndexOneOfEqIso_inv_p₁
  条件: (k : E.I₁ i j)
  证明: by
  subst hii' hjj'
  simp [congrIndexOneOfEqIso, congrIndexOneOfEq]

Depends on / 依赖: congrIndexOneOfEq, congrIndexOneOfEqIso
-/
lemma congrIndexOneOfEqIso_inv_p₁ (k : E.I₁ i j) :
    (E.congrIndexOneOfEqIso hii' hjj' k).inv ≫ E.p₁ _ = E.p₁ k ≫ eqToHom (by rw [hii']) := by
  subst hii' hjj'
  simp [congrIndexOneOfEqIso, congrIndexOneOfEq]

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/--
lemma `congrIndexOneOfEqIso_inv_p₂` / 引理 `congrIndexOneOfEqIso_inv_p₂`

English:
lemma congrIndexOneOfEqIso_inv_p₂
  given: (k : E.I₁ i j)
  proof: by
  subst hii' hjj'
  simp [congrIndexOneOfEqIso, congrIndexOneOfEq]

中文:
引理 congrIndexOneOfEqIso_inv_p₂
  条件: (k : E.I₁ i j)
  证明: by
  subst hii' hjj'
  simp [congrIndexOneOfEqIso, congrIndexOneOfEq]

Depends on / 依赖: congrIndexOneOfEq, congrIndexOneOfEqIso
-/
lemma congrIndexOneOfEqIso_inv_p₂ (k : E.I₁ i j) :
    (E.congrIndexOneOfEqIso hii' hjj' k).inv ≫ E.p₂ _ = E.p₂ k ≫ eqToHom (by rw [hjj']) := by
  subst hii' hjj'
  simp [congrIndexOneOfEqIso, congrIndexOneOfEq]

variable {i i' j j' : E.I₀} (u₀ : E.I₀ -> F.I₀)
  (u₁ : forall i j : E.I₀, forall _ : E.I₁ i j, F.I₁ (u₀ i) (u₀ j))
  (z : forall i j (k : E.I₁ i j), E.Y k ⟶ F.Y (u₁ i j k))
  (hii' : i = i') (hjj' : j = j') (k : E.I₁ i j)

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
/--
lemma `congrIndexOneOfEqIso_hom_naturality` / 引理 `congrIndexOneOfEqIso_hom_naturality`

English:
lemma congrIndexOneOfEqIso_hom_naturality
  proof: by
  subst hii' hjj'
  simp [congrIndexOneOfEqIso, congrIndexOneOfEq]

中文:
引理 congrIndexOneOfEqIso_hom_naturality
  证明: by
  subst hii' hjj'
  simp [congrIndexOneOfEqIso, congrIndexOneOfEq]

Depends on / 依赖: congrIndexOneOfEq, congrIndexOneOfEqIso
-/
lemma congrIndexOneOfEqIso_hom_naturality :
    (E.congrIndexOneOfEqIso hii' hjj' k).hom ≫
      z i j k =
      z i' j' _ ≫ eqToHom (by subst hii' hjj'; simp [congrIndexOneOfEq]) ≫
      (F.congrIndexOneOfEqIso (congrArg u₀ hii') (congrArg u₀ hjj') _).hom := by
  subst hii' hjj'
  simp [congrIndexOneOfEqIso, congrIndexOneOfEq]

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
/--
lemma `congrIndexOneOfEqIso_inv_naturality` / 引理 `congrIndexOneOfEqIso_inv_naturality`

English:
lemma congrIndexOneOfEqIso_inv_naturality
  proof: by
  subst hii' hjj'
  simp [congrIndexOneOfEqIso, congrIndexOneOfEq]

中文:
引理 congrIndexOneOfEqIso_inv_naturality
  证明: by
  subst hii' hjj'
  simp [congrIndexOneOfEqIso, congrIndexOneOfEq]

Depends on / 依赖: congrIndexOneOfEq, congrIndexOneOfEqIso
-/
lemma congrIndexOneOfEqIso_inv_naturality :
    (E.congrIndexOneOfEqIso hii' hjj' k).inv ≫
      z i' j' _ ≫
      eqToHom (by subst hii' hjj'; simp [congrIndexOneOfEq]) =
      z i j k ≫
        (F.congrIndexOneOfEqIso (congrArg u₀ hii') (congrArg u₀ hjj') (u₁ _ _ k)).inv := by
  subst hii' hjj'
  simp [congrIndexOneOfEqIso, congrIndexOneOfEq]

end

set_option backward.isDefEq.respectTransparency false in
/--
lemma `Hom.ext'` / 引理 `Hom.ext'`

English:
lemma Hom.ext'
  statement: {E F : PreOneHypercover S} {f g : E.Hom F}
  proof: by
  obtain ⟨toHomf, fs₁, fh₁⟩ := f
  obtain ⟨toHomg, gs₁, gh₁⟩ := g
  obtain rfl : toHomf = toHomg := PreZeroHypercover.Hom.ext' hs₀ hh₀
  obtain rfl : @fs₁ = @gs₁ := by
    ext i j k
    simpa using hs₁ i j k
  simp_all only [eqToHom_refl, Category.comp_id, implies_true, congrIndexOneOfEqIso_refl,

中文:
引理 Hom.ext'
  结论: {E F : PreOneHypercover S} {f g : E.Hom F}
  证明: by
  obtain ⟨toHomf, fs₁, fh₁⟩ := f
  obtain ⟨toHomg, gs₁, gh₁⟩ := g
  obtain rfl : toHomf = toHomg := PreZeroHypercover.Hom.ext' hs₀ hh₀
  obtain rfl : @fs₁ = @gs₁ := by
    ext i j k
    simpa using hs₁ i j k
  simp_all only [eqToHom_refl, Category.comp_id, implies_true, congrIndexOneOfEqIso_refl,
-/
lemma Hom.ext' {E F : PreOneHypercover S} {f g : E.Hom F}
    (hs₀ : f.s₀ = g.s₀) (hh₀ : forall i, f.h₀ i = g.h₀ i ≫ eqToHom (by simp [hs₀]))
    (hs₁ : forall (i j : E.I₀) (k : E.I₁ i j),
      f.s₁ k = F.congrIndexOneOfEq (by simp [hs₀]) (by simp [hs₀]) (g.s₁ k))
    (hh₁ : forall (i j : E.I₀) (k : E.I₁ i j),
      f.h₁ k = g.h₁ k ≫
        (F.congrIndexOneOfEqIso (congrFun hs₀.symm i) (congrFun hs₀.symm j) (g.s₁ k)).inv ≫
        eqToHom (by rw [PreOneHypercover.congrIndexOneOfEq_congrFun hs₀ hs₁])) :
    f = g := by
  obtain ⟨toHomf, fs₁, fh₁⟩ := f
  obtain ⟨toHomg, gs₁, gh₁⟩ := g
  obtain rfl : toHomf = toHomg := PreZeroHypercover.Hom.ext' hs₀ hh₀
  obtain rfl : @fs₁ = @gs₁ := by
    ext i j k
    simpa using hs₁ i j k
  simp_all only [eqToHom_refl, Category.comp_id, implies_true, congrIndexOneOfEqIso_refl,
    Iso.refl_inv, mk.injEq, heq_eq_eq, true_and]
  ext i j k
  rw [hh₁ i j k]
  exact Category.comp_id _

/--
lemma `Hom.ext'_iff` / 引理 `Hom.ext'_iff`

English:
lemma Hom.ext'_iff
  given: {E F : PreOneHypercover S} {f g : E.Hom F}
  proof: by
  refine ⟨fun h => ?_, fun ⟨hs₀, hh₀, hs₁, hh₁⟩ => Hom.ext' hs₀ hh₀ hs₁ hh₁⟩
  subst h
  simp [congrIndexOneOfEq]

中文:
引理 Hom.ext'_iff
  条件: {E F : PreOneHypercover S} {f g : E.Hom F}
  证明: by
  refine ⟨fun h => ?_, fun ⟨hs₀, hh₀, hs₁, hh₁⟩ => Hom.ext' hs₀ hh₀ hs₁ hh₁⟩
  subst h
  simp [congrIndexOneOfEq]
-/
lemma Hom.ext'_iff {E F : PreOneHypercover S} {f g : E.Hom F} :
    f = g ↔ exists (hs₀ : f.s₀ = g.s₀) (_ : forall i, f.h₀ i = g.h₀ i ≫ eqToHom (by simp [hs₀]))
      (hs₁ : forall (i j : E.I₀) (k : E.I₁ i j),
        f.s₁ k = F.congrIndexOneOfEq (by simp [hs₀]) (by simp [hs₀]) (g.s₁ k)),
      forall (i j : E.I₀) (k : E.I₁ i j),
        f.h₁ k = g.h₁ k ≫
          (F.congrIndexOneOfEqIso (congrFun hs₀.symm i) (congrFun hs₀.symm j) (g.s₁ k)).inv ≫
          eqToHom (by rw [PreOneHypercover.congrIndexOneOfEq_congrFun hs₀ hs₁]) := by
  refine ⟨fun h => ?_, fun ⟨hs₀, hh₀, hs₁, hh₁⟩ => Hom.ext' hs₀ hh₀ hs₁ hh₁⟩
  subst h
  simp [congrIndexOneOfEq]

section

variable (s₀ : E.I₀ ≃ F.I₀) (s₁ : forall ⦃i j : E.I₀⦄, E.I₁ i j ≃ F.I₁ (s₀ i) (s₀ j))
  {i j : E.I₀} (k : E.I₁ i j)

/--
lemma `congrIndexOneOfEq_equiv` / 引理 `congrIndexOneOfEq_equiv`

English:
lemma congrIndexOneOfEq_equiv
  proof: by
  apply Equiv.injective (s₁ (i := s₀.symm (s₀ i)) (j := s₀.symm (s₀ j)))
  simp [PreOneHypercover.congrIndexOneOfEq_naturality (u₁ := fun i j k => s₁ k)]

中文:
引理 congrIndexOneOfEq_equiv
  证明: by
  apply Equiv.injective (s₁ (i := s₀.symm (s₀ i)) (j := s₀.symm (s₀ j)))
  simp [PreOneHypercover.congrIndexOneOfEq_naturality (u₁ := fun i j k => s₁ k)]

Depends on / 依赖: Equiv.injective, PreOneHypercover, PreOneHypercover.congrIndexOneOfEq_naturality, congrIndexOneOfEq_naturality, injective
-/
lemma congrIndexOneOfEq_equiv :
    (congrIndexOneOfEq (s₀.symm_apply_apply i).symm (s₀.symm_apply_apply j).symm) k =
      s₁.symm ((congrIndexOneOfEq (by simp) (by simp)) (s₁ k)) := by
  apply Equiv.injective (s₁ (i := s₀.symm (s₀ i)) (j := s₀.symm (s₀ j)))
  simp [PreOneHypercover.congrIndexOneOfEq_naturality (u₁ := fun i j k => s₁ k)]

/-- (Implementation): Auxiliary lemma for `CategoryTheory.PreOneHypercover.isoMk`. -/
@[reassoc]
/--
lemma `isoMk_aux` / 引理 `isoMk_aux`

English:
lemma isoMk_aux
  given: (h₁ : forall ⦃i j : E.I₀⦄ (k : E.I₁ i j), E.Y k ≅ F.Y (s₁ k)) (k : E.I₁ i j)
  proof: by
  rw [← PreOneHypercover.congrIndexOneOfEqIso_inv_naturality_assoc
      (z := fun i j k => (h₁ k).hom) (hii' := by simp) (hjj' := by simp)]; rw [eqToHom_trans_assoc]; rw [eqToHom_iso_hom_naturality_assoc]
  · simp
  · apply PreOneHypercover.congrIndexOneOfEq_equiv

中文:
引理 isoMk_aux
  条件: (h₁ : 对任意 ⦃i j : E.I₀⦄ (k : E.I₁ i j), E.Y k ≅ F.Y (s₁ k)) (k : E.I₁ i j)
  证明: by
  rw [← PreOneHypercover.congrIndexOneOfEqIso_inv_naturality_assoc
      (z := fun i j k => (h₁ k).hom) (hii' := by simp) (hjj' := by simp)]; rw [eqToHom_trans_assoc]; rw [eqToHom_iso_hom_naturality_assoc]
  · simp
  · apply PreOneHypercover.congrIndexOneOfEq_equiv

Depends on / 依赖: PreOneHypercover, PreOneHypercover.congrIndexOneOfEqIso_inv_naturality_assoc, PreOneHypercover.congrIndexOneOfEq_equiv, congrIndexOneOfEqIso_inv_naturality_assoc, congrIndexOneOfEq_equiv, eqToHom_iso_hom_naturality_assoc, eqToHom_trans_assoc
-/
lemma isoMk_aux (h₁ : forall ⦃i j : E.I₀⦄ (k : E.I₁ i j), E.Y k ≅ F.Y (s₁ k)) (k : E.I₁ i j) :
    (h₁ k).hom ≫ (congrIndexOneOfEqIso
        (congrArg s₀ (s₀.symm_apply_apply i).symm)
        (congrArg s₀ (s₀.symm_apply_apply j).symm) (s₁ k)).inv ≫
      eqToHom (by simp) ≫
      (h₁ (s₁.symm ((congrIndexOneOfEq
        (congrArg s₀ (s₀.symm_apply_apply i).symm)
        (congrArg s₀ (s₀.symm_apply_apply j).symm)) (s₁ k)))).inv =
      (congrIndexOneOfEqIso (s₀.symm_apply_apply i).symm (s₀.symm_apply_apply j).symm k).inv ≫
      eqToHom (by congr 1; apply E.congrIndexOneOfEq_equiv s₀ s₁ _) := by
  rw [← PreOneHypercover.congrIndexOneOfEqIso_inv_naturality_assoc
      (z := fun i j k => (h₁ k).hom) (hii' := by simp) (hjj' := by simp)]; rw [eqToHom_trans_assoc]; rw [eqToHom_iso_hom_naturality_assoc]
  · simp
  · apply PreOneHypercover.congrIndexOneOfEq_equiv

end

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Construct an isomorphism of `1`-hypercovers by giving the compatibility conditions only
in the forward direction. -/
@[simps!]
/--
Definition of `isoMk` / `isoMk` 的定义

English:
definition isoMk
  signature: {S : C} {E F : PreOneHypercover S}
  body: (PreZeroHypercover.isoMk s₀ h₀ w₀).hom
  hom.s₁ k := s₁ k
  hom.h₁ k := (h₁ k).hom
  inv.toHom := (PreZeroHypercover.isoMk s₀ h₀ w₀).inv
  inv.s₁ {i j} k := s₁.symm (F.congrIndexOneOfEq (by simp) (by simp) k)
  inv.h₁ {i j} k :=
    (F.congrIndexOneOfEqIso (s₀.apply_symm_apply i).symm (s₀.apply_symm

中文:
定义 isoMk
  签名: {S : C} {E F : PreOneHypercover S}
  定义体: (PreZeroHypercover.isoMk s₀ h₀ w₀).hom
  hom.s₁ k := s₁ k
  hom.h₁ k := (h₁ k).hom
  inv.toHom := (PreZeroHypercover.isoMk s₀ h₀ w₀).inv
  inv.s₁ {i j} k := s₁.symm (F.congrIndexOneOfEq (by simp) (by simp) k)
  inv.h₁ {i j} k :=
    (F.congrIndexOneOfEqIso (s₀.apply_symm_apply i).symm (s₀.apply_symm

Depends on / 依赖: F.congrIndexOneOfEq, F.congrIndexOneOfEqIso, PreZeroHypercover, PreZeroHypercover.isoMk, apply_sy, cat_disch, congrIndexOneOfEq, congrIndexOneOfEqIso, hom.h, hom.s, hom.toHom, inv.h, inv.s, inv.toHom
-/
def isoMk {S : C} {E F : PreOneHypercover S}
    (s₀ : E.I₀ ≃ F.I₀) (h₀ : (i : E.I₀) -> E.X i ≅ F.X (s₀ i))
    (s₁ : forall ⦃i j : E.I₀⦄, E.I₁ i j ≃ F.I₁ (s₀ i) (s₀ j))
    (h₁ : forall ⦃i j : E.I₀⦄ (k : E.I₁ i j), E.Y k ≅ F.Y (s₁ k))
    (w₀ : forall (i : E.I₀), (h₀ i).hom ≫ F.f (s₀ i) = E.f i := by cat_disch)
    (w₁₁ : forall ⦃i j : E.I₀⦄ (k : E.I₁ i j),
      (h₁ k).hom ≫ F.p₁ _ = E.p₁ _ ≫ (h₀ i).hom := by cat_disch)
    (w₁₂ : forall ⦃i j : E.I₀⦄ (k : E.I₁ i j),
      (h₁ k).hom ≫ F.p₂ _ = E.p₂ _ ≫ (h₀ j).hom := by cat_disch) :
    E ≅ F where
  hom.toHom := (PreZeroHypercover.isoMk s₀ h₀ w₀).hom
  hom.s₁ k := s₁ k
  hom.h₁ k := (h₁ k).hom
  inv.toHom := (PreZeroHypercover.isoMk s₀ h₀ w₀).inv
  inv.s₁ {i j} k := s₁.symm (F.congrIndexOneOfEq (by simp) (by simp) k)
  inv.h₁ {i j} k :=
    (F.congrIndexOneOfEqIso (s₀.apply_symm_apply i).symm (s₀.apply_symm_apply j).symm k).inv ≫
      eqToHom (by simp) ≫ (h₁ _).inv
  inv.w₁₁ {i j} k := by
    obtain ⟨i, rfl⟩ := s₀.surjective i
    obtain ⟨j, rfl⟩ := s₀.surjective j
    obtain ⟨k, rfl⟩ := s₁.surjective k
    rw [← cancel_epi (h₁ k).hom]; rw [reassoc_of% w₁₁ k]
    simp only [PreZeroHypercover.isoMk_inv_s₀, Category.assoc, PreZeroHypercover.isoMk_inv_h₀,
      Equiv.symm_apply_apply, eqToHom_iso_hom_naturality_assoc, Iso.hom_inv_id,
      Category.comp_id]
    rw [PreOneHypercover.isoMk_aux_assoc]; rw [← eqToHom_naturality]; rw [eqToHom_refl]; rw [Category.comp_id]; rw [congrIndexOneOfEqIso_inv_p₁]
    apply PreOneHypercover.congrIndexOneOfEq_equiv
  inv.w₁₂ {i j} k := by
    obtain ⟨i, rfl⟩ := s₀.surjective i
    obtain ⟨j, rfl⟩ := s₀.surjective j
    obtain ⟨k, rfl⟩ := s₁.surjective k
    rw [← cancel_epi (h₁ k).hom]; rw [reassoc_of% w₁₂ k]
    simp only [PreZeroHypercover.isoMk_inv_s₀, Category.assoc, PreZeroHypercover.isoMk_inv_h₀,
      Equiv.symm_apply_apply, eqToHom_iso_hom_naturality_assoc, Iso.hom_inv_id,
      Category.comp_id]
    rw [PreOneHypercover.isoMk_aux_assoc]; rw [← eqToHom_naturality]; rw [eqToHom_refl]; rw [Category.comp_id]; rw [congrIndexOneOfEqIso_inv_p₂]
    apply PreOneHypercover.congrIndexOneOfEq_equiv
  inv_hom_id := by
    refine PreOneHypercover.Hom.ext' (by ext; simp) (by intro i; simp)
      (by simp) fun i j k => ?_
    dsimp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    -- If this step is replaced by `simp only [Category.id_comp]` it takes 5 seconds
    exact (Category.id_comp _).symm
  hom_inv_id := by
    refine PreOneHypercover.Hom.ext' (by ext; simp) (by intro i; simp)
      (fun i j k => (E.congrIndexOneOfEq_equiv s₀ s₁ _).symm) ?_
    intro i j k
    simpa using E.isoMk_aux s₀ s₁ h₁ k

section

variable {S : C} {E F : PreOneHypercover.{w} S} (e : E ≅ F)

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `hom_inv_s₀_apply` / 引理 `hom_inv_s₀_apply`

English:
lemma hom_inv_s₀_apply
  given: (i : E.I₀)
  statement: e.inv.s₀ (e.hom.s₀ i) = i
  proof: congr($(e.hom_inv_id).s₀ i)

中文:
引理 hom_inv_s₀_apply
  条件: (i : E.I₀)
  结论: e.inv.s₀ (e.hom.s₀ i) = i
  证明: congr($(e.hom_inv_id).s₀ i)

Depends on / 依赖: e.hom_inv_id, hom_inv_id
-/
lemma hom_inv_s₀_apply (i : E.I₀) : e.inv.s₀ (e.hom.s₀ i) = i :=
  congr($(e.hom_inv_id).s₀ i)

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `inv_hom_s₀_apply` / 引理 `inv_hom_s₀_apply`

English:
lemma inv_hom_s₀_apply
  given: (i : F.I₀)
  statement: e.hom.s₀ (e.inv.s₀ i) = i
  proof: congr($(e.inv_hom_id).s₀ i)

中文:
引理 inv_hom_s₀_apply
  条件: (i : F.I₀)
  结论: e.hom.s₀ (e.inv.s₀ i) = i
  证明: congr($(e.inv_hom_id).s₀ i)

Depends on / 依赖: e.inv_hom_id, inv_hom_id
-/
lemma inv_hom_s₀_apply (i : F.I₀) : e.hom.s₀ (e.inv.s₀ i) = i :=
  congr($(e.inv_hom_id).s₀ i)

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `hom_inv_s₁_apply` / 引理 `hom_inv_s₁_apply`

English:
lemma hom_inv_s₁_apply
  given: {i j : E.I₀} (k : E.I₁ i j)
  proof: by
  obtain ⟨hs₀, hh₀, hs₁, hh₁⟩ := PreOneHypercover.Hom.ext'_iff.mp e.hom_inv_id
  simpa using! hs₁ i j k

中文:
引理 hom_inv_s₁_apply
  条件: {i j : E.I₀} (k : E.I₁ i j)
  证明: by
  obtain ⟨hs₀, hh₀, hs₁, hh₁⟩ := PreOneHypercover.Hom.ext'_iff.mp e.hom_inv_id
  simpa using! hs₁ i j k

Depends on / 依赖: PreOneHypercover, PreOneHypercover.Hom.ext, _iff, _iff.mp, e.hom_inv_id, hom_inv_id
-/
lemma hom_inv_s₁_apply {i j : E.I₀} (k : E.I₁ i j) :
    e.inv.s₁ (e.hom.s₁ k) = E.congrIndexOneOfEq (by simp) (by simp) k := by
  obtain ⟨hs₀, hh₀, hs₁, hh₁⟩ := PreOneHypercover.Hom.ext'_iff.mp e.hom_inv_id
  simpa using! hs₁ i j k

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `inv_hom_s₁_apply` / 引理 `inv_hom_s₁_apply`

English:
lemma inv_hom_s₁_apply
  given: {i j : F.I₀} (k : F.I₁ i j)
  proof: by
  obtain ⟨hs₀, hh₀, hs₁, hh₁⟩ := PreOneHypercover.Hom.ext'_iff.mp e.inv_hom_id
  simpa using! hs₁ i j k

中文:
引理 inv_hom_s₁_apply
  条件: {i j : F.I₀} (k : F.I₁ i j)
  证明: by
  obtain ⟨hs₀, hh₀, hs₁, hh₁⟩ := PreOneHypercover.Hom.ext'_iff.mp e.inv_hom_id
  simpa using! hs₁ i j k

Depends on / 依赖: PreOneHypercover, PreOneHypercover.Hom.ext, _iff, _iff.mp, e.inv_hom_id, inv_hom_id
-/
lemma inv_hom_s₁_apply {i j : F.I₀} (k : F.I₁ i j) :
    e.hom.s₁ (e.inv.s₁ k) = F.congrIndexOneOfEq (by simp) (by simp) k := by
  obtain ⟨hs₀, hh₀, hs₁, hh₁⟩ := PreOneHypercover.Hom.ext'_iff.mp e.inv_hom_id
  simpa using! hs₁ i j k

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/--
lemma `hom_inv_h₀` / 引理 `hom_inv_h₀`

English:
lemma hom_inv_h₀
  given: (i : E.I₀)
  statement: e.hom.h₀ i ≫ e.inv.h₀ (e.hom.s₀ i) = eqToHom (by simp)
  proof: by
  obtain ⟨hs, hh, _⟩ := Hom.ext'_iff.mp e.hom_inv_id
  simpa using hh i

中文:
引理 hom_inv_h₀
  条件: (i : E.I₀)
  结论: e.hom.h₀ i ≫ e.inv.h₀ (e.hom.s₀ i) = eqToHom (by simp)
  证明: by
  obtain ⟨hs, hh, _⟩ := Hom.ext'_iff.mp e.hom_inv_id
  simpa using hh i

Depends on / 依赖: Hom.ext, _iff, _iff.mp, e.hom_inv_id, hom_inv_id
-/
lemma hom_inv_h₀ (i : E.I₀) : e.hom.h₀ i ≫ e.inv.h₀ (e.hom.s₀ i) = eqToHom (by simp) := by
  obtain ⟨hs, hh, _⟩ := Hom.ext'_iff.mp e.hom_inv_id
  simpa using hh i

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/--
lemma `inv_hom_h₀` / 引理 `inv_hom_h₀`

English:
lemma inv_hom_h₀
  given: (i : F.I₀)
  statement: e.inv.h₀ i ≫ e.hom.h₀ (e.inv.s₀ i) = eqToHom (by simp)
  proof: by
  obtain ⟨hs, hh, _⟩ := Hom.ext'_iff.mp e.inv_hom_id
  simpa using hh i

中文:
引理 inv_hom_h₀
  条件: (i : F.I₀)
  结论: e.inv.h₀ i ≫ e.hom.h₀ (e.inv.s₀ i) = eqToHom (by simp)
  证明: by
  obtain ⟨hs, hh, _⟩ := Hom.ext'_iff.mp e.inv_hom_id
  simpa using hh i

Depends on / 依赖: Hom.ext, _iff, _iff.mp, e.inv_hom_id, inv_hom_id
-/
lemma inv_hom_h₀ (i : F.I₀) : e.inv.h₀ i ≫ e.hom.h₀ (e.inv.s₀ i) = eqToHom (by simp) := by
  obtain ⟨hs, hh, _⟩ := Hom.ext'_iff.mp e.inv_hom_id
  simpa using hh i

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/--
lemma `hom_inv_h₁` / 引理 `hom_inv_h₁`

English:
lemma hom_inv_h₁
  given: {i j : E.I₀} (k : E.I₁ i j)
  proof: by
  obtain ⟨hs, _, _, hh⟩ := Hom.ext'_iff.mp e.hom_inv_id
  simpa using hh i j k

中文:
引理 hom_inv_h₁
  条件: {i j : E.I₀} (k : E.I₁ i j)
  证明: by
  obtain ⟨hs, _, _, hh⟩ := Hom.ext'_iff.mp e.hom_inv_id
  simpa using hh i j k

Depends on / 依赖: Hom.ext, _iff, _iff.mp, e.hom_inv_id, hom_inv_id
-/
lemma hom_inv_h₁ {i j : E.I₀} (k : E.I₁ i j) :
    e.hom.h₁ k ≫ e.inv.h₁ (e.hom.s₁ k) =
      (E.congrIndexOneOfEqIso (hom_inv_s₀_apply e i).symm (hom_inv_s₀_apply e j).symm k).inv ≫
      eqToHom (by congr 1; simp) := by
  obtain ⟨hs, _, _, hh⟩ := Hom.ext'_iff.mp e.hom_inv_id
  simpa using hh i j k

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/--
lemma `inv_hom_h₁` / 引理 `inv_hom_h₁`

English:
lemma inv_hom_h₁
  given: {i j : F.I₀} (k : F.I₁ i j)
  proof: by
  obtain ⟨hs, _, _, hh⟩ := Hom.ext'_iff.mp e.inv_hom_id
  simpa using hh i j k

中文:
引理 inv_hom_h₁
  条件: {i j : F.I₀} (k : F.I₁ i j)
  证明: by
  obtain ⟨hs, _, _, hh⟩ := Hom.ext'_iff.mp e.inv_hom_id
  simpa using hh i j k

Depends on / 依赖: Hom.ext, _iff, _iff.mp, e.inv_hom_id, inv_hom_id
-/
lemma inv_hom_h₁ {i j : F.I₀} (k : F.I₁ i j) :
    e.inv.h₁ k ≫ e.hom.h₁ (e.inv.s₁ k) =
      (F.congrIndexOneOfEqIso (inv_hom_s₀_apply e i).symm (inv_hom_s₀_apply e j).symm k).inv ≫
      eqToHom (by congr 1; simp) := by
  obtain ⟨hs, _, _, hh⟩ := Hom.ext'_iff.mp e.inv_hom_id
  simpa using hh i j k

set_option backward.isDefEq.respectTransparency.types false in
instance (i : E.I₀) : IsIso (e.hom.h₀ i) := by
  use e.inv.h₀ (e.hom.s₀ i) ≫ eqToHom (by simp)
  rw [PreOneHypercover.hom_inv_h₀_assoc]; rw [eqToHom_trans]; rw [eqToHom_refl]; rw [Category.assoc]; rw [← eqToHom_naturality _ (by simp)]; rw [PreOneHypercover.inv_hom_h₀_assoc]
  simp

set_option backward.isDefEq.respectTransparency.types false in
instance (i : F.I₀) : IsIso (e.inv.h₀ i) :=
  .of_isIso_fac_right (PreOneHypercover.inv_hom_h₀ e i)

set_option backward.isDefEq.respectTransparency.types false in
instance {i j : E.I₀} (k : E.I₁ i j) : IsIso (e.hom.h₁ k) := by
  use e.inv.h₁ _ ≫ eqToHom (by congr 1; simp) ≫ (E.congrIndexOneOfEqIso (by simp) (by simp) k).hom
  simp only [PreOneHypercover.hom_inv_h₁_assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
    Iso.inv_hom_id, Category.assoc, true_and, PreOneHypercover.congrIndexOneOfEqIso_hom_naturality]
  rw [← eqToHom_naturality_assoc _ (by simp)]
  simp

set_option backward.isDefEq.respectTransparency.types false in
instance {i j : F.I₀} (k : F.I₁ i j) : IsIso (e.inv.h₁ k) :=
  .of_isIso_fac_right (PreOneHypercover.inv_hom_h₁ e k)

end

section

set_option backward.isDefEq.respectTransparency.types false in
/-- A refinement morphism `E ⟶ F` induces a functor between the multifork indexing categories. -/
@[simps]
/--
Definition of `Hom.mapMulticospan` / `Hom.mapMulticospan` 的定义

English:
definition Hom.mapMulticospan
  signature: {E : PreOneHypercover.{w} S} {F : PreOneHypercover.{w'} S} (f : E.Hom F)

中文:
定义 Hom.mapMulticospan
  签名: {E : PreOneHypercover.{w} S} {F : PreOneHypercover.{w'} S} (f : E.Hom F)

Depends on / 依赖: F.multicospanShape, multicospanShape
-/
def Hom.mapMulticospan {E : PreOneHypercover.{w} S} {F : PreOneHypercover.{w'} S} (f : E.Hom F) :
    WalkingMulticospan E.multicospanShape ⥤ WalkingMulticospan F.multicospanShape where
  obj
    | .left i => .left (f.s₀ i)
    | .right i => .right (f.s₁' i)
  map
    | .id _ => .id _
    | .fst i => WalkingMulticospan.Hom.fst (J := F.multicospanShape) (f.s₁' i)
    | .snd i => WalkingMulticospan.Hom.snd (J := F.multicospanShape) (f.s₁' i)
  map_id
    | .left _ => rfl
    | .right _ => rfl
  map_comp
    | .id _, _ => by simp
    | .fst _, .id _ => by simp
    | .snd _, .id _ => by simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Isomorphic pre-`1`-hypercovers have equivalent multifork index categories. -/
@[simps! functor inverse]
/--
Definition of `equivalenceMulticospanOfIso` / `equivalenceMulticospanOfIso` 的定义

English:
definition equivalenceMulticospanOfIso
  signature: {E F : PreOneHypercover.{w} S} (f : E ≅ F)
  body: f.hom.mapMulticospan
  inverse := f.inv.mapMulticospan
  unitIso :=
    eqToIso (WalkingMulticospan.functor_ext (by simp)
      (fun _ => by dsimp; congr; apply PreOneHypercover.I₁'.ext <;> simp)
      (fun _ => by dsimp; rw [eqToHom_naturality]; apply PreOneHypercover.I₁'.ext <;> simp)
      (fun _

中文:
定义 equivalenceMulticospanOfIso
  签名: {E F : PreOneHypercover.{w} S} (f : E ≅ F)
  定义体: f.hom.mapMulticospan
  inverse := f.inv.mapMulticospan
  unitIso :=
    eqToIso (WalkingMulticospan.functor_ext (by simp)
      (fun _ => by dsimp; congr; apply PreOneHypercover.I₁'.ext <;> simp)
      (fun _ => by dsimp; rw [eqToHom_naturality]; apply PreOneHypercover.I₁'.ext <;> simp)
      (fun _

Depends on / 依赖: f.hom.mapMulticospan, mapMulticospan
-/
def equivalenceMulticospanOfIso {E F : PreOneHypercover.{w} S} (f : E ≅ F) :
    WalkingMulticospan E.multicospanShape ≌ WalkingMulticospan F.multicospanShape where
  functor := f.hom.mapMulticospan
  inverse := f.inv.mapMulticospan
  unitIso :=
    eqToIso (WalkingMulticospan.functor_ext (by simp)
      (fun _ => by dsimp; congr; apply PreOneHypercover.I₁'.ext <;> simp)
      (fun _ => by dsimp; rw [eqToHom_naturality]; apply PreOneHypercover.I₁'.ext <;> simp)
      (fun _ => by dsimp; rw [eqToHom_naturality]; apply PreOneHypercover.I₁'.ext <;> simp))
  counitIso :=
    eqToIso (WalkingMulticospan.functor_ext (by simp)
      (fun _ => by dsimp; congr 1; apply PreOneHypercover.I₁'.ext <;> simp)
      (fun _ => by dsimp; rw [eqToHom_naturality]; apply PreOneHypercover.I₁'.ext <;> simp)
      (fun _ => by dsimp; rw [eqToHom_naturality]; apply PreOneHypercover.I₁'.ext <;> simp))
  functor_unitIso_comp c := by
    cases c <;> rw [eqToIso.hom, eqToHom_app, eqToHom_map] <;> simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- If `E` and `F` are isomorphic pre-`1`-hypercovers and `G` is a presheaf,
the multifork for `E` is exact if and only if the multifork for `F` is exact. -/
noncomputable
/--
Definition of `isLimitEquivOfIso` / `isLimitEquivOfIso` 的定义

English:
definition isLimitEquivOfIso
  signature: {E F : PreOneHypercover.{w} S} (f : E ≅ F) (G : Cᵒᵖ ⥤ A)
  body: by
  refine Equiv.trans ?_
    (IsLimit.whiskerEquivalenceEquiv <| PreOneHypercover.equivalenceMulticospanOfIso f).symm
  refine IsLimit.equivOfNatIsoOfIso ?_ _ _ ?_
  · refine WalkingMulticospan.functorExt ?_ ?_ ?_ ?_
    · intro i
      exact G.mapIso (asIso (f.hom.h₀ i)).symm.op
    · intro i
   

中文:
定义 isLimitEquivOfIso
  签名: {E F : PreOneHypercover.{w} S} (f : E ≅ F) (G : Cᵒᵖ ⥤ A)
  定义体: by
  refine Equiv.trans ?_
    (IsLimit.whiskerEquivalenceEquiv <| PreOneHypercover.equivalenceMulticospanOfIso f).symm
  refine IsLimit.equivOfNatIsoOfIso ?_ _ _ ?_
  · refine WalkingMulticospan.functorExt ?_ ?_ ?_ ?_
    · intro i
      exact G.mapIso (asIso (f.hom.h₀ i)).symm.op
    · intro i
   

Depends on / 依赖: Cone.ext, Equiv.trans, Functor, Functor.map_comp, Functor.map_comp_assoc, G.mapIso, IsLimit, IsLimit.equivOfNatIsoOfIso, IsLimit.whiskerEquivalenceEquiv, Iso.refl, PreOneHypercover, PreOneHypercover.equivalenceMulticospanOfIso, WalkingMulticospan, WalkingMulticospan.functorExt, equivOfNatIsoOfIso, equivalenceMulticospanOfIso, f.hom.h, f.hom.w, functorExt, mapIso
-/
def isLimitEquivOfIso {E F : PreOneHypercover.{w} S} (f : E ≅ F) (G : Cᵒᵖ ⥤ A) :
    IsLimit (E.multifork G) ≃ IsLimit (F.multifork G) := by
  refine Equiv.trans ?_
    (IsLimit.whiskerEquivalenceEquiv <| PreOneHypercover.equivalenceMulticospanOfIso f).symm
  refine IsLimit.equivOfNatIsoOfIso ?_ _ _ ?_
  · refine WalkingMulticospan.functorExt ?_ ?_ ?_ ?_
    · intro i
      exact G.mapIso (asIso (f.hom.h₀ i)).symm.op
    · intro i
      exact G.mapIso (asIso (f.hom.h₁ i.2)).symm.op
    · simp [← Functor.map_comp_assoc, ← Functor.map_comp, ← op_comp, f.hom.w₁₁]
    · simp [← Functor.map_comp_assoc, ← Functor.map_comp, ← op_comp, f.hom.w₁₂]
  · refine Cone.ext (Iso.refl _) fun i => ?_
    induction i with
    | left _ => simp [← Functor.map_comp, ← op_comp]
    | right _ => simp [← Functor.map_comp, ← op_comp, f.hom.w₁₁_assoc]

end

end Category

section

variable (F : PreOneHypercover.{w'} S) {G : PreOneHypercover.{w''} S}
  [forall (i : E.I₀) (j : F.I₀), HasPullback (E.f i) (F.f j)]
  [forall (i j : E.I₀) (k : E.I₁ i j) (a b : F.I₀) (l : F.I₁ a b),
    HasPullback (E.p₁ k ≫ E.f i) (F.p₁ l ≫ F.f a)]

set_option backward.isDefEq.respectTransparency false in
/-- First projection from the intersection of two pre-`1`-hypercovers. -/
@[simps toHom s₁]
noncomputable
/--
Definition of `interFst` / `interFst` 的定义

English:
definition interFst
  signature: : (E.inter F).Hom E where
  body: E.toPreZeroHypercover.interFst F.toPreZeroHypercover
  s₁ {i j} k := k.1
  h₁ _ := pullback.fst _ _

中文:
定义 interFst
  签名: : (E.inter F).Hom E where
  定义体: E.toPreZeroHypercover.interFst F.toPreZeroHypercover
  s₁ {i j} k := k.1
  h₁ _ := pullback.fst _ _

Depends on / 依赖: E.toPreZeroHypercover.interFst, F.toPreZeroHypercover, interFst, toPreZeroHypercover
-/
def interFst : (E.inter F).Hom E where
  __ := E.toPreZeroHypercover.interFst F.toPreZeroHypercover
  s₁ {i j} k := k.1
  h₁ _ := pullback.fst _ _

set_option backward.isDefEq.respectTransparency false in
/-- Second projection from the intersection of two pre-`1`-hypercovers. -/
@[simps toHom s₁]
noncomputable
/--
Definition of `interSnd` / `interSnd` 的定义

English:
definition interSnd
  signature: : (E.inter F).Hom F where
  body: E.toPreZeroHypercover.interSnd F.toPreZeroHypercover
  s₁ {i j} k := k.2
  h₁ _ := pullback.snd _ _

中文:
定义 interSnd
  签名: : (E.inter F).Hom F where
  定义体: E.toPreZeroHypercover.interSnd F.toPreZeroHypercover
  s₁ {i j} k := k.2
  h₁ _ := pullback.snd _ _

Depends on / 依赖: E.toPreZeroHypercover.interSnd, F.toPreZeroHypercover, interSnd, toPreZeroHypercover
-/
def interSnd : (E.inter F).Hom F where
  __ := E.toPreZeroHypercover.interSnd F.toPreZeroHypercover
  s₁ {i j} k := k.2
  h₁ _ := pullback.snd _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
variable {E F} in
/-- Universal property of the intersection of two pre-`1`-hypercovers. -/
noncomputable
/--
Definition of `interLift` / `interLift` 的定义

English:
definition interLift
  signature: {G : PreOneHypercover.{w''} S} (f : G.Hom E) (g : G.Hom F)
  body: PreZeroHypercover.interLift f.toHom g.toHom
  s₁ {i j} k := ⟨f.s₁ k, g.s₁ k⟩
h₁ k := pullback.lift (f.h₁ k) (g.h₁ k) by
    rw [f.w₁₁_assoc k]; rw [g.w₁₁_assoc k]
    simp
  w₀ := by simp
  w₁₁ k := by
    apply pullback.hom_ext
    · simpa using f.w₁₁ k
    · simpa using g.w₁₁ k
  w₁₂ k := by
    a

中文:
定义 interLift
  签名: {G : PreOneHypercover.{w''} S} (f : G.Hom E) (g : G.Hom F)
  定义体: PreZeroHypercover.interLift f.toHom g.toHom
  s₁ {i j} k := ⟨f.s₁ k, g.s₁ k⟩
h₁ k := pullback.lift (f.h₁ k) (g.h₁ k) by
    rw [f.w₁₁_assoc k]; rw [g.w₁₁_assoc k]
    simp
  w₀ := by simp
  w₁₁ k := by
    apply pullback.hom_ext
    · simpa using f.w₁₁ k
    · simpa using g.w₁₁ k
  w₁₂ k := by
    a

Depends on / 依赖: PreZeroHypercover, PreZeroHypercover.interLift, f.toHom, g.toHom, interLift
-/
def interLift {G : PreOneHypercover.{w''} S} (f : G.Hom E) (g : G.Hom F) :
    G.Hom (E.inter F) where
  __ := PreZeroHypercover.interLift f.toHom g.toHom
  s₁ {i j} k := ⟨f.s₁ k, g.s₁ k⟩
h₁ k := pullback.lift (f.h₁ k) (g.h₁ k) by
    rw [f.w₁₁_assoc k]; rw [g.w₁₁_assoc k]
    simp
  w₀ := by simp
  w₁₁ k := by
    apply pullback.hom_ext
    · simpa using f.w₁₁ k
    · simpa using g.w₁₁ k
  w₁₂ k := by
    apply pullback.hom_ext
    · simpa using f.w₁₂ k
    · simpa using g.w₁₂ k

end

end PreOneHypercover

namespace GrothendieckTopology

variable (J : GrothendieckTopology C)

/--
Definition of `OneHypercover` / `OneHypercover` 的定义

English:
structure OneHypercover
  parameters: (S : C)
  extends: PreOneHypercover.{w} S
  axioms and operations (2):
    - mem₀ : toPreOneHypercover.sieve₀ in J S
    - mem₁((i₁ i₂ : I₀) ⦃W) : C⦄ (p₁ : W ⟶ X i₁) (p₂ : W ⟶ X i₂) (w : p₁ ≫ f i₁ = p₂ ≫ f i₂) : toPreOneHypercover.sieve₁ p₁ p₂ in J W

中文:
结构 OneHypercover
  参数: (S : C)
  继承: PreOneHypercover.{w} S
  公理与运算 (2 个):
    - mem₀ : toPreOneHypercover.sieve₀ in J S
    - mem₁((i₁ i₂ : I₀) ⦃W) : C⦄ (p₁ : W ⟶ X i₁) (p₂ : W ⟶ X i₂) (w : p₁ ≫ f i₁ = p₂ ≫ f i₂) : toPreOneHypercover.sieve₁ p₁ p₂ in J W
-/
structure OneHypercover (S : C) extends PreOneHypercover.{w} S where
  mem₀ : toPreOneHypercover.sieve₀ in J S
  mem₁ (i₁ i₂ : I₀) ⦃W : C⦄ (p₁ : W ⟶ X i₁) (p₂ : W ⟶ X i₂) (w : p₁ ≫ f i₁ = p₂ ≫ f i₂) :
    toPreOneHypercover.sieve₁ p₁ p₂ in J W

variable {J}

/--
lemma `OneHypercover.mem_sieve₁'` / 引理 `OneHypercover.mem_sieve₁'`

English:
lemma OneHypercover.mem_sieve₁'
  statement: {S : C} (E : J.OneHypercover S)
  proof: by
  rw [E.sieve₁'_eq_sieve₁]
  exact mem₁ _ _ _ _ _ pullback.condition

中文:
引理 OneHypercover.mem_sieve₁'
  结论: {S : C} (E : J.OneHypercover S)
  证明: by
  rw [E.sieve₁'_eq_sieve₁]
  exact mem₁ _ _ _ _ _ pullback.condition

Depends on / 依赖: E.sieve, condition, pullback, pullback.condition
-/
lemma OneHypercover.mem_sieve₁' {S : C} (E : J.OneHypercover S)
    (i₁ i₂ : E.I₀) [HasPullback (E.f i₁) (E.f i₂)] :
    E.sieve₁' i₁ i₂ in J _ := by
  rw [E.sieve₁'_eq_sieve₁]
  exact mem₁ _ _ _ _ _ pullback.condition

namespace OneHypercover

/-- In order to check that a certain data is a `1`-hypercover of `S`, it suffices to
check that the data provides a covering of `S` and of the fibre products. -/
@[simps toPreOneHypercover]
/--
Definition of `mk'` / `mk'` 的定义

English:
definition mk'
  signature: {S : C} (E : PreOneHypercover S) [E.HasPullbacks]
  body: E
  mem₀ := mem₀
  mem₁ i₁ i₂ W p₁ p₂ w := by
    rw [E.sieve₁_eq_pullback_sieve₁' _ _ w]
    exact J.pullback_stable' _ (mem₁' i₁ i₂)

中文:
定义 mk'
  签名: {S : C} (E : PreOneHypercover S) [E.HasPullbacks]
  定义体: E
  mem₀ := mem₀
  mem₁ i₁ i₂ W p₁ p₂ w := by
    rw [E.sieve₁_eq_pullback_sieve₁' _ _ w]
    exact J.pullback_stable' _ (mem₁' i₁ i₂)
-/
def mk' {S : C} (E : PreOneHypercover S) [E.HasPullbacks]
    (mem₀ : E.sieve₀ in J S) (mem₁' : forall (i₁ i₂ : E.I₀), E.sieve₁' i₁ i₂ in J _) :
    J.OneHypercover S where
  toPreOneHypercover := E
  mem₀ := mem₀
  mem₁ i₁ i₂ W p₁ p₂ w := by
    rw [E.sieve₁_eq_pullback_sieve₁' _ _ w]
    exact J.pullback_stable' _ (mem₁' i₁ i₂)

section

variable {S : C} (E : J.OneHypercover S) (F : Sheaf J A)

section

variable {E F}
variable (c : Multifork (E.multicospanIndex F.obj))

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `multiforkLift` / `multiforkLift` 的定义

English:
definition multiforkLift
  signature: : c.pt ⟶ F.obj.obj (Opposite.op S)
  body: F.property.amalgamateOfArrows _ E.mem₀ c.ι (fun W i₁ i₂ p₁ p₂ w => by
    apply F.property.hom_ext ⟨_, E.mem₁ _ _ _ _ w⟩
    rintro ⟨T, g, j, h, fac₁, fac₂⟩
    dsimp
    simp only [assoc, ← Functor.map_comp, ← op_comp, fac₁, fac₂]
    simp only [op_comp, Functor.map_comp]
    simpa using! c.conditi

中文:
定义 multiforkLift
  签名: : c.pt ⟶ F.obj.obj (Opposite.op S)
  定义体: F.property.amalgamateOfArrows _ E.mem₀ c.ι (fun W i₁ i₂ p₁ p₂ w => by
    apply F.property.hom_ext ⟨_, E.mem₁ _ _ _ _ w⟩
    rintro ⟨T, g, j, h, fac₁, fac₂⟩
    dsimp
    simp only [assoc, ← Functor.map_comp, ← op_comp, fac₁, fac₂]
    simp only [op_comp, Functor.map_comp]
    simpa using! c.conditi

Depends on / 依赖: E.mem, F.obj.map, F.property.amalgamateOfArrows, F.property.hom_ext, Functor, Functor.map_comp, amalgamateOfArrows, c.condition, condition, h.op, hom_ext, map_comp, op_comp, property
-/
noncomputable def multiforkLift : c.pt ⟶ F.obj.obj (Opposite.op S) :=
  F.property.amalgamateOfArrows _ E.mem₀ c.ι (fun W i₁ i₂ p₁ p₂ w => by
    apply F.property.hom_ext ⟨_, E.mem₁ _ _ _ _ w⟩
    rintro ⟨T, g, j, h, fac₁, fac₂⟩
    dsimp
    simp only [assoc, ← Functor.map_comp, ← op_comp, fac₁, fac₂]
    simp only [op_comp, Functor.map_comp]
    simpa using! c.condition ⟨⟨i₁, i₂⟩, j⟩ =≫ F.obj.map h.op)

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
/--
lemma `multiforkLift_map` / 引理 `multiforkLift_map`

English:
lemma multiforkLift_map
  given: (i₀ : E.I₀)
  statement: multiforkLift c ≫ F.obj.map (E.f i₀).op = c.ι i₀
  proof: by
  simp [multiforkLift]

中文:
引理 multiforkLift_map
  条件: (i₀ : E.I₀)
  结论: multiforkLift c ≫ F.obj.map (E.f i₀).op = c.ι i₀
  证明: by
  simp [multiforkLift]

Depends on / 依赖: multiforkLift
-/
lemma multiforkLift_map (i₀ : E.I₀) : multiforkLift c ≫ F.obj.map (E.f i₀).op = c.ι i₀ := by
  simp [multiforkLift]

end

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `isLimitMultifork` / `isLimitMultifork` 的定义

English:
definition isLimitMultifork
  signature: : IsLimit (E.multifork F.1)
  body: Multifork.IsLimit.mk _ (fun c => multiforkLift c) (fun c => multiforkLift_map c) (by
    intro c m hm
    apply F.property.hom_ext_ofArrows _ E.mem₀
    intro i₀
    rw [multiforkLift_map]
    exact hm i₀)

中文:
定义 isLimitMultifork
  签名: : IsLimit (E.multifork F.1)
  定义体: Multifork.IsLimit.mk _ (fun c => multiforkLift c) (fun c => multiforkLift_map c) (by
    intro c m hm
    apply F.property.hom_ext_ofArrows _ E.mem₀
    intro i₀
    rw [multiforkLift_map]
    exact hm i₀)

Depends on / 依赖: E.mem, F.property.hom_ext_ofArrows, IsLimit, Multifork, Multifork.IsLimit.mk, hom_ext_ofArrows, multiforkLift, multiforkLift_map, property
-/
noncomputable def isLimitMultifork : IsLimit (E.multifork F.1) :=
  Multifork.IsLimit.mk _ (fun c => multiforkLift c) (fun c => multiforkLift_map c) (by
    intro c m hm
    apply F.property.hom_ext_ofArrows _ E.mem₀
    intro i₀
    rw [multiforkLift_map]
    exact hm i₀)

end

section

variable {S : C}

/-- Forget the `1`-components of a `OneHypercover`. -/
@[simps toPreZeroHypercover]
/--
Definition of `toZeroHypercover` / `toZeroHypercover` 的定义

English:
definition toZeroHypercover
  signature: (E : OneHypercover.{w} J S)
  body: E.toPreZeroHypercover
  mem₀ := E.mem₀

中文:
定义 toZeroHypercover
  签名: (E : OneHypercover.{w} J S)
  定义体: E.toPreZeroHypercover
  mem₀ := E.mem₀

Depends on / 依赖: E.toPreZeroHypercover, toPreZeroHypercover
-/
def toZeroHypercover (E : OneHypercover.{w} J S) : J.toPrecoverage.ZeroHypercover S where
  __ := E.toPreZeroHypercover
  mem₀ := E.mem₀

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
variable (J) in
/-- The trivial `1`-hypercover of `S` where a single component `S`. -/
@[simps toPreOneHypercover]
/--
Definition of `trivial` / `trivial` 的定义

English:
definition trivial
  signature: (S : C)
  body: PreOneHypercover.trivial S
  mem₀ := by simp only [PreOneHypercover.sieve₀_trivial, J.top_mem]
  mem₁ _ _ _ _ _ h := by
    simp only [PreOneHypercover.trivial_toPreZeroHypercover, PreZeroHypercover.singleton_X,
      PreZeroHypercover.singleton_f, Category.comp_id] at h
    subst h
    simp

中文:
定义 trivial
  签名: (S : C)
  定义体: PreOneHypercover.trivial S
  mem₀ := by simp only [PreOneHypercover.sieve₀_trivial, J.top_mem]
  mem₁ _ _ _ _ _ h := by
    simp only [PreOneHypercover.trivial_toPreZeroHypercover, PreZeroHypercover.singleton_X,
      PreZeroHypercover.singleton_f, Category.comp_id] at h
    subst h
    simp

Depends on / 依赖: PreOneHypercover, PreOneHypercover.trivial
-/
def trivial (S : C) : OneHypercover.{w} J S where
  __ := PreOneHypercover.trivial S
  mem₀ := by simp only [PreOneHypercover.sieve₀_trivial, J.top_mem]
  mem₁ _ _ _ _ _ h := by
    simp only [PreOneHypercover.trivial_toPreZeroHypercover, PreZeroHypercover.singleton_X,
      PreZeroHypercover.singleton_f, Category.comp_id] at h
    subst h
    simp

instance (S : C) : Nonempty (J.OneHypercover S) := ⟨trivial J S⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- Intersection of two `1`-hypercovers. -/
@[simps toPreOneHypercover]
noncomputable
/--
Definition of `inter` / `inter` 的定义

English:
definition inter
  signature: [HasPullbacks C] (E F : J.OneHypercover S)
  body: E.toPreOneHypercover.inter F.toPreOneHypercover
  mem₀ := (E.toZeroHypercover.inter F.toZeroHypercover).mem₀
  mem₁ i₁ i₂ W p₁ p₂ h := by
    rw [PreOneHypercover.sieve₁_inter h]
    refine J.bind_covering (E.mem₁ _ _ _ _ (by simpa using! h)) fun _ _ _ => ?_
    exact J.pullback_stable _
      (F.me

中文:
定义 inter
  签名: [HasPullbacks C] (E F : J.OneHypercover S)
  定义体: E.toPreOneHypercover.inter F.toPreOneHypercover
  mem₀ := (E.toZeroHypercover.inter F.toZeroHypercover).mem₀
  mem₁ i₁ i₂ W p₁ p₂ h := by
    rw [PreOneHypercover.sieve₁_inter h]
    refine J.bind_covering (E.mem₁ _ _ _ _ (by simpa using! h)) fun _ _ _ => ?_
    exact J.pullback_stable _
      (F.me

Depends on / 依赖: E.toPreOneHypercover.inter, F.toPreOneHypercover, toPreOneHypercover
-/
def inter [HasPullbacks C] (E F : J.OneHypercover S)
    [forall (i : E.I₀) (j : F.I₀), HasPullback (E.f i) (F.f j)]
    [forall (i j : E.I₀) (k : E.I₁ i j) (a b : F.I₀) (l : F.I₁ a b),
      HasPullback (E.p₁ k ≫ E.f i) (F.p₁ l ≫ F.f a)] : J.OneHypercover S where
  __ := E.toPreOneHypercover.inter F.toPreOneHypercover
  mem₀ := (E.toZeroHypercover.inter F.toZeroHypercover).mem₀
  mem₁ i₁ i₂ W p₁ p₂ h := by
    rw [PreOneHypercover.sieve₁_inter h]
    refine J.bind_covering (E.mem₁ _ _ _ _ (by simpa using! h)) fun _ _ _ => ?_
    exact J.pullback_stable _
      (F.mem₁ _ _ _ _ (by simpa [Category.assoc, ← pullback.condition]))

end

section Category

variable {S : C} {E : OneHypercover.{w} J S} {F : OneHypercover.{w'} J S}

/--
Definition of `Hom` / `Hom` 的定义

English:
abbreviation Hom
  signature: (E : OneHypercover.{w} J S) (F : OneHypercover.{w'} J S)
  body: E.toPreOneHypercover.Hom F.toPreOneHypercover

中文:
缩写 Hom
  签名: (E : OneHypercover.{w} J S) (F : OneHypercover.{w'} J S)
  定义体: E.toPreOneHypercover.Hom F.toPreOneHypercover

Depends on / 依赖: E.toPreOneHypercover.Hom, F.toPreOneHypercover, toPreOneHypercover
-/
abbrev Hom (E : OneHypercover.{w} J S) (F : OneHypercover.{w'} J S) :=
  E.toPreOneHypercover.Hom F.toPreOneHypercover

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simps! id_s₀ id_s₁ id_h₀ id_h₁ comp_s₀ comp_s₁ comp_h₀ comp_h₁]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category (J.OneHypercover S)
  body: Hom
  id E := PreOneHypercover.Hom.id E.toPreOneHypercover
  comp f g := f.comp g

中文:
实例 :
  签名: Category (J.OneHypercover S)
  定义体: Hom
  id E := PreOneHypercover.Hom.id E.toPreOneHypercover
  comp f g := f.comp g
-/
instance : Category (J.OneHypercover S) where
  Hom := Hom
  id E := PreOneHypercover.Hom.id E.toPreOneHypercover
  comp f g := f.comp g

set_option backward.isDefEq.respectTransparency.types false in
/-- An isomorphism of `1`-hypercovers is an isomorphism of pre-`1`-hypercovers. -/
@[simps]
/--
Definition of `isoMk` / `isoMk` 的定义

English:
definition isoMk
  signature: {E F : J.OneHypercover S} (f : E.toPreOneHypercover ≅ F.toPreOneHypercover)
  body: f

中文:
定义 isoMk
  签名: {E F : J.OneHypercover S} (f : E.toPreOneHypercover ≅ F.toPreOneHypercover)
  定义体: f
-/
def isoMk {E F : J.OneHypercover S} (f : E.toPreOneHypercover ≅ F.toPreOneHypercover) :
    E ≅ F where
  __ := f

end Category

end OneHypercover

namespace Cover

variable {X : C} (S : J.Cover X)

/-- The tautological 1-pre-hypercover induced by `S : J.Cover X`. Its index type `I₀`
is given by `S.Arrow` (i.e. all the morphisms in the sieve `S`), while `I₁` is given
by all possible pullback cones. -/
@[simps]
/--
Definition of `preOneHypercover` / `preOneHypercover` 的定义

English:
definition preOneHypercover
  signature: : PreOneHypercover.{max u v} X where
  body: S.Arrow
  X f := f.Y
  f f := f.f
  I₁ f₁ f₂ := f₁.Relation f₂
  Y _ _ r := r.Z
  p₁ _ _ r := r.g₁
  p₂ _ _ r := r.g₂
  w _ _ r := r.w

@[simp]

中文:
定义 preOneHypercover
  签名: : PreOneHypercover.{max u v} X where
  定义体: S.Arrow
  X f := f.Y
  f f := f.f
  I₁ f₁ f₂ := f₁.Relation f₂
  Y _ _ r := r.Z
  p₁ _ _ r := r.g₁
  p₂ _ _ r := r.g₂
  w _ _ r := r.w

@[simp]

Depends on / 依赖: S.Arrow
-/
def preOneHypercover : PreOneHypercover.{max u v} X where
  I₀ := S.Arrow
  X f := f.Y
  f f := f.f
  I₁ f₁ f₂ := f₁.Relation f₂
  Y _ _ r := r.Z
  p₁ _ _ r := r.g₁
  p₂ _ _ r := r.g₂
  w _ _ r := r.w

@[simp]
/--
lemma `preOneHypercover_sieve₀` / 引理 `preOneHypercover_sieve₀`

English:
lemma preOneHypercover_sieve₀
  statement: S.preOneHypercover.sieve₀ = S.1
  proof: by
  ext Y f
  constructor
  · rintro ⟨_, _, _, ⟨g⟩, rfl⟩
    exact S.1.downward_closed g.hf _
  · intro hf
    exact Sieve.ofArrows_mk _ _ ({ hf := hf, .. } : S.Arrow)

中文:
引理 preOneHypercover_sieve₀
  结论: S.preOneHypercover.sieve₀ = S.1
  证明: by
  ext Y f
  constructor
  · rintro ⟨_, _, _, ⟨g⟩, rfl⟩
    exact S.1.downward_closed g.hf _
  · intro hf
    exact Sieve.ofArrows_mk _ _ ({ hf := hf, .. } : S.Arrow)

Depends on / 依赖: S.Arrow, Sieve.ofArrows_mk, downward_closed, g.hf, ofArrows_mk
-/
lemma preOneHypercover_sieve₀ : S.preOneHypercover.sieve₀ = S.1 := by
  ext Y f
  constructor
  · rintro ⟨_, _, _, ⟨g⟩, rfl⟩
    exact S.1.downward_closed g.hf _
  · intro hf
    exact Sieve.ofArrows_mk _ _ ({ hf := hf, .. } : S.Arrow)

/--
lemma `preOneHypercover_sieve₁` / 引理 `preOneHypercover_sieve₁`

English:
lemma preOneHypercover_sieve₁
  statement: (f₁ f₂ : S.Arrow) {W : C} (p₁ : W ⟶ f₁.Y) (p₂ : W ⟶ f₂.Y)
  proof: by
  ext Y f
  simp only [Sieve.top_apply, iff_true]
  exact ⟨{ w := w, .. }, f, rfl, rfl⟩

中文:
引理 preOneHypercover_sieve₁
  结论: (f₁ f₂ : S.Arrow) {W : C} (p₁ : W ⟶ f₁.Y) (p₂ : W ⟶ f₂.Y)
  证明: by
  ext Y f
  simp only [Sieve.top_apply, iff_true]
  exact ⟨{ w := w, .. }, f, rfl, rfl⟩

Depends on / 依赖: Sieve.top_apply, iff_true, top_apply
-/
lemma preOneHypercover_sieve₁ (f₁ f₂ : S.Arrow) {W : C} (p₁ : W ⟶ f₁.Y) (p₂ : W ⟶ f₂.Y)
    (w : p₁ ≫ f₁.f = p₂ ≫ f₂.f) :
    S.preOneHypercover.sieve₁ p₁ p₂ = ⊤ := by
  ext Y f
  simp only [Sieve.top_apply, iff_true]
  exact ⟨{ w := w, .. }, f, rfl, rfl⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- The tautological 1-hypercover induced by `S : J.Cover X`. Its index type `I₀`
is given by `S.Arrow` (i.e. all the morphisms in the sieve `S`), while `I₁` is given
by all possible pullback cones. -/
@[simps toPreOneHypercover]
/--
Definition of `oneHypercover` / `oneHypercover` 的定义

English:
definition oneHypercover
  signature: : J.OneHypercover X where
  body: S.preOneHypercover
  mem₀ := by simp
  mem₁ f₁ f₂ _ p₁ p₂ w := by simp [S.preOneHypercover_sieve₁ f₁ f₂ p₁ p₂ w]

中文:
定义 oneHypercover
  签名: : J.OneHypercover X where
  定义体: S.preOneHypercover
  mem₀ := by simp
  mem₁ f₁ f₂ _ p₁ p₂ w := by simp [S.preOneHypercover_sieve₁ f₁ f₂ p₁ p₂ w]

Depends on / 依赖: S.preOneHypercover, preOneHypercover
-/
def oneHypercover : J.OneHypercover X where
  toPreOneHypercover := S.preOneHypercover
  mem₀ := by simp
  mem₁ f₁ f₂ _ p₁ p₂ w := by simp [S.preOneHypercover_sieve₁ f₁ f₂ p₁ p₂ w]

end Cover

end GrothendieckTopology

/--
lemma `PreZeroHypercover.ext_of_isSeparatedFor` / 引理 `PreZeroHypercover.ext_of_isSeparatedFor`

English:
lemma PreZeroHypercover.ext_of_isSeparatedFor
  statement: {P : Cᵒᵖ ⥤ Type*} {S : C} (E : PreZeroHypercover S)
  proof: h.ext fun _ _ ⟨i⟩ => hi i

中文:
引理 PreZeroHypercover.ext_of_isSeparatedFor
  结论: {P : Cᵒᵖ ⥤ 类型} {S : C} (E : PreZeroHypercover S)
  证明: h.ext fun _ _ ⟨i⟩ => hi i

Depends on / 依赖: h.ext
-/
lemma PreZeroHypercover.ext_of_isSeparatedFor {P : Cᵒᵖ ⥤ Type*} {S : C} (E : PreZeroHypercover S)
    (h : E.presieve₀.IsSeparatedFor P) {x y : P.obj (.op S)}
    (hi : forall i, P.map (E.f i).op x = P.map (E.f i).op y) :
    x = y :=
  h.ext fun _ _ ⟨i⟩ => hi i

/-- If the pairwise pullbacks exist, this is the pre-`1`-hypercover where the covers
by the pullbacks are given by the pullbacks themselves. -/
@[simps toPreZeroHypercover I₁ Y p₁ p₂]
/--
Definition of `PreZeroHypercover.toPreOneHypercover` / `PreZeroHypercover.toPreOneHypercover` 的定义

English:
definition PreZeroHypercover.toPreOneHypercover
  signature: {S : C} (E : PreZeroHypercover S)
  body: E
  I₁ _ _ := PUnit
  Y i j _ := pullback (E.f i) (E.f j)
  p₁ _ _ _ := pullback.fst _ _
  p₂ _ _ _ := pullback.snd _ _
  w _ _ _ := pullback.condition

中文:
定义 PreZeroHypercover.toPreOneHypercover
  签名: {S : C} (E : PreZeroHypercover S)
  定义体: E
  I₁ _ _ := PUnit
  Y i j _ := pullback (E.f i) (E.f j)
  p₁ _ _ _ := pullback.fst _ _
  p₂ _ _ _ := pullback.snd _ _
  w _ _ _ := pullback.condition
-/
noncomputable def PreZeroHypercover.toPreOneHypercover {S : C} (E : PreZeroHypercover S)
    [E.HasPullbacks] :
    PreOneHypercover S where
  __ := E
  I₁ _ _ := PUnit
  Y i j _ := pullback (E.f i) (E.f j)
  p₁ _ _ _ := pullback.fst _ _
  p₂ _ _ _ := pullback.snd _ _
  w _ _ _ := pullback.condition

set_option backward.defeqAttrib.useBackward true in
instance {S : C} (E : PreZeroHypercover S) [E.HasPullbacks] :
    E.toPreOneHypercover.HasPullbacks := by
  dsimp
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
lemma `sieve₁'_toPreOneHypercover_eq_top` / 引理 `sieve₁'_toPreOneHypercover_eq_top`

English:
lemma sieve₁'_toPreOneHypercover_eq_top
  statement: {S : C} (E : PreZeroHypercover S) [E.HasPullbacks]
  proof: by
  rw [eq_top_iff]
  intro Y f _
  refine ⟨pullback (E.f i) (E.f j), f, 𝟙 _, ?_, by simp⟩
  refine Presieve.ofArrows.mk' ⟨⟩ rfl ?_
  apply pullback.hom_ext <;> simp [PreOneHypercover.toPullback]

中文:
引理 sieve₁'_toPreOneHypercover_eq_top
  结论: {S : C} (E : PreZeroHypercover S) [E.HasPullbacks]
  证明: by
  rw [eq_top_iff]
  intro Y f _
  refine ⟨pullback (E.f i) (E.f j), f, 𝟙 _, ?_, by simp⟩
  refine Presieve.ofArrows.mk' ⟨⟩ rfl ?_
  apply pullback.hom_ext <;> simp [PreOneHypercover.toPullback]

Depends on / 依赖: PreOneHypercover, PreOneHypercover.toPullback, Presieve, Presieve.ofArrows.mk, eq_top_iff, hom_ext, ofArrows, pullback, pullback.hom_ext, toPullback
-/
lemma sieve₁'_toPreOneHypercover_eq_top {S : C} (E : PreZeroHypercover S) [E.HasPullbacks]
    (i j : E.I₀) :
    E.toPreOneHypercover.sieve₁' i j = ⊤ := by
  rw [eq_top_iff]
  intro Y f _
  refine ⟨pullback (E.f i) (E.f j), f, 𝟙 _, ?_, by simp⟩
  refine Presieve.ofArrows.mk' ⟨⟩ rfl ?_
  apply pullback.hom_ext <;> simp [PreOneHypercover.toPullback]

set_option backward.isDefEq.respectTransparency.types false in
/-- If the pairwise pullbacks exist, this is the pre-`1`-hypercover where the covers
by the pullbacks are given by the pullbacks themselves. -/
@[simps! toPreOneHypercover]
/--
Definition of `Precoverage.ZeroHypercover.toOneHypercover` / `Precoverage.ZeroHypercover.toOneHypercover` 的定义

English:
definition Precoverage.ZeroHypercover.toOneHypercover
  signature: {J : Precoverage C}
  body: .mk' E.toPreZeroHypercover.toPreOneHypercover (J.generate_mem_toGrothendieck E.mem₀) (by simp)

中文:
定义 Precoverage.ZeroHypercover.toOneHypercover
  签名: {J : Precoverage C}
  定义体: .mk' E.toPreZeroHypercover.toPreOneHypercover (J.generate_mem_toGrothendieck E.mem₀) (by simp)

Depends on / 依赖: E.mem, E.toPreZeroHypercover.toPreOneHypercover, J.generate_mem_toGrothendieck, generate_mem_toGrothendieck, toPreOneHypercover, toPreZeroHypercover
-/
noncomputable def Precoverage.ZeroHypercover.toOneHypercover {J : Precoverage C}
    {S : C} (E : J.ZeroHypercover S) [E.HasPullbacks] :
    (J.toGrothendieck).OneHypercover S :=
  .mk' E.toPreZeroHypercover.toPreOneHypercover (J.generate_mem_toGrothendieck E.mem₀) (by simp)

section

/-- Refine a pre-`0`-hypercover by `0`-hypercovers of the pairwise pullbacks. -/
@[simps toPreZeroHypercover I₁ Y p₁ p₂]
noncomputable
/--
Definition of `PreZeroHypercover.refineOneHypercover` / `PreZeroHypercover.refineOneHypercover` 的定义

English:
definition PreZeroHypercover.refineOneHypercover
  signature: {X : C} (E : PreZeroHypercover.{w} X) [E.HasPullbacks]
  body: E
  I₁ i j := (F i j).I₀
  Y i j k := (F i j).X k
  p₁ i j k := (F i j).f k ≫ pullback.fst _ _
  p₂ i j k := (F i j).f k ≫ pullback.snd _ _
  w i j k := by simp [pullback.condition]

中文:
定义 PreZeroHypercover.refineOneHypercover
  签名: {X : C} (E : PreZeroHypercover.{w} X) [E.HasPullbacks]
  定义体: E
  I₁ i j := (F i j).I₀
  Y i j k := (F i j).X k
  p₁ i j k := (F i j).f k ≫ pullback.fst _ _
  p₂ i j k := (F i j).f k ≫ pullback.snd _ _
  w i j k := by simp [pullback.condition]
-/
def PreZeroHypercover.refineOneHypercover {X : C} (E : PreZeroHypercover.{w} X) [E.HasPullbacks]
    (F : forall i j, PreZeroHypercover.{w} (pullback (E.f i) (E.f j))) :
    PreOneHypercover.{w} X where
  __ := E
  I₁ i j := (F i j).I₀
  Y i j k := (F i j).X k
  p₁ i j k := (F i j).f k ≫ pullback.fst _ _
  p₂ i j k := (F i j).f k ≫ pullback.snd _ _
  w i j k := by simp [pullback.condition]

variable {X : C} (E : PreZeroHypercover.{w} X) [E.HasPullbacks]
  (F : forall i j, PreZeroHypercover.{w} (pullback (E.f i) (E.f j)))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (E.refineOneHypercover F).HasPullbacks
  body: ‹_›

中文:
实例 :
  签名: (E.refineOneHypercover F).HasPullbacks
  定义体: ‹_›

Depends on / 依赖: Finset, Finset.univ.map, SimpleGraph, SimpleGraph.mk
-/
instance : (E.refineOneHypercover F).HasPullbacks := ‹_›

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `PreZeroHypercover.sieve₁'_refineOneHypercover` / 引理 `PreZeroHypercover.sieve₁'_refineOneHypercover`

English:
lemma PreZeroHypercover.sieve₁'_refineOneHypercover
  given: (i j : E.I₀)
  proof: by
  rw [PreOneHypercover.sieve₁']
  congr
  ext <;> simp [PreOneHypercover.toPullback]

中文:
引理 PreZeroHypercover.sieve₁'_refineOneHypercover
  条件: (i j : E.I₀)
  证明: by
  rw [PreOneHypercover.sieve₁']
  congr
  ext <;> simp [PreOneHypercover.toPullback]

Depends on / 依赖: PreOneHypercover, PreOneHypercover.sieve, PreOneHypercover.toPullback, toPullback
-/
lemma PreZeroHypercover.sieve₁'_refineOneHypercover (i j : E.I₀) :
    (E.refineOneHypercover F).sieve₁' i j = (F i j).sieve₀ := by
  rw [PreOneHypercover.sieve₁']
  congr
  ext <;> simp [PreOneHypercover.toPullback]

end

end CategoryTheory
