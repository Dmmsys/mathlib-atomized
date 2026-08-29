/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Splitting
public import Mathlib.AlgebraicTopology.SimplicialSet.Dimension
public import Mathlib.AlgebraicTopology.DoldKan.SplitSimplicialObject
public import Mathlib.CategoryTheory.Limits.Preserves.SigmaConst

/-!
# Computing homology using nondegenerate simplices

In this file, we introduce the normalized chain complex `X.normalizedChainComplex R`
of a simplicial set `X` with coefficients in `R` (where `R` is an object of a
preadditive category `C` with coproducts). The `n`-chains of this complex
identify to the coproduct of copies of `R` indexed by the nondegenerate
`n`-simplices of `X`. In particular, we deduce that the homology is zero in degree `≥ d`
when `X` has dimension `< d`.

-/

@[expose] public section

universe w v u

open CategoryTheory Limits HomologicalComplex Simplicial
  AlgebraicTopology.DoldKan

namespace SSet

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]
  (X Y : SSet.{w}) (f : X ⟶ Y) (R : C)

/--
Definition of `normalizedChainComplex` / `normalizedChainComplex` 的定义

English:
definition normalizedChainComplex
  signature: : ChainComplex C Nat
  body: (X.splitting.map (sigmaConst.obj R)).nondegComplex

中文:
定义 normalizedChainComplex
  签名: : ChainComplex C 自然数
  定义体: (X.splitting.map (sigmaConst.obj R)).nondegComplex

Depends on / 依赖: X.splitting.map, nondegComplex, sigmaConst, sigmaConst.obj, splitting
-/
noncomputable def normalizedChainComplex : ChainComplex C Nat :=
  (X.splitting.map (sigmaConst.obj R)).nondegComplex

/--
Definition of `toNormalizedChainComplex` / `toNormalizedChainComplex` 的定义

English:
definition toNormalizedChainComplex
  signature: : X.chainComplex R ⟶ X.normalizedChainComplex R
  body: (X.splitting.map (sigmaConst.obj R)).toNondegComplex

中文:
定义 toNormalizedChainComplex
  签名: : X.chainComplex R ⟶ X.normalizedChainComplex R
  定义体: (X.splitting.map (sigmaConst.obj R)).toNondegComplex

Depends on / 依赖: X.splitting.map, sigmaConst, sigmaConst.obj, splitting, toNondegComplex
-/
noncomputable def toNormalizedChainComplex : X.chainComplex R ⟶ X.normalizedChainComplex R :=
  (X.splitting.map (sigmaConst.obj R)).toNondegComplex

/--
Definition of `fromNormalizedChainComplex` / `fromNormalizedChainComplex` 的定义

English:
definition fromNormalizedChainComplex
  signature: : X.normalizedChainComplex R ⟶ X.chainComplex R
  body: (X.splitting.map (sigmaConst.obj R)).fromNondegComplex

@[reassoc (attr := simp)]

中文:
定义 fromNormalizedChainComplex
  签名: : X.normalizedChainComplex R ⟶ X.chainComplex R
  定义体: (X.splitting.map (sigmaConst.obj R)).fromNondegComplex

@[reassoc (attr := simp)]

Depends on / 依赖: X.splitting.map, fromNondegComplex, sigmaConst, sigmaConst.obj, splitting
-/
noncomputable def fromNormalizedChainComplex : X.normalizedChainComplex R ⟶ X.chainComplex R :=
  (X.splitting.map (sigmaConst.obj R)).fromNondegComplex

@[reassoc (attr := simp)]
/--
lemma `PInfty_toNormalizedChainComplex` / 引理 `PInfty_toNormalizedChainComplex`

English:
lemma PInfty_toNormalizedChainComplex
  proof: SimplicialObject.Splitting.PInfty_toNondegComplex _

中文:
引理 PInfty_toNormalizedChainComplex
  证明: SimplicialObject.Splitting.PInfty_toNondegComplex _

Depends on / 依赖: PInfty_toNondegComplex, SimplicialObject, SimplicialObject.Splitting.PInfty_toNondegComplex, Splitting
-/
lemma PInfty_toNormalizedChainComplex :
    PInfty ≫ X.toNormalizedChainComplex R = X.toNormalizedChainComplex R :=
  SimplicialObject.Splitting.PInfty_toNondegComplex _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsSplitEpi (X.toNormalizedChainComplex R)
  body: SimplicialObject.Splitting.isSplitEpi_toNondegComplex _

中文:
实例 :
  签名: IsSplitEpi (X.toNormalizedChainComplex R)
  定义体: SimplicialObject.Splitting.isSplitEpi_toNondegComplex _

Depends on / 依赖: SimplicialObject, SimplicialObject.Splitting.isSplitEpi_toNondegComplex, Splitting, isSplitEpi_toNondegComplex
-/
instance : IsSplitEpi (X.toNormalizedChainComplex R) :=
  SimplicialObject.Splitting.isSplitEpi_toNondegComplex _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsSplitMono (X.fromNormalizedChainComplex R)
  body: SimplicialObject.Splitting.isSplitMono_fromNondegComplex _

@[reassoc (attr := simp)]

中文:
实例 :
  签名: IsSplitMono (X.fromNormalizedChainComplex R)
  定义体: SimplicialObject.Splitting.isSplitMono_fromNondegComplex _

@[reassoc (attr := simp)]

Depends on / 依赖: SimplicialObject, SimplicialObject.Splitting.isSplitMono_fromNondegComplex, Splitting, isSplitMono_fromNondegComplex
-/
instance : IsSplitMono (X.fromNormalizedChainComplex R) :=
  SimplicialObject.Splitting.isSplitMono_fromNondegComplex _

@[reassoc (attr := simp)]
/--
lemma `fromNormalizedChainComplex_toNormalizedChainComplex` / 引理 `fromNormalizedChainComplex_toNormalizedChainComplex`

English:
lemma fromNormalizedChainComplex_toNormalizedChainComplex
  proof: SimplicialObject.Splitting.fromNondegComplex_toNondegComplex _

@[reassoc (attr := simp)]

中文:
引理 fromNormalizedChainComplex_toNormalizedChainComplex
  证明: SimplicialObject.Splitting.fromNondegComplex_toNondegComplex _

@[reassoc (attr := simp)]

Depends on / 依赖: SimplicialObject, SimplicialObject.Splitting.fromNondegComplex_toNondegComplex, Splitting, fromNondegComplex_toNondegComplex
-/
lemma fromNormalizedChainComplex_toNormalizedChainComplex :
    X.fromNormalizedChainComplex R ≫ X.toNormalizedChainComplex R = 𝟙 _ :=
  SimplicialObject.Splitting.fromNondegComplex_toNondegComplex _

@[reassoc (attr := simp)]
/--
lemma `fromNormalizedChainComplex_f_toNormalizedChainComplex_f` / 引理 `fromNormalizedChainComplex_f_toNormalizedChainComplex_f`

English:
lemma fromNormalizedChainComplex_f_toNormalizedChainComplex_f
  given: (n : Nat)
  proof: by
  simp [← HomologicalComplex.comp_f]

@[reassoc (attr := simp)]

中文:
引理 fromNormalizedChainComplex_f_toNormalizedChainComplex_f
  条件: (n : 自然数)
  证明: by
  simp [← HomologicalComplex.comp_f]

@[reassoc (attr := simp)]

Depends on / 依赖: HomologicalComplex, HomologicalComplex.comp_f, comp_f
-/
lemma fromNormalizedChainComplex_f_toNormalizedChainComplex_f (n : Nat) :
    (X.fromNormalizedChainComplex R).f n ≫ (X.toNormalizedChainComplex R).f n = 𝟙 _ := by
  simp [← HomologicalComplex.comp_f]

@[reassoc (attr := simp)]
/--
lemma `toNormalizedChainComplex_fromNormalizedChainComplex` / 引理 `toNormalizedChainComplex_fromNormalizedChainComplex`

English:
lemma toNormalizedChainComplex_fromNormalizedChainComplex
  proof: SimplicialObject.Splitting.toNondegComplex_fromNondegComplex _

@[reassoc (attr := simp)]

中文:
引理 toNormalizedChainComplex_fromNormalizedChainComplex
  证明: SimplicialObject.Splitting.toNondegComplex_fromNondegComplex _

@[reassoc (attr := simp)]

Depends on / 依赖: SimplicialObject, SimplicialObject.Splitting.toNondegComplex_fromNondegComplex, Splitting, toNondegComplex_fromNondegComplex
-/
lemma toNormalizedChainComplex_fromNormalizedChainComplex :
    X.toNormalizedChainComplex R ≫ X.fromNormalizedChainComplex R = PInfty :=
  SimplicialObject.Splitting.toNondegComplex_fromNondegComplex _

@[reassoc (attr := simp)]
/--
lemma `toNormalizedChainComplex_f_fromNormalizedChainComplex_f` / 引理 `toNormalizedChainComplex_f_fromNormalizedChainComplex_f`

English:
lemma toNormalizedChainComplex_f_fromNormalizedChainComplex_f
  given: (n : Nat)
  proof: by
  simp [← HomologicalComplex.comp_f]

中文:
引理 toNormalizedChainComplex_f_fromNormalizedChainComplex_f
  条件: (n : 自然数)
  证明: by
  simp [← HomologicalComplex.comp_f]

Depends on / 依赖: HomologicalComplex, HomologicalComplex.comp_f, comp_f
-/
lemma toNormalizedChainComplex_f_fromNormalizedChainComplex_f (n : Nat) :
    (X.toNormalizedChainComplex R).f n ≫ (X.fromNormalizedChainComplex R).f n = PInfty.f n := by
  simp [← HomologicalComplex.comp_f]

/--
Definition of `homotopyEquivNormalizedChainComplex` / `homotopyEquivNormalizedChainComplex` 的定义

English:
definition homotopyEquivNormalizedChainComplex
  signature: :
  body: SimplicialObject.Splitting.homotopyEquivNondegComplex _

@[simp]

中文:
定义 homotopyEquivNormalizedChainComplex
  签名: :
  定义体: SimplicialObject.Splitting.homotopyEquivNondegComplex _

@[simp]

Depends on / 依赖: SimplicialObject, SimplicialObject.Splitting.homotopyEquivNondegComplex, Splitting, homotopyEquivNondegComplex
-/
noncomputable def homotopyEquivNormalizedChainComplex :
    HomotopyEquiv (X.chainComplex R) (X.normalizedChainComplex R) :=
  SimplicialObject.Splitting.homotopyEquivNondegComplex _

@[simp]
/--
lemma `homotopyEquivNormalizedChainComplex_hom` / 引理 `homotopyEquivNormalizedChainComplex_hom`

English:
lemma homotopyEquivNormalizedChainComplex_hom
  proof: rfl

@[simp]

中文:
引理 homotopyEquivNormalizedChainComplex_hom
  证明: rfl

@[simp]
-/
lemma homotopyEquivNormalizedChainComplex_hom :
    (X.homotopyEquivNormalizedChainComplex R).hom = X.toNormalizedChainComplex R := rfl

@[simp]
/--
lemma `homotopyEquivNormalizedChainComplex_inv` / 引理 `homotopyEquivNormalizedChainComplex_inv`

English:
lemma homotopyEquivNormalizedChainComplex_inv
  proof: rfl

中文:
引理 homotopyEquivNormalizedChainComplex_inv
  证明: rfl
-/
lemma homotopyEquivNormalizedChainComplex_inv :
    (X.homotopyEquivNormalizedChainComplex R).inv = X.fromNormalizedChainComplex R := rfl

section

variable {R} {n : Nat}

/-- The map `R ⟶ (X.normalizedChainComplex R).X n` for any `x : X _⦋n⦌`. Note that
this is zero if `x` is a degenerate simplex, see `ιNormalizedChainComplex_eq_zero`. -/
@[no_expose]
/--
Definition of `ιNormalizedChainComplex` / `ιNormalizedChainComplex` 的定义

English:
definition ιNormalizedChainComplex
  signature: (x : X _⦋n⦌)
  body: X.ιChainComplex x ≫ (X.toNormalizedChainComplex R).f n

@[reassoc (attr := simp)]

中文:
定义 ιNormalizedChainComplex
  签名: (x : X _⦋n⦌)
  定义体: X.ιChainComplex x ≫ (X.toNormalizedChainComplex R).f n

@[reassoc (attr := simp)]

Depends on / 依赖: X.toNormalizedChainComplex, toNormalizedChainComplex
-/
noncomputable def ιNormalizedChainComplex (x : X _⦋n⦌) :
    R ⟶ (X.normalizedChainComplex R).X n :=
  X.ιChainComplex x ≫ (X.toNormalizedChainComplex R).f n

@[reassoc (attr := simp)]
/--
lemma `ιChainComplex_toNormalizedChainComplex_f` / 引理 `ιChainComplex_toNormalizedChainComplex_f`

English:
lemma ιChainComplex_toNormalizedChainComplex_f
  given: (x : X _⦋n⦌)
  proof: by
  rfl

@[reassoc (attr := simp)]

中文:
引理 ιChainComplex_toNormalizedChainComplex_f
  条件: (x : X _⦋n⦌)
  证明: by
  rfl

@[reassoc (attr := simp)]
-/
lemma ιChainComplex_toNormalizedChainComplex_f (x : X _⦋n⦌) :
    X.ιChainComplex x ≫ (X.toNormalizedChainComplex R).f n =
    X.ιNormalizedChainComplex x := by
  rfl

@[reassoc (attr := simp)]
/--
lemma `ιNormalizedChainComplex_d` / 引理 `ιNormalizedChainComplex_d`

English:
lemma ιNormalizedChainComplex_d
  given: {n : Nat} (x : X _⦋n + 1⦌)
  proof: by
  simp [ιNormalizedChainComplex, Preadditive.sum_comp,
    -ιChainComplex_toNormalizedChainComplex_f]

#adaptation_note

中文:
引理 ιNormalizedChainComplex_d
  条件: {n : 自然数} (x : X _⦋n + 1⦌)
  证明: by
  simp [ιNormalizedChainComplex, Preadditive.sum_comp,
    -ιChainComplex_toNormalizedChainComplex_f]

#adaptation_note

Depends on / 依赖: Preadditive, Preadditive.sum_comp, sum_comp
-/
lemma ιNormalizedChainComplex_d {n : Nat} (x : X _⦋n + 1⦌) :
    X.ιNormalizedChainComplex x ≫ (X.normalizedChainComplex R).d (n + 1) n =
      ∑ (i : Fin (n + 2)), (-1) ^ i.val • X.ιNormalizedChainComplex (X.δ i x) := by
  simp [ιNormalizedChainComplex, Preadditive.sum_comp,
    -ιChainComplex_toNormalizedChainComplex_f]

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
/--
lemma `ιNormalizedChainComplex_fromNormalizedChainComplex_f` / 引理 `ιNormalizedChainComplex_fromNormalizedChainComplex_f`

English:
lemma ιNormalizedChainComplex_fromNormalizedChainComplex_f
  given: (x : X _⦋n⦌)
  proof: by
  dsimp [ιNormalizedChainComplex]
  rw [Category.assoc]; rw [toNormalizedChainComplex_f_fromNormalizedChainComplex_f]

中文:
引理 ιNormalizedChainComplex_fromNormalizedChainComplex_f
  条件: (x : X _⦋n⦌)
  证明: by
  dsimp [ιNormalizedChainComplex]
  rw [Category.assoc]; rw [toNormalizedChainComplex_f_fromNormalizedChainComplex_f]

Depends on / 依赖: Category, Category.assoc, toNormalizedChainComplex_f_fromNormalizedChainComplex_f
-/
lemma ιNormalizedChainComplex_fromNormalizedChainComplex_f (x : X _⦋n⦌) :
    X.ιNormalizedChainComplex x ≫ (X.fromNormalizedChainComplex R).f n =
      X.ιChainComplex x ≫ (PInfty).f n := by
  dsimp [ιNormalizedChainComplex]
  rw [Category.assoc]; rw [toNormalizedChainComplex_f_fromNormalizedChainComplex_f]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `ιNormalizedChainComplex_eq_zero` / 引理 `ιNormalizedChainComplex_eq_zero`

English:
lemma ιNormalizedChainComplex_eq_zero
  given: (x : X _⦋n⦌) (hx : x in X.degenerate n)
  proof: by
  rw [← cancel_mono ((X.fromNormalizedChainComplex R).f n)]; rw [zero_comp]; rw [ιNormalizedChainComplex_fromNormalizedChainComplex_f]
  obtain _ | n := n
  · simp at hx
  · simp only [degenerate_eq_iUnion_range_σ, Set.mem_iUnion, Set.mem_range] at hx
    let X' := ((SimplicialObject.whiskering _

中文:
引理 ιNormalizedChainComplex_eq_zero
  条件: (x : X _⦋n⦌) (hx : x in X.degenerate n)
  证明: by
  rw [← cancel_mono ((X.fromNormalizedChainComplex R).f n)]; rw [zero_comp]; rw [ιNormalizedChainComplex_fromNormalizedChainComplex_f]
  obtain _ | n := n
  · simp at hx
  · simp only [degenerate_eq_iUnion_range_σ, Set.mem_iUnion, Set.mem_range] at hx
    let X' := ((SimplicialObject.whiskering _

Depends on / 依赖: PInfty, Set.mem_iUnion, Set.mem_range, SimplicialObject, SimplicialObject.whiskering, X.fromNormalizedChainComplex, cancel_mono, fromNormalizedChainComplex, mem_iUnion, mem_range, sigmaConst, sigmaConst.obj, whiskering, zero_comp
-/
lemma ιNormalizedChainComplex_eq_zero (x : X _⦋n⦌) (hx : x in X.degenerate n) :
    X.ιNormalizedChainComplex (R := R) x = 0 := by
  rw [← cancel_mono ((X.fromNormalizedChainComplex R).f n)]; rw [zero_comp]; rw [ιNormalizedChainComplex_fromNormalizedChainComplex_f]
  obtain _ | n := n
  · simp at hx
  · simp only [degenerate_eq_iUnion_range_σ, Set.mem_iUnion, Set.mem_range] at hx
    let X' := ((SimplicialObject.whiskering _ _).obj (sigmaConst.obj R)).obj X
    obtain ⟨i, y, rfl⟩ := hx
    trans X.ιChainComplex y ≫ X'.σ i ≫ (PInfty (X := X')).f _
    · simp [ιChainComplex, X']
    · simp

variable (R n) in
/--
Definition of `cofanNormalizedChainComplex` / `cofanNormalizedChainComplex` 的定义

English:
abbreviation cofanNormalizedChainComplex
  signature: : Cofan (fun (_ : X.nonDegenerate n) => R)
  body: Cofan.mk _ (fun x => X.ιNormalizedChainComplex x.val)

中文:
缩写 cofanNormalizedChainComplex
  签名: : Cofan (fun (_ : X.nonDegenerate n) => R)
  定义体: Cofan.mk _ (fun x => X.ιNormalizedChainComplex x.val)

Depends on / 依赖: Cofan.mk, x.val
-/
noncomputable abbrev cofanNormalizedChainComplex : Cofan (fun (_ : X.nonDegenerate n) => R) :=
  Cofan.mk _ (fun x => X.ιNormalizedChainComplex x.val)

set_option backward.isDefEq.respectTransparency false in
variable (R n) in
/--
lemma `ιNormalizedChainComplex_eq_ι` / 引理 `ιNormalizedChainComplex_eq_ι`

English:
lemma ιNormalizedChainComplex_eq_ι
  given: (x : X _⦋n⦌) (hx : x in X.nonDegenerate n)
  proof: by
  dsimp [ιNormalizedChainComplex, ιChainComplex]
  rw [← cancel_mono ((X.fromNormalizedChainComplex R).f n)]; rw [Category.assoc]; rw [toNormalizedChainComplex_f_fromNormalizedChainComplex_f]
  simp [fromNormalizedChainComplex, SimplicialObject.Splitting.fromNondegComplex_f]

中文:
引理 ιNormalizedChainComplex_eq_ι
  条件: (x : X _⦋n⦌) (hx : x in X.nonDegenerate n)
  证明: by
  dsimp [ιNormalizedChainComplex, ιChainComplex]
  rw [← cancel_mono ((X.fromNormalizedChainComplex R).f n)]; rw [Category.assoc]; rw [toNormalizedChainComplex_f_fromNormalizedChainComplex_f]
  simp [fromNormalizedChainComplex, SimplicialObject.Splitting.fromNondegComplex_f]
-/
private lemma ιNormalizedChainComplex_eq_ι (x : X _⦋n⦌) (hx : x in X.nonDegenerate n) :
    X.ιNormalizedChainComplex (R := R) x =
      Sigma.ι (fun (_ : X.nonDegenerate n) => R) ⟨x, hx⟩ := by
  dsimp [ιNormalizedChainComplex, ιChainComplex]
  rw [← cancel_mono ((X.fromNormalizedChainComplex R).f n)]; rw [Category.assoc]; rw [toNormalizedChainComplex_f_fromNormalizedChainComplex_f]
  simp [fromNormalizedChainComplex, SimplicialObject.Splitting.fromNondegComplex_f]

set_option backward.isDefEq.respectTransparency false in
variable (R n) in
/-- `(X.normalizedChainComplex R).X n` identifies to the coproduct of copies
of `R` indexed by the nondegenerate `n`-simplices of the simplicial set `X`. -/
@[no_expose]
/--
Definition of `isColimitCofanNormalizedChainComplex` / `isColimitCofanNormalizedChainComplex` 的定义

English:
definition isColimitCofanNormalizedChainComplex
  signature: :
  body: IsColimit.ofIsoColimit (coproductIsCoproduct _)
    (Cofan.ext (Iso.refl _) (fun ⟨x, hx⟩ => by
      simpa using (X.ιNormalizedChainComplex_eq_ι R n x hx).symm))

@[ext]

中文:
定义 isColimitCofanNormalizedChainComplex
  签名: :
  定义体: IsColimit.ofIsoColimit (coproductIsCoproduct _)
    (Cofan.ext (Iso.refl _) (fun ⟨x, hx⟩ => by
      simpa using (X.ιNormalizedChainComplex_eq_ι R n x hx).symm))

@[ext]

Depends on / 依赖: Cofan.ext, IsColimit, IsColimit.ofIsoColimit, Iso.refl, coproductIsCoproduct, ofIsoColimit
-/
noncomputable def isColimitCofanNormalizedChainComplex :
    IsColimit (X.cofanNormalizedChainComplex R n) :=
  IsColimit.ofIsoColimit (coproductIsCoproduct _)
    (Cofan.ext (Iso.refl _) (fun ⟨x, hx⟩ => by
      simpa using (X.ιNormalizedChainComplex_eq_ι R n x hx).symm))

@[ext]
/--
lemma `normalizedChainComplex_hom_ext` / 引理 `normalizedChainComplex_hom_ext`

English:
lemma normalizedChainComplex_hom_ext
  statement: {T : C} {f g : (X.normalizedChainComplex R).X n ⟶ T}
  proof: (X.isColimitCofanNormalizedChainComplex R n).hom_ext (fun ⟨x, hx⟩ => h x hx)

中文:
引理 normalizedChainComplex_hom_ext
  结论: {T : C} {f g : (X.normalizedChainComplex R).X n ⟶ T}
  证明: (X.isColimitCofanNormalizedChainComplex R n).hom_ext (fun ⟨x, hx⟩ => h x hx)

Depends on / 依赖: X.isColimitCofanNormalizedChainComplex, hom_ext, isColimitCofanNormalizedChainComplex
-/
lemma normalizedChainComplex_hom_ext {T : C} {f g : (X.normalizedChainComplex R).X n ⟶ T}
    (h : forall (x : X _⦋n⦌) (_ : x in X.nonDegenerate n),
      X.ιNormalizedChainComplex x ≫ f = X.ιNormalizedChainComplex x ≫ g) :
    f = g :=
  (X.isColimitCofanNormalizedChainComplex R n).hom_ext (fun ⟨x, hx⟩ => h x hx)

end

/--
lemma `isZero_normalizedChainComplex_X_of_hasDimensionLT` / 引理 `isZero_normalizedChainComplex_X_of_hasDimensionLT`

English:
lemma isZero_normalizedChainComplex_X_of_hasDimensionLT
  statement: (n d : Nat) [X.HasDimensionLT d]
  proof: by
  rw [IsZero.iff_id_eq_zero]
  ext x hx
  exact (h.not_gt (X.dim_lt_of_nonDegenerate ⟨x, hx⟩ d)).elim

中文:
引理 isZero_normalizedChainComplex_X_of_hasDimensionLT
  结论: (n d : 自然数) [X.HasDimensionLT d]
  证明: by
  rw [IsZero.iff_id_eq_zero]
  ext x hx
  exact (h.not_gt (X.dim_lt_of_nonDegenerate ⟨x, hx⟩ d)).elim

Depends on / 依赖: IsZero, IsZero.iff_id_eq_zero, X.dim_lt_of_nonDegenerate, X.normalizedChainComplex, dim_lt_of_nonDegenerate, h.not_gt, iff_id_eq_zero, normalizedChainComplex, not_gt
-/
lemma isZero_normalizedChainComplex_X_of_hasDimensionLT (n d : Nat) [X.HasDimensionLT d]
    (h : d <= n := by lia) :
    IsZero ((X.normalizedChainComplex R).X n) := by
  rw [IsZero.iff_id_eq_zero]
  ext x hx
  exact (h.not_gt (X.dim_lt_of_nonDegenerate ⟨x, hx⟩ d)).elim

section

variable {X Y}

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `chainComplexMap_PInfty` / 引理 `chainComplexMap_PInfty`

English:
lemma chainComplexMap_PInfty
  proof: (natTransPInfty _).naturality _

中文:
引理 chainComplexMap_PInfty
  证明: (natTransPInfty _).naturality _

Depends on / 依赖: natTransPInfty, naturality
-/
lemma chainComplexMap_PInfty :
    chainComplexMap f R ≫ PInfty = PInfty ≫ chainComplexMap f R :=
  (natTransPInfty _).naturality _

/--
Definition of `normalizedChainComplexMap` / `normalizedChainComplexMap` 的定义

English:
definition normalizedChainComplexMap
  signature: :
  body: X.fromNormalizedChainComplex R ≫ chainComplexMap f R ≫ Y.toNormalizedChainComplex R

中文:
定义 normalizedChainComplexMap
  签名: :
  定义体: X.fromNormalizedChainComplex R ≫ chainComplexMap f R ≫ Y.toNormalizedChainComplex R

Depends on / 依赖: X.fromNormalizedChainComplex, Y.toNormalizedChainComplex, chainComplexMap, fromNormalizedChainComplex, toNormalizedChainComplex
-/
noncomputable def normalizedChainComplexMap :
    X.normalizedChainComplex R ⟶ Y.normalizedChainComplex R :=
  X.fromNormalizedChainComplex R ≫ chainComplexMap f R ≫ Y.toNormalizedChainComplex R

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `toNormalizedChainComplex_normalizedChainComplexMap` / 引理 `toNormalizedChainComplex_normalizedChainComplexMap`

English:
lemma toNormalizedChainComplex_normalizedChainComplexMap
  proof: by
  simp [normalizedChainComplexMap, ← chainComplexMap_PInfty_assoc]

@[reassoc (attr := simp)]

中文:
引理 toNormalizedChainComplex_normalizedChainComplexMap
  证明: by
  simp [normalizedChainComplexMap, ← chainComplexMap_PInfty_assoc]

@[reassoc (attr := simp)]

Depends on / 依赖: chainComplexMap_PInfty_assoc, normalizedChainComplexMap
-/
lemma toNormalizedChainComplex_normalizedChainComplexMap :
    X.toNormalizedChainComplex R ≫ normalizedChainComplexMap f R =
      chainComplexMap f R ≫ Y.toNormalizedChainComplex R := by
  simp [normalizedChainComplexMap, ← chainComplexMap_PInfty_assoc]

@[reassoc (attr := simp)]
/--
lemma `ι_normalizedChainComplexMap_f` / 引理 `ι_normalizedChainComplexMap_f`

English:
lemma ι_normalizedChainComplexMap_f
  given: {n : Nat} (x : X _⦋n⦌)
  proof: by
  simpa only [comp_f, eval_map, ιNormalizedChainComplex,
    ιChainComplex_toNormalizedChainComplex_f_assoc, ι_chainComplexMap_f_assoc] using
    X.ιChainComplex x ≫=
      (eval _ _ n).congr_map (toNormalizedChainComplex_normalizedChainComplexMap f R)

中文:
引理 ι_normalizedChainComplexMap_f
  条件: {n : 自然数} (x : X _⦋n⦌)
  证明: by
  simpa only [comp_f, eval_map, ιNormalizedChainComplex,
    ιChainComplex_toNormalizedChainComplex_f_assoc, ι_chainComplexMap_f_assoc] using
    X.ιChainComplex x ≫=
      (eval _ _ n).congr_map (toNormalizedChainComplex_normalizedChainComplexMap f R)

Depends on / 依赖: comp_f, congr_map, eval_map, toNormalizedChainComplex_normalizedChainComplexMap
-/
lemma ι_normalizedChainComplexMap_f {n : Nat} (x : X _⦋n⦌) :
    X.ιNormalizedChainComplex x ≫ (normalizedChainComplexMap f R).f n =
      Y.ιNormalizedChainComplex (f.app _ x) := by
  simpa only [comp_f, eval_map, ιNormalizedChainComplex,
    ιChainComplex_toNormalizedChainComplex_f_assoc, ι_chainComplexMap_f_assoc] using
    X.ιChainComplex x ≫=
      (eval _ _ n).congr_map (toNormalizedChainComplex_normalizedChainComplexMap f R)

/-- Given `R : C`, this is the functor `SSet.{w} ⥤ ChainComplex C ℕ` which sends
a simplicial set `X` to `X.normalizedChainComplex R`. -/
@[simps]
/--
Definition of `normalizedChainComplexFunctorObj` / `normalizedChainComplexFunctorObj` 的定义

English:
definition normalizedChainComplexFunctorObj
  signature: : SSet.{w} ⥤ ChainComplex C Nat where
  body: X.normalizedChainComplex R
  map f := normalizedChainComplexMap f R

中文:
定义 normalizedChainComplexFunctorObj
  签名: : SSet.{w} ⥤ ChainComplex C 自然数 where
  定义体: X.normalizedChainComplex R
  map f := normalizedChainComplexMap f R

Depends on / 依赖: X.normalizedChainComplex, normalizedChainComplex
-/
noncomputable def normalizedChainComplexFunctorObj : SSet.{w} ⥤ ChainComplex C Nat where
  obj X := X.normalizedChainComplex R
  map f := normalizedChainComplexMap f R

set_option backward.defeqAttrib.useBackward true in
/-- The morphism `X.toNormalizedChainComplex R` for any simplicial set `X`,
as a natural transformation. -/
@[simps]
/--
Definition of `toNormalizedChainComplexNatTrans` / `toNormalizedChainComplexNatTrans` 的定义

English:
definition toNormalizedChainComplexNatTrans
  signature: :
  body: X.toNormalizedChainComplex R

中文:
定义 toNormalizedChainComplexNatTrans
  签名: :
  定义体: X.toNormalizedChainComplex R

Depends on / 依赖: X.toNormalizedChainComplex, toNormalizedChainComplex
-/
noncomputable def toNormalizedChainComplexNatTrans :
    (chainComplexFunctor C).obj R ⟶ normalizedChainComplexFunctorObj R where
  app X := X.toNormalizedChainComplex R

end

section

variable [CategoryWithHomology C]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: QuasiIso (X.toNormalizedChainComplex R)
  body: (X.homotopyEquivNormalizedChainComplex R).quasiIso_hom

中文:
实例 :
  签名: QuasiIso (X.toNormalizedChainComplex R)
  定义体: (X.homotopyEquivNormalizedChainComplex R).quasiIso_hom

Depends on / 依赖: X.homotopyEquivNormalizedChainComplex, homotopyEquivNormalizedChainComplex, quasiIso_hom
-/
instance : QuasiIso (X.toNormalizedChainComplex R) :=
  (X.homotopyEquivNormalizedChainComplex R).quasiIso_hom

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: QuasiIso (X.fromNormalizedChainComplex R)
  body: (X.homotopyEquivNormalizedChainComplex R).quasiIso_inv

中文:
实例 :
  签名: QuasiIso (X.fromNormalizedChainComplex R)
  定义体: (X.homotopyEquivNormalizedChainComplex R).quasiIso_inv

Depends on / 依赖: X.homotopyEquivNormalizedChainComplex, homotopyEquivNormalizedChainComplex, quasiIso_inv
-/
instance : QuasiIso (X.fromNormalizedChainComplex R) :=
  (X.homotopyEquivNormalizedChainComplex R).quasiIso_inv

/--
lemma `exactAt_chainComplex_of_hasDimensionLT` / 引理 `exactAt_chainComplex_of_hasDimensionLT`

English:
lemma exactAt_chainComplex_of_hasDimensionLT
  statement: (n d : Nat) [X.HasDimensionLT d]
  proof: by
  rw [exactAt_iff_of_quasiIsoAt (X.toNormalizedChainComplex R)]
  exact .of_isZero (X.isZero_normalizedChainComplex_X_of_hasDimensionLT R n d)

中文:
引理 exactAt_chainComplex_of_hasDimensionLT
  结论: (n d : 自然数) [X.HasDimensionLT d]
  证明: by
  rw [exactAt_iff_of_quasiIsoAt (X.toNormalizedChainComplex R)]
  exact .of_isZero (X.isZero_normalizedChainComplex_X_of_hasDimensionLT R n d)

Depends on / 依赖: ExactAt, X.chainComplex, X.isZero_normalizedChainComplex_X_of_hasDimensionLT, X.toNormalizedChainComplex, chainComplex, exactAt_iff_of_quasiIsoAt, isZero_normalizedChainComplex_X_of_hasDimensionLT, of_isZero, toNormalizedChainComplex
-/
lemma exactAt_chainComplex_of_hasDimensionLT (n d : Nat) [X.HasDimensionLT d]
    (h : d <= n := by lia) :
    (X.chainComplex R).ExactAt n := by
  rw [exactAt_iff_of_quasiIsoAt (X.toNormalizedChainComplex R)]
  exact .of_isZero (X.isZero_normalizedChainComplex_X_of_hasDimensionLT R n d)

/--
lemma `isZero_homology_of_hasDimensionLT` / 引理 `isZero_homology_of_hasDimensionLT`

English:
lemma isZero_homology_of_hasDimensionLT
  statement: (n d : Nat) [X.HasDimensionLT d]
  proof: by
  rw [← exactAt_iff_isZero_homology]
  exact X.exactAt_chainComplex_of_hasDimensionLT R n d

中文:
引理 isZero_homology_of_hasDimensionLT
  结论: (n d : 自然数) [X.HasDimensionLT d]
  证明: by
  rw [← exactAt_iff_isZero_homology]
  exact X.exactAt_chainComplex_of_hasDimensionLT R n d

Depends on / 依赖: IsZero, X.exactAt_chainComplex_of_hasDimensionLT, X.homology, exactAt_chainComplex_of_hasDimensionLT, exactAt_iff_isZero_homology, homology
-/
lemma isZero_homology_of_hasDimensionLT (n d : Nat) [X.HasDimensionLT d]
    (h : d <= n := by lia) :
    IsZero (X.homology R n) := by
  rw [← exactAt_iff_isZero_homology]
  exact X.exactAt_chainComplex_of_hasDimensionLT R n d

end

end SSet
