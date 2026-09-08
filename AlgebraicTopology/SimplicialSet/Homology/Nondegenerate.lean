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

/-- The normalized chain complex of a simplicial set `X` with coefficients in `R`.
In degree `n`, it consists of a coproduct of copies of `R` indexed by the
nondegenerate `n`-simplices of `X`. -/
/-
**SSet.normalizedChainComplex** 是 Mathlib 中的一个定义，位于命名空间 `SSet`。
形式化陈述：normalizedChainComplex : ChainComplex C Nat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The normalized chain complex of a simplicial set `X` with coefficients in `R`.
In degree `n`, it consists of a coproduct of copies of `R` indexed by the
nondegenerate `n`-simplices of `X`.
-/
noncomputable def normalizedChainComplex : ChainComplex C ℕ :=
  (X.splitting.map (sigmaConst.obj R)).nondegComplex

/-- The split epi `X.chainComplex R ⟶ X.normalizedChainComplex R`. -/
/-
**SSet.toNormalizedChainComplex** 是 Mathlib 中的一个定义，位于命名空间 `SSet`。
形式化陈述：toNormalizedChainComplex : X.chainComplex R ⟶ X.normalizedChainComplex R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The split epi `X.chainComplex R ⟶ X.normalizedChainComplex R`.
-/
noncomputable def toNormalizedChainComplex : X.chainComplex R ⟶ X.normalizedChainComplex R :=
  (X.splitting.map (sigmaConst.obj R)).toNondegComplex

/-- The split mono `X.normalizedChainComplex R ⟶ X.chainComplex R`. -/
/-
**SSet.fromNormalizedChainComplex** 是 Mathlib 中的一个定义，位于命名空间 `SSet`。
形式化陈述：fromNormalizedChainComplex : X.normalizedChainComplex R ⟶ X.chainComplex R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The split mono `X.normalizedChainComplex R ⟶ X.chainComplex R`.
-/
noncomputable def fromNormalizedChainComplex : X.normalizedChainComplex R ⟶ X.chainComplex R :=
  (X.splitting.map (sigmaConst.obj R)).fromNondegComplex

@[reassoc (attr := simp)]
/-
**SSet.PInfty_toNormalizedChainComplex** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：PInfty_toNormalizedChainComplex : PInfty ≫ X.toNormalizedChainComplex R = 
X.toNormalizedChainComplex R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.SimplicialObject.Splitting.PInfty_toNondegComplex`：PInfty
_toNondegComplex : PInfty ≫ s.toNondegComplex = s.toNondegComplex
-/
lemma PInfty_toNormalizedChainComplex :
    PInfty ≫ X.toNormalizedChainComplex R = X.toNormalizedChainComplex R :=
  SimplicialObject.Splitting.PInfty_toNondegComplex _
/-
**SSet.** 是 Mathlib 中的一个实例，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsSplitEpi (X.toNormalizedChainComplex R) :=
  SimplicialObject.Splitting.isSplitEpi_toNondegComplex _
/-
**SSet.** 是 Mathlib 中的一个实例，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsSplitMono (X.fromNormalizedChainComplex R) :=
  SimplicialObject.Splitting.isSplitMono_fromNondegComplex _

@[reassoc (attr := simp)]
/-
**SSet.fromNormalizedChainComplex_toNormalizedChainComplex** 是 Mathlib 中的一个引理，位于
命名空间 `SSet`。
形式化陈述：fromNormalizedChainComplex_toNormalizedChainComplex : X.fromNormalizedChai
nComplex R ≫ X.toNormalizedChainComplex R = 𝟙 _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.SimplicialObject.Splitting.fromNondegComplex_toNondegComp
lex`：fromNondegComplex_toNondegComplex : s.fromNondegComplex ≫ s.toNondegComplex
 = 𝟙 _
-/
lemma fromNormalizedChainComplex_toNormalizedChainComplex :
    X.fromNormalizedChainComplex R ≫ X.toNormalizedChainComplex R = 𝟙 _ :=
  SimplicialObject.Splitting.fromNondegComplex_toNondegComplex _

@[reassoc (attr := simp)]
/-
**SSet.fromNormalizedChainComplex_f_toNormalizedChainComplex_f** 是 Mathlib 中的一个引
理，位于命名空间 `SSet`。
形式化陈述：fromNormalizedChainComplex_f_toNormalizedChainComplex_f (n : Nat) : (X.fro
mNormalizedChainComplex R).f n ≫ (X.toNormalizedChainComplex R).f n = 𝟙 _
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `SSet.fromNormalizedChainComplex_toNormalizedChainComplex`：fromNormalized
ChainComplex_toNormalizedChainComplex : X.fromNormalizedChainComplex R ≫ X.toNor
malizedChainComplex R = 𝟙 _
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma fromNormalizedChainComplex_f_toNormalizedChainComplex_f (n : ℕ) :
    (X.fromNormalizedChainComplex R).f n ≫ (X.toNormalizedChainComplex R).f n = 𝟙 _ := by
  simp [← HomologicalComplex.comp_f]

@[reassoc (attr := simp)]
/-
**SSet.toNormalizedChainComplex_fromNormalizedChainComplex** 是 Mathlib 中的一个引理，位于
命名空间 `SSet`。
形式化陈述：toNormalizedChainComplex_fromNormalizedChainComplex : X.toNormalizedChainC
omplex R ≫ X.fromNormalizedChainComplex R = PInfty
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.SimplicialObject.Splitting.toNondegComplex_fromNondegComp
lex`：toNondegComplex_fromNondegComplex : s.toNondegComplex ≫ s.fromNondegComplex
 = PInfty
-/
lemma toNormalizedChainComplex_fromNormalizedChainComplex :
    X.toNormalizedChainComplex R ≫ X.fromNormalizedChainComplex R = PInfty :=
  SimplicialObject.Splitting.toNondegComplex_fromNondegComplex _

@[reassoc (attr := simp)]
/-
**SSet.toNormalizedChainComplex_f_fromNormalizedChainComplex_f** 是 Mathlib 中的一个引
理，位于命名空间 `SSet`。
形式化陈述：toNormalizedChainComplex_f_fromNormalizedChainComplex_f (n : Nat) : (X.toN
ormalizedChainComplex R).f n ≫ (X.fromNormalizedChainComplex R).f n = PInfty.f n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `SSet.toNormalizedChainComplex_fromNormalizedChainComplex`：toNormalizedCh
ainComplex_fromNormalizedChainComplex : X.toNormalizedChainComplex R ≫ X.fromNor
malizedChainComplex R = PInfty
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma toNormalizedChainComplex_f_fromNormalizedChainComplex_f (n : ℕ) :
    (X.toNormalizedChainComplex R).f n ≫ (X.fromNormalizedChainComplex R).f n = PInfty.f n := by
  simp [← HomologicalComplex.comp_f]

/-- The homotopy equivalence from `X.chainComplex R` to `X.normalizedChainComplex R`. -/
/-
**SSet.homotopyEquivNormalizedChainComplex** 是 Mathlib 中的一个定义，位于命名空间 `SSet`。
形式化陈述：homotopyEquivNormalizedChainComplex : HomotopyEquiv (X.chainComplex R) (X.
normalizedChainComplex R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The homotopy equivalence from `X.chainComplex R` to `X.normalizedChainComplex R`
.
-/
noncomputable def homotopyEquivNormalizedChainComplex :
    HomotopyEquiv (X.chainComplex R) (X.normalizedChainComplex R) :=
  SimplicialObject.Splitting.homotopyEquivNondegComplex _

@[simp]
/-
**SSet.homotopyEquivNormalizedChainComplex_hom** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：homotopyEquivNormalizedChainComplex_hom : (X.homotopyEquivNormalizedChainC
omplex R).hom = X.toNormalizedChainComplex R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
lemma homotopyEquivNormalizedChainComplex_hom :
    (X.homotopyEquivNormalizedChainComplex R).hom = X.toNormalizedChainComplex R := rfl

@[simp]
/-
**SSet.homotopyEquivNormalizedChainComplex_inv** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：homotopyEquivNormalizedChainComplex_inv : (X.homotopyEquivNormalizedChainC
omplex R).inv = X.fromNormalizedChainComplex R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
lemma homotopyEquivNormalizedChainComplex_inv :
    (X.homotopyEquivNormalizedChainComplex R).inv = X.fromNormalizedChainComplex R := rfl

section

variable {R} {n : ℕ}

/-- The map `R ⟶ (X.normalizedChainComplex R).X n` for any `x : X _⦋n⦌`. Note that
this is zero if `x` is a degenerate simplex, see `ιNormalizedChainComplex_eq_zero`. -/
@[no_expose]
/-
**SSet.** 是 Mathlib 中的一个定义，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map `R ⟶ (X.normalizedChainComplex R).X n` for any `x : X _⦋n⦌`. Note that
this is zero if `x` is a degenerate simplex, see `ιNormalizedChainComplex_eq_zer
o`.
-/
noncomputable def ιNormalizedChainComplex (x : X _⦋n⦌) :
    R ⟶ (X.normalizedChainComplex R).X n :=
  X.ιChainComplex x ≫ (X.toNormalizedChainComplex R).f n

@[reassoc (attr := simp)]
/-
**SSet.** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ιChainComplex_toNormalizedChainComplex_f (x : X _⦋n⦌) :
    X.ιChainComplex x ≫ (X.toNormalizedChainComplex R).f n =
    X.ιNormalizedChainComplex x := by
  rfl

@[reassoc (attr := simp)]
/-
**SSet.** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ιNormalizedChainComplex_d {n : ℕ} (x : X _⦋n + 1⦌) :
    X.ιNormalizedChainComplex x ≫ (X.normalizedChainComplex R).d (n + 1) n =
      ∑ (i : Fin (n + 2)), (-1) ^ i.val • X.ιNormalizedChainComplex (X.δ i x) := by
  simp [ιNormalizedChainComplex, Preadditive.sum_comp,
    -ιChainComplex_toNormalizedChainComplex_f]

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
/-
**SSet.** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`respectTransparency.types true` changes the auto-generated lemmas' signature
-/
lemma ιNormalizedChainComplex_fromNormalizedChainComplex_f (x : X _⦋n⦌) :
    X.ιNormalizedChainComplex x ≫ (X.fromNormalizedChainComplex R).f n =
      X.ιChainComplex x ≫ (PInfty).f n := by
  dsimp [ιNormalizedChainComplex]
  rw [Category.assoc, toNormalizedChainComplex_f_fromNormalizedChainComplex_f]

set_option backward.isDefEq.respectTransparency false in
/-
**SSet.** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ιNormalizedChainComplex_eq_zero (x : X _⦋n⦌) (hx : x ∈ X.degenerate n) :
    X.ιNormalizedChainComplex (R := R) x = 0 := by
  rw [← cancel_mono ((X.fromNormalizedChainComplex R).f n), zero_comp,
    ιNormalizedChainComplex_fromNormalizedChainComplex_f]
  obtain _ | n := n
  · simp at hx
  · simp only [degenerate_eq_iUnion_range_σ, Set.mem_iUnion, Set.mem_range] at hx
    let X' := ((SimplicialObject.whiskering _ _).obj (sigmaConst.obj R)).obj X
    obtain ⟨i, y, rfl⟩ := hx
    trans X.ιChainComplex y ≫ X'.σ i ≫ (PInfty (X := X')).f _
    · simp [ιChainComplex, X']
    · simp

variable (R n) in
/-- The cofan given by the inclusions
`X.ιNormalizedChainComplex x : R ⟶ (X.normalizedChainComplex R).X n` for all
nondegenerate `n`-simplices `x` of a simplicial set `X`. -/
/-
**SSet.cofanNormalizedChainComplex** 是 Mathlib 中的一个缩写定义，位于命名空间 `SSet`。
形式化陈述：cofanNormalizedChainComplex : Cofan (fun (_ : X.nonDegenerate n) => R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cofan given by the inclusions
`X.ιNormalizedChainComplex x : R ⟶ (X.normalizedChainComplex R).X n` for all
nondegenerate `n`-simplices `x` of a simplicial set `X`.
-/
noncomputable abbrev cofanNormalizedChainComplex : Cofan (fun (_ : X.nonDegenerate n) ↦ R) :=
  Cofan.mk _ (fun x ↦ X.ιNormalizedChainComplex x.val)

set_option backward.isDefEq.respectTransparency false in
variable (R n) in
/-
**SSet.** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma ιNormalizedChainComplex_eq_ι (x : X _⦋n⦌) (hx : x ∈ X.nonDegenerate n) :
    X.ιNormalizedChainComplex (R := R) x =
      Sigma.ι (fun (_ : X.nonDegenerate n) ↦ R) ⟨x, hx⟩ := by
  dsimp [ιNormalizedChainComplex, ιChainComplex]
  rw [← cancel_mono ((X.fromNormalizedChainComplex R).f n), Category.assoc,
    toNormalizedChainComplex_f_fromNormalizedChainComplex_f]
  simp [fromNormalizedChainComplex, SimplicialObject.Splitting.fromNondegComplex_f]

set_option backward.isDefEq.respectTransparency false in
variable (R n) in
/-- `(X.normalizedChainComplex R).X n` identifies to the coproduct of copies
of `R` indexed by the nondegenerate `n`-simplices of the simplicial set `X`. -/
@[no_expose]
/-
**SSet.isColimitCofanNormalizedChainComplex** 是 Mathlib 中的一个定义，位于命名空间 `SSet`。
形式化陈述：isColimitCofanNormalizedChainComplex : IsColimit (X.cofanNormalizedChainCo
mplex R n)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`(X.normalizedChainComplex R).X n` identifies to the coproduct of copies
of `R` indexed by the nondegenerate `n`-simplices of the simplicial set `X`.
-/
noncomputable def isColimitCofanNormalizedChainComplex :
    IsColimit (X.cofanNormalizedChainComplex R n) :=
  IsColimit.ofIsoColimit (coproductIsCoproduct _)
    (Cofan.ext (Iso.refl _) (fun ⟨x, hx⟩ ↦ by
      simpa using (X.ιNormalizedChainComplex_eq_ι R n x hx).symm))

@[ext]
/-
**SSet.normalizedChainComplex_hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：normalizedChainComplex_hom_ext {T : C} {f g : (X.normalizedChainComplex R)
.X n ⟶ T} (h : forall (x : X _⦋n⦌) (_ : x in X.nonDegenerate n), X.ιNormalizedCh
ainComplex x ≫ f = X.ιNormalizedChainComplex x ≫ g) : f = g
参数：X.normalizedChainComplex R；h : forall (x : X _⦋n⦌) (_ : x in X.nonDegenerate 
n), X.ιNormalizedChainComplex x ≫ f = X.ιNormalizedChainComplex x ≫ g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `CategoryTheory.Limits.IsColimit.hom_ext`：∀ {J : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃
, u₃} C]   {F : CategoryTheor…
-/
lemma normalizedChainComplex_hom_ext {T : C} {f g : (X.normalizedChainComplex R).X n ⟶ T}
    (h : ∀ (x : X _⦋n⦌) (_ : x ∈ X.nonDegenerate n),
      X.ιNormalizedChainComplex x ≫ f = X.ιNormalizedChainComplex x ≫ g) :
    f = g :=
  (X.isColimitCofanNormalizedChainComplex R n).hom_ext (fun ⟨x, hx⟩ ↦ h x hx)

end

/-
**SSet.isZero_normalizedChainComplex_X_of_hasDimensionLT** 是 Mathlib 中的一个引理，位于命名
空间 `SSet`。
形式化陈述：isZero_normalizedChainComplex_X_of_hasDimensionLT (n d : Nat) [X.HasDimens
ionLT d] (h : d <= n
参数：n d : Nat。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.IsZero.iff_id_eq_zero`：iff_id_eq_zero (X : C) : Is
Zero X ↔ 𝟙 X = 0
· 使用引理 `SSet.normalizedChainComplex_hom_ext`：normalizedChainComplex_hom_ext {T :
 C} {f g : (X.normalizedChainComplex R).X n ⟶ T} (h : forall (x : X _⦋n⦌) (_ : x
 in X.nonDegenerate n), X…
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用引理 `SSet.dim_lt_of_nonDegenerate`：dim_lt_of_nonDegenerate {n : Nat} (x : X.n
onDegenerate n) (d : Nat) [X.HasDimensionLT d] : n < d
-/
lemma isZero_normalizedChainComplex_X_of_hasDimensionLT (n d : ℕ) [X.HasDimensionLT d]
    (h : d ≤ n := by lia) :
    IsZero ((X.normalizedChainComplex R).X n) := by
  rw [IsZero.iff_id_eq_zero]
  ext x hx
  exact (h.not_gt (X.dim_lt_of_nonDegenerate ⟨x, hx⟩ d)).elim

section

variable {X Y}

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**SSet.chainComplexMap_PInfty** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：chainComplexMap_PInfty : chainComplexMap f R ≫ PInfty = PInfty ≫ chainComp
lexMap f R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
lemma chainComplexMap_PInfty :
    chainComplexMap f R ≫ PInfty = PInfty ≫ chainComplexMap f R :=
  (natTransPInfty _).naturality _

/-- The morphism `X.normalizedChainComplex R ⟶ Y.normalizedChainComplex R` induced
by a morphism a simplicial sets `X ⟶ Y`. -/
/-
**SSet.normalizedChainComplexMap** 是 Mathlib 中的一个定义，位于命名空间 `SSet`。
形式化陈述：normalizedChainComplexMap : X.normalizedChainComplex R ⟶ Y.normalizedChain
Complex R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism `X.normalizedChainComplex R ⟶ Y.normalizedChainComplex R` induced
by a morphism a simplicial sets `X ⟶ Y`.
-/
noncomputable def normalizedChainComplexMap :
    X.normalizedChainComplex R ⟶ Y.normalizedChainComplex R :=
  X.fromNormalizedChainComplex R ≫ chainComplexMap f R ≫ Y.toNormalizedChainComplex R

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**SSet.toNormalizedChainComplex_normalizedChainComplexMap** 是 Mathlib 中的一个引理，位于命
名空间 `SSet`。
形式化陈述：toNormalizedChainComplex_normalizedChainComplexMap : X.toNormalizedChainCo
mplex R ≫ normalizedChainComplexMap f R = chainComplexMap f R ≫ Y.toNormalizedCh
ainComplex R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SSet.toNormalizedChainComplex_fromNormalizedChainComplex_assoc`：∀ {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits
.HasCoproducts C]   [inst_2 : CategoryTheory.Preaddi…
· 使用引理 `SSet.PInfty_toNormalizedChainComplex`：PInfty_toNormalizedChainComplex : 
PInfty ≫ X.toNormalizedChainComplex R = X.toNormalizedChainComplex R
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma toNormalizedChainComplex_normalizedChainComplexMap :
    X.toNormalizedChainComplex R ≫ normalizedChainComplexMap f R =
      chainComplexMap f R ≫ Y.toNormalizedChainComplex R := by
  simp [normalizedChainComplexMap, ← chainComplexMap_PInfty_assoc]

@[reassoc (attr := simp)]
/-
**SSet.** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ι_normalizedChainComplexMap_f {n : ℕ} (x : X _⦋n⦌) :
    X.ιNormalizedChainComplex x ≫ (normalizedChainComplexMap f R).f n =
      Y.ιNormalizedChainComplex (f.app _ x) := by
  simpa only [comp_f, eval_map, ιNormalizedChainComplex,
    ιChainComplex_toNormalizedChainComplex_f_assoc, ι_chainComplexMap_f_assoc] using
    X.ιChainComplex x ≫=
      (eval _ _ n).congr_map (toNormalizedChainComplex_normalizedChainComplexMap f R)

/-- Given `R : C`, this is the functor `SSet.{w} ⥤ ChainComplex C ℕ` which sends
a simplicial set `X` to `X.normalizedChainComplex R`. -/
@[simps]
/-
**SSet.normalizedChainComplexFunctorObj** 是 Mathlib 中的一个定义，位于命名空间 `SSet`。
形式化陈述：normalizedChainComplexFunctorObj : SSet.{w} ⥤ ChainComplex C Nat where obj
 X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `R : C`, this is the functor `SSet.{w} ⥤ ChainComplex C ℕ` which sends
a simplicial set `X` to `X.normalizedChainComplex R`.
-/
noncomputable def normalizedChainComplexFunctorObj : SSet.{w} ⥤ ChainComplex C ℕ where
  obj X := X.normalizedChainComplex R
  map f := normalizedChainComplexMap f R

set_option backward.defeqAttrib.useBackward true in
/-- The morphism `X.toNormalizedChainComplex R` for any simplicial set `X`,
as a natural transformation. -/
@[simps]
/-
**SSet.toNormalizedChainComplexNatTrans** 是 Mathlib 中的一个定义，位于命名空间 `SSet`。
形式化陈述：toNormalizedChainComplexNatTrans : (chainComplexFunctor C).obj R ⟶ normali
zedChainComplexFunctorObj R where app X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism `X.toNormalizedChainComplex R` for any simplicial set `X`,
as a natural transformation.
-/
noncomputable def toNormalizedChainComplexNatTrans :
    (chainComplexFunctor C).obj R ⟶ normalizedChainComplexFunctorObj R where
  app X := X.toNormalizedChainComplex R

end

section

variable [CategoryWithHomology C]

/-
**SSet.** 是 Mathlib 中的一个实例，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : QuasiIso (X.toNormalizedChainComplex R) :=
  (X.homotopyEquivNormalizedChainComplex R).quasiIso_hom
/-
**SSet.** 是 Mathlib 中的一个实例，位于命名空间 `SSet`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : QuasiIso (X.fromNormalizedChainComplex R) :=
  (X.homotopyEquivNormalizedChainComplex R).quasiIso_inv
/-
**SSet.exactAt_chainComplex_of_hasDimensionLT** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：exactAt_chainComplex_of_hasDimensionLT (n d : Nat) [X.HasDimensionLT d] (h
 : d <= n
参数：n d : Nat。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `exactAt_iff_of_quasiIsoAt`：exactAt_iff_of_quasiIsoAt (f : K ⟶ L) (i : ι)
 [K.HasHomology i] [L.HasHomology i] [QuasiIsoAt f i] : K.ExactAt i ↔ L.ExactAt 
i
· 使用定理 `CategoryTheory.CategoryWithHomology.hasHomology`：∀ {C : Type u} {inst : 
CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphis
ms C}   [self : CategoryTheory.Catego…
· 使用定理 `QuasiIso.quasiIsoAt`：∀ {ι : Type u_1} {C : Type u} {inst : CategoryTheor
y.Category.{v, u} C}   {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C} {c : 
ComplexSh…
· 使用定理 `SSet.instQuasiIsoNatToNormalizedChainComplex`：∀ {C : Type u} [inst : Cat
egoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasCoproducts C] 
  [inst_2 : CategoryTheory.Preaddi…
· 使用定理 `HomologicalComplex.ExactAt.of_isZero`：∀ {C : Type u_1} [inst : CategoryT
heory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]
   {ι : Type u_2} {c : Com…
· 使用引理 `SSet.isZero_normalizedChainComplex_X_of_hasDimensionLT`：isZero_normalize
dChainComplex_X_of_hasDimensionLT (n d : Nat) [X.HasDimensionLT d] (h : d <= n
-/
lemma exactAt_chainComplex_of_hasDimensionLT (n d : ℕ) [X.HasDimensionLT d]
    (h : d ≤ n := by lia) :
    (X.chainComplex R).ExactAt n := by
  rw [exactAt_iff_of_quasiIsoAt (X.toNormalizedChainComplex R)]
  exact .of_isZero (X.isZero_normalizedChainComplex_X_of_hasDimensionLT R n d)
/-
**SSet.isZero_homology_of_hasDimensionLT** 是 Mathlib 中的一个引理，位于命名空间 `SSet`。
形式化陈述：isZero_homology_of_hasDimensionLT (n d : Nat) [X.HasDimensionLT d] (h : d 
<= n
参数：n d : Nat。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `HomologicalComplex.exactAt_iff_isZero_homology`：exactAt_iff_isZero_homol
ogy [K.HasHomology i] : K.ExactAt i ↔ IsZero (K.homology i)
· 使用引理 `SSet.exactAt_chainComplex_of_hasDimensionLT`：exactAt_chainComplex_of_has
DimensionLT (n d : Nat) [X.HasDimensionLT d] (h : d <= n
-/
lemma isZero_homology_of_hasDimensionLT (n d : ℕ) [X.HasDimensionLT d]
    (h : d ≤ n := by lia) :
    IsZero (X.homology R n) := by
  rw [← exactAt_iff_isZero_homology]
  exact X.exactAt_chainComplex_of_hasDimensionLT R n d

end

end SSet

