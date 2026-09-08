/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang, Christian Merten
-/
module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.AlgebraicGeometry.Sites.ConstantSheaf
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.NumberTheory.Padics.PadicIntegers

/-!

# `ℓ`-adic cohomology of a scheme

Let `X` be a scheme and `ℓ` be a prime number. In this file we define the sheaf
associated to the topological group `ℤ_[ℓ]` on the pro-étale site of `X`.
Its cohomology groups are the `ℓ`-adic cohomology groups of `X`.

## Main declarations

- `AlgebraicGeometry.Scheme.ellAdicSheaf`: The sheaf `U ↦ C(U, ℤ_[ℓ])`.
- `AlgebraicGeometry.Scheme.EllAdicCohomology`: The pro-étale cohomology groups `Hⁱ(X, ℤ_[ℓ])`.

## Notes

The `ℓ`-adic cohomology groups of `X : Scheme.{u}` are in `Type (u + 1)`, because
the pro-étale site of `X` has no essentially small subcategory with the same category of sheaves.
Eventually, we will be able to compare the `ℓ`-adic cohomology defined here with the classical
definition using étale cohomology. This will show that the groups defined here are indeed `u`-small.

## References

- [Bhatt, Bhargav and Scholze, Peter, The pro-étale topology for schemes][proetale2015]

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})

/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsGrothendieckAbelian.{u + 1} (Sheaf (ProEt.topology X) Ab.{u + 1}) := by
  -- Without this, lean starts searching for `EssentiallySmall.{max (u + 1) ?v}` and fails.
  have : EssentiallySmall.{u + 1} X.ProEt := inferInstance
  exact Sheaf.isGrothendieckAbelian_of_essentiallySmall (ProEt.topology X) Ab.{u + 1}

/--
The sheaf of continuous maps `U ↦ C(U, ℤ_[ℓ])` on the pro-étale site. This the coefficient
sheaf for `ℓ`-adic cohomology.
[Definition 6.8.1.][proetale2015]
-/
/-
**AlgebraicGeometry.Scheme.ellAdicSheaf** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeom
etry.Scheme`。
形式化陈述：ellAdicSheaf (ℓ : Nat) [Fact ℓ.Prime] : Sheaf (ProEt.topology X) Ab.{u}
参数：ℓ : Nat。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.ProEt.instIsContinuousCompOverForgetForgetTopol
ogyProetaleTopology`：∀ (S : AlgebraicGeometry.Scheme),   ((AlgebraicGeometry.Sch
eme.ProEt.forget S).comp (CategoryTheory.Over.forget S)).IsContinuous     (Algeb
r…

--- 原说明 ---
The sheaf of continuous maps `U ↦ C(U, ℤ_[ℓ])` on the pro-étale site. This the c
oefficient
sheaf for `ℓ`-adic cohomology.
[Definition 6.8.1.][proetale2015]
-/
noncomputable def ellAdicSheaf (ℓ : ℕ) [Fact ℓ.Prime] :
    Sheaf (ProEt.topology X) Ab.{u} :=
  ((ProEt.forget X ⋙ Over.forget _).sheafPushforwardContinuous _ _ proetaleTopology).obj
    ⟨continuousMapPresheafAb (ℤ_[ℓ]), .of_le proetaleTopology_le_fpqcTopology <|
      isSheaf_fpqcTopology_continuousMapPresheafAb _⟩

variable (ℓ : ℕ) [Fact ℓ.Prime]
/-
**AlgebraicGeometry.Scheme.isZero_ellAdicSheaf_of_isEmpty** 是 Mathlib 中的一个引理，位于命
名空间 `AlgebraicGeometry.Scheme`。
形式化陈述：isZero_ellAdicSheaf_of_isEmpty [IsEmpty X] : IsZero (X.ellAdicSheaf ℓ)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsTerminal.isZero`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] [CategoryTheory.Limits.HasZeroMorphisms C] {X : C}   (
hX : CategoryTheory.Limits.Is…
· 使用引理 `AlgebraicGeometry.Scheme.ProEt.topology_eq_top_of_isEmpty`：topology_eq_t
op_of_isEmpty [IsEmpty S] : topology S = ⊤
-/
lemma isZero_ellAdicSheaf_of_isEmpty [IsEmpty X] : IsZero (X.ellAdicSheaf ℓ) :=
  (Sheaf.isTerminalOfEqTop (ProEt.topology_eq_top_of_isEmpty _) _).isZero

/-- `ℓ`-adic cohomology of a scheme in degree `n`. -/
/-
**AlgebraicGeometry.Scheme.EllAdicCohomology** 是 Mathlib 中的一个定义，位于命名空间 `Algebrai
cGeometry.Scheme`。
形式化陈述：EllAdicCohomology (ℓ : Nat) [Fact ℓ.Prime] (n : Nat) : Type (u + 1)
参数：ℓ : Nat；n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ℓ`-adic cohomology of a scheme in degree `n`.
-/
def EllAdicCohomology (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ) : Type (u + 1) :=
  ((sheafCompose _ AddCommGrpCat.uliftFunctor.{u + 1}).obj <| X.ellAdicSheaf ℓ).H n
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ) : AddCommGroup (X.EllAdicCohomology ℓ n) :=
  inferInstanceAs <| AddCommGroup <|
    ((sheafCompose _ AddCommGrpCat.uliftFunctor.{u + 1}).obj <| X.ellAdicSheaf ℓ).H n

/-- `ℓ`-adic cohomology is trivial for the empty scheme. -/
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ℓ`-adic cohomology is trivial for the empty scheme.
-/
instance [IsEmpty X] (n : ℕ) : Subsingleton (X.EllAdicCohomology ℓ n) := by
  apply Sheaf.subsingleton_H_of_isZero
  exact Functor.map_isZero _ (isZero_ellAdicSheaf_of_isEmpty _ _)

end AlgebraicGeometry.Scheme

