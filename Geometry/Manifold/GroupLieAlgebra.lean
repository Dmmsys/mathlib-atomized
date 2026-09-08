/-
Copyright (c) 2024 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Algebra.Lie.Basic
public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import Mathlib.Geometry.Manifold.VectorField.LieBracket

/-!
# The Lie algebra of a Lie group

Given a Lie group, we define `GroupLieAlgebra I G` as its tangent space at the identity, and we
endow it with a Lie bracket, as follows. Given two vectors `v, w : GroupLieAlgebra I G`, consider
the associated left-invariant vector fields `mulInvariantVectorField v` (given at a point `g` by
the image of `v` under the derivative of left-multiplication by `g`) and
`mulInvariantVectorField w`. Then take their Lie bracket at the identity: this is by definition
the bracket of `v` and `w`.

Due to general properties of the Lie bracket of vector fields, this gives a Lie algebra structure
on `GroupLieAlgebra I G`.

Note that one can also define a Lie algebra on the space of left-invariant derivations on `C^∞`
functions (see `LeftInvariantDerivation.instLieAlgebra`). For finite-dimensional `C^∞` real
manifolds, this space of derivations can be canonically identified with the tangent space, and we
recover the same Lie algebra structure (TODO: prove this). In other smoothness classes or on other
fields, this identification is not always true, though, so the derivations point of view does not
work in these settings. Therefore, the point of view in the current file is more general, and
should be favored when possible.

The standing assumption in this file is that the group is `C^n` for `n = minSmoothness 𝕜 3`, i.e.,
it is `C^3` over `ℝ` or `ℂ`, and analytic otherwise.
-/

@[expose] public section

noncomputable section

section LieGroup

open Bundle Filter Function Set
open scoped Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {H : Type*} [TopologicalSpace H] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {I : ModelWithCorners 𝕜 E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]

variable (I G) in
/-- The Lie algebra of a Lie group, i.e., its tangent space at the identity. We use the word
`GroupLieAlgebra` instead of `LieAlgebra` as the latter is taken as a generic class. -/
@[to_additive /-- The Lie algebra of an additive Lie group, i.e., its tangent space at zero. We use
the word `AddGroupLieAlgebra` instead of `LieAlgebra` as the latter is taken as a generic class. -/]
/-
**GroupLieAlgebra** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：GroupLieAlgebra : Type _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
abbrev GroupLieAlgebra : Type _ := TangentSpace% (1 : G)

/-- The invariant vector field associated to a vector `v` in the Lie algebra. At a point `g`, it
is given by the image of `v` under left-multiplication by `g`. -/
@[to_additive /-- The invariant vector field associated to a vector `v` in the Lie algebra. At a
point `g`, it is given by the image of `v` under left-addition by `g`. -/]
/-
**mulInvariantVectorField** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：mulInvariantVectorField (v : GroupLieAlgebra I G) (g : G) : TangentSpace% 
g
参数：v : GroupLieAlgebra I G；g : G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def mulInvariantVectorField (v : GroupLieAlgebra I G) (g : G) : TangentSpace% g :=
  mfderiv% (g * ·) (1 : G) v

set_option backward.isDefEq.respectTransparency false in
@[to_additive]
/-
**mulInvariantVectorField_add** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mulInvariantVectorField_add (v w : GroupLieAlgebra I G) : mulInvariantVect
orField (v + w) = mulInvariantVectorField v + mulInvariantVectorField w
参数：v w : GroupLieAlgebra I G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mulInvariantVectorField_add (v w : GroupLieAlgebra I G) :
    mulInvariantVectorField (v + w) = mulInvariantVectorField v + mulInvariantVectorField w := by
  ext g
  simp [mulInvariantVectorField]

set_option backward.isDefEq.respectTransparency false in
/- `to_additive` fails on the next lemma, as it tries to additivize `smul` while it shouldn't.
Therefore, we state and prove by hand the additive version. -/
/-
**addInvariantVectorField_smul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：addInvariantVectorField_smul {G : Type*} [TopologicalSpace G] [ChartedSpac
e H G] [AddGroup G] (c : 𝕜) (v : AddGroupLieAlgebra I G) : addInvariantVectorFie
ld (c • v) = c • addInvariantVectorField v
参数：c : 𝕜；v : AddGroupLieAlgebra I G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`to_additive` fails on the next lemma, as it tries to additivize `smul` while it
 shouldn't.
Therefore, we state and prove by hand the additive version.
-/
lemma addInvariantVectorField_smul {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [AddGroup G]
    (c : 𝕜) (v : AddGroupLieAlgebra I G) :
    addInvariantVectorField (c • v) = c • addInvariantVectorField v := by
  ext g
  simp [addInvariantVectorField]

set_option backward.isDefEq.respectTransparency false in
/-
**mulInvariantVectorField_smul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mulInvariantVectorField_smul (c : 𝕜) (v : GroupLieAlgebra I G) : mulInvari
antVectorField (c • v) = c • mulInvariantVectorField v
参数：c : 𝕜；v : GroupLieAlgebra I G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mulInvariantVectorField_smul (c : 𝕜) (v : GroupLieAlgebra I G) :
    mulInvariantVectorField (c • v) = c • mulInvariantVectorField v := by
  ext g
  simp [mulInvariantVectorField]

open VectorField

/-- The Lie bracket of two vectors `v` and `w` in the Lie algebra of a Lie group is obtained by
taking the Lie bracket of the associated invariant vector fields, at the identity. -/
@[to_additive /-- The Lie bracket of two vectors `v` and `w` in the Lie algebra of an additive Lie
group is obtained by taking the Lie bracket of the associated invariant vector fields, at zero. -/]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : Bracket (GroupLieAlgebra I G) (GroupLieAlgebra I G) where
  bracket v w := mlieBracket I (mulInvariantVectorField v) (mulInvariantVectorField w) (1 : G)

@[to_additive]
/-
**GroupLieAlgebra.bracket_def** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：GroupLieAlgebra.bracket_def (v w : GroupLieAlgebra I G) : ⁅v, w⁆ = mlieBra
cket I (mulInvariantVectorField v) (mulInvariantVectorField w) (1 : G)
参数：v w : GroupLieAlgebra I G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma GroupLieAlgebra.bracket_def (v w : GroupLieAlgebra I G) :
    ⁅v, w⁆ = mlieBracket I (mulInvariantVectorField v) (mulInvariantVectorField w) (1 : G) := rfl

variable [LieGroup I (minSmoothness 𝕜 3) G]

@[to_additive (attr := simp)]
/-
**inverse_mfderiv_mul_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：inverse_mfderiv_mul_left {g h : G} : (mfderiv% (fun b => g * b) h).inverse
 = mfderiv% (fun b => g⁻¹ * b) (g * h)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `instNoZeroDivisorsENat`：NoZeroDivisors ℕ∞
· 使用定理 `instNontrivialENat`：Nontrivial ℕ∞
· 使用定理 `WithTop.nontrivial`：∀ {α : Type u_1} [Nonempty α], Nontrivial (WithTop α
)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用引理 `le_minSmoothness`：le_minSmoothness {n : Nat∞ω} : n <= minSmoothness 𝕜 n
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_mul_cancel_left`：inv_mul_cancel_left (a b : G) : a⁻¹ * (a * b) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `id_eq`：∀ {α : Sort u_1} (a : α), id a = a
· 使用定理 `mfderiv_id`：mfderiv_id : mfderiv% (@id M) x = ContinuousLinearMap.id 𝕜 (
TangentSpace% x)
· 使用定理 `mul_inv_cancel_left`：mul_inv_cancel_left (a b : G) : a * (a⁻¹ * b) = b
· 使用引理 `ContinuousLinearMap.inverse_eq`：inverse_eq {f : M ->L[R] M₂} {g : M₂ ->L
[R] M} (hf : f ∘L g = .id R M₂) (hg : g ∘L f = .id R M) : f.inverse = g
· 使用定理 `mfderiv_comp`：mfderiv_comp (hg : MDiffAt g (f x)) (hf : MDiffAt f x) : m
fderiv% (g ∘ f) x = (mfderiv% g (f x)).comp (mfderiv% f x)
· 使用定理 `ContMDiffAt.mdifferentiableAt`：ContMDiffAt.mdifferentiableAt (hf : CMDif
fAt n f x) (hn : n != 0) : MDiffAt f x
· 使用定理 `ContMDiff.contMDiffAt`：ContMDiff.contMDiffAt (h : ContMDiff I I' n f) : 
ContMDiffAt I I' n f x
· 使用定理 `contMDiff_mul_left`：contMDiff_mul_left {a : G} : CMDiff n (a * ·)
· 使用定理 `LieGroup.toContMDiffMul`：∀ {𝕜 : Type u_1} {inst : NontriviallyNormedFiel
d 𝕜} {H : Type u_2} {inst_1 : TopologicalSpace H} {E : Type u_3}   {inst_2 : Nor
medAddCommGro…
-/
lemma inverse_mfderiv_mul_left {g h : G} :
    (mfderiv% (fun b ↦ g * b) h).inverse = mfderiv% (fun b ↦ g⁻¹ * b) (g * h) := by
  have M : minSmoothness 𝕜 3 ≠ 0 := lt_of_lt_of_le (by simp) le_minSmoothness |>.ne'
  have A : mfderiv% ((fun x ↦ g⁻¹ * x) ∘ (fun x ↦ g * x)) h =
      ContinuousLinearMap.id _ _ := by
    have : (fun x ↦ g⁻¹ * x) ∘ (fun x ↦ g * x) = id := by ext x; simp
    rw [this, id_eq, mfderiv_id]
  rw [mfderiv_comp (I' := I) _ (contMDiff_mul_left.contMDiffAt.mdifferentiableAt M)
    (contMDiff_mul_left.contMDiffAt.mdifferentiableAt M)] at A
  have A' : mfderiv% ((fun x ↦ g * x) ∘ (fun x ↦ g⁻¹ * x)) (g * h) =
      ContinuousLinearMap.id _ _ := by
    have : (fun x ↦ g * x) ∘ (fun x ↦ g⁻¹ * x) = id := by ext x; simp
    rw [this, id_eq, mfderiv_id]
  rw [mfderiv_comp (I' := I) _ (contMDiff_mul_left.contMDiffAt.mdifferentiableAt M)
    (contMDiff_mul_left.contMDiffAt.mdifferentiableAt M), inv_mul_cancel_left g h] at A'
  exact ContinuousLinearMap.inverse_eq A' A

/-- Invariant vector fields are invariant under pullbacks. -/
@[to_additive /-- Invariant vector fields are invariant under pullbacks. -/]
/-
**mpullback_mulInvariantVectorField** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mpullback_mulInvariantVectorField (g : G) (v : GroupLieAlgebra I G) : mpul
lback I I (g * ·) (mulInvariantVectorField v) = mulInvariantVectorField v
参数：g : G；v : GroupLieAlgebra I G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `instNoZeroDivisorsENat`：NoZeroDivisors ℕ∞
· 使用定理 `instNontrivialENat`：Nontrivial ℕ∞
· 使用定理 `WithTop.nontrivial`：∀ {α : Type u_1} [Nonempty α], Nontrivial (WithTop α
)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用引理 `le_minSmoothness`：le_minSmoothness {n : Nat∞ω} : n <= minSmoothness 𝕜 n
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `inverse_mfderiv_mul_left`：inverse_mfderiv_mul_left {g h : G} : (mfderiv%
 (fun b => g * b) h).inverse = mfderiv% (fun b => g⁻¹ * b) (g * h)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
· 使用定理 `zpow_zero`：∀ {G : Type u_1} [inst : DivInvMonoid G] (a : G), a ^ 0 = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `mfderiv_comp`：mfderiv_comp (hg : MDiffAt g (f x)) (hf : MDiffAt f x) : m
fderiv% (g ∘ f) x = (mfderiv% g (f x)).comp (mfderiv% f x)
· 使用定理 `ContMDiffAt.mdifferentiableAt`：ContMDiffAt.mdifferentiableAt (hf : CMDif
fAt n f x) (hn : n != 0) : MDiffAt f x
· 使用定理 `ContMDiff.contMDiffAt`：ContMDiff.contMDiffAt (h : ContMDiff I I' n f) : 
ContMDiffAt I I' n f x
· 使用定理 `contMDiff_mul_left`：contMDiff_mul_left {a : G} : CMDiff n (a * ·)
· 使用定理 `LieGroup.toContMDiffMul`：∀ {𝕜 : Type u_1} {inst : NontriviallyNormedFiel
d 𝕜} {H : Type u_2} {inst_1 : TopologicalSpace H} {E : Type u_3}   {inst_2 : Nor
medAddCommGro…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a

--- 原说明 ---
Invariant vector fields are invariant under pullbacks.
-/
lemma mpullback_mulInvariantVectorField (g : G) (v : GroupLieAlgebra I G) :
    mpullback I I (g * ·) (mulInvariantVectorField v) = mulInvariantVectorField v := by
  have M : minSmoothness 𝕜 3 ≠ 0 := lt_of_lt_of_le (by simp) le_minSmoothness |>.ne'
  ext h
  simp only [mpullback, inverse_mfderiv_mul_left, mulInvariantVectorField]
  have D : (fun x ↦ h * x) = (fun b ↦ g⁻¹ * b) ∘ (fun x ↦ g * h * x) := by
    ext x; simp only [comp_apply]; group
  rw [D, mfderiv_comp (I' := I)]
  · congr 2
    simp
  · exact contMDiff_mul_left.contMDiffAt.mdifferentiableAt M
  · exact contMDiff_mul_left.contMDiffAt.mdifferentiableAt M

set_option backward.isDefEq.respectTransparency false in
@[to_additive]
/-
**mulInvariantVectorField_eq_mpullback** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mulInvariantVectorField_eq_mpullback (g : G) (V : Π (g : G), TangentSpace%
 g) : mulInvariantVectorField (V 1) g = mpullback I I (g⁻¹ * ·) V g
参数：g : G；V : Π (g : G), TangentSpace% g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_mul_cancel`：inv_mul_cancel (a : G) : a⁻¹ * a = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `inverse_mfderiv_mul_left`：inverse_mfderiv_mul_left {g h : G} : (mfderiv%
 (fun b => g * b) h).inverse = mfderiv% (fun b => g⁻¹ * b) (g * h)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
-/
lemma mulInvariantVectorField_eq_mpullback (g : G) (V : Π (g : G), TangentSpace% g) :
    mulInvariantVectorField (V 1) g = mpullback I I (g⁻¹ * ·) V g := by
  have A : 1 = g⁻¹ * g := by simp
  simp only [mulInvariantVectorField, mpullback, inverse_mfderiv_mul_left]
  congr
  simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[to_additive]
/-
**contMDiff_mulInvariantVectorField** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiff_mulInvariantVectorField (v : GroupLieAlgebra I G) : CMDiff (minS
moothness 𝕜 2) (fun (g : G) => (mulInvariantVectorField v g : TangentBundle I G)
)
参数：v : GroupLieAlgebra I G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `instNoZeroDivisorsENat`：NoZeroDivisors ℕ∞
· 使用定理 `instNontrivialENat`：Nontrivial ℕ∞
· 使用定理 `WithTop.nontrivial`：∀ {α : Type u_1} [Nonempty α], Nontrivial (WithTop α
)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用引理 `le_minSmoothness`：le_minSmoothness {n : Nat∞ω} : n <= minSmoothness 𝕜 n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `minSmoothness_add`：minSmoothness_add {n m : Nat∞ω} : minSmoothness 𝕜 (n 
+ m) = minSmoothness 𝕜 n + m
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_eq`：∀ {α : Type u} [inst : AddMonoidWithOn
e α] {n : ℕ} {a a' : α}, Mathlib.Meta.NormNum.IsNat a n → ↑n = a' → a = a'
· 使用定理 `Mathlib.Meta.NormNum.isNat_add`：∀ {α : Type u_1} [inst : AddMonoidWithOn
e α] {f : α → α → α} {a b : α} {a' b' c : ℕ},   f = HAdd.hAdd →     Mathlib.Meta
.NormNum.IsNat a a' …
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `instIsManifoldOfNatWithTopENatOfMinSmoothness_1`：∀ {𝕜 : Type u_1} [inst 
: NontriviallyNormedField 𝕜] {H : Type u_2} [inst_1 : TopologicalSpace H] {E : T
ype u_3}   [inst_2 : NormedAddCommGro…
· 使用定理 `instIsManifoldMinSmoothnessOfNatWithTopENat_1`：∀ {𝕜 : Type u_1} [inst : 
NontriviallyNormedField 𝕜] {H : Type u_2} [inst_1 : TopologicalSpace H] {E : Typ
e u_3}   [inst_2 : NormedAddCommGro…
· 使用定理 `instIsManifoldMinSmoothnessOfNatWithTopENat`：∀ {𝕜 : Type u_1} [inst : No
ntriviallyNormedField 𝕜] {H : Type u_2} [inst_1 : TopologicalSpace H] {E : Type 
u_3}   [inst_2 : NormedAddCommGro…
· 使用定理 `ContMDiffMul.toIsManifold`：∀ {𝕜 : Type u_1} {inst : NontriviallyNormedFi
eld 𝕜} {H : Type u_2} {inst_1 : TopologicalSpace H} {E : Type u_3}   {inst_2 : N
ormedAddCommGro…
· 使用定理 `LieGroup.toContMDiffMul`：∀ {𝕜 : Type u_1} {inst : NontriviallyNormedFiel
d 𝕜} {H : Type u_2} {inst_1 : TopologicalSpace H} {E : Type u_3}   {inst_2 : Nor
medAddCommGro…
· 使用定理 `Bundle.contMDiff_zeroSection`：contMDiff_zeroSection : ContMDiff IB (IB.p
rod 𝓘(𝕜, F)) n (zeroSection F E)
· 使用定理 `contMDiff_const`：contMDiff_const : ContMDiff I I' n fun _ : M => c
（共 49 条，此处仅展示前 30 条）
-/
theorem contMDiff_mulInvariantVectorField (v : GroupLieAlgebra I G) :
    CMDiff (minSmoothness 𝕜 2)
      (fun (g : G) ↦ (mulInvariantVectorField v g : TangentBundle I G)) := by
  /- We will write the desired map as a composition of obviously smooth maps.
  The derivative of the product `P : (g, h) ↦ g * h` is given by
  `DP (g, h) ⬝ (u, v) = DL_g v + DR_h u`, where `L_g` and `R_h` are respectively left and right
  multiplication by `g` and `h`. As `P` is smooth, so is `DP`.
  Consider the map `F₁ : M → T (M × M)` mapping `g` to `(0, v) ∈ T_(g, e) (M × M)`. Then the
  composition of `DP` with `F₁` maps `g` to `DL_g v ∈ T_g M`, thanks to the above formula. This
  is the desired invariant vector field. Since both `DP` and `F₁` are smooth, their composition is
  smooth as desired.
  There is a small abuse of notation in the above argument, where we have identified `T (M × M)`
  and `TM × TM`. In the formal proof, we need to introduce this identification, called `F₂` below,
  which is also already known to be smooth. -/
  have M : minSmoothness 𝕜 3 ≠ 0 := lt_of_lt_of_le (by simp) le_minSmoothness |>.ne'
  have A : minSmoothness 𝕜 2 + 1 = minSmoothness 𝕜 3 := by
    rw [← minSmoothness_add]
    norm_num
  let fg : G → TangentBundle I G := fun g ↦ TotalSpace.mk' E g 0
  have sfg : CMDiff (minSmoothness 𝕜 2) fg := contMDiff_zeroSection _ _
  let fv : G → TangentBundle I G := fun _ ↦ TotalSpace.mk' E 1 v
  have sfv : CMDiff (minSmoothness 𝕜 2) fv := contMDiff_const
  let F₁ : G → (TangentBundle I G × TangentBundle I G) := fun g ↦ (fg g, fv g)
  have S₁ : CMDiff (minSmoothness 𝕜 2) F₁ := sfg.prodMk sfv
  let F₂ : (TangentBundle I G × TangentBundle I G) → TangentBundle (I.prod I) (G × G) :=
    (equivTangentBundleProd I G I G).symm
  have S₂ : CMDiff (minSmoothness 𝕜 2) F₂ := contMDiff_equivTangentBundleProd_symm
  let F₃ : TangentBundle (I.prod I) (G × G) → TangentBundle I G :=
    tangentMap% (fun (p : G × G) ↦ p.1 * p.2)
  have S₃ : CMDiff (minSmoothness 𝕜 2) F₃ := by
    apply ContMDiff.contMDiff_tangentMap _ (m := minSmoothness 𝕜 2) le_rfl
    rw [A]
    exact contMDiff_mul I (minSmoothness 𝕜 3)
  let S := (S₃.comp S₂).comp S₁
  convert! S with g
  · simp [F₁, F₂, F₃, fg, fv]
  · simp only [comp_apply, tangentMap, F₃, F₂, F₁, fg, fv]
    rw [mfderiv_prod_eq_add_apply ((contMDiff_mul I (minSmoothness 𝕜 3)).mdifferentiableAt M)]
    simp +instances [mulInvariantVectorField]

@[to_additive]
/-
**contMDiffAt_mulInvariantVectorField** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffAt_mulInvariantVectorField (v : GroupLieAlgebra I G) {g : G} : CM
DiffAt (minSmoothness 𝕜 2) (fun (g : G) => (mulInvariantVectorField v g : Tangen
tBundle I G)) g
参数：v : GroupLieAlgebra I G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `ContMDiff.contMDiffAt`：ContMDiff.contMDiffAt (h : ContMDiff I I' n f) : 
ContMDiffAt I I' n f x
· 使用定理 `instIsManifoldOfNatWithTopENatOfMinSmoothness_1`：∀ {𝕜 : Type u_1} [inst 
: NontriviallyNormedField 𝕜] {H : Type u_2} [inst_1 : TopologicalSpace H] {E : T
ype u_3}   [inst_2 : NormedAddCommGro…
· 使用定理 `instIsManifoldMinSmoothnessOfNatWithTopENat_1`：∀ {𝕜 : Type u_1} [inst : 
NontriviallyNormedField 𝕜] {H : Type u_2} [inst_1 : TopologicalSpace H] {E : Typ
e u_3}   [inst_2 : NormedAddCommGro…
· 使用定理 `instIsManifoldMinSmoothnessOfNatWithTopENat`：∀ {𝕜 : Type u_1} [inst : No
ntriviallyNormedField 𝕜] {H : Type u_2} [inst_1 : TopologicalSpace H] {E : Type 
u_3}   [inst_2 : NormedAddCommGro…
· 使用定理 `ContMDiffMul.toIsManifold`：∀ {𝕜 : Type u_1} {inst : NontriviallyNormedFi
eld 𝕜} {H : Type u_2} {inst_1 : TopologicalSpace H} {E : Type u_3}   {inst_2 : N
ormedAddCommGro…
· 使用定理 `LieGroup.toContMDiffMul`：∀ {𝕜 : Type u_1} {inst : NontriviallyNormedFiel
d 𝕜} {H : Type u_2} {inst_1 : TopologicalSpace H} {E : Type u_3}   {inst_2 : Nor
medAddCommGro…
· 使用定理 `contMDiff_mulInvariantVectorField`：contMDiff_mulInvariantVectorField (v 
: GroupLieAlgebra I G) : CMDiff (minSmoothness 𝕜 2) (fun (g : G) => (mulInvarian
tVectorField v g : Tang…
-/
theorem contMDiffAt_mulInvariantVectorField (v : GroupLieAlgebra I G) {g : G} :
    CMDiffAt (minSmoothness 𝕜 2)
      (fun (g : G) ↦ (mulInvariantVectorField v g : TangentBundle I G)) g :=
  (contMDiff_mulInvariantVectorField v).contMDiffAt

@[to_additive]
/-
**mdifferentiable_mulInvariantVectorField** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mdifferentiable_mulInvariantVectorField (v : GroupLieAlgebra I G) : MDiff 
(fun (g : G) => (mulInvariantVectorField v g : TangentBundle I G))
参数：v : GroupLieAlgebra I G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `ContMDiff.mdifferentiable`：ContMDiff.mdifferentiable (hf : CMDiff n f) (
hn : n != 0) : MDiff f
· 使用定理 `instIsManifoldOfNatWithTopENatOfMinSmoothness_1`：∀ {𝕜 : Type u_1} [inst 
: NontriviallyNormedField 𝕜] {H : Type u_2} [inst_1 : TopologicalSpace H] {E : T
ype u_3}   [inst_2 : NormedAddCommGro…
· 使用定理 `instIsManifoldMinSmoothnessOfNatWithTopENat_1`：∀ {𝕜 : Type u_1} [inst : 
NontriviallyNormedField 𝕜] {H : Type u_2} [inst_1 : TopologicalSpace H] {E : Typ
e u_3}   [inst_2 : NormedAddCommGro…
· 使用定理 `instIsManifoldMinSmoothnessOfNatWithTopENat`：∀ {𝕜 : Type u_1} [inst : No
ntriviallyNormedField 𝕜] {H : Type u_2} [inst_1 : TopologicalSpace H] {E : Type 
u_3}   [inst_2 : NormedAddCommGro…
· 使用定理 `ContMDiffMul.toIsManifold`：∀ {𝕜 : Type u_1} {inst : NontriviallyNormedFi
eld 𝕜} {H : Type u_2} {inst_1 : TopologicalSpace H} {E : Type u_3}   {inst_2 : N
ormedAddCommGro…
· 使用定理 `LieGroup.toContMDiffMul`：∀ {𝕜 : Type u_1} {inst : NontriviallyNormedFiel
d 𝕜} {H : Type u_2} {inst_1 : TopologicalSpace H} {E : Type u_3}   {inst_2 : Nor
medAddCommGro…
· 使用定理 `contMDiff_mulInvariantVectorField`：contMDiff_mulInvariantVectorField (v 
: GroupLieAlgebra I G) : CMDiff (minSmoothness 𝕜 2) (fun (g : G) => (mulInvarian
tVectorField v g : Tang…
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `instNoZeroDivisorsENat`：NoZeroDivisors ℕ∞
· 使用定理 `instNontrivialENat`：Nontrivial ℕ∞
· 使用定理 `WithTop.nontrivial`：∀ {α : Type u_1} [Nonempty α], Nontrivial (WithTop α
)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用引理 `le_minSmoothness`：le_minSmoothness {n : Nat∞ω} : n <= minSmoothness 𝕜 n
-/
theorem mdifferentiable_mulInvariantVectorField (v : GroupLieAlgebra I G) :
    MDiff (fun (g : G) ↦ (mulInvariantVectorField v g : TangentBundle I G)) :=
  (contMDiff_mulInvariantVectorField v).mdifferentiable
    (lt_of_lt_of_le (by simp) le_minSmoothness).ne'

@[to_additive]
/-
**mdifferentiableAt_mulInvariantVectorField** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mdifferentiableAt_mulInvariantVectorField (v : GroupLieAlgebra I G) {g : G
} : MDiffAt (fun (g : G) => (mulInvariantVectorField v g : TangentBundle I G)) g
参数：v : GroupLieAlgebra I G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `ContMDiffAt.mdifferentiableAt`：ContMDiffAt.mdifferentiableAt (hf : CMDif
fAt n f x) (hn : n != 0) : MDiffAt f x
· 使用定理 `instIsManifoldOfNatWithTopENatOfMinSmoothness_1`：∀ {𝕜 : Type u_1} [inst 
: NontriviallyNormedField 𝕜] {H : Type u_2} [inst_1 : TopologicalSpace H] {E : T
ype u_3}   [inst_2 : NormedAddCommGro…
· 使用定理 `instIsManifoldMinSmoothnessOfNatWithTopENat_1`：∀ {𝕜 : Type u_1} [inst : 
NontriviallyNormedField 𝕜] {H : Type u_2} [inst_1 : TopologicalSpace H] {E : Typ
e u_3}   [inst_2 : NormedAddCommGro…
· 使用定理 `instIsManifoldMinSmoothnessOfNatWithTopENat`：∀ {𝕜 : Type u_1} [inst : No
ntriviallyNormedField 𝕜] {H : Type u_2} [inst_1 : TopologicalSpace H] {E : Type 
u_3}   [inst_2 : NormedAddCommGro…
· 使用定理 `ContMDiffMul.toIsManifold`：∀ {𝕜 : Type u_1} {inst : NontriviallyNormedFi
eld 𝕜} {H : Type u_2} {inst_1 : TopologicalSpace H} {E : Type u_3}   {inst_2 : N
ormedAddCommGro…
· 使用定理 `LieGroup.toContMDiffMul`：∀ {𝕜 : Type u_1} {inst : NontriviallyNormedFiel
d 𝕜} {H : Type u_2} {inst_1 : TopologicalSpace H} {E : Type u_3}   {inst_2 : Nor
medAddCommGro…
· 使用定理 `contMDiffAt_mulInvariantVectorField`：contMDiffAt_mulInvariantVectorField
 (v : GroupLieAlgebra I G) {g : G} : CMDiffAt (minSmoothness 𝕜 2) (fun (g : G) =
> (mulInvariantVectorFiel…
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `instNoZeroDivisorsENat`：NoZeroDivisors ℕ∞
· 使用定理 `instNontrivialENat`：Nontrivial ℕ∞
· 使用定理 `WithTop.nontrivial`：∀ {α : Type u_1} [Nonempty α], Nontrivial (WithTop α
)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用引理 `le_minSmoothness`：le_minSmoothness {n : Nat∞ω} : n <= minSmoothness 𝕜 n
-/
theorem mdifferentiableAt_mulInvariantVectorField (v : GroupLieAlgebra I G) {g : G} :
    MDiffAt (fun (g : G) ↦ (mulInvariantVectorField v g : TangentBundle I G)) g :=
  (contMDiffAt_mulInvariantVectorField v).mdifferentiableAt
    (lt_of_lt_of_le (by simp) le_minSmoothness).ne'

open VectorField

variable [CompleteSpace E]

/-- The invariant vector field associated to the value at the identity of the Lie bracket of
two invariant vector fields, is everywhere the Lie bracket of the invariant vector fields. -/
@[to_additive /-- The invariant vector field associated to the value at zero of the Lie
bracket of two invariant vector fields, is everywhere the Lie bracket of the invariant vector
fields. -/]
/-
**mulInvariantVector_mlieBracket** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mulInvariantVector_mlieBracket (v w : GroupLieAlgebra I G) : mulInvariantV
ectorField (mlieBracket I (mulInvariantVectorField v) (mulInvariantVectorField w
) 1) = mlieBracket I (mulInvariantVectorField v) (mulInvariantVectorField w)
参数：v w : GroupLieAlgebra I G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `mulInvariantVectorField_eq_mpullback`：mulInvariantVectorField_eq_mpullba
ck (g : G) (V : Π (g : G), TangentSpace% g) : mulInvariantVectorField (V 1) g = 
mpullback I I (g⁻¹ * ·) V …
· 使用引理 `VectorField.mpullback_mlieBracket`：mpullback_mlieBracket {f : M -> M'} {
V W : Π (x : M'), TangentSpace I' x} {x₀ : M} (hV : MDiffAt (T% V) (f x₀)) (hW :
 MDiffAt (T% W) (f x₀))…
· 使用定理 `instIsManifoldMinSmoothnessOfNatWithTopENat`：∀ {𝕜 : Type u_1} [inst : No
ntriviallyNormedField 𝕜] {H : Type u_2} [inst_1 : TopologicalSpace H] {E : Type 
u_3}   [inst_2 : NormedAddCommGro…
· 使用定理 `ContMDiffMul.toIsManifold`：∀ {𝕜 : Type u_1} {inst : NontriviallyNormedFi
eld 𝕜} {H : Type u_2} {inst_1 : TopologicalSpace H} {E : Type u_3}   {inst_2 : N
ormedAddCommGro…
· 使用定理 `LieGroup.toContMDiffMul`：∀ {𝕜 : Type u_1} {inst : NontriviallyNormedFiel
d 𝕜} {H : Type u_2} {inst_1 : TopologicalSpace H} {E : Type u_3}   {inst_2 : Nor
medAddCommGro…
· 使用定理 `mdifferentiableAt_mulInvariantVectorField`：mdifferentiableAt_mulInvarian
tVectorField (v : GroupLieAlgebra I G) {g : G} : MDiffAt (fun (g : G) => (mulInv
ariantVectorField v g : Tangent…
· 使用定理 `contMDiffAt_mul_left`：contMDiffAt_mul_left {a b : G} : CMDiffAt n (a * ·
) b
· 使用引理 `minSmoothness_monotone`：minSmoothness_monotone : Monotone (minSmoothness
 𝕜)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LinearOrderedAddCommMonoidWithTop.toIsOrderedAddMonoid`：∀ {α : Type u_3}
 [self : LinearOrderedAddCommMonoidWithTop α], IsOrderedAddMonoid α
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用引理 `mpullback_mulInvariantVectorField`：mpullback_mulInvariantVectorField (g 
: G) (v : GroupLieAlgebra I G) : mpullback I I (g * ·) (mulInvariantVectorField 
v) = mulInvariantVector…
-/
lemma mulInvariantVector_mlieBracket (v w : GroupLieAlgebra I G) :
    mulInvariantVectorField
      (mlieBracket I (mulInvariantVectorField v) (mulInvariantVectorField w) 1) =
    mlieBracket I (mulInvariantVectorField v) (mulInvariantVectorField w) := by
  ext g
  rw [mulInvariantVectorField_eq_mpullback, mpullback_mlieBracket (n := minSmoothness 𝕜 3),
    mpullback_mulInvariantVectorField, mpullback_mulInvariantVectorField]
  · exact mdifferentiableAt_mulInvariantVectorField _
  · exact mdifferentiableAt_mulInvariantVectorField _
  · exact contMDiffAt_mul_left
  · exact minSmoothness_monotone (by norm_cast)

/-- The tangent space at the identity of a Lie group is a Lie ring, for the bracket
given by the Lie bracket of invariant vector fields. -/
@[to_additive /-- The tangent space at the identity of an additive Lie group is a Lie ring, for the
bracket given by the Lie bracket of invariant vector fields. -/]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : LieRing (GroupLieAlgebra I G) where
  add_lie u v w := by
    simp only [GroupLieAlgebra.bracket_def, mulInvariantVectorField_add]
    rw [mlieBracket_add_left]
    · exact mdifferentiableAt_mulInvariantVectorField _
    · exact mdifferentiableAt_mulInvariantVectorField _
  lie_add u v w := by
    simp only [GroupLieAlgebra.bracket_def, mulInvariantVectorField_add]
    rw [mlieBracket_add_right]
    · exact mdifferentiableAt_mulInvariantVectorField _
    · exact mdifferentiableAt_mulInvariantVectorField _
  lie_self v := by simp [GroupLieAlgebra.bracket_def]
  leibniz_lie u v w := by
    simp only [GroupLieAlgebra.bracket_def, mulInvariantVector_mlieBracket]
    apply leibniz_identity_mlieBracket_apply <;>
      exact contMDiff_mulInvariantVectorField _ _

/- `to_additive` fails on the next instance, as it tries to additivize `smul` while it shouldn't.
Therefore, we state and prove by hand the additive version. -/

/-- The tangent space at the identity of an additive Lie group is a Lie algebra, for the bracket
given by the Lie bracket of invariant vector fields. -/
/-
**instLieAlgebraAddGroupLieAlgebra** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：instLieAlgebraAddGroupLieAlgebra {G : Type*} [TopologicalSpace G] [Charted
Space H G] [AddGroup G] [LieAddGroup I (minSmoothness 𝕜 3) G] : LieAlgebra 𝕜 (Ad
dGroupLieAlgebra I G) where lie_smul c v w
参数：minSmoothness 𝕜 3。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The tangent space at the identity of an additive Lie group is a Lie algebra, for
 the bracket
given by the Lie bracket of invariant vector fields.
-/
noncomputable instance instLieAlgebraAddGroupLieAlgebra
    {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [AddGroup G]
    [LieAddGroup I (minSmoothness 𝕜 3) G] : LieAlgebra 𝕜 (AddGroupLieAlgebra I G) where
  lie_smul c v w := by
    simp only [AddGroupLieAlgebra.bracket_def, addInvariantVectorField_smul]
    rw [mlieBracket_const_smul_right]
    exact mdifferentiableAt_addInvariantVectorField _

/-- The tangent space at the identity of a Lie group is a Lie algebra, for the bracket
given by the Lie bracket of invariant vector fields. -/
/-
**instLieAlgebraGroupLieAlgebra** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：instLieAlgebraGroupLieAlgebra : LieAlgebra 𝕜 (GroupLieAlgebra I G) where l
ie_smul c v w
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The tangent space at the identity of a Lie group is a Lie algebra, for the brack
et
given by the Lie bracket of invariant vector fields.
-/
noncomputable instance instLieAlgebraGroupLieAlgebra : LieAlgebra 𝕜 (GroupLieAlgebra I G) where
  lie_smul c v w := by
    simp only [GroupLieAlgebra.bracket_def, mulInvariantVectorField_smul]
    rw [mlieBracket_const_smul_right]
    exact mdifferentiableAt_mulInvariantVectorField _

end LieGroup

