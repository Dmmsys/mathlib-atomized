/-
Copyright (c) 2025 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.CStarAlgebra.Exponential
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic

/-! # The unitary group in a unital C⋆-algebra is locally path connected

When `A` is a unital C⋆-algebra and `u : unitary A` is a unitary element whose distance to `1` is
less that `2`, the spectrum of `u` is contained in the slit plane, so the principal branch of the
logarithm is continuous on the spectrum of `u` (or equivalently, `Complex.arg` is continuous on the
spectrum). The continuous functional calculus can then be used to define a selfadjoint element `x`
such that `u = exp (I • x)`. Moreover, there is a relatively nice relationship between the norm of
`x` and the norm of `u - 1`, namely `‖u - 1‖ ^ 2 = 2 * (1 - cos ‖x‖)`. In fact, these maps `u ↦ x`
and `x ↦ u` establish a partial homeomorphism between `ball (1 : unitary A) 2` and
`ball (0 : selfAdjoint A) π`.

The map `t ↦ exp (t • (I • x))` constitutes a path from `1` to `u`, showing that unitary elements
sufficiently close (i.e., within a distance `2`) to `1 : unitary A` are path connected to `1`.
This property can be translated around the unitary group to show that if `u v : unitary A` are
unitary elements with `‖u - v‖ < 2`, then there is a path joining them. In fact, this path has the
property that it lies within `closedBall u ‖u - v‖`, and consequently any ball of radius `δ < 2` in
`unitary A` is path connected. Therefore, the unitary group is locally path connected.

Finally, we provide the standard characterization of the path component of `1 : unitary A` as finite
products of exponential unitaries.

## Main results

+ `Unitary.argSelfAdjoint`: the selfadjoint element obtained by taking the argument (using the
  principal branch and the continuous functional calculus) of a unitary. This returns `0` if
  the principal branch of the logarithm is not continuous on the spectrum of the unitary element.
+ `selfAdjoint.norm_sq_expUnitary_sub_one`:
  `‖(selfAdjoint.expUnitary x - 1 : A)‖ ^ 2 = 2 * (1 - Real.cos ‖x‖)`
+ `Unitary.norm_argSelfAdjoint`:
  `‖Unitary.argSelfAdjoint u‖ = Real.arccos (1 - ‖(u - 1 : A)‖ ^ 2 / 2)`
+ `Unitary.openPartialHomeomorph`: the maps `Unitary.argSelfAdjoint` and `selfAdjoint.expUnitary`
  form a partial homeomorphism between `ball (1 : unitary A) 2` and `ball (0 : selfAdjoint A) π`.
+ `selfAdjoint.expUnitaryPathToOne`: the path `t ↦ expUnitary (t • x)` from `1` to
  `expUnitary x` for a selfadjoint element `x`.
+ `Unitary.isPathConnected_ball`: any ball of radius `δ < 2` in the unitary group of a unital
  C⋆-algebra is path connected.
+ `Unitary.instLocallyPathConnectedSpace`: the unitary group of a C⋆-algebra is
  locally path connected.
+ `Unitary.mem_pathComponentOne_iff`: The path component of the identity in the unitary group of a
  C⋆-algebra is the set of unitaries that can be expressed as a product of exponentials of
  selfadjoint elements.
-/

@[expose] public section

variable {A : Type*} [CStarAlgebra A]

open Complex Metric NormedSpace selfAdjoint Unitary
open scoped Real

/-
**Unitary.two_mul_one_sub_le_norm_sub_one_sq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Unitary.two_mul_one_sub_le_norm_sub_one_sq {u : A} (hu : u in unitary A) {
z : Complex} (hz : z in spectrum Complex u) : 2 * (1 - z.re) <= ‖u - 1‖ ^ 2
参数：hu : u in unitary A；hz : z in spectrum Complex u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.sqrt_le_left`：sqrt_le_left (hy : 0 <= y) : √x <= y ↔ x <= y ^ 2
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `spectrum.subset_circle_of_unitary`：spectrum.subset_circle_of_unitary {u 
: E} (h : u in unitary E) : spectrum 𝕜 u subseteq Metric.sphere 0 1
· 使用定理 `CStarAlgebra.toCStarRing`：∀ {A : Type u_1} [self : CStarAlgebra A], CSta
rRing A
· 使用定理 `CStarAlgebra.toCompleteSpace`：∀ {A : Type u_1} [self : CStarAlgebra A], 
CompleteSpace A
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Complex.instContinuousStar`：ContinuousStar ℂ
· 使用定理 `IsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus`：∀ 
{R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} 
{inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用引理 `cfc_id'`：cfc_id' (ha : p a
· 使用定理 `isStarNormal_of_mem_unitary`：∀ {R : Type u_1} [inst : Monoid R] [inst_1 
: StarMul R] {u : R}, u ∈ unitary R → IsStarNormal u
· 使用引理 `cfc_one`：cfc_one : cfc (1 : R -> R) a = 1
· 使用引理 `cfc_sub`：cfc_sub : cfc (fun x => f x - g x) a = cfc f a - cfc g a
· 使用定理 `continuousOn_id'`：continuousOn_id' (s : Set α) : ContinuousOn (fun x : α
 => x) s
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `continuous_one`：continuous_one [TopologicalSpace M] [One M] : Continuous
 (1 : X -> M)
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Real.sqrt_mul`：sqrt_mul {x : Real} (hx : 0 <= x) (y : Real) : √(x * y) =
 √x * √y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Real.sqrt_sq`：sqrt_sq (h : 0 <= x) : √(x ^ 2) = x
· 使用引理 `Complex.norm_sub_one_sq_eq_of_norm_eq_one`：norm_sub_one_sq_eq_of_norm_eq
_one {z : Complex} (hz : ‖z‖ = 1) : ‖z - 1‖ ^ 2 = 2 * (1 - z.re)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
（共 38 条，此处仅展示前 30 条）
-/
lemma Unitary.two_mul_one_sub_le_norm_sub_one_sq {u : A} (hu : u ∈ unitary A)
    {z : ℂ} (hz : z ∈ spectrum ℂ u) :
    2 * (1 - z.re) ≤ ‖u - 1‖ ^ 2 := by
  rw [← Real.sqrt_le_left (by positivity)]
  have := spectrum.subset_circle_of_unitary hu hz
  simp only [mem_sphere_iff_norm, sub_zero] at this
  rw [← cfc_id' ℂ u, ← cfc_one ℂ u, ← cfc_sub ..]
  convert! norm_apply_le_norm_cfc (fun z ↦ z - 1) u hz
  simpa using congr(Real.sqrt $(norm_sub_one_sq_eq_of_norm_eq_one this)).symm
/-
**Unitary.norm_sub_one_sq_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Unitary.norm_sub_one_sq_eq {u : A} (hu : u in unitary A) {x : Real} (hz : 
IsLeast (re '' (spectrum Complex u)) x) : ‖u - 1‖ ^ 2 = 2 * (1 - x)
参数：hu : u in unitary A；hz : IsLeast (re '' (spectrum Complex u)) x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `Set.Nonempty.ne_empty`：∀ {α : Type u} {s : Set α}, s.Nonempty → s ≠ ∅
· 使用定理 `Set.Nonempty.of_image`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {s : 
Set α}, (f '' s).Nonempty → s.Nonempty
· 使用定理 `IsLeast.nonempty`：IsLeast.nonempty (h : IsLeast s a) : s.Nonempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `spectrum.of_subsingleton`：of_subsingleton [Subsingleton A] (a : A) : spe
ctrum R a = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Complex.instContinuousStar`：ContinuousStar ℂ
· 使用定理 `IsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus`：∀ 
{R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} 
{inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `cfc_id'`：cfc_id' (ha : p a
· 使用定理 `isStarNormal_of_mem_unitary`：∀ {R : Type u_1} [inst : Monoid R] [inst_1 
: StarMul R] {u : R}, u ∈ unitary R → IsStarNormal u
· 使用引理 `cfc_one`：cfc_one : cfc (1 : R -> R) a = 1
· 使用引理 `cfc_sub`：cfc_sub : cfc (fun x => f x - g x) a = cfc f a - cfc g a
· 使用定理 `continuousOn_id'`：continuousOn_id' (s : Set α) : ContinuousOn (fun x : α
 => x) s
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `continuous_one`：continuous_one [TopologicalSpace M] [One M] : Continuous
 (1 : X -> M)
· 使用定理 `Set.EqOn.mono`：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {f₁ f₂ : 
α → β}, s₁ ⊆ s₂ → Set.EqOn f₁ f₂ s₂ → Set.EqOn f₁ f₂ s₁
· 使用定理 `spectrum.subset_circle_of_unitary`：spectrum.subset_circle_of_unitary {u 
: E} (h : u in unitary E) : spectrum 𝕜 u subseteq Metric.sphere 0 1
· 使用定理 `CStarAlgebra.toCStarRing`：∀ {A : Type u_1} [self : CStarAlgebra A], CSta
rRing A
· 使用定理 `CStarAlgebra.toCompleteSpace`：∀ {A : Type u_1} [self : CStarAlgebra A], 
CompleteSpace A
· 使用引理 `Complex.norm_sub_one_sq_eqOn_sphere`：norm_sub_one_sq_eqOn_sphere : (Metr
ic.sphere (0 : Complex) 1).EqOn (‖· - 1‖ ^ 2) (fun z => 2 * (1 - z.re))
（共 54 条，此处仅展示前 30 条）
-/
lemma Unitary.norm_sub_one_sq_eq {u : A} (hu : u ∈ unitary A) {x : ℝ}
    (hz : IsLeast (re '' (spectrum ℂ u)) x) :
    ‖u - 1‖ ^ 2 = 2 * (1 - x) := by
  obtain (_ | _) := subsingleton_or_nontrivial A
  · exfalso; apply hz.nonempty.of_image.ne_empty; simp
  rw [← cfc_id' ℂ u, ← cfc_one ℂ u, ← cfc_sub ..]
  have h_eqOn : (spectrum ℂ u).EqOn (fun z ↦ ‖z - 1‖ ^ 2) (fun z ↦ 2 * (1 - z.re)) :=
    Complex.norm_sub_one_sq_eqOn_sphere.mono <| spectrum.subset_circle_of_unitary (𝕜 := ℂ) hu
  have h₂ : IsGreatest ((fun z ↦ 2 * (1 - z.re)) '' (spectrum ℂ u)) (2 * (1 - x)) := by
    have : Antitone (fun y : ℝ ↦ 2 * (1 - y)) := by intro _ _ _; simp only; gcongr
    simpa [Set.image_image] using this.map_isLeast hz
  have h₃ : IsGreatest ((‖· - 1‖ ^ 2) '' spectrum ℂ u) (‖cfc (· - 1 : ℂ → ℂ) u‖ ^ 2) := by
    have := pow_left_monotoneOn (n := 2) |>.mono (s₂ := ((‖· - 1‖) '' spectrum ℂ u)) (by simp)
    simpa [Set.image_image] using this.map_isGreatest (IsGreatest.norm_cfc (fun z : ℂ ↦ z - 1) u)
  exact h₃.unique (h_eqOn.image_eq ▸ h₂)
/-
**Unitary.norm_sub_one_lt_two_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Unitary.norm_sub_one_lt_two_iff {u : A} (hu : u in unitary A) : ‖u - 1‖ < 
2 ↔ -1 ∉ spectrum Complex u
参数：hu : u in unitary A。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `norm_of_subsingleton`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] [Su
bsingleton E] (a : E), ‖a‖ = 0
· 使用定理 `spectrum.of_subsingleton`：of_subsingleton [Subsingleton A] (a : A) : spe
ctrum R a = ∅
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `sq_lt_sq₀`：sq_lt_sq₀ (ha : 0 <= a) (hb : 0 <= b) : a ^ 2 < b ^ 2 ↔ a < b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用引理 `Unitary.two_mul_one_sub_le_norm_sub_one_sq`：Unitary.two_mul_one_sub_le_n
orm_sub_one_sq {u : A} (hu : u in unitary A) {z : Complex} (hz : z in spectrum C
omplex u) : 2 * (1 - z.re) <= ‖u…
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_eq`：∀ {α : Type u} [inst : AddMonoidWithOn
e α] {n : ℕ} {a a' : α}, Mathlib.Meta.NormNum.IsNat a n → ↑n = a' → a = a'
· 使用定理 `Mathlib.Meta.NormNum.isNat_add`：∀ {α : Type u_1} [inst : AddMonoidWithOn
e α] {f : α → α → α} {a b : α} {a' b' c : ℕ},   f = HAdd.hAdd →     Mathlib.Meta
.NormNum.IsNat a a' …
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.isNat_pow`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → ℕ → α} {a : α} {b a' b' c : ℕ},   f = HPow.hPow →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNatPowT.run`：∀ {a b c : ℕ}, Mathlib.Meta.NormNum.
IsNatPowT (a.pow 1 = a) a b c → a.pow b = c
（共 99 条，此处仅展示前 30 条）
-/
lemma Unitary.norm_sub_one_lt_two_iff {u : A} (hu : u ∈ unitary A) :
    ‖u - 1‖ < 2 ↔ -1 ∉ spectrum ℂ u := by
  nontriviality A
  rw [← sq_lt_sq₀ (by positivity) (by positivity)]
  constructor
  · intro h h1
    have := two_mul_one_sub_le_norm_sub_one_sq hu h1 |>.trans_lt h
    norm_num at this
  · contrapose!
    obtain ⟨x, hx⟩ := spectrum.isCompact (𝕜 := ℂ) u |>.image continuous_re |>.exists_isLeast <|
      (spectrum.nonempty _).image _
    rw [norm_sub_one_sq_eq hu hx]
    obtain ⟨z, hz, rfl⟩ := hx.1
    intro key
    replace key : z.re ≤ -1 := by linarith
    have hz_norm : ‖z‖ = 1 := spectrum.norm_eq_one_of_unitary hu hz
    rw [← hz_norm, ← RCLike.re_eq_complex_re, RCLike.re_le_neg_norm_iff_eq_neg_norm, hz_norm] at key
    exact key ▸ hz
/-
**Unitary.spectrum_subset_slitPlane_iff_norm_lt_two** 是 Mathlib 中的一个引理，位于命名空间 ``
。
形式化陈述：Unitary.spectrum_subset_slitPlane_iff_norm_lt_two {u : A} (hu : u in unita
ry A) : spectrum Complex u subseteq slitPlane ↔ ‖u - 1‖ < 2
参数：hu : u in unitary A。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.subset_slitPlane_iff_of_subset_sphere`：∀ {r : ℝ} {s : Set ℂ}, s 
⊆ Metric.sphere 0 r → (s ⊆ Complex.slitPlane ↔ -↑r ∉ s)
· 使用定理 `spectrum.subset_circle_of_unitary`：spectrum.subset_circle_of_unitary {u 
: E} (h : u in unitary E) : spectrum 𝕜 u subseteq Metric.sphere 0 1
· 使用定理 `CStarAlgebra.toCStarRing`：∀ {A : Type u_1} [self : CStarAlgebra A], CSta
rRing A
· 使用定理 `CStarAlgebra.toCompleteSpace`：∀ {A : Type u_1} [self : CStarAlgebra A], 
CompleteSpace A
· 使用引理 `Unitary.norm_sub_one_lt_two_iff`：Unitary.norm_sub_one_lt_two_iff {u : A}
 (hu : u in unitary A) : ‖u - 1‖ < 2 ↔ -1 ∉ spectrum Complex u
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma Unitary.spectrum_subset_slitPlane_iff_norm_lt_two {u : A} (hu : u ∈ unitary A) :
    spectrum ℂ u ⊆ slitPlane ↔ ‖u - 1‖ < 2 := by
  simp [subset_slitPlane_iff_of_subset_sphere (spectrum.subset_circle_of_unitary hu),
    norm_sub_one_lt_two_iff hu]

@[aesop safe apply (rule_sets := [CStarAlgebra])]
/-
**IsSelfAdjoint.cfc_arg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsSelfAdjoint.cfc_arg (u : A) : IsSelfAdjoint (cfc (ofReal ∘ arg : Complex
 -> Complex) u)
参数：u : A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Complex.instContinuousStar`：ContinuousStar ℂ
· 使用定理 `IsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus`：∀ 
{R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} 
{inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `cfc.congr_simp`：∀ {R : Type u_3} {A : Type u_4} {p p_1 : A → Prop} (e_p 
: p = p_1) [inst : CommSemiring R] [inst_1 : StarRing R]   [inst_2 : MetricSpace
 R] …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Complex.conj_ofReal`：conj_ofReal (r : Real) : conj (r : Complex) = r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma IsSelfAdjoint.cfc_arg (u : A) : IsSelfAdjoint (cfc (ofReal ∘ arg : ℂ → ℂ) u) := by
  simp [isSelfAdjoint_iff, ← cfc_star, Function.comp_def]

/-- The selfadjoint element obtained by taking the argument (using the principal branch and the
continuous functional calculus) of a unitary whose spectrum does not contain `-1`. This returns
`0` if the principal branch of the logarithm is not continuous on the spectrum of the unitary
element. -/
@[simps]
/-
**Unitary.argSelfAdjoint** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Unitary.argSelfAdjoint (u : unitary A) : selfAdjoint A
参数：u : unitary A。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.instContinuousStar`：ContinuousStar ℂ

--- 原说明 ---
The selfadjoint element obtained by taking the argument (using the principal bra
nch and the
continuous functional calculus) of a unitary whose spectrum does not contain `-1
`. This returns
`0` if the principal branch of the logarithm is not continuous on the spectrum o
f the unitary
element.
-/
noncomputable def Unitary.argSelfAdjoint (u : unitary A) : selfAdjoint A :=
  ⟨cfc (arg · : ℂ → ℂ) (u : A), .cfc_arg (u : A)⟩
/-
**selfAdjoint.norm_sq_expUnitary_sub_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：selfAdjoint.norm_sq_expUnitary_sub_one {x : selfAdjoint A} (hx : ‖x‖ <= π)
 : ‖(expUnitary x - 1 : A)‖ ^ 2 = 2 * (1 - Real.cos ‖x‖)
参数：hx : ‖x‖ <= π。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `NormedStarGroup.to_continuousStar`：∀ {E : Type u_2} [inst : SeminormedAd
dCommGroup E] [inst_1 : StarAddMonoid E] [NormedStarGroup E], ContinuousStar E
· 使用定理 `CStarRing.to_normedStarGroup`：∀ {E : Type u_2} [inst : NonUnitalNormedRi
ng E] [inst_1 : StarRing E] [CStarRing E], NormedStarGroup E
· 使用定理 `CStarAlgebra.toCStarRing`：∀ {A : Type u_1} [self : CStarAlgebra A], CSta
rRing A
· 使用定理 `CStarAlgebra.toCompleteSpace`：∀ {A : Type u_1} [self : CStarAlgebra A], 
CompleteSpace A
· 使用定理 `CStarAlgebra.toStarModule`：∀ {A : Type u_1} [self : CStarAlgebra A], Sta
rModule ℂ A
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `selfAdjoint.expUnitary_coe`：∀ {A : Type u_1} [inst : NormedRing A] [inst
_1 : NormedAlgebra ℂ A] [inst_2 : StarRing A] [inst_3 : ContinuousStar A]   [ins
t_4 : CompleteSp…
· 使用定理 `norm_of_subsingleton`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] [Su
bsingleton E] (a : E), ‖a‖ = 0
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Real.cos_zero`：cos_zero : cos 0 = 1
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Unitary.norm_sub_one_sq_eq`：Unitary.norm_sub_one_sq_eq {u : A} (hu : u i
n unitary A) {x : Real} (hz : IsLeast (re '' (spectrum Complex u)) x) : ‖u - 1‖ 
^ 2 = 2 * (1 - x…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `IsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus`：∀ 
{R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} 
{inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
（共 65 条，此处仅展示前 30 条）
-/
lemma selfAdjoint.norm_sq_expUnitary_sub_one {x : selfAdjoint A} (hx : ‖x‖ ≤ π) :
    ‖(expUnitary x - 1 : A)‖ ^ 2 = 2 * (1 - Real.cos ‖x‖) := by
  nontriviality A
  apply norm_sub_one_sq_eq (expUnitary x).2
  simp only [expUnitary_coe]
  rw [← CFC.exp_eq_normedSpace_exp (𝕜 := ℂ), ← cfc_comp_smul I _ (x : A), cfc_map_spectrum ..,
    ← x.2.spectrumRestricts.algebraMap_image]
  simp only [Set.image_image, coe_algebraMap, smul_eq_mul, mul_comm I, ← exp_eq_exp_ℂ,
    exp_ofReal_mul_I_re]
  refine ⟨?_, ?_⟩
  · cases CStarAlgebra.norm_or_neg_norm_mem_spectrum x.2 with
    | inl h => exact ⟨_, h, rfl⟩
    | inr h => exact ⟨_, h, by simp⟩
  · rintro - ⟨y, hy, rfl⟩
    exact Real.cos_abs y ▸ Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) hx <|
      spectrum.norm_le_norm_of_mem hy
/-
**argSelfAdjoint_expUnitary** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：argSelfAdjoint_expUnitary {x : selfAdjoint A} (hx : ‖x‖ < π) : argSelfAdjo
int (expUnitary x) = x
参数：hx : ‖x‖ < π。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `NormedStarGroup.to_continuousStar`：∀ {E : Type u_2} [inst : SeminormedAd
dCommGroup E] [inst_1 : StarAddMonoid E] [NormedStarGroup E], ContinuousStar E
· 使用定理 `CStarRing.to_normedStarGroup`：∀ {E : Type u_2} [inst : NonUnitalNormedRi
ng E] [inst_1 : StarRing E] [CStarRing E], NormedStarGroup E
· 使用定理 `CStarAlgebra.toCStarRing`：∀ {A : Type u_1} [self : CStarAlgebra A], CSta
rRing A
· 使用定理 `CStarAlgebra.toCompleteSpace`：∀ {A : Type u_1} [self : CStarAlgebra A], 
CompleteSpace A
· 使用定理 `CStarAlgebra.toStarModule`：∀ {A : Type u_1} [self : CStarAlgebra A], Sta
rModule ℂ A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instSubsingletonSubtype_mathlib`：∀ {α : Sort u_1} [Subsingleton α] (p : 
α → Prop), Subsingleton (Subtype p)
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Unitary.spectrum_subset_slitPlane_iff_norm_lt_two`：Unitary.spectrum_subs
et_slitPlane_iff_norm_lt_two {u : A} (hu : u in unitary A) : spectrum Complex u 
subseteq slitPlane ↔ ‖u - 1‖ < 2
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `sq_lt_sq₀`：sq_lt_sq₀ (ha : 0 <= a) (hb : 0 <= b) : a ^ 2 < b ^ 2 ↔ a < b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用引理 `selfAdjoint.norm_sq_expUnitary_sub_one`：selfAdjoint.norm_sq_expUnitary_s
ub_one {x : selfAdjoint A} (hx : ‖x‖ <= π) : ‖(expUnitary x - 1 : A)‖ ^ 2 = 2 * 
(1 - Real.cos ‖x‖)
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `mul_lt_mul_of_pos_left`：mul_lt_mul_of_pos_left [PosMulStrictMono α] (hbc
 : b < c) (ha : 0 < a) : a * b < a * c
· 使用定理 `sub_lt_sub_left`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [Add
LeftStrictMono α] [AddRightStrictMono α] {a b : α},   a < b → ∀ (c : α), c - b <
 c - …
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
（共 99 条，此处仅展示前 30 条）
-/
lemma argSelfAdjoint_expUnitary {x : selfAdjoint A} (hx : ‖x‖ < π) :
    argSelfAdjoint (expUnitary x) = x := by
  nontriviality A
  ext
  have : spectrum ℂ (expUnitary x : A) ⊆ slitPlane := by
    rw [spectrum_subset_slitPlane_iff_norm_lt_two (expUnitary x).2,
      ← sq_lt_sq₀ (by positivity) (by positivity), norm_sq_expUnitary_sub_one hx.le]
    calc
      2 * (1 - Real.cos ‖x‖) < 2 * (1 - Real.cos π) := by
        gcongr
        exact Real.cos_lt_cos_of_nonneg_of_le_pi (by positivity) le_rfl hx
      _ = 2 ^ 2 := by norm_num
  simp only [argSelfAdjoint_coe, expUnitary_coe]
  rw [← CFC.exp_eq_normedSpace_exp (𝕜 := ℂ), ← cfc_comp_smul .., ← cfc_comp' (hg := ?hg)]
  case hg =>
    refine continuous_ofReal.comp_continuousOn <| continuousOn_arg.mono ?_
    rwa [expUnitary_coe, ← CFC.exp_eq_normedSpace_exp (𝕜 := ℂ), ← cfc_comp_smul ..,
      cfc_map_spectrum ..] at this
  conv_rhs => rw [← cfc_id' ℂ (x : A)]
  refine cfc_congr fun y hy ↦ ?_
  rw [← x.2.spectrumRestricts.algebraMap_image] at hy
  obtain ⟨y, hy, rfl⟩ := hy
  simp only [coe_algebraMap, smul_eq_mul, mul_comm I, ← exp_eq_exp_ℂ, ofReal_inj]
  replace hy : ‖y‖ < π := spectrum.norm_le_norm_of_mem hy |>.trans_lt hx
  simp only [Real.norm_eq_abs, abs_lt] at hy
  rw [← Circle.coe_exp, Circle.arg_exp hy.1 hy.2.le]
/-
**expUnitary_argSelfAdjoint** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：expUnitary_argSelfAdjoint {u : unitary A} (hu : ‖(u - 1 : A)‖ < 2) : expUn
itary (argSelfAdjoint u) = u
参数：hu : ‖(u - 1 : A)‖ < 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `NormedStarGroup.to_continuousStar`：∀ {E : Type u_2} [inst : SeminormedAd
dCommGroup E] [inst_1 : StarAddMonoid E] [NormedStarGroup E], ContinuousStar E
· 使用定理 `CStarRing.to_normedStarGroup`：∀ {E : Type u_2} [inst : NonUnitalNormedRi
ng E] [inst_1 : StarRing E] [CStarRing E], NormedStarGroup E
· 使用定理 `CStarAlgebra.toCStarRing`：∀ {A : Type u_1} [self : CStarAlgebra A], CSta
rRing A
· 使用定理 `CStarAlgebra.toCompleteSpace`：∀ {A : Type u_1} [self : CStarAlgebra A], 
CompleteSpace A
· 使用定理 `CStarAlgebra.toStarModule`：∀ {A : Type u_1} [self : CStarAlgebra A], Sta
rModule ℂ A
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t
· 使用定理 `Complex.continuousOn_arg`：continuousOn_arg : ContinuousOn arg slitPlane
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Unitary.spectrum_subset_slitPlane_iff_norm_lt_two`：Unitary.spectrum_subs
et_slitPlane_iff_norm_lt_two {u : A} (hu : u in unitary A) : spectrum Complex u 
subseteq slitPlane ↔ ‖u - 1‖ < 2
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `selfAdjoint.expUnitary_coe`：∀ {A : Type u_1} [inst : NormedRing A] [inst
_1 : NormedAlgebra ℂ A] [inst_2 : StarRing A] [inst_3 : ContinuousStar A]   [ins
t_4 : CompleteSp…
· 使用定理 `Complex.instContinuousStar`：ContinuousStar ℂ
· 使用定理 `Unitary.argSelfAdjoint_coe`：∀ {A : Type u_1} [inst : CStarAlgebra A] (u 
: ↥(unitary A)), ↑(Unitary.argSelfAdjoint u) = cfc (fun x => ↑x.arg) ↑u
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `IsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus`：∀ 
{R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} 
{inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CFC.exp_eq_normedSpace_exp`：exp_eq_normedSpace_exp {a : A} (ha : p a
· 使用定理 `IsStarNormal.smul`：∀ {R : Type u_3} {A : Type u_4} [inst : SMul R A] [in
st_1 : Star R] [inst_2 : Star A] [inst_3 : Mul A] [StarModule R A]   [SMulCommCl
ass R A…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `cfc_comp_smul`：cfc_comp_smul {S : Type*} [SMul S R] [ContinuousConstSMul
 S R] [SMulZeroClass S A] [IsScalarTower S R A] [IsScalarTower S R (R -> R)] (s 
: S…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
（共 67 条，此处仅展示前 30 条）
-/
lemma expUnitary_argSelfAdjoint {u : unitary A} (hu : ‖(u - 1 : A)‖ < 2) :
    expUnitary (argSelfAdjoint u) = u := by
  ext
  have : ContinuousOn arg (spectrum ℂ (u : A)) :=
    continuousOn_arg.mono <| (spectrum_subset_slitPlane_iff_norm_lt_two u.2).mpr hu
  rw [expUnitary_coe, argSelfAdjoint_coe, ← CFC.exp_eq_normedSpace_exp (𝕜 := ℂ),
    ← cfc_comp_smul .., ← cfc_comp' ..]
  conv_rhs => rw [← cfc_id' ℂ (u : A)]
  refine cfc_congr fun y hy ↦ ?_
  have hy₁ : ‖y‖ = 1 := spectrum.norm_eq_one_of_unitary u.2 hy
  have : I * y.arg = log y :=
    Complex.ext (by simp [log_re, spectrum.norm_eq_one_of_unitary u.2 hy]) (by simp [log_im])
  simpa [← exp_eq_exp_ℂ, this] using exp_log (by aesop)
/-
**Unitary.norm_argSelfAdjoint_le_pi** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Unitary.norm_argSelfAdjoint_le_pi (u : unitary A) : ‖argSelfAdjoint u‖ <= 
π
参数：u : unitary A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `norm_cfc_le`：norm_cfc_le {f : 𝕜 -> 𝕜} {a : A} {c : Real} (hc : 0 <= c) (
h : forall x in σ 𝕜 a, ‖f x‖ <= c) : ‖cfc f a‖ <= c
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.pi_pos`：pi_pos : 0 < π
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Complex.norm_real`：norm_real (r : Real) : ‖(r : Complex)‖ = ‖r‖
· 使用定理 `Complex.abs_arg_le_pi`：abs_arg_le_pi (z : Complex) : |arg z| <= π
-/
lemma Unitary.norm_argSelfAdjoint_le_pi (u : unitary A) :
    ‖argSelfAdjoint u‖ ≤ π :=
  norm_cfc_le (by positivity) fun y hy ↦ by simpa using abs_arg_le_pi y
/-
**Unitary.two_mul_one_sub_cos_norm_argSelfAdjoint** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Unitary.two_mul_one_sub_cos_norm_argSelfAdjoint {u : unitary A} (hu : ‖(u 
- 1 : A)‖ < 2) : 2 * (1 - Real.cos ‖argSelfAdjoint u‖) = ‖(u - 1 : A)‖ ^ 2
参数：hu : ‖(u - 1 : A)‖ < 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `NormedStarGroup.to_continuousStar`：∀ {E : Type u_2} [inst : SeminormedAd
dCommGroup E] [inst_1 : StarAddMonoid E] [NormedStarGroup E], ContinuousStar E
· 使用定理 `CStarRing.to_normedStarGroup`：∀ {E : Type u_2} [inst : NonUnitalNormedRi
ng E] [inst_1 : StarRing E] [CStarRing E], NormedStarGroup E
· 使用定理 `CStarAlgebra.toCStarRing`：∀ {A : Type u_1} [self : CStarAlgebra A], CSta
rRing A
· 使用定理 `CStarAlgebra.toCompleteSpace`：∀ {A : Type u_1} [self : CStarAlgebra A], 
CompleteSpace A
· 使用定理 `CStarAlgebra.toStarModule`：∀ {A : Type u_1} [self : CStarAlgebra A], Sta
rModule ℂ A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `expUnitary_argSelfAdjoint`：expUnitary_argSelfAdjoint {u : unitary A} (hu
 : ‖(u - 1 : A)‖ < 2) : expUnitary (argSelfAdjoint u) = u
· 使用引理 `selfAdjoint.norm_sq_expUnitary_sub_one`：selfAdjoint.norm_sq_expUnitary_s
ub_one {x : selfAdjoint A} (hx : ‖x‖ <= π) : ‖(expUnitary x - 1 : A)‖ ^ 2 = 2 * 
(1 - Real.cos ‖x‖)
· 使用引理 `Unitary.norm_argSelfAdjoint_le_pi`：Unitary.norm_argSelfAdjoint_le_pi (u 
: unitary A) : ‖argSelfAdjoint u‖ <= π
-/
lemma Unitary.two_mul_one_sub_cos_norm_argSelfAdjoint {u : unitary A} (hu : ‖(u - 1 : A)‖ < 2) :
    2 * (1 - Real.cos ‖argSelfAdjoint u‖) = ‖(u - 1 : A)‖ ^ 2 := by
  conv_rhs => rw [← expUnitary_argSelfAdjoint hu]
  exact Eq.symm <| norm_sq_expUnitary_sub_one <| norm_argSelfAdjoint_le_pi u
/-
**Unitary.norm_argSelfAdjoint** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Unitary.norm_argSelfAdjoint {u : unitary A} (hu : ‖(u - 1 : A)‖ < 2) : ‖ar
gSelfAdjoint u‖ = Real.arccos (1 - ‖(u - 1 : A)‖ ^ 2 / 2)
参数：hu : ‖(u - 1 : A)‖ < 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Real.arccos_eq_of_eq_cos`：arccos_eq_of_eq_cos (hy₀ : 0 <= y) (hy₁ : y <=
 π) (hxy : x = cos y) : arccos x = y
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用引理 `Unitary.norm_argSelfAdjoint_le_pi`：Unitary.norm_argSelfAdjoint_le_pi (u 
: unitary A) : ‖argSelfAdjoint u‖ <= π
· 使用引理 `Mathlib.Tactic.Linarith.eq_of_not_lt_of_not_gt`：eq_of_not_lt_of_not_gt {
α} [LinearOrder α] (a b : α) (h1 : ¬ a < b) (h2 : ¬ b < a) : a = b
· 使用定理 `Not.intro`：∀ {a : Prop}, (a → False) → ¬a
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a c₁ c₂ : R} {b₁ b₂ : ℕ} {d : R},   a ^ b₁ = c₁ → a ^ b₂ = c₂ → c₁ * c₂ = 
d → a ^ (b₁ + b₂) = d
（共 74 条，此处仅展示前 30 条）
-/
lemma Unitary.norm_argSelfAdjoint {u : unitary A} (hu : ‖(u - 1 : A)‖ < 2) :
    ‖argSelfAdjoint u‖ = Real.arccos (1 - ‖(u - 1 : A)‖ ^ 2 / 2) := by
  refine Real.arccos_eq_of_eq_cos (by positivity) (norm_argSelfAdjoint_le_pi u) ?_ |>.symm
  linarith [two_mul_one_sub_cos_norm_argSelfAdjoint hu]

set_option backward.isDefEq.respectTransparency false in
/-
**Unitary.norm_expUnitary_smul_argSelfAdjoint_sub_one_le** 是 Mathlib 中的一个引理，位于命名
空间 ``。
形式化陈述：Unitary.norm_expUnitary_smul_argSelfAdjoint_sub_one_le (u : unitary A) {t 
: Real} (ht : t in Set.Icc 0 1) (hu : ‖(u - 1 : A)‖ < 2) : ‖(expUnitary (t • arg
SelfAdjoint u) - 1 : A)‖ <= ‖(u - 1 : A)‖
参数：u : unitary A；ht : t in Set.Icc 0 1；hu : ‖(u - 1 : A)‖ < 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `instTrivialStarReal`：TrivialStar ℝ
· 使用定理 `StarModule.complexToReal`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst
_1 : Star E] [inst_2 : _root_.Module ℂ E] [StarModule ℂ E], StarModule ℝ E
· 使用定理 `CStarAlgebra.toStarModule`：∀ {A : Type u_1} [self : CStarAlgebra A], Sta
rModule ℂ A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `NormedStarGroup.to_continuousStar`：∀ {E : Type u_2} [inst : SeminormedAd
dCommGroup E] [inst_1 : StarAddMonoid E] [NormedStarGroup E], ContinuousStar E
· 使用定理 `CStarRing.to_normedStarGroup`：∀ {E : Type u_2} [inst : NonUnitalNormedRi
ng E] [inst_1 : StarRing E] [CStarRing E], NormedStarGroup E
· 使用定理 `CStarAlgebra.toCStarRing`：∀ {A : Type u_1} [self : CStarAlgebra A], CSta
rRing A
· 使用定理 `CStarAlgebra.toCompleteSpace`：∀ {A : Type u_1} [self : CStarAlgebra A], 
CompleteSpace A
· 使用引理 `sq_le_sq₀`：sq_le_sq₀ (ha : 0 <= a) (hb : 0 <= b) : a ^ 2 <= b ^ 2 ↔ a <=
 b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `selfAdjoint.norm_sq_expUnitary_sub_one`：selfAdjoint.norm_sq_expUnitary_s
ub_one {x : selfAdjoint A} (hx : ‖x‖ <= π) : ‖(expUnitary x - 1 : A)‖ ^ 2 = 2 * 
(1 - Real.cos ‖x‖)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `Unitary.norm_argSelfAdjoint_le_pi`：Unitary.norm_argSelfAdjoint_le_pi (u 
: unitary A) : ‖argSelfAdjoint u‖ <= π
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `sub_le_sub_left`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [Add
LeftMono α] [AddRightMono α] {a b : α},   a ≤ b → ∀ (c : α), c - b ≤ c - a
（共 38 条，此处仅展示前 30 条）
-/
lemma Unitary.norm_expUnitary_smul_argSelfAdjoint_sub_one_le (u : unitary A)
    {t : ℝ} (ht : t ∈ Set.Icc 0 1) (hu : ‖(u - 1 : A)‖ < 2) :
    ‖(expUnitary (t • argSelfAdjoint u) - 1 : A)‖ ≤ ‖(u - 1 : A)‖ := by
  have key : ‖t • argSelfAdjoint u‖ ≤ ‖argSelfAdjoint u‖ := by
    rw [← one_mul ‖argSelfAdjoint u‖]
    simp_rw [AddSubgroupClass.coe_norm, val_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    gcongr
    exact ht.2
  rw [← sq_le_sq₀ (by positivity) (by positivity)]
  rw [norm_sq_expUnitary_sub_one (key.trans <| norm_argSelfAdjoint_le_pi u)]
  trans 2 * (1 - Real.cos ‖argSelfAdjoint u‖)
  · gcongr
    exact Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) (norm_argSelfAdjoint_le_pi u) key
  · exact (two_mul_one_sub_cos_norm_argSelfAdjoint hu).le

@[fun_prop]
/-
**Unitary.continuousOn_argSelfAdjoint** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Unitary.continuousOn_argSelfAdjoint : ContinuousOn (argSelfAdjoint : unita
ry A -> selfAdjoint A) (ball (1 : unitary A) 2)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Topology.IsInducing.continuousOn_iff`：Topology.IsInducing.continuousOn_i
ff {f : α -> β} {g : β -> γ} (hg : IsInducing g) {s : Set α} : ContinuousOn f s 
↔ ContinuousOn (g ∘ f) s
· 使用引理 `Topology.IsInducing.subtypeVal`：Topology.IsInducing.subtypeVal {t : Set 
Y} : IsInducing ((↑) : t -> Y)
· 使用定理 `Complex.instContinuousStar`：ContinuousStar ℂ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Unitary.argSelfAdjoint_coe`：∀ {A : Type u_1} [inst : CStarAlgebra A] (u 
: ↥(unitary A)), ↑(Unitary.argSelfAdjoint u) = cfc (fun x => ↑x.arg) ↑u
· 使用定理 `IsOpen.continuousOn_iff`：IsOpen.continuousOn_iff (hs : IsOpen s) : Conti
nuousOn f s ↔ forall ⦃a⦄, a in s -> ContinuousAt f a
· 使用定理 `Metric.isOpen_ball`：∀ {α : Type u} [inst : PseudoMetricSpace α] {x : α} 
{ε : ℝ}, IsOpen (Metric.ball x ε)
· 使用定理 `exists_between`：exists_between [LT α] [DenselyOrdered α] {a₁ a₂ : α} : a
₁ < a₂ -> exists a, a₁ < a ∧ a < a₂
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `sq_lt_sq₀`：sq_lt_sq₀ (ha : 0 <= a) (hb : 0 <= b) : a ^ 2 < b ^ 2 ↔ a < b
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `dist_nonneg`：dist_nonneg {x y : α} : 0 <= dist x y
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `Even.pow_nonneg`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : LinearOr
der R] [IsOrderedRing R] [ExistsAddOfLE R] {n : ℕ},   Even n → ∀ (a : R), 0 ≤ a 
^ n
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用引理 `even_two_mul`：even_two_mul (a : α) : Even (2 * a)
· 使用定理 `Real.lt_sqrt_of_sq_lt`：lt_sqrt_of_sq_lt (h : x ^ 2 < y) : x < √y
（共 95 条，此处仅展示前 30 条）
-/
lemma Unitary.continuousOn_argSelfAdjoint :
    ContinuousOn (argSelfAdjoint : unitary A → selfAdjoint A) (ball (1 : unitary A) 2) := by
  rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
  simp only [Function.comp_def, argSelfAdjoint_coe]
  rw [isOpen_ball.continuousOn_iff]
  intro u (hu : dist u 1 < 2)
  obtain ⟨ε, huε, hε2⟩ := exists_between (sq_lt_sq₀ (by positivity) (by positivity) |>.mpr hu)
  have hε : 0 < ε := lt_of_le_of_lt (by positivity) huε
  have huε' : dist u 1 < √ε := Real.lt_sqrt_of_sq_lt huε
  apply ContinuousOn.continuousAt ?_ (closedBall_mem_nhds_of_mem huε')
  apply ContinuousOn.image_comp_continuous ?_ continuous_subtype_val
  apply continuousOn_cfc A (s := sphere 0 1 ∩ {z | 2 * (1 - z.re) ≤ ε}) ?_ _ ?_ |>.mono
  · rintro - ⟨v, hv, rfl⟩
    simp only [Set.subset_inter_iff, Set.mem_ofPred_eq]
    refine ⟨inferInstance, spectrum_subset_circle v, ?_⟩
    intro z hz
    simp only [Set.mem_ofPred_eq]
    trans ‖(v - 1 : A)‖ ^ 2
    · exact two_mul_one_sub_le_norm_sub_one_sq v.2 hz
    · refine Real.le_sqrt (by positivity) (by positivity) |>.mp ?_
      simpa [Subtype.dist_eq, dist_eq_norm] using hv
  · exact isCompact_sphere 0 1 |>.inter_right <| isClosed_le (by fun_prop) (by fun_prop)
  · refine continuous_ofReal.comp_continuousOn <| continuousOn_arg.mono ?_
    apply subset_slitPlane_iff_of_subset_sphere Set.inter_subset_left |>.mpr
    norm_num at hε2 ⊢
    exact hε2

set_option backward.isDefEq.respectTransparency false in
/-- the maps `unitary.argSelfAdjoint` and `selfAdjoint.expUnitary` form a partial
homeomorphism between `ball (1 : unitary A) 2` and `ball (0 : selfAdjoint A) π`. -/
@[simps]
/-
**Unitary.openPartialHomeomorph** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Unitary.openPartialHomeomorph : OpenPartialHomeomorph (unitary A) (selfAdj
oint A) where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CStarAlgebra.toCompleteSpace`：∀ {A : Type u_1} [self : CStarAlgebra A], 
CompleteSpace A
· 使用定理 `CStarAlgebra.toStarModule`：∀ {A : Type u_1} [self : CStarAlgebra A], Sta
rModule ℂ A

--- 原说明 ---
the maps `unitary.argSelfAdjoint` and `selfAdjoint.expUnitary` form a partial
homeomorphism between `ball (1 : unitary A) 2` and `ball (0 : selfAdjoint A) π`.
-/
noncomputable def Unitary.openPartialHomeomorph :
    OpenPartialHomeomorph (unitary A) (selfAdjoint A) where
  toFun := argSelfAdjoint
  invFun := expUnitary
  source := ball 1 2
  target := ball 0 π
  map_source' u hu := by
    simp only [mem_ball, Subtype.dist_eq, OneMemClass.coe_one, dist_eq_norm, sub_zero] at hu ⊢
    rw [norm_argSelfAdjoint hu]
    calc
      Real.arccos (1 - ‖(u - 1 : A)‖ ^ 2 / 2) < Real.arccos (1 - 2 ^ 2 / 2) := by
        apply Real.arccos_lt_arccos (by norm_num) (by gcongr)
        linarith [(by positivity : 0 ≤ ‖(u - 1 : A)‖ ^ 2 / 2)]
      _ = π := by norm_num
  map_target' x hx := by
    simp only [mem_ball, Subtype.dist_eq, OneMemClass.coe_one, dist_eq_norm, sub_zero] at hx ⊢
    rw [← sq_lt_sq₀ (by positivity) (by positivity), norm_sq_expUnitary_sub_one hx.le]
    have : -1 < Real.cos ‖(x : A)‖ :=
      Real.cos_pi ▸ Real.cos_lt_cos_of_nonneg_of_le_pi (by positivity) le_rfl hx
    simp only [AddSubgroupClass.coe_norm, mul_sub, mul_one, sq, gt_iff_lt]
    linarith
  left_inv' u hu := expUnitary_argSelfAdjoint <| by
    simpa [Subtype.dist_eq, dist_eq_norm] using hu
  right_inv' x hx := argSelfAdjoint_expUnitary <| by simpa using hx
  open_source := isOpen_ball
  open_target := isOpen_ball
  continuousOn_toFun := by fun_prop
  continuousOn_invFun := by fun_prop
/-
**Unitary.norm_sub_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Unitary.norm_sub_eq (u v : unitary A) : ‖(u - v : A)‖ = ‖((u * star v : un
itary A) - 1 : A)‖
参数：u v : unitary A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Unitary.star_mul_self_of_mem`：star_mul_self_of_mem {U : R} (hU : U in un
itary R) : star U * U = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CStarRing.norm_mul_coe_unitary`：norm_mul_coe_unitary (A : E) (U : unitar
y E) : ‖A * U‖ = ‖A‖
· 使用定理 `CStarAlgebra.toCStarRing`：∀ {A : Type u_1} [self : CStarAlgebra A], CSta
rRing A
-/
lemma Unitary.norm_sub_eq (u v : unitary A) :
    ‖(u - v : A)‖ = ‖((u * star v : unitary A) - 1 : A)‖ := calc
  ‖(u - v : A)‖ = ‖(u * star v - 1 : A) * v‖ := by simp [sub_mul, mul_assoc]
  _ = ‖((u * star v : unitary A) - 1 : A)‖ := by simp
/-
**Unitary.expUnitary_eq_mul_inv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Unitary.expUnitary_eq_mul_inv (u v : unitary A) (huv : ‖(u - v : A)‖ < 2) 
: expUnitary (argSelfAdjoint (u * star v)) = u * star v
参数：u v : unitary A；huv : ‖(u - v : A)‖ < 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `expUnitary_argSelfAdjoint`：expUnitary_argSelfAdjoint {u : unitary A} (hu
 : ‖(u - 1 : A)‖ < 2) : expUnitary (argSelfAdjoint u) = u
· 使用引理 `Unitary.norm_sub_eq`：Unitary.norm_sub_eq (u v : unitary A) : ‖(u - v : A
)‖ = ‖((u * star v : unitary A) - 1 : A)‖
-/
lemma Unitary.expUnitary_eq_mul_inv (u v : unitary A) (huv : ‖(u - v : A)‖ < 2) :
    expUnitary (argSelfAdjoint (u * star v)) = u * star v :=
  expUnitary_argSelfAdjoint <| norm_sub_eq u v ▸ huv

/-- For a selfadjoint element `x` in a C⋆-algebra, this is the path from `1` to `expUnitary x`
given by `t ↦ expUnitary (t • x)`. -/
@[simps]
/-
**selfAdjoint.expUnitaryPathToOne** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：selfAdjoint.expUnitaryPathToOne (x : selfAdjoint A) : Path 1 (expUnitary x
) where toFun t
参数：x : selfAdjoint A。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CStarAlgebra.toCompleteSpace`：∀ {A : Type u_1} [self : CStarAlgebra A], 
CompleteSpace A
· 使用定理 `CStarAlgebra.toStarModule`：∀ {A : Type u_1} [self : CStarAlgebra A], Sta
rModule ℂ A
· 使用定理 `instTrivialStarReal`：TrivialStar ℝ

--- 原说明 ---
For a selfadjoint element `x` in a C⋆-algebra, this is the path from `1` to `exp
Unitary x`
given by `t ↦ expUnitary (t • x)`.
-/
noncomputable def selfAdjoint.expUnitaryPathToOne (x : selfAdjoint A) :
    Path 1 (expUnitary x) where
  toFun t := expUnitary ((t : ℝ) • x)
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by simp

@[simp]
/-
**selfAdjoint.joined_one_expUnitary** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：selfAdjoint.joined_one_expUnitary (x : selfAdjoint A) : Joined (1 : unitar
y A) (expUnitary x)
参数：x : selfAdjoint A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedStarGroup.to_continuousStar`：∀ {E : Type u_2} [inst : SeminormedAd
dCommGroup E] [inst_1 : StarAddMonoid E] [NormedStarGroup E], ContinuousStar E
· 使用定理 `CStarRing.to_normedStarGroup`：∀ {E : Type u_2} [inst : NonUnitalNormedRi
ng E] [inst_1 : StarRing E] [CStarRing E], NormedStarGroup E
· 使用定理 `CStarAlgebra.toCStarRing`：∀ {A : Type u_1} [self : CStarAlgebra A], CSta
rRing A
· 使用定理 `CStarAlgebra.toCompleteSpace`：∀ {A : Type u_1} [self : CStarAlgebra A], 
CompleteSpace A
· 使用定理 `CStarAlgebra.toStarModule`：∀ {A : Type u_1} [self : CStarAlgebra A], Sta
rModule ℂ A
-/
lemma selfAdjoint.joined_one_expUnitary (x : selfAdjoint A) :
    Joined (1 : unitary A) (expUnitary x) :=
  ⟨expUnitaryPathToOne x⟩

/-- The path `t ↦ expUnitary (t • argSelfAdjoint (v * star u)) * u`
from `u : unitary A` to `v` when `‖v - u‖ < 2`. -/
@[simps]
/-
**Unitary.path** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Unitary.path (u v : unitary A) (huv : ‖(v - u : A)‖ < 2) : Path u v where 
toFun t
参数：u v : unitary A；huv : ‖(v - u : A)‖ < 2。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CStarAlgebra.toCompleteSpace`：∀ {A : Type u_1} [self : CStarAlgebra A], 
CompleteSpace A
· 使用定理 `CStarAlgebra.toStarModule`：∀ {A : Type u_1} [self : CStarAlgebra A], Sta
rModule ℂ A
· 使用定理 `instTrivialStarReal`：TrivialStar ℝ

--- 原说明 ---
The path `t ↦ expUnitary (t • argSelfAdjoint (v * star u)) * u`
from `u : unitary A` to `v` when `‖v - u‖ < 2`.
-/
noncomputable def Unitary.path (u v : unitary A) (huv : ‖(v - u : A)‖ < 2) :
    Path u v where
  toFun t := expUnitary ((t : ℝ) • argSelfAdjoint (v * star u)) * u
  continuous_toFun := by fun_prop
  source' := by ext; simp
  target' := by simp [expUnitary_eq_mul_inv v u huv, mul_assoc]

/-- Two unitary elements `u` and `v` in a unital C⋆-algebra are joined by a path if the
distance between them is less than `2`. -/
/-
**Unitary.joined** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Unitary.joined (u v : unitary A) (huv : ‖(v - u : A)‖ < 2) : Joined u v
参数：u v : unitary A；huv : ‖(v - u : A)‖ < 2。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)

--- 原说明 ---
Two unitary elements `u` and `v` in a unital C⋆-algebra are joined by a path if 
the
distance between them is less than `2`.
-/
lemma Unitary.joined (u v : unitary A) (huv : ‖(v - u : A)‖ < 2) :
    Joined u v :=
  ⟨path u v huv⟩

/-- Any ball of radius `δ < 2` in the unitary group of a unital C⋆-algebra is path connected. -/
/-
**Unitary.isPathConnected_ball** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Unitary.isPathConnected_ball (u : unitary A) (δ : Real) (hδ₀ : 0 < δ) (hδ₂
 : δ < 2) : IsPathConnected (ball (u : unitary A) δ)
参数：u : unitary A；δ : Real；hδ₀ : 0 < δ；hδ₂ : δ < 2。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_self`：dist_self (x : α) : dist x x = 0
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `Complex.instContinuousStar`：ContinuousStar ℂ
· 使用定理 `CStarAlgebra.toCompleteSpace`：∀ {A : Type u_1} [self : CStarAlgebra A], 
CompleteSpace A
· 使用定理 `CStarAlgebra.toStarModule`：∀ {A : Type u_1} [self : CStarAlgebra A], Sta
rModule ℂ A
· 使用定理 `instTrivialStarReal`：TrivialStar ℝ
· 使用定理 `Unitary.path_apply`：∀ {A : Type u_1} [inst : CStarAlgebra A] (u v : ↥(un
itary A)) (huv : ‖↑v - ↑u‖ < 2) (t : ↑unitInterval),   (Unitary.path u v huv) t 
= selfAd…
· 使用定理 `selfAdjoint.expUnitary.congr_simp`：∀ {A : Type u_1} [inst : NormedRing A
] [inst_1 : NormedAlgebra ℂ A] [inst_2 : StarRing A] [inst_3 : ContinuousStar A]
   [inst_4 : CompleteSp…
· 使用定理 `star_one`：star_one [MulOneClass R] [StarMul R] : star (1 : R) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `selfAdjoint.expUnitary_coe`：∀ {A : Type u_1} [inst : NormedRing A] [inst
_1 : NormedAlgebra ℂ A] [inst_2 : StarRing A] [inst_3 : ContinuousStar A]   [ins
t_4 : CompleteSp…
· 使用定理 `NormedSpace.exp.congr_simp`：∀ {𝔸 : Type u_3} [inst : Ring 𝔸] [inst_1 : T
opologicalSpace 𝔸] [inst_2 : IsTopologicalRing 𝔸] (x x_1 : 𝔸),   x = x_1 → Norme
dSpace.exp x = N…
· 使用定理 `Unitary.argSelfAdjoint_coe`：∀ {A : Type u_1} [inst : CStarAlgebra A] (u 
: ↥(unitary A)), ↑(Unitary.argSelfAdjoint u) = cfc (fun x => ↑x.arg) ↑u
· 使用定理 `NormedStarGroup.to_continuousStar`：∀ {E : Type u_2} [inst : SeminormedAd
dCommGroup E] [inst_1 : StarAddMonoid E] [NormedStarGroup E], ContinuousStar E
· 使用定理 `CStarRing.to_normedStarGroup`：∀ {E : Type u_2} [inst : NonUnitalNormedRi
ng E] [inst_1 : StarRing E] [CStarRing E], NormedStarGroup E
· 使用定理 `CStarAlgebra.toCStarRing`：∀ {A : Type u_1} [self : CStarAlgebra A], CSta
rRing A
· 使用定理 `StarModule.complexToReal`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst
_1 : Star E] [inst_2 : _root_.Module ℂ E] [StarModule ℂ E], StarModule ℝ E
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用引理 `Unitary.norm_expUnitary_smul_argSelfAdjoint_sub_one_le`：Unitary.norm_exp
Unitary_smul_argSelfAdjoint_sub_one_le (u : unitary A) {t : Real} (ht : t in Set
.Icc 0 1) (hu : ‖(u - 1 : A)‖ < 2) : ‖(expUn…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `inv_mul_cancel`：inv_mul_cancel (a : G) : a⁻¹ * a = 1
（共 41 条，此处仅展示前 30 条）

--- 原说明 ---
Any ball of radius `δ < 2` in the unitary group of a unital C⋆-algebra is path c
onnected.
-/
lemma Unitary.isPathConnected_ball (u : unitary A) (δ : ℝ) (hδ₀ : 0 < δ) (hδ₂ : δ < 2) :
    IsPathConnected (ball (u : unitary A) δ) := by
  suffices IsPathConnected (ball (1 : unitary A) δ) by
    convert! this |>.image (f := (u * ·)) (by fun_prop)
    ext v
    rw [← inv_mul_cancel u]
    simp [-inv_mul_cancel, Subtype.dist_eq, dist_eq_norm, ← mul_sub]
  refine ⟨1, by simpa, fun {u} hu ↦ ?_⟩
  have hu : ‖(u - 1 : A)‖ < δ := by simpa [Subtype.dist_eq, dist_eq_norm] using hu
  refine ⟨path 1 u (hu.trans hδ₂), fun t ↦ ?_⟩
  simpa [Subtype.dist_eq, dist_eq_norm] using
    norm_expUnitary_smul_argSelfAdjoint_sub_one_le u t.2 (hu.trans hδ₂) |>.trans_lt hu

/-- The unitary group in a C⋆-algebra is locally path connected. -/
/-
**Unitary.instLocallyPathConnectedSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Unitary.instLocallyPathConnectedSpace : LocallyPathConnectedSpace (unitary
 A)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `LocallyPathConnectedSpace.of_bases`：LocallyPathConnectedSpace.of_bases {
p : X -> ι -> Prop} {s : X -> ι -> Set X} (h : forall x, (𝓝 x).HasBasis (p x) (s
 x)) (h' : forall x i, p…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `nhds_basis_uniformity`：nhds_basis_uniformity {p : ι -> Prop} {s : ι -> S
etRel α α} (h : (𝓤 α).HasBasis p s) {x : α} : (𝓝 x).HasBasis p fun i => { y | (y
, x) in s i…
· 使用定理 `Metric.uniformity_basis_dist_lt`：uniformity_basis_dist_lt {R : Real} (hR
 : 0 < R) : (𝓤 α).HasBasis (fun r : Real => 0 < r ∧ r < R) fun r => { p : α × α 
| dist p.1 p.2 < r }
· 使用定理 `zero_lt_two`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : Part
ialOrder α] [ZeroLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 2
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用引理 `Unitary.isPathConnected_ball`：Unitary.isPathConnected_ball (u : unitary 
A) (δ : Real) (hδ₀ : 0 < δ) (hδ₂ : δ < 2) : IsPathConnected (ball (u : unitary A
) δ)

--- 原说明 ---
The unitary group in a C⋆-algebra is locally path connected.
-/
instance Unitary.instLocallyPathConnectedSpace : LocallyPathConnectedSpace (unitary A) :=
  .of_bases (fun _ ↦ nhds_basis_uniformity <| uniformity_basis_dist_lt zero_lt_two) <| by
    simpa using! isPathConnected_ball

/-- The path component of the identity in the unitary group of a C⋆-algebra is the set of
unitaries that can be expressed as a product of exponential unitaries. -/
/-
**Unitary.mem_pathComponentOne_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Unitary.mem_pathComponentOne_iff {u : unitary A} : u in pathComponent 1 ↔ 
exists l : List (selfAdjoint A), (l.map expUnitary).prod = u
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedStarGroup.to_continuousStar`：∀ {E : Type u_2} [inst : SeminormedAd
dCommGroup E] [inst_1 : StarAddMonoid E] [NormedStarGroup E], ContinuousStar E
· 使用定理 `CStarRing.to_normedStarGroup`：∀ {E : Type u_2} [inst : NonUnitalNormedRi
ng E] [inst_1 : StarRing E] [CStarRing E], NormedStarGroup E
· 使用定理 `CStarAlgebra.toCStarRing`：∀ {A : Type u_1} [self : CStarAlgebra A], CSta
rRing A
· 使用定理 `CStarAlgebra.toCompleteSpace`：∀ {A : Type u_1} [self : CStarAlgebra A], 
CompleteSpace A
· 使用定理 `CStarAlgebra.toStarModule`：∀ {A : Type u_1} [self : CStarAlgebra A], Sta
rModule ℂ A
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pathComponent_eq_connectedComponent`：pathComponent_eq_connectedComponent
 (x : X) : pathComponent x = connectedComponent x
· 使用定理 `IsClopen.connectedComponent_subset`：IsClopen.connectedComponent_subset {
x} (hs : IsClopen s) (hx : x in s) : connectedComponent x subseteq s
· 使用引理 `IsClopen.of_thickening_subset_self`：IsClopen.of_thickening_subset_self {
δ : Real} (hδ : 0 < δ) (hs : thickening δ s subseteq s) : IsClopen s
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `zero_lt_two`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : Part
ialOrder α] [ZeroLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 2
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Metric.mem_thickening_iff`：mem_thickening_iff {E : Set X} {x : X} : x in
 thickening δ E ↔ exists z in E, dist x z < δ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用引理 `Unitary.expUnitary_eq_mul_inv`：Unitary.expUnitary_eq_mul_inv (u v : unit
ary A) (huv : ‖(u - v : A)‖ < 2) : expUnitary (argSelfAdjoint (u * star v)) = u 
* star v
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Unitary.star_mul_self`：star_mul_self (U : unitary R) : star U * U = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
（共 35 条，此处仅展示前 30 条）

--- 原说明 ---
The path component of the identity in the unitary group of a C⋆-algebra is the s
et of
unitaries that can be expressed as a product of exponential unitaries.
-/
lemma Unitary.mem_pathComponentOne_iff {u : unitary A} :
    u ∈ pathComponent 1 ↔ ∃ l : List (selfAdjoint A), (l.map expUnitary).prod = u := by
  constructor
  · revert u
    simp_rw [← Set.mem_range, ← Set.subset_def, pathComponent_eq_connectedComponent]
    refine IsClopen.connectedComponent_subset ?_ ⟨[], by simp⟩
    refine .of_thickening_subset_self zero_lt_two ?_
    intro u hu
    rw [mem_thickening_iff] at hu
    obtain ⟨v, ⟨⟨l, (hlv : (l.map expUnitary).prod = v)⟩, huv⟩⟩ := hu
    refine ⟨argSelfAdjoint (u * star v) :: l, ?_⟩
    simp [hlv, mul_assoc,
      expUnitary_eq_mul_inv u v (by simpa [Subtype.dist_eq, dist_eq_norm] using! huv)]
  · rintro ⟨l, rfl⟩
    induction l with
    | nil => simp
    | cons x xs ih => simpa using! (joined_one_expUnitary x).mul ih
