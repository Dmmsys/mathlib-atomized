/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Smoothness of `Real.sqrt`

In this file we prove that `Real.sqrt` is infinitely smooth at all points `x ≠ 0` and provide some
dot-notation lemmas.

## Tags

sqrt, differentiable
-/

@[expose] public section


open Set

open scoped Topology

namespace Real

/-- Local homeomorph between `(0, +∞)` and `(0, +∞)` with `toFun = (· ^ 2)` and
`invFun = Real.sqrt`. -/
/-
**Real.sqPartialHomeomorph** 是 Mathlib 中的一个定义，位于命名空间 `Real`。
形式化陈述：sqPartialHomeomorph : OpenPartialHomeomorph Real Real where toFun x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Local homeomorph between `(0, +∞)` and `(0, +∞)` with `toFun = (· ^ 2)` and
`invFun = Real.sqrt`.
-/
noncomputable def sqPartialHomeomorph : OpenPartialHomeomorph ℝ ℝ where
  toFun x := x ^ 2
  invFun := (√·)
  source := Ioi 0
  target := Ioi 0
  map_source' _ h := mem_Ioi.2 (pow_pos (mem_Ioi.1 h) _)
  map_target' _ h := mem_Ioi.2 (sqrt_pos.2 h)
  left_inv' _ h := sqrt_sq (le_of_lt h)
  right_inv' _ h := sq_sqrt (le_of_lt h)
  open_source := isOpen_Ioi
  open_target := isOpen_Ioi
  continuousOn_toFun := (continuous_pow 2).continuousOn
  continuousOn_invFun := continuousOn_id.sqrt
/-
**Real.deriv_sqrt_aux** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：deriv_sqrt_aux {x : Real} (hx : x != 0) : HasStrictDerivAt (√·) (1 / (2 * 
√x)) x ∧ forall n, ContDiffAt Real n (√·) x
参数：hx : x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Ne.lt_or_gt`：Ne.lt_or_gt (h : a != b) : a < b ∨ b < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.sqrt_eq_zero_of_nonpos`：sqrt_eq_zero_of_nonpos (h : x <= 0) : √x = 
0
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `gt_mem_nhds`：∀ {α : Type u} [ts : TopologicalSpace α] [inst : Preorder α
] [OrderTopology α] {a b : α},   b < a → ∀ᶠ (x : α) in nhds b, x < a
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `HasStrictDerivAt.congr_of_eventuallyEq`：HasStrictDerivAt.congr_of_eventu
allyEq (h : HasStrictDerivAt f f' x) (h₁ : f =ᶠ[𝓝 x] f₁) : HasStrictDerivAt f₁ f
' x
· 使用定理 `hasStrictDerivAt_const`：hasStrictDerivAt_const : HasStrictDerivAt (fun _
 => c) 0 x
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `ContDiffAt.congr_of_eventuallyEq`：ContDiffAt.congr_of_eventuallyEq (h : 
ContDiffAt 𝕜 n f x) (hg : f₁ =ᶠ[𝓝 x] f) : ContDiffAt 𝕜 n f₁ x
· 使用定理 `contDiffAt_const`：contDiffAt_const {c : F} : ContDiffAt 𝕜 n (fun _ : E =
> c) x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
（共 44 条，此处仅展示前 30 条）
-/
theorem deriv_sqrt_aux {x : ℝ} (hx : x ≠ 0) :
    HasStrictDerivAt (√·) (1 / (2 * √x)) x ∧ ∀ n, ContDiffAt ℝ n (√·) x := by
  rcases hx.lt_or_gt with hx | hx
  · rw [sqrt_eq_zero_of_nonpos hx.le, mul_zero, div_zero]
    have : (√·) =ᶠ[𝓝 x] fun _ => 0 := (gt_mem_nhds hx).mono fun x hx => sqrt_eq_zero_of_nonpos hx.le
    exact
      ⟨(hasStrictDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq this.symm, fun n =>
        contDiffAt_const.congr_of_eventuallyEq this⟩
  · have : ↑2 * √x ^ (2 - 1) ≠ 0 := by simp [(sqrt_pos.2 hx).ne', @two_ne_zero ℝ]
    constructor
    · simpa using! sqPartialHomeomorph.hasStrictDerivAt_symm hx this (hasStrictDerivAt_pow 2 _)
    · exact fun n => sqPartialHomeomorph.contDiffAt_symm_deriv this hx (hasDerivAt_pow 2 (√x))
        (contDiffAt_id.pow 2)
/-
**Real.hasStrictDerivAt_sqrt** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：hasStrictDerivAt_sqrt {x : Real} (hx : x != 0) : HasStrictDerivAt (√·) (1 
/ (2 * √x)) x
参数：hx : x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Real.deriv_sqrt_aux`：deriv_sqrt_aux {x : Real} (hx : x != 0) : HasStrict
DerivAt (√·) (1 / (2 * √x)) x ∧ forall n, ContDiffAt Real n (√·) x
-/
theorem hasStrictDerivAt_sqrt {x : ℝ} (hx : x ≠ 0) : HasStrictDerivAt (√·) (1 / (2 * √x)) x :=
  (deriv_sqrt_aux hx).1

@[fun_prop]
/-
**Real.contDiffAt_sqrt** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：contDiffAt_sqrt {x : Real} {n : WithTop Nat∞} (hx : x != 0) : ContDiffAt R
eal n (√·) x
参数：hx : x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Real.deriv_sqrt_aux`：deriv_sqrt_aux {x : Real} (hx : x != 0) : HasStrict
DerivAt (√·) (1 / (2 * √x)) x ∧ forall n, ContDiffAt Real n (√·) x
-/
theorem contDiffAt_sqrt {x : ℝ} {n : WithTop ℕ∞} (hx : x ≠ 0) : ContDiffAt ℝ n (√·) x :=
  (deriv_sqrt_aux hx).2 n
/-
**Real.hasDerivAt_sqrt** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：hasDerivAt_sqrt {x : Real} (hx : x != 0) : HasDerivAt (√·) (1 / (2 * √x)) 
x
参数：hx : x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasStrictDerivAt.hasDerivAt`：HasStrictDerivAt.hasDerivAt (h : HasStrictD
erivAt f f' x) : HasDerivAt f f' x
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Real.hasStrictDerivAt_sqrt`：hasStrictDerivAt_sqrt {x : Real} (hx : x != 
0) : HasStrictDerivAt (√·) (1 / (2 * √x)) x
-/
theorem hasDerivAt_sqrt {x : ℝ} (hx : x ≠ 0) : HasDerivAt (√·) (1 / (2 * √x)) x :=
  (hasStrictDerivAt_sqrt hx).hasDerivAt

end Real

open Real

section deriv

variable {f : ℝ → ℝ} {s : Set ℝ} {f' x : ℝ}

/-
**HasDerivWithinAt.sqrt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivWithinAt.sqrt (hf : HasDerivWithinAt f f' s x) (hx : f x != 0) : H
asDerivWithinAt (fun y => √(f y)) (f' / (2 * √(f x))) s x
参数：hf : HasDerivWithinAt f f' s x；hx : f x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `HasDerivWithinAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFi
eld 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [in
st_3 : Topologica…
· 使用定理 `div_eq_inv_mul`：div_eq_inv_mul : a / b = b⁻¹ * a
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `HasDerivAt.comp_hasDerivWithinAt`：HasDerivAt.comp_hasDerivWithinAt (hh₂ 
: HasDerivAt h₂ h₂' (h x)) (hh : HasDerivWithinAt h h' s x) : HasDerivWithinAt (
h₂ ∘ h) (h₂' * h') s x
· 使用定理 `Real.hasDerivAt_sqrt`：hasDerivAt_sqrt {x : Real} (hx : x != 0) : HasDeri
vAt (√·) (1 / (2 * √x)) x
-/
theorem HasDerivWithinAt.sqrt (hf : HasDerivWithinAt f f' s x) (hx : f x ≠ 0) :
    HasDerivWithinAt (fun y => √(f y)) (f' / (2 * √(f x))) s x := by
  simpa only [(· ∘ ·), div_eq_inv_mul, mul_one] using!
    (hasDerivAt_sqrt hx).comp_hasDerivWithinAt x hf
/-
**HasDerivAt.sqrt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasDerivAt.sqrt (hf : HasDerivAt f f' x) (hx : f x != 0) : HasDerivAt (fun
 y => √(f y)) (f' / (2 * √(f x))) x
参数：hf : HasDerivAt f f' x；hx : f x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `HasDerivAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜]
 {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [inst_3 :
 Topologica…
· 使用定理 `div_eq_inv_mul`：div_eq_inv_mul : a / b = b⁻¹ * a
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `HasDerivAt.comp`：HasDerivAt.comp (hh₂ : HasDerivAt h₂ h₂' (h x)) (hh : H
asDerivAt h h' x) : HasDerivAt (h₂ ∘ h) (h₂' * h') x
· 使用定理 `Real.hasDerivAt_sqrt`：hasDerivAt_sqrt {x : Real} (hx : x != 0) : HasDeri
vAt (√·) (1 / (2 * √x)) x
-/
theorem HasDerivAt.sqrt (hf : HasDerivAt f f' x) (hx : f x ≠ 0) :
    HasDerivAt (fun y => √(f y)) (f' / (2 * √(f x))) x := by
  simpa only [(· ∘ ·), div_eq_inv_mul, mul_one] using! (hasDerivAt_sqrt hx).comp x hf
/-
**HasStrictDerivAt.sqrt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictDerivAt.sqrt (hf : HasStrictDerivAt f f' x) (hx : f x != 0) : Has
StrictDerivAt (fun t => √(f t)) (f' / (2 * √(f x))) x
参数：hf : HasStrictDerivAt f f' x；hx : f x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `HasStrictDerivAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFi
eld 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [in
st_3 : Topologica…
· 使用定理 `div_eq_inv_mul`：div_eq_inv_mul : a / b = b⁻¹ * a
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `HasStrictDerivAt.comp`：HasStrictDerivAt.comp (hh₂ : HasStrictDerivAt h₂ 
h₂' (h x)) (hh : HasStrictDerivAt h h' x) : HasStrictDerivAt (h₂ ∘ h) (h₂' * h')
 x
· 使用定理 `Real.hasStrictDerivAt_sqrt`：hasStrictDerivAt_sqrt {x : Real} (hx : x != 
0) : HasStrictDerivAt (√·) (1 / (2 * √x)) x
-/
theorem HasStrictDerivAt.sqrt (hf : HasStrictDerivAt f f' x) (hx : f x ≠ 0) :
    HasStrictDerivAt (fun t => √(f t)) (f' / (2 * √(f x))) x := by
  simpa only [(· ∘ ·), div_eq_inv_mul, mul_one] using! (hasStrictDerivAt_sqrt hx).comp x hf
/-
**derivWithin_sqrt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：derivWithin_sqrt (hf : DifferentiableWithinAt Real f s x) (hx : f x != 0) 
(hxs : UniqueDiffWithinAt Real s x) : derivWithin (fun x => √(f x)) s x = derivW
ithin f s x / (2 * √(f x))
参数：hf : DifferentiableWithinAt Real f s x；hx : f x != 0；hxs : UniqueDiffWithinAt
 Real s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivWithinAt.derivWithin`：HasDerivWithinAt.derivWithin (h : HasDeriv
WithinAt f f' s x) (hxs : UniqueDiffWithinAt 𝕜 s x) : derivWithin f s x = f'
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `HasDerivWithinAt.sqrt`：HasDerivWithinAt.sqrt (hf : HasDerivWithinAt f f'
 s x) (hx : f x != 0) : HasDerivWithinAt (fun y => √(f y)) (f' / (2 * √(f x))) s
 x
· 使用定理 `DifferentiableWithinAt.hasDerivWithinAt`：DifferentiableWithinAt.hasDeriv
WithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasDerivWithinAt f (derivWithin 
f s x) s x
-/
theorem derivWithin_sqrt (hf : DifferentiableWithinAt ℝ f s x) (hx : f x ≠ 0)
    (hxs : UniqueDiffWithinAt ℝ s x) :
    derivWithin (fun x => √(f x)) s x = derivWithin f s x / (2 * √(f x)) :=
  (hf.hasDerivWithinAt.sqrt hx).derivWithin hxs

@[simp]
/-
**deriv_sqrt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：deriv_sqrt (hf : DifferentiableAt Real f x) (hx : f x != 0) : deriv (fun x
 => √(f x)) x = deriv f x / (2 * √(f x))
参数：hf : DifferentiableAt Real f x；hx : f x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `HasDerivAt.sqrt`：HasDerivAt.sqrt (hf : HasDerivAt f f' x) (hx : f x != 0
) : HasDerivAt (fun y => √(f y)) (f' / (2 * √(f x))) x
· 使用定理 `DifferentiableAt.hasDerivAt`：DifferentiableAt.hasDerivAt (h : Differenti
ableAt 𝕜 f x) : HasDerivAt f (deriv f x) x
-/
theorem deriv_sqrt (hf : DifferentiableAt ℝ f x) (hx : f x ≠ 0) :
    deriv (fun x => √(f x)) x = deriv f x / (2 * √(f x)) :=
  (hf.hasDerivAt.sqrt hx).deriv

end deriv

section fderiv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ} {n : WithTop ℕ∞}
  {s : Set E} {x : E} {f' : StrongDual ℝ E}

/-
**HasFDerivAt.sqrt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivAt.sqrt (hf : HasFDerivAt f f' x) (hx : f x != 0) : HasFDerivAt (
fun y => √(f y)) ((1 / (2 * √(f x))) • f') x
参数：hf : HasFDerivAt f f' x；hx : f x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.comp_hasFDerivAt`：HasDerivAt.comp_hasFDerivAt {f : E -> 𝕜'} {
f' : E ->L[𝕜] 𝕜'} (x) (hh : HasDerivAt h₂ h₂' (f x)) (hf : HasFDerivAt f f' x) :
 HasFDerivAt (h₂ …
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Real.hasDerivAt_sqrt`：hasDerivAt_sqrt {x : Real} (hx : x != 0) : HasDeri
vAt (√·) (1 / (2 * √x)) x
-/
theorem HasFDerivAt.sqrt (hf : HasFDerivAt f f' x) (hx : f x ≠ 0) :
    HasFDerivAt (fun y => √(f y)) ((1 / (2 * √(f x))) • f') x :=
  (hasDerivAt_sqrt hx).comp_hasFDerivAt x hf
/-
**HasStrictFDerivAt.sqrt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasStrictFDerivAt.sqrt (hf : HasStrictFDerivAt f f' x) (hx : f x != 0) : H
asStrictFDerivAt (fun y => √(f y)) ((1 / (2 * √(f x))) • f') x
参数：hf : HasStrictFDerivAt f f' x；hx : f x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasStrictDerivAt.comp_hasStrictFDerivAt`：HasStrictDerivAt.comp_hasStrict
FDerivAt {f : E -> 𝕜'} {f' : E ->L[𝕜] 𝕜'} (x) (hh : HasStrictDerivAt h₂ h₂' (f x
)) (hf : HasStrictFDerivAt f …
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Real.hasStrictDerivAt_sqrt`：hasStrictDerivAt_sqrt {x : Real} (hx : x != 
0) : HasStrictDerivAt (√·) (1 / (2 * √x)) x
-/
theorem HasStrictFDerivAt.sqrt (hf : HasStrictFDerivAt f f' x) (hx : f x ≠ 0) :
    HasStrictFDerivAt (fun y => √(f y)) ((1 / (2 * √(f x))) • f') x :=
  (hasStrictDerivAt_sqrt hx).comp_hasStrictFDerivAt x hf
/-
**HasFDerivWithinAt.sqrt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFDerivWithinAt.sqrt (hf : HasFDerivWithinAt f f' s x) (hx : f x != 0) :
 HasFDerivWithinAt (fun y => √(f y)) ((1 / (2 * √(f x))) • f') s x
参数：hf : HasFDerivWithinAt f f' s x；hx : f x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.comp_hasFDerivWithinAt`：HasDerivAt.comp_hasFDerivWithinAt {f 
: E -> 𝕜'} {f' : E ->L[𝕜] 𝕜'} {s} (x) (hh : HasDerivAt h₂ h₂' (f x)) (hf : HasFD
erivWithinAt f f' s x) …
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Real.hasDerivAt_sqrt`：hasDerivAt_sqrt {x : Real} (hx : x != 0) : HasDeri
vAt (√·) (1 / (2 * √x)) x
-/
theorem HasFDerivWithinAt.sqrt (hf : HasFDerivWithinAt f f' s x) (hx : f x ≠ 0) :
    HasFDerivWithinAt (fun y => √(f y)) ((1 / (2 * √(f x))) • f') s x :=
  (hasDerivAt_sqrt hx).comp_hasFDerivWithinAt x hf

@[fun_prop]
/-
**DifferentiableWithinAt.sqrt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableWithinAt.sqrt (hf : DifferentiableWithinAt Real f s x) (hx :
 f x != 0) : DifferentiableWithinAt Real (fun y => √(f y)) s x
参数：hf : DifferentiableWithinAt Real f s x；hx : f x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivWithinAt.differentiableWithinAt`：HasFDerivWithinAt.differentiab
leWithinAt (h : HasFDerivWithinAt f f' s x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `HasFDerivWithinAt.sqrt`：HasFDerivWithinAt.sqrt (hf : HasFDerivWithinAt f
 f' s x) (hx : f x != 0) : HasFDerivWithinAt (fun y => √(f y)) ((1 / (2 * √(f x)
)) • f') s x
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
-/
theorem DifferentiableWithinAt.sqrt (hf : DifferentiableWithinAt ℝ f s x) (hx : f x ≠ 0) :
    DifferentiableWithinAt ℝ (fun y => √(f y)) s x :=
  (hf.hasFDerivWithinAt.sqrt hx).differentiableWithinAt

@[fun_prop]
/-
**DifferentiableAt.sqrt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableAt.sqrt (hf : DifferentiableAt Real f x) (hx : f x != 0) : D
ifferentiableAt Real (fun y => √(f y)) x
参数：hf : DifferentiableAt Real f x；hx : f x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.differentiableAt`：HasFDerivAt.differentiableAt (h : HasFDeri
vAt f f' x) : DifferentiableAt 𝕜 f x
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `HasFDerivAt.sqrt`：HasFDerivAt.sqrt (hf : HasFDerivAt f f' x) (hx : f x !
= 0) : HasFDerivAt (fun y => √(f y)) ((1 / (2 * √(f x))) • f') x
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
-/
theorem DifferentiableAt.sqrt (hf : DifferentiableAt ℝ f x) (hx : f x ≠ 0) :
    DifferentiableAt ℝ (fun y => √(f y)) x :=
  (hf.hasFDerivAt.sqrt hx).differentiableAt

@[fun_prop]
/-
**DifferentiableOn.sqrt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableOn.sqrt (hf : DifferentiableOn Real f s) (hs : forall x in s
, f x != 0) : DifferentiableOn Real (fun y => √(f y)) s
参数：hf : DifferentiableOn Real f s；hs : forall x in s, f x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableWithinAt.sqrt`：DifferentiableWithinAt.sqrt (hf : Different
iableWithinAt Real f s x) (hx : f x != 0) : DifferentiableWithinAt Real (fun y =
> √(f y)) s x
-/
theorem DifferentiableOn.sqrt (hf : DifferentiableOn ℝ f s) (hs : ∀ x ∈ s, f x ≠ 0) :
    DifferentiableOn ℝ (fun y => √(f y)) s := fun x hx => (hf x hx).sqrt (hs x hx)

@[fun_prop]
/-
**Differentiable.sqrt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Differentiable.sqrt (hf : Differentiable Real f) (hs : forall x, f x != 0)
 : Differentiable Real fun y => √(f y)
参数：hf : Differentiable Real f；hs : forall x, f x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.sqrt`：DifferentiableAt.sqrt (hf : DifferentiableAt Real
 f x) (hx : f x != 0) : DifferentiableAt Real (fun y => √(f y)) x
-/
theorem Differentiable.sqrt (hf : Differentiable ℝ f) (hs : ∀ x, f x ≠ 0) :
    Differentiable ℝ fun y => √(f y) := fun x => (hf x).sqrt (hs x)
/-
**fderivWithin_sqrt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderivWithin_sqrt (hf : DifferentiableWithinAt Real f s x) (hx : f x != 0)
 (hxs : UniqueDiffWithinAt Real s x) : fderivWithin Real (fun x => √(f x)) s x =
 (1 / (2 * √(f x))) • fderivWithin Real f s x
参数：hf : DifferentiableWithinAt Real f s x；hx : f x != 0；hxs : UniqueDiffWithinAt
 Real s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivWithinAt.fderivWithin`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜
 E] [inst_3 : Topolo…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `HasFDerivWithinAt.sqrt`：HasFDerivWithinAt.sqrt (hf : HasFDerivWithinAt f
 f' s x) (hx : f x != 0) : HasFDerivWithinAt (fun y => √(f y)) ((1 / (2 * √(f x)
)) • f') s x
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
-/
theorem fderivWithin_sqrt (hf : DifferentiableWithinAt ℝ f s x) (hx : f x ≠ 0)
    (hxs : UniqueDiffWithinAt ℝ s x) :
    fderivWithin ℝ (fun x => √(f x)) s x = (1 / (2 * √(f x))) • fderivWithin ℝ f s x :=
  (hf.hasFDerivWithinAt.sqrt hx).fderivWithin hxs

@[simp]
/-
**fderiv_sqrt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：fderiv_sqrt (hf : DifferentiableAt Real f x) (hx : f x != 0) : fderiv Real
 (fun x => √(f x)) x = (1 / (2 * √(f x))) • fderiv Real f x
参数：hf : DifferentiableAt Real f x；hx : f x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasFDerivAt.fderiv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 
: Topolo…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `HasFDerivAt.sqrt`：HasFDerivAt.sqrt (hf : HasFDerivAt f f' x) (hx : f x !
= 0) : HasFDerivAt (fun y => √(f y)) ((1 / (2 * √(f x))) • f') x
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
-/
theorem fderiv_sqrt (hf : DifferentiableAt ℝ f x) (hx : f x ≠ 0) :
    fderiv ℝ (fun x => √(f x)) x = (1 / (2 * √(f x))) • fderiv ℝ f x :=
  (hf.hasFDerivAt.sqrt hx).fderiv

@[fun_prop]
/-
**ContDiffAt.sqrt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffAt.sqrt (hf : ContDiffAt Real n f x) (hx : f x != 0) : ContDiffAt 
Real n (fun y => √(f y)) x
参数：hf : ContDiffAt Real n f x；hx : f x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.comp`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} {G : Typ
e u_4} [inst : NontriviallyNormedField 𝕜]   [inst_1 : NormedAddCommGroup E] [ins
t_2 :…
· 使用定理 `Real.contDiffAt_sqrt`：contDiffAt_sqrt {x : Real} {n : WithTop Nat∞} (hx 
: x != 0) : ContDiffAt Real n (√·) x
-/
theorem ContDiffAt.sqrt (hf : ContDiffAt ℝ n f x) (hx : f x ≠ 0) :
    ContDiffAt ℝ n (fun y => √(f y)) x :=
  (contDiffAt_sqrt hx).comp x hf

@[fun_prop]
/-
**ContDiffWithinAt.sqrt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffWithinAt.sqrt (hf : ContDiffWithinAt Real n f s x) (hx : f x != 0)
 : ContDiffWithinAt Real n (fun y => √(f y)) s x
参数：hf : ContDiffWithinAt Real n f s x；hx : f x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.comp_contDiffWithinAt`：ContDiffAt.comp_contDiffWithinAt (x : 
E) (hg : ContDiffAt 𝕜 n g (f x)) (hf : ContDiffWithinAt 𝕜 n f s x) : ContDiffWit
hinAt 𝕜 n (g ∘ f) s x
· 使用定理 `Real.contDiffAt_sqrt`：contDiffAt_sqrt {x : Real} {n : WithTop Nat∞} (hx 
: x != 0) : ContDiffAt Real n (√·) x
-/
theorem ContDiffWithinAt.sqrt (hf : ContDiffWithinAt ℝ n f s x) (hx : f x ≠ 0) :
    ContDiffWithinAt ℝ n (fun y => √(f y)) s x :=
  (contDiffAt_sqrt hx).comp_contDiffWithinAt x hf

@[fun_prop]
/-
**ContDiffOn.sqrt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffOn.sqrt (hf : ContDiffOn Real n f s) (hs : forall x in s, f x != 0
) : ContDiffOn Real n (fun y => √(f y)) s
参数：hf : ContDiffOn Real n f s；hs : forall x in s, f x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffWithinAt.sqrt`：ContDiffWithinAt.sqrt (hf : ContDiffWithinAt Real
 n f s x) (hx : f x != 0) : ContDiffWithinAt Real n (fun y => √(f y)) s x
-/
theorem ContDiffOn.sqrt (hf : ContDiffOn ℝ n f s) (hs : ∀ x ∈ s, f x ≠ 0) :
    ContDiffOn ℝ n (fun y => √(f y)) s := fun x hx => (hf x hx).sqrt (hs x hx)

@[fun_prop]
/-
**ContDiff.sqrt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiff.sqrt (hf : ContDiff Real n f) (h : forall x, f x != 0) : ContDiff
 Real n fun y => √(f y)
参数：hf : ContDiff Real n f；h : forall x, f x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `contDiff_iff_contDiffAt`：contDiff_iff_contDiffAt : ContDiff 𝕜 n f ↔ fora
ll x, ContDiffAt 𝕜 n f x
· 使用定理 `ContDiffAt.sqrt`：ContDiffAt.sqrt (hf : ContDiffAt Real n f x) (hx : f x 
!= 0) : ContDiffAt Real n (fun y => √(f y)) x
· 使用定理 `ContDiff.contDiffAt`：ContDiff.contDiffAt (h : ContDiff 𝕜 n f) : ContDiff
At 𝕜 n f x
-/
theorem ContDiff.sqrt (hf : ContDiff ℝ n f) (h : ∀ x, f x ≠ 0) : ContDiff ℝ n fun y => √(f y) :=
  contDiff_iff_contDiffAt.2 fun x => hf.contDiffAt.sqrt (h x)

end fderiv

