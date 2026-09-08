/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Grönwall's inequality

The main technical result of this file is the Grönwall-like inequality
`norm_le_gronwallBound_of_norm_deriv_right_le`. It states that if `f : ℝ → E` satisfies `‖f a‖ ≤ δ`
and `∀ x ∈ [a, b), ‖f' x‖ ≤ K * ‖f x‖ + ε`, then for all `x ∈ [a, b]` we have `‖f x‖ ≤ δ * exp (K *
x) + (ε / K) * (exp (K * x) - 1)`.

Then we use this inequality to prove some estimates on the possible rate of growth of the distance
between two approximate or exact solutions of an ordinary differential equation.

The proofs are based on [Hubbard and West, *Differential Equations: A Dynamical Systems Approach*,
Sec. 4.5][HubbardWest-ode], where `norm_le_gronwallBound_of_norm_deriv_right_le` is called
“Fundamental Inequality”.

## TODO

- Once we have FTC, prove an inequality for a function satisfying `‖f' x‖ ≤ K x * ‖f x‖ + ε`,
  or more generally `liminf_{y→x+0} (f y - f x)/(y - x) ≤ K x * f x + ε` with any sign
  of `K x` and `f x`.
-/

@[expose] public section

open Metric Set Asymptotics Filter Real
open scoped Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### Technical lemmas about `gronwallBound` -/


/-- Upper bound used in several Grönwall-like inequalities. -/
/-
**gronwallBound** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：gronwallBound (δ K ε x : Real) : Real
参数：δ K ε x : Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Upper bound used in several Grönwall-like inequalities.
-/
noncomputable def gronwallBound (δ K ε x : ℝ) : ℝ :=
  if K = 0 then δ + ε * x else δ * exp (K * x) + ε / K * (exp (K * x) - 1)
/-
**gronwallBound_K0** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：gronwallBound_K0 (δ ε : Real) : gronwallBound δ 0 ε = fun x => δ + ε * x
参数：δ ε : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
theorem gronwallBound_K0 (δ ε : ℝ) : gronwallBound δ 0 ε = fun x => δ + ε * x :=
  funext fun _ => if_pos rfl
/-
**gronwallBound_of_K_ne_0** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：gronwallBound_of_K_ne_0 {δ K ε : Real} (hK : K != 0) : gronwallBound δ K ε
 = fun x => δ * exp (K * x) + ε / K * (exp (K * x) - 1)
参数：hK : K != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem gronwallBound_of_K_ne_0 {δ K ε : ℝ} (hK : K ≠ 0) :
    gronwallBound δ K ε = fun x => δ * exp (K * x) + ε / K * (exp (K * x) - 1) :=
  funext fun _ => if_neg hK
/-
**hasDerivAt_gronwallBound** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivAt_gronwallBound (δ K ε x : Real) : HasDerivAt (gronwallBound δ K 
ε) (K * gronwallBound δ K ε x + ε) x
参数：δ K ε x : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `HasDerivAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜]
 {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [inst_3 :
 Topologica…
· 使用定理 `gronwallBound_K0`：gronwallBound_K0 (δ ε : Real) : gronwallBound δ 0 ε = 
fun x => δ + ε * x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `HasDerivAt.const_add`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜] 
{F : Type v} [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] {f : 𝕜
 → F} {f' …
· 使用定理 `HasDerivAt.const_mul`：HasDerivAt.const_mul (c : 𝔸) (hd : HasDerivAt d d'
 x) : HasDerivAt (fun y => c * d y) (c * d') x
· 使用定理 `hasDerivAt_id`：hasDerivAt_id : HasDerivAt id 1 x
· 使用定理 `gronwallBound_of_K_ne_0`：gronwallBound_of_K_ne_0 {δ K ε : Real} (hK : K 
!= 0) : gronwallBound δ K ε = fun x => δ * exp (K * x) + ε / K * (exp (K * x) - 
1)
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_eq_cancel_eq`：eq_eq_cancel_eq {M : Type*} [M
onoidWithZero M] [IsLeftCancelMulZero M] {e₁ e₂ f₁ f₂ L : M} (H₁ : e₁ = L * f₁) 
(H₂ : e₂ = L * f₂) (HL : L != …
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `instIsCancelMulZero`：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀], IsCanc
elMulZero G₀
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_mul_of_eq_eq_eq_mul`：eq_mul_of_eq_eq_eq_mul 
{M : Type*} [Mul M] {a b c D e f : M} (h₁ : a = b) (h₂ : b = c) (h₃ : c = D * e)
 (h₄ : e = f) : a = D * f
· 使用定理 `Mathlib.Tactic.FieldSimp.subst_add`：subst_add {M : Type*} [Semiring M] {
x₁ x₂ X₁ X₂ Y y a : M} (h₁ : x₁ = a * X₁) (h₂ : x₂ = a * X₂) (H_atom : X₁ + X₂ =
 Y) (hy : a * Y = y) : x…
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval`：mul_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al * l₂.eval = l.eval) : x₁ *…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval₃`：mul_eq_eval₃ [CommGroupWithZer
o M] {a₁ : Int × M} (a₂ : Int × M) {l₁ l₂ l : NF M} (h : (a₁ ::ᵣ l₁).eval * l₂.e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
（共 87 条，此处仅展示前 30 条）
-/
theorem hasDerivAt_gronwallBound (δ K ε x : ℝ) :
    HasDerivAt (gronwallBound δ K ε) (K * gronwallBound δ K ε x + ε) x := by
  by_cases hK : K = 0
  · subst K
    simp only [gronwallBound_K0, zero_mul, zero_add]
    convert! ((hasDerivAt_id x).const_mul ε).const_add δ
    rw [mul_one]
  · simp only [gronwallBound_of_K_ne_0 hK]
    convert!
      (((hasDerivAt_id x).const_mul K).exp.const_mul δ).add
        ((((hasDerivAt_id x).const_mul K).exp.sub_const 1).const_mul (ε / K)) using 1
    simp only [id]
    field
/-
**hasDerivAt_gronwallBound_shift** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasDerivAt_gronwallBound_shift (δ K ε x a : Real) : HasDerivAt (fun y => g
ronwallBound δ K ε (y - a)) (K * gronwallBound δ K ε (x - a) + ε) x
参数：δ K ε x a : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `id.eq_1`：∀ {α : Sort u} (a : α), id a = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `HasDerivAt.comp`：HasDerivAt.comp (hh₂ : HasDerivAt h₂ h₂' (h x)) (hh : H
asDerivAt h h' x) : HasDerivAt (h₂ ∘ h) (h₂' * h') x
· 使用定理 `hasDerivAt_gronwallBound`：hasDerivAt_gronwallBound (δ K ε x : Real) : Ha
sDerivAt (gronwallBound δ K ε) (K * gronwallBound δ K ε x + ε) x
· 使用定理 `HasDerivAt.sub_const`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜] 
{F : Type v} [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] {f : 𝕜
 → F} {f' …
· 使用定理 `hasDerivAt_id`：hasDerivAt_id : HasDerivAt id 1 x
-/
theorem hasDerivAt_gronwallBound_shift (δ K ε x a : ℝ) :
    HasDerivAt (fun y => gronwallBound δ K ε (y - a)) (K * gronwallBound δ K ε (x - a) + ε) x := by
  convert! (hasDerivAt_gronwallBound δ K ε _).comp x ((hasDerivAt_id x).sub_const a) using 1
  rw [id, mul_one]
/-
**gronwallBound_x0** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：gronwallBound_x0 (δ K ε : Real) : gronwallBound δ K ε 0 = δ
参数：δ K ε : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Real.exp_zero`：exp_zero : exp 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem gronwallBound_x0 (δ K ε : ℝ) : gronwallBound δ K ε 0 = δ := by
  by_cases hK : K = 0
  · simp only [gronwallBound, if_pos hK, mul_zero, add_zero]
  · simp only [gronwallBound, if_neg hK, mul_zero, exp_zero, sub_self, mul_one,
      add_zero]
/-
**gronwallBound_** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem gronwallBound_ε0 (δ K x : ℝ) : gronwallBound δ K 0 x = δ * exp (K * x) := by
  by_cases hK : K = 0
  · simp only [gronwallBound_K0, hK, zero_mul, exp_zero, add_zero, mul_one]
  · simp only [gronwallBound_of_K_ne_0 hK, zero_div, zero_mul, add_zero]
/-
**gronwallBound_** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem gronwallBound_ε0_δ0 (K x : ℝ) : gronwallBound 0 K 0 x = 0 := by
  simp only [gronwallBound_ε0, zero_mul]
/-
**gronwallBound_continuous_** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem gronwallBound_continuous_ε (δ K x : ℝ) : Continuous fun ε => gronwallBound δ K ε x := by
  by_cases hK : K = 0
  · simp only [gronwallBound_K0, hK]
    fun_prop
  · simp only [gronwallBound_of_K_ne_0 hK]
    fun_prop

/-- The Grönwall bound is monotone with respect to the time variable `x`. -/
/-
**gronwallBound_mono** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：gronwallBound_mono {δ K ε : Real} (hδ : 0 <= δ) (hε : 0 <= ε) (hK : 0 <= K
) : Monotone (gronwallBound δ K ε)
参数：hδ : 0 <= δ；hε : 0 <= ε；hK : 0 <= K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `lt_of_le_of_ne'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≠ b → b < a
· 使用定理 `Real.exp_monotone`：exp_monotone : Monotone exp
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `sub_le_sub_right`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [Ad
dRightMono α] {a b : α}, a ≤ b → ∀ (c : α), a - c ≤ b - c
· 使用引理 `Mathlib.Meta.Positivity.div_nonneg_of_nonneg_of_pos`：div_nonneg_of_nonne
g_of_pos [PosMulReflectLT α] (ha : 0 <= a) (hb : 0 < b) : 0 <= a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R

--- 原说明 ---
The Grönwall bound is monotone with respect to the time variable `x`.
-/
lemma gronwallBound_mono {δ K ε : ℝ} (hδ : 0 ≤ δ) (hε : 0 ≤ ε) (hK : 0 ≤ K) :
    Monotone (gronwallBound δ K ε) := by
  intro x₁ x₂ hx
  unfold gronwallBound
  split_ifs with hK₀
  · gcongr
  · have hK_pos : 0 < K := by positivity
    gcongr

/-! ### Inequality and corollaries -/

/-- A Grönwall-like inequality: if `f : ℝ → ℝ` is continuous on `[a, b]` and satisfies
the inequalities `f a ≤ δ` and
`∀ x ∈ [a, b), liminf_{z→x+0} (f z - f x)/(z - x) ≤ K * (f x) + ε`, then `f x`
is bounded by `gronwallBound δ K ε (x - a)` on `[a, b]`.

See also `norm_le_gronwallBound_of_norm_deriv_right_le` for a version bounding `‖f x‖`,
`f : ℝ → E`. -/
/-
**le_gronwallBound_of_liminf_deriv_right_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_gronwallBound_of_liminf_deriv_right_le {f f' : Real -> Real} {δ K ε : R
eal} {a b : Real} (hf : ContinuousOn f (Icc a b)) (hf' : forall x in Ico a b, fo
rall r, f' x < r -> existsᶠ z in 𝓝[>] x, (z - x)⁻¹ * (f z - f x) < r) (ha : f a 
<= δ) (bound : forall x in Ico a b, f' x <= K * f x + ε) : forall x in Icc a b, 
f x <= gronwallBound δ K ε (x - a)
参数：hf : ContinuousOn f (Icc a b)；hf' : forall x in Ico a b, forall r, f' x < r -
> existsᶠ z in 𝓝[>] x, (z - x)⁻¹ * (f z - f x) < r；ha : f a <= δ；bound : forall 
x in Ico a b, f' x <= K * f x + ε。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `image_le_of_liminf_slope_right_lt_deriv_boundary`：image_le_of_liminf_slo
pe_right_lt_deriv_boundary {f f' : Real -> Real} {a b : Real} (hf : ContinuousOn
 f (Icc a b)) -- `hf'` actually says `…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `gronwallBound_x0`：gronwallBound_x0 (δ K ε : Real) : gronwallBound δ K ε 
0 = δ
· 使用定理 `hasDerivAt_gronwallBound_shift`：hasDerivAt_gronwallBound_shift (δ K ε x 
a : Real) : HasDerivAt (fun y => gronwallBound δ K ε (y - a)) (K * gronwallBound
 δ K ε (x - a) + ε) …
· 使用定理 `ContinuousWithinAt.closure_le`：ContinuousWithinAt.closure_le [Topologica
lSpace β] {f g : β -> α} {s : Set β} {x : β} (hx : x in closure s) (hf : Continu
ousWithinAt f s x) …
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `closure_Ioi`：closure_Ioi (a : α) [NoMaxOrder α] : closure (Ioi a) = Ici 
a
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
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
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `continuousWithinAt_const`：continuousWithinAt_const {b : β} {s : Set α} {
x : α} : ContinuousWithinAt (fun _ : α => b) s x
· 使用定理 `Continuous.continuousWithinAt`：Continuous.continuousWithinAt (h : Contin
uous f) : ContinuousWithinAt f s x
· 使用定理 `gronwallBound_continuous_ε`：gronwallBound_continuous_ε (δ K x : Real) : 
Continuous fun ε => gronwallBound δ K ε x

--- 原说明 ---
A Grönwall-like inequality: if `f : ℝ → ℝ` is continuous on `[a, b]` and satisfi
es
the inequalities `f a ≤ δ` and
`∀ x ∈ [a, b), liminf_{z→x+0} (f z - f x)/(z - x) ≤ K * (f x) + ε`, then `f x`
is bounded by `gronwallBound δ K ε (x - a)` on `[a, b]`.

See also `norm_le_gronwallBound_of_norm_deriv_right_le` for a version bounding `
‖f x‖`,
`f : ℝ → E`.
-/
theorem le_gronwallBound_of_liminf_deriv_right_le {f f' : ℝ → ℝ} {δ K ε : ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ x ∈ Ico a b, ∀ r, f' x < r → ∃ᶠ z in 𝓝[>] x, (z - x)⁻¹ * (f z - f x) < r)
    (ha : f a ≤ δ) (bound : ∀ x ∈ Ico a b, f' x ≤ K * f x + ε) :
    ∀ x ∈ Icc a b, f x ≤ gronwallBound δ K ε (x - a) := by
  have H : ∀ x ∈ Icc a b, ∀ ε' ∈ Ioi ε, f x ≤ gronwallBound δ K ε' (x - a) := by
    intro x hx ε' (hε' : ε < ε')
    apply image_le_of_liminf_slope_right_lt_deriv_boundary hf hf'
    · rwa [sub_self, gronwallBound_x0]
    · exact fun x => hasDerivAt_gronwallBound_shift δ K ε' x a
    · grind
    · exact hx
  intro x hx
  change f x ≤ (fun ε' => gronwallBound δ K ε' (x - a)) ε
  convert! continuousWithinAt_const.closure_le _ _ (H x hx)
  · simp only [closure_Ioi, self_mem_Ici]
  exact (gronwallBound_continuous_ε δ K (x - a)).continuousWithinAt

/-- A Grönwall-like inequality: if `f : ℝ → E` is continuous on `[a, b]`, has right derivative
`f' x` at every point `x ∈ [a, b)`, and satisfies the inequalities `‖f a‖ ≤ δ`,
`∀ x ∈ [a, b), ‖f' x‖ ≤ K * ‖f x‖ + ε`, then `‖f x‖` is bounded by `gronwallBound δ K ε (x - a)`
on `[a, b]`. -/
/-
**norm_le_gronwallBound_of_norm_deriv_right_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_le_gronwallBound_of_norm_deriv_right_le {f f' : Real -> E} {δ K ε : R
eal} {a b : Real} (hf : ContinuousOn f (Icc a b)) (hf' : forall x in Ico a b, Ha
sDerivWithinAt f (f' x) (Ici x) x) (ha : ‖f a‖ <= δ) (bound : forall x in Ico a 
b, ‖f' x‖ <= K * ‖f x‖ + ε) : forall x in Icc a b, ‖f x‖ <= gronwallBound δ K ε 
(x - a)
参数：hf : ContinuousOn f (Icc a b)；hf' : forall x in Ico a b, HasDerivWithinAt f (
f' x) (Ici x) x；ha : ‖f a‖ <= δ；bound : forall x in Ico a b, ‖f' x‖ <= K * ‖f x‖
 + ε。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `le_gronwallBound_of_liminf_deriv_right_le`：le_gronwallBound_of_liminf_de
riv_right_le {f f' : Real -> Real} {δ K ε : Real} {a b : Real} (hf : ContinuousO
n f (Icc a b)) (hf' : forall x …
· 使用定理 `Continuous.comp_continuousOn`：Continuous.comp_continuousOn {g : β -> γ} 
{f : α -> β} {s : Set α} (hg : Continuous g) (hf : ContinuousOn f s) : Continuou
sOn (g ∘ f) s
· 使用定理 `continuous_norm`：∀ {E : Type u_4} [inst : SeminormedAddGroup E], Continu
ous fun a => ‖a‖
· 使用定理 `HasDerivWithinAt.liminf_right_slope_norm_le`：HasDerivWithinAt.liminf_rig
ht_slope_norm_le (hf : HasDerivWithinAt f f' (Ici x) x) (hr : ‖f'‖ < r) : exists
ᶠ z in 𝓝[>] x, (z - x)⁻¹ * (‖f z‖…

--- 原说明 ---
A Grönwall-like inequality: if `f : ℝ → E` is continuous on `[a, b]`, has right 
derivative
`f' x` at every point `x ∈ [a, b)`, and satisfies the inequalities `‖f a‖ ≤ δ`,
`∀ x ∈ [a, b), ‖f' x‖ ≤ K * ‖f x‖ + ε`, then `‖f x‖` is bounded by `gronwallBoun
d δ K ε (x - a)`
on `[a, b]`.
-/
theorem norm_le_gronwallBound_of_norm_deriv_right_le {f f' : ℝ → E} {δ K ε : ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b)) (hf' : ∀ x ∈ Ico a b, HasDerivWithinAt f (f' x) (Ici x) x)
    (ha : ‖f a‖ ≤ δ) (bound : ∀ x ∈ Ico a b, ‖f' x‖ ≤ K * ‖f x‖ + ε) :
    ∀ x ∈ Icc a b, ‖f x‖ ≤ gronwallBound δ K ε (x - a) :=
  le_gronwallBound_of_liminf_deriv_right_le (continuous_norm.comp_continuousOn hf)
    (fun x hx _r hr => (hf' x hx).liminf_right_slope_norm_le hr) ha bound

/-- Let `f : [a, b] → E` be a differentiable function such that `f a = 0`
and `‖f'(x)‖ ≤ K ‖f(x)‖` for some constant `K`. Then `f = 0` on `[a, b]`. -/
/-
**eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right** 是 Mathlib 中的一个定理，位于命名空
间 ``。
形式化陈述：eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right {f f' : Real -> E} {
K a b : Real} (hf : ContinuousOn f (Icc a b)) (hf' : forall x in Ico a b, HasDer
ivWithinAt f (f' x) (Ici x) x) (ha : f a = 0) (bound : forall x in Ico a b, ‖f' 
x‖ <= K * ‖f x‖) : forall x in Set.Icc a b, f x = 0
参数：hf : ContinuousOn f (Icc a b)；hf' : forall x in Ico a b, HasDerivWithinAt f (
f' x) (Ici x) x；ha : f a = 0；bound : forall x in Ico a b, ‖f' x‖ <= K * ‖f x‖。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `norm_le_zero_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, ‖a
‖ ≤ 0 ↔ a = 0
· 使用定理 `norm_le_gronwallBound_of_norm_deriv_right_le`：norm_le_gronwallBound_of_n
orm_deriv_right_le {f f' : Real -> E} {δ K ε : Real} {a b : Real} (hf : Continuo
usOn f (Icc a b)) (hf' : forall x …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `gronwallBound_ε0_δ0`：gronwallBound_ε0_δ0 (K x : Real) : gronwallBound 0 
K 0 x = 0

--- 原说明 ---
Let `f : [a, b] → E` be a differentiable function such that `f a = 0`
and `‖f'(x)‖ ≤ K ‖f(x)‖` for some constant `K`. Then `f = 0` on `[a, b]`.
-/
theorem eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right {f f' : ℝ → E} {K a b : ℝ}
    (hf : ContinuousOn f (Icc a b)) (hf' : ∀ x ∈ Ico a b, HasDerivWithinAt f (f' x) (Ici x) x)
    (ha : f a = 0) (bound : ∀ x ∈ Ico a b, ‖f' x‖ ≤ K * ‖f x‖) :
    ∀ x ∈ Set.Icc a b, f x = 0 := by
  intro x hx
  apply norm_le_zero_iff.mp
  calc ‖f x‖
    _ ≤ gronwallBound 0 K 0 (x - a) :=
      norm_le_gronwallBound_of_norm_deriv_right_le hf hf' (by simp [ha]) (by simpa using bound) _ hx
    _ = 0 := by rw [gronwallBound_ε0_δ0]

variable {v : ℝ → E → E} {s : ℝ → Set E} {K : ℝ≥0} {f g f' g' : ℝ → E} {a b t₀ : ℝ} {εf εg δ : ℝ}

/-- If `f` and `g` are two approximate solutions of the same ODE, then the distance between them
can't grow faster than exponentially. This is a simple corollary of Grönwall's inequality, and some
people call this Grönwall's inequality too.

This version assumes all inequalities to be true in some time-dependent set `s t`,
and assumes that the solutions never leave this set. -/
/-
**dist_le_of_approx_trajectories_ODE_of_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_le_of_approx_trajectories_ODE_of_mem (hv : forall t in Ico a b, Lipsc
hitzOnWith K (v t) (s t)) (hf : ContinuousOn f (Icc a b)) (hf' : forall t in Ico
 a b, HasDerivWithinAt f (f' t) (Ici t) t) (f_bound : forall t in Ico a b, dist 
(f' t) (v t (f t)) <= εf) (hfs : forall t in Ico a b, f t in s t) (hg : Continuo
usOn g (Icc a b)) (hg' : forall t in Ico a b, HasDerivWithinAt g (g' t) (Ici t) 
t) (g_bound : forall t in Ico a b, dist (g' t) (v t (g t)) <= εg) (hgs : forall 
t in Ico a b, g t in s t) 
参数：hv : forall t in Ico a b, LipschitzOnWith K (v t) (s t)；hf : ContinuousOn f (
Icc a b)；hf' : forall t in Ico a b, HasDerivWithinAt f (f' t) (Ici t) t；f_bound 
: forall t in Ico a b, dist (f' t) (v t (f t)) <= εf；hfs : forall t in Ico a b, 
f t in s t；hg : ContinuousOn g (Icc a b)；hg' : forall t in Ico a b, HasDerivWith
inAt g (g' t) (Ici t) t；g_bound : forall t in Ico a b, dist (g' t) (v t (g t)) <
= εg；hgs : forall t in Ico a b, g t in s t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
· 使用定理 `HasDerivWithinAt.sub`：HasDerivWithinAt.sub (hf : HasDerivWithinAt f f' s
 x) (hg : HasDerivWithinAt g g' s x) : HasDerivWithinAt (f - g) (f' - g') s x
· 使用定理 `norm_le_gronwallBound_of_norm_deriv_right_le`：norm_le_gronwallBound_of_n
orm_deriv_right_le {f f' : Real -> E} {δ K ε : Real} {a b : Real} (hf : Continuo
usOn f (Icc a b)) (hf' : forall x …
· 使用定理 `ContinuousOn.fun_sub`：∀ {G : Type u_1} {X : Type u_3} [inst : Topologica
lSpace X] [inst_1 : TopologicalSpace G] [inst_2 : Sub G]   [ContinuousSub G] {f 
g : X → G}…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `dist_triangle4_right`：dist_triangle4_right (x₁ y₁ x₂ y₂ : α) : dist x₁ y
₁ <= dist x₁ x₂ + dist y₁ y₂ + dist x₂ y₂
· 使用定理 `LipschitzOnWith.dist_le_mul`：∀ {α : Type u} {β : Type v} [inst : PseudoM
etricSpace α] [inst_1 : PseudoMetricSpace β] {K : NNReal} {s : Set α}   {f : α →
 β}, LipschitzOnW…

--- 原说明 ---
If `f` and `g` are two approximate solutions of the same ODE, then the distance 
between them
can't grow faster than exponentially. This is a simple corollary of Grönwall's i
nequality, and some
people call this Grönwall's inequality too.

This version assumes all inequalities to be true in some time-dependent set `s t
`,
and assumes that the solutions never leave this set.
-/
theorem dist_le_of_approx_trajectories_ODE_of_mem
    (hv : ∀ t ∈ Ico a b, LipschitzOnWith K (v t) (s t))
    (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ t ∈ Ico a b, HasDerivWithinAt f (f' t) (Ici t) t)
    (f_bound : ∀ t ∈ Ico a b, dist (f' t) (v t (f t)) ≤ εf)
    (hfs : ∀ t ∈ Ico a b, f t ∈ s t)
    (hg : ContinuousOn g (Icc a b))
    (hg' : ∀ t ∈ Ico a b, HasDerivWithinAt g (g' t) (Ici t) t)
    (g_bound : ∀ t ∈ Ico a b, dist (g' t) (v t (g t)) ≤ εg)
    (hgs : ∀ t ∈ Ico a b, g t ∈ s t)
    (ha : dist (f a) (g a) ≤ δ) :
    ∀ t ∈ Icc a b, dist (f t) (g t) ≤ gronwallBound δ K (εf + εg) (t - a) := by
  simp only [dist_eq_norm] at ha ⊢
  have h_deriv : ∀ t ∈ Ico a b, HasDerivWithinAt (fun t => f t - g t) (f' t - g' t) (Ici t) t :=
    fun t ht => (hf' t ht).sub (hg' t ht)
  apply norm_le_gronwallBound_of_norm_deriv_right_le (hf.fun_sub hg) h_deriv ha
  intro t ht
  have := dist_triangle4_right (f' t) (g' t) (v t (f t)) (v t (g t))
  have := (hv t ht).dist_le_mul _ (hfs t ht) _ (hgs t ht)
  grind [dist_eq_norm]

/-- If `f` and `g` are two approximate solutions of the same ODE, then the distance between them
can't grow faster than exponentially. This is a simple corollary of Grönwall's inequality, and some
people call this Grönwall's inequality too.

This version assumes all inequalities to be true in the whole space. -/
/-
**dist_le_of_approx_trajectories_ODE** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_le_of_approx_trajectories_ODE (hv : forall t, LipschitzWith K (v t)) 
(hf : ContinuousOn f (Icc a b)) (hf' : forall t in Ico a b, HasDerivWithinAt f (
f' t) (Ici t) t) (f_bound : forall t in Ico a b, dist (f' t) (v t (f t)) <= εf) 
(hg : ContinuousOn g (Icc a b)) (hg' : forall t in Ico a b, HasDerivWithinAt g (
g' t) (Ici t) t) (g_bound : forall t in Ico a b, dist (g' t) (v t (g t)) <= εg) 
(ha : dist (f a) (g a) <= δ) : forall t in Icc a b, dist (f t) (g t) <= gronwall
Bound δ K (εf + εg) (t - a
参数：hv : forall t, LipschitzWith K (v t)；hf : ContinuousOn f (Icc a b)；hf' : fora
ll t in Ico a b, HasDerivWithinAt f (f' t) (Ici t) t；f_bound : forall t in Ico a
 b, dist (f' t) (v t (f t)) <= εf；hg : ContinuousOn g (Icc a b)；hg' : forall t i
n Ico a b, HasDerivWithinAt g (g' t) (Ici t) t；g_bound : forall t in Ico a b, di
st (g' t) (v t (g t)) <= εg；ha : dist (f a) (g a) <= δ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `trivial`：True
· 使用定理 `dist_le_of_approx_trajectories_ODE_of_mem`：dist_le_of_approx_trajectorie
s_ODE_of_mem (hv : forall t in Ico a b, LipschitzOnWith K (v t) (s t)) (hf : Con
tinuousOn f (Icc a b)) (hf' : f…
· 使用定理 `LipschitzWith.lipschitzOnWith`：∀ {α : Type u} {β : Type v} [inst : Pseud
oEMetricSpace α] [inst_1 : PseudoEMetricSpace β] {K : NNReal} {f : α → β}   {s :
 Set α}, LipschitzW…

--- 原说明 ---
If `f` and `g` are two approximate solutions of the same ODE, then the distance 
between them
can't grow faster than exponentially. This is a simple corollary of Grönwall's i
nequality, and some
people call this Grönwall's inequality too.

This version assumes all inequalities to be true in the whole space.
-/
theorem dist_le_of_approx_trajectories_ODE
    (hv : ∀ t, LipschitzWith K (v t))
    (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ t ∈ Ico a b, HasDerivWithinAt f (f' t) (Ici t) t)
    (f_bound : ∀ t ∈ Ico a b, dist (f' t) (v t (f t)) ≤ εf)
    (hg : ContinuousOn g (Icc a b))
    (hg' : ∀ t ∈ Ico a b, HasDerivWithinAt g (g' t) (Ici t) t)
    (g_bound : ∀ t ∈ Ico a b, dist (g' t) (v t (g t)) ≤ εg)
    (ha : dist (f a) (g a) ≤ δ) :
    ∀ t ∈ Icc a b, dist (f t) (g t) ≤ gronwallBound δ K (εf + εg) (t - a) :=
  have hfs : ∀ t ∈ Ico a b, f t ∈ @univ E := fun _ _ => trivial
  dist_le_of_approx_trajectories_ODE_of_mem (fun t _ => (hv t).lipschitzOnWith) hf hf'
    f_bound hfs hg hg' g_bound (fun _ _ => trivial) ha

/-- If `f` and `g` are two exact solutions of the same ODE, then the distance between them
can't grow faster than exponentially. This is a simple corollary of Grönwall's inequality, and some
people call this Grönwall's inequality too.

This version assumes all inequalities to be true in some time-dependent set `s t`,
and assumes that the solutions never leave this set. -/
/-
**dist_le_of_trajectories_ODE_of_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_le_of_trajectories_ODE_of_mem (hv : forall t in Ico a b, LipschitzOnW
ith K (v t) (s t)) (hf : ContinuousOn f (Icc a b)) (hf' : forall t in Ico a b, H
asDerivWithinAt f (v t (f t)) (Ici t) t) (hfs : forall t in Ico a b, f t in s t)
 (hg : ContinuousOn g (Icc a b)) (hg' : forall t in Ico a b, HasDerivWithinAt g 
(v t (g t)) (Ici t) t) (hgs : forall t in Ico a b, g t in s t) (ha : dist (f a) 
(g a) <= δ) : forall t in Icc a b, dist (f t) (g t) <= δ * exp (K * (t - a))
参数：hv : forall t in Ico a b, LipschitzOnWith K (v t) (s t)；hf : ContinuousOn f (
Icc a b)；hf' : forall t in Ico a b, HasDerivWithinAt f (v t (f t)) (Ici t) t；hfs
 : forall t in Ico a b, f t in s t；hg : ContinuousOn g (Icc a b)；hg' : forall t 
in Ico a b, HasDerivWithinAt g (v t (g t)) (Ici t) t；hgs : forall t in Ico a b, 
g t in s t；ha : dist (f a) (g a) <= δ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_self`：dist_self (x : α) : dist x x = 0
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `dist_le_of_approx_trajectories_ODE_of_mem`：dist_le_of_approx_trajectorie
s_ODE_of_mem (hv : forall t in Ico a b, LipschitzOnWith K (v t) (s t)) (hf : Con
tinuousOn f (Icc a b)) (hf' : f…
· 使用定理 `gronwallBound_ε0`：gronwallBound_ε0 (δ K x : Real) : gronwallBound δ K 0 
x = δ * exp (K * x)
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a

--- 原说明 ---
If `f` and `g` are two exact solutions of the same ODE, then the distance betwee
n them
can't grow faster than exponentially. This is a simple corollary of Grönwall's i
nequality, and some
people call this Grönwall's inequality too.

This version assumes all inequalities to be true in some time-dependent set `s t
`,
and assumes that the solutions never leave this set.
-/
theorem dist_le_of_trajectories_ODE_of_mem
    (hv : ∀ t ∈ Ico a b, LipschitzOnWith K (v t) (s t))
    (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ t ∈ Ico a b, HasDerivWithinAt f (v t (f t)) (Ici t) t)
    (hfs : ∀ t ∈ Ico a b, f t ∈ s t)
    (hg : ContinuousOn g (Icc a b)) (hg' : ∀ t ∈ Ico a b, HasDerivWithinAt g (v t (g t)) (Ici t) t)
    (hgs : ∀ t ∈ Ico a b, g t ∈ s t) (ha : dist (f a) (g a) ≤ δ) :
    ∀ t ∈ Icc a b, dist (f t) (g t) ≤ δ * exp (K * (t - a)) := by
  have f_bound : ∀ t ∈ Ico a b, dist (v t (f t)) (v t (f t)) ≤ 0 := by intros; rw [dist_self]
  have g_bound : ∀ t ∈ Ico a b, dist (v t (g t)) (v t (g t)) ≤ 0 := by intros; rw [dist_self]
  intro t ht
  have :=
    dist_le_of_approx_trajectories_ODE_of_mem hv hf hf' f_bound hfs hg hg' g_bound hgs ha t ht
  rwa [zero_add, gronwallBound_ε0] at this

/-- If `f` and `g` are two exact solutions of the same ODE, then the distance between them
can't grow faster than exponentially. This is a simple corollary of Grönwall's inequality, and some
people call this Grönwall's inequality too.

This version assumes all inequalities to be true in the whole space. -/
/-
**dist_le_of_trajectories_ODE** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_le_of_trajectories_ODE (hv : forall t, LipschitzWith K (v t)) (hf : C
ontinuousOn f (Icc a b)) (hf' : forall t in Ico a b, HasDerivWithinAt f (v t (f 
t)) (Ici t) t) (hg : ContinuousOn g (Icc a b)) (hg' : forall t in Ico a b, HasDe
rivWithinAt g (v t (g t)) (Ici t) t) (ha : dist (f a) (g a) <= δ) : forall t in 
Icc a b, dist (f t) (g t) <= δ * exp (K * (t - a))
参数：hv : forall t, LipschitzWith K (v t)；hf : ContinuousOn f (Icc a b)；hf' : fora
ll t in Ico a b, HasDerivWithinAt f (v t (f t)) (Ici t) t；hg : ContinuousOn g (I
cc a b)；hg' : forall t in Ico a b, HasDerivWithinAt g (v t (g t)) (Ici t) t；ha :
 dist (f a) (g a) <= δ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `trivial`：True
· 使用定理 `dist_le_of_trajectories_ODE_of_mem`：dist_le_of_trajectories_ODE_of_mem (
hv : forall t in Ico a b, LipschitzOnWith K (v t) (s t)) (hf : ContinuousOn f (I
cc a b)) (hf' : forall t…
· 使用定理 `LipschitzWith.lipschitzOnWith`：∀ {α : Type u} {β : Type v} [inst : Pseud
oEMetricSpace α] [inst_1 : PseudoEMetricSpace β] {K : NNReal} {f : α → β}   {s :
 Set α}, LipschitzW…

--- 原说明 ---
If `f` and `g` are two exact solutions of the same ODE, then the distance betwee
n them
can't grow faster than exponentially. This is a simple corollary of Grönwall's i
nequality, and some
people call this Grönwall's inequality too.

This version assumes all inequalities to be true in the whole space.
-/
theorem dist_le_of_trajectories_ODE
    (hv : ∀ t, LipschitzWith K (v t))
    (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ t ∈ Ico a b, HasDerivWithinAt f (v t (f t)) (Ici t) t)
    (hg : ContinuousOn g (Icc a b))
    (hg' : ∀ t ∈ Ico a b, HasDerivWithinAt g (v t (g t)) (Ici t) t)
    (ha : dist (f a) (g a) ≤ δ) :
    ∀ t ∈ Icc a b, dist (f t) (g t) ≤ δ * exp (K * (t - a)) :=
  have hfs : ∀ t ∈ Ico a b, f t ∈ @univ E := fun _ _ => trivial
  dist_le_of_trajectories_ODE_of_mem (fun t _ => (hv t).lipschitzOnWith) hf hf' hfs hg
    hg' (fun _ _ => trivial) ha
