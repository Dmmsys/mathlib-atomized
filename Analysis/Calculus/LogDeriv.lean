/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Calculus.Deriv.ZPow
public import Mathlib.Analysis.Calculus.MeanValue

import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.Deriv.Slope
/-!
# Logarithmic Derivatives

We define the logarithmic derivative of a function `f` as `deriv f / f`. We then prove some basic
facts about this, including how it changes under multiplication and composition.

-/

@[expose] public section

noncomputable section

open Filter Function Set

open scoped Topology

variable {𝕜 𝕜' : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜']
  [NormedAlgebra 𝕜 𝕜']

/-- The logarithmic derivative of a function defined as `deriv f /f`. Note that it will be zero
at `x` if `f` is not DifferentiableAt `x`. -/
/-
**logDeriv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：logDeriv (f : 𝕜 -> 𝕜')
参数：f : 𝕜 -> 𝕜'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The logarithmic derivative of a function defined as `deriv f /f`. Note that it w
ill be zero
at `x` if `f` is not DifferentiableAt `x`.
-/
def logDeriv (f : 𝕜 → 𝕜') :=
  deriv f / f
/-
**logDeriv_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：logDeriv_apply (f : 𝕜 -> 𝕜') (x : 𝕜) : logDeriv f x = deriv f x / f x
参数：f : 𝕜 -> 𝕜'；x : 𝕜。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem logDeriv_apply (f : 𝕜 → 𝕜') (x : 𝕜) : logDeriv f x = deriv f x / f x := rfl
/-
**logDeriv_eq_zero_of_not_differentiableAt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：logDeriv_eq_zero_of_not_differentiableAt (f : 𝕜 -> 𝕜') (x : 𝕜) (h : ¬Diffe
rentiableAt 𝕜 f x) : logDeriv f x = 0
参数：f : 𝕜 -> 𝕜'；x : 𝕜；h : ¬DifferentiableAt 𝕜 f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `deriv_zero_of_not_differentiableAt`：deriv_zero_of_not_differentiableAt (
h : ¬DifferentiableAt 𝕜 f x) : deriv f x = 0
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma logDeriv_eq_zero_of_not_differentiableAt (f : 𝕜 → 𝕜') (x : 𝕜) (h : ¬DifferentiableAt 𝕜 f x) :
    logDeriv f x = 0 := by
  simp only [logDeriv_apply, deriv_zero_of_not_differentiableAt h, zero_div]

/-- If two functions agree in a neighborhood of `x`, then so do their logarithmic derivatives. -/
/-
**logDeriv_congr_nhds** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：logDeriv_congr_nhds {f g : 𝕜 -> 𝕜'} {x : 𝕜} (h : f =ᶠ[𝓝 x] g) : logDeriv f
 =ᶠ[𝓝 x] logDeriv g
参数：h : f =ᶠ[𝓝 x] g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.div`：∀ {α : Type u} {β : Type v} [inst : Div β] {f f
' g g' : α → β} {l : Filter α},   f =ᶠ[l] g → f' =ᶠ[l] g' → f / f' =ᶠ[l] g / g'
· 使用定理 `Filter.EventuallyEq.deriv`：∀ {𝕜 : Type u} [inst : NontriviallyNormedFiel
d 𝕜] {F : Type v} [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] {
f f₁ : 𝕜 → F} {…

--- 原说明 ---
If two functions agree in a neighborhood of `x`, then so do their logarithmic de
rivatives.
-/
lemma logDeriv_congr_nhds {f g : 𝕜 → 𝕜'} {x : 𝕜} (h : f =ᶠ[𝓝 x] g) :
    logDeriv f =ᶠ[𝓝 x] logDeriv g := h.deriv.div h

/--
If two functions agree in a punctured neighborhood of `x`, then so do their logarithmic derivatives.
-/
/-
**logDeriv_congr_nhdsNE** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：logDeriv_congr_nhdsNE {f g : 𝕜 -> 𝕜'} {x : 𝕜} (h : f =ᶠ[𝓝[!=] x] g) : logD
eriv f =ᶠ[𝓝[!=] x] logDeriv g
参数：h : f =ᶠ[𝓝[!=] x] g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.div`：∀ {α : Type u} {β : Type v} [inst : Div β] {f f
' g g' : α → β} {l : Filter α},   f =ᶠ[l] g → f' =ᶠ[l] g' → f / f' =ᶠ[l] g / g'
· 使用定理 `Filter.EventuallyEq.nhdsNE_deriv`：Filter.EventuallyEq.nhdsNE_deriv (h : 
f₁ =ᶠ[𝓝[!=] x] f) : deriv f₁ =ᶠ[𝓝[!=] x] deriv f

--- 原说明 ---
If two functions agree in a punctured neighborhood of `x`, then so do their loga
rithmic derivatives.
-/
lemma logDeriv_congr_nhdsNE {f g : 𝕜 → 𝕜'} {x : 𝕜} (h : f =ᶠ[𝓝[≠] x] g) :
    logDeriv f =ᶠ[𝓝[≠] x] logDeriv g := h.nhdsNE_deriv.div h

/--
If two functions agree on a codiscrete subset of an open set `U`, then so do their logarithmic
derivatives.
-/
/-
**logDeriv_congr_codiscreteWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：logDeriv_congr_codiscreteWithin {f g : 𝕜 -> 𝕜'} {U : Set 𝕜} (hU : IsOpen U
) (h : f =ᶠ[codiscreteWithin U] g) : logDeriv f =ᶠ[codiscreteWithin U] logDeriv 
g
参数：hU : IsOpen U；h : f =ᶠ[codiscreteWithin U] g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mem_codiscreteWithin_iff_forall_mem_nhdsNE`：mem_codiscreteWithin_iff_for
all_mem_nhdsNE {S T : Set X} : S in codiscreteWithin T ↔ forall x in T, S union 
Tᶜ in 𝓝[!=] x
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用引理 `logDeriv_congr_nhdsNE`：logDeriv_congr_nhdsNE {f g : 𝕜 -> 𝕜'} {x : 𝕜} (h 
: f =ᶠ[𝓝[!=] x] g) : logDeriv f =ᶠ[𝓝[!=] x] logDeriv g
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `nhdsWithin_le_nhds`：nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a <= 𝓝
 a
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `not_not_intro`：∀ {p : Prop}, p → ¬¬p
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t

--- 原说明 ---
If two functions agree on a codiscrete subset of an open set `U`, then so do the
ir logarithmic
derivatives.
-/
theorem logDeriv_congr_codiscreteWithin {f g : 𝕜 → 𝕜'} {U : Set 𝕜} (hU : IsOpen U)
    (h : f =ᶠ[codiscreteWithin U] g) :
    logDeriv f =ᶠ[codiscreteWithin U] logDeriv g := by
  refine mem_codiscreteWithin_iff_forall_mem_nhdsNE.2 fun x hx ↦ ?_
  refine mem_of_superset (logDeriv_congr_nhdsNE ?_) Set.subset_union_left
  filter_upwards [mem_codiscreteWithin_iff_forall_mem_nhdsNE.1 h x hx,
    nhdsWithin_le_nhds (hU.mem_nhds hx)] with z hz hzU
  exact hz.resolve_right (not_not_intro hzU)

/--
If two functions agree on a codiscrete subset of `𝕜`, then so do their logarithmic derivatives.
-/
/-
**logDeriv_congr_codiscrete** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：logDeriv_congr_codiscrete {f g : 𝕜 -> 𝕜'} (h : f =ᶠ[codiscrete 𝕜] g) : log
Deriv f =ᶠ[codiscrete 𝕜] logDeriv g
参数：h : f =ᶠ[codiscrete 𝕜] g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `logDeriv_congr_codiscreteWithin`：logDeriv_congr_codiscreteWithin {f g : 
𝕜 -> 𝕜'} {U : Set 𝕜} (hU : IsOpen U) (h : f =ᶠ[codiscreteWithin U] g) : logDeriv
 f =ᶠ[codiscreteWithi…
· 使用定理 `isOpen_univ`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen Set.univ

--- 原说明 ---
If two functions agree on a codiscrete subset of `𝕜`, then so do their logarithm
ic derivatives.
-/
theorem logDeriv_congr_codiscrete {f g : 𝕜 → 𝕜'} (h : f =ᶠ[codiscrete 𝕜] g) :
    logDeriv f =ᶠ[codiscrete 𝕜] logDeriv g :=
  logDeriv_congr_codiscreteWithin isOpen_univ h

@[simp]
/-
**logDeriv_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：logDeriv_id (x : 𝕜) : logDeriv id x = 1 / x
参数：x : 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `deriv_id'`：deriv_id' : deriv (@id 𝕜) = fun _ => 1
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem logDeriv_id (x : 𝕜) : logDeriv id x = 1 / x := by
  simp [logDeriv_apply]
/-
**logDeriv_id'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] (x : 𝕜), logDeriv (fun
 x => x) x = 1 / x
参数：x : 𝕜；fun x => x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `logDeriv_id`：logDeriv_id (x : 𝕜) : logDeriv id x = 1 / x
-/
@[simp] theorem logDeriv_id' (x : 𝕜) : logDeriv (·) x = 1 / x := logDeriv_id x

@[simp]
/-
**logDeriv_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：logDeriv_const (a : 𝕜') : logDeriv (fun _ : 𝕜 => a) = 0
参数：a : 𝕜'。
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
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `deriv_const'`：deriv_const' : (deriv fun _ : 𝕜 => c) = fun _ => 0
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem logDeriv_const (a : 𝕜') : logDeriv (fun _ : 𝕜 ↦ a) = 0 := by
  ext
  simp [logDeriv_apply]
/-
**logDeriv_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：logDeriv_mul {f g : 𝕜 -> 𝕜'} (x : 𝕜) (hf : f x != 0) (hg : g x != 0) (hdf 
: DifferentiableAt 𝕜 f x) (hdg : DifferentiableAt 𝕜 g x) : logDeriv (fun z => f 
z * g z) x = logDeriv f x + logDeriv g x
参数：x : 𝕜；hf : f x != 0；hg : g x != 0；hdf : DifferentiableAt 𝕜 f x；hdg : Differen
tiableAt 𝕜 g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `deriv_fun_mul`：deriv_fun_mul (hc : DifferentiableAt 𝕜 c x) (hd : Differe
ntiableAt 𝕜 d x) : deriv (fun y => c y * d y) x = deriv c x * d x + c x * deriv 
d x
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
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval`：div_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al / l₂.eval = l.eval) : x₁ /…
· 使用定理 `Mathlib.Tactic.FieldSimp.subst_add`：subst_add {M : Type*} [Semiring M] {
x₁ x₂ X₁ X₂ Y y a : M} (h₁ : x₁ = a * X₁) (h₂ : x₂ = a * X₂) (H_atom : X₁ + X₂ =
 Y) (hy : a * Y = y) : x…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval`：mul_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al * l₂.eval = l.eval) : x₁ *…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval₃`：mul_eq_eval₃ [CommGroupWithZer
o M] {a₁ : Int × M} (a₂ : Int × M) {l₁ l₂ l : NF M} (h : (a₁ ::ᵣ l₁).eval * l₂.e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_mul_eval_cons`：eval_mul_eval_cons [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : L.eval * ((n, e) ::ᵣ l).eval = …
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_div_of_eq_one_of_subst`：eq_div_of_eq_one_of_
subst {M : Type*} [DivInvOneMonoid M] {l l_n n : M} (h : l = l_n / 1) (hn : l_n 
= n) : l = n
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.cons_eq_div_of_eq_div`：cons_eq_div_of_eq_div
 [CommGroupWithZero M] (n : Int) (e : M) {t t_n t_d : NF M} (h : t.eval = t_n.ev
al / t_d.eval) : ((n, e) ::ᵣ t).eval = …
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons`：∀ {M : Type u_1} [inst : CommGrou
pWithZero M] (p : ℤ × M) (l : Mathlib.Tactic.FieldSimp.NF M),   (p ::ᵣ l).eval =
 l.eval * Mathlib.Tactic.Fi…
· 使用定理 `Mathlib.Tactic.FieldSimp.zpow'_one`：∀ {α : Type u_1} [inst : GroupWithZe
ro α] (a : α), Mathlib.Tactic.FieldSimp.zpow' a 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval₁`：mul_eq_eval₁ [CommGroupWithZer
o M] (a₁ : Int × M) {a₂ : Int × M} {l₁ l₂ l : NF M} (h : l₁.eval * (a₂ ::ᵣ l₂).e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval₁`：div_eq_eval₁ [CommGroupWithZer
o M] (a₁ : Int × M) {a₂ : Int × M} {l₁ l₂ l : NF M} (h : l₁.eval / (a₂ ::ᵣ l₂).e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.one_div_eq_eval`：one_div_eq_eval [CommGroupW
ithZero M] (l : NF M) : 1 / l.eval = (l⁻¹).eval
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons_mul_eval`：eval_cons_mul_eval [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : ((n, e) ::ᵣ L).eval * l.eval = …
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval₃`：div_eq_eval₃ [CommGroupWithZer
o M] {a₁ : Int × M} (a₂ : Int × M) {l₁ l₂ l : NF M} (h : (a₁ ::ᵣ l₁).eval / l₂.e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons_mul_eval_cons_neg`：eval_cons_mul_e
val_cons_neg [CommGroupWithZero M] (n : Int) {e : M} (he : e != 0) {L l l' : NF 
M} (h : L.eval * l.eval = l'.eval) : ((n, e) …
（共 34 条，此处仅展示前 30 条）
-/
theorem logDeriv_mul {f g : 𝕜 → 𝕜'} (x : 𝕜) (hf : f x ≠ 0) (hg : g x ≠ 0)
    (hdf : DifferentiableAt 𝕜 f x) (hdg : DifferentiableAt 𝕜 g x) :
      logDeriv (fun z => f z * g z) x = logDeriv f x + logDeriv g x := by
  simp [field, logDeriv_apply, *]
/-
**logDeriv_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：logDeriv_div {f g : 𝕜 -> 𝕜'} (x : 𝕜) (hf : f x != 0) (hg : g x != 0) (hdf 
: DifferentiableAt 𝕜 f x) (hdg : DifferentiableAt 𝕜 g x) : logDeriv (fun z => f 
z / g z) x = logDeriv f x - logDeriv g x
参数：x : 𝕜；hf : f x != 0；hg : g x != 0；hdf : DifferentiableAt 𝕜 f x；hdg : Differen
tiableAt 𝕜 g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `deriv_fun_div`：deriv_fun_div (hc : DifferentiableAt 𝕜 c x) (hd : Differe
ntiableAt 𝕜 d x) (hx : d x != 0) : deriv (fun x => c x / d x) x = (deriv c x * d
 x …
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
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
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval`：div_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al / l₂.eval = l.eval) : x₁ /…
· 使用定理 `Mathlib.Tactic.FieldSimp.subst_sub`：subst_sub {M : Type*} [Ring M] {x₁ x
₂ X₁ X₂ Y y a : M} (h₁ : x₁ = a * X₁) (h₂ : x₂ = a * X₂) (H_atom : X₁ - X₂ = Y) 
(hy : a * Y = y) : x₁ - …
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval`：mul_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al * l₂.eval = l.eval) : x₁ *…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval₃`：mul_eq_eval₃ [CommGroupWithZer
o M] {a₁ : Int × M} (a₂ : Int × M) {l₁ l₂ l : NF M} (h : (a₁ ::ᵣ l₁).eval * l₂.e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_mul_eval_cons`：eval_mul_eval_cons [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : L.eval * ((n, e) ::ᵣ l).eval = …
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_div_of_eq_one_of_subst`：eq_div_of_eq_one_of_
subst {M : Type*} [DivInvOneMonoid M] {l l_n n : M} (h : l = l_n / 1) (hn : l_n 
= n) : l = n
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.cons_eq_div_of_eq_div`：cons_eq_div_of_eq_div
 [CommGroupWithZero M] (n : Int) (e : M) {t t_n t_d : NF M} (h : t.eval = t_n.ev
al / t_d.eval) : ((n, e) ::ᵣ t).eval = …
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons`：∀ {M : Type u_1} [inst : CommGrou
pWithZero M] (p : ℤ × M) (l : Mathlib.Tactic.FieldSimp.NF M),   (p ::ᵣ l).eval =
 l.eval * Mathlib.Tactic.Fi…
· 使用定理 `Mathlib.Tactic.FieldSimp.zpow'_one`：∀ {α : Type u_1} [inst : GroupWithZe
ro α] (a : α), Mathlib.Tactic.FieldSimp.zpow' a 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.pow_eq_eval`：pow_eq_eval [CommGroupWithZero 
M] {l : NF M} {r : Nat} (hr : r != 0) {x : M} (hx : x = l.eval) : x ^ r = (l ^ r
).eval
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval₁`：div_eq_eval₁ [CommGroupWithZer
o M] (a₁ : Int × M) {a₂ : Int × M} {l₁ l₂ l : NF M} (h : l₁.eval / (a₂ ::ᵣ l₂).e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
（共 39 条，此处仅展示前 30 条）
-/
theorem logDeriv_div {f g : 𝕜 → 𝕜'} (x : 𝕜) (hf : f x ≠ 0) (hg : g x ≠ 0)
    (hdf : DifferentiableAt 𝕜 f x) (hdg : DifferentiableAt 𝕜 g x) :
    logDeriv (fun z => f z / g z) x = logDeriv f x - logDeriv g x := by
  simp [field, logDeriv_apply, *]
/-
**logDeriv_mul_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：logDeriv_mul_const {f : 𝕜 -> 𝕜'} (x : 𝕜) (a : 𝕜') (ha : a != 0) : logDeriv
 (fun z => f z * a) x = logDeriv f x
参数：x : 𝕜；a : 𝕜'；ha : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `deriv_mul_const_field`：deriv_mul_const_field (v : 𝕜') : deriv (fun y => 
u y * v) x = deriv u x * v
· 使用引理 `mul_div_mul_right`：mul_div_mul_right (a b : G₀) (hc : c != 0) : a * c / 
(b * c) = a / b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem logDeriv_mul_const {f : 𝕜 → 𝕜'} (x : 𝕜) (a : 𝕜') (ha : a ≠ 0) :
    logDeriv (fun z => f z * a) x = logDeriv f x := by
  simp only [logDeriv_apply, deriv_mul_const_field, mul_div_mul_right _ _ ha]
/-
**logDeriv_const_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：logDeriv_const_mul {f : 𝕜 -> 𝕜'} (x : 𝕜) (a : 𝕜') (ha : a != 0) : logDeriv
 (fun z => a * f z) x = logDeriv f x
参数：x : 𝕜；a : 𝕜'；ha : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `deriv_const_mul_field`：deriv_const_mul_field (u : 𝕜') : deriv (fun y => 
u * v y) x = u * deriv v x
· 使用引理 `mul_div_mul_left`：mul_div_mul_left (a b : G₀) (hc : c != 0) : c * a / (c
 * b) = a / b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem logDeriv_const_mul {f : 𝕜 → 𝕜'} (x : 𝕜) (a : 𝕜') (ha : a ≠ 0) :
    logDeriv (fun z => a * f z) x = logDeriv f x := by
  simp only [logDeriv_apply, deriv_const_mul_field, mul_div_mul_left _ _ ha]

/-- The logarithmic derivative of a finite product is the sum of the logarithmic derivatives. -/
/-
**logDeriv_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：logDeriv_prod {ι : Type*} {s : Finset ι} {f : ι -> 𝕜 -> 𝕜'} {x : 𝕜} (hf : 
forall i in s, f i x != 0) (hd : forall i in s, DifferentiableAt 𝕜 (f i) x) : lo
gDeriv (∏ i in s, f i ·) x = ∑ i in s, logDeriv (f i) x
参数：hf : forall i in s, f i x != 0；hd : forall i in s, DifferentiableAt 𝕜 (f i) x
。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.cons_induction`：∀ {α : Type u_3} {motive : Finset α → Prop},   mo
tive ∅ → (∀ (a : α) (s : Finset α) (h : a ∉ s), motive s → motive (Finset.cons a
 s h)) → ∀ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `logDeriv_const`：logDeriv_const (a : 𝕜') : logDeriv (fun _ : 𝕜 => a) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.prod_cons`：prod_cons (h : a ∉ s) : ∏ x in cons a s h, f x = f a *
 ∏ x in s, f x
· 使用定理 `Finset.sum_cons`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι} 
[inst : AddCommMonoid M] {f : ι → M} (h : a ∉ s),   ∑ x ∈ Finset.cons a s h, f x
 = f …
· 使用定理 `logDeriv_mul`：logDeriv_mul {f g : 𝕜 -> 𝕜'} (x : 𝕜) (hf : f x != 0) (hg :
 g x != 0) (hdf : DifferentiableAt 𝕜 f x) (hdg : DifferentiableAt 𝕜 g x) : logDe
ri…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Finset.forall_mem_cons`：forall_mem_cons (h : a ∉ s) (p : α -> Prop) : (f
orall x, x in cons a s h -> p x) ↔ p a ∧ forall x, x in s -> p x
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `DifferentiableAt.fun_finsetProd`：DifferentiableAt.fun_finsetProd (hd : f
orall i in u, DifferentiableAt 𝕜 (f i) x) : DifferentiableAt 𝕜 (∏ i in u, f i ·)
 x

--- 原说明 ---
The logarithmic derivative of a finite product is the sum of the logarithmic der
ivatives.
-/
theorem logDeriv_prod {ι : Type*} {s : Finset ι} {f : ι → 𝕜 → 𝕜'} {x : 𝕜} (hf : ∀ i ∈ s, f i x ≠ 0)
    (hd : ∀ i ∈ s, DifferentiableAt 𝕜 (f i) x) :
    logDeriv (∏ i ∈ s, f i ·) x = ∑ i ∈ s, logDeriv (f i) x := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    rw [Finset.forall_mem_cons] at hf hd
    simp_rw [Finset.prod_cons, Finset.sum_cons]
    rw [logDeriv_mul, ih hf.2 hd.2]
    · exact hf.1
    · simpa [Finset.prod_eq_zero_iff] using hf.2
    · exact hd.1
    · exact .fun_finsetProd hd.2
/-
**logDeriv_fun_zpow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：logDeriv_fun_zpow {f : 𝕜 -> 𝕜'} {x : 𝕜} (hdf : DifferentiableAt 𝕜 f x) (n 
: Int) : logDeriv (f · ^ n) x = n * logDeriv f x
参数：hdf : DifferentiableAt 𝕜 f x；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `zpow_ofNat`：zpow_ofNat (a : G) (n : Nat) : a ^ (ofNat(n) : Int) = a ^ Of
Nat.ofNat n
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `logDeriv_const`：logDeriv_const (a : 𝕜') : logDeriv (fun _ : 𝕜 => a) = 0
· 使用定理 `Int.cast_zero`：cast_zero : ((0 : Int) : R) = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zero_zpow`：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀] (n : ℤ), n ≠ 0 → 
0 ^ n = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `logDeriv_apply`：logDeriv_apply (f : 𝕜 -> 𝕜') (x : 𝕜) : logDeriv f x = de
riv f x / f x
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)
· 使用定理 `deriv_comp`：deriv_comp (hh₂ : DifferentiableAt 𝕜' h₂ (h x)) (hh : Differ
entiableAt 𝕜 h x) : deriv (h₂ ∘ h) x = deriv h₂ (h x) * deriv h x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `differentiableAt_zpow`：differentiableAt_zpow : DifferentiableAt 𝕜 (fun x
 => x ^ m) x ↔ x != 0 ∨ 0 <= m
· 使用定理 `deriv_zpow`：deriv_zpow (m : Int) (x : 𝕜) : deriv (fun x => x ^ m) x = m 
* x ^ (m - 1)
· 使用引理 `zpow_sub_one₀`：zpow_sub_one₀ (ha : a != 0) (n : Int) : a ^ (n - 1) = a ^
 n * a⁻¹
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_eq_cancel_eq`：eq_eq_cancel_eq {M : Type*} [M
onoidWithZero M] [IsLeftCancelMulZero M] {e₁ e₂ f₁ f₂ L : M} (H₁ : e₁ = L * f₁) 
(H₂ : e₂ = L * f₂) (HL : L != …
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `instIsCancelMulZero`：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀], IsCanc
elMulZero G₀
（共 57 条，此处仅展示前 30 条）
-/
lemma logDeriv_fun_zpow {f : 𝕜 → 𝕜'} {x : 𝕜} (hdf : DifferentiableAt 𝕜 f x) (n : ℤ) :
    logDeriv (f · ^ n) x = n * logDeriv f x := by
  rcases eq_or_ne n 0 with rfl | hn; · simp
  rcases eq_or_ne (f x) 0 with hf | hf
  · simp [logDeriv_apply, zero_zpow, *]
  · rw [logDeriv_apply, ← comp_def (· ^ n), deriv_comp _ (differentiableAt_zpow.2 <| .inl hf) hdf,
      deriv_zpow, logDeriv_apply]
    simp [field, zpow_sub_one₀ hf]
/-
**logDeriv_fun_pow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：logDeriv_fun_pow {f : 𝕜 -> 𝕜'} {x : 𝕜} (hdf : DifferentiableAt 𝕜 f x) (n :
 Nat) : logDeriv (f · ^ n) x = n * logDeriv f x
参数：hdf : DifferentiableAt 𝕜 f x；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用引理 `logDeriv_fun_zpow`：logDeriv_fun_zpow {f : 𝕜 -> 𝕜'} {x : 𝕜} (hdf : Differ
entiableAt 𝕜 f x) (n : Int) : logDeriv (f · ^ n) x = n * logDeriv f x
-/
lemma logDeriv_fun_pow {f : 𝕜 → 𝕜'} {x : 𝕜} (hdf : DifferentiableAt 𝕜 f x) (n : ℕ) :
    logDeriv (f · ^ n) x = n * logDeriv f x :=
  mod_cast logDeriv_fun_zpow hdf n

@[simp]
/-
**logDeriv_zpow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：logDeriv_zpow (x : 𝕜) (n : Int) : logDeriv (· ^ n) x = n / x
参数：x : 𝕜；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `logDeriv_fun_zpow`：logDeriv_fun_zpow {f : 𝕜 -> 𝕜'} {x : 𝕜} (hdf : Differ
entiableAt 𝕜 f x) (n : Int) : logDeriv (f · ^ n) x = n * logDeriv f x
· 使用定理 `differentiableAt_id`：differentiableAt_id : DifferentiableAt 𝕜 id x
· 使用定理 `logDeriv_id'`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] (x : 𝕜
), logDeriv (fun x => x) x = 1 / x
· 使用定理 `mul_one_div`：mul_one_div (x y : G) : x * (1 / y) = x / y
-/
lemma logDeriv_zpow (x : 𝕜) (n : ℤ) : logDeriv (· ^ n) x = n / x := by
  rw [logDeriv_fun_zpow (by fun_prop), logDeriv_id', mul_one_div]

@[simp]
/-
**logDeriv_pow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：logDeriv_pow (x : 𝕜) (n : Nat) : logDeriv (· ^ n) x = n / x
参数：x : 𝕜；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用引理 `logDeriv_zpow`：logDeriv_zpow (x : 𝕜) (n : Int) : logDeriv (· ^ n) x = n 
/ x
-/
lemma logDeriv_pow (x : 𝕜) (n : ℕ) : logDeriv (· ^ n) x = n / x :=
  mod_cast logDeriv_zpow x n
/-
**logDeriv_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] (x : 𝕜), logDeriv (fun
 x => x⁻¹) x = -1 / x
参数：x : 𝕜；fun x => x⁻¹。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用引理 `zpow_ofNat`：zpow_ofNat (a : G) (n : Nat) : a ^ (ofNat(n) : Int) = a ^ Of
Nat.ofNat n
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用引理 `logDeriv_zpow`：logDeriv_zpow (x : 𝕜) (n : Int) : logDeriv (· ^ n) x = n 
/ x
-/
@[simp] lemma logDeriv_inv (x : 𝕜) : logDeriv (·⁻¹) x = -1 / x := by
  simpa using logDeriv_zpow x (-1)
/-
**logDeriv_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：logDeriv_comp {f : 𝕜' -> 𝕜'} {g : 𝕜 -> 𝕜'} {x : 𝕜} (hf : DifferentiableAt 
𝕜' f (g x)) (hg : DifferentiableAt 𝕜 g x) : logDeriv (f ∘ g) x = logDeriv f (g x
) * deriv g x
参数：hf : DifferentiableAt 𝕜' f (g x)；hg : DifferentiableAt 𝕜 g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `deriv_comp`：deriv_comp (hh₂ : DifferentiableAt 𝕜' h₂ (h x)) (hh : Differ
entiableAt 𝕜 h x) : deriv (h₂ ∘ h) x = deriv h₂ (h x) * deriv h x
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.div_congr`：∀ {R : Type u_2} [inst : Semifield
 R] {a a' b b' c : R}, a = a' → b = b' → a' / b' = c → a / b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
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
· 使用定理 `Mathlib.Tactic.Ring.Common.div_pf`：∀ {R : Type u_2} [inst : Semifield R]
 {a b c d : R}, b⁻¹ = c → a * c = d → a / b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.inv_single`：∀ {R : Type u_2} [inst : Semifiel
d R] {a b : R}, a⁻¹ = b → (a + 0)⁻¹ = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.inv_mul`：∀ {R : Type u_2} [inst : Semifield R
] {a₁ : R} {a₂ : ℕ} {a₃ b₁ b₃ c : R},   a₁⁻¹ = b₁ → a₃⁻¹ = b₃ → b₃ * (b₁ ^ a₂ * 
Nat.rawCast 1) = c → (a₁…
· 使用定理 `Mathlib.Meta.NormNum.isNat_inv_one`：∀ {α : Type u_1} [inst : DivisionSem
iring α] {a : α}, Mathlib.Meta.NormNum.IsNat a 1 → Mathlib.Meta.NormNum.IsNat a⁻
¹ 1
-/
theorem logDeriv_comp {f : 𝕜' → 𝕜'} {g : 𝕜 → 𝕜'} {x : 𝕜} (hf : DifferentiableAt 𝕜' f (g x))
    (hg : DifferentiableAt 𝕜 g x) : logDeriv (f ∘ g) x = logDeriv f (g x) * deriv g x := by
  simp only [logDeriv, Pi.div_apply, deriv_comp _ hf hg, comp_apply]
  ring
/-
**logDeriv_eqOn_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：logDeriv_eqOn_iff [IsRCLikeNormedField 𝕜] {f g : 𝕜 -> 𝕜'} {s : Set 𝕜} (hf 
: DifferentiableOn 𝕜 f s) (hg : DifferentiableOn 𝕜 g s) (hs2 : IsOpen s) (hsc : 
IsPreconnected s) (hgn : forall x in s, g x != 0) (hfn : forall x in s, f x != 0
) : EqOn (logDeriv f) (logDeriv g) s ↔ exists z : 𝕜', z != 0 ∧ EqOn f (z • g) s
参数：hf : DifferentiableOn 𝕜 f s；hg : DifferentiableOn 𝕜 g s；hs2 : IsOpen s；hsc : 
IsPreconnected s；hgn : forall x in s, g x != 0；hfn : forall x in s, f x != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `true_iff`：∀ (p : Prop), (True ↔ p) = p
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `deriv_mul`：deriv_mul (hc : DifferentiableAt 𝕜 c x) (hd : DifferentiableA
t 𝕜 d x) : deriv (c * d) x = deriv c x * d x + c x * deriv d x
· 使用定理 `DifferentiableOn.differentiableAt`：DifferentiableOn.differentiableAt (h 
: DifferentiableOn 𝕜 f s) (hs : s in 𝓝 x) : DifferentiableAt 𝕜 f x
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `DifferentiableAt.inv`：DifferentiableAt.inv (hf : DifferentiableAt 𝕜 h z)
 (hz : h z != 0) : DifferentiableAt 𝕜 (h⁻¹) z
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `deriv_comp`：deriv_comp (hh₂ : DifferentiableAt 𝕜' h₂ (h x)) (hh : Differ
entiableAt 𝕜 h x) : deriv (h₂ ∘ h) x = deriv h₂ (h x) * deriv h x
· 使用定理 `differentiableAt_inv`：differentiableAt_inv {x : R} (hx : x != 0) : Diffe
rentiableAt 𝕜 Inv.inv x
· 使用定理 `deriv_inv`：deriv_inv : deriv (fun x => x⁻¹) x = -(x ^ 2)⁻¹
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.inv_congr`：∀ {R : Type u_2} [inst : Semifield
 R] {a a' b : R}, a = a' → a'⁻¹ = b → a⁻¹ = b
· 使用定理 `Mathlib.Tactic.Ring.Common.inv_single`：∀ {R : Type u_2} [inst : Semifiel
d R] {a b : R}, a⁻¹ = b → (a + 0)⁻¹ = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.inv_mul`：∀ {R : Type u_2} [inst : Semifield R
] {a₁ : R} {a₂ : ℕ} {a₃ b₁ b₃ c : R},   a₁⁻¹ = b₁ → a₃⁻¹ = b₃ → b₃ * (b₁ ^ a₂ * 
Nat.rawCast 1) = c → (a₁…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_inv_one`：∀ {α : Type u_1} [inst : DivisionSem
iring α] {a : α}, Mathlib.Meta.NormNum.IsNat a 1 → Mathlib.Meta.NormNum.IsNat a⁻
¹ 1
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
（共 74 条，此处仅展示前 30 条）
-/
lemma logDeriv_eqOn_iff [IsRCLikeNormedField 𝕜] {f g : 𝕜 → 𝕜'} {s : Set 𝕜}
    (hf : DifferentiableOn 𝕜 f s) (hg : DifferentiableOn 𝕜 g s)
    (hs2 : IsOpen s) (hsc : IsPreconnected s) (hgn : ∀ x ∈ s, g x ≠ 0) (hfn : ∀ x ∈ s, f x ≠ 0) :
    EqOn (logDeriv f) (logDeriv g) s ↔ ∃ z : 𝕜', z ≠ 0 ∧ EqOn f (z • g) s := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨t, ht⟩
  · simpa using ⟨1, one_ne_zero⟩
  · constructor
    · refine fun h ↦ ⟨f t * (g t)⁻¹, by grind, fun y hy ↦ ?_⟩
      have hderiv : s.EqOn (deriv (f * g⁻¹)) (deriv f * g⁻¹ - f * deriv g / g ^ 2) := by
        intro z hz
        rw [deriv_mul (hf.differentiableAt (hs2.mem_nhds hz)) ((hg.differentiableAt
          (hs2.mem_nhds hz)).inv (hgn z hz))]
        simp only [Pi.inv_apply, show g⁻¹ = (fun x => x⁻¹) ∘ g by rfl, deriv_inv, neg_mul,
          deriv_comp z (differentiableAt_inv (hgn z hz)) (hg.differentiableAt (hs2.mem_nhds hz)),
          mul_neg, Pi.sub_apply, Pi.mul_apply, comp_apply, Pi.div_apply, Pi.pow_apply]
        ring
      have hfg : EqOn (deriv (f * g⁻¹)) 0 s := hderiv.trans fun z hz ↦ by
        simp only [Pi.sub_apply, Pi.mul_apply, Pi.inv_apply, Pi.div_apply, Pi.pow_apply,
          Pi.zero_apply]
        grind [logDeriv_apply, Pi.div_apply]
      let := IsRCLikeNormedField.rclike 𝕜
      obtain ⟨a, ha⟩ := hs2.exists_is_const_of_deriv_eq_zero hsc (hf.mul (hg.inv hgn)) hfg
      grind [Pi.mul_apply, Pi.inv_apply, Pi.smul_apply, smul_eq_mul]
    · rintro ⟨z, hz0, hz⟩ x hx
      simp [logDeriv_apply, hz.deriv hs2 hx, hz hx, deriv_const_smul _
        (hg.differentiableAt (hs2.mem_nhds hx)), mul_div_mul_left (deriv g x) (g x) hz0]


/-- At a simple zero of an analytic function, the logarithmic residue
`(w - x) * logDeriv f w` tends to 1. -/
/-
**AnalyticAt.tendsto_mul_logDeriv_simple_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticAt.tendsto_mul_logDeriv_simple_zero [CompleteSpace 𝕜] {f : 𝕜 -> 𝕜}
 {x : 𝕜} (hf : AnalyticAt 𝕜 f x) (hfx : f x = 0) (hf' : deriv f x != 0) : Filter
.Tendsto (fun w => (w - x) * logDeriv f w) (𝓝[!=] x) (𝓝 1)
参数：hf : AnalyticAt 𝕜 f x；hfx : f x = 0；hf' : deriv f x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `hasDerivAt_iff_tendsto_slope`：hasDerivAt_iff_tendsto_slope : HasDerivAt 
f f' x ↔ Tendsto (slope f x) (𝓝[!=] x) (𝓝 f')
· 使用定理 `DifferentiableAt.hasDerivAt`：DifferentiableAt.hasDerivAt (h : Differenti
ableAt 𝕜 f x) : HasDerivAt f (deriv f x) x
· 使用定理 `AnalyticAt.differentiableAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormed
Field 𝕜] {E : Type u} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 
E] {F : Type v} […
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
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
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval`：mul_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al * l₂.eval = l.eval) : x₁ *…
· 使用定理 `Mathlib.Tactic.FieldSimp.subst_sub`：subst_sub {M : Type*} [Ring M] {x₁ x
₂ X₁ X₂ Y y a : M} (h₁ : x₁ = a * X₁) (h₂ : x₂ = a * X₂) (H_atom : X₁ - X₂ = Y) 
(hy : a * Y = y) : x₁ - …
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_mul_eval_cons`：eval_mul_eval_cons [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : L.eval * ((n, e) ::ᵣ l).eval = …
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_div_of_eq_one_of_subst`：eq_div_of_eq_one_of_
subst {M : Type*} [DivInvOneMonoid M] {l l_n n : M} (h : l = l_n / 1) (hn : l_n 
= n) : l = n
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.cons_eq_div_of_eq_div`：cons_eq_div_of_eq_div
 [CommGroupWithZero M] (n : Int) (e : M) {t t_n t_d : NF M} (h : t.eval = t_n.ev
al / t_d.eval) : ((n, e) ::ᵣ t).eval = …
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons`：∀ {M : Type u_1} [inst : CommGrou
pWithZero M] (p : ℤ × M) (l : Mathlib.Tactic.FieldSimp.NF M),   (p ::ᵣ l).eval =
 l.eval * Mathlib.Tactic.Fi…
· 使用定理 `Mathlib.Tactic.FieldSimp.zpow'_one`：∀ {α : Type u_1} [inst : GroupWithZe
ro α] (a : α), Mathlib.Tactic.FieldSimp.zpow' a 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval`：div_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al / l₂.eval = l.eval) : x₁ /…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval₃`：div_eq_eval₃ [CommGroupWithZer
o M] {a₁ : Int × M} (a₂ : Int × M) {l₁ l₂ l : NF M} (h : (a₁ ::ᵣ l₁).eval / l₂.e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval₃`：mul_eq_eval₃ [CommGroupWithZer
o M] {a₁ : Int × M} (a₂ : Int × M) {l₁ l₂ l : NF M} (h : (a₁ ::ᵣ l₁).eval * l₂.e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
（共 80 条，此处仅展示前 30 条）

--- 原说明 ---
At a simple zero of an analytic function, the logarithmic residue
`(w - x) * logDeriv f w` tends to 1.
-/
theorem AnalyticAt.tendsto_mul_logDeriv_simple_zero [CompleteSpace 𝕜]
    {f : 𝕜 → 𝕜} {x : 𝕜}
    (hf : AnalyticAt 𝕜 f x) (hfx : f x = 0) (hf' : deriv f x ≠ 0) :
    Filter.Tendsto (fun w => (w - x) * logDeriv f w)
      (𝓝[≠] x) (𝓝 1) := by
  have h_slope := hasDerivAt_iff_tendsto_slope.mp hf.differentiableAt.hasDerivAt
  rw [← div_self hf']
  convert hf.deriv.continuousAt.tendsto.mono_left nhdsWithin_le_nhds |>.div h_slope hf'
  simp [logDeriv, slope, hfx]
  field
