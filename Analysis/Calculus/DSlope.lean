/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Slope of a differentiable function

Given a function `f : 𝕜 → E` from a nontrivially normed field to a normed space over this field,
`dslope f a b` is defined as `slope f a b = (b - a)⁻¹ • (f b - f a)` for `a ≠ b` and as `deriv f a`
for `a = b`.

In this file we define `dslope` and prove some basic lemmas about its continuity and
differentiability.
-/

@[expose] public section

open scoped Topology Filter

open Function Set Filter

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

open scoped Classical in
/-- `dslope f a b` is defined as `slope f a b = (b - a)⁻¹ • (f b - f a)` for `a ≠ b` and
`deriv f a` for `a = b`. -/
/-
**dslope** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：dslope (f : 𝕜 -> E) (a : 𝕜) : 𝕜 -> E
参数：f : 𝕜 -> E；a : 𝕜。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`dslope f a b` is defined as `slope f a b = (b - a)⁻¹ • (f b - f a)` for `a ≠ b`
 and
`deriv f a` for `a = b`.
-/
noncomputable def dslope (f : 𝕜 → E) (a : 𝕜) : 𝕜 → E :=
  update (slope f a) a (deriv f a)

@[simp]
/-
**dslope_same** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dslope_same (f : 𝕜 -> E) (a : 𝕜) : dslope f a a = deriv f a
参数：f : 𝕜 -> E；a : 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
-/
theorem dslope_same (f : 𝕜 → E) (a : 𝕜) : dslope f a a = deriv f a := by
  classical
  exact update_self ..

variable {f : 𝕜 → E} {a b : 𝕜} {s : Set 𝕜}
/-
**dslope_of_ne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dslope_of_ne (f : 𝕜 -> E) (h : b != a) : dslope f a b = slope f a b
参数：f : 𝕜 -> E；h : b != a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
-/
theorem dslope_of_ne (f : 𝕜 → E) (h : b ≠ a) : dslope f a b = slope f a b := by
  classical
  exact update_of_ne h ..
/-
**ContinuousLinearMap.dslope_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousLinearMap.dslope_comp {F : Type*} [NormedAddCommGroup F] [Normed
Space 𝕜 F] (f : E ->L[𝕜] F) (g : 𝕜 -> E) (a b : 𝕜) (H : a = b -> DifferentiableA
t 𝕜 g a) : dslope (f ∘ g) a b = f (dslope g a b)
参数：f : E ->L[𝕜] F；g : 𝕜 -> E；a b : 𝕜；H : a = b -> DifferentiableAt 𝕜 g a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dslope_same`：dslope_same (f : 𝕜 -> E) (a : 𝕜) : dslope f a a = deriv f a
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用定理 `HasFDerivAt.comp_hasDerivAt`：HasFDerivAt.comp_hasDerivAt (hl : HasFDeriv
At l l' (f x)) (hf : HasDerivAt f f' x) : HasDerivAt (l ∘ f) (l' f') x
· 使用定理 `ContinuousLinearMap.hasFDerivAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNo
rmedField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 
𝕜 E] [inst_3 : Topolo…
· 使用定理 `DifferentiableAt.hasDerivAt`：DifferentiableAt.hasDerivAt (h : Differenti
ableAt 𝕜 f x) : HasDerivAt f (deriv f x) x
· 使用定理 `dslope_of_ne`：dslope_of_ne (f : 𝕜 -> E) (h : b != a) : dslope f a b = sl
ope f a b
· 使用定理 `LinearMap.slope_comp`：LinearMap.slope_comp {F : Type*} [AddCommGroup F] 
[Module k F] (f : E ->ₗ[k] F) (g : k -> E) (a b : k) : slope (f ∘ g) a b = f (sl
ope g a b)
-/
theorem ContinuousLinearMap.dslope_comp {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (f : E →L[𝕜] F) (g : 𝕜 → E) (a b : 𝕜) (H : a = b → DifferentiableAt 𝕜 g a) :
    dslope (f ∘ g) a b = f (dslope g a b) := by
  rcases eq_or_ne b a with (rfl | hne)
  · simp only [dslope_same]
    exact (f.hasFDerivAt.comp_hasDerivAt b (H rfl).hasDerivAt).deriv
  · simpa only [dslope_of_ne _ hne] using! f.toLinearMap.slope_comp g a b
/-
**eqOn_dslope_slope** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eqOn_dslope_slope (f : 𝕜 -> E) (a : 𝕜) : EqOn (dslope f a) (slope f a) {a}
ᶜ
参数：f : 𝕜 -> E；a : 𝕜。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dslope_of_ne`：dslope_of_ne (f : 𝕜 -> E) (h : b != a) : dslope f a b = sl
ope f a b
-/
theorem eqOn_dslope_slope (f : 𝕜 → E) (a : 𝕜) : EqOn (dslope f a) (slope f a) {a}ᶜ := fun _ =>
  dslope_of_ne f
/-
**dslope_eventuallyEq_slope_of_ne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dslope_eventuallyEq_slope_of_ne (f : 𝕜 -> E) (h : b != a) : dslope f a =ᶠ[
𝓝 b] slope f a
参数：f : 𝕜 -> E；h : b != a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.EqOn.eventuallyEq_of_mem`：Set.EqOn.eventuallyEq_of_mem {α β} {s : Se
t α} {l : Filter α} {f g : α -> β} (h : EqOn f g s) (hl : s in l) : f =ᶠ[l] g
· 使用定理 `eqOn_dslope_slope`：eqOn_dslope_slope (f : 𝕜 -> E) (a : 𝕜) : EqOn (dslope
 f a) (slope f a) {a}ᶜ
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `isOpen_ne`：isOpen_ne [T1Space X] {x : X} : IsOpen { y | y != x }
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
-/
theorem dslope_eventuallyEq_slope_of_ne (f : 𝕜 → E) (h : b ≠ a) : dslope f a =ᶠ[𝓝 b] slope f a :=
  (eqOn_dslope_slope f a).eventuallyEq_of_mem (isOpen_ne.mem_nhds h)
/-
**dslope_eventuallyEq_slope_nhdsNE** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dslope_eventuallyEq_slope_nhdsNE (f : 𝕜 -> E) : dslope f a =ᶠ[𝓝[!=] a] slo
pe f a
参数：f : 𝕜 -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.EqOn.eventuallyEq_of_mem`：Set.EqOn.eventuallyEq_of_mem {α β} {s : Se
t α} {l : Filter α} {f g : α -> β} (h : EqOn f g s) (hl : s in l) : f =ᶠ[l] g
· 使用定理 `eqOn_dslope_slope`：eqOn_dslope_slope (f : 𝕜 -> E) (a : 𝕜) : EqOn (dslope
 f a) (slope f a) {a}ᶜ
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
-/
theorem dslope_eventuallyEq_slope_nhdsNE (f : 𝕜 → E) : dslope f a =ᶠ[𝓝[≠] a] slope f a :=
  (eqOn_dslope_slope f a).eventuallyEq_of_mem self_mem_nhdsWithin

@[simp]
/-
**sub_smul_dslope** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sub_smul_dslope (f : 𝕜 -> E) (a b : 𝕜) : (b - a) • dslope f a b = f b - f 
a
参数：f : 𝕜 -> E；a b : 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `dslope_same`：dslope_same (f : 𝕜 -> E) (a : 𝕜) : dslope f a a = deriv f a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dslope_of_ne`：dslope_of_ne (f : 𝕜 -> E) (h : b != a) : dslope f a b = sl
ope f a b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `sub_smul_slope`：sub_smul_slope (f : k -> PE) (a b : k) : (b - a) • slope
 f a b = f b -ᵥ f a
-/
theorem sub_smul_dslope (f : 𝕜 → E) (a b : 𝕜) : (b - a) • dslope f a b = f b - f a := by
  rcases eq_or_ne b a with (rfl | hne) <;> simp [dslope_of_ne, *]
/-
**dslope_sub_smul_of_ne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dslope_sub_smul_of_ne (f : 𝕜 -> E) (h : b != a) : dslope (fun x => (x - a)
 • f x) a b = f b
参数：f : 𝕜 -> E；h : b != a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dslope_of_ne`：dslope_of_ne (f : 𝕜 -> E) (h : b != a) : dslope f a b = sl
ope f a b
· 使用定理 `slope_sub_smul`：slope_sub_smul (f : k -> E) {a b : k} (h : a != b) : slo
pe (fun x => (x - a) • f x) a b = f b
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
-/
theorem dslope_sub_smul_of_ne (f : 𝕜 → E) (h : b ≠ a) :
    dslope (fun x => (x - a) • f x) a b = f b := by
  rw [dslope_of_ne _ h, slope_sub_smul _ h.symm]
/-
**eqOn_dslope_sub_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eqOn_dslope_sub_smul (f : 𝕜 -> E) (a : 𝕜) : EqOn (dslope (fun x => (x - a)
 • f x) a) f {a}ᶜ
参数：f : 𝕜 -> E；a : 𝕜。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dslope_sub_smul_of_ne`：dslope_sub_smul_of_ne (f : 𝕜 -> E) (h : b != a) :
 dslope (fun x => (x - a) • f x) a b = f b
-/
theorem eqOn_dslope_sub_smul (f : 𝕜 → E) (a : 𝕜) :
    EqOn (dslope (fun x => (x - a) • f x) a) f {a}ᶜ := fun _ => dslope_sub_smul_of_ne f
/-
**dslope_sub_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dslope_sub_smul [DecidableEq 𝕜] (f : 𝕜 -> E) (a : 𝕜) : dslope (fun x => (x
 - a) • f x) a = update f a (deriv (fun x => (x - a) • f x) a)
参数：f : 𝕜 -> E；a : 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.eq_update_iff`：eq_update_iff {a : α} {b : β a} {f g : forall a,
 β a} : g = update f a b ↔ g a = b ∧ forall x != a, g x = f x
· 使用定理 `dslope_same`：dslope_same (f : 𝕜 -> E) (a : 𝕜) : dslope f a a = deriv f a
· 使用定理 `eqOn_dslope_sub_smul`：eqOn_dslope_sub_smul (f : 𝕜 -> E) (a : 𝕜) : EqOn (
dslope (fun x => (x - a) • f x) a) f {a}ᶜ
-/
theorem dslope_sub_smul [DecidableEq 𝕜] (f : 𝕜 → E) (a : 𝕜) :
    dslope (fun x => (x - a) • f x) a = update f a (deriv (fun x => (x - a) • f x) a) :=
  eq_update_iff.2 ⟨dslope_same _ _, eqOn_dslope_sub_smul f a⟩

@[simp]
/-
**continuousAt_dslope_same** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousAt_dslope_same : ContinuousAt (dslope f a) a ↔ DifferentiableAt 
𝕜 f a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem continuousAt_dslope_same : ContinuousAt (dslope f a) a ↔ DifferentiableAt 𝕜 f a := by
  simp only [dslope, continuousAt_update_same, ← hasDerivAt_deriv_iff, hasDerivAt_iff_tendsto_slope]
/-
**ContinuousWithinAt.of_dslope** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousWithinAt.of_dslope (h : ContinuousWithinAt (dslope f a) s b) : C
ontinuousWithinAt f s b
参数：h : ContinuousWithinAt (dslope f a) s b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [in
st_1 : Add M] [ContinuousAdd M] {X : Type u_2}   [inst_3 : TopologicalSpace X] {
f g : X → M}…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContinuousWithinAt.smul`：ContinuousWithinAt.smul (hf : ContinuousWithinA
t f s b) (hg : ContinuousWithinAt g s b) : ContinuousWithinAt (f • g) s b
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `ContinuousWithinAt.sub`：∀ {G : Type u_1} {X : Type u_3} [inst : Topologi
calSpace X] [inst_1 : TopologicalSpace G] [inst_2 : Sub G]   [ContinuousSub G] {
f g : X → G}…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `continuousWithinAt_id`：continuousWithinAt_id {s : Set α} {x : α} : Conti
nuousWithinAt id s x
· 使用定理 `continuousWithinAt_const`：continuousWithinAt_const {b : β} {s : Set α} {
x : α} : ContinuousWithinAt (fun _ : α => b) s x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sub_smul_dslope`：sub_smul_dslope (f : 𝕜 -> E) (a b : 𝕜) : (b - a) • dslo
pe f a b = f b - f a
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
-/
theorem ContinuousWithinAt.of_dslope (h : ContinuousWithinAt (dslope f a) s b) :
    ContinuousWithinAt f s b := by
  have : ContinuousWithinAt (fun x => (x - a) • dslope f a x + f a) s b :=
    ((continuousWithinAt_id.sub continuousWithinAt_const).smul h).add continuousWithinAt_const
  simpa only [sub_smul_dslope, sub_add_cancel] using this
/-
**ContinuousAt.of_dslope** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousAt.of_dslope (h : ContinuousAt (dslope f a) b) : ContinuousAt f 
b
参数：h : ContinuousAt (dslope f a) b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `continuousWithinAt_univ`：continuousWithinAt_univ (f : α -> β) (x : α) : 
ContinuousWithinAt f Set.univ x ↔ ContinuousAt f x
· 使用定理 `ContinuousWithinAt.of_dslope`：ContinuousWithinAt.of_dslope (h : Continuo
usWithinAt (dslope f a) s b) : ContinuousWithinAt f s b
· 使用定理 `ContinuousAt.continuousWithinAt`：ContinuousAt.continuousWithinAt (h : Co
ntinuousAt f x) : ContinuousWithinAt f s x
-/
theorem ContinuousAt.of_dslope (h : ContinuousAt (dslope f a) b) : ContinuousAt f b :=
  (continuousWithinAt_univ _ _).1 h.continuousWithinAt.of_dslope
/-
**ContinuousOn.of_dslope** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.of_dslope (h : ContinuousOn (dslope f a) s) : ContinuousOn f 
s
参数：h : ContinuousOn (dslope f a) s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.of_dslope`：ContinuousWithinAt.of_dslope (h : Continuo
usWithinAt (dslope f a) s b) : ContinuousWithinAt f s b
-/
theorem ContinuousOn.of_dslope (h : ContinuousOn (dslope f a) s) : ContinuousOn f s := fun x hx =>
  (h x hx).of_dslope
/-
**continuousWithinAt_dslope_of_ne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousWithinAt_dslope_of_ne (h : b != a) : ContinuousWithinAt (dslope 
f a) s b ↔ ContinuousWithinAt f s b
参数：h : b != a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.of_dslope`：ContinuousWithinAt.of_dslope (h : Continuo
usWithinAt (dslope f a) s b) : ContinuousWithinAt f s b
· 使用定理 `continuousWithinAt_update_of_ne`：continuousWithinAt_update_of_ne [T1Spac
e X] [DecidableEq X] [TopologicalSpace Y] {f : X -> Y} {s : Set X} {x x' : X} {y
 : Y} (hne : x' != x)…
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `ContinuousWithinAt.smul`：ContinuousWithinAt.smul (hf : ContinuousWithinA
t f s b) (hg : ContinuousWithinAt g s b) : ContinuousWithinAt (f • g) s b
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `ContinuousWithinAt.inv₀`：∀ {α : Type u_1} {G₀ : Type u_3} [inst : Zero G
₀] [inst_1 : Inv G₀] [inst_2 : TopologicalSpace G₀] [ContinuousInv₀ G₀]   {f : α
 → G₀} {s : S…
· 使用定理 `IsTopologicalDivisionRing.toContinuousInv₀`：∀ {K : Type u_1} {inst : Div
isionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing K],
   ContinuousInv₀ K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `ContinuousWithinAt.sub`：∀ {G : Type u_1} {X : Type u_3} [inst : Topologi
calSpace X] [inst_1 : TopologicalSpace G] [inst_2 : Sub G]   [ContinuousSub G] {
f g : X → G}…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `continuousWithinAt_id`：continuousWithinAt_id {s : Set α} {x : α} : Conti
nuousWithinAt id s x
· 使用定理 `continuousWithinAt_const`：continuousWithinAt_const {b : β} {s : Set α} {
x : α} : ContinuousWithinAt (fun _ : α => b) s x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_ne_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b ≠ 0 ↔
 a ≠ b
-/
theorem continuousWithinAt_dslope_of_ne (h : b ≠ a) :
    ContinuousWithinAt (dslope f a) s b ↔ ContinuousWithinAt f s b := by
  refine ⟨ContinuousWithinAt.of_dslope, fun hc => ?_⟩
  classical
  simp only [dslope, continuousWithinAt_update_of_ne h]
  exact ((continuousWithinAt_id.sub continuousWithinAt_const).inv₀ (sub_ne_zero.2 h)).smul
    (hc.sub continuousWithinAt_const)
/-
**continuousAt_dslope_of_ne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousAt_dslope_of_ne (h : b != a) : ContinuousAt (dslope f a) b ↔ Con
tinuousAt f b
参数：h : b != a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `continuousWithinAt_dslope_of_ne`：continuousWithinAt_dslope_of_ne (h : b 
!= a) : ContinuousWithinAt (dslope f a) s b ↔ ContinuousWithinAt f s b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem continuousAt_dslope_of_ne (h : b ≠ a) : ContinuousAt (dslope f a) b ↔ ContinuousAt f b := by
  simp only [← continuousWithinAt_univ, continuousWithinAt_dslope_of_ne h]
/-
**continuousOn_dslope** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousOn_dslope (h : s in 𝓝 a) : ContinuousOn (dslope f a) s ↔ Continu
ousOn f s ∧ DifferentiableAt 𝕜 f a
参数：h : s in 𝓝 a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.of_dslope`：ContinuousOn.of_dslope (h : ContinuousOn (dslope
 f a) s) : ContinuousOn f s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `continuousAt_dslope_same`：continuousAt_dslope_same : ContinuousAt (dslop
e f a) a ↔ DifferentiableAt 𝕜 f a
· 使用定理 `ContinuousOn.continuousAt`：ContinuousOn.continuousAt (h : ContinuousOn f
 s) (hx : s in 𝓝 x) : ContinuousAt f x
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `ContinuousAt.continuousWithinAt`：ContinuousAt.continuousWithinAt (h : Co
ntinuousAt f x) : ContinuousWithinAt f s x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuousWithinAt_dslope_of_ne`：continuousWithinAt_dslope_of_ne (h : b 
!= a) : ContinuousWithinAt (dslope f a) s b ↔ ContinuousWithinAt f s b
-/
theorem continuousOn_dslope (h : s ∈ 𝓝 a) :
    ContinuousOn (dslope f a) s ↔ ContinuousOn f s ∧ DifferentiableAt 𝕜 f a := by
  refine ⟨fun hc => ⟨hc.of_dslope, continuousAt_dslope_same.1 <| hc.continuousAt h⟩, ?_⟩
  rintro ⟨hc, hd⟩ x hx
  rcases eq_or_ne x a with (rfl | hne)
  exacts [(continuousAt_dslope_same.2 hd).continuousWithinAt,
    (continuousWithinAt_dslope_of_ne hne).2 (hc x hx)]
/-
**DifferentiableWithinAt.of_dslope** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableWithinAt.of_dslope (h : DifferentiableWithinAt 𝕜 (dslope f a
) s b) : DifferentiableWithinAt 𝕜 f s b
参数：h : DifferentiableWithinAt 𝕜 (dslope f a) s b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sub_smul_dslope`：sub_smul_dslope (f : 𝕜 -> E) (a b : 𝕜) : (b - a) • dslo
pe f a b = f b - f a
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `DifferentiableWithinAt.add_const`：∀ {𝕜 : Type u_1} [inst : NontriviallyN
ormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedS
pace 𝕜 E] {F : Type u_…
· 使用定理 `DifferentiableWithinAt.fun_smul`：∀ {𝕜 : Type u_1} [inst : NontriviallyNo
rmedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSp
ace 𝕜 E] {F : Type u_…
· 使用定理 `DifferentiableWithinAt.sub_const`：DifferentiableWithinAt.sub_const (hf :
 DifferentiableWithinAt 𝕜 f s x) (c : F) : DifferentiableWithinAt 𝕜 (fun y => f 
y - c) s x
· 使用定理 `differentiableWithinAt_id`：differentiableWithinAt_id : DifferentiableWit
hinAt 𝕜 id s x
-/
theorem DifferentiableWithinAt.of_dslope (h : DifferentiableWithinAt 𝕜 (dslope f a) s b) :
    DifferentiableWithinAt 𝕜 f s b := by
  simpa only [id, sub_smul_dslope f a, sub_add_cancel] using
    ((differentiableWithinAt_id.sub_const a).fun_smul h).add_const (f a)
/-
**DifferentiableAt.of_dslope** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableAt.of_dslope (h : DifferentiableAt 𝕜 (dslope f a) b) : Diffe
rentiableAt 𝕜 f b
参数：h : DifferentiableAt 𝕜 (dslope f a) b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `differentiableWithinAt_univ`：differentiableWithinAt_univ : Differentiabl
eWithinAt 𝕜 f univ x ↔ DifferentiableAt 𝕜 f x
· 使用定理 `DifferentiableWithinAt.of_dslope`：DifferentiableWithinAt.of_dslope (h : 
DifferentiableWithinAt 𝕜 (dslope f a) s b) : DifferentiableWithinAt 𝕜 f s b
· 使用定理 `DifferentiableAt.differentiableWithinAt`：DifferentiableAt.differentiable
WithinAt (h : DifferentiableAt 𝕜 f x) : DifferentiableWithinAt 𝕜 f s x
-/
theorem DifferentiableAt.of_dslope (h : DifferentiableAt 𝕜 (dslope f a) b) :
    DifferentiableAt 𝕜 f b :=
  differentiableWithinAt_univ.1 h.differentiableWithinAt.of_dslope
/-
**DifferentiableOn.of_dslope** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DifferentiableOn.of_dslope (h : DifferentiableOn 𝕜 (dslope f a) s) : Diffe
rentiableOn 𝕜 f s
参数：h : DifferentiableOn 𝕜 (dslope f a) s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableWithinAt.of_dslope`：DifferentiableWithinAt.of_dslope (h : 
DifferentiableWithinAt 𝕜 (dslope f a) s b) : DifferentiableWithinAt 𝕜 f s b
-/
theorem DifferentiableOn.of_dslope (h : DifferentiableOn 𝕜 (dslope f a) s) :
    DifferentiableOn 𝕜 f s := fun x hx => (h x hx).of_dslope
/-
**differentiableWithinAt_dslope_of_ne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableWithinAt_dslope_of_ne (h : b != a) : DifferentiableWithinAt 
𝕜 (dslope f a) s b ↔ DifferentiableWithinAt 𝕜 f s b
参数：h : b != a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableWithinAt.of_dslope`：DifferentiableWithinAt.of_dslope (h : 
DifferentiableWithinAt 𝕜 (dslope f a) s b) : DifferentiableWithinAt 𝕜 f s b
· 使用定理 `DifferentiableWithinAt.congr_of_eventuallyEq`：DifferentiableWithinAt.con
gr_of_eventuallyEq (h : DifferentiableWithinAt 𝕜 f s x) (h₁ : f₁ =ᶠ[𝓝[s] x] f) (
hx : f₁ x = f x) : DifferentiableW…
· 使用定理 `DifferentiableWithinAt.smul`：DifferentiableWithinAt.smul (hc : Different
iableWithinAt 𝕜 c s x) (hf : DifferentiableWithinAt 𝕜 f s x) : DifferentiableWit
hinAt 𝕜 (c • f) s…
· 使用定理 `DifferentiableWithinAt.inv`：DifferentiableWithinAt.inv (hf : Differentia
bleWithinAt 𝕜 h S z) (hz : h z != 0) : DifferentiableWithinAt 𝕜 (h⁻¹) S z
· 使用定理 `DifferentiableWithinAt.sub_const`：DifferentiableWithinAt.sub_const (hf :
 DifferentiableWithinAt 𝕜 f s x) (c : F) : DifferentiableWithinAt 𝕜 (fun y => f 
y - c) s x
· 使用定理 `differentiableWithinAt_id`：differentiableWithinAt_id : DifferentiableWit
hinAt 𝕜 id s x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_ne_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b ≠ 0 ↔
 a ≠ b
· 使用定理 `Set.EqOn.eventuallyEq_of_mem`：Set.EqOn.eventuallyEq_of_mem {α β} {s : Se
t α} {l : Filter α} {f g : α -> β} (h : EqOn f g s) (hl : s in l) : f =ᶠ[l] g
· 使用定理 `eqOn_dslope_slope`：eqOn_dslope_slope (f : 𝕜 -> E) (a : 𝕜) : EqOn (dslope
 f a) (slope f a) {a}ᶜ
· 使用定理 `mem_nhdsWithin_of_mem_nhds`：mem_nhdsWithin_of_mem_nhds {s t : Set α} {a 
: α} (h : s in 𝓝 a) : s in 𝓝[t] a
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `isOpen_ne`：isOpen_ne [T1Space X] {x : X} : IsOpen { y | y != x }
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `dslope_of_ne`：dslope_of_ne (f : 𝕜 -> E) (h : b != a) : dslope f a b = sl
ope f a b
-/
theorem differentiableWithinAt_dslope_of_ne (h : b ≠ a) :
    DifferentiableWithinAt 𝕜 (dslope f a) s b ↔ DifferentiableWithinAt 𝕜 f s b := by
  refine ⟨DifferentiableWithinAt.of_dslope, fun hd => ?_⟩
  refine (((differentiableWithinAt_id.sub_const a).inv (sub_ne_zero.2 h)).smul
    (hd.sub_const (f a))).congr_of_eventuallyEq ?_ (dslope_of_ne _ h)
  refine (eqOn_dslope_slope _ _).eventuallyEq_of_mem ?_
  exact mem_nhdsWithin_of_mem_nhds (isOpen_ne.mem_nhds h)
/-
**differentiableOn_dslope_of_notMem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableOn_dslope_of_notMem (h : a ∉ s) : DifferentiableOn 𝕜 (dslope
 f a) s ↔ DifferentiableOn 𝕜 f s
参数：h : a ∉ s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `differentiableWithinAt_dslope_of_ne`：differentiableWithinAt_dslope_of_ne
 (h : b != a) : DifferentiableWithinAt 𝕜 (dslope f a) s b ↔ DifferentiableWithin
At 𝕜 f s b
· 使用定理 `ne_of_mem_of_not_mem`：∀ {α : Type u_1} {β : Type u_2} [inst : Membership
 α β] {s : β} {a b : α}, a ∈ s → b ∉ s → a ≠ b
-/
theorem differentiableOn_dslope_of_notMem (h : a ∉ s) :
    DifferentiableOn 𝕜 (dslope f a) s ↔ DifferentiableOn 𝕜 f s :=
  forall_congr' fun _ =>
    forall_congr' fun hx => differentiableWithinAt_dslope_of_ne <| ne_of_mem_of_not_mem hx h
/-
**differentiableAt_dslope_of_ne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：differentiableAt_dslope_of_ne (h : b != a) : DifferentiableAt 𝕜 (dslope f 
a) b ↔ DifferentiableAt 𝕜 f b
参数：h : b != a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `differentiableWithinAt_dslope_of_ne`：differentiableWithinAt_dslope_of_ne
 (h : b != a) : DifferentiableWithinAt 𝕜 (dslope f a) s b ↔ DifferentiableWithin
At 𝕜 f s b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem differentiableAt_dslope_of_ne (h : b ≠ a) :
    DifferentiableAt 𝕜 (dslope f a) b ↔ DifferentiableAt 𝕜 f b := by
  simp only [← differentiableWithinAt_univ, differentiableWithinAt_dslope_of_ne h]
/-
**sub_smul_dslope_of_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：sub_smul_dslope_of_zero {f : 𝕜 -> E} {a : 𝕜} (hf : f a = 0) (b : 𝕜) : (b -
 a) • dslope f a b = f b
参数：hf : f a = 0；b : 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_smul_dslope`：sub_smul_dslope (f : 𝕜 -> E) (a b : 𝕜) : (b - a) • dslo
pe f a b = f b - f a
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma sub_smul_dslope_of_zero {f : 𝕜 → E} {a : 𝕜} (hf : f a = 0) (b : 𝕜) :
    (b - a) • dslope f a b = f b := by
  simp [hf]
/-
**pow_sub_smul_iterate_dslope_of_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：pow_sub_smul_iterate_dslope_of_zero {f : 𝕜 -> E} {a : 𝕜} (n : Nat) (hf : f
orall k < n, (Function.swap dslope a)^[k] f a = 0) (b : 𝕜) : (b - a) ^ n • (Func
tion.swap dslope a)^[n] f b = f b
参数：n : Nat；hf : forall k < n, (Function.swap dslope a)^[k] f a = 0；b : 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Function.iterate_succ_apply'`：iterate_succ_apply' (n : Nat) (x : α) : f^
[n.succ] x = f (f^[n] x)
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用引理 `sub_smul_dslope_of_zero`：sub_smul_dslope_of_zero {f : 𝕜 -> E} {a : 𝕜} (h
f : f a = 0) (b : 𝕜) : (b - a) • dslope f a b = f b
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ
-/
lemma pow_sub_smul_iterate_dslope_of_zero {f : 𝕜 → E} {a : 𝕜} (n : ℕ)
    (hf : ∀ k < n, (Function.swap dslope a)^[k] f a = 0) (b : 𝕜) :
    (b - a) ^ n • (Function.swap dslope a)^[n] f b = f b := by
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', pow_succ, mul_smul,
      sub_smul_dslope_of_zero (hf n n.lt_succ_self), ih (by grind)]
