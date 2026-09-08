/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Sébastien Gouëzel, Frédéric Dupuis
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!
# Continuity of inner product

We show that the inner product is continuous, `continuous_inner`.

## Tags

inner product space, Hilbert space, norm

-/

public section

noncomputable section

open RCLike Real Filter Topology ComplexConjugate Finsupp
open LinearMap renaming BilinForm → BilinForm

variable {𝕜 E F : Type*} [RCLike 𝕜]


section Continuous

variable [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-!
### Continuity of the inner product
-/

/-- When an inner product space `E` over `𝕜` is considered as a real normed space, its inner
product satisfies `IsBoundedBilinearMap`.

In order to state these results, we need a `NormedSpace ℝ E` instance. We will later establish
such an instance by restriction-of-scalars, `InnerProductSpace.rclikeToReal 𝕜 E`, but this
instance may be not definitionally equal to some other “natural” instance. So, we assume
`[NormedSpace ℝ E]`.
-/
/-
**_root_.isBoundedBilinearMap_inner** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：_root_.isBoundedBilinearMap_inner [NormedSpace Real E] [IsScalarTower Real
 𝕜 E] : IsBoundedBilinearMap Real fun p : E × E => ⟪p.1, p.2⟫
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When an inner product space `E` over `𝕜` is considered as a real normed space, i
ts inner
product satisfies `IsBoundedBilinearMap`.

In order to state these results, we need a `NormedSpace ℝ E` instance. We will l
ater establish
such an instance by restriction-of-scalars, `InnerProductSpace.rclikeToReal 𝕜 E`
, but this
instance may be not definitionally equal to some other “natural” instance. So, w
e assume
`[NormedSpace ℝ E]`.
-/
theorem _root_.isBoundedBilinearMap_inner [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] :
    IsBoundedBilinearMap ℝ fun p : E × E => ⟪p.1, p.2⟫ :=
  { add_left := inner_add_left
    smul_left := fun r x y => by
      simp only [← algebraMap_smul 𝕜 r x, algebraMap_eq_ofReal, inner_smul_real_left]
    add_right := inner_add_right
    smul_right := fun r x y => by
      simp only [← algebraMap_smul 𝕜 r y, algebraMap_eq_ofReal, inner_smul_real_right]
    bound :=
      ⟨1, zero_lt_one, fun x y => by
        rw [one_mul]
        exact norm_inner_le_norm x y⟩ }
/-
**continuous_inner** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_inner : Continuous fun p : E × E => ⟪p.1, p.2⟫
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedBilinearMap.continuous`：continuous (h : IsBoundedBilinearMap 𝕜 
f) : Continuous f
· 使用定理 `isBoundedBilinearMap_inner`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLi
ke 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E]   [in
st_3 : NormedSpa…
· 使用定理 `IsScalarTower.restrictScalars`：IsScalarTower.restrictScalars [Module S M
] : letI
-/
theorem continuous_inner : Continuous fun p : E × E => ⟪p.1, p.2⟫ :=
  letI : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal 𝕜 E
  haveI := IsScalarTower.restrictScalars ℝ 𝕜 E
  isBoundedBilinearMap_inner.continuous

variable {α : Type*}
/-
**Filter.Tendsto.inner** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.inner {f g : α -> E} {l : Filter α} {x y : E} (hf : Tendsto
 f l (𝓝 x)) (hg : Tendsto g l (𝓝 y)) : Tendsto (fun t => ⟪f t, g t⟫) l (𝓝 ⟪x, y⟫
)
参数：hf : Tendsto f l (𝓝 x)；hg : Tendsto g l (𝓝 y)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用定理 `continuous_inner`：continuous_inner : Continuous fun p : E × E => ⟪p.1, p
.2⟫
· 使用定理 `Filter.Tendsto.prodMk_nhds`：Filter.Tendsto.prodMk_nhds {γ} {x : X} {y : 
Y} {f : Filter γ} {mx : γ -> X} {my : γ -> Y} (hx : Tendsto mx f (𝓝 x)) (hy : Te
ndsto my f (𝓝 y)…
-/
theorem Filter.Tendsto.inner {f g : α → E} {l : Filter α} {x y : E} (hf : Tendsto f l (𝓝 x))
    (hg : Tendsto g l (𝓝 y)) : Tendsto (fun t => ⟪f t, g t⟫) l (𝓝 ⟪x, y⟫) :=
  (continuous_inner.tendsto _).comp (hf.prodMk_nhds hg)

variable [TopologicalSpace α] {f g : α → E} {x : α} {s : Set α}
/-
**ContinuousWithinAt.inner** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousWithinAt.inner (hf : ContinuousWithinAt f s x) (hg : ContinuousW
ithinAt g s x) : ContinuousWithinAt (fun t => ⟪f t, g t⟫) s x
参数：hf : ContinuousWithinAt f s x；hg : ContinuousWithinAt g s x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.inner`：Filter.Tendsto.inner {f g : α -> E} {l : Filter α}
 {x y : E} (hf : Tendsto f l (𝓝 x)) (hg : Tendsto g l (𝓝 y)) : Tendsto (fun t =>
 ⟪f t, g t…
-/
theorem ContinuousWithinAt.inner (hf : ContinuousWithinAt f s x) (hg : ContinuousWithinAt g s x) :
    ContinuousWithinAt (fun t => ⟪f t, g t⟫) s x :=
  Filter.Tendsto.inner hf hg

@[fun_prop]
/-
**ContinuousAt.inner** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousAt.inner (hf : ContinuousAt f x) (hg : ContinuousAt g x) : Conti
nuousAt (fun t => ⟪f t, g t⟫) x
参数：hf : ContinuousAt f x；hg : ContinuousAt g x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.inner`：Filter.Tendsto.inner {f g : α -> E} {l : Filter α}
 {x y : E} (hf : Tendsto f l (𝓝 x)) (hg : Tendsto g l (𝓝 y)) : Tendsto (fun t =>
 ⟪f t, g t…
-/
theorem ContinuousAt.inner (hf : ContinuousAt f x) (hg : ContinuousAt g x) :
    ContinuousAt (fun t => ⟪f t, g t⟫) x :=
  Filter.Tendsto.inner hf hg

@[fun_prop]
/-
**ContinuousOn.inner** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.inner (hf : ContinuousOn f s) (hg : ContinuousOn g s) : Conti
nuousOn (fun t => ⟪f t, g t⟫) s
参数：hf : ContinuousOn f s；hg : ContinuousOn g s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.inner`：ContinuousWithinAt.inner (hf : ContinuousWithi
nAt f s x) (hg : ContinuousWithinAt g s x) : ContinuousWithinAt (fun t => ⟪f t, 
g t⟫) s x
-/
theorem ContinuousOn.inner (hf : ContinuousOn f s) (hg : ContinuousOn g s) :
    ContinuousOn (fun t => ⟪f t, g t⟫) s := fun x hx => (hf x hx).inner (hg x hx)

@[continuity, fun_prop]
/-
**Continuous.inner** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.inner (hf : Continuous f) (hg : Continuous g) : Continuous fun 
t => ⟪f t, g t⟫
参数：hf : Continuous f；hg : Continuous g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用定理 `ContinuousAt.inner`：ContinuousAt.inner (hf : ContinuousAt f x) (hg : Con
tinuousAt g x) : ContinuousAt (fun t => ⟪f t, g t⟫) x
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
-/
theorem Continuous.inner (hf : Continuous f) (hg : Continuous g) : Continuous fun t => ⟪f t, g t⟫ :=
  continuous_iff_continuousAt.2 fun _x => by fun_prop

end Continuous

open Submodule

variable {E F ι : Type*}
variable (𝕜 : Type*) [RCLike 𝕜]
variable [NormedAddCommGroup E] [NormedAddCommGroup F]
variable [InnerProductSpace 𝕜 E] [InnerProductSpace ℝ F]
variable {x y : E} {S : Set E} {f : ι → E}

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-
**Dense.eq_zero_of_inner_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Dense.eq_zero_of_inner_left (hS : Dense S) (h : forall v in S, ⟪x, v⟫ = 0)
 : x = 0
参数：hS : Dense S；h : forall v in S, ⟪x, v⟫ = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dense.mono`：Dense.mono (h : s₁ subseteq s₂) (hd : Dense s₁) : Dense s₂
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `Continuous.ext_on`：Continuous.ext_on [T2Space X] {s : Set Y} (hs : Dense
 s) {f g : Y -> X} (hf : Continuous f) (hg : Continuous g) (h : EqOn f g s) : f 
= g
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Continuous.inner`：Continuous.inner (hf : Continuous f) (hg : Continuous 
g) : Continuous fun t => ⟪f t, g t⟫
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
· 使用定理 `Submodule.span_induction`：span_induction {p : (x : M) -> x in span R s -
> Prop} (mem : forall (x) (h : x in s), p x (subset_span h)) (zero : p 0 (Submod
ule.zero_mem _…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inner_zero_right`：inner_zero_right (x : E) : ⟪x, 0⟫ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `inner_add_right`：inner_add_right (x y z : E) : ⟪x, y + z⟫ = ⟪x, y⟫ + ⟪x,
 z⟫
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `inner_smul_right`：inner_smul_right (x y : E) (r : 𝕜) : ⟪x, r • y⟫ = r * 
⟪x, y⟫
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `inner_self_eq_norm_sq_to_K`：inner_self_eq_norm_sq_to_K (x : E) : ⟪x, x⟫ 
= (‖x‖ : 𝕜) ^ 2
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `instNontrivialOfCharZero`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [
CharZero α], Nontrivial α
（共 33 条，此处仅展示前 30 条）
-/
theorem Dense.eq_zero_of_inner_left (hS : Dense S) (h : ∀ v ∈ S, ⟪x, v⟫ = 0) : x = 0 := by
  let K := span 𝕜 S
  have hK : Dense (K : Set E) := hS.mono subset_span
  have : (⟪x, ·⟫) = 0 := (continuous_const.inner continuous_id).ext_on
    hK continuous_const fun v ↦ Submodule.span_induction h (by simp)
      (by simp +contextual [inner_add_right]) (by simp +contextual [inner_smul_right])
  simpa using congr_fun this x
/-
**Dense.eq_zero_of_inner_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Dense.eq_zero_of_inner_right (hS : Dense S) (h : forall v in S, ⟪v, x⟫ = 0
) : x = 0
参数：hS : Dense S；h : forall v in S, ⟪v, x⟫ = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dense.eq_zero_of_inner_left`：Dense.eq_zero_of_inner_left (hS : Dense S) 
(h : forall v in S, ⟪x, v⟫ = 0) : x = 0
· 使用定理 `Mathlib.Tactic.DepRewrite.eq_of_heq`：eq_of_heq.{u} {α : Sort u} {a a' : 
α} (h : a ≍ a') : a = a'
· 使用定理 `Mathlib.Tactic.DepRewrite.hdcongrArg`：hdcongrArg.{u, v} {α : Sort u} {a 
a' : α} {β : (a' : α) -> a = a' -> Sort v} (h : a = a') (f : (a' : α) -> (h : a 
= a') -> β a' h) : f a rfl…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inner_conj_symm`：inner_conj_symm (x y : E) : ⟪y, x⟫† = ⟪x, y⟫
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Dense.eq_zero_of_inner_right (hS : Dense S) (h : ∀ v ∈ S, ⟪v, x⟫ = 0) : x = 0 :=
  hS.eq_zero_of_inner_left 𝕜 fun v hv ↦ by rw! [← inner_conj_symm]; simp [-inner_conj_symm, h, hv]
/-
**Dense.eq_of_inner_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Dense.eq_of_inner_left (hS : Dense S) (h : forall v in S, ⟪x, v⟫ = ⟪y, v⟫)
 : x = y
参数：hS : Dense S；h : forall v in S, ⟪x, v⟫ = ⟪y, v⟫。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `Dense.eq_zero_of_inner_left`：Dense.eq_zero_of_inner_left (hS : Dense S) 
(h : forall v in S, ⟪x, v⟫ = 0) : x = 0
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inner_sub_left`：inner_sub_left (x y z : E) : ⟪x - y, z⟫ = ⟪x, z⟫ - ⟪y, z
⟫
-/
theorem Dense.eq_of_inner_left (hS : Dense S) (h : ∀ v ∈ S, ⟪x, v⟫ = ⟪y, v⟫) : x = y := by
  rw [← sub_eq_zero]; exact hS.eq_zero_of_inner_left 𝕜 (by simpa [inner_sub_left, sub_eq_zero])
/-
**Dense.eq_of_inner_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Dense.eq_of_inner_right (hS : Dense S) (h : forall v in S, ⟪v, x⟫ = ⟪v, y⟫
) : x = y
参数：hS : Dense S；h : forall v in S, ⟪v, x⟫ = ⟪v, y⟫。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `Dense.eq_zero_of_inner_right`：Dense.eq_zero_of_inner_right (hS : Dense S
) (h : forall v in S, ⟪v, x⟫ = 0) : x = 0
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inner_sub_right`：inner_sub_right (x y z : E) : ⟪x, y - z⟫ = ⟪x, y⟫ - ⟪x,
 z⟫
-/
theorem Dense.eq_of_inner_right (hS : Dense S) (h : ∀ v ∈ S, ⟪v, x⟫ = ⟪v, y⟫) : x = y := by
  rw [← sub_eq_zero]; exact hS.eq_zero_of_inner_right 𝕜 (by simpa [inner_sub_right, sub_eq_zero])

nonrec theorem DenseRange.eq_of_inner_left (hf : DenseRange f) (h : ∀ i, ⟪x, f i⟫ = ⟪y, f i⟫) :
    x = y := hf.eq_of_inner_left 𝕜 (by simpa)

nonrec theorem DenseRange.eq_of_inner_right (hf : DenseRange f) (h : ∀ i, ⟪f i, x⟫ = ⟪f i, y⟫) :
    x = y := hf.eq_of_inner_right 𝕜 (by simpa)

nonrec theorem DenseRange.eq_zero_of_inner_left (hf : DenseRange f) (h : ∀ i, ⟪x, f i⟫ = 0) :
    x = 0 := hf.eq_zero_of_inner_left 𝕜 (by simpa)

nonrec theorem DenseRange.eq_zero_of_inner_right (hf : DenseRange f) (h : ∀ i, ⟪f i, x⟫ = 0) :
    x = 0 := hf.eq_zero_of_inner_right 𝕜 (by simpa)
