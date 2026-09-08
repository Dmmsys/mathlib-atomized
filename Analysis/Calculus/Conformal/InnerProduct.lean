/-
Copyright (c) 2021 Yourong Zang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yourong Zang
-/
module

public import Mathlib.Analysis.Calculus.Conformal.NormedSpace
public import Mathlib.Analysis.InnerProductSpace.ConformalLinearMap

/-!
# Conformal maps between inner product spaces

A function between inner product spaces which has a derivative at `x`
is conformal at `x` iff the derivative preserves inner products up to a scalar multiple.
-/

@[expose] public section


noncomputable section

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedAddCommGroup F]
variable [InnerProductSpace ℝ E] [InnerProductSpace ℝ F]

open RealInnerProductSpace

/-- A real differentiable map `f` is conformal at point `x` if and only if its
differential `fderiv ℝ f x` at that point scales every inner product by a positive scalar. -/
/-
**conformalAt_iff'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：conformalAt_iff' {f : E -> F} {x : E} : ConformalAt f x ↔ exists c : Real,
 0 < c ∧ forall u v : E, ⟪fderiv Real f x u, fderiv Real f x v⟫ = c * ⟪u, v⟫
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `conformalAt_iff_isConformalMap_fderiv`：conformalAt_iff_isConformalMap_fd
eriv {f : X -> Y} {x : X} : ConformalAt f x ↔ IsConformalMap (fderiv Real f x)
· 使用定理 `isConformalMap_iff`：isConformalMap_iff (f : E ->L[Real] F) : IsConformal
Map f ↔ exists c : Real, 0 < c ∧ forall u v : E, ⟪f u, f v⟫ = c * ⟪u, v⟫
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
A real differentiable map `f` is conformal at point `x` if and only if its
differential `fderiv ℝ f x` at that point scales every inner product by a positi
ve scalar.
-/
theorem conformalAt_iff' {f : E → F} {x : E} : ConformalAt f x ↔
    ∃ c : ℝ, 0 < c ∧ ∀ u v : E, ⟪fderiv ℝ f x u, fderiv ℝ f x v⟫ = c * ⟪u, v⟫ := by
  rw [conformalAt_iff_isConformalMap_fderiv, isConformalMap_iff]

/-- A real differentiable map `f` is conformal at point `x` if and only if its
differential `f'` at that point scales every inner product by a positive scalar. -/
/-
**conformalAt_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：conformalAt_iff {f : E -> F} {x : E} {f' : E ->L[Real] F} (h : HasFDerivAt
 f f' x) : ConformalAt f x ↔ exists c : Real, 0 < c ∧ forall u v : E, ⟪f' u, f' 
v⟫ = c * ⟪u, v⟫
参数：h : HasFDerivAt f f' x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `HasFDerivAt.fderiv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 
: Topolo…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A real differentiable map `f` is conformal at point `x` if and only if its
differential `f'` at that point scales every inner product by a positive scalar.
-/
theorem conformalAt_iff {f : E → F} {x : E} {f' : E →L[ℝ] F} (h : HasFDerivAt f f' x) :
    ConformalAt f x ↔ ∃ c : ℝ, 0 < c ∧ ∀ u v : E, ⟪f' u, f' v⟫ = c * ⟪u, v⟫ := by
  simp only [conformalAt_iff', h.fderiv]

/-- The conformal factor of a conformal map at some point `x`. Some authors refer to this function
as the characteristic function of the conformal map. -/
/-
**conformalFactorAt** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：conformalFactorAt {f : E -> F} {x : E} (h : ConformalAt f x) : Real
参数：h : ConformalAt f x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The conformal factor of a conformal map at some point `x`. Some authors refer to
 this function
as the characteristic function of the conformal map.
-/
def conformalFactorAt {f : E → F} {x : E} (h : ConformalAt f x) : ℝ :=
  Classical.choose (conformalAt_iff'.mp h)
/-
**conformalFactorAt_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：conformalFactorAt_pos {f : E -> F} {x : E} (h : ConformalAt f x) : 0 < con
formalFactorAt h
参数：h : ConformalAt f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `conformalAt_iff'`：conformalAt_iff' {f : E -> F} {x : E} : ConformalAt f 
x ↔ exists c : Real, 0 < c ∧ forall u v : E, ⟪fderiv Real f x u, fderiv Real f x
 v⟫ = …
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem conformalFactorAt_pos {f : E → F} {x : E} (h : ConformalAt f x) : 0 < conformalFactorAt h :=
  (Classical.choose_spec <| conformalAt_iff'.mp h).1
/-
**conformalFactorAt_inner_eq_mul_inner'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：conformalFactorAt_inner_eq_mul_inner' {f : E -> F} {x : E} (h : ConformalA
t f x) (u v : E) : ⟪(fderiv Real f x) u, (fderiv Real f x) v⟫ = (conformalFactor
At h : Real) * ⟪u, v⟫
参数：h : ConformalAt f x；u v : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `conformalAt_iff'`：conformalAt_iff' {f : E -> F} {x : E} : ConformalAt f 
x ↔ exists c : Real, 0 < c ∧ forall u v : E, ⟪fderiv Real f x u, fderiv Real f x
 v⟫ = …
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem conformalFactorAt_inner_eq_mul_inner' {f : E → F} {x : E} (h : ConformalAt f x) (u v : E) :
    ⟪(fderiv ℝ f x) u, (fderiv ℝ f x) v⟫ = (conformalFactorAt h : ℝ) * ⟪u, v⟫ :=
  (Classical.choose_spec <| conformalAt_iff'.mp h).2 u v
/-
**conformalFactorAt_inner_eq_mul_inner** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：conformalFactorAt_inner_eq_mul_inner {f : E -> F} {x : E} {f' : E ->L[Real
] F} (h : HasFDerivAt f f' x) (H : ConformalAt f x) (u v : E) : ⟪f' u, f' v⟫ = (
conformalFactorAt H : Real) * ⟪u, v⟫
参数：h : HasFDerivAt f f' x；H : ConformalAt f x；u v : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `conformalFactorAt_inner_eq_mul_inner'`：conformalFactorAt_inner_eq_mul_in
ner' {f : E -> F} {x : E} (h : ConformalAt f x) (u v : E) : ⟪(fderiv Real f x) u
, (fderiv Real f x) v⟫ = (c…
· 使用定理 `HasFDerivAt.unique`：HasFDerivAt.unique (h₀ : HasFDerivAt f f' x) (h₁ : H
asFDerivAt f f₁' x) : f' = f₁'
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `DifferentiableAt.hasFDerivAt`：DifferentiableAt.hasFDerivAt (h : Differen
tiableAt 𝕜 f x) : HasFDerivAt f (fderiv 𝕜 f x) x
· 使用定理 `ConformalAt.differentiableAt`：differentiableAt {f : X -> Y} {x : X} (h :
 ConformalAt f x) : DifferentiableAt Real f x
-/
theorem conformalFactorAt_inner_eq_mul_inner {f : E → F} {x : E} {f' : E →L[ℝ] F}
    (h : HasFDerivAt f f' x) (H : ConformalAt f x) (u v : E) :
    ⟪f' u, f' v⟫ = (conformalFactorAt H : ℝ) * ⟪u, v⟫ :=
  H.differentiableAt.hasFDerivAt.unique h ▸ conformalFactorAt_inner_eq_mul_inner' H u v
