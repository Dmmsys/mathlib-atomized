/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# One-dimensional iterated derivatives

We define the `n`-th derivative of a function `f : 𝕜 → F` as a function
`iteratedDeriv n f : 𝕜 → F`, as well as a version on domains `iteratedDerivWithin n f s : 𝕜 → F`,
and prove their basic properties.

## Main definitions and results

Let `𝕜` be a nontrivially normed field, and `F` a normed vector space over `𝕜`. Let `f : 𝕜 → F`.

* `iteratedDeriv n f` is the `n`-th derivative of `f`, seen as a function from `𝕜` to `F`.
  It is defined as the `n`-th Fréchet derivative (which is a multilinear map) applied to the
  vector `(1, ..., 1)`, to take advantage of all the existing framework, but we show that it
  coincides with the naive iterative definition.
* `iteratedDeriv_eq_iterate` states that the `n`-th derivative of `f` is obtained by starting
  from `f` and differentiating it `n` times.
* `iteratedDerivWithin n f s` is the `n`-th derivative of `f` within the domain `s`. It only
  behaves well when `s` has the unique derivative property.
* `iteratedDerivWithin_eq_iterate` states that the `n`-th derivative of `f` in the domain `s` is
  obtained by starting from `f` and differentiating it `n` times within `s`. This only holds when
  `s` has the unique derivative property.

## Implementation details

The results are deduced from the corresponding results for the more general (multilinear) iterated
Fréchet derivative. For this, we write `iteratedDeriv n f` as the composition of
`iteratedFDeriv 𝕜 n f` and a continuous linear equiv. As continuous linear equivs respect
differentiability and commute with differentiation, this makes it possible to prove readily that
the derivative of the `n`-th derivative is the `n+1`-th derivative in `iteratedDerivWithin_succ`,
by translating the corresponding result `iteratedFDerivWithin_succ_apply_left` for the
iterated Fréchet derivative.
-/

@[expose] public section

noncomputable section

open scoped Topology ContDiff
open Filter Asymptotics Set

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The `n`-th iterated derivative of a function from `𝕜` to `F`, as a function from `𝕜` to `F`. -/
/-
**iteratedDeriv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：iteratedDeriv (n : Nat) (f : 𝕜 -> F) (x : 𝕜) : F
参数：n : Nat；f : 𝕜 -> F；x : 𝕜。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `n`-th iterated derivative of a function from `𝕜` to `F`, as a function from
 `𝕜` to `F`.
-/
def iteratedDeriv (n : ℕ) (f : 𝕜 → F) (x : 𝕜) : F :=
  (iteratedFDeriv 𝕜 n f x : (Fin n → 𝕜) → F) fun _ : Fin n => 1

/-- The `n`-th iterated derivative of a function from `𝕜` to `F` within a set `s`, as a function
from `𝕜` to `F`. -/
/-
**iteratedDerivWithin** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：iteratedDerivWithin (n : Nat) (f : 𝕜 -> F) (s : Set 𝕜) (x : 𝕜) : F
参数：n : Nat；f : 𝕜 -> F；s : Set 𝕜；x : 𝕜。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `n`-th iterated derivative of a function from `𝕜` to `F` within a set `s`, a
s a function
from `𝕜` to `F`.
-/
def iteratedDerivWithin (n : ℕ) (f : 𝕜 → F) (s : Set 𝕜) (x : 𝕜) : F :=
  (iteratedFDerivWithin 𝕜 n f s x : (Fin n → 𝕜) → F) fun _ : Fin n => 1

variable {n : ℕ} {f : 𝕜 → F} {s : Set 𝕜} {x : 𝕜}

@[simp]
/-
**iteratedDerivWithin_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedDerivWithin_univ : iteratedDerivWithin n f univ = iteratedDeriv n 
f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iteratedDerivWithin.eq_1`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFie
ld 𝕜] {F : Type u_2} [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F
] (n : ℕ) (f :…
· 使用定理 `iteratedDeriv.eq_1`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] 
{F : Type u_2} [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] (n :
 ℕ) (f :…
· 使用定理 `iteratedFDerivWithin_univ`：iteratedFDerivWithin_univ {n : Nat} : iterate
dFDerivWithin 𝕜 n f univ = iteratedFDeriv 𝕜 n f
-/
theorem iteratedDerivWithin_univ : iteratedDerivWithin n f univ = iteratedDeriv n f := by
  ext x
  rw [iteratedDerivWithin, iteratedDeriv, iteratedFDerivWithin_univ]
/-
**iteratedDerivWithin_eq_iteratedDeriv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedDerivWithin_eq_iteratedDeriv (hs : UniqueDiffOn 𝕜 s) (h : ContDiff
At 𝕜 n f x) (hx : x in s) : iteratedDerivWithin n f s x = iteratedDeriv n f x
参数：hs : UniqueDiffOn 𝕜 s；h : ContDiffAt 𝕜 n f x；hx : x in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iteratedDerivWithin.eq_1`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFie
ld 𝕜] {F : Type u_2} [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F
] (n : ℕ) (f :…
· 使用定理 `iteratedDeriv.eq_1`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] 
{F : Type u_2} [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] (n :
 ℕ) (f :…
· 使用定理 `iteratedFDerivWithin_eq_iteratedFDeriv`：iteratedFDerivWithin_eq_iterated
FDeriv {n : Nat} (hs : UniqueDiffOn 𝕜 s) (h : ContDiffAt 𝕜 n f x) (hx : x in s) 
: iteratedFDerivWithin 𝕜 n f…
-/
theorem iteratedDerivWithin_eq_iteratedDeriv (hs : UniqueDiffOn 𝕜 s) (h : ContDiffAt 𝕜 n f x)
    (hx : x ∈ s) : iteratedDerivWithin n f s x = iteratedDeriv n f x := by
  rw [iteratedDerivWithin, iteratedDeriv, iteratedFDerivWithin_eq_iteratedFDeriv hs h hx]

/-! ### Properties of the iterated derivative within a set -/


/-
**iteratedDerivWithin_eq_iteratedFDerivWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedDerivWithin_eq_iteratedFDerivWithin : iteratedDerivWithin n f s x 
= (iteratedFDerivWithin 𝕜 n f s x : (Fin n -> 𝕜) -> F) fun _ : Fin n => 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Properties of the iterated derivative within a set
-/
theorem iteratedDerivWithin_eq_iteratedFDerivWithin : iteratedDerivWithin n f s x =
    (iteratedFDerivWithin 𝕜 n f s x : (Fin n → 𝕜) → F) fun _ : Fin n => 1 :=
  rfl

/-- Write the iterated derivative as the composition of a continuous linear equiv and the iterated
Fréchet derivative -/
/-
**iteratedDerivWithin_eq_equiv_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedDerivWithin_eq_equiv_comp : iteratedDerivWithin n f s = (Continuou
sMultilinearMap.piFieldEquiv 𝕜 (Fin n) F).symm ∘ iteratedFDerivWithin 𝕜 n f s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …

--- 原说明 ---
Write the iterated derivative as the composition of a continuous linear equiv an
d the iterated
Fréchet derivative
-/
theorem iteratedDerivWithin_eq_equiv_comp : iteratedDerivWithin n f s =
    (ContinuousMultilinearMap.piFieldEquiv 𝕜 (Fin n) F).symm ∘ iteratedFDerivWithin 𝕜 n f s := by
  ext x; rfl

/-- Write the iterated Fréchet derivative as the composition of a continuous linear equiv and the
iterated derivative. -/
/-
**iteratedFDerivWithin_eq_equiv_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedFDerivWithin_eq_equiv_comp : iteratedFDerivWithin 𝕜 n f s = Contin
uousMultilinearMap.piFieldEquiv 𝕜 (Fin n) F ∘ iteratedDerivWithin n f s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iteratedDerivWithin_eq_equiv_comp`：iteratedDerivWithin_eq_equiv_comp : i
teratedDerivWithin n f s = (ContinuousMultilinearMap.piFieldEquiv 𝕜 (Fin n) F).s
ymm ∘ iteratedFDerivWit…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.comp_assoc`：comp_assoc (f : φ -> δ) (g : β -> φ) (h : α -> β) :
 (f ∘ g) ∘ h = f ∘ g ∘ h
· 使用定理 `LinearIsometryEquiv.self_comp_symm`：self_comp_symm : e ∘ e.symm = id
· 使用定理 `Function.id_comp`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β), id ∘ f = 
f

--- 原说明 ---
Write the iterated Fréchet derivative as the composition of a continuous linear 
equiv and the
iterated derivative.
-/
theorem iteratedFDerivWithin_eq_equiv_comp :
    iteratedFDerivWithin 𝕜 n f s =
      ContinuousMultilinearMap.piFieldEquiv 𝕜 (Fin n) F ∘ iteratedDerivWithin n f s := by
  rw [iteratedDerivWithin_eq_equiv_comp, ← Function.comp_assoc, LinearIsometryEquiv.self_comp_symm,
    Function.id_comp]

/-- The `n`-th Fréchet derivative applied to a vector `(m 0, ..., m (n-1))` is the derivative
multiplied by the product of the `m i`s. -/
/-
**iteratedFDerivWithin_apply_eq_iteratedDerivWithin_mul_prod** 是 Mathlib 中的一个定理，
位于命名空间 ``。
形式化陈述：iteratedFDerivWithin_apply_eq_iteratedDerivWithin_mul_prod {m : Fin n -> 𝕜
} : (iteratedFDerivWithin 𝕜 n f s x : (Fin n -> 𝕜) -> F) m = (∏ i, m i) • iterat
edDerivWithin n f s x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iteratedDerivWithin_eq_iteratedFDerivWithin`：iteratedDerivWithin_eq_iter
atedFDerivWithin : iteratedDerivWithin n f s x = (iteratedFDerivWithin 𝕜 n f s x
 : (Fin n -> 𝕜) -> F) fun _ : Fin…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousMultilinearMap.map_smul_univ`：map_smul_univ [Fintype ι] (c : ι
 -> R) (m : forall i, M₁ i) : (f fun i => c i • m i) = (∏ i, c i) • f m
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The `n`-th Fréchet derivative applied to a vector `(m 0, ..., m (n-1))` is the d
erivative
multiplied by the product of the `m i`s.
-/
theorem iteratedFDerivWithin_apply_eq_iteratedDerivWithin_mul_prod {m : Fin n → 𝕜} :
    (iteratedFDerivWithin 𝕜 n f s x : (Fin n → 𝕜) → F) m =
      (∏ i, m i) • iteratedDerivWithin n f s x := by
  rw [iteratedDerivWithin_eq_iteratedFDerivWithin, ← ContinuousMultilinearMap.map_smul_univ]
  simp
/-
**norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin** 是 Mathlib 中的一个定理，位于命名空
间 ``。
形式化陈述：norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin : ‖iteratedFDerivWit
hin 𝕜 n f s x‖ = ‖iteratedDerivWithin n f s x‖
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iteratedDerivWithin_eq_equiv_comp`：iteratedDerivWithin_eq_equiv_comp : i
teratedDerivWithin n f s = (ContinuousMultilinearMap.piFieldEquiv 𝕜 (Fin n) F).s
ymm ∘ iteratedFDerivWit…
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `LinearIsometryEquiv.norm_map`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type
 u_5} {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* 
R₂} {σ₂₁ : R₂ →+* …
-/
theorem norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin :
    ‖iteratedFDerivWithin 𝕜 n f s x‖ = ‖iteratedDerivWithin n f s x‖ := by
  rw [iteratedDerivWithin_eq_equiv_comp, Function.comp_apply, LinearIsometryEquiv.norm_map]

@[simp]
/-
**iteratedDerivWithin_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedDerivWithin_zero : iteratedDerivWithin 0 f s = f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iteratedDerivWithin_zero : iteratedDerivWithin 0 f s = f := by
  ext x
  simp [iteratedDerivWithin]

@[simp]
/-
**iteratedDerivWithin_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedDerivWithin_one : iteratedDerivWithin 1 f s = derivWithin f s
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
· 使用定理 `iteratedFDerivWithin_one_apply`：iteratedFDerivWithin_one_apply (h : Uniq
ueDiffWithinAt 𝕜 s x) (m : Fin 1 -> E) : iteratedFDerivWithin 𝕜 1 f s x m = fder
ivWithin 𝕜 f s x (m …
· 使用定理 `AccPt.uniqueDiffWithinAt`：∀ {𝕜 : Type u_1} [inst : NormedDivisionRing 𝕜]
 {s : Set 𝕜} {x : 𝕜},   AccPt x (Filter.principal s) → UniqueDiffWithinAt 𝕜 s x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `fderivWithin_zero_of_not_accPt`：fderivWithin_zero_of_not_accPt (h : ¬Acc
Pt x (𝓟 s)) : fderivWithin 𝕜 f s x = 0
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `ContinuousMultilinearMap.instIsZeroApplyForall`：∀ {R : Type u} {ι : Type
 v} {M₁ : ι → Type w₁} {M₂ : Type w₂} [inst : Semiring R]   [inst_1 : (i : ι) → 
AddCommMonoid (M₁ i)] [inst_2 : AddC…
· 使用定理 `derivWithin_zero_of_not_accPt`：derivWithin_zero_of_not_accPt (h : ¬AccPt
 x (𝓟 s)) : derivWithin f s x = 0
-/
theorem iteratedDerivWithin_one :
    iteratedDerivWithin 1 f s = derivWithin f s := by
  ext x
  by_cases hsx : AccPt x (𝓟 s)
  · simp only [iteratedDerivWithin, iteratedFDerivWithin_one_apply hsx.uniqueDiffWithinAt,
      derivWithin]
  · simp [derivWithin_zero_of_not_accPt hsx, iteratedDerivWithin, iteratedFDerivWithin,
      fderivWithin_zero_of_not_accPt hsx]

/-- If the first `n` derivatives within a set of a function are continuous, and its first `n-1`
derivatives are differentiable, then the function is `C^n`. This is not an equivalence in general,
but this is an equivalence when the set has unique derivatives, see
`contDiffOn_iff_continuousOn_differentiableOn_deriv`. -/
/-
**contDiffOn_of_continuousOn_differentiableOn_deriv** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：contDiffOn_of_continuousOn_differentiableOn_deriv {n : Nat∞} (Hcont : fora
ll m : Nat, (m : Nat∞) <= n -> ContinuousOn (fun x => iteratedDerivWithin m f s 
x) s) (Hdiff : forall m : Nat, (m : Nat∞) < n -> DifferentiableOn 𝕜 (fun x => it
eratedDerivWithin m f s x) s) : ContDiffOn 𝕜 n f s
参数：Hcont : forall m : Nat, (m : Nat∞) <= n -> ContinuousOn (fun x => iteratedDer
ivWithin m f s x) s；Hdiff : forall m : Nat, (m : Nat∞) < n -> DifferentiableOn 𝕜
 (fun x => iteratedDerivWithin m f s x) s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `contDiffOn_of_continuousOn_differentiableOn`：contDiffOn_of_continuousOn_
differentiableOn {n : Nat∞} (Hcont : forall m : Nat, m <= n -> ContinuousOn (fun
 x => iteratedFDerivWithin 𝕜 m f …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `iteratedFDerivWithin_eq_equiv_comp`：iteratedFDerivWithin_eq_equiv_comp :
 iteratedFDerivWithin 𝕜 n f s = ContinuousMultilinearMap.piFieldEquiv 𝕜 (Fin n) 
F ∘ iteratedDerivWithin …

--- 原说明 ---
If the first `n` derivatives within a set of a function are continuous, and its 
first `n-1`
derivatives are differentiable, then the function is `C^n`. This is not an equiv
alence in general,
but this is an equivalence when the set has unique derivatives, see
`contDiffOn_iff_continuousOn_differentiableOn_deriv`.
-/
theorem contDiffOn_of_continuousOn_differentiableOn_deriv {n : ℕ∞}
    (Hcont : ∀ m : ℕ, (m : ℕ∞) ≤ n → ContinuousOn (fun x => iteratedDerivWithin m f s x) s)
    (Hdiff : ∀ m : ℕ, (m : ℕ∞) < n → DifferentiableOn 𝕜 (fun x => iteratedDerivWithin m f s x) s) :
    ContDiffOn 𝕜 n f s := by
  apply contDiffOn_of_continuousOn_differentiableOn
  · simpa only [iteratedFDerivWithin_eq_equiv_comp, LinearIsometryEquiv.comp_continuousOn_iff]
  · simpa only [iteratedFDerivWithin_eq_equiv_comp, LinearIsometryEquiv.comp_differentiableOn_iff]

/-- To check that a function is `n` times continuously differentiable, it suffices to check that its
first `n` derivatives are differentiable. This is slightly too strong as the condition we
require on the `n`-th derivative is differentiability instead of continuity, but it has the
advantage of avoiding the discussion of continuity in the proof (and for `n = ∞` this is optimal).
-/
/-
**contDiffOn_of_differentiableOn_deriv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffOn_of_differentiableOn_deriv {n : Nat∞} (h : forall m : Nat, (m : 
Nat∞) <= n -> DifferentiableOn 𝕜 (iteratedDerivWithin m f s) s) : ContDiffOn 𝕜 n
 f s
参数：h : forall m : Nat, (m : Nat∞) <= n -> DifferentiableOn 𝕜 (iteratedDerivWithi
n m f s) s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `contDiffOn_of_differentiableOn`：contDiffOn_of_differentiableOn {n : Nat∞
} (h : forall m : Nat, m <= n -> DifferentiableOn 𝕜 (iteratedFDerivWithin 𝕜 m f 
s) s) : ContDiffOn 𝕜…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iteratedFDerivWithin_eq_equiv_comp`：iteratedFDerivWithin_eq_equiv_comp :
 iteratedFDerivWithin 𝕜 n f s = ContinuousMultilinearMap.piFieldEquiv 𝕜 (Fin n) 
F ∘ iteratedDerivWithin …

--- 原说明 ---
To check that a function is `n` times continuously differentiable, it suffices t
o check that its
first `n` derivatives are differentiable. This is slightly too strong as the con
dition we
require on the `n`-th derivative is differentiability instead of continuity, but
 it has the
advantage of avoiding the discussion of continuity in the proof (and for `n = ∞`
 this is optimal).
-/
theorem contDiffOn_of_differentiableOn_deriv {n : ℕ∞}
    (h : ∀ m : ℕ, (m : ℕ∞) ≤ n → DifferentiableOn 𝕜 (iteratedDerivWithin m f s) s) :
    ContDiffOn 𝕜 n f s := by
  apply contDiffOn_of_differentiableOn
  simpa only [iteratedFDerivWithin_eq_equiv_comp, LinearIsometryEquiv.comp_differentiableOn_iff]

/-- On a set with unique derivatives, a `C^n` function has derivatives up to `n` which are
continuous. -/
/-
**ContDiffOn.continuousOn_iteratedDerivWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffOn.continuousOn_iteratedDerivWithin {n : Nat∞ω} {m : Nat} (h : Con
tDiffOn 𝕜 n f s) (hmn : m <= n) (hs : UniqueDiffOn 𝕜 s) : ContinuousOn (iterated
DerivWithin m f s) s
参数：h : ContDiffOn 𝕜 n f s；hmn : m <= n；hs : UniqueDiffOn 𝕜 s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iteratedDerivWithin_eq_equiv_comp`：iteratedDerivWithin_eq_equiv_comp : i
teratedDerivWithin n f s = (ContinuousMultilinearMap.piFieldEquiv 𝕜 (Fin n) F).s
ymm ∘ iteratedFDerivWit…
· 使用定理 `ContDiffOn.continuousOn_iteratedFDerivWithin`：ContDiffOn.continuousOn_it
eratedFDerivWithin {m : Nat} (h : ContDiffOn 𝕜 n f s) (hmn : m <= n) (hs : Uniqu
eDiffOn 𝕜 s) : ContinuousOn (itera…

--- 原说明 ---
On a set with unique derivatives, a `C^n` function has derivatives up to `n` whi
ch are
continuous.
-/
theorem ContDiffOn.continuousOn_iteratedDerivWithin
    {n : ℕ∞ω} {m : ℕ} (h : ContDiffOn 𝕜 n f s)
    (hmn : m ≤ n) (hs : UniqueDiffOn 𝕜 s) : ContinuousOn (iteratedDerivWithin m f s) s := by
  simpa only [iteratedDerivWithin_eq_equiv_comp, LinearIsometryEquiv.comp_continuousOn_iff] using
    h.continuousOn_iteratedFDerivWithin hmn hs
/-
**ContDiffWithinAt.differentiableWithinAt_iteratedDerivWithin** 是 Mathlib 中的一个定理
，位于命名空间 ``。
形式化陈述：ContDiffWithinAt.differentiableWithinAt_iteratedDerivWithin {n : Nat∞ω} {m
 : Nat} (h : ContDiffWithinAt 𝕜 n f s x) (hmn : m < n) (hs : UniqueDiffOn 𝕜 (ins
ert x s)) : DifferentiableWithinAt 𝕜 (iteratedDerivWithin m f s) s x
参数：h : ContDiffWithinAt 𝕜 n f s x；hmn : m < n；hs : UniqueDiffOn 𝕜 (insert x s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iteratedDerivWithin_eq_equiv_comp`：iteratedDerivWithin_eq_equiv_comp : i
teratedDerivWithin n f s = (ContinuousMultilinearMap.piFieldEquiv 𝕜 (Fin n) F).s
ymm ∘ iteratedFDerivWit…
· 使用定理 `ContDiffWithinAt.differentiableWithinAt_iteratedFDerivWithin`：ContDiffWi
thinAt.differentiableWithinAt_iteratedFDerivWithin {m : Nat} (h : ContDiffWithin
At 𝕜 n f s x) (hmn : m < n) (hs : UniqueDiffOn 𝕜 (…
-/
theorem ContDiffWithinAt.differentiableWithinAt_iteratedDerivWithin {n : ℕ∞ω} {m : ℕ}
    (h : ContDiffWithinAt 𝕜 n f s x) (hmn : m < n) (hs : UniqueDiffOn 𝕜 (insert x s)) :
    DifferentiableWithinAt 𝕜 (iteratedDerivWithin m f s) s x := by
  simpa only [iteratedDerivWithin_eq_equiv_comp,
    LinearIsometryEquiv.comp_differentiableWithinAt_iff] using
    h.differentiableWithinAt_iteratedFDerivWithin hmn hs

/-- On a set with unique derivatives, a `C^n` function has derivatives less than `n` which are
differentiable. -/
/-
**ContDiffOn.differentiableOn_iteratedDerivWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiffOn.differentiableOn_iteratedDerivWithin {n : Nat∞ω} {m : Nat} (h :
 ContDiffOn 𝕜 n f s) (hmn : m < n) (hs : UniqueDiffOn 𝕜 s) : DifferentiableOn 𝕜 
(iteratedDerivWithin m f s) s
参数：h : ContDiffOn 𝕜 n f s；hmn : m < n；hs : UniqueDiffOn 𝕜 s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffWithinAt.differentiableWithinAt_iteratedDerivWithin`：ContDiffWit
hinAt.differentiableWithinAt_iteratedDerivWithin {n : Nat∞ω} {m : Nat} (h : Cont
DiffWithinAt 𝕜 n f s x) (hmn : m < n) (hs : Uniqu…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.insert_eq_of_mem`：insert_eq_of_mem {a : α} {s : Set α} (h : a in s) 
: insert a s = s

--- 原说明 ---
On a set with unique derivatives, a `C^n` function has derivatives less than `n`
 which are
differentiable.
-/
theorem ContDiffOn.differentiableOn_iteratedDerivWithin {n : ℕ∞ω} {m : ℕ}
    (h : ContDiffOn 𝕜 n f s) (hmn : m < n) (hs : UniqueDiffOn 𝕜 s) :
    DifferentiableOn 𝕜 (iteratedDerivWithin m f s) s := fun x hx =>
  (h x hx).differentiableWithinAt_iteratedDerivWithin hmn <| by rwa [insert_eq_of_mem hx]

/-- The property of being `C^n`, initially defined in terms of the Fréchet derivative, can be
reformulated in terms of the one-dimensional derivative on sets with unique derivatives. -/
/-
**contDiffOn_iff_continuousOn_differentiableOn_deriv** 是 Mathlib 中的一个定理，位于命名空间 `
`。
形式化陈述：contDiffOn_iff_continuousOn_differentiableOn_deriv {n : Nat∞} (hs : Unique
DiffOn 𝕜 s) : ContDiffOn 𝕜 n f s ↔ (forall m : Nat, (m : Nat∞) <= n -> Continuou
sOn (iteratedDerivWithin m f s) s) ∧ forall m : Nat, (m : Nat∞) < n -> Different
iableOn 𝕜 (iteratedDerivWithin m f s) s
参数：hs : UniqueDiffOn 𝕜 s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `contDiffOn_iff_continuousOn_differentiableOn`：contDiffOn_iff_continuousO
n_differentiableOn {n : Nat∞} (hs : UniqueDiffOn 𝕜 s) : ContDiffOn 𝕜 n f s ↔ (fo
rall m : Nat, m <= n -> Continuous…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `iteratedFDerivWithin_eq_equiv_comp`：iteratedFDerivWithin_eq_equiv_comp :
 iteratedFDerivWithin 𝕜 n f s = ContinuousMultilinearMap.piFieldEquiv 𝕜 (Fin n) 
F ∘ iteratedDerivWithin …
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
The property of being `C^n`, initially defined in terms of the Fréchet derivativ
e, can be
reformulated in terms of the one-dimensional derivative on sets with unique deri
vatives.
-/
theorem contDiffOn_iff_continuousOn_differentiableOn_deriv {n : ℕ∞} (hs : UniqueDiffOn 𝕜 s) :
    ContDiffOn 𝕜 n f s ↔ (∀ m : ℕ, (m : ℕ∞) ≤ n → ContinuousOn (iteratedDerivWithin m f s) s) ∧
      ∀ m : ℕ, (m : ℕ∞) < n → DifferentiableOn 𝕜 (iteratedDerivWithin m f s) s := by
  simp only [contDiffOn_iff_continuousOn_differentiableOn hs, iteratedFDerivWithin_eq_equiv_comp,
    LinearIsometryEquiv.comp_continuousOn_iff, LinearIsometryEquiv.comp_differentiableOn_iff]

/-- The property of being `C^n`, initially defined in terms of the Fréchet derivative, can be
reformulated in terms of the one-dimensional derivative on sets with unique derivatives. -/
/-
**contDiffOn_nat_iff_continuousOn_differentiableOn_deriv** 是 Mathlib 中的一个定理，位于命名
空间 ``。
形式化陈述：contDiffOn_nat_iff_continuousOn_differentiableOn_deriv {n : Nat} (hs : Uni
queDiffOn 𝕜 s) : ContDiffOn 𝕜 n f s ↔ (forall m : Nat, m <= n -> ContinuousOn (i
teratedDerivWithin m f s) s) ∧ forall m : Nat, m < n -> DifferentiableOn 𝕜 (iter
atedDerivWithin m f s) s
参数：hs : UniqueDiffOn 𝕜 s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `contDiffOn_iff_continuousOn_differentiableOn_deriv`：contDiffOn_iff_conti
nuousOn_differentiableOn_deriv {n : Nat∞} (hs : UniqueDiffOn 𝕜 s) : ContDiffOn 𝕜
 n f s ↔ (forall m : Nat, (m : Nat∞) <= …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LinearOrderedAddCommMonoidWithTop.toIsOrderedAddMonoid`：∀ {α : Type u_3}
 [self : LinearOrderedAddCommMonoidWithTop α], IsOrderedAddMonoid α
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
The property of being `C^n`, initially defined in terms of the Fréchet derivativ
e, can be
reformulated in terms of the one-dimensional derivative on sets with unique deri
vatives.
-/
theorem contDiffOn_nat_iff_continuousOn_differentiableOn_deriv {n : ℕ} (hs : UniqueDiffOn 𝕜 s) :
    ContDiffOn 𝕜 n f s ↔ (∀ m : ℕ, m ≤ n → ContinuousOn (iteratedDerivWithin m f s) s) ∧
      ∀ m : ℕ, m < n → DifferentiableOn 𝕜 (iteratedDerivWithin m f s) s := by
  rw [show n = ((n : ℕ∞) : ℕ∞ω) from rfl,
    contDiffOn_iff_continuousOn_differentiableOn_deriv hs]
  simp

/-- The `n+1`-th iterated derivative within a set with unique derivatives can be obtained by
differentiating the `n`-th iterated derivative. -/
/-
**iteratedDerivWithin_succ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedDerivWithin_succ : iteratedDerivWithin (n + 1) f s = derivWithin (
iteratedDerivWithin n f s) s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iteratedDerivWithin_eq_iteratedFDerivWithin`：iteratedDerivWithin_eq_iter
atedFDerivWithin : iteratedDerivWithin n f s x = (iteratedFDerivWithin 𝕜 n f s x
 : (Fin n -> 𝕜) -> F) fun _ : Fin…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `iteratedFDerivWithin_succ_apply_left`：iteratedFDerivWithin_succ_apply_le
ft {n : Nat} (m : Fin (n + 1) -> E) : (iteratedFDerivWithin 𝕜 (n + 1) f s x : (F
in (n + 1) -> E) -> F) m =…
· 使用定理 `iteratedFDerivWithin_eq_equiv_comp`：iteratedFDerivWithin_eq_equiv_comp :
 iteratedFDerivWithin 𝕜 n f s = ContinuousMultilinearMap.piFieldEquiv 𝕜 (Fin n) 
F ∘ iteratedDerivWithin …
· 使用定理 `LinearIsometryEquiv.comp_fderivWithin`：comp_fderivWithin {f : G -> E} {s
 : Set G} {x : G} (hxs : UniqueDiffWithinAt 𝕜 s x) : fderivWithin 𝕜 (iso ∘ f) s 
x = (iso : E ->L[𝕜] F).comp…
· 使用定理 `AccPt.uniqueDiffWithinAt`：∀ {𝕜 : Type u_1} [inst : NormedDivisionRing 𝕜]
 {s : Set 𝕜} {x : 𝕜},   AccPt x (Filter.principal s) → UniqueDiffWithinAt 𝕜 s x
· 使用定理 `derivWithin.eq_1`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜] {F :
 Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [inst_3 : Topo
logica…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.prod_const_one`：prod_const_one : (∏ _x in s, (1 : M)) = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `fderivWithin_zero_of_not_accPt`：fderivWithin_zero_of_not_accPt (h : ¬Acc
Pt x (𝓟 s)) : fderivWithin 𝕜 f s x = 0
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `ContinuousMultilinearMap.instIsZeroApplyForall`：∀ {R : Type u} {ι : Type
 v} {M₁ : ι → Type w₁} {M₂ : Type w₂} [inst : Semiring R]   [inst_1 : (i : ι) → 
AddCommMonoid (M₁ i)] [inst_2 : AddC…
· 使用定理 `derivWithin_zero_of_not_accPt`：derivWithin_zero_of_not_accPt (h : ¬AccPt
 x (𝓟 s)) : derivWithin f s x = 0

--- 原说明 ---
The `n+1`-th iterated derivative within a set with unique derivatives can be obt
ained by
differentiating the `n`-th iterated derivative.
-/
theorem iteratedDerivWithin_succ :
    iteratedDerivWithin (n + 1) f s = derivWithin (iteratedDerivWithin n f s) s := by
  ext x
  by_cases hxs : AccPt x (𝓟 s)
  · rw [iteratedDerivWithin_eq_iteratedFDerivWithin, iteratedFDerivWithin_succ_apply_left,
      iteratedFDerivWithin_eq_equiv_comp,
      LinearIsometryEquiv.comp_fderivWithin _ hxs.uniqueDiffWithinAt, derivWithin]
    change ((ContinuousMultilinearMap.mkPiRing 𝕜 (Fin n) ((fderivWithin 𝕜
      (iteratedDerivWithin n f s) s x : 𝕜 → F) 1) : (Fin n → 𝕜) → F) fun _ : Fin n => 1) =
      (fderivWithin 𝕜 (iteratedDerivWithin n f s) s x : 𝕜 → F) 1
    simp
  · simp [derivWithin_zero_of_not_accPt hxs, iteratedDerivWithin, iteratedFDerivWithin,
      fderivWithin_zero_of_not_accPt hxs]

/-- The `n`-th iterated derivative within a set with unique derivatives can be obtained by
iterating `n` times the differentiation operation. -/
/-
**iteratedDerivWithin_eq_iterate** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedDerivWithin_eq_iterate {x : 𝕜} : iteratedDerivWithin n f s x = (fu
n g : 𝕜 -> F => derivWithin g s)^[n] f x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `iteratedDerivWithin_zero`：iteratedDerivWithin_zero : iteratedDerivWithin
 0 f s = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iteratedDerivWithin_succ`：iteratedDerivWithin_succ : iteratedDerivWithin
 (n + 1) f s = derivWithin (iteratedDerivWithin n f s) s
· 使用定理 `Function.iterate_succ'`：iterate_succ' (n : Nat) : f^[n.succ] = f ∘ f^[n]
· 使用定理 `derivWithin_congr`：derivWithin_congr (hs : EqOn f₁ f s) (hx : f₁ x = f x
) : derivWithin f₁ s x = derivWithin f s x

--- 原说明 ---
The `n`-th iterated derivative within a set with unique derivatives can be obtai
ned by
iterating `n` times the differentiation operation.
-/
theorem iteratedDerivWithin_eq_iterate {x : 𝕜} :
    iteratedDerivWithin n f s x = (fun g : 𝕜 → F => derivWithin g s)^[n] f x := by
  induction n generalizing x with
  | zero => simp
  | succ n IH =>
    rw [iteratedDerivWithin_succ, Function.iterate_succ']
    exact derivWithin_congr (fun y hy => IH) IH

/-- The `n+1`-th iterated derivative within a set with unique derivatives can be obtained by
taking the `n`-th derivative of the derivative. -/
/-
**iteratedDerivWithin_succ'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedDerivWithin_succ' : iteratedDerivWithin (n + 1) f s = (iteratedDer
ivWithin n (derivWithin f s) s)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iteratedDerivWithin_eq_iterate`：iteratedDerivWithin_eq_iterate {x : 𝕜} :
 iteratedDerivWithin n f s x = (fun g : 𝕜 -> F => derivWithin g s)^[n] f x

--- 原说明 ---
The `n+1`-th iterated derivative within a set with unique derivatives can be obt
ained by
taking the `n`-th derivative of the derivative.
-/
theorem iteratedDerivWithin_succ' :
    iteratedDerivWithin (n + 1) f s = (iteratedDerivWithin n (derivWithin f s) s) := by
  ext x; rw [iteratedDerivWithin_eq_iterate, iteratedDerivWithin_eq_iterate]; rfl

/-- `C^{n + 1}` is equivalent to `C^n` and the `n`-th derivative being `C^1`. -/
/-
**contDiffOn_nat_succ_iff_contDiffOn_one_iteratedDerivWithin** 是 Mathlib 中的一个定理，
位于命名空间 ``。
形式化陈述：contDiffOn_nat_succ_iff_contDiffOn_one_iteratedDerivWithin {n : Nat} (hs :
 UniqueDiffOn 𝕜 s) : ContDiffOn 𝕜 (n + 1 : Nat) f s ↔ ContDiffOn 𝕜 n f s ∧ ContD
iffOn 𝕜 1 (iteratedDerivWithin n f s) s
参数：hs : UniqueDiffOn 𝕜 s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a

--- 原说明 ---
`C^{n + 1}` is equivalent to `C^n` and the `n`-th derivative being `C^1`.
-/
theorem contDiffOn_nat_succ_iff_contDiffOn_one_iteratedDerivWithin {n : ℕ}
    (hs : UniqueDiffOn 𝕜 s) : ContDiffOn 𝕜 (n + 1 : ℕ) f s ↔
      ContDiffOn 𝕜 n f s ∧ ContDiffOn 𝕜 1 (iteratedDerivWithin n f s) s := by
  simp only [contDiffOn_nat_iff_continuousOn_differentiableOn_deriv, hs,
    contDiffOn_one_iff_derivWithin, ← iteratedDerivWithin_succ]
  grind

/-! ### Properties of the iterated derivative on the whole space -/


/-
**iteratedDeriv_eq_iteratedFDeriv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedDeriv_eq_iteratedFDeriv : iteratedDeriv n f x = (iteratedFDeriv 𝕜 
n f x : (Fin n -> 𝕜) -> F) fun _ : Fin n => 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Properties of the iterated derivative on the whole space
-/
theorem iteratedDeriv_eq_iteratedFDeriv :
    iteratedDeriv n f x = (iteratedFDeriv 𝕜 n f x : (Fin n → 𝕜) → F) fun _ : Fin n => 1 :=
  rfl

/-- Write the iterated derivative as the composition of a continuous linear equiv and the iterated
Fréchet derivative -/
/-
**iteratedDeriv_eq_equiv_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedDeriv_eq_equiv_comp : iteratedDeriv n f = (ContinuousMultilinearMa
p.piFieldEquiv 𝕜 (Fin n) F).symm ∘ iteratedFDeriv 𝕜 n f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …

--- 原说明 ---
Write the iterated derivative as the composition of a continuous linear equiv an
d the iterated
Fréchet derivative
-/
theorem iteratedDeriv_eq_equiv_comp : iteratedDeriv n f =
    (ContinuousMultilinearMap.piFieldEquiv 𝕜 (Fin n) F).symm ∘ iteratedFDeriv 𝕜 n f := by
  ext x; rfl

/-- Write the iterated Fréchet derivative as the composition of a continuous linear equiv and the
iterated derivative. -/
/-
**iteratedFDeriv_eq_equiv_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedFDeriv_eq_equiv_comp : iteratedFDeriv 𝕜 n f = ContinuousMultilinea
rMap.piFieldEquiv 𝕜 (Fin n) F ∘ iteratedDeriv n f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iteratedDeriv_eq_equiv_comp`：iteratedDeriv_eq_equiv_comp : iteratedDeriv
 n f = (ContinuousMultilinearMap.piFieldEquiv 𝕜 (Fin n) F).symm ∘ iteratedFDeriv
 𝕜 n f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.comp_assoc`：comp_assoc (f : φ -> δ) (g : β -> φ) (h : α -> β) :
 (f ∘ g) ∘ h = f ∘ g ∘ h
· 使用定理 `LinearIsometryEquiv.self_comp_symm`：self_comp_symm : e ∘ e.symm = id
· 使用定理 `Function.id_comp`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β), id ∘ f = 
f

--- 原说明 ---
Write the iterated Fréchet derivative as the composition of a continuous linear 
equiv and the
iterated derivative.
-/
theorem iteratedFDeriv_eq_equiv_comp : iteratedFDeriv 𝕜 n f =
    ContinuousMultilinearMap.piFieldEquiv 𝕜 (Fin n) F ∘ iteratedDeriv n f := by
  rw [iteratedDeriv_eq_equiv_comp, ← Function.comp_assoc, LinearIsometryEquiv.self_comp_symm,
    Function.id_comp]

/-- The `n`-th Fréchet derivative applied to a vector `(m 0, ..., m (n-1))` is the derivative
multiplied by the product of the `m i`s. -/
/-
**iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod {m : Fin n -> 𝕜} : (iterate
dFDeriv 𝕜 n f x : (Fin n -> 𝕜) -> F) m = (∏ i, m i) • iteratedDeriv n f x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iteratedDeriv_eq_iteratedFDeriv`：iteratedDeriv_eq_iteratedFDeriv : itera
tedDeriv n f x = (iteratedFDeriv 𝕜 n f x : (Fin n -> 𝕜) -> F) fun _ : Fin n => 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousMultilinearMap.map_smul_univ`：map_smul_univ [Fintype ι] (c : ι
 -> R) (m : forall i, M₁ i) : (f fun i => c i • m i) = (∏ i, c i) • f m
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The `n`-th Fréchet derivative applied to a vector `(m 0, ..., m (n-1))` is the d
erivative
multiplied by the product of the `m i`s.
-/
theorem iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod {m : Fin n → 𝕜} :
    (iteratedFDeriv 𝕜 n f x : (Fin n → 𝕜) → F) m = (∏ i, m i) • iteratedDeriv n f x := by
  rw [iteratedDeriv_eq_iteratedFDeriv, ← ContinuousMultilinearMap.map_smul_univ]; simp
/-
**norm_iteratedFDeriv_eq_norm_iteratedDeriv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_iteratedFDeriv_eq_norm_iteratedDeriv : ‖iteratedFDeriv 𝕜 n f x‖ = ‖it
eratedDeriv n f x‖
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iteratedDeriv_eq_equiv_comp`：iteratedDeriv_eq_equiv_comp : iteratedDeriv
 n f = (ContinuousMultilinearMap.piFieldEquiv 𝕜 (Fin n) F).symm ∘ iteratedFDeriv
 𝕜 n f
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `LinearIsometryEquiv.norm_map`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type
 u_5} {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* 
R₂} {σ₂₁ : R₂ →+* …
-/
theorem norm_iteratedFDeriv_eq_norm_iteratedDeriv :
    ‖iteratedFDeriv 𝕜 n f x‖ = ‖iteratedDeriv n f x‖ := by
  rw [iteratedDeriv_eq_equiv_comp, Function.comp_apply, LinearIsometryEquiv.norm_map]

@[simp]
/-
**iteratedDeriv_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedDeriv_zero : iteratedDeriv 0 f = f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iteratedDeriv_zero : iteratedDeriv 0 f = f := by ext x; simp [iteratedDeriv]

@[simp]
/-
**iteratedDeriv_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedDeriv_one : iteratedDeriv 1 f = deriv f
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
· 使用定理 `iteratedFDeriv_one_apply`：iteratedFDeriv_one_apply (m : Fin 1 -> E) : it
eratedFDeriv 𝕜 1 f x m = fderiv 𝕜 f x (m 0)
· 使用定理 `fderiv_eq_smul_deriv`：fderiv_eq_smul_deriv (y : 𝕜) : (fderiv 𝕜 f x : 𝕜 -
> F) y = y • deriv f x
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iteratedDeriv_one : iteratedDeriv 1 f = deriv f := by ext x; simp [iteratedDeriv]

/-- The property of being `C^n`, initially defined in terms of the Fréchet derivative, can be
reformulated in terms of the one-dimensional derivative. -/
/-
**contDiff_iff_iteratedDeriv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiff_iff_iteratedDeriv {n : Nat∞} : ContDiff 𝕜 n f ↔ (forall m : Nat, 
(m : Nat∞) <= n -> Continuous (iteratedDeriv m f)) ∧ forall m : Nat, (m : Nat∞) 
< n -> Differentiable 𝕜 (iteratedDeriv m f)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `iteratedFDeriv_eq_equiv_comp`：iteratedFDeriv_eq_equiv_comp : iteratedFDe
riv 𝕜 n f = ContinuousMultilinearMap.piFieldEquiv 𝕜 (Fin n) F ∘ iteratedDeriv n 
f
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
The property of being `C^n`, initially defined in terms of the Fréchet derivativ
e, can be
reformulated in terms of the one-dimensional derivative.
-/
theorem contDiff_iff_iteratedDeriv {n : ℕ∞} : ContDiff 𝕜 n f ↔
    (∀ m : ℕ, (m : ℕ∞) ≤ n → Continuous (iteratedDeriv m f)) ∧
      ∀ m : ℕ, (m : ℕ∞) < n → Differentiable 𝕜 (iteratedDeriv m f) := by
  simp only [contDiff_iff_continuous_differentiable, iteratedFDeriv_eq_equiv_comp,
    LinearIsometryEquiv.comp_continuous_iff, LinearIsometryEquiv.comp_differentiable_iff]

/-- The property of being `C^n`, initially defined in terms of the Fréchet derivative, can be
reformulated in terms of the one-dimensional derivative. -/
/-
**contDiff_nat_iff_iteratedDeriv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiff_nat_iff_iteratedDeriv {n : Nat} : ContDiff 𝕜 n f ↔ (forall m : Na
t, m <= n -> Continuous (iteratedDeriv m f)) ∧ forall m : Nat, m < n -> Differen
tiable 𝕜 (iteratedDeriv m f)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithTop.coe_natCast`：∀ {α : Type u} [inst : AddMonoidWithOne α] (n : ℕ),
 ↑↑n = ↑n
· 使用定理 `contDiff_iff_iteratedDeriv`：contDiff_iff_iteratedDeriv {n : Nat∞} : Cont
Diff 𝕜 n f ↔ (forall m : Nat, (m : Nat∞) <= n -> Continuous (iteratedDeriv m f))
 ∧ forall m : Na…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LinearOrderedAddCommMonoidWithTop.toIsOrderedAddMonoid`：∀ {α : Type u_3}
 [self : LinearOrderedAddCommMonoidWithTop α], IsOrderedAddMonoid α
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
The property of being `C^n`, initially defined in terms of the Fréchet derivativ
e, can be
reformulated in terms of the one-dimensional derivative.
-/
theorem contDiff_nat_iff_iteratedDeriv {n : ℕ} : ContDiff 𝕜 n f ↔
    (∀ m : ℕ, m ≤ n → Continuous (iteratedDeriv m f)) ∧
      ∀ m : ℕ, m < n → Differentiable 𝕜 (iteratedDeriv m f) := by
  rw [← WithTop.coe_natCast, contDiff_iff_iteratedDeriv]
  simp

/-- To check that a function is `n` times continuously differentiable, it suffices to check that its
first `n` derivatives are differentiable. This is slightly too strong as the condition we
require on the `n`-th derivative is differentiability instead of continuity, but it has the
advantage of avoiding the discussion of continuity in the proof (and for `n = ∞` this is optimal).
-/
/-
**contDiff_of_differentiable_iteratedDeriv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiff_of_differentiable_iteratedDeriv {n : Nat∞} (h : forall m : Nat, (
m : Nat∞) <= n -> Differentiable 𝕜 (iteratedDeriv m f)) : ContDiff 𝕜 n f
参数：h : forall m : Nat, (m : Nat∞) <= n -> Differentiable 𝕜 (iteratedDeriv m f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `contDiff_iff_iteratedDeriv`：contDiff_iff_iteratedDeriv {n : Nat∞} : Cont
Diff 𝕜 n f ↔ (forall m : Nat, (m : Nat∞) <= n -> Continuous (iteratedDeriv m f))
 ∧ forall m : Na…
· 使用定理 `Differentiable.continuous`：Differentiable.continuous (h : Differentiable
 𝕜 f) : Continuous f
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b

--- 原说明 ---
To check that a function is `n` times continuously differentiable, it suffices t
o check that its
first `n` derivatives are differentiable. This is slightly too strong as the con
dition we
require on the `n`-th derivative is differentiability instead of continuity, but
 it has the
advantage of avoiding the discussion of continuity in the proof (and for `n = ∞`
 this is optimal).
-/
theorem contDiff_of_differentiable_iteratedDeriv {n : ℕ∞}
    (h : ∀ m : ℕ, (m : ℕ∞) ≤ n → Differentiable 𝕜 (iteratedDeriv m f)) : ContDiff 𝕜 n f :=
  contDiff_iff_iteratedDeriv.2 ⟨fun m hm => (h m hm).continuous, fun m hm => h m (le_of_lt hm)⟩
/-
**ContDiff.continuous_iteratedDeriv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiff.continuous_iteratedDeriv {n : Nat∞ω} (m : Nat) (h : ContDiff 𝕜 n 
f) (hmn : m <= n) : Continuous (iteratedDeriv m f)
参数：m : Nat；h : ContDiff 𝕜 n f；hmn : m <= n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `contDiff_iff_iteratedDeriv`：contDiff_iff_iteratedDeriv {n : Nat∞} : Cont
Diff 𝕜 n f ↔ (forall m : Nat, (m : Nat∞) <= n -> Continuous (iteratedDeriv m f))
 ∧ forall m : Na…
· 使用定理 `ContDiff.of_le`：ContDiff.of_le (h : ContDiff 𝕜 n f) (hmn : m <= n) : Con
tDiff 𝕜 m f
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem ContDiff.continuous_iteratedDeriv {n : ℕ∞ω} (m : ℕ) (h : ContDiff 𝕜 n f)
    (hmn : m ≤ n) : Continuous (iteratedDeriv m f) :=
  (contDiff_iff_iteratedDeriv.1 (h.of_le hmn)).1 m le_rfl

@[fun_prop]
/-
**ContDiff.continuous_iteratedDeriv'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiff.continuous_iteratedDeriv' (m : Nat) (h : ContDiff 𝕜 m f) : Contin
uous (iteratedDeriv m f)
参数：m : Nat；h : ContDiff 𝕜 m f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiff.continuous_iteratedDeriv`：ContDiff.continuous_iteratedDeriv {n 
: Nat∞ω} (m : Nat) (h : ContDiff 𝕜 n f) (hmn : m <= n) : Continuous (iteratedDer
iv m f)
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem ContDiff.continuous_iteratedDeriv' (m : ℕ) (h : ContDiff 𝕜 m f) :
    Continuous (iteratedDeriv m f) :=
  ContDiff.continuous_iteratedDeriv m h (le_refl _)
/-
**ContDiff.differentiable_iteratedDeriv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiff.differentiable_iteratedDeriv {n : Nat∞ω} (m : Nat) (h : ContDiff 
𝕜 n f) (hmn : m < n) : Differentiable 𝕜 (iteratedDeriv m f)
参数：m : Nat；h : ContDiff 𝕜 n f；hmn : m < n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `contDiff_iff_iteratedDeriv`：contDiff_iff_iteratedDeriv {n : Nat∞} : Cont
Diff 𝕜 n f ↔ (forall m : Nat, (m : Nat∞) <= n -> Continuous (iteratedDeriv m f))
 ∧ forall m : Na…
· 使用定理 `ContDiff.of_le`：ContDiff.of_le (h : ContDiff 𝕜 n f) (hmn : m <= n) : Con
tDiff 𝕜 m f
· 使用引理 `ENat.add_one_natCast_le_withTop_of_lt`：add_one_natCast_le_withTop_of_lt 
{m : Nat} {n : WithTop Nat∞} (h : m < n) : (m + 1 : Nat) <= n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LinearOrderedAddCommMonoidWithTop.toIsOrderedAddMonoid`：∀ {α : Type u_3}
 [self : LinearOrderedAddCommMonoidWithTop α], IsOrderedAddMonoid α
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用引理 `lt_add_one`：lt_add_one [One α] [AddZeroClass α] [PartialOrder α] [ZeroLE
OneClass α] [NeZero (1 : α)] [AddLeftStrictMono α] (a : α) : a < a + 1
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
-/
theorem ContDiff.differentiable_iteratedDeriv {n : ℕ∞ω} (m : ℕ) (h : ContDiff 𝕜 n f)
    (hmn : m < n) : Differentiable 𝕜 (iteratedDeriv m f) :=
  (contDiff_iff_iteratedDeriv.1 (h.of_le (ENat.add_one_natCast_le_withTop_of_lt hmn))).2 m
    (mod_cast (lt_add_one m))

@[fun_prop]
/-
**ContDiff.differentiable_iteratedDeriv'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContDiff.differentiable_iteratedDeriv' (m : Nat) (h : ContDiff 𝕜 (m + 1) f
) : Differentiable 𝕜 (iteratedDeriv m f)
参数：m : Nat；h : ContDiff 𝕜 (m + 1) f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiff.differentiable_iteratedDeriv`：ContDiff.differentiable_iteratedD
eriv {n : Nat∞ω} (m : Nat) (h : ContDiff 𝕜 n f) (hmn : m < n) : Differentiable 𝕜
 (iteratedDeriv m f)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_lt`：cast_lt : (m : α) < n ↔ m < n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LinearOrderedAddCommMonoidWithTop.toIsOrderedAddMonoid`：∀ {α : Type u_3}
 [self : LinearOrderedAddCommMonoidWithTop α], IsOrderedAddMonoid α
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ
-/
theorem ContDiff.differentiable_iteratedDeriv' (m : ℕ) (h : ContDiff 𝕜 (m + 1) f) :
    Differentiable 𝕜 (iteratedDeriv m f) :=
  h.differentiable_iteratedDeriv m (Nat.cast_lt.mpr m.lt_succ_self)

/-- The `n+1`-th iterated derivative can be obtained by differentiating the `n`-th
iterated derivative. -/
/-
**iteratedDeriv_succ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedDeriv_succ : iteratedDeriv (n + 1) f = deriv (iteratedDeriv n f)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `iteratedDerivWithin_univ`：iteratedDerivWithin_univ : iteratedDerivWithin
 n f univ = iteratedDeriv n f
· 使用定理 `derivWithin_univ`：derivWithin_univ : derivWithin f univ = deriv f
· 使用定理 `iteratedDerivWithin_succ`：iteratedDerivWithin_succ : iteratedDerivWithin
 (n + 1) f s = derivWithin (iteratedDerivWithin n f s) s

--- 原说明 ---
The `n+1`-th iterated derivative can be obtained by differentiating the `n`-th
iterated derivative.
-/
theorem iteratedDeriv_succ : iteratedDeriv (n + 1) f = deriv (iteratedDeriv n f) := by
  rw [← iteratedDerivWithin_univ, ← iteratedDerivWithin_univ, ← derivWithin_univ]
  exact iteratedDerivWithin_succ

/-- The `n`-th iterated derivative can be obtained by iterating `n` times the
differentiation operation. -/
/-
**iteratedDeriv_eq_iterate** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedDeriv_eq_iterate : iteratedDeriv n f = deriv^[n] f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `iteratedDerivWithin_univ`：iteratedDerivWithin_univ : iteratedDerivWithin
 n f univ = iteratedDeriv n f
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `derivWithin_univ`：derivWithin_univ : derivWithin f univ = deriv f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iteratedDerivWithin_eq_iterate`：iteratedDerivWithin_eq_iterate {x : 𝕜} :
 iteratedDerivWithin n f s x = (fun g : 𝕜 -> F => derivWithin g s)^[n] f x

--- 原说明 ---
The `n`-th iterated derivative can be obtained by iterating `n` times the
differentiation operation.
-/
theorem iteratedDeriv_eq_iterate : iteratedDeriv n f = deriv^[n] f := by
  ext x
  rw [← iteratedDerivWithin_univ]
  convert! iteratedDerivWithin_eq_iterate (F := F)
  simp [derivWithin_univ]
/-
**iteratedDerivWithin_of_isOpen** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedDerivWithin_of_isOpen (hs : IsOpen s) : Set.EqOn (iteratedDerivWit
hin n f s) (iteratedDeriv n f) s
参数：hs : IsOpen s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iteratedFDerivWithin_of_isOpen`：iteratedFDerivWithin_of_isOpen (n : Nat)
 (hs : IsOpen s) : EqOn (iteratedFDerivWithin 𝕜 n f s) (iteratedFDeriv 𝕜 n f) s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iteratedDerivWithin_of_isOpen (hs : IsOpen s) :
    Set.EqOn (iteratedDerivWithin n f s) (iteratedDeriv n f) s := by
  intro x hx
  simp_rw [iteratedDerivWithin, iteratedDeriv, iteratedFDerivWithin_of_isOpen n hs hx]
/-
**iteratedDerivWithin_congr_right_of_isOpen** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedDerivWithin_congr_right_of_isOpen (f : 𝕜 -> F) (n : Nat) {s t : Se
t 𝕜} (hs : IsOpen s) (ht : IsOpen t) : (s inter t).EqOn (iteratedDerivWithin n f
 s) (iteratedDerivWithin n f t)
参数：f : 𝕜 -> F；n : Nat；hs : IsOpen s；ht : IsOpen t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iteratedDerivWithin_of_isOpen`：iteratedDerivWithin_of_isOpen (hs : IsOpe
n s) : Set.EqOn (iteratedDerivWithin n f s) (iteratedDeriv n f) s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem iteratedDerivWithin_congr_right_of_isOpen (f : 𝕜 → F) (n : ℕ) {s t : Set 𝕜} (hs : IsOpen s)
    (ht : IsOpen t) : (s ∩ t).EqOn (iteratedDerivWithin n f s) (iteratedDerivWithin n f t) := by
  intro r hr
  rw [iteratedDerivWithin_of_isOpen hs hr.1, iteratedDerivWithin_of_isOpen ht hr.2]
/-
**iteratedDerivWithin_of_isOpen_eq_iterate** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedDerivWithin_of_isOpen_eq_iterate (hs : IsOpen s) : EqOn (iteratedD
erivWithin n f s) (deriv^[n] f) s
参数：hs : IsOpen s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.EqOn.trans`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f₁ f₂ f₃ : 
α → β}, Set.EqOn f₁ f₂ s → Set.EqOn f₂ f₃ s → Set.EqOn f₁ f₃ s
· 使用定理 `iteratedDerivWithin_of_isOpen`：iteratedDerivWithin_of_isOpen (hs : IsOpe
n s) : Set.EqOn (iteratedDerivWithin n f s) (iteratedDeriv n f) s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iteratedDeriv_eq_iterate`：iteratedDeriv_eq_iterate : iteratedDeriv n f =
 deriv^[n] f
· 使用定理 `Set.eqOn_refl`：eqOn_refl (f : α -> β) (s : Set α) : EqOn f f s
-/
theorem iteratedDerivWithin_of_isOpen_eq_iterate (hs : IsOpen s) :
    EqOn (iteratedDerivWithin n f s) (deriv^[n] f) s := by
  apply Set.EqOn.trans (iteratedDerivWithin_of_isOpen hs)
  rw [iteratedDeriv_eq_iterate]
  exact Set.eqOn_refl _ _

/-- The `n+1`-th iterated derivative can be obtained by taking the `n`-th derivative of the
derivative. -/
/-
**iteratedDeriv_succ'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedDeriv_succ' : iteratedDeriv (n + 1) f = iteratedDeriv n (deriv f)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iteratedDeriv_eq_iterate`：iteratedDeriv_eq_iterate : iteratedDeriv n f =
 deriv^[n] f
· 使用定理 `Function.iterate_succ_apply`：iterate_succ_apply (n : Nat) (x : α) : f^[n
.succ] x = f^[n] (f x)

--- 原说明 ---
The `n+1`-th iterated derivative can be obtained by taking the `n`-th derivative
 of the
derivative.
-/
theorem iteratedDeriv_succ' : iteratedDeriv (n + 1) f = iteratedDeriv n (deriv f) := by
  rw [iteratedDeriv_eq_iterate, iteratedDeriv_eq_iterate, Function.iterate_succ_apply]
/-
**AnalyticAt.hasFPowerSeriesAt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AnalyticAt.hasFPowerSeriesAt {𝕜 : Type*} [NontriviallyNormedField 𝕜] [Comp
leteSpace 𝕜] [CharZero 𝕜] {f : 𝕜 -> 𝕜} {x : 𝕜} (h : AnalyticAt 𝕜 f x) : HasFPowe
rSeriesAt f (FormalMultilinearSeries.ofScalars 𝕜 (fun n => iteratedDeriv n f x /
 n.factorial)) x
参数：h : AnalyticAt 𝕜 f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FormalMultilinearSeries.ext`：∀ {𝕜 : Type u} {E : Type v} {F : Type w} [i
nst : Semiring 𝕜] [inst_1 : AddCommMonoid E] [inst_2 : _root_.Module 𝕜 E]   [ins
t_3 : Topological…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `SMulCommClass.continuousConstSMul`：∀ {R : Type u_6} {A : Type u_7} [inst
 : Monoid A] [inst_1 : SMul R A] [SMulCommClass R A A]   [inst_3 : TopologicalSp
ace A] [SeparatelyConti…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `ContinuousMultilinearMap.ext_ring`：ext_ring [Finite ι] [TopologicalSpace
 R] ⦃f g : ContinuousMultilinearMap R (fun _ : ι => R) M₂⦄ (h : f (fun _ => 1) =
 g (fun _ => 1)) : f = …
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `HasFPowerSeriesOnBall.factorial_smul`：factorial_smul (n : Nat) : n ! • p
 n (fun _ => y) = iteratedFDeriv 𝕜 n f x (fun _ => y)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FormalMultilinearSeries.apply_eq_prod_smul_coeff`：apply_eq_prod_smul_coe
ff : p n y = (∏ i, y i) • p.coeff n
· 使用引理 `FormalMultilinearSeries.coeff_ofScalars`：coeff_ofScalars {𝕜 : Type*} [No
ntriviallyNormedField 𝕜] {p : Nat -> 𝕜} {n : Nat} : (FormalMultilinearSeries.ofS
calars 𝕜 p).coeff n = p n
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `Field.isDomain`：∀ {K : Type u_1} [inst : Field K], IsDomain K
· 使用引理 `div_eq_iff`：div_eq_iff (hb : b != 0) : a / b = c ↔ a = c * b
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Nat.factorial_pos`：∀ (n : ℕ), 0 < n.factorial
（共 39 条，此处仅展示前 30 条）
-/
lemma AnalyticAt.hasFPowerSeriesAt {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    [CharZero 𝕜] {f : 𝕜 → 𝕜} {x : 𝕜} (h : AnalyticAt 𝕜 f x) :
    HasFPowerSeriesAt f
      (FormalMultilinearSeries.ofScalars 𝕜 (fun n ↦ iteratedDeriv n f x / n.factorial)) x := by
  obtain ⟨p, hp⟩ := h
  convert! hp
  obtain ⟨r, hpr⟩ := hp
  ext n
  have h_fact_smul := hpr.factorial_smul 1
  simp only [FormalMultilinearSeries.apply_eq_prod_smul_coeff, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, nsmul_eq_mul, one_pow, one_mul] at h_fact_smul
  simp only [FormalMultilinearSeries.apply_eq_prod_smul_coeff,
    FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul, mul_eq_mul_left_iff]
  left
  rw [div_eq_iff, mul_comm, h_fact_smul, ← iteratedDeriv_eq_iteratedFDeriv]
  norm_cast
  positivity
/-
**iteratedDeriv_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedDeriv_const {n : Nat} {c : F} {x : 𝕜} : iteratedDeriv n (fun _ => 
c) x = if n = 0 then c else 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `iteratedDeriv_zero`：iteratedDeriv_zero : iteratedDeriv 0 f = f
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iteratedDeriv_succ'`：iteratedDeriv_succ' : iteratedDeriv (n + 1) f = ite
ratedDeriv n (deriv f)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `deriv_const'`：deriv_const' : (deriv fun _ : 𝕜 => c) = fun _ => 0
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
-/
theorem iteratedDeriv_const {n : ℕ} {c : F} {x : 𝕜} :
    iteratedDeriv n (fun _ ↦ c) x = if n = 0 then c else 0 := by
  induction n generalizing c with
  | zero => simp
  | succ n h => simp [iteratedDeriv_succ', h]
/-
**iteratedDerivWithin_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iteratedDerivWithin_const {n : Nat} {c : F} {s : Set 𝕜} {x : 𝕜} : iterated
DerivWithin n (fun _ => c) s x = if n = 0 then c else 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `iteratedDerivWithin_zero`：iteratedDerivWithin_zero : iteratedDerivWithin
 0 f s = f
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iteratedDerivWithin_succ'`：iteratedDerivWithin_succ' : iteratedDerivWith
in (n + 1) f s = (iteratedDerivWithin n (derivWithin f s) s)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `derivWithin_fun_const`：derivWithin_fun_const : derivWithin (fun _ => c) 
s = 0
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
-/
theorem iteratedDerivWithin_const {n : ℕ} {c : F} {s : Set 𝕜} {x : 𝕜} :
    iteratedDerivWithin n (fun _ ↦ c) s x = if n = 0 then c else 0 := by
  induction n generalizing c with
  | zero => simp
  | succ n h => simp [iteratedDerivWithin_succ', Pi.zero_def, h]

@[simp]
/-
**iteratedDeriv_fun_const_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：iteratedDeriv_fun_const_zero : iteratedDeriv n (fun _ => 0) x = (0 : F)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
· 使用定理 `iteratedDeriv_const`：iteratedDeriv_const {n : Nat} {c : F} {x : 𝕜} : ite
ratedDeriv n (fun _ => c) x = if n = 0 then c else 0
-/
lemma iteratedDeriv_fun_const_zero : iteratedDeriv n (fun _ ↦ 0) x = (0 : F) := by
  simpa using @iteratedDeriv_const 𝕜 _ F _ _ n 0

@[simp]
/-
**iteratedDeriv_const_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：iteratedDeriv_const_zero : iteratedDeriv n (0 : 𝕜 -> F) x = (0 : F)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `iteratedDeriv_fun_const_zero`：iteratedDeriv_fun_const_zero : iteratedDer
iv n (fun _ => 0) x = (0 : F)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma iteratedDeriv_const_zero : iteratedDeriv n (0 : 𝕜 → F) x = (0 : F) := by
  simp [Pi.zero_def]

@[simp]
/-
**iteratedDerivWithin_fun_const_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：iteratedDerivWithin_fun_const_zero {s : Set 𝕜} : iteratedDerivWithin n (fu
n _ => 0) s x = (0 : F)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
· 使用定理 `iteratedDerivWithin_const`：iteratedDerivWithin_const {n : Nat} {c : F} {
s : Set 𝕜} {x : 𝕜} : iteratedDerivWithin n (fun _ => c) s x = if n = 0 then c el
se 0
-/
lemma iteratedDerivWithin_fun_const_zero {s : Set 𝕜} :
    iteratedDerivWithin n (fun _ ↦ 0) s x = (0 : F) := by
  simpa using @iteratedDerivWithin_const 𝕜 _ F _ _ n 0

@[simp]
/-
**iteratedDerivWithin_const_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：iteratedDerivWithin_const_zero {s : Set 𝕜} : iteratedDerivWithin n (0 : 𝕜 
-> F) s x = (0 : F)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `iteratedDerivWithin_fun_const_zero`：iteratedDerivWithin_fun_const_zero {
s : Set 𝕜} : iteratedDerivWithin n (fun _ => 0) s x = (0 : F)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma iteratedDerivWithin_const_zero {s : Set 𝕜} :
    iteratedDerivWithin n (0 : 𝕜 → F) s x = (0 : F) := by
  simp [Pi.zero_def]

/-- `C^{n + 1}` is equivalent to `C^n` and the `n`-th derivative being `C^1`. -/
/-
**contDiff_nat_succ_iff_contDiff_one_iteratedDeriv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiff_nat_succ_iff_contDiff_one_iteratedDeriv {n : Nat} : ContDiff 𝕜 (n
 + 1 : Nat) f ↔ ContDiff 𝕜 n f ∧ ContDiff 𝕜 1 (iteratedDeriv n f)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c

--- 原说明 ---
`C^{n + 1}` is equivalent to `C^n` and the `n`-th derivative being `C^1`.
-/
theorem contDiff_nat_succ_iff_contDiff_one_iteratedDeriv {n : ℕ} : ContDiff 𝕜 (n + 1 : ℕ) f ↔
    ContDiff 𝕜 n f ∧ ContDiff 𝕜 1 (iteratedDeriv n f) := by
  simp only [contDiff_nat_iff_iteratedDeriv, contDiff_one_iff_deriv, ← iteratedDeriv_succ]
  grind
