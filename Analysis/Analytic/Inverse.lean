/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Analytic.Composition
public import Mathlib.Analysis.Analytic.Linear
public import Mathlib.Tactic.Positivity

/-!

# Inverse of analytic functions

We construct the left and right inverse of a formal multilinear series with invertible linear term,
we prove that they coincide and study their properties (notably convergence). We deduce that the
inverse of an analytic open partial homeomorphism is analytic.

## Main statements

* `p.leftInv i x`: the formal left inverse of the formal multilinear series `p`, with constant
  coefficient `x`, for `i : E ≃L[𝕜] F` which coincides with `p₁`.
* `p.rightInv i x`: the formal right inverse of the formal multilinear series `p`, with constant
  coefficient `x`, for `i : E ≃L[𝕜] F` which coincides with `p₁`.
* `p.leftInv_comp` says that `p.leftInv i x` is indeed a left inverse to `p` when `p₁ = i`.
* `p.rightInv_comp` says that `p.rightInv i x` is indeed a right inverse to `p` when `p₁ = i`.
* `p.leftInv_eq_rightInv`: the two inverses coincide.
* `p.radius_rightInv_pos_of_radius_pos`: if a power series has a positive radius of convergence,
  then so does its inverse.

* `OpenPartialHomeomorph.hasFPowerSeriesAt_symm` shows that, if an open partial homeomorph has a
  power series `p` at a point, with invertible linear part, then the inverse also has a power series
  at the image point, given by `p.leftInv`.
-/

@[expose] public section

open scoped Topology ENNReal

open Finset Filter

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]

namespace FormalMultilinearSeries

/-! ### The left inverse of a formal multilinear series -/


/-- The left inverse of a formal multilinear series, where the `n`-th term is defined inductively
in terms of the previous ones to make sure that `(leftInv p i) ∘ p = id`. For this, the linear term
`p₁` in `p` should be invertible. In the definition, `i` is a linear isomorphism that should
coincide with `p₁`, so that one can use its inverse in the construction. The definition does not
use that `i = p₁`, but proofs that the definition is well-behaved do.

The `n`-th term in `q ∘ p` is `∑ qₖ (p_{j₁}, ..., p_{jₖ})` over `j₁ + ... + jₖ = n`. In this
expression, `qₙ` appears only once, in `qₙ (p₁, ..., p₁)`. We adjust the definition so that this
term compensates the rest of the sum, using `i⁻¹` as an inverse to `p₁`.

These formulas only make sense when the constant term `p₀` vanishes. The definition we give is
general, but it ignores the value of `p₀`.
-/
/-
**FormalMultilinearSeries.leftInv** 是 Mathlib 中的一个定义，位于命名空间 `FormalMultilinearSe
ries`。
形式化陈述：{𝕜 : Type u_1} →   [inst : NontriviallyNormedField 𝕜] →     {E : Type u_2}
 →       [inst_1 : NormedAddCommGroup E] →         [inst_2 : NormedSpace 𝕜 E] → 
          {F : Type u_3} →             [inst_3 : NormedAddCommGroup F] →        
       [inst_4 : NormedSpace 𝕜 F] →                 FormalMultilinearSeries 𝕜 E 
F → (E ≃L[𝕜] F) → E → FormalMultilinearSeries 𝕜 F E
参数：E ≃L[𝕜] F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The left inverse of a formal multilinear series, where the `n`-th term is define
d inductively
in terms of the previous ones to make sure that `(leftInv p i) ∘ p = id`. For th
is, the linear term
`p₁` in `p` should be invertible. In the definition, `i` is a linear isomorphism
 that should
coincide with `p₁`, so that one can use its inverse in the construction. The def
inition does not
use that `i = p₁`, but proofs that the definition is well-behaved do.

The `n`-th term in `q ∘ p` is `∑ qₖ (p_{j₁}, ..., p_{jₖ})` over `j₁ + ... + jₖ =
 n`. In this
expression, `qₙ` appears only once, in `qₙ (p₁, ..., p₁)`. We adjust the definit
ion so that this
term compensates the rest of the sum, using `i⁻¹` as an inverse to `p₁`.

These formulas only make sense when the constant term `p₀` vanishes. The definit
ion we give is
general, but it ignores the value of `p₀`.
-/
noncomputable def leftInv (p : FormalMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F) (x : E) :
    FormalMultilinearSeries 𝕜 F E
  | 0 => ContinuousMultilinearMap.uncurry0 𝕜 _ x
  | 1 => (continuousMultilinearCurryFin1 𝕜 F E).symm i.symm
  | n + 2 =>
    -∑ c : { c : Composition (n + 2) // c.length < n + 2 },
        (leftInv p i x (c : Composition (n + 2)).length).compAlongComposition
          (p.compContinuousLinearMap i.symm) c

@[simp]
/-
**FormalMultilinearSeries.leftInv_coeff_zero** 是 Mathlib 中的一个定理，位于命名空间 `FormalMu
ltilinearSeries`。
形式化陈述：leftInv_coeff_zero (p : FormalMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F) (x 
: E) : p.leftInv i x 0 = ContinuousMultilinearMap.uncurry0 𝕜 _ x
参数：p : FormalMultilinearSeries 𝕜 E F；i : E ≃L[𝕜] F；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FormalMultilinearSeries.leftInv.eq_1`：∀ {𝕜 : Type u_1} [inst : Nontrivia
llyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Nor
medSpace 𝕜 E] {F : Type u_…
-/
theorem leftInv_coeff_zero (p : FormalMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F) (x : E) :
    p.leftInv i x 0 = ContinuousMultilinearMap.uncurry0 𝕜 _ x := by rw [leftInv]

@[simp]
/-
**FormalMultilinearSeries.leftInv_coeff_one** 是 Mathlib 中的一个定理，位于命名空间 `FormalMul
tilinearSeries`。
形式化陈述：leftInv_coeff_one (p : FormalMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F) (x :
 E) : p.leftInv i x 1 = (continuousMultilinearCurryFin1 𝕜 F E).symm i.symm
参数：p : FormalMultilinearSeries 𝕜 E F；i : E ≃L[𝕜] F；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FormalMultilinearSeries.leftInv.eq_2`：∀ {𝕜 : Type u_1} [inst : Nontrivia
llyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Nor
medSpace 𝕜 E] {F : Type u_…
-/
theorem leftInv_coeff_one (p : FormalMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F) (x : E) :
    p.leftInv i x 1 = (continuousMultilinearCurryFin1 𝕜 F E).symm i.symm := by rw [leftInv]

/-- The left inverse does not depend on the zeroth coefficient of a formal multilinear
series. -/
/-
**FormalMultilinearSeries.leftInv_removeZero** 是 Mathlib 中的一个定理，位于命名空间 `FormalMu
ltilinearSeries`。
形式化陈述：leftInv_removeZero (p : FormalMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F) (x 
: E) : p.removeZero.leftInv i x = p.leftInv i x
参数：p : FormalMultilinearSeries 𝕜 E F；i : E ≃L[𝕜] F；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `FormalMultilinearSeries.ext`：∀ {𝕜 : Type u} {E : Type v} {F : Type w} [i
nst : Semiring 𝕜] [inst_1 : AddCommMonoid E] [inst_2 : _root_.Module 𝕜 E]   [ins
t_3 : Topological…
· 使用定理 `Nat.strong_induction_on`：∀ {p : ℕ → Prop} (n : ℕ), (∀ (n : ℕ), (∀ m < n,
 p m) → p n) → p n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FormalMultilinearSeries.leftInv_coeff_zero`：leftInv_coeff_zero (p : Form
alMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F) (x : E) : p.leftInv i x 0 = Continuou
sMultilinearMap.uncurry0 𝕜 _ x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `FormalMultilinearSeries.leftInv_coeff_one`：leftInv_coeff_one (p : Formal
MultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F) (x : E) : p.leftInv i x 1 = (continuous
MultilinearCurryFin1 𝕜 F E).sym…
· 使用定理 `FormalMultilinearSeries.leftInv.eq_3`：∀ {𝕜 : Type u_1} [inst : Nontrivia
llyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Nor
medSpace 𝕜 E] {F : Type u_…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `ContinuousMultilinearMap.ext`：ext {f f' : ContinuousMultilinearMap R M₁ 
M₂} (H : forall x, f x = f' x) : f = f'
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `FormalMultilinearSeries.compContinuousLinearMap_applyComposition`：compCo
ntinuousLinearMap_applyComposition {n : Nat} (p : FormalMultilinearSeries 𝕜 F G)
 (f : E ->L[𝕜] F) (c : Composition n) (v : Fin n -> E)…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `FormalMultilinearSeries.removeZero_applyComposition`：removeZero_applyCom
position (p : FormalMultilinearSeries 𝕜 E F) {n : Nat} (c : Composition n) : p.r
emoveZero.applyComposition c = p.applyCom…

--- 原说明 ---
The left inverse does not depend on the zeroth coefficient of a formal multiline
ar
series.
-/
theorem leftInv_removeZero (p : FormalMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F) (x : E) :
    p.removeZero.leftInv i x = p.leftInv i x := by
  ext1 n
  induction n using Nat.strong_induction_on with | _ n IH
  match n with
  | 0 => simp -- if one replaces `simp` with `refl`, the proof times out in the kernel.
  | 1 => simp -- TODO: why?
  | n + 2 =>
    simp only [leftInv, neg_inj]
    refine Finset.sum_congr rfl fun c cuniv => ?_
    rcases c with ⟨c, hc⟩
    ext v
    simp [IH _ hc]

/-- The left inverse to a formal multilinear series is indeed a left inverse, provided its linear
term is invertible. -/
/-
**FormalMultilinearSeries.leftInv_comp** 是 Mathlib 中的一个定理，位于命名空间 `FormalMultilin
earSeries`。
形式化陈述：leftInv_comp (p : FormalMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F) (x : E) (
h : p 1 = (continuousMultilinearCurryFin1 𝕜 E F).symm i) : (leftInv p i x).comp 
p = id 𝕜 E x
参数：p : FormalMultilinearSeries 𝕜 E F；i : E ≃L[𝕜] F；x : E；h : p 1 = (continuousMu
ltilinearCurryFin1 𝕜 E F).symm i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `FormalMultilinearSeries.ext`：∀ {𝕜 : Type u} {E : Type v} {F : Type w} [i
nst : Semiring 𝕜] [inst_1 : AddCommMonoid E] [inst_2 : _root_.Module 𝕜 E]   [ins
t_3 : Topological…
· 使用定理 `ContinuousMultilinearMap.ext`：ext {f f' : ContinuousMultilinearMap R M₁ 
M₂} (H : forall x, f x = f' x) : f = f'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FormalMultilinearSeries.comp_coeff_zero'`：comp_coeff_zero' (q : FormalMu
ltilinearSeries 𝕜 F G) (p : FormalMultilinearSeries 𝕜 E F) (v : Fin 0 -> E) : (q
.comp p) 0 v = q 0 fun _i => 0
· 使用定理 `FormalMultilinearSeries.leftInv_coeff_zero`：leftInv_coeff_zero (p : Form
alMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F) (x : E) : p.leftInv i x 0 = Continuou
sMultilinearMap.uncurry0 𝕜 _ x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `FormalMultilinearSeries.comp_coeff_one`：comp_coeff_one (q : FormalMultil
inearSeries 𝕜 F G) (p : FormalMultilinearSeries 𝕜 E F) (v : Fin 1 -> E) : (q.com
p p) 1 v = q 1 fun _i => p 1…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `FormalMultilinearSeries.leftInv_coeff_one`：leftInv_coeff_one (p : Formal
MultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F) (x : E) : p.leftInv i x 1 = (continuous
MultilinearCurryFin1 𝕜 F E).sym…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ContinuousLinearEquiv.symm_apply_apply`：symm_apply_apply (e : M₁ ≃SL[σ₁₂
] M₂) (b : M₁) : e.symm (e b) = b
· 使用定理 `Finset.Subset.antisymm`：∀ {α : Type u_1} {s₁ s₂ : Finset α}, s₁ ⊆ s₂ → s
₂ ⊆ s₁ → s₁ = s₂
· 使用定理 `Set.toFinset_ofPred`：toFinset_ofPred [Fintype α] (p : α -> Prop) [Decida
blePred p] [Fintype { x | p x }] : Set.toFinset {x | p x} = Finset.univ.filter p
· 使用引理 `Finset.union_singleton`：union_singleton (x : α) (s : Finset α) : s union
 {x} = insert x s
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Composition.eq_ones_iff_le_length`：eq_ones_iff_le_length {c : Compositio
n n} : c = ones n ↔ n <= c.length
· 使用定理 `Composition.ones_length`：ones_length (n : Nat) : (ones n).length = n
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
（共 63 条，此处仅展示前 30 条）

--- 原说明 ---
The left inverse to a formal multilinear series is indeed a left inverse, provid
ed its linear
term is invertible.
-/
theorem leftInv_comp (p : FormalMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F) (x : E)
    (h : p 1 = (continuousMultilinearCurryFin1 𝕜 E F).symm i) :
    (leftInv p i x).comp p = id 𝕜 E x := by
  ext n v
  match n with
  | 0 =>
    simp only [comp_coeff_zero', leftInv_coeff_zero, ContinuousMultilinearMap.uncurry0_apply,
      id_apply_zero]
  | 1 =>
    simp only [leftInv_coeff_one, comp_coeff_one, h, id_apply_one, ContinuousLinearEquiv.coe_apply,
      ContinuousLinearEquiv.symm_apply_apply, continuousMultilinearCurryFin1_symm_apply]
  | n + 2 =>
    have A :
      (Finset.univ : Finset (Composition (n + 2))) =
        {c | Composition.length c < n + 2}.toFinset ∪ {Composition.ones (n + 2)} := by
      refine Subset.antisymm (fun c _ => ?_) (subset_univ _)
      by_cases! h : c.length < n + 2
      · simp [h]
      · simp [Composition.eq_ones_iff_le_length.2 h]
    have B :
      Disjoint ({c | Composition.length c < n + 2} : Set (Composition (n + 2))).toFinset
        {Composition.ones (n + 2)} := by
      simp
    have C :
      ((p.leftInv i x (Composition.ones (n + 2)).length)
          fun j : Fin (Composition.ones n.succ.succ).length =>
          p 1 fun _ => v ((Fin.castLE (Composition.length_le _)) j)) =
        p.leftInv i x (n + 2) fun j : Fin (n + 2) => p 1 fun _ => v j := by
      apply FormalMultilinearSeries.congr _ (Composition.ones_length _) fun j hj1 hj2 => ?_
      exact FormalMultilinearSeries.congr _ rfl fun k _ _ => by congr
    have D :
      (p.leftInv i x (n + 2) fun j : Fin (n + 2) => p 1 fun _ => v j) =
        -∑ c ∈ {c : Composition (n + 2) | c.length < n + 2}.toFinset,
            (p.leftInv i x c.length) (p.applyComposition c v) := by
      simp only [leftInv, _root_.neg_apply, neg_inj, _root_.sum_apply]
      convert!
        (sum_toFinset_eq_subtype (fun c : Composition (n + 2) => c.length < n + 2)
              (fun c : Composition (n + 2) =>
                (ContinuousMultilinearMap.compAlongComposition
                    (p.compContinuousLinearMap (i.symm : F →L[𝕜] E)) c (p.leftInv i x c.length))
                  fun j : Fin (n + 2) => p 1 fun _ : Fin 1 => v j)).symm.trans
          _
      simp only [compContinuousLinearMap_applyComposition,
        ContinuousMultilinearMap.compAlongComposition_apply]
      congr
      ext c
      congr
      ext k
      simp [h]
    simp [FormalMultilinearSeries.comp, A, Finset.sum_union B,
      applyComposition_ones, C, D, -Set.toFinset_ofPred, -Finset.union_singleton]

/-! ### The right inverse of a formal multilinear series -/


/-- The right inverse of a formal multilinear series, where the `n`-th term is defined inductively
in terms of the previous ones to make sure that `p ∘ (rightInv p i) = id`. For this, the linear
term `p₁` in `p` should be invertible. In the definition, `i` is a linear isomorphism that should
coincide with `p₁`, so that one can use its inverse in the construction. The definition does not
use that `i = p₁`, but proofs that the definition is well-behaved do.

The `n`-th term in `p ∘ q` is `∑ pₖ (q_{j₁}, ..., q_{jₖ})` over `j₁ + ... + jₖ = n`. In this
expression, `qₙ` appears only once, in `p₁ (qₙ)`. We adjust the definition of `qₙ` so that this
term compensates the rest of the sum, using `i⁻¹` as an inverse to `p₁`.

These formulas only make sense when the constant term `p₀` vanishes. The definition we give is
general, but it ignores the value of `p₀`.
-/
/-
**FormalMultilinearSeries.rightInv** 是 Mathlib 中的一个定义，位于命名空间 `FormalMultilinearS
eries`。
形式化陈述：rightInv (p : FormalMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F) (x : E) : For
malMultilinearSeries 𝕜 F E | 0 => ContinuousMultilinearMap.uncurry0 𝕜 _ x | 1 =>
 (continuousMultilinearCurryFin1 𝕜 F E).symm i.symm | n + 2 => let q : FormalMul
tilinearSeries 𝕜 F E
参数：p : FormalMultilinearSeries 𝕜 E F；i : E ≃L[𝕜] F；x : E。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The right inverse of a formal multilinear series, where the `n`-th term is defin
ed inductively
in terms of the previous ones to make sure that `p ∘ (rightInv p i) = id`. For t
his, the linear
term `p₁` in `p` should be invertible. In the definition, `i` is a linear isomor
phism that should
coincide with `p₁`, so that one can use its inverse in the construction. The def
inition does not
use that `i = p₁`, but proofs that the definition is well-behaved do.

The `n`-th term in `p ∘ q` is `∑ pₖ (q_{j₁}, ..., q_{jₖ})` over `j₁ + ... + jₖ =
 n`. In this
expression, `qₙ` appears only once, in `p₁ (qₙ)`. We adjust the definition of `q
ₙ` so that this
term compensates the rest of the sum, using `i⁻¹` as an inverse to `p₁`.

These formulas only make sense when the constant term `p₀` vanishes. The definit
ion we give is
general, but it ignores the value of `p₀`.
-/
noncomputable def rightInv (p : FormalMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F) (x : E) :
    FormalMultilinearSeries 𝕜 F E
  | 0 => ContinuousMultilinearMap.uncurry0 𝕜 _ x
  | 1 => (continuousMultilinearCurryFin1 𝕜 F E).symm i.symm
  | n + 2 =>
    let q : FormalMultilinearSeries 𝕜 F E := fun k => if k < n + 2 then rightInv p i x k else 0;
    -(i.symm : F →L[𝕜] E).compContinuousMultilinearMap ((p.comp q) (n + 2))

@[simp]
/-
**FormalMultilinearSeries.rightInv_coeff_zero** 是 Mathlib 中的一个定理，位于命名空间 `FormalM
ultilinearSeries`。
形式化陈述：rightInv_coeff_zero (p : FormalMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F) (x
 : E) : p.rightInv i x 0 = ContinuousMultilinearMap.uncurry0 𝕜 _ x
参数：p : FormalMultilinearSeries 𝕜 E F；i : E ≃L[𝕜] F；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FormalMultilinearSeries.rightInv.eq_1`：∀ {𝕜 : Type u_1} [inst : Nontrivi
allyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : No
rmedSpace 𝕜 E] {F : Type u_…
-/
theorem rightInv_coeff_zero (p : FormalMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F) (x : E) :
    p.rightInv i x 0 = ContinuousMultilinearMap.uncurry0 𝕜 _ x := by rw [rightInv]

@[simp]
/-
**FormalMultilinearSeries.rightInv_coeff_one** 是 Mathlib 中的一个定理，位于命名空间 `FormalMu
ltilinearSeries`。
形式化陈述：rightInv_coeff_one (p : FormalMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F) (x 
: E) : p.rightInv i x 1 = (continuousMultilinearCurryFin1 𝕜 F E).symm i.symm
参数：p : FormalMultilinearSeries 𝕜 E F；i : E ≃L[𝕜] F；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FormalMultilinearSeries.rightInv.eq_2`：∀ {𝕜 : Type u_1} [inst : Nontrivi
allyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : No
rmedSpace 𝕜 E] {F : Type u_…
-/
theorem rightInv_coeff_one (p : FormalMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F) (x : E) :
    p.rightInv i x 1 = (continuousMultilinearCurryFin1 𝕜 F E).symm i.symm := by rw [rightInv]

set_option backward.isDefEq.respectTransparency false in
/-- The right inverse does not depend on the zeroth coefficient of a formal multilinear
series. -/
/-
**FormalMultilinearSeries.rightInv_removeZero** 是 Mathlib 中的一个定理，位于命名空间 `FormalM
ultilinearSeries`。
形式化陈述：rightInv_removeZero (p : FormalMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F) (x
 : E) : p.removeZero.rightInv i x = p.rightInv i x
参数：p : FormalMultilinearSeries 𝕜 E F；i : E ≃L[𝕜] F；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `FormalMultilinearSeries.ext`：∀ {𝕜 : Type u} {E : Type v} {F : Type w} [i
nst : Semiring 𝕜] [inst_1 : AddCommMonoid E] [inst_2 : _root_.Module 𝕜 E]   [ins
t_3 : Topological…
· 使用定理 `Nat.strong_induction_on`：∀ {p : ℕ → Prop} (n : ℕ), (∀ (n : ℕ), (∀ m < n,
 p m) → p n) → p n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FormalMultilinearSeries.rightInv_coeff_zero`：rightInv_coeff_zero (p : Fo
rmalMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F) (x : E) : p.rightInv i x 0 = Contin
uousMultilinearMap.uncurry0 𝕜 _ x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `FormalMultilinearSeries.rightInv_coeff_one`：rightInv_coeff_one (p : Form
alMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F) (x : E) : p.rightInv i x 1 = (continu
ousMultilinearCurryFin1 𝕜 F E).s…
· 使用定理 `FormalMultilinearSeries.rightInv.eq_3`：∀ {𝕜 : Type u_1} [inst : Nontrivi
allyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : No
rmedSpace 𝕜 E] {F : Type u_…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `FormalMultilinearSeries.removeZero_comp_of_pos`：removeZero_comp_of_pos (
q : FormalMultilinearSeries 𝕜 F G) (p : FormalMultilinearSeries 𝕜 E F) {n : Nat}
 (hn : 0 < n) : q.removeZero.comp p …
· 使用定理 `add_pos_of_nonneg_of_pos`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst
_1 : Preorder α] [AddLeftStrictMono α] {a b : α},   0 ≤ a → 0 < b → 0 < a + b
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `zero_lt_two`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : Part
ialOrder α] [ZeroLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 2
· 使用定理 `ContinuousMultilinearMap.ext`：ext {f f' : ContinuousMultilinearMap R M₁ 
M₂} (H : forall x, f x = f' x) : f = f'
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
（共 32 条，此处仅展示前 30 条）

--- 原说明 ---
The right inverse does not depend on the zeroth coefficient of a formal multilin
ear
series.
-/
theorem rightInv_removeZero (p : FormalMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F) (x : E) :
    p.removeZero.rightInv i x = p.rightInv i x := by
  ext1 n
  induction n using Nat.strong_induction_on with | _ n IH
  match n with
  | 0 => simp only [rightInv_coeff_zero]
  | 1 => simp only [rightInv_coeff_one]
  | n + 2 =>
    simp only [rightInv, neg_inj]
    rw [removeZero_comp_of_pos _ _ (add_pos_of_nonneg_of_pos n.zero_le zero_lt_two)]
    congr (config := { closePost := false }) 2 with k
    by_cases hk : k < n + 2 <;> simp [hk, IH]
/-
**FormalMultilinearSeries.comp_rightInv_aux1** 是 Mathlib 中的一个定理，位于命名空间 `FormalMu
ltilinearSeries`。
形式化陈述：comp_rightInv_aux1 {n : Nat} (hn : 0 < n) (p : FormalMultilinearSeries 𝕜 E
 F) (q : FormalMultilinearSeries 𝕜 F E) (v : Fin n -> F) : p.comp q n v = ∑ c in
 {c : Composition n | 1 < c.length}.toFinset, p c.length (q.applyComposition c v
) + p 1 fun _ => q n v
参数：hn : 0 < n；p : FormalMultilinearSeries 𝕜 E F；q : FormalMultilinearSeries 𝕜 F 
E；v : Fin n -> F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `Finset.Subset.antisymm`：∀ {α : Type u_1} {s₁ s₂ : Finset α}, s₁ ⊆ s₂ → s
₂ ⊆ s₁ → s₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.toFinset_ofPred`：toFinset_ofPred [Fintype α] (p : α -> Prop) [Decida
blePred p] [Fintype { x | p x }] : Set.toFinset {x | p x} = Finset.univ.filter p
· 使用引理 `Finset.union_singleton`：union_singleton (x : α) (s : Finset α) : s union
 {x} = insert x s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_iff_le_not_lt`：eq_iff_le_not_lt : a = b ↔ a <= b ∧ ¬a < b
· 使用定理 `Composition.length_pos_of_pos`：∀ {n : ℕ} (c : Composition n), 0 < n → 0 
< c.length
· 使用定理 `Composition.eq_single_iff_length`：eq_single_iff_length {n : Nat} (h : 0 
< n) {c : Composition n} : c = single n h ↔ c.length = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `Finset.subset_univ`：subset_univ (s : Finset α) : s subseteq univ
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `FormalMultilinearSeries.congr`：congr (p : FormalMultilinearSeries 𝕜 E F)
 {m n : Nat} {v : Fin m -> E} {w : Fin n -> E} (h1 : m = n) (h2 : forall (i : Na
t) (him : i < m) (h…
· 使用定理 `Composition.single_length`：single_length {n : Nat} (h : 0 < n) : (single
 n h).length = 1
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `FormalMultilinearSeries.applyComposition_single`：applyComposition_single
 (p : FormalMultilinearSeries 𝕜 E F) {n : Nat} (hn : 0 < n) (v : Fin n -> E) : p
.applyComposition (Composition.single…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
（共 36 条，此处仅展示前 30 条）
-/
theorem comp_rightInv_aux1 {n : ℕ} (hn : 0 < n) (p : FormalMultilinearSeries 𝕜 E F)
    (q : FormalMultilinearSeries 𝕜 F E) (v : Fin n → F) :
    p.comp q n v =
      ∑ c ∈ {c : Composition n | 1 < c.length}.toFinset,
          p c.length (q.applyComposition c v) + p 1 fun _ => q n v := by
  have A :
    (Finset.univ : Finset (Composition n)) =
      {c | 1 < Composition.length c}.toFinset ∪ {Composition.single n hn} := by
    refine Subset.antisymm (fun c _ => ?_) (subset_univ _)
    by_cases h : 1 < c.length
    · simp [h]
    · have : c.length = 1 := by
        refine (eq_iff_le_not_lt.2 ⟨?_, h⟩).symm; exact c.length_pos_of_pos hn
      rw [← Composition.eq_single_iff_length hn] at this
      simp [this]
  have B :
    Disjoint ({c | 1 < Composition.length c} : Set (Composition n)).toFinset
      {Composition.single n hn} := by
    simp
  have C :
    p (Composition.single n hn).length (q.applyComposition (Composition.single n hn) v) =
      p 1 fun _ : Fin 1 => q n v := by
    apply p.congr (Composition.single_length hn) fun j hj1 _ => ?_
    simp [applyComposition_single]
  simp [FormalMultilinearSeries.comp, A, Finset.sum_union B, C, -Set.toFinset_ofPred,
    -add_right_inj, -Composition.single_length, -Finset.union_singleton]
/-
**FormalMultilinearSeries.comp_rightInv_aux2** 是 Mathlib 中的一个定理，位于命名空间 `FormalMu
ltilinearSeries`。
形式化陈述：comp_rightInv_aux2 (p : FormalMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F) (x 
: E) (n : Nat) (v : Fin (n + 2) -> F) : ∑ c in {c : Composition (n + 2) | 1 < c.
length}.toFinset, p c.length (applyComposition (fun k : Nat => ite (k < n + 2) (
p.rightInv i x k) 0) c v) = ∑ c in {c : Composition (n + 2) | 1 < c.length}.toFi
nset, p c.length ((p.rightInv i x).applyComposition c v)
参数：p : FormalMultilinearSeries 𝕜 E F；i : E ≃L[𝕜] F；x : E；n : Nat；v : Fin (n + 2)
 -> F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `FormalMultilinearSeries.congr`：congr (p : FormalMultilinearSeries 𝕜 E F)
 {m n : Nat} {v : Fin m -> E} {w : Fin n -> E} (h1 : m = n) (h2 : forall (i : Na
t) (him : i < m) (h…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Composition.ne_single_iff`：ne_single_iff {n : Nat} (hn : 0 < n) {c : Com
position n} : c != single n hn ↔ forall i, c.blocksFun i < n
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Set.mem_toFinset`：mem_toFinset {s : Set α} [Fintype s] {a : α} : a in s.
toFinset ↔ a in s
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
（共 31 条，此处仅展示前 30 条）
-/
theorem comp_rightInv_aux2 (p : FormalMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F) (x : E) (n : ℕ)
    (v : Fin (n + 2) → F) :
    ∑ c ∈ {c : Composition (n + 2) | 1 < c.length}.toFinset,
        p c.length (applyComposition (fun k : ℕ => ite (k < n + 2) (p.rightInv i x k) 0) c v) =
      ∑ c ∈ {c : Composition (n + 2) | 1 < c.length}.toFinset,
        p c.length ((p.rightInv i x).applyComposition c v) := by
  have N : 0 < n + 2 := by simp
  refine sum_congr rfl fun c hc => p.congr rfl fun j hj1 hj2 => ?_
  have : ∀ k, c.blocksFun k < n + 2 := by
    simp only [Set.mem_toFinset (s := {c : Composition (n + 2) | 1 < c.length}),
      Set.mem_ofPred_eq] at hc
    simp [← Composition.ne_single_iff N, Composition.eq_single_iff_length, ne_of_gt hc]
  simp [applyComposition, this]

set_option backward.isDefEq.respectTransparency false in
/-- The right inverse to a formal multilinear series is indeed a right inverse, provided its linear
term is invertible and its constant term vanishes. -/
/-
**FormalMultilinearSeries.comp_rightInv** 是 Mathlib 中的一个定理，位于命名空间 `FormalMultili
nearSeries`。
形式化陈述：comp_rightInv (p : FormalMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F) (x : E) 
(h : p 1 = (continuousMultilinearCurryFin1 𝕜 E F).symm i) : p.comp (rightInv p i
 x) = id 𝕜 F (p 0 0)
参数：p : FormalMultilinearSeries 𝕜 E F；i : E ≃L[𝕜] F；x : E；h : p 1 = (continuousMu
ltilinearCurryFin1 𝕜 E F).symm i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `FormalMultilinearSeries.ext`：∀ {𝕜 : Type u} {E : Type v} {F : Type w} [i
nst : Semiring 𝕜] [inst_1 : AddCommMonoid E] [inst_2 : _root_.Module 𝕜 E]   [ins
t_3 : Topological…
· 使用定理 `ContinuousMultilinearMap.ext`：ext {f f' : ContinuousMultilinearMap R M₁ 
M₂} (H : forall x, f x = f' x) : f = f'
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FormalMultilinearSeries.comp_coeff_zero'`：comp_coeff_zero' (q : FormalMu
ltilinearSeries 𝕜 F G) (p : FormalMultilinearSeries 𝕜 E F) (v : Fin 0 -> E) : (q
.comp p) 0 v = q 0 fun _i => 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Matrix.zero_empty`：∀ {α : Type u_1} [inst : Zero α], 0 = ![]
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `FormalMultilinearSeries.comp_coeff_one`：comp_coeff_one (q : FormalMultil
inearSeries 𝕜 F G) (p : FormalMultilinearSeries 𝕜 E F) (v : Fin 1 -> E) : (q.com
p p) 1 v = q 1 fun _i => p 1…
· 使用定理 `FormalMultilinearSeries.rightInv_coeff_one`：rightInv_coeff_one (p : Form
alMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F) (x : E) : p.rightInv i x 1 = (continu
ousMultilinearCurryFin1 𝕜 F E).s…
· 使用定理 `ContinuousLinearEquiv.apply_symm_apply`：apply_symm_apply (e : M₁ ≃SL[σ₁₂
] M₂) (c : M₂) : e (e.symm c) = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
（共 54 条，此处仅展示前 30 条）

--- 原说明 ---
The right inverse to a formal multilinear series is indeed a right inverse, prov
ided its linear
term is invertible and its constant term vanishes.
-/
theorem comp_rightInv (p : FormalMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F) (x : E)
    (h : p 1 = (continuousMultilinearCurryFin1 𝕜 E F).symm i) :
    p.comp (rightInv p i x) = id 𝕜 F (p 0 0) := by
  ext (n v)
  match n with
  | 0 =>
    simp only [comp_coeff_zero', Matrix.zero_empty, id_apply_zero]
    congr
    ext i
    exact i.elim0
  | 1 =>
    simp only [comp_coeff_one, h, rightInv_coeff_one, ContinuousLinearEquiv.apply_symm_apply,
      id_apply_one, ContinuousLinearEquiv.coe_apply, continuousMultilinearCurryFin1_symm_apply]
  | n + 2 =>
    have N : 0 < n + 2 := by simp
    simp [comp_rightInv_aux1 N, h, rightInv, comp_rightInv_aux2, -Set.toFinset_ofPred]

set_option backward.isDefEq.respectTransparency false in
/-
**FormalMultilinearSeries.rightInv_coeff** 是 Mathlib 中的一个定理，位于命名空间 `FormalMultil
inearSeries`。
形式化陈述：rightInv_coeff (p : FormalMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F) (x : E)
 (n : Nat) (hn : 2 <= n) : p.rightInv i x n = -(i.symm : F ->L[𝕜] E).compContinu
ousMultilinearMap (∑ c in ({c | 1 < Composition.length c}.toFinset : Finset (Com
position n)), p.compAlongComposition (p.rightInv i x) c)
参数：p : FormalMultilinearSeries 𝕜 E F；i : E ≃L[𝕜] F；x : E；n : Nat；hn : 2 <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `zero_lt_two`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : Part
ialOrder α] [ZeroLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 2
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `one_lt_two`：one_lt_two [AddLeftStrictMono α] : (1 : α) < 2
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FormalMultilinearSeries.rightInv.eq_3`：∀ {𝕜 : Type u_1} [inst : Nontrivi
allyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : No
rmedSpace 𝕜 E] {F : Type u_…
· 使用定理 `ContinuousMultilinearMap.ext`：ext {f f' : ContinuousMultilinearMap R M₁ 
M₂} (H : forall x, f x = f' x) : f = f'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `ContinuousMultilinearMap.map_zero`：map_zero [Nonempty ι] : f 0 = 0
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
（共 42 条，此处仅展示前 30 条）
-/
theorem rightInv_coeff (p : FormalMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F) (x : E)
    (n : ℕ) (hn : 2 ≤ n) :
    p.rightInv i x n =
      -(i.symm : F →L[𝕜] E).compContinuousMultilinearMap
          (∑ c ∈ ({c | 1 < Composition.length c}.toFinset : Finset (Composition n)),
            p.compAlongComposition (p.rightInv i x) c) := by
  match n with
  | 0 => exact False.elim (zero_lt_two.not_ge hn)
  | 1 => exact False.elim (one_lt_two.not_ge hn)
  | n + 2 =>
    simp only [rightInv, neg_inj]
    congr (config := { closePost := false }) 1
    ext v
    have N : 0 < n + 2 := by simp
    have : ((p 1) fun _ : Fin 1 => 0) = 0 := ContinuousMultilinearMap.map_zero _
    simp [comp_rightInv_aux1 N, this, comp_rightInv_aux2, -Set.toFinset_ofPred]

/-! ### Coincidence of the left and the right inverse -/


/-
**FormalMultilinearSeries.leftInv_eq_rightInv** 是 Mathlib 中的一个定理，位于命名空间 `FormalM
ultilinearSeries`。
形式化陈述：leftInv_eq_rightInv (p : FormalMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F) (x
 : E) (h : p 1 = (continuousMultilinearCurryFin1 𝕜 E F).symm i) : leftInv p i x 
= rightInv p i x
参数：p : FormalMultilinearSeries 𝕜 E F；i : E ≃L[𝕜] F；x : E；h : p 1 = (continuousMu
ltilinearCurryFin1 𝕜 E F).symm i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.zero_empty`：∀ {α : Type u_1} [inst : Zero α], 0 = ![]
· 使用定理 `FormalMultilinearSeries.comp_id`：comp_id (p : FormalMultilinearSeries 𝕜 
E F) (x : E) : p.comp (id 𝕜 E x) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `FormalMultilinearSeries.comp_rightInv`：comp_rightInv (p : FormalMultilin
earSeries 𝕜 E F) (i : E ≃L[𝕜] F) (x : E) (h : p 1 = (continuousMultilinearCurryF
in1 𝕜 E F).symm i) : p.comp…
· 使用定理 `FormalMultilinearSeries.comp_assoc`：comp_assoc (r : FormalMultilinearSer
ies 𝕜 G H) (q : FormalMultilinearSeries 𝕜 F G) (p : FormalMultilinearSeries 𝕜 E 
F) : (r.comp q).comp p =…
· 使用定理 `FormalMultilinearSeries.leftInv_comp`：leftInv_comp (p : FormalMultilinea
rSeries 𝕜 E F) (i : E ≃L[𝕜] F) (x : E) (h : p 1 = (continuousMultilinearCurryFin
1 𝕜 E F).symm i) : (leftIn…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `FormalMultilinearSeries.id_comp'`：id_comp' (p : FormalMultilinearSeries 
𝕜 E F) (x : F) (v0 : Fin 0 -> E) (h : x = p 0 v0) : (id 𝕜 F x).comp p = p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `FormalMultilinearSeries.rightInv_coeff_zero`：rightInv_coeff_zero (p : Fo
rmalMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F) (x : E) : p.rightInv i x 0 = Contin
uousMultilinearMap.uncurry0 𝕜 _ x

--- 原说明 ---
### Coincidence of the left and the right inverse
-/
theorem leftInv_eq_rightInv (p : FormalMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F) (x : E)
    (h : p 1 = (continuousMultilinearCurryFin1 𝕜 E F).symm i) :
    leftInv p i x = rightInv p i x :=
  calc
    leftInv p i x = (leftInv p i x).comp (id 𝕜 F (p 0 0)) := by simp
    _ = (leftInv p i x).comp (p.comp (rightInv p i x)) := by rw [comp_rightInv p i _ h]
    _ = ((leftInv p i x).comp p).comp (rightInv p i x) := by rw [comp_assoc]
    _ = (id 𝕜 E x).comp (rightInv p i x) := by rw [leftInv_comp p i _ h]
    _ = rightInv p i x := by simp [id_comp' _ _ 0]

/-!
### Convergence of the inverse of a power series

Assume that `p` is a convergent multilinear series, and let `q` be its (left or right) inverse.
Using the left-inverse formula gives
$$
q_n = - (p_1)^{-n} \sum_{k=0}^{n-1} \sum_{i_1 + \dotsc + i_k = n} q_k (p_{i_1}, \dotsc, p_{i_k}).
$$
Assume for simplicity that we are in dimension `1` and `p₁ = 1`. In the formula for `qₙ`, the term
`q_{n-1}` appears with a multiplicity of `n-1` (choosing the index `i_j` for which `i_j = 2` while
all the other indices are equal to `1`), which indicates that `qₙ` might grow like `n!`. This is
bad for summability properties.

It turns out that the right-inverse formula is better behaved, and should instead be used for this
kind of estimate. It reads
$$
q_n = - (p_1)^{-1} \sum_{k=2}^n \sum_{i_1 + \dotsc + i_k = n} p_k (q_{i_1}, \dotsc, q_{i_k}).
$$
Here, `q_{n-1}` can only appear in the term with `k = 2`, and it only appears twice, so there is
hope this formula can lead to an at most geometric behavior.

Let `Qₙ = ‖qₙ‖`. Bounding `‖pₖ‖` with `C r^k` gives an inequality
$$
Q_n ≤ C' \sum_{k=2}^n r^k \sum_{i_1 + \dotsc + i_k = n} Q_{i_1} \dotsm Q_{i_k}.
$$

This formula is not enough to prove by naive induction on `n` a bound of the form `Qₙ ≤ D R^n`.
However, assuming that the inequality above were an equality, one could get a formula for the
generating series of the `Qₙ`:

$$
\begin{align}
Q(z) & := \sum Q_n z^n = Q_1 z + C' \sum_{2 \leq k \leq n} \sum_{i_1 + \dotsc + i_k = n}
  (r z^{i_1} Q_{i_1}) \dotsm (r z^{i_k} Q_{i_k})
\\ & = Q_1 z + C' \sum_{k = 2}^\infty (\sum_{i_1 \geq 1} r z^{i_1} Q_{i_1})
  \dotsm (\sum_{i_k \geq 1} r z^{i_k} Q_{i_k})
\\ & = Q_1 z + C' \sum_{k = 2}^\infty (r Q(z))^k
= Q_1 z + C' (r Q(z))^2 / (1 - r Q(z)).
\end{align}
$$

One can solve this formula explicitly. The solution is analytic in a neighborhood of `0` in `ℂ`,
hence its coefficients grow at most geometrically (by a contour integral argument), and therefore
the original `Qₙ`, which are bounded by these ones, are also at most geometric.

This classical argument is not really satisfactory, as it requires an a priori bound on a complex
analytic function. Another option would be to compute explicitly its terms (with binomial
coefficients) to obtain an explicit geometric bound, but this would be very painful.

Instead, we will use the above intuition, but in a slightly different form, with finite sums and an
induction. I learnt this trick in [poeschel2017siegelsternberg]. Let
$S_n = \sum_{k=1}^n Q_k a^k$ (where `a` is a positive real parameter to be chosen suitably small).
The above computation but with finite sums shows that

$$
S_n \leq Q_1 a + C' \sum_{k=2}^n (r S_{n-1})^k.
$$

In particular, $S_n \leq Q_1 a + C' (r S_{n-1})^2 / (1- r S_{n-1})$.
Assume that $S_{n-1} \leq K a$, where `K > Q₁` is fixed and `a` is small enough so that
`r K a ≤ 1/2` (to control the denominator). Then this equation gives a bound
$S_n \leq Q_1 a + 2 C' r^2 K^2 a^2$.
If `a` is small enough, this is bounded by `K a` as the second term is quadratic in `a`, and
therefore negligible.

By induction, we deduce `Sₙ ≤ K a` for all `n`, which gives in particular the fact that `aⁿ Qₙ`
remains bounded.
-/


/-- First technical lemma to control the growth of coefficients of the inverse. Bound the explicit
expression for `∑_{k<n+1} aᵏ Qₖ` in terms of a sum of powers of the same sum one step before,
in a general abstract setup. -/
/-
**FormalMultilinearSeries.radius_right_inv_pos_of_radius_pos_aux1** 是 Mathlib 中的
一个定理，位于命名空间 `FormalMultilinearSeries`。
形式化陈述：radius_right_inv_pos_of_radius_pos_aux1 (n : Nat) (p : Nat -> Real) (hp : 
forall k, 0 <= p k) {r a : Real} (hr : 0 <= r) (ha : 0 <= a) : ∑ k in Ico 2 (n +
 1), a ^ k * ∑ c in ({c | 1 < Composition.length c}.toFinset : Finset (Compositi
on k)), r ^ c.length * ∏ j, p (c.blocksFun j) <= ∑ j in Ico 2 (n + 1), r ^ j * (
∑ k in Ico 1 n, a ^ k * p k) ^ j
参数：n : Nat；p : Nat -> Real；hp : forall k, 0 <= p k；hr : 0 <= r；ha : 0 <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `Finset.prod_mul_distrib`：prod_mul_distrib : ∏ x in s, f x * g x = (∏ x i
n s, f x) * ∏ x in s, g x
· 使用引理 `Finset.prod_pow_eq_pow_sum`：prod_pow_eq_pow_sum (s : Finset ι) (f : ι ->
 Nat) (a : M) : ∏ i in s, a ^ f i = a ^ ∑ i in s, f i
· 使用定理 `Composition.sum_blocksFun`：sum_blocksFun : ∑ i, c.blocksFun i = n
· 使用定理 `Finset.prod_const`：prod_const (b : M) : ∏ _x in s, b = b ^ #s
· 使用定理 `Finset.card_fin`：Finset.card_fin (n : Nat) : #(univ : Finset (Fin n)) = 
n
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a c₁ c₂ : R} {b₁ b₂ : ℕ} {d : R},   a ^ b₁ = c₁ → a ^ b₂ = c₂ → c₁ * c₂ = 
d → a ^ (b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.single_pow`：∀ {R : Type u_1} [inst : CommSemi
ring R] {a c : R} {b : ℕ}, a ^ b = c → (a + 0) ^ b = c + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pow_mul`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₂ c₂ : R} {ea₁ b c₁ : ℕ} {xa₁ c₃ d : R},   ea₁ * b = c₁ → a₂ ^ b = c₂
 → xa₁ ^ c₁ * Nat.rawCast 1 …
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
· 使用定理 `Mathlib.Tactic.Ring.Common.one_pow`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a : R} (b : ℕ), Mathlib.Meta.NormNum.IsNat a 1 → a ^ b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R) {e : R}, Nat.rawCast 1 = e → a ^ 0 = e + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Finset.sum_sigma'`：∀ {α : Type u_3} {β : Type u_4} [inst : AddCommMonoid
 β] {σ : α → Type u_6} (s : Finset α) (t : (a : α) → Finset (σ a))   (f : (a : α
) → σ a…
（共 68 条，此处仅展示前 30 条）

--- 原说明 ---
First technical lemma to control the growth of coefficients of the inverse. Boun
d the explicit
expression for `∑_{k<n+1} aᵏ Qₖ` in terms of a sum of powers of the same sum one
 step before,
in a general abstract setup.
-/
theorem radius_right_inv_pos_of_radius_pos_aux1 (n : ℕ) (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k) {r a : ℝ}
    (hr : 0 ≤ r) (ha : 0 ≤ a) :
    ∑ k ∈ Ico 2 (n + 1),
        a ^ k *
          ∑ c ∈ ({c | 1 < Composition.length c}.toFinset : Finset (Composition k)),
            r ^ c.length * ∏ j, p (c.blocksFun j) ≤
      ∑ j ∈ Ico 2 (n + 1), r ^ j * (∑ k ∈ Ico 1 n, a ^ k * p k) ^ j :=
  calc
    ∑ k ∈ Ico 2 (n + 1),
          a ^ k *
            ∑ c ∈ ({c | 1 < Composition.length c}.toFinset : Finset (Composition k)),
              r ^ c.length * ∏ j, p (c.blocksFun j) =
        ∑ k ∈ Ico 2 (n + 1),
          ∑ c ∈ ({c | 1 < Composition.length c}.toFinset : Finset (Composition k)),
            ∏ j, r * (a ^ c.blocksFun j * p (c.blocksFun j)) := by
      simp_rw [mul_sum]
      congr! with k _ c
      rw [prod_mul_distrib, prod_mul_distrib, prod_pow_eq_pow_sum, Composition.sum_blocksFun,
        prod_const, card_fin]
      ring
    _ ≤
        ∑ d ∈ compPartialSumTarget 2 (n + 1) n,
          ∏ j : Fin d.2.length, r * (a ^ d.2.blocksFun j * p (d.2.blocksFun j)) := by
      rw [sum_sigma']
      gcongr
      · intro x _ _
        exact prod_nonneg fun j _ ↦ (by positivity [ha, hp (x.snd.blocksFun j)])
      rintro ⟨k, c⟩ hd
      simp only [Set.mem_toFinset (s := {c | 1 < Composition.length c}), mem_Ico, mem_sigma,
        Set.mem_ofPred_eq] at hd
      simp only [mem_compPartialSumTarget_iff]
      refine ⟨hd.2, c.length_le.trans_lt hd.1.2, fun j => ?_⟩
      have : c ≠ Composition.single k (zero_lt_two.trans_le hd.1.1) := by
        simp [Composition.eq_single_iff_length, ne_of_gt hd.2]
      rw [Composition.ne_single_iff] at this
      exact (this j).trans_le (Nat.lt_succ_iff.mp hd.1.2)
    _ = ∑ e ∈ compPartialSumSource 2 (n + 1) n, ∏ j : Fin e.1, r * (a ^ e.2 j * p (e.2 j)) := by
      symm
      apply compChangeOfVariables_sum
      rintro ⟨k, blocksFun⟩ H
      have K : (compChangeOfVariables 2 (n + 1) n ⟨k, blocksFun⟩ H).snd.length = k := by simp
      congr 2 <;> try rw [K]
      rw [Fin.heq_fun_iff K.symm]
      intro j
      rw [compChangeOfVariables_blocksFun]
    _ = ∑ j ∈ Ico 2 (n + 1), r ^ j * (∑ k ∈ Ico 1 n, a ^ k * p k) ^ j := by
      rw [compPartialSumSource,
        ← sum_sigma' (Ico 2 (n + 1))
          (fun k : ℕ => (Fintype.piFinset fun _ : Fin k => Ico 1 n : Finset (Fin k → ℕ)))
          (fun n e => ∏ j : Fin n, r * (a ^ e j * p (e j)))]
      congr! with j
      simp only [← @MultilinearMap.mkPiAlgebra_apply ℝ (Fin j) _ ℝ]
      simp only [←
        MultilinearMap.map_sum_finset (MultilinearMap.mkPiAlgebra ℝ (Fin j) ℝ) fun _ (m : ℕ) =>
          r * (a ^ m * p m)]
      simp only [MultilinearMap.mkPiAlgebra_apply]
      simp [prod_const, ← mul_sum, mul_pow]

/-- Second technical lemma to control the growth of coefficients of the inverse. Bound the explicit
expression for `∑_{k<n+1} aᵏ Qₖ` in terms of a sum of powers of the same sum one step before,
in the specific setup we are interesting in, by reducing to the general bound in
`radius_rightInv_pos_of_radius_pos_aux1`. -/
/-
**FormalMultilinearSeries.radius_rightInv_pos_of_radius_pos_aux2** 是 Mathlib 中的一
个定理，位于命名空间 `FormalMultilinearSeries`。
形式化陈述：radius_rightInv_pos_of_radius_pos_aux2 {x : E} {n : Nat} (hn : 2 <= n + 1)
 (p : FormalMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F) {r a C : Real} (hr : 0 <= r
) (ha : 0 <= a) (hC : 0 <= C) (hp : forall n, ‖p n‖ <= C * r ^ n) : ∑ k in Ico 1
 (n + 1), a ^ k * ‖p.rightInv i x k‖ <= ‖(i.symm : F ->L[𝕜] E)‖ * a + ‖(i.symm :
 F ->L[𝕜] E)‖ * C * ∑ k in Ico 2 (n + 1), (r * ∑ j in Ico 1 n, a ^ j * ‖p.rightI
nv i x j‖) ^ k
参数：hn : 2 <= n + 1；p : FormalMultilinearSeries 𝕜 E F；i : E ≃L[𝕜] F；hr : 0 <= r；h
a : 0 <= a；hC : 0 <= C；hp : forall n, ‖p n‖ <= C * r ^ n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_Ico_consecutive`：∀ {M : Type u_3} [inst : AddCommMonoid M] (f
 : ℕ → M) {m n k : ℕ},   m ≤ n → n ≤ k → ∑ i ∈ Finset.Ico m n, f i + ∑ i ∈ Finse
t.Ico n k, f i =…
· 使用引理 `one_le_two`：one_le_two [LE α] [ZeroLEOneClass α] [AddLeftMono α] : (1 : 
α) <= 2
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Nat.Ico_succ_singleton`：Ico_succ_singleton : Ico a (a + 1) = {a}
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `FormalMultilinearSeries.rightInv_coeff_one`：rightInv_coeff_one (p : Form
alMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F) (x : E) : p.rightInv i x 1 = (continu
ousMultilinearCurryFin1 𝕜 F E).s…
· 使用定理 `LinearIsometryEquiv.norm_map`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type
 u_5} {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* 
R₂} {σ₂₁ : R₂ →+* …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `FormalMultilinearSeries.rightInv_coeff`：rightInv_coeff (p : FormalMultil
inearSeries 𝕜 E F) (i : E ≃L[𝕜] F) (x : E) (n : Nat) (hn : 2 <= n) : p.rightInv 
i x n = -(i.symm : F ->L[𝕜] …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_Ico`：mem_Ico : x in Ico a b ↔ a <= x ∧ x < b
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
（共 65 条，此处仅展示前 30 条）

--- 原说明 ---
Second technical lemma to control the growth of coefficients of the inverse. Bou
nd the explicit
expression for `∑_{k<n+1} aᵏ Qₖ` in terms of a sum of powers of the same sum one
 step before,
in the specific setup we are interesting in, by reducing to the general bound in
`radius_rightInv_pos_of_radius_pos_aux1`.
-/
theorem radius_rightInv_pos_of_radius_pos_aux2 {x : E} {n : ℕ} (hn : 2 ≤ n + 1)
    (p : FormalMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F) {r a C : ℝ} (hr : 0 ≤ r) (ha : 0 ≤ a)
    (hC : 0 ≤ C) (hp : ∀ n, ‖p n‖ ≤ C * r ^ n) :
    ∑ k ∈ Ico 1 (n + 1), a ^ k * ‖p.rightInv i x k‖ ≤
      ‖(i.symm : F →L[𝕜] E)‖ * a +
        ‖(i.symm : F →L[𝕜] E)‖ * C *
          ∑ k ∈ Ico 2 (n + 1), (r * ∑ j ∈ Ico 1 n, a ^ j * ‖p.rightInv i x j‖) ^ k :=
  let I := ‖(i.symm : F →L[𝕜] E)‖
  calc
    ∑ k ∈ Ico 1 (n + 1), a ^ k * ‖p.rightInv i x k‖ =
        a * I + ∑ k ∈ Ico 2 (n + 1), a ^ k * ‖p.rightInv i x k‖ := by
      simp only [I, LinearIsometryEquiv.norm_map, pow_one, rightInv_coeff_one,
        show Ico (1 : ℕ) 2 = {1} from Nat.Ico_succ_singleton 1,
        sum_singleton, ← sum_Ico_consecutive _ one_le_two hn]
    _ =
        a * I +
          ∑ k ∈ Ico 2 (n + 1),
            a ^ k *
              ‖(i.symm : F →L[𝕜] E).compContinuousMultilinearMap
                  (∑ c ∈ ({c | 1 < Composition.length c}.toFinset : Finset (Composition k)),
                    p.compAlongComposition (p.rightInv i x) c)‖ := by
      congr! 2 with j hj
      rw [rightInv_coeff _ _ _ _ (mem_Ico.1 hj).1, norm_neg]
    _ ≤
        a * ‖(i.symm : F →L[𝕜] E)‖ +
          ∑ k ∈ Ico 2 (n + 1),
            a ^ k *
              (I *
                ∑ c ∈ ({c | 1 < Composition.length c}.toFinset : Finset (Composition k)),
                  C * r ^ c.length * ∏ j, ‖p.rightInv i x (c.blocksFun j)‖) := by
      gcongr with j
      apply (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans
      gcongr
      apply (norm_sum_le _ _).trans
      gcongr
      apply (compAlongComposition_norm _ _ _).trans
      gcongr
      apply hp
    _ = I * a + I * C * ∑ k ∈ Ico 2 (n + 1), a ^ k *
          ∑ c ∈ ({c | 1 < Composition.length c}.toFinset : Finset (Composition k)),
            r ^ c.length * ∏ j, ‖p.rightInv i x (c.blocksFun j)‖ := by
      simp_rw [I, mul_assoc C, ← mul_sum, ← mul_assoc, mul_comm _ ‖(i.symm : F →L[𝕜] E)‖,
        mul_assoc, ← mul_sum, ← mul_assoc, mul_comm _ C, mul_assoc, ← mul_sum]
      ring
    _ ≤ I * a + I * C *
        ∑ k ∈ Ico 2 (n + 1), (r * ∑ j ∈ Ico 1 n, a ^ j * ‖p.rightInv i x j‖) ^ k := by
      gcongr _ + _ * _ * ?_
      simp_rw [mul_pow]
      apply
        radius_right_inv_pos_of_radius_pos_aux1 n (fun k => ‖p.rightInv i x k‖)
          (fun k => norm_nonneg _) hr ha

/-- If a a formal multilinear series has a positive radius of convergence, then its right inverse
also has a positive radius of convergence. -/
/-
**FormalMultilinearSeries.radius_rightInv_pos_of_radius_pos** 是 Mathlib 中的一个定理，位
于命名空间 `FormalMultilinearSeries`。
形式化陈述：radius_rightInv_pos_of_radius_pos {p : FormalMultilinearSeries 𝕜 E F} {i :
 E ≃L[𝕜] F} {x : E} (hp : 0 < p.radius) : 0 < (p.rightInv i x).radius
参数：hp : 0 < p.radius。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `FormalMultilinearSeries.le_mul_pow_of_radius_pos`：le_mul_pow_of_radius_p
os (p : FormalMultilinearSeries 𝕜 E F) (h : 0 < p.radius) : exists (C r : _) (_ 
: 0 < C) (_ : 0 < r), forall n, ‖p n‖ …
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Filter.Tendsto.mul`：Filter.Tendsto.mul {α : Type*} {f g : α -> M} {x : F
ilter α} {a b : M} (hf : Tendsto f x (𝓝 a)) (hg : Tendsto g x (𝓝 b)) : Tendsto (
fun x =>…
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `tendsto_order`：tendsto_order [OrderTopology α] {f : β -> α} {a : α} {x :
 Filter β} : Tendsto f x (𝓝 a) ↔ (forall a' < a, forallᶠ b in x, a' < f b) ∧ for
all…
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
（共 171 条，此处仅展示前 30 条）

--- 原说明 ---
If a a formal multilinear series has a positive radius of convergence, then its 
right inverse
also has a positive radius of convergence.
-/
theorem radius_rightInv_pos_of_radius_pos
    {p : FormalMultilinearSeries 𝕜 E F} {i : E ≃L[𝕜] F} {x : E}
    (hp : 0 < p.radius) : 0 < (p.rightInv i x).radius := by
  obtain ⟨C, r, Cpos, rpos, ple⟩ :
    ∃ (C r : _) (_ : 0 < C) (_ : 0 < r), ∀ n : ℕ, ‖p n‖ ≤ C * r ^ n :=
    le_mul_pow_of_radius_pos p hp
  let I := ‖(i.symm : F →L[𝕜] E)‖
  -- choose `a` small enough to make sure that `∑_{k ≤ n} aᵏ Qₖ` will be controllable by
  -- induction
  obtain ⟨a, apos, ha1, ha2⟩ :
    ∃ (a : _) (apos : 0 < a),
      2 * I * C * r ^ 2 * (I + 1) ^ 2 * a ≤ 1 ∧ r * (I + 1) * a ≤ 1 / 2 := by
    have :
      Tendsto (fun a => 2 * I * C * r ^ 2 * (I + 1) ^ 2 * a) (𝓝 0)
        (𝓝 (2 * I * C * r ^ 2 * (I + 1) ^ 2 * 0)) :=
      tendsto_const_nhds.mul tendsto_id
    have A : ∀ᶠ a in 𝓝 0, 2 * I * C * r ^ 2 * (I + 1) ^ 2 * a < 1 := by
      apply (tendsto_order.1 this).2; simp [zero_lt_one]
    have : Tendsto (fun a => r * (I + 1) * a) (𝓝 0) (𝓝 (r * (I + 1) * 0)) :=
      tendsto_const_nhds.mul tendsto_id
    have B : ∀ᶠ a in 𝓝 0, r * (I + 1) * a < 1 / 2 := by
      apply (tendsto_order.1 this).2; simp
    have C : ∀ᶠ a in 𝓝[>] (0 : ℝ), (0 : ℝ) < a := by
      filter_upwards [self_mem_nhdsWithin] with _ ha using ha
    rcases (C.and ((A.and B).filter_mono inf_le_left)).exists with ⟨a, ha⟩
    exact ⟨a, ha.1, ha.2.1.le, ha.2.2.le⟩
  -- check by induction that the partial sums are suitably bounded, using the choice of `a` and the
  -- inductive control from Lemma `radius_rightInv_pos_of_radius_pos_aux2`.
  let S n := ∑ k ∈ Ico 1 n, a ^ k * ‖p.rightInv i x k‖
  have IRec : ∀ n, 1 ≤ n → S n ≤ (I + 1) * a := by
    apply Nat.le_induction
    · simp only [S]
      rw [Ico_eq_empty_of_le (le_refl 1), sum_empty]
      positivity
    · intro n one_le_n hn
      have In : 2 ≤ n + 1 := by lia
      have rSn : r * S n ≤ 1 / 2 :=
        calc
          r * S n ≤ r * ((I + 1) * a) := by gcongr
          _ ≤ 1 / 2 := by rwa [← mul_assoc]
      calc
        S (n + 1) ≤ I * a + I * C * ∑ k ∈ Ico 2 (n + 1), (r * S n) ^ k :=
          radius_rightInv_pos_of_radius_pos_aux2 In p i rpos.le apos.le Cpos.le ple
        _ = I * a + I * C * (((r * S n) ^ 2 - (r * S n) ^ (n + 1)) / (1 - r * S n)) := by
          rw [geom_sum_Ico' _ In]; exact ne_of_lt (rSn.trans_lt (by norm_num))
        _ ≤ I * a + I * C * ((r * S n) ^ 2 / (1 / 2)) := by
          gcongr
          · simp only [sub_le_self_iff]
            positivity
          · linarith only [rSn]
        _ = I * a + 2 * I * C * (r * S n) ^ 2 := by ring
        _ ≤ I * a + 2 * I * C * (r * ((I + 1) * a)) ^ 2 := by gcongr
        _ = (I + 2 * I * C * r ^ 2 * (I + 1) ^ 2 * a) * a := by ring
        _ ≤ (I + 1) * a := by gcongr
  -- conclude that all coefficients satisfy `aⁿ Qₙ ≤ (I + 1) a`.
  let a' : NNReal := ⟨a, apos.le⟩
  suffices H : (a' : ENNReal) ≤ (p.rightInv i x).radius by
    apply lt_of_lt_of_le _ H
    -- Prior to https://github.com/leanprover/lean4/pull/2734, this was `exact_mod_cast apos`.
    simpa only [ENNReal.coe_pos]
  apply le_radius_of_eventually_le _ ((I + 1) * a)
  filter_upwards [Ici_mem_atTop 1] with n (hn : 1 ≤ n)
  calc
    ‖p.rightInv i x n‖ * (a' : ℝ) ^ n = a ^ n * ‖p.rightInv i x n‖ := mul_comm _ _
    _ ≤ ∑ k ∈ Ico 1 (n + 1), a ^ k * ‖p.rightInv i x k‖ :=
      (haveI : ∀ k ∈ Ico 1 (n + 1), 0 ≤ a ^ k * ‖p.rightInv i x k‖ := fun k _ => by positivity
      single_le_sum this (by simp [hn]))
    _ ≤ (I + 1) * a := IRec (n + 1) (by simp)

/-- If a a formal multilinear series has a positive radius of convergence, then its left inverse
also has a positive radius of convergence. -/
/-
**FormalMultilinearSeries.radius_leftInv_pos_of_radius_pos** 是 Mathlib 中的一个定理，位于
命名空间 `FormalMultilinearSeries`。
形式化陈述：radius_leftInv_pos_of_radius_pos {p : FormalMultilinearSeries 𝕜 E F} {i : 
E ≃L[𝕜] F} {x : E} (hp : 0 < p.radius) (h : p 1 = (continuousMultilinearCurryFin
1 𝕜 E F).symm i) : 0 < (p.leftInv i x).radius
参数：hp : 0 < p.radius；h : p 1 = (continuousMultilinearCurryFin1 𝕜 E F).symm i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FormalMultilinearSeries.leftInv_eq_rightInv`：leftInv_eq_rightInv (p : Fo
rmalMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F) (x : E) (h : p 1 = (continuousMulti
linearCurryFin1 𝕜 E F).symm i) : …
· 使用定理 `FormalMultilinearSeries.radius_rightInv_pos_of_radius_pos`：radius_rightI
nv_pos_of_radius_pos {p : FormalMultilinearSeries 𝕜 E F} {i : E ≃L[𝕜] F} {x : E}
 (hp : 0 < p.radius) : 0 < (p.rightInv i x).rad…

--- 原说明 ---
If a a formal multilinear series has a positive radius of convergence, then its 
left inverse
also has a positive radius of convergence.
-/
theorem radius_leftInv_pos_of_radius_pos
    {p : FormalMultilinearSeries 𝕜 E F} {i : E ≃L[𝕜] F} {x : E}
    (hp : 0 < p.radius) (h : p 1 = (continuousMultilinearCurryFin1 𝕜 E F).symm i) :
    0 < (p.leftInv i x).radius := by
  rw [leftInv_eq_rightInv _ _ _ h]
  exact radius_rightInv_pos_of_radius_pos hp

end FormalMultilinearSeries

/-!
### The inverse of an analytic open partial homeomorphism is analytic
-/

open FormalMultilinearSeries List

/-
**HasFPowerSeriesAt.tendsto_partialSum_prod_of_comp** 是 Mathlib 中的一个引理，位于命名空间 ``
。
形式化陈述：HasFPowerSeriesAt.tendsto_partialSum_prod_of_comp {f : E -> G} {q : Formal
MultilinearSeries 𝕜 F G} {p : FormalMultilinearSeries 𝕜 E F} {x : E} (hf : HasFP
owerSeriesAt f (q.comp p) x) (hq : 0 < q.radius) (hp : 0 < p.radius) : forallᶠ y
 in 𝓝 0, Tendsto (fun (a : Nat × Nat) => q.partialSum a.1 (p.partialSum a.2 y - 
p 0 (fun _ => 0))) atTop (𝓝 (f (x + y)))
参数：hf : HasFPowerSeriesAt f (q.comp p) x；hq : 0 < q.radius；hp : 0 < p.radius。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `FormalMultilinearSeries.comp_summable_nnreal`：comp_summable_nnreal (q : 
FormalMultilinearSeries 𝕜 F G) (p : FormalMultilinearSeries 𝕜 E F) (hq : 0 < q.r
adius) (hp : 0 < p.radius) : exist…
· 使用定理 `Metric.eball_mem_nhds`：eball_mem_nhds (x : α) {ε : Real>=0∞} (ε0 : 0 < ε
) : eball x ε in 𝓝 x
· 使用引理 `lt_min`：lt_min (h₁ : a < b) (h₂ : a < c) : a < min b c
· 使用定理 `HasFPowerSeriesOnBall.r_pos`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u
_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2
 : NormedSpace 𝕜 …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Metric.eball_subset_eball`：eball_subset_eball (h : ε₁ <= ε₂) : eball x ε
₁ subseteq eball x ε₂
· 使用引理 `min_le_left`：min_le_left (a b : α) : min a b <= a
· 使用定理 `cauchySeq_finset_of_norm_bounded`：cauchySeq_finset_of_norm_bounded {f : 
ι -> E} {g : ι -> Real} (hg : Summable g) (h : forall i, ‖f i‖ <= g i) : CauchyS
eq fun s : Finset ι =>…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `NNReal.summable_coe`：summable_coe {f : α -> Real>=0} : (Summable (fun a 
=> (f a : Real)) L) ↔ Summable f L
· 使用定理 `ContinuousMultilinearMap.le_opNorm`：le_opNorm (f : ContinuousMultilinear
Map 𝕜 E G) (m : forall i, E i) : ‖f m‖ <= ‖f‖ * ∏ i, ‖m i‖
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Finset.prod_const`：prod_const (b : M) : ∏ _x in s, b = b ^ #s
· 使用定理 `Finset.card_fin`：Finset.card_fin (n : Nat) : #(univ : Finset (Fin n)) = 
n
· 使用定理 `pow_le_pow_left₀`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 :
 Preorder M₀] {a b : M₀} [PosMulMono M₀] [MulPosMono M₀],   0 ≤ a → a ≤ b → ∀ (n
 : ℕ),…
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
（共 56 条，此处仅展示前 30 条）
-/
lemma HasFPowerSeriesAt.tendsto_partialSum_prod_of_comp
    {f : E → G} {q : FormalMultilinearSeries 𝕜 F G}
    {p : FormalMultilinearSeries 𝕜 E F} {x : E}
    (hf : HasFPowerSeriesAt f (q.comp p) x) (hq : 0 < q.radius) (hp : 0 < p.radius) :
    ∀ᶠ y in 𝓝 0, Tendsto (fun (a : ℕ × ℕ) ↦ q.partialSum a.1 (p.partialSum a.2 y
      - p 0 (fun _ ↦ 0))) atTop (𝓝 (f (x + y))) := by
  rcases hf with ⟨r0, h0⟩
  rcases q.comp_summable_nnreal p hq hp with ⟨r1, r1_pos : 0 < r1, hr1⟩
  let r : ℝ≥0∞ := min r0 r1
  have : Metric.eball (0 : E) r ∈ 𝓝 0 :=
    Metric.eball_mem_nhds 0 (lt_min h0.r_pos (by exact_mod_cast r1_pos))
  filter_upwards [this] with y hy
  have hy0 : y ∈ Metric.eball 0 r0 := Metric.eball_subset_eball (min_le_left _ _) hy
  have A : HasSum (fun i : Σ n, Composition n => q.compAlongComposition p i.2 fun _j => y)
      (f (x + y)) := by
    have cau : CauchySeq fun s : Finset (Σ n, Composition n) =>
        ∑ i ∈ s, q.compAlongComposition p i.2 fun _j => y := by
      apply cauchySeq_finset_of_norm_bounded (NNReal.summable_coe.2 hr1) _
      simp only [coe_nnnorm, NNReal.coe_mul, NNReal.coe_pow]
      rintro ⟨n, c⟩
      calc
        ‖(compAlongComposition q p c) fun _j : Fin n => y‖ ≤
            ‖compAlongComposition q p c‖ * ∏ _j : Fin n, ‖y‖ := by
          apply ContinuousMultilinearMap.le_opNorm
        _ ≤ ‖compAlongComposition q p c‖ * (r1 : ℝ) ^ n := by
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          rw [Finset.prod_const, Finset.card_fin]
          gcongr
          rw [Metric.mem_eball, edist_zero_right] at hy
          have := le_trans (le_of_lt hy) (min_le_right _ _)
          rwa [enorm_le_coe, ← NNReal.coe_le_coe, coe_nnnorm] at this
    apply HasSum.of_sigma (fun b ↦ hasSum_fintype _) ?_ cau
    simpa [FormalMultilinearSeries.comp] using h0.hasSum hy0
  have B : Tendsto (fun (n : ℕ × ℕ) => ∑ i ∈ compPartialSumTarget 0 n.1 n.2,
      q.compAlongComposition p i.2 fun _j => y) atTop (𝓝 (f (x + y))) := by
    apply Tendsto.comp A compPartialSumTarget_tendsto_prod_atTop
  have C : Tendsto (fun (n : ℕ × ℕ) => q.partialSum n.1 (∑ a ∈ Finset.Ico 1 n.2, p a fun _b ↦ y))
      atTop (𝓝 (f (x + y))) := by simpa [comp_partialSum] using B
  apply C.congr'
  filter_upwards [Ici_mem_atTop (0, 1)]
  rintro ⟨-, n⟩ ⟨-, (hn : 1 ≤ n)⟩
  congr
  rw [partialSum, eq_sub_iff_add_eq', Finset.range_eq_Ico,
        Finset.sum_eq_sum_Ico_succ_bot hn]
  congr with i
  exact i.elim0
/-
**HasFPowerSeriesAt.eventually_hasSum_of_comp** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：HasFPowerSeriesAt.eventually_hasSum_of_comp {f : E -> F} {g : F -> G} {q :
 FormalMultilinearSeries 𝕜 F G} {p : FormalMultilinearSeries 𝕜 E F} {x : E} (hgf
 : HasFPowerSeriesAt (g ∘ f) (q.comp p) x) (hf : HasFPowerSeriesAt f p x) (hq : 
0 < q.radius) : forallᶠ y in 𝓝 0, HasSum (fun n : Nat => q n fun _ : Fin n => (f
 (x + y) - f x)) (g (f (x + y)))
参数：hgf : HasFPowerSeriesAt (g ∘ f) (q.comp p) x；hf : HasFPowerSeriesAt f p x；hq 
: 0 < q.radius。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `ContinuousAt.sub`：∀ {G : Type u_1} {X : Type u_3} [inst : TopologicalSpa
ce X] [inst_1 : TopologicalSpace G] [inst_2 : Sub G]   [ContinuousSub G] {f g : 
X → G}…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `ContinuousAt.comp_of_eq`：ContinuousAt.comp_of_eq {g : Y -> Z} (hg : Cont
inuousAt g y) (hf : ContinuousAt f x) (hy : f x = y) : ContinuousAt (g ∘ f) x
· 使用定理 `HasFPowerSeriesAt.continuousAt`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Typ
e u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [ins
t_2 : NormedSpace 𝕜 …
· 使用定理 `ContinuousAt.const_add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [in
st_1 : Add M] [SeparatelyContinuousAdd M] {X : Type u_2}   [inst_3 : Topological
Space X] {f …
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `continuousAt_id'`：continuousAt_id' (y) : ContinuousAt (fun x : X => x) y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `continuousAt_const`：continuousAt_const : ContinuousAt (fun _ : X => y) x
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `Metric.eball_mem_nhds`：eball_mem_nhds (x : α) {ε : Real>=0∞} (ε0 : 0 < ε
) : eball x ε in 𝓝 x
· 使用定理 `ContinuousAt.preimage_mem_nhds`：ContinuousAt.preimage_mem_nhds {t : Set 
Y} (h : ContinuousAt f x) (ht : t in 𝓝 (f x)) : f ⁻¹' t in 𝓝 x
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `HasFPowerSeriesAt.tendsto_partialSum`：HasFPowerSeriesAt.tendsto_partialS
um (hf : HasFPowerSeriesAt f p x) : forallᶠ y in 𝓝 0, Tendsto (fun n => p.partia
lSum n y) atTop (𝓝 (f (x +…
· 使用引理 `HasFPowerSeriesAt.tendsto_partialSum_prod_of_comp`：HasFPowerSeriesAt.ten
dsto_partialSum_prod_of_comp {f : E -> G} {q : FormalMultilinearSeries 𝕜 F G} {p
 : FormalMultilinearSeries 𝕜 E F} {x : …
· 使用定理 `HasFPowerSeriesAt.radius_pos`：HasFPowerSeriesAt.radius_pos (hf : HasFPow
erSeriesAt f p x) : 0 < p.radius
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.HasBasis.tendsto_right_iff`：∀ {α : Type u_1} {β : Type u_2} {ι' :
 Sort u_5} {la : Filter α} {lb : Filter β} {pb : ι' → Prop} {sb : ι' → Set β}   
{f : α → β}, lb.HasBasi…
· 使用定理 `closed_nhds_basis`：closed_nhds_basis (x : X) : (𝓝 x).HasBasis (fun s : S
et X => s in 𝓝 x ∧ IsClosed s) id
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.regularSpace`：∀ {X : Type u_2} [i
nst : TopologicalSpace X] [TopologicalSpace.PseudoMetrizableSpace X], RegularSpa
ce X
（共 59 条，此处仅展示前 30 条）
-/
lemma HasFPowerSeriesAt.eventually_hasSum_of_comp {f : E → F} {g : F → G}
    {q : FormalMultilinearSeries 𝕜 F G} {p : FormalMultilinearSeries 𝕜 E F} {x : E}
    (hgf : HasFPowerSeriesAt (g ∘ f) (q.comp p) x) (hf : HasFPowerSeriesAt f p x)
    (hq : 0 < q.radius) :
    ∀ᶠ y in 𝓝 0, HasSum (fun n : ℕ => q n fun _ : Fin n => (f (x + y) - f x)) (g (f (x + y))) := by
  have : ∀ᶠ y in 𝓝 (0 : E), f (x + y) - f x ∈ Metric.eball 0 q.radius := by
    have A : ContinuousAt (fun y ↦ f (x + y) - f x) 0 := by
      apply ContinuousAt.sub _ continuousAt_const
      exact hf.continuousAt.comp_of_eq (by fun_prop) (by simp)
    have B : Metric.eball 0 q.radius ∈ 𝓝 (f (x + 0) - f x) := by
      simpa using Metric.eball_mem_nhds _ hq
    exact A.preimage_mem_nhds B
  filter_upwards [hgf.tendsto_partialSum_prod_of_comp hq (hf.radius_pos),
    hf.tendsto_partialSum, this] with y hy h'y h''y
  have L : Tendsto (fun n ↦ q.partialSum n (f (x + y) - f x)) atTop (𝓝 (g (f (x + y)))) := by
    apply (closed_nhds_basis (g (f (x + y)))).tendsto_right_iff.2
    rintro u ⟨hu, u_closed⟩
    simp only [id_eq, eventually_atTop]
    rcases mem_nhds_iff.1 hu with ⟨v, vu, v_open, hv⟩
    obtain ⟨a₀, b₀, hab⟩ : ∃ a₀ b₀, ∀ (a b : ℕ), a₀ ≤ a → b₀ ≤ b →
        q.partialSum a (p.partialSum b y - (p 0) fun _ ↦ 0) ∈ v := by
      simpa using hy (v_open.mem_nhds hv)
    refine ⟨a₀, fun a ha ↦ ?_⟩
    have : Tendsto (fun b ↦ q.partialSum a (p.partialSum b y - (p 0) fun _ ↦ 0)) atTop
        (𝓝 (q.partialSum a (f (x + y) - f x))) := by
      have : ContinuousAt (q.partialSum a) (f (x + y) - f x) :=
        (partialSum_continuous q a).continuousAt
      apply this.tendsto.comp
      apply Tendsto.sub h'y
      convert! tendsto_const_nhds
      exact (HasFPowerSeriesAt.coeff_zero hf fun _ ↦ 0).symm
    apply u_closed.mem_of_tendsto this
    filter_upwards [Ici_mem_atTop b₀] with b hb using vu (hab _ _ ha hb)
  have C : CauchySeq (fun (s : Finset ℕ) ↦ ∑ n ∈ s, q n fun _ : Fin n => (f (x + y) - f x)) := by
    have Z := q.summable_norm_apply (x := f (x + y) - f x) h''y
    exact cauchySeq_finset_of_norm_bounded Z (fun i ↦ le_rfl)
  exact tendsto_nhds_of_cauchySeq_of_subseq C tendsto_finset_range L

/-- If an open partial homeomorphism `f` is defined at `a` and has a power series expansion there
with invertible linear term, then `f.symm` has a power series expansion at `f a`, given by the
inverse of the initial power series. -/
/-
**OpenPartialHomeomorph.hasFPowerSeriesAt_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：OpenPartialHomeomorph.hasFPowerSeriesAt_symm (f : OpenPartialHomeomorph E 
F) {a : E} {i : E ≃L[𝕜] F} (h0 : a in f.source) {p : FormalMultilinearSeries 𝕜 E
 F} (h : HasFPowerSeriesAt f p a) (hp : p 1 = (continuousMultilinearCurryFin1 𝕜 
E F).symm i) : HasFPowerSeriesAt f.symm (p.leftInv i a) (f a)
参数：f : OpenPartialHomeomorph E F；h0 : a in f.source；h : HasFPowerSeriesAt f p a；
hp : p 1 = (continuousMultilinearCurryFin1 𝕜 E F).symm i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FormalMultilinearSeries.leftInv_comp`：leftInv_comp (p : FormalMultilinea
rSeries 𝕜 E F) (i : E ≃L[𝕜] F) (x : E) (h : p 1 = (continuousMultilinearCurryFin
1 𝕜 E F).symm i) : (leftIn…
· 使用定理 `ContinuousLinearMap.hasFPowerSeriesAt`：∀ {𝕜 : Type u_1} [inst : Nontrivi
allyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : No
rmedSpace 𝕜 E] {F : Type u_…
· 使用定理 `HasFPowerSeriesAt.congr`：HasFPowerSeriesAt.congr (hf : HasFPowerSeriesAt
 f p x) (hg : f =ᶠ[𝓝 x] g) : HasFPowerSeriesAt g p x
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `OpenPartialHomeomorph.open_source`：∀ {X : Type u_7} {Y : Type u_8} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : OpenPartialHomeom
orph X Y), IsOpen self.…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `OpenPartialHomeomorph.left_inv`：left_inv {x : X} (h : x in e.source) : e
.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `HasFPowerSeriesAt.eventually_hasSum_of_comp`：HasFPowerSeriesAt.eventuall
y_hasSum_of_comp {f : E -> F} {g : F -> G} {q : FormalMultilinearSeries 𝕜 F G} {
p : FormalMultilinearSeries 𝕜 E F…
· 使用定理 `FormalMultilinearSeries.radius_leftInv_pos_of_radius_pos`：radius_leftInv
_pos_of_radius_pos {p : FormalMultilinearSeries 𝕜 E F} {i : E ≃L[𝕜] F} {x : E} (
hp : 0 < p.radius) (h : p 1 = (continuousMulti…
· 使用定理 `HasFPowerSeriesAt.radius_pos`：HasFPowerSeriesAt.radius_pos (hf : HasFPow
erSeriesAt f p x) : 0 < p.radius
· 使用定理 `ContinuousAt.fun_sub`：∀ {G : Type u_1} {X : Type u_3} [inst : Topologica
lSpace X] [inst_1 : TopologicalSpace G] [inst_2 : Sub G]   [ContinuousSub G] {f 
g : X → G}…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `continuousAt_id'`：continuousAt_id' (y) : ContinuousAt (fun x : X => x) y
· 使用定理 `continuousAt_const`：continuousAt_const : ContinuousAt (fun _ : X => y) x
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b
· 使用定理 `ContinuousAt.preimage_mem_nhds`：ContinuousAt.preimage_mem_nhds {t : Set 
Y} (h : ContinuousAt f x) (ht : t in 𝓝 (f x)) : f ⁻¹' t in 𝓝 x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_zero_of_eq`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a = b
 → a - b = 0
（共 43 条，此处仅展示前 30 条）

--- 原说明 ---
If an open partial homeomorphism `f` is defined at `a` and has a power series ex
pansion there
with invertible linear term, then `f.symm` has a power series expansion at `f a`
, given by the
inverse of the initial power series.
-/
theorem OpenPartialHomeomorph.hasFPowerSeriesAt_symm (f : OpenPartialHomeomorph E F) {a : E}
    {i : E ≃L[𝕜] F} (h0 : a ∈ f.source) {p : FormalMultilinearSeries 𝕜 E F}
    (h : HasFPowerSeriesAt f p a) (hp : p 1 = (continuousMultilinearCurryFin1 𝕜 E F).symm i) :
    HasFPowerSeriesAt f.symm (p.leftInv i a) (f a) := by
  have A : HasFPowerSeriesAt (f.symm ∘ f) ((p.leftInv i a).comp p) a := by
    have : HasFPowerSeriesAt (ContinuousLinearMap.id 𝕜 E) ((p.leftInv i a).comp p) a := by
      rw [leftInv_comp _ _ _ hp]
      exact (ContinuousLinearMap.id 𝕜 E).hasFPowerSeriesAt a
    apply this.congr
    filter_upwards [f.open_source.mem_nhds h0] with x hx using by simp [hx]
  have B : ∀ᶠ (y : E) in 𝓝 0, HasSum (fun n ↦ (p.leftInv i a n) fun _ ↦ f (a + y) - f a)
      (f.symm (f (a + y))) := by
    simpa using! A.eventually_hasSum_of_comp h (radius_leftInv_pos_of_radius_pos h.radius_pos hp)
  have C : ∀ᶠ (y : E) in 𝓝 a, HasSum (fun n ↦ (p.leftInv i a n) fun _ ↦ f y - f a)
      (f.symm (f y)) := by
    rw [← sub_eq_zero_of_eq (a := a) rfl] at B
    have : ContinuousAt (fun x ↦ x - a) a := by fun_prop
    simpa using! this.preimage_mem_nhds B
  have D : ∀ᶠ (y : E) in 𝓝 (f.symm (f a)),
      HasSum (fun n ↦ (p.leftInv i a n) fun _ ↦ f y - f a) y := by
    simp only [h0, OpenPartialHomeomorph.left_inv]
    filter_upwards [C, f.open_source.mem_nhds h0] with x hx h'x
    simpa [h'x] using! hx
  have E : ∀ᶠ z in 𝓝 (f a), HasSum (fun n ↦ (p.leftInv i a n) fun _ ↦ f (f.symm z) - f a)
      (f.symm z) := by
    have : ContinuousAt f.symm (f a) := f.continuousAt_symm (f.map_source h0)
    exact this D
  have F : ∀ᶠ z in 𝓝 (f a), HasSum (fun n ↦ (p.leftInv i a n) fun _ ↦ z - f a) (f.symm z) := by
    filter_upwards [f.open_target.mem_nhds (f.map_source h0), E] with z hz h'z
    simpa [hz] using! h'z
  rcases EMetric.mem_nhds_iff.1 F with ⟨r, r_pos, hr⟩
  refine ⟨min r (p.leftInv i a).radius, min_le_right _ _,
    lt_min r_pos (radius_leftInv_pos_of_radius_pos h.radius_pos hp), fun {y} hy ↦ ?_⟩
  have : y + f a ∈ Metric.eball (f a) r := by
    simp only [Metric.mem_eball, edist_eq_enorm_sub, sub_zero, lt_min_iff,
      add_sub_cancel_right] at hy ⊢
    exact hy.1
  simpa [add_comm] using! hr this
