/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Jireh Loreaux
-/
module

public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Data.Fintype.Order
public import Mathlib.LinearAlgebra.Matrix.Basis
public import Mathlib.Analysis.Normed.Lp.ProdLp

/-!
# `L^p` distance on finite products of metric spaces

Given finitely many metric spaces, one can put the max distance on their product, but there is also
a whole family of natural distances, indexed by a parameter `p : ℝ≥0∞`, that also induce
the product topology. We define them in this file. For `0 < p < ∞`, the distance on `Π i, α i`
is given by
$$
d(x, y) = \left(\sum d(x_i, y_i)^p\right)^{1/p}.
$$,
whereas for `p = 0` it is the cardinality of the set ${i | d (x_i, y_i) ≠ 0}$. For `p = ∞` the
distance is the supremum of the distances.

We give instances of this construction for emetric spaces, metric spaces, normed groups and normed
spaces.

To avoid conflicting instances, all these are defined on a copy of the original Π-type, named
`PiLp p α`. The assumption `[Fact (1 ≤ p)]` is required for the metric and normed space instances.

We ensure that the topology, bornology and uniform structure on `PiLp p α` are (defeq to) the
product topology, product bornology and product uniformity, to be able to use freely continuity
statements for the coordinate functions, for instance.

If you wish to endow a type synonym of `Π i, α i` with the `L^p` distance, you can use
`pseudoMetricSpaceToPi` and the declarations below that one.

## Implementation notes

We only deal with the `L^p` distance on a product of finitely many metric spaces, which may be
distinct. A closely related construction is `lp`, the `L^p` norm on a product of (possibly
infinitely many) normed spaces, where the norm is
$$
\left(\sum ‖f (x)‖^p \right)^{1/p}.
$$
However, the topology induced by this construction is not the product topology, and some functions
have infinite `L^p` norm. These subtleties are not present in the case of finitely many metric
spaces, hence it is worth devoting a file to this specific case which is particularly well behaved.

Another related construction is `MeasureTheory.Lp`, the `L^p` norm on the space of functions from
a measure space to a normed space, where the norm is
$$
\left(\int ‖f (x)‖^p dμ\right)^{1/p}.
$$
This has all the same subtleties as `lp`, and the further subtlety that this only
defines a seminorm (as almost everywhere zero functions have zero `L^p` norm).
The construction `PiLp` corresponds to the special case of `MeasureTheory.Lp` in which the basis
is a finite space equipped with the counting measure.

To prove that the topology (and the uniform structure) on a finite product with the `L^p` distance
are the same as those coming from the `L^∞` distance, we could argue that the `L^p` and `L^∞` norms
are equivalent on `ℝ^n` for abstract (norm equivalence) reasons. Instead, we give a more explicit
(easy) proof which provides a comparison between these two norms with explicit constants.

We also set up the theory for `PseudoEMetricSpace` and `PseudoMetricSpace`.

## TODO

TODO: the results about uniformity and bornology in the `Aux` section should be using the tools in
`Mathlib.Topology.MetricSpace.Bilipschitz`, so that they can be inlined in the next section and
the only remaining results are about `Lipschitz` and `Antilipschitz`.
-/

@[expose] public section

open Module Real Set Filter RCLike Bornology Uniformity Topology NNReal ENNReal WithLp

noncomputable section

/-- A copy of a Pi type, on which we will put the `L^p` distance. Since the Pi type itself is
already endowed with the `L^∞` distance, we need the type synonym to avoid confusing typeclass
resolution. Also, we let it depend on `p`, to get a whole family of type on which we can put
different distances. -/
/-
**PiLp** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：PiLp (p : Real>=0∞) {ι : Type*} (α : ι -> Type*) : Type _
参数：p : Real>=0∞；α : ι -> Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A copy of a Pi type, on which we will put the `L^p` distance. Since the Pi type 
itself is
already endowed with the `L^∞` distance, we need the type synonym to avoid confu
sing typeclass
resolution. Also, we let it depend on `p`, to get a whole family of type on whic
h we can put
different distances.
-/
abbrev PiLp (p : ℝ≥0∞) {ι : Type*} (α : ι → Type*) : Type _ :=
  WithLp p (∀ i : ι, α i)

/-The following should not be a `FunLike` instance because then the coercion `⇑` would get
unfolded to `FunLike.coe` instead of `WithLp.equiv`. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The following should not be a `FunLike` instance because then the coercion `⇑` w
ould get
unfolded to `FunLike.coe` instead of `WithLp.equiv`.
-/
instance (p : ℝ≥0∞) {ι : Type*} (α : ι → Type*) : CoeFun (PiLp p α) (fun _ ↦ (i : ι) → α i) where
  coe := ofLp
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (p : ℝ≥0∞) {ι : Type*} (α : ι → Type*) [∀ i, Inhabited (α i)] : Inhabited (PiLp p α) :=
  ⟨toLp p fun _ => default⟩

@[ext]
/-
**PiLp.ext** 是 Mathlib 中的一个定理，位于命名空间 `PiLp`。
形式化陈述：∀ {p : ENNReal} {ι : Type u_1} {α : ι → Type u_2} {x y : PiLp p α}, (∀ (i 
: ι), x.ofLp i = y.ofLp i) → x = y
参数：∀ (i : ι), x.ofLp i = y.ofLp i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WithLp.ofLp_injective`：ofLp_injective : Function.Injective (@ofLp p V)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
protected theorem PiLp.ext {p : ℝ≥0∞} {ι : Type*} {α : ι → Type*} {x y : PiLp p α}
    (h : ∀ i, x i = y i) : x = y := ofLp_injective p <| funext h

namespace PiLp

variable (p : ℝ≥0∞) (𝕜 : Type*) {ι : Type*} (α : ι → Type*) (β : ι → Type*)
section
/- Register simplification lemmas for the applications of `PiLp` elements, as the usual lemmas
for Pi types will not trigger. -/
variable {𝕜 p α}
variable [Semiring 𝕜] [∀ i, SeminormedAddCommGroup (β i)]
variable [∀ i, Module 𝕜 (β i)] (c : 𝕜)
variable (x y : PiLp p β) (i : ι)

@[simp]
/-
**PiLp.zero_apply** 是 Mathlib 中的一个定理，位于命名空间 `PiLp`。
形式化陈述：zero_apply : (0 : PiLp p β) i = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zero_apply : (0 : PiLp p β) i = 0 :=
  rfl

@[simp]
/-
**PiLp.add_apply** 是 Mathlib 中的一个定理，位于命名空间 `PiLp`。
形式化陈述：add_apply : (x + y) i = x i + y i
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem add_apply : (x + y) i = x i + y i :=
  rfl

@[simp]
/-
**PiLp.sub_apply** 是 Mathlib 中的一个定理，位于命名空间 `PiLp`。
形式化陈述：sub_apply : (x - y) i = x i - y i
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sub_apply : (x - y) i = x i - y i :=
  rfl

@[simp]
/-
**PiLp.smul_apply** 是 Mathlib 中的一个定理，位于命名空间 `PiLp`。
形式化陈述：smul_apply : (c • x) i = c • x i
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_apply : (c • x) i = c • x i :=
  rfl

@[simp]
/-
**PiLp.neg_apply** 是 Mathlib 中的一个定理，位于命名空间 `PiLp`。
形式化陈述：neg_apply : (-x) i = -x i
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem neg_apply : (-x) i = -x i :=
  rfl

variable (p) in
/-- The projection on the `i`-th coordinate of `WithLp p (∀ i, α i)`, as a linear map. -/
@[simps!]
/-
**PiLp.proj** 是 Mathlib 中的一个定义，位于命名空间 `PiLp`。
形式化陈述：proj (i : ι) : PiLp p β ->L[𝕜] β i where __
参数：i : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The projection on the `i`-th coordinate of `WithLp p (∀ i, α i)`, as a linear ma
p.
-/
def projₗ (i : ι) : PiLp p β →ₗ[𝕜] β i :=
  (LinearMap.proj i : (∀ i, β i) →ₗ[𝕜] β i) ∘ₗ (WithLp.linearEquiv p 𝕜 (∀ i, β i)).toLinearMap

end

/-
**PiLp.toLp_apply** 是 Mathlib 中的一个引理，位于命名空间 `PiLp`。
形式化陈述：toLp_apply (x : forall i, α i) (i : ι) : toLp p x i = x i
参数：x : forall i, α i；i : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toLp_apply (x : ∀ i, α i) (i : ι) : toLp p x i = x i := rfl

section Single
variable [DecidableEq ι]
variable {β}

section Zero
variable [∀ i, Zero (β i)]

/-- The vector given in `PiLp` by being `a : β i` at coordinate `i : ι` and `0 : β j` at
all other coordinates `j`. -/
/-
**PiLp.single** 是 Mathlib 中的一个定义，位于命名空间 `PiLp`。
形式化陈述：single (i : ι) (a : β i) : PiLp p β
参数：i : ι；a : β i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The vector given in `PiLp` by being `a : β i` at coordinate `i : ι` and `0 : β j
` at
all other coordinates `j`.
-/
def single (i : ι) (a : β i) : PiLp p β := toLp p (Pi.single i a)

@[simp]
/-
**PiLp.ofLp_single** 是 Mathlib 中的一个引理，位于命名空间 `PiLp`。
形式化陈述：ofLp_single (i : ι) (a : β i) : ofLp (single p i a) = Pi.single i a
参数：i : ι；a : β i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofLp_single (i : ι) (a : β i) : ofLp (single p i a) = Pi.single i a := rfl

@[simp]
/-
**PiLp.toLp_single** 是 Mathlib 中的一个引理，位于命名空间 `PiLp`。
形式化陈述：toLp_single (i : ι) (a : β i) : toLp p (Pi.single i a) = single p i a
参数：i : ι；a : β i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toLp_single (i : ι) (a : β i) : toLp p (Pi.single i a) = single p i a := rfl

@[simp]
/-
**PiLp.single_eq_same** 是 Mathlib 中的一个引理，位于命名空间 `PiLp`。
形式化陈述：single_eq_same (i : ι) (a : β i) : single p i a i = a
参数：i : ι；a : β i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `PiLp.ofLp_single`：ofLp_single (i : ι) (a : β i) : ofLp (single p i a) = 
Pi.single i a
· 使用定理 `Pi.single_eq_same`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) →
 Zero (M i)] [inst_1 : DecidableEq ι] (i : ι) (x : M i),   Pi.single i x i = x
-/
lemma single_eq_same (i : ι) (a : β i) : single p i a i = a := by
  rw [ofLp_single, Pi.single_eq_same]

@[simp]
/-
**PiLp.single_eq_of_ne** 是 Mathlib 中的一个引理，位于命名空间 `PiLp`。
形式化陈述：single_eq_of_ne {i i' : ι} (h : i' != i) (a : β i) : single p i a i' = 0
参数：h : i' != i；a : β i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `PiLp.ofLp_single`：ofLp_single (i : ι) (a : β i) : ofLp (single p i a) = 
Pi.single i a
· 使用定理 `Pi.single_eq_of_ne`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) 
→ Zero (M i)] [inst_1 : DecidableEq ι] {i i' : ι},   i' ≠ i → ∀ (x : M i), Pi.si
ngle i x…
-/
lemma single_eq_of_ne {i i' : ι} (h : i' ≠ i) (a : β i) : single p i a i' = 0 := by
  rw [ofLp_single, Pi.single_eq_of_ne h]

/-- Changing the hypothesis direction in `PiLp.single_eq_of_ne` for for ease of use by simp. -/
@[simp]
/-
**PiLp.single_eq_of_ne'** 是 Mathlib 中的一个引理，位于命名空间 `PiLp`。
形式化陈述：single_eq_of_ne' {i i' : ι} (h : i != i') (a : β i) : single p i a i' = 0
参数：h : i != i'；a : β i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `PiLp.ofLp_single`：ofLp_single (i : ι) (a : β i) : ofLp (single p i a) = 
Pi.single i a
· 使用定理 `Pi.single_eq_of_ne'`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι)
 → Zero (M i)] [inst_1 : DecidableEq ι] {i i' : ι},   i ≠ i' → ∀ (x : M i), Pi.s
ingle i x…

--- 原说明 ---
Changing the hypothesis direction in `PiLp.single_eq_of_ne` for for ease of use 
by simp.
-/
lemma single_eq_of_ne' {i i' : ι} (h : i ≠ i') (a : β i) : single p i a i' = 0 := by
  rw [ofLp_single, Pi.single_eq_of_ne' h]

end Zero

@[simp]
/-
**PiLp.single_apply** 是 Mathlib 中的一个引理，位于命名空间 `PiLp`。
形式化陈述：single_apply [Zero 𝕜] (i : ι) (a : 𝕜) (j : ι) : (single p i a : PiLp p (fu
n _ => 𝕜)) j = ite (j = i) a 0
参数：i : ι；a : 𝕜；j : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `PiLp.toLp_single`：toLp_single (i : ι) (a : β i) : toLp p (Pi.single i a)
 = single p i a
· 使用引理 `PiLp.toLp_apply`：toLp_apply (x : forall i, α i) (i : ι) : toLp p x i = x
 i
· 使用定理 `Pi.single_apply`：∀ {ι : Type u_1} [inst : DecidableEq ι] {M : Type u_9} 
[inst_1 : Zero M] (i : ι) (x : M) (i' : ι),   Pi.single i x i' = if i' = i then 
x els…
-/
lemma single_apply [Zero 𝕜] (i : ι) (a : 𝕜) (j : ι) :
    (single p i a : PiLp p (fun _ ↦ 𝕜)) j = ite (j = i) a 0 := by
  rw [← toLp_single, PiLp.toLp_apply, ← Pi.single_apply i a j]

section AddCommGroup
variable [∀ i, AddCommGroup (β i)]

@[simp]
/-
**PiLp.single_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `PiLp`。
形式化陈述：single_eq_zero_iff (p : Real>=0∞) (i : ι) {a : β i} : single p i a = 0 ↔ a
 = 0
参数：p : Real>=0∞；i : ι。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `WithLp.toLp_eq_zero`：∀ (p : ENNReal) {V : Type u_4} [inst : AddCommGroup
 V] {x : V}, WithLp.toLp p x = 0 ↔ x = 0
· 使用定理 `Pi.single_eq_zero_iff`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : 
ι) → Zero (M i)] [inst_1 : DecidableEq ι] {i : ι} {x : M i},   Pi.single i x = 0
 ↔ x = 0
-/
theorem single_eq_zero_iff (p : ℝ≥0∞) (i : ι) {a : β i} :
    single p i a = 0 ↔ a = 0 :=
  (toLp_eq_zero p).trans Pi.single_eq_zero_iff
/-
**PiLp.single_add** 是 Mathlib 中的一个引理，位于命名空间 `PiLp`。
形式化陈述：single_add (p : Real>=0∞) (i : ι) {a b : β i} : single p i (a + b) = singl
e p i a + single p i b
参数：p : Real>=0∞；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Pi.single_add`：∀ {I : Type u} {f : I → Type v} [inst : DecidableEq I] [i
nst_1 : (i : I) → AddZeroClass (f i)] (i : I) (x y : f i),   Pi.single i (x + y)
 = …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma single_add (p : ℝ≥0∞) (i : ι) {a b : β i} :
    single p i (a + b) = single p i a + single p i b := by
  simp_rw [← toLp_single, Pi.single_add, toLp_add]
/-
**PiLp.single_sub** 是 Mathlib 中的一个引理，位于命名空间 `PiLp`。
形式化陈述：single_sub (p : Real>=0∞) (i : ι) {a b : β i} : single p i (a - b) = singl
e p i a - single p i b
参数：p : Real>=0∞；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Pi.single_sub`：∀ {I : Type u} {f : I → Type v} [inst : DecidableEq I] [i
nst_1 : (i : I) → AddGroup (f i)] (i : I) (x y : f i),   Pi.single i (x - y) = P
i.s…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma single_sub (p : ℝ≥0∞) (i : ι) {a b : β i} :
    single p i (a - b) = single p i a - single p i b := by
  simp_rw [← toLp_single, Pi.single_sub, toLp_sub]
/-
**PiLp.single_neg** 是 Mathlib 中的一个引理，位于命名空间 `PiLp`。
形式化陈述：single_neg (p : Real>=0∞) (i : ι) {a : β i} : single p i (-a) = -single p 
i a
参数：p : Real>=0∞；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Pi.single_neg`：∀ {I : Type u} {f : I → Type v} [inst : DecidableEq I] [i
nst_1 : (i : I) → AddGroup (f i)] (i : I) (x : f i),   Pi.single i (-x) = -Pi.si
ngl…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma single_neg (p : ℝ≥0∞) (i : ι) {a : β i} :
    single p i (-a) = -single p i a := by
  simp_rw [← toLp_single, Pi.single_neg, toLp_neg]

end AddCommGroup

section LinearIndependent

/-
**PiLp.linearIndependent_single** 是 Mathlib 中的一个定理，位于命名空间 `PiLp`。
形式化陈述：linearIndependent_single [Semiring 𝕜] {η : Type*} {ιs : η -> Type*} {Ms : 
η -> Type*} [forall i, AddCommGroup (Ms i)] [forall i, Module 𝕜 (Ms i)] [Decidab
leEq η] (v : forall j, ιs j -> Ms j) (hs : forall i, LinearIndependent 𝕜 (v i)) 
: LinearIndependent 𝕜 fun ji : Σ j, ιs j => single p ji.1 (v ji.1 ji.2)
参数：Ms i；Ms i；v : forall j, ιs j -> Ms j；hs : forall i, LinearIndependent 𝕜 (v i)
。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.linearIndependent_iff_of_injOn`：∀ {ι : Type u'} {R : Type u_2}
 {M : Type u_4} {M' : Type u_5} {v : ι → M} [inst : Semiring R] [inst_1 : AddCom
mMonoid M]   [inst_2 : AddComm…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `WithLp.linearEquiv_symm_apply`：∀ (p : ENNReal) (K : Type u_1) (V : Type 
u_4) [inst : Semiring K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V] 
  (a : V), (WithLp.…
· 使用定理 `WithLp.addEquiv_symm_apply`：∀ (p : ENNReal) (V : Type u_4) [inst : AddCo
mmGroup V] (ofLp : V), (WithLp.addEquiv p V).symm ofLp = WithLp.toLp p ofLp
· 使用定理 `WithLp.toLp.injEq`：∀ (p : ENNReal) {V : Type u_1} (ofLp ofLp_1 : V), (Wi
thLp.toLp p ofLp = WithLp.toLp p ofLp_1) = (ofLp = ofLp_1)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Pi.linearIndependent_single`：linearIndependent_single [Semiring R] [fora
ll i, AddCommMonoid (Ms i)] [forall i, Module R (Ms i)] [DecidableEq η] (v : for
all j, ιs j -> Ms…
-/
theorem linearIndependent_single [Semiring 𝕜] {η : Type*} {ιs : η → Type*}
    {Ms : η → Type*} [∀ i, AddCommGroup (Ms i)] [∀ i, Module 𝕜 (Ms i)] [DecidableEq η]
    (v : ∀ j, ιs j → Ms j) (hs : ∀ i, LinearIndependent 𝕜 (v i)) :
    LinearIndependent 𝕜 fun ji : Σ j, ιs j ↦ single p ji.1 (v ji.1 ji.2) := by
  suffices LinearIndependent 𝕜 ((WithLp.linearEquiv p 𝕜 _).symm.toLinearMap ∘
      fun ji : Σ j, ιs j ↦ Pi.single ji.1 (v ji.1 ji.2)) by
    simpa
  rw [LinearMap.linearIndependent_iff_of_injOn _ (by simp)]
  exact Pi.linearIndependent_single v hs
/-
**PiLp.linearIndependent_single_one** 是 Mathlib 中的一个定理，位于命名空间 `PiLp`。
形式化陈述：linearIndependent_single_one [Ring 𝕜] : LinearIndependent 𝕜 (fun i : ι => 
single p i (1 : 𝕜))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.linearIndependent_iff_of_injOn`：∀ {ι : Type u'} {R : Type u_2}
 {M : Type u_4} {M' : Type u_5} {v : ι → M} [inst : Semiring R] [inst_1 : AddCom
mMonoid M]   [inst_2 : AddComm…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `WithLp.linearEquiv_symm_apply`：∀ (p : ENNReal) (K : Type u_1) (V : Type 
u_4) [inst : Semiring K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V] 
  (a : V), (WithLp.…
· 使用定理 `WithLp.addEquiv_symm_apply`：∀ (p : ENNReal) (V : Type u_4) [inst : AddCo
mmGroup V] (ofLp : V), (WithLp.addEquiv p V).symm ofLp = WithLp.toLp p ofLp
· 使用定理 `WithLp.toLp.injEq`：∀ (p : ENNReal) {V : Type u_1} (ofLp ofLp_1 : V), (Wi
thLp.toLp p ofLp = WithLp.toLp p ofLp_1) = (ofLp = ofLp_1)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Pi.linearIndependent_single_one`：linearIndependent_single_one (ι R : Typ
e*) [Semiring R] [DecidableEq ι] : LinearIndependent R (fun i : ι => Pi.single i
 (1 : R))
-/
theorem linearIndependent_single_one [Ring 𝕜] :
    LinearIndependent 𝕜 (fun i : ι ↦ single p i (1 : 𝕜)) := by
  suffices LinearIndependent 𝕜 ((WithLp.linearEquiv p 𝕜 _).symm.toLinearMap ∘
      fun i : ι ↦ Pi.single i (1 : 𝕜)) by
    simpa
  rw [LinearMap.linearIndependent_iff_of_injOn _ (by simp)]
  exact Pi.linearIndependent_single_one ι 𝕜
/-
**PiLp.linearIndependent_single_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `PiLp`。
形式化陈述：linearIndependent_single_of_ne_zero [Ring 𝕜] [IsDomain 𝕜] {M : Type*} [Add
CommGroup M] [Module 𝕜 M] [IsTorsionFree 𝕜 M] {v : ι -> M} (hv : forall i, v i !
= 0) : LinearIndependent 𝕜 fun i : ι => single p i (v i)
参数：hv : forall i, v i != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.linearIndependent_iff_of_injOn`：∀ {ι : Type u'} {R : Type u_2}
 {M : Type u_4} {M' : Type u_5} {v : ι → M} [inst : Semiring R] [inst_1 : AddCom
mMonoid M]   [inst_2 : AddComm…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `WithLp.linearEquiv_symm_apply`：∀ (p : ENNReal) (K : Type u_1) (V : Type 
u_4) [inst : Semiring K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V] 
  (a : V), (WithLp.…
· 使用定理 `WithLp.addEquiv_symm_apply`：∀ (p : ENNReal) (V : Type u_4) [inst : AddCo
mmGroup V] (ofLp : V), (WithLp.addEquiv p V).symm ofLp = WithLp.toLp p ofLp
· 使用定理 `WithLp.toLp.injEq`：∀ (p : ENNReal) {V : Type u_1} (ofLp ofLp_1 : V), (Wi
thLp.toLp p ofLp = WithLp.toLp p ofLp_1) = (ofLp = ofLp_1)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用引理 `Pi.linearIndependent_single_of_ne_zero`：linearIndependent_single_of_ne_z
ero [Ring R] [IsDomain R] [AddCommGroup M] [Module R M] [IsTorsionFree R M] [Dec
idableEq ι] {v : ι -> M} (hv…
-/
theorem linearIndependent_single_of_ne_zero [Ring 𝕜] [IsDomain 𝕜] {M : Type*}
    [AddCommGroup M] [Module 𝕜 M] [IsTorsionFree 𝕜 M] {v : ι → M} (hv : ∀ i, v i ≠ 0) :
    LinearIndependent 𝕜 fun i : ι ↦ single p i (v i) := by
  suffices LinearIndependent 𝕜 ((WithLp.linearEquiv p 𝕜 _).symm.toLinearMap ∘
      fun i : ι ↦ Pi.single i (v i)) by
    simpa
  rw [LinearMap.linearIndependent_iff_of_injOn _ (by simp)]
  exact Pi.linearIndependent_single_of_ne_zero hv

end LinearIndependent

end Single

section DistNorm

variable [Fintype ι]

/-!
### Definition of `edist`, `dist` and `norm` on `PiLp`

In this section we define the `edist`, `dist` and `norm` functions on `PiLp p α` without assuming
`[Fact (1 ≤ p)]` or metric properties of the spaces `α i`. This allows us to provide the rewrite
lemmas for each of three cases `p = 0`, `p = ∞` and `0 < p.to_real`.
-/


section EDist

variable [∀ i, EDist (β i)]

/-- Endowing the space `PiLp p β` with the `L^p` edistance. We register this instance
separate from `pi_Lp.pseudo_emetric` since the latter requires the type class hypothesis
`[Fact (1 ≤ p)]` in order to prove the triangle inequality.

Registering this separately allows for a future emetric-like structure on `PiLp p β` for `p < 1`
satisfying a relaxed triangle inequality. The terminology for this varies throughout the
literature, but it is sometimes called a *quasi-metric* or *semi-metric*. -/
/-
**PiLp.** 是 Mathlib 中的一个实例，位于命名空间 `PiLp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Endowing the space `PiLp p β` with the `L^p` edistance. We register this instanc
e
separate from `pi_Lp.pseudo_emetric` since the latter requires the type class hy
pothesis
`[Fact (1 ≤ p)]` in order to prove the triangle inequality.

Registering this separately allows for a future emetric-like structure on `PiLp 
p β` for `p < 1`
satisfying a relaxed triangle inequality. The terminology for this varies throug
hout the
literature, but it is sometimes called a *quasi-metric* or *semi-metric*.
-/
instance : EDist (PiLp p β) where
  edist f g :=
    if p = 0 then {i | edist (f i) (g i) ≠ 0}.toFinite.toFinset.card
    else
      if p = ∞ then ⨆ i, edist (f i) (g i) else (∑ i, edist (f i) (g i) ^ p.toReal) ^ (1 / p.toReal)

variable {β}
/-
**PiLp.edist_eq_card** 是 Mathlib 中的一个定理，位于命名空间 `PiLp`。
形式化陈述：edist_eq_card (f g : PiLp 0 β) : edist f g = {i | edist (f i) (g i) != 0}.
toFinite.toFinset.card
参数：f g : PiLp 0 β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
theorem edist_eq_card (f g : PiLp 0 β) :
    edist f g = {i | edist (f i) (g i) ≠ 0}.toFinite.toFinset.card :=
  if_pos rfl
/-
**PiLp.edist_eq_sum** 是 Mathlib 中的一个定理，位于命名空间 `PiLp`。
形式化陈述：edist_eq_sum {p : Real>=0∞} (hp : 0 < p.toReal) (f g : PiLp p β) : edist f
 g = (∑ i, edist (f i) (g i) ^ p.toReal) ^ (1 / p.toReal)
参数：hp : 0 < p.toReal；f g : PiLp p β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ENNReal.toReal_pos_iff`：toReal_pos_iff : 0 < a.toReal ↔ 0 < a ∧ a < ∞
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem edist_eq_sum {p : ℝ≥0∞} (hp : 0 < p.toReal) (f g : PiLp p β) :
    edist f g = (∑ i, edist (f i) (g i) ^ p.toReal) ^ (1 / p.toReal) :=
  let hp' := ENNReal.toReal_pos_iff.mp hp
  (if_neg hp'.1.ne').trans (if_neg hp'.2.ne)
/-
**PiLp.edist_eq_iSup** 是 Mathlib 中的一个定理，位于命名空间 `PiLp`。
形式化陈述：edist_eq_iSup (f g : PiLp ∞ β) : edist f g = ⨆ i, edist (f i) (g i)
参数：f g : PiLp ∞ β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem edist_eq_iSup (f g : PiLp ∞ β) : edist f g = ⨆ i, edist (f i) (g i) := rfl

end EDist

section EDistProp

variable {β}
variable [∀ i, PseudoEMetricSpace (β i)]

/-- This holds independent of `p` and does not require `[Fact (1 ≤ p)]`. We keep it separate
from `pi_Lp.pseudo_emetric_space` so it can be used also for `p < 1`. -/
/-
**PiLp.edist_self** 是 Mathlib 中的一个定理，位于命名空间 `PiLp`。
形式化陈述：∀ (p : ENNReal) {ι : Type u_2} {β : ι → Type u_4} [inst : Fintype ι] [inst
_1 : (i : ι) → PseudoEMetricSpace (β i)]   (f : PiLp p β), edist f f = 0
参数：p : ENNReal；i : ι；β i；f : PiLp p β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.trichotomy`：∀ (p : ENNReal), p = 0 ∨ p = ⊤ ∨ 0 < p.toReal
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `PiLp.edist_eq_card`：edist_eq_card (f g : PiLp 0 β) : edist f g = {i | ed
ist (f i) (g i) != 0}.toFinite.toFinset.card
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `PseudoEMetricSpace.edist_self`：∀ {α : Type u} [self : PseudoEMetricSpace
 α] (x : α), edist x x = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Set.Finite.toFinset.congr_simp`：∀ {α : Type u} {s s_1 : Set α} (e_s : s 
= s_1) (h : s.Finite), h.toFinset = ⋯.toFinset
· 使用定理 `Set.Finite.toFinset_ofPred`：∀ {α : Type u} [inst : Fintype α] (p : α → P
rop) [inst_1 : DecidablePred p] (h : {x | p x}.Finite),   h.toFinset = {x | p x}
· 使用定理 `Finset.filter_false`：∀ {α : Type u_1} {h : DecidablePred fun x => False}
 (s : Finset α), {x ∈ s | False} = ∅
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.iSup_zero`：∀ {ι : Sort u_1}, ⨆ x, 0 = 0
· 使用定理 `PiLp.edist_eq_sum`：edist_eq_sum {p : Real>=0∞} (hp : 0 < p.toReal) (f g 
: PiLp p β) : edist f g = (∑ i, edist (f i) (g i) ^ p.toReal) ^ (1 / p.toReal)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `ENNReal.zero_rpow_of_pos`：zero_rpow_of_pos {y : Real} (h : 0 < y) : (0 :
 Real>=0∞) ^ y = 0
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inv_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : PartialOr
der G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a⁻¹ ↔ 0 < a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R

--- 原说明 ---
This holds independent of `p` and does not require `[Fact (1 ≤ p)]`. We keep it 
separate
from `pi_Lp.pseudo_emetric_space` so it can be used also for `p < 1`.
-/
protected theorem edist_self (f : PiLp p β) : edist f f = 0 := by
  rcases p.trichotomy with (rfl | rfl | h)
  · simp [edist_eq_card]
  · simp [edist_eq_iSup]
  · simp [edist_eq_sum h, ENNReal.zero_rpow_of_pos h, ENNReal.zero_rpow_of_pos (inv_pos.2 <| h)]

/-- This holds independent of `p` and does not require `[Fact (1 ≤ p)]`. We keep it separate
from `pi_Lp.pseudo_emetric_space` so it can be used also for `p < 1`. -/
/-
**PiLp.edist_comm** 是 Mathlib 中的一个定理，位于命名空间 `PiLp`。
形式化陈述：∀ (p : ENNReal) {ι : Type u_2} {β : ι → Type u_4} [inst : Fintype ι] [inst
_1 : (i : ι) → PseudoEMetricSpace (β i)]   (f g : PiLp p β), edist f g = edist g
 f
参数：p : ENNReal；i : ι；β i；f g : PiLp p β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.trichotomy`：∀ (p : ENNReal), p = 0 ∨ p = ⊤ ∨ 0 < p.toReal
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `PseudoEMetricSpace.edist_comm`：∀ {α : Type u} [self : PseudoEMetricSpace
 α] (x y : α), edist x y = edist y x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `PiLp.edist_eq_card`：edist_eq_card (f g : PiLp 0 β) : edist f g = {i | ed
ist (f i) (g i) != 0}.toFinite.toFinset.card
· 使用定理 `Set.Finite.toFinset.congr_simp`：∀ {α : Type u} {s s_1 : Set α} (e_s : s 
= s_1) (h : s.Finite), h.toFinset = ⋯.toFinset
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PiLp.edist_eq_sum`：edist_eq_sum {p : Real>=0∞} (hp : 0 < p.toReal) (f g 
: PiLp p β) : edist f g = (∑ i, edist (f i) (g i) ^ p.toReal) ^ (1 / p.toReal)
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…

--- 原说明 ---
This holds independent of `p` and does not require `[Fact (1 ≤ p)]`. We keep it 
separate
from `pi_Lp.pseudo_emetric_space` so it can be used also for `p < 1`.
-/
protected theorem edist_comm (f g : PiLp p β) : edist f g = edist g f := by
  rcases p.trichotomy with (rfl | rfl | h)
  · simp only [edist_eq_card, edist_comm]
  · simp only [edist_eq_iSup, edist_comm]
  · simp only [edist_eq_sum h, edist_comm]

end EDistProp

section Dist

variable [∀ i, Dist (α i)]

/-- Endowing the space `PiLp p β` with the `L^p` distance. We register this instance
separate from `pi_Lp.pseudo_metric` since the latter requires the type class hypothesis
`[Fact (1 ≤ p)]` in order to prove the triangle inequality.

Registering this separately allows for a future metric-like structure on `PiLp p β` for `p < 1`
satisfying a relaxed triangle inequality. The terminology for this varies throughout the
literature, but it is sometimes called a *quasi-metric* or *semi-metric*. -/
/-
**PiLp.** 是 Mathlib 中的一个实例，位于命名空间 `PiLp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Endowing the space `PiLp p β` with the `L^p` distance. We register this instance
separate from `pi_Lp.pseudo_metric` since the latter requires the type class hyp
othesis
`[Fact (1 ≤ p)]` in order to prove the triangle inequality.

Registering this separately allows for a future metric-like structure on `PiLp p
 β` for `p < 1`
satisfying a relaxed triangle inequality. The terminology for this varies throug
hout the
literature, but it is sometimes called a *quasi-metric* or *semi-metric*.
-/
instance : Dist (PiLp p α) where
  dist f g :=
    if p = 0 then {i | dist (f i) (g i) ≠ 0}.toFinite.toFinset.card
    else
      if p = ∞ then ⨆ i, dist (f i) (g i) else (∑ i, dist (f i) (g i) ^ p.toReal) ^ (1 / p.toReal)

variable {α}
/-
**PiLp.dist_eq_card** 是 Mathlib 中的一个定理，位于命名空间 `PiLp`。
形式化陈述：dist_eq_card (f g : PiLp 0 α) : dist f g = {i | dist (f i) (g i) != 0}.toF
inite.toFinset.card
参数：f g : PiLp 0 α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
theorem dist_eq_card (f g : PiLp 0 α) :
    dist f g = {i | dist (f i) (g i) ≠ 0}.toFinite.toFinset.card :=
  if_pos rfl
/-
**PiLp.dist_eq_sum** 是 Mathlib 中的一个定理，位于命名空间 `PiLp`。
形式化陈述：dist_eq_sum {p : Real>=0∞} (hp : 0 < p.toReal) (f g : PiLp p α) : dist f g
 = (∑ i, dist (f i) (g i) ^ p.toReal) ^ (1 / p.toReal)
参数：hp : 0 < p.toReal；f g : PiLp p α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ENNReal.toReal_pos_iff`：toReal_pos_iff : 0 < a.toReal ↔ 0 < a ∧ a < ∞
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem dist_eq_sum {p : ℝ≥0∞} (hp : 0 < p.toReal) (f g : PiLp p α) :
    dist f g = (∑ i, dist (f i) (g i) ^ p.toReal) ^ (1 / p.toReal) :=
  let hp' := ENNReal.toReal_pos_iff.mp hp
  (if_neg hp'.1.ne').trans (if_neg hp'.2.ne)
/-
**PiLp.dist_eq_iSup** 是 Mathlib 中的一个定理，位于命名空间 `PiLp`。
形式化陈述：dist_eq_iSup (f g : PiLp ∞ α) : dist f g = ⨆ i, dist (f i) (g i)
参数：f g : PiLp ∞ α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem dist_eq_iSup (f g : PiLp ∞ α) : dist f g = ⨆ i, dist (f i) (g i) := rfl

end Dist

section Norm

variable [∀ i, Norm (β i)]

/-- Endowing the space `PiLp p β` with the `L^p` norm. We register this instance
separate from `PiLp.seminormedAddCommGroup` since the latter requires the type class hypothesis
`[Fact (1 ≤ p)]` in order to prove the triangle inequality.

Registering this separately allows for a future norm-like structure on `PiLp p β` for `p < 1`
satisfying a relaxed triangle inequality. These are called *quasi-norms*. -/
/-
**PiLp.instNorm** 是 Mathlib 中的一个实例，位于命名空间 `PiLp`。
形式化陈述：instNorm : Norm (PiLp p β) where norm f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Endowing the space `PiLp p β` with the `L^p` norm. We register this instance
separate from `PiLp.seminormedAddCommGroup` since the latter requires the type c
lass hypothesis
`[Fact (1 ≤ p)]` in order to prove the triangle inequality.

Registering this separately allows for a future norm-like structure on `PiLp p β
` for `p < 1`
satisfying a relaxed triangle inequality. These are called *quasi-norms*.
-/
instance instNorm : Norm (PiLp p β) where
  norm f :=
    if p = 0 then {i | ‖f i‖ ≠ 0}.toFinite.toFinset.card
    else if p = ∞ then ⨆ i, ‖f i‖ else (∑ i, ‖f i‖ ^ p.toReal) ^ (1 / p.toReal)

variable {p β}
/-
**PiLp.norm_eq_card** 是 Mathlib 中的一个定理，位于命名空间 `PiLp`。
形式化陈述：norm_eq_card (f : PiLp 0 β) : ‖f‖ = {i | ‖f i‖ != 0}.toFinite.toFinset.car
d
参数：f : PiLp 0 β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
theorem norm_eq_card (f : PiLp 0 β) : ‖f‖ = {i | ‖f i‖ ≠ 0}.toFinite.toFinset.card :=
  if_pos rfl
/-
**PiLp.norm_eq_ciSup** 是 Mathlib 中的一个定理，位于命名空间 `PiLp`。
形式化陈述：norm_eq_ciSup (f : PiLp ∞ β) : ‖f‖ = ⨆ i, ‖f i‖
参数：f : PiLp ∞ β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem norm_eq_ciSup (f : PiLp ∞ β) : ‖f‖ = ⨆ i, ‖f i‖ := rfl
/-
**PiLp.norm_eq_sum** 是 Mathlib 中的一个定理，位于命名空间 `PiLp`。
形式化陈述：norm_eq_sum (hp : 0 < p.toReal) (f : PiLp p β) : ‖f‖ = (∑ i, ‖f i‖ ^ p.toR
eal) ^ (1 / p.toReal)
参数：hp : 0 < p.toReal；f : PiLp p β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ENNReal.toReal_pos_iff`：toReal_pos_iff : 0 < a.toReal ↔ 0 < a ∧ a < ∞
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem norm_eq_sum (hp : 0 < p.toReal) (f : PiLp p β) :
    ‖f‖ = (∑ i, ‖f i‖ ^ p.toReal) ^ (1 / p.toReal) :=
  let hp' := ENNReal.toReal_pos_iff.mp hp
  (if_neg hp'.1.ne').trans (if_neg hp'.2.ne)

end Norm

end DistNorm

section Aux

/-!
### The uniformity on finite `L^p` products is the product uniformity

In this section, we put the `L^p` edistance on `PiLp p α`, and we check that the uniformity
coming from this edistance coincides with the product uniformity, by showing that the canonical
map to the Pi type (with the `L^∞` distance) is a uniform embedding, as it is both Lipschitz and
antiLipschitz.

We only register this emetric space structure as a temporary instance, as the true instance (to be
registered later) will have as uniformity exactly the product uniformity, instead of the one coming
from the edistance (which is equal to it, but not defeq). See Note [forgetful inheritance]
explaining why having definitionally the right uniformity is often important.

TODO: the results about uniformity and bornology should be using the tools in
`Mathlib.Topology.MetricSpace.Bilipschitz`, so that they can be inlined in the next section and
the only remaining results are about `Lipschitz` and `Antilipschitz`.
-/


variable [Fact (1 ≤ p)] [∀ i, PseudoMetricSpace (α i)] [∀ i, PseudoEMetricSpace (β i)]
variable [Fintype ι]

/-- Endowing the space `PiLp p β` with the `L^p` pseudoemetric structure. This definition is not
satisfactory, as it does not register the fact that the topology and the uniform structure coincide
with the product one. Therefore, we do not register it as an instance. Using this as a temporary
pseudoemetric space instance, we will show that the uniform structure is equal (but not defeq) to
the product one, and then register an instance in which we replace the uniform structure by the
product one using this pseudoemetric space and `PseudoEMetricSpace.replaceUniformity`. -/
@[instance_reducible]
/-
**PiLp.pseudoEmetricAux** 是 Mathlib 中的一个定义，位于命名空间 `PiLp`。
形式化陈述：pseudoEmetricAux : PseudoEMetricSpace (PiLp p β) where edist_self
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `PiLp.edist_self`：∀ (p : ENNReal) {ι : Type u_2} {β : ι → Type u_4} [inst
 : Fintype ι] [inst_1 : (i : ι) → PseudoEMetricSpace (β i)]   (f : PiLp p β), ed
ist f…
· 使用定理 `PiLp.edist_comm`：∀ (p : ENNReal) {ι : Type u_2} {β : ι → Type u_4} [inst
 : Fintype ι] [inst_1 : (i : ι) → PseudoEMetricSpace (β i)]   (f g : PiLp p β), 
edist…

--- 原说明 ---
Endowing the space `PiLp p β` with the `L^p` pseudoemetric structure. This defin
ition is not
satisfactory, as it does not register the fact that the topology and the uniform
 structure coincide
with the product one. Therefore, we do not register it as an instance. Using thi
s as a temporary
pseudoemetric space instance, we will show that the uniform structure is equal (
but not defeq) to
the product one, and then register an instance in which we replace the uniform s
tructure by the
product one using this pseudoemetric space and `PseudoEMetricSpace.replaceUnifor
mity`.
-/
def pseudoEmetricAux : PseudoEMetricSpace (PiLp p β) where
  edist_self := PiLp.edist_self p
  edist_comm := PiLp.edist_comm p
  edist_triangle f g h := by
    rcases p.dichotomy with (rfl | hp)
    · simp only [edist_eq_iSup]
      cases isEmpty_or_nonempty ι
      · simp only [ciSup_of_empty, ENNReal.bot_eq_zero, add_zero, nonpos_iff_eq_zero]
      -- Porting note: `le_iSup` needed some help
      refine
        iSup_le fun i => (edist_triangle _ (g i) _).trans <| add_le_add
            (le_iSup (fun k => edist (f k) (g k)) i) (le_iSup (fun k => edist (g k) (h k)) i)
    · simp only [edist_eq_sum (zero_lt_one.trans_le hp)]
      calc
        (∑ i, edist (f i) (h i) ^ p.toReal) ^ (1 / p.toReal) ≤
            (∑ i, (edist (f i) (g i) + edist (g i) (h i)) ^ p.toReal) ^ (1 / p.toReal) := by
          gcongr
          apply edist_triangle
        _ ≤
            (∑ i, edist (f i) (g i) ^ p.toReal) ^ (1 / p.toReal) +
              (∑ i, edist (g i) (h i) ^ p.toReal) ^ (1 / p.toReal) :=
          ENNReal.Lp_add_le _ _ _ hp

attribute [local instance] PiLp.pseudoEmetricAux

set_option backward.isDefEq.respectTransparency false in
/-- An auxiliary lemma used twice in the proof of `PiLp.pseudoMetricAux` below. Not intended for
use outside this file. -/
/-
**PiLp.iSup_edist_ne_top_aux** 是 Mathlib 中的一个定理，位于命名空间 `PiLp`。
形式化陈述：iSup_edist_ne_top_aux {ι : Type*} [Finite ι] {α : ι -> Type*} [forall i, P
seudoMetricSpace (α i)] (f g : PiLp ∞ α) : (⨆ i, edist (f i) (g i)) != ⊤
参数：α i；f g : PiLp ∞ α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `dist_nonneg`：dist_nonneg {x y : α} : 0 <= dist x y
· 使用定理 `Finite.exists_le`：Finite.exists_le [IsDirectedOrder α] (f : ι -> α) : ex
ists M, forall i, f i <= M
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `PseudoMetricSpace.edist_dist`：∀ {α : Type u} [self : PseudoMetricSpace α
] (x y : α), PseudoMetricSpace.edist x y = ENNReal.ofReal (dist x y)
· 使用定理 `ENNReal.ofReal_eq_coe_nnreal`：ofReal_eq_coe_nnreal {x : Real} (h : 0 <= 
x) : ENNReal.ofReal x = ofNNReal (NNReal.mk x h)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.coe_lt_top`：∀ {r : NNReal}, ↑r < ⊤

--- 原说明 ---
An auxiliary lemma used twice in the proof of `PiLp.pseudoMetricAux` below. Not 
intended for
use outside this file.
-/
theorem iSup_edist_ne_top_aux {ι : Type*} [Finite ι] {α : ι → Type*}
    [∀ i, PseudoMetricSpace (α i)] (f g : PiLp ∞ α) : (⨆ i, edist (f i) (g i)) ≠ ⊤ := by
  cases nonempty_fintype ι
  obtain ⟨M, hM⟩ := Finite.exists_le fun i => (⟨dist (f i) (g i), dist_nonneg⟩ : ℝ≥0)
  refine ne_of_lt ((iSup_le fun i => ?_).trans_lt (@ENNReal.coe_lt_top M))
  simp only [edist, PseudoMetricSpace.edist_dist, ENNReal.ofReal_eq_coe_nnreal dist_nonneg]
  exact mod_cast hM i

/-- Endowing the space `PiLp p α` with the `L^p` pseudometric structure. This definition is not
satisfactory, as it does not register the fact that the topology, the uniform structure, and the
bornology coincide with the product ones. Therefore, we do not register it as an instance. Using
this as a temporary pseudoemetric space instance, we will show that the uniform structure is equal
(but not defeq) to the product one, and then register an instance in which we replace the uniform
structure and the bornology by the product ones using this pseudometric space,
`PseudoMetricSpace.replaceUniformity`, and `PseudoMetricSpace.replaceBornology`.

See note [reducible non-instances] -/
/-
**PiLp.pseudoMetricAux** 是 Mathlib 中的一个缩写定义，位于命名空间 `PiLp`。
形式化陈述：pseudoMetricAux : PseudoMetricSpace (PiLp p α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Endowing the space `PiLp p α` with the `L^p` pseudometric structure. This defini
tion is not
satisfactory, as it does not register the fact that the topology, the uniform st
ructure, and the
bornology coincide with the product ones. Therefore, we do not register it as an
 instance. Using
this as a temporary pseudoemetric space instance, we will show that the uniform 
structure is equal
(but not defeq) to the product one, and then register an instance in which we re
place the uniform
structure and the bornology by the product ones using this pseudometric space,
`PseudoMetricSpace.replaceUniformity`, and `PseudoMetricSpace.replaceBornology`.

See note [reducible non-instances]
-/
abbrev pseudoMetricAux : PseudoMetricSpace (PiLp p α) :=
  PseudoEMetricSpace.toPseudoMetricSpaceOfDist dist
    (fun f g => by
      rcases p.dichotomy with (rfl | h)
      · simp only [dist, top_ne_zero, ↓reduceIte]
        exact Real.iSup_nonneg fun i ↦ dist_nonneg
      · simp only [dist]
        split_ifs with hp
        · linarith
        · exact Real.iSup_nonneg fun i ↦ dist_nonneg
        · exact rpow_nonneg (Fintype.sum_nonneg fun i ↦ by positivity) (1 / p.toReal))
    fun f g => by
    rcases p.dichotomy with (rfl | h)
    · rw [edist_eq_iSup, dist_eq_iSup]
      cases isEmpty_or_nonempty ι
      · simp
      · refine ENNReal.eq_of_forall_le_nnreal_iff fun r ↦ ?_
        have : BddAbove <| .range fun i ↦ dist (f i) (g i) := Finite.bddAbove_range _
        simp [ciSup_le_iff this]
    · have : 0 < p.toReal := by rw [ENNReal.toReal_pos_iff_ne_top]; rintro rfl; norm_num at h
      simp only [edist_eq_sum, edist_dist, dist_eq_sum, this]
      rw [← ENNReal.ofReal_rpow_of_nonneg (by simp [Finset.sum_nonneg, Real.rpow_nonneg]) (by simp)]
      simp [Real.rpow_nonneg, ENNReal.ofReal_sum_of_nonneg, ← ENNReal.ofReal_rpow_of_nonneg]

attribute [local instance] PiLp.pseudoMetricAux

variable {p β} in
/-
**PiLp.edist_apply_le_edist_aux** 是 Mathlib 中的一个定理，位于命名空间 `PiLp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem edist_apply_le_edist_aux (x y : PiLp p β) (i : ι) :
    edist (x i) (y i) ≤ edist x y := by
  rcases p.dichotomy with (rfl | h)
  · simpa only [edist_eq_iSup] using le_iSup (fun i => edist (x i) (y i)) i
  · have cancel : p.toReal * (1 / p.toReal) = 1 := mul_div_cancel₀ 1 (zero_lt_one.trans_le h).ne'
    rw [edist_eq_sum (zero_lt_one.trans_le h)]
    calc
      edist (x i) (y i) = (edist (x i) (y i) ^ p.toReal) ^ (1 / p.toReal) := by
        simp [← ENNReal.rpow_mul, cancel, -one_div]
      _ ≤ (∑ i, edist (x i) (y i) ^ p.toReal) ^ (1 / p.toReal) := by
        gcongr
        exact Finset.single_le_sum (fun i _ => (bot_le : (0 : ℝ≥0∞) ≤ _)) (Finset.mem_univ i)
/-
**PiLp.lipschitzWith_ofLp_aux** 是 Mathlib 中的一个引理，位于命名空间 `PiLp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma lipschitzWith_ofLp_aux : LipschitzWith 1 (@ofLp p (∀ i, β i)) :=
  .of_edist_le fun x y => by
    simp_rw [edist_pi_def, Finset.sup_le_iff, Finset.mem_univ, forall_true_left]
    exact edist_apply_le_edist_aux _ _
/-
**PiLp.antilipschitzWith_ofLp_aux** 是 Mathlib 中的一个引理，位于命名空间 `PiLp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma antilipschitzWith_ofLp_aux :
    AntilipschitzWith ((Fintype.card ι : ℝ≥0) ^ (1 / p).toReal) (@ofLp p (∀ i, β i)) := by
  intro x y
  rcases p.dichotomy with (rfl | h)
  · simp only [edist_eq_iSup, ENNReal.div_top, ENNReal.toReal_zero, NNReal.rpow_zero,
      ENNReal.coe_one, one_mul, iSup_le_iff]
    -- Porting note: `Finset.le_sup` needed some help
    exact fun i => Finset.le_sup (f := fun i => edist (x i) (y i)) (Finset.mem_univ i)
  · have pos : 0 < p.toReal := zero_lt_one.trans_le h
    have nonneg : 0 ≤ 1 / p.toReal := one_div_nonneg.2 (le_of_lt pos)
    have cancel : p.toReal * (1 / p.toReal) = 1 := mul_div_cancel₀ 1 (ne_of_gt pos)
    rw [edist_eq_sum pos, ENNReal.toReal_div 1 p]
    simp only [edist, ENNReal.toReal_one]
    calc
      (∑ i, edist (x i) (y i) ^ p.toReal) ^ (1 / p.toReal) ≤
          (∑ _i, edist (ofLp x) (ofLp y) ^ p.toReal) ^ (1 / p.toReal) := by
        gcongr with i
        exact Finset.le_sup (f := fun i => edist (x i) (y i)) (Finset.mem_univ i)
      _ =
          ((Fintype.card ι : ℝ≥0) ^ (1 / p.toReal) : ℝ≥0) *
            edist (ofLp x) (ofLp y) := by
        simp only [nsmul_eq_mul, Finset.card_univ, ENNReal.rpow_one, Finset.sum_const,
          ENNReal.mul_rpow_of_nonneg _ _ nonneg, ← ENNReal.rpow_mul, cancel]
        have : (Fintype.card ι : ℝ≥0∞) = (Fintype.card ι : ℝ≥0) :=
          (ENNReal.coe_natCast (Fintype.card ι)).symm
        rw [this, ENNReal.coe_rpow_of_nonneg _ nonneg]
/-
**PiLp.isUniformInducing_ofLp_aux** 是 Mathlib 中的一个引理，位于命名空间 `PiLp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma isUniformInducing_ofLp_aux : IsUniformInducing (@ofLp p (∀ i, β i)) :=
    (antilipschitzWith_ofLp_aux p β).isUniformInducing
      (lipschitzWith_ofLp_aux p β).uniformContinuous

set_option backward.privateInPublic true in
/-
**PiLp.uniformity_aux** 是 Mathlib 中的一个引理，位于命名空间 `PiLp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma uniformity_aux : 𝓤 (PiLp p β) = 𝓤[UniformSpace.comap ofLp inferInstance] := by
  rw [← (isUniformInducing_ofLp_aux p β).comap_uniformity]
  rfl
/-
**PiLp.bornology** 是 Mathlib 中的一个实例，位于命名空间 `PiLp`。
形式化陈述：bornology (p : Real>=0∞) (β : ι -> Type*) [forall i, Bornology (β i)] : Bo
rnology (PiLp p β)
参数：p : Real>=0∞；β : ι -> Type*；β i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance bornology (p : ℝ≥0∞) (β : ι → Type*) [∀ i, Bornology (β i)] :
    Bornology (PiLp p β) := Bornology.induced ofLp

set_option backward.privateInPublic true in
/-
**PiLp.cobounded_aux** 是 Mathlib 中的一个引理，位于命名空间 `PiLp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma cobounded_aux : @cobounded _ PseudoMetricSpace.toBornology = cobounded (PiLp p α) :=
  le_antisymm (antilipschitzWith_ofLp_aux p α).tendsto_cobounded.le_comap
    (lipschitzWith_ofLp_aux p α).comap_cobounded_le

end Aux

/-! ### Instances on finite `L^p` products -/

/-
**PiLp.topologicalSpace** 是 Mathlib 中的一个实例，位于命名空间 `PiLp`。
形式化陈述：topologicalSpace [forall i, TopologicalSpace (β i)] : TopologicalSpace (Pi
Lp p β)
参数：β i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Instances on finite `L^p` products
-/
instance topologicalSpace [∀ i, TopologicalSpace (β i)] : TopologicalSpace (PiLp p β) :=
  Pi.topologicalSpace.induced ofLp

@[fun_prop, continuity]
/-
**PiLp.continuous_ofLp** 是 Mathlib 中的一个定理，位于命名空间 `PiLp`。
形式化陈述：continuous_ofLp [forall i, TopologicalSpace (β i)] : Continuous (@ofLp p (
forall i, β i))
参数：β i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_induced_dom`：continuous_induced_dom {t : TopologicalSpace β} 
: Continuous[induced f t, t] f
-/
theorem continuous_ofLp [∀ i, TopologicalSpace (β i)] : Continuous (@ofLp p (∀ i, β i)) :=
  continuous_induced_dom

@[fun_prop, continuity]
/-
**PiLp.continuous_apply** 是 Mathlib 中的一个定理，位于命名空间 `PiLp`。
形式化陈述：∀ (p : ENNReal) {ι : Type u_2} (β : ι → Type u_4) [inst : (i : ι) → Topolo
gicalSpace (β i)] (i : ι),   Continuous fun f => f.ofLp i
参数：p : ENNReal；β : ι → Type u_4；i : ι；β i；i : ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `continuous_apply`：continuous_apply (a : α) : Continuous (fun f : (α → X)
 ↦ f a)
· 使用定理 `PiLp.continuous_ofLp`：continuous_ofLp [forall i, TopologicalSpace (β i)]
 : Continuous (@ofLp p (forall i, β i))
-/
protected lemma continuous_apply [∀ i, TopologicalSpace (β i)] (i : ι) :
    Continuous (fun f : PiLp p β ↦ f i) := (continuous_apply i).comp (continuous_ofLp p β)

@[fun_prop, continuity]
/-
**PiLp.continuous_toLp** 是 Mathlib 中的一个定理，位于命名空间 `PiLp`。
形式化陈述：continuous_toLp [forall i, TopologicalSpace (β i)] : Continuous (@toLp p (
forall i, β i))
参数：β i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_induced_rng`：continuous_induced_rng {g : γ -> α} {t₂ : Topolo
gicalSpace β} {t₁ : TopologicalSpace γ} : Continuous[t₁, induced f t₂] g ↔ Conti
nuous[t₁, t₂…
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
-/
theorem continuous_toLp [∀ i, TopologicalSpace (β i)] : Continuous (@toLp p (∀ i, β i)) :=
  continuous_induced_rng.2 continuous_id

/-- `WithLp.equiv` as a homeomorphism. -/
/-
**PiLp.homeomorph** 是 Mathlib 中的一个定义，位于命名空间 `PiLp`。
形式化陈述：homeomorph [forall i, TopologicalSpace (β i)] : PiLp p β ≃ₜ (Π i, β i) whe
re toEquiv
参数：β i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`WithLp.equiv` as a homeomorphism.
-/
def homeomorph [∀ i, TopologicalSpace (β i)] : PiLp p β ≃ₜ (Π i, β i) where
  toEquiv := WithLp.equiv p (Π i, β i)

@[simp]
/-
**PiLp.toEquiv_homeomorph** 是 Mathlib 中的一个引理，位于命名空间 `PiLp`。
形式化陈述：toEquiv_homeomorph [forall i, TopologicalSpace (β i)] : (homeomorph p β).t
oEquiv = WithLp.equiv p (Π i, β i)
参数：β i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toEquiv_homeomorph [∀ i, TopologicalSpace (β i)] :
    (homeomorph p β).toEquiv = WithLp.equiv p (Π i, β i) := rfl
/-
**PiLp.isOpenMap_apply** 是 Mathlib 中的一个引理，位于命名空间 `PiLp`。
形式化陈述：isOpenMap_apply [forall i, TopologicalSpace (β i)] (i : ι) : IsOpenMap (fu
n f : PiLp p β => f i)
参数：β i；i : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpenMap.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} {f : X → 
Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : TopologicalSpace Y] [inst
_2 :…
· 使用引理 `isOpenMap_eval`：isOpenMap_eval (i : ι) : IsOpenMap (Function.eval i : (f
orall i, X i) -> X i)
· 使用定理 `Homeomorph.isOpenMap`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologica
lSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y), IsOpenMap ⇑h
-/
lemma isOpenMap_apply [∀ i, TopologicalSpace (β i)] (i : ι) :
    IsOpenMap (fun f : PiLp p β ↦ f i) := (isOpenMap_eval i).comp (homeomorph p β).isOpenMap
/-
**PiLp.instProdT0Space** 是 Mathlib 中的一个实例，位于命名空间 `PiLp`。
形式化陈述：instProdT0Space [forall i, TopologicalSpace (β i)] [forall i, T0Space (β i
)] : T0Space (PiLp p β)
参数：β i；β i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.t0Space`：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalS
pace X] [inst_1 : TopologicalSpace Y] [T0Space X] (h : X ≃ₜ Y),   T0Space Y
-/
instance instProdT0Space [∀ i, TopologicalSpace (β i)] [∀ i, T0Space (β i)] :
    T0Space (PiLp p β) :=
  (homeomorph p β).symm.t0Space
/-
**PiLp.secondCountableTopology** 是 Mathlib 中的一个实例，位于命名空间 `PiLp`。
形式化陈述：secondCountableTopology [Countable ι] [forall i, TopologicalSpace (β i)] [
forall i, SecondCountableTopology (β i)] : SecondCountableTopology (PiLp p β)
参数：β i；β i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.secondCountableTopology`：∀ {X : Type u_1} {Y : Type u_2} [ins
t : TopologicalSpace X] [inst_1 : TopologicalSpace Y] [SecondCountableTopology Y
]   (h : X ≃ₜ Y), Second…
· 使用定理 `TopologicalSpace.instSecondCountableTopologyForallOfCountable`：∀ {ι : Ty
pe u_1} {X : ι → Type u_2} [Countable ι] [inst : (a : ι) → TopologicalSpace (X a
)]   [∀ (a : ι), SecondCountableTopology (X a)], Se…
-/
instance secondCountableTopology [Countable ι] [∀ i, TopologicalSpace (β i)]
    [∀ i, SecondCountableTopology (β i)] : SecondCountableTopology (PiLp p β) :=
  (homeomorph p β).secondCountableTopology
/-
**PiLp.uniformSpace** 是 Mathlib 中的一个实例，位于命名空间 `PiLp`。
形式化陈述：uniformSpace [forall i, UniformSpace (β i)] : UniformSpace (PiLp p β)
参数：β i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance uniformSpace [∀ i, UniformSpace (β i)] : UniformSpace (PiLp p β) :=
  (Pi.uniformSpace β).comap ofLp

@[fun_prop]
/-
**PiLp.uniformContinuous_ofLp** 是 Mathlib 中的一个引理，位于命名空间 `PiLp`。
形式化陈述：uniformContinuous_ofLp [forall i, UniformSpace (β i)] : UniformContinuous 
(@ofLp p (forall i, β i))
参数：β i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `uniformContinuous_comap`：uniformContinuous_comap {f : α -> β} [u : Unifo
rmSpace β] : @UniformContinuous α β (UniformSpace.comap f u) u f
-/
lemma uniformContinuous_ofLp [∀ i, UniformSpace (β i)] :
    UniformContinuous (@ofLp p (∀ i, β i)) :=
  uniformContinuous_comap

@[fun_prop]
/-
**PiLp.uniformContinuous_toLp** 是 Mathlib 中的一个引理，位于命名空间 `PiLp`。
形式化陈述：uniformContinuous_toLp [forall i, UniformSpace (β i)] : UniformContinuous 
(@toLp p (forall i, β i))
参数：β i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `uniformContinuous_comap'`：uniformContinuous_comap' {f : γ -> β} {g : α -
> γ} [v : UniformSpace β] [u : UniformSpace α] (h : UniformContinuous (f ∘ g)) :
 @UniformConti…
· 使用定理 `uniformContinuous_id`：uniformContinuous_id : UniformContinuous (@id α)
-/
lemma uniformContinuous_toLp [∀ i, UniformSpace (β i)] :
    UniformContinuous (@toLp p (∀ i, β i)) :=
  uniformContinuous_comap' uniformContinuous_id

/-- `WithLp.equiv` as a uniform isomorphism. -/
/-
**PiLp.uniformEquiv** 是 Mathlib 中的一个定义，位于命名空间 `PiLp`。
形式化陈述：uniformEquiv [forall i, UniformSpace (β i)] : PiLp p β ≃ᵤ (Π i, β i) where
 toEquiv
参数：β i。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `PiLp.uniformContinuous_ofLp`：uniformContinuous_ofLp [forall i, UniformSp
ace (β i)] : UniformContinuous (@ofLp p (forall i, β i))
· 使用引理 `PiLp.uniformContinuous_toLp`：uniformContinuous_toLp [forall i, UniformSp
ace (β i)] : UniformContinuous (@toLp p (forall i, β i))

--- 原说明 ---
`WithLp.equiv` as a uniform isomorphism.
-/
def uniformEquiv [∀ i, UniformSpace (β i)] : PiLp p β ≃ᵤ (Π i, β i) where
  toEquiv := WithLp.equiv p (Π i, β i)
  uniformContinuous_toFun := uniformContinuous_ofLp p β
  uniformContinuous_invFun := uniformContinuous_toLp p β

@[simp]
/-
**PiLp.toHomeomorph_uniformEquiv** 是 Mathlib 中的一个引理，位于命名空间 `PiLp`。
形式化陈述：toHomeomorph_uniformEquiv [forall i, UniformSpace (β i)] : (uniformEquiv p
 β).toHomeomorph = homeomorph p β
参数：β i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toHomeomorph_uniformEquiv [∀ i, UniformSpace (β i)] :
    (uniformEquiv p β).toHomeomorph = homeomorph p β := rfl

@[simp]
/-
**PiLp.toEquiv_uniformEquiv** 是 Mathlib 中的一个引理，位于命名空间 `PiLp`。
形式化陈述：toEquiv_uniformEquiv [forall i, UniformSpace (β i)] : (uniformEquiv p β).t
oEquiv = WithLp.equiv p (Π i, β i)
参数：β i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toEquiv_uniformEquiv [∀ i, UniformSpace (β i)] :
    (uniformEquiv p β).toEquiv = WithLp.equiv p (Π i, β i) := rfl
/-
**PiLp.completeSpace** 是 Mathlib 中的一个实例，位于命名空间 `PiLp`。
形式化陈述：completeSpace [forall i, UniformSpace (β i)] [forall i, CompleteSpace (β i
)] : CompleteSpace (PiLp p β)
参数：β i；β i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `UniformEquiv.completeSpace_iff`：completeSpace_iff (h : α ≃ᵤ β) : Complet
eSpace α ↔ CompleteSpace β
-/
instance completeSpace [∀ i, UniformSpace (β i)] [∀ i, CompleteSpace (β i)] :
    CompleteSpace (PiLp p β) :=
  (uniformEquiv p β).completeSpace_iff.2 inferInstance

section Fintype
variable [hp : Fact (1 ≤ p)]
variable [Fintype ι]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- pseudoemetric space instance on the product of finitely many pseudoemetric spaces, using the
`L^p` pseudoedistance, and having as uniformity the product uniformity. -/
/-
**PiLp.** 是 Mathlib 中的一个实例，位于命名空间 `PiLp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
pseudoemetric space instance on the product of finitely many pseudoemetric space
s, using the
`L^p` pseudoedistance, and having as uniformity the product uniformity.
-/
instance [∀ i, PseudoEMetricSpace (β i)] : PseudoEMetricSpace (PiLp p β) :=
  (pseudoEmetricAux p β).replaceUniformity (uniformity_aux p β).symm

/-- emetric space instance on the product of finitely many emetric spaces, using the `L^p`
edistance, and having as uniformity the product uniformity. -/
/-
**PiLp.** 是 Mathlib 中的一个实例，位于命名空间 `PiLp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
emetric space instance on the product of finitely many emetric spaces, using the
 `L^p`
edistance, and having as uniformity the product uniformity.
-/
instance [∀ i, EMetricSpace (α i)] : EMetricSpace (PiLp p α) :=
  EMetricSpace.ofT0PseudoEMetricSpace (PiLp p α)

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- pseudometric space instance on the product of finitely many pseudometric spaces, using the
`L^p` distance, and having as uniformity the product uniformity. -/
/-
**PiLp.** 是 Mathlib 中的一个实例，位于命名空间 `PiLp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
pseudometric space instance on the product of finitely many pseudometric spaces,
 using the
`L^p` distance, and having as uniformity the product uniformity.
-/
instance [∀ i, PseudoMetricSpace (β i)] : PseudoMetricSpace (PiLp p β) :=
  ((pseudoMetricAux p β).replaceUniformity (uniformity_aux p β).symm).replaceBornology fun s =>
    Filter.ext_iff.1 (cobounded_aux p β).symm sᶜ

/-- metric space instance on the product of finitely many metric spaces, using the `L^p` distance,
and having as uniformity the product uniformity. -/
/-
**PiLp.** 是 Mathlib 中的一个实例，位于命名空间 `PiLp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
metric space instance on the product of finitely many metric spaces, using the `
L^p` distance,
and having as uniformity the product uniformity.
-/
instance [∀ i, MetricSpace (α i)] : MetricSpace (PiLp p α) :=
  MetricSpace.ofT0PseudoMetricSpace _
/-
**PiLp.nndist_eq_sum** 是 Mathlib 中的一个定理，位于命名空间 `PiLp`。
形式化陈述：nndist_eq_sum {p : Real>=0∞} [Fact (1 <= p)] {β : ι -> Type*} [forall i, P
seudoMetricSpace (β i)] (hp : p != ∞) (x y : PiLp p β) : nndist x y = (∑ i : ι, 
nndist (x i) (y i) ^ p.toReal) ^ (1 / p.toReal)
参数：1 <= p；β i；hp : p != ∞；x y : PiLp p β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `NNReal.coe_sum`：coe_sum (s : Finset ι) (f : ι -> Real>=0) : ∑ i in s, f 
i = ∑ i in s, (f i : Real)
· 使用定理 `PiLp.dist_eq_sum`：dist_eq_sum {p : Real>=0∞} (hp : 0 < p.toReal) (f g : 
PiLp p α) : dist f g = (∑ i, dist (f i) (g i) ^ p.toReal) ^ (1 / p.toReal)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.toReal_pos_iff_ne_top`：toReal_pos_iff_ne_top (p : Real>=0∞) [Fac
t (1 <= p)] : 0 < p.toReal ↔ p != ∞
-/
theorem nndist_eq_sum {p : ℝ≥0∞} [Fact (1 ≤ p)] {β : ι → Type*} [∀ i, PseudoMetricSpace (β i)]
    (hp : p ≠ ∞) (x y : PiLp p β) :
    nndist x y = (∑ i : ι, nndist (x i) (y i) ^ p.toReal) ^ (1 / p.toReal) :=
  NNReal.eq <| by
    push_cast
    exact dist_eq_sum (p.toReal_pos_iff_ne_top.mpr hp) _ _
/-
**PiLp.nndist_eq_iSup** 是 Mathlib 中的一个定理，位于命名空间 `PiLp`。
形式化陈述：nndist_eq_iSup {β : ι -> Type*} [forall i, PseudoMetricSpace (β i)] (x y :
 PiLp ∞ β) : nndist x y = ⨆ i, nndist (x i) (y i)
参数：β i；x y : PiLp ∞ β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `fact_one_le_top_ennreal`：Fact (1 ≤ ⊤)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NNReal.coe_iSup`：coe_iSup {ι : Sort*} (s : ι -> Real>=0) : (↑(⨆ i, s i) 
: Real) = ⨆ i, ↑(s i)
· 使用定理 `PiLp.dist_eq_iSup`：dist_eq_iSup (f g : PiLp ∞ α) : dist f g = ⨆ i, dist 
(f i) (g i)
-/
theorem nndist_eq_iSup {β : ι → Type*} [∀ i, PseudoMetricSpace (β i)] (x y : PiLp ∞ β) :
    nndist x y = ⨆ i, nndist (x i) (y i) :=
  NNReal.eq <| by
    push_cast
    exact dist_eq_iSup _ _

section
variable {β p}

/-
**PiLp.edist_apply_le** 是 Mathlib 中的一个定理，位于命名空间 `PiLp`。
形式化陈述：edist_apply_le [forall i, PseudoEMetricSpace (β i)] (x y : PiLp p β) (i : 
ι) : edist (x i) (y i) <= edist x y
参数：β i；x y : PiLp p β；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Analysis.Normed.Lp.PiLp.0.PiLp.edist_apply_le_edist_aux
`：∀ {p : ENNReal} {ι : Type u_2} {β : ι → Type u_4} [Fact (1 ≤ p)] [inst : (i : 
ι) → PseudoEMetricSpace (β i)]   [inst_1 : Fintype ι] (x y : P…
-/
theorem edist_apply_le [∀ i, PseudoEMetricSpace (β i)] (x y : PiLp p β) (i : ι) :
    edist (x i) (y i) ≤ edist x y :=
  edist_apply_le_edist_aux x y i
/-
**PiLp.nndist_apply_le** 是 Mathlib 中的一个定理，位于命名空间 `PiLp`。
形式化陈述：nndist_apply_le [forall i, PseudoMetricSpace (β i)] (x y : PiLp p β) (i : 
ι) : nndist (x i) (y i) <= nndist x y
参数：β i；x y : PiLp p β；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PiLp.edist_apply_le`：edist_apply_le [forall i, PseudoEMetricSpace (β i)]
 (x y : PiLp p β) (i : ι) : edist (x i) (y i) <= edist x y
-/
theorem nndist_apply_le [∀ i, PseudoMetricSpace (β i)] (x y : PiLp p β) (i : ι) :
    nndist (x i) (y i) ≤ nndist x y := by
  simpa [← coe_nnreal_ennreal_nndist] using edist_apply_le x y i
/-
**PiLp.dist_apply_le** 是 Mathlib 中的一个定理，位于命名空间 `PiLp`。
形式化陈述：dist_apply_le [forall i, PseudoMetricSpace (β i)] (x y : PiLp p β) (i : ι)
 : dist (x i) (y i) <= dist x y
参数：β i；x y : PiLp p β；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PiLp.nndist_apply_le`：nndist_apply_le [forall i, PseudoMetricSpace (β i)
] (x y : PiLp p β) (i : ι) : nndist (x i) (y i) <= nndist x y
-/
theorem dist_apply_le [∀ i, PseudoMetricSpace (β i)] (x y : PiLp p β) (i : ι) :
    dist (x i) (y i) ≤ dist x y :=
  nndist_apply_le x y i

end

/-
**PiLp.lipschitzWith_ofLp** 是 Mathlib 中的一个引理，位于命名空间 `PiLp`。
形式化陈述：lipschitzWith_ofLp [forall i, PseudoEMetricSpace (β i)] : LipschitzWith 1 
(@ofLp p (forall i, β i))
参数：β i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Analysis.Normed.Lp.PiLp.0.PiLp.lipschitzWith_ofLp_aux`：
∀ (p : ENNReal) {ι : Type u_2} (β : ι → Type u_4) [inst : Fact (1 ≤ p)] [inst_1 
: (i : ι) → PseudoEMetricSpace (β i)]   [inst_2 : Fintype ι]…
-/
lemma lipschitzWith_ofLp [∀ i, PseudoEMetricSpace (β i)] :
    LipschitzWith 1 (@ofLp p (∀ i, β i)) :=
  lipschitzWith_ofLp_aux p β
/-
**PiLp.antilipschitzWith_toLp** 是 Mathlib 中的一个引理，位于命名空间 `PiLp`。
形式化陈述：antilipschitzWith_toLp [forall i, PseudoEMetricSpace (β i)] : Antilipschit
zWith 1 (@toLp p (forall i, β i))
参数：β i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzWith.to_rightInverse`：LipschitzWith.to_rightInverse [PseudoEMet
ricSpace α] [PseudoEMetricSpace β] {K : Real>=0} {f : α -> β} (hf : LipschitzWit
h K f) {g : β -> α}…
· 使用引理 `PiLp.lipschitzWith_ofLp`：lipschitzWith_ofLp [forall i, PseudoEMetricSpac
e (β i)] : LipschitzWith 1 (@ofLp p (forall i, β i))
· 使用引理 `WithLp.ofLp_toLp`：ofLp_toLp (x : V) : ofLp (toLp p x) = x
-/
lemma antilipschitzWith_toLp [∀ i, PseudoEMetricSpace (β i)] :
    AntilipschitzWith 1 (@toLp p (∀ i, β i)) :=
  (lipschitzWith_ofLp p β).to_rightInverse (ofLp_toLp p)
/-
**PiLp.antilipschitzWith_ofLp** 是 Mathlib 中的一个定理，位于命名空间 `PiLp`。
形式化陈述：antilipschitzWith_ofLp [forall i, PseudoEMetricSpace (β i)] : Antilipschit
zWith ((Fintype.card ι : Real>=0) ^ (1 / p).toReal) (@ofLp p (forall i, β i))
参数：β i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Analysis.Normed.Lp.PiLp.0.PiLp.antilipschitzWith_ofLp_a
ux`：∀ (p : ENNReal) {ι : Type u_2} (β : ι → Type u_4) [inst : Fact (1 ≤ p)] [ins
t_1 : (i : ι) → PseudoEMetricSpace (β i)]   [inst_2 : Fintype ι]…
-/
theorem antilipschitzWith_ofLp [∀ i, PseudoEMetricSpace (β i)] :
    AntilipschitzWith ((Fintype.card ι : ℝ≥0) ^ (1 / p).toReal) (@ofLp p (∀ i, β i)) :=
  antilipschitzWith_ofLp_aux p β
/-
**PiLp.lipschitzWith_toLp** 是 Mathlib 中的一个引理，位于命名空间 `PiLp`。
形式化陈述：lipschitzWith_toLp [forall i, PseudoEMetricSpace (β i)] : LipschitzWith ((
Fintype.card ι : Real>=0) ^ (1 / p).toReal) (@toLp p (forall i, β i))
参数：β i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AntilipschitzWith.to_rightInverse`：to_rightInverse (hf : AntilipschitzWi
th K f) {g : β -> α} (hg : Function.RightInverse g f) : LipschitzWith K g
· 使用定理 `PiLp.antilipschitzWith_ofLp`：antilipschitzWith_ofLp [forall i, PseudoEMe
tricSpace (β i)] : AntilipschitzWith ((Fintype.card ι : Real>=0) ^ (1 / p).toRea
l) (@ofLp p (fora…
· 使用引理 `WithLp.ofLp_toLp`：ofLp_toLp (x : V) : ofLp (toLp p x) = x
-/
lemma lipschitzWith_toLp [∀ i, PseudoEMetricSpace (β i)] :
    LipschitzWith ((Fintype.card ι : ℝ≥0) ^ (1 / p).toReal) (@toLp p (∀ i, β i)) :=
  (antilipschitzWith_ofLp p β).to_rightInverse (ofLp_toLp p)
/-
**PiLp.isometry_ofLp_infty** 是 Mathlib 中的一个引理，位于命名空间 `PiLp`。
形式化陈述：isometry_ofLp_infty [forall i, PseudoEMetricSpace (β i)] : Isometry (@ofLp
 ∞ (forall i, β i))
参数：β i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `fact_one_le_top_ennreal`：Fact (1 ≤ ⊤)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用引理 `PiLp.lipschitzWith_ofLp`：lipschitzWith_ofLp [forall i, PseudoEMetricSpac
e (β i)] : LipschitzWith 1 (@ofLp p (forall i, β i))
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ENNReal.div_top`：∀ {a : ENNReal}, a / ⊤ = 0
· 使用定理 `NNReal.rpow_zero`：rpow_zero (x : Real>=0) : x ^ (0 : Real) = 1
· 使用定理 `PiLp.antilipschitzWith_ofLp`：antilipschitzWith_ofLp [forall i, PseudoEMe
tricSpace (β i)] : AntilipschitzWith ((Fintype.card ι : Real>=0) ^ (1 / p).toRea
l) (@ofLp p (fora…
-/
lemma isometry_ofLp_infty [∀ i, PseudoEMetricSpace (β i)] :
    Isometry (@ofLp ∞ (∀ i, β i)) :=
  fun x y =>
  le_antisymm (by simpa only [ENNReal.coe_one, one_mul] using lipschitzWith_ofLp ∞ β x y)
    (by simpa only [ENNReal.div_top, ENNReal.toReal_zero, NNReal.rpow_zero, ENNReal.coe_one,
      one_mul] using antilipschitzWith_ofLp ∞ β x y)

/-- seminormed group instance on the product of finitely many normed groups, using the `L^p`
norm. -/
/-
**PiLp.seminormedAddCommGroup** 是 Mathlib 中的一个实例，位于命名空间 `PiLp`。
形式化陈述：seminormedAddCommGroup [forall i, SeminormedAddCommGroup (β i)] : Seminorm
edAddCommGroup (PiLp p β) where dist_eq
参数：β i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
seminormed group instance on the product of finitely many normed groups, using t
he `L^p`
norm.
-/
instance seminormedAddCommGroup [∀ i, SeminormedAddCommGroup (β i)] :
    SeminormedAddCommGroup (PiLp p β) where
  dist_eq := fun x y => by
    rcases p.dichotomy with (rfl | h)
    · simp only [dist_eq_iSup, norm_eq_ciSup, dist_eq_norm, add_apply, neg_apply, norm_neg_add]
    · have : p ≠ ∞ := by
        intro hp
        rw [hp, ENNReal.toReal_top] at h
        linarith
      simp only [dist_eq_sum (zero_lt_one.trans_le h), norm_eq_sum (zero_lt_one.trans_le h),
        dist_eq_norm, add_apply, neg_apply, norm_neg_add]

omit [Fintype ι] in
/-
**PiLp.isUniformInducing_toLp** 是 Mathlib 中的一个引理，位于命名空间 `PiLp`。
形式化陈述：isUniformInducing_toLp [Finite ι] [forall i, PseudoEMetricSpace (β i)] : I
sUniformInducing (@toLp p (Π i, β i))
参数：β i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AntilipschitzWith.isUniformInducing`：isUniformInducing (hf : Antilipschi
tzWith K f) (hfc : UniformContinuous f) : IsUniformInducing f
· 使用引理 `PiLp.antilipschitzWith_toLp`：antilipschitzWith_toLp [forall i, PseudoEMe
tricSpace (β i)] : AntilipschitzWith 1 (@toLp p (forall i, β i))
· 使用定理 `LipschitzWith.uniformContinuous`：∀ {α : Type u} {β : Type v} [inst : Pse
udoEMetricSpace α] [inst_1 : PseudoEMetricSpace β] {K : NNReal} {f : α → β},   L
ipschitzWith K f → Un…
· 使用引理 `PiLp.lipschitzWith_toLp`：lipschitzWith_toLp [forall i, PseudoEMetricSpac
e (β i)] : LipschitzWith ((Fintype.card ι : Real>=0) ^ (1 / p).toReal) (@toLp p 
(forall i, β …
-/
lemma isUniformInducing_toLp [Finite ι] [∀ i, PseudoEMetricSpace (β i)] :
    IsUniformInducing (@toLp p (Π i, β i)) :=
  have := Fintype.ofFinite ι
  (antilipschitzWith_toLp p β).isUniformInducing
    (lipschitzWith_toLp p β).uniformContinuous

section
variable {β p}

/-
**PiLp.enorm_apply_le** 是 Mathlib 中的一个定理，位于命名空间 `PiLp`。
形式化陈述：enorm_apply_le [forall i, SeminormedAddCommGroup (β i)] (x : PiLp p β) (i 
: ι) : ‖x i‖ₑ <= ‖x‖ₑ
参数：β i；x : PiLp p β；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `edist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E)
, edist a 0 = ‖a‖ₑ
· 使用定理 `PiLp.edist_apply_le`：edist_apply_le [forall i, PseudoEMetricSpace (β i)]
 (x y : PiLp p β) (i : ι) : edist (x i) (y i) <= edist x y
-/
theorem enorm_apply_le [∀ i, SeminormedAddCommGroup (β i)] (x : PiLp p β) (i : ι) :
    ‖x i‖ₑ ≤ ‖x‖ₑ := by
  simpa using edist_apply_le x 0 i
/-
**PiLp.nnnorm_apply_le** 是 Mathlib 中的一个定理，位于命名空间 `PiLp`。
形式化陈述：nnnorm_apply_le [forall i, SeminormedAddCommGroup (β i)] (x : PiLp p β) (i
 : ι) : ‖x i‖₊ <= ‖x‖₊
参数：β i；x : PiLp p β；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nndist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E
), nndist a 0 = ‖a‖₊
· 使用定理 `PiLp.nndist_apply_le`：nndist_apply_le [forall i, PseudoMetricSpace (β i)
] (x y : PiLp p β) (i : ι) : nndist (x i) (y i) <= nndist x y
-/
theorem nnnorm_apply_le [∀ i, SeminormedAddCommGroup (β i)] (x : PiLp p β) (i : ι) :
    ‖x i‖₊ ≤ ‖x‖₊ := by
  simpa using nndist_apply_le x 0 i
/-
**PiLp.norm_apply_le** 是 Mathlib 中的一个定理，位于命名空间 `PiLp`。
形式化陈述：norm_apply_le [forall i, SeminormedAddCommGroup (β i)] (x : PiLp p β) (i :
 ι) : ‖x i‖ <= ‖x‖
参数：β i；x : PiLp p β；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E),
 dist a 0 = ‖a‖
· 使用定理 `PiLp.dist_apply_le`：dist_apply_le [forall i, PseudoMetricSpace (β i)] (x
 y : PiLp p β) (i : ι) : dist (x i) (y i) <= dist x y
-/
theorem norm_apply_le [∀ i, SeminormedAddCommGroup (β i)] (x : PiLp p β) (i : ι) :
    ‖x i‖ ≤ ‖x‖ := by
  simpa using dist_apply_le x 0 i

end

/-- normed group instance on the product of finitely many normed groups, using the `L^p` norm. -/
/-
**PiLp.normedAddCommGroup** 是 Mathlib 中的一个实例，位于命名空间 `PiLp`。
形式化陈述：normedAddCommGroup [forall i, NormedAddCommGroup (α i)] : NormedAddCommGro
up (PiLp p α)
参数：α i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
normed group instance on the product of finitely many normed groups, using the `
L^p` norm.
-/
instance normedAddCommGroup [∀ i, NormedAddCommGroup (α i)] : NormedAddCommGroup (PiLp p α) :=
  { PiLp.seminormedAddCommGroup p α with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }
/-
**PiLp.nnnorm_eq_sum** 是 Mathlib 中的一个定理，位于命名空间 `PiLp`。
形式化陈述：nnnorm_eq_sum {p : Real>=0∞} [Fact (1 <= p)] {β : ι -> Type*} (hp : p != ∞
) [forall i, SeminormedAddCommGroup (β i)] (f : PiLp p β) : ‖f‖₊ = (∑ i, ‖f i‖₊ 
^ p.toReal) ^ (1 / p.toReal)
参数：1 <= p；hp : p != ∞；β i；f : PiLp p β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PiLp.norm_eq_sum`：norm_eq_sum (hp : 0 < p.toReal) (f : PiLp p β) : ‖f‖ =
 (∑ i, ‖f i‖ ^ p.toReal) ^ (1 / p.toReal)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.toReal_pos_iff_ne_top`：toReal_pos_iff_ne_top (p : Real>=0∞) [Fac
t (1 <= p)] : 0 < p.toReal ↔ p != ∞
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `NNReal.coe_sum`：coe_sum (s : Finset ι) (f : ι -> Real>=0) : ∑ i in s, f 
i = ∑ i in s, (f i : Real)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem nnnorm_eq_sum {p : ℝ≥0∞} [Fact (1 ≤ p)] {β : ι → Type*} (hp : p ≠ ∞)
    [∀ i, SeminormedAddCommGroup (β i)] (f : PiLp p β) :
    ‖f‖₊ = (∑ i, ‖f i‖₊ ^ p.toReal) ^ (1 / p.toReal) := by
  ext
  simp [NNReal.coe_sum, norm_eq_sum (p.toReal_pos_iff_ne_top.mpr hp)]

section Linfty
variable {β}
variable [∀ i, SeminormedAddCommGroup (β i)]

/-
**PiLp.nnnorm_eq_ciSup** 是 Mathlib 中的一个定理，位于命名空间 `PiLp`。
形式化陈述：nnnorm_eq_ciSup (f : PiLp ∞ β) : ‖f‖₊ = ⨆ i, ‖f i‖₊
参数：f : PiLp ∞ β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `fact_one_le_top_ennreal`：Fact (1 ≤ ⊤)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NNReal.coe_iSup`：coe_iSup {ι : Sort*} (s : ι -> Real>=0) : (↑(⨆ i, s i) 
: Real) = ⨆ i, ↑(s i)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem nnnorm_eq_ciSup (f : PiLp ∞ β) : ‖f‖₊ = ⨆ i, ‖f i‖₊ := by
  ext
  simp [NNReal.coe_iSup, norm_eq_ciSup]
/-
**PiLp.nnnorm_ofLp** 是 Mathlib 中的一个定理，位于命名空间 `PiLp`。
形式化陈述：∀ {ι : Type u_2} {β : ι → Type u_4} [inst : Fintype ι] [inst_1 : (i : ι) →
 SeminormedAddCommGroup (β i)] (f : PiLp ⊤ β),   ‖f.ofLp‖₊ = ‖f‖₊
参数：i : ι；β i；f : PiLp ⊤ β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_top_ennreal`：Fact (1 ≤ ⊤)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PiLp.nnnorm_eq_ciSup`：nnnorm_eq_ciSup (f : PiLp ∞ β) : ‖f‖₊ = ⨆ i, ‖f i‖
₊
· 使用定理 `Pi.nnnorm_def`：∀ {ι : Type u_1} {G : ι → Type u_4} [inst : Fintype ι] [i
nst_1 : (i : ι) → SeminormedAddGroup (G i)]   (f : (i : ι) → G i), ‖f‖₊ = Finset
.un…
· 使用引理 `Finset.sup_univ_eq_ciSup`：sup_univ_eq_ciSup [Fintype ι] (f : ι -> α) : u
niv.sup f = ⨆ i, f i
-/
@[simp] lemma nnnorm_ofLp (f : PiLp ∞ β) : ‖ofLp f‖₊ = ‖f‖₊ := by
  rw [nnnorm_eq_ciSup, Pi.nnnorm_def, Finset.sup_univ_eq_ciSup]
/-
**PiLp.nnnorm_toLp** 是 Mathlib 中的一个定理，位于命名空间 `PiLp`。
形式化陈述：∀ {ι : Type u_2} {β : ι → Type u_4} [inst : Fintype ι] [inst_1 : (i : ι) →
 SeminormedAddCommGroup (β i)]   (f : (i : ι) → β i), ‖WithLp.toLp ⊤ f‖₊ = ‖f‖₊
参数：i : ι；β i；f : (i : ι) → β i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `fact_one_le_top_ennreal`：Fact (1 ≤ ⊤)
· 使用定理 `PiLp.nnnorm_ofLp`：∀ {ι : Type u_2} {β : ι → Type u_4} [inst : Fintype ι]
 [inst_1 : (i : ι) → SeminormedAddCommGroup (β i)] (f : PiLp ⊤ β),   ‖f.ofLp‖₊ =
 ‖f‖₊
-/
@[simp] lemma nnnorm_toLp (f : ∀ i, β i) : ‖toLp ∞ f‖₊ = ‖f‖₊ := (nnnorm_ofLp _).symm
/-
**PiLp.norm_ofLp** 是 Mathlib 中的一个定理，位于命名空间 `PiLp`。
形式化陈述：∀ {ι : Type u_2} {β : ι → Type u_4} [inst : Fintype ι] [inst_1 : (i : ι) →
 SeminormedAddCommGroup (β i)] (f : PiLp ⊤ β),   ‖f.ofLp‖ = ‖f‖
参数：i : ι；β i；f : PiLp ⊤ β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `fact_one_le_top_ennreal`：Fact (1 ≤ ⊤)
· 使用定理 `PiLp.nnnorm_ofLp`：∀ {ι : Type u_2} {β : ι → Type u_4} [inst : Fintype ι]
 [inst_1 : (i : ι) → SeminormedAddCommGroup (β i)] (f : PiLp ⊤ β),   ‖f.ofLp‖₊ =
 ‖f‖₊
-/
@[simp] lemma norm_ofLp (f : PiLp ∞ β) : ‖ofLp f‖ = ‖f‖ := congr_arg NNReal.toReal <| nnnorm_ofLp f
/-
**PiLp.norm_toLp** 是 Mathlib 中的一个定理，位于命名空间 `PiLp`。
形式化陈述：∀ {ι : Type u_2} {β : ι → Type u_4} [inst : Fintype ι] [inst_1 : (i : ι) →
 SeminormedAddCommGroup (β i)]   (f : (i : ι) → β i), ‖WithLp.toLp ⊤ f‖ = ‖f‖
参数：i : ι；β i；f : (i : ι) → β i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PiLp.norm_ofLp`：∀ {ι : Type u_2} {β : ι → Type u_4} [inst : Fintype ι] [
inst_1 : (i : ι) → SeminormedAddCommGroup (β i)] (f : PiLp ⊤ β),   ‖f.ofLp‖ = ‖f
‖
-/
@[simp] lemma norm_toLp (f : ∀ i, β i) : ‖toLp ∞ f‖ = ‖f‖ := (norm_ofLp _).symm

end Linfty

/-
**PiLp.norm_eq_of_nat** 是 Mathlib 中的一个定理，位于命名空间 `PiLp`。
形式化陈述：norm_eq_of_nat {p : Real>=0∞} [Fact (1 <= p)] {β : ι -> Type*} [forall i, 
SeminormedAddCommGroup (β i)] (n : Nat) (h : p = n) (f : PiLp p β) : ‖f‖ = (∑ i,
 ‖f i‖ ^ n) ^ (1 / (n : Real))
参数：1 <= p；β i；n : Nat；h : p = n；f : PiLp p β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.toReal_pos_iff_ne_top`：toReal_pos_iff_ne_top (p : Real>=0∞) [Fac
t (1 <= p)] : 0 < p.toReal ↔ p != ∞
· 使用引理 `ne_of_eq_of_ne`：ne_of_eq_of_ne {α : Sort*} {a b c : α} (h₁ : a = b) (h₂ 
: b != c) : a != c
· 使用定理 `ENNReal.natCast_ne_top`：natCast_ne_top (n : Nat) : (n : Real>=0∞) != ∞
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PiLp.norm_eq_sum`：norm_eq_sum (hp : 0 < p.toReal) (f : PiLp p β) : ‖f‖ =
 (∑ i, ‖f i‖ ^ p.toReal) ^ (1 / p.toReal)
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `ENNReal.toReal_natCast`：toReal_natCast (n : Nat) : (n : Real>=0∞).toReal
 = n
· 使用定理 `Real.rpow_natCast`：rpow_natCast (x : Real) (n : Nat) : x ^ (n : Real) = 
x ^ n
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem norm_eq_of_nat {p : ℝ≥0∞} [Fact (1 ≤ p)] {β : ι → Type*}
    [∀ i, SeminormedAddCommGroup (β i)] (n : ℕ) (h : p = n) (f : PiLp p β) :
    ‖f‖ = (∑ i, ‖f i‖ ^ n) ^ (1 / (n : ℝ)) := by
  have := p.toReal_pos_iff_ne_top.mpr (ne_of_eq_of_ne h <| ENNReal.natCast_ne_top n)
  simp only [one_div, h, Real.rpow_natCast, ENNReal.toReal_natCast,
    norm_eq_sum this]

section L1
variable {β} [∀ i, SeminormedAddCommGroup (β i)]

set_option backward.isDefEq.respectTransparency false in
/-
**PiLp.norm_eq_of_L1** 是 Mathlib 中的一个定理，位于命名空间 `PiLp`。
形式化陈述：norm_eq_of_L1 (x : PiLp 1 β) : ‖x‖ = ∑ i : ι, ‖x i‖
参数：x : PiLp 1 β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PiLp.norm_eq_sum`：norm_eq_sum (hp : 0 < p.toReal) (f : PiLp p β) : ‖f‖ =
 (∑ i, ‖f i‖ ^ p.toReal) ^ (1 / p.toReal)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Real.rpow_one`：rpow_one (x : Real) : x ^ (1 : Real) = x
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem norm_eq_of_L1 (x : PiLp 1 β) : ‖x‖ = ∑ i : ι, ‖x i‖ := by
  simp [norm_eq_sum]
/-
**PiLp.nnnorm_eq_of_L1** 是 Mathlib 中的一个定理，位于命名空间 `PiLp`。
形式化陈述：nnnorm_eq_of_L1 (x : PiLp 1 β) : ‖x‖₊ = ∑ i : ι, ‖x i‖₊
参数：x : PiLp 1 β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NNReal.coe_sum`：coe_sum (s : Finset ι) (f : ι -> Real>=0) : ∑ i in s, f 
i = ∑ i in s, (f i : Real)
· 使用定理 `PiLp.norm_eq_of_L1`：norm_eq_of_L1 (x : PiLp 1 β) : ‖x‖ = ∑ i : ι, ‖x i‖
-/
theorem nnnorm_eq_of_L1 (x : PiLp 1 β) : ‖x‖₊ = ∑ i : ι, ‖x i‖₊ :=
  NNReal.eq <| by push_cast; exact norm_eq_of_L1 x
/-
**PiLp.dist_eq_of_L1** 是 Mathlib 中的一个定理，位于命名空间 `PiLp`。
形式化陈述：dist_eq_of_L1 (x y : PiLp 1 β) : dist x y = ∑ i, dist (x i) (y i)
参数：x y : PiLp 1 β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `PiLp.norm_eq_of_L1`：norm_eq_of_L1 (x : PiLp 1 β) : ‖x‖ = ∑ i : ι, ‖x i‖
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem dist_eq_of_L1 (x y : PiLp 1 β) : dist x y = ∑ i, dist (x i) (y i) := by
  simp_rw [dist_eq_norm, norm_eq_of_L1, sub_apply]
/-
**PiLp.nndist_eq_of_L1** 是 Mathlib 中的一个定理，位于命名空间 `PiLp`。
形式化陈述：nndist_eq_of_L1 (x y : PiLp 1 β) : nndist x y = ∑ i, nndist (x i) (y i)
参数：x y : PiLp 1 β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NNReal.coe_sum`：coe_sum (s : Finset ι) (f : ι -> Real>=0) : ∑ i in s, f 
i = ∑ i in s, (f i : Real)
· 使用定理 `PiLp.dist_eq_of_L1`：dist_eq_of_L1 (x y : PiLp 1 β) : dist x y = ∑ i, dis
t (x i) (y i)
-/
theorem nndist_eq_of_L1 (x y : PiLp 1 β) : nndist x y = ∑ i, nndist (x i) (y i) :=
  NNReal.eq <| by push_cast; exact dist_eq_of_L1 _ _

set_option backward.isDefEq.respectTransparency false in
/-
**PiLp.edist_eq_of_L1** 是 Mathlib 中的一个定理，位于命名空间 `PiLp`。
形式化陈述：edist_eq_of_L1 (x y : PiLp 1 β) : edist x y = ∑ i, edist (x i) (y i)
参数：x y : PiLp 1 β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PiLp.edist_eq_sum`：edist_eq_sum {p : Real>=0∞} (hp : 0 < p.toReal) (f g 
: PiLp p β) : edist f g = (∑ i, edist (f i) (g i) ^ p.toReal) ^ (1 / p.toReal)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `ENNReal.rpow_one`：rpow_one (x : Real>=0∞) : x ^ (1 : Real) = x
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem edist_eq_of_L1 (x y : PiLp 1 β) : edist x y = ∑ i, edist (x i) (y i) := by
  simp [PiLp.edist_eq_sum]

end L1

section L2
variable {β} [∀ i, SeminormedAddCommGroup (β i)]

/-
**PiLp.norm_eq_of_L2** 是 Mathlib 中的一个定理，位于命名空间 `PiLp`。
形式化陈述：norm_eq_of_L2 (x : PiLp 2 β) : ‖x‖ = √(∑ i : ι, ‖x i‖ ^ 2)
参数：x : PiLp 2 β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PiLp.norm_eq_of_nat`：norm_eq_of_nat {p : Real>=0∞} [Fact (1 <= p)] {β : 
ι -> Type*} [forall i, SeminormedAddCommGroup (β i)] (n : Nat) (h : p = n) (f : 
PiLp p β)…
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `Real.sqrt_eq_rpow`：sqrt_eq_rpow (x : Real) : √x = x ^ (1 / (2 : Real))
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
-/
theorem norm_eq_of_L2 (x : PiLp 2 β) :
    ‖x‖ = √(∑ i : ι, ‖x i‖ ^ 2) := by
  rw [norm_eq_of_nat 2 (by norm_cast) _]
  rw [Real.sqrt_eq_rpow]
  norm_cast
/-
**PiLp.nnnorm_eq_of_L2** 是 Mathlib 中的一个定理，位于命名空间 `PiLp`。
形式化陈述：nnnorm_eq_of_L2 (x : PiLp 2 β) : ‖x‖₊ = NNReal.sqrt (∑ i : ι, ‖x i‖₊ ^ 2)
参数：x : PiLp 2 β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Real.coe_sqrt`：coe_sqrt {x : Real>=0} : (NNReal.sqrt x : Real) = √(x : R
eal)
· 使用定理 `NNReal.coe_sum`：coe_sum (s : Finset ι) (f : ι -> Real>=0) : ∑ i in s, f 
i = ∑ i in s, (f i : Real)
· 使用定理 `PiLp.norm_eq_of_L2`：norm_eq_of_L2 (x : PiLp 2 β) : ‖x‖ = √(∑ i : ι, ‖x i
‖ ^ 2)
-/
theorem nnnorm_eq_of_L2 (x : PiLp 2 β) :
    ‖x‖₊ = NNReal.sqrt (∑ i : ι, ‖x i‖₊ ^ 2) :=
  NNReal.eq <| by
    push_cast
    exact norm_eq_of_L2 x
/-
**PiLp.norm_sq_eq_of_L2** 是 Mathlib 中的一个定理，位于命名空间 `PiLp`。
形式化陈述：norm_sq_eq_of_L2 (β : ι -> Type*) [forall i, SeminormedAddCommGroup (β i)]
 (x : PiLp 2 β) : ‖x‖ ^ 2 = ∑ i : ι, ‖x i‖ ^ 2
参数：β : ι -> Type*；β i；x : PiLp 2 β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PiLp.nnnorm_eq_of_L2`：nnnorm_eq_of_L2 (x : PiLp 2 β) : ‖x‖₊ = NNReal.sqr
t (∑ i : ι, ‖x i‖₊ ^ 2)
· 使用定理 `NNReal.sq_sqrt`：∀ (x : NNReal), NNReal.sqrt x ^ 2 = x
· 使用定理 `NNReal.coe_sum`：coe_sum (s : Finset ι) (f : ι -> Real>=0) : ∑ i in s, f 
i = ∑ i in s, (f i : Real)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem norm_sq_eq_of_L2 (β : ι → Type*) [∀ i, SeminormedAddCommGroup (β i)] (x : PiLp 2 β) :
    ‖x‖ ^ 2 = ∑ i : ι, ‖x i‖ ^ 2 := by
  suffices ‖x‖₊ ^ 2 = ∑ i : ι, ‖x i‖₊ ^ 2 by
    simpa only [NNReal.coe_sum] using! congr_arg ((↑) : ℝ≥0 → ℝ) this
  rw [nnnorm_eq_of_L2, NNReal.sq_sqrt]
/-
**PiLp.dist_eq_of_L2** 是 Mathlib 中的一个定理，位于命名空间 `PiLp`。
形式化陈述：dist_eq_of_L2 (x y : PiLp 2 β) : dist x y = √(∑ i, dist (x i) (y i) ^ 2)
参数：x y : PiLp 2 β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `PiLp.norm_eq_of_L2`：norm_eq_of_L2 (x : PiLp 2 β) : ‖x‖ = √(∑ i : ι, ‖x i
‖ ^ 2)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem dist_eq_of_L2 (x y : PiLp 2 β) :
    dist x y = √(∑ i, dist (x i) (y i) ^ 2) := by
  simp_rw [dist_eq_norm, norm_eq_of_L2, sub_apply]
/-
**PiLp.dist_sq_eq_of_L2** 是 Mathlib 中的一个定理，位于命名空间 `PiLp`。
形式化陈述：dist_sq_eq_of_L2 (x y : PiLp 2 β) : dist x y ^ 2 = ∑ i, dist (x i) (y i) ^
 2
参数：x y : PiLp 2 β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `PiLp.norm_sq_eq_of_L2`：norm_sq_eq_of_L2 (β : ι -> Type*) [forall i, Semi
normedAddCommGroup (β i)] (x : PiLp 2 β) : ‖x‖ ^ 2 = ∑ i : ι, ‖x i‖ ^ 2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem dist_sq_eq_of_L2 (x y : PiLp 2 β) :
    dist x y ^ 2 = ∑ i, dist (x i) (y i) ^ 2 := by
  simp_rw [dist_eq_norm, norm_sq_eq_of_L2, sub_apply]
/-
**PiLp.nndist_eq_of_L2** 是 Mathlib 中的一个定理，位于命名空间 `PiLp`。
形式化陈述：nndist_eq_of_L2 (x y : PiLp 2 β) : nndist x y = NNReal.sqrt (∑ i, nndist (
x i) (y i) ^ 2)
参数：x y : PiLp 2 β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Real.coe_sqrt`：coe_sqrt {x : Real>=0} : (NNReal.sqrt x : Real) = √(x : R
eal)
· 使用定理 `NNReal.coe_sum`：coe_sum (s : Finset ι) (f : ι -> Real>=0) : ∑ i in s, f 
i = ∑ i in s, (f i : Real)
· 使用定理 `PiLp.dist_eq_of_L2`：dist_eq_of_L2 (x y : PiLp 2 β) : dist x y = √(∑ i, d
ist (x i) (y i) ^ 2)
-/
theorem nndist_eq_of_L2 (x y : PiLp 2 β) :
    nndist x y = NNReal.sqrt (∑ i, nndist (x i) (y i) ^ 2) :=
  NNReal.eq <| by
    push_cast
    exact dist_eq_of_L2 _ _
/-
**PiLp.edist_eq_of_L2** 是 Mathlib 中的一个定理，位于命名空间 `PiLp`。
形式化陈述：edist_eq_of_L2 (x y : PiLp 2 β) : edist x y = (∑ i, edist (x i) (y i) ^ 2)
 ^ (1 / 2 : Real)
参数：x y : PiLp 2 β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PiLp.edist_eq_sum`：edist_eq_sum {p : Real>=0∞} (hp : 0 < p.toReal) (f g 
: PiLp p β) : edist f g = (∑ i, edist (f i) (g i) ^ p.toReal) ^ (1 / p.toReal)
· 使用定理 `ENNReal.toReal_ofNat`：∀ (n : ℕ) [inst : n.AtLeastTwo], (OfNat.ofNat n).t
oReal = OfNat.ofNat n
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `ENNReal.rpow_ofNat`：rpow_ofNat (x : Real>=0∞) (n : Nat) [n.AtLeastTwo] :
 x ^ (ofNat(n) : Real) = x ^ (OfNat.ofNat n)
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem edist_eq_of_L2 (x y : PiLp 2 β) :
    edist x y = (∑ i, edist (x i) (y i) ^ 2) ^ (1 / 2 : ℝ) := by simp [PiLp.edist_eq_sum]

end L2

/-
**PiLp.instIsBoundedSMul** 是 Mathlib 中的一个实例，位于命名空间 `PiLp`。
形式化陈述：instIsBoundedSMul [SeminormedRing 𝕜] [forall i, SeminormedAddCommGroup (β 
i)] [forall i, Module 𝕜 (β i)] [forall i, IsBoundedSMul 𝕜 (β i)] : IsBoundedSMul
 𝕜 (PiLp p β)
参数：β i；β i；β i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBoundedSMul.of_nnnorm_smul_le`：IsBoundedSMul.of_nnnorm_smul_le (h : fo
rall (r : α) (x : β), ‖r • x‖₊ <= ‖r‖₊ * ‖x‖₊) : IsBoundedSMul α β
· 使用定理 `ENNReal.dichotomy`：∀ (p : ENNReal) [Fact (1 ≤ p)], p = ⊤ ∨ 1 ≤ p.toReal
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `fact_one_le_top_ennreal`：Fact (1 ≤ ⊤)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PiLp.nnnorm_ofLp`：∀ {ι : Type u_2} {β : ι → Type u_4} [inst : Fintype ι]
 [inst_1 : (i : ι) → SeminormedAddCommGroup (β i)] (f : PiLp ⊤ β),   ‖f.ofLp‖₊ =
 ‖f‖₊
· 使用定理 `WithLp.ofLp_smul`：∀ (p : ENNReal) {K : Type u_1} {V : Type u_4} [inst : 
SMul K V] (c : K) (x : WithLp p V), (c • x).ofLp = c • x.ofLp
· 使用定理 `nnnorm_smul_le`：nnnorm_smul_le (r : α) (x : β) : ‖r • x‖₊ <= ‖r‖₊ * ‖x‖₊
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ENNReal.toReal_pos_iff_ne_top`：toReal_pos_iff_ne_top (p : Real>=0∞) [Fac
t (1 <= p)] : 0 < p.toReal ↔ p != ∞
· 使用定理 `PiLp.nnnorm_eq_sum`：nnnorm_eq_sum {p : Real>=0∞} [Fact (1 <= p)] {β : ι 
-> Type*} (hp : p != ∞) [forall i, SeminormedAddCommGroup (β i)] (f : PiLp p β) 
: ‖f‖₊ =…
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `NNReal.rpow_inv_le_iff`：rpow_inv_le_iff {x y : Real>=0} {z : Real} (hz :
 0 < z) : x ^ z⁻¹ <= y ↔ x <= y ^ z
· 使用定理 `NNReal.mul_rpow`：mul_rpow {x y : Real>=0} {z : Real} : (x * y) ^ z = x ^
 z * y ^ z
· 使用定理 `NNReal.rpow_mul`：rpow_mul (x : Real>=0) (y z : Real) : x ^ (y * z) = (x 
^ y) ^ z
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `NNReal.rpow_one`：rpow_one (x : Real>=0) : x ^ (1 : Real) = x
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f g : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈
 s, f i…
· 使用定理 `NNReal.rpow_le_rpow`：∀ {x y : NNReal} {z : ℝ}, x ≤ y → 0 ≤ z → x ^ z ≤ y
 ^ z
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
-/
instance instIsBoundedSMul [SeminormedRing 𝕜] [∀ i, SeminormedAddCommGroup (β i)]
    [∀ i, Module 𝕜 (β i)] [∀ i, IsBoundedSMul 𝕜 (β i)] :
    IsBoundedSMul 𝕜 (PiLp p β) :=
  .of_nnnorm_smul_le fun c f => by
    rcases p.dichotomy with (rfl | hp)
    · rw [← nnnorm_ofLp, ← nnnorm_ofLp, ofLp_smul]
      exact nnnorm_smul_le c (ofLp f)
    · have hp0 : 0 < p.toReal := zero_lt_one.trans_le hp
      have hpt : p ≠ ⊤ := p.toReal_pos_iff_ne_top.mp hp0
      rw [nnnorm_eq_sum hpt, nnnorm_eq_sum hpt, one_div, NNReal.rpow_inv_le_iff hp0,
        NNReal.mul_rpow, ← NNReal.rpow_mul, inv_mul_cancel₀ hp0.ne', NNReal.rpow_one,
        Finset.mul_sum]
      simp_rw [← NNReal.mul_rpow, smul_apply]
      gcongr
      apply nnnorm_smul_le
/-
**PiLp.instNormSMulClass** 是 Mathlib 中的一个实例，位于命名空间 `PiLp`。
形式化陈述：instNormSMulClass [SeminormedRing 𝕜] [forall i, SeminormedAddCommGroup (β 
i)] [forall i, Module 𝕜 (β i)] [forall i, NormSMulClass 𝕜 (β i)] : NormSMulClass
 𝕜 (PiLp p β)
参数：β i；β i；β i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `NormSMulClass.of_nnnorm_smul`：NormSMulClass.of_nnnorm_smul (h : forall (
r : α) (x : β), ‖r • x‖₊ = ‖r‖₊ * ‖x‖₊) : NormSMulClass α β where norm_smul r b
· 使用定理 `ENNReal.dichotomy`：∀ (p : ENNReal) [Fact (1 ≤ p)], p = ⊤ ∨ 1 ≤ p.toReal
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `fact_one_le_top_ennreal`：Fact (1 ≤ ⊤)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PiLp.nnnorm_ofLp`：∀ {ι : Type u_2} {β : ι → Type u_4} [inst : Fintype ι]
 [inst_1 : (i : ι) → SeminormedAddCommGroup (β i)] (f : PiLp ⊤ β),   ‖f.ofLp‖₊ =
 ‖f‖₊
· 使用定理 `WithLp.ofLp_smul`：∀ (p : ENNReal) {K : Type u_1} {V : Type u_4} [inst : 
SMul K V] (c : K) (x : WithLp p V), (c • x).ofLp = c • x.ofLp
· 使用定理 `nnnorm_smul`：nnnorm_smul (r : α) (x : β) : ‖r • x‖₊ = ‖r‖₊ * ‖x‖₊
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ENNReal.toReal_pos_iff_ne_top`：toReal_pos_iff_ne_top (p : Real>=0∞) [Fac
t (1 <= p)] : 0 < p.toReal ↔ p != ∞
· 使用定理 `PiLp.nnnorm_eq_sum`：nnnorm_eq_sum {p : Real>=0∞} [Fact (1 <= p)] {β : ι 
-> Type*} (hp : p != ∞) [forall i, SeminormedAddCommGroup (β i)] (f : PiLp p β) 
: ‖f‖₊ =…
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `NNReal.rpow_inv_eq_iff`：rpow_inv_eq_iff {x y : Real>=0} {z : Real} (hz :
 z != 0) : x ^ z⁻¹ = y ↔ x = y ^ z
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `NNReal.mul_rpow`：mul_rpow {x y : Real>=0} {z : Real} : (x * y) ^ z = x ^
 z * y ^ z
· 使用定理 `NNReal.rpow_mul`：rpow_mul (x : Real>=0) (y z : Real) : x ^ (y * z) = (x 
^ y) ^ z
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `NNReal.rpow_one`：rpow_one (x : Real>=0) : x ^ (1 : Real) = x
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance instNormSMulClass [SeminormedRing 𝕜] [∀ i, SeminormedAddCommGroup (β i)]
    [∀ i, Module 𝕜 (β i)] [∀ i, NormSMulClass 𝕜 (β i)] :
    NormSMulClass 𝕜 (PiLp p β) :=
  .of_nnnorm_smul fun c f => by
    rcases p.dichotomy with (rfl | hp)
    · rw [← nnnorm_ofLp, ← nnnorm_ofLp, WithLp.ofLp_smul, nnnorm_smul]
    · have hp0 : 0 < p.toReal := zero_lt_one.trans_le hp
      have hpt : p ≠ ⊤ := p.toReal_pos_iff_ne_top.mp hp0
      rw [nnnorm_eq_sum hpt, nnnorm_eq_sum hpt, one_div, NNReal.rpow_inv_eq_iff hp0.ne',
        NNReal.mul_rpow, ← NNReal.rpow_mul, inv_mul_cancel₀ hp0.ne', NNReal.rpow_one,
        Finset.mul_sum]
      simp_rw [← NNReal.mul_rpow, smul_apply, nnnorm_smul]

/-- The product of finitely many normed spaces is a normed space, with the `L^p` norm. -/
/-
**PiLp.normedSpace** 是 Mathlib 中的一个实例，位于命名空间 `PiLp`。
形式化陈述：normedSpace [NormedField 𝕜] [forall i, SeminormedAddCommGroup (β i)] [fora
ll i, NormedSpace 𝕜 (β i)] : NormedSpace 𝕜 (PiLp p β) where norm_smul_le
参数：β i；β i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The product of finitely many normed spaces is a normed space, with the `L^p` nor
m.
-/
instance normedSpace [NormedField 𝕜] [∀ i, SeminormedAddCommGroup (β i)]
    [∀ i, NormedSpace 𝕜 (β i)] : NormedSpace 𝕜 (PiLp p β) where
  norm_smul_le := norm_smul_le

variable {𝕜 p α}
variable [Semiring 𝕜] [∀ i, SeminormedAddCommGroup (α i)] [∀ i, SeminormedAddCommGroup (β i)]
variable [∀ i, Module 𝕜 (α i)] [∀ i, Module 𝕜 (β i)] (c : 𝕜)

/-- The canonical map `WithLp.equiv` between `PiLp ∞ β` and `Π i, β i` as a linear isometric
equivalence. -/
/-
**PiLp.equiv** 是 Mathlib 中的一个定义，位于命名空间 `PiLp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical map `WithLp.equiv` between `PiLp ∞ β` and `Π i, β i` as a linear i
sometric
equivalence.
-/
def equivₗᵢ : PiLp ∞ β ≃ₗᵢ[𝕜] (∀ i, β i) where
  __ := WithLp.linearEquiv ∞ 𝕜 _
  norm_map' := norm_ofLp

section piLpCongrLeft
variable {ι' : Type*}
variable [Fintype ι']
variable (p 𝕜)
variable (E : Type*) [SeminormedAddCommGroup E] [Module 𝕜 E]

/-- An equivalence of finite domains induces a linearly isometric equivalence of finitely supported
functions. -/
/-
**PiLp._root_.LinearIsometryEquiv.piLpCongrLeft** 是 Mathlib 中的一个定义，位于命名空间 `PiLp`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An equivalence of finite domains induces a linearly isometric equivalence of fin
itely supported
functions.
-/
def _root_.LinearIsometryEquiv.piLpCongrLeft (e : ι ≃ ι') :
    (PiLp p fun _ : ι => E) ≃ₗᵢ[𝕜] PiLp p fun _ : ι' => E where
  toLinearEquiv := (WithLp.linearEquiv p 𝕜 (ι → E)).trans
    ((LinearEquiv.piCongrLeft' 𝕜 (fun _ : ι => E) e).trans (WithLp.linearEquiv p 𝕜 (ι' → E)).symm)
  norm_map' x' := by
    rcases p.dichotomy with (rfl | h)
    · simp_rw [norm_eq_ciSup]
      exact e.symm.iSup_congr fun _ => rfl
    · simp only [norm_eq_sum (zero_lt_one.trans_le h)]
      congr 1
      exact Fintype.sum_equiv e.symm _ _ fun _ => rfl

variable {p 𝕜 E}

@[simp]
/-
**PiLp._root_.LinearIsometryEquiv.piLpCongrLeft_apply** 是 Mathlib 中的一个定理，位于命名空间 
`PiLp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.LinearIsometryEquiv.piLpCongrLeft_apply (e : ι ≃ ι') (v : PiLp p fun _ : ι => E) :
    LinearIsometryEquiv.piLpCongrLeft p 𝕜 E e v = Equiv.piCongrLeft' (fun _ : ι => E) e v :=
  rfl

@[simp]
/-
**PiLp._root_.LinearIsometryEquiv.piLpCongrLeft_symm** 是 Mathlib 中的一个定理，位于命名空间 `
PiLp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.LinearIsometryEquiv.piLpCongrLeft_symm (e : ι ≃ ι') :
    (LinearIsometryEquiv.piLpCongrLeft p 𝕜 E e).symm =
      LinearIsometryEquiv.piLpCongrLeft p 𝕜 E e.symm := by
  ext
  simp [LinearIsometryEquiv.piLpCongrLeft, LinearIsometryEquiv.symm]

@[simp high]
/-
**PiLp._root_.LinearIsometryEquiv.piLpCongrLeft_single** 是 Mathlib 中的一个定理，位于命名空间
 `PiLp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.LinearIsometryEquiv.piLpCongrLeft_single [DecidableEq ι] [DecidableEq ι']
    (e : ι ≃ ι') (i : ι) (v : E) :
    LinearIsometryEquiv.piLpCongrLeft p 𝕜 E e (single p i v) = single p (e i) v := by
  ext x
  simp [LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft',
    Pi.single, Function.update, Equiv.symm_apply_eq]

end piLpCongrLeft

section piLpCongrRight
variable {β}

variable (p) in
/-- A family of linearly isometric equivalences in the codomain induces an isometric equivalence
between Pi types with the Lp norm.

This is the isometry version of `LinearEquiv.piCongrRight`. -/
/-
**PiLp._root_.LinearIsometryEquiv.piLpCongrRight** 是 Mathlib 中的一个定义，位于命名空间 `PiLp
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A family of linearly isometric equivalences in the codomain induces an isometric
 equivalence
between Pi types with the Lp norm.

This is the isometry version of `LinearEquiv.piCongrRight`.
-/
protected def _root_.LinearIsometryEquiv.piLpCongrRight (e : ∀ i, α i ≃ₗᵢ[𝕜] β i) :
    PiLp p α ≃ₗᵢ[𝕜] PiLp p β where
  toLinearEquiv :=
    WithLp.linearEquiv _ _ _
      ≪≫ₗ (LinearEquiv.piCongrRight fun i => (e i).toLinearEquiv)
      ≪≫ₗ (WithLp.linearEquiv _ _ _).symm
  norm_map' := (WithLp.linearEquiv p 𝕜 _).symm.surjective.forall.2 fun x => by
    simp only [coe_symm_linearEquiv, LinearEquiv.trans_apply, coe_linearEquiv]
    obtain rfl | hp := p.dichotomy
    · simp_rw [PiLp.norm_toLp, Pi.norm_def, LinearEquiv.piCongrRight_apply,
        LinearIsometryEquiv.coe_toLinearEquiv, LinearIsometryEquiv.nnnorm_map]
    · have : 0 < p.toReal := zero_lt_one.trans_le <| by norm_cast
      simp only [PiLp.norm_eq_sum this, LinearEquiv.piCongrRight_apply,
        LinearIsometryEquiv.coe_toLinearEquiv, LinearIsometryEquiv.norm_map, one_div]

@[simp]
/-
**PiLp._root_.LinearIsometryEquiv.piLpCongrRight_apply** 是 Mathlib 中的一个定理，位于命名空间
 `PiLp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.LinearIsometryEquiv.piLpCongrRight_apply (e : ∀ i, α i ≃ₗᵢ[𝕜] β i) (x : PiLp p α) :
    LinearIsometryEquiv.piLpCongrRight p e x = toLp p fun i => e i (x i) := rfl

@[simp]
/-
**PiLp._root_.LinearIsometryEquiv.piLpCongrRight_refl** 是 Mathlib 中的一个定理，位于命名空间 
`PiLp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.LinearIsometryEquiv.piLpCongrRight_refl :
    LinearIsometryEquiv.piLpCongrRight p (fun i => .refl 𝕜 (α i)) = .refl _ _ :=
  rfl

@[simp]
/-
**PiLp._root_.LinearIsometryEquiv.piLpCongrRight_symm** 是 Mathlib 中的一个定理，位于命名空间 
`PiLp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.LinearIsometryEquiv.piLpCongrRight_symm (e : ∀ i, α i ≃ₗᵢ[𝕜] β i) :
    (LinearIsometryEquiv.piLpCongrRight p e).symm =
      LinearIsometryEquiv.piLpCongrRight p (fun i => (e i).symm) :=
  rfl

@[simp high]
/-
**PiLp._root_.LinearIsometryEquiv.piLpCongrRight_single** 是 Mathlib 中的一个定理，位于命名空
间 `PiLp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.LinearIsometryEquiv.piLpCongrRight_single (e : ∀ i, α i ≃ₗᵢ[𝕜] β i) [DecidableEq ι]
    (i : ι) (v : α i) :
    LinearIsometryEquiv.piLpCongrRight p e (single p i v) = single p i (e _ v) :=
  PiLp.ext <| Pi.apply_single (e ·) (fun _ => map_zero _) _ _

end piLpCongrRight

section piLpCurry

variable {ι : Type*} {κ : ι → Type*} (p : ℝ≥0∞) [Fact (1 ≤ p)]
  [Fintype ι] [∀ i, Fintype (κ i)]
  (α : ∀ i, κ i → Type*) [∀ i k, SeminormedAddCommGroup (α i k)] [∀ i k, Module 𝕜 (α i k)]

variable (𝕜) in
/-- `LinearEquiv.piCurry` for `PiLp`, as an isometry. -/
/-
**PiLp._root_.LinearIsometryEquiv.piLpCurry** 是 Mathlib 中的一个定义，位于命名空间 `PiLp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`LinearEquiv.piCurry` for `PiLp`, as an isometry.
-/
def _root_.LinearIsometryEquiv.piLpCurry :
    PiLp p (fun i : Sigma _ => α i.1 i.2) ≃ₗᵢ[𝕜] PiLp p (fun i => PiLp p (α i)) where
  toLinearEquiv :=
    WithLp.linearEquiv _ _ _
      ≪≫ₗ LinearEquiv.piCurry 𝕜 α
      ≪≫ₗ (LinearEquiv.piCongrRight fun _ => (WithLp.linearEquiv _ _ _).symm)
      ≪≫ₗ (WithLp.linearEquiv _ _ _).symm
  norm_map' := (WithLp.linearEquiv p 𝕜 _).symm.surjective.forall.2 fun x => by
    simp_rw [← coe_nnnorm, NNReal.coe_inj, WithLp.linearEquiv_symm_apply]
    obtain rfl | hp := eq_or_ne p ⊤
    · simp [Pi.nnnorm_def, ← Finset.univ_sigma_univ, Finset.sup_sigma, Sigma.curry]
    · have : 0 < p.toReal := (toReal_pos_iff_ne_top _).mpr hp
      simp [nnnorm_eq_sum hp, this.ne', ← Finset.univ_sigma_univ, Finset.sum_sigma, Sigma.curry]
/-
**PiLp._root_.LinearIsometryEquiv.piLpCurry_apply** 是 Mathlib 中的一个定理，位于命名空间 `PiL
p`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem _root_.LinearIsometryEquiv.piLpCurry_apply
    (f : PiLp p (fun i : Sigma κ => α i.1 i.2)) :
    _root_.LinearIsometryEquiv.piLpCurry 𝕜 p α f =
      toLp p (fun i => (toLp p) <| Sigma.curry (ofLp f) i) :=
  rfl
/-
**PiLp._root_.LinearIsometryEquiv.piLpCurry_symm_apply** 是 Mathlib 中的一个定理，位于命名空间
 `PiLp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem _root_.LinearIsometryEquiv.piLpCurry_symm_apply
    (f : PiLp p (fun i => PiLp p (α i))) :
    (_root_.LinearIsometryEquiv.piLpCurry 𝕜 p α).symm f =
      toLp p (Sigma.uncurry fun i j => f i j) :=
  rfl

end piLpCurry

section sumPiLpEquivProdLpPiLp

variable {ι κ : Type*} (p : ℝ≥0∞) (α : ι ⊕ κ → Type*) [Fintype ι] [Fintype κ] [Fact (1 ≤ p)]
variable [∀ i, SeminormedAddCommGroup (α i)] [∀ i, Module 𝕜 (α i)]

/-- `LinearEquiv.sumPiEquivProdPi` for `PiLp`, as an isometry. -/
@[simps! +simpRhs]
/-
**PiLp.sumPiLpEquivProdLpPiLp** 是 Mathlib 中的一个定义，位于命名空间 `PiLp`。
形式化陈述：sumPiLpEquivProdLpPiLp : WithLp p (Π i, α i) ≃ₗᵢ[𝕜] WithLp p (WithLp p (Π 
i, α (.inl i)) × WithLp p (Π i, α (.inr i))) where toLinearEquiv
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`LinearEquiv.sumPiEquivProdPi` for `PiLp`, as an isometry.
-/
def sumPiLpEquivProdLpPiLp :
    WithLp p (Π i, α i) ≃ₗᵢ[𝕜]
      WithLp p (WithLp p (Π i, α (.inl i)) × WithLp p (Π i, α (.inr i))) where
  toLinearEquiv :=
    WithLp.linearEquiv p _ _
      ≪≫ₗ LinearEquiv.sumPiEquivProdPi _ _ _ α
      ≪≫ₗ LinearEquiv.prodCongr (WithLp.linearEquiv p _ _).symm
        (WithLp.linearEquiv _ _ _).symm
      ≪≫ₗ (WithLp.linearEquiv p _ _).symm
  norm_map' := (WithLp.linearEquiv p 𝕜 _).symm.surjective.forall.2 fun x => by
    obtain rfl | hp := p.dichotomy
    · simp [← Finset.univ_disjSum_univ, Finset.sup_disjSum, Pi.norm_def]
    · have : 0 < p.toReal := by positivity
      have hpt : p ≠ ⊤ := (toReal_pos_iff_ne_top p).mp this
      simp_rw [← coe_nnnorm]; congr 1 -- convert to nnnorm to avoid needing positivity arguments
      simp [nnnorm_eq_sum hpt, WithLp.prod_nnnorm_eq_add hpt, NNReal.rpow_inv_rpow this.ne']

end sumPiLpEquivProdLpPiLp

section Single

variable (p)
variable [DecidableEq ι]

@[simp]
/-
**PiLp.nnnorm_single** 是 Mathlib 中的一个定理，位于命名空间 `PiLp`。
形式化陈述：nnnorm_single (i : ι) (b : β i) : ‖single p i b‖₊ = ‖b‖₊
参数：i : ι；b : β i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PiLp.nnnorm_eq_ciSup`：nnnorm_eq_ciSup (f : PiLp ∞ β) : ‖f‖₊ = ⨆ i, ‖f i‖
₊
· 使用定理 `ciSup_eq_of_forall_le_of_forall_lt_exists_gt`：ciSup_eq_of_forall_le_of_f
orall_lt_exists_gt [Nonempty ι] {f : ι -> α} (h₁ : forall i, f i <= b) (h₂ : for
all w, w < b -> exists i, w < f i)…
· 使用定理 `Decidable.eq_or_ne`：Decidable.eq_or_ne {α : Sort*} (x y : α) [Decidable 
(x = y)] : x = y ∨ x != y
· 使用引理 `PiLp.single_eq_same`：single_eq_same (i : ι) (a : β i) : single p i a i =
 a
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `PiLp.single_eq_of_ne'`：single_eq_of_ne' {i i' : ι} (h : i != i') (a : β 
i) : single p i a i' = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `nnnorm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖₊ = 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `LT.lt.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LT α], a < b → b = 
c → a < c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `ENNReal.instIsOrderedRing`：IsOrderedRing ENNReal
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `PiLp.nnnorm_eq_sum`：nnnorm_eq_sum {p : Real>=0∞} [Fact (1 <= p)] {β : ι 
-> Type*} (hp : p != ∞) [forall i, SeminormedAddCommGroup (β i)] (f : PiLp p β) 
: ‖f‖₊ =…
· 使用定理 `ENNReal.coe_ne_top`：coe_ne_top : (r : Real>=0∞) != ∞
· 使用定理 `ENNReal.coe_toReal`：∀ (r : NNReal), (↑r).toReal = ↑r
· 使用定理 `Fintype.sum_eq_single`：∀ {α : Type u_1} {M : Type u_4} [inst : Fintype α
] [inst_1 : AddCommMonoid M] {f : α → M} (a : α),   (∀ (x : α), x ≠ a → f x = 0)
 → ∑ x, f x…
· 使用引理 `PiLp.toLp_apply`：toLp_apply (x : forall i, α i) (i : ι) : toLp p x i = x
 i
· 使用引理 `PiLp.single_eq_of_ne`：single_eq_of_ne {i i' : ι} (h : i' != i) (a : β i)
 : single p i a i' = 0
（共 35 条，此处仅展示前 30 条）
-/
theorem nnnorm_single (i : ι) (b : β i) : ‖single p i b‖₊ = ‖b‖₊ := by
  have : Nonempty ι := ⟨i⟩
  induction p generalizing hp with
  | top =>
    simp_rw [nnnorm_eq_ciSup]
    refine
      ciSup_eq_of_forall_le_of_forall_lt_exists_gt (fun j => ?_) fun n hn => ⟨i, hn.trans_eq ?_⟩
    · obtain rfl | hij := Decidable.eq_or_ne i j
      · rw [single_eq_same]
      · simp [hij]
    · rw [single_eq_same]
  | coe p =>
    have hp0 : (p : ℝ) ≠ 0 :=
      mod_cast (zero_lt_one.trans_le <| Fact.out (p := 1 ≤ (p : ℝ≥0∞))).ne'
    rw [nnnorm_eq_sum ENNReal.coe_ne_top, ENNReal.coe_toReal, Fintype.sum_eq_single i,
      toLp_apply, single_eq_same, ← NNReal.rpow_mul, one_div,
      mul_inv_cancel₀ hp0, NNReal.rpow_one]
    intro j hij
    rw [toLp_apply, single_eq_of_ne _ hij, nnnorm_zero, NNReal.zero_rpow hp0]

@[deprecated nnnorm_single (since := "2026-03-15")]
/-
**PiLp.nnnorm_toLp_single** 是 Mathlib 中的一个定理，位于命名空间 `PiLp`。
形式化陈述：nnnorm_toLp_single (i : ι) (b : β i) : ‖toLp p (Pi.single i b)‖₊ = ‖b‖₊
参数：i : ι；b : β i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PiLp.nnnorm_single`：nnnorm_single (i : ι) (b : β i) : ‖single p i b‖₊ = 
‖b‖₊
-/
theorem nnnorm_toLp_single (i : ι) (b : β i) : ‖toLp p (Pi.single i b)‖₊ = ‖b‖₊ :=
  nnnorm_single p β i b

@[simp]
/-
**PiLp.norm_single** 是 Mathlib 中的一个引理，位于命名空间 `PiLp`。
形式化陈述：norm_single (i : ι) (b : β i) : ‖single p i b‖ = ‖b‖
参数：i : ι；b : β i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `PiLp.nnnorm_single`：nnnorm_single (i : ι) (b : β i) : ‖single p i b‖₊ = 
‖b‖₊
-/
lemma norm_single (i : ι) (b : β i) : ‖single p i b‖ = ‖b‖ :=
  congr_arg ((↑) : ℝ≥0 → ℝ) <| nnnorm_single p β i b

@[deprecated norm_single (since := "2026-03-15")]
/-
**PiLp.norm_toLp_single** 是 Mathlib 中的一个引理，位于命名空间 `PiLp`。
形式化陈述：norm_toLp_single (i : ι) (b : β i) : ‖toLp p (Pi.single i b)‖ = ‖b‖
参数：i : ι；b : β i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `PiLp.norm_single`：norm_single (i : ι) (b : β i) : ‖single p i b‖ = ‖b‖
-/
lemma norm_toLp_single (i : ι) (b : β i) : ‖toLp p (Pi.single i b)‖ = ‖b‖ :=
  norm_single p β i b

@[simp]
/-
**PiLp.nndist_single_same** 是 Mathlib 中的一个引理，位于命名空间 `PiLp`。
形式化陈述：nndist_single_same (i : ι) (b₁ b₂ : β i) : nndist (single p i b₁) (single 
p i b₂) = nndist b₁ b₂
参数：i : ι；b₁ b₂ : β i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nndist_eq_nnnorm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a 
b : E), nndist a b = ‖a - b‖₊
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `PiLp.single_sub`：single_sub (p : Real>=0∞) (i : ι) {a b : β i} : single 
p i (a - b) = single p i a - single p i b
· 使用定理 `PiLp.nnnorm_single`：nnnorm_single (i : ι) (b : β i) : ‖single p i b‖₊ = 
‖b‖₊
-/
lemma nndist_single_same (i : ι) (b₁ b₂ : β i) :
    nndist (single p i b₁) (single p i b₂) = nndist b₁ b₂ := by
  rw [nndist_eq_nnnorm, nndist_eq_nnnorm, ← single_sub, nnnorm_single]

@[deprecated nndist_single_same (since := "2026-03-15")]
/-
**PiLp.nndist_toLp_single_same** 是 Mathlib 中的一个引理，位于命名空间 `PiLp`。
形式化陈述：nndist_toLp_single_same (i : ι) (b₁ b₂ : β i) : nndist (toLp p (Pi.single 
i b₁)) (toLp p (Pi.single i b₂)) = nndist b₁ b₂
参数：i : ι；b₁ b₂ : β i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `PiLp.nndist_single_same`：nndist_single_same (i : ι) (b₁ b₂ : β i) : nndi
st (single p i b₁) (single p i b₂) = nndist b₁ b₂
-/
lemma nndist_toLp_single_same (i : ι) (b₁ b₂ : β i) :
    nndist (toLp p (Pi.single i b₁)) (toLp p (Pi.single i b₂)) = nndist b₁ b₂ :=
  nndist_single_same p β i b₁ b₂

@[simp]
/-
**PiLp.dist_single_same** 是 Mathlib 中的一个引理，位于命名空间 `PiLp`。
形式化陈述：dist_single_same (i : ι) (b₁ b₂ : β i) : dist (single p i b₁) (single p i 
b₂) = dist b₁ b₂
参数：i : ι；b₁ b₂ : β i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用引理 `PiLp.nndist_single_same`：nndist_single_same (i : ι) (b₁ b₂ : β i) : nndi
st (single p i b₁) (single p i b₂) = nndist b₁ b₂
-/
lemma dist_single_same (i : ι) (b₁ b₂ : β i) :
    dist (single p i b₁) (single p i b₂) = dist b₁ b₂ :=
  congr_arg ((↑) : ℝ≥0 → ℝ) <| nndist_single_same p β i b₁ b₂

@[deprecated dist_single_same (since := "2026-03-15")]
/-
**PiLp.dist_toLp_single_same** 是 Mathlib 中的一个引理，位于命名空间 `PiLp`。
形式化陈述：dist_toLp_single_same (i : ι) (b₁ b₂ : β i) : dist (toLp p (Pi.single i b₁
)) (toLp p (Pi.single i b₂)) = dist b₁ b₂
参数：i : ι；b₁ b₂ : β i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `PiLp.dist_single_same`：dist_single_same (i : ι) (b₁ b₂ : β i) : dist (si
ngle p i b₁) (single p i b₂) = dist b₁ b₂
-/
lemma dist_toLp_single_same (i : ι) (b₁ b₂ : β i) :
    dist (toLp p (Pi.single i b₁)) (toLp p (Pi.single i b₂)) = dist b₁ b₂ :=
  dist_single_same p β i b₁ b₂

@[simp]
/-
**PiLp.edist_single_same** 是 Mathlib 中的一个引理，位于命名空间 `PiLp`。
形式化陈述：edist_single_same (i : ι) (b₁ b₂ : β i) : edist (single p i b₁) (single p 
i b₂) = edist b₁ b₂
参数：i : ι；b₁ b₂ : β i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `edist_nndist`：edist_nndist (x y : α) : edist x y = nndist x y
· 使用引理 `PiLp.nndist_single_same`：nndist_single_same (i : ι) (b₁ b₂ : β i) : nndi
st (single p i b₁) (single p i b₂) = nndist b₁ b₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma edist_single_same (i : ι) (b₁ b₂ : β i) :
    edist (single p i b₁) (single p i b₂) = edist b₁ b₂ := by
  simp only [edist_nndist, nndist_single_same p β i b₁ b₂]

@[deprecated edist_single_same (since := "2026-03-15")]
/-
**PiLp.edist_toLp_single_same** 是 Mathlib 中的一个引理，位于命名空间 `PiLp`。
形式化陈述：edist_toLp_single_same (i : ι) (b₁ b₂ : β i) : edist (toLp p (Pi.single i 
b₁)) (toLp p (Pi.single i b₂)) = edist b₁ b₂
参数：i : ι；b₁ b₂ : β i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `PiLp.edist_single_same`：edist_single_same (i : ι) (b₁ b₂ : β i) : edist 
(single p i b₁) (single p i b₂) = edist b₁ b₂
-/
lemma edist_toLp_single_same (i : ι) (b₁ b₂ : β i) :
    edist (toLp p (Pi.single i b₁)) (toLp p (Pi.single i b₂)) = edist b₁ b₂ :=
  edist_single_same p β i b₁ b₂

end Single

/-- When `p = ∞`, this lemma does not hold without the additional assumption `Nonempty ι` because
the left-hand side simplifies to `0`, while the right-hand side simplifies to `‖b‖₊`. See
`PiLp.nnnorm_equiv_symm_const'` for a version which exchanges the hypothesis `p ≠ ∞` for
`Nonempty ι`. -/
/-
**PiLp.nnnorm_toLp_const** 是 Mathlib 中的一个引理，位于命名空间 `PiLp`。
形式化陈述：nnnorm_toLp_const {β} [SeminormedAddCommGroup β] (hp : p != ∞) (b : β) : ‖
toLp p (Function.const ι b)‖₊ = (Fintype.card ι : Real>=0) ^ (1 / p).toReal * ‖b
‖₊
参数：hp : p != ∞；b : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.dichotomy`：∀ (p : ENNReal) [Fact (1 ≤ p)], p = ⊤ ∨ 1 ≤ p.toReal
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `PiLp.nnnorm_eq_sum`：nnnorm_eq_sum {p : Real>=0∞} [Fact (1 <= p)] {β : ι 
-> Type*} (hp : p != ∞) [forall i, SeminormedAddCommGroup (β i)] (f : PiLp p β) 
: ‖f‖₊ =…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `NNReal.mul_rpow`：mul_rpow {x y : Real>=0} {z : Real} : (x * y) ^ z = x ^
 z * y ^ z
· 使用引理 `mul_one_div_cancel`：mul_one_div_cancel (h : a != 0) : a * (1 / a) = 1
· 使用定理 `NNReal.rpow_one`：rpow_one (x : Real>=0) : x ^ (1 : Real) = x
· 使用定理 `ENNReal.toReal_div`：∀ (a b : ENNReal), (a / b).toReal = a.toReal / b.toR
eal
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
When `p = ∞`, this lemma does not hold without the additional assumption `Nonemp
ty ι` because
the left-hand side simplifies to `0`, while the right-hand side simplifies to `‖
b‖₊`. See
`PiLp.nnnorm_equiv_symm_const'` for a version which exchanges the hypothesis `p 
≠ ∞` for
`Nonempty ι`.
-/
lemma nnnorm_toLp_const {β} [SeminormedAddCommGroup β] (hp : p ≠ ∞) (b : β) :
    ‖toLp p (Function.const ι b)‖₊ =
      (Fintype.card ι : ℝ≥0) ^ (1 / p).toReal * ‖b‖₊ := by
  rcases p.dichotomy with (h | h)
  · exact False.elim (hp h)
  · have ne_zero : p.toReal ≠ 0 := (zero_lt_one.trans_le h).ne'
    simp_rw [nnnorm_eq_sum hp, Function.const_apply, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, NNReal.mul_rpow, ← NNReal.rpow_mul,
      mul_one_div_cancel ne_zero, NNReal.rpow_one, ENNReal.toReal_div, ENNReal.toReal_one]

/-- When `IsEmpty ι`, this lemma does not hold without the additional assumption `p ≠ ∞` because
the left-hand side simplifies to `0`, while the right-hand side simplifies to `‖b‖₊`. See
`PiLp.nnnorm_toLp_const` for a version which exchanges the hypothesis `Nonempty ι`.
for `p ≠ ∞`. -/
/-
**PiLp.nnnorm_toLp_const'** 是 Mathlib 中的一个引理，位于命名空间 `PiLp`。
形式化陈述：nnnorm_toLp_const' {β} [SeminormedAddCommGroup β] [Nonempty ι] (b : β) : ‖
toLp p (Function.const ι b)‖₊ = (Fintype.card ι : Real>=0) ^ (1 / p).toReal * ‖b
‖₊
参数：b : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `fact_one_le_top_ennreal`：Fact (1 ≤ ⊤)
· 使用定理 `PiLp.nnnorm_eq_ciSup`：nnnorm_eq_ciSup (f : PiLp ∞ β) : ‖f‖₊ = ⨆ i, ‖f i‖
₊
· 使用定理 `ciSup_const`：ciSup_const [hι : Nonempty ι] {a : α} : ⨆ _ : ι, a = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ENNReal.div_top`：∀ {a : ENNReal}, a / ⊤ = 0
· 使用定理 `NNReal.rpow_zero`：rpow_zero (x : Real>=0) : x ^ (0 : Real) = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `PiLp.nnnorm_toLp_const`：nnnorm_toLp_const {β} [SeminormedAddCommGroup β]
 (hp : p != ∞) (b : β) : ‖toLp p (Function.const ι b)‖₊ = (Fintype.card ι : Real
>=0) ^ (1 / …

--- 原说明 ---
When `IsEmpty ι`, this lemma does not hold without the additional assumption `p 
≠ ∞` because
the left-hand side simplifies to `0`, while the right-hand side simplifies to `‖
b‖₊`. See
`PiLp.nnnorm_toLp_const` for a version which exchanges the hypothesis `Nonempty 
ι`.
for `p ≠ ∞`.
-/
lemma nnnorm_toLp_const' {β} [SeminormedAddCommGroup β] [Nonempty ι] (b : β) :
    ‖toLp p (Function.const ι b)‖₊ =
      (Fintype.card ι : ℝ≥0) ^ (1 / p).toReal * ‖b‖₊ := by
  rcases em <| p = ∞ with (rfl | hp)
  · simp only [ENNReal.div_top, ENNReal.toReal_zero, NNReal.rpow_zero,
      one_mul, nnnorm_eq_ciSup, Function.const_apply, ciSup_const]
  · exact nnnorm_toLp_const hp b

/-- When `p = ∞`, this lemma does not hold without the additional assumption `Nonempty ι` because
the left-hand side simplifies to `0`, while the right-hand side simplifies to `‖b‖₊`. See
`PiLp.norm_toLp_const'` for a version which exchanges the hypothesis `p ≠ ∞` for
`Nonempty ι`. -/
/-
**PiLp.norm_toLp_const** 是 Mathlib 中的一个引理，位于命名空间 `PiLp`。
形式化陈述：norm_toLp_const {β} [SeminormedAddCommGroup β] (hp : p != ∞) (b : β) : ‖to
Lp p (Function.const ι b)‖ = (Fintype.card ι : Real>=0) ^ (1 / p).toReal * ‖b‖
参数：hp : p != ∞；b : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用引理 `PiLp.nnnorm_toLp_const`：nnnorm_toLp_const {β} [SeminormedAddCommGroup β]
 (hp : p != ∞) (b : β) : ‖toLp p (Function.const ι b)‖₊ = (Fintype.card ι : Real
>=0) ^ (1 / …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `ENNReal.toReal_inv`：∀ (a : ENNReal), a⁻¹.toReal = a.toReal⁻¹
· 使用定理 `NNReal.coe_natCast`：∀ (n : ℕ), ↑↑n = ↑n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
When `p = ∞`, this lemma does not hold without the additional assumption `Nonemp
ty ι` because
the left-hand side simplifies to `0`, while the right-hand side simplifies to `‖
b‖₊`. See
`PiLp.norm_toLp_const'` for a version which exchanges the hypothesis `p ≠ ∞` for
`Nonempty ι`.
-/
lemma norm_toLp_const {β} [SeminormedAddCommGroup β] (hp : p ≠ ∞) (b : β) :
    ‖toLp p (Function.const ι b)‖ =
      (Fintype.card ι : ℝ≥0) ^ (1 / p).toReal * ‖b‖ :=
  (congr_arg ((↑) : ℝ≥0 → ℝ) <| nnnorm_toLp_const hp b).trans <| by simp

/-- When `IsEmpty ι`, this lemma does not hold without the additional assumption `p ≠ ∞` because
the left-hand side simplifies to `0`, while the right-hand side simplifies to `‖b‖₊`. See
`PiLp.norm_equiv_symm_const` for a version which exchanges the hypothesis `Nonempty ι`.
for `p ≠ ∞`. -/
/-
**PiLp.norm_toLp_const'** 是 Mathlib 中的一个引理，位于命名空间 `PiLp`。
形式化陈述：norm_toLp_const' {β} [SeminormedAddCommGroup β] [Nonempty ι] (b : β) : ‖to
Lp p (Function.const ι b)‖ = (Fintype.card ι : Real>=0) ^ (1 / p).toReal * ‖b‖
参数：b : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用引理 `PiLp.nnnorm_toLp_const'`：nnnorm_toLp_const' {β} [SeminormedAddCommGroup 
β] [Nonempty ι] (b : β) : ‖toLp p (Function.const ι b)‖₊ = (Fintype.card ι : Rea
l>=0) ^ (1 / …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `ENNReal.toReal_inv`：∀ (a : ENNReal), a⁻¹.toReal = a.toReal⁻¹
· 使用定理 `NNReal.coe_natCast`：∀ (n : ℕ), ↑↑n = ↑n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
When `IsEmpty ι`, this lemma does not hold without the additional assumption `p 
≠ ∞` because
the left-hand side simplifies to `0`, while the right-hand side simplifies to `‖
b‖₊`. See
`PiLp.norm_equiv_symm_const` for a version which exchanges the hypothesis `Nonem
pty ι`.
for `p ≠ ∞`.
-/
lemma norm_toLp_const' {β} [SeminormedAddCommGroup β] [Nonempty ι] (b : β) :
    ‖toLp p (Function.const ι b)‖ =
      (Fintype.card ι : ℝ≥0) ^ (1 / p).toReal * ‖b‖ :=
  (congr_arg ((↑) : ℝ≥0 → ℝ) <| nnnorm_toLp_const' b).trans <| by simp
/-
**PiLp.nnnorm_toLp_one** 是 Mathlib 中的一个引理，位于命名空间 `PiLp`。
形式化陈述：nnnorm_toLp_one {β} [SeminormedAddCommGroup β] (hp : p != ∞) [One β] : ‖to
Lp p (1 : ι -> β)‖₊ = (Fintype.card ι : Real>=0) ^ (1 / p).toReal * ‖(1 : β)‖₊
参数：hp : p != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `PiLp.nnnorm_toLp_const`：nnnorm_toLp_const {β} [SeminormedAddCommGroup β]
 (hp : p != ∞) (b : β) : ‖toLp p (Function.const ι b)‖₊ = (Fintype.card ι : Real
>=0) ^ (1 / …
-/
lemma nnnorm_toLp_one {β} [SeminormedAddCommGroup β] (hp : p ≠ ∞) [One β] :
    ‖toLp p (1 : ι → β)‖₊ = (Fintype.card ι : ℝ≥0) ^ (1 / p).toReal * ‖(1 : β)‖₊ :=
  (nnnorm_toLp_const hp (1 : β)).trans rfl
/-
**PiLp.norm_toLp_one** 是 Mathlib 中的一个引理，位于命名空间 `PiLp`。
形式化陈述：norm_toLp_one {β} [SeminormedAddCommGroup β] (hp : p != ∞) [One β] : ‖toLp
 p (1 : ι -> β)‖ = (Fintype.card ι : Real>=0) ^ (1 / p).toReal * ‖(1 : β)‖
参数：hp : p != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `PiLp.norm_toLp_const`：norm_toLp_const {β} [SeminormedAddCommGroup β] (hp
 : p != ∞) (b : β) : ‖toLp p (Function.const ι b)‖ = (Fintype.card ι : Real>=0) 
^ (1 / p).…
-/
lemma norm_toLp_one {β} [SeminormedAddCommGroup β] (hp : p ≠ ∞) [One β] :
    ‖toLp p (1 : ι → β)‖ = (Fintype.card ι : ℝ≥0) ^ (1 / p).toReal * ‖(1 : β)‖ :=
  (norm_toLp_const hp (1 : β)).trans rfl

end Fintype

section

variable [Semiring 𝕜] [∀ i, AddCommGroup (β i)] [∀ i, Module 𝕜 (β i)] [∀ i, TopologicalSpace (β i)]

/-- `WithLp.linearEquiv` as a continuous linear equivalence. -/
@[simps! apply symm_apply]
/-
**PiLp.continuousLinearEquiv** 是 Mathlib 中的一个定义，位于命名空间 `PiLp`。
形式化陈述：continuousLinearEquiv : PiLp p β ≃L[𝕜] forall i, β i where toLinearEquiv
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`WithLp.linearEquiv` as a continuous linear equivalence.
-/
def continuousLinearEquiv : PiLp p β ≃L[𝕜] ∀ i, β i where
  toLinearEquiv := WithLp.linearEquiv _ _ _
  continuous_invFun := (by fun_prop : Continuous fun (a : Π i, β i) ↦ toLp p a)
/-
**PiLp.coe_continuousLinearEquiv** 是 Mathlib 中的一个引理，位于命名空间 `PiLp`。
形式化陈述：coe_continuousLinearEquiv : ⇑(PiLp.continuousLinearEquiv p 𝕜 β) = ofLp
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_continuousLinearEquiv :
    ⇑(PiLp.continuousLinearEquiv p 𝕜 β) = ofLp := rfl
/-
**PiLp.coe_symm_continuousLinearEquiv** 是 Mathlib 中的一个引理，位于命名空间 `PiLp`。
形式化陈述：coe_symm_continuousLinearEquiv : ⇑(PiLp.continuousLinearEquiv p 𝕜 β).symm 
= toLp p
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_symm_continuousLinearEquiv :
    ⇑(PiLp.continuousLinearEquiv p 𝕜 β).symm = toLp p := rfl

/-- The natural equivalence between `PiLp p β` and `β default`,
for any index type `ι` with a unique element. -/
@[simps! apply symm_apply]
/-
**PiLp.equivOfUnique** 是 Mathlib 中的一个定义，位于命名空间 `PiLp`。
形式化陈述：equivOfUnique [Unique ι] : PiLp p β ≃L[𝕜] β default
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural equivalence between `PiLp p β` and `β default`,
for any index type `ι` with a unique element.
-/
def equivOfUnique [Unique ι] : PiLp p β ≃L[𝕜] β default :=
  (continuousLinearEquiv p 𝕜 β).trans <| .piUnique 𝕜 β

end

section

variable [Semiring 𝕜] [∀ i, NormedAddCommGroup (β i)] [∀ i, Module 𝕜 (β i)]

variable {𝕜} in
/-- The projection on the `i`-th coordinate of `PiLp p β`, as a continuous linear map. -/
@[simps!]
/-
**PiLp.proj** 是 Mathlib 中的一个定义，位于命名空间 `PiLp`。
形式化陈述：proj (i : ι) : PiLp p β ->L[𝕜] β i where __
参数：i : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The projection on the `i`-th coordinate of `PiLp p β`, as a continuous linear ma
p.
-/
def proj (i : ι) : PiLp p β →L[𝕜] β i where
  __ := projₗ p β i
  cont := (by fun_prop : Continuous fun a : PiLp p β ↦ a.ofLp i)

end

section Basis

variable [Finite ι] [Ring 𝕜]
variable (ι)

/-- A version of `Pi.basisFun` for `PiLp`. -/
/-
**PiLp.basisFun** 是 Mathlib 中的一个定义，位于命名空间 `PiLp`。
形式化陈述：basisFun : Basis ι 𝕜 (PiLp p fun _ : ι => 𝕜)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A version of `Pi.basisFun` for `PiLp`.
-/
def basisFun : Basis ι 𝕜 (PiLp p fun _ : ι => 𝕜) :=
  Basis.ofEquivFun (WithLp.linearEquiv p 𝕜 (ι → 𝕜))

@[simp]
/-
**PiLp.basisFun_apply** 是 Mathlib 中的一个定理，位于命名空间 `PiLp`。
形式化陈述：basisFun_apply [DecidableEq ι] (i) : basisFun p 𝕜 ι i = single p i 1
参数：i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Module.Basis.coe_ofEquivFun`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u
_6} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M
] [inst_3 : Finit…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem basisFun_apply [DecidableEq ι] (i) :
    basisFun p 𝕜 ι i = single p i 1 := by
  simp_rw [basisFun, Basis.coe_ofEquivFun, WithLp.coe_symm_linearEquiv, toLp_single]

@[simp]
/-
**PiLp.basisFun_repr** 是 Mathlib 中的一个定理，位于命名空间 `PiLp`。
形式化陈述：basisFun_repr (x : PiLp p fun _ : ι => 𝕜) (i : ι) : (basisFun p 𝕜 ι).repr 
x i = x i
参数：x : PiLp p fun _ : ι => 𝕜；i : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem basisFun_repr (x : PiLp p fun _ : ι => 𝕜) (i : ι) : (basisFun p 𝕜 ι).repr x i = x i :=
  rfl

@[simp]
/-
**PiLp.basisFun_equivFun** 是 Mathlib 中的一个定理，位于命名空间 `PiLp`。
形式化陈述：basisFun_equivFun : (basisFun p 𝕜 ι).equivFun = WithLp.linearEquiv p 𝕜 (ι 
-> 𝕜)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.equivFun_ofEquivFun`：∀ {ι : Type u_1} {R : Type u_3} {M : T
ype u_6} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Modul
e R M] [inst_3 : Finit…
-/
theorem basisFun_equivFun : (basisFun p 𝕜 ι).equivFun = WithLp.linearEquiv p 𝕜 (ι → 𝕜) :=
  Basis.equivFun_ofEquivFun _
/-
**PiLp.basisFun_eq_pi_basisFun** 是 Mathlib 中的一个定理，位于命名空间 `PiLp`。
形式化陈述：basisFun_eq_pi_basisFun : basisFun p 𝕜 ι = (Pi.basisFun 𝕜 ι).map (WithLp.l
inearEquiv p 𝕜 (ι -> 𝕜)).symm
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem basisFun_eq_pi_basisFun :
    basisFun p 𝕜 ι = (Pi.basisFun 𝕜 ι).map (WithLp.linearEquiv p 𝕜 (ι → 𝕜)).symm :=
  rfl

@[simp]
/-
**PiLp.basisFun_map** 是 Mathlib 中的一个定理，位于命名空间 `PiLp`。
形式化陈述：basisFun_map : (basisFun p 𝕜 ι).map (WithLp.linearEquiv p 𝕜 (ι -> 𝕜)) = Pi
.basisFun 𝕜 ι
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem basisFun_map :
    (basisFun p 𝕜 ι).map (WithLp.linearEquiv p 𝕜 (ι → 𝕜)) = Pi.basisFun 𝕜 ι := rfl

end Basis

open Matrix

nonrec theorem basis_toMatrix_basisFun_mul [Fintype ι]
    {𝕜} [SeminormedCommRing 𝕜] (b : Basis ι 𝕜 (PiLp p fun _ : ι => 𝕜))
    (A : Matrix ι ι 𝕜) :
    b.toMatrix (PiLp.basisFun _ _ _) * A =
      Matrix.of fun i j => b.repr (toLp p (Aᵀ j)) i := by
  have := basis_toMatrix_basisFun_mul (b.map (WithLp.linearEquiv _ 𝕜 _)) A
  simp_rw [← PiLp.basisFun_map p, Basis.map_repr, LinearEquiv.trans_apply,
    WithLp.linearEquiv_symm_apply, Basis.toMatrix_map, Function.comp_def, Basis.map_apply,
    LinearEquiv.symm_apply_apply] at this
  exact this

section toPi

/-!
### `L^p` distance on a product space

In this section we define a pseudometric space structure on `Π i, α i`, as well as a seminormed
group structure. These are meant to be used to put the desired instances on type synonyms
of `Π i, α i`. See for instance `Matrix.frobeniusSeminormedAddCommGroup`.
-/

-- This prevents Lean from elaborating terms of `Π i, α i` with an unintended norm.
attribute [-instance] Pi.seminormedAddGroup

variable [Fact (1 ≤ p)] [Fintype ι]

/-- This definition allows to endow `Π i, α i` with the Lp distance with the uniformity and
bornology being defeq to the product ones. It is useful to endow a type synonym of `Π i, α i` with
the Lp distance. -/
/-
**PiLp.pseudoMetricSpaceToPi** 是 Mathlib 中的一个缩写定义，位于命名空间 `PiLp`。
形式化陈述：pseudoMetricSpaceToPi [forall i, PseudoMetricSpace (α i)] : PseudoMetricSp
ace (Π i, α i)
参数：α i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This definition allows to endow `Π i, α i` with the Lp distance with the uniform
ity and
bornology being defeq to the product ones. It is useful to endow a type synonym 
of `Π i, α i` with
the Lp distance.
-/
abbrev pseudoMetricSpaceToPi [∀ i, PseudoMetricSpace (α i)] :
    PseudoMetricSpace (Π i, α i) :=
  (isUniformInducing_toLp p α).comapPseudoMetricSpace.replaceBornology
    fun s => Filter.ext_iff.1
      (le_antisymm (antilipschitzWith_toLp p α).tendsto_cobounded.le_comap
        (lipschitzWith_toLp p α).comap_cobounded_le) sᶜ
/-
**PiLp.dist_pseudoMetricSpaceToPi** 是 Mathlib 中的一个引理，位于命名空间 `PiLp`。
形式化陈述：dist_pseudoMetricSpaceToPi [forall i, PseudoMetricSpace (α i)] (x y : Π i,
 α i) : @dist _ (pseudoMetricSpaceToPi p α).toDist x y = dist (toLp p x) (toLp p
 y)
参数：α i；x y : Π i, α i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma dist_pseudoMetricSpaceToPi [∀ i, PseudoMetricSpace (α i)] (x y : Π i, α i) :
    @dist _ (pseudoMetricSpaceToPi p α).toDist x y = dist (toLp p x) (toLp p y) := rfl

/-- This definition allows to endow `Π i, α i` with the Lp norm with the uniformity and bornology
being defeq to the product ones. It is useful to endow a type synonym of `Π i, α i` with the
Lp norm. -/
/-
**PiLp.seminormedAddCommGroupToPi** 是 Mathlib 中的一个缩写定义，位于命名空间 `PiLp`。
形式化陈述：seminormedAddCommGroupToPi [forall i, SeminormedAddCommGroup (α i)] : Semi
normedAddCommGroup (Π i, α i) where norm x
参数：α i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This definition allows to endow `Π i, α i` with the Lp norm with the uniformity 
and bornology
being defeq to the product ones. It is useful to endow a type synonym of `Π i, α
 i` with the
Lp norm.
-/
abbrev seminormedAddCommGroupToPi [∀ i, SeminormedAddCommGroup (α i)] :
    SeminormedAddCommGroup (Π i, α i) where
  norm x := ‖toLp p x‖
  toPseudoMetricSpace := pseudoMetricSpaceToPi p α
  dist_eq x y := by
    rw [dist_pseudoMetricSpaceToPi, SeminormedAddCommGroup.dist_eq, toLp_add, toLp_neg]
/-
**PiLp.norm_seminormedAddCommGroupToPi** 是 Mathlib 中的一个引理，位于命名空间 `PiLp`。
形式化陈述：norm_seminormedAddCommGroupToPi [forall i, SeminormedAddCommGroup (α i)] (
x : Π i, α i) : @Norm.norm _ (seminormedAddCommGroupToPi p α).toNorm x = ‖toLp p
 x‖
参数：α i；x : Π i, α i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma norm_seminormedAddCommGroupToPi [∀ i, SeminormedAddCommGroup (α i)] (x : Π i, α i) :
    @Norm.norm _ (seminormedAddCommGroupToPi p α).toNorm x = ‖toLp p x‖ := rfl
/-
**PiLp.nnnorm_seminormedAddCommGroupToPi** 是 Mathlib 中的一个引理，位于命名空间 `PiLp`。
形式化陈述：nnnorm_seminormedAddCommGroupToPi [forall i, SeminormedAddCommGroup (α i)]
 (x : Π i, α i) : @NNNorm.nnnorm _ (seminormedAddCommGroupToPi p α).toSeminormed
AddGroup.toNNNorm x = ‖toLp p x‖₊
参数：α i；x : Π i, α i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma nnnorm_seminormedAddCommGroupToPi [∀ i, SeminormedAddCommGroup (α i)] (x : Π i, α i) :
    @NNNorm.nnnorm _ (seminormedAddCommGroupToPi p α).toSeminormedAddGroup.toNNNorm x =
    ‖toLp p x‖₊ := rfl
/-
**PiLp.isBoundedSMulSeminormedAddCommGroupToPi** 是 Mathlib 中的一个引理，位于命名空间 `PiLp`。
形式化陈述：isBoundedSMulSeminormedAddCommGroupToPi [forall i, SeminormedAddCommGroup 
(α i)] {R : Type*} [SeminormedRing R] [forall i, Module R (α i)] [forall i, IsBo
undedSMul R (α i)] : letI
参数：α i；α i；α i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E),
 dist a 0 = ‖a‖
· 使用定理 `dist_smul_pair`：dist_smul_pair (x : α) (y₁ y₂ : β) : dist (x • y₁) (x • 
y₂) <= dist x 0 * dist y₁ y₂
· 使用定理 `dist_pair_smul`：dist_pair_smul (x₁ x₂ : α) (y : β) : dist (x₁ • y) (x₂ •
 y) <= dist x₁ x₂ * dist y 0
-/
lemma isBoundedSMulSeminormedAddCommGroupToPi
    [∀ i, SeminormedAddCommGroup (α i)] {R : Type*} [SeminormedRing R]
    [∀ i, Module R (α i)] [∀ i, IsBoundedSMul R (α i)] :
    letI := pseudoMetricSpaceToPi p α
    IsBoundedSMul R (Π i, α i) := by
  let := pseudoMetricSpaceToPi p α
  refine ⟨fun x y z ↦ ?_, fun x y z ↦ ?_⟩
  · simpa [dist_pseudoMetricSpaceToPi] using dist_smul_pair x (toLp p y) (toLp p z)
  · simpa [dist_pseudoMetricSpaceToPi] using dist_pair_smul x y (toLp p z)
/-
**PiLp.normSMulClassSeminormedAddCommGroupToPi** 是 Mathlib 中的一个引理，位于命名空间 `PiLp`。
形式化陈述：normSMulClassSeminormedAddCommGroupToPi [forall i, SeminormedAddCommGroup 
(α i)] {R : Type*} [SeminormedRing R] [forall i, Module R (α i)] [forall i, Norm
SMulClass R (α i)] : letI
参数：α i；α i；α i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma normSMulClassSeminormedAddCommGroupToPi
    [∀ i, SeminormedAddCommGroup (α i)] {R : Type*} [SeminormedRing R]
    [∀ i, Module R (α i)] [∀ i, NormSMulClass R (α i)] :
    letI := seminormedAddCommGroupToPi p α
    NormSMulClass R (Π i, α i) := by
  let := seminormedAddCommGroupToPi p α
  refine ⟨fun x y ↦ ?_⟩
  simp [norm_seminormedAddCommGroupToPi, norm_smul]

/-- This definition allows to endow `Π i, α i` with a normed space structure corresponding to
the Lp norm. It is useful for type synonyms of `Π i, α i`. -/
/-
**PiLp.normedSpaceSeminormedAddCommGroupToPi** 是 Mathlib 中的一个缩写定义，位于命名空间 `PiLp`。
形式化陈述：normedSpaceSeminormedAddCommGroupToPi [forall i, SeminormedAddCommGroup (α
 i)] {R : Type*} [NormedField R] [forall i, NormedSpace R (α i)] : letI
参数：α i；α i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This definition allows to endow `Π i, α i` with a normed space structure corresp
onding to
the Lp norm. It is useful for type synonyms of `Π i, α i`.
-/
abbrev normedSpaceSeminormedAddCommGroupToPi
    [∀ i, SeminormedAddCommGroup (α i)] {R : Type*} [NormedField R]
    [∀ i, NormedSpace R (α i)] :
    letI := seminormedAddCommGroupToPi p α
    NormedSpace R (Π i, α i) := by
  letI := seminormedAddCommGroupToPi p α
  refine ⟨fun x y ↦ ?_⟩
  simp [norm_seminormedAddCommGroupToPi, norm_smul]

/-- This definition allows to endow `Π i, α i` with the Lp norm with the uniformity and bornology
being defeq to the product ones. It is useful to endow a type synonym of `Π i, α i` with the
Lp norm. -/
/-
**PiLp.normedAddCommGroupToPi** 是 Mathlib 中的一个缩写定义，位于命名空间 `PiLp`。
形式化陈述：normedAddCommGroupToPi [forall i, NormedAddCommGroup (α i)] : NormedAddCom
mGroup (Π i, α i) where norm x
参数：α i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This definition allows to endow `Π i, α i` with the Lp norm with the uniformity 
and bornology
being defeq to the product ones. It is useful to endow a type synonym of `Π i, α
 i` with the
Lp norm.
-/
abbrev normedAddCommGroupToPi [∀ i, NormedAddCommGroup (α i)] :
    NormedAddCommGroup (Π i, α i) where
  norm x := ‖toLp p x‖
  toPseudoMetricSpace := pseudoMetricSpaceToPi p α
  dist_eq x y := by
    rw [dist_pseudoMetricSpaceToPi, SeminormedAddCommGroup.dist_eq, toLp_add, toLp_neg]
  eq_of_dist_eq_zero {x y} h := by
    rw [dist_pseudoMetricSpaceToPi] at h
    apply eq_of_dist_eq_zero at h
    exact WithLp.toLp_injective p h

end toPi

end PiLp

