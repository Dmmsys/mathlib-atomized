/-
Copyright (c) 2026 Fengyang Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fengyang Wang
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Constructions
public import Mathlib.Topology.Algebra.InfiniteSum.Module
public import Mathlib.Algebra.Module.LinearMap.Basic
public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Data.Set.MulAntidiagonal

/-!
# Discrete Convolution

Discrete convolution over monoids: `(f ⋆[L] g) x = ∑' (a, b) : mulFiber x, L (f a) (g b)`
where `mulFiber x = {(a, b) | a * b = x}`. Additive monoids are also supported.

## Design

Uses a bilinear map `L : E →ₗ[S] E' →ₗ[S] F` to combine values, following
`MeasureTheory.convolution`.

The index monoid `M` can be non-commutative (group algebras R[G] with non-abelian G).

`@[to_additive]` generates multiplicative and additive versions from a single definition.
The `mul/add` distinction refers to the index monoid `M`: multiplicative sums over
`mulFiber x = {(a,b) | a * b = x}`, additive sums over `addFiber x = {(a,b) | a + b = x}`.

## Main Definitions

* `mulFiber x`: the fiber of multiplication at `x`, all pairs `(a, b)` with `a * b = x`.
* `convolution L f g`: the discrete convolution
  `(f ⋆[L] g) x = ∑' ab : mulFiber x, L (f ab.1) (g ab.2)`.
* `ConvolutionExistsAt L f g x`: the convolution sum is summable at `x`.
* `ConvolutionExists L f g`: the convolution sum is summable at every point.

## Main Results

* `convolution_indicator_one_left`, `convolution_indicator_one_right`: identity element
  (`Set.indicator {1} (fun _ => e)` where `L e` is the identity map)
* `ConvolutionExists.distrib_add`, `ConvolutionExists.add_distrib`: distributivity over addition
* `ConvolutionExistsAt.smul_convolution`, `ConvolutionExistsAt.convolution_smul`:
  scalar multiplication
* `convolution_comm`: commutativity for symmetric bilinear maps over commutative monoids

## Notation

| Notation     | Operation                                       |
|--------------|-------------------------------------------------|
| `f ⋆[L] g`   | `∑' ab : mulFiber x, L (f ab.1.1) (g ab.1.2)`   |
| `f ⋆₊[L] g`  | `∑' ab : addFiber x, L (f ab.1.1) (g ab.1.2)`   |

Precedence design: `f:68` and `g:67` gives right associativity (`f ⋆ g ⋆ h` parses as
`f ⋆ (g ⋆ h)`), matching function composition `∘` and `MeasureTheory.convolution`.
-/

@[expose] public section

open scoped BigOperators

noncomputable section

namespace DiscreteConvolution

variable {M S E E' E'' F F' G R : Type*}

/-! ### Multiplication Fiber -/

section Fiber

variable [Monoid M]

/-- The fiber of multiplication at `x`: all pairs `(a, b)` with `a * b = x`. -/
@[to_additive /-- The fiber of addition at `x`: all pairs `(a, b)` with `a + b = x`. -/]
/-
**DiscreteConvolution.mulFiber** 是 Mathlib 中的一个定义，位于命名空间 `DiscreteConvolution`。
形式化陈述：mulFiber (x : M) : Set (M × M)
参数：x : M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The fiber of multiplication at `x`: all pairs `(a, b)` with `a * b = x`.
-/
def mulFiber (x : M) : Set (M × M) := Set.mulAntidiagonal Set.univ Set.univ x

@[to_additive (attr := grind =)]
/-
**DiscreteConvolution.mem_mulFiber** 是 Mathlib 中的一个引理，位于命名空间 `DiscreteConvolutio
n`。
形式化陈述：mem_mulFiber {x : M} {ab : M × M} : ab in mulFiber x ↔ ab.1 * ab.2 = x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mem_mulFiber {x : M} {ab : M × M} : ab ∈ mulFiber x ↔ ab.1 * ab.2 = x := by simp [mulFiber]

@[to_additive]
/-
**DiscreteConvolution.mulFiber_one_mem** 是 Mathlib 中的一个引理，位于命名空间 `DiscreteConvol
ution`。
形式化陈述：mulFiber_one_mem : (1, 1) in mulFiber (1 : M)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
lemma mulFiber_one_mem : (1, 1) ∈ mulFiber (1 : M) := by simp [mulFiber]

end Fiber

/-! ### Convolution Definition and Existence -/

section Definition

variable [Monoid M] [CommSemiring S] [AddCommMonoid E] [AddCommMonoid E'] [AddCommMonoid F]
variable [Module S E] [Module S E'] [Module S F]
variable [TopologicalSpace F]

/-- The discrete convolution of `f` and `g` using bilinear map `L`:
`(f ⋆[L] g) x = ∑' (a, b) : mulFiber x, L (f a) (g b)`. -/
@[to_additive (dont_translate := S E E' F) addConvolution
  /-- Additive convolution: `(f ⋆₊[L] g) x = ∑' ab : addFiber x, L (f ab.1) (g ab.2)`. -/]
/-
**DiscreteConvolution.convolution** 是 Mathlib 中的一个定义，位于命名空间 `DiscreteConvolution
`。
形式化陈述：convolution (L : E ->ₗ[S] E' ->ₗ[S] F) (f : M -> E) (g : M -> E') : M -> F
参数：L : E ->ₗ[S] E' ->ₗ[S] F；f : M -> E；g : M -> E'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def convolution (L : E →ₗ[S] E' →ₗ[S] F) (f : M → E) (g : M → E') : M → F :=
  fun x => ∑' ab : mulFiber x, L (f ab.1.1) (g ab.1.2)

/-- Notation for discrete convolution with explicit bilinear map:
`(f ⋆[L] g) x = ∑' ab : mulFiber x, L (f ab.1) (g ab.2)`. -/
scoped notation:67 f:68 " ⋆[" L "] " g:67 => convolution L f g

/-- Notation for additive convolution with explicit bilinear map:
`(f ⋆₊[L] g) x = ∑' ab : addFiber x, L (f ab.1) (g ab.2)`. -/
scoped notation:67 f:68 " ⋆₊[" L "] " g:67 => addConvolution L f g

end Definition

section BasicProperties

variable [Monoid M] [CommSemiring S] [AddCommMonoid E] [AddCommMonoid E'] [AddCommMonoid F]
variable [Module S E] [Module S E'] [Module S F]
variable [TopologicalSpace F]

@[to_additive (dont_translate := S E E' F) (attr := simp) zero_addConvolution]
/-
**DiscreteConvolution.zero_convolution** 是 Mathlib 中的一个引理，位于命名空间 `DiscreteConvol
ution`。
形式化陈述：zero_convolution (L : E ->ₗ[S] E' ->ₗ[S] F) (f : M -> E') : (0 : M -> E) ⋆
[L] f = 0
参数：L : E ->ₗ[S] E' ->ₗ[S] F；f : M -> E'。
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
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `tsum_zero`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [ins
t_1 : TopologicalSpace α] {L : SummationFilter β},   ∑'[L] (x : β), 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma zero_convolution (L : E →ₗ[S] E' →ₗ[S] F) (f : M → E') :
    (0 : M → E) ⋆[L] f = 0 := by
  ext; simp [convolution]

@[to_additive (dont_translate := S E E' F) (attr := simp) addConvolution_zero]
/-
**DiscreteConvolution.convolution_zero** 是 Mathlib 中的一个引理，位于命名空间 `DiscreteConvol
ution`。
形式化陈述：convolution_zero (L : E ->ₗ[S] E' ->ₗ[S] F) (f : M -> E) : f ⋆[L] (0 : M -
> E') = 0
参数：L : E ->ₗ[S] E' ->ₗ[S] F；f : M -> E。
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
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `tsum_zero`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [ins
t_1 : TopologicalSpace α] {L : SummationFilter β},   ∑'[L] (x : β), 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma convolution_zero (L : E →ₗ[S] E' →ₗ[S] F) (f : M → E) :
    f ⋆[L] (0 : M → E') = 0 := by
  ext; simp [convolution]

@[to_additive (dont_translate := S E F) (attr := simp) addConvolution_indicator_zero_left]
/-
**DiscreteConvolution.convolution_indicator_one_left** 是 Mathlib 中的一个引理，位于命名空间 `
DiscreteConvolution`。
形式化陈述：convolution_indicator_one_left (L : E ->ₗ[S] F ->ₗ[S] F) (e : E) (f : M ->
 F) (hL : forall y, L e y = y) : Set.indicator {1} (fun _ => e) ⋆[L] f = f
参数：L : E ->ₗ[S] F ->ₗ[S] F；e : E；f : M -> F；hL : forall y, L e y = y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.indicator_apply`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] (s 
: Set α) (f : α → M) (a : α) [inst_1 : Decidable (a ∈ s)],   s.indicator f a = i
f a ∈ s t…
· 使用定理 `tsum_eq_single`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {L : SummationFilter β}   [L.LeAtTop] {f : β → α}
 (b …
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma convolution_indicator_one_left (L : E →ₗ[S] F →ₗ[S] F) (e : E) (f : M → F)
    (hL : ∀ y, L e y = y) :
    Set.indicator {1} (fun _ => e) ⋆[L] f = f := by
  classical
  ext x; simp only [convolution, Set.indicator_apply]
  rw [tsum_eq_single (⟨(1, x), by grind⟩ : mulFiber x) (by grind [LinearMap.zero_apply])]
  simp [hL]

@[to_additive (dont_translate := S E F) (attr := simp) addConvolution_indicator_zero_right]
/-
**DiscreteConvolution.convolution_indicator_one_right** 是 Mathlib 中的一个引理，位于命名空间 
`DiscreteConvolution`。
形式化陈述：convolution_indicator_one_right (L : F ->ₗ[S] E ->ₗ[S] F) (f : M -> F) (e 
: E) (hL : forall y, L y e = y) : f ⋆[L] Set.indicator {1} (fun _ => e) = f
参数：L : F ->ₗ[S] E ->ₗ[S] F；f : M -> F；e : E；hL : forall y, L y e = y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.indicator_apply`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] (s 
: Set α) (f : α → M) (a : α) [inst_1 : Decidable (a ∈ s)],   s.indicator f a = i
f a ∈ s t…
· 使用定理 `tsum_eq_single`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {L : SummationFilter β}   [L.LeAtTop] {f : β → α}
 (b …
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma convolution_indicator_one_right (L : F →ₗ[S] E →ₗ[S] F) (f : M → F) (e : E)
    (hL : ∀ y, L y e = y) :
    f ⋆[L] Set.indicator {1} (fun _ => e) = f := by
  classical
  ext x; simp only [convolution, Set.indicator_apply]
  rw [tsum_eq_single (⟨(x, 1), by grind⟩ : mulFiber x) (by grind [LinearMap.zero_apply])]
  simp [hL]

end BasicProperties

section ExistenceProperties

variable [Monoid M] [CommSemiring S] [AddCommMonoid E] [AddCommMonoid E'] [AddCommMonoid F]
variable [Module S E] [Module S E'] [Module S F]
variable [TopologicalSpace F]

/-- The convolution of `f` and `g` with bilinear map `L` exists at `x` when the sum over
the fiber is summable. -/
@[to_additive (dont_translate := S E E' F) AddConvolutionExistsAt
  /-- Additive convolution exists at `x` when the fiber sum is summable. -/]
/-
**DiscreteConvolution.ConvolutionExistsAt** 是 Mathlib 中的一个定义，位于命名空间 `DiscreteCon
volution`。
形式化陈述：ConvolutionExistsAt (L : E ->ₗ[S] E' ->ₗ[S] F) (f : M -> E) (g : M -> E') 
(x : M) : Prop
参数：L : E ->ₗ[S] E' ->ₗ[S] F；f : M -> E；g : M -> E'；x : M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def ConvolutionExistsAt (L : E →ₗ[S] E' →ₗ[S] F) (f : M → E) (g : M → E') (x : M) : Prop :=
  Summable fun ab : mulFiber x => L (f ab.1.1) (g ab.1.2)

/-- The convolution of `f` and `g` with bilinear map `L` exists when it exists at every point. -/
@[to_additive (dont_translate := S E E' F) AddConvolutionExists
  /-- Additive convolution exists when it exists at every point. -/]
/-
**DiscreteConvolution.ConvolutionExists** 是 Mathlib 中的一个定义，位于命名空间 `DiscreteConvo
lution`。
形式化陈述：ConvolutionExists (L : E ->ₗ[S] E' ->ₗ[S] F) (f : M -> E) (g : M -> E') : 
Prop
参数：L : E ->ₗ[S] E' ->ₗ[S] F；f : M -> E；g : M -> E'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def ConvolutionExists (L : E →ₗ[S] E' →ₗ[S] F) (f : M → E) (g : M → E') : Prop :=
  ∀ x, ConvolutionExistsAt L f g x

variable [T2Space F] [ContinuousAdd F]

@[to_additive (dont_translate := S E E' F)]
/-
**DiscreteConvolution.ConvolutionExistsAt.distrib_add** 是 Mathlib 中的一个定理，位于命名空间 
`DiscreteConvolution.ConvolutionExistsAt`。
形式化陈述：∀ {M : Type u_1} {S : Type u_2} {E : Type u_3} {E' : Type u_4} {F : Type u
_6} [inst : Monoid M]   [inst_1 : CommSemiring S] [inst_2 : AddCommMonoid E] [in
st_3 : AddCommMonoid E'] [inst_4 : AddCommMonoid F]   [inst_5 : _root_.Module S 
E] [inst_6 : _root_.Module S E'] [inst_7 : _root_.Module S F] [inst_8 : Topologi
calSpace F]   [T2Space F] [ContinuousAdd F] {f : M → E} {g g' : M → E'} {x : M} 
(L : E →ₗ[S] E' →ₗ[S] F),   DiscreteConvolution.ConvolutionExistsAt L f g x →   
  DiscreteConvolution.ConvolutionExistsAt L f g' x →       DiscreteConvolution.c
onvolution L f (g + g') x =         DiscreteConvolution.convolution L f g x + Di
screteConvolution.convolution L f g' x
参数：L : E →ₗ[S] E' →ₗ[S] F；g + g'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `Summable.tsum_add`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid
 α] [inst_1 : TopologicalSpace α] {f g : β → α}   {L : SummationFilter β} [T2Spa
ce α] […
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
-/
lemma ConvolutionExistsAt.distrib_add {f : M → E} {g g' : M → E'} {x : M}
    (L : E →ₗ[S] E' →ₗ[S] F) (hfg : ConvolutionExistsAt L f g x)
    (hfg' : ConvolutionExistsAt L f g' x) :
    (f ⋆[L] (g + g')) x = (f ⋆[L] g) x + (f ⋆[L] g') x := by
  simpa [convolution] using hfg.tsum_add hfg'

@[to_additive (dont_translate := S E E' F)]
/-
**DiscreteConvolution.ConvolutionExists.distrib_add** 是 Mathlib 中的一个定理，位于命名空间 `D
iscreteConvolution.ConvolutionExists`。
形式化陈述：∀ {M : Type u_1} {S : Type u_2} {E : Type u_3} {E' : Type u_4} {F : Type u
_6} [inst : Monoid M]   [inst_1 : CommSemiring S] [inst_2 : AddCommMonoid E] [in
st_3 : AddCommMonoid E'] [inst_4 : AddCommMonoid F]   [inst_5 : _root_.Module S 
E] [inst_6 : _root_.Module S E'] [inst_7 : _root_.Module S F] [inst_8 : Topologi
calSpace F]   [T2Space F] [ContinuousAdd F] {f : M → E} {g g' : M → E'} (L : E →
ₗ[S] E' →ₗ[S] F),   DiscreteConvolution.ConvolutionExists L f g →     DiscreteCo
nvolution.ConvolutionExists L f g' →       DiscreteConvolution.convolution L f (
g + g') =         DiscreteConvolution.convolution L f g + DiscreteConvolution.co
nvolution L f g'
参数：L : E →ₗ[S] E' →ₗ[S] F；g + g'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `DiscreteConvolution.ConvolutionExistsAt.distrib_add`：∀ {M : Type u_1} {S
 : Type u_2} {E : Type u_3} {E' : Type u_4} {F : Type u_6} [inst : Monoid M]   [
inst_1 : CommSemiring S] [inst_2 : AddCom…
-/
lemma ConvolutionExists.distrib_add {f : M → E} {g g' : M → E'} (L : E →ₗ[S] E' →ₗ[S] F)
    (hfg : ConvolutionExists L f g) (hfg' : ConvolutionExists L f g') :
    f ⋆[L] (g + g') = f ⋆[L] g + f ⋆[L] g' := by
  ext x; exact (hfg x).distrib_add L (hfg' x)

@[to_additive (dont_translate := S E E' F)]
/-
**DiscreteConvolution.ConvolutionExistsAt.add_distrib** 是 Mathlib 中的一个定理，位于命名空间 
`DiscreteConvolution.ConvolutionExistsAt`。
形式化陈述：∀ {M : Type u_1} {S : Type u_2} {E : Type u_3} {E' : Type u_4} {F : Type u
_6} [inst : Monoid M]   [inst_1 : CommSemiring S] [inst_2 : AddCommMonoid E] [in
st_3 : AddCommMonoid E'] [inst_4 : AddCommMonoid F]   [inst_5 : _root_.Module S 
E] [inst_6 : _root_.Module S E'] [inst_7 : _root_.Module S F] [inst_8 : Topologi
calSpace F]   [T2Space F] [ContinuousAdd F] {f f' : M → E} {g : M → E'} {x : M} 
(L : E →ₗ[S] E' →ₗ[S] F),   DiscreteConvolution.ConvolutionExistsAt L f g x →   
  DiscreteConvolution.ConvolutionExistsAt L f' g x →       DiscreteConvolution.c
onvolution L (f + f') g x =         DiscreteConvolution.convolution L f g x + Di
screteConvolution.convolution L f' g x
参数：L : E →ₗ[S] E' →ₗ[S] F；f + f'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `Summable.tsum_add`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid
 α] [inst_1 : TopologicalSpace α] {f g : β → α}   {L : SummationFilter β} [T2Spa
ce α] […
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
-/
lemma ConvolutionExistsAt.add_distrib {f f' : M → E} {g : M → E'} {x : M}
    (L : E →ₗ[S] E' →ₗ[S] F) (hfg : ConvolutionExistsAt L f g x)
    (hfg' : ConvolutionExistsAt L f' g x) :
    ((f + f') ⋆[L] g) x = (f ⋆[L] g) x + (f' ⋆[L] g) x := by
  simpa [convolution] using hfg.tsum_add hfg'

@[to_additive (dont_translate := S E E' F)]
/-
**DiscreteConvolution.ConvolutionExists.add_distrib** 是 Mathlib 中的一个定理，位于命名空间 `D
iscreteConvolution.ConvolutionExists`。
形式化陈述：∀ {M : Type u_1} {S : Type u_2} {E : Type u_3} {E' : Type u_4} {F : Type u
_6} [inst : Monoid M]   [inst_1 : CommSemiring S] [inst_2 : AddCommMonoid E] [in
st_3 : AddCommMonoid E'] [inst_4 : AddCommMonoid F]   [inst_5 : _root_.Module S 
E] [inst_6 : _root_.Module S E'] [inst_7 : _root_.Module S F] [inst_8 : Topologi
calSpace F]   [T2Space F] [ContinuousAdd F] {f f' : M → E} {g : M → E'} (L : E →
ₗ[S] E' →ₗ[S] F),   DiscreteConvolution.ConvolutionExists L f g →     DiscreteCo
nvolution.ConvolutionExists L f' g →       DiscreteConvolution.convolution L (f 
+ f') g =         DiscreteConvolution.convolution L f g + DiscreteConvolution.co
nvolution L f' g
参数：L : E →ₗ[S] E' →ₗ[S] F；f + f'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `DiscreteConvolution.ConvolutionExistsAt.add_distrib`：∀ {M : Type u_1} {S
 : Type u_2} {E : Type u_3} {E' : Type u_4} {F : Type u_6} [inst : Monoid M]   [
inst_1 : CommSemiring S] [inst_2 : AddCom…
-/
lemma ConvolutionExists.add_distrib {f f' : M → E} {g : M → E'} (L : E →ₗ[S] E' →ₗ[S] F)
    (hfg : ConvolutionExists L f g) (hfg' : ConvolutionExists L f' g) :
    (f + f') ⋆[L] g = f ⋆[L] g + f' ⋆[L] g := by
  ext x; exact (hfg x).add_distrib L (hfg' x)

variable {F : Type*}
variable [AddCommMonoid F] [Module S F] [TopologicalSpace F] [ContinuousConstSMul S F] [T2Space F]

@[to_additive (dont_translate := S E E' F)]
/-
**DiscreteConvolution.ConvolutionExistsAt.smul_convolution** 是 Mathlib 中的一个定理，位于
命名空间 `DiscreteConvolution.ConvolutionExistsAt`。
形式化陈述：∀ {M : Type u_1} {S : Type u_2} {E : Type u_3} {E' : Type u_4} [inst : Mon
oid M] [inst_1 : CommSemiring S]   [inst_2 : AddCommMonoid E] [inst_3 : AddCommM
onoid E'] [inst_4 : _root_.Module S E] [inst_5 : _root_.Module S E']   {F : Type
 u_10} [inst_6 : AddCommMonoid F] [inst_7 : _root_.Module S F] [inst_8 : Topolog
icalSpace F]   [ContinuousConstSMul S F] [T2Space F] {c : S} {f : M → E} {g : M 
→ E'} {x : M} (L : E →ₗ[S] E' →ₗ[S] F),   DiscreteConvolution.ConvolutionExistsA
t L f g x →     DiscreteConvolution.convolution L (c • f) g x = c • DiscreteConv
olution.convolution L f g x
参数：L : E →ₗ[S] E' →ₗ[S] F；c • f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `Summable.tsum_const_smul`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3}
 [inst : TopologicalSpace α] [inst_1 : AddCommMonoid α]   [inst_2 : DistribSMul 
γ α] [Continuo…
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
-/
lemma ConvolutionExistsAt.smul_convolution {c : S} {f : M → E} {g : M → E'} {x : M}
    (L : E →ₗ[S] E' →ₗ[S] F) (hfg : ConvolutionExistsAt L f g x) :
    ((c • f) ⋆[L] g) x = c • ((f ⋆[L] g) x) := by
  simpa [convolution] using hfg.tsum_const_smul c

@[to_additive (dont_translate := S E E' F)]
/-
**DiscreteConvolution.ConvolutionExistsAt.convolution_smul** 是 Mathlib 中的一个定理，位于
命名空间 `DiscreteConvolution.ConvolutionExistsAt`。
形式化陈述：∀ {M : Type u_1} {S : Type u_2} {E : Type u_3} {E' : Type u_4} [inst : Mon
oid M] [inst_1 : CommSemiring S]   [inst_2 : AddCommMonoid E] [inst_3 : AddCommM
onoid E'] [inst_4 : _root_.Module S E] [inst_5 : _root_.Module S E']   {F : Type
 u_10} [inst_6 : AddCommMonoid F] [inst_7 : _root_.Module S F] [inst_8 : Topolog
icalSpace F]   [ContinuousConstSMul S F] [T2Space F] {c : S} {f : M → E} {g : M 
→ E'} {x : M} (L : E →ₗ[S] E' →ₗ[S] F),   DiscreteConvolution.ConvolutionExistsA
t L f g x →     DiscreteConvolution.convolution L f (c • g) x = c • DiscreteConv
olution.convolution L f g x
参数：L : E →ₗ[S] E' →ₗ[S] F；c • g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `Summable.tsum_const_smul`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3}
 [inst : TopologicalSpace α] [inst_1 : AddCommMonoid α]   [inst_2 : DistribSMul 
γ α] [Continuo…
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
-/
lemma ConvolutionExistsAt.convolution_smul {c : S} {f : M → E} {g : M → E'} {x : M}
    (L : E →ₗ[S] E' →ₗ[S] F) (hfg : ConvolutionExistsAt L f g x) :
    (f ⋆[L] (c • g)) x = c • ((f ⋆[L] g) x) := by
  simpa [convolution] using hfg.tsum_const_smul c

end ExistenceProperties

/-! ### Commutativity -/

section CommMonoid

variable [CommMonoid M] [CommSemiring S] [AddCommMonoid E] [Module S E] [TopologicalSpace E]

@[to_additive]
/-
**DiscreteConvolution.mulFiber_swapEquiv** 是 Mathlib 中的一个定义，位于命名空间 `DiscreteConv
olution`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private def mulFiber_swapEquiv (x : M) : mulFiber x ≃ mulFiber x where
  toFun := fun ⟨p, h⟩ => ⟨p.swap, by simp_all [mem_mulFiber, mul_comm]⟩
  invFun := fun ⟨p, h⟩ => ⟨p.swap, by simp_all [mem_mulFiber, mul_comm]⟩
  left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
  right_inv := fun ⟨⟨_, _⟩, _⟩ => rfl

@[to_additive (dont_translate := S E) addConvolution_comm]
/-
**DiscreteConvolution.convolution_comm** 是 Mathlib 中的一个定理，位于命名空间 `DiscreteConvol
ution`。
形式化陈述：convolution_comm (L : E ->ₗ[S] E ->ₗ[S] E) (f g : M -> E) (hL : forall x y
, L x y = L y x) : f ⋆[L] g = g ⋆[L] f
参数：L : E ->ₗ[S] E ->ₗ[S] E；f g : M -> E；hL : forall x y, L x y = L y x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : Ad
dCommMonoid α] [inst_1 : TopologicalSpace α] (e : γ ≃ β)   (f : β → α), ∑' (c : 
γ),…
-/
theorem convolution_comm (L : E →ₗ[S] E →ₗ[S] E) (f g : M → E) (hL : ∀ x y, L x y = L y x) :
    f ⋆[L] g = g ⋆[L] f := by
  unfold convolution; ext x
  rw [← (mulFiber_swapEquiv x).tsum_eq]
  congr 1; funext ⟨⟨a, b⟩, _⟩; exact hL (f b) (g a)

end CommMonoid

end DiscreteConvolution

end

