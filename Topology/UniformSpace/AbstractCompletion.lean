/-
Copyright (c) 2019 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
module

public import Mathlib.Topology.UniformSpace.UniformEmbedding
public import Mathlib.Topology.UniformSpace.Equiv

/-!
# Abstract theory of Hausdorff completions of uniform spaces

This file characterizes Hausdorff completions of a uniform space α as complete Hausdorff spaces
equipped with a map from α which has dense image and induces the original uniform structure on α.
Assuming these properties we "extend" uniformly continuous maps from α to complete Hausdorff spaces
to the completions of α. This is the universal property expected from a completion.
It is then used to extend uniformly continuous maps from α to α' to maps between
completions of α and α'.

This file does not construct any such completion; it only studies consequences of their existence.
The first advantage is that formal properties are clearly highlighted without interference from
construction details. The second advantage is that this framework can then be used to compare
different completion constructions. See `Topology/UniformSpace/CompareReals` for an example.
Of course the comparison comes from the universal property as usual.

A general explicit construction of completions is done in `UniformSpace/Completion`, leading
to a functor from uniform spaces to complete Hausdorff uniform spaces that is left adjoint to the
inclusion, see `UniformSpace/UniformSpaceCat` for the category packaging.

## Implementation notes

A tiny technical advantage of using a characteristic predicate such as the properties listed in
`AbstractCompletion` instead of stating the universal property is that the universal property
derived from the predicate is more universe polymorphic.

## References

We don't know any traditional text discussing this. Real world mathematics simply silently
identify the results of any two constructions that lead to something one could reasonably
call a completion.

## Tags

uniform spaces, completion, universal property
-/

@[expose] public section


noncomputable section

open Filter Set Function

/-- A completion of `α` is the data of a complete separated uniform space
and a map from `α` with dense range and inducing the original uniform structure on `α`. -/
@[pp_with_univ]
/-
**AbstractCompletion.** 是 Mathlib 中的一个结构，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A completion of `α` is the data of a complete separated uniform space
and a map from `α` with dense range and inducing the original uniform structure 
on `α`.
-/
structure AbstractCompletion.{v, u} (α : Type u) [UniformSpace α] where
  /-- The underlying space of the completion. -/
  space : Type v
  /-- A map from a space to its completion. -/
  coe : α → space
  /-- The completion carries a uniform structure. -/
  uniformStruct : UniformSpace space
  /-- The completion is complete. -/
  complete : CompleteSpace space
  /-- The completion is a T₀ space. -/
  separation : T0Space space
  /-- The map into the completion is uniform-inducing. -/
  isUniformInducing : IsUniformInducing coe
  /-- The map into the completion has dense range. -/
  dense : DenseRange coe

attribute [local instance]
  AbstractCompletion.uniformStruct AbstractCompletion.complete AbstractCompletion.separation

namespace AbstractCompletion

universe uα vα vα' uβ vβ uγ vγ

variable {α : Type uα} [UniformSpace α] (pkg : AbstractCompletion.{vα} α)

local notation "hatα" => pkg.space

local notation "ι" => pkg.coe

/-- If `α` is complete, then it is an abstract completion of itself. -/
/-
**AbstractCompletion.ofComplete** 是 Mathlib 中的一个定义，位于命名空间 `AbstractCompletion`。
形式化陈述：ofComplete [T0Space α] [CompleteSpace α] : AbstractCompletion α
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsUniformInducing.id`：IsUniformInducing.id : IsUniformInducing (@id α)

--- 原说明 ---
If `α` is complete, then it is an abstract completion of itself.
-/
def ofComplete [T0Space α] [CompleteSpace α] : AbstractCompletion α :=
  mk α id inferInstance inferInstance inferInstance .id denseRange_id
/-
**AbstractCompletion.closure_range** 是 Mathlib 中的一个定理，位于命名空间 `AbstractCompletion
`。
形式化陈述：closure_range : closure (range ι) = univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DenseRange.closure_range`：DenseRange.closure_range (h : DenseRange f) : 
closure (range f) = univ
· 使用定理 `AbstractCompletion.dense`：∀ {α : Type u} [inst : UniformSpace α] (self :
 AbstractCompletion.{v, u} α), DenseRange self.coe
-/
theorem closure_range : closure (range ι) = univ :=
  pkg.dense.closure_range
/-
**AbstractCompletion.isDenseInducing** 是 Mathlib 中的一个定理，位于命名空间 `AbstractCompleti
on`。
形式化陈述：isDenseInducing : IsDenseInducing ι
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUniformInducing.isInducing`：IsUniformInducing.isInducing {f : α -> β} 
(h : IsUniformInducing f) : IsInducing f
· 使用定理 `AbstractCompletion.isUniformInducing`：∀ {α : Type u} [inst : UniformSpac
e α] (self : AbstractCompletion.{v, u} α), IsUniformInducing self.coe
· 使用定理 `AbstractCompletion.dense`：∀ {α : Type u} [inst : UniformSpace α] (self :
 AbstractCompletion.{v, u} α), DenseRange self.coe
-/
theorem isDenseInducing : IsDenseInducing ι :=
  ⟨pkg.isUniformInducing.isInducing, pkg.dense⟩

@[fun_prop]
/-
**AbstractCompletion.uniformContinuous_coe** 是 Mathlib 中的一个定理，位于命名空间 `AbstractCo
mpletion`。
形式化陈述：uniformContinuous_coe : UniformContinuous ι
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUniformInducing.uniformContinuous`：IsUniformInducing.uniformContinuous
 {f : α -> β} (hf : IsUniformInducing f) : UniformContinuous f
· 使用定理 `AbstractCompletion.isUniformInducing`：∀ {α : Type u} [inst : UniformSpac
e α] (self : AbstractCompletion.{v, u} α), IsUniformInducing self.coe
-/
theorem uniformContinuous_coe : UniformContinuous ι :=
  IsUniformInducing.uniformContinuous pkg.isUniformInducing
/-
**AbstractCompletion.continuous_coe** 是 Mathlib 中的一个定理，位于命名空间 `AbstractCompletio
n`。
形式化陈述：continuous_coe : Continuous ι
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuous.continuous`：UniformContinuous.continuous (hf : Uniform
Continuous f) : Continuous f
· 使用定理 `AbstractCompletion.uniformContinuous_coe`：uniformContinuous_coe : Unifor
mContinuous ι
-/
theorem continuous_coe : Continuous ι :=
  pkg.uniformContinuous_coe.continuous

@[elab_as_elim]
/-
**AbstractCompletion.induction_on** 是 Mathlib 中的一个定理，位于命名空间 `AbstractCompletion`
。
形式化陈述：induction_on {p : hatα -> Prop} (a : hatα) (hp : IsClosed { a | p a }) (ih
 : forall a, p (ι a)) : p a
参数：a : hatα；hp : IsClosed { a | p a }；ih : forall a, p (ι a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isClosed_property`：isClosed_property [TopologicalSpace β] {e : α -> β} {
p : β -> Prop} (he : DenseRange e) (hp : IsClosed { x | p x }) (h : forall a, p 
(e a)) …
· 使用定理 `AbstractCompletion.dense`：∀ {α : Type u} [inst : UniformSpace α] (self :
 AbstractCompletion.{v, u} α), DenseRange self.coe
-/
theorem induction_on {p : hatα → Prop} (a : hatα) (hp : IsClosed { a | p a }) (ih : ∀ a, p (ι a)) :
    p a :=
  isClosed_property pkg.dense hp ih a

variable {β : Type uβ}
/-
**AbstractCompletion.funext** 是 Mathlib 中的一个定理，位于命名空间 `AbstractCompletion`。
形式化陈述：∀ {α : Type uα} [inst : UniformSpace α] (pkg : AbstractCompletion.{vα, uα}
 α) {β : Type uβ}   [inst_1 : TopologicalSpace β] [T2Space β] {f g : pkg.space →
 β},   Continuous f → Continuous g → (∀ (a : α), f (pkg.coe a) = g (pkg.coe a)) 
→ f = g
参数：pkg : AbstractCompletion.{vα, uα} α；∀ (a : α), f (pkg.coe a) = g (pkg.coe a)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `AbstractCompletion.induction_on`：induction_on {p : hatα -> Prop} (a : ha
tα) (hp : IsClosed { a | p a }) (ih : forall a, p (ι a)) : p a
· 使用定理 `isClosed_eq`：isClosed_eq [T2Space X] {f g : Y -> X} (hf : Continuous f) 
(hg : Continuous g) : IsClosed { y : Y | f y = g y }
-/
protected theorem funext [TopologicalSpace β] [T2Space β] {f g : hatα → β} (hf : Continuous f)
    (hg : Continuous g) (h : ∀ a, f (ι a) = g (ι a)) : f = g :=
  funext fun a => pkg.induction_on a (isClosed_eq hf hg) h

variable [UniformSpace β]

section Extend

/-- Extension of maps to completions -/
/-
**AbstractCompletion.extend** 是 Mathlib 中的一个定义，位于命名空间 `AbstractCompletion`。
形式化陈述：{α : Type uα} →   [inst : UniformSpace α] →     (pkg : AbstractCompletion.
{vα, uα} α) → {β : Type uβ} → [UniformSpace β] → (α → β) → pkg.space → β
参数：pkg : AbstractCompletion.{vα, uα} α；α → β。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AbstractCompletion.isDenseInducing`：isDenseInducing : IsDenseInducing ι
· 使用定理 `AbstractCompletion.dense`：∀ {α : Type u} [inst : UniformSpace α] (self :
 AbstractCompletion.{v, u} α), DenseRange self.coe

--- 原说明 ---
Extension of maps to completions
-/
protected def extend (f : α → β) : hatα → β :=
  open scoped Classical in
  if UniformContinuous f then pkg.isDenseInducing.extend f else fun x => f (pkg.dense.some x)

variable {f : α → β}
/-
**AbstractCompletion.extend_def** 是 Mathlib 中的一个定理，位于命名空间 `AbstractCompletion`。
形式化陈述：extend_def (hf : UniformContinuous f) : pkg.extend f = pkg.isDenseInducing
.extend f
参数：hf : UniformContinuous f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `AbstractCompletion.isDenseInducing`：isDenseInducing : IsDenseInducing ι
· 使用定理 `AbstractCompletion.dense`：∀ {α : Type u} [inst : UniformSpace α] (self :
 AbstractCompletion.{v, u} α), DenseRange self.coe
-/
theorem extend_def (hf : UniformContinuous f) : pkg.extend f = pkg.isDenseInducing.extend f :=
  if_pos hf
/-
**AbstractCompletion.inseparable_extend_coe** 是 Mathlib 中的一个定理，位于命名空间 `AbstractC
ompletion`。
形式化陈述：inseparable_extend_coe (hf : UniformContinuous f) (x : α) : Inseparable (p
kg.extend f (ι x)) (f x)
参数：hf : UniformContinuous f；x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AbstractCompletion.isDenseInducing`：isDenseInducing : IsDenseInducing ι
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AbstractCompletion.extend_def`：extend_def (hf : UniformContinuous f) : p
kg.extend f = pkg.isDenseInducing.extend f
· 使用定理 `IsDenseInducing.inseparable_extend`：inseparable_extend [R1Space γ] (di :
 IsDenseInducing i) {f : α -> γ} {a : α} (hf : ContinuousAt f a) : Inseparable (
di.extend f (i a)) (f a)
· 使用定理 `instR1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [RegularSpace 
X], R1Space X
· 使用定理 `UniformSpace.to_regularSpace`：∀ {α : Type u} [inst : UniformSpace α], Re
gularSpace α
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `UniformContinuous.continuous`：UniformContinuous.continuous (hf : Uniform
Continuous f) : Continuous f
-/
theorem inseparable_extend_coe (hf : UniformContinuous f) (x : α) :
    Inseparable (pkg.extend f (ι x)) (f x) := by
  rw [extend_def _ hf]
  exact pkg.isDenseInducing.inseparable_extend hf.continuous.continuousAt
/-
**AbstractCompletion.extend_coe** 是 Mathlib 中的一个定理，位于命名空间 `AbstractCompletion`。
形式化陈述：extend_coe [T2Space β] (hf : UniformContinuous f) (a : α) : (pkg.extend f)
 (ι a) = f a
参数：hf : UniformContinuous f；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AbstractCompletion.isDenseInducing`：isDenseInducing : IsDenseInducing ι
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AbstractCompletion.extend_def`：extend_def (hf : UniformContinuous f) : p
kg.extend f = pkg.isDenseInducing.extend f
· 使用定理 `IsDenseInducing.extend_eq`：extend_eq [T2Space γ] (di : IsDenseInducing i
) {f : α -> γ} (hf : Continuous f) (a : α) : di.extend f (i a) = f a
· 使用定理 `UniformContinuous.continuous`：UniformContinuous.continuous (hf : Uniform
Continuous f) : Continuous f
-/
theorem extend_coe [T2Space β] (hf : UniformContinuous f) (a : α) : (pkg.extend f) (ι a) = f a := by
  rw [pkg.extend_def hf]
  exact pkg.isDenseInducing.extend_eq hf.continuous a

variable [CompleteSpace β]

@[fun_prop]
/-
**AbstractCompletion.uniformContinuous_extend** 是 Mathlib 中的一个定理，位于命名空间 `Abstrac
tCompletion`。
形式化陈述：uniformContinuous_extend : UniformContinuous (pkg.extend f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AbstractCompletion.isDenseInducing`：isDenseInducing : IsDenseInducing ι
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AbstractCompletion.extend_def`：extend_def (hf : UniformContinuous f) : p
kg.extend f = pkg.isDenseInducing.extend f
· 使用定理 `uniformContinuous_uniformly_extend`：uniformContinuous_uniformly_extend [
CompleteSpace γ] : UniformContinuous ψ
· 使用定理 `AbstractCompletion.isUniformInducing`：∀ {α : Type u} [inst : UniformSpac
e α] (self : AbstractCompletion.{v, u} α), IsUniformInducing self.coe
· 使用定理 `AbstractCompletion.dense`：∀ {α : Type u} [inst : UniformSpace α] (self :
 AbstractCompletion.{v, u} α), DenseRange self.coe
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `uniformContinuous_of_const`：uniformContinuous_of_const {c : α -> β} (h :
 forall a b, c a = c b) : UniformContinuous c
-/
theorem uniformContinuous_extend : UniformContinuous (pkg.extend f) := by
  by_cases hf : UniformContinuous f
  · rw [pkg.extend_def hf]
    exact uniformContinuous_uniformly_extend pkg.isUniformInducing pkg.dense hf
  · unfold AbstractCompletion.extend
    rw [if_neg hf]
    exact uniformContinuous_of_const fun a b => by congr 1
/-
**AbstractCompletion.continuous_extend** 是 Mathlib 中的一个定理，位于命名空间 `AbstractComple
tion`。
形式化陈述：continuous_extend : Continuous (pkg.extend f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformContinuous.continuous`：UniformContinuous.continuous (hf : Uniform
Continuous f) : Continuous f
· 使用定理 `AbstractCompletion.uniformContinuous_extend`：uniformContinuous_extend : 
UniformContinuous (pkg.extend f)
-/
theorem continuous_extend : Continuous (pkg.extend f) :=
  pkg.uniformContinuous_extend.continuous

@[fun_prop]
/-
**AbstractCompletion.isUniformInducing_extend** 是 Mathlib 中的一个引理，位于命名空间 `Abstrac
tCompletion`。
形式化陈述：isUniformInducing_extend (h : IsUniformInducing f) : IsUniformInducing (pk
g.extend f)
参数：h : IsUniformInducing f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AbstractCompletion.isDenseInducing`：isDenseInducing : IsDenseInducing ι
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AbstractCompletion.extend_def`：extend_def (hf : UniformContinuous f) : p
kg.extend f = pkg.isDenseInducing.extend f
· 使用定理 `IsUniformInducing.uniformContinuous`：IsUniformInducing.uniformContinuous
 {f : α -> β} (hf : IsUniformInducing f) : UniformContinuous f
· 使用引理 `IsDenseInducing.isUniformInducing_extend`：IsDenseInducing.isUniformInduc
ing_extend {γ : Type*} [UniformSpace γ] [CompleteSpace β] [CompleteSpace γ] {i :
 α -> β} {f : α -> γ} (hid : I…
· 使用定理 `AbstractCompletion.complete`：∀ {α : Type u} [inst : UniformSpace α] (sel
f : AbstractCompletion.{v, u} α), CompleteSpace self.space
· 使用定理 `AbstractCompletion.isUniformInducing`：∀ {α : Type u} [inst : UniformSpac
e α] (self : AbstractCompletion.{v, u} α), IsUniformInducing self.coe
-/
lemma isUniformInducing_extend (h : IsUniformInducing f) :
    IsUniformInducing (pkg.extend f) := by
  rw [extend_def _ h.uniformContinuous]
  exact pkg.isDenseInducing.isUniformInducing_extend pkg.isUniformInducing h

variable [T0Space β]
/-
**AbstractCompletion.extend_unique** 是 Mathlib 中的一个定理，位于命名空间 `AbstractCompletion
`。
形式化陈述：extend_unique (hf : UniformContinuous f) {g : hatα -> β} (hg : UniformCont
inuous g) (h : forall a : α, f a = g (ι a)) : pkg.extend f = g
参数：hf : UniformContinuous f；hg : UniformContinuous g；h : forall a : α, f a = g (
ι a)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AbstractCompletion.funext`：∀ {α : Type uα} [inst : UniformSpace α] (pkg 
: AbstractCompletion.{vα, uα} α) {β : Type uβ}   [inst_1 : TopologicalSpace β] [
T2Space β] {f g…
· 使用定理 `T25Space.t2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T25Space
 X], T2Space X
· 使用定理 `T3Space.t25Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T3Space 
X], T25Space X
· 使用定理 `instT3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T0Space X] [R
egularSpace X], T3Space X
· 使用定理 `UniformSpace.to_regularSpace`：∀ {α : Type u} [inst : UniformSpace α], Re
gularSpace α
· 使用定理 `AbstractCompletion.continuous_extend`：continuous_extend : Continuous (pk
g.extend f)
· 使用定理 `UniformContinuous.continuous`：UniformContinuous.continuous (hf : Uniform
Continuous f) : Continuous f
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AbstractCompletion.extend_coe`：extend_coe [T2Space β] (hf : UniformConti
nuous f) (a : α) : (pkg.extend f) (ι a) = f a
-/
theorem extend_unique (hf : UniformContinuous f) {g : hatα → β} (hg : UniformContinuous g)
    (h : ∀ a : α, f a = g (ι a)) : pkg.extend f = g := by
  apply pkg.funext pkg.continuous_extend hg.continuous
  simpa only [pkg.extend_coe hf] using h

@[simp]
/-
**AbstractCompletion.extend_comp_coe** 是 Mathlib 中的一个定理，位于命名空间 `AbstractCompleti
on`。
形式化陈述：extend_comp_coe {f : hatα -> β} (hf : UniformContinuous f) : pkg.extend (f
 ∘ ι) = f
参数：hf : UniformContinuous f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `AbstractCompletion.induction_on`：induction_on {p : hatα -> Prop} (a : ha
tα) (hp : IsClosed { a | p a }) (ih : forall a, p (ι a)) : p a
· 使用定理 `isClosed_eq`：isClosed_eq [T2Space X] {f g : Y -> X} (hf : Continuous f) 
(hg : Continuous g) : IsClosed { y : Y | f y = g y }
· 使用定理 `T25Space.t2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T25Space
 X], T2Space X
· 使用定理 `T3Space.t25Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T3Space 
X], T25Space X
· 使用定理 `instT3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T0Space X] [R
egularSpace X], T3Space X
· 使用定理 `UniformSpace.to_regularSpace`：∀ {α : Type u} [inst : UniformSpace α], Re
gularSpace α
· 使用定理 `AbstractCompletion.continuous_extend`：continuous_extend : Continuous (pk
g.extend f)
· 使用定理 `UniformContinuous.continuous`：UniformContinuous.continuous (hf : Uniform
Continuous f) : Continuous f
· 使用定理 `AbstractCompletion.extend_coe`：extend_coe [T2Space β] (hf : UniformConti
nuous f) (a : α) : (pkg.extend f) (ι a) = f a
· 使用定理 `UniformContinuous.comp`：∀ {α : Type ua} {β : Type ub} {γ : Type uc} [ins
t : UniformSpace α] [inst_1 : UniformSpace β] [inst_2 : UniformSpace γ]   {g : β
 → γ} {f : α…
· 使用定理 `AbstractCompletion.uniformContinuous_coe`：uniformContinuous_coe : Unifor
mContinuous ι
-/
theorem extend_comp_coe {f : hatα → β} (hf : UniformContinuous f) : pkg.extend (f ∘ ι) = f :=
  funext fun x =>
    pkg.induction_on x (isClosed_eq pkg.continuous_extend hf.continuous) fun y =>
      pkg.extend_coe (hf.comp <| pkg.uniformContinuous_coe) y

end Extend

section MapSec

variable (pkg' : AbstractCompletion.{vβ} β)

local notation "hatβ" => pkg'.space

local notation "ι'" => pkg'.coe

/-- Lifting maps to completions -/
/-
**AbstractCompletion.map** 是 Mathlib 中的一个定义，位于命名空间 `AbstractCompletion`。
形式化陈述：{α : Type uα} →   [inst : UniformSpace α] →     (pkg : AbstractCompletion.
{vα, uα} α) →       {β : Type uβ} →         [inst_1 : UniformSpace β] → (pkg' : 
AbstractCompletion.{vβ, uβ} β) → (α → β) → pkg.space → pkg'.space
参数：pkg : AbstractCompletion.{vα, uα} α；pkg' : AbstractCompletion.{vβ, uβ} β；α → 
β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lifting maps to completions
-/
protected def map (f : α → β) : hatα → hatβ :=
  pkg.extend (ι' ∘ f)

local notation "map" => pkg.map pkg'

variable (f : α → β)

@[fun_prop]
/-
**AbstractCompletion.uniformContinuous_map** 是 Mathlib 中的一个定理，位于命名空间 `AbstractCo
mpletion`。
形式化陈述：uniformContinuous_map : UniformContinuous (map f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AbstractCompletion.uniformContinuous_extend`：uniformContinuous_extend : 
UniformContinuous (pkg.extend f)
· 使用定理 `AbstractCompletion.complete`：∀ {α : Type u} [inst : UniformSpace α] (sel
f : AbstractCompletion.{v, u} α), CompleteSpace self.space
-/
theorem uniformContinuous_map : UniformContinuous (map f) :=
  pkg.uniformContinuous_extend

@[continuity]
/-
**AbstractCompletion.continuous_map** 是 Mathlib 中的一个定理，位于命名空间 `AbstractCompletio
n`。
形式化陈述：continuous_map : Continuous (map f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AbstractCompletion.continuous_extend`：continuous_extend : Continuous (pk
g.extend f)
· 使用定理 `AbstractCompletion.complete`：∀ {α : Type u} [inst : UniformSpace α] (sel
f : AbstractCompletion.{v, u} α), CompleteSpace self.space
-/
theorem continuous_map : Continuous (map f) :=
  pkg.continuous_extend

variable {f}

@[simp]
/-
**AbstractCompletion.map_coe** 是 Mathlib 中的一个定理，位于命名空间 `AbstractCompletion`。
形式化陈述：map_coe (hf : UniformContinuous f) (a : α) : map f (ι a) = ι' (f a)
参数：hf : UniformContinuous f；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AbstractCompletion.extend_coe`：extend_coe [T2Space β] (hf : UniformConti
nuous f) (a : α) : (pkg.extend f) (ι a) = f a
· 使用定理 `T25Space.t2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T25Space
 X], T2Space X
· 使用定理 `T3Space.t25Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T3Space 
X], T25Space X
· 使用定理 `instT3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T0Space X] [R
egularSpace X], T3Space X
· 使用定理 `AbstractCompletion.separation`：∀ {α : Type u} [inst : UniformSpace α] (s
elf : AbstractCompletion.{v, u} α), T0Space self.space
· 使用定理 `UniformSpace.to_regularSpace`：∀ {α : Type u} [inst : UniformSpace α], Re
gularSpace α
· 使用定理 `UniformContinuous.comp`：∀ {α : Type ua} {β : Type ub} {γ : Type uc} [ins
t : UniformSpace α] [inst_1 : UniformSpace β] [inst_2 : UniformSpace γ]   {g : β
 → γ} {f : α…
· 使用定理 `AbstractCompletion.uniformContinuous_coe`：uniformContinuous_coe : Unifor
mContinuous ι
-/
theorem map_coe (hf : UniformContinuous f) (a : α) : map f (ι a) = ι' (f a) :=
  pkg.extend_coe (pkg'.uniformContinuous_coe.comp hf) a
/-
**AbstractCompletion.map_unique** 是 Mathlib 中的一个定理，位于命名空间 `AbstractCompletion`。
形式化陈述：map_unique {f : α -> β} {g : hatα -> hatβ} (hg : UniformContinuous g) (h :
 forall a, ι' (f a) = g (ι a)) : map f = g
参数：hg : UniformContinuous g；h : forall a, ι' (f a) = g (ι a)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AbstractCompletion.funext`：∀ {α : Type uα} [inst : UniformSpace α] (pkg 
: AbstractCompletion.{vα, uα} α) {β : Type uβ}   [inst_1 : TopologicalSpace β] [
T2Space β] {f g…
· 使用定理 `T25Space.t2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T25Space
 X], T2Space X
· 使用定理 `T3Space.t25Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T3Space 
X], T25Space X
· 使用定理 `instT3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T0Space X] [R
egularSpace X], T3Space X
· 使用定理 `AbstractCompletion.separation`：∀ {α : Type u} [inst : UniformSpace α] (s
elf : AbstractCompletion.{v, u} α), T0Space self.space
· 使用定理 `UniformSpace.to_regularSpace`：∀ {α : Type u} [inst : UniformSpace α], Re
gularSpace α
· 使用定理 `AbstractCompletion.continuous_map`：continuous_map : Continuous (map f)
· 使用定理 `UniformContinuous.continuous`：UniformContinuous.continuous (hf : Uniform
Continuous f) : Continuous f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `AbstractCompletion.extend_coe`：extend_coe [T2Space β] (hf : UniformConti
nuous f) (a : α) : (pkg.extend f) (ι a) = f a
· 使用定理 `UniformContinuous.comp`：∀ {α : Type ua} {β : Type ub} {γ : Type uc} [ins
t : UniformSpace α] [inst_1 : UniformSpace β] [inst_2 : UniformSpace γ]   {g : β
 → γ} {f : α…
· 使用定理 `AbstractCompletion.uniformContinuous_coe`：uniformContinuous_coe : Unifor
mContinuous ι
-/
theorem map_unique {f : α → β} {g : hatα → hatβ} (hg : UniformContinuous g)
    (h : ∀ a, ι' (f a) = g (ι a)) : map f = g :=
  pkg.funext (pkg.continuous_map _ _) hg.continuous <| by
    intro a
    change pkg.extend (ι' ∘ f) _ = _
    simp_rw [Function.comp_def, h, ← comp_apply (f := g)]
    rw [pkg.extend_coe (hg.comp pkg.uniformContinuous_coe)]

@[simp]
/-
**AbstractCompletion.map_id** 是 Mathlib 中的一个定理，位于命名空间 `AbstractCompletion`。
形式化陈述：map_id : pkg.map pkg id = id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AbstractCompletion.map_unique`：map_unique {f : α -> β} {g : hatα -> hatβ
} (hg : UniformContinuous g) (h : forall a, ι' (f a) = g (ι a)) : map f = g
· 使用定理 `uniformContinuous_id`：uniformContinuous_id : UniformContinuous (@id α)
-/
theorem map_id : pkg.map pkg id = id :=
  pkg.map_unique pkg uniformContinuous_id fun _ => rfl

variable {γ : Type uγ} [UniformSpace γ]
/-
**AbstractCompletion.extend_map** 是 Mathlib 中的一个定理，位于命名空间 `AbstractCompletion`。
形式化陈述：extend_map [CompleteSpace γ] [T0Space γ] {f : β -> γ} {g : α -> β} (hf : U
niformContinuous f) (hg : UniformContinuous g) : pkg'.extend f ∘ map g = pkg.ext
end (f ∘ g)
参数：hf : UniformContinuous f；hg : UniformContinuous g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AbstractCompletion.funext`：∀ {α : Type uα} [inst : UniformSpace α] (pkg 
: AbstractCompletion.{vα, uα} α) {β : Type uβ}   [inst_1 : TopologicalSpace β] [
T2Space β] {f g…
· 使用定理 `T25Space.t2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T25Space
 X], T2Space X
· 使用定理 `T3Space.t25Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T3Space 
X], T25Space X
· 使用定理 `instT3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T0Space X] [R
egularSpace X], T3Space X
· 使用定理 `UniformSpace.to_regularSpace`：∀ {α : Type u} [inst : UniformSpace α], Re
gularSpace α
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `AbstractCompletion.continuous_extend`：continuous_extend : Continuous (pk
g.extend f)
· 使用定理 `AbstractCompletion.continuous_map`：continuous_map : Continuous (map f)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AbstractCompletion.extend_coe`：extend_coe [T2Space β] (hf : UniformConti
nuous f) (a : α) : (pkg.extend f) (ι a) = f a
· 使用定理 `UniformContinuous.comp`：∀ {α : Type ua} {β : Type ub} {γ : Type uc} [ins
t : UniformSpace α] [inst_1 : UniformSpace β] [inst_2 : UniformSpace γ]   {g : β
 → γ} {f : α…
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `AbstractCompletion.map_coe`：map_coe (hf : UniformContinuous f) (a : α) :
 map f (ι a) = ι' (f a)
-/
theorem extend_map [CompleteSpace γ] [T0Space γ] {f : β → γ} {g : α → β}
    (hf : UniformContinuous f) (hg : UniformContinuous g) :
    pkg'.extend f ∘ map g = pkg.extend (f ∘ g) :=
  pkg.funext (pkg'.continuous_extend.comp (pkg.continuous_map pkg' _)) pkg.continuous_extend
    fun a => by
    rw [pkg.extend_coe (hf.comp hg), comp_apply, pkg.map_coe pkg' hg, pkg'.extend_coe hf]
    rfl

variable (pkg'' : AbstractCompletion.{vγ} γ)
/-
**AbstractCompletion.map_comp** 是 Mathlib 中的一个定理，位于命名空间 `AbstractCompletion`。
形式化陈述：map_comp {g : β -> γ} {f : α -> β} (hg : UniformContinuous g) (hf : Unifor
mContinuous f) : pkg'.map pkg'' g ∘ pkg.map pkg' f = pkg.map pkg'' (g ∘ f)
参数：hg : UniformContinuous g；hf : UniformContinuous f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AbstractCompletion.extend_map`：extend_map [CompleteSpace γ] [T0Space γ] 
{f : β -> γ} {g : α -> β} (hf : UniformContinuous f) (hg : UniformContinuous g) 
: pkg'.extend f ∘ m…
· 使用定理 `AbstractCompletion.complete`：∀ {α : Type u} [inst : UniformSpace α] (sel
f : AbstractCompletion.{v, u} α), CompleteSpace self.space
· 使用定理 `AbstractCompletion.separation`：∀ {α : Type u} [inst : UniformSpace α] (s
elf : AbstractCompletion.{v, u} α), T0Space self.space
· 使用定理 `UniformContinuous.comp`：∀ {α : Type ua} {β : Type ub} {γ : Type uc} [ins
t : UniformSpace α] [inst_1 : UniformSpace β] [inst_2 : UniformSpace γ]   {g : β
 → γ} {f : α…
· 使用定理 `AbstractCompletion.uniformContinuous_coe`：uniformContinuous_coe : Unifor
mContinuous ι
-/
theorem map_comp {g : β → γ} {f : α → β} (hg : UniformContinuous g) (hf : UniformContinuous f) :
    pkg'.map pkg'' g ∘ pkg.map pkg' f = pkg.map pkg'' (g ∘ f) :=
  pkg.extend_map pkg' (pkg''.uniformContinuous_coe.comp hg) hf

/-- The uniform isomorphism between two completions of isomorphic uniform spaces. -/
/-
**AbstractCompletion.mapEquiv** 是 Mathlib 中的一个定义，位于命名空间 `AbstractCompletion`。
形式化陈述：mapEquiv (e : α ≃ᵤ β) : hatα ≃ᵤ hatβ where toFun
参数：e : α ≃ᵤ β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The uniform isomorphism between two completions of isomorphic uniform spaces.
-/
def mapEquiv (e : α ≃ᵤ β) : hatα ≃ᵤ hatβ where
  toFun := pkg.map pkg' e
  invFun := pkg'.map pkg e.symm
  uniformContinuous_toFun := uniformContinuous_map ..
  uniformContinuous_invFun := uniformContinuous_map ..
  left_inv := Function.leftInverse_iff_comp.2 <| by
    simp [map_comp _ _ _ e.symm.uniformContinuous e.uniformContinuous]
  right_inv := Function.rightInverse_iff_comp.2 <| by
    simp [map_comp _ _ _ e.uniformContinuous e.symm.uniformContinuous]

@[simp]
/-
**AbstractCompletion.mapEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `AbstractCompletion
`。
形式化陈述：mapEquiv_symm (e : α ≃ᵤ β) : (pkg.mapEquiv pkg' e).symm = pkg'.mapEquiv pk
g e.symm
参数：e : α ≃ᵤ β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapEquiv_symm (e : α ≃ᵤ β) :
    (pkg.mapEquiv pkg' e).symm = pkg'.mapEquiv pkg e.symm := rfl

@[simp]
/-
**AbstractCompletion.mapEquiv_coe** 是 Mathlib 中的一个定理，位于命名空间 `AbstractCompletion`
。
形式化陈述：mapEquiv_coe (e : α ≃ᵤ β) (a : α) : pkg.mapEquiv pkg' e (ι a) = ι' (e a)
参数：e : α ≃ᵤ β；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AbstractCompletion.map_coe`：map_coe (hf : UniformContinuous f) (a : α) :
 map f (ι a) = ι' (f a)
· 使用定理 `UniformEquiv.uniformContinuous`：∀ {α : Type u} {β : Type u_1} [inst : Un
iformSpace α] [inst_1 : UniformSpace β] (h : α ≃ᵤ β), UniformContinuous ⇑h
-/
theorem mapEquiv_coe (e : α ≃ᵤ β) (a : α) : pkg.mapEquiv pkg' e (ι a) = ι' (e a) :=
  pkg.map_coe pkg' e.uniformContinuous _

end MapSec

section Compare

-- We can now compare two completion packages for the same uniform space
variable (pkg' : AbstractCompletion.{vα'} α)

/-- The comparison map between two completions of the same uniform space. -/
/-
**AbstractCompletion.compare** 是 Mathlib 中的一个定义，位于命名空间 `AbstractCompletion`。
形式化陈述：compare : pkg.space -> pkg'.space
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The comparison map between two completions of the same uniform space.
-/
def compare : pkg.space → pkg'.space :=
  pkg.extend pkg'.coe

@[fun_prop]
/-
**AbstractCompletion.uniformContinuous_compare** 是 Mathlib 中的一个定理，位于命名空间 `Abstra
ctCompletion`。
形式化陈述：uniformContinuous_compare : UniformContinuous (pkg.compare pkg')
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AbstractCompletion.uniformContinuous_extend`：uniformContinuous_extend : 
UniformContinuous (pkg.extend f)
· 使用定理 `AbstractCompletion.complete`：∀ {α : Type u} [inst : UniformSpace α] (sel
f : AbstractCompletion.{v, u} α), CompleteSpace self.space
-/
theorem uniformContinuous_compare : UniformContinuous (pkg.compare pkg') :=
  pkg.uniformContinuous_extend
/-
**AbstractCompletion.compare_coe** 是 Mathlib 中的一个定理，位于命名空间 `AbstractCompletion`。
形式化陈述：compare_coe (a : α) : pkg.compare pkg' (pkg.coe a) = pkg'.coe a
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AbstractCompletion.extend_coe`：extend_coe [T2Space β] (hf : UniformConti
nuous f) (a : α) : (pkg.extend f) (ι a) = f a
· 使用定理 `T25Space.t2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T25Space
 X], T2Space X
· 使用定理 `T3Space.t25Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T3Space 
X], T25Space X
· 使用定理 `instT3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T0Space X] [R
egularSpace X], T3Space X
· 使用定理 `AbstractCompletion.separation`：∀ {α : Type u} [inst : UniformSpace α] (s
elf : AbstractCompletion.{v, u} α), T0Space self.space
· 使用定理 `UniformSpace.to_regularSpace`：∀ {α : Type u} [inst : UniformSpace α], Re
gularSpace α
· 使用定理 `AbstractCompletion.uniformContinuous_coe`：uniformContinuous_coe : Unifor
mContinuous ι
-/
theorem compare_coe (a : α) : pkg.compare pkg' (pkg.coe a) = pkg'.coe a :=
  pkg.extend_coe pkg'.uniformContinuous_coe a
/-
**AbstractCompletion.inverse_compare** 是 Mathlib 中的一个定理，位于命名空间 `AbstractCompleti
on`。
形式化陈述：inverse_compare : pkg.compare pkg' ∘ pkg'.compare pkg = id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AbstractCompletion.uniformContinuous_compare`：uniformContinuous_compare 
: UniformContinuous (pkg.compare pkg')
· 使用定理 `AbstractCompletion.funext`：∀ {α : Type uα} [inst : UniformSpace α] (pkg 
: AbstractCompletion.{vα, uα} α) {β : Type uβ}   [inst_1 : TopologicalSpace β] [
T2Space β] {f g…
· 使用定理 `T25Space.t2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T25Space
 X], T2Space X
· 使用定理 `T3Space.t25Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T3Space 
X], T25Space X
· 使用定理 `instT3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T0Space X] [R
egularSpace X], T3Space X
· 使用定理 `AbstractCompletion.separation`：∀ {α : Type u} [inst : UniformSpace α] (s
elf : AbstractCompletion.{v, u} α), T0Space self.space
· 使用定理 `UniformSpace.to_regularSpace`：∀ {α : Type u} [inst : UniformSpace α], Re
gularSpace α
· 使用定理 `UniformContinuous.continuous`：UniformContinuous.continuous (hf : Uniform
Continuous f) : Continuous f
· 使用定理 `UniformContinuous.comp`：∀ {α : Type ua} {β : Type ub} {γ : Type uc} [ins
t : UniformSpace α] [inst_1 : UniformSpace β] [inst_2 : UniformSpace γ]   {g : β
 → γ} {f : α…
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `AbstractCompletion.compare_coe`：compare_coe (a : α) : pkg.compare pkg' (
pkg.coe a) = pkg'.coe a
-/
theorem inverse_compare : pkg.compare pkg' ∘ pkg'.compare pkg = id := by
  have uc := pkg.uniformContinuous_compare pkg'
  have uc' := pkg'.uniformContinuous_compare pkg
  apply pkg'.funext (uc.comp uc').continuous continuous_id
  intro a
  rw [comp_apply, pkg'.compare_coe pkg, pkg.compare_coe pkg']
  rfl

/-- The uniform bijection between two completions of the same uniform space. -/
/-
**AbstractCompletion.compareEquiv** 是 Mathlib 中的一个定义，位于命名空间 `AbstractCompletion`
。
形式化陈述：compareEquiv : pkg.space ≃ᵤ pkg'.space where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AbstractCompletion.uniformContinuous_compare`：uniformContinuous_compare 
: UniformContinuous (pkg.compare pkg')

--- 原说明 ---
The uniform bijection between two completions of the same uniform space.
-/
def compareEquiv : pkg.space ≃ᵤ pkg'.space where
  toFun := pkg.compare pkg'
  invFun := pkg'.compare pkg
  left_inv := congr_fun (pkg'.inverse_compare pkg)
  right_inv := congr_fun (pkg.inverse_compare pkg')
  uniformContinuous_toFun := uniformContinuous_compare _ _
  uniformContinuous_invFun := uniformContinuous_compare _ _

@[fun_prop]
/-
**AbstractCompletion.uniformContinuous_compareEquiv** 是 Mathlib 中的一个定理，位于命名空间 `A
bstractCompletion`。
形式化陈述：uniformContinuous_compareEquiv : UniformContinuous (pkg.compareEquiv pkg')
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AbstractCompletion.uniformContinuous_compare`：uniformContinuous_compare 
: UniformContinuous (pkg.compare pkg')
-/
theorem uniformContinuous_compareEquiv : UniformContinuous (pkg.compareEquiv pkg') :=
  pkg.uniformContinuous_compare pkg'

@[fun_prop]
/-
**AbstractCompletion.uniformContinuous_compareEquiv_symm** 是 Mathlib 中的一个定理，位于命名
空间 `AbstractCompletion`。
形式化陈述：uniformContinuous_compareEquiv_symm : UniformContinuous (pkg.compareEquiv 
pkg').symm
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AbstractCompletion.uniformContinuous_compare`：uniformContinuous_compare 
: UniformContinuous (pkg.compare pkg')
-/
theorem uniformContinuous_compareEquiv_symm : UniformContinuous (pkg.compareEquiv pkg').symm :=
  pkg'.uniformContinuous_compare pkg


open scoped Topology

/-Let `f : α → γ` be a continuous function between a uniform space `α` and a regular topological
space `γ`, and let `pkg, pkg'` be two abstract completions of `α`. Then
if for every point `a : pkg` the filter `f.map (coe⁻¹ (𝓝 a))` obtained by pushing forward with `f`
the preimage in `α` of `𝓝 a` tends to `𝓝 (f.extend a : β)`, then the comparison map
between `pkg` and `pkg'` composed with the extension of `f` to `pkg`` coincides with the
extension of `f` to `pkg'`. The situation is described in the following diagram, where the
two diagonal arrows are the extensions of `f` to the two different completions `pkg` and `pkg'`;
the statement of `compare_comp_eq_compare` is the commutativity of the right triangle.

```
`α^`=`pkg` ≅ `α^'`=`pkg'`   *here `≅` is `compare`*
  ∧     \        /
  |      \      /
  |       \    /
  |        V  ∨
 α ---f---> γ
```
-/
/-
**AbstractCompletion.compare_comp_eq_compare** 是 Mathlib 中的一个定理，位于命名空间 `Abstract
Completion`。
形式化陈述：compare_comp_eq_compare (γ : Type uγ) [TopologicalSpace γ] [T3Space γ] {f 
: α -> γ} (cont_f : Continuous f) : letI
参数：γ : Type uγ；cont_f : Continuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AbstractCompletion.isDenseInducing`：isDenseInducing : IsDenseInducing ι
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsDenseInducing.extend.congr_simp`：∀ {α : Type u_1} {β : Type u_2} {γ : 
Type u_3} [inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] {i i_1 : α →
 β}   (e_i : i = i_1) […
· 使用定理 `AbstractCompletion.compare_coe`：compare_coe (a : α) : pkg.compare pkg' (
pkg.coe a) = pkg'.coe a
· 使用定理 `IsDenseInducing.extend_eq`：extend_eq [T2Space γ] (di : IsDenseInducing i
) {f : α -> γ} (hf : Continuous f) (a : α) : di.extend f (i a) = f a
· 使用定理 `T25Space.t2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T25Space
 X], T2Space X
· 使用定理 `T3Space.t25Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T3Space 
X], T25Space X
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsDenseInducing.extend_unique`：extend_unique [T2Space γ] {f : α -> γ} {g
 : β -> γ} (di : IsDenseInducing i) (hf : forall x, g (i x) = f x) (hg : Continu
ous g) : di.extend …
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `IsDenseInducing.continuous_extend`：continuous_extend [T3Space γ] {f : α 
-> γ} (di : IsDenseInducing i) (hf : forall b, exists c, Tendsto f (comap i (𝓝 b
)) (𝓝 c)) : Continuous …
· 使用定理 `UniformContinuous.continuous`：UniformContinuous.continuous (hf : Uniform
Continuous f) : Continuous f
· 使用定理 `AbstractCompletion.uniformContinuous_compare`：uniformContinuous_compare 
: UniformContinuous (pkg.compare pkg')

--- 原说明 ---
Let `f : α → γ` be a continuous function between a uniform space `α` and a regul
ar topological
space `γ`, and let `pkg, pkg'` be two abstract completions of `α`. Then
if for every point `a : pkg` the filter `f.map (coe⁻¹ (𝓝 a))` obtained by pushin
g forward with `f`
the preimage in `α` of `𝓝 a` tends to `𝓝 (f.extend a : β)`, then the comparison 
map
between `pkg` and `pkg'` composed with the extension of `f` to `pkg`` coincides 
with the
extension of `f` to `pkg'`. The situation is described in the following diagram,
 where the
two diagonal arrows are the extensions of `f` to the two different completions `
pkg` and `pkg'`;
the statement of `compare_comp_eq_compare` is the commutativity of the right tri
angle.

```
`α^`=`pkg` ≅ `α^'`=`pkg'`   *here `≅` is `compare`*
  ∧     \        /
  |      \      /
  |       \    /
  |        V  ∨
 α ---f---> γ
```
-/
theorem compare_comp_eq_compare (γ : Type uγ) [TopologicalSpace γ]
    [T3Space γ] {f : α → γ} (cont_f : Continuous f) :
    letI := pkg.uniformStruct.toTopologicalSpace
    letI := pkg'.uniformStruct.toTopologicalSpace
    (∀ a : pkg.space,
      Filter.Tendsto f (Filter.comap pkg.coe (𝓝 a)) (𝓝 ((pkg.isDenseInducing.extend f) a))) →
      pkg.isDenseInducing.extend f ∘ pkg'.compare pkg = pkg'.isDenseInducing.extend f := by
  intro h
  have (x : α) : (pkg.isDenseInducing.extend f ∘ pkg'.compare pkg) (pkg'.coe x) = f x := by
    simp only [Function.comp_apply, compare_coe, IsDenseInducing.extend_eq _ cont_f]
  apply (IsDenseInducing.extend_unique (AbstractCompletion.isDenseInducing _) this
    (Continuous.comp _ (uniformContinuous_compare pkg' pkg).continuous)).symm
  apply IsDenseInducing.continuous_extend
  exact fun a ↦ ⟨(pkg.isDenseInducing.extend f) a, h a⟩

end Compare

section Prod

variable (pkg' : AbstractCompletion.{vβ} β)

local notation "hatβ" => pkg'.space

local notation "ι'" => pkg'.coe

/-- Products of completions -/
/-
**AbstractCompletion.prod** 是 Mathlib 中的一个定义，位于命名空间 `AbstractCompletion`。
形式化陈述：{α : Type uα} →   [inst : UniformSpace α] →     AbstractCompletion.{vα, uα
} α →       {β : Type uβ} →         [inst_1 : UniformSpace β] → AbstractCompleti
on.{vβ, uβ} β → AbstractCompletion.{max vβ vα, max uβ uα} (α × β)
参数：α × β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Products of completions
-/
protected def prod : AbstractCompletion (α × β) where
  space := hatα × hatβ
  coe p := ⟨ι p.1, ι' p.2⟩
  uniformStruct := inferInstance
  complete := inferInstance
  separation := inferInstance
  isUniformInducing := IsUniformInducing.prod pkg.isUniformInducing pkg'.isUniformInducing
  dense := pkg.dense.prodMap pkg'.dense

end Prod

section Extension₂

variable (pkg' : AbstractCompletion.{vβ} β)

local notation "hatβ" => pkg'.space

local notation "ι'" => pkg'.coe

variable {γ : Type uγ} [UniformSpace γ]

open Function

/-- Extend two variable map to completions. -/
/-
**AbstractCompletion.extend** 是 Mathlib 中的一个定义，位于命名空间 `AbstractCompletion`。
形式化陈述：{α : Type uα} →   [inst : UniformSpace α] →     (pkg : AbstractCompletion.
{vα, uα} α) → {β : Type uβ} → [UniformSpace β] → (α → β) → pkg.space → β
参数：pkg : AbstractCompletion.{vα, uα} α；α → β。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AbstractCompletion.isDenseInducing`：isDenseInducing : IsDenseInducing ι
· 使用定理 `AbstractCompletion.dense`：∀ {α : Type u} [inst : UniformSpace α] (self :
 AbstractCompletion.{v, u} α), DenseRange self.coe

--- 原说明 ---
Extend two variable map to completions.
-/
protected def extend₂ (f : α → β → γ) : hatα → hatβ → γ :=
  curry <| (pkg.prod pkg').extend (uncurry f)

section T0Space

variable [T0Space γ] {f : α → β → γ}

/-
**AbstractCompletion.extension** 是 Mathlib 中的一个定理，位于命名空间 `AbstractCompletion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem extension₂_coe_coe (hf : UniformContinuous <| uncurry f) (a : α) (b : β) :
    pkg.extend₂ pkg' f (ι a) (ι' b) = f a b :=
  show (pkg.prod pkg').extend (uncurry f) ((pkg.prod pkg').coe (a, b)) = uncurry f (a, b) from
    (pkg.prod pkg').extend_coe hf _

end T0Space

variable {f : α → β → γ}
variable [CompleteSpace γ] (f)

set_option backward.isDefEq.respectTransparency false in
@[fun_prop]
/-
**AbstractCompletion.uniformContinuous_extension** 是 Mathlib 中的一个定理，位于命名空间 `Abst
ractCompletion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem uniformContinuous_extension₂ : UniformContinuous₂ (pkg.extend₂ pkg' f) := by
  rw [uniformContinuous₂_def, AbstractCompletion.extend₂, uncurry_curry]
  apply uniformContinuous_extend

end Extension₂

section Map₂

variable (pkg' : AbstractCompletion β)

local notation "hatβ" => pkg'.space

local notation "ι'" => pkg'.coe

variable {γ : Type uγ} [UniformSpace γ] (pkg'' : AbstractCompletion.{vγ} γ)

local notation "hatγ" => pkg''.space

local notation "ι''" => pkg''.coe

local notation f " ∘₂ " g => bicompr f g

/-- Lift two variable maps to completions. -/
/-
**AbstractCompletion.map** 是 Mathlib 中的一个定义，位于命名空间 `AbstractCompletion`。
形式化陈述：{α : Type uα} →   [inst : UniformSpace α] →     (pkg : AbstractCompletion.
{vα, uα} α) →       {β : Type uβ} →         [inst_1 : UniformSpace β] → (pkg' : 
AbstractCompletion.{vβ, uβ} β) → (α → β) → pkg.space → pkg'.space
参数：pkg : AbstractCompletion.{vα, uα} α；pkg' : AbstractCompletion.{vβ, uβ} β；α → 
β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lift two variable maps to completions.
-/
protected def map₂ (f : α → β → γ) : hatα → hatβ → hatγ :=
  pkg.extend₂ pkg' (pkg''.coe ∘₂ f)

@[fun_prop]
/-
**AbstractCompletion.uniformContinuous_map** 是 Mathlib 中的一个定理，位于命名空间 `AbstractCo
mpletion`。
形式化陈述：uniformContinuous_map : UniformContinuous (map f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AbstractCompletion.uniformContinuous_extend`：uniformContinuous_extend : 
UniformContinuous (pkg.extend f)
· 使用定理 `AbstractCompletion.complete`：∀ {α : Type u} [inst : UniformSpace α] (sel
f : AbstractCompletion.{v, u} α), CompleteSpace self.space
-/
theorem uniformContinuous_map₂ (f : α → β → γ) : UniformContinuous₂ (pkg.map₂ pkg' pkg'' f) :=
  AbstractCompletion.uniformContinuous_extension₂ pkg pkg' _
/-
**AbstractCompletion.continuous_map** 是 Mathlib 中的一个定理，位于命名空间 `AbstractCompletio
n`。
形式化陈述：continuous_map : Continuous (map f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AbstractCompletion.continuous_extend`：continuous_extend : Continuous (pk
g.extend f)
· 使用定理 `AbstractCompletion.complete`：∀ {α : Type u} [inst : UniformSpace α] (sel
f : AbstractCompletion.{v, u} α), CompleteSpace self.space
-/
theorem continuous_map₂ {δ} [TopologicalSpace δ] {f : α → β → γ} {a : δ → hatα} {b : δ → hatβ}
    (ha : Continuous a) (hb : Continuous b) :
    Continuous fun d : δ => pkg.map₂ pkg' pkg'' f (a d) (b d) :=
  (pkg.uniformContinuous_map₂ pkg' pkg'' f).continuous.comp₂ ha hb
/-
**AbstractCompletion.map** 是 Mathlib 中的一个定义，位于命名空间 `AbstractCompletion`。
形式化陈述：{α : Type uα} →   [inst : UniformSpace α] →     (pkg : AbstractCompletion.
{vα, uα} α) →       {β : Type uβ} →         [inst_1 : UniformSpace β] → (pkg' : 
AbstractCompletion.{vβ, uβ} β) → (α → β) → pkg.space → pkg'.space
参数：pkg : AbstractCompletion.{vα, uα} α；pkg' : AbstractCompletion.{vβ, uβ} β；α → 
β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map₂_coe_coe (a : α) (b : β) (f : α → β → γ) (hf : UniformContinuous₂ f) :
    pkg.map₂ pkg' pkg'' f (ι a) (ι' b) = ι'' (f a b) :=
  pkg.extension₂_coe_coe (f := pkg''.coe ∘₂ f) pkg' (pkg''.uniformContinuous_coe.comp hf) a b

end Map₂

end AbstractCompletion

