/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Patrick Massot
-/
module

public import Mathlib.Algebra.Group.Submonoid.BigOperators
public import Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.Algebra.Module.Basic
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Separation.Hausdorff

/-!
# The topological support of a function

In this file we define the topological support of a function `f`, `tsupport f`, as the closure of
the support of `f`.

Furthermore, we say that `f` has compact support if the topological support of `f` is compact.

## Main definitions

* `mulTSupport` & `tsupport`
* `HasCompactMulSupport` & `HasCompactSupport`

## TODO

The definitions have been put in the root namespace following many other topological definitions,
like `Embedding`. Since then, `Embedding` was renamed to `Topology.IsEmbedding`, so it might be
worth reconsidering namespacing the definitions here.
-/

@[expose] public section


open Function Set Filter Topology

variable {X α α' β γ δ M R : Type*}

section One

variable [One α] [TopologicalSpace X]

/-- The topological support of a function is the closure of its support, i.e. the closure of the
set of all elements where the function is not equal to 1. -/
@[to_additive /-- The topological support of a function is the closure of its support. i.e. the
closure of the set of all elements where the function is nonzero. -/]
/-
**mulTSupport** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：mulTSupport (f : X -> α) : Set X
参数：f : X -> α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def mulTSupport (f : X → α) : Set X := closure (mulSupport f)

@[to_additive]
/-
**subset_mulTSupport** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：subset_mulTSupport (f : X -> α) : mulSupport f subseteq mulTSupport f
参数：f : X -> α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
-/
theorem subset_mulTSupport (f : X → α) : mulSupport f ⊆ mulTSupport f :=
  subset_closure

@[to_additive]
/-
**isClosed_mulTSupport** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClosed_mulTSupport (f : X -> α) : IsClosed (mulTSupport f)
参数：f : X -> α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
-/
theorem isClosed_mulTSupport (f : X → α) : IsClosed (mulTSupport f) :=
  isClosed_closure

@[to_additive]
/-
**mulTSupport_eq_empty_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mulTSupport_eq_empty_iff {f : X -> α} : mulTSupport f = ∅ ↔ f = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mulTSupport.eq_1`：∀ {X : Type u_1} {α : Type u_2} [inst : One α] [inst_1
 : TopologicalSpace X] (f : X → α),   mulTSupport f = closure (Function.mulSuppo
rt f)
· 使用定理 `closure_empty_iff`：closure_empty_iff (s : Set X) : closure s = ∅ ↔ s = ∅
· 使用引理 `Function.mulSupport_eq_empty_iff`：mulSupport_eq_empty_iff : mulSupport f
 = ∅ ↔ f = 1
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mulTSupport_eq_empty_iff {f : X → α} : mulTSupport f = ∅ ↔ f = 1 := by
  rw [mulTSupport, closure_empty_iff, mulSupport_eq_empty_iff]

@[to_additive (attr := simp)]
/-
**mulTSupport_fun_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mulTSupport_fun_one : mulTSupport (fun _ => 1 : X -> α) = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mulTSupport.eq_1`：∀ {X : Type u_1} {α : Type u_2} [inst : One α] [inst_1
 : TopologicalSpace X] (f : X → α),   mulTSupport f = closure (Function.mulSuppo
rt f)
· 使用引理 `Function.mulSupport_fun_one`：mulSupport_fun_one : mulSupport (fun _ => 1
 : ι -> M) = ∅
· 使用定理 `closure_empty`：closure_empty : closure (∅ : Set X) = ∅
-/
theorem mulTSupport_fun_one : mulTSupport (fun _ ↦ 1 : X → α) = ∅ := by
  rw [mulTSupport, mulSupport_fun_one, closure_empty]

@[to_additive (attr := simp)]
/-
**mulTSupport_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mulTSupport_one : mulTSupport (1 : X -> α) = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mulTSupport.eq_1`：∀ {X : Type u_1} {α : Type u_2} [inst : One α] [inst_1
 : TopologicalSpace X] (f : X → α),   mulTSupport f = closure (Function.mulSuppo
rt f)
· 使用引理 `Function.mulSupport_one`：mulSupport_one : mulSupport (1 : ι -> M) = ∅
· 使用定理 `closure_empty`：closure_empty : closure (∅ : Set X) = ∅
-/
theorem mulTSupport_one : mulTSupport (1 : X → α) = ∅ := by
  rw [mulTSupport, mulSupport_one, closure_empty]

@[to_additive]
/-
**mulTSupport_binop_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mulTSupport_binop_subset [One β] [One γ] (op : α -> β -> γ) (op1 : op 1 1 
= 1) (f : X -> α) (g : X -> β) : mulTSupport (fun x => op (f x) (g x)) subseteq 
mulTSupport f union mulTSupport g
参数：op : α -> β -> γ；op1 : op 1 1 = 1；f : X -> α；g : X -> β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `closure_mono`：closure_mono (h : s subseteq t) : closure s subseteq closu
re t
· 使用引理 `Function.mulSupport_binop_subset`：mulSupport_binop_subset (op : M -> N -
> P) (op1 : op 1 1 = 1) (f : ι -> M) (g : ι -> N) : mulSupport (fun x => op (f x
) (g x)) subseteq mulS…
· 使用定理 `Eq.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorder
 α] {a b : α}, a = b → a ⊆ b
· 使用定理 `closure_union`：closure_union : closure (s union t) = closure s union clo
sure t
-/
theorem mulTSupport_binop_subset [One β] [One γ] (op : α → β → γ)
    (op1 : op 1 1 = 1) (f : X → α) (g : X → β) :
    mulTSupport (fun x ↦ op (f x) (g x)) ⊆ mulTSupport f ∪ mulTSupport g :=
  closure_mono (mulSupport_binop_subset op op1 f g) |>.trans closure_union.subset

@[to_additive]
/-
**mulTSupport_comp_subset** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mulTSupport_comp_subset [One β] {g : α -> β} (hg : g 1 = 1) (f : X -> α) :
 mulTSupport (g ∘ f) subseteq mulTSupport f
参数：hg : g 1 = 1；f : X -> α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `closure_mono`：closure_mono (h : s subseteq t) : closure s subseteq closu
re t
· 使用引理 `Function.mulSupport_comp_subset`：mulSupport_comp_subset {g : M -> N} (hg
 : g 1 = 1) (f : ι -> M) : mulSupport (g ∘ f) subseteq mulSupport f
-/
lemma mulTSupport_comp_subset [One β] {g : α → β} (hg : g 1 = 1) (f : X → α) :
    mulTSupport (g ∘ f) ⊆ mulTSupport f :=
  closure_mono (mulSupport_comp_subset hg f)

@[to_additive]
/-
**mulTSupport_subset_comp** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mulTSupport_subset_comp [One β] {g : α -> β} (hg : forall {x}, g x = 1 -> 
x = 1) (f : X -> α) : mulTSupport f subseteq mulTSupport (g ∘ f)
参数：hg : forall {x}, g x = 1 -> x = 1；f : X -> α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `closure_mono`：closure_mono (h : s subseteq t) : closure s subseteq closu
re t
· 使用引理 `Function.mulSupport_subset_comp`：mulSupport_subset_comp {g : M -> N} (hg
 : forall {x}, g x = 1 -> x = 1) (f : ι -> M) : mulSupport f subseteq mulSupport
 (g ∘ f)
-/
lemma mulTSupport_subset_comp [One β] {g : α → β} (hg : ∀ {x}, g x = 1 → x = 1) (f : X → α) :
    mulTSupport f ⊆ mulTSupport (g ∘ f) :=
  closure_mono (mulSupport_subset_comp hg f)

@[to_additive]
/-
**mulTSupport_comp_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mulTSupport_comp_eq [One β] {g : α -> β} (hg : forall {x}, g x = 1 ↔ x = 1
) (f : X -> α) : mulTSupport (g ∘ f) = mulTSupport f
参数：hg : forall {x}, g x = 1 ↔ x = 1；f : X -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mulTSupport.eq_1`：∀ {X : Type u_1} {α : Type u_2} [inst : One α] [inst_1
 : TopologicalSpace X] (f : X → α),   mulTSupport f = closure (Function.mulSuppo
rt f)
· 使用引理 `Function.mulSupport_comp_eq`：mulSupport_comp_eq (g : M -> N) (hg : foral
l {x}, g x = 1 ↔ x = 1) (f : ι -> M) : mulSupport (g ∘ f) = mulSupport f
-/
lemma mulTSupport_comp_eq [One β] {g : α → β} (hg : ∀ {x}, g x = 1 ↔ x = 1) (f : X → α) :
    mulTSupport (g ∘ f) = mulTSupport f := by
  rw [mulTSupport, mulTSupport, mulSupport_comp_eq g hg]

@[to_additive]
/-
**mulTSupport_comp_eq_of_range_subset** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mulTSupport_comp_eq_of_range_subset [One β] {g : α -> β} {f : X -> α} (hg 
: forall {x}, x in range f -> (g x = 1 ↔ x = 1)) : mulTSupport (g ∘ f) = mulTSup
port f
参数：hg : forall {x}, x in range f -> (g x = 1 ↔ x = 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mulTSupport.eq_1`：∀ {X : Type u_1} {α : Type u_2} [inst : One α] [inst_1
 : TopologicalSpace X] (f : X → α),   mulTSupport f = closure (Function.mulSuppo
rt f)
· 使用引理 `Function.mulSupport_comp_eq_of_range_subset`：mulSupport_comp_eq_of_range
_subset {g : M -> N} {f : ι -> M} (hg : forall {x}, x in range f -> (g x = 1 ↔ x
 = 1)) : mulSupport (g ∘ f) = mul…
-/
lemma mulTSupport_comp_eq_of_range_subset [One β] {g : α → β} {f : X → α}
    (hg : ∀ {x}, x ∈ range f → (g x = 1 ↔ x = 1)) :
    mulTSupport (g ∘ f) = mulTSupport f := by
  rw [mulTSupport, mulTSupport, mulSupport_comp_eq_of_range_subset hg]

@[to_additive]
/-
**mulTSupport_comp_subset_preimage** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mulTSupport_comp_subset_preimage {Y : Type*} [TopologicalSpace Y] (g : Y -
> α) {f : X -> Y} (hf : Continuous f) : mulTSupport (g ∘ f) subseteq f ⁻¹' mulTS
upport g
参数：g : Y -> α；hf : Continuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mulTSupport.eq_1`：∀ {X : Type u_1} {α : Type u_2} [inst : One α] [inst_1
 : TopologicalSpace X] (f : X → α),   mulTSupport f = closure (Function.mulSuppo
rt f)
· 使用引理 `Function.mulSupport_comp_eq_preimage`：mulSupport_comp_eq_preimage (g : κ
 -> M) (f : ι -> κ) : mulSupport (g ∘ f) = f ⁻¹' mulSupport g
· 使用定理 `Continuous.closure_preimage_subset`：Continuous.closure_preimage_subset (
hf : Continuous f) (t : Set Y) : closure (f ⁻¹' t) subseteq f ⁻¹' closure t
-/
lemma mulTSupport_comp_subset_preimage {Y : Type*} [TopologicalSpace Y] (g : Y → α) {f : X → Y}
    (hf : Continuous f) :
    mulTSupport (g ∘ f) ⊆ f ⁻¹' mulTSupport g := by
  rw [mulTSupport, mulTSupport, mulSupport_comp_eq_preimage]
  exact hf.closure_preimage_subset _

@[to_additive]
/-
**mulTSupport_comp_eq_preimage** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mulTSupport_comp_eq_preimage {Y : Type*} [TopologicalSpace Y] (g : Y -> α)
 (f : X ≃ₜ Y) : mulTSupport (g ∘ f) = f ⁻¹' mulTSupport g
参数：g : Y -> α；f : X ≃ₜ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mulTSupport.eq_1`：∀ {X : Type u_1} {α : Type u_2} [inst : One α] [inst_1
 : TopologicalSpace X] (f : X → α),   mulTSupport f = closure (Function.mulSuppo
rt f)
· 使用引理 `Function.mulSupport_comp_eq_preimage`：mulSupport_comp_eq_preimage (g : κ
 -> M) (f : ι -> κ) : mulSupport (g ∘ f) = f ⁻¹' mulSupport g
· 使用定理 `Homeomorph.preimage_closure`：preimage_closure (h : X ≃ₜ Y) (s : Set Y) :
 h ⁻¹' closure s = closure (h ⁻¹' s)
-/
lemma mulTSupport_comp_eq_preimage {Y : Type*} [TopologicalSpace Y] (g : Y → α) (f : X ≃ₜ Y) :
    mulTSupport (g ∘ f) = f ⁻¹' mulTSupport g := by
  rw [mulTSupport, mulTSupport, mulSupport_comp_eq_preimage, Homeomorph.preimage_closure]

@[to_additive]
/-
**image_eq_one_of_notMem_mulTSupport** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：image_eq_one_of_notMem_mulTSupport {f : X -> α} {x : X} (hx : x ∉ mulTSupp
ort f) : f x = 1
参数：hx : x ∉ mulTSupport f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Function.mulSupport_subset_iff'`：mulSupport_subset_iff' : mulSupport f s
ubseteq s ↔ forall x ∉ s, f x = 1
· 使用定理 `subset_mulTSupport`：subset_mulTSupport (f : X -> α) : mulSupport f subse
teq mulTSupport f
-/
theorem image_eq_one_of_notMem_mulTSupport {f : X → α} {x : X} (hx : x ∉ mulTSupport f) : f x = 1 :=
  mulSupport_subset_iff'.mp (subset_mulTSupport f) x hx

@[to_additive]
/-
**range_subset_insert_image_mulTSupport** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：range_subset_insert_image_mulTSupport (f : X -> α) : range f subseteq inse
rt 1 (f '' mulTSupport f)
参数：f : X -> α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Set.insert_subset_insert`：insert_subset_insert (h : s subseteq t) : inse
rt a s subseteq insert a t
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `subset_mulTSupport`：subset_mulTSupport (f : X -> α) : mulSupport f subse
teq mulTSupport f
· 使用引理 `Function.range_subset_insert_image_mulSupport`：range_subset_insert_image
_mulSupport (f : ι -> M) : range f subseteq insert 1 (f '' mulSupport f)
-/
theorem range_subset_insert_image_mulTSupport (f : X → α) :
    range f ⊆ insert 1 (f '' mulTSupport f) := by
  grw [← subset_mulTSupport f]; exact range_subset_insert_image_mulSupport f

@[to_additive]
/-
**range_eq_image_mulTSupport_or** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：range_eq_image_mulTSupport_or (f : X -> α) : range f = f '' mulTSupport f 
∨ range f = insert 1 (f '' mulTSupport f)
参数：f : X -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WCovBy.eq_or_eq`：WCovBy.eq_or_eq (h : a ⩿ b) (h2 : a <= c) (h3 : c <= b)
 : c = a ∨ c = b
· 使用定理 `Set.wcovBy_insert`：∀ {α : Type u_1} (x : α) (s : Set α), s ⩿ insert x s
· 使用定理 `Set.image_subset_range`：image_subset_range (f : α -> β) (s) : f '' s sub
seteq range f
· 使用定理 `range_subset_insert_image_mulTSupport`：range_subset_insert_image_mulTSup
port (f : X -> α) : range f subseteq insert 1 (f '' mulTSupport f)
-/
theorem range_eq_image_mulTSupport_or (f : X → α) :
    range f = f '' mulTSupport f ∨ range f = insert 1 (f '' mulTSupport f) :=
  (wcovBy_insert _ _).eq_or_eq (image_subset_range _ _) (range_subset_insert_image_mulTSupport f)
/-
**tsupport_mul_subset_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tsupport_mul_subset_left {α : Type*} [MulZeroClass α] {f g : X -> α} : (ts
upport fun x => f x * g x) subseteq tsupport f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `closure_mono`：closure_mono (h : s subseteq t) : closure s subseteq closu
re t
· 使用引理 `Function.support_mul_subset_left`：support_mul_subset_left (f g : ι -> M₀
) : support (fun x => f x * g x) subseteq support f
-/
theorem tsupport_mul_subset_left {α : Type*} [MulZeroClass α] {f g : X → α} :
    (tsupport fun x => f x * g x) ⊆ tsupport f :=
  closure_mono (support_mul_subset_left _ _)
/-
**tsupport_mul_subset_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tsupport_mul_subset_right {α : Type*} [MulZeroClass α] {f g : X -> α} : (t
support fun x => f x * g x) subseteq tsupport g
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `closure_mono`：closure_mono (h : s subseteq t) : closure s subseteq closu
re t
· 使用引理 `Function.support_mul_subset_right`：support_mul_subset_right (f g : ι -> 
M₀) : support (fun x => f x * g x) subseteq support g
-/
theorem tsupport_mul_subset_right {α : Type*} [MulZeroClass α] {f g : X → α} :
    (tsupport fun x => f x * g x) ⊆ tsupport g :=
  closure_mono (support_mul_subset_right _ _)

end One

section Operations

variable [TopologicalSpace X]

@[to_additive (attr := simp)]
/-
**mulTSupport_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mulTSupport_mul [MulOneClass α] (f g : X -> α) : (mulTSupport fun x => f x
 * g x) subseteq mulTSupport f union mulTSupport g
参数：f g : X -> α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mulTSupport_binop_subset`：mulTSupport_binop_subset [One β] [One γ] (op :
 α -> β -> γ) (op1 : op 1 1 = 1) (f : X -> α) (g : X -> β) : mulTSupport (fun x 
=> op (f x) (g…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mulTSupport_mul [MulOneClass α] (f g : X → α) :
    (mulTSupport fun x ↦ f x * g x) ⊆ mulTSupport f ∪ mulTSupport g :=
  mulTSupport_binop_subset (· * ·) (by simp) f g

@[to_additive]
/-
**mulTSupport_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mulTSupport_pow [Monoid α] (f : X -> α) (n : Nat) : (mulTSupport fun x => 
f x ^ n) subseteq mulTSupport f
参数：f : X -> α；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `closure_mono`：closure_mono (h : s subseteq t) : closure s subseteq closu
re t
· 使用定理 `Function.mulSupport_pow`：mulSupport_pow [Monoid M] (f : α -> M) (n : Nat
) : (mulSupport fun x => f x ^ n) subseteq mulSupport f
-/
theorem mulTSupport_pow [Monoid α] (f : X → α) (n : ℕ) :
    (mulTSupport fun x => f x ^ n) ⊆ mulTSupport f :=
  closure_mono <| mulSupport_pow f n

@[to_additive (attr := simp)]
/-
**mulTSupport_fun_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mulTSupport_fun_inv [DivisionMonoid α] (f : X -> α) : (mulTSupport fun x =
> (f x)⁻¹) = mulTSupport f
参数：f : X -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.mulSupport_fun_inv`：mulSupport_fun_inv : (mulSupport fun x => (
f x)⁻¹) = mulSupport f
-/
theorem mulTSupport_fun_inv [DivisionMonoid α] (f : X → α) :
    (mulTSupport fun x => (f x)⁻¹) = mulTSupport f :=
  congrArg closure <| mulSupport_fun_inv f

@[to_additive (attr := simp)]
/-
**mulTSupport_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mulTSupport_inv [DivisionMonoid α] (f : X -> α) : mulTSupport f⁻¹ = mulTSu
pport f
参数：f : X -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mulTSupport_fun_inv`：mulTSupport_fun_inv [DivisionMonoid α] (f : X -> α)
 : (mulTSupport fun x => (f x)⁻¹) = mulTSupport f
-/
theorem mulTSupport_inv [DivisionMonoid α] (f : X → α) :
    mulTSupport f⁻¹ = mulTSupport f :=
  mulTSupport_fun_inv f

@[to_additive]
/-
**mulTSupport_mul_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mulTSupport_mul_inv [DivisionMonoid α] (f g : X -> α) : (mulTSupport fun x
 => f x * (g x)⁻¹) subseteq mulTSupport f union mulTSupport g
参数：f g : X -> α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mulTSupport_binop_subset`：mulTSupport_binop_subset [One β] [One γ] (op :
 α -> β -> γ) (op1 : op 1 1 = 1) (f : X -> α) (g : X -> β) : mulTSupport (fun x 
=> op (f x) (g…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mulTSupport_mul_inv [DivisionMonoid α] (f g : X → α) :
    (mulTSupport fun x => f x * (g x)⁻¹) ⊆ mulTSupport f ∪ mulTSupport g :=
  mulTSupport_binop_subset (· * ·⁻¹) (by simp) f g

@[to_additive]
/-
**mulTSupport_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mulTSupport_div [DivisionMonoid α] (f g : X -> α) : (mulTSupport fun x => 
f x / g x) subseteq mulTSupport f union mulTSupport g
参数：f g : X -> α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mulTSupport_binop_subset`：mulTSupport_binop_subset [One β] [One γ] (op :
 α -> β -> γ) (op1 : op 1 1 = 1) (f : X -> α) (g : X -> β) : mulTSupport (fun x 
=> op (f x) (g…
· 使用定理 `one_div_one`：one_div_one : (1 : G) / 1 = 1
-/
theorem mulTSupport_div [DivisionMonoid α] (f g : X → α) :
    (mulTSupport fun x => f x / g x) ⊆ mulTSupport f ∪ mulTSupport g :=
  mulTSupport_binop_subset (· / ·) one_div_one f g
/-
**tsupport_smul_subset_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tsupport_smul_subset_left {M α} [Zero M] [Zero α] [SMulWithZero M α] (f : 
X -> M) (g : X -> α) : (tsupport fun x => f x • g x) subseteq tsupport f
参数：f : X -> M；g : X -> α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `closure_mono`：closure_mono (h : s subseteq t) : closure s subseteq closu
re t
· 使用引理 `Function.support_smul_subset_left`：support_smul_subset_left [Zero R] [Ze
ro M] [SMulWithZero R M] (f : α -> R) (g : α -> M) : support (f • g) subseteq su
pport f
-/
theorem tsupport_smul_subset_left {M α} [Zero M] [Zero α] [SMulWithZero M α]
    (f : X → M) (g : X → α) : (tsupport fun x => f x • g x) ⊆ tsupport f :=
  closure_mono <| support_smul_subset_left f g
/-
**tsupport_smul_subset_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tsupport_smul_subset_right {M α} [Zero α] [SMulZeroClass M α] (f : X -> M)
 (g : X -> α) : (tsupport fun x => f x • g x) subseteq tsupport g
参数：f : X -> M；g : X -> α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `closure_mono`：closure_mono (h : s subseteq t) : closure s subseteq closu
re t
· 使用引理 `Function.support_smul_subset_right`：support_smul_subset_right [Zero M] [
SMulZeroClass R M] (f : α -> R) (g : α -> M) : support (f • g) subseteq support 
g
-/
theorem tsupport_smul_subset_right {M α} [Zero α] [SMulZeroClass M α]
    (f : X → M) (g : X → α) : (tsupport fun x => f x • g x) ⊆ tsupport g :=
  closure_mono <| support_smul_subset_right f g

end Operations

section

variable [TopologicalSpace α]
variable [One β]
variable {f : α → β} {x : α}

@[to_additive]
/-
**notMem_mulTSupport_iff_eventuallyEq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：notMem_mulTSupport_iff_eventuallyEq : x ∉ mulTSupport f ↔ f =ᶠ[𝓝 x] 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem notMem_mulTSupport_iff_eventuallyEq : x ∉ mulTSupport f ↔ f =ᶠ[𝓝 x] 1 := by
  simp_rw [mulTSupport, mem_closure_iff_nhds, not_forall, not_nonempty_iff_eq_empty, exists_prop,
    ← disjoint_iff_inter_eq_empty, disjoint_mulSupport_iff, eventuallyEq_iff_exists_mem]

@[to_additive]
/-
**continuous_of_mulTSupport** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_of_mulTSupport [TopologicalSpace β] {f : α -> β} (hf : forall x
 in mulTSupport f, ContinuousAt f x) : Continuous f
参数：hf : forall x in mulTSupport f, ContinuousAt f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `ContinuousAt.congr`：ContinuousAt.congr {g : X -> Y} (hf : ContinuousAt f
 x) (h : f =ᶠ[𝓝 x] g) : ContinuousAt g x
· 使用定理 `continuousAt_const`：continuousAt_const : ContinuousAt (fun _ : X => y) x
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `notMem_mulTSupport_iff_eventuallyEq`：notMem_mulTSupport_iff_eventuallyEq
 : x ∉ mulTSupport f ↔ f =ᶠ[𝓝 x] 1
-/
theorem continuous_of_mulTSupport [TopologicalSpace β] {f : α → β}
    (hf : ∀ x ∈ mulTSupport f, ContinuousAt f x) : Continuous f :=
  continuous_iff_continuousAt.2 fun x => (em _).elim (hf x) fun hx =>
    (@continuousAt_const _ _ _ _ _ 1).congr (notMem_mulTSupport_iff_eventuallyEq.mp hx).symm

@[to_additive]
/-
**ContinuousOn.continuous_of_mulTSupport_subset** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContinuousOn.continuous_of_mulTSupport_subset [TopologicalSpace β] {f : α 
-> β} {s : Set α} (hs : ContinuousOn f s) (h's : IsOpen s) (h''s : mulTSupport f
 subseteq s) : Continuous f
参数：hs : ContinuousOn f s；h's : IsOpen s；h''s : mulTSupport f subseteq s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_of_mulTSupport`：continuous_of_mulTSupport [TopologicalSpace β
] {f : α -> β} (hf : forall x in mulTSupport f, ContinuousAt f x) : Continuous f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsOpen.continuousOn_iff`：IsOpen.continuousOn_iff (hs : IsOpen s) : Conti
nuousOn f s ↔ forall ⦃a⦄, a in s -> ContinuousAt f a
-/
lemma ContinuousOn.continuous_of_mulTSupport_subset [TopologicalSpace β] {f : α → β}
    {s : Set α} (hs : ContinuousOn f s) (h's : IsOpen s) (h''s : mulTSupport f ⊆ s) :
    Continuous f :=
  continuous_of_mulTSupport fun _ hx ↦ h's.continuousOn_iff.mp hs <| h''s hx

end

/-! ## Functions with compact support -/
section CompactSupport

variable [TopologicalSpace α] [TopologicalSpace α'] [One β] [One γ] [One δ]
  {g : β → γ} {f : α → β} {f₂ : α → γ} {m : β → γ → δ}

/-- A function `f` *has compact multiplicative support* or is *compactly supported* if the closure
of the multiplicative support of `f` is compact. In a T₂ space this is equivalent to `f` being equal
to `1` outside a compact set. -/
@[to_additive /-- A function `f` *has compact support* or is *compactly supported* if the closure of
the support of `f` is compact. In a T₂ space this is equivalent to `f` being equal to `0` outside a
compact set. -/]
/-
**HasCompactMulSupport** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：HasCompactMulSupport (f : α -> β) : Prop
参数：f : α -> β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def HasCompactMulSupport (f : α → β) : Prop :=
  IsCompact (mulTSupport f)

@[to_additive]
/-
**hasCompactMulSupport_def** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasCompactMulSupport_def : HasCompactMulSupport f ↔ IsCompact (closure (mu
lSupport f))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem hasCompactMulSupport_def : HasCompactMulSupport f ↔ IsCompact (closure (mulSupport f)) := by
  rfl

@[to_additive]
/-
**exists_compact_iff_hasCompactMulSupport** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_compact_iff_hasCompactMulSupport [R1Space α] : (exists K : Set α, I
sCompact K ∧ forall x, x ∉ K -> f x = 1) ↔ HasCompactMulSupport f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem exists_compact_iff_hasCompactMulSupport [R1Space α] :
    (∃ K : Set α, IsCompact K ∧ ∀ x, x ∉ K → f x = 1) ↔ HasCompactMulSupport f := by
  simp_rw [← notMem_mulSupport, ← mem_compl_iff, ← subset_def, compl_subset_compl,
    hasCompactMulSupport_def, exists_isCompact_superset_iff]

namespace HasCompactMulSupport

variable {K : Set α}

@[to_additive]
/-
**HasCompactMulSupport.intro** 是 Mathlib 中的一个定理，位于命名空间 `HasCompactMulSupport`。
形式化陈述：intro [R1Space α] (hK : IsCompact K) (hfK : forall x, x ∉ K -> f x = 1) : 
HasCompactMulSupport f
参数：hK : IsCompact K；hfK : forall x, x ∉ K -> f x = 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `exists_compact_iff_hasCompactMulSupport`：exists_compact_iff_hasCompactMu
lSupport [R1Space α] : (exists K : Set α, IsCompact K ∧ forall x, x ∉ K -> f x =
 1) ↔ HasCompactMulSupport f
-/
theorem intro [R1Space α] (hK : IsCompact K) (hfK : ∀ x, x ∉ K → f x = 1) :
    HasCompactMulSupport f :=
  exists_compact_iff_hasCompactMulSupport.mp ⟨K, hK, hfK⟩

@[to_additive]
/-
**HasCompactMulSupport.intro'** 是 Mathlib 中的一个定理，位于命名空间 `HasCompactMulSupport`。
形式化陈述：intro' (hK : IsCompact K) (h'K : IsClosed K) (hfK : forall x, x ∉ K -> f x
 = 1) : HasCompactMulSupport f
参数：hK : IsCompact K；h'K : IsClosed K；hfK : forall x, x ∉ K -> f x = 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x
· 使用定理 `closure_mono`：closure_mono (h : s subseteq t) : closure s subseteq closu
re t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Function.mulSupport_subset_iff'`：mulSupport_subset_iff' : mulSupport f s
ubseteq s ↔ forall x ∉ s, f x = 1
· 使用定理 `IsCompact.of_isClosed_subset`：IsCompact.of_isClosed_subset (hs : IsCompa
ct s) (ht : IsClosed t) (h : t subseteq s) : IsCompact t
· 使用定理 `isClosed_mulTSupport`：isClosed_mulTSupport (f : X -> α) : IsClosed (mulT
Support f)
-/
theorem intro' (hK : IsCompact K) (h'K : IsClosed K) (hfK : ∀ x, x ∉ K → f x = 1) :
    HasCompactMulSupport f := by
  have : mulTSupport f ⊆ K := by
    rw [← h'K.closure_eq]
    apply closure_mono (mulSupport_subset_iff'.2 hfK)
  exact IsCompact.of_isClosed_subset hK (isClosed_mulTSupport f) this

@[to_additive]
/-
**HasCompactMulSupport.of_mulSupport_subset_isCompact** 是 Mathlib 中的一个定理，位于命名空间 
`HasCompactMulSupport`。
形式化陈述：of_mulSupport_subset_isCompact [R1Space α] (hK : IsCompact K) (h : mulSupp
ort f subseteq K) : HasCompactMulSupport f
参数：hK : IsCompact K；h : mulSupport f subseteq K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.closure_of_subset`：IsCompact.closure_of_subset {s K : Set X} (
hK : IsCompact K) (h : s subseteq K) : IsCompact (closure s)
-/
theorem of_mulSupport_subset_isCompact [R1Space α] (hK : IsCompact K) (h : mulSupport f ⊆ K) :
    HasCompactMulSupport f :=
  hK.closure_of_subset h

@[to_additive]
/-
**HasCompactMulSupport.isCompact** 是 Mathlib 中的一个定理，位于命名空间 `HasCompactMulSupport
`。
形式化陈述：isCompact (hf : HasCompactMulSupport f) : IsCompact (mulTSupport f)
参数：hf : HasCompactMulSupport f。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isCompact (hf : HasCompactMulSupport f) : IsCompact (mulTSupport f) := hf

@[to_additive]
/-
**HasCompactMulSupport._root_.hasCompactMulSupport_iff_eventuallyEq** 是 Mathlib 
中的一个定理，位于命名空间 `HasCompactMulSupport`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.hasCompactMulSupport_iff_eventuallyEq :
    HasCompactMulSupport f ↔ f =ᶠ[coclosedCompact α] 1 :=
  mem_coclosedCompact_iff.symm

@[to_additive]
/-
**HasCompactMulSupport._root_.isCompact_range_of_mulSupport_subset_isCompact** 是
 Mathlib 中的一个定理，位于命名空间 `HasCompactMulSupport`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.isCompact_range_of_mulSupport_subset_isCompact [TopologicalSpace β]
    (hf : Continuous f) (hk : IsCompact K) (h'f : mulSupport f ⊆ K) :
    IsCompact (range f) := by
  rcases range_eq_image_or_of_mulSupport_subset h'f with h2 | h2 <;> rw [h2]
  exacts [hk.image hf, (hk.image hf).insert 1]

@[to_additive]
/-
**HasCompactMulSupport.isCompact_range** 是 Mathlib 中的一个定理，位于命名空间 `HasCompactMulS
upport`。
形式化陈述：isCompact_range [TopologicalSpace β] (h : HasCompactMulSupport f) (hf : Co
ntinuous f) : IsCompact (range f)
参数：h : HasCompactMulSupport f；hf : Continuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isCompact_range_of_mulSupport_subset_isCompact`：∀ {α : Type u_2} {β : Ty
pe u_4} [inst : TopologicalSpace α] [inst_1 : One β] {f : α → β} {K : Set α}   [
inst_2 : TopologicalSpace β], Contin…
· 使用定理 `subset_mulTSupport`：subset_mulTSupport (f : X -> α) : mulSupport f subse
teq mulTSupport f
-/
theorem isCompact_range [TopologicalSpace β] (h : HasCompactMulSupport f)
    (hf : Continuous f) : IsCompact (range f) :=
  isCompact_range_of_mulSupport_subset_isCompact hf h (subset_mulTSupport f)

@[to_additive]
/-
**HasCompactMulSupport.mono'** 是 Mathlib 中的一个定理，位于命名空间 `HasCompactMulSupport`。
形式化陈述：mono' {f' : α -> γ} (hf : HasCompactMulSupport f) (hff' : mulSupport f' su
bseteq mulTSupport f) : HasCompactMulSupport f'
参数：hf : HasCompactMulSupport f；hff' : mulSupport f' subseteq mulTSupport f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.of_isClosed_subset`：IsCompact.of_isClosed_subset (hs : IsCompa
ct s) (ht : IsClosed t) (h : t subseteq s) : IsCompact t
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用定理 `closure_minimal`：closure_minimal (h₁ : s subseteq t) (h₂ : IsClosed t) :
 closure s subseteq t
-/
theorem mono' {f' : α → γ} (hf : HasCompactMulSupport f) (hff' : mulSupport f' ⊆ mulTSupport f) :
    HasCompactMulSupport f' :=
  IsCompact.of_isClosed_subset hf isClosed_closure <| closure_minimal hff' isClosed_closure

@[to_additive]
/-
**HasCompactMulSupport.mono** 是 Mathlib 中的一个定理，位于命名空间 `HasCompactMulSupport`。
形式化陈述：mono {f' : α -> γ} (hf : HasCompactMulSupport f) (hff' : mulSupport f' sub
seteq mulSupport f) : HasCompactMulSupport f'
参数：hf : HasCompactMulSupport f；hff' : mulSupport f' subseteq mulSupport f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasCompactMulSupport.mono'`：mono' {f' : α -> γ} (hf : HasCompactMulSuppo
rt f) (hff' : mulSupport f' subseteq mulTSupport f) : HasCompactMulSupport f'
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
-/
theorem mono {f' : α → γ} (hf : HasCompactMulSupport f) (hff' : mulSupport f' ⊆ mulSupport f) :
    HasCompactMulSupport f' :=
  hf.mono' <| hff'.trans subset_closure

@[to_additive]
/-
**HasCompactMulSupport.comp_left** 是 Mathlib 中的一个定理，位于命名空间 `HasCompactMulSupport
`。
形式化陈述：comp_left (hf : HasCompactMulSupport f) (hg : g 1 = 1) : HasCompactMulSupp
ort (g ∘ f)
参数：hf : HasCompactMulSupport f；hg : g 1 = 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasCompactMulSupport.mono`：mono {f' : α -> γ} (hf : HasCompactMulSupport
 f) (hff' : mulSupport f' subseteq mulSupport f) : HasCompactMulSupport f'
· 使用引理 `Function.mulSupport_comp_subset`：mulSupport_comp_subset {g : M -> N} (hg
 : g 1 = 1) (f : ι -> M) : mulSupport (g ∘ f) subseteq mulSupport f
-/
theorem comp_left (hf : HasCompactMulSupport f) (hg : g 1 = 1) :
    HasCompactMulSupport (g ∘ f) :=
  hf.mono <| mulSupport_comp_subset hg f

@[to_additive]
/-
**HasCompactMulSupport._root_.hasCompactMulSupport_comp_left** 是 Mathlib 中的一个定理，
位于命名空间 `HasCompactMulSupport`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.hasCompactMulSupport_comp_left (hg : ∀ {x}, g x = 1 ↔ x = 1) :
    HasCompactMulSupport (g ∘ f) ↔ HasCompactMulSupport f := by
  simp_rw [hasCompactMulSupport_def, mulSupport_comp_eq g (@hg) f]

@[to_additive]
/-
**HasCompactMulSupport.comp_isClosedEmbedding** 是 Mathlib 中的一个定理，位于命名空间 `HasComp
actMulSupport`。
形式化陈述：comp_isClosedEmbedding (hf : HasCompactMulSupport f) {g : α' -> α} (hg : I
sClosedEmbedding g) : HasCompactMulSupport (f ∘ g)
参数：hf : HasCompactMulSupport f；hg : IsClosedEmbedding g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `hasCompactMulSupport_def`：hasCompactMulSupport_def : HasCompactMulSuppor
t f ↔ IsCompact (closure (mulSupport f))
· 使用引理 `Function.mulSupport_comp_eq_preimage`：mulSupport_comp_eq_preimage (g : κ
 -> M) (f : ι -> κ) : mulSupport (g ∘ f) = f ⁻¹' mulSupport g
· 使用定理 `IsCompact.of_isClosed_subset`：IsCompact.of_isClosed_subset (hs : IsCompa
ct s) (ht : IsClosed t) (h : t subseteq s) : IsCompact t
· 使用定理 `Topology.IsClosedEmbedding.isCompact_preimage`：Topology.IsClosedEmbeddin
g.isCompact_preimage (hf : IsClosedEmbedding f) {K : Set Y} (hK : IsCompact K) :
 IsCompact (f ⁻¹' K)
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用定理 `Topology.IsEmbedding.closure_eq_preimage_closure_image`：∀ {X : Type u_1}
 {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpa
ce Y],   Topology.IsEmbedding f → ∀ (s : Set…
· 使用定理 `Topology.IsClosedEmbedding.isEmbedding`：∀ {X : Type u_1} {Y : Type u_2} 
{f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topolog
y.IsClosedEmbedding f → Topo…
· 使用定理 `Set.preimage_mono`：preimage_mono {s t : Set β} (h : s subseteq t) : f ⁻¹
' s subseteq f ⁻¹' t
· 使用定理 `closure_mono`：closure_mono (h : s subseteq t) : closure s subseteq closu
re t
· 使用定理 `Set.image_preimage_subset`：image_preimage_subset (f : α -> β) (s : Set β
) : f '' f ⁻¹' s subseteq s
-/
theorem comp_isClosedEmbedding (hf : HasCompactMulSupport f) {g : α' → α}
    (hg : IsClosedEmbedding g) : HasCompactMulSupport (f ∘ g) := by
  rw [hasCompactMulSupport_def, Function.mulSupport_comp_eq_preimage]
  refine IsCompact.of_isClosed_subset (hg.isCompact_preimage hf) isClosed_closure ?_
  rw [hg.isEmbedding.closure_eq_preimage_closure_image]
  exact preimage_mono (closure_mono <| image_preimage_subset _ _)

@[to_additive]
/-
**HasCompactMulSupport.comp** 是 Mathlib 中的一个定理，位于命名空间 `HasCompactMulSupport`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp₂_left (hf : HasCompactMulSupport f)
    (hf₂ : HasCompactMulSupport f₂) (hm : m 1 1 = 1) :
    HasCompactMulSupport fun x => m (f x) (f₂ x) := by
  rw [hasCompactMulSupport_iff_eventuallyEq] at hf hf₂ ⊢
  filter_upwards [hf, hf₂] with x hx hx₂
  simp_rw [hx, hx₂, Pi.one_apply, hm]

@[to_additive]
/-
**HasCompactMulSupport.isCompact_preimage** 是 Mathlib 中的一个引理，位于命名空间 `HasCompactM
ulSupport`。
形式化陈述：isCompact_preimage [TopologicalSpace β] {K : Set β} (h'f : HasCompactMulSu
pport f) (hf : Continuous f) (hk : IsClosed K) (h'k : 1 ∉ K) : IsCompact (f ⁻¹' 
K)
参数：h'f : HasCompactMulSupport f；hf : Continuous f；hk : IsClosed K；h'k : 1 ∉ K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.of_isClosed_subset`：IsCompact.of_isClosed_subset (hs : IsCompa
ct s) (ht : IsClosed t) (h : t subseteq s) : IsCompact t
· 使用定理 `IsClosed.preimage`：IsClosed.preimage (hf : Continuous f) {t : Set Y} (h 
: IsClosed t) : IsClosed (f ⁻¹' t)
· 使用定理 `subset_mulTSupport`：subset_mulTSupport (f : X -> α) : mulSupport f subse
teq mulTSupport f
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
-/
lemma isCompact_preimage [TopologicalSpace β] {K : Set β}
    (h'f : HasCompactMulSupport f) (hf : Continuous f) (hk : IsClosed K) (h'k : 1 ∉ K) :
    IsCompact (f ⁻¹' K) := by
  apply IsCompact.of_isClosed_subset h'f (hk.preimage hf) (fun x hx ↦ ?_)
  apply subset_mulTSupport
  aesop

variable [T2Space α']

section

variable (hf : HasCompactMulSupport f) {g : α → α'} (cont : Continuous g)
include hf cont

@[to_additive]
/-
**HasCompactMulSupport.mulTSupport_extend_one_subset** 是 Mathlib 中的一个定理，位于命名空间 `
HasCompactMulSupport`。
形式化陈述：mulTSupport_extend_one_subset : mulTSupport (g.extend f 1) subseteq g '' m
ulTSupport f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsClosed.closure_subset_iff`：IsClosed.closure_subset_iff (h₁ : IsClosed 
t) : closure s subseteq t ↔ s subseteq t
· 使用定理 `IsCompact.isClosed`：IsCompact.isClosed [T2Space X] {s : Set X} (hs : IsC
ompact s) : IsClosed s
· 使用定理 `IsCompact.image`：IsCompact.image {f : X -> Y} (hs : IsCompact s) (hf : C
ontinuous f) : IsCompact (f '' s)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `Function.mulSupport_extend_one_subset`：mulSupport_extend_one_subset {f :
 ι -> κ} {g : ι -> N} : mulSupport (f.extend g 1) subseteq f '' mulSupport g
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
-/
theorem mulTSupport_extend_one_subset :
    mulTSupport (g.extend f 1) ⊆ g '' mulTSupport f :=
  (hf.image cont).isClosed.closure_subset_iff.mpr <|
    mulSupport_extend_one_subset.trans (image_mono subset_closure)

@[to_additive]
/-
**HasCompactMulSupport.extend_one** 是 Mathlib 中的一个定理，位于命名空间 `HasCompactMulSuppor
t`。
形式化陈述：extend_one : HasCompactMulSupport (g.extend f 1)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasCompactMulSupport.of_mulSupport_subset_isCompact`：of_mulSupport_subse
t_isCompact [R1Space α] (hK : IsCompact K) (h : mulSupport f subseteq K) : HasCo
mpactMulSupport f
· 使用定理 `T2Space.r1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], R1Space X
· 使用定理 `IsCompact.image`：IsCompact.image {f : X -> Y} (hs : IsCompact s) (hf : C
ontinuous f) : IsCompact (f '' s)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `HasCompactMulSupport.mulTSupport_extend_one_subset`：mulTSupport_extend_o
ne_subset : mulTSupport (g.extend f 1) subseteq g '' mulTSupport f
-/
theorem extend_one : HasCompactMulSupport (g.extend f 1) :=
  HasCompactMulSupport.of_mulSupport_subset_isCompact (hf.image cont)
    (subset_closure.trans <| hf.mulTSupport_extend_one_subset cont)

@[to_additive]
/-
**HasCompactMulSupport.mulTSupport_extend_one** 是 Mathlib 中的一个定理，位于命名空间 `HasComp
actMulSupport`。
形式化陈述：mulTSupport_extend_one (inj : g.Injective) : mulTSupport (g.extend f 1) = 
g '' mulTSupport f
参数：inj : g.Injective。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `HasCompactMulSupport.mulTSupport_extend_one_subset`：mulTSupport_extend_o
ne_subset : mulTSupport (g.extend f 1) subseteq g '' mulTSupport f
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `image_closure_subset_closure_image`：image_closure_subset_closure_image (
h : Continuous f) : f '' closure s subseteq closure (f '' s)
· 使用定理 `closure_mono`：closure_mono (h : s subseteq t) : closure s subseteq closu
re t
· 使用定理 `Eq.superset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preord
er α] {a b : α}, a = b → b ⊆ a
· 使用引理 `Function.mulSupport_extend_one`：mulSupport_extend_one {f : ι -> κ} {g : 
ι -> N} (hf : f.Injective) : mulSupport (f.extend g 1) = f '' mulSupport g
-/
theorem mulTSupport_extend_one (inj : g.Injective) :
    mulTSupport (g.extend f 1) = g '' mulTSupport f :=
  (hf.mulTSupport_extend_one_subset cont).antisymm <|
    (image_closure_subset_closure_image cont).trans
      (closure_mono (mulSupport_extend_one inj).superset)

end

@[to_additive]
/-
**HasCompactMulSupport.continuous_extend_one** 是 Mathlib 中的一个定理，位于命名空间 `HasCompa
ctMulSupport`。
形式化陈述：continuous_extend_one [TopologicalSpace β] {U : Set α'} (hU : IsOpen U) {f
 : U -> β} (cont : Continuous f) (supp : HasCompactMulSupport f) : Continuous (S
ubtype.val.extend f 1)
参数：hU : IsOpen U；cont : Continuous f；supp : HasCompactMulSupport f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_of_mulTSupport`：continuous_of_mulTSupport [TopologicalSpace β
] {f : α -> β} (hf : forall x in mulTSupport f, ContinuousAt f x) : Continuous f
· 使用定理 `Subtype.coe_image_subset`：coe_image_subset (s : Set α) (t : Set s) : ((↑
) : s -> α) '' t subseteq s
· 使用定理 `HasCompactMulSupport.mulTSupport_extend_one_subset`：mulTSupport_extend_o
ne_subset : mulTSupport (g.extend f 1) subseteq g '' mulTSupport f
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Topology.IsOpenEmbedding.continuousAt_iff`：∀ {X : Type u_1} {Y : Type u_
2} {Z : Type u_3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 
: TopologicalSpace Y] [inst_2 :…
· 使用定理 `IsOpen.isOpenEmbedding_subtypeVal`：IsOpen.isOpenEmbedding_subtypeVal {s 
: Set X} (hs : IsOpen s) : IsOpenEmbedding ((↑) : s -> X)
· 使用定理 `Function.extend_comp`：extend_comp (hf : Injective f) (g : α -> γ) (e' : 
β -> γ) : extend f g e' ∘ f = g
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
-/
theorem continuous_extend_one [TopologicalSpace β] {U : Set α'} (hU : IsOpen U) {f : U → β}
    (cont : Continuous f) (supp : HasCompactMulSupport f) :
    Continuous (Subtype.val.extend f 1) :=
  continuous_of_mulTSupport fun x h ↦ by
    rw [show x = ↑(⟨x, Subtype.coe_image_subset _ _
      (supp.mulTSupport_extend_one_subset continuous_subtype_val h)⟩ : U) by rfl,
      ← (hU.isOpenEmbedding_subtypeVal).continuousAt_iff, extend_comp Subtype.val_injective]
    exact cont.continuousAt

/-- If `f` has compact multiplicative support, then `f` tends to 1 at infinity. -/
@[to_additive /-- If `f` has compact support, then `f` tends to zero at infinity. -/]
/-
**HasCompactMulSupport.is_one_at_infty** 是 Mathlib 中的一个定理，位于命名空间 `HasCompactMulS
upport`。
形式化陈述：is_one_at_infty {f : α -> γ} [TopologicalSpace γ] (h : HasCompactMulSuppor
t f) : Tendsto f (cocompact α) (𝓝 1)
参数：h : HasCompactMulSupport f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.mem_map`：mem_map : t in map m f ↔ m ⁻¹' t in f
· 使用定理 `Filter.mem_cocompact'`：mem_cocompact' : s in cocompact X ↔ exists t, IsC
ompact t ∧ sᶜ subseteq t
· 使用定理 `HasCompactMulSupport.isCompact`：isCompact (hf : HasCompactMulSupport f) 
: IsCompact (mulTSupport f)
· 使用定理 `Set.compl_subset_comm`：compl_subset_comm : sᶜ subseteq t ↔ tᶜ subseteq s
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
· 使用定理 `image_eq_one_of_notMem_mulTSupport`：image_eq_one_of_notMem_mulTSupport {
f : X -> α} {x : X} (hx : x ∉ mulTSupport f) : f x = 1
· 使用定理 `mem_of_mem_nhds`：mem_of_mem_nhds : s in 𝓝 x -> x in s

--- 原说明 ---
If `f` has compact multiplicative support, then `f` tends to 1 at infinity.
-/
theorem is_one_at_infty {f : α → γ} [TopologicalSpace γ]
    (h : HasCompactMulSupport f) : Tendsto f (cocompact α) (𝓝 1) := by
  intro N hN
  rw [mem_map, mem_cocompact']
  refine ⟨mulTSupport f, h.isCompact, ?_⟩
  rw [compl_subset_comm]
  intro v hv
  rw [mem_preimage, image_eq_one_of_notMem_mulTSupport hv]
  exact mem_of_mem_nhds hN

end HasCompactMulSupport

section Compact

variable [CompactSpace α]

/-- In a compact space `α`, any function has compact support. -/
@[to_additive]
/-
**HasCompactMulSupport.of_compactSpace** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasCompactMulSupport.of_compactSpace (f : α -> γ) : HasCompactMulSupport f
参数：f : α -> γ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.of_isClosed_subset`：IsCompact.of_isClosed_subset (hs : IsCompa
ct s) (ht : IsClosed t) (h : t subseteq s) : IsCompact t
· 使用定理 `isCompact_univ`：isCompact_univ [h : CompactSpace X] : IsCompact (univ : 
Set X)
· 使用定理 `isClosed_mulTSupport`：isClosed_mulTSupport (f : X -> α) : IsClosed (mulT
Support f)
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ

--- 原说明 ---
In a compact space `α`, any function has compact support.
-/
theorem HasCompactMulSupport.of_compactSpace (f : α → γ) :
    HasCompactMulSupport f :=
  IsCompact.of_isClosed_subset isCompact_univ (isClosed_mulTSupport f)
    (Set.subset_univ (mulTSupport f))

end Compact

end CompactSupport

/-! ## Functions with compact support: algebraic operations -/
section CompactSupport2
section Monoid

variable [TopologicalSpace α] [MulOneClass β]
variable {f f' : α → β}

@[to_additive]
/-
**HasCompactMulSupport.mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasCompactMulSupport.mul (hf : HasCompactMulSupport f) (hf' : HasCompactMu
lSupport f') : HasCompactMulSupport (f * f')
参数：hf : HasCompactMulSupport f；hf' : HasCompactMulSupport f'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasCompactMulSupport.comp₂_left`：comp₂_left (hf : HasCompactMulSupport f
) (hf₂ : HasCompactMulSupport f₂) (hm : m 1 1 = 1) : HasCompactMulSupport fun x 
=> m (f x) (f₂ x)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem HasCompactMulSupport.mul (hf : HasCompactMulSupport f) (hf' : HasCompactMulSupport f') :
    HasCompactMulSupport (f * f') := hf.comp₂_left hf' (mul_one 1)

@[to_additive, simp]
/-
**HasCompactMulSupport.one** 是 Mathlib 中的一个定理，位于命名空间 `HasCompactMulSupport`。
形式化陈述：∀ {α : Type u_9} {β : Type u_10} [inst : TopologicalSpace α] [inst_1 : One
 β], HasCompactMulSupport 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mulTSupport_one`：mulTSupport_one : mulTSupport (1 : X -> α) = ∅
-/
protected lemma HasCompactMulSupport.one {α β : Type*} [TopologicalSpace α] [One β] :
    HasCompactMulSupport (1 : α → β) := by
  simp [HasCompactMulSupport]

variable (α β) in
/-- The submonoid of functions `α → β` with compact multiplicative support. -/
@[to_additive /-- The additive submonoid of functions `α → β` with compact support. -/]
/-
**HasCompactMulSupport.submonoid** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：HasCompactMulSupport.submonoid : Submonoid (α -> β) where carrier
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `HasCompactMulSupport.mul`：HasCompactMulSupport.mul (hf : HasCompactMulSu
pport f) (hf' : HasCompactMulSupport f') : HasCompactMulSupport (f * f')

--- 原说明 ---
The submonoid of functions `α → β` with compact multiplicative support.
-/
def HasCompactMulSupport.submonoid : Submonoid (α → β) where
  carrier := {f | HasCompactMulSupport f}
  one_mem' := .one
  mul_mem' := .mul

@[to_additive (attr := simp)]
/-
**HasCompactMulSupport.mem_submonoid_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasCompactMulSupport.mem_submonoid_iff {f : α -> β} : f in HasCompactMulSu
pport.submonoid α β ↔ HasCompactMulSupport f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem HasCompactMulSupport.mem_submonoid_iff {f : α → β} :
    f ∈ HasCompactMulSupport.submonoid α β ↔ HasCompactMulSupport f :=
  Iff.rfl

@[to_additive]
/-
**HasCompactMulSupport.list_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasCompactMulSupport.list_prod {α β : Type*} [TopologicalSpace α] [Monoid 
β] {l : List (α -> β)} (hl : forall f in l, HasCompactMulSupport f) : HasCompact
MulSupport l.prod
参数：α -> β；hl : forall f in l, HasCompactMulSupport f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `list_prod_mem`：list_prod_mem {l : List M} (hl : forall x in l, x in S) :
 l.prod in S
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
-/
theorem HasCompactMulSupport.list_prod {α β : Type*} [TopologicalSpace α] [Monoid β]
    {l : List (α → β)} (hl : ∀ f ∈ l, HasCompactMulSupport f) :
    HasCompactMulSupport l.prod :=
  list_prod_mem (S := HasCompactMulSupport.submonoid α β) hl

end Monoid

section CommMonoid

variable [TopologicalSpace α] [CommMonoid β]

@[to_additive]
/-
**HasCompactMulSupport.multiset_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasCompactMulSupport.multiset_prod (m : Multiset (α -> β)) (hm : forall f 
in m, HasCompactMulSupport f) : HasCompactMulSupport m.prod
参数：m : Multiset (α -> β)；hm : forall f in m, HasCompactMulSupport f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `multiset_prod_mem`：multiset_prod_mem {M} [CommMonoid M] [SetLike B M] [S
ubmonoidClass B M] (m : Multiset M) (hm : forall a in m, a in S) : m.prod in S
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
-/
theorem HasCompactMulSupport.multiset_prod
    (m : Multiset (α → β)) (hm : ∀ f ∈ m, HasCompactMulSupport f) :
    HasCompactMulSupport m.prod :=
  multiset_prod_mem (S := HasCompactMulSupport.submonoid α β) m hm

@[to_additive]
/-
**HasCompactMulSupport.finset_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasCompactMulSupport.finset_prod {ι : Type*} {s : Finset ι} {f : ι -> α ->
 β} (hf : forall i in s, HasCompactMulSupport (f i)) : HasCompactMulSupport (∏ i
 in s, f i)
参数：hf : forall i in s, HasCompactMulSupport (f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `prod_mem`：prod_mem {M : Type*} [CommMonoid M] [SetLike B M] [SubmonoidCl
ass B M] {ι : Type*} {t : Finset ι} {f : ι -> M} (h : forall c in t, f c in S)…
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
-/
theorem HasCompactMulSupport.finset_prod {ι : Type*}
    {s : Finset ι} {f : ι → α → β} (hf : ∀ i ∈ s, HasCompactMulSupport (f i)) :
    HasCompactMulSupport (∏ i ∈ s, f i) :=
  prod_mem (S := HasCompactMulSupport.submonoid α β) hf

end CommMonoid

section DivisionMonoid

@[to_additive]
/-
**HasCompactMulSupport.inv** 是 Mathlib 中的一个定理，位于命名空间 `HasCompactMulSupport`。
形式化陈述：∀ {α : Type u_9} {β : Type u_10} [inst : TopologicalSpace α] [inst_1 : Div
isionMonoid β] {f : α → β},   HasCompactMulSupport f → HasCompactMulSupport f⁻¹
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.mulSupport_inv`：mulSupport_inv : mulSupport f⁻¹ = mulSupport f
-/
protected lemma HasCompactMulSupport.inv {α β : Type*} [TopologicalSpace α] [DivisionMonoid β]
    {f : α → β} (hf : HasCompactMulSupport f) :
    HasCompactMulSupport (f⁻¹) := by
  simpa only [HasCompactMulSupport, mulTSupport, mulSupport_inv] using hf

@[to_additive]
/-
**HasCompactSupport.div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasCompactSupport.div {α β : Type*} [TopologicalSpace α] [DivisionMonoid β
] {f f' : α -> β} (hf : HasCompactMulSupport f) (hf' : HasCompactMulSupport f') 
: HasCompactMulSupport (f / f')
参数：hf : HasCompactMulSupport f；hf' : HasCompactMulSupport f'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasCompactMulSupport.mul`：HasCompactMulSupport.mul (hf : HasCompactMulSu
pport f) (hf' : HasCompactMulSupport f') : HasCompactMulSupport (f * f')
· 使用定理 `HasCompactMulSupport.inv`：∀ {α : Type u_9} {β : Type u_10} [inst : Topol
ogicalSpace α] [inst_1 : DivisionMonoid β] {f : α → β},   HasCompactMulSupport f
 → HasCompactM…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
-/
theorem HasCompactSupport.div {α β : Type*} [TopologicalSpace α] [DivisionMonoid β]
    {f f' : α → β} (hf : HasCompactMulSupport f) (hf' : HasCompactMulSupport f') :
    HasCompactMulSupport (f / f') :=
  div_eq_mul_inv f f' ▸ hf.mul hf'.inv

end DivisionMonoid

section SMulZeroClass

variable [TopologicalSpace α] [Zero M] [SMulZeroClass R M]
variable {f : α → R} {f' : α → M}

/-
**HasCompactSupport.smul_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasCompactSupport.smul_left (hf : HasCompactSupport f') : HasCompactSuppor
t (f • f')
参数：hf : HasCompactSupport f'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `hasCompactSupport_iff_eventuallyEq`：∀ {α : Type u_2} {β : Type u_4} [ins
t : TopologicalSpace α] [inst_1 : Zero β] {f : α → β},   HasCompactSupport f ↔ f
 =ᶠ[Filter.coclosedCompa…
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem HasCompactSupport.smul_left (hf : HasCompactSupport f') : HasCompactSupport (f • f') := by
  rw [hasCompactSupport_iff_eventuallyEq] at hf ⊢
  exact hf.mono fun x hx => by simp_rw [Pi.smul_apply', hx, Pi.zero_apply, smul_zero]

end SMulZeroClass

section SMulWithZero

variable [TopologicalSpace α] [Zero R] [Zero M] [SMulWithZero R M]
variable {f : α → R} {f' : α → M}

/-
**HasCompactSupport.smul_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasCompactSupport.smul_right (hf : HasCompactSupport f) : HasCompactSuppor
t (f • f')
参数：hf : HasCompactSupport f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `hasCompactSupport_iff_eventuallyEq`：∀ {α : Type u_2} {β : Type u_4} [ins
t : TopologicalSpace α] [inst_1 : Zero β] {f : α → β},   HasCompactSupport f ↔ f
 =ᶠ[Filter.coclosedCompa…
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem HasCompactSupport.smul_right (hf : HasCompactSupport f) : HasCompactSupport (f • f') := by
  rw [hasCompactSupport_iff_eventuallyEq] at hf ⊢
  exact hf.mono fun x hx => by simp_rw [Pi.smul_apply', hx, Pi.zero_apply, zero_smul]

end SMulWithZero

section MulZeroClass

variable [TopologicalSpace α] [MulZeroClass β]
variable {f f' : α → β}

/-
**HasCompactSupport.mul_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasCompactSupport.mul_right (hf : HasCompactSupport f) : HasCompactSupport
 (f * f')
参数：hf : HasCompactSupport f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `hasCompactSupport_iff_eventuallyEq`：∀ {α : Type u_2} {β : Type u_4} [ins
t : TopologicalSpace α] [inst_1 : Zero β] {f : α → β},   HasCompactSupport f ↔ f
 =ᶠ[Filter.coclosedCompa…
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem HasCompactSupport.mul_right (hf : HasCompactSupport f) : HasCompactSupport (f * f') := by
  rw [hasCompactSupport_iff_eventuallyEq] at hf ⊢
  exact hf.mono fun x hx => by simp_rw [Pi.mul_apply, hx, Pi.zero_apply, zero_mul]
/-
**HasCompactSupport.mul_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasCompactSupport.mul_left (hf : HasCompactSupport f') : HasCompactSupport
 (f * f')
参数：hf : HasCompactSupport f'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `hasCompactSupport_iff_eventuallyEq`：∀ {α : Type u_2} {β : Type u_4} [ins
t : TopologicalSpace α] [inst_1 : Zero β] {f : α → β},   HasCompactSupport f ↔ f
 =ᶠ[Filter.coclosedCompa…
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem HasCompactSupport.mul_left (hf : HasCompactSupport f') : HasCompactSupport (f * f') := by
  rw [hasCompactSupport_iff_eventuallyEq] at hf ⊢
  exact hf.mono fun x hx => by simp_rw [Pi.mul_apply, hx, Pi.zero_apply, mul_zero]

end MulZeroClass

section OrderedAddGroup

variable [TopologicalSpace α] [AddGroup β] [Lattice β] [AddLeftMono β]

/-
**HasCompactSupport.abs** 是 Mathlib 中的一个定理，位于命名空间 `HasCompactSupport`。
形式化陈述：∀ {α : Type u_2} {β : Type u_4} [inst : TopologicalSpace α] [inst_1 : AddG
roup β] [inst_2 : Lattice β] [AddLeftMono β]   {f : α → β}, HasCompactSupport f 
→ HasCompactSupport |f|
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasCompactSupport.comp_left`：∀ {α : Type u_2} {β : Type u_4} {γ : Type u
_5} [inst : TopologicalSpace α] [inst_1 : Zero β] [inst_2 : Zero γ]   {g : β → γ
} {f : α → β}, Ha…
· 使用定理 `abs_zero`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [Add
LeftMono α], |0| = 0
-/
protected theorem HasCompactSupport.abs {f : α → β} (hf : HasCompactSupport f) :
    HasCompactSupport |f| :=
  hf.comp_left (g := abs) abs_zero

end OrderedAddGroup

end CompactSupport2

section LocallyFinite

variable {ι : Type*} [TopologicalSpace X]

-- TODO: reformulate for any locally finite family of sets
/-- If a family of functions `f` has locally-finite multiplicative support, subordinate to a family
of open sets, then for any point we can find a neighbourhood on which only finitely-many members of
`f` are not equal to 1. -/
@[to_additive /-- If a family of functions `f` has locally-finite support, subordinate to a family
of open sets, then for any point we can find a neighbourhood on which only finitely-many members of
`f` are non-zero. -/]
/-
**LocallyFinite.exists_finset_nhds_mulSupport_subset** 是 Mathlib 中的一个定理，位于命名空间 `
`。
形式化陈述：LocallyFinite.exists_finset_nhds_mulSupport_subset {U : ι -> Set X} [One R
] {f : ι -> X -> R} (hlf : LocallyFinite fun i => mulSupport (f i)) (hso : foral
l i, mulTSupport (f i) subseteq U i) (ho : forall i, IsOpen (U i)) (x : X) : exi
sts (is : Finset ι), exists n, n in 𝓝 x ∧ (n subseteq ⋂ i in is, U i) ∧ forall z
 in n, (mulSupport fun i => f i z) subseteq is
参数：hlf : LocallyFinite fun i => mulSupport (f i)；hso : forall i, mulTSupport (f 
i) subseteq U i；ho : forall i, IsOpen (U i)；x : X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.biInter_finset_mem`：biInter_finset_mem {β : Type v} {s : β -> Set
 α} (is : Finset β) : (⋂ i in is, s i) in f ↔ forall i in is, s i in f
· 使用定理 `IsClosed.compl_mem_nhds`：IsClosed.compl_mem_nhds (hs : IsClosed s) (hx :
 x ∉ s) : sᶜ in 𝓝 x
· 使用定理 `isClosed_mulTSupport`：isClosed_mulTSupport (f : X -> α) : IsClosed (mulT
Support f)
· 使用定理 `Set.notMem_subset`：notMem_subset (h : s subseteq t) : a ∉ t -> a ∉ s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `Set.mem_of_mem_inter_left`：mem_of_mem_inter_left {x : α} {a b : Set α} (
h : x in a inter b) : x in a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.inter_assoc`：inter_assoc (a b c : Set α) : a inter b inter c = a int
er (b inter c)
· 使用定理 `Set.mem_of_mem_inter_right`：mem_of_mem_inter_right {x : α} {a b : Set α}
 (h : x in a inter b) : x in b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.Finite.coe_toFinset`：∀ {α : Type u} {s : Set α} (hs : s.Finite), ↑hs
.toFinset = s
· 使用定理 `Finset.subset_coe_filter_of_subset_forall`：∀ {α : Type u_1} (p : α → Pro
p) [inst : DecidablePred p] (s : Finset α) {t : Set α},   t ⊆ ↑s → (∀ x ∈ t, p x
) → t ⊆ ↑(Finset.filter p s)
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `subset_mulTSupport`：subset_mulTSupport (f : X -> α) : mulSupport f subse
teq mulTSupport f
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
（共 31 条，此处仅展示前 30 条）
-/
theorem LocallyFinite.exists_finset_nhds_mulSupport_subset {U : ι → Set X} [One R] {f : ι → X → R}
    (hlf : LocallyFinite fun i => mulSupport (f i)) (hso : ∀ i, mulTSupport (f i) ⊆ U i)
    (ho : ∀ i, IsOpen (U i)) (x : X) :
    ∃ (is : Finset ι), ∃ n, n ∈ 𝓝 x ∧ (n ⊆ ⋂ i ∈ is, U i) ∧
      ∀ z ∈ n, (mulSupport fun i => f i z) ⊆ is := by
  obtain ⟨n, hn, hnf⟩ := hlf x
  classical
    let is := {i ∈ hnf.toFinset | x ∈ U i}
    let js := {j ∈ hnf.toFinset | x ∉ U j}
    refine
      ⟨is, (n ∩ ⋂ j ∈ js, (mulTSupport (f j))ᶜ) ∩ ⋂ i ∈ is, U i, inter_mem (inter_mem hn ?_) ?_,
        inter_subset_right, fun z hz => ?_⟩
    · exact (biInter_finset_mem js).mpr fun j hj => IsClosed.compl_mem_nhds (isClosed_mulTSupport _)
        (Set.notMem_subset (hso j) (Finset.mem_filter.mp hj).2)
    · exact (biInter_finset_mem is).mpr fun i hi => (ho i).mem_nhds (Finset.mem_filter.mp hi).2
    · have hzn : z ∈ n := by
        rw [inter_assoc] at hz
        exact mem_of_mem_inter_left hz
      replace hz := mem_of_mem_inter_right (mem_of_mem_inter_left hz)
      simp only [js, Finset.mem_filter, Finite.mem_toFinset, mem_ofPred_eq, mem_iInter,
        and_imp] at hz
      suffices (mulSupport fun i => f i z) ⊆ hnf.toFinset by
        refine hnf.toFinset.subset_coe_filter_of_subset_forall _ this fun i hi => ?_
        specialize hz i ⟨z, ⟨hi, hzn⟩⟩
        contrapose hz
        simp [hz, subset_mulTSupport (f i) hi]
      intro i hi
      simp only [Finite.coe_toFinset, mem_ofPred_eq]
      exact ⟨z, ⟨hi, hzn⟩⟩

@[to_additive]
/-
**locallyFinite_mulSupport_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：locallyFinite_mulSupport_iff [One M] {f : ι -> X -> M} : (LocallyFinite fu
n i => mulSupport <| f i) ↔ LocallyFinite fun i => mulTSupport f i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LocallyFinite.closure`：∀ {ι : Type u_1} {X : Type u_4} [inst : Topologic
alSpace X] {f : ι → Set X},   LocallyFinite f → LocallyFinite fun i => closure (
f i)
· 使用定理 `LocallyFinite.subset`：∀ {ι : Type u_1} {X : Type u_4} [inst : Topologica
lSpace X] {f g : ι → Set X},   LocallyFinite f → (∀ (i : ι), g i ⊆ f i) → Locall
yFinite g
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
-/
theorem locallyFinite_mulSupport_iff [One M] {f : ι → X → M} :
    (LocallyFinite fun i ↦ mulSupport <| f i) ↔ LocallyFinite fun i ↦ mulTSupport <| f i :=
  ⟨LocallyFinite.closure, fun H ↦ H.subset fun _ ↦ subset_closure⟩
/-
**LocallyFinite.smul_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LocallyFinite.smul_left [Zero R] [Zero M] [SMulWithZero R M] {s : ι -> X -
> R} (h : LocallyFinite fun i => support <| s i) (f : ι -> X -> M) : LocallyFini
te fun i => support s i • f i
参数：h : LocallyFinite fun i => support <| s i；f : ι -> X -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LocallyFinite.subset`：∀ {ι : Type u_1} {X : Type u_4} [inst : Topologica
lSpace X] {f g : ι → Set X},   LocallyFinite f → (∀ (i : ι), g i ⊆ f i) → Locall
yFinite g
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Pi.smul_apply'`：smul_apply' [forall i, SMul (α i) (β i)] (s : forall i, 
α i) (x : forall i, β i) : (s • x) i = s i • x i
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
-/
theorem LocallyFinite.smul_left [Zero R] [Zero M] [SMulWithZero R M]
    {s : ι → X → R} (h : LocallyFinite fun i ↦ support <| s i) (f : ι → X → M) :
    LocallyFinite fun i ↦ support <| s i • f i :=
  h.subset fun i x ↦ mt <| fun h ↦ by rw [Pi.smul_apply', h, zero_smul]
/-
**LocallyFinite.smul_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LocallyFinite.smul_right [Zero M] [SMulZeroClass R M] {f : ι -> X -> M} (h
 : LocallyFinite fun i => support <| f i) (s : ι -> X -> R) : LocallyFinite fun 
i => support s i • f i
参数：h : LocallyFinite fun i => support <| f i；s : ι -> X -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LocallyFinite.subset`：∀ {ι : Type u_1} {X : Type u_4} [inst : Topologica
lSpace X] {f g : ι → Set X},   LocallyFinite f → (∀ (i : ι), g i ⊆ f i) → Locall
yFinite g
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Pi.smul_apply'`：smul_apply' [forall i, SMul (α i) (β i)] (s : forall i, 
α i) (x : forall i, β i) : (s • x) i = s i • x i
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
-/
theorem LocallyFinite.smul_right [Zero M] [SMulZeroClass R M]
    {f : ι → X → M} (h : LocallyFinite fun i ↦ support <| f i) (s : ι → X → R) :
    LocallyFinite fun i ↦ support <| s i • f i :=
  h.subset fun i x ↦ mt <| fun h ↦ by rw [Pi.smul_apply', h, smul_zero]

end LocallyFinite

section Homeomorph

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

@[to_additive]
/-
**HasCompactMulSupport.comp_homeomorph** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasCompactMulSupport.comp_homeomorph {M} [One M] {f : Y -> M} (hf : HasCom
pactMulSupport f) (φ : X ≃ₜ Y) : HasCompactMulSupport (f ∘ φ)
参数：hf : HasCompactMulSupport f；φ : X ≃ₜ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasCompactMulSupport.comp_isClosedEmbedding`：comp_isClosedEmbedding (hf 
: HasCompactMulSupport f) {g : α' -> α} (hg : IsClosedEmbedding g) : HasCompactM
ulSupport (f ∘ g)
· 使用定理 `Homeomorph.isClosedEmbedding`：isClosedEmbedding (h : X ≃ₜ Y) : IsClosedE
mbedding h
-/
theorem HasCompactMulSupport.comp_homeomorph {M} [One M] {f : Y → M}
    (hf : HasCompactMulSupport f) (φ : X ≃ₜ Y) : HasCompactMulSupport (f ∘ φ) :=
  hf.comp_isClosedEmbedding φ.isClosedEmbedding

end Homeomorph

