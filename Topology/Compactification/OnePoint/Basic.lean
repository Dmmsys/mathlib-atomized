/-
Copyright (c) 2021 Yourong Zang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yourong Zang, Yury Kudryashov
-/
module

public import Mathlib.Data.Fintype.Option
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.WithTopology

/-!
# The one-point compactification

We construct the one-point compactification of an arbitrary topological space `X` and prove some
properties inherited from `X`.

## Main definitions

* `OnePoint`: the one-point compactification, we use coercion for the canonical embedding
  `X → OnePoint X`; when `X` is already compact, the compactification adds an isolated point
  to the space.
* `OnePoint.infty`: the extra point

## Main results

* The topological structure of `OnePoint X`
* The connectedness of `OnePoint X` for a noncompact, preconnected `X`
* `OnePoint X` is `T₀` for a T₀ space `X`
* `OnePoint X` is `T₁` for a T₁ space `X`
* `OnePoint X` is normal if `X` is a locally compact Hausdorff space

## Tags

one point compactification, Alexandroff compactification, compactness
-/

@[expose] public section


open Set Filter Topology

/-!
### Definition and basic properties

In this section we define `OnePoint X` to be the disjoint union of `X` and `∞`, implemented as
`Option X`. Then we restate some lemmas about `Option X` for `OnePoint X`.
-/


variable {X Y : Type*}

/-- The one-point extension of an arbitrary topological space `X` -/
/-
**OnePoint** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：OnePoint (X : Type*)
参数：X : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The one-point extension of an arbitrary topological space `X`
-/
def OnePoint (X : Type*) :=
  Option X

/-- The repr uses the notation from the `OnePoint` locale. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The repr uses the notation from the `OnePoint` locale.
-/
instance [Repr X] : Repr (OnePoint X) :=
  ⟨fun o _ =>
    match o with
    | none => "∞"
    | some a => "↑" ++ repr a⟩

namespace OnePoint

/-- The point at infinity -/
/-
**OnePoint.infty** 是 Mathlib 中的一个定义，位于命名空间 `OnePoint`。
形式化陈述：{X : Type u_1} → OnePoint X
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The point at infinity
-/
@[match_pattern] def infty : OnePoint X := none

@[inherit_doc]
scoped notation "∞" => OnePoint.infty

/-- Coercion from `X` to `OnePoint X`. -/
/-
**OnePoint.some** 是 Mathlib 中的一个定义，位于命名空间 `OnePoint`。
形式化陈述：{X : Type u_1} → X → OnePoint X
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Coercion from `X` to `OnePoint X`.
-/
@[coe, match_pattern] def some : X → OnePoint X := Option.some

@[simp]
/-
**OnePoint.some_eq_iff** 是 Mathlib 中的一个引理，位于命名空间 `OnePoint`。
形式化陈述：some_eq_iff (x₁ x₂ : X) : (some x₁ = some x₂) ↔ (x₁ = x₂)
参数：x₁ x₂ : X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `iff_eq_eq`：iff_eq_eq {a b : Prop} : (a ↔ b) = (a = b)
· 使用定理 `Option.some.injEq`：∀ {α : Type u} (val val_1 : α), (some val = some val_
1) = (val = val_1)

--- 原说明 ---
Coercion from `X` to `OnePoint X`.
-/
lemma some_eq_iff (x₁ x₂ : X) : (some x₁ = some x₂) ↔ (x₁ = x₂) := by
  rw [iff_eq_eq]
  exact Option.some.injEq x₁ x₂
/-
**OnePoint.** 是 Mathlib 中的一个实例，位于命名空间 `OnePoint`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeTC X (OnePoint X) := ⟨some⟩
/-
**OnePoint.** 是 Mathlib 中的一个实例，位于命名空间 `OnePoint`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (OnePoint X) := ⟨∞⟩
/-
**OnePoint.** 是 Mathlib 中的一个实例，位于命名空间 `OnePoint`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsEmpty X] : Subsingleton (OnePoint X) :=
  inferInstanceAs <| Subsingleton (Option X)
/-
**OnePoint.** 是 Mathlib 中的一个引理，位于命名空间 `OnePoint`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected lemma «forall» {p : OnePoint X → Prop} :
    (∀ (x : OnePoint X), p x) ↔ p ∞ ∧ ∀ (x : X), p x :=
  Option.forall
/-
**OnePoint.** 是 Mathlib 中的一个引理，位于命名空间 `OnePoint`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected lemma «exists» {p : OnePoint X → Prop} :
    (∃ x, p x) ↔ p ∞ ∨ ∃ (x : X), p x :=
  Option.exists
/-
**OnePoint.** 是 Mathlib 中的一个实例，位于命名空间 `OnePoint`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Fintype X] : Fintype (OnePoint X) :=
  inferInstanceAs (Fintype (Option X))
/-
**OnePoint.infinite** 是 Mathlib 中的一个实例，位于命名空间 `OnePoint`。
形式化陈述：infinite [Infinite X] : Infinite (OnePoint X)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance infinite [Infinite X] : Infinite (OnePoint X) :=
  inferInstanceAs (Infinite (Option X))
/-
**OnePoint.coe_injective** 是 Mathlib 中的一个定理，位于命名空间 `OnePoint`。
形式化陈述：coe_injective : Function.Injective ((↑) : X -> OnePoint X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Option.some_injective`：some_injective (α : Type*) : Function.Injective (
@some α)
-/
theorem coe_injective : Function.Injective ((↑) : X → OnePoint X) :=
  Option.some_injective X

@[norm_cast]
/-
**OnePoint.coe_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `OnePoint`。
形式化陈述：coe_eq_coe {x y : X} : (x : OnePoint X) = y ↔ x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `OnePoint.coe_injective`：coe_injective : Function.Injective ((↑) : X -> O
nePoint X)
-/
theorem coe_eq_coe {x y : X} : (x : OnePoint X) = y ↔ x = y :=
  coe_injective.eq_iff

@[simp]
/-
**OnePoint.coe_ne_infty** 是 Mathlib 中的一个定理，位于命名空间 `OnePoint`。
形式化陈述：coe_ne_infty (x : X) : (x : OnePoint X) != ∞
参数：x : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_ne_infty (x : X) : (x : OnePoint X) ≠ ∞ :=
  nofun

@[simp]
/-
**OnePoint.infty_ne_coe** 是 Mathlib 中的一个定理，位于命名空间 `OnePoint`。
形式化陈述：infty_ne_coe (x : X) : ∞ != (x : OnePoint X)
参数：x : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem infty_ne_coe (x : X) : ∞ ≠ (x : OnePoint X) :=
  nofun

/-- Recursor for `OnePoint` using the preferred forms `∞` and `↑x`. -/
@[elab_as_elim, induction_eliminator, cases_eliminator]
/-
**OnePoint.rec** 是 Mathlib 中的一个定义，位于命名空间 `OnePoint`。
形式化陈述：{X : Type u_1} → {C : OnePoint X → Sort u_3} → C OnePoint.infty → ((x : X)
 → C ↑x) → (z : OnePoint X) → C z
参数：(x : X) → C ↑x；z : OnePoint X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Recursor for `OnePoint` using the preferred forms `∞` and `↑x`.
-/
protected def rec {C : OnePoint X → Sort*} (infty : C ∞) (coe : ∀ x : X, C x) :
    ∀ z : OnePoint X, C z
  | ∞ => infty
  | (x : X) => coe x

/-- An elimination principle for `OnePoint`. -/
/-
**OnePoint.elim** 是 Mathlib 中的一个定义，位于命名空间 `OnePoint`。
形式化陈述：{X : Type u_1} → {Y : Type u_2} → OnePoint X → Y → (X → Y) → Y
参数：X → Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An elimination principle for `OnePoint`.
-/
@[inline] protected def elim : OnePoint X → Y → (X → Y) → Y := Option.elim
/-
**OnePoint.elim_infty** 是 Mathlib 中的一个定理，位于命名空间 `OnePoint`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} (y : Y) (f : X → Y), OnePoint.infty.elim y
 f = y
参数：y : Y；f : X → Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An elimination principle for `OnePoint`.
-/
@[simp] theorem elim_infty (y : Y) (f : X → Y) : ∞.elim y f = y := rfl
/-
**OnePoint.elim_some** 是 Mathlib 中的一个定理，位于命名空间 `OnePoint`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} (y : Y) (f : X → Y) (x : X), (↑x).elim y f
 = f x
参数：y : Y；f : X → Y；x : X；↑x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An elimination principle for `OnePoint`.
-/
@[simp] theorem elim_some (y : Y) (f : X → Y) (x : X) : (some x).elim y f = f x := rfl
/-
**OnePoint.isCompl_range_coe_infty** 是 Mathlib 中的一个定理，位于命名空间 `OnePoint`。
形式化陈述：isCompl_range_coe_infty : IsCompl (range ((↑) : X -> OnePoint X)) {∞}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.isCompl_range_some_none`：isCompl_range_some_none (α : Type*) : IsCom
pl (range (some : α -> Option α)) {none}

--- 原说明 ---
An elimination principle for `OnePoint`.
-/
theorem isCompl_range_coe_infty : IsCompl (range ((↑) : X → OnePoint X)) {∞} :=
  isCompl_range_some_none X
/-
**OnePoint.range_coe_union_infty** 是 Mathlib 中的一个定理，位于命名空间 `OnePoint`。
形式化陈述：range_coe_union_infty : range ((↑) : X -> OnePoint X) union {∞} = univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.range_some_union_none`：range_some_union_none (α : Type*) : range (so
me : α -> Option α) union {none} = univ
-/
theorem range_coe_union_infty : range ((↑) : X → OnePoint X) ∪ {∞} = univ :=
  range_some_union_none X

@[simp]
/-
**OnePoint.insert_infty_range_coe** 是 Mathlib 中的一个定理，位于命名空间 `OnePoint`。
形式化陈述：insert_infty_range_coe : insert ∞ (range (@some X)) = univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.insert_none_range_some`：insert_none_range_some (α : Type*) : insert 
none (range (some : α -> Option α)) = univ
-/
theorem insert_infty_range_coe : insert ∞ (range (@some X)) = univ :=
  insert_none_range_some _

@[simp]
/-
**OnePoint.compl_range_coe** 是 Mathlib 中的一个定理，位于命名空间 `OnePoint`。
形式化陈述：compl_range_coe : (range ((↑) : X -> OnePoint X))ᶜ = {∞}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.compl_range_some`：compl_range_some (α : Type*) : (range (some : α ->
 Option α))ᶜ = {none}
-/
theorem compl_range_coe : (range ((↑) : X → OnePoint X))ᶜ = {∞} :=
  compl_range_some X
/-
**OnePoint.compl_infty** 是 Mathlib 中的一个定理，位于命名空间 `OnePoint`。
形式化陈述：compl_infty : ({∞}ᶜ : Set (OnePoint X)) = range ((↑) : X -> OnePoint X)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompl.compl_eq`：IsCompl.compl_eq (h : IsCompl a b) : aᶜ = b
· 使用定理 `IsCompl.symm`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Bounded
Order α] {x y : α}, IsCompl x y → IsCompl y x
· 使用定理 `OnePoint.isCompl_range_coe_infty`：isCompl_range_coe_infty : IsCompl (ran
ge ((↑) : X -> OnePoint X)) {∞}
-/
theorem compl_infty : ({∞}ᶜ : Set (OnePoint X)) = range ((↑) : X → OnePoint X) :=
  (@isCompl_range_coe_infty X).symm.compl_eq
/-
**OnePoint.compl_image_coe** 是 Mathlib 中的一个定理，位于命名空间 `OnePoint`。
形式化陈述：compl_image_coe (s : Set X) : ((↑) '' s : Set (OnePoint X))ᶜ = (↑) '' sᶜ u
nion {∞}
参数：s : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Injective.compl_image_eq`：∀ {α : Type u_1} {β : Type u_2} {f : 
α → β}, Function.Injective f → ∀ (s : Set α), (f '' s)ᶜ = f '' sᶜ ∪ (Set.range f
)ᶜ
· 使用定理 `OnePoint.coe_injective`：coe_injective : Function.Injective ((↑) : X -> O
nePoint X)
· 使用定理 `OnePoint.compl_range_coe`：compl_range_coe : (range ((↑) : X -> OnePoint 
X))ᶜ = {∞}
-/
theorem compl_image_coe (s : Set X) : ((↑) '' s : Set (OnePoint X))ᶜ = (↑) '' sᶜ ∪ {∞} := by
  rw [coe_injective.compl_image_eq, compl_range_coe]
/-
**OnePoint.ne_infty_iff_exists** 是 Mathlib 中的一个定理，位于命名空间 `OnePoint`。
形式化陈述：ne_infty_iff_exists {x : OnePoint X} : x != ∞ ↔ exists y : X, (y : OnePoin
t X) = x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem ne_infty_iff_exists {x : OnePoint X} : x ≠ ∞ ↔ ∃ y : X, (y : OnePoint X) = x := by
  induction x using OnePoint.rec <;> simp
/-
**OnePoint.canLift** 是 Mathlib 中的一个实例，位于命名空间 `OnePoint`。
形式化陈述：canLift : CanLift (OnePoint X) X (↑) fun x => x != ∞
该定义给出了一等式。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `WithTop.canLift`：∀ {α : Type u_1}, CanLift (WithTop α) α WithTop.some fu
n r => r ≠ ⊤
-/
instance canLift : CanLift (OnePoint X) X (↑) fun x => x ≠ ∞ :=
  WithTop.canLift
/-
**OnePoint.notMem_range_coe_iff** 是 Mathlib 中的一个定理，位于命名空间 `OnePoint`。
形式化陈述：notMem_range_coe_iff {x : OnePoint X} : x ∉ range some ↔ x = ∞
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.mem_compl_iff`：mem_compl_iff (s : Set α) (x : α) : x in sᶜ ↔ x ∉ s
· 使用定理 `OnePoint.compl_range_coe`：compl_range_coe : (range ((↑) : X -> OnePoint 
X))ᶜ = {∞}
· 使用定理 `Set.mem_singleton_iff`：mem_singleton_iff {a b : α} : a in ({b} : Set α) 
↔ a = b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem notMem_range_coe_iff {x : OnePoint X} : x ∉ range some ↔ x = ∞ := by
  rw [← mem_compl_iff, compl_range_coe, mem_singleton_iff]
/-
**OnePoint.infty_notMem_range_coe** 是 Mathlib 中的一个定理，位于命名空间 `OnePoint`。
形式化陈述：infty_notMem_range_coe : ∞ ∉ range ((↑) : X -> OnePoint X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `OnePoint.notMem_range_coe_iff`：notMem_range_coe_iff {x : OnePoint X} : x
 ∉ range some ↔ x = ∞
-/
theorem infty_notMem_range_coe : ∞ ∉ range ((↑) : X → OnePoint X) :=
  notMem_range_coe_iff.2 rfl
/-
**OnePoint.infty_notMem_image_coe** 是 Mathlib 中的一个定理，位于命名空间 `OnePoint`。
形式化陈述：infty_notMem_image_coe {s : Set X} : ∞ ∉ ((↑) : X -> OnePoint X) '' s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.notMem_subset`：notMem_subset (h : s subseteq t) : a ∉ t -> a ∉ s
· 使用定理 `Set.image_subset_range`：image_subset_range (f : α -> β) (s) : f '' s sub
seteq range f
· 使用定理 `OnePoint.infty_notMem_range_coe`：infty_notMem_range_coe : ∞ ∉ range ((↑)
 : X -> OnePoint X)
-/
theorem infty_notMem_image_coe {s : Set X} : ∞ ∉ ((↑) : X → OnePoint X) '' s :=
  notMem_subset (image_subset_range _ _) infty_notMem_range_coe

@[simp]
/-
**OnePoint.coe_preimage_infty** 是 Mathlib 中的一个定理，位于命名空间 `OnePoint`。
形式化陈述：coe_preimage_infty : ((↑) : X -> OnePoint X) ⁻¹' {∞} = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem coe_preimage_infty : ((↑) : X → OnePoint X) ⁻¹' {∞} = ∅ := by
  ext
  simp

/-- Extend a map `f : X → Y` to a map `OnePoint X → OnePoint Y`
by sending infinity to infinity. -/
/-
**OnePoint.map** 是 Mathlib 中的一个定义，位于命名空间 `OnePoint`。
形式化陈述：{X : Type u_1} → {Y : Type u_2} → (X → Y) → OnePoint X → OnePoint Y
参数：X → Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Extend a map `f : X → Y` to a map `OnePoint X → OnePoint Y`
by sending infinity to infinity.
-/
protected def map (f : X → Y) : OnePoint X → OnePoint Y :=
  Option.map f
/-
**OnePoint.map_infty** 是 Mathlib 中的一个定理，位于命名空间 `OnePoint`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} (f : X → Y), OnePoint.map f OnePoint.infty
 = OnePoint.infty
参数：f : X → Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem map_infty (f : X → Y) : OnePoint.map f ∞ = ∞ := rfl
/-
**OnePoint.map_some** 是 Mathlib 中的一个定理，位于命名空间 `OnePoint`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} (f : X → Y) (x : X), OnePoint.map f ↑x = ↑
(f x)
参数：f : X → Y；x : X；f x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem map_some (f : X → Y) (x : X) : (x : OnePoint X).map f = f x := rfl
/-
**OnePoint.map_id** 是 Mathlib 中的一个定理，位于命名空间 `OnePoint`。
形式化陈述：∀ {X : Type u_1}, OnePoint.map id = id
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Option.map_id`：∀ {α : Type u_1}, Option.map id = id
-/
@[simp] theorem map_id : OnePoint.map (id : X → X) = id := Option.map_id
/-
**OnePoint.map_comp** 是 Mathlib 中的一个定理，位于命名空间 `OnePoint`。
形式化陈述：map_comp {Z : Type*} (f : Y -> Z) (g : X -> Y) : OnePoint.map (f ∘ g) = On
ePoint.map f ∘ OnePoint.map g
参数：f : Y -> Z；g : X -> Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Option.map_comp_map`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} (f :
 α → β) (g : β → γ), Option.map g ∘ Option.map f = Option.map (g ∘ f)
-/
theorem map_comp {Z : Type*} (f : Y → Z) (g : X → Y) :
    OnePoint.map (f ∘ g) = OnePoint.map f ∘ OnePoint.map g :=
  (Option.map_comp_map _ _).symm

/-!
### Topological space structure on `OnePoint X`

We define a topological space structure on `OnePoint X` so that `s` is open if and only if

* `(↑) ⁻¹' s` is open in `X`;
* if `∞ ∈ s`, then `((↑) ⁻¹' s)ᶜ` is compact.

Then we reformulate this definition in a few different ways, and prove that
`(↑) : X → OnePoint X` is an open embedding. If `X` is not a compact space, then we also prove
that `(↑)` has dense range, so it is a dense embedding.
-/


variable [TopologicalSpace X]

/-
**OnePoint.** 是 Mathlib 中的一个实例，位于命名空间 `OnePoint`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : TopologicalSpace (OnePoint X) where
  IsOpen s := (∞ ∈ s → IsCompact (((↑) : X → OnePoint X) ⁻¹' s)ᶜ) ∧
    IsOpen (((↑) : X → OnePoint X) ⁻¹' s)
  isOpen_univ := by simp
  isOpen_inter s t := by
    rintro ⟨hms, hs⟩ ⟨hmt, ht⟩
    refine ⟨?_, hs.inter ht⟩
    rintro ⟨hms', hmt'⟩
    simpa [compl_inter] using (hms hms').union (hmt hmt')
  isOpen_sUnion S ho := by
    suffices IsOpen ((↑) ⁻¹' ⋃₀ S : Set X) by
      refine ⟨?_, this⟩
      rintro ⟨s, hsS : s ∈ S, hs : ∞ ∈ s⟩
      refine IsCompact.of_isClosed_subset ((ho s hsS).1 hs) this.isClosed_compl ?_
      exact compl_subset_compl.mpr (preimage_mono <| subset_sUnion_of_mem hsS)
    rw [preimage_sUnion]
    exact isOpen_biUnion fun s hs => (ho s hs).2

variable {s : Set (OnePoint X)}
/-
**OnePoint.isOpen_def** 是 Mathlib 中的一个定理，位于命名空间 `OnePoint`。
形式化陈述：isOpen_def : IsOpen s ↔ (∞ in s -> IsCompact ((↑) ⁻¹' s : Set X)ᶜ) ∧ IsOpe
n ((↑) ⁻¹' s : Set X)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isOpen_def :
    IsOpen s ↔ (∞ ∈ s → IsCompact ((↑) ⁻¹' s : Set X)ᶜ) ∧ IsOpen ((↑) ⁻¹' s : Set X) :=
  Iff.rfl
/-
**OnePoint.isOpen_iff_of_mem'** 是 Mathlib 中的一个定理，位于命名空间 `OnePoint`。
形式化陈述：isOpen_iff_of_mem' (h : ∞ in s) : IsOpen s ↔ IsCompact ((↑) ⁻¹' s : Set X)
ᶜ ∧ IsOpen ((↑) ⁻¹' s : Set X)
参数：h : ∞ in s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isOpen_iff_of_mem' (h : ∞ ∈ s) :
    IsOpen s ↔ IsCompact ((↑) ⁻¹' s : Set X)ᶜ ∧ IsOpen ((↑) ⁻¹' s : Set X) := by
  simp [isOpen_def, h]
/-
**OnePoint.isOpen_iff_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `OnePoint`。
形式化陈述：isOpen_iff_of_mem (h : ∞ in s) : IsOpen s ↔ IsClosed ((↑) ⁻¹' s : Set X)ᶜ 
∧ IsCompact ((↑) ⁻¹' s : Set X)ᶜ
参数：h : ∞ in s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OnePoint.isOpen_iff_of_mem'`：isOpen_iff_of_mem' (h : ∞ in s) : IsOpen s 
↔ IsCompact ((↑) ⁻¹' s : Set X)ᶜ ∧ IsOpen ((↑) ⁻¹' s : Set X)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isOpen_iff_of_mem (h : ∞ ∈ s) :
    IsOpen s ↔ IsClosed ((↑) ⁻¹' s : Set X)ᶜ ∧ IsCompact ((↑) ⁻¹' s : Set X)ᶜ := by
  simp only [isOpen_iff_of_mem' h, isClosed_compl_iff, and_comm]
/-
**OnePoint.isOpen_iff_of_notMem** 是 Mathlib 中的一个定理，位于命名空间 `OnePoint`。
形式化陈述：isOpen_iff_of_notMem (h : ∞ ∉ s) : IsOpen s ↔ IsOpen ((↑) ⁻¹' s : Set X)
参数：h : ∞ ∉ s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isOpen_iff_of_notMem (h : ∞ ∉ s) : IsOpen s ↔ IsOpen ((↑) ⁻¹' s : Set X) := by
  simp [isOpen_def, h]
/-
**OnePoint.isClosed_iff_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `OnePoint`。
形式化陈述：isClosed_iff_of_mem (h : ∞ in s) : IsClosed s ↔ IsClosed ((↑) ⁻¹' s : Set 
X)
参数：h : ∞ in s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isOpen_compl_iff`：∀ {X : Type u} {s : Set X} [inst : TopologicalSpace X]
, IsOpen sᶜ ↔ IsClosed s
· 使用定理 `OnePoint.isOpen_iff_of_notMem`：isOpen_iff_of_notMem (h : ∞ ∉ s) : IsOpen
 s ↔ IsOpen ((↑) ⁻¹' s : Set X)
· 使用定理 `Set.preimage_compl`：preimage_compl {s : Set β} : f ⁻¹' sᶜ = (f ⁻¹' s)ᶜ
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isClosed_iff_of_mem (h : ∞ ∈ s) : IsClosed s ↔ IsClosed ((↑) ⁻¹' s : Set X) := by
  have : ∞ ∉ sᶜ := fun H => H h
  rw [← isOpen_compl_iff, isOpen_iff_of_notMem this, ← isOpen_compl_iff, preimage_compl]
/-
**OnePoint.isClosed_iff_of_notMem** 是 Mathlib 中的一个定理，位于命名空间 `OnePoint`。
形式化陈述：isClosed_iff_of_notMem (h : ∞ ∉ s) : IsClosed s ↔ IsClosed ((↑) ⁻¹' s : Se
t X) ∧ IsCompact ((↑) ⁻¹' s : Set X)
参数：h : ∞ ∉ s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isOpen_compl_iff`：∀ {X : Type u} {s : Set X} [inst : TopologicalSpace X]
, IsOpen sᶜ ↔ IsClosed s
· 使用定理 `OnePoint.isOpen_iff_of_mem`：isOpen_iff_of_mem (h : ∞ in s) : IsOpen s ↔ 
IsClosed ((↑) ⁻¹' s : Set X)ᶜ ∧ IsCompact ((↑) ⁻¹' s : Set X)ᶜ
· 使用定理 `Set.mem_compl`：mem_compl {s : Set α} {x : α} (h : x ∉ s) : x in sᶜ
· 使用定理 `Set.preimage_compl`：preimage_compl {s : Set β} : f ⁻¹' sᶜ = (f ⁻¹' s)ᶜ
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isClosed_iff_of_notMem (h : ∞ ∉ s) :
    IsClosed s ↔ IsClosed ((↑) ⁻¹' s : Set X) ∧ IsCompact ((↑) ⁻¹' s : Set X) := by
  rw [← isOpen_compl_iff, isOpen_iff_of_mem (mem_compl h), ← preimage_compl, compl_compl]

@[simp]
/-
**OnePoint.isOpen_image_coe** 是 Mathlib 中的一个定理，位于命名空间 `OnePoint`。
形式化陈述：isOpen_image_coe {s : Set X} : IsOpen ((↑) '' s : Set (OnePoint X)) ↔ IsOp
en s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OnePoint.isOpen_iff_of_notMem`：isOpen_iff_of_notMem (h : ∞ ∉ s) : IsOpen
 s ↔ IsOpen ((↑) ⁻¹' s : Set X)
· 使用定理 `OnePoint.infty_notMem_image_coe`：infty_notMem_image_coe {s : Set X} : ∞ 
∉ ((↑) : X -> OnePoint X) '' s
· 使用定理 `Set.preimage_image_eq`：preimage_image_eq {f : α -> β} (s : Set α) (h : I
njective f) : f ⁻¹' f '' s = s
· 使用定理 `OnePoint.coe_injective`：coe_injective : Function.Injective ((↑) : X -> O
nePoint X)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isOpen_image_coe {s : Set X} : IsOpen ((↑) '' s : Set (OnePoint X)) ↔ IsOpen s := by
  rw [isOpen_iff_of_notMem infty_notMem_image_coe, preimage_image_eq _ coe_injective]
/-
**OnePoint.isOpen_compl_image_coe** 是 Mathlib 中的一个定理，位于命名空间 `OnePoint`。
形式化陈述：isOpen_compl_image_coe {s : Set X} : IsOpen ((↑) '' s : Set (OnePoint X))ᶜ
 ↔ IsClosed s ∧ IsCompact s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OnePoint.isOpen_iff_of_mem`：isOpen_iff_of_mem (h : ∞ in s) : IsOpen s ↔ 
IsClosed ((↑) ⁻¹' s : Set X)ᶜ ∧ IsCompact ((↑) ⁻¹' s : Set X)ᶜ
· 使用定理 `OnePoint.infty_notMem_image_coe`：infty_notMem_image_coe {s : Set X} : ∞ 
∉ ((↑) : X -> OnePoint X) '' s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.preimage_compl`：preimage_compl {s : Set β} : f ⁻¹' sᶜ = (f ⁻¹' s)ᶜ
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `Set.preimage_image_eq`：preimage_image_eq {f : α -> β} (s : Set α) (h : I
njective f) : f ⁻¹' f '' s = s
· 使用定理 `OnePoint.coe_injective`：coe_injective : Function.Injective ((↑) : X -> O
nePoint X)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isOpen_compl_image_coe {s : Set X} :
    IsOpen ((↑) '' s : Set (OnePoint X))ᶜ ↔ IsClosed s ∧ IsCompact s := by
  rw [isOpen_iff_of_mem, ← preimage_compl, compl_compl, preimage_image_eq _ coe_injective]
  exact infty_notMem_image_coe

@[simp]
/-
**OnePoint.isClosed_image_coe** 是 Mathlib 中的一个定理，位于命名空间 `OnePoint`。
形式化陈述：isClosed_image_coe {s : Set X} : IsClosed ((↑) '' s : Set (OnePoint X)) ↔ 
IsClosed s ∧ IsCompact s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isOpen_compl_iff`：∀ {X : Type u} {s : Set X} [inst : TopologicalSpace X]
, IsOpen sᶜ ↔ IsClosed s
· 使用定理 `OnePoint.isOpen_compl_image_coe`：isOpen_compl_image_coe {s : Set X} : Is
Open ((↑) '' s : Set (OnePoint X))ᶜ ↔ IsClosed s ∧ IsCompact s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isClosed_image_coe {s : Set X} :
    IsClosed ((↑) '' s : Set (OnePoint X)) ↔ IsClosed s ∧ IsCompact s := by
  rw [← isOpen_compl_iff, isOpen_compl_image_coe]

/-- An open set in `OnePoint X` constructed from a closed compact set in `X` -/
/-
**OnePoint.opensOfCompl** 是 Mathlib 中的一个定义，位于命名空间 `OnePoint`。
形式化陈述：opensOfCompl (s : Set X) (h₁ : IsClosed s) (h₂ : IsCompact s) : Topologica
lSpace.Opens (OnePoint X)
参数：s : Set X；h₁ : IsClosed s；h₂ : IsCompact s。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An open set in `OnePoint X` constructed from a closed compact set in `X`
-/
def opensOfCompl (s : Set X) (h₁ : IsClosed s) (h₂ : IsCompact s) :
    TopologicalSpace.Opens (OnePoint X) :=
  ⟨((↑) '' s)ᶜ, isOpen_compl_image_coe.2 ⟨h₁, h₂⟩⟩
/-
**OnePoint.infty_mem_opensOfCompl** 是 Mathlib 中的一个定理，位于命名空间 `OnePoint`。
形式化陈述：infty_mem_opensOfCompl {s : Set X} (h₁ : IsClosed s) (h₂ : IsCompact s) : 
∞ in opensOfCompl s h₁ h₂
参数：h₁ : IsClosed s；h₂ : IsCompact s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_compl`：mem_compl {s : Set α} {x : α} (h : x ∉ s) : x in sᶜ
· 使用定理 `OnePoint.infty_notMem_image_coe`：infty_notMem_image_coe {s : Set X} : ∞ 
∉ ((↑) : X -> OnePoint X) '' s
-/
theorem infty_mem_opensOfCompl {s : Set X} (h₁ : IsClosed s) (h₂ : IsCompact s) :
    ∞ ∈ opensOfCompl s h₁ h₂ :=
  mem_compl infty_notMem_image_coe

@[continuity]
/-
**OnePoint.continuous_coe** 是 Mathlib 中的一个定理，位于命名空间 `OnePoint`。
形式化陈述：continuous_coe : Continuous ((↑) : X -> OnePoint X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_def`：continuous_def {_ : TopologicalSpace X} {_ : Topological
Space Y} {f : X -> Y} : Continuous f ↔ forall s, IsOpen s -> IsOpen (f ⁻¹' s)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem continuous_coe : Continuous ((↑) : X → OnePoint X) :=
  continuous_def.mpr fun _s hs => hs.right
/-
**OnePoint.isOpenMap_coe** 是 Mathlib 中的一个定理，位于命名空间 `OnePoint`。
形式化陈述：isOpenMap_coe : IsOpenMap ((↑) : X -> OnePoint X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `OnePoint.isOpen_image_coe`：isOpen_image_coe {s : Set X} : IsOpen ((↑) ''
 s : Set (OnePoint X)) ↔ IsOpen s
-/
theorem isOpenMap_coe : IsOpenMap ((↑) : X → OnePoint X) := fun _ => isOpen_image_coe.2
/-
**OnePoint.isOpenEmbedding_coe** 是 Mathlib 中的一个定理，位于命名空间 `OnePoint`。
形式化陈述：isOpenEmbedding_coe : IsOpenEmbedding ((↑) : X -> OnePoint X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap`：∀ {X : Type 
u_1} {Y : Type u_2} {f : X → Y} [inst : TopologicalSpace X] [inst_1 : Topologica
lSpace Y],   Continuous f → Function.Injective f…
· 使用定理 `OnePoint.continuous_coe`：continuous_coe : Continuous ((↑) : X -> OnePoin
t X)
· 使用定理 `OnePoint.coe_injective`：coe_injective : Function.Injective ((↑) : X -> O
nePoint X)
· 使用定理 `OnePoint.isOpenMap_coe`：isOpenMap_coe : IsOpenMap ((↑) : X -> OnePoint X
)
-/
theorem isOpenEmbedding_coe : IsOpenEmbedding ((↑) : X → OnePoint X) :=
  .of_continuous_injective_isOpenMap continuous_coe coe_injective isOpenMap_coe
/-
**OnePoint.isOpen_range_coe** 是 Mathlib 中的一个定理，位于命名空间 `OnePoint`。
形式化陈述：isOpen_range_coe : IsOpen (range ((↑) : X -> OnePoint X))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsOpenEmbedding.isOpen_range`：∀ {X : Type u_1} {Y : Type u_2} [
tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsOpe
nEmbedding f → IsOpen (Set.…
· 使用定理 `OnePoint.isOpenEmbedding_coe`：isOpenEmbedding_coe : IsOpenEmbedding ((↑)
 : X -> OnePoint X)
-/
theorem isOpen_range_coe : IsOpen (range ((↑) : X → OnePoint X)) :=
  isOpenEmbedding_coe.isOpen_range
/-
**OnePoint.isClosed_infty** 是 Mathlib 中的一个定理，位于命名空间 `OnePoint`。
形式化陈述：isClosed_infty : IsClosed ({∞} : Set (OnePoint X))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OnePoint.compl_range_coe`：compl_range_coe : (range ((↑) : X -> OnePoint 
X))ᶜ = {∞}
· 使用定理 `isClosed_compl_iff`：isClosed_compl_iff {s : Set X} : IsClosed sᶜ ↔ IsOpe
n s
· 使用定理 `OnePoint.isOpen_range_coe`：isOpen_range_coe : IsOpen (range ((↑) : X -> 
OnePoint X))
-/
theorem isClosed_infty : IsClosed ({∞} : Set (OnePoint X)) := by
  rw [← compl_range_coe, isClosed_compl_iff]
  exact isOpen_range_coe
/-
**OnePoint.nhds_coe_eq** 是 Mathlib 中的一个定理，位于命名空间 `OnePoint`。
形式化陈述：nhds_coe_eq (x : X) : 𝓝 ↑x = map ((↑) : X -> OnePoint X) (𝓝 x)
参数：x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Topology.IsOpenEmbedding.map_nhds_eq`：∀ {X : Type u_1} {Y : Type u_2} {f
 : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.
IsOpenEmbedding f → ∀ (x :…
· 使用定理 `OnePoint.isOpenEmbedding_coe`：isOpenEmbedding_coe : IsOpenEmbedding ((↑)
 : X -> OnePoint X)
-/
theorem nhds_coe_eq (x : X) : 𝓝 ↑x = map ((↑) : X → OnePoint X) (𝓝 x) :=
  (isOpenEmbedding_coe.map_nhds_eq x).symm
/-
**OnePoint.nhdsWithin_coe_image** 是 Mathlib 中的一个定理，位于命名空间 `OnePoint`。
形式化陈述：nhdsWithin_coe_image (s : Set X) (x : X) : 𝓝[(↑) '' s] (x : OnePoint X) = 
map (↑) (𝓝[s] x)
参数：s : Set X；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Topology.IsEmbedding.map_nhdsWithin_eq`：Topology.IsEmbedding.map_nhdsWit
hin_eq {f : α -> β} (hf : IsEmbedding f) (s : Set α) (x : α) : map f (𝓝[s] x) = 
𝓝[f '' s] f x
· 使用定理 `Topology.IsOpenEmbedding.isEmbedding`：∀ {X : Type u_1} {Y : Type u_2} {f
 : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.
IsOpenEmbedding f → Topolo…
· 使用定理 `OnePoint.isOpenEmbedding_coe`：isOpenEmbedding_coe : IsOpenEmbedding ((↑)
 : X -> OnePoint X)
-/
theorem nhdsWithin_coe_image (s : Set X) (x : X) :
    𝓝[(↑) '' s] (x : OnePoint X) = map (↑) (𝓝[s] x) :=
  (isOpenEmbedding_coe.isEmbedding.map_nhdsWithin_eq _ _).symm
/-
**OnePoint.nhdsWithin_coe** 是 Mathlib 中的一个定理，位于命名空间 `OnePoint`。
形式化陈述：nhdsWithin_coe (s : Set (OnePoint X)) (x : X) : 𝓝[s] ↑x = map (↑) (𝓝[(↑) ⁻
¹' s] x)
参数：s : Set (OnePoint X)；x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Topology.IsOpenEmbedding.map_nhdsWithin_preimage_eq`：Topology.IsOpenEmbe
dding.map_nhdsWithin_preimage_eq {f : α -> β} (hf : IsOpenEmbedding f) (s : Set 
β) (x : α) : map f (𝓝[f ⁻¹' s] x) = 𝓝[s] …
· 使用定理 `OnePoint.isOpenEmbedding_coe`：isOpenEmbedding_coe : IsOpenEmbedding ((↑)
 : X -> OnePoint X)
-/
theorem nhdsWithin_coe (s : Set (OnePoint X)) (x : X) : 𝓝[s] ↑x = map (↑) (𝓝[(↑) ⁻¹' s] x) :=
  (isOpenEmbedding_coe.map_nhdsWithin_preimage_eq _ _).symm
/-
**OnePoint.comap_coe_nhds** 是 Mathlib 中的一个定理，位于命名空间 `OnePoint`。
形式化陈述：comap_coe_nhds (x : X) : comap ((↑) : X -> OnePoint X) (𝓝 x) = 𝓝 x
参数：x : X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Topology.IsInducing.nhds_eq_comap`：nhds_eq_comap (hf : IsInducing f) : f
orall x : X, 𝓝 x = comap f (𝓝 <| f x)
· 使用定理 `Topology.IsOpenEmbedding.isInducing`：∀ {X : Type u_1} {Y : Type u_2} {f 
: X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.I
sOpenEmbedding f → Topolo…
· 使用定理 `OnePoint.isOpenEmbedding_coe`：isOpenEmbedding_coe : IsOpenEmbedding ((↑)
 : X -> OnePoint X)
-/
theorem comap_coe_nhds (x : X) : comap ((↑) : X → OnePoint X) (𝓝 x) = 𝓝 x :=
  (isOpenEmbedding_coe.isInducing.nhds_eq_comap x).symm

/-- If `x` is not an isolated point of `X`, then `x : OnePoint X` is not an isolated point
of `OnePoint X`. -/
/-
**OnePoint.nhdsNE_coe_neBot** 是 Mathlib 中的一个实例，位于命名空间 `OnePoint`。
形式化陈述：nhdsNE_coe_neBot (x : X) [h : NeBot (𝓝[!=] x)] : NeBot (𝓝[!=] (x : OnePoin
t X))
参数：x : X；𝓝[!=] x。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `OnePoint.nhdsWithin_coe`：nhdsWithin_coe (s : Set (OnePoint X)) (x : X) :
 𝓝[s] ↑x = map (↑) (𝓝[(↑) ⁻¹' s] x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.NeBot.map`：∀ {α : Type u_1} {β : Type u_2} {f : Filter α}, f.NeBo
t → ∀ (m : α → β), (Filter.map m f).NeBot

--- 原说明 ---
If `x` is not an isolated point of `X`, then `x : OnePoint X` is not an isolated
 point
of `OnePoint X`.
-/
instance nhdsNE_coe_neBot (x : X) [h : NeBot (𝓝[≠] x)] : NeBot (𝓝[≠] (x : OnePoint X)) := by
  simpa [nhdsWithin_coe, preimage, coe_eq_coe] using! h.map some
/-
**OnePoint.nhdsNE_infty_eq** 是 Mathlib 中的一个定理，位于命名空间 `OnePoint`。
形式化陈述：nhdsNE_infty_eq : 𝓝[!=] (∞ : OnePoint X) = map (↑) (coclosedCompact X)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.ext`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort u_5} {l 
l' : Filter α} {p : ι → Prop} {s : ι → Set α} {p' : ι' → Prop}   {s' : ι' → Set 
α},   l.H…
· 使用定理 `nhdsWithin_basis_open`：nhdsWithin_basis_open (a : α) (t : Set α) : (𝓝[t]
 a).HasBasis (fun u => a in u ∧ IsOpen u) fun u => u inter t
· 使用定理 `Filter.HasBasis.map`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {l :
 Filter α} {p : ι → Prop} {s : ι → Set α} (f : α → β),   l.HasBasis p s → (Filte
r.map f l…
· 使用定理 `Filter.hasBasis_coclosedCompact`：hasBasis_coclosedCompact : (Filter.cocl
osedCompact X).HasBasis (fun s => IsClosed s ∧ IsCompact s) compl
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `OnePoint.isOpen_iff_of_mem`：isOpen_iff_of_mem (h : ∞ in s) : IsOpen s ↔ 
IsClosed ((↑) ⁻¹' s : Set X)ᶜ ∧ IsCompact ((↑) ⁻¹' s : Set X)ᶜ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Set.mem_compl`：mem_compl {s : Set α} {x : α} (h : x ∉ s) : x in sᶜ
· 使用定理 `OnePoint.infty_notMem_image_coe`：infty_notMem_image_coe {s : Set X} : ∞ 
∉ ((↑) : X -> OnePoint X) '' s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `OnePoint.isOpen_compl_image_coe`：isOpen_compl_image_coe {s : Set X} : Is
Open ((↑) '' s : Set (OnePoint X))ᶜ ↔ IsClosed s ∧ IsCompact s
· 使用定理 `OnePoint.compl_image_coe`：compl_image_coe (s : Set X) : ((↑) '' s : Set 
(OnePoint X))ᶜ = (↑) '' sᶜ union {∞}
· 使用定理 `Set.union_singleton`：union_singleton : s union {a} = insert a s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.sdiff_eq`：sdiff_eq (s t : Set α) : s \ t = s inter tᶜ
· 使用引理 `Set.insert_sdiff_of_mem`：insert_sdiff_of_mem (s) (h : a in t) : insert a
 s \ t = s \ t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Set.sdiff_singleton_eq_self`：sdiff_singleton_eq_self (h : a ∉ s) : s \ {
a} = s
-/
theorem nhdsNE_infty_eq : 𝓝[≠] (∞ : OnePoint X) = map (↑) (coclosedCompact X) := by
  refine (nhdsWithin_basis_open ∞ _).ext (hasBasis_coclosedCompact.map _) ?_ ?_
  · rintro s ⟨hs, hso⟩
    refine ⟨_, (isOpen_iff_of_mem hs).mp hso, ?_⟩
    simp
  · rintro s ⟨h₁, h₂⟩
    refine ⟨_, ⟨mem_compl infty_notMem_image_coe, isOpen_compl_image_coe.2 ⟨h₁, h₂⟩⟩, ?_⟩
    simp [compl_image_coe, ← sdiff_eq]

/-- If `X` is a non-compact space, then `∞` is not an isolated point of `OnePoint X`. -/
/-
**OnePoint.nhdsNE_infty_neBot** 是 Mathlib 中的一个实例，位于命名空间 `OnePoint`。
形式化陈述：nhdsNE_infty_neBot [NoncompactSpace X] : NeBot (𝓝[!=] (∞ : OnePoint X))
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OnePoint.nhdsNE_infty_eq`：nhdsNE_infty_eq : 𝓝[!=] (∞ : OnePoint X) = map
 (↑) (coclosedCompact X)
· 使用定理 `instNeBotCoclosedCompactOfNoncompactSpace`：∀ {X : Type u} [inst : Topolo
gicalSpace X] [NoncompactSpace X], (Filter.coclosedCompact X).NeBot

--- 原说明 ---
If `X` is a non-compact space, then `∞` is not an isolated point of `OnePoint X`
.
-/
instance nhdsNE_infty_neBot [NoncompactSpace X] : NeBot (𝓝[≠] (∞ : OnePoint X)) := by
  rw [nhdsNE_infty_eq]
  infer_instance
/-
**OnePoint.** 是 Mathlib 中的一个实例，位于命名空间 `OnePoint`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 900) nhdsNE_neBot [∀ x : X, NeBot (𝓝[≠] x)] [NoncompactSpace X]
    (x : OnePoint X) : NeBot (𝓝[≠] x) :=
  OnePoint.rec OnePoint.nhdsNE_infty_neBot (fun y => OnePoint.nhdsNE_coe_neBot y) x
/-
**OnePoint.nhds_infty_eq** 是 Mathlib 中的一个定理，位于命名空间 `OnePoint`。
形式化陈述：nhds_infty_eq : 𝓝 (∞ : OnePoint X) = map (↑) (coclosedCompact X) ⊔ pure ∞
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OnePoint.nhdsNE_infty_eq`：nhdsNE_infty_eq : 𝓝[!=] (∞ : OnePoint X) = map
 (↑) (coclosedCompact X)
· 使用定理 `nhdsNE_sup_pure`：nhdsNE_sup_pure (a : α) : 𝓝[!=] a ⊔ pure a = 𝓝 a
-/
theorem nhds_infty_eq : 𝓝 (∞ : OnePoint X) = map (↑) (coclosedCompact X) ⊔ pure ∞ := by
  rw [← nhdsNE_infty_eq, nhdsNE_sup_pure]
/-
**OnePoint.tendsto_coe_infty** 是 Mathlib 中的一个定理，位于命名空间 `OnePoint`。
形式化陈述：tendsto_coe_infty : Tendsto (↑) (coclosedCompact X) (𝓝 (∞ : OnePoint X))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OnePoint.nhds_infty_eq`：nhds_infty_eq : 𝓝 (∞ : OnePoint X) = map (↑) (co
closedCompact X) ⊔ pure ∞
· 使用定理 `Filter.Tendsto.mono_right`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
x : Filter α} {y z : Filter β},   Filter.Tendsto f x y → y ≤ z → Filter.Tendsto 
f x z
· 使用定理 `Filter.tendsto_map`：tendsto_map {f : α -> β} {x : Filter α} : Tendsto f 
x (map f x)
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
-/
theorem tendsto_coe_infty : Tendsto (↑) (coclosedCompact X) (𝓝 (∞ : OnePoint X)) := by
  rw [nhds_infty_eq]
  exact Filter.Tendsto.mono_right tendsto_map le_sup_left
/-
**OnePoint.hasBasis_nhds_infty** 是 Mathlib 中的一个定理，位于命名空间 `OnePoint`。
形式化陈述：hasBasis_nhds_infty : (𝓝 (∞ : OnePoint X)).HasBasis (fun s : Set X => IsCl
osed s ∧ IsCompact s) fun s => (↑) '' sᶜ union {∞}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OnePoint.nhds_infty_eq`：nhds_infty_eq : 𝓝 (∞ : OnePoint X) = map (↑) (co
closedCompact X) ⊔ pure ∞
· 使用定理 `Filter.HasBasis.sup_pure`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α}
 {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → ∀ (x : α), (l ⊔ pure x).HasB
asis p fun i =…
· 使用定理 `Filter.HasBasis.map`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {l :
 Filter α} {p : ι → Prop} {s : ι → Set α} (f : α → β),   l.HasBasis p s → (Filte
r.map f l…
· 使用定理 `Filter.hasBasis_coclosedCompact`：hasBasis_coclosedCompact : (Filter.cocl
osedCompact X).HasBasis (fun s => IsClosed s ∧ IsCompact s) compl
-/
theorem hasBasis_nhds_infty :
    (𝓝 (∞ : OnePoint X)).HasBasis (fun s : Set X => IsClosed s ∧ IsCompact s) fun s =>
      (↑) '' sᶜ ∪ {∞} := by
  rw [nhds_infty_eq]
  exact (hasBasis_coclosedCompact.map _).sup_pure _

@[simp]
/-
**OnePoint.comap_coe_nhds_infty** 是 Mathlib 中的一个定理，位于命名空间 `OnePoint`。
形式化陈述：comap_coe_nhds_infty : comap ((↑) : X -> OnePoint X) (𝓝 ∞) = coclosedCompa
ct X
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OnePoint.nhds_infty_eq`：nhds_infty_eq : 𝓝 (∞ : OnePoint X) = map (↑) (co
closedCompact X) ⊔ pure ∞
· 使用定理 `Filter.comap_sup`：comap_sup : comap m (g₁ ⊔ g₂) = comap m g₁ ⊔ comap m g
₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Filter.comap_map`：comap_map {f : Filter α} {m : α -> β} (h : Injective m
) : comap m (map m f) = f
· 使用定理 `OnePoint.coe_injective`：coe_injective : Function.Injective ((↑) : X -> O
nePoint X)
· 使用定理 `Filter.comap_pure`：comap_pure {b : β} : comap m (pure b) = 𝓟 (m ⁻¹' {b})
· 使用定理 `OnePoint.coe_preimage_infty`：coe_preimage_infty : ((↑) : X -> OnePoint X
) ⁻¹' {∞} = ∅
· 使用定理 `Filter.principal_empty`：principal_empty : 𝓟 (∅ : Set α) = ⊥
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem comap_coe_nhds_infty : comap ((↑) : X → OnePoint X) (𝓝 ∞) = coclosedCompact X := by
  simp [nhds_infty_eq, comap_sup, comap_map coe_injective]
/-
**OnePoint.le_nhds_infty** 是 Mathlib 中的一个定理，位于命名空间 `OnePoint`。
形式化陈述：le_nhds_infty {f : Filter (OnePoint X)} : f <= 𝓝 ∞ ↔ forall s : Set X, IsC
losed s -> IsCompact s -> (↑) '' sᶜ union {∞} in f
参数：OnePoint X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.HasBasis.ge_iff`：∀ {α : Type u_1} {ι' : Sort u_5} {l l' : Filter 
α} {p' : ι' → Prop} {s' : ι' → Set α},   l'.HasBasis p' s' → (l ≤ l' ↔ ∀ (i' : ι
'), p' i' → …
· 使用定理 `OnePoint.hasBasis_nhds_infty`：hasBasis_nhds_infty : (𝓝 (∞ : OnePoint X))
.HasBasis (fun s : Set X => IsClosed s ∧ IsCompact s) fun s => (↑) '' sᶜ union {
∞}
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem le_nhds_infty {f : Filter (OnePoint X)} :
    f ≤ 𝓝 ∞ ↔ ∀ s : Set X, IsClosed s → IsCompact s → (↑) '' sᶜ ∪ {∞} ∈ f := by
  simp only [hasBasis_nhds_infty.ge_iff, and_imp]
/-
**OnePoint.ultrafilter_le_nhds_infty** 是 Mathlib 中的一个定理，位于命名空间 `OnePoint`。
形式化陈述：ultrafilter_le_nhds_infty {f : Ultrafilter (OnePoint X)} : (f : Filter (On
ePoint X)) <= 𝓝 ∞ ↔ forall s : Set X, IsClosed s -> IsCompact s -> (↑) '' s ∉ f
参数：OnePoint X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem ultrafilter_le_nhds_infty {f : Ultrafilter (OnePoint X)} :
    (f : Filter (OnePoint X)) ≤ 𝓝 ∞ ↔ ∀ s : Set X, IsClosed s → IsCompact s → (↑) '' s ∉ f := by
  simp only [le_nhds_infty, ← compl_image_coe, Ultrafilter.mem_coe,
    Ultrafilter.compl_mem_iff_notMem]
/-
**OnePoint.tendsto_nhds_infty'** 是 Mathlib 中的一个定理，位于命名空间 `OnePoint`。
形式化陈述：tendsto_nhds_infty' {α : Type*} {f : OnePoint X -> α} {l : Filter α} : Ten
dsto f (𝓝 ∞) l ↔ Tendsto f (pure ∞) l ∧ Tendsto (f ∘ (↑)) (coclosedCompact X) l
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `OnePoint.nhds_infty_eq`：nhds_infty_eq : 𝓝 (∞ : OnePoint X) = map (↑) (co
closedCompact X) ⊔ pure ∞
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem tendsto_nhds_infty' {α : Type*} {f : OnePoint X → α} {l : Filter α} :
    Tendsto f (𝓝 ∞) l ↔ Tendsto f (pure ∞) l ∧ Tendsto (f ∘ (↑)) (coclosedCompact X) l := by
  simp [nhds_infty_eq, and_comm]
/-
**OnePoint.tendsto_nhds_infty** 是 Mathlib 中的一个定理，位于命名空间 `OnePoint`。
形式化陈述：tendsto_nhds_infty {α : Type*} {f : OnePoint X -> α} {l : Filter α} : Tend
sto f (𝓝 ∞) l ↔ forall s in l, f ∞ in s ∧ exists t : Set X, IsClosed t ∧ IsCompa
ct t ∧ MapsTo (f ∘ (↑)) tᶜ s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `OnePoint.tendsto_nhds_infty'`：tendsto_nhds_infty' {α : Type*} {f : OnePo
int X -> α} {l : Filter α} : Tendsto f (𝓝 ∞) l ↔ Tendsto f (pure ∞) l ∧ Tendsto 
(f ∘ (↑)) (coclose…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.HasBasis.tendsto_left_iff`：∀ {α : Type u_1} {β : Type u_2} {ι : S
ort u_4} {la : Filter α} {pa : ι → Prop} {sa : ι → Set α} {lb : Filter β}   {f :
 α → β}, la.HasBasis p…
· 使用定理 `Filter.hasBasis_coclosedCompact`：hasBasis_coclosedCompact : (Filter.cocl
osedCompact X).HasBasis (fun s => IsClosed s ∧ IsCompact s) compl
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem tendsto_nhds_infty {α : Type*} {f : OnePoint X → α} {l : Filter α} :
    Tendsto f (𝓝 ∞) l ↔
      ∀ s ∈ l, f ∞ ∈ s ∧ ∃ t : Set X, IsClosed t ∧ IsCompact t ∧ MapsTo (f ∘ (↑)) tᶜ s :=
  tendsto_nhds_infty'.trans <| by
    simp only [tendsto_pure_left, hasBasis_coclosedCompact.tendsto_left_iff, forall_and,
      and_assoc]
/-
**OnePoint.continuousAt_infty'** 是 Mathlib 中的一个定理，位于命名空间 `OnePoint`。
形式化陈述：continuousAt_infty' {Y : Type*} [TopologicalSpace Y] {f : OnePoint X -> Y}
 : ContinuousAt f ∞ ↔ Tendsto (f ∘ (↑)) (coclosedCompact X) (𝓝 (f ∞))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `OnePoint.tendsto_nhds_infty'`：tendsto_nhds_infty' {α : Type*} {f : OnePo
int X -> α} {l : Filter α} : Tendsto f (𝓝 ∞) l ↔ Tendsto f (pure ∞) l ∧ Tendsto 
(f ∘ (↑)) (coclose…
· 使用定理 `and_iff_right`：∀ {a b : Prop}, a → (a ∧ b ↔ b)
· 使用定理 `tendsto_pure_nhds`：tendsto_pure_nhds (f : α -> X) (a : α) : Tendsto f (p
ure a) (𝓝 (f a))
-/
theorem continuousAt_infty' {Y : Type*} [TopologicalSpace Y] {f : OnePoint X → Y} :
    ContinuousAt f ∞ ↔ Tendsto (f ∘ (↑)) (coclosedCompact X) (𝓝 (f ∞)) :=
  tendsto_nhds_infty'.trans <| and_iff_right (tendsto_pure_nhds _ _)
/-
**OnePoint.continuousAt_infty** 是 Mathlib 中的一个定理，位于命名空间 `OnePoint`。
形式化陈述：continuousAt_infty {Y : Type*} [TopologicalSpace Y] {f : OnePoint X -> Y} 
: ContinuousAt f ∞ ↔ forall s in 𝓝 (f ∞), exists t : Set X, IsClosed t ∧ IsCompa
ct t ∧ MapsTo (f ∘ (↑)) tᶜ s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `OnePoint.continuousAt_infty'`：continuousAt_infty' {Y : Type*} [Topologic
alSpace Y] {f : OnePoint X -> Y} : ContinuousAt f ∞ ↔ Tendsto (f ∘ (↑)) (coclose
dCompact X) (𝓝 (f …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.HasBasis.tendsto_left_iff`：∀ {α : Type u_1} {β : Type u_2} {ι : S
ort u_4} {la : Filter α} {pa : ι → Prop} {sa : ι → Set α} {lb : Filter β}   {f :
 α → β}, la.HasBasis p…
· 使用定理 `Filter.hasBasis_coclosedCompact`：hasBasis_coclosedCompact : (Filter.cocl
osedCompact X).HasBasis (fun s => IsClosed s ∧ IsCompact s) compl
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem continuousAt_infty {Y : Type*} [TopologicalSpace Y] {f : OnePoint X → Y} :
    ContinuousAt f ∞ ↔
      ∀ s ∈ 𝓝 (f ∞), ∃ t : Set X, IsClosed t ∧ IsCompact t ∧ MapsTo (f ∘ (↑)) tᶜ s :=
  continuousAt_infty'.trans <| by simp only [hasBasis_coclosedCompact.tendsto_left_iff, and_assoc]
/-
**OnePoint.continuousAt_coe** 是 Mathlib 中的一个定理，位于命名空间 `OnePoint`。
形式化陈述：continuousAt_coe {Y : Type*} [TopologicalSpace Y] {f : OnePoint X -> Y} {x
 : X} : ContinuousAt f x ↔ ContinuousAt (f ∘ (↑)) x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousAt.eq_1`：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSp
ace X] [inst_1 : TopologicalSpace Y] (f : X → Y) (x : X),   ContinuousAt f x = F
ilter.T…
· 使用定理 `OnePoint.nhds_coe_eq`：nhds_coe_eq (x : X) : 𝓝 ↑x = map ((↑) : X -> OnePo
int X) (𝓝 x)
· 使用定理 `Filter.tendsto_map'_iff`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} 
{f : β → γ} {g : α → β} {x : Filter α} {y : Filter γ},   Filter.Tendsto f (Filte
r.map g x) y …
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem continuousAt_coe {Y : Type*} [TopologicalSpace Y] {f : OnePoint X → Y} {x : X} :
    ContinuousAt f x ↔ ContinuousAt (f ∘ (↑)) x := by
  rw [ContinuousAt, nhds_coe_eq, tendsto_map'_iff, ContinuousAt]; rfl
/-
**OnePoint.continuous_iff** 是 Mathlib 中的一个引理，位于命名空间 `OnePoint`。
形式化陈述：continuous_iff {Y : Type*} [TopologicalSpace Y] (f : OnePoint X -> Y) : Co
ntinuous f ↔ Tendsto (fun x : X => f x) (coclosedCompact X) (𝓝 (f ∞)) ∧ Continuo
us (fun x : X => f x)
参数：f : OnePoint X -> Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma continuous_iff {Y : Type*} [TopologicalSpace Y] (f : OnePoint X → Y) : Continuous f ↔
    Tendsto (fun x : X ↦ f x) (coclosedCompact X) (𝓝 (f ∞)) ∧ Continuous (fun x : X ↦ f x) := by
  simp only [continuous_iff_continuousAt, OnePoint.forall, continuousAt_coe, continuousAt_infty',
    Function.comp_def]

/--
A constructor for continuous maps out of a one point compactification, given a continuous map from
the underlying space and a limit value at infinity.
-/
/-
**OnePoint.continuousMapMk** 是 Mathlib 中的一个定义，位于命名空间 `OnePoint`。
形式化陈述：continuousMapMk {Y : Type*} [TopologicalSpace Y] (f : C(X, Y)) (y : Y) (h 
: Tendsto f (coclosedCompact X) (𝓝 y)) : C(OnePoint X, Y) where toFun x
参数：f : C(X, Y)；y : Y；h : Tendsto f (coclosedCompact X) (𝓝 y)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A constructor for continuous maps out of a one point compactification, given a c
ontinuous map from
the underlying space and a limit value at infinity.
-/
def continuousMapMk {Y : Type*} [TopologicalSpace Y] (f : C(X, Y)) (y : Y)
    (h : Tendsto f (coclosedCompact X) (𝓝 y)) : C(OnePoint X, Y) where
  toFun x := x.elim y f
  continuous_toFun := by
    rw [continuous_iff]
    refine ⟨h, f.continuous⟩
/-
**OnePoint.continuous_iff_from_discrete** 是 Mathlib 中的一个引理，位于命名空间 `OnePoint`。
形式化陈述：continuous_iff_from_discrete {Y : Type*} [TopologicalSpace Y] [DiscreteTop
ology X] (f : OnePoint X -> Y) : Continuous f ↔ Tendsto (fun x : X => f x) cofin
ite (𝓝 (f ∞))
参数：f : OnePoint X -> Y。
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
· 使用定理 `Filter.coclosedCompact_eq_cocompact`：Filter.coclosedCompact_eq_cocompact
 : coclosedCompact X = cocompact X
· 使用定理 `T2Space.r1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], R1Space X
· 使用定理 `DiscreteTopology.toT2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X]
 [DiscreteTopology X], T2Space X
· 使用定理 `Filter.cocompact_eq_cofinite`：cocompact_eq_cofinite (X : Type*) [Topolog
icalSpace X] [DiscreteTopology X] : cocompact X = cofinite
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma continuous_iff_from_discrete {Y : Type*} [TopologicalSpace Y]
    [DiscreteTopology X] (f : OnePoint X → Y) :
    Continuous f ↔ Tendsto (fun x : X ↦ f x) cofinite (𝓝 (f ∞)) := by
  simp [continuous_iff, cocompact_eq_cofinite, continuous_of_discreteTopology]

/--
A constructor for continuous maps out of a one point compactification of a discrete space, given a
map from the underlying space and a limit value at infinity.
-/
/-
**OnePoint.continuousMapMkDiscrete** 是 Mathlib 中的一个定义，位于命名空间 `OnePoint`。
形式化陈述：continuousMapMkDiscrete {Y : Type*} [TopologicalSpace Y] [DiscreteTopology
 X] (f : X -> Y) (y : Y) (h : Tendsto f cofinite (𝓝 y)) : C(OnePoint X, Y)
参数：f : X -> Y；y : Y；h : Tendsto f cofinite (𝓝 y)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_of_discreteTopology`：continuous_of_discreteTopology [Topologi
calSpace β] {f : α -> β} : Continuous f

--- 原说明 ---
A constructor for continuous maps out of a one point compactification of a discr
ete space, given a
map from the underlying space and a limit value at infinity.
-/
def continuousMapMkDiscrete {Y : Type*} [TopologicalSpace Y]
    [DiscreteTopology X] (f : X → Y) (y : Y) (h : Tendsto f cofinite (𝓝 y)) :
    C(OnePoint X, Y) :=
  continuousMapMk ⟨f, continuous_of_discreteTopology⟩ y (by simpa [cocompact_eq_cofinite])

variable (X) in
/--
Continuous maps out of the one point compactification of an infinite discrete space to a Hausdorff
space correspond bijectively to "convergent" maps out of the discrete space.
-/
/-
**OnePoint.continuousMapDiscreteEquiv** 是 Mathlib 中的一个定义，位于命名空间 `OnePoint`。
形式化陈述：continuousMapDiscreteEquiv (Y : Type*) [DiscreteTopology X] [TopologicalSp
ace Y] [T2Space Y] [Infinite X] : C(OnePoint X, Y) ≃ { f : X -> Y // exists L, T
endsto (fun x : X => f x) cofinite (𝓝 L) } where .mp (map_continuous f)⟩⟩ toFun 
f
参数：Y : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Continuous maps out of the one point compactification of an infinite discrete sp
ace to a Hausdorff
space correspond bijectively to "convergent" maps out of the discrete space.
-/
noncomputable def continuousMapDiscreteEquiv (Y : Type*) [DiscreteTopology X] [TopologicalSpace Y]
    [T2Space Y] [Infinite X] :
    C(OnePoint X, Y) ≃ { f : X → Y // ∃ L, Tendsto (fun x : X ↦ f x) cofinite (𝓝 L) } where
  toFun f := ⟨(f ·), ⟨f ∞, continuous_iff_from_discrete _ |>.mp (map_continuous f)⟩⟩
  invFun f :=
    { toFun := fun x => match x with
        | ∞ => Classical.choose f.2
        | some x => f.1 x
      continuous_toFun := continuous_iff_from_discrete _ |>.mpr <| Classical.choose_spec f.2 }
  left_inv f := by
    ext x
    refine OnePoint.rec ?_ ?_ x
    · refine tendsto_nhds_unique ?_ (continuous_iff_from_discrete _ |>.mp <| map_continuous f)
      let f' : { f : X → Y // ∃ L, Tendsto (fun x : X ↦ f x) cofinite (𝓝 L) } :=
        ⟨fun x ↦ f x, ⟨f ∞, continuous_iff_from_discrete f |>.mp <| map_continuous f⟩⟩
      exact Classical.choose_spec f'.property
    · simp
/-
**OnePoint.continuous_iff_from_nat** 是 Mathlib 中的一个引理，位于命名空间 `OnePoint`。
形式化陈述：continuous_iff_from_nat {Y : Type*} [TopologicalSpace Y] (f : OnePoint Nat
 -> Y) : Continuous f ↔ Tendsto (fun x : Nat => f x) atTop (𝓝 (f ∞))
参数：f : OnePoint Nat -> Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `OnePoint.continuous_iff_from_discrete`：continuous_iff_from_discrete {Y :
 Type*} [TopologicalSpace Y] [DiscreteTopology X] (f : OnePoint X -> Y) : Contin
uous f ↔ Tendsto (fun x : X…
· 使用定理 `instDiscreteTopologyNat`：DiscreteTopology ℕ
· 使用定理 `Nat.cofinite_eq_atTop`：Nat.cofinite_eq_atTop : @cofinite Nat = atTop
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma continuous_iff_from_nat {Y : Type*} [TopologicalSpace Y] (f : OnePoint ℕ → Y) :
    Continuous f ↔ Tendsto (fun x : ℕ ↦ f x) atTop (𝓝 (f ∞)) := by
  rw [continuous_iff_from_discrete, Nat.cofinite_eq_atTop]

/--
A constructor for continuous maps out of the one point compactification of `ℕ`, given a
sequence and a limit value at infinity.
-/
/-
**OnePoint.continuousMapMkNat** 是 Mathlib 中的一个定义，位于命名空间 `OnePoint`。
形式化陈述：continuousMapMkNat {Y : Type*} [TopologicalSpace Y] (f : Nat -> Y) (y : Y)
 (h : Tendsto f atTop (𝓝 y)) : C(OnePoint Nat, Y)
参数：f : Nat -> Y；y : Y；h : Tendsto f atTop (𝓝 y)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instDiscreteTopologyNat`：DiscreteTopology ℕ

--- 原说明 ---
A constructor for continuous maps out of the one point compactification of `ℕ`, 
given a
sequence and a limit value at infinity.
-/
def continuousMapMkNat {Y : Type*} [TopologicalSpace Y]
    (f : ℕ → Y) (y : Y) (h : Tendsto f atTop (𝓝 y)) :
    C(OnePoint ℕ, Y) :=
  continuousMapMkDiscrete f y (by rwa [Nat.cofinite_eq_atTop])

/--
Continuous maps out of the one point compactification of `ℕ` to a Hausdorff space `Y` correspond
bijectively to convergent sequences in `Y`.
-/
/-
**OnePoint.continuousMapNatEquiv** 是 Mathlib 中的一个定义，位于命名空间 `OnePoint`。
形式化陈述：continuousMapNatEquiv (Y : Type*) [TopologicalSpace Y] [T2Space Y] : C(One
Point Nat, Y) ≃ { f : Nat -> Y // exists L, Tendsto (f ·) atTop (𝓝 L) }
参数：Y : Type*。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `instDiscreteTopologyNat`：DiscreteTopology ℕ
· 使用定理 `instInfiniteNat`：Infinite ℕ

--- 原说明 ---
Continuous maps out of the one point compactification of `ℕ` to a Hausdorff spac
e `Y` correspond
bijectively to convergent sequences in `Y`.
-/
noncomputable def continuousMapNatEquiv (Y : Type*) [TopologicalSpace Y] [T2Space Y] :
    C(OnePoint ℕ, Y) ≃ { f : ℕ → Y // ∃ L, Tendsto (f ·) atTop (𝓝 L) } := by
  refine (continuousMapDiscreteEquiv ℕ Y).trans {
    toFun := fun ⟨f, hf⟩ ↦ ⟨f, by rwa [← Nat.cofinite_eq_atTop]⟩
    invFun := fun ⟨f, hf⟩ ↦ ⟨f, by rwa [Nat.cofinite_eq_atTop]⟩ }

/-- If `X` is not a compact space, then the natural embedding `X → OnePoint X` has dense range.
-/
/-
**OnePoint.denseRange_coe** 是 Mathlib 中的一个定理，位于命名空间 `OnePoint`。
形式化陈述：denseRange_coe [NoncompactSpace X] : DenseRange ((↑) : X -> OnePoint X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DenseRange.eq_1`：∀ {X : Type u} [inst : TopologicalSpace X] {α : Type u_
1} (f : α → X), DenseRange f = Dense (Set.range f)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OnePoint.compl_infty`：compl_infty : ({∞}ᶜ : Set (OnePoint X)) = range ((
↑) : X -> OnePoint X)
· 使用定理 `dense_compl_singleton`：dense_compl_singleton (x : X) [NeBot (𝓝[!=] x)] :
 Dense ({x}ᶜ : Set X)

--- 原说明 ---
If `X` is not a compact space, then the natural embedding `X → OnePoint X` has d
ense range.
-/
theorem denseRange_coe [NoncompactSpace X] : DenseRange ((↑) : X → OnePoint X) := by
  rw [DenseRange, ← compl_infty]
  exact dense_compl_singleton _
/-
**OnePoint.isDenseEmbedding_coe** 是 Mathlib 中的一个定理，位于命名空间 `OnePoint`。
形式化陈述：isDenseEmbedding_coe [NoncompactSpace X] : IsDenseEmbedding ((↑) : X -> On
ePoint X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OnePoint.isOpenEmbedding_coe`：isOpenEmbedding_coe : IsOpenEmbedding ((↑)
 : X -> OnePoint X)
· 使用定理 `Topology.IsEmbedding.toIsInducing`：∀ {X : Type u_1} {Y : Type u_2} [tX :
 TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbeddi
ng f → Topology.IsInduc…
· 使用定理 `Topology.IsOpenEmbedding.toIsEmbedding`：∀ {X : Type u_1} {Y : Type u_2} 
[tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsOp
enEmbedding f → Topology.IsE…
· 使用定理 `OnePoint.denseRange_coe`：denseRange_coe [NoncompactSpace X] : DenseRange
 ((↑) : X -> OnePoint X)
· 使用定理 `Topology.IsEmbedding.injective`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbedding 
f → Function.Injecti…
-/
theorem isDenseEmbedding_coe [NoncompactSpace X] : IsDenseEmbedding ((↑) : X → OnePoint X) :=
  { isOpenEmbedding_coe with dense := denseRange_coe }

@[simp, norm_cast]
/-
**OnePoint.specializes_coe** 是 Mathlib 中的一个定理，位于命名空间 `OnePoint`。
形式化陈述：specializes_coe {x y : X} : (x : OnePoint X) ⤳ y ↔ x ⤳ y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsInducing.specializes_iff`：Topology.IsInducing.specializes_iff
 (hf : IsInducing f) : f x ⤳ f y ↔ x ⤳ y
· 使用定理 `Topology.IsOpenEmbedding.isInducing`：∀ {X : Type u_1} {Y : Type u_2} {f 
: X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.I
sOpenEmbedding f → Topolo…
· 使用定理 `OnePoint.isOpenEmbedding_coe`：isOpenEmbedding_coe : IsOpenEmbedding ((↑)
 : X -> OnePoint X)
-/
theorem specializes_coe {x y : X} : (x : OnePoint X) ⤳ y ↔ x ⤳ y :=
  isOpenEmbedding_coe.isInducing.specializes_iff

@[simp, norm_cast]
/-
**OnePoint.inseparable_coe** 是 Mathlib 中的一个定理，位于命名空间 `OnePoint`。
形式化陈述：inseparable_coe {x y : X} : Inseparable (x : OnePoint X) y ↔ Inseparable x
 y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsInducing.inseparable_iff`：Topology.IsInducing.inseparable_iff
 (hf : IsInducing f) : (f x ~ᵢ f y) ↔ (x ~ᵢ y)
· 使用定理 `Topology.IsOpenEmbedding.isInducing`：∀ {X : Type u_1} {Y : Type u_2} {f 
: X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.I
sOpenEmbedding f → Topolo…
· 使用定理 `OnePoint.isOpenEmbedding_coe`：isOpenEmbedding_coe : IsOpenEmbedding ((↑)
 : X -> OnePoint X)
-/
theorem inseparable_coe {x y : X} : Inseparable (x : OnePoint X) y ↔ Inseparable x y :=
  isOpenEmbedding_coe.isInducing.inseparable_iff
/-
**OnePoint.not_specializes_infty_coe** 是 Mathlib 中的一个定理，位于命名空间 `OnePoint`。
形式化陈述：not_specializes_infty_coe {x : X} : ¬Specializes ∞ (x : OnePoint X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosed.not_specializes`：IsClosed.not_specializes (hs : IsClosed s) (hx
 : x in s) (hy : y ∉ s) : ¬x ⤳ y
· 使用定理 `OnePoint.isClosed_infty`：isClosed_infty : IsClosed ({∞} : Set (OnePoint 
X))
· 使用定理 `OnePoint.coe_ne_infty`：coe_ne_infty (x : X) : (x : OnePoint X) != ∞
-/
theorem not_specializes_infty_coe {x : X} : ¬Specializes ∞ (x : OnePoint X) :=
  isClosed_infty.not_specializes rfl (coe_ne_infty x)
/-
**OnePoint.not_inseparable_infty_coe** 是 Mathlib 中的一个定理，位于命名空间 `OnePoint`。
形式化陈述：not_inseparable_infty_coe {x : X} : ¬Inseparable ∞ (x : OnePoint X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OnePoint.not_specializes_infty_coe`：not_specializes_infty_coe {x : X} : 
¬Specializes ∞ (x : OnePoint X)
· 使用定理 `Inseparable.specializes`：Inseparable.specializes (h : x ~ᵢ y) : x ⤳ y
-/
theorem not_inseparable_infty_coe {x : X} : ¬Inseparable ∞ (x : OnePoint X) := fun h =>
  not_specializes_infty_coe h.specializes
/-
**OnePoint.not_inseparable_coe_infty** 是 Mathlib 中的一个定理，位于命名空间 `OnePoint`。
形式化陈述：not_inseparable_coe_infty {x : X} : ¬Inseparable (x : OnePoint X) ∞
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OnePoint.not_specializes_infty_coe`：not_specializes_infty_coe {x : X} : 
¬Specializes ∞ (x : OnePoint X)
· 使用定理 `Inseparable.specializes'`：Inseparable.specializes' (h : x ~ᵢ y) : y ⤳ x
-/
theorem not_inseparable_coe_infty {x : X} : ¬Inseparable (x : OnePoint X) ∞ := fun h =>
  not_specializes_infty_coe h.specializes'
/-
**OnePoint.inseparable_iff** 是 Mathlib 中的一个定理，位于命名空间 `OnePoint`。
形式化陈述：inseparable_iff {x y : OnePoint X} : Inseparable x y ↔ x = ∞ ∧ y = ∞ ∨ exi
sts x' : X, x = x' ∧ exists y' : X, y = y' ∧ Inseparable x' y'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
-/
theorem inseparable_iff {x y : OnePoint X} :
    Inseparable x y ↔ x = ∞ ∧ y = ∞ ∨ ∃ x' : X, x = x' ∧ ∃ y' : X, y = y' ∧ Inseparable x' y' := by
  induction x using OnePoint.rec <;> induction y using OnePoint.rec <;>
    simp [not_inseparable_infty_coe, not_inseparable_coe_infty, coe_eq_coe, Inseparable.refl]
/-
**OnePoint.continuous_map_iff** 是 Mathlib 中的一个定理，位于命名空间 `OnePoint`。
形式化陈述：continuous_map_iff [TopologicalSpace Y] {f : X -> Y} : Continuous (OnePoin
t.map f) ↔ Continuous f ∧ Tendsto f (coclosedCompact X) (coclosedCompact Y)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Topology.IsInducing.continuous_iff`：continuous_iff (hg : IsInducing g) :
 Continuous f ↔ Continuous (g ∘ f)
· 使用定理 `Topology.IsOpenEmbedding.isInducing`：∀ {X : Type u_1} {Y : Type u_2} {f 
: X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.I
sOpenEmbedding f → Topolo…
· 使用定理 `OnePoint.isOpenEmbedding_coe`：isOpenEmbedding_coe : IsOpenEmbedding ((↑)
 : X -> OnePoint X)
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
-/
theorem continuous_map_iff [TopologicalSpace Y] {f : X → Y} :
    Continuous (OnePoint.map f) ↔
      Continuous f ∧ Tendsto f (coclosedCompact X) (coclosedCompact Y) := by
  simp_rw [continuous_iff, map_some, ← comap_coe_nhds_infty, tendsto_comap_iff, map_infty,
    isOpenEmbedding_coe.isInducing.continuous_iff (Y := Y)]
  exact and_comm
/-
**OnePoint.continuous_map** 是 Mathlib 中的一个定理，位于命名空间 `OnePoint`。
形式化陈述：continuous_map [TopologicalSpace Y] {f : X -> Y} (hc : Continuous f) (h : 
Tendsto f (coclosedCompact X) (coclosedCompact Y)) : Continuous (OnePoint.map f)
参数：hc : Continuous f；h : Tendsto f (coclosedCompact X) (coclosedCompact Y)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `OnePoint.continuous_map_iff`：continuous_map_iff [TopologicalSpace Y] {f 
: X -> Y} : Continuous (OnePoint.map f) ↔ Continuous f ∧ Tendsto f (coclosedComp
act X) (coclosedC…
-/
theorem continuous_map [TopologicalSpace Y] {f : X → Y} (hc : Continuous f)
    (h : Tendsto f (coclosedCompact X) (coclosedCompact Y)) :
    Continuous (OnePoint.map f) :=
  continuous_map_iff.mpr ⟨hc, h⟩

/-!
### Compactness and separation properties

In this section we prove that `OnePoint X` is a compact space; it is a T₀ (resp., T₁) space if
the original space satisfies the same separation axiom. If the original space is a locally compact
Hausdorff space, then `OnePoint X` is a normal (hence, T₃ and Hausdorff) space.

Finally, if the original space `X` is *not* compact and is a preconnected space, then
`OnePoint X` is a connected space.
-/

set_option backward.isDefEq.respectTransparency false in
/-- For any topological space `X`, its one point compactification is a compact space. -/
/-
**OnePoint.** 是 Mathlib 中的一个实例，位于命名空间 `OnePoint`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For any topological space `X`, its one point compactification is a compact space
.
-/
instance : CompactSpace (OnePoint X) where
  isCompact_univ := by
    have : Tendsto ((↑) : X → OnePoint X) (cocompact X) (𝓝 ∞) := by
      rw [nhds_infty_eq]
      exact (tendsto_map.mono_left cocompact_le_coclosedCompact).mono_right le_sup_left
    rw [← insert_none_range_some X]
    exact this.isCompact_insert_range_of_cocompact continuous_coe

/-- The one point compactification of a `T0Space` space is a `T0Space`. -/
/-
**OnePoint.** 是 Mathlib 中的一个实例，位于命名空间 `OnePoint`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The one point compactification of a `T0Space` space is a `T0Space`.
-/
instance [T0Space X] : T0Space (OnePoint X) := by
  refine ⟨fun x y hxy => ?_⟩
  rcases inseparable_iff.1 hxy with (⟨rfl, rfl⟩ | ⟨x, rfl, y, rfl, h⟩)
  exacts [rfl, congr_arg some h.eq]

/-- The one point compactification of a `T1Space` space is a `T1Space`. -/
/-
**OnePoint.** 是 Mathlib 中的一个实例，位于命名空间 `OnePoint`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The one point compactification of a `T1Space` space is a `T1Space`.
-/
instance [T1Space X] : T1Space (OnePoint X) where
  t1 z := by
    induction z using OnePoint.rec
    · exact isClosed_infty
    · rw [← image_singleton, isClosed_image_coe]
      exact ⟨isClosed_singleton, isCompact_singleton⟩

/-- The one point compactification of a weakly locally compact R₁ space
is a normal topological space. -/
/-
**OnePoint.** 是 Mathlib 中的一个实例，位于命名空间 `OnePoint`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The one point compactification of a weakly locally compact R₁ space
is a normal topological space.
-/
instance [WeaklyLocallyCompactSpace X] [R1Space X] : NormalSpace (OnePoint X) := by
  suffices R1Space (OnePoint X) by infer_instance
  have key : ∀ z : X, Disjoint (𝓝 (some z)) (𝓝 ∞) := fun z ↦ by
    rw [nhds_infty_eq, disjoint_sup_right, nhds_coe_eq, coclosedCompact_eq_cocompact,
      disjoint_map coe_injective, ← principal_singleton, disjoint_principal_right, compl_infty]
    exact ⟨disjoint_nhds_cocompact z, range_mem_map⟩
  refine ⟨fun x y ↦ ?_⟩
  induction x using OnePoint.rec <;> induction y using OnePoint.rec
  · exact .inl le_rfl
  · exact .inr (key _).symm
  · exact .inr (key _)
  · rw [nhds_coe_eq, nhds_coe_eq, disjoint_map coe_injective, specializes_coe]
    apply specializes_or_disjoint_nhds

/-- The one point compactification of a weakly locally compact Hausdorff space is a T₄
(hence, Hausdorff and regular) topological space. -/
/-
**OnePoint.** 是 Mathlib 中的一个示例，位于命名空间 `OnePoint`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The one point compactification of a weakly locally compact Hausdorff space is a 
T₄
(hence, Hausdorff and regular) topological space.
-/
example [WeaklyLocallyCompactSpace X] [T2Space X] : T4Space (OnePoint X) := inferInstance

/-- If `X` is not a compact space, then `OnePoint X` is a connected space. -/
/-
**OnePoint.** 是 Mathlib 中的一个实例，位于命名空间 `OnePoint`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `X` is not a compact space, then `OnePoint X` is a connected space.
-/
instance [PreconnectedSpace X] [NoncompactSpace X] : ConnectedSpace (OnePoint X) where
  toPreconnectedSpace := isDenseEmbedding_coe.isDenseInducing.preconnectedSpace
  toNonempty := inferInstance

/-- If `X` is an infinite type with discrete topology (e.g., `ℕ`), then the identity map from
`CofiniteTopology (OnePoint X)` to `OnePoint X` is not continuous. -/
/-
**OnePoint.not_continuous_cofiniteTopology_of_symm** 是 Mathlib 中的一个定理，位于命名空间 `On
ePoint`。
形式化陈述：not_continuous_cofiniteTopology_of_symm [Infinite X] [DiscreteTopology X] 
: ¬Continuous (@CofiniteTopology.of (OnePoint X)).symm
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nontrivial.to_nonempty`：∀ {α : Type u_1} [Nontrivial α], Nonempty α
· 使用定理 `Infinite.instNontrivial`：∀ (α : Type u_4) [Infinite α], Nontrivial α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CofiniteTopology.nhds_eq`：nhds_eq (x : CofiniteTopology X) : 𝓝 x = pure 
x ⊔ cofinite
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `OnePoint.nhds_coe_eq`：nhds_coe_eq (x : X) : 𝓝 ↑x = map ((↑) : X -> OnePo
int X) (𝓝 x)
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `nhds_discrete`：nhds_discrete (α : Type*) [TopologicalSpace α] [DiscreteT
opology α] : @nhds α _ = pure
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Set.Finite.infinite_compl`：∀ {α : Type u} [Infinite α] {s : Set α}, s.Fi
nite → sᶜ.Infinite
· 使用定理 `WithTopology.instInfinite`：∀ {X : Type u_1} (t : TopologicalSpace X) [In
finite X], Infinite (WithTopology X t)
· 使用定理 `Set.finite_singleton`：finite_singleton (a : α) : ({a} : Set α).Finite

--- 原说明 ---
If `X` is an infinite type with discrete topology (e.g., `ℕ`), then the identity
 map from
`CofiniteTopology (OnePoint X)` to `OnePoint X` is not continuous.
-/
theorem not_continuous_cofiniteTopology_of_symm [Infinite X] [DiscreteTopology X] :
    ¬Continuous (@CofiniteTopology.of (OnePoint X)).symm := by
  inhabit X
  simp only [continuous_iff_continuousAt, ContinuousAt, not_forall]
  use CofiniteTopology.of ↑(default : X)
  simpa [nhds_coe_eq, nhds_discrete, CofiniteTopology.nhds_eq, Equiv.symm_apply_eq,
    Set.compl_def, Set.mem_singleton_iff] using (finite_singleton _).infinite_compl
/-
**OnePoint.** 是 Mathlib 中的一个实例，位于命名空间 `OnePoint`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : Type*) [TopologicalSpace X] [DiscreteTopology X] :
    TotallySeparatedSpace (OnePoint X) where
  isTotallySeparated_univ x _ y _ hxy := by
    cases x with
    | infty =>
      refine ⟨{y}ᶜ, {y}, isOpen_compl_singleton, ?_, hxy, rfl, (compl_union_self _).symm.subset,
        disjoint_compl_left⟩
      rw [OnePoint.isOpen_iff_of_notMem]
      exacts [isOpen_discrete _, hxy]
    | coe val =>
      refine ⟨{some val}, {some val}ᶜ, ?_, isOpen_compl_singleton, rfl, hxy.symm, by simp,
        disjoint_compl_right⟩
      rw [OnePoint.isOpen_iff_of_notMem]
      exacts [isOpen_discrete _, (Option.some_ne_none val).symm]

section Uniqueness

variable [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
  (y : Y) (f : X → Y) (hf : IsEmbedding f) (hy : range f = {y}ᶜ)

open scoped Classical in
/-- If `f` embeds `X` into a compact Hausdorff space `Y`, and has exactly one point outside its
range, then `(Y, f)` is the one-point compactification of `X`. -/
/-
**OnePoint.equivOfIsEmbeddingOfRangeEq** 是 Mathlib 中的一个定义，位于命名空间 `OnePoint`。
形式化陈述：equivOfIsEmbeddingOfRangeEq : OnePoint X ≃ₜ Y
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.t2Space`：Topology.IsEmbedding.t2Space [TopologicalS
pace Y] [T2Space Y] {f : X -> Y} (hf : IsEmbedding f) : T2Space X
· 使用定理 `OnePoint.instCompactSpace`：∀ {X : Type u_1} [inst : TopologicalSpace X],
 CompactSpace (OnePoint X)

--- 原说明 ---
If `f` embeds `X` into a compact Hausdorff space `Y`, and has exactly one point 
outside its
range, then `(Y, f)` is the one-point compactification of `X`.
-/
noncomputable def equivOfIsEmbeddingOfRangeEq :
    OnePoint X ≃ₜ Y :=
  have _i := hf.t2Space
  have : Tendsto f (coclosedCompact X) (𝓝 y) := by
    rw [coclosedCompact_eq_cocompact, hasBasis_cocompact.tendsto_left_iff]
    intro N hN
    obtain ⟨U, hU₁, hU₂, hU₃⟩ := mem_nhds_iff.mp hN
    refine ⟨f⁻¹' Uᶜ, ?_, by simpa using (mapsTo_preimage f U).mono_right hU₁⟩
    rw [hf.isCompact_iff, image_preimage_eq_iff.mpr (by simpa [hy])]
    exact (isClosed_compl_iff.mpr hU₂).isCompact
  let e : OnePoint X ≃ Y :=
    { toFun := fun p ↦ p.elim y f
      invFun := fun q ↦ if hq : q = y then ∞ else ↑(show q ∈ range f by simpa [hy]).choose
      left_inv := fun p ↦ by
        induction p using OnePoint.rec with
        | infty => simp
        | coe p =>
          have hp : f p ≠ y := by simpa [hy] using mem_range_self (f := f) p
          simpa [hp] using hf.injective (mem_range_self p).choose_spec
      right_inv := fun q ↦ by
        rcases eq_or_ne q y with rfl | hq
        · simp
        · have hq' : q ∈ range f := by simpa [hy]
          simpa [hq] using hq'.choose_spec }
  Continuous.homeoOfEquivCompactToT2 <| (continuous_iff e).mpr ⟨this, hf.continuous⟩

@[simp]
/-
**OnePoint.equivOfIsEmbeddingOfRangeEq_apply_coe** 是 Mathlib 中的一个引理，位于命名空间 `OneP
oint`。
形式化陈述：equivOfIsEmbeddingOfRangeEq_apply_coe (x : X) : equivOfIsEmbeddingOfRangeE
q y f hf hy x = f x
参数：x : X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma equivOfIsEmbeddingOfRangeEq_apply_coe (x : X) :
    equivOfIsEmbeddingOfRangeEq y f hf hy x = f x :=
  rfl

@[simp]
/-
**OnePoint.equivOfIsEmbeddingOfRangeEq_apply_infty** 是 Mathlib 中的一个引理，位于命名空间 `On
ePoint`。
形式化陈述：equivOfIsEmbeddingOfRangeEq_apply_infty : equivOfIsEmbeddingOfRangeEq y f 
hf hy ∞ = y
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma equivOfIsEmbeddingOfRangeEq_apply_infty :
    equivOfIsEmbeddingOfRangeEq y f hf hy ∞ = y :=
  rfl

end Uniqueness

end OnePoint

namespace Homeomorph

variable [TopologicalSpace X] [TopologicalSpace Y]

open OnePoint

/-- Extend a homeomorphism of topological spaces
to the homeomorphism of their one point compactifications. -/
@[simps]
/-
**Homeomorph.onePointCongr** 是 Mathlib 中的一个定义，位于命名空间 `Homeomorph`。
形式化陈述：onePointCongr (h : X ≃ₜ Y) : OnePoint X ≃ₜ OnePoint Y where __
参数：h : X ≃ₜ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Extend a homeomorphism of topological spaces
to the homeomorphism of their one point compactifications.
-/
def onePointCongr (h : X ≃ₜ Y) : OnePoint X ≃ₜ OnePoint Y where
  __ := h.toEquiv.withTopCongr
  toFun := OnePoint.map h
  invFun := OnePoint.map h.symm
  continuous_toFun := continuous_map (map_continuous h) h.map_coclosedCompact.le
  continuous_invFun := continuous_map (map_continuous h.symm) h.symm.map_coclosedCompact.le

end Homeomorph

/-- A concrete counterexample shows that `Continuous.homeoOfEquivCompactToT2`
cannot be generalized from `T2Space` to `T1Space`.

Let `α = OnePoint ℕ` be the one-point compactification of `ℕ`, and let `β` be the same space
`OnePoint ℕ` with the cofinite topology.  Then `α` is compact, `β` is T1, and the identity map
`id : α → β` is a continuous equivalence that is not a homeomorphism.
-/
/-
**Continuous.homeoOfEquivCompactToT2.t1_counterexample** 是 Mathlib 中的一个定理，位于命名空间
 ``。
形式化陈述：Continuous.homeoOfEquivCompactToT2.t1_counterexample : exists (α β : Type)
 (_ : TopologicalSpace α) (_ : TopologicalSpace β), CompactSpace α ∧ T1Space β ∧
 exists f : α ≃ β, Continuous f ∧ ¬Continuous f.symm
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `OnePoint.instCompactSpace`：∀ {X : Type u_1} [inst : TopologicalSpace X],
 CompactSpace (OnePoint X)
· 使用定理 `instT1SpaceCofiniteTopology`：∀ {X : Type u_1}, T1Space (CofiniteTopology
 X)
· 使用定理 `CofiniteTopology.continuous_of`：CofiniteTopology.continuous_of [T1Space 
X] : Continuous (@CofiniteTopology.of X)
· 使用定理 `OnePoint.instT1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T1Sp
ace X], T1Space (OnePoint X)
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `DiscreteTopology.toT2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X]
 [DiscreteTopology X], T2Space X
· 使用定理 `instDiscreteTopologyNat`：DiscreteTopology ℕ
· 使用定理 `OnePoint.not_continuous_cofiniteTopology_of_symm`：not_continuous_cofinit
eTopology_of_symm [Infinite X] [DiscreteTopology X] : ¬Continuous (@CofiniteTopo
logy.of (OnePoint X)).symm
· 使用定理 `instInfiniteNat`：Infinite ℕ

--- 原说明 ---
A concrete counterexample shows that `Continuous.homeoOfEquivCompactToT2`
cannot be generalized from `T2Space` to `T1Space`.

Let `α = OnePoint ℕ` be the one-point compactification of `ℕ`, and let `β` be th
e same space
`OnePoint ℕ` with the cofinite topology.  Then `α` is compact, `β` is T1, and th
e identity map
`id : α → β` is a continuous equivalence that is not a homeomorphism.
-/
theorem Continuous.homeoOfEquivCompactToT2.t1_counterexample :
    ∃ (α β : Type) (_ : TopologicalSpace α) (_ : TopologicalSpace β),
      CompactSpace α ∧ T1Space β ∧ ∃ f : α ≃ β, Continuous f ∧ ¬Continuous f.symm :=
  ⟨OnePoint ℕ, CofiniteTopology (OnePoint ℕ), inferInstance, inferInstance, inferInstance,
    inferInstance, CofiniteTopology.of, CofiniteTopology.continuous_of,
    OnePoint.not_continuous_cofiniteTopology_of_symm⟩
