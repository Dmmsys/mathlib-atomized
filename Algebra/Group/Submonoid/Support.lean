/-
Copyright (c) 2026 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
-/
module

public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Algebra.Group.Subgroup.Lattice

import Mathlib.Tactic.ApplyFun

/-!
# Supports of submonoids

Let `G` be an (additive) group, and let `M` be a submonoid of `G`.
The *support* of `M` is `M ∩ -M`, the largest subgroup of `G` contained in `M`.
A submonoid `C` is *pointed*, or a *positive cone*, if it has zero support.
A submonoid `C` is *spanning* if the subgroup it generates is `G` itself.

The names for these concepts are taken from the theory of convex cones.

## Main definitions

* `AddSubmonoid.support`: the support of a submonoid.
* `AddSubmonoid.IsPointed`: typeclass for submonoids with zero support.
* `AddSubmonoid.IsSpanning`: typeclass for submonoids generating the whole group.

-/

@[expose] public section

namespace Submonoid

open scoped Pointwise

variable {G : Type*} [Group G] (M : Submonoid G)

/--
The support of a submonoid `M` of a group `G` is `M ∩ M⁻¹`,
the largest subgroup of `G` contained in `M`.
-/
@[to_additive (attr := simps!)
/-- The support of a submonoid `M` of a group `G` is `M ∩ -M`,
the largest subgroup of `G` contained in `M`. -/]
/-
**Submonoid.mulSupport** 是 Mathlib 中的一个定义，位于命名空间 `Submonoid`。
形式化陈述：mulSupport : Subgroup G where toSubmonoid
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def mulSupport : Subgroup G where
  toSubmonoid := M ⊓ M⁻¹
  inv_mem' := by aesop

variable {M} in
@[to_additive (attr := simp)]
/-
**Submonoid.mem_mulSupport** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：mem_mulSupport {x} : x in M.mulSupport ↔ x in M ∧ x⁻¹ in M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_mulSupport {x} : x ∈ M.mulSupport ↔ x ∈ M ∧ x⁻¹ ∈ M := .rfl

@[to_additive (attr := simp)]
/-
**Submonoid.mulSupport_toSubmonoid** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：mulSupport_toSubmonoid : M.mulSupport.toSubmonoid = M ⊓ M⁻¹
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mulSupport_toSubmonoid : M.mulSupport.toSubmonoid = M ⊓ M⁻¹ := rfl

/-- The support of a submonoid is the largest subgroup it contains. -/
@[to_additive /-- The support of a submonoid is the largest subgroup it contains. -/]
/-
**Submonoid._root_.Subgroup.gc_toSubmonoid_mulSupport** 是 Mathlib 中的一个定理，位于命名空间 
`Submonoid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The support of a submonoid is the largest subgroup it contains.
-/
theorem _root_.Subgroup.gc_toSubmonoid_mulSupport :
    GaloisConnection (α := Subgroup G) Subgroup.toSubmonoid mulSupport :=
  fun _ _ ↦ ⟨fun _ _ ↦ by aesop, fun h _ hx ↦ (h hx).1⟩

variable {M}

variable (M) in
/-- A submonoid is pointed if it has zero support. -/
@[to_additive /-- A submonoid is pointed if it has zero support. -/]
/-
**Submonoid.IsMulPointed** 是 Mathlib 中的一个定义，位于命名空间 `Submonoid`。
形式化陈述：IsMulPointed
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A submonoid is pointed if it has zero support.
-/
def IsMulPointed := ∀ x ∈ M, x⁻¹ ∈ M → x = 1

namespace IsMulPointed

@[to_additive (attr := aesop 90%)]
/-
**Submonoid.IsMulPointed.mk** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid.IsMulPointed`。
形式化陈述：mk (h : forall x in M, x⁻¹ in M -> x = 1) : M.IsMulPointed
参数：h : forall x in M, x⁻¹ in M -> x = 1。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk (h : ∀ x ∈ M, x⁻¹ ∈ M → x = 1) : M.IsMulPointed := h -- for Aesop

@[to_additive (attr := aesop safe forward (immediate := [hM, hx₁]))]
/-
**Submonoid.IsMulPointed.eq_one_of_mem_of_inv_mem** 是 Mathlib 中的一个定理，位于命名空间 `Sub
monoid.IsMulPointed`。
形式化陈述：eq_one_of_mem_of_inv_mem (hM : M.IsMulPointed) {x : G} (hx₁ : x in M) (hx₂
 : x⁻¹ in M) : x = 1
参数：hM : M.IsMulPointed；hx₁ : x in M；hx₂ : x⁻¹ in M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eq_one_of_mem_of_inv_mem (hM : M.IsMulPointed)
    {x : G} (hx₁ : x ∈ M) (hx₂ : x⁻¹ ∈ M) : x = 1 := hM _ hx₁ hx₂

@[to_additive (attr := aesop safe forward (immediate := [hM, hx₂]))]
alias eq_one_of_mem_of_inv_mem₂ := eq_one_of_mem_of_inv_mem -- for Aesop

@[to_additive]
/-
**Submonoid.IsMulPointed._root_.isMulPointed_iff_mulSupport_eq_bot** 是 Mathlib 中
的一个定理，位于命名空间 `Submonoid.IsMulPointed`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.isMulPointed_iff_mulSupport_eq_bot : M.IsMulPointed ↔ M.mulSupport = ⊥ where
  mp := by aesop
  mpr h := fun x ↦ by
    apply_fun (x ∈ ·) at h
    aesop

@[to_additive (attr := simp)]
alias ⟨mulSupport_eq_bot, _⟩ := isMulPointed_iff_mulSupport_eq_bot

@[to_additive]
alias ⟨_, of_mulSupport_eq_bot⟩ := isMulPointed_iff_mulSupport_eq_bot

end IsMulPointed

variable (M) in
/-- A submonoid `M` of a group `G` is spanning if `M` generates `G` as a subgroup. -/
@[to_additive
/-- A submonoid `M` of a group `G` is spanning if `M` generates `G` as a subgroup. -/]
/-
**Submonoid.IsMulSpanning** 是 Mathlib 中的一个定义，位于命名空间 `Submonoid`。
形式化陈述：IsMulSpanning
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def IsMulSpanning := ∀ a : G, a ∈ M ∨ a⁻¹ ∈ M

namespace IsMulSpanning

@[to_additive (attr := aesop 90%)]
/-
**Submonoid.IsMulSpanning.mk** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid.IsMulSpanning`
。
形式化陈述：mk (h : forall a : G, a in M ∨ a⁻¹ in M) : M.IsMulSpanning
参数：h : forall a : G, a in M ∨ a⁻¹ in M。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk (h : ∀ a : G, a ∈ M ∨ a⁻¹ ∈ M) : M.IsMulSpanning := h -- for Aesop

@[to_additive (attr := aesop safe forward)]
/-
**Submonoid.IsMulSpanning.mem_or_inv_mem** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid.Is
MulSpanning`。
形式化陈述：mem_or_inv_mem (hM : M.IsMulSpanning) (a : G) : a in M ∨ a⁻¹ in M
参数：hM : M.IsMulSpanning；a : G。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mem_or_inv_mem (hM : M.IsMulSpanning) (a : G) : a ∈ M ∨ a⁻¹ ∈ M := by aesop

@[to_additive]
/-
**Submonoid.IsMulSpanning.of_le** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid.IsMulSpanni
ng`。
形式化陈述：of_le {N : Submonoid G} (hM : M.IsMulSpanning) (h : M <= N) : N.IsMulSpann
ing
参数：hM : M.IsMulSpanning；h : M <= N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.IsMulSpanning.mk`：mk (h : forall a : G, a in M ∨ a⁻¹ in M) : M
.IsMulSpanning
· 使用定理 `Submonoid.IsMulSpanning.mem_or_inv_mem`：mem_or_inv_mem (hM : M.IsMulSpan
ning) (a : G) : a in M ∨ a⁻¹ in M
-/
theorem of_le {N : Submonoid G} (hM : M.IsMulSpanning) (h : M ≤ N) :
    N.IsMulSpanning := by aesop

@[to_additive]
/-
**Submonoid.IsMulSpanning.maximal_isMulPointed** 是 Mathlib 中的一个定理，位于命名空间 `Submon
oid.IsMulSpanning`。
形式化陈述：maximal_isMulPointed (hMp : M.IsMulPointed) (hMs : M.IsMulSpanning) : Maxi
mal IsMulPointed M
参数：hMp : M.IsMulPointed；hMs : M.IsMulSpanning。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SetLike.le_def`：le_def {S T : A} : S <= T ↔ forall ⦃x : B⦄, x in S -> x 
in T
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `Submonoid.IsMulSpanning.mem_or_inv_mem`：mem_or_inv_mem (hM : M.IsMulSpan
ning) (a : G) : a in M ∨ a⁻¹ in M
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Submonoid.IsMulPointed.eq_one_of_mem_of_inv_mem`：eq_one_of_mem_of_inv_me
m (hM : M.IsMulPointed) {x : G} (hx₁ : x in M) (hx₂ : x⁻¹ in M) : x = 1
· 使用定理 `SubmonoidClass.toOneMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   On
eMemClass S M
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
-/
theorem maximal_isMulPointed (hMp : M.IsMulPointed) (hMs : M.IsMulSpanning) :
    Maximal IsMulPointed M :=
  ⟨hMp, fun N hN h ↦ by rw [SetLike.le_def] at h ⊢; aesop⟩

end Submonoid.IsMulSpanning

