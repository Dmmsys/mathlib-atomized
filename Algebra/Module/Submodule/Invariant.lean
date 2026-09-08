/-
Copyright (c) 2024 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Order.Sublattice

/-!
# The lattice of invariant submodules

In this file we defined the type `Module.End.invtSubmodule`, associated to a linear endomorphism of
a module. Its utility stems primarily from those occasions on which we wish to take advantage of the
lattice structure of invariant submodules.

See also `Mathlib/Algebra/Polynomial/Module/AEval.lean`.

-/

@[expose] public section

open Submodule (span)

namespace Module.End

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] (f g : End R M)

/-- Given an endomorphism, `f` of some module, this is the sublattice of all `f`-invariant
submodules. -/
/-
**Module.End.invtSubmodule** 是 Mathlib 中的一个定义，位于命名空间 `Module.End`。
形式化陈述：invtSubmodule : Sublattice (Submodule R M) where carrier
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an endomorphism, `f` of some module, this is the sublattice of all `f`-inv
ariant
submodules.
-/
def invtSubmodule : Sublattice (Submodule R M) where
  carrier := {p : Submodule R M | p ≤ p.comap f}
  supClosed' p hp q hq := sup_le_iff.mpr
    ⟨le_trans hp <| Submodule.comap_mono le_sup_left,
    le_trans hq <| Submodule.comap_mono le_sup_right⟩
  infClosed' p hp q hq := by
    simp only [Set.mem_ofPred_eq, Submodule.comap_inf, le_inf_iff]
    exact ⟨inf_le_of_left_le hp, inf_le_of_right_le hq⟩
/-
**Module.End.mem_invtSubmodule** 是 Mathlib 中的一个引理，位于命名空间 `Module.End`。
形式化陈述：mem_invtSubmodule {p : Submodule R M} : p in f.invtSubmodule ↔ p <= p.coma
p f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_invtSubmodule {p : Submodule R M} :
    p ∈ f.invtSubmodule ↔ p ≤ p.comap f :=
  Iff.rfl

/-- `p` is `f` invariant if and only if `p.map f ≤ p`. -/
/-
**Module.End.mem_invtSubmodule_iff_map_le** 是 Mathlib 中的一个定理，位于命名空间 `Module.End`
。
形式化陈述：mem_invtSubmodule_iff_map_le {p : Submodule R M} : p in f.invtSubmodule ↔ 
p.map f <= p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Submodule.map_le_iff_le_comap`：map_le_iff_le_comap {f : M ->ₛₗ[σ₁₂] M₂} 
{p : Submodule R M} {q : Submodule R₂ M₂} : map f p <= q ↔ p <= comap f q

--- 原说明 ---
`p` is `f` invariant if and only if `p.map f ≤ p`.
-/
theorem mem_invtSubmodule_iff_map_le {p : Submodule R M} :
    p ∈ f.invtSubmodule ↔ p.map f ≤ p := Submodule.map_le_iff_le_comap.symm

/-- `p` is `f` invariant if and only if `Set.MapsTo f p p`. -/
/-
**Module.End.mem_invtSubmodule_iff_mapsTo** 是 Mathlib 中的一个定理，位于命名空间 `Module.End`
。
形式化陈述：mem_invtSubmodule_iff_mapsTo {p : Submodule R M} : p in f.invtSubmodule ↔ 
Set.MapsTo f p p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
`p` is `f` invariant if and only if `Set.MapsTo f p p`.
-/
theorem mem_invtSubmodule_iff_mapsTo {p : Submodule R M} :
    p ∈ f.invtSubmodule ↔ Set.MapsTo f p p := Iff.rfl

alias ⟨_, _root_.Set.Mapsto.mem_invtSubmodule⟩ := mem_invtSubmodule_iff_mapsTo
/-
**Module.End.mem_invtSubmodule_iff_forall_mem_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `
Module.End`。
形式化陈述：mem_invtSubmodule_iff_forall_mem_of_mem {p : Submodule R M} : p in f.invtS
ubmodule ↔ forall x in p, f x in p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_invtSubmodule_iff_forall_mem_of_mem {p : Submodule R M} :
    p ∈ f.invtSubmodule ↔ ∀ x ∈ p, f x ∈ p :=
  Iff.rfl

/-- `p` is `f.symm` invariant if and only if `p ≤ p.map f`. -/
/-
**Module.End.mem_invtSubmodule_symm_iff_le_map** 是 Mathlib 中的一个引理，位于命名空间 `Module
.End`。
形式化陈述：mem_invtSubmodule_symm_iff_le_map {f : M ≃ₗ[R] M} {p : Submodule R M} : p 
in invtSubmodule f.symm ↔ p <= p.map (f : M ->ₗ[R] M)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Module.End.mem_invtSubmodule_iff_map_le`：mem_invtSubmodule_iff_map_le {p
 : Submodule R M} : p in f.invtSubmodule ↔ p.map f <= p
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.subset_symm_image`：∀ {α : Type u_3} {β : Type u_4} (e : α ≃ β) (s 
: Set α) (t : Set β), s ⊆ ⇑e.symm '' t ↔ ⇑e '' s ⊆ t

--- 原说明 ---
`p` is `f.symm` invariant if and only if `p ≤ p.map f`.
-/
lemma mem_invtSubmodule_symm_iff_le_map {f : M ≃ₗ[R] M} {p : Submodule R M} :
    p ∈ invtSubmodule f.symm ↔ p ≤ p.map (f : M →ₗ[R] M) :=
  (mem_invtSubmodule_iff_map_le _).trans (f.toEquiv.symm.subset_symm_image _ _).symm
/-
**Module.End.invtSubmodule_inf_invtSubmodule_le_invtSubmodule_add** 是 Mathlib 中的
一个引理，位于命名空间 `Module.End`。
形式化陈述：invtSubmodule_inf_invtSubmodule_le_invtSubmodule_add : f.invtSubmodule ⊓ g
.invtSubmodule <= (f + g).invtSubmodule
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.add_mem`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [inst
_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodule R M) {x y 
: M}, x…
-/
lemma invtSubmodule_inf_invtSubmodule_le_invtSubmodule_add :
    f.invtSubmodule ⊓ g.invtSubmodule ≤ (f + g).invtSubmodule :=
  fun p ⟨hfp, hgp⟩ _ hx ↦ p.add_mem (hfp hx) (hgp hx)

section CommRing

variable {R S : Type*} [Semiring R] [Semiring S] [Module R M] [Module S M]
  [DistribSMul S R] [SMulCommClass R S M] [IsScalarTower S R M] (f : End R M)

/-
**Module.End.invtSubmodule_le_invtSubmodule_smul** 是 Mathlib 中的一个引理，位于命名空间 `Modu
le.End`。
形式化陈述：invtSubmodule_le_invtSubmodule_smul (c : S) : f.invtSubmodule <= (c • f).i
nvtSubmodule
参数：c : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.smul_of_tower_mem`：smul_of_tower_mem [SMul S R] [SMul S M] [Is
ScalarTower S R M] (r : S) (h : x in p) : r • x in p
-/
lemma invtSubmodule_le_invtSubmodule_smul (c : S) : f.invtSubmodule ≤ (c • f).invtSubmodule :=
  fun p hfp _ hx ↦ p.smul_of_tower_mem c (hfp hx)

@[simp]
/-
**Module.End.invtSubmodule_smul** 是 Mathlib 中的一个引理，位于命名空间 `Module.End`。
形式化陈述：invtSubmodule_smul (c : Sˣ) : (c • f).invtSubmodule = f.invtSubmodule
参数：c : Sˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用引理 `Module.End.invtSubmodule_le_invtSubmodule_smul`：invtSubmodule_le_invtSub
module_smul (c : S) : f.invtSubmodule <= (c • f).invtSubmodule
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `Units.inv_mul`：inv_mul : (↑a⁻¹ * a : α) = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
lemma invtSubmodule_smul (c : Sˣ) : (c • f).invtSubmodule = f.invtSubmodule := by
  apply le_antisymm ?_ (invtSubmodule_le_invtSubmodule_smul f c.1)
  grw [invtSubmodule_le_invtSubmodule_smul (c.1 • f) c⁻¹.1]
  simp [smul_smul]

end CommRing

namespace invtSubmodule

variable {f}

/-
**Module.End.invtSubmodule.inf_mem** 是 Mathlib 中的一个引理，位于命名空间 `Module.End.invtSub
module`。
形式化陈述：inf_mem {p q : Submodule R M} (hp : p in f.invtSubmodule) (hq : q in f.inv
tSubmodule) : p ⊓ q in f.invtSubmodule
参数：hp : p in f.invtSubmodule；hq : q in f.invtSubmodule。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Sublattice.inf_mem`：inf_mem (ha : a in L) (hb : b in L) : a ⊓ b in L
-/
lemma inf_mem {p q : Submodule R M} (hp : p ∈ f.invtSubmodule) (hq : q ∈ f.invtSubmodule) :
    p ⊓ q ∈ f.invtSubmodule :=
  Sublattice.inf_mem hp hq
/-
**Module.End.invtSubmodule.sup_mem** 是 Mathlib 中的一个引理，位于命名空间 `Module.End.invtSub
module`。
形式化陈述：sup_mem {p q : Submodule R M} (hp : p in f.invtSubmodule) (hq : q in f.inv
tSubmodule) : p ⊔ q in f.invtSubmodule
参数：hp : p in f.invtSubmodule；hq : q in f.invtSubmodule。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Sublattice.sup_mem`：sup_mem (ha : a in L) (hb : b in L) : a ⊔ b in L
-/
lemma sup_mem {p q : Submodule R M} (hp : p ∈ f.invtSubmodule) (hq : q ∈ f.invtSubmodule) :
    p ⊔ q ∈ f.invtSubmodule :=
  Sublattice.sup_mem hp hq

variable (f)

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Module.End.invtSubmodule.top_mem** 是 Mathlib 中的一个定理，位于命名空间 `Module.End.invtSub
module`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : Semiring R] [inst_1 : AddCommMonoi
d M] [inst_2 : _root_.Module R M]   (f : Module.End R M), ⊤ ∈ f.invtSubmodule
参数：f : Module.End R M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
protected lemma top_mem : ⊤ ∈ f.invtSubmodule := by simp [invtSubmodule]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Module.End.invtSubmodule.bot_mem** 是 Mathlib 中的一个定理，位于命名空间 `Module.End.invtSub
module`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : Semiring R] [inst_1 : AddCommMonoi
d M] [inst_2 : _root_.Module R M]   (f : Module.End R M), ⊥ ∈ f.invtSubmodule
参数：f : Module.End R M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
protected lemma bot_mem : ⊥ ∈ f.invtSubmodule := by simp [invtSubmodule]
/-
**Module.End.invtSubmodule.** 是 Mathlib 中的一个实例，位于命名空间 `Module.End.invtSubmodule`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : BoundedOrder (f.invtSubmodule) where
  top := ⟨⊤, invtSubmodule.top_mem f⟩
  bot := ⟨⊥, invtSubmodule.bot_mem f⟩
  le_top := fun ⟨p, hp⟩ ↦ by simp
  bot_le := fun ⟨p, hp⟩ ↦ by simp

@[simp]
/-
**Module.End.invtSubmodule.zero** 是 Mathlib 中的一个定理，位于命名空间 `Module.End.invtSubmod
ule`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : Semiring R] [inst_1 : AddCommMonoi
d M] [inst_2 : _root_.Module R M],   Module.End.invtSubmodule 0 = ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Submodule.comap_zero`：comap_zero : comap (0 : M ->ₛₗ[σ₁₂] M₂) q = ⊤
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Sublattice.mk.congr_simp`：∀ {α : Type u_2} [inst : Lattice α] (carrier c
arrier_1 : Set α) (e_carrier : carrier = carrier_1)   (supClosed' : SupClosed ca
rrier) (infClo…
-/
protected lemma zero :
    (0 : End R M).invtSubmodule = ⊤ :=
  eq_top_iff.mpr fun x ↦ by simp [invtSubmodule]

@[simp]
/-
**Module.End.invtSubmodule.id** 是 Mathlib 中的一个定理，位于命名空间 `Module.End.invtSubmodul
e`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : Semiring R] [inst_1 : AddCommMonoi
d M] [inst_2 : _root_.Module R M],   Module.End.invtSubmodule LinearMap.id = ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Submodule.comap_id`：comap_id : comap (LinearMap.id : M ->ₗ[R] M) p = p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Sublattice.mk.congr_simp`：∀ {α : Type u_2} [inst : Lattice α] (carrier c
arrier_1 : Set α) (e_carrier : carrier = carrier_1)   (supClosed' : SupClosed ca
rrier) (infClo…
-/
protected lemma id :
    invtSubmodule (LinearMap.id : End R M) = ⊤ :=
  eq_top_iff.mpr fun x ↦ by simp [invtSubmodule]

@[simp]
/-
**Module.End.invtSubmodule.one** 是 Mathlib 中的一个定理，位于命名空间 `Module.End.invtSubmodu
le`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : Semiring R] [inst_1 : AddCommMonoi
d M] [inst_2 : _root_.Module R M],   Module.End.invtSubmodule 1 = ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.End.invtSubmodule.id`：∀ {R : Type u_1} {M : Type u_2} [inst : Sem
iring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M],   Module.End.i
nvtSubmodule Line…
-/
protected lemma one :
    invtSubmodule (1 : End R M) = ⊤ :=
  invtSubmodule.id

set_option backward.isDefEq.respectTransparency false in
/-
**Module.End.invtSubmodule.mk_eq_bot_iff** 是 Mathlib 中的一个定理，位于命名空间 `Module.End.i
nvtSubmodule`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : Semiring R] [inst_1 : AddCommMonoi
d M] [inst_2 : _root_.Module R M]   (f : Module.End R M) {p : Submodule R M} (hp
 : p ∈ f.invtSubmodule), ⟨p, hp⟩ = ⊥ ↔ p = ⊥
参数：f : Module.End R M；hp : p ∈ f.invtSubmodule。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.mk_eq_bot_iff`：mk_eq_bot_iff [OrderBot α] [OrderBot (Subtype p)]
 (hbot : p ⊥) {x : α} (hx : p x) : (⟨x, hx⟩ : Subtype p) = ⊥ ↔ x = ⊥
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
protected lemma mk_eq_bot_iff {p : Submodule R M} (hp : p ∈ f.invtSubmodule) :
    (⟨p, hp⟩ : f.invtSubmodule) = ⊥ ↔ p = ⊥ :=
  Subtype.mk_eq_bot_iff (by simp [invtSubmodule]) _

set_option backward.isDefEq.respectTransparency false in
/-
**Module.End.invtSubmodule.mk_eq_top_iff** 是 Mathlib 中的一个定理，位于命名空间 `Module.End.i
nvtSubmodule`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : Semiring R] [inst_1 : AddCommMonoi
d M] [inst_2 : _root_.Module R M]   (f : Module.End R M) {p : Submodule R M} (hp
 : p ∈ f.invtSubmodule), ⟨p, hp⟩ = ⊤ ↔ p = ⊤
参数：f : Module.End R M；hp : p ∈ f.invtSubmodule。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.mk_eq_top_iff`：∀ {α : Type u} {p : α → Prop} [inst : PartialOrde
r α] [inst_1 : OrderTop α] [inst_2 : OrderTop (Subtype p)],   p ⊤ → ∀ {x : α} (h
x : p x), ⟨…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
protected lemma mk_eq_top_iff {p : Submodule R M} (hp : p ∈ f.invtSubmodule) :
    (⟨p, hp⟩ : f.invtSubmodule) = ⊤ ↔ p = ⊤ :=
  Subtype.mk_eq_top_iff (by simp [invtSubmodule]) _

@[simp]
/-
**Module.End.invtSubmodule.disjoint_mk_iff** 是 Mathlib 中的一个定理，位于命名空间 `Module.End
.invtSubmodule`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : Semiring R] [inst_1 : AddCommMonoi
d M] [inst_2 : _root_.Module R M]   (f : Module.End R M) {p q : Submodule R M} (
hp : p ∈ f.invtSubmodule) (hq : q ∈ f.invtSubmodule),   Disjoint ⟨p, hp⟩ ⟨q, hq⟩
 ↔ Disjoint p q
参数：f : Module.End R M；hp : p ∈ f.invtSubmodule；hq : q ∈ f.invtSubmodule。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `disjoint_iff`：disjoint_iff : Disjoint a b ↔ a ⊓ b = ⊥
· 使用定理 `Sublattice.infClosed`：∀ {α : Type u_2} [inst : Lattice α] (L : Sublattic
e α), InfClosed ↑L
· 使用定理 `Sublattice.mk_inf_mk`：∀ {α : Type u_2} [inst : Lattice α] {L : Sublattic
e α} (a b : α) (ha : a ∈ L) (hb : b ∈ L),   ⟨a, ha⟩ ⊓ ⟨b, hb⟩ = ⟨a ⊓ b, ⋯⟩
· 使用定理 `Subtype.mk_eq_bot_iff`：mk_eq_bot_iff [OrderBot α] [OrderBot (Subtype p)]
 (hbot : p ⊥) {x : α} (hx : p x) : (⟨x, hx⟩ : Subtype p) = ⊥ ↔ x = ⊥
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
protected lemma disjoint_mk_iff {p q : Submodule R M}
    (hp : p ∈ f.invtSubmodule) (hq : q ∈ f.invtSubmodule) :
    Disjoint (α := f.invtSubmodule) ⟨p, hp⟩ ⟨q, hq⟩ ↔ Disjoint p q := by
  rw [disjoint_iff, disjoint_iff, Sublattice.mk_inf_mk,
    Subtype.mk_eq_bot_iff (⊥ : f.invtSubmodule).property]
/-
**Module.End.invtSubmodule.disjoint_iff** 是 Mathlib 中的一个定理，位于命名空间 `Module.End.in
vtSubmodule`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : Semiring R] [inst_1 : AddCommMonoi
d M] [inst_2 : _root_.Module R M]   (f : Module.End R M) {p q : ↥f.invtSubmodule
}, Disjoint p q ↔ Disjoint ↑p ↑q
参数：f : Module.End R M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
protected lemma disjoint_iff {p q : f.invtSubmodule} :
    Disjoint p q ↔ Disjoint (p : Submodule R M) (q : Submodule R M) := by
  obtain ⟨p, hp⟩ := p
  obtain ⟨q, hq⟩ := q
  simp

@[simp]
/-
**Module.End.invtSubmodule.codisjoint_mk_iff** 是 Mathlib 中的一个定理，位于命名空间 `Module.E
nd.invtSubmodule`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : Semiring R] [inst_1 : AddCommMonoi
d M] [inst_2 : _root_.Module R M]   (f : Module.End R M) {p q : Submodule R M} (
hp : p ∈ f.invtSubmodule) (hq : q ∈ f.invtSubmodule),   Codisjoint ⟨p, hp⟩ ⟨q, h
q⟩ ↔ Codisjoint p q
参数：f : Module.End R M；hp : p ∈ f.invtSubmodule；hq : q ∈ f.invtSubmodule。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `codisjoint_iff`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : Ord
erTop α] {a b : α}, Codisjoint a b ↔ a ⊔ b = ⊤
· 使用定理 `Sublattice.supClosed`：∀ {α : Type u_2} [inst : Lattice α] (L : Sublattic
e α), SupClosed ↑L
· 使用定理 `Sublattice.mk_sup_mk`：∀ {α : Type u_2} [inst : Lattice α] {L : Sublattic
e α} (a b : α) (ha : a ∈ L) (hb : b ∈ L),   ⟨a, ha⟩ ⊔ ⟨b, hb⟩ = ⟨a ⊔ b, ⋯⟩
· 使用定理 `Subtype.mk_eq_top_iff`：∀ {α : Type u} {p : α → Prop} [inst : PartialOrde
r α] [inst_1 : OrderTop α] [inst_2 : OrderTop (Subtype p)],   p ⊤ → ∀ {x : α} (h
x : p x), ⟨…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
protected lemma codisjoint_mk_iff {p q : Submodule R M}
    (hp : p ∈ f.invtSubmodule) (hq : q ∈ f.invtSubmodule) :
    Codisjoint (α := f.invtSubmodule) ⟨p, hp⟩ ⟨q, hq⟩ ↔ Codisjoint p q := by
  rw [codisjoint_iff, codisjoint_iff, Sublattice.mk_sup_mk,
    Subtype.mk_eq_top_iff (⊤ : f.invtSubmodule).property]
/-
**Module.End.invtSubmodule.codisjoint_iff** 是 Mathlib 中的一个定理，位于命名空间 `Module.End.
invtSubmodule`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : Semiring R] [inst_1 : AddCommMonoi
d M] [inst_2 : _root_.Module R M]   (f : Module.End R M) {p q : ↥f.invtSubmodule
}, Codisjoint p q ↔ Codisjoint ↑p ↑q
参数：f : Module.End R M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
protected lemma codisjoint_iff {p q : f.invtSubmodule} :
    Codisjoint p q ↔ Codisjoint (p : Submodule R M) (q : Submodule R M) := by
  obtain ⟨p, hp⟩ := p
  obtain ⟨q, hq⟩ := q
  simp

@[simp]
/-
**Module.End.invtSubmodule.isCompl_mk_iff** 是 Mathlib 中的一个定理，位于命名空间 `Module.End.
invtSubmodule`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : Semiring R] [inst_1 : AddCommMonoi
d M] [inst_2 : _root_.Module R M]   (f : Module.End R M) {p q : Submodule R M} (
hp : p ∈ f.invtSubmodule) (hq : q ∈ f.invtSubmodule),   IsCompl ⟨p, hp⟩ ⟨q, hq⟩ 
↔ IsCompl p q
参数：f : Module.End R M；hp : p ∈ f.invtSubmodule；hq : q ∈ f.invtSubmodule。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
protected lemma isCompl_mk_iff {p q : Submodule R M}
    (hp : p ∈ f.invtSubmodule) (hq : q ∈ f.invtSubmodule) :
    IsCompl (α := f.invtSubmodule) ⟨p, hp⟩ ⟨q, hq⟩ ↔ IsCompl p q := by
  simp [isCompl_iff]
/-
**Module.End.invtSubmodule.isCompl_iff** 是 Mathlib 中的一个定理，位于命名空间 `Module.End.inv
tSubmodule`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : Semiring R] [inst_1 : AddCommMonoi
d M] [inst_2 : _root_.Module R M]   (f : Module.End R M) {p q : ↥f.invtSubmodule
}, IsCompl p q ↔ IsCompl ↑p ↑q
参数：f : Module.End R M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
protected lemma isCompl_iff {p q : f.invtSubmodule} :
    IsCompl p q ↔ IsCompl (p : Submodule R M) (q : Submodule R M) := by
  obtain ⟨p, hp⟩ := p
  obtain ⟨q, hq⟩ := q
  simp

set_option backward.isDefEq.respectTransparency false in
/-
**Module.End.invtSubmodule.map_subtype_mem_of_mem_invtSubmodule** 是 Mathlib 中的一个
引理，位于命名空间 `Module.End.invtSubmodule`。
形式化陈述：map_subtype_mem_of_mem_invtSubmodule {p : Submodule R M} (hp : p in f.invt
Submodule) {q : Submodule R p} (hq : q in invtSubmodule (LinearMap.restrict f hp
)) : Submodule.map p.subtype q in f.invtSubmodule
参数：hp : p in f.invtSubmodule；hq : q in invtSubmodule (LinearMap.restrict f hp)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `LinearMap.restrict_apply`：restrict_apply {f : M ->ₛₗ[σ₁₂] M₂} {p : Submo
dule R M} {q : Submodule R₂ M₂} (hf : forall x in p, f x in q) (x : p) : f.restr
ict hf x = ⟨f …
· 使用定理 `Submodule.mem_comap`：mem_comap {f : M ->ₛₗ[σ₁₂] M₂} {p : Submodule R₂ M₂
} : x in comap f p ↔ f x in p
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
-/
lemma map_subtype_mem_of_mem_invtSubmodule {p : Submodule R M} (hp : p ∈ f.invtSubmodule)
    {q : Submodule R p} (hq : q ∈ invtSubmodule (LinearMap.restrict f hp)) :
    Submodule.map p.subtype q ∈ f.invtSubmodule := by
  rintro - ⟨⟨x, hx⟩, hx', rfl⟩
  specialize hq hx'
  rw [Submodule.mem_comap, LinearMap.restrict_apply] at hq
  simpa [hq] using hp hx
/-
**Module.End.invtSubmodule.comp** 是 Mathlib 中的一个定理，位于命名空间 `Module.End.invtSubmod
ule`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : Semiring R] [inst_1 : AddCommMonoi
d M] [inst_2 : _root_.Module R M]   (f : Module.End R M) {p : Submodule R M} {g 
: Module.End R M},   p ∈ f.invtSubmodule → p ∈ g.invtSubmodule → p ∈ Module.End.
invtSubmodule (f ∘ₗ g)
参数：f : Module.End R M；f ∘ₗ g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected lemma comp {p : Submodule R M} {g : End R M}
    (hf : p ∈ f.invtSubmodule) (hg : p ∈ g.invtSubmodule) :
    p ∈ invtSubmodule (f ∘ₗ g) :=
  fun _ hx ↦ hf (hg hx)
/-
**Module.End.invtSubmodule._root_.LinearEquiv.map_mem_invtSubmodule_conj_iff** 是
 Mathlib 中的一个引理，位于命名空间 `Module.End.invtSubmodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma _root_.LinearEquiv.map_mem_invtSubmodule_conj_iff {R M N : Type*} [CommSemiring R]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N] {f : End R M}
    {e : M ≃ₗ[R] N} {p : Submodule R M} :
    p.map (e : M →ₗ[R] N) ∈ (e.conj f).invtSubmodule ↔ p ∈ f.invtSubmodule := by
  have : e.symm.toLinearMap ∘ₗ ((e ∘ₗ f) ∘ₗ e.symm.toLinearMap) ∘ₗ e = f := by ext; simp
  rw [LinearEquiv.conj_apply, mem_invtSubmodule, mem_invtSubmodule, Submodule.map_le_iff_le_comap,
    Submodule.map_equiv_eq_comap_symm, ← Submodule.comap_comp, ← Submodule.comap_comp, this]
/-
**Module.End.invtSubmodule._root_.LinearEquiv.map_mem_invtSubmodule_iff** 是 Math
lib 中的一个引理，位于命名空间 `Module.End.invtSubmodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.LinearEquiv.map_mem_invtSubmodule_iff {R M N : Type*} [CommSemiring R]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N] {f : End R N}
    {e : M ≃ₗ[R] N} {p : Submodule R M} :
    p.map (e : M →ₗ[R] N) ∈ f.invtSubmodule ↔ p ∈ (e.symm.conj f).invtSubmodule := by
  simp [← e.map_mem_invtSubmodule_conj_iff]

end invtSubmodule

variable (R) in
/-
**Module.End.span_orbit_mem_invtSubmodule** 是 Mathlib 中的一个引理，位于命名空间 `Module.End`
。
形式化陈述：span_orbit_mem_invtSubmodule {G : Type*} [Monoid G] [DistribMulAction G M]
 [SMulCommClass G R M] (x : M) (g : G) : span R (MulAction.orbit G x) in invtSub
module (DistribSMul.toLinearMap R M g)
参数：x : M；g : G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Module.End.mem_invtSubmodule`：mem_invtSubmodule {p : Submodule R M} : p 
in f.invtSubmodule ↔ p <= p.comap f
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
· 使用定理 `Submodule.comap_coe`：comap_coe (f : M ->ₛₗ[σ₁₂] M₂) (p : Submodule R₂ M₂
) : (comap f p : Set M) = f ⁻¹' p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `DistribSMul.toLinearMap_apply`：∀ (R : Type u_1) {S : Type u_3} (M : Type
 u_4) [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R
 M] [inst_3 : Distr…
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `MulAction.mem_orbit_of_mem_orbit`：mem_orbit_of_mem_orbit {a₁ a₂ : α} (m 
: M) (h : a₂ in orbit M a₁) : m • a₂ in orbit M a₁
-/
lemma span_orbit_mem_invtSubmodule {G : Type*}
    [Monoid G] [DistribMulAction G M] [SMulCommClass G R M] (x : M) (g : G) :
    span R (MulAction.orbit G x) ∈ invtSubmodule (DistribSMul.toLinearMap R M g) := by
  rw [mem_invtSubmodule, Submodule.span_le, Submodule.comap_coe]
  intro y hy
  simp only [Set.mem_preimage, DistribSMul.toLinearMap_apply, SetLike.mem_coe]
  exact Submodule.subset_span <| MulAction.mem_orbit_of_mem_orbit g hy

end Module.End

