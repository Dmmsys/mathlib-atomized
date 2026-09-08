/-
Copyright (c) 2021 Roberto Alvarez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Roberto Alvarez
-/
module

public import Mathlib.Algebra.Group.Ext
public import Mathlib.Algebra.Group.TransferInstance
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import Mathlib.GroupTheory.EckmannHilton

/-!
# `n`th homotopy group

We define the `n`th homotopy group at `x : X`, `π_n X x`, as the equivalence classes
of functions from the `n`-dimensional cube to the topological space `X`
that send the boundary to the base point `x`, up to homotopic equivalence.
Note that such functions are generalized loops `GenLoop (Fin n) x`; in particular
`GenLoop (Fin 1) x ≃ Path x x`.

We show that `π_0 X x` is equivalent to the path-connected components, and
that `π_1 X x` is equivalent to the fundamental group at `x`.
We provide a group instance using path composition and show commutativity when `n > 1`.

## definitions

* `GenLoop N x` is the type of continuous functions `I^N → X` that send the boundary to `x`,
* `HomotopyGroup.Pi n X x` denoted `π_ n X x` is the quotient of `GenLoop (Fin n) x` by
  homotopy relative to the boundary,
* group instance `Group (π_(n+1) X x)`,
* commutative group instance `CommGroup (π_(n+2) X x)`.

TODO:
* `Ω^M (Ω^N X) ≃ₜ Ω^(M⊕N) X`, and `Ω^M X ≃ₜ Ω^N X` when `M ≃ N`. Similarly for `π_`.
* Examples with `𝕊^n`: `π_n (𝕊^n) = ℤ`, `π_m (𝕊^n)` trivial for `m < n`.
* Actions of π_1 on π_n.
* Lie algebra: `⁅π_(n+1), π_(m+1)⁆` contained in `π_(n+m+1)`.

-/

@[expose] public section


open scoped unitInterval Topology

open Homeomorph

noncomputable section

/-- `I^N` is notation (in the Topology namespace) for `N → I`,
i.e. the unit cube indexed by a type `N`. -/
scoped[Topology] notation "I^" N => N → I

namespace Cube

/-- The points in a cube with at least one projection equal to 0 or 1. -/
/-
**Cube.boundary** 是 Mathlib 中的一个定义，位于命名空间 `Cube`。
形式化陈述：boundary (N : Type*) : Set (I^N)
参数：N : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The points in a cube with at least one projection equal to 0 or 1.
-/
def boundary (N : Type*) : Set (I^N) :=
  {y | ∃ i, y i = 0 ∨ y i = 1}

variable {N : Type*} [DecidableEq N]

/-- The forward direction of the homeomorphism
  between the cube $I^N$ and $I × I^{N\setminus\{j\}}$. -/
/-
**Cube.splitAt** 是 Mathlib 中的一个缩写定义，位于命名空间 `Cube`。
形式化陈述：splitAt (i : N) : (I^N) ≃ₜ I × I^{ j // j != i }
参数：i : N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forward direction of the homeomorphism
  between the cube $I^N$ and $I × I^{N\setminus\{j\}}$.
-/
abbrev splitAt (i : N) : (I^N) ≃ₜ I × I^{ j // j ≠ i } :=
  funSplitAt I i

/-- The backward direction of the homeomorphism
  between the cube $I^N$ and $I × I^{N\setminus\{j\}}$. -/
/-
**Cube.insertAt** 是 Mathlib 中的一个缩写定义，位于命名空间 `Cube`。
形式化陈述：insertAt (i : N) : (I × I^{ j // j != i }) ≃ₜ I^N
参数：i : N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The backward direction of the homeomorphism
  between the cube $I^N$ and $I × I^{N\setminus\{j\}}$.
-/
abbrev insertAt (i : N) : (I × I^{ j // j ≠ i }) ≃ₜ I^N :=
  (funSplitAt I i).symm
/-
**Cube.insertAt_boundary** 是 Mathlib 中的一个定理，位于命名空间 `Cube`。
形式化陈述：insertAt_boundary (i : N) {t₀ : I} {t} (H : (t₀ = 0 ∨ t₀ = 1) ∨ t in bound
ary { j // j != i }) : insertAt i ⟨t₀, t⟩ in boundary N
参数：i : N；H : (t₀ = 0 ∨ t₀ = 1) ∨ t in boundary { j // j != i }。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.mpr_not`：∀ {p q : Prop}, p = q → ¬q → ¬p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Homeomorph.funSplitAt_symm_apply`：∀ (Y : Type u_2) [inst : TopologicalSp
ace Y] {ι : Type u_7} [inst_1 : DecidableEq ι] (i : ι)   (f : (fun a => Y) i × (
(j : { j // j ≠ i }) →…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Subtype.coe_eta`：coe_eta (a : { a // p a }) (h : p a) : mk (↑a) h = a
-/
theorem insertAt_boundary (i : N) {t₀ : I} {t}
    (H : (t₀ = 0 ∨ t₀ = 1) ∨ t ∈ boundary { j // j ≠ i }) : insertAt i ⟨t₀, t⟩ ∈ boundary N := by
  obtain H | ⟨j, H⟩ := H
  · use i; rwa [funSplitAt_symm_apply, dif_pos rfl]
  · use j; rwa [funSplitAt_symm_apply, dif_neg j.prop, Subtype.coe_eta]

end Cube

variable (N X : Type*) [TopologicalSpace X] (x : X)

/-- The space of paths with both endpoints equal to a specified point `x : X`.
Denoted as `Ω`, within the `Topology.Homotopy` namespace. -/
/-
**LoopSpace** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：LoopSpace
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The space of paths with both endpoints equal to a specified point `x : X`.
Denoted as `Ω`, within the `Topology.Homotopy` namespace.
-/
abbrev LoopSpace :=
  Path x x

@[inherit_doc] scoped[Topology.Homotopy] notation "Ω" => LoopSpace
/-
**LoopSpace.inhabited** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：LoopSpace.inhabited : Inhabited (Path x x)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance LoopSpace.inhabited : Inhabited (Path x x) :=
  ⟨Path.refl x⟩

/-- The `n`-dimensional generalized loops based at `x` in a space `X` are
  continuous functions `I^n → X` that sends the boundary to `x`.
  We allow an arbitrary indexing type `N` in place of `Fin n` here. -/
/-
**GenLoop** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：GenLoop : Set C(I^N, X)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `n`-dimensional generalized loops based at `x` in a space `X` are
  continuous functions `I^n → X` that sends the boundary to `x`.
  We allow an arbitrary indexing type `N` in place of `Fin n` here.
-/
def GenLoop : Set C(I^N, X) :=
  {p | ∀ y ∈ Cube.boundary N, p y = x}

@[inherit_doc] scoped[Topology.Homotopy] notation "Ω^" => GenLoop

open Topology.Homotopy

variable {N X x}

namespace GenLoop

/-
**GenLoop.instFunLike** 是 Mathlib 中的一个实例，位于命名空间 `GenLoop`。
形式化陈述：instFunLike : FunLike (Ω^ N X x) (I^N) X where coe f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instFunLike : FunLike (Ω^ N X x) (I^N) X where
  coe f := f.1
  coe_injective := fun ⟨⟨f, _⟩, _⟩ ⟨⟨g, _⟩, _⟩ _ ↦ by congr

@[simp]
/-
**GenLoop.coe_coe** 是 Mathlib 中的一个定理，位于命名空间 `GenLoop`。
形式化陈述：coe_coe (f : Ω^ N X x) : ⇑(f : C(I^N, X)) = f
参数：f : Ω^ N X x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_coe (f : Ω^ N X x) : ⇑(f : C(I^N, X)) = f := rfl

@[ext]
/-
**GenLoop.ext** 是 Mathlib 中的一个定理，位于命名空间 `GenLoop`。
形式化陈述：ext (f g : Ω^ N X x) (H : forall y, f y = g y) : f = g
参数：f g : Ω^ N X x；H : forall y, f y = g y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem ext (f g : Ω^ N X x) (H : ∀ y, f y = g y) : f = g :=
  DFunLike.coe_injective (funext H)

@[simp]
/-
**GenLoop.mk_apply** 是 Mathlib 中的一个定理，位于命名空间 `GenLoop`。
形式化陈述：mk_apply (f : C(I^N, X)) (H y) : (⟨f, H⟩ : Ω^ N X x) y = f y
参数：f : C(I^N, X)；H y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_apply (f : C(I^N, X)) (H y) : (⟨f, H⟩ : Ω^ N X x) y = f y :=
  rfl
/-
**GenLoop.instContinuousEval** 是 Mathlib 中的一个实例，位于命名空间 `GenLoop`。
形式化陈述：instContinuousEval : ContinuousEval (Ω^ N X x) (I^N) X
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousEval.of_continuous_forget`：ContinuousEval.of_continuous_forget
 {F' : Type*} [FunLike F' X Y] [TopologicalSpace F'] {f : F' -> F} (hc : Continu
ous f) (hf : forall g, ⇑(…
· 使用定理 `ContinuousMap.instContinuousEvalOfLocallyCompactPair`：∀ {X : Type u_2} {
Y : Type u_3} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y] [Locally
CompactPair X Y],   ContinuousEval C(X, Y)…
· 使用定理 `instLocallyCompactPairOfLocallyCompactSpace`：∀ {X : Type u_1} {Y : Type 
u_2} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y] [LocallyCompactSp
ace X],   LocallyCompactPair X Y
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `proper_of_compact`：∀ {α : Type u} [inst : PseudoMetricSpace α] [CompactS
pace α], ProperSpace α
· 使用定理 `ConditionallyCompleteLinearOrder.toCompactIccSpace`：∀ (α : Type u_2) [in
st : ConditionallyCompleteLinearOrder α] [inst_1 : TopologicalSpace α] [OrderTop
ology α],   CompactIccSpace α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
-/
instance instContinuousEval : ContinuousEval (Ω^ N X x) (I^N) X :=
  .of_continuous_forget continuous_subtype_val
/-
**GenLoop.instContinuousEvalConst** 是 Mathlib 中的一个实例，位于命名空间 `GenLoop`。
形式化陈述：instContinuousEvalConst : ContinuousEvalConst (Ω^ N X x) (I^N) X
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousEval.toContinuousEvalConst`：∀ {F : Type u_1} {X : Type u_2} {Y
 : Type u_3} [inst : FunLike F X Y] [inst_1 : TopologicalSpace F]   [inst_2 : To
pologicalSpace X] [inst_3 …
-/
instance instContinuousEvalConst : ContinuousEvalConst (Ω^ N X x) (I^N) X := inferInstance

/-- Copy of a `GenLoop` with a new map from the unit cube equal to the old one.
  Useful to fix definitional equalities. -/
/-
**GenLoop.copy** 是 Mathlib 中的一个定义，位于命名空间 `GenLoop`。
形式化陈述：copy (f : Ω^ N X x) (g : (I^N) -> X) (h : g = f) : Ω^ N X x
参数：f : Ω^ N X x；g : (I^N) -> X；h : g = f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Copy of a `GenLoop` with a new map from the unit cube equal to the old one.
  Useful to fix definitional equalities.
-/
def copy (f : Ω^ N X x) (g : (I^N) → X) (h : g = f) : Ω^ N X x :=
  ⟨⟨g, h.symm ▸ f.1.2⟩, by convert! f.2⟩
/-
**GenLoop.coe_copy** 是 Mathlib 中的一个定理，位于命名空间 `GenLoop`。
形式化陈述：coe_copy (f : Ω^ N X x) {g : (I^N) -> X} (h : g = f) : ⇑(copy f g h) = g
参数：f : Ω^ N X x；I^N；h : g = f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_copy (f : Ω^ N X x) {g : (I^N) → X} (h : g = f) : ⇑(copy f g h) = g :=
  rfl
/-
**GenLoop.copy_eq** 是 Mathlib 中的一个定理，位于命名空间 `GenLoop`。
形式化陈述：copy_eq (f : Ω^ N X x) {g : (I^N) -> X} (h : g = f) : copy f g h = f
参数：f : Ω^ N X x；I^N；h : g = f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GenLoop.ext`：ext (f g : Ω^ N X x) (H : forall y, f y = g y) : f = g
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
-/
theorem copy_eq (f : Ω^ N X x) {g : (I^N) → X} (h : g = f) : copy f g h = f := by
  ext x
  exact congr_fun h x
/-
**GenLoop.boundary** 是 Mathlib 中的一个定理，位于命名空间 `GenLoop`。
形式化陈述：boundary (f : Ω^ N X x) : forall y in Cube.boundary N, f y = x
参数：f : Ω^ N X x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem boundary (f : Ω^ N X x) : ∀ y ∈ Cube.boundary N, f y = x :=
  f.2

/-- The constant `GenLoop` at `x`. -/
/-
**GenLoop.const** 是 Mathlib 中的一个定义，位于命名空间 `GenLoop`。
形式化陈述：const : Ω^ N X x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The constant `GenLoop` at `x`.
-/
def const : Ω^ N X x :=
  ⟨ContinuousMap.const _ x, fun _ _ ↦ rfl⟩

@[simp]
/-
**GenLoop.const_apply** 是 Mathlib 中的一个定理，位于命名空间 `GenLoop`。
形式化陈述：const_apply {t} : (@const N X _ x) t = x
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem const_apply {t} : (@const N X _ x) t = x :=
  rfl
/-
**GenLoop.inhabited** 是 Mathlib 中的一个实例，位于命名空间 `GenLoop`。
形式化陈述：inhabited : Inhabited (Ω^ N X x)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance inhabited : Inhabited (Ω^ N X x) :=
  ⟨const⟩

section

variable {M} (x : X)

/-- Homeomorphism `Ω^M X ≃ₜ Ω^N X` if `M ≃ N`. -/
/-
**GenLoop.congr** 是 Mathlib 中的一个定义，位于命名空间 `GenLoop`。
形式化陈述：congr (e : M ≃ N) : Ω^ M X x ≃ₜ Ω^ N X x where toFun p
参数：e : M ≃ N。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Homeomorphism `Ω^M X ≃ₜ Ω^N X` if `M ≃ N`.
-/
def congr (e : M ≃ N) : Ω^ M X x ≃ₜ Ω^ N X x where
  toFun p := ⟨p.1.comp ⟨fun t m ↦ t (e m), by fun_prop⟩, fun y ⟨n, hn⟩ =>
    by simpa using p.2 _ ⟨e.symm n, by simpa using hn⟩⟩
  invFun p := ⟨p.1.comp ⟨fun t n ↦ t (e.symm n), by fun_prop⟩, fun y ⟨m, hm⟩ => by
    simpa using p.2 _ ⟨e m, by simpa using hm⟩⟩
  left_inv p := by ext t; simp
  right_inv p := by ext t; simp
/-
**GenLoop._root_.Cube.boundary_sum_iff** 是 Mathlib 中的一个定理，位于命名空间 `GenLoop`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Cube.boundary_sum_iff {y : I^(M ⊕ N)} :
    y ∈ Cube.boundary (M ⊕ N) ↔ y ∘ Sum.inl ∈ Cube.boundary M ∨ y ∘ Sum.inr ∈ Cube.boundary N := by
  constructor
  · rintro ⟨i | i, hi⟩
    · exact Or.inl ⟨i, hi⟩
    · exact Or.inr ⟨i, hi⟩
  · rintro (⟨m, hm⟩ | ⟨n, hn⟩)
    · exact ⟨Sum.inl m, hm⟩
    · exact ⟨Sum.inr n, hn⟩

@[simp]
/-
**GenLoop.apply_inl_apply_inr_eq_of_mem_boundary_sum** 是 Mathlib 中的一个引理，位于命名空间 `
GenLoop`。
形式化陈述：apply_inl_apply_inr_eq_of_mem_boundary_sum (p : Ω^ M (Ω^ N X x) const) {y 
: I^(M oplus N)} (hy : y in Cube.boundary (M oplus N)) : p (y ∘ Sum.inl) (y ∘ Su
m.inr) = x
参数：p : Ω^ M (Ω^ N X x) const；M oplus N；hy : y in Cube.boundary (M oplus N)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Cube.boundary_sum_iff`：∀ {N : Type u_1} {M : Type u_3} {y : M ⊕ N → ↑uni
tInterval},   y ∈ Cube.boundary (M ⊕ N) ↔ y ∘ Sum.inl ∈ Cube.boundary M ∨ y ∘ Su
m.inr ∈ Cub…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma apply_inl_apply_inr_eq_of_mem_boundary_sum
    (p : Ω^ M (Ω^ N X x) const) {y : I^(M ⊕ N)} (hy : y ∈ Cube.boundary (M ⊕ N)) :
    p (y ∘ Sum.inl) (y ∘ Sum.inr) = x := by
  rcases Cube.boundary_sum_iff.mp hy with hM | hN
  · have : p (y ∘ Sum.inl) = const := p.property (y ∘ Sum.inl) hM
    simp [this]
  · simpa using (p.val (y ∘ Sum.inl)).property (y ∘ Sum.inr) hN

/-- Curries an `(M ⊕ N)`-cube into an `M`-cube of `N`-cubes. -/
@[simps]
/-
**GenLoop.currySum** 是 Mathlib 中的一个定义，位于命名空间 `GenLoop`。
形式化陈述：currySum (q : Ω^ (M oplus N) X x) : C(I^M, Ω^ N X x) where toFun a
参数：q : Ω^ (M oplus N) X x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Curries an `(M ⊕ N)`-cube into an `M`-cube of `N`-cubes.
-/
def currySum (q : Ω^ (M ⊕ N) X x) : C(I^M, Ω^ N X x) where
  toFun a := ⟨(q.1.comp ⟨sumArrowHomeomorphProdArrow.invFun,
    sumArrowHomeomorphProdArrow.continuous_invFun⟩).curry.toFun a,
      fun _ hm => q.2 _ (Cube.boundary_sum_iff.mpr (Or.inr hm))⟩
  continuous_toFun := Continuous.subtype_mk (q.1.comp
    ⟨sumArrowHomeomorphProdArrow.invFun,
      sumArrowHomeomorphProdArrow.continuous_invFun⟩).curry.continuous_toFun _

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**GenLoop.currySum_apply_inl_inr** 是 Mathlib 中的一个引理，位于命名空间 `GenLoop`。
形式化陈述：currySum_apply_inl_inr (p : Ω^ (M oplus N) X x) (y : I^(M oplus N)) : curr
ySum x p (y ∘ Sum.inl) (y ∘ Sum.inr) = p y
参数：p : Ω^ (M oplus N) X x；y : I^(M oplus N)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Sum.elim_comp_inl_inr`：∀ {α : Type u_1} {β : Type u_2} {γ : Sort u_3} (f
 : α ⊕ β → γ), Sum.elim (f ∘ Sum.inl) (f ∘ Sum.inr) = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma currySum_apply_inl_inr (p : Ω^ (M ⊕ N) X x) (y : I^(M ⊕ N)) :
    currySum x p (y ∘ Sum.inl) (y ∘ Sum.inr) = p y := by
  simp [currySum, sumArrowHomeomorphProdArrow, Equiv.sumArrowEquivProdArrow]

@[fun_prop]
/-
**GenLoop.continuous_currySum** 是 Mathlib 中的一个引理，位于命名空间 `GenLoop`。
形式化陈述：continuous_currySum : Continuous (currySum x (M
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.continuous_of_continuous_uncurry`：continuous_of_continuous
_uncurry (f : X -> C(Y, Z)) (h : Continuous (Function.uncurry fun x y => f x y))
 : Continuous f
· 使用定理 `Continuous.subtype_mk`：Continuous.subtype_mk {f : Y -> X} (h : Continuou
s f) (hp : forall x, p (f x)) : Continuous fun x => (⟨f x, hp x⟩ : Subtype p)
· 使用定理 `Continuous.eval`：∀ {F : Type u_1} {X : Type u_2} {Y : Type u_3} {Z : Typ
e u_4} [inst : FunLike F X Y] [inst_1 : TopologicalSpace F]   [inst_2 : Topologi
calSp…
· 使用定理 `Continuous.fst`：Continuous.fst {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).1
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `Homeomorph.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologic
alSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y), Continuous ⇑h
· 使用定理 `Continuous.prodMk`：Continuous.prodMk {f : Z -> X} {g : Z -> Y} (hf : Con
tinuous f) (hg : Continuous g) : Continuous fun x => (f x, g x)
· 使用定理 `Continuous.snd`：Continuous.snd {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).2
-/
lemma continuous_currySum : Continuous (currySum x (M := M) (N := N)) :=
  ContinuousMap.continuous_of_continuous_uncurry _ <| Continuous.subtype_mk
    (ContinuousMap.continuous_of_continuous_uncurry _ (by dsimp; fun_prop)) _

/-- Given an element `p` in the `M`-iterated loop space of the `N`-iterated loop space of `X`,
this induces a continuous function from `I^M × I^N` to `X`. -/
/-
**GenLoop.uncurry** 是 Mathlib 中的一个定义，位于命名空间 `GenLoop`。
形式化陈述：{N : Type u_1} →   {X : Type u_2} →     [inst : TopologicalSpace X] →     
  {M : Type u_3} →         (x : X) → ↑(GenLoop M (↑(GenLoop N X x)) GenLoop.cons
t) → C((M → ↑unitInterval) × (N → ↑unitInterval), X)
参数：x : X；GenLoop M (↑(GenLoop N X x)) GenLoop.const；(M → ↑unitInterval) × (N → ↑
unitInterval), X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an element `p` in the `M`-iterated loop space of the `N`-iterated loop spa
ce of `X`,
this induces a continuous function from `I^M × I^N` to `X`.
-/
protected def uncurry (p : Ω^ M (Ω^ N X x) const) : C((I^M) × (I^N), X) :=
  .uncurry ⟨fun a => ⟨(p.1 a).1, ContinuousMap.continuous _⟩, (map_continuous p).subtype_val⟩

@[simp]
/-
**GenLoop.uncurry_apply** 是 Mathlib 中的一个引理，位于命名空间 `GenLoop`。
形式化陈述：uncurry_apply (p : Ω^ M (Ω^ N X x) const) (y : (I^M) × (I^N)) : GenLoop.un
curry x p y = p y.1 y.2
参数：p : Ω^ M (Ω^ N X x) const；y : (I^M) × (I^N)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma uncurry_apply (p : Ω^ M (Ω^ N X x) const) (y : (I^M) × (I^N)) :
    GenLoop.uncurry x p y = p y.1 y.2 := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- `Ω^M (Ω^N X) ≃ₜ Ω^(M ⊕ N) X`. -/
@[simps]
/-
**GenLoop.genLoopGenLoopEquiv** 是 Mathlib 中的一个定义，位于命名空间 `GenLoop`。
形式化陈述：genLoopGenLoopEquiv : Ω^ M (Ω^ N X x) GenLoop.const ≃ₜ Ω^ (M oplus N) X x 
where toFun p
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Ω^M (Ω^N X) ≃ₜ Ω^(M ⊕ N) X`.
-/
def genLoopGenLoopEquiv : Ω^ M (Ω^ N X x) GenLoop.const ≃ₜ Ω^ (M ⊕ N) X x where
  toFun p := ⟨(GenLoop.uncurry x p).comp ⟨sumArrowHomeomorphProdArrow.toFun,
    sumArrowHomeomorphProdArrow.continuous_toFun⟩, fun y hy => by simp [hy]⟩
  invFun q :=
    ⟨currySum x q, fun _ hm => by ext n; exact q.2 _ (Cube.boundary_sum_iff.mpr (Or.inl hm))⟩
  left_inv p := by ext; simp; rfl
  right_inv p := by ext; simp
  continuous_toFun := ((ContinuousMap.continuous_uncurry.comp' ((ContinuousMap.continuous_postcomp
    ⟨_, continuous_subtype_val⟩).comp continuous_subtype_val)).compCM
      continuous_const).subtype_mk _

end

/-- The "homotopic relative to boundary" relation between `GenLoop`s. -/
/-
**GenLoop.Homotopic** 是 Mathlib 中的一个定义，位于命名空间 `GenLoop`。
形式化陈述：Homotopic (f g : Ω^ N X x) : Prop
参数：f g : Ω^ N X x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The "homotopic relative to boundary" relation between `GenLoop`s.
-/
def Homotopic (f g : Ω^ N X x) : Prop :=
  f.1.HomotopicRel g.1 (Cube.boundary N)

namespace Homotopic

variable {f g h : Ω^ N X x}

@[refl]
/-
**GenLoop.Homotopic.refl** 是 Mathlib 中的一个定理，位于命名空间 `GenLoop.Homotopic`。
形式化陈述：refl (f : Ω^ N X x) : Homotopic f f
参数：f : Ω^ N X x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.HomotopicRel.refl`：refl (f : C(X, Y)) : HomotopicRel f f S
-/
theorem refl (f : Ω^ N X x) : Homotopic f f :=
  ContinuousMap.HomotopicRel.refl _

@[symm]
nonrec theorem symm (H : Homotopic f g) : Homotopic g f :=
  H.symm

@[trans]
nonrec theorem trans (H0 : Homotopic f g) (H1 : Homotopic g h) : Homotopic f h :=
  H0.trans H1
/-
**GenLoop.Homotopic.equiv** 是 Mathlib 中的一个定理，位于命名空间 `GenLoop.Homotopic`。
形式化陈述：equiv : Equivalence (@Homotopic N X _ x)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GenLoop.Homotopic.refl`：refl (f : Ω^ N X x) : Homotopic f f
· 使用定理 `GenLoop.Homotopic.symm`：∀ {N : Type u_1} {X : Type u_2} [inst : Topologi
calSpace X] {x : X} {f g : ↑(GenLoop N X x)},   GenLoop.Homotopic f g → GenLoop.
Homotopic g …
· 使用定理 `GenLoop.Homotopic.trans`：∀ {N : Type u_1} {X : Type u_2} [inst : Topolog
icalSpace X] {x : X} {f g h : ↑(GenLoop N X x)},   GenLoop.Homotopic f g → GenLo
op.Homotopic …
-/
theorem equiv : Equivalence (@Homotopic N X _ x) :=
  ⟨Homotopic.refl, Homotopic.symm, Homotopic.trans⟩
/-
**GenLoop.Homotopic.setoid** 是 Mathlib 中的一个实例，位于命名空间 `GenLoop.Homotopic`。
形式化陈述：setoid (N) (x : X) : Setoid (Ω^ N X x)
参数：N；x : X。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `GenLoop.Homotopic.equiv`：equiv : Equivalence (@Homotopic N X _ x)
-/
instance setoid (N) (x : X) : Setoid (Ω^ N X x) :=
  ⟨Homotopic, equiv⟩

end Homotopic

section LoopHomeo

variable [DecidableEq N]

/-- Loop from a generalized loop by currying $I^N → X$ into $I → (I^{N\setminus\{j\}} → X)$. -/
@[simps]
/-
**GenLoop.toLoop** 是 Mathlib 中的一个定义，位于命名空间 `GenLoop`。
形式化陈述：toLoop (i : N) (p : Ω^ N X x) : Ω (Ω^ { j // j != i } X x) const where toF
un t
参数：i : N；p : Ω^ N X x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Loop from a generalized loop by currying $I^N → X$ into $I → (I^{N\setminus\{j\}
} → X)$.
-/
def toLoop (i : N) (p : Ω^ N X x) : Ω (Ω^ { j // j ≠ i } X x) const where
  toFun t :=
    ⟨(p.val.comp (Cube.insertAt i)).curry t, fun y yH ↦
      p.property (Cube.insertAt i (t, y)) (Cube.insertAt_boundary i <| Or.inr yH)⟩
  source' := by ext t; refine p.property (Cube.insertAt i (0, t)) ⟨i, Or.inl ?_⟩; simp
  target' := by ext t; refine p.property (Cube.insertAt i (1, t)) ⟨i, Or.inr ?_⟩; simp
/-
**GenLoop.continuous_toLoop** 是 Mathlib 中的一个定理，位于命名空间 `GenLoop`。
形式化陈述：continuous_toLoop (i : N) : Continuous (@toLoop N X _ x _ i)
参数：i : N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Path.continuous_uncurry_iff`：continuous_uncurry_iff {Y} [TopologicalSpac
e Y] {g : Y -> Path x y} : Continuous ↿g ↔ Continuous g
· 使用定理 `Continuous.subtype_mk`：Continuous.subtype_mk {f : Y -> X} (h : Continuou
s f) (hp : forall x, p (f x)) : Continuous fun x => (⟨f x, hp x⟩ : Subtype p)
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `ContinuousEval.continuous_eval`：∀ {F : Type u_1} {X : outParam (Type u_2
)} {Y : outParam (Type u_3)} {inst : FunLike F X Y}   {inst_1 : TopologicalSpace
 F} {inst_2 : Topolo…
· 使用定理 `ContinuousMap.instContinuousEvalOfLocallyCompactPair`：∀ {X : Type u_2} {
Y : Type u_3} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y] [Locally
CompactPair X Y],   ContinuousEval C(X, Y)…
· 使用定理 `instLocallyCompactPairOfLocallyCompactSpace`：∀ {X : Type u_1} {Y : Type 
u_2} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y] [LocallyCompactSp
ace X],   LocallyCompactPair X Y
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `proper_of_compact`：∀ {α : Type u} [inst : PseudoMetricSpace α] [CompactS
pace α], ProperSpace α
· 使用定理 `ConditionallyCompleteLinearOrder.toCompactIccSpace`：∀ (α : Type u_2) [in
st : ConditionallyCompleteLinearOrder α] [inst_1 : TopologicalSpace α] [OrderTop
ology α],   CompactIccSpace α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Continuous.prodMap`：Continuous.prodMap {f : Z -> X} {g : W -> Y} (hf : C
ontinuous f) (hg : Continuous g) : Continuous (Prod.map f g)
· 使用定理 `ContinuousMap.continuous_curry`：continuous_curry [LocallyCompactSpace (X
 × Y)] : Continuous (curry : C(X × Y, Z) -> C(X, C(Y, Z)))
· 使用定理 `ContinuousMap.continuous_precomp`：continuous_precomp (f : C(X, Y)) : Con
tinuous (fun g => g.comp f : C(Y, Z) -> C(X, Z))
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
-/
theorem continuous_toLoop (i : N) : Continuous (@toLoop N X _ x _ i) :=
  Path.continuous_uncurry_iff.1 <|
    Continuous.subtype_mk
      (continuous_eval.comp <|
        Continuous.prodMap
          (ContinuousMap.continuous_curry.comp <|
            (ContinuousMap.continuous_precomp _).comp continuous_subtype_val)
          continuous_id)
      _

/-- Generalized loop from a loop by uncurrying $I → (I^{N\setminus\{j\}} → X)$ into $I^N → X$. -/
@[simps]
/-
**GenLoop.fromLoop** 是 Mathlib 中的一个定义，位于命名空间 `GenLoop`。
形式化陈述：fromLoop (i : N) (p : Ω (Ω^ { j // j != i } X x) const) : Ω^ N X x
参数：i : N；p : Ω (Ω^ { j // j != i } X x) const。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Generalized loop from a loop by uncurrying $I → (I^{N\setminus\{j\}} → X)$ into 
$I^N → X$.
-/
def fromLoop (i : N) (p : Ω (Ω^ { j // j ≠ i } X x) const) : Ω^ N X x :=
  ⟨(ContinuousMap.comp ⟨Subtype.val, by fun_prop⟩ p.toContinuousMap).uncurry.comp
    (Cube.splitAt i),
    by
    rintro y ⟨j, Hj⟩
    simp only [ContinuousMap.comp_apply,
      funSplitAt_apply, ContinuousMap.uncurry_apply, ContinuousMap.coe_mk,
      Function.uncurry_apply_pair]
    obtain rfl | Hne := eq_or_ne j i
    · rcases Hj with Hj | Hj <;> simp only [Hj, p.coe_toContinuousMap, p.source, p.target] <;> rfl
    · exact GenLoop.boundary _ _ ⟨⟨j, Hne⟩, Hj⟩⟩
/-
**GenLoop.continuous_fromLoop** 是 Mathlib 中的一个定理，位于命名空间 `GenLoop`。
形式化陈述：continuous_fromLoop (i : N) : Continuous (@fromLoop N X _ x _ i)
参数：i : N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.subtype_mk`：Continuous.subtype_mk {f : Y -> X} (h : Continuou
s f) (hp : forall x, p (f x)) : Continuous fun x => (⟨f x, hp x⟩ : Subtype p)
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `ContinuousMap.continuous_precomp`：continuous_precomp (f : C(X, Y)) : Con
tinuous (fun g => g.comp f : C(Y, Z) -> C(X, Z))
· 使用定理 `ContinuousMap.continuous_uncurry`：continuous_uncurry [LocallyCompactSpac
e X] [LocallyCompactSpace Y] : Continuous (uncurry : C(X, C(Y, Z)) -> C(X × Y, Z
))
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `proper_of_compact`：∀ {α : Type u} [inst : PseudoMetricSpace α] [CompactS
pace α], ProperSpace α
· 使用定理 `ConditionallyCompleteLinearOrder.toCompactIccSpace`：∀ (α : Type u_2) [in
st : ConditionallyCompleteLinearOrder α] [inst_1 : TopologicalSpace α] [OrderTop
ology α],   CompactIccSpace α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `ContinuousMap.continuous_postcomp`：continuous_postcomp (g : C(Y, Z)) : C
ontinuous (ContinuousMap.comp g : C(X, Y) -> C(X, Z))
· 使用定理 `continuous_induced_dom`：continuous_induced_dom {t : TopologicalSpace β} 
: Continuous[induced f t, t] f
-/
theorem continuous_fromLoop (i : N) : Continuous (@fromLoop N X _ x _ i) :=
  ((ContinuousMap.continuous_precomp _).comp <|
        ContinuousMap.continuous_uncurry.comp <|
          (ContinuousMap.continuous_postcomp _).comp continuous_induced_dom).subtype_mk
    _
/-
**GenLoop.to_from** 是 Mathlib 中的一个定理，位于命名空间 `GenLoop`。
形式化陈述：to_from (i : N) (p : Ω (Ω^ { j // j != i } X x) const) : toLoop i (fromLoo
p i p) = p
参数：i : N；p : Ω (Ω^ { j // j != i } X x) const。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Homeomorph.toContinuousMap_comp_symm`：toContinuousMap_comp_symm : (f : C
(α, β)).comp (f.symm : C(β, α)) = ContinuousMap.id β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `ContinuousMap.mk.congr_simp`：∀ {X : Type u_1} {Y : Type u_2} [inst : Top
ologicalSpace X] [inst_1 : TopologicalSpace Y] (toFun toFun_1 : X → Y)   (e_toFu
n : toFun = toFun…
· 使用定理 `Path.mk.congr_simp`：∀ {X : Type u_1} [inst : TopologicalSpace X] {x y : 
X} (toContinuousMap toContinuousMap_1 : C(↑unitInterval, X))   (e_toContinuousMa
p : toCo…
· 使用定理 `ContinuousMap.comp_id`：comp_id (f : C(α, β)) : f.comp (ContinuousMap.id 
_) = f
· 使用定理 `Path.ext`：∀ {X : Type u_1} [inst : TopologicalSpace X] {x y : X} {γ₁ γ₂ 
: Path x y}, ⇑γ₁ = ⇑γ₂ → γ₁ = γ₂
· 使用定理 `GenLoop.ext`：ext (f g : Ω^ N X x) (H : forall y, f y = g y) : f = g
-/
theorem to_from (i : N) (p : Ω (Ω^ { j // j ≠ i } X x) const) : toLoop i (fromLoop i p) = p := by
  simp_rw [toLoop, fromLoop, ContinuousMap.comp_assoc,
    toContinuousMap_comp_symm, ContinuousMap.comp_id]
  ext; rfl

/-- The `n+1`-dimensional loops are in bijection with the loops in the space of
  `n`-dimensional loops with base point `const`.
  We allow an arbitrary indexing type `N` in place of `Fin n` here. -/
@[simps]
/-
**GenLoop.loopHomeo** 是 Mathlib 中的一个定义，位于命名空间 `GenLoop`。
形式化陈述：loopHomeo (i : N) : Ω^ N X x ≃ₜ Ω (Ω^ { j // j != i } X x) const where toF
un
参数：i : N。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `GenLoop.to_from`：to_from (i : N) (p : Ω (Ω^ { j // j != i } X x) const) 
: toLoop i (fromLoop i p) = p
· 使用定理 `GenLoop.continuous_toLoop`：continuous_toLoop (i : N) : Continuous (@toLo
op N X _ x _ i)
· 使用定理 `GenLoop.continuous_fromLoop`：continuous_fromLoop (i : N) : Continuous (@
fromLoop N X _ x _ i)

--- 原说明 ---
The `n+1`-dimensional loops are in bijection with the loops in the space of
  `n`-dimensional loops with base point `const`.
  We allow an arbitrary indexing type `N` in place of `Fin n` here.
-/
def loopHomeo (i : N) : Ω^ N X x ≃ₜ Ω (Ω^ { j // j ≠ i } X x) const where
  toFun := toLoop i
  invFun := fromLoop i
  left_inv p := by ext; exact congr_arg p (by dsimp; exact Equiv.apply_symm_apply _ _)
  right_inv := to_from i
  continuous_toFun := continuous_toLoop i
  continuous_invFun := continuous_fromLoop i
/-
**GenLoop.toLoop_apply** 是 Mathlib 中的一个定理，位于命名空间 `GenLoop`。
形式化陈述：toLoop_apply (i : N) {p : Ω^ N X x} {t} {tn} : toLoop i p t tn = p (Cube.i
nsertAt i ⟨t, tn⟩)
参数：i : N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toLoop_apply (i : N) {p : Ω^ N X x} {t} {tn} :
    toLoop i p t tn = p (Cube.insertAt i ⟨t, tn⟩) :=
  rfl
/-
**GenLoop.fromLoop_apply** 是 Mathlib 中的一个定理，位于命名空间 `GenLoop`。
形式化陈述：fromLoop_apply (i : N) {p : Ω (Ω^ { j // j != i } X x) const} {t : I^N} : 
fromLoop i p t = p (t i) (Cube.splitAt i t).snd
参数：i : N；Ω^ { j // j != i } X x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fromLoop_apply (i : N) {p : Ω (Ω^ { j // j ≠ i } X x) const} {t : I^N} :
    fromLoop i p t = p (t i) (Cube.splitAt i t).snd :=
  rfl

/-- Composition with `Cube.insertAt` as a continuous map. -/
/-
**GenLoop.cCompInsert** 是 Mathlib 中的一个缩写定义，位于命名空间 `GenLoop`。
形式化陈述：cCompInsert (i : N) : C(C(I^N, X), C(I × I^{ j // j != i }, X))
参数：i : N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition with `Cube.insertAt` as a continuous map.
-/
abbrev cCompInsert (i : N) : C(C(I^N, X), C(I × I^{ j // j ≠ i }, X)) :=
  ⟨fun f ↦ f.comp (Cube.insertAt i),
    (toContinuousMap <| Cube.insertAt i).continuous_precomp⟩

/-- A homotopy between `n+1`-dimensional loops `p` and `q` constant on the boundary
  seen as a homotopy between two paths in the space of `n`-dimensional paths. -/
/-
**GenLoop.homotopyTo** 是 Mathlib 中的一个定义，位于命名空间 `GenLoop`。
形式化陈述：homotopyTo (i : N) {p q : Ω^ N X x} (H : p.1.HomotopyRel q.1 (Cube.boundar
y N)) : C(I × I, C(I^{ j // j != i }, X))
参数：i : N；H : p.1.HomotopyRel q.1 (Cube.boundary N)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A homotopy between `n+1`-dimensional loops `p` and `q` constant on the boundary
  seen as a homotopy between two paths in the space of `n`-dimensional paths.
-/
def homotopyTo (i : N) {p q : Ω^ N X x} (H : p.1.HomotopyRel q.1 (Cube.boundary N)) :
    C(I × I, C(I^{ j // j ≠ i }, X)) :=
  ((⟨_, ContinuousMap.continuous_curry⟩ : C(_, _)).comp <|
      (cCompInsert i).comp H.toContinuousMap.curry).uncurry

-- `@[simps]` generates this lemma but it's named `homotopyTo_apply_apply` instead
/-
**GenLoop.homotopyTo_apply** 是 Mathlib 中的一个定理，位于命名空间 `GenLoop`。
形式化陈述：homotopyTo_apply (i : N) {p q : Ω^ N X x} (H : p.1.HomotopyRel q.1 <| Cube
.boundary N) (t : I × I) (tₙ : I^{ j // j != i }) : homotopyTo i H t tₙ = H (t.f
st, Cube.insertAt i (t.snd, tₙ))
参数：i : N；H : p.1.HomotopyRel q.1 <| Cube.boundary N；t : I × I；tₙ : I^{ j // j !=
 i }。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem homotopyTo_apply (i : N) {p q : Ω^ N X x} (H : p.1.HomotopyRel q.1 <| Cube.boundary N)
    (t : I × I) (tₙ : I^{ j // j ≠ i }) :
    homotopyTo i H t tₙ = H (t.fst, Cube.insertAt i (t.snd, tₙ)) :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**GenLoop.homotopicTo** 是 Mathlib 中的一个定理，位于命名空间 `GenLoop`。
形式化陈述：homotopicTo (i : N) {p q : Ω^ N X x} : Homotopic p q -> (toLoop i p).Homot
opic (toLoop i q)
参数：i : N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nonempty.map`：Nonempty.map {α β} (f : α -> β) : Nonempty α -> Nonempty β
 | ⟨h⟩ => ⟨f h⟩  protected theorem Nonempty.map2 {α β γ : Sort*} (f : α -> β -> 
γ)…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `GenLoop.homotopyTo_apply`：homotopyTo_apply (i : N) {p q : Ω^ N X x} (H :
 p.1.HomotopyRel q.1 <| Cube.boundary N) (t : I × I) (tₙ : I^{ j // j != i }) : 
homotopyTo i H…
· 使用定理 `ContinuousMap.HomotopyRel.eq_fst`：eq_fst (F : HomotopyRel f₀ f₁ S) (t : 
I) {x : X} (hx : x in S) : F (t, x) = f₀ x
· 使用定理 `Cube.insertAt_boundary`：insertAt_boundary (i : N) {t₀ : I} {t} (H : (t₀ 
= 0 ∨ t₀ = 1) ∨ t in boundary { j // j != i }) : insertAt i ⟨t₀, t⟩ in boundary 
N
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Continuous.subtype_mk`：Continuous.subtype_mk {f : Y -> X} (h : Continuou
s f) (hp : forall x, p (f x)) : Continuous fun x => (⟨f x, hp x⟩ : Subtype p)
· 使用定理 `ContinuousMapClass.map_continuous`：∀ {F : Type u_1} {X : outParam (Type 
u_2)} {Y : outParam (Type u_3)} {inst : TopologicalSpace X}   {inst_1 : Topologi
calSpace Y} {inst_2 : F…
· 使用定理 `GenLoop.ext`：ext (f g : Ω^ N X x) (H : forall y, f y = g y) : f = g
· 使用定理 `GenLoop.toLoop_apply`：toLoop_apply (i : N) {p : Ω^ N X x} {t} {tn} : toL
oop i p t tn = p (Cube.insertAt i ⟨t, tn⟩)
· 使用定理 `ContinuousMap.HomotopyWith.apply_zero`：apply_zero (F : HomotopyWith f₀ f
₁ P) (x : X) : F (0, x) = f₀ x
· 使用定理 `ContinuousMap.HomotopyWith.apply_one`：apply_one (F : HomotopyWith f₀ f₁ 
P) (x : X) : F (1, x) = f₁ x
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `ContinuousMap.continuous_toFun`：∀ {X : Type u_1} {Y : Type u_2} [inst : 
TopologicalSpace X] [inst_1 : TopologicalSpace Y] (self : C(X, Y)),   Continuous
 self.toFun
· 使用定理 `Eq.mpr_not`：∀ {p q : Prop}, p = q → ¬q → ¬p
· 使用定理 `Homeomorph.funSplitAt_symm_apply`：∀ (Y : Type u_2) [inst : TopologicalSp
ace Y] {ι : Type u_7} [inst_1 : DecidableEq ι] (i : ι)   (f : (fun a => Y) i × (
(j : { j // j ≠ i }) →…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
-/
theorem homotopicTo (i : N) {p q : Ω^ N X x} :
    Homotopic p q → (toLoop i p).Homotopic (toLoop i q) := by
  refine Nonempty.map fun H ↦ ⟨⟨⟨fun t ↦ ⟨homotopyTo i H t, ?_⟩, ?_⟩, ?_, ?_⟩, ?_⟩
  · rintro y ⟨i, iH⟩
    rw [homotopyTo_apply, H.eq_fst, p.2]
    all_goals apply Cube.insertAt_boundary; right; exact ⟨i, iH⟩
  · fun_prop
  iterate 2
    intro
    ext
    dsimp
    rw [homotopyTo_apply, toLoop_apply]
    swap
  · apply H.apply_zero
  · apply H.apply_one
  intro t y yH
  ext
  dsimp
  rw [homotopyTo_apply]
  apply H.eq_fst; use i
  rw [funSplitAt_symm_apply, dif_pos rfl]; exact yH

/-- The converse to `GenLoop.homotopyTo`: a homotopy between two loops in the space of
  `n`-dimensional loops can be seen as a homotopy between two `n+1`-dimensional paths. -/
/-
**GenLoop.homotopyFrom** 是 Mathlib 中的一个定义，位于命名空间 `GenLoop`。
形式化陈述：{N : Type u_1} →   {X : Type u_2} →     [inst : TopologicalSpace X] →     
  {x : X} →         [inst_1 : DecidableEq N] →           (i : N) →             {
p q : ↑(GenLoop N X x)} →               Path.Homotopy (GenLoop.toLoop i p) (GenL
oop.toLoop i q) → C(↑unitInterval × (N → ↑unitInterval), X)
参数：i : N；GenLoop N X x；GenLoop.toLoop i p；GenLoop.toLoop i q；↑unitInterval × (N 
→ ↑unitInterval), X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The converse to `GenLoop.homotopyTo`: a homotopy between two loops in the space 
of
  `n`-dimensional loops can be seen as a homotopy between two `n+1`-dimensional 
paths.
-/
@[simps!] def homotopyFrom (i : N) {p q : Ω^ N X x} (H : (toLoop i p).Homotopy (toLoop i q)) :
    C(I × I^N, X) :=
  (ContinuousMap.comp ⟨_, ContinuousMap.continuous_uncurry⟩
          (ContinuousMap.comp ⟨Subtype.val, by fun_prop⟩ H.toContinuousMap).curry).uncurry.comp <|
    (ContinuousMap.id I).prodMap (Cube.splitAt i)
/-
**GenLoop.homotopicFrom** 是 Mathlib 中的一个定理，位于命名空间 `GenLoop`。
形式化陈述：homotopicFrom (i : N) {p q : Ω^ N X x} : (toLoop i p).Homotopic (toLoop i 
q) -> Homotopic p q
参数：i : N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nonempty.map`：Nonempty.map {α β} (f : α -> β) : Nonempty α -> Nonempty β
 | ⟨h⟩ => ⟨f h⟩  protected theorem Nonempty.map2 {α β γ : Sort*} (f : α -> β -> 
γ)…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `GenLoop.homotopyFrom_apply`：∀ {N : Type u_1} {X : Type u_2} [inst : Topo
logicalSpace X] {x : X} [inst_1 : DecidableEq N] (i : N)   {p q : ↑(GenLoop N X 
x)} (H : Path.Ho…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Homeomorph.funSplitAt_apply`：∀ (Y : Type u_2) [inst : TopologicalSpace Y
] {ι : Type u_7} [inst_1 : DecidableEq ι] (i : ι)   (f : (j : ι) → (fun a => Y) 
j), (Homeomorph.f…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ContinuousMap.HomotopyWith.apply_zero`：apply_zero (F : HomotopyWith f₀ f
₁ P) (x : X) : F (0, x) = f₀ x
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Equiv.left_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Function
.LeftInverse self.invFun self.toFun
· 使用定理 `ContinuousMap.HomotopyWith.apply_one`：apply_one (F : HomotopyWith f₀ f₁ 
P) (x : X) : F (1, x) = f₁ x
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `ContinuousMap.continuous_toFun`：∀ {X : Type u_1} {Y : Type u_2} [inst : 
TopologicalSpace X] [inst_1 : TopologicalSpace Y] (self : C(X, Y)),   Continuous
 self.toFun
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `ContinuousMap.HomotopyRel.eq_fst`：eq_fst (F : HomotopyRel f₀ f₁ S) (t : 
I) {x : X} (hx : x in S) : F (t, x) = f₀ x
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `GenLoop.boundary`：boundary (f : Ω^ N X x) : forall y in Cube.boundary N,
 f y = x
-/
theorem homotopicFrom (i : N) {p q : Ω^ N X x} :
    (toLoop i p).Homotopic (toLoop i q) → Homotopic p q := by
  refine Nonempty.map fun H ↦ ⟨⟨homotopyFrom i H, ?_, ?_⟩, ?_⟩
  pick_goal 3
  · rintro t y ⟨j, jH⟩
    erw [homotopyFrom_apply]
    obtain rfl | h := eq_or_ne j i
    · simp only [Prod.map_apply, id_eq, funSplitAt_apply, Function.uncurry_apply_pair]
      rw [H.eq_fst]
      exacts [congr_arg p ((Cube.splitAt j).left_inv _), jH]
    · rw [p.2 _ ⟨j, jH⟩]; apply boundary; exact ⟨⟨j, h⟩, jH⟩
  all_goals
    intro
    apply (homotopyFrom_apply _ _ _).trans
    simp only [Prod.map_apply, id_eq, funSplitAt_apply,
      Function.uncurry_apply_pair, ContinuousMap.HomotopyWith.apply_zero,
      ContinuousMap.HomotopyWith.apply_one, ne_eq, Path.coe_toContinuousMap]
    first
    | apply congr_arg p
    | apply congr_arg q
    apply (Cube.splitAt i).left_inv

set_option backward.defeqAttrib.useBackward true in
/-- Concatenation of two `GenLoop`s along the `i`th coordinate. -/
/-
**GenLoop.transAt** 是 Mathlib 中的一个定义，位于命名空间 `GenLoop`。
形式化陈述：transAt (i : N) (f g : Ω^ N X x) : Ω^ N X x
参数：i : N；f g : Ω^ N X x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Concatenation of two `GenLoop`s along the `i`th coordinate.
-/
def transAt (i : N) (f g : Ω^ N X x) : Ω^ N X x :=
  copy (fromLoop i <| (toLoop i f).trans <| toLoop i g)
    (fun t ↦ if (t i : ℝ) ≤ 1 / 2
      then f (Function.update t i <| Set.projIcc 0 1 zero_le_one (2 * t i))
      else g (Function.update t i <| Set.projIcc 0 1 zero_le_one (2 * t i - 1)))
    (by
      ext1; symm
      dsimp only [Path.trans, fromLoop, Path.coe_mk_mk, Function.comp_apply, mk_apply,
        ContinuousMap.comp_apply, ContinuousMap.coe_coe, funSplitAt_apply,
        ContinuousMap.uncurry_apply, ContinuousMap.coe_mk, Function.uncurry_apply_pair]
      split_ifs
      · change f _ = _; congr 1
      · change g _ = _; congr 1)

/-- Reversal of a `GenLoop` along the `i`th coordinate. -/
/-
**GenLoop.symmAt** 是 Mathlib 中的一个定义，位于命名空间 `GenLoop`。
形式化陈述：symmAt (i : N) (f : Ω^ N X x) : Ω^ N X x
参数：i : N；f : Ω^ N X x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reversal of a `GenLoop` along the `i`th coordinate.
-/
def symmAt (i : N) (f : Ω^ N X x) : Ω^ N X x :=
  (copy (fromLoop i (toLoop i f).symm) fun t ↦ f fun j ↦ if j = i then σ (t i) else t j) <| by
    ext1; change _ = f _; congr; ext1; simp
/-
**GenLoop.transAt_distrib** 是 Mathlib 中的一个定理，位于命名空间 `GenLoop`。
形式化陈述：transAt_distrib {i j : N} (h : i != j) (a b c d : Ω^ N X x) : transAt i (t
ransAt j a b) (transAt j c d) = transAt j (transAt i a c) (transAt i b d)
参数：h : i != j；a b c d : Ω^ N X x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GenLoop.ext`：ext (f g : Ω^ N X x) (H : forall y, f y = g y) : f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Function.update_apply`：update_apply {β : Sort*} (f : α -> β) (a' : α) (b
 : β) (a : α) : update f a' b a = if a = a' then b else f a
· 使用定理 `Set.projIcc.congr_simp`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α
) (h : a ≤ b) (x x_1 : α),   x = x_1 → Set.projIcc a b h x = Set.projIcc a b h x
_1
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `dite.congr_simp`：∀ {α : Sort u} (c : Prop) {h : Decidable c} [h_1 : Deci
dable c] (t t_1 : c → α),   t = t_1 → ∀ (e e_1 : ¬c → α), e = e_1 → dite c t e =
 dite…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_rec_constant`：∀ {α : Sort u_1} {a a' : α} {β : Sort u_2} (y : β) (h :
 a = a'), h ▸ y = y
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `ite_ite_comm`：ite_ite_comm (h : P -> ¬Q) : (if P then a else if Q then b
 else c) = if Q then b else if P then a else c
-/
theorem transAt_distrib {i j : N} (h : i ≠ j) (a b c d : Ω^ N X x) :
    transAt i (transAt j a b) (transAt j c d) = transAt j (transAt i a c) (transAt i b d) := by
  ext; simp_rw [transAt, coe_copy, Function.update_apply, if_neg h, if_neg h.symm]
  split_ifs <;>
    · congr 1; ext1; simp only [Function.update, eq_rec_constant, dite_eq_ite]
      apply ite_ite_comm; rintro rfl; exact h.symm
/-
**GenLoop.fromLoop_trans_toLoop** 是 Mathlib 中的一个定理，位于命名空间 `GenLoop`。
形式化陈述：fromLoop_trans_toLoop {i : N} {p q : Ω^ N X x} : fromLoop i ((toLoop i p).
trans <| toLoop i q) = transAt i p q
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `GenLoop.copy_eq`：copy_eq (f : Ω^ N X x) {g : (I^N) -> X} (h : g = f) : c
opy f g h = f
-/
theorem fromLoop_trans_toLoop {i : N} {p q : Ω^ N X x} :
    fromLoop i ((toLoop i p).trans <| toLoop i q) = transAt i p q :=
  (copy_eq _ _).symm
/-
**GenLoop.fromLoop_symm_toLoop** 是 Mathlib 中的一个定理，位于命名空间 `GenLoop`。
形式化陈述：fromLoop_symm_toLoop {i : N} {p : Ω^ N X x} : fromLoop i (toLoop i p).symm
 = symmAt i p
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `GenLoop.copy_eq`：copy_eq (f : Ω^ N X x) {g : (I^N) -> X} (h : g = f) : c
opy f g h = f
-/
theorem fromLoop_symm_toLoop {i : N} {p : Ω^ N X x} : fromLoop i (toLoop i p).symm = symmAt i p :=
  (copy_eq _ _).symm

end LoopHomeo

end GenLoop

/-- The `n`th homotopy group at `x` defined as the quotient of `Ω^n x` by the
  `GenLoop.Homotopic` relation. -/
/-
**HomotopyGroup** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：HomotopyGroup (N X : Type*) [TopologicalSpace X] (x : X) : Type _
参数：N X : Type*；x : X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `n`th homotopy group at `x` defined as the quotient of `Ω^n x` by the
  `GenLoop.Homotopic` relation.
-/
def HomotopyGroup (N X : Type*) [TopologicalSpace X] (x : X) : Type _ :=
  Quotient (GenLoop.Homotopic.setoid N x)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (HomotopyGroup N X x) :=
  inferInstanceAs <| Inhabited <| Quotient (GenLoop.Homotopic.setoid N x)

variable [DecidableEq N]

open GenLoop

/-- Equivalence between the homotopy group of X and the fundamental group of
  `Ω^{j // j ≠ i} x`. -/
/-
**homotopyGroupEquivFundamentalGroup** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：homotopyGroupEquivFundamentalGroup (i : N) : HomotopyGroup N X x ≃ Fundame
ntalGroup (Ω^ { j // j != i } X x) const
参数：i : N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Equivalence between the homotopy group of X and the fundamental group of
  `Ω^{j // j ≠ i} x`.
-/
def homotopyGroupEquivFundamentalGroup (i : N) :
    HomotopyGroup N X x ≃ FundamentalGroup (Ω^ { j // j ≠ i } X x) const :=
  Quotient.congr (loopHomeo i).toEquiv fun _ _ ↦ ⟨homotopicTo i, homotopicFrom i⟩

/-- Homotopy group of finite index, denoted as `π_n` within the Topology namespace. -/
/-
**HomotopyGroup.Pi** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：HomotopyGroup.Pi (n) (X : Type*) [TopologicalSpace X] (x : X)
参数：n；X : Type*；x : X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Homotopy group of finite index, denoted as `π_n` within the Topology namespace.
-/
abbrev HomotopyGroup.Pi (n) (X : Type*) [TopologicalSpace X] (x : X) :=
  HomotopyGroup (Fin n) _ x

@[inherit_doc] scoped[Topology] notation "π_" => HomotopyGroup.Pi

/-- The 0-dimensional generalized loops based at `x` are in bijection with `X`. -/
/-
**genLoopHomeoOfIsEmpty** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：genLoopHomeoOfIsEmpty (N x) [IsEmpty N] : Ω^ N X x ≃ₜ X where toFun f
参数：N x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The 0-dimensional generalized loops based at `x` are in bijection with `X`.
-/
def genLoopHomeoOfIsEmpty (N x) [IsEmpty N] : Ω^ N X x ≃ₜ X where
  toFun f := f 0
  invFun y := ⟨ContinuousMap.const _ y, fun _ ⟨i, _⟩ ↦ isEmptyElim i⟩
  left_inv f := by ext; exact congr_arg f (Subsingleton.elim _ _)
  continuous_invFun := ContinuousMap.const'.2.subtype_mk _

/-- The homotopy "group" indexed by an empty type is in bijection with
  the path components of `X`, aka the `ZerothHomotopy`. -/
/-
**homotopyGroupEquivZerothHomotopyOfIsEmpty** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：homotopyGroupEquivZerothHomotopyOfIsEmpty (N x) [IsEmpty N] : HomotopyGrou
p N X x ≃ ZerothHomotopy X
参数：N x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The homotopy "group" indexed by an empty type is in bijection with
  the path components of `X`, aka the `ZerothHomotopy`.
-/
def homotopyGroupEquivZerothHomotopyOfIsEmpty (N x) [IsEmpty N] :
    HomotopyGroup N X x ≃ ZerothHomotopy X :=
  Quotient.congr (genLoopHomeoOfIsEmpty N x).toEquiv
    (by
      -- joined iff homotopic
      intro a₁ a₂
      constructor <;> rintro ⟨H⟩
      exacts
        [⟨{ toFun := fun t ↦ H ⟨t, isEmptyElim⟩
            source' := (H.apply_zero _).trans (congr_arg a₁ <| Subsingleton.elim _ _)
            target' := (H.apply_one _).trans (congr_arg a₂ <| Subsingleton.elim _ _) }⟩,
        ⟨{  toFun := fun t0 ↦ H t0.fst
            map_zero_left := fun _ ↦ H.source.trans (congr_arg a₁ <| Subsingleton.elim _ _)
            map_one_left := fun _ ↦ H.target.trans (congr_arg a₂ <| Subsingleton.elim _ _)
            prop' := fun _ _ ⟨i, _⟩ ↦ isEmptyElim i }⟩])

/-- The 0th homotopy "group" is in bijection with `ZerothHomotopy`. -/
/-
**HomotopyGroup.pi0EquivZerothHomotopy** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：HomotopyGroup.pi0EquivZerothHomotopy : π_ 0 X x ≃ ZerothHomotopy X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The 0th homotopy "group" is in bijection with `ZerothHomotopy`.
-/
def HomotopyGroup.pi0EquivZerothHomotopy : π_ 0 X x ≃ ZerothHomotopy X :=
  homotopyGroupEquivZerothHomotopyOfIsEmpty (Fin 0) x

/-- The 1-dimensional generalized loops based at `x` are in bijection with loops at `x`. -/
/-
**genLoopEquivOfUnique** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：genLoopEquivOfUnique (N) [Unique N] : Ω^ N X x ≃ Ω X x where toFun p
参数：N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The 1-dimensional generalized loops based at `x` are in bijection with loops at 
`x`.
-/
def genLoopEquivOfUnique (N) [Unique N] : Ω^ N X x ≃ Ω X x where
  toFun p :=
    Path.mk ⟨fun t ↦ p fun _ ↦ t, by fun_prop⟩
      (GenLoop.boundary _ (fun _ ↦ 0) ⟨default, Or.inl rfl⟩)
      (GenLoop.boundary _ (fun _ ↦ 1) ⟨default, Or.inr rfl⟩)
  invFun p :=
    ⟨⟨fun c ↦ p (c default), by fun_prop⟩,
      by
      rintro y ⟨i, iH | iH⟩ <;> cases Unique.eq_default i <;> apply (congr_arg p iH).trans
      exacts [p.source, p.target]⟩
  left_inv p := by ext y; exact congr_arg p (eq_const_of_unique y).symm

/- TODO (?): deducing this from `homotopyGroupEquivFundamentalGroup` would require
  combination of `CategoryTheory.Functor.mapAut` and
  `FundamentalGroupoid.fundamentalGroupoidFunctor` applied to `genLoopHomeoOfIsEmpty`,
  with possibly worse defeq. -/
/-- The homotopy group at `x` indexed by a singleton is in bijection with the fundamental group,
  i.e. the loops based at `x` up to homotopy. -/
/-
**homotopyGroupEquivFundamentalGroupOfUnique** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：homotopyGroupEquivFundamentalGroupOfUnique (N) [Unique N] : HomotopyGroup 
N X x ≃ FundamentalGroup X x
参数：N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The homotopy group at `x` indexed by a singleton is in bijection with the fundam
ental group,
  i.e. the loops based at `x` up to homotopy.
-/
def homotopyGroupEquivFundamentalGroupOfUnique (N) [Unique N] :
    HomotopyGroup N X x ≃ FundamentalGroup X x :=
  Quotient.congr (genLoopEquivOfUnique N) fun a₁ a₂ ↦ by
    constructor <;> rintro ⟨H⟩
    · exact
        ⟨{  toFun := fun tx ↦ H (tx.fst, fun _ ↦ tx.snd)
            map_zero_left := fun _ ↦ H.apply_zero _
            map_one_left := fun _ ↦ H.apply_one _
            prop' := fun t y iH ↦ H.prop' _ _ ⟨default, iH⟩ }⟩
    refine
      ⟨⟨⟨⟨fun tx ↦ H (tx.fst, tx.snd default), H.continuous.comp ?_⟩, fun y ↦ ?_, fun y ↦ ?_⟩, ?_⟩⟩
    · fun_prop
    · exact (H.apply_zero _).trans (congr_arg a₁ (eq_const_of_unique y).symm)
    · exact (H.apply_one _).trans (congr_arg a₂ (eq_const_of_unique y).symm)
    · rintro t y ⟨i, iH⟩
      cases Unique.eq_default i
      exact (H.eq_fst _ iH).trans (congr_arg a₁ (eq_const_of_unique y).symm)

/-- The first homotopy group at `x` is in bijection with the fundamental group. -/
/-
**HomotopyGroup.pi1EquivFundamentalGroup** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：HomotopyGroup.pi1EquivFundamentalGroup : π_ 1 X x ≃ FundamentalGroup X x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The first homotopy group at `x` is in bijection with the fundamental group.
-/
def HomotopyGroup.pi1EquivFundamentalGroup : π_ 1 X x ≃ FundamentalGroup X x :=
  homotopyGroupEquivFundamentalGroupOfUnique (Fin 1)
/-
**HomotopyGroup.genLoopEquivOfUnique_transAt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：HomotopyGroup.genLoopEquivOfUnique_transAt (N) [DecidableEq N] [Unique N] 
(p q : Ω^ N X x) : genLoopEquivOfUnique _ (transAt default q p) = (genLoopEquivO
fUnique _ q).trans (genLoopEquivOfUnique _ p)
参数：N；p q : Ω^ N X x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Path.ext`：∀ {X : Type u_1} [inst : TopologicalSpace X] {x y : X} {γ₁ γ₂ 
: Path x y}, ⇑γ₁ = ⇑γ₂ → γ₁ = γ₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `ContinuousMap.mk.congr_simp`：∀ {X : Type u_1} {Y : Type u_2} [inst : Top
ologicalSpace X] [inst_1 : TopologicalSpace Y] (toFun toFun_1 : X → Y)   (e_toFu
n : toFun = toFun…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `ite.congr_simp`：∀ {α : Sort u} (c c_1 : Prop),   c = c_1 →     ∀ {h : De
cidable c} [h_1 : Decidable c_1] (t t_1 : α),       t = t_1 → ∀ (e e_1 : α), e =
 e_1…
· 使用定理 `Path.mk.congr_simp`：∀ {X : Type u_1} [inst : TopologicalSpace X] {x y : 
X} (toContinuousMap toContinuousMap_1 : C(↑unitInterval, X))   (e_toContinuousMa
p : toCo…
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Unique.eq_default`：eq_default (a : α) : a = default
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma HomotopyGroup.genLoopEquivOfUnique_transAt (N) [DecidableEq N] [Unique N] (p q : Ω^ N X x) :
    genLoopEquivOfUnique _ (transAt default q p) =
      (genLoopEquivOfUnique _ q).trans (genLoopEquivOfUnique _ p) := by
  ext t
  simp only [genLoopEquivOfUnique, GenLoop.transAt, GenLoop.copy,
    one_div, ContinuousMap.coe_mk, Path.coe_mk', Path.trans,
    Function.comp_apply]
  refine ite_congr rfl (fun _ ↦ congrArg q ?_)
    fun _ ↦ congrArg p ?_
  <;> (ext i; rw [Unique.eq_default i]; simp)

namespace HomotopyGroup

/-- Group structure on `HomotopyGroup N X x` for nonempty `N` (in particular `π_(n+1) X x`). -/
/-
**HomotopyGroup.group** 是 Mathlib 中的一个实例，位于命名空间 `HomotopyGroup`。
形式化陈述：group (N) [DecidableEq N] [Nonempty N] : Group (HomotopyGroup N X x)
参数：N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Group structure on `HomotopyGroup N X x` for nonempty `N` (in particular `π_(n+1
) X x`).
-/
instance group (N) [DecidableEq N] [Nonempty N] : Group (HomotopyGroup N X x) :=
  (homotopyGroupEquivFundamentalGroup <| Classical.arbitrary N).group

/-- Group structure on `HomotopyGroup` obtained by pulling back path composition along the
  `i`th direction. The group structures for two different `i j : N` distribute over each
  other, and therefore are equal by the Eckmann-Hilton argument. -/
/-
**HomotopyGroup.auxGroup** 是 Mathlib 中的一个缩写定义，位于命名空间 `HomotopyGroup`。
形式化陈述：auxGroup (i : N) : Group (HomotopyGroup N X x)
参数：i : N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Group structure on `HomotopyGroup` obtained by pulling back path composition alo
ng the
  `i`th direction. The group structures for two different `i j : N` distribute o
ver each
  other, and therefore are equal by the Eckmann-Hilton argument.
-/
abbrev auxGroup (i : N) : Group (HomotopyGroup N X x) :=
  (homotopyGroupEquivFundamentalGroup i).group
/-
**HomotopyGroup.isUnital_auxGroup** 是 Mathlib 中的一个定理，位于命名空间 `HomotopyGroup`。
形式化陈述：isUnital_auxGroup (i : N) : EckmannHilton.IsUnital (auxGroup i).mul (⟦cons
t⟧ : HomotopyGroup N X x) where left_id
参数：i : N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monoid.one_mul`：∀ {M : Type u} [self : Monoid M] (a : M), 1 * a = a
· 使用定理 `Monoid.mul_one`：∀ {M : Type u} [self : Monoid M] (a : M), a * 1 = a
-/
theorem isUnital_auxGroup (i : N) :
    EckmannHilton.IsUnital (auxGroup i).mul (⟦const⟧ : HomotopyGroup N X x) where
  left_id := (auxGroup i).one_mul
  right_id := (auxGroup i).mul_one
/-
**HomotopyGroup.auxGroup_indep** 是 Mathlib 中的一个定理，位于命名空间 `HomotopyGroup`。
形式化陈述：auxGroup_indep (i j : N) : (auxGroup i : Group (HomotopyGroup N X x)) = au
xGroup j
参数：i j : N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Group.ext`：Group.ext {G : Type*} ⦃g₁ g₂ : Group G⦄ (h_mul : (letI
· 使用定理 `EckmannHilton.mul`：mul : m₁ = m₂
· 使用定理 `HomotopyGroup.isUnital_auxGroup`：isUnital_auxGroup (i : N) : EckmannHilt
on.IsUnital (auxGroup i).mul (⟦const⟧ : HomotopyGroup N X x) where left_id
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Quotient.mk'`：Quotient.mk'_surjective [s : Setoid α] : Function.Surjecti
ve (Quotient.mk' : α -> Quotient s)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `GenLoop.loopHomeo_apply`：∀ {N : Type u_1} {X : Type u_2} [inst : Topolog
icalSpace X] {x : X} [inst_1 : DecidableEq N] (i : N)   (p : ↑(GenLoop N X x)), 
(GenLoop.loop…
· 使用定理 `GenLoop.loopHomeo_symm_apply`：∀ {N : Type u_1} {X : Type u_2} [inst : To
pologicalSpace X] {x : X} [inst_1 : DecidableEq N] (i : N)   (p : LoopSpace (↑(G
enLoop { j // j ≠ …
· 使用定理 `GenLoop.fromLoop_trans_toLoop`：fromLoop_trans_toLoop {i : N} {p q : Ω^ N
 X x} : fromLoop i ((toLoop i p).trans <| toLoop i q) = transAt i p q
· 使用定理 `GenLoop.transAt_distrib`：transAt_distrib {i j : N} (h : i != j) (a b c d
 : Ω^ N X x) : transAt i (transAt j a b) (transAt j c d) = transAt j (transAt i 
a c) (transAt…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem auxGroup_indep (i j : N) : (auxGroup i : Group (HomotopyGroup N X x)) = auxGroup j := by
  by_cases h : i = j; · rw [h]
  refine Group.ext (EckmannHilton.mul (isUnital_auxGroup i) (isUnital_auxGroup j) ?_)
  rintro ⟨a⟩ ⟨b⟩ ⟨c⟩ ⟨d⟩
  change Quotient.mk' _ = _
  apply congr_arg Quotient.mk'
  simp only [fromLoop_trans_toLoop, transAt_distrib h, coe_toEquiv, loopHomeo_apply,
    coe_symm_toEquiv, loopHomeo_symm_apply]
/-
**HomotopyGroup.transAt_indep** 是 Mathlib 中的一个定理，位于命名空间 `HomotopyGroup`。
形式化陈述：transAt_indep {i} (j) (f g : Ω^ N X x) : (⟦transAt i f g⟧ : HomotopyGroup 
N X x) = ⟦transAt j f g⟧
参数：j；f g : Ω^ N X x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr_fun₂`：∀ {α : Sort u_1} {β : α → Sort u_2} {γ : (a : α) → β a → Sor
t u_3} {f g : (a : α) → (b : β a) → γ a b},   f = g → ∀ (a : α) (b : β a), f a b
…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `HomotopyGroup.auxGroup_indep`：auxGroup_indep (i j : N) : (auxGroup i : G
roup (HomotopyGroup N X x)) = auxGroup j
-/
theorem transAt_indep {i} (j) (f g : Ω^ N X x) :
    (⟦transAt i f g⟧ : HomotopyGroup N X x) = ⟦transAt j f g⟧ := by
  simp_rw [← fromLoop_trans_toLoop]
  let m := fun (G) (_ : Group G) ↦ ((· * ·) : G → G → G)
  exact congr_fun₂ (congr_arg (m <| HomotopyGroup N X x) <| auxGroup_indep i j) ⟦g⟧ ⟦f⟧
/-
**HomotopyGroup.symmAt_indep** 是 Mathlib 中的一个定理，位于命名空间 `HomotopyGroup`。
形式化陈述：symmAt_indep {i} (j) (f : Ω^ N X x) : (⟦symmAt i f⟧ : HomotopyGroup N X x)
 = ⟦symmAt j f⟧
参数：j；f : Ω^ N X x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `HomotopyGroup.auxGroup_indep`：auxGroup_indep (i j : N) : (auxGroup i : G
roup (HomotopyGroup N X x)) = auxGroup j
-/
theorem symmAt_indep {i} (j) (f : Ω^ N X x) :
    (⟦symmAt i f⟧ : HomotopyGroup N X x) = ⟦symmAt j f⟧ := by
  simp_rw [← fromLoop_symm_toLoop]
  let inv := fun (G) (_ : Group G) ↦ ((·⁻¹) : G → G)
  exact congr_fun (congr_arg (inv <| HomotopyGroup N X x) <| auxGroup_indep i j) ⟦f⟧

/-- Characterization of multiplicative identity -/
/-
**HomotopyGroup.one_def** 是 Mathlib 中的一个定理，位于命名空间 `HomotopyGroup`。
形式化陈述：one_def [Nonempty N] : (1 : HomotopyGroup N X x) = ⟦const⟧
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Characterization of multiplicative identity
-/
theorem one_def [Nonempty N] : (1 : HomotopyGroup N X x) = ⟦const⟧ :=
  rfl

/-- Characterization of multiplication -/
/-
**HomotopyGroup.mul_spec** 是 Mathlib 中的一个定理，位于命名空间 `HomotopyGroup`。
形式化陈述：mul_spec [Nonempty N] {i} {p q : Ω^ N X x} : -- TODO: introduce `HomotopyG
roup.mk` and remove defeq abuse. ((· * ·) : _ -> _ -> HomotopyGroup N X x) ⟦p⟧ ⟦
q⟧ = ⟦transAt i q p⟧
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HomotopyGroup.transAt_indep`：transAt_indep {i} (j) (f g : Ω^ N X x) : (⟦
transAt i f g⟧ : HomotopyGroup N X x) = ⟦transAt j f g⟧
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `GenLoop.fromLoop_trans_toLoop`：fromLoop_trans_toLoop {i : N} {p q : Ω^ N
 X x} : fromLoop i ((toLoop i p).trans <| toLoop i q) = transAt i p q
· 使用定理 `Quotient.sound`：∀ {α : Sort u} {s : Setoid α} {a b : α}, a ≈ b → ⟦a⟧ = ⟦
b⟧
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Setoid.refl`：∀ {α : Sort u} [inst : Setoid α] (a : α), a ≈ a

--- 原说明 ---
Characterization of multiplication
-/
theorem mul_spec [Nonempty N] {i} {p q : Ω^ N X x} :
    -- TODO: introduce `HomotopyGroup.mk` and remove defeq abuse.
    ((· * ·) : _ → _ → HomotopyGroup N X x) ⟦p⟧ ⟦q⟧ = ⟦transAt i q p⟧ := by
  rw [transAt_indep (Classical.arbitrary N) q, ← fromLoop_trans_toLoop]
  apply Quotient.sound
  rfl

/-- Characterization of multiplicative inverse -/
/-
**HomotopyGroup.inv_spec** 是 Mathlib 中的一个定理，位于命名空间 `HomotopyGroup`。
形式化陈述：inv_spec [Nonempty N] {i} {p : Ω^ N X x} : ((⟦p⟧)⁻¹ : HomotopyGroup N X x)
 = ⟦symmAt i p⟧
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HomotopyGroup.symmAt_indep`：symmAt_indep {i} (j) (f : Ω^ N X x) : (⟦symm
At i f⟧ : HomotopyGroup N X x) = ⟦symmAt j f⟧
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `GenLoop.fromLoop_symm_toLoop`：fromLoop_symm_toLoop {i : N} {p : Ω^ N X x
} : fromLoop i (toLoop i p).symm = symmAt i p
· 使用定理 `Quotient.sound`：∀ {α : Sort u} {s : Setoid α} {a b : α}, a ≈ b → ⟦a⟧ = ⟦
b⟧
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Setoid.refl`：∀ {α : Sort u} [inst : Setoid α] (a : α), a ≈ a

--- 原说明 ---
Characterization of multiplicative inverse
-/
theorem inv_spec [Nonempty N] {i} {p : Ω^ N X x} :
    ((⟦p⟧)⁻¹ : HomotopyGroup N X x) = ⟦symmAt i p⟧ := by
  rw [symmAt_indep (Classical.arbitrary N) p, ← fromLoop_symm_toLoop]
  apply Quotient.sound
  rfl

/-- Multiplication on `HomotopyGroup N X x` is commutative for nontrivial `N`.
  In particular, multiplication on `π_(n+2)` is commutative. -/
/-
**HomotopyGroup.commGroup** 是 Mathlib 中的一个实例，位于命名空间 `HomotopyGroup`。
形式化陈述：commGroup [Nontrivial N] : CommGroup (HomotopyGroup N X x)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Nontrivial.to_nonempty`：∀ {α : Type u_1} [Nontrivial α], Nonempty α

--- 原说明 ---
Multiplication on `HomotopyGroup N X x` is commutative for nontrivial `N`.
  In particular, multiplication on `π_(n+2)` is commutative.
-/
instance commGroup [Nontrivial N] : CommGroup (HomotopyGroup N X x) :=
  let h := exists_ne (Classical.arbitrary N)
  fast_instance% @EckmannHilton.commGroup (HomotopyGroup N X x) _ 1
    (isUnital_auxGroup <| Classical.choose h) _
    (by
      rintro ⟨a⟩ ⟨b⟩ ⟨c⟩ ⟨d⟩
      apply congr_arg Quotient.mk'
      simp only [fromLoop_trans_toLoop, transAt_distrib <| Classical.choose_spec h, coe_toEquiv,
        loopHomeo_apply, coe_symm_toEquiv, loopHomeo_symm_apply])

/-- The homotopy group at `x` indexed by a singleton is isomorphic to the fundamental group,
  i.e. the loops based at `x` up to homotopy. -/
/-
**HomotopyGroup.homotopyGroupOfUniqueMulEquivFundamentalGroup** 是 Mathlib 中的一个定义
，位于命名空间 `HomotopyGroup`。
形式化陈述：homotopyGroupOfUniqueMulEquivFundamentalGroup (N) [Unique N] : HomotopyGro
up N X x ≃* FundamentalGroup X x where toEquiv
参数：N。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α

--- 原说明 ---
The homotopy group at `x` indexed by a singleton is isomorphic to the fundamenta
l group,
  i.e. the loops based at `x` up to homotopy.
-/
def homotopyGroupOfUniqueMulEquivFundamentalGroup (N) [Unique N] :
    HomotopyGroup N X x ≃* FundamentalGroup X x where
  toEquiv := homotopyGroupEquivFundamentalGroupOfUnique N
  map_mul' a b := Quotient.inductionOn₂ a b fun p q => by
    simp only [HomotopyGroup.mul_spec (i := default)]
    apply Quotient.sound
    simp [genLoopEquivOfUnique_transAt]

/-- The first homotopy group at `x` is isomorphic to the fundamental group. -/
/-
**HomotopyGroup.pi1MulEquivFundamentalGroup** 是 Mathlib 中的一个定义，位于命名空间 `HomotopyG
roup`。
形式化陈述：pi1MulEquivFundamentalGroup : π_ 1 X x ≃* FundamentalGroup X x where toEqu
iv
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The first homotopy group at `x` is isomorphic to the fundamental group.
-/
def pi1MulEquivFundamentalGroup :
    π_ 1 X x ≃* FundamentalGroup X x where
  toEquiv := HomotopyGroup.pi1EquivFundamentalGroup (X := X) (x := x)
  map_mul' a b := Quotient.inductionOn₂ a b fun p q => by
    simp only [HomotopyGroup.mul_spec (i := (0 : Fin 1))]
    apply Quotient.sound
    rw [Unique.eq_default 0, genLoopEquivOfUnique_transAt]

end HomotopyGroup

