/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Ira Fesefeldt
-/
module

public import Mathlib.Control.Monad.Basic
public import Mathlib.Dynamics.FixedPoints.Basic
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.Iterate
public import Mathlib.Order.Part
public import Mathlib.Order.Preorder.Chain
public import Mathlib.Order.ScottContinuity

/-!
# Omega Complete Partial Orders

An omega-complete partial order is a partial order with a supremum
operation on increasing sequences indexed by natural numbers (which we
call `ωSup`). In this sense, it is strictly weaker than join complete
semi-lattices as only ω-sized totally ordered sets have a supremum.

The concept of an omega-complete partial order (ωCPO) is useful for the
formalization of the semantics of programming languages. Its notion of
supremum helps define the meaning of recursive procedures.

## Main definitions

* class `OmegaCompletePartialOrder`
* `ite`, `map`, `bind`, `seq` as continuous morphisms

## Instances of `OmegaCompletePartialOrder`

* `Part`
* every `CompleteLattice` (proved in `BourbakiWitt` as a special case of chain-complete
  partial orders)
* pi-types
* product types
* `OrderHom`
* `ContinuousHom` (with notation →𝒄)
  * an instance of `OmegaCompletePartialOrder (α →𝒄 β)`
* `ContinuousHom.ofFun`
* `ContinuousHom.ofMono`
* continuous functions:
  * `id`
  * `ite`
  * `const`
  * `Part.bind`
  * `Part.map`
  * `Part.seq`

## References

* [Chain-complete posets and directed sets with applications][markowsky1976]
* [Recursive definitions of partial functions and their computations][cadiou1972]
* [Semantics of Programming Languages: Structures and Techniques][gunter1992]
-/

@[expose] public section

assert_not_exists IsOrderedMonoid

universe u v
variable {ι : Sort*} {α β γ δ : Type*}

namespace OmegaCompletePartialOrder

/-- A chain is a monotone sequence.

This is made a one-field structure around order homomorphisms `ℕ →o α` because we want to endow
chains with the domination order rather than the pointwise order. See `Chain.instLE`.

See the definition on page 114 of [gunter1992]. -/
/-
**OmegaCompletePartialOrder.Chain** 是 Mathlib 中的一个归纳类型，位于命名空间 `OmegaCompletePart
ialOrder`。
形式化陈述：(α : Type u) → [Preorder α] → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A chain is a monotone sequence.

This is made a one-field structure around order homomorphisms `ℕ →o α` because w
e want to endow
chains with the domination order rather than the pointwise order. See `Chain.ins
tLE`.

See the definition on page 114 of [gunter1992].
-/
structure Chain (α : Type u) [Preorder α] extends ℕ →o α

namespace Chain
variable [Preorder α] [Preorder β] [Preorder γ]

/-
**OmegaCompletePartialOrder.Chain.** 是 Mathlib 中的一个实例，位于命名空间 `OmegaCompleteParti
alOrder.Chain`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FunLike (Chain α) ℕ α where
  coe c := c.toOrderHom
  coe_injective := by rintro ⟨f, hf⟩; congr!

initialize_simps_projections Chain (toFun → apply)
/-
**OmegaCompletePartialOrder.Chain.** 是 Mathlib 中的一个实例，位于命名空间 `OmegaCompleteParti
alOrder.Chain`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : OrderHomClass (Chain α) ℕ α where
  map_rel c _m _n hmn := c.monotone hmn

/-- See note [partially-applied ext lemmas]. -/
/-
**OmegaCompletePartialOrder.Chain.ext** 是 Mathlib 中的一个定理，位于命名空间 `OmegaCompletePa
rtialOrder.Chain`。
形式化陈述：∀ {α : Type u_2} [inst : Preorder α] ⦃f g : OmegaCompletePartialOrder.Chai
n α⦄, ⇑f = ⇑g → f = g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext'`：ext' {f g : F} (h : (f : forall a : α, β a) = (g : forall
 a : α, β a)) : f = g

--- 原说明 ---
See note [partially-applied ext lemmas].
-/
@[ext] lemma ext ⦃f g : Chain α⦄ (h : ⇑f = ⇑g) : f = g := DFunLike.ext' h
/-
**OmegaCompletePartialOrder.Chain.coe_toOrderHom** 是 Mathlib 中的一个定理，位于命名空间 `Omeg
aCompletePartialOrder.Chain`。
形式化陈述：∀ {α : Type u_2} [inst : Preorder α] (c : OmegaCompletePartialOrder.Chain 
α), ⇑c.toOrderHom = ⇑c
参数：c : OmegaCompletePartialOrder.Chain α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See note [partially-applied ext lemmas].
-/
@[simp] lemma coe_toOrderHom (c : Chain α) : ⇑c.toOrderHom = c := rfl
/-
**OmegaCompletePartialOrder.Chain.** 是 Mathlib 中的一个实例，位于命名空间 `OmegaCompleteParti
alOrder.Chain`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See note [partially-applied ext lemmas].
-/
instance [Inhabited α] : Inhabited (Chain α) :=
  ⟨⟨default, fun _ _ _ => le_rfl⟩⟩
/-
**OmegaCompletePartialOrder.Chain.** 是 Mathlib 中的一个实例，位于命名空间 `OmegaCompleteParti
alOrder.Chain`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Membership α (Chain α) where
  mem c a := ∃ i, a = c i

variable (c c' : Chain α)
variable (f : α →o β)
variable (g : β →o γ)
/-
**OmegaCompletePartialOrder.Chain.instLE** 是 Mathlib 中的一个实例，位于命名空间 `OmegaComplet
ePartialOrder.Chain`。
形式化陈述：instLE : LE (Chain α) where le x y
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instLE : LE (Chain α) where le x y := ∀ i, ∃ j, x i ≤ y j
/-
**OmegaCompletePartialOrder.Chain.isChain_range** 是 Mathlib 中的一个引理，位于命名空间 `Omega
CompletePartialOrder.Chain`。
形式化陈述：isChain_range : IsChain (· <= ·) (Set.range c)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.isChain_range`：Monotone.isChain_range [LinearOrder α] [Preorder
 β] {f : α -> β} (hf : Monotone f) : IsChain (· <= ·) (range f)
· 使用定理 `OrderHomClass.mono`：∀ {F : Type u_1} {α : Type u_2} {β : Type u_3} [inst
 : Preorder α] [inst_1 : Preorder β] [inst_2 : FunLike F α β]   [OrderHomClass F
 α β] (f…
· 使用定理 `OmegaCompletePartialOrder.Chain.instOrderHomClassNat`：∀ {α : Type u_2} [
inst : Preorder α], OrderHomClass (OmegaCompletePartialOrder.Chain α) ℕ α
-/
lemma isChain_range : IsChain (· ≤ ·) (Set.range c) := Monotone.isChain_range (OrderHomClass.mono c)
/-
**OmegaCompletePartialOrder.Chain.directed** 是 Mathlib 中的一个引理，位于命名空间 `OmegaCompl
etePartialOrder.Chain`。
形式化陈述：directed : Directed (· <= ·) c
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `directedOn_range`：directedOn_range {f : ι -> α} : DirectedOn r (.range f
) ↔ Directed r f
· 使用定理 `IsChain.directedOn`：IsChain.directedOn (H : IsChain r s) : DirectedOn r 
s
· 使用引理 `OmegaCompletePartialOrder.Chain.isChain_range`：isChain_range : IsChain (
· <= ·) (Set.range c)
-/
lemma directed : Directed (· ≤ ·) c := directedOn_range.1 c.isChain_range.directedOn

/-- `map` function for `Chain` -/
@[simps toOrderHom]
/-
**OmegaCompletePartialOrder.Chain.map** 是 Mathlib 中的一个定义，位于命名空间 `OmegaCompletePa
rtialOrder.Chain`。
形式化陈述：map : Chain β where toOrderHom
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`map` function for `Chain`
-/
def map : Chain β where toOrderHom := f.comp c.toOrderHom
/-
**OmegaCompletePartialOrder.Chain.coe_map** 是 Mathlib 中的一个定理，位于命名空间 `OmegaComple
tePartialOrder.Chain`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [inst_1 : Preorder β] 
(c : OmegaCompletePartialOrder.Chain α)   (f : α →o β), ⇑(c.map f) = ⇑f ∘ ⇑c
参数：c : OmegaCompletePartialOrder.Chain α；f : α →o β；c.map f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_map : ⇑(c.map f) = f ∘ c := rfl

@[deprecated (since := "2026-03-27")] alias map_coe := coe_map

variable {f}
/-
**OmegaCompletePartialOrder.Chain.mem_map** 是 Mathlib 中的一个定理，位于命名空间 `OmegaComple
tePartialOrder.Chain`。
形式化陈述：mem_map (x : α) : x in c -> f x in Chain.map c f
参数：x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem mem_map (x : α) : x ∈ c → f x ∈ Chain.map c f :=
  fun ⟨i, h⟩ => ⟨i, h.symm ▸ rfl⟩
/-
**OmegaCompletePartialOrder.Chain.exists_of_mem_map** 是 Mathlib 中的一个定理，位于命名空间 `O
megaCompletePartialOrder.Chain`。
形式化陈述：exists_of_mem_map {b : β} : b in c.map f -> exists a, a in c ∧ f a = b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem exists_of_mem_map {b : β} : b ∈ c.map f → ∃ a, a ∈ c ∧ f a = b :=
  fun ⟨i, h⟩ => ⟨c i, ⟨i, rfl⟩, h.symm⟩

@[simp]
/-
**OmegaCompletePartialOrder.Chain.mem_map_iff** 是 Mathlib 中的一个定理，位于命名空间 `OmegaCo
mpletePartialOrder.Chain`。
形式化陈述：mem_map_iff {b : β} : b in c.map f ↔ exists a, a in c ∧ f a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OmegaCompletePartialOrder.Chain.exists_of_mem_map`：exists_of_mem_map {b 
: β} : b in c.map f -> exists a, a in c ∧ f a = b
· 使用定理 `OmegaCompletePartialOrder.Chain.mem_map`：mem_map (x : α) : x in c -> f x
 in Chain.map c f
-/
theorem mem_map_iff {b : β} : b ∈ c.map f ↔ ∃ a, a ∈ c ∧ f a = b :=
  ⟨exists_of_mem_map _, fun h => by
    rcases h with ⟨w, h, h'⟩
    subst b
    apply mem_map c _ h⟩
/-
**OmegaCompletePartialOrder.Chain.map_id** 是 Mathlib 中的一个定理，位于命名空间 `OmegaComplet
ePartialOrder.Chain`。
形式化陈述：∀ {α : Type u_2} [inst : Preorder α] (c : OmegaCompletePartialOrder.Chain 
α), c.map OrderHom.id = c
参数：c : OmegaCompletePartialOrder.Chain α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OmegaCompletePartialOrder.Chain.ext`：∀ {α : Type u_2} [inst : Preorder α
] ⦃f g : OmegaCompletePartialOrder.Chain α⦄, ⇑f = ⇑g → f = g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OrderHom.id_coe`：∀ {α : Type u_2} [inst : Preorder α], ⇑OrderHom.id = id
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma map_id : c.map OrderHom.id = c := by ext; simp
/-
**OmegaCompletePartialOrder.Chain.map_comp** 是 Mathlib 中的一个定理，位于命名空间 `OmegaCompl
etePartialOrder.Chain`。
形式化陈述：map_comp : (c.map f).map g = c.map (g.comp f)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_comp : (c.map f).map g = c.map (g.comp f) :=
  rfl

@[gcongr, mono]
/-
**OmegaCompletePartialOrder.Chain.map_le_map** 是 Mathlib 中的一个定理，位于命名空间 `OmegaCom
pletePartialOrder.Chain`。
形式化陈述：map_le_map {g : α ->o β} (h : f <= g) : c.map f <= c.map g
参数：h : f <= g。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_le_map {g : α →o β} (h : f ≤ g) : c.map f ≤ c.map g := fun _ ↦ ⟨_, h _⟩

/-- `OmegaCompletePartialOrder.Chain.zip` pairs up the elements of two chains
that have the same index. -/
@[simps toOrderHom]
/-
**OmegaCompletePartialOrder.Chain.zip** 是 Mathlib 中的一个定义，位于命名空间 `OmegaCompletePa
rtialOrder.Chain`。
形式化陈述：zip (c₀ : Chain α) (c₁ : Chain β) : Chain (α × β) where toOrderHom
参数：c₀ : Chain α；c₁ : Chain β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`OmegaCompletePartialOrder.Chain.zip` pairs up the elements of two chains
that have the same index.
-/
def zip (c₀ : Chain α) (c₁ : Chain β) : Chain (α × β) where
  toOrderHom := c₀.toOrderHom.prod c₁.toOrderHom
/-
**OmegaCompletePartialOrder.Chain.zip_apply** 是 Mathlib 中的一个定理，位于命名空间 `OmegaComp
letePartialOrder.Chain`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [inst_1 : Preorder β] 
(c₀ : OmegaCompletePartialOrder.Chain α)   (c₁ : OmegaCompletePartialOrder.Chain
 β) (n : ℕ), (c₀.zip c₁) n = (c₀ n, c₁ n)
参数：c₀ : OmegaCompletePartialOrder.Chain α；c₁ : OmegaCompletePartialOrder.Chain β
；n : ℕ；c₀.zip c₁；c₀ n, c₁ n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma zip_apply (c₀ : Chain α) (c₁ : Chain β) (n : ℕ) : c₀.zip c₁ n = (c₀ n, c₁ n) := rfl

@[deprecated (since := "2026-03-27")] alias zip_coe := zip_apply

/-- An example of a `Chain` constructed from an ordered pair. -/
/-
**OmegaCompletePartialOrder.Chain.pair** 是 Mathlib 中的一个定义，位于命名空间 `OmegaCompleteP
artialOrder.Chain`。
形式化陈述：pair (a b : α) (hab : a <= b) : Chain α where toFun | 0 => a | _ => b mono
tone' _ _ _
参数：a b : α；hab : a <= b。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An example of a `Chain` constructed from an ordered pair.
-/
def pair (a b : α) (hab : a ≤ b) : Chain α where
  toFun
    | 0 => a
    | _ => b
  monotone' _ _ _ := by aesop
/-
**OmegaCompletePartialOrder.Chain.pair_zero** 是 Mathlib 中的一个定理，位于命名空间 `OmegaComp
letePartialOrder.Chain`。
形式化陈述：∀ {α : Type u_2} [inst : Preorder α] (a b : α) (hab : a ≤ b), (OmegaComple
tePartialOrder.Chain.pair a b hab) 0 = a
参数：a b : α；hab : a ≤ b；OmegaCompletePartialOrder.Chain.pair a b hab。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma pair_zero (a b : α) (hab) : pair a b hab 0 = a := rfl
/-
**OmegaCompletePartialOrder.Chain.pair_succ** 是 Mathlib 中的一个定理，位于命名空间 `OmegaComp
letePartialOrder.Chain`。
形式化陈述：∀ {α : Type u_2} [inst : Preorder α] (a b : α) (hab : a ≤ b) (n : ℕ),   (O
megaCompletePartialOrder.Chain.pair a b hab) (n + 1) = b
参数：a b : α；hab : a ≤ b；n : ℕ；OmegaCompletePartialOrder.Chain.pair a b hab；n + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma pair_succ (a b : α) (hab) (n : ℕ) : pair a b hab (n + 1) = b := rfl
/-
**OmegaCompletePartialOrder.Chain.range_pair** 是 Mathlib 中的一个定理，位于命名空间 `OmegaCom
pletePartialOrder.Chain`。
形式化陈述：∀ {α : Type u_2} [inst : Preorder α] (a b : α) (hab : a ≤ b),   Set.range 
⇑(OmegaCompletePartialOrder.Chain.pair a b hab) = {a, b}
参数：a b : α；hab : a ≤ b；OmegaCompletePartialOrder.Chain.pair a b hab。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Nat.or_exists_add_one`：∀ {p : ℕ → Prop}, (p 0 ∨ ∃ n, p (n + 1)) ↔ Exists
 p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
-/
@[simp] lemma range_pair (a b : α) (hab) : Set.range (pair a b hab) = {a, b} := by
  ext; exact Nat.or_exists_add_one.symm.trans (by aesop)
/-
**OmegaCompletePartialOrder.Chain.pair_zip_pair** 是 Mathlib 中的一个定理，位于命名空间 `Omega
CompletePartialOrder.Chain`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [inst_1 : Preorder β] 
(a₁ a₂ : α) (b₁ b₂ : β) (ha : a₁ ≤ a₂)   (hb : b₁ ≤ b₂),   (OmegaCompletePartial
Order.Chain.pair a₁ a₂ ha).zip (OmegaCompletePartialOrder.Chain.pair b₁ b₂ hb) =
     OmegaCompletePartialOrder.Chain.pair (a₁, b₁) (a₂, b₂) ⋯
参数：a₁ a₂ : α；b₁ b₂ : β；ha : a₁ ≤ a₂；hb : b₁ ≤ b₂；OmegaCompletePartialOrder.Chain
.pair a₁ a₂ ha；OmegaCompletePartialOrder.Chain.pair b₁ b₂ hb；a₁, b₁；a₂, b₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OmegaCompletePartialOrder.Chain.ext`：∀ {α : Type u_2} [inst : Preorder α
] ⦃f g : OmegaCompletePartialOrder.Chain α⦄, ⇑f = ⇑g → f = g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Prod.le_def`：∀ {α : Type u_2} {β : Type u_3} [inst : LE α] [inst_1 : LE 
β] {x y : α × β}, x ≤ y ↔ x.1 ≤ y.1 ∧ x.2 ≤ y.2
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
@[simp] lemma pair_zip_pair (a₁ a₂ : α) (b₁ b₂ : β) (ha hb) :
    (pair a₁ a₂ ha).zip (pair b₁ b₂ hb) = pair (a₁, b₁) (a₂, b₂) (Prod.le_def.2 ⟨ha, hb⟩) := by
  ext n : 2; cases n <;> rfl

end Chain

end OmegaCompletePartialOrder

open OmegaCompletePartialOrder Chain

/-- An omega-complete partial order is a partial order with a supremum
operation on increasing sequences indexed by natural numbers (which we
call `ωSup`). In this sense, it is strictly weaker than join complete
semi-lattices as only ω-sized totally ordered sets have a supremum.

See the definition on page 114 of [gunter1992]. -/
/-
**OmegaCompletePartialOrder** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u_6 → Type u_6
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An omega-complete partial order is a partial order with a supremum
operation on increasing sequences indexed by natural numbers (which we
call `ωSup`). In this sense, it is strictly weaker than join complete
semi-lattices as only ω-sized totally ordered sets have a supremum.

See the definition on page 114 of [gunter1992].
-/
class OmegaCompletePartialOrder (α : Type*) extends PartialOrder α where
  /-- The supremum of an increasing sequence -/
  ωSup : Chain α → α
  /-- `ωSup` is an upper bound of the increasing sequence -/
  le_ωSup : ∀ c : Chain α, ∀ i, c i ≤ ωSup c
  /-- `ωSup` is a lower bound of the set of upper bounds of the increasing sequence -/
  ωSup_le : ∀ (c : Chain α) (x), (∀ i, c i ≤ x) → ωSup c ≤ x

namespace OmegaCompletePartialOrder
variable [OmegaCompletePartialOrder α]

/-- Transfer an `OmegaCompletePartialOrder` on `β` to an `OmegaCompletePartialOrder` on `α`
using a strictly monotone function `f : β →o α`, a definition of ωSup and a proof that `f` is
continuous with regard to the provided `ωSup` and the ωCPO on `α`. -/
/-
**OmegaCompletePartialOrder.lift** 是 Mathlib 中的一个定义，位于命名空间 `OmegaCompletePartial
Order`。
形式化陈述：{α : Type u_2} →   {β : Type u_3} →     [inst : OmegaCompletePartialOrder 
α] →       [inst_1 : PartialOrder β] →         (f : β →o α) →           (ωSup₀ :
 OmegaCompletePartialOrder.Chain β → β) →             (∀ (x y : β), f x ≤ f y → 
x ≤ y) →               (∀ (c : OmegaCompletePartialOrder.Chain β), f (ωSup₀ c) =
 OmegaCompletePartialOrder.ωSup (c.map f)) →                 OmegaCompletePartia
lOrder β
参数：f : β →o α；ωSup₀ : OmegaCompletePartialOrder.Chain β → β；∀ (x y : β), f x ≤ f
 y → x ≤ y；∀ (c : OmegaCompletePartialOrder.Chain β), f (ωSup₀ c) = OmegaComplet
ePartialOrder.ωSup (c.map f)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Transfer an `OmegaCompletePartialOrder` on `β` to an `OmegaCompletePartialOrder`
 on `α`
using a strictly monotone function `f : β →o α`, a definition of ωSup and a proo
f that `f` is
continuous with regard to the provided `ωSup` and the ωCPO on `α`.
-/
protected abbrev lift [PartialOrder β] (f : β →o α) (ωSup₀ : Chain β → β)
    (h : ∀ x y, f x ≤ f y → x ≤ y) (h' : ∀ c, f (ωSup₀ c) = ωSup (c.map f)) :
    OmegaCompletePartialOrder β where
  ωSup := ωSup₀
  ωSup_le c x hx := h _ _ (by rw [h']; apply ωSup_le; intro i; apply f.monotone (hx i))
  le_ωSup c i := h _ _ (by rw [h']; apply le_ωSup (c.map f))
/-
**OmegaCompletePartialOrder.le_** 是 Mathlib 中的一个定理，位于命名空间 `OmegaCompletePartialO
rder`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem le_ωSup_of_le {c : Chain α} {x : α} (i : ℕ) (h : x ≤ c i) : x ≤ ωSup c :=
  le_trans h (le_ωSup c _)
/-
**OmegaCompletePartialOrder.** 是 Mathlib 中的一个定理，位于命名空间 `OmegaCompletePartialOrde
r`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ωSup_total {c : Chain α} {x : α} (h : ∀ i, c i ≤ x ∨ x ≤ c i) : ωSup c ≤ x ∨ x ≤ ωSup c :=
  by_cases
    (fun (this : ∀ i, c i ≤ x) => Or.inl (ωSup_le _ _ this))
    (fun (this : ¬∀ i, c i ≤ x) =>
      have : ∃ i, ¬c i ≤ x := by simp only [not_forall] at this ⊢; assumption
      let ⟨i, hx⟩ := this
      have : x ≤ c i := (h i).resolve_left hx
      Or.inr <| le_ωSup_of_le _ this)

@[gcongr, mono]
/-
**OmegaCompletePartialOrder.** 是 Mathlib 中的一个定理，位于命名空间 `OmegaCompletePartialOrde
r`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ωSup_le_ωSup_of_le {c₀ c₁ : Chain α} (h : c₀ ≤ c₁) : ωSup c₀ ≤ ωSup c₁ :=
  (ωSup_le _ _) fun i => by
    obtain ⟨_, h⟩ := h i
    exact le_trans h (le_ωSup _ _)
/-
**OmegaCompletePartialOrder.** 是 Mathlib 中的一个定理，位于命名空间 `OmegaCompletePartialOrde
r`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem ωSup_le_iff {c : Chain α} {x : α} : ωSup c ≤ x ↔ ∀ i, c i ≤ x := by
  constructor <;> intros
  · trans ωSup c
    · exact le_ωSup _ _
    · assumption
  exact ωSup_le _ _ ‹_›
/-
**OmegaCompletePartialOrder.isLUB_range_** 是 Mathlib 中的一个引理，位于命名空间 `OmegaComplet
ePartialOrder`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isLUB_range_ωSup (c : Chain α) : IsLUB (Set.range c) (ωSup c) := by
  constructor
  · simp only [upperBounds, Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff,
      Set.mem_ofPred_eq]
    exact fun a ↦ le_ωSup c a
  · simp only [lowerBounds, upperBounds, Set.mem_range, forall_exists_index,
      forall_apply_eq_imp_iff, Set.mem_ofPred_eq]
    exact fun ⦃a⦄ a_1 ↦ ωSup_le c a a_1
/-
**OmegaCompletePartialOrder.** 是 Mathlib 中的一个引理，位于命名空间 `OmegaCompletePartialOrde
r`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ωSup_eq_of_isLUB {c : Chain α} {a : α} (h : IsLUB (Set.range c) a) : a = ωSup c := by
  rw [le_antisymm_iff]
  simp only [IsLUB, IsLeast, upperBounds, lowerBounds, Set.mem_range, forall_exists_index,
    forall_apply_eq_imp_iff, Set.mem_ofPred_eq] at h
  constructor
  · apply h.2
    exact fun a ↦ le_ωSup c a
  · rw [ωSup_le_iff]
    apply h.1

/-- A subset `p : α → Prop` of the type closed under `ωSup` induces an
`OmegaCompletePartialOrder` on the subtype `{a : α // p a}`. -/
@[instance_reducible]
/-
**OmegaCompletePartialOrder.subtype** 是 Mathlib 中的一个定义，位于命名空间 `OmegaCompletePart
ialOrder`。
形式化陈述：subtype {α : Type*} [OmegaCompletePartialOrder α] (p : α -> Prop) (hp : fo
rall c : Chain α, (forall i in c, p i) -> p (ωSup c)) : OmegaCompletePartialOrde
r (Subtype p)
参数：p : α -> Prop；hp : forall c : Chain α, (forall i in c, p i) -> p (ωSup c)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subset `p : α → Prop` of the type closed under `ωSup` induces an
`OmegaCompletePartialOrder` on the subtype `{a : α // p a}`.
-/
def subtype {α : Type*} [OmegaCompletePartialOrder α] (p : α → Prop)
    (hp : ∀ c : Chain α, (∀ i ∈ c, p i) → p (ωSup c)) : OmegaCompletePartialOrder (Subtype p) :=
  OmegaCompletePartialOrder.lift (OrderHom.Subtype.val p)
    (fun c => ⟨ωSup _, hp (c.map (OrderHom.Subtype.val p)) fun _ ⟨n, q⟩ => q.symm ▸ (c n).2⟩)
    (fun _ _ h => h) (fun _ => rfl)

section Continuity

variable [OmegaCompletePartialOrder β]
variable [OmegaCompletePartialOrder γ]
variable {f : α → β} {g : β → γ}

/-- A function `f` between `ω`-complete partial orders is `ωScottContinuous` if it is
Scott continuous over chains. -/
@[fun_prop]
/-
**OmegaCompletePartialOrder.** 是 Mathlib 中的一个定义，位于命名空间 `OmegaCompletePartialOrde
r`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function `f` between `ω`-complete partial orders is `ωScottContinuous` if it i
s
Scott continuous over chains.
-/
def ωScottContinuous (f : α → β) : Prop :=
    ScottContinuousOn (Set.range fun c : Chain α => Set.range c) f
/-
**OmegaCompletePartialOrder._root_.ScottContinuous.** 是 Mathlib 中的一个引理，位于命名空间 `O
megaCompletePartialOrder`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.ScottContinuous.ωScottContinuous (hf : ScottContinuous f) : ωScottContinuous f :=
  hf.scottContinuousOn
/-
**OmegaCompletePartialOrder.** 是 Mathlib 中的一个引理，位于命名空间 `OmegaCompletePartialOrde
r`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ωScottContinuous.monotone (h : ωScottContinuous f) : Monotone f :=
  ScottContinuousOn.monotone _ (fun a b hab => by
    use pair a b hab; exact range_pair a b hab) h
/-
**OmegaCompletePartialOrder.** 是 Mathlib 中的一个引理，位于命名空间 `OmegaCompletePartialOrde
r`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ωScottContinuous.isLUB {c : Chain α} (hf : ωScottContinuous f) :
    IsLUB (Set.range (c.map ⟨f, hf.monotone⟩)) (f (ωSup c)) := by
  simpa [Set.range_comp]
    using hf (by simp) (Set.range_nonempty _) (isChain_range c).directedOn (isLUB_range_ωSup c)

@[fun_prop, to_fun (attr := simp)]
/-
**OmegaCompletePartialOrder.** 是 Mathlib 中的一个引理，位于命名空间 `OmegaCompletePartialOrde
r`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ωScottContinuous.id : ωScottContinuous (id : α → α) := ScottContinuousOn.id
/-
**OmegaCompletePartialOrder.** 是 Mathlib 中的一个引理，位于命名空间 `OmegaCompletePartialOrde
r`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ωScottContinuous.map_ωSup (hf : ωScottContinuous f) (c : Chain α) :
    f (ωSup c) = ωSup (c.map ⟨f, hf.monotone⟩) := ωSup_eq_of_isLUB hf.isLUB

/-- `ωScottContinuous f` asserts that `f` is both monotone and distributes over ωSup. -/
/-
**OmegaCompletePartialOrder.** 是 Mathlib 中的一个引理，位于命名空间 `OmegaCompletePartialOrde
r`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ωScottContinuous f` asserts that `f` is both monotone and distributes over ωSup
.
-/
lemma ωScottContinuous_iff_monotone_map_ωSup :
    ωScottContinuous f ↔ ∃ hf : Monotone f, ∀ c : Chain α, f (ωSup c) = ωSup (c.map ⟨f, hf⟩) := by
  refine ⟨fun hf ↦ ⟨hf.monotone, hf.map_ωSup⟩, ?_⟩
  intro hf _ ⟨c, hc⟩ _ _ _ hda
  convert! isLUB_range_ωSup (c.map { toFun := f, monotone' := hf.1 })
  · simp [← hc, ← (Set.range_comp f ⇑c)]
  · rw [← hc] at hda
    rw [← hf.2 c, ωSup_eq_of_isLUB hda]

alias ⟨ωScottContinuous.monotone_map_ωSup, ωScottContinuous.of_monotone_map_ωSup⟩ :=
  ωScottContinuous_iff_monotone_map_ωSup

/--
A monotone function `f : α →o β` is ωScott continuous if and only if it distributes over ωSup. -/
/-
**OmegaCompletePartialOrder.** 是 Mathlib 中的一个引理，位于命名空间 `OmegaCompletePartialOrde
r`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A monotone function `f : α →o β` is ωScott continuous if and only if it distribu
tes over ωSup.
-/
lemma ωScottContinuous_iff_map_ωSup_of_orderHom {f : α →o β} :
    ωScottContinuous f ↔ ∀ c : Chain α, f (ωSup c) = ωSup (c.map f) := by
  rw [ωScottContinuous_iff_monotone_map_ωSup]
  exact exists_prop_of_true f.monotone'

alias ⟨ωScottContinuous.map_ωSup_of_orderHom, ωScottContinuous.of_map_ωSup_of_orderHom⟩ :=
  ωScottContinuous_iff_map_ωSup_of_orderHom

-- Allow `to_fun` to eta-expand `g ∘ f`. Ideally, `Function.comp_def` would be a global pull lemma
-- instead, which is not supported yet: see https://github.com/leanprover-community/mathlib4/issues/40183.
attribute [local push ←] Function.comp_def
attribute [local push] Function.const_def

@[fun_prop, to_fun]
/-
**OmegaCompletePartialOrder.** 是 Mathlib 中的一个引理，位于命名空间 `OmegaCompletePartialOrde
r`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ωScottContinuous.comp (hg : ωScottContinuous g) (hf : ωScottContinuous f) :
    ωScottContinuous (g.comp f) :=
  ωScottContinuous.of_monotone_map_ωSup
    ⟨hg.monotone.comp hf.monotone, by simp [hf.map_ωSup, hg.map_ωSup, map_comp]⟩

@[fun_prop, to_fun (attr := simp)]
/-
**OmegaCompletePartialOrder.** 是 Mathlib 中的一个引理，位于命名空间 `OmegaCompletePartialOrde
r`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ωScottContinuous.const {x : β} : ωScottContinuous (Function.const α x) :=
  ScottContinuousOn.const x

end Continuity

end OmegaCompletePartialOrder

namespace Part

/-
**Part.eq_of_chain** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
形式化陈述：eq_of_chain {c : Chain (Part α)} {a b : α} (ha : some a in c) (hb : some b
 in c) : a = b
参数：Part α；ha : some a in c；hb : some b in c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `OrderHom.monotone`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [
inst_1 : Preorder β] (f : α →o β), Monotone ⇑f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Part.eq_some_iff`：eq_some_iff {a : α} {o : Part α} : o = some a ↔ a in o
· 使用定理 `Part.mem_unique`：∀ {α : Type u_1} {a b : α} {o : Part α}, a ∈ o → b ∈ o 
→ a = b
-/
theorem eq_of_chain {c : Chain (Part α)} {a b : α} (ha : some a ∈ c) (hb : some b ∈ c) : a = b := by
  obtain ⟨i, ha⟩ := ha; replace ha := ha.symm
  obtain ⟨j, hb⟩ := hb; replace hb := hb.symm
  rw [eq_some_iff] at ha hb
  rcases le_total i j with hij | hji
  · have := c.monotone hij _ ha; apply mem_unique this hb
  · have := c.monotone hji _ hb; apply Eq.symm; apply mem_unique this ha

open scoped Classical in
/-- The (noncomputable) `ωSup` definition for the `ω`-CPO structure on `Part α`. -/
/-
**Part.** 是 Mathlib 中的一个定义，位于命名空间 `Part`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The (noncomputable) `ωSup` definition for the `ω`-CPO structure on `Part α`.
-/
protected noncomputable def ωSup (c : Chain (Part α)) : Part α :=
  if h : ∃ a, some a ∈ c then some (Classical.choose h) else none
/-
**Part.** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ωSup_eq_some {c : Chain (Part α)} {a : α} (h : some a ∈ c) : Part.ωSup c = some a :=
  have : ∃ a, some a ∈ c := ⟨a, h⟩
  have a' : some (Classical.choose this) ∈ c := Classical.choose_spec this
  calc
    Part.ωSup c = some (Classical.choose this) := dif_pos this
    _ = some a := congr_arg _ (eq_of_chain a' h)
/-
**Part.** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ωSup_eq_none {c : Chain (Part α)} (h : ¬∃ a, some a ∈ c) : Part.ωSup c = none :=
  dif_neg h
/-
**Part.mem_chain_of_mem_** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mem_chain_of_mem_ωSup {c : Chain (Part α)} {a : α} (h : a ∈ Part.ωSup c) : some a ∈ c := by
  simp only [Part.ωSup] at h; split_ifs at h with h_1
  · have h' := Classical.choose_spec h_1
    rw [← eq_some_iff] at h
    rw [← h]
    exact h'
  · rcases h with ⟨⟨⟩⟩
/-
**Part.omegaCompletePartialOrder** 是 Mathlib 中的一个实例，位于命名空间 `Part`。
形式化陈述：omegaCompletePartialOrder : OmegaCompletePartialOrder (Part α) where ωSup
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance omegaCompletePartialOrder :
    OmegaCompletePartialOrder (Part α) where
  ωSup := Part.ωSup
  le_ωSup c i := by
    intro x hx
    rw [← eq_some_iff] at hx ⊢
    rw [ωSup_eq_some]
    rw [← hx]
    exact ⟨i, rfl⟩
  ωSup_le := by
    rintro c x hx a ha
    replace ha := mem_chain_of_mem_ωSup ha
    obtain ⟨i, ha⟩ := ha
    apply hx i
    rw [← ha]
    apply mem_some

section Inst

/-
**Part.mem_** 是 Mathlib 中的一个定理，位于命名空间 `Part`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mem_ωSup (x : α) (c : Chain (Part α)) : x ∈ ωSup c ↔ some x ∈ c := by
  simp only [ωSup, Part.ωSup]
  constructor
  · exact fun a ↦ mem_chain_of_mem_ωSup a
  · intro h
    have h' : ∃ a : α, some a ∈ c := ⟨_, h⟩
    rw [dif_pos h']
    have hh := Classical.choose_spec h'
    rw [eq_of_chain hh h]
    simp

end Inst

end Part

section Pi

variable {β : α → Type*}

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ a, OmegaCompletePartialOrder (β a)] :
    OmegaCompletePartialOrder (∀ a, β a) where
  ωSup c a := ωSup (c.map (Pi.evalOrderHom a))
  ωSup_le _ _ hf a :=
    ωSup_le _ _ <| by
      rintro i
      apply hf
  le_ωSup _ _ _ := le_ωSup_of_le _ <| le_rfl

namespace OmegaCompletePartialOrder

variable [∀ x, OmegaCompletePartialOrder <| β x]
variable [OmegaCompletePartialOrder γ]
variable {f : γ → ∀ x, β x}

/-
**OmegaCompletePartialOrder.** 是 Mathlib 中的一个引理，位于命名空间 `OmegaCompletePartialOrde
r`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ωScottContinuous.apply₂ (hf : ωScottContinuous f) (a : α) : ωScottContinuous (f · a) :=
  ωScottContinuous.of_monotone_map_ωSup
    ⟨fun _ _ h ↦ hf.monotone h a, fun c ↦ congr_fun (hf.map_ωSup c) a⟩

@[fun_prop]
/-
**OmegaCompletePartialOrder.** 是 Mathlib 中的一个引理，位于命名空间 `OmegaCompletePartialOrde
r`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ωScottContinuous.apply (x : α) : ωScottContinuous (fun f : ∀ x, β x ↦ f x) :=
  apply₂ id x

@[fun_prop]
/-
**OmegaCompletePartialOrder.** 是 Mathlib 中的一个引理，位于命名空间 `OmegaCompletePartialOrde
r`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ωScottContinuous.of_apply₂ (hf : ∀ a, ωScottContinuous (f · a)) : ωScottContinuous f :=
  ωScottContinuous.of_monotone_map_ωSup
    ⟨fun _ _ h a ↦ (hf a).monotone h, fun c ↦ by ext a; apply (hf a).map_ωSup c⟩
/-
**OmegaCompletePartialOrder.** 是 Mathlib 中的一个引理，位于命名空间 `OmegaCompletePartialOrde
r`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ωScottContinuous_iff_apply₂ : ωScottContinuous f ↔ ∀ a, ωScottContinuous (f · a) :=
  ⟨ωScottContinuous.apply₂, ωScottContinuous.of_apply₂⟩

end OmegaCompletePartialOrder

end Pi

namespace Prod

variable [OmegaCompletePartialOrder α]
variable [OmegaCompletePartialOrder β]
variable [OmegaCompletePartialOrder γ]

/-- The supremum of a chain in the product `ω`-CPO. -/
@[simps]
/-
**Prod.** 是 Mathlib 中的一个定义，位于命名空间 `Prod`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The supremum of a chain in the product `ω`-CPO.
-/
protected def ωSupImpl (c : Chain (α × β)) : α × β :=
  (ωSup (c.map OrderHom.fst), ωSup (c.map OrderHom.snd))

@[simps! ωSup_fst ωSup_snd]
/-
**Prod.** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : OmegaCompletePartialOrder (α × β) where
  ωSup := Prod.ωSupImpl
  ωSup_le := fun _ _ h => ⟨ωSup_le _ _ fun i => (h i).1, ωSup_le _ _ fun i => (h i).2⟩
  le_ωSup c i := ⟨le_ωSup (c.map OrderHom.fst) i, le_ωSup (c.map OrderHom.snd) i⟩
/-
**Prod.** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ωSup_zip (c₀ : Chain α) (c₁ : Chain β) : ωSup (c₀.zip c₁) = (ωSup c₀, ωSup c₁) := rfl

@[fun_prop]
/-
**Prod.** 是 Mathlib 中的一个引理，位于命名空间 `Prod`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ωScottContinuous.prodMk
    {f : α → β} (hf : ωScottContinuous f) {g : α → γ} (hg : ωScottContinuous g) :
    ωScottContinuous fun x ↦ (f x, g x) :=
  ScottContinuousOn.prodMk (fun a b hab ↦ ⟨pair a b hab, range_pair a b hab⟩) hf hg

@[fun_prop]
/-
**Prod.** 是 Mathlib 中的一个引理，位于命名空间 `Prod`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ωScottContinuous_fst : ωScottContinuous (Prod.fst : α × β → α) :=
  ScottContinuousOn.fst

@[fun_prop]
/-
**Prod.** 是 Mathlib 中的一个引理，位于命名空间 `Prod`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ωScottContinuous_snd : ωScottContinuous (Prod.snd : α × β → β) :=
  ScottContinuousOn.snd

end Prod

namespace OmegaCompletePartialOrder
variable [OmegaCompletePartialOrder α] [OmegaCompletePartialOrder β]
variable [OmegaCompletePartialOrder γ] [OmegaCompletePartialOrder δ]

namespace OrderHom

/-- The `ωSup` operator for monotone functions. -/
@[simps]
/-
**OmegaCompletePartialOrder.OrderHom.** 是 Mathlib 中的一个定义，位于命名空间 `OmegaCompletePa
rtialOrder.OrderHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `ωSup` operator for monotone functions.
-/
protected def ωSup (c : Chain (α →o β)) : α →o β where
  toFun a := ωSup (c.map (OrderHom.apply a))
  monotone' _ _ h := ωSup_le_ωSup_of_le ((Chain.map_le_map _) fun a => a.monotone h)

@[simps! ωSup_coe]
/-
**OmegaCompletePartialOrder.OrderHom.omegaCompletePartialOrder** 是 Mathlib 中的一个实
例，位于命名空间 `OmegaCompletePartialOrder.OrderHom`。
形式化陈述：omegaCompletePartialOrder : OmegaCompletePartialOrder (α ->o β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance omegaCompletePartialOrder : OmegaCompletePartialOrder (α →o β) :=
  OmegaCompletePartialOrder.lift OrderHom.coeFnHom OrderHom.ωSup (fun _ _ h => h) fun _ => rfl

end OrderHom

variable (α β) in
/-- A monotone function on `ω`-continuous partial orders is said to be continuous
if for every chain `c : chain α`, `f (⊔ i, c i) = ⊔ i, f (c i)`.
This is just the bundled version of `OrderHom.continuous`. -/
/-
**OmegaCompletePartialOrder.ContinuousHom** 是 Mathlib 中的一个归纳类型，位于命名空间 `OmegaComp
letePartialOrder`。
形式化陈述：(α : Type u_2) → (β : Type u_3) → [OmegaCompletePartialOrder α] → [OmegaCo
mpletePartialOrder β] → Type (max u_2 u_3)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A monotone function on `ω`-continuous partial orders is said to be continuous
if for every chain `c : chain α`, `f (⊔ i, c i) = ⊔ i, f (c i)`.
This is just the bundled version of `OrderHom.continuous`.
-/
structure ContinuousHom extends OrderHom α β where
  /-- The underlying function of a `ContinuousHom` is continuous, i.e. it preserves `ωSup` -/
  protected map_ωSup' (c : Chain α) : toFun (ωSup c) = ωSup (c.map toOrderHom)

attribute [nolint docBlame] ContinuousHom.toOrderHom

@[inherit_doc] infixr:25 " →𝒄 " => ContinuousHom -- Input: \r\MIc
/-
**OmegaCompletePartialOrder.** 是 Mathlib 中的一个实例，位于命名空间 `OmegaCompletePartialOrde
r`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FunLike (α →𝒄 β) α β where
  coe f := f.toFun
  coe_injective := by rintro ⟨⟩ ⟨⟩ h; congr; exact DFunLike.ext' h
/-
**OmegaCompletePartialOrder.** 是 Mathlib 中的一个实例，位于命名空间 `OmegaCompletePartialOrde
r`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : OrderHomClass (α →𝒄 β) α β where
  map_rel f _ _ h := f.mono h
/-
**OmegaCompletePartialOrder.** 是 Mathlib 中的一个实例，位于命名空间 `OmegaCompletePartialOrde
r`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder (α →𝒄 β) :=
  (PartialOrder.lift fun f => f.toOrderHom.toFun) <| by rintro ⟨⟨⟩⟩ ⟨⟨⟩⟩ h; congr

namespace ContinuousHom

@[fun_prop]
/-
**OmegaCompletePartialOrder.ContinuousHom.** 是 Mathlib 中的一个引理，位于命名空间 `OmegaCompl
etePartialOrder.ContinuousHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected lemma ωScottContinuous (f : α →𝒄 β) : ωScottContinuous f :=
  ωScottContinuous.of_map_ωSup_of_orderHom f.map_ωSup'

-- Not a `simp` lemma because in many cases projection is simpler than a generic coercion
/-
**OmegaCompletePartialOrder.ContinuousHom.toOrderHom_eq_coe** 是 Mathlib 中的一个定理，位
于命名空间 `OmegaCompletePartialOrder.ContinuousHom`。
形式化陈述：toOrderHom_eq_coe (f : α ->𝒄 β) : f.1 = f
参数：f : α ->𝒄 β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toOrderHom_eq_coe (f : α →𝒄 β) : f.1 = f := rfl
/-
**OmegaCompletePartialOrder.ContinuousHom.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `Omeg
aCompletePartialOrder.ContinuousHom`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : OmegaCompletePartialOrder α] [inst
_1 : OmegaCompletePartialOrder β] (f : α →o β)   (hf :     ∀ (c : OmegaCompleteP
artialOrder.Chain α),       f.toFun (OmegaCompletePartialOrder.ωSup c) = OmegaCo
mpletePartialOrder.ωSup (c.map f)),   ⇑{ toOrderHom := f, map_ωSup' := hf } = ⇑f
参数：f : α →o β；hf :     ∀ (c : OmegaCompletePartialOrder.Chain α),       f.toFun 
(OmegaCompletePartialOrder.ωSup c) = OmegaCompletePartialOrder.ωSup (c.map f)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem coe_mk (f : α →o β) (hf) : ⇑(mk f hf) = f := rfl
/-
**OmegaCompletePartialOrder.ContinuousHom.coe_toOrderHom** 是 Mathlib 中的一个定理，位于命名
空间 `OmegaCompletePartialOrder.ContinuousHom`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : OmegaCompletePartialOrder α] [inst
_1 : OmegaCompletePartialOrder β]   (f : α →𝒄 β), ⇑f.toOrderHom = ⇑f
参数：f : α →𝒄 β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem coe_toOrderHom (f : α →𝒄 β) : ⇑f.1 = f := rfl

/-- See Note [custom simps projection]. We specify this explicitly because we don't have a DFunLike
instance.
-/
/-
**OmegaCompletePartialOrder.ContinuousHom.Simps.apply** 是 Mathlib 中的一个定义，位于命名空间 
`OmegaCompletePartialOrder.ContinuousHom.Simps`。
形式化陈述：{α : Type u_2} →   {β : Type u_3} → [inst : OmegaCompletePartialOrder α] →
 [inst_1 : OmegaCompletePartialOrder β] → (α →𝒄 β) → α → β
参数：α →𝒄 β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See Note [custom simps projection]. We specify this explicitly because we don't 
have a DFunLike
instance.
-/
def Simps.apply (h : α →𝒄 β) : α → β :=
  h

initialize_simps_projections ContinuousHom (toFun → apply)

/-- Constructs a `ContinuousHom` from a function `f` and a proof of `ωScottContinuous f`.
By default, the proof is inferred by `fun_prop`, which makes it ideal for simple cases.
-/
@[simps!]
/-
**OmegaCompletePartialOrder.ContinuousHom.ofFun** 是 Mathlib 中的一个定义，位于命名空间 `Omega
CompletePartialOrder.ContinuousHom`。
形式化陈述：ofFun (f : α -> β) (hf : ωScottContinuous f
参数：f : α -> β。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `OmegaCompletePartialOrder.ωScottContinuous.monotone`：∀ {α : Type u_2} {β
 : Type u_3} [inst : OmegaCompletePartialOrder α] [inst_1 : OmegaCompletePartial
Order β] {f : α → β},   OmegaCompletePart…
· 使用定理 `OmegaCompletePartialOrder.ωScottContinuous.map_ωSup`：∀ {α : Type u_2} {β
 : Type u_3} [inst : OmegaCompletePartialOrder α] [inst_1 : OmegaCompletePartial
Order β] {f : α → β}   (hf : OmegaComplet…

--- 原说明 ---
Constructs a `ContinuousHom` from a function `f` and a proof of `ωScottContinuou
s f`.
By default, the proof is inferred by `fun_prop`, which makes it ideal for simple
 cases.
-/
def ofFun (f : α → β) (hf : ωScottContinuous f := by fun_prop) : α →𝒄 β where
  toFun := f
  monotone' := hf.monotone
  map_ωSup' := hf.map_ωSup
/-
**OmegaCompletePartialOrder.ContinuousHom.congr_fun** 是 Mathlib 中的一个定理，位于命名空间 `O
megaCompletePartialOrder.ContinuousHom`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : OmegaCompletePartialOrder α] [inst
_1 : OmegaCompletePartialOrder β]   {f g : α →𝒄 β}, f = g → ∀ (x : α), f x = g x
参数：x : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
-/
protected theorem congr_fun {f g : α →𝒄 β} (h : f = g) (x : α) : f x = g x :=
  DFunLike.congr_fun h x
/-
**OmegaCompletePartialOrder.ContinuousHom.congr_arg** 是 Mathlib 中的一个定理，位于命名空间 `O
megaCompletePartialOrder.ContinuousHom`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : OmegaCompletePartialOrder α] [inst
_1 : OmegaCompletePartialOrder β] (f : α →𝒄 β)   {x y : α}, x = y → f x = f y
参数：f : α →𝒄 β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
protected theorem congr_arg (f : α →𝒄 β) {x y : α} (h : x = y) : f x = f y :=
  congr_arg f h
/-
**OmegaCompletePartialOrder.ContinuousHom.monotone** 是 Mathlib 中的一个定理，位于命名空间 `Om
egaCompletePartialOrder.ContinuousHom`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : OmegaCompletePartialOrder α] [inst
_1 : OmegaCompletePartialOrder β]   (f : α →𝒄 β), Monotone ⇑f
参数：f : α →𝒄 β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderHom.monotone'`：∀ {α : Type u_6} {β : Type u_7} [inst : Preorder α] 
[inst_1 : Preorder β] (self : α →o β), Monotone self.toFun
-/
protected theorem monotone (f : α →𝒄 β) : Monotone f :=
  f.monotone'

@[gcongr, mono]
/-
**OmegaCompletePartialOrder.ContinuousHom.apply_mono** 是 Mathlib 中的一个定理，位于命名空间 `
OmegaCompletePartialOrder.ContinuousHom`。
形式化陈述：apply_mono {f g : α ->𝒄 β} {x y : α} (h₁ : f <= g) (h₂ : x <= y) : f x <= 
g y
参数：h₁ : f <= g；h₂ : x <= y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderHom.apply_mono`：apply_mono {f g : α ->o β} {x y : α} (h₁ : f <= g) 
(h₂ : x <= y) : f x <= g y
· 使用定理 `OmegaCompletePartialOrder.instOrderHomClassContinuousHom`：∀ {α : Type u_
2} {β : Type u_3} [inst : OmegaCompletePartialOrder α] [inst_1 : OmegaCompletePa
rtialOrder β],   OrderHomClass (α →𝒄 β) α β
-/
theorem apply_mono {f g : α →𝒄 β} {x y : α} (h₁ : f ≤ g) (h₂ : x ≤ y) : f x ≤ g y :=
  OrderHom.apply_mono (show (f : α →o β) ≤ g from h₁) h₂
/-
**OmegaCompletePartialOrder.ContinuousHom.** 是 Mathlib 中的一个定理，位于命名空间 `OmegaCompl
etePartialOrder.ContinuousHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ωSup_bind {β γ : Type v} (c : Chain α) (f : α →o Part β) (g : α →o β → Part γ) :
    ωSup (c.map (f.partBind g)) = ωSup (c.map f) >>= ωSup (c.map g) := by
  apply eq_of_forall_ge_iff; intro x
  simp only [ωSup_le_iff, Part.bind_le]
  constructor <;> intro h'''
  · intro b hb
    apply ωSup_le _ _ _
    rintro i y hy
    simp only [Part.mem_ωSup] at hb
    rcases hb with ⟨j, hb⟩
    replace hb := hb.symm
    simp only [Part.eq_some_iff, Chain.coe_map, Function.comp_apply] at hy hb
    replace hb : b ∈ f (c (max i j)) := f.mono (c.mono (le_max_right i j)) _ hb
    replace hy : y ∈ g (c (max i j)) b := g.mono (c.mono (le_max_left i j)) _ _ hy
    apply h''' (max i j)
    simp only [Part.mem_bind_iff, Chain.coe_map,
      Function.comp_apply, OrderHom.partBind_coe]
    exact ⟨_, hb, hy⟩
  · intro i y hy
    simp only [Part.mem_bind_iff, Chain.coe_map,
      Function.comp_apply, OrderHom.partBind_coe] at hy
    rcases hy with ⟨b, hb₀, hb₁⟩
    apply h''' b _
    · apply le_ωSup (c.map g) _ _ _ hb₁
    · apply le_ωSup (c.map f) i _ hb₀

-- TODO: We should move `ωScottContinuous` to the root namespace
/-
**OmegaCompletePartialOrder.ContinuousHom.** 是 Mathlib 中的一个引理，位于命名空间 `OmegaCompl
etePartialOrder.ContinuousHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ωScottContinuous.bind {β γ} {f : α → Part β} {g : α → β → Part γ} (hf : ωScottContinuous f)
    (hg : ωScottContinuous g) : ωScottContinuous fun x ↦ f x >>= g x :=
  ωScottContinuous.of_monotone_map_ωSup
    ⟨hf.monotone.partBind hg.monotone, fun c ↦ by rw [hf.map_ωSup, hg.map_ωSup, ← ωSup_bind]; rfl⟩
/-
**OmegaCompletePartialOrder.ContinuousHom.** 是 Mathlib 中的一个引理，位于命名空间 `OmegaCompl
etePartialOrder.ContinuousHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ωScottContinuous.map {β γ} {f : β → γ} {g : α → Part β} (hg : ωScottContinuous g) :
    ωScottContinuous fun x ↦ f <$> g x := by
  simpa only [map_eq_bind_pure_comp] using! ωScottContinuous.bind hg ωScottContinuous.const
/-
**OmegaCompletePartialOrder.ContinuousHom.** 是 Mathlib 中的一个引理，位于命名空间 `OmegaCompl
etePartialOrder.ContinuousHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ωScottContinuous.seq {β γ} {f : α → Part (β → γ)} {g : α → Part β} (hf : ωScottContinuous f)
    (hg : ωScottContinuous g) : ωScottContinuous fun x ↦ f x <*> g x := by
  simp only [seq_eq_bind_map]
  exact ωScottContinuous.bind hf <| ωScottContinuous.of_apply₂ fun _ ↦ ωScottContinuous.map hg
/-
**OmegaCompletePartialOrder.ContinuousHom.continuous** 是 Mathlib 中的一个定理，位于命名空间 `
OmegaCompletePartialOrder.ContinuousHom`。
形式化陈述：continuous (F : α ->𝒄 β) (C : Chain α) : F (ωSup C) = ωSup (C.map F)
参数：F : α ->𝒄 β；C : Chain α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OmegaCompletePartialOrder.ωScottContinuous.map_ωSup`：∀ {α : Type u_2} {β
 : Type u_3} [inst : OmegaCompletePartialOrder α] [inst_1 : OmegaCompletePartial
Order β] {f : α → β}   (hf : OmegaComplet…
· 使用定理 `OmegaCompletePartialOrder.ContinuousHom.ωScottContinuous`：∀ {α : Type u_
2} {β : Type u_3} [inst : OmegaCompletePartialOrder α] [inst_1 : OmegaCompletePa
rtialOrder β]   (f : α →𝒄 β), OmegaCompletePar…
-/
theorem continuous (F : α →𝒄 β) (C : Chain α) : F (ωSup C) = ωSup (C.map F) :=
  F.ωScottContinuous.map_ωSup _

/-- Construct a continuous function from a bare function, a continuous function, and a proof that
they are equal. -/
@[simps!]
/-
**OmegaCompletePartialOrder.ContinuousHom.copy** 是 Mathlib 中的一个定义，位于命名空间 `OmegaC
ompletePartialOrder.ContinuousHom`。
形式化陈述：copy (f : α -> β) (g : α ->𝒄 β) (h : f = g) : α ->𝒄 β where toOrderHom
参数：f : α -> β；g : α ->𝒄 β；h : f = g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a continuous function from a bare function, a continuous function, and
 a proof that
they are equal.
-/
def copy (f : α → β) (g : α →𝒄 β) (h : f = g) : α →𝒄 β where
  toOrderHom := g.1.copy f h
  map_ωSup' := by rw [OrderHom.copy_eq]; exact g.map_ωSup'

/-- The identity as a continuous function. -/
@[simps!]
/-
**OmegaCompletePartialOrder.ContinuousHom.id** 是 Mathlib 中的一个定义，位于命名空间 `OmegaCom
pletePartialOrder.ContinuousHom`。
形式化陈述：id : α ->𝒄 α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity as a continuous function.
-/
def id : α →𝒄 α := ⟨OrderHom.id, ωScottContinuous.id.map_ωSup⟩

/-- The composition of continuous functions. -/
@[simps!]
/-
**OmegaCompletePartialOrder.ContinuousHom.comp** 是 Mathlib 中的一个定义，位于命名空间 `OmegaC
ompletePartialOrder.ContinuousHom`。
形式化陈述：comp (f : β ->𝒄 γ) (g : α ->𝒄 β) : α ->𝒄 γ
参数：f : β ->𝒄 γ；g : α ->𝒄 β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The composition of continuous functions.
-/
def comp (f : β →𝒄 γ) (g : α →𝒄 β) : α →𝒄 γ :=
  ⟨.comp f.1 g.1, (f.ωScottContinuous.comp g.ωScottContinuous).map_ωSup⟩

@[ext]
/-
**OmegaCompletePartialOrder.ContinuousHom.ext** 是 Mathlib 中的一个定理，位于命名空间 `OmegaCo
mpletePartialOrder.ContinuousHom`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : OmegaCompletePartialOrder α] [inst
_1 : OmegaCompletePartialOrder β]   (f g : α →𝒄 β), (∀ (x : α), f x = g x) → f =
 g
参数：f g : α →𝒄 β；∀ (x : α), f x = g x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
protected theorem ext (f g : α →𝒄 β) (h : ∀ x, f x = g x) : f = g := DFunLike.ext f g h
/-
**OmegaCompletePartialOrder.ContinuousHom.coe_inj** 是 Mathlib 中的一个定理，位于命名空间 `Ome
gaCompletePartialOrder.ContinuousHom`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : OmegaCompletePartialOrder α] [inst
_1 : OmegaCompletePartialOrder β]   (f g : α →𝒄 β), ⇑f = ⇑g → f = g
参数：f g : α →𝒄 β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext'`：ext' {f g : F} (h : (f : forall a : α, β a) = (g : forall
 a : α, β a)) : f = g
-/
protected theorem coe_inj (f g : α →𝒄 β) (h : (f : α → β) = g) : f = g :=
  DFunLike.ext' h

@[simp]
/-
**OmegaCompletePartialOrder.ContinuousHom.comp_id** 是 Mathlib 中的一个定理，位于命名空间 `Ome
gaCompletePartialOrder.ContinuousHom`。
形式化陈述：comp_id (f : β ->𝒄 γ) : f.comp id = f
参数：f : β ->𝒄 γ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_id (f : β →𝒄 γ) : f.comp id = f := rfl

@[simp]
/-
**OmegaCompletePartialOrder.ContinuousHom.id_comp** 是 Mathlib 中的一个定理，位于命名空间 `Ome
gaCompletePartialOrder.ContinuousHom`。
形式化陈述：id_comp (f : β ->𝒄 γ) : id.comp f = f
参数：f : β ->𝒄 γ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_comp (f : β →𝒄 γ) : id.comp f = f := rfl

@[simp]
/-
**OmegaCompletePartialOrder.ContinuousHom.comp_assoc** 是 Mathlib 中的一个定理，位于命名空间 `
OmegaCompletePartialOrder.ContinuousHom`。
形式化陈述：comp_assoc (f : γ ->𝒄 δ) (g : β ->𝒄 γ) (h : α ->𝒄 β) : f.comp (g.comp h) =
 (f.comp g).comp h
参数：f : γ ->𝒄 δ；g : β ->𝒄 γ；h : α ->𝒄 β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_assoc (f : γ →𝒄 δ) (g : β →𝒄 γ) (h : α →𝒄 β) : f.comp (g.comp h) = (f.comp g).comp h :=
  rfl

@[simp]
/-
**OmegaCompletePartialOrder.ContinuousHom.coe_apply** 是 Mathlib 中的一个定理，位于命名空间 `O
megaCompletePartialOrder.ContinuousHom`。
形式化陈述：coe_apply (a : α) (f : α ->𝒄 β) : (f : α ->o β) a = f a
参数：a : α；f : α ->𝒄 β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OmegaCompletePartialOrder.instOrderHomClassContinuousHom`：∀ {α : Type u_
2} {β : Type u_3} [inst : OmegaCompletePartialOrder α] [inst_1 : OmegaCompletePa
rtialOrder β],   OrderHomClass (α →𝒄 β) α β
-/
theorem coe_apply (a : α) (f : α →𝒄 β) : (f : α →o β) a = f a :=
  rfl

/-- `Function.const` is a continuous function. -/
@[simps!]
/-
**OmegaCompletePartialOrder.ContinuousHom.const** 是 Mathlib 中的一个定义，位于命名空间 `Omega
CompletePartialOrder.ContinuousHom`。
形式化陈述：const (x : β) : α ->𝒄 β
参数：x : β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Function.const` is a continuous function.
-/
def const (x : β) : α →𝒄 β := ⟨.const _ x, ωScottContinuous.const.map_ωSup⟩
/-
**OmegaCompletePartialOrder.ContinuousHom.** 是 Mathlib 中的一个实例，位于命名空间 `OmegaCompl
etePartialOrder.ContinuousHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Inhabited β] : Inhabited (α →𝒄 β) :=
  ⟨const default⟩

/-- The map from continuous functions to monotone functions is itself a monotone function. -/
@[simps]
/-
**OmegaCompletePartialOrder.ContinuousHom.toMono** 是 Mathlib 中的一个定义，位于命名空间 `Omeg
aCompletePartialOrder.ContinuousHom`。
形式化陈述：toMono : (α ->𝒄 β) ->o α ->o β where toFun f
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `OmegaCompletePartialOrder.instOrderHomClassContinuousHom`：∀ {α : Type u_
2} {β : Type u_3} [inst : OmegaCompletePartialOrder α] [inst_1 : OmegaCompletePa
rtialOrder β],   OrderHomClass (α →𝒄 β) α β

--- 原说明 ---
The map from continuous functions to monotone functions is itself a monotone fun
ction.
-/
def toMono : (α →𝒄 β) →o α →o β where
  toFun f := f
  monotone' _ _ h := h

/-- When proving that a chain of applications is below a bound `z`, it suffices to consider the
functions and values being selected from the same index in the chains.

This lemma is more specific than necessary, i.e. `c₀` only needs to be a
chain of monotone functions, but it is only used with continuous functions. -/
@[simp]
/-
**OmegaCompletePartialOrder.ContinuousHom.forall_forall_merge** 是 Mathlib 中的一个定理
，位于命名空间 `OmegaCompletePartialOrder.ContinuousHom`。
形式化陈述：forall_forall_merge (c₀ : Chain (α ->𝒄 β)) (c₁ : Chain α) (z : β) : (foral
l i j : Nat, (c₀ i) (c₁ j) <= z) ↔ forall i : Nat, (c₀ i) (c₁ i) <= z
参数：c₀ : Chain (α ->𝒄 β)；c₁ : Chain α；z : β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `OmegaCompletePartialOrder.ContinuousHom.monotone`：∀ {α : Type u_2} {β : 
Type u_3} [inst : OmegaCompletePartialOrder α] [inst_1 : OmegaCompletePartialOrd
er β]   (f : α →𝒄 β), Monotone ⇑f
· 使用定理 `OrderHom.monotone`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [
inst_1 : Preorder β] (f : α →o β), Monotone ⇑f
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b

--- 原说明 ---
When proving that a chain of applications is below a bound `z`, it suffices to c
onsider the
functions and values being selected from the same index in the chains.

This lemma is more specific than necessary, i.e. `c₀` only needs to be a
chain of monotone functions, but it is only used with continuous functions.
-/
theorem forall_forall_merge (c₀ : Chain (α →𝒄 β)) (c₁ : Chain α) (z : β) :
    (∀ i j : ℕ, (c₀ i) (c₁ j) ≤ z) ↔ ∀ i : ℕ, (c₀ i) (c₁ i) ≤ z := by
  constructor <;> introv h
  · apply h
  · apply le_trans _ (h (max i j))
    trans c₀ i (c₁ (max i j))
    · apply (c₀ i).monotone
      apply c₁.monotone
      apply le_max_right
    · apply c₀.monotone
      apply le_max_left

@[simp]
/-
**OmegaCompletePartialOrder.ContinuousHom.forall_forall_merge'** 是 Mathlib 中的一个定
理，位于命名空间 `OmegaCompletePartialOrder.ContinuousHom`。
形式化陈述：forall_forall_merge' (c₀ : Chain (α ->𝒄 β)) (c₁ : Chain α) (z : β) : (fora
ll j i : Nat, (c₀ i) (c₁ j) <= z) ↔ forall i : Nat, (c₀ i) (c₁ i) <= z
参数：c₀ : Chain (α ->𝒄 β)；c₁ : Chain α；z : β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
· 使用定理 `OmegaCompletePartialOrder.ContinuousHom.forall_forall_merge`：forall_fora
ll_merge (c₀ : Chain (α ->𝒄 β)) (c₁ : Chain α) (z : β) : (forall i j : Nat, (c₀ 
i) (c₁ j) <= z) ↔ forall i : Nat, (c₀ i) (c₁ i) <…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem forall_forall_merge' (c₀ : Chain (α →𝒄 β)) (c₁ : Chain α) (z : β) :
    (∀ j i : ℕ, (c₀ i) (c₁ j) ≤ z) ↔ ∀ i : ℕ, (c₀ i) (c₁ i) ≤ z := by
  rw [forall_comm, forall_forall_merge]

/-- The `ωSup` operator for continuous functions, which takes the pointwise countable supremum
of the functions in the `ω`-chain. -/
@[simps!]
/-
**OmegaCompletePartialOrder.ContinuousHom.** 是 Mathlib 中的一个定义，位于命名空间 `OmegaCompl
etePartialOrder.ContinuousHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `ωSup` operator for continuous functions, which takes the pointwise countabl
e supremum
of the functions in the `ω`-chain.
-/
protected def ωSup (c : Chain (α →𝒄 β)) : α →𝒄 β where
  toOrderHom := ωSup <| c.map toMono
  map_ωSup' c' := eq_of_forall_ge_iff fun a ↦ by simp [(c _).ωScottContinuous.map_ωSup]

@[simps ωSup]
/-
**OmegaCompletePartialOrder.ContinuousHom.** 是 Mathlib 中的一个实例，位于命名空间 `OmegaCompl
etePartialOrder.ContinuousHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : OmegaCompletePartialOrder (α →𝒄 β) :=
  OmegaCompletePartialOrder.lift ContinuousHom.toMono ContinuousHom.ωSup
    (fun _ _ h => h) (fun _ => rfl)

set_option backward.defeqAttrib.useBackward true in
@[fun_prop]
/-
**OmegaCompletePartialOrder.ContinuousHom.** 是 Mathlib 中的一个引理，位于命名空间 `OmegaCompl
etePartialOrder.ContinuousHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ωScottContinuous_apply
    {f : α → β →𝒄 γ} (hf : ωScottContinuous f) {g : α → β} (hg : ωScottContinuous g) :
    ωScottContinuous fun x ↦ f x (g x) := by
  apply ωScottContinuous.of_monotone_map_ωSup ⟨?_, fun c ↦ ?_⟩
  · intro x y hxy
    exact OrderHom.apply_mono (hf.monotone hxy) (hg.monotone hxy)
  · rw [hf.map_ωSup, hg.map_ωSup]
    simp only [ωSup_def, ωSup_apply]
    apply le_antisymm
    · apply ωSup_le
      intro i
      dsimp
      rw [(f (c i)).continuous]
      apply ωSup_le
      intro j
      apply le_ωSup_of_le (i ⊔ j)
      apply apply_mono
      · apply hf.monotone (c.monotone le_sup_left)
      · apply hg.monotone (c.monotone le_sup_right)
    · simp only [ωSup_le_iff]
      intro i
      apply le_ωSup_of_le i
      apply (f (c i)).monotone
      apply le_ωSup_of_le i
      rfl

namespace Prod

/-- The application of continuous functions as a continuous function. -/
@[simps!]
/-
**OmegaCompletePartialOrder.ContinuousHom.Prod.apply** 是 Mathlib 中的一个定义，位于命名空间 `
OmegaCompletePartialOrder.ContinuousHom.Prod`。
形式化陈述：apply : (α ->𝒄 β) × α ->𝒄 β
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The application of continuous functions as a continuous function.
-/
def apply : (α →𝒄 β) × α →𝒄 β := ofFun (fun f ↦ f.1 f.2)

end Prod

/-
**OmegaCompletePartialOrder.ContinuousHom.** 是 Mathlib 中的一个定理，位于命名空间 `OmegaCompl
etePartialOrder.ContinuousHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ωSup_apply_ωSup (c₀ : Chain (α →𝒄 β)) (c₁ : Chain α) :
    ωSup c₀ (ωSup c₁) = Prod.apply (ωSup (c₀.zip c₁)) := by simp [Prod.apply_apply, Prod.ωSup_zip]

/-- A family of continuous functions yields a continuous family of functions. -/
@[simps!]
/-
**OmegaCompletePartialOrder.ContinuousHom.flip** 是 Mathlib 中的一个定义，位于命名空间 `OmegaC
ompletePartialOrder.ContinuousHom`。
形式化陈述：flip {α : Type*} (f : α -> β ->𝒄 γ) : β ->𝒄 α -> γ
参数：f : α -> β ->𝒄 γ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A family of continuous functions yields a continuous family of functions.
-/
def flip {α : Type*} (f : α → β →𝒄 γ) : β →𝒄 α → γ :=
  ofFun fun x y ↦ f y x

/-- `Part.bind` as a continuous function. -/
@[simps! apply]
/-
**OmegaCompletePartialOrder.ContinuousHom.bind** 是 Mathlib 中的一个定义，位于命名空间 `OmegaC
ompletePartialOrder.ContinuousHom`。
形式化陈述：bind {β γ : Type v} (f : α ->𝒄 Part β) (g : α ->𝒄 β -> Part γ) : α ->𝒄 Par
t γ
参数：f : α ->𝒄 Part β；g : α ->𝒄 β -> Part γ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Part.bind` as a continuous function.
-/
noncomputable def bind {β γ : Type v} (f : α →𝒄 Part β) (g : α →𝒄 β → Part γ) : α →𝒄 Part γ :=
  .mk (OrderHom.partBind f g.toOrderHom) fun c => by
    rw [ωSup_bind, ← f.continuous, g.toOrderHom_eq_coe, ← g.continuous]
    rfl

/-- `Part.map` as a continuous function. -/
@[simps! apply]
/-
**OmegaCompletePartialOrder.ContinuousHom.map** 是 Mathlib 中的一个定义，位于命名空间 `OmegaCo
mpletePartialOrder.ContinuousHom`。
形式化陈述：map {β γ : Type v} (f : β -> γ) (g : α ->𝒄 Part β) : α ->𝒄 Part γ
参数：f : β -> γ；g : α ->𝒄 Part β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Part.map` as a continuous function.
-/
noncomputable def map {β γ : Type v} (f : β → γ) (g : α →𝒄 Part β) : α →𝒄 Part γ :=
  .copy (fun x => f <$> g x) (bind g (const (pure ∘ f))) <| by
    ext1
    simp only [map_eq_bind_pure_comp, bind, coe_mk, OrderHom.partBind_coe, coe_apply,
      coe_toOrderHom, const_apply, Part.bind_eq_bind]

/-- `Part.seq` as a continuous function. -/
@[simps! apply]
/-
**OmegaCompletePartialOrder.ContinuousHom.seq** 是 Mathlib 中的一个定义，位于命名空间 `OmegaCo
mpletePartialOrder.ContinuousHom`。
形式化陈述：seq {β γ : Type v} (f : α ->𝒄 Part (β -> γ)) (g : α ->𝒄 Part β) : α ->𝒄 Pa
rt γ
参数：f : α ->𝒄 Part (β -> γ)；g : α ->𝒄 Part β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Part.seq` as a continuous function.
-/
noncomputable def seq {β γ : Type v} (f : α →𝒄 Part (β → γ)) (g : α →𝒄 Part β) : α →𝒄 Part γ :=
  .copy (fun x => f x <*> g x) (bind f <| flip <| _root_.flip map g) <| by
      ext
      simp only [seq_eq_bind_map, Part.bind_eq_bind, Part.mem_bind_iff, flip_apply, _root_.flip,
        map_apply, bind_apply, Part.map_eq_map]

end ContinuousHom

namespace fixedPoints

open Function

/-- Iteration of a function on an initial element interpreted as a chain. -/
/-
**OmegaCompletePartialOrder.fixedPoints.iterateChain** 是 Mathlib 中的一个定义，位于命名空间 `
OmegaCompletePartialOrder.fixedPoints`。
形式化陈述：iterateChain (f : α ->o α) (x : α) (h : x <= f x) : Chain α
参数：f : α ->o α；x : α；h : x <= f x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Iteration of a function on an initial element interpreted as a chain.
-/
def iterateChain (f : α →o α) (x : α) (h : x ≤ f x) : Chain α :=
  ⟨fun n => f^[n] x, f.monotone.monotone_iterate_of_le_map h⟩

variable (f : α →𝒄 α) (x : α)

/-- The supremum of iterating a function on x arbitrary often is a fixed point -/
/-
**OmegaCompletePartialOrder.fixedPoints.** 是 Mathlib 中的一个定理，位于命名空间 `OmegaComplet
ePartialOrder.fixedPoints`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The supremum of iterating a function on x arbitrary often is a fixed point
-/
theorem ωSup_iterate_mem_fixedPoint (h : x ≤ f x) :
    ωSup (iterateChain f x h) ∈ fixedPoints f := by
  rw [mem_fixedPoints, IsFixedPt, f.continuous]
  apply le_antisymm
  · apply ωSup_le
    intro n
    simp only [Chain.coe_map, OrderHomClass.coe_coe, comp_apply]
    have : iterateChain f x h (n.succ) = f (iterateChain f x h n) :=
      Function.iterate_succ_apply' ..
    rw [← this]
    apply le_ωSup
  · apply ωSup_le
    rintro (_ | n)
    · apply le_trans h
      change ((iterateChain f x h).map f) 0 ≤ ωSup ((iterateChain f x h).map (f : α →o α))
      apply le_ωSup
    · have : iterateChain f x h (n.succ) = (iterateChain f x h).map f n :=
        Function.iterate_succ_apply' ..
      rw [this]
      apply le_ωSup

/-- The supremum of iterating a function on x arbitrary often is smaller than any prefixed point.

A prefixed point is a value `a` with `f a ≤ a`. -/
/-
**OmegaCompletePartialOrder.fixedPoints.** 是 Mathlib 中的一个定理，位于命名空间 `OmegaComplet
ePartialOrder.fixedPoints`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The supremum of iterating a function on x arbitrary often is smaller than any pr
efixed point.

A prefixed point is a value `a` with `f a ≤ a`.
-/
theorem ωSup_iterate_le_prefixedPoint (h : x ≤ f x) {a : α}
    (h_a : f a ≤ a) (h_x_le_a : x ≤ a) :
    ωSup (iterateChain f x h) ≤ a := by
  apply ωSup_le
  intro n
  induction n with
  | zero => exact h_x_le_a
  | succ n h_ind =>
    have : iterateChain f x h (n.succ) = f (iterateChain f x h n) :=
      Function.iterate_succ_apply' ..
    rw [this]
    exact le_trans (f.monotone h_ind) h_a

/-- The supremum of iterating a function on x arbitrary often is smaller than any fixed point. -/
/-
**OmegaCompletePartialOrder.fixedPoints.** 是 Mathlib 中的一个定理，位于命名空间 `OmegaComplet
ePartialOrder.fixedPoints`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The supremum of iterating a function on x arbitrary often is smaller than any fi
xed point.
-/
theorem ωSup_iterate_le_fixedPoint (h : x ≤ f x) {a : α}
    (h_a : a ∈ fixedPoints f) (h_x_le_a : x ≤ a) :
    ωSup (iterateChain f x h) ≤ a := by
  rw [mem_fixedPoints] at h_a
  obtain h_a := Eq.le h_a
  exact ωSup_iterate_le_prefixedPoint f x h h_a h_x_le_a

end fixedPoints

end OmegaCompletePartialOrder

