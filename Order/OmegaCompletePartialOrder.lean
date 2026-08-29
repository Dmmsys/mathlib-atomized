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

/--
Definition of `Chain` / `Chain` 的定义

English:
structure Chain
  parameters: (α : Type u) [Preorder α]
  extends: Nat ->o α
  (no additional axioms)

中文:
结构 Chain
  参数: (α : 类型u) [Preorder α]
  继承: Nat ->o α
  (无附加公理)
-/
structure Chain (α : Type u) [Preorder α] extends Nat ->o α

namespace Chain
variable [Preorder α] [Preorder β] [Preorder γ]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FunLike (Chain α) Nat α
  body: c.toOrderHom
  coe_injective := by rintro ⟨f, hf⟩; congr!

initialize_simps_projections Chain (toFun -> apply)

中文:
实例 :
  签名: FunLike (Chain α) 自然数 α
  定义体: c.toOrderHom
  coe_injective := by rintro ⟨f, hf⟩; congr!

initialize_simps_projections Chain (toFun -> apply)

Depends on / 依赖: c.toOrderHom, toOrderHom
-/
instance : FunLike (Chain α) Nat α where
  coe c := c.toOrderHom
  coe_injective := by rintro ⟨f, hf⟩; congr!

initialize_simps_projections Chain (toFun -> apply)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: OrderHomClass (Chain α) Nat α
  body: c.monotone hmn

中文:
实例 :
  签名: OrderHomClass (Chain α) 自然数 α
  定义体: c.monotone hmn

Depends on / 依赖: c.monotone, isIntegral_one, monotone
-/
instance : OrderHomClass (Chain α) Nat α where
  map_rel c _m _n hmn := c.monotone hmn

/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  given: ⦃f g
  statement: Chain α⦄ (h : ⇑f = ⇑g) : f = g
  proof: DFunLike.ext' h

中文:
引理 ext
  条件: ⦃f g
  结论: Chain α⦄ (h : ⇑f = ⇑g) : f = g
  证明: DFunLike.ext' h

Depends on / 依赖: isIntegral_zero
-/
@[ext] lemma ext ⦃f g : Chain α⦄ (h : ⇑f = ⇑g) : f = g := DFunLike.ext' h

/--
lemma `coe_toOrderHom` / 引理 `coe_toOrderHom`

English:
lemma coe_toOrderHom
  given: (c : Chain α)
  statement: ⇑c.toOrderHom = c
  proof: rfl

中文:
引理 coe_toOrderHom
  条件: (c : Chain α)
  结论: ⇑c.toOrderHom = c
  证明: rfl

Depends on / 依赖: algebraMap_injective, algebraMap_mk, map_add
-/
@[simp] lemma coe_toOrderHom (c : Chain α) : ⇑c.toOrderHom = c := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Inhabited
  signature: α] : Inhabited (Chain α)
  body: ⟨⟨default, fun _ _ _ => le_rfl⟩⟩

中文:
实例 [Inhabited
  签名: α] : Inhabited (Chain α)
  定义体: ⟨⟨default, fun _ _ _ => le_rfl⟩⟩

Depends on / 依赖: algebraMap_injective, algebraMap_mk, le_rfl, map_mul
-/
instance [Inhabited α] : Inhabited (Chain α) :=
  ⟨⟨default, fun _ _ _ => le_rfl⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Membership α (Chain α)
  body: exists i, a = c i

中文:
实例 :
  签名: Membership α (Chain α)
  定义体: exists i, a = c i

Depends on / 依赖: isIntegral_algebraMap
-/
instance : Membership α (Chain α) where
  mem c a := exists i, a = c i

variable (c c' : Chain α)
variable (f : α ->o β)
variable (g : β ->o γ)

/--
Instance `instLE` / 实例 `instLE`

English:
instance instLE
  signature: : LE (Chain α) where le x y
  body: forall i, exists j, x i <= y j

中文:
实例 instLE
  签名: : LE (Chain α) where le x y
  定义体: forall i, exists j, x i <= y j
-/
instance instLE : LE (Chain α) where le x y := forall i, exists j, x i <= y j

/--
lemma `isChain_range` / 引理 `isChain_range`

English:
lemma isChain_range
  statement: IsChain (· <= ·) (Set.range c)
  proof: Monotone.isChain_range (OrderHomClass.mono c)

中文:
引理 isChain_range
  结论: IsChain (· <= ·) (Set.range c)
  证明: Monotone.isChain_range (OrderHomClass.mono c)

Depends on / 依赖: Monotone, Monotone.isChain_range, OrderHomClass, OrderHomClass.mono, isChain_range
-/
lemma isChain_range : IsChain (· <= ·) (Set.range c) := Monotone.isChain_range (OrderHomClass.mono c)

/--
lemma `directed` / 引理 `directed`

English:
lemma directed
  statement: Directed (· <= ·) c
  proof: directedOn_range.1 c.isChain_range.directedOn

中文:
引理 directed
  结论: Directed (· <= ·) c
  证明: directedOn_range.1 c.isChain_range.directedOn

Depends on / 依赖: c.isChain_range.directedOn, directedOn, directedOn_range, isChain_range
-/
lemma directed : Directed (· <= ·) c := directedOn_range.1 c.isChain_range.directedOn

/-- `map` function for `Chain` -/
@[simps toOrderHom]
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: : Chain β where toOrderHom
  body: f.comp c.toOrderHom

中文:
定义 map
  签名: : Chain β where toOrderHom
  定义体: f.comp c.toOrderHom

Depends on / 依赖: c.toOrderHom, f.comp, toOrderHom
-/
def map : Chain β where toOrderHom := f.comp c.toOrderHom

/--
lemma `coe_map` / 引理 `coe_map`

English:
lemma coe_map
  statement: ⇑(c.map f) = f ∘ c
  proof: rfl

@[deprecated (since := "2026-03-27")] alias map_coe := coe_map

中文:
引理 coe_map
  结论: ⇑(c.map f) = f ∘ c
  证明: rfl

@[deprecated (since := "2026-03-27")] alias map_coe := coe_map
-/
@[simp] lemma coe_map : ⇑(c.map f) = f ∘ c := rfl

@[deprecated (since := "2026-03-27")] alias map_coe := coe_map

variable {f}

/--
theorem `mem_map` / 定理 `mem_map`

English:
theorem mem_map
  given: (x : α)
  statement: x in c -> f x in Chain.map c f
  proof: fun ⟨i, h⟩ => ⟨i, h.symm ▸ rfl⟩

中文:
定理 mem_map
  条件: (x : α)
  结论: x in c -> f x in Chain.map c f
  证明: fun ⟨i, h⟩ => ⟨i, h.symm ▸ rfl⟩

Depends on / 依赖: h.symm
-/
theorem mem_map (x : α) : x in c -> f x in Chain.map c f :=
  fun ⟨i, h⟩ => ⟨i, h.symm ▸ rfl⟩

/--
theorem `exists_of_mem_map` / 定理 `exists_of_mem_map`

English:
theorem exists_of_mem_map
  given: {b : β}
  statement: b in c.map f -> exists a, a in c ∧ f a = b
  proof: fun ⟨i, h⟩ => ⟨c i, ⟨i, rfl⟩, h.symm⟩

@[simp]

中文:
定理 exists_of_mem_map
  条件: {b : β}
  结论: b in c.map f -> 存在 a, a in c ∧ f a = b
  证明: fun ⟨i, h⟩ => ⟨c i, ⟨i, rfl⟩, h.symm⟩

@[simp]

Depends on / 依赖: h.symm
-/
theorem exists_of_mem_map {b : β} : b in c.map f -> exists a, a in c ∧ f a = b :=
  fun ⟨i, h⟩ => ⟨c i, ⟨i, rfl⟩, h.symm⟩

@[simp]
/--
theorem `mem_map_iff` / 定理 `mem_map_iff`

English:
theorem mem_map_iff
  given: {b : β}
  statement: b in c.map f ↔ exists a, a in c ∧ f a = b
  proof: ⟨exists_of_mem_map _, fun h => by
    rcases h with ⟨w, h, h'⟩
    subst b
    apply mem_map c _ h⟩

中文:
定理 mem_map_iff
  条件: {b : β}
  结论: b in c.map f ↔ 存在 a, a in c ∧ f a = b
  证明: ⟨exists_of_mem_map _, fun h => by
    rcases h with ⟨w, h, h'⟩
    subst b
    apply mem_map c _ h⟩

Depends on / 依赖: exists_of_mem_map, mem_map
-/
theorem mem_map_iff {b : β} : b in c.map f ↔ exists a, a in c ∧ f a = b :=
  ⟨exists_of_mem_map _, fun h => by
    rcases h with ⟨w, h, h'⟩
    subst b
    apply mem_map c _ h⟩

/--
lemma `map_id` / 引理 `map_id`

English:
lemma map_id
  statement: c.map OrderHom.id = c
  proof: by ext; simp

中文:
引理 map_id
  结论: c.map OrderHom.id = c
  证明: by ext; simp
-/
@[simp] lemma map_id : c.map OrderHom.id = c := by ext; simp

/--
theorem `map_comp` / 定理 `map_comp`

English:
theorem map_comp
  statement: (c.map f).map g = c.map (g.comp f)
  proof: rfl

@[gcongr, mono]

中文:
定理 map_comp
  结论: (c.map f).map g = c.map (g.comp f)
  证明: rfl

@[gcongr, mono]
-/
theorem map_comp : (c.map f).map g = c.map (g.comp f) :=
  rfl

@[gcongr, mono]
/--
theorem `map_le_map` / 定理 `map_le_map`

English:
theorem map_le_map
  given: {g : α ->o β} (h : f <= g)
  statement: c.map f <= c.map g
  proof: fun _ => ⟨_, h _⟩

中文:
定理 map_le_map
  条件: {g : α ->o β} (h : f <= g)
  结论: c.map f <= c.map g
  证明: fun _ => ⟨_, h _⟩
-/
theorem map_le_map {g : α ->o β} (h : f <= g) : c.map f <= c.map g := fun _ => ⟨_, h _⟩

/-- `OmegaCompletePartialOrder.Chain.zip` pairs up the elements of two chains
that have the same index. -/
@[simps toOrderHom]
/--
Definition of `zip` / `zip` 的定义

English:
definition zip
  signature: (c₀ : Chain α) (c₁ : Chain β)
  body: c₀.toOrderHom.prod c₁.toOrderHom

中文:
定义 zip
  签名: (c₀ : Chain α) (c₁ : Chain β)
  定义体: c₀.toOrderHom.prod c₁.toOrderHom

Depends on / 依赖: toOrderHom, toOrderHom.prod
-/
def zip (c₀ : Chain α) (c₁ : Chain β) : Chain (α × β) where
  toOrderHom := c₀.toOrderHom.prod c₁.toOrderHom

/--
lemma `zip_apply` / 引理 `zip_apply`

English:
lemma zip_apply
  given: (c₀ : Chain α) (c₁ : Chain β) (n : Nat)
  statement: c₀.zip c₁ n = (c₀ n, c₁ n)
  proof: rfl

@[deprecated (since := "2026-03-27")] alias zip_coe := zip_apply

中文:
引理 zip_apply
  条件: (c₀ : Chain α) (c₁ : Chain β) (n : 自然数)
  结论: c₀.zip c₁ n = (c₀ n, c₁ n)
  证明: rfl

@[deprecated (since := "2026-03-27")] alias zip_coe := zip_apply
-/
@[simp] lemma zip_apply (c₀ : Chain α) (c₁ : Chain β) (n : Nat) : c₀.zip c₁ n = (c₀ n, c₁ n) := rfl

@[deprecated (since := "2026-03-27")] alias zip_coe := zip_apply

/--
Definition of `pair` / `pair` 的定义

English:
definition pair
  signature: (a b : α) (hab : a <= b)
  body: by aesop

中文:
定义 pair
  签名: (a b : α) (hab : a <= b)
  定义体: by aesop
-/
def pair (a b : α) (hab : a <= b) : Chain α where
  toFun
    | 0 => a
    | _ => b
  monotone' _ _ _ := by aesop

/--
lemma `pair_zero` / 引理 `pair_zero`

English:
lemma pair_zero
  given: (a b : α) (hab)
  statement: pair a b hab 0 = a
  proof: rfl

中文:
引理 pair_zero
  条件: (a b : α) (hab)
  结论: pair a b hab 0 = a
  证明: rfl
-/
@[simp] lemma pair_zero (a b : α) (hab) : pair a b hab 0 = a := rfl
/--
lemma `pair_succ` / 引理 `pair_succ`

English:
lemma pair_succ
  given: (a b : α) (hab) (n : Nat)
  statement: pair a b hab (n + 1) = b
  proof: rfl

中文:
引理 pair_succ
  条件: (a b : α) (hab) (n : 自然数)
  结论: pair a b hab (n + 1) = b
  证明: rfl
-/
@[simp] lemma pair_succ (a b : α) (hab) (n : Nat) : pair a b hab (n + 1) = b := rfl

/--
lemma `range_pair` / 引理 `range_pair`

English:
lemma range_pair
  given: (a b : α) (hab)
  statement: Set.range (pair a b hab) = {a, b}
  proof: by
  ext; exact Nat.or_exists_add_one.symm.trans (by aesop)

中文:
引理 range_pair
  条件: (a b : α) (hab)
  结论: Set.range (pair a b hab) = {a, b}
  证明: by
  ext; exact Nat.or_exists_add_one.symm.trans (by aesop)

Depends on / 依赖: Algebra, Algebra.IsIntegral.trans, IsIntegral
-/
@[simp] lemma range_pair (a b : α) (hab) : Set.range (pair a b hab) = {a, b} := by
  ext; exact Nat.or_exists_add_one.symm.trans (by aesop)

/--
lemma `pair_zip_pair` / 引理 `pair_zip_pair`

English:
lemma pair_zip_pair
  given: (a₁ a₂ : α) (b₁ b₂ : β) (ha hb)
  proof: by
  ext n : 2; cases n <;> rfl

中文:
引理 pair_zip_pair
  条件: (a₁ a₂ : α) (b₁ b₂ : β) (ha hb)
  证明: by
  ext n : 2; cases n <;> rfl
-/
@[simp] lemma pair_zip_pair (a₁ a₂ : α) (b₁ b₂ : β) (ha hb) :
    (pair a₁ a₂ ha).zip (pair b₁ b₂ hb) = pair (a₁, b₁) (a₂, b₂) (Prod.le_def.2 ⟨ha, hb⟩) := by
  ext n : 2; cases n <;> rfl

end Chain

end OmegaCompletePartialOrder

open OmegaCompletePartialOrder Chain

/--
Definition of `OmegaCompletePartialOrder` / `OmegaCompletePartialOrder` 的定义

English:
class OmegaCompletePartialOrder
  parameters: (α : Type*)
  extends: PartialOrder α
  axioms and operations (3):
    - ωSup : Chain α -> α
    - le_ωSup : forall c : Chain α, forall i, c i <= ωSup c
    - ωSup_le : forall (c : Chain α) (x), (forall i, c i <= x) -> ωSup c <= x

中文:
类 OmegaCompletePartialOrder
  参数: (α : 类型)
  继承: PartialOrder α
  公理与运算 (3 个):
    - ωSup : Chain α -> α
    - le_ωSup : 对任意 c : Chain α, 对任意 i, c i <= ωSup c
    - ωSup_le : 对任意 (c : Chain α) (x), (对任意 i, c i <= x) -> ωSup c <= x
-/
class OmegaCompletePartialOrder (α : Type*) extends PartialOrder α where
  /-- The supremum of an increasing sequence -/
  ωSup : Chain α -> α
  /-- `ωSup` is an upper bound of the increasing sequence -/
  le_ωSup : forall c : Chain α, forall i, c i <= ωSup c
  /-- `ωSup` is a lower bound of the set of upper bounds of the increasing sequence -/
  ωSup_le : forall (c : Chain α) (x), (forall i, c i <= x) -> ωSup c <= x

namespace OmegaCompletePartialOrder
variable [OmegaCompletePartialOrder α]

/--
Definition of `lift` / `lift` 的定义

English:
abbreviation lift
  signature: [PartialOrder β] (f : β ->o α) (ωSup₀ : Chain β -> β)
  body: ωSup₀
  ωSup_le c x hx := h _ _ (by rw [h']; apply ωSup_le; intro i; apply f.monotone (hx i))
  le_ωSup c i := h _ _ (by rw [h']; apply le_ωSup (c.map f))

中文:
缩写 lift
  签名: [PartialOrder β] (f : β ->o α) (ωSup₀ : Chain β -> β)
  定义体: ωSup₀
  ωSup_le c x hx := h _ _ (by rw [h']; apply ωSup_le; intro i; apply f.monotone (hx i))
  le_ωSup c i := h _ _ (by rw [h']; apply le_ωSup (c.map f))
-/
protected abbrev lift [PartialOrder β] (f : β ->o α) (ωSup₀ : Chain β -> β)
    (h : forall x y, f x <= f y -> x <= y) (h' : forall c, f (ωSup₀ c) = ωSup (c.map f)) :
    OmegaCompletePartialOrder β where
  ωSup := ωSup₀
  ωSup_le c x hx := h _ _ (by rw [h']; apply ωSup_le; intro i; apply f.monotone (hx i))
  le_ωSup c i := h _ _ (by rw [h']; apply le_ωSup (c.map f))

/--
theorem `le_ωSup_of_le` / 定理 `le_ωSup_of_le`

English:
theorem le_ωSup_of_le
  given: {c : Chain α} {x : α} (i : Nat) (h : x <= c i)
  statement: x <= ωSup c
  proof: le_trans h (le_ωSup c _)

中文:
定理 le_ωSup_of_le
  条件: {c : Chain α} {x : α} (i : 自然数) (h : x <= c i)
  结论: x <= ωSup c
  证明: le_trans h (le_ωSup c _)

Depends on / 依赖: le_trans
-/
theorem le_ωSup_of_le {c : Chain α} {x : α} (i : Nat) (h : x <= c i) : x <= ωSup c :=
  le_trans h (le_ωSup c _)

/--
theorem `ωSup_total` / 定理 `ωSup_total`

English:
theorem ωSup_total
  given: {c : Chain α} {x : α} (h : forall i, c i <= x ∨ x <= c i)
  statement: ωSup c <= x ∨ x <= ωSup c
  proof: by_cases
    (fun (this : forall i, c i <= x) => Or.inl (ωSup_le _ _ this))
    (fun (this : ¬forall i, c i <= x) =>
      have : exists i, ¬c i <= x := by simp only [not_forall] at this ⊢; assumption
      let ⟨i, hx⟩ := this
      have : x <= c i := (h i).resolve_left hx
Or.inr le_ωSup_of_le _ thi

中文:
定理 ωSup_total
  条件: {c : Chain α} {x : α} (h : 对任意 i, c i <= x ∨ x <= c i)
  结论: ωSup c <= x ∨ x <= ωSup c
  证明: by_cases
    (fun (this : forall i, c i <= x) => Or.inl (ωSup_le _ _ this))
    (fun (this : ¬forall i, c i <= x) =>
      have : exists i, ¬c i <= x := by simp only [not_forall] at this ⊢; assumption
      let ⟨i, hx⟩ := this
      have : x <= c i := (h i).resolve_left hx
Or.inr le_ωSup_of_le _ thi

Depends on / 依赖: Or.inl, Or.inr, not_forall, resolve_left
-/
theorem ωSup_total {c : Chain α} {x : α} (h : forall i, c i <= x ∨ x <= c i) : ωSup c <= x ∨ x <= ωSup c :=
  by_cases
    (fun (this : forall i, c i <= x) => Or.inl (ωSup_le _ _ this))
    (fun (this : ¬forall i, c i <= x) =>
      have : exists i, ¬c i <= x := by simp only [not_forall] at this ⊢; assumption
      let ⟨i, hx⟩ := this
      have : x <= c i := (h i).resolve_left hx
Or.inr le_ωSup_of_le _ this)

@[gcongr, mono]
/--
theorem `ωSup_le_ωSup_of_le` / 定理 `ωSup_le_ωSup_of_le`

English:
theorem ωSup_le_ωSup_of_le
  given: {c₀ c₁ : Chain α} (h : c₀ <= c₁)
  statement: ωSup c₀ <= ωSup c₁
  proof: (ωSup_le _ _) fun i => by
    obtain ⟨_, h⟩ := h i
    exact le_trans h (le_ωSup _ _)

中文:
定理 ωSup_le_ωSup_of_le
  条件: {c₀ c₁ : Chain α} (h : c₀ <= c₁)
  结论: ωSup c₀ <= ωSup c₁
  证明: (ωSup_le _ _) fun i => by
    obtain ⟨_, h⟩ := h i
    exact le_trans h (le_ωSup _ _)

Depends on / 依赖: le_trans
-/
theorem ωSup_le_ωSup_of_le {c₀ c₁ : Chain α} (h : c₀ <= c₁) : ωSup c₀ <= ωSup c₁ :=
  (ωSup_le _ _) fun i => by
    obtain ⟨_, h⟩ := h i
    exact le_trans h (le_ωSup _ _)

/--
theorem `ωSup_le_iff` / 定理 `ωSup_le_iff`

English:
theorem ωSup_le_iff
  given: {c : Chain α} {x : α}
  statement: ωSup c <= x ↔ forall i, c i <= x
  proof: by
  constructor <;> intros
  · trans ωSup c
    · exact le_ωSup _ _
    · assumption
  exact ωSup_le _ _ ‹_›

中文:
定理 ωSup_le_iff
  条件: {c : Chain α} {x : α}
  结论: ωSup c <= x ↔ 对任意 i, c i <= x
  证明: by
  constructor <;> intros
  · trans ωSup c
    · exact le_ωSup _ _
    · assumption
  exact ωSup_le _ _ ‹_›
-/
@[simp] theorem ωSup_le_iff {c : Chain α} {x : α} : ωSup c <= x ↔ forall i, c i <= x := by
  constructor <;> intros
  · trans ωSup c
    · exact le_ωSup _ _
    · assumption
  exact ωSup_le _ _ ‹_›

/--
lemma `isLUB_range_ωSup` / 引理 `isLUB_range_ωSup`

English:
lemma isLUB_range_ωSup
  given: (c : Chain α)
  statement: IsLUB (Set.range c) (ωSup c)
  proof: by
  constructor
  · simp only [upperBounds, Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff,
      Set.mem_ofPred_eq]
    exact fun a => le_ωSup c a
  · simp only [lowerBounds, upperBounds, Set.mem_range, forall_exists_index,
      forall_apply_eq_imp_iff, Set.mem_ofPred_eq]
    exact f

中文:
引理 isLUB_range_ωSup
  条件: (c : Chain α)
  结论: IsLUB (Set.range c) (ωSup c)
  证明: by
  constructor
  · simp only [upperBounds, Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff,
      Set.mem_ofPred_eq]
    exact fun a => le_ωSup c a
  · simp only [lowerBounds, upperBounds, Set.mem_range, forall_exists_index,
      forall_apply_eq_imp_iff, Set.mem_ofPred_eq]
    exact f

Depends on / 依赖: Set.mem_ofPred_eq, Set.mem_range, forall_apply_eq_imp_iff, forall_exists_index, lowerBounds, mem_ofPred_eq, mem_range, upperBounds
-/
lemma isLUB_range_ωSup (c : Chain α) : IsLUB (Set.range c) (ωSup c) := by
  constructor
  · simp only [upperBounds, Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff,
      Set.mem_ofPred_eq]
    exact fun a => le_ωSup c a
  · simp only [lowerBounds, upperBounds, Set.mem_range, forall_exists_index,
      forall_apply_eq_imp_iff, Set.mem_ofPred_eq]
    exact fun ⦃a⦄ a_1 => ωSup_le c a a_1

/--
lemma `ωSup_eq_of_isLUB` / 引理 `ωSup_eq_of_isLUB`

English:
lemma ωSup_eq_of_isLUB
  given: {c : Chain α} {a : α} (h : IsLUB (Set.range c) a)
  statement: a = ωSup c
  proof: by
  rw [le_antisymm_iff]
  simp only [IsLUB, IsLeast, upperBounds, lowerBounds, Set.mem_range, forall_exists_index,
    forall_apply_eq_imp_iff, Set.mem_ofPred_eq] at h
  constructor
  · apply h.2
    exact fun a => le_ωSup c a
  · rw [ωSup_le_iff]
    apply h.1

中文:
引理 ωSup_eq_of_isLUB
  条件: {c : Chain α} {a : α} (h : IsLUB (Set.range c) a)
  结论: a = ωSup c
  证明: by
  rw [le_antisymm_iff]
  simp only [IsLUB, IsLeast, upperBounds, lowerBounds, Set.mem_range, forall_exists_index,
    forall_apply_eq_imp_iff, Set.mem_ofPred_eq] at h
  constructor
  · apply h.2
    exact fun a => le_ωSup c a
  · rw [ωSup_le_iff]
    apply h.1

Depends on / 依赖: IsLeast, Set.mem_ofPred_eq, Set.mem_range, forall_apply_eq_imp_iff, forall_exists_index, le_antisymm_iff, lowerBounds, mem_ofPred_eq, mem_range, upperBounds
-/
lemma ωSup_eq_of_isLUB {c : Chain α} {a : α} (h : IsLUB (Set.range c) a) : a = ωSup c := by
  rw [le_antisymm_iff]
  simp only [IsLUB, IsLeast, upperBounds, lowerBounds, Set.mem_range, forall_exists_index,
    forall_apply_eq_imp_iff, Set.mem_ofPred_eq] at h
  constructor
  · apply h.2
    exact fun a => le_ωSup c a
  · rw [ωSup_le_iff]
    apply h.1

/-- A subset `p : α → Prop` of the type closed under `ωSup` induces an
`OmegaCompletePartialOrder` on the subtype `{a : α // p a}`. -/
@[instance_reducible]
/--
Definition of `subtype` / `subtype` 的定义

English:
definition subtype
  signature: {α : Type*} [OmegaCompletePartialOrder α] (p : α -> Prop)
  body: OmegaCompletePartialOrder.lift (OrderHom.Subtype.val p)
    (fun c => ⟨ωSup _, hp (c.map (OrderHom.Subtype.val p)) fun _ ⟨n, q⟩ => q.symm ▸ (c n).2⟩)
    (fun _ _ h => h) (fun _ => rfl)

中文:
定义 subtype
  签名: {α : 类型} [OmegaCompletePartialOrder α] (p : α -> 命题)
  定义体: OmegaCompletePartialOrder.lift (OrderHom.Subtype.val p)
    (fun c => ⟨ωSup _, hp (c.map (OrderHom.Subtype.val p)) fun _ ⟨n, q⟩ => q.symm ▸ (c n).2⟩)
    (fun _ _ h => h) (fun _ => rfl)

Depends on / 依赖: OmegaCompletePartialOrder, OmegaCompletePartialOrder.lift, OrderHom, OrderHom.Subtype.val, Subtype, c.map, q.symm
-/
def subtype {α : Type*} [OmegaCompletePartialOrder α] (p : α -> Prop)
    (hp : forall c : Chain α, (forall i in c, p i) -> p (ωSup c)) : OmegaCompletePartialOrder (Subtype p) :=
  OmegaCompletePartialOrder.lift (OrderHom.Subtype.val p)
    (fun c => ⟨ωSup _, hp (c.map (OrderHom.Subtype.val p)) fun _ ⟨n, q⟩ => q.symm ▸ (c n).2⟩)
    (fun _ _ h => h) (fun _ => rfl)

section Continuity

variable [OmegaCompletePartialOrder β]
variable [OmegaCompletePartialOrder γ]
variable {f : α -> β} {g : β -> γ}

/-- A function `f` between `ω`-complete partial orders is `ωScottContinuous` if it is
Scott continuous over chains. -/
@[fun_prop]
/--
Definition of `ωScottContinuous` / `ωScottContinuous` 的定义

English:
definition ωScottContinuous
  signature: (f : α -> β)
  body: ScottContinuousOn (Set.range fun c : Chain α => Set.range c) f

中文:
定义 ωScottContinuous
  签名: (f : α -> β)
  定义体: ScottContinuousOn (Set.range fun c : Chain α => Set.range c) f

Depends on / 依赖: ScottContinuousOn, Set.range
-/
def ωScottContinuous (f : α -> β) : Prop :=
    ScottContinuousOn (Set.range fun c : Chain α => Set.range c) f

/--
lemma `_root_.ScottContinuous.ωScottContinuous` / 引理 `_root_.ScottContinuous.ωScottContinuous`

English:
lemma _root_.ScottContinuous.ωScottContinuous
  given: (hf : ScottContinuous f)
  statement: ωScottContinuous f
  proof: hf.scottContinuousOn

中文:
引理 _root_.ScottContinuous.ωScottContinuous
  条件: (hf : ScottContinuous f)
  结论: ωScottContinuous f
  证明: hf.scottContinuousOn

Depends on / 依赖: hf.scottContinuousOn, scottContinuousOn
-/
lemma _root_.ScottContinuous.ωScottContinuous (hf : ScottContinuous f) : ωScottContinuous f :=
  hf.scottContinuousOn

/--
lemma `ωScottContinuous.monotone` / 引理 `ωScottContinuous.monotone`

English:
lemma ωScottContinuous.monotone
  given: (h : ωScottContinuous f)
  statement: Monotone f
  proof: ScottContinuousOn.monotone _ (fun a b hab => by
    use pair a b hab; exact range_pair a b hab) h

中文:
引理 ωScottContinuous.monotone
  条件: (h : ωScottContinuous f)
  结论: Monotone f
  证明: ScottContinuousOn.monotone _ (fun a b hab => by
    use pair a b hab; exact range_pair a b hab) h

Depends on / 依赖: H.Normal, Normal, Quotient, Quotient.ind, Quotient.lift, ScottContinuousOn, ScottContinuousOn.monotone, Subtype, Subtype.ext, conj_mem, monotone, mul_smul, one_smul, range_pair, smul_add, smul_one, smul_zero
-/
lemma ωScottContinuous.monotone (h : ωScottContinuous f) : Monotone f :=
  ScottContinuousOn.monotone _ (fun a b hab => by
    use pair a b hab; exact range_pair a b hab) h

/--
lemma `ωScottContinuous.isLUB` / 引理 `ωScottContinuous.isLUB`

English:
lemma ωScottContinuous.isLUB
  given: {c : Chain α} (hf : ωScottContinuous f)
  proof: by
  simpa [Set.range_comp]
    using hf (by simp) (Set.range_nonempty _) (isChain_range c).directedOn (isLUB_range_ωSup c)

@[fun_prop, to_fun (attr := simp)]

中文:
引理 ωScottContinuous.isLUB
  条件: {c : Chain α} (hf : ωScottContinuous f)
  证明: by
  simpa [Set.range_comp]
    using hf (by simp) (Set.range_nonempty _) (isChain_range c).directedOn (isLUB_range_ωSup c)

@[fun_prop, to_fun (attr := simp)]

Depends on / 依赖: FixedPoints, FixedPoints.subring, MulSemiringAction, Set.range_comp, Set.range_nonempty, directedOn, isChain_range, range_comp, range_nonempty, subring
-/
lemma ωScottContinuous.isLUB {c : Chain α} (hf : ωScottContinuous f) :
    IsLUB (Set.range (c.map ⟨f, hf.monotone⟩)) (f (ωSup c)) := by
  simpa [Set.range_comp]
    using hf (by simp) (Set.range_nonempty _) (isChain_range c).directedOn (isLUB_range_ωSup c)

@[fun_prop, to_fun (attr := simp)]
/--
lemma `ωScottContinuous.id` / 引理 `ωScottContinuous.id`

English:
lemma ωScottContinuous.id
  statement: ωScottContinuous (id : α -> α)
  proof: ScottContinuousOn.id

中文:
引理 ωScottContinuous.id
  结论: ωScottContinuous (id : α -> α)
  证明: ScottContinuousOn.id

Depends on / 依赖: Quotient, Quotient.ind, ScottContinuousOn, ScottContinuousOn.id, Subtype, Subtype.ext, smul_comm
-/
lemma ωScottContinuous.id : ωScottContinuous (id : α -> α) := ScottContinuousOn.id

/--
lemma `ωScottContinuous.map_ωSup` / 引理 `ωScottContinuous.map_ωSup`

English:
lemma ωScottContinuous.map_ωSup
  given: (hf : ωScottContinuous f) (c : Chain α)
  proof: ωSup_eq_of_isLUB hf.isLUB

中文:
引理 ωScottContinuous.map_ωSup
  条件: (hf : ωScottContinuous f) (c : Chain α)
  证明: ωSup_eq_of_isLUB hf.isLUB

Depends on / 依赖: Algebra, Algebra.IsInvariant.isInvariant, IsInvariant, Subtype, Subtype.ext, Subtype.val, congr_arg, hf.isLUB, isInvariant
-/
lemma ωScottContinuous.map_ωSup (hf : ωScottContinuous f) (c : Chain α) :
    f (ωSup c) = ωSup (c.map ⟨f, hf.monotone⟩) := ωSup_eq_of_isLUB hf.isLUB

/--
lemma `ωScottContinuous_iff_monotone_map_ωSup` / 引理 `ωScottContinuous_iff_monotone_map_ωSup`

English:
lemma ωScottContinuous_iff_monotone_map_ωSup
  proof: by
  refine ⟨fun hf => ⟨hf.monotone, hf.map_ωSup⟩, ?_⟩
  intro hf _ ⟨c, hc⟩ _ _ _ hda
  convert! isLUB_range_ωSup (c.map { toFun := f, monotone' := hf.1 })
  · simp [← hc, ← (Set.range_comp f ⇑c)]
  · rw [← hc] at hda
    rw [← hf.2 c]; rw [ωSup_eq_of_isLUB hda]

alias ⟨ωScottContinuous.monotone_map

中文:
引理 ωScottContinuous_iff_monotone_map_ωSup
  证明: by
  refine ⟨fun hf => ⟨hf.monotone, hf.map_ωSup⟩, ?_⟩
  intro hf _ ⟨c, hc⟩ _ _ _ hda
  convert! isLUB_range_ωSup (c.map { toFun := f, monotone' := hf.1 })
  · simp [← hc, ← (Set.range_comp f ⇑c)]
  · rw [← hc] at hda
    rw [← hf.2 c]; rw [ωSup_eq_of_isLUB hda]

alias ⟨ωScottContinuous.monotone_map

Depends on / 依赖: Set.range_comp, c.map, convert, hf.map_, hf.monotone, monotone, range_comp
-/
lemma ωScottContinuous_iff_monotone_map_ωSup :
    ωScottContinuous f ↔ exists hf : Monotone f, forall c : Chain α, f (ωSup c) = ωSup (c.map ⟨f, hf⟩) := by
  refine ⟨fun hf => ⟨hf.monotone, hf.map_ωSup⟩, ?_⟩
  intro hf _ ⟨c, hc⟩ _ _ _ hda
  convert! isLUB_range_ωSup (c.map { toFun := f, monotone' := hf.1 })
  · simp [← hc, ← (Set.range_comp f ⇑c)]
  · rw [← hc] at hda
    rw [← hf.2 c]; rw [ωSup_eq_of_isLUB hda]

alias ⟨ωScottContinuous.monotone_map_ωSup, ωScottContinuous.of_monotone_map_ωSup⟩ :=
  ωScottContinuous_iff_monotone_map_ωSup

/--
lemma `ωScottContinuous_iff_map_ωSup_of_orderHom` / 引理 `ωScottContinuous_iff_map_ωSup_of_orderHom`

English:
lemma ωScottContinuous_iff_map_ωSup_of_orderHom
  given: {f : α ->o β}
  proof: by
  rw [ωScottContinuous_iff_monotone_map_ωSup]
  exact exists_prop_of_true f.monotone'

alias ⟨ωScottContinuous.map_ωSup_of_orderHom, ωScottContinuous.of_map_ωSup_of_orderHom⟩ :=
  ωScottContinuous_iff_map_ωSup_of_orderHom

中文:
引理 ωScottContinuous_iff_map_ωSup_of_orderHom
  条件: {f : α ->o β}
  证明: by
  rw [ωScottContinuous_iff_monotone_map_ωSup]
  exact exists_prop_of_true f.monotone'

alias ⟨ωScottContinuous.map_ωSup_of_orderHom, ωScottContinuous.of_map_ωSup_of_orderHom⟩ :=
  ωScottContinuous_iff_map_ωSup_of_orderHom

Depends on / 依赖: exists_prop_of_true, f.monotone, monotone
-/
lemma ωScottContinuous_iff_map_ωSup_of_orderHom {f : α ->o β} :
    ωScottContinuous f ↔ forall c : Chain α, f (ωSup c) = ωSup (c.map f) := by
  rw [ωScottContinuous_iff_monotone_map_ωSup]
  exact exists_prop_of_true f.monotone'

alias ⟨ωScottContinuous.map_ωSup_of_orderHom, ωScottContinuous.of_map_ωSup_of_orderHom⟩ :=
  ωScottContinuous_iff_map_ωSup_of_orderHom

-- Allow `to_fun` to eta-expand `g ∘ f`. Ideally, `Function.comp_def` would be a global pull lemma
-- instead, which is not supported yet: see https://github.com/leanprover-community/mathlib4/issues/40183.
attribute [local push ←] Function.comp_def
attribute [local push] Function.const_def

@[fun_prop, to_fun]
/--
lemma `ωScottContinuous.comp` / 引理 `ωScottContinuous.comp`

English:
lemma ωScottContinuous.comp
  given: (hg : ωScottContinuous g) (hf : ωScottContinuous f)
  proof: ωScottContinuous.of_monotone_map_ωSup
    ⟨hg.monotone.comp hf.monotone, by simp [hf.map_ωSup, hg.map_ωSup, map_comp]⟩

@[fun_prop, to_fun (attr := simp)]

中文:
引理 ωScottContinuous.comp
  条件: (hg : ωScottContinuous g) (hf : ωScottContinuous f)
  证明: ωScottContinuous.of_monotone_map_ωSup
    ⟨hg.monotone.comp hf.monotone, by simp [hf.map_ωSup, hg.map_ωSup, map_comp]⟩

@[fun_prop, to_fun (attr := simp)]

Depends on / 依赖: ScottContinuous.of_monotone_map_, hf.map_, hf.monotone, hg.map_, hg.monotone.comp, map_comp, monotone
-/
lemma ωScottContinuous.comp (hg : ωScottContinuous g) (hf : ωScottContinuous f) :
    ωScottContinuous (g.comp f) :=
  ωScottContinuous.of_monotone_map_ωSup
    ⟨hg.monotone.comp hf.monotone, by simp [hf.map_ωSup, hg.map_ωSup, map_comp]⟩

@[fun_prop, to_fun (attr := simp)]
/--
lemma `ωScottContinuous.const` / 引理 `ωScottContinuous.const`

English:
lemma ωScottContinuous.const
  given: {x : β}
  statement: ωScottContinuous (Function.const α x)
  proof: ScottContinuousOn.const x

中文:
引理 ωScottContinuous.const
  条件: {x : β}
  结论: ωScottContinuous (Function.const α x)
  证明: ScottContinuousOn.const x

Depends on / 依赖: ScottContinuousOn, ScottContinuousOn.const
-/
lemma ωScottContinuous.const {x : β} : ωScottContinuous (Function.const α x) :=
  ScottContinuousOn.const x

end Continuity

end OmegaCompletePartialOrder

namespace Part

/--
theorem `eq_of_chain` / 定理 `eq_of_chain`

English:
theorem eq_of_chain
  given: {c : Chain (Part α)} {a b : α} (ha : some a in c) (hb : some b in c)
  statement: a = b
  proof: by
  obtain ⟨i, ha⟩ := ha; replace ha := ha.symm
  obtain ⟨j, hb⟩ := hb; replace hb := hb.symm
  rw [eq_some_iff] at ha hb
  rcases le_total i j with hij | hji
  · have := c.monotone hij _ ha; apply mem_unique this hb
  · have := c.monotone hji _ hb; apply Eq.symm; apply mem_unique this ha

中文:
定理 eq_of_chain
  条件: {c : Chain (Part α)} {a b : α} (ha : some a in c) (hb : some b in c)
  结论: a = b
  证明: by
  obtain ⟨i, ha⟩ := ha; replace ha := ha.symm
  obtain ⟨j, hb⟩ := hb; replace hb := hb.symm
  rw [eq_some_iff] at ha hb
  rcases le_total i j with hij | hji
  · have := c.monotone hij _ ha; apply mem_unique this hb
  · have := c.monotone hji _ hb; apply Eq.symm; apply mem_unique this ha

Depends on / 依赖: Eq.symm, c.monotone, eq_some_iff, ha.symm, hb.symm, le_total, mem_unique, monotone, replace
-/
theorem eq_of_chain {c : Chain (Part α)} {a b : α} (ha : some a in c) (hb : some b in c) : a = b := by
  obtain ⟨i, ha⟩ := ha; replace ha := ha.symm
  obtain ⟨j, hb⟩ := hb; replace hb := hb.symm
  rw [eq_some_iff] at ha hb
  rcases le_total i j with hij | hji
  · have := c.monotone hij _ ha; apply mem_unique this hb
  · have := c.monotone hji _ hb; apply Eq.symm; apply mem_unique this ha

open scoped Classical in
/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def ωSup (c : Chain (Part α))
  body: if h : exists a, some a in c then some (Classical.choose h) else none

中文:
定义 noncomputable
  签名: def ωSup (c : Chain (Part α))
  定义体: if h : exists a, some a in c then some (Classical.choose h) else none
-/
protected noncomputable def ωSup (c : Chain (Part α)) : Part α :=
  if h : exists a, some a in c then some (Classical.choose h) else none

/--
theorem `ωSup_eq_some` / 定理 `ωSup_eq_some`

English:
theorem ωSup_eq_some
  given: {c : Chain (Part α)} {a : α} (h : some a in c)
  statement: Part.ωSup c = some a
  proof: have : exists a, some a in c := ⟨a, h⟩
  have a' : some (Classical.choose this) in c := Classical.choose_spec this
  calc
    Part.ωSup c = some (Classical.choose this) := dif_pos this
    _ = some a := congr_arg _ (eq_of_chain a' h)

中文:
定理 ωSup_eq_some
  条件: {c : Chain (Part α)} {a : α} (h : some a in c)
  结论: Part.ωSup c = some a
  证明: have : exists a, some a in c := ⟨a, h⟩
  have a' : some (Classical.choose this) in c := Classical.choose_spec this
  calc
    Part.ωSup c = some (Classical.choose this) := dif_pos this
    _ = some a := congr_arg _ (eq_of_chain a' h)

Depends on / 依赖: Classical, Classical.choose, Classical.choose_spec, choose_spec, congr_arg, dif_pos, eq_of_chain
-/
theorem ωSup_eq_some {c : Chain (Part α)} {a : α} (h : some a in c) : Part.ωSup c = some a :=
  have : exists a, some a in c := ⟨a, h⟩
  have a' : some (Classical.choose this) in c := Classical.choose_spec this
  calc
    Part.ωSup c = some (Classical.choose this) := dif_pos this
    _ = some a := congr_arg _ (eq_of_chain a' h)

/--
theorem `ωSup_eq_none` / 定理 `ωSup_eq_none`

English:
theorem ωSup_eq_none
  given: {c : Chain (Part α)} (h : ¬exists a, some a in c)
  statement: Part.ωSup c = none
  proof: dif_neg h

中文:
定理 ωSup_eq_none
  条件: {c : Chain (Part α)} (h : ¬存在 a, some a in c)
  结论: Part.ωSup c = none
  证明: dif_neg h

Depends on / 依赖: dif_neg
-/
theorem ωSup_eq_none {c : Chain (Part α)} (h : ¬exists a, some a in c) : Part.ωSup c = none :=
  dif_neg h

/--
theorem `mem_chain_of_mem_ωSup` / 定理 `mem_chain_of_mem_ωSup`

English:
theorem mem_chain_of_mem_ωSup
  given: {c : Chain (Part α)} {a : α} (h : a in Part.ωSup c)
  statement: some a in c
  proof: by
  simp only [Part.ωSup] at h; split_ifs at h with h_1
  · have h' := Classical.choose_spec h_1
    rw [← eq_some_iff] at h
    rw [← h]
    exact h'
  · rcases h with ⟨⟨⟩⟩

中文:
定理 mem_chain_of_mem_ωSup
  条件: {c : Chain (Part α)} {a : α} (h : a in Part.ωSup c)
  结论: some a in c
  证明: by
  simp only [Part.ωSup] at h; split_ifs at h with h_1
  · have h' := Classical.choose_spec h_1
    rw [← eq_some_iff] at h
    rw [← h]
    exact h'
  · rcases h with ⟨⟨⟩⟩

Depends on / 依赖: Classical, Classical.choose_spec, choose_spec, eq_some_iff, split_ifs
-/
theorem mem_chain_of_mem_ωSup {c : Chain (Part α)} {a : α} (h : a in Part.ωSup c) : some a in c := by
  simp only [Part.ωSup] at h; split_ifs at h with h_1
  · have h' := Classical.choose_spec h_1
    rw [← eq_some_iff] at h
    rw [← h]
    exact h'
  · rcases h with ⟨⟨⟩⟩

/--
Instance `omegaCompletePartialOrder` / 实例 `omegaCompletePartialOrder`

English:
instance omegaCompletePartialOrder
  signature: :
  body: Part.ωSup
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

中文:
实例 omegaCompletePartialOrder
  签名: :
  定义体: Part.ωSup
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

/--
theorem `mem_ωSup` / 定理 `mem_ωSup`

English:
theorem mem_ωSup
  given: (x : α) (c : Chain (Part α))
  statement: x in ωSup c ↔ some x in c
  proof: by
  simp only [ωSup, Part.ωSup]
  constructor
  · exact fun a => mem_chain_of_mem_ωSup a
  · intro h
    have h' : exists a : α, some a in c := ⟨_, h⟩
    rw [dif_pos h']
    have hh := Classical.choose_spec h'
    rw [eq_of_chain hh h]
    simp

中文:
定理 mem_ωSup
  条件: (x : α) (c : Chain (Part α))
  结论: x in ωSup c ↔ some x in c
  证明: by
  simp only [ωSup, Part.ωSup]
  constructor
  · exact fun a => mem_chain_of_mem_ωSup a
  · intro h
    have h' : exists a : α, some a in c := ⟨_, h⟩
    rw [dif_pos h']
    have hh := Classical.choose_spec h'
    rw [eq_of_chain hh h]
    simp

Depends on / 依赖: Classical, Classical.choose_spec, choose_spec, dif_pos, eq_of_chain
-/
theorem mem_ωSup (x : α) (c : Chain (Part α)) : x in ωSup c ↔ some x in c := by
  simp only [ωSup, Part.ωSup]
  constructor
  · exact fun a => mem_chain_of_mem_ωSup a
  · intro h
    have h' : exists a : α, some a in c := ⟨_, h⟩
    rw [dif_pos h']
    have hh := Classical.choose_spec h'
    rw [eq_of_chain hh h]
    simp

end Inst

end Part

section Pi

variable {β : α -> Type*}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: a, OmegaCompletePartialOrder (β a)] :
  body: ωSup (c.map (Pi.evalOrderHom a))
  ωSup_le _ _ hf a :=
ωSup_le _ _ by
      rintro i
      apply hf
le_ωSup _ _ _ := le_ωSup_of_le _ le_rfl

中文:
实例 [forall
  签名: a, OmegaCompletePartialOrder (β a)] :
  定义体: ωSup (c.map (Pi.evalOrderHom a))
  ωSup_le _ _ hf a :=
ωSup_le _ _ by
      rintro i
      apply hf
le_ωSup _ _ _ := le_ωSup_of_le _ le_rfl

Depends on / 依赖: Pi.evalOrderHom, c.map, evalOrderHom
-/
instance [forall a, OmegaCompletePartialOrder (β a)] :
    OmegaCompletePartialOrder (forall a, β a) where
  ωSup c a := ωSup (c.map (Pi.evalOrderHom a))
  ωSup_le _ _ hf a :=
ωSup_le _ _ by
      rintro i
      apply hf
le_ωSup _ _ _ := le_ωSup_of_le _ le_rfl

namespace OmegaCompletePartialOrder

variable [forall x, OmegaCompletePartialOrder <| β x]
variable [OmegaCompletePartialOrder γ]
variable {f : γ -> forall x, β x}

/--
lemma `ωScottContinuous.apply₂` / 引理 `ωScottContinuous.apply₂`

English:
lemma ωScottContinuous.apply₂
  given: (hf : ωScottContinuous f) (a : α)
  statement: ωScottContinuous (f · a)
  proof: ωScottContinuous.of_monotone_map_ωSup
    ⟨fun _ _ h => hf.monotone h a, fun c => congr_fun (hf.map_ωSup c) a⟩

@[fun_prop]

中文:
引理 ωScottContinuous.apply₂
  条件: (hf : ωScottContinuous f) (a : α)
  结论: ωScottContinuous (f · a)
  证明: ωScottContinuous.of_monotone_map_ωSup
    ⟨fun _ _ h => hf.monotone h a, fun c => congr_fun (hf.map_ωSup c) a⟩

@[fun_prop]

Depends on / 依赖: ScottContinuous.of_monotone_map_, congr_fun, hf.map_, hf.monotone, monotone
-/
lemma ωScottContinuous.apply₂ (hf : ωScottContinuous f) (a : α) : ωScottContinuous (f · a) :=
  ωScottContinuous.of_monotone_map_ωSup
    ⟨fun _ _ h => hf.monotone h a, fun c => congr_fun (hf.map_ωSup c) a⟩

@[fun_prop]
/--
lemma `ωScottContinuous.apply` / 引理 `ωScottContinuous.apply`

English:
lemma ωScottContinuous.apply
  given: (x : α)
  statement: ωScottContinuous (fun f : forall x, β x => f x)
  proof: apply₂ id x

@[fun_prop]

中文:
引理 ωScottContinuous.apply
  条件: (x : α)
  结论: ωScottContinuous (fun f : 对任意 x, β x => f x)
  证明: apply₂ id x

@[fun_prop]
-/
lemma ωScottContinuous.apply (x : α) : ωScottContinuous (fun f : forall x, β x => f x) :=
  apply₂ id x

@[fun_prop]
/--
lemma `ωScottContinuous.of_apply₂` / 引理 `ωScottContinuous.of_apply₂`

English:
lemma ωScottContinuous.of_apply₂
  given: (hf : forall a, ωScottContinuous (f · a))
  statement: ωScottContinuous f
  proof: ωScottContinuous.of_monotone_map_ωSup
    ⟨fun _ _ h a => (hf a).monotone h, fun c => by ext a; apply (hf a).map_ωSup c⟩

中文:
引理 ωScottContinuous.of_apply₂
  条件: (hf : 对任意 a, ωScottContinuous (f · a))
  结论: ωScottContinuous f
  证明: ωScottContinuous.of_monotone_map_ωSup
    ⟨fun _ _ h a => (hf a).monotone h, fun c => by ext a; apply (hf a).map_ωSup c⟩

Depends on / 依赖: ScottContinuous.of_monotone_map_, monotone
-/
lemma ωScottContinuous.of_apply₂ (hf : forall a, ωScottContinuous (f · a)) : ωScottContinuous f :=
  ωScottContinuous.of_monotone_map_ωSup
    ⟨fun _ _ h a => (hf a).monotone h, fun c => by ext a; apply (hf a).map_ωSup c⟩

/--
lemma `ωScottContinuous_iff_apply₂` / 引理 `ωScottContinuous_iff_apply₂`

English:
lemma ωScottContinuous_iff_apply₂
  statement: ωScottContinuous f ↔ forall a, ωScottContinuous (f · a)
  proof: ⟨ωScottContinuous.apply₂, ωScottContinuous.of_apply₂⟩

中文:
引理 ωScottContinuous_iff_apply₂
  结论: ωScottContinuous f ↔ 对任意 a, ωScottContinuous (f · a)
  证明: ⟨ωScottContinuous.apply₂, ωScottContinuous.of_apply₂⟩

Depends on / 依赖: ScottContinuous.apply, ScottContinuous.of_apply
-/
lemma ωScottContinuous_iff_apply₂ : ωScottContinuous f ↔ forall a, ωScottContinuous (f · a) :=
  ⟨ωScottContinuous.apply₂, ωScottContinuous.of_apply₂⟩

end OmegaCompletePartialOrder

end Pi

namespace Prod

variable [OmegaCompletePartialOrder α]
variable [OmegaCompletePartialOrder β]
variable [OmegaCompletePartialOrder γ]

/-- The supremum of a chain in the product `ω`-CPO. -/
@[simps]
/--
Definition of `ωSupImpl` / `ωSupImpl` 的定义

English:
definition ωSupImpl
  signature: (c : Chain (α × β))
  body: (ωSup (c.map OrderHom.fst), ωSup (c.map OrderHom.snd))

@[simps! ωSup_fst ωSup_snd]

中文:
定义 ωSupImpl
  签名: (c : Chain (α × β))
  定义体: (ωSup (c.map OrderHom.fst), ωSup (c.map OrderHom.snd))

@[simps! ωSup_fst ωSup_snd]
-/
protected def ωSupImpl (c : Chain (α × β)) : α × β :=
  (ωSup (c.map OrderHom.fst), ωSup (c.map OrderHom.snd))

@[simps! ωSup_fst ωSup_snd]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: OmegaCompletePartialOrder (α × β)
  body: Prod.ωSupImpl
  ωSup_le := fun _ _ h => ⟨ωSup_le _ _ fun i => (h i).1, ωSup_le _ _ fun i => (h i).2⟩
  le_ωSup c i := ⟨le_ωSup (c.map OrderHom.fst) i, le_ωSup (c.map OrderHom.snd) i⟩

中文:
实例 :
  签名: OmegaCompletePartialOrder (α × β)
  定义体: Prod.ωSupImpl
  ωSup_le := fun _ _ h => ⟨ωSup_le _ _ fun i => (h i).1, ωSup_le _ _ fun i => (h i).2⟩
  le_ωSup c i := ⟨le_ωSup (c.map OrderHom.fst) i, le_ωSup (c.map OrderHom.snd) i⟩
-/
instance : OmegaCompletePartialOrder (α × β) where
  ωSup := Prod.ωSupImpl
  ωSup_le := fun _ _ h => ⟨ωSup_le _ _ fun i => (h i).1, ωSup_le _ _ fun i => (h i).2⟩
  le_ωSup c i := ⟨le_ωSup (c.map OrderHom.fst) i, le_ωSup (c.map OrderHom.snd) i⟩

/--
theorem `ωSup_zip` / 定理 `ωSup_zip`

English:
theorem ωSup_zip
  given: (c₀ : Chain α) (c₁ : Chain β)
  statement: ωSup (c₀.zip c₁) = (ωSup c₀, ωSup c₁)
  proof: rfl

@[fun_prop]

中文:
定理 ωSup_zip
  条件: (c₀ : Chain α) (c₁ : Chain β)
  结论: ωSup (c₀.zip c₁) = (ωSup c₀, ωSup c₁)
  证明: rfl

@[fun_prop]
-/
theorem ωSup_zip (c₀ : Chain α) (c₁ : Chain β) : ωSup (c₀.zip c₁) = (ωSup c₀, ωSup c₁) := rfl

@[fun_prop]
/--
lemma `ωScottContinuous.prodMk` / 引理 `ωScottContinuous.prodMk`

English:
lemma ωScottContinuous.prodMk
  proof: ScottContinuousOn.prodMk (fun a b hab => ⟨pair a b hab, range_pair a b hab⟩) hf hg

@[fun_prop]

中文:
引理 ωScottContinuous.prodMk
  证明: ScottContinuousOn.prodMk (fun a b hab => ⟨pair a b hab, range_pair a b hab⟩) hf hg

@[fun_prop]

Depends on / 依赖: ScottContinuousOn, ScottContinuousOn.prodMk, prodMk, range_pair
-/
lemma ωScottContinuous.prodMk
    {f : α -> β} (hf : ωScottContinuous f) {g : α -> γ} (hg : ωScottContinuous g) :
    ωScottContinuous fun x => (f x, g x) :=
  ScottContinuousOn.prodMk (fun a b hab => ⟨pair a b hab, range_pair a b hab⟩) hf hg

@[fun_prop]
/--
lemma `ωScottContinuous_fst` / 引理 `ωScottContinuous_fst`

English:
lemma ωScottContinuous_fst
  statement: ωScottContinuous (Prod.fst : α × β -> α)
  proof: ScottContinuousOn.fst

@[fun_prop]

中文:
引理 ωScottContinuous_fst
  结论: ωScottContinuous (Prod.fst : α × β -> α)
  证明: ScottContinuousOn.fst

@[fun_prop]

Depends on / 依赖: ScottContinuousOn, ScottContinuousOn.fst
-/
lemma ωScottContinuous_fst : ωScottContinuous (Prod.fst : α × β -> α) :=
  ScottContinuousOn.fst

@[fun_prop]
/--
lemma `ωScottContinuous_snd` / 引理 `ωScottContinuous_snd`

English:
lemma ωScottContinuous_snd
  statement: ωScottContinuous (Prod.snd : α × β -> β)
  proof: ScottContinuousOn.snd

中文:
引理 ωScottContinuous_snd
  结论: ωScottContinuous (Prod.snd : α × β -> β)
  证明: ScottContinuousOn.snd

Depends on / 依赖: ScottContinuousOn, ScottContinuousOn.snd
-/
lemma ωScottContinuous_snd : ωScottContinuous (Prod.snd : α × β -> β) :=
  ScottContinuousOn.snd

end Prod

namespace OmegaCompletePartialOrder
variable [OmegaCompletePartialOrder α] [OmegaCompletePartialOrder β]
variable [OmegaCompletePartialOrder γ] [OmegaCompletePartialOrder δ]

namespace OrderHom

/-- The `ωSup` operator for monotone functions. -/
@[simps]
/--
Definition of `ωSup` / `ωSup` 的定义

English:
definition ωSup
  signature: (c : Chain (α ->o β))
  body: ωSup (c.map (OrderHom.apply a))
  monotone' _ _ h := ωSup_le_ωSup_of_le ((Chain.map_le_map _) fun a => a.monotone h)

@[simps! ωSup_coe]

中文:
定义 ωSup
  签名: (c : Chain (α ->o β))
  定义体: ωSup (c.map (OrderHom.apply a))
  monotone' _ _ h := ωSup_le_ωSup_of_le ((Chain.map_le_map _) fun a => a.monotone h)

@[simps! ωSup_coe]
-/
protected def ωSup (c : Chain (α ->o β)) : α ->o β where
  toFun a := ωSup (c.map (OrderHom.apply a))
  monotone' _ _ h := ωSup_le_ωSup_of_le ((Chain.map_le_map _) fun a => a.monotone h)

@[simps! ωSup_coe]
/--
Instance `omegaCompletePartialOrder` / 实例 `omegaCompletePartialOrder`

English:
instance omegaCompletePartialOrder
  signature: : OmegaCompletePartialOrder (α ->o β)
  body: OmegaCompletePartialOrder.lift OrderHom.coeFnHom OrderHom.ωSup (fun _ _ h => h) fun _ => rfl

中文:
实例 omegaCompletePartialOrder
  签名: : OmegaCompletePartialOrder (α ->o β)
  定义体: OmegaCompletePartialOrder.lift OrderHom.coeFnHom OrderHom.ωSup (fun _ _ h => h) fun _ => rfl

Depends on / 依赖: OmegaCompletePartialOrder, OmegaCompletePartialOrder.lift, OrderHom, OrderHom.coeFnHom, coeFnHom
-/
instance omegaCompletePartialOrder : OmegaCompletePartialOrder (α ->o β) :=
  OmegaCompletePartialOrder.lift OrderHom.coeFnHom OrderHom.ωSup (fun _ _ h => h) fun _ => rfl

end OrderHom

variable (α β) in
/--
Definition of `ContinuousHom` / `ContinuousHom` 的定义

English:
structure ContinuousHom
  parameters: extends OrderHom α β
  extends: OrderHom α β
  axioms and operations (1):
    - map_ωSup'((c : Chain α)) : toFun (ωSup c) = ωSup (c.map toOrderHom)

中文:
结构 ContinuousHom
  参数: extends OrderHom α β
  继承: OrderHom α β
  公理与运算 (1 个):
    - map_ωSup'((c : Chain α)) : toFun (ωSup c) = ωSup (c.map toOrderHom)
-/
structure ContinuousHom extends OrderHom α β where
  /-- The underlying function of a `ContinuousHom` is continuous, i.e. it preserves `ωSup` -/
  protected map_ωSup' (c : Chain α) : toFun (ωSup c) = ωSup (c.map toOrderHom)

attribute [nolint docBlame] ContinuousHom.toOrderHom

@[inherit_doc] infixr:25 " ->𝒄 " => ContinuousHom -- Input: \r\MIc

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FunLike (α ->𝒄 β) α β
  body: f.toFun
  coe_injective := by rintro ⟨⟩ ⟨⟩ h; congr; exact DFunLike.ext' h

中文:
实例 :
  签名: FunLike (α ->𝒄 β) α β
  定义体: f.toFun
  coe_injective := by rintro ⟨⟩ ⟨⟩ h; congr; exact DFunLike.ext' h

Depends on / 依赖: f.toFun
-/
instance : FunLike (α ->𝒄 β) α β where
  coe f := f.toFun
  coe_injective := by rintro ⟨⟩ ⟨⟩ h; congr; exact DFunLike.ext' h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: OrderHomClass (α ->𝒄 β) α β
  body: f.mono h

中文:
实例 :
  签名: OrderHomClass (α ->𝒄 β) α β
  定义体: f.mono h

Depends on / 依赖: f.mono
-/
instance : OrderHomClass (α ->𝒄 β) α β where
  map_rel f _ _ h := f.mono h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (α ->𝒄 β)
  body: (PartialOrder.lift fun f => f.toOrderHom.toFun) by rintro ⟨⟨⟩⟩ ⟨⟨⟩⟩ h; congr

中文:
实例 :
  签名: PartialOrder (α ->𝒄 β)
  定义体: (PartialOrder.lift fun f => f.toOrderHom.toFun) by rintro ⟨⟨⟩⟩ ⟨⟨⟩⟩ h; congr

Depends on / 依赖: PartialOrder, PartialOrder.lift, f.toOrderHom.toFun, toOrderHom
-/
instance : PartialOrder (α ->𝒄 β) :=
(PartialOrder.lift fun f => f.toOrderHom.toFun) by rintro ⟨⟨⟩⟩ ⟨⟨⟩⟩ h; congr

namespace ContinuousHom

@[fun_prop]
/--
lemma `ωScottContinuous` / 引理 `ωScottContinuous`

English:
lemma ωScottContinuous
  given: (f : α ->𝒄 β)
  statement: ωScottContinuous f
  proof: ωScottContinuous.of_map_ωSup_of_orderHom f.map_ωSup'

中文:
引理 ωScottContinuous
  条件: (f : α ->𝒄 β)
  结论: ωScottContinuous f
  证明: ωScottContinuous.of_map_ωSup_of_orderHom f.map_ωSup'
-/
protected lemma ωScottContinuous (f : α ->𝒄 β) : ωScottContinuous f :=
  ωScottContinuous.of_map_ωSup_of_orderHom f.map_ωSup'

-- Not a `simp` lemma because in many cases projection is simpler than a generic coercion
/--
theorem `toOrderHom_eq_coe` / 定理 `toOrderHom_eq_coe`

English:
theorem toOrderHom_eq_coe
  given: (f : α ->𝒄 β)
  statement: f.1 = f
  proof: rfl

中文:
定理 toOrderHom_eq_coe
  条件: (f : α ->𝒄 β)
  结论: f.1 = f
  证明: rfl
-/
theorem toOrderHom_eq_coe (f : α ->𝒄 β) : f.1 = f := rfl

/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  given: (f : α ->o β) (hf)
  statement: ⇑(mk f hf) = f
  proof: rfl

中文:
定理 coe_mk
  条件: (f : α ->o β) (hf)
  结论: ⇑(mk f hf) = f
  证明: rfl
-/
@[simp] theorem coe_mk (f : α ->o β) (hf) : ⇑(mk f hf) = f := rfl

/--
theorem `coe_toOrderHom` / 定理 `coe_toOrderHom`

English:
theorem coe_toOrderHom
  given: (f : α ->𝒄 β)
  statement: ⇑f.1 = f
  proof: rfl

中文:
定理 coe_toOrderHom
  条件: (f : α ->𝒄 β)
  结论: ⇑f.1 = f
  证明: rfl
-/
@[simp] theorem coe_toOrderHom (f : α ->𝒄 β) : ⇑f.1 = f := rfl

/--
Definition of `Simps.apply` / `Simps.apply` 的定义

English:
definition Simps.apply
  signature: (h : α ->𝒄 β)
  body: h

initialize_simps_projections ContinuousHom (toFun -> apply)

中文:
定义 Simps.apply
  签名: (h : α ->𝒄 β)
  定义体: h

initialize_simps_projections ContinuousHom (toFun -> apply)
-/
def Simps.apply (h : α ->𝒄 β) : α -> β :=
  h

initialize_simps_projections ContinuousHom (toFun -> apply)

/-- Constructs a `ContinuousHom` from a function `f` and a proof of `ωScottContinuous f`.
By default, the proof is inferred by `fun_prop`, which makes it ideal for simple cases.
-/
@[simps!]
/--
Definition of `ofFun` / `ofFun` 的定义

English:
definition ofFun
  signature: (f : α -> β) (hf : ωScottContinuous f := by fun_prop)
  body: f
  monotone' := hf.monotone
  map_ωSup' := hf.map_ωSup

中文:
定义 ofFun
  签名: (f : α -> β) (hf : ωScottContinuous f := by fun_prop)
  定义体: f
  monotone' := hf.monotone
  map_ωSup' := hf.map_ωSup

Depends on / 依赖: fun_prop, hf.map_, hf.monotone, monotone
-/
def ofFun (f : α -> β) (hf : ωScottContinuous f := by fun_prop) : α ->𝒄 β where
  toFun := f
  monotone' := hf.monotone
  map_ωSup' := hf.map_ωSup

/--
theorem `congr_fun` / 定理 `congr_fun`

English:
theorem congr_fun
  given: {f g : α ->𝒄 β} (h : f = g) (x : α)
  statement: f x = g x
  proof: DFunLike.congr_fun h x

中文:
定理 congr_fun
  条件: {f g : α ->𝒄 β} (h : f = g) (x : α)
  结论: f x = g x
  证明: DFunLike.congr_fun h x
-/
protected theorem congr_fun {f g : α ->𝒄 β} (h : f = g) (x : α) : f x = g x :=
  DFunLike.congr_fun h x

/--
theorem `congr_arg` / 定理 `congr_arg`

English:
theorem congr_arg
  given: (f : α ->𝒄 β) {x y : α} (h : x = y)
  statement: f x = f y
  proof: congr_arg f h

中文:
定理 congr_arg
  条件: (f : α ->𝒄 β) {x y : α} (h : x = y)
  结论: f x = f y
  证明: congr_arg f h
-/
protected theorem congr_arg (f : α ->𝒄 β) {x y : α} (h : x = y) : f x = f y :=
  congr_arg f h

/--
theorem `monotone` / 定理 `monotone`

English:
theorem monotone
  given: (f : α ->𝒄 β)
  statement: Monotone f
  proof: f.monotone'

@[gcongr, mono]

中文:
定理 monotone
  条件: (f : α ->𝒄 β)
  结论: Monotone f
  证明: f.monotone'

@[gcongr, mono]
-/
protected theorem monotone (f : α ->𝒄 β) : Monotone f :=
  f.monotone'

@[gcongr, mono]
/--
theorem `apply_mono` / 定理 `apply_mono`

English:
theorem apply_mono
  given: {f g : α ->𝒄 β} {x y : α} (h₁ : f <= g) (h₂ : x <= y)
  statement: f x <= g y
  proof: OrderHom.apply_mono (show (f : α ->o β) <= g from h₁) h₂

中文:
定理 apply_mono
  条件: {f g : α ->𝒄 β} {x y : α} (h₁ : f <= g) (h₂ : x <= y)
  结论: f x <= g y
  证明: OrderHom.apply_mono (show (f : α ->o β) <= g from h₁) h₂

Depends on / 依赖: OrderHom, OrderHom.apply_mono, apply_mono, infer_instance, stabilizerHomSurjectiveAuxFunctor
-/
theorem apply_mono {f g : α ->𝒄 β} {x y : α} (h₁ : f <= g) (h₂ : x <= y) : f x <= g y :=
  OrderHom.apply_mono (show (f : α ->o β) <= g from h₁) h₂

/--
theorem `ωSup_bind` / 定理 `ωSup_bind`

English:
theorem ωSup_bind
  given: {β γ : Type v} (c : Chain α) (f : α ->o Part β) (g : α ->o β -> Part γ)
  proof: by
  apply eq_of_forall_ge_iff; intro x
  simp only [ωSup_le_iff, Part.bind_le]
  constructor <;> intro h'''
  · intro b hb
    apply ωSup_le _ _ _
    rintro i y hy
    simp only [Part.mem_ωSup] at hb
    rcases hb with ⟨j, hb⟩
    replace hb := hb.symm
    simp only [Part.eq_some_iff, Chain.coe_ma

中文:
定理 ωSup_bind
  条件: {β γ : 类型v} (c : Chain α) (f : α ->o Part β) (g : α ->o β -> Part γ)
  证明: by
  apply eq_of_forall_ge_iff; intro x
  simp only [ωSup_le_iff, Part.bind_le]
  constructor <;> intro h'''
  · intro b hb
    apply ωSup_le _ _ _
    rintro i y hy
    simp only [Part.mem_ωSup] at hb
    rcases hb with ⟨j, hb⟩
    replace hb := hb.symm
    simp only [Part.eq_some_iff, Chain.coe_ma

Depends on / 依赖: Chain.coe_map, FixedPoints, FixedPoints.subalgebra, Function, Function.comp_apply, Ideal.Quotient.exists_algEquiv_fixedPoint_quotient_under, Ideal.Quotient.mk_s, Ideal.Quotient.stabilizerHom_surjective, IsScalarTower, IsScalarTower.of_algebraMap_eq, Part.bind_le, Part.eq_some_iff, Part.mem_, Part.mem_b, Q.under, Quotient, Quotient.ind, bind_le, c.mono, coe_map
-/
theorem ωSup_bind {β γ : Type v} (c : Chain α) (f : α ->o Part β) (g : α ->o β -> Part γ) :
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
    replace hb : b in f (c (max i j)) := f.mono (c.mono (le_max_right i j)) _ hb
    replace hy : y in g (c (max i j)) b := g.mono (c.mono (le_max_left i j)) _ _ hy
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
/--
lemma `ωScottContinuous.bind` / 引理 `ωScottContinuous.bind`

English:
lemma ωScottContinuous.bind
  statement: {β γ} {f : α -> Part β} {g : α -> β -> Part γ} (hf : ωScottContinuous f)
  proof: ωScottContinuous.of_monotone_map_ωSup
    ⟨hf.monotone.partBind hg.monotone, fun c => by rw [hf.map_ωSup, hg.map_ωSup, ← ωSup_bind]; rfl⟩

中文:
引理 ωScottContinuous.bind
  结论: {β γ} {f : α -> Part β} {g : α -> β -> Part γ} (hf : ωScottContinuous f)
  证明: ωScottContinuous.of_monotone_map_ωSup
    ⟨hf.monotone.partBind hg.monotone, fun c => by rw [hf.map_ωSup, hg.map_ωSup, ← ωSup_bind]; rfl⟩

Depends on / 依赖: ScottContinuous.of_monotone_map_, hf.map_, hf.monotone.partBind, hg.map_, hg.monotone, monotone, partBind
-/
lemma ωScottContinuous.bind {β γ} {f : α -> Part β} {g : α -> β -> Part γ} (hf : ωScottContinuous f)
    (hg : ωScottContinuous g) : ωScottContinuous fun x => f x >>= g x :=
  ωScottContinuous.of_monotone_map_ωSup
    ⟨hf.monotone.partBind hg.monotone, fun c => by rw [hf.map_ωSup, hg.map_ωSup, ← ωSup_bind]; rfl⟩

/--
lemma `ωScottContinuous.map` / 引理 `ωScottContinuous.map`

English:
lemma ωScottContinuous.map
  given: {β γ} {f : β -> γ} {g : α -> Part β} (hg : ωScottContinuous g)
  proof: by
  simpa only [map_eq_bind_pure_comp] using! ωScottContinuous.bind hg ωScottContinuous.const

中文:
引理 ωScottContinuous.map
  条件: {β γ} {f : β -> γ} {g : α -> Part β} (hg : ωScottContinuous g)
  证明: by
  simpa only [map_eq_bind_pure_comp] using! ωScottContinuous.bind hg ωScottContinuous.const

Depends on / 依赖: ScottContinuous.bind, ScottContinuous.const, map_eq_bind_pure_comp
-/
lemma ωScottContinuous.map {β γ} {f : β -> γ} {g : α -> Part β} (hg : ωScottContinuous g) :
ωScottContinuous fun x => f < > g x := by
  simpa only [map_eq_bind_pure_comp] using! ωScottContinuous.bind hg ωScottContinuous.const

/--
lemma `ωScottContinuous.seq` / 引理 `ωScottContinuous.seq`

English:
lemma ωScottContinuous.seq
  statement: {β γ} {f : α -> Part (β -> γ)} {g : α -> Part β} (hf : ωScottContinuous f)
  proof: by
  simp only [seq_eq_bind_map]
exact ωScottContinuous.bind hf ωScottContinuous.of_apply₂ fun _ => ωScottContinuous.map hg

中文:
引理 ωScottContinuous.seq
  结论: {β γ} {f : α -> Part (β -> γ)} {g : α -> Part β} (hf : ωScottContinuous f)
  证明: by
  simp only [seq_eq_bind_map]
exact ωScottContinuous.bind hf ωScottContinuous.of_apply₂ fun _ => ωScottContinuous.map hg

Depends on / 依赖: ScottContinuous.bind, ScottContinuous.map, ScottContinuous.of_apply, seq_eq_bind_map
-/
lemma ωScottContinuous.seq {β γ} {f : α -> Part (β -> γ)} {g : α -> Part β} (hf : ωScottContinuous f)
    (hg : ωScottContinuous g) : ωScottContinuous fun x => f x <*> g x := by
  simp only [seq_eq_bind_map]
exact ωScottContinuous.bind hf ωScottContinuous.of_apply₂ fun _ => ωScottContinuous.map hg

/--
theorem `continuous` / 定理 `continuous`

English:
theorem continuous
  given: (F : α ->𝒄 β) (C : Chain α)
  statement: F (ωSup C) = ωSup (C.map F)
  proof: F.ωScottContinuous.map_ωSup _

中文:
定理 continuous
  条件: (F : α ->𝒄 β) (C : Chain α)
  结论: F (ωSup C) = ωSup (C.map F)
  证明: F.ωScottContinuous.map_ωSup _

Depends on / 依赖: ScottContinuous.map_
-/
theorem continuous (F : α ->𝒄 β) (C : Chain α) : F (ωSup C) = ωSup (C.map F) :=
  F.ωScottContinuous.map_ωSup _

/-- Construct a continuous function from a bare function, a continuous function, and a proof that
they are equal. -/
@[simps!]
/--
Definition of `copy` / `copy` 的定义

English:
definition copy
  signature: (f : α -> β) (g : α ->𝒄 β) (h : f = g)
  body: g.1.copy f h
  map_ωSup' := by rw [OrderHom.copy_eq]; exact g.map_ωSup'

中文:
定义 copy
  签名: (f : α -> β) (g : α ->𝒄 β) (h : f = g)
  定义体: g.1.copy f h
  map_ωSup' := by rw [OrderHom.copy_eq]; exact g.map_ωSup'
-/
def copy (f : α -> β) (g : α ->𝒄 β) (h : f = g) : α ->𝒄 β where
  toOrderHom := g.1.copy f h
  map_ωSup' := by rw [OrderHom.copy_eq]; exact g.map_ωSup'

/-- The identity as a continuous function. -/
@[simps!]
/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: : α ->𝒄 α
  body: ⟨OrderHom.id, ωScottContinuous.id.map_ωSup⟩

中文:
定义 id
  签名: : α ->𝒄 α
  定义体: ⟨OrderHom.id, ωScottContinuous.id.map_ωSup⟩

Depends on / 依赖: OrderHom, OrderHom.id, ScottContinuous.id.map_
-/
def id : α ->𝒄 α := ⟨OrderHom.id, ωScottContinuous.id.map_ωSup⟩

/-- The composition of continuous functions. -/
@[simps!]
/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: (f : β ->𝒄 γ) (g : α ->𝒄 β)
  body: ⟨.comp f.1 g.1, (f.ωScottContinuous.comp g.ωScottContinuous).map_ωSup⟩

@[ext]

中文:
定义 comp
  签名: (f : β ->𝒄 γ) (g : α ->𝒄 β)
  定义体: ⟨.comp f.1 g.1, (f.ωScottContinuous.comp g.ωScottContinuous).map_ωSup⟩

@[ext]

Depends on / 依赖: ScottContinuous.comp
-/
def comp (f : β ->𝒄 γ) (g : α ->𝒄 β) : α ->𝒄 γ :=
  ⟨.comp f.1 g.1, (f.ωScottContinuous.comp g.ωScottContinuous).map_ωSup⟩

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: (f g : α ->𝒄 β) (h : forall x, f x = g x)
  statement: f = g
  proof: DFunLike.ext f g h

中文:
定理 ext
  条件: (f g : α ->𝒄 β) (h : 对任意 x, f x = g x)
  结论: f = g
  证明: DFunLike.ext f g h
-/
protected theorem ext (f g : α ->𝒄 β) (h : forall x, f x = g x) : f = g := DFunLike.ext f g h

/--
theorem `coe_inj` / 定理 `coe_inj`

English:
theorem coe_inj
  given: (f g : α ->𝒄 β) (h : (f : α -> β) = g)
  statement: f = g
  proof: DFunLike.ext' h

@[simp]

中文:
定理 coe_inj
  条件: (f g : α ->𝒄 β) (h : (f : α -> β) = g)
  结论: f = g
  证明: DFunLike.ext' h

@[simp]

Depends on / 依赖: faithful, hGKL.faithful
-/
protected theorem coe_inj (f g : α ->𝒄 β) (h : (f : α -> β) = g) : f = g :=
  DFunLike.ext' h

@[simp]
/--
theorem `comp_id` / 定理 `comp_id`

English:
theorem comp_id
  given: (f : β ->𝒄 γ)
  statement: f.comp id = f
  proof: rfl

@[simp]

中文:
定理 comp_id
  条件: (f : β ->𝒄 γ)
  结论: f.comp id = f
  证明: rfl

@[simp]
-/
theorem comp_id (f : β ->𝒄 γ) : f.comp id = f := rfl

@[simp]
/--
theorem `id_comp` / 定理 `id_comp`

English:
theorem id_comp
  given: (f : β ->𝒄 γ)
  statement: id.comp f = f
  proof: rfl

@[simp]

中文:
定理 id_comp
  条件: (f : β ->𝒄 γ)
  结论: id.comp f = f
  证明: rfl

@[simp]
-/
theorem id_comp (f : β ->𝒄 γ) : id.comp f = f := rfl

@[simp]
/--
theorem `comp_assoc` / 定理 `comp_assoc`

English:
theorem comp_assoc
  given: (f : γ ->𝒄 δ) (g : β ->𝒄 γ) (h : α ->𝒄 β)
  statement: f.comp (g.comp h) = (f.comp g).comp h
  proof: rfl

@[simp]

中文:
定理 comp_assoc
  条件: (f : γ ->𝒄 δ) (g : β ->𝒄 γ) (h : α ->𝒄 β)
  结论: f.comp (g.comp h) = (f.comp g).comp h
  证明: rfl

@[simp]
-/
theorem comp_assoc (f : γ ->𝒄 δ) (g : β ->𝒄 γ) (h : α ->𝒄 β) : f.comp (g.comp h) = (f.comp g).comp h :=
  rfl

@[simp]
/--
theorem `coe_apply` / 定理 `coe_apply`

English:
theorem coe_apply
  given: (a : α) (f : α ->𝒄 β)
  statement: (f : α ->o β) a = f a
  proof: rfl

中文:
定理 coe_apply
  条件: (a : α) (f : α ->𝒄 β)
  结论: (f : α ->o β) a = f a
  证明: rfl
-/
theorem coe_apply (a : α) (f : α ->𝒄 β) : (f : α ->o β) a = f a :=
  rfl

/-- `Function.const` is a continuous function. -/
@[simps!]
/--
Definition of `const` / `const` 的定义

English:
definition const
  signature: (x : β)
  body: ⟨.const _ x, ωScottContinuous.const.map_ωSup⟩

中文:
定义 const
  签名: (x : β)
  定义体: ⟨.const _ x, ωScottContinuous.const.map_ωSup⟩

Depends on / 依赖: ScottContinuous.const.map_
-/
def const (x : β) : α ->𝒄 β := ⟨.const _ x, ωScottContinuous.const.map_ωSup⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Inhabited
  signature: β] : Inhabited (α ->𝒄 β)
  body: ⟨const default⟩

中文:
实例 [Inhabited
  签名: β] : Inhabited (α ->𝒄 β)
  定义体: ⟨const default⟩
-/
instance [Inhabited β] : Inhabited (α ->𝒄 β) :=
  ⟨const default⟩

/-- The map from continuous functions to monotone functions is itself a monotone function. -/
@[simps]
/--
Definition of `toMono` / `toMono` 的定义

English:
definition toMono
  signature: : (α ->𝒄 β) ->o α ->o β where
  body: f
  monotone' _ _ h := h

中文:
定义 toMono
  签名: : (α ->𝒄 β) ->o α ->o β where
  定义体: f
  monotone' _ _ h := h
-/
def toMono : (α ->𝒄 β) ->o α ->o β where
  toFun f := f
  monotone' _ _ h := h

/-- When proving that a chain of applications is below a bound `z`, it suffices to consider the
functions and values being selected from the same index in the chains.

This lemma is more specific than necessary, i.e. `c₀` only needs to be a
chain of monotone functions, but it is only used with continuous functions. -/
@[simp]
/--
theorem `forall_forall_merge` / 定理 `forall_forall_merge`

English:
theorem forall_forall_merge
  given: (c₀ : Chain (α ->𝒄 β)) (c₁ : Chain α) (z : β)
  proof: by
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

中文:
定理 forall_forall_merge
  条件: (c₀ : Chain (α ->𝒄 β)) (c₁ : Chain α) (z : β)
  证明: by
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

Depends on / 依赖: introv, le_max_left, le_max_right, le_trans, monotone
-/
theorem forall_forall_merge (c₀ : Chain (α ->𝒄 β)) (c₁ : Chain α) (z : β) :
    (forall i j : Nat, (c₀ i) (c₁ j) <= z) ↔ forall i : Nat, (c₀ i) (c₁ i) <= z := by
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
/--
theorem `forall_forall_merge'` / 定理 `forall_forall_merge'`

English:
theorem forall_forall_merge'
  given: (c₀ : Chain (α ->𝒄 β)) (c₁ : Chain α) (z : β)
  proof: by
  rw [forall_comm]; rw [forall_forall_merge]

中文:
定理 forall_forall_merge'
  条件: (c₀ : Chain (α ->𝒄 β)) (c₁ : Chain α) (z : β)
  证明: by
  rw [forall_comm]; rw [forall_forall_merge]

Depends on / 依赖: forall_comm, forall_forall_merge
-/
theorem forall_forall_merge' (c₀ : Chain (α ->𝒄 β)) (c₁ : Chain α) (z : β) :
    (forall j i : Nat, (c₀ i) (c₁ j) <= z) ↔ forall i : Nat, (c₀ i) (c₁ i) <= z := by
  rw [forall_comm]; rw [forall_forall_merge]

/-- The `ωSup` operator for continuous functions, which takes the pointwise countable supremum
of the functions in the `ω`-chain. -/
@[simps!]
/--
Definition of `ωSup` / `ωSup` 的定义

English:
definition ωSup
  signature: (c : Chain (α ->𝒄 β))
  body: ωSup c.map toMono
  map_ωSup' c' := eq_of_forall_ge_iff fun a => by simp [(c _).ωScottContinuous.map_ωSup]

@[simps ωSup]

中文:
定义 ωSup
  签名: (c : Chain (α ->𝒄 β))
  定义体: ωSup c.map toMono
  map_ωSup' c' := eq_of_forall_ge_iff fun a => by simp [(c _).ωScottContinuous.map_ωSup]

@[simps ωSup]
-/
protected def ωSup (c : Chain (α ->𝒄 β)) : α ->𝒄 β where
toOrderHom := ωSup c.map toMono
  map_ωSup' c' := eq_of_forall_ge_iff fun a => by simp [(c _).ωScottContinuous.map_ωSup]

@[simps ωSup]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: OmegaCompletePartialOrder (α ->𝒄 β)
  body: OmegaCompletePartialOrder.lift ContinuousHom.toMono ContinuousHom.ωSup
    (fun _ _ h => h) (fun _ => rfl)

中文:
实例 :
  签名: OmegaCompletePartialOrder (α ->𝒄 β)
  定义体: OmegaCompletePartialOrder.lift ContinuousHom.toMono ContinuousHom.ωSup
    (fun _ _ h => h) (fun _ => rfl)

Depends on / 依赖: ContinuousHom, ContinuousHom.toMono, OmegaCompletePartialOrder, OmegaCompletePartialOrder.lift, toMono
-/
instance : OmegaCompletePartialOrder (α ->𝒄 β) :=
  OmegaCompletePartialOrder.lift ContinuousHom.toMono ContinuousHom.ωSup
    (fun _ _ h => h) (fun _ => rfl)

set_option backward.defeqAttrib.useBackward true in
@[fun_prop]
/--
lemma `ωScottContinuous_apply` / 引理 `ωScottContinuous_apply`

English:
lemma ωScottContinuous_apply
  proof: by
  apply ωScottContinuous.of_monotone_map_ωSup ⟨?_, fun c => ?_⟩
  · intro x y hxy
    exact OrderHom.apply_mono (hf.monotone hxy) (hg.monotone hxy)
  · rw [hf.map_ωSup, hg.map_ωSup]
    simp only [ωSup_def, ωSup_apply]
    apply le_antisymm
    · apply ωSup_le
      intro i
      dsimp
      rw [

中文:
引理 ωScottContinuous_apply
  证明: by
  apply ωScottContinuous.of_monotone_map_ωSup ⟨?_, fun c => ?_⟩
  · intro x y hxy
    exact OrderHom.apply_mono (hf.monotone hxy) (hg.monotone hxy)
  · rw [hf.map_ωSup, hg.map_ωSup]
    simp only [ωSup_def, ωSup_apply]
    apply le_antisymm
    · apply ωSup_le
      intro i
      dsimp
      rw [

Depends on / 依赖: OrderHom, OrderHom.apply_mono, ScottContinuous.of_monotone_map_, apply_mono, c.monotone, continuous, hf.map_, hf.monotone, hg.map_, hg.monotone, le_antisymm, le_sup_left, le_sup_right, monotone
-/
lemma ωScottContinuous_apply
    {f : α -> β ->𝒄 γ} (hf : ωScottContinuous f) {g : α -> β} (hg : ωScottContinuous g) :
    ωScottContinuous fun x => f x (g x) := by
  apply ωScottContinuous.of_monotone_map_ωSup ⟨?_, fun c => ?_⟩
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
/--
Definition of `apply` / `apply` 的定义

English:
definition apply
  signature: : (α ->𝒄 β) × α ->𝒄 β
  body: ofFun (fun f => f.1 f.2)

中文:
定义 apply
  签名: : (α ->𝒄 β) × α ->𝒄 β
  定义体: ofFun (fun f => f.1 f.2)
-/
def apply : (α ->𝒄 β) × α ->𝒄 β := ofFun (fun f => f.1 f.2)

end Prod

/--
theorem `ωSup_apply_ωSup` / 定理 `ωSup_apply_ωSup`

English:
theorem ωSup_apply_ωSup
  given: (c₀ : Chain (α ->𝒄 β)) (c₁ : Chain α)
  proof: by simp [Prod.apply_apply, Prod.ωSup_zip]

中文:
定理 ωSup_apply_ωSup
  条件: (c₀ : Chain (α ->𝒄 β)) (c₁ : Chain α)
  证明: by simp [Prod.apply_apply, Prod.ωSup_zip]

Depends on / 依赖: Prod.apply_apply, apply_apply
-/
theorem ωSup_apply_ωSup (c₀ : Chain (α ->𝒄 β)) (c₁ : Chain α) :
    ωSup c₀ (ωSup c₁) = Prod.apply (ωSup (c₀.zip c₁)) := by simp [Prod.apply_apply, Prod.ωSup_zip]

/-- A family of continuous functions yields a continuous family of functions. -/
@[simps!]
/--
Definition of `flip` / `flip` 的定义

English:
definition flip
  signature: {α : Type*} (f : α -> β ->𝒄 γ)
  body: ofFun fun x y => f y x

中文:
定义 flip
  签名: {α : 类型} (f : α -> β ->𝒄 γ)
  定义体: ofFun fun x y => f y x
-/
def flip {α : Type*} (f : α -> β ->𝒄 γ) : β ->𝒄 α -> γ :=
  ofFun fun x y => f y x

/-- `Part.bind` as a continuous function. -/
@[simps! apply]
/--
Definition of `bind` / `bind` 的定义

English:
definition bind
  signature: {β γ : Type v} (f : α ->𝒄 Part β) (g : α ->𝒄 β -> Part γ)
  body: .mk (OrderHom.partBind f g.toOrderHom) fun c => by
    rw [ωSup_bind]; rw [← f.continuous]; rw [g.toOrderHom_eq_coe]; rw [← g.continuous]
    rfl

中文:
定义 bind
  签名: {β γ : 类型v} (f : α ->𝒄 Part β) (g : α ->𝒄 β -> Part γ)
  定义体: .mk (OrderHom.partBind f g.toOrderHom) fun c => by
    rw [ωSup_bind]; rw [← f.continuous]; rw [g.toOrderHom_eq_coe]; rw [← g.continuous]
    rfl

Depends on / 依赖: OrderHom, OrderHom.partBind, continuous, f.continuous, g.continuous, g.toOrderHom, g.toOrderHom_eq_coe, partBind, toOrderHom, toOrderHom_eq_coe
-/
noncomputable def bind {β γ : Type v} (f : α ->𝒄 Part β) (g : α ->𝒄 β -> Part γ) : α ->𝒄 Part γ :=
  .mk (OrderHom.partBind f g.toOrderHom) fun c => by
    rw [ωSup_bind]; rw [← f.continuous]; rw [g.toOrderHom_eq_coe]; rw [← g.continuous]
    rfl

/-- `Part.map` as a continuous function. -/
@[simps! apply]
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: {β γ : Type v} (f : β -> γ) (g : α ->𝒄 Part β)
  body: .copy (fun x => f <$> g x) (bind g (const (pure ∘ f))) by
    ext1
    simp only [map_eq_bind_pure_comp, bind, coe_mk, OrderHom.partBind_coe, coe_apply,
      coe_toOrderHom, const_apply, Part.bind_eq_bind]

中文:
定义 map
  签名: {β γ : 类型v} (f : β -> γ) (g : α ->𝒄 Part β)
  定义体: .copy (fun x => f <$> g x) (bind g (const (pure ∘ f))) by
    ext1
    simp only [map_eq_bind_pure_comp, bind, coe_mk, OrderHom.partBind_coe, coe_apply,
      coe_toOrderHom, const_apply, Part.bind_eq_bind]

Depends on / 依赖: OrderHom, OrderHom.partBind_coe, Part.bind_eq_bind, bind_eq_bind, coe_apply, coe_mk, coe_toOrderHom, const_apply, map_eq_bind_pure_comp, partBind_coe
-/
noncomputable def map {β γ : Type v} (f : β -> γ) (g : α ->𝒄 Part β) : α ->𝒄 Part γ :=
.copy (fun x => f <$> g x) (bind g (const (pure ∘ f))) by
    ext1
    simp only [map_eq_bind_pure_comp, bind, coe_mk, OrderHom.partBind_coe, coe_apply,
      coe_toOrderHom, const_apply, Part.bind_eq_bind]

/-- `Part.seq` as a continuous function. -/
@[simps! apply]
/--
Definition of `seq` / `seq` 的定义

English:
definition seq
  signature: {β γ : Type v} (f : α ->𝒄 Part (β -> γ)) (g : α ->𝒄 Part β)
  body: .copy (fun x => f x <*> g x) (bind f <| flip <| _root_.flip map g) by
      ext
      simp only [seq_eq_bind_map, Part.bind_eq_bind, Part.mem_bind_iff, flip_apply, _root_.flip,
        map_apply, bind_apply, Part.map_eq_map]

中文:
定义 seq
  签名: {β γ : 类型v} (f : α ->𝒄 Part (β -> γ)) (g : α ->𝒄 Part β)
  定义体: .copy (fun x => f x <*> g x) (bind f <| flip <| _root_.flip map g) by
      ext
      simp only [seq_eq_bind_map, Part.bind_eq_bind, Part.mem_bind_iff, flip_apply, _root_.flip,
        map_apply, bind_apply, Part.map_eq_map]

Depends on / 依赖: Part.bind_eq_bind, Part.map_eq_map, Part.mem_bind_iff, _root_, _root_.flip, bind_apply, bind_eq_bind, flip_apply, map_apply, map_eq_map, mem_bind_iff, seq_eq_bind_map
-/
noncomputable def seq {β γ : Type v} (f : α ->𝒄 Part (β -> γ)) (g : α ->𝒄 Part β) : α ->𝒄 Part γ :=
.copy (fun x => f x <*> g x) (bind f <| flip <| _root_.flip map g) by
      ext
      simp only [seq_eq_bind_map, Part.bind_eq_bind, Part.mem_bind_iff, flip_apply, _root_.flip,
        map_apply, bind_apply, Part.map_eq_map]

end ContinuousHom

namespace fixedPoints

open Function

/--
Definition of `iterateChain` / `iterateChain` 的定义

English:
definition iterateChain
  signature: (f : α ->o α) (x : α) (h : x <= f x)
  body: ⟨fun n => f^[n] x, f.monotone.monotone_iterate_of_le_map h⟩

中文:
定义 iterateChain
  签名: (f : α ->o α) (x : α) (h : x <= f x)
  定义体: ⟨fun n => f^[n] x, f.monotone.monotone_iterate_of_le_map h⟩

Depends on / 依赖: f.monotone.monotone_iterate_of_le_map, monotone, monotone_iterate_of_le_map
-/
def iterateChain (f : α ->o α) (x : α) (h : x <= f x) : Chain α :=
  ⟨fun n => f^[n] x, f.monotone.monotone_iterate_of_le_map h⟩

variable (f : α ->𝒄 α) (x : α)

/--
theorem `ωSup_iterate_mem_fixedPoint` / 定理 `ωSup_iterate_mem_fixedPoint`

English:
theorem ωSup_iterate_mem_fixedPoint
  given: (h : x <= f x)
  proof: by
  rw [mem_fixedPoints]; rw [IsFixedPt]; rw [f.continuous]
  apply le_antisymm
  · apply ωSup_le
    intro n
    simp only [Chain.coe_map, OrderHomClass.coe_coe, comp_apply]
    have : iterateChain f x h (n.succ) = f (iterateChain f x h n) :=
      Function.iterate_succ_apply' ..
    rw [← this]
 

中文:
定理 ωSup_iterate_mem_fixedPoint
  条件: (h : x <= f x)
  证明: by
  rw [mem_fixedPoints]; rw [IsFixedPt]; rw [f.continuous]
  apply le_antisymm
  · apply ωSup_le
    intro n
    simp only [Chain.coe_map, OrderHomClass.coe_coe, comp_apply]
    have : iterateChain f x h (n.succ) = f (iterateChain f x h n) :=
      Function.iterate_succ_apply' ..
    rw [← this]
 

Depends on / 依赖: Chain.coe_map, Function, Function.iterate_succ_apply, IsFixedPt, OrderHomClass, OrderHomClass.coe_coe, coe_coe, coe_map, comp_apply, continuous, f.continuous, iterateChain, iterate_succ_apply, le_antisymm, le_trans, mem_fixedPoints, n.succ
-/
theorem ωSup_iterate_mem_fixedPoint (h : x <= f x) :
    ωSup (iterateChain f x h) in fixedPoints f := by
  rw [mem_fixedPoints]; rw [IsFixedPt]; rw [f.continuous]
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
      change ((iterateChain f x h).map f) 0 <= ωSup ((iterateChain f x h).map (f : α ->o α))
      apply le_ωSup
    · have : iterateChain f x h (n.succ) = (iterateChain f x h).map f n :=
        Function.iterate_succ_apply' ..
      rw [this]
      apply le_ωSup

/--
theorem `ωSup_iterate_le_prefixedPoint` / 定理 `ωSup_iterate_le_prefixedPoint`

English:
theorem ωSup_iterate_le_prefixedPoint
  statement: (h : x <= f x) {a : α}
  proof: by
  apply ωSup_le
  intro n
  induction n with
  | zero => exact h_x_le_a
  | succ n h_ind =>
    have : iterateChain f x h (n.succ) = f (iterateChain f x h n) :=
      Function.iterate_succ_apply' ..
    rw [this]
    exact le_trans (f.monotone h_ind) h_a

中文:
定理 ωSup_iterate_le_prefixedPoint
  结论: (h : x <= f x) {a : α}
  证明: by
  apply ωSup_le
  intro n
  induction n with
  | zero => exact h_x_le_a
  | succ n h_ind =>
    have : iterateChain f x h (n.succ) = f (iterateChain f x h n) :=
      Function.iterate_succ_apply' ..
    rw [this]
    exact le_trans (f.monotone h_ind) h_a

Depends on / 依赖: Function, Function.iterate_succ_apply, f.monotone, h_ind, h_x_le_a, iterateChain, iterate_succ_apply, le_trans, monotone, n.succ
-/
theorem ωSup_iterate_le_prefixedPoint (h : x <= f x) {a : α}
    (h_a : f a <= a) (h_x_le_a : x <= a) :
    ωSup (iterateChain f x h) <= a := by
  apply ωSup_le
  intro n
  induction n with
  | zero => exact h_x_le_a
  | succ n h_ind =>
    have : iterateChain f x h (n.succ) = f (iterateChain f x h n) :=
      Function.iterate_succ_apply' ..
    rw [this]
    exact le_trans (f.monotone h_ind) h_a

/--
theorem `ωSup_iterate_le_fixedPoint` / 定理 `ωSup_iterate_le_fixedPoint`

English:
theorem ωSup_iterate_le_fixedPoint
  statement: (h : x <= f x) {a : α}
  proof: by
  rw [mem_fixedPoints] at h_a
  obtain h_a := Eq.le h_a
  exact ωSup_iterate_le_prefixedPoint f x h h_a h_x_le_a

中文:
定理 ωSup_iterate_le_fixedPoint
  结论: (h : x <= f x) {a : α}
  证明: by
  rw [mem_fixedPoints] at h_a
  obtain h_a := Eq.le h_a
  exact ωSup_iterate_le_prefixedPoint f x h h_a h_x_le_a

Depends on / 依赖: Eq.le, h_x_le_a, mem_fixedPoints
-/
theorem ωSup_iterate_le_fixedPoint (h : x <= f x) {a : α}
    (h_a : a in fixedPoints f) (h_x_le_a : x <= a) :
    ωSup (iterateChain f x h) <= a := by
  rw [mem_fixedPoints] at h_a
  obtain h_a := Eq.le h_a
  exact ωSup_iterate_le_prefixedPoint f x h h_a h_x_le_a

end fixedPoints

end OmegaCompletePartialOrder
