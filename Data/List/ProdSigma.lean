/-
Copyright (c) 2015 Leonardo de Moura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
module

public import Mathlib.Data.List.Defs
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Common

/-!
# Lists in product and sigma types

This file proves basic properties of `List.product` and `List.sigma`, which are list constructions
living in `Prod` and `Sigma` types respectively. Their definitions can be found in
[`Data.List.Defs`](./defs). Beware, this is not about `List.prod`, the multiplicative product.
-/

public section


variable {α β : Type*}

namespace List

/-! ### product -/


@[simp]
/--
theorem `nil_product` / 定理 `nil_product`

English:
theorem nil_product
  given: (l : List β)
  statement: (@nil α) ×ˢ l = []
  proof: rfl

@[simp]

中文:
定理 nil_product
  条件: (l : List β)
  结论: (@nil α) ×ˢ l = []
  证明: rfl

@[simp]
-/
theorem nil_product (l : List β) : (@nil α) ×ˢ l = [] :=
  rfl

@[simp]
/--
theorem `product_cons` / 定理 `product_cons`

English:
theorem product_cons
  given: (a : α) (l₁ : List α) (l₂ : List β)
  proof: rfl

@[simp]

中文:
定理 product_cons
  条件: (a : α) (l₁ : List α) (l₂ : List β)
  证明: rfl

@[simp]
-/
theorem product_cons (a : α) (l₁ : List α) (l₂ : List β) :
    (a :: l₁) ×ˢ l₂ = map (fun b => (a, b)) l₂ ++ (l₁ ×ˢ l₂) :=
  rfl

@[simp]
/--
theorem `product_nil` / 定理 `product_nil`

English:
theorem product_nil
  statement: forall l : List α, l ×ˢ (@nil β) = []

中文:
定理 product_nil
  结论: 对任意 l : List α, l ×ˢ (@nil β) = []
-/
theorem product_nil : forall l : List α, l ×ˢ (@nil β) = []
  | [] => rfl
  | _ :: l => by simp [product_cons, product_nil l]

@[simp]
/--
theorem `mem_product` / 定理 `mem_product`

English:
theorem mem_product
  given: {l₁ : List α} {l₂ : List β} {a : α} {b : β}
  proof: by
  simp_all [SProd.sprod, product, mem_flatMap, mem_map, Prod.ext_iff, and_left_comm]

中文:
定理 mem_product
  条件: {l₁ : List α} {l₂ : List β} {a : α} {b : β}
  证明: by
  simp_all [SProd.sprod, product, mem_flatMap, mem_map, Prod.ext_iff, and_left_comm]

Depends on / 依赖: Prod.ext_iff, SProd.sprod, and_left_comm, ext_iff, mem_flatMap, mem_map, product
-/
theorem mem_product {l₁ : List α} {l₂ : List β} {a : α} {b : β} :
    (a, b) in l₁ ×ˢ l₂ ↔ a in l₁ ∧ b in l₂ := by
  simp_all [SProd.sprod, product, mem_flatMap, mem_map, Prod.ext_iff, and_left_comm]

/--
theorem `length_product` / 定理 `length_product`

English:
theorem length_product
  given: (l₁ : List α) (l₂ : List β)
  proof: by
  induction l₁ with
  | nil => exact (Nat.zero_mul _).symm
  | cons x l₁ IH =>
    simp only [length, product_cons, length_append, IH, Nat.add_mul, Nat.one_mul, length_map,
      Nat.add_comm]

中文:
定理 length_product
  条件: (l₁ : List α) (l₂ : List β)
  证明: by
  induction l₁ with
  | nil => exact (Nat.zero_mul _).symm
  | cons x l₁ IH =>
    simp only [length, product_cons, length_append, IH, Nat.add_mul, Nat.one_mul, length_map,
      Nat.add_comm]

Depends on / 依赖: Nat.add_comm, Nat.add_mul, Nat.one_mul, Nat.zero_mul, add_comm, add_mul, length, length_append, length_map, one_mul, product_cons, zero_mul
-/
theorem length_product (l₁ : List α) (l₂ : List β) :
    length (l₁ ×ˢ l₂) = length l₁ * length l₂ := by
  induction l₁ with
  | nil => exact (Nat.zero_mul _).symm
  | cons x l₁ IH =>
    simp only [length, product_cons, length_append, IH, Nat.add_mul, Nat.one_mul, length_map,
      Nat.add_comm]

/-! ### sigma -/


variable {σ : α -> Type*}

@[simp]
/--
theorem `nil_sigma` / 定理 `nil_sigma`

English:
theorem nil_sigma
  given: (l : forall a, List (σ a))
  statement: (@nil α).sigma l = []
  proof: rfl

@[simp]

中文:
定理 nil_sigma
  条件: (l : 对任意 a, List (σ a))
  结论: (@nil α).sigma l = []
  证明: rfl

@[simp]
-/
theorem nil_sigma (l : forall a, List (σ a)) : (@nil α).sigma l = [] :=
  rfl

@[simp]
/--
theorem `sigma_cons` / 定理 `sigma_cons`

English:
theorem sigma_cons
  given: (a : α) (l₁ : List α) (l₂ : forall a, List (σ a))
  proof: rfl

@[simp]

中文:
定理 sigma_cons
  条件: (a : α) (l₁ : List α) (l₂ : 对任意 a, List (σ a))
  证明: rfl

@[simp]
-/
theorem sigma_cons (a : α) (l₁ : List α) (l₂ : forall a, List (σ a)) :
    (a :: l₁).sigma l₂ = map (Sigma.mk a) (l₂ a) ++ l₁.sigma l₂ :=
  rfl

@[simp]
/--
theorem `sigma_nil` / 定理 `sigma_nil`

English:
theorem sigma_nil
  statement: forall l : List α, (l.sigma fun a => @nil (σ a)) = []

中文:
定理 sigma_nil
  结论: 对任意 l : List α, (l.sigma fun a => @nil (σ a)) = []
-/
theorem sigma_nil : forall l : List α, (l.sigma fun a => @nil (σ a)) = []
  | [] => rfl
  | _ :: l => by simp [sigma_cons, sigma_nil l]

@[simp]
/--
theorem `mem_sigma` / 定理 `mem_sigma`

English:
theorem mem_sigma
  given: {l₁ : List α} {l₂ : forall a, List (σ a)} {a : α} {b : σ a}
  proof: by
  simp [List.sigma, mem_flatMap, mem_map, exists_and_left, and_left_comm,
    exists_eq_left, exists_eq_right]

中文:
定理 mem_sigma
  条件: {l₁ : List α} {l₂ : 对任意 a, List (σ a)} {a : α} {b : σ a}
  证明: by
  simp [List.sigma, mem_flatMap, mem_map, exists_and_left, and_left_comm,
    exists_eq_left, exists_eq_right]

Depends on / 依赖: List.sigma, and_left_comm, exists_and_left, exists_eq_left, exists_eq_right, mem_flatMap, mem_map
-/
theorem mem_sigma {l₁ : List α} {l₂ : forall a, List (σ a)} {a : α} {b : σ a} :
    Sigma.mk a b in l₁.sigma l₂ ↔ a in l₁ ∧ b in l₂ a := by
  simp [List.sigma, mem_flatMap, mem_map, exists_and_left, and_left_comm,
    exists_eq_left, exists_eq_right]

/-! ### Miscellaneous lemmas -/

@[simp 1100]
/--
theorem `mem_map_swap` / 定理 `mem_map_swap`

English:
theorem mem_map_swap
  given: (x : α) (y : β) (xs : List (α × β))
  proof: by
  simp

中文:
定理 mem_map_swap
  条件: (x : α) (y : β) (xs : List (α × β))
  证明: by
  simp
-/
theorem mem_map_swap (x : α) (y : β) (xs : List (α × β)) :
    (y, x) in map Prod.swap xs ↔ (x, y) in xs := by
  simp

end List
