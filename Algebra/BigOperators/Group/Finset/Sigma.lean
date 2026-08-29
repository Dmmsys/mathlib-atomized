/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Data.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Product and sums indexed by finite sets in sigma types.

-/

public section

variable {ι κ α β γ : Type*}

open Fin Function

variable {s s₁ s₂ : Finset α} {a : α} {f g : α -> β}

namespace Finset

section CommMonoid

variable [CommMonoid β]

/-- The product over a sigma type equals the product of the fiberwise products.
For rewriting in the reverse direction, use `Finset.prod_sigma'`.

See also `Fintype.prod_sigma` for the product over the whole type. -/
@[to_additive /-- The sum over a sigma type equals the sum of the fiberwise sums. For rewriting
in the reverse direction, use `Finset.sum_sigma'`.

See also `Fintype.sum_sigma` for the sum over the whole type. -/]
/--
theorem `prod_sigma` / 定理 `prod_sigma`

English:
theorem prod_sigma
  given: {σ : α -> Type*} (s : Finset α) (t : forall a, Finset (σ a)) (f : Sigma σ -> β)
  proof: by
  simp_rw [← disjiUnion_map_sigma_mk, prod_disjiUnion, prod_map, Function.Embedding.sigmaMk_apply]

中文:
定理 prod_sigma
  条件: {σ : α -> 类型} (s : Finset α) (t : 对任意 a, Finset (σ a)) (f : Sigma σ -> β)
  证明: by
  simp_rw [← disjiUnion_map_sigma_mk, prod_disjiUnion, prod_map, Function.Embedding.sigmaMk_apply]

Depends on / 依赖: Embedding, Function, Function.Embedding.sigmaMk_apply, disjiUnion_map_sigma_mk, prod_disjiUnion, prod_map, sigmaMk_apply, simp_rw
-/
theorem prod_sigma {σ : α -> Type*} (s : Finset α) (t : forall a, Finset (σ a)) (f : Sigma σ -> β) :
    ∏ x in s.sigma t, f x = ∏ a in s, ∏ s in t a, f ⟨a, s⟩ := by
  simp_rw [← disjiUnion_map_sigma_mk, prod_disjiUnion, prod_map, Function.Embedding.sigmaMk_apply]

/-- The product over a sigma type equals the product of the fiberwise products. For rewriting
in the reverse direction, use `Finset.prod_sigma`. -/
@[to_additive /-- The sum over a sigma type equals the sum of the fiberwise sums. For rewriting
in the reverse direction, use `Finset.sum_sigma` -/]
/--
theorem `prod_sigma'` / 定理 `prod_sigma'`

English:
theorem prod_sigma'
  given: {σ : α -> Type*} (s : Finset α) (t : forall a, Finset (σ a)) (f : forall a, σ a -> β)
  proof: Eq.symm prod_sigma s t fun x => f x.1 x.2

@[to_additive]

中文:
定理 prod_sigma'
  条件: {σ : α -> 类型} (s : Finset α) (t : 对任意 a, Finset (σ a)) (f : 对任意 a, σ a -> β)
  证明: Eq.symm prod_sigma s t fun x => f x.1 x.2

@[to_additive]

Depends on / 依赖: Eq.symm, prod_sigma
-/
theorem prod_sigma' {σ : α -> Type*} (s : Finset α) (t : forall a, Finset (σ a)) (f : forall a, σ a -> β) :
    (∏ a in s, ∏ s in t a, f a s) = ∏ x in s.sigma t, f x.1 x.2 :=
Eq.symm prod_sigma s t fun x => f x.1 x.2

@[to_additive]
/--
theorem `prod_finset_product` / 定理 `prod_finset_product`

English:
theorem prod_finset_product
  statement: (r : Finset (γ × α)) (s : Finset γ) (t : γ -> Finset α)
  proof: by
  refine Eq.trans ?_ (prod_sigma s t fun p => f (p.1, p.2))
  apply prod_equiv (Equiv.sigmaEquivProd _ _).symm <;> simp [h]

@[to_additive]

中文:
定理 prod_finset_product
  结论: (r : Finset (γ × α)) (s : Finset γ) (t : γ -> Finset α)
  证明: by
  refine Eq.trans ?_ (prod_sigma s t fun p => f (p.1, p.2))
  apply prod_equiv (Equiv.sigmaEquivProd _ _).symm <;> simp [h]

@[to_additive]

Depends on / 依赖: Eq.trans, Equiv.sigmaEquivProd, prod_equiv, prod_sigma, sigmaEquivProd
-/
theorem prod_finset_product (r : Finset (γ × α)) (s : Finset γ) (t : γ -> Finset α)
    (h : forall p : γ × α, p in r ↔ p.1 in s ∧ p.2 in t p.1) {f : γ × α -> β} :
    ∏ p in r, f p = ∏ c in s, ∏ a in t c, f (c, a) := by
  refine Eq.trans ?_ (prod_sigma s t fun p => f (p.1, p.2))
  apply prod_equiv (Equiv.sigmaEquivProd _ _).symm <;> simp [h]

@[to_additive]
/--
theorem `prod_finset_product'` / 定理 `prod_finset_product'`

English:
theorem prod_finset_product'
  statement: (r : Finset (γ × α)) (s : Finset γ) (t : γ -> Finset α)
  proof: prod_finset_product r s t h

@[to_additive]

中文:
定理 prod_finset_product'
  结论: (r : Finset (γ × α)) (s : Finset γ) (t : γ -> Finset α)
  证明: prod_finset_product r s t h

@[to_additive]

Depends on / 依赖: prod_finset_product
-/
theorem prod_finset_product' (r : Finset (γ × α)) (s : Finset γ) (t : γ -> Finset α)
    (h : forall p : γ × α, p in r ↔ p.1 in s ∧ p.2 in t p.1) {f : γ -> α -> β} :
    ∏ p in r, f p.1 p.2 = ∏ c in s, ∏ a in t c, f c a :=
  prod_finset_product r s t h

@[to_additive]
/--
theorem `prod_finset_product_right` / 定理 `prod_finset_product_right`

English:
theorem prod_finset_product_right
  statement: (r : Finset (α × γ)) (s : Finset γ) (t : γ -> Finset α)
  proof: by
  refine Eq.trans ?_ (prod_sigma s t fun p => f (p.2, p.1))
  apply prod_equiv ((Equiv.prodComm _ _).trans (Equiv.sigmaEquivProd _ _).symm) <;> simp [h]

@[to_additive]

中文:
定理 prod_finset_product_right
  结论: (r : Finset (α × γ)) (s : Finset γ) (t : γ -> Finset α)
  证明: by
  refine Eq.trans ?_ (prod_sigma s t fun p => f (p.2, p.1))
  apply prod_equiv ((Equiv.prodComm _ _).trans (Equiv.sigmaEquivProd _ _).symm) <;> simp [h]

@[to_additive]

Depends on / 依赖: Eq.trans, Equiv.prodComm, Equiv.sigmaEquivProd, prodComm, prod_equiv, prod_sigma, sigmaEquivProd
-/
theorem prod_finset_product_right (r : Finset (α × γ)) (s : Finset γ) (t : γ -> Finset α)
    (h : forall p : α × γ, p in r ↔ p.2 in s ∧ p.1 in t p.2) {f : α × γ -> β} :
    ∏ p in r, f p = ∏ c in s, ∏ a in t c, f (a, c) := by
  refine Eq.trans ?_ (prod_sigma s t fun p => f (p.2, p.1))
  apply prod_equiv ((Equiv.prodComm _ _).trans (Equiv.sigmaEquivProd _ _).symm) <;> simp [h]

@[to_additive]
/--
theorem `prod_finset_product_right'` / 定理 `prod_finset_product_right'`

English:
theorem prod_finset_product_right'
  statement: (r : Finset (α × γ)) (s : Finset γ) (t : γ -> Finset α)
  proof: prod_finset_product_right r s t h

中文:
定理 prod_finset_product_right'
  结论: (r : Finset (α × γ)) (s : Finset γ) (t : γ -> Finset α)
  证明: prod_finset_product_right r s t h

Depends on / 依赖: prod_finset_product_right
-/
theorem prod_finset_product_right' (r : Finset (α × γ)) (s : Finset γ) (t : γ -> Finset α)
    (h : forall p : α × γ, p in r ↔ p.2 in s ∧ p.1 in t p.2) {f : α -> γ -> β} :
    ∏ p in r, f p.1 p.2 = ∏ c in s, ∏ a in t c, f a c :=
  prod_finset_product_right r s t h

/-- The product over a product set equals the product of the fiberwise products. For rewriting
in the reverse direction, use `Finset.prod_product'`. -/
@[to_additive /-- The sum over a product set equals the sum of the fiberwise sums. For rewriting
in the reverse direction, use `Finset.sum_product'` -/]
/--
theorem `prod_product` / 定理 `prod_product`

English:
theorem prod_product
  given: (s : Finset γ) (t : Finset α) (f : γ × α -> β)
  proof: prod_finset_product (s ×ˢ t) s (fun _a => t) fun _p => mem_product

中文:
定理 prod_product
  条件: (s : Finset γ) (t : Finset α) (f : γ × α -> β)
  证明: prod_finset_product (s ×ˢ t) s (fun _a => t) fun _p => mem_product

Depends on / 依赖: mem_product, prod_finset_product
-/
theorem prod_product (s : Finset γ) (t : Finset α) (f : γ × α -> β) :
    ∏ x in s ×ˢ t, f x = ∏ x in s, ∏ y in t, f (x, y) :=
  prod_finset_product (s ×ˢ t) s (fun _a => t) fun _p => mem_product

/-- The product over a product set equals the product of the fiberwise products. For rewriting
in the reverse direction, use `Finset.prod_product`. -/
@[to_additive /-- The sum over a product set equals the sum of the fiberwise sums. For rewriting
in the reverse direction, use `Finset.sum_product` -/]
/--
theorem `prod_product'` / 定理 `prod_product'`

English:
theorem prod_product'
  given: (s : Finset γ) (t : Finset α) (f : γ -> α -> β)
  proof: prod_product ..

@[to_additive]

中文:
定理 prod_product'
  条件: (s : Finset γ) (t : Finset α) (f : γ -> α -> β)
  证明: prod_product ..

@[to_additive]

Depends on / 依赖: prod_product
-/
theorem prod_product' (s : Finset γ) (t : Finset α) (f : γ -> α -> β) :
    ∏ x in s ×ˢ t, f x.1 x.2 = ∏ x in s, ∏ y in t, f x y :=
  prod_product ..

@[to_additive]
/--
theorem `prod_product_right` / 定理 `prod_product_right`

English:
theorem prod_product_right
  given: (s : Finset γ) (t : Finset α) (f : γ × α -> β)
  proof: prod_finset_product_right (s ×ˢ t) t (fun _a => s) fun _p => mem_product.trans and_comm

中文:
定理 prod_product_right
  条件: (s : Finset γ) (t : Finset α) (f : γ × α -> β)
  证明: prod_finset_product_right (s ×ˢ t) t (fun _a => s) fun _p => mem_product.trans and_comm

Depends on / 依赖: and_comm, mem_product, mem_product.trans, prod_finset_product_right
-/
theorem prod_product_right (s : Finset γ) (t : Finset α) (f : γ × α -> β) :
    ∏ x in s ×ˢ t, f x = ∏ y in t, ∏ x in s, f (x, y) :=
  prod_finset_product_right (s ×ˢ t) t (fun _a => s) fun _p => mem_product.trans and_comm

/-- An uncurried version of `Finset.prod_product_right`. -/
@[to_additive /-- An uncurried version of `Finset.sum_product_right` -/]
/--
theorem `prod_product_right'` / 定理 `prod_product_right'`

English:
theorem prod_product_right'
  given: (s : Finset γ) (t : Finset α) (f : γ -> α -> β)
  proof: prod_product_right ..

中文:
定理 prod_product_right'
  条件: (s : Finset γ) (t : Finset α) (f : γ -> α -> β)
  证明: prod_product_right ..

Depends on / 依赖: prod_product_right
-/
theorem prod_product_right' (s : Finset γ) (t : Finset α) (f : γ -> α -> β) :
    ∏ x in s ×ˢ t, f x.1 x.2 = ∏ y in t, ∏ x in s, f x y :=
  prod_product_right ..

/-- Generalization of `Finset.prod_comm` to the case when the inner `Finset`s depend on the outer
variable. -/
@[to_additive /-- Generalization of `Finset.sum_comm` to the case when the inner `Finset`s depend on
the outer variable. -/]
/--
theorem `prod_comm'` / 定理 `prod_comm'`

English:
theorem prod_comm'
  statement: {s : Finset γ} {t : γ -> Finset α} {t' : Finset α} {s' : α -> Finset γ}
  proof: by
  classical
    have : forall z : γ × α, (z in s.biUnion fun x => (t x).map <| Function.Embedding.sectR x _) ↔
      z.1 in s ∧ z.2 in t z.1 := by
      rintro ⟨x, y⟩
      simp only [mem_biUnion, mem_map, Function.Embedding.sectR_apply, Prod.mk.injEq,
        exists_eq_right, ← and_assoc]
    ex

中文:
定理 prod_comm'
  结论: {s : Finset γ} {t : γ -> Finset α} {t' : Finset α} {s' : α -> Finset γ}
  证明: by
  classical
    have : forall z : γ × α, (z in s.biUnion fun x => (t x).map <| Function.Embedding.sectR x _) ↔
      z.1 in s ∧ z.2 in t z.1 := by
      rintro ⟨x, y⟩
      simp only [mem_biUnion, mem_map, Function.Embedding.sectR_apply, Prod.mk.injEq,
        exists_eq_right, ← and_assoc]
    ex

Depends on / 依赖: Embedding, Function, Function.Embedding.sectR, Function.Embedding.sectR_apply, Prod.mk.injEq, and_assoc, and_comm, biUnion, classical, exists_eq_right, mem_biUnion, mem_map, prod_finset_product, prod_finset_product_right, s.biUnion, sectR_apply, symm.trans
-/
theorem prod_comm' {s : Finset γ} {t : γ -> Finset α} {t' : Finset α} {s' : α -> Finset γ}
    (h : forall x y, x in s ∧ y in t x ↔ x in s' y ∧ y in t') {f : γ -> α -> β} :
    (∏ x in s, ∏ y in t x, f x y) = ∏ y in t', ∏ x in s' y, f x y := by
  classical
    have : forall z : γ × α, (z in s.biUnion fun x => (t x).map <| Function.Embedding.sectR x _) ↔
      z.1 in s ∧ z.2 in t z.1 := by
      rintro ⟨x, y⟩
      simp only [mem_biUnion, mem_map, Function.Embedding.sectR_apply, Prod.mk.injEq,
        exists_eq_right, ← and_assoc]
    exact
      (prod_finset_product' _ _ _ this).symm.trans
        ((prod_finset_product_right' _ _ _) fun ⟨x, y⟩ => (this _).trans ((h x y).trans and_comm))

@[to_additive]
/--
theorem `prod_comm` / 定理 `prod_comm`

English:
theorem prod_comm
  given: {s : Finset γ} {t : Finset α} {f : γ -> α -> β}
  proof: prod_comm' fun _ _ => Iff.rfl

中文:
定理 prod_comm
  条件: {s : Finset γ} {t : Finset α} {f : γ -> α -> β}
  证明: prod_comm' fun _ _ => Iff.rfl

Depends on / 依赖: Iff.rfl, prod_comm
-/
theorem prod_comm {s : Finset γ} {t : Finset α} {f : γ -> α -> β} :
    (∏ x in s, ∏ y in t, f x y) = ∏ y in t, ∏ x in s, f x y :=
  prod_comm' fun _ _ => Iff.rfl

/-- Cyclically permute 3 nested instances of `Finset.prod`. -/
@[to_additive]
/--
theorem `prod_comm_cycle` / 定理 `prod_comm_cycle`

English:
theorem prod_comm_cycle
  given: {s : Finset γ} {t : Finset α} {u : Finset κ} {f : γ -> α -> κ -> β}
  proof: by
  simp_rw [prod_comm (s := t), prod_comm (s := s)]

中文:
定理 prod_comm_cycle
  条件: {s : Finset γ} {t : Finset α} {u : Finset κ} {f : γ -> α -> κ -> β}
  证明: by
  simp_rw [prod_comm (s := t), prod_comm (s := s)]

Depends on / 依赖: prod_comm, simp_rw
-/
theorem prod_comm_cycle {s : Finset γ} {t : Finset α} {u : Finset κ} {f : γ -> α -> κ -> β} :
    (∏ x in s, ∏ y in t, ∏ z in u, f x y z) = ∏ z in u, ∏ x in s, ∏ y in t, f x y z := by
  simp_rw [prod_comm (s := t), prod_comm (s := s)]

end CommMonoid

@[simp]
/--
theorem `card_sigma` / 定理 `card_sigma`

English:
theorem card_sigma
  given: {σ : α -> Type*} (s : Finset α) (t : forall a, Finset (σ a))
  proof: Multiset.card_sigma _ _

中文:
定理 card_sigma
  条件: {σ : α -> 类型} (s : Finset α) (t : 对任意 a, Finset (σ a))
  证明: Multiset.card_sigma _ _

Depends on / 依赖: Multiset, Multiset.card_sigma, card_sigma
-/
theorem card_sigma {σ : α -> Type*} (s : Finset α) (t : forall a, Finset (σ a)) :
    #(s.sigma t) = ∑ a in s, #(t a) :=
  Multiset.card_sigma _ _

end Finset
