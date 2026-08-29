/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Order.Fin.Tuple
public import Mathlib.Order.Hom.Set
public import Mathlib.Data.Finset.Insert

/-!
# Order isomorphisms from Fin to finsets

We define order isomorphisms like `Fin.orderIsoTriple` from `Fin 3`
to the finset `{a, b, c}` when `a < b` and `b < c`.

## Future works

* Do the same for `Set` without too much duplication of code (TODO)
* Provide a definition which would take as an input an order
  isomorphism `e : Fin (n + 1) ≃o s` (with `s : Set α` (or `Finset α`)) and
  extend it to an order isomorphism `Fin (n + 2) ≃o Finset.insert i s` when `i < e 0` (TODO).

-/

@[expose] public section

namespace Fin

variable {α : Type*} [Preorder α]

/--
Definition of `orderIsoSingleton` / `orderIsoSingleton` 的定义

English:
definition orderIsoSingleton
  signature: (a : α)
  body: OrderIso.ofUnique _ _

@[simp]

中文:
定义 orderIsoSingleton
  签名: (a : α)
  定义体: OrderIso.ofUnique _ _

@[simp]

Depends on / 依赖: OrderIso, OrderIso.ofUnique, ofUnique
-/
noncomputable def orderIsoSingleton (a : α) :
    Fin 1 ≃o ({a} : Finset α) :=
  OrderIso.ofUnique _ _

@[simp]
/--
lemma `orderIsoSingleton_apply` / 引理 `orderIsoSingleton_apply`

English:
lemma orderIsoSingleton_apply
  given: (a : α) (i : Fin 1)
  proof: rfl

中文:
引理 orderIsoSingleton_apply
  条件: (a : α) (i : 有限集 1)
  证明: rfl
-/
lemma orderIsoSingleton_apply (a : α) (i : Fin 1) :
    orderIsoSingleton a i = a := rfl

variable [DecidableEq α]

section

variable (a b : α) (hab : a < b)

/--
Definition of `orderIsoPair` / `orderIsoPair` 的定义

English:
definition orderIsoPair
  signature: :
  body: StrictMono.orderIsoOfSurjective ![⟨a, by simp⟩, ⟨b, by simp⟩]
    (strictMono_vecEmpty.vecCons hab) (fun ⟨x, hx⟩ => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      obtain rfl | rfl := hx
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩)

中文:
定义 orderIsoPair
  签名: :
  定义体: StrictMono.orderIsoOfSurjective ![⟨a, by simp⟩, ⟨b, by simp⟩]
    (strictMono_vecEmpty.vecCons hab) (fun ⟨x, hx⟩ => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      obtain rfl | rfl := hx
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩)

Depends on / 依赖: Finset, Finset.mem_insert, Finset.mem_singleton, StrictMono, StrictMono.orderIsoOfSurjective, mem_insert, mem_singleton, orderIsoOfSurjective, strictMono_vecEmpty, strictMono_vecEmpty.vecCons, vecCons
-/
noncomputable def orderIsoPair :
    Fin 2 ≃o ({a, b} : Finset α) :=
  StrictMono.orderIsoOfSurjective ![⟨a, by simp⟩, ⟨b, by simp⟩]
    (strictMono_vecEmpty.vecCons hab) (fun ⟨x, hx⟩ => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      obtain rfl | rfl := hx
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩)

/--
lemma `orderIsoPair_zero` / 引理 `orderIsoPair_zero`

English:
lemma orderIsoPair_zero
  statement: orderIsoPair a b hab 0 = a
  proof: rfl

中文:
引理 orderIsoPair_zero
  结论: orderIsoPair a b hab 0 = a
  证明: rfl
-/
@[simp] lemma orderIsoPair_zero : orderIsoPair a b hab 0 = a := rfl
/--
lemma `orderIsoPair_one` / 引理 `orderIsoPair_one`

English:
lemma orderIsoPair_one
  statement: orderIsoPair a b hab 1 = b
  proof: rfl

中文:
引理 orderIsoPair_one
  结论: orderIsoPair a b hab 1 = b
  证明: rfl
-/
@[simp] lemma orderIsoPair_one : orderIsoPair a b hab 1 = b := rfl

end

section

variable (a b c : α) (hab : a < b) (hbc : b < c)

/--
Definition of `orderIsoTriple` / `orderIsoTriple` 的定义

English:
definition orderIsoTriple
  signature: :
  body: StrictMono.orderIsoOfSurjective ![⟨a, by simp⟩, ⟨b, by simp⟩, ⟨c, by simp⟩]
    (StrictMono.vecCons (strictMono_vecEmpty.vecCons hbc) hab) (fun ⟨x, hx⟩ => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      obtain rfl | rfl | rfl := hx
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩)

中文:
定义 orderIsoTriple
  签名: :
  定义体: StrictMono.orderIsoOfSurjective ![⟨a, by simp⟩, ⟨b, by simp⟩, ⟨c, by simp⟩]
    (StrictMono.vecCons (strictMono_vecEmpty.vecCons hbc) hab) (fun ⟨x, hx⟩ => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      obtain rfl | rfl | rfl := hx
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩)

Depends on / 依赖: Finset, Finset.mem_insert, Finset.mem_singleton, StrictMono, StrictMono.orderIsoOfSurjective, StrictMono.vecCons, mem_insert, mem_singleton, orderIsoOfSurjective, strictMono_vecEmpty, strictMono_vecEmpty.vecCons, vecCons
-/
noncomputable def orderIsoTriple :
    Fin 3 ≃o ({a, b, c} : Finset α) :=
  StrictMono.orderIsoOfSurjective ![⟨a, by simp⟩, ⟨b, by simp⟩, ⟨c, by simp⟩]
    (StrictMono.vecCons (strictMono_vecEmpty.vecCons hbc) hab) (fun ⟨x, hx⟩ => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      obtain rfl | rfl | rfl := hx
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩)

/--
lemma `orderIsoTriple_zero` / 引理 `orderIsoTriple_zero`

English:
lemma orderIsoTriple_zero
  statement: orderIsoTriple a b c hab hbc 0 = a
  proof: rfl

中文:
引理 orderIsoTriple_zero
  结论: orderIsoTriple a b c hab hbc 0 = a
  证明: rfl
-/
@[simp] lemma orderIsoTriple_zero : orderIsoTriple a b c hab hbc 0 = a := rfl
/--
lemma `orderIsoTriple_one` / 引理 `orderIsoTriple_one`

English:
lemma orderIsoTriple_one
  statement: orderIsoTriple a b c hab hbc 1 = b
  proof: rfl

中文:
引理 orderIsoTriple_one
  结论: orderIsoTriple a b c hab hbc 1 = b
  证明: rfl
-/
@[simp] lemma orderIsoTriple_one : orderIsoTriple a b c hab hbc 1 = b := rfl
/--
lemma `orderIsoTriple_two` / 引理 `orderIsoTriple_two`

English:
lemma orderIsoTriple_two
  statement: orderIsoTriple a b c hab hbc 2 = c
  proof: rfl

中文:
引理 orderIsoTriple_two
  结论: orderIsoTriple a b c hab hbc 2 = c
  证明: rfl
-/
@[simp] lemma orderIsoTriple_two : orderIsoTriple a b c hab hbc 2 = c := rfl

end

end Fin
