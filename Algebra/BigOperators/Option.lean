/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Data.Finset.Option
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Lemmas about products and sums over finite sets in `Option α`

In this file we prove formulas for products and sums over `Finset.insertNone s` and
`Finset.eraseNone s`.
-/

public section

open Function

namespace Finset

variable {α M : Type*} [CommMonoid M]

@[to_additive (attr := simp)]
/--
theorem `prod_insertNone` / 定理 `prod_insertNone`

English:
theorem prod_insertNone
  given: (f : Option α -> M) (s : Finset α)
  proof: by simp [insertNone]

@[to_additive]

中文:
定理 prod_insertNone
  条件: (f : Option α -> M) (s : Finset α)
  证明: by simp [insertNone]

@[to_additive]

Depends on / 依赖: insertNone
-/
theorem prod_insertNone (f : Option α -> M) (s : Finset α) :
    ∏ x in insertNone s, f x = f none * ∏ x in s, f (some x) := by simp [insertNone]

@[to_additive]
/--
theorem `mul_prod_eq_prod_insertNone` / 定理 `mul_prod_eq_prod_insertNone`

English:
theorem mul_prod_eq_prod_insertNone
  given: (f : α -> M) (x : M) (s : Finset α)
  proof: (prod_insertNone (fun i => i.elim x f) _).symm

@[to_additive]

中文:
定理 mul_prod_eq_prod_insertNone
  条件: (f : α -> M) (x : M) (s : Finset α)
  证明: (prod_insertNone (fun i => i.elim x f) _).symm

@[to_additive]

Depends on / 依赖: i.elim, prod_insertNone
-/
theorem mul_prod_eq_prod_insertNone (f : α -> M) (x : M) (s : Finset α) :
    x * ∏ i in s, f i = ∏ i in insertNone s, i.elim x f :=
  (prod_insertNone (fun i => i.elim x f) _).symm

@[to_additive]
/--
theorem `prod_eraseNone` / 定理 `prod_eraseNone`

English:
theorem prod_eraseNone
  given: (f : α -> M) (s : Finset (Option α))
  proof: by
  classical calc
      ∏ x in eraseNone s, f x = ∏ x in (eraseNone s).map Embedding.some, Option.elim' 1 f x :=
        (prod_map (eraseNone s) Embedding.some <| Option.elim' 1 f).symm
      _ = ∏ x in s.erase none, Option.elim' 1 f x := by rw [map_some_eraseNone]
      _ = ∏ x in s, Option.elim'

中文:
定理 prod_eraseNone
  条件: (f : α -> M) (s : Finset (Option α))
  证明: by
  classical calc
      ∏ x in eraseNone s, f x = ∏ x in (eraseNone s).map Embedding.some, Option.elim' 1 f x :=
        (prod_map (eraseNone s) Embedding.some <| Option.elim' 1 f).symm
      _ = ∏ x in s.erase none, Option.elim' 1 f x := by rw [map_some_eraseNone]
      _ = ∏ x in s, Option.elim'

Depends on / 依赖: Embedding, Embedding.some, Option.elim, classical, eraseNone, map_some_eraseNone, prod_erase, prod_map, s.erase
-/
theorem prod_eraseNone (f : α -> M) (s : Finset (Option α)) :
    ∏ x in eraseNone s, f x = ∏ x in s, Option.elim' 1 f x := by
  classical calc
      ∏ x in eraseNone s, f x = ∏ x in (eraseNone s).map Embedding.some, Option.elim' 1 f x :=
        (prod_map (eraseNone s) Embedding.some <| Option.elim' 1 f).symm
      _ = ∏ x in s.erase none, Option.elim' 1 f x := by rw [map_some_eraseNone]
      _ = ∏ x in s, Option.elim' 1 f x := prod_erase _ rfl

end Finset
