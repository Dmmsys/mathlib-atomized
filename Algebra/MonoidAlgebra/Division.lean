/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.Group.Hom.End
public import Mathlib.Algebra.MonoidAlgebra.Defs

/-!
# Division of `AddMonoidAlgebra` by monomials

This file is most important for when `G = ℕ` (polynomials) or `G = σ →₀ ℕ` (multivariate
polynomials).

In order to apply in maximal generality (such as for `LaurentPolynomial`s), this uses
`∃ d, g' = g + d` in many places instead of `g ≤ g'`.

## Main definitions

* `AddMonoidAlgebra.divOf x g`: divides `x` by the monomial `AddMonoidAlgebra.of k G g`
* `AddMonoidAlgebra.modOf x g`: the remainder upon dividing `x` by the monomial
  `AddMonoidAlgebra.of k G g`.

## Main results

* `AddMonoidAlgebra.divOf_add_modOf`, `AddMonoidAlgebra.modOf_add_divOf`: `divOf` and
  `modOf` are well-behaved as quotient and remainder operators.

## Implementation notes

`∃ d, g' = g + d` is used as opposed to some other permutation up to commutativity in order to match
the definition of `semigroupDvd`. The results in this file could be duplicated for
`MonoidAlgebra` by using `g ∣ g'`, but this can't be done automatically, and in any case is not
likely to be very useful.

-/

@[expose] public section


variable {k G : Type*} [Semiring k]

namespace AddMonoidAlgebra

section

variable [AddCommMonoid G]

/--
Definition of `divOf` / `divOf` 的定义

English:
definition divOf
  signature: [IsCancelAdd G] (x : k[G]) (g : G)
  body: x.coeff.comapDomain (g + ·) (add_right_injective g).injOn

local infixl:70 " /ᵒᶠ " => divOf

中文:
定义 divOf
  签名: [IsCancelAdd G] (x : k[G]) (g : G)
  定义体: x.coeff.comapDomain (g + ·) (add_right_injective g).injOn

local infixl:70 " /ᵒᶠ " => divOf

Depends on / 依赖: add_right_injective, comapDomain, x.coeff.comapDomain
-/
noncomputable def divOf [IsCancelAdd G] (x : k[G]) (g : G) : k[G] where
  -- note: comapping by `+ g` has the effect of subtracting `g` from every element in
  -- the support, and discarding the elements of the support from which `g` can't be subtracted.
  -- If `G` is an additive group, such as `ℤ` when used for `LaurentPolynomial`,
  -- then no discarding occurs.
  coeff := x.coeff.comapDomain (g + ·) (add_right_injective g).injOn

local infixl:70 " /ᵒᶠ " => divOf

section divOf
variable [IsCancelAdd G]

/--
lemma `coeff_divOf` / 引理 `coeff_divOf`

English:
lemma coeff_divOf
  given: (g : G) (x : k[G]) (g' : G)
  statement: (x /ᵒᶠ g).coeff g' = x.coeff (g + g')
  proof: rfl

@[deprecated (since := "2026-06-18")] alias divOf_apply := coeff_divOf

@[simp]

中文:
引理 coeff_divOf
  条件: (g : G) (x : k[G]) (g' : G)
  结论: (x /ᵒᶠ g).coeff g' = x.coeff (g + g')
  证明: rfl

@[deprecated (since := "2026-06-18")] alias divOf_apply := coeff_divOf

@[simp]
-/
@[simp] lemma coeff_divOf (g : G) (x : k[G]) (g' : G) : (x /ᵒᶠ g).coeff g' = x.coeff (g + g') := rfl

@[deprecated (since := "2026-06-18")] alias divOf_apply := coeff_divOf

@[simp]
/--
theorem `support_coeff_divOf` / 定理 `support_coeff_divOf`

English:
theorem support_coeff_divOf
  given: (g : G) (x : k[G])
  proof: rfl

@[deprecated (since := "2026-06-18")] alias support_divOf := support_coeff_divOf

@[simp]

中文:
定理 support_coeff_divOf
  条件: (g : G) (x : k[G])
  证明: rfl

@[deprecated (since := "2026-06-18")] alias support_divOf := support_coeff_divOf

@[simp]
-/
theorem support_coeff_divOf (g : G) (x : k[G]) :
    (x /ᵒᶠ g).coeff.support = x.coeff.support.preimage (g + ·) (add_right_injective g).injOn :=
  rfl

@[deprecated (since := "2026-06-18")] alias support_divOf := support_coeff_divOf

@[simp]
/--
theorem `zero_divOf` / 定理 `zero_divOf`

English:
theorem zero_divOf
  given: (g : G)
  statement: (0 : k[G]) /ᵒᶠ g = 0
  proof: by ext; simp

@[simp]

中文:
定理 zero_divOf
  条件: (g : G)
  结论: (0 : k[G]) /ᵒᶠ g = 0
  证明: by ext; simp

@[simp]
-/
theorem zero_divOf (g : G) : (0 : k[G]) /ᵒᶠ g = 0 := by ext; simp

@[simp]
/--
theorem `divOf_zero` / 定理 `divOf_zero`

English:
theorem divOf_zero
  given: (x : k[G])
  statement: x /ᵒᶠ 0 = x
  proof: by ext; simp

中文:
定理 divOf_zero
  条件: (x : k[G])
  结论: x /ᵒᶠ 0 = x
  证明: by ext; simp
-/
theorem divOf_zero (x : k[G]) : x /ᵒᶠ 0 = x := by ext; simp

/--
theorem `add_divOf` / 定理 `add_divOf`

English:
theorem add_divOf
  given: (x y : k[G]) (g : G)
  statement: (x + y) /ᵒᶠ g = x /ᵒᶠ g + y /ᵒᶠ g
  proof: by ext; simp

中文:
定理 add_divOf
  条件: (x y : k[G]) (g : G)
  结论: (x + y) /ᵒᶠ g = x /ᵒᶠ g + y /ᵒᶠ g
  证明: by ext; simp
-/
theorem add_divOf (x y : k[G]) (g : G) : (x + y) /ᵒᶠ g = x /ᵒᶠ g + y /ᵒᶠ g := by ext; simp

/--
theorem `divOf_add` / 定理 `divOf_add`

English:
theorem divOf_add
  given: (x : k[G]) (a b : G)
  statement: x /ᵒᶠ (a + b) = x /ᵒᶠ a /ᵒᶠ b
  proof: by ext; simp [add_assoc]

中文:
定理 divOf_add
  条件: (x : k[G]) (a b : G)
  结论: x /ᵒᶠ (a + b) = x /ᵒᶠ a /ᵒᶠ b
  证明: by ext; simp [add_assoc]

Depends on / 依赖: add_assoc
-/
theorem divOf_add (x : k[G]) (a b : G) : x /ᵒᶠ (a + b) = x /ᵒᶠ a /ᵒᶠ b := by ext; simp [add_assoc]

/-- A bundled version of `AddMonoidAlgebra.divOf`. -/
@[simps]
/--
Definition of `divOfHom` / `divOfHom` 的定义

English:
definition divOfHom
  signature: : Multiplicative G ->* AddMonoid.End k[G] where
  body: { toFun := fun x => divOf x g.toAdd
      map_zero' := zero_divOf _
      map_add' := fun x y => add_divOf x y g.toAdd }
  map_one' := AddMonoidHom.ext divOf_zero
  map_mul' g₁ g₂ :=
    AddMonoidHom.ext fun _x =>
      (congr_arg _ (add_comm g₁.toAdd g₂.toAdd)).trans
        (divOf_add _ _ _)

中文:
定义 divOfHom
  签名: : Multiplicative G ->* AddMonoid.End k[G] where
  定义体: { toFun := fun x => divOf x g.toAdd
      map_zero' := zero_divOf _
      map_add' := fun x y => add_divOf x y g.toAdd }
  map_one' := AddMonoidHom.ext divOf_zero
  map_mul' g₁ g₂ :=
    AddMonoidHom.ext fun _x =>
      (congr_arg _ (add_comm g₁.toAdd g₂.toAdd)).trans
        (divOf_add _ _ _)

Depends on / 依赖: AddMonoidHom, AddMonoidHom.ext, add_comm, add_divOf, congr_arg, divOf_add, divOf_zero, g.toAdd, map_add, map_mul, map_one, map_zero, zero_divOf
-/
noncomputable def divOfHom : Multiplicative G ->* AddMonoid.End k[G] where
  toFun g :=
    { toFun := fun x => divOf x g.toAdd
      map_zero' := zero_divOf _
      map_add' := fun x y => add_divOf x y g.toAdd }
  map_one' := AddMonoidHom.ext divOf_zero
  map_mul' g₁ g₂ :=
    AddMonoidHom.ext fun _x =>
      (congr_arg _ (add_comm g₁.toAdd g₂.toAdd)).trans
        (divOf_add _ _ _)

/--
theorem `of'_mul_divOf` / 定理 `of'_mul_divOf`

English:
theorem of'_mul_divOf
  given: (a : G) (x : k[G])
  statement: of' k G a * x /ᵒᶠ a = x
  proof: by
  ext; simp only [of'_apply, coeff_divOf, coeff_single_mul_add, one_mul]

中文:
定理 of'_mul_divOf
  条件: (a : G) (x : k[G])
  结论: of' k G a * x /ᵒᶠ a = x
  证明: by
  ext; simp only [of'_apply, coeff_divOf, coeff_single_mul_add, one_mul]
-/
theorem of'_mul_divOf (a : G) (x : k[G]) : of' k G a * x /ᵒᶠ a = x := by
  ext; simp only [of'_apply, coeff_divOf, coeff_single_mul_add, one_mul]

/--
theorem `mul_of'_divOf` / 定理 `mul_of'_divOf`

English:
theorem mul_of'_divOf
  given: (x : k[G]) (a : G)
  statement: x * of' k G a /ᵒᶠ a = x
  proof: by
  ext; simp only [of'_apply, coeff_divOf, add_comm a, coeff_mul_single_add, mul_one]

中文:
定理 mul_of'_divOf
  条件: (x : k[G]) (a : G)
  结论: x * of' k G a /ᵒᶠ a = x
  证明: by
  ext; simp only [of'_apply, coeff_divOf, add_comm a, coeff_mul_single_add, mul_one]

Depends on / 依赖: _apply, add_comm, coeff_divOf, coeff_mul_single_add, mul_one
-/
theorem mul_of'_divOf (x : k[G]) (a : G) : x * of' k G a /ᵒᶠ a = x := by
  ext; simp only [of'_apply, coeff_divOf, add_comm a, coeff_mul_single_add, mul_one]

/--
theorem `of'_divOf` / 定理 `of'_divOf`

English:
theorem of'_divOf
  given: (a : G)
  statement: of' k G a /ᵒᶠ a = 1
  proof: by
  simpa only [one_mul] using mul_of'_divOf (1 : k[G]) a

中文:
定理 of'_divOf
  条件: (a : G)
  结论: of' k G a /ᵒᶠ a = 1
  证明: by
  simpa only [one_mul] using mul_of'_divOf (1 : k[G]) a
-/
theorem of'_divOf (a : G) : of' k G a /ᵒᶠ a = 1 := by
  simpa only [one_mul] using mul_of'_divOf (1 : k[G]) a

end divOf

/--
Definition of `modOf` / `modOf` 的定义

English:
definition modOf
  signature: (x : k[G]) (g : G)
  body: letI := Classical.decPred fun g₁ => exists g₂, g₁ = g + g₂
.ofCoeff x.coeff.filter fun g₁ => ¬exists g₂, g₁ = g + g₂

local infixl:70 " %ᵒᶠ " => modOf

@[simp]

中文:
定义 modOf
  签名: (x : k[G]) (g : G)
  定义体: letI := Classical.decPred fun g₁ => exists g₂, g₁ = g + g₂
.ofCoeff x.coeff.filter fun g₁ => ¬exists g₂, g₁ = g + g₂

local infixl:70 " %ᵒᶠ " => modOf

@[simp]

Depends on / 依赖: Classical, Classical.decPred, decPred, filter, ofCoeff, x.coeff.filter
-/
noncomputable def modOf (x : k[G]) (g : G) : k[G] :=
  letI := Classical.decPred fun g₁ => exists g₂, g₁ = g + g₂
.ofCoeff x.coeff.filter fun g₁ => ¬exists g₂, g₁ = g + g₂

local infixl:70 " %ᵒᶠ " => modOf

@[simp]
/--
theorem `coeff_modOf_of_not_exists_add` / 定理 `coeff_modOf_of_not_exists_add`

English:
theorem coeff_modOf_of_not_exists_add
  given: (x : k[G]) (g : G) (g' : G) (h : ¬exists d, g' = g + d)
  proof: by
  classical exact Finsupp.filter_apply_pos _ _ h

@[deprecated (since := "2026-06-18")]
alias modOf_apply_of_not_exists_add := coeff_modOf_of_not_exists_add

@[simp]

中文:
定理 coeff_modOf_of_not_exists_add
  条件: (x : k[G]) (g : G) (g' : G) (h : ¬存在 d, g' = g + d)
  证明: by
  classical exact Finsupp.filter_apply_pos _ _ h

@[deprecated (since := "2026-06-18")]
alias modOf_apply_of_not_exists_add := coeff_modOf_of_not_exists_add

@[simp]

Depends on / 依赖: Finsupp, Finsupp.filter_apply_pos, classical, filter_apply_pos
-/
theorem coeff_modOf_of_not_exists_add (x : k[G]) (g : G) (g' : G) (h : ¬exists d, g' = g + d) :
    (x %ᵒᶠ g).coeff g' = x.coeff g' := by
  classical exact Finsupp.filter_apply_pos _ _ h

@[deprecated (since := "2026-06-18")]
alias modOf_apply_of_not_exists_add := coeff_modOf_of_not_exists_add

@[simp]
/--
theorem `coeff_modOf_of_exists_add` / 定理 `coeff_modOf_of_exists_add`

English:
theorem coeff_modOf_of_exists_add
  given: (x : k[G]) (g : G) (g' : G) (h : exists d, g' = g + d)
  proof: by
classical exact Finsupp.filter_apply_neg _ _ by rwa [Classical.not_not]

@[deprecated (since := "2026-06-18")] alias modOf_apply_of_exists_add := coeff_modOf_of_exists_add

@[simp]

中文:
定理 coeff_modOf_of_exists_add
  条件: (x : k[G]) (g : G) (g' : G) (h : 存在 d, g' = g + d)
  证明: by
classical exact Finsupp.filter_apply_neg _ _ by rwa [Classical.not_not]

@[deprecated (since := "2026-06-18")] alias modOf_apply_of_exists_add := coeff_modOf_of_exists_add

@[simp]

Depends on / 依赖: Classical, Classical.not_not, Finsupp, Finsupp.filter_apply_neg, classical, filter_apply_neg, not_not
-/
theorem coeff_modOf_of_exists_add (x : k[G]) (g : G) (g' : G) (h : exists d, g' = g + d) :
    (x %ᵒᶠ g).coeff g' = 0 := by
classical exact Finsupp.filter_apply_neg _ _ by rwa [Classical.not_not]

@[deprecated (since := "2026-06-18")] alias modOf_apply_of_exists_add := coeff_modOf_of_exists_add

@[simp]
/--
theorem `coeff_modOf_add_self` / 定理 `coeff_modOf_add_self`

English:
theorem coeff_modOf_add_self
  given: (x : k[G]) (g : G) (d : G)
  statement: (x %ᵒᶠ g).coeff (d + g) = 0
  proof: coeff_modOf_of_exists_add _ _ _ ⟨_, add_comm _ _⟩

@[deprecated (since := "2026-06-18")] alias modOf_apply_add_self := coeff_modOf_add_self

中文:
定理 coeff_modOf_add_self
  条件: (x : k[G]) (g : G) (d : G)
  结论: (x %ᵒᶠ g).coeff (d + g) = 0
  证明: coeff_modOf_of_exists_add _ _ _ ⟨_, add_comm _ _⟩

@[deprecated (since := "2026-06-18")] alias modOf_apply_add_self := coeff_modOf_add_self

Depends on / 依赖: add_comm, coeff_modOf_of_exists_add
-/
theorem coeff_modOf_add_self (x : k[G]) (g : G) (d : G) : (x %ᵒᶠ g).coeff (d + g) = 0 :=
  coeff_modOf_of_exists_add _ _ _ ⟨_, add_comm _ _⟩

@[deprecated (since := "2026-06-18")] alias modOf_apply_add_self := coeff_modOf_add_self

/--
theorem `coeff_modOf_self_add` / 定理 `coeff_modOf_self_add`

English:
theorem coeff_modOf_self_add
  given: (x : k[G]) (g : G) (d : G)
  statement: (x %ᵒᶠ g).coeff (g + d) = 0
  proof: coeff_modOf_of_exists_add _ _ _ ⟨_, rfl⟩

@[deprecated (since := "2026-06-18")] alias modOf_apply_self_add := coeff_modOf_self_add

中文:
定理 coeff_modOf_self_add
  条件: (x : k[G]) (g : G) (d : G)
  结论: (x %ᵒᶠ g).coeff (g + d) = 0
  证明: coeff_modOf_of_exists_add _ _ _ ⟨_, rfl⟩

@[deprecated (since := "2026-06-18")] alias modOf_apply_self_add := coeff_modOf_self_add

Depends on / 依赖: coeff_modOf_of_exists_add
-/
theorem coeff_modOf_self_add (x : k[G]) (g : G) (d : G) : (x %ᵒᶠ g).coeff (g + d) = 0 :=
  coeff_modOf_of_exists_add _ _ _ ⟨_, rfl⟩

@[deprecated (since := "2026-06-18")] alias modOf_apply_self_add := coeff_modOf_self_add

/--
theorem `of'_mul_modOf` / 定理 `of'_mul_modOf`

English:
theorem of'_mul_modOf
  given: (g : G) (x : k[G])
  statement: of' k G g * x %ᵒᶠ g = 0
  proof: by
  ext g'
  simp only [of'_apply, coeff_zero, Finsupp.coe_zero, Pi.zero_apply]
  obtain ⟨d, rfl⟩ | h := em (exists d, g' = g + d)
  · rw [coeff_modOf_self_add]
  · rw [coeff_modOf_of_not_exists_add _ _ _ h, coeff_single_mul_of_forall_add_ne]
    simpa [eq_comm] using h

中文:
定理 of'_mul_modOf
  条件: (g : G) (x : k[G])
  结论: of' k G g * x %ᵒᶠ g = 0
  证明: by
  ext g'
  simp only [of'_apply, coeff_zero, Finsupp.coe_zero, Pi.zero_apply]
  obtain ⟨d, rfl⟩ | h := em (exists d, g' = g + d)
  · rw [coeff_modOf_self_add]
  · rw [coeff_modOf_of_not_exists_add _ _ _ h, coeff_single_mul_of_forall_add_ne]
    simpa [eq_comm] using h
-/
theorem of'_mul_modOf (g : G) (x : k[G]) : of' k G g * x %ᵒᶠ g = 0 := by
  ext g'
  simp only [of'_apply, coeff_zero, Finsupp.coe_zero, Pi.zero_apply]
  obtain ⟨d, rfl⟩ | h := em (exists d, g' = g + d)
  · rw [coeff_modOf_self_add]
  · rw [coeff_modOf_of_not_exists_add _ _ _ h, coeff_single_mul_of_forall_add_ne]
    simpa [eq_comm] using h

/--
theorem `mul_of'_modOf` / 定理 `mul_of'_modOf`

English:
theorem mul_of'_modOf
  given: (x : k[G]) (g : G)
  statement: x * of' k G g %ᵒᶠ g = 0
  proof: by
  ext g'
  simp only [of'_apply, coeff_zero, Finsupp.zero_apply]
  obtain ⟨d, rfl⟩ | h := em (exists d, g' = g + d)
  · rw [coeff_modOf_self_add]
  · rw [coeff_modOf_of_not_exists_add _ _ _ h, coeff_mul_single_of_forall_add_ne]
    simpa [eq_comm, add_comm] using h

中文:
定理 mul_of'_modOf
  条件: (x : k[G]) (g : G)
  结论: x * of' k G g %ᵒᶠ g = 0
  证明: by
  ext g'
  simp only [of'_apply, coeff_zero, Finsupp.zero_apply]
  obtain ⟨d, rfl⟩ | h := em (exists d, g' = g + d)
  · rw [coeff_modOf_self_add]
  · rw [coeff_modOf_of_not_exists_add _ _ _ h, coeff_mul_single_of_forall_add_ne]
    simpa [eq_comm, add_comm] using h
-/
theorem mul_of'_modOf (x : k[G]) (g : G) : x * of' k G g %ᵒᶠ g = 0 := by
  ext g'
  simp only [of'_apply, coeff_zero, Finsupp.zero_apply]
  obtain ⟨d, rfl⟩ | h := em (exists d, g' = g + d)
  · rw [coeff_modOf_self_add]
  · rw [coeff_modOf_of_not_exists_add _ _ _ h, coeff_mul_single_of_forall_add_ne]
    simpa [eq_comm, add_comm] using h

/--
theorem `of'_modOf` / 定理 `of'_modOf`

English:
theorem of'_modOf
  given: (g : G)
  statement: of' k G g %ᵒᶠ g = 0
  proof: by
  simpa only [one_mul] using mul_of'_modOf (1 : k[G]) g

中文:
定理 of'_modOf
  条件: (g : G)
  结论: of' k G g %ᵒᶠ g = 0
  证明: by
  simpa only [one_mul] using mul_of'_modOf (1 : k[G]) g
-/
theorem of'_modOf (g : G) : of' k G g %ᵒᶠ g = 0 := by
  simpa only [one_mul] using mul_of'_modOf (1 : k[G]) g

/--
theorem `divOf_add_modOf` / 定理 `divOf_add_modOf`

English:
theorem divOf_add_modOf
  given: [IsCancelAdd G] (x : k[G]) (g : G)
  proof: by
  ext g'
  dsimp only [coeff_add, of'_apply, Finsupp.add_apply]
  obtain ⟨d, rfl⟩ | h := em (exists d, g' = g + d)
  · rw [coeff_modOf_self_add, add_zero, coeff_single_mul_add, one_mul, coeff_divOf]
  · rw [coeff_modOf_of_not_exists_add x _ _ h, coeff_single_mul_of_forall_add_ne, zero_add]
    si

中文:
定理 divOf_add_modOf
  条件: [IsCancelAdd G] (x : k[G]) (g : G)
  证明: by
  ext g'
  dsimp only [coeff_add, of'_apply, Finsupp.add_apply]
  obtain ⟨d, rfl⟩ | h := em (exists d, g' = g + d)
  · rw [coeff_modOf_self_add, add_zero, coeff_single_mul_add, one_mul, coeff_divOf]
  · rw [coeff_modOf_of_not_exists_add x _ _ h, coeff_single_mul_of_forall_add_ne, zero_add]
    si

Depends on / 依赖: Finsupp, Finsupp.add_apply, _apply, add_apply, add_zero, coeff_add, coeff_divOf, coeff_modOf_of_not_exists_add, coeff_modOf_self_add, coeff_single_mul_add, coeff_single_mul_of_forall_add_ne, eq_comm, one_mul, zero_add
-/
theorem divOf_add_modOf [IsCancelAdd G] (x : k[G]) (g : G) :
    of' k G g * (x /ᵒᶠ g) + x %ᵒᶠ g = x := by
  ext g'
  dsimp only [coeff_add, of'_apply, Finsupp.add_apply]
  obtain ⟨d, rfl⟩ | h := em (exists d, g' = g + d)
  · rw [coeff_modOf_self_add, add_zero, coeff_single_mul_add, one_mul, coeff_divOf]
  · rw [coeff_modOf_of_not_exists_add x _ _ h, coeff_single_mul_of_forall_add_ne, zero_add]
    simpa [eq_comm] using h

/--
theorem `modOf_add_divOf` / 定理 `modOf_add_divOf`

English:
theorem modOf_add_divOf
  given: [IsCancelAdd G] (x : k[G]) (g : G)
  proof: by
  rw [add_comm]; rw [divOf_add_modOf]

中文:
定理 modOf_add_divOf
  条件: [IsCancelAdd G] (x : k[G]) (g : G)
  证明: by
  rw [add_comm]; rw [divOf_add_modOf]

Depends on / 依赖: add_comm, divOf_add_modOf
-/
theorem modOf_add_divOf [IsCancelAdd G] (x : k[G]) (g : G) :
    x %ᵒᶠ g + of' k G g * (x /ᵒᶠ g) = x := by
  rw [add_comm]; rw [divOf_add_modOf]

/--
theorem `of'_dvd_iff_modOf_eq_zero` / 定理 `of'_dvd_iff_modOf_eq_zero`

English:
theorem of'_dvd_iff_modOf_eq_zero
  given: [IsCancelAdd G] {x : k[G]} {g : G}
  proof: by
  constructor
  · rintro ⟨x, rfl⟩
    rw [of'_mul_modOf]
  · intro h
    rw [← divOf_add_modOf x g]; rw [h]; rw [add_zero]
    exact dvd_mul_right _ _

中文:
定理 of'_dvd_iff_modOf_eq_zero
  条件: [IsCancelAdd G] {x : k[G]} {g : G}
  证明: by
  constructor
  · rintro ⟨x, rfl⟩
    rw [of'_mul_modOf]
  · intro h
    rw [← divOf_add_modOf x g]; rw [h]; rw [add_zero]
    exact dvd_mul_right _ _
-/
theorem of'_dvd_iff_modOf_eq_zero [IsCancelAdd G] {x : k[G]} {g : G} :
    of' k G g ∣ x ↔ x %ᵒᶠ g = 0 := by
  constructor
  · rintro ⟨x, rfl⟩
    rw [of'_mul_modOf]
  · intro h
    rw [← divOf_add_modOf x g]; rw [h]; rw [add_zero]
    exact dvd_mul_right _ _

end

end AddMonoidAlgebra
