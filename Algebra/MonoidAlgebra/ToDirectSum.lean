/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.DirectSum.Algebra
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Data.Finsupp.ToDFinsupp

/-!
# Conversion between `AddMonoidAlgebra` and homogeneous `DirectSum`

This module provides conversions between `AddMonoidAlgebra` and `DirectSum`.
The latter is essentially a dependent version of the former.

Note that since `DirectSum.instMul` combines indices additively, there is no equivalent to
`MonoidAlgebra`.

## Main definitions

* `AddMonoidAlgebra.toDirectSum : AddMonoidAlgebra M ι → (⨁ i : ι, M)`
* `DirectSum.toAddMonoidAlgebra : (⨁ i : ι, M) → AddMonoidAlgebra M ι`
* Bundled equiv versions of the above:
  * `addMonoidAlgebraEquivDirectSum : AddMonoidAlgebra M ι ≃ (⨁ i : ι, M)`
  * `addMonoidAlgebraAddEquivDirectSum : AddMonoidAlgebra M ι ≃+ (⨁ i : ι, M)`
  * `addMonoidAlgebraRingEquivDirectSum R : AddMonoidAlgebra M ι ≃+* (⨁ i : ι, M)`
  * `addMonoidAlgebraAlgEquivDirectSum R : AddMonoidAlgebra A ι ≃ₐ[R] (⨁ i : ι, A)`

## Theorems

The defining feature of these operations is that they map `AddMonoidAlgebra.single` to
`DirectSum.of` and vice versa:

* `AddMonoidAlgebra.toDirectSum_single`
* `DirectSum.toAddMonoidAlgebra_of`

as well as preserving arithmetic operations.

For the bundled equivalences, we provide lemmas that they reduce to
`AddMonoidAlgebra.toDirectSum`:

* `addMonoidAlgebraAddEquivDirectSum_apply`
* `add_monoid_algebra_lequiv_direct_sum_apply`
* `addMonoidAlgebraAddEquivDirectSum_symm_apply`
* `add_monoid_algebra_lequiv_direct_sum_symm_apply`

## Implementation notes

This file largely just copies the API of `Mathlib/Data/Finsupp/ToDFinsupp.lean`, and reuses the
proofs. Recall that `AddMonoidAlgebra M ι` is defeq to `ι →₀ M` and `⨁ i : ι, M` is defeq to
`Π₀ i : ι, M`.
-/

@[expose] public section


variable {ι : Type*} {R : Type*} {M : Type*} {A : Type*}

open DirectSum

/-! ### Basic definitions and lemmas -/


section Defs

/--
Definition of `AddMonoidAlgebra.toDirectSum` / `AddMonoidAlgebra.toDirectSum` 的定义

English:
definition AddMonoidAlgebra.toDirectSum
  signature: [Semiring M] (f : AddMonoidAlgebra M ι)
  body: f.coeff.toDFinsupp

中文:
定义 AddMonoidAlgebra.toDirectSum
  签名: [Semiring M] (f : AddMonoidAlgebra M ι)
  定义体: f.coeff.toDFinsupp

Depends on / 依赖: f.coeff.toDFinsupp, toDFinsupp
-/
def AddMonoidAlgebra.toDirectSum [Semiring M] (f : AddMonoidAlgebra M ι) : ⨁ _ : ι, M :=
  f.coeff.toDFinsupp

section

variable [DecidableEq ι] [Semiring M]

@[simp]
/--
lemma `AddMonoidAlgebra.toDirectSum_single` / 引理 `AddMonoidAlgebra.toDirectSum_single`

English:
lemma AddMonoidAlgebra.toDirectSum_single
  given: (i : ι) (m : M)
  statement: toDirectSum (single i m) = .of _ i m
  proof: Finsupp.toDFinsupp_single i m

中文:
引理 AddMonoidAlgebra.toDirectSum_single
  条件: (i : ι) (m : M)
  结论: toDirectSum (single i m) = .of _ i m
  证明: Finsupp.toDFinsupp_single i m

Depends on / 依赖: Finsupp, Finsupp.toDFinsupp_single, toDFinsupp_single
-/
lemma AddMonoidAlgebra.toDirectSum_single (i : ι) (m : M) : toDirectSum (single i m) = .of _ i m :=
  Finsupp.toDFinsupp_single i m

variable [forall m : M, Decidable (m != 0)]

/--
Definition of `DirectSum.toAddMonoidAlgebra` / `DirectSum.toAddMonoidAlgebra` 的定义

English:
definition DirectSum.toAddMonoidAlgebra
  signature: (f : ⨁ _ : ι, M)
  body: .ofCoeff f.toFinsupp

@[simp]

中文:
定义 DirectSum.toAddMonoidAlgebra
  签名: (f : ⨁ _ : ι, M)
  定义体: .ofCoeff f.toFinsupp

@[simp]

Depends on / 依赖: f.toFinsupp, ofCoeff, toFinsupp
-/
def DirectSum.toAddMonoidAlgebra (f : ⨁ _ : ι, M) : AddMonoidAlgebra M ι := .ofCoeff f.toFinsupp

@[simp]
/--
theorem `DirectSum.toAddMonoidAlgebra_of` / 定理 `DirectSum.toAddMonoidAlgebra_of`

English:
theorem DirectSum.toAddMonoidAlgebra_of
  given: (i : ι) (m : M)
  proof: by
  ext : 1; exact DFinsupp.toFinsupp_single i m

@[simp]

中文:
定理 DirectSum.toAddMonoidAlgebra_of
  条件: (i : ι) (m : M)
  证明: by
  ext : 1; exact DFinsupp.toFinsupp_single i m

@[simp]

Depends on / 依赖: DFinsupp, DFinsupp.toFinsupp_single, toFinsupp_single
-/
theorem DirectSum.toAddMonoidAlgebra_of (i : ι) (m : M) :
    (DirectSum.of _ i m : ⨁ _ : ι, M).toAddMonoidAlgebra = .single i m := by
  ext : 1; exact DFinsupp.toFinsupp_single i m

@[simp]
/--
theorem `AddMonoidAlgebra.toDirectSum_toAddMonoidAlgebra` / 定理 `AddMonoidAlgebra.toDirectSum_toAddMonoidAlgebra`

English:
theorem AddMonoidAlgebra.toDirectSum_toAddMonoidAlgebra
  given: (f : AddMonoidAlgebra M ι)
  proof: by ext : 1; exact Finsupp.toDFinsupp_toFinsupp _

@[simp]

中文:
定理 AddMonoidAlgebra.toDirectSum_toAddMonoidAlgebra
  条件: (f : AddMonoidAlgebra M ι)
  证明: by ext : 1; exact Finsupp.toDFinsupp_toFinsupp _

@[simp]

Depends on / 依赖: Finsupp, Finsupp.toDFinsupp_toFinsupp, toDFinsupp_toFinsupp
-/
theorem AddMonoidAlgebra.toDirectSum_toAddMonoidAlgebra (f : AddMonoidAlgebra M ι) :
    f.toDirectSum.toAddMonoidAlgebra = f := by ext : 1; exact Finsupp.toDFinsupp_toFinsupp _

@[simp]
/--
theorem `DirectSum.toAddMonoidAlgebra_toDirectSum` / 定理 `DirectSum.toAddMonoidAlgebra_toDirectSum`

English:
theorem DirectSum.toAddMonoidAlgebra_toDirectSum
  given: (f : ⨁ _ : ι, M)
  proof: (DFinsupp.toFinsupp_toDFinsupp (show Π₀ _ : ι, M from f) :)

中文:
定理 DirectSum.toAddMonoidAlgebra_toDirectSum
  条件: (f : ⨁ _ : ι, M)
  证明: (DFinsupp.toFinsupp_toDFinsupp (show Π₀ _ : ι, M from f) :)

Depends on / 依赖: DFinsupp, DFinsupp.toFinsupp_toDFinsupp, toFinsupp_toDFinsupp
-/
theorem DirectSum.toAddMonoidAlgebra_toDirectSum (f : ⨁ _ : ι, M) :
    f.toAddMonoidAlgebra.toDirectSum = f :=
  (DFinsupp.toFinsupp_toDFinsupp (show Π₀ _ : ι, M from f) :)

end

end Defs

/-! ### Lemmas about arithmetic operations -/


section Lemmas

namespace AddMonoidAlgebra

@[simp]
/--
theorem `toDirectSum_zero` / 定理 `toDirectSum_zero`

English:
theorem toDirectSum_zero
  given: [Semiring M]
  statement: (0 : AddMonoidAlgebra M ι).toDirectSum = 0
  proof: Finsupp.toDFinsupp_zero

@[simp]

中文:
定理 toDirectSum_zero
  条件: [Semiring M]
  结论: (0 : AddMonoidAlgebra M ι).toDirectSum = 0
  证明: Finsupp.toDFinsupp_zero

@[simp]

Depends on / 依赖: Finsupp, Finsupp.toDFinsupp_zero, toDFinsupp_zero
-/
theorem toDirectSum_zero [Semiring M] : (0 : AddMonoidAlgebra M ι).toDirectSum = 0 :=
  Finsupp.toDFinsupp_zero

@[simp]
/--
theorem `toDirectSum_add` / 定理 `toDirectSum_add`

English:
theorem toDirectSum_add
  given: [Semiring M] (f g : AddMonoidAlgebra M ι)
  proof: Finsupp.toDFinsupp_add _ _

@[simp]

中文:
定理 toDirectSum_add
  条件: [Semiring M] (f g : AddMonoidAlgebra M ι)
  证明: Finsupp.toDFinsupp_add _ _

@[simp]

Depends on / 依赖: Finsupp, Finsupp.toDFinsupp_add, toDFinsupp_add
-/
theorem toDirectSum_add [Semiring M] (f g : AddMonoidAlgebra M ι) :
    (f + g).toDirectSum = f.toDirectSum + g.toDirectSum :=
  Finsupp.toDFinsupp_add _ _

@[simp]
/--
theorem `toDirectSum_natCast` / 定理 `toDirectSum_natCast`

English:
theorem toDirectSum_natCast
  given: [DecidableEq ι] [AddMonoid ι] [Semiring M] (n : Nat)
  proof: Finsupp.toDFinsupp_single _ _

@[simp]

中文:
定理 toDirectSum_natCast
  条件: [DecidableEq ι] [AddMonoid ι] [Semiring M] (n : 自然数)
  证明: Finsupp.toDFinsupp_single _ _

@[simp]

Depends on / 依赖: Finsupp, Finsupp.toDFinsupp_single, toDFinsupp_single
-/
theorem toDirectSum_natCast [DecidableEq ι] [AddMonoid ι] [Semiring M] (n : Nat) :
    (n : AddMonoidAlgebra M ι).toDirectSum = n :=
  Finsupp.toDFinsupp_single _ _

@[simp]
/--
theorem `toDirectSum_ofNat` / 定理 `toDirectSum_ofNat`

English:
theorem toDirectSum_ofNat
  given: [DecidableEq ι] [AddMonoid ι] [Semiring M] (n : Nat) [n.AtLeastTwo]
  proof: Finsupp.toDFinsupp_single _ _

@[simp]

中文:
定理 toDirectSum_ofNat
  条件: [DecidableEq ι] [AddMonoid ι] [Semiring M] (n : 自然数) [n.AtLeastTwo]
  证明: Finsupp.toDFinsupp_single _ _

@[simp]

Depends on / 依赖: Finsupp, Finsupp.toDFinsupp_single, toDFinsupp_single
-/
theorem toDirectSum_ofNat [DecidableEq ι] [AddMonoid ι] [Semiring M] (n : Nat) [n.AtLeastTwo] :
    (ofNat(n) : AddMonoidAlgebra M ι).toDirectSum = ofNat(n) :=
  Finsupp.toDFinsupp_single _ _

@[simp]
/--
theorem `toDirectSum_sub` / 定理 `toDirectSum_sub`

English:
theorem toDirectSum_sub
  given: [Ring M] (f g : AddMonoidAlgebra M ι)
  proof: Finsupp.toDFinsupp_sub _ _

@[simp]

中文:
定理 toDirectSum_sub
  条件: [Ring M] (f g : AddMonoidAlgebra M ι)
  证明: Finsupp.toDFinsupp_sub _ _

@[simp]

Depends on / 依赖: Finsupp, Finsupp.toDFinsupp_sub, toDFinsupp_sub
-/
theorem toDirectSum_sub [Ring M] (f g : AddMonoidAlgebra M ι) :
    (f - g).toDirectSum = f.toDirectSum - g.toDirectSum :=
  Finsupp.toDFinsupp_sub _ _

@[simp]
/--
theorem `toDirectSum_neg` / 定理 `toDirectSum_neg`

English:
theorem toDirectSum_neg
  given: [Ring M] (f : AddMonoidAlgebra M ι)
  proof: Finsupp.toDFinsupp_neg _

@[simp]

中文:
定理 toDirectSum_neg
  条件: [Ring M] (f : AddMonoidAlgebra M ι)
  证明: Finsupp.toDFinsupp_neg _

@[simp]

Depends on / 依赖: Finsupp, Finsupp.toDFinsupp_neg, toDFinsupp_neg
-/
theorem toDirectSum_neg [Ring M] (f : AddMonoidAlgebra M ι) :
    (-f).toDirectSum = - f.toDirectSum :=
  Finsupp.toDFinsupp_neg _

@[simp]
/--
theorem `toDirectSum_intCast` / 定理 `toDirectSum_intCast`

English:
theorem toDirectSum_intCast
  given: [DecidableEq ι] [AddMonoid ι] [Ring M] (z : Int)
  proof: Finsupp.toDFinsupp_single _ _

@[simp]

中文:
定理 toDirectSum_intCast
  条件: [DecidableEq ι] [AddMonoid ι] [Ring M] (z : 整数)
  证明: Finsupp.toDFinsupp_single _ _

@[simp]

Depends on / 依赖: Finsupp, Finsupp.toDFinsupp_single, toDFinsupp_single
-/
theorem toDirectSum_intCast [DecidableEq ι] [AddMonoid ι] [Ring M] (z : Int) :
    (Int.cast z : AddMonoidAlgebra M ι).toDirectSum = z :=
  Finsupp.toDFinsupp_single _ _

@[simp]
/--
theorem `toDirectSum_one` / 定理 `toDirectSum_one`

English:
theorem toDirectSum_one
  given: [DecidableEq ι] [Zero ι] [Semiring M]
  proof: Finsupp.toDFinsupp_single _ _

@[simp]

中文:
定理 toDirectSum_one
  条件: [DecidableEq ι] [Zero ι] [Semiring M]
  证明: Finsupp.toDFinsupp_single _ _

@[simp]

Depends on / 依赖: Finsupp, Finsupp.toDFinsupp_single, toDFinsupp_single
-/
theorem toDirectSum_one [DecidableEq ι] [Zero ι] [Semiring M] :
    (1 : AddMonoidAlgebra M ι).toDirectSum = 1 :=
  Finsupp.toDFinsupp_single _ _

@[simp]
/--
theorem `toDirectSum_mul` / 定理 `toDirectSum_mul`

English:
theorem toDirectSum_mul
  given: [DecidableEq ι] [AddMonoid ι] [Semiring M] (f g : AddMonoidAlgebra M ι)
  proof: by
  let to_hom : AddMonoidAlgebra M ι ->+ ⨁ _ : ι, M :=
  { toFun := toDirectSum
    map_zero' := toDirectSum_zero
    map_add' := toDirectSum_add }
  change to_hom (f * g) = to_hom f * to_hom g
  revert f g
  rw [AddMonoidHom.map_mul_iff]
  ext xi xv yi yv : 4
  simp [to_hom, AddMonoidAlgebra.sing

中文:
定理 toDirectSum_mul
  条件: [DecidableEq ι] [AddMonoid ι] [Semiring M] (f g : AddMonoidAlgebra M ι)
  证明: by
  let to_hom : AddMonoidAlgebra M ι ->+ ⨁ _ : ι, M :=
  { toFun := toDirectSum
    map_zero' := toDirectSum_zero
    map_add' := toDirectSum_add }
  change to_hom (f * g) = to_hom f * to_hom g
  revert f g
  rw [AddMonoidHom.map_mul_iff]
  ext xi xv yi yv : 4
  simp [to_hom, AddMonoidAlgebra.sing

Depends on / 依赖: AddMonoidAlgebra, AddMonoidAlgebra.single_mul_single, AddMonoidHom, AddMonoidHom.map_mul_iff, DirectSum, DirectSum.of_mul_of, map_add, map_mul_iff, map_zero, of_mul_of, revert, single_mul_single, toDirectSum, toDirectSum_add, toDirectSum_zero, to_hom
-/
theorem toDirectSum_mul [DecidableEq ι] [AddMonoid ι] [Semiring M] (f g : AddMonoidAlgebra M ι) :
    (f * g).toDirectSum = f.toDirectSum * g.toDirectSum := by
  let to_hom : AddMonoidAlgebra M ι ->+ ⨁ _ : ι, M :=
  { toFun := toDirectSum
    map_zero' := toDirectSum_zero
    map_add' := toDirectSum_add }
  change to_hom (f * g) = to_hom f * to_hom g
  revert f g
  rw [AddMonoidHom.map_mul_iff]
  ext xi xv yi yv : 4
  simp [to_hom, AddMonoidAlgebra.single_mul_single, DirectSum.of_mul_of]

end AddMonoidAlgebra

namespace DirectSum

variable [DecidableEq ι]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `toAddMonoidAlgebra_zero` / 定理 `toAddMonoidAlgebra_zero`

English:
theorem toAddMonoidAlgebra_zero
  given: [Semiring M] [forall m : M, Decidable (m != 0)]
  proof: by simp [toAddMonoidAlgebra]

@[simp]

中文:
定理 toAddMonoidAlgebra_zero
  条件: [Semiring M] [对任意 m : M, Decidable (m != 0)]
  证明: by simp [toAddMonoidAlgebra]

@[simp]

Depends on / 依赖: toAddMonoidAlgebra
-/
theorem toAddMonoidAlgebra_zero [Semiring M] [forall m : M, Decidable (m != 0)] :
    toAddMonoidAlgebra 0 = (0 : AddMonoidAlgebra M ι) := by simp [toAddMonoidAlgebra]

@[simp]
/--
theorem `toAddMonoidAlgebra_add` / 定理 `toAddMonoidAlgebra_add`

English:
theorem toAddMonoidAlgebra_add
  given: [Semiring M] [forall m : M, Decidable (m != 0)] (f g : ⨁ _ : ι, M)
  proof: by
  ext; simp [toAddMonoidAlgebra]

@[simp]

中文:
定理 toAddMonoidAlgebra_add
  条件: [Semiring M] [对任意 m : M, Decidable (m != 0)] (f g : ⨁ _ : ι, M)
  证明: by
  ext; simp [toAddMonoidAlgebra]

@[simp]

Depends on / 依赖: toAddMonoidAlgebra
-/
theorem toAddMonoidAlgebra_add [Semiring M] [forall m : M, Decidable (m != 0)] (f g : ⨁ _ : ι, M) :
    (f + g).toAddMonoidAlgebra = toAddMonoidAlgebra f + toAddMonoidAlgebra g := by
  ext; simp [toAddMonoidAlgebra]

@[simp]
/--
theorem `toAddMonoidAlgebra_natCast` / 定理 `toAddMonoidAlgebra_natCast`

English:
theorem toAddMonoidAlgebra_natCast
  given: [AddMonoid ι] [Semiring M] [forall m : M, Decidable (m != 0)] (n : Nat)
  proof: by
  ext : 1; exact DFinsupp.toFinsupp_single ..

@[simp]

中文:
定理 toAddMonoidAlgebra_natCast
  条件: [AddMonoid ι] [Semiring M] [对任意 m : M, Decidable (m != 0)] (n : 自然数)
  证明: by
  ext : 1; exact DFinsupp.toFinsupp_single ..

@[simp]

Depends on / 依赖: DFinsupp, DFinsupp.toFinsupp_single, toFinsupp_single
-/
theorem toAddMonoidAlgebra_natCast [AddMonoid ι] [Semiring M] [forall m : M, Decidable (m != 0)] (n : Nat) :
    (n : ⨁ _ : ι, M).toAddMonoidAlgebra = n := by
  ext : 1; exact DFinsupp.toFinsupp_single ..

@[simp]
/--
theorem `toAddMonoidAlgebra_ofNat` / 定理 `toAddMonoidAlgebra_ofNat`

English:
theorem toAddMonoidAlgebra_ofNat
  statement: [AddMonoid ι] [Semiring M] [forall m : M, Decidable (m != 0)] (n : Nat)
  proof: toAddMonoidAlgebra_natCast _

@[simp]

中文:
定理 toAddMonoidAlgebra_ofNat
  结论: [AddMonoid ι] [Semiring M] [对任意 m : M, Decidable (m != 0)] (n : 自然数)
  证明: toAddMonoidAlgebra_natCast _

@[simp]

Depends on / 依赖: toAddMonoidAlgebra_natCast
-/
theorem toAddMonoidAlgebra_ofNat [AddMonoid ι] [Semiring M] [forall m : M, Decidable (m != 0)] (n : Nat)
    [n.AtLeastTwo] :
    (ofNat(n) : ⨁ _ : ι, M).toAddMonoidAlgebra = ofNat(n) :=
  toAddMonoidAlgebra_natCast _

@[simp]
/--
theorem `toAddMonoidAlgebra_sub` / 定理 `toAddMonoidAlgebra_sub`

English:
theorem toAddMonoidAlgebra_sub
  given: [Ring M] [forall m : M, Decidable (m != 0)] (f g : ⨁ _ : ι, M)
  proof: by
  ext : 1; exact DFinsupp.toFinsupp_sub ..

@[simp]

中文:
定理 toAddMonoidAlgebra_sub
  条件: [Ring M] [对任意 m : M, Decidable (m != 0)] (f g : ⨁ _ : ι, M)
  证明: by
  ext : 1; exact DFinsupp.toFinsupp_sub ..

@[simp]

Depends on / 依赖: DFinsupp, DFinsupp.toFinsupp_sub, toFinsupp_sub
-/
theorem toAddMonoidAlgebra_sub [Ring M] [forall m : M, Decidable (m != 0)] (f g : ⨁ _ : ι, M) :
    (f - g).toAddMonoidAlgebra = toAddMonoidAlgebra f - toAddMonoidAlgebra g := by
  ext : 1; exact DFinsupp.toFinsupp_sub ..

@[simp]
/--
theorem `toAddMonoidAlgebra_neg` / 定理 `toAddMonoidAlgebra_neg`

English:
theorem toAddMonoidAlgebra_neg
  given: [Ring M] [forall m : M, Decidable (m != 0)] (f : ⨁ _ : ι, M)
  proof: by
  ext : 1; exact DFinsupp.toFinsupp_neg ..

@[simp]

中文:
定理 toAddMonoidAlgebra_neg
  条件: [Ring M] [对任意 m : M, Decidable (m != 0)] (f : ⨁ _ : ι, M)
  证明: by
  ext : 1; exact DFinsupp.toFinsupp_neg ..

@[simp]

Depends on / 依赖: DFinsupp, DFinsupp.toFinsupp_neg, toFinsupp_neg
-/
theorem toAddMonoidAlgebra_neg [Ring M] [forall m : M, Decidable (m != 0)] (f : ⨁ _ : ι, M) :
    (-f).toAddMonoidAlgebra = -toAddMonoidAlgebra f := by
  ext : 1; exact DFinsupp.toFinsupp_neg ..

@[simp]
/--
theorem `toAddMonoidAlgebra_intCast` / 定理 `toAddMonoidAlgebra_intCast`

English:
theorem toAddMonoidAlgebra_intCast
  given: [AddMonoid ι] [Ring M] [forall m : M, Decidable (m != 0)] (z : Int)
  proof: by
  ext : 1; exact DFinsupp.toFinsupp_single ..

@[simp]

中文:
定理 toAddMonoidAlgebra_intCast
  条件: [AddMonoid ι] [Ring M] [对任意 m : M, Decidable (m != 0)] (z : 整数)
  证明: by
  ext : 1; exact DFinsupp.toFinsupp_single ..

@[simp]

Depends on / 依赖: DFinsupp, DFinsupp.toFinsupp_single, toFinsupp_single
-/
theorem toAddMonoidAlgebra_intCast [AddMonoid ι] [Ring M] [forall m : M, Decidable (m != 0)] (z : Int) :
    (z : ⨁ _ : ι, M).toAddMonoidAlgebra = z := by
  ext : 1; exact DFinsupp.toFinsupp_single ..

@[simp]
/--
theorem `toAddMonoidAlgebra_one` / 定理 `toAddMonoidAlgebra_one`

English:
theorem toAddMonoidAlgebra_one
  given: [Zero ι] [Semiring M] [forall m : M, Decidable (m != 0)]
  proof: by
  ext : 1; exact DFinsupp.toFinsupp_single ..

@[simp]

中文:
定理 toAddMonoidAlgebra_one
  条件: [Zero ι] [Semiring M] [对任意 m : M, Decidable (m != 0)]
  证明: by
  ext : 1; exact DFinsupp.toFinsupp_single ..

@[simp]

Depends on / 依赖: DFinsupp, DFinsupp.toFinsupp_single, toFinsupp_single
-/
theorem toAddMonoidAlgebra_one [Zero ι] [Semiring M] [forall m : M, Decidable (m != 0)] :
    (1 : ⨁ _ : ι, M).toAddMonoidAlgebra = 1 := by
  ext : 1; exact DFinsupp.toFinsupp_single ..

@[simp]
/--
theorem `toAddMonoidAlgebra_mul` / 定理 `toAddMonoidAlgebra_mul`

English:
theorem toAddMonoidAlgebra_mul
  statement: [AddMonoid ι] [Semiring M]
  proof: by
  apply_fun AddMonoidAlgebra.toDirectSum
  · simp
  · apply Function.LeftInverse.injective
    apply AddMonoidAlgebra.toDirectSum_toAddMonoidAlgebra

中文:
定理 toAddMonoidAlgebra_mul
  结论: [AddMonoid ι] [Semiring M]
  证明: by
  apply_fun AddMonoidAlgebra.toDirectSum
  · simp
  · apply Function.LeftInverse.injective
    apply AddMonoidAlgebra.toDirectSum_toAddMonoidAlgebra

Depends on / 依赖: AddMonoidAlgebra, AddMonoidAlgebra.toDirectSum, AddMonoidAlgebra.toDirectSum_toAddMonoidAlgebra, Function, Function.LeftInverse.injective, LeftInverse, apply_fun, injective, toDirectSum, toDirectSum_toAddMonoidAlgebra
-/
theorem toAddMonoidAlgebra_mul [AddMonoid ι] [Semiring M]
    [forall m : M, Decidable (m != 0)] (f g : ⨁ _ : ι, M) :
    (f * g).toAddMonoidAlgebra = toAddMonoidAlgebra f * toAddMonoidAlgebra g := by
  apply_fun AddMonoidAlgebra.toDirectSum
  · simp
  · apply Function.LeftInverse.injective
    apply AddMonoidAlgebra.toDirectSum_toAddMonoidAlgebra

end DirectSum

end Lemmas

/-! ### Bundled `Equiv`s -/


section Equivs

/-- `AddMonoidAlgebra.toDirectSum` and `DirectSum.toAddMonoidAlgebra` together form an
equiv. -/
@[simps -fullyApplied]
/--
Definition of `addMonoidAlgebraEquivDirectSum` / `addMonoidAlgebraEquivDirectSum` 的定义

English:
definition addMonoidAlgebraEquivDirectSum
  signature: [DecidableEq ι] [Semiring M] [forall m : M, Decidable (m != 0)]
  body: AddMonoidAlgebra.toDirectSum
  invFun := DirectSum.toAddMonoidAlgebra

中文:
定义 addMonoidAlgebraEquivDirectSum
  签名: [DecidableEq ι] [Semiring M] [对任意 m : M, Decidable (m != 0)]
  定义体: AddMonoidAlgebra.toDirectSum
  invFun := DirectSum.toAddMonoidAlgebra

Depends on / 依赖: AddMonoidAlgebra, AddMonoidAlgebra.toDirectSum, toDirectSum
-/
def addMonoidAlgebraEquivDirectSum [DecidableEq ι] [Semiring M] [forall m : M, Decidable (m != 0)] :
    AddMonoidAlgebra M ι ≃ ⨁ _ : ι, M where
  toFun := AddMonoidAlgebra.toDirectSum
  invFun := DirectSum.toAddMonoidAlgebra

/-- The additive version of `AddMonoidAlgebra.addMonoidAlgebraEquivDirectSum`. -/
@[simps! -fullyApplied]
/--
Definition of `addMonoidAlgebraAddEquivDirectSum` / `addMonoidAlgebraAddEquivDirectSum` 的定义

English:
definition addMonoidAlgebraAddEquivDirectSum
  signature: [DecidableEq ι] [Semiring M] [forall m : M, Decidable (m != 0)]
  body: addMonoidAlgebraEquivDirectSum
  map_add' := AddMonoidAlgebra.toDirectSum_add

中文:
定义 addMonoidAlgebraAddEquivDirectSum
  签名: [DecidableEq ι] [Semiring M] [对任意 m : M, Decidable (m != 0)]
  定义体: addMonoidAlgebraEquivDirectSum
  map_add' := AddMonoidAlgebra.toDirectSum_add

Depends on / 依赖: addMonoidAlgebraEquivDirectSum
-/
def addMonoidAlgebraAddEquivDirectSum [DecidableEq ι] [Semiring M] [forall m : M, Decidable (m != 0)] :
    AddMonoidAlgebra M ι ≃+ ⨁ _ : ι, M where
  toEquiv := addMonoidAlgebraEquivDirectSum
  map_add' := AddMonoidAlgebra.toDirectSum_add

/-- The ring version of `AddMonoidAlgebra.addMonoidAlgebraEquivDirectSum`. -/
@[simps -fullyApplied]
/--
Definition of `addMonoidAlgebraRingEquivDirectSum` / `addMonoidAlgebraRingEquivDirectSum` 的定义

English:
definition addMonoidAlgebraRingEquivDirectSum
  signature: [DecidableEq ι] [AddMonoid ι] [Semiring M]
  body: { (addMonoidAlgebraAddEquivDirectSum : AddMonoidAlgebra M ι ≃+ ⨁ _ : ι, M) with
    toFun := AddMonoidAlgebra.toDirectSum
    invFun := DirectSum.toAddMonoidAlgebra
    map_mul' := AddMonoidAlgebra.toDirectSum_mul }

中文:
定义 addMonoidAlgebraRingEquivDirectSum
  签名: [DecidableEq ι] [AddMonoid ι] [Semiring M]
  定义体: { (addMonoidAlgebraAddEquivDirectSum : AddMonoidAlgebra M ι ≃+ ⨁ _ : ι, M) with
    toFun := AddMonoidAlgebra.toDirectSum
    invFun := DirectSum.toAddMonoidAlgebra
    map_mul' := AddMonoidAlgebra.toDirectSum_mul }

Depends on / 依赖: AddMonoidAlgebra, AddMonoidAlgebra.toDirectSum, AddMonoidAlgebra.toDirectSum_mul, DirectSum, DirectSum.toAddMonoidAlgebra, addMonoidAlgebraAddEquivDirectSum, invFun, map_mul, toAddMonoidAlgebra, toDirectSum, toDirectSum_mul
-/
def addMonoidAlgebraRingEquivDirectSum [DecidableEq ι] [AddMonoid ι] [Semiring M]
    [forall m : M, Decidable (m != 0)] : AddMonoidAlgebra M ι ≃+* ⨁ _ : ι, M :=
  { (addMonoidAlgebraAddEquivDirectSum : AddMonoidAlgebra M ι ≃+ ⨁ _ : ι, M) with
    toFun := AddMonoidAlgebra.toDirectSum
    invFun := DirectSum.toAddMonoidAlgebra
    map_mul' := AddMonoidAlgebra.toDirectSum_mul }

/-- The algebra version of `AddMonoidAlgebra.addMonoidAlgebraEquivDirectSum`. -/
@[simps -fullyApplied]
/--
Definition of `addMonoidAlgebraAlgEquivDirectSum` / `addMonoidAlgebraAlgEquivDirectSum` 的定义

English:
definition addMonoidAlgebraAlgEquivDirectSum
  signature: [DecidableEq ι] [AddMonoid ι] [CommSemiring R] [Semiring A]
  body: { (addMonoidAlgebraRingEquivDirectSum : AddMonoidAlgebra A ι ≃+* ⨁ _ : ι, A) with
    toFun := AddMonoidAlgebra.toDirectSum
    invFun := DirectSum.toAddMonoidAlgebra
    commutes' := fun _r => AddMonoidAlgebra.toDirectSum_single _ _ }

@[simp]

中文:
定义 addMonoidAlgebraAlgEquivDirectSum
  签名: [DecidableEq ι] [AddMonoid ι] [CommSemiring R] [Semiring A]
  定义体: { (addMonoidAlgebraRingEquivDirectSum : AddMonoidAlgebra A ι ≃+* ⨁ _ : ι, A) with
    toFun := AddMonoidAlgebra.toDirectSum
    invFun := DirectSum.toAddMonoidAlgebra
    commutes' := fun _r => AddMonoidAlgebra.toDirectSum_single _ _ }

@[simp]

Depends on / 依赖: AddMonoidAlgebra, AddMonoidAlgebra.toDirectSum, AddMonoidAlgebra.toDirectSum_single, DirectSum, DirectSum.toAddMonoidAlgebra, addMonoidAlgebraRingEquivDirectSum, commutes, invFun, toAddMonoidAlgebra, toDirectSum, toDirectSum_single
-/
def addMonoidAlgebraAlgEquivDirectSum [DecidableEq ι] [AddMonoid ι] [CommSemiring R] [Semiring A]
    [Algebra R A] [forall m : A, Decidable (m != 0)] : AddMonoidAlgebra A ι ≃ₐ[R] ⨁ _ : ι, A :=
  { (addMonoidAlgebraRingEquivDirectSum : AddMonoidAlgebra A ι ≃+* ⨁ _ : ι, A) with
    toFun := AddMonoidAlgebra.toDirectSum
    invFun := DirectSum.toAddMonoidAlgebra
    commutes' := fun _r => AddMonoidAlgebra.toDirectSum_single _ _ }

@[simp]
/--
theorem `AddMonoidAlgebra.toDirectSum_pow` / 定理 `AddMonoidAlgebra.toDirectSum_pow`

English:
theorem AddMonoidAlgebra.toDirectSum_pow
  statement: [DecidableEq ι] [AddMonoid ι] [Semiring M]
  proof: by
  classical exact map_pow addMonoidAlgebraRingEquivDirectSum f n

@[simp]

中文:
定理 AddMonoidAlgebra.toDirectSum_pow
  结论: [DecidableEq ι] [AddMonoid ι] [Semiring M]
  证明: by
  classical exact map_pow addMonoidAlgebraRingEquivDirectSum f n

@[simp]

Depends on / 依赖: addMonoidAlgebraRingEquivDirectSum, classical, map_pow
-/
theorem AddMonoidAlgebra.toDirectSum_pow [DecidableEq ι] [AddMonoid ι] [Semiring M]
    (f : AddMonoidAlgebra M ι) (n : Nat) :
    (f ^ n).toDirectSum = f.toDirectSum ^ n := by
  classical exact map_pow addMonoidAlgebraRingEquivDirectSum f n

@[simp]
/--
theorem `DirectSum.toAddMonoidAlgebra_pow` / 定理 `DirectSum.toAddMonoidAlgebra_pow`

English:
theorem DirectSum.toAddMonoidAlgebra_pow
  statement: [DecidableEq ι] [AddMonoid ι] [Semiring M]
  proof: by
  exact map_pow addMonoidAlgebraRingEquivDirectSum.symm f n

中文:
定理 DirectSum.toAddMonoidAlgebra_pow
  结论: [DecidableEq ι] [AddMonoid ι] [Semiring M]
  证明: by
  exact map_pow addMonoidAlgebraRingEquivDirectSum.symm f n

Depends on / 依赖: addMonoidAlgebraRingEquivDirectSum, addMonoidAlgebraRingEquivDirectSum.symm, map_pow
-/
theorem DirectSum.toAddMonoidAlgebra_pow [DecidableEq ι] [AddMonoid ι] [Semiring M]
    [forall m : M, Decidable (m != 0)] (f : ⨁ _ : ι, M) (n : Nat) :
    (f ^ n).toAddMonoidAlgebra = toAddMonoidAlgebra f ^ n := by
  exact map_pow addMonoidAlgebraRingEquivDirectSum.symm f n

end Equivs
