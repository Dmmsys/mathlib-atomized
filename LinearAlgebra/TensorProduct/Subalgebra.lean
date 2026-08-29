/-
Copyright (c) 2024 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Submodule
public import Mathlib.RingTheory.TensorProduct.Maps

/-!

# Some results on tensor product of subalgebras

## Linear maps induced by multiplication for subalgebras

Let `R` be a commutative ring, `S` be a commutative `R`-algebra.
Let `A` and `B` be `R`-subalgebras in `S` (`Subalgebra R S`). We define some linear maps
induced by the multiplication in `S`, which are
mainly used in the definition of linearly disjointness.

- `Subalgebra.mulMap`: the natural `R`-algebra homomorphism `A ⊗[R] B →ₐ[R] S`
  induced by the multiplication in `S`, whose image is `A ⊔ B` (`Subalgebra.mulMap_range`).

- `Subalgebra.mulMap'`: the natural `R`-algebra homomorphism `A ⊗[R] B →ₗ[R] A ⊔ B`
  induced by multiplication in `S`, which is surjective (`Subalgebra.mulMap'_surjective`).

- `Subalgebra.lTensorBot`, `Subalgebra.rTensorBot`: the natural isomorphism of `R`-algebras between
  `i(R) ⊗[R] A` and `A`, resp. `A ⊗[R] i(R)` and `A`, induced by multiplication in `S`,
  here `i : R → S` is the structure map. They generalize `Algebra.TensorProduct.lid`
  and `Algebra.TensorProduct.rid`, as `i(R)` is not necessarily isomorphic to `R`.

  They are `Subalgebra` versions of `Submodule.lTensorOne` and `Submodule.rTensorOne`.

-/

@[expose] public section

open scoped TensorProduct

open Module

noncomputable section

variable {R S T : Type*}

section Semiring

variable [CommSemiring R] [Semiring S] [Algebra R S] [Semiring T] [Algebra R T]

namespace Subalgebra

variable (A : Subalgebra R S)

/--
Definition of `lTensorBot` / `lTensorBot` 的定义

English:
definition lTensorBot
  signature: : (⊥ : Subalgebra R S) otimes[R] A ≃ₐ[R] A
  body: by
  refine Algebra.TensorProduct.algEquivOfLinearEquivTensorProduct (toSubmodule A).lTensorOne ?_ ?_
  · rintro x y a b
    obtain ⟨x', hx⟩ := Algebra.mem_bot.1 x.2
    replace hx : algebraMap R _ x' = x := Subtype.val_injective hx
    obtain ⟨y', hy⟩ := Algebra.mem_bot.1 y.2
    replace hy : algeb

中文:
定义 lTensorBot
  签名: : (⊥ : Subalgebra R S) otimes[R] A ≃ₐ[R] A
  定义体: by
  refine Algebra.TensorProduct.algEquivOfLinearEquivTensorProduct (toSubmodule A).lTensorOne ?_ ?_
  · rintro x y a b
    obtain ⟨x', hx⟩ := Algebra.mem_bot.1 x.2
    replace hx : algebraMap R _ x' = x := Subtype.val_injective hx
    obtain ⟨y', hy⟩ := Algebra.mem_bot.1 y.2
    replace hy : algeb

Depends on / 依赖: Algebra, Algebra.TensorProduct.algEquivOfLinearEquivTensorProduct, Algebra.mem_bot, Subtype, Subtype.val_injective, TensorProduct, algEquivOfLinearEquivTensorProduct, algebraMap, lTensorOne, lTensorOne_tmul, map_mul, mem_bot, replace, toSubmodule, val_injective
-/
def lTensorBot : (⊥ : Subalgebra R S) otimes[R] A ≃ₐ[R] A := by
  refine Algebra.TensorProduct.algEquivOfLinearEquivTensorProduct (toSubmodule A).lTensorOne ?_ ?_
  · rintro x y a b
    obtain ⟨x', hx⟩ := Algebra.mem_bot.1 x.2
    replace hx : algebraMap R _ x' = x := Subtype.val_injective hx
    obtain ⟨y', hy⟩ := Algebra.mem_bot.1 y.2
    replace hy : algebraMap R _ y' = y := Subtype.val_injective hy
    rw [← hx]; rw [← hy]; rw [← map_mul]; rw [(toSubmodule A).lTensorOne_tmul x' a]; rw [(toSubmodule A).lTensorOne_tmul y' b]; rw [(toSubmodule A).lTensorOne_tmul (x' * y') (a * b)]; rw [Algebra.mul_smul_comm]; rw [Algebra.smul_mul_assoc]; rw [smul_smul]; rw [mul_comm x' y']
  · exact Submodule.lTensorOne_one_tmul _

variable {A}

@[simp]
/--
theorem `lTensorBot_tmul` / 定理 `lTensorBot_tmul`

English:
theorem lTensorBot_tmul
  given: (x : R) (a : A)
  statement: A.lTensorBot (algebraMap R _ x otimesₜ[R] a) = x • a
  proof: (toSubmodule A).lTensorOne_tmul x a

@[simp]

中文:
定理 lTensorBot_tmul
  条件: (x : R) (a : A)
  结论: A.lTensorBot (algebraMap R _ x otimesₜ[R] a) = x • a
  证明: (toSubmodule A).lTensorOne_tmul x a

@[simp]

Depends on / 依赖: lTensorOne_tmul, toSubmodule
-/
theorem lTensorBot_tmul (x : R) (a : A) : A.lTensorBot (algebraMap R _ x otimesₜ[R] a) = x • a :=
  (toSubmodule A).lTensorOne_tmul x a

@[simp]
/--
theorem `lTensorBot_one_tmul` / 定理 `lTensorBot_one_tmul`

English:
theorem lTensorBot_one_tmul
  given: (a : A)
  statement: A.lTensorBot (1 otimesₜ[R] a) = a
  proof: (toSubmodule A).lTensorOne_one_tmul a

@[simp]

中文:
定理 lTensorBot_one_tmul
  条件: (a : A)
  结论: A.lTensorBot (1 otimesₜ[R] a) = a
  证明: (toSubmodule A).lTensorOne_one_tmul a

@[simp]

Depends on / 依赖: lTensorOne_one_tmul, toSubmodule
-/
theorem lTensorBot_one_tmul (a : A) : A.lTensorBot (1 otimesₜ[R] a) = a :=
  (toSubmodule A).lTensorOne_one_tmul a

@[simp]
/--
theorem `lTensorBot_symm_apply` / 定理 `lTensorBot_symm_apply`

English:
theorem lTensorBot_symm_apply
  given: (a : A)
  statement: A.lTensorBot.symm a = 1 otimesₜ[R] a
  proof: rfl

中文:
定理 lTensorBot_symm_apply
  条件: (a : A)
  结论: A.lTensorBot.symm a = 1 otimesₜ[R] a
  证明: rfl
-/
theorem lTensorBot_symm_apply (a : A) : A.lTensorBot.symm a = 1 otimesₜ[R] a := rfl

variable (A) in
/--
Definition of `rTensorBot` / `rTensorBot` 的定义

English:
definition rTensorBot
  signature: : A otimes[R] (⊥ : Subalgebra R S) ≃ₐ[R] A
  body: by
  refine Algebra.TensorProduct.algEquivOfLinearEquivTensorProduct (toSubmodule A).rTensorOne ?_ ?_
  · rintro a b x y
    obtain ⟨x', hx⟩ := Algebra.mem_bot.1 x.2
    replace hx : algebraMap R _ x' = x := Subtype.val_injective hx
    obtain ⟨y', hy⟩ := Algebra.mem_bot.1 y.2
    replace hy : algeb

中文:
定义 rTensorBot
  签名: : A otimes[R] (⊥ : Subalgebra R S) ≃ₐ[R] A
  定义体: by
  refine Algebra.TensorProduct.algEquivOfLinearEquivTensorProduct (toSubmodule A).rTensorOne ?_ ?_
  · rintro a b x y
    obtain ⟨x', hx⟩ := Algebra.mem_bot.1 x.2
    replace hx : algebraMap R _ x' = x := Subtype.val_injective hx
    obtain ⟨y', hy⟩ := Algebra.mem_bot.1 y.2
    replace hy : algeb

Depends on / 依赖: Algebra, Algebra.TensorProduct.algEquivOfLinearEquivTensorProduct, Algebra.mem_bot, Subtype, Subtype.val_injective, TensorProduct, algEquivOfLinearEquivTensorProduct, algebraMap, map_mul, mem_bot, rTensorOne, rTensorOne_tmul, replace, toSubmodule, val_injective
-/
def rTensorBot : A otimes[R] (⊥ : Subalgebra R S) ≃ₐ[R] A := by
  refine Algebra.TensorProduct.algEquivOfLinearEquivTensorProduct (toSubmodule A).rTensorOne ?_ ?_
  · rintro a b x y
    obtain ⟨x', hx⟩ := Algebra.mem_bot.1 x.2
    replace hx : algebraMap R _ x' = x := Subtype.val_injective hx
    obtain ⟨y', hy⟩ := Algebra.mem_bot.1 y.2
    replace hy : algebraMap R _ y' = y := Subtype.val_injective hy
    rw [← hx]; rw [← hy]; rw [← map_mul]; rw [(toSubmodule A).rTensorOne_tmul x' a]; rw [(toSubmodule A).rTensorOne_tmul y' b]; rw [(toSubmodule A).rTensorOne_tmul (x' * y') (a * b)]; rw [Algebra.mul_smul_comm]; rw [Algebra.smul_mul_assoc]; rw [smul_smul]; rw [mul_comm x' y']
  · exact Submodule.rTensorOne_tmul_one _

@[simp]
/--
theorem `rTensorBot_tmul` / 定理 `rTensorBot_tmul`

English:
theorem rTensorBot_tmul
  given: (x : R) (a : A)
  statement: A.rTensorBot (a otimesₜ[R] algebraMap R _ x) = x • a
  proof: (toSubmodule A).rTensorOne_tmul x a

@[simp]

中文:
定理 rTensorBot_tmul
  条件: (x : R) (a : A)
  结论: A.rTensorBot (a otimesₜ[R] algebraMap R _ x) = x • a
  证明: (toSubmodule A).rTensorOne_tmul x a

@[simp]

Depends on / 依赖: rTensorOne_tmul, toSubmodule
-/
theorem rTensorBot_tmul (x : R) (a : A) : A.rTensorBot (a otimesₜ[R] algebraMap R _ x) = x • a :=
  (toSubmodule A).rTensorOne_tmul x a

@[simp]
/--
theorem `rTensorBot_tmul_one` / 定理 `rTensorBot_tmul_one`

English:
theorem rTensorBot_tmul_one
  given: (a : A)
  statement: A.rTensorBot (a otimesₜ[R] 1) = a
  proof: (toSubmodule A).rTensorOne_tmul_one a

@[simp]

中文:
定理 rTensorBot_tmul_one
  条件: (a : A)
  结论: A.rTensorBot (a otimesₜ[R] 1) = a
  证明: (toSubmodule A).rTensorOne_tmul_one a

@[simp]

Depends on / 依赖: rTensorOne_tmul_one, toSubmodule
-/
theorem rTensorBot_tmul_one (a : A) : A.rTensorBot (a otimesₜ[R] 1) = a :=
  (toSubmodule A).rTensorOne_tmul_one a

@[simp]
/--
theorem `rTensorBot_symm_apply` / 定理 `rTensorBot_symm_apply`

English:
theorem rTensorBot_symm_apply
  given: (a : A)
  statement: A.rTensorBot.symm a = a otimesₜ[R] 1
  proof: rfl

中文:
定理 rTensorBot_symm_apply
  条件: (a : A)
  结论: A.rTensorBot.symm a = a otimesₜ[R] 1
  证明: rfl
-/
theorem rTensorBot_symm_apply (a : A) : A.rTensorBot.symm a = a otimesₜ[R] 1 := rfl

variable (A)

@[simp]
/--
theorem `comm_trans_lTensorBot` / 定理 `comm_trans_lTensorBot`

English:
theorem comm_trans_lTensorBot
  proof: AlgEquiv.toLinearEquiv_injective (toSubmodule A).comm_trans_lTensorOne

@[simp]

中文:
定理 comm_trans_lTensorBot
  证明: AlgEquiv.toLinearEquiv_injective (toSubmodule A).comm_trans_lTensorOne

@[simp]

Depends on / 依赖: AlgEquiv, AlgEquiv.toLinearEquiv_injective, comm_trans_lTensorOne, toLinearEquiv_injective, toSubmodule
-/
theorem comm_trans_lTensorBot :
    (Algebra.TensorProduct.comm R _ _).trans A.lTensorBot = A.rTensorBot :=
  AlgEquiv.toLinearEquiv_injective (toSubmodule A).comm_trans_lTensorOne

@[simp]
/--
theorem `comm_trans_rTensorBot` / 定理 `comm_trans_rTensorBot`

English:
theorem comm_trans_rTensorBot
  proof: AlgEquiv.toLinearEquiv_injective (toSubmodule A).comm_trans_rTensorOne

中文:
定理 comm_trans_rTensorBot
  证明: AlgEquiv.toLinearEquiv_injective (toSubmodule A).comm_trans_rTensorOne

Depends on / 依赖: AlgEquiv, AlgEquiv.toLinearEquiv_injective, comm_trans_rTensorOne, toLinearEquiv_injective, toSubmodule
-/
theorem comm_trans_rTensorBot :
    (Algebra.TensorProduct.comm R _ _).trans A.rTensorBot = A.lTensorBot :=
  AlgEquiv.toLinearEquiv_injective (toSubmodule A).comm_trans_rTensorOne

end Subalgebra

namespace Algebra.TensorProduct

variable (R S T)

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `linearEquivIncludeRange` / `linearEquivIncludeRange` 的定义

English:
definition linearEquivIncludeRange
  signature: :
  body: .ofLinearMap
  (_root_.TensorProduct.map
    includeLeft.toLinearMap.rangeRestrict includeRight.toLinearMap.rangeRestrict)
  (includeLeft.toLinearMap.range.mulMap includeRight.toLinearMap.range)
  (_root_.TensorProduct.ext' <| by
    rintro ⟨x', x, rfl : x otimesₜ 1 = x'⟩ ⟨y', y, rfl : 1 otimesₜ y =

中文:
定义 linearEquivIncludeRange
  签名: :
  定义体: .ofLinearMap
  (_root_.TensorProduct.map
    includeLeft.toLinearMap.rangeRestrict includeRight.toLinearMap.rangeRestrict)
  (includeLeft.toLinearMap.range.mulMap includeRight.toLinearMap.range)
  (_root_.TensorProduct.ext' <| by
    rintro ⟨x', x, rfl : x otimesₜ 1 = x'⟩ ⟨y', y, rfl : 1 otimesₜ y =

Depends on / 依赖: ofLinearMap
-/
def linearEquivIncludeRange :
    S otimes[R] T ≃ₗ[R] (includeLeft : S ->ₐ[R] S otimes[R] T).range otimes[R]
      (includeRight : T ->ₐ[R] S otimes[R] T).range := .ofLinearMap
  (_root_.TensorProduct.map
    includeLeft.toLinearMap.rangeRestrict includeRight.toLinearMap.rangeRestrict)
  (includeLeft.toLinearMap.range.mulMap includeRight.toLinearMap.range)
  (_root_.TensorProduct.ext' <| by
    rintro ⟨x', x, rfl : x otimesₜ 1 = x'⟩ ⟨y', y, rfl : 1 otimesₜ y = y'⟩
    rw [LinearMap.comp_apply]; rw [LinearMap.id_apply]
    erw [Submodule.mulMap_tmul]
    rw [tmul_mul_tmul]; rw [mul_one]; rw [one_mul]; rw [_root_.TensorProduct.map_tmul]
    rfl)
  (_root_.TensorProduct.ext' fun x y => by
    rw [LinearMap.comp_apply]; rw [LinearMap.id_apply]; rw [_root_.TensorProduct.map_tmul]
    erw [Submodule.mulMap_tmul]
    change (x otimesₜ 1) * (1 otimesₜ y) = _
    rw [tmul_mul_tmul]; rw [mul_one]; rw [one_mul])

/--
theorem `linearEquivIncludeRange_toLinearMap` / 定理 `linearEquivIncludeRange_toLinearMap`

English:
theorem linearEquivIncludeRange_toLinearMap
  proof: rfl

中文:
定理 linearEquivIncludeRange_toLinearMap
  证明: rfl
-/
theorem linearEquivIncludeRange_toLinearMap :
    (linearEquivIncludeRange R S T).toLinearMap =
      _root_.TensorProduct.map includeLeft.toLinearMap.rangeRestrict
        includeRight.toLinearMap.rangeRestrict := rfl

/--
theorem `linearEquivIncludeRange_symm_toLinearMap` / 定理 `linearEquivIncludeRange_symm_toLinearMap`

English:
theorem linearEquivIncludeRange_symm_toLinearMap
  proof: rfl

@[simp]

中文:
定理 linearEquivIncludeRange_symm_toLinearMap
  证明: rfl

@[simp]
-/
theorem linearEquivIncludeRange_symm_toLinearMap :
    (linearEquivIncludeRange R S T).symm.toLinearMap =
      includeLeft.toLinearMap.range.mulMap includeRight.toLinearMap.range := rfl

@[simp]
/--
theorem `linearEquivIncludeRange_tmul` / 定理 `linearEquivIncludeRange_tmul`

English:
theorem linearEquivIncludeRange_tmul
  given: (x y)
  proof: rfl

@[simp]

中文:
定理 linearEquivIncludeRange_tmul
  条件: (x y)
  证明: rfl

@[simp]
-/
theorem linearEquivIncludeRange_tmul (x y) :
    linearEquivIncludeRange R S T (x otimesₜ[R] y) =
      ((includeLeft : S ->ₐ[R] S otimes[R] T).rangeRestrict x) otimesₜ[R]
        ((includeRight : T ->ₐ[R] S otimes[R] T).rangeRestrict y) := rfl

@[simp]
/--
theorem `linearEquivIncludeRange_symm_tmul` / 定理 `linearEquivIncludeRange_symm_tmul`

English:
theorem linearEquivIncludeRange_symm_tmul
  given: (x y)
  proof: rfl

中文:
定理 linearEquivIncludeRange_symm_tmul
  条件: (x y)
  证明: rfl
-/
theorem linearEquivIncludeRange_symm_tmul (x y) :
    (linearEquivIncludeRange R S T).symm (x otimesₜ[R] y) = x.1 * y.1 := rfl

/--
Definition of `algEquivIncludeRange` / `algEquivIncludeRange` 的定义

English:
definition algEquivIncludeRange
  signature: :
  body: algEquivOfLinearEquivTensorProduct (linearEquivIncludeRange R S T) (by simp) rfl

中文:
定义 algEquivIncludeRange
  签名: :
  定义体: algEquivOfLinearEquivTensorProduct (linearEquivIncludeRange R S T) (by simp) rfl

Depends on / 依赖: algEquivOfLinearEquivTensorProduct, linearEquivIncludeRange
-/
def algEquivIncludeRange :
    S otimes[R] T ≃ₐ[R] (includeLeft : S ->ₐ[R] S otimes[R] T).range otimes[R]
      (includeRight : T ->ₐ[R] S otimes[R] T).range :=
  algEquivOfLinearEquivTensorProduct (linearEquivIncludeRange R S T) (by simp) rfl

/--
theorem `algEquivIncludeRange_toAlgHom` / 定理 `algEquivIncludeRange_toAlgHom`

English:
theorem algEquivIncludeRange_toAlgHom
  proof: rfl

@[simp]

中文:
定理 algEquivIncludeRange_toAlgHom
  证明: rfl

@[simp]
-/
theorem algEquivIncludeRange_toAlgHom :
    (algEquivIncludeRange R S T).toAlgHom =
      map includeLeft.rangeRestrict includeRight.rangeRestrict := rfl

@[simp]
/--
theorem `algEquivIncludeRange_tmul` / 定理 `algEquivIncludeRange_tmul`

English:
theorem algEquivIncludeRange_tmul
  given: (x y)
  proof: rfl

@[simp]

中文:
定理 algEquivIncludeRange_tmul
  条件: (x y)
  证明: rfl

@[simp]
-/
theorem algEquivIncludeRange_tmul (x y) :
    algEquivIncludeRange R S T (x otimesₜ[R] y) =
      ((includeLeft : S ->ₐ[R] S otimes[R] T).rangeRestrict x) otimesₜ[R]
        ((includeRight : T ->ₐ[R] S otimes[R] T).rangeRestrict y) := rfl

@[simp]
/--
theorem `algEquivIncludeRange_symm_tmul` / 定理 `algEquivIncludeRange_symm_tmul`

English:
theorem algEquivIncludeRange_symm_tmul
  given: (x y)
  proof: rfl

中文:
定理 algEquivIncludeRange_symm_tmul
  条件: (x y)
  证明: rfl
-/
theorem algEquivIncludeRange_symm_tmul (x y) :
    (algEquivIncludeRange R S T).symm (x otimesₜ[R] y) = x.1 * y.1 := rfl

end Algebra.TensorProduct

end Semiring

section CommSemiring

variable [CommSemiring R] [CommSemiring S] [Algebra R S] [CommSemiring T] [Algebra R T]

variable (A B : Subalgebra R S)

/--
Definition of `Subalgebra.mulMap` / `Subalgebra.mulMap` 的定义

English:
definition Subalgebra.mulMap
  signature: : A otimes[R] B ->ₐ[R] S
  body: Algebra.TensorProduct.productMap A.val B.val

中文:
定义 Subalgebra.mulMap
  签名: : A otimes[R] B ->ₐ[R] S
  定义体: Algebra.TensorProduct.productMap A.val B.val

Depends on / 依赖: A.val, Algebra, Algebra.TensorProduct.productMap, B.val, TensorProduct, productMap
-/
def Subalgebra.mulMap : A otimes[R] B ->ₐ[R] S := Algebra.TensorProduct.productMap A.val B.val

variable (R S T) in
/--
theorem `Algebra.TensorProduct.algEquivIncludeRange_symm_toAlgHom` / 定理 `Algebra.TensorProduct.algEquivIncludeRange_symm_toAlgHom`

English:
theorem Algebra.TensorProduct.algEquivIncludeRange_symm_toAlgHom
  proof: rfl

中文:
定理 Algebra.TensorProduct.algEquivIncludeRange_symm_toAlgHom
  证明: rfl
-/
theorem Algebra.TensorProduct.algEquivIncludeRange_symm_toAlgHom :
    (algEquivIncludeRange R S T).symm.toAlgHom =
      (includeLeft : S ->ₐ[R] S otimes[R] T).range.mulMap includeRight.range := rfl

namespace Subalgebra

@[simp]
/--
theorem `mulMap_tmul` / 定理 `mulMap_tmul`

English:
theorem mulMap_tmul
  given: (a : A) (b : B)
  statement: mulMap A B (a otimesₜ[R] b) = a.1 * b.1
  proof: rfl

中文:
定理 mulMap_tmul
  条件: (a : A) (b : B)
  结论: mulMap A B (a otimesₜ[R] b) = a.1 * b.1
  证明: rfl
-/
theorem mulMap_tmul (a : A) (b : B) : mulMap A B (a otimesₜ[R] b) = a.1 * b.1 := rfl

/--
theorem `mulMap_map_comp_eq` / 定理 `mulMap_map_comp_eq`

English:
theorem mulMap_map_comp_eq
  given: (f : S ->ₐ[R] T)
  proof: by
  ext <;> simp

中文:
定理 mulMap_map_comp_eq
  条件: (f : S ->ₐ[R] T)
  证明: by
  ext <;> simp
-/
theorem mulMap_map_comp_eq (f : S ->ₐ[R] T) :
    (mulMap (A.map f) (B.map f)).comp
      (Algebra.TensorProduct.map (f.subalgebraMap A) (f.subalgebraMap B))
        = f.comp (mulMap A B) := by
  ext <;> simp

/--
theorem `mulMap_toLinearMap` / 定理 `mulMap_toLinearMap`

English:
theorem mulMap_toLinearMap
  statement: (A.mulMap B).toLinearMap = (toSubmodule A).mulMap (toSubmodule B)
  proof: rfl

中文:
定理 mulMap_toLinearMap
  结论: (A.mulMap B).toLinearMap = (toSubmodule A).mulMap (toSubmodule B)
  证明: rfl
-/
theorem mulMap_toLinearMap : (A.mulMap B).toLinearMap = (toSubmodule A).mulMap (toSubmodule B) :=
  rfl

/--
theorem `mulMap_comm` / 定理 `mulMap_comm`

English:
theorem mulMap_comm
  statement: mulMap B A = (mulMap A B).comp (Algebra.TensorProduct.comm R B A)
  proof: by
  ext <;> simp

中文:
定理 mulMap_comm
  结论: mulMap B A = (mulMap A B).comp (Algebra.TensorProduct.comm R B A)
  证明: by
  ext <;> simp
-/
theorem mulMap_comm : mulMap B A = (mulMap A B).comp (Algebra.TensorProduct.comm R B A) := by
  ext <;> simp

/--
theorem `mulMap_range` / 定理 `mulMap_range`

English:
theorem mulMap_range
  statement: (A.mulMap B).range = A ⊔ B
  proof: by
  simp_rw [mulMap, Algebra.TensorProduct.productMap_range, Subalgebra.range_val]

中文:
定理 mulMap_range
  结论: (A.mulMap B).range = A ⊔ B
  证明: by
  simp_rw [mulMap, Algebra.TensorProduct.productMap_range, Subalgebra.range_val]

Depends on / 依赖: Algebra, Algebra.TensorProduct.productMap_range, Subalgebra, Subalgebra.range_val, TensorProduct, mulMap, productMap_range, range_val, simp_rw
-/
theorem mulMap_range : (A.mulMap B).range = A ⊔ B := by
  simp_rw [mulMap, Algebra.TensorProduct.productMap_range, Subalgebra.range_val]

/--
theorem `mulMap_bot_left_eq` / 定理 `mulMap_bot_left_eq`

English:
theorem mulMap_bot_left_eq
  statement: mulMap ⊥ A = A.val.comp A.lTensorBot.toAlgHom
  proof: AlgHom.toLinearMap_injective (toSubmodule A).mulMap_one_left_eq

中文:
定理 mulMap_bot_left_eq
  结论: mulMap ⊥ A = A.val.comp A.lTensorBot.toAlgHom
  证明: AlgHom.toLinearMap_injective (toSubmodule A).mulMap_one_left_eq

Depends on / 依赖: AlgHom, AlgHom.toLinearMap_injective, mulMap_one_left_eq, toLinearMap_injective, toSubmodule
-/
theorem mulMap_bot_left_eq : mulMap ⊥ A = A.val.comp A.lTensorBot.toAlgHom :=
  AlgHom.toLinearMap_injective (toSubmodule A).mulMap_one_left_eq

/--
theorem `mulMap_bot_right_eq` / 定理 `mulMap_bot_right_eq`

English:
theorem mulMap_bot_right_eq
  statement: mulMap A ⊥ = A.val.comp A.rTensorBot.toAlgHom
  proof: AlgHom.toLinearMap_injective (toSubmodule A).mulMap_one_right_eq

中文:
定理 mulMap_bot_right_eq
  结论: mulMap A ⊥ = A.val.comp A.rTensorBot.toAlgHom
  证明: AlgHom.toLinearMap_injective (toSubmodule A).mulMap_one_right_eq

Depends on / 依赖: AlgHom, AlgHom.toLinearMap_injective, mulMap_one_right_eq, toLinearMap_injective, toSubmodule
-/
theorem mulMap_bot_right_eq : mulMap A ⊥ = A.val.comp A.rTensorBot.toAlgHom :=
  AlgHom.toLinearMap_injective (toSubmodule A).mulMap_one_right_eq

/--
Definition of `mulMap'` / `mulMap'` 的定义

English:
definition mulMap'
  signature: : A otimes[R] B ->ₐ[R] ↥(A ⊔ B)
  body: (equivOfEq _ _ (mulMap_range A B)).toAlgHom.comp (mulMap A B).rangeRestrict

中文:
定义 mulMap'
  签名: : A otimes[R] B ->ₐ[R] ↥(A ⊔ B)
  定义体: (equivOfEq _ _ (mulMap_range A B)).toAlgHom.comp (mulMap A B).rangeRestrict

Depends on / 依赖: equivOfEq, mulMap, mulMap_range, rangeRestrict, toAlgHom, toAlgHom.comp
-/
def mulMap' : A otimes[R] B ->ₐ[R] ↥(A ⊔ B) :=
  (equivOfEq _ _ (mulMap_range A B)).toAlgHom.comp (mulMap A B).rangeRestrict

variable {A B} in
@[simp]
/--
theorem `val_mulMap'_tmul` / 定理 `val_mulMap'_tmul`

English:
theorem val_mulMap'_tmul
  given: (a : A) (b : B)
  statement: (mulMap' A B (a otimesₜ[R] b) : S) = a.1 * b.1
  proof: rfl

中文:
定理 val_mulMap'_tmul
  条件: (a : A) (b : B)
  结论: (mulMap' A B (a otimesₜ[R] b) : S) = a.1 * b.1
  证明: rfl
-/
theorem val_mulMap'_tmul (a : A) (b : B) : (mulMap' A B (a otimesₜ[R] b) : S) = a.1 * b.1 := rfl

/--
theorem `mulMap'_surjective` / 定理 `mulMap'_surjective`

English:
theorem mulMap'_surjective
  statement: Function.Surjective (mulMap' A B)
  proof: by
  simp_rw [mulMap', AlgHom.coe_comp, AlgEquiv.coe_toAlgHom,
    EquivLike.comp_surjective, AlgHom.rangeRestrict_surjective]

中文:
定理 mulMap'_surjective
  结论: Function.Surjective (mulMap' A B)
  证明: by
  simp_rw [mulMap', AlgHom.coe_comp, AlgEquiv.coe_toAlgHom,
    EquivLike.comp_surjective, AlgHom.rangeRestrict_surjective]
-/
theorem mulMap'_surjective : Function.Surjective (mulMap' A B) := by
  simp_rw [mulMap', AlgHom.coe_comp, AlgEquiv.coe_toAlgHom,
    EquivLike.comp_surjective, AlgHom.rangeRestrict_surjective]

end Subalgebra

end CommSemiring
