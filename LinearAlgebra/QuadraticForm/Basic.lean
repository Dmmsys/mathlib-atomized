/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Kexing Ying, Eric Wieser
-/
module

public import Mathlib.Data.Finset.Sym
public import Mathlib.LinearAlgebra.SesquilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
public import Mathlib.LinearAlgebra.Matrix.Symmetric

/-!
# Quadratic maps

This file defines quadratic maps on an `R`-module `M`, taking values in an `R`-module `N`.
An `N`-valued quadratic map on a module `M` over a commutative ring `R` is a map `Q : M → N` such
that:

* `QuadraticMap.map_smul`: `Q (a • x) = (a * a) • Q x`
* `QuadraticMap.polar_add_left`, `QuadraticMap.polar_add_right`,
  `QuadraticMap.polar_smul_left`, `QuadraticMap.polar_smul_right`:
  the map `QuadraticMap.polar Q := fun x y ↦ Q (x + y) - Q x - Q y` is bilinear.

This notion generalizes to commutative semirings using the approach in [izhakian2016][] which
requires that there be a (possibly non-unique) companion bilinear map `B` such that
`∀ x y, Q (x + y) = Q x + Q y + B x y`. Over a ring, this `B` is precisely `QuadraticMap.polar Q`.

To build a `QuadraticMap` from the `polar` axioms, use `QuadraticMap.ofPolar`.

Quadratic maps come with a scalar multiplication, `(a • Q) x = a • Q x`,
and composition with linear maps `f`, `Q.comp f x = Q (f x)`.

## Main definitions

* `QuadraticMap.ofPolar`: a more familiar constructor that works on rings
* `QuadraticMap.associated`: associated bilinear map
* `QuadraticMap.PosDef`: positive definite quadratic maps
* `QuadraticMap.Anisotropic`: anisotropic quadratic maps
* `QuadraticMap.discr`: discriminant of a quadratic map
* `QuadraticMap.IsOrtho`: orthogonality of vectors with respect to a quadratic map.

## Main statements

* `QuadraticMap.associated_left_inverse`,
* `QuadraticMap.associated_rightInverse`: in a commutative ring where 2 has
  an inverse, there is a correspondence between quadratic maps and symmetric
  bilinear forms
* `LinearMap.BilinForm.exists_orthogonal_basis`: There exists an orthogonal basis with
  respect to any nondegenerate, symmetric bilinear map `B`.

## Notation

In this file, the variable `R` is used when a `CommSemiring` structure is available.

The variable `S` is used when `R` itself has a `•` action.

## Implementation notes

While the definition and many results make sense if we drop commutativity assumptions,
the correct definition of a quadratic maps in the noncommutative setting would require
substantial refactors from the current version, such that $Q(rm) = rQ(m)r^*$ for some
suitable conjugation $r^*$.

The [Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Quadratic.20Maps/near/395529867)
has some further discussion.

## References

* https://en.wikipedia.org/wiki/Quadratic_form
* https://en.wikipedia.org/wiki/Discriminant#Quadratic_forms

## Tags

quadratic map, homogeneous polynomial, quadratic polynomial
-/

@[expose] public section

universe u v w

variable {S T : Type*}
variable {R : Type*} {M N P A : Type*}

open LinearMap (BilinMap BilinForm)

section Polar

variable [CommRing R] [AddCommGroup M] [AddCommGroup N]

namespace QuadraticMap

/--
Definition of `polar` / `polar` 的定义

English:
definition polar
  signature: (f : M -> N) (x y : M)
  body: f (x + y) - f x - f y

中文:
定义 polar
  签名: (f : M -> N) (x y : M)
  定义体: f (x + y) - f x - f y
-/
def polar (f : M -> N) (x y : M) :=
  f (x + y) - f x - f y

/--
theorem `map_add` / 定理 `map_add`

English:
theorem map_add
  given: (f : M -> N) (x y : M)
  proof: by
  rw [polar]
  abel

中文:
定理 map_add
  条件: (f : M -> N) (x y : M)
  证明: by
  rw [polar]
  abel
-/
protected theorem map_add (f : M -> N) (x y : M) :
    f (x + y) = f x + f y + polar f x y := by
  rw [polar]
  abel

/--
theorem `polar_add` / 定理 `polar_add`

English:
theorem polar_add
  given: (f g : M -> N) (x y : M)
  statement: polar (f + g) x y = polar f x y + polar g x y
  proof: by
  simp only [polar, Pi.add_apply]
  abel

中文:
定理 polar_add
  条件: (f g : M -> N) (x y : M)
  结论: polar (f + g) x y = polar f x y + polar g x y
  证明: by
  simp only [polar, Pi.add_apply]
  abel

Depends on / 依赖: Pi.add_apply, add_apply
-/
theorem polar_add (f g : M -> N) (x y : M) : polar (f + g) x y = polar f x y + polar g x y := by
  simp only [polar, Pi.add_apply]
  abel

/--
theorem `polar_neg` / 定理 `polar_neg`

English:
theorem polar_neg
  given: (f : M -> N) (x y : M)
  statement: polar (-f) x y = -polar f x y
  proof: by
  simp only [polar, Pi.neg_apply, sub_eq_add_neg, neg_add]

中文:
定理 polar_neg
  条件: (f : M -> N) (x y : M)
  结论: polar (-f) x y = -polar f x y
  证明: by
  simp only [polar, Pi.neg_apply, sub_eq_add_neg, neg_add]

Depends on / 依赖: Pi.neg_apply, neg_add, neg_apply, sub_eq_add_neg
-/
theorem polar_neg (f : M -> N) (x y : M) : polar (-f) x y = -polar f x y := by
  simp only [polar, Pi.neg_apply, sub_eq_add_neg, neg_add]

/--
theorem `polar_smul` / 定理 `polar_smul`

English:
theorem polar_smul
  given: [Monoid S] [DistribMulAction S N] (f : M -> N) (s : S) (x y : M)
  proof: by simp only [polar, Pi.smul_apply, smul_sub]

中文:
定理 polar_smul
  条件: [Monoid S] [DistribMulAction S N] (f : M -> N) (s : S) (x y : M)
  证明: by simp only [polar, Pi.smul_apply, smul_sub]

Depends on / 依赖: Pi.smul_apply, smul_apply, smul_sub
-/
theorem polar_smul [Monoid S] [DistribMulAction S N] (f : M -> N) (s : S) (x y : M) :
    polar (s • f) x y = s • polar f x y := by simp only [polar, Pi.smul_apply, smul_sub]

/--
theorem `polar_comm` / 定理 `polar_comm`

English:
theorem polar_comm
  given: (f : M -> N) (x y : M)
  statement: polar f x y = polar f y x
  proof: by
  rw [polar]; rw [polar]; rw [add_comm]; rw [sub_sub]; rw [sub_sub]; rw [add_comm (f x) (f y)]

中文:
定理 polar_comm
  条件: (f : M -> N) (x y : M)
  结论: polar f x y = polar f y x
  证明: by
  rw [polar]; rw [polar]; rw [add_comm]; rw [sub_sub]; rw [sub_sub]; rw [add_comm (f x) (f y)]

Depends on / 依赖: add_comm, sub_sub
-/
theorem polar_comm (f : M -> N) (x y : M) : polar f x y = polar f y x := by
  rw [polar]; rw [polar]; rw [add_comm]; rw [sub_sub]; rw [sub_sub]; rw [add_comm (f x) (f y)]

/--
theorem `polar_add_left_iff` / 定理 `polar_add_left_iff`

English:
theorem polar_add_left_iff
  given: {f : M -> N} {x x' y : M}
  proof: by
  simp only [← add_assoc]
  simp only [polar, sub_eq_iff_eq_add, eq_sub_iff_add_eq, sub_add_eq_add_sub, add_sub]
  simp only [add_right_comm _ (f y) _, add_right_comm _ (f x') (f x)]
  rw [add_comm y x]; rw [add_right_comm _ _ (f (x + y))]; rw [add_comm _ (f (x + y))]; rw [add_right_comm (f (x + 

中文:
定理 polar_add_left_iff
  条件: {f : M -> N} {x x' y : M}
  证明: by
  simp only [← add_assoc]
  simp only [polar, sub_eq_iff_eq_add, eq_sub_iff_add_eq, sub_add_eq_add_sub, add_sub]
  simp only [add_right_comm _ (f y) _, add_right_comm _ (f x') (f x)]
  rw [add_comm y x]; rw [add_right_comm _ _ (f (x + y))]; rw [add_comm _ (f (x + y))]; rw [add_right_comm (f (x + 

Depends on / 依赖: add_assoc, add_comm, add_left_inj, add_right_comm, add_sub, eq_sub_iff_add_eq, sub_add_eq_add_sub, sub_eq_iff_eq_add
-/
theorem polar_add_left_iff {f : M -> N} {x x' y : M} :
    polar f (x + x') y = polar f x y + polar f x' y ↔
      f (x + x' + y) + (f x + f x' + f y) = f (x + x') + f (x' + y) + f (y + x) := by
  simp only [← add_assoc]
  simp only [polar, sub_eq_iff_eq_add, eq_sub_iff_add_eq, sub_add_eq_add_sub, add_sub]
  simp only [add_right_comm _ (f y) _, add_right_comm _ (f x') (f x)]
  rw [add_comm y x]; rw [add_right_comm _ _ (f (x + y))]; rw [add_comm _ (f (x + y))]; rw [add_right_comm (f (x + y))]; rw [add_left_inj]

/--
theorem `polar_comp` / 定理 `polar_comp`

English:
theorem polar_comp
  statement: {F : Type*} [AddCommGroup S] [FunLike F N S] [AddMonoidHomClass F N S]
  proof: by
  simp only [polar, Function.comp_apply, map_sub]

中文:
定理 polar_comp
  结论: {F : 类型} [AddCommGroup S] [FunLike F N S] [AddMonoidHomClass F N S]
  证明: by
  simp only [polar, Function.comp_apply, map_sub]

Depends on / 依赖: Function, Function.comp_apply, comp_apply, map_sub
-/
theorem polar_comp {F : Type*} [AddCommGroup S] [FunLike F N S] [AddMonoidHomClass F N S]
    (f : M -> N) (g : F) (x y : M) :
    polar (g ∘ f) x y = g (polar f x y) := by
  simp only [polar, Function.comp_apply, map_sub]

/--
Definition of `polarSym2` / `polarSym2` 的定义

English:
definition polarSym2
  signature: (f : M -> N)
  body: Sym2.lift ⟨polar f, polar_comm _⟩

@[simp]

中文:
定义 polarSym2
  签名: (f : M -> N)
  定义体: Sym2.lift ⟨polar f, polar_comm _⟩

@[simp]

Depends on / 依赖: Sym2.lift, polar_comm
-/
def polarSym2 (f : M -> N) : Sym2 M -> N :=
  Sym2.lift ⟨polar f, polar_comm _⟩

@[simp]
/--
lemma `polarSym2_sym2Mk` / 引理 `polarSym2_sym2Mk`

English:
lemma polarSym2_sym2Mk
  given: (f : M -> N) (x y : M)
  statement: polarSym2 f s(x, y) = polar f x y
  proof: rfl

中文:
引理 polarSym2_sym2Mk
  条件: (f : M -> N) (x y : M)
  结论: polarSym2 f s(x, y) = polar f x y
  证明: rfl
-/
lemma polarSym2_sym2Mk (f : M -> N) (x y : M) : polarSym2 f s(x, y) = polar f x y := rfl

end QuadraticMap

end Polar

/--
Definition of `QuadraticMap` / `QuadraticMap` 的定义

English:
structure QuadraticMap
  parameters: (R : Type u) (M : Type v) (N : Type w) [CommSemiring R] [AddCommMonoid M]
  axioms and operations (3):
    - toFun : M -> N
    - toFun_smul : forall (a : R) (x : M), toFun (a • x) = (a * a) • toFun x
    - exists_companion' : exists B : BilinMap R M N, forall x y, toFun (x + y) = toFun x + toFun y + B x y

中文:
结构 QuadraticMap
  参数: (R : 类型u) (M : 类型v) (N : Type w) [CommSemiring R] [AddCommMonoid M]
  公理与运算 (3 个):
    - toFun : M -> N
    - toFun_smul : 对任意 (a : R) (x : M), toFun (a • x) = (a * a) • toFun x
    - exists_companion' : 存在 B : BilinMap R M N, 对任意 x y, toFun (x + y) = toFun x + toFun y + B x y
-/
structure QuadraticMap (R : Type u) (M : Type v) (N : Type w) [CommSemiring R] [AddCommMonoid M]
    [Module R M] [AddCommMonoid N] [Module R N] where
  /-- The underlying function.

  Do NOT use directly. Use the coercion instead. -/
  toFun : M -> N
  toFun_smul : forall (a : R) (x : M), toFun (a • x) = (a * a) • toFun x
  exists_companion' : exists B : BilinMap R M N, forall x y, toFun (x + y) = toFun x + toFun y + B x y

section QuadraticForm

variable (R : Type u) (M : Type v) [CommSemiring R] [AddCommMonoid M] [Module R M]

/--
Definition of `QuadraticForm` / `QuadraticForm` 的定义

English:
abbreviation QuadraticForm
  signature: : Type _
  body: QuadraticMap R M R

中文:
缩写 QuadraticForm
  签名: : Type _
  定义体: QuadraticMap R M R

Depends on / 依赖: QuadraticMap
-/
abbrev QuadraticForm : Type _ := QuadraticMap R M R

end QuadraticForm

namespace QuadraticMap

section DFunLike

variable [CommSemiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
variable {Q Q' : QuadraticMap R M N}

/--
Instance `instFunLike` / 实例 `instFunLike`

English:
instance instFunLike
  signature: : FunLike (QuadraticMap R M N) M N where
  body: toFun
  coe_injective x y h := by cases x; cases y; congr

中文:
实例 instFunLike
  签名: : FunLike (QuadraticMap R M N) M N where
  定义体: toFun
  coe_injective x y h := by cases x; cases y; congr
-/
instance instFunLike : FunLike (QuadraticMap R M N) M N where
  coe := toFun
  coe_injective x y h := by cases x; cases y; congr

variable (Q)

/-- The `simp` normal form for a quadratic map is `DFunLike.coe`, not `toFun`. -/
@[simp]
/--
theorem `toFun_eq_coe` / 定理 `toFun_eq_coe`

English:
theorem toFun_eq_coe
  statement: Q.toFun = ⇑Q
  proof: rfl

@[simp]

中文:
定理 toFun_eq_coe
  结论: Q.toFun = ⇑Q
  证明: rfl

@[simp]
-/
theorem toFun_eq_coe : Q.toFun = ⇑Q :=
  rfl

@[simp]
/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  given: (toFun : M -> N) (toFun_smul exists_companion')
  proof: rfl

中文:
定理 coe_mk
  条件: (toFun : M -> N) (toFun_smul 存在_companion')
  证明: rfl
-/
theorem coe_mk (toFun : M -> N) (toFun_smul exists_companion') :
    ⇑({toFun, toFun_smul, exists_companion'} : QuadraticMap R M N) = toFun := rfl

-- this must come after the instFunLike definition
initialize_simps_projections QuadraticMap (toFun -> apply)

variable {Q}

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: (H : forall x : M, Q x = Q' x)
  statement: Q = Q'
  proof: DFunLike.ext _ _ H

中文:
定理 ext
  条件: (H : 对任意 x : M, Q x = Q' x)
  结论: Q = Q'
  证明: DFunLike.ext _ _ H

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext (H : forall x : M, Q x = Q' x) : Q = Q' :=
  DFunLike.ext _ _ H

/--
theorem `congr_fun` / 定理 `congr_fun`

English:
theorem congr_fun
  given: (h : Q = Q') (x : M)
  statement: Q x = Q' x
  proof: DFunLike.congr_fun h _

中文:
定理 congr_fun
  条件: (h : Q = Q') (x : M)
  结论: Q x = Q' x
  证明: DFunLike.congr_fun h _

Depends on / 依赖: DFunLike, DFunLike.congr_fun, congr_fun
-/
theorem congr_fun (h : Q = Q') (x : M) : Q x = Q' x :=
  DFunLike.congr_fun h _

/--
Definition of `copy` / `copy` 的定义

English:
definition copy
  signature: (Q : QuadraticMap R M N) (Q' : M -> N) (h : Q' = ⇑Q)
  body: Q'
  toFun_smul := h.symm ▸ Q.toFun_smul
  exists_companion' := h.symm ▸ Q.exists_companion'

@[simp]

中文:
定义 copy
  签名: (Q : QuadraticMap R M N) (Q' : M -> N) (h : Q' = ⇑Q)
  定义体: Q'
  toFun_smul := h.symm ▸ Q.toFun_smul
  exists_companion' := h.symm ▸ Q.exists_companion'

@[simp]
-/
protected def copy (Q : QuadraticMap R M N) (Q' : M -> N) (h : Q' = ⇑Q) : QuadraticMap R M N where
  toFun := Q'
  toFun_smul := h.symm ▸ Q.toFun_smul
  exists_companion' := h.symm ▸ Q.exists_companion'

@[simp]
/--
theorem `coe_copy` / 定理 `coe_copy`

English:
theorem coe_copy
  given: (Q : QuadraticMap R M N) (Q' : M -> N) (h : Q' = ⇑Q)
  statement: ⇑(Q.copy Q' h) = Q'
  proof: rfl

中文:
定理 coe_copy
  条件: (Q : QuadraticMap R M N) (Q' : M -> N) (h : Q' = ⇑Q)
  结论: ⇑(Q.copy Q' h) = Q'
  证明: rfl
-/
theorem coe_copy (Q : QuadraticMap R M N) (Q' : M -> N) (h : Q' = ⇑Q) : ⇑(Q.copy Q' h) = Q' :=
  rfl

/--
theorem `copy_eq` / 定理 `copy_eq`

English:
theorem copy_eq
  given: (Q : QuadraticMap R M N) (Q' : M -> N) (h : Q' = ⇑Q)
  statement: Q.copy Q' h = Q
  proof: DFunLike.ext' h

中文:
定理 copy_eq
  条件: (Q : QuadraticMap R M N) (Q' : M -> N) (h : Q' = ⇑Q)
  结论: Q.copy Q' h = Q
  证明: DFunLike.ext' h

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem copy_eq (Q : QuadraticMap R M N) (Q' : M -> N) (h : Q' = ⇑Q) : Q.copy Q' h = Q :=
  DFunLike.ext' h

end DFunLike

section CommSemiring

variable [CommSemiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
variable (Q : QuadraticMap R M N)

/--
theorem `map_smul` / 定理 `map_smul`

English:
theorem map_smul
  given: (a : R) (x : M)
  statement: Q (a • x) = (a * a) • Q x
  proof: Q.toFun_smul a x

中文:
定理 map_smul
  条件: (a : R) (x : M)
  结论: Q (a • x) = (a * a) • Q x
  证明: Q.toFun_smul a x
-/
protected theorem map_smul (a : R) (x : M) : Q (a • x) = (a * a) • Q x :=
  Q.toFun_smul a x

/--
theorem `exists_companion` / 定理 `exists_companion`

English:
theorem exists_companion
  statement: exists B : BilinMap R M N, forall x y, Q (x + y) = Q x + Q y + B x y
  proof: Q.exists_companion'

中文:
定理 exists_companion
  结论: 存在 B : BilinMap R M N, 对任意 x y, Q (x + y) = Q x + Q y + B x y
  证明: Q.exists_companion'

Depends on / 依赖: Q.exists_companion, ae_restrict_iff, exists_companion, hs.nullMeasurableSet, nullMeasurableSet
-/
theorem exists_companion : exists B : BilinMap R M N, forall x y, Q (x + y) = Q x + Q y + B x y :=
  Q.exists_companion'

/--
theorem `map_add_add_add_map` / 定理 `map_add_add_add_map`

English:
theorem map_add_add_add_map
  given: (x y z : M)
  proof: by
  obtain ⟨B, h⟩ := Q.exists_companion
  rw [add_comm z x]
  simp only [h, LinearMap.map_add₂]
  abel

中文:
定理 map_add_add_add_map
  条件: (x y z : M)
  证明: by
  obtain ⟨B, h⟩ := Q.exists_companion
  rw [add_comm z x]
  simp only [h, LinearMap.map_add₂]
  abel

Depends on / 依赖: LinearMap, LinearMap.map_add, Q.exists_companion, add_comm, exists_companion
-/
theorem map_add_add_add_map (x y z : M) :
    Q (x + y + z) + (Q x + Q y + Q z) = Q (x + y) + Q (y + z) + Q (z + x) := by
  obtain ⟨B, h⟩ := Q.exists_companion
  rw [add_comm z x]
  simp only [h, LinearMap.map_add₂]
  abel

/--
theorem `map_add_self` / 定理 `map_add_self`

English:
theorem map_add_self
  given: (x : M)
  statement: Q (x + x) = 4 • Q x
  proof: by
  rw [← two_smul R x]; rw [Q.map_smul]; rw [← Nat.cast_smul_eq_nsmul R]
  norm_num

中文:
定理 map_add_self
  条件: (x : M)
  结论: Q (x + x) = 4 • Q x
  证明: by
  rw [← two_smul R x]; rw [Q.map_smul]; rw [← Nat.cast_smul_eq_nsmul R]
  norm_num

Depends on / 依赖: Nat.cast_smul_eq_nsmul, Q.map_smul, cast_smul_eq_nsmul, map_smul, two_smul
-/
theorem map_add_self (x : M) : Q (x + x) = 4 • Q x := by
  rw [← two_smul R x]; rw [Q.map_smul]; rw [← Nat.cast_smul_eq_nsmul R]
  norm_num

-- not @[simp] because it is superseded by `ZeroHomClass.map_zero`
/--
theorem `map_zero` / 定理 `map_zero`

English:
theorem map_zero
  statement: Q 0 = 0
  proof: by
  rw [← @zero_smul R _ _ _ _ (0 : M)]; rw [Q.map_smul]; rw [zero_mul]; rw [zero_smul]

中文:
定理 map_zero
  结论: Q 0 = 0
  证明: by
  rw [← @zero_smul R _ _ _ _ (0 : M)]; rw [Q.map_smul]; rw [zero_mul]; rw [zero_smul]
-/
protected theorem map_zero : Q 0 = 0 := by
  rw [← @zero_smul R _ _ _ _ (0 : M)]; rw [Q.map_smul]; rw [zero_mul]; rw [zero_smul]

/--
Instance `zeroHomClass` / 实例 `zeroHomClass`

English:
instance zeroHomClass
  signature: : ZeroHomClass (QuadraticMap R M N) M N
  body: { QuadraticMap.instFunLike (R := R) (M := M) (N := N) with map_zero := QuadraticMap.map_zero }

中文:
实例 zeroHomClass
  签名: : ZeroHomClass (QuadraticMap R M N) M N
  定义体: { QuadraticMap.instFunLike (R := R) (M := M) (N := N) with map_zero := QuadraticMap.map_zero }

Depends on / 依赖: QuadraticMap, QuadraticMap.instFunLike, QuadraticMap.map_zero, instFunLike, map_zero
-/
instance zeroHomClass : ZeroHomClass (QuadraticMap R M N) M N :=
  { QuadraticMap.instFunLike (R := R) (M := M) (N := N) with map_zero := QuadraticMap.map_zero }

/--
theorem `map_smul_of_tower` / 定理 `map_smul_of_tower`

English:
theorem map_smul_of_tower
  statement: [CommSemiring S] [Algebra S R] [SMul S M] [IsScalarTower S R M]
  proof: by
  rw [← IsScalarTower.algebraMap_smul R a x]; rw [Q.map_smul]; rw [← map_mul]; rw [algebraMap_smul]

中文:
定理 map_smul_of_tower
  结论: [CommSemiring S] [Algebra S R] [SMul S M] [IsScalarTower S R M]
  证明: by
  rw [← IsScalarTower.algebraMap_smul R a x]; rw [Q.map_smul]; rw [← map_mul]; rw [algebraMap_smul]

Depends on / 依赖: IsScalarTower, IsScalarTower.algebraMap_smul, Q.map_smul, algebraMap_smul, map_mul, map_smul
-/
theorem map_smul_of_tower [CommSemiring S] [Algebra S R] [SMul S M] [IsScalarTower S R M]
    [Module S N] [IsScalarTower S R N] (a : S)
    (x : M) : Q (a • x) = (a * a) • Q x := by
  rw [← IsScalarTower.algebraMap_smul R a x]; rw [Q.map_smul]; rw [← map_mul]; rw [algebraMap_smul]

/--
Definition of `restrict` / `restrict` 的定义

English:
definition restrict
  signature: (Q : QuadraticMap R M N) (V : Submodule R M)
  body: Q v
  toFun_smul a v := Q.toFun_smul a v.val
  exists_companion' := match Q.exists_companion with
    | ⟨b, hb⟩ => ⟨b.domRestrict₁₂ V V, fun x y => hb x.val y.val⟩

中文:
定义 restrict
  签名: (Q : QuadraticMap R M N) (V : Submodule R M)
  定义体: Q v
  toFun_smul a v := Q.toFun_smul a v.val
  exists_companion' := match Q.exists_companion with
    | ⟨b, hb⟩ => ⟨b.domRestrict₁₂ V V, fun x y => hb x.val y.val⟩
-/
@[simps] def restrict (Q : QuadraticMap R M N) (V : Submodule R M) : QuadraticMap R V N where
  toFun v := Q v
  toFun_smul a v := Q.toFun_smul a v.val
  exists_companion' := match Q.exists_companion with
    | ⟨b, hb⟩ => ⟨b.domRestrict₁₂ V V, fun x y => hb x.val y.val⟩

end CommSemiring

section CommRing

variable [CommRing R] [AddCommGroup M] [AddCommGroup N]
variable [Module R M] [Module R N] (Q : QuadraticMap R M N)

@[simp]
/--
theorem `map_neg` / 定理 `map_neg`

English:
theorem map_neg
  given: (x : M)
  statement: Q (-x) = Q x
  proof: by
  rw [← @neg_one_smul R _ _ _ _ x]; rw [Q.map_smul]; rw [neg_one_mul]; rw [neg_neg]; rw [one_smul]

中文:
定理 map_neg
  条件: (x : M)
  结论: Q (-x) = Q x
  证明: by
  rw [← @neg_one_smul R _ _ _ _ x]; rw [Q.map_smul]; rw [neg_one_mul]; rw [neg_neg]; rw [one_smul]
-/
protected theorem map_neg (x : M) : Q (-x) = Q x := by
  rw [← @neg_one_smul R _ _ _ _ x]; rw [Q.map_smul]; rw [neg_one_mul]; rw [neg_neg]; rw [one_smul]

/--
theorem `map_sub` / 定理 `map_sub`

English:
theorem map_sub
  given: (x y : M)
  statement: Q (x - y) = Q (y - x)
  proof: by rw [← neg_sub, Q.map_neg]

@[simp]

中文:
定理 map_sub
  条件: (x y : M)
  结论: Q (x - y) = Q (y - x)
  证明: by rw [← neg_sub, Q.map_neg]

@[simp]
-/
protected theorem map_sub (x y : M) : Q (x - y) = Q (y - x) := by rw [← neg_sub, Q.map_neg]

@[simp]
/--
theorem `polar_zero_left` / 定理 `polar_zero_left`

English:
theorem polar_zero_left
  given: (y : M)
  statement: polar Q 0 y = 0
  proof: by
  simp only [polar, zero_add, QuadraticMap.map_zero, sub_zero, sub_self]

@[simp]

中文:
定理 polar_zero_left
  条件: (y : M)
  结论: polar Q 0 y = 0
  证明: by
  simp only [polar, zero_add, QuadraticMap.map_zero, sub_zero, sub_self]

@[simp]

Depends on / 依赖: QuadraticMap, QuadraticMap.map_zero, map_zero, sub_self, sub_zero, zero_add
-/
theorem polar_zero_left (y : M) : polar Q 0 y = 0 := by
  simp only [polar, zero_add, QuadraticMap.map_zero, sub_zero, sub_self]

@[simp]
/--
theorem `polar_add_left` / 定理 `polar_add_left`

English:
theorem polar_add_left
  given: (x x' y : M)
  statement: polar Q (x + x') y = polar Q x y + polar Q x' y
  proof: polar_add_left_iff.mpr Q.map_add_add_add_map x x' y

@[simp]

中文:
定理 polar_add_left
  条件: (x x' y : M)
  结论: polar Q (x + x') y = polar Q x y + polar Q x' y
  证明: polar_add_left_iff.mpr Q.map_add_add_add_map x x' y

@[simp]

Depends on / 依赖: Q.map_add_add_add_map, map_add_add_add_map, polar_add_left_iff, polar_add_left_iff.mpr
-/
theorem polar_add_left (x x' y : M) : polar Q (x + x') y = polar Q x y + polar Q x' y :=
polar_add_left_iff.mpr Q.map_add_add_add_map x x' y

@[simp]
/--
theorem `polar_smul_left` / 定理 `polar_smul_left`

English:
theorem polar_smul_left
  given: (a : R) (x y : M)
  statement: polar Q (a • x) y = a • polar Q x y
  proof: by
  obtain ⟨B, h⟩ := Q.exists_companion
  simp_rw [polar, h, Q.map_smul, LinearMap.map_smul₂, sub_sub, add_sub_cancel_left]

@[simp]

中文:
定理 polar_smul_left
  条件: (a : R) (x y : M)
  结论: polar Q (a • x) y = a • polar Q x y
  证明: by
  obtain ⟨B, h⟩ := Q.exists_companion
  simp_rw [polar, h, Q.map_smul, LinearMap.map_smul₂, sub_sub, add_sub_cancel_left]

@[simp]

Depends on / 依赖: LinearMap, LinearMap.map_smul, Q.exists_companion, Q.map_smul, add_sub_cancel_left, exists_companion, map_smul, simp_rw, sub_sub
-/
theorem polar_smul_left (a : R) (x y : M) : polar Q (a • x) y = a • polar Q x y := by
  obtain ⟨B, h⟩ := Q.exists_companion
  simp_rw [polar, h, Q.map_smul, LinearMap.map_smul₂, sub_sub, add_sub_cancel_left]

@[simp]
/--
theorem `polar_neg_left` / 定理 `polar_neg_left`

English:
theorem polar_neg_left
  given: (x y : M)
  statement: polar Q (-x) y = -polar Q x y
  proof: by
  rw [← neg_one_smul R x]; rw [polar_smul_left]; rw [neg_one_smul]

@[simp]

中文:
定理 polar_neg_left
  条件: (x y : M)
  结论: polar Q (-x) y = -polar Q x y
  证明: by
  rw [← neg_one_smul R x]; rw [polar_smul_left]; rw [neg_one_smul]

@[simp]

Depends on / 依赖: neg_one_smul, polar_smul_left
-/
theorem polar_neg_left (x y : M) : polar Q (-x) y = -polar Q x y := by
  rw [← neg_one_smul R x]; rw [polar_smul_left]; rw [neg_one_smul]

@[simp]
/--
theorem `polar_sub_left` / 定理 `polar_sub_left`

English:
theorem polar_sub_left
  given: (x x' y : M)
  statement: polar Q (x - x') y = polar Q x y - polar Q x' y
  proof: by
  rw [sub_eq_add_neg]; rw [sub_eq_add_neg]; rw [polar_add_left]; rw [polar_neg_left]

@[simp]

中文:
定理 polar_sub_left
  条件: (x x' y : M)
  结论: polar Q (x - x') y = polar Q x y - polar Q x' y
  证明: by
  rw [sub_eq_add_neg]; rw [sub_eq_add_neg]; rw [polar_add_left]; rw [polar_neg_left]

@[simp]

Depends on / 依赖: polar_add_left, polar_neg_left, sub_eq_add_neg
-/
theorem polar_sub_left (x x' y : M) : polar Q (x - x') y = polar Q x y - polar Q x' y := by
  rw [sub_eq_add_neg]; rw [sub_eq_add_neg]; rw [polar_add_left]; rw [polar_neg_left]

@[simp]
/--
theorem `polar_zero_right` / 定理 `polar_zero_right`

English:
theorem polar_zero_right
  given: (y : M)
  statement: polar Q y 0 = 0
  proof: by
  simp only [add_zero, polar, QuadraticMap.map_zero, sub_self]

@[simp]

中文:
定理 polar_zero_right
  条件: (y : M)
  结论: polar Q y 0 = 0
  证明: by
  simp only [add_zero, polar, QuadraticMap.map_zero, sub_self]

@[simp]

Depends on / 依赖: QuadraticMap, QuadraticMap.map_zero, add_zero, map_zero, sub_self
-/
theorem polar_zero_right (y : M) : polar Q y 0 = 0 := by
  simp only [add_zero, polar, QuadraticMap.map_zero, sub_self]

@[simp]
/--
theorem `polar_add_right` / 定理 `polar_add_right`

English:
theorem polar_add_right
  given: (x y y' : M)
  statement: polar Q x (y + y') = polar Q x y + polar Q x y'
  proof: by
  rw [polar_comm Q x]; rw [polar_comm Q x]; rw [polar_comm Q x]; rw [polar_add_left]

@[simp]

中文:
定理 polar_add_right
  条件: (x y y' : M)
  结论: polar Q x (y + y') = polar Q x y + polar Q x y'
  证明: by
  rw [polar_comm Q x]; rw [polar_comm Q x]; rw [polar_comm Q x]; rw [polar_add_left]

@[simp]

Depends on / 依赖: polar_add_left, polar_comm
-/
theorem polar_add_right (x y y' : M) : polar Q x (y + y') = polar Q x y + polar Q x y' := by
  rw [polar_comm Q x]; rw [polar_comm Q x]; rw [polar_comm Q x]; rw [polar_add_left]

@[simp]
/--
theorem `polar_smul_right` / 定理 `polar_smul_right`

English:
theorem polar_smul_right
  given: (a : R) (x y : M)
  statement: polar Q x (a • y) = a • polar Q x y
  proof: by
  rw [polar_comm Q x]; rw [polar_comm Q x]; rw [polar_smul_left]

@[simp]

中文:
定理 polar_smul_right
  条件: (a : R) (x y : M)
  结论: polar Q x (a • y) = a • polar Q x y
  证明: by
  rw [polar_comm Q x]; rw [polar_comm Q x]; rw [polar_smul_left]

@[simp]

Depends on / 依赖: polar_comm, polar_smul_left
-/
theorem polar_smul_right (a : R) (x y : M) : polar Q x (a • y) = a • polar Q x y := by
  rw [polar_comm Q x]; rw [polar_comm Q x]; rw [polar_smul_left]

@[simp]
/--
theorem `polar_neg_right` / 定理 `polar_neg_right`

English:
theorem polar_neg_right
  given: (x y : M)
  statement: polar Q x (-y) = -polar Q x y
  proof: by
  rw [← neg_one_smul R y]; rw [polar_smul_right]; rw [neg_one_smul]

@[simp]

中文:
定理 polar_neg_right
  条件: (x y : M)
  结论: polar Q x (-y) = -polar Q x y
  证明: by
  rw [← neg_one_smul R y]; rw [polar_smul_right]; rw [neg_one_smul]

@[simp]

Depends on / 依赖: neg_one_smul, polar_smul_right
-/
theorem polar_neg_right (x y : M) : polar Q x (-y) = -polar Q x y := by
  rw [← neg_one_smul R y]; rw [polar_smul_right]; rw [neg_one_smul]

@[simp]
/--
theorem `polar_sub_right` / 定理 `polar_sub_right`

English:
theorem polar_sub_right
  given: (x y y' : M)
  statement: polar Q x (y - y') = polar Q x y - polar Q x y'
  proof: by
  rw [sub_eq_add_neg]; rw [sub_eq_add_neg]; rw [polar_add_right]; rw [polar_neg_right]

@[simp]

中文:
定理 polar_sub_right
  条件: (x y y' : M)
  结论: polar Q x (y - y') = polar Q x y - polar Q x y'
  证明: by
  rw [sub_eq_add_neg]; rw [sub_eq_add_neg]; rw [polar_add_right]; rw [polar_neg_right]

@[simp]

Depends on / 依赖: polar_add_right, polar_neg_right, sub_eq_add_neg
-/
theorem polar_sub_right (x y y' : M) : polar Q x (y - y') = polar Q x y - polar Q x y' := by
  rw [sub_eq_add_neg]; rw [sub_eq_add_neg]; rw [polar_add_right]; rw [polar_neg_right]

@[simp]
/--
theorem `polar_self` / 定理 `polar_self`

English:
theorem polar_self
  given: (x : M)
  statement: polar Q x x = 2 • Q x
  proof: by
  rw [polar]; rw [map_add_self]; rw [sub_sub]; rw [sub_eq_iff_eq_add]; rw [← two_smul Nat]; rw [← two_smul Nat]; rw [← mul_smul]
  simp

中文:
定理 polar_self
  条件: (x : M)
  结论: polar Q x x = 2 • Q x
  证明: by
  rw [polar]; rw [map_add_self]; rw [sub_sub]; rw [sub_eq_iff_eq_add]; rw [← two_smul Nat]; rw [← two_smul Nat]; rw [← mul_smul]
  simp

Depends on / 依赖: map_add_self, mul_smul, sub_eq_iff_eq_add, sub_sub, two_smul
-/
theorem polar_self (x : M) : polar Q x x = 2 • Q x := by
  rw [polar]; rw [map_add_self]; rw [sub_sub]; rw [sub_eq_iff_eq_add]; rw [← two_smul Nat]; rw [← two_smul Nat]; rw [← mul_smul]
  simp

/-- `QuadraticMap.polar` as a bilinear map -/
@[simps!]
/--
Definition of `polarBilin` / `polarBilin` 的定义

English:
definition polarBilin
  signature: : BilinMap R M N
  body: LinearMap.mk₂ R (polar Q) (polar_add_left Q) (polar_smul_left Q) (polar_add_right Q)
  (polar_smul_right Q)

中文:
定义 polarBilin
  签名: : BilinMap R M N
  定义体: LinearMap.mk₂ R (polar Q) (polar_add_left Q) (polar_smul_left Q) (polar_add_right Q)
  (polar_smul_right Q)

Depends on / 依赖: LinearMap, LinearMap.mk, polar_add_left, polar_add_right, polar_smul_left, polar_smul_right
-/
def polarBilin : BilinMap R M N :=
  LinearMap.mk₂ R (polar Q) (polar_add_left Q) (polar_smul_left Q) (polar_add_right Q)
  (polar_smul_right Q)

/--
lemma `polarSym2_map_smul` / 引理 `polarSym2_map_smul`

English:
lemma polarSym2_map_smul
  given: {ι} (Q : QuadraticMap R M N) (g : ι -> M) (l : ι -> R) (p : Sym2 ι)
  proof: by
  obtain ⟨_, _⟩ := p; simp [← smul_assoc, mul_comm]

中文:
引理 polarSym2_map_smul
  条件: {ι} (Q : QuadraticMap R M N) (g : ι -> M) (l : ι -> R) (p : Sym2 ι)
  证明: by
  obtain ⟨_, _⟩ := p; simp [← smul_assoc, mul_comm]

Depends on / 依赖: mul_comm, smul_assoc
-/
lemma polarSym2_map_smul {ι} (Q : QuadraticMap R M N) (g : ι -> M) (l : ι -> R) (p : Sym2 ι) :
    polarSym2 Q (p.map (l • g)) = (p.map l).mul • polarSym2 Q (p.map g) := by
  obtain ⟨_, _⟩ := p; simp [← smul_assoc, mul_comm]

variable [CommSemiring S] [Algebra S R] [Module S M] [IsScalarTower S R M] [Module S N]
    [IsScalarTower S R N]

@[simp]
/--
theorem `polar_smul_left_of_tower` / 定理 `polar_smul_left_of_tower`

English:
theorem polar_smul_left_of_tower
  given: (a : S) (x y : M)
  statement: polar Q (a • x) y = a • polar Q x y
  proof: by
  rw [← IsScalarTower.algebraMap_smul R a x]; rw [polar_smul_left]; rw [algebraMap_smul]

@[simp]

中文:
定理 polar_smul_left_of_tower
  条件: (a : S) (x y : M)
  结论: polar Q (a • x) y = a • polar Q x y
  证明: by
  rw [← IsScalarTower.algebraMap_smul R a x]; rw [polar_smul_left]; rw [algebraMap_smul]

@[simp]

Depends on / 依赖: IsScalarTower, IsScalarTower.algebraMap_smul, algebraMap_smul, polar_smul_left
-/
theorem polar_smul_left_of_tower (a : S) (x y : M) : polar Q (a • x) y = a • polar Q x y := by
  rw [← IsScalarTower.algebraMap_smul R a x]; rw [polar_smul_left]; rw [algebraMap_smul]

@[simp]
/--
theorem `polar_smul_right_of_tower` / 定理 `polar_smul_right_of_tower`

English:
theorem polar_smul_right_of_tower
  given: (a : S) (x y : M)
  statement: polar Q x (a • y) = a • polar Q x y
  proof: by
  rw [← IsScalarTower.algebraMap_smul R a y]; rw [polar_smul_right]; rw [algebraMap_smul]

中文:
定理 polar_smul_right_of_tower
  条件: (a : S) (x y : M)
  结论: polar Q x (a • y) = a • polar Q x y
  证明: by
  rw [← IsScalarTower.algebraMap_smul R a y]; rw [polar_smul_right]; rw [algebraMap_smul]

Depends on / 依赖: IsScalarTower, IsScalarTower.algebraMap_smul, algebraMap_smul, polar_smul_right
-/
theorem polar_smul_right_of_tower (a : S) (x y : M) : polar Q x (a • y) = a • polar Q x y := by
  rw [← IsScalarTower.algebraMap_smul R a y]; rw [polar_smul_right]; rw [algebraMap_smul]

/-- An alternative constructor to `QuadraticMap.mk`, for rings where `polar` can be used. -/
@[simps]
/--
Definition of `ofPolar` / `ofPolar` 的定义

English:
definition ofPolar
  signature: (toFun : M -> N) (toFun_smul : forall (a : R) (x : M), toFun (a • x) = (a * a) • toFun x)
  body: { toFun
    toFun_smul
    exists_companion' := ⟨LinearMap.mk₂ R (polar toFun) (polar_add_left) (polar_smul_left)
      (fun x _ _ => by simp_rw [polar_comm _ x, polar_add_left])
      (fun _ _ _ => by rw [polar_comm, polar_smul_left, polar_comm]),
      fun _ _ => by
        simp only [LinearMap.mk

中文:
定义 ofPolar
  签名: (toFun : M -> N) (toFun_smul : 对任意 (a : R) (x : M), toFun (a • x) = (a * a) • toFun x)
  定义体: { toFun
    toFun_smul
    exists_companion' := ⟨LinearMap.mk₂ R (polar toFun) (polar_add_left) (polar_smul_left)
      (fun x _ _ => by simp_rw [polar_comm _ x, polar_add_left])
      (fun _ _ _ => by rw [polar_comm, polar_smul_left, polar_comm]),
      fun _ _ => by
        simp only [LinearMap.mk

Depends on / 依赖: LinearMap, LinearMap.mk, add_sub_cancel, exists_companion, polar_add_left, polar_comm, polar_smul_left, simp_rw, sub_sub, toFun_smul
-/
def ofPolar (toFun : M -> N) (toFun_smul : forall (a : R) (x : M), toFun (a • x) = (a * a) • toFun x)
    (polar_add_left : forall x x' y : M, polar toFun (x + x') y = polar toFun x y + polar toFun x' y)
    (polar_smul_left : forall (a : R) (x y : M), polar toFun (a • x) y = a • polar toFun x y) :
    QuadraticMap R M N :=
  { toFun
    toFun_smul
    exists_companion' := ⟨LinearMap.mk₂ R (polar toFun) (polar_add_left) (polar_smul_left)
      (fun x _ _ => by simp_rw [polar_comm _ x, polar_add_left])
      (fun _ _ _ => by rw [polar_comm, polar_smul_left, polar_comm]),
      fun _ _ => by
        simp only [LinearMap.mk₂_apply]
        rw [polar]; rw [sub_sub]; rw [add_sub_cancel]⟩ }

/--
theorem `choose_exists_companion` / 定理 `choose_exists_companion`

English:
theorem choose_exists_companion
  statement: Q.exists_companion.choose = polarBilin Q
  proof: LinearMap.ext₂ fun x y => by
    rw [polarBilin_apply_apply]; rw [polar]; rw [Q.exists_companion.choose_spec]; rw [sub_sub]; rw [add_sub_cancel_left]

中文:
定理 choose_exists_companion
  结论: Q.存在_companion.choose = polarBilin Q
  证明: LinearMap.ext₂ fun x y => by
    rw [polarBilin_apply_apply]; rw [polar]; rw [Q.exists_companion.choose_spec]; rw [sub_sub]; rw [add_sub_cancel_left]

Depends on / 依赖: LinearMap, LinearMap.ext, Q.exists_companion.choose_spec, add_sub_cancel_left, choose_spec, exists_companion, polarBilin_apply_apply, sub_sub
-/
theorem choose_exists_companion : Q.exists_companion.choose = polarBilin Q :=
  LinearMap.ext₂ fun x y => by
    rw [polarBilin_apply_apply]; rw [polar]; rw [Q.exists_companion.choose_spec]; rw [sub_sub]; rw [add_sub_cancel_left]

/--
theorem `map_sum` / 定理 `map_sum`

English:
theorem map_sum
  given: {ι} [DecidableEq ι] (Q : QuadraticMap R M N) (s : Finset ι) (f : ι -> M)
  proof: by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    simp_rw [Finset.sum_cons, QuadraticMap.map_add, ih, add_assoc, Finset.sym2_cons,
      Finset.sum_filter, Finset.sum_disjUnion, Finset.sum_map, Finset.sum_cons,
      Sym2.mkEmbedding_apply, Sym2.mk_isDiag_

中文:
定理 map_sum
  条件: {ι} [DecidableEq ι] (Q : QuadraticMap R M N) (s : Finset ι) (f : ι -> M)
  证明: by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    simp_rw [Finset.sum_cons, QuadraticMap.map_add, ih, add_assoc, Finset.sym2_cons,
      Finset.sum_filter, Finset.sum_disjUnion, Finset.sum_map, Finset.sum_cons,
      Sym2.mkEmbedding_apply, Sym2.mk_isDiag_
-/
protected theorem map_sum {ι} [DecidableEq ι] (Q : QuadraticMap R M N) (s : Finset ι) (f : ι -> M) :
    Q (∑ i in s, f i) = ∑ i in s, Q (f i)
      + ∑ ij in s.sym2 with ¬ ij.IsDiag, polarSym2 Q (ij.map f) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    simp_rw [Finset.sum_cons, QuadraticMap.map_add, ih, add_assoc, Finset.sym2_cons,
      Finset.sum_filter, Finset.sum_disjUnion, Finset.sum_map, Finset.sum_cons,
      Sym2.mkEmbedding_apply, Sym2.mk_isDiag_iff, not_true, if_false, zero_add,
      Sym2.map_mk, polarSym2_sym2Mk, ← polarBilin_apply_apply, _root_.map_sum,
      polarBilin_apply_apply]
    congr 2
    rw [add_comm]
    congr! with i hi
    rw [if_pos (ne_of_mem_of_not_mem hi ha).symm]

/--
theorem `map_sum'` / 定理 `map_sum'`

English:
theorem map_sum'
  given: {ι} (Q : QuadraticMap R M N) (s : Finset ι) (f : ι -> M)
  proof: by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    simp_rw [Finset.sum_cons, QuadraticMap.map_add Q, ih, add_assoc, Finset.sym2_cons,
      Finset.sum_disjUnion, Finset.sum_map, Finset.sum_cons, Sym2.mkEmbedding_apply,
      Sym2.map_mk, polarSym2_sym2Mk, ←

中文:
定理 map_sum'
  条件: {ι} (Q : QuadraticMap R M N) (s : Finset ι) (f : ι -> M)
  证明: by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    simp_rw [Finset.sum_cons, QuadraticMap.map_add Q, ih, add_assoc, Finset.sym2_cons,
      Finset.sum_disjUnion, Finset.sum_map, Finset.sum_cons, Sym2.mkEmbedding_apply,
      Sym2.map_mk, polarSym2_sym2Mk, ←
-/
protected theorem map_sum' {ι} (Q : QuadraticMap R M N) (s : Finset ι) (f : ι -> M) :
    Q (∑ i in s, f i) = ∑ ij in s.sym2, polarSym2 Q (ij.map f) - ∑ i in s, Q (f i) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    simp_rw [Finset.sum_cons, QuadraticMap.map_add Q, ih, add_assoc, Finset.sym2_cons,
      Finset.sum_disjUnion, Finset.sum_map, Finset.sum_cons, Sym2.mkEmbedding_apply,
      Sym2.map_mk, polarSym2_sym2Mk, ← polarBilin_apply_apply, _root_.map_sum,
      polarBilin_apply_apply, polar_self]
    abel_nf

end CommRing

section SemiringOperators

variable [CommSemiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

section SMul

variable [Monoid S] [Monoid T] [DistribMulAction S N] [DistribMulAction T N]
variable [SMulCommClass S R N] [SMulCommClass T R N]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMul S (QuadraticMap R M N)
  body: ⟨fun a Q =>
    { toFun := a • ⇑Q
      toFun_smul := fun b x => by
        rw [Pi.smul_apply]; rw [Q.map_smul]; rw [Pi.smul_apply]; rw [smul_comm]
      exists_companion' :=
        let ⟨B, h⟩ := Q.exists_companion
        letI := SMulCommClass.symm S R N
        ⟨a • B, by simp [h]⟩ }⟩

中文:
实例 :
  签名: SMul S (QuadraticMap R M N)
  定义体: ⟨fun a Q =>
    { toFun := a • ⇑Q
      toFun_smul := fun b x => by
        rw [Pi.smul_apply]; rw [Q.map_smul]; rw [Pi.smul_apply]; rw [smul_comm]
      exists_companion' :=
        let ⟨B, h⟩ := Q.exists_companion
        letI := SMulCommClass.symm S R N
        ⟨a • B, by simp [h]⟩ }⟩

Depends on / 依赖: Pi.smul_apply, Q.exists_companion, Q.map_smul, SMulCommClass, SMulCommClass.symm, exists_companion, map_smul, smul_apply, smul_comm, toFun_smul
-/
instance : SMul S (QuadraticMap R M N) :=
  ⟨fun a Q =>
    { toFun := a • ⇑Q
      toFun_smul := fun b x => by
        rw [Pi.smul_apply]; rw [Q.map_smul]; rw [Pi.smul_apply]; rw [smul_comm]
      exists_companion' :=
        let ⟨B, h⟩ := Q.exists_companion
        letI := SMulCommClass.symm S R N
        ⟨a • B, by simp [h]⟩ }⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsSMulApply S (QuadraticMap R M N) M N
  body: rfl

@[deprecated (since := "2026-07-27")] alias coeFn_smul := FunLike.coe_smul

@[deprecated (since := "2026-07-27")] protected alias smul_apply := smul_apply

中文:
实例 :
  签名: IsSMulApply S (QuadraticMap R M N) M N
  定义体: rfl

@[deprecated (since := "2026-07-27")] alias coeFn_smul := FunLike.coe_smul

@[deprecated (since := "2026-07-27")] protected alias smul_apply := smul_apply
-/
instance : IsSMulApply S (QuadraticMap R M N) M N where
  smul_apply _ _ _ := rfl

@[deprecated (since := "2026-07-27")] alias coeFn_smul := FunLike.coe_smul

@[deprecated (since := "2026-07-27")] protected alias smul_apply := smul_apply

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMulCommClass
  signature: S T N] : SMulCommClass S T (QuadraticMap R M N)
  body: FunLike.smulCommClass

中文:
实例 [SMulCommClass
  签名: S T N] : SMulCommClass S T (QuadraticMap R M N)
  定义体: FunLike.smulCommClass

Depends on / 依赖: FunLike, FunLike.smulCommClass, smulCommClass
-/
instance [SMulCommClass S T N] : SMulCommClass S T (QuadraticMap R M N) :=
  FunLike.smulCommClass

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: S T] [IsScalarTower S T N] : IsScalarTower S T (QuadraticMap R M N)
  body: FunLike.isScalarTower

中文:
实例 [SMul
  签名: S T] [IsScalarTower S T N] : IsScalarTower S T (QuadraticMap R M N)
  定义体: FunLike.isScalarTower

Depends on / 依赖: FunLike, FunLike.isScalarTower, isScalarTower
-/
instance [SMul S T] [IsScalarTower S T N] : IsScalarTower S T (QuadraticMap R M N) :=
  FunLike.isScalarTower

end SMul

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Zero (QuadraticMap R M N)
  body: ⟨{ toFun := fun _ => 0
      toFun_smul := fun a _ => by simp only [smul_zero]
      exists_companion' := ⟨0, fun _ _ => by simp only [add_zero, LinearMap.zero_apply]⟩ }⟩

中文:
实例 :
  签名: Zero (QuadraticMap R M N)
  定义体: ⟨{ toFun := fun _ => 0
      toFun_smul := fun a _ => by simp only [smul_zero]
      exists_companion' := ⟨0, fun _ _ => by simp only [add_zero, LinearMap.zero_apply]⟩ }⟩

Depends on / 依赖: LinearMap, LinearMap.zero_apply, add_zero, exists_companion, smul_zero, toFun_smul, zero_apply
-/
instance : Zero (QuadraticMap R M N) :=
  ⟨{ toFun := fun _ => 0
      toFun_smul := fun a _ => by simp only [smul_zero]
      exists_companion' := ⟨0, fun _ _ => by simp only [add_zero, LinearMap.zero_apply]⟩ }⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsZeroApply (QuadraticMap R M N) M N
  body: rfl

@[deprecated (since := "2026-07-27")] alias coeFn_zero := FunLike.coe_zero

@[deprecated (since := "2026-07-27")] protected alias zero_apply := zero_apply

中文:
实例 :
  签名: IsZeroApply (QuadraticMap R M N) M N
  定义体: rfl

@[deprecated (since := "2026-07-27")] alias coeFn_zero := FunLike.coe_zero

@[deprecated (since := "2026-07-27")] protected alias zero_apply := zero_apply
-/
instance : IsZeroApply (QuadraticMap R M N) M N where
  zero_apply _ := rfl

@[deprecated (since := "2026-07-27")] alias coeFn_zero := FunLike.coe_zero

@[deprecated (since := "2026-07-27")] protected alias zero_apply := zero_apply

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (QuadraticMap R M N)
  body: ⟨0⟩

中文:
实例 :
  签名: Inhabited (QuadraticMap R M N)
  定义体: ⟨0⟩
-/
instance : Inhabited (QuadraticMap R M N) :=
  ⟨0⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Add (QuadraticMap R M N)
  body: ⟨fun Q Q' =>
    { toFun := Q + Q'
      toFun_smul := fun a x => by simp only [Pi.add_apply, smul_add, QuadraticMap.map_smul]
      exists_companion' :=
        let ⟨B, h⟩ := Q.exists_companion
        let ⟨B', h'⟩ := Q'.exists_companion
        ⟨B + B', fun x y => by
          simp_rw [Pi.add_appl

中文:
实例 :
  签名: Add (QuadraticMap R M N)
  定义体: ⟨fun Q Q' =>
    { toFun := Q + Q'
      toFun_smul := fun a x => by simp only [Pi.add_apply, smul_add, QuadraticMap.map_smul]
      exists_companion' :=
        let ⟨B, h⟩ := Q.exists_companion
        let ⟨B', h'⟩ := Q'.exists_companion
        ⟨B + B', fun x y => by
          simp_rw [Pi.add_appl

Depends on / 依赖: LinearMap, LinearMap.add_apply, Pi.add_apply, Q.exists_companion, QuadraticMap, QuadraticMap.map_smul, add_add_add_comm, add_apply, exists_companion, map_smul, simp_rw, smul_add, toFun_smul
-/
instance : Add (QuadraticMap R M N) :=
  ⟨fun Q Q' =>
    { toFun := Q + Q'
      toFun_smul := fun a x => by simp only [Pi.add_apply, smul_add, QuadraticMap.map_smul]
      exists_companion' :=
        let ⟨B, h⟩ := Q.exists_companion
        let ⟨B', h'⟩ := Q'.exists_companion
        ⟨B + B', fun x y => by
          simp_rw [Pi.add_apply, h, h', LinearMap.add_apply, add_add_add_comm]⟩ }⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsAddApply (QuadraticMap R M N) M N
  body: rfl

@[deprecated (since := "2026-07-27")] alias coeFn_add := FunLike.coe_add

@[deprecated (since := "2026-07-27")] protected alias add_apply := add_apply

中文:
实例 :
  签名: IsAddApply (QuadraticMap R M N) M N
  定义体: rfl

@[deprecated (since := "2026-07-27")] alias coeFn_add := FunLike.coe_add

@[deprecated (since := "2026-07-27")] protected alias add_apply := add_apply
-/
instance : IsAddApply (QuadraticMap R M N) M N where
  add_apply _ _ _ := rfl

@[deprecated (since := "2026-07-27")] alias coeFn_add := FunLike.coe_add

@[deprecated (since := "2026-07-27")] protected alias add_apply := add_apply

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddCommMonoid (QuadraticMap R M N)
  body: fast_instance% FunLike.addCommMonoid

@[deprecated (since := "2026-07-27")] alias coeFnAddMonoidHom := FunLike.coeAddMonoidHom

@[deprecated (since := "2026-07-27")] alias coeFnAddMonoidHom_apply := FunLike.coeAddMonoidHom_apply

中文:
实例 :
  签名: AddCommMonoid (QuadraticMap R M N)
  定义体: fast_instance% FunLike.addCommMonoid

@[deprecated (since := "2026-07-27")] alias coeFnAddMonoidHom := FunLike.coeAddMonoidHom

@[deprecated (since := "2026-07-27")] alias coeFnAddMonoidHom_apply := FunLike.coeAddMonoidHom_apply

Depends on / 依赖: FunLike, FunLike.addCommMonoid, addCommMonoid, fast_instance
-/
instance : AddCommMonoid (QuadraticMap R M N) := fast_instance% FunLike.addCommMonoid

@[deprecated (since := "2026-07-27")] alias coeFnAddMonoidHom := FunLike.coeAddMonoidHom

@[deprecated (since := "2026-07-27")] alias coeFnAddMonoidHom_apply := FunLike.coeAddMonoidHom_apply

/-- Evaluation on a particular element of the module `M` is an additive map on quadratic maps. -/
@[simps! apply]
/--
Definition of `evalAddMonoidHom` / `evalAddMonoidHom` 的定义

English:
definition evalAddMonoidHom
  signature: (m : M)
  body: (Pi.evalAddMonoidHom _ m).comp (FunLike.coeAddMonoidHom _ _ _)

@[deprecated (since := "2026-07-27")] alias coeFn_sum := FunLike.coe_sum

@[deprecated (since := "2026-07-27")] protected alias sum_apply := sum_apply

中文:
定义 evalAddMonoidHom
  签名: (m : M)
  定义体: (Pi.evalAddMonoidHom _ m).comp (FunLike.coeAddMonoidHom _ _ _)

@[deprecated (since := "2026-07-27")] alias coeFn_sum := FunLike.coe_sum

@[deprecated (since := "2026-07-27")] protected alias sum_apply := sum_apply

Depends on / 依赖: FunLike, FunLike.coeAddMonoidHom, Pi.evalAddMonoidHom, coeAddMonoidHom, evalAddMonoidHom
-/
def evalAddMonoidHom (m : M) : QuadraticMap R M N ->+ N :=
  (Pi.evalAddMonoidHom _ m).comp (FunLike.coeAddMonoidHom _ _ _)

@[deprecated (since := "2026-07-27")] alias coeFn_sum := FunLike.coe_sum

@[deprecated (since := "2026-07-27")] protected alias sum_apply := sum_apply

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Monoid
  signature: S] [DistribMulAction S N] [SMulCommClass S R N] :
  body: fast_instance% FunLike.distribMulAction

中文:
实例 [Monoid
  签名: S] [DistribMulAction S N] [SMulCommClass S R N] :
  定义体: fast_instance% FunLike.distribMulAction

Depends on / 依赖: FunLike, FunLike.distribMulAction, distribMulAction, fast_instance
-/
instance [Monoid S] [DistribMulAction S N] [SMulCommClass S R N] :
    DistribMulAction S (QuadraticMap R M N) := fast_instance% FunLike.distribMulAction

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Semiring
  signature: S] [Module S N] [SMulCommClass S R N] :
  body: fast_instance% FunLike.module

中文:
实例 [Semiring
  签名: S] [Module S N] [SMulCommClass S R N] :
  定义体: fast_instance% FunLike.module

Depends on / 依赖: FunLike, FunLike.module, fast_instance, module
-/
instance [Semiring S] [Module S N] [SMulCommClass S R N] :
    Module S (QuadraticMap R M N) := fast_instance% FunLike.module

end SemiringOperators

section RingOperators

variable [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Neg (QuadraticMap R M N)
  body: ⟨fun Q =>
    { toFun := -Q
      toFun_smul := fun a x => by simp only [Pi.neg_apply, Q.map_smul, smul_neg]
      exists_companion' :=
        let ⟨B, h⟩ := Q.exists_companion
        ⟨-B, fun x y => by simp_rw [Pi.neg_apply, h, LinearMap.neg_apply, neg_add]⟩ }⟩

中文:
实例 :
  签名: Neg (QuadraticMap R M N)
  定义体: ⟨fun Q =>
    { toFun := -Q
      toFun_smul := fun a x => by simp only [Pi.neg_apply, Q.map_smul, smul_neg]
      exists_companion' :=
        let ⟨B, h⟩ := Q.exists_companion
        ⟨-B, fun x y => by simp_rw [Pi.neg_apply, h, LinearMap.neg_apply, neg_add]⟩ }⟩

Depends on / 依赖: LinearMap, LinearMap.neg_apply, Pi.neg_apply, Q.exists_companion, Q.map_smul, exists_companion, map_smul, neg_add, neg_apply, simp_rw, smul_neg, toFun_smul
-/
instance : Neg (QuadraticMap R M N) :=
  ⟨fun Q =>
    { toFun := -Q
      toFun_smul := fun a x => by simp only [Pi.neg_apply, Q.map_smul, smul_neg]
      exists_companion' :=
        let ⟨B, h⟩ := Q.exists_companion
        ⟨-B, fun x y => by simp_rw [Pi.neg_apply, h, LinearMap.neg_apply, neg_add]⟩ }⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsNegApply (QuadraticMap R M N) M N
  body: rfl

@[deprecated (since := "2026-07-27")] alias coeFn_neg := FunLike.coe_neg

@[deprecated (since := "2026-07-27")] protected alias neg_apply := neg_apply

中文:
实例 :
  签名: IsNegApply (QuadraticMap R M N) M N
  定义体: rfl

@[deprecated (since := "2026-07-27")] alias coeFn_neg := FunLike.coe_neg

@[deprecated (since := "2026-07-27")] protected alias neg_apply := neg_apply
-/
instance : IsNegApply (QuadraticMap R M N) M N where
  neg_apply _ _ := rfl

@[deprecated (since := "2026-07-27")] alias coeFn_neg := FunLike.coe_neg

@[deprecated (since := "2026-07-27")] protected alias neg_apply := neg_apply

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Sub (QuadraticMap R M N)
  body: ⟨fun Q Q' => (Q + -Q').copy (Q - Q') (sub_eq_add_neg _ _)⟩

中文:
实例 :
  签名: Sub (QuadraticMap R M N)
  定义体: ⟨fun Q Q' => (Q + -Q').copy (Q - Q') (sub_eq_add_neg _ _)⟩

Depends on / 依赖: sub_eq_add_neg
-/
instance : Sub (QuadraticMap R M N) :=
  ⟨fun Q Q' => (Q + -Q').copy (Q - Q') (sub_eq_add_neg _ _)⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsSubApply (QuadraticMap R M N) M N
  body: rfl

@[deprecated (since := "2026-07-27")] alias coeFn_sub := FunLike.coe_sub

@[deprecated (since := "2026-07-27")] protected alias sub_apply := sub_apply

中文:
实例 :
  签名: IsSubApply (QuadraticMap R M N) M N
  定义体: rfl

@[deprecated (since := "2026-07-27")] alias coeFn_sub := FunLike.coe_sub

@[deprecated (since := "2026-07-27")] protected alias sub_apply := sub_apply
-/
instance : IsSubApply (QuadraticMap R M N) M N where
  sub_apply _ _ _ := rfl

@[deprecated (since := "2026-07-27")] alias coeFn_sub := FunLike.coe_sub

@[deprecated (since := "2026-07-27")] protected alias sub_apply := sub_apply

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddCommGroup (QuadraticMap R M N)
  body: fast_instance% FunLike.addCommGroup

中文:
实例 :
  签名: AddCommGroup (QuadraticMap R M N)
  定义体: fast_instance% FunLike.addCommGroup

Depends on / 依赖: FunLike, FunLike.addCommGroup, addCommGroup, fast_instance
-/
instance : AddCommGroup (QuadraticMap R M N) := fast_instance% FunLike.addCommGroup

end RingOperators

section restrictScalars

variable [CommSemiring R] [CommSemiring S] [AddCommMonoid M] [Module R M] [AddCommMonoid N]
  [Module R N] [Module S M] [Module S N] [Algebra S R]
variable [IsScalarTower S R M] [IsScalarTower S R N]

/-- If `Q : M → N` is a quadratic map of `R`-modules and `R` is an `S`-algebra,
then the restriction of scalars is a quadratic map of `S`-modules. -/
@[simps!]
/--
Definition of `restrictScalars` / `restrictScalars` 的定义

English:
definition restrictScalars
  signature: (Q : QuadraticMap R M N)
  body: Q x
  toFun_smul a x := by
    simp [map_smul_of_tower]
  exists_companion' :=
    let ⟨B, h⟩ := Q.exists_companion
    ⟨B.restrictScalars₁₂ (S := R) (R' := S) (S' := S), fun x y => by
      simp only [LinearMap.restrictScalars₁₂_apply_apply, h]⟩

中文:
定义 restrictScalars
  签名: (Q : QuadraticMap R M N)
  定义体: Q x
  toFun_smul a x := by
    simp [map_smul_of_tower]
  exists_companion' :=
    let ⟨B, h⟩ := Q.exists_companion
    ⟨B.restrictScalars₁₂ (S := R) (R' := S) (S' := S), fun x y => by
      simp only [LinearMap.restrictScalars₁₂_apply_apply, h]⟩
-/
def restrictScalars (Q : QuadraticMap R M N) : QuadraticMap S M N where
  toFun x := Q x
  toFun_smul a x := by
    simp [map_smul_of_tower]
  exists_companion' :=
    let ⟨B, h⟩ := Q.exists_companion
    ⟨B.restrictScalars₁₂ (S := R) (R' := S) (S' := S), fun x y => by
      simp only [LinearMap.restrictScalars₁₂_apply_apply, h]⟩

end restrictScalars

section Comp

variable [CommSemiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
variable [AddCommMonoid P] [Module R P]

/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: (Q : QuadraticMap R N P) (f : M ->ₗ[R] N)
  body: Q (f x)
  toFun_smul a x := by simp only [Q.map_smul, map_smul]
  exists_companion' :=
    let ⟨B, h⟩ := Q.exists_companion
    ⟨B.compl₁₂ f f, fun x y => by simp_rw [f.map_add]; exact h (f x) (f y)⟩

@[simp]

中文:
定义 comp
  签名: (Q : QuadraticMap R N P) (f : M ->ₗ[R] N)
  定义体: Q (f x)
  toFun_smul a x := by simp only [Q.map_smul, map_smul]
  exists_companion' :=
    let ⟨B, h⟩ := Q.exists_companion
    ⟨B.compl₁₂ f f, fun x y => by simp_rw [f.map_add]; exact h (f x) (f y)⟩

@[simp]
-/
def comp (Q : QuadraticMap R N P) (f : M ->ₗ[R] N) : QuadraticMap R M P where
  toFun x := Q (f x)
  toFun_smul a x := by simp only [Q.map_smul, map_smul]
  exists_companion' :=
    let ⟨B, h⟩ := Q.exists_companion
    ⟨B.compl₁₂ f f, fun x y => by simp_rw [f.map_add]; exact h (f x) (f y)⟩

@[simp]
/--
theorem `comp_apply` / 定理 `comp_apply`

English:
theorem comp_apply
  given: (Q : QuadraticMap R N P) (f : M ->ₗ[R] N) (x : M)
  statement: (Q.comp f) x = Q (f x)
  proof: rfl

中文:
定理 comp_apply
  条件: (Q : QuadraticMap R N P) (f : M ->ₗ[R] N) (x : M)
  结论: (Q.comp f) x = Q (f x)
  证明: rfl
-/
theorem comp_apply (Q : QuadraticMap R N P) (f : M ->ₗ[R] N) (x : M) : (Q.comp f) x = Q (f x) :=
  rfl

/-- Compose a quadratic map with a linear function on the left. -/
@[simps +simpRhs]
/--
Definition of `_root_.LinearMap.compQuadraticMap` / `_root_.LinearMap.compQuadraticMap` 的定义

English:
definition _root_.LinearMap.compQuadraticMap
  signature: (f : N ->ₗ[R] P) (Q : QuadraticMap R M N)
  body: f (Q x)
  toFun_smul b x := by simp only [Q.map_smul, map_smul]
  exists_companion' :=
    let ⟨B, h⟩ := Q.exists_companion
    ⟨B.compr₂ f, fun x y => by simp only [h, map_add, LinearMap.compr₂_apply]⟩

中文:
定义 _root_.LinearMap.compQuadraticMap
  签名: (f : N ->ₗ[R] P) (Q : QuadraticMap R M N)
  定义体: f (Q x)
  toFun_smul b x := by simp only [Q.map_smul, map_smul]
  exists_companion' :=
    let ⟨B, h⟩ := Q.exists_companion
    ⟨B.compr₂ f, fun x y => by simp only [h, map_add, LinearMap.compr₂_apply]⟩
-/
def _root_.LinearMap.compQuadraticMap (f : N ->ₗ[R] P) (Q : QuadraticMap R M N) :
    QuadraticMap R M P where
  toFun x := f (Q x)
  toFun_smul b x := by simp only [Q.map_smul, map_smul]
  exists_companion' :=
    let ⟨B, h⟩ := Q.exists_companion
    ⟨B.compr₂ f, fun x y => by simp only [h, map_add, LinearMap.compr₂_apply]⟩

/-- Compose a quadratic map with a linear function on the left. -/
@[simps! +simpRhs]
/--
Definition of `_root_.LinearMap.compQuadraticMap'` / `_root_.LinearMap.compQuadraticMap'` 的定义

English:
definition _root_.LinearMap.compQuadraticMap'
  signature: [CommSemiring S] [Algebra S R] [Module S N] [Module S M]
  body: _root_.LinearMap.compQuadraticMap f Q.restrictScalars

中文:
定义 _root_.LinearMap.compQuadraticMap'
  签名: [CommSemiring S] [Algebra S R] [Module S N] [Module S M]
  定义体: _root_.LinearMap.compQuadraticMap f Q.restrictScalars

Depends on / 依赖: LinearMap, Q.restrictScalars, _root_, _root_.LinearMap.compQuadraticMap, compQuadraticMap, restrictScalars
-/
def _root_.LinearMap.compQuadraticMap' [CommSemiring S] [Algebra S R] [Module S N] [Module S M]
    [IsScalarTower S R N] [IsScalarTower S R M] [Module S P]
    (f : N ->ₗ[S] P) (Q : QuadraticMap R M N) : QuadraticMap S M P :=
  _root_.LinearMap.compQuadraticMap f Q.restrictScalars

/-- When `N` and `P` are equivalent, quadratic maps on `M` into `N` are equivalent to quadratic
maps on `M` into `P`.

See `LinearMap.BilinMap.congr₂` for the bilinear map version. -/
@[simps apply]
/--
Definition of `_root_.LinearEquiv.congrQuadraticMap` / `_root_.LinearEquiv.congrQuadraticMap` 的定义

English:
definition _root_.LinearEquiv.congrQuadraticMap
  signature: (e : N ≃ₗ[R] P)
  body: e.compQuadraticMap Q
  invFun Q := e.symm.compQuadraticMap Q
  left_inv _ := ext fun _ => e.symm_apply_apply _
  right_inv _ := ext fun _ => e.apply_symm_apply _
  map_add' _ _ := ext fun _ => map_add e _ _
  map_smul' _ _ := ext fun _ => e.map_smul _ _

@[simp]

中文:
定义 _root_.LinearEquiv.congrQuadraticMap
  签名: (e : N ≃ₗ[R] P)
  定义体: e.compQuadraticMap Q
  invFun Q := e.symm.compQuadraticMap Q
  left_inv _ := ext fun _ => e.symm_apply_apply _
  right_inv _ := ext fun _ => e.apply_symm_apply _
  map_add' _ _ := ext fun _ => map_add e _ _
  map_smul' _ _ := ext fun _ => e.map_smul _ _

@[simp]

Depends on / 依赖: compQuadraticMap, e.compQuadraticMap
-/
def _root_.LinearEquiv.congrQuadraticMap (e : N ≃ₗ[R] P) :
    QuadraticMap R M N ≃ₗ[R] QuadraticMap R M P where
  toFun Q := e.compQuadraticMap Q
  invFun Q := e.symm.compQuadraticMap Q
  left_inv _ := ext fun _ => e.symm_apply_apply _
  right_inv _ := ext fun _ => e.apply_symm_apply _
  map_add' _ _ := ext fun _ => map_add e _ _
  map_smul' _ _ := ext fun _ => e.map_smul _ _

@[simp]
/--
theorem `_root_.LinearEquiv.congrQuadraticMap_refl` / 定理 `_root_.LinearEquiv.congrQuadraticMap_refl`

English:
theorem _root_.LinearEquiv.congrQuadraticMap_refl
  proof: rfl

@[simp]

中文:
定理 _root_.LinearEquiv.congrQuadraticMap_refl
  证明: rfl

@[simp]
-/
theorem _root_.LinearEquiv.congrQuadraticMap_refl :
    LinearEquiv.congrQuadraticMap (.refl R N) = .refl R (QuadraticMap R M N) := rfl

@[simp]
/--
theorem `_root_.LinearEquiv.congrQuadraticMap_symm` / 定理 `_root_.LinearEquiv.congrQuadraticMap_symm`

English:
theorem _root_.LinearEquiv.congrQuadraticMap_symm
  given: (e : N ≃ₗ[R] P)
  proof: rfl

中文:
定理 _root_.LinearEquiv.congrQuadraticMap_symm
  条件: (e : N ≃ₗ[R] P)
  证明: rfl

Depends on / 依赖: congrQuadraticMap, e.symm.congrQuadraticMap
-/
theorem _root_.LinearEquiv.congrQuadraticMap_symm (e : N ≃ₗ[R] P) :
    (LinearEquiv.congrQuadraticMap e (M := M)).symm = e.symm.congrQuadraticMap := rfl

end Comp

section NonUnitalNonAssocSemiring

variable [CommSemiring R] [NonUnitalNonAssocSemiring A] [AddCommMonoid M] [Module R M]
variable [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]

/--
Definition of `linMulLin` / `linMulLin` 的定义

English:
definition linMulLin
  signature: (f g : M ->ₗ[R] A)
  body: f * g
  toFun_smul a x := by
    rw [Pi.mul_apply]; rw [Pi.mul_apply]; rw [map_smulₛₗ]; rw [RingHom.id_apply]; rw [map_smulₛₗ]; rw [RingHom.id_apply]; rw [smul_mul_assoc]; rw [mul_smul_comm]; rw [← smul_assoc]; rw [smul_eq_mul]
  exists_companion' :=
    ⟨(LinearMap.mul R A).compl₁₂ f g + (LinearMap

中文:
定义 linMulLin
  签名: (f g : M ->ₗ[R] A)
  定义体: f * g
  toFun_smul a x := by
    rw [Pi.mul_apply]; rw [Pi.mul_apply]; rw [map_smulₛₗ]; rw [RingHom.id_apply]; rw [map_smulₛₗ]; rw [RingHom.id_apply]; rw [smul_mul_assoc]; rw [mul_smul_comm]; rw [← smul_assoc]; rw [smul_eq_mul]
  exists_companion' :=
    ⟨(LinearMap.mul R A).compl₁₂ f g + (LinearMap
-/
def linMulLin (f g : M ->ₗ[R] A) : QuadraticMap R M A where
  toFun := f * g
  toFun_smul a x := by
    rw [Pi.mul_apply]; rw [Pi.mul_apply]; rw [map_smulₛₗ]; rw [RingHom.id_apply]; rw [map_smulₛₗ]; rw [RingHom.id_apply]; rw [smul_mul_assoc]; rw [mul_smul_comm]; rw [← smul_assoc]; rw [smul_eq_mul]
  exists_companion' :=
    ⟨(LinearMap.mul R A).compl₁₂ f g + (LinearMap.mul R A).flip.compl₁₂ g f, fun x y => by
      simp only [Pi.mul_apply, map_add, left_distrib, right_distrib, LinearMap.add_apply,
        LinearMap.compl₁₂_apply, LinearMap.mul_apply', LinearMap.flip_apply]
      abel_nf⟩

@[simp]
/--
theorem `linMulLin_apply` / 定理 `linMulLin_apply`

English:
theorem linMulLin_apply
  given: (f g : M ->ₗ[R] A) (x)
  statement: linMulLin f g x = f x * g x
  proof: rfl

@[simp]

中文:
定理 linMulLin_apply
  条件: (f g : M ->ₗ[R] A) (x)
  结论: linMulLin f g x = f x * g x
  证明: rfl

@[simp]
-/
theorem linMulLin_apply (f g : M ->ₗ[R] A) (x) : linMulLin f g x = f x * g x :=
  rfl

@[simp]
/--
theorem `add_linMulLin` / 定理 `add_linMulLin`

English:
theorem add_linMulLin
  given: (f g h : M ->ₗ[R] A)
  statement: linMulLin (f + g) h = linMulLin f h + linMulLin g h
  proof: ext fun _ => add_mul _ _ _

@[simp]

中文:
定理 add_linMulLin
  条件: (f g h : M ->ₗ[R] A)
  结论: linMulLin (f + g) h = linMulLin f h + linMulLin g h
  证明: ext fun _ => add_mul _ _ _

@[simp]

Depends on / 依赖: add_mul
-/
theorem add_linMulLin (f g h : M ->ₗ[R] A) : linMulLin (f + g) h = linMulLin f h + linMulLin g h :=
  ext fun _ => add_mul _ _ _

@[simp]
/--
theorem `linMulLin_add` / 定理 `linMulLin_add`

English:
theorem linMulLin_add
  given: (f g h : M ->ₗ[R] A)
  statement: linMulLin f (g + h) = linMulLin f g + linMulLin f h
  proof: ext fun _ => mul_add _ _ _

中文:
定理 linMulLin_add
  条件: (f g h : M ->ₗ[R] A)
  结论: linMulLin f (g + h) = linMulLin f g + linMulLin f h
  证明: ext fun _ => mul_add _ _ _

Depends on / 依赖: mul_add
-/
theorem linMulLin_add (f g h : M ->ₗ[R] A) : linMulLin f (g + h) = linMulLin f g + linMulLin f h :=
  ext fun _ => mul_add _ _ _

variable {N' : Type*} [AddCommMonoid N'] [Module R N']

@[simp]
/--
theorem `linMulLin_comp` / 定理 `linMulLin_comp`

English:
theorem linMulLin_comp
  given: (f g : M ->ₗ[R] A) (h : N' ->ₗ[R] M)
  proof: rfl

中文:
定理 linMulLin_comp
  条件: (f g : M ->ₗ[R] A) (h : N' ->ₗ[R] M)
  证明: rfl
-/
theorem linMulLin_comp (f g : M ->ₗ[R] A) (h : N' ->ₗ[R] M) :
    (linMulLin f g).comp h = linMulLin (f.comp h) (g.comp h) :=
  rfl

variable {n : Type*}

/-- `sq` is the quadratic map sending the vector `x : A` to `x * x` -/
@[simps!]
/--
Definition of `sq` / `sq` 的定义

English:
definition sq
  signature: : QuadraticMap R A A
  body: linMulLin LinearMap.id LinearMap.id

中文:
定义 sq
  签名: : QuadraticMap R A A
  定义体: linMulLin LinearMap.id LinearMap.id

Depends on / 依赖: LinearMap, LinearMap.id, linMulLin
-/
def sq : QuadraticMap R A A :=
  linMulLin LinearMap.id LinearMap.id

/--
Definition of `proj` / `proj` 的定义

English:
definition proj
  signature: (i j : n)
  body: linMulLin (@LinearMap.proj _ _ _ (fun _ => A) _ _ i) (@LinearMap.proj _ _ _ (fun _ => A) _ _ j)

@[simp]

中文:
定义 proj
  签名: (i j : n)
  定义体: linMulLin (@LinearMap.proj _ _ _ (fun _ => A) _ _ i) (@LinearMap.proj _ _ _ (fun _ => A) _ _ j)

@[simp]

Depends on / 依赖: LinearMap, LinearMap.proj, linMulLin
-/
def proj (i j : n) : QuadraticMap R (n -> A) A :=
  linMulLin (@LinearMap.proj _ _ _ (fun _ => A) _ _ i) (@LinearMap.proj _ _ _ (fun _ => A) _ _ j)

@[simp]
/--
theorem `proj_apply` / 定理 `proj_apply`

English:
theorem proj_apply
  given: (i j : n) (x : n -> A)
  statement: proj (R := R) i j x = x i * x j
  proof: rfl

中文:
定理 proj_apply
  条件: (i j : n) (x : n -> A)
  结论: proj (R := R) i j x = x i * x j
  证明: rfl
-/
theorem proj_apply (i j : n) (x : n -> A) : proj (R := R) i j x = x i * x j :=
  rfl

end NonUnitalNonAssocSemiring

end QuadraticMap

/-!
### Associated bilinear maps

If multiplication by 2 is invertible on the target module `N` of
`QuadraticMap R M N`, then there is a linear bijection `QuadraticMap.associated`
between quadratic maps `Q` over `R` from `M` to `N` and symmetric bilinear maps
`B : M →ₗ[R] M →ₗ[R] → N` such that `BilinMap.toQuadraticMap B = Q`
(see `QuadraticMap.associated_rightInverse`). The associated bilinear map is half
`Q.polarBilin` (see `QuadraticMap.two_nsmul_associated`); this is where the invertibility condition
comes from. We spell the condition as `[Invertible (2 : Module.End R N)]`.

Note that this makes the bijection available in more cases than the simpler condition
`Invertible (2 : R)`, e.g., when `R = ℤ` and `N = ℝ`.
-/

namespace LinearMap

namespace BilinMap

open QuadraticMap
open LinearMap (BilinMap)

section Semiring

variable [CommSemiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
variable {N' : Type*} [AddCommMonoid N'] [Module R N']

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `toQuadraticMap` / `toQuadraticMap` 的定义

English:
definition toQuadraticMap
  signature: (B : BilinMap R M N)
  body: B x x
  toFun_smul a x := by simp only [map_smul, LinearMap.smul_apply, smul_smul]
  exists_companion' := ⟨B + LinearMap.flip B, fun x y => by simp [add_add_add_comm, add_comm]⟩

@[simp]

中文:
定义 toQuadraticMap
  签名: (B : BilinMap R M N)
  定义体: B x x
  toFun_smul a x := by simp only [map_smul, LinearMap.smul_apply, smul_smul]
  exists_companion' := ⟨B + LinearMap.flip B, fun x y => by simp [add_add_add_comm, add_comm]⟩

@[simp]
-/
def toQuadraticMap (B : BilinMap R M N) : QuadraticMap R M N where
  toFun x := B x x
  toFun_smul a x := by simp only [map_smul, LinearMap.smul_apply, smul_smul]
  exists_companion' := ⟨B + LinearMap.flip B, fun x y => by simp [add_add_add_comm, add_comm]⟩

@[simp]
/--
theorem `toQuadraticMap_apply` / 定理 `toQuadraticMap_apply`

English:
theorem toQuadraticMap_apply
  given: (B : BilinMap R M N) (x : M)
  statement: B.toQuadraticMap x = B x x
  proof: rfl

中文:
定理 toQuadraticMap_apply
  条件: (B : BilinMap R M N) (x : M)
  结论: B.toQuadraticMap x = B x x
  证明: rfl
-/
theorem toQuadraticMap_apply (B : BilinMap R M N) (x : M) : B.toQuadraticMap x = B x x :=
  rfl

/--
theorem `toQuadraticMap_comp_same` / 定理 `toQuadraticMap_comp_same`

English:
theorem toQuadraticMap_comp_same
  given: (B : BilinMap R M N) (f : N' ->ₗ[R] M)
  proof: rfl

中文:
定理 toQuadraticMap_comp_same
  条件: (B : BilinMap R M N) (f : N' ->ₗ[R] M)
  证明: rfl
-/
theorem toQuadraticMap_comp_same (B : BilinMap R M N) (f : N' ->ₗ[R] M) :
    BilinMap.toQuadraticMap (B.compl₁₂ f f) = B.toQuadraticMap.comp f := rfl

section

variable (R M)

@[simp]
/--
theorem `toQuadraticMap_zero` / 定理 `toQuadraticMap_zero`

English:
theorem toQuadraticMap_zero
  statement: (0 : BilinMap R M N).toQuadraticMap = 0
  proof: rfl

中文:
定理 toQuadraticMap_zero
  结论: (0 : BilinMap R M N).toQuadraticMap = 0
  证明: rfl
-/
theorem toQuadraticMap_zero : (0 : BilinMap R M N).toQuadraticMap = 0 :=
  rfl

end

@[simp]
/--
theorem `toQuadraticMap_add` / 定理 `toQuadraticMap_add`

English:
theorem toQuadraticMap_add
  given: (B₁ B₂ : BilinMap R M N)
  proof: rfl

@[simp]

中文:
定理 toQuadraticMap_add
  条件: (B₁ B₂ : BilinMap R M N)
  证明: rfl

@[simp]
-/
theorem toQuadraticMap_add (B₁ B₂ : BilinMap R M N) :
    (B₁ + B₂).toQuadraticMap = B₁.toQuadraticMap + B₂.toQuadraticMap :=
  rfl

@[simp]
/--
theorem `toQuadraticMap_smul` / 定理 `toQuadraticMap_smul`

English:
theorem toQuadraticMap_smul
  statement: [Monoid S] [DistribMulAction S N] [SMulCommClass S R N]
  proof: rfl

中文:
定理 toQuadraticMap_smul
  结论: [Monoid S] [DistribMulAction S N] [SMulCommClass S R N]
  证明: rfl
-/
theorem toQuadraticMap_smul [Monoid S] [DistribMulAction S N] [SMulCommClass S R N]
    [SMulCommClass R S N] (a : S)
    (B : BilinMap R M N) : (a • B).toQuadraticMap = a • B.toQuadraticMap :=
  rfl

section

variable (S R M)

/-- `LinearMap.BilinMap.toQuadraticMap` as an additive homomorphism -/
@[simps]
/--
Definition of `toQuadraticMapAddMonoidHom` / `toQuadraticMapAddMonoidHom` 的定义

English:
definition toQuadraticMapAddMonoidHom
  signature: : (BilinMap R M N) ->+ QuadraticMap R M N where
  body: toQuadraticMap
  map_zero' := toQuadraticMap_zero _ _
  map_add' := toQuadraticMap_add

中文:
定义 toQuadraticMapAddMonoidHom
  签名: : (BilinMap R M N) ->+ QuadraticMap R M N where
  定义体: toQuadraticMap
  map_zero' := toQuadraticMap_zero _ _
  map_add' := toQuadraticMap_add

Depends on / 依赖: toQuadraticMap
-/
def toQuadraticMapAddMonoidHom : (BilinMap R M N) ->+ QuadraticMap R M N where
  toFun := toQuadraticMap
  map_zero' := toQuadraticMap_zero _ _
  map_add' := toQuadraticMap_add

/-- `LinearMap.BilinMap.toQuadraticMap` as a linear map -/
@[simps]
/--
Definition of `toQuadraticMapLinearMap` / `toQuadraticMapLinearMap` 的定义

English:
definition toQuadraticMapLinearMap
  signature: [Semiring S] [Module S N] [SMulCommClass S R N] [SMulCommClass R S N]
  body: toQuadraticMap
  map_smul' := toQuadraticMap_smul
  map_add' := toQuadraticMap_add

中文:
定义 toQuadraticMapLinearMap
  签名: [Semiring S] [Module S N] [SMulCommClass S R N] [SMulCommClass R S N]
  定义体: toQuadraticMap
  map_smul' := toQuadraticMap_smul
  map_add' := toQuadraticMap_add

Depends on / 依赖: toQuadraticMap
-/
def toQuadraticMapLinearMap [Semiring S] [Module S N] [SMulCommClass S R N] [SMulCommClass R S N] :
    (BilinMap R M N) ->ₗ[S] QuadraticMap R M N where
  toFun := toQuadraticMap
  map_smul' := toQuadraticMap_smul
  map_add' := toQuadraticMap_add

end

@[simp]
/--
theorem `toQuadraticMap_list_sum` / 定理 `toQuadraticMap_list_sum`

English:
theorem toQuadraticMap_list_sum
  given: (B : List (BilinMap R M N))
  proof: map_list_sum (toQuadraticMapAddMonoidHom R M) B

@[simp]

中文:
定理 toQuadraticMap_list_sum
  条件: (B : List (BilinMap R M N))
  证明: map_list_sum (toQuadraticMapAddMonoidHom R M) B

@[simp]

Depends on / 依赖: map_list_sum, toQuadraticMapAddMonoidHom
-/
theorem toQuadraticMap_list_sum (B : List (BilinMap R M N)) :
    B.sum.toQuadraticMap = (B.map toQuadraticMap).sum :=
  map_list_sum (toQuadraticMapAddMonoidHom R M) B

@[simp]
/--
theorem `toQuadraticMap_multiset_sum` / 定理 `toQuadraticMap_multiset_sum`

English:
theorem toQuadraticMap_multiset_sum
  given: (B : Multiset (BilinMap R M N))
  proof: map_multiset_sum (toQuadraticMapAddMonoidHom R M) B

@[simp]

中文:
定理 toQuadraticMap_multiset_sum
  条件: (B : Multiset (BilinMap R M N))
  证明: map_multiset_sum (toQuadraticMapAddMonoidHom R M) B

@[simp]

Depends on / 依赖: map_multiset_sum, toQuadraticMapAddMonoidHom
-/
theorem toQuadraticMap_multiset_sum (B : Multiset (BilinMap R M N)) :
    B.sum.toQuadraticMap = (B.map toQuadraticMap).sum :=
  map_multiset_sum (toQuadraticMapAddMonoidHom R M) B

@[simp]
/--
theorem `toQuadraticMap_sum` / 定理 `toQuadraticMap_sum`

English:
theorem toQuadraticMap_sum
  given: {ι : Type*} (s : Finset ι) (B : ι -> (BilinMap R M N))
  proof: map_sum (toQuadraticMapAddMonoidHom R M) B s

@[simp]

中文:
定理 toQuadraticMap_sum
  条件: {ι : 类型} (s : Finset ι) (B : ι -> (BilinMap R M N))
  证明: map_sum (toQuadraticMapAddMonoidHom R M) B s

@[simp]

Depends on / 依赖: map_sum, toQuadraticMapAddMonoidHom
-/
theorem toQuadraticMap_sum {ι : Type*} (s : Finset ι) (B : ι -> (BilinMap R M N)) :
    (∑ i in s, B i).toQuadraticMap = ∑ i in s, (B i).toQuadraticMap :=
  map_sum (toQuadraticMapAddMonoidHom R M) B s

@[simp]
/--
theorem `toQuadraticMap_eq_zero` / 定理 `toQuadraticMap_eq_zero`

English:
theorem toQuadraticMap_eq_zero
  given: {B : BilinMap R M N}
  proof: QuadraticMap.ext_iff

中文:
定理 toQuadraticMap_eq_zero
  条件: {B : BilinMap R M N}
  证明: QuadraticMap.ext_iff

Depends on / 依赖: QuadraticMap, QuadraticMap.ext_iff, ext_iff
-/
theorem toQuadraticMap_eq_zero {B : BilinMap R M N} :
    B.toQuadraticMap = 0 ↔ B.IsAlt :=
  QuadraticMap.ext_iff

end Semiring

section Ring

variable [CommRing R] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
variable {B : BilinMap R M N}

@[simp]
/--
theorem `toQuadraticMap_neg` / 定理 `toQuadraticMap_neg`

English:
theorem toQuadraticMap_neg
  given: (B : BilinMap R M N)
  statement: (-B).toQuadraticMap = -B.toQuadraticMap
  proof: rfl

@[simp]

中文:
定理 toQuadraticMap_neg
  条件: (B : BilinMap R M N)
  结论: (-B).toQuadraticMap = -B.toQuadraticMap
  证明: rfl

@[simp]
-/
theorem toQuadraticMap_neg (B : BilinMap R M N) : (-B).toQuadraticMap = -B.toQuadraticMap :=
  rfl

@[simp]
/--
theorem `toQuadraticMap_sub` / 定理 `toQuadraticMap_sub`

English:
theorem toQuadraticMap_sub
  given: (B₁ B₂ : BilinMap R M N)
  proof: rfl

中文:
定理 toQuadraticMap_sub
  条件: (B₁ B₂ : BilinMap R M N)
  证明: rfl
-/
theorem toQuadraticMap_sub (B₁ B₂ : BilinMap R M N) :
    (B₁ - B₂).toQuadraticMap = B₁.toQuadraticMap - B₂.toQuadraticMap :=
  rfl

/--
theorem `polar_toQuadraticMap` / 定理 `polar_toQuadraticMap`

English:
theorem polar_toQuadraticMap
  given: (x y : M)
  statement: polar (toQuadraticMap B) x y = B x y + B y x
  proof: by
  simp only [polar, toQuadraticMap_apply, map_add, add_apply, add_assoc, add_comm (B y x) _,
    add_sub_cancel_left, sub_eq_add_neg _ (B y y), add_neg_cancel_left]

中文:
定理 polar_toQuadraticMap
  条件: (x y : M)
  结论: polar (toQuadraticMap B) x y = B x y + B y x
  证明: by
  simp only [polar, toQuadraticMap_apply, map_add, add_apply, add_assoc, add_comm (B y x) _,
    add_sub_cancel_left, sub_eq_add_neg _ (B y y), add_neg_cancel_left]

Depends on / 依赖: add_apply, add_assoc, add_comm, add_neg_cancel_left, add_sub_cancel_left, map_add, sub_eq_add_neg, toQuadraticMap_apply
-/
theorem polar_toQuadraticMap (x y : M) : polar (toQuadraticMap B) x y = B x y + B y x := by
  simp only [polar, toQuadraticMap_apply, map_add, add_apply, add_assoc, add_comm (B y x) _,
    add_sub_cancel_left, sub_eq_add_neg _ (B y y), add_neg_cancel_left]

/--
theorem `polarBilin_toQuadraticMap` / 定理 `polarBilin_toQuadraticMap`

English:
theorem polarBilin_toQuadraticMap
  statement: polarBilin (toQuadraticMap B) = B + flip B
  proof: LinearMap.ext₂ polar_toQuadraticMap

中文:
定理 polarBilin_toQuadraticMap
  结论: polarBilin (toQuadraticMap B) = B + flip B
  证明: LinearMap.ext₂ polar_toQuadraticMap

Depends on / 依赖: LinearMap, LinearMap.ext, polar_toQuadraticMap
-/
theorem polarBilin_toQuadraticMap : polarBilin (toQuadraticMap B) = B + flip B :=
  LinearMap.ext₂ polar_toQuadraticMap

/--
theorem `_root_.QuadraticMap.toQuadraticMap_polarBilin` / 定理 `_root_.QuadraticMap.toQuadraticMap_polarBilin`

English:
theorem _root_.QuadraticMap.toQuadraticMap_polarBilin
  given: (Q : QuadraticMap R M N)
  proof: QuadraticMap.ext fun x => (polar_self _ x).trans by simp

中文:
定理 _root_.QuadraticMap.toQuadraticMap_polarBilin
  条件: (Q : QuadraticMap R M N)
  证明: QuadraticMap.ext fun x => (polar_self _ x).trans by simp
-/
@[simp] theorem _root_.QuadraticMap.toQuadraticMap_polarBilin (Q : QuadraticMap R M N) :
    toQuadraticMap (polarBilin Q) = 2 • Q :=
QuadraticMap.ext fun x => (polar_self _ x).trans by simp

/--
theorem `_root_.QuadraticMap.polarBilin_injective` / 定理 `_root_.QuadraticMap.polarBilin_injective`

English:
theorem _root_.QuadraticMap.polarBilin_injective
  given: (h : IsUnit (2 : R))
  proof: by
  intro Q₁ Q₂ h₁₂
  apply h.smul_left_cancel.mp
  rw [show (2 : R) = (2 : Nat) by rfl]
  simp_rw [Nat.cast_smul_eq_nsmul R, ← QuadraticMap.toQuadraticMap_polarBilin]
  exact congrArg toQuadraticMap h₁₂

中文:
定理 _root_.QuadraticMap.polarBilin_injective
  条件: (h : IsUnit (2 : R))
  证明: by
  intro Q₁ Q₂ h₁₂
  apply h.smul_left_cancel.mp
  rw [show (2 : R) = (2 : Nat) by rfl]
  simp_rw [Nat.cast_smul_eq_nsmul R, ← QuadraticMap.toQuadraticMap_polarBilin]
  exact congrArg toQuadraticMap h₁₂

Depends on / 依赖: Nat.cast_smul_eq_nsmul, QuadraticMap, QuadraticMap.toQuadraticMap_polarBilin, cast_smul_eq_nsmul, h.smul_left_cancel.mp, simp_rw, smul_left_cancel, toQuadraticMap, toQuadraticMap_polarBilin
-/
theorem _root_.QuadraticMap.polarBilin_injective (h : IsUnit (2 : R)) :
    Function.Injective (polarBilin : QuadraticMap R M N -> _) := by
  intro Q₁ Q₂ h₁₂
  apply h.smul_left_cancel.mp
  rw [show (2 : R) = (2 : Nat) by rfl]
  simp_rw [Nat.cast_smul_eq_nsmul R, ← QuadraticMap.toQuadraticMap_polarBilin]
  exact congrArg toQuadraticMap h₁₂

section

variable {N' : Type*} [AddCommGroup N'] [Module R N']

/--
theorem `_root_.QuadraticMap.polarBilin_comp` / 定理 `_root_.QuadraticMap.polarBilin_comp`

English:
theorem _root_.QuadraticMap.polarBilin_comp
  given: (Q : QuadraticMap R N' N) (f : M ->ₗ[R] N')
  proof: LinearMap.ext₂ fun x y => by simp [polar]

中文:
定理 _root_.QuadraticMap.polarBilin_comp
  条件: (Q : QuadraticMap R N' N) (f : M ->ₗ[R] N')
  证明: LinearMap.ext₂ fun x y => by simp [polar]

Depends on / 依赖: LinearMap, LinearMap.ext
-/
theorem _root_.QuadraticMap.polarBilin_comp (Q : QuadraticMap R N' N) (f : M ->ₗ[R] N') :
    polarBilin (Q.comp f) = LinearMap.compl₁₂ (polarBilin Q) f f :=
LinearMap.ext₂ fun x y => by simp [polar]

end

variable {N' : Type*} [AddCommGroup N']

/--
theorem `_root_.LinearMap.compQuadraticMap_polar` / 定理 `_root_.LinearMap.compQuadraticMap_polar`

English:
theorem _root_.LinearMap.compQuadraticMap_polar
  statement: [CommSemiring S] [Algebra S R] [Module S N]
  proof: by
  simp [polar]

中文:
定理 _root_.LinearMap.compQuadraticMap_polar
  结论: [CommSemiring S] [Algebra S R] [Module S N]
  证明: by
  simp [polar]
-/
theorem _root_.LinearMap.compQuadraticMap_polar [CommSemiring S] [Algebra S R] [Module S N]
    [Module S N'] [IsScalarTower S R N] [Module S M] [IsScalarTower S R M] (f : N ->ₗ[S] N')
    (Q : QuadraticMap R M N) (x y : M) : polar (f.compQuadraticMap' Q) x y = f (polar Q x y) := by
  simp [polar]

variable [Module R N']

/--
theorem `_root_.LinearMap.compQuadraticMap_polarBilin` / 定理 `_root_.LinearMap.compQuadraticMap_polarBilin`

English:
theorem _root_.LinearMap.compQuadraticMap_polarBilin
  given: (f : N ->ₗ[R] N') (Q : QuadraticMap R M N)
  proof: by
  ext
  rw [polarBilin_apply_apply]; rw [compr₂_apply]; rw [polarBilin_apply_apply]; rw [LinearMap.compQuadraticMap_polar]

中文:
定理 _root_.LinearMap.compQuadraticMap_polarBilin
  条件: (f : N ->ₗ[R] N') (Q : QuadraticMap R M N)
  证明: by
  ext
  rw [polarBilin_apply_apply]; rw [compr₂_apply]; rw [polarBilin_apply_apply]; rw [LinearMap.compQuadraticMap_polar]

Depends on / 依赖: LinearMap, LinearMap.compQuadraticMap_polar, compQuadraticMap_polar, polarBilin_apply_apply
-/
theorem _root_.LinearMap.compQuadraticMap_polarBilin (f : N ->ₗ[R] N') (Q : QuadraticMap R M N) :
    (f.compQuadraticMap' Q).polarBilin = Q.polarBilin.compr₂ f := by
  ext
  rw [polarBilin_apply_apply]; rw [compr₂_apply]; rw [polarBilin_apply_apply]; rw [LinearMap.compQuadraticMap_polar]

end Ring

end BilinMap

end LinearMap

namespace QuadraticMap

open LinearMap (BilinMap)

section

variable [Semiring R] [AddCommMonoid M] [Module R M]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Invertible
  signature: (2 : R)] : Invertible (2
  body: (⟨⅟2, Set.invOf_mem_center (Set.ofNat_mem_center _ _)⟩ : Submonoid.center R) •
    (1 : Module.End R M)
  invOf_mul_self := by
    ext m
    dsimp [Submonoid.smul_def]
    rw [← ofNat_smul_eq_nsmul R]; rw [invOf_smul_smul (2 : R) m]
  mul_invOf_self := by
    ext m
    dsimp [Submonoid.smul_def]
   

中文:
实例 [Invertible
  签名: (2 : R)] : Invertible (2
  定义体: (⟨⅟2, Set.invOf_mem_center (Set.ofNat_mem_center _ _)⟩ : Submonoid.center R) •
    (1 : Module.End R M)
  invOf_mul_self := by
    ext m
    dsimp [Submonoid.smul_def]
    rw [← ofNat_smul_eq_nsmul R]; rw [invOf_smul_smul (2 : R) m]
  mul_invOf_self := by
    ext m
    dsimp [Submonoid.smul_def]
   

Depends on / 依赖: Set.invOf_mem_center, Set.ofNat_mem_center, Submonoid, Submonoid.center, center, invOf_mem_center, ofNat_mem_center
-/
instance [Invertible (2 : R)] : Invertible (2 : Module.End R M) where
  invOf := (⟨⅟2, Set.invOf_mem_center (Set.ofNat_mem_center _ _)⟩ : Submonoid.center R) •
    (1 : Module.End R M)
  invOf_mul_self := by
    ext m
    dsimp [Submonoid.smul_def]
    rw [← ofNat_smul_eq_nsmul R]; rw [invOf_smul_smul (2 : R) m]
  mul_invOf_self := by
    ext m
    dsimp [Submonoid.smul_def]
    rw [← ofNat_smul_eq_nsmul R]; rw [smul_invOf_smul (2 : R) m]

/-- If `2` is invertible in `R`, then applying the inverse of `2` in `End R M` to an element
of `M` is the same as multiplying by the inverse of `2` in `R`. -/
@[simp]
/--
lemma `half_moduleEnd_apply_eq_half_smul` / 引理 `half_moduleEnd_apply_eq_half_smul`

English:
lemma half_moduleEnd_apply_eq_half_smul
  given: [Invertible (2 : R)] (x : M)
  proof: rfl

中文:
引理 half_moduleEnd_apply_eq_half_smul
  条件: [Invertible (2 : R)] (x : M)
  证明: rfl
-/
lemma half_moduleEnd_apply_eq_half_smul [Invertible (2 : R)] (x : M) :
    ⅟(2 : Module.End R M) x = ⅟(2 : R) • x :=
  rfl

end

section AssociatedHom

variable [CommRing R] [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]
variable (S) [CommSemiring S] [Algebra S R] [Module S N] [IsScalarTower S R N]

-- the requirement that multiplication by `2` is invertible on the target module `N`
variable [Invertible (2 : Module.End R N)]

/--
Definition of `associatedHom` / `associatedHom` 的定义

English:
definition associatedHom
  signature: : QuadraticMap R M N ->ₗ[S] (BilinMap R M N) where
  body: ⅟(2 : Module.End R N) • polarBilin Q
  map_add' _ _ := LinearMap.ext₂ fun _ _ => by simp [polar_add]
  map_smul' _ _ := LinearMap.ext₂ fun _ _ => by simp [polar_smul]

中文:
定义 associatedHom
  签名: : QuadraticMap R M N ->ₗ[S] (BilinMap R M N) where
  定义体: ⅟(2 : Module.End R N) • polarBilin Q
  map_add' _ _ := LinearMap.ext₂ fun _ _ => by simp [polar_add]
  map_smul' _ _ := LinearMap.ext₂ fun _ _ => by simp [polar_smul]

Depends on / 依赖: Module, Module.End, polarBilin
-/
def associatedHom : QuadraticMap R M N ->ₗ[S] (BilinMap R M N) where
  toFun Q := ⅟(2 : Module.End R N) • polarBilin Q
  map_add' _ _ := LinearMap.ext₂ fun _ _ => by simp [polar_add]
  map_smul' _ _ := LinearMap.ext₂ fun _ _ => by simp [polar_smul]

variable (Q : QuadraticMap R M N)

/--
theorem `associated_apply` / 定理 `associated_apply`

English:
theorem associated_apply
  given: (x y : M)
  proof: rfl

中文:
定理 associated_apply
  条件: (x y : M)
  证明: rfl
-/
theorem associated_apply (x y : M) :
    associatedHom S Q x y = ⅟(2 : Module.End R N) • (Q (x + y) - Q x - Q y) := rfl

set_option backward.defeqAttrib.useBackward true in
/--
theorem `two_nsmul_associated` / 定理 `two_nsmul_associated`

English:
theorem two_nsmul_associated
  statement: 2 • associatedHom S Q = Q.polarBilin
  proof: by
  ext
  dsimp [associated_apply]
  rw [← LinearMap.smul_apply]; rw [nsmul_eq_mul]; rw [Nat.cast_ofNat]; rw [mul_invOf_self']; rw [Module.End.one_apply]; rw [polar]

中文:
定理 two_nsmul_associated
  结论: 2 • associatedHom S Q = Q.polarBilin
  证明: by
  ext
  dsimp [associated_apply]
  rw [← LinearMap.smul_apply]; rw [nsmul_eq_mul]; rw [Nat.cast_ofNat]; rw [mul_invOf_self']; rw [Module.End.one_apply]; rw [polar]
-/
@[simp] theorem two_nsmul_associated : 2 • associatedHom S Q = Q.polarBilin := by
  ext
  dsimp [associated_apply]
  rw [← LinearMap.smul_apply]; rw [nsmul_eq_mul]; rw [Nat.cast_ofNat]; rw [mul_invOf_self']; rw [Module.End.one_apply]; rw [polar]

/--
theorem `associated_isSymm` / 定理 `associated_isSymm`

English:
theorem associated_isSymm
  given: (Q : QuadraticMap R M N) (x y : M)
  proof: by
  simp only [associated_apply, sub_eq_add_neg, add_assoc, add_comm, add_left_comm]

中文:
定理 associated_isSymm
  条件: (Q : QuadraticMap R M N) (x y : M)
  证明: by
  simp only [associated_apply, sub_eq_add_neg, add_assoc, add_comm, add_left_comm]

Depends on / 依赖: add_assoc, add_comm, add_left_comm, associated_apply, sub_eq_add_neg
-/
theorem associated_isSymm (Q : QuadraticMap R M N) (x y : M) :
    associatedHom S Q x y = associatedHom S Q y x := by
  simp only [associated_apply, sub_eq_add_neg, add_assoc, add_comm, add_left_comm]

/--
theorem `_root_.QuadraticForm.associated_isSymm` / 定理 `_root_.QuadraticForm.associated_isSymm`

English:
theorem _root_.QuadraticForm.associated_isSymm
  given: (Q : QuadraticForm R M) [Invertible (2 : R)]
  proof: ⟨QuadraticMap.associated_isSymm S Q⟩

中文:
定理 _root_.QuadraticForm.associated_isSymm
  条件: (Q : QuadraticForm R M) [Invertible (2 : R)]
  证明: ⟨QuadraticMap.associated_isSymm S Q⟩

Depends on / 依赖: QuadraticMap, QuadraticMap.associated_isSymm, associated_isSymm
-/
theorem _root_.QuadraticForm.associated_isSymm (Q : QuadraticForm R M) [Invertible (2 : R)] :
    (associatedHom S Q).IsSymm :=
  ⟨QuadraticMap.associated_isSymm S Q⟩

/--
lemma `associated_flip` / 引理 `associated_flip`

English:
lemma associated_flip
  statement: (associatedHom S Q).flip = associatedHom S Q
  proof: by
  ext
  simp only [LinearMap.flip_apply, associated_apply, add_comm, sub_eq_add_neg, add_left_comm,
    add_assoc]

@[simp]

中文:
引理 associated_flip
  结论: (associatedHom S Q).flip = associatedHom S Q
  证明: by
  ext
  simp only [LinearMap.flip_apply, associated_apply, add_comm, sub_eq_add_neg, add_left_comm,
    add_assoc]

@[simp]

Depends on / 依赖: LinearMap, LinearMap.flip_apply, add_assoc, add_comm, add_left_comm, associated_apply, flip_apply, sub_eq_add_neg
-/
lemma associated_flip : (associatedHom S Q).flip = associatedHom S Q := by
  ext
  simp only [LinearMap.flip_apply, associated_apply, add_comm, sub_eq_add_neg, add_left_comm,
    add_assoc]

@[simp]
/--
theorem `associated_comp` / 定理 `associated_comp`

English:
theorem associated_comp
  given: {N' : Type*} [AddCommGroup N'] [Module R N'] (f : N' ->ₗ[R] M)
  proof: by
  ext
  simp only [associated_apply, comp_apply, map_add, LinearMap.compl₁₂_apply]

中文:
定理 associated_comp
  条件: {N' : 类型} [AddCommGroup N'] [Module R N'] (f : N' ->ₗ[R] M)
  证明: by
  ext
  simp only [associated_apply, comp_apply, map_add, LinearMap.compl₁₂_apply]

Depends on / 依赖: LinearMap, LinearMap.compl, associated_apply, comp_apply, map_add
-/
theorem associated_comp {N' : Type*} [AddCommGroup N'] [Module R N'] (f : N' ->ₗ[R] M) :
    associatedHom S (Q.comp f) = (associatedHom S Q).compl₁₂ f f := by
  ext
  simp only [associated_apply, comp_apply, map_add, LinearMap.compl₁₂_apply]

/--
theorem `associated_toQuadraticMap` / 定理 `associated_toQuadraticMap`

English:
theorem associated_toQuadraticMap
  given: (B : BilinMap R M N) (x y : M)
  proof: by
  simp only [associated_apply, BilinMap.toQuadraticMap_apply, map_add, LinearMap.add_apply,
    Module.End.smul_def, map_sub]
  abel_nf

中文:
定理 associated_toQuadraticMap
  条件: (B : BilinMap R M N) (x y : M)
  证明: by
  simp only [associated_apply, BilinMap.toQuadraticMap_apply, map_add, LinearMap.add_apply,
    Module.End.smul_def, map_sub]
  abel_nf

Depends on / 依赖: BilinMap, BilinMap.toQuadraticMap_apply, LinearMap, LinearMap.add_apply, Module, Module.End.smul_def, abel_nf, add_apply, associated_apply, map_add, map_sub, smul_def, toQuadraticMap_apply
-/
theorem associated_toQuadraticMap (B : BilinMap R M N) (x y : M) :
    associatedHom S B.toQuadraticMap x y = ⅟(2 : Module.End R N) • (B x y + B y x) := by
  simp only [associated_apply, BilinMap.toQuadraticMap_apply, map_add, LinearMap.add_apply,
    Module.End.smul_def, map_sub]
  abel_nf

/--
theorem `associated_left_inverse` / 定理 `associated_left_inverse`

English:
theorem associated_left_inverse
  given: {B₁ : BilinMap R M N} (h : forall x y, B₁ x y = B₁ y x)
  proof: LinearMap.ext₂ fun x y => by
    rw [associated_toQuadraticMap]; rw [← h x y]; rw [← two_smul R]; rw [invOf_smul_eq_iff]; rw [two_smul]; rw [two_smul]

中文:
定理 associated_left_inverse
  条件: {B₁ : BilinMap R M N} (h : 对任意 x y, B₁ x y = B₁ y x)
  证明: LinearMap.ext₂ fun x y => by
    rw [associated_toQuadraticMap]; rw [← h x y]; rw [← two_smul R]; rw [invOf_smul_eq_iff]; rw [two_smul]; rw [two_smul]

Depends on / 依赖: LinearMap, LinearMap.ext, associated_toQuadraticMap, invOf_smul_eq_iff, two_smul
-/
theorem associated_left_inverse {B₁ : BilinMap R M N} (h : forall x y, B₁ x y = B₁ y x) :
    associatedHom S B₁.toQuadraticMap = B₁ :=
  LinearMap.ext₂ fun x y => by
    rw [associated_toQuadraticMap]; rw [← h x y]; rw [← two_smul R]; rw [invOf_smul_eq_iff]; rw [two_smul]; rw [two_smul]

/--
lemma `associated_left_inverse'` / 引理 `associated_left_inverse'`

English:
lemma associated_left_inverse'
  given: {B₁ : BilinMap R M N} (hB₁ : B₁.flip = B₁)
  proof: by
  ext _ y
  rw [associated_toQuadraticMap]; rw [← LinearMap.flip_apply _ y]; rw [hB₁]; rw [invOf_smul_eq_iff]; rw [two_smul]

中文:
引理 associated_left_inverse'
  条件: {B₁ : BilinMap R M N} (hB₁ : B₁.flip = B₁)
  证明: by
  ext _ y
  rw [associated_toQuadraticMap]; rw [← LinearMap.flip_apply _ y]; rw [hB₁]; rw [invOf_smul_eq_iff]; rw [two_smul]

Depends on / 依赖: LinearMap, LinearMap.flip_apply, associated_toQuadraticMap, flip_apply, invOf_smul_eq_iff, two_smul
-/
lemma associated_left_inverse' {B₁ : BilinMap R M N} (hB₁ : B₁.flip = B₁) :
    associatedHom S B₁.toQuadraticMap = B₁ := by
  ext _ y
  rw [associated_toQuadraticMap]; rw [← LinearMap.flip_apply _ y]; rw [hB₁]; rw [invOf_smul_eq_iff]; rw [two_smul]

/--
theorem `associated_eq_self_apply` / 定理 `associated_eq_self_apply`

English:
theorem associated_eq_self_apply
  given: (x : M)
  statement: associatedHom S Q x x = Q x
  proof: by
  rw [associated_apply]; rw [map_add_self]; rw [← three_add_one_eq_four]; rw [← two_add_one_eq_three]; rw [add_smul]; rw [add_smul]; rw [one_smul]; rw [add_sub_cancel_right]; rw [add_sub_cancel_right]; rw [two_smul]; rw [← two_smul R]; rw [invOf_smul_eq_iff]; rw [two_smul]; rw [two_smul]

中文:
定理 associated_eq_self_apply
  条件: (x : M)
  结论: associatedHom S Q x x = Q x
  证明: by
  rw [associated_apply]; rw [map_add_self]; rw [← three_add_one_eq_four]; rw [← two_add_one_eq_three]; rw [add_smul]; rw [add_smul]; rw [one_smul]; rw [add_sub_cancel_right]; rw [add_sub_cancel_right]; rw [two_smul]; rw [← two_smul R]; rw [invOf_smul_eq_iff]; rw [two_smul]; rw [two_smul]

Depends on / 依赖: add_smul, add_sub_cancel_right, associated_apply, invOf_smul_eq_iff, map_add_self, one_smul, three_add_one_eq_four, two_add_one_eq_three, two_smul
-/
theorem associated_eq_self_apply (x : M) : associatedHom S Q x x = Q x := by
  rw [associated_apply]; rw [map_add_self]; rw [← three_add_one_eq_four]; rw [← two_add_one_eq_three]; rw [add_smul]; rw [add_smul]; rw [one_smul]; rw [add_sub_cancel_right]; rw [add_sub_cancel_right]; rw [two_smul]; rw [← two_smul R]; rw [invOf_smul_eq_iff]; rw [two_smul]; rw [two_smul]

/--
theorem `toQuadraticMap_associated` / 定理 `toQuadraticMap_associated`

English:
theorem toQuadraticMap_associated
  statement: (associatedHom S Q).toQuadraticMap = Q
  proof: QuadraticMap.ext associated_eq_self_apply S Q

中文:
定理 toQuadraticMap_associated
  结论: (associatedHom S Q).toQuadraticMap = Q
  证明: QuadraticMap.ext associated_eq_self_apply S Q

Depends on / 依赖: QuadraticMap, QuadraticMap.ext, associated_eq_self_apply
-/
theorem toQuadraticMap_associated : (associatedHom S Q).toQuadraticMap = Q :=
QuadraticMap.ext associated_eq_self_apply S Q

-- note: usually `rightInverse` lemmas are named the other way around, but this is consistent
-- with historical naming in this file.
/--
theorem `associated_rightInverse` / 定理 `associated_rightInverse`

English:
theorem associated_rightInverse
  proof: toQuadraticMap_associated S

中文:
定理 associated_rightInverse
  证明: toQuadraticMap_associated S

Depends on / 依赖: toQuadraticMap_associated
-/
theorem associated_rightInverse :
    Function.RightInverse (associatedHom S) (BilinMap.toQuadraticMap : _ -> QuadraticMap R M N) :=
  toQuadraticMap_associated S

/--
Definition of `associated'` / `associated'` 的定义

English:
abbreviation associated'
  signature: : QuadraticMap R M N ->ₗ[Int] BilinMap R M N
  body: associatedHom Int

中文:
缩写 associated'
  签名: : QuadraticMap R M N ->ₗ[整数] BilinMap R M N
  定义体: associatedHom Int

Depends on / 依赖: associatedHom
-/
abbrev associated' : QuadraticMap R M N ->ₗ[Int] BilinMap R M N :=
  associatedHom Int

/--
Instance `canLift` / 实例 `canLift`

English:
instance canLift
  signature: [Invertible (2 : R)]
  body: fun ⟨hB⟩ => ⟨B.toQuadraticMap, associated_left_inverse _ hB⟩

中文:
实例 canLift
  签名: [Invertible (2 : R)]
  定义体: fun ⟨hB⟩ => ⟨B.toQuadraticMap, associated_left_inverse _ hB⟩

Depends on / 依赖: B.toQuadraticMap, associated_left_inverse, toQuadraticMap
-/
instance canLift [Invertible (2 : R)] :
    CanLift (BilinMap R M R) (QuadraticForm R M) (associatedHom Nat) LinearMap.IsSymm where
  prf B := fun ⟨hB⟩ => ⟨B.toQuadraticMap, associated_left_inverse _ hB⟩

/--
Instance `canLift'` / 实例 `canLift'`

English:
instance canLift'
  signature: :
  body: ⟨B.toQuadraticMap, associated_left_inverse' _ hB⟩

中文:
实例 canLift'
  签名: :
  定义体: ⟨B.toQuadraticMap, associated_left_inverse' _ hB⟩

Depends on / 依赖: B.toQuadraticMap, associated_left_inverse, toQuadraticMap
-/
instance canLift' :
    CanLift (BilinMap R M N) (QuadraticMap R M N) (associatedHom Nat) fun B => B.flip = B where
  prf B hB := ⟨B.toQuadraticMap, associated_left_inverse' _ hB⟩

/--
theorem `exists_quadraticMap_ne_zero` / 定理 `exists_quadraticMap_ne_zero`

English:
theorem exists_quadraticMap_ne_zero
  statement: {Q : QuadraticMap R M N}
  proof: by
  rw [← not_forall]
  intro h
  apply hB₁
  rw [(QuadraticMap.ext h : Q = 0)]; rw [map_zero]

中文:
定理 exists_quadraticMap_ne_zero
  结论: {Q : QuadraticMap R M N}
  证明: by
  rw [← not_forall]
  intro h
  apply hB₁
  rw [(QuadraticMap.ext h : Q = 0)]; rw [map_zero]
-/
theorem exists_quadraticMap_ne_zero {Q : QuadraticMap R M N}
    -- Porting note: added implicit argument
    (hB₁ : associated' (N := N) Q != 0) :
    exists x, Q x != 0 := by
  rw [← not_forall]
  intro h
  apply hB₁
  rw [(QuadraticMap.ext h : Q = 0)]; rw [map_zero]

end AssociatedHom

section Associated

variable [CommSemiring S] [CommRing R] [AddCommGroup M] [Algebra S R] [Module R M]
variable [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower S R N]
variable [Invertible (2 : Module.End R N)]

-- Note: When possible, rather than writing lemmas about `associated`, write a lemma applying to
-- the more general `associatedHom` and place it in the previous section.

/--
Definition of `associated` / `associated` 的定义

English:
abbreviation associated
  signature: : QuadraticMap R M N ->ₗ[R] BilinMap R M N
  body: associatedHom R

中文:
缩写 associated
  签名: : QuadraticMap R M N ->ₗ[R] BilinMap R M N
  定义体: associatedHom R

Depends on / 依赖: associatedHom
-/
abbrev associated : QuadraticMap R M N ->ₗ[R] BilinMap R M N :=
  associatedHom R

variable (S) in
/--
theorem `coe_associatedHom` / 定理 `coe_associatedHom`

English:
theorem coe_associatedHom
  proof: rfl

中文:
定理 coe_associatedHom
  证明: rfl
-/
theorem coe_associatedHom :
    ⇑(associatedHom S : QuadraticMap R M N ->ₗ[S] BilinMap R M N) = associated :=
  rfl

open LinearMap in
@[simp]
/--
theorem `associated_linMulLin` / 定理 `associated_linMulLin`

English:
theorem associated_linMulLin
  given: [Invertible (2 : R)] (f g : M ->ₗ[R] R)
  proof: by
  ext
  simp only [associated_apply, linMulLin_apply, map_add, smul_add, LinearMap.add_apply,
    LinearMap.smul_apply, compl₁₂_apply, mul_apply', smul_eq_mul, invOf_smul_eq_iff]
  simp only [Module.End.smul_def, Module.End.ofNat_apply, nsmul_eq_mul, Nat.cast_ofNat,
    mul_invOf_cancel_left']
  

中文:
定理 associated_linMulLin
  条件: [Invertible (2 : R)] (f g : M ->ₗ[R] R)
  证明: by
  ext
  simp only [associated_apply, linMulLin_apply, map_add, smul_add, LinearMap.add_apply,
    LinearMap.smul_apply, compl₁₂_apply, mul_apply', smul_eq_mul, invOf_smul_eq_iff]
  simp only [Module.End.smul_def, Module.End.ofNat_apply, nsmul_eq_mul, Nat.cast_ofNat,
    mul_invOf_cancel_left']
  

Depends on / 依赖: linMulLin
-/
theorem associated_linMulLin [Invertible (2 : R)] (f g : M ->ₗ[R] R) :
    associated (R := R) (N := R) (linMulLin f g) =
      ⅟(2 : R) • ((mul R R).compl₁₂ f g + (mul R R).compl₁₂ g f) := by
  ext
  simp only [associated_apply, linMulLin_apply, map_add, smul_add, LinearMap.add_apply,
    LinearMap.smul_apply, compl₁₂_apply, mul_apply', smul_eq_mul, invOf_smul_eq_iff]
  simp only [Module.End.smul_def, Module.End.ofNat_apply, nsmul_eq_mul, Nat.cast_ofNat,
    mul_invOf_cancel_left']
  ring_nf

open LinearMap in
@[simp]
/--
lemma `associated_sq` / 引理 `associated_sq`

English:
lemma associated_sq
  given: [Invertible (2 : R)]
  statement: associated (R := R) sq = mul R R
  proof: by
  rw [sq]; rw [associated_linMulLin]
  simp only [smul_add, invOf_two_smul_add_invOf_two_smul]
  rfl

中文:
引理 associated_sq
  条件: [Invertible (2 : R)]
  结论: associated (R := R) sq = mul R R
  证明: by
  rw [sq]; rw [associated_linMulLin]
  simp only [smul_add, invOf_two_smul_add_invOf_two_smul]
  rfl

Depends on / 依赖: associated_linMulLin, invOf_two_smul_add_invOf_two_smul, smul_add
-/
lemma associated_sq [Invertible (2 : R)] : associated (R := R) sq = mul R R := by
  rw [sq]; rw [associated_linMulLin]
  simp only [smul_add, invOf_two_smul_add_invOf_two_smul]
  rfl

end Associated

section IsOrtho

/-! ### Orthogonality -/

section CommSemiring
variable [CommSemiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
  {Q : QuadraticMap R M N}

/--
Definition of `IsOrtho` / `IsOrtho` 的定义

English:
definition IsOrtho
  signature: (Q : QuadraticMap R M N) (x y : M)
  body: Q (x + y) = Q x + Q y

中文:
定义 IsOrtho
  签名: (Q : QuadraticMap R M N) (x y : M)
  定义体: Q (x + y) = Q x + Q y
-/
def IsOrtho (Q : QuadraticMap R M N) (x y : M) : Prop :=
  Q (x + y) = Q x + Q y

/--
theorem `isOrtho_def` / 定理 `isOrtho_def`

English:
theorem isOrtho_def
  given: {Q : QuadraticMap R M N} {x y : M}
  statement: Q.IsOrtho x y ↔ Q (x + y) = Q x + Q y
  proof: Iff.rfl

中文:
定理 isOrtho_def
  条件: {Q : QuadraticMap R M N} {x y : M}
  结论: Q.IsOrtho x y ↔ Q (x + y) = Q x + Q y
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem isOrtho_def {Q : QuadraticMap R M N} {x y : M} : Q.IsOrtho x y ↔ Q (x + y) = Q x + Q y :=
  Iff.rfl

/--
theorem `IsOrtho.all` / 定理 `IsOrtho.all`

English:
theorem IsOrtho.all
  given: (x y : M)
  statement: IsOrtho (0 : QuadraticMap R M N) x y
  proof: (zero_add _).symm

中文:
定理 IsOrtho.all
  条件: (x y : M)
  结论: IsOrtho (0 : QuadraticMap R M N) x y
  证明: (zero_add _).symm

Depends on / 依赖: zero_add
-/
theorem IsOrtho.all (x y : M) : IsOrtho (0 : QuadraticMap R M N) x y := (zero_add _).symm

/--
theorem `IsOrtho.zero_left` / 定理 `IsOrtho.zero_left`

English:
theorem IsOrtho.zero_left
  given: (x : M)
  statement: IsOrtho Q (0 : M) x
  proof: by simp [isOrtho_def]

中文:
定理 IsOrtho.zero_left
  条件: (x : M)
  结论: IsOrtho Q (0 : M) x
  证明: by simp [isOrtho_def]

Depends on / 依赖: isOrtho_def
-/
theorem IsOrtho.zero_left (x : M) : IsOrtho Q (0 : M) x := by simp [isOrtho_def]

/--
theorem `IsOrtho.zero_right` / 定理 `IsOrtho.zero_right`

English:
theorem IsOrtho.zero_right
  given: (x : M)
  statement: IsOrtho Q x (0 : M)
  proof: by simp [isOrtho_def]

中文:
定理 IsOrtho.zero_right
  条件: (x : M)
  结论: IsOrtho Q x (0 : M)
  证明: by simp [isOrtho_def]

Depends on / 依赖: isOrtho_def
-/
theorem IsOrtho.zero_right (x : M) : IsOrtho Q x (0 : M) := by simp [isOrtho_def]

/--
theorem `ne_zero_of_not_isOrtho_self` / 定理 `ne_zero_of_not_isOrtho_self`

English:
theorem ne_zero_of_not_isOrtho_self
  given: {Q : QuadraticMap R M N} (x : M) (hx₁ : ¬Q.IsOrtho x x)
  proof: fun hx₂ => hx₁ (hx₂.symm ▸ .zero_left _)

中文:
定理 ne_zero_of_not_isOrtho_self
  条件: {Q : QuadraticMap R M N} (x : M) (hx₁ : ¬Q.IsOrtho x x)
  证明: fun hx₂ => hx₁ (hx₂.symm ▸ .zero_left _)

Depends on / 依赖: zero_left
-/
theorem ne_zero_of_not_isOrtho_self {Q : QuadraticMap R M N} (x : M) (hx₁ : ¬Q.IsOrtho x x) :
    x != 0 :=
  fun hx₂ => hx₁ (hx₂.symm ▸ .zero_left _)

/--
theorem `isOrtho_comm` / 定理 `isOrtho_comm`

English:
theorem isOrtho_comm
  given: {x y : M}
  statement: IsOrtho Q x y ↔ IsOrtho Q y x
  proof: by simp_rw [isOrtho_def, add_comm]

alias ⟨IsOrtho.symm, _⟩ := isOrtho_comm

中文:
定理 isOrtho_comm
  条件: {x y : M}
  结论: IsOrtho Q x y ↔ IsOrtho Q y x
  证明: by simp_rw [isOrtho_def, add_comm]

alias ⟨IsOrtho.symm, _⟩ := isOrtho_comm

Depends on / 依赖: add_comm, isOrtho_def, simp_rw
-/
theorem isOrtho_comm {x y : M} : IsOrtho Q x y ↔ IsOrtho Q y x := by simp_rw [isOrtho_def, add_comm]

alias ⟨IsOrtho.symm, _⟩ := isOrtho_comm

/--
theorem `_root_.LinearMap.BilinForm.toQuadraticMap_isOrtho` / 定理 `_root_.LinearMap.BilinForm.toQuadraticMap_isOrtho`

English:
theorem _root_.LinearMap.BilinForm.toQuadraticMap_isOrtho
  statement: [IsCancelAdd R]
  proof: by
  let : AddCancelMonoid R := { ‹IsCancelAdd R›, (inferInstance : AddCommMonoid R) with }
  simp_rw [isOrtho_def, B.toQuadraticMap_apply, map_add,
    LinearMap.add_apply, add_comm _ (B y y), add_add_add_comm _ _ (B y y), add_comm (B y y)]
  rw [add_eq_left (a := B x x + B y y)]; rw [← h.eq]; rw [

中文:
定理 _root_.LinearMap.BilinForm.toQuadraticMap_isOrtho
  结论: [IsCancelAdd R]
  证明: by
  let : AddCancelMonoid R := { ‹IsCancelAdd R›, (inferInstance : AddCommMonoid R) with }
  simp_rw [isOrtho_def, B.toQuadraticMap_apply, map_add,
    LinearMap.add_apply, add_comm _ (B y y), add_add_add_comm _ _ (B y y), add_comm (B y y)]
  rw [add_eq_left (a := B x x + B y y)]; rw [← h.eq]; rw [

Depends on / 依赖: AddCancelMonoid, AddCommMonoid, B.toQuadraticMap_apply, IsCancelAdd, LinearMap, LinearMap.add_apply, RingHom, RingHom.id_apply, add_add_add_comm, add_apply, add_comm, add_eq_left, add_self_eq_zero, h.eq, id_apply, isOrtho_def, map_add, simp_rw, toQuadraticMap_apply
-/
theorem _root_.LinearMap.BilinForm.toQuadraticMap_isOrtho [IsCancelAdd R]
    [NoZeroDivisors R] [CharZero R] {B : BilinMap R M R} {x y : M} (h : B.IsSymm) :
    B.toQuadraticMap.IsOrtho x y ↔ B x y = 0 := by
  let : AddCancelMonoid R := { ‹IsCancelAdd R›, (inferInstance : AddCommMonoid R) with }
  simp_rw [isOrtho_def, B.toQuadraticMap_apply, map_add,
    LinearMap.add_apply, add_comm _ (B y y), add_add_add_comm _ _ (B y y), add_comm (B y y)]
  rw [add_eq_left (a := B x x + B y y)]; rw [← h.eq]; rw [RingHom.id_apply]; rw [add_self_eq_zero]

end CommSemiring

section CommRing
variable [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {Q : QuadraticMap R M N}

/--
theorem `isOrtho_polarBilin` / 定理 `isOrtho_polarBilin`

English:
theorem isOrtho_polarBilin
  given: {x y : M}
  statement: Q.polarBilin x y = 0 ↔ IsOrtho Q x y
  proof: by
  simp_rw [isOrtho_def, polarBilin_apply_apply, polar, sub_sub, sub_eq_zero]

中文:
定理 isOrtho_polarBilin
  条件: {x y : M}
  结论: Q.polarBilin x y = 0 ↔ IsOrtho Q x y
  证明: by
  simp_rw [isOrtho_def, polarBilin_apply_apply, polar, sub_sub, sub_eq_zero]

Depends on / 依赖: isOrtho_def, polarBilin_apply_apply, simp_rw, sub_eq_zero, sub_sub
-/
theorem isOrtho_polarBilin {x y : M} : Q.polarBilin x y = 0 ↔ IsOrtho Q x y := by
  simp_rw [isOrtho_def, polarBilin_apply_apply, polar, sub_sub, sub_eq_zero]

/--
theorem `IsOrtho.polar_eq_zero` / 定理 `IsOrtho.polar_eq_zero`

English:
theorem IsOrtho.polar_eq_zero
  given: {x y : M} (h : IsOrtho Q x y)
  statement: polar Q x y = 0
  proof: isOrtho_polarBilin.mpr h

@[simp]

中文:
定理 IsOrtho.polar_eq_zero
  条件: {x y : M} (h : IsOrtho Q x y)
  结论: polar Q x y = 0
  证明: isOrtho_polarBilin.mpr h

@[simp]

Depends on / 依赖: isOrtho_polarBilin, isOrtho_polarBilin.mpr
-/
theorem IsOrtho.polar_eq_zero {x y : M} (h : IsOrtho Q x y) : polar Q x y = 0 :=
  isOrtho_polarBilin.mpr h

@[simp]
/--
theorem `associated_isOrtho` / 定理 `associated_isOrtho`

English:
theorem associated_isOrtho
  given: [Invertible (2 : R)] {x y : M}
  proof: by
  simp_rw [isOrtho_def, associated_apply, invOf_smul_eq_iff, smul_zero, sub_sub, sub_eq_zero]

中文:
定理 associated_isOrtho
  条件: [Invertible (2 : R)] {x y : M}
  证明: by
  simp_rw [isOrtho_def, associated_apply, invOf_smul_eq_iff, smul_zero, sub_sub, sub_eq_zero]

Depends on / 依赖: associated_apply, invOf_smul_eq_iff, isOrtho_def, simp_rw, smul_zero, sub_eq_zero, sub_sub
-/
theorem associated_isOrtho [Invertible (2 : R)] {x y : M} :
    Q.associated x y = 0 ↔ Q.IsOrtho x y := by
  simp_rw [isOrtho_def, associated_apply, invOf_smul_eq_iff, smul_zero, sub_sub, sub_eq_zero]

end CommRing

end IsOrtho

section Anisotropic

section Semiring

variable [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]

/--
Definition of `Anisotropic` / `Anisotropic` 的定义

English:
definition Anisotropic
  signature: (Q : QuadraticMap R M N)
  body: forall x, Q x = 0 -> x = 0

中文:
定义 Anisotropic
  签名: (Q : QuadraticMap R M N)
  定义体: forall x, Q x = 0 -> x = 0
-/
def Anisotropic (Q : QuadraticMap R M N) : Prop :=
  forall x, Q x = 0 -> x = 0

/--
theorem `not_anisotropic_iff_exists` / 定理 `not_anisotropic_iff_exists`

English:
theorem not_anisotropic_iff_exists
  given: (Q : QuadraticMap R M N)
  proof: by
  simp only [Anisotropic, not_forall, exists_prop, and_comm]

中文:
定理 not_anisotropic_iff_exists
  条件: (Q : QuadraticMap R M N)
  证明: by
  simp only [Anisotropic, not_forall, exists_prop, and_comm]

Depends on / 依赖: Anisotropic, and_comm, exists_prop, not_forall
-/
theorem not_anisotropic_iff_exists (Q : QuadraticMap R M N) :
    ¬Anisotropic Q ↔ exists x, x != 0 ∧ Q x = 0 := by
  simp only [Anisotropic, not_forall, exists_prop, and_comm]

/--
theorem `Anisotropic.eq_zero_iff` / 定理 `Anisotropic.eq_zero_iff`

English:
theorem Anisotropic.eq_zero_iff
  given: {Q : QuadraticMap R M N} (h : Anisotropic Q) {x : M}
  proof: ⟨h x, fun h => h.symm ▸ map_zero Q⟩

中文:
定理 Anisotropic.eq_zero_iff
  条件: {Q : QuadraticMap R M N} (h : Anisotropic Q) {x : M}
  证明: ⟨h x, fun h => h.symm ▸ map_zero Q⟩

Depends on / 依赖: h.symm, map_zero
-/
theorem Anisotropic.eq_zero_iff {Q : QuadraticMap R M N} (h : Anisotropic Q) {x : M} :
    Q x = 0 ↔ x = 0 :=
  ⟨h x, fun h => h.symm ▸ map_zero Q⟩

end Semiring

section Ring

variable [CommRing R] [AddCommGroup M] [Module R M]

/--
theorem `separatingLeft_of_anisotropic` / 定理 `separatingLeft_of_anisotropic`

English:
theorem separatingLeft_of_anisotropic
  statement: [Invertible (2 : R)] (Q : QuadraticMap R M R)
  proof: fun x hx => hB _ by
  rw [← hx x]
  exact (associated_eq_self_apply _ _ x).symm

中文:
定理 separatingLeft_of_anisotropic
  结论: [Invertible (2 : R)] (Q : QuadraticMap R M R)
  证明: fun x hx => hB _ by
  rw [← hx x]
  exact (associated_eq_self_apply _ _ x).symm

Depends on / 依赖: SeparatingLeft, associated_eq_self_apply
-/
theorem separatingLeft_of_anisotropic [Invertible (2 : R)] (Q : QuadraticMap R M R)
    (hB : Q.Anisotropic) :
    -- Porting note: added implicit argument
(QuadraticMap.associated' (N := R) Q).SeparatingLeft := fun x hx => hB _ by
  rw [← hx x]
  exact (associated_eq_self_apply _ _ x).symm

end Ring

end Anisotropic

section PosDef

variable {R₂ : Type u} [CommSemiring R₂] [AddCommMonoid M] [Module R₂ M]
variable [PartialOrder N] [AddCommMonoid N] [Module R₂ N]
variable {Q₂ : QuadraticMap R₂ M N}

/--
Definition of `PosDef` / `PosDef` 的定义

English:
definition PosDef
  signature: (Q₂ : QuadraticMap R₂ M N)
  body: forall x, x != 0 -> 0 < Q₂ x

中文:
定义 PosDef
  签名: (Q₂ : QuadraticMap R₂ M N)
  定义体: forall x, x != 0 -> 0 < Q₂ x
-/
def PosDef (Q₂ : QuadraticMap R₂ M N) : Prop :=
  forall x, x != 0 -> 0 < Q₂ x


/--
theorem `PosDef.smul` / 定理 `PosDef.smul`

English:
theorem PosDef.smul
  statement: {R} [CommSemiring R] [PartialOrder R]
  proof: fun x hx => smul_pos a_pos (h x hx)

中文:
定理 PosDef.smul
  结论: {R} [CommSemiring R] [PartialOrder R]
  证明: fun x hx => smul_pos a_pos (h x hx)

Depends on / 依赖: a_pos, smul_pos
-/
theorem PosDef.smul {R} [CommSemiring R] [PartialOrder R]
    [Module R M] [Module R N] [PosSMulStrictMono R N]
    {Q : QuadraticMap R M N} (h : PosDef Q) {a : R} (a_pos : 0 < a) : PosDef (a • Q) :=
  fun x hx => smul_pos a_pos (h x hx)

variable {n : Type*}

/--
theorem `PosDef.nonneg` / 定理 `PosDef.nonneg`

English:
theorem PosDef.nonneg
  given: {Q : QuadraticMap R₂ M N} (hQ : PosDef Q) (x : M)
  statement: 0 <= Q x
  proof: (eq_or_ne x 0).elim (fun h => h.symm ▸ (map_zero Q).symm.le) fun h => (hQ _ h).le

中文:
定理 PosDef.nonneg
  条件: {Q : QuadraticMap R₂ M N} (hQ : PosDef Q) (x : M)
  结论: 0 <= Q x
  证明: (eq_or_ne x 0).elim (fun h => h.symm ▸ (map_zero Q).symm.le) fun h => (hQ _ h).le

Depends on / 依赖: eq_or_ne, h.symm, map_zero, symm.le
-/
theorem PosDef.nonneg {Q : QuadraticMap R₂ M N} (hQ : PosDef Q) (x : M) : 0 <= Q x :=
  (eq_or_ne x 0).elim (fun h => h.symm ▸ (map_zero Q).symm.le) fun h => (hQ _ h).le

/--
theorem `PosDef.anisotropic` / 定理 `PosDef.anisotropic`

English:
theorem PosDef.anisotropic
  given: {Q : QuadraticMap R₂ M N} (hQ : Q.PosDef)
  statement: Q.Anisotropic
  proof: fun x hQx => by_contradiction fun hx =>
lt_irrefl (0 : N) by
      have := hQ _ hx
      rw [hQx] at this
      exact this

中文:
定理 PosDef.anisotropic
  条件: {Q : QuadraticMap R₂ M N} (hQ : Q.PosDef)
  结论: Q.Anisotropic
  证明: fun x hQx => by_contradiction fun hx =>
lt_irrefl (0 : N) by
      have := hQ _ hx
      rw [hQx] at this
      exact this

Depends on / 依赖: by_contradiction, lt_irrefl
-/
theorem PosDef.anisotropic {Q : QuadraticMap R₂ M N} (hQ : Q.PosDef) : Q.Anisotropic :=
  fun x hQx => by_contradiction fun hx =>
lt_irrefl (0 : N) by
      have := hQ _ hx
      rw [hQx] at this
      exact this

/--
theorem `PosDef.le_zero_iff` / 定理 `PosDef.le_zero_iff`

English:
theorem PosDef.le_zero_iff
  given: {Q : QuadraticMap R₂ M N} (hQ : PosDef Q) {x : M}
  proof: by
  refine ⟨fun h => ?_, fun h => by simp [h]⟩
  have : Q x = 0 := le_antisymm h (hQ.nonneg x)
  rwa [← hQ.anisotropic]

中文:
定理 PosDef.le_zero_iff
  条件: {Q : QuadraticMap R₂ M N} (hQ : PosDef Q) {x : M}
  证明: by
  refine ⟨fun h => ?_, fun h => by simp [h]⟩
  have : Q x = 0 := le_antisymm h (hQ.nonneg x)
  rwa [← hQ.anisotropic]

Depends on / 依赖: anisotropic, hQ.anisotropic, hQ.nonneg, le_antisymm, nonneg
-/
theorem PosDef.le_zero_iff {Q : QuadraticMap R₂ M N} (hQ : PosDef Q) {x : M} :
    Q x <= 0 ↔ x = 0 := by
  refine ⟨fun h => ?_, fun h => by simp [h]⟩
  have : Q x = 0 := le_antisymm h (hQ.nonneg x)
  rwa [← hQ.anisotropic]

/--
theorem `posDef_of_nonneg` / 定理 `posDef_of_nonneg`

English:
theorem posDef_of_nonneg
  given: {Q : QuadraticMap R₂ M N} (h : forall x, 0 <= Q x) (h0 : Q.Anisotropic)
  proof: fun x hx => lt_of_le_of_ne (h x) (Ne.symm fun hQx => hx <| h0 _ hQx)

中文:
定理 posDef_of_nonneg
  条件: {Q : QuadraticMap R₂ M N} (h : 对任意 x, 0 <= Q x) (h0 : Q.Anisotropic)
  证明: fun x hx => lt_of_le_of_ne (h x) (Ne.symm fun hQx => hx <| h0 _ hQx)

Depends on / 依赖: Ne.symm, lt_of_le_of_ne
-/
theorem posDef_of_nonneg {Q : QuadraticMap R₂ M N} (h : forall x, 0 <= Q x) (h0 : Q.Anisotropic) :
    PosDef Q :=
  fun x hx => lt_of_le_of_ne (h x) (Ne.symm fun hQx => hx <| h0 _ hQx)

/--
theorem `posDef_iff_nonneg` / 定理 `posDef_iff_nonneg`

English:
theorem posDef_iff_nonneg
  given: {Q : QuadraticMap R₂ M N}
  statement: PosDef Q ↔ (forall x, 0 <= Q x) ∧ Q.Anisotropic
  proof: ⟨fun h => ⟨h.nonneg, h.anisotropic⟩, fun ⟨n, a⟩ => posDef_of_nonneg n a⟩

中文:
定理 posDef_iff_nonneg
  条件: {Q : QuadraticMap R₂ M N}
  结论: PosDef Q ↔ (对任意 x, 0 <= Q x) ∧ Q.Anisotropic
  证明: ⟨fun h => ⟨h.nonneg, h.anisotropic⟩, fun ⟨n, a⟩ => posDef_of_nonneg n a⟩

Depends on / 依赖: anisotropic, h.anisotropic, h.nonneg, nonneg, posDef_of_nonneg
-/
theorem posDef_iff_nonneg {Q : QuadraticMap R₂ M N} : PosDef Q ↔ (forall x, 0 <= Q x) ∧ Q.Anisotropic :=
  ⟨fun h => ⟨h.nonneg, h.anisotropic⟩, fun ⟨n, a⟩ => posDef_of_nonneg n a⟩

/--
theorem `PosDef.add` / 定理 `PosDef.add`

English:
theorem PosDef.add
  statement: [AddLeftStrictMono N]
  proof: fun x hx => add_pos (hQ x hx) (hQ' x hx)

中文:
定理 PosDef.add
  结论: [AddLeftStrictMono N]
  证明: fun x hx => add_pos (hQ x hx) (hQ' x hx)

Depends on / 依赖: add_pos
-/
theorem PosDef.add [AddLeftStrictMono N]
    (Q Q' : QuadraticMap R₂ M N) (hQ : PosDef Q) (hQ' : PosDef Q') :
    PosDef (Q + Q') :=
  fun x hx => add_pos (hQ x hx) (hQ' x hx)

/--
theorem `linMulLinSelfPosDef` / 定理 `linMulLinSelfPosDef`

English:
theorem linMulLinSelfPosDef
  statement: {R} [CommSemiring R] [Module R M]
  proof: fun _x hx => mul_self_pos.2 fun h => hx LinearMap.ker_eq_bot'.mp hf _ h

中文:
定理 linMulLinSelfPosDef
  结论: {R} [CommSemiring R] [Module R M]
  证明: fun _x hx => mul_self_pos.2 fun h => hx LinearMap.ker_eq_bot'.mp hf _ h
-/
theorem linMulLinSelfPosDef {R} [CommSemiring R] [Module R M]
    [Semiring A] [LinearOrder A] [IsStrictOrderedRing A]
    [ExistsAddOfLE A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A] (f : M ->ₗ[R] A)
    (hf : LinearMap.ker f = ⊥) : PosDef (linMulLin (A := A) f f) :=
fun _x hx => mul_self_pos.2 fun h => hx LinearMap.ker_eq_bot'.mp hf _ h

end PosDef

end QuadraticMap

section

/-!
### Quadratic forms and matrices

Connect quadratic forms and matrices, in order to explicitly compute with them.
The convention is twos out, so there might be a factor 2⁻¹ in the entries of the
matrix.
The determinant of the matrix is the discriminant of the quadratic form.
-/

variable {n : Type w} [Fintype n] [DecidableEq n]
variable [CommRing R] [AddCommMonoid M] [Module R M]

/--
Definition of `Matrix.toQuadraticForm'` / `Matrix.toQuadraticForm'` 的定义

English:
definition Matrix.toQuadraticForm'
  signature: (M : Matrix n n R)
  body: LinearMap.BilinMap.toQuadraticMap (Matrix.toLinearMap₂' R M)

@[deprecated (since := "2026-05-15")] alias Matrix.toQuadraticMap' := Matrix.toQuadraticForm'

中文:
定义 Matrix.toQuadraticForm'
  签名: (M : Matrix n n R)
  定义体: LinearMap.BilinMap.toQuadraticMap (Matrix.toLinearMap₂' R M)

@[deprecated (since := "2026-05-15")] alias Matrix.toQuadraticMap' := Matrix.toQuadraticForm'

Depends on / 依赖: BilinMap, LinearMap, LinearMap.BilinMap.toQuadraticMap, Matrix, Matrix.toLinearMap, toQuadraticMap
-/
def Matrix.toQuadraticForm' (M : Matrix n n R) : QuadraticForm R (n -> R) :=
  LinearMap.BilinMap.toQuadraticMap (Matrix.toLinearMap₂' R M)

@[deprecated (since := "2026-05-15")] alias Matrix.toQuadraticMap' := Matrix.toQuadraticForm'

variable [Invertible (2 : R)]

namespace QuadraticForm

section Rn

/--
Definition of `toMatrix'` / `toMatrix'` 的定义

English:
definition toMatrix'
  signature: (Q : QuadraticForm R (n -> R))
  body: LinearMap.toMatrix₂' R Q.associated

中文:
定义 toMatrix'
  签名: (Q : QuadraticForm R (n -> R))
  定义体: LinearMap.toMatrix₂' R Q.associated

Depends on / 依赖: LinearMap, LinearMap.toMatrix, Q.associated, associated
-/
def toMatrix' (Q : QuadraticForm R (n -> R)) : Matrix n n R :=
  LinearMap.toMatrix₂' R Q.associated

/--
theorem `toMatrix'_smul` / 定理 `toMatrix'_smul`

English:
theorem toMatrix'_smul
  given: (a : R) (Q : QuadraticForm R (n -> R))
  proof: by
  simp [toMatrix']

中文:
定理 toMatrix'_smul
  条件: (a : R) (Q : QuadraticForm R (n -> R))
  证明: by
  simp [toMatrix']
-/
theorem toMatrix'_smul (a : R) (Q : QuadraticForm R (n -> R)) :
    (a • Q).toMatrix' = a • Q.toMatrix' := by
  simp [toMatrix']

/--
theorem `isSymm_toMatrix'` / 定理 `isSymm_toMatrix'`

English:
theorem isSymm_toMatrix'
  given: (Q : QuadraticForm R (n -> R))
  statement: Q.toMatrix'.IsSymm
  proof: by
  ext i j
  rw [toMatrix']; rw [Matrix.transpose_apply]; rw [LinearMap.toMatrix₂'_apply]; rw [LinearMap.toMatrix₂'_apply]; rw [← QuadraticMap.associated_isSymm]

中文:
定理 isSymm_toMatrix'
  条件: (Q : QuadraticForm R (n -> R))
  结论: Q.toMatrix'.IsSymm
  证明: by
  ext i j
  rw [toMatrix']; rw [Matrix.transpose_apply]; rw [LinearMap.toMatrix₂'_apply]; rw [LinearMap.toMatrix₂'_apply]; rw [← QuadraticMap.associated_isSymm]

Depends on / 依赖: LinearMap, LinearMap.toMatrix, Matrix, Matrix.transpose_apply, QuadraticMap, QuadraticMap.associated_isSymm, _apply, associated_isSymm, toMatrix, transpose_apply
-/
theorem isSymm_toMatrix' (Q : QuadraticForm R (n -> R)) : Q.toMatrix'.IsSymm := by
  ext i j
  rw [toMatrix']; rw [Matrix.transpose_apply]; rw [LinearMap.toMatrix₂'_apply]; rw [LinearMap.toMatrix₂'_apply]; rw [← QuadraticMap.associated_isSymm]

variable {m : Type w} [DecidableEq m] [Fintype m]

open Matrix

@[simp]
/--
theorem `toMatrix'_comp` / 定理 `toMatrix'_comp`

English:
theorem toMatrix'_comp
  given: (Q : QuadraticForm R (m -> R)) (f : (n -> R) ->ₗ[R] m -> R)
  proof: by
  simp only [QuadraticMap.associated_comp, LinearMap.toMatrix₂'_compl₁₂, toMatrix']

@[deprecated (since := "2026-05-15")] alias QuadraticMap.toMatrix' := QuadraticForm.toMatrix'
@[deprecated (since := "2026-05-15")] alias QuadraticMap.toMatrix'_smul :=
  QuadraticForm.toMatrix'_smul
@[deprecated

中文:
定理 toMatrix'_comp
  条件: (Q : QuadraticForm R (m -> R)) (f : (n -> R) ->ₗ[R] m -> R)
  证明: by
  simp only [QuadraticMap.associated_comp, LinearMap.toMatrix₂'_compl₁₂, toMatrix']

@[deprecated (since := "2026-05-15")] alias QuadraticMap.toMatrix' := QuadraticForm.toMatrix'
@[deprecated (since := "2026-05-15")] alias QuadraticMap.toMatrix'_smul :=
  QuadraticForm.toMatrix'_smul
@[deprecated
-/
theorem toMatrix'_comp (Q : QuadraticForm R (m -> R)) (f : (n -> R) ->ₗ[R] m -> R) :
    QuadraticForm.toMatrix' (Q.comp f) =
      (LinearMap.toMatrix' f)ᵀ * Q.toMatrix' * (LinearMap.toMatrix' f) := by
  simp only [QuadraticMap.associated_comp, LinearMap.toMatrix₂'_compl₁₂, toMatrix']

@[deprecated (since := "2026-05-15")] alias QuadraticMap.toMatrix' := QuadraticForm.toMatrix'
@[deprecated (since := "2026-05-15")] alias QuadraticMap.toMatrix'_smul :=
  QuadraticForm.toMatrix'_smul
@[deprecated (since := "2026-05-15")] alias QuadraticMap.isSymm_toMatrix' :=
  QuadraticForm.isSymm_toMatrix'
@[deprecated (since := "2026-05-15")] alias QuadraticMap.toMatrix'_comp :=
  QuadraticForm.toMatrix'_comp

end Rn
section Basis

open Module

variable [AddCommGroup N] [Module R N] (b : Basis n R N) (Q : QuadraticForm R N)

/--
Definition of `toMatrix` / `toMatrix` 的定义

English:
definition toMatrix
  signature: : Matrix n n R
  body: LinearMap.toMatrix₂ b b (Q.associated)

中文:
定义 toMatrix
  签名: : Matrix n n R
  定义体: LinearMap.toMatrix₂ b b (Q.associated)

Depends on / 依赖: LinearMap, LinearMap.toMatrix, Q.associated, associated
-/
noncomputable def toMatrix : Matrix n n R :=
  LinearMap.toMatrix₂ b b (Q.associated)

/--
lemma `toMatrix_eq_toMatrix'` / 引理 `toMatrix_eq_toMatrix'`

English:
lemma toMatrix_eq_toMatrix'
  given: (Q : QuadraticForm R (n -> R))
  proof: by
  simp only [toMatrix, toMatrix']
  exact LinearEquiv.congr_arg rfl

中文:
引理 toMatrix_eq_toMatrix'
  条件: (Q : QuadraticForm R (n -> R))
  证明: by
  simp only [toMatrix, toMatrix']
  exact LinearEquiv.congr_arg rfl

Depends on / 依赖: LinearEquiv, LinearEquiv.congr_arg, congr_arg, toMatrix
-/
lemma toMatrix_eq_toMatrix' (Q : QuadraticForm R (n -> R)) :
    Q.toMatrix (Pi.basisFun R n) = Q.toMatrix' := by
  simp only [toMatrix, toMatrix']
  exact LinearEquiv.congr_arg rfl

/--
theorem `toMatrix_smul` / 定理 `toMatrix_smul`

English:
theorem toMatrix_smul
  given: (a : R) (Q : QuadraticForm R N)
  proof: by
  simp [toMatrix]

中文:
定理 toMatrix_smul
  条件: (a : R) (Q : QuadraticForm R N)
  证明: by
  simp [toMatrix]

Depends on / 依赖: toMatrix
-/
theorem toMatrix_smul (a : R) (Q : QuadraticForm R N) :
    (a • Q).toMatrix b = a • (Q.toMatrix b) := by
  simp [toMatrix]

/--
theorem `isSymm_toMatrix` / 定理 `isSymm_toMatrix`

English:
theorem isSymm_toMatrix
  given: (Q : QuadraticForm R N)
  statement: (Q.toMatrix b).IsSymm
  proof: by
  ext i j
  rw [toMatrix]; rw [Matrix.transpose_apply]; rw [LinearMap.toMatrix₂_apply]; rw [LinearMap.toMatrix₂_apply]; rw [← QuadraticMap.associated_isSymm]

中文:
定理 isSymm_toMatrix
  条件: (Q : QuadraticForm R N)
  结论: (Q.toMatrix b).IsSymm
  证明: by
  ext i j
  rw [toMatrix]; rw [Matrix.transpose_apply]; rw [LinearMap.toMatrix₂_apply]; rw [LinearMap.toMatrix₂_apply]; rw [← QuadraticMap.associated_isSymm]

Depends on / 依赖: LinearMap, LinearMap.toMatrix, Matrix, Matrix.transpose_apply, QuadraticMap, QuadraticMap.associated_isSymm, associated_isSymm, toMatrix, transpose_apply
-/
theorem isSymm_toMatrix (Q : QuadraticForm R N) : (Q.toMatrix b).IsSymm := by
  ext i j
  rw [toMatrix]; rw [Matrix.transpose_apply]; rw [LinearMap.toMatrix₂_apply]; rw [LinearMap.toMatrix₂_apply]; rw [← QuadraticMap.associated_isSymm]

variable {m : Type w} [DecidableEq m] [Fintype m] [AddCommGroup P] [Module R P]

open Matrix

/--
theorem `toMatrix_comp` / 定理 `toMatrix_comp`

English:
theorem toMatrix_comp
  given: (b' : Basis m R P) (Q : QuadraticForm R P) (f : N ->ₗ[R] P)
  proof: by
  simp only [QuadraticMap.associated_comp, LinearMap.toMatrix₂_compl₁₂ b' b', toMatrix]

中文:
定理 toMatrix_comp
  条件: (b' : Basis m R P) (Q : QuadraticForm R P) (f : N ->ₗ[R] P)
  证明: by
  simp only [QuadraticMap.associated_comp, LinearMap.toMatrix₂_compl₁₂ b' b', toMatrix]

Depends on / 依赖: LinearMap, LinearMap.toMatrix, QuadraticMap, QuadraticMap.associated_comp, associated_comp, toMatrix
-/
theorem toMatrix_comp (b' : Basis m R P) (Q : QuadraticForm R P) (f : N ->ₗ[R] P) :
    QuadraticForm.toMatrix b (Q.comp f) =
      (f.toMatrix b b')ᵀ * (Q.toMatrix b') * (f.toMatrix b b') := by
  simp only [QuadraticMap.associated_comp, LinearMap.toMatrix₂_compl₁₂ b' b', toMatrix]

end Basis

section Discriminant

section Rn

/--
Definition of `discr'` / `discr'` 的定义

English:
definition discr'
  signature: (Q : QuadraticForm R (n -> R))
  body: Q.toMatrix'.det

中文:
定义 discr'
  签名: (Q : QuadraticForm R (n -> R))
  定义体: Q.toMatrix'.det

Depends on / 依赖: Q.toMatrix, toMatrix
-/
def discr' (Q : QuadraticForm R (n -> R)) : R :=
  Q.toMatrix'.det

variable {Q : QuadraticForm R (n -> R)}

/--
theorem `discr'_smul` / 定理 `discr'_smul`

English:
theorem discr'_smul
  given: (a : R)
  statement: (a • Q).discr' = a ^ Fintype.card n * Q.discr'
  proof: by
  simp [discr', toMatrix'_smul]

中文:
定理 discr'_smul
  条件: (a : R)
  结论: (a • Q).discr' = a ^ Fintype.card n * Q.discr'
  证明: by
  simp [discr', toMatrix'_smul]
-/
theorem discr'_smul (a : R) : (a • Q).discr' = a ^ Fintype.card n * Q.discr' := by
  simp [discr', toMatrix'_smul]

/--
theorem `discr'_comp` / 定理 `discr'_comp`

English:
theorem discr'_comp
  given: (f : (n -> R) ->ₗ[R] n -> R)
  proof: by
  simp [mul_left_comm, toMatrix'_comp, mul_comm, discr']

@[deprecated (since := "2026-05-15")] alias QuadraticMap.discr := QuadraticForm.discr'
@[deprecated (since := "2026-05-15")] alias QuadraticMap.discr_smul :=
  QuadraticForm.discr'_smul
@[deprecated (since := "2026-05-15")] alias Quadratic

中文:
定理 discr'_comp
  条件: (f : (n -> R) ->ₗ[R] n -> R)
  证明: by
  simp [mul_left_comm, toMatrix'_comp, mul_comm, discr']

@[deprecated (since := "2026-05-15")] alias QuadraticMap.discr := QuadraticForm.discr'
@[deprecated (since := "2026-05-15")] alias QuadraticMap.discr_smul :=
  QuadraticForm.discr'_smul
@[deprecated (since := "2026-05-15")] alias Quadratic
-/
theorem discr'_comp (f : (n -> R) ->ₗ[R] n -> R) :
    QuadraticForm.discr' (Q.comp f) = f.toMatrix'.det * f.toMatrix'.det * Q.discr' := by
  simp [mul_left_comm, toMatrix'_comp, mul_comm, discr']

@[deprecated (since := "2026-05-15")] alias QuadraticMap.discr := QuadraticForm.discr'
@[deprecated (since := "2026-05-15")] alias QuadraticMap.discr_smul :=
  QuadraticForm.discr'_smul
@[deprecated (since := "2026-05-15")] alias QuadraticMap.discr_comp :=
  QuadraticForm.discr'_comp

end Rn

section Basis

open Module

variable [AddCommGroup N] [Module R N] (b : Basis n R N) (Q : QuadraticForm R N)

/--
Definition of `discr` / `discr` 的定义

English:
definition discr
  signature: : R
  body: (Q.toMatrix b).det

中文:
定义 discr
  签名: : R
  定义体: (Q.toMatrix b).det

Depends on / 依赖: Q.toMatrix, toMatrix
-/
noncomputable def discr : R := (Q.toMatrix b).det

variable {b Q}

/--
theorem `discr_smul` / 定理 `discr_smul`

English:
theorem discr_smul
  given: (a : R)
  statement: (a • Q).discr b = a ^ Fintype.card n * (Q.discr b)
  proof: by
  simp [discr, toMatrix_smul]

中文:
定理 discr_smul
  条件: (a : R)
  结论: (a • Q).discr b = a ^ Fintype.card n * (Q.discr b)
  证明: by
  simp [discr, toMatrix_smul]

Depends on / 依赖: toMatrix_smul
-/
theorem discr_smul (a : R) : (a • Q).discr b = a ^ Fintype.card n * (Q.discr b) := by
  simp [discr, toMatrix_smul]

/--
theorem `discr_comp` / 定理 `discr_comp`

English:
theorem discr_comp
  statement: [AddCommGroup P] [Module R P] (b' : Basis n R P) (Q : QuadraticForm R P)
  proof: by
  simp [mul_left_comm, toMatrix_comp b b', mul_comm, discr]

中文:
定理 discr_comp
  结论: [AddCommGroup P] [Module R P] (b' : Basis n R P) (Q : QuadraticForm R P)
  证明: by
  simp [mul_left_comm, toMatrix_comp b b', mul_comm, discr]

Depends on / 依赖: mul_comm, mul_left_comm, toMatrix_comp
-/
theorem discr_comp [AddCommGroup P] [Module R P] (b' : Basis n R P) (Q : QuadraticForm R P)
    (f : N ->ₗ[R] P) :
    QuadraticForm.discr b (Q.comp f) =
      (f.toMatrix b b').det * (f.toMatrix b b').det * (Q.discr b') := by
  simp [mul_left_comm, toMatrix_comp b b', mul_comm, discr]

/--
lemma `discr_eq_discr'` / 引理 `discr_eq_discr'`

English:
lemma discr_eq_discr'
  given: (Q : QuadraticForm R (n -> R))
  proof: by
  rw [discr]; rw [discr']; rw [toMatrix_eq_toMatrix']

中文:
引理 discr_eq_discr'
  条件: (Q : QuadraticForm R (n -> R))
  证明: by
  rw [discr]; rw [discr']; rw [toMatrix_eq_toMatrix']

Depends on / 依赖: toMatrix_eq_toMatrix
-/
lemma discr_eq_discr' (Q : QuadraticForm R (n -> R)) :
    Q.discr (Pi.basisFun R n) = Q.discr' := by
  rw [discr]; rw [discr']; rw [toMatrix_eq_toMatrix']

end Basis

end Discriminant

end QuadraticForm

end

namespace LinearMap

namespace BilinForm

open LinearMap (BilinMap)

section Semiring

variable [CommSemiring R] [AddCommMonoid M] [Module R M]

/--
theorem `separatingLeft_of_anisotropic` / 定理 `separatingLeft_of_anisotropic`

English:
theorem separatingLeft_of_anisotropic
  given: {B : BilinForm R M} (hB : B.toQuadraticMap.Anisotropic)
  proof: fun x hx => hB _ (hx x)

中文:
定理 separatingLeft_of_anisotropic
  条件: {B : BilinForm R M} (hB : B.toQuadraticMap.Anisotropic)
  证明: fun x hx => hB _ (hx x)
-/
theorem separatingLeft_of_anisotropic {B : BilinForm R M} (hB : B.toQuadraticMap.Anisotropic) :
    B.SeparatingLeft := fun x hx => hB _ (hx x)

end Semiring

variable [CommRing R] [AddCommGroup M] [Module R M]

/--
theorem `exists_bilinForm_self_ne_zero` / 定理 `exists_bilinForm_self_ne_zero`

English:
theorem exists_bilinForm_self_ne_zero
  statement: [htwo : Invertible (2 : R)] {B : BilinForm R M}
  proof: by
  lift B to QuadraticForm R M using hB₂ with Q
  obtain ⟨x, hx⟩ := QuadraticMap.exists_quadraticMap_ne_zero hB₁
  exact ⟨x, fun h => hx (Q.associated_eq_self_apply Nat x ▸ h)⟩

中文:
定理 exists_bilinForm_self_ne_zero
  结论: [htwo : Invertible (2 : R)] {B : BilinForm R M}
  证明: by
  lift B to QuadraticForm R M using hB₂ with Q
  obtain ⟨x, hx⟩ := QuadraticMap.exists_quadraticMap_ne_zero hB₁
  exact ⟨x, fun h => hx (Q.associated_eq_self_apply Nat x ▸ h)⟩

Depends on / 依赖: Q.associated_eq_self_apply, QuadraticForm, QuadraticMap, QuadraticMap.exists_quadraticMap_ne_zero, associated_eq_self_apply, exists_quadraticMap_ne_zero
-/
theorem exists_bilinForm_self_ne_zero [htwo : Invertible (2 : R)] {B : BilinForm R M}
    (hB₁ : B != 0) (hB₂ : B.IsSymm) : exists x, B x x != 0 := by
  lift B to QuadraticForm R M using hB₂ with Q
  obtain ⟨x, hx⟩ := QuadraticMap.exists_quadraticMap_ne_zero hB₁
  exact ⟨x, fun h => hx (Q.associated_eq_self_apply Nat x ▸ h)⟩

open Module

variable {V : Type u} {K : Type v} [Field K] [AddCommGroup V] [Module K V]
variable [FiniteDimensional K V]

/--
theorem `exists_orthogonal_basis` / 定理 `exists_orthogonal_basis`

English:
theorem exists_orthogonal_basis
  statement: [hK : Invertible (2 : K)] {B : LinearMap.BilinForm K V}
  proof: by
  suffices forall d, finrank K V = d -> exists v : Basis (Fin d) K V, B.IsOrthoᵢ v by exact this _ rfl
  intro d hd
  induction d generalizing V with
  | zero => exact ⟨basisOfFinrankZero hd, fun _ _ _ => map_zero _⟩
  | succ d ih =>
  -- either the bilinear form is trivial or we can pick a non-n

中文:
定理 exists_orthogonal_basis
  结论: [hK : Invertible (2 : K)] {B : LinearMap.BilinForm K V}
  证明: by
  suffices forall d, finrank K V = d -> exists v : Basis (Fin d) K V, B.IsOrthoᵢ v by exact this _ rfl
  intro d hd
  induction d generalizing V with
  | zero => exact ⟨basisOfFinrankZero hd, fun _ _ _ => map_zero _⟩
  | succ d ih =>
  -- either the bilinear form is trivial or we can pick a non-n

Depends on / 依赖: B.IsOrtho, basisOfFinrankZero, finrank, generalizing, map_zero
-/
theorem exists_orthogonal_basis [hK : Invertible (2 : K)] {B : LinearMap.BilinForm K V}
    (hB₂ : B.IsSymm) : exists v : Basis (Fin (finrank K V)) K V, B.IsOrthoᵢ v := by
  suffices forall d, finrank K V = d -> exists v : Basis (Fin d) K V, B.IsOrthoᵢ v by exact this _ rfl
  intro d hd
  induction d generalizing V with
  | zero => exact ⟨basisOfFinrankZero hd, fun _ _ _ => map_zero _⟩
  | succ d ih =>
  -- either the bilinear form is trivial or we can pick a non-null `x`
  obtain rfl | hB₁ := eq_or_ne B 0
  · let b := Module.finBasis K V
    rw [hd] at b
    exact ⟨b, fun i j _ => rfl⟩
  obtain ⟨x, hx⟩ := exists_bilinForm_self_ne_zero hB₁ hB₂
  rw [← Submodule.finrank_add_eq_of_isCompl (isCompl_span_singleton_orthogonal hx).symm]; rw [finrank_span_singleton (ne_zero_of_map hx)] at hd
  let B' := B.domRestrict₁₂ ((K ∙ x).orthogonalBilin B) ((K ∙ x).orthogonalBilin B)
  obtain ⟨v', hv₁⟩ := ih (hB₂.domRestrict _ : B'.IsSymm) (Nat.succ.inj hd)
  -- concatenate `x` with the basis obtained by induction
  let b :=
    Basis.mkFinCons x v'
      (by
        rintro c y hy hc
        rw [add_eq_zero_iff_neg_eq] at hc
        rw [← hc]; rw [Submodule.neg_mem_iff] at hy
        have := (isCompl_span_singleton_orthogonal hx).disjoint
        rw [Submodule.disjoint_def] at this
        have := this (c • x) (Submodule.smul_mem _ _ <| Submodule.mem_span_singleton_self _) hy
exact (smul_eq_zero.1 this).resolve_right fun h => hx h.symm ▸ map_zero _)
      (by
        intro y
        refine ⟨-B x y / B x x, fun z hz => ?_⟩
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hz
        rw [map_smul]; rw [smul_apply]; rw [map_add]; rw [map_smul]; rw [smul_eq_mul]; rw [smul_eq_mul]; rw [div_mul_cancel₀ _ hx]; rw [add_neg_cancel]; rw [mul_zero])
  refine ⟨b, ?_⟩
  rw [Basis.coe_mkFinCons]
  intro j i
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;> intro hij <;>
    simp only [Function.onFun, Fin.cons_zero, Fin.cons_succ, Function.comp_apply]
  · exact (hij rfl).elim
  · rw [← hB₂.eq]
    exact (v' j).prop _ (Submodule.mem_span_singleton_self x)
  · exact (v' i).prop _ (Submodule.mem_span_singleton_self x)
  · exact hv₁ (ne_of_apply_ne _ hij)

end BilinForm

end LinearMap

namespace QuadraticMap

open Finset Module

variable [CommSemiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
variable {ι : Type*}

/--
Definition of `basisRepr` / `basisRepr` 的定义

English:
definition basisRepr
  signature: [Finite ι] (Q : QuadraticMap R M N) (v : Basis ι R M)
  body: Q.comp v.equivFun.symm

@[simp]

中文:
定义 basisRepr
  签名: [Finite ι] (Q : QuadraticMap R M N) (v : Basis ι R M)
  定义体: Q.comp v.equivFun.symm

@[simp]

Depends on / 依赖: Q.comp, equivFun, v.equivFun.symm
-/
noncomputable def basisRepr [Finite ι] (Q : QuadraticMap R M N) (v : Basis ι R M) :
    QuadraticMap R (ι -> R) N :=
  Q.comp v.equivFun.symm

@[simp]
/--
theorem `basisRepr_apply` / 定理 `basisRepr_apply`

English:
theorem basisRepr_apply
  given: [Fintype ι] {v : Basis ι R M} (Q : QuadraticMap R M N) (w : ι -> R)
  proof: by
  rw [← v.equivFun_symm_apply]
  rfl

中文:
定理 basisRepr_apply
  条件: [Fintype ι] {v : Basis ι R M} (Q : QuadraticMap R M N) (w : ι -> R)
  证明: by
  rw [← v.equivFun_symm_apply]
  rfl

Depends on / 依赖: equivFun_symm_apply, v.equivFun_symm_apply
-/
theorem basisRepr_apply [Fintype ι] {v : Basis ι R M} (Q : QuadraticMap R M N) (w : ι -> R) :
    Q.basisRepr v w = Q (∑ i : ι, w i • v i) := by
  rw [← v.equivFun_symm_apply]
  rfl

variable [Fintype ι]

section

variable (R)

/--
Definition of `weightedSumSquares` / `weightedSumSquares` 的定义

English:
definition weightedSumSquares
  signature: [Monoid S] [DistribMulAction S R] [SMulCommClass S R R] (w : ι -> S)
  body: ∑ i : ι, w i • (proj (R := R) (n := ι) i i)

中文:
定义 weightedSumSquares
  签名: [Monoid S] [DistribMulAction S R] [SMulCommClass S R R] (w : ι -> S)
  定义体: ∑ i : ι, w i • (proj (R := R) (n := ι) i i)
-/
def weightedSumSquares [Monoid S] [DistribMulAction S R] [SMulCommClass S R R] (w : ι -> S) :
    QuadraticMap R (ι -> R) R :=
  ∑ i : ι, w i • (proj (R := R) (n := ι) i i)

end

@[simp]
/--
theorem `weightedSumSquares_apply` / 定理 `weightedSumSquares_apply`

English:
theorem weightedSumSquares_apply
  statement: [Monoid S] [DistribMulAction S R] [SMulCommClass S R R]
  proof: sum_apply _ _ _

中文:
定理 weightedSumSquares_apply
  结论: [Monoid S] [DistribMulAction S R] [SMulCommClass S R R]
  证明: sum_apply _ _ _

Depends on / 依赖: sum_apply
-/
theorem weightedSumSquares_apply [Monoid S] [DistribMulAction S R] [SMulCommClass S R R]
    (w : ι -> S) (v : ι -> R) :
    weightedSumSquares R w v = ∑ i : ι, w i • (v i * v i) :=
  sum_apply _ _ _

/--
theorem `basisRepr_eq_of_iIsOrtho` / 定理 `basisRepr_eq_of_iIsOrtho`

English:
theorem basisRepr_eq_of_iIsOrtho
  statement: {R M} [CommRing R] [AddCommGroup M] [Module R M]
  proof: by
  ext w
  rw [basisRepr_apply]; rw [← @associated_eq_self_apply R]; rw [map_sum]; rw [weightedSumSquares_apply]
  refine sum_congr rfl fun j hj => ?_
  rw [← @associated_eq_self_apply R]; rw [LinearMap.map_sum₂]; rw [sum_eq_single_of_mem j hj]
  · rw [map_smul, LinearMap.map_smul₂, smul_eq_mul, a

中文:
定理 basisRepr_eq_of_iIsOrtho
  结论: {R M} [CommRing R] [AddCommGroup M] [Module R M]
  证明: by
  ext w
  rw [basisRepr_apply]; rw [← @associated_eq_self_apply R]; rw [map_sum]; rw [weightedSumSquares_apply]
  refine sum_congr rfl fun j hj => ?_
  rw [← @associated_eq_self_apply R]; rw [LinearMap.map_sum₂]; rw [sum_eq_single_of_mem j hj]
  · rw [map_smul, LinearMap.map_smul₂, smul_eq_mul, a
-/
theorem basisRepr_eq_of_iIsOrtho {R M} [CommRing R] [AddCommGroup M] [Module R M]
    [Invertible (2 : R)] (Q : QuadraticForm R M) (v : Basis ι R M)
    (hv₂ : (associated (R := R) Q).IsOrthoᵢ v) :
    Q.basisRepr v = weightedSumSquares _ fun i => Q (v i) := by
  ext w
  rw [basisRepr_apply]; rw [← @associated_eq_self_apply R]; rw [map_sum]; rw [weightedSumSquares_apply]
  refine sum_congr rfl fun j hj => ?_
  rw [← @associated_eq_self_apply R]; rw [LinearMap.map_sum₂]; rw [sum_eq_single_of_mem j hj]
  · rw [map_smul, LinearMap.map_smul₂, smul_eq_mul, associated_apply, smul_eq_mul,
      smul_eq_mul, Module.End.smul_def, half_moduleEnd_apply_eq_half_smul]
    ring_nf
  · intro i _ hij
    rw [map_smul]; rw [LinearMap.map_smul₂]; rw [hv₂ hij]
    module

end QuadraticMap
