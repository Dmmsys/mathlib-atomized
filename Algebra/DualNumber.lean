/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.TrivSqZeroExt.Basic

/-!
# Dual numbers

The dual numbers over `R` are of the form `a + bε`, where `a` and `b` are typically elements of a
commutative ring `R`, and `ε` is a symbol satisfying `ε^2 = 0` that commutes with every other
element. They are a special case of `TrivSqZeroExt R M` with `M = R`.

## Notation

In the `DualNumber` locale:

* `R[ε]` is a shorthand for `DualNumber R`
* `ε` is a shorthand for `DualNumber.eps`

## Main definitions

* `DualNumber`
* `DualNumber.eps`
* `DualNumber.lift`

## Implementation notes

Rather than duplicating the API of `TrivSqZeroExt`, this file reuses the functions there.

## References

* https://en.wikipedia.org/wiki/Dual_number
-/

@[expose] public section


variable {R A B : Type*}

/--
Definition of `DualNumber` / `DualNumber` 的定义

English:
abbreviation DualNumber
  signature: (R : Type*)
  body: TrivSqZeroExt R R

中文:
缩写 DualNumber
  签名: (R : 类型)
  定义体: TrivSqZeroExt R R

Depends on / 依赖: TrivSqZeroExt
-/
abbrev DualNumber (R : Type*) : Type _ :=
  TrivSqZeroExt R R

/--
Definition of `DualNumber.eps` / `DualNumber.eps` 的定义

English:
definition DualNumber.eps
  signature: [Zero R] [One R]
  body: TrivSqZeroExt.inr 1

@[inherit_doc]
scoped[DualNumber] notation "ε" => DualNumber.eps

@[inherit_doc]
scoped[DualNumber] postfix:1024 "[ε]" => DualNumber

中文:
定义 DualNumber.eps
  签名: [零 R] [幺 R]
  定义体: TrivSqZeroExt.inr 1

@[inherit_doc]
scoped[DualNumber] notation "ε" => DualNumber.eps

@[inherit_doc]
scoped[DualNumber] postfix:1024 "[ε]" => DualNumber

Depends on / 依赖: TrivSqZeroExt, TrivSqZeroExt.inr
-/
def DualNumber.eps [Zero R] [One R] : DualNumber R :=
  TrivSqZeroExt.inr 1

@[inherit_doc]
scoped[DualNumber] notation "ε" => DualNumber.eps

@[inherit_doc]
scoped[DualNumber] postfix:1024 "[ε]" => DualNumber

open DualNumber

namespace DualNumber

open TrivSqZeroExt Algebra

@[simp]
/--
theorem `fst_eps` / 定理 `fst_eps`

English:
theorem fst_eps
  given: [Zero R] [One R]
  statement: fst ε = (0 : R)
  proof: rfl

@[simp]

中文:
定理 fst_eps
  条件: [零 R] [幺 R]
  结论: fst ε = (0 : R)
  证明: rfl

@[simp]

Depends on / 依赖: SMulCommClass
-/
theorem fst_eps [Zero R] [One R] : fst ε = (0 : R) :=
  rfl

@[simp]
/--
theorem `snd_eps` / 定理 `snd_eps`

English:
theorem snd_eps
  given: [Zero R] [One R]
  statement: snd ε = (1 : R)
  proof: rfl

中文:
定理 snd_eps
  条件: [零 R] [幺 R]
  结论: snd ε = (1 : R)
  证明: rfl

Depends on / 依赖: IsScalarTower
-/
theorem snd_eps [Zero R] [One R] : snd ε = (1 : R) :=
  rfl

/-- A version of `TrivSqZeroExt.snd_mul` with `*` instead of `•`. -/
@[simp]
/--
theorem `snd_mul` / 定理 `snd_mul`

English:
theorem snd_mul
  given: [Semiring R] (x y : R[ε])
  statement: snd (x * y) = fst x * snd y + snd x * fst y
  proof: rfl

@[simp]

中文:
定理 snd_mul
  条件: [半环 R] (x y : R[ε])
  结论: snd (x * y) = fst x * snd y + snd x * fst y
  证明: rfl

@[simp]
-/
theorem snd_mul [Semiring R] (x y : R[ε]) : snd (x * y) = fst x * snd y + snd x * fst y :=
  rfl

@[simp]
/--
theorem `eps_mul_eps` / 定理 `eps_mul_eps`

English:
theorem eps_mul_eps
  given: [Semiring R]
  statement: (ε * ε : R[ε]) = 0
  proof: inr_mul_inr _ _ _

@[simp]

中文:
定理 eps_mul_eps
  条件: [半环 R]
  结论: (ε * ε : R[ε]) = 0
  证明: inr_mul_inr _ _ _

@[simp]

Depends on / 依赖: inr_mul_inr
-/
theorem eps_mul_eps [Semiring R] : (ε * ε : R[ε]) = 0 :=
  inr_mul_inr _ _ _

@[simp]
/--
lemma `eps_pow_two` / 引理 `eps_pow_two`

English:
lemma eps_pow_two
  given: [Semiring R]
  statement: (ε : R[ε]) ^ 2 = 0
  proof: by
  simp [pow_two]

@[simp]

中文:
引理 eps_pow_two
  条件: [半环 R]
  结论: (ε : R[ε]) ^ 2 = 0
  证明: by
  simp [pow_two]

@[simp]

Depends on / 依赖: pow_two
-/
lemma eps_pow_two [Semiring R] : (ε : R[ε]) ^ 2 = 0 := by
  simp [pow_two]

@[simp]
/--
theorem `inv_eps` / 定理 `inv_eps`

English:
theorem inv_eps
  given: [DivisionRing R]
  statement: (ε : R[ε])⁻¹ = 0
  proof: TrivSqZeroExt.inv_inr 1

@[simp]

中文:
定理 inv_eps
  条件: [除环 R]
  结论: (ε : R[ε])⁻¹ = 0
  证明: TrivSqZeroExt.inv_inr 1

@[simp]

Depends on / 依赖: TrivSqZeroExt, TrivSqZeroExt.inv_inr, inv_inr
-/
theorem inv_eps [DivisionRing R] : (ε : R[ε])⁻¹ = 0 :=
  TrivSqZeroExt.inv_inr 1

@[simp]
/--
theorem `inr_eq_smul_eps` / 定理 `inr_eq_smul_eps`

English:
theorem inr_eq_smul_eps
  given: [MulZeroOneClass R] (r : R)
  statement: inr r = (r • ε : R[ε])
  proof: ext (mul_zero r).symm (mul_one r).symm

中文:
定理 inr_eq_smul_eps
  条件: [乘零幺类 R] (r : R)
  结论: inr r = (r • ε : R[ε])
  证明: ext (mul_zero r).symm (mul_one r).symm

Depends on / 依赖: mul_one, mul_zero
-/
theorem inr_eq_smul_eps [MulZeroOneClass R] (r : R) : inr r = (r • ε : R[ε]) :=
  ext (mul_zero r).symm (mul_one r).symm

/--
theorem `commute_eps_left` / 定理 `commute_eps_left`

English:
theorem commute_eps_left
  given: [Semiring R] (x : DualNumber R)
  statement: Commute ε x
  proof: by
  ext <;> simp

中文:
定理 commute_eps_left
  条件: [半环 R] (x : DualNumber R)
  结论: Commute ε x
  证明: by
  ext <;> simp
-/
theorem commute_eps_left [Semiring R] (x : DualNumber R) : Commute ε x := by
  ext <;> simp

/--
theorem `commute_eps_right` / 定理 `commute_eps_right`

English:
theorem commute_eps_right
  given: [Semiring R] (x : DualNumber R)
  statement: Commute x ε
  proof: (commute_eps_left x).symm

中文:
定理 commute_eps_right
  条件: [半环 R] (x : DualNumber R)
  结论: Commute x ε
  证明: (commute_eps_left x).symm

Depends on / 依赖: commute_eps_left
-/
theorem commute_eps_right [Semiring R] (x : DualNumber R) : Commute x ε := (commute_eps_left x).symm

variable {A : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]

/-- For two `R`-algebra morphisms out of `A[ε]` to agree, it suffices for them to agree on the
elements of `A` and the `A`-multiples of `ε`. -/
@[ext 1100]
nonrec theorem algHom_ext' ⦃f g : A[ε] ->ₐ[R] B⦄
    (hinl : f.comp (inlAlgHom _ _ _) = g.comp (inlAlgHom _ _ _))
    (hinr : f.toLinearMap ∘ₗ (LinearMap.toSpanSingleton A A[ε] ε).restrictScalars R =
        g.toLinearMap ∘ₗ (LinearMap.toSpanSingleton A A[ε] ε).restrictScalars R) :
      f = g :=
  algHom_ext' hinl (by
    ext a
    change f (inr a) = g (inr a)
    simpa only [inr_eq_smul_eps] using! DFunLike.congr_fun hinr a)

set_option backward.defeqAttrib.useBackward true in
/-- For two `R`-algebra morphisms out of `R[ε]` to agree, it suffices for them to agree on `ε`. -/
@[ext 1200]
/--
theorem `algHom_ext` / 定理 `algHom_ext`

English:
theorem algHom_ext
  given: ⦃f g
  statement: R[ε] ->ₐ[R] A⦄ (hε : f ε = g ε) : f = g
  proof: by
  ext
  dsimp
  simp only [one_smul, hε]

中文:
定理 algHom_ext
  条件: ⦃f g
  结论: R[ε] ->ₐ[R] A⦄ (hε : f ε = g ε) : f = g
  证明: by
  ext
  dsimp
  simp only [one_smul, hε]

Depends on / 依赖: one_smul
-/
theorem algHom_ext ⦃f g : R[ε] ->ₐ[R] A⦄ (hε : f ε = g ε) : f = g := by
  ext
  dsimp
  simp only [one_smul, hε]

/-- A ring morphism `R[ε] →+* R'` is determined by its restriction
on `R` and its value on `ε`. -/
@[ext high]
/--
lemma `ringHom_ext` / 引理 `ringHom_ext`

English:
lemma ringHom_ext
  statement: {R' : Type*} [CommSemiring R'] {f g : R[ε] ->+* R'}
  proof: by
  let : Algebra R R' := by
    letI := f.toAlgebra
    exact Algebra.compHom _ (algebraMap R R[ε])
  let f' : R[ε] ->ₐ[R] R' :=
    { toRingHom := f
      commutes' _ := rfl }
  let g' : R[ε] ->ₐ[R] R' :=
    { toRingHom := g
      commutes' r := (DFunLike.congr_fun h₀ r).symm }
  exact congr_arg

中文:
引理 ringHom_ext
  结论: {R' : 类型} [交换半环 R'] {f g : R[ε] ->+* R'}
  证明: by
  let : Algebra R R' := by
    letI := f.toAlgebra
    exact Algebra.compHom _ (algebraMap R R[ε])
  let f' : R[ε] ->ₐ[R] R' :=
    { toRingHom := f
      commutes' _ := rfl }
  let g' : R[ε] ->ₐ[R] R' :=
    { toRingHom := g
      commutes' r := (DFunLike.congr_fun h₀ r).symm }
  exact congr_arg

Depends on / 依赖: AlgHom, AlgHom.toRingHom, Algebra, Algebra.compHom, DFunLike, DFunLike.congr_fun, algHom_ext, algebraMap, commutes, compHom, congr_arg, congr_fun, f.toAlgebra, toAlgebra, toRingHom
-/
lemma ringHom_ext {R' : Type*} [CommSemiring R'] {f g : R[ε] ->+* R'}
    (h₀ : f.comp (algebraMap R R[ε]) = g.comp (algebraMap R R[ε]))
    (hε : f ε = g ε) : f = g := by
  let : Algebra R R' := by
    letI := f.toAlgebra
    exact Algebra.compHom _ (algebraMap R R[ε])
  let f' : R[ε] ->ₐ[R] R' :=
    { toRingHom := f
      commutes' _ := rfl }
  let g' : R[ε] ->ₐ[R] R' :=
    { toRingHom := g
      commutes' r := (DFunLike.congr_fun h₀ r).symm }
  exact congr_arg AlgHom.toRingHom (show f' = g' from algHom_ext hε)

/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: :
  body: by
  refine Equiv.trans ?_ TrivSqZeroExt.liftEquiv
  exact {
    toFun := fun fe => ⟨
      (fe.val.1, MulOpposite.op fe.val.2 • fe.val.1.toLinearMap),
      fun x y => show (fe.val.1 x * fe.val.2) * (fe.val.1 y * fe.val.2) = 0 by
        rw [(fe.prop.2 _).mul_mul_mul_comm]; rw [fe.prop.1]; rw [mul_

中文:
定义 lift
  签名: :
  定义体: by
  refine Equiv.trans ?_ TrivSqZeroExt.liftEquiv
  exact {
    toFun := fun fe => ⟨
      (fe.val.1, MulOpposite.op fe.val.2 • fe.val.1.toLinearMap),
      fun x y => show (fe.val.1 x * fe.val.2) * (fe.val.1 y * fe.val.2) = 0 by
        rw [(fe.prop.2 _).mul_mul_mul_comm]; rw [fe.prop.1]; rw [mul_

Depends on / 依赖: Equiv.trans, MulOpposite, MulOpposite.op, TrivSqZeroExt, TrivSqZeroExt.liftEquiv, fe.prop, fe.val, liftEquiv, map_mul, mul_assoc, mul_mul_mul_comm, mul_zero, toLinearMap
-/
def lift :
    {fe : (A ->ₐ[R] B) × B // fe.2 * fe.2 = 0 ∧ forall a, Commute fe.2 (fe.1 a)} ≃ (A[ε] ->ₐ[R] B) := by
  refine Equiv.trans ?_ TrivSqZeroExt.liftEquiv
  exact {
    toFun := fun fe => ⟨
      (fe.val.1, MulOpposite.op fe.val.2 • fe.val.1.toLinearMap),
      fun x y => show (fe.val.1 x * fe.val.2) * (fe.val.1 y * fe.val.2) = 0 by
        rw [(fe.prop.2 _).mul_mul_mul_comm]; rw [fe.prop.1]; rw [mul_zero],
      fun r x => show fe.val.1 (r * x) * fe.val.2 = fe.val.1 r * (fe.val.1 x * fe.val.2) by
        rw [map_mul]; rw [mul_assoc],
      fun r x => show fe.val.1 (x * r) * fe.val.2 = (fe.val.1 x * fe.val.2) * fe.val.1 r by
        rw [map_mul]; rw [(fe.prop.2 _).right_comm]⟩
    invFun := fun fg => ⟨
      (fg.val.1, fg.val.2 1),
      fg.prop.1 _ _,
      fun a => show fg.val.2 1 * fg.val.1 a = fg.val.1 a * fg.val.2 1 by
        rw [← fg.prop.2.1]; rw [← fg.prop.2.2]; rw [smul_eq_mul]; rw [op_smul_eq_mul]; rw [mul_one]; rw [one_mul]⟩
left_inv := fun fe => Subtype.ext Prod.ext rfl
      show fe.val.1 1 * fe.val.2 = fe.val.2 by
        rw [map_one]; rw [one_mul]
right_inv := fun fg => Subtype.ext Prod.ext rfl LinearMap.ext fun x =>
      show fg.val.1 x * fg.val.2 1 = fg.val.2 x by
        rw [← fg.prop.2.1]; rw [smul_eq_mul]; rw [mul_one] }

/--
theorem `lift_apply_apply` / 定理 `lift_apply_apply`

English:
theorem lift_apply_apply
  given: (fe : {_fe : (A ->ₐ[R] B) × B // _}) (a : A[ε])
  proof: rfl

中文:
定理 lift_apply_apply
  条件: (fe : {_fe : (A ->ₐ[R] B) × B // _}) (a : A[ε])
  证明: rfl
-/
theorem lift_apply_apply (fe : {_fe : (A ->ₐ[R] B) × B // _}) (a : A[ε]) :
    lift fe a = fe.val.1 a.fst + fe.val.1 a.snd * fe.val.2 := rfl

/--
theorem `coe_lift_symm_apply` / 定理 `coe_lift_symm_apply`

English:
theorem coe_lift_symm_apply
  given: (F : A[ε] ->ₐ[R] B)
  proof: rfl

中文:
定理 coe_lift_symm_apply
  条件: (F : A[ε] ->ₐ[R] B)
  证明: rfl
-/
@[simp] theorem coe_lift_symm_apply (F : A[ε] ->ₐ[R] B) :
    (lift.symm F).val = (F.comp (inlAlgHom _ _ _), F ε) := rfl

/--
theorem `lift_apply_inl` / 定理 `lift_apply_inl`

English:
theorem lift_apply_inl
  given: (fe : {_fe : (A ->ₐ[R] B) × B // _}) (a : A)
  proof: by
  rw [lift_apply_apply]; rw [fst_inl]; rw [snd_inl]; rw [map_zero]; rw [zero_mul]; rw [add_zero]

中文:
定理 lift_apply_inl
  条件: (fe : {_fe : (A ->ₐ[R] B) × B // _}) (a : A)
  证明: by
  rw [lift_apply_apply]; rw [fst_inl]; rw [snd_inl]; rw [map_zero]; rw [zero_mul]; rw [add_zero]
-/
@[simp] theorem lift_apply_inl (fe : {_fe : (A ->ₐ[R] B) × B // _}) (a : A) :
    lift fe (inl a : A[ε]) = fe.val.1 a := by
  rw [lift_apply_apply]; rw [fst_inl]; rw [snd_inl]; rw [map_zero]; rw [zero_mul]; rw [add_zero]

/--
theorem `lift_comp_inlHom` / 定理 `lift_comp_inlHom`

English:
theorem lift_comp_inlHom
  given: (fe : {_fe : (A ->ₐ[R] B) × B // _})
  proof: AlgHom.ext lift_apply_inl fe

中文:
定理 lift_comp_inlHom
  条件: (fe : {_fe : (A ->ₐ[R] B) × B // _})
  证明: AlgHom.ext lift_apply_inl fe
-/
@[simp] theorem lift_comp_inlHom (fe : {_fe : (A ->ₐ[R] B) × B // _}) :
    (lift fe).comp (inlAlgHom R A A) = fe.val.1 :=
AlgHom.ext lift_apply_inl fe

/--
theorem `lift_smul` / 定理 `lift_smul`

English:
theorem lift_smul
  given: (fe : {_fe : (A ->ₐ[R] B) × B // _}) (a : A) (ad : A[ε])
  proof: by
  rw [← inl_mul_eq_smul]; rw [map_mul]; rw [lift_apply_inl]

中文:
定理 lift_smul
  条件: (fe : {_fe : (A ->ₐ[R] B) × B // _}) (a : A) (ad : A[ε])
  证明: by
  rw [← inl_mul_eq_smul]; rw [map_mul]; rw [lift_apply_inl]
-/
@[simp] theorem lift_smul (fe : {_fe : (A ->ₐ[R] B) × B // _}) (a : A) (ad : A[ε]) :
    lift fe (a • ad) = fe.val.1 a * lift fe ad := by
  rw [← inl_mul_eq_smul]; rw [map_mul]; rw [lift_apply_inl]

/--
theorem `lift_op_smul` / 定理 `lift_op_smul`

English:
theorem lift_op_smul
  given: (fe : {_fe : (A ->ₐ[R] B) × B // _}) (a : A) (ad : A[ε])
  proof: by
  rw [← mul_inl_eq_op_smul]; rw [map_mul]; rw [lift_apply_inl]

中文:
定理 lift_op_smul
  条件: (fe : {_fe : (A ->ₐ[R] B) × B // _}) (a : A) (ad : A[ε])
  证明: by
  rw [← mul_inl_eq_op_smul]; rw [map_mul]; rw [lift_apply_inl]
-/
@[simp] theorem lift_op_smul (fe : {_fe : (A ->ₐ[R] B) × B // _}) (a : A) (ad : A[ε]) :
    lift fe (MulOpposite.op a • ad) = lift fe ad * fe.val.1 a := by
  rw [← mul_inl_eq_op_smul]; rw [map_mul]; rw [lift_apply_inl]

/--
theorem `lift_apply_eps` / 定理 `lift_apply_eps`

English:
theorem lift_apply_eps
  proof: by
  simp only [lift_apply_apply, fst_eps, map_zero, snd_eps, map_one, one_mul, zero_add]

中文:
定理 lift_apply_eps
  证明: by
  simp only [lift_apply_apply, fst_eps, map_zero, snd_eps, map_one, one_mul, zero_add]
-/
@[simp] theorem lift_apply_eps
    (fe : {fe : (A ->ₐ[R] B) × B // fe.2 * fe.2 = 0 ∧ forall a, Commute fe.2 (fe.1 a)}) :
    lift fe (ε : A[ε]) = fe.val.2 := by
  simp only [lift_apply_apply, fst_eps, map_zero, snd_eps, map_one, one_mul, zero_add]

/-- Lifting `DualNumber.eps` itself gives the identity. -/
@[simp]
/--
theorem `lift_inlAlgHom_eps` / 定理 `lift_inlAlgHom_eps`

English:
theorem lift_inlAlgHom_eps
  proof: lift.apply_symm_apply AlgHom.id R A[ε]

@[simp]

中文:
定理 lift_inlAlgHom_eps
  证明: lift.apply_symm_apply AlgHom.id R A[ε]

@[simp]

Depends on / 依赖: AlgHom, AlgHom.id, apply_symm_apply, lift.apply_symm_apply
-/
theorem lift_inlAlgHom_eps :
    lift ⟨(inlAlgHom _ _ _, ε), eps_mul_eps, fun _ => commute_eps_left _⟩ = AlgHom.id R A[ε] :=
lift.apply_symm_apply AlgHom.id R A[ε]

@[simp]
/--
theorem `range_inlAlgHom_sup_adjoin_eps` / 定理 `range_inlAlgHom_sup_adjoin_eps`

English:
theorem range_inlAlgHom_sup_adjoin_eps
  proof: by
  refine top_unique fun x hx => ?_; clear hx
  rw [← x.inl_fst_add_inr_snd_eq]; rw [inr_eq_smul_eps]; rw [← inl_mul_eq_smul]
  refine add_mem ?_ (mul_mem ?_ ?_)
· exact le_sup_left (α := Subalgebra R _) Set.mem_range_self x.fst
· exact le_sup_left (α := Subalgebra R _) Set.mem_range_self x.snd
· 

中文:
定理 range_inlAlgHom_sup_adjoin_eps
  证明: by
  refine top_unique fun x hx => ?_; clear hx
  rw [← x.inl_fst_add_inr_snd_eq]; rw [inr_eq_smul_eps]; rw [← inl_mul_eq_smul]
  refine add_mem ?_ (mul_mem ?_ ?_)
· exact le_sup_left (α := Subalgebra R _) Set.mem_range_self x.fst
· exact le_sup_left (α := Subalgebra R _) Set.mem_range_self x.snd
· 

Depends on / 依赖: Set.mem_range_self, Set.mem_singleton, Subalgebra, add_mem, inl_fst_add_inr_snd_eq, inl_mul_eq_smul, inr_eq_smul_eps, le_sup_left, le_sup_right, mem_range_self, mem_singleton, mul_mem, subset_adjoin, top_unique, x.fst, x.inl_fst_add_inr_snd_eq, x.snd
-/
theorem range_inlAlgHom_sup_adjoin_eps :
    (inlAlgHom R A A).range ⊔ Algebra.adjoin R {ε} = ⊤ := by
  refine top_unique fun x hx => ?_; clear hx
  rw [← x.inl_fst_add_inr_snd_eq]; rw [inr_eq_smul_eps]; rw [← inl_mul_eq_smul]
  refine add_mem ?_ (mul_mem ?_ ?_)
· exact le_sup_left (α := Subalgebra R _) Set.mem_range_self x.fst
· exact le_sup_left (α := Subalgebra R _) Set.mem_range_self x.snd
· refine le_sup_right (α := Subalgebra R _) subset_adjoin Set.mem_singleton ε

@[simp]
/--
theorem `range_lift` / 定理 `range_lift`

English:
theorem range_lift
  proof: by
  simp_rw [← Algebra.map_top, ← range_inlAlgHom_sup_adjoin_eps, Algebra.map_sup,
    AlgHom.map_adjoin, ← AlgHom.range_comp, Set.image_singleton, lift_apply_eps, lift_comp_inlHom,
    Algebra.map_top]

中文:
定理 range_lift
  证明: by
  simp_rw [← Algebra.map_top, ← range_inlAlgHom_sup_adjoin_eps, Algebra.map_sup,
    AlgHom.map_adjoin, ← AlgHom.range_comp, Set.image_singleton, lift_apply_eps, lift_comp_inlHom,
    Algebra.map_top]

Depends on / 依赖: AlgHom, AlgHom.map_adjoin, AlgHom.range_comp, Algebra, Algebra.map_sup, Algebra.map_top, Set.image_singleton, image_singleton, lift_apply_eps, lift_comp_inlHom, map_adjoin, map_sup, map_top, range_comp, range_inlAlgHom_sup_adjoin_eps, simp_rw
-/
theorem range_lift
    (fe : {fe : (A ->ₐ[R] B) × B // fe.2 * fe.2 = 0 ∧ forall a, Commute fe.2 (fe.1 a)}) :
    (lift fe).range = fe.1.1.range ⊔ R[fe.1.2] := by
  simp_rw [← Algebra.map_top, ← range_inlAlgHom_sup_adjoin_eps, Algebra.map_sup,
    AlgHom.map_adjoin, ← AlgHom.range_comp, Set.image_singleton, lift_apply_eps, lift_comp_inlHom,
    Algebra.map_top]

/--
Instance `instRepr` / 实例 `instRepr`

English:
instance instRepr
  signature: [Repr R]
  body: (if p > 65 then (Std.Format.bracket "(" · ")") else (·))
      reprPrec f.fst 65 ++ " + " ++ reprPrec f.snd 70 ++ "*ε"

中文:
实例 instRepr
  签名: [Repr R]
  定义体: (if p > 65 then (Std.Format.bracket "(" · ")") else (·))
      reprPrec f.fst 65 ++ " + " ++ reprPrec f.snd 70 ++ "*ε"

Depends on / 依赖: Format, Std.Format.bracket, bracket, f.fst, f.snd, reprPrec
-/
instance instRepr [Repr R] : Repr (DualNumber R) where
  reprPrec f p :=
(if p > 65 then (Std.Format.bracket "(" · ")") else (·))
      reprPrec f.fst 65 ++ " + " ++ reprPrec f.snd 70 ++ "*ε"

end DualNumber
