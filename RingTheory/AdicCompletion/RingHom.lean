/-
Copyright (c) 2025 Jiedong Jiang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang
-/
module

public import Mathlib.RingTheory.AdicCompletion.Algebra

/-!
# Lift of ring homomorphisms to adic completions

Let `R`, `S` be rings, `I` be an ideal of `S`.
In this file we prove that a compatible family of ring homomorphisms from a ring `R` to
`S ⧸ I ^ n` can be lifted to a ring homomorphism `R →+* AdicCompletion I S`.
If `S` is `I`-adically complete, then this compatible family of ring homomorphisms can be
lifted to a ring homomorphism `R →+* S`.

## Main definitions

- `IsAdicComplete.liftRingHom`: if `R` is
  `I`-adically complete, then a compatible family of
  ring maps `S →+* R ⧸ I ^ n` can be lifted to a unique ring map `S →+* R`.
  Together with `mk_liftRingHom_apply` and `eq_liftRingHom`, it gives the universal property
  of `R` being `I`-adically complete.
-/

@[expose] public section

open Ideal Quotient

variable {R S : Type*} [NonAssocSemiring R] [CommRing S] (I : Ideal S)

namespace IsAdicComplete

open AdicCompletion

section

variable [IsAdicComplete I S] (f : (n : Nat) -> R ->+* S ⧸ I ^ n)
    (hf : forall {m n : Nat} (hle : m <= n), (factorPow I hle).comp (f n) = f m)

/--
Definition of `liftRingHom` / `liftRingHom` 的定义

English:
definition liftRingHom
  signature: :
  body: ((ofAlgEquiv I).symm : _ ->+* _).comp (AdicCompletion.liftRingHom I f hf)

@[simp]

中文:
定义 liftRingHom
  签名: :
  定义体: ((ofAlgEquiv I).symm : _ ->+* _).comp (AdicCompletion.liftRingHom I f hf)

@[simp]

Depends on / 依赖: AdicCompletion, AdicCompletion.liftRingHom, liftRingHom, ofAlgEquiv
-/
noncomputable def liftRingHom :
    R ->+* S :=
  ((ofAlgEquiv I).symm : _ ->+* _).comp (AdicCompletion.liftRingHom I f hf)

@[simp]
/--
theorem `of_liftRingHom` / 定理 `of_liftRingHom`

English:
theorem of_liftRingHom
  given: (x : R)
  proof: by
  simp [liftRingHom]

@[simp]

中文:
定理 of_liftRingHom
  条件: (x : R)
  证明: by
  simp [liftRingHom]

@[simp]

Depends on / 依赖: liftRingHom
-/
theorem of_liftRingHom (x : R) :
    of I S (liftRingHom I f hf x) = (AdicCompletion.liftRingHom I f hf x) := by
  simp [liftRingHom]

@[simp]
/--
theorem `ofAlgEquiv_comp_liftRingHom` / 定理 `ofAlgEquiv_comp_liftRingHom`

English:
theorem ofAlgEquiv_comp_liftRingHom
  proof: by
  ext; simp

中文:
定理 ofAlgEquiv_comp_liftRingHom
  证明: by
  ext; simp
-/
theorem ofAlgEquiv_comp_liftRingHom :
    (ofAlgEquiv I : S ->+* AdicCompletion I S).comp (liftRingHom I f hf) =
      AdicCompletion.liftRingHom I f hf := by
  ext; simp

/--
The composition of lift linear map `lift I f hf : R →+* S` with the canonical
projection `S →+* S ⧸ (I ^ n)` is `f n` .
-/
@[simp]
/--
theorem `mk_liftRingHom` / 定理 `mk_liftRingHom`

English:
theorem mk_liftRingHom
  given: (n : Nat) (x : R)
  proof: by
  simp only [liftRingHom, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply]
  rw [← evalₐ_of I n]
  simp

@[simp]

中文:
定理 mk_liftRingHom
  条件: (n : 自然数) (x : R)
  证明: by
  simp only [liftRingHom, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply]
  rw [← evalₐ_of I n]
  simp

@[simp]

Depends on / 依赖: Function, Function.comp_apply, RingHom, RingHom.coe_coe, RingHom.coe_comp, coe_coe, coe_comp, comp_apply, liftRingHom
-/
theorem mk_liftRingHom (n : Nat) (x : R) :
    Ideal.Quotient.mk (I ^ n) (liftRingHom I f hf x) = f n x := by
  simp only [liftRingHom, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply]
  rw [← evalₐ_of I n]
  simp

@[simp]
/--
theorem `mk_comp_liftRingHom` / 定理 `mk_comp_liftRingHom`

English:
theorem mk_comp_liftRingHom
  given: (n : Nat)
  proof: by
  ext; simp

中文:
定理 mk_comp_liftRingHom
  条件: (n : 自然数)
  证明: by
  ext; simp
-/
theorem mk_comp_liftRingHom (n : Nat) :
    (Ideal.Quotient.mk (I ^ n)).comp (liftRingHom I f hf) = f n := by
  ext; simp

/--
theorem `eq_liftRingHom` / 定理 `eq_liftRingHom`

English:
theorem eq_liftRingHom
  statement: (F : R ->+* S)
  proof: by
  apply DFunLike.coe_injective
  apply IsHausdorff.funext' I
  intro n m
  simp [← hF n]

中文:
定理 eq_liftRingHom
  结论: (F : R ->+* S)
  证明: by
  apply DFunLike.coe_injective
  apply IsHausdorff.funext' I
  intro n m
  simp [← hF n]

Depends on / 依赖: DFunLike, DFunLike.coe_injective, IsHausdorff, IsHausdorff.funext, coe_injective
-/
theorem eq_liftRingHom (F : R ->+* S)
    (hF : forall n, (Ideal.Quotient.mk (I ^ n)).comp F = f n) :
    F = liftRingHom I f hf := by
  apply DFunLike.coe_injective
  apply IsHausdorff.funext' I
  intro n m
  simp [← hF n]

section

variable {R S A : Type*} [CommRing R] [CommRing S] [Algebra R S] (I : Ideal S)
  [IsAdicComplete I S] [CommRing A] [Algebra R A]

/-- `AlgHom` version of `IsAdicCompletion.liftRingHom`. -/
noncomputable
/--
Definition of `liftAlgHom` / `liftAlgHom` 的定义

English:
definition liftAlgHom
  signature: (f : (n : Nat) -> A ->ₐ[R] S ⧸ I ^ n)
  body: ((ofAlgEquiv I).symm.toAlgHom.restrictScalars R).comp (AdicCompletion.liftAlgHom I f hf)

中文:
定义 liftAlgHom
  签名: (f : (n : 自然数) -> A ->ₐ[R] S ⧸ I ^ n)
  定义体: ((ofAlgEquiv I).symm.toAlgHom.restrictScalars R).comp (AdicCompletion.liftAlgHom I f hf)

Depends on / 依赖: AdicCompletion, AdicCompletion.liftAlgHom, liftAlgHom, ofAlgEquiv, restrictScalars, symm.toAlgHom.restrictScalars, toAlgHom
-/
def liftAlgHom (f : (n : Nat) -> A ->ₐ[R] S ⧸ I ^ n)
    (hf : forall {m n : Nat} (hle : m <= n),
      (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hle)).comp (f n) = f m) :
    A ->ₐ[R] S :=
  ((ofAlgEquiv I).symm.toAlgHom.restrictScalars R).comp (AdicCompletion.liftAlgHom I f hf)

variable (f : (n : Nat) -> A ->ₐ[R] S ⧸ I ^ n)
    (hf : forall {m n : Nat} (hle : m <= n),
      (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hle)).comp (f n) = f m)

@[simp]
/--
lemma `mk_liftAlgHom` / 引理 `mk_liftAlgHom`

English:
lemma mk_liftAlgHom
  given: (n : Nat) (x : A)
  statement: liftAlgHom I f hf x = f n x
  proof: by
  simp [liftAlgHom]

@[simp]

中文:
引理 mk_liftAlgHom
  条件: (n : 自然数) (x : A)
  结论: liftAlgHom I f hf x = f n x
  证明: by
  simp [liftAlgHom]

@[simp]

Depends on / 依赖: liftAlgHom
-/
lemma mk_liftAlgHom (n : Nat) (x : A) : liftAlgHom I f hf x = f n x := by
  simp [liftAlgHom]

@[simp]
/--
lemma `mkₐ_comp_liftAlgHom` / 引理 `mkₐ_comp_liftAlgHom`

English:
lemma mkₐ_comp_liftAlgHom
  given: (n : Nat)
  proof: AlgHom.ext fun _ => mk_liftAlgHom _ _ hf _ _

中文:
引理 mkₐ_comp_liftAlgHom
  条件: (n : 自然数)
  证明: AlgHom.ext fun _ => mk_liftAlgHom _ _ hf _ _

Depends on / 依赖: AlgHom, AlgHom.ext, mk_liftAlgHom
-/
lemma mkₐ_comp_liftAlgHom (n : Nat) :
    (Ideal.Quotient.mkₐ R (I ^ n)).comp (liftAlgHom I f hf) = f n :=
  AlgHom.ext fun _ => mk_liftAlgHom _ _ hf _ _

/--
lemma `algHom_ext` / 引理 `algHom_ext`

English:
lemma algHom_ext
  statement: {f g : A ->ₐ[R] S}
  proof: by
  rw [← AlgHom.cancel_left (f := ((ofAlgEquiv I).restrictScalars R).toAlgHom)
    (ofAlgEquiv I).injective]
  ext1 x
  refine AdicCompletion.ext_evalₐ fun n => ?_
  simpa using congr($(H n) x)

中文:
引理 algHom_ext
  结论: {f g : A ->ₐ[R] S}
  证明: by
  rw [← AlgHom.cancel_left (f := ((ofAlgEquiv I).restrictScalars R).toAlgHom)
    (ofAlgEquiv I).injective]
  ext1 x
  refine AdicCompletion.ext_evalₐ fun n => ?_
  simpa using congr($(H n) x)

Depends on / 依赖: AdicCompletion, AdicCompletion.ext_eval, AlgHom, AlgHom.cancel_left, cancel_left, injective, ofAlgEquiv, restrictScalars, toAlgHom
-/
lemma algHom_ext {f g : A ->ₐ[R] S}
    (H : forall n, (Ideal.Quotient.mkₐ R (I ^ n)).comp f = (Ideal.Quotient.mkₐ R (I ^ n)).comp g) :
    f = g := by
  rw [← AlgHom.cancel_left (f := ((ofAlgEquiv I).restrictScalars R).toAlgHom)
    (ofAlgEquiv I).injective]
  ext1 x
  refine AdicCompletion.ext_evalₐ fun n => ?_
  simpa using congr($(H n) x)

end

end

namespace StrictMono

variable {a : Nat -> Nat} (ha : StrictMono a) (f : (n : Nat) -> R ->+* S ⧸ I ^ a n)
variable (hf : forall {m}, (factorPow I (ha.monotone m.le_succ)).comp (f (m + 1)) = f m)

variable {I}

include hf in
/--
theorem `factorPow_comp_eq_of_factorPow_comp_succ_eq'` / 定理 `factorPow_comp_eq_of_factorPow_comp_succ_eq'`

English:
theorem factorPow_comp_eq_of_factorPow_comp_succ_eq'
  proof: by
  ext x
  symm
  refine Submodule.eq_factor_of_eq_factor_succ ?_ (fun n => f n x) ?_ hle
  · exact fun _ _ le => Ideal.pow_le_pow_right (ha.monotone le)
  · intro s
    simp only [RingHom.ext_iff] at hf
    simpa using (hf x).symm

中文:
定理 factorPow_comp_eq_of_factorPow_comp_succ_eq'
  证明: by
  ext x
  symm
  refine Submodule.eq_factor_of_eq_factor_succ ?_ (fun n => f n x) ?_ hle
  · exact fun _ _ le => Ideal.pow_le_pow_right (ha.monotone le)
  · intro s
    simp only [RingHom.ext_iff] at hf
    simpa using (hf x).symm

Depends on / 依赖: Ideal.pow_le_pow_right, RingHom, RingHom.ext_iff, Submodule, Submodule.eq_factor_of_eq_factor_succ, eq_factor_of_eq_factor_succ, ext_iff, ha.monotone, monotone, pow_le_pow_right
-/
theorem factorPow_comp_eq_of_factorPow_comp_succ_eq'
    {m n : Nat} (hle : m <= n) : (factorPow I (ha.monotone hle)).comp (f n) = f m := by
  ext x
  symm
  refine Submodule.eq_factor_of_eq_factor_succ ?_ (fun n => f n x) ?_ hle
  · exact fun _ _ le => Ideal.pow_le_pow_right (ha.monotone le)
  · intro s
    simp only [RingHom.ext_iff] at hf
    simpa using (hf x).symm

variable [IsAdicComplete I S]

variable (I)

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `liftRingHom` / `liftRingHom` 的定义

English:
definition liftRingHom
  signature: : R ->+* S
  body: IsAdicComplete.liftRingHom I (fun n => (factorPow I (ha.id_le n)).comp (f n))
    (fun hle => by ext; simp [← factorPow_comp_eq_of_factorPow_comp_succ_eq' ha f hf hle])

中文:
定义 liftRingHom
  签名: : R ->+* S
  定义体: IsAdicComplete.liftRingHom I (fun n => (factorPow I (ha.id_le n)).comp (f n))
    (fun hle => by ext; simp [← factorPow_comp_eq_of_factorPow_comp_succ_eq' ha f hf hle])

Depends on / 依赖: IsAdicComplete, IsAdicComplete.liftRingHom, factorPow, factorPow_comp_eq_of_factorPow_comp_succ_eq, ha.id_le, id_le, liftRingHom
-/
noncomputable def liftRingHom : R ->+* S :=
  IsAdicComplete.liftRingHom I (fun n => (factorPow I (ha.id_le n)).comp (f n))
    (fun hle => by ext; simp [← factorPow_comp_eq_of_factorPow_comp_succ_eq' ha f hf hle])

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `mk_liftRingHom` / 定理 `mk_liftRingHom`

English:
theorem mk_liftRingHom
  given: {n : Nat} (x : R)
  proof: by
  simp [liftRingHom, IsAdicComplete.liftRingHom,
      factorPow_comp_eq_of_factorPow_comp_succ_eq' ha f hf ha.le_apply]

@[simp]

中文:
定理 mk_liftRingHom
  条件: {n : 自然数} (x : R)
  证明: by
  simp [liftRingHom, IsAdicComplete.liftRingHom,
      factorPow_comp_eq_of_factorPow_comp_succ_eq' ha f hf ha.le_apply]

@[simp]

Depends on / 依赖: IsAdicComplete, IsAdicComplete.liftRingHom, factorPow_comp_eq_of_factorPow_comp_succ_eq, ha.le_apply, le_apply, liftRingHom
-/
theorem mk_liftRingHom {n : Nat} (x : R) :
    Ideal.Quotient.mk _ (liftRingHom I ha f hf x) = f n x := by
  simp [liftRingHom, IsAdicComplete.liftRingHom,
      factorPow_comp_eq_of_factorPow_comp_succ_eq' ha f hf ha.le_apply]

@[simp]
/--
theorem `mk_comp_liftRingHom` / 定理 `mk_comp_liftRingHom`

English:
theorem mk_comp_liftRingHom
  given: {n : Nat}
  proof: by
  ext; simp

中文:
定理 mk_comp_liftRingHom
  条件: {n : 自然数}
  证明: by
  ext; simp
-/
theorem mk_comp_liftRingHom {n : Nat} :
    (Ideal.Quotient.mk (I ^ (a n))).comp (liftRingHom I ha f hf) = f n := by
  ext; simp

/--
theorem `eq_liftRingHom` / 定理 `eq_liftRingHom`

English:
theorem eq_liftRingHom
  statement: {F : R ->+* S}
  proof: by
  apply DFunLike.coe_injective
  apply IsHausdorff.StrictMono.funext' I ha
  intro n m
  simp [← hF n]

中文:
定理 eq_liftRingHom
  结论: {F : R ->+* S}
  证明: by
  apply DFunLike.coe_injective
  apply IsHausdorff.StrictMono.funext' I ha
  intro n m
  simp [← hF n]

Depends on / 依赖: DFunLike, DFunLike.coe_injective, IsHausdorff, IsHausdorff.StrictMono.funext, StrictMono, coe_injective
-/
theorem eq_liftRingHom {F : R ->+* S}
    (hF : forall n, (Ideal.Quotient.mk _).comp F = f n) : F = liftRingHom I ha f hf := by
  apply DFunLike.coe_injective
  apply IsHausdorff.StrictMono.funext' I ha
  intro n m
  simp [← hF n]

end StrictMono

end IsAdicComplete
