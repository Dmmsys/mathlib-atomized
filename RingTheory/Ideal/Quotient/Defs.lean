/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Chris Hughes, Mario Carneiro, Anne Baanen
-/
module

public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.RingTheory.Congruence.Defs
public import Mathlib.RingTheory.Ideal.Defs

/-!
# Ideal quotients

This file defines ideal quotients as a special case of submodule quotients and proves some basic
results about these quotients.

See `RingCon.Quotient` for quotients of (possibly non-commutative) semirings.

## Main definitions

- `Ideal.instHasQuotient`: the quotient of a commutative ring `R` by an ideal `I : Ideal R`
- `Ideal.Quotient.commRing`: the ring structure of the ideal quotient
- `Ideal.Quotient.mk`: map an element of `R` to the quotient `R ⧸ I`
- `Ideal.Quotient.lift`: turn a map `R → S` into a map `R ⧸ I → S`
- `Ideal.quotEquivOfEq`: quotienting by equal ideals gives isomorphic rings
-/

@[expose] public section


universe u v w

namespace Ideal

open Set

variable {R : Type u} [Ring R] (I J : Ideal R) {a b : R}
variable {S : Type v}

/--
Instance `instHasQuotient` / 实例 `instHasQuotient`

English:
instance instHasQuotient
  signature: : HasQuotient R (Ideal R)
  body: Submodule.hasQuotient

中文:
实例 instHasQuotient
  签名: : HasQuotient R (Ideal R)
  定义体: Submodule.hasQuotient

Depends on / 依赖: Submodule, Submodule.hasQuotient, hasQuotient
-/
instance instHasQuotient : HasQuotient R (Ideal R) := Submodule.hasQuotient

/-- Shortcut instance for commutative rings. -/
instance {R} [CommRing R] : HasQuotient R (Ideal R) := inferInstance

namespace Quotient

variable {I} {x y : R}

/--
Instance `one` / 实例 `one`

English:
instance one
  signature: (I : Ideal R)
  body: ⟨Submodule.Quotient.mk 1⟩

中文:
实例 one
  签名: (I : Ideal R)
  定义体: ⟨Submodule.Quotient.mk 1⟩

Depends on / 依赖: Quotient, Submodule, Submodule.Quotient.mk
-/
instance one (I : Ideal R) : One (R ⧸ I) :=
  ⟨Submodule.Quotient.mk 1⟩

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `ringCon` / `ringCon` 的定义

English:
definition ringCon
  signature: (I : Ideal R) [I.IsTwoSided]
  body: QuotientAddGroup.con I.toAddSubgroup
  mul' {a₁ b₁ a₂ b₂} h₁ h₂ := by
    rw [Submodule.quotientRel_def] at h₁ h₂ ⊢
    exact mul_sub_mul_mem I h₁ h₂

中文:
定义 ringCon
  签名: (I : Ideal R) [I.IsTwoSided]
  定义体: QuotientAddGroup.con I.toAddSubgroup
  mul' {a₁ b₁ a₂ b₂} h₁ h₂ := by
    rw [Submodule.quotientRel_def] at h₁ h₂ ⊢
    exact mul_sub_mul_mem I h₁ h₂
-/
protected def ringCon (I : Ideal R) [I.IsTwoSided] : RingCon R where
  __ := QuotientAddGroup.con I.toAddSubgroup
  mul' {a₁ b₁ a₂ b₂} h₁ h₂ := by
    rw [Submodule.quotientRel_def] at h₁ h₂ ⊢
    exact mul_sub_mul_mem I h₁ h₂

/-- **Quotient ring**: the quotient of a ring by a two-sided ideal is a ring. -/
@[wikidata Q619436]
/--
Instance `ring` / 实例 `ring`

English:
instance ring
  signature: (I : Ideal R) [I.IsTwoSided]
  body: inferInstanceAs Ring (Quotient.ringCon I).Quotient

中文:
实例 ring
  签名: (I : Ideal R) [I.IsTwoSided]
  定义体: inferInstanceAs Ring (Quotient.ringCon I).Quotient

Depends on / 依赖: Quotient, Quotient.ringCon, ringCon
-/
instance ring (I : Ideal R) [I.IsTwoSided] : Ring (R ⧸ I) :=
inferInstanceAs Ring (Quotient.ringCon I).Quotient

/--
Instance `semiring` / 实例 `semiring`

English:
instance semiring
  signature: {R} [CommRing R] (I : Ideal R)
  body: (ring I).toSemiring

中文:
实例 semiring
  签名: {R} [CommRing R] (I : Ideal R)
  定义体: (ring I).toSemiring

Depends on / 依赖: toSemiring
-/
instance semiring {R} [CommRing R] (I : Ideal R) : Semiring (R ⧸ I) := (ring I).toSemiring
/--
Instance `commSemiring` / 实例 `commSemiring`

English:
instance commSemiring
  signature: {R} [CommRing R] (I : Ideal R)
  body: by rintro ⟨a⟩ ⟨b⟩; exact congr_arg _ (mul_comm a b)

中文:
实例 commSemiring
  签名: {R} [CommRing R] (I : Ideal R)
  定义体: by rintro ⟨a⟩ ⟨b⟩; exact congr_arg _ (mul_comm a b)

Depends on / 依赖: congr_arg, mul_comm
-/
instance commSemiring {R} [CommRing R] (I : Ideal R) : CommSemiring (R ⧸ I) where
  mul_comm := by rintro ⟨a⟩ ⟨b⟩; exact congr_arg _ (mul_comm a b)

instance {R} [CommRing R] (I : Ideal R) : Ring (R ⧸ I) := ring I
/--
Instance `commRing` / 实例 `commRing`

English:
instance commRing
  signature: {R} [CommRing R] (I : Ideal R)

中文:
实例 commRing
  签名: {R} [CommRing R] (I : Ideal R)

Depends on / 依赖: with_reducible_and_instances
-/
instance commRing {R} [CommRing R] (I : Ideal R) : CommRing (R ⧸ I) where

variable [I.IsTwoSided]

-- Sanity test to make sure no diamonds have emerged in `commRing`
example : (ring I).toAddCommGroup = Submodule.Quotient.addCommGroup I := by
  with_reducible_and_instances rfl

variable (I) in
/--
Definition of `mk` / `mk` 的定义

English:
definition mk
  signature: : R ->+* R ⧸ I where
  body: Submodule.Quotient.mk a
  map_zero' := rfl
  map_one' := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

中文:
定义 mk
  签名: : R ->+* R ⧸ I where
  定义体: Submodule.Quotient.mk a
  map_zero' := rfl
  map_one' := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

Depends on / 依赖: Quotient, Submodule, Submodule.Quotient.mk
-/
def mk : R ->+* R ⧸ I where
  toFun a := Submodule.Quotient.mk a
  map_zero' := rfl
  map_one' := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Coe R (R ⧸ I)
  body: ⟨Ideal.Quotient.mk I⟩

中文:
实例 :
  签名: Coe R (R ⧸ I)
  定义体: ⟨Ideal.Quotient.mk I⟩

Depends on / 依赖: Ideal.Quotient.mk, Quotient
-/
instance : Coe R (R ⧸ I) :=
  ⟨Ideal.Quotient.mk I⟩

/-- Two `RingHom`s from the quotient by an ideal are equal if their
compositions with `Ideal.Quotient.mk'` are equal.

See note [partially-applied ext lemmas]. -/
@[ext 1100]
/--
theorem `ringHom_ext` / 定理 `ringHom_ext`

English:
theorem ringHom_ext
  given: [NonAssocSemiring S] ⦃f g
  statement: R ⧸ I ->+* S⦄ (h : f.comp (mk I) = g.comp (mk I)) :
  proof: RingHom.ext fun x => Quotient.inductionOn' x (RingHom.congr_fun h :)

中文:
定理 ringHom_ext
  条件: [NonAssocSemiring S] ⦃f g
  结论: R ⧸ I ->+* S⦄ (h : f.comp (mk I) = g.comp (mk I)) :
  证明: RingHom.ext fun x => Quotient.inductionOn' x (RingHom.congr_fun h :)

Depends on / 依赖: Quotient, Quotient.inductionOn, RingHom, RingHom.congr_fun, RingHom.ext, congr_fun, inductionOn
-/
theorem ringHom_ext [NonAssocSemiring S] ⦃f g : R ⧸ I ->+* S⦄ (h : f.comp (mk I) = g.comp (mk I)) :
    f = g :=
RingHom.ext fun x => Quotient.inductionOn' x (RingHom.congr_fun h :)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Nonempty (R ⧸ I)
  body: ⟨mk I 37⟩

中文:
实例 :
  签名: Nonempty (R ⧸ I)
  定义体: ⟨mk I 37⟩
-/
instance : Nonempty (R ⧸ I) :=
  ⟨mk I 37⟩

/--
theorem `eq` / 定理 `eq`

English:
theorem eq
  statement: mk I x = mk I y ↔ x - y in I
  proof: Submodule.Quotient.eq I

@[simp]

中文:
定理 eq
  结论: mk I x = mk I y ↔ x - y in I
  证明: Submodule.Quotient.eq I

@[simp]
-/
protected theorem eq : mk I x = mk I y ↔ x - y in I :=
  Submodule.Quotient.eq I

@[simp]
/--
theorem `mk_eq_mk` / 定理 `mk_eq_mk`

English:
theorem mk_eq_mk
  given: (x : R)
  statement: (Submodule.Quotient.mk x : R ⧸ I) = mk I x
  proof: rfl

中文:
定理 mk_eq_mk
  条件: (x : R)
  结论: (Submodule.Quotient.mk x : R ⧸ I) = mk I x
  证明: rfl
-/
theorem mk_eq_mk (x : R) : (Submodule.Quotient.mk x : R ⧸ I) = mk I x := rfl

/--
theorem `eq_zero_iff_mem` / 定理 `eq_zero_iff_mem`

English:
theorem eq_zero_iff_mem
  statement: mk I a = 0 ↔ a in I
  proof: Submodule.Quotient.mk_eq_zero _

中文:
定理 eq_zero_iff_mem
  结论: mk I a = 0 ↔ a in I
  证明: Submodule.Quotient.mk_eq_zero _

Depends on / 依赖: Quotient, Submodule, Submodule.Quotient.mk_eq_zero, mk_eq_zero
-/
theorem eq_zero_iff_mem : mk I a = 0 ↔ a in I :=
  Submodule.Quotient.mk_eq_zero _

/--
theorem `mk_eq_mk_iff_sub_mem` / 定理 `mk_eq_mk_iff_sub_mem`

English:
theorem mk_eq_mk_iff_sub_mem
  given: (x y : R)
  statement: mk I x = mk I y ↔ x - y in I
  proof: by
  rw [← eq_zero_iff_mem]; rw [map_sub]; rw [sub_eq_zero]

中文:
定理 mk_eq_mk_iff_sub_mem
  条件: (x y : R)
  结论: mk I x = mk I y ↔ x - y in I
  证明: by
  rw [← eq_zero_iff_mem]; rw [map_sub]; rw [sub_eq_zero]

Depends on / 依赖: eq_zero_iff_mem, map_sub, sub_eq_zero
-/
theorem mk_eq_mk_iff_sub_mem (x y : R) : mk I x = mk I y ↔ x - y in I := by
  rw [← eq_zero_iff_mem]; rw [map_sub]; rw [sub_eq_zero]

/--
lemma `mk_eq_one_iff_sub_mem` / 引理 `mk_eq_one_iff_sub_mem`

English:
lemma mk_eq_one_iff_sub_mem
  given: (x : R)
  statement: mk I x = 1 ↔ x - 1 in I
  proof: by
  rw [← mk_eq_mk_iff_sub_mem]; rw [map_one]

@[simp]

中文:
引理 mk_eq_one_iff_sub_mem
  条件: (x : R)
  结论: mk I x = 1 ↔ x - 1 in I
  证明: by
  rw [← mk_eq_mk_iff_sub_mem]; rw [map_one]

@[simp]

Depends on / 依赖: map_one, mk_eq_mk_iff_sub_mem
-/
lemma mk_eq_one_iff_sub_mem (x : R) : mk I x = 1 ↔ x - 1 in I := by
  rw [← mk_eq_mk_iff_sub_mem]; rw [map_one]

@[simp]
/--
theorem `mk_out` / 定理 `mk_out`

English:
theorem mk_out
  given: (x : R ⧸ I)
  statement: Ideal.Quotient.mk I (Quotient.out x) = x
  proof: Quotient.out_eq x

中文:
定理 mk_out
  条件: (x : R ⧸ I)
  结论: Ideal.Quotient.mk I (Quotient.out x) = x
  证明: Quotient.out_eq x

Depends on / 依赖: Quotient, Quotient.out_eq, out_eq
-/
theorem mk_out (x : R ⧸ I) : Ideal.Quotient.mk I (Quotient.out x) = x :=
  Quotient.out_eq x

/--
theorem `mk_surjective` / 定理 `mk_surjective`

English:
theorem mk_surjective
  statement: Function.Surjective (mk I)
  proof: fun y =>
  Quotient.inductionOn' y fun x => Exists.intro x rfl

中文:
定理 mk_surjective
  结论: Function.Surjective (mk I)
  证明: fun y =>
  Quotient.inductionOn' y fun x => Exists.intro x rfl
-/
theorem mk_surjective : Function.Surjective (mk I) := fun y =>
  Quotient.inductionOn' y fun x => Exists.intro x rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: RingHomSurjective (mk I)
  body: ⟨mk_surjective⟩

中文:
实例 :
  签名: RingHomSurjective (mk I)
  定义体: ⟨mk_surjective⟩

Depends on / 依赖: mk_surjective
-/
instance : RingHomSurjective (mk I) :=
  ⟨mk_surjective⟩

/--
theorem `quotient_ring_saturate` / 定理 `quotient_ring_saturate`

English:
theorem quotient_ring_saturate
  given: (s : Set R)
  proof: by
  ext x
  simp only [mem_preimage, mem_image, mem_iUnion, Ideal.Quotient.eq]
  exact
    ⟨fun ⟨a, a_in, h⟩ => ⟨⟨_, I.neg_mem h⟩, a, a_in, by simp⟩, fun ⟨⟨i, hi⟩, a, ha, Eq⟩ =>
      ⟨a, ha, by rw [← Eq, sub_add_eq_sub_sub_swap, sub_self, zero_sub]; exact I.neg_mem hi⟩⟩

中文:
定理 quotient_ring_saturate
  条件: (s : Set R)
  证明: by
  ext x
  simp only [mem_preimage, mem_image, mem_iUnion, Ideal.Quotient.eq]
  exact
    ⟨fun ⟨a, a_in, h⟩ => ⟨⟨_, I.neg_mem h⟩, a, a_in, by simp⟩, fun ⟨⟨i, hi⟩, a, ha, Eq⟩ =>
      ⟨a, ha, by rw [← Eq, sub_add_eq_sub_sub_swap, sub_self, zero_sub]; exact I.neg_mem hi⟩⟩

Depends on / 依赖: I.neg_mem, Ideal.Quotient.eq, Quotient, a_in, mem_iUnion, mem_image, mem_preimage, neg_mem, sub_add_eq_sub_sub_swap, sub_self, zero_sub
-/
theorem quotient_ring_saturate (s : Set R) :
    mk I ⁻¹' mk I '' s = ⋃ x : I, (fun y => x.1 + y) '' s := by
  ext x
  simp only [mem_preimage, mem_image, mem_iUnion, Ideal.Quotient.eq]
  exact
    ⟨fun ⟨a, a_in, h⟩ => ⟨⟨_, I.neg_mem h⟩, a, a_in, by simp⟩, fun ⟨⟨i, hi⟩, a, ha, Eq⟩ =>
      ⟨a, ha, by rw [← Eq, sub_add_eq_sub_sub_swap, sub_self, zero_sub]; exact I.neg_mem hi⟩⟩

variable [Semiring S] (I)

/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: (f : R ->+* S) (H : forall a : R, a in I -> f a = 0)
  body: { QuotientAddGroup.lift I.toAddSubgroup f.toAddMonoidHom H with
    map_one' := f.map_one
    map_mul' := fun a₁ a₂ => Quotient.inductionOn₂' a₁ a₂ f.map_mul }

@[simp]

中文:
定义 lift
  签名: (f : R ->+* S) (H : 对任意 a : R, a in I -> f a = 0)
  定义体: { QuotientAddGroup.lift I.toAddSubgroup f.toAddMonoidHom H with
    map_one' := f.map_one
    map_mul' := fun a₁ a₂ => Quotient.inductionOn₂' a₁ a₂ f.map_mul }

@[simp]

Depends on / 依赖: I.toAddSubgroup, Quotient, Quotient.inductionOn, QuotientAddGroup, QuotientAddGroup.lift, f.map_mul, f.map_one, f.toAddMonoidHom, map_mul, map_one, toAddMonoidHom, toAddSubgroup
-/
def lift (f : R ->+* S) (H : forall a : R, a in I -> f a = 0) : R ⧸ I ->+* S :=
  { QuotientAddGroup.lift I.toAddSubgroup f.toAddMonoidHom H with
    map_one' := f.map_one
    map_mul' := fun a₁ a₂ => Quotient.inductionOn₂' a₁ a₂ f.map_mul }

@[simp]
/--
theorem `lift_mk` / 定理 `lift_mk`

English:
theorem lift_mk
  given: (f : R ->+* S) (H : forall a : R, a in I -> f a = 0)
  proof: rfl

中文:
定理 lift_mk
  条件: (f : R ->+* S) (H : 对任意 a : R, a in I -> f a = 0)
  证明: rfl
-/
theorem lift_mk (f : R ->+* S) (H : forall a : R, a in I -> f a = 0) :
    lift I f H (mk I a) = f a :=
  rfl

/--
lemma `lift_comp_mk` / 引理 `lift_comp_mk`

English:
lemma lift_comp_mk
  given: (f : R ->+* S) (H : forall a : R, a in I -> f a = 0)
  proof: rfl

中文:
引理 lift_comp_mk
  条件: (f : R ->+* S) (H : 对任意 a : R, a in I -> f a = 0)
  证明: rfl
-/
lemma lift_comp_mk (f : R ->+* S) (H : forall a : R, a in I -> f a = 0) :
    (lift I f H).comp (mk I) = f := rfl

/--
theorem `lift_surjective_of_surjective` / 定理 `lift_surjective_of_surjective`

English:
theorem lift_surjective_of_surjective
  statement: {f : R ->+* S} (H : forall a : R, a in I -> f a = 0)
  proof: by
  intro y
  obtain ⟨x, rfl⟩ := hf y
  use Ideal.Quotient.mk I x
  simp only [Ideal.Quotient.lift_mk]

中文:
定理 lift_surjective_of_surjective
  结论: {f : R ->+* S} (H : 对任意 a : R, a in I -> f a = 0)
  证明: by
  intro y
  obtain ⟨x, rfl⟩ := hf y
  use Ideal.Quotient.mk I x
  simp only [Ideal.Quotient.lift_mk]

Depends on / 依赖: Ideal.Quotient.lift_mk, Ideal.Quotient.mk, Quotient, lift_mk
-/
theorem lift_surjective_of_surjective {f : R ->+* S} (H : forall a : R, a in I -> f a = 0)
    (hf : Function.Surjective f) : Function.Surjective (Ideal.Quotient.lift I f H) := by
  intro y
  obtain ⟨x, rfl⟩ := hf y
  use Ideal.Quotient.mk I x
  simp only [Ideal.Quotient.lift_mk]

variable {S T U : Ideal R} [S.IsTwoSided] [T.IsTwoSided] [U.IsTwoSided]

/--
Definition of `factor` / `factor` 的定义

English:
definition factor
  signature: (H : S <= T)
  body: Ideal.Quotient.lift S (mk T) fun _ hx => eq_zero_iff_mem.2 (H hx)

@[simp]

中文:
定义 factor
  签名: (H : S <= T)
  定义体: Ideal.Quotient.lift S (mk T) fun _ hx => eq_zero_iff_mem.2 (H hx)

@[simp]

Depends on / 依赖: Ideal.Quotient.lift, Quotient, eq_zero_iff_mem
-/
def factor (H : S <= T) : R ⧸ S ->+* R ⧸ T :=
  Ideal.Quotient.lift S (mk T) fun _ hx => eq_zero_iff_mem.2 (H hx)

@[simp]
/--
theorem `factor_mk` / 定理 `factor_mk`

English:
theorem factor_mk
  given: (H : S <= T) (x : R)
  statement: factor H (mk S x) = mk T x
  proof: rfl

@[simp]

中文:
定理 factor_mk
  条件: (H : S <= T) (x : R)
  结论: factor H (mk S x) = mk T x
  证明: rfl

@[simp]
-/
theorem factor_mk (H : S <= T) (x : R) : factor H (mk S x) = mk T x :=
  rfl

@[simp]
/--
theorem `factor_eq` / 定理 `factor_eq`

English:
theorem factor_eq
  statement: factor (le_refl S) = RingHom.id _
  proof: by
  ext
  simp

@[simp]

中文:
定理 factor_eq
  结论: factor (le_refl S) = RingHom.id _
  证明: by
  ext
  simp

@[simp]
-/
theorem factor_eq : factor (le_refl S) = RingHom.id _ := by
  ext
  simp

@[simp]
/--
theorem `factor_comp_mk` / 定理 `factor_comp_mk`

English:
theorem factor_comp_mk
  given: (H : S <= T)
  statement: (factor H).comp (mk S) = mk T
  proof: by
  ext x
  rw [RingHom.comp_apply]; rw [factor_mk]

@[simp]

中文:
定理 factor_comp_mk
  条件: (H : S <= T)
  结论: (factor H).comp (mk S) = mk T
  证明: by
  ext x
  rw [RingHom.comp_apply]; rw [factor_mk]

@[simp]

Depends on / 依赖: RingHom, RingHom.comp_apply, comp_apply, factor_mk
-/
theorem factor_comp_mk (H : S <= T) : (factor H).comp (mk S) = mk T := by
  ext x
  rw [RingHom.comp_apply]; rw [factor_mk]

@[simp]
/--
theorem `factor_comp` / 定理 `factor_comp`

English:
theorem factor_comp
  given: (H1 : S <= T) (H2 : T <= U)
  proof: by
  ext
  simp

@[simp]

中文:
定理 factor_comp
  条件: (H1 : S <= T) (H2 : T <= U)
  证明: by
  ext
  simp

@[simp]
-/
theorem factor_comp (H1 : S <= T) (H2 : T <= U) :
    (factor H2).comp (factor H1) = factor (H1.trans H2) := by
  ext
  simp

@[simp]
/--
theorem `factor_comp_apply` / 定理 `factor_comp_apply`

English:
theorem factor_comp_apply
  given: (H1 : S <= T) (H2 : T <= U) (x : R ⧸ S)
  proof: by
  rw [← RingHom.comp_apply]
  simp

中文:
定理 factor_comp_apply
  条件: (H1 : S <= T) (H2 : T <= U) (x : R ⧸ S)
  证明: by
  rw [← RingHom.comp_apply]
  simp

Depends on / 依赖: RingHom, RingHom.comp_apply, comp_apply
-/
theorem factor_comp_apply (H1 : S <= T) (H2 : T <= U) (x : R ⧸ S) :
    factor H2 (factor H1 x) = factor (H1.trans H2) x := by
  rw [← RingHom.comp_apply]
  simp

/--
lemma `factor_surjective` / 引理 `factor_surjective`

English:
lemma factor_surjective
  given: (H : S <= T)
  statement: Function.Surjective (factor H)
  proof: Ideal.Quotient.lift_surjective_of_surjective _ _ Ideal.Quotient.mk_surjective

中文:
引理 factor_surjective
  条件: (H : S <= T)
  结论: Function.Surjective (factor H)
  证明: Ideal.Quotient.lift_surjective_of_surjective _ _ Ideal.Quotient.mk_surjective

Depends on / 依赖: Ideal.Quotient.lift_surjective_of_surjective, Ideal.Quotient.mk_surjective, Quotient, lift_surjective_of_surjective, mk_surjective
-/
lemma factor_surjective (H : S <= T) : Function.Surjective (factor H) :=
  Ideal.Quotient.lift_surjective_of_surjective _ _ Ideal.Quotient.mk_surjective

end Quotient

variable {I J} [I.IsTwoSided] [J.IsTwoSided]

/--
Definition of `quotEquivOfEq` / `quotEquivOfEq` 的定义

English:
definition quotEquivOfEq
  signature: (h : I = J)
  body: { Submodule.quotEquivOfEq I J h with
    map_mul' := by
      rintro ⟨x⟩ ⟨y⟩
      rfl }

@[simp]

中文:
定义 quotEquivOfEq
  签名: (h : I = J)
  定义体: { Submodule.quotEquivOfEq I J h with
    map_mul' := by
      rintro ⟨x⟩ ⟨y⟩
      rfl }

@[simp]

Depends on / 依赖: Submodule, Submodule.quotEquivOfEq, map_mul, quotEquivOfEq
-/
def quotEquivOfEq (h : I = J) : R ⧸ I ≃+* R ⧸ J :=
  { Submodule.quotEquivOfEq I J h with
    map_mul' := by
      rintro ⟨x⟩ ⟨y⟩
      rfl }

@[simp]
/--
theorem `quotEquivOfEq_mk` / 定理 `quotEquivOfEq_mk`

English:
theorem quotEquivOfEq_mk
  given: (h : I = J) (x : R)
  proof: rfl

@[simp]

中文:
定理 quotEquivOfEq_mk
  条件: (h : I = J) (x : R)
  证明: rfl

@[simp]
-/
theorem quotEquivOfEq_mk (h : I = J) (x : R) :
    quotEquivOfEq h (Ideal.Quotient.mk I x) = Ideal.Quotient.mk J x :=
  rfl

@[simp]
/--
theorem `quotEquivOfEq_symm` / 定理 `quotEquivOfEq_symm`

English:
theorem quotEquivOfEq_symm
  given: (h : I = J)
  proof: by ext; rfl

中文:
定理 quotEquivOfEq_symm
  条件: (h : I = J)
  证明: by ext; rfl
-/
theorem quotEquivOfEq_symm (h : I = J) :
    (Ideal.quotEquivOfEq h).symm = Ideal.quotEquivOfEq h.symm := by ext; rfl

/--
theorem `quotEquivOfEq_eq_factor` / 定理 `quotEquivOfEq_eq_factor`

English:
theorem quotEquivOfEq_eq_factor
  given: (h : I = J) (x : R ⧸ I)
  proof: rfl

中文:
定理 quotEquivOfEq_eq_factor
  条件: (h : I = J) (x : R ⧸ I)
  证明: rfl
-/
theorem quotEquivOfEq_eq_factor (h : I = J) (x : R ⧸ I) :
    Ideal.quotEquivOfEq h x = Ideal.Quotient.factor (h ▸ le_refl I) x := rfl

end Ideal
