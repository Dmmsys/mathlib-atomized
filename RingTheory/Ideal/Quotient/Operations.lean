/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Patrick Massot
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Operations
public import Mathlib.Algebra.Ring.Fin
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Basic

/-!
# More operations on modules and ideals related to quotients

## Main results:

- `RingHom.quotientKerEquivRange` : the **first isomorphism theorem** for commutative rings.
- `RingHom.quotientKerEquivRangeS` : the **first isomorphism theorem**
  for a morphism from a commutative ring to a semiring.
- `AlgHom.quotientKerEquivRange` : the **first isomorphism theorem**
  for a morphism of algebras (over a commutative semiring)
- `Ideal.quotientInfRingEquivPiQuotient`: the **Chinese Remainder Theorem**, version for coprime
  ideals (see also `ZMod.prodEquivPi` in `Data.ZMod.Quotient` for elementary versions about
  `ZMod`).
-/

@[expose] public section

universe u v w

namespace RingHom

variable {R : Type u} {S : Type v} [Ring R] [Semiring S] (f : R ->+* S)

/--
Definition of `kerLift` / `kerLift` 的定义

English:
definition kerLift
  signature: : R ⧸ ker f ->+* S
  body: Ideal.Quotient.lift _ f fun _ => mem_ker.mp

@[simp]

中文:
定义 kerLift
  签名: : R ⧸ ker f ->+* S
  定义体: Ideal.Quotient.lift _ f fun _ => mem_ker.mp

@[simp]

Depends on / 依赖: Ideal.Quotient.lift, Quotient, mem_ker, mem_ker.mp
-/
def kerLift : R ⧸ ker f ->+* S :=
  Ideal.Quotient.lift _ f fun _ => mem_ker.mp

@[simp]
/--
theorem `kerLift_mk` / 定理 `kerLift_mk`

English:
theorem kerLift_mk
  given: (r : R)
  statement: kerLift f (Ideal.Quotient.mk (ker f) r) = f r
  proof: Ideal.Quotient.lift_mk _ _ _

中文:
定理 kerLift_mk
  条件: (r : R)
  结论: kerLift f (理想.商.mk (ker f) r) = f r
  证明: Ideal.Quotient.lift_mk _ _ _

Depends on / 依赖: Ideal.Quotient.lift_mk, Quotient, lift_mk
-/
theorem kerLift_mk (r : R) : kerLift f (Ideal.Quotient.mk (ker f) r) = f r :=
  Ideal.Quotient.lift_mk _ _ _

/--
theorem `lift_injective_of_ker_le_ideal` / 定理 `lift_injective_of_ker_le_ideal`

English:
theorem lift_injective_of_ker_le_ideal
  statement: (I : Ideal R) [I.IsTwoSided]
  proof: by
  rw [RingHom.injective_iff_ker_eq_bot]; rw [RingHom.ker_eq_bot_iff_eq_zero]
  intro u hu
  obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective u
  rw [Ideal.Quotient.lift_mk] at hu
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact hI (RingHom.mem_ker.mpr hu)

中文:
定理 lift_injective_of_ker_le_ideal
  结论: (I : 理想 R) [I.是TwoSided]
  证明: by
  rw [RingHom.injective_iff_ker_eq_bot]; rw [RingHom.ker_eq_bot_iff_eq_zero]
  intro u hu
  obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective u
  rw [Ideal.Quotient.lift_mk] at hu
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact hI (RingHom.mem_ker.mpr hu)

Depends on / 依赖: Ideal.Quotient.eq_zero_iff_mem, Ideal.Quotient.lift_mk, Ideal.Quotient.mk_surjective, Quotient, RingHom, RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_bot_iff_eq_zero, RingHom.mem_ker.mpr, eq_zero_iff_mem, injective_iff_ker_eq_bot, ker_eq_bot_iff_eq_zero, lift_mk, mem_ker, mk_surjective
-/
theorem lift_injective_of_ker_le_ideal (I : Ideal R) [I.IsTwoSided]
    {f : R ->+* S} (H : forall a : R, a in I -> f a = 0)
    (hI : ker f <= I) : Function.Injective (Ideal.Quotient.lift I f H) := by
  rw [RingHom.injective_iff_ker_eq_bot]; rw [RingHom.ker_eq_bot_iff_eq_zero]
  intro u hu
  obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective u
  rw [Ideal.Quotient.lift_mk] at hu
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact hI (RingHom.mem_ker.mpr hu)

/--
theorem `kerLift_injective` / 定理 `kerLift_injective`

English:
theorem kerLift_injective
  statement: Function.Injective (kerLift f)
  proof: lift_injective_of_ker_le_ideal (ker f) (fun a => by simp only [mem_ker, imp_self]) le_rfl

中文:
定理 kerLift_injective
  结论: 函数.单射 (kerLift f)
  证明: lift_injective_of_ker_le_ideal (ker f) (fun a => by simp only [mem_ker, imp_self]) le_rfl

Depends on / 依赖: imp_self, le_rfl, lift_injective_of_ker_le_ideal, mem_ker
-/
theorem kerLift_injective : Function.Injective (kerLift f) :=
  lift_injective_of_ker_le_ideal (ker f) (fun a => by simp only [mem_ker, imp_self]) le_rfl


variable {f}

/--
Definition of `quotientKerEquivOfRightInverse` / `quotientKerEquivOfRightInverse` 的定义

English:
definition quotientKerEquivOfRightInverse
  signature: {g : S -> R} (hf : Function.RightInverse g f)
  body: { kerLift f with
    toFun := kerLift f
    invFun := Ideal.Quotient.mk (ker f) ∘ g
    left_inv := by
      rintro ⟨x⟩
      apply kerLift_injective
      simp only [Submodule.Quotient.quot_mk_eq_mk, Ideal.Quotient.mk_eq_mk, kerLift_mk,
        Function.comp_apply, hf (f x)]
    right_inv := hf }



中文:
定义 quotientKerEquivOfRightInverse
  签名: {g : S -> R} (hf : 函数.右逆 g f)
  定义体: { kerLift f with
    toFun := kerLift f
    invFun := Ideal.Quotient.mk (ker f) ∘ g
    left_inv := by
      rintro ⟨x⟩
      apply kerLift_injective
      simp only [Submodule.Quotient.quot_mk_eq_mk, Ideal.Quotient.mk_eq_mk, kerLift_mk,
        Function.comp_apply, hf (f x)]
    right_inv := hf }



Depends on / 依赖: Function, Function.comp_apply, Ideal.Quotient.mk, Ideal.Quotient.mk_eq_mk, Quotient, Submodule, Submodule.Quotient.quot_mk_eq_mk, comp_apply, invFun, kerLift, kerLift_injective, kerLift_mk, left_inv, mk_eq_mk, quot_mk_eq_mk, right_inv
-/
def quotientKerEquivOfRightInverse {g : S -> R} (hf : Function.RightInverse g f) :
    R ⧸ ker f ≃+* S :=
  { kerLift f with
    toFun := kerLift f
    invFun := Ideal.Quotient.mk (ker f) ∘ g
    left_inv := by
      rintro ⟨x⟩
      apply kerLift_injective
      simp only [Submodule.Quotient.quot_mk_eq_mk, Ideal.Quotient.mk_eq_mk, kerLift_mk,
        Function.comp_apply, hf (f x)]
    right_inv := hf }

@[simp]
/--
theorem `quotientKerEquivOfRightInverse.apply` / 定理 `quotientKerEquivOfRightInverse.apply`

English:
theorem quotientKerEquivOfRightInverse.apply
  statement: {g : S -> R} (hf : Function.RightInverse g f)
  proof: rfl

@[simp]

中文:
定理 quotientKerEquivOfRightInverse.apply
  结论: {g : S -> R} (hf : 函数.右逆 g f)
  证明: rfl

@[simp]
-/
theorem quotientKerEquivOfRightInverse.apply {g : S -> R} (hf : Function.RightInverse g f)
    (x : R ⧸ ker f) : quotientKerEquivOfRightInverse hf x = kerLift f x :=
  rfl

@[simp]
/--
theorem `quotientKerEquivOfRightInverse.Symm.apply` / 定理 `quotientKerEquivOfRightInverse.Symm.apply`

English:
theorem quotientKerEquivOfRightInverse.Symm.apply
  statement: {g : S -> R} (hf : Function.RightInverse g f)
  proof: rfl

中文:
定理 quotientKerEquivOfRightInverse.Symm.apply
  结论: {g : S -> R} (hf : 函数.右逆 g f)
  证明: rfl
-/
theorem quotientKerEquivOfRightInverse.Symm.apply {g : S -> R} (hf : Function.RightInverse g f)
    (x : S) : (quotientKerEquivOfRightInverse hf).symm x = Ideal.Quotient.mk (ker f) (g x) :=
  rfl

/--
Definition of `quotientKerEquivOfSurjective` / `quotientKerEquivOfSurjective` 的定义

English:
definition quotientKerEquivOfSurjective
  signature: (hf : Function.Surjective f)
  body: quotientKerEquivOfRightInverse (Classical.choose_spec hf.hasRightInverse)

@[simp]

中文:
定义 quotientKerEquivOfSurjective
  签名: (hf : 函数.满射 f)
  定义体: quotientKerEquivOfRightInverse (Classical.choose_spec hf.hasRightInverse)

@[simp]

Depends on / 依赖: Classical, Classical.choose_spec, choose_spec, hasRightInverse, hf.hasRightInverse, quotientKerEquivOfRightInverse
-/
noncomputable def quotientKerEquivOfSurjective (hf : Function.Surjective f) : R ⧸ (ker f) ≃+* S :=
  quotientKerEquivOfRightInverse (Classical.choose_spec hf.hasRightInverse)

@[simp]
/--
lemma `quotientKerEquivOfSurjective_apply_mk` / 引理 `quotientKerEquivOfSurjective_apply_mk`

English:
lemma quotientKerEquivOfSurjective_apply_mk
  given: {f : R ->+* S} (hf : Function.Surjective f) (x : R)
  proof: rfl

@[simp]

中文:
引理 quotientKerEquivOfSurjective_apply_mk
  条件: {f : R ->+* S} (hf : 函数.满射 f) (x : R)
  证明: rfl

@[simp]
-/
lemma quotientKerEquivOfSurjective_apply_mk {f : R ->+* S} (hf : Function.Surjective f) (x : R) :
    f.quotientKerEquivOfSurjective hf (Ideal.Quotient.mk _ x) = f x :=
  rfl

@[simp]
/--
lemma `quotientKerEquivOfSurjective_symm_apply` / 引理 `quotientKerEquivOfSurjective_symm_apply`

English:
lemma quotientKerEquivOfSurjective_symm_apply
  given: {f : R ->+* S} (hf : Function.Surjective f) (x : R)
  proof: by
  apply (RingHom.quotientKerEquivOfSurjective hf).injective
  simp

中文:
引理 quotientKerEquivOfSurjective_symm_apply
  条件: {f : R ->+* S} (hf : 函数.满射 f) (x : R)
  证明: by
  apply (RingHom.quotientKerEquivOfSurjective hf).injective
  simp

Depends on / 依赖: RingHom, RingHom.quotientKerEquivOfSurjective, injective, quotientKerEquivOfSurjective
-/
lemma quotientKerEquivOfSurjective_symm_apply {f : R ->+* S} (hf : Function.Surjective f) (x : R) :
    (RingHom.quotientKerEquivOfSurjective hf).symm (f x) = Ideal.Quotient.mk _ x := by
  apply (RingHom.quotientKerEquivOfSurjective hf).injective
  simp

/--
lemma `quotientKerEquivOfSurjective_symm_comp` / 引理 `quotientKerEquivOfSurjective_symm_comp`

English:
lemma quotientKerEquivOfSurjective_symm_comp
  given: {f : R ->+* S} (hf : Function.Surjective f)
  proof: by
  ext; simp

中文:
引理 quotientKerEquivOfSurjective_symm_comp
  条件: {f : R ->+* S} (hf : 函数.满射 f)
  证明: by
  ext; simp
-/
lemma quotientKerEquivOfSurjective_symm_comp {f : R ->+* S} (hf : Function.Surjective f) :
    (RingHom.quotientKerEquivOfSurjective hf).symm.toRingHom.comp f = Ideal.Quotient.mk _ := by
  ext; simp

/--
Definition of `quotientKerEquivRangeS` / `quotientKerEquivRangeS` 的定义

English:
definition quotientKerEquivRangeS
  signature: (f : R ->+* S)
  body: (Ideal.quotEquivOfEq f.ker_rangeSRestrict.symm).trans
  quotientKerEquivOfSurjective f.rangeSRestrict_surjective

中文:
定义 quotientKerEquivRangeS
  签名: (f : R ->+* S)
  定义体: (Ideal.quotEquivOfEq f.ker_rangeSRestrict.symm).trans
  quotientKerEquivOfSurjective f.rangeSRestrict_surjective

Depends on / 依赖: Ideal.quotEquivOfEq, f.ker_rangeSRestrict.symm, f.rangeSRestrict_surjective, ker_rangeSRestrict, quotEquivOfEq, quotientKerEquivOfSurjective, rangeSRestrict_surjective
-/
noncomputable def quotientKerEquivRangeS (f : R ->+* S) : R ⧸ ker f ≃+* f.rangeS :=
(Ideal.quotEquivOfEq f.ker_rangeSRestrict.symm).trans
  quotientKerEquivOfSurjective f.rangeSRestrict_surjective

variable {S : Type v} [Ring S] (f : R ->+* S)

/--
Definition of `quotientKerEquivRange` / `quotientKerEquivRange` 的定义

English:
definition quotientKerEquivRange
  signature: (f : R ->+* S)
  body: (Ideal.quotEquivOfEq f.ker_rangeRestrict.symm).trans
    quotientKerEquivOfSurjective f.rangeRestrict_surjective

中文:
定义 quotientKerEquivRange
  签名: (f : R ->+* S)
  定义体: (Ideal.quotEquivOfEq f.ker_rangeRestrict.symm).trans
    quotientKerEquivOfSurjective f.rangeRestrict_surjective

Depends on / 依赖: Ideal.quotEquivOfEq, f.ker_rangeRestrict.symm, f.rangeRestrict_surjective, ker_rangeRestrict, quotEquivOfEq, quotientKerEquivOfSurjective, rangeRestrict_surjective
-/
noncomputable def quotientKerEquivRange (f : R ->+* S) : R ⧸ ker f ≃+* f.range :=
(Ideal.quotEquivOfEq f.ker_rangeRestrict.symm).trans
    quotientKerEquivOfSurjective f.rangeRestrict_surjective

end RingHom

namespace Ideal
open Function RingHom

variable {R : Type u} {S : Type v} {F : Type w} [Ring R] [Semiring S]

@[simp]
/--
theorem `map_quotient_self` / 定理 `map_quotient_self`

English:
theorem map_quotient_self
  given: (I : Ideal R) [I.IsTwoSided]
  statement: map (Quotient.mk I) I = ⊥
  proof: eq_bot_iff.2
    Ideal.map_le_iff_le_comap.2 fun _ hx =>
(Submodule.mem_bot (R ⧸ I)).2 Ideal.Quotient.eq_zero_iff_mem.2 hx

@[simp]

中文:
定理 map_quotient_self
  条件: (I : 理想 R) [I.是TwoSided]
  结论: map (商.mk I) I = ⊥
  证明: eq_bot_iff.2
    Ideal.map_le_iff_le_comap.2 fun _ hx =>
(Submodule.mem_bot (R ⧸ I)).2 Ideal.Quotient.eq_zero_iff_mem.2 hx

@[simp]

Depends on / 依赖: Ideal.Quotient.eq_zero_iff_mem, Ideal.map_le_iff_le_comap, Quotient, Submodule, Submodule.mem_bot, eq_bot_iff, eq_zero_iff_mem, map_le_iff_le_comap, mem_bot
-/
theorem map_quotient_self (I : Ideal R) [I.IsTwoSided] : map (Quotient.mk I) I = ⊥ :=
eq_bot_iff.2
    Ideal.map_le_iff_le_comap.2 fun _ hx =>
(Submodule.mem_bot (R ⧸ I)).2 Ideal.Quotient.eq_zero_iff_mem.2 hx

@[simp]
/--
theorem `mk_ker` / 定理 `mk_ker`

English:
theorem mk_ker
  given: {I : Ideal R} [I.IsTwoSided]
  statement: ker (Quotient.mk I) = I
  proof: by
  ext
  rw [ker]; rw [mem_comap]; rw [Submodule.mem_bot]; rw [Quotient.eq_zero_iff_mem]

中文:
定理 mk_ker
  条件: {I : 理想 R} [I.是TwoSided]
  结论: ker (商.mk I) = I
  证明: by
  ext
  rw [ker]; rw [mem_comap]; rw [Submodule.mem_bot]; rw [Quotient.eq_zero_iff_mem]

Depends on / 依赖: Quotient, Quotient.eq_zero_iff_mem, Submodule, Submodule.mem_bot, eq_zero_iff_mem, mem_bot, mem_comap
-/
theorem mk_ker {I : Ideal R} [I.IsTwoSided] : ker (Quotient.mk I) = I := by
  ext
  rw [ker]; rw [mem_comap]; rw [Submodule.mem_bot]; rw [Quotient.eq_zero_iff_mem]

/--
theorem `map_mk_eq_bot_of_le` / 定理 `map_mk_eq_bot_of_le`

English:
theorem map_mk_eq_bot_of_le
  given: {I J : Ideal R} [J.IsTwoSided] (h : I <= J)
  proof: by
  rw [map_eq_bot_iff_le_ker]; rw [mk_ker]
  exact h

中文:
定理 map_mk_eq_bot_of_le
  条件: {I J : 理想 R} [J.是TwoSided] (h : I <= J)
  证明: by
  rw [map_eq_bot_iff_le_ker]; rw [mk_ker]
  exact h

Depends on / 依赖: map_eq_bot_iff_le_ker, mk_ker
-/
theorem map_mk_eq_bot_of_le {I J : Ideal R} [J.IsTwoSided] (h : I <= J) :
    I.map (Quotient.mk J) = ⊥ := by
  rw [map_eq_bot_iff_le_ker]; rw [mk_ker]
  exact h

set_option backward.isDefEq.respectTransparency false in
/--
theorem `ker_quotient_lift` / 定理 `ker_quotient_lift`

English:
theorem ker_quotient_lift
  statement: {I : Ideal R} [I.IsTwoSided] (f : R ->+* S)
  proof: by
  apply Ideal.ext
  intro x
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := Quotient.mk_surjective x
    rw [mem_ker]; rw [← hy]; rw [Ideal.Quotient.lift_mk]; rw [← mem_ker] at hx
    rw [← hy]; rw [mem_map_iff_of_surjective (Quotient.mk I) Quotient.mk_surjective]
    exact ⟨y, hx, rfl⟩
  · intr

中文:
定理 ker_quotient_lift
  结论: {I : 理想 R} [I.是TwoSided] (f : R ->+* S)
  证明: by
  apply Ideal.ext
  intro x
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := Quotient.mk_surjective x
    rw [mem_ker]; rw [← hy]; rw [Ideal.Quotient.lift_mk]; rw [← mem_ker] at hx
    rw [← hy]; rw [mem_map_iff_of_surjective (Quotient.mk I) Quotient.mk_surjective]
    exact ⟨y, hx, rfl⟩
  · intr

Depends on / 依赖: Ideal.Quotient.lift_mk, Ideal.ext, Quotient, Quotient.mk, Quotient.mk_surjective, hy.left, hy.right, lift_mk, mem_ker, mem_map_iff_of_surjective, mk_surjective
-/
theorem ker_quotient_lift {I : Ideal R} [I.IsTwoSided] (f : R ->+* S)
    (H : I <= ker f) :
    ker (Ideal.Quotient.lift I f H) = (RingHom.ker f).map (Quotient.mk I) := by
  apply Ideal.ext
  intro x
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := Quotient.mk_surjective x
    rw [mem_ker]; rw [← hy]; rw [Ideal.Quotient.lift_mk]; rw [← mem_ker] at hx
    rw [← hy]; rw [mem_map_iff_of_surjective (Quotient.mk I) Quotient.mk_surjective]
    exact ⟨y, hx, rfl⟩
  · intro hx
    rw [mem_map_iff_of_surjective (Quotient.mk I) Quotient.mk_surjective] at hx
    obtain ⟨y, hy⟩ := hx
    rw [mem_ker]; rw [← hy.right]; rw [Ideal.Quotient.lift_mk]
    exact hy.left

set_option backward.isDefEq.respectTransparency false in
/--
lemma `injective_lift_iff` / 引理 `injective_lift_iff`

English:
lemma injective_lift_iff
  statement: {I : Ideal R} [I.IsTwoSided]
  proof: by
  rw [injective_iff_ker_eq_bot]; rw [ker_quotient_lift]; rw [map_eq_bot_iff_le_ker]; rw [mk_ker]
  constructor
  · exact fun h => le_antisymm h H
  · rintro rfl; rfl

中文:
引理 injective_lift_iff
  结论: {I : 理想 R} [I.是TwoSided]
  证明: by
  rw [injective_iff_ker_eq_bot]; rw [ker_quotient_lift]; rw [map_eq_bot_iff_le_ker]; rw [mk_ker]
  constructor
  · exact fun h => le_antisymm h H
  · rintro rfl; rfl

Depends on / 依赖: injective_iff_ker_eq_bot, ker_quotient_lift, le_antisymm, map_eq_bot_iff_le_ker, mk_ker
-/
lemma injective_lift_iff {I : Ideal R} [I.IsTwoSided]
    {f : R ->+* S} (H : forall (a : R), a in I -> f a = 0) :
    Injective (Quotient.lift I f H) ↔ ker f = I := by
  rw [injective_iff_ker_eq_bot]; rw [ker_quotient_lift]; rw [map_eq_bot_iff_le_ker]; rw [mk_ker]
  constructor
  · exact fun h => le_antisymm h H
  · rintro rfl; rfl

/--
lemma `ker_Pi_Quotient_mk` / 引理 `ker_Pi_Quotient_mk`

English:
lemma ker_Pi_Quotient_mk
  given: {ι : Type*} (I : ι -> Ideal R) [forall i, (I i).IsTwoSided]
  proof: by
  simp [Pi.ker_ringHom, mk_ker]

@[simp]

中文:
引理 ker_Pi_Quotient_mk
  条件: {ι : 类型} (I : ι -> 理想 R) [对任意 i, (I i).是TwoSided]
  证明: by
  simp [Pi.ker_ringHom, mk_ker]

@[simp]

Depends on / 依赖: Pi.ker_ringHom, ker_ringHom, mk_ker
-/
lemma ker_Pi_Quotient_mk {ι : Type*} (I : ι -> Ideal R) [forall i, (I i).IsTwoSided] :
    ker (RingHom.pi fun i : ι => Quotient.mk (I i)) = ⨅ i, I i := by
  simp [Pi.ker_ringHom, mk_ker]

@[simp]
/--
theorem `bot_quotient_isMaximal_iff` / 定理 `bot_quotient_isMaximal_iff`

English:
theorem bot_quotient_isMaximal_iff
  given: (I : Ideal R) [I.IsTwoSided]
  proof: ⟨fun hI =>
    mk_ker (I := I) ▸
      comap_isMaximal_of_surjective (Quotient.mk I) Quotient.mk_surjective (K := ⊥) (H := hI),
    fun hI => by
    let := Quotient.divisionRing I
    exact bot_isMaximal⟩

中文:
定理 bot_quotient_isMaximal_iff
  条件: (I : 理想 R) [I.是TwoSided]
  证明: ⟨fun hI =>
    mk_ker (I := I) ▸
      comap_isMaximal_of_surjective (Quotient.mk I) Quotient.mk_surjective (K := ⊥) (H := hI),
    fun hI => by
    let := Quotient.divisionRing I
    exact bot_isMaximal⟩

Depends on / 依赖: Quotient, Quotient.divisionRing, Quotient.mk, Quotient.mk_surjective, bot_isMaximal, comap_isMaximal_of_surjective, divisionRing, mk_ker, mk_surjective
-/
theorem bot_quotient_isMaximal_iff (I : Ideal R) [I.IsTwoSided] :
    (⊥ : Ideal (R ⧸ I)).IsMaximal ↔ I.IsMaximal :=
  ⟨fun hI =>
    mk_ker (I := I) ▸
      comap_isMaximal_of_surjective (Quotient.mk I) Quotient.mk_surjective (K := ⊥) (H := hI),
    fun hI => by
    let := Quotient.divisionRing I
    exact bot_isMaximal⟩

/-- See also `Ideal.mem_quotient_iff_mem` in case `I ≤ J`. -/
@[simp]
/--
theorem `mem_quotient_iff_mem_sup` / 定理 `mem_quotient_iff_mem_sup`

English:
theorem mem_quotient_iff_mem_sup
  given: {I J : Ideal R} [I.IsTwoSided] {x : R}
  proof: by
  rw [← mem_comap]; rw [comap_map_of_surjective (Quotient.mk I) Quotient.mk_surjective]; rw [←
    ker_eq_comap_bot]; rw [mk_ker]

中文:
定理 mem_quotient_iff_mem_sup
  条件: {I J : 理想 R} [I.是TwoSided] {x : R}
  证明: by
  rw [← mem_comap]; rw [comap_map_of_surjective (Quotient.mk I) Quotient.mk_surjective]; rw [←
    ker_eq_comap_bot]; rw [mk_ker]

Depends on / 依赖: Quotient, Quotient.mk, Quotient.mk_surjective, comap_map_of_surjective, ker_eq_comap_bot, mem_comap, mk_ker, mk_surjective
-/
theorem mem_quotient_iff_mem_sup {I J : Ideal R} [I.IsTwoSided] {x : R} :
    Quotient.mk I x in J.map (Quotient.mk I) ↔ x in J ⊔ I := by
  rw [← mem_comap]; rw [comap_map_of_surjective (Quotient.mk I) Quotient.mk_surjective]; rw [←
    ker_eq_comap_bot]; rw [mk_ker]

/--
theorem `mem_quotient_iff_mem` / 定理 `mem_quotient_iff_mem`

English:
theorem mem_quotient_iff_mem
  given: {I J : Ideal R} [I.IsTwoSided] (hIJ : I <= J) {x : R}
  proof: by
  rw [mem_quotient_iff_mem_sup]; rw [sup_eq_left.mpr hIJ]

中文:
定理 mem_quotient_iff_mem
  条件: {I J : 理想 R} [I.是TwoSided] (hIJ : I <= J) {x : R}
  证明: by
  rw [mem_quotient_iff_mem_sup]; rw [sup_eq_left.mpr hIJ]

Depends on / 依赖: mem_quotient_iff_mem_sup, sup_eq_left, sup_eq_left.mpr
-/
theorem mem_quotient_iff_mem {I J : Ideal R} [I.IsTwoSided] (hIJ : I <= J) {x : R} :
    Quotient.mk I x in J.map (Quotient.mk I) ↔ x in J := by
  rw [mem_quotient_iff_mem_sup]; rw [sup_eq_left.mpr hIJ]

section ChineseRemainder
open Function Ideal.Quotient Finset

variable {ι : Type*}

/--
Definition of `quotientInfToPiQuotient` / `quotientInfToPiQuotient` 的定义

English:
definition quotientInfToPiQuotient
  signature: (I : ι -> Ideal R) [forall i, (I i).IsTwoSided]
  body: Quotient.lift (⨅ i, I i) (RingHom.pi fun i : ι => Quotient.mk (I i))
    (by simp [← RingHom.mem_ker, ker_Pi_Quotient_mk])

中文:
定义 quotientInfToPiQuotient
  签名: (I : ι -> 理想 R) [对任意 i, (I i).是TwoSided]
  定义体: Quotient.lift (⨅ i, I i) (RingHom.pi fun i : ι => Quotient.mk (I i))
    (by simp [← RingHom.mem_ker, ker_Pi_Quotient_mk])

Depends on / 依赖: Quotient, Quotient.lift, Quotient.mk, RingHom, RingHom.mem_ker, RingHom.pi, ker_Pi_Quotient_mk, mem_ker
-/
def quotientInfToPiQuotient (I : ι -> Ideal R) [forall i, (I i).IsTwoSided] :
    (R ⧸ ⨅ i, I i) ->+* forall i, R ⧸ I i :=
  Quotient.lift (⨅ i, I i) (RingHom.pi fun i : ι => Quotient.mk (I i))
    (by simp [← RingHom.mem_ker, ker_Pi_Quotient_mk])

/--
lemma `quotientInfToPiQuotient_mk` / 引理 `quotientInfToPiQuotient_mk`

English:
lemma quotientInfToPiQuotient_mk
  given: (I : ι -> Ideal R) [forall i, (I i).IsTwoSided] (x : R)
  proof: rfl

中文:
引理 quotientInfToPiQuotient_mk
  条件: (I : ι -> 理想 R) [对任意 i, (I i).是TwoSided] (x : R)
  证明: rfl
-/
lemma quotientInfToPiQuotient_mk (I : ι -> Ideal R) [forall i, (I i).IsTwoSided] (x : R) :
    quotientInfToPiQuotient I (Quotient.mk _ x) = fun i : ι => Quotient.mk (I i) x :=
  rfl

/--
lemma `quotientInfToPiQuotient_mk'` / 引理 `quotientInfToPiQuotient_mk'`

English:
lemma quotientInfToPiQuotient_mk'
  given: (I : ι -> Ideal R) [forall i, (I i).IsTwoSided] (x : R) (i : ι)
  proof: rfl

中文:
引理 quotientInfToPiQuotient_mk'
  条件: (I : ι -> 理想 R) [对任意 i, (I i).是TwoSided] (x : R) (i : ι)
  证明: rfl
-/
lemma quotientInfToPiQuotient_mk' (I : ι -> Ideal R) [forall i, (I i).IsTwoSided] (x : R) (i : ι) :
    quotientInfToPiQuotient I (Quotient.mk _ x) i = Quotient.mk (I i) x :=
  rfl

/--
lemma `quotientInfToPiQuotient_inj` / 引理 `quotientInfToPiQuotient_inj`

English:
lemma quotientInfToPiQuotient_inj
  given: (I : ι -> Ideal R) [forall i, (I i).IsTwoSided]
  proof: by
  rw [quotientInfToPiQuotient]; rw [injective_lift_iff]; rw [ker_Pi_Quotient_mk]

中文:
引理 quotientInfToPiQuotient_inj
  条件: (I : ι -> 理想 R) [对任意 i, (I i).是TwoSided]
  证明: by
  rw [quotientInfToPiQuotient]; rw [injective_lift_iff]; rw [ker_Pi_Quotient_mk]

Depends on / 依赖: injective_lift_iff, ker_Pi_Quotient_mk, quotientInfToPiQuotient
-/
lemma quotientInfToPiQuotient_inj (I : ι -> Ideal R) [forall i, (I i).IsTwoSided] :
    Injective (quotientInfToPiQuotient I) := by
  rw [quotientInfToPiQuotient]; rw [injective_lift_iff]; rw [ker_Pi_Quotient_mk]

variable {R : Type*} [CommRing R] {ι : Type*} [Finite ι]

/--
lemma `quotientInfToPiQuotient_surj` / 引理 `quotientInfToPiQuotient_surj`

English:
lemma quotientInfToPiQuotient_surj
  statement: {I : ι -> Ideal R}
  proof: by
  classical
  cases nonempty_fintype ι
  intro g
  choose f hf using fun i => mk_surjective (g i)
  have key : forall i, exists e : R, mk (I i) e = 1 ∧ forall j, j != i -> mk (I j) e = 0 := by
    intro i
    have hI' : forall j in ({i} : Finset ι)ᶜ, IsCoprime (I i) (I j) := by
      intro j hj
 

中文:
引理 quotientInfToPiQuotient_surj
  结论: {I : ι -> 理想 R}
  证明: by
  classical
  cases nonempty_fintype ι
  intro g
  choose f hf using fun i => mk_surjective (g i)
  have key : forall i, exists e : R, mk (I i) e = 1 ∧ forall j, j != i -> mk (I j) e = 0 := by
    intro i
    have hI' : forall j in ({i} : Finset ι)ᶜ, IsCoprime (I i) (I j) := by
      intro j hj
 

Depends on / 依赖: Finset, IsCoprime, classical, isCoprime_biInf, isCoprime_iff_add, isCoprime_iff_exists, isCoprime_iff_exists.mp, mk_surjective, ne_comm, nonempty_fintype, replace
-/
lemma quotientInfToPiQuotient_surj {I : ι -> Ideal R}
    (hI : Pairwise (IsCoprime on I)) : Surjective (quotientInfToPiQuotient I) := by
  classical
  cases nonempty_fintype ι
  intro g
  choose f hf using fun i => mk_surjective (g i)
  have key : forall i, exists e : R, mk (I i) e = 1 ∧ forall j, j != i -> mk (I j) e = 0 := by
    intro i
    have hI' : forall j in ({i} : Finset ι)ᶜ, IsCoprime (I i) (I j) := by
      intro j hj
      exact hI (by simpa [ne_comm, isCoprime_iff_add] using hj)
    rcases isCoprime_iff_exists.mp (isCoprime_biInf hI') with ⟨u, hu, e, he, hue⟩
    replace he : forall j, j != i -> e in I j := by simpa using he
    refine ⟨e, ?_, ?_⟩
    · simp [eq_sub_of_add_eq' hue, map_sub, eq_zero_iff_mem.mpr hu]
    · exact fun j hj => eq_zero_iff_mem.mpr (he j hj)
  choose e he using key
  use mk _ (∑ i, f i * e i)
  ext i
  rw [quotientInfToPiQuotient_mk']; rw [map_sum]; rw [Fintype.sum_eq_single i]
  · simp [(he i).1, hf]
  · intro j hj
    simp [(he j).2 i hj.symm]

/-- **Chinese Remainder Theorem**. Eisenbud Ex.2.6.
Similar to Atiyah-Macdonald 1.10 and Stacks 00DT -/
@[wikidata Q193878]
/--
Definition of `quotientInfRingEquivPiQuotient` / `quotientInfRingEquivPiQuotient` 的定义

English:
definition quotientInfRingEquivPiQuotient
  signature: (f : ι -> Ideal R)
  body: { Equiv.ofBijective _ ⟨quotientInfToPiQuotient_inj f, quotientInfToPiQuotient_surj hf⟩,
    quotientInfToPiQuotient f with }

中文:
定义 quotientInfRingEquivPiQuotient
  签名: (f : ι -> 理想 R)
  定义体: { Equiv.ofBijective _ ⟨quotientInfToPiQuotient_inj f, quotientInfToPiQuotient_surj hf⟩,
    quotientInfToPiQuotient f with }

Depends on / 依赖: Equiv.ofBijective, ofBijective, quotientInfToPiQuotient, quotientInfToPiQuotient_inj, quotientInfToPiQuotient_surj
-/
noncomputable def quotientInfRingEquivPiQuotient (f : ι -> Ideal R)
    (hf : Pairwise (IsCoprime on f)) : (R ⧸ ⨅ i, f i) ≃+* forall i, R ⧸ f i :=
  { Equiv.ofBijective _ ⟨quotientInfToPiQuotient_inj f, quotientInfToPiQuotient_surj hf⟩,
    quotientInfToPiQuotient f with }

/--
lemma `pi_quotient_surjective` / 引理 `pi_quotient_surjective`

English:
lemma pi_quotient_surjective
  statement: {I : ι -> Ideal R}
  proof: by
  obtain ⟨y, rfl⟩ := Ideal.quotientInfToPiQuotient_surj hf x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact ⟨r, fun i => rfl⟩

中文:
引理 pi_quotient_surjective
  结论: {I : ι -> 理想 R}
  证明: by
  obtain ⟨y, rfl⟩ := Ideal.quotientInfToPiQuotient_surj hf x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact ⟨r, fun i => rfl⟩

Depends on / 依赖: Ideal.Quotient.mk_surjective, Ideal.quotientInfToPiQuotient_surj, Quotient, mk_surjective, quotientInfToPiQuotient_surj
-/
lemma pi_quotient_surjective {I : ι -> Ideal R}
    (hf : Pairwise (IsCoprime on I)) (x : (i : ι) -> R ⧸ I i) :
    exists r : R, forall i, r = x i := by
  obtain ⟨y, rfl⟩ := Ideal.quotientInfToPiQuotient_surj hf x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact ⟨r, fun i => rfl⟩

/--
lemma `pi_mkQ_surjective` / 引理 `pi_mkQ_surjective`

English:
lemma pi_mkQ_surjective
  given: {I : ι -> Ideal R} (hI : Pairwise (IsCoprime on I))
  proof: fun x => have ⟨r, eq⟩ := pi_quotient_surjective hI x; ⟨r, funext eq⟩

中文:
引理 pi_mkQ_surjective
  条件: {I : ι -> 理想 R} (hI : 两两 (IsCoprime on I))
  证明: fun x => have ⟨r, eq⟩ := pi_quotient_surjective hI x; ⟨r, funext eq⟩

Depends on / 依赖: pi_quotient_surjective
-/
lemma pi_mkQ_surjective {I : ι -> Ideal R} (hI : Pairwise (IsCoprime on I)) :
    Surjective (LinearMap.pi fun i => (I i).mkQ) :=
  fun x => have ⟨r, eq⟩ := pi_quotient_surjective hI x; ⟨r, funext eq⟩

-- variant of `IsDedekindDomain.exists_forall_sub_mem_ideal` which doesn't assume Dedekind domain!
/--
lemma `exists_forall_sub_mem_ideal` / 引理 `exists_forall_sub_mem_ideal`

English:
lemma exists_forall_sub_mem_ideal
  proof: by
  obtain ⟨y, hy⟩ := Ideal.pi_quotient_surjective hI (fun i => x i)
exact ⟨y, fun i => (Submodule.Quotient.eq (I i)).mp hy i⟩

中文:
引理 存在_对任意_sub_mem_ideal
  证明: by
  obtain ⟨y, hy⟩ := Ideal.pi_quotient_surjective hI (fun i => x i)
exact ⟨y, fun i => (Submodule.Quotient.eq (I i)).mp hy i⟩

Depends on / 依赖: Ideal.pi_quotient_surjective, Quotient, Submodule, Submodule.Quotient.eq, pi_quotient_surjective
-/
lemma exists_forall_sub_mem_ideal
    {I : ι -> Ideal R} (hI : Pairwise (IsCoprime on I)) (x : ι -> R) :
    exists r : R, forall i, r - x i in I i := by
  obtain ⟨y, hy⟩ := Ideal.pi_quotient_surjective hI (fun i => x i)
exact ⟨y, fun i => (Submodule.Quotient.eq (I i)).mp hy i⟩

/--
Definition of `quotientInfEquivQuotientProd` / `quotientInfEquivQuotientProd` 的定义

English:
definition quotientInfEquivQuotientProd
  signature: (I J : Ideal R) (coprime : IsCoprime I J)
  body: let f : Fin 2 -> Ideal R := ![I, J]
  have hf : Pairwise (IsCoprime on f) := by
    intro i j h
    fin_cases i <;> fin_cases j <;> try contradiction
    · assumption
    · exact coprime.symm
(Ideal.quotEquivOfEq (by simp [f, iInf, inf_comm])).trans
(Ideal.quotientInfRingEquivPiQuotient f hf).trans 

中文:
定义 quotientInfEquivQuotientProd
  签名: (I J : 理想 R) (coprime : IsCoprime I J)
  定义体: let f : Fin 2 -> Ideal R := ![I, J]
  have hf : Pairwise (IsCoprime on f) := by
    intro i j h
    fin_cases i <;> fin_cases j <;> try contradiction
    · assumption
    · exact coprime.symm
(Ideal.quotEquivOfEq (by simp [f, iInf, inf_comm])).trans
(Ideal.quotientInfRingEquivPiQuotient f hf).trans 

Depends on / 依赖: Ideal.quotEquivOfEq, Ideal.quotientInfRingEquivPiQuotient, IsCoprime, Pairwise, RingEquiv, RingEquiv.piFinTwo, coprime, coprime.symm, fin_cases, inf_comm, piFinTwo, quotEquivOfEq, quotientInfRingEquivPiQuotient
-/
noncomputable def quotientInfEquivQuotientProd (I J : Ideal R) (coprime : IsCoprime I J) :
    R ⧸ I ⊓ J ≃+* (R ⧸ I) × R ⧸ J :=
  let f : Fin 2 -> Ideal R := ![I, J]
  have hf : Pairwise (IsCoprime on f) := by
    intro i j h
    fin_cases i <;> fin_cases j <;> try contradiction
    · assumption
    · exact coprime.symm
(Ideal.quotEquivOfEq (by simp [f, iInf, inf_comm])).trans
(Ideal.quotientInfRingEquivPiQuotient f hf).trans RingEquiv.piFinTwo fun i => R ⧸ f i

@[simp]
/--
theorem `quotientInfEquivQuotientProd_fst` / 定理 `quotientInfEquivQuotientProd_fst`

English:
theorem quotientInfEquivQuotientProd_fst
  given: (I J : Ideal R) (coprime : IsCoprime I J) (x : R ⧸ I ⊓ J)
  proof: Quot.inductionOn x fun _ => rfl

@[simp]

中文:
定理 quotientInfEquivQuotientProd_fst
  条件: (I J : 理想 R) (coprime : IsCoprime I J) (x : R ⧸ I ⊓ J)
  证明: Quot.inductionOn x fun _ => rfl

@[simp]

Depends on / 依赖: Quot.inductionOn, inductionOn
-/
theorem quotientInfEquivQuotientProd_fst (I J : Ideal R) (coprime : IsCoprime I J) (x : R ⧸ I ⊓ J) :
    (quotientInfEquivQuotientProd I J coprime x).fst =
      Ideal.Quotient.factor inf_le_left x :=
  Quot.inductionOn x fun _ => rfl

@[simp]
/--
theorem `quotientInfEquivQuotientProd_snd` / 定理 `quotientInfEquivQuotientProd_snd`

English:
theorem quotientInfEquivQuotientProd_snd
  given: (I J : Ideal R) (coprime : IsCoprime I J) (x : R ⧸ I ⊓ J)
  proof: Quot.inductionOn x fun _ => rfl

@[simp]

中文:
定理 quotientInfEquivQuotientProd_snd
  条件: (I J : 理想 R) (coprime : IsCoprime I J) (x : R ⧸ I ⊓ J)
  证明: Quot.inductionOn x fun _ => rfl

@[simp]

Depends on / 依赖: Quot.inductionOn, inductionOn
-/
theorem quotientInfEquivQuotientProd_snd (I J : Ideal R) (coprime : IsCoprime I J) (x : R ⧸ I ⊓ J) :
    (quotientInfEquivQuotientProd I J coprime x).snd =
      Ideal.Quotient.factor inf_le_right x :=
  Quot.inductionOn x fun _ => rfl

@[simp]
/--
theorem `fst_comp_quotientInfEquivQuotientProd` / 定理 `fst_comp_quotientInfEquivQuotientProd`

English:
theorem fst_comp_quotientInfEquivQuotientProd
  given: (I J : Ideal R) (coprime : IsCoprime I J)
  proof: by
  apply Quotient.ringHom_ext; ext; rfl

@[simp]

中文:
定理 fst_comp_quotientInfEquivQuotientProd
  条件: (I J : 理想 R) (coprime : IsCoprime I J)
  证明: by
  apply Quotient.ringHom_ext; ext; rfl

@[simp]

Depends on / 依赖: Quotient, Quotient.ringHom_ext, ringHom_ext
-/
theorem fst_comp_quotientInfEquivQuotientProd (I J : Ideal R) (coprime : IsCoprime I J) :
    (RingHom.fst _ _).comp
        (quotientInfEquivQuotientProd I J coprime : R ⧸ I ⊓ J ->+* (R ⧸ I) × R ⧸ J) =
      Ideal.Quotient.factor inf_le_left := by
  apply Quotient.ringHom_ext; ext; rfl

@[simp]
/--
theorem `snd_comp_quotientInfEquivQuotientProd` / 定理 `snd_comp_quotientInfEquivQuotientProd`

English:
theorem snd_comp_quotientInfEquivQuotientProd
  given: (I J : Ideal R) (coprime : IsCoprime I J)
  proof: by
  apply Quotient.ringHom_ext; ext; rfl

中文:
定理 snd_comp_quotientInfEquivQuotientProd
  条件: (I J : 理想 R) (coprime : IsCoprime I J)
  证明: by
  apply Quotient.ringHom_ext; ext; rfl

Depends on / 依赖: Quotient, Quotient.ringHom_ext, ringHom_ext
-/
theorem snd_comp_quotientInfEquivQuotientProd (I J : Ideal R) (coprime : IsCoprime I J) :
    (RingHom.snd _ _).comp
        (quotientInfEquivQuotientProd I J coprime : R ⧸ I ⊓ J ->+* (R ⧸ I) × R ⧸ J) =
      Ideal.Quotient.factor inf_le_right := by
  apply Quotient.ringHom_ext; ext; rfl

/--
Definition of `quotientMulEquivQuotientProd` / `quotientMulEquivQuotientProd` 的定义

English:
definition quotientMulEquivQuotientProd
  signature: (I J : Ideal R) (coprime : IsCoprime I J)
  body: .trans Ideal.quotEquivOfEq (mul_eq_inf_of_isCoprime coprime)
    Ideal.quotientInfEquivQuotientProd I J coprime

@[simp]

中文:
定义 quotientMulEquivQuotientProd
  签名: (I J : 理想 R) (coprime : IsCoprime I J)
  定义体: .trans Ideal.quotEquivOfEq (mul_eq_inf_of_isCoprime coprime)
    Ideal.quotientInfEquivQuotientProd I J coprime

@[simp]

Depends on / 依赖: Ideal.quotEquivOfEq, Ideal.quotientInfEquivQuotientProd, coprime, mul_eq_inf_of_isCoprime, quotEquivOfEq, quotientInfEquivQuotientProd
-/
noncomputable def quotientMulEquivQuotientProd (I J : Ideal R) (coprime : IsCoprime I J) :
    R ⧸ I * J ≃+* (R ⧸ I) × R ⧸ J :=
.trans Ideal.quotEquivOfEq (mul_eq_inf_of_isCoprime coprime)
    Ideal.quotientInfEquivQuotientProd I J coprime

@[simp]
/--
theorem `quotientMulEquivQuotientProd_fst` / 定理 `quotientMulEquivQuotientProd_fst`

English:
theorem quotientMulEquivQuotientProd_fst
  given: (I J : Ideal R) (coprime : IsCoprime I J) (x : R ⧸ I * J)
  proof: Quot.inductionOn x fun _ => rfl

@[simp]

中文:
定理 quotientMulEquivQuotientProd_fst
  条件: (I J : 理想 R) (coprime : IsCoprime I J) (x : R ⧸ I * J)
  证明: Quot.inductionOn x fun _ => rfl

@[simp]

Depends on / 依赖: Quot.inductionOn, inductionOn
-/
theorem quotientMulEquivQuotientProd_fst (I J : Ideal R) (coprime : IsCoprime I J) (x : R ⧸ I * J) :
    (quotientMulEquivQuotientProd I J coprime x).fst =
      Ideal.Quotient.factor mul_le_left x :=
  Quot.inductionOn x fun _ => rfl

@[simp]
/--
theorem `quotientMulEquivQuotientProd_snd` / 定理 `quotientMulEquivQuotientProd_snd`

English:
theorem quotientMulEquivQuotientProd_snd
  given: (I J : Ideal R) (coprime : IsCoprime I J) (x : R ⧸ I * J)
  proof: Quot.inductionOn x fun _ => rfl

@[simp]

中文:
定理 quotientMulEquivQuotientProd_snd
  条件: (I J : 理想 R) (coprime : IsCoprime I J) (x : R ⧸ I * J)
  证明: Quot.inductionOn x fun _ => rfl

@[simp]

Depends on / 依赖: Quot.inductionOn, inductionOn
-/
theorem quotientMulEquivQuotientProd_snd (I J : Ideal R) (coprime : IsCoprime I J) (x : R ⧸ I * J) :
    (quotientMulEquivQuotientProd I J coprime x).snd =
      Ideal.Quotient.factor mul_le_right x :=
  Quot.inductionOn x fun _ => rfl

@[simp]
/--
theorem `fst_comp_quotientMulEquivQuotientProd` / 定理 `fst_comp_quotientMulEquivQuotientProd`

English:
theorem fst_comp_quotientMulEquivQuotientProd
  given: (I J : Ideal R) (coprime : IsCoprime I J)
  proof: by
  apply Quotient.ringHom_ext; ext; rfl

@[simp]

中文:
定理 fst_comp_quotientMulEquivQuotientProd
  条件: (I J : 理想 R) (coprime : IsCoprime I J)
  证明: by
  apply Quotient.ringHom_ext; ext; rfl

@[simp]

Depends on / 依赖: Quotient, Quotient.ringHom_ext, ringHom_ext
-/
theorem fst_comp_quotientMulEquivQuotientProd (I J : Ideal R) (coprime : IsCoprime I J) :
    (RingHom.fst _ _).comp
        (quotientMulEquivQuotientProd I J coprime : R ⧸ I * J ->+* (R ⧸ I) × R ⧸ J) =
      Ideal.Quotient.factor mul_le_left := by
  apply Quotient.ringHom_ext; ext; rfl

@[simp]
/--
theorem `snd_comp_quotientMulEquivQuotientProd` / 定理 `snd_comp_quotientMulEquivQuotientProd`

English:
theorem snd_comp_quotientMulEquivQuotientProd
  given: (I J : Ideal R) (coprime : IsCoprime I J)
  proof: by
  apply Quotient.ringHom_ext; ext; rfl

中文:
定理 snd_comp_quotientMulEquivQuotientProd
  条件: (I J : 理想 R) (coprime : IsCoprime I J)
  证明: by
  apply Quotient.ringHom_ext; ext; rfl

Depends on / 依赖: Quotient, Quotient.ringHom_ext, ringHom_ext
-/
theorem snd_comp_quotientMulEquivQuotientProd (I J : Ideal R) (coprime : IsCoprime I J) :
    (RingHom.snd _ _).comp
        (quotientMulEquivQuotientProd I J coprime : R ⧸ I * J ->+* (R ⧸ I) × R ⧸ J) =
      Ideal.Quotient.factor mul_le_right := by
  apply Quotient.ringHom_ext; ext; rfl

end ChineseRemainder

section QuotientAlgebra

variable (R₁ R₂ : Type*) {A B : Type*}
variable [CommSemiring R₁] [CommSemiring R₂] [Ring A]
variable [Algebra R₁ A] [Algebra R₂ A]

/--
Instance `Quotient.algebra` / 实例 `Quotient.algebra`

English:
instance Quotient.algebra
  signature: {I : Ideal A} [I.IsTwoSided]
  body: (Ideal.Quotient.mk I).comp (algebraMap R₁ A)
  smul_def' := fun _ x =>
    Quotient.inductionOn' x fun _ =>
      ((Quotient.mk I).congr_arg <| Algebra.smul_def _ _).trans (map_mul _ _ _)
  commutes' := by rintro r ⟨x⟩; exact congr_arg (⟦·⟧) (Algebra.commutes r x)

中文:
实例 商.algebra
  签名: {I : 理想 A} [I.是TwoSided]
  定义体: (Ideal.Quotient.mk I).comp (algebraMap R₁ A)
  smul_def' := fun _ x =>
    Quotient.inductionOn' x fun _ =>
      ((Quotient.mk I).congr_arg <| Algebra.smul_def _ _).trans (map_mul _ _ _)
  commutes' := by rintro r ⟨x⟩; exact congr_arg (⟦·⟧) (Algebra.commutes r x)

Depends on / 依赖: Ideal.Quotient.mk, Quotient, algebraMap
-/
instance Quotient.algebra {I : Ideal A} [I.IsTwoSided] : Algebra R₁ (A ⧸ I) where
  algebraMap := (Ideal.Quotient.mk I).comp (algebraMap R₁ A)
  smul_def' := fun _ x =>
    Quotient.inductionOn' x fun _ =>
      ((Quotient.mk I).congr_arg <| Algebra.smul_def _ _).trans (map_mul _ _ _)
  commutes' := by rintro r ⟨x⟩; exact congr_arg (⟦·⟧) (Algebra.commutes r x)

instance {A} [CommRing A] [Algebra R₁ A] (I : Ideal A) : Algebra R₁ (A ⧸ I) := inferInstance

-- This instance can be inferred, but is kept around as a useful shortcut.
/--
Instance `Quotient.isScalarTower` / 实例 `Quotient.isScalarTower`

English:
instance Quotient.isScalarTower
  signature: [SMul R₁ R₂] [IsScalarTower R₁ R₂ A] (I : Ideal A)
  body: inferInstance

中文:
实例 商.isScalarTower
  签名: [标量乘法 R₁ R₂] [标量塔 R₁ R₂ A] (I : 理想 A)
  定义体: inferInstance
-/
instance Quotient.isScalarTower [SMul R₁ R₂] [IsScalarTower R₁ R₂ A] (I : Ideal A) :
    IsScalarTower R₁ R₂ (A ⧸ I) := inferInstance

/--
Definition of `Quotient.mkₐ` / `Quotient.mkₐ` 的定义

English:
definition Quotient.mkₐ
  signature: (I : Ideal A) [I.IsTwoSided]
  body: ⟨⟨⟨⟨fun a => Submodule.Quotient.mk a, rfl⟩, fun _ _ => rfl⟩, rfl, fun _ _ => rfl⟩, fun _ => rfl⟩

中文:
定义 商.mkₐ
  签名: (I : 理想 A) [I.是TwoSided]
  定义体: ⟨⟨⟨⟨fun a => Submodule.Quotient.mk a, rfl⟩, fun _ _ => rfl⟩, rfl, fun _ _ => rfl⟩, fun _ => rfl⟩

Depends on / 依赖: Quotient, Submodule, Submodule.Quotient.mk
-/
def Quotient.mkₐ (I : Ideal A) [I.IsTwoSided] : A ->ₐ[R₁] A ⧸ I :=
  ⟨⟨⟨⟨fun a => Submodule.Quotient.mk a, rfl⟩, fun _ _ => rfl⟩, rfl, fun _ _ => rfl⟩, fun _ => rfl⟩

/--
theorem `Quotient.algHom_ext` / 定理 `Quotient.algHom_ext`

English:
theorem Quotient.algHom_ext
  statement: {I : Ideal A} [I.IsTwoSided]
  proof: AlgHom.ext fun x => Quotient.inductionOn' x AlgHom.congr_fun h

中文:
定理 商.algHom_ext
  结论: {I : 理想 A} [I.是TwoSided]
  证明: AlgHom.ext fun x => Quotient.inductionOn' x AlgHom.congr_fun h

Depends on / 依赖: AlgHom, AlgHom.congr_fun, AlgHom.ext, Quotient, Quotient.inductionOn, congr_fun, inductionOn
-/
theorem Quotient.algHom_ext {I : Ideal A} [I.IsTwoSided]
    {S} [Semiring S] [Algebra R₁ S] ⦃f g : A ⧸ I ->ₐ[R₁] S⦄
    (h : f.comp (Quotient.mkₐ R₁ I) = g.comp (Quotient.mkₐ R₁ I)) : f = g :=
AlgHom.ext fun x => Quotient.inductionOn' x AlgHom.congr_fun h

/--
theorem `Quotient.alg_map_eq` / 定理 `Quotient.alg_map_eq`

English:
theorem Quotient.alg_map_eq
  given: {A} [CommRing A] [Algebra R₁ A] (I : Ideal A)
  proof: rfl

中文:
定理 商.alg_map_eq
  条件: {A} [交换环 A] [代数 R₁ A] (I : 理想 A)
  证明: rfl
-/
theorem Quotient.alg_map_eq {A} [CommRing A] [Algebra R₁ A] (I : Ideal A) :
    algebraMap R₁ (A ⧸ I) = (algebraMap A (A ⧸ I)).comp (algebraMap R₁ A) :=
  rfl

/--
theorem `Quotient.mkₐ_toRingHom` / 定理 `Quotient.mkₐ_toRingHom`

English:
theorem Quotient.mkₐ_toRingHom
  given: (I : Ideal A) [I.IsTwoSided]
  proof: rfl

@[simp]

中文:
定理 商.mkₐ_toRingHom
  条件: (I : 理想 A) [I.是TwoSided]
  证明: rfl

@[simp]
-/
theorem Quotient.mkₐ_toRingHom (I : Ideal A) [I.IsTwoSided] :
    (Quotient.mkₐ R₁ I).toRingHom = Ideal.Quotient.mk I :=
  rfl

@[simp]
/--
theorem `Quotient.mkₐ_eq_mk` / 定理 `Quotient.mkₐ_eq_mk`

English:
theorem Quotient.mkₐ_eq_mk
  given: (I : Ideal A) [I.IsTwoSided]
  statement: ⇑(Quotient.mkₐ R₁ I) = Quotient.mk I
  proof: rfl

@[simp]

中文:
定理 商.mkₐ_eq_mk
  条件: (I : 理想 A) [I.是TwoSided]
  结论: ⇑(商.mkₐ R₁ I) = 商.mk I
  证明: rfl

@[simp]
-/
theorem Quotient.mkₐ_eq_mk (I : Ideal A) [I.IsTwoSided] : ⇑(Quotient.mkₐ R₁ I) = Quotient.mk I :=
  rfl

@[simp]
/--
theorem `Quotient.algebraMap_eq` / 定理 `Quotient.algebraMap_eq`

English:
theorem Quotient.algebraMap_eq
  given: {R} [CommRing R] (I : Ideal R)
  proof: rfl

@[simp]

中文:
定理 商.algebraMap_eq
  条件: {R} [交换环 R] (I : 理想 R)
  证明: rfl

@[simp]
-/
theorem Quotient.algebraMap_eq {R} [CommRing R] (I : Ideal R) :
    algebraMap R (R ⧸ I) = Quotient.mk I :=
  rfl

@[simp]
/--
theorem `Quotient.mk_comp_algebraMap` / 定理 `Quotient.mk_comp_algebraMap`

English:
theorem Quotient.mk_comp_algebraMap
  given: (I : Ideal A) [I.IsTwoSided]
  proof: rfl

@[simp]

中文:
定理 商.mk_comp_algebraMap
  条件: (I : 理想 A) [I.是TwoSided]
  证明: rfl

@[simp]
-/
theorem Quotient.mk_comp_algebraMap (I : Ideal A) [I.IsTwoSided] :
    (Quotient.mk I).comp (algebraMap R₁ A) = algebraMap R₁ (A ⧸ I) :=
  rfl

@[simp]
/--
theorem `Quotient.mk_algebraMap` / 定理 `Quotient.mk_algebraMap`

English:
theorem Quotient.mk_algebraMap
  given: (I : Ideal A) [I.IsTwoSided] (x : R₁)
  proof: rfl

中文:
定理 商.mk_algebraMap
  条件: (I : 理想 A) [I.是TwoSided] (x : R₁)
  证明: rfl
-/
theorem Quotient.mk_algebraMap (I : Ideal A) [I.IsTwoSided] (x : R₁) :
    Quotient.mk I (algebraMap R₁ A x) = algebraMap R₁ (A ⧸ I) x :=
  rfl

/--
theorem `Quotient.mkₐ_surjective` / 定理 `Quotient.mkₐ_surjective`

English:
theorem Quotient.mkₐ_surjective
  given: (I : Ideal A) [I.IsTwoSided]
  proof: Quot.mk_surjective

中文:
定理 商.mkₐ_surjective
  条件: (I : 理想 A) [I.是TwoSided]
  证明: Quot.mk_surjective

Depends on / 依赖: Quot.mk_surjective, mk_surjective
-/
theorem Quotient.mkₐ_surjective (I : Ideal A) [I.IsTwoSided] :
    Function.Surjective (Quotient.mkₐ R₁ I) :=
  Quot.mk_surjective

/-- The kernel of `A →ₐ[R₁] I.quotient` is `I`. -/
@[simp]
/--
theorem `Quotient.mkₐ_ker` / 定理 `Quotient.mkₐ_ker`

English:
theorem Quotient.mkₐ_ker
  given: (I : Ideal A) [I.IsTwoSided]
  proof: Ideal.mk_ker

中文:
定理 商.mkₐ_ker
  条件: (I : 理想 A) [I.是TwoSided]
  证明: Ideal.mk_ker

Depends on / 依赖: Ideal.mk_ker, mk_ker
-/
theorem Quotient.mkₐ_ker (I : Ideal A) [I.IsTwoSided] :
    RingHom.ker (Quotient.mkₐ R₁ I : A ->+* A ⧸ I) = I :=
  Ideal.mk_ker

/--
lemma `Quotient.mk_bijective_iff_eq_bot` / 引理 `Quotient.mk_bijective_iff_eq_bot`

English:
lemma Quotient.mk_bijective_iff_eq_bot
  given: (I : Ideal A) [I.IsTwoSided]
  proof: by
  constructor
  · intro h
    rw [← map_eq_bot_iff_of_injective h.1]
exact (map_eq_bot_iff_le_ker _).mpr le_of_eq mk_ker.symm
· exact fun h => ⟨(injective_iff_ker_eq_bot _).mpr by rw [mk_ker, h], mk_surjective⟩

中文:
引理 商.mk_bijective_iff_eq_bot
  条件: (I : 理想 A) [I.是TwoSided]
  证明: by
  constructor
  · intro h
    rw [← map_eq_bot_iff_of_injective h.1]
exact (map_eq_bot_iff_le_ker _).mpr le_of_eq mk_ker.symm
· exact fun h => ⟨(injective_iff_ker_eq_bot _).mpr by rw [mk_ker, h], mk_surjective⟩

Depends on / 依赖: injective_iff_ker_eq_bot, le_of_eq, map_eq_bot_iff_le_ker, map_eq_bot_iff_of_injective, mk_ker, mk_ker.symm, mk_surjective
-/
lemma Quotient.mk_bijective_iff_eq_bot (I : Ideal A) [I.IsTwoSided] :
    Function.Bijective (mk I) ↔ I = ⊥ := by
  constructor
  · intro h
    rw [← map_eq_bot_iff_of_injective h.1]
exact (map_eq_bot_iff_le_ker _).mpr le_of_eq mk_ker.symm
· exact fun h => ⟨(injective_iff_ker_eq_bot _).mpr by rw [mk_ker, h], mk_surjective⟩

section

/--
Definition of `Quotient.factorₐ` / `Quotient.factorₐ` 的定义

English:
definition Quotient.factorₐ
  signature: {I J : Ideal A} [I.IsTwoSided] [J.IsTwoSided] (hIJ : I <= J)
  body: Ideal.Quotient.factor hIJ
  commutes' _ := rfl

中文:
定义 商.factorₐ
  签名: {I J : 理想 A} [I.是TwoSided] [J.是TwoSided] (hIJ : I <= J)
  定义体: Ideal.Quotient.factor hIJ
  commutes' _ := rfl

Depends on / 依赖: Ideal.Quotient.factor, Quotient, factor
-/
def Quotient.factorₐ {I J : Ideal A} [I.IsTwoSided] [J.IsTwoSided] (hIJ : I <= J) :
    A ⧸ I ->ₐ[R₁] A ⧸ J where
  __ := Ideal.Quotient.factor hIJ
  commutes' _ := rfl

variable {I J : Ideal A} [I.IsTwoSided] [J.IsTwoSided] (hIJ : I <= J)

@[simp]
/--
lemma `Quotient.coe_factorₐ` / 引理 `Quotient.coe_factorₐ`

English:
lemma Quotient.coe_factorₐ
  proof: rfl

@[simp]

中文:
引理 商.coe_factorₐ
  证明: rfl

@[simp]

Depends on / 依赖: exacts, h.t_inv, t_inv
-/
lemma Quotient.coe_factorₐ :
    (Ideal.Quotient.factorₐ R₁ hIJ : A ⧸ I ->+* A ⧸ J) = Ideal.Quotient.factor hIJ := rfl

@[simp]
/--
lemma `Quotient.factorₐ_apply_mk` / 引理 `Quotient.factorₐ_apply_mk`

English:
lemma Quotient.factorₐ_apply_mk
  given: (x : A)
  proof: rfl

@[simp]

中文:
引理 商.factorₐ_apply_mk
  条件: (x : A)
  证明: rfl

@[simp]
-/
lemma Quotient.factorₐ_apply_mk (x : A) :
    Ideal.Quotient.factorₐ R₁ hIJ x = x := rfl

@[simp]
/--
lemma `Quotient.factorₐ_comp_mk` / 引理 `Quotient.factorₐ_comp_mk`

English:
lemma Quotient.factorₐ_comp_mk
  proof: rfl

@[simp]

中文:
引理 商.factorₐ_comp_mk
  证明: rfl

@[simp]
-/
lemma Quotient.factorₐ_comp_mk :
    (Ideal.Quotient.factorₐ R₁ hIJ).comp (Ideal.Quotient.mkₐ R₁ I) = Ideal.Quotient.mkₐ R₁ J := rfl

@[simp]
/--
theorem `Quotient.factorₐ_apply` / 定理 `Quotient.factorₐ_apply`

English:
theorem Quotient.factorₐ_apply
  given: (x : A ⧸ I)
  proof: rfl

@[simp]

中文:
定理 商.factorₐ_apply
  条件: (x : A ⧸ I)
  证明: rfl

@[simp]
-/
theorem Quotient.factorₐ_apply (x : A ⧸ I) :
    Quotient.factorₐ R₁ hIJ x = Quotient.factor hIJ x := rfl

@[simp]
/--
lemma `Quotient.factorₐ_refl` / 引理 `Quotient.factorₐ_refl`

English:
lemma Quotient.factorₐ_refl
  given: {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (I : Ideal A)
  proof: by
  ext
  simp

@[simp]

中文:
引理 商.factorₐ_refl
  条件: {R A : 类型} [交换环 R] [交换环 A] [代数 R A] (I : 理想 A)
  证明: by
  ext
  simp

@[simp]
-/
lemma Quotient.factorₐ_refl {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (I : Ideal A) :
    Ideal.Quotient.factorₐ R (le_refl I) = AlgHom.id R _ := by
  ext
  simp

@[simp]
/--
lemma `Quotient.factorₐ_comp` / 引理 `Quotient.factorₐ_comp`

English:
lemma Quotient.factorₐ_comp
  given: {K : Ideal A} [K.IsTwoSided] (hJK : J <= K)
  proof: Ideal.Quotient.algHom_ext _ (by ext; simp)

中文:
引理 商.factorₐ_comp
  条件: {K : 理想 A} [K.是TwoSided] (hJK : J <= K)
  证明: Ideal.Quotient.algHom_ext _ (by ext; simp)

Depends on / 依赖: Ideal.Quotient.algHom_ext, Quotient, algHom_ext
-/
lemma Quotient.factorₐ_comp {K : Ideal A} [K.IsTwoSided] (hJK : J <= K) :
    (Ideal.Quotient.factorₐ R₁ hJK).comp (Ideal.Quotient.factorₐ R₁ hIJ) =
      Ideal.Quotient.factorₐ R₁ (hIJ.trans hJK) :=
  Ideal.Quotient.algHom_ext _ (by ext; simp)

end

variable {R₁}

section

variable [Semiring B] [Algebra R₁ B]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `Quotient.liftₐ` / `Quotient.liftₐ` 的定义

English:
definition Quotient.liftₐ
  signature: (I : Ideal A) [I.IsTwoSided] (f : A ->ₐ[R₁] B) (hI : forall a : A, a in I -> f a = 0)
  body: { -- this is IsScalarTower.algebraMap_apply R₁ A (A ⧸ I) but the file `Algebra.Algebra.Tower`
    -- imports this file.
      Ideal.Quotient.lift
      I (f : A ->+* B) hI with
    commutes' := fun r => by
      have : algebraMap R₁ (A ⧸ I) r = Ideal.Quotient.mk I (algebraMap R₁ A r) := rfl
      rw

中文:
定义 商.liftₐ
  签名: (I : 理想 A) [I.是TwoSided] (f : A ->ₐ[R₁] B) (hI : 对任意 a : A, a in I -> f a = 0)
  定义体: { -- this is IsScalarTower.algebraMap_apply R₁ A (A ⧸ I) but the file `Algebra.Algebra.Tower`
    -- imports this file.
      Ideal.Quotient.lift
      I (f : A ->+* B) hI with
    commutes' := fun r => by
      have : algebraMap R₁ (A ⧸ I) r = Ideal.Quotient.mk I (algebraMap R₁ A r) := rfl
      rw

Depends on / 依赖: Algebra, Algebra.Algebra.Tower, IsScalarTower, IsScalarTower.algebraMap_apply, algebraMap_apply
-/
def Quotient.liftₐ (I : Ideal A) [I.IsTwoSided] (f : A ->ₐ[R₁] B) (hI : forall a : A, a in I -> f a = 0) :
    A ⧸ I ->ₐ[R₁] B :=
  { -- this is IsScalarTower.algebraMap_apply R₁ A (A ⧸ I) but the file `Algebra.Algebra.Tower`
    -- imports this file.
      Ideal.Quotient.lift
      I (f : A ->+* B) hI with
    commutes' := fun r => by
      have : algebraMap R₁ (A ⧸ I) r = Ideal.Quotient.mk I (algebraMap R₁ A r) := rfl
      rw [this]; rw [RingHom.toFun_eq_coe]; rw [Ideal.Quotient.lift_mk]; rw [AlgHom.coe_toRingHom]; rw [Algebra.algebraMap_eq_smul_one]; rw [Algebra.algebraMap_eq_smul_one]; rw [map_smul]; rw [map_one] }

@[simp]
/--
theorem `Quotient.liftₐ_apply` / 定理 `Quotient.liftₐ_apply`

English:
theorem Quotient.liftₐ_apply
  statement: (I : Ideal A) [I.IsTwoSided]
  proof: rfl

中文:
定理 商.liftₐ_apply
  结论: (I : 理想 A) [I.是TwoSided]
  证明: rfl
-/
theorem Quotient.liftₐ_apply (I : Ideal A) [I.IsTwoSided]
    (f : A ->ₐ[R₁] B) (hI : forall a : A, a in I -> f a = 0) (x) :
    Ideal.Quotient.liftₐ I f hI x = Ideal.Quotient.lift I (f : A ->+* B) hI x :=
  rfl

/--
theorem `Quotient.liftₐ_comp` / 定理 `Quotient.liftₐ_comp`

English:
theorem Quotient.liftₐ_comp
  statement: (I : Ideal A) [I.IsTwoSided]
  proof: AlgHom.ext fun _ => (Ideal.Quotient.lift_mk I (f : A ->+* B) hI :)

中文:
定理 商.liftₐ_comp
  结论: (I : 理想 A) [I.是TwoSided]
  证明: AlgHom.ext fun _ => (Ideal.Quotient.lift_mk I (f : A ->+* B) hI :)

Depends on / 依赖: AlgHom, AlgHom.ext, Ideal.Quotient.lift_mk, Quotient, lift_mk
-/
theorem Quotient.liftₐ_comp (I : Ideal A) [I.IsTwoSided]
    (f : A ->ₐ[R₁] B) (hI : forall a : A, a in I -> f a = 0) :
    (Ideal.Quotient.liftₐ I f hI).comp (Ideal.Quotient.mkₐ R₁ I) = f :=
  AlgHom.ext fun _ => (Ideal.Quotient.lift_mk I (f : A ->+* B) hI :)

/--
theorem `Quotient.span_singleton_one` / 定理 `Quotient.span_singleton_one`

English:
theorem Quotient.span_singleton_one
  given: (I : Ideal A) [I.IsTwoSided]
  proof: by
  rw [← map_one (mk _)]; rw [← Submodule.range_mkQ I]; rw [← Submodule.map_top]; rw [← Ideal.span_singleton_one]; rw [Ideal.span]; rw [Submodule.map_span]; rw [Set.image_singleton]; rw [Submodule.mkQ_apply]; rw [Quotient.mk_eq_mk]

中文:
定理 商.span_singleton_one
  条件: (I : 理想 A) [I.是TwoSided]
  证明: by
  rw [← map_one (mk _)]; rw [← Submodule.range_mkQ I]; rw [← Submodule.map_top]; rw [← Ideal.span_singleton_one]; rw [Ideal.span]; rw [Submodule.map_span]; rw [Set.image_singleton]; rw [Submodule.mkQ_apply]; rw [Quotient.mk_eq_mk]

Depends on / 依赖: Ideal.span, Ideal.span_singleton_one, Quotient, Quotient.mk_eq_mk, Set.image_singleton, Submodule, Submodule.map_span, Submodule.map_top, Submodule.mkQ_apply, Submodule.range_mkQ, image_singleton, map_one, map_span, map_top, mkQ_apply, mk_eq_mk, range_mkQ, span_singleton_one
-/
theorem Quotient.span_singleton_one (I : Ideal A) [I.IsTwoSided] :
    Submodule.span A {(1 : A ⧸ I)} = ⊤ := by
  rw [← map_one (mk _)]; rw [← Submodule.range_mkQ I]; rw [← Submodule.map_top]; rw [← Ideal.span_singleton_one]; rw [Ideal.span]; rw [Submodule.map_span]; rw [Set.image_singleton]; rw [Submodule.mkQ_apply]; rw [Quotient.mk_eq_mk]

open scoped Pointwise in
/--
lemma `Quotient.smul_top` / 引理 `Quotient.smul_top`

English:
lemma Quotient.smul_top
  given: {R : Type*} [CommRing R] (a : R) (I : Ideal R)
  proof: by
  simp [← Ideal.Quotient.span_singleton_one, Algebra.smul_def, Submodule.smul_span]

中文:
引理 商.smul_top
  条件: {R : 类型} [交换环 R] (a : R) (I : 理想 R)
  证明: by
  simp [← Ideal.Quotient.span_singleton_one, Algebra.smul_def, Submodule.smul_span]

Depends on / 依赖: Algebra, Algebra.smul_def, Ideal.Quotient.span_singleton_one, Quotient, Submodule, Submodule.smul_span, smul_def, smul_span, span_singleton_one
-/
lemma Quotient.smul_top {R : Type*} [CommRing R] (a : R) (I : Ideal R) :
    (a • ⊤ : Submodule R (R ⧸ I)) = Submodule.span R {Submodule.Quotient.mk a} := by
  simp [← Ideal.Quotient.span_singleton_one, Algebra.smul_def, Submodule.smul_span]

/--
theorem `KerLift.map_smul` / 定理 `KerLift.map_smul`

English:
theorem KerLift.map_smul
  given: (f : A ->ₐ[R₁] B) (r : R₁) (x : A ⧸ (RingHom.ker f))
  proof: by
  obtain ⟨a, rfl⟩ := Quotient.mkₐ_surjective R₁ _ x
  exact _root_.map_smul f _ _

中文:
定理 KerLift.map_smul
  条件: (f : A ->ₐ[R₁] B) (r : R₁) (x : A ⧸ (环态射.ker f))
  证明: by
  obtain ⟨a, rfl⟩ := Quotient.mkₐ_surjective R₁ _ x
  exact _root_.map_smul f _ _

Depends on / 依赖: Quotient, Quotient.mk, _root_, _root_.map_smul, map_smul
-/
theorem KerLift.map_smul (f : A ->ₐ[R₁] B) (r : R₁) (x : A ⧸ (RingHom.ker f)) :
    f.kerLift (r • x) = r • f.kerLift x := by
  obtain ⟨a, rfl⟩ := Quotient.mkₐ_surjective R₁ _ x
  exact _root_.map_smul f _ _

/--
Definition of `kerLiftAlg` / `kerLiftAlg` 的定义

English:
definition kerLiftAlg
  signature: (f : A ->ₐ[R₁] B)
  body: AlgHom.mk' (RingHom.kerLift (f : A ->+* B)) fun _ _ => KerLift.map_smul f _ _

@[simp]

中文:
定义 kerLiftAlg
  签名: (f : A ->ₐ[R₁] B)
  定义体: AlgHom.mk' (RingHom.kerLift (f : A ->+* B)) fun _ _ => KerLift.map_smul f _ _

@[simp]

Depends on / 依赖: AlgHom, AlgHom.mk, KerLift, KerLift.map_smul, RingHom, RingHom.kerLift, kerLift, map_smul
-/
def kerLiftAlg (f : A ->ₐ[R₁] B) : A ⧸ (RingHom.ker f) ->ₐ[R₁] B :=
  AlgHom.mk' (RingHom.kerLift (f : A ->+* B)) fun _ _ => KerLift.map_smul f _ _

@[simp]
/--
theorem `kerLiftAlg_mk` / 定理 `kerLiftAlg_mk`

English:
theorem kerLiftAlg_mk
  given: (f : A ->ₐ[R₁] B) (a : A)
  proof: by
  rfl

@[simp]

中文:
定理 kerLiftAlg_mk
  条件: (f : A ->ₐ[R₁] B) (a : A)
  证明: by
  rfl

@[simp]
-/
theorem kerLiftAlg_mk (f : A ->ₐ[R₁] B) (a : A) :
    kerLiftAlg f (Quotient.mk (RingHom.ker f) a) = f a := by
  rfl

@[simp]
/--
theorem `kerLiftAlg_toRingHom` / 定理 `kerLiftAlg_toRingHom`

English:
theorem kerLiftAlg_toRingHom
  given: (f : A ->ₐ[R₁] B)
  proof: rfl

中文:
定理 kerLiftAlg_toRingHom
  条件: (f : A ->ₐ[R₁] B)
  证明: rfl
-/
theorem kerLiftAlg_toRingHom (f : A ->ₐ[R₁] B) :
    (kerLiftAlg f : A ⧸ ker f ->+* B) = RingHom.kerLift (f : A ->+* B) :=
  rfl

/--
theorem `kerLiftAlg_injective` / 定理 `kerLiftAlg_injective`

English:
theorem kerLiftAlg_injective
  given: (f : A ->ₐ[R₁] B)
  statement: Function.Injective (kerLiftAlg f)
  proof: RingHom.kerLift_injective (R := A) (S := B) f

中文:
定理 kerLiftAlg_injective
  条件: (f : A ->ₐ[R₁] B)
  结论: 函数.单射 (kerLiftAlg f)
  证明: RingHom.kerLift_injective (R := A) (S := B) f

Depends on / 依赖: RingHom, RingHom.kerLift_injective, kerLift_injective
-/
theorem kerLiftAlg_injective (f : A ->ₐ[R₁] B) : Function.Injective (kerLiftAlg f) :=
  RingHom.kerLift_injective (R := A) (S := B) f

/-- The **first isomorphism** theorem for algebras, computable version. -/
@[simps!]
/--
Definition of `quotientKerAlgEquivOfRightInverse` / `quotientKerAlgEquivOfRightInverse` 的定义

English:
definition quotientKerAlgEquivOfRightInverse
  signature: {f : A ->ₐ[R₁] B} {g : B -> A}
  body: { RingHom.quotientKerEquivOfRightInverse hf,
    kerLiftAlg f with }

中文:
定义 quotientKerAlgEquivOfRightInverse
  签名: {f : A ->ₐ[R₁] B} {g : B -> A}
  定义体: { RingHom.quotientKerEquivOfRightInverse hf,
    kerLiftAlg f with }

Depends on / 依赖: RingHom, RingHom.quotientKerEquivOfRightInverse, kerLiftAlg, quotientKerEquivOfRightInverse
-/
def quotientKerAlgEquivOfRightInverse {f : A ->ₐ[R₁] B} {g : B -> A}
    (hf : Function.RightInverse g f) : (A ⧸ RingHom.ker f) ≃ₐ[R₁] B :=
  { RingHom.quotientKerEquivOfRightInverse hf,
    kerLiftAlg f with }

/-- The **first isomorphism theorem** for algebras. -/
@[simps! -isSimp apply]
/--
Definition of `quotientKerAlgEquivOfSurjective` / `quotientKerAlgEquivOfSurjective` 的定义

English:
definition quotientKerAlgEquivOfSurjective
  signature: {f : A ->ₐ[R₁] B} (hf : Function.Surjective f)
  body: quotientKerAlgEquivOfRightInverse (Classical.choose_spec hf.hasRightInverse)

@[simp]

中文:
定义 quotientKerAlgEquivOfSurjective
  签名: {f : A ->ₐ[R₁] B} (hf : 函数.满射 f)
  定义体: quotientKerAlgEquivOfRightInverse (Classical.choose_spec hf.hasRightInverse)

@[simp]

Depends on / 依赖: Classical, Classical.choose_spec, choose_spec, hasRightInverse, hf.hasRightInverse, quotientKerAlgEquivOfRightInverse
-/
noncomputable def quotientKerAlgEquivOfSurjective {f : A ->ₐ[R₁] B} (hf : Function.Surjective f) :
    (A ⧸ (RingHom.ker f)) ≃ₐ[R₁] B :=
  quotientKerAlgEquivOfRightInverse (Classical.choose_spec hf.hasRightInverse)

@[simp]
/--
lemma `quotientKerAlgEquivOfSurjective_mk` / 引理 `quotientKerAlgEquivOfSurjective_mk`

English:
lemma quotientKerAlgEquivOfSurjective_mk
  statement: {f : A ->ₐ[R₁] B} (hf : Function.Surjective f)
  proof: rfl

@[simp]

中文:
引理 quotientKerAlgEquivOfSurjective_mk
  结论: {f : A ->ₐ[R₁] B} (hf : 函数.满射 f)
  证明: rfl

@[simp]
-/
lemma quotientKerAlgEquivOfSurjective_mk {f : A ->ₐ[R₁] B} (hf : Function.Surjective f)
    (a : A) : Ideal.quotientKerAlgEquivOfSurjective hf (Ideal.Quotient.mk _ a) = f a :=
  rfl

@[simp]
/--
lemma `quotientKerAlgEquivOfSurjective_symm_apply` / 引理 `quotientKerAlgEquivOfSurjective_symm_apply`

English:
lemma quotientKerAlgEquivOfSurjective_symm_apply
  statement: {f : A ->ₐ[R₁] B} (hf : Function.Surjective f)
  proof: by
  apply (Ideal.quotientKerAlgEquivOfSurjective hf).injective
  simp

中文:
引理 quotientKerAlgEquivOfSurjective_symm_apply
  结论: {f : A ->ₐ[R₁] B} (hf : 函数.满射 f)
  证明: by
  apply (Ideal.quotientKerAlgEquivOfSurjective hf).injective
  simp

Depends on / 依赖: Ideal.quotientKerAlgEquivOfSurjective, injective, quotientKerAlgEquivOfSurjective
-/
lemma quotientKerAlgEquivOfSurjective_symm_apply {f : A ->ₐ[R₁] B} (hf : Function.Surjective f)
    (a : A) : (Ideal.quotientKerAlgEquivOfSurjective hf).symm (f a) = a := by
  apply (Ideal.quotientKerAlgEquivOfSurjective hf).injective
  simp

section liftOfSurjective

variable {R A B C : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra R C]

/-- `AlgHom` version of `RingHom.liftOfSurjective` that descends an algebra homomorphism
along a surjection. -/
noncomputable
/--
Definition of `_root_.AlgHom.liftOfSurjective` / `_root_.AlgHom.liftOfSurjective` 的定义

English:
definition _root_.AlgHom.liftOfSurjective
  signature: (f : A ->ₐ[R] B) (hf : Function.Surjective f)
  body: .comp (Ideal.Quotient.liftₐ _ g H) (Ideal.quotientKerAlgEquivOfSurjective hf).symm.toAlgHom

中文:
定义 _root_.代数态射.liftOfSurjective
  签名: (f : A ->ₐ[R] B) (hf : 函数.满射 f)
  定义体: .comp (Ideal.Quotient.liftₐ _ g H) (Ideal.quotientKerAlgEquivOfSurjective hf).symm.toAlgHom

Depends on / 依赖: Ideal.Quotient.lift, Ideal.quotientKerAlgEquivOfSurjective, Quotient, quotientKerAlgEquivOfSurjective, symm.toAlgHom, toAlgHom
-/
def _root_.AlgHom.liftOfSurjective (f : A ->ₐ[R] B) (hf : Function.Surjective f)
    (g : A ->ₐ[R] C) (H : RingHom.ker f.toRingHom <= RingHom.ker g.toRingHom) : B ->ₐ[R] C :=
  .comp (Ideal.Quotient.liftₐ _ g H) (Ideal.quotientKerAlgEquivOfSurjective hf).symm.toAlgHom

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `_root_.AlgHom.liftOfSurjective_apply` / 引理 `_root_.AlgHom.liftOfSurjective_apply`

English:
lemma _root_.AlgHom.liftOfSurjective_apply
  statement: (f : A ->ₐ[R] B) (hf : Function.Surjective f)
  proof: by
  dsimp [AlgHom.liftOfSurjective]
  erw [AlgEquiv.coe_toAlgHom] -- fixed after #21031
  rw [Ideal.quotientKerAlgEquivOfSurjective_symm_apply]
  rfl

中文:
引理 _root_.代数态射.liftOfSurjective_apply
  结论: (f : A ->ₐ[R] B) (hf : 函数.满射 f)
  证明: by
  dsimp [AlgHom.liftOfSurjective]
  erw [AlgEquiv.coe_toAlgHom] -- fixed after #21031
  rw [Ideal.quotientKerAlgEquivOfSurjective_symm_apply]
  rfl

Depends on / 依赖: AlgEquiv, AlgEquiv.coe_toAlgHom, AlgHom, AlgHom.liftOfSurjective, Ideal.quotientKerAlgEquivOfSurjective_symm_apply, coe_toAlgHom, liftOfSurjective, quotientKerAlgEquivOfSurjective_symm_apply
-/
lemma _root_.AlgHom.liftOfSurjective_apply (f : A ->ₐ[R] B) (hf : Function.Surjective f)
    (g : A ->ₐ[R] C) (H : RingHom.ker f.toRingHom <= RingHom.ker g.toRingHom) (x) :
    AlgHom.liftOfSurjective f hf g H (f x) = g x := by
  dsimp [AlgHom.liftOfSurjective]
  erw [AlgEquiv.coe_toAlgHom] -- fixed after #21031
  rw [Ideal.quotientKerAlgEquivOfSurjective_symm_apply]
  rfl

/--
lemma `_root_.AlgHom.liftOfSurjective_comp` / 引理 `_root_.AlgHom.liftOfSurjective_comp`

English:
lemma _root_.AlgHom.liftOfSurjective_comp
  statement: (f : A ->ₐ[R] B) (hf : Function.Surjective f)
  proof: by
  ext; simp

中文:
引理 _root_.代数态射.liftOfSurjective_comp
  结论: (f : A ->ₐ[R] B) (hf : 函数.满射 f)
  证明: by
  ext; simp
-/
lemma _root_.AlgHom.liftOfSurjective_comp (f : A ->ₐ[R] B) (hf : Function.Surjective f)
    (g : A ->ₐ[R] C) (H : RingHom.ker f.toRingHom <= RingHom.ker g.toRingHom) :
    (AlgHom.liftOfSurjective f hf g H).comp f = g := by
  ext; simp

/--
lemma `_root_.AlgHom.liftOfSurjective_surjective` / 引理 `_root_.AlgHom.liftOfSurjective_surjective`

English:
lemma _root_.AlgHom.liftOfSurjective_surjective
  statement: (f : A ->ₐ[R] B) (hf : Function.Surjective f)
  proof: .of_comp (g := f) (by convert! hg; ext; simp)

中文:
引理 _root_.代数态射.liftOfSurjective_surjective
  结论: (f : A ->ₐ[R] B) (hf : 函数.满射 f)
  证明: .of_comp (g := f) (by convert! hg; ext; simp)

Depends on / 依赖: convert, of_comp
-/
lemma _root_.AlgHom.liftOfSurjective_surjective (f : A ->ₐ[R] B) (hf : Function.Surjective f)
    (g : A ->ₐ[R] C) (H : RingHom.ker f.toRingHom <= RingHom.ker g.toRingHom)
    (hg : Function.Surjective g) : Function.Surjective (AlgHom.liftOfSurjective f hf g H) :=
  .of_comp (g := f) (by convert! hg; ext; simp)

end liftOfSurjective

end

section Ring_Ring

variable {S : Type v} [Ring S]

/--
Definition of `quotientMap` / `quotientMap` 的定义

English:
definition quotientMap
  signature: {I : Ideal R} (J : Ideal S) [I.IsTwoSided] [J.IsTwoSided] (f : R ->+* S)
  body: Quotient.lift I ((Quotient.mk J).comp f) fun _ ha => by
    simpa [Function.comp_apply, RingHom.coe_comp, Quotient.eq_zero_iff_mem] using hIJ ha

@[simp]

中文:
定义 quotientMap
  签名: {I : 理想 R} (J : 理想 S) [I.是TwoSided] [J.是TwoSided] (f : R ->+* S)
  定义体: Quotient.lift I ((Quotient.mk J).comp f) fun _ ha => by
    simpa [Function.comp_apply, RingHom.coe_comp, Quotient.eq_zero_iff_mem] using hIJ ha

@[simp]

Depends on / 依赖: Function, Function.comp_apply, Quotient, Quotient.eq_zero_iff_mem, Quotient.lift, Quotient.mk, RingHom, RingHom.coe_comp, coe_comp, comp_apply, eq_zero_iff_mem
-/
def quotientMap {I : Ideal R} (J : Ideal S) [I.IsTwoSided] [J.IsTwoSided] (f : R ->+* S)
    (hIJ : I <= J.comap f) : R ⧸ I ->+* S ⧸ J :=
  Quotient.lift I ((Quotient.mk J).comp f) fun _ ha => by
    simpa [Function.comp_apply, RingHom.coe_comp, Quotient.eq_zero_iff_mem] using hIJ ha

@[simp]
/--
theorem `quotientMap_mk` / 定理 `quotientMap_mk`

English:
theorem quotientMap_mk
  statement: {J : Ideal R} {I : Ideal S} [I.IsTwoSided] [J.IsTwoSided]
  proof: Quotient.lift_mk J _ _

@[simp]

中文:
定理 quotientMap_mk
  结论: {J : 理想 R} {I : 理想 S} [I.是TwoSided] [J.是TwoSided]
  证明: Quotient.lift_mk J _ _

@[simp]

Depends on / 依赖: Quotient, Quotient.lift_mk, lift_mk
-/
theorem quotientMap_mk {J : Ideal R} {I : Ideal S} [I.IsTwoSided] [J.IsTwoSided]
    {f : R ->+* S} {H : J <= I.comap f} {x : R} :
    quotientMap I f H (Quotient.mk J x) = Quotient.mk I (f x) :=
  Quotient.lift_mk J _ _

@[simp]
/--
theorem `quotientMap_algebraMap` / 定理 `quotientMap_algebraMap`

English:
theorem quotientMap_algebraMap
  statement: {J : Ideal A} {I : Ideal S} [I.IsTwoSided] [J.IsTwoSided]
  proof: Quotient.lift_mk J _ _

中文:
定理 quotientMap_algebraMap
  结论: {J : 理想 A} {I : 理想 S} [I.是TwoSided] [J.是TwoSided]
  证明: Quotient.lift_mk J _ _

Depends on / 依赖: Quotient, Quotient.lift_mk, lift_mk
-/
theorem quotientMap_algebraMap {J : Ideal A} {I : Ideal S} [I.IsTwoSided] [J.IsTwoSided]
    {f : A ->+* S} {H : J <= I.comap f}
    {x : R₁} : quotientMap I f H (algebraMap R₁ (A ⧸ J) x) = Quotient.mk I (f (algebraMap _ _ x)) :=
  Quotient.lift_mk J _ _

/--
theorem `quotientMap_comp_mk` / 定理 `quotientMap_comp_mk`

English:
theorem quotientMap_comp_mk
  statement: {J : Ideal R} {I : Ideal S} [I.IsTwoSided] [J.IsTwoSided]
  proof: RingHom.ext fun x => by simp only [Function.comp_apply, RingHom.coe_comp, Ideal.quotientMap_mk]

中文:
定理 quotientMap_comp_mk
  结论: {J : 理想 R} {I : 理想 S} [I.是TwoSided] [J.是TwoSided]
  证明: RingHom.ext fun x => by simp only [Function.comp_apply, RingHom.coe_comp, Ideal.quotientMap_mk]

Depends on / 依赖: Function, Function.comp_apply, Ideal.quotientMap_mk, RingHom, RingHom.coe_comp, RingHom.ext, coe_comp, comp_apply, quotientMap_mk
-/
theorem quotientMap_comp_mk {J : Ideal R} {I : Ideal S} [I.IsTwoSided] [J.IsTwoSided]
    {f : R ->+* S} (H : J <= I.comap f) :
    (quotientMap I f H).comp (Quotient.mk J) = (Quotient.mk I).comp f :=
  RingHom.ext fun x => by simp only [Function.comp_apply, RingHom.coe_comp, Ideal.quotientMap_mk]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `ker_quotientMap_mk` / 引理 `ker_quotientMap_mk`

English:
lemma ker_quotientMap_mk
  given: {I J : Ideal R} [I.IsTwoSided] [J.IsTwoSided]
  proof: by
  rw [Ideal.quotientMap]; rw [Ideal.ker_quotient_lift]; rw [← RingHom.comap_ker]; rw [Ideal.mk_ker]; rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective]; rw [← RingHom.ker_eq_comap_bot]; rw [Ideal.mk_ker]; rw [Ideal.map_sup]; rw [Ideal.map_quotient_self]; rw [bot_sup_eq]

中文:
引理 ker_quotientMap_mk
  条件: {I J : 理想 R} [I.是TwoSided] [J.是TwoSided]
  证明: by
  rw [Ideal.quotientMap]; rw [Ideal.ker_quotient_lift]; rw [← RingHom.comap_ker]; rw [Ideal.mk_ker]; rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective]; rw [← RingHom.ker_eq_comap_bot]; rw [Ideal.mk_ker]; rw [Ideal.map_sup]; rw [Ideal.map_quotient_self]; rw [bot_sup_eq]

Depends on / 依赖: Ideal.Quotient.mk_surjective, Ideal.comap_map_of_surjective, Ideal.ker_quotient_lift, Ideal.map_quotient_self, Ideal.map_sup, Ideal.mk_ker, Ideal.quotientMap, Quotient, RingHom, RingHom.comap_ker, RingHom.ker_eq_comap_bot, bot_sup_eq, comap_ker, comap_map_of_surjective, ker_eq_comap_bot, ker_quotient_lift, map_quotient_self, map_sup, mk_ker, mk_surjective
-/
lemma ker_quotientMap_mk {I J : Ideal R} [I.IsTwoSided] [J.IsTwoSided] :
    RingHom.ker (quotientMap (J.map _) (Quotient.mk I) le_comap_map) = I.map (Quotient.mk J) := by
  rw [Ideal.quotientMap]; rw [Ideal.ker_quotient_lift]; rw [← RingHom.comap_ker]; rw [Ideal.mk_ker]; rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective]; rw [← RingHom.ker_eq_comap_bot]; rw [Ideal.mk_ker]; rw [Ideal.map_sup]; rw [Ideal.map_quotient_self]; rw [bot_sup_eq]

section quotientEquiv

variable (I : Ideal R) (J : Ideal S) [I.IsTwoSided] [J.IsTwoSided]
    (f : R ≃+* S) (hIJ : J = I.map (f : R ->+* S))

/-- The ring equiv `R/I ≃+* S/J` induced by a ring equiv `f : R ≃+* S`, where `J = f(I)`. -/
@[simps]
/--
Definition of `quotientEquiv` / `quotientEquiv` 的定义

English:
definition quotientEquiv
  signature: : R ⧸ I ≃+* S ⧸ J where
  body: quotientMap J f (hIJ ▸ le_comap_map)
  invFun := quotientMap I f.symm (hIJ ▸ (map_comap_of_equiv f).le)
  left_inv := by
    rintro ⟨r⟩
    simp only [Submodule.Quotient.quot_mk_eq_mk, Quotient.mk_eq_mk, RingHom.toFun_eq_coe,
      quotientMap_mk, RingEquiv.coe_toRingHom, RingEquiv.symm_apply_apply]

中文:
定义 quotientEquiv
  签名: : R ⧸ I ≃+* S ⧸ J where
  定义体: quotientMap J f (hIJ ▸ le_comap_map)
  invFun := quotientMap I f.symm (hIJ ▸ (map_comap_of_equiv f).le)
  left_inv := by
    rintro ⟨r⟩
    simp only [Submodule.Quotient.quot_mk_eq_mk, Quotient.mk_eq_mk, RingHom.toFun_eq_coe,
      quotientMap_mk, RingEquiv.coe_toRingHom, RingEquiv.symm_apply_apply]

Depends on / 依赖: le_comap_map, quotientMap
-/
def quotientEquiv : R ⧸ I ≃+* S ⧸ J where
  __ := quotientMap J f (hIJ ▸ le_comap_map)
  invFun := quotientMap I f.symm (hIJ ▸ (map_comap_of_equiv f).le)
  left_inv := by
    rintro ⟨r⟩
    simp only [Submodule.Quotient.quot_mk_eq_mk, Quotient.mk_eq_mk, RingHom.toFun_eq_coe,
      quotientMap_mk, RingEquiv.coe_toRingHom, RingEquiv.symm_apply_apply]
  right_inv := by
    rintro ⟨s⟩
    simp only [Submodule.Quotient.quot_mk_eq_mk, Quotient.mk_eq_mk, RingHom.toFun_eq_coe,
      quotientMap_mk, RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply]

-- Not `@[simp]` since `simp` proves it.
/--
theorem `quotientEquiv_mk` / 定理 `quotientEquiv_mk`

English:
theorem quotientEquiv_mk
  given: (x : R)
  proof: rfl

中文:
定理 quotientEquiv_mk
  条件: (x : R)
  证明: rfl
-/
theorem quotientEquiv_mk (x : R) :
    quotientEquiv I J f hIJ (Ideal.Quotient.mk I x) = Ideal.Quotient.mk J (f x) :=
  rfl

-- Not `@[simp]` since `simp` proves it.
/--
theorem `quotientEquiv_symm_mk` / 定理 `quotientEquiv_symm_mk`

English:
theorem quotientEquiv_symm_mk
  given: (x : S)
  proof: rfl

中文:
定理 quotientEquiv_symm_mk
  条件: (x : S)
  证明: rfl
-/
theorem quotientEquiv_symm_mk (x : S) :
    (quotientEquiv I J f hIJ).symm (Ideal.Quotient.mk J x) = Ideal.Quotient.mk I (f.symm x) :=
  rfl

end quotientEquiv

/--
theorem `quotientMap_injective'` / 定理 `quotientMap_injective'`

English:
theorem quotientMap_injective'
  statement: {J : Ideal R} {I : Ideal S} [I.IsTwoSided] [J.IsTwoSided]
  proof: by
  refine (injective_iff_map_eq_zero (quotientMap I f H)).2 fun a ha => ?_
  obtain ⟨r, rfl⟩ := Quotient.mk_surjective a
  rw [quotientMap_mk]; rw [Quotient.eq_zero_iff_mem] at ha
  exact Quotient.eq_zero_iff_mem.mpr (h ha)

中文:
定理 quotientMap_injective'
  结论: {J : 理想 R} {I : 理想 S} [I.是TwoSided] [J.是TwoSided]
  证明: by
  refine (injective_iff_map_eq_zero (quotientMap I f H)).2 fun a ha => ?_
  obtain ⟨r, rfl⟩ := Quotient.mk_surjective a
  rw [quotientMap_mk]; rw [Quotient.eq_zero_iff_mem] at ha
  exact Quotient.eq_zero_iff_mem.mpr (h ha)

Depends on / 依赖: Quotient, Quotient.eq_zero_iff_mem, Quotient.eq_zero_iff_mem.mpr, Quotient.mk_surjective, eq_zero_iff_mem, injective_iff_map_eq_zero, mk_surjective, quotientMap, quotientMap_mk
-/
theorem quotientMap_injective' {J : Ideal R} {I : Ideal S} [I.IsTwoSided] [J.IsTwoSided]
    {f : R ->+* S} {H : J <= I.comap f} (h : I.comap f <= J) :
    Function.Injective (quotientMap I f H) := by
  refine (injective_iff_map_eq_zero (quotientMap I f H)).2 fun a ha => ?_
  obtain ⟨r, rfl⟩ := Quotient.mk_surjective a
  rw [quotientMap_mk]; rw [Quotient.eq_zero_iff_mem] at ha
  exact Quotient.eq_zero_iff_mem.mpr (h ha)

/--
theorem `quotientMap_injective` / 定理 `quotientMap_injective`

English:
theorem quotientMap_injective
  given: {I : Ideal S} {f : R ->+* S} [I.IsTwoSided]
  proof: quotientMap_injective' le_rfl

中文:
定理 quotientMap_injective
  条件: {I : 理想 S} {f : R ->+* S} [I.是TwoSided]
  证明: quotientMap_injective' le_rfl

Depends on / 依赖: le_rfl, quotientMap_injective
-/
theorem quotientMap_injective {I : Ideal S} {f : R ->+* S} [I.IsTwoSided] :
    Function.Injective (quotientMap I f le_rfl) :=
  quotientMap_injective' le_rfl

/--
theorem `quotientMap_surjective` / 定理 `quotientMap_surjective`

English:
theorem quotientMap_surjective
  statement: {J : Ideal R} {I : Ideal S} [I.IsTwoSided] [J.IsTwoSided]
  proof: fun x =>
  let ⟨x, hx⟩ := Quotient.mk_surjective x
  let ⟨y, hy⟩ := hf x
  ⟨(Quotient.mk J) y, by simp [hx, hy]⟩

中文:
定理 quotientMap_surjective
  结论: {J : 理想 R} {I : 理想 S} [I.是TwoSided] [J.是TwoSided]
  证明: fun x =>
  let ⟨x, hx⟩ := Quotient.mk_surjective x
  let ⟨y, hy⟩ := hf x
  ⟨(Quotient.mk J) y, by simp [hx, hy]⟩
-/
theorem quotientMap_surjective {J : Ideal R} {I : Ideal S} [I.IsTwoSided] [J.IsTwoSided]
    {f : R ->+* S} {H : J <= I.comap f}
    (hf : Function.Surjective f) : Function.Surjective (quotientMap I f H) := fun x =>
  let ⟨x, hx⟩ := Quotient.mk_surjective x
  let ⟨y, hy⟩ := hf x
  ⟨(Quotient.mk J) y, by simp [hx, hy]⟩

/--
theorem `comp_quotientMap_eq_of_comp_eq` / 定理 `comp_quotientMap_eq_of_comp_eq`

English:
theorem comp_quotientMap_eq_of_comp_eq
  statement: {R' S' : Type*} [Ring R'] [Ring S'] {f : R ->+* S}
  proof: le_of_eq (_root_.trans (comap_comap f g') (hfg ▸ comap_comap g f'))
    (quotientMap I g' le_rfl).comp (quotientMap (I.comap g') f le_rfl) =
    (quotientMap I f' le_rfl).comp (quotientMap (I.comap f') g leq) := by
  refine RingHom.ext fun a => ?_
  obtain ⟨r, rfl⟩ := Quotient.mk_surjective a
  simp

中文:
定理 comp_quotientMap_eq_of_comp_eq
  结论: {R' S' : 类型} [环 R'] [环 S'] {f : R ->+* S}
  证明: le_of_eq (_root_.trans (comap_comap f g') (hfg ▸ comap_comap g f'))
    (quotientMap I g' le_rfl).comp (quotientMap (I.comap g') f le_rfl) =
    (quotientMap I f' le_rfl).comp (quotientMap (I.comap f') g leq) := by
  refine RingHom.ext fun a => ?_
  obtain ⟨r, rfl⟩ := Quotient.mk_surjective a
  simp

Depends on / 依赖: _root_, _root_.trans, comap_comap, le_of_eq
-/
theorem comp_quotientMap_eq_of_comp_eq {R' S' : Type*} [Ring R'] [Ring S'] {f : R ->+* S}
    {f' : R' ->+* S'} {g : R ->+* R'} {g' : S ->+* S'} (hfg : f'.comp g = g'.comp f)
    (I : Ideal S') [I.IsTwoSided] :
    let leq := le_of_eq (_root_.trans (comap_comap f g') (hfg ▸ comap_comap g f'))
    (quotientMap I g' le_rfl).comp (quotientMap (I.comap g') f le_rfl) =
    (quotientMap I f' le_rfl).comp (quotientMap (I.comap f') g leq) := by
  refine RingHom.ext fun a => ?_
  obtain ⟨r, rfl⟩ := Quotient.mk_surjective a
  simp only [RingHom.comp_apply, quotientMap_mk]
  exact (Ideal.Quotient.mk I).congr_arg (_root_.trans (g'.comp_apply f r).symm
    (hfg ▸ f'.comp_apply g r))

end Ring_Ring


section

variable [Ring B] [Algebra R₁ B] {I : Ideal A} (J : Ideal B) [I.IsTwoSided] [J.IsTwoSided]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `quotientMapₐ` / `quotientMapₐ` 的定义

English:
definition quotientMapₐ
  signature: (f : A ->ₐ[R₁] B) (hIJ : I <= J.comap f)
  body: { quotientMap J (f : A ->+* B) hIJ with commutes' := fun r => by simp only [RingHom.toFun_eq_coe,
    quotientMap_algebraMap, AlgHom.coe_toRingHom, AlgHom.commutes, Quotient.mk_algebraMap] }

@[simp]

中文:
定义 quotientMapₐ
  签名: (f : A ->ₐ[R₁] B) (hIJ : I <= J.comap f)
  定义体: { quotientMap J (f : A ->+* B) hIJ with commutes' := fun r => by simp only [RingHom.toFun_eq_coe,
    quotientMap_algebraMap, AlgHom.coe_toRingHom, AlgHom.commutes, Quotient.mk_algebraMap] }

@[simp]

Depends on / 依赖: AlgHom, AlgHom.coe_toRingHom, AlgHom.commutes, Quotient, Quotient.mk_algebraMap, RingHom, RingHom.toFun_eq_coe, coe_toRingHom, commutes, mk_algebraMap, quotientMap, quotientMap_algebraMap, toFun_eq_coe
-/
def quotientMapₐ (f : A ->ₐ[R₁] B) (hIJ : I <= J.comap f) :
    A ⧸ I ->ₐ[R₁] B ⧸ J :=
  { quotientMap J (f : A ->+* B) hIJ with commutes' := fun r => by simp only [RingHom.toFun_eq_coe,
    quotientMap_algebraMap, AlgHom.coe_toRingHom, AlgHom.commutes, Quotient.mk_algebraMap] }

@[simp]
/--
theorem `quotient_map_mkₐ` / 定理 `quotient_map_mkₐ`

English:
theorem quotient_map_mkₐ
  given: (f : A ->ₐ[R₁] B) (H : I <= J.comap f) {x : A}
  proof: rfl

中文:
定理 quotient_map_mkₐ
  条件: (f : A ->ₐ[R₁] B) (H : I <= J.comap f) {x : A}
  证明: rfl
-/
theorem quotient_map_mkₐ (f : A ->ₐ[R₁] B) (H : I <= J.comap f) {x : A} :
    quotientMapₐ J f H (Quotient.mk I x) = Quotient.mkₐ R₁ J (f x) :=
  rfl

/--
theorem `quotient_map_comp_mkₐ` / 定理 `quotient_map_comp_mkₐ`

English:
theorem quotient_map_comp_mkₐ
  given: (f : A ->ₐ[R₁] B) (H : I <= J.comap f)
  proof: AlgHom.ext fun x => by simp only [quotient_map_mkₐ, Quotient.mkₐ_eq_mk, AlgHom.comp_apply]

中文:
定理 quotient_map_comp_mkₐ
  条件: (f : A ->ₐ[R₁] B) (H : I <= J.comap f)
  证明: AlgHom.ext fun x => by simp only [quotient_map_mkₐ, Quotient.mkₐ_eq_mk, AlgHom.comp_apply]

Depends on / 依赖: AlgHom, AlgHom.comp_apply, AlgHom.ext, Quotient, Quotient.mk, comp_apply
-/
theorem quotient_map_comp_mkₐ (f : A ->ₐ[R₁] B) (H : I <= J.comap f) :
    (quotientMapₐ J f H).comp (Quotient.mkₐ R₁ I) = (Quotient.mkₐ R₁ J).comp f :=
  AlgHom.ext fun x => by simp only [quotient_map_mkₐ, Quotient.mkₐ_eq_mk, AlgHom.comp_apply]

set_option backward.isDefEq.respectTransparency false in
variable (I) in
/--
Definition of `quotientEquivAlg` / `quotientEquivAlg` 的定义

English:
definition quotientEquivAlg
  signature: (f : A ≃ₐ[R₁] B) (hIJ : J = I.map (f : A ->+* B))
  body: { quotientEquiv I J (f : A ≃+* B) hIJ with
    commutes' r := by simp }

@[simp]

中文:
定义 quotientEquivAlg
  签名: (f : A ≃ₐ[R₁] B) (hIJ : J = I.map (f : A ->+* B))
  定义体: { quotientEquiv I J (f : A ≃+* B) hIJ with
    commutes' r := by simp }

@[simp]

Depends on / 依赖: commutes, quotientEquiv
-/
def quotientEquivAlg (f : A ≃ₐ[R₁] B) (hIJ : J = I.map (f : A ->+* B)) :
    (A ⧸ I) ≃ₐ[R₁] B ⧸ J :=
  { quotientEquiv I J (f : A ≃+* B) hIJ with
    commutes' r := by simp }

@[simp]
/--
lemma `quotientEquivAlg_symm` / 引理 `quotientEquivAlg_symm`

English:
lemma quotientEquivAlg_symm
  given: (f : A ≃ₐ[R₁] B) (hIJ : J = I.map (f : A ->+* B))
  proof: rfl

@[simp]

中文:
引理 quotientEquivAlg_symm
  条件: (f : A ≃ₐ[R₁] B) (hIJ : J = I.map (f : A ->+* B))
  证明: rfl

@[simp]
-/
lemma quotientEquivAlg_symm (f : A ≃ₐ[R₁] B) (hIJ : J = I.map (f : A ->+* B)) :
    (quotientEquivAlg I J f hIJ).symm = quotientEquivAlg J I f.symm
      (by simp only [← AlgEquiv.toAlgHom_toRingHom, hIJ, map_map, ← AlgHom.comp_toRingHom,
        AlgEquiv.symm_comp, AlgHom.id_toRingHom, map_id]) :=
  rfl

@[simp]
/--
lemma `quotientEquivAlg_mk` / 引理 `quotientEquivAlg_mk`

English:
lemma quotientEquivAlg_mk
  given: (f : A ≃ₐ[R₁] B) (hIJ : J = I.map (f : A ->+* B)) (x : A)
  proof: rfl

中文:
引理 quotientEquivAlg_mk
  条件: (f : A ≃ₐ[R₁] B) (hIJ : J = I.map (f : A ->+* B)) (x : A)
  证明: rfl
-/
lemma quotientEquivAlg_mk (f : A ≃ₐ[R₁] B) (hIJ : J = I.map (f : A ->+* B)) (x : A) :
    Ideal.quotientEquivAlg I J f hIJ x = f x :=
  rfl

end

/--
Definition of `Quotient.algebraQuotientOfLEComap` / `Quotient.algebraQuotientOfLEComap` 的定义

English:
abbreviation Quotient.algebraQuotientOfLEComap
  signature: {R} [CommRing R] [Algebra R A] {p : Ideal R}
  body: quotientMap P (algebraMap R A) h
smul := Quotient.lift₂ (⟦· • ·⟧) fun r₁ a₁ r₂ a₂ hr ha => Quotient.sound by
    have := h (p.quotientRel_def.mp hr)
    rw [mem_comap]; rw [map_sub] at this
    simpa only [Algebra.smul_def] using P.quotientRel_def.mpr
      (P.mul_sub_mul_mem this <| P.quotientRel_d

中文:
缩写 商.algebraQuotientOfLEComap
  签名: {R} [交换环 R] [代数 R A] {p : 理想 R}
  定义体: quotientMap P (algebraMap R A) h
smul := Quotient.lift₂ (⟦· • ·⟧) fun r₁ a₁ r₂ a₂ hr ha => Quotient.sound by
    have := h (p.quotientRel_def.mp hr)
    rw [mem_comap]; rw [map_sub] at this
    simpa only [Algebra.smul_def] using P.quotientRel_def.mpr
      (P.mul_sub_mul_mem this <| P.quotientRel_d

Depends on / 依赖: algebraMap, quotientMap
-/
abbrev Quotient.algebraQuotientOfLEComap {R} [CommRing R] [Algebra R A] {p : Ideal R}
    {P : Ideal A} [P.IsTwoSided] (h : p <= comap (algebraMap R A) P) :
    Algebra (R ⧸ p) (A ⧸ P) where
  algebraMap := quotientMap P (algebraMap R A) h
smul := Quotient.lift₂ (⟦· • ·⟧) fun r₁ a₁ r₂ a₂ hr ha => Quotient.sound by
    have := h (p.quotientRel_def.mp hr)
    rw [mem_comap]; rw [map_sub] at this
    simpa only [Algebra.smul_def] using P.quotientRel_def.mpr
      (P.mul_sub_mul_mem this <| P.quotientRel_def.mp ha)
  smul_def' := by rintro ⟨_⟩ ⟨_⟩; exact congr_arg (⟦·⟧) (Algebra.smul_def _ _)
  commutes' := by rintro ⟨_⟩ ⟨_⟩; exact congr_arg (⟦·⟧) (Algebra.commutes _ _)

instance (priority := 100) quotientAlgebra {R} [CommRing R] {I : Ideal A} [I.IsTwoSided]
    [Algebra R A] : Algebra (R ⧸ I.comap (algebraMap R A)) (A ⧸ I) :=
  Quotient.algebraQuotientOfLEComap le_rfl

instance (R) {A} [CommRing R] [CommRing A] (I : Ideal A) [Algebra R A] :
    Algebra (R ⧸ I.comap (algebraMap R A)) (A ⧸ I) := inferInstance

/--
theorem `algebraMap_quotient_injective` / 定理 `algebraMap_quotient_injective`

English:
theorem algebraMap_quotient_injective
  given: {R} [CommRing R] {I : Ideal A} [I.IsTwoSided] [Algebra R A]
  proof: by
  rintro ⟨a⟩ ⟨b⟩ hab
  replace hab := Quotient.eq.mp hab
  rw [← map_sub] at hab
  exact Quotient.eq.mpr hab

中文:
定理 algebraMap_quotient_injective
  条件: {R} [交换环 R] {I : 理想 A} [I.是TwoSided] [代数 R A]
  证明: by
  rintro ⟨a⟩ ⟨b⟩ hab
  replace hab := Quotient.eq.mp hab
  rw [← map_sub] at hab
  exact Quotient.eq.mpr hab

Depends on / 依赖: Quotient, Quotient.eq.mp, Quotient.eq.mpr, map_sub, replace
-/
theorem algebraMap_quotient_injective {R} [CommRing R] {I : Ideal A} [I.IsTwoSided] [Algebra R A] :
    Function.Injective (algebraMap (R ⧸ I.comap (algebraMap R A)) (A ⧸ I)) := by
  rintro ⟨a⟩ ⟨b⟩ hab
  replace hab := Quotient.eq.mp hab
  rw [← map_sub] at hab
  exact Quotient.eq.mpr hab

variable (R₁)

/--
Definition of `quotientEquivAlgOfEq` / `quotientEquivAlgOfEq` 的定义

English:
definition quotientEquivAlgOfEq
  signature: {I J : Ideal A} [I.IsTwoSided] [J.IsTwoSided] (h : I = J)
  body: quotientEquivAlg I J AlgEquiv.refl h ▸ (map_id I).symm

@[simp]

中文:
定义 quotientEquivAlgOfEq
  签名: {I J : 理想 A} [I.是TwoSided] [J.是TwoSided] (h : I = J)
  定义体: quotientEquivAlg I J AlgEquiv.refl h ▸ (map_id I).symm

@[simp]

Depends on / 依赖: AlgEquiv, AlgEquiv.refl, map_id, quotientEquivAlg
-/
def quotientEquivAlgOfEq {I J : Ideal A} [I.IsTwoSided] [J.IsTwoSided] (h : I = J) :
    (A ⧸ I) ≃ₐ[R₁] A ⧸ J :=
quotientEquivAlg I J AlgEquiv.refl h ▸ (map_id I).symm

@[simp]
/--
theorem `quotientEquivAlgOfEq_mk` / 定理 `quotientEquivAlgOfEq_mk`

English:
theorem quotientEquivAlgOfEq_mk
  given: {I J : Ideal A} [I.IsTwoSided] [J.IsTwoSided] (h : I = J) (x : A)
  proof: rfl

@[simp]

中文:
定理 quotientEquivAlgOfEq_mk
  条件: {I J : 理想 A} [I.是TwoSided] [J.是TwoSided] (h : I = J) (x : A)
  证明: rfl

@[simp]
-/
theorem quotientEquivAlgOfEq_mk {I J : Ideal A} [I.IsTwoSided] [J.IsTwoSided] (h : I = J) (x : A) :
    quotientEquivAlgOfEq R₁ h (Ideal.Quotient.mk I x) = Ideal.Quotient.mk J x :=
  rfl

@[simp]
/--
theorem `quotientEquivAlgOfEq_coe_eq_factorₐ` / 定理 `quotientEquivAlgOfEq_coe_eq_factorₐ`

English:
theorem quotientEquivAlgOfEq_coe_eq_factorₐ
  proof: rfl

@[simp]

中文:
定理 quotientEquivAlgOfEq_coe_eq_factorₐ
  证明: rfl

@[simp]
-/
theorem quotientEquivAlgOfEq_coe_eq_factorₐ
    {I J : Ideal A} [I.IsTwoSided] [J.IsTwoSided] (h : I = J) :
    (quotientEquivAlgOfEq R₁ h : A ⧸ I ->ₐ[R₁] A ⧸ J) = Quotient.factorₐ R₁ (le_of_eq h) := rfl

@[simp]
/--
theorem `quotientEquivAlgOfEq_coe_eq_factor` / 定理 `quotientEquivAlgOfEq_coe_eq_factor`

English:
theorem quotientEquivAlgOfEq_coe_eq_factor
  proof: rfl

@[simp]

中文:
定理 quotientEquivAlgOfEq_coe_eq_factor
  证明: rfl

@[simp]
-/
theorem quotientEquivAlgOfEq_coe_eq_factor
    {I J : Ideal A} [I.IsTwoSided] [J.IsTwoSided] (h : I = J) :
    (quotientEquivAlgOfEq R₁ h : A ⧸ I ->+* A ⧸ J) = Quotient.factor (le_of_eq h) := rfl

@[simp]
/--
theorem `quotientEquivAlgOfEq_symm` / 定理 `quotientEquivAlgOfEq_symm`

English:
theorem quotientEquivAlgOfEq_symm
  given: {I J : Ideal A} [I.IsTwoSided] [J.IsTwoSided] (h : I = J)
  proof: by
  ext
  rfl

@[simp]

中文:
定理 quotientEquivAlgOfEq_symm
  条件: {I J : 理想 A} [I.是TwoSided] [J.是TwoSided] (h : I = J)
  证明: by
  ext
  rfl

@[simp]
-/
theorem quotientEquivAlgOfEq_symm {I J : Ideal A} [I.IsTwoSided] [J.IsTwoSided] (h : I = J) :
    (quotientEquivAlgOfEq R₁ h).symm = quotientEquivAlgOfEq R₁ h.symm := by
  ext
  rfl

@[simp]
/--
lemma `comap_map_quotientMk` / 引理 `comap_map_quotientMk`

English:
lemma comap_map_quotientMk
  given: (I J : Ideal R) [I.IsTwoSided]
  proof: by
  ext x
  simp only [mem_comap, mem_quotient_iff_mem_sup, sup_comm]

中文:
引理 comap_map_quotientMk
  条件: (I J : 理想 R) [I.是TwoSided]
  证明: by
  ext x
  simp only [mem_comap, mem_quotient_iff_mem_sup, sup_comm]

Depends on / 依赖: mem_comap, mem_quotient_iff_mem_sup, sup_comm
-/
lemma comap_map_quotientMk (I J : Ideal R) [I.IsTwoSided] :
    (J.map <| Ideal.Quotient.mk I).comap (Ideal.Quotient.mk I) = I ⊔ J := by
  ext x
  simp only [mem_comap, mem_quotient_iff_mem_sup, sup_comm]

/--
lemma `comap_map_mk` / 引理 `comap_map_mk`

English:
lemma comap_map_mk
  given: {I J : Ideal R} [I.IsTwoSided] (h : I <= J)
  proof: by
  simpa

中文:
引理 comap_map_mk
  条件: {I J : 理想 R} [I.是TwoSided] (h : I <= J)
  证明: by
  simpa
-/
lemma comap_map_mk {I J : Ideal R} [I.IsTwoSided] (h : I <= J) :
    Ideal.comap (Ideal.Quotient.mk I) (Ideal.map (Ideal.Quotient.mk I) J) = J := by
  simpa

/--
lemma `isPrime_map_quotientMk_of_isPrime` / 引理 `isPrime_map_quotientMk_of_isPrime`

English:
lemma isPrime_map_quotientMk_of_isPrime
  statement: {I : Ideal R} [I.IsTwoSided] {p : Ideal R}
  proof: by
  apply Ideal.map_isPrime_of_surjective
  · exact Quotient.mk_surjective
  · simpa

中文:
引理 isPrime_map_quotientMk_of_isPrime
  结论: {I : 理想 R} [I.是TwoSided] {p : 理想 R}
  证明: by
  apply Ideal.map_isPrime_of_surjective
  · exact Quotient.mk_surjective
  · simpa

Depends on / 依赖: Ideal.map_isPrime_of_surjective, Quotient, Quotient.mk_surjective, map_isPrime_of_surjective, mk_surjective
-/
lemma isPrime_map_quotientMk_of_isPrime {I : Ideal R} [I.IsTwoSided] {p : Ideal R}
    [p.IsPrime] (hIP : I <= p) : (p.map (Ideal.Quotient.mk I)).IsPrime := by
  apply Ideal.map_isPrime_of_surjective
  · exact Quotient.mk_surjective
  · simpa

/--
Definition of `quotientKerEquivRange` / `quotientKerEquivRange` 的定义

English:
definition quotientKerEquivRange
  body: (Ideal.quotientEquivAlgOfEq R (AlgHom.ker_rangeRestrict f).symm).trans
    Ideal.quotientKerAlgEquivOfSurjective f.rangeRestrict_surjective

中文:
定义 quotientKerEquivRange
  定义体: (Ideal.quotientEquivAlgOfEq R (AlgHom.ker_rangeRestrict f).symm).trans
    Ideal.quotientKerAlgEquivOfSurjective f.rangeRestrict_surjective

Depends on / 依赖: AlgHom, AlgHom.ker_rangeRestrict, Ideal.quotientEquivAlgOfEq, Ideal.quotientKerAlgEquivOfSurjective, f.rangeRestrict_surjective, ker_rangeRestrict, quotientEquivAlgOfEq, quotientKerAlgEquivOfSurjective, rangeRestrict_surjective
-/
noncomputable def quotientKerEquivRange
    {R A B : Type*} [CommSemiring R] [Ring A] [Algebra R A] [Semiring B] [Algebra R B]
    (f : A ->ₐ[R] B) :
    (A ⧸ RingHom.ker f) ≃ₐ[R] f.range :=
(Ideal.quotientEquivAlgOfEq R (AlgHom.ker_rangeRestrict f).symm).trans
    Ideal.quotientKerAlgEquivOfSurjective f.rangeRestrict_surjective

end QuotientAlgebra

end Ideal

section quotientBot

variable {R S : Type*}

variable (R) in
/--
Definition of `RingEquiv.quotientBot` / `RingEquiv.quotientBot` 的定义

English:
definition RingEquiv.quotientBot
  signature: [Ring R]
  body: (Ideal.quotEquivOfEq (RingHom.ker_coe_equiv <| .refl _).symm).trans
    RingHom.quotientKerEquivOfRightInverse (f := .id R) (g := _root_.id) fun _ => rfl

@[simp]

中文:
定义 环等价.quotientBot
  签名: [环 R]
  定义体: (Ideal.quotEquivOfEq (RingHom.ker_coe_equiv <| .refl _).symm).trans
    RingHom.quotientKerEquivOfRightInverse (f := .id R) (g := _root_.id) fun _ => rfl

@[simp]

Depends on / 依赖: Ideal.quotEquivOfEq, RingHom, RingHom.ker_coe_equiv, RingHom.quotientKerEquivOfRightInverse, _root_, _root_.id, ker_coe_equiv, quotEquivOfEq, quotientKerEquivOfRightInverse
-/
def RingEquiv.quotientBot [Ring R] : R ⧸ (⊥ : Ideal R) ≃+* R :=
(Ideal.quotEquivOfEq (RingHom.ker_coe_equiv <| .refl _).symm).trans
    RingHom.quotientKerEquivOfRightInverse (f := .id R) (g := _root_.id) fun _ => rfl

@[simp]
/--
lemma `RingEquiv.quotientBot_mk` / 引理 `RingEquiv.quotientBot_mk`

English:
lemma RingEquiv.quotientBot_mk
  given: [Ring R] (r : R)
  proof: rfl

@[simp]

中文:
引理 环等价.quotientBot_mk
  条件: [环 R] (r : R)
  证明: rfl

@[simp]
-/
lemma RingEquiv.quotientBot_mk [Ring R] (r : R) :
    RingEquiv.quotientBot R (Ideal.Quotient.mk ⊥ r) = r :=
  rfl

@[simp]
/--
lemma `RingEquiv.quotientBot_symm_mk` / 引理 `RingEquiv.quotientBot_symm_mk`

English:
lemma RingEquiv.quotientBot_symm_mk
  given: [Ring R] (r : R)
  proof: rfl

中文:
引理 环等价.quotientBot_symm_mk
  条件: [环 R] (r : R)
  证明: rfl
-/
lemma RingEquiv.quotientBot_symm_mk [Ring R] (r : R) :
    (RingEquiv.quotientBot R).symm r = r :=
  rfl

variable (R S) in
/--
Definition of `AlgEquiv.quotientBot` / `AlgEquiv.quotientBot` 的定义

English:
definition AlgEquiv.quotientBot
  signature: [CommSemiring R] [Ring S] [Algebra R S]
  body: RingEquiv.quotientBot S
  commutes' x := by simp [← Ideal.Quotient.mk_algebraMap]

@[simp]

中文:
定义 代数等价.quotientBot
  签名: [交换半环 R] [环 S] [代数 R S]
  定义体: RingEquiv.quotientBot S
  commutes' x := by simp [← Ideal.Quotient.mk_algebraMap]

@[simp]

Depends on / 依赖: RingEquiv, RingEquiv.quotientBot, quotientBot
-/
def AlgEquiv.quotientBot [CommSemiring R] [Ring S] [Algebra R S] :
    (S ⧸ (⊥ : Ideal S)) ≃ₐ[R] S where
  __ := RingEquiv.quotientBot S
  commutes' x := by simp [← Ideal.Quotient.mk_algebraMap]

@[simp]
/--
lemma `AlgEquiv.quotientBot_mk` / 引理 `AlgEquiv.quotientBot_mk`

English:
lemma AlgEquiv.quotientBot_mk
  given: [CommSemiring R] [CommRing S] [Algebra R S] (s : S)
  proof: rfl

@[simp]

中文:
引理 代数等价.quotientBot_mk
  条件: [交换半环 R] [交换环 S] [代数 R S] (s : S)
  证明: rfl

@[simp]
-/
lemma AlgEquiv.quotientBot_mk [CommSemiring R] [CommRing S] [Algebra R S] (s : S) :
    AlgEquiv.quotientBot R S (Ideal.Quotient.mk ⊥ s) = s :=
  rfl

@[simp]
/--
lemma `AlgEquiv.quotientBot_symm_mk` / 引理 `AlgEquiv.quotientBot_symm_mk`

English:
lemma AlgEquiv.quotientBot_symm_mk
  statement: [CommSemiring R] [CommRing S] [Algebra R S]
  proof: rfl

中文:
引理 代数等价.quotientBot_symm_mk
  结论: [交换半环 R] [交换环 S] [代数 R S]
  证明: rfl
-/
lemma AlgEquiv.quotientBot_symm_mk [CommSemiring R] [CommRing S] [Algebra R S]
    (s : S) : (AlgEquiv.quotientBot R S).symm s = s :=
  rfl

end quotientBot

namespace DoubleQuot

open Ideal

variable {R : Type u}

section

variable [CommRing R] (I J : Ideal R)

/--
Definition of `quotLeftToQuotSup` / `quotLeftToQuotSup` 的定义

English:
definition quotLeftToQuotSup
  signature: : R ⧸ I ->+* R ⧸ I ⊔ J
  body: Ideal.Quotient.factor le_sup_left

中文:
定义 quotLeftToQuotSup
  签名: : R ⧸ I ->+* R ⧸ I ⊔ J
  定义体: Ideal.Quotient.factor le_sup_left

Depends on / 依赖: Ideal.Quotient.factor, Quotient, factor, le_sup_left
-/
def quotLeftToQuotSup : R ⧸ I ->+* R ⧸ I ⊔ J :=
  Ideal.Quotient.factor le_sup_left

set_option backward.isDefEq.respectTransparency false in
/--
theorem `ker_quotLeftToQuotSup` / 定理 `ker_quotLeftToQuotSup`

English:
theorem ker_quotLeftToQuotSup
  statement: RingHom.ker (quotLeftToQuotSup I J) =
  proof: by
  simp only [mk_ker, sup_idem, sup_comm, quotLeftToQuotSup, Quotient.factor, ker_quotient_lift,
    map_eq_iff_sup_ker_eq_of_surjective (Ideal.Quotient.mk I) Quotient.mk_surjective, ← sup_assoc]

中文:
定理 ker_quotLeftToQuotSup
  结论: 环态射.ker (quotLeftToQuotSup I J) =
  证明: by
  simp only [mk_ker, sup_idem, sup_comm, quotLeftToQuotSup, Quotient.factor, ker_quotient_lift,
    map_eq_iff_sup_ker_eq_of_surjective (Ideal.Quotient.mk I) Quotient.mk_surjective, ← sup_assoc]

Depends on / 依赖: Ideal.Quotient.mk, Quotient, Quotient.factor, Quotient.mk_surjective, factor, ker_quotient_lift, map_eq_iff_sup_ker_eq_of_surjective, mk_ker, mk_surjective, quotLeftToQuotSup, sup_assoc, sup_comm, sup_idem
-/
theorem ker_quotLeftToQuotSup : RingHom.ker (quotLeftToQuotSup I J) =
    J.map (Ideal.Quotient.mk I) := by
  simp only [mk_ker, sup_idem, sup_comm, quotLeftToQuotSup, Quotient.factor, ker_quotient_lift,
    map_eq_iff_sup_ker_eq_of_surjective (Ideal.Quotient.mk I) Quotient.mk_surjective, ← sup_assoc]

/--
Definition of `quotQuotToQuotSup` / `quotQuotToQuotSup` 的定义

English:
definition quotQuotToQuotSup
  signature: : (R ⧸ I) ⧸ J.map (Ideal.Quotient.mk I) ->+* R ⧸ I ⊔ J
  body: Ideal.Quotient.lift (J.map (Ideal.Quotient.mk I)) (quotLeftToQuotSup I J)
    (ker_quotLeftToQuotSup I J).symm.le

中文:
定义 quotQuotToQuotSup
  签名: : (R ⧸ I) ⧸ J.map (理想.商.mk I) ->+* R ⧸ I ⊔ J
  定义体: Ideal.Quotient.lift (J.map (Ideal.Quotient.mk I)) (quotLeftToQuotSup I J)
    (ker_quotLeftToQuotSup I J).symm.le

Depends on / 依赖: Ideal.Quotient.lift, Ideal.Quotient.mk, J.map, Quotient, ker_quotLeftToQuotSup, quotLeftToQuotSup, symm.le
-/
def quotQuotToQuotSup : (R ⧸ I) ⧸ J.map (Ideal.Quotient.mk I) ->+* R ⧸ I ⊔ J :=
  Ideal.Quotient.lift (J.map (Ideal.Quotient.mk I)) (quotLeftToQuotSup I J)
    (ker_quotLeftToQuotSup I J).symm.le

/--
Definition of `quotQuotMk` / `quotQuotMk` 的定义

English:
definition quotQuotMk
  signature: : R ->+* (R ⧸ I) ⧸ J.map (Ideal.Quotient.mk I)
  body: (Ideal.Quotient.mk (J.map (Ideal.Quotient.mk I))).comp (Ideal.Quotient.mk I)

中文:
定义 quotQuotMk
  签名: : R ->+* (R ⧸ I) ⧸ J.map (理想.商.mk I)
  定义体: (Ideal.Quotient.mk (J.map (Ideal.Quotient.mk I))).comp (Ideal.Quotient.mk I)

Depends on / 依赖: Ideal.Quotient.mk, J.map, Quotient
-/
def quotQuotMk : R ->+* (R ⧸ I) ⧸ J.map (Ideal.Quotient.mk I) :=
  (Ideal.Quotient.mk (J.map (Ideal.Quotient.mk I))).comp (Ideal.Quotient.mk I)

/--
theorem `ker_quotQuotMk` / 定理 `ker_quotQuotMk`

English:
theorem ker_quotQuotMk
  statement: RingHom.ker (quotQuotMk I J) = I ⊔ J
  proof: by
  rw [RingHom.ker_eq_comap_bot]; rw [quotQuotMk]; rw [← comap_comap]; rw [← RingHom.ker]; rw [mk_ker]; rw [comap_map_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective]; rw [← RingHom.ker]; rw [mk_ker]; rw [sup_comm]

中文:
定理 ker_quotQuotMk
  结论: 环态射.ker (quotQuotMk I J) = I ⊔ J
  证明: by
  rw [RingHom.ker_eq_comap_bot]; rw [quotQuotMk]; rw [← comap_comap]; rw [← RingHom.ker]; rw [mk_ker]; rw [comap_map_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective]; rw [← RingHom.ker]; rw [mk_ker]; rw [sup_comm]

Depends on / 依赖: Ideal.Quotient.mk, Ideal.Quotient.mk_surjective, Quotient, RingHom, RingHom.ker, RingHom.ker_eq_comap_bot, comap_comap, comap_map_of_surjective, ker_eq_comap_bot, mk_ker, mk_surjective, quotQuotMk, sup_comm
-/
theorem ker_quotQuotMk : RingHom.ker (quotQuotMk I J) = I ⊔ J := by
  rw [RingHom.ker_eq_comap_bot]; rw [quotQuotMk]; rw [← comap_comap]; rw [← RingHom.ker]; rw [mk_ker]; rw [comap_map_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective]; rw [← RingHom.ker]; rw [mk_ker]; rw [sup_comm]

/--
Definition of `liftSupQuotQuotMk` / `liftSupQuotQuotMk` 的定义

English:
definition liftSupQuotQuotMk
  signature: (I J : Ideal R)
  body: Ideal.Quotient.lift (I ⊔ J) (quotQuotMk I J) (ker_quotQuotMk I J).symm.le

中文:
定义 liftSupQuotQuotMk
  签名: (I J : 理想 R)
  定义体: Ideal.Quotient.lift (I ⊔ J) (quotQuotMk I J) (ker_quotQuotMk I J).symm.le

Depends on / 依赖: Ideal.Quotient.lift, Quotient, ker_quotQuotMk, quotQuotMk, symm.le
-/
def liftSupQuotQuotMk (I J : Ideal R) : R ⧸ I ⊔ J ->+* (R ⧸ I) ⧸ J.map (Ideal.Quotient.mk I) :=
  Ideal.Quotient.lift (I ⊔ J) (quotQuotMk I J) (ker_quotQuotMk I J).symm.le

/--
Definition of `quotQuotEquivQuotSup` / `quotQuotEquivQuotSup` 的定义

English:
definition quotQuotEquivQuotSup
  signature: : (R ⧸ I) ⧸ J.map (Ideal.Quotient.mk I) ≃+* R ⧸ I ⊔ J
  body: RingEquiv.ofRingHom (quotQuotToQuotSup I J) (liftSupQuotQuotMk I J)
    (by
      repeat apply Ideal.Quotient.ringHom_ext
      rfl)
    (by
      repeat apply Ideal.Quotient.ringHom_ext
      rfl)

@[simp]

中文:
定义 quotQuotEquivQuotSup
  签名: : (R ⧸ I) ⧸ J.map (理想.商.mk I) ≃+* R ⧸ I ⊔ J
  定义体: RingEquiv.ofRingHom (quotQuotToQuotSup I J) (liftSupQuotQuotMk I J)
    (by
      repeat apply Ideal.Quotient.ringHom_ext
      rfl)
    (by
      repeat apply Ideal.Quotient.ringHom_ext
      rfl)

@[simp]

Depends on / 依赖: Ideal.Quotient.ringHom_ext, Quotient, RingEquiv, RingEquiv.ofRingHom, liftSupQuotQuotMk, ofRingHom, quotQuotToQuotSup, repeat, ringHom_ext
-/
def quotQuotEquivQuotSup : (R ⧸ I) ⧸ J.map (Ideal.Quotient.mk I) ≃+* R ⧸ I ⊔ J :=
  RingEquiv.ofRingHom (quotQuotToQuotSup I J) (liftSupQuotQuotMk I J)
    (by
      repeat apply Ideal.Quotient.ringHom_ext
      rfl)
    (by
      repeat apply Ideal.Quotient.ringHom_ext
      rfl)

@[simp]
/--
theorem `quotQuotEquivQuotSup_quotQuotMk` / 定理 `quotQuotEquivQuotSup_quotQuotMk`

English:
theorem quotQuotEquivQuotSup_quotQuotMk
  given: (x : R)
  proof: rfl

@[simp]

中文:
定理 quotQuotEquivQuotSup_quotQuotMk
  条件: (x : R)
  证明: rfl

@[simp]
-/
theorem quotQuotEquivQuotSup_quotQuotMk (x : R) :
    quotQuotEquivQuotSup I J (quotQuotMk I J x) = Ideal.Quotient.mk (I ⊔ J) x :=
  rfl

@[simp]
/--
theorem `quotQuotEquivQuotSup_symm_quotQuotMk` / 定理 `quotQuotEquivQuotSup_symm_quotQuotMk`

English:
theorem quotQuotEquivQuotSup_symm_quotQuotMk
  given: (x : R)
  proof: rfl

中文:
定理 quotQuotEquivQuotSup_symm_quotQuotMk
  条件: (x : R)
  证明: rfl
-/
theorem quotQuotEquivQuotSup_symm_quotQuotMk (x : R) :
    (quotQuotEquivQuotSup I J).symm (Ideal.Quotient.mk (I ⊔ J) x) = quotQuotMk I J x :=
  rfl

/--
Definition of `quotQuotEquivComm` / `quotQuotEquivComm` 的定义

English:
definition quotQuotEquivComm
  signature: : (R ⧸ I) ⧸ J.map (Ideal.Quotient.mk I) ≃+*
  body: ((quotQuotEquivQuotSup I J).trans (quotEquivOfEq (sup_comm ..))).trans
    (quotQuotEquivQuotSup J I).symm

@[simp]

中文:
定义 quotQuotEquivComm
  签名: : (R ⧸ I) ⧸ J.map (理想.商.mk I) ≃+*
  定义体: ((quotQuotEquivQuotSup I J).trans (quotEquivOfEq (sup_comm ..))).trans
    (quotQuotEquivQuotSup J I).symm

@[simp]

Depends on / 依赖: quotEquivOfEq, quotQuotEquivQuotSup, sup_comm
-/
def quotQuotEquivComm : (R ⧸ I) ⧸ J.map (Ideal.Quotient.mk I) ≃+*
    (R ⧸ J) ⧸ I.map (Ideal.Quotient.mk J) :=
  ((quotQuotEquivQuotSup I J).trans (quotEquivOfEq (sup_comm ..))).trans
    (quotQuotEquivQuotSup J I).symm

@[simp]
/--
theorem `quotQuotEquivComm_quotQuotMk` / 定理 `quotQuotEquivComm_quotQuotMk`

English:
theorem quotQuotEquivComm_quotQuotMk
  given: (x : R)
  proof: rfl

@[simp]

中文:
定理 quotQuotEquivComm_quotQuotMk
  条件: (x : R)
  证明: rfl

@[simp]
-/
theorem quotQuotEquivComm_quotQuotMk (x : R) :
    quotQuotEquivComm I J (quotQuotMk I J x) = quotQuotMk J I x :=
  rfl

@[simp]
/--
theorem `quotQuotEquivComm_comp_quotQuotMk` / 定理 `quotQuotEquivComm_comp_quotQuotMk`

English:
theorem quotQuotEquivComm_comp_quotQuotMk
  proof: RingHom.ext quotQuotEquivComm_quotQuotMk I J

@[simp]

中文:
定理 quotQuotEquivComm_comp_quotQuotMk
  证明: RingHom.ext quotQuotEquivComm_quotQuotMk I J

@[simp]

Depends on / 依赖: RingHom, RingHom.ext, quotQuotEquivComm_quotQuotMk
-/
theorem quotQuotEquivComm_comp_quotQuotMk :
    RingHom.comp (↑(quotQuotEquivComm I J)) (quotQuotMk I J) = quotQuotMk J I :=
RingHom.ext quotQuotEquivComm_quotQuotMk I J

@[simp]
/--
theorem `quotQuotEquivComm_symm` / 定理 `quotQuotEquivComm_symm`

English:
theorem quotQuotEquivComm_symm
  statement: (quotQuotEquivComm I J).symm = quotQuotEquivComm J I
  proof: by
  rfl

中文:
定理 quotQuotEquivComm_symm
  结论: (quotQuotEquivComm I J).symm = quotQuotEquivComm J I
  证明: by
  rfl
-/
theorem quotQuotEquivComm_symm : (quotQuotEquivComm I J).symm = quotQuotEquivComm J I := by
  rfl

variable {I J}

/--
Definition of `quotQuotEquivQuotOfLE` / `quotQuotEquivQuotOfLE` 的定义

English:
definition quotQuotEquivQuotOfLE
  signature: (h : I <= J)
  body: (quotQuotEquivQuotSup I J).trans (Ideal.quotEquivOfEq <| sup_eq_right.mpr h)

@[simp]

中文:
定义 quotQuotEquivQuotOfLE
  签名: (h : I <= J)
  定义体: (quotQuotEquivQuotSup I J).trans (Ideal.quotEquivOfEq <| sup_eq_right.mpr h)

@[simp]

Depends on / 依赖: Ideal.quotEquivOfEq, quotEquivOfEq, quotQuotEquivQuotSup, sup_eq_right, sup_eq_right.mpr
-/
def quotQuotEquivQuotOfLE (h : I <= J) : (R ⧸ I) ⧸ J.map (Ideal.Quotient.mk I) ≃+* R ⧸ J :=
  (quotQuotEquivQuotSup I J).trans (Ideal.quotEquivOfEq <| sup_eq_right.mpr h)

@[simp]
/--
theorem `quotQuotEquivQuotOfLE_quotQuotMk` / 定理 `quotQuotEquivQuotOfLE_quotQuotMk`

English:
theorem quotQuotEquivQuotOfLE_quotQuotMk
  given: (x : R) (h : I <= J)
  proof: rfl

@[simp]

中文:
定理 quotQuotEquivQuotOfLE_quotQuotMk
  条件: (x : R) (h : I <= J)
  证明: rfl

@[simp]
-/
theorem quotQuotEquivQuotOfLE_quotQuotMk (x : R) (h : I <= J) :
    quotQuotEquivQuotOfLE h (quotQuotMk I J x) = (Ideal.Quotient.mk J) x :=
  rfl

@[simp]
/--
theorem `quotQuotEquivQuotOfLE_symm_mk` / 定理 `quotQuotEquivQuotOfLE_symm_mk`

English:
theorem quotQuotEquivQuotOfLE_symm_mk
  given: (x : R) (h : I <= J)
  proof: rfl

中文:
定理 quotQuotEquivQuotOfLE_symm_mk
  条件: (x : R) (h : I <= J)
  证明: rfl
-/
theorem quotQuotEquivQuotOfLE_symm_mk (x : R) (h : I <= J) :
    (quotQuotEquivQuotOfLE h).symm ((Ideal.Quotient.mk J) x) = quotQuotMk I J x :=
  rfl

/--
theorem `quotQuotEquivQuotOfLE_comp_quotQuotMk` / 定理 `quotQuotEquivQuotOfLE_comp_quotQuotMk`

English:
theorem quotQuotEquivQuotOfLE_comp_quotQuotMk
  given: (h : I <= J)
  proof: by
  ext
  rfl

中文:
定理 quotQuotEquivQuotOfLE_comp_quotQuotMk
  条件: (h : I <= J)
  证明: by
  ext
  rfl
-/
theorem quotQuotEquivQuotOfLE_comp_quotQuotMk (h : I <= J) :
    RingHom.comp (↑(quotQuotEquivQuotOfLE h)) (quotQuotMk I J) = (Ideal.Quotient.mk J) := by
  ext
  rfl

/--
theorem `quotQuotEquivQuotOfLE_symm_comp_mk` / 定理 `quotQuotEquivQuotOfLE_symm_comp_mk`

English:
theorem quotQuotEquivQuotOfLE_symm_comp_mk
  given: (h : I <= J)
  proof: by
  ext
  rfl

中文:
定理 quotQuotEquivQuotOfLE_symm_comp_mk
  条件: (h : I <= J)
  证明: by
  ext
  rfl
-/
theorem quotQuotEquivQuotOfLE_symm_comp_mk (h : I <= J) :
    RingHom.comp (↑(quotQuotEquivQuotOfLE h).symm) (Ideal.Quotient.mk J) = quotQuotMk I J := by
  ext
  rfl

end

section Algebra

@[simp]
/--
theorem `quotQuotEquivComm_mk_mk` / 定理 `quotQuotEquivComm_mk_mk`

English:
theorem quotQuotEquivComm_mk_mk
  given: [CommRing R] (I J : Ideal R) (x : R)
  proof: rfl

中文:
定理 quotQuotEquivComm_mk_mk
  条件: [交换环 R] (I J : 理想 R) (x : R)
  证明: rfl
-/
theorem quotQuotEquivComm_mk_mk [CommRing R] (I J : Ideal R) (x : R) :
    quotQuotEquivComm I J (Ideal.Quotient.mk _ (Ideal.Quotient.mk _ x)) = algebraMap R _ x :=
  rfl

variable [CommSemiring R] {A : Type v} [CommRing A] [Algebra R A] (I J : Ideal A)

@[simp]
/--
theorem `quotQuotEquivQuotSup_quot_quot_algebraMap` / 定理 `quotQuotEquivQuotSup_quot_quot_algebraMap`

English:
theorem quotQuotEquivQuotSup_quot_quot_algebraMap
  given: (x : R)
  proof: rfl

@[simp]

中文:
定理 quotQuotEquivQuotSup_quot_quot_algebraMap
  条件: (x : R)
  证明: rfl

@[simp]
-/
theorem quotQuotEquivQuotSup_quot_quot_algebraMap (x : R) :
    DoubleQuot.quotQuotEquivQuotSup I J (algebraMap R _ x) = algebraMap _ _ x :=
  rfl

@[simp]
/--
theorem `quotQuotEquivComm_algebraMap` / 定理 `quotQuotEquivComm_algebraMap`

English:
theorem quotQuotEquivComm_algebraMap
  given: (x : R)
  proof: rfl

中文:
定理 quotQuotEquivComm_algebraMap
  条件: (x : R)
  证明: rfl
-/
theorem quotQuotEquivComm_algebraMap (x : R) :
    quotQuotEquivComm I J (algebraMap R _ x) = algebraMap _ _ x :=
  rfl

end Algebra

section AlgebraQuotient

variable (R) {A : Type*} [CommSemiring R] [CommRing A] [Algebra R A] (I J : Ideal A)

/--
Definition of `quotLeftToQuotSupₐ` / `quotLeftToQuotSupₐ` 的定义

English:
definition quotLeftToQuotSupₐ
  signature: : A ⧸ I ->ₐ[R] A ⧸ I ⊔ J
  body: AlgHom.mk (quotLeftToQuotSup I J) fun _ => rfl

@[simp]

中文:
定义 quotLeftToQuotSupₐ
  签名: : A ⧸ I ->ₐ[R] A ⧸ I ⊔ J
  定义体: AlgHom.mk (quotLeftToQuotSup I J) fun _ => rfl

@[simp]

Depends on / 依赖: AlgHom, AlgHom.mk, quotLeftToQuotSup
-/
def quotLeftToQuotSupₐ : A ⧸ I ->ₐ[R] A ⧸ I ⊔ J :=
  AlgHom.mk (quotLeftToQuotSup I J) fun _ => rfl

@[simp]
/--
theorem `quotLeftToQuotSupₐ_toRingHom` / 定理 `quotLeftToQuotSupₐ_toRingHom`

English:
theorem quotLeftToQuotSupₐ_toRingHom
  proof: rfl

@[simp]

中文:
定理 quotLeftToQuotSupₐ_toRingHom
  证明: rfl

@[simp]
-/
theorem quotLeftToQuotSupₐ_toRingHom :
    (quotLeftToQuotSupₐ R I J : _ ->+* _) = quotLeftToQuotSup I J :=
  rfl

@[simp]
/--
theorem `coe_quotLeftToQuotSupₐ` / 定理 `coe_quotLeftToQuotSupₐ`

English:
theorem coe_quotLeftToQuotSupₐ
  statement: ⇑(quotLeftToQuotSupₐ R I J) = quotLeftToQuotSup I J
  proof: rfl

中文:
定理 coe_quotLeftToQuotSupₐ
  结论: ⇑(quotLeftToQuotSupₐ R I J) = quotLeftToQuotSup I J
  证明: rfl
-/
theorem coe_quotLeftToQuotSupₐ : ⇑(quotLeftToQuotSupₐ R I J) = quotLeftToQuotSup I J :=
  rfl

/--
Definition of `quotQuotToQuotSupₐ` / `quotQuotToQuotSupₐ` 的定义

English:
definition quotQuotToQuotSupₐ
  signature: : (A ⧸ I) ⧸ J.map (Quotient.mkₐ R I) ->ₐ[R] A ⧸ I ⊔ J
  body: AlgHom.mk (quotQuotToQuotSup I J) fun _ => rfl

@[simp]

中文:
定义 quotQuotToQuotSupₐ
  签名: : (A ⧸ I) ⧸ J.map (商.mkₐ R I) ->ₐ[R] A ⧸ I ⊔ J
  定义体: AlgHom.mk (quotQuotToQuotSup I J) fun _ => rfl

@[simp]

Depends on / 依赖: AlgHom, AlgHom.mk, quotQuotToQuotSup
-/
def quotQuotToQuotSupₐ : (A ⧸ I) ⧸ J.map (Quotient.mkₐ R I) ->ₐ[R] A ⧸ I ⊔ J :=
  AlgHom.mk (quotQuotToQuotSup I J) fun _ => rfl

@[simp]
/--
theorem `quotQuotToQuotSupₐ_toRingHom` / 定理 `quotQuotToQuotSupₐ_toRingHom`

English:
theorem quotQuotToQuotSupₐ_toRingHom
  proof: rfl

@[simp]

中文:
定理 quotQuotToQuotSupₐ_toRingHom
  证明: rfl

@[simp]
-/
theorem quotQuotToQuotSupₐ_toRingHom :
    ((quotQuotToQuotSupₐ R I J) : _ ⧸ map (Ideal.Quotient.mkₐ R I) J ->+* _) =
      quotQuotToQuotSup I J :=
  rfl

@[simp]
/--
theorem `coe_quotQuotToQuotSupₐ` / 定理 `coe_quotQuotToQuotSupₐ`

English:
theorem coe_quotQuotToQuotSupₐ
  statement: ⇑(quotQuotToQuotSupₐ R I J) = quotQuotToQuotSup I J
  proof: rfl

中文:
定理 coe_quotQuotToQuotSupₐ
  结论: ⇑(quotQuotToQuotSupₐ R I J) = quotQuotToQuotSup I J
  证明: rfl
-/
theorem coe_quotQuotToQuotSupₐ : ⇑(quotQuotToQuotSupₐ R I J) = quotQuotToQuotSup I J :=
  rfl

/--
Definition of `quotQuotMkₐ` / `quotQuotMkₐ` 的定义

English:
definition quotQuotMkₐ
  signature: : A ->ₐ[R] (A ⧸ I) ⧸ J.map (Quotient.mkₐ R I)
  body: AlgHom.mk (quotQuotMk I J) fun _ => rfl

@[simp]

中文:
定义 quotQuotMkₐ
  签名: : A ->ₐ[R] (A ⧸ I) ⧸ J.map (商.mkₐ R I)
  定义体: AlgHom.mk (quotQuotMk I J) fun _ => rfl

@[simp]

Depends on / 依赖: AlgHom, AlgHom.mk, quotQuotMk
-/
def quotQuotMkₐ : A ->ₐ[R] (A ⧸ I) ⧸ J.map (Quotient.mkₐ R I) :=
  AlgHom.mk (quotQuotMk I J) fun _ => rfl

@[simp]
/--
theorem `quotQuotMkₐ_toRingHom` / 定理 `quotQuotMkₐ_toRingHom`

English:
theorem quotQuotMkₐ_toRingHom
  proof: rfl

@[simp]

中文:
定理 quotQuotMkₐ_toRingHom
  证明: rfl

@[simp]
-/
theorem quotQuotMkₐ_toRingHom :
    (quotQuotMkₐ R I J : _ ->+* _ ⧸ J.map (Quotient.mkₐ R I)) = quotQuotMk I J :=
  rfl

@[simp]
/--
theorem `coe_quotQuotMkₐ` / 定理 `coe_quotQuotMkₐ`

English:
theorem coe_quotQuotMkₐ
  statement: ⇑(quotQuotMkₐ R I J) = quotQuotMk I J
  proof: rfl

中文:
定理 coe_quotQuotMkₐ
  结论: ⇑(quotQuotMkₐ R I J) = quotQuotMk I J
  证明: rfl
-/
theorem coe_quotQuotMkₐ : ⇑(quotQuotMkₐ R I J) = quotQuotMk I J :=
  rfl

/--
Definition of `liftSupQuotQuotMkₐ` / `liftSupQuotQuotMkₐ` 的定义

English:
definition liftSupQuotQuotMkₐ
  signature: (I J : Ideal A)
  body: AlgHom.mk (liftSupQuotQuotMk I J) fun _ => rfl

@[simp]

中文:
定义 liftSupQuotQuotMkₐ
  签名: (I J : 理想 A)
  定义体: AlgHom.mk (liftSupQuotQuotMk I J) fun _ => rfl

@[simp]

Depends on / 依赖: AlgHom, AlgHom.mk, liftSupQuotQuotMk
-/
def liftSupQuotQuotMkₐ (I J : Ideal A) : A ⧸ I ⊔ J ->ₐ[R] (A ⧸ I) ⧸ J.map (Quotient.mkₐ R I) :=
  AlgHom.mk (liftSupQuotQuotMk I J) fun _ => rfl

@[simp]
/--
theorem `liftSupQuotQuotMkₐ_toRingHom` / 定理 `liftSupQuotQuotMkₐ_toRingHom`

English:
theorem liftSupQuotQuotMkₐ_toRingHom
  proof: rfl

@[simp]

中文:
定理 liftSupQuotQuotMkₐ_toRingHom
  证明: rfl

@[simp]
-/
theorem liftSupQuotQuotMkₐ_toRingHom :
    (liftSupQuotQuotMkₐ R I J : _ ->+* _ ⧸ J.map (Quotient.mkₐ R I)) = liftSupQuotQuotMk I J :=
  rfl

@[simp]
/--
theorem `coe_liftSupQuotQuotMkₐ` / 定理 `coe_liftSupQuotQuotMkₐ`

English:
theorem coe_liftSupQuotQuotMkₐ
  statement: ⇑(liftSupQuotQuotMkₐ R I J) = liftSupQuotQuotMk I J
  proof: rfl

中文:
定理 coe_liftSupQuotQuotMkₐ
  结论: ⇑(liftSupQuotQuotMkₐ R I J) = liftSupQuotQuotMk I J
  证明: rfl
-/
theorem coe_liftSupQuotQuotMkₐ : ⇑(liftSupQuotQuotMkₐ R I J) = liftSupQuotQuotMk I J :=
  rfl

/--
Definition of `quotQuotEquivQuotSupₐ` / `quotQuotEquivQuotSupₐ` 的定义

English:
definition quotQuotEquivQuotSupₐ
  signature: : ((A ⧸ I) ⧸ J.map (Quotient.mkₐ R I)) ≃ₐ[R] A ⧸ I ⊔ J
  body: AlgEquiv.ofRingEquiv (f := quotQuotEquivQuotSup I J) fun _ => rfl

@[simp]

中文:
定义 quotQuotEquivQuotSupₐ
  签名: : ((A ⧸ I) ⧸ J.map (商.mkₐ R I)) ≃ₐ[R] A ⧸ I ⊔ J
  定义体: AlgEquiv.ofRingEquiv (f := quotQuotEquivQuotSup I J) fun _ => rfl

@[simp]

Depends on / 依赖: AlgEquiv, AlgEquiv.ofRingEquiv, ofRingEquiv, quotQuotEquivQuotSup
-/
def quotQuotEquivQuotSupₐ : ((A ⧸ I) ⧸ J.map (Quotient.mkₐ R I)) ≃ₐ[R] A ⧸ I ⊔ J :=
  AlgEquiv.ofRingEquiv (f := quotQuotEquivQuotSup I J) fun _ => rfl

@[simp]
/--
theorem `quotQuotEquivQuotSupₐ_toRingEquiv` / 定理 `quotQuotEquivQuotSupₐ_toRingEquiv`

English:
theorem quotQuotEquivQuotSupₐ_toRingEquiv
  proof: rfl

@[simp]

中文:
定理 quotQuotEquivQuotSupₐ_toRingEquiv
  证明: rfl

@[simp]
-/
theorem quotQuotEquivQuotSupₐ_toRingEquiv :
    (quotQuotEquivQuotSupₐ R I J : _ ⧸ J.map (Quotient.mkₐ R I) ≃+* _) = quotQuotEquivQuotSup I J :=
  rfl

@[simp]
/--
theorem `coe_quotQuotEquivQuotSupₐ` / 定理 `coe_quotQuotEquivQuotSupₐ`

English:
theorem coe_quotQuotEquivQuotSupₐ
  statement: ⇑(quotQuotEquivQuotSupₐ R I J) = quotQuotEquivQuotSup I J
  proof: rfl

@[simp]

中文:
定理 coe_quotQuotEquivQuotSupₐ
  结论: ⇑(quotQuotEquivQuotSupₐ R I J) = quotQuotEquivQuotSup I J
  证明: rfl

@[simp]
-/
theorem coe_quotQuotEquivQuotSupₐ : ⇑(quotQuotEquivQuotSupₐ R I J) = quotQuotEquivQuotSup I J :=
  rfl

@[simp]
/--
theorem `quotQuotEquivQuotSupₐ_symm_toRingEquiv` / 定理 `quotQuotEquivQuotSupₐ_symm_toRingEquiv`

English:
theorem quotQuotEquivQuotSupₐ_symm_toRingEquiv
  proof: rfl

@[simp]

中文:
定理 quotQuotEquivQuotSupₐ_symm_toRingEquiv
  证明: rfl

@[simp]
-/
theorem quotQuotEquivQuotSupₐ_symm_toRingEquiv :
    ((quotQuotEquivQuotSupₐ R I J).symm : _ ≃+* _ ⧸ J.map (Quotient.mkₐ R I)) =
      (quotQuotEquivQuotSup I J).symm :=
  rfl

@[simp]
/--
theorem `coe_quotQuotEquivQuotSupₐ_symm` / 定理 `coe_quotQuotEquivQuotSupₐ_symm`

English:
theorem coe_quotQuotEquivQuotSupₐ_symm
  proof: rfl

中文:
定理 coe_quotQuotEquivQuotSupₐ_symm
  证明: rfl
-/
theorem coe_quotQuotEquivQuotSupₐ_symm :
    ⇑(quotQuotEquivQuotSupₐ R I J).symm = (quotQuotEquivQuotSup I J).symm :=
  rfl

/--
Definition of `quotQuotEquivCommₐ` / `quotQuotEquivCommₐ` 的定义

English:
definition quotQuotEquivCommₐ
  signature: :
  body: AlgEquiv.ofRingEquiv (f := quotQuotEquivComm I J) fun _ => rfl

@[simp]

中文:
定义 quotQuotEquivCommₐ
  签名: :
  定义体: AlgEquiv.ofRingEquiv (f := quotQuotEquivComm I J) fun _ => rfl

@[simp]

Depends on / 依赖: AlgEquiv, AlgEquiv.ofRingEquiv, ofRingEquiv, quotQuotEquivComm
-/
def quotQuotEquivCommₐ :
    ((A ⧸ I) ⧸ J.map (Quotient.mkₐ R I)) ≃ₐ[R] (A ⧸ J) ⧸ I.map (Quotient.mkₐ R J) :=
  AlgEquiv.ofRingEquiv (f := quotQuotEquivComm I J) fun _ => rfl

@[simp]
/--
theorem `quotQuotEquivCommₐ_toRingEquiv` / 定理 `quotQuotEquivCommₐ_toRingEquiv`

English:
theorem quotQuotEquivCommₐ_toRingEquiv
  proof: rfl

@[simp]

中文:
定理 quotQuotEquivCommₐ_toRingEquiv
  证明: rfl

@[simp]
-/
theorem quotQuotEquivCommₐ_toRingEquiv :
    (quotQuotEquivCommₐ R I J : _ ⧸ J.map (Quotient.mkₐ R I) ≃+* _ ⧸ I.map (Quotient.mkₐ R J)) =
      quotQuotEquivComm I J :=
  rfl

@[simp]
/--
theorem `coe_quotQuotEquivCommₐ` / 定理 `coe_quotQuotEquivCommₐ`

English:
theorem coe_quotQuotEquivCommₐ
  statement: ⇑(quotQuotEquivCommₐ R I J) = ⇑(quotQuotEquivComm I J)
  proof: rfl

@[simp]

中文:
定理 coe_quotQuotEquivCommₐ
  结论: ⇑(quotQuotEquivCommₐ R I J) = ⇑(quotQuotEquivComm I J)
  证明: rfl

@[simp]
-/
theorem coe_quotQuotEquivCommₐ : ⇑(quotQuotEquivCommₐ R I J) = ⇑(quotQuotEquivComm I J) :=
  rfl

@[simp]
/--
theorem `quotQuotEquivComm_symmₐ` / 定理 `quotQuotEquivComm_symmₐ`

English:
theorem quotQuotEquivComm_symmₐ
  statement: (quotQuotEquivCommₐ R I J).symm = quotQuotEquivCommₐ R J I
  proof: by
  rfl

@[simp]

中文:
定理 quotQuotEquivComm_symmₐ
  结论: (quotQuotEquivCommₐ R I J).symm = quotQuotEquivCommₐ R J I
  证明: by
  rfl

@[simp]
-/
theorem quotQuotEquivComm_symmₐ : (quotQuotEquivCommₐ R I J).symm = quotQuotEquivCommₐ R J I := by
  rfl

@[simp]
/--
theorem `quotQuotEquivComm_comp_quotQuotMkₐ` / 定理 `quotQuotEquivComm_comp_quotQuotMkₐ`

English:
theorem quotQuotEquivComm_comp_quotQuotMkₐ
  proof: AlgHom.ext quotQuotEquivComm_quotQuotMk I J

中文:
定理 quotQuotEquivComm_comp_quotQuotMkₐ
  证明: AlgHom.ext quotQuotEquivComm_quotQuotMk I J

Depends on / 依赖: AlgHom, AlgHom.ext, quotQuotEquivComm_quotQuotMk
-/
theorem quotQuotEquivComm_comp_quotQuotMkₐ :
    AlgHom.comp (↑(quotQuotEquivCommₐ R I J)) (quotQuotMkₐ R I J) = quotQuotMkₐ R J I :=
AlgHom.ext quotQuotEquivComm_quotQuotMk I J

variable {I J}

/--
Definition of `quotQuotEquivQuotOfLEₐ` / `quotQuotEquivQuotOfLEₐ` 的定义

English:
definition quotQuotEquivQuotOfLEₐ
  signature: (h : I <= J)
  body: AlgEquiv.ofRingEquiv (f := quotQuotEquivQuotOfLE h) fun _ => rfl

@[simp]

中文:
定义 quotQuotEquivQuotOfLEₐ
  签名: (h : I <= J)
  定义体: AlgEquiv.ofRingEquiv (f := quotQuotEquivQuotOfLE h) fun _ => rfl

@[simp]

Depends on / 依赖: AlgEquiv, AlgEquiv.ofRingEquiv, ofRingEquiv, quotQuotEquivQuotOfLE
-/
def quotQuotEquivQuotOfLEₐ (h : I <= J) : ((A ⧸ I) ⧸ J.map (Quotient.mkₐ R I)) ≃ₐ[R] A ⧸ J :=
  AlgEquiv.ofRingEquiv (f := quotQuotEquivQuotOfLE h) fun _ => rfl

@[simp]
/--
theorem `quotQuotEquivQuotOfLEₐ_toRingEquiv` / 定理 `quotQuotEquivQuotOfLEₐ_toRingEquiv`

English:
theorem quotQuotEquivQuotOfLEₐ_toRingEquiv
  given: (h : I <= J)
  proof: rfl

@[simp]

中文:
定理 quotQuotEquivQuotOfLEₐ_toRingEquiv
  条件: (h : I <= J)
  证明: rfl

@[simp]
-/
theorem quotQuotEquivQuotOfLEₐ_toRingEquiv (h : I <= J) :
    (quotQuotEquivQuotOfLEₐ R h : _ ⧸ J.map (Quotient.mkₐ R I) ≃+* _) = quotQuotEquivQuotOfLE h :=
  rfl

@[simp]
/--
theorem `coe_quotQuotEquivQuotOfLEₐ` / 定理 `coe_quotQuotEquivQuotOfLEₐ`

English:
theorem coe_quotQuotEquivQuotOfLEₐ
  given: (h : I <= J)
  proof: rfl

@[simp]

中文:
定理 coe_quotQuotEquivQuotOfLEₐ
  条件: (h : I <= J)
  证明: rfl

@[simp]
-/
theorem coe_quotQuotEquivQuotOfLEₐ (h : I <= J) :
    ⇑(quotQuotEquivQuotOfLEₐ R h) = quotQuotEquivQuotOfLE h :=
  rfl

@[simp]
/--
theorem `quotQuotEquivQuotOfLEₐ_symm_toRingEquiv` / 定理 `quotQuotEquivQuotOfLEₐ_symm_toRingEquiv`

English:
theorem quotQuotEquivQuotOfLEₐ_symm_toRingEquiv
  given: (h : I <= J)
  proof: rfl

@[simp]

中文:
定理 quotQuotEquivQuotOfLEₐ_symm_toRingEquiv
  条件: (h : I <= J)
  证明: rfl

@[simp]
-/
theorem quotQuotEquivQuotOfLEₐ_symm_toRingEquiv (h : I <= J) :
    ((quotQuotEquivQuotOfLEₐ R h).symm : _ ≃+* _ ⧸ J.map (Quotient.mkₐ R I)) =
      (quotQuotEquivQuotOfLE h).symm :=
  rfl

@[simp]
/--
theorem `coe_quotQuotEquivQuotOfLEₐ_symm` / 定理 `coe_quotQuotEquivQuotOfLEₐ_symm`

English:
theorem coe_quotQuotEquivQuotOfLEₐ_symm
  given: (h : I <= J)
  proof: rfl

@[simp]

中文:
定理 coe_quotQuotEquivQuotOfLEₐ_symm
  条件: (h : I <= J)
  证明: rfl

@[simp]
-/
theorem coe_quotQuotEquivQuotOfLEₐ_symm (h : I <= J) :
    ⇑(quotQuotEquivQuotOfLEₐ R h).symm = (quotQuotEquivQuotOfLE h).symm :=
  rfl

@[simp]
/--
theorem `quotQuotEquivQuotOfLE_comp_quotQuotMkₐ` / 定理 `quotQuotEquivQuotOfLE_comp_quotQuotMkₐ`

English:
theorem quotQuotEquivQuotOfLE_comp_quotQuotMkₐ
  given: (h : I <= J)
  proof: rfl

@[simp]

中文:
定理 quotQuotEquivQuotOfLE_comp_quotQuotMkₐ
  条件: (h : I <= J)
  证明: rfl

@[simp]
-/
theorem quotQuotEquivQuotOfLE_comp_quotQuotMkₐ (h : I <= J) :
    AlgHom.comp (↑(quotQuotEquivQuotOfLEₐ R h)) (quotQuotMkₐ R I J) = Quotient.mkₐ R J :=
  rfl

@[simp]
/--
theorem `quotQuotEquivQuotOfLE_symm_comp_mkₐ` / 定理 `quotQuotEquivQuotOfLE_symm_comp_mkₐ`

English:
theorem quotQuotEquivQuotOfLE_symm_comp_mkₐ
  given: (h : I <= J)
  proof: rfl

中文:
定理 quotQuotEquivQuotOfLE_symm_comp_mkₐ
  条件: (h : I <= J)
  证明: rfl
-/
theorem quotQuotEquivQuotOfLE_symm_comp_mkₐ (h : I <= J) :
    AlgHom.comp (↑(quotQuotEquivQuotOfLEₐ R h).symm) (Quotient.mkₐ R J) = quotQuotMkₐ R I J :=
  rfl

/--
lemma `quotQuotEquivQuotOfLEₐ_comp_mkₐ` / 引理 `quotQuotEquivQuotOfLEₐ_comp_mkₐ`

English:
lemma quotQuotEquivQuotOfLEₐ_comp_mkₐ
  given: (h : I <= J)
  proof: by
  ext x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

中文:
引理 quotQuotEquivQuotOfLEₐ_comp_mkₐ
  条件: (h : I <= J)
  证明: by
  ext x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

Depends on / 依赖: Ideal.Quotient.mk_surjective, Quotient, mk_surjective
-/
lemma quotQuotEquivQuotOfLEₐ_comp_mkₐ (h : I <= J) :
    (quotQuotEquivQuotOfLEₐ R h).toAlgHom.comp (Ideal.Quotient.mkₐ _ _) =
      Ideal.Quotient.factorₐ _ h := by
  ext x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

end AlgebraQuotient
end DoubleQuot

namespace Ideal

section PowQuot

variable {R : Type*} [CommRing R] (I : Ideal R) (n : Nat)

set_option backward.isDefEq.respectTransparency false in
/-- `I ^ n ⧸ I ^ (n + 1)` can be viewed as a quotient module and as ideal of `R ⧸ I ^ (n + 1)`.
This definition gives the `R`-linear equivalence between the two. -/
noncomputable
/--
Definition of `powQuotPowSuccLinearEquivMapMkPowSuccPow` / `powQuotPowSuccLinearEquivMapMkPowSuccPow` 的定义

English:
definition powQuotPowSuccLinearEquivMapMkPowSuccPow
  signature: :
  body: by
  refine { LinearMap.codRestrict
    (Submodule.restrictScalars _ (Ideal.map (Ideal.Quotient.mk (I ^ (n + 1))) (I ^ n)))
    (Submodule.mapQ (I • ⊤) (I ^ (n + 1)) (Submodule.subtype (I ^ n)) ?_) ?_,
    Equiv.ofBijective _ ⟨?_, ?_⟩ with }
  · intro
    simp [Submodule.mem_smul_top_iff, pow_succ']

中文:
定义 powQuotPowSuccLinearEquivMapMkPowSuccPow
  签名: :
  定义体: by
  refine { LinearMap.codRestrict
    (Submodule.restrictScalars _ (Ideal.map (Ideal.Quotient.mk (I ^ (n + 1))) (I ^ n)))
    (Submodule.mapQ (I • ⊤) (I ^ (n + 1)) (Submodule.subtype (I ^ n)) ?_) ?_,
    Equiv.ofBijective _ ⟨?_, ?_⟩ with }
  · intro
    simp [Submodule.mem_smul_top_iff, pow_succ']

Depends on / 依赖: Equiv.ofBijective, Ideal.Quotient.mk, Ideal.map, Ideal.mem_sup_left, LinearMap, LinearMap.codRestrict, Quotient, Submodule, Submodule.Quotient, Submodule.Quotient.mk_surjective, Submodule.mapQ, Submodule.mem_smul_top_iff, Submodule.restrictScalars, Submodule.subtype, codRestrict, mem_smul_top_iff, mem_sup_left, mk_surjective, ofBijective, pow_succ
-/
def powQuotPowSuccLinearEquivMapMkPowSuccPow :
    ((I ^ n : Ideal R) ⧸ (I • ⊤ : Submodule R (I ^ n : Ideal R))) ≃ₗ[R]
    Ideal.map (Ideal.Quotient.mk (I ^ (n + 1))) (I ^ n) := by
  refine { LinearMap.codRestrict
    (Submodule.restrictScalars _ (Ideal.map (Ideal.Quotient.mk (I ^ (n + 1))) (I ^ n)))
    (Submodule.mapQ (I • ⊤) (I ^ (n + 1)) (Submodule.subtype (I ^ n)) ?_) ?_,
    Equiv.ofBijective _ ⟨?_, ?_⟩ with }
  · intro
    simp [Submodule.mem_smul_top_iff, pow_succ']
  · intro x
    obtain ⟨⟨y, hy⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    simp [Ideal.mem_sup_left hy]
  · intro a b
    obtain ⟨⟨x, hx⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ a
    obtain ⟨⟨y, hy⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ b
    simp [Ideal.Quotient.eq, Submodule.Quotient.eq, Submodule.mem_smul_top_iff, pow_succ']
  · intro ⟨x, hx⟩
    rw [Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    refine ⟨Submodule.Quotient.mk ⟨y, hy⟩, ?_⟩
    simp

/-- `I ^ n ⧸ I ^ (n + 1)` can be viewed as a quotient module and as ideal of `R ⧸ I ^ (n + 1)`.
This definition gives the equivalence between the two, instead of the `R`-linear equivalence,
to bypass typeclass synthesis issues on complex `Module` goals. -/
noncomputable
/--
Definition of `powQuotPowSuccEquivMapMkPowSuccPow` / `powQuotPowSuccEquivMapMkPowSuccPow` 的定义

English:
definition powQuotPowSuccEquivMapMkPowSuccPow
  signature: :
  body: powQuotPowSuccLinearEquivMapMkPowSuccPow I n

中文:
定义 powQuotPowSuccEquivMapMkPowSuccPow
  签名: :
  定义体: powQuotPowSuccLinearEquivMapMkPowSuccPow I n

Depends on / 依赖: powQuotPowSuccLinearEquivMapMkPowSuccPow
-/
def powQuotPowSuccEquivMapMkPowSuccPow :
    ((I ^ n : Ideal R) ⧸ (I • ⊤ : Submodule R (I ^ n : Ideal R))) ≃
    Ideal.map (Ideal.Quotient.mk (I ^ (n + 1))) (I ^ n) :=
  powQuotPowSuccLinearEquivMapMkPowSuccPow I n

end PowQuot

end Ideal
