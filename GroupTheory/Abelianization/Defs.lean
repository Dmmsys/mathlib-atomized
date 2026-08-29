/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Michael Howes, Antoine Chambert-Loir
-/
module

public import Mathlib.GroupTheory.Commutator.Basic

/-!
# The abelianization of a group

This file defines the commutator and the abelianization of a group. It furthermore prepares for the
result that the abelianization is left adjoint to the forgetful functor from abelian groups to
groups, which can be found in `Mathlib/Algebra/Category/Grp/Adjunctions.lean`.

## Main definitions

* `Abelianization`: defines the abelianization of a group `G` as the quotient of a group by its
  commutator subgroup.
* `Abelianization.map`: lifts a group homomorphism to a homomorphism between the abelianizations
* `MulEquiv.abelianizationCongr`: Equivalent groups have equivalent abelianizations

-/

@[expose] public section

assert_not_exists Cardinal Field

universe u v w

-- Let G be a group.
variable (G : Type u) [Group G]

open Subgroup (centralizer)

/--
Definition of `Abelianization` / `Abelianization` 的定义

English:
definition Abelianization
  signature: : Type u
  body: G ⧸ commutator G

中文:
定义 Abelianization
  签名: : 类型u
  定义体: G ⧸ commutator G

Depends on / 依赖: commutator
-/
def Abelianization : Type u :=
  G ⧸ commutator G

namespace Abelianization

/--
Instance `commGroup` / 实例 `commGroup`

English:
instance commGroup
  signature: : CommGroup (Abelianization G) where
  body: QuotientGroup.Quotient.group _
mul_comm x y := Quotient.inductionOn₂ x y fun a b => Quotient.sound'
QuotientGroup.leftRel_apply.mpr Subgroup.subset_closure
      -- We avoid `group` here to minimize imports while low in the hierarchy;
      -- typically it would be better to invoke the tactic.
     

中文:
实例 commGroup
  签名: : CommGroup (Abelianization G) where
  定义体: QuotientGroup.Quotient.group _
mul_comm x y := Quotient.inductionOn₂ x y fun a b => Quotient.sound'
QuotientGroup.leftRel_apply.mpr Subgroup.subset_closure
      -- We avoid `group` here to minimize imports while low in the hierarchy;
      -- typically it would be better to invoke the tactic.
     

Depends on / 依赖: Quotient, QuotientGroup, QuotientGroup.Quotient.group
-/
instance commGroup : CommGroup (Abelianization G) where
  __ := QuotientGroup.Quotient.group _
mul_comm x y := Quotient.inductionOn₂ x y fun a b => Quotient.sound'
QuotientGroup.leftRel_apply.mpr Subgroup.subset_closure
      -- We avoid `group` here to minimize imports while low in the hierarchy;
      -- typically it would be better to invoke the tactic.
      ⟨b⁻¹, Subgroup.mem_top _, a⁻¹, Subgroup.mem_top _, by simp [commutatorElement_def, mul_assoc]⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (Abelianization G)
  body: ⟨1⟩

中文:
实例 :
  签名: Inhabited (Abelianization G)
  定义体: ⟨1⟩
-/
instance : Inhabited (Abelianization G) :=
  ⟨1⟩

variable {G}

/--
Definition of `of` / `of` 的定义

English:
definition of
  signature: : G ->* Abelianization G where
  body: QuotientGroup.mk
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp]

中文:
定义 of
  签名: : G ->* Abelianization G where
  定义体: QuotientGroup.mk
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp]

Depends on / 依赖: QuotientGroup, QuotientGroup.mk
-/
def of : G ->* Abelianization G where
  toFun := QuotientGroup.mk
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp]
/--
theorem `mk_eq_of` / 定理 `mk_eq_of`

English:
theorem mk_eq_of
  given: (a : G)
  statement: Quot.mk _ a = of a
  proof: rfl

中文:
定理 mk_eq_of
  条件: (a : G)
  结论: Quot.mk _ a = of a
  证明: rfl
-/
theorem mk_eq_of (a : G) : Quot.mk _ a = of a :=
  rfl

variable (G) in
@[simp]
/--
theorem `ker_of` / 定理 `ker_of`

English:
theorem ker_of
  statement: of.ker = commutator G
  proof: QuotientGroup.ker_mk' (commutator G)

中文:
定理 ker_of
  结论: of.ker = commutator G
  证明: QuotientGroup.ker_mk' (commutator G)

Depends on / 依赖: QuotientGroup, QuotientGroup.ker_mk, commutator, ker_mk
-/
theorem ker_of : of.ker = commutator G :=
  QuotientGroup.ker_mk' (commutator G)

section lift

-- So far we have built Gᵃᵇ and proved it's an abelian group.
-- Furthermore we defined the canonical projection `of : G → Gᵃᵇ`
-- Let `A` be an abelian group and let `f` be a group homomorphism from `G` to `A`.
variable {A : Type v} [CommGroup A] (f : G ->* A)

/--
theorem `commutator_subset_ker` / 定理 `commutator_subset_ker`

English:
theorem commutator_subset_ker
  statement: commutator G <= f.ker
  proof: by
  rw [commutator_eq_closure]; rw [Subgroup.closure_le]
  rintro x ⟨p, q, rfl⟩
  simp [MonoidHom.mem_ker, mul_right_comm (f p) (f q), commutatorElement_def]

中文:
定理 commutator_subset_ker
  结论: commutator G <= f.ker
  证明: by
  rw [commutator_eq_closure]; rw [Subgroup.closure_le]
  rintro x ⟨p, q, rfl⟩
  simp [MonoidHom.mem_ker, mul_right_comm (f p) (f q), commutatorElement_def]

Depends on / 依赖: MonoidHom, MonoidHom.mem_ker, Subgroup, Subgroup.closure_le, closure_le, commutatorElement_def, commutator_eq_closure, mem_ker, mul_right_comm
-/
theorem commutator_subset_ker : commutator G <= f.ker := by
  rw [commutator_eq_closure]; rw [Subgroup.closure_le]
  rintro x ⟨p, q, rfl⟩
  simp [MonoidHom.mem_ker, mul_right_comm (f p) (f q), commutatorElement_def]

/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: : (G ->* A) ≃ (Abelianization G ->* A) where
  body: QuotientGroup.lift _ f fun _ h => MonoidHom.mem_ker.2 commutator_subset_ker _ h
  invFun F := F.comp of
  right_inv _ := MonoidHom.ext fun x => QuotientGroup.induction_on x fun _ => rfl

@[simp]

中文:
定义 lift
  签名: : (G ->* A) ≃ (Abelianization G ->* A) where
  定义体: QuotientGroup.lift _ f fun _ h => MonoidHom.mem_ker.2 commutator_subset_ker _ h
  invFun F := F.comp of
  right_inv _ := MonoidHom.ext fun x => QuotientGroup.induction_on x fun _ => rfl

@[simp]

Depends on / 依赖: MonoidHom, MonoidHom.mem_ker, QuotientGroup, QuotientGroup.lift, commutator_subset_ker, mem_ker
-/
def lift : (G ->* A) ≃ (Abelianization G ->* A) where
toFun f := QuotientGroup.lift _ f fun _ h => MonoidHom.mem_ker.2 commutator_subset_ker _ h
  invFun F := F.comp of
  right_inv _ := MonoidHom.ext fun x => QuotientGroup.induction_on x fun _ => rfl

@[simp]
/--
theorem `lift_apply_of` / 定理 `lift_apply_of`

English:
theorem lift_apply_of
  given: (x : G)
  statement: lift f (of x) = f x
  proof: rfl

中文:
定理 lift_apply_of
  条件: (x : G)
  结论: lift f (of x) = f x
  证明: rfl
-/
theorem lift_apply_of (x : G) : lift f (of x) = f x :=
  rfl

/--
theorem `coe_lift_symm` / 定理 `coe_lift_symm`

English:
theorem coe_lift_symm
  statement: (lift.symm : (Abelianization G ->* A) -> (G ->* A)) = (·.comp of)
  proof: rfl

@[simp]

中文:
定理 coe_lift_symm
  结论: (lift.symm : (Abelianization G ->* A) -> (G ->* A)) = (·.comp of)
  证明: rfl

@[simp]
-/
theorem coe_lift_symm : (lift.symm : (Abelianization G ->* A) -> (G ->* A)) = (·.comp of) := rfl

@[simp]
/--
theorem `lift_symm_apply` / 定理 `lift_symm_apply`

English:
theorem lift_symm_apply
  given: (f : Abelianization G ->* A)
  statement: lift.symm f = f.comp of
  proof: rfl

中文:
定理 lift_symm_apply
  条件: (f : Abelianization G ->* A)
  结论: lift.symm f = f.comp of
  证明: rfl
-/
theorem lift_symm_apply (f : Abelianization G ->* A) : lift.symm f = f.comp of := rfl

/--
theorem `lift_unique` / 定理 `lift_unique`

English:
theorem lift_unique
  statement: (φ : Abelianization G ->* A)
  proof: QuotientGroup.induction_on x hφ

@[simp]

中文:
定理 lift_unique
  结论: (φ : Abelianization G ->* A)
  证明: QuotientGroup.induction_on x hφ

@[simp]

Depends on / 依赖: QuotientGroup, QuotientGroup.induction_on, induction_on
-/
theorem lift_unique (φ : Abelianization G ->* A)
    -- hφ : φ agrees with f on the image of G in Gᵃᵇ
    (hφ : forall x : G, φ (Abelianization.of x) = f x)
    {x : Abelianization G} : φ x = lift f x :=
  QuotientGroup.induction_on x hφ

@[simp]
/--
theorem `lift_of` / 定理 `lift_of`

English:
theorem lift_of
  statement: lift of = MonoidHom.id (Abelianization G)
  proof: lift.apply_symm_apply MonoidHom.id _

中文:
定理 lift_of
  结论: lift of = MonoidHom.id (Abelianization G)
  证明: lift.apply_symm_apply MonoidHom.id _

Depends on / 依赖: MonoidHom, MonoidHom.id, apply_symm_apply, lift.apply_symm_apply
-/
theorem lift_of : lift of = MonoidHom.id (Abelianization G) :=
lift.apply_symm_apply MonoidHom.id _

end lift

variable {A : Type v} [Monoid A]

/-- See note [partially-applied ext lemmas]. -/
@[ext]
/--
theorem `hom_ext` / 定理 `hom_ext`

English:
theorem hom_ext
  given: (φ ψ : Abelianization G ->* A) (h : φ.comp of = ψ.comp of)
  statement: φ = ψ
  proof: MonoidHom.ext fun x => QuotientGroup.induction_on x DFunLike.congr_fun h

中文:
定理 hom_ext
  条件: (φ ψ : Abelianization G ->* A) (h : φ.comp of = ψ.comp of)
  结论: φ = ψ
  证明: MonoidHom.ext fun x => QuotientGroup.induction_on x DFunLike.congr_fun h

Depends on / 依赖: DFunLike, DFunLike.congr_fun, MonoidHom, MonoidHom.ext, QuotientGroup, QuotientGroup.induction_on, congr_fun, induction_on
-/
theorem hom_ext (φ ψ : Abelianization G ->* A) (h : φ.comp of = ψ.comp of) : φ = ψ :=
MonoidHom.ext fun x => QuotientGroup.induction_on x DFunLike.congr_fun h

section Map

variable {H : Type v} [Group H] (f : G ->* H)

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: : Abelianization G ->* Abelianization H
  body: lift (of.comp f)

中文:
定义 map
  签名: : Abelianization G ->* Abelianization H
  定义体: lift (of.comp f)

Depends on / 依赖: of.comp
-/
def map : Abelianization G ->* Abelianization H :=
  lift (of.comp f)

/--
theorem `lift_of_comp` / 定理 `lift_of_comp`

English:
theorem lift_of_comp
  proof: rfl

@[simp]

中文:
定理 lift_of_comp
  证明: rfl

@[simp]
-/
@[simp] theorem lift_of_comp :
    Abelianization.lift (Abelianization.of.comp f) = Abelianization.map f := rfl

@[simp]
/--
theorem `map_of` / 定理 `map_of`

English:
theorem map_of
  given: (x : G)
  statement: map f (of x) = of (f x)
  proof: rfl

@[simp]

中文:
定理 map_of
  条件: (x : G)
  结论: map f (of x) = of (f x)
  证明: rfl

@[simp]
-/
theorem map_of (x : G) : map f (of x) = of (f x) :=
  rfl

@[simp]
/--
theorem `map_id` / 定理 `map_id`

English:
theorem map_id
  statement: map (MonoidHom.id G) = MonoidHom.id (Abelianization G)
  proof: hom_ext _ _ rfl

@[simp]

中文:
定理 map_id
  结论: map (MonoidHom.id G) = MonoidHom.id (Abelianization G)
  证明: hom_ext _ _ rfl

@[simp]

Depends on / 依赖: hom_ext
-/
theorem map_id : map (MonoidHom.id G) = MonoidHom.id (Abelianization G) :=
  hom_ext _ _ rfl

@[simp]
/--
theorem `map_comp` / 定理 `map_comp`

English:
theorem map_comp
  given: {I : Type w} [Group I] (g : H ->* I)
  statement: (map g).comp (map f) = map (g.comp f)
  proof: hom_ext _ _ rfl

@[simp]

中文:
定理 map_comp
  条件: {I : Type w} [Group I] (g : H ->* I)
  结论: (map g).comp (map f) = map (g.comp f)
  证明: hom_ext _ _ rfl

@[simp]

Depends on / 依赖: hom_ext
-/
theorem map_comp {I : Type w} [Group I] (g : H ->* I) : (map g).comp (map f) = map (g.comp f) :=
  hom_ext _ _ rfl

@[simp]
/--
theorem `map_map_apply` / 定理 `map_map_apply`

English:
theorem map_map_apply
  given: {I : Type w} [Group I] {g : H ->* I} {x : Abelianization G}
  proof: DFunLike.congr_fun (map_comp _ _) x

中文:
定理 map_map_apply
  条件: {I : Type w} [Group I] {g : H ->* I} {x : Abelianization G}
  证明: DFunLike.congr_fun (map_comp _ _) x

Depends on / 依赖: DFunLike, DFunLike.congr_fun, congr_fun, map_comp
-/
theorem map_map_apply {I : Type w} [Group I] {g : H ->* I} {x : Abelianization G} :
    map g (map f x) = map (g.comp f) x :=
  DFunLike.congr_fun (map_comp _ _) x

end Map

end Abelianization

section AbelianizationCongr

variable {G} {H : Type v} [Group H]

/--
Definition of `MulEquiv.abelianizationCongr` / `MulEquiv.abelianizationCongr` 的定义

English:
definition MulEquiv.abelianizationCongr
  signature: (e : G ≃* H)
  body: Abelianization.map e.toMonoidHom
  invFun := Abelianization.map e.symm.toMonoidHom
  left_inv := by
    rintro ⟨a⟩
    simp
  right_inv := by
    rintro ⟨a⟩
    simp
  map_mul' := map_mul _

@[simp]

中文:
定义 MulEquiv.abelianizationCongr
  签名: (e : G ≃* H)
  定义体: Abelianization.map e.toMonoidHom
  invFun := Abelianization.map e.symm.toMonoidHom
  left_inv := by
    rintro ⟨a⟩
    simp
  right_inv := by
    rintro ⟨a⟩
    simp
  map_mul' := map_mul _

@[simp]

Depends on / 依赖: Abelianization, Abelianization.map, e.toMonoidHom, toMonoidHom
-/
def MulEquiv.abelianizationCongr (e : G ≃* H) : Abelianization G ≃* Abelianization H where
  toFun := Abelianization.map e.toMonoidHom
  invFun := Abelianization.map e.symm.toMonoidHom
  left_inv := by
    rintro ⟨a⟩
    simp
  right_inv := by
    rintro ⟨a⟩
    simp
  map_mul' := map_mul _

@[simp]
/--
theorem `abelianizationCongr_of` / 定理 `abelianizationCongr_of`

English:
theorem abelianizationCongr_of
  given: (e : G ≃* H) (x : G)
  proof: rfl

@[simp]

中文:
定理 abelianizationCongr_of
  条件: (e : G ≃* H) (x : G)
  证明: rfl

@[simp]
-/
theorem abelianizationCongr_of (e : G ≃* H) (x : G) :
    e.abelianizationCongr (Abelianization.of x) = Abelianization.of (e x) :=
  rfl

@[simp]
/--
theorem `abelianizationCongr_refl` / 定理 `abelianizationCongr_refl`

English:
theorem abelianizationCongr_refl
  proof: MulEquiv.toMonoidHom_injective Abelianization.lift_of

@[simp]

中文:
定理 abelianizationCongr_refl
  证明: MulEquiv.toMonoidHom_injective Abelianization.lift_of

@[simp]

Depends on / 依赖: Abelianization, Abelianization.lift_of, MulEquiv, MulEquiv.toMonoidHom_injective, lift_of, toMonoidHom_injective
-/
theorem abelianizationCongr_refl :
    (MulEquiv.refl G).abelianizationCongr = MulEquiv.refl (Abelianization G) :=
  MulEquiv.toMonoidHom_injective Abelianization.lift_of

@[simp]
/--
theorem `abelianizationCongr_symm` / 定理 `abelianizationCongr_symm`

English:
theorem abelianizationCongr_symm
  given: (e : G ≃* H)
  proof: rfl

@[simp]

中文:
定理 abelianizationCongr_symm
  条件: (e : G ≃* H)
  证明: rfl

@[simp]
-/
theorem abelianizationCongr_symm (e : G ≃* H) :
    e.abelianizationCongr.symm = e.symm.abelianizationCongr :=
  rfl

@[simp]
/--
theorem `abelianizationCongr_trans` / 定理 `abelianizationCongr_trans`

English:
theorem abelianizationCongr_trans
  given: {I : Type v} [Group I] (e : G ≃* H) (e₂ : H ≃* I)
  proof: MulEquiv.toMonoidHom_injective (Abelianization.hom_ext _ _ rfl)

中文:
定理 abelianizationCongr_trans
  条件: {I : 类型v} [Group I] (e : G ≃* H) (e₂ : H ≃* I)
  证明: MulEquiv.toMonoidHom_injective (Abelianization.hom_ext _ _ rfl)

Depends on / 依赖: Abelianization, Abelianization.hom_ext, MulEquiv, MulEquiv.toMonoidHom_injective, hom_ext, toMonoidHom_injective
-/
theorem abelianizationCongr_trans {I : Type v} [Group I] (e : G ≃* H) (e₂ : H ≃* I) :
    e.abelianizationCongr.trans e₂.abelianizationCongr = (e.trans e₂).abelianizationCongr :=
  MulEquiv.toMonoidHom_injective (Abelianization.hom_ext _ _ rfl)

end AbelianizationCongr

/-- An Abelian group is equivalent to its own abelianization. -/
@[simps]
/--
Definition of `Abelianization.equivOfComm` / `Abelianization.equivOfComm` 的定义

English:
definition Abelianization.equivOfComm
  signature: {H : Type*} [CommGroup H]
  body: { Abelianization.of with
    toFun := Abelianization.of
    invFun := Abelianization.lift (MonoidHom.id H)
    right_inv := by
      rintro ⟨a⟩
      rfl }

中文:
定义 Abelianization.equivOfComm
  签名: {H : 类型} [CommGroup H]
  定义体: { Abelianization.of with
    toFun := Abelianization.of
    invFun := Abelianization.lift (MonoidHom.id H)
    right_inv := by
      rintro ⟨a⟩
      rfl }

Depends on / 依赖: Abelianization, Abelianization.lift, Abelianization.of, MonoidHom, MonoidHom.id, invFun, right_inv
-/
def Abelianization.equivOfComm {H : Type*} [CommGroup H] : H ≃* Abelianization H :=
  { Abelianization.of with
    toFun := Abelianization.of
    invFun := Abelianization.lift (MonoidHom.id H)
    right_inv := by
      rintro ⟨a⟩
      rfl }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Unique
  signature: G] : Unique (Abelianization G)
  body: Quotient.instUniqueQuotient _

中文:
实例 [Unique
  签名: G] : Unique (Abelianization G)
  定义体: Quotient.instUniqueQuotient _
-/
instance [Unique G] : Unique (Abelianization G) := Quotient.instUniqueQuotient _
