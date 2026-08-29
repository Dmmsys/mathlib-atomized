/-
Copyright (c) 2019 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
module

public import Mathlib.Algebra.Group.Submonoid.Operations
public import Mathlib.Data.Setoid.Basic
public import Mathlib.GroupTheory.Congruence.Hom

/-!
# Congruence relations

This file proves basic properties of the quotient of a type by a congruence relation.

The second half of the file concerns congruence relations on monoids, in which case the
quotient by the congruence relation is also a monoid. There are results about the universal
property of quotients of monoids, and the isomorphism theorems for monoids.

## Implementation notes

A congruence relation on a monoid `M` can be thought of as a submonoid of `M × M` for which
membership is an equivalence relation, but whilst this fact is established in the file, it is not
used, since this perspective adds more layers of definitional unfolding.

## Tags

congruence, congruence relation, quotient, quotient by congruence relation, monoid,
quotient monoid, isomorphism theorems
-/

@[expose] public section


variable (M : Type*) {N : Type*} {P : Type*}

open Function Setoid

variable {M}

namespace Con

section

variable [Mul M] [Mul N] [Mul P] (c : Con M)

variable {c}

/-- Given types with multiplications `M, N`, the product of two congruence relations `c` on `M` and
`d` on `N`: `(x₁, x₂), (y₁, y₂) ∈ M × N` are related by `c.prod d` iff `x₁` is related to `y₁`
by `c` and `x₂` is related to `y₂` by `d`. -/
@[to_additive prod /-- Given types with additions `M, N`, the product of two congruence relations
`c` on `M` and `d` on `N`: `(x₁, x₂), (y₁, y₂) ∈ M × N` are related by `c.prod d` iff `x₁`
is related to `y₁` by `c` and `x₂` is related to `y₂` by `d`. -/]
/--
Definition of `prod` / `prod` 的定义

English:
definition prod
  signature: (c : Con M) (d : Con N)
  body: { c.toSetoid.prod d.toSetoid with
    mul' := fun h1 h2 => ⟨c.mul h1.1 h2.1, d.mul h1.2 h2.2⟩ }

中文:
定义 乘积
  签名: (c : Con M) (d : Con N)
  定义体: { c.toSetoid.prod d.toSetoid with
    mul' := fun h1 h2 => ⟨c.mul h1.1 h2.1, d.mul h1.2 h2.2⟩ }
-/
protected def prod (c : Con M) (d : Con N) : Con (M × N) :=
  { c.toSetoid.prod d.toSetoid with
    mul' := fun h1 h2 => ⟨c.mul h1.1 h2.1, d.mul h1.2 h2.2⟩ }

/-- The product of an indexed collection of congruence relations. -/
@[to_additive /-- The product of an indexed collection of additive congruence relations. -/]
/--
Definition of `pi` / `pi` 的定义

English:
definition pi
  signature: {ι : Type*} {f : ι -> Type*} [forall i, Mul (f i)] (C : forall i, Con (f i))
  body: { @piSetoid _ _ fun i => (C i).toSetoid with
    mul' := fun h1 h2 i => (C i).mul (h1 i) (h2 i) }

中文:
定义 pi
  签名: {ι : 类型} {f : ι -> 类型} [对任意 i, 乘法 (f i)] (C : 对任意 i, Con (f i))
  定义体: { @piSetoid _ _ fun i => (C i).toSetoid with
    mul' := fun h1 h2 i => (C i).mul (h1 i) (h2 i) }

Depends on / 依赖: piSetoid, toSetoid
-/
def pi {ι : Type*} {f : ι -> Type*} [forall i, Mul (f i)] (C : forall i, Con (f i)) : Con (forall i, f i) :=
  { @piSetoid _ _ fun i => (C i).toSetoid with
    mul' := fun h1 h2 i => (C i).mul (h1 i) (h2 i) }

/-- A multiplicative equivalence `e : α ≃* β` generates an equivalence between quotient spaces,
if it is compatible with the relations. -/
@[to_additive
/-- An additive equivalence `e : α ≃+ β` generates an equivalence between quotient spaces,
if it is compatible with the relations. -/]
/--
Definition of `congr` / `congr` 的定义

English:
definition congr
  signature: {c : Con M} {d : Con N} (e : M ≃* N) (h : c = d.comap e (map_mul e))
  body: Quotient.congr e by apply Con.ext_iff.mp h
  map_mul' := by rintro ⟨x⟩ ⟨y⟩; exact congrArg toQuotient (e.map_mul x y)

@[to_additive (attr := simp)]

中文:
定义 congr
  签名: {c : Con M} {d : Con N} (e : M ≃* N) (h : c = d.comap e (map_mul e))
  定义体: Quotient.congr e by apply Con.ext_iff.mp h
  map_mul' := by rintro ⟨x⟩ ⟨y⟩; exact congrArg toQuotient (e.map_mul x y)

@[to_additive (attr := simp)]
-/
protected def congr {c : Con M} {d : Con N} (e : M ≃* N) (h : c = d.comap e (map_mul e)) :
    c.Quotient ≃* d.Quotient where
__ := Quotient.congr e by apply Con.ext_iff.mp h
  map_mul' := by rintro ⟨x⟩ ⟨y⟩; exact congrArg toQuotient (e.map_mul x y)

@[to_additive (attr := simp)]
/--
theorem `congr_mk` / 定理 `congr_mk`

English:
theorem congr_mk
  given: {c : Con M} {d : Con N} (e : M ≃* N) (h : c = d.comap e (map_mul e)) (a : M)
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 congr_mk
  条件: {c : Con M} {d : Con N} (e : M ≃* N) (h : c = d.comap e (map_mul e)) (a : M)
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem congr_mk {c : Con M} {d : Con N} (e : M ≃* N) (h : c = d.comap e (map_mul e)) (a : M) :
    Con.congr e h (a : c.Quotient) = (e a : d.Quotient) := rfl

@[to_additive (attr := simp)]
/--
theorem `congr_symm` / 定理 `congr_symm`

English:
theorem congr_symm
  given: {c : Con M} {d : Con N} (e : M ≃* N) (h : c = d.comap e (map_mul e))
  proof: rfl

@[to_additive]

中文:
定理 congr_symm
  条件: {c : Con M} {d : Con N} (e : M ≃* N) (h : c = d.comap e (map_mul e))
  证明: rfl

@[to_additive]
-/
theorem congr_symm {c : Con M} {d : Con N} (e : M ≃* N) (h : c = d.comap e (map_mul e)) :
    (Con.congr e h).symm =
      Con.congr e.symm (ext <| e.surjective.forall₂.2 <| by simp [h]) :=
  rfl

@[to_additive]
/--
theorem `comap_conGen_equiv` / 定理 `comap_conGen_equiv`

English:
theorem comap_conGen_equiv
  given: {M N : Type*} [Mul M] [Mul N] (f : MulEquiv M N) (rel : N -> N -> Prop)
  proof: by
  apply le_antisymm _ (le_comap_conGen rel f (map_mul f))
  intro a b h
  simp only [Con.comap_rel] at h
  unfold Function.onFun
  generalize fa : f a = n1 at h
  generalize fb : f b = n2 at h
  induction h generalizing a b with
  | of x y h =>
    apply ConGen.Rel.of
    rwa [fa, fb]
  | refl x 

中文:
定理 comap_conGen_equiv
  条件: {M N : 类型} [乘法 M] [乘法 N] (f : 乘法等价 M N) (rel : N -> N -> 命题)
  证明: by
  apply le_antisymm _ (le_comap_conGen rel f (map_mul f))
  intro a b h
  simp only [Con.comap_rel] at h
  unfold Function.onFun
  generalize fa : f a = n1 at h
  generalize fb : f b = n2 at h
  induction h generalizing a b with
  | of x y h =>
    apply ConGen.Rel.of
    rwa [fa, fb]
  | refl x 

Depends on / 依赖: Con.comap_rel, ConGen, ConGen.Rel.of, ConGen.Rel.refl, ConGen.Rel.symm, ConGen.Rel.trans, Exists, Exists.casesOn, Function, Function.onFun, casesOn, comap_rel, f.injective, f.surjective, fa.trans, fb.symm, generalize, generalizing, injective, le_antisymm
-/
theorem comap_conGen_equiv {M N : Type*} [Mul M] [Mul N] (f : MulEquiv M N) (rel : N -> N -> Prop) :
    Con.comap f (map_mul f) (conGen rel) = conGen (fun x y => rel (f x) (f y)) := by
  apply le_antisymm _ (le_comap_conGen rel f (map_mul f))
  intro a b h
  simp only [Con.comap_rel] at h
  unfold Function.onFun
  generalize fa : f a = n1 at h
  generalize fb : f b = n2 at h
  induction h generalizing a b with
  | of x y h =>
    apply ConGen.Rel.of
    rwa [fa, fb]
  | refl x =>
    rw [f.injective (fa.trans fb.symm)]
    exact ConGen.Rel.refl _
  | symm _ h => exact ConGen.Rel.symm (h fb fa)
  | trans _ _ ih ih1 =>
    exact Exists.casesOn (f.surjective _) fun c' hc' => ConGen.Rel.trans (ih fa hc') (ih1 hc' fb)
  | @mul w x y z _ _ ih ih1 =>
    rw [← f.eq_symm_apply]; rw [map_mul] at fa fb
    rw [fa]; rw [fb]
    exact ConGen.Rel.mul (ih (by simp) (by simp)) (ih1 (by simp) (by simp))

@[to_additive]
/--
theorem `comap_conGen_of_bijective` / 定理 `comap_conGen_of_bijective`

English:
theorem comap_conGen_of_bijective
  statement: {M N : Type*} [Mul M] [Mul N] (f : M -> N)
  proof: comap_conGen_equiv (MulEquiv.ofBijective (MulHom.mk f H) hf) rel

中文:
定理 comap_conGen_of_bijective
  结论: {M N : 类型} [乘法 M] [乘法 N] (f : M -> N)
  证明: comap_conGen_equiv (MulEquiv.ofBijective (MulHom.mk f H) hf) rel

Depends on / 依赖: MulEquiv, MulEquiv.ofBijective, MulHom, MulHom.mk, comap_conGen_equiv, ofBijective
-/
theorem comap_conGen_of_bijective {M N : Type*} [Mul M] [Mul N] (f : M -> N)
    (hf : Function.Bijective f) (H : forall (x y : M), f (x * y) = f x * f y) (rel : N -> N -> Prop) :
    Con.comap f H (conGen rel) = conGen (fun x y => rel (f x) (f y)) :=
  comap_conGen_equiv (MulEquiv.ofBijective (MulHom.mk f H) hf) rel

end

section MulOneClass

variable [MulOneClass M] [MulOneClass N] [MulOneClass P] (c : Con M)

/-- The submonoid of `M × M` defined by a congruence relation on a monoid `M`. -/
@[to_additive (attr := coe) /-- The `AddSubmonoid` of `M × M` defined by an additive congruence
relation on an `AddMonoid` `M`. -/]
/--
Definition of `submonoid` / `submonoid` 的定义

English:
definition submonoid
  signature: : Submonoid (M × M) where
  body: { x | c x.1 x.2 }
  one_mem' := c.iseqv.1 1
  mul_mem' := c.mul

中文:
定义 submonoid
  签名: : 子幺半群 (M × M) where
  定义体: { x | c x.1 x.2 }
  one_mem' := c.iseqv.1 1
  mul_mem' := c.mul
-/
protected def submonoid : Submonoid (M × M) where
  carrier := { x | c x.1 x.2 }
  one_mem' := c.iseqv.1 1
  mul_mem' := c.mul

variable {c}

/-- The congruence relation on a monoid `M` from a submonoid of `M × M` for which membership
is an equivalence relation. -/
@[to_additive /-- The additive congruence relation on an `AddMonoid` `M` from
an `AddSubmonoid` of `M × M` for which membership is an equivalence relation. -/]
/--
Definition of `ofSubmonoid` / `ofSubmonoid` 的定义

English:
definition ofSubmonoid
  signature: (N : Submonoid (M × M)) (H : Equivalence fun x y => (x, y) in N)
  body: (x, y) in N
  iseqv := H
  mul' := N.mul_mem

中文:
定义 ofSubmonoid
  签名: (N : 子幺半群 (M × M)) (H : 等价 fun x y => (x, y) in N)
  定义体: (x, y) in N
  iseqv := H
  mul' := N.mul_mem
-/
def ofSubmonoid (N : Submonoid (M × M)) (H : Equivalence fun x y => (x, y) in N) : Con M where
  r x y := (x, y) in N
  iseqv := H
  mul' := N.mul_mem

/-- Coercion from a congruence relation `c` on a monoid `M` to the submonoid of `M × M` whose
elements are `(x, y)` such that `x` is related to `y` by `c`. -/
@[to_additive /-- Coercion from a congruence relation `c` on an `AddMonoid` `M`
to the `AddSubmonoid` of `M × M` whose elements are `(x, y)` such that `x`
is related to `y` by `c`. -/]
/--
Instance `toSubmonoid` / 实例 `toSubmonoid`

English:
instance toSubmonoid
  signature: : Coe (Con M) (Submonoid (M × M))
  body: ⟨fun c => c.submonoid⟩

@[to_additive]

中文:
实例 toSubmonoid
  签名: : Coe (Con M) (子幺半群 (M × M))
  定义体: ⟨fun c => c.submonoid⟩

@[to_additive]

Depends on / 依赖: c.submonoid, submonoid
-/
instance toSubmonoid : Coe (Con M) (Submonoid (M × M)) :=
  ⟨fun c => c.submonoid⟩

@[to_additive]
/--
theorem `mem_coe` / 定理 `mem_coe`

English:
theorem mem_coe
  given: {c : Con M} {x y}
  statement: (x, y) in (↑c : Submonoid (M × M)) ↔ (x, y) in c
  proof: Iff.rfl

@[to_additive]

中文:
定理 mem_coe
  条件: {c : Con M} {x y}
  结论: (x, y) in (↑c : 子幺半群 (M × M)) ↔ (x, y) in c
  证明: Iff.rfl

@[to_additive]

Depends on / 依赖: Iff.rfl
-/
theorem mem_coe {c : Con M} {x y} : (x, y) in (↑c : Submonoid (M × M)) ↔ (x, y) in c :=
  Iff.rfl

@[to_additive]
/--
theorem `to_submonoid_inj` / 定理 `to_submonoid_inj`

English:
theorem to_submonoid_inj
  given: (c d : Con M) (H : (c : Submonoid (M × M)) = d)
  statement: c = d
  proof: ext fun x y => show (x, y) in c.submonoid ↔ (x, y) in d from H ▸ Iff.rfl

@[to_additive]

中文:
定理 to_submonoid_inj
  条件: (c d : Con M) (H : (c : 子幺半群 (M × M)) = d)
  结论: c = d
  证明: ext fun x y => show (x, y) in c.submonoid ↔ (x, y) in d from H ▸ Iff.rfl

@[to_additive]

Depends on / 依赖: Iff.rfl, c.submonoid, submonoid
-/
theorem to_submonoid_inj (c d : Con M) (H : (c : Submonoid (M × M)) = d) : c = d :=
  ext fun x y => show (x, y) in c.submonoid ↔ (x, y) in d from H ▸ Iff.rfl

@[to_additive]
/--
theorem `le_iff` / 定理 `le_iff`

English:
theorem le_iff
  given: {c d : Con M}
  statement: c <= d ↔ (c : Submonoid (M × M)) <= d
  proof: ⟨fun h _ H => h H, fun h x y hc => h show (x, y) in c from hc⟩

中文:
定理 le_iff
  条件: {c d : Con M}
  结论: c <= d ↔ (c : 子幺半群 (M × M)) <= d
  证明: ⟨fun h _ H => h H, fun h x y hc => h show (x, y) in c from hc⟩
-/
theorem le_iff {c d : Con M} : c <= d ↔ (c : Submonoid (M × M)) <= d :=
⟨fun h _ H => h H, fun h x y hc => h show (x, y) in c from hc⟩

variable (x y : M)

@[to_additive (attr := simp)]
-- Porting note (https://github.com/leanprover-community/mathlib4/issues/11036): removed dot notation
/--
theorem `mrange_mk'` / 定理 `mrange_mk'`

English:
theorem mrange_mk'
  statement: MonoidHom.mrange c.mk' = ⊤
  proof: MonoidHom.mrange_eq_top.2 mk'_surjective

中文:
定理 mrange_mk'
  结论: 幺半群态射.mrange c.mk' = ⊤
  证明: MonoidHom.mrange_eq_top.2 mk'_surjective

Depends on / 依赖: MonoidHom, MonoidHom.mrange_eq_top, _surjective, mrange_eq_top
-/
theorem mrange_mk' : MonoidHom.mrange c.mk' = ⊤ :=
  MonoidHom.mrange_eq_top.2 mk'_surjective

variable {f : M ->* P}

/-- Given a congruence relation `c` on a monoid and a homomorphism `f` constant on `c`'s
equivalence classes, `f` has the same image as the homomorphism that `f` induces on the
quotient. -/
@[to_additive /-- Given an additive congruence relation `c` on an `AddMonoid` and a homomorphism `f`
constant on `c`'s equivalence classes, `f` has the same image as the homomorphism that `f` induces
on the quotient. -/]
/--
theorem `lift_range` / 定理 `lift_range`

English:
theorem lift_range
  given: (H : c <= ker f)
  statement: MonoidHom.mrange (c.lift f H) = MonoidHom.mrange f
  proof: Submonoid.ext fun x => ⟨by rintro ⟨⟨y⟩, hy⟩; exact ⟨y, hy⟩, fun ⟨y, hy⟩ => ⟨↑y, hy⟩⟩

中文:
定理 lift_range
  条件: (H : c <= ker f)
  结论: 幺半群态射.mrange (c.lift f H) = 幺半群态射.mrange f
  证明: Submonoid.ext fun x => ⟨by rintro ⟨⟨y⟩, hy⟩; exact ⟨y, hy⟩, fun ⟨y, hy⟩ => ⟨↑y, hy⟩⟩

Depends on / 依赖: Submonoid, Submonoid.ext
-/
theorem lift_range (H : c <= ker f) : MonoidHom.mrange (c.lift f H) = MonoidHom.mrange f :=
  Submonoid.ext fun x => ⟨by rintro ⟨⟨y⟩, hy⟩; exact ⟨y, hy⟩, fun ⟨y, hy⟩ => ⟨↑y, hy⟩⟩

/-- Given a monoid homomorphism `f`, the induced homomorphism on the quotient by `f`'s kernel has
the same image as `f`. -/
@[to_additive (attr := simp) /-- Given an `AddMonoid` homomorphism `f`, the induced homomorphism
on the quotient by `f`'s kernel has the same image as `f`. -/]
/--
theorem `kerLift_range_eq` / 定理 `kerLift_range_eq`

English:
theorem kerLift_range_eq
  statement: MonoidHom.mrange (kerLift f) = MonoidHom.mrange f
  proof: lift_range fun _ _ => id

中文:
定理 kerLift_range_eq
  结论: 幺半群态射.mrange (kerLift f) = 幺半群态射.mrange f
  证明: lift_range fun _ _ => id

Depends on / 依赖: lift_range
-/
theorem kerLift_range_eq : MonoidHom.mrange (kerLift f) = MonoidHom.mrange f :=
  lift_range fun _ _ => id

variable (c)

/-- The **first isomorphism theorem for monoids**. -/
@[to_additive /-- The first isomorphism theorem for `AddMonoid`s. -/]
/--
Definition of `quotientKerEquivRange` / `quotientKerEquivRange` 的定义

English:
definition quotientKerEquivRange
  signature: (f : M ->* P)
  body: { Equiv.ofBijective
        ((@MulEquiv.toMonoidHom (MonoidHom.mrange (kerLift f)) _ _ _ <|
              MulEquiv.submonoidCongr kerLift_range_eq).comp
          (kerLift f).mrangeRestrict) <|
      ((Equiv.bijective (@MulEquiv.toEquiv (MonoidHom.mrange (kerLift f)) _ _ _ <|
          MulEquiv.subm

中文:
定义 quotientKerEquivRange
  签名: (f : M ->* P)
  定义体: { Equiv.ofBijective
        ((@MulEquiv.toMonoidHom (MonoidHom.mrange (kerLift f)) _ _ _ <|
              MulEquiv.submonoidCongr kerLift_range_eq).comp
          (kerLift f).mrangeRestrict) <|
      ((Equiv.bijective (@MulEquiv.toEquiv (MonoidHom.mrange (kerLift f)) _ _ _ <|
          MulEquiv.subm

Depends on / 依赖: Equiv.bijective, Equiv.ofBijective, MonoidHom, MonoidHom.mrange, MulEquiv, MulEquiv.submonoidCongr, MulEquiv.toEquiv, MulEquiv.toMonoidHom, bijective, injections, kerLift, kerLift_injective, kerLift_range_eq, map_mul, mrange, mrangeRestrict, ofBijective, submonoidCongr, toEquiv, toMonoidHom
-/
noncomputable def quotientKerEquivRange (f : M ->* P) : (ker f).Quotient ≃* MonoidHom.mrange f :=
  { Equiv.ofBijective
        ((@MulEquiv.toMonoidHom (MonoidHom.mrange (kerLift f)) _ _ _ <|
              MulEquiv.submonoidCongr kerLift_range_eq).comp
          (kerLift f).mrangeRestrict) <|
      ((Equiv.bijective (@MulEquiv.toEquiv (MonoidHom.mrange (kerLift f)) _ _ _ <|
          MulEquiv.submonoidCongr kerLift_range_eq)).comp
        ⟨fun x y h =>
kerLift_injective f by rcases x with ⟨⟩; rcases y with ⟨⟩; injections,
          fun ⟨w, z, hz⟩ => ⟨z, by rcases hz with ⟨⟩; rfl⟩⟩) with
    map_mul' := map_mul _ }

/-- The first isomorphism theorem for monoids in the case of a homomorphism with right inverse. -/
@[to_additive (attr := simps)
  /-- The first isomorphism theorem for `AddMonoid`s in the case of a homomorphism
  with right inverse. -/]
/--
Definition of `quotientKerEquivOfRightInverse` / `quotientKerEquivOfRightInverse` 的定义

English:
definition quotientKerEquivOfRightInverse
  signature: (f : M ->* P) (g : P -> M) (hf : Function.RightInverse g f)
  body: { kerLift f with
    toFun := kerLift f
    invFun := (↑) ∘ g
    left_inv := fun x => kerLift_injective _ (by rw [Function.comp_apply, kerLift_mk, hf])
    right_inv := fun x => by (conv_rhs => rw [← hf x]); rfl }

中文:
定义 quotientKerEquivOfRightInverse
  签名: (f : M ->* P) (g : P -> M) (hf : 函数.右逆 g f)
  定义体: { kerLift f with
    toFun := kerLift f
    invFun := (↑) ∘ g
    left_inv := fun x => kerLift_injective _ (by rw [Function.comp_apply, kerLift_mk, hf])
    right_inv := fun x => by (conv_rhs => rw [← hf x]); rfl }

Depends on / 依赖: Function, Function.comp_apply, comp_apply, conv_rhs, invFun, kerLift, kerLift_injective, kerLift_mk, left_inv, right_inv
-/
def quotientKerEquivOfRightInverse (f : M ->* P) (g : P -> M) (hf : Function.RightInverse g f) :
    (ker f).Quotient ≃* P :=
  { kerLift f with
    toFun := kerLift f
    invFun := (↑) ∘ g
    left_inv := fun x => kerLift_injective _ (by rw [Function.comp_apply, kerLift_mk, hf])
    right_inv := fun x => by (conv_rhs => rw [← hf x]); rfl }

/-- The first isomorphism theorem for Monoids in the case of a surjective homomorphism.

For a `computable` version, see `Con.quotientKerEquivOfRightInverse`.
-/
@[to_additive /-- The first isomorphism theorem for `AddMonoid`s in the case of a surjective
homomorphism.

For a `computable` version, see `AddCon.quotientKerEquivOfRightInverse`. -/]
/--
Definition of `quotientKerEquivOfSurjective` / `quotientKerEquivOfSurjective` 的定义

English:
definition quotientKerEquivOfSurjective
  signature: (f : M ->* P) (hf : Surjective f)
  body: quotientKerEquivOfRightInverse _ _ hf.hasRightInverse.choose_spec

中文:
定义 quotientKerEquivOfSurjective
  签名: (f : M ->* P) (hf : 满射 f)
  定义体: quotientKerEquivOfRightInverse _ _ hf.hasRightInverse.choose_spec

Depends on / 依赖: choose_spec, hasRightInverse, hf.hasRightInverse.choose_spec, quotientKerEquivOfRightInverse
-/
noncomputable def quotientKerEquivOfSurjective (f : M ->* P) (hf : Surjective f) :
    (ker f).Quotient ≃* P :=
  quotientKerEquivOfRightInverse _ _ hf.hasRightInverse.choose_spec

/-- If e : M →* N is surjective then (c.comap e).Quotient ≃* c.Quotient with c : Con N -/
@[to_additive /-- If e : M →* N is surjective then (c.comap e).Quotient ≃* c.Quotient with c :
AddCon N -/]
/--
Definition of `comapQuotientEquivOfSurj` / `comapQuotientEquivOfSurj` 的定义

English:
definition comapQuotientEquivOfSurj
  signature: (c : Con M) (f : N ->* M) (hf : Function.Surjective f)
  body: (Con.congr (.refl _) Con.comap_eq).trans Con.quotientKerEquivOfSurjective (c.mk'.comp f)
    Con.mk'_surjective.comp hf

@[to_additive (attr := simp)]

中文:
定义 comapQuotientEquivOfSurj
  签名: (c : Con M) (f : N ->* M) (hf : 函数.满射 f)
  定义体: (Con.congr (.refl _) Con.comap_eq).trans Con.quotientKerEquivOfSurjective (c.mk'.comp f)
    Con.mk'_surjective.comp hf

@[to_additive (attr := simp)]

Depends on / 依赖: Con.comap_eq, Con.congr, Con.mk, Con.quotientKerEquivOfSurjective, _surjective, _surjective.comp, c.mk, comap_eq, quotientKerEquivOfSurjective
-/
noncomputable def comapQuotientEquivOfSurj (c : Con M) (f : N ->* M) (hf : Function.Surjective f) :
    (Con.comap f f.map_mul c).Quotient ≃* c.Quotient :=
(Con.congr (.refl _) Con.comap_eq).trans Con.quotientKerEquivOfSurjective (c.mk'.comp f)
    Con.mk'_surjective.comp hf

@[to_additive (attr := simp)]
/--
lemma `comapQuotientEquivOfSurj_mk` / 引理 `comapQuotientEquivOfSurj_mk`

English:
lemma comapQuotientEquivOfSurj_mk
  given: (c : Con M) {f : N ->* M} (hf : Function.Surjective f) (x : N)
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 comapQuotientEquivOfSurj_mk
  条件: (c : Con M) {f : N ->* M} (hf : 函数.满射 f) (x : N)
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma comapQuotientEquivOfSurj_mk (c : Con M) {f : N ->* M} (hf : Function.Surjective f) (x : N) :
    comapQuotientEquivOfSurj c f hf x = f x := rfl

@[to_additive (attr := simp)]
/--
lemma `comapQuotientEquivOfSurj_symm_mk` / 引理 `comapQuotientEquivOfSurj_symm_mk`

English:
lemma comapQuotientEquivOfSurj_symm_mk
  given: (c : Con M) {f : N ->* M} (hf) (x : N)
  proof: (MulEquiv.symm_apply_eq (c.comapQuotientEquivOfSurj f hf)).mpr rfl

中文:
引理 comapQuotientEquivOfSurj_symm_mk
  条件: (c : Con M) {f : N ->* M} (hf) (x : N)
  证明: (MulEquiv.symm_apply_eq (c.comapQuotientEquivOfSurj f hf)).mpr rfl

Depends on / 依赖: MulEquiv, MulEquiv.symm_apply_eq, c.comapQuotientEquivOfSurj, comapQuotientEquivOfSurj, symm_apply_eq
-/
lemma comapQuotientEquivOfSurj_symm_mk (c : Con M) {f : N ->* M} (hf) (x : N) :
    (comapQuotientEquivOfSurj c f hf).symm (f x) = x :=
  (MulEquiv.symm_apply_eq (c.comapQuotientEquivOfSurj f hf)).mpr rfl

set_option backward.isDefEq.respectTransparency false in
/-- This version infers the surjectivity of the function from a MulEquiv function -/
@[to_additive (attr := simp) /-- This version infers the surjectivity of the function from a
MulEquiv function -/]
/--
lemma `comapQuotientEquivOfSurj_symm_mk'` / 引理 `comapQuotientEquivOfSurj_symm_mk'`

English:
lemma comapQuotientEquivOfSurj_symm_mk'
  given: (c : Con M) (f : N ≃* M) (x : N)
  proof: (MulEquiv.symm_apply_eq (@comapQuotientEquivOfSurj M N _ _ c f _)).mpr rfl

中文:
引理 comapQuotientEquivOfSurj_symm_mk'
  条件: (c : Con M) (f : N ≃* M) (x : N)
  证明: (MulEquiv.symm_apply_eq (@comapQuotientEquivOfSurj M N _ _ c f _)).mpr rfl

Depends on / 依赖: MulEquiv, MulEquiv.symm_apply_eq, comapQuotientEquivOfSurj, symm_apply_eq
-/
lemma comapQuotientEquivOfSurj_symm_mk' (c : Con M) (f : N ≃* M) (x : N) :
    ((@MulEquiv.symm (Con.Quotient (comap ⇑f _ c)) _ _ _
      (comapQuotientEquivOfSurj c (f : N ->* M) f.surjective)) ⟦f x⟧) = ↑x :=
  (MulEquiv.symm_apply_eq (@comapQuotientEquivOfSurj M N _ _ c f _)).mpr rfl

/-- The **second isomorphism theorem for monoids**. -/
@[to_additive /-- The second isomorphism theorem for `AddMonoid`s. -/]
/--
Definition of `comapQuotientEquiv` / `comapQuotientEquiv` 的定义

English:
definition comapQuotientEquiv
  signature: (f : N ->* M)
  body: (Con.congr (.refl _) comap_eq).trans quotientKerEquivRange c.mk'.comp f

中文:
定义 comapQuotientEquiv
  签名: (f : N ->* M)
  定义体: (Con.congr (.refl _) comap_eq).trans quotientKerEquivRange c.mk'.comp f

Depends on / 依赖: Con.congr, c.mk, comap_eq, quotientKerEquivRange
-/
noncomputable def comapQuotientEquiv (f : N ->* M) :
    (comap f f.map_mul c).Quotient ≃* MonoidHom.mrange (c.mk'.comp f) :=
(Con.congr (.refl _) comap_eq).trans quotientKerEquivRange c.mk'.comp f

/-- The **third isomorphism theorem for monoids**. -/
@[to_additive /-- The third isomorphism theorem for `AddMonoid`s. -/]
/--
Definition of `quotientQuotientEquivQuotient` / `quotientQuotientEquivQuotient` 的定义

English:
definition quotientQuotientEquivQuotient
  signature: (c d : Con M) (h : c <= d)
  body: { Setoid.quotientQuotientEquivQuotient c.toSetoid d.toSetoid h with
    map_mul' := fun x y =>
      Con.induction_on₂ x y fun w z =>
        Con.induction_on₂ w z fun a b =>
          show _ = d.mk' a * d.mk' b by rw [← d.mk'.map_mul]; rfl }

中文:
定义 quotientQuotientEquivQuotient
  签名: (c d : Con M) (h : c <= d)
  定义体: { Setoid.quotientQuotientEquivQuotient c.toSetoid d.toSetoid h with
    map_mul' := fun x y =>
      Con.induction_on₂ x y fun w z =>
        Con.induction_on₂ w z fun a b =>
          show _ = d.mk' a * d.mk' b by rw [← d.mk'.map_mul]; rfl }

Depends on / 依赖: Con.induction_on, Setoid, Setoid.quotientQuotientEquivQuotient, c.toSetoid, d.mk, d.toSetoid, map_mul, quotientQuotientEquivQuotient, toSetoid
-/
def quotientQuotientEquivQuotient (c d : Con M) (h : c <= d) :
    (ker (c.map d h)).Quotient ≃* d.Quotient :=
  { Setoid.quotientQuotientEquivQuotient c.toSetoid d.toSetoid h with
    map_mul' := fun x y =>
      Con.induction_on₂ x y fun w z =>
        Con.induction_on₂ w z fun a b =>
          show _ = d.mk' a * d.mk' b by rw [← d.mk'.map_mul]; rfl }

end MulOneClass

section Monoids

@[to_additive]
/--
theorem `smul` / 定理 `smul`

English:
theorem smul
  statement: {α M : Type*} [MulOneClass M] [SMul α M] [IsScalarTower α M M] (c : Con M) (a : α)
  proof: by
  simpa only [smul_one_mul] using c.mul (c.refl' (a • (1 : M) : M)) h

中文:
定理 smul
  结论: {α M : 类型} [MulOne类 M] [标量乘法 α M] [标量塔 α M M] (c : Con M) (a : α)
  证明: by
  simpa only [smul_one_mul] using c.mul (c.refl' (a • (1 : M) : M)) h

Depends on / 依赖: c.mul, c.refl, smul_one_mul
-/
theorem smul {α M : Type*} [MulOneClass M] [SMul α M] [IsScalarTower α M M] (c : Con M) (a : α)
    {w x : M} (h : c w x) : c (a • w) (a • x) := by
  simpa only [smul_one_mul] using c.mul (c.refl' (a • (1 : M) : M)) h

end Monoids

section Actions

@[to_additive]
/--
Instance `instSMul` / 实例 `instSMul`

English:
instance instSMul
  signature: {α M : Type*} [MulOneClass M] [SMul α M] [IsScalarTower α M M] (c : Con M)
  body: (Quotient.map' (a • ·)) fun _ _ => c.smul a

@[to_additive]

中文:
实例 instSMul
  签名: {α M : 类型} [MulOne类 M] [标量乘法 α M] [标量塔 α M M] (c : Con M)
  定义体: (Quotient.map' (a • ·)) fun _ _ => c.smul a

@[to_additive]

Depends on / 依赖: Quotient, Quotient.map, c.smul
-/
instance instSMul {α M : Type*} [MulOneClass M] [SMul α M] [IsScalarTower α M M] (c : Con M) :
    SMul α c.Quotient where
  smul a := (Quotient.map' (a • ·)) fun _ _ => c.smul a

@[to_additive]
/--
theorem `coe_smul` / 定理 `coe_smul`

English:
theorem coe_smul
  statement: {α M : Type*} [MulOneClass M] [SMul α M] [IsScalarTower α M M] (c : Con M)
  proof: rfl

中文:
定理 coe_smul
  结论: {α M : 类型} [MulOne类 M] [标量乘法 α M] [标量塔 α M M] (c : Con M)
  证明: rfl
-/
theorem coe_smul {α M : Type*} [MulOneClass M] [SMul α M] [IsScalarTower α M M] (c : Con M)
    (a : α) (x : M) : (↑(a • x) : c.Quotient) = a • (x : c.Quotient) :=
  rfl

/--
Instance `instSMulCommClass` / 实例 `instSMulCommClass`

English:
instance instSMulCommClass
  signature: {α β M : Type*} [MulOneClass M] [SMul α M] [SMul β M]
  body: Quotient.ind' fun m => congr_arg Quotient.mk'' smul_comm a b m

中文:
实例 instSMulCommClass
  签名: {α β M : 类型} [MulOne类 M] [标量乘法 α M] [标量乘法 β M]
  定义体: Quotient.ind' fun m => congr_arg Quotient.mk'' smul_comm a b m

Depends on / 依赖: Quotient, Quotient.ind, Quotient.mk, congr_arg, smul_comm
-/
instance instSMulCommClass {α β M : Type*} [MulOneClass M] [SMul α M] [SMul β M]
    [IsScalarTower α M M] [IsScalarTower β M M] [SMulCommClass α β M] (c : Con M) :
    SMulCommClass α β c.Quotient where
smul_comm a b := Quotient.ind' fun m => congr_arg Quotient.mk'' smul_comm a b m

/--
Instance `instIsScalarTower` / 实例 `instIsScalarTower`

English:
instance instIsScalarTower
  signature: {α β M : Type*} [MulOneClass M] [SMul α β] [SMul α M] [SMul β M]
  body: Quotient.ind' fun m => congr_arg Quotient.mk'' smul_assoc a b m

中文:
实例 instIsScalarTower
  签名: {α β M : 类型} [MulOne类 M] [标量乘法 α β] [标量乘法 α M] [标量乘法 β M]
  定义体: Quotient.ind' fun m => congr_arg Quotient.mk'' smul_assoc a b m

Depends on / 依赖: Quotient, Quotient.ind, Quotient.mk, congr_arg, smul_assoc
-/
instance instIsScalarTower {α β M : Type*} [MulOneClass M] [SMul α β] [SMul α M] [SMul β M]
    [IsScalarTower α M M] [IsScalarTower β M M] [IsScalarTower α β M] (c : Con M) :
    IsScalarTower α β c.Quotient where
smul_assoc a b := Quotient.ind' fun m => congr_arg Quotient.mk'' smul_assoc a b m

/--
Instance `instIsCentralScalar` / 实例 `instIsCentralScalar`

English:
instance instIsCentralScalar
  signature: {α M : Type*} [MulOneClass M] [SMul α M] [SMul αᵐᵒᵖ M]
  body: Quotient.ind' fun m => congr_arg Quotient.mk'' op_smul_eq_smul a m

@[to_additive]

中文:
实例 instIsCentralScalar
  签名: {α M : 类型} [MulOne类 M] [标量乘法 α M] [标量乘法 αᵐᵒᵖ M]
  定义体: Quotient.ind' fun m => congr_arg Quotient.mk'' op_smul_eq_smul a m

@[to_additive]

Depends on / 依赖: Quotient, Quotient.ind, Quotient.mk, congr_arg, op_smul_eq_smul
-/
instance instIsCentralScalar {α M : Type*} [MulOneClass M] [SMul α M] [SMul αᵐᵒᵖ M]
    [IsScalarTower α M M] [IsScalarTower αᵐᵒᵖ M M] [IsCentralScalar α M] (c : Con M) :
    IsCentralScalar α c.Quotient where
op_smul_eq_smul a := Quotient.ind' fun m => congr_arg Quotient.mk'' op_smul_eq_smul a m

@[to_additive]
/--
Instance `mulAction` / 实例 `mulAction`

English:
instance mulAction
  signature: {α M : Type*} [Monoid α] [MulOneClass M] [MulAction α M] [IsScalarTower α M M]
  body: Quotient.ind' fun _ => congr_arg Quotient.mk'' one_smul _ _
mul_smul _ _ := Quotient.ind' fun _ => congr_arg Quotient.mk'' mul_smul _ _ _

中文:
实例 mulAction
  签名: {α M : 类型} [幺半群 α] [MulOne类 M] [乘法作用 α M] [标量塔 α M M]
  定义体: Quotient.ind' fun _ => congr_arg Quotient.mk'' one_smul _ _
mul_smul _ _ := Quotient.ind' fun _ => congr_arg Quotient.mk'' mul_smul _ _ _

Depends on / 依赖: Quotient, Quotient.ind, Quotient.mk, congr_arg, one_smul
-/
instance mulAction {α M : Type*} [Monoid α] [MulOneClass M] [MulAction α M] [IsScalarTower α M M]
    (c : Con M) : MulAction α c.Quotient where
one_smul := Quotient.ind' fun _ => congr_arg Quotient.mk'' one_smul _ _
mul_smul _ _ := Quotient.ind' fun _ => congr_arg Quotient.mk'' mul_smul _ _ _

/--
Instance `mulDistribMulAction` / 实例 `mulDistribMulAction`

English:
instance mulDistribMulAction
  signature: {α M : Type*} [Monoid α] [Monoid M] [MulDistribMulAction α M]
  body: { smul_one := fun _ => congr_arg Quotient.mk'' <| smul_one _
smul_mul := fun _ => Quotient.ind₂' fun _ _ => congr_arg Quotient.mk'' smul_mul' _ _ _ }

中文:
实例 mulDistribMulAction
  签名: {α M : 类型} [幺半群 α] [幺半群 M] [MulDistribMul作用 α M]
  定义体: { smul_one := fun _ => congr_arg Quotient.mk'' <| smul_one _
smul_mul := fun _ => Quotient.ind₂' fun _ _ => congr_arg Quotient.mk'' smul_mul' _ _ _ }

Depends on / 依赖: Quotient, Quotient.ind, Quotient.mk, congr_arg, smul_mul, smul_one
-/
instance mulDistribMulAction {α M : Type*} [Monoid α] [Monoid M] [MulDistribMulAction α M]
    [IsScalarTower α M M] (c : Con M) : MulDistribMulAction α c.Quotient :=
  { smul_one := fun _ => congr_arg Quotient.mk'' <| smul_one _
smul_mul := fun _ => Quotient.ind₂' fun _ _ => congr_arg Quotient.mk'' smul_mul' _ _ _ }

end Actions

end Con
