/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Jireh Loreaux
-/
module

public import Mathlib.Algebra.Group.Center
public import Mathlib.Algebra.Group.Subsemigroup.Defs

/-!
# Centers of semigroups, as subsemigroups.

## Main definitions

* `Subsemigroup.center`: the center of a semigroup
* `AddSubsemigroup.center`: the center of an additive semigroup

We provide `Submonoid.center`, `AddSubmonoid.center`, `Subgroup.center`, `AddSubgroup.center`,
`Subsemiring.center`, and `Subring.center` in other files.

## References

* [Cabrera García and Rodríguez Palacios, Non-associative normed algebras. Volume 1]
  [cabreragarciarodriguezpalacios2014]
-/

@[expose] public section

assert_not_exists RelIso Finset

/-! ### `Set.center` as a `Subsemigroup`. -/

variable (M)
namespace Subsemigroup

section Mul
variable [Mul M]

/-- The center of a semigroup `M` is the set of elements that commute with everything in `M` -/
@[to_additive /-- The center of an additive semigroup `M` is the set of elements that commute with
everything in `M` -/]
/--
Definition of `center` / `center` 的定义

English:
definition center
  signature: : Subsemigroup M where
  body: Set.center M
  mul_mem' := Set.mul_mem_center

中文:
定义 center
  签名: : Subsemigroup M where
  定义体: Set.center M
  mul_mem' := Set.mul_mem_center

Depends on / 依赖: Set.center, center
-/
def center : Subsemigroup M where
  carrier := Set.center M
  mul_mem' := Set.mul_mem_center

variable {M}

/-- The center of a magma is commutative and associative. -/
@[to_additive /-- The center of an additive magma is commutative and associative. -/]
/--
Instance `center.commSemigroup` / 实例 `center.commSemigroup`

English:
instance center.commSemigroup
  signature: : CommSemigroup (center M) where
  body: Subtype.ext b.2.mid_assoc _ _
mul_comm a _ := Subtype.ext a.2.comm _

中文:
实例 center.commSemigroup
  签名: : CommSemigroup (center M) where
  定义体: Subtype.ext b.2.mid_assoc _ _
mul_comm a _ := Subtype.ext a.2.comm _

Depends on / 依赖: Subtype, Subtype.ext, mid_assoc
-/
instance center.commSemigroup : CommSemigroup (center M) where
mul_assoc _ b _ := Subtype.ext b.2.mid_assoc _ _
mul_comm a _ := Subtype.ext a.2.comm _

end Mul

section Semigroup
variable {M} [Semigroup M]

@[to_additive]
/--
theorem `mem_center_iff` / 定理 `mem_center_iff`

English:
theorem mem_center_iff
  given: {z : M}
  statement: z in center M ↔ forall g, g * z = z * g
  proof: by
  rw [← Semigroup.mem_center_iff]
  exact Iff.rfl

@[to_additive]

中文:
定理 mem_center_iff
  条件: {z : M}
  结论: z in center M ↔ 对任意 g, g * z = z * g
  证明: by
  rw [← Semigroup.mem_center_iff]
  exact Iff.rfl

@[to_additive]

Depends on / 依赖: Iff.rfl, Semigroup, Semigroup.mem_center_iff, mem_center_iff
-/
theorem mem_center_iff {z : M} : z in center M ↔ forall g, g * z = z * g := by
  rw [← Semigroup.mem_center_iff]
  exact Iff.rfl

@[to_additive]
/--
Instance `decidableMemCenter` / 实例 `decidableMemCenter`

English:
instance decidableMemCenter
  signature: (a) [Decidable <| forall b : M, b * a = a * b]
  body: decidable_of_iff' _ Semigroup.mem_center_iff

中文:
实例 decidableMemCenter
  签名: (a) [Decidable <| 对任意 b : M, b * a = a * b]
  定义体: decidable_of_iff' _ Semigroup.mem_center_iff

Depends on / 依赖: Semigroup, Semigroup.mem_center_iff, decidable_of_iff, mem_center_iff
-/
instance decidableMemCenter (a) [Decidable <| forall b : M, b * a = a * b] :
    Decidable (a in center M) :=
  decidable_of_iff' _ Semigroup.mem_center_iff

end Semigroup

section CommSemigroup
variable [CommSemigroup M]

@[to_additive (attr := simp)]
/--
theorem `center_eq_top` / 定理 `center_eq_top`

English:
theorem center_eq_top
  statement: center M = ⊤
  proof: SetLike.coe_injective (Set.center_eq_univ M)

中文:
定理 center_eq_top
  结论: center M = ⊤
  证明: SetLike.coe_injective (Set.center_eq_univ M)

Depends on / 依赖: Set.center_eq_univ, SetLike, SetLike.coe_injective, center_eq_univ, coe_injective
-/
theorem center_eq_top : center M = ⊤ :=
  SetLike.coe_injective (Set.center_eq_univ M)

end CommSemigroup

end Subsemigroup
