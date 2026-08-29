/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.CharP.Algebra

/-!
# Characteristic of subrings
-/

public section


universe u v

namespace CharP

/--
Instance `subsemiring` / 实例 `subsemiring`

English:
instance subsemiring
  signature: (R : Type u) [Semiring R] (p : Nat) [CharP R p] (S : Subsemiring R)
  body: ⟨fun x =>
Iff.symm
      (CharP.cast_eq_zero_iff R p x).symm.trans
⟨fun h => Subtype.ext show S.subtype x = 0 by rw [map_natCast, h], fun h =>
          map_natCast S.subtype x ▸ by rw [h, map_zero]⟩⟩

中文:
实例 subsemiring
  签名: (R : 类型u) [Semiring R] (p : 自然数) [CharP R p] (S : Subsemiring R)
  定义体: ⟨fun x =>
Iff.symm
      (CharP.cast_eq_zero_iff R p x).symm.trans
⟨fun h => Subtype.ext show S.subtype x = 0 by rw [map_natCast, h], fun h =>
          map_natCast S.subtype x ▸ by rw [h, map_zero]⟩⟩

Depends on / 依赖: CharP.cast_eq_zero_iff, Iff.symm, S.subtype, Subtype, Subtype.ext, cast_eq_zero_iff, map_natCast, map_zero, subtype, symm.trans
-/
instance subsemiring (R : Type u) [Semiring R] (p : Nat) [CharP R p] (S : Subsemiring R) :
    CharP S p :=
  ⟨fun x =>
Iff.symm
      (CharP.cast_eq_zero_iff R p x).symm.trans
⟨fun h => Subtype.ext show S.subtype x = 0 by rw [map_natCast, h], fun h =>
          map_natCast S.subtype x ▸ by rw [h, map_zero]⟩⟩

/--
Instance `subring` / 实例 `subring`

English:
instance subring
  signature: (R : Type u) [Ring R] (p : Nat) [CharP R p] (S : Subring R)
  body: ⟨fun x =>
Iff.symm
      (CharP.cast_eq_zero_iff R p x).symm.trans
⟨fun h => Subtype.ext show S.subtype x = 0 by rw [map_natCast, h], fun h =>
          map_natCast S.subtype x ▸ by rw [h, map_zero]⟩⟩

中文:
实例 subring
  签名: (R : 类型u) [Ring R] (p : 自然数) [CharP R p] (S : Subring R)
  定义体: ⟨fun x =>
Iff.symm
      (CharP.cast_eq_zero_iff R p x).symm.trans
⟨fun h => Subtype.ext show S.subtype x = 0 by rw [map_natCast, h], fun h =>
          map_natCast S.subtype x ▸ by rw [h, map_zero]⟩⟩

Depends on / 依赖: CharP.cast_eq_zero_iff, Iff.symm, S.subtype, Subtype, Subtype.ext, cast_eq_zero_iff, map_natCast, map_zero, subtype, symm.trans
-/
instance subring (R : Type u) [Ring R] (p : Nat) [CharP R p] (S : Subring R) : CharP S p :=
  ⟨fun x =>
Iff.symm
      (CharP.cast_eq_zero_iff R p x).symm.trans
⟨fun h => Subtype.ext show S.subtype x = 0 by rw [map_natCast, h], fun h =>
          map_natCast S.subtype x ▸ by rw [h, map_zero]⟩⟩

/--
Instance `subring'` / 实例 `subring'`

English:
instance subring'
  signature: (R : Type u) [CommRing R] (p : Nat) [CharP R p] (S : Subring R)
  body: CharP.subring R p S

中文:
实例 subring'
  签名: (R : 类型u) [CommRing R] (p : 自然数) [CharP R p] (S : Subring R)
  定义体: CharP.subring R p S

Depends on / 依赖: CharP.subring, subring
-/
instance subring' (R : Type u) [CommRing R] (p : Nat) [CharP R p] (S : Subring R) : CharP S p :=
  CharP.subring R p S

/--
theorem `charP_center_iff` / 定理 `charP_center_iff`

English:
theorem charP_center_iff
  given: {R : Type u} [Ring R] {p : Nat}
  proof: (algebraMap (Subring.center R) R).charP_iff Subtype.val_injective p

中文:
定理 charP_center_iff
  条件: {R : 类型u} [Ring R] {p : 自然数}
  证明: (algebraMap (Subring.center R) R).charP_iff Subtype.val_injective p

Depends on / 依赖: Subring, Subring.center, Subtype, Subtype.val_injective, algebraMap, center, charP_iff, val_injective
-/
theorem charP_center_iff {R : Type u} [Ring R] {p : Nat} :
    CharP (Subring.center R) p ↔ CharP R p :=
  (algebraMap (Subring.center R) R).charP_iff Subtype.val_injective p

end CharP

namespace ExpChar

/--
theorem `expChar_center_iff` / 定理 `expChar_center_iff`

English:
theorem expChar_center_iff
  given: {R : Type u} [Ring R] {p : Nat}
  proof: (algebraMap (Subring.center R) R).expChar_iff Subtype.val_injective p

中文:
定理 expChar_center_iff
  条件: {R : 类型u} [Ring R] {p : 自然数}
  证明: (algebraMap (Subring.center R) R).expChar_iff Subtype.val_injective p

Depends on / 依赖: Subring, Subring.center, Subtype, Subtype.val_injective, algebraMap, center, expChar_iff, val_injective
-/
theorem expChar_center_iff {R : Type u} [Ring R] {p : Nat} :
    ExpChar (Subring.center R) p ↔ ExpChar R p :=
  (algebraMap (Subring.center R) R).expChar_iff Subtype.val_injective p

end ExpChar
