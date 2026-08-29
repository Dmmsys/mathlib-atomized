/-
Copyright (c) 2019 Abhimanyu Pallavi Sudhir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhimanyu Pallavi Sudhir, Violeta Hernández Palacios
-/
module

public import Mathlib.Algebra.Order.Ring.StandardPart
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Order.Filter.FilterProduct

/-!
# Construction of the hyperreal numbers as an ultraproduct of real sequences

We define the `Hyperreal` numbers as quotients of sequences `ℕ → ℝ` by an ultrafilter. These form
a field, and we prove some of their basic properties.

Note that most of the machinery that is usually defined for the specific purpose of non-standard
analysis (infinitesimal and infinite elements, standard parts) has been generalized to other
non-archimedean fields. In particular:

- `ArchimedeanClass` can be used to measure whether an element is infinitesimal (`0 < mk x`) or
  infinite (`mk x < 0`).
- `ArchimedeanClass.stdPart` generalizes the standard part function to a general ordered field.

## Todo

Use Łoś's Theorem `FirstOrder.Language.Ultraproduct.sentence_realize` to formalize the transfer
principle on `Hyperreal`.
-/

@[expose] public section

open ArchimedeanClass Filter Germ Topology

noncomputable section

/--
Definition of `Hyperreal` / `Hyperreal` 的定义

English:
definition Hyperreal
  signature: : Type
  body: Germ (hyperfilter Nat : Filter Nat) Real
deriving Inhabited

中文:
定义 Hyperreal
  签名: : Type
  定义体: Germ (hyperfilter Nat : Filter Nat) Real
deriving Inhabited

Depends on / 依赖: Filter, hyperfilter
-/
def Hyperreal : Type :=
  Germ (hyperfilter Nat : Filter Nat) Real
deriving Inhabited

namespace Hyperreal

@[inherit_doc] notation "Real*" => Hyperreal

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Field Real*
  body: inferInstanceAs (Field (Germ _ _))

中文:
实例 :
  签名: Field 实数*
  定义体: inferInstanceAs (Field (Germ _ _))
-/
instance : Field Real* :=
  inferInstanceAs (Field (Germ _ _))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LinearOrder Real*
  body: inferInstanceAs (LinearOrder (Germ _ _))

中文:
实例 :
  签名: LinearOrder 实数*
  定义体: inferInstanceAs (LinearOrder (Germ _ _))

Depends on / 依赖: LinearOrder
-/
instance : LinearOrder Real* :=
  inferInstanceAs (LinearOrder (Germ _ _))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsStrictOrderedRing Real*
  body: inferInstanceAs (IsStrictOrderedRing (Germ _ _))

中文:
实例 :
  签名: IsStrictOrderedRing 实数*
  定义体: inferInstanceAs (IsStrictOrderedRing (Germ _ _))

Depends on / 依赖: IsStrictOrderedRing
-/
instance : IsStrictOrderedRing Real* :=
  inferInstanceAs (IsStrictOrderedRing (Germ _ _))

/--
Definition of `ofReal` / `ofReal` 的定义

English:
definition ofReal
  signature: : Real -> Real*
  body: const

中文:
定义 ofReal
  签名: : 实数 -> 实数*
  定义体: const
-/
@[coe] def ofReal : Real -> Real* := const

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeTC Real Real*
  body: ⟨ofReal⟩

@[simp, norm_cast]

中文:
实例 :
  签名: CoeTC 实数 实数*
  定义体: ⟨ofReal⟩

@[simp, norm_cast]

Depends on / 依赖: CategoryTheory, CategoryTheory.mono_iff_injective, F.map, Functor, Functor.map_id, WidePushoutShape, WidePushoutShape.hom_id, eq_iff, forall_comm, forall_eq, hom_id, id_apply, map_id, mono_iff_injective, ofReal
-/
instance : CoeTC Real Real* := ⟨ofReal⟩

@[simp, norm_cast]
/--
theorem `coe_eq_coe` / 定理 `coe_eq_coe`

English:
theorem coe_eq_coe
  given: {x y : Real}
  statement: (x : Real*) = y ↔ x = y
  proof: Germ.const_inj

中文:
定理 coe_eq_coe
  条件: {x y : 实数}
  结论: (x : 实数*) = y ↔ x = y
  证明: Germ.const_inj

Depends on / 依赖: Germ.const_inj, const_inj
-/
theorem coe_eq_coe {x y : Real} : (x : Real*) = y ↔ x = y :=
  Germ.const_inj

/--
theorem `coe_ne_coe` / 定理 `coe_ne_coe`

English:
theorem coe_ne_coe
  given: {x y : Real}
  statement: (x : Real*) != y ↔ x != y
  proof: coe_eq_coe.not

@[simp, norm_cast]

中文:
定理 coe_ne_coe
  条件: {x y : 实数}
  结论: (x : 实数*) != y ↔ x != y
  证明: coe_eq_coe.not

@[simp, norm_cast]

Depends on / 依赖: coe_eq_coe, coe_eq_coe.not
-/
theorem coe_ne_coe {x y : Real} : (x : Real*) != y ↔ x != y :=
  coe_eq_coe.not

@[simp, norm_cast]
/--
theorem `coe_eq_zero` / 定理 `coe_eq_zero`

English:
theorem coe_eq_zero
  given: {x : Real}
  statement: (x : Real*) = 0 ↔ x = 0
  proof: coe_eq_coe

@[simp, norm_cast]

中文:
定理 coe_eq_zero
  条件: {x : 实数}
  结论: (x : 实数*) = 0 ↔ x = 0
  证明: coe_eq_coe

@[simp, norm_cast]

Depends on / 依赖: coe_eq_coe
-/
theorem coe_eq_zero {x : Real} : (x : Real*) = 0 ↔ x = 0 :=
  coe_eq_coe

@[simp, norm_cast]
/--
theorem `coe_eq_one` / 定理 `coe_eq_one`

English:
theorem coe_eq_one
  given: {x : Real}
  statement: (x : Real*) = 1 ↔ x = 1
  proof: coe_eq_coe

@[norm_cast]

中文:
定理 coe_eq_one
  条件: {x : 实数}
  结论: (x : 实数*) = 1 ↔ x = 1
  证明: coe_eq_coe

@[norm_cast]

Depends on / 依赖: coe_eq_coe
-/
theorem coe_eq_one {x : Real} : (x : Real*) = 1 ↔ x = 1 :=
  coe_eq_coe

@[norm_cast]
/--
theorem `coe_ne_zero` / 定理 `coe_ne_zero`

English:
theorem coe_ne_zero
  given: {x : Real}
  statement: (x : Real*) != 0 ↔ x != 0
  proof: coe_ne_coe

@[norm_cast]

中文:
定理 coe_ne_zero
  条件: {x : 实数}
  结论: (x : 实数*) != 0 ↔ x != 0
  证明: coe_ne_coe

@[norm_cast]

Depends on / 依赖: coe_ne_coe
-/
theorem coe_ne_zero {x : Real} : (x : Real*) != 0 ↔ x != 0 :=
  coe_ne_coe

@[norm_cast]
/--
theorem `coe_ne_one` / 定理 `coe_ne_one`

English:
theorem coe_ne_one
  given: {x : Real}
  statement: (x : Real*) != 1 ↔ x != 1
  proof: coe_ne_coe

@[simp, norm_cast]

中文:
定理 coe_ne_one
  条件: {x : 实数}
  结论: (x : 实数*) != 1 ↔ x != 1
  证明: coe_ne_coe

@[simp, norm_cast]

Depends on / 依赖: coe_ne_coe
-/
theorem coe_ne_one {x : Real} : (x : Real*) != 1 ↔ x != 1 :=
  coe_ne_coe

@[simp, norm_cast]
/--
theorem `coe_one` / 定理 `coe_one`

English:
theorem coe_one
  statement: ↑(1 : Real) = (1 : Real*)
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_one
  结论: ↑(1 : 实数) = (1 : 实数*)
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_one : ↑(1 : Real) = (1 : Real*) :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_zero` / 定理 `coe_zero`

English:
theorem coe_zero
  statement: ↑(0 : Real) = (0 : Real*)
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_zero
  结论: ↑(0 : 实数) = (0 : 实数*)
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_zero : ↑(0 : Real) = (0 : Real*) :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_inv` / 定理 `coe_inv`

English:
theorem coe_inv
  given: (x : Real)
  statement: ↑x⁻¹ = (x⁻¹ : Real*)
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_inv
  条件: (x : 实数)
  结论: ↑x⁻¹ = (x⁻¹ : 实数*)
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_inv (x : Real) : ↑x⁻¹ = (x⁻¹ : Real*) :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_neg` / 定理 `coe_neg`

English:
theorem coe_neg
  given: (x : Real)
  statement: ↑(-x) = (-x : Real*)
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_neg
  条件: (x : 实数)
  结论: ↑(-x) = (-x : 实数*)
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_neg (x : Real) : ↑(-x) = (-x : Real*) :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_add` / 定理 `coe_add`

English:
theorem coe_add
  given: (x y : Real)
  statement: ↑(x + y) = (x + y : Real*)
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_add
  条件: (x y : 实数)
  结论: ↑(x + y) = (x + y : 实数*)
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_add (x y : Real) : ↑(x + y) = (x + y : Real*) :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_ofNat` / 定理 `coe_ofNat`

English:
theorem coe_ofNat
  given: (n : Nat) [n.AtLeastTwo]
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_ofNat
  条件: (n : 自然数) [n.AtLeastTwo]
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_ofNat (n : Nat) [n.AtLeastTwo] :
    ((ofNat(n) : Real) : Real*) = OfNat.ofNat n :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_mul` / 定理 `coe_mul`

English:
theorem coe_mul
  given: (x y : Real)
  statement: ↑(x * y) = (x * y : Real*)
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_mul
  条件: (x y : 实数)
  结论: ↑(x * y) = (x * y : 实数*)
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_mul (x y : Real) : ↑(x * y) = (x * y : Real*) :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_div` / 定理 `coe_div`

English:
theorem coe_div
  given: (x y : Real)
  statement: ↑(x / y) = (x / y : Real*)
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_div
  条件: (x y : 实数)
  结论: ↑(x / y) = (x / y : 实数*)
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_div (x y : Real) : ↑(x / y) = (x / y : Real*) :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_sub` / 定理 `coe_sub`

English:
theorem coe_sub
  given: (x y : Real)
  statement: ↑(x - y) = (x - y : Real*)
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_sub
  条件: (x y : 实数)
  结论: ↑(x - y) = (x - y : 实数*)
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_sub (x y : Real) : ↑(x - y) = (x - y : Real*) :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_le_coe` / 定理 `coe_le_coe`

English:
theorem coe_le_coe
  given: {x y : Real}
  statement: (x : Real*) <= y ↔ x <= y
  proof: Germ.const_le_iff

@[simp, norm_cast]

中文:
定理 coe_le_coe
  条件: {x y : 实数}
  结论: (x : 实数*) <= y ↔ x <= y
  证明: Germ.const_le_iff

@[simp, norm_cast]

Depends on / 依赖: Germ.const_le_iff, const_le_iff
-/
theorem coe_le_coe {x y : Real} : (x : Real*) <= y ↔ x <= y :=
  Germ.const_le_iff

@[simp, norm_cast]
/--
theorem `coe_lt_coe` / 定理 `coe_lt_coe`

English:
theorem coe_lt_coe
  given: {x y : Real}
  statement: (x : Real*) < y ↔ x < y
  proof: Germ.const_lt_iff

@[simp, norm_cast]

中文:
定理 coe_lt_coe
  条件: {x y : 实数}
  结论: (x : 实数*) < y ↔ x < y
  证明: Germ.const_lt_iff

@[simp, norm_cast]

Depends on / 依赖: Germ.const_lt_iff, const_lt_iff
-/
theorem coe_lt_coe {x y : Real} : (x : Real*) < y ↔ x < y :=
  Germ.const_lt_iff

@[simp, norm_cast]
/--
theorem `coe_nonneg` / 定理 `coe_nonneg`

English:
theorem coe_nonneg
  given: {x : Real}
  statement: 0 <= (x : Real*) ↔ 0 <= x
  proof: coe_le_coe

@[simp, norm_cast]

中文:
定理 coe_nonneg
  条件: {x : 实数}
  结论: 0 <= (x : 实数*) ↔ 0 <= x
  证明: coe_le_coe

@[simp, norm_cast]

Depends on / 依赖: coe_le_coe
-/
theorem coe_nonneg {x : Real} : 0 <= (x : Real*) ↔ 0 <= x :=
  coe_le_coe

@[simp, norm_cast]
/--
theorem `coe_pos` / 定理 `coe_pos`

English:
theorem coe_pos
  given: {x : Real}
  statement: 0 < (x : Real*) ↔ 0 < x
  proof: coe_lt_coe

@[simp, norm_cast]

中文:
定理 coe_pos
  条件: {x : 实数}
  结论: 0 < (x : 实数*) ↔ 0 < x
  证明: coe_lt_coe

@[simp, norm_cast]

Depends on / 依赖: coe_lt_coe
-/
theorem coe_pos {x : Real} : 0 < (x : Real*) ↔ 0 < x :=
  coe_lt_coe

@[simp, norm_cast]
/--
theorem `coe_abs` / 定理 `coe_abs`

English:
theorem coe_abs
  given: (x : Real)
  statement: ((|x| : Real) : Real*) = |↑x|
  proof: const_abs x

@[simp, norm_cast]

中文:
定理 coe_abs
  条件: (x : 实数)
  结论: ((|x| : 实数) : 实数*) = |↑x|
  证明: const_abs x

@[simp, norm_cast]

Depends on / 依赖: const_abs
-/
theorem coe_abs (x : Real) : ((|x| : Real) : Real*) = |↑x| :=
  const_abs x

@[simp, norm_cast]
/--
theorem `coe_max` / 定理 `coe_max`

English:
theorem coe_max
  given: (x y : Real)
  statement: ((max x y : Real) : Real*) = max ↑x ↑y
  proof: Germ.const_max _ _

@[simp, norm_cast]

中文:
定理 coe_max
  条件: (x y : 实数)
  结论: ((max x y : 实数) : 实数*) = max ↑x ↑y
  证明: Germ.const_max _ _

@[simp, norm_cast]

Depends on / 依赖: Germ.const_max, const_max
-/
theorem coe_max (x y : Real) : ((max x y : Real) : Real*) = max ↑x ↑y :=
  Germ.const_max _ _

@[simp, norm_cast]
/--
theorem `coe_min` / 定理 `coe_min`

English:
theorem coe_min
  given: (x y : Real)
  statement: ((min x y : Real) : Real*) = min ↑x ↑y
  proof: Germ.const_min _ _

中文:
定理 coe_min
  条件: (x y : 实数)
  结论: ((min x y : 实数) : 实数*) = min ↑x ↑y
  证明: Germ.const_min _ _

Depends on / 依赖: Germ.const_min, const_min
-/
theorem coe_min (x y : Real) : ((min x y : Real) : Real*) = min ↑x ↑y :=
  Germ.const_min _ _

/-- The canonical map `ℝ → ℝ*` as an `OrderRingHom`. -/
@[simps]
/--
Definition of `coeRingHom` / `coeRingHom` 的定义

English:
definition coeRingHom
  signature: : Real ->+*o Real* where
  body: x
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  monotone' _ _ := coe_le_coe.2

@[simp]

中文:
定义 coeRingHom
  签名: : 实数 ->+*o 实数* where
  定义体: x
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  monotone' _ _ := coe_le_coe.2

@[simp]
-/
def coeRingHom : Real ->+*o Real* where
  toFun x := x
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  monotone' _ _ := coe_le_coe.2

@[simp]
/--
theorem `archimedeanClassMk_coe_nonneg` / 定理 `archimedeanClassMk_coe_nonneg`

English:
theorem archimedeanClassMk_coe_nonneg
  given: (x : Real)
  statement: 0 <= mk (x : Real*)
  proof: mk_map_nonneg_of_archimedean coeRingHom x

@[simp]

中文:
定理 archimedeanClassMk_coe_nonneg
  条件: (x : 实数)
  结论: 0 <= mk (x : 实数*)
  证明: mk_map_nonneg_of_archimedean coeRingHom x

@[simp]

Depends on / 依赖: coeRingHom, mk_map_nonneg_of_archimedean
-/
theorem archimedeanClassMk_coe_nonneg (x : Real) : 0 <= mk (x : Real*) :=
  mk_map_nonneg_of_archimedean coeRingHom x

@[simp]
/--
theorem `archimdeanClassMk_coe` / 定理 `archimdeanClassMk_coe`

English:
theorem archimdeanClassMk_coe
  given: {x : Real} (hx : x != 0)
  statement: mk (x : Real*) = 0
  proof: mk_map_of_archimedean' coeRingHom hx

@[simp]

中文:
定理 archimdeanClassMk_coe
  条件: {x : 实数} (hx : x != 0)
  结论: mk (x : 实数*) = 0
  证明: mk_map_of_archimedean' coeRingHom hx

@[simp]

Depends on / 依赖: coeRingHom, mk_map_of_archimedean
-/
theorem archimdeanClassMk_coe {x : Real} (hx : x != 0) : mk (x : Real*) = 0 :=
  mk_map_of_archimedean' coeRingHom hx

@[simp]
/--
theorem `stdPart_coe` / 定理 `stdPart_coe`

English:
theorem stdPart_coe
  given: (x : Real)
  statement: stdPart (x : Real*) = x
  proof: stdPart_map_real coeRingHom x

中文:
定理 stdPart_coe
  条件: (x : 实数)
  结论: stdPart (x : 实数*) = x
  证明: stdPart_map_real coeRingHom x

Depends on / 依赖: coeRingHom, stdPart_map_real
-/
theorem stdPart_coe (x : Real) : stdPart (x : Real*) = x :=
  stdPart_map_real coeRingHom x

/-! ### Basic constants -/

/--
Definition of `ofSeq` / `ofSeq` 的定义

English:
definition ofSeq
  signature: (f : Nat -> Real)
  body: (↑f : Germ (hyperfilter Nat : Filter Nat) Real)

中文:
定义 ofSeq
  签名: (f : 自然数 -> 实数)
  定义体: (↑f : Germ (hyperfilter Nat : Filter Nat) Real)

Depends on / 依赖: Filter, hyperfilter
-/
def ofSeq (f : Nat -> Real) : Real* := (↑f : Germ (hyperfilter Nat : Filter Nat) Real)

/--
theorem `ofSeq_surjective` / 定理 `ofSeq_surjective`

English:
theorem ofSeq_surjective
  statement: Function.Surjective ofSeq
  proof: Quot.exists_rep

中文:
定理 ofSeq_surjective
  结论: Function.Surjective ofSeq
  证明: Quot.exists_rep

Depends on / 依赖: Quot.exists_rep, exists_rep
-/
theorem ofSeq_surjective : Function.Surjective ofSeq := Quot.exists_rep

/--
theorem `ofSeq_lt_ofSeq` / 定理 `ofSeq_lt_ofSeq`

English:
theorem ofSeq_lt_ofSeq
  given: {f g : Nat -> Real}
  statement: ofSeq f < ofSeq g ↔ forallᶠ n in hyperfilter Nat, f n < g n
  proof: Germ.coe_lt

中文:
定理 ofSeq_lt_ofSeq
  条件: {f g : 自然数 -> 实数}
  结论: ofSeq f < ofSeq g ↔ 对任意ᶠ n in hyperfilter 自然数, f n < g n
  证明: Germ.coe_lt

Depends on / 依赖: Germ.coe_lt, coe_lt
-/
theorem ofSeq_lt_ofSeq {f g : Nat -> Real} : ofSeq f < ofSeq g ↔ forallᶠ n in hyperfilter Nat, f n < g n :=
  Germ.coe_lt

/--
theorem `ofSeq_le_ofSeq` / 定理 `ofSeq_le_ofSeq`

English:
theorem ofSeq_le_ofSeq
  given: {f g : Nat -> Real}
  statement: ofSeq f <= ofSeq g ↔ forallᶠ n in hyperfilter Nat, f n <= g n
  proof: Germ.coe_le

中文:
定理 ofSeq_le_ofSeq
  条件: {f g : 自然数 -> 实数}
  结论: ofSeq f <= ofSeq g ↔ 对任意ᶠ n in hyperfilter 自然数, f n <= g n
  证明: Germ.coe_le

Depends on / 依赖: Germ.coe_le, coe_le
-/
theorem ofSeq_le_ofSeq {f g : Nat -> Real} : ofSeq f <= ofSeq g ↔ forallᶠ n in hyperfilter Nat, f n <= g n :=
  Germ.coe_le

/-! #### ω -/

/--
Definition of `omega` / `omega` 的定义

English:
definition omega
  signature: : Real*
  body: ofSeq Nat.cast

@[inherit_doc] scoped notation "ω" => Hyperreal.omega
recommended_spelling "omega" for "ω" in [omega, «termω»]

中文:
定义 omega
  签名: : 实数*
  定义体: ofSeq Nat.cast

@[inherit_doc] scoped notation "ω" => Hyperreal.omega
recommended_spelling "omega" for "ω" in [omega, «termω»]

Depends on / 依赖: Nat.cast
-/
def omega : Real* := ofSeq Nat.cast

@[inherit_doc] scoped notation "ω" => Hyperreal.omega
recommended_spelling "omega" for "ω" in [omega, «termω»]

/--
theorem `coe_lt_omega` / 定理 `coe_lt_omega`

English:
theorem coe_lt_omega
  given: (r : Real)
  statement: r < ω
  proof: by
apply ofSeq_lt_ofSeq.2 Filter.Eventually.filter_mono Nat.hyperfilter_le_atTop _
  obtain ⟨n, hn⟩ := exists_nat_gt r
  rw [eventually_atTop]
  exact ⟨n, fun m hm => hn.trans_le (mod_cast hm)⟩

中文:
定理 coe_lt_omega
  条件: (r : 实数)
  结论: r < ω
  证明: by
apply ofSeq_lt_ofSeq.2 Filter.Eventually.filter_mono Nat.hyperfilter_le_atTop _
  obtain ⟨n, hn⟩ := exists_nat_gt r
  rw [eventually_atTop]
  exact ⟨n, fun m hm => hn.trans_le (mod_cast hm)⟩

Depends on / 依赖: Eventually, Filter, Filter.Eventually.filter_mono, Nat.hyperfilter_le_atTop, eventually_atTop, exists_nat_gt, filter_mono, hn.trans_le, hyperfilter_le_atTop, mod_cast, ofSeq_lt_ofSeq, trans_le
-/
theorem coe_lt_omega (r : Real) : r < ω := by
apply ofSeq_lt_ofSeq.2 Filter.Eventually.filter_mono Nat.hyperfilter_le_atTop _
  obtain ⟨n, hn⟩ := exists_nat_gt r
  rw [eventually_atTop]
  exact ⟨n, fun m hm => hn.trans_le (mod_cast hm)⟩

/--
theorem `omega_pos` / 定理 `omega_pos`

English:
theorem omega_pos
  statement: 0 < ω
  proof: coe_lt_omega 0

@[simp]

中文:
定理 omega_pos
  结论: 0 < ω
  证明: coe_lt_omega 0

@[simp]

Depends on / 依赖: coe_lt_omega
-/
theorem omega_pos : 0 < ω :=
  coe_lt_omega 0

@[simp]
/--
theorem `omega_ne_zero` / 定理 `omega_ne_zero`

English:
theorem omega_ne_zero
  statement: ω != 0
  proof: omega_pos.ne'

@[simp]

中文:
定理 omega_ne_zero
  结论: ω != 0
  证明: omega_pos.ne'

@[simp]

Depends on / 依赖: omega_pos, omega_pos.ne
-/
theorem omega_ne_zero : ω != 0 :=
  omega_pos.ne'

@[simp]
/--
theorem `abs_omega` / 定理 `abs_omega`

English:
theorem abs_omega
  statement: |ω| = ω
  proof: abs_of_pos omega_pos

@[simp]

中文:
定理 abs_omega
  结论: |ω| = ω
  证明: abs_of_pos omega_pos

@[simp]

Depends on / 依赖: abs_of_pos, omega_pos
-/
theorem abs_omega : |ω| = ω :=
  abs_of_pos omega_pos

@[simp]
/--
theorem `archimedeanClassMk_omega_neg` / 定理 `archimedeanClassMk_omega_neg`

English:
theorem archimedeanClassMk_omega_neg
  statement: mk ω < 0
  proof: fun n => by simpa using! coe_lt_omega n

@[simp]

中文:
定理 archimedeanClassMk_omega_neg
  结论: mk ω < 0
  证明: fun n => by simpa using! coe_lt_omega n

@[simp]

Depends on / 依赖: coe_lt_omega
-/
theorem archimedeanClassMk_omega_neg : mk ω < 0 :=
  fun n => by simpa using! coe_lt_omega n

@[simp]
/--
theorem `stdPart_omega` / 定理 `stdPart_omega`

English:
theorem stdPart_omega
  statement: stdPart ω = 0
  proof: by
  rw [stdPart_eq_zero]
  exact archimedeanClassMk_omega_neg.ne

中文:
定理 stdPart_omega
  结论: stdPart ω = 0
  证明: by
  rw [stdPart_eq_zero]
  exact archimedeanClassMk_omega_neg.ne

Depends on / 依赖: NatTrans, NatTrans.id, archimedeanClassMk_omega_neg, archimedeanClassMk_omega_neg.ne, stdPart_eq_zero
-/
theorem stdPart_omega : stdPart ω = 0 := by
  rw [stdPart_eq_zero]
  exact archimedeanClassMk_omega_neg.ne

/-! #### ε -/

/--
Definition of `epsilon` / `epsilon` 的定义

English:
definition epsilon
  signature: : Real*
  body: ofSeq fun n => n⁻¹

@[inherit_doc] scoped notation "ε" => Hyperreal.epsilon
recommended_spelling "epsilon" for "ε" in [epsilon, «termε»]

@[simp]

中文:
定义 epsilon
  签名: : 实数*
  定义体: ofSeq fun n => n⁻¹

@[inherit_doc] scoped notation "ε" => Hyperreal.epsilon
recommended_spelling "epsilon" for "ε" in [epsilon, «termε»]

@[simp]
-/
def epsilon : Real* :=
  ofSeq fun n => n⁻¹

@[inherit_doc] scoped notation "ε" => Hyperreal.epsilon
recommended_spelling "epsilon" for "ε" in [epsilon, «termε»]

@[simp]
/--
theorem `inv_omega` / 定理 `inv_omega`

English:
theorem inv_omega
  statement: ω⁻¹ = ε
  proof: rfl

@[simp]

中文:
定理 inv_omega
  结论: ω⁻¹ = ε
  证明: rfl

@[simp]
-/
theorem inv_omega : ω⁻¹ = ε :=
  rfl

@[simp]
/--
theorem `inv_epsilon` / 定理 `inv_epsilon`

English:
theorem inv_epsilon
  statement: ε⁻¹ = ω
  proof: @inv_inv _ _ ω

@[simp]

中文:
定理 inv_epsilon
  结论: ε⁻¹ = ω
  证明: @inv_inv _ _ ω

@[simp]

Depends on / 依赖: inv_inv
-/
theorem inv_epsilon : ε⁻¹ = ω :=
  @inv_inv _ _ ω

@[simp]
/--
theorem `epsilon_pos` / 定理 `epsilon_pos`

English:
theorem epsilon_pos
  statement: 0 < ε
  proof: inv_pos_of_pos omega_pos

@[simp]

中文:
定理 epsilon_pos
  结论: 0 < ε
  证明: inv_pos_of_pos omega_pos

@[simp]

Depends on / 依赖: inv_pos_of_pos, omega_pos
-/
theorem epsilon_pos : 0 < ε :=
  inv_pos_of_pos omega_pos

@[simp]
/--
theorem `epsilon_ne_zero` / 定理 `epsilon_ne_zero`

English:
theorem epsilon_ne_zero
  statement: ε != 0
  proof: epsilon_pos.ne'

@[simp]

中文:
定理 epsilon_ne_zero
  结论: ε != 0
  证明: epsilon_pos.ne'

@[simp]

Depends on / 依赖: epsilon_pos, epsilon_pos.ne
-/
theorem epsilon_ne_zero : ε != 0 :=
  epsilon_pos.ne'

@[simp]
/--
theorem `epsilon_mul_omega` / 定理 `epsilon_mul_omega`

English:
theorem epsilon_mul_omega
  statement: ε * ω = 1
  proof: @inv_mul_cancel₀ _ _ ω omega_ne_zero

@[simp]

中文:
定理 epsilon_mul_omega
  结论: ε * ω = 1
  证明: @inv_mul_cancel₀ _ _ ω omega_ne_zero

@[simp]

Depends on / 依赖: omega_ne_zero
-/
theorem epsilon_mul_omega : ε * ω = 1 :=
  @inv_mul_cancel₀ _ _ ω omega_ne_zero

@[simp]
/--
theorem `archimedeanClassMk_epsilon_pos` / 定理 `archimedeanClassMk_epsilon_pos`

English:
theorem archimedeanClassMk_epsilon_pos
  statement: 0 < mk ε
  proof: by
  simp [← inv_omega]

中文:
定理 archimedeanClassMk_epsilon_pos
  结论: 0 < mk ε
  证明: by
  simp [← inv_omega]

Depends on / 依赖: inv_omega
-/
theorem archimedeanClassMk_epsilon_pos : 0 < mk ε := by
  simp [← inv_omega]

/-!
### Some facts about `Tendsto`
-/

@[simp]
/--
theorem `tendsto_ofSeq` / 定理 `tendsto_ofSeq`

English:
theorem tendsto_ofSeq
  given: {f : Nat -> Real} {lb : Filter Real}
  proof: .rfl

中文:
定理 tendsto_ofSeq
  条件: {f : 自然数 -> 实数} {lb : Filter 实数}
  证明: .rfl
-/
theorem tendsto_ofSeq {f : Nat -> Real} {lb : Filter Real} :
    (ofSeq f).Tendsto lb ↔ Tendsto f (hyperfilter Nat) lb :=
  .rfl

/--
theorem `stdPart_map` / 定理 `stdPart_map`

English:
theorem stdPart_map
  statement: {x : Real*} {r : Real} {f : Real -> Real} (hf : ContinuousAt f r)
  proof: by
  rcases ofSeq_surjective x with ⟨g, rfl⟩
  exact hf.tendsto.comp hxr

中文:
定理 stdPart_map
  结论: {x : 实数*} {r : 实数} {f : 实数 -> 实数} (hf : ContinuousAt f r)
  证明: by
  rcases ofSeq_surjective x with ⟨g, rfl⟩
  exact hf.tendsto.comp hxr

Depends on / 依赖: hf.tendsto.comp, ofSeq_surjective, tendsto
-/
theorem stdPart_map {x : Real*} {r : Real} {f : Real -> Real} (hf : ContinuousAt f r)
    (hxr : x.Tendsto (𝓝 r)) : (x.map f).Tendsto (𝓝 (f r)) := by
  rcases ofSeq_surjective x with ⟨g, rfl⟩
  exact hf.tendsto.comp hxr

/--
theorem `stdPart_map₂` / 定理 `stdPart_map₂`

English:
theorem stdPart_map₂
  statement: {x y : Real*} {r s : Real} {f : Real -> Real -> Real}
  proof: by
  rcases ofSeq_surjective x with ⟨x, rfl⟩
  rcases ofSeq_surjective y with ⟨y, rfl⟩
  exact hf.tendsto.comp (hxr.prodMk_nhds hys)

中文:
定理 stdPart_map₂
  结论: {x y : 实数*} {r s : 实数} {f : 实数 -> 实数 -> 实数}
  证明: by
  rcases ofSeq_surjective x with ⟨x, rfl⟩
  rcases ofSeq_surjective y with ⟨y, rfl⟩
  exact hf.tendsto.comp (hxr.prodMk_nhds hys)

Depends on / 依赖: hf.tendsto.comp, hxr.prodMk_nhds, ofSeq_surjective, prodMk_nhds, tendsto
-/
theorem stdPart_map₂ {x y : Real*} {r s : Real} {f : Real -> Real -> Real}
    (hxr : x.Tendsto (𝓝 r)) (hys : y.Tendsto (𝓝 s))
    (hf : ContinuousAt (Function.uncurry f) (r, s)) : (x.map₂ f y).Tendsto (𝓝 (f r s)) := by
  rcases ofSeq_surjective x with ⟨x, rfl⟩
  rcases ofSeq_surjective y with ⟨y, rfl⟩
  exact hf.tendsto.comp (hxr.prodMk_nhds hys)

/--
theorem `tendsto_iff_forall` / 定理 `tendsto_iff_forall`

English:
theorem tendsto_iff_forall
  given: {x : Real*} {r : Real}
  proof: by
  rcases ofSeq_surjective x with ⟨f, rfl⟩
  rw [tendsto_ofSeq]; rw [(nhds_basis_Ioo _).tendsto_right_iff]
  simp_rw [Set.mem_Ioo, eventually_and, ← ofSeq_lt_ofSeq]
  refine ⟨fun H => ⟨fun s hs => ?_, fun s hs => ?_⟩, fun H ⟨s, t⟩ ⟨hs, ht⟩ => ⟨?_, ?_⟩⟩
  · obtain ⟨t, ht⟩ := exists_gt r
    exact (

中文:
定理 tendsto_iff_forall
  条件: {x : 实数*} {r : 实数}
  证明: by
  rcases ofSeq_surjective x with ⟨f, rfl⟩
  rw [tendsto_ofSeq]; rw [(nhds_basis_Ioo _).tendsto_right_iff]
  simp_rw [Set.mem_Ioo, eventually_and, ← ofSeq_lt_ofSeq]
  refine ⟨fun H => ⟨fun s hs => ?_, fun s hs => ?_⟩, fun H ⟨s, t⟩ ⟨hs, ht⟩ => ⟨?_, ?_⟩⟩
  · obtain ⟨t, ht⟩ := exists_gt r
    exact (

Depends on / 依赖: Set.mem_Ioo, coe_lt_coe, eventually_and, exists_between, exists_gt, exists_lt, mem_Ioo, nhds_basis_Ioo, ofSeq_lt_ofSeq, ofSeq_surjective, simp_rw, tendsto_ofSeq, tendsto_right_iff, trans_le
-/
theorem tendsto_iff_forall {x : Real*} {r : Real} :
    x.Tendsto (𝓝 r) ↔ (forall s < r, s <= x) ∧ (forall s > r, x <= s) := by
  rcases ofSeq_surjective x with ⟨f, rfl⟩
  rw [tendsto_ofSeq]; rw [(nhds_basis_Ioo _).tendsto_right_iff]
  simp_rw [Set.mem_Ioo, eventually_and, ← ofSeq_lt_ofSeq]
  refine ⟨fun H => ⟨fun s hs => ?_, fun s hs => ?_⟩, fun H ⟨s, t⟩ ⟨hs, ht⟩ => ⟨?_, ?_⟩⟩
  · obtain ⟨t, ht⟩ := exists_gt r
    exact (H ⟨s, t⟩ ⟨hs, ht⟩).1.le
  · obtain ⟨t, ht⟩ := exists_lt r
    exact (H ⟨t, s⟩ ⟨ht, hs⟩).2.le
  · obtain ⟨u, hu, hu'⟩ := exists_between hs
    exact (coe_lt_coe.2 hu).trans_le (H.1 _ hu')
  · obtain ⟨u, hu, hu'⟩ := exists_between ht
    exact (H.2 _ hu).trans_lt (coe_lt_coe.2 hu')

/--
theorem `archimedeanClassMk_nonneg_of_tendsto` / 定理 `archimedeanClassMk_nonneg_of_tendsto`

English:
theorem archimedeanClassMk_nonneg_of_tendsto
  given: {x : Real*} {r : Real} (hx : x.Tendsto (𝓝 r))
  proof: by
  rw [tendsto_iff_forall] at hx
  obtain ⟨s, hs⟩ := exists_lt r
  obtain ⟨t, ht⟩ := exists_gt r
  exact mk_nonneg_of_le_of_le_of_archimedean coeRingHom (hx.1 s hs) (hx.2 t ht)

中文:
定理 archimedeanClassMk_nonneg_of_tendsto
  条件: {x : 实数*} {r : 实数} (hx : x.Tendsto (𝓝 r))
  证明: by
  rw [tendsto_iff_forall] at hx
  obtain ⟨s, hs⟩ := exists_lt r
  obtain ⟨t, ht⟩ := exists_gt r
  exact mk_nonneg_of_le_of_le_of_archimedean coeRingHom (hx.1 s hs) (hx.2 t ht)

Depends on / 依赖: coeRingHom, exists_gt, exists_lt, mk_nonneg_of_le_of_le_of_archimedean, tendsto_iff_forall
-/
theorem archimedeanClassMk_nonneg_of_tendsto {x : Real*} {r : Real} (hx : x.Tendsto (𝓝 r)) :
    0 <= mk x := by
  rw [tendsto_iff_forall] at hx
  obtain ⟨s, hs⟩ := exists_lt r
  obtain ⟨t, ht⟩ := exists_gt r
  exact mk_nonneg_of_le_of_le_of_archimedean coeRingHom (hx.1 s hs) (hx.2 t ht)

/--
theorem `stdPart_of_tendsto` / 定理 `stdPart_of_tendsto`

English:
theorem stdPart_of_tendsto
  given: {x : Real*} {r : Real} (hx : x.Tendsto (𝓝 r))
  statement: stdPart x = r
  proof: by
  rw [tendsto_iff_forall] at hx
  exact stdPart_eq coeRingHom hx.1 hx.2

中文:
定理 stdPart_of_tendsto
  条件: {x : 实数*} {r : 实数} (hx : x.Tendsto (𝓝 r))
  结论: stdPart x = r
  证明: by
  rw [tendsto_iff_forall] at hx
  exact stdPart_eq coeRingHom hx.1 hx.2

Depends on / 依赖: coeRingHom, stdPart_eq, tendsto_iff_forall
-/
theorem stdPart_of_tendsto {x : Real*} {r : Real} (hx : x.Tendsto (𝓝 r)) : stdPart x = r := by
  rw [tendsto_iff_forall] at hx
  exact stdPart_eq coeRingHom hx.1 hx.2

/--
theorem `archimedeanClassMk_pos_of_tendsto` / 定理 `archimedeanClassMk_pos_of_tendsto`

English:
theorem archimedeanClassMk_pos_of_tendsto
  given: {x : Real*} (hx : x.Tendsto (𝓝 0))
  statement: 0 < mk x
  proof: by
  apply (archimedeanClassMk_nonneg_of_tendsto hx).lt_of_ne'
  rw [← stdPart_eq_zero]; rw [stdPart_of_tendsto hx]

@[simp]

中文:
定理 archimedeanClassMk_pos_of_tendsto
  条件: {x : 实数*} (hx : x.Tendsto (𝓝 0))
  结论: 0 < mk x
  证明: by
  apply (archimedeanClassMk_nonneg_of_tendsto hx).lt_of_ne'
  rw [← stdPart_eq_zero]; rw [stdPart_of_tendsto hx]

@[simp]

Depends on / 依赖: archimedeanClassMk_nonneg_of_tendsto, lt_of_ne, stdPart_eq_zero, stdPart_of_tendsto
-/
theorem archimedeanClassMk_pos_of_tendsto {x : Real*} (hx : x.Tendsto (𝓝 0)) : 0 < mk x := by
  apply (archimedeanClassMk_nonneg_of_tendsto hx).lt_of_ne'
  rw [← stdPart_eq_zero]; rw [stdPart_of_tendsto hx]

@[simp]
/--
theorem `stdPart_epsilon` / 定理 `stdPart_epsilon`

English:
theorem stdPart_epsilon
  statement: stdPart ε = 0
  proof: stdPart_eq_zero.2 archimedeanClassMk_epsilon_pos.ne'

中文:
定理 stdPart_epsilon
  结论: stdPart ε = 0
  证明: stdPart_eq_zero.2 archimedeanClassMk_epsilon_pos.ne'

Depends on / 依赖: archimedeanClassMk_epsilon_pos, archimedeanClassMk_epsilon_pos.ne, stdPart_eq_zero
-/
theorem stdPart_epsilon : stdPart ε = 0 :=
stdPart_eq_zero.2 archimedeanClassMk_epsilon_pos.ne'

/--
theorem `epsilon_lt_of_pos` / 定理 `epsilon_lt_of_pos`

English:
theorem epsilon_lt_of_pos
  given: {r : Real}
  statement: 0 < r -> ε < r
  proof: lt_of_pos_of_archimedean coeRingHom archimedeanClassMk_epsilon_pos

中文:
定理 epsilon_lt_of_pos
  条件: {r : 实数}
  结论: 0 < r -> ε < r
  证明: lt_of_pos_of_archimedean coeRingHom archimedeanClassMk_epsilon_pos

Depends on / 依赖: archimedeanClassMk_epsilon_pos, coeRingHom, lt_of_pos_of_archimedean
-/
theorem epsilon_lt_of_pos {r : Real} : 0 < r -> ε < r :=
  lt_of_pos_of_archimedean coeRingHom archimedeanClassMk_epsilon_pos

/--
theorem `epsilon_lt_of_neg` / 定理 `epsilon_lt_of_neg`

English:
theorem epsilon_lt_of_neg
  given: {r : Real}
  statement: r < 0 -> r < ε
  proof: lt_of_neg_of_archimedean coeRingHom archimedeanClassMk_epsilon_pos

@[deprecated (since := "2026-01-05")]
alias epsilon_lt_pos := epsilon_lt_of_pos

@[deprecated archimedeanClassMk_pos_of_tendsto (since := "2026-01-05")]

中文:
定理 epsilon_lt_of_neg
  条件: {r : 实数}
  结论: r < 0 -> r < ε
  证明: lt_of_neg_of_archimedean coeRingHom archimedeanClassMk_epsilon_pos

@[deprecated (since := "2026-01-05")]
alias epsilon_lt_pos := epsilon_lt_of_pos

@[deprecated archimedeanClassMk_pos_of_tendsto (since := "2026-01-05")]

Depends on / 依赖: archimedeanClassMk_epsilon_pos, coeRingHom, lt_of_neg_of_archimedean
-/
theorem epsilon_lt_of_neg {r : Real} : r < 0 -> r < ε :=
  lt_of_neg_of_archimedean coeRingHom archimedeanClassMk_epsilon_pos

@[deprecated (since := "2026-01-05")]
alias epsilon_lt_pos := epsilon_lt_of_pos

@[deprecated archimedeanClassMk_pos_of_tendsto (since := "2026-01-05")]
/--
theorem `lt_of_tendsto_zero_of_pos` / 定理 `lt_of_tendsto_zero_of_pos`

English:
theorem lt_of_tendsto_zero_of_pos
  given: {f : Nat -> Real} (hf : Tendsto f atTop (𝓝 0))
  proof: fun hr =>
ofSeq_lt_ofSeq.2 (hf.eventually <| gt_mem_nhds hr).filter_mono Nat.hyperfilter_le_atTop

@[deprecated archimedeanClassMk_pos_of_tendsto (since := "2026-01-05")]

中文:
定理 lt_of_tendsto_zero_of_pos
  条件: {f : 自然数 -> 实数} (hf : Tendsto f atTop (𝓝 0))
  证明: fun hr =>
ofSeq_lt_ofSeq.2 (hf.eventually <| gt_mem_nhds hr).filter_mono Nat.hyperfilter_le_atTop

@[deprecated archimedeanClassMk_pos_of_tendsto (since := "2026-01-05")]
-/
theorem lt_of_tendsto_zero_of_pos {f : Nat -> Real} (hf : Tendsto f atTop (𝓝 0)) :
    forall {r : Real}, 0 < r -> ofSeq f < (r : Real*) := fun hr =>
ofSeq_lt_ofSeq.2 (hf.eventually <| gt_mem_nhds hr).filter_mono Nat.hyperfilter_le_atTop

@[deprecated archimedeanClassMk_pos_of_tendsto (since := "2026-01-05")]
/--
theorem `neg_lt_of_tendsto_zero_of_pos` / 定理 `neg_lt_of_tendsto_zero_of_pos`

English:
theorem neg_lt_of_tendsto_zero_of_pos
  given: {f : Nat -> Real} (hf : Tendsto f atTop (𝓝 0))
  proof: fun hr =>
  have hg := hf.neg
  neg_lt_of_neg_lt (by rw [neg_zero] at hg; exact lt_of_tendsto_zero_of_pos hg hr)

@[deprecated archimedeanClassMk_pos_of_tendsto (since := "2026-01-05")]

中文:
定理 neg_lt_of_tendsto_zero_of_pos
  条件: {f : 自然数 -> 实数} (hf : Tendsto f atTop (𝓝 0))
  证明: fun hr =>
  have hg := hf.neg
  neg_lt_of_neg_lt (by rw [neg_zero] at hg; exact lt_of_tendsto_zero_of_pos hg hr)

@[deprecated archimedeanClassMk_pos_of_tendsto (since := "2026-01-05")]
-/
theorem neg_lt_of_tendsto_zero_of_pos {f : Nat -> Real} (hf : Tendsto f atTop (𝓝 0)) :
    forall {r : Real}, 0 < r -> (-r : Real*) < ofSeq f := fun hr =>
  have hg := hf.neg
  neg_lt_of_neg_lt (by rw [neg_zero] at hg; exact lt_of_tendsto_zero_of_pos hg hr)

@[deprecated archimedeanClassMk_pos_of_tendsto (since := "2026-01-05")]
/--
theorem `gt_of_tendsto_zero_of_neg` / 定理 `gt_of_tendsto_zero_of_neg`

English:
theorem gt_of_tendsto_zero_of_neg
  given: {f : Nat -> Real} (hf : Tendsto f atTop (𝓝 0))
  proof: fun {r} hr => by
  rw [← neg_neg r]; rw [coe_neg]; exact neg_lt_of_tendsto_zero_of_pos hf (neg_pos.mpr hr)

中文:
定理 gt_of_tendsto_zero_of_neg
  条件: {f : 自然数 -> 实数} (hf : Tendsto f atTop (𝓝 0))
  证明: fun {r} hr => by
  rw [← neg_neg r]; rw [coe_neg]; exact neg_lt_of_tendsto_zero_of_pos hf (neg_pos.mpr hr)

Depends on / 依赖: coe_neg, neg_lt_of_tendsto_zero_of_pos, neg_neg, neg_pos, neg_pos.mpr
-/
theorem gt_of_tendsto_zero_of_neg {f : Nat -> Real} (hf : Tendsto f atTop (𝓝 0)) :
    forall {r : Real}, r < 0 -> (r : Real*) < ofSeq f := fun {r} hr => by
  rw [← neg_neg r]; rw [coe_neg]; exact neg_lt_of_tendsto_zero_of_pos hf (neg_pos.mpr hr)

/--
theorem `lt_of_tendsto_atTop` / 定理 `lt_of_tendsto_atTop`

English:
theorem lt_of_tendsto_atTop
  given: {x : Real*} (r : Real) (hx : x.Tendsto atTop)
  statement: r < x
  proof: by
  rcases ofSeq_surjective x with ⟨f, rfl⟩
  rw [tendsto_ofSeq] at hx
exact ofSeq_lt_ofSeq.2 hx.eventually_mem (Ioi_mem_atTop r)

中文:
定理 lt_of_tendsto_atTop
  条件: {x : 实数*} (r : 实数) (hx : x.Tendsto atTop)
  结论: r < x
  证明: by
  rcases ofSeq_surjective x with ⟨f, rfl⟩
  rw [tendsto_ofSeq] at hx
exact ofSeq_lt_ofSeq.2 hx.eventually_mem (Ioi_mem_atTop r)

Depends on / 依赖: Ioi_mem_atTop, eventually_mem, hx.eventually_mem, ofSeq_lt_ofSeq, ofSeq_surjective, tendsto_ofSeq
-/
theorem lt_of_tendsto_atTop {x : Real*} (r : Real) (hx : x.Tendsto atTop) : r < x := by
  rcases ofSeq_surjective x with ⟨f, rfl⟩
  rw [tendsto_ofSeq] at hx
exact ofSeq_lt_ofSeq.2 hx.eventually_mem (Ioi_mem_atTop r)

/--
theorem `lt_of_tendsto_atBot` / 定理 `lt_of_tendsto_atBot`

English:
theorem lt_of_tendsto_atBot
  given: {x : Real*} (r : Real) (hx : x.Tendsto atBot)
  statement: x < r
  proof: by
  rcases ofSeq_surjective x with ⟨f, rfl⟩
  rw [tendsto_ofSeq] at hx
exact ofSeq_lt_ofSeq.2 hx.eventually_mem (Iio_mem_atBot r)

中文:
定理 lt_of_tendsto_atBot
  条件: {x : 实数*} (r : 实数) (hx : x.Tendsto atBot)
  结论: x < r
  证明: by
  rcases ofSeq_surjective x with ⟨f, rfl⟩
  rw [tendsto_ofSeq] at hx
exact ofSeq_lt_ofSeq.2 hx.eventually_mem (Iio_mem_atBot r)

Depends on / 依赖: Iio_mem_atBot, eventually_mem, hx.eventually_mem, ofSeq_lt_ofSeq, ofSeq_surjective, tendsto_ofSeq
-/
theorem lt_of_tendsto_atBot {x : Real*} (r : Real) (hx : x.Tendsto atBot) : x < r := by
  rcases ofSeq_surjective x with ⟨f, rfl⟩
  rw [tendsto_ofSeq] at hx
exact ofSeq_lt_ofSeq.2 hx.eventually_mem (Iio_mem_atBot r)

/--
theorem `archimedeanClassMk_neg_of_tendsto_atTop` / 定理 `archimedeanClassMk_neg_of_tendsto_atTop`

English:
theorem archimedeanClassMk_neg_of_tendsto_atTop
  given: {x : Real*} (hx : x.Tendsto atTop)
  statement: mk x < 0
  proof: by
  have : 0 < x := lt_of_tendsto_atTop 0 hx
  intro n
  simpa [abs_of_pos this] using! lt_of_tendsto_atTop n hx

中文:
定理 archimedeanClassMk_neg_of_tendsto_atTop
  条件: {x : 实数*} (hx : x.Tendsto atTop)
  结论: mk x < 0
  证明: by
  have : 0 < x := lt_of_tendsto_atTop 0 hx
  intro n
  simpa [abs_of_pos this] using! lt_of_tendsto_atTop n hx

Depends on / 依赖: abs_of_pos, lt_of_tendsto_atTop
-/
theorem archimedeanClassMk_neg_of_tendsto_atTop {x : Real*} (hx : x.Tendsto atTop) : mk x < 0 := by
  have : 0 < x := lt_of_tendsto_atTop 0 hx
  intro n
  simpa [abs_of_pos this] using! lt_of_tendsto_atTop n hx

/--
theorem `archimedeanClassMk_neg_of_tendsto_atBot` / 定理 `archimedeanClassMk_neg_of_tendsto_atBot`

English:
theorem archimedeanClassMk_neg_of_tendsto_atBot
  given: {x : Real*} (hx : x.Tendsto atBot)
  statement: mk x < 0
  proof: by
  have : x < 0 := lt_of_tendsto_atBot 0 hx
  intro n
  simpa [abs_of_neg this, lt_neg] using! lt_of_tendsto_atBot (-n) hx

中文:
定理 archimedeanClassMk_neg_of_tendsto_atBot
  条件: {x : 实数*} (hx : x.Tendsto atBot)
  结论: mk x < 0
  证明: by
  have : x < 0 := lt_of_tendsto_atBot 0 hx
  intro n
  simpa [abs_of_neg this, lt_neg] using! lt_of_tendsto_atBot (-n) hx

Depends on / 依赖: abs_of_neg, lt_neg, lt_of_tendsto_atBot
-/
theorem archimedeanClassMk_neg_of_tendsto_atBot {x : Real*} (hx : x.Tendsto atBot) : mk x < 0 := by
  have : x < 0 := lt_of_tendsto_atBot 0 hx
  intro n
  simpa [abs_of_neg this, lt_neg] using! lt_of_tendsto_atBot (-n) hx

/--
theorem `tendsto_atTop_iff` / 定理 `tendsto_atTop_iff`

English:
theorem tendsto_atTop_iff
  given: {x : Real*}
  statement: x.Tendsto atTop ↔ 0 < x ∧ mk x < 0 where
  proof: ⟨lt_of_tendsto_atTop 0 h, archimedeanClassMk_neg_of_tendsto_atTop h⟩
  mpr h := by
    rcases ofSeq_surjective x with ⟨f, rfl⟩
    rw [tendsto_ofSeq]; rw [tendsto_atTop]
exact fun r => ofSeq_le_ofSeq.1
      (lt_of_mk_lt_mk_of_nonneg (h.2.trans_le <| archimedeanClassMk_coe_nonneg r) h.1.le).le

中文:
定理 tendsto_atTop_iff
  条件: {x : 实数*}
  结论: x.Tendsto atTop ↔ 0 < x ∧ mk x < 0 where
  证明: ⟨lt_of_tendsto_atTop 0 h, archimedeanClassMk_neg_of_tendsto_atTop h⟩
  mpr h := by
    rcases ofSeq_surjective x with ⟨f, rfl⟩
    rw [tendsto_ofSeq]; rw [tendsto_atTop]
exact fun r => ofSeq_le_ofSeq.1
      (lt_of_mk_lt_mk_of_nonneg (h.2.trans_le <| archimedeanClassMk_coe_nonneg r) h.1.le).le

Depends on / 依赖: archimedeanClassMk_neg_of_tendsto_atTop, lt_of_tendsto_atTop
-/
theorem tendsto_atTop_iff {x : Real*} : x.Tendsto atTop ↔ 0 < x ∧ mk x < 0 where
  mp h := ⟨lt_of_tendsto_atTop 0 h, archimedeanClassMk_neg_of_tendsto_atTop h⟩
  mpr h := by
    rcases ofSeq_surjective x with ⟨f, rfl⟩
    rw [tendsto_ofSeq]; rw [tendsto_atTop]
exact fun r => ofSeq_le_ofSeq.1
      (lt_of_mk_lt_mk_of_nonneg (h.2.trans_le <| archimedeanClassMk_coe_nonneg r) h.1.le).le

/--
theorem `tendsto_atBot_iff` / 定理 `tendsto_atBot_iff`

English:
theorem tendsto_atBot_iff
  given: {x : Real*}
  statement: x.Tendsto atBot ↔ x < 0 ∧ mk x < 0 where
  proof: ⟨lt_of_tendsto_atBot 0 h, archimedeanClassMk_neg_of_tendsto_atBot h⟩
  mpr h := by
    rcases ofSeq_surjective x with ⟨f, rfl⟩
    rw [tendsto_ofSeq]; rw [tendsto_atBot]
exact fun r => ofSeq_le_ofSeq.1
      (lt_of_mk_lt_mk_of_nonpos (h.2.trans_le <| archimedeanClassMk_coe_nonneg r) h.1.le).le

中文:
定理 tendsto_atBot_iff
  条件: {x : 实数*}
  结论: x.Tendsto atBot ↔ x < 0 ∧ mk x < 0 where
  证明: ⟨lt_of_tendsto_atBot 0 h, archimedeanClassMk_neg_of_tendsto_atBot h⟩
  mpr h := by
    rcases ofSeq_surjective x with ⟨f, rfl⟩
    rw [tendsto_ofSeq]; rw [tendsto_atBot]
exact fun r => ofSeq_le_ofSeq.1
      (lt_of_mk_lt_mk_of_nonpos (h.2.trans_le <| archimedeanClassMk_coe_nonneg r) h.1.le).le

Depends on / 依赖: archimedeanClassMk_neg_of_tendsto_atBot, lt_of_tendsto_atBot
-/
theorem tendsto_atBot_iff {x : Real*} : x.Tendsto atBot ↔ x < 0 ∧ mk x < 0 where
  mp h := ⟨lt_of_tendsto_atBot 0 h, archimedeanClassMk_neg_of_tendsto_atBot h⟩
  mpr h := by
    rcases ofSeq_surjective x with ⟨f, rfl⟩
    rw [tendsto_ofSeq]; rw [tendsto_atBot]
exact fun r => ofSeq_le_ofSeq.1
      (lt_of_mk_lt_mk_of_nonpos (h.2.trans_le <| archimedeanClassMk_coe_nonneg r) h.1.le).le

/-- Standard part predicate.
**Do not use.** This is equivalent to the conjunction of `0 ≤ ArchimedeanClass.mk x` and
`ArchimedeanClass.stdPart x = r`. -/
@[deprecated stdPart (since := "2026-01-05")]
/--
Definition of `IsSt` / `IsSt` 的定义

English:
definition IsSt
  signature: (x : Real*) (r : Real)
  body: forall δ : Real, 0 < δ -> (r - δ : Real*) < x ∧ x < r + δ

@[deprecated "`IsSt` is deprecated" (since := "2026-01-05")]

中文:
定义 IsSt
  签名: (x : 实数*) (r : 实数)
  定义体: forall δ : Real, 0 < δ -> (r - δ : Real*) < x ∧ x < r + δ

@[deprecated "`IsSt` is deprecated" (since := "2026-01-05")]
-/
def IsSt (x : Real*) (r : Real) :=
  forall δ : Real, 0 < δ -> (r - δ : Real*) < x ∧ x < r + δ

@[deprecated "`IsSt` is deprecated" (since := "2026-01-05")]
/--
theorem `isSt_iff` / 定理 `isSt_iff`

English:
theorem isSt_iff
  given: {x r}
  statement: IsSt x r ↔ 0 <= mk x ∧ stdPart x = r where
  proof: by
    refine ⟨?_, stdPart_eq coeRingHom (fun s hs => ?_) (fun s hs => ?_)⟩
    · have h := h 1 zero_lt_one
      exact mk_nonneg_of_le_of_le_of_archimedean coeRingHom h.1.le h.2.le
    · simpa using (h _ (sub_pos_of_lt hs)).1.le
    · simpa using (h _ (sub_pos_of_lt hs)).2.le
  mpr h := by
    obta

中文:
定理 isSt_iff
  条件: {x r}
  结论: IsSt x r ↔ 0 <= mk x ∧ stdPart x = r where
  证明: by
    refine ⟨?_, stdPart_eq coeRingHom (fun s hs => ?_) (fun s hs => ?_)⟩
    · have h := h 1 zero_lt_one
      exact mk_nonneg_of_le_of_le_of_archimedean coeRingHom h.1.le h.2.le
    · simpa using (h _ (sub_pos_of_lt hs)).1.le
    · simpa using (h _ (sub_pos_of_lt hs)).2.le
  mpr h := by
    obta

Depends on / 依赖: coeRingHom, lt_of_lt_stdPart, lt_of_stdPart_lt, mk_nonneg_of_le_of_le_of_archimedean, stdPart_eq, sub_pos_of_lt, zero_lt_one
-/
theorem isSt_iff {x r} : IsSt x r ↔ 0 <= mk x ∧ stdPart x = r where
  mp h := by
    refine ⟨?_, stdPart_eq coeRingHom (fun s hs => ?_) (fun s hs => ?_)⟩
    · have h := h 1 zero_lt_one
      exact mk_nonneg_of_le_of_le_of_archimedean coeRingHom h.1.le h.2.le
    · simpa using (h _ (sub_pos_of_lt hs)).1.le
    · simpa using (h _ (sub_pos_of_lt hs)).2.le
  mpr h := by
    obtain ⟨h, rfl⟩ := h
    refine fun y hy => ⟨?_, ?_⟩
    · apply lt_of_lt_stdPart coeRingHom h; simpa
    · apply lt_of_stdPart_lt coeRingHom h; simpa

open scoped Classical in
/-- Standard part function: like a "round" to ℝ instead of ℤ -/
@[deprecated stdPart (since := "2026-01-05")]
/--
Definition of `st` / `st` 的定义

English:
definition st
  signature: : Real* -> Real
  body: fun x => if h : exists r, IsSt x r then Classical.choose h else 0

@[deprecated "`st` is deprecated" (since := "2026-01-05")]

中文:
定义 st
  签名: : 实数* -> 实数
  定义体: fun x => if h : exists r, IsSt x r then Classical.choose h else 0

@[deprecated "`st` is deprecated" (since := "2026-01-05")]

Depends on / 依赖: Classical, Classical.choose
-/
noncomputable def st : Real* -> Real := fun x => if h : exists r, IsSt x r then Classical.choose h else 0

@[deprecated "`st` is deprecated" (since := "2026-01-05")]
/--
theorem `st_eq` / 定理 `st_eq`

English:
theorem st_eq
  given: (x : Real*)
  statement: st x = stdPart x
  proof: by
  rw [st]
  split_ifs with h
  · exact (isSt_iff.1 (Classical.choose_spec h)).2.symm
  · simp_rw [isSt_iff] at h
    push Not at h
    rw [eq_comm]; rw [stdPart_eq_zero]
    apply ne_of_lt
    by_contra! hx
    exact h _ hx rfl

中文:
定理 st_eq
  条件: (x : 实数*)
  结论: st x = stdPart x
  证明: by
  rw [st]
  split_ifs with h
  · exact (isSt_iff.1 (Classical.choose_spec h)).2.symm
  · simp_rw [isSt_iff] at h
    push Not at h
    rw [eq_comm]; rw [stdPart_eq_zero]
    apply ne_of_lt
    by_contra! hx
    exact h _ hx rfl

Depends on / 依赖: Classical, Classical.choose_spec, choose_spec, eq_comm, isSt_iff, ne_of_lt, simp_rw, split_ifs, stdPart_eq_zero
-/
theorem st_eq (x : Real*) : st x = stdPart x := by
  rw [st]
  split_ifs with h
  · exact (isSt_iff.1 (Classical.choose_spec h)).2.symm
  · simp_rw [isSt_iff] at h
    push Not at h
    rw [eq_comm]; rw [stdPart_eq_zero]
    apply ne_of_lt
    by_contra! hx
    exact h _ hx rfl

/-- A hyperreal number is infinitesimal if its standard part is 0.
**Do not use.** Write `0 < ArchimedeanClass.mk x` instead. -/
@[deprecated ArchimedeanClass.mk (since := "2026-01-05")]
/--
Definition of `Infinitesimal` / `Infinitesimal` 的定义

English:
definition Infinitesimal
  signature: (x : Real*)
  body: IsSt x 0

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]

中文:
定义 Infinitesimal
  签名: (x : 实数*)
  定义体: IsSt x 0

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
-/
def Infinitesimal (x : Real*) :=
  IsSt x 0

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
/--
theorem `infinitesimal_iff` / 定理 `infinitesimal_iff`

English:
theorem infinitesimal_iff
  given: {x : Real*}
  statement: Infinitesimal x ↔ 0 < mk x
  proof: by
  rw [Infinitesimal]; rw [isSt_iff]; rw [stdPart_eq_zero]; rw [lt_iff_le_and_ne']

中文:
定理 infinitesimal_iff
  条件: {x : 实数*}
  结论: Infinitesimal x ↔ 0 < mk x
  证明: by
  rw [Infinitesimal]; rw [isSt_iff]; rw [stdPart_eq_zero]; rw [lt_iff_le_and_ne']

Depends on / 依赖: Infinitesimal, isSt_iff, lt_iff_le_and_ne, stdPart_eq_zero
-/
theorem infinitesimal_iff {x : Real*} : Infinitesimal x ↔ 0 < mk x := by
  rw [Infinitesimal]; rw [isSt_iff]; rw [stdPart_eq_zero]; rw [lt_iff_le_and_ne']

/-- A hyperreal number is positive infinite if it is larger than all real numbers.
**Do not use.** Write `0 < x ∧ ArchimedeanClass.mk x < 0` instead. -/
@[deprecated ArchimedeanClass.mk (since := "2026-01-05")]
/--
Definition of `InfinitePos` / `InfinitePos` 的定义

English:
definition InfinitePos
  signature: (x : Real*)
  body: forall r : Real, ↑r < x

@[deprecated "`InfinitePos` is deprecated" (since := "2026-01-05")]

中文:
定义 InfinitePos
  签名: (x : 实数*)
  定义体: forall r : Real, ↑r < x

@[deprecated "`InfinitePos` is deprecated" (since := "2026-01-05")]
-/
def InfinitePos (x : Real*) :=
  forall r : Real, ↑r < x

@[deprecated "`InfinitePos` is deprecated" (since := "2026-01-05")]
/--
theorem `infinitePos_iff` / 定理 `infinitePos_iff`

English:
theorem infinitePos_iff
  given: {x : Real*}
  statement: InfinitePos x ↔ 0 < x ∧ mk x < 0
  proof: by
  refine ⟨fun h => ?_, fun ⟨hx, hx'⟩ r => ?_⟩
  · have hx : 0 < x := h 0
    refine ⟨h 0, fun n => ?_⟩
    simpa [abs_of_pos hx] using! h n
  · exact lt_of_mk_lt_mk_of_nonneg (hx'.trans_le <| mk_map_nonneg_of_archimedean coeRingHom _) hx.le

中文:
定理 infinitePos_iff
  条件: {x : 实数*}
  结论: InfinitePos x ↔ 0 < x ∧ mk x < 0
  证明: by
  refine ⟨fun h => ?_, fun ⟨hx, hx'⟩ r => ?_⟩
  · have hx : 0 < x := h 0
    refine ⟨h 0, fun n => ?_⟩
    simpa [abs_of_pos hx] using! h n
  · exact lt_of_mk_lt_mk_of_nonneg (hx'.trans_le <| mk_map_nonneg_of_archimedean coeRingHom _) hx.le

Depends on / 依赖: abs_of_pos, coeRingHom, hx.le, lt_of_mk_lt_mk_of_nonneg, mk_map_nonneg_of_archimedean, trans_le
-/
theorem infinitePos_iff {x : Real*} : InfinitePos x ↔ 0 < x ∧ mk x < 0 := by
  refine ⟨fun h => ?_, fun ⟨hx, hx'⟩ r => ?_⟩
  · have hx : 0 < x := h 0
    refine ⟨h 0, fun n => ?_⟩
    simpa [abs_of_pos hx] using! h n
  · exact lt_of_mk_lt_mk_of_nonneg (hx'.trans_le <| mk_map_nonneg_of_archimedean coeRingHom _) hx.le

/-- A hyperreal number is negative infinite if it is smaller than all real numbers.
**Do not use.** Write `x < 0 ∧ ArchimedeanClass.mk x < 0` instead. -/
@[deprecated ArchimedeanClass.mk (since := "2026-01-05")]
/--
Definition of `InfiniteNeg` / `InfiniteNeg` 的定义

English:
definition InfiniteNeg
  signature: (x : Real*)
  body: forall r : Real, x < r

@[deprecated "`InfiniteNeg` is deprecated" (since := "2026-01-05")]

中文:
定义 InfiniteNeg
  签名: (x : 实数*)
  定义体: forall r : Real, x < r

@[deprecated "`InfiniteNeg` is deprecated" (since := "2026-01-05")]
-/
def InfiniteNeg (x : Real*) :=
  forall r : Real, x < r

@[deprecated "`InfiniteNeg` is deprecated" (since := "2026-01-05")]
/--
theorem `infiniteNeg_iff` / 定理 `infiniteNeg_iff`

English:
theorem infiniteNeg_iff
  given: {x : Real*}
  statement: InfiniteNeg x ↔ x < 0 ∧ mk x < 0
  proof: by
  refine ⟨fun h => ?_, fun ⟨hx, hx'⟩ r => ?_⟩
  · have hx : x < 0 := h 0
    refine ⟨h 0, fun n => ?_⟩
    simpa [abs_of_neg hx, lt_neg] using! h (-n)
  · exact lt_of_mk_lt_mk_of_nonpos (hx'.trans_le <| mk_map_nonneg_of_archimedean coeRingHom _) hx.le

中文:
定理 infiniteNeg_iff
  条件: {x : 实数*}
  结论: InfiniteNeg x ↔ x < 0 ∧ mk x < 0
  证明: by
  refine ⟨fun h => ?_, fun ⟨hx, hx'⟩ r => ?_⟩
  · have hx : x < 0 := h 0
    refine ⟨h 0, fun n => ?_⟩
    simpa [abs_of_neg hx, lt_neg] using! h (-n)
  · exact lt_of_mk_lt_mk_of_nonpos (hx'.trans_le <| mk_map_nonneg_of_archimedean coeRingHom _) hx.le

Depends on / 依赖: abs_of_neg, coeRingHom, hx.le, lt_neg, lt_of_mk_lt_mk_of_nonpos, mk_map_nonneg_of_archimedean, trans_le
-/
theorem infiniteNeg_iff {x : Real*} : InfiniteNeg x ↔ x < 0 ∧ mk x < 0 := by
  refine ⟨fun h => ?_, fun ⟨hx, hx'⟩ r => ?_⟩
  · have hx : x < 0 := h 0
    refine ⟨h 0, fun n => ?_⟩
    simpa [abs_of_neg hx, lt_neg] using! h (-n)
  · exact lt_of_mk_lt_mk_of_nonpos (hx'.trans_le <| mk_map_nonneg_of_archimedean coeRingHom _) hx.le

/-- A hyperreal number is infinite if it is infinite positive or infinite negative.
**Do not use.** Write `ArchimedeanClass.mk x < 0` instead. -/
@[deprecated ArchimedeanClass.mk (since := "2026-01-05")]
/--
Definition of `Infinite` / `Infinite` 的定义

English:
definition Infinite
  signature: (x : Real*)
  body: InfinitePos x ∨ InfiniteNeg x

@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]

中文:
定义 Infinite
  签名: (x : 实数*)
  定义体: InfinitePos x ∨ InfiniteNeg x

@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]

Depends on / 依赖: InfiniteNeg, InfinitePos
-/
def Infinite (x : Real*) :=
  InfinitePos x ∨ InfiniteNeg x

@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]
/--
theorem `infinite_iff` / 定理 `infinite_iff`

English:
theorem infinite_iff
  given: {x : Real*}
  statement: Infinite x ↔ mk x < 0
  proof: by
  rw [Infinite]; rw [infinitePos_iff]; rw [infiniteNeg_iff]
  aesop

@[deprecated tendsto_iff_forall (since := "2026-01-05")]

中文:
定理 infinite_iff
  条件: {x : 实数*}
  结论: Infinite x ↔ mk x < 0
  证明: by
  rw [Infinite]; rw [infinitePos_iff]; rw [infiniteNeg_iff]
  aesop

@[deprecated tendsto_iff_forall (since := "2026-01-05")]

Depends on / 依赖: Infinite, infiniteNeg_iff, infinitePos_iff
-/
theorem infinite_iff {x : Real*} : Infinite x ↔ mk x < 0 := by
  rw [Infinite]; rw [infinitePos_iff]; rw [infiniteNeg_iff]
  aesop

@[deprecated tendsto_iff_forall (since := "2026-01-05")]
/--
theorem `isSt_ofSeq_iff_tendsto` / 定理 `isSt_ofSeq_iff_tendsto`

English:
theorem isSt_ofSeq_iff_tendsto
  given: {f : Nat -> Real} {r : Real}
  proof: Iff.trans (forall₂_congr fun _ _ => (ofSeq_lt_ofSeq.and ofSeq_lt_ofSeq).trans eventually_and.symm)
    (nhds_basis_Ioo_pos _).tendsto_right_iff.symm

@[deprecated tendsto_iff_forall (since := "2026-01-05")]

中文:
定理 isSt_ofSeq_iff_tendsto
  条件: {f : 自然数 -> 实数} {r : 实数}
  证明: Iff.trans (forall₂_congr fun _ _ => (ofSeq_lt_ofSeq.and ofSeq_lt_ofSeq).trans eventually_and.symm)
    (nhds_basis_Ioo_pos _).tendsto_right_iff.symm

@[deprecated tendsto_iff_forall (since := "2026-01-05")]

Depends on / 依赖: Iff.trans, eventually_and, eventually_and.symm, nhds_basis_Ioo_pos, ofSeq_lt_ofSeq, ofSeq_lt_ofSeq.and, tendsto_right_iff, tendsto_right_iff.symm
-/
theorem isSt_ofSeq_iff_tendsto {f : Nat -> Real} {r : Real} :
    IsSt (ofSeq f) r ↔ Tendsto f (hyperfilter Nat) (𝓝 r) :=
  Iff.trans (forall₂_congr fun _ _ => (ofSeq_lt_ofSeq.and ofSeq_lt_ofSeq).trans eventually_and.symm)
    (nhds_basis_Ioo_pos _).tendsto_right_iff.symm

@[deprecated tendsto_iff_forall (since := "2026-01-05")]
/--
theorem `isSt_iff_tendsto` / 定理 `isSt_iff_tendsto`

English:
theorem isSt_iff_tendsto
  given: {x : Real*} {r : Real}
  statement: IsSt x r ↔ x.Tendsto (𝓝 r)
  proof: by
  rcases ofSeq_surjective x with ⟨f, rfl⟩
  exact isSt_ofSeq_iff_tendsto

@[deprecated stdPart_of_tendsto (since := "2026-01-05")]

中文:
定理 isSt_iff_tendsto
  条件: {x : 实数*} {r : 实数}
  结论: IsSt x r ↔ x.Tendsto (𝓝 r)
  证明: by
  rcases ofSeq_surjective x with ⟨f, rfl⟩
  exact isSt_ofSeq_iff_tendsto

@[deprecated stdPart_of_tendsto (since := "2026-01-05")]

Depends on / 依赖: isSt_ofSeq_iff_tendsto, ofSeq_surjective
-/
theorem isSt_iff_tendsto {x : Real*} {r : Real} : IsSt x r ↔ x.Tendsto (𝓝 r) := by
  rcases ofSeq_surjective x with ⟨f, rfl⟩
  exact isSt_ofSeq_iff_tendsto

@[deprecated stdPart_of_tendsto (since := "2026-01-05")]
/--
theorem `isSt_of_tendsto` / 定理 `isSt_of_tendsto`

English:
theorem isSt_of_tendsto
  given: {f : Nat -> Real} {r : Real} (hf : Tendsto f atTop (𝓝 r))
  statement: IsSt (ofSeq f) r
  proof: isSt_ofSeq_iff_tendsto.2 hf.mono_left Nat.hyperfilter_le_atTop

@[deprecated "Use `stdPart_monotoneOn` and `MonotoneOn.reflect_lt`" (since := "2026-01-05")]

中文:
定理 isSt_of_tendsto
  条件: {f : 自然数 -> 实数} {r : 实数} (hf : Tendsto f atTop (𝓝 r))
  结论: IsSt (ofSeq f) r
  证明: isSt_ofSeq_iff_tendsto.2 hf.mono_left Nat.hyperfilter_le_atTop

@[deprecated "Use `stdPart_monotoneOn` and `MonotoneOn.reflect_lt`" (since := "2026-01-05")]

Depends on / 依赖: F.preimage, Nat.hyperfilter_le_atTop, f.unop, hf.mono_left, hyperfilter_le_atTop, isSt_ofSeq_iff_tendsto, mono_left, preimage
-/
theorem isSt_of_tendsto {f : Nat -> Real} {r : Real} (hf : Tendsto f atTop (𝓝 r)) : IsSt (ofSeq f) r :=
isSt_ofSeq_iff_tendsto.2 hf.mono_left Nat.hyperfilter_le_atTop

@[deprecated "Use `stdPart_monotoneOn` and `MonotoneOn.reflect_lt`" (since := "2026-01-05")]
/--
theorem `IsSt.lt` / 定理 `IsSt.lt`

English:
theorem IsSt.lt
  given: {x y : Real*} {r s : Real} (hxr : IsSt x r) (hys : IsSt y s) (hrs : r < s)
  proof: by
  rcases ofSeq_surjective x with ⟨f, rfl⟩
  rcases ofSeq_surjective y with ⟨g, rfl⟩
  rw [isSt_ofSeq_iff_tendsto] at hxr hys
exact ofSeq_lt_ofSeq.2 hxr.eventually_lt hys hrs

@[deprecated "`IsSt` is deprecated" (since := "2026-01-05")]

中文:
定理 IsSt.lt
  条件: {x y : 实数*} {r s : 实数} (hxr : IsSt x r) (hys : IsSt y s) (hrs : r < s)
  证明: by
  rcases ofSeq_surjective x with ⟨f, rfl⟩
  rcases ofSeq_surjective y with ⟨g, rfl⟩
  rw [isSt_ofSeq_iff_tendsto] at hxr hys
exact ofSeq_lt_ofSeq.2 hxr.eventually_lt hys hrs

@[deprecated "`IsSt` is deprecated" (since := "2026-01-05")]

Depends on / 依赖: Quiver, Quiver.Hom.op_inj, Quiver.Hom.unop_inj, map_injective, op_inj, unop_inj
-/
protected theorem IsSt.lt {x y : Real*} {r s : Real} (hxr : IsSt x r) (hys : IsSt y s) (hrs : r < s) :
    x < y := by
  rcases ofSeq_surjective x with ⟨f, rfl⟩
  rcases ofSeq_surjective y with ⟨g, rfl⟩
  rw [isSt_ofSeq_iff_tendsto] at hxr hys
exact ofSeq_lt_ofSeq.2 hxr.eventually_lt hys hrs

@[deprecated "`IsSt` is deprecated" (since := "2026-01-05")]
/--
theorem `IsSt.unique` / 定理 `IsSt.unique`

English:
theorem IsSt.unique
  given: {x : Real*} {r s : Real} (hr : IsSt x r) (hs : IsSt x s)
  statement: r = s
  proof: by
  rcases ofSeq_surjective x with ⟨f, rfl⟩
  rw [isSt_ofSeq_iff_tendsto] at hr hs
  exact tendsto_nhds_unique hr hs

@[deprecated "`IsSt` is deprecated" (since := "2026-01-05")]

中文:
定理 IsSt.unique
  条件: {x : 实数*} {r s : 实数} (hr : IsSt x r) (hs : IsSt x s)
  结论: r = s
  证明: by
  rcases ofSeq_surjective x with ⟨f, rfl⟩
  rw [isSt_ofSeq_iff_tendsto] at hr hs
  exact tendsto_nhds_unique hr hs

@[deprecated "`IsSt` is deprecated" (since := "2026-01-05")]

Depends on / 依赖: isSt_ofSeq_iff_tendsto, ofSeq_surjective, tendsto_nhds_unique
-/
theorem IsSt.unique {x : Real*} {r s : Real} (hr : IsSt x r) (hs : IsSt x s) : r = s := by
  rcases ofSeq_surjective x with ⟨f, rfl⟩
  rw [isSt_ofSeq_iff_tendsto] at hr hs
  exact tendsto_nhds_unique hr hs

@[deprecated "`IsSt` is deprecated" (since := "2026-01-05")]
/--
theorem `IsSt.st_eq` / 定理 `IsSt.st_eq`

English:
theorem IsSt.st_eq
  given: {x : Real*} {r : Real} (hxr : IsSt x r)
  statement: st x = r
  proof: by
  have h : exists r, IsSt x r := ⟨r, hxr⟩
  rw [st]; rw [dif_pos h]
  exact (Classical.choose_spec h).unique hxr

@[deprecated "`IsSt` is deprecated" (since := "2026-01-05")]

中文:
定理 IsSt.st_eq
  条件: {x : 实数*} {r : 实数} (hxr : IsSt x r)
  结论: st x = r
  证明: by
  have h : exists r, IsSt x r := ⟨r, hxr⟩
  rw [st]; rw [dif_pos h]
  exact (Classical.choose_spec h).unique hxr

@[deprecated "`IsSt` is deprecated" (since := "2026-01-05")]

Depends on / 依赖: Classical, Classical.choose_spec, choose_spec, dif_pos, unique
-/
theorem IsSt.st_eq {x : Real*} {r : Real} (hxr : IsSt x r) : st x = r := by
  have h : exists r, IsSt x r := ⟨r, hxr⟩
  rw [st]; rw [dif_pos h]
  exact (Classical.choose_spec h).unique hxr

@[deprecated "`IsSt` is deprecated" (since := "2026-01-05")]
/--
theorem `IsSt.not_infinite` / 定理 `IsSt.not_infinite`

English:
theorem IsSt.not_infinite
  given: {x : Real*} {r : Real} (h : IsSt x r)
  statement: ¬Infinite x
  proof: fun hi =>
  hi.elim (fun hp => lt_asymm (h 1 one_pos).2 (hp (r + 1))) fun hn =>
    lt_asymm (h 1 one_pos).1 (hn (r - 1))

@[deprecated "`IsSt` is deprecated" (since := "2026-01-05")]

中文:
定理 IsSt.not_infinite
  条件: {x : 实数*} {r : 实数} (h : IsSt x r)
  结论: ¬Infinite x
  证明: fun hi =>
  hi.elim (fun hp => lt_asymm (h 1 one_pos).2 (hp (r + 1))) fun hn =>
    lt_asymm (h 1 one_pos).1 (hn (r - 1))

@[deprecated "`IsSt` is deprecated" (since := "2026-01-05")]
-/
theorem IsSt.not_infinite {x : Real*} {r : Real} (h : IsSt x r) : ¬Infinite x := fun hi =>
  hi.elim (fun hp => lt_asymm (h 1 one_pos).2 (hp (r + 1))) fun hn =>
    lt_asymm (h 1 one_pos).1 (hn (r - 1))

@[deprecated "`IsSt` is deprecated" (since := "2026-01-05")]
/--
theorem `not_infinite_of_exists_st` / 定理 `not_infinite_of_exists_st`

English:
theorem not_infinite_of_exists_st
  given: {x : Real*}
  statement: (exists r : Real, IsSt x r) -> ¬Infinite x
  proof: fun ⟨_r, hr⟩ =>
  hr.not_infinite

@[deprecated stdPart_eq_zero (since := "2026-01-05")]

中文:
定理 not_infinite_of_exists_st
  条件: {x : 实数*}
  结论: (存在 r : 实数, IsSt x r) -> ¬Infinite x
  证明: fun ⟨_r, hr⟩ =>
  hr.not_infinite

@[deprecated stdPart_eq_zero (since := "2026-01-05")]
-/
theorem not_infinite_of_exists_st {x : Real*} : (exists r : Real, IsSt x r) -> ¬Infinite x := fun ⟨_r, hr⟩ =>
  hr.not_infinite

@[deprecated stdPart_eq_zero (since := "2026-01-05")]
/--
theorem `Infinite.st_eq` / 定理 `Infinite.st_eq`

English:
theorem Infinite.st_eq
  given: {x : Real*} (hi : Infinite x)
  statement: st x = 0
  proof: dif_neg fun ⟨_r, hr⟩ => hr.not_infinite hi

@[deprecated stdPart_eq_sSup (since := "2026-01-05")]

中文:
定理 Infinite.st_eq
  条件: {x : 实数*} (hi : Infinite x)
  结论: st x = 0
  证明: dif_neg fun ⟨_r, hr⟩ => hr.not_infinite hi

@[deprecated stdPart_eq_sSup (since := "2026-01-05")]

Depends on / 依赖: dif_neg, hr.not_infinite, not_infinite
-/
theorem Infinite.st_eq {x : Real*} (hi : Infinite x) : st x = 0 :=
  dif_neg fun ⟨_r, hr⟩ => hr.not_infinite hi

@[deprecated stdPart_eq_sSup (since := "2026-01-05")]
/--
theorem `isSt_sSup` / 定理 `isSt_sSup`

English:
theorem isSt_sSup
  given: {x : Real*} (hni : ¬Infinite x)
  statement: IsSt x (sSup { y : Real | (y : Real*) < x })
  proof: by
  rw [infinite_iff]; rw [not_lt] at hni
  rw [isSt_iff]
  exact ⟨hni, stdPart_eq_sSup coeRingHom x⟩

@[deprecated stdPart_eq_sSup (since := "2026-01-05")]

中文:
定理 isSt_sSup
  条件: {x : 实数*} (hni : ¬Infinite x)
  结论: IsSt x (sSup { y : 实数 | (y : 实数*) < x })
  证明: by
  rw [infinite_iff]; rw [not_lt] at hni
  rw [isSt_iff]
  exact ⟨hni, stdPart_eq_sSup coeRingHom x⟩

@[deprecated stdPart_eq_sSup (since := "2026-01-05")]

Depends on / 依赖: coeRingHom, infinite_iff, isSt_iff, not_lt, stdPart_eq_sSup
-/
theorem isSt_sSup {x : Real*} (hni : ¬Infinite x) : IsSt x (sSup { y : Real | (y : Real*) < x }) := by
  rw [infinite_iff]; rw [not_lt] at hni
  rw [isSt_iff]
  exact ⟨hni, stdPart_eq_sSup coeRingHom x⟩

@[deprecated stdPart_eq_sSup (since := "2026-01-05")]
/--
theorem `exists_st_of_not_infinite` / 定理 `exists_st_of_not_infinite`

English:
theorem exists_st_of_not_infinite
  given: {x : Real*} (hni : ¬Infinite x)
  statement: exists r : Real, IsSt x r
  proof: ⟨sSup { y : Real | (y : Real*) < x }, isSt_sSup hni⟩

@[deprecated stdPart_eq_sSup (since := "2026-01-05")]

中文:
定理 exists_st_of_not_infinite
  条件: {x : 实数*} (hni : ¬Infinite x)
  结论: 存在 r : 实数, IsSt x r
  证明: ⟨sSup { y : Real | (y : Real*) < x }, isSt_sSup hni⟩

@[deprecated stdPart_eq_sSup (since := "2026-01-05")]

Depends on / 依赖: isSt_sSup
-/
theorem exists_st_of_not_infinite {x : Real*} (hni : ¬Infinite x) : exists r : Real, IsSt x r :=
  ⟨sSup { y : Real | (y : Real*) < x }, isSt_sSup hni⟩

@[deprecated stdPart_eq_sSup (since := "2026-01-05")]
/--
theorem `st_eq_sSup` / 定理 `st_eq_sSup`

English:
theorem st_eq_sSup
  given: {x : Real*}
  statement: st x = sSup { y : Real | (y : Real*) < x }
  proof: by
  rw [st_eq]
  exact stdPart_eq_sSup coeRingHom x

@[deprecated "`IsSt` is deprecated" (since := "2026-01-05")]

中文:
定理 st_eq_sSup
  条件: {x : 实数*}
  结论: st x = sSup { y : 实数 | (y : 实数*) < x }
  证明: by
  rw [st_eq]
  exact stdPart_eq_sSup coeRingHom x

@[deprecated "`IsSt` is deprecated" (since := "2026-01-05")]

Depends on / 依赖: coeRingHom, st_eq, stdPart_eq_sSup
-/
theorem st_eq_sSup {x : Real*} : st x = sSup { y : Real | (y : Real*) < x } := by
  rw [st_eq]
  exact stdPart_eq_sSup coeRingHom x

@[deprecated "`IsSt` is deprecated" (since := "2026-01-05")]
/--
theorem `exists_st_iff_not_infinite` / 定理 `exists_st_iff_not_infinite`

English:
theorem exists_st_iff_not_infinite
  given: {x : Real*}
  statement: (exists r : Real, IsSt x r) ↔ ¬Infinite x
  proof: ⟨not_infinite_of_exists_st, exists_st_of_not_infinite⟩

@[deprecated "`IsSt` is deprecated" (since := "2026-01-05")]

中文:
定理 exists_st_iff_not_infinite
  条件: {x : 实数*}
  结论: (存在 r : 实数, IsSt x r) ↔ ¬Infinite x
  证明: ⟨not_infinite_of_exists_st, exists_st_of_not_infinite⟩

@[deprecated "`IsSt` is deprecated" (since := "2026-01-05")]

Depends on / 依赖: exists_st_of_not_infinite, not_infinite_of_exists_st
-/
theorem exists_st_iff_not_infinite {x : Real*} : (exists r : Real, IsSt x r) ↔ ¬Infinite x :=
  ⟨not_infinite_of_exists_st, exists_st_of_not_infinite⟩

@[deprecated "`IsSt` is deprecated" (since := "2026-01-05")]
/--
theorem `infinite_iff_not_exists_st` / 定理 `infinite_iff_not_exists_st`

English:
theorem infinite_iff_not_exists_st
  given: {x : Real*}
  statement: Infinite x ↔ ¬exists r : Real, IsSt x r
  proof: iff_not_comm.mp exists_st_iff_not_infinite

@[deprecated "`IsSt` is deprecated" (since := "2026-01-05")]

中文:
定理 infinite_iff_not_exists_st
  条件: {x : 实数*}
  结论: Infinite x ↔ ¬存在 r : 实数, IsSt x r
  证明: iff_not_comm.mp exists_st_iff_not_infinite

@[deprecated "`IsSt` is deprecated" (since := "2026-01-05")]

Depends on / 依赖: exists_st_iff_not_infinite, iff_not_comm, iff_not_comm.mp
-/
theorem infinite_iff_not_exists_st {x : Real*} : Infinite x ↔ ¬exists r : Real, IsSt x r :=
  iff_not_comm.mp exists_st_iff_not_infinite

@[deprecated "`IsSt` is deprecated" (since := "2026-01-05")]
/--
theorem `IsSt.isSt_st` / 定理 `IsSt.isSt_st`

English:
theorem IsSt.isSt_st
  given: {x : Real*} {r : Real} (hxr : IsSt x r)
  statement: IsSt x (st x)
  proof: by
  rwa [hxr.st_eq]

@[deprecated "`IsSt` is deprecated" (since := "2026-01-05")]

中文:
定理 IsSt.isSt_st
  条件: {x : 实数*} {r : 实数} (hxr : IsSt x r)
  结论: IsSt x (st x)
  证明: by
  rwa [hxr.st_eq]

@[deprecated "`IsSt` is deprecated" (since := "2026-01-05")]

Depends on / 依赖: hxr.st_eq, st_eq
-/
theorem IsSt.isSt_st {x : Real*} {r : Real} (hxr : IsSt x r) : IsSt x (st x) := by
  rwa [hxr.st_eq]

@[deprecated "`IsSt` is deprecated" (since := "2026-01-05")]
/--
theorem `isSt_st_of_exists_st` / 定理 `isSt_st_of_exists_st`

English:
theorem isSt_st_of_exists_st
  given: {x : Real*} (hx : exists r : Real, IsSt x r)
  statement: IsSt x (st x)
  proof: let ⟨_r, hr⟩ := hx; hr.isSt_st

@[deprecated "`IsSt` is deprecated" (since := "2026-01-05")]

中文:
定理 isSt_st_of_exists_st
  条件: {x : 实数*} (hx : 存在 r : 实数, IsSt x r)
  结论: IsSt x (st x)
  证明: let ⟨_r, hr⟩ := hx; hr.isSt_st

@[deprecated "`IsSt` is deprecated" (since := "2026-01-05")]

Depends on / 依赖: hr.isSt_st, isSt_st
-/
theorem isSt_st_of_exists_st {x : Real*} (hx : exists r : Real, IsSt x r) : IsSt x (st x) :=
  let ⟨_r, hr⟩ := hx; hr.isSt_st

@[deprecated "`IsSt` is deprecated" (since := "2026-01-05")]
/--
theorem `isSt_st'` / 定理 `isSt_st'`

English:
theorem isSt_st'
  given: {x : Real*} (hx : ¬Infinite x)
  statement: IsSt x (st x)
  proof: (isSt_sSup hx).isSt_st

@[deprecated "`IsSt` is deprecated" (since := "2026-01-05")]

中文:
定理 isSt_st'
  条件: {x : 实数*} (hx : ¬Infinite x)
  结论: IsSt x (st x)
  证明: (isSt_sSup hx).isSt_st

@[deprecated "`IsSt` is deprecated" (since := "2026-01-05")]

Depends on / 依赖: isSt_sSup, isSt_st
-/
theorem isSt_st' {x : Real*} (hx : ¬Infinite x) : IsSt x (st x) :=
  (isSt_sSup hx).isSt_st

@[deprecated "`IsSt` is deprecated" (since := "2026-01-05")]
/--
theorem `isSt_st` / 定理 `isSt_st`

English:
theorem isSt_st
  given: {x : Real*} (hx : st x != 0)
  statement: IsSt x (st x)
  proof: isSt_st' mt Infinite.st_eq hx

@[deprecated "`IsSt` is deprecated" (since := "2026-01-05")]

中文:
定理 isSt_st
  条件: {x : 实数*} (hx : st x != 0)
  结论: IsSt x (st x)
  证明: isSt_st' mt Infinite.st_eq hx

@[deprecated "`IsSt` is deprecated" (since := "2026-01-05")]

Depends on / 依赖: Infinite, Infinite.st_eq, isSt_st, st_eq
-/
theorem isSt_st {x : Real*} (hx : st x != 0) : IsSt x (st x) :=
isSt_st' mt Infinite.st_eq hx

@[deprecated "`IsSt` is deprecated" (since := "2026-01-05")]
/--
theorem `isSt_refl_real` / 定理 `isSt_refl_real`

English:
theorem isSt_refl_real
  given: (r : Real)
  statement: IsSt r r
  proof: isSt_ofSeq_iff_tendsto.2 tendsto_const_nhds

@[deprecated stdPart_coe (since := "2026-01-05")]

中文:
定理 isSt_refl_real
  条件: (r : 实数)
  结论: IsSt r r
  证明: isSt_ofSeq_iff_tendsto.2 tendsto_const_nhds

@[deprecated stdPart_coe (since := "2026-01-05")]

Depends on / 依赖: isSt_ofSeq_iff_tendsto, tendsto_const_nhds
-/
theorem isSt_refl_real (r : Real) : IsSt r r := isSt_ofSeq_iff_tendsto.2 tendsto_const_nhds

@[deprecated stdPart_coe (since := "2026-01-05")]
/--
theorem `st_id_real` / 定理 `st_id_real`

English:
theorem st_id_real
  given: (r : Real)
  statement: st r = r
  proof: (isSt_refl_real r).st_eq

@[deprecated "`IsSt` is deprecated" (since := "2026-01-05")]

中文:
定理 st_id_real
  条件: (r : 实数)
  结论: st r = r
  证明: (isSt_refl_real r).st_eq

@[deprecated "`IsSt` is deprecated" (since := "2026-01-05")]

Depends on / 依赖: isSt_refl_real, st_eq
-/
theorem st_id_real (r : Real) : st r = r := (isSt_refl_real r).st_eq

@[deprecated "`IsSt` is deprecated" (since := "2026-01-05")]
/--
theorem `eq_of_isSt_real` / 定理 `eq_of_isSt_real`

English:
theorem eq_of_isSt_real
  given: {r s : Real}
  statement: IsSt r s -> r = s
  proof: (isSt_refl_real r).unique

@[deprecated "`IsSt` is deprecated" (since := "2026-01-05")]

中文:
定理 eq_of_isSt_real
  条件: {r s : 实数}
  结论: IsSt r s -> r = s
  证明: (isSt_refl_real r).unique

@[deprecated "`IsSt` is deprecated" (since := "2026-01-05")]

Depends on / 依赖: isSt_refl_real, unique
-/
theorem eq_of_isSt_real {r s : Real} : IsSt r s -> r = s :=
  (isSt_refl_real r).unique

@[deprecated "`IsSt` is deprecated" (since := "2026-01-05")]
/--
theorem `isSt_real_iff_eq` / 定理 `isSt_real_iff_eq`

English:
theorem isSt_real_iff_eq
  given: {r s : Real}
  statement: IsSt r s ↔ r = s
  proof: ⟨eq_of_isSt_real, fun hrs => hrs ▸ isSt_refl_real r⟩

@[deprecated "`IsSt` is deprecated" (since := "2026-01-05")]

中文:
定理 isSt_real_iff_eq
  条件: {r s : 实数}
  结论: IsSt r s ↔ r = s
  证明: ⟨eq_of_isSt_real, fun hrs => hrs ▸ isSt_refl_real r⟩

@[deprecated "`IsSt` is deprecated" (since := "2026-01-05")]

Depends on / 依赖: eq_of_isSt_real, isSt_refl_real
-/
theorem isSt_real_iff_eq {r s : Real} : IsSt r s ↔ r = s :=
  ⟨eq_of_isSt_real, fun hrs => hrs ▸ isSt_refl_real r⟩

@[deprecated "`IsSt` is deprecated" (since := "2026-01-05")]
/--
theorem `isSt_symm_real` / 定理 `isSt_symm_real`

English:
theorem isSt_symm_real
  given: {r s : Real}
  statement: IsSt r s ↔ IsSt s r
  proof: by
  rw [isSt_real_iff_eq]; rw [isSt_real_iff_eq]; rw [eq_comm]

@[deprecated "`IsSt` is deprecated" (since := "2026-01-05")]

中文:
定理 isSt_symm_real
  条件: {r s : 实数}
  结论: IsSt r s ↔ IsSt s r
  证明: by
  rw [isSt_real_iff_eq]; rw [isSt_real_iff_eq]; rw [eq_comm]

@[deprecated "`IsSt` is deprecated" (since := "2026-01-05")]

Depends on / 依赖: eq_comm, isSt_real_iff_eq
-/
theorem isSt_symm_real {r s : Real} : IsSt r s ↔ IsSt s r := by
  rw [isSt_real_iff_eq]; rw [isSt_real_iff_eq]; rw [eq_comm]

@[deprecated "`IsSt` is deprecated" (since := "2026-01-05")]
/--
theorem `isSt_trans_real` / 定理 `isSt_trans_real`

English:
theorem isSt_trans_real
  given: {r s t : Real}
  statement: IsSt r s -> IsSt s t -> IsSt r t
  proof: by
  rw [isSt_real_iff_eq]; rw [isSt_real_iff_eq]; rw [isSt_real_iff_eq]; exact Eq.trans

@[deprecated "`IsSt` is deprecated" (since := "2026-01-05")]

中文:
定理 isSt_trans_real
  条件: {r s t : 实数}
  结论: IsSt r s -> IsSt s t -> IsSt r t
  证明: by
  rw [isSt_real_iff_eq]; rw [isSt_real_iff_eq]; rw [isSt_real_iff_eq]; exact Eq.trans

@[deprecated "`IsSt` is deprecated" (since := "2026-01-05")]

Depends on / 依赖: Eq.trans, isSt_real_iff_eq
-/
theorem isSt_trans_real {r s t : Real} : IsSt r s -> IsSt s t -> IsSt r t := by
  rw [isSt_real_iff_eq]; rw [isSt_real_iff_eq]; rw [isSt_real_iff_eq]; exact Eq.trans

@[deprecated "`IsSt` is deprecated" (since := "2026-01-05")]
/--
theorem `isSt_inj_real` / 定理 `isSt_inj_real`

English:
theorem isSt_inj_real
  given: {r₁ r₂ s : Real} (h1 : IsSt r₁ s) (h2 : IsSt r₂ s)
  statement: r₁ = r₂
  proof: Eq.trans (eq_of_isSt_real h1) (eq_of_isSt_real h2).symm

@[deprecated "`IsSt` is deprecated" (since := "2026-01-05")]

中文:
定理 isSt_inj_real
  条件: {r₁ r₂ s : 实数} (h1 : IsSt r₁ s) (h2 : IsSt r₂ s)
  结论: r₁ = r₂
  证明: Eq.trans (eq_of_isSt_real h1) (eq_of_isSt_real h2).symm

@[deprecated "`IsSt` is deprecated" (since := "2026-01-05")]

Depends on / 依赖: Eq.trans, eq_of_isSt_real
-/
theorem isSt_inj_real {r₁ r₂ s : Real} (h1 : IsSt r₁ s) (h2 : IsSt r₂ s) : r₁ = r₂ :=
  Eq.trans (eq_of_isSt_real h1) (eq_of_isSt_real h2).symm

@[deprecated "`IsSt` is deprecated" (since := "2026-01-05")]
/--
theorem `isSt_iff_abs_sub_lt_delta` / 定理 `isSt_iff_abs_sub_lt_delta`

English:
theorem isSt_iff_abs_sub_lt_delta
  given: {x : Real*} {r : Real}
  statement: IsSt x r ↔ forall δ : Real, 0 < δ -> |x - ↑r| < δ
  proof: by
  simp only [abs_sub_lt_iff, sub_lt_iff_lt_add, IsSt, and_comm, add_comm]

@[deprecated stdPart_map (since := "2026-01-05")]

中文:
定理 isSt_iff_abs_sub_lt_delta
  条件: {x : 实数*} {r : 实数}
  结论: IsSt x r ↔ 对任意 δ : 实数, 0 < δ -> |x - ↑r| < δ
  证明: by
  simp only [abs_sub_lt_iff, sub_lt_iff_lt_add, IsSt, and_comm, add_comm]

@[deprecated stdPart_map (since := "2026-01-05")]

Depends on / 依赖: abs_sub_lt_iff, add_comm, and_comm, sub_lt_iff_lt_add
-/
theorem isSt_iff_abs_sub_lt_delta {x : Real*} {r : Real} : IsSt x r ↔ forall δ : Real, 0 < δ -> |x - ↑r| < δ := by
  simp only [abs_sub_lt_iff, sub_lt_iff_lt_add, IsSt, and_comm, add_comm]

@[deprecated stdPart_map (since := "2026-01-05")]
/--
theorem `IsSt.map` / 定理 `IsSt.map`

English:
theorem IsSt.map
  given: {x : Real*} {r : Real} (hxr : IsSt x r) {f : Real -> Real} (hf : ContinuousAt f r)
  proof: by
  rcases ofSeq_surjective x with ⟨g, rfl⟩
exact isSt_ofSeq_iff_tendsto.2 hf.tendsto.comp (isSt_ofSeq_iff_tendsto.1 hxr)

@[deprecated stdPart_map₂ (since := "2026-01-05")]

中文:
定理 IsSt.map
  条件: {x : 实数*} {r : 实数} (hxr : IsSt x r) {f : 实数 -> 实数} (hf : ContinuousAt f r)
  证明: by
  rcases ofSeq_surjective x with ⟨g, rfl⟩
exact isSt_ofSeq_iff_tendsto.2 hf.tendsto.comp (isSt_ofSeq_iff_tendsto.1 hxr)

@[deprecated stdPart_map₂ (since := "2026-01-05")]

Depends on / 依赖: hf.tendsto.comp, isSt_ofSeq_iff_tendsto, ofSeq_surjective, tendsto
-/
theorem IsSt.map {x : Real*} {r : Real} (hxr : IsSt x r) {f : Real -> Real} (hf : ContinuousAt f r) :
    IsSt (x.map f) (f r) := by
  rcases ofSeq_surjective x with ⟨g, rfl⟩
exact isSt_ofSeq_iff_tendsto.2 hf.tendsto.comp (isSt_ofSeq_iff_tendsto.1 hxr)

@[deprecated stdPart_map₂ (since := "2026-01-05")]
/--
theorem `IsSt.map₂` / 定理 `IsSt.map₂`

English:
theorem IsSt.map₂
  statement: {x y : Real*} {r s : Real} (hxr : IsSt x r) (hys : IsSt y s) {f : Real -> Real -> Real}
  proof: by
  rcases ofSeq_surjective x with ⟨x, rfl⟩
  rcases ofSeq_surjective y with ⟨y, rfl⟩
  rw [isSt_ofSeq_iff_tendsto] at hxr hys
exact isSt_ofSeq_iff_tendsto.2 hf.tendsto.comp (hxr.prodMk_nhds hys)

@[deprecated stdPart_add (since := "2026-01-05")]

中文:
定理 IsSt.map₂
  结论: {x y : 实数*} {r s : 实数} (hxr : IsSt x r) (hys : IsSt y s) {f : 实数 -> 实数 -> 实数}
  证明: by
  rcases ofSeq_surjective x with ⟨x, rfl⟩
  rcases ofSeq_surjective y with ⟨y, rfl⟩
  rw [isSt_ofSeq_iff_tendsto] at hxr hys
exact isSt_ofSeq_iff_tendsto.2 hf.tendsto.comp (hxr.prodMk_nhds hys)

@[deprecated stdPart_add (since := "2026-01-05")]

Depends on / 依赖: hf.tendsto.comp, hxr.prodMk_nhds, isSt_ofSeq_iff_tendsto, ofSeq_surjective, prodMk_nhds, tendsto
-/
theorem IsSt.map₂ {x y : Real*} {r s : Real} (hxr : IsSt x r) (hys : IsSt y s) {f : Real -> Real -> Real}
    (hf : ContinuousAt (Function.uncurry f) (r, s)) : IsSt (x.map₂ f y) (f r s) := by
  rcases ofSeq_surjective x with ⟨x, rfl⟩
  rcases ofSeq_surjective y with ⟨y, rfl⟩
  rw [isSt_ofSeq_iff_tendsto] at hxr hys
exact isSt_ofSeq_iff_tendsto.2 hf.tendsto.comp (hxr.prodMk_nhds hys)

@[deprecated stdPart_add (since := "2026-01-05")]
/--
theorem `IsSt.add` / 定理 `IsSt.add`

English:
theorem IsSt.add
  given: {x y : Real*} {r s : Real} (hxr : IsSt x r) (hys : IsSt y s)
  proof: hxr.map₂ hys continuous_add.continuousAt

@[deprecated stdPart_neg (since := "2026-01-05")]

中文:
定理 IsSt.add
  条件: {x y : 实数*} {r s : 实数} (hxr : IsSt x r) (hys : IsSt y s)
  证明: hxr.map₂ hys continuous_add.continuousAt

@[deprecated stdPart_neg (since := "2026-01-05")]

Depends on / 依赖: continuousAt, continuous_add, continuous_add.continuousAt, hxr.map
-/
theorem IsSt.add {x y : Real*} {r s : Real} (hxr : IsSt x r) (hys : IsSt y s) :
    IsSt (x + y) (r + s) := hxr.map₂ hys continuous_add.continuousAt

@[deprecated stdPart_neg (since := "2026-01-05")]
/--
theorem `IsSt.neg` / 定理 `IsSt.neg`

English:
theorem IsSt.neg
  given: {x : Real*} {r : Real} (hxr : IsSt x r)
  statement: IsSt (-x) (-r)
  proof: hxr.map continuous_neg.continuousAt

@[deprecated stdPart_sub (since := "2026-01-05")]

中文:
定理 IsSt.neg
  条件: {x : 实数*} {r : 实数} (hxr : IsSt x r)
  结论: IsSt (-x) (-r)
  证明: hxr.map continuous_neg.continuousAt

@[deprecated stdPart_sub (since := "2026-01-05")]

Depends on / 依赖: continuousAt, continuous_neg, continuous_neg.continuousAt, hxr.map
-/
theorem IsSt.neg {x : Real*} {r : Real} (hxr : IsSt x r) : IsSt (-x) (-r) :=
  hxr.map continuous_neg.continuousAt

@[deprecated stdPart_sub (since := "2026-01-05")]
/--
theorem `IsSt.sub` / 定理 `IsSt.sub`

English:
theorem IsSt.sub
  given: {x y : Real*} {r s : Real} (hxr : IsSt x r) (hys : IsSt y s)
  statement: IsSt (x - y) (r - s)
  proof: hxr.map₂ hys continuous_sub.continuousAt

@[deprecated stdPart_monotoneOn (since := "2026-01-05")]

中文:
定理 IsSt.sub
  条件: {x y : 实数*} {r s : 实数} (hxr : IsSt x r) (hys : IsSt y s)
  结论: IsSt (x - y) (r - s)
  证明: hxr.map₂ hys continuous_sub.continuousAt

@[deprecated stdPart_monotoneOn (since := "2026-01-05")]

Depends on / 依赖: continuousAt, continuous_sub, continuous_sub.continuousAt, hxr.map
-/
theorem IsSt.sub {x y : Real*} {r s : Real} (hxr : IsSt x r) (hys : IsSt y s) : IsSt (x - y) (r - s) :=
  hxr.map₂ hys continuous_sub.continuousAt

@[deprecated stdPart_monotoneOn (since := "2026-01-05")]
/--
theorem `IsSt.le` / 定理 `IsSt.le`

English:
theorem IsSt.le
  given: {x y : Real*} {r s : Real} (hrx : IsSt x r) (hsy : IsSt y s) (hxy : x <= y)
  statement: r <= s
  proof: not_lt.1 fun h => hxy.not_gt hsy.lt hrx h

@[deprecated stdPart_monotoneOn (since := "2026-01-05")]

中文:
定理 IsSt.le
  条件: {x y : 实数*} {r s : 实数} (hrx : IsSt x r) (hsy : IsSt y s) (hxy : x <= y)
  结论: r <= s
  证明: not_lt.1 fun h => hxy.not_gt hsy.lt hrx h

@[deprecated stdPart_monotoneOn (since := "2026-01-05")]

Depends on / 依赖: hsy.lt, hxy.not_gt, not_gt, not_lt
-/
theorem IsSt.le {x y : Real*} {r s : Real} (hrx : IsSt x r) (hsy : IsSt y s) (hxy : x <= y) : r <= s :=
not_lt.1 fun h => hxy.not_gt hsy.lt hrx h

@[deprecated stdPart_monotoneOn (since := "2026-01-05")]
/--
theorem `st_le_of_le` / 定理 `st_le_of_le`

English:
theorem st_le_of_le
  given: {x y : Real*} (hix : ¬Infinite x) (hiy : ¬Infinite y)
  statement: x <= y -> st x <= st y
  proof: (isSt_st' hix).le (isSt_st' hiy)

@[deprecated stdPart_monotoneOn (since := "2026-01-05")]

中文:
定理 st_le_of_le
  条件: {x y : 实数*} (hix : ¬Infinite x) (hiy : ¬Infinite y)
  结论: x <= y -> st x <= st y
  证明: (isSt_st' hix).le (isSt_st' hiy)

@[deprecated stdPart_monotoneOn (since := "2026-01-05")]

Depends on / 依赖: isSt_st
-/
theorem st_le_of_le {x y : Real*} (hix : ¬Infinite x) (hiy : ¬Infinite y) : x <= y -> st x <= st y :=
  (isSt_st' hix).le (isSt_st' hiy)

@[deprecated stdPart_monotoneOn (since := "2026-01-05")]
/--
theorem `lt_of_st_lt` / 定理 `lt_of_st_lt`

English:
theorem lt_of_st_lt
  given: {x y : Real*} (hix : ¬Infinite x) (hiy : ¬Infinite y)
  statement: st x < st y -> x < y
  proof: (isSt_st' hix).lt (isSt_st' hiy)

@[deprecated "`InfinitePos` is deprecated" (since := "2026-01-05")]

中文:
定理 lt_of_st_lt
  条件: {x y : 实数*} (hix : ¬Infinite x) (hiy : ¬Infinite y)
  结论: st x < st y -> x < y
  证明: (isSt_st' hix).lt (isSt_st' hiy)

@[deprecated "`InfinitePos` is deprecated" (since := "2026-01-05")]

Depends on / 依赖: isSt_st
-/
theorem lt_of_st_lt {x y : Real*} (hix : ¬Infinite x) (hiy : ¬Infinite y) : st x < st y -> x < y :=
  (isSt_st' hix).lt (isSt_st' hiy)

@[deprecated "`InfinitePos` is deprecated" (since := "2026-01-05")]
/--
theorem `infinitePos_def` / 定理 `infinitePos_def`

English:
theorem infinitePos_def
  given: {x : Real*}
  statement: InfinitePos x ↔ forall r : Real, ↑r < x
  proof: Iff.rfl

@[deprecated "`InfiniteNeg` is deprecated" (since := "2026-01-05")]

中文:
定理 infinitePos_def
  条件: {x : 实数*}
  结论: InfinitePos x ↔ 对任意 r : 实数, ↑r < x
  证明: Iff.rfl

@[deprecated "`InfiniteNeg` is deprecated" (since := "2026-01-05")]

Depends on / 依赖: Iff.rfl
-/
theorem infinitePos_def {x : Real*} : InfinitePos x ↔ forall r : Real, ↑r < x := Iff.rfl

@[deprecated "`InfiniteNeg` is deprecated" (since := "2026-01-05")]
/--
theorem `infiniteNeg_def` / 定理 `infiniteNeg_def`

English:
theorem infiniteNeg_def
  given: {x : Real*}
  statement: InfiniteNeg x ↔ forall r : Real, x < r
  proof: Iff.rfl

@[deprecated "`InfinitePos` is deprecated" (since := "2026-01-05")]

中文:
定理 infiniteNeg_def
  条件: {x : 实数*}
  结论: InfiniteNeg x ↔ 对任意 r : 实数, x < r
  证明: Iff.rfl

@[deprecated "`InfinitePos` is deprecated" (since := "2026-01-05")]

Depends on / 依赖: Iff.rfl
-/
theorem infiniteNeg_def {x : Real*} : InfiniteNeg x ↔ forall r : Real, x < r := Iff.rfl

@[deprecated "`InfinitePos` is deprecated" (since := "2026-01-05")]
/--
theorem `InfinitePos.pos` / 定理 `InfinitePos.pos`

English:
theorem InfinitePos.pos
  given: {x : Real*} (hip : InfinitePos x)
  statement: 0 < x
  proof: hip 0

@[deprecated "`InfiniteNeg` is deprecated" (since := "2026-01-05")]

中文:
定理 InfinitePos.pos
  条件: {x : 实数*} (hip : InfinitePos x)
  结论: 0 < x
  证明: hip 0

@[deprecated "`InfiniteNeg` is deprecated" (since := "2026-01-05")]
-/
theorem InfinitePos.pos {x : Real*} (hip : InfinitePos x) : 0 < x := hip 0

@[deprecated "`InfiniteNeg` is deprecated" (since := "2026-01-05")]
/--
theorem `InfiniteNeg.lt_zero` / 定理 `InfiniteNeg.lt_zero`

English:
theorem InfiniteNeg.lt_zero
  given: {x : Real*}
  statement: InfiniteNeg x -> x < 0
  proof: fun hin => hin 0

@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]

中文:
定理 InfiniteNeg.lt_zero
  条件: {x : 实数*}
  结论: InfiniteNeg x -> x < 0
  证明: fun hin => hin 0

@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]
-/
theorem InfiniteNeg.lt_zero {x : Real*} : InfiniteNeg x -> x < 0 := fun hin => hin 0

@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]
/--
theorem `Infinite.ne_zero` / 定理 `Infinite.ne_zero`

English:
theorem Infinite.ne_zero
  given: {x : Real*} (hI : Infinite x)
  statement: x != 0
  proof: hI.elim (fun hip => hip.pos.ne') fun hin => hin.lt_zero.ne

@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]

中文:
定理 Infinite.ne_zero
  条件: {x : 实数*} (hI : Infinite x)
  结论: x != 0
  证明: hI.elim (fun hip => hip.pos.ne') fun hin => hin.lt_zero.ne

@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]

Depends on / 依赖: hI.elim, hin.lt_zero.ne, hip.pos.ne, lt_zero
-/
theorem Infinite.ne_zero {x : Real*} (hI : Infinite x) : x != 0 :=
  hI.elim (fun hip => hip.pos.ne') fun hin => hin.lt_zero.ne

@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]
/--
theorem `not_infinite_zero` / 定理 `not_infinite_zero`

English:
theorem not_infinite_zero
  statement: ¬Infinite 0
  proof: fun hI => hI.ne_zero rfl

@[deprecated "`InfinitePos` and `InfiniteNeg` are deprecated" (since := "2026-01-05")]

中文:
定理 not_infinite_zero
  结论: ¬Infinite 0
  证明: fun hI => hI.ne_zero rfl

@[deprecated "`InfinitePos` and `InfiniteNeg` are deprecated" (since := "2026-01-05")]

Depends on / 依赖: hI.ne_zero, ne_zero
-/
theorem not_infinite_zero : ¬Infinite 0 := fun hI => hI.ne_zero rfl

@[deprecated "`InfinitePos` and `InfiniteNeg` are deprecated" (since := "2026-01-05")]
/--
theorem `InfiniteNeg.not_infinitePos` / 定理 `InfiniteNeg.not_infinitePos`

English:
theorem InfiniteNeg.not_infinitePos
  given: {x : Real*}
  statement: InfiniteNeg x -> ¬InfinitePos x
  proof: fun hn hp =>
  (hn 0).not_gt (hp 0)

@[deprecated "`InfinitePos` and `InfiniteNeg` are deprecated" (since := "2026-01-05")]

中文:
定理 InfiniteNeg.not_infinitePos
  条件: {x : 实数*}
  结论: InfiniteNeg x -> ¬InfinitePos x
  证明: fun hn hp =>
  (hn 0).not_gt (hp 0)

@[deprecated "`InfinitePos` and `InfiniteNeg` are deprecated" (since := "2026-01-05")]
-/
theorem InfiniteNeg.not_infinitePos {x : Real*} : InfiniteNeg x -> ¬InfinitePos x := fun hn hp =>
  (hn 0).not_gt (hp 0)

@[deprecated "`InfinitePos` and `InfiniteNeg` are deprecated" (since := "2026-01-05")]
/--
theorem `InfinitePos.not_infiniteNeg` / 定理 `InfinitePos.not_infiniteNeg`

English:
theorem InfinitePos.not_infiniteNeg
  given: {x : Real*} (hp : InfinitePos x)
  statement: ¬InfiniteNeg x
  proof: fun hn =>
  hn.not_infinitePos hp

@[deprecated "`InfinitePos` and `InfiniteNeg` are deprecated" (since := "2026-01-05")]

中文:
定理 InfinitePos.not_infiniteNeg
  条件: {x : 实数*} (hp : InfinitePos x)
  结论: ¬InfiniteNeg x
  证明: fun hn =>
  hn.not_infinitePos hp

@[deprecated "`InfinitePos` and `InfiniteNeg` are deprecated" (since := "2026-01-05")]
-/
theorem InfinitePos.not_infiniteNeg {x : Real*} (hp : InfinitePos x) : ¬InfiniteNeg x := fun hn =>
  hn.not_infinitePos hp

@[deprecated "`InfinitePos` and `InfiniteNeg` are deprecated" (since := "2026-01-05")]
/--
theorem `InfinitePos.neg` / 定理 `InfinitePos.neg`

English:
theorem InfinitePos.neg
  given: {x : Real*}
  statement: InfinitePos x -> InfiniteNeg (-x)
  proof: fun hp r =>
  neg_lt.mp (hp (-r))

@[deprecated "`InfinitePos` and `InfiniteNeg` are deprecated" (since := "2026-01-05")]

中文:
定理 InfinitePos.neg
  条件: {x : 实数*}
  结论: InfinitePos x -> InfiniteNeg (-x)
  证明: fun hp r =>
  neg_lt.mp (hp (-r))

@[deprecated "`InfinitePos` and `InfiniteNeg` are deprecated" (since := "2026-01-05")]
-/
theorem InfinitePos.neg {x : Real*} : InfinitePos x -> InfiniteNeg (-x) := fun hp r =>
  neg_lt.mp (hp (-r))

@[deprecated "`InfinitePos` and `InfiniteNeg` are deprecated" (since := "2026-01-05")]
/--
theorem `InfiniteNeg.neg` / 定理 `InfiniteNeg.neg`

English:
theorem InfiniteNeg.neg
  given: {x : Real*}
  statement: InfiniteNeg x -> InfinitePos (-x)
  proof: fun hp r =>
  lt_neg.mp (hp (-r))

@[deprecated "`InfinitePos` and `InfiniteNeg` are deprecated" (since := "2026-01-05")]

中文:
定理 InfiniteNeg.neg
  条件: {x : 实数*}
  结论: InfiniteNeg x -> InfinitePos (-x)
  证明: fun hp r =>
  lt_neg.mp (hp (-r))

@[deprecated "`InfinitePos` and `InfiniteNeg` are deprecated" (since := "2026-01-05")]
-/
theorem InfiniteNeg.neg {x : Real*} : InfiniteNeg x -> InfinitePos (-x) := fun hp r =>
  lt_neg.mp (hp (-r))

@[deprecated "`InfinitePos` and `InfiniteNeg` are deprecated" (since := "2026-01-05")]
/--
theorem `infiniteNeg_neg` / 定理 `infiniteNeg_neg`

English:
theorem infiniteNeg_neg
  given: {x : Real*}
  statement: InfiniteNeg (-x) ↔ InfinitePos x
  proof: ⟨fun hin => neg_neg x ▸ hin.neg, InfinitePos.neg⟩

@[deprecated "`InfinitePos` and `InfiniteNeg` are deprecated" (since := "2026-01-05")]

中文:
定理 infiniteNeg_neg
  条件: {x : 实数*}
  结论: InfiniteNeg (-x) ↔ InfinitePos x
  证明: ⟨fun hin => neg_neg x ▸ hin.neg, InfinitePos.neg⟩

@[deprecated "`InfinitePos` and `InfiniteNeg` are deprecated" (since := "2026-01-05")]

Depends on / 依赖: InfinitePos, InfinitePos.neg, hin.neg, neg_neg
-/
theorem infiniteNeg_neg {x : Real*} : InfiniteNeg (-x) ↔ InfinitePos x :=
  ⟨fun hin => neg_neg x ▸ hin.neg, InfinitePos.neg⟩

@[deprecated "`InfinitePos` and `InfiniteNeg` are deprecated" (since := "2026-01-05")]
/--
theorem `infinitePos_neg` / 定理 `infinitePos_neg`

English:
theorem infinitePos_neg
  given: {x : Real*}
  statement: InfinitePos (-x) ↔ InfiniteNeg x
  proof: ⟨fun hin => neg_neg x ▸ hin.neg, InfiniteNeg.neg⟩

@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]

中文:
定理 infinitePos_neg
  条件: {x : 实数*}
  结论: InfinitePos (-x) ↔ InfiniteNeg x
  证明: ⟨fun hin => neg_neg x ▸ hin.neg, InfiniteNeg.neg⟩

@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]

Depends on / 依赖: InfiniteNeg, InfiniteNeg.neg, hin.neg, neg_neg
-/
theorem infinitePos_neg {x : Real*} : InfinitePos (-x) ↔ InfiniteNeg x :=
  ⟨fun hin => neg_neg x ▸ hin.neg, InfiniteNeg.neg⟩

@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]
/--
theorem `infinite_neg` / 定理 `infinite_neg`

English:
theorem infinite_neg
  given: {x : Real*}
  statement: Infinite (-x) ↔ Infinite x
  proof: or_comm.trans infiniteNeg_neg.or infinitePos_neg

@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]
nonrec theorem Infinitesimal.not_infinite {x : Real*} (h : Infinitesimal x) : ¬Infinite x :=
  h.not_infinite

@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]

中文:
定理 infinite_neg
  条件: {x : 实数*}
  结论: Infinite (-x) ↔ Infinite x
  证明: or_comm.trans infiniteNeg_neg.or infinitePos_neg

@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]
nonrec theorem Infinitesimal.not_infinite {x : Real*} (h : Infinitesimal x) : ¬Infinite x :=
  h.not_infinite

@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]

Depends on / 依赖: infiniteNeg_neg, infiniteNeg_neg.or, infinitePos_neg, or_comm, or_comm.trans
-/
theorem infinite_neg {x : Real*} : Infinite (-x) ↔ Infinite x :=
or_comm.trans infiniteNeg_neg.or infinitePos_neg

@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]
nonrec theorem Infinitesimal.not_infinite {x : Real*} (h : Infinitesimal x) : ¬Infinite x :=
  h.not_infinite

@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]
/--
theorem `Infinite.not_infinitesimal` / 定理 `Infinite.not_infinitesimal`

English:
theorem Infinite.not_infinitesimal
  given: {x : Real*} (h : Infinite x)
  statement: ¬Infinitesimal x
  proof: fun h' =>
  h'.not_infinite h

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]

中文:
定理 Infinite.not_infinitesimal
  条件: {x : 实数*} (h : Infinite x)
  结论: ¬Infinitesimal x
  证明: fun h' =>
  h'.not_infinite h

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
-/
theorem Infinite.not_infinitesimal {x : Real*} (h : Infinite x) : ¬Infinitesimal x := fun h' =>
  h'.not_infinite h

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
/--
theorem `InfinitePos.not_infinitesimal` / 定理 `InfinitePos.not_infinitesimal`

English:
theorem InfinitePos.not_infinitesimal
  given: {x : Real*} (h : InfinitePos x)
  statement: ¬Infinitesimal x
  proof: Infinite.not_infinitesimal (Or.inl h)

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]

中文:
定理 InfinitePos.not_infinitesimal
  条件: {x : 实数*} (h : InfinitePos x)
  结论: ¬Infinitesimal x
  证明: Infinite.not_infinitesimal (Or.inl h)

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]

Depends on / 依赖: Infinite, Infinite.not_infinitesimal, Or.inl, not_infinitesimal
-/
theorem InfinitePos.not_infinitesimal {x : Real*} (h : InfinitePos x) : ¬Infinitesimal x :=
  Infinite.not_infinitesimal (Or.inl h)

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
/--
theorem `InfiniteNeg.not_infinitesimal` / 定理 `InfiniteNeg.not_infinitesimal`

English:
theorem InfiniteNeg.not_infinitesimal
  given: {x : Real*} (h : InfiniteNeg x)
  statement: ¬Infinitesimal x
  proof: Infinite.not_infinitesimal (Or.inr h)

@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]

中文:
定理 InfiniteNeg.not_infinitesimal
  条件: {x : 实数*} (h : InfiniteNeg x)
  结论: ¬Infinitesimal x
  证明: Infinite.not_infinitesimal (Or.inr h)

@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]

Depends on / 依赖: Infinite, Infinite.not_infinitesimal, Or.inr, not_infinitesimal
-/
theorem InfiniteNeg.not_infinitesimal {x : Real*} (h : InfiniteNeg x) : ¬Infinitesimal x :=
  Infinite.not_infinitesimal (Or.inr h)

@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]
/--
theorem `infinitePos_iff_infinite_and_pos` / 定理 `infinitePos_iff_infinite_and_pos`

English:
theorem infinitePos_iff_infinite_and_pos
  given: {x : Real*}
  statement: InfinitePos x ↔ Infinite x ∧ 0 < x
  proof: ⟨fun hip => ⟨Or.inl hip, hip 0⟩, fun ⟨hi, hp⟩ =>
    hi.casesOn id fun hin => False.elim (not_lt_of_gt hp (hin 0))⟩

@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]

中文:
定理 infinitePos_iff_infinite_and_pos
  条件: {x : 实数*}
  结论: InfinitePos x ↔ Infinite x ∧ 0 < x
  证明: ⟨fun hip => ⟨Or.inl hip, hip 0⟩, fun ⟨hi, hp⟩ =>
    hi.casesOn id fun hin => False.elim (not_lt_of_gt hp (hin 0))⟩

@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]

Depends on / 依赖: False.elim, Or.inl, casesOn, hi.casesOn, not_lt_of_gt
-/
theorem infinitePos_iff_infinite_and_pos {x : Real*} : InfinitePos x ↔ Infinite x ∧ 0 < x :=
  ⟨fun hip => ⟨Or.inl hip, hip 0⟩, fun ⟨hi, hp⟩ =>
    hi.casesOn id fun hin => False.elim (not_lt_of_gt hp (hin 0))⟩

@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]
/--
theorem `infiniteNeg_iff_infinite_and_neg` / 定理 `infiniteNeg_iff_infinite_and_neg`

English:
theorem infiniteNeg_iff_infinite_and_neg
  given: {x : Real*}
  statement: InfiniteNeg x ↔ Infinite x ∧ x < 0
  proof: ⟨fun hip => ⟨Or.inr hip, hip 0⟩, fun ⟨hi, hp⟩ =>
    hi.casesOn (fun hin => False.elim (not_lt_of_gt hp (hin 0))) fun hip => hip⟩

@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]

中文:
定理 infiniteNeg_iff_infinite_and_neg
  条件: {x : 实数*}
  结论: InfiniteNeg x ↔ Infinite x ∧ x < 0
  证明: ⟨fun hip => ⟨Or.inr hip, hip 0⟩, fun ⟨hi, hp⟩ =>
    hi.casesOn (fun hin => False.elim (not_lt_of_gt hp (hin 0))) fun hip => hip⟩

@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]

Depends on / 依赖: False.elim, Or.inr, casesOn, hi.casesOn, not_lt_of_gt
-/
theorem infiniteNeg_iff_infinite_and_neg {x : Real*} : InfiniteNeg x ↔ Infinite x ∧ x < 0 :=
  ⟨fun hip => ⟨Or.inr hip, hip 0⟩, fun ⟨hi, hp⟩ =>
    hi.casesOn (fun hin => False.elim (not_lt_of_gt hp (hin 0))) fun hip => hip⟩

@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]
/--
theorem `infinitePos_iff_infinite_of_nonneg` / 定理 `infinitePos_iff_infinite_of_nonneg`

English:
theorem infinitePos_iff_infinite_of_nonneg
  given: {x : Real*} (hp : 0 <= x)
  statement: InfinitePos x ↔ Infinite x
  proof: .symm or_iff_left fun h => h.lt_zero.not_ge hp

@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]

中文:
定理 infinitePos_iff_infinite_of_nonneg
  条件: {x : 实数*} (hp : 0 <= x)
  结论: InfinitePos x ↔ Infinite x
  证明: .symm or_iff_left fun h => h.lt_zero.not_ge hp

@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]

Depends on / 依赖: h.lt_zero.not_ge, lt_zero, not_ge, or_iff_left
-/
theorem infinitePos_iff_infinite_of_nonneg {x : Real*} (hp : 0 <= x) : InfinitePos x ↔ Infinite x :=
.symm or_iff_left fun h => h.lt_zero.not_ge hp

@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]
/--
theorem `infinitePos_iff_infinite_of_pos` / 定理 `infinitePos_iff_infinite_of_pos`

English:
theorem infinitePos_iff_infinite_of_pos
  given: {x : Real*} (hp : 0 < x)
  statement: InfinitePos x ↔ Infinite x
  proof: infinitePos_iff_infinite_of_nonneg hp.le

@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]

中文:
定理 infinitePos_iff_infinite_of_pos
  条件: {x : 实数*} (hp : 0 < x)
  结论: InfinitePos x ↔ Infinite x
  证明: infinitePos_iff_infinite_of_nonneg hp.le

@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]

Depends on / 依赖: hp.le, infinitePos_iff_infinite_of_nonneg
-/
theorem infinitePos_iff_infinite_of_pos {x : Real*} (hp : 0 < x) : InfinitePos x ↔ Infinite x :=
  infinitePos_iff_infinite_of_nonneg hp.le

@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]
/--
theorem `infiniteNeg_iff_infinite_of_neg` / 定理 `infiniteNeg_iff_infinite_of_neg`

English:
theorem infiniteNeg_iff_infinite_of_neg
  given: {x : Real*} (hn : x < 0)
  statement: InfiniteNeg x ↔ Infinite x
  proof: .symm or_iff_right fun h => h.pos.not_gt hn

@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]

中文:
定理 infiniteNeg_iff_infinite_of_neg
  条件: {x : 实数*} (hn : x < 0)
  结论: InfiniteNeg x ↔ Infinite x
  证明: .symm or_iff_right fun h => h.pos.not_gt hn

@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]

Depends on / 依赖: h.pos.not_gt, not_gt, or_iff_right
-/
theorem infiniteNeg_iff_infinite_of_neg {x : Real*} (hn : x < 0) : InfiniteNeg x ↔ Infinite x :=
.symm or_iff_right fun h => h.pos.not_gt hn

@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]
/--
theorem `infinitePos_abs_iff_infinite_abs` / 定理 `infinitePos_abs_iff_infinite_abs`

English:
theorem infinitePos_abs_iff_infinite_abs
  given: {x : Real*}
  statement: InfinitePos |x| ↔ Infinite |x|
  proof: infinitePos_iff_infinite_of_nonneg (abs_nonneg _)

@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]

中文:
定理 infinitePos_abs_iff_infinite_abs
  条件: {x : 实数*}
  结论: InfinitePos |x| ↔ Infinite |x|
  证明: infinitePos_iff_infinite_of_nonneg (abs_nonneg _)

@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]

Depends on / 依赖: abs_nonneg, infinitePos_iff_infinite_of_nonneg
-/
theorem infinitePos_abs_iff_infinite_abs {x : Real*} : InfinitePos |x| ↔ Infinite |x| :=
  infinitePos_iff_infinite_of_nonneg (abs_nonneg _)

@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]
/--
theorem `infinite_abs_iff` / 定理 `infinite_abs_iff`

English:
theorem infinite_abs_iff
  given: {x : Real*}
  statement: Infinite |x| ↔ Infinite x
  proof: by
  cases le_total 0 x <;> simp [*, abs_of_nonneg, abs_of_nonpos, infinite_neg]

@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]

中文:
定理 infinite_abs_iff
  条件: {x : 实数*}
  结论: Infinite |x| ↔ Infinite x
  证明: by
  cases le_total 0 x <;> simp [*, abs_of_nonneg, abs_of_nonpos, infinite_neg]

@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]

Depends on / 依赖: abs_of_nonneg, abs_of_nonpos, infinite_neg, le_total
-/
theorem infinite_abs_iff {x : Real*} : Infinite |x| ↔ Infinite x := by
  cases le_total 0 x <;> simp [*, abs_of_nonneg, abs_of_nonpos, infinite_neg]

@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]
/--
theorem `infinitePos_abs_iff_infinite` / 定理 `infinitePos_abs_iff_infinite`

English:
theorem infinitePos_abs_iff_infinite
  given: {x : Real*}
  statement: InfinitePos |x| ↔ Infinite x
  proof: infinitePos_abs_iff_infinite_abs.trans infinite_abs_iff

@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]

中文:
定理 infinitePos_abs_iff_infinite
  条件: {x : 实数*}
  结论: InfinitePos |x| ↔ Infinite x
  证明: infinitePos_abs_iff_infinite_abs.trans infinite_abs_iff

@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]

Depends on / 依赖: infinitePos_abs_iff_infinite_abs, infinitePos_abs_iff_infinite_abs.trans, infinite_abs_iff
-/
theorem infinitePos_abs_iff_infinite {x : Real*} : InfinitePos |x| ↔ Infinite x :=
  infinitePos_abs_iff_infinite_abs.trans infinite_abs_iff

@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]
/--
theorem `infinite_iff_abs_lt_abs` / 定理 `infinite_iff_abs_lt_abs`

English:
theorem infinite_iff_abs_lt_abs
  given: {x : Real*}
  statement: Infinite x ↔ forall r : Real, (|r| : Real*) < |x|
  proof: infinitePos_abs_iff_infinite.symm.trans ⟨fun hI r => coe_abs r ▸ hI |r|, fun hR r =>
    (le_abs_self _).trans_lt (hR r)⟩

@[deprecated "`InfinitePos` and `InfiniteNeg` are deprecated" (since := "2026-01-05")]

中文:
定理 infinite_iff_abs_lt_abs
  条件: {x : 实数*}
  结论: Infinite x ↔ 对任意 r : 实数, (|r| : 实数*) < |x|
  证明: infinitePos_abs_iff_infinite.symm.trans ⟨fun hI r => coe_abs r ▸ hI |r|, fun hR r =>
    (le_abs_self _).trans_lt (hR r)⟩

@[deprecated "`InfinitePos` and `InfiniteNeg` are deprecated" (since := "2026-01-05")]

Depends on / 依赖: coe_abs, infinitePos_abs_iff_infinite, infinitePos_abs_iff_infinite.symm.trans, le_abs_self, trans_lt
-/
theorem infinite_iff_abs_lt_abs {x : Real*} : Infinite x ↔ forall r : Real, (|r| : Real*) < |x| :=
  infinitePos_abs_iff_infinite.symm.trans ⟨fun hI r => coe_abs r ▸ hI |r|, fun hR r =>
    (le_abs_self _).trans_lt (hR r)⟩

@[deprecated "`InfinitePos` and `InfiniteNeg` are deprecated" (since := "2026-01-05")]
/--
theorem `infinitePos_add_not_infiniteNeg` / 定理 `infinitePos_add_not_infiniteNeg`

English:
theorem infinitePos_add_not_infiniteNeg
  given: {x y : Real*}
  proof: by
  intro hip hnin r
  obtain ⟨r₂, hr₂⟩ := not_forall.mp hnin
  convert! add_lt_add_of_lt_of_le (hip (r + -r₂)) (not_lt.mp hr₂) using 1
  simp

@[deprecated "`InfinitePos` and `InfiniteNeg` are deprecated" (since := "2026-01-05")]

中文:
定理 infinitePos_add_not_infiniteNeg
  条件: {x y : 实数*}
  证明: by
  intro hip hnin r
  obtain ⟨r₂, hr₂⟩ := not_forall.mp hnin
  convert! add_lt_add_of_lt_of_le (hip (r + -r₂)) (not_lt.mp hr₂) using 1
  simp

@[deprecated "`InfinitePos` and `InfiniteNeg` are deprecated" (since := "2026-01-05")]

Depends on / 依赖: add_lt_add_of_lt_of_le, convert, not_forall, not_forall.mp, not_lt, not_lt.mp
-/
theorem infinitePos_add_not_infiniteNeg {x y : Real*} :
    InfinitePos x -> ¬InfiniteNeg y -> InfinitePos (x + y) := by
  intro hip hnin r
  obtain ⟨r₂, hr₂⟩ := not_forall.mp hnin
  convert! add_lt_add_of_lt_of_le (hip (r + -r₂)) (not_lt.mp hr₂) using 1
  simp

@[deprecated "`InfinitePos` and `InfiniteNeg` are deprecated" (since := "2026-01-05")]
/--
theorem `not_infiniteNeg_add_infinitePos` / 定理 `not_infiniteNeg_add_infinitePos`

English:
theorem not_infiniteNeg_add_infinitePos
  given: {x y : Real*}
  proof: fun hx hy =>
  add_comm y x ▸ infinitePos_add_not_infiniteNeg hy hx

@[deprecated "`InfinitePos` and `InfiniteNeg` are deprecated" (since := "2026-01-05")]

中文:
定理 not_infiniteNeg_add_infinitePos
  条件: {x y : 实数*}
  证明: fun hx hy =>
  add_comm y x ▸ infinitePos_add_not_infiniteNeg hy hx

@[deprecated "`InfinitePos` and `InfiniteNeg` are deprecated" (since := "2026-01-05")]

Depends on / 依赖: NatIso, NatIso.op, isIso_hom
-/
theorem not_infiniteNeg_add_infinitePos {x y : Real*} :
    ¬InfiniteNeg x -> InfinitePos y -> InfinitePos (x + y) := fun hx hy =>
  add_comm y x ▸ infinitePos_add_not_infiniteNeg hy hx

@[deprecated "`InfinitePos` and `InfiniteNeg` are deprecated" (since := "2026-01-05")]
/--
theorem `infiniteNeg_add_not_infinitePos` / 定理 `infiniteNeg_add_not_infinitePos`

English:
theorem infiniteNeg_add_not_infinitePos
  given: {x y : Real*}
  proof: by
  rw [← infinitePos_neg]; rw [← infinitePos_neg]; rw [← @infiniteNeg_neg y]; rw [neg_add]
  exact infinitePos_add_not_infiniteNeg

@[deprecated "`InfinitePos` and `InfiniteNeg` are deprecated" (since := "2026-01-05")]

中文:
定理 infiniteNeg_add_not_infinitePos
  条件: {x y : 实数*}
  证明: by
  rw [← infinitePos_neg]; rw [← infinitePos_neg]; rw [← @infiniteNeg_neg y]; rw [neg_add]
  exact infinitePos_add_not_infiniteNeg

@[deprecated "`InfinitePos` and `InfiniteNeg` are deprecated" (since := "2026-01-05")]

Depends on / 依赖: infiniteNeg_neg, infinitePos_add_not_infiniteNeg, infinitePos_neg, neg_add
-/
theorem infiniteNeg_add_not_infinitePos {x y : Real*} :
    InfiniteNeg x -> ¬InfinitePos y -> InfiniteNeg (x + y) := by
  rw [← infinitePos_neg]; rw [← infinitePos_neg]; rw [← @infiniteNeg_neg y]; rw [neg_add]
  exact infinitePos_add_not_infiniteNeg

@[deprecated "`InfinitePos` and `InfiniteNeg` are deprecated" (since := "2026-01-05")]
/--
theorem `not_infinitePos_add_infiniteNeg` / 定理 `not_infinitePos_add_infiniteNeg`

English:
theorem not_infinitePos_add_infiniteNeg
  given: {x y : Real*}
  proof: fun hx hy =>
  add_comm y x ▸ infiniteNeg_add_not_infinitePos hy hx

@[deprecated "`InfinitePos` and `InfiniteNeg` are deprecated" (since := "2026-01-05")]

中文:
定理 not_infinitePos_add_infiniteNeg
  条件: {x y : 实数*}
  证明: fun hx hy =>
  add_comm y x ▸ infiniteNeg_add_not_infinitePos hy hx

@[deprecated "`InfinitePos` and `InfiniteNeg` are deprecated" (since := "2026-01-05")]
-/
theorem not_infinitePos_add_infiniteNeg {x y : Real*} :
    ¬InfinitePos x -> InfiniteNeg y -> InfiniteNeg (x + y) := fun hx hy =>
  add_comm y x ▸ infiniteNeg_add_not_infinitePos hy hx

@[deprecated "`InfinitePos` and `InfiniteNeg` are deprecated" (since := "2026-01-05")]
/--
theorem `infinitePos_add_infinitePos` / 定理 `infinitePos_add_infinitePos`

English:
theorem infinitePos_add_infinitePos
  given: {x y : Real*}
  proof: fun hx hy =>
  infinitePos_add_not_infiniteNeg hx hy.not_infiniteNeg

@[deprecated "`InfinitePos` and `InfiniteNeg` are deprecated" (since := "2026-01-05")]

中文:
定理 infinitePos_add_infinitePos
  条件: {x y : 实数*}
  证明: fun hx hy =>
  infinitePos_add_not_infiniteNeg hx hy.not_infiniteNeg

@[deprecated "`InfinitePos` and `InfiniteNeg` are deprecated" (since := "2026-01-05")]
-/
theorem infinitePos_add_infinitePos {x y : Real*} :
    InfinitePos x -> InfinitePos y -> InfinitePos (x + y) := fun hx hy =>
  infinitePos_add_not_infiniteNeg hx hy.not_infiniteNeg

@[deprecated "`InfinitePos` and `InfiniteNeg` are deprecated" (since := "2026-01-05")]
/--
theorem `infiniteNeg_add_infiniteNeg` / 定理 `infiniteNeg_add_infiniteNeg`

English:
theorem infiniteNeg_add_infiniteNeg
  given: {x y : Real*}
  proof: fun hx hy =>
  infiniteNeg_add_not_infinitePos hx hy.not_infinitePos

@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]

中文:
定理 infiniteNeg_add_infiniteNeg
  条件: {x y : 实数*}
  证明: fun hx hy =>
  infiniteNeg_add_not_infinitePos hx hy.not_infinitePos

@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]

Depends on / 依赖: opEquiv
-/
theorem infiniteNeg_add_infiniteNeg {x y : Real*} :
    InfiniteNeg x -> InfiniteNeg y -> InfiniteNeg (x + y) := fun hx hy =>
  infiniteNeg_add_not_infinitePos hx hy.not_infinitePos

@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]
/--
theorem `infinitePos_add_not_infinite` / 定理 `infinitePos_add_not_infinite`

English:
theorem infinitePos_add_not_infinite
  given: {x y : Real*}
  proof: fun hx hy =>
  infinitePos_add_not_infiniteNeg hx (not_or.mp hy).2

@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]

中文:
定理 infinitePos_add_not_infinite
  条件: {x y : 实数*}
  证明: fun hx hy =>
  infinitePos_add_not_infiniteNeg hx (not_or.mp hy).2

@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]

Depends on / 依赖: opEquiv
-/
theorem infinitePos_add_not_infinite {x y : Real*} :
    InfinitePos x -> ¬Infinite y -> InfinitePos (x + y) := fun hx hy =>
  infinitePos_add_not_infiniteNeg hx (not_or.mp hy).2

@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]
/--
theorem `infiniteNeg_add_not_infinite` / 定理 `infiniteNeg_add_not_infinite`

English:
theorem infiniteNeg_add_not_infinite
  given: {x y : Real*}
  proof: fun hx hy =>
  infiniteNeg_add_not_infinitePos hx (not_or.mp hy).1

@[deprecated "`InfinitePos` is deprecated" (since := "2026-01-05")]

中文:
定理 infiniteNeg_add_not_infinite
  条件: {x y : 实数*}
  证明: fun hx hy =>
  infiniteNeg_add_not_infinitePos hx (not_or.mp hy).1

@[deprecated "`InfinitePos` is deprecated" (since := "2026-01-05")]

Depends on / 依赖: opEquiv, to_dual
-/
theorem infiniteNeg_add_not_infinite {x y : Real*} :
    InfiniteNeg x -> ¬Infinite y -> InfiniteNeg (x + y) := fun hx hy =>
  infiniteNeg_add_not_infinitePos hx (not_or.mp hy).1

@[deprecated "`InfinitePos` is deprecated" (since := "2026-01-05")]
/--
theorem `infinitePos_of_tendsto_top` / 定理 `infinitePos_of_tendsto_top`

English:
theorem infinitePos_of_tendsto_top
  given: {f : Nat -> Real} (hf : Tendsto f atTop atTop)
  proof: by
  replace hf := hf.mono_left Nat.hyperfilter_le_atTop
  rw [infinitePos_iff]
  exact ⟨lt_of_tendsto_atTop 0 hf, archimedeanClassMk_neg_of_tendsto_atTop hf⟩

@[deprecated "`InfiniteNeg` is deprecated" (since := "2026-01-05")]

中文:
定理 infinitePos_of_tendsto_top
  条件: {f : 自然数 -> 实数} (hf : Tendsto f atTop atTop)
  证明: by
  replace hf := hf.mono_left Nat.hyperfilter_le_atTop
  rw [infinitePos_iff]
  exact ⟨lt_of_tendsto_atTop 0 hf, archimedeanClassMk_neg_of_tendsto_atTop hf⟩

@[deprecated "`InfiniteNeg` is deprecated" (since := "2026-01-05")]

Depends on / 依赖: Nat.hyperfilter_le_atTop, archimedeanClassMk_neg_of_tendsto_atTop, hf.mono_left, hyperfilter_le_atTop, infinitePos_iff, lt_of_tendsto_atTop, mono_left, replace
-/
theorem infinitePos_of_tendsto_top {f : Nat -> Real} (hf : Tendsto f atTop atTop) :
    InfinitePos (ofSeq f) := by
  replace hf := hf.mono_left Nat.hyperfilter_le_atTop
  rw [infinitePos_iff]
  exact ⟨lt_of_tendsto_atTop 0 hf, archimedeanClassMk_neg_of_tendsto_atTop hf⟩

@[deprecated "`InfiniteNeg` is deprecated" (since := "2026-01-05")]
/--
theorem `infiniteNeg_of_tendsto_bot` / 定理 `infiniteNeg_of_tendsto_bot`

English:
theorem infiniteNeg_of_tendsto_bot
  given: {f : Nat -> Real} (hf : Tendsto f atTop atBot)
  proof: by
  replace hf := hf.mono_left Nat.hyperfilter_le_atTop
  rw [infiniteNeg_iff]
  exact ⟨lt_of_tendsto_atBot 0 hf, archimedeanClassMk_neg_of_tendsto_atBot hf⟩

@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]

中文:
定理 infiniteNeg_of_tendsto_bot
  条件: {f : 自然数 -> 实数} (hf : Tendsto f atTop atBot)
  证明: by
  replace hf := hf.mono_left Nat.hyperfilter_le_atTop
  rw [infiniteNeg_iff]
  exact ⟨lt_of_tendsto_atBot 0 hf, archimedeanClassMk_neg_of_tendsto_atBot hf⟩

@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]

Depends on / 依赖: Nat.hyperfilter_le_atTop, archimedeanClassMk_neg_of_tendsto_atBot, hf.mono_left, hyperfilter_le_atTop, infiniteNeg_iff, lt_of_tendsto_atBot, mono_left, replace
-/
theorem infiniteNeg_of_tendsto_bot {f : Nat -> Real} (hf : Tendsto f atTop atBot) :
    InfiniteNeg (ofSeq f) := by
  replace hf := hf.mono_left Nat.hyperfilter_le_atTop
  rw [infiniteNeg_iff]
  exact ⟨lt_of_tendsto_atBot 0 hf, archimedeanClassMk_neg_of_tendsto_atBot hf⟩

@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]
/--
theorem `not_infinite_neg` / 定理 `not_infinite_neg`

English:
theorem not_infinite_neg
  given: {x : Real*}
  statement: ¬Infinite x -> ¬Infinite (-x)
  proof: mt infinite_neg.mp

@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]

中文:
定理 not_infinite_neg
  条件: {x : 实数*}
  结论: ¬Infinite x -> ¬Infinite (-x)
  证明: mt infinite_neg.mp

@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]

Depends on / 依赖: infinite_neg, infinite_neg.mp
-/
theorem not_infinite_neg {x : Real*} : ¬Infinite x -> ¬Infinite (-x) := mt infinite_neg.mp

@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]
/--
theorem `not_infinite_add` / 定理 `not_infinite_add`

English:
theorem not_infinite_add
  given: {x y : Real*} (hx : ¬Infinite x) (hy : ¬Infinite y)
  statement: ¬Infinite (x + y)
  proof: have ⟨r, hr⟩ := exists_st_of_not_infinite hx
  have ⟨s, hs⟩ := exists_st_of_not_infinite hy
not_infinite_of_exists_st ⟨r + s, hr.add hs⟩

@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]

中文:
定理 not_infinite_add
  条件: {x y : 实数*} (hx : ¬Infinite x) (hy : ¬Infinite y)
  结论: ¬Infinite (x + y)
  证明: have ⟨r, hr⟩ := exists_st_of_not_infinite hx
  have ⟨s, hs⟩ := exists_st_of_not_infinite hy
not_infinite_of_exists_st ⟨r + s, hr.add hs⟩

@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]

Depends on / 依赖: exists_st_of_not_infinite, hr.add, not_infinite_of_exists_st
-/
theorem not_infinite_add {x y : Real*} (hx : ¬Infinite x) (hy : ¬Infinite y) : ¬Infinite (x + y) :=
  have ⟨r, hr⟩ := exists_st_of_not_infinite hx
  have ⟨s, hs⟩ := exists_st_of_not_infinite hy
not_infinite_of_exists_st ⟨r + s, hr.add hs⟩

@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]
/--
theorem `not_infinite_iff_exist_lt_gt` / 定理 `not_infinite_iff_exist_lt_gt`

English:
theorem not_infinite_iff_exist_lt_gt
  given: {x : Real*}
  statement: ¬Infinite x ↔ exists r s : Real, (r : Real*) < x ∧ x < s
  proof: ⟨fun hni => let ⟨r, hr⟩ := exists_st_of_not_infinite hni; ⟨r - 1, r + 1, hr 1 one_pos⟩,
    fun ⟨r, s, hr, hs⟩ hi => hi.elim (fun hp => (hp s).not_gt hs) (fun hn => (hn r).not_gt hr)⟩

@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]

中文:
定理 not_infinite_iff_exist_lt_gt
  条件: {x : 实数*}
  结论: ¬Infinite x ↔ 存在 r s : 实数, (r : 实数*) < x ∧ x < s
  证明: ⟨fun hni => let ⟨r, hr⟩ := exists_st_of_not_infinite hni; ⟨r - 1, r + 1, hr 1 one_pos⟩,
    fun ⟨r, s, hr, hs⟩ hi => hi.elim (fun hp => (hp s).not_gt hs) (fun hn => (hn r).not_gt hr)⟩

@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]

Depends on / 依赖: exists_st_of_not_infinite, hi.elim, not_gt, one_pos
-/
theorem not_infinite_iff_exist_lt_gt {x : Real*} : ¬Infinite x ↔ exists r s : Real, (r : Real*) < x ∧ x < s :=
  ⟨fun hni => let ⟨r, hr⟩ := exists_st_of_not_infinite hni; ⟨r - 1, r + 1, hr 1 one_pos⟩,
    fun ⟨r, s, hr, hs⟩ hi => hi.elim (fun hp => (hp s).not_gt hs) (fun hn => (hn r).not_gt hr)⟩

@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]
/--
theorem `not_infinite_real` / 定理 `not_infinite_real`

English:
theorem not_infinite_real
  given: (r : Real)
  statement: ¬Infinite r
  proof: by
  rw [not_infinite_iff_exist_lt_gt]
exact ⟨r - 1, r + 1, coe_lt_coe.2 sub_one_lt r, coe_lt_coe.2 lt_add_one r⟩

@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]

中文:
定理 not_infinite_real
  条件: (r : 实数)
  结论: ¬Infinite r
  证明: by
  rw [not_infinite_iff_exist_lt_gt]
exact ⟨r - 1, r + 1, coe_lt_coe.2 sub_one_lt r, coe_lt_coe.2 lt_add_one r⟩

@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]

Depends on / 依赖: coe_lt_coe, lt_add_one, not_infinite_iff_exist_lt_gt, sub_one_lt
-/
theorem not_infinite_real (r : Real) : ¬Infinite r := by
  rw [not_infinite_iff_exist_lt_gt]
exact ⟨r - 1, r + 1, coe_lt_coe.2 sub_one_lt r, coe_lt_coe.2 lt_add_one r⟩

@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]
/--
theorem `Infinite.ne_real` / 定理 `Infinite.ne_real`

English:
theorem Infinite.ne_real
  given: {x : Real*}
  statement: Infinite x -> forall r : Real, x != r
  proof: fun hi r hr =>
not_infinite_real r @Eq.subst _ Infinite _ _ hr hi

中文:
定理 Infinite.ne_real
  条件: {x : 实数*}
  结论: Infinite x -> 对任意 r : 实数, x != r
  证明: fun hi r hr =>
not_infinite_real r @Eq.subst _ Infinite _ _ hr hi

Depends on / 依赖: F.objObjPreimageIso, X.unop, objObjPreimageIso, op.symm
-/
theorem Infinite.ne_real {x : Real*} : Infinite x -> forall r : Real, x != r := fun hi r hr =>
not_infinite_real r @Eq.subst _ Infinite _ _ hr hi

/-!
### Facts about `st` that require some infinite machinery
-/

@[deprecated stdPart_mul (since := "2026-01-05")]
/--
theorem `IsSt.mul` / 定理 `IsSt.mul`

English:
theorem IsSt.mul
  given: {x y : Real*} {r s : Real} (hxr : IsSt x r) (hys : IsSt y s)
  statement: IsSt (x * y) (r * s)
  proof: hxr.map₂ hys continuous_mul.continuousAt

@[deprecated mk_mul (since := "2026-01-05")]

中文:
定理 IsSt.mul
  条件: {x y : 实数*} {r s : 实数} (hxr : IsSt x r) (hys : IsSt y s)
  结论: IsSt (x * y) (r * s)
  证明: hxr.map₂ hys continuous_mul.continuousAt

@[deprecated mk_mul (since := "2026-01-05")]

Depends on / 依赖: F.objObjPreimageIso, X.unop, continuousAt, continuous_mul, continuous_mul.continuousAt, hxr.map, objObjPreimageIso, op.symm
-/
theorem IsSt.mul {x y : Real*} {r s : Real} (hxr : IsSt x r) (hys : IsSt y s) : IsSt (x * y) (r * s) :=
  hxr.map₂ hys continuous_mul.continuousAt

@[deprecated mk_mul (since := "2026-01-05")]
/--
theorem `not_infinite_mul` / 定理 `not_infinite_mul`

English:
theorem not_infinite_mul
  given: {x y : Real*} (hx : ¬Infinite x) (hy : ¬Infinite y)
  statement: ¬Infinite (x * y)
  proof: have ⟨_r, hr⟩ := exists_st_of_not_infinite hx
  have ⟨_s, hs⟩ := exists_st_of_not_infinite hy
  (hr.mul hs).not_infinite

@[deprecated stdPart_add (since := "2026-01-05")]

中文:
定理 not_infinite_mul
  条件: {x y : 实数*} (hx : ¬Infinite x) (hy : ¬Infinite y)
  结论: ¬Infinite (x * y)
  证明: have ⟨_r, hr⟩ := exists_st_of_not_infinite hx
  have ⟨_s, hs⟩ := exists_st_of_not_infinite hy
  (hr.mul hs).not_infinite

@[deprecated stdPart_add (since := "2026-01-05")]

Depends on / 依赖: F.objObjPreimageIso, exists_st_of_not_infinite, hr.mul, not_infinite, objObjPreimageIso, unop.symm
-/
theorem not_infinite_mul {x y : Real*} (hx : ¬Infinite x) (hy : ¬Infinite y) : ¬Infinite (x * y) :=
  have ⟨_r, hr⟩ := exists_st_of_not_infinite hx
  have ⟨_s, hs⟩ := exists_st_of_not_infinite hy
  (hr.mul hs).not_infinite

@[deprecated stdPart_add (since := "2026-01-05")]
/--
theorem `st_add` / 定理 `st_add`

English:
theorem st_add
  given: {x y : Real*} (hx : ¬Infinite x) (hy : ¬Infinite y)
  statement: st (x + y) = st x + st y
  proof: (isSt_st' (not_infinite_add hx hy)).unique ((isSt_st' hx).add (isSt_st' hy))

@[deprecated stdPart_neg (since := "2026-01-05")]

中文:
定理 st_add
  条件: {x y : 实数*} (hx : ¬Infinite x) (hy : ¬Infinite y)
  结论: st (x + y) = st x + st y
  证明: (isSt_st' (not_infinite_add hx hy)).unique ((isSt_st' hx).add (isSt_st' hy))

@[deprecated stdPart_neg (since := "2026-01-05")]

Depends on / 依赖: Discrete, Discrete.as, Function, Function.isEmpty, isEmpty, isSt_st, not_infinite_add, unique
-/
theorem st_add {x y : Real*} (hx : ¬Infinite x) (hy : ¬Infinite y) : st (x + y) = st x + st y :=
  (isSt_st' (not_infinite_add hx hy)).unique ((isSt_st' hx).add (isSt_st' hy))

@[deprecated stdPart_neg (since := "2026-01-05")]
/--
theorem `st_neg` / 定理 `st_neg`

English:
theorem st_neg
  given: (x : Real*)
  statement: st (-x) = -st x
  proof: by
  by_cases h : Infinite x
  · rw [h.st_eq, (infinite_neg.2 h).st_eq, neg_zero]
  · exact (isSt_st' (not_infinite_neg h)).unique (isSt_st' h).neg

@[deprecated stdPart_mul (since := "2026-01-05")]

中文:
定理 st_neg
  条件: (x : 实数*)
  结论: st (-x) = -st x
  证明: by
  by_cases h : Infinite x
  · rw [h.st_eq, (infinite_neg.2 h).st_eq, neg_zero]
  · exact (isSt_st' (not_infinite_neg h)).unique (isSt_st' h).neg

@[deprecated stdPart_mul (since := "2026-01-05")]

Depends on / 依赖: Infinite, h.st_eq, infinite_neg, isSt_st, neg_zero, not_infinite_neg, st_eq, unique
-/
theorem st_neg (x : Real*) : st (-x) = -st x := by
  by_cases h : Infinite x
  · rw [h.st_eq, (infinite_neg.2 h).st_eq, neg_zero]
  · exact (isSt_st' (not_infinite_neg h)).unique (isSt_st' h).neg

@[deprecated stdPart_mul (since := "2026-01-05")]
/--
theorem `st_mul` / 定理 `st_mul`

English:
theorem st_mul
  given: {x y : Real*} (hx : ¬Infinite x) (hy : ¬Infinite y)
  statement: st (x * y) = st x * st y
  proof: have hx' := isSt_st' hx
  have hy' := isSt_st' hy
  have hxy := isSt_st' (not_infinite_mul hx hy)
  hxy.unique (hx'.mul hy')

中文:
定理 st_mul
  条件: {x y : 实数*} (hx : ¬Infinite x) (hy : ¬Infinite y)
  结论: st (x * y) = st x * st y
  证明: have hx' := isSt_st' hx
  have hy' := isSt_st' hy
  have hxy := isSt_st' (not_infinite_mul hx hy)
  hxy.unique (hx'.mul hy')

Depends on / 依赖: hxy.unique, isSt_st, not_infinite_mul, unique
-/
theorem st_mul {x y : Real*} (hx : ¬Infinite x) (hy : ¬Infinite y) : st (x * y) = st x * st y :=
  have hx' := isSt_st' hx
  have hy' := isSt_st' hy
  have hxy := isSt_st' (not_infinite_mul hx hy)
  hxy.unique (hx'.mul hy')

/-!
### Basic lemmas about infinitesimal
-/

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
/--
theorem `infinitesimal_def` / 定理 `infinitesimal_def`

English:
theorem infinitesimal_def
  given: {x : Real*}
  statement: Infinitesimal x ↔ forall r : Real, 0 < r -> -(r : Real*) < x ∧ x < r
  proof: by
  simp [Infinitesimal, IsSt]

@[deprecated lt_of_pos_of_archimedean (since := "2026-01-05")]

中文:
定理 infinitesimal_def
  条件: {x : 实数*}
  结论: Infinitesimal x ↔ 对任意 r : 实数, 0 < r -> -(r : 实数*) < x ∧ x < r
  证明: by
  simp [Infinitesimal, IsSt]

@[deprecated lt_of_pos_of_archimedean (since := "2026-01-05")]

Depends on / 依赖: Infinitesimal
-/
theorem infinitesimal_def {x : Real*} : Infinitesimal x ↔ forall r : Real, 0 < r -> -(r : Real*) < x ∧ x < r := by
  simp [Infinitesimal, IsSt]

@[deprecated lt_of_pos_of_archimedean (since := "2026-01-05")]
/--
theorem `lt_of_pos_of_infinitesimal` / 定理 `lt_of_pos_of_infinitesimal`

English:
theorem lt_of_pos_of_infinitesimal
  given: {x : Real*}
  statement: Infinitesimal x -> forall r : Real, 0 < r -> x < r
  proof: fun hi r hr => ((infinitesimal_def.mp hi) r hr).2

@[deprecated lt_of_neg_of_archimedean (since := "2026-01-05")]

中文:
定理 lt_of_pos_of_infinitesimal
  条件: {x : 实数*}
  结论: Infinitesimal x -> 对任意 r : 实数, 0 < r -> x < r
  证明: fun hi r hr => ((infinitesimal_def.mp hi) r hr).2

@[deprecated lt_of_neg_of_archimedean (since := "2026-01-05")]

Depends on / 依赖: infinitesimal_def, infinitesimal_def.mp
-/
theorem lt_of_pos_of_infinitesimal {x : Real*} : Infinitesimal x -> forall r : Real, 0 < r -> x < r :=
  fun hi r hr => ((infinitesimal_def.mp hi) r hr).2

@[deprecated lt_of_neg_of_archimedean (since := "2026-01-05")]
/--
theorem `lt_neg_of_pos_of_infinitesimal` / 定理 `lt_neg_of_pos_of_infinitesimal`

English:
theorem lt_neg_of_pos_of_infinitesimal
  given: {x : Real*}
  statement: Infinitesimal x -> forall r : Real, 0 < r -> -↑r < x
  proof: fun hi r hr => ((infinitesimal_def.mp hi) r hr).1

@[deprecated lt_of_neg_of_archimedean (since := "2026-01-05")]

中文:
定理 lt_neg_of_pos_of_infinitesimal
  条件: {x : 实数*}
  结论: Infinitesimal x -> 对任意 r : 实数, 0 < r -> -↑r < x
  证明: fun hi r hr => ((infinitesimal_def.mp hi) r hr).1

@[deprecated lt_of_neg_of_archimedean (since := "2026-01-05")]

Depends on / 依赖: infinitesimal_def, infinitesimal_def.mp
-/
theorem lt_neg_of_pos_of_infinitesimal {x : Real*} : Infinitesimal x -> forall r : Real, 0 < r -> -↑r < x :=
  fun hi r hr => ((infinitesimal_def.mp hi) r hr).1

@[deprecated lt_of_neg_of_archimedean (since := "2026-01-05")]
/--
theorem `gt_of_neg_of_infinitesimal` / 定理 `gt_of_neg_of_infinitesimal`

English:
theorem gt_of_neg_of_infinitesimal
  given: {x : Real*} (hi : Infinitesimal x) (r : Real) (hr : r < 0)
  statement: ↑r < x
  proof: neg_neg r ▸ (infinitesimal_def.1 hi (-r) (neg_pos.2 hr)).1

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]

中文:
定理 gt_of_neg_of_infinitesimal
  条件: {x : 实数*} (hi : Infinitesimal x) (r : 实数) (hr : r < 0)
  结论: ↑r < x
  证明: neg_neg r ▸ (infinitesimal_def.1 hi (-r) (neg_pos.2 hr)).1

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]

Depends on / 依赖: infinitesimal_def, neg_neg, neg_pos
-/
theorem gt_of_neg_of_infinitesimal {x : Real*} (hi : Infinitesimal x) (r : Real) (hr : r < 0) : ↑r < x :=
  neg_neg r ▸ (infinitesimal_def.1 hi (-r) (neg_pos.2 hr)).1

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
/--
theorem `abs_lt_real_iff_infinitesimal` / 定理 `abs_lt_real_iff_infinitesimal`

English:
theorem abs_lt_real_iff_infinitesimal
  given: {x : Real*}
  statement: Infinitesimal x ↔ forall r : Real, r != 0 -> |x| < |↑r|
  proof: ⟨fun hi r hr => abs_lt.mpr (coe_abs r ▸ infinitesimal_def.mp hi |r| (abs_pos.2 hr)), fun hR =>
infinitesimal_def.mpr fun r hr => abs_lt.mp (abs_of_pos <| coe_pos.2 hr) ▸ hR r hr.ne'⟩

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]

中文:
定理 abs_lt_real_iff_infinitesimal
  条件: {x : 实数*}
  结论: Infinitesimal x ↔ 对任意 r : 实数, r != 0 -> |x| < |↑r|
  证明: ⟨fun hi r hr => abs_lt.mpr (coe_abs r ▸ infinitesimal_def.mp hi |r| (abs_pos.2 hr)), fun hR =>
infinitesimal_def.mpr fun r hr => abs_lt.mp (abs_of_pos <| coe_pos.2 hr) ▸ hR r hr.ne'⟩

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]

Depends on / 依赖: abs_lt, abs_lt.mp, abs_lt.mpr, abs_of_pos, abs_pos, coe_abs, coe_pos, hr.ne, infinitesimal_def, infinitesimal_def.mp, infinitesimal_def.mpr
-/
theorem abs_lt_real_iff_infinitesimal {x : Real*} : Infinitesimal x ↔ forall r : Real, r != 0 -> |x| < |↑r| :=
  ⟨fun hi r hr => abs_lt.mpr (coe_abs r ▸ infinitesimal_def.mp hi |r| (abs_pos.2 hr)), fun hR =>
infinitesimal_def.mpr fun r hr => abs_lt.mp (abs_of_pos <| coe_pos.2 hr) ▸ hR r hr.ne'⟩

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
/--
theorem `infinitesimal_zero` / 定理 `infinitesimal_zero`

English:
theorem infinitesimal_zero
  statement: Infinitesimal 0
  proof: isSt_refl_real 0

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]

中文:
定理 infinitesimal_zero
  结论: Infinitesimal 0
  证明: isSt_refl_real 0

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]

Depends on / 依赖: isSt_refl_real
-/
theorem infinitesimal_zero : Infinitesimal 0 := isSt_refl_real 0

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
/--
theorem `Infinitesimal.eq_zero` / 定理 `Infinitesimal.eq_zero`

English:
theorem Infinitesimal.eq_zero
  given: {r : Real}
  statement: Infinitesimal r -> r = 0
  proof: eq_of_isSt_real

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]

中文:
定理 Infinitesimal.eq_zero
  条件: {r : 实数}
  结论: Infinitesimal r -> r = 0
  证明: eq_of_isSt_real

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]

Depends on / 依赖: eq_of_isSt_real
-/
theorem Infinitesimal.eq_zero {r : Real} : Infinitesimal r -> r = 0 := eq_of_isSt_real

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
/--
theorem `infinitesimal_real_iff` / 定理 `infinitesimal_real_iff`

English:
theorem infinitesimal_real_iff
  given: {r : Real}
  statement: Infinitesimal r ↔ r = 0
  proof: isSt_real_iff_eq

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
nonrec theorem Infinitesimal.add {x y : Real*} (hx : Infinitesimal x) (hy : Infinitesimal y) :
    Infinitesimal (x + y) := by simpa only [add_zero] using! hx.add hy

@[deprecated "`Infinitesimal` is deprecated" 

中文:
定理 infinitesimal_real_iff
  条件: {r : 实数}
  结论: Infinitesimal r ↔ r = 0
  证明: isSt_real_iff_eq

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
nonrec theorem Infinitesimal.add {x y : Real*} (hx : Infinitesimal x) (hy : Infinitesimal y) :
    Infinitesimal (x + y) := by simpa only [add_zero] using! hx.add hy

@[deprecated "`Infinitesimal` is deprecated" 

Depends on / 依赖: isSt_real_iff_eq
-/
theorem infinitesimal_real_iff {r : Real} : Infinitesimal r ↔ r = 0 :=
  isSt_real_iff_eq

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
nonrec theorem Infinitesimal.add {x y : Real*} (hx : Infinitesimal x) (hy : Infinitesimal y) :
    Infinitesimal (x + y) := by simpa only [add_zero] using! hx.add hy

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
nonrec theorem Infinitesimal.neg {x : Real*} (hx : Infinitesimal x) : Infinitesimal (-x) := by
  simpa only [neg_zero] using! hx.neg

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
/--
theorem `infinitesimal_neg` / 定理 `infinitesimal_neg`

English:
theorem infinitesimal_neg
  given: {x : Real*}
  statement: Infinitesimal (-x) ↔ Infinitesimal x
  proof: ⟨fun h => neg_neg x ▸ h.neg, Infinitesimal.neg⟩

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
nonrec theorem Infinitesimal.mul {x y : Real*} (hx : Infinitesimal x) (hy : Infinitesimal y) :
    Infinitesimal (x * y) := by simpa only [mul_zero] using! hx.mul hy

@[deprecated "

中文:
定理 infinitesimal_neg
  条件: {x : 实数*}
  结论: Infinitesimal (-x) ↔ Infinitesimal x
  证明: ⟨fun h => neg_neg x ▸ h.neg, Infinitesimal.neg⟩

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
nonrec theorem Infinitesimal.mul {x y : Real*} (hx : Infinitesimal x) (hy : Infinitesimal y) :
    Infinitesimal (x * y) := by simpa only [mul_zero] using! hx.mul hy

@[deprecated "

Depends on / 依赖: Infinitesimal, Infinitesimal.neg, h.neg, neg_neg
-/
theorem infinitesimal_neg {x : Real*} : Infinitesimal (-x) ↔ Infinitesimal x :=
  ⟨fun h => neg_neg x ▸ h.neg, Infinitesimal.neg⟩

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
nonrec theorem Infinitesimal.mul {x y : Real*} (hx : Infinitesimal x) (hy : Infinitesimal y) :
    Infinitesimal (x * y) := by simpa only [mul_zero] using! hx.mul hy

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
/--
theorem `infinitesimal_of_tendsto_zero` / 定理 `infinitesimal_of_tendsto_zero`

English:
theorem infinitesimal_of_tendsto_zero
  given: {f : Nat -> Real} (h : Tendsto f atTop (𝓝 0))
  proof: isSt_of_tendsto h

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]

中文:
定理 infinitesimal_of_tendsto_zero
  条件: {f : 自然数 -> 实数} (h : Tendsto f atTop (𝓝 0))
  证明: isSt_of_tendsto h

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]

Depends on / 依赖: isSt_of_tendsto
-/
theorem infinitesimal_of_tendsto_zero {f : Nat -> Real} (h : Tendsto f atTop (𝓝 0)) :
    Infinitesimal (ofSeq f) :=
  isSt_of_tendsto h

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
/--
theorem `infinitesimal_epsilon` / 定理 `infinitesimal_epsilon`

English:
theorem infinitesimal_epsilon
  statement: Infinitesimal ε
  proof: infinitesimal_of_tendsto_zero tendsto_inv_atTop_nhds_zero_nat

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]

中文:
定理 infinitesimal_epsilon
  结论: Infinitesimal ε
  证明: infinitesimal_of_tendsto_zero tendsto_inv_atTop_nhds_zero_nat

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]

Depends on / 依赖: infinitesimal_of_tendsto_zero, tendsto_inv_atTop_nhds_zero_nat
-/
theorem infinitesimal_epsilon : Infinitesimal ε :=
  infinitesimal_of_tendsto_zero tendsto_inv_atTop_nhds_zero_nat

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
/--
theorem `not_real_of_infinitesimal_ne_zero` / 定理 `not_real_of_infinitesimal_ne_zero`

English:
theorem not_real_of_infinitesimal_ne_zero
  given: (x : Real*)
  statement: Infinitesimal x -> x != 0 -> forall r : Real, x != r
  proof: fun hi hx r hr =>
hx hr.trans coe_eq_zero.2 IsSt.unique (hr.symm ▸ isSt_refl_real r : IsSt x r) hi

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]

中文:
定理 not_real_of_infinitesimal_ne_zero
  条件: (x : 实数*)
  结论: Infinitesimal x -> x != 0 -> 对任意 r : 实数, x != r
  证明: fun hi hx r hr =>
hx hr.trans coe_eq_zero.2 IsSt.unique (hr.symm ▸ isSt_refl_real r : IsSt x r) hi

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]

Depends on / 依赖: IsSt.unique, coe_eq_zero, hr.symm, hr.trans, isSt_refl_real, unique
-/
theorem not_real_of_infinitesimal_ne_zero (x : Real*) : Infinitesimal x -> x != 0 -> forall r : Real, x != r :=
  fun hi hx r hr =>
hx hr.trans coe_eq_zero.2 IsSt.unique (hr.symm ▸ isSt_refl_real r : IsSt x r) hi

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
/--
theorem `IsSt.infinitesimal_sub` / 定理 `IsSt.infinitesimal_sub`

English:
theorem IsSt.infinitesimal_sub
  given: {x : Real*} {r : Real} (hxr : IsSt x r)
  statement: Infinitesimal (x - ↑r)
  proof: by
  simpa only [sub_self] using! hxr.sub (isSt_refl_real r)

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]

中文:
定理 IsSt.infinitesimal_sub
  条件: {x : 实数*} {r : 实数} (hxr : IsSt x r)
  结论: Infinitesimal (x - ↑r)
  证明: by
  simpa only [sub_self] using! hxr.sub (isSt_refl_real r)

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]

Depends on / 依赖: hxr.sub, isSt_refl_real, sub_self
-/
theorem IsSt.infinitesimal_sub {x : Real*} {r : Real} (hxr : IsSt x r) : Infinitesimal (x - ↑r) := by
  simpa only [sub_self] using! hxr.sub (isSt_refl_real r)

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
/--
theorem `infinitesimal_sub_st` / 定理 `infinitesimal_sub_st`

English:
theorem infinitesimal_sub_st
  given: {x : Real*} (hx : ¬Infinite x)
  statement: Infinitesimal (x - ↑(st x))
  proof: (isSt_st' hx).infinitesimal_sub

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]

中文:
定理 infinitesimal_sub_st
  条件: {x : 实数*} (hx : ¬Infinite x)
  结论: Infinitesimal (x - ↑(st x))
  证明: (isSt_st' hx).infinitesimal_sub

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]

Depends on / 依赖: infinitesimal_sub, isSt_st
-/
theorem infinitesimal_sub_st {x : Real*} (hx : ¬Infinite x) : Infinitesimal (x - ↑(st x)) :=
  (isSt_st' hx).infinitesimal_sub

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
/--
theorem `infinitePos_iff_infinitesimal_inv_pos` / 定理 `infinitePos_iff_infinitesimal_inv_pos`

English:
theorem infinitePos_iff_infinitesimal_inv_pos
  given: {x : Real*}
  proof: by
  rw [infinitePos_iff]; rw [infinitesimal_iff]
  aesop

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]

中文:
定理 infinitePos_iff_infinitesimal_inv_pos
  条件: {x : 实数*}
  证明: by
  rw [infinitePos_iff]; rw [infinitesimal_iff]
  aesop

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]

Depends on / 依赖: infinitePos_iff, infinitesimal_iff
-/
theorem infinitePos_iff_infinitesimal_inv_pos {x : Real*} :
    InfinitePos x ↔ Infinitesimal x⁻¹ ∧ 0 < x⁻¹ := by
  rw [infinitePos_iff]; rw [infinitesimal_iff]
  aesop

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
/--
theorem `infiniteNeg_iff_infinitesimal_inv_neg` / 定理 `infiniteNeg_iff_infinitesimal_inv_neg`

English:
theorem infiniteNeg_iff_infinitesimal_inv_neg
  given: {x : Real*}
  proof: by
  rw [← infinitePos_neg]; rw [infinitePos_iff_infinitesimal_inv_pos]; rw [inv_neg]; rw [neg_pos]; rw [infinitesimal_neg]

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]

中文:
定理 infiniteNeg_iff_infinitesimal_inv_neg
  条件: {x : 实数*}
  证明: by
  rw [← infinitePos_neg]; rw [infinitePos_iff_infinitesimal_inv_pos]; rw [inv_neg]; rw [neg_pos]; rw [infinitesimal_neg]

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]

Depends on / 依赖: infinitePos_iff_infinitesimal_inv_pos, infinitePos_neg, infinitesimal_neg, inv_neg, neg_pos
-/
theorem infiniteNeg_iff_infinitesimal_inv_neg {x : Real*} :
    InfiniteNeg x ↔ Infinitesimal x⁻¹ ∧ x⁻¹ < 0 := by
  rw [← infinitePos_neg]; rw [infinitePos_iff_infinitesimal_inv_pos]; rw [inv_neg]; rw [neg_pos]; rw [infinitesimal_neg]

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
/--
theorem `infinitesimal_inv_of_infinite` / 定理 `infinitesimal_inv_of_infinite`

English:
theorem infinitesimal_inv_of_infinite
  given: {x : Real*}
  statement: Infinite x -> Infinitesimal x⁻¹
  proof: fun hi =>
  Or.casesOn hi (fun hip => (infinitePos_iff_infinitesimal_inv_pos.mp hip).1) fun hin =>
    (infiniteNeg_iff_infinitesimal_inv_neg.mp hin).1

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]

中文:
定理 infinitesimal_inv_of_infinite
  条件: {x : 实数*}
  结论: Infinite x -> Infinitesimal x⁻¹
  证明: fun hi =>
  Or.casesOn hi (fun hip => (infinitePos_iff_infinitesimal_inv_pos.mp hip).1) fun hin =>
    (infiniteNeg_iff_infinitesimal_inv_neg.mp hin).1

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
-/
theorem infinitesimal_inv_of_infinite {x : Real*} : Infinite x -> Infinitesimal x⁻¹ := fun hi =>
  Or.casesOn hi (fun hip => (infinitePos_iff_infinitesimal_inv_pos.mp hip).1) fun hin =>
    (infiniteNeg_iff_infinitesimal_inv_neg.mp hin).1

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
/--
theorem `infinite_of_infinitesimal_inv` / 定理 `infinite_of_infinitesimal_inv`

English:
theorem infinite_of_infinitesimal_inv
  given: {x : Real*} (h0 : x != 0) (hi : Infinitesimal x⁻¹)
  proof: by
  rcases lt_or_gt_of_ne h0 with hn | hp
  · exact Or.inr (infiniteNeg_iff_infinitesimal_inv_neg.mpr ⟨hi, inv_lt_zero.mpr hn⟩)
  · exact Or.inl (infinitePos_iff_infinitesimal_inv_pos.mpr ⟨hi, inv_pos.mpr hp⟩)

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]

中文:
定理 infinite_of_infinitesimal_inv
  条件: {x : 实数*} (h0 : x != 0) (hi : Infinitesimal x⁻¹)
  证明: by
  rcases lt_or_gt_of_ne h0 with hn | hp
  · exact Or.inr (infiniteNeg_iff_infinitesimal_inv_neg.mpr ⟨hi, inv_lt_zero.mpr hn⟩)
  · exact Or.inl (infinitePos_iff_infinitesimal_inv_pos.mpr ⟨hi, inv_pos.mpr hp⟩)

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]

Depends on / 依赖: Or.inl, Or.inr, infiniteNeg_iff_infinitesimal_inv_neg, infiniteNeg_iff_infinitesimal_inv_neg.mpr, infinitePos_iff_infinitesimal_inv_pos, infinitePos_iff_infinitesimal_inv_pos.mpr, inv_lt_zero, inv_lt_zero.mpr, inv_pos, inv_pos.mpr, lt_or_gt_of_ne
-/
theorem infinite_of_infinitesimal_inv {x : Real*} (h0 : x != 0) (hi : Infinitesimal x⁻¹) :
    Infinite x := by
  rcases lt_or_gt_of_ne h0 with hn | hp
  · exact Or.inr (infiniteNeg_iff_infinitesimal_inv_neg.mpr ⟨hi, inv_lt_zero.mpr hn⟩)
  · exact Or.inl (infinitePos_iff_infinitesimal_inv_pos.mpr ⟨hi, inv_pos.mpr hp⟩)

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
/--
theorem `infinite_iff_infinitesimal_inv` / 定理 `infinite_iff_infinitesimal_inv`

English:
theorem infinite_iff_infinitesimal_inv
  given: {x : Real*} (h0 : x != 0)
  statement: Infinite x ↔ Infinitesimal x⁻¹
  proof: ⟨infinitesimal_inv_of_infinite, infinite_of_infinitesimal_inv h0⟩

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]

中文:
定理 infinite_iff_infinitesimal_inv
  条件: {x : 实数*} (h0 : x != 0)
  结论: Infinite x ↔ Infinitesimal x⁻¹
  证明: ⟨infinitesimal_inv_of_infinite, infinite_of_infinitesimal_inv h0⟩

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]

Depends on / 依赖: infinite_of_infinitesimal_inv, infinitesimal_inv_of_infinite
-/
theorem infinite_iff_infinitesimal_inv {x : Real*} (h0 : x != 0) : Infinite x ↔ Infinitesimal x⁻¹ :=
  ⟨infinitesimal_inv_of_infinite, infinite_of_infinitesimal_inv h0⟩

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
/--
theorem `infinitesimal_pos_iff_infinitePos_inv` / 定理 `infinitesimal_pos_iff_infinitePos_inv`

English:
theorem infinitesimal_pos_iff_infinitePos_inv
  given: {x : Real*}
  proof: infinitePos_iff_infinitesimal_inv_pos.trans by rw [inv_inv]

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]

中文:
定理 infinitesimal_pos_iff_infinitePos_inv
  条件: {x : 实数*}
  证明: infinitePos_iff_infinitesimal_inv_pos.trans by rw [inv_inv]

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]

Depends on / 依赖: infinitePos_iff_infinitesimal_inv_pos, infinitePos_iff_infinitesimal_inv_pos.trans, inv_inv
-/
theorem infinitesimal_pos_iff_infinitePos_inv {x : Real*} :
    InfinitePos x⁻¹ ↔ Infinitesimal x ∧ 0 < x :=
infinitePos_iff_infinitesimal_inv_pos.trans by rw [inv_inv]

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
/--
theorem `infinitesimal_neg_iff_infiniteNeg_inv` / 定理 `infinitesimal_neg_iff_infiniteNeg_inv`

English:
theorem infinitesimal_neg_iff_infiniteNeg_inv
  given: {x : Real*}
  proof: infiniteNeg_iff_infinitesimal_inv_neg.trans by rw [inv_inv]

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]

中文:
定理 infinitesimal_neg_iff_infiniteNeg_inv
  条件: {x : 实数*}
  证明: infiniteNeg_iff_infinitesimal_inv_neg.trans by rw [inv_inv]

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]

Depends on / 依赖: infiniteNeg_iff_infinitesimal_inv_neg, infiniteNeg_iff_infinitesimal_inv_neg.trans, inv_inv
-/
theorem infinitesimal_neg_iff_infiniteNeg_inv {x : Real*} :
    InfiniteNeg x⁻¹ ↔ Infinitesimal x ∧ x < 0 :=
infiniteNeg_iff_infinitesimal_inv_neg.trans by rw [inv_inv]

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
/--
theorem `infinitesimal_iff_infinite_inv` / 定理 `infinitesimal_iff_infinite_inv`

English:
theorem infinitesimal_iff_infinite_inv
  given: {x : Real*} (h : x != 0)
  statement: Infinitesimal x ↔ Infinite x⁻¹
  proof: Iff.trans (by rw [inv_inv]) (infinite_iff_infinitesimal_inv (inv_ne_zero h)).symm

@[deprecated stdPart_inv (since := "2026-01-05")]

中文:
定理 infinitesimal_iff_infinite_inv
  条件: {x : 实数*} (h : x != 0)
  结论: Infinitesimal x ↔ Infinite x⁻¹
  证明: Iff.trans (by rw [inv_inv]) (infinite_iff_infinitesimal_inv (inv_ne_zero h)).symm

@[deprecated stdPart_inv (since := "2026-01-05")]

Depends on / 依赖: Iff.trans, infinite_iff_infinitesimal_inv, inv_inv, inv_ne_zero
-/
theorem infinitesimal_iff_infinite_inv {x : Real*} (h : x != 0) : Infinitesimal x ↔ Infinite x⁻¹ :=
  Iff.trans (by rw [inv_inv]) (infinite_iff_infinitesimal_inv (inv_ne_zero h)).symm

@[deprecated stdPart_inv (since := "2026-01-05")]
/--
theorem `IsSt.inv` / 定理 `IsSt.inv`

English:
theorem IsSt.inv
  given: {x : Real*} {r : Real} (hi : ¬Infinitesimal x) (hr : IsSt x r)
  statement: IsSt x⁻¹ r⁻¹
  proof: hr.map continuousAt_inv₀ by rintro rfl; exact hi hr

@[deprecated stdPart_inv (since := "2026-01-05")]

中文:
定理 IsSt.inv
  条件: {x : 实数*} {r : 实数} (hi : ¬Infinitesimal x) (hr : IsSt x r)
  结论: IsSt x⁻¹ r⁻¹
  证明: hr.map continuousAt_inv₀ by rintro rfl; exact hi hr

@[deprecated stdPart_inv (since := "2026-01-05")]

Depends on / 依赖: hr.map
-/
theorem IsSt.inv {x : Real*} {r : Real} (hi : ¬Infinitesimal x) (hr : IsSt x r) : IsSt x⁻¹ r⁻¹ :=
hr.map continuousAt_inv₀ by rintro rfl; exact hi hr

@[deprecated stdPart_inv (since := "2026-01-05")]
/--
theorem `st_inv` / 定理 `st_inv`

English:
theorem st_inv
  given: (x : Real*)
  statement: st x⁻¹ = (st x)⁻¹
  proof: by
  simp [st_eq]

@[deprecated archimedeanClassMk_omega_neg (since := "2026-01-05")]

中文:
定理 st_inv
  条件: (x : 实数*)
  结论: st x⁻¹ = (st x)⁻¹
  证明: by
  simp [st_eq]

@[deprecated archimedeanClassMk_omega_neg (since := "2026-01-05")]

Depends on / 依赖: Quot.mk, a.as, st_eq
-/
theorem st_inv (x : Real*) : st x⁻¹ = (st x)⁻¹ := by
  simp [st_eq]

@[deprecated archimedeanClassMk_omega_neg (since := "2026-01-05")]
/--
theorem `infinitePos_omega` / 定理 `infinitePos_omega`

English:
theorem infinitePos_omega
  statement: InfinitePos ω
  proof: infinitePos_iff_infinitesimal_inv_pos.mpr ⟨infinitesimal_epsilon, epsilon_pos⟩

@[deprecated archimedeanClassMk_omega_neg (since := "2026-01-05")]

中文:
定理 infinitePos_omega
  结论: InfinitePos ω
  证明: infinitePos_iff_infinitesimal_inv_pos.mpr ⟨infinitesimal_epsilon, epsilon_pos⟩

@[deprecated archimedeanClassMk_omega_neg (since := "2026-01-05")]

Depends on / 依赖: epsilon_pos, infinitePos_iff_infinitesimal_inv_pos, infinitePos_iff_infinitesimal_inv_pos.mpr, infinitesimal_epsilon
-/
theorem infinitePos_omega : InfinitePos ω :=
  infinitePos_iff_infinitesimal_inv_pos.mpr ⟨infinitesimal_epsilon, epsilon_pos⟩

@[deprecated archimedeanClassMk_omega_neg (since := "2026-01-05")]
/--
theorem `infinite_omega` / 定理 `infinite_omega`

English:
theorem infinite_omega
  statement: Infinite ω
  proof: (infinite_iff_infinitesimal_inv omega_ne_zero).mpr infinitesimal_epsilon

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]

中文:
定理 infinite_omega
  结论: Infinite ω
  证明: (infinite_iff_infinitesimal_inv omega_ne_zero).mpr infinitesimal_epsilon

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]

Depends on / 依赖: infinite_iff_infinitesimal_inv, infinitesimal_epsilon, omega_ne_zero
-/
theorem infinite_omega : Infinite ω :=
  (infinite_iff_infinitesimal_inv omega_ne_zero).mpr infinitesimal_epsilon

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
/--
theorem `infinitePos_mul_of_infinitePos_not_infinitesimal_pos` / 定理 `infinitePos_mul_of_infinitePos_not_infinitesimal_pos`

English:
theorem infinitePos_mul_of_infinitePos_not_infinitesimal_pos
  given: {x y : Real*}
  proof: fun hx hy₁ hy₂ r => by
  have hy₁' := not_forall.mp (mt infinitesimal_def.2 hy₁)
  let ⟨r₁, hy₁''⟩ := hy₁'
  have hyr : 0 < r₁ ∧ ↑r₁ <= y := by
    rwa [Classical.not_imp, ← abs_lt, not_lt, abs_of_pos hy₂] at hy₁''
  rw [← div_mul_cancel₀ r (ne_of_gt hyr.1)]; rw [coe_mul]
  exact mul_lt_mul (hx (r /

中文:
定理 infinitePos_mul_of_infinitePos_not_infinitesimal_pos
  条件: {x y : 实数*}
  证明: fun hx hy₁ hy₂ r => by
  have hy₁' := not_forall.mp (mt infinitesimal_def.2 hy₁)
  let ⟨r₁, hy₁''⟩ := hy₁'
  have hyr : 0 < r₁ ∧ ↑r₁ <= y := by
    rwa [Classical.not_imp, ← abs_lt, not_lt, abs_of_pos hy₂] at hy₁''
  rw [← div_mul_cancel₀ r (ne_of_gt hyr.1)]; rw [coe_mul]
  exact mul_lt_mul (hx (r /

Depends on / 依赖: Classical, Classical.not_imp, abs_lt, abs_of_pos, coe_lt_coe, coe_mul, infinitesimal_def, le_of_lt, mul_lt_mul, ne_of_gt, not_forall, not_forall.mp, not_imp, not_lt
-/
theorem infinitePos_mul_of_infinitePos_not_infinitesimal_pos {x y : Real*} :
    InfinitePos x -> ¬Infinitesimal y -> 0 < y -> InfinitePos (x * y) := fun hx hy₁ hy₂ r => by
  have hy₁' := not_forall.mp (mt infinitesimal_def.2 hy₁)
  let ⟨r₁, hy₁''⟩ := hy₁'
  have hyr : 0 < r₁ ∧ ↑r₁ <= y := by
    rwa [Classical.not_imp, ← abs_lt, not_lt, abs_of_pos hy₂] at hy₁''
  rw [← div_mul_cancel₀ r (ne_of_gt hyr.1)]; rw [coe_mul]
  exact mul_lt_mul (hx (r / r₁)) hyr.2 (coe_lt_coe.2 hyr.1) (le_of_lt (hx 0))

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
/--
theorem `infinitePos_mul_of_not_infinitesimal_pos_infinitePos` / 定理 `infinitePos_mul_of_not_infinitesimal_pos_infinitePos`

English:
theorem infinitePos_mul_of_not_infinitesimal_pos_infinitePos
  given: {x y : Real*}
  proof: fun hx hp hy =>
  mul_comm y x ▸ infinitePos_mul_of_infinitePos_not_infinitesimal_pos hy hx hp

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]

中文:
定理 infinitePos_mul_of_not_infinitesimal_pos_infinitePos
  条件: {x y : 实数*}
  证明: fun hx hp hy =>
  mul_comm y x ▸ infinitePos_mul_of_infinitePos_not_infinitesimal_pos hy hx hp

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
-/
theorem infinitePos_mul_of_not_infinitesimal_pos_infinitePos {x y : Real*} :
    ¬Infinitesimal x -> 0 < x -> InfinitePos y -> InfinitePos (x * y) := fun hx hp hy =>
  mul_comm y x ▸ infinitePos_mul_of_infinitePos_not_infinitesimal_pos hy hx hp

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
/--
theorem `infinitePos_mul_of_infiniteNeg_not_infinitesimal_neg` / 定理 `infinitePos_mul_of_infiniteNeg_not_infinitesimal_neg`

English:
theorem infinitePos_mul_of_infiniteNeg_not_infinitesimal_neg
  given: {x y : Real*}
  proof: by
  rw [← infinitePos_neg]; rw [← neg_pos]; rw [← neg_mul_neg]; rw [← infinitesimal_neg]
  exact infinitePos_mul_of_infinitePos_not_infinitesimal_pos

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]

中文:
定理 infinitePos_mul_of_infiniteNeg_not_infinitesimal_neg
  条件: {x y : 实数*}
  证明: by
  rw [← infinitePos_neg]; rw [← neg_pos]; rw [← neg_mul_neg]; rw [← infinitesimal_neg]
  exact infinitePos_mul_of_infinitePos_not_infinitesimal_pos

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]

Depends on / 依赖: infinitePos_mul_of_infinitePos_not_infinitesimal_pos, infinitePos_neg, infinitesimal_neg, neg_mul_neg, neg_pos
-/
theorem infinitePos_mul_of_infiniteNeg_not_infinitesimal_neg {x y : Real*} :
    InfiniteNeg x -> ¬Infinitesimal y -> y < 0 -> InfinitePos (x * y) := by
  rw [← infinitePos_neg]; rw [← neg_pos]; rw [← neg_mul_neg]; rw [← infinitesimal_neg]
  exact infinitePos_mul_of_infinitePos_not_infinitesimal_pos

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
/--
theorem `infinitePos_mul_of_not_infinitesimal_neg_infiniteNeg` / 定理 `infinitePos_mul_of_not_infinitesimal_neg_infiniteNeg`

English:
theorem infinitePos_mul_of_not_infinitesimal_neg_infiniteNeg
  given: {x y : Real*}
  proof: fun hx hp hy =>
  mul_comm y x ▸ infinitePos_mul_of_infiniteNeg_not_infinitesimal_neg hy hx hp

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]

中文:
定理 infinitePos_mul_of_not_infinitesimal_neg_infiniteNeg
  条件: {x y : 实数*}
  证明: fun hx hp hy =>
  mul_comm y x ▸ infinitePos_mul_of_infiniteNeg_not_infinitesimal_neg hy hx hp

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
-/
theorem infinitePos_mul_of_not_infinitesimal_neg_infiniteNeg {x y : Real*} :
    ¬Infinitesimal x -> x < 0 -> InfiniteNeg y -> InfinitePos (x * y) := fun hx hp hy =>
  mul_comm y x ▸ infinitePos_mul_of_infiniteNeg_not_infinitesimal_neg hy hx hp

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
/--
theorem `infiniteNeg_mul_of_infinitePos_not_infinitesimal_neg` / 定理 `infiniteNeg_mul_of_infinitePos_not_infinitesimal_neg`

English:
theorem infiniteNeg_mul_of_infinitePos_not_infinitesimal_neg
  given: {x y : Real*}
  proof: by
  rw [← infinitePos_neg]; rw [← neg_pos]; rw [neg_mul_eq_mul_neg]; rw [← infinitesimal_neg]
  exact infinitePos_mul_of_infinitePos_not_infinitesimal_pos

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]

中文:
定理 infiniteNeg_mul_of_infinitePos_not_infinitesimal_neg
  条件: {x y : 实数*}
  证明: by
  rw [← infinitePos_neg]; rw [← neg_pos]; rw [neg_mul_eq_mul_neg]; rw [← infinitesimal_neg]
  exact infinitePos_mul_of_infinitePos_not_infinitesimal_pos

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]

Depends on / 依赖: infinitePos_mul_of_infinitePos_not_infinitesimal_pos, infinitePos_neg, infinitesimal_neg, neg_mul_eq_mul_neg, neg_pos
-/
theorem infiniteNeg_mul_of_infinitePos_not_infinitesimal_neg {x y : Real*} :
    InfinitePos x -> ¬Infinitesimal y -> y < 0 -> InfiniteNeg (x * y) := by
  rw [← infinitePos_neg]; rw [← neg_pos]; rw [neg_mul_eq_mul_neg]; rw [← infinitesimal_neg]
  exact infinitePos_mul_of_infinitePos_not_infinitesimal_pos

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
/--
theorem `infiniteNeg_mul_of_not_infinitesimal_neg_infinitePos` / 定理 `infiniteNeg_mul_of_not_infinitesimal_neg_infinitePos`

English:
theorem infiniteNeg_mul_of_not_infinitesimal_neg_infinitePos
  given: {x y : Real*}
  proof: fun hx hp hy =>
  mul_comm y x ▸ infiniteNeg_mul_of_infinitePos_not_infinitesimal_neg hy hx hp

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]

中文:
定理 infiniteNeg_mul_of_not_infinitesimal_neg_infinitePos
  条件: {x y : 实数*}
  证明: fun hx hp hy =>
  mul_comm y x ▸ infiniteNeg_mul_of_infinitePos_not_infinitesimal_neg hy hx hp

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
-/
theorem infiniteNeg_mul_of_not_infinitesimal_neg_infinitePos {x y : Real*} :
    ¬Infinitesimal x -> x < 0 -> InfinitePos y -> InfiniteNeg (x * y) := fun hx hp hy =>
  mul_comm y x ▸ infiniteNeg_mul_of_infinitePos_not_infinitesimal_neg hy hx hp

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
/--
theorem `infiniteNeg_mul_of_infiniteNeg_not_infinitesimal_pos` / 定理 `infiniteNeg_mul_of_infiniteNeg_not_infinitesimal_pos`

English:
theorem infiniteNeg_mul_of_infiniteNeg_not_infinitesimal_pos
  given: {x y : Real*}
  proof: by
  rw [← infinitePos_neg]; rw [← infinitePos_neg]; rw [neg_mul_eq_neg_mul]
  exact infinitePos_mul_of_infinitePos_not_infinitesimal_pos

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]

中文:
定理 infiniteNeg_mul_of_infiniteNeg_not_infinitesimal_pos
  条件: {x y : 实数*}
  证明: by
  rw [← infinitePos_neg]; rw [← infinitePos_neg]; rw [neg_mul_eq_neg_mul]
  exact infinitePos_mul_of_infinitePos_not_infinitesimal_pos

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]

Depends on / 依赖: infinitePos_mul_of_infinitePos_not_infinitesimal_pos, infinitePos_neg, neg_mul_eq_neg_mul
-/
theorem infiniteNeg_mul_of_infiniteNeg_not_infinitesimal_pos {x y : Real*} :
    InfiniteNeg x -> ¬Infinitesimal y -> 0 < y -> InfiniteNeg (x * y) := by
  rw [← infinitePos_neg]; rw [← infinitePos_neg]; rw [neg_mul_eq_neg_mul]
  exact infinitePos_mul_of_infinitePos_not_infinitesimal_pos

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
/--
theorem `infiniteNeg_mul_of_not_infinitesimal_pos_infiniteNeg` / 定理 `infiniteNeg_mul_of_not_infinitesimal_pos_infiniteNeg`

English:
theorem infiniteNeg_mul_of_not_infinitesimal_pos_infiniteNeg
  given: {x y : Real*}
  proof: fun hx hp hy => by
  rw [mul_comm]; exact infiniteNeg_mul_of_infiniteNeg_not_infinitesimal_pos hy hx hp

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]

中文:
定理 infiniteNeg_mul_of_not_infinitesimal_pos_infiniteNeg
  条件: {x y : 实数*}
  证明: fun hx hp hy => by
  rw [mul_comm]; exact infiniteNeg_mul_of_infiniteNeg_not_infinitesimal_pos hy hx hp

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]

Depends on / 依赖: infiniteNeg_mul_of_infiniteNeg_not_infinitesimal_pos, mul_comm
-/
theorem infiniteNeg_mul_of_not_infinitesimal_pos_infiniteNeg {x y : Real*} :
    ¬Infinitesimal x -> 0 < x -> InfiniteNeg y -> InfiniteNeg (x * y) := fun hx hp hy => by
  rw [mul_comm]; exact infiniteNeg_mul_of_infiniteNeg_not_infinitesimal_pos hy hx hp

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
/--
theorem `infinitePos_mul_infinitePos` / 定理 `infinitePos_mul_infinitePos`

English:
theorem infinitePos_mul_infinitePos
  given: {x y : Real*}
  proof: fun hx hy =>
  infinitePos_mul_of_infinitePos_not_infinitesimal_pos hx hy.not_infinitesimal (hy 0)

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]

中文:
定理 infinitePos_mul_infinitePos
  条件: {x y : 实数*}
  证明: fun hx hy =>
  infinitePos_mul_of_infinitePos_not_infinitesimal_pos hx hy.not_infinitesimal (hy 0)

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
-/
theorem infinitePos_mul_infinitePos {x y : Real*} :
    InfinitePos x -> InfinitePos y -> InfinitePos (x * y) := fun hx hy =>
  infinitePos_mul_of_infinitePos_not_infinitesimal_pos hx hy.not_infinitesimal (hy 0)

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
/--
theorem `infiniteNeg_mul_infiniteNeg` / 定理 `infiniteNeg_mul_infiniteNeg`

English:
theorem infiniteNeg_mul_infiniteNeg
  given: {x y : Real*}
  proof: fun hx hy =>
  infinitePos_mul_of_infiniteNeg_not_infinitesimal_neg hx hy.not_infinitesimal (hy 0)

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]

中文:
定理 infiniteNeg_mul_infiniteNeg
  条件: {x y : 实数*}
  证明: fun hx hy =>
  infinitePos_mul_of_infiniteNeg_not_infinitesimal_neg hx hy.not_infinitesimal (hy 0)

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
-/
theorem infiniteNeg_mul_infiniteNeg {x y : Real*} :
    InfiniteNeg x -> InfiniteNeg y -> InfinitePos (x * y) := fun hx hy =>
  infinitePos_mul_of_infiniteNeg_not_infinitesimal_neg hx hy.not_infinitesimal (hy 0)

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
/--
theorem `infinitePos_mul_infiniteNeg` / 定理 `infinitePos_mul_infiniteNeg`

English:
theorem infinitePos_mul_infiniteNeg
  given: {x y : Real*}
  proof: fun hx hy =>
  infiniteNeg_mul_of_infinitePos_not_infinitesimal_neg hx hy.not_infinitesimal (hy 0)

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]

中文:
定理 infinitePos_mul_infiniteNeg
  条件: {x y : 实数*}
  证明: fun hx hy =>
  infiniteNeg_mul_of_infinitePos_not_infinitesimal_neg hx hy.not_infinitesimal (hy 0)

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
-/
theorem infinitePos_mul_infiniteNeg {x y : Real*} :
    InfinitePos x -> InfiniteNeg y -> InfiniteNeg (x * y) := fun hx hy =>
  infiniteNeg_mul_of_infinitePos_not_infinitesimal_neg hx hy.not_infinitesimal (hy 0)

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
/--
theorem `infiniteNeg_mul_infinitePos` / 定理 `infiniteNeg_mul_infinitePos`

English:
theorem infiniteNeg_mul_infinitePos
  given: {x y : Real*}
  proof: fun hx hy =>
  infiniteNeg_mul_of_infiniteNeg_not_infinitesimal_pos hx hy.not_infinitesimal (hy 0)

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]

中文:
定理 infiniteNeg_mul_infinitePos
  条件: {x y : 实数*}
  证明: fun hx hy =>
  infiniteNeg_mul_of_infiniteNeg_not_infinitesimal_pos hx hy.not_infinitesimal (hy 0)

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
-/
theorem infiniteNeg_mul_infinitePos {x y : Real*} :
    InfiniteNeg x -> InfinitePos y -> InfiniteNeg (x * y) := fun hx hy =>
  infiniteNeg_mul_of_infiniteNeg_not_infinitesimal_pos hx hy.not_infinitesimal (hy 0)

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
/--
theorem `infinite_mul_of_infinite_not_infinitesimal` / 定理 `infinite_mul_of_infinite_not_infinitesimal`

English:
theorem infinite_mul_of_infinite_not_infinitesimal
  given: {x y : Real*}
  proof: fun hx hy =>
  have h0 : y < 0 ∨ 0 < y := lt_or_gt_of_ne fun H0 => hy (Eq.substr H0 (isSt_refl_real 0))
  hx.elim
    (h0.elim
      (fun H0 Hx => Or.inr (infiniteNeg_mul_of_infinitePos_not_infinitesimal_neg Hx hy H0))
      fun H0 Hx => Or.inl (infinitePos_mul_of_infinitePos_not_infinitesimal_pos H

中文:
定理 infinite_mul_of_infinite_not_infinitesimal
  条件: {x y : 实数*}
  证明: fun hx hy =>
  have h0 : y < 0 ∨ 0 < y := lt_or_gt_of_ne fun H0 => hy (Eq.substr H0 (isSt_refl_real 0))
  hx.elim
    (h0.elim
      (fun H0 Hx => Or.inr (infiniteNeg_mul_of_infinitePos_not_infinitesimal_neg Hx hy H0))
      fun H0 Hx => Or.inl (infinitePos_mul_of_infinitePos_not_infinitesimal_pos H
-/
theorem infinite_mul_of_infinite_not_infinitesimal {x y : Real*} :
    Infinite x -> ¬Infinitesimal y -> Infinite (x * y) := fun hx hy =>
  have h0 : y < 0 ∨ 0 < y := lt_or_gt_of_ne fun H0 => hy (Eq.substr H0 (isSt_refl_real 0))
  hx.elim
    (h0.elim
      (fun H0 Hx => Or.inr (infiniteNeg_mul_of_infinitePos_not_infinitesimal_neg Hx hy H0))
      fun H0 Hx => Or.inl (infinitePos_mul_of_infinitePos_not_infinitesimal_pos Hx hy H0))
    (h0.elim
      (fun H0 Hx => Or.inl (infinitePos_mul_of_infiniteNeg_not_infinitesimal_neg Hx hy H0))
      fun H0 Hx => Or.inr (infiniteNeg_mul_of_infiniteNeg_not_infinitesimal_pos Hx hy H0))

@[deprecated "`Infinitesimal` is deprecated" (since := "2026-01-05")]
/--
theorem `infinite_mul_of_not_infinitesimal_infinite` / 定理 `infinite_mul_of_not_infinitesimal_infinite`

English:
theorem infinite_mul_of_not_infinitesimal_infinite
  given: {x y : Real*}
  proof: fun hx hy => by
  rw [mul_comm]; exact infinite_mul_of_infinite_not_infinitesimal hy hx

@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]

中文:
定理 infinite_mul_of_not_infinitesimal_infinite
  条件: {x y : 实数*}
  证明: fun hx hy => by
  rw [mul_comm]; exact infinite_mul_of_infinite_not_infinitesimal hy hx

@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]

Depends on / 依赖: infinite_mul_of_infinite_not_infinitesimal, mul_comm
-/
theorem infinite_mul_of_not_infinitesimal_infinite {x y : Real*} :
    ¬Infinitesimal x -> Infinite y -> Infinite (x * y) := fun hx hy => by
  rw [mul_comm]; exact infinite_mul_of_infinite_not_infinitesimal hy hx

@[deprecated "`Infinite` is deprecated" (since := "2026-01-05")]
/--
theorem `Infinite.mul` / 定理 `Infinite.mul`

English:
theorem Infinite.mul
  given: {x y : Real*}
  statement: Infinite x -> Infinite y -> Infinite (x * y)
  proof: fun hx hy =>
  infinite_mul_of_infinite_not_infinitesimal hx hy.not_infinitesimal

中文:
定理 Infinite.mul
  条件: {x y : 实数*}
  结论: Infinite x -> Infinite y -> Infinite (x * y)
  证明: fun hx hy =>
  infinite_mul_of_infinite_not_infinitesimal hx hy.not_infinitesimal
-/
theorem Infinite.mul {x y : Real*} : Infinite x -> Infinite y -> Infinite (x * y) := fun hx hy =>
  infinite_mul_of_infinite_not_infinitesimal hx hy.not_infinitesimal

end Hyperreal
end

/-
Porting note (https://github.com/leanprover-community/mathlib4/issues/11215): TODO: restore `positivity` plugin

namespace Tactic

open Positivity

private theorem hyperreal_coe_ne_zero {r : ℝ} : r ≠ 0 → (r : ℝ*) ≠ 0 :=
  Hyperreal.coe_ne_zero.2

private theorem hyperreal_coe_nonneg {r : ℝ} : 0 ≤ r → 0 ≤ (r : ℝ*) :=
  Hyperreal.coe_nonneg.2

private theorem hyperreal_coe_pos {r : ℝ} : 0 < r → 0 < (r : ℝ*) :=
  Hyperreal.coe_pos.2

/-- Extension for the `positivity` tactic: cast from `ℝ` to `ℝ*`. -/
@[positivity]
unsafe def positivity_coe_real_hyperreal : expr -> tactic strictness
  | q(@coe _ _ $(inst) $(a)) => do
    unify inst q(@coeToLift _ _ Hyperreal.hasCoeT)
    let strictness_a ← core a
    match strictness_a with
| positive p => positive < > mk_app `` hyperreal_coe_pos [p]
| nonnegative p => nonnegative < > mk_app `` hyperreal_coe_nonneg [p]
| nonzero p => nonzero < > mk_app `` hyperreal_coe_ne_zero [p]
  | e =>
    pp e >>= fail ∘ format.bracket "The expression " " is not of the form `(r : Real*)` for `r : Real`"

end Tactic
-/
