/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Order.SemiconjSup

/-!
# Translation number of a monotone real map that commutes with `x ↦ x + 1`

Let `f : ℝ → ℝ` be a monotone map such that `f (x + 1) = f x + 1` for all `x`. Then the limit
$$
  \tau(f)=\lim_{n\to\infty}{f^n(x)-x}{n}
$$
exists and does not depend on `x`. This number is called the *translation number* of `f`.
Different authors use different notation for this number: `τ`, `ρ`, `rot`, etc

In this file we define a structure `CircleDeg1Lift` for bundled maps with these properties, define
translation number of `f : CircleDeg1Lift`, prove some estimates relating `f^n(x)-x` to `τ(f)`. In
case of a continuous map `f` we also prove that `f` admits a point `x` such that `f^n(x)=x+m` if and
only if `τ(f)=m/n`.

Maps of this type naturally appear as lifts of orientation-preserving circle homeomorphisms. More
precisely, let `f` be an orientation-preserving homeomorphism of the circle $S^1=ℝ/ℤ$, and
consider a real number `a` such that
`⟦a⟧ = f 0`, where `⟦⟧` means the natural projection `ℝ → ℝ/ℤ`. Then there exists a unique
continuous function `F : ℝ → ℝ` such that `F 0 = a` and `⟦F x⟧ = f ⟦x⟧` for all `x` (this fact is
not formalized yet). This function is strictly monotone, continuous, and satisfies
`F (x + 1) = F x + 1`. The number `⟦τ F⟧ : ℝ / ℤ` is called the *rotation number* of `f`.
It does not depend on the choice of `a`.

## Main definitions

* `CircleDeg1Lift`: a monotone map `f : ℝ → ℝ` such that `f (x + 1) = f x + 1` for all `x`;
  the type `CircleDeg1Lift` is equipped with `Lattice` and `Monoid` structures; the
  multiplication is given by composition: `(f * g) x = f (g x)`.
* `CircleDeg1Lift.translationNumber`: translation number of `f : CircleDeg1Lift`.

## Main statements

We prove the following properties of `CircleDeg1Lift.translationNumber`.

* `CircleDeg1Lift.translationNumber_eq_of_dist_bounded`: if the distance between `(f^n) 0`
  and `(g^n) 0` is bounded from above uniformly in `n : ℕ`, then `f` and `g` have equal
  translation numbers.

* `CircleDeg1Lift.translationNumber_eq_of_semiconjBy`: if two `CircleDeg1Lift` maps `f`, `g`
  are semiconjugate by a `CircleDeg1Lift` map, then `τ f = τ g`.

* `CircleDeg1Lift.translationNumber_units_inv`: if `f` is an invertible `CircleDeg1Lift` map
  (equivalently, `f` is a lift of an orientation-preserving circle homeomorphism), then
  the translation number of `f⁻¹` is the negative of the translation number of `f`.

* `CircleDeg1Lift.translationNumber_mul_of_commute`: if `f` and `g` commute, then
  `τ (f * g) = τ f + τ g`.

* `CircleDeg1Lift.translationNumber_eq_rat_iff`: the translation number of `f` is equal to
  a rational number `m / n` if and only if `(f^n) x = x + m` for some `x`.

* `CircleDeg1Lift.semiconj_of_bijective_of_translationNumber_eq`: if `f` and `g` are two
  bijective `CircleDeg1Lift` maps and their translation numbers are equal, then these
  maps are semiconjugate to each other.

* `CircleDeg1Lift.semiconj_of_group_action_of_forall_translationNumber_eq`: let `f₁` and `f₂` be
  two actions of a group `G` on the circle by degree 1 maps (formally, `f₁` and `f₂` are two
  homomorphisms from `G →* CircleDeg1Lift`). If the translation numbers of `f₁ g` and `f₂ g` are
  equal to each other for all `g : G`, then these two actions are semiconjugate by some
  `F : CircleDeg1Lift`. This is a version of Proposition 5.4 from [Étienne Ghys, Groupes
  d'homéomorphismes du cercle et cohomologie bornée][ghys87:groupes].

## Notation

We use a local notation `τ` for the translation number of `f : CircleDeg1Lift`.

## Implementation notes

We define the translation number of `f : CircleDeg1Lift` to be the limit of the sequence
`(f ^ (2 ^ n)) 0 / (2 ^ n)`, then prove that `((f ^ n) x - x) / n` tends to this number for any `x`.
This way it is much easier to prove that the limit exists and basic properties of the limit.

We define translation number for a wider class of maps `f : ℝ → ℝ` instead of lifts of orientation
preserving circle homeomorphisms for two reasons:

* non-strictly monotone circle self-maps with discontinuities naturally appear as Poincaré maps
  for some flows on the two-torus (e.g., one can take a constant flow and glue in a few Cherry
  cells);
* definition and some basic properties still work for this class.

## References

* [Étienne Ghys, Groupes d'homéomorphismes du cercle et cohomologie bornée][ghys87:groupes]

## TODO

Here are some short-term goals.

* Introduce a structure or a typeclass for lifts of circle homeomorphisms. We use
  `Units CircleDeg1Lift` for now, but it's better to have a dedicated type (or a typeclass?).

* Prove that the `SemiconjBy` relation on circle homeomorphisms is an equivalence relation.

* Introduce `ConditionallyCompleteLattice` structure, use it in the proof of
  `CircleDeg1Lift.semiconj_of_group_action_of_forall_translationNumber_eq`.

* Prove that the orbits of the irrational rotation are dense in the circle. Deduce that a
  homeomorphism with an irrational rotation is semiconjugate to the corresponding irrational
  translation by a continuous `CircleDeg1Lift`.

## Tags

circle homeomorphism, rotation number
-/

@[expose] public section

open Filter Set Int Topology
open Function hiding Commute

/-!
### Definition and monoid structure
-/

/--
Definition of `CircleDeg1Lift` / `CircleDeg1Lift` 的定义

English:
structure CircleDeg1Lift
  parameters: : Type extends Real ->o Real where
  extends: Real ->o Real
  axioms and operations (1):
    - map_add_one' : forall x, toFun (x + 1) = toFun x + 1

中文:
结构 CircleDeg1Lift
  参数: : 类型 extends 实数 ->o 实数 where
  继承: 实数 ->o 实数
  公理与运算 (1 个):
    - map_add_one' : 对任意 x, toFun (x + 1) = toFun x + 1
-/
structure CircleDeg1Lift : Type extends Real ->o Real where
  map_add_one' : forall x, toFun (x + 1) = toFun x + 1

namespace CircleDeg1Lift

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FunLike CircleDeg1Lift Real Real
  body: f.toFun
  coe_injective | ⟨⟨_, _⟩, _⟩, ⟨⟨_, _⟩, _⟩, rfl => rfl

中文:
实例 :
  签名: 函数状 CircleDeg1Lift 实数 实数
  定义体: f.toFun
  coe_injective | ⟨⟨_, _⟩, _⟩, ⟨⟨_, _⟩, _⟩, rfl => rfl

Depends on / 依赖: f.toFun
-/
instance : FunLike CircleDeg1Lift Real Real where
  coe f := f.toFun
  coe_injective | ⟨⟨_, _⟩, _⟩, ⟨⟨_, _⟩, _⟩, rfl => rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: OrderHomClass CircleDeg1Lift Real Real
  body: f.monotone' h

中文:
实例 :
  签名: 序态射类 CircleDeg1Lift 实数 实数
  定义体: f.monotone' h

Depends on / 依赖: f.monotone, monotone
-/
instance : OrderHomClass CircleDeg1Lift Real Real where
  map_rel f _ _ h := f.monotone' h

/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  given: (f h)
  statement: ⇑(mk f h) = f
  proof: rfl

中文:
定理 coe_mk
  条件: (f h)
  结论: ⇑(mk f h) = f
  证明: rfl
-/
@[simp] theorem coe_mk (f h) : ⇑(mk f h) = f := rfl

variable (f g : CircleDeg1Lift)

/--
theorem `coe_toOrderHom` / 定理 `coe_toOrderHom`

English:
theorem coe_toOrderHom
  statement: ⇑f.toOrderHom = f
  proof: rfl

中文:
定理 coe_toOrderHom
  结论: ⇑f.toOrderHom = f
  证明: rfl
-/
@[simp] theorem coe_toOrderHom : ⇑f.toOrderHom = f := rfl

/--
theorem `monotone` / 定理 `monotone`

English:
theorem monotone
  statement: Monotone f
  proof: f.monotone'

中文:
定理 monotone
  结论: 递增 f
  证明: f.monotone'
-/
protected theorem monotone : Monotone f := f.monotone'

/--
theorem `mono` / 定理 `mono`

English:
theorem mono
  given: {x y} (h : x <= y)
  statement: f x <= f y
  proof: f.monotone h

中文:
定理 mono
  条件: {x y} (h : x <= y)
  结论: f x <= f y
  证明: f.monotone h
-/
@[gcongr, mono] theorem mono {x y} (h : x <= y) : f x <= f y := f.monotone h

/--
theorem `strictMono_iff_injective` / 定理 `strictMono_iff_injective`

English:
theorem strictMono_iff_injective
  statement: StrictMono f ↔ Injective f
  proof: f.monotone.strictMono_iff_injective

@[simp]

中文:
定理 strictMono_iff_injective
  结论: 严格递增 f ↔ 单射 f
  证明: f.monotone.strictMono_iff_injective

@[simp]

Depends on / 依赖: f.monotone.strictMono_iff_injective, monotone, strictMono_iff_injective
-/
theorem strictMono_iff_injective : StrictMono f ↔ Injective f :=
  f.monotone.strictMono_iff_injective

@[simp]
/--
theorem `map_add_one` / 定理 `map_add_one`

English:
theorem map_add_one
  statement: forall x, f (x + 1) = f x + 1
  proof: f.map_add_one'

@[simp]

中文:
定理 map_add_one
  结论: 对任意 x, f (x + 1) = f x + 1
  证明: f.map_add_one'

@[simp]

Depends on / 依赖: f.map_add_one, map_add_one
-/
theorem map_add_one : forall x, f (x + 1) = f x + 1 :=
  f.map_add_one'

@[simp]
/--
theorem `map_one_add` / 定理 `map_one_add`

English:
theorem map_one_add
  given: (x : Real)
  statement: f (1 + x) = 1 + f x
  proof: by rw [add_comm, map_add_one, add_comm 1]

@[ext]

中文:
定理 map_one_add
  条件: (x : 实数)
  结论: f (1 + x) = 1 + f x
  证明: by rw [add_comm, map_add_one, add_comm 1]

@[ext]

Depends on / 依赖: add_comm, map_add_one
-/
theorem map_one_add (x : Real) : f (1 + x) = 1 + f x := by rw [add_comm, map_add_one, add_comm 1]

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: ⦃f g
  statement: CircleDeg1Lift⦄ (h : forall x, f x = g x) : f = g
  proof: DFunLike.ext f g h

中文:
定理 ext
  条件: ⦃f g
  结论: CircleDeg1Lift⦄ (h : 对任意 x, f x = g x) : f = g
  证明: DFunLike.ext f g h

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext ⦃f g : CircleDeg1Lift⦄ (h : forall x, f x = g x) : f = g :=
  DFunLike.ext f g h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Monoid CircleDeg1Lift
  body: { toOrderHom := f.1.comp g.1
      map_add_one' := fun x => by simp [map_add_one] }
  one := ⟨.id, fun _ => rfl⟩
  mul_one _ := rfl
  one_mul _ := rfl
  mul_assoc _ _ _ := DFunLike.coe_injective rfl

中文:
实例 :
  签名: 幺半群 CircleDeg1Lift
  定义体: { toOrderHom := f.1.comp g.1
      map_add_one' := fun x => by simp [map_add_one] }
  one := ⟨.id, fun _ => rfl⟩
  mul_one _ := rfl
  one_mul _ := rfl
  mul_assoc _ _ _ := DFunLike.coe_injective rfl

Depends on / 依赖: DFunLike, DFunLike.coe_injective, coe_injective, map_add_one, mul_assoc, mul_one, one_mul, toOrderHom
-/
instance : Monoid CircleDeg1Lift where
  mul f g :=
    { toOrderHom := f.1.comp g.1
      map_add_one' := fun x => by simp [map_add_one] }
  one := ⟨.id, fun _ => rfl⟩
  mul_one _ := rfl
  one_mul _ := rfl
  mul_assoc _ _ _ := DFunLike.coe_injective rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited CircleDeg1Lift
  body: ⟨1⟩

@[simp]

中文:
实例 :
  签名: 可居 CircleDeg1Lift
  定义体: ⟨1⟩

@[simp]
-/
instance : Inhabited CircleDeg1Lift := ⟨1⟩

@[simp]
/--
theorem `coe_mul` / 定理 `coe_mul`

English:
theorem coe_mul
  statement: ⇑(f * g) = f ∘ g
  proof: rfl

中文:
定理 coe_mul
  结论: ⇑(f * g) = f ∘ g
  证明: rfl
-/
theorem coe_mul : ⇑(f * g) = f ∘ g :=
  rfl

/--
theorem `mul_apply` / 定理 `mul_apply`

English:
theorem mul_apply
  given: (x)
  statement: (f * g) x = f (g x)
  proof: rfl

@[simp]

中文:
定理 mul_apply
  条件: (x)
  结论: (f * g) x = f (g x)
  证明: rfl

@[simp]
-/
theorem mul_apply (x) : (f * g) x = f (g x) :=
  rfl

@[simp]
/--
theorem `coe_one` / 定理 `coe_one`

English:
theorem coe_one
  statement: ⇑(1 : CircleDeg1Lift) = id
  proof: rfl

中文:
定理 coe_one
  结论: ⇑(1 : CircleDeg1Lift) = id
  证明: rfl
-/
theorem coe_one : ⇑(1 : CircleDeg1Lift) = id :=
  rfl

/--
Instance `unitsHasCoeToFun` / 实例 `unitsHasCoeToFun`

English:
instance unitsHasCoeToFun
  signature: : CoeFun CircleDeg1Liftˣ fun _ => Real -> Real
  body: ⟨fun f => ⇑(f : CircleDeg1Lift)⟩

@[simp]

中文:
实例 unitsHasCoeToFun
  签名: : CoeFun CircleDeg1Liftˣ fun _ => 实数 -> 实数
  定义体: ⟨fun f => ⇑(f : CircleDeg1Lift)⟩

@[simp]

Depends on / 依赖: CircleDeg1Lift
-/
instance unitsHasCoeToFun : CoeFun CircleDeg1Liftˣ fun _ => Real -> Real :=
  ⟨fun f => ⇑(f : CircleDeg1Lift)⟩

@[simp]
/--
theorem `units_inv_apply_apply` / 定理 `units_inv_apply_apply`

English:
theorem units_inv_apply_apply
  given: (f : CircleDeg1Liftˣ) (x : Real)
  proof: by simp only [← mul_apply, f.inv_mul, coe_one, id]

@[simp]

中文:
定理 units_inv_apply_apply
  条件: (f : CircleDeg1Liftˣ) (x : 实数)
  证明: by simp only [← mul_apply, f.inv_mul, coe_one, id]

@[simp]

Depends on / 依赖: coe_one, f.inv_mul, inv_mul, mul_apply
-/
theorem units_inv_apply_apply (f : CircleDeg1Liftˣ) (x : Real) :
    (f⁻¹ : CircleDeg1Liftˣ) (f x) = x := by simp only [← mul_apply, f.inv_mul, coe_one, id]

@[simp]
/--
theorem `units_apply_inv_apply` / 定理 `units_apply_inv_apply`

English:
theorem units_apply_inv_apply
  given: (f : CircleDeg1Liftˣ) (x : Real)
  proof: by simp only [← mul_apply, f.mul_inv, coe_one, id]

中文:
定理 units_apply_inv_apply
  条件: (f : CircleDeg1Liftˣ) (x : 实数)
  证明: by simp only [← mul_apply, f.mul_inv, coe_one, id]

Depends on / 依赖: coe_one, f.mul_inv, mul_apply, mul_inv
-/
theorem units_apply_inv_apply (f : CircleDeg1Liftˣ) (x : Real) :
    f ((f⁻¹ : CircleDeg1Liftˣ) x) = x := by simp only [← mul_apply, f.mul_inv, coe_one, id]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `toOrderIso` / `toOrderIso` 的定义

English:
definition toOrderIso
  signature: : CircleDeg1Liftˣ ->* Real ≃o Real where
  body: { toFun := f
      invFun := ⇑f⁻¹
      left_inv := units_inv_apply_apply f
      right_inv := units_apply_inv_apply f
      map_rel_iff' := ⟨fun h => by simpa using mono (↑f⁻¹) h, mono f⟩ }
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp]

中文:
定义 toOrderIso
  签名: : CircleDeg1Liftˣ ->* 实数 ≃o 实数 where
  定义体: { toFun := f
      invFun := ⇑f⁻¹
      left_inv := units_inv_apply_apply f
      right_inv := units_apply_inv_apply f
      map_rel_iff' := ⟨fun h => by simpa using mono (↑f⁻¹) h, mono f⟩ }
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp]

Depends on / 依赖: invFun, left_inv, map_mul, map_one, map_rel_iff, right_inv, units_apply_inv_apply, units_inv_apply_apply
-/
def toOrderIso : CircleDeg1Liftˣ ->* Real ≃o Real where
  toFun f :=
    { toFun := f
      invFun := ⇑f⁻¹
      left_inv := units_inv_apply_apply f
      right_inv := units_apply_inv_apply f
      map_rel_iff' := ⟨fun h => by simpa using mono (↑f⁻¹) h, mono f⟩ }
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp]
/--
theorem `coe_toOrderIso` / 定理 `coe_toOrderIso`

English:
theorem coe_toOrderIso
  given: (f : CircleDeg1Liftˣ)
  statement: ⇑(toOrderIso f) = f
  proof: rfl

@[simp]

中文:
定理 coe_toOrderIso
  条件: (f : CircleDeg1Liftˣ)
  结论: ⇑(toOrderIso f) = f
  证明: rfl

@[simp]
-/
theorem coe_toOrderIso (f : CircleDeg1Liftˣ) : ⇑(toOrderIso f) = f :=
  rfl

@[simp]
/--
theorem `coe_toOrderIso_symm` / 定理 `coe_toOrderIso_symm`

English:
theorem coe_toOrderIso_symm
  given: (f : CircleDeg1Liftˣ)
  proof: rfl

@[simp]

中文:
定理 coe_toOrderIso_symm
  条件: (f : CircleDeg1Liftˣ)
  证明: rfl

@[simp]
-/
theorem coe_toOrderIso_symm (f : CircleDeg1Liftˣ) :
    ⇑(toOrderIso f).symm = (f⁻¹ : CircleDeg1Liftˣ) :=
  rfl

@[simp]
/--
theorem `coe_toOrderIso_inv` / 定理 `coe_toOrderIso_inv`

English:
theorem coe_toOrderIso_inv
  given: (f : CircleDeg1Liftˣ)
  statement: ⇑(toOrderIso f)⁻¹ = (f⁻¹ : CircleDeg1Liftˣ)
  proof: rfl

中文:
定理 coe_toOrderIso_inv
  条件: (f : CircleDeg1Liftˣ)
  结论: ⇑(toOrderIso f)⁻¹ = (f⁻¹ : CircleDeg1Liftˣ)
  证明: rfl
-/
theorem coe_toOrderIso_inv (f : CircleDeg1Liftˣ) : ⇑(toOrderIso f)⁻¹ = (f⁻¹ : CircleDeg1Liftˣ) :=
  rfl

/--
theorem `isUnit_iff_bijective` / 定理 `isUnit_iff_bijective`

English:
theorem isUnit_iff_bijective
  given: {f : CircleDeg1Lift}
  statement: IsUnit f ↔ Bijective f
  proof: ⟨fun ⟨u, h⟩ => h ▸ (toOrderIso u).bijective, fun h =>
    Units.isUnit
      { val := f
        inv :=
          { toFun := (Equiv.ofBijective f h).symm
            monotone' := fun x y hxy =>
              (f.strictMono_iff_injective.2 h.1).le_iff_le.1
                (by simp only [Equiv.ofBijective_apply_symm_apply f h, hxy])
            map_add_one' := fun x =>
h.1 by simp only [Equiv.ofBijective_apply_symm_apply f, f.map_add_one] }
val_inv := ext Equiv.ofBijective_apply_symm_apply f h
inv_val := ext Equiv.ofBijective_symm_apply_apply f h }⟩

中文:
定理 isUnit_iff_bijective
  条件: {f : CircleDeg1Lift}
  结论: 是单位 f ↔ 双射 f
  证明: ⟨fun ⟨u, h⟩ => h ▸ (toOrderIso u).bijective, fun h =>
    Units.isUnit
      { val := f
        inv :=
          { toFun := (Equiv.ofBijective f h).symm
            monotone' := fun x y hxy =>
              (f.strictMono_iff_injective.2 h.1).le_iff_le.1
                (by simp only [Equiv.ofBijective_apply_symm_apply f h, hxy])
            map_add_one' := fun x =>
h.1 by simp only [Equiv.ofBijective_apply_symm_apply f, f.map_add_one] }
val_inv := ext Equiv.ofBijective_apply_symm_apply f h
inv_val := ext Equiv.ofBijective_symm_apply_apply f h }⟩

Depends on / 依赖: Equiv.ofBijective, Equiv.ofBijective_apply_symm_apply, Equiv.ofBijective_symm_apply_apply, Units.isUnit, bijective, f.map_add_one, f.strictMono_iff_injective, inv_val, isUnit, le_iff_le, map_add_one, monotone, ofBijective, ofBijective_apply_symm_apply, ofBijective_symm_apply_apply, strictMono_iff_injective, toOrderIso, val_inv
-/
theorem isUnit_iff_bijective {f : CircleDeg1Lift} : IsUnit f ↔ Bijective f :=
  ⟨fun ⟨u, h⟩ => h ▸ (toOrderIso u).bijective, fun h =>
    Units.isUnit
      { val := f
        inv :=
          { toFun := (Equiv.ofBijective f h).symm
            monotone' := fun x y hxy =>
              (f.strictMono_iff_injective.2 h.1).le_iff_le.1
                (by simp only [Equiv.ofBijective_apply_symm_apply f h, hxy])
            map_add_one' := fun x =>
h.1 by simp only [Equiv.ofBijective_apply_symm_apply f, f.map_add_one] }
val_inv := ext Equiv.ofBijective_apply_symm_apply f h
inv_val := ext Equiv.ofBijective_symm_apply_apply f h }⟩

/--
theorem `coe_pow` / 定理 `coe_pow`

English:
theorem coe_pow
  statement: forall n : Nat, ⇑(f ^ n) = f^[n]

中文:
定理 coe_pow
  结论: 对任意 n : 自然数, ⇑(f ^ n) = f^[n]
-/
theorem coe_pow : forall n : Nat, ⇑(f ^ n) = f^[n]
  | 0 => rfl
  | n + 1 => by
    simp [coe_pow n, pow_succ]

/--
theorem `semiconjBy_iff_semiconj` / 定理 `semiconjBy_iff_semiconj`

English:
theorem semiconjBy_iff_semiconj
  given: {f g₁ g₂ : CircleDeg1Lift}
  proof: CircleDeg1Lift.ext_iff

中文:
定理 semiconjBy_iff_semiconj
  条件: {f g₁ g₂ : CircleDeg1Lift}
  证明: CircleDeg1Lift.ext_iff

Depends on / 依赖: CircleDeg1Lift, CircleDeg1Lift.ext_iff, ext_iff
-/
theorem semiconjBy_iff_semiconj {f g₁ g₂ : CircleDeg1Lift} :
    SemiconjBy f g₁ g₂ ↔ Semiconj f g₁ g₂ :=
  CircleDeg1Lift.ext_iff

/--
theorem `commute_iff_commute` / 定理 `commute_iff_commute`

English:
theorem commute_iff_commute
  given: {f g : CircleDeg1Lift}
  statement: Commute f g ↔ Function.Commute f g
  proof: CircleDeg1Lift.ext_iff

中文:
定理 commute_iff_commute
  条件: {f g : CircleDeg1Lift}
  结论: Commute f g ↔ 函数.Commute f g
  证明: CircleDeg1Lift.ext_iff

Depends on / 依赖: CircleDeg1Lift, CircleDeg1Lift.ext_iff, ext_iff
-/
theorem commute_iff_commute {f g : CircleDeg1Lift} : Commute f g ↔ Function.Commute f g :=
  CircleDeg1Lift.ext_iff

/-!
### Translate by a constant
-/


/--
Definition of `translate` / `translate` 的定义

English:
definition translate
  signature: : Multiplicative Real ->* CircleDeg1Liftˣ
  body: MonoidHom.toHomUnits
  { toFun x := ⟨⟨fun y => x.toAdd + y, add_right_mono⟩, fun _ => (add_assoc ..).symm⟩
    map_one' := ext zero_add
map_mul' _ _ := ext add_assoc _ _ }

@[simp]

中文:
定义 translate
  签名: : Multiplicative 实数 ->* CircleDeg1Liftˣ
  定义体: MonoidHom.toHomUnits
  { toFun x := ⟨⟨fun y => x.toAdd + y, add_right_mono⟩, fun _ => (add_assoc ..).symm⟩
    map_one' := ext zero_add
map_mul' _ _ := ext add_assoc _ _ }

@[simp]

Depends on / 依赖: MonoidHom, MonoidHom.toHomUnits, toHomUnits
-/
def translate : Multiplicative Real ->* CircleDeg1Liftˣ := MonoidHom.toHomUnits
  { toFun x := ⟨⟨fun y => x.toAdd + y, add_right_mono⟩, fun _ => (add_assoc ..).symm⟩
    map_one' := ext zero_add
map_mul' _ _ := ext add_assoc _ _ }

@[simp]
/--
theorem `translate_apply` / 定理 `translate_apply`

English:
theorem translate_apply
  given: (x y : Real)
  statement: translate (Multiplicative.ofAdd x) y = x + y
  proof: rfl

@[simp]

中文:
定理 translate_apply
  条件: (x y : 实数)
  结论: translate (Multiplicative.ofAdd x) y = x + y
  证明: rfl

@[simp]
-/
theorem translate_apply (x y : Real) : translate (Multiplicative.ofAdd x) y = x + y :=
  rfl

@[simp]
/--
theorem `translate_inv_apply` / 定理 `translate_inv_apply`

English:
theorem translate_inv_apply
  given: (x y : Real)
  statement: (translate <| Multiplicative.ofAdd x)⁻¹ y = -x + y
  proof: rfl

@[simp]

中文:
定理 translate_inv_apply
  条件: (x y : 实数)
  结论: (translate <| Multiplicative.ofAdd x)⁻¹ y = -x + y
  证明: rfl

@[simp]
-/
theorem translate_inv_apply (x y : Real) : (translate <| Multiplicative.ofAdd x)⁻¹ y = -x + y :=
  rfl

@[simp]
/--
theorem `translate_zpow` / 定理 `translate_zpow`

English:
theorem translate_zpow
  given: (x : Real) (n : Int)
  proof: by
  simp only [← zsmul_eq_mul, ofAdd_zsmul, map_zpow]

@[simp]

中文:
定理 translate_zpow
  条件: (x : 实数) (n : 整数)
  证明: by
  simp only [← zsmul_eq_mul, ofAdd_zsmul, map_zpow]

@[simp]

Depends on / 依赖: map_zpow, ofAdd_zsmul, zsmul_eq_mul
-/
theorem translate_zpow (x : Real) (n : Int) :
    translate (Multiplicative.ofAdd x) ^ n = translate (Multiplicative.ofAdd <| ↑n * x) := by
  simp only [← zsmul_eq_mul, ofAdd_zsmul, map_zpow]

@[simp]
/--
theorem `translate_pow` / 定理 `translate_pow`

English:
theorem translate_pow
  given: (x : Real) (n : Nat)
  proof: translate_zpow x n

@[simp]

中文:
定理 translate_pow
  条件: (x : 实数) (n : 自然数)
  证明: translate_zpow x n

@[simp]

Depends on / 依赖: translate_zpow
-/
theorem translate_pow (x : Real) (n : Nat) :
    translate (Multiplicative.ofAdd x) ^ n = translate (Multiplicative.ofAdd <| ↑n * x) :=
  translate_zpow x n

@[simp]
/--
theorem `translate_iterate` / 定理 `translate_iterate`

English:
theorem translate_iterate
  given: (x : Real) (n : Nat)
  proof: by
  rw [← coe_pow]; rw [← Units.val_pow_eq_pow_val]; rw [translate_pow]

中文:
定理 translate_iterate
  条件: (x : 实数) (n : 自然数)
  证明: by
  rw [← coe_pow]; rw [← Units.val_pow_eq_pow_val]; rw [translate_pow]

Depends on / 依赖: Units.val_pow_eq_pow_val, coe_pow, translate_pow, val_pow_eq_pow_val
-/
theorem translate_iterate (x : Real) (n : Nat) :
    (translate (Multiplicative.ofAdd x))^[n] = translate (Multiplicative.ofAdd <| ↑n * x) := by
  rw [← coe_pow]; rw [← Units.val_pow_eq_pow_val]; rw [translate_pow]


/--
theorem `commute_nat_add` / 定理 `commute_nat_add`

English:
theorem commute_nat_add
  given: (n : Nat)
  statement: Function.Commute f (n + ·)
  proof: by
  simpa only [nsmul_one, add_left_iterate] using Function.Commute.iterate_right f.map_one_add n

中文:
定理 commute_nat_add
  条件: (n : 自然数)
  结论: 函数.Commute f (n + ·)
  证明: by
  simpa only [nsmul_one, add_left_iterate] using Function.Commute.iterate_right f.map_one_add n

Depends on / 依赖: Commute, Function, Function.Commute.iterate_right, add_left_iterate, f.map_one_add, iterate_right, map_one_add, nsmul_one
-/
theorem commute_nat_add (n : Nat) : Function.Commute f (n + ·) := by
  simpa only [nsmul_one, add_left_iterate] using Function.Commute.iterate_right f.map_one_add n

/--
theorem `commute_add_nat` / 定理 `commute_add_nat`

English:
theorem commute_add_nat
  given: (n : Nat)
  statement: Function.Commute f (· + n)
  proof: by
  simp only [add_comm _ (n : Real), f.commute_nat_add n]

中文:
定理 commute_add_nat
  条件: (n : 自然数)
  结论: 函数.Commute f (· + n)
  证明: by
  simp only [add_comm _ (n : Real), f.commute_nat_add n]

Depends on / 依赖: add_comm, commute_nat_add, f.commute_nat_add
-/
theorem commute_add_nat (n : Nat) : Function.Commute f (· + n) := by
  simp only [add_comm _ (n : Real), f.commute_nat_add n]

/--
theorem `commute_sub_nat` / 定理 `commute_sub_nat`

English:
theorem commute_sub_nat
  given: (n : Nat)
  statement: Function.Commute f (· - n)
  proof: by
  simpa only [sub_eq_add_neg] using!
    (f.commute_add_nat n).inverses_right (Equiv.addRight _).right_inv (Equiv.addRight _).left_inv

中文:
定理 commute_sub_nat
  条件: (n : 自然数)
  结论: 函数.Commute f (· - n)
  证明: by
  simpa only [sub_eq_add_neg] using!
    (f.commute_add_nat n).inverses_right (Equiv.addRight _).right_inv (Equiv.addRight _).left_inv

Depends on / 依赖: Equiv.addRight, addRight, commute_add_nat, f.commute_add_nat, inverses_right, left_inv, right_inv, sub_eq_add_neg
-/
theorem commute_sub_nat (n : Nat) : Function.Commute f (· - n) := by
  simpa only [sub_eq_add_neg] using!
    (f.commute_add_nat n).inverses_right (Equiv.addRight _).right_inv (Equiv.addRight _).left_inv

/--
theorem `commute_add_int` / 定理 `commute_add_int`

English:
theorem commute_add_int
  statement: forall n : Int, Function.Commute f (· + n)

中文:
定理 commute_add_int
  结论: 对任意 n : 整数, 函数.Commute f (· + n)
-/
theorem commute_add_int : forall n : Int, Function.Commute f (· + n)
  | (n : Nat) => f.commute_add_nat n
  | -[n+1] => by simpa [sub_eq_add_neg] using f.commute_sub_nat (n + 1)

/--
theorem `commute_int_add` / 定理 `commute_int_add`

English:
theorem commute_int_add
  given: (n : Int)
  statement: Function.Commute f (n + ·)
  proof: by
  simpa only [add_comm _ (n : Real)] using f.commute_add_int n

中文:
定理 commute_int_add
  条件: (n : 整数)
  结论: 函数.Commute f (n + ·)
  证明: by
  simpa only [add_comm _ (n : Real)] using f.commute_add_int n

Depends on / 依赖: add_comm, commute_add_int, f.commute_add_int
-/
theorem commute_int_add (n : Int) : Function.Commute f (n + ·) := by
  simpa only [add_comm _ (n : Real)] using f.commute_add_int n

/--
theorem `commute_sub_int` / 定理 `commute_sub_int`

English:
theorem commute_sub_int
  given: (n : Int)
  statement: Function.Commute f (· - n)
  proof: by
  simpa only [sub_eq_add_neg] using!
    (f.commute_add_int n).inverses_right (Equiv.addRight _).right_inv (Equiv.addRight _).left_inv

@[simp]

中文:
定理 commute_sub_int
  条件: (n : 整数)
  结论: 函数.Commute f (· - n)
  证明: by
  simpa only [sub_eq_add_neg] using!
    (f.commute_add_int n).inverses_right (Equiv.addRight _).right_inv (Equiv.addRight _).left_inv

@[simp]

Depends on / 依赖: Equiv.addRight, addRight, commute_add_int, f.commute_add_int, inverses_right, left_inv, right_inv, sub_eq_add_neg
-/
theorem commute_sub_int (n : Int) : Function.Commute f (· - n) := by
  simpa only [sub_eq_add_neg] using!
    (f.commute_add_int n).inverses_right (Equiv.addRight _).right_inv (Equiv.addRight _).left_inv

@[simp]
/--
theorem `map_int_add` / 定理 `map_int_add`

English:
theorem map_int_add
  given: (m : Int) (x : Real)
  statement: f (m + x) = m + f x
  proof: f.commute_int_add m x

@[simp]

中文:
定理 map_int_add
  条件: (m : 整数) (x : 实数)
  结论: f (m + x) = m + f x
  证明: f.commute_int_add m x

@[simp]

Depends on / 依赖: commute_int_add, f.commute_int_add
-/
theorem map_int_add (m : Int) (x : Real) : f (m + x) = m + f x :=
  f.commute_int_add m x

@[simp]
/--
theorem `map_add_int` / 定理 `map_add_int`

English:
theorem map_add_int
  given: (x : Real) (m : Int)
  statement: f (x + m) = f x + m
  proof: f.commute_add_int m x

@[simp]

中文:
定理 map_add_int
  条件: (x : 实数) (m : 整数)
  结论: f (x + m) = f x + m
  证明: f.commute_add_int m x

@[simp]

Depends on / 依赖: commute_add_int, f.commute_add_int
-/
theorem map_add_int (x : Real) (m : Int) : f (x + m) = f x + m :=
  f.commute_add_int m x

@[simp]
/--
theorem `map_sub_int` / 定理 `map_sub_int`

English:
theorem map_sub_int
  given: (x : Real) (n : Int)
  statement: f (x - n) = f x - n
  proof: f.commute_sub_int n x

@[simp]

中文:
定理 map_sub_int
  条件: (x : 实数) (n : 整数)
  结论: f (x - n) = f x - n
  证明: f.commute_sub_int n x

@[simp]

Depends on / 依赖: commute_sub_int, f.commute_sub_int
-/
theorem map_sub_int (x : Real) (n : Int) : f (x - n) = f x - n :=
  f.commute_sub_int n x

@[simp]
/--
theorem `map_add_nat` / 定理 `map_add_nat`

English:
theorem map_add_nat
  given: (x : Real) (n : Nat)
  statement: f (x + n) = f x + n
  proof: f.map_add_int x n

@[simp]

中文:
定理 map_add_nat
  条件: (x : 实数) (n : 自然数)
  结论: f (x + n) = f x + n
  证明: f.map_add_int x n

@[simp]

Depends on / 依赖: f.map_add_int, map_add_int
-/
theorem map_add_nat (x : Real) (n : Nat) : f (x + n) = f x + n :=
  f.map_add_int x n

@[simp]
/--
theorem `map_nat_add` / 定理 `map_nat_add`

English:
theorem map_nat_add
  given: (n : Nat) (x : Real)
  statement: f (n + x) = n + f x
  proof: f.map_int_add n x

@[simp]

中文:
定理 map_nat_add
  条件: (n : 自然数) (x : 实数)
  结论: f (n + x) = n + f x
  证明: f.map_int_add n x

@[simp]

Depends on / 依赖: f.map_int_add, map_int_add
-/
theorem map_nat_add (n : Nat) (x : Real) : f (n + x) = n + f x :=
  f.map_int_add n x

@[simp]
/--
theorem `map_sub_nat` / 定理 `map_sub_nat`

English:
theorem map_sub_nat
  given: (x : Real) (n : Nat)
  statement: f (x - n) = f x - n
  proof: f.map_sub_int x n

中文:
定理 map_sub_nat
  条件: (x : 实数) (n : 自然数)
  结论: f (x - n) = f x - n
  证明: f.map_sub_int x n

Depends on / 依赖: f.map_sub_int, map_sub_int
-/
theorem map_sub_nat (x : Real) (n : Nat) : f (x - n) = f x - n :=
  f.map_sub_int x n

/--
theorem `map_int_of_map_zero` / 定理 `map_int_of_map_zero`

English:
theorem map_int_of_map_zero
  given: (n : Int)
  statement: f n = f 0 + n
  proof: by rw [← f.map_add_int, zero_add]

@[simp]

中文:
定理 map_int_of_map_zero
  条件: (n : 整数)
  结论: f n = f 0 + n
  证明: by rw [← f.map_add_int, zero_add]

@[simp]

Depends on / 依赖: f.map_add_int, map_add_int, zero_add
-/
theorem map_int_of_map_zero (n : Int) : f n = f 0 + n := by rw [← f.map_add_int, zero_add]

@[simp]
/--
theorem `map_fract_sub_fract_eq` / 定理 `map_fract_sub_fract_eq`

English:
theorem map_fract_sub_fract_eq
  given: (x : Real)
  statement: f (fract x) - fract x = f x - x
  proof: by
  rw [Int.fract]; rw [f.map_sub_int]; rw [sub_sub_sub_cancel_right]

中文:
定理 map_fract_sub_fract_eq
  条件: (x : 实数)
  结论: f (fract x) - fract x = f x - x
  证明: by
  rw [Int.fract]; rw [f.map_sub_int]; rw [sub_sub_sub_cancel_right]

Depends on / 依赖: Int.fract, f.map_sub_int, map_sub_int, sub_sub_sub_cancel_right
-/
theorem map_fract_sub_fract_eq (x : Real) : f (fract x) - fract x = f x - x := by
  rw [Int.fract]; rw [f.map_sub_int]; rw [sub_sub_sub_cancel_right]

/-!
### Pointwise order on circle maps
-/


/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Lattice CircleDeg1Lift
  body: { toFun := fun x => max (f x) (g x)
      monotone' := fun _ _ h => max_le_max (f.mono h) (g.mono h)
      -- TODO: generalize to `Monotone.max`
      map_add_one' := fun x => by simp [max_add_add_right] }
  le f g := forall x, f x <= g x
  le_refl f x := le_refl (f x)
  le_trans _ _ _ h₁₂ h₂₃ x := le_trans (h₁₂ x) (h₂₃ x)
  le_antisymm _ _ h₁₂ h₂₁ := ext fun x => le_antisymm (h₁₂ x) (h₂₁ x)
  le_sup_left f g x := le_max_left (f x) (g x)
  le_sup_right f g x := le_max_right (f x) (g x)
  sup_le _ _ _ h₁ h₂ x := max_le (h₁ x) (h₂ x)
  inf f g :=
    { toFun := fun x => min (f x) (g x)
      monotone' := fun _ _ h => min_le_min (f.mono h) (g.mono h)
      map_add_one' := fun x => by simp [min_add_add_right] }
  inf_le_left f g x := min_le_left (f x) (g x)
  inf_le_right f g x := min_le_right (f x) (g x)
  le_inf _ _ _ h₂ h₃ x := le_min (h₂ x) (h₃ x)

@[simp]

中文:
实例 :
  签名: 格 CircleDeg1Lift
  定义体: { toFun := fun x => max (f x) (g x)
      monotone' := fun _ _ h => max_le_max (f.mono h) (g.mono h)
      -- TODO: generalize to `Monotone.max`
      map_add_one' := fun x => by simp [max_add_add_right] }
  le f g := forall x, f x <= g x
  le_refl f x := le_refl (f x)
  le_trans _ _ _ h₁₂ h₂₃ x := le_trans (h₁₂ x) (h₂₃ x)
  le_antisymm _ _ h₁₂ h₂₁ := ext fun x => le_antisymm (h₁₂ x) (h₂₁ x)
  le_sup_left f g x := le_max_left (f x) (g x)
  le_sup_right f g x := le_max_right (f x) (g x)
  sup_le _ _ _ h₁ h₂ x := max_le (h₁ x) (h₂ x)
  inf f g :=
    { toFun := fun x => min (f x) (g x)
      monotone' := fun _ _ h => min_le_min (f.mono h) (g.mono h)
      map_add_one' := fun x => by simp [min_add_add_right] }
  inf_le_left f g x := min_le_left (f x) (g x)
  inf_le_right f g x := min_le_right (f x) (g x)
  le_inf _ _ _ h₂ h₃ x := le_min (h₂ x) (h₃ x)

@[simp]

Depends on / 依赖: f.mono, g.mono, max_le_max, monotone
-/
noncomputable instance : Lattice CircleDeg1Lift where
  sup f g :=
    { toFun := fun x => max (f x) (g x)
      monotone' := fun _ _ h => max_le_max (f.mono h) (g.mono h)
      -- TODO: generalize to `Monotone.max`
      map_add_one' := fun x => by simp [max_add_add_right] }
  le f g := forall x, f x <= g x
  le_refl f x := le_refl (f x)
  le_trans _ _ _ h₁₂ h₂₃ x := le_trans (h₁₂ x) (h₂₃ x)
  le_antisymm _ _ h₁₂ h₂₁ := ext fun x => le_antisymm (h₁₂ x) (h₂₁ x)
  le_sup_left f g x := le_max_left (f x) (g x)
  le_sup_right f g x := le_max_right (f x) (g x)
  sup_le _ _ _ h₁ h₂ x := max_le (h₁ x) (h₂ x)
  inf f g :=
    { toFun := fun x => min (f x) (g x)
      monotone' := fun _ _ h => min_le_min (f.mono h) (g.mono h)
      map_add_one' := fun x => by simp [min_add_add_right] }
  inf_le_left f g x := min_le_left (f x) (g x)
  inf_le_right f g x := min_le_right (f x) (g x)
  le_inf _ _ _ h₂ h₃ x := le_min (h₂ x) (h₃ x)

@[simp]
/--
theorem `sup_apply` / 定理 `sup_apply`

English:
theorem sup_apply
  given: (x : Real)
  statement: (f ⊔ g) x = max (f x) (g x)
  proof: rfl

@[simp]

中文:
定理 sup_apply
  条件: (x : 实数)
  结论: (f ⊔ g) x = 最大值 (f x) (g x)
  证明: rfl

@[simp]
-/
theorem sup_apply (x : Real) : (f ⊔ g) x = max (f x) (g x) :=
  rfl

@[simp]
/--
theorem `inf_apply` / 定理 `inf_apply`

English:
theorem inf_apply
  given: (x : Real)
  statement: (f ⊓ g) x = min (f x) (g x)
  proof: rfl

中文:
定理 inf_apply
  条件: (x : 实数)
  结论: (f ⊓ g) x = 最小值 (f x) (g x)
  证明: rfl
-/
theorem inf_apply (x : Real) : (f ⊓ g) x = min (f x) (g x) :=
  rfl

/--
theorem `iterate_monotone` / 定理 `iterate_monotone`

English:
theorem iterate_monotone
  given: (n : Nat)
  statement: Monotone fun f : CircleDeg1Lift => f^[n]
  proof: fun f _ h =>
  f.monotone.iterate_le_of_le h _

中文:
定理 iterate_monotone
  条件: (n : 自然数)
  结论: 递增 fun f : CircleDeg1Lift => f^[n]
  证明: fun f _ h =>
  f.monotone.iterate_le_of_le h _
-/
theorem iterate_monotone (n : Nat) : Monotone fun f : CircleDeg1Lift => f^[n] := fun f _ h =>
  f.monotone.iterate_le_of_le h _

/--
theorem `iterate_mono` / 定理 `iterate_mono`

English:
theorem iterate_mono
  given: {f g : CircleDeg1Lift} (h : f <= g) (n : Nat)
  statement: f^[n] <= g^[n]
  proof: iterate_monotone n h

中文:
定理 iterate_mono
  条件: {f g : CircleDeg1Lift} (h : f <= g) (n : 自然数)
  结论: f^[n] <= g^[n]
  证明: iterate_monotone n h

Depends on / 依赖: iterate_monotone
-/
theorem iterate_mono {f g : CircleDeg1Lift} (h : f <= g) (n : Nat) : f^[n] <= g^[n] :=
  iterate_monotone n h

/--
theorem `pow_mono` / 定理 `pow_mono`

English:
theorem pow_mono
  given: {f g : CircleDeg1Lift} (h : f <= g) (n : Nat)
  statement: f ^ n <= g ^ n
  proof: fun x => by
  simp only [coe_pow, iterate_mono h n x]

中文:
定理 pow_mono
  条件: {f g : CircleDeg1Lift} (h : f <= g) (n : 自然数)
  结论: f ^ n <= g ^ n
  证明: fun x => by
  simp only [coe_pow, iterate_mono h n x]

Depends on / 依赖: coe_pow, iterate_mono
-/
theorem pow_mono {f g : CircleDeg1Lift} (h : f <= g) (n : Nat) : f ^ n <= g ^ n := fun x => by
  simp only [coe_pow, iterate_mono h n x]

/--
theorem `pow_monotone` / 定理 `pow_monotone`

English:
theorem pow_monotone
  given: (n : Nat)
  statement: Monotone fun f : CircleDeg1Lift => f ^ n
  proof: fun _ _ h => pow_mono h n

中文:
定理 pow_monotone
  条件: (n : 自然数)
  结论: 递增 fun f : CircleDeg1Lift => f ^ n
  证明: fun _ _ h => pow_mono h n

Depends on / 依赖: pow_mono
-/
theorem pow_monotone (n : Nat) : Monotone fun f : CircleDeg1Lift => f ^ n := fun _ _ h => pow_mono h n


/--
theorem `map_le_of_map_zero` / 定理 `map_le_of_map_zero`

English:
theorem map_le_of_map_zero
  given: (x : Real)
  statement: f x <= f 0 + ⌈x⌉
  proof: calc
f x <= f ⌈x⌉ := f.monotone le_ceil _
    _ = f 0 + ⌈x⌉ := f.map_int_of_map_zero _

中文:
定理 map_le_of_map_zero
  条件: (x : 实数)
  结论: f x <= f 0 + ⌈x⌉
  证明: calc
f x <= f ⌈x⌉ := f.monotone le_ceil _
    _ = f 0 + ⌈x⌉ := f.map_int_of_map_zero _

Depends on / 依赖: f.map_int_of_map_zero, f.monotone, le_ceil, map_int_of_map_zero, monotone
-/
theorem map_le_of_map_zero (x : Real) : f x <= f 0 + ⌈x⌉ :=
  calc
f x <= f ⌈x⌉ := f.monotone le_ceil _
    _ = f 0 + ⌈x⌉ := f.map_int_of_map_zero _

/--
theorem `map_map_zero_le` / 定理 `map_map_zero_le`

English:
theorem map_map_zero_le
  statement: f (g 0) <= f 0 + ⌈g 0⌉
  proof: f.map_le_of_map_zero (g 0)

中文:
定理 map_map_zero_le
  结论: f (g 0) <= f 0 + ⌈g 0⌉
  证明: f.map_le_of_map_zero (g 0)

Depends on / 依赖: f.map_le_of_map_zero, map_le_of_map_zero
-/
theorem map_map_zero_le : f (g 0) <= f 0 + ⌈g 0⌉ :=
  f.map_le_of_map_zero (g 0)

/--
theorem `floor_map_map_zero_le` / 定理 `floor_map_map_zero_le`

English:
theorem floor_map_map_zero_le
  statement: ⌊f (g 0)⌋ <= ⌊f 0⌋ + ⌈g 0⌉
  proof: calc
⌊f (g 0)⌋ <= ⌊f 0 + ⌈g 0⌉⌋ := floor_mono f.map_map_zero_le g
    _ = ⌊f 0⌋ + ⌈g 0⌉ := floor_add_intCast _ _

中文:
定理 floor_map_map_zero_le
  结论: ⌊f (g 0)⌋ <= ⌊f 0⌋ + ⌈g 0⌉
  证明: calc
⌊f (g 0)⌋ <= ⌊f 0 + ⌈g 0⌉⌋ := floor_mono f.map_map_zero_le g
    _ = ⌊f 0⌋ + ⌈g 0⌉ := floor_add_intCast _ _

Depends on / 依赖: f.map_map_zero_le, floor_add_intCast, floor_mono, map_map_zero_le
-/
theorem floor_map_map_zero_le : ⌊f (g 0)⌋ <= ⌊f 0⌋ + ⌈g 0⌉ :=
  calc
⌊f (g 0)⌋ <= ⌊f 0 + ⌈g 0⌉⌋ := floor_mono f.map_map_zero_le g
    _ = ⌊f 0⌋ + ⌈g 0⌉ := floor_add_intCast _ _

/--
theorem `ceil_map_map_zero_le` / 定理 `ceil_map_map_zero_le`

English:
theorem ceil_map_map_zero_le
  statement: ⌈f (g 0)⌉ <= ⌈f 0⌉ + ⌈g 0⌉
  proof: calc
⌈f (g 0)⌉ <= ⌈f 0 + ⌈g 0⌉⌉ := ceil_mono f.map_map_zero_le g
    _ = ⌈f 0⌉ + ⌈g 0⌉ := ceil_add_intCast _ _

中文:
定理 ceil_map_map_zero_le
  结论: ⌈f (g 0)⌉ <= ⌈f 0⌉ + ⌈g 0⌉
  证明: calc
⌈f (g 0)⌉ <= ⌈f 0 + ⌈g 0⌉⌉ := ceil_mono f.map_map_zero_le g
    _ = ⌈f 0⌉ + ⌈g 0⌉ := ceil_add_intCast _ _

Depends on / 依赖: ceil_add_intCast, ceil_mono, f.map_map_zero_le, map_map_zero_le
-/
theorem ceil_map_map_zero_le : ⌈f (g 0)⌉ <= ⌈f 0⌉ + ⌈g 0⌉ :=
  calc
⌈f (g 0)⌉ <= ⌈f 0 + ⌈g 0⌉⌉ := ceil_mono f.map_map_zero_le g
    _ = ⌈f 0⌉ + ⌈g 0⌉ := ceil_add_intCast _ _

/--
theorem `map_map_zero_lt` / 定理 `map_map_zero_lt`

English:
theorem map_map_zero_lt
  statement: f (g 0) < f 0 + g 0 + 1
  proof: calc
    f (g 0) <= f 0 + ⌈g 0⌉ := f.map_map_zero_le g
    _ < f 0 + (g 0 + 1) := by gcongr; exact ceil_lt_add_one _
    _ = f 0 + g 0 + 1 := (add_assoc _ _ _).symm

中文:
定理 map_map_zero_lt
  结论: f (g 0) < f 0 + g 0 + 1
  证明: calc
    f (g 0) <= f 0 + ⌈g 0⌉ := f.map_map_zero_le g
    _ < f 0 + (g 0 + 1) := by gcongr; exact ceil_lt_add_one _
    _ = f 0 + g 0 + 1 := (add_assoc _ _ _).symm

Depends on / 依赖: add_assoc, ceil_lt_add_one, f.map_map_zero_le, map_map_zero_le
-/
theorem map_map_zero_lt : f (g 0) < f 0 + g 0 + 1 :=
  calc
    f (g 0) <= f 0 + ⌈g 0⌉ := f.map_map_zero_le g
    _ < f 0 + (g 0 + 1) := by gcongr; exact ceil_lt_add_one _
    _ = f 0 + g 0 + 1 := (add_assoc _ _ _).symm

/--
theorem `le_map_of_map_zero` / 定理 `le_map_of_map_zero`

English:
theorem le_map_of_map_zero
  given: (x : Real)
  statement: f 0 + ⌊x⌋ <= f x
  proof: calc
    f 0 + ⌊x⌋ = f ⌊x⌋ := (f.map_int_of_map_zero _).symm
_ <= f x := f.monotone floor_le _

中文:
定理 le_map_of_map_zero
  条件: (x : 实数)
  结论: f 0 + ⌊x⌋ <= f x
  证明: calc
    f 0 + ⌊x⌋ = f ⌊x⌋ := (f.map_int_of_map_zero _).symm
_ <= f x := f.monotone floor_le _

Depends on / 依赖: f.map_int_of_map_zero, f.monotone, floor_le, map_int_of_map_zero, monotone
-/
theorem le_map_of_map_zero (x : Real) : f 0 + ⌊x⌋ <= f x :=
  calc
    f 0 + ⌊x⌋ = f ⌊x⌋ := (f.map_int_of_map_zero _).symm
_ <= f x := f.monotone floor_le _

/--
theorem `le_map_map_zero` / 定理 `le_map_map_zero`

English:
theorem le_map_map_zero
  statement: f 0 + ⌊g 0⌋ <= f (g 0)
  proof: f.le_map_of_map_zero (g 0)

中文:
定理 le_map_map_zero
  结论: f 0 + ⌊g 0⌋ <= f (g 0)
  证明: f.le_map_of_map_zero (g 0)

Depends on / 依赖: f.le_map_of_map_zero, le_map_of_map_zero
-/
theorem le_map_map_zero : f 0 + ⌊g 0⌋ <= f (g 0) :=
  f.le_map_of_map_zero (g 0)

/--
theorem `le_floor_map_map_zero` / 定理 `le_floor_map_map_zero`

English:
theorem le_floor_map_map_zero
  statement: ⌊f 0⌋ + ⌊g 0⌋ <= ⌊f (g 0)⌋
  proof: calc
    ⌊f 0⌋ + ⌊g 0⌋ = ⌊f 0 + ⌊g 0⌋⌋ := (floor_add_intCast _ _).symm
_ <= ⌊f (g 0)⌋ := floor_mono f.le_map_map_zero g

中文:
定理 le_floor_map_map_zero
  结论: ⌊f 0⌋ + ⌊g 0⌋ <= ⌊f (g 0)⌋
  证明: calc
    ⌊f 0⌋ + ⌊g 0⌋ = ⌊f 0 + ⌊g 0⌋⌋ := (floor_add_intCast _ _).symm
_ <= ⌊f (g 0)⌋ := floor_mono f.le_map_map_zero g

Depends on / 依赖: f.le_map_map_zero, floor_add_intCast, floor_mono, le_map_map_zero
-/
theorem le_floor_map_map_zero : ⌊f 0⌋ + ⌊g 0⌋ <= ⌊f (g 0)⌋ :=
  calc
    ⌊f 0⌋ + ⌊g 0⌋ = ⌊f 0 + ⌊g 0⌋⌋ := (floor_add_intCast _ _).symm
_ <= ⌊f (g 0)⌋ := floor_mono f.le_map_map_zero g

/--
theorem `le_ceil_map_map_zero` / 定理 `le_ceil_map_map_zero`

English:
theorem le_ceil_map_map_zero
  statement: ⌈f 0⌉ + ⌊g 0⌋ <= ⌈(f * g) 0⌉
  proof: calc
    ⌈f 0⌉ + ⌊g 0⌋ = ⌈f 0 + ⌊g 0⌋⌉ := (ceil_add_intCast _ _).symm
_ <= ⌈f (g 0)⌉ := ceil_mono f.le_map_map_zero g

中文:
定理 le_ceil_map_map_zero
  结论: ⌈f 0⌉ + ⌊g 0⌋ <= ⌈(f * g) 0⌉
  证明: calc
    ⌈f 0⌉ + ⌊g 0⌋ = ⌈f 0 + ⌊g 0⌋⌉ := (ceil_add_intCast _ _).symm
_ <= ⌈f (g 0)⌉ := ceil_mono f.le_map_map_zero g

Depends on / 依赖: ceil_add_intCast, ceil_mono, f.le_map_map_zero, le_map_map_zero
-/
theorem le_ceil_map_map_zero : ⌈f 0⌉ + ⌊g 0⌋ <= ⌈(f * g) 0⌉ :=
  calc
    ⌈f 0⌉ + ⌊g 0⌋ = ⌈f 0 + ⌊g 0⌋⌉ := (ceil_add_intCast _ _).symm
_ <= ⌈f (g 0)⌉ := ceil_mono f.le_map_map_zero g

/--
theorem `lt_map_map_zero` / 定理 `lt_map_map_zero`

English:
theorem lt_map_map_zero
  statement: f 0 + g 0 - 1 < f (g 0)
  proof: calc
    f 0 + g 0 - 1 = f 0 + (g 0 - 1) := add_sub_assoc _ _ _
    _ < f 0 + ⌊g 0⌋ := by gcongr; exact sub_one_lt_floor _
    _ <= f (g 0) := f.le_map_map_zero g

中文:
定理 lt_map_map_zero
  结论: f 0 + g 0 - 1 < f (g 0)
  证明: calc
    f 0 + g 0 - 1 = f 0 + (g 0 - 1) := add_sub_assoc _ _ _
    _ < f 0 + ⌊g 0⌋ := by gcongr; exact sub_one_lt_floor _
    _ <= f (g 0) := f.le_map_map_zero g

Depends on / 依赖: add_sub_assoc, f.le_map_map_zero, le_map_map_zero, sub_one_lt_floor
-/
theorem lt_map_map_zero : f 0 + g 0 - 1 < f (g 0) :=
  calc
    f 0 + g 0 - 1 = f 0 + (g 0 - 1) := add_sub_assoc _ _ _
    _ < f 0 + ⌊g 0⌋ := by gcongr; exact sub_one_lt_floor _
    _ <= f (g 0) := f.le_map_map_zero g

/--
theorem `dist_map_map_zero_lt` / 定理 `dist_map_map_zero_lt`

English:
theorem dist_map_map_zero_lt
  statement: dist (f 0 + g 0) (f (g 0)) < 1
  proof: by
  rw [dist_comm]; rw [Real.dist_eq]; rw [abs_lt]; rw [lt_sub_iff_add_lt']; rw [sub_lt_iff_lt_add']; rw [← sub_eq_add_neg]
  exact ⟨f.lt_map_map_zero g, f.map_map_zero_lt g⟩

中文:
定理 dist_map_map_zero_lt
  结论: dist (f 0 + g 0) (f (g 0)) < 1
  证明: by
  rw [dist_comm]; rw [Real.dist_eq]; rw [abs_lt]; rw [lt_sub_iff_add_lt']; rw [sub_lt_iff_lt_add']; rw [← sub_eq_add_neg]
  exact ⟨f.lt_map_map_zero g, f.map_map_zero_lt g⟩

Depends on / 依赖: Real.dist_eq, abs_lt, dist_comm, dist_eq, f.lt_map_map_zero, f.map_map_zero_lt, lt_map_map_zero, lt_sub_iff_add_lt, map_map_zero_lt, sub_eq_add_neg, sub_lt_iff_lt_add
-/
theorem dist_map_map_zero_lt : dist (f 0 + g 0) (f (g 0)) < 1 := by
  rw [dist_comm]; rw [Real.dist_eq]; rw [abs_lt]; rw [lt_sub_iff_add_lt']; rw [sub_lt_iff_lt_add']; rw [← sub_eq_add_neg]
  exact ⟨f.lt_map_map_zero g, f.map_map_zero_lt g⟩

/--
theorem `dist_map_zero_lt_of_semiconj` / 定理 `dist_map_zero_lt_of_semiconj`

English:
theorem dist_map_zero_lt_of_semiconj
  given: {f g₁ g₂ : CircleDeg1Lift} (h : Function.Semiconj f g₁ g₂)
  proof: calc
    dist (g₁ 0) (g₂ 0) <= dist (g₁ 0) (f (g₁ 0) - f 0) + dist _ (g₂ 0) := dist_triangle _ _ _
    _ = dist (f 0 + g₁ 0) (f (g₁ 0)) + dist (g₂ 0 + f 0) (g₂ (f 0)) := by
      simp only [h.eq, Real.dist_eq, sub_sub, add_comm (f 0), sub_sub_eq_add_sub,
        abs_sub_comm (g₂ (f 0))]
    _ < 1 + 1 := add_lt_add (f.dist_map_map_zero_lt g₁) (g₂.dist_map_map_zero_lt f)
    _ = 2 := one_add_one_eq_two

中文:
定理 dist_map_zero_lt_of_semiconj
  条件: {f g₁ g₂ : CircleDeg1Lift} (h : 函数.Semiconj f g₁ g₂)
  证明: calc
    dist (g₁ 0) (g₂ 0) <= dist (g₁ 0) (f (g₁ 0) - f 0) + dist _ (g₂ 0) := dist_triangle _ _ _
    _ = dist (f 0 + g₁ 0) (f (g₁ 0)) + dist (g₂ 0 + f 0) (g₂ (f 0)) := by
      simp only [h.eq, Real.dist_eq, sub_sub, add_comm (f 0), sub_sub_eq_add_sub,
        abs_sub_comm (g₂ (f 0))]
    _ < 1 + 1 := add_lt_add (f.dist_map_map_zero_lt g₁) (g₂.dist_map_map_zero_lt f)
    _ = 2 := one_add_one_eq_two

Depends on / 依赖: Real.dist_eq, abs_sub_comm, add_comm, add_lt_add, dist_eq, dist_map_map_zero_lt, dist_triangle, f.dist_map_map_zero_lt, h.eq, one_add_one_eq_two, sub_sub, sub_sub_eq_add_sub
-/
theorem dist_map_zero_lt_of_semiconj {f g₁ g₂ : CircleDeg1Lift} (h : Function.Semiconj f g₁ g₂) :
    dist (g₁ 0) (g₂ 0) < 2 :=
  calc
    dist (g₁ 0) (g₂ 0) <= dist (g₁ 0) (f (g₁ 0) - f 0) + dist _ (g₂ 0) := dist_triangle _ _ _
    _ = dist (f 0 + g₁ 0) (f (g₁ 0)) + dist (g₂ 0 + f 0) (g₂ (f 0)) := by
      simp only [h.eq, Real.dist_eq, sub_sub, add_comm (f 0), sub_sub_eq_add_sub,
        abs_sub_comm (g₂ (f 0))]
    _ < 1 + 1 := add_lt_add (f.dist_map_map_zero_lt g₁) (g₂.dist_map_map_zero_lt f)
    _ = 2 := one_add_one_eq_two

/--
theorem `dist_map_zero_lt_of_semiconjBy` / 定理 `dist_map_zero_lt_of_semiconjBy`

English:
theorem dist_map_zero_lt_of_semiconjBy
  given: {f g₁ g₂ : CircleDeg1Lift} (h : SemiconjBy f g₁ g₂)
  proof: dist_map_zero_lt_of_semiconj semiconjBy_iff_semiconj.1 h

中文:
定理 dist_map_zero_lt_of_semiconjBy
  条件: {f g₁ g₂ : CircleDeg1Lift} (h : SemiconjBy f g₁ g₂)
  证明: dist_map_zero_lt_of_semiconj semiconjBy_iff_semiconj.1 h

Depends on / 依赖: dist_map_zero_lt_of_semiconj, semiconjBy_iff_semiconj
-/
theorem dist_map_zero_lt_of_semiconjBy {f g₁ g₂ : CircleDeg1Lift} (h : SemiconjBy f g₁ g₂) :
    dist (g₁ 0) (g₂ 0) < 2 :=
dist_map_zero_lt_of_semiconj semiconjBy_iff_semiconj.1 h


/--
theorem `tendsto_atBot` / 定理 `tendsto_atBot`

English:
theorem tendsto_atBot
  statement: Tendsto f atBot atBot
  proof: tendsto_atBot_mono f.map_le_of_map_zero tendsto_atBot_add_const_left _ _
(tendsto_atBot_mono fun x => (ceil_lt_add_one x).le)
      tendsto_atBot_add_const_right _ _ tendsto_id

中文:
定理 tendsto_atBot
  结论: 收敛 f atBot atBot
  证明: tendsto_atBot_mono f.map_le_of_map_zero tendsto_atBot_add_const_left _ _
(tendsto_atBot_mono fun x => (ceil_lt_add_one x).le)
      tendsto_atBot_add_const_right _ _ tendsto_id
-/
protected theorem tendsto_atBot : Tendsto f atBot atBot :=
tendsto_atBot_mono f.map_le_of_map_zero tendsto_atBot_add_const_left _ _
(tendsto_atBot_mono fun x => (ceil_lt_add_one x).le)
      tendsto_atBot_add_const_right _ _ tendsto_id

/--
theorem `tendsto_atTop` / 定理 `tendsto_atTop`

English:
theorem tendsto_atTop
  statement: Tendsto f atTop atTop
  proof: tendsto_atTop_mono f.le_map_of_map_zero tendsto_atTop_add_const_left _ _
(tendsto_atTop_mono fun x => (sub_one_lt_floor x).le) by
      simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right _ _ tendsto_id

中文:
定理 tendsto_atTop
  结论: 收敛 f atTop atTop
  证明: tendsto_atTop_mono f.le_map_of_map_zero tendsto_atTop_add_const_left _ _
(tendsto_atTop_mono fun x => (sub_one_lt_floor x).le) by
      simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right _ _ tendsto_id
-/
protected theorem tendsto_atTop : Tendsto f atTop atTop :=
tendsto_atTop_mono f.le_map_of_map_zero tendsto_atTop_add_const_left _ _
(tendsto_atTop_mono fun x => (sub_one_lt_floor x).le) by
      simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right _ _ tendsto_id

/--
theorem `continuous_iff_surjective` / 定理 `continuous_iff_surjective`

English:
theorem continuous_iff_surjective
  statement: Continuous f ↔ Function.Surjective f
  proof: ⟨fun h => h.surjective f.tendsto_atTop f.tendsto_atBot, f.monotone.continuous_of_surjective⟩

中文:
定理 continuous_iff_surjective
  结论: 连续 f ↔ 函数.满射 f
  证明: ⟨fun h => h.surjective f.tendsto_atTop f.tendsto_atBot, f.monotone.continuous_of_surjective⟩

Depends on / 依赖: continuous_of_surjective, f.monotone.continuous_of_surjective, f.tendsto_atBot, f.tendsto_atTop, h.surjective, monotone, surjective, tendsto_atBot, tendsto_atTop
-/
theorem continuous_iff_surjective : Continuous f ↔ Function.Surjective f :=
  ⟨fun h => h.surjective f.tendsto_atTop f.tendsto_atBot, f.monotone.continuous_of_surjective⟩



/--
theorem `iterate_le_of_map_le_add_int` / 定理 `iterate_le_of_map_le_add_int`

English:
theorem iterate_le_of_map_le_add_int
  given: {x : Real} {m : Int} (h : f x <= x + m) (n : Nat)
  proof: by
  simpa only [nsmul_eq_mul, add_right_iterate] using
    (f.commute_add_int m).iterate_le_of_map_le f.monotone (monotone_id.add_const (m : Real)) h n

中文:
定理 iterate_le_of_map_le_add_int
  条件: {x : 实数} {m : 整数} (h : f x <= x + m) (n : 自然数)
  证明: by
  simpa only [nsmul_eq_mul, add_right_iterate] using
    (f.commute_add_int m).iterate_le_of_map_le f.monotone (monotone_id.add_const (m : Real)) h n

Depends on / 依赖: add_const, add_right_iterate, commute_add_int, f.commute_add_int, f.monotone, iterate_le_of_map_le, monotone, monotone_id, monotone_id.add_const, nsmul_eq_mul
-/
theorem iterate_le_of_map_le_add_int {x : Real} {m : Int} (h : f x <= x + m) (n : Nat) :
    f^[n] x <= x + n * m := by
  simpa only [nsmul_eq_mul, add_right_iterate] using
    (f.commute_add_int m).iterate_le_of_map_le f.monotone (monotone_id.add_const (m : Real)) h n

/--
theorem `le_iterate_of_add_int_le_map` / 定理 `le_iterate_of_add_int_le_map`

English:
theorem le_iterate_of_add_int_le_map
  given: {x : Real} {m : Int} (h : x + m <= f x) (n : Nat)
  proof: by
  simpa only [nsmul_eq_mul, add_right_iterate] using
    (f.commute_add_int m).symm.iterate_le_of_map_le (monotone_id.add_const (m : Real)) f.monotone h n

中文:
定理 le_iterate_of_add_int_le_map
  条件: {x : 实数} {m : 整数} (h : x + m <= f x) (n : 自然数)
  证明: by
  simpa only [nsmul_eq_mul, add_right_iterate] using
    (f.commute_add_int m).symm.iterate_le_of_map_le (monotone_id.add_const (m : Real)) f.monotone h n

Depends on / 依赖: add_const, add_right_iterate, commute_add_int, f.commute_add_int, f.monotone, iterate_le_of_map_le, monotone, monotone_id, monotone_id.add_const, nsmul_eq_mul, symm.iterate_le_of_map_le
-/
theorem le_iterate_of_add_int_le_map {x : Real} {m : Int} (h : x + m <= f x) (n : Nat) :
    x + n * m <= f^[n] x := by
  simpa only [nsmul_eq_mul, add_right_iterate] using
    (f.commute_add_int m).symm.iterate_le_of_map_le (monotone_id.add_const (m : Real)) f.monotone h n

/--
theorem `iterate_eq_of_map_eq_add_int` / 定理 `iterate_eq_of_map_eq_add_int`

English:
theorem iterate_eq_of_map_eq_add_int
  given: {x : Real} {m : Int} (h : f x = x + m) (n : Nat)
  proof: by
  simpa only [nsmul_eq_mul, add_right_iterate] using (f.commute_add_int m).iterate_eq_of_map_eq n h

中文:
定理 iterate_eq_of_map_eq_add_int
  条件: {x : 实数} {m : 整数} (h : f x = x + m) (n : 自然数)
  证明: by
  simpa only [nsmul_eq_mul, add_right_iterate] using (f.commute_add_int m).iterate_eq_of_map_eq n h

Depends on / 依赖: add_right_iterate, commute_add_int, f.commute_add_int, iterate_eq_of_map_eq, nsmul_eq_mul
-/
theorem iterate_eq_of_map_eq_add_int {x : Real} {m : Int} (h : f x = x + m) (n : Nat) :
    f^[n] x = x + n * m := by
  simpa only [nsmul_eq_mul, add_right_iterate] using (f.commute_add_int m).iterate_eq_of_map_eq n h

/--
theorem `iterate_pos_le_iff` / 定理 `iterate_pos_le_iff`

English:
theorem iterate_pos_le_iff
  given: {x : Real} {m : Int} {n : Nat} (hn : 0 < n)
  proof: by
  simpa only [nsmul_eq_mul, add_right_iterate] using
    (f.commute_add_int m).iterate_pos_le_iff_map_le f.monotone (strictMono_id.add_const (m : Real)) hn

中文:
定理 iterate_pos_le_iff
  条件: {x : 实数} {m : 整数} {n : 自然数} (hn : 0 < n)
  证明: by
  simpa only [nsmul_eq_mul, add_right_iterate] using
    (f.commute_add_int m).iterate_pos_le_iff_map_le f.monotone (strictMono_id.add_const (m : Real)) hn

Depends on / 依赖: add_const, add_right_iterate, commute_add_int, f.commute_add_int, f.monotone, iterate_pos_le_iff_map_le, monotone, nsmul_eq_mul, strictMono_id, strictMono_id.add_const
-/
theorem iterate_pos_le_iff {x : Real} {m : Int} {n : Nat} (hn : 0 < n) :
    f^[n] x <= x + n * m ↔ f x <= x + m := by
  simpa only [nsmul_eq_mul, add_right_iterate] using
    (f.commute_add_int m).iterate_pos_le_iff_map_le f.monotone (strictMono_id.add_const (m : Real)) hn

/--
theorem `iterate_pos_lt_iff` / 定理 `iterate_pos_lt_iff`

English:
theorem iterate_pos_lt_iff
  given: {x : Real} {m : Int} {n : Nat} (hn : 0 < n)
  proof: by
  simpa only [nsmul_eq_mul, add_right_iterate] using
    (f.commute_add_int m).iterate_pos_lt_iff_map_lt f.monotone (strictMono_id.add_const (m : Real)) hn

中文:
定理 iterate_pos_lt_iff
  条件: {x : 实数} {m : 整数} {n : 自然数} (hn : 0 < n)
  证明: by
  simpa only [nsmul_eq_mul, add_right_iterate] using
    (f.commute_add_int m).iterate_pos_lt_iff_map_lt f.monotone (strictMono_id.add_const (m : Real)) hn

Depends on / 依赖: add_const, add_right_iterate, commute_add_int, f.commute_add_int, f.monotone, iterate_pos_lt_iff_map_lt, monotone, nsmul_eq_mul, strictMono_id, strictMono_id.add_const
-/
theorem iterate_pos_lt_iff {x : Real} {m : Int} {n : Nat} (hn : 0 < n) :
    f^[n] x < x + n * m ↔ f x < x + m := by
  simpa only [nsmul_eq_mul, add_right_iterate] using
    (f.commute_add_int m).iterate_pos_lt_iff_map_lt f.monotone (strictMono_id.add_const (m : Real)) hn

/--
theorem `iterate_pos_eq_iff` / 定理 `iterate_pos_eq_iff`

English:
theorem iterate_pos_eq_iff
  given: {x : Real} {m : Int} {n : Nat} (hn : 0 < n)
  proof: by
  simpa only [nsmul_eq_mul, add_right_iterate] using
    (f.commute_add_int m).iterate_pos_eq_iff_map_eq f.monotone (strictMono_id.add_const (m : Real)) hn

中文:
定理 iterate_pos_eq_iff
  条件: {x : 实数} {m : 整数} {n : 自然数} (hn : 0 < n)
  证明: by
  simpa only [nsmul_eq_mul, add_right_iterate] using
    (f.commute_add_int m).iterate_pos_eq_iff_map_eq f.monotone (strictMono_id.add_const (m : Real)) hn

Depends on / 依赖: add_const, add_right_iterate, commute_add_int, f.commute_add_int, f.monotone, iterate_pos_eq_iff_map_eq, monotone, nsmul_eq_mul, strictMono_id, strictMono_id.add_const
-/
theorem iterate_pos_eq_iff {x : Real} {m : Int} {n : Nat} (hn : 0 < n) :
    f^[n] x = x + n * m ↔ f x = x + m := by
  simpa only [nsmul_eq_mul, add_right_iterate] using
    (f.commute_add_int m).iterate_pos_eq_iff_map_eq f.monotone (strictMono_id.add_const (m : Real)) hn

/--
theorem `le_iterate_pos_iff` / 定理 `le_iterate_pos_iff`

English:
theorem le_iterate_pos_iff
  given: {x : Real} {m : Int} {n : Nat} (hn : 0 < n)
  proof: by
  simpa only [not_lt] using not_congr (f.iterate_pos_lt_iff hn)

中文:
定理 le_iterate_pos_iff
  条件: {x : 实数} {m : 整数} {n : 自然数} (hn : 0 < n)
  证明: by
  simpa only [not_lt] using not_congr (f.iterate_pos_lt_iff hn)

Depends on / 依赖: f.iterate_pos_lt_iff, iterate_pos_lt_iff, not_congr, not_lt
-/
theorem le_iterate_pos_iff {x : Real} {m : Int} {n : Nat} (hn : 0 < n) :
    x + n * m <= f^[n] x ↔ x + m <= f x := by
  simpa only [not_lt] using not_congr (f.iterate_pos_lt_iff hn)

/--
theorem `lt_iterate_pos_iff` / 定理 `lt_iterate_pos_iff`

English:
theorem lt_iterate_pos_iff
  given: {x : Real} {m : Int} {n : Nat} (hn : 0 < n)
  proof: by
  simpa only [not_le] using not_congr (f.iterate_pos_le_iff hn)

中文:
定理 lt_iterate_pos_iff
  条件: {x : 实数} {m : 整数} {n : 自然数} (hn : 0 < n)
  证明: by
  simpa only [not_le] using not_congr (f.iterate_pos_le_iff hn)

Depends on / 依赖: f.iterate_pos_le_iff, iterate_pos_le_iff, not_congr, not_le
-/
theorem lt_iterate_pos_iff {x : Real} {m : Int} {n : Nat} (hn : 0 < n) :
    x + n * m < f^[n] x ↔ x + m < f x := by
  simpa only [not_le] using not_congr (f.iterate_pos_le_iff hn)

/--
theorem `mul_floor_map_zero_le_floor_iterate_zero` / 定理 `mul_floor_map_zero_le_floor_iterate_zero`

English:
theorem mul_floor_map_zero_le_floor_iterate_zero
  given: (n : Nat)
  statement: ↑n * ⌊f 0⌋ <= ⌊f^[n] 0⌋
  proof: by
  rw [le_floor]; rw [Int.cast_mul]; rw [Int.cast_natCast]; rw [← zero_add ((n : Real) * _)]
  apply le_iterate_of_add_int_le_map
  simp [floor_le]

中文:
定理 mul_floor_map_zero_le_floor_iterate_zero
  条件: (n : 自然数)
  结论: ↑n * ⌊f 0⌋ <= ⌊f^[n] 0⌋
  证明: by
  rw [le_floor]; rw [Int.cast_mul]; rw [Int.cast_natCast]; rw [← zero_add ((n : Real) * _)]
  apply le_iterate_of_add_int_le_map
  simp [floor_le]

Depends on / 依赖: Int.cast_mul, Int.cast_natCast, cast_mul, cast_natCast, floor_le, le_floor, le_iterate_of_add_int_le_map, zero_add
-/
theorem mul_floor_map_zero_le_floor_iterate_zero (n : Nat) : ↑n * ⌊f 0⌋ <= ⌊f^[n] 0⌋ := by
  rw [le_floor]; rw [Int.cast_mul]; rw [Int.cast_natCast]; rw [← zero_add ((n : Real) * _)]
  apply le_iterate_of_add_int_le_map
  simp [floor_le]

/-!
### Definition of translation number
-/

noncomputable section

/--
Definition of `transnumAuxSeq` / `transnumAuxSeq` 的定义

English:
definition transnumAuxSeq
  signature: (n : Nat)
  body: (f ^ (2 ^ n : Nat)) 0 / 2 ^ n

中文:
定义 transnumAuxSeq
  签名: (n : 自然数)
  定义体: (f ^ (2 ^ n : Nat)) 0 / 2 ^ n
-/
def transnumAuxSeq (n : Nat) : Real :=
  (f ^ (2 ^ n : Nat)) 0 / 2 ^ n

/--
Definition of `translationNumber` / `translationNumber` 的定义

English:
definition translationNumber
  signature: : Real
  body: limUnder atTop f.transnumAuxSeq

中文:
定义 translationNumber
  签名: : 实数
  定义体: limUnder atTop f.transnumAuxSeq

Depends on / 依赖: f.transnumAuxSeq, limUnder, transnumAuxSeq
-/
def translationNumber : Real :=
  limUnder atTop f.transnumAuxSeq

end

-- TODO: choose two different symbols for `CircleDeg1Lift.translationNumber` and the future
-- `circle_mono_homeo.rotation_number`, then make them `localized notation`s
local notation "τ" => translationNumber

/--
theorem `transnumAuxSeq_def` / 定理 `transnumAuxSeq_def`

English:
theorem transnumAuxSeq_def
  statement: f.transnumAuxSeq = fun n : Nat => (f ^ (2 ^ n : Nat)) 0 / 2 ^ n
  proof: rfl

中文:
定理 transnumAuxSeq_def
  结论: f.transnumAuxSeq = fun n : 自然数 => (f ^ (2 ^ n : 自然数)) 0 / 2 ^ n
  证明: rfl
-/
theorem transnumAuxSeq_def : f.transnumAuxSeq = fun n : Nat => (f ^ (2 ^ n : Nat)) 0 / 2 ^ n :=
  rfl

/--
theorem `translationNumber_eq_of_tendsto_aux` / 定理 `translationNumber_eq_of_tendsto_aux`

English:
theorem translationNumber_eq_of_tendsto_aux
  given: {τ' : Real} (h : Tendsto f.transnumAuxSeq atTop (𝓝 τ'))
  proof: h.limUnder_eq

中文:
定理 translationNumber_eq_of_tendsto_aux
  条件: {τ' : 实数} (h : 收敛 f.transnumAuxSeq atTop (𝓝 τ'))
  证明: h.limUnder_eq

Depends on / 依赖: IsMultiplyPreprimitive, IsMultiplyPreprimitive.isMultiplyPretransitive, h.limUnder_eq, isMultiplyPretransitive, limUnder_eq
-/
theorem translationNumber_eq_of_tendsto_aux {τ' : Real} (h : Tendsto f.transnumAuxSeq atTop (𝓝 τ')) :
    τ f = τ' :=
  h.limUnder_eq

/--
theorem `translationNumber_eq_of_tendsto₀` / 定理 `translationNumber_eq_of_tendsto₀`

English:
theorem translationNumber_eq_of_tendsto₀
  statement: {τ' : Real}
  proof: f.translationNumber_eq_of_tendsto_aux by
    simpa [Function.comp_def, transnumAuxSeq_def, coe_pow] using
      h.comp (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)

中文:
定理 translationNumber_eq_of_tendsto₀
  结论: {τ' : 实数}
  证明: f.translationNumber_eq_of_tendsto_aux by
    simpa [Function.comp_def, transnumAuxSeq_def, coe_pow] using
      h.comp (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)

Depends on / 依赖: Function, Function.comp_def, coe_pow, comp_def, f.translationNumber_eq_of_tendsto_aux, h.comp, one_lt_two, tendsto_pow_atTop_atTop_of_one_lt, translationNumber_eq_of_tendsto_aux, transnumAuxSeq_def
-/
theorem translationNumber_eq_of_tendsto₀ {τ' : Real}
    (h : Tendsto (fun n : Nat => f^[n] 0 / n) atTop (𝓝 τ')) : τ f = τ' :=
f.translationNumber_eq_of_tendsto_aux by
    simpa [Function.comp_def, transnumAuxSeq_def, coe_pow] using
      h.comp (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)

/--
theorem `translationNumber_eq_of_tendsto₀'` / 定理 `translationNumber_eq_of_tendsto₀'`

English:
theorem translationNumber_eq_of_tendsto₀'
  statement: {τ' : Real}
  proof: f.translationNumber_eq_of_tendsto₀ (tendsto_add_atTop_iff_nat 1).1 (mod_cast h)

中文:
定理 translationNumber_eq_of_tendsto₀'
  结论: {τ' : 实数}
  证明: f.translationNumber_eq_of_tendsto₀ (tendsto_add_atTop_iff_nat 1).1 (mod_cast h)

Depends on / 依赖: f.translationNumber_eq_of_tendsto, mod_cast, tendsto_add_atTop_iff_nat
-/
theorem translationNumber_eq_of_tendsto₀' {τ' : Real}
    (h : Tendsto (fun n : Nat => f^[n + 1] 0 / (n + 1)) atTop (𝓝 τ')) : τ f = τ' :=
f.translationNumber_eq_of_tendsto₀ (tendsto_add_atTop_iff_nat 1).1 (mod_cast h)

/--
theorem `transnumAuxSeq_zero` / 定理 `transnumAuxSeq_zero`

English:
theorem transnumAuxSeq_zero
  statement: f.transnumAuxSeq 0 = f 0
  proof: by simp [transnumAuxSeq]

中文:
定理 transnumAuxSeq_zero
  结论: f.transnumAuxSeq 0 = f 0
  证明: by simp [transnumAuxSeq]

Depends on / 依赖: transnumAuxSeq
-/
theorem transnumAuxSeq_zero : f.transnumAuxSeq 0 = f 0 := by simp [transnumAuxSeq]

/--
theorem `transnumAuxSeq_dist_lt` / 定理 `transnumAuxSeq_dist_lt`

English:
theorem transnumAuxSeq_dist_lt
  given: (n : Nat)
  proof: by
  have : 0 < (2 ^ (n + 1) : Real) := pow_pos zero_lt_two _
  rw [div_div]; rw [← pow_succ']; rw [← abs_of_pos this]
  calc
    _ = dist ((f ^ 2 ^ n) 0 + (f ^ 2 ^ n) 0) ((f ^ 2 ^ n) ((f ^ 2 ^ n) 0)) / |2 ^ (n + 1)| := by
      simp_rw [transnumAuxSeq, Real.dist_eq]
      rw [← abs_div]; rw [sub_div]; rw [pow_succ]; rw [pow_succ']; rw [← two_mul]; rw [mul_div_mul_left _ _ (two_ne_zero' Real)]; rw [pow_mul]; rw [sq]; rw [mul_apply]
    _ < _ := by gcongr; exact (f ^ 2 ^ n).dist_map_map_zero_lt (f ^ 2 ^ n)

中文:
定理 transnumAuxSeq_dist_lt
  条件: (n : 自然数)
  证明: by
  have : 0 < (2 ^ (n + 1) : Real) := pow_pos zero_lt_two _
  rw [div_div]; rw [← pow_succ']; rw [← abs_of_pos this]
  calc
    _ = dist ((f ^ 2 ^ n) 0 + (f ^ 2 ^ n) 0) ((f ^ 2 ^ n) ((f ^ 2 ^ n) 0)) / |2 ^ (n + 1)| := by
      simp_rw [transnumAuxSeq, Real.dist_eq]
      rw [← abs_div]; rw [sub_div]; rw [pow_succ]; rw [pow_succ']; rw [← two_mul]; rw [mul_div_mul_left _ _ (two_ne_zero' Real)]; rw [pow_mul]; rw [sq]; rw [mul_apply]
    _ < _ := by gcongr; exact (f ^ 2 ^ n).dist_map_map_zero_lt (f ^ 2 ^ n)

Depends on / 依赖: Real.dist_eq, abs_div, abs_of_pos, dist_eq, dist_map_map_zero_lt, div_div, mul_apply, mul_div_mul_left, pow_mul, pow_pos, pow_succ, simp_rw, sub_div, transnumAuxSeq, two_mul, two_ne_zero, zero_lt_two
-/
theorem transnumAuxSeq_dist_lt (n : Nat) :
    dist (f.transnumAuxSeq n) (f.transnumAuxSeq (n + 1)) < 1 / 2 / 2 ^ n := by
  have : 0 < (2 ^ (n + 1) : Real) := pow_pos zero_lt_two _
  rw [div_div]; rw [← pow_succ']; rw [← abs_of_pos this]
  calc
    _ = dist ((f ^ 2 ^ n) 0 + (f ^ 2 ^ n) 0) ((f ^ 2 ^ n) ((f ^ 2 ^ n) 0)) / |2 ^ (n + 1)| := by
      simp_rw [transnumAuxSeq, Real.dist_eq]
      rw [← abs_div]; rw [sub_div]; rw [pow_succ]; rw [pow_succ']; rw [← two_mul]; rw [mul_div_mul_left _ _ (two_ne_zero' Real)]; rw [pow_mul]; rw [sq]; rw [mul_apply]
    _ < _ := by gcongr; exact (f ^ 2 ^ n).dist_map_map_zero_lt (f ^ 2 ^ n)

/--
theorem `tendsto_translationNumber_aux` / 定理 `tendsto_translationNumber_aux`

English:
theorem tendsto_translationNumber_aux
  statement: Tendsto f.transnumAuxSeq atTop (𝓝 <| τ f)
  proof: (cauchySeq_of_le_geometric_two fun n => le_of_lt <| f.transnumAuxSeq_dist_lt n).tendsto_limUnder

中文:
定理 tendsto_translationNumber_aux
  结论: 收敛 f.transnumAuxSeq atTop (𝓝 <| τ f)
  证明: (cauchySeq_of_le_geometric_two fun n => le_of_lt <| f.transnumAuxSeq_dist_lt n).tendsto_limUnder

Depends on / 依赖: cauchySeq_of_le_geometric_two, f.transnumAuxSeq_dist_lt, le_of_lt, tendsto_limUnder, transnumAuxSeq_dist_lt
-/
theorem tendsto_translationNumber_aux : Tendsto f.transnumAuxSeq atTop (𝓝 <| τ f) :=
  (cauchySeq_of_le_geometric_two fun n => le_of_lt <| f.transnumAuxSeq_dist_lt n).tendsto_limUnder

/--
theorem `dist_map_zero_translationNumber_le` / 定理 `dist_map_zero_translationNumber_le`

English:
theorem dist_map_zero_translationNumber_le
  statement: dist (f 0) (τ f) <= 1
  proof: f.transnumAuxSeq_zero ▸
    dist_le_of_le_geometric_two_of_tendsto₀ (fun n => le_of_lt <| f.transnumAuxSeq_dist_lt n)
      f.tendsto_translationNumber_aux

中文:
定理 dist_map_zero_translationNumber_le
  结论: dist (f 0) (τ f) <= 1
  证明: f.transnumAuxSeq_zero ▸
    dist_le_of_le_geometric_two_of_tendsto₀ (fun n => le_of_lt <| f.transnumAuxSeq_dist_lt n)
      f.tendsto_translationNumber_aux

Depends on / 依赖: f.tendsto_translationNumber_aux, f.transnumAuxSeq_dist_lt, f.transnumAuxSeq_zero, le_of_lt, tendsto_translationNumber_aux, transnumAuxSeq_dist_lt, transnumAuxSeq_zero
-/
theorem dist_map_zero_translationNumber_le : dist (f 0) (τ f) <= 1 :=
  f.transnumAuxSeq_zero ▸
    dist_le_of_le_geometric_two_of_tendsto₀ (fun n => le_of_lt <| f.transnumAuxSeq_dist_lt n)
      f.tendsto_translationNumber_aux

/--
theorem `tendsto_translationNumber_of_dist_bounded_aux` / 定理 `tendsto_translationNumber_of_dist_bounded_aux`

English:
theorem tendsto_translationNumber_of_dist_bounded_aux
  statement: (x : Nat -> Real) (C : Real)
  proof: by
  apply f.tendsto_translationNumber_aux.congr_dist (squeeze_zero (fun _ => dist_nonneg) _ _)
  · exact fun n => C / 2 ^ n
  · intro n
    have : 0 < (2 ^ n : Real) := pow_pos zero_lt_two _
    convert! (div_le_div_iff_of_pos_right this).2 (H (2 ^ n)) using 1
    rw [transnumAuxSeq]; rw [Real.dist_eq]; rw [← sub_div]; rw [abs_div]; rw [abs_of_pos this]; rw [Real.dist_eq]
· exact mul_zero C ▸ tendsto_const_nhds.mul tendsto_inv_atTop_zero.comp
      tendsto_pow_atTop_atTop_of_one_lt one_lt_two

中文:
定理 tendsto_translationNumber_of_dist_bounded_aux
  结论: (x : 自然数 -> 实数) (C : 实数)
  证明: by
  apply f.tendsto_translationNumber_aux.congr_dist (squeeze_zero (fun _ => dist_nonneg) _ _)
  · exact fun n => C / 2 ^ n
  · intro n
    have : 0 < (2 ^ n : Real) := pow_pos zero_lt_two _
    convert! (div_le_div_iff_of_pos_right this).2 (H (2 ^ n)) using 1
    rw [transnumAuxSeq]; rw [Real.dist_eq]; rw [← sub_div]; rw [abs_div]; rw [abs_of_pos this]; rw [Real.dist_eq]
· exact mul_zero C ▸ tendsto_const_nhds.mul tendsto_inv_atTop_zero.comp
      tendsto_pow_atTop_atTop_of_one_lt one_lt_two

Depends on / 依赖: Real.dist_eq, abs_div, abs_of_pos, congr_dist, convert, dist_eq, dist_nonneg, div_le_div_iff_of_pos_right, f.tendsto_translationNumber_aux.congr_dist, mul_zero, one_lt_two, pow_pos, squeeze_zero, sub_div, tendsto_const_nhds, tendsto_const_nhds.mul, tendsto_inv_atTop_zero, tendsto_inv_atTop_zero.comp, tendsto_pow_atTop_atTop_of_one_lt, tendsto_translationNumber_aux
-/
theorem tendsto_translationNumber_of_dist_bounded_aux (x : Nat -> Real) (C : Real)
    (H : forall n : Nat, dist ((f ^ n) 0) (x n) <= C) :
    Tendsto (fun n : Nat => x (2 ^ n) / 2 ^ n) atTop (𝓝 <| τ f) := by
  apply f.tendsto_translationNumber_aux.congr_dist (squeeze_zero (fun _ => dist_nonneg) _ _)
  · exact fun n => C / 2 ^ n
  · intro n
    have : 0 < (2 ^ n : Real) := pow_pos zero_lt_two _
    convert! (div_le_div_iff_of_pos_right this).2 (H (2 ^ n)) using 1
    rw [transnumAuxSeq]; rw [Real.dist_eq]; rw [← sub_div]; rw [abs_div]; rw [abs_of_pos this]; rw [Real.dist_eq]
· exact mul_zero C ▸ tendsto_const_nhds.mul tendsto_inv_atTop_zero.comp
      tendsto_pow_atTop_atTop_of_one_lt one_lt_two

/--
theorem `translationNumber_eq_of_dist_bounded` / 定理 `translationNumber_eq_of_dist_bounded`

English:
theorem translationNumber_eq_of_dist_bounded
  statement: {f g : CircleDeg1Lift} (C : Real)
  proof: Eq.symm g.translationNumber_eq_of_tendsto_aux
    f.tendsto_translationNumber_of_dist_bounded_aux (fun n => (g ^ n) 0) C H

@[simp]

中文:
定理 translationNumber_eq_of_dist_bounded
  结论: {f g : CircleDeg1Lift} (C : 实数)
  证明: Eq.symm g.translationNumber_eq_of_tendsto_aux
    f.tendsto_translationNumber_of_dist_bounded_aux (fun n => (g ^ n) 0) C H

@[simp]

Depends on / 依赖: Eq.symm, f.tendsto_translationNumber_of_dist_bounded_aux, g.translationNumber_eq_of_tendsto_aux, tendsto_translationNumber_of_dist_bounded_aux, translationNumber_eq_of_tendsto_aux
-/
theorem translationNumber_eq_of_dist_bounded {f g : CircleDeg1Lift} (C : Real)
    (H : forall n : Nat, dist ((f ^ n) 0) ((g ^ n) 0) <= C) : τ f = τ g :=
Eq.symm g.translationNumber_eq_of_tendsto_aux
    f.tendsto_translationNumber_of_dist_bounded_aux (fun n => (g ^ n) 0) C H

@[simp]
/--
theorem `translationNumber_one` / 定理 `translationNumber_one`

English:
theorem translationNumber_one
  statement: τ 1 = 0
  proof: translationNumber_eq_of_tendsto₀ _ by simp

中文:
定理 translationNumber_one
  结论: τ 1 = 0
  证明: translationNumber_eq_of_tendsto₀ _ by simp
-/
theorem translationNumber_one : τ 1 = 0 :=
translationNumber_eq_of_tendsto₀ _ by simp

/--
theorem `translationNumber_eq_of_semiconjBy` / 定理 `translationNumber_eq_of_semiconjBy`

English:
theorem translationNumber_eq_of_semiconjBy
  given: {f g₁ g₂ : CircleDeg1Lift} (H : SemiconjBy f g₁ g₂)
  proof: translationNumber_eq_of_dist_bounded 2 fun n =>
le_of_lt dist_map_zero_lt_of_semiconjBy H.pow_right n

中文:
定理 translationNumber_eq_of_semiconjBy
  条件: {f g₁ g₂ : CircleDeg1Lift} (H : SemiconjBy f g₁ g₂)
  证明: translationNumber_eq_of_dist_bounded 2 fun n =>
le_of_lt dist_map_zero_lt_of_semiconjBy H.pow_right n

Depends on / 依赖: H.pow_right, dist_map_zero_lt_of_semiconjBy, le_of_lt, pow_right, translationNumber_eq_of_dist_bounded
-/
theorem translationNumber_eq_of_semiconjBy {f g₁ g₂ : CircleDeg1Lift} (H : SemiconjBy f g₁ g₂) :
    τ g₁ = τ g₂ :=
  translationNumber_eq_of_dist_bounded 2 fun n =>
le_of_lt dist_map_zero_lt_of_semiconjBy H.pow_right n

/--
theorem `translationNumber_eq_of_semiconj` / 定理 `translationNumber_eq_of_semiconj`

English:
theorem translationNumber_eq_of_semiconj
  statement: {f g₁ g₂ : CircleDeg1Lift}
  proof: translationNumber_eq_of_semiconjBy semiconjBy_iff_semiconj.2 H

中文:
定理 translationNumber_eq_of_semiconj
  结论: {f g₁ g₂ : CircleDeg1Lift}
  证明: translationNumber_eq_of_semiconjBy semiconjBy_iff_semiconj.2 H

Depends on / 依赖: semiconjBy_iff_semiconj, translationNumber_eq_of_semiconjBy
-/
theorem translationNumber_eq_of_semiconj {f g₁ g₂ : CircleDeg1Lift}
    (H : Function.Semiconj f g₁ g₂) : τ g₁ = τ g₂ :=
translationNumber_eq_of_semiconjBy semiconjBy_iff_semiconj.2 H

/--
theorem `translationNumber_mul_of_commute` / 定理 `translationNumber_mul_of_commute`

English:
theorem translationNumber_mul_of_commute
  given: {f g : CircleDeg1Lift} (h : Commute f g)
  proof: by
  refine tendsto_nhds_unique ?_
    (f.tendsto_translationNumber_aux.add g.tendsto_translationNumber_aux)
  simp only [transnumAuxSeq, ← add_div]
  refine (f * g).tendsto_translationNumber_of_dist_bounded_aux
    (fun n => (f ^ n) 0 + (g ^ n) 0) 1 fun n => ?_
  rw [h.mul_pow]; rw [dist_comm]
  exact le_of_lt ((f ^ n).dist_map_map_zero_lt (g ^ n))

@[simp]

中文:
定理 translationNumber_mul_of_commute
  条件: {f g : CircleDeg1Lift} (h : Commute f g)
  证明: by
  refine tendsto_nhds_unique ?_
    (f.tendsto_translationNumber_aux.add g.tendsto_translationNumber_aux)
  simp only [transnumAuxSeq, ← add_div]
  refine (f * g).tendsto_translationNumber_of_dist_bounded_aux
    (fun n => (f ^ n) 0 + (g ^ n) 0) 1 fun n => ?_
  rw [h.mul_pow]; rw [dist_comm]
  exact le_of_lt ((f ^ n).dist_map_map_zero_lt (g ^ n))

@[simp]

Depends on / 依赖: add_div, dist_comm, dist_map_map_zero_lt, f.tendsto_translationNumber_aux.add, g.tendsto_translationNumber_aux, h.mul_pow, le_of_lt, mul_pow, tendsto_nhds_unique, tendsto_translationNumber_aux, tendsto_translationNumber_of_dist_bounded_aux, transnumAuxSeq
-/
theorem translationNumber_mul_of_commute {f g : CircleDeg1Lift} (h : Commute f g) :
    τ (f * g) = τ f + τ g := by
  refine tendsto_nhds_unique ?_
    (f.tendsto_translationNumber_aux.add g.tendsto_translationNumber_aux)
  simp only [transnumAuxSeq, ← add_div]
  refine (f * g).tendsto_translationNumber_of_dist_bounded_aux
    (fun n => (f ^ n) 0 + (g ^ n) 0) 1 fun n => ?_
  rw [h.mul_pow]; rw [dist_comm]
  exact le_of_lt ((f ^ n).dist_map_map_zero_lt (g ^ n))

@[simp]
/--
theorem `translationNumber_units_inv` / 定理 `translationNumber_units_inv`

English:
theorem translationNumber_units_inv
  given: (f : CircleDeg1Liftˣ)
  statement: τ ↑f⁻¹ = -τ f
  proof: eq_neg_iff_add_eq_zero.2 by
    simp [← translationNumber_mul_of_commute (Commute.refl _).units_inv_left]

@[simp]

中文:
定理 translationNumber_units_inv
  条件: (f : CircleDeg1Liftˣ)
  结论: τ ↑f⁻¹ = -τ f
  证明: eq_neg_iff_add_eq_zero.2 by
    simp [← translationNumber_mul_of_commute (Commute.refl _).units_inv_left]

@[simp]

Depends on / 依赖: Commute, Commute.refl, eq_neg_iff_add_eq_zero, translationNumber_mul_of_commute, units_inv_left
-/
theorem translationNumber_units_inv (f : CircleDeg1Liftˣ) : τ ↑f⁻¹ = -τ f :=
eq_neg_iff_add_eq_zero.2 by
    simp [← translationNumber_mul_of_commute (Commute.refl _).units_inv_left]

@[simp]
/--
theorem `translationNumber_pow` / 定理 `translationNumber_pow`

English:
theorem translationNumber_pow
  statement: forall n : Nat, τ (f ^ n) = n * τ f

中文:
定理 translationNumber_pow
  结论: 对任意 n : 自然数, τ (f ^ n) = n * τ f
-/
theorem translationNumber_pow : forall n : Nat, τ (f ^ n) = n * τ f
  | 0 => by simp
  | n + 1 => by
    rw [pow_succ]; rw [translationNumber_mul_of_commute (Commute.pow_self f n)]; rw [translationNumber_pow n]; rw [Nat.cast_add_one]; rw [add_mul]; rw [one_mul]

@[simp]
/--
theorem `translationNumber_zpow` / 定理 `translationNumber_zpow`

English:
theorem translationNumber_zpow
  given: (f : CircleDeg1Liftˣ)
  statement: forall n : Int, τ (f ^ n : Units _) = n * τ f

中文:
定理 translationNumber_zpow
  条件: (f : CircleDeg1Liftˣ)
  结论: 对任意 n : 整数, τ (f ^ n : 单位群 _) = n * τ f
-/
theorem translationNumber_zpow (f : CircleDeg1Liftˣ) : forall n : Int, τ (f ^ n : Units _) = n * τ f
  | (n : Nat) => by simp [translationNumber_pow f n]
  | -[n+1] => by simp; ring

@[simp]
/--
theorem `translationNumber_conj_eq` / 定理 `translationNumber_conj_eq`

English:
theorem translationNumber_conj_eq
  given: (f : CircleDeg1Liftˣ) (g : CircleDeg1Lift)
  proof: (translationNumber_eq_of_semiconjBy (f.mk_semiconjBy g)).symm

@[simp]

中文:
定理 translationNumber_conj_eq
  条件: (f : CircleDeg1Liftˣ) (g : CircleDeg1Lift)
  证明: (translationNumber_eq_of_semiconjBy (f.mk_semiconjBy g)).symm

@[simp]

Depends on / 依赖: f.mk_semiconjBy, mk_semiconjBy, translationNumber_eq_of_semiconjBy
-/
theorem translationNumber_conj_eq (f : CircleDeg1Liftˣ) (g : CircleDeg1Lift) :
    τ (↑f * g * ↑f⁻¹) = τ g :=
  (translationNumber_eq_of_semiconjBy (f.mk_semiconjBy g)).symm

@[simp]
/--
theorem `translationNumber_conj_eq'` / 定理 `translationNumber_conj_eq'`

English:
theorem translationNumber_conj_eq'
  given: (f : CircleDeg1Liftˣ) (g : CircleDeg1Lift)
  proof: translationNumber_conj_eq f⁻¹ g

中文:
定理 translationNumber_conj_eq'
  条件: (f : CircleDeg1Liftˣ) (g : CircleDeg1Lift)
  证明: translationNumber_conj_eq f⁻¹ g

Depends on / 依赖: translationNumber_conj_eq
-/
theorem translationNumber_conj_eq' (f : CircleDeg1Liftˣ) (g : CircleDeg1Lift) :
    τ (↑f⁻¹ * g * f) = τ g :=
  translationNumber_conj_eq f⁻¹ g

/--
theorem `dist_pow_map_zero_mul_translationNumber_le` / 定理 `dist_pow_map_zero_mul_translationNumber_le`

English:
theorem dist_pow_map_zero_mul_translationNumber_le
  given: (n : Nat)
  proof: f.translationNumber_pow n ▸ (f ^ n).dist_map_zero_translationNumber_le

中文:
定理 dist_pow_map_zero_mul_translationNumber_le
  条件: (n : 自然数)
  证明: f.translationNumber_pow n ▸ (f ^ n).dist_map_zero_translationNumber_le

Depends on / 依赖: dist_map_zero_translationNumber_le, f.translationNumber_pow, translationNumber_pow
-/
theorem dist_pow_map_zero_mul_translationNumber_le (n : Nat) :
    dist ((f ^ n) 0) (n * f.translationNumber) <= 1 :=
  f.translationNumber_pow n ▸ (f ^ n).dist_map_zero_translationNumber_le

/--
theorem `tendsto_translation_number₀'` / 定理 `tendsto_translation_number₀'`

English:
theorem tendsto_translation_number₀'
  proof: by
  refine
tendsto_iff_dist_tendsto_zero.2
      squeeze_zero (fun _ => dist_nonneg) (fun n => ?_)
        ((tendsto_const_div_atTop_nhds_zero_nat 1).comp (tendsto_add_atTop_nat 1))
  dsimp
  have : (0 : Real) < n + 1 := n.cast_add_one_pos
  rw [Real.dist_eq]; rw [div_sub' (ne_of_gt this)]; rw [abs_div]; rw [← Real.dist_eq]; rw [abs_of_pos this]; rw [Nat.cast_add_one]; rw [div_le_div_iff_of_pos_right this]; rw [← Nat.cast_add_one]
  apply dist_pow_map_zero_mul_translationNumber_le

中文:
定理 tendsto_translation_number₀'
  证明: by
  refine
tendsto_iff_dist_tendsto_zero.2
      squeeze_zero (fun _ => dist_nonneg) (fun n => ?_)
        ((tendsto_const_div_atTop_nhds_zero_nat 1).comp (tendsto_add_atTop_nat 1))
  dsimp
  have : (0 : Real) < n + 1 := n.cast_add_one_pos
  rw [Real.dist_eq]; rw [div_sub' (ne_of_gt this)]; rw [abs_div]; rw [← Real.dist_eq]; rw [abs_of_pos this]; rw [Nat.cast_add_one]; rw [div_le_div_iff_of_pos_right this]; rw [← Nat.cast_add_one]
  apply dist_pow_map_zero_mul_translationNumber_le

Depends on / 依赖: Nat.cast_add_one, Real.dist_eq, abs_div, abs_of_pos, cast_add_one, cast_add_one_pos, dist_eq, dist_nonneg, dist_pow_map_zero_mul_translationNumber_le, div_le_div_iff_of_pos_right, div_sub, n.cast_add_one_pos, ne_of_gt, squeeze_zero, tendsto_add_atTop_nat, tendsto_const_div_atTop_nhds_zero_nat, tendsto_iff_dist_tendsto_zero
-/
theorem tendsto_translation_number₀' :
    Tendsto (fun n : Nat => (f ^ (n + 1) : CircleDeg1Lift) 0 / ((n : Real) + 1)) atTop (𝓝 <| τ f) := by
  refine
tendsto_iff_dist_tendsto_zero.2
      squeeze_zero (fun _ => dist_nonneg) (fun n => ?_)
        ((tendsto_const_div_atTop_nhds_zero_nat 1).comp (tendsto_add_atTop_nat 1))
  dsimp
  have : (0 : Real) < n + 1 := n.cast_add_one_pos
  rw [Real.dist_eq]; rw [div_sub' (ne_of_gt this)]; rw [abs_div]; rw [← Real.dist_eq]; rw [abs_of_pos this]; rw [Nat.cast_add_one]; rw [div_le_div_iff_of_pos_right this]; rw [← Nat.cast_add_one]
  apply dist_pow_map_zero_mul_translationNumber_le

/--
theorem `tendsto_translation_number₀` / 定理 `tendsto_translation_number₀`

English:
theorem tendsto_translation_number₀
  statement: Tendsto (fun n : Nat => (f ^ n) 0 / n) atTop (𝓝 <| τ f)
  proof: (tendsto_add_atTop_iff_nat 1).1 (mod_cast f.tendsto_translation_number₀')

中文:
定理 tendsto_translation_number₀
  结论: 收敛 (fun n : 自然数 => (f ^ n) 0 / n) atTop (𝓝 <| τ f)
  证明: (tendsto_add_atTop_iff_nat 1).1 (mod_cast f.tendsto_translation_number₀')

Depends on / 依赖: f.tendsto_translation_number, mod_cast, tendsto_add_atTop_iff_nat
-/
theorem tendsto_translation_number₀ : Tendsto (fun n : Nat => (f ^ n) 0 / n) atTop (𝓝 <| τ f) :=
  (tendsto_add_atTop_iff_nat 1).1 (mod_cast f.tendsto_translation_number₀')

/--
theorem `tendsto_translationNumber` / 定理 `tendsto_translationNumber`

English:
theorem tendsto_translationNumber
  given: (x : Real)
  proof: by
  rw [← translationNumber_conj_eq' (translate <| Multiplicative.ofAdd x)]
  refine (tendsto_translation_number₀ _).congr fun n => ?_
  simp [sub_eq_neg_add, Units.conj_pow']

中文:
定理 tendsto_translationNumber
  条件: (x : 实数)
  证明: by
  rw [← translationNumber_conj_eq' (translate <| Multiplicative.ofAdd x)]
  refine (tendsto_translation_number₀ _).congr fun n => ?_
  simp [sub_eq_neg_add, Units.conj_pow']

Depends on / 依赖: Multiplicative, Multiplicative.ofAdd, Units.conj_pow, conj_pow, sub_eq_neg_add, translate, translationNumber_conj_eq
-/
theorem tendsto_translationNumber (x : Real) :
    Tendsto (fun n : Nat => ((f ^ n) x - x) / n) atTop (𝓝 <| τ f) := by
  rw [← translationNumber_conj_eq' (translate <| Multiplicative.ofAdd x)]
  refine (tendsto_translation_number₀ _).congr fun n => ?_
  simp [sub_eq_neg_add, Units.conj_pow']

/--
theorem `tendsto_translation_number'` / 定理 `tendsto_translation_number'`

English:
theorem tendsto_translation_number'
  given: (x : Real)
  proof: mod_cast (tendsto_add_atTop_iff_nat 1).2 (f.tendsto_translationNumber x)

中文:
定理 tendsto_translation_number'
  条件: (x : 实数)
  证明: mod_cast (tendsto_add_atTop_iff_nat 1).2 (f.tendsto_translationNumber x)

Depends on / 依赖: f.tendsto_translationNumber, mod_cast, tendsto_add_atTop_iff_nat, tendsto_translationNumber
-/
theorem tendsto_translation_number' (x : Real) :
    Tendsto (fun n : Nat => ((f ^ (n + 1) : CircleDeg1Lift) x - x) / (n + 1)) atTop (𝓝 <| τ f) :=
  mod_cast (tendsto_add_atTop_iff_nat 1).2 (f.tendsto_translationNumber x)

/--
theorem `translationNumber_mono` / 定理 `translationNumber_mono`

English:
theorem translationNumber_mono
  statement: Monotone τ
  proof: fun f g h =>
  le_of_tendsto_of_tendsto' f.tendsto_translation_number₀ g.tendsto_translation_number₀ fun n => by
    gcongr; exact pow_mono h _ _

中文:
定理 translationNumber_mono
  结论: 递增 τ
  证明: fun f g h =>
  le_of_tendsto_of_tendsto' f.tendsto_translation_number₀ g.tendsto_translation_number₀ fun n => by
    gcongr; exact pow_mono h _ _
-/
theorem translationNumber_mono : Monotone τ := fun f g h =>
  le_of_tendsto_of_tendsto' f.tendsto_translation_number₀ g.tendsto_translation_number₀ fun n => by
    gcongr; exact pow_mono h _ _

/--
theorem `translationNumber_translate` / 定理 `translationNumber_translate`

English:
theorem translationNumber_translate
  given: (x : Real)
  statement: τ (translate <| Multiplicative.ofAdd x) = x
  proof: translationNumber_eq_of_tendsto₀' _ by
    simp only [translate_iterate, translate_apply, add_zero, Nat.cast_succ,
      mul_div_cancel_left₀ (M₀ := Real) _ (Nat.cast_add_one_ne_zero _), tendsto_const_nhds]

中文:
定理 translationNumber_translate
  条件: (x : 实数)
  结论: τ (translate <| Multiplicative.ofAdd x) = x
  证明: translationNumber_eq_of_tendsto₀' _ by
    simp only [translate_iterate, translate_apply, add_zero, Nat.cast_succ,
      mul_div_cancel_left₀ (M₀ := Real) _ (Nat.cast_add_one_ne_zero _), tendsto_const_nhds]

Depends on / 依赖: Nat.cast_add_one_ne_zero, Nat.cast_succ, add_zero, cast_add_one_ne_zero, cast_succ, tendsto_const_nhds, translate_apply, translate_iterate
-/
theorem translationNumber_translate (x : Real) : τ (translate <| Multiplicative.ofAdd x) = x :=
translationNumber_eq_of_tendsto₀' _ by
    simp only [translate_iterate, translate_apply, add_zero, Nat.cast_succ,
      mul_div_cancel_left₀ (M₀ := Real) _ (Nat.cast_add_one_ne_zero _), tendsto_const_nhds]

/--
theorem `translationNumber_le_of_le_add` / 定理 `translationNumber_le_of_le_add`

English:
theorem translationNumber_le_of_le_add
  given: {z : Real} (hz : forall x, f x <= x + z)
  statement: τ f <= z
  proof: translationNumber_translate z ▸ translationNumber_mono fun x => (hz x).trans_eq (add_comm _ _)

中文:
定理 translationNumber_le_of_le_add
  条件: {z : 实数} (hz : 对任意 x, f x <= x + z)
  结论: τ f <= z
  证明: translationNumber_translate z ▸ translationNumber_mono fun x => (hz x).trans_eq (add_comm _ _)

Depends on / 依赖: add_comm, trans_eq, translationNumber_mono, translationNumber_translate
-/
theorem translationNumber_le_of_le_add {z : Real} (hz : forall x, f x <= x + z) : τ f <= z :=
  translationNumber_translate z ▸ translationNumber_mono fun x => (hz x).trans_eq (add_comm _ _)

/--
theorem `le_translationNumber_of_add_le` / 定理 `le_translationNumber_of_add_le`

English:
theorem le_translationNumber_of_add_le
  given: {z : Real} (hz : forall x, x + z <= f x)
  statement: z <= τ f
  proof: translationNumber_translate z ▸ translationNumber_mono fun x => (add_comm _ _).trans_le (hz x)

中文:
定理 le_translationNumber_of_add_le
  条件: {z : 实数} (hz : 对任意 x, x + z <= f x)
  结论: z <= τ f
  证明: translationNumber_translate z ▸ translationNumber_mono fun x => (add_comm _ _).trans_le (hz x)

Depends on / 依赖: add_comm, trans_le, translationNumber_mono, translationNumber_translate
-/
theorem le_translationNumber_of_add_le {z : Real} (hz : forall x, x + z <= f x) : z <= τ f :=
  translationNumber_translate z ▸ translationNumber_mono fun x => (add_comm _ _).trans_le (hz x)

/--
theorem `translationNumber_le_of_le_add_int` / 定理 `translationNumber_le_of_le_add_int`

English:
theorem translationNumber_le_of_le_add_int
  given: {x : Real} {m : Int} (h : f x <= x + m)
  statement: τ f <= m
  proof: le_of_tendsto' (f.tendsto_translation_number' x) fun n =>
(div_le_iff₀' (n.cast_add_one_pos : (0 : Real) < _)).mpr sub_le_iff_le_add'.2
      (coe_pow f (n + 1)).symm ▸ @Nat.cast_add_one Real _ n ▸ f.iterate_le_of_map_le_add_int h (n + 1)

中文:
定理 translationNumber_le_of_le_add_int
  条件: {x : 实数} {m : 整数} (h : f x <= x + m)
  结论: τ f <= m
  证明: le_of_tendsto' (f.tendsto_translation_number' x) fun n =>
(div_le_iff₀' (n.cast_add_one_pos : (0 : Real) < _)).mpr sub_le_iff_le_add'.2
      (coe_pow f (n + 1)).symm ▸ @Nat.cast_add_one Real _ n ▸ f.iterate_le_of_map_le_add_int h (n + 1)

Depends on / 依赖: Nat.cast_add_one, cast_add_one, cast_add_one_pos, coe_pow, f.iterate_le_of_map_le_add_int, f.tendsto_translation_number, iterate_le_of_map_le_add_int, le_of_tendsto, n.cast_add_one_pos, sub_le_iff_le_add, tendsto_translation_number
-/
theorem translationNumber_le_of_le_add_int {x : Real} {m : Int} (h : f x <= x + m) : τ f <= m :=
  le_of_tendsto' (f.tendsto_translation_number' x) fun n =>
(div_le_iff₀' (n.cast_add_one_pos : (0 : Real) < _)).mpr sub_le_iff_le_add'.2
      (coe_pow f (n + 1)).symm ▸ @Nat.cast_add_one Real _ n ▸ f.iterate_le_of_map_le_add_int h (n + 1)

/--
theorem `translationNumber_le_of_le_add_nat` / 定理 `translationNumber_le_of_le_add_nat`

English:
theorem translationNumber_le_of_le_add_nat
  given: {x : Real} {m : Nat} (h : f x <= x + m)
  statement: τ f <= m
  proof: @translationNumber_le_of_le_add_int f x m h

中文:
定理 translationNumber_le_of_le_add_nat
  条件: {x : 实数} {m : 自然数} (h : f x <= x + m)
  结论: τ f <= m
  证明: @translationNumber_le_of_le_add_int f x m h

Depends on / 依赖: translationNumber_le_of_le_add_int
-/
theorem translationNumber_le_of_le_add_nat {x : Real} {m : Nat} (h : f x <= x + m) : τ f <= m :=
  @translationNumber_le_of_le_add_int f x m h

/--
theorem `le_translationNumber_of_add_int_le` / 定理 `le_translationNumber_of_add_int_le`

English:
theorem le_translationNumber_of_add_int_le
  given: {x : Real} {m : Int} (h : x + m <= f x)
  statement: ↑m <= τ f
  proof: ge_of_tendsto' (f.tendsto_translation_number' x) fun n =>
(le_div_iff₀ (n.cast_add_one_pos : (0 : Real) < _)).mpr le_sub_iff_add_le'.2 by
      simp only [coe_pow, mul_comm (m : Real), ← Nat.cast_add_one, f.le_iterate_of_add_int_le_map h]

中文:
定理 le_translationNumber_of_add_int_le
  条件: {x : 实数} {m : 整数} (h : x + m <= f x)
  结论: ↑m <= τ f
  证明: ge_of_tendsto' (f.tendsto_translation_number' x) fun n =>
(le_div_iff₀ (n.cast_add_one_pos : (0 : Real) < _)).mpr le_sub_iff_add_le'.2 by
      simp only [coe_pow, mul_comm (m : Real), ← Nat.cast_add_one, f.le_iterate_of_add_int_le_map h]

Depends on / 依赖: Nat.cast_add_one, cast_add_one, cast_add_one_pos, coe_pow, f.le_iterate_of_add_int_le_map, f.tendsto_translation_number, ge_of_tendsto, le_iterate_of_add_int_le_map, le_sub_iff_add_le, mul_comm, n.cast_add_one_pos, tendsto_translation_number
-/
theorem le_translationNumber_of_add_int_le {x : Real} {m : Int} (h : x + m <= f x) : ↑m <= τ f :=
  ge_of_tendsto' (f.tendsto_translation_number' x) fun n =>
(le_div_iff₀ (n.cast_add_one_pos : (0 : Real) < _)).mpr le_sub_iff_add_le'.2 by
      simp only [coe_pow, mul_comm (m : Real), ← Nat.cast_add_one, f.le_iterate_of_add_int_le_map h]

/--
theorem `le_translationNumber_of_add_nat_le` / 定理 `le_translationNumber_of_add_nat_le`

English:
theorem le_translationNumber_of_add_nat_le
  given: {x : Real} {m : Nat} (h : x + m <= f x)
  statement: ↑m <= τ f
  proof: @le_translationNumber_of_add_int_le f x m h

中文:
定理 le_translationNumber_of_add_nat_le
  条件: {x : 实数} {m : 自然数} (h : x + m <= f x)
  结论: ↑m <= τ f
  证明: @le_translationNumber_of_add_int_le f x m h

Depends on / 依赖: le_translationNumber_of_add_int_le
-/
theorem le_translationNumber_of_add_nat_le {x : Real} {m : Nat} (h : x + m <= f x) : ↑m <= τ f :=
  @le_translationNumber_of_add_int_le f x m h

/--
theorem `translationNumber_of_eq_add_int` / 定理 `translationNumber_of_eq_add_int`

English:
theorem translationNumber_of_eq_add_int
  given: {x : Real} {m : Int} (h : f x = x + m)
  statement: τ f = m
  proof: le_antisymm (translationNumber_le_of_le_add_int f <| le_of_eq h)
    (le_translationNumber_of_add_int_le f <| le_of_eq h.symm)

中文:
定理 translationNumber_of_eq_add_int
  条件: {x : 实数} {m : 整数} (h : f x = x + m)
  结论: τ f = m
  证明: le_antisymm (translationNumber_le_of_le_add_int f <| le_of_eq h)
    (le_translationNumber_of_add_int_le f <| le_of_eq h.symm)

Depends on / 依赖: h.symm, le_antisymm, le_of_eq, le_translationNumber_of_add_int_le, translationNumber_le_of_le_add_int
-/
theorem translationNumber_of_eq_add_int {x : Real} {m : Int} (h : f x = x + m) : τ f = m :=
  le_antisymm (translationNumber_le_of_le_add_int f <| le_of_eq h)
    (le_translationNumber_of_add_int_le f <| le_of_eq h.symm)

/--
theorem `floor_sub_le_translationNumber` / 定理 `floor_sub_le_translationNumber`

English:
theorem floor_sub_le_translationNumber
  given: (x : Real)
  statement: ↑⌊f x - x⌋ <= τ f
  proof: le_translationNumber_of_add_int_le f le_sub_iff_add_le'.1 (floor_le <| f x - x)

中文:
定理 floor_sub_le_translationNumber
  条件: (x : 实数)
  结论: ↑⌊f x - x⌋ <= τ f
  证明: le_translationNumber_of_add_int_le f le_sub_iff_add_le'.1 (floor_le <| f x - x)

Depends on / 依赖: floor_le, le_sub_iff_add_le, le_translationNumber_of_add_int_le
-/
theorem floor_sub_le_translationNumber (x : Real) : ↑⌊f x - x⌋ <= τ f :=
le_translationNumber_of_add_int_le f le_sub_iff_add_le'.1 (floor_le <| f x - x)

/--
theorem `translationNumber_le_ceil_sub` / 定理 `translationNumber_le_ceil_sub`

English:
theorem translationNumber_le_ceil_sub
  given: (x : Real)
  statement: τ f <= ⌈f x - x⌉
  proof: translationNumber_le_of_le_add_int f sub_le_iff_le_add'.1 (le_ceil <| f x - x)

中文:
定理 translationNumber_le_ceil_sub
  条件: (x : 实数)
  结论: τ f <= ⌈f x - x⌉
  证明: translationNumber_le_of_le_add_int f sub_le_iff_le_add'.1 (le_ceil <| f x - x)

Depends on / 依赖: le_ceil, sub_le_iff_le_add, translationNumber_le_of_le_add_int
-/
theorem translationNumber_le_ceil_sub (x : Real) : τ f <= ⌈f x - x⌉ :=
translationNumber_le_of_le_add_int f sub_le_iff_le_add'.1 (le_ceil <| f x - x)

/--
theorem `map_lt_of_translationNumber_lt_int` / 定理 `map_lt_of_translationNumber_lt_int`

English:
theorem map_lt_of_translationNumber_lt_int
  given: {n : Int} (h : τ f < n) (x : Real)
  statement: f x < x + n
  proof: not_le.1 mt f.le_translationNumber_of_add_int_le not_le.2 h

中文:
定理 map_lt_of_translationNumber_lt_int
  条件: {n : 整数} (h : τ f < n) (x : 实数)
  结论: f x < x + n
  证明: not_le.1 mt f.le_translationNumber_of_add_int_le not_le.2 h

Depends on / 依赖: f.le_translationNumber_of_add_int_le, le_translationNumber_of_add_int_le, not_le
-/
theorem map_lt_of_translationNumber_lt_int {n : Int} (h : τ f < n) (x : Real) : f x < x + n :=
not_le.1 mt f.le_translationNumber_of_add_int_le not_le.2 h

/--
theorem `map_lt_of_translationNumber_lt_nat` / 定理 `map_lt_of_translationNumber_lt_nat`

English:
theorem map_lt_of_translationNumber_lt_nat
  given: {n : Nat} (h : τ f < n) (x : Real)
  statement: f x < x + n
  proof: @map_lt_of_translationNumber_lt_int f n h x

中文:
定理 map_lt_of_translationNumber_lt_nat
  条件: {n : 自然数} (h : τ f < n) (x : 实数)
  结论: f x < x + n
  证明: @map_lt_of_translationNumber_lt_int f n h x

Depends on / 依赖: map_lt_of_translationNumber_lt_int
-/
theorem map_lt_of_translationNumber_lt_nat {n : Nat} (h : τ f < n) (x : Real) : f x < x + n :=
  @map_lt_of_translationNumber_lt_int f n h x

/--
theorem `map_lt_add_floor_translationNumber_add_one` / 定理 `map_lt_add_floor_translationNumber_add_one`

English:
theorem map_lt_add_floor_translationNumber_add_one
  given: (x : Real)
  statement: f x < x + ⌊τ f⌋ + 1
  proof: by
  rw [add_assoc]
  norm_cast
  refine map_lt_of_translationNumber_lt_int _ ?_ _
  push_cast
  exact lt_floor_add_one _

中文:
定理 map_lt_add_floor_translationNumber_add_one
  条件: (x : 实数)
  结论: f x < x + ⌊τ f⌋ + 1
  证明: by
  rw [add_assoc]
  norm_cast
  refine map_lt_of_translationNumber_lt_int _ ?_ _
  push_cast
  exact lt_floor_add_one _

Depends on / 依赖: add_assoc, lt_floor_add_one, map_lt_of_translationNumber_lt_int
-/
theorem map_lt_add_floor_translationNumber_add_one (x : Real) : f x < x + ⌊τ f⌋ + 1 := by
  rw [add_assoc]
  norm_cast
  refine map_lt_of_translationNumber_lt_int _ ?_ _
  push_cast
  exact lt_floor_add_one _

/--
theorem `map_lt_add_translationNumber_add_one` / 定理 `map_lt_add_translationNumber_add_one`

English:
theorem map_lt_add_translationNumber_add_one
  given: (x : Real)
  statement: f x < x + τ f + 1
  proof: calc
    f x < x + ⌊τ f⌋ + 1 := f.map_lt_add_floor_translationNumber_add_one x
    _ <= x + τ f + 1 := by gcongr; apply floor_le

中文:
定理 map_lt_add_translationNumber_add_one
  条件: (x : 实数)
  结论: f x < x + τ f + 1
  证明: calc
    f x < x + ⌊τ f⌋ + 1 := f.map_lt_add_floor_translationNumber_add_one x
    _ <= x + τ f + 1 := by gcongr; apply floor_le

Depends on / 依赖: f.map_lt_add_floor_translationNumber_add_one, floor_le, map_lt_add_floor_translationNumber_add_one
-/
theorem map_lt_add_translationNumber_add_one (x : Real) : f x < x + τ f + 1 :=
  calc
    f x < x + ⌊τ f⌋ + 1 := f.map_lt_add_floor_translationNumber_add_one x
    _ <= x + τ f + 1 := by gcongr; apply floor_le

/--
theorem `lt_map_of_int_lt_translationNumber` / 定理 `lt_map_of_int_lt_translationNumber`

English:
theorem lt_map_of_int_lt_translationNumber
  given: {n : Int} (h : ↑n < τ f) (x : Real)
  statement: x + n < f x
  proof: not_le.1 mt f.translationNumber_le_of_le_add_int not_le.2 h

中文:
定理 lt_map_of_int_lt_translationNumber
  条件: {n : 整数} (h : ↑n < τ f) (x : 实数)
  结论: x + n < f x
  证明: not_le.1 mt f.translationNumber_le_of_le_add_int not_le.2 h

Depends on / 依赖: f.translationNumber_le_of_le_add_int, not_le, translationNumber_le_of_le_add_int
-/
theorem lt_map_of_int_lt_translationNumber {n : Int} (h : ↑n < τ f) (x : Real) : x + n < f x :=
not_le.1 mt f.translationNumber_le_of_le_add_int not_le.2 h

/--
theorem `lt_map_of_nat_lt_translationNumber` / 定理 `lt_map_of_nat_lt_translationNumber`

English:
theorem lt_map_of_nat_lt_translationNumber
  given: {n : Nat} (h : ↑n < τ f) (x : Real)
  statement: x + n < f x
  proof: @lt_map_of_int_lt_translationNumber f n h x

中文:
定理 lt_map_of_nat_lt_translationNumber
  条件: {n : 自然数} (h : ↑n < τ f) (x : 实数)
  结论: x + n < f x
  证明: @lt_map_of_int_lt_translationNumber f n h x

Depends on / 依赖: lt_map_of_int_lt_translationNumber
-/
theorem lt_map_of_nat_lt_translationNumber {n : Nat} (h : ↑n < τ f) (x : Real) : x + n < f x :=
  @lt_map_of_int_lt_translationNumber f n h x

/--
theorem `translationNumber_of_map_pow_eq_add_int` / 定理 `translationNumber_of_map_pow_eq_add_int`

English:
theorem translationNumber_of_map_pow_eq_add_int
  statement: {x : Real} {n : Nat} {m : Int} (h : (f ^ n) x = x + m)
  proof: by
  have := (f ^ n).translationNumber_of_eq_add_int h
  rwa [translationNumber_pow, mul_comm, ← eq_div_iff] at this
  exact Nat.cast_ne_zero.2 (ne_of_gt hn)

中文:
定理 translationNumber_of_map_pow_eq_add_int
  结论: {x : 实数} {n : 自然数} {m : 整数} (h : (f ^ n) x = x + m)
  证明: by
  have := (f ^ n).translationNumber_of_eq_add_int h
  rwa [translationNumber_pow, mul_comm, ← eq_div_iff] at this
  exact Nat.cast_ne_zero.2 (ne_of_gt hn)

Depends on / 依赖: Nat.cast_ne_zero, cast_ne_zero, eq_div_iff, mul_comm, ne_of_gt, translationNumber_of_eq_add_int, translationNumber_pow
-/
theorem translationNumber_of_map_pow_eq_add_int {x : Real} {n : Nat} {m : Int} (h : (f ^ n) x = x + m)
    (hn : 0 < n) : τ f = m / n := by
  have := (f ^ n).translationNumber_of_eq_add_int h
  rwa [translationNumber_pow, mul_comm, ← eq_div_iff] at this
  exact Nat.cast_ne_zero.2 (ne_of_gt hn)

/--
theorem `forall_map_sub_of_Icc` / 定理 `forall_map_sub_of_Icc`

English:
theorem forall_map_sub_of_Icc
  given: (P : Real -> Prop) (h : forall x in Icc (0 : Real) 1, P (f x - x)) (x : Real)
  proof: f.map_fract_sub_fract_eq x ▸ h _ ⟨fract_nonneg _, le_of_lt (fract_lt_one _)⟩

中文:
定理 对任意_map_sub_of_Icc
  条件: (P : 实数 -> 命题) (h : 对任意 x in 闭区间 (0 : 实数) 1, P (f x - x)) (x : 实数)
  证明: f.map_fract_sub_fract_eq x ▸ h _ ⟨fract_nonneg _, le_of_lt (fract_lt_one _)⟩

Depends on / 依赖: f.map_fract_sub_fract_eq, fract_lt_one, fract_nonneg, le_of_lt, map_fract_sub_fract_eq
-/
theorem forall_map_sub_of_Icc (P : Real -> Prop) (h : forall x in Icc (0 : Real) 1, P (f x - x)) (x : Real) :
    P (f x - x) :=
  f.map_fract_sub_fract_eq x ▸ h _ ⟨fract_nonneg _, le_of_lt (fract_lt_one _)⟩

/--
theorem `translationNumber_lt_of_forall_lt_add` / 定理 `translationNumber_lt_of_forall_lt_add`

English:
theorem translationNumber_lt_of_forall_lt_add
  given: (hf : Continuous f) {z : Real} (hz : forall x, f x < x + z)
  proof: by
  obtain ⟨x, -, hx⟩ : exists x in Icc (0 : Real) 1, forall y in Icc (0 : Real) 1, f y - y <= f x - x :=
    isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 zero_le_one)
      (hf.sub continuous_id).continuousOn
  refine lt_of_le_of_lt ?_ (sub_lt_iff_lt_add'.2 <| hz x)
  apply translationNumber_le_of_le_add
  simp only [← sub_le_iff_le_add']
  exact f.forall_map_sub_of_Icc (fun a => a <= f x - x) hx

中文:
定理 translationNumber_lt_of_对任意_lt_add
  条件: (hf : 连续 f) {z : 实数} (hz : 对任意 x, f x < x + z)
  证明: by
  obtain ⟨x, -, hx⟩ : exists x in Icc (0 : Real) 1, forall y in Icc (0 : Real) 1, f y - y <= f x - x :=
    isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 zero_le_one)
      (hf.sub continuous_id).continuousOn
  refine lt_of_le_of_lt ?_ (sub_lt_iff_lt_add'.2 <| hz x)
  apply translationNumber_le_of_le_add
  simp only [← sub_le_iff_le_add']
  exact f.forall_map_sub_of_Icc (fun a => a <= f x - x) hx

Depends on / 依赖: continuousOn, continuous_id, exists_isMaxOn, f.forall_map_sub_of_Icc, forall_map_sub_of_Icc, hf.sub, isCompact_Icc, isCompact_Icc.exists_isMaxOn, lt_of_le_of_lt, nonempty_Icc, sub_le_iff_le_add, sub_lt_iff_lt_add, translationNumber_le_of_le_add, zero_le_one
-/
theorem translationNumber_lt_of_forall_lt_add (hf : Continuous f) {z : Real} (hz : forall x, f x < x + z) :
    τ f < z := by
  obtain ⟨x, -, hx⟩ : exists x in Icc (0 : Real) 1, forall y in Icc (0 : Real) 1, f y - y <= f x - x :=
    isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 zero_le_one)
      (hf.sub continuous_id).continuousOn
  refine lt_of_le_of_lt ?_ (sub_lt_iff_lt_add'.2 <| hz x)
  apply translationNumber_le_of_le_add
  simp only [← sub_le_iff_le_add']
  exact f.forall_map_sub_of_Icc (fun a => a <= f x - x) hx

/--
theorem `lt_translationNumber_of_forall_add_lt` / 定理 `lt_translationNumber_of_forall_add_lt`

English:
theorem lt_translationNumber_of_forall_add_lt
  given: (hf : Continuous f) {z : Real} (hz : forall x, x + z < f x)
  proof: by
  obtain ⟨x, -, hx⟩ : exists x in Icc (0 : Real) 1, forall y in Icc (0 : Real) 1, f x - x <= f y - y :=
    isCompact_Icc.exists_isMinOn (nonempty_Icc.2 zero_le_one) (hf.sub continuous_id).continuousOn
  refine lt_of_lt_of_le (lt_sub_iff_add_lt'.2 <| hz x) ?_
  apply le_translationNumber_of_add_le
  simp only [← le_sub_iff_add_le']
  exact f.forall_map_sub_of_Icc _ hx

中文:
定理 lt_translationNumber_of_对任意_add_lt
  条件: (hf : 连续 f) {z : 实数} (hz : 对任意 x, x + z < f x)
  证明: by
  obtain ⟨x, -, hx⟩ : exists x in Icc (0 : Real) 1, forall y in Icc (0 : Real) 1, f x - x <= f y - y :=
    isCompact_Icc.exists_isMinOn (nonempty_Icc.2 zero_le_one) (hf.sub continuous_id).continuousOn
  refine lt_of_lt_of_le (lt_sub_iff_add_lt'.2 <| hz x) ?_
  apply le_translationNumber_of_add_le
  simp only [← le_sub_iff_add_le']
  exact f.forall_map_sub_of_Icc _ hx

Depends on / 依赖: continuousOn, continuous_id, exists_isMinOn, f.forall_map_sub_of_Icc, forall_map_sub_of_Icc, hf.sub, isCompact_Icc, isCompact_Icc.exists_isMinOn, le_sub_iff_add_le, le_translationNumber_of_add_le, lt_of_lt_of_le, lt_sub_iff_add_lt, nonempty_Icc, zero_le_one
-/
theorem lt_translationNumber_of_forall_add_lt (hf : Continuous f) {z : Real} (hz : forall x, x + z < f x) :
    z < τ f := by
  obtain ⟨x, -, hx⟩ : exists x in Icc (0 : Real) 1, forall y in Icc (0 : Real) 1, f x - x <= f y - y :=
    isCompact_Icc.exists_isMinOn (nonempty_Icc.2 zero_le_one) (hf.sub continuous_id).continuousOn
  refine lt_of_lt_of_le (lt_sub_iff_add_lt'.2 <| hz x) ?_
  apply le_translationNumber_of_add_le
  simp only [← le_sub_iff_add_le']
  exact f.forall_map_sub_of_Icc _ hx

/--
theorem `exists_eq_add_translationNumber` / 定理 `exists_eq_add_translationNumber`

English:
theorem exists_eq_add_translationNumber
  given: (hf : Continuous f)
  statement: exists x, f x = x + τ f
  proof: by
  obtain ⟨a, ha⟩ : exists x, f x <= x + τ f := by
    by_contra! H
    exact lt_irrefl _ (f.lt_translationNumber_of_forall_add_lt hf H)
  obtain ⟨b, hb⟩ : exists x, x + τ f <= f x := by
    by_contra! H
    exact lt_irrefl _ (f.translationNumber_lt_of_forall_lt_add hf H)
  exact intermediate_value_univ₂ hf (by fun_prop) ha hb

中文:
定理 存在_eq_add_translationNumber
  条件: (hf : 连续 f)
  结论: 存在 x, f x = x + τ f
  证明: by
  obtain ⟨a, ha⟩ : exists x, f x <= x + τ f := by
    by_contra! H
    exact lt_irrefl _ (f.lt_translationNumber_of_forall_add_lt hf H)
  obtain ⟨b, hb⟩ : exists x, x + τ f <= f x := by
    by_contra! H
    exact lt_irrefl _ (f.translationNumber_lt_of_forall_lt_add hf H)
  exact intermediate_value_univ₂ hf (by fun_prop) ha hb

Depends on / 依赖: f.lt_translationNumber_of_forall_add_lt, f.translationNumber_lt_of_forall_lt_add, fun_prop, lt_irrefl, lt_translationNumber_of_forall_add_lt, translationNumber_lt_of_forall_lt_add
-/
theorem exists_eq_add_translationNumber (hf : Continuous f) : exists x, f x = x + τ f := by
  obtain ⟨a, ha⟩ : exists x, f x <= x + τ f := by
    by_contra! H
    exact lt_irrefl _ (f.lt_translationNumber_of_forall_add_lt hf H)
  obtain ⟨b, hb⟩ : exists x, x + τ f <= f x := by
    by_contra! H
    exact lt_irrefl _ (f.translationNumber_lt_of_forall_lt_add hf H)
  exact intermediate_value_univ₂ hf (by fun_prop) ha hb

/--
theorem `translationNumber_eq_int_iff` / 定理 `translationNumber_eq_int_iff`

English:
theorem translationNumber_eq_int_iff
  given: (hf : Continuous f) {m : Int}
  proof: by
  constructor
  · intro h
    simp only [← h]
    exact f.exists_eq_add_translationNumber hf
  · rintro ⟨x, hx⟩
    exact f.translationNumber_of_eq_add_int hx

中文:
定理 translationNumber_eq_int_iff
  条件: (hf : 连续 f) {m : 整数}
  证明: by
  constructor
  · intro h
    simp only [← h]
    exact f.exists_eq_add_translationNumber hf
  · rintro ⟨x, hx⟩
    exact f.translationNumber_of_eq_add_int hx

Depends on / 依赖: exists_eq_add_translationNumber, f.exists_eq_add_translationNumber, f.translationNumber_of_eq_add_int, translationNumber_of_eq_add_int
-/
theorem translationNumber_eq_int_iff (hf : Continuous f) {m : Int} :
    τ f = m ↔ exists x : Real, f x = x + m := by
  constructor
  · intro h
    simp only [← h]
    exact f.exists_eq_add_translationNumber hf
  · rintro ⟨x, hx⟩
    exact f.translationNumber_of_eq_add_int hx

/--
theorem `continuous_pow` / 定理 `continuous_pow`

English:
theorem continuous_pow
  given: (hf : Continuous f) (n : Nat)
  statement: Continuous (f ^ n : CircleDeg1Lift)
  proof: by
  rw [coe_pow]
  exact hf.iterate n

中文:
定理 continuous_pow
  条件: (hf : 连续 f) (n : 自然数)
  结论: 连续 (f ^ n : CircleDeg1Lift)
  证明: by
  rw [coe_pow]
  exact hf.iterate n

Depends on / 依赖: coe_pow, hf.iterate, iterate
-/
theorem continuous_pow (hf : Continuous f) (n : Nat) : Continuous (f ^ n : CircleDeg1Lift) := by
  rw [coe_pow]
  exact hf.iterate n

/--
theorem `translationNumber_eq_rat_iff` / 定理 `translationNumber_eq_rat_iff`

English:
theorem translationNumber_eq_rat_iff
  given: (hf : Continuous f) {m : Int} {n : Nat} (hn : 0 < n)
  proof: by
  rw [eq_div_iff]; rw [mul_comm]; rw [← translationNumber_pow] <;> [skip; exact ne_of_gt (Nat.cast_pos.2 hn)]
  exact (f ^ n).translationNumber_eq_int_iff (f.continuous_pow hf n)

中文:
定理 translationNumber_eq_rat_iff
  条件: (hf : 连续 f) {m : 整数} {n : 自然数} (hn : 0 < n)
  证明: by
  rw [eq_div_iff]; rw [mul_comm]; rw [← translationNumber_pow] <;> [skip; exact ne_of_gt (Nat.cast_pos.2 hn)]
  exact (f ^ n).translationNumber_eq_int_iff (f.continuous_pow hf n)

Depends on / 依赖: Nat.cast_pos, cast_pos, continuous_pow, eq_div_iff, f.continuous_pow, mul_comm, ne_of_gt, translationNumber_eq_int_iff, translationNumber_pow
-/
theorem translationNumber_eq_rat_iff (hf : Continuous f) {m : Int} {n : Nat} (hn : 0 < n) :
    τ f = m / n ↔ exists x, (f ^ n) x = x + m := by
  rw [eq_div_iff]; rw [mul_comm]; rw [← translationNumber_pow] <;> [skip; exact ne_of_gt (Nat.cast_pos.2 hn)]
  exact (f ^ n).translationNumber_eq_int_iff (f.continuous_pow hf n)

/--
theorem `semiconj_of_group_action_of_forall_translationNumber_eq` / 定理 `semiconj_of_group_action_of_forall_translationNumber_eq`

English:
theorem semiconj_of_group_action_of_forall_translationNumber_eq
  statement: {G : Type*} [Group G]
  proof: by
  -- Equality of translation number guarantees that for each `x`
  -- the set `{f₂ g⁻¹ (f₁ g x) | g : G}` is bounded above.
  have : forall x, BddAbove (range fun g => f₂ g⁻¹ (f₁ g x)) := by
    refine fun x => ⟨x + 2, ?_⟩
    rintro _ ⟨g, rfl⟩
    have : τ (f₂ g⁻¹) = -τ (f₂ g) := by
      rw [← MonoidHom.coe_toHomUnits]; rw [map_inv]; rw [translationNumber_units_inv]; rw [MonoidHom.coe_toHomUnits]
    calc
      f₂ g⁻¹ (f₁ g x) <= f₂ g⁻¹ (x + τ (f₁ g) + 1) :=
        mono _ (map_lt_add_translationNumber_add_one _ _).le
      _ = f₂ g⁻¹ (x + τ (f₂ g)) + 1 := by rw [h, map_add_one]
      _ <= x + τ (f₂ g) + τ (f₂ g⁻¹) + 1 + 1 := by grw [map_lt_add_translationNumber_add_one]
      _ = x + 2 := by simp [this, add_assoc, one_add_one_eq_two]
  -- We have a theorem about actions by `OrderIso`, so we introduce auxiliary maps
  -- to `ℝ ≃o ℝ`.
  set F₁ := toOrderIso.comp f₁.toHomUnits
  set F₂ := toOrderIso.comp f₂.toHomUnits
  have hF₁ : forall g, ⇑(F₁ g) = f₁ g := fun _ => rfl
  have hF₂ : forall g, ⇑(F₂ g) = f₂ g := fun _ => rfl
  -- Now we apply `csSup_div_semiconj` and go back to `f₁` and `f₂`.
  refine ⟨⟨⟨fun x => ⨆ g', (F₂ g')⁻¹ (F₁ g' x), fun x y hxy => ?_⟩, fun x => ?_⟩,
    csSup_div_semiconj F₂ F₁ fun x => ?_⟩ <;> simp only [hF₁, hF₂, ← map_inv]
  · exact ciSup_mono (this y) fun g => mono _ (mono _ hxy)
  · simp only [map_add_one]
    exact (Monotone.map_ciSup_of_continuousAt (by fun_prop)
      (monotone_id.add_const (1 : Real)) (this x)).symm
  · exact this x

中文:
定理 semiconj_of_group_action_of_对任意_translationNumber_eq
  结论: {G : 类型} [群 G]
  证明: by
  -- Equality of translation number guarantees that for each `x`
  -- the set `{f₂ g⁻¹ (f₁ g x) | g : G}` is bounded above.
  have : forall x, BddAbove (range fun g => f₂ g⁻¹ (f₁ g x)) := by
    refine fun x => ⟨x + 2, ?_⟩
    rintro _ ⟨g, rfl⟩
    have : τ (f₂ g⁻¹) = -τ (f₂ g) := by
      rw [← MonoidHom.coe_toHomUnits]; rw [map_inv]; rw [translationNumber_units_inv]; rw [MonoidHom.coe_toHomUnits]
    calc
      f₂ g⁻¹ (f₁ g x) <= f₂ g⁻¹ (x + τ (f₁ g) + 1) :=
        mono _ (map_lt_add_translationNumber_add_one _ _).le
      _ = f₂ g⁻¹ (x + τ (f₂ g)) + 1 := by rw [h, map_add_one]
      _ <= x + τ (f₂ g) + τ (f₂ g⁻¹) + 1 + 1 := by grw [map_lt_add_translationNumber_add_one]
      _ = x + 2 := by simp [this, add_assoc, one_add_one_eq_two]
  -- We have a theorem about actions by `OrderIso`, so we introduce auxiliary maps
  -- to `ℝ ≃o ℝ`.
  set F₁ := toOrderIso.comp f₁.toHomUnits
  set F₂ := toOrderIso.comp f₂.toHomUnits
  have hF₁ : forall g, ⇑(F₁ g) = f₁ g := fun _ => rfl
  have hF₂ : forall g, ⇑(F₂ g) = f₂ g := fun _ => rfl
  -- Now we apply `csSup_div_semiconj` and go back to `f₁` and `f₂`.
  refine ⟨⟨⟨fun x => ⨆ g', (F₂ g')⁻¹ (F₁ g' x), fun x y hxy => ?_⟩, fun x => ?_⟩,
    csSup_div_semiconj F₂ F₁ fun x => ?_⟩ <;> simp only [hF₁, hF₂, ← map_inv]
  · exact ciSup_mono (this y) fun g => mono _ (mono _ hxy)
  · simp only [map_add_one]
    exact (Monotone.map_ciSup_of_continuousAt (by fun_prop)
      (monotone_id.add_const (1 : Real)) (this x)).symm
  · exact this x
-/
theorem semiconj_of_group_action_of_forall_translationNumber_eq {G : Type*} [Group G]
    (f₁ f₂ : G ->* CircleDeg1Lift) (h : forall g, τ (f₁ g) = τ (f₂ g)) :
    exists F : CircleDeg1Lift, forall g, Semiconj F (f₁ g) (f₂ g) := by
  -- Equality of translation number guarantees that for each `x`
  -- the set `{f₂ g⁻¹ (f₁ g x) | g : G}` is bounded above.
  have : forall x, BddAbove (range fun g => f₂ g⁻¹ (f₁ g x)) := by
    refine fun x => ⟨x + 2, ?_⟩
    rintro _ ⟨g, rfl⟩
    have : τ (f₂ g⁻¹) = -τ (f₂ g) := by
      rw [← MonoidHom.coe_toHomUnits]; rw [map_inv]; rw [translationNumber_units_inv]; rw [MonoidHom.coe_toHomUnits]
    calc
      f₂ g⁻¹ (f₁ g x) <= f₂ g⁻¹ (x + τ (f₁ g) + 1) :=
        mono _ (map_lt_add_translationNumber_add_one _ _).le
      _ = f₂ g⁻¹ (x + τ (f₂ g)) + 1 := by rw [h, map_add_one]
      _ <= x + τ (f₂ g) + τ (f₂ g⁻¹) + 1 + 1 := by grw [map_lt_add_translationNumber_add_one]
      _ = x + 2 := by simp [this, add_assoc, one_add_one_eq_two]
  -- We have a theorem about actions by `OrderIso`, so we introduce auxiliary maps
  -- to `ℝ ≃o ℝ`.
  set F₁ := toOrderIso.comp f₁.toHomUnits
  set F₂ := toOrderIso.comp f₂.toHomUnits
  have hF₁ : forall g, ⇑(F₁ g) = f₁ g := fun _ => rfl
  have hF₂ : forall g, ⇑(F₂ g) = f₂ g := fun _ => rfl
  -- Now we apply `csSup_div_semiconj` and go back to `f₁` and `f₂`.
  refine ⟨⟨⟨fun x => ⨆ g', (F₂ g')⁻¹ (F₁ g' x), fun x y hxy => ?_⟩, fun x => ?_⟩,
    csSup_div_semiconj F₂ F₁ fun x => ?_⟩ <;> simp only [hF₁, hF₂, ← map_inv]
  · exact ciSup_mono (this y) fun g => mono _ (mono _ hxy)
  · simp only [map_add_one]
    exact (Monotone.map_ciSup_of_continuousAt (by fun_prop)
      (monotone_id.add_const (1 : Real)) (this x)).symm
  · exact this x

/--
theorem `units_semiconj_of_translationNumber_eq` / 定理 `units_semiconj_of_translationNumber_eq`

English:
theorem units_semiconj_of_translationNumber_eq
  given: {f₁ f₂ : CircleDeg1Liftˣ} (h : τ f₁ = τ f₂)
  proof: have : forall n : Multiplicative Int,
      τ ((Units.coeHom _).comp (zpowersHom _ f₁) n) =
        τ ((Units.coeHom _).comp (zpowersHom _ f₂) n) := fun n => by
    simp [h]
  (semiconj_of_group_action_of_forall_translationNumber_eq _ _ this).imp fun F hF => by
    simpa using hF (Multiplicative.ofAdd 1)

中文:
定理 units_semiconj_of_translationNumber_eq
  条件: {f₁ f₂ : CircleDeg1Liftˣ} (h : τ f₁ = τ f₂)
  证明: have : forall n : Multiplicative Int,
      τ ((Units.coeHom _).comp (zpowersHom _ f₁) n) =
        τ ((Units.coeHom _).comp (zpowersHom _ f₂) n) := fun n => by
    simp [h]
  (semiconj_of_group_action_of_forall_translationNumber_eq _ _ this).imp fun F hF => by
    simpa using hF (Multiplicative.ofAdd 1)

Depends on / 依赖: Multiplicative, Multiplicative.ofAdd, Units.coeHom, coeHom, semiconj_of_group_action_of_forall_translationNumber_eq, zpowersHom
-/
theorem units_semiconj_of_translationNumber_eq {f₁ f₂ : CircleDeg1Liftˣ} (h : τ f₁ = τ f₂) :
    exists F : CircleDeg1Lift, Semiconj F f₁ f₂ :=
  have : forall n : Multiplicative Int,
      τ ((Units.coeHom _).comp (zpowersHom _ f₁) n) =
        τ ((Units.coeHom _).comp (zpowersHom _ f₂) n) := fun n => by
    simp [h]
  (semiconj_of_group_action_of_forall_translationNumber_eq _ _ this).imp fun F hF => by
    simpa using hF (Multiplicative.ofAdd 1)

/--
theorem `semiconj_of_isUnit_of_translationNumber_eq` / 定理 `semiconj_of_isUnit_of_translationNumber_eq`

English:
theorem semiconj_of_isUnit_of_translationNumber_eq
  statement: {f₁ f₂ : CircleDeg1Lift} (h₁ : IsUnit f₁)
  proof: by
  rcases h₁, h₂ with ⟨⟨f₁, rfl⟩, ⟨f₂, rfl⟩⟩
  exact units_semiconj_of_translationNumber_eq h

中文:
定理 semiconj_of_isUnit_of_translationNumber_eq
  结论: {f₁ f₂ : CircleDeg1Lift} (h₁ : 是单位 f₁)
  证明: by
  rcases h₁, h₂ with ⟨⟨f₁, rfl⟩, ⟨f₂, rfl⟩⟩
  exact units_semiconj_of_translationNumber_eq h

Depends on / 依赖: units_semiconj_of_translationNumber_eq
-/
theorem semiconj_of_isUnit_of_translationNumber_eq {f₁ f₂ : CircleDeg1Lift} (h₁ : IsUnit f₁)
    (h₂ : IsUnit f₂) (h : τ f₁ = τ f₂) : exists F : CircleDeg1Lift, Semiconj F f₁ f₂ := by
  rcases h₁, h₂ with ⟨⟨f₁, rfl⟩, ⟨f₂, rfl⟩⟩
  exact units_semiconj_of_translationNumber_eq h

/--
theorem `semiconj_of_bijective_of_translationNumber_eq` / 定理 `semiconj_of_bijective_of_translationNumber_eq`

English:
theorem semiconj_of_bijective_of_translationNumber_eq
  statement: {f₁ f₂ : CircleDeg1Lift} (h₁ : Bijective f₁)
  proof: semiconj_of_isUnit_of_translationNumber_eq (isUnit_iff_bijective.2 h₁) (isUnit_iff_bijective.2 h₂)
    h

中文:
定理 semiconj_of_bijective_of_translationNumber_eq
  结论: {f₁ f₂ : CircleDeg1Lift} (h₁ : 双射 f₁)
  证明: semiconj_of_isUnit_of_translationNumber_eq (isUnit_iff_bijective.2 h₁) (isUnit_iff_bijective.2 h₂)
    h

Depends on / 依赖: isUnit_iff_bijective, semiconj_of_isUnit_of_translationNumber_eq
-/
theorem semiconj_of_bijective_of_translationNumber_eq {f₁ f₂ : CircleDeg1Lift} (h₁ : Bijective f₁)
    (h₂ : Bijective f₂) (h : τ f₁ = τ f₂) : exists F : CircleDeg1Lift, Semiconj F f₁ f₂ :=
  semiconj_of_isUnit_of_translationNumber_eq (isUnit_iff_bijective.2 h₁) (isUnit_iff_bijective.2 h₂)
    h

end CircleDeg1Lift
