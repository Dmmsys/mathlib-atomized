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

/-- A lift of a monotone degree one map `S¹ → S¹`. -/
/-
**CircleDeg1Lift** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A lift of a monotone degree one map `S¹ → S¹`.
-/
structure CircleDeg1Lift : Type extends ℝ →o ℝ where
  map_add_one' : ∀ x, toFun (x + 1) = toFun x + 1

namespace CircleDeg1Lift

/-
**CircleDeg1Lift.** 是 Mathlib 中的一个实例，位于命名空间 `CircleDeg1Lift`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FunLike CircleDeg1Lift ℝ ℝ where
  coe f := f.toFun
  coe_injective | ⟨⟨_, _⟩, _⟩, ⟨⟨_, _⟩, _⟩, rfl => rfl
/-
**CircleDeg1Lift.** 是 Mathlib 中的一个实例，位于命名空间 `CircleDeg1Lift`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : OrderHomClass CircleDeg1Lift ℝ ℝ where
  map_rel f _ _ h := f.monotone' h
/-
**CircleDeg1Lift.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `CircleDeg1Lift`。
形式化陈述：∀ (f : ℝ →o ℝ) (h : ∀ (x : ℝ), f.toFun (x + 1) = f.toFun x + 1), ⇑{ toOrde
rHom := f, map_add_one' := h } = ⇑f
参数：f : ℝ →o ℝ；h : ∀ (x : ℝ), f.toFun (x + 1) = f.toFun x + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem coe_mk (f h) : ⇑(mk f h) = f := rfl

variable (f g : CircleDeg1Lift)
/-
**CircleDeg1Lift.coe_toOrderHom** 是 Mathlib 中的一个定理，位于命名空间 `CircleDeg1Lift`。
形式化陈述：∀ (f : CircleDeg1Lift), ⇑f.toOrderHom = ⇑f
参数：f : CircleDeg1Lift。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem coe_toOrderHom : ⇑f.toOrderHom = f := rfl
/-
**CircleDeg1Lift.monotone** 是 Mathlib 中的一个定理，位于命名空间 `CircleDeg1Lift`。
形式化陈述：∀ (f : CircleDeg1Lift), Monotone ⇑f
参数：f : CircleDeg1Lift。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderHom.monotone'`：∀ {α : Type u_6} {β : Type u_7} [inst : Preorder α] 
[inst_1 : Preorder β] (self : α →o β), Monotone self.toFun
-/
protected theorem monotone : Monotone f := f.monotone'
/-
**CircleDeg1Lift.mono** 是 Mathlib 中的一个定理，位于命名空间 `CircleDeg1Lift`。
形式化陈述：∀ (f : CircleDeg1Lift) {x y : ℝ}, x ≤ y → f x ≤ f y
参数：f : CircleDeg1Lift。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CircleDeg1Lift.monotone`：∀ (f : CircleDeg1Lift), Monotone ⇑f
-/
@[gcongr, mono] theorem mono {x y} (h : x ≤ y) : f x ≤ f y := f.monotone h
/-
**CircleDeg1Lift.strictMono_iff_injective** 是 Mathlib 中的一个定理，位于命名空间 `CircleDeg1L
ift`。
形式化陈述：strictMono_iff_injective : StrictMono f ↔ Injective f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.strictMono_iff_injective`：Monotone.strictMono_iff_injective (hf
 : Monotone f) : StrictMono f ↔ Injective f
· 使用定理 `CircleDeg1Lift.monotone`：∀ (f : CircleDeg1Lift), Monotone ⇑f
-/
theorem strictMono_iff_injective : StrictMono f ↔ Injective f :=
  f.monotone.strictMono_iff_injective

@[simp]
/-
**CircleDeg1Lift.map_add_one** 是 Mathlib 中的一个定理，位于命名空间 `CircleDeg1Lift`。
形式化陈述：map_add_one : forall x, f (x + 1) = f x + 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CircleDeg1Lift.map_add_one'`：∀ (self : CircleDeg1Lift) (x : ℝ), self.toF
un (x + 1) = self.toFun x + 1
-/
theorem map_add_one : ∀ x, f (x + 1) = f x + 1 :=
  f.map_add_one'

@[simp]
/-
**CircleDeg1Lift.map_one_add** 是 Mathlib 中的一个定理，位于命名空间 `CircleDeg1Lift`。
形式化陈述：map_one_add (x : Real) : f (1 + x) = 1 + f x
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `CircleDeg1Lift.map_add_one`：map_add_one : forall x, f (x + 1) = f x + 1
-/
theorem map_one_add (x : ℝ) : f (1 + x) = 1 + f x := by rw [add_comm, map_add_one, add_comm 1]

@[ext]
/-
**CircleDeg1Lift.ext** 是 Mathlib 中的一个定理，位于命名空间 `CircleDeg1Lift`。
形式化陈述：ext ⦃f g : CircleDeg1Lift⦄ (h : forall x, f x = g x) : f = g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext ⦃f g : CircleDeg1Lift⦄ (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h
/-
**CircleDeg1Lift.** 是 Mathlib 中的一个实例，位于命名空间 `CircleDeg1Lift`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Monoid CircleDeg1Lift where
  mul f g :=
    { toOrderHom := f.1.comp g.1
      map_add_one' := fun x => by simp [map_add_one] }
  one := ⟨.id, fun _ => rfl⟩
  mul_one _ := rfl
  one_mul _ := rfl
  mul_assoc _ _ _ := DFunLike.coe_injective rfl
/-
**CircleDeg1Lift.** 是 Mathlib 中的一个实例，位于命名空间 `CircleDeg1Lift`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited CircleDeg1Lift := ⟨1⟩

@[simp]
/-
**CircleDeg1Lift.coe_mul** 是 Mathlib 中的一个定理，位于命名空间 `CircleDeg1Lift`。
形式化陈述：coe_mul : ⇑(f * g) = f ∘ g
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mul : ⇑(f * g) = f ∘ g :=
  rfl
/-
**CircleDeg1Lift.mul_apply** 是 Mathlib 中的一个定理，位于命名空间 `CircleDeg1Lift`。
形式化陈述：mul_apply (x) : (f * g) x = f (g x)
参数：x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mul_apply (x) : (f * g) x = f (g x) :=
  rfl

@[simp]
/-
**CircleDeg1Lift.coe_one** 是 Mathlib 中的一个定理，位于命名空间 `CircleDeg1Lift`。
形式化陈述：coe_one : ⇑(1 : CircleDeg1Lift) = id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_one : ⇑(1 : CircleDeg1Lift) = id :=
  rfl
/-
**CircleDeg1Lift.unitsHasCoeToFun** 是 Mathlib 中的一个实例，位于命名空间 `CircleDeg1Lift`。
形式化陈述：unitsHasCoeToFun : CoeFun CircleDeg1Liftˣ fun _ => Real -> Real
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance unitsHasCoeToFun : CoeFun CircleDeg1Liftˣ fun _ => ℝ → ℝ :=
  ⟨fun f => ⇑(f : CircleDeg1Lift)⟩

@[simp]
/-
**CircleDeg1Lift.units_inv_apply_apply** 是 Mathlib 中的一个定理，位于命名空间 `CircleDeg1Lift
`。
形式化陈述：units_inv_apply_apply (f : CircleDeg1Liftˣ) (x : Real) : (f⁻¹ : CircleDeg1
Liftˣ) (f x) = x
参数：f : CircleDeg1Liftˣ；x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Units.inv_mul`：inv_mul : (↑a⁻¹ * a : α) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem units_inv_apply_apply (f : CircleDeg1Liftˣ) (x : ℝ) :
    (f⁻¹ : CircleDeg1Liftˣ) (f x) = x := by simp only [← mul_apply, f.inv_mul, coe_one, id]

@[simp]
/-
**CircleDeg1Lift.units_apply_inv_apply** 是 Mathlib 中的一个定理，位于命名空间 `CircleDeg1Lift
`。
形式化陈述：units_apply_inv_apply (f : CircleDeg1Liftˣ) (x : Real) : f ((f⁻¹ : CircleD
eg1Liftˣ) x) = x
参数：f : CircleDeg1Liftˣ；x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Units.mul_inv`：mul_inv : (a * ↑a⁻¹ : α) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem units_apply_inv_apply (f : CircleDeg1Liftˣ) (x : ℝ) :
    f ((f⁻¹ : CircleDeg1Liftˣ) x) = x := by simp only [← mul_apply, f.mul_inv, coe_one, id]

set_option backward.isDefEq.respectTransparency false in
/-- If a lift of a circle map is bijective, then it is an order automorphism of the line. -/
/-
**CircleDeg1Lift.toOrderIso** 是 Mathlib 中的一个定义，位于命名空间 `CircleDeg1Lift`。
形式化陈述：toOrderIso : CircleDeg1Liftˣ ->* Real ≃o Real where toFun f
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CircleDeg1Lift.units_inv_apply_apply`：units_inv_apply_apply (f : CircleD
eg1Liftˣ) (x : Real) : (f⁻¹ : CircleDeg1Liftˣ) (f x) = x
· 使用定理 `CircleDeg1Lift.units_apply_inv_apply`：units_apply_inv_apply (f : CircleD
eg1Liftˣ) (x : Real) : f ((f⁻¹ : CircleDeg1Liftˣ) x) = x

--- 原说明 ---
If a lift of a circle map is bijective, then it is an order automorphism of the 
line.
-/
def toOrderIso : CircleDeg1Liftˣ →* ℝ ≃o ℝ where
  toFun f :=
    { toFun := f
      invFun := ⇑f⁻¹
      left_inv := units_inv_apply_apply f
      right_inv := units_apply_inv_apply f
      map_rel_iff' := ⟨fun h => by simpa using mono (↑f⁻¹) h, mono f⟩ }
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp]
/-
**CircleDeg1Lift.coe_toOrderIso** 是 Mathlib 中的一个定理，位于命名空间 `CircleDeg1Lift`。
形式化陈述：coe_toOrderIso (f : CircleDeg1Liftˣ) : ⇑(toOrderIso f) = f
参数：f : CircleDeg1Liftˣ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toOrderIso (f : CircleDeg1Liftˣ) : ⇑(toOrderIso f) = f :=
  rfl

@[simp]
/-
**CircleDeg1Lift.coe_toOrderIso_symm** 是 Mathlib 中的一个定理，位于命名空间 `CircleDeg1Lift`。
形式化陈述：coe_toOrderIso_symm (f : CircleDeg1Liftˣ) : ⇑(toOrderIso f).symm = (f⁻¹ : 
CircleDeg1Liftˣ)
参数：f : CircleDeg1Liftˣ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toOrderIso_symm (f : CircleDeg1Liftˣ) :
    ⇑(toOrderIso f).symm = (f⁻¹ : CircleDeg1Liftˣ) :=
  rfl

@[simp]
/-
**CircleDeg1Lift.coe_toOrderIso_inv** 是 Mathlib 中的一个定理，位于命名空间 `CircleDeg1Lift`。
形式化陈述：coe_toOrderIso_inv (f : CircleDeg1Liftˣ) : ⇑(toOrderIso f)⁻¹ = (f⁻¹ : Circ
leDeg1Liftˣ)
参数：f : CircleDeg1Liftˣ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toOrderIso_inv (f : CircleDeg1Liftˣ) : ⇑(toOrderIso f)⁻¹ = (f⁻¹ : CircleDeg1Liftˣ) :=
  rfl
/-
**CircleDeg1Lift.isUnit_iff_bijective** 是 Mathlib 中的一个定理，位于命名空间 `CircleDeg1Lift`
。
形式化陈述：isUnit_iff_bijective {f : CircleDeg1Lift} : IsUnit f ↔ Bijective f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.bijective`：∀ {α : Type u_2} {β : Type u_3} [inst : LE α] [inst_
1 : LE β] (e : α ≃o β), Function.Bijective ⇑e
· 使用定理 `Units.isUnit`：∀ {M : Type u_1} [inst : Monoid M] (u : Mˣ), IsUnit ↑u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `StrictMono.le_iff_le`：StrictMono.le_iff_le (hf : StrictMono f) {a b : α}
 : f a <= f b ↔ a <= b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CircleDeg1Lift.strictMono_iff_injective`：strictMono_iff_injective : Stri
ctMono f ↔ Injective f
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Equiv.ofBijective_apply_symm_apply`：ofBijective_apply_symm_apply (f : α 
-> β) (hf : Bijective f) (x : β) : f ((ofBijective f hf).symm x) = x
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `CircleDeg1Lift.map_add_one`：map_add_one : forall x, f (x + 1) = f x + 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CircleDeg1Lift.ext`：ext ⦃f g : CircleDeg1Lift⦄ (h : forall x, f x = g x)
 : f = g
· 使用引理 `Equiv.ofBijective_symm_apply_apply`：ofBijective_symm_apply_apply (f : α 
-> β) (hf : Bijective f) (x : α) : (ofBijective f hf).symm (f x) = x
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
              h.1 <| by simp only [Equiv.ofBijective_apply_symm_apply f, f.map_add_one] }
        val_inv := ext <| Equiv.ofBijective_apply_symm_apply f h
        inv_val := ext <| Equiv.ofBijective_symm_apply_apply f h }⟩
/-
**CircleDeg1Lift.coe_pow** 是 Mathlib 中的一个定理，位于命名空间 `CircleDeg1Lift`。
形式化陈述：∀ (f : CircleDeg1Lift) (n : ℕ), ⇑(f ^ n) = (⇑f)^[n]
参数：f : CircleDeg1Lift；n : ℕ；f ^ n；⇑f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_pow : ∀ n : ℕ, ⇑(f ^ n) = f^[n]
  | 0 => rfl
  | n + 1 => by
    simp [coe_pow n, pow_succ]
/-
**CircleDeg1Lift.semiconjBy_iff_semiconj** 是 Mathlib 中的一个定理，位于命名空间 `CircleDeg1Li
ft`。
形式化陈述：semiconjBy_iff_semiconj {f g₁ g₂ : CircleDeg1Lift} : SemiconjBy f g₁ g₂ ↔ 
Semiconj f g₁ g₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CircleDeg1Lift.ext_iff`：∀ {f g : CircleDeg1Lift}, f = g ↔ ∀ (x : ℝ), f x
 = g x
-/
theorem semiconjBy_iff_semiconj {f g₁ g₂ : CircleDeg1Lift} :
    SemiconjBy f g₁ g₂ ↔ Semiconj f g₁ g₂ :=
  CircleDeg1Lift.ext_iff
/-
**CircleDeg1Lift.commute_iff_commute** 是 Mathlib 中的一个定理，位于命名空间 `CircleDeg1Lift`。
形式化陈述：commute_iff_commute {f g : CircleDeg1Lift} : Commute f g ↔ Function.Commut
e f g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CircleDeg1Lift.ext_iff`：∀ {f g : CircleDeg1Lift}, f = g ↔ ∀ (x : ℝ), f x
 = g x
-/
theorem commute_iff_commute {f g : CircleDeg1Lift} : Commute f g ↔ Function.Commute f g :=
  CircleDeg1Lift.ext_iff

/-!
### Translate by a constant
-/


/-- The map `y ↦ x + y` as a `CircleDeg1Lift`. More precisely, we define a homomorphism from
`Multiplicative ℝ` to `CircleDeg1Liftˣ`, so the translation by `x` is
`translation (Multiplicative.ofAdd x)`. -/
/-
**CircleDeg1Lift.translate** 是 Mathlib 中的一个定义，位于命名空间 `CircleDeg1Lift`。
形式化陈述：translate : Multiplicative Real ->* CircleDeg1Liftˣ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map `y ↦ x + y` as a `CircleDeg1Lift`. More precisely, we define a homomorph
ism from
`Multiplicative ℝ` to `CircleDeg1Liftˣ`, so the translation by `x` is
`translation (Multiplicative.ofAdd x)`.
-/
def translate : Multiplicative ℝ →* CircleDeg1Liftˣ := MonoidHom.toHomUnits <|
  { toFun x := ⟨⟨fun y => x.toAdd + y, add_right_mono⟩, fun _ => (add_assoc ..).symm⟩
    map_one' := ext zero_add
    map_mul' _ _ := ext <| add_assoc _ _ }

@[simp]
/-
**CircleDeg1Lift.translate_apply** 是 Mathlib 中的一个定理，位于命名空间 `CircleDeg1Lift`。
形式化陈述：translate_apply (x y : Real) : translate (Multiplicative.ofAdd x) y = x + 
y
参数：x y : Real。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem translate_apply (x y : ℝ) : translate (Multiplicative.ofAdd x) y = x + y :=
  rfl

@[simp]
/-
**CircleDeg1Lift.translate_inv_apply** 是 Mathlib 中的一个定理，位于命名空间 `CircleDeg1Lift`。
形式化陈述：translate_inv_apply (x y : Real) : (translate <| Multiplicative.ofAdd x)⁻¹
 y = -x + y
参数：x y : Real。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem translate_inv_apply (x y : ℝ) : (translate <| Multiplicative.ofAdd x)⁻¹ y = -x + y :=
  rfl

@[simp]
/-
**CircleDeg1Lift.translate_zpow** 是 Mathlib 中的一个定理，位于命名空间 `CircleDeg1Lift`。
形式化陈述：translate_zpow (x : Real) (n : Int) : translate (Multiplicative.ofAdd x) ^
 n = translate (Multiplicative.ofAdd <| ↑n * x)
参数：x : Real；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zpow`：map_zpow [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (
f : F) (g : G) (n : Int) : f (g ^ n) = f g ^ n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem translate_zpow (x : ℝ) (n : ℤ) :
    translate (Multiplicative.ofAdd x) ^ n = translate (Multiplicative.ofAdd <| ↑n * x) := by
  simp only [← zsmul_eq_mul, ofAdd_zsmul, map_zpow]

@[simp]
/-
**CircleDeg1Lift.translate_pow** 是 Mathlib 中的一个定理，位于命名空间 `CircleDeg1Lift`。
形式化陈述：translate_pow (x : Real) (n : Nat) : translate (Multiplicative.ofAdd x) ^ 
n = translate (Multiplicative.ofAdd <| ↑n * x)
参数：x : Real；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CircleDeg1Lift.translate_zpow`：translate_zpow (x : Real) (n : Int) : tra
nslate (Multiplicative.ofAdd x) ^ n = translate (Multiplicative.ofAdd <| ↑n * x)
-/
theorem translate_pow (x : ℝ) (n : ℕ) :
    translate (Multiplicative.ofAdd x) ^ n = translate (Multiplicative.ofAdd <| ↑n * x) :=
  translate_zpow x n

@[simp]
/-
**CircleDeg1Lift.translate_iterate** 是 Mathlib 中的一个定理，位于命名空间 `CircleDeg1Lift`。
形式化陈述：translate_iterate (x : Real) (n : Nat) : (translate (Multiplicative.ofAdd 
x))^[n] = translate (Multiplicative.ofAdd <| ↑n * x)
参数：x : Real；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CircleDeg1Lift.coe_pow`：∀ (f : CircleDeg1Lift) (n : ℕ), ⇑(f ^ n) = (⇑f)^
[n]
· 使用引理 `Units.val_pow_eq_pow_val`：val_pow_eq_pow_val (n : Nat) : ↑(a ^ n) = (a ^
 n : α)
· 使用定理 `CircleDeg1Lift.translate_pow`：translate_pow (x : Real) (n : Nat) : trans
late (Multiplicative.ofAdd x) ^ n = translate (Multiplicative.ofAdd <| ↑n * x)
-/
theorem translate_iterate (x : ℝ) (n : ℕ) :
    (translate (Multiplicative.ofAdd x))^[n] = translate (Multiplicative.ofAdd <| ↑n * x) := by
  rw [← coe_pow, ← Units.val_pow_eq_pow_val, translate_pow]

/-!
### Commutativity with integer translations

In this section we prove that `f` commutes with translations by an integer number.
First we formulate these statements (for a natural or an integer number,
addition on the left or on the right, addition or subtraction) using `Function.Commute`,
then reformulate as `simp` lemmas `map_int_add` etc.
-/

/-
**CircleDeg1Lift.commute_nat_add** 是 Mathlib 中的一个定理，位于命名空间 `CircleDeg1Lift`。
形式化陈述：commute_nat_add (n : Nat) : Function.Commute f (n + ·)
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_left_iterate`：∀ {M : Type u_4} [inst : AddMonoid M] (a : M) (n : ℕ),
 (fun x => a + x)^[n] = fun x => n • a + x
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `nsmul_one`：∀ {A : Type u_2} [inst : AddMonoidWithOne A] (n : ℕ), n • 1 =
 ↑n
· 使用定理 `Function.Commute.iterate_right`：iterate_right (h : Commute f g) (n : Nat
) : Commute f g^[n]
· 使用定理 `CircleDeg1Lift.map_one_add`：map_one_add (x : Real) : f (1 + x) = 1 + f x

--- 原说明 ---
### Commutativity with integer translations

In this section we prove that `f` commutes with translations by an integer numbe
r.
First we formulate these statements (for a natural or an integer number,
addition on the left or on the right, addition or subtraction) using `Function.C
ommute`,
then reformulate as `simp` lemmas `map_int_add` etc.
-/
theorem commute_nat_add (n : ℕ) : Function.Commute f (n + ·) := by
  simpa only [nsmul_one, add_left_iterate] using Function.Commute.iterate_right f.map_one_add n
/-
**CircleDeg1Lift.commute_add_nat** 是 Mathlib 中的一个定理，位于命名空间 `CircleDeg1Lift`。
形式化陈述：commute_add_nat (n : Nat) : Function.Commute f (· + n)
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `CircleDeg1Lift.commute_nat_add`：commute_nat_add (n : Nat) : Function.Com
mute f (n + ·)
-/
theorem commute_add_nat (n : ℕ) : Function.Commute f (· + n) := by
  simp only [add_comm _ (n : ℝ), f.commute_nat_add n]
/-
**CircleDeg1Lift.commute_sub_nat** 是 Mathlib 中的一个定理，位于命名空间 `CircleDeg1Lift`。
形式化陈述：commute_sub_nat (n : Nat) : Function.Commute f (· - n)
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Function.Semiconj.inverses_right`：inverses_right (h : Semiconj f ga gb) 
(ha : RightInverse ga' ga) (hb : LeftInverse gb' gb) : Semiconj f ga' gb'
· 使用定理 `CircleDeg1Lift.commute_add_nat`：commute_add_nat (n : Nat) : Function.Com
mute f (· + n)
· 使用定理 `Equiv.right_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Functio
n.RightInverse self.invFun self.toFun
· 使用定理 `Equiv.left_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Function
.LeftInverse self.invFun self.toFun
-/
theorem commute_sub_nat (n : ℕ) : Function.Commute f (· - n) := by
  simpa only [sub_eq_add_neg] using!
    (f.commute_add_nat n).inverses_right (Equiv.addRight _).right_inv (Equiv.addRight _).left_inv
/-
**CircleDeg1Lift.commute_add_int** 是 Mathlib 中的一个定理，位于命名空间 `CircleDeg1Lift`。
形式化陈述：∀ (f : CircleDeg1Lift) (n : ℤ), Function.Commute ⇑f fun x => x + ↑n
参数：f : CircleDeg1Lift；n : ℤ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CircleDeg1Lift.commute_add_nat`：commute_add_nat (n : Nat) : Function.Com
mute f (· + n)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Int.cast_negSucc`：cast_negSucc (n : Nat) : (-[n+1] : R) = -(n + 1 : Nat)
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `neg_add_rev`：∀ {G : Type u_1} [inst : SubtractionMonoid G] (a b : G), -(
a + b) = -b + -a
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `CircleDeg1Lift.commute_sub_nat`：commute_sub_nat (n : Nat) : Function.Com
mute f (· - n)
-/
theorem commute_add_int : ∀ n : ℤ, Function.Commute f (· + n)
  | (n : ℕ) => f.commute_add_nat n
  | -[n+1] => by simpa [sub_eq_add_neg] using f.commute_sub_nat (n + 1)
/-
**CircleDeg1Lift.commute_int_add** 是 Mathlib 中的一个定理，位于命名空间 `CircleDeg1Lift`。
形式化陈述：commute_int_add (n : Int) : Function.Commute f (n + ·)
参数：n : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `CircleDeg1Lift.commute_add_int`：∀ (f : CircleDeg1Lift) (n : ℤ), Function
.Commute ⇑f fun x => x + ↑n
-/
theorem commute_int_add (n : ℤ) : Function.Commute f (n + ·) := by
  simpa only [add_comm _ (n : ℝ)] using f.commute_add_int n
/-
**CircleDeg1Lift.commute_sub_int** 是 Mathlib 中的一个定理，位于命名空间 `CircleDeg1Lift`。
形式化陈述：commute_sub_int (n : Int) : Function.Commute f (· - n)
参数：n : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Function.Semiconj.inverses_right`：inverses_right (h : Semiconj f ga gb) 
(ha : RightInverse ga' ga) (hb : LeftInverse gb' gb) : Semiconj f ga' gb'
· 使用定理 `CircleDeg1Lift.commute_add_int`：∀ (f : CircleDeg1Lift) (n : ℤ), Function
.Commute ⇑f fun x => x + ↑n
· 使用定理 `Equiv.right_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Functio
n.RightInverse self.invFun self.toFun
· 使用定理 `Equiv.left_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Function
.LeftInverse self.invFun self.toFun
-/
theorem commute_sub_int (n : ℤ) : Function.Commute f (· - n) := by
  simpa only [sub_eq_add_neg] using!
    (f.commute_add_int n).inverses_right (Equiv.addRight _).right_inv (Equiv.addRight _).left_inv

@[simp]
/-
**CircleDeg1Lift.map_int_add** 是 Mathlib 中的一个定理，位于命名空间 `CircleDeg1Lift`。
形式化陈述：map_int_add (m : Int) (x : Real) : f (m + x) = m + f x
参数：m : Int；x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CircleDeg1Lift.commute_int_add`：commute_int_add (n : Int) : Function.Com
mute f (n + ·)
-/
theorem map_int_add (m : ℤ) (x : ℝ) : f (m + x) = m + f x :=
  f.commute_int_add m x

@[simp]
/-
**CircleDeg1Lift.map_add_int** 是 Mathlib 中的一个定理，位于命名空间 `CircleDeg1Lift`。
形式化陈述：map_add_int (x : Real) (m : Int) : f (x + m) = f x + m
参数：x : Real；m : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CircleDeg1Lift.commute_add_int`：∀ (f : CircleDeg1Lift) (n : ℤ), Function
.Commute ⇑f fun x => x + ↑n
-/
theorem map_add_int (x : ℝ) (m : ℤ) : f (x + m) = f x + m :=
  f.commute_add_int m x

@[simp]
/-
**CircleDeg1Lift.map_sub_int** 是 Mathlib 中的一个定理，位于命名空间 `CircleDeg1Lift`。
形式化陈述：map_sub_int (x : Real) (n : Int) : f (x - n) = f x - n
参数：x : Real；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CircleDeg1Lift.commute_sub_int`：commute_sub_int (n : Int) : Function.Com
mute f (· - n)
-/
theorem map_sub_int (x : ℝ) (n : ℤ) : f (x - n) = f x - n :=
  f.commute_sub_int n x

@[simp]
/-
**CircleDeg1Lift.map_add_nat** 是 Mathlib 中的一个定理，位于命名空间 `CircleDeg1Lift`。
形式化陈述：map_add_nat (x : Real) (n : Nat) : f (x + n) = f x + n
参数：x : Real；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CircleDeg1Lift.map_add_int`：map_add_int (x : Real) (m : Int) : f (x + m)
 = f x + m
-/
theorem map_add_nat (x : ℝ) (n : ℕ) : f (x + n) = f x + n :=
  f.map_add_int x n

@[simp]
/-
**CircleDeg1Lift.map_nat_add** 是 Mathlib 中的一个定理，位于命名空间 `CircleDeg1Lift`。
形式化陈述：map_nat_add (n : Nat) (x : Real) : f (n + x) = n + f x
参数：n : Nat；x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CircleDeg1Lift.map_int_add`：map_int_add (m : Int) (x : Real) : f (m + x)
 = m + f x
-/
theorem map_nat_add (n : ℕ) (x : ℝ) : f (n + x) = n + f x :=
  f.map_int_add n x

@[simp]
/-
**CircleDeg1Lift.map_sub_nat** 是 Mathlib 中的一个定理，位于命名空间 `CircleDeg1Lift`。
形式化陈述：map_sub_nat (x : Real) (n : Nat) : f (x - n) = f x - n
参数：x : Real；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CircleDeg1Lift.map_sub_int`：map_sub_int (x : Real) (n : Int) : f (x - n)
 = f x - n
-/
theorem map_sub_nat (x : ℝ) (n : ℕ) : f (x - n) = f x - n :=
  f.map_sub_int x n
/-
**CircleDeg1Lift.map_int_of_map_zero** 是 Mathlib 中的一个定理，位于命名空间 `CircleDeg1Lift`。
形式化陈述：map_int_of_map_zero (n : Int) : f n = f 0 + n
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CircleDeg1Lift.map_add_int`：map_add_int (x : Real) (m : Int) : f (x + m)
 = f x + m
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
theorem map_int_of_map_zero (n : ℤ) : f n = f 0 + n := by rw [← f.map_add_int, zero_add]

@[simp]
/-
**CircleDeg1Lift.map_fract_sub_fract_eq** 是 Mathlib 中的一个定理，位于命名空间 `CircleDeg1Lif
t`。
形式化陈述：map_fract_sub_fract_eq (x : Real) : f (fract x) - fract x = f x - x
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.fract.eq_1`：∀ {α : Type u_2} [inst : Ring α] [inst_1 : LinearOrder α
] [inst_2 : FloorRing α] (a : α), Int.fract a = a - ↑⌊a⌋
· 使用定理 `CircleDeg1Lift.map_sub_int`：map_sub_int (x : Real) (n : Int) : f (x - n)
 = f x - n
· 使用定理 `sub_sub_sub_cancel_right`：∀ {G : Type u_3} [inst : AddGroup G] (a b c : 
G), a - c - (b - c) = a - b
-/
theorem map_fract_sub_fract_eq (x : ℝ) : f (fract x) - fract x = f x - x := by
  rw [Int.fract, f.map_sub_int, sub_sub_sub_cancel_right]

/-!
### Pointwise order on circle maps
-/


/-- Monotone circle maps form a lattice with respect to the pointwise order -/
/-
**CircleDeg1Lift.** 是 Mathlib 中的一个实例，位于命名空间 `CircleDeg1Lift`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Monotone circle maps form a lattice with respect to the pointwise order
-/
noncomputable instance : Lattice CircleDeg1Lift where
  sup f g :=
    { toFun := fun x => max (f x) (g x)
      monotone' := fun _ _ h => max_le_max (f.mono h) (g.mono h)
      -- TODO: generalize to `Monotone.max`
      map_add_one' := fun x => by simp [max_add_add_right] }
  le f g := ∀ x, f x ≤ g x
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
/-
**CircleDeg1Lift.sup_apply** 是 Mathlib 中的一个定理，位于命名空间 `CircleDeg1Lift`。
形式化陈述：sup_apply (x : Real) : (f ⊔ g) x = max (f x) (g x)
参数：x : Real。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sup_apply (x : ℝ) : (f ⊔ g) x = max (f x) (g x) :=
  rfl

@[simp]
/-
**CircleDeg1Lift.inf_apply** 是 Mathlib 中的一个定理，位于命名空间 `CircleDeg1Lift`。
形式化陈述：inf_apply (x : Real) : (f ⊓ g) x = min (f x) (g x)
参数：x : Real。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inf_apply (x : ℝ) : (f ⊓ g) x = min (f x) (g x) :=
  rfl
/-
**CircleDeg1Lift.iterate_monotone** 是 Mathlib 中的一个定理，位于命名空间 `CircleDeg1Lift`。
形式化陈述：iterate_monotone (n : Nat) : Monotone fun f : CircleDeg1Lift => f^[n]
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.iterate_le_of_le`：iterate_le_of_le {g : α -> α} (hf : Monotone 
f) (h : f <= g) (n : Nat) : f^[n] <= g^[n]
· 使用定理 `CircleDeg1Lift.monotone`：∀ (f : CircleDeg1Lift), Monotone ⇑f
-/
theorem iterate_monotone (n : ℕ) : Monotone fun f : CircleDeg1Lift => f^[n] := fun f _ h =>
  f.monotone.iterate_le_of_le h _
/-
**CircleDeg1Lift.iterate_mono** 是 Mathlib 中的一个定理，位于命名空间 `CircleDeg1Lift`。
形式化陈述：iterate_mono {f g : CircleDeg1Lift} (h : f <= g) (n : Nat) : f^[n] <= g^[n
]
参数：h : f <= g；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CircleDeg1Lift.iterate_monotone`：iterate_monotone (n : Nat) : Monotone f
un f : CircleDeg1Lift => f^[n]
-/
theorem iterate_mono {f g : CircleDeg1Lift} (h : f ≤ g) (n : ℕ) : f^[n] ≤ g^[n] :=
  iterate_monotone n h
/-
**CircleDeg1Lift.pow_mono** 是 Mathlib 中的一个定理，位于命名空间 `CircleDeg1Lift`。
形式化陈述：pow_mono {f g : CircleDeg1Lift} (h : f <= g) (n : Nat) : f ^ n <= g ^ n
参数：h : f <= g；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CircleDeg1Lift.coe_pow`：∀ (f : CircleDeg1Lift) (n : ℕ), ⇑(f ^ n) = (⇑f)^
[n]
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `CircleDeg1Lift.iterate_mono`：iterate_mono {f g : CircleDeg1Lift} (h : f 
<= g) (n : Nat) : f^[n] <= g^[n]
-/
theorem pow_mono {f g : CircleDeg1Lift} (h : f ≤ g) (n : ℕ) : f ^ n ≤ g ^ n := fun x => by
  simp only [coe_pow, iterate_mono h n x]
/-
**CircleDeg1Lift.pow_monotone** 是 Mathlib 中的一个定理，位于命名空间 `CircleDeg1Lift`。
形式化陈述：pow_monotone (n : Nat) : Monotone fun f : CircleDeg1Lift => f ^ n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CircleDeg1Lift.pow_mono`：pow_mono {f g : CircleDeg1Lift} (h : f <= g) (n
 : Nat) : f ^ n <= g ^ n
-/
theorem pow_monotone (n : ℕ) : Monotone fun f : CircleDeg1Lift => f ^ n := fun _ _ h => pow_mono h n

/-!
### Estimates on `(f * g) 0`

We prove the estimates `f 0 + ⌊g 0⌋ ≤ f (g 0) ≤ f 0 + ⌈g 0⌉` and some corollaries with added/removed
floors and ceils.

We also prove that for two semiconjugate maps `g₁`, `g₂`, the distance between `g₁ 0` and `g₂ 0`
is less than two.
-/

/-
**CircleDeg1Lift.map_le_of_map_zero** 是 Mathlib 中的一个定理，位于命名空间 `CircleDeg1Lift`。
形式化陈述：map_le_of_map_zero (x : Real) : f x <= f 0 + ⌈x⌉
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CircleDeg1Lift.monotone`：∀ (f : CircleDeg1Lift), Monotone ⇑f
· 使用定理 `Int.le_ceil`：le_ceil (a : α) : a <= ⌈a⌉
· 使用定理 `CircleDeg1Lift.map_int_of_map_zero`：map_int_of_map_zero (n : Int) : f n 
= f 0 + n

--- 原说明 ---
### Estimates on `(f * g) 0`

We prove the estimates `f 0 + ⌊g 0⌋ ≤ f (g 0) ≤ f 0 + ⌈g 0⌉` and some corollarie
s with added/removed
floors and ceils.

We also prove that for two semiconjugate maps `g₁`, `g₂`, the distance between `
g₁ 0` and `g₂ 0`
is less than two.
-/
theorem map_le_of_map_zero (x : ℝ) : f x ≤ f 0 + ⌈x⌉ :=
  calc
    f x ≤ f ⌈x⌉ := f.monotone <| le_ceil _
    _ = f 0 + ⌈x⌉ := f.map_int_of_map_zero _
/-
**CircleDeg1Lift.map_map_zero_le** 是 Mathlib 中的一个定理，位于命名空间 `CircleDeg1Lift`。
形式化陈述：map_map_zero_le : f (g 0) <= f 0 + ⌈g 0⌉
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CircleDeg1Lift.map_le_of_map_zero`：map_le_of_map_zero (x : Real) : f x <
= f 0 + ⌈x⌉
-/
theorem map_map_zero_le : f (g 0) ≤ f 0 + ⌈g 0⌉ :=
  f.map_le_of_map_zero (g 0)
/-
**CircleDeg1Lift.floor_map_map_zero_le** 是 Mathlib 中的一个定理，位于命名空间 `CircleDeg1Lift
`。
形式化陈述：floor_map_map_zero_le : ⌊f (g 0)⌋ <= ⌊f 0⌋ + ⌈g 0⌉
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.floor_mono`：floor_mono : Monotone (floor : R -> Int)
· 使用定理 `CircleDeg1Lift.map_map_zero_le`：map_map_zero_le : f (g 0) <= f 0 + ⌈g 0⌉
· 使用定理 `Int.floor_add_intCast`：floor_add_intCast (a : R) (z : Int) : ⌊a + z⌋ = ⌊
a⌋ + z
-/
theorem floor_map_map_zero_le : ⌊f (g 0)⌋ ≤ ⌊f 0⌋ + ⌈g 0⌉ :=
  calc
    ⌊f (g 0)⌋ ≤ ⌊f 0 + ⌈g 0⌉⌋ := floor_mono <| f.map_map_zero_le g
    _ = ⌊f 0⌋ + ⌈g 0⌉ := floor_add_intCast _ _
/-
**CircleDeg1Lift.ceil_map_map_zero_le** 是 Mathlib 中的一个定理，位于命名空间 `CircleDeg1Lift`
。
形式化陈述：ceil_map_map_zero_le : ⌈f (g 0)⌉ <= ⌈f 0⌉ + ⌈g 0⌉
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.ceil_mono`：ceil_mono : Monotone (ceil : R -> Int)
· 使用定理 `CircleDeg1Lift.map_map_zero_le`：map_map_zero_le : f (g 0) <= f 0 + ⌈g 0⌉
· 使用定理 `Int.ceil_add_intCast`：ceil_add_intCast (a : R) (z : Int) : ⌈a + z⌉ = ⌈a⌉
 + z
-/
theorem ceil_map_map_zero_le : ⌈f (g 0)⌉ ≤ ⌈f 0⌉ + ⌈g 0⌉ :=
  calc
    ⌈f (g 0)⌉ ≤ ⌈f 0 + ⌈g 0⌉⌉ := ceil_mono <| f.map_map_zero_le g
    _ = ⌈f 0⌉ + ⌈g 0⌉ := ceil_add_intCast _ _
/-
**CircleDeg1Lift.map_map_zero_lt** 是 Mathlib 中的一个定理，位于命名空间 `CircleDeg1Lift`。
形式化陈述：map_map_zero_lt : f (g 0) < f 0 + g 0 + 1
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CircleDeg1Lift.map_map_zero_le`：map_map_zero_le : f (g 0) <= f 0 + ⌈g 0⌉
· 使用定理 `add_lt_add_right`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LT α] [AddLe
ftStrictMono α] {b c : α}, b < c → ∀ (a : α), a + b < a + c
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Int.ceil_lt_add_one`：ceil_lt_add_one (a : R) : (⌈a⌉ : R) < a + 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
-/
theorem map_map_zero_lt : f (g 0) < f 0 + g 0 + 1 :=
  calc
    f (g 0) ≤ f 0 + ⌈g 0⌉ := f.map_map_zero_le g
    _ < f 0 + (g 0 + 1) := by gcongr; exact ceil_lt_add_one _
    _ = f 0 + g 0 + 1 := (add_assoc _ _ _).symm
/-
**CircleDeg1Lift.le_map_of_map_zero** 是 Mathlib 中的一个定理，位于命名空间 `CircleDeg1Lift`。
形式化陈述：le_map_of_map_zero (x : Real) : f 0 + ⌊x⌋ <= f x
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CircleDeg1Lift.map_int_of_map_zero`：map_int_of_map_zero (n : Int) : f n 
= f 0 + n
· 使用定理 `CircleDeg1Lift.monotone`：∀ (f : CircleDeg1Lift), Monotone ⇑f
· 使用定理 `Int.floor_le`：floor_le (a : α) : (⌊a⌋ : α) <= a
-/
theorem le_map_of_map_zero (x : ℝ) : f 0 + ⌊x⌋ ≤ f x :=
  calc
    f 0 + ⌊x⌋ = f ⌊x⌋ := (f.map_int_of_map_zero _).symm
    _ ≤ f x := f.monotone <| floor_le _
/-
**CircleDeg1Lift.le_map_map_zero** 是 Mathlib 中的一个定理，位于命名空间 `CircleDeg1Lift`。
形式化陈述：le_map_map_zero : f 0 + ⌊g 0⌋ <= f (g 0)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CircleDeg1Lift.le_map_of_map_zero`：le_map_of_map_zero (x : Real) : f 0 +
 ⌊x⌋ <= f x
-/
theorem le_map_map_zero : f 0 + ⌊g 0⌋ ≤ f (g 0) :=
  f.le_map_of_map_zero (g 0)
/-
**CircleDeg1Lift.le_floor_map_map_zero** 是 Mathlib 中的一个定理，位于命名空间 `CircleDeg1Lift
`。
形式化陈述：le_floor_map_map_zero : ⌊f 0⌋ + ⌊g 0⌋ <= ⌊f (g 0)⌋
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.floor_add_intCast`：floor_add_intCast (a : R) (z : Int) : ⌊a + z⌋ = ⌊
a⌋ + z
· 使用定理 `Int.floor_mono`：floor_mono : Monotone (floor : R -> Int)
· 使用定理 `CircleDeg1Lift.le_map_map_zero`：le_map_map_zero : f 0 + ⌊g 0⌋ <= f (g 0)
-/
theorem le_floor_map_map_zero : ⌊f 0⌋ + ⌊g 0⌋ ≤ ⌊f (g 0)⌋ :=
  calc
    ⌊f 0⌋ + ⌊g 0⌋ = ⌊f 0 + ⌊g 0⌋⌋ := (floor_add_intCast _ _).symm
    _ ≤ ⌊f (g 0)⌋ := floor_mono <| f.le_map_map_zero g
/-
**CircleDeg1Lift.le_ceil_map_map_zero** 是 Mathlib 中的一个定理，位于命名空间 `CircleDeg1Lift`
。
形式化陈述：le_ceil_map_map_zero : ⌈f 0⌉ + ⌊g 0⌋ <= ⌈(f * g) 0⌉
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.ceil_add_intCast`：ceil_add_intCast (a : R) (z : Int) : ⌈a + z⌉ = ⌈a⌉
 + z
· 使用定理 `Int.ceil_mono`：ceil_mono : Monotone (ceil : R -> Int)
· 使用定理 `CircleDeg1Lift.le_map_map_zero`：le_map_map_zero : f 0 + ⌊g 0⌋ <= f (g 0)
-/
theorem le_ceil_map_map_zero : ⌈f 0⌉ + ⌊g 0⌋ ≤ ⌈(f * g) 0⌉ :=
  calc
    ⌈f 0⌉ + ⌊g 0⌋ = ⌈f 0 + ⌊g 0⌋⌉ := (ceil_add_intCast _ _).symm
    _ ≤ ⌈f (g 0)⌉ := ceil_mono <| f.le_map_map_zero g
/-
**CircleDeg1Lift.lt_map_map_zero** 是 Mathlib 中的一个定理，位于命名空间 `CircleDeg1Lift`。
形式化陈述：lt_map_map_zero : f 0 + g 0 - 1 < f (g 0)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `add_sub_assoc`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b c : G), a +
 b - c = a + (b - c)
· 使用定理 `add_lt_add_right`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LT α] [AddLe
ftStrictMono α] {b c : α}, b < c → ∀ (a : α), a + b < a + c
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Int.sub_one_lt_floor`：sub_one_lt_floor (a : R) : a - 1 < ⌊a⌋
· 使用定理 `CircleDeg1Lift.le_map_map_zero`：le_map_map_zero : f 0 + ⌊g 0⌋ <= f (g 0)
-/
theorem lt_map_map_zero : f 0 + g 0 - 1 < f (g 0) :=
  calc
    f 0 + g 0 - 1 = f 0 + (g 0 - 1) := add_sub_assoc _ _ _
    _ < f 0 + ⌊g 0⌋ := by gcongr; exact sub_one_lt_floor _
    _ ≤ f (g 0) := f.le_map_map_zero g
/-
**CircleDeg1Lift.dist_map_map_zero_lt** 是 Mathlib 中的一个定理，位于命名空间 `CircleDeg1Lift`
。
形式化陈述：dist_map_map_zero_lt : dist (f 0 + g 0) (f (g 0)) < 1
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `Real.dist_eq`：Real.dist_eq (x y : Real) : dist x y = |x - y|
· 使用定理 `abs_lt`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LinearOrder α] [A
ddLeftMono α] {a b : α} [AddRightMono α],   |a| < b ↔ -b < a ∧ a < b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `lt_sub_iff_add_lt'`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : LT 
α] [AddLeftStrictMono α] {a b c : α}, b < c - a ↔ a + b < c
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `sub_lt_iff_lt_add'`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : LT 
α] [AddLeftStrictMono α] {a b c : α}, a - b < c ↔ a < b + c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `CircleDeg1Lift.lt_map_map_zero`：lt_map_map_zero : f 0 + g 0 - 1 < f (g 0
)
· 使用定理 `CircleDeg1Lift.map_map_zero_lt`：map_map_zero_lt : f (g 0) < f 0 + g 0 + 
1
-/
theorem dist_map_map_zero_lt : dist (f 0 + g 0) (f (g 0)) < 1 := by
  rw [dist_comm, Real.dist_eq, abs_lt, lt_sub_iff_add_lt', sub_lt_iff_lt_add', ← sub_eq_add_neg]
  exact ⟨f.lt_map_map_zero g, f.map_map_zero_lt g⟩
/-
**CircleDeg1Lift.dist_map_zero_lt_of_semiconj** 是 Mathlib 中的一个定理，位于命名空间 `CircleD
eg1Lift`。
形式化陈述：dist_map_zero_lt_of_semiconj {f g₁ g₂ : CircleDeg1Lift} (h : Function.Semi
conj f g₁ g₂) : dist (g₁ 0) (g₂ 0) < 2
参数：h : Function.Semiconj f g₁ g₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `dist_triangle`：dist_triangle (x y z : α) : dist x z <= dist x y + dist y
 z
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Function.Semiconj.eq`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {ga : 
α → α} {gb : β → β},   Function.Semiconj f ga gb → ∀ (x : α), f (ga x) = gb (f x
)
· 使用定理 `sub_sub_eq_add_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b c
 : α), a - (b - c) = a + c - b
· 使用定理 `sub_sub`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b c : α), 
a - b - c = a - (b + c)
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `abs_sub_comm`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] 
(a b : α), |a - b| = |b - a|
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `add_lt_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftStrictMono α] [AddRightStrictMono α] {a b c d : α},   a < b → c < d → a + c < 
…
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `CircleDeg1Lift.dist_map_map_zero_lt`：dist_map_map_zero_lt : dist (f 0 + 
g 0) (f (g 0)) < 1
· 使用定理 `one_add_one_eq_two`：one_add_one_eq_two [AddMonoidWithOne R] : 1 + 1 = (2
 : R)
-/
theorem dist_map_zero_lt_of_semiconj {f g₁ g₂ : CircleDeg1Lift} (h : Function.Semiconj f g₁ g₂) :
    dist (g₁ 0) (g₂ 0) < 2 :=
  calc
    dist (g₁ 0) (g₂ 0) ≤ dist (g₁ 0) (f (g₁ 0) - f 0) + dist _ (g₂ 0) := dist_triangle _ _ _
    _ = dist (f 0 + g₁ 0) (f (g₁ 0)) + dist (g₂ 0 + f 0) (g₂ (f 0)) := by
      simp only [h.eq, Real.dist_eq, sub_sub, add_comm (f 0), sub_sub_eq_add_sub,
        abs_sub_comm (g₂ (f 0))]
    _ < 1 + 1 := add_lt_add (f.dist_map_map_zero_lt g₁) (g₂.dist_map_map_zero_lt f)
    _ = 2 := one_add_one_eq_two
/-
**CircleDeg1Lift.dist_map_zero_lt_of_semiconjBy** 是 Mathlib 中的一个定理，位于命名空间 `Circl
eDeg1Lift`。
形式化陈述：dist_map_zero_lt_of_semiconjBy {f g₁ g₂ : CircleDeg1Lift} (h : SemiconjBy 
f g₁ g₂) : dist (g₁ 0) (g₂ 0) < 2
参数：h : SemiconjBy f g₁ g₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CircleDeg1Lift.dist_map_zero_lt_of_semiconj`：dist_map_zero_lt_of_semicon
j {f g₁ g₂ : CircleDeg1Lift} (h : Function.Semiconj f g₁ g₂) : dist (g₁ 0) (g₂ 0
) < 2
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CircleDeg1Lift.semiconjBy_iff_semiconj`：semiconjBy_iff_semiconj {f g₁ g₂
 : CircleDeg1Lift} : SemiconjBy f g₁ g₂ ↔ Semiconj f g₁ g₂
-/
theorem dist_map_zero_lt_of_semiconjBy {f g₁ g₂ : CircleDeg1Lift} (h : SemiconjBy f g₁ g₂) :
    dist (g₁ 0) (g₂ 0) < 2 :=
  dist_map_zero_lt_of_semiconj <| semiconjBy_iff_semiconj.1 h

/-!
### Limits at infinities and continuity
-/

/-
**CircleDeg1Lift.tendsto_atBot** 是 Mathlib 中的一个定理，位于命名空间 `CircleDeg1Lift`。
形式化陈述：∀ (f : CircleDeg1Lift), Filter.Tendsto (⇑f) Filter.atBot Filter.atBot
参数：f : CircleDeg1Lift；⇑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.tendsto_atBot_mono`：∀ {α : Type u_3} {β : Type u_4} [inst : Preor
der β] {l : Filter α} {f g : α → β},   (∀ (n : α), g n ≤ f n) → Filter.Tendsto f
 l Filter.atBot…
· 使用定理 `CircleDeg1Lift.map_le_of_map_zero`：map_le_of_map_zero (x : Real) : f x <
= f 0 + ⌈x⌉
· 使用定理 `Filter.tendsto_atBot_add_const_left`：∀ {α : Type u_1} {G : Type u_2} [in
st : AddCommGroup G] [inst_1 : PartialOrder G] [IsOrderedAddMonoid G] (l : Filte
r α)   {f : α → G} (C : G…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Int.ceil_lt_add_one`：ceil_lt_add_one (a : R) : (⌈a⌉ : R) < a + 1
· 使用定理 `Filter.tendsto_atBot_add_const_right`：∀ {α : Type u_1} {G : Type u_2} [i
nst : AddCommGroup G] [inst_1 : PartialOrder G] [IsOrderedAddMonoid G] (l : Filt
er α)   {f : α → G} (C : G…
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x

--- 原说明 ---
### Limits at infinities and continuity
-/
protected theorem tendsto_atBot : Tendsto f atBot atBot :=
  tendsto_atBot_mono f.map_le_of_map_zero <| tendsto_atBot_add_const_left _ _ <|
    (tendsto_atBot_mono fun x => (ceil_lt_add_one x).le) <|
      tendsto_atBot_add_const_right _ _ tendsto_id
/-
**CircleDeg1Lift.tendsto_atTop** 是 Mathlib 中的一个定理，位于命名空间 `CircleDeg1Lift`。
形式化陈述：∀ (f : CircleDeg1Lift), Filter.Tendsto (⇑f) Filter.atTop Filter.atTop
参数：f : CircleDeg1Lift；⇑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.tendsto_atTop_mono`：tendsto_atTop_mono [Preorder β] {l : Filter α
} {f g : α -> β} (h : forall n, f n <= g n) : Tendsto f l atTop -> Tendsto g l a
tTop
· 使用定理 `CircleDeg1Lift.le_map_of_map_zero`：le_map_of_map_zero (x : Real) : f 0 +
 ⌊x⌋ <= f x
· 使用定理 `Filter.tendsto_atTop_add_const_left`：∀ {α : Type u_1} {G : Type u_2} [in
st : AddCommGroup G] [inst_1 : PartialOrder G] [IsOrderedAddMonoid G] (l : Filte
r α)   {f : α → G} (C : G…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Int.sub_one_lt_floor`：sub_one_lt_floor (a : R) : a - 1 < ⌊a⌋
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Filter.tendsto_atTop_add_const_right`：∀ {α : Type u_1} {G : Type u_2} [i
nst : AddCommGroup G] [inst_1 : PartialOrder G] [IsOrderedAddMonoid G] (l : Filt
er α)   {f : α → G} (C : G…
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x
-/
protected theorem tendsto_atTop : Tendsto f atTop atTop :=
  tendsto_atTop_mono f.le_map_of_map_zero <| tendsto_atTop_add_const_left _ _ <|
    (tendsto_atTop_mono fun x => (sub_one_lt_floor x).le) <| by
      simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right _ _ tendsto_id
/-
**CircleDeg1Lift.continuous_iff_surjective** 是 Mathlib 中的一个定理，位于命名空间 `CircleDeg1
Lift`。
形式化陈述：continuous_iff_surjective : Continuous f ↔ Function.Surjective f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.surjective`：Continuous.surjective {f : α -> δ} (hf : Continuo
us f) (h_top : Tendsto f atTop atTop) (h_bot : Tendsto f atBot atBot) : Function
.Surjective…
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `CircleDeg1Lift.tendsto_atTop`：∀ (f : CircleDeg1Lift), Filter.Tendsto (⇑f
) Filter.atTop Filter.atTop
· 使用定理 `CircleDeg1Lift.tendsto_atBot`：∀ (f : CircleDeg1Lift), Filter.Tendsto (⇑f
) Filter.atBot Filter.atBot
· 使用定理 `Monotone.continuous_of_surjective`：Monotone.continuous_of_surjective [De
nselyOrdered β] {f : α -> β} (h_mono : Monotone f) (h_surj : Function.Surjective
 f) : Continuous f
· 使用定理 `CircleDeg1Lift.monotone`：∀ (f : CircleDeg1Lift), Monotone ⇑f
-/
theorem continuous_iff_surjective : Continuous f ↔ Function.Surjective f :=
  ⟨fun h => h.surjective f.tendsto_atTop f.tendsto_atBot, f.monotone.continuous_of_surjective⟩

/-!
### Estimates on `(f^n) x`

If we know that `f x` is `≤`/`<`/`≥`/`>`/`=` to `x + m`, then we have a similar estimate on
`f^[n] x` and `x + n * m`.

For `≤`, `≥`, and `=` we formulate both `of` (implication) and `iff` versions because implications
work for `n = 0`. For `<` and `>` we formulate only `iff` versions.
-/


/-
**CircleDeg1Lift.iterate_le_of_map_le_add_int** 是 Mathlib 中的一个定理，位于命名空间 `CircleD
eg1Lift`。
形式化陈述：iterate_le_of_map_le_add_int {x : Real} {m : Int} (h : f x <= x + m) (n : 
Nat) : f^[n] x <= x + n * m
参数：h : f x <= x + m；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `add_right_iterate`：∀ {M : Type u_4} [inst : AddMonoid M] (a : M) (n : ℕ)
, (fun x => x + a)^[n] = fun x => x + n • a
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `Function.Commute.iterate_le_of_map_le`：iterate_le_of_map_le (h : Commute
 f g) (hf : Monotone f) (hg : Monotone g) {x} (hx : f x <= g x) (n : Nat) : f^[n
] x <= g^[n] x
· 使用定理 `CircleDeg1Lift.commute_add_int`：∀ (f : CircleDeg1Lift) (n : ℤ), Function
.Commute ⇑f fun x => x + ↑n
· 使用定理 `CircleDeg1Lift.monotone`：∀ (f : CircleDeg1Lift), Monotone ⇑f
· 使用定理 `Monotone.add_const`：∀ {α : Type u_1} {β : Type u_2} [inst : Add α] [inst
_1 : Preorder α] [inst_2 : Preorder β] {f : β → α} [AddRightMono α],   Monotone 
f → ∀ (a…
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `monotone_id`：monotone_id [Preorder α] : Monotone (id : α -> α)

--- 原说明 ---
### Estimates on `(f^n) x`

If we know that `f x` is `≤`/`<`/`≥`/`>`/`=` to `x + m`, then we have a similar 
estimate on
`f^[n] x` and `x + n * m`.

For `≤`, `≥`, and `=` we formulate both `of` (implication) and `iff` versions be
cause implications
work for `n = 0`. For `<` and `>` we formulate only `iff` versions.
-/
theorem iterate_le_of_map_le_add_int {x : ℝ} {m : ℤ} (h : f x ≤ x + m) (n : ℕ) :
    f^[n] x ≤ x + n * m := by
  simpa only [nsmul_eq_mul, add_right_iterate] using
    (f.commute_add_int m).iterate_le_of_map_le f.monotone (monotone_id.add_const (m : ℝ)) h n
/-
**CircleDeg1Lift.le_iterate_of_add_int_le_map** 是 Mathlib 中的一个定理，位于命名空间 `CircleD
eg1Lift`。
形式化陈述：le_iterate_of_add_int_le_map {x : Real} {m : Int} (h : x + m <= f x) (n : 
Nat) : x + n * m <= f^[n] x
参数：h : x + m <= f x；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `add_right_iterate`：∀ {M : Type u_4} [inst : AddMonoid M] (a : M) (n : ℕ)
, (fun x => x + a)^[n] = fun x => x + n • a
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `Function.Commute.iterate_le_of_map_le`：iterate_le_of_map_le (h : Commute
 f g) (hf : Monotone f) (hg : Monotone g) {x} (hx : f x <= g x) (n : Nat) : f^[n
] x <= g^[n] x
· 使用定理 `Function.Commute.symm`：symm (h : Commute f g) : Commute g f
· 使用定理 `CircleDeg1Lift.commute_add_int`：∀ (f : CircleDeg1Lift) (n : ℤ), Function
.Commute ⇑f fun x => x + ↑n
· 使用定理 `Monotone.add_const`：∀ {α : Type u_1} {β : Type u_2} [inst : Add α] [inst
_1 : Preorder α] [inst_2 : Preorder β] {f : β → α} [AddRightMono α],   Monotone 
f → ∀ (a…
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `monotone_id`：monotone_id [Preorder α] : Monotone (id : α -> α)
· 使用定理 `CircleDeg1Lift.monotone`：∀ (f : CircleDeg1Lift), Monotone ⇑f
-/
theorem le_iterate_of_add_int_le_map {x : ℝ} {m : ℤ} (h : x + m ≤ f x) (n : ℕ) :
    x + n * m ≤ f^[n] x := by
  simpa only [nsmul_eq_mul, add_right_iterate] using
    (f.commute_add_int m).symm.iterate_le_of_map_le (monotone_id.add_const (m : ℝ)) f.monotone h n
/-
**CircleDeg1Lift.iterate_eq_of_map_eq_add_int** 是 Mathlib 中的一个定理，位于命名空间 `CircleD
eg1Lift`。
形式化陈述：iterate_eq_of_map_eq_add_int {x : Real} {m : Int} (h : f x = x + m) (n : N
at) : f^[n] x = x + n * m
参数：h : f x = x + m；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `add_right_iterate`：∀ {M : Type u_4} [inst : AddMonoid M] (a : M) (n : ℕ)
, (fun x => x + a)^[n] = fun x => x + n • a
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `Function.Commute.iterate_eq_of_map_eq`：iterate_eq_of_map_eq (h : Commute
 f g) (n : Nat) {x} (hx : f x = g x) : f^[n] x = g^[n] x
· 使用定理 `CircleDeg1Lift.commute_add_int`：∀ (f : CircleDeg1Lift) (n : ℤ), Function
.Commute ⇑f fun x => x + ↑n
-/
theorem iterate_eq_of_map_eq_add_int {x : ℝ} {m : ℤ} (h : f x = x + m) (n : ℕ) :
    f^[n] x = x + n * m := by
  simpa only [nsmul_eq_mul, add_right_iterate] using (f.commute_add_int m).iterate_eq_of_map_eq n h
/-
**CircleDeg1Lift.iterate_pos_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `CircleDeg1Lift`。
形式化陈述：iterate_pos_le_iff {x : Real} {m : Int} {n : Nat} (hn : 0 < n) : f^[n] x <
= x + n * m ↔ f x <= x + m
参数：hn : 0 < n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `add_right_iterate`：∀ {M : Type u_4} [inst : AddMonoid M] (a : M) (n : ℕ)
, (fun x => x + a)^[n] = fun x => x + n • a
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `Function.Commute.iterate_pos_le_iff_map_le`：iterate_pos_le_iff_map_le (h
 : Commute f g) (hf : Monotone f) (hg : StrictMono g) {x n} (hn : 0 < n) : f^[n]
 x <= g^[n] x ↔ f x <= g x
· 使用定理 `CircleDeg1Lift.commute_add_int`：∀ (f : CircleDeg1Lift) (n : ℤ), Function
.Commute ⇑f fun x => x + ↑n
· 使用定理 `CircleDeg1Lift.monotone`：∀ (f : CircleDeg1Lift), Monotone ⇑f
· 使用定理 `StrictMono.add_const`：∀ {α : Type u_1} {β : Type u_2} [inst : Add α] [in
st_1 : Preorder α] [inst_2 : Preorder β] {f : β → α}   [AddRightStrictMono α], S
trictMono …
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `strictMono_id`：strictMono_id [Preorder α] : StrictMono (id : α -> α)
-/
theorem iterate_pos_le_iff {x : ℝ} {m : ℤ} {n : ℕ} (hn : 0 < n) :
    f^[n] x ≤ x + n * m ↔ f x ≤ x + m := by
  simpa only [nsmul_eq_mul, add_right_iterate] using
    (f.commute_add_int m).iterate_pos_le_iff_map_le f.monotone (strictMono_id.add_const (m : ℝ)) hn
/-
**CircleDeg1Lift.iterate_pos_lt_iff** 是 Mathlib 中的一个定理，位于命名空间 `CircleDeg1Lift`。
形式化陈述：iterate_pos_lt_iff {x : Real} {m : Int} {n : Nat} (hn : 0 < n) : f^[n] x <
 x + n * m ↔ f x < x + m
参数：hn : 0 < n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `add_right_iterate`：∀ {M : Type u_4} [inst : AddMonoid M] (a : M) (n : ℕ)
, (fun x => x + a)^[n] = fun x => x + n • a
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `Function.Commute.iterate_pos_lt_iff_map_lt`：iterate_pos_lt_iff_map_lt (h
 : Commute f g) (hf : Monotone f) (hg : StrictMono g) {x n} (hn : 0 < n) : f^[n]
 x < g^[n] x ↔ f x < g x
· 使用定理 `CircleDeg1Lift.commute_add_int`：∀ (f : CircleDeg1Lift) (n : ℤ), Function
.Commute ⇑f fun x => x + ↑n
· 使用定理 `CircleDeg1Lift.monotone`：∀ (f : CircleDeg1Lift), Monotone ⇑f
· 使用定理 `StrictMono.add_const`：∀ {α : Type u_1} {β : Type u_2} [inst : Add α] [in
st_1 : Preorder α] [inst_2 : Preorder β] {f : β → α}   [AddRightStrictMono α], S
trictMono …
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `strictMono_id`：strictMono_id [Preorder α] : StrictMono (id : α -> α)
-/
theorem iterate_pos_lt_iff {x : ℝ} {m : ℤ} {n : ℕ} (hn : 0 < n) :
    f^[n] x < x + n * m ↔ f x < x + m := by
  simpa only [nsmul_eq_mul, add_right_iterate] using
    (f.commute_add_int m).iterate_pos_lt_iff_map_lt f.monotone (strictMono_id.add_const (m : ℝ)) hn
/-
**CircleDeg1Lift.iterate_pos_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `CircleDeg1Lift`。
形式化陈述：iterate_pos_eq_iff {x : Real} {m : Int} {n : Nat} (hn : 0 < n) : f^[n] x =
 x + n * m ↔ f x = x + m
参数：hn : 0 < n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `add_right_iterate`：∀ {M : Type u_4} [inst : AddMonoid M] (a : M) (n : ℕ)
, (fun x => x + a)^[n] = fun x => x + n • a
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `Function.Commute.iterate_pos_eq_iff_map_eq`：iterate_pos_eq_iff_map_eq (h
 : Commute f g) (hf : Monotone f) (hg : StrictMono g) {x n} (hn : 0 < n) : f^[n]
 x = g^[n] x ↔ f x = g x
· 使用定理 `CircleDeg1Lift.commute_add_int`：∀ (f : CircleDeg1Lift) (n : ℤ), Function
.Commute ⇑f fun x => x + ↑n
· 使用定理 `CircleDeg1Lift.monotone`：∀ (f : CircleDeg1Lift), Monotone ⇑f
· 使用定理 `StrictMono.add_const`：∀ {α : Type u_1} {β : Type u_2} [inst : Add α] [in
st_1 : Preorder α] [inst_2 : Preorder β] {f : β → α}   [AddRightStrictMono α], S
trictMono …
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `strictMono_id`：strictMono_id [Preorder α] : StrictMono (id : α -> α)
-/
theorem iterate_pos_eq_iff {x : ℝ} {m : ℤ} {n : ℕ} (hn : 0 < n) :
    f^[n] x = x + n * m ↔ f x = x + m := by
  simpa only [nsmul_eq_mul, add_right_iterate] using
    (f.commute_add_int m).iterate_pos_eq_iff_map_eq f.monotone (strictMono_id.add_const (m : ℝ)) hn
/-
**CircleDeg1Lift.le_iterate_pos_iff** 是 Mathlib 中的一个定理，位于命名空间 `CircleDeg1Lift`。
形式化陈述：le_iterate_pos_iff {x : Real} {m : Int} {n : Nat} (hn : 0 < n) : x + n * m
 <= f^[n] x ↔ x + m <= f x
参数：hn : 0 < n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_congr`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `CircleDeg1Lift.iterate_pos_lt_iff`：iterate_pos_lt_iff {x : Real} {m : In
t} {n : Nat} (hn : 0 < n) : f^[n] x < x + n * m ↔ f x < x + m
-/
theorem le_iterate_pos_iff {x : ℝ} {m : ℤ} {n : ℕ} (hn : 0 < n) :
    x + n * m ≤ f^[n] x ↔ x + m ≤ f x := by
  simpa only [not_lt] using not_congr (f.iterate_pos_lt_iff hn)
/-
**CircleDeg1Lift.lt_iterate_pos_iff** 是 Mathlib 中的一个定理，位于命名空间 `CircleDeg1Lift`。
形式化陈述：lt_iterate_pos_iff {x : Real} {m : Int} {n : Nat} (hn : 0 < n) : x + n * m
 < f^[n] x ↔ x + m < f x
参数：hn : 0 < n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_congr`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `CircleDeg1Lift.iterate_pos_le_iff`：iterate_pos_le_iff {x : Real} {m : In
t} {n : Nat} (hn : 0 < n) : f^[n] x <= x + n * m ↔ f x <= x + m
-/
theorem lt_iterate_pos_iff {x : ℝ} {m : ℤ} {n : ℕ} (hn : 0 < n) :
    x + n * m < f^[n] x ↔ x + m < f x := by
  simpa only [not_le] using not_congr (f.iterate_pos_le_iff hn)
/-
**CircleDeg1Lift.mul_floor_map_zero_le_floor_iterate_zero** 是 Mathlib 中的一个定理，位于命
名空间 `CircleDeg1Lift`。
形式化陈述：mul_floor_map_zero_le_floor_iterate_zero (n : Nat) : ↑n * ⌊f 0⌋ <= ⌊f^[n] 
0⌋
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.le_floor`：le_floor : z <= ⌊a⌋ ↔ (z : α) <= a
· 使用引理 `Int.cast_mul`：cast_mul {α : Type*} [NonAssocRing α] : forall m n, ((m * 
n : Int) : α) = m * n
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `CircleDeg1Lift.le_iterate_of_add_int_le_map`：le_iterate_of_add_int_le_ma
p {x : Real} {m : Int} (h : x + m <= f x) (n : Nat) : x + n * m <= f^[n] x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
theorem mul_floor_map_zero_le_floor_iterate_zero (n : ℕ) : ↑n * ⌊f 0⌋ ≤ ⌊f^[n] 0⌋ := by
  rw [le_floor, Int.cast_mul, Int.cast_natCast, ← zero_add ((n : ℝ) * _)]
  apply le_iterate_of_add_int_le_map
  simp [floor_le]

/-!
### Definition of translation number
-/

noncomputable section

/-- An auxiliary sequence used to define the translation number. -/
/-
**CircleDeg1Lift.transnumAuxSeq** 是 Mathlib 中的一个定义，位于命名空间 `CircleDeg1Lift`。
形式化陈述：transnumAuxSeq (n : Nat) : Real
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An auxiliary sequence used to define the translation number.
-/
def transnumAuxSeq (n : ℕ) : ℝ :=
  (f ^ (2 ^ n : ℕ)) 0 / 2 ^ n

/-- The translation number of a `CircleDeg1Lift`, $τ(f)=\lim_{n→∞}\frac{f^n(x)-x}{n}$. We use
an auxiliary sequence `\frac{f^{2^n}(0)}{2^n}` to define `τ(f)` because some proofs are simpler
this way. -/
/-
**CircleDeg1Lift.translationNumber** 是 Mathlib 中的一个定义，位于命名空间 `CircleDeg1Lift`。
形式化陈述：translationNumber : Real
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α

--- 原说明 ---
The translation number of a `CircleDeg1Lift`, $τ(f)=\lim_{n→∞}\frac{f^n(x)-x}{n}
$. We use
an auxiliary sequence `\frac{f^{2^n}(0)}{2^n}` to define `τ(f)` because some pro
ofs are simpler
this way.
-/
def translationNumber : ℝ :=
  limUnder atTop f.transnumAuxSeq

end

-- TODO: choose two different symbols for `CircleDeg1Lift.translationNumber` and the future
-- `circle_mono_homeo.rotation_number`, then make them `localized notation`s
local notation "τ" => translationNumber

/-
**CircleDeg1Lift.transnumAuxSeq_def** 是 Mathlib 中的一个定理，位于命名空间 `CircleDeg1Lift`。
形式化陈述：transnumAuxSeq_def : f.transnumAuxSeq = fun n : Nat => (f ^ (2 ^ n : Nat))
 0 / 2 ^ n
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem transnumAuxSeq_def : f.transnumAuxSeq = fun n : ℕ => (f ^ (2 ^ n : ℕ)) 0 / 2 ^ n :=
  rfl
/-
**CircleDeg1Lift.translationNumber_eq_of_tendsto_aux** 是 Mathlib 中的一个定理，位于命名空间 `
CircleDeg1Lift`。
形式化陈述：translationNumber_eq_of_tendsto_aux {τ' : Real} (h : Tendsto f.transnumAux
Seq atTop (𝓝 τ')) : τ f = τ'
参数：h : Tendsto f.transnumAuxSeq atTop (𝓝 τ')。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.limUnder_eq`：Filter.Tendsto.limUnder_eq {x : X} {f : Filt
er Y} [NeBot f] {g : Y -> X} (h : Tendsto g f (𝓝 x)) : @limUnder _ _ _ ⟨x⟩ f g =
 x
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
theorem translationNumber_eq_of_tendsto_aux {τ' : ℝ} (h : Tendsto f.transnumAuxSeq atTop (𝓝 τ')) :
    τ f = τ' :=
  h.limUnder_eq
/-
**CircleDeg1Lift.translationNumber_eq_of_tendsto** 是 Mathlib 中的一个定理，位于命名空间 `Circ
leDeg1Lift`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem translationNumber_eq_of_tendsto₀ {τ' : ℝ}
    (h : Tendsto (fun n : ℕ => f^[n] 0 / n) atTop (𝓝 τ')) : τ f = τ' :=
  f.translationNumber_eq_of_tendsto_aux <| by
    simpa [Function.comp_def, transnumAuxSeq_def, coe_pow] using
      h.comp (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)
/-
**CircleDeg1Lift.translationNumber_eq_of_tendsto** 是 Mathlib 中的一个定理，位于命名空间 `Circ
leDeg1Lift`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem translationNumber_eq_of_tendsto₀' {τ' : ℝ}
    (h : Tendsto (fun n : ℕ => f^[n + 1] 0 / (n + 1)) atTop (𝓝 τ')) : τ f = τ' :=
  f.translationNumber_eq_of_tendsto₀ <| (tendsto_add_atTop_iff_nat 1).1 (mod_cast h)
/-
**CircleDeg1Lift.transnumAuxSeq_zero** 是 Mathlib 中的一个定理，位于命名空间 `CircleDeg1Lift`。
形式化陈述：transnumAuxSeq_zero : f.transnumAuxSeq 0 = f 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem transnumAuxSeq_zero : f.transnumAuxSeq 0 = f 0 := by simp [transnumAuxSeq]
/-
**CircleDeg1Lift.transnumAuxSeq_dist_lt** 是 Mathlib 中的一个定理，位于命名空间 `CircleDeg1Lif
t`。
形式化陈述：transnumAuxSeq_dist_lt (n : Nat) : dist (f.transnumAuxSeq n) (f.transnumAu
xSeq (n + 1)) < 1 / 2 / 2 ^ n
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `zero_lt_two`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : Part
ialOrder α] [ZeroLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 2
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_div`：div_div : a / b / c = a / (b * c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `abs_of_pos`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] {a
 : α} [AddLeftMono α], 0 < a → |a| = a
· 使用定理 `abs_div`：abs_div (a b : α) : |a / b| = |a| / |b|
· 使用定理 `sub_div`：sub_div (a b c : K) : (a - b) / c = a / c - b / c
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用引理 `mul_div_mul_left`：mul_div_mul_left (a b : G₀) (hc : c != 0) : c * a / (c
 * b) = a / b
· 使用引理 `two_ne_zero'`：two_ne_zero' [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `CircleDeg1Lift.mul_apply`：mul_apply (x) : (f * g) x = f (g x)
· 使用引理 `div_lt_div_of_pos_right`：div_lt_div_of_pos_right (h : a < b) (hc : 0 < c
) : a / c < b / c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `CircleDeg1Lift.dist_map_map_zero_lt`：dist_map_map_zero_lt : dist (f 0 + 
g 0) (f (g 0)) < 1
· 使用定理 `abs_pos_of_pos`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LinearOrd
er α] [AddLeftMono α] {a : α}, 0 < a → 0 < |a|
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
（共 31 条，此处仅展示前 30 条）
-/
theorem transnumAuxSeq_dist_lt (n : ℕ) :
    dist (f.transnumAuxSeq n) (f.transnumAuxSeq (n + 1)) < 1 / 2 / 2 ^ n := by
  have : 0 < (2 ^ (n + 1) : ℝ) := pow_pos zero_lt_two _
  rw [div_div, ← pow_succ', ← abs_of_pos this]
  calc
    _ = dist ((f ^ 2 ^ n) 0 + (f ^ 2 ^ n) 0) ((f ^ 2 ^ n) ((f ^ 2 ^ n) 0)) / |2 ^ (n + 1)| := by
      simp_rw [transnumAuxSeq, Real.dist_eq]
      rw [← abs_div, sub_div, pow_succ, pow_succ', ← two_mul, mul_div_mul_left _ _ (two_ne_zero' ℝ),
        pow_mul, sq, mul_apply]
    _ < _ := by gcongr; exact (f ^ 2 ^ n).dist_map_map_zero_lt (f ^ 2 ^ n)
/-
**CircleDeg1Lift.tendsto_translationNumber_aux** 是 Mathlib 中的一个定理，位于命名空间 `Circle
Deg1Lift`。
形式化陈述：tendsto_translationNumber_aux : Tendsto f.transnumAuxSeq atTop (𝓝 <| τ f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CauchySeq.tendsto_limUnder`：CauchySeq.tendsto_limUnder [Preorder β] [Com
pleteSpace α] {u : β -> α} (h : CauchySeq u) : haveI
· 使用定理 `cauchySeq_of_le_geometric_two`：cauchySeq_of_le_geometric_two : CauchySeq
 f
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `CircleDeg1Lift.transnumAuxSeq_dist_lt`：transnumAuxSeq_dist_lt (n : Nat) 
: dist (f.transnumAuxSeq n) (f.transnumAuxSeq (n + 1)) < 1 / 2 / 2 ^ n
-/
theorem tendsto_translationNumber_aux : Tendsto f.transnumAuxSeq atTop (𝓝 <| τ f) :=
  (cauchySeq_of_le_geometric_two fun n => le_of_lt <| f.transnumAuxSeq_dist_lt n).tendsto_limUnder
/-
**CircleDeg1Lift.dist_map_zero_translationNumber_le** 是 Mathlib 中的一个定理，位于命名空间 `C
ircleDeg1Lift`。
形式化陈述：dist_map_zero_translationNumber_le : dist (f 0) (τ f) <= 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dist_le_of_le_geometric_two_of_tendsto₀`：dist_le_of_le_geometric_two_of_
tendsto₀ {a : α} (ha : Tendsto f atTop (𝓝 a)) : dist (f 0) a <= C
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `CircleDeg1Lift.transnumAuxSeq_dist_lt`：transnumAuxSeq_dist_lt (n : Nat) 
: dist (f.transnumAuxSeq n) (f.transnumAuxSeq (n + 1)) < 1 / 2 / 2 ^ n
· 使用定理 `CircleDeg1Lift.tendsto_translationNumber_aux`：tendsto_translationNumber_
aux : Tendsto f.transnumAuxSeq atTop (𝓝 <| τ f)
· 使用定理 `CircleDeg1Lift.transnumAuxSeq_zero`：transnumAuxSeq_zero : f.transnumAuxS
eq 0 = f 0
-/
theorem dist_map_zero_translationNumber_le : dist (f 0) (τ f) ≤ 1 :=
  f.transnumAuxSeq_zero ▸
    dist_le_of_le_geometric_two_of_tendsto₀ (fun n => le_of_lt <| f.transnumAuxSeq_dist_lt n)
      f.tendsto_translationNumber_aux
/-
**CircleDeg1Lift.tendsto_translationNumber_of_dist_bounded_aux** 是 Mathlib 中的一个定
理，位于命名空间 `CircleDeg1Lift`。
形式化陈述：tendsto_translationNumber_of_dist_bounded_aux (x : Nat -> Real) (C : Real)
 (H : forall n : Nat, dist ((f ^ n) 0) (x n) <= C) : Tendsto (fun n : Nat => x (
2 ^ n) / 2 ^ n) atTop (𝓝 <| τ f)
参数：x : Nat -> Real；C : Real；H : forall n : Nat, dist ((f ^ n) 0) (x n) <= C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.congr_dist`：Filter.Tendsto.congr_dist {f₁ f₂ : ι -> α} {p
 : Filter ι} {a : α} (h₁ : Tendsto f₁ p (𝓝 a)) (h : Tendsto (fun x => dist (f₁ x
) (f₂ x)) p (𝓝 …
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `CircleDeg1Lift.tendsto_translationNumber_aux`：tendsto_translationNumber_
aux : Tendsto f.transnumAuxSeq atTop (𝓝 <| τ f)
· 使用引理 `squeeze_zero`：squeeze_zero {α} {f g : α -> Real} {t₀ : Filter α} (hf : f
orall t, 0 <= f t) (hft : forall t, f t <= g t) (g0 : Tendsto g t₀ (𝓝 0)) : Tend
st…
· 使用定理 `dist_nonneg`：dist_nonneg {x y : α} : 0 <= dist x y
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `zero_lt_two`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : Part
ialOrder α] [ZeroLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 2
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CircleDeg1Lift.transnumAuxSeq.eq_1`：∀ (f : CircleDeg1Lift) (n : ℕ), f.tr
ansnumAuxSeq n = (f ^ 2 ^ n) 0 / 2 ^ n
· 使用定理 `Real.dist_eq`：Real.dist_eq (x y : Real) : dist x y = |x - y|
· 使用定理 `sub_div`：sub_div (a b c : K) : (a - b) / c = a / c - b / c
· 使用定理 `abs_div`：abs_div (a b : α) : |a / b| = |a| / |b|
· 使用定理 `abs_of_pos`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] {a
 : α} [AddLeftMono α], 0 < a → |a| = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `div_le_div_iff_of_pos_right`：div_le_div_iff_of_pos_right (hc : 0 < c) : 
a / c <= b / c ↔ a <= b
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `Filter.Tendsto.mul`：Filter.Tendsto.mul {α : Type*} {f g : α -> M} {x : F
ilter α} {a b : M} (hf : Tendsto f x (𝓝 a)) (hg : Tendsto g x (𝓝 b)) : Tendsto (
fun x =>…
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
（共 39 条，此处仅展示前 30 条）
-/
theorem tendsto_translationNumber_of_dist_bounded_aux (x : ℕ → ℝ) (C : ℝ)
    (H : ∀ n : ℕ, dist ((f ^ n) 0) (x n) ≤ C) :
    Tendsto (fun n : ℕ => x (2 ^ n) / 2 ^ n) atTop (𝓝 <| τ f) := by
  apply f.tendsto_translationNumber_aux.congr_dist (squeeze_zero (fun _ => dist_nonneg) _ _)
  · exact fun n => C / 2 ^ n
  · intro n
    have : 0 < (2 ^ n : ℝ) := pow_pos zero_lt_two _
    convert! (div_le_div_iff_of_pos_right this).2 (H (2 ^ n)) using 1
    rw [transnumAuxSeq, Real.dist_eq, ← sub_div, abs_div, abs_of_pos this, Real.dist_eq]
  · exact mul_zero C ▸ tendsto_const_nhds.mul <| tendsto_inv_atTop_zero.comp <|
      tendsto_pow_atTop_atTop_of_one_lt one_lt_two
/-
**CircleDeg1Lift.translationNumber_eq_of_dist_bounded** 是 Mathlib 中的一个定理，位于命名空间 
`CircleDeg1Lift`。
形式化陈述：translationNumber_eq_of_dist_bounded {f g : CircleDeg1Lift} (C : Real) (H 
: forall n : Nat, dist ((f ^ n) 0) ((g ^ n) 0) <= C) : τ f = τ g
参数：C : Real；H : forall n : Nat, dist ((f ^ n) 0) ((g ^ n) 0) <= C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CircleDeg1Lift.translationNumber_eq_of_tendsto_aux`：translationNumber_eq
_of_tendsto_aux {τ' : Real} (h : Tendsto f.transnumAuxSeq atTop (𝓝 τ')) : τ f = 
τ'
· 使用定理 `CircleDeg1Lift.tendsto_translationNumber_of_dist_bounded_aux`：tendsto_tr
anslationNumber_of_dist_bounded_aux (x : Nat -> Real) (C : Real) (H : forall n :
 Nat, dist ((f ^ n) 0) (x n) <= C) : Tendsto (fun …
-/
theorem translationNumber_eq_of_dist_bounded {f g : CircleDeg1Lift} (C : ℝ)
    (H : ∀ n : ℕ, dist ((f ^ n) 0) ((g ^ n) 0) ≤ C) : τ f = τ g :=
  Eq.symm <| g.translationNumber_eq_of_tendsto_aux <|
    f.tendsto_translationNumber_of_dist_bounded_aux (fun n ↦ (g ^ n) 0) C H

@[simp]
/-
**CircleDeg1Lift.translationNumber_one** 是 Mathlib 中的一个定理，位于命名空间 `CircleDeg1Lift
`。
形式化陈述：translationNumber_one : τ 1 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CircleDeg1Lift.translationNumber_eq_of_tendsto₀`：translationNumber_eq_of
_tendsto₀ {τ' : Real} (h : Tendsto (fun n : Nat => f^[n] 0 / n) atTop (𝓝 τ')) : 
τ f = τ'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Function.iterate_id`：iterate_id (n : Nat) : (id : α -> α)^[n] = id
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `OrderTopology.t5Space`：∀ {X : Type u_1} [inst : LinearOrder X] [inst_1 :
 TopologicalSpace X] [OrderTopology X], T5Space X
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem translationNumber_one : τ 1 = 0 :=
  translationNumber_eq_of_tendsto₀ _ <| by simp
/-
**CircleDeg1Lift.translationNumber_eq_of_semiconjBy** 是 Mathlib 中的一个定理，位于命名空间 `C
ircleDeg1Lift`。
形式化陈述：translationNumber_eq_of_semiconjBy {f g₁ g₂ : CircleDeg1Lift} (H : Semicon
jBy f g₁ g₂) : τ g₁ = τ g₂
参数：H : SemiconjBy f g₁ g₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CircleDeg1Lift.translationNumber_eq_of_dist_bounded`：translationNumber_e
q_of_dist_bounded {f g : CircleDeg1Lift} (C : Real) (H : forall n : Nat, dist ((
f ^ n) 0) ((g ^ n) 0) <= C) : τ f = τ g
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `CircleDeg1Lift.dist_map_zero_lt_of_semiconjBy`：dist_map_zero_lt_of_semic
onjBy {f g₁ g₂ : CircleDeg1Lift} (h : SemiconjBy f g₁ g₂) : dist (g₁ 0) (g₂ 0) <
 2
· 使用定理 `SemiconjBy.pow_right`：pow_right {a x y : M} (h : SemiconjBy a x y) (n : 
Nat) : SemiconjBy a (x ^ n) (y ^ n)
-/
theorem translationNumber_eq_of_semiconjBy {f g₁ g₂ : CircleDeg1Lift} (H : SemiconjBy f g₁ g₂) :
    τ g₁ = τ g₂ :=
  translationNumber_eq_of_dist_bounded 2 fun n =>
    le_of_lt <| dist_map_zero_lt_of_semiconjBy <| H.pow_right n
/-
**CircleDeg1Lift.translationNumber_eq_of_semiconj** 是 Mathlib 中的一个定理，位于命名空间 `Cir
cleDeg1Lift`。
形式化陈述：translationNumber_eq_of_semiconj {f g₁ g₂ : CircleDeg1Lift} (H : Function.
Semiconj f g₁ g₂) : τ g₁ = τ g₂
参数：H : Function.Semiconj f g₁ g₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CircleDeg1Lift.translationNumber_eq_of_semiconjBy`：translationNumber_eq_
of_semiconjBy {f g₁ g₂ : CircleDeg1Lift} (H : SemiconjBy f g₁ g₂) : τ g₁ = τ g₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CircleDeg1Lift.semiconjBy_iff_semiconj`：semiconjBy_iff_semiconj {f g₁ g₂
 : CircleDeg1Lift} : SemiconjBy f g₁ g₂ ↔ Semiconj f g₁ g₂
-/
theorem translationNumber_eq_of_semiconj {f g₁ g₂ : CircleDeg1Lift}
    (H : Function.Semiconj f g₁ g₂) : τ g₁ = τ g₂ :=
  translationNumber_eq_of_semiconjBy <| semiconjBy_iff_semiconj.2 H
/-
**CircleDeg1Lift.translationNumber_mul_of_commute** 是 Mathlib 中的一个定理，位于命名空间 `Cir
cleDeg1Lift`。
形式化陈述：translationNumber_mul_of_commute {f g : CircleDeg1Lift} (h : Commute f g) 
: τ (f * g) = τ f + τ g
参数：h : Commute f g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_nhds_unique`：tendsto_nhds_unique [T2Space X] {f : Y -> X} {l : F
ilter Y} {a b : X} [NeBot l] (ha : Tendsto f l (𝓝 a)) (hb : Tendsto f l (𝓝 b)) :
 a = b
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CircleDeg1Lift.tendsto_translationNumber_of_dist_bounded_aux`：tendsto_tr
anslationNumber_of_dist_bounded_aux (x : Nat -> Real) (C : Real) (H : forall n :
 Nat, dist ((f ^ n) 0) (x n) <= C) : Tendsto (fun …
· 使用定理 `Commute.mul_pow`：∀ {M : Type u_2} [inst : Monoid M] {a b : M}, Commute a
 b → ∀ (n : ℕ), (a * b) ^ n = a ^ n * b ^ n
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `CircleDeg1Lift.dist_map_map_zero_lt`：dist_map_map_zero_lt : dist (f 0 + 
g 0) (f (g 0)) < 1
· 使用定理 `Filter.Tendsto.add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst_1
 : Add M] [ContinuousAdd M] {α : Type u_2} {f g : α → M}   {x : Filter α} {a b :
 M},   F…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `CircleDeg1Lift.tendsto_translationNumber_aux`：tendsto_translationNumber_
aux : Tendsto f.transnumAuxSeq atTop (𝓝 <| τ f)
-/
theorem translationNumber_mul_of_commute {f g : CircleDeg1Lift} (h : Commute f g) :
    τ (f * g) = τ f + τ g := by
  refine tendsto_nhds_unique ?_
    (f.tendsto_translationNumber_aux.add g.tendsto_translationNumber_aux)
  simp only [transnumAuxSeq, ← add_div]
  refine (f * g).tendsto_translationNumber_of_dist_bounded_aux
    (fun n ↦ (f ^ n) 0 + (g ^ n) 0) 1 fun n ↦ ?_
  rw [h.mul_pow, dist_comm]
  exact le_of_lt ((f ^ n).dist_map_map_zero_lt (g ^ n))

@[simp]
/-
**CircleDeg1Lift.translationNumber_units_inv** 是 Mathlib 中的一个定理，位于命名空间 `CircleDe
g1Lift`。
形式化陈述：translationNumber_units_inv (f : CircleDeg1Liftˣ) : τ ↑f⁻¹ = -τ f
参数：f : CircleDeg1Liftˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_neg_iff_add_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, 
a = -b ↔ a + b = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CircleDeg1Lift.translationNumber_mul_of_commute`：translationNumber_mul_o
f_commute {f g : CircleDeg1Lift} (h : Commute f g) : τ (f * g) = τ f + τ g
· 使用定理 `Commute.units_inv_left`：units_inv_left : Commute (↑u) a -> Commute (↑u⁻¹
) a
· 使用定理 `Commute.refl`：∀ {S : Type u_3} [inst : Mul S] (a : S), Commute a a
· 使用定理 `Units.inv_mul`：inv_mul : (↑a⁻¹ * a : α) = 1
· 使用定理 `CircleDeg1Lift.translationNumber_one`：translationNumber_one : τ 1 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem translationNumber_units_inv (f : CircleDeg1Liftˣ) : τ ↑f⁻¹ = -τ f :=
  eq_neg_iff_add_eq_zero.2 <| by
    simp [← translationNumber_mul_of_commute (Commute.refl _).units_inv_left]

@[simp]
/-
**CircleDeg1Lift.translationNumber_pow** 是 Mathlib 中的一个定理，位于命名空间 `CircleDeg1Lift
`。
形式化陈述：∀ (f : CircleDeg1Lift) (n : ℕ), (f ^ n).translationNumber = ↑n * f.transla
tionNumber
参数：f : CircleDeg1Lift；n : ℕ；f ^ n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem translationNumber_pow : ∀ n : ℕ, τ (f ^ n) = n * τ f
  | 0 => by simp
  | n + 1 => by
    rw [pow_succ, translationNumber_mul_of_commute (Commute.pow_self f n),
      translationNumber_pow n, Nat.cast_add_one, add_mul, one_mul]

@[simp]
/-
**CircleDeg1Lift.translationNumber_zpow** 是 Mathlib 中的一个定理，位于命名空间 `CircleDeg1Lif
t`。
形式化陈述：∀ (f : CircleDeg1Liftˣ) (n : ℤ), (↑(f ^ n)).translationNumber = ↑n * (↑f).
translationNumber
参数：f : CircleDeg1Liftˣ；n : ℤ；↑(f ^ n)；↑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `CircleDeg1Lift.translationNumber_pow`：∀ (f : CircleDeg1Lift) (n : ℕ), (f
 ^ n).translationNumber = ↑n * f.translationNumber
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `zpow_negSucc`：zpow_negSucc (a : G) (n : Nat) : a ^ (Int.negSucc n) = (a 
^ (n + 1))⁻¹
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `CircleDeg1Lift.translationNumber_units_inv`：translationNumber_units_inv 
(f : CircleDeg1Liftˣ) : τ ↑f⁻¹ = -τ f
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `Int.cast_negSucc`：cast_negSucc (n : Nat) : (-[n+1] : R) = -(n + 1 : Nat)
· 使用定理 `neg_add_rev`：∀ {G : Type u_1} [inst : SubtractionMonoid G] (a b : G), -(
a + b) = -b + -a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
（共 45 条，此处仅展示前 30 条）
-/
theorem translationNumber_zpow (f : CircleDeg1Liftˣ) : ∀ n : ℤ, τ (f ^ n : Units _) = n * τ f
  | (n : ℕ) => by simp [translationNumber_pow f n]
  | -[n+1] => by simp; ring

@[simp]
/-
**CircleDeg1Lift.translationNumber_conj_eq** 是 Mathlib 中的一个定理，位于命名空间 `CircleDeg1
Lift`。
形式化陈述：translationNumber_conj_eq (f : CircleDeg1Liftˣ) (g : CircleDeg1Lift) : τ (
↑f * g * ↑f⁻¹) = τ g
参数：f : CircleDeg1Liftˣ；g : CircleDeg1Lift。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CircleDeg1Lift.translationNumber_eq_of_semiconjBy`：translationNumber_eq_
of_semiconjBy {f g₁ g₂ : CircleDeg1Lift} (H : SemiconjBy f g₁ g₂) : τ g₁ = τ g₂
· 使用引理 `Units.mk_semiconjBy`：mk_semiconjBy (u : Mˣ) (x : M) : SemiconjBy (↑u) x 
(u * x * ↑u⁻¹)
-/
theorem translationNumber_conj_eq (f : CircleDeg1Liftˣ) (g : CircleDeg1Lift) :
    τ (↑f * g * ↑f⁻¹) = τ g :=
  (translationNumber_eq_of_semiconjBy (f.mk_semiconjBy g)).symm

@[simp]
/-
**CircleDeg1Lift.translationNumber_conj_eq'** 是 Mathlib 中的一个定理，位于命名空间 `CircleDeg
1Lift`。
形式化陈述：translationNumber_conj_eq' (f : CircleDeg1Liftˣ) (g : CircleDeg1Lift) : τ 
(↑f⁻¹ * g * f) = τ g
参数：f : CircleDeg1Liftˣ；g : CircleDeg1Lift。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CircleDeg1Lift.translationNumber_conj_eq`：translationNumber_conj_eq (f :
 CircleDeg1Liftˣ) (g : CircleDeg1Lift) : τ (↑f * g * ↑f⁻¹) = τ g
-/
theorem translationNumber_conj_eq' (f : CircleDeg1Liftˣ) (g : CircleDeg1Lift) :
    τ (↑f⁻¹ * g * f) = τ g :=
  translationNumber_conj_eq f⁻¹ g
/-
**CircleDeg1Lift.dist_pow_map_zero_mul_translationNumber_le** 是 Mathlib 中的一个定理，位
于命名空间 `CircleDeg1Lift`。
形式化陈述：dist_pow_map_zero_mul_translationNumber_le (n : Nat) : dist ((f ^ n) 0) (n
 * f.translationNumber) <= 1
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CircleDeg1Lift.dist_map_zero_translationNumber_le`：dist_map_zero_transla
tionNumber_le : dist (f 0) (τ f) <= 1
· 使用定理 `CircleDeg1Lift.translationNumber_pow`：∀ (f : CircleDeg1Lift) (n : ℕ), (f
 ^ n).translationNumber = ↑n * f.translationNumber
-/
theorem dist_pow_map_zero_mul_translationNumber_le (n : ℕ) :
    dist ((f ^ n) 0) (n * f.translationNumber) ≤ 1 :=
  f.translationNumber_pow n ▸ (f ^ n).dist_map_zero_translationNumber_le
/-
**CircleDeg1Lift.tendsto_translation_number** 是 Mathlib 中的一个定理，位于命名空间 `CircleDeg
1Lift`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem tendsto_translation_number₀' :
    Tendsto (fun n : ℕ => (f ^ (n + 1) : CircleDeg1Lift) 0 / ((n : ℝ) + 1)) atTop (𝓝 <| τ f) := by
  refine
    tendsto_iff_dist_tendsto_zero.2 <|
      squeeze_zero (fun _ => dist_nonneg) (fun n => ?_)
        ((tendsto_const_div_atTop_nhds_zero_nat 1).comp (tendsto_add_atTop_nat 1))
  dsimp
  have : (0 : ℝ) < n + 1 := n.cast_add_one_pos
  rw [Real.dist_eq, div_sub' (ne_of_gt this), abs_div, ← Real.dist_eq, abs_of_pos this,
    Nat.cast_add_one, div_le_div_iff_of_pos_right this, ← Nat.cast_add_one]
  apply dist_pow_map_zero_mul_translationNumber_le
/-
**CircleDeg1Lift.tendsto_translation_number** 是 Mathlib 中的一个定理，位于命名空间 `CircleDeg
1Lift`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem tendsto_translation_number₀ : Tendsto (fun n : ℕ => (f ^ n) 0 / n) atTop (𝓝 <| τ f) :=
  (tendsto_add_atTop_iff_nat 1).1 (mod_cast f.tendsto_translation_number₀')

/-- For any `x : ℝ` the sequence $\frac{f^n(x)-x}{n}$ tends to the translation number of `f`.
In particular, this limit does not depend on `x`. -/
/-
**CircleDeg1Lift.tendsto_translationNumber** 是 Mathlib 中的一个定理，位于命名空间 `CircleDeg1
Lift`。
形式化陈述：tendsto_translationNumber (x : Real) : Tendsto (fun n : Nat => ((f ^ n) x 
- x) / n) atTop (𝓝 <| τ f)
参数：x : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CircleDeg1Lift.translationNumber_conj_eq'`：translationNumber_conj_eq' (f
 : CircleDeg1Liftˣ) (g : CircleDeg1Lift) : τ (↑f⁻¹ * g * f) = τ g
· 使用定理 `Filter.Tendsto.congr`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {l
₁ : Filter α} {l₂ : Filter β},   (∀ (x : α), f₁ x = f₂ x) → Filter.Tendsto f₁ l₁
 l₂ → Filt…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Units.conj_pow'`：conj_pow' (u : Mˣ) (x : M) (n : Nat) : ((↑u⁻¹ : M) * x 
* (u : M)) ^ n = (↑u⁻¹ : M) * x ^ n * (u : M)
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `sub_eq_neg_add`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b :
 α), a - b = -b + a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CircleDeg1Lift.tendsto_translation_number₀`：tendsto_translation_number₀ 
: Tendsto (fun n : Nat => (f ^ n) 0 / n) atTop (𝓝 <| τ f)

--- 原说明 ---
For any `x : ℝ` the sequence $\frac{f^n(x)-x}{n}$ tends to the translation numbe
r of `f`.
In particular, this limit does not depend on `x`.
-/
theorem tendsto_translationNumber (x : ℝ) :
    Tendsto (fun n : ℕ => ((f ^ n) x - x) / n) atTop (𝓝 <| τ f) := by
  rw [← translationNumber_conj_eq' (translate <| Multiplicative.ofAdd x)]
  refine (tendsto_translation_number₀ _).congr fun n ↦ ?_
  simp [sub_eq_neg_add, Units.conj_pow']
/-
**CircleDeg1Lift.tendsto_translation_number'** 是 Mathlib 中的一个定理，位于命名空间 `CircleDe
g1Lift`。
形式化陈述：tendsto_translation_number' (x : Real) : Tendsto (fun n : Nat => ((f ^ (n 
+ 1) : CircleDeg1Lift) x - x) / (n + 1)) atTop (𝓝 <| τ f)
参数：x : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.tendsto_add_atTop_iff_nat`：tendsto_add_atTop_iff_nat {f : Nat -> 
α} {l : Filter α} (k : Nat) : Tendsto (fun n => f (n + k)) atTop l ↔ Tendsto f a
tTop l
· 使用定理 `CircleDeg1Lift.tendsto_translationNumber`：tendsto_translationNumber (x :
 Real) : Tendsto (fun n : Nat => ((f ^ n) x - x) / n) atTop (𝓝 <| τ f)
-/
theorem tendsto_translation_number' (x : ℝ) :
    Tendsto (fun n : ℕ => ((f ^ (n + 1) : CircleDeg1Lift) x - x) / (n + 1)) atTop (𝓝 <| τ f) :=
  mod_cast (tendsto_add_atTop_iff_nat 1).2 (f.tendsto_translationNumber x)
/-
**CircleDeg1Lift.translationNumber_mono** 是 Mathlib 中的一个定理，位于命名空间 `CircleDeg1Lif
t`。
形式化陈述：translationNumber_mono : Monotone τ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_tendsto_of_tendsto'`：le_of_tendsto_of_tendsto' {f g : β -> α} {b :
 Filter β} {a₁ a₂ : α} [hb : NeBot b] (hf : Tendsto f b (𝓝 a₁)) (hg : Tendsto g 
b (𝓝 a₂)) (h : …
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `CircleDeg1Lift.tendsto_translation_number₀`：tendsto_translation_number₀ 
: Tendsto (fun n : Nat => (f ^ n) 0 / n) atTop (𝓝 <| τ f)
· 使用引理 `div_le_div_of_nonneg_right`：div_le_div_of_nonneg_right (hab : a <= b) (h
c : 0 <= c) : a / c <= b / c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `CircleDeg1Lift.pow_mono`：pow_mono {f g : CircleDeg1Lift} (h : f <= g) (n
 : Nat) : f ^ n <= g ^ n
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem translationNumber_mono : Monotone τ := fun f g h =>
  le_of_tendsto_of_tendsto' f.tendsto_translation_number₀ g.tendsto_translation_number₀ fun n => by
    gcongr; exact pow_mono h _ _
/-
**CircleDeg1Lift.translationNumber_translate** 是 Mathlib 中的一个定理，位于命名空间 `CircleDe
g1Lift`。
形式化陈述：translationNumber_translate (x : Real) : τ (translate <| Multiplicative.of
Add x) = x
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CircleDeg1Lift.translationNumber_eq_of_tendsto₀'`：translationNumber_eq_o
f_tendsto₀' {τ' : Real} (h : Tendsto (fun n : Nat => f^[n + 1] 0 / (n + 1)) atTo
p (𝓝 τ')) : τ f = τ'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CircleDeg1Lift.translate_iterate`：translate_iterate (x : Real) (n : Nat)
 : (translate (Multiplicative.ofAdd x))^[n] = translate (Multiplicative.ofAdd <|
 ↑n * x)
· 使用定理 `Nat.cast_succ`：cast_succ (n : Nat) : ((succ n : Nat) : R) = n + 1
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `mul_div_cancel_left₀`：∀ {M₀ : Type u_1} [inst : CommMonoidWithZero M₀] [
inst_1 : Div M₀] [MulDivCancelClass M₀] (b : M₀) {a : M₀},   a ≠ 0 → a * b / a =
 b
· 使用定理 `GroupWithZero.toMulDivCancelClass`：∀ {G₀ : Type u} [inst : GroupWithZero
 G₀], MulDivCancelClass G₀
· 使用定理 `Nat.cast_add_one_ne_zero`：cast_add_one_ne_zero (n : Nat) : (n + 1 : R) !
= 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
theorem translationNumber_translate (x : ℝ) : τ (translate <| Multiplicative.ofAdd x) = x :=
  translationNumber_eq_of_tendsto₀' _ <| by
    simp only [translate_iterate, translate_apply, add_zero, Nat.cast_succ,
      mul_div_cancel_left₀ (M₀ := ℝ) _ (Nat.cast_add_one_ne_zero _), tendsto_const_nhds]
/-
**CircleDeg1Lift.translationNumber_le_of_le_add** 是 Mathlib 中的一个定理，位于命名空间 `Circl
eDeg1Lift`。
形式化陈述：translationNumber_le_of_le_add {z : Real} (hz : forall x, f x <= x + z) : 
τ f <= z
参数：hz : forall x, f x <= x + z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CircleDeg1Lift.translationNumber_mono`：translationNumber_mono : Monotone
 τ
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `CircleDeg1Lift.translationNumber_translate`：translationNumber_translate 
(x : Real) : τ (translate <| Multiplicative.ofAdd x) = x
-/
theorem translationNumber_le_of_le_add {z : ℝ} (hz : ∀ x, f x ≤ x + z) : τ f ≤ z :=
  translationNumber_translate z ▸ translationNumber_mono fun x => (hz x).trans_eq (add_comm _ _)
/-
**CircleDeg1Lift.le_translationNumber_of_add_le** 是 Mathlib 中的一个定理，位于命名空间 `Circl
eDeg1Lift`。
形式化陈述：le_translationNumber_of_add_le {z : Real} (hz : forall x, x + z <= f x) : 
z <= τ f
参数：hz : forall x, x + z <= f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CircleDeg1Lift.translationNumber_mono`：translationNumber_mono : Monotone
 τ
· 使用定理 `Eq.trans_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ c →
 a ≤ c
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `CircleDeg1Lift.translationNumber_translate`：translationNumber_translate 
(x : Real) : τ (translate <| Multiplicative.ofAdd x) = x
-/
theorem le_translationNumber_of_add_le {z : ℝ} (hz : ∀ x, x + z ≤ f x) : z ≤ τ f :=
  translationNumber_translate z ▸ translationNumber_mono fun x => (add_comm _ _).trans_le (hz x)
/-
**CircleDeg1Lift.translationNumber_le_of_le_add_int** 是 Mathlib 中的一个定理，位于命名空间 `C
ircleDeg1Lift`。
形式化陈述：translationNumber_le_of_le_add_int {x : Real} {m : Int} (h : f x <= x + m)
 : τ f <= m
参数：h : f x <= x + m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_tendsto'`：le_of_tendsto' {x : Filter β} [hx : NeBot x] (lim : Tend
sto f x (𝓝 a)) (h : forall c, f c <= b) : a <= b
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `CircleDeg1Lift.tendsto_translation_number'`：tendsto_translation_number' 
(x : Real) : Tendsto (fun n : Nat => ((f ^ (n + 1) : CircleDeg1Lift) x - x) / (n
 + 1)) atTop (𝓝 <| τ f)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `div_le_iff₀'`：div_le_iff₀' (hc : 0 < c) : b / c <= a ↔ b <= c * a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Nat.cast_add_one_pos`：cast_add_one_pos (n : Nat) : 0 < (n : α) + 1
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `sub_le_iff_le_add'`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : LE 
α] [AddLeftMono α] {a b c : α}, a - b ≤ c ↔ a ≤ b + c
· 使用定理 `CircleDeg1Lift.iterate_le_of_map_le_add_int`：iterate_le_of_map_le_add_in
t {x : Real} {m : Int} (h : f x <= x + m) (n : Nat) : f^[n] x <= x + n * m
· 使用定理 `Nat.cast_add_one`：cast_add_one (n : Nat) : ((n + 1 : Nat) : R) = n + 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CircleDeg1Lift.coe_pow`：∀ (f : CircleDeg1Lift) (n : ℕ), ⇑(f ^ n) = (⇑f)^
[n]
-/
theorem translationNumber_le_of_le_add_int {x : ℝ} {m : ℤ} (h : f x ≤ x + m) : τ f ≤ m :=
  le_of_tendsto' (f.tendsto_translation_number' x) fun n =>
    (div_le_iff₀' (n.cast_add_one_pos : (0 : ℝ) < _)).mpr <| sub_le_iff_le_add'.2 <|
      (coe_pow f (n + 1)).symm ▸ @Nat.cast_add_one ℝ _ n ▸ f.iterate_le_of_map_le_add_int h (n + 1)
/-
**CircleDeg1Lift.translationNumber_le_of_le_add_nat** 是 Mathlib 中的一个定理，位于命名空间 `C
ircleDeg1Lift`。
形式化陈述：translationNumber_le_of_le_add_nat {x : Real} {m : Nat} (h : f x <= x + m)
 : τ f <= m
参数：h : f x <= x + m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CircleDeg1Lift.translationNumber_le_of_le_add_int`：translationNumber_le_
of_le_add_int {x : Real} {m : Int} (h : f x <= x + m) : τ f <= m
-/
theorem translationNumber_le_of_le_add_nat {x : ℝ} {m : ℕ} (h : f x ≤ x + m) : τ f ≤ m :=
  @translationNumber_le_of_le_add_int f x m h
/-
**CircleDeg1Lift.le_translationNumber_of_add_int_le** 是 Mathlib 中的一个定理，位于命名空间 `C
ircleDeg1Lift`。
形式化陈述：le_translationNumber_of_add_int_le {x : Real} {m : Int} (h : x + m <= f x)
 : ↑m <= τ f
参数：h : x + m <= f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ge_of_tendsto'`：∀ {α : Type u} {β : Type v} [inst : TopologicalSpace α] 
[inst_1 : Preorder α] [ClosedIciTopology α] {f : β → α}   {a b : α} {x : Filter 
β} […
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `CircleDeg1Lift.tendsto_translation_number'`：tendsto_translation_number' 
(x : Real) : Tendsto (fun n : Nat => ((f ^ (n + 1) : CircleDeg1Lift) x - x) / (n
 + 1)) atTop (𝓝 <| τ f)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `le_div_iff₀`：le_div_iff₀ (hc : 0 < c) : a <= b / c ↔ a * c <= b
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `Nat.cast_add_one_pos`：cast_add_one_pos (n : Nat) : 0 < (n : α) + 1
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `le_sub_iff_add_le'`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : LE 
α] [AddLeftMono α] {a b c : α}, b ≤ c - a ↔ a + b ≤ c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CircleDeg1Lift.coe_pow`：∀ (f : CircleDeg1Lift) (n : ℕ), ⇑(f ^ n) = (⇑f)^
[n]
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `CircleDeg1Lift.le_iterate_of_add_int_le_map`：le_iterate_of_add_int_le_ma
p {x : Real} {m : Int} (h : x + m <= f x) (n : Nat) : x + n * m <= f^[n] x
-/
theorem le_translationNumber_of_add_int_le {x : ℝ} {m : ℤ} (h : x + m ≤ f x) : ↑m ≤ τ f :=
  ge_of_tendsto' (f.tendsto_translation_number' x) fun n =>
    (le_div_iff₀ (n.cast_add_one_pos : (0 : ℝ) < _)).mpr <| le_sub_iff_add_le'.2 <| by
      simp only [coe_pow, mul_comm (m : ℝ), ← Nat.cast_add_one, f.le_iterate_of_add_int_le_map h]
/-
**CircleDeg1Lift.le_translationNumber_of_add_nat_le** 是 Mathlib 中的一个定理，位于命名空间 `C
ircleDeg1Lift`。
形式化陈述：le_translationNumber_of_add_nat_le {x : Real} {m : Nat} (h : x + m <= f x)
 : ↑m <= τ f
参数：h : x + m <= f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CircleDeg1Lift.le_translationNumber_of_add_int_le`：le_translationNumber_
of_add_int_le {x : Real} {m : Int} (h : x + m <= f x) : ↑m <= τ f
-/
theorem le_translationNumber_of_add_nat_le {x : ℝ} {m : ℕ} (h : x + m ≤ f x) : ↑m ≤ τ f :=
  @le_translationNumber_of_add_int_le f x m h

/-- If `f x - x` is an integer number `m` for some point `x`, then `τ f = m`.
On the circle this means that a map with a fixed point has rotation number zero. -/
/-
**CircleDeg1Lift.translationNumber_of_eq_add_int** 是 Mathlib 中的一个定理，位于命名空间 `Circ
leDeg1Lift`。
形式化陈述：translationNumber_of_eq_add_int {x : Real} {m : Int} (h : f x = x + m) : τ
 f = m
参数：h : f x = x + m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `CircleDeg1Lift.translationNumber_le_of_le_add_int`：translationNumber_le_
of_le_add_int {x : Real} {m : Int} (h : f x <= x + m) : τ f <= m
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `CircleDeg1Lift.le_translationNumber_of_add_int_le`：le_translationNumber_
of_add_int_le {x : Real} {m : Int} (h : x + m <= f x) : ↑m <= τ f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If `f x - x` is an integer number `m` for some point `x`, then `τ f = m`.
On the circle this means that a map with a fixed point has rotation number zero.
-/
theorem translationNumber_of_eq_add_int {x : ℝ} {m : ℤ} (h : f x = x + m) : τ f = m :=
  le_antisymm (translationNumber_le_of_le_add_int f <| le_of_eq h)
    (le_translationNumber_of_add_int_le f <| le_of_eq h.symm)
/-
**CircleDeg1Lift.floor_sub_le_translationNumber** 是 Mathlib 中的一个定理，位于命名空间 `Circl
eDeg1Lift`。
形式化陈述：floor_sub_le_translationNumber (x : Real) : ↑⌊f x - x⌋ <= τ f
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CircleDeg1Lift.le_translationNumber_of_add_int_le`：le_translationNumber_
of_add_int_le {x : Real} {m : Int} (h : x + m <= f x) : ↑m <= τ f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `le_sub_iff_add_le'`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : LE 
α] [AddLeftMono α] {a b c : α}, b ≤ c - a ↔ a + b ≤ c
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Int.floor_le`：floor_le (a : α) : (⌊a⌋ : α) <= a
-/
theorem floor_sub_le_translationNumber (x : ℝ) : ↑⌊f x - x⌋ ≤ τ f :=
  le_translationNumber_of_add_int_le f <| le_sub_iff_add_le'.1 (floor_le <| f x - x)
/-
**CircleDeg1Lift.translationNumber_le_ceil_sub** 是 Mathlib 中的一个定理，位于命名空间 `Circle
Deg1Lift`。
形式化陈述：translationNumber_le_ceil_sub (x : Real) : τ f <= ⌈f x - x⌉
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CircleDeg1Lift.translationNumber_le_of_le_add_int`：translationNumber_le_
of_le_add_int {x : Real} {m : Int} (h : f x <= x + m) : τ f <= m
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `sub_le_iff_le_add'`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : LE 
α] [AddLeftMono α] {a b c : α}, a - b ≤ c ↔ a ≤ b + c
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Int.le_ceil`：le_ceil (a : α) : a <= ⌈a⌉
-/
theorem translationNumber_le_ceil_sub (x : ℝ) : τ f ≤ ⌈f x - x⌉ :=
  translationNumber_le_of_le_add_int f <| sub_le_iff_le_add'.1 (le_ceil <| f x - x)
/-
**CircleDeg1Lift.map_lt_of_translationNumber_lt_int** 是 Mathlib 中的一个定理，位于命名空间 `C
ircleDeg1Lift`。
形式化陈述：map_lt_of_translationNumber_lt_int {n : Int} (h : τ f < n) (x : Real) : f 
x < x + n
参数：h : τ f < n；x : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `CircleDeg1Lift.le_translationNumber_of_add_int_le`：le_translationNumber_
of_add_int_le {x : Real} {m : Int} (h : x + m <= f x) : ↑m <= τ f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem map_lt_of_translationNumber_lt_int {n : ℤ} (h : τ f < n) (x : ℝ) : f x < x + n :=
  not_le.1 <| mt f.le_translationNumber_of_add_int_le <| not_le.2 h
/-
**CircleDeg1Lift.map_lt_of_translationNumber_lt_nat** 是 Mathlib 中的一个定理，位于命名空间 `C
ircleDeg1Lift`。
形式化陈述：map_lt_of_translationNumber_lt_nat {n : Nat} (h : τ f < n) (x : Real) : f 
x < x + n
参数：h : τ f < n；x : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CircleDeg1Lift.map_lt_of_translationNumber_lt_int`：map_lt_of_translation
Number_lt_int {n : Int} (h : τ f < n) (x : Real) : f x < x + n
-/
theorem map_lt_of_translationNumber_lt_nat {n : ℕ} (h : τ f < n) (x : ℝ) : f x < x + n :=
  @map_lt_of_translationNumber_lt_int f n h x
/-
**CircleDeg1Lift.map_lt_add_floor_translationNumber_add_one** 是 Mathlib 中的一个定理，位
于命名空间 `CircleDeg1Lift`。
形式化陈述：map_lt_add_floor_translationNumber_add_one (x : Real) : f x < x + ⌊τ f⌋ + 
1
参数：x : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `CircleDeg1Lift.map_lt_of_translationNumber_lt_int`：map_lt_of_translation
Number_lt_int {n : Int} (h : τ f < n) (x : Real) : f x < x + n
· 使用定理 `Int.cast_add`：∀ {R : Type u} [inst : AddGroupWithOne R] (m n : ℤ), ↑(m +
 n) = ↑m + ↑n
· 使用定理 `Int.lt_floor_add_one`：lt_floor_add_one (a : R) : a < ⌊a⌋ + 1
-/
theorem map_lt_add_floor_translationNumber_add_one (x : ℝ) : f x < x + ⌊τ f⌋ + 1 := by
  rw [add_assoc]
  norm_cast
  refine map_lt_of_translationNumber_lt_int _ ?_ _
  push_cast
  exact lt_floor_add_one _
/-
**CircleDeg1Lift.map_lt_add_translationNumber_add_one** 是 Mathlib 中的一个定理，位于命名空间 
`CircleDeg1Lift`。
形式化陈述：map_lt_add_translationNumber_add_one (x : Real) : f x < x + τ f + 1
参数：x : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CircleDeg1Lift.map_lt_add_floor_translationNumber_add_one`：map_lt_add_fl
oor_translationNumber_add_one (x : Real) : f x < x + ⌊τ f⌋ + 1
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Int.floor_le`：floor_le (a : α) : (⌊a⌋ : α) <= a
-/
theorem map_lt_add_translationNumber_add_one (x : ℝ) : f x < x + τ f + 1 :=
  calc
    f x < x + ⌊τ f⌋ + 1 := f.map_lt_add_floor_translationNumber_add_one x
    _ ≤ x + τ f + 1 := by gcongr; apply floor_le
/-
**CircleDeg1Lift.lt_map_of_int_lt_translationNumber** 是 Mathlib 中的一个定理，位于命名空间 `C
ircleDeg1Lift`。
形式化陈述：lt_map_of_int_lt_translationNumber {n : Int} (h : ↑n < τ f) (x : Real) : x
 + n < f x
参数：h : ↑n < τ f；x : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `CircleDeg1Lift.translationNumber_le_of_le_add_int`：translationNumber_le_
of_le_add_int {x : Real} {m : Int} (h : f x <= x + m) : τ f <= m
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem lt_map_of_int_lt_translationNumber {n : ℤ} (h : ↑n < τ f) (x : ℝ) : x + n < f x :=
  not_le.1 <| mt f.translationNumber_le_of_le_add_int <| not_le.2 h
/-
**CircleDeg1Lift.lt_map_of_nat_lt_translationNumber** 是 Mathlib 中的一个定理，位于命名空间 `C
ircleDeg1Lift`。
形式化陈述：lt_map_of_nat_lt_translationNumber {n : Nat} (h : ↑n < τ f) (x : Real) : x
 + n < f x
参数：h : ↑n < τ f；x : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CircleDeg1Lift.lt_map_of_int_lt_translationNumber`：lt_map_of_int_lt_tran
slationNumber {n : Int} (h : ↑n < τ f) (x : Real) : x + n < f x
-/
theorem lt_map_of_nat_lt_translationNumber {n : ℕ} (h : ↑n < τ f) (x : ℝ) : x + n < f x :=
  @lt_map_of_int_lt_translationNumber f n h x

/-- If `f^n x - x`, `n > 0`, is an integer number `m` for some point `x`, then
`τ f = m / n`. On the circle this means that a map with a periodic orbit has
a rational rotation number. -/
/-
**CircleDeg1Lift.translationNumber_of_map_pow_eq_add_int** 是 Mathlib 中的一个定理，位于命名
空间 `CircleDeg1Lift`。
形式化陈述：translationNumber_of_map_pow_eq_add_int {x : Real} {n : Nat} {m : Int} (h 
: (f ^ n) x = x + m) (hn : 0 < n) : τ f = m / n
参数：h : (f ^ n) x = x + m；hn : 0 < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CircleDeg1Lift.translationNumber_of_eq_add_int`：translationNumber_of_eq_
add_int {x : Real} {m : Int} (h : f x = x + m) : τ f = m
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `eq_div_iff`：eq_div_iff (hb : b != 0) : c = a / b ↔ c * b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_ne_zero`：cast_ne_zero {n : Nat} : (n : R) != 0 ↔ n != 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `CircleDeg1Lift.translationNumber_pow`：∀ (f : CircleDeg1Lift) (n : ℕ), (f
 ^ n).translationNumber = ↑n * f.translationNumber

--- 原说明 ---
If `f^n x - x`, `n > 0`, is an integer number `m` for some point `x`, then
`τ f = m / n`. On the circle this means that a map with a periodic orbit has
a rational rotation number.
-/
theorem translationNumber_of_map_pow_eq_add_int {x : ℝ} {n : ℕ} {m : ℤ} (h : (f ^ n) x = x + m)
    (hn : 0 < n) : τ f = m / n := by
  have := (f ^ n).translationNumber_of_eq_add_int h
  rwa [translationNumber_pow, mul_comm, ← eq_div_iff] at this
  exact Nat.cast_ne_zero.2 (ne_of_gt hn)

/-- If a predicate depends only on `f x - x` and holds for all `0 ≤ x ≤ 1`,
then it holds for all `x`. -/
/-
**CircleDeg1Lift.forall_map_sub_of_Icc** 是 Mathlib 中的一个定理，位于命名空间 `CircleDeg1Lift
`。
形式化陈述：forall_map_sub_of_Icc (P : Real -> Prop) (h : forall x in Icc (0 : Real) 1
, P (f x - x)) (x : Real) : P (f x - x)
参数：P : Real -> Prop；h : forall x in Icc (0 : Real) 1, P (f x - x)；x : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.fract_nonneg`：fract_nonneg (a : R) : 0 <= fract a
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Int.fract_lt_one`：fract_lt_one (a : R) : fract a < 1
· 使用定理 `CircleDeg1Lift.map_fract_sub_fract_eq`：map_fract_sub_fract_eq (x : Real)
 : f (fract x) - fract x = f x - x

--- 原说明 ---
If a predicate depends only on `f x - x` and holds for all `0 ≤ x ≤ 1`,
then it holds for all `x`.
-/
theorem forall_map_sub_of_Icc (P : ℝ → Prop) (h : ∀ x ∈ Icc (0 : ℝ) 1, P (f x - x)) (x : ℝ) :
    P (f x - x) :=
  f.map_fract_sub_fract_eq x ▸ h _ ⟨fract_nonneg _, le_of_lt (fract_lt_one _)⟩
/-
**CircleDeg1Lift.translationNumber_lt_of_forall_lt_add** 是 Mathlib 中的一个定理，位于命名空间
 `CircleDeg1Lift`。
形式化陈述：translationNumber_lt_of_forall_lt_add (hf : Continuous f) {z : Real} (hz :
 forall x, f x < x + z) : τ f < z
参数：hf : Continuous f；hz : forall x, f x < x + z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.exists_isMaxOn`：IsCompact.exists_isMaxOn [ClosedIciTopology α]
 {s : Set β} (hs : IsCompact s) (ne_s : s.Nonempty) {f : β -> α} (hf : Continuou
sOn f s) : exi…
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `CompactIccSpace.isCompact_Icc`：∀ {α : Type u_1} {inst : TopologicalSpace
 α} {inst_1 : Preorder α} [self : CompactIccSpace α] {a b : α},   IsCompact (Set
.Icc a b)
· 使用定理 `ConditionallyCompleteLinearOrder.toCompactIccSpace`：∀ (α : Type u_2) [in
st : ConditionallyCompleteLinearOrder α] [inst_1 : TopologicalSpace α] [OrderTop
ology α],   CompactIccSpace α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.nonempty_Icc`：nonempty_Icc : (Icc a b).Nonempty ↔ a <= b
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `Continuous.sub`：∀ {G : Type u_1} {X : Type u_3} [inst : TopologicalSpace
 X] [inst_1 : TopologicalSpace G] [inst_2 : Sub G]   [ContinuousSub G] {f g : X 
→ G}…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `CircleDeg1Lift.translationNumber_le_of_le_add`：translationNumber_le_of_l
e_add {z : Real} (hz : forall x, f x <= x + z) : τ f <= z
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `CircleDeg1Lift.forall_map_sub_of_Icc`：forall_map_sub_of_Icc (P : Real ->
 Prop) (h : forall x in Icc (0 : Real) 1, P (f x - x)) (x : Real) : P (f x - x)
· 使用定理 `sub_lt_iff_lt_add'`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : LT 
α] [AddLeftStrictMono α] {a b c : α}, a - b < c ↔ a < b + c
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
-/
theorem translationNumber_lt_of_forall_lt_add (hf : Continuous f) {z : ℝ} (hz : ∀ x, f x < x + z) :
    τ f < z := by
  obtain ⟨x, -, hx⟩ : ∃ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, f y - y ≤ f x - x :=
    isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 zero_le_one)
      (hf.sub continuous_id).continuousOn
  refine lt_of_le_of_lt ?_ (sub_lt_iff_lt_add'.2 <| hz x)
  apply translationNumber_le_of_le_add
  simp only [← sub_le_iff_le_add']
  exact f.forall_map_sub_of_Icc (fun a => a ≤ f x - x) hx
/-
**CircleDeg1Lift.lt_translationNumber_of_forall_add_lt** 是 Mathlib 中的一个定理，位于命名空间
 `CircleDeg1Lift`。
形式化陈述：lt_translationNumber_of_forall_add_lt (hf : Continuous f) {z : Real} (hz :
 forall x, x + z < f x) : z < τ f
参数：hf : Continuous f；hz : forall x, x + z < f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.exists_isMinOn`：IsCompact.exists_isMinOn [ClosedIicTopology α]
 {s : Set β} (hs : IsCompact s) (ne_s : s.Nonempty) {f : β -> α} (hf : Continuou
sOn f s) : exi…
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `CompactIccSpace.isCompact_Icc`：∀ {α : Type u_1} {inst : TopologicalSpace
 α} {inst_1 : Preorder α} [self : CompactIccSpace α] {a b : α},   IsCompact (Set
.Icc a b)
· 使用定理 `ConditionallyCompleteLinearOrder.toCompactIccSpace`：∀ (α : Type u_2) [in
st : ConditionallyCompleteLinearOrder α] [inst_1 : TopologicalSpace α] [OrderTop
ology α],   CompactIccSpace α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.nonempty_Icc`：nonempty_Icc : (Icc a b).Nonempty ↔ a <= b
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `Continuous.sub`：∀ {G : Type u_1} {X : Type u_3} [inst : TopologicalSpace
 X] [inst_1 : TopologicalSpace G] [inst_2 : Sub G]   [ContinuousSub G] {f g : X 
→ G}…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `lt_sub_iff_add_lt'`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : LT 
α] [AddLeftStrictMono α] {a b c : α}, b < c - a ↔ a + b < c
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `CircleDeg1Lift.le_translationNumber_of_add_le`：le_translationNumber_of_a
dd_le {z : Real} (hz : forall x, x + z <= f x) : z <= τ f
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `CircleDeg1Lift.forall_map_sub_of_Icc`：forall_map_sub_of_Icc (P : Real ->
 Prop) (h : forall x in Icc (0 : Real) 1, P (f x - x)) (x : Real) : P (f x - x)
-/
theorem lt_translationNumber_of_forall_add_lt (hf : Continuous f) {z : ℝ} (hz : ∀ x, x + z < f x) :
    z < τ f := by
  obtain ⟨x, -, hx⟩ : ∃ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, f x - x ≤ f y - y :=
    isCompact_Icc.exists_isMinOn (nonempty_Icc.2 zero_le_one) (hf.sub continuous_id).continuousOn
  refine lt_of_lt_of_le (lt_sub_iff_add_lt'.2 <| hz x) ?_
  apply le_translationNumber_of_add_le
  simp only [← le_sub_iff_add_le']
  exact f.forall_map_sub_of_Icc _ hx

/-- If `f` is a continuous monotone map `ℝ → ℝ`, `f (x + 1) = f x + 1`, then there exists `x`
such that `f x = x + τ f`. -/
/-
**CircleDeg1Lift.exists_eq_add_translationNumber** 是 Mathlib 中的一个定理，位于命名空间 `Circ
leDeg1Lift`。
形式化陈述：exists_eq_add_translationNumber (hf : Continuous f) : exists x, f x = x + 
τ f
参数：hf : Continuous f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用定理 `CircleDeg1Lift.lt_translationNumber_of_forall_add_lt`：lt_translationNumb
er_of_forall_add_lt (hf : Continuous f) {z : Real} (hz : forall x, x + z < f x) 
: z < τ f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `CircleDeg1Lift.translationNumber_lt_of_forall_lt_add`：translationNumber_
lt_of_forall_lt_add (hf : Continuous f) {z : Real} (hz : forall x, f x < x + z) 
: τ f < z
· 使用定理 `intermediate_value_univ₂`：intermediate_value_univ₂ [PreconnectedSpace X]
 {a b : X} {f g : X -> α} (hf : Continuous f) (hg : Continuous g) (ha : f a <= g
 a) (hb : g b …
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `ordered_connected_space`：∀ {α : Type u} [inst : TopologicalSpace α] [ins
t_1 : ConditionallyCompleteLinearOrder α] [OrderTopology α]   [DenselyOrdered α]
, Preconnecte…
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Continuous.add_const`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst
_1 : Add M] [SeparatelyContinuousAdd M] {X : Type u_2}   [inst_3 : TopologicalSp
ace X] {f …
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)

--- 原说明 ---
If `f` is a continuous monotone map `ℝ → ℝ`, `f (x + 1) = f x + 1`, then there e
xists `x`
such that `f x = x + τ f`.
-/
theorem exists_eq_add_translationNumber (hf : Continuous f) : ∃ x, f x = x + τ f := by
  obtain ⟨a, ha⟩ : ∃ x, f x ≤ x + τ f := by
    by_contra! H
    exact lt_irrefl _ (f.lt_translationNumber_of_forall_add_lt hf H)
  obtain ⟨b, hb⟩ : ∃ x, x + τ f ≤ f x := by
    by_contra! H
    exact lt_irrefl _ (f.translationNumber_lt_of_forall_lt_add hf H)
  exact intermediate_value_univ₂ hf (by fun_prop) ha hb
/-
**CircleDeg1Lift.translationNumber_eq_int_iff** 是 Mathlib 中的一个定理，位于命名空间 `CircleD
eg1Lift`。
形式化陈述：translationNumber_eq_int_iff (hf : Continuous f) {m : Int} : τ f = m ↔ exi
sts x : Real, f x = x + m
参数：hf : Continuous f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CircleDeg1Lift.exists_eq_add_translationNumber`：exists_eq_add_translatio
nNumber (hf : Continuous f) : exists x, f x = x + τ f
· 使用定理 `CircleDeg1Lift.translationNumber_of_eq_add_int`：translationNumber_of_eq_
add_int {x : Real} {m : Int} (h : f x = x + m) : τ f = m
-/
theorem translationNumber_eq_int_iff (hf : Continuous f) {m : ℤ} :
    τ f = m ↔ ∃ x : ℝ, f x = x + m := by
  constructor
  · intro h
    simp only [← h]
    exact f.exists_eq_add_translationNumber hf
  · rintro ⟨x, hx⟩
    exact f.translationNumber_of_eq_add_int hx
/-
**CircleDeg1Lift.continuous_pow** 是 Mathlib 中的一个定理，位于命名空间 `CircleDeg1Lift`。
形式化陈述：continuous_pow (hf : Continuous f) (n : Nat) : Continuous (f ^ n : CircleD
eg1Lift)
参数：hf : Continuous f；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CircleDeg1Lift.coe_pow`：∀ (f : CircleDeg1Lift) (n : ℕ), ⇑(f ^ n) = (⇑f)^
[n]
· 使用定理 `Continuous.iterate`：Continuous.iterate {f : X -> X} (h : Continuous f) (
n : Nat) : Continuous f^[n]
-/
theorem continuous_pow (hf : Continuous f) (n : ℕ) : Continuous (f ^ n : CircleDeg1Lift) := by
  rw [coe_pow]
  exact hf.iterate n
/-
**CircleDeg1Lift.translationNumber_eq_rat_iff** 是 Mathlib 中的一个定理，位于命名空间 `CircleD
eg1Lift`。
形式化陈述：translationNumber_eq_rat_iff (hf : Continuous f) {m : Int} {n : Nat} (hn :
 0 < n) : τ f = m / n ↔ exists x, (f ^ n) x = x + m
参数：hf : Continuous f；hn : 0 < n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `eq_div_iff`：eq_div_iff (hb : b != 0) : c = a / b ↔ c * b = a
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_pos`：cast_pos {α} [Semiring α] [PartialOrder α] [IsOrderedRing 
α] [Nontrivial α] {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CircleDeg1Lift.translationNumber_pow`：∀ (f : CircleDeg1Lift) (n : ℕ), (f
 ^ n).translationNumber = ↑n * f.translationNumber
· 使用定理 `CircleDeg1Lift.translationNumber_eq_int_iff`：translationNumber_eq_int_if
f (hf : Continuous f) {m : Int} : τ f = m ↔ exists x : Real, f x = x + m
· 使用定理 `CircleDeg1Lift.continuous_pow`：continuous_pow (hf : Continuous f) (n : N
at) : Continuous (f ^ n : CircleDeg1Lift)
-/
theorem translationNumber_eq_rat_iff (hf : Continuous f) {m : ℤ} {n : ℕ} (hn : 0 < n) :
    τ f = m / n ↔ ∃ x, (f ^ n) x = x + m := by
  rw [eq_div_iff, mul_comm, ← translationNumber_pow] <;> [skip; exact ne_of_gt (Nat.cast_pos.2 hn)]
  exact (f ^ n).translationNumber_eq_int_iff (f.continuous_pow hf n)

/-- Consider two actions `f₁ f₂ : G →* CircleDeg1Lift` of a group on the real line by lifts of
orientation-preserving circle homeomorphisms. Suppose that for each `g : G` the homeomorphisms
`f₁ g` and `f₂ g` have equal rotation numbers. Then there exists `F : CircleDeg1Lift` such that
`F * f₁ g = f₂ g * F` for all `g : G`.

This is a version of Proposition 5.4 from [Étienne Ghys, Groupes d'homéomorphismes du cercle et
cohomologie bornée][ghys87:groupes]. -/
/-
**CircleDeg1Lift.semiconj_of_group_action_of_forall_translationNumber_eq** 是 Mat
hlib 中的一个定理，位于命名空间 `CircleDeg1Lift`。
形式化陈述：semiconj_of_group_action_of_forall_translationNumber_eq {G : Type*} [Group
 G] (f₁ f₂ : G ->* CircleDeg1Lift) (h : forall g, τ (f₁ g) = τ (f₂ g)) : exists 
F : CircleDeg1Lift, forall g, Semiconj F (f₁ g) (f₂ g)
参数：f₁ f₂ : G ->* CircleDeg1Lift；h : forall g, τ (f₁ g) = τ (f₂ g)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MonoidHom.coe_toHomUnits`：coe_toHomUnits (f : G ->* M) (g : G) : (f.toHo
mUnits g : M) = f g
· 使用定理 `map_inv`：map_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f 
: F) (a : G) : f a⁻¹ = (f a)⁻¹
· 使用定理 `CircleDeg1Lift.translationNumber_units_inv`：translationNumber_units_inv 
(f : CircleDeg1Liftˣ) : τ ↑f⁻¹ = -τ f
· 使用定理 `CircleDeg1Lift.mono`：∀ (f : CircleDeg1Lift) {x y : ℝ}, x ≤ y → f x ≤ f y
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `CircleDeg1Lift.map_lt_add_translationNumber_add_one`：map_lt_add_translat
ionNumber_add_one (x : Real) : f x < x + τ f + 1
· 使用定理 `CircleDeg1Lift.map_add_one`：map_add_one : forall x, f (x + 1) = f x + 1
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `add_neg_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a + -a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `one_add_one_eq_two`：one_add_one_eq_two [AddMonoidWithOne R] : 1 + 1 = (2
 : R)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `ciSup_mono`：ciSup_mono {f g : ι -> α} (B : BddAbove (range g)) (H : fora
ll x, f x <= g x) : iSup f <= iSup g
· 使用定理 `Monotone.map_ciSup_of_continuousAt`：Monotone.map_ciSup_of_continuousAt {
ι : Sort*} [Nonempty ι] {f : α -> β} {g : ι -> α} (Cf : ContinuousAt f (iSup g))
 (Mf : Monotone f) (bdd …
（共 43 条，此处仅展示前 30 条）

--- 原说明 ---
Consider two actions `f₁ f₂ : G →* CircleDeg1Lift` of a group on the real line b
y lifts of
orientation-preserving circle homeomorphisms. Suppose that for each `g : G` the 
homeomorphisms
`f₁ g` and `f₂ g` have equal rotation numbers. Then there exists `F : CircleDeg1
Lift` such that
`F * f₁ g = f₂ g * F` for all `g : G`.

This is a version of Proposition 5.4 from [Étienne Ghys, Groupes d'homéomorphism
es du cercle et
cohomologie bornée][ghys87:groupes].
-/
theorem semiconj_of_group_action_of_forall_translationNumber_eq {G : Type*} [Group G]
    (f₁ f₂ : G →* CircleDeg1Lift) (h : ∀ g, τ (f₁ g) = τ (f₂ g)) :
    ∃ F : CircleDeg1Lift, ∀ g, Semiconj F (f₁ g) (f₂ g) := by
  -- Equality of translation number guarantees that for each `x`
  -- the set `{f₂ g⁻¹ (f₁ g x) | g : G}` is bounded above.
  have : ∀ x, BddAbove (range fun g => f₂ g⁻¹ (f₁ g x)) := by
    refine fun x => ⟨x + 2, ?_⟩
    rintro _ ⟨g, rfl⟩
    have : τ (f₂ g⁻¹) = -τ (f₂ g) := by
      rw [← MonoidHom.coe_toHomUnits, map_inv, translationNumber_units_inv,
        MonoidHom.coe_toHomUnits]
    calc
      f₂ g⁻¹ (f₁ g x) ≤ f₂ g⁻¹ (x + τ (f₁ g) + 1) :=
        mono _ (map_lt_add_translationNumber_add_one _ _).le
      _ = f₂ g⁻¹ (x + τ (f₂ g)) + 1 := by rw [h, map_add_one]
      _ ≤ x + τ (f₂ g) + τ (f₂ g⁻¹) + 1 + 1 := by grw [map_lt_add_translationNumber_add_one]
      _ = x + 2 := by simp [this, add_assoc, one_add_one_eq_two]
  -- We have a theorem about actions by `OrderIso`, so we introduce auxiliary maps
  -- to `ℝ ≃o ℝ`.
  set F₁ := toOrderIso.comp f₁.toHomUnits
  set F₂ := toOrderIso.comp f₂.toHomUnits
  have hF₁ : ∀ g, ⇑(F₁ g) = f₁ g := fun _ => rfl
  have hF₂ : ∀ g, ⇑(F₂ g) = f₂ g := fun _ => rfl
  -- Now we apply `csSup_div_semiconj` and go back to `f₁` and `f₂`.
  refine ⟨⟨⟨fun x ↦ ⨆ g', (F₂ g')⁻¹ (F₁ g' x), fun x y hxy => ?_⟩, fun x => ?_⟩,
    csSup_div_semiconj F₂ F₁ fun x => ?_⟩ <;> simp only [hF₁, hF₂, ← map_inv]
  · exact ciSup_mono (this y) fun g => mono _ (mono _ hxy)
  · simp only [map_add_one]
    exact (Monotone.map_ciSup_of_continuousAt (by fun_prop)
      (monotone_id.add_const (1 : ℝ)) (this x)).symm
  · exact this x

/-- If two lifts of circle homeomorphisms have the same translation number, then they are
semiconjugate by a `CircleDeg1Lift`. This version uses arguments `f₁ f₂ : CircleDeg1Liftˣ`
to assume that `f₁` and `f₂` are homeomorphisms. -/
/-
**CircleDeg1Lift.units_semiconj_of_translationNumber_eq** 是 Mathlib 中的一个定理，位于命名空
间 `CircleDeg1Lift`。
形式化陈述：units_semiconj_of_translationNumber_eq {f₁ f₂ : CircleDeg1Liftˣ} (h : τ f₁
 = τ f₂) : exists F : CircleDeg1Lift, Semiconj F f₁ f₂
参数：h : τ f₁ = τ f₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CircleDeg1Lift.translationNumber_zpow`：∀ (f : CircleDeg1Liftˣ) (n : ℤ), 
(↑(f ^ n)).translationNumber = ↑n * (↑f).translationNumber
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用引理 `zpow_ofNat`：zpow_ofNat (a : G) (n : Nat) : a ^ (ofNat(n) : Int) = a ^ Of
Nat.ofNat n
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `CircleDeg1Lift.semiconj_of_group_action_of_forall_translationNumber_eq`：
semiconj_of_group_action_of_forall_translationNumber_eq {G : Type*} [Group G] (f
₁ f₂ : G ->* CircleDeg1Lift) (h : forall g, τ (f₁ g) = τ (f₂…

--- 原说明 ---
If two lifts of circle homeomorphisms have the same translation number, then the
y are
semiconjugate by a `CircleDeg1Lift`. This version uses arguments `f₁ f₂ : Circle
Deg1Liftˣ`
to assume that `f₁` and `f₂` are homeomorphisms.
-/
theorem units_semiconj_of_translationNumber_eq {f₁ f₂ : CircleDeg1Liftˣ} (h : τ f₁ = τ f₂) :
    ∃ F : CircleDeg1Lift, Semiconj F f₁ f₂ :=
  have : ∀ n : Multiplicative ℤ,
      τ ((Units.coeHom _).comp (zpowersHom _ f₁) n) =
        τ ((Units.coeHom _).comp (zpowersHom _ f₂) n) := fun n ↦ by
    simp [h]
  (semiconj_of_group_action_of_forall_translationNumber_eq _ _ this).imp fun F hF => by
    simpa using hF (Multiplicative.ofAdd 1)

/-- If two lifts of circle homeomorphisms have the same translation number, then they are
semiconjugate by a `CircleDeg1Lift`. This version uses assumptions `IsUnit f₁` and `IsUnit f₂`
to assume that `f₁` and `f₂` are homeomorphisms. -/
/-
**CircleDeg1Lift.semiconj_of_isUnit_of_translationNumber_eq** 是 Mathlib 中的一个定理，位
于命名空间 `CircleDeg1Lift`。
形式化陈述：semiconj_of_isUnit_of_translationNumber_eq {f₁ f₂ : CircleDeg1Lift} (h₁ : 
IsUnit f₁) (h₂ : IsUnit f₂) (h : τ f₁ = τ f₂) : exists F : CircleDeg1Lift, Semic
onj F f₁ f₂
参数：h₁ : IsUnit f₁；h₂ : IsUnit f₂；h : τ f₁ = τ f₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CircleDeg1Lift.units_semiconj_of_translationNumber_eq`：units_semiconj_of
_translationNumber_eq {f₁ f₂ : CircleDeg1Liftˣ} (h : τ f₁ = τ f₂) : exists F : C
ircleDeg1Lift, Semiconj F f₁ f₂

--- 原说明 ---
If two lifts of circle homeomorphisms have the same translation number, then the
y are
semiconjugate by a `CircleDeg1Lift`. This version uses assumptions `IsUnit f₁` a
nd `IsUnit f₂`
to assume that `f₁` and `f₂` are homeomorphisms.
-/
theorem semiconj_of_isUnit_of_translationNumber_eq {f₁ f₂ : CircleDeg1Lift} (h₁ : IsUnit f₁)
    (h₂ : IsUnit f₂) (h : τ f₁ = τ f₂) : ∃ F : CircleDeg1Lift, Semiconj F f₁ f₂ := by
  rcases h₁, h₂ with ⟨⟨f₁, rfl⟩, ⟨f₂, rfl⟩⟩
  exact units_semiconj_of_translationNumber_eq h

/-- If two lifts of circle homeomorphisms have the same translation number, then they are
semiconjugate by a `CircleDeg1Lift`. This version uses assumptions `bijective f₁` and
`bijective f₂` to assume that `f₁` and `f₂` are homeomorphisms. -/
/-
**CircleDeg1Lift.semiconj_of_bijective_of_translationNumber_eq** 是 Mathlib 中的一个定
理，位于命名空间 `CircleDeg1Lift`。
形式化陈述：semiconj_of_bijective_of_translationNumber_eq {f₁ f₂ : CircleDeg1Lift} (h₁
 : Bijective f₁) (h₂ : Bijective f₂) (h : τ f₁ = τ f₂) : exists F : CircleDeg1Li
ft, Semiconj F f₁ f₂
参数：h₁ : Bijective f₁；h₂ : Bijective f₂；h : τ f₁ = τ f₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CircleDeg1Lift.semiconj_of_isUnit_of_translationNumber_eq`：semiconj_of_i
sUnit_of_translationNumber_eq {f₁ f₂ : CircleDeg1Lift} (h₁ : IsUnit f₁) (h₂ : Is
Unit f₂) (h : τ f₁ = τ f₂) : exists F : CircleD…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CircleDeg1Lift.isUnit_iff_bijective`：isUnit_iff_bijective {f : CircleDeg
1Lift} : IsUnit f ↔ Bijective f

--- 原说明 ---
If two lifts of circle homeomorphisms have the same translation number, then the
y are
semiconjugate by a `CircleDeg1Lift`. This version uses assumptions `bijective f₁
` and
`bijective f₂` to assume that `f₁` and `f₂` are homeomorphisms.
-/
theorem semiconj_of_bijective_of_translationNumber_eq {f₁ f₂ : CircleDeg1Lift} (h₁ : Bijective f₁)
    (h₂ : Bijective f₂) (h : τ f₁ = τ f₂) : ∃ F : CircleDeg1Lift, Semiconj F f₁ f₂ :=
  semiconj_of_isUnit_of_translationNumber_eq (isUnit_iff_bijective.2 h₁) (isUnit_iff_bijective.2 h₂)
    h

end CircleDeg1Lift

