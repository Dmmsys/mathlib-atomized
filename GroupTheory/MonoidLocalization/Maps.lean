/-
Copyright (c) 2019 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
module

public import Mathlib.GroupTheory.MonoidLocalization.Basic

/-!
# Mapping properties of monoid localizations

Given an `S`-localization map `f : M →* N`, we can define `Submonoid.LocalizationMap.lift`, the
homomorphism from `N` induced by a homomorphism from `M` which maps elements of `S` to invertible
elements of the codomain. Similarly, given commutative monoids `P, Q`, a submonoid `T` of `P` and a
localization map for `T` from `P` to `Q`, then a homomorphism `g : M →* P` such that `g(S) ⊆ T`
induces a homomorphism of localizations, `LocalizationMap.map`, from `N` to `Q`.

## Tags

localization, monoid localization, quotient monoid, congruence relation, characteristic predicate,
commutative monoid, grothendieck group
-/

@[expose] public section

assert_not_exists MonoidWithZero Ring

open Function

section CommMonoid

variable {M : Type*} [CommMonoid M] (S : Submonoid M) (N : Type*) [CommMonoid N] {P : Type*}
  [CommMonoid P]

variable {S N}

namespace Submonoid

namespace LocalizationMap

variable (f : LocalizationMap S N)

variable {g : M →* P}

/-- Given a Localization map `f : M →* N` for a Submonoid `S ⊆ M` and a map of `CommMonoid`s
`g : M →* P` such that `g(S) ⊆ Units P`, `f x = f y → g x = g y` for all `x y : M`. -/
@[to_additive
/-- Given a Localization map `f : M →+ N` for an AddSubmonoid `S ⊆ M` and a map of
`AddCommMonoid`s `g : M →+ P` such that `g(S) ⊆ AddUnits P`, `f x = f y → g x = g y`
for all `x y : M`. -/]
/-
**Submonoid.LocalizationMap.eq_of_eq** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid.Locali
zationMap`。
形式化陈述：eq_of_eq (hg : forall y : S, IsUnit (g y)) {x y} (h : f x = f y) : g x = g
 y
参数：hg : forall y : S, IsUnit (g y)；h : f x = f y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submonoid.LocalizationMap.eq_iff_exists`：eq_iff_exists (f : Localization
Map S N) {x y} : f x = f y ↔ exists c : S, c * x = c * y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `IsUnit.liftRight_inv_mul`：liftRight_inv_mul (f : M ->* N) (h : forall x,
 IsUnit (f x)) (x) : ↑(IsUnit.liftRight f h x)⁻¹ * f x = 1
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `MonoidHom.map_mul`：∀ {M : Type u_4} {N : Type u_5} [inst : MulOne M] [in
st_1 : MulOne N] (f : M →* N) (a b : M), f (a * b) = f a * f b
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Submonoid.LocalizationMap.mul_inv_left`：mul_inv_left {f : M ->* N} (h : 
forall y : S, IsUnit (f y)) (y : S) (w z : N) : w * (IsUnit.liftRight (f.domRest
rict S) h y)⁻¹ = z ↔ w = f y…
-/
theorem eq_of_eq (hg : ∀ y : S, IsUnit (g y)) {x y} (h : f x = f y) : g x = g y := by
  obtain ⟨c, hc⟩ := f.eq_iff_exists.1 h
  rw [← one_mul (g x), ← IsUnit.liftRight_inv_mul (g.domRestrict S) hg c]
  change _ * g c * _ = _
  rw [mul_assoc, ← g.map_mul, hc, mul_comm, mul_inv_left hg, g.map_mul]

/-- Given `CommMonoid`s `M, P`, Localization maps `f : M →* N, k : P →* Q` for Submonoids
`S, T` respectively, and `g : M →* P` such that `g(S) ⊆ T`, `f x = f y` implies
`k (g x) = k (g y)`. -/
@[to_additive
/-- Given `AddCommMonoid`s `M, P`, Localization maps `f : M →+ N, k : P →+ Q` for AddSubmonoids
`S, T` respectively, and `g : M →+ P` such that `g(S) ⊆ T`, `f x = f y`
implies `k (g x) = k (g y)`. -/]
/-
**Submonoid.LocalizationMap.comp_eq_of_eq** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid.L
ocalizationMap`。
形式化陈述：comp_eq_of_eq {T : Submonoid P} {Q : Type*} [CommMonoid Q] (hg : forall y 
: S, g y in T) (k : LocalizationMap T Q) {x y} (h : f x = f y) : k (g x) = k (g 
y)
参数：hg : forall y : S, g y in T；k : LocalizationMap T Q；h : f x = f y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.LocalizationMap.eq_of_eq`：eq_of_eq (hg : forall y : S, IsUnit 
(g y)) {x y} (h : f x = f y) : g x = g y
· 使用定理 `Submonoid.LocalizationMap.map_units`：map_units (f : LocalizationMap S N)
 (y : S) : IsUnit (f y)
-/
theorem comp_eq_of_eq {T : Submonoid P} {Q : Type*} [CommMonoid Q] (hg : ∀ y : S, g y ∈ T)
    (k : LocalizationMap T Q) {x y} (h : f x = f y) : k (g x) = k (g y) :=
  f.eq_of_eq (fun y : S ↦ show IsUnit (k.toMonoidHom.comp g y) from k.map_units ⟨g y, hg y⟩) h

variable (hg : ∀ y : S, IsUnit (g y))

/-- Given a Localization map `f : M →* N` for a Submonoid `S ⊆ M` and a map of `CommMonoid`s
`g : M →* P` such that `g y` is invertible for all `y : S`, the homomorphism induced from
`N` to `P` sending `z : N` to `g x * (g y)⁻¹`, where `(x, y) : M × S` are such that
`z = f x * (f y)⁻¹`. -/
@[to_additive
/-- Given a localization map `f : M →+ N` for a submonoid `S ⊆ M` and a map of
`AddCommMonoid`s `g : M →+ P` such that `g y` is invertible for all `y : S`, the homomorphism
induced from `N` to `P` sending `z : N` to `g x - g y`, where `(x, y) : M × S` are such that
`z = f x - f y`. -/]
/-
**Submonoid.LocalizationMap.lift** 是 Mathlib 中的一个定义，位于命名空间 `Submonoid.Localizati
onMap`。
形式化陈述：lift : N ->* P where toFun z
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def lift : N →* P where
  toFun z := g (f.sec z).1 * (IsUnit.liftRight (g.domRestrict S) hg (f.sec z).2)⁻¹
  map_one' := by rw [mul_inv_left, mul_one]; exact f.eq_of_eq hg (by rw [← sec_spec, one_mul])
  map_mul' x y := by
    rw [mul_inv_left hg, ← mul_assoc, ← mul_assoc, mul_inv_right hg, mul_comm _ (g (f.sec y).1), ←
      mul_assoc, ← mul_assoc, mul_inv_right hg]
    repeat rw [← g.map_mul]
    refine f.eq_of_eq hg ?_
    simp_rw [map_mul, sec_spec', ← toMonoidHom_apply]
    ac_rfl

@[to_additive]
/-
**Submonoid.LocalizationMap.lift_apply** 是 Mathlib 中的一个引理，位于命名空间 `Submonoid.Loca
lizationMap`。
形式化陈述：lift_apply (z) : f.lift hg z = g (f.sec z).1 * (IsUnit.liftRight (g.domRes
trict S) hg (f.sec z).2)⁻¹
参数：z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma lift_apply (z) :
    f.lift hg z = g (f.sec z).1 * (IsUnit.liftRight (g.domRestrict S) hg (f.sec z).2)⁻¹ :=
  rfl

/-- Given a Localization map `f : M →* N` for a Submonoid `S ⊆ M` and a map of `CommMonoid`s
`g : M →* P` such that `g y` is invertible for all `y : S`, the homomorphism induced from
`N` to `P` maps `f x * (f y)⁻¹` to `g x * (g y)⁻¹` for all `x : M, y ∈ S`. -/
@[to_additive
/-- Given a Localization map `f : M →+ N` for an AddSubmonoid `S ⊆ M` and a map of
`AddCommMonoid`s `g : M →+ P` such that `g y` is invertible for all `y : S`, the homomorphism
induced from `N` to `P` maps `f x - f y` to `g x - g y` for all `x : M, y ∈ S`. -/]
/-
**Submonoid.LocalizationMap.lift_mk'** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid.Locali
zationMap`。
形式化陈述：lift_mk' (x y) : f.lift hg (f.mk' x y) = g x * (IsUnit.liftRight (g.domRes
trict S) hg y)⁻¹
参数：x y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `Submonoid.LocalizationMap.mul_inv`：mul_inv {f : M ->* N} (h : forall y :
 S, IsUnit (f y)) {x₁ x₂} {y₁ y₂ : S} : f x₁ * (IsUnit.liftRight (f.domRestrict 
S) h y₁)⁻¹ = f x₂ * (Is…
· 使用定理 `Submonoid.LocalizationMap.eq_of_eq`：eq_of_eq (hg : forall y : S, IsUnit 
(g y)) {x y} (h : f x = f y) : g x = g y
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `Submonoid.LocalizationMap.instMonoidHomClass`：∀ {M : Type u_1} [inst : C
ommMonoid M] {S : Submonoid M} {N : Type u_2} [inst_1 : CommMonoid N],   MonoidH
omClass (S.LocalizationMap N) M N
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Submonoid.LocalizationMap.sec_spec'`：sec_spec' {f : LocalizationMap S N}
 (z : N) : f (f.sec z).1 = f (f.sec z).2 * z
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Submonoid.LocalizationMap.mk'_spec`：∀ {M : Type u_1} [inst : CommMonoid 
M] {S : Submonoid M} {N : Type u_2} [inst_1 : CommMonoid N]   (f : S.Localizatio
nMap N) (x : M) (y : ↥S)…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lift_mk' (x y) :
    f.lift hg (f.mk' x y) = g x * (IsUnit.liftRight (g.domRestrict S) hg y)⁻¹ :=
  (mul_inv hg).2 <|
    f.eq_of_eq hg <| by
      simp_rw [map_mul, sec_spec', mul_assoc, f.mk'_spec, mul_comm]

/-- Given a Localization map `f : M →* N` for a Submonoid `S ⊆ M` and a localization map
`g : M →* P` for the same submonoid, the homomorphism induced from
`N` to `P` maps `f x * (f y)⁻¹` to `g x * (g y)⁻¹` for all `x : M, y ∈ S`. -/
@[to_additive (attr := simp)
/-- Given a Localization map `f : M →+ N` for an AddSubmonoid `S ⊆ M` and a localization map
`g : M →+ P` for the same submonoid, the homomorphism
induced from `N` to `P` maps `f x - f y` to `g x - g y` for all `x : M, y ∈ S`. -/]
/-
**Submonoid.LocalizationMap.lift_localizationMap_mk'** 是 Mathlib 中的一个定理，位于命名空间 `
Submonoid.LocalizationMap`。
形式化陈述：lift_localizationMap_mk' (g : S.LocalizationMap P) (x y) : f.lift g.map_un
its (f.mk' x y) = g.mk' x y
参数：g : S.LocalizationMap P；x y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.LocalizationMap.lift_mk'`：lift_mk' (x y) : f.lift hg (f.mk' x 
y) = g x * (IsUnit.liftRight (g.domRestrict S) hg y)⁻¹
· 使用定理 `Submonoid.LocalizationMap.map_units`：map_units (f : LocalizationMap S N)
 (y : S) : IsUnit (f y)
-/
theorem lift_localizationMap_mk' (g : S.LocalizationMap P) (x y) :
    f.lift g.map_units (f.mk' x y) = g.mk' x y :=
  f.lift_mk' _ _ _

/-- Given a Localization map `f : M →* N` for a Submonoid `S ⊆ M`, if a `CommMonoid` map
`g : M →* P` induces a map `f.lift hg : N →* P` then for all `z : N, v : P`, we have
`f.lift hg z = v ↔ g x = g y * v`, where `x : M, y ∈ S` are such that `z * f y = f x`. -/
@[to_additive
/-- Given a Localization map `f : M →+ N` for an AddSubmonoid `S ⊆ M`, if an
`AddCommMonoid` map `g : M →+ P` induces a map `f.lift hg : N →+ P` then for all
`z : N, v : P`, we have `f.lift hg z = v ↔ g x = g y + v`, where `x : M, y ∈ S` are such that
`z + f y = f x`. -/]
/-
**Submonoid.LocalizationMap.lift_spec** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid.Local
izationMap`。
形式化陈述：lift_spec (z v) : f.lift hg z = v ↔ g (f.sec z).1 = g (f.sec z).2 * v
参数：z v。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.LocalizationMap.mul_inv_left`：mul_inv_left {f : M ->* N} (h : 
forall y : S, IsUnit (f y)) (y : S) (w z : N) : w * (IsUnit.liftRight (f.domRest
rict S) h y)⁻¹ = z ↔ w = f y…
-/
theorem lift_spec (z v) : f.lift hg z = v ↔ g (f.sec z).1 = g (f.sec z).2 * v :=
  mul_inv_left hg _ _ v

/-- Given a Localization map `f : M →* N` for a Submonoid `S ⊆ M`, if a `CommMonoid` map
`g : M →* P` induces a map `f.lift hg : N →* P` then for all `z : N, v w : P`, we have
`f.lift hg z * w = v ↔ g x * w = g y * v`, where `x : M, y ∈ S` are such that
`z * f y = f x`. -/
@[to_additive
/-- Given a Localization map `f : M →+ N` for an AddSubmonoid `S ⊆ M`, if an `AddCommMonoid` map
`g : M →+ P` induces a map `f.lift hg : N →+ P` then for all
`z : N, v w : P`, we have `f.lift hg z + w = v ↔ g x + w = g y + v`, where `x : M, y ∈ S` are such
that `z + f y = f x`. -/]
/-
**Submonoid.LocalizationMap.lift_spec_mul** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid.L
ocalizationMap`。
形式化陈述：lift_spec_mul (z w v) : f.lift hg z * w = v ↔ g (f.sec z).1 * w = g (f.sec
 z).2 * v
参数：z w v。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用引理 `Submonoid.LocalizationMap.lift_apply`：lift_apply (z) : f.lift hg z = g (
f.sec z).1 * (IsUnit.liftRight (g.domRestrict S) hg (f.sec z).2)⁻¹
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Submonoid.LocalizationMap.mul_inv_left`：mul_inv_left {f : M ->* N} (h : 
forall y : S, IsUnit (f y)) (y : S) (w z : N) : w * (IsUnit.liftRight (f.domRest
rict S) h y)⁻¹ = z ↔ w = f y…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem lift_spec_mul (z w v) : f.lift hg z * w = v ↔ g (f.sec z).1 * w = g (f.sec z).2 * v := by
  rw [mul_comm, lift_apply, ← mul_assoc, mul_inv_left hg, mul_comm]

@[to_additive]
/-
**Submonoid.LocalizationMap.lift_mk'_spec** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid.L
ocalizationMap`。
形式化陈述：∀ {M : Type u_1} [inst : CommMonoid M] {S : Submonoid M} {N : Type u_2} [i
nst_1 : CommMonoid N] {P : Type u_3}   [inst_2 : CommMonoid P] (f : S.Localizati
onMap N) {g : M →* P} (hg : ∀ (y : ↥S), IsUnit (g ↑y)) (x : M) (v : P)   (y : ↥S
), (f.lift hg) (f.mk' x y) = v ↔ g x = g ↑y * v
参数：f : S.LocalizationMap N；hg : ∀ (y : ↥S), IsUnit (g ↑y)；x : M；v : P；y : ↥S；f.l
ift hg；f.mk' x y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submonoid.LocalizationMap.lift_mk'`：lift_mk' (x y) : f.lift hg (f.mk' x 
y) = g x * (IsUnit.liftRight (g.domRestrict S) hg y)⁻¹
· 使用定理 `Submonoid.LocalizationMap.mul_inv_left`：mul_inv_left {f : M ->* N} (h : 
forall y : S, IsUnit (f y)) (y : S) (w z : N) : w * (IsUnit.liftRight (f.domRest
rict S) h y)⁻¹ = z ↔ w = f y…
-/
theorem lift_mk'_spec (x v) (y : S) : f.lift hg (f.mk' x y) = v ↔ g x = g y * v := by
  rw [f.lift_mk' hg]; exact mul_inv_left hg _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- Given a Localization map `f : M →* N` for a Submonoid `S ⊆ M`, if a `CommMonoid` map
`g : M →* P` induces a map `f.lift hg : N →* P` then for all `z : N`, we have
`f.lift hg z * g y = g x`, where `x : M, y ∈ S` are such that `z * f y = f x`. -/
@[to_additive
/-- Given a Localization map `f : M →+ N` for an AddSubmonoid `S ⊆ M`, if an `AddCommMonoid`
map `g : M →+ P` induces a map `f.lift hg : N →+ P` then for all `z : N`, we have
`f.lift hg z + g y = g x`, where `x : M, y ∈ S` are such that `z + f y = f x`. -/]
/-
**Submonoid.LocalizationMap.lift_mul_right** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid.
LocalizationMap`。
形式化陈述：lift_mul_right (z) : f.lift hg z * g (f.sec z).2 = g (f.sec z).1
参数：z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Submonoid.LocalizationMap.lift_apply`：lift_apply (z) : f.lift hg z = g (
f.sec z).1 * (IsUnit.liftRight (g.domRestrict S) hg (f.sec z).2)⁻¹
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MonoidHom.domRestrict_apply`：domRestrict_apply {N S : Type*} [MulOneClas
s N] [SetLike S M] [SubmonoidClass S M] (f : M ->* N) (s : S) (x : s) : f.domRes
trict s x = f x
· 使用定理 `IsUnit.liftRight_inv_mul`：liftRight_inv_mul (f : M ->* N) (h : forall x,
 IsUnit (f x)) (x) : ↑(IsUnit.liftRight f h x)⁻¹ * f x = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem lift_mul_right (z) : f.lift hg z * g (f.sec z).2 = g (f.sec z).1 := by
  rw [lift_apply, mul_assoc, ← g.domRestrict_apply, IsUnit.liftRight_inv_mul, mul_one]

/-- Given a Localization map `f : M →* N` for a Submonoid `S ⊆ M`, if a `CommMonoid` map
`g : M →* P` induces a map `f.lift hg : N →* P` then for all `z : N`, we have
`g y * f.lift hg z = g x`, where `x : M, y ∈ S` are such that `z * f y = f x`. -/
@[to_additive
/-- Given a Localization map `f : M →+ N` for an AddSubmonoid `S ⊆ M`, if an `AddCommMonoid` map
`g : M →+ P` induces a map `f.lift hg : N →+ P` then for all `z : N`, we have
`g y + f.lift hg z = g x`, where `x : M, y ∈ S` are such that `z + f y = f x`. -/]
/-
**Submonoid.LocalizationMap.lift_mul_left** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid.L
ocalizationMap`。
形式化陈述：lift_mul_left (z) : g (f.sec z).2 * f.lift hg z = g (f.sec z).1
参数：z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Submonoid.LocalizationMap.lift_mul_right`：lift_mul_right (z) : f.lift hg
 z * g (f.sec z).2 = g (f.sec z).1
-/
theorem lift_mul_left (z) : g (f.sec z).2 * f.lift hg z = g (f.sec z).1 := by
  rw [mul_comm, lift_mul_right]

@[to_additive (attr := simp)]
/-
**Submonoid.LocalizationMap.lift_eq** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid.Localiz
ationMap`。
形式化陈述：lift_eq (x : M) : f.lift hg (f x) = g x
参数：x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submonoid.LocalizationMap.lift_spec`：lift_spec (z v) : f.lift hg z = v ↔
 g (f.sec z).1 = g (f.sec z).2 * v
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MonoidHom.map_mul`：∀ {M : Type u_4} {N : Type u_5} [inst : MulOne M] [in
st_1 : MulOne N] (f : M →* N) (a b : M), f (a * b) = f a * f b
· 使用定理 `Submonoid.LocalizationMap.eq_of_eq`：eq_of_eq (hg : forall y : S, IsUnit 
(g y)) {x y} (h : f x = f y) : g x = g y
· 使用定理 `Submonoid.LocalizationMap.sec_spec'`：sec_spec' {f : LocalizationMap S N}
 (z : N) : f (f.sec z).1 = f (f.sec z).2 * z
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `Submonoid.LocalizationMap.instMonoidHomClass`：∀ {M : Type u_1} [inst : C
ommMonoid M] {S : Submonoid M} {N : Type u_2} [inst_1 : CommMonoid N],   MonoidH
omClass (S.LocalizationMap N) M N
-/
theorem lift_eq (x : M) : f.lift hg (f x) = g x := by
  rw [lift_spec, ← g.map_mul]; exact f.eq_of_eq hg (by rw [sec_spec', map_mul])

@[to_additive]
/-
**Submonoid.LocalizationMap.lift_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid.Loc
alizationMap`。
形式化陈述：lift_eq_iff {x y : M × S} : f.lift hg (f.mk' x.1 x.2) = f.lift hg (f.mk' y
.1 y.2) ↔ g (x.1 * y.2) = g (y.1 * x.2)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submonoid.LocalizationMap.lift_mk'`：lift_mk' (x y) : f.lift hg (f.mk' x 
y) = g x * (IsUnit.liftRight (g.domRestrict S) hg y)⁻¹
· 使用定理 `Submonoid.LocalizationMap.mul_inv`：mul_inv {f : M ->* N} (h : forall y :
 S, IsUnit (f y)) {x₁ x₂} {y₁ y₂ : S} : f x₁ * (IsUnit.liftRight (f.domRestrict 
S) h y₁)⁻¹ = f x₂ * (Is…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem lift_eq_iff {x y : M × S} :
    f.lift hg (f.mk' x.1 x.2) = f.lift hg (f.mk' y.1 y.2) ↔ g (x.1 * y.2) = g (y.1 * x.2) := by
  rw [lift_mk', lift_mk', mul_inv hg]

@[to_additive (attr := simp)]
/-
**Submonoid.LocalizationMap.lift_comp** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid.Local
izationMap`。
形式化陈述：lift_comp : (f.lift hg).comp f.toMonoidHom = g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.ext`：MonoidHom.ext [MulOne M] [MulOne N] ⦃f g : M ->* N⦄ (h : 
forall x, f x = g x) : f = g
· 使用定理 `Submonoid.LocalizationMap.lift_eq`：lift_eq (x : M) : f.lift hg (f x) = g
 x
-/
theorem lift_comp : (f.lift hg).comp f.toMonoidHom = g := by ext; exact f.lift_eq hg _

@[to_additive (attr := simp)]
/-
**Submonoid.LocalizationMap.lift_of_comp** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid.Lo
calizationMap`。
形式化陈述：lift_of_comp (j : N ->* P) : f.lift (f.isUnit_comp j) = j
参数：j : N ->* P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.ext`：MonoidHom.ext [MulOne M] [MulOne N] ⦃f g : M ->* N⦄ (h : 
forall x, f x = g x) : f = g
· 使用定理 `Submonoid.LocalizationMap.isUnit_comp`：isUnit_comp (j : N ->* P) (y : S)
 : IsUnit (j.comp f.toMonoidHom y)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonoidHom.comp_apply`：MonoidHom.comp_apply [MulOne M] [MulOne N] [MulOne
 P] (g : N ->* P) (f : M ->* N) (x : M) : g.comp f x = g (f x)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Submonoid.LocalizationMap.sec_spec'`：sec_spec' {f : LocalizationMap S N}
 (z : N) : f (f.sec z).1 = f (f.sec z).2 * z
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lift_of_comp (j : N →* P) : f.lift (f.isUnit_comp j) = j := by
  ext; simp_rw [lift_spec, j.comp_apply, ← map_mul, toMonoidHom_apply, sec_spec']

@[to_additive]
/-
**Submonoid.LocalizationMap.lift_unique** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid.Loc
alizationMap`。
形式化陈述：lift_unique {j : N ->* P} (hj : forall x, j (f x) = g x) : f.lift hg = j
参数：hj : forall x, j (f x) = g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.ext`：MonoidHom.ext [MulOne M] [MulOne N] ⦃f g : M ->* N⦄ (h : 
forall x, f x = g x) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submonoid.LocalizationMap.lift_spec`：lift_spec (z v) : f.lift hg z = v ↔
 g (f.sec z).1 = g (f.sec z).2 * v
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MonoidHom.map_mul`：∀ {M : Type u_4} {N : Type u_5} [inst : MulOne M] [in
st_1 : MulOne N] (f : M →* N) (a b : M), f (a * b) = f a * f b
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Submonoid.LocalizationMap.sec_spec'`：sec_spec' {f : LocalizationMap S N}
 (z : N) : f (f.sec z).1 = f (f.sec z).2 * z
-/
theorem lift_unique {j : N →* P} (hj : ∀ x, j (f x) = g x) : f.lift hg = j := by
  ext
  rw [lift_spec, ← hj, ← hj, ← j.map_mul]
  apply congr_arg
  rw [← sec_spec']

@[to_additive (attr := simp)]
/-
**Submonoid.LocalizationMap.lift_id** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid.Localiz
ationMap`。
形式化陈述：lift_id (x) : f.lift f.map_units x = x
参数：x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submonoid.LocalizationMap.isUnit_comp`：isUnit_comp (j : N ->* P) (y : S)
 : IsUnit (j.comp f.toMonoidHom y)
· 使用定理 `DFunLike.ext_iff`：ext_iff {f g : F} : f = g ↔ forall x, f x = g x
· 使用定理 `Submonoid.LocalizationMap.lift_of_comp`：lift_of_comp (j : N ->* P) : f.l
ift (f.isUnit_comp j) = j
-/
theorem lift_id (x) : f.lift f.map_units x = x :=
  DFunLike.ext_iff.1 (f.lift_of_comp <| MonoidHom.id N) x

/-- Given Localization maps `f : M →* N` for a Submonoid `S ⊆ M` and
`k : M →* Q` for a Submonoid `T ⊆ M`, such that `S ≤ T`, and we have
`l : M →* A`, the composition of the induced map `f.lift` for `k` with
the induced map `k.lift` for `l` is equal to the induced map `f.lift` for `l`. -/
@[to_additive
/-- Given Localization maps `f : M →+ N` for a Submonoid `S ⊆ M` and
`k : M →+ Q` for a Submonoid `T ⊆ M`, such that `S ≤ T`, and we have
`l : M →+ A`, the composition of the induced map `f.lift` for `k` with
the induced map `k.lift` for `l` is equal to the induced map `f.lift` for `l` -/]
/-
**Submonoid.LocalizationMap.lift_comp_lift** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid.
LocalizationMap`。
形式化陈述：lift_comp_lift {T : Submonoid M} (hST : S <= T) {Q : Type*} [CommMonoid Q]
 (k : LocalizationMap T Q) {A : Type*} [CommMonoid A] {l : M ->* A} (hl : forall
 w : T, IsUnit (l w)) : (k.lift hl).comp (f.lift (map_units k ⟨_, hST ·.2⟩)) = f
.lift (hl ⟨_, hST ·.2⟩)
参数：hST : S <= T；k : LocalizationMap T Q；hl : forall w : T, IsUnit (l w)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Submonoid.LocalizationMap.map_units`：map_units (f : LocalizationMap S N)
 (y : S) : IsUnit (f y)
· 使用定理 `Submonoid.LocalizationMap.lift_unique`：lift_unique {j : N ->* P} (hj : f
orall x, j (f x) = g x) : f.lift hg = j
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submonoid.LocalizationMap.toMonoidHom_apply`：∀ {M : Type u_1} [inst : Co
mmMonoid M] {S : Submonoid M} {N : Type u_2} [inst_1 : CommMonoid N]   (f : S.Lo
calizationMap N) (x : M), f.toMon…
· 使用定理 `MonoidHom.comp_apply`：MonoidHom.comp_apply [MulOne M] [MulOne N] [MulOne
 P] (g : N ->* P) (f : M ->* N) (x : M) : g.comp f x = g (f x)
· 使用定理 `MonoidHom.comp_assoc`：MonoidHom.comp_assoc {Q : Type*} [MulOne M] [MulOn
e N] [MulOne P] [MulOne Q] (f : M ->* N) (g : N ->* P) (h : P ->* Q) : (h.comp g
).comp f =…
· 使用定理 `Submonoid.LocalizationMap.lift_comp`：lift_comp : (f.lift hg).comp f.toMo
noidHom = g
-/
theorem lift_comp_lift {T : Submonoid M} (hST : S ≤ T) {Q : Type*} [CommMonoid Q]
    (k : LocalizationMap T Q) {A : Type*} [CommMonoid A] {l : M →* A}
    (hl : ∀ w : T, IsUnit (l w)) :
    (k.lift hl).comp (f.lift (map_units k ⟨_, hST ·.2⟩)) =
    f.lift (hl ⟨_, hST ·.2⟩) := .symm <|
  lift_unique _ _ fun x ↦ by rw [← toMonoidHom_apply, ← MonoidHom.comp_apply,
    MonoidHom.comp_assoc, lift_comp, lift_comp]

@[to_additive]
/-
**Submonoid.LocalizationMap.lift_comp_lift_eq** 是 Mathlib 中的一个定理，位于命名空间 `Submono
id.LocalizationMap`。
形式化陈述：lift_comp_lift_eq {Q : Type*} [CommMonoid Q] (k : LocalizationMap S Q) {A 
: Type*} [CommMonoid A] {l : M ->* A} (hl : forall w : S, IsUnit (l w)) : (k.lif
t hl).comp (f.lift k.map_units) = f.lift hl
参数：k : LocalizationMap S Q；hl : forall w : S, IsUnit (l w)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.LocalizationMap.lift_comp_lift`：lift_comp_lift {T : Submonoid 
M} (hST : S <= T) {Q : Type*} [CommMonoid Q] (k : LocalizationMap T Q) {A : Type
*} [CommMonoid A] {l : M ->* A…
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem lift_comp_lift_eq {Q : Type*} [CommMonoid Q] (k : LocalizationMap S Q)
    {A : Type*} [CommMonoid A] {l : M →* A} (hl : ∀ w : S, IsUnit (l w)) :
    (k.lift hl).comp (f.lift k.map_units) = f.lift hl :=
  lift_comp_lift f le_rfl k hl

/-- Given two Localization maps `f : M →* N, k : M →* P` for a Submonoid `S ⊆ M`, the hom
from `P` to `N` induced by `f` is left inverse to the hom from `N` to `P` induced by `k`. -/
@[to_additive (attr := simp)
/-- Given two Localization maps `f : M →+ N, k : M →+ P` for a Submonoid `S ⊆ M`, the hom
from `P` to `N` induced by `f` is left inverse to the hom from `N` to `P` induced by `k`. -/]
/-
**Submonoid.LocalizationMap.lift_left_inverse** 是 Mathlib 中的一个定理，位于命名空间 `Submono
id.LocalizationMap`。
形式化陈述：lift_left_inverse {k : LocalizationMap S P} (z : N) : k.lift f.map_units (
f.lift k.map_units z) = z
参数：z : N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Submonoid.LocalizationMap.map_units`：map_units (f : LocalizationMap S N)
 (y : S) : IsUnit (f y)
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用定理 `Submonoid.LocalizationMap.lift_comp_lift_eq`：lift_comp_lift_eq {Q : Type
*} [CommMonoid Q] (k : LocalizationMap S Q) {A : Type*} [CommMonoid A] {l : M ->
* A} (hl : forall w : S, IsUnit (…
· 使用定理 `Submonoid.LocalizationMap.lift_id`：lift_id (x) : f.lift f.map_units x = 
x
-/
theorem lift_left_inverse {k : LocalizationMap S P} (z : N) :
    k.lift f.map_units (f.lift k.map_units z) = z :=
  (DFunLike.congr_fun (lift_comp_lift_eq f k f.map_units) z).trans (lift_id f z)

@[to_additive]
/-
**Submonoid.LocalizationMap.lift_surjective_iff** 是 Mathlib 中的一个定理，位于命名空间 `Submo
noid.LocalizationMap`。
形式化陈述：lift_surjective_iff : Function.Surjective (f.lift hg) ↔ forall v : P, exis
ts x : M × S, v * g x.2 = g x.1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.LocalizationMap.surj`：surj (f : LocalizationMap S N) (z : N) :
 exists x : M × S, z * f x.2 = f x.1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submonoid.LocalizationMap.eq_mk'_iff_mul_eq`：∀ {M : Type u_1} [inst : Co
mmMonoid M] {S : Submonoid M} {N : Type u_2} [inst_1 : CommMonoid N]   (f : S.Lo
calizationMap N) {x : M} {y : ↥S}…
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `Submonoid.LocalizationMap.lift_mk'`：lift_mk' (x y) : f.lift hg (f.mk' x 
y) = g x * (IsUnit.liftRight (g.domRestrict S) hg y)⁻¹
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `MonoidHom.domRestrict_apply`：domRestrict_apply {N S : Type*} [MulOneClas
s N] [SetLike S M] [SubmonoidClass S M] (f : M ->* N) (s : S) (x : s) : f.domRes
trict s x = f x
· 使用定理 `IsUnit.mul_liftRight_inv`：mul_liftRight_inv (f : M ->* N) (h : forall x,
 IsUnit (f x)) (x) : f x * ↑(IsUnit.liftRight f h x)⁻¹ = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Submonoid.LocalizationMap.mul_inv_left`：mul_inv_left {f : M ->* N} (h : 
forall y : S, IsUnit (f y)) (y : S) (w z : N) : w * (IsUnit.liftRight (f.domRest
rict S) h y)⁻¹ = z ↔ w = f y…
-/
theorem lift_surjective_iff :
    Function.Surjective (f.lift hg) ↔ ∀ v : P, ∃ x : M × S, v * g x.2 = g x.1 := by
  constructor
  · intro H v
    obtain ⟨z, hz⟩ := H v
    obtain ⟨x, hx⟩ := f.surj z
    use x
    rw [← hz, f.eq_mk'_iff_mul_eq.2 hx, lift_mk', mul_assoc, mul_comm _ (g ↑x.2),
      ← MonoidHom.domRestrict_apply, IsUnit.mul_liftRight_inv (g.domRestrict S) hg, mul_one]
  · intro H v
    obtain ⟨x, hx⟩ := H v
    use f.mk' x.1 x.2
    rw [lift_mk', mul_inv_left hg, mul_comm, ← hx]

@[to_additive]
/-
**Submonoid.LocalizationMap.lift_injective_iff** 是 Mathlib 中的一个定理，位于命名空间 `Submon
oid.LocalizationMap`。
形式化陈述：lift_injective_iff : Function.Injective (f.lift hg) ↔ forall x y, f x = f 
y ↔ g x = g y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.LocalizationMap.eq_of_eq`：eq_of_eq (hg : forall y : S, IsUnit 
(g y)) {x y} (h : f x = f y) : g x = g y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submonoid.LocalizationMap.lift_eq`：lift_eq (x : M) : f.lift hg (f x) = g
 x
· 使用定理 `Submonoid.LocalizationMap.surj`：surj (f : LocalizationMap S N) (z : N) :
 exists x : M × S, z * f x.2 = f x.1
· 使用定理 `Submonoid.LocalizationMap.mk'_sec`：∀ {M : Type u_1} [inst : CommMonoid M
] {S : Submonoid M} {N : Type u_2} [inst_1 : CommMonoid N]   (f : S.Localization
Map N) (z : N), f.mk' (…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `Submonoid.LocalizationMap.map_units`：map_units (f : LocalizationMap S N)
 (y : S) : IsUnit (f y)
· 使用定理 `Submonoid.LocalizationMap.mul_inv`：mul_inv {f : M ->* N} (h : forall y :
 S, IsUnit (f y)) {x₁ x₂} {y₁ y₂ : S} : f x₁ * (IsUnit.liftRight (f.domRestrict 
S) h y₁)⁻¹ = f x₂ * (Is…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem lift_injective_iff :
    Function.Injective (f.lift hg) ↔ ∀ x y, f x = f y ↔ g x = g y := by
  constructor
  · intro H x y
    constructor
    · exact f.eq_of_eq hg
    · intro h
      rw [← f.lift_eq hg, ← f.lift_eq hg] at h
      exact H h
  · intro H z w h
    obtain ⟨_, _⟩ := f.surj z
    obtain ⟨_, _⟩ := f.surj w
    rw [← f.mk'_sec z, ← f.mk'_sec w]
    exact (mul_inv f.map_units).2 ((H _ _).2 <| (mul_inv hg).1 h)

variable {T : Submonoid P} (hy : ∀ y : S, g y ∈ T) {Q : Type*} [CommMonoid Q]
  (k : LocalizationMap T Q)

/-- Given a `CommMonoid` homomorphism `g : M →* P` where for Submonoids `S ⊆ M, T ⊆ P` we have
`g(S) ⊆ T`, the induced Monoid homomorphism from the Localization of `M` at `S` to the
Localization of `P` at `T`: if `f : M →* N` and `k : P →* Q` are Localization maps for `S` and
`T` respectively, we send `z : N` to `k (g x) * (k (g y))⁻¹`, where `(x, y) : M × S` are such
that `z = f x * (f y)⁻¹`. -/
@[to_additive
/-- Given an `AddCommMonoid` homomorphism `g : M →+ P` where for AddSubmonoids `S ⊆ M, T ⊆ P` we
have `g(S) ⊆ T`, the induced AddMonoid homomorphism from the Localization of `M` at `S` to the
Localization of `P` at `T`: if `f : M →+ N` and `k : P →+ Q` are Localization maps for `S` and
`T` respectively, we send `z : N` to `k (g x) - k (g y)`, where `(x, y) : M × S` are such
that `z = f x - f y`. -/]
/-
**Submonoid.LocalizationMap.map** 是 Mathlib 中的一个定义，位于命名空间 `Submonoid.Localizatio
nMap`。
形式化陈述：map : N ->* Q
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def map : N →* Q :=
  @lift _ _ _ _ _ _ _ f (k.toMonoidHom.comp g) fun y ↦ k.map_units ⟨g y, hy y⟩

variable {k}

@[to_additive (attr := simp)]
/-
**Submonoid.LocalizationMap.map_eq** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid.Localiza
tionMap`。
形式化陈述：map_eq (x) : f.map hy k (f x) = k (g x)
参数：x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.LocalizationMap.lift_eq`：lift_eq (x : M) : f.lift hg (f x) = g
 x
· 使用定理 `Submonoid.LocalizationMap.map_units`：map_units (f : LocalizationMap S N)
 (y : S) : IsUnit (f y)
-/
theorem map_eq (x) : f.map hy k (f x) = k (g x) :=
  f.lift_eq (fun y ↦ k.map_units ⟨g y, hy y⟩) x

@[to_additive (attr := simp)]
/-
**Submonoid.LocalizationMap.map_comp** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid.Locali
zationMap`。
形式化陈述：map_comp : (f.map hy k).comp f.toMonoidHom = k.toMonoidHom.comp g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.LocalizationMap.lift_comp`：lift_comp : (f.lift hg).comp f.toMo
noidHom = g
· 使用定理 `Submonoid.LocalizationMap.map_units`：map_units (f : LocalizationMap S N)
 (y : S) : IsUnit (f y)
-/
theorem map_comp : (f.map hy k).comp f.toMonoidHom = k.toMonoidHom.comp g :=
  f.lift_comp fun y ↦ k.map_units ⟨g y, hy y⟩

set_option backward.isDefEq.respectTransparency false in
@[to_additive (attr := simp)]
/-
**Submonoid.LocalizationMap.map_mk'** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid.Localiz
ationMap`。
形式化陈述：map_mk' (x) (y : S) : f.map hy k (f.mk' x y) = k.mk' (g x) ⟨g y, hy y⟩
参数：x；y : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submonoid.LocalizationMap.map.eq_1`：∀ {M : Type u_1} [inst : CommMonoid 
M] {S : Submonoid M} {N : Type u_2} [inst_1 : CommMonoid N] {P : Type u_3}   [in
st_2 : CommMonoid P] (f …
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `Submonoid.LocalizationMap.lift_mk'`：lift_mk' (x y) : f.lift hg (f.mk' x 
y) = g x * (IsUnit.liftRight (g.domRestrict S) hg y)⁻¹
· 使用定理 `Submonoid.LocalizationMap.mul_inv_left`：mul_inv_left {f : M ->* N} (h : 
forall y : S, IsUnit (f y)) (y : S) (w z : N) : w * (IsUnit.liftRight (f.domRest
rict S) h y)⁻¹ = z ↔ w = f y…
· 使用定理 `Submonoid.LocalizationMap.mul_mk'_eq_mk'_of_mul`：∀ {M : Type u_1} [inst 
: CommMonoid M] {S : Submonoid M} {N : Type u_2} [inst_1 : CommMonoid N]   (f : 
S.LocalizationMap N) (x₁ x₂ : M) (y :…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submonoid.LocalizationMap.mk'_mul_cancel_left`：∀ {M : Type u_1} [inst : 
CommMonoid M] {S : Submonoid M} {N : Type u_2} [inst_1 : CommMonoid N]   (f : S.
LocalizationMap N) (x : M) (y : ↥S)…
-/
theorem map_mk' (x) (y : S) : f.map hy k (f.mk' x y) = k.mk' (g x) ⟨g y, hy y⟩ := by
  rw [map, lift_mk', mul_inv_left]
  change k (g x) = k (g y) * _
  rw [mul_mk'_eq_mk'_of_mul]
  exact (k.mk'_mul_cancel_left (g x) ⟨g y, hy y⟩).symm

/-- Given Localization maps `f : M →* N, k : P →* Q` for Submonoids `S, T` respectively, if a
`CommMonoid` homomorphism `g : M →* P` induces a `f.map hy k : N →* Q`, then for all `z : N`,
`u : Q`, we have `f.map hy k z = u ↔ k (g x) = k (g y) * u` where `x : M, y ∈ S` are such that
`z * f y = f x`. -/
@[to_additive
/-- Given Localization maps `f : M →+ N, k : P →+ Q` for AddSubmonoids `S, T` respectively, if an
`AddCommMonoid` homomorphism `g : M →+ P` induces a `f.map hy k : N →+ Q`, then for all `z : N`,
`u : Q`, we have `f.map hy k z = u ↔ k (g x) = k (g y) + u` where `x : M, y ∈ S` are such that
`z + f y = f x`. -/]
/-
**Submonoid.LocalizationMap.map_spec** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid.Locali
zationMap`。
形式化陈述：map_spec (z u) : f.map hy k z = u ↔ k (g (f.sec z).1) = k (g (f.sec z).2) 
* u
参数：z u。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.LocalizationMap.lift_spec`：lift_spec (z v) : f.lift hg z = v ↔
 g (f.sec z).1 = g (f.sec z).2 * v
· 使用定理 `Submonoid.LocalizationMap.map_units`：map_units (f : LocalizationMap S N)
 (y : S) : IsUnit (f y)
-/
theorem map_spec (z u) : f.map hy k z = u ↔ k (g (f.sec z).1) = k (g (f.sec z).2) * u :=
  f.lift_spec (fun y ↦ k.map_units ⟨g y, hy y⟩) _ _

/-- Given Localization maps `f : M →* N, k : P →* Q` for Submonoids `S, T` respectively, if a
`CommMonoid` homomorphism `g : M →* P` induces a `f.map hy k : N →* Q`, then for all `z : N`,
we have `f.map hy k z * k (g y) = k (g x)` where `x : M, y ∈ S` are such that
`z * f y = f x`. -/
@[to_additive
/-- Given Localization maps `f : M →+ N, k : P →+ Q` for AddSubmonoids `S, T` respectively, if an
`AddCommMonoid` homomorphism `g : M →+ P` induces a `f.map hy k : N →+ Q`, then for all `z : N`,
we have `f.map hy k z + k (g y) = k (g x)` where `x : M, y ∈ S` are such that
`z + f y = f x`. -/]
/-
**Submonoid.LocalizationMap.map_mul_right** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid.L
ocalizationMap`。
形式化陈述：map_mul_right (z) : f.map hy k z * k (g (f.sec z).2) = k (g (f.sec z).1)
参数：z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.LocalizationMap.lift_mul_right`：lift_mul_right (z) : f.lift hg
 z * g (f.sec z).2 = g (f.sec z).1
· 使用定理 `Submonoid.LocalizationMap.map_units`：map_units (f : LocalizationMap S N)
 (y : S) : IsUnit (f y)
-/
theorem map_mul_right (z) : f.map hy k z * k (g (f.sec z).2) = k (g (f.sec z).1) :=
  f.lift_mul_right (fun y ↦ k.map_units ⟨g y, hy y⟩) _

/-- Given Localization maps `f : M →* N, k : P →* Q` for Submonoids `S, T` respectively, if a
`CommMonoid` homomorphism `g : M →* P` induces a `f.map hy k : N →* Q`, then for all `z : N`,
we have `k (g y) * f.map hy k z = k (g x)` where `x : M, y ∈ S` are such that
`z * f y = f x`. -/
@[to_additive
/-- Given Localization maps `f : M →+ N, k : P →+ Q` for AddSubmonoids `S, T` respectively if an
`AddCommMonoid` homomorphism `g : M →+ P` induces a `f.map hy k : N →+ Q`, then for all `z : N`,
we have `k (g y) + f.map hy k z = k (g x)` where `x : M, y ∈ S` are such that
`z + f y = f x`. -/]
/-
**Submonoid.LocalizationMap.map_mul_left** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid.Lo
calizationMap`。
形式化陈述：map_mul_left (z) : k (g (f.sec z).2) * f.map hy k z = k (g (f.sec z).1)
参数：z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Submonoid.LocalizationMap.map_mul_right`：map_mul_right (z) : f.map hy k 
z * k (g (f.sec z).2) = k (g (f.sec z).1)
-/
theorem map_mul_left (z) : k (g (f.sec z).2) * f.map hy k z = k (g (f.sec z).1) := by
  rw [mul_comm, f.map_mul_right]

@[to_additive (attr := simp)]
/-
**Submonoid.LocalizationMap.map_id** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid.Localiza
tionMap`。
形式化陈述：map_id (z : N) : f.map (fun y => show MonoidHom.id M y in S from y.2) f z 
= z
参数：z : N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.LocalizationMap.lift_id`：lift_id (x) : f.lift f.map_units x = 
x
-/
theorem map_id (z : N) : f.map (fun y ↦ show MonoidHom.id M y ∈ S from y.2) f z = z :=
  f.lift_id z

set_option backward.isDefEq.respectTransparency false in
/-- If `CommMonoid` homs `g : M →* P, l : P →* A` induce maps of localizations, the composition
of the induced maps equals the map of localizations induced by `l ∘ g`. -/
@[to_additive
/-- If `AddCommMonoid` homs `g : M →+ P, l : P →+ A` induce maps of localizations, the composition
of the induced maps equals the map of localizations induced by `l ∘ g`. -/]
/-
**Submonoid.LocalizationMap.map_comp_map** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid.Lo
calizationMap`。
形式化陈述：map_comp_map {A : Type*} [CommMonoid A] {U : Submonoid A} {R} [CommMonoid 
R] (j : LocalizationMap U R) {l : P ->* A} (hl : forall w : T, l w in U) : (k.ma
p hl j).comp (f.map hy k) = f.map (fun x => show l.comp g x in U from hl ⟨g x, h
y x⟩) j
参数：j : LocalizationMap U R；hl : forall w : T, l w in U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.ext`：MonoidHom.ext [MulOne M] [MulOne N] ⦃f g : M ->* N⦄ (h : 
forall x, f x = g x) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `Submonoid.LocalizationMap.mul_inv_left`：mul_inv_left {f : M ->* N} (h : 
forall y : S, IsUnit (f y)) (y : S) (w z : N) : w * (IsUnit.liftRight (f.domRest
rict S) h y)⁻¹ = z ↔ w = f y…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Submonoid.LocalizationMap.mul_inv_right`：mul_inv_right {f : M ->* N} (h 
: forall y : S, IsUnit (f y)) (y : S) (w z : N) : z = w * (IsUnit.liftRight (f.d
omRestrict S) h y)⁻¹ ↔ z * f …
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `Submonoid.LocalizationMap.instMonoidHomClass`：∀ {M : Type u_1} [inst : C
ommMonoid M] {S : Submonoid M} {N : Type u_2} [inst_1 : CommMonoid N],   MonoidH
omClass (S.LocalizationMap N) M N
· 使用定理 `MonoidHom.map_mul`：∀ {M : Type u_4} {N : Type u_5} [inst : MulOne M] [in
st_1 : MulOne N] (f : M →* N) (a b : M), f (a * b) = f a * f b
· 使用定理 `Submonoid.LocalizationMap.comp_eq_of_eq`：comp_eq_of_eq {T : Submonoid P}
 {Q : Type*} [CommMonoid Q] (hg : forall y : S, g y in T) (k : LocalizationMap T
 Q) {x y} (h : f x = f y) : k…
· 使用定理 `Submonoid.LocalizationMap.sec_spec'`：sec_spec' {f : LocalizationMap S N}
 (z : N) : f (f.sec z).1 = f (f.sec z).2 * z
· 使用定理 `Submonoid.LocalizationMap.map_mul_right`：map_mul_right (z) : f.map hy k 
z * k (g (f.sec z).2) = k (g (f.sec z).1)
-/
theorem map_comp_map {A : Type*} [CommMonoid A] {U : Submonoid A} {R} [CommMonoid R]
    (j : LocalizationMap U R) {l : P →* A} (hl : ∀ w : T, l w ∈ U) :
    (k.map hl j).comp (f.map hy k) =
    f.map (fun x ↦ show l.comp g x ∈ U from hl ⟨g x, hy x⟩) j := by
  ext z
  change j _ * _ = j (l _) * _
  rw [mul_inv_left, ← mul_assoc, mul_inv_right]
  change j _ * j (l (g _)) = j (l _) * _
  rw [← map_mul j, ← map_mul j, ← l.map_mul, ← l.map_mul]
  refine k.comp_eq_of_eq hl j ?_
  rw [map_mul k, map_mul k, sec_spec', mul_assoc, map_mul_right]

/-- If `CommMonoid` homs `g : M →* P, l : P →* A` induce maps of localizations, the composition
of the induced maps equals the map of localizations induced by `l ∘ g`. -/
@[to_additive
/-- If `AddCommMonoid` homs `g : M →+ P, l : P →+ A` induce maps of localizations, the composition
of the induced maps equals the map of localizations induced by `l ∘ g`. -/]
/-
**Submonoid.LocalizationMap.map_map** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid.Localiz
ationMap`。
形式化陈述：map_map {A : Type*} [CommMonoid A] {U : Submonoid A} {R} [CommMonoid R] (j
 : LocalizationMap U R) {l : P ->* A} (hl : forall w : T, l w in U) (x) : k.map 
hl j (f.map hy k x) = f.map (fun x => show l.comp g x in U from hl ⟨g x, hy x⟩) 
j x
参数：j : LocalizationMap U R；hl : forall w : T, l w in U；x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submonoid.LocalizationMap.map_comp_map`：map_comp_map {A : Type*} [CommMo
noid A] {U : Submonoid A} {R} [CommMonoid R] (j : LocalizationMap U R) {l : P ->
* A} (hl : forall w : T, l w…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_map {A : Type*} [CommMonoid A] {U : Submonoid A} {R} [CommMonoid R]
    (j : LocalizationMap U R) {l : P →* A} (hl : ∀ w : T, l w ∈ U) (x) :
    k.map hl j (f.map hy k x) = f.map (fun x ↦ show l.comp g x ∈ U from hl ⟨g x, hy x⟩) j x := by
  -- Porting note: need to specify `k` explicitly
  rw [← f.map_comp_map (k := k) hy j hl]
  simp only [MonoidHom.coe_comp, comp_apply]
/-
**Submonoid.LocalizationMap.map_injective_of_surjOn_or_injective** 是 Mathlib 中的一
个定理，位于命名空间 `Submonoid.LocalizationMap`。
形式化陈述：∀ {M : Type u_1} [inst : CommMonoid M] {S : Submonoid M} {N : Type u_2} [i
nst_1 : CommMonoid N] {P : Type u_3}   [inst_2 : CommMonoid P] (f : S.Localizati
onMap N) {g : M →* P} {T : Submonoid P} (hy : ∀ (y : ↥S), g ↑y ∈ T)   {Q : Type 
u_4} [inst_3 : CommMonoid Q] {k : T.LocalizationMap Q},   Set.SurjOn ⇑g ↑S ↑T ∨ 
Function.Injective ⇑k → Function.Injective ⇑g → Function.Injective ⇑(f.map hy k)
参数：f : S.LocalizationMap N；hy : ∀ (y : ↥S), g ↑y ∈ T；f.map hy k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.LocalizationMap.map_eq`：map_eq (x) : f.map hy k (f x) = k (g x
)
· 使用定理 `Submonoid.LocalizationMap.surj₂`：surj₂ (f : LocalizationMap S N) (z w : 
N) : exists z' w' : M, exists d : S, (z * f d = f z') ∧ (w * f d = f w')
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `Submonoid.LocalizationMap.exists_of_eq`：exists_of_eq (f : LocalizationMa
p S N) {x y : M} : f x = f y -> exists c : S, c * x = c * y
· 使用定理 `IsUnit.mul_left_inj`：mul_left_inj (h : IsUnit a) : b * a = c * a ↔ b = c
· 使用定理 `Submonoid.LocalizationMap.map_units`：map_units (f : LocalizationMap S N)
 (y : S) : IsUnit (f y)
· 使用定理 `Submonoid.LocalizationMap.eq_iff_exists`：eq_iff_exists (f : Localization
Map S N) {x y} : f x = f y ↔ exists c : S, c * x = c * y
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `IsUnit.mul_right_cancel`：∀ {M : Type u_1} [inst : Monoid M] {a b c : M},
 IsUnit b → a * b = c * b → a = c
-/
@[to_additive] theorem map_injective_of_surjOn_or_injective
    (or : (S : Set M).SurjOn g T ∨ Injective k) (hg : Injective g) :
    Injective (f.map hy k) := fun z w hizw ↦ by
  set i := f.map hy k
  have ifkg (a : M) : i (f a) = k (g a) := f.map_eq hy a
  have ⟨z', w', x, hxz, hxw⟩ := surj₂ f z w
  have : k (g z') = k (g w') := by rw [← ifkg, ← ifkg, ← hxz, ← hxw, map_mul, map_mul, hizw]
  obtain surj | inj := or
  · have ⟨⟨c, hc'⟩, eq⟩ := k.exists_of_eq this
    obtain ⟨c, hc, rfl⟩ := surj hc'
    simp_rw [← map_mul, hg.eq_iff] at eq
    rw [← (f.map_units x).mul_left_inj, hxz, hxw, f.eq_iff_exists]
    exact ⟨⟨c, hc⟩, eq⟩
  · apply (f.map_units x).mul_right_cancel
    rw [hxz, hxw, hg (inj this)]
/-
**Submonoid.LocalizationMap.map_surjective_of_surjOn** 是 Mathlib 中的一个定理，位于命名空间 `
Submonoid.LocalizationMap`。
形式化陈述：∀ {M : Type u_1} [inst : CommMonoid M] {S : Submonoid M} {N : Type u_2} [i
nst_1 : CommMonoid N] {P : Type u_3}   [inst_2 : CommMonoid P] (f : S.Localizati
onMap N) {g : M →* P} {T : Submonoid P} (hy : ∀ (y : ↥S), g ↑y ∈ T)   {Q : Type 
u_4} [inst_3 : CommMonoid Q] {k : T.LocalizationMap Q},   Set.SurjOn ⇑g ↑S ↑T → 
Function.Surjective ⇑g → Function.Surjective ⇑(f.map hy k)
参数：f : S.LocalizationMap N；hy : ∀ (y : ↥S), g ↑y ∈ T；f.map hy k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.LocalizationMap.mk'_surjective`：∀ {M : Type u_1} [inst : CommM
onoid M] {S : Submonoid M} {N : Type u_2} [inst_1 : CommMonoid N]   (f : S.Local
izationMap N) (z : N), ∃ x y, …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submonoid.LocalizationMap.map_mk'`：map_mk' (x) (y : S) : f.map hy k (f.m
k' x y) = k.mk' (g x) ⟨g y, hy y⟩
-/
@[to_additive] theorem map_surjective_of_surjOn (surj : (S : Set M).SurjOn g T)
    (hg : Surjective g) : Surjective (f.map hy k) := fun z ↦ by
  obtain ⟨y, ⟨t, ht⟩, rfl⟩ := k.mk'_surjective z
  obtain ⟨s, hs, rfl⟩ := surj ht
  obtain ⟨x, rfl⟩ := hg y
  use f.mk' x ⟨s, hs⟩
  rw [map_mk']

/-- Given an injective `CommMonoid` homomorphism `g : M →* P`, and a submonoid `S ⊆ M`,
the induced monoid homomorphism from the localization of `M` at `S` to the
localization of `P` at `g S`, is injective.
-/
@[to_additive /-- Given an injective `AddCommMonoid` homomorphism `g : M →+ P`, and a
submonoid `S ⊆ M`, the induced monoid homomorphism from the localization of `M` at `S`
to the localization of `P` at `g S`, is injective. -/]
/-
**Submonoid.LocalizationMap.map_injective_of_injective** 是 Mathlib 中的一个定理，位于命名空间
 `Submonoid.LocalizationMap`。
形式化陈述：map_injective_of_injective (hg : Injective g) (k : LocalizationMap (S.map 
g) Q) : Injective (map f (apply_coe_mem_map g S) k)
参数：hg : Injective g；k : LocalizationMap (S.map g) Q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.LocalizationMap.map_injective_of_surjOn_or_injective`：∀ {M : T
ype u_1} [inst : CommMonoid M] {S : Submonoid M} {N : Type u_2} [inst_1 : CommMo
noid N] {P : Type u_3}   [inst_2 : CommMonoid P] (f …
· 使用定理 `Submonoid.apply_coe_mem_map`：apply_coe_mem_map (f : F) (S : Submonoid M)
 (x : S) : f x in S.map f
· 使用定理 `Set.surjOn_image`：surjOn_image (f : α -> β) (s : Set α) : SurjOn f s (f 
'' s)
-/
theorem map_injective_of_injective (hg : Injective g) (k : LocalizationMap (S.map g) Q) :
    Injective (map f (apply_coe_mem_map g S) k) :=
  f.map_injective_of_surjOn_or_injective _ (.inl <| Set.surjOn_image ..) hg

/-- Given a surjective `CommMonoid` homomorphism `g : M →* P`, and a submonoid `S ⊆ M`,
the induced monoid homomorphism from the localization of `M` at `S` to the
localization of `P` at `g S`, is surjective.
-/
@[to_additive /-- Given a surjective `AddCommMonoid` homomorphism `g : M →+ P`, and a
submonoid `S ⊆ M`, the induced monoid homomorphism from the localization of `M` at `S`
to the localization of `P` at `g S`, is surjective. -/]
/-
**Submonoid.LocalizationMap.map_surjective_of_surjective** 是 Mathlib 中的一个定理，位于命名
空间 `Submonoid.LocalizationMap`。
形式化陈述：map_surjective_of_surjective (hg : Surjective g) (k : LocalizationMap (S.m
ap g) Q) : Surjective (map f (apply_coe_mem_map g S) k)
参数：hg : Surjective g；k : LocalizationMap (S.map g) Q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.LocalizationMap.map_surjective_of_surjOn`：∀ {M : Type u_1} [in
st : CommMonoid M] {S : Submonoid M} {N : Type u_2} [inst_1 : CommMonoid N] {P :
 Type u_3}   [inst_2 : CommMonoid P] (f …
· 使用定理 `Submonoid.apply_coe_mem_map`：apply_coe_mem_map (f : F) (S : Submonoid M)
 (x : S) : f x in S.map f
· 使用定理 `Set.surjOn_image`：surjOn_image (f : α -> β) (s : Set α) : SurjOn f s (f 
'' s)
-/
theorem map_surjective_of_surjective (hg : Surjective g) (k : LocalizationMap (S.map g) Q) :
    Surjective (map f (apply_coe_mem_map g S) k) :=
  f.map_surjective_of_surjOn _ (Set.surjOn_image ..) hg

end LocalizationMap

end Submonoid

namespace Submonoid

namespace LocalizationMap

variable (f : S.LocalizationMap N) {g : M →* P} (hg : ∀ y : S, IsUnit (g y)) {T : Submonoid P}
  {Q : Type*} [CommMonoid Q]

/-- If `f : M →* N` and `k : M →* P` are Localization maps for a Submonoid `S`, we get an
isomorphism of `N` and `P`. -/
@[to_additive
/-- If `f : M →+ N` and `k : M →+ R` are Localization maps for an AddSubmonoid `S`, we get an
isomorphism of `N` and `R`. -/]
/-
**Submonoid.LocalizationMap.mulEquivOfLocalizations** 是 Mathlib 中的一个定义，位于命名空间 `S
ubmonoid.LocalizationMap`。
形式化陈述：mulEquivOfLocalizations (k : LocalizationMap S P) : N ≃* P
参数：k : LocalizationMap S P。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.LocalizationMap.map_units`：map_units (f : LocalizationMap S N)
 (y : S) : IsUnit (f y)
· 使用定理 `Submonoid.LocalizationMap.lift_left_inverse`：lift_left_inverse {k : Loca
lizationMap S P} (z : N) : k.lift f.map_units (f.lift k.map_units z) = z
-/
noncomputable def mulEquivOfLocalizations (k : LocalizationMap S P) : N ≃* P :=
{ toFun := f.lift k.map_units
  invFun := k.lift f.map_units
  left_inv := f.lift_left_inverse
  right_inv := k.lift_left_inverse
  map_mul' := map_mul _ }

@[to_additive (attr := simp)]
/-
**Submonoid.LocalizationMap.mulEquivOfLocalizations_apply** 是 Mathlib 中的一个定理，位于命
名空间 `Submonoid.LocalizationMap`。
形式化陈述：mulEquivOfLocalizations_apply {k : LocalizationMap S P} {x} : f.mulEquivOf
Localizations k x = f.lift k.map_units x
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mulEquivOfLocalizations_apply {k : LocalizationMap S P} {x} :
    f.mulEquivOfLocalizations k x = f.lift k.map_units x := rfl

@[to_additive (attr := simp)]
/-
**Submonoid.LocalizationMap.mulEquivOfLocalizations_symm_apply** 是 Mathlib 中的一个定
理，位于命名空间 `Submonoid.LocalizationMap`。
形式化陈述：mulEquivOfLocalizations_symm_apply {k : LocalizationMap S P} {x} : (f.mulE
quivOfLocalizations k).symm x = k.lift f.map_units x
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mulEquivOfLocalizations_symm_apply {k : LocalizationMap S P} {x} :
    (f.mulEquivOfLocalizations k).symm x = k.lift f.map_units x := rfl

@[to_additive]
/-
**Submonoid.LocalizationMap.mulEquivOfLocalizations_symm_eq_mulEquivOfLocalizati
ons** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid.LocalizationMap`。
形式化陈述：mulEquivOfLocalizations_symm_eq_mulEquivOfLocalizations {k : LocalizationM
ap S P} : (k.mulEquivOfLocalizations f).symm = f.mulEquivOfLocalizations k
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mulEquivOfLocalizations_symm_eq_mulEquivOfLocalizations {k : LocalizationMap S P} :
    (k.mulEquivOfLocalizations f).symm = f.mulEquivOfLocalizations k := rfl

/-- If `f : M →* N` is a Localization map for a Submonoid `S` and `k : N ≃* P` is an isomorphism
of `CommMonoid`s, `k ∘ f` is a Localization map for `M` at `S`. -/
@[to_additive
/-- If `f : M →+ N` is a Localization map for a Submonoid `S` and `k : N ≃+ P` is an isomorphism
of `AddCommMonoid`s, `k ∘ f` is a Localization map for `M` at `S`. -/]
/-
**Submonoid.LocalizationMap.ofMulEquivOfLocalizations** 是 Mathlib 中的一个定义，位于命名空间 
`Submonoid.LocalizationMap`。
形式化陈述：ofMulEquivOfLocalizations (k : N ≃* P) : LocalizationMap S P
参数：k : N ≃* P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def ofMulEquivOfLocalizations (k : N ≃* P) : LocalizationMap S P :=
  (k.toMonoidHom.comp f.toMonoidHom).toLocalizationMap (fun y ↦ isUnit_comp f k.toMonoidHom y)
    (fun v ↦
      let ⟨z, hz⟩ := k.surjective v
      let ⟨x, hx⟩ := f.surj z
      ⟨x, show v * k (f _) = k (f _) by rw [← hx, map_mul, ← hz]⟩)
    fun x y ↦ (k.apply_eq_iff_eq.trans f.eq_iff_exists).1

@[to_additive (attr := simp)]
/-
**Submonoid.LocalizationMap.ofMulEquivOfLocalizations_apply** 是 Mathlib 中的一个定理，位
于命名空间 `Submonoid.LocalizationMap`。
形式化陈述：ofMulEquivOfLocalizations_apply {k : N ≃* P} (x) : f.ofMulEquivOfLocalizat
ions k x = k (f x)
参数：x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofMulEquivOfLocalizations_apply {k : N ≃* P} (x) :
    f.ofMulEquivOfLocalizations k x = k (f x) := rfl

@[to_additive]
/-
**Submonoid.LocalizationMap.ofMulEquivOfLocalizations_eq** 是 Mathlib 中的一个定理，位于命名
空间 `Submonoid.LocalizationMap`。
形式化陈述：ofMulEquivOfLocalizations_eq {k : N ≃* P} : (f.ofMulEquivOfLocalizations k
).toMonoidHom = k.toMonoidHom.comp f.toMonoidHom
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofMulEquivOfLocalizations_eq {k : N ≃* P} :
    (f.ofMulEquivOfLocalizations k).toMonoidHom = k.toMonoidHom.comp f.toMonoidHom := rfl

@[to_additive]
/-
**Submonoid.LocalizationMap.symm_comp_ofMulEquivOfLocalizations_apply** 是 Mathli
b 中的一个定理，位于命名空间 `Submonoid.LocalizationMap`。
形式化陈述：symm_comp_ofMulEquivOfLocalizations_apply {k : N ≃* P} (x) : k.symm (f.ofM
ulEquivOfLocalizations k x) = f x
参数：x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulEquiv.symm_apply_apply`：symm_apply_apply (e : M ≃* N) (x : M) : e.sym
m (e x) = x
-/
theorem symm_comp_ofMulEquivOfLocalizations_apply {k : N ≃* P} (x) :
    k.symm (f.ofMulEquivOfLocalizations k x) = f x := k.symm_apply_apply (f x)

@[to_additive]
/-
**Submonoid.LocalizationMap.symm_comp_ofMulEquivOfLocalizations_apply'** 是 Mathl
ib 中的一个定理，位于命名空间 `Submonoid.LocalizationMap`。
形式化陈述：symm_comp_ofMulEquivOfLocalizations_apply' {k : P ≃* N} (x) : k (f.ofMulEq
uivOfLocalizations k.symm x) = f x
参数：x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulEquiv.apply_symm_apply`：apply_symm_apply (e : M ≃* N) (y : N) : e (e.
symm y) = y
-/
theorem symm_comp_ofMulEquivOfLocalizations_apply' {k : P ≃* N} (x) :
    k (f.ofMulEquivOfLocalizations k.symm x) = f x := k.apply_symm_apply (f x)

@[to_additive]
/-
**Submonoid.LocalizationMap.ofMulEquivOfLocalizations_eq_iff_eq** 是 Mathlib 中的一个
定理，位于命名空间 `Submonoid.LocalizationMap`。
形式化陈述：ofMulEquivOfLocalizations_eq_iff_eq {k : N ≃* P} {x y} : f.ofMulEquivOfLoc
alizations k x = y ↔ f x = k.symm y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.eq_symm_apply`：eq_symm_apply {α β} (e : α ≃ β) {x y} : y = e.symm 
x ↔ e y = x
-/
theorem ofMulEquivOfLocalizations_eq_iff_eq {k : N ≃* P} {x y} :
    f.ofMulEquivOfLocalizations k x = y ↔ f x = k.symm y :=
  k.toEquiv.eq_symm_apply.symm

@[to_additive addEquivOfLocalizations_right_inv]
/-
**Submonoid.LocalizationMap.mulEquivOfLocalizations_right_inv** 是 Mathlib 中的一个定理
，位于命名空间 `Submonoid.LocalizationMap`。
形式化陈述：mulEquivOfLocalizations_right_inv (k : LocalizationMap S P) : f.ofMulEquiv
OfLocalizations (f.mulEquivOfLocalizations k) = k
参数：k : LocalizationMap S P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.LocalizationMap.toMonoidHom_injective`：toMonoidHom_injective :
 Injective (toMonoidHom : LocalizationMap S N -> M ->* N)
· 使用定理 `Submonoid.LocalizationMap.lift_comp`：lift_comp : (f.lift hg).comp f.toMo
noidHom = g
· 使用定理 `Submonoid.LocalizationMap.map_units`：map_units (f : LocalizationMap S N)
 (y : S) : IsUnit (f y)
-/
theorem mulEquivOfLocalizations_right_inv (k : LocalizationMap S P) :
    f.ofMulEquivOfLocalizations (f.mulEquivOfLocalizations k) = k :=
  toMonoidHom_injective <| f.lift_comp k.map_units

@[to_additive addEquivOfLocalizations_right_inv_apply]
/-
**Submonoid.LocalizationMap.mulEquivOfLocalizations_right_inv_apply** 是 Mathlib 
中的一个定理，位于命名空间 `Submonoid.LocalizationMap`。
形式化陈述：mulEquivOfLocalizations_right_inv_apply {k : LocalizationMap S P} {x} : f.
ofMulEquivOfLocalizations (f.mulEquivOfLocalizations k) x = k x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submonoid.LocalizationMap.lift_eq`：lift_eq (x : M) : f.lift hg (f x) = g
 x
· 使用定理 `Submonoid.LocalizationMap.map_units`：map_units (f : LocalizationMap S N)
 (y : S) : IsUnit (f y)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mulEquivOfLocalizations_right_inv_apply {k : LocalizationMap S P} {x} :
    f.ofMulEquivOfLocalizations (f.mulEquivOfLocalizations k) x = k x := by simp

@[to_additive (attr := simp)]
/-
**Submonoid.LocalizationMap.mulEquivOfLocalizations_left_inv** 是 Mathlib 中的一个定理，
位于命名空间 `Submonoid.LocalizationMap`。
形式化陈述：mulEquivOfLocalizations_left_inv (k : N ≃* P) : f.mulEquivOfLocalizations 
(f.ofMulEquivOfLocalizations k) = k
参数：k : N ≃* P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submonoid.LocalizationMap.isUnit_comp`：isUnit_comp (j : N ->* P) (y : S)
 : IsUnit (j.comp f.toMonoidHom y)
· 使用定理 `DFunLike.ext_iff`：ext_iff {f g : F} : f = g ↔ forall x, f x = g x
· 使用定理 `Submonoid.LocalizationMap.lift_of_comp`：lift_of_comp (j : N ->* P) : f.l
ift (f.isUnit_comp j) = j
-/
theorem mulEquivOfLocalizations_left_inv (k : N ≃* P) :
    f.mulEquivOfLocalizations (f.ofMulEquivOfLocalizations k) = k :=
  DFunLike.ext _ _ fun x ↦ DFunLike.ext_iff.1 (f.lift_of_comp k.toMonoidHom) x

@[to_additive]
/-
**Submonoid.LocalizationMap.mulEquivOfLocalizations_left_inv_apply** 是 Mathlib 中
的一个定理，位于命名空间 `Submonoid.LocalizationMap`。
形式化陈述：mulEquivOfLocalizations_left_inv_apply {k : N ≃* P} (x) : f.mulEquivOfLoca
lizations (f.ofMulEquivOfLocalizations k) x = k x
参数：x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submonoid.LocalizationMap.mulEquivOfLocalizations_left_inv`：mulEquivOfLo
calizations_left_inv (k : N ≃* P) : f.mulEquivOfLocalizations (f.ofMulEquivOfLoc
alizations k) = k
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mulEquivOfLocalizations_left_inv_apply {k : N ≃* P} (x) :
    f.mulEquivOfLocalizations (f.ofMulEquivOfLocalizations k) x = k x := by simp

@[to_additive (attr := simp)]
/-
**Submonoid.LocalizationMap.ofMulEquivOfLocalizations_id** 是 Mathlib 中的一个定理，位于命名
空间 `Submonoid.LocalizationMap`。
形式化陈述：ofMulEquivOfLocalizations_id : f.ofMulEquivOfLocalizations (MulEquiv.refl 
N) = f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.LocalizationMap.ext`：ext {f g : LocalizationMap S N} (h : fora
ll x, f x = g x) : f = g
-/
theorem ofMulEquivOfLocalizations_id : f.ofMulEquivOfLocalizations (MulEquiv.refl N) = f := by
  ext; rfl

@[to_additive]
/-
**Submonoid.LocalizationMap.ofMulEquivOfLocalizations_comp** 是 Mathlib 中的一个定理，位于
命名空间 `Submonoid.LocalizationMap`。
形式化陈述：ofMulEquivOfLocalizations_comp {k : N ≃* P} {j : P ≃* Q} : (f.ofMulEquivOf
Localizations (k.trans j)).toMonoidHom = j.toMonoidHom.comp (f.ofMulEquivOfLocal
izations k).toMonoidHom
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.ext`：MonoidHom.ext [MulOne M] [MulOne N] ⦃f g : M ->* N⦄ (h : 
forall x, f x = g x) : f = g
-/
theorem ofMulEquivOfLocalizations_comp {k : N ≃* P} {j : P ≃* Q} :
    (f.ofMulEquivOfLocalizations (k.trans j)).toMonoidHom =
      j.toMonoidHom.comp (f.ofMulEquivOfLocalizations k).toMonoidHom := by
  ext; rfl

/-- Given `CommMonoid`s `M, P` and Submonoids `S ⊆ M, T ⊆ P`, if `f : M →* N` is a Localization
map for `S` and `k : P ≃* M` is an isomorphism of `CommMonoid`s such that `k(T) = S`, `f ∘ k`
is a Localization map for `T`. -/
@[to_additive
/-- Given `AddCommMonoid`s `M, P` and `AddSubmonoid`s `S ⊆ M, T ⊆ P`, if `f : M →* N` is a
Localization map for `S` and `k : P ≃+ M` is an isomorphism of `AddCommMonoid`s such that
`k(T) = S`, `f ∘ k` is a Localization map for `T`. -/]
/-
**Submonoid.LocalizationMap.ofMulEquivOfDom** 是 Mathlib 中的一个定义，位于命名空间 `Submonoid
.LocalizationMap`。
形式化陈述：ofMulEquivOfDom {k : P ≃* M} (H : T.map k.toMonoidHom = S) : LocalizationM
ap T N
参数：H : T.map k.toMonoidHom = S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def ofMulEquivOfDom {k : P ≃* M} (H : T.map k.toMonoidHom = S) : LocalizationMap T N :=
  have H' : S.comap k.toMonoidHom = T :=
    H ▸ (SetLike.coe_injective <| T.1.1.preimage_image_eq k.toEquiv.injective)
  (f.toMonoidHom.comp k.toMonoidHom).toLocalizationMap
    (fun y ↦
      let ⟨z, hz⟩ := f.map_units ⟨k y, H ▸ Set.mem_image_of_mem k y.2⟩
      ⟨z, hz⟩)
    (fun z ↦
      let ⟨x, hx⟩ := f.surj z
      let ⟨v, hv⟩ := k.surjective x.1
      let ⟨w, hw⟩ := k.surjective x.2
      ⟨(v, ⟨w, H' ▸ show k w ∈ S from hw.symm ▸ x.2.2⟩), by
        simp_rw [MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, hv, hw]
        dsimp
        rw [hx]⟩)
    fun x y ↦ by
      rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe,
        MonoidHom.coe_coe, toMonoidHom_apply, toMonoidHom_apply, f.eq_iff_exists]
      rintro ⟨c, hc⟩
      let ⟨d, hd⟩ := k.surjective c
      refine ⟨⟨d, H' ▸ show k d ∈ S from hd.symm ▸ c.2⟩, ?_⟩
      rw [← hd, ← map_mul k, ← map_mul k] at hc; exact k.injective hc

@[to_additive (attr := simp)]
/-
**Submonoid.LocalizationMap.ofMulEquivOfDom_apply** 是 Mathlib 中的一个定理，位于命名空间 `Sub
monoid.LocalizationMap`。
形式化陈述：ofMulEquivOfDom_apply {k : P ≃* M} (H : T.map k.toMonoidHom = S) (x) : f.o
fMulEquivOfDom H x = f (k x)
参数：H : T.map k.toMonoidHom = S；x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofMulEquivOfDom_apply {k : P ≃* M} (H : T.map k.toMonoidHom = S) (x) :
    f.ofMulEquivOfDom H x = f (k x) := rfl

@[to_additive]
/-
**Submonoid.LocalizationMap.ofMulEquivOfDom_eq** 是 Mathlib 中的一个定理，位于命名空间 `Submon
oid.LocalizationMap`。
形式化陈述：ofMulEquivOfDom_eq {k : P ≃* M} (H : T.map k.toMonoidHom = S) : (f.ofMulEq
uivOfDom H).toMonoidHom = f.toMonoidHom.comp k.toMonoidHom
参数：H : T.map k.toMonoidHom = S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofMulEquivOfDom_eq {k : P ≃* M} (H : T.map k.toMonoidHom = S) :
    (f.ofMulEquivOfDom H).toMonoidHom = f.toMonoidHom.comp k.toMonoidHom := rfl

@[to_additive]
/-
**Submonoid.LocalizationMap.ofMulEquivOfDom_comp_symm** 是 Mathlib 中的一个定理，位于命名空间 
`Submonoid.LocalizationMap`。
形式化陈述：ofMulEquivOfDom_comp_symm {k : P ≃* M} (H : T.map k.toMonoidHom = S) (x) :
 f.ofMulEquivOfDom H (k.symm x) = f x
参数：H : T.map k.toMonoidHom = S；x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `MulEquiv.apply_symm_apply`：apply_symm_apply (e : M ≃* N) (y : N) : e (e.
symm y) = y
-/
theorem ofMulEquivOfDom_comp_symm {k : P ≃* M} (H : T.map k.toMonoidHom = S) (x) :
    f.ofMulEquivOfDom H (k.symm x) = f x :=
  congr_arg f <| k.apply_symm_apply x

@[to_additive]
/-
**Submonoid.LocalizationMap.ofMulEquivOfDom_comp** 是 Mathlib 中的一个定理，位于命名空间 `Subm
onoid.LocalizationMap`。
形式化陈述：ofMulEquivOfDom_comp {k : M ≃* P} (H : T.map k.symm.toMonoidHom = S) (x) :
 f.ofMulEquivOfDom H (k x) = f x
参数：H : T.map k.symm.toMonoidHom = S；x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `MulEquiv.symm_apply_apply`：symm_apply_apply (e : M ≃* N) (x : M) : e.sym
m (e x) = x
-/
theorem ofMulEquivOfDom_comp {k : M ≃* P} (H : T.map k.symm.toMonoidHom = S) (x) :
    f.ofMulEquivOfDom H (k x) = f x := congr_arg f <| k.symm_apply_apply x

/-- A special case of `f ∘ id = f`, `f` a Localization map. -/
@[to_additive (attr := simp) /-- A special case of `f ∘ id = f`, `f` a Localization map. -/]
/-
**Submonoid.LocalizationMap.ofMulEquivOfDom_id** 是 Mathlib 中的一个定理，位于命名空间 `Submon
oid.LocalizationMap`。
形式化陈述：ofMulEquivOfDom_id : f.ofMulEquivOfDom (show S.map (MulEquiv.refl M).toMon
oidHom = S from Submonoid.ext fun x => ⟨fun ⟨_, hy, h⟩ => h ▸ hy, fun h => ⟨x, h
, rfl⟩⟩) = f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.LocalizationMap.ext`：ext {f g : LocalizationMap S N} (h : fora
ll x, f x = g x) : f = g
· 使用定理 `Submonoid.ext`：ext {S T : Submonoid M} (h : forall x, x in S ↔ x in T) :
 S = T

--- 原说明 ---
A special case of `f ∘ id = f`, `f` a Localization map.
-/
theorem ofMulEquivOfDom_id :
    f.ofMulEquivOfDom
        (show S.map (MulEquiv.refl M).toMonoidHom = S from
          Submonoid.ext fun x ↦ ⟨fun ⟨_, hy, h⟩ ↦ h ▸ hy, fun h ↦ ⟨x, h, rfl⟩⟩) = f := by
  ext; rfl

/-- Given Localization maps `f : M →* N, k : P →* U` for Submonoids `S, T` respectively, an
isomorphism `j : M ≃* P` such that `j(S) = T` induces an isomorphism of localizations `N ≃* U`. -/
@[to_additive
/-- Given Localization maps `f : M →+ N, k : P →+ U` for Submonoids `S, T` respectively, an
isomorphism `j : M ≃+ P` such that `j(S) = T` induces an isomorphism of localizations `N ≃+ U`. -/]
/-
**Submonoid.LocalizationMap.mulEquivOfMulEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Submon
oid.LocalizationMap`。
形式化陈述：mulEquivOfMulEquiv (k : LocalizationMap T Q) {j : M ≃* P} (H : S.map j.toM
onoidHom = T) : N ≃* Q
参数：k : LocalizationMap T Q；H : S.map j.toMonoidHom = T。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def mulEquivOfMulEquiv (k : LocalizationMap T Q) {j : M ≃* P}
    (H : S.map j.toMonoidHom = T) : N ≃* Q :=
  f.mulEquivOfLocalizations <| k.ofMulEquivOfDom H

@[to_additive (attr := simp)]
/-
**Submonoid.LocalizationMap.mulEquivOfMulEquiv_eq_map_apply** 是 Mathlib 中的一个定理，位
于命名空间 `Submonoid.LocalizationMap`。
形式化陈述：mulEquivOfMulEquiv_eq_map_apply {k : LocalizationMap T Q} {j : M ≃* P} (H 
: S.map j.toMonoidHom = T) (x) : f.mulEquivOfMulEquiv k H x = f.map (fun y : S =
> show j.toMonoidHom y in T from H ▸ Set.mem_image_of_mem j y.2) k x
参数：H : S.map j.toMonoidHom = T；x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mulEquivOfMulEquiv_eq_map_apply {k : LocalizationMap T Q} {j : M ≃* P}
    (H : S.map j.toMonoidHom = T) (x) :
    f.mulEquivOfMulEquiv k H x =
      f.map (fun y : S ↦ show j.toMonoidHom y ∈ T from H ▸ Set.mem_image_of_mem j y.2) k x := rfl

@[to_additive]
/-
**Submonoid.LocalizationMap.mulEquivOfMulEquiv_eq_map** 是 Mathlib 中的一个定理，位于命名空间 
`Submonoid.LocalizationMap`。
形式化陈述：mulEquivOfMulEquiv_eq_map {k : LocalizationMap T Q} {j : M ≃* P} (H : S.ma
p j.toMonoidHom = T) : (f.mulEquivOfMulEquiv k H).toMonoidHom = f.map (fun y : S
 => show j.toMonoidHom y in T from H ▸ Set.mem_image_of_mem j y.2) k
参数：H : S.map j.toMonoidHom = T。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mulEquivOfMulEquiv_eq_map {k : LocalizationMap T Q} {j : M ≃* P}
    (H : S.map j.toMonoidHom = T) :
    (f.mulEquivOfMulEquiv k H).toMonoidHom =
      f.map (fun y : S ↦ show j.toMonoidHom y ∈ T from H ▸ Set.mem_image_of_mem j y.2) k := rfl

@[to_additive]
/-
**Submonoid.LocalizationMap.mulEquivOfMulEquiv_eq** 是 Mathlib 中的一个定理，位于命名空间 `Sub
monoid.LocalizationMap`。
形式化陈述：mulEquivOfMulEquiv_eq {k : LocalizationMap T Q} {j : M ≃* P} (H : S.map j.
toMonoidHom = T) (x) : f.mulEquivOfMulEquiv k H (f x) = k (j x)
参数：H : S.map j.toMonoidHom = T；x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.LocalizationMap.map_eq`：map_eq (x) : f.map hy k (f x) = k (g x
)
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem mulEquivOfMulEquiv_eq {k : LocalizationMap T Q} {j : M ≃* P} (H : S.map j.toMonoidHom = T)
    (x) :
    f.mulEquivOfMulEquiv k H (f x) = k (j x) :=
  f.map_eq (fun y : S ↦ H ▸ Set.mem_image_of_mem j y.2) _

@[to_additive]
/-
**Submonoid.LocalizationMap.mulEquivOfMulEquiv_mk'** 是 Mathlib 中的一个定理，位于命名空间 `Su
bmonoid.LocalizationMap`。
形式化陈述：mulEquivOfMulEquiv_mk' {k : LocalizationMap T Q} {j : M ≃* P} (H : S.map j
.toMonoidHom = T) (x y) : f.mulEquivOfMulEquiv k H (f.mk' x y) = k.mk' (j x) ⟨j 
y, H ▸ Set.mem_image_of_mem j y.2⟩
参数：H : S.map j.toMonoidHom = T；x y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.LocalizationMap.map_mk'`：map_mk' (x) (y : S) : f.map hy k (f.m
k' x y) = k.mk' (g x) ⟨g y, hy y⟩
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem mulEquivOfMulEquiv_mk' {k : LocalizationMap T Q} {j : M ≃* P} (H : S.map j.toMonoidHom = T)
    (x y) :
    f.mulEquivOfMulEquiv k H (f.mk' x y) = k.mk' (j x) ⟨j y, H ▸ Set.mem_image_of_mem j y.2⟩ :=
  f.map_mk' (fun y : S ↦ H ▸ Set.mem_image_of_mem j y.2) _ _

@[to_additive]
/-
**Submonoid.LocalizationMap.of_mulEquivOfMulEquiv_apply** 是 Mathlib 中的一个定理，位于命名空
间 `Submonoid.LocalizationMap`。
形式化陈述：of_mulEquivOfMulEquiv_apply {k : LocalizationMap T Q} {j : M ≃* P} (H : S.
map j.toMonoidHom = T) (x) : f.ofMulEquivOfLocalizations (f.mulEquivOfMulEquiv k
 H) x = k (j x)
参数：H : S.map j.toMonoidHom = T；x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submonoid.LocalizationMap.ext_iff`：∀ {M : Type u_1} [inst : CommMonoid M
] {S : Submonoid M} {N : Type u_2} [inst_1 : CommMonoid N]   {f g : S.Localizati
onMap N}, f = g ↔ ∀ (x …
· 使用定理 `Submonoid.LocalizationMap.mulEquivOfLocalizations_right_inv`：mulEquivOfL
ocalizations_right_inv (k : LocalizationMap S P) : f.ofMulEquivOfLocalizations (
f.mulEquivOfLocalizations k) = k
-/
theorem of_mulEquivOfMulEquiv_apply {k : LocalizationMap T Q} {j : M ≃* P}
    (H : S.map j.toMonoidHom = T) (x) :
    f.ofMulEquivOfLocalizations (f.mulEquivOfMulEquiv k H) x = k (j x) :=
  Submonoid.LocalizationMap.ext_iff.1 (f.mulEquivOfLocalizations_right_inv (k.ofMulEquivOfDom H)) x

@[to_additive]
/-
**Submonoid.LocalizationMap.of_mulEquivOfMulEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Sub
monoid.LocalizationMap`。
形式化陈述：of_mulEquivOfMulEquiv {k : LocalizationMap T Q} {j : M ≃* P} (H : S.map j.
toMonoidHom = T) : (f.ofMulEquivOfLocalizations (f.mulEquivOfMulEquiv k H)).toMo
noidHom = k.toMonoidHom.comp j.toMonoidHom
参数：H : S.map j.toMonoidHom = T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.ext`：MonoidHom.ext [MulOne M] [MulOne N] ⦃f g : M ->* N⦄ (h : 
forall x, f x = g x) : f = g
· 使用定理 `Submonoid.LocalizationMap.of_mulEquivOfMulEquiv_apply`：of_mulEquivOfMulE
quiv_apply {k : LocalizationMap T Q} {j : M ≃* P} (H : S.map j.toMonoidHom = T) 
(x) : f.ofMulEquivOfLocalizations (f.mulEqu…
-/
theorem of_mulEquivOfMulEquiv {k : LocalizationMap T Q} {j : M ≃* P} (H : S.map j.toMonoidHom = T) :
    (f.ofMulEquivOfLocalizations (f.mulEquivOfMulEquiv k H)).toMonoidHom =
      k.toMonoidHom.comp j.toMonoidHom :=
  MonoidHom.ext <| f.of_mulEquivOfMulEquiv_apply H

end LocalizationMap

end Submonoid

namespace Localization

variable (f : Submonoid.LocalizationMap S N)

/-- Given a Localization map `f : M →* N` for a Submonoid `S`, we get an isomorphism between
the Localization of `M` at `S` as a quotient type and `N`. -/
@[to_additive
/-- Given a Localization map `f : M →+ N` for a Submonoid `S`, we get an isomorphism between
the Localization of `M` at `S` as a quotient type and `N`. -/]
/-
**Localization.mulEquivOfQuotient** 是 Mathlib 中的一个定义，位于命名空间 `Localization`。
形式化陈述：mulEquivOfQuotient (f : Submonoid.LocalizationMap S N) : Localization S ≃*
 N
参数：f : Submonoid.LocalizationMap S N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def mulEquivOfQuotient (f : Submonoid.LocalizationMap S N) : Localization S ≃* N :=
  (monoidOf S).mulEquivOfLocalizations f

variable {f}

@[to_additive (attr := simp)]
/-
**Localization.mulEquivOfQuotient_apply** 是 Mathlib 中的一个定理，位于命名空间 `Localization`
。
形式化陈述：mulEquivOfQuotient_apply (x) : mulEquivOfQuotient f x = (monoidOf S).lift 
f.map_units x
参数：x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mulEquivOfQuotient_apply (x) : mulEquivOfQuotient f x = (monoidOf S).lift f.map_units x :=
  rfl

@[to_additive]
/-
**Localization.mulEquivOfQuotient_mk'** 是 Mathlib 中的一个定理，位于命名空间 `Localization`。
形式化陈述：mulEquivOfQuotient_mk' (x y) : mulEquivOfQuotient f ((monoidOf S).mk' x y)
 = f.mk' x y
参数：x y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.LocalizationMap.lift_mk'`：lift_mk' (x y) : f.lift hg (f.mk' x 
y) = g x * (IsUnit.liftRight (g.domRestrict S) hg y)⁻¹
· 使用定理 `Submonoid.LocalizationMap.map_units`：map_units (f : LocalizationMap S N)
 (y : S) : IsUnit (f y)
-/
theorem mulEquivOfQuotient_mk' (x y) : mulEquivOfQuotient f ((monoidOf S).mk' x y) = f.mk' x y :=
  (monoidOf S).lift_mk' _ _ _

@[to_additive]
/-
**Localization.mulEquivOfQuotient_mk** 是 Mathlib 中的一个定理，位于命名空间 `Localization`。
形式化陈述：mulEquivOfQuotient_mk (x y) : mulEquivOfQuotient f (mk x y) = f.mk' x y
参数：x y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Localization.mk_eq_monoidOf_mk'_apply`：∀ {M : Type u_1} [inst : CommMono
id M] {S : Submonoid M} (x : M) (y : ↥S),   Localization.mk x y = (Localization.
monoidOf S).mk' x y
· 使用定理 `Localization.mulEquivOfQuotient_mk'`：mulEquivOfQuotient_mk' (x y) : mulE
quivOfQuotient f ((monoidOf S).mk' x y) = f.mk' x y
-/
theorem mulEquivOfQuotient_mk (x y) : mulEquivOfQuotient f (mk x y) = f.mk' x y := by
  rw [mk_eq_monoidOf_mk'_apply]; exact mulEquivOfQuotient_mk' _ _

@[to_additive]
/-
**Localization.mulEquivOfQuotient_monoidOf** 是 Mathlib 中的一个定理，位于命名空间 `Localizati
on`。
形式化陈述：mulEquivOfQuotient_monoidOf (x) : mulEquivOfQuotient f (monoidOf S x) = f 
x
参数：x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submonoid.LocalizationMap.lift_eq`：lift_eq (x : M) : f.lift hg (f x) = g
 x
· 使用定理 `Submonoid.LocalizationMap.map_units`：map_units (f : LocalizationMap S N)
 (y : S) : IsUnit (f y)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mulEquivOfQuotient_monoidOf (x) : mulEquivOfQuotient f (monoidOf S x) = f x := by simp

@[to_additive (attr := simp)]
/-
**Localization.mulEquivOfQuotient_symm_mk'** 是 Mathlib 中的一个定理，位于命名空间 `Localizati
on`。
形式化陈述：mulEquivOfQuotient_symm_mk' (x y) : (mulEquivOfQuotient f).symm (f.mk' x y
) = (monoidOf S).mk' x y
参数：x y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.LocalizationMap.lift_mk'`：lift_mk' (x y) : f.lift hg (f.mk' x 
y) = g x * (IsUnit.liftRight (g.domRestrict S) hg y)⁻¹
· 使用定理 `Submonoid.LocalizationMap.map_units`：map_units (f : LocalizationMap S N)
 (y : S) : IsUnit (f y)
-/
theorem mulEquivOfQuotient_symm_mk' (x y) :
    (mulEquivOfQuotient f).symm (f.mk' x y) = (monoidOf S).mk' x y :=
  f.lift_mk' (monoidOf S).map_units _ _

@[to_additive]
/-
**Localization.mulEquivOfQuotient_symm_mk** 是 Mathlib 中的一个定理，位于命名空间 `Localizatio
n`。
形式化陈述：mulEquivOfQuotient_symm_mk (x y) : (mulEquivOfQuotient f).symm (f.mk' x y)
 = mk x y
参数：x y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Localization.mk_eq_monoidOf_mk'_apply`：∀ {M : Type u_1} [inst : CommMono
id M] {S : Submonoid M} (x : M) (y : ↥S),   Localization.mk x y = (Localization.
monoidOf S).mk' x y
· 使用定理 `Localization.mulEquivOfQuotient_symm_mk'`：mulEquivOfQuotient_symm_mk' (x
 y) : (mulEquivOfQuotient f).symm (f.mk' x y) = (monoidOf S).mk' x y
-/
theorem mulEquivOfQuotient_symm_mk (x y) : (mulEquivOfQuotient f).symm (f.mk' x y) = mk x y := by
  rw [mk_eq_monoidOf_mk'_apply]; exact mulEquivOfQuotient_symm_mk' _ _

@[to_additive (attr := simp)]
/-
**Localization.mulEquivOfQuotient_symm_monoidOf** 是 Mathlib 中的一个定理，位于命名空间 `Local
ization`。
形式化陈述：mulEquivOfQuotient_symm_monoidOf (x) : (mulEquivOfQuotient f).symm (f x) =
 monoidOf S x
参数：x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.LocalizationMap.lift_eq`：lift_eq (x : M) : f.lift hg (f x) = g
 x
· 使用定理 `Submonoid.LocalizationMap.map_units`：map_units (f : LocalizationMap S N)
 (y : S) : IsUnit (f y)
-/
theorem mulEquivOfQuotient_symm_monoidOf (x) : (mulEquivOfQuotient f).symm (f x) = monoidOf S x :=
  f.lift_eq (monoidOf S).map_units _

end Localization

end CommMonoid

