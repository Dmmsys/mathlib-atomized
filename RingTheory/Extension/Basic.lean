/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.Localization.Defs

/-!

# Extension of algebras

## Main definitions

- `Algebra.Extension`: An extension of an `R`-algebra `S` is an `R` algebra `P` together with a
  surjection `P →ₐ[R] R`.

- `Algebra.Extension.Hom`: Given a commuting square
  ```
  R --→ P -→ S
  | |
  ↓ ↓
  R' -→ P' → S
  ```
  A hom between `P` and `P'` is a ring homomorphism that makes the two squares commute.

- `Algebra.Extension.Cotangent`:
  The cotangent space w.r.t. an extension `P → S` by `I`, i.e. the space `I/I²`.

-/

@[expose] public section

universe w u v

open TensorProduct MvPolynomial

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]

/--
Definition of `Algebra.Extension` / `Algebra.Extension` 的定义

English:
structure Algebra.Extension
  parameters: where
  axioms and operations (7):
    - Ring : Type w
    - [commRing : CommRing Ring]
    - [algebra₁ : Algebra R Ring]
    - [algebra₂ : Algebra Ring S]
    - [isScalarTower : IsScalarTower R Ring S]
    - σ : S -> Ring
    - algebraMap_σ : forall x, algebraMap Ring S (σ x) = x

中文:
结构 代数.扩张
  参数: where
  公理与运算 (7 个):
    - Ring : 类型 w
    - [commRing : 交换环 环]
    - [algebra₁ : 代数 R 环]
    - [algebra₂ : 代数 环 S]
    - [isScalarTower : 标量塔 R 环 S]
    - σ : S -> 环
    - algebraMap_σ : 对任意 x, algebraMap 环 S (σ x) = x
-/
structure Algebra.Extension where
  /-- The underlying algebra of an extension. -/
  Ring : Type w
  [commRing : CommRing Ring]
  [algebra₁ : Algebra R Ring]
  [algebra₂ : Algebra Ring S]
  [isScalarTower : IsScalarTower R Ring S]
  /-- A chosen (set-theoretic) section of an extension. -/
  σ : S -> Ring
  algebraMap_σ : forall x, algebraMap Ring S (σ x) = x

namespace Algebra.Extension

variable {R S}
variable (P : Extension.{w} R S)

attribute [instance] commRing algebra₁ algebra₂ isScalarTower

attribute [simp] algebraMap_σ

-- We want to make sure `R₀` acts compatibly on `R` and `S` to avoid nonsensical instances
@[nolint unusedArguments]
noncomputable instance {R₀} [CommRing R₀] [Algebra R₀ R] [Algebra R₀ S] [IsScalarTower R₀ R S] :
    Algebra R₀ P.Ring := Algebra.compHom P.Ring (algebraMap R₀ R)

instance {R₀} [CommRing R₀] [Algebra R₀ R] [Algebra R₀ S] [IsScalarTower R₀ R S] :
    IsScalarTower R₀ R P.Ring := IsScalarTower.of_algebraMap_eq' rfl

instance {R₀} [CommRing R₀] [Algebra R₀ R] [Algebra R₀ S] [IsScalarTower R₀ R S]
    {R₁} [CommRing R₁] [Algebra R₁ R] [Algebra R₁ S] [IsScalarTower R₁ R S]
    [Algebra R₀ R₁] [IsScalarTower R₀ R₁ R] :
IsScalarTower R₀ R₁ P.Ring := IsScalarTower.of_algebraMap_eq' by
  rw [IsScalarTower.algebraMap_eq R₀ R]; rw [IsScalarTower.algebraMap_eq R₁ R]; rw [RingHom.comp_assoc]; rw [← IsScalarTower.algebraMap_eq R₀ R₁ R]

instance {R₀} [CommRing R₀] [Algebra R₀ R] [Algebra R₀ S] [IsScalarTower R₀ R S] :
IsScalarTower R₀ P.Ring S := IsScalarTower.of_algebraMap_eq' by
  rw [IsScalarTower.algebraMap_eq R₀ R P.Ring]; rw [← RingHom.comp_assoc]; rw [← IsScalarTower.algebraMap_eq]; rw [← IsScalarTower.algebraMap_eq]

@[simp]
/--
lemma `σ_smul` / 引理 `σ_smul`

English:
lemma σ_smul
  given: (x y)
  statement: P.σ x • y = x * y
  proof: by
  rw [Algebra.smul_def]; rw [algebraMap_σ]

中文:
引理 σ_smul
  条件: (x y)
  结论: P.σ x • y = x * y
  证明: by
  rw [Algebra.smul_def]; rw [algebraMap_σ]

Depends on / 依赖: Algebra, Algebra.smul_def, smul_def
-/
lemma σ_smul (x y) : P.σ x • y = x * y := by
  rw [Algebra.smul_def]; rw [algebraMap_σ]

/--
lemma `σ_injective` / 引理 `σ_injective`

English:
lemma σ_injective
  statement: P.σ.Injective
  proof: by
  intro x y e
  rw [← P.algebraMap_σ x]; rw [← P.algebraMap_σ y]; rw [e]

中文:
引理 σ_injective
  结论: P.σ.单射
  证明: by
  intro x y e
  rw [← P.algebraMap_σ x]; rw [← P.algebraMap_σ y]; rw [e]

Depends on / 依赖: P.algebraMap_
-/
lemma σ_injective : P.σ.Injective := by
  intro x y e
  rw [← P.algebraMap_σ x]; rw [← P.algebraMap_σ y]; rw [e]

/--
lemma `algebraMap_surjective` / 引理 `algebraMap_surjective`

English:
lemma algebraMap_surjective
  statement: Function.Surjective (algebraMap P.Ring S)
  proof: (⟨_, P.algebraMap_σ ·⟩)

中文:
引理 algebraMap_surjective
  结论: 函数.满射 (algebraMap P.环 S)
  证明: (⟨_, P.algebraMap_σ ·⟩)

Depends on / 依赖: P.algebraMap_
-/
lemma algebraMap_surjective : Function.Surjective (algebraMap P.Ring S) := (⟨_, P.algebraMap_σ ·⟩)

section Construction

/-- Construct `Extension` from a surjective algebra homomorphism. -/
@[simps -isSimp Ring σ]
noncomputable
/--
Definition of `ofSurjective` / `ofSurjective` 的定义

English:
definition ofSurjective
  signature: {P : Type w} [CommRing P] [Algebra R P] (f : P ->ₐ[R] S)
  body: P
  algebra₂ := f.toAlgebra
  isScalarTower := letI := f.toAlgebra; IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  σ x := (h x).choose
  algebraMap_σ x := (h x).choose_spec

中文:
定义 ofSurjective
  签名: {P : 类型 w} [交换环 P] [代数 R P] (f : P ->ₐ[R] S)
  定义体: P
  algebra₂ := f.toAlgebra
  isScalarTower := letI := f.toAlgebra; IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  σ x := (h x).choose
  algebraMap_σ x := (h x).choose_spec
-/
def ofSurjective {P : Type w} [CommRing P] [Algebra R P] (f : P ->ₐ[R] S)
    (h : Function.Surjective f) : Extension.{w} R S where
  Ring := P
  algebra₂ := f.toAlgebra
  isScalarTower := letI := f.toAlgebra; IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  σ x := (h x).choose
  algebraMap_σ x := (h x).choose_spec

variable (R S) in
/-- The trivial extension of `S`. -/
@[simps -isSimp Ring σ]
noncomputable
/--
Definition of `self` / `self` 的定义

English:
definition self
  signature: : Extension R S where
  body: S
  σ := _root_.id
  algebraMap_σ _ := rfl

中文:
定义 self
  签名: : 扩张 R S where
  定义体: S
  σ := _root_.id
  algebraMap_σ _ := rfl
-/
def self : Extension R S where
  Ring := S
  σ := _root_.id
  algebraMap_σ _ := rfl

/--
Definition of `ker` / `ker` 的定义

English:
abbreviation ker
  signature: : Ideal P.Ring
  body: RingHom.ker (algebraMap P.Ring S)

中文:
缩写 ker
  签名: : 理想 P.环
  定义体: RingHom.ker (algebraMap P.Ring S)

Depends on / 依赖: P.Ring, RingHom, RingHom.ker, algebraMap
-/
abbrev ker : Ideal P.Ring := RingHom.ker (algebraMap P.Ring S)

section Localization

variable (M : Submonoid S) {S' : Type*} [CommRing S'] [Algebra S S'] [IsLocalization M S']
variable [Algebra R S'] [IsScalarTower R S S']

/--
An `R`-extension `P → S` gives an `R`-extension `Pₘ → Sₘ`.
Note that this is different from `baseChange` as the base does not change.
-/
noncomputable
/--
Definition of `localization` / `localization` 的定义

English:
definition localization
  signature: (P : Extension.{w} R S)
  body: Localization (M.comap (algebraMap P.Ring S))
  algebra₂ := (IsLocalization.lift (M := (M.comap (algebraMap P.Ring S)))
      (g := (algebraMap S S').comp (algebraMap P.Ring S))
      (by simpa using fun x hx => IsLocalization.map_units S' ⟨_, hx⟩)).toAlgebra
  isScalarTower := by
    let : Algebra (

中文:
定义 localization
  签名: (P : 扩张.{w} R S)
  定义体: Localization (M.comap (algebraMap P.Ring S))
  algebra₂ := (IsLocalization.lift (M := (M.comap (algebraMap P.Ring S)))
      (g := (algebraMap S S').comp (algebraMap P.Ring S))
      (by simpa using fun x hx => IsLocalization.map_units S' ⟨_, hx⟩)).toAlgebra
  isScalarTower := by
    let : Algebra (

Depends on / 依赖: Localization, M.comap, P.Ring, algebraMap
-/
def localization (P : Extension.{w} R S) : Extension R S' where
  Ring := Localization (M.comap (algebraMap P.Ring S))
  algebra₂ := (IsLocalization.lift (M := (M.comap (algebraMap P.Ring S)))
      (g := (algebraMap S S').comp (algebraMap P.Ring S))
      (by simpa using fun x hx => IsLocalization.map_units S' ⟨_, hx⟩)).toAlgebra
  isScalarTower := by
    let : Algebra (Localization (M.comap (algebraMap P.Ring S))) S' :=
      (IsLocalization.lift (M := (M.comap (algebraMap P.Ring S)))
        (g := (algebraMap S S').comp (algebraMap P.Ring S))
        (by simpa using fun x hx => IsLocalization.map_units S' ⟨_, hx⟩)).toAlgebra
    apply IsScalarTower.of_algebraMap_eq'
    rw [RingHom.algebraMap_toAlgebra]; rw [IsScalarTower.algebraMap_eq R P.Ring (Localization _)]; rw [← RingHom.comp_assoc]; rw [IsLocalization.lift_comp]; rw [RingHom.comp_assoc]; rw [← IsScalarTower.algebraMap_eq]; rw [← IsScalarTower.algebraMap_eq]
  σ s := Localization.mk (P.σ (IsLocalization.sec M s).1) ⟨P.σ (IsLocalization.sec M s).2, by simp⟩
  algebraMap_σ s := by
    simp [RingHom.algebraMap_toAlgebra, Localization.mk_eq_mk', IsLocalization.lift_mk',
      Units.mul_inv_eq_iff_eq_mul, IsUnit.coe_liftRight, IsLocalization.sec_spec]

end Localization

variable {T} [CommRing T] [Algebra R T]

/-- The base change of an `R`-extension of `S` to `T` gives a `T`-extension of `T ⊗[R] S`. -/
noncomputable
/--
Definition of `baseChange` / `baseChange` 的定义

English:
definition baseChange
  signature: {T} [CommRing T] [Algebra R T] (P : Extension R S)
  body: T otimes[R] P.Ring
  __ := ofSurjective (P := T otimes[R] P.Ring) (Algebra.TensorProduct.map (AlgHom.id T T)
    (IsScalarTower.toAlgHom _ _ _)) (LinearMap.lTensor_surjective T
    (g := (IsScalarTower.toAlgHom R P.Ring S).toLinearMap) P.algebraMap_surjective)

中文:
定义 baseChange
  签名: {T} [交换环 T] [代数 R T] (P : 扩张 R S)
  定义体: T otimes[R] P.Ring
  __ := ofSurjective (P := T otimes[R] P.Ring) (Algebra.TensorProduct.map (AlgHom.id T T)
    (IsScalarTower.toAlgHom _ _ _)) (LinearMap.lTensor_surjective T
    (g := (IsScalarTower.toAlgHom R P.Ring S).toLinearMap) P.algebraMap_surjective)

Depends on / 依赖: P.Ring, otimes
-/
def baseChange {T} [CommRing T] [Algebra R T] (P : Extension R S) : Extension T (T otimes[R] S) where
  Ring := T otimes[R] P.Ring
  __ := ofSurjective (P := T otimes[R] P.Ring) (Algebra.TensorProduct.map (AlgHom.id T T)
    (IsScalarTower.toAlgHom _ _ _)) (LinearMap.lTensor_surjective T
    (g := (IsScalarTower.toAlgHom R P.Ring S).toLinearMap) P.algebraMap_surjective)

variable (T) in
/--
lemma `ker_baseChange` / 引理 `ker_baseChange`

English:
lemma ker_baseChange
  proof: Algebra.TensorProduct.lTensor_ker (A := T) (IsScalarTower.toAlgHom R P.Ring S)
    P.algebraMap_surjective

中文:
引理 ker_baseChange
  证明: Algebra.TensorProduct.lTensor_ker (A := T) (IsScalarTower.toAlgHom R P.Ring S)
    P.algebraMap_surjective

Depends on / 依赖: Algebra, Algebra.TensorProduct.includeRight.toRingHom, P.ker.map, TensorProduct, includeRight, toRingHom
-/
lemma ker_baseChange :
    (P.baseChange (T := T)).ker = P.ker.map Algebra.TensorProduct.includeRight.toRingHom :=
  Algebra.TensorProduct.lTensor_ker (A := T) (IsScalarTower.toAlgHom R P.Ring S)
    P.algebraMap_surjective

variable (T) in
/--
The ring `T ⊗[R] P.Ring` underlying the extension `P.baseChange T` is a `P.Ring`-algebra
by action on the right. This causes a (mathematical) diamond when `T = P.Ring`, so it is
not an instance.
-/
@[instance_reducible]
/--
Definition of `algebraBaseChange` / `algebraBaseChange` 的定义

English:
definition algebraBaseChange
  signature: : Algebra P.Ring (P.baseChange (T := T)).Ring
  body: fast_instance% TensorProduct.rightAlgebra

中文:
定义 algebraBaseChange
  签名: : 代数 P.环 (P.baseChange (T := T)).环
  定义体: fast_instance% TensorProduct.rightAlgebra
-/
noncomputable def algebraBaseChange : Algebra P.Ring (P.baseChange (T := T)).Ring :=
  fast_instance% TensorProduct.rightAlgebra

set_option backward.isDefEq.respectTransparency false in
attribute [local instance] algebraBaseChange in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsScalarTower R P.Ring (P.baseChange (T := T)).Ring
  body: .of_algebraMap_eq fun x => by simp [baseChange, RingHom.algebraMap_toAlgebra]; rfl

中文:
实例 :
  签名: 标量塔 R P.环 (P.baseChange (T := T)).环
  定义体: .of_algebraMap_eq fun x => by simp [baseChange, RingHom.algebraMap_toAlgebra]; rfl
-/
instance : IsScalarTower R P.Ring (P.baseChange (T := T)).Ring :=
  .of_algebraMap_eq fun x => by simp [baseChange, RingHom.algebraMap_toAlgebra]; rfl

end Construction

variable {R' S'} [CommRing R'] [CommRing S'] [Algebra R' S'] (P' : Extension R' S')
variable {R'' S''} [CommRing R''] [CommRing S''] [Algebra R'' S''] (P'' : Extension R'' S'')

section Hom

section

variable [Algebra R R'] [Algebra R' R''] [Algebra R R'']
variable [Algebra S S'] [Algebra S' S''] [Algebra S S'']

/-- Given a commuting square
```
R --→ P -→ S
| |
↓ ↓
R' -→ P' → S
```
A hom between `P` and `P'` is a ring homomorphism that makes the two squares commute.
-/
@[ext]
/--
Definition of `Hom` / `Hom` 的定义

English:
structure Hom
  parameters: where
  axioms and operations (3):
    - toRingHom : P.Ring ->+* P'.Ring
    - toRingHom_algebraMap : forall x, toRingHom (algebraMap R P.Ring x) = algebraMap R' P'.Ring (algebraMap R R' x)
    - algebraMap_toRingHom : forall x, (algebraMap P'.Ring S' (toRingHom x)) = algebraMap S S' (algebraMap P.Ring S x)

中文:
结构 态射
  参数: where
  公理与运算 (3 个):
    - toRingHom : P.环 ->+* P'.环
    - toRingHom_algebraMap : 对任意 x, toRingHom (algebraMap R P.环 x) = algebraMap R' P'.环 (algebraMap R R' x)
    - algebraMap_toRingHom : 对任意 x, (algebraMap P'.环 S' (toRingHom x)) = algebraMap S S' (algebraMap P.环 S x)
-/
structure Hom where
  /-- The underlying ring homomorphism of a hom between extensions. -/
  toRingHom : P.Ring ->+* P'.Ring
  toRingHom_algebraMap :
    forall x, toRingHom (algebraMap R P.Ring x) = algebraMap R' P'.Ring (algebraMap R R' x)
  algebraMap_toRingHom :
    forall x, (algebraMap P'.Ring S' (toRingHom x)) = algebraMap S S' (algebraMap P.Ring S x)

attribute [simp] Hom.toRingHom_algebraMap Hom.algebraMap_toRingHom

variable {P P'}

/-- A hom between extensions as an algebra homomorphism. -/
noncomputable
/--
Definition of `Hom.toAlgHom` / `Hom.toAlgHom` 的定义

English:
definition Hom.toAlgHom
  signature: [Algebra R S'] [IsScalarTower R R' S'] (f : Hom P P')
  body: f.toRingHom
  commutes' := by simp [← IsScalarTower.algebraMap_apply]

@[simp]

中文:
定义 态射.toAlgHom
  签名: [代数 R S'] [标量塔 R R' S'] (f : 态射 P P')
  定义体: f.toRingHom
  commutes' := by simp [← IsScalarTower.algebraMap_apply]

@[simp]

Depends on / 依赖: f.toRingHom, toRingHom
-/
def Hom.toAlgHom [Algebra R S'] [IsScalarTower R R' S'] (f : Hom P P') :
    P.Ring ->ₐ[R] P'.Ring where
  __ := f.toRingHom
  commutes' := by simp [← IsScalarTower.algebraMap_apply]

@[simp]
/--
lemma `Hom.toAlgHom_apply` / 引理 `Hom.toAlgHom_apply`

English:
lemma Hom.toAlgHom_apply
  given: [Algebra R S'] [IsScalarTower R R' S'] (f : Hom P P') (x)
  proof: rfl

中文:
引理 态射.toAlgHom_apply
  条件: [代数 R S'] [标量塔 R R' S'] (f : 态射 P P') (x)
  证明: rfl
-/
lemma Hom.toAlgHom_apply [Algebra R S'] [IsScalarTower R R' S'] (f : Hom P P') (x) :
    f.toAlgHom x = f.toRingHom x := rfl

/-- A hom of extensions `P → P'` can be constructed from an algebra map
`P.Ring →ₐ[R] P'.Ring`. -/
@[simps]
/--
Definition of `Hom.ofAlgHom` / `Hom.ofAlgHom` 的定义

English:
definition Hom.ofAlgHom
  signature: [Algebra R S'] [IsScalarTower R R' S'] [IsScalarTower R S S']
  body: f.toRingHom
  toRingHom_algebraMap := f.commutes'
  algebraMap_toRingHom x := congr($H x)

@[simp]

中文:
定义 态射.ofAlgHom
  签名: [代数 R S'] [标量塔 R R' S'] [标量塔 R S S']
  定义体: f.toRingHom
  toRingHom_algebraMap := f.commutes'
  algebraMap_toRingHom x := congr($H x)

@[simp]

Depends on / 依赖: f.toRingHom, toRingHom
-/
def Hom.ofAlgHom [Algebra R S'] [IsScalarTower R R' S'] [IsScalarTower R S S']
    (f : P.Ring ->ₐ[R] P'.Ring)
    (H : (IsScalarTower.toAlgHom R P'.Ring S').comp f =
      (IsScalarTower.toAlgHom R S S').comp (IsScalarTower.toAlgHom R P.Ring S)) :
    P.Hom P' where
  toRingHom := f.toRingHom
  toRingHom_algebraMap := f.commutes'
  algebraMap_toRingHom x := congr($H x)

@[simp]
/--
lemma `Hom.toAlgHom_ofAlgHom` / 引理 `Hom.toAlgHom_ofAlgHom`

English:
lemma Hom.toAlgHom_ofAlgHom
  statement: [Algebra R S'] [IsScalarTower R R' S'] [IsScalarTower R S S']
  proof: rfl

中文:
引理 态射.toAlgHom_ofAlgHom
  结论: [代数 R S'] [标量塔 R R' S'] [标量塔 R S S']
  证明: rfl
-/
lemma Hom.toAlgHom_ofAlgHom [Algebra R S'] [IsScalarTower R R' S'] [IsScalarTower R S S']
    (f : P.Ring ->ₐ[R] P'.Ring)
    (H : (IsScalarTower.toAlgHom R P'.Ring S').comp f =
      (IsScalarTower.toAlgHom R S S').comp (IsScalarTower.toAlgHom R P.Ring S)) :
    (Hom.ofAlgHom f H).toAlgHom = f :=
  rfl

variable (P P')

/-- The identity hom. -/
@[simps]
/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def Hom.id
  body: ⟨RingHom.id _, by simp, by simp⟩

@[simp]

中文:
定义 noncomputable
  签名: def 态射.id
  定义体: ⟨RingHom.id _, by simp, by simp⟩

@[simp]
-/
protected noncomputable def Hom.id : Hom P P := ⟨RingHom.id _, by simp, by simp⟩

@[simp]
/--
lemma `Hom.toAlgHom_id` / 引理 `Hom.toAlgHom_id`

English:
lemma Hom.toAlgHom_id
  statement: Hom.toAlgHom (.id P) = AlgHom.id _ _
  proof: by ext1; simp

中文:
引理 态射.toAlgHom_id
  结论: 态射.toAlgHom (.id P) = 代数态射.id _ _
  证明: by ext1; simp
-/
lemma Hom.toAlgHom_id : Hom.toAlgHom (.id P) = AlgHom.id _ _ := by ext1; simp

variable {P P' P''}

variable [IsScalarTower R R' R''] [IsScalarTower S S' S''] in
/-- The composition of two homs. -/
@[simps]
/--
Definition of `Hom.comp` / `Hom.comp` 的定义

English:
definition Hom.comp
  signature: (f : Hom P' P'') (g : Hom P P')
  body: f.toRingHom.comp g.toRingHom
  toRingHom_algebraMap := by simp [← IsScalarTower.algebraMap_apply]
  algebraMap_toRingHom := by simp [← IsScalarTower.algebraMap_apply]

@[simp]

中文:
定义 态射.comp
  签名: (f : 态射 P' P'') (g : 态射 P P')
  定义体: f.toRingHom.comp g.toRingHom
  toRingHom_algebraMap := by simp [← IsScalarTower.algebraMap_apply]
  algebraMap_toRingHom := by simp [← IsScalarTower.algebraMap_apply]

@[simp]
-/
noncomputable def Hom.comp (f : Hom P' P'') (g : Hom P P') : Hom P P'' where
  toRingHom := f.toRingHom.comp g.toRingHom
  toRingHom_algebraMap := by simp [← IsScalarTower.algebraMap_apply]
  algebraMap_toRingHom := by simp [← IsScalarTower.algebraMap_apply]

@[simp]
/--
lemma `Hom.comp_id` / 引理 `Hom.comp_id`

English:
lemma Hom.comp_id
  given: (f : Hom P P')
  statement: f.comp (Hom.id P) = f
  proof: by ext; simp

@[simp]

中文:
引理 态射.comp_id
  条件: (f : 态射 P P')
  结论: f.comp (态射.id P) = f
  证明: by ext; simp

@[simp]
-/
lemma Hom.comp_id (f : Hom P P') : f.comp (Hom.id P) = f := by ext; simp

@[simp]
/--
lemma `Hom.id_comp` / 引理 `Hom.id_comp`

English:
lemma Hom.id_comp
  given: (f : Hom P P')
  statement: (Hom.id P').comp f = f
  proof: by
  ext; simp [Hom.id]

中文:
引理 态射.id_comp
  条件: (f : 态射 P P')
  结论: (态射.id P').comp f = f
  证明: by
  ext; simp [Hom.id]

Depends on / 依赖: Hom.id, mk_iff, ppSpace
-/
lemma Hom.id_comp (f : Hom P P') : (Hom.id P').comp f = f := by
  ext; simp [Hom.id]

/-- A map between extensions induce a map between kernels. -/
@[simps]
/--
Definition of `Hom.mapKer` / `Hom.mapKer` 的定义

English:
definition Hom.mapKer
  signature: (f : P.Hom P')
  body: ⟨f.toRingHom x, by simp [show algebraMap P.Ring S x = 0 from x.2]⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' := by simp [Algebra.smul_def, ← halg]

中文:
定义 态射.mapKer
  签名: (f : P.态射 P')
  定义体: ⟨f.toRingHom x, by simp [show algebraMap P.Ring S x = 0 from x.2]⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' := by simp [Algebra.smul_def, ← halg]

Depends on / 依赖: P.Ring, algebraMap, f.toRingHom, toRingHom
-/
def Hom.mapKer (f : P.Hom P')
    [alg : Algebra P.Ring P'.Ring] (halg : algebraMap P.Ring P'.Ring = f.toRingHom) :
    P.ker ->ₗ[P.Ring] P'.ker where
  toFun x := ⟨f.toRingHom x, by simp [show algebraMap P.Ring S x = 0 from x.2]⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' := by simp [Algebra.smul_def, ← halg]

set_option backward.isDefEq.respectTransparency false in
attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- The canonical hom from `P` to its base change `P.baseChange`. -/
@[simps]
/--
Definition of `toBaseChange` / `toBaseChange` 的定义

English:
definition toBaseChange
  signature: (T : Type*) [CommRing T] [Algebra R T]
  body: TensorProduct.includeRight.toRingHom
  toRingHom_algebraMap x := by simp [baseChange]
  algebraMap_toRingHom x := rfl

中文:
定义 toBaseChange
  签名: (T : 类型) [交换环 T] [代数 R T]
  定义体: TensorProduct.includeRight.toRingHom
  toRingHom_algebraMap x := by simp [baseChange]
  algebraMap_toRingHom x := rfl
-/
noncomputable def toBaseChange (T : Type*) [CommRing T] [Algebra R T] :
    P.Hom (P.baseChange (T := T)) where
  toRingHom := TensorProduct.includeRight.toRingHom
  toRingHom_algebraMap x := by simp [baseChange]
  algebraMap_toRingHom x := rfl

end

instance {P P' : Extension R S} : FunLike (P.Hom P') P.Ring P'.Ring where
  coe f := f.toRingHom
  coe_injective _ _ h := Extension.Hom.ext (DFunLike.coe_fn_eq.mp h)

end Hom

section Infinitesimal

/-- Given an `R`-algebra extension `0 → I → P → S → 0` of `S`,
the infinitesimal extension associated to it is `0 → I/I² → P/I² → S → 0`. -/
noncomputable
/--
Definition of `infinitesimal` / `infinitesimal` 的定义

English:
definition infinitesimal
  signature: (P : Extension R S)
  body: P.Ring ⧸ P.ker ^ 2
  σ := Ideal.Quotient.mk _ ∘ P.σ
  algebraMap_σ x := by dsimp; exact P.algebraMap_σ x

中文:
定义 infinitesimal
  签名: (P : 扩张 R S)
  定义体: P.Ring ⧸ P.ker ^ 2
  σ := Ideal.Quotient.mk _ ∘ P.σ
  algebraMap_σ x := by dsimp; exact P.algebraMap_σ x

Depends on / 依赖: P.Ring, P.ker
-/
def infinitesimal (P : Extension R S) : Extension R S where
  Ring := P.Ring ⧸ P.ker ^ 2
  σ := Ideal.Quotient.mk _ ∘ P.σ
  algebraMap_σ x := by dsimp; exact P.algebraMap_σ x

/-- The canonical map `P → P/I²` as maps between extensions. -/
noncomputable
/--
Definition of `toInfinitesimal` / `toInfinitesimal` 的定义

English:
definition toInfinitesimal
  signature: (P : Extension R S)
  body: Ideal.Quotient.mk _
  toRingHom_algebraMap _ := rfl
  algebraMap_toRingHom _ := rfl

中文:
定义 toInfinitesimal
  签名: (P : 扩张 R S)
  定义体: Ideal.Quotient.mk _
  toRingHom_algebraMap _ := rfl
  algebraMap_toRingHom _ := rfl

Depends on / 依赖: Ideal.Quotient.mk, Quotient
-/
def toInfinitesimal (P : Extension R S) : P.Hom P.infinitesimal where
  toRingHom := Ideal.Quotient.mk _
  toRingHom_algebraMap _ := rfl
  algebraMap_toRingHom _ := rfl

/--
lemma `ker_infinitesimal` / 引理 `ker_infinitesimal`

English:
lemma ker_infinitesimal
  given: (P : Extension R S)
  proof: AlgHom.ker_kerSquareLift _

中文:
引理 ker_infinitesimal
  条件: (P : 扩张 R S)
  证明: AlgHom.ker_kerSquareLift _

Depends on / 依赖: AlgHom, AlgHom.ker_kerSquareLift, ker_kerSquareLift
-/
lemma ker_infinitesimal (P : Extension R S) :
    P.infinitesimal.ker = P.ker.cotangentIdeal :=
  AlgHom.ker_kerSquareLift _

end Infinitesimal

section Cotangent

/--
Definition of `Cotangent` / `Cotangent` 的定义

English:
definition Cotangent
  signature: : Type _
  body: P.ker.Cotangent

noncomputable

中文:
定义 余切
  签名: : 类型 _
  定义体: P.ker.Cotangent

noncomputable

Depends on / 依赖: Cotangent, P.ker.Cotangent
-/
def Cotangent : Type _ := P.ker.Cotangent

noncomputable
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddCommGroup P.Cotangent
  body: inferInstanceAs (AddCommGroup P.ker.Cotangent)

中文:
实例 :
  签名: 加法交换群 P.余切
  定义体: inferInstanceAs (AddCommGroup P.ker.Cotangent)

Depends on / 依赖: AddCommGroup, Cotangent, P.ker.Cotangent
-/
instance : AddCommGroup P.Cotangent := inferInstanceAs (AddCommGroup P.ker.Cotangent)

variable {P}

/--
Definition of `Cotangent.of` / `Cotangent.of` 的定义

English:
definition Cotangent.of
  signature: (x : P.ker.Cotangent)
  body: x

中文:
定义 余切.of
  签名: (x : P.ker.余切)
  定义体: x
-/
def Cotangent.of (x : P.ker.Cotangent) : P.Cotangent := x

/--
Definition of `Cotangent.val` / `Cotangent.val` 的定义

English:
definition Cotangent.val
  signature: (x : P.Cotangent)
  body: x

@[ext]

中文:
定义 余切.val
  签名: (x : P.余切)
  定义体: x

@[ext]
-/
def Cotangent.val (x : P.Cotangent) : P.ker.Cotangent := x

@[ext]
/--
lemma `Cotangent.ext` / 引理 `Cotangent.ext`

English:
lemma Cotangent.ext
  given: {x y : P.Cotangent} (e : x.val = y.val)
  statement: x = y
  proof: e

中文:
引理 余切.ext
  条件: {x y : P.余切} (e : x.val = y.val)
  结论: x = y
  证明: e
-/
lemma Cotangent.ext {x y : P.Cotangent} (e : x.val = y.val) : x = y := e

namespace Cotangent

variable (x y : P.Cotangent) (w z : P.ker.Cotangent)

/--
lemma `val_add` / 引理 `val_add`

English:
lemma val_add
  statement: (x + y).val = x.val + y.val
  proof: rfl

中文:
引理 val_add
  结论: (x + y).val = x.val + y.val
  证明: rfl
-/
@[simp] lemma val_add : (x + y).val = x.val + y.val := rfl
/--
lemma `val_zero` / 引理 `val_zero`

English:
lemma val_zero
  statement: (0 : P.Cotangent).val = 0
  proof: rfl

中文:
引理 val_zero
  结论: (0 : P.余切).val = 0
  证明: rfl
-/
@[simp] lemma val_zero : (0 : P.Cotangent).val = 0 := rfl
/--
lemma `of_add` / 引理 `of_add`

English:
lemma of_add
  statement: of (w + z) = of w + of z
  proof: rfl

中文:
引理 of_add
  结论: of (w + z) = of w + of z
  证明: rfl
-/
@[simp] lemma of_add : of (w + z) = of w + of z := rfl
/--
lemma `of_zero` / 引理 `of_zero`

English:
lemma of_zero
  statement: (of 0 : P.Cotangent) = 0
  proof: rfl

中文:
引理 of_zero
  结论: (of 0 : P.余切) = 0
  证明: rfl
-/
@[simp] lemma of_zero : (of 0 : P.Cotangent) = 0 := rfl
/--
lemma `of_val` / 引理 `of_val`

English:
lemma of_val
  statement: of x.val = x
  proof: rfl

中文:
引理 of_val
  结论: of x.val = x
  证明: rfl
-/
@[simp] lemma of_val : of x.val = x := rfl
/--
lemma `val_of` / 引理 `val_of`

English:
lemma val_of
  statement: (of w).val = w
  proof: rfl

中文:
引理 val_of
  结论: (of w).val = w
  证明: rfl
-/
@[simp] lemma val_of : (of w).val = w := rfl
/--
lemma `val_sub` / 引理 `val_sub`

English:
lemma val_sub
  statement: (x - y).val = x.val - y.val
  proof: rfl

中文:
引理 val_sub
  结论: (x - y).val = x.val - y.val
  证明: rfl
-/
@[simp] lemma val_sub : (x - y).val = x.val - y.val := rfl

end Cotangent

/--
lemma `Cotangent.smul_eq_zero_of_mem` / 引理 `Cotangent.smul_eq_zero_of_mem`

English:
lemma Cotangent.smul_eq_zero_of_mem
  given: (p : P.Ring) (hp : p in P.ker) (m : P.ker.Cotangent)
  proof: Ideal.Cotangent.smul_eq_zero_of_mem hp m

中文:
引理 余切.smul_eq_zero_of_mem
  条件: (p : P.环) (hp : p in P.ker) (m : P.ker.余切)
  证明: Ideal.Cotangent.smul_eq_zero_of_mem hp m

Depends on / 依赖: Cotangent, Ideal.Cotangent.smul_eq_zero_of_mem, smul_eq_zero_of_mem
-/
lemma Cotangent.smul_eq_zero_of_mem (p : P.Ring) (hp : p in P.ker) (m : P.ker.Cotangent) :
    p • m = 0 :=
  Ideal.Cotangent.smul_eq_zero_of_mem hp m

attribute [local simp] RingHom.mem_ker

set_option backward.isDefEq.respectTransparency.types false in
noncomputable
/--
Instance `Cotangent.module` / 实例 `Cotangent.module`

English:
instance Cotangent.module
  signature: : Module S P.Cotangent where
  body: fun r s => .of (P.σ r • s.val)
  smul_zero := fun r => ext (smul_zero (P.σ r))
  smul_add := fun r x y => ext (smul_add (P.σ r) x.val y.val)
  add_smul := fun r s x => by
    have := smul_eq_zero_of_mem (P.σ (r + s) - (P.σ r + P.σ s) : P.Ring) (by simp) x
    simpa only [sub_smul, add_smul, sub_eq_z

中文:
实例 余切.module
  签名: : 模 S P.余切 where
  定义体: fun r s => .of (P.σ r • s.val)
  smul_zero := fun r => ext (smul_zero (P.σ r))
  smul_add := fun r x y => ext (smul_add (P.σ r) x.val y.val)
  add_smul := fun r s x => by
    have := smul_eq_zero_of_mem (P.σ (r + s) - (P.σ r + P.σ s) : P.Ring) (by simp) x
    simpa only [sub_smul, add_smul, sub_eq_z

Depends on / 依赖: s.val
-/
instance Cotangent.module : Module S P.Cotangent where
  smul := fun r s => .of (P.σ r • s.val)
  smul_zero := fun r => ext (smul_zero (P.σ r))
  smul_add := fun r x y => ext (smul_add (P.σ r) x.val y.val)
  add_smul := fun r s x => by
    have := smul_eq_zero_of_mem (P.σ (r + s) - (P.σ r + P.σ s) : P.Ring) (by simp) x
    simpa only [sub_smul, add_smul, sub_eq_zero]
  zero_smul := fun x => smul_eq_zero_of_mem (P.σ 0 : P.Ring) (by simp) x
  one_smul := fun x => by
    have := smul_eq_zero_of_mem (P.σ 1 - 1 : P.Ring) (by simp) x
    simpa [sub_eq_zero, sub_smul]
  mul_smul := fun r s x => by
    have := smul_eq_zero_of_mem (P.σ (r * s) - (P.σ r * P.σ s) : P.Ring) (by simp) x
    simpa only [sub_smul, mul_smul, sub_eq_zero] using! this

noncomputable
instance {R₀} [CommRing R₀] [Algebra R₀ S] : Module R₀ P.Cotangent :=
  Module.compHom P.Cotangent (algebraMap R₀ S)

instance {R₁ R₂} [CommRing R₁] [CommRing R₂] [Algebra R₁ S] [Algebra R₂ S] [Algebra R₁ R₂]
    [IsScalarTower R₁ R₂ S] :
    IsScalarTower R₁ R₂ P.Cotangent := by
  constructor
  intro r s m
  change algebraMap R₂ S (r • s) • m = (algebraMap _ S r) • (algebraMap _ S s) • m
  rw [Algebra.smul_def]; rw [map_mul]; rw [mul_smul]; rw [← IsScalarTower.algebraMap_apply]

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `Cotangent.val_smul'''` / 引理 `Cotangent.val_smul'''`

English:
lemma Cotangent.val_smul'''
  given: {R₀} [CommRing R₀] [Algebra R₀ S] (r : R₀) (x : P.Cotangent)
  proof: rfl

中文:
引理 余切.val_smul'''
  条件: {R₀} [交换环 R₀] [代数 R₀ S] (r : R₀) (x : P.余切)
  证明: rfl
-/
lemma Cotangent.val_smul''' {R₀} [CommRing R₀] [Algebra R₀ S] (r : R₀) (x : P.Cotangent) :
    (r • x).val = P.σ (algebraMap R₀ S r) • x.val := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- The action of `S` on `P.Cotangent` for an extension `P → S`. -/
@[simp]
/--
lemma `Cotangent.val_smul` / 引理 `Cotangent.val_smul`

English:
lemma Cotangent.val_smul
  given: (r : S) (x : P.Cotangent)
  statement: (r • x).val = P.σ r • x.val
  proof: rfl

中文:
引理 余切.val_smul
  条件: (r : S) (x : P.余切)
  结论: (r • x).val = P.σ r • x.val
  证明: rfl
-/
lemma Cotangent.val_smul (r : S) (x : P.Cotangent) : (r • x).val = P.σ r • x.val := rfl

/-- The action of `P` on `P.Cotangent` for an extension `P → S`. -/
@[simp]
/--
lemma `Cotangent.val_smul'` / 引理 `Cotangent.val_smul'`

English:
lemma Cotangent.val_smul'
  given: (r : P.Ring) (x : P.Cotangent)
  statement: (r • x).val = r • x.val
  proof: by
  rw [val_smul''']; rw [← sub_eq_zero]; rw [← sub_smul]
  exact Cotangent.smul_eq_zero_of_mem _ (by simp) _

中文:
引理 余切.val_smul'
  条件: (r : P.环) (x : P.余切)
  结论: (r • x).val = r • x.val
  证明: by
  rw [val_smul''']; rw [← sub_eq_zero]; rw [← sub_smul]
  exact Cotangent.smul_eq_zero_of_mem _ (by simp) _

Depends on / 依赖: Cotangent, Cotangent.smul_eq_zero_of_mem, smul_eq_zero_of_mem, sub_eq_zero, sub_smul, val_smul
-/
lemma Cotangent.val_smul' (r : P.Ring) (x : P.Cotangent) : (r • x).val = r • x.val := by
  rw [val_smul''']; rw [← sub_eq_zero]; rw [← sub_smul]
  exact Cotangent.smul_eq_zero_of_mem _ (by simp) _

/-- The action of `R` on `P.Cotangent` for an `R`-extension `P → S`. -/
@[simp]
/--
lemma `Cotangent.val_smul''` / 引理 `Cotangent.val_smul''`

English:
lemma Cotangent.val_smul''
  given: (r : R) (x : P.Cotangent)
  statement: (r • x).val = r • x.val
  proof: by
  rw [← algebraMap_smul P.Ring]; rw [val_smul']; rw [algebraMap_smul]

中文:
引理 余切.val_smul''
  条件: (r : R) (x : P.余切)
  结论: (r • x).val = r • x.val
  证明: by
  rw [← algebraMap_smul P.Ring]; rw [val_smul']; rw [algebraMap_smul]

Depends on / 依赖: P.Ring, algebraMap_smul, val_smul
-/
lemma Cotangent.val_smul'' (r : R) (x : P.Cotangent) : (r • x).val = r • x.val := by
  rw [← algebraMap_smul P.Ring]; rw [val_smul']; rw [algebraMap_smul]

/-- `Cotangent.val` as a linear isomorphism. -/
@[simps]
/--
Definition of `cotangentEquivCotangentKer` / `cotangentEquivCotangentKer` 的定义

English:
definition cotangentEquivCotangentKer
  signature: : P.Cotangent ≃ₗ[P.Ring] P.ker.Cotangent where
  body: Cotangent.val
  invFun := Cotangent.of
  map_add' x y := by simp
  map_smul' x y := by simp

中文:
定义 cotangentEquivCotangentKer
  签名: : P.余切 ≃ₗ[P.环] P.ker.余切 where
  定义体: Cotangent.val
  invFun := Cotangent.of
  map_add' x y := by simp
  map_smul' x y := by simp

Depends on / 依赖: Cotangent, Cotangent.val
-/
def cotangentEquivCotangentKer : P.Cotangent ≃ₗ[P.Ring] P.ker.Cotangent where
  toFun := Cotangent.val
  invFun := Cotangent.of
  map_add' x y := by simp
  map_smul' x y := by simp

/--
Definition of `Cotangent.mk` / `Cotangent.mk` 的定义

English:
definition Cotangent.mk
  signature: : P.ker ->ₗ[P.Ring] P.Cotangent where
  body: .of (Ideal.toCotangent _ x)
  map_add' x y := by simp
map_smul' x y := ext by simp

@[simp]

中文:
定义 余切.mk
  签名: : P.ker ->ₗ[P.环] P.余切 where
  定义体: .of (Ideal.toCotangent _ x)
  map_add' x y := by simp
map_smul' x y := ext by simp

@[simp]

Depends on / 依赖: Ideal.toCotangent, toCotangent
-/
noncomputable def Cotangent.mk : P.ker ->ₗ[P.Ring] P.Cotangent where
  toFun x := .of (Ideal.toCotangent _ x)
  map_add' x y := by simp
map_smul' x y := ext by simp

@[simp]
/--
lemma `Cotangent.val_mk` / 引理 `Cotangent.val_mk`

English:
lemma Cotangent.val_mk
  given: (x : P.ker)
  statement: (mk x).val = Ideal.toCotangent _ x
  proof: rfl

中文:
引理 余切.val_mk
  条件: (x : P.ker)
  结论: (mk x).val = 理想.toCotangent _ x
  证明: rfl
-/
lemma Cotangent.val_mk (x : P.ker) : (mk x).val = Ideal.toCotangent _ x := rfl

/--
lemma `Cotangent.mk_surjective` / 引理 `Cotangent.mk_surjective`

English:
lemma Cotangent.mk_surjective
  statement: Function.Surjective (mk (P := P))
  proof: fun x => Ideal.toCotangent_surjective P.ker x.val

中文:
引理 余切.mk_surjective
  结论: 函数.满射 (mk (P := P))
  证明: fun x => Ideal.toCotangent_surjective P.ker x.val
-/
lemma Cotangent.mk_surjective : Function.Surjective (mk (P := P)) :=
  fun x => Ideal.toCotangent_surjective P.ker x.val

/--
lemma `Cotangent.mk_eq_zero_iff` / 引理 `Cotangent.mk_eq_zero_iff`

English:
lemma Cotangent.mk_eq_zero_iff
  given: {P : Extension R S} (x : P.ker)
  proof: by
  simp [Cotangent.ext_iff, Ideal.toCotangent_eq_zero]

中文:
引理 余切.mk_eq_zero_iff
  条件: {P : 扩张 R S} (x : P.ker)
  证明: by
  simp [Cotangent.ext_iff, Ideal.toCotangent_eq_zero]

Depends on / 依赖: Cotangent, Cotangent.ext_iff, Ideal.toCotangent_eq_zero, ext_iff, toCotangent_eq_zero
-/
lemma Cotangent.mk_eq_zero_iff {P : Extension R S} (x : P.ker) :
    Cotangent.mk x = 0 ↔ x.val in P.ker ^ 2 := by
  simp [Cotangent.ext_iff, Ideal.toCotangent_eq_zero]

/--
lemma `Cotangent.mk_eq_mk_iff_sub_mem` / 引理 `Cotangent.mk_eq_mk_iff_sub_mem`

English:
lemma Cotangent.mk_eq_mk_iff_sub_mem
  given: (x y : P.ker)
  proof: by
  simp [Extension.Cotangent.ext_iff, Ideal.toCotangent_eq]

中文:
引理 余切.mk_eq_mk_iff_sub_mem
  条件: (x y : P.ker)
  证明: by
  simp [Extension.Cotangent.ext_iff, Ideal.toCotangent_eq]

Depends on / 依赖: Cotangent, Extension, Extension.Cotangent.ext_iff, Ideal.toCotangent_eq, ext_iff, toCotangent_eq
-/
lemma Cotangent.mk_eq_mk_iff_sub_mem (x y : P.ker) :
    mk x = mk y ↔ x.val - y.val in P.ker ^ 2 := by
  simp [Extension.Cotangent.ext_iff, Ideal.toCotangent_eq]

variable (P) in
/--
lemma `Cotangent.ker_mk` / 引理 `Cotangent.ker_mk`

English:
lemma Cotangent.ker_mk
  statement: LinearMap.ker (mk (P := P)) = P.ker • ⊤
  proof: by
  ext ⟨x, hx⟩
  simp [LinearMap.mem_ker, mk_eq_zero_iff, Submodule.mem_smul_top_iff, sq]

中文:
引理 余切.ker_mk
  结论: 线性映射.ker (mk (P := P)) = P.ker • ⊤
  证明: by
  ext ⟨x, hx⟩
  simp [LinearMap.mem_ker, mk_eq_zero_iff, Submodule.mem_smul_top_iff, sq]

Depends on / 依赖: LinearMap, LinearMap.mem_ker, P.ker, Submodule, Submodule.mem_smul_top_iff, mem_ker, mem_smul_top_iff, mk_eq_zero_iff
-/
lemma Cotangent.ker_mk : LinearMap.ker (mk (P := P)) = P.ker • ⊤ := by
  ext ⟨x, hx⟩
  simp [LinearMap.mem_ker, mk_eq_zero_iff, Submodule.mem_smul_top_iff, sq]

/--
lemma `Cotangent.span_eq_top_of_span_eq_ker` / 引理 `Cotangent.span_eq_top_of_span_eq_ker`

English:
lemma Cotangent.span_eq_top_of_span_eq_ker
  statement: {ι : Type*} (s : ι -> P.Ring)
  proof: by
  rw [Ideal.span]; rw [← Submodule.span_range_subtype_eq_top_iff] at hs
  · apply Submodule.span_eq_top_of_span_eq_top (R := P.Ring)
    rw [← Function.comp_def]; rw [Set.range_comp]; rw [← Submodule.map_span]; rw [hs]; rw [Submodule.map_top]; rw [LinearMap.range_eq_top_of_surjective _ mk_surject

中文:
引理 余切.span_eq_top_of_span_eq_ker
  结论: {ι : 类型} (s : ι -> P.环)
  证明: by
  rw [Ideal.span]; rw [← Submodule.span_range_subtype_eq_top_iff] at hs
  · apply Submodule.span_eq_top_of_span_eq_top (R := P.Ring)
    rw [← Function.comp_def]; rw [Set.range_comp]; rw [← Submodule.map_span]; rw [hs]; rw [Submodule.map_top]; rw [LinearMap.range_eq_top_of_surjective _ mk_surject

Depends on / 依赖: Function, Function.comp_def, Ideal.mem_span_range_self, Ideal.span, LinearMap, LinearMap.range_eq_top_of_surjective, P.Ring, Set.range_comp, Submodule, Submodule.map_span, Submodule.map_top, Submodule.span_eq_top_of_span_eq_top, Submodule.span_range_subtype_eq_top_iff, comp_def, map_span, map_top, mem_span_range_self, mk_surjective, range_comp, range_eq_top_of_surjective
-/
lemma Cotangent.span_eq_top_of_span_eq_ker {ι : Type*} (s : ι -> P.Ring)
    (hs : Ideal.span (Set.range s) = P.ker) :
    Submodule.span S (.range (fun i => mk ⟨s i, hs.le (Ideal.subset_span ⟨i, rfl⟩)⟩)) = ⊤ := by
  rw [Ideal.span]; rw [← Submodule.span_range_subtype_eq_top_iff] at hs
  · apply Submodule.span_eq_top_of_span_eq_top (R := P.Ring)
    rw [← Function.comp_def]; rw [Set.range_comp]; rw [← Submodule.map_span]; rw [hs]; rw [Submodule.map_top]; rw [LinearMap.range_eq_top_of_surjective _ mk_surjective]
  · simp [← hs, Ideal.mem_span_range_self]

variable {P'}
variable [Algebra R R'] [Algebra R' R''] [Algebra R' S'']
variable [Algebra S S'] [Algebra S' S''] [Algebra S S'']
variable [Algebra R S'] [IsScalarTower R R' S']

/-- A hom between two extensions induces a map between cotangent spaces. -/
noncomputable
/--
Definition of `Cotangent.map` / `Cotangent.map` 的定义

English:
definition Cotangent.map
  signature: (f : Hom P P')
  body: .of (Ideal.mapCotangent (R := R) _ _ f.toAlgHom
    (fun x hx => by simpa using RingHom.congr_arg (algebraMap S S') hx) x.val)
  map_add' x y := ext (map_add _ x.val y.val)
  map_smul' r x := by
    ext
    obtain ⟨x, rfl⟩ := Cotangent.mk_surjective x
    obtain ⟨r, rfl⟩ := P.algebraMap_surjective r

中文:
定义 余切.map
  签名: (f : 态射 P P')
  定义体: .of (Ideal.mapCotangent (R := R) _ _ f.toAlgHom
    (fun x hx => by simpa using RingHom.congr_arg (algebraMap S S') hx) x.val)
  map_add' x y := ext (map_add _ x.val y.val)
  map_smul' r x := by
    ext
    obtain ⟨x, rfl⟩ := Cotangent.mk_surjective x
    obtain ⟨r, rfl⟩ := P.algebraMap_surjective r

Depends on / 依赖: Ideal.mapCotangent, f.toAlgHom, mapCotangent, toAlgHom
-/
def Cotangent.map (f : Hom P P') : P.Cotangent ->ₗ[S] P'.Cotangent where
  toFun x := .of (Ideal.mapCotangent (R := R) _ _ f.toAlgHom
    (fun x hx => by simpa using RingHom.congr_arg (algebraMap S S') hx) x.val)
  map_add' x y := ext (map_add _ x.val y.val)
  map_smul' r x := by
    ext
    obtain ⟨x, rfl⟩ := Cotangent.mk_surjective x
    obtain ⟨r, rfl⟩ := P.algebraMap_surjective r
    simp only [algebraMap_smul, val_smul', val_mk, val_of, Ideal.mapCotangent_toCotangent,
      RingHomCompTriple.comp_apply, ← (Ideal.toCotangent _).map_smul]
    conv_rhs => rw [← algebraMap_smul S', ← f.algebraMap_toRingHom, algebraMap_smul, val_smul',
      val_of, ← (Ideal.toCotangent _).map_smul]
    congr 1
    ext1
    simp only [SetLike.val_smul, smul_eq_mul, map_mul, Hom.toAlgHom_apply]

@[simp]
/--
lemma `Cotangent.map_mk` / 引理 `Cotangent.map_mk`

English:
lemma Cotangent.map_mk
  given: (f : Hom P P') (x)
  proof: rfl

@[simp]

中文:
引理 余切.map_mk
  条件: (f : 态射 P P') (x)
  证明: rfl

@[simp]
-/
lemma Cotangent.map_mk (f : Hom P P') (x) :
    Cotangent.map f (.mk x) =
      .mk ⟨f.toAlgHom x, by simpa [-map_aeval] using RingHom.congr_arg (algebraMap S S') x.2⟩ :=
  rfl

@[simp]
/--
lemma `Cotangent.map_id` / 引理 `Cotangent.map_id`

English:
lemma Cotangent.map_id
  proof: by
  ext x
  obtain ⟨x, rfl⟩ := Cotangent.mk_surjective x
  simp only [map_mk, Hom.toAlgHom_id, AlgHom.coe_id, id_eq, Subtype.coe_eta, val_mk,
    LinearMap.id_coe]

中文:
引理 余切.map_id
  证明: by
  ext x
  obtain ⟨x, rfl⟩ := Cotangent.mk_surjective x
  simp only [map_mk, Hom.toAlgHom_id, AlgHom.coe_id, id_eq, Subtype.coe_eta, val_mk,
    LinearMap.id_coe]

Depends on / 依赖: AlgHom, AlgHom.coe_id, Cotangent, Cotangent.mk_surjective, Hom.toAlgHom_id, LinearMap, LinearMap.id_coe, Subtype, Subtype.coe_eta, coe_eta, coe_id, id_coe, id_eq, map_mk, mk_surjective, toAlgHom_id, val_mk
-/
lemma Cotangent.map_id :
    Cotangent.map (.id P) = LinearMap.id := by
  ext x
  obtain ⟨x, rfl⟩ := Cotangent.mk_surjective x
  simp only [map_mk, Hom.toAlgHom_id, AlgHom.coe_id, id_eq, Subtype.coe_eta, val_mk,
    LinearMap.id_coe]

variable [Algebra R R''] [IsScalarTower R R' R''] [IsScalarTower R' R'' S'']
  [Algebra R S''] [IsScalarTower R R'' S''] [IsScalarTower S S' S'']

/--
lemma `Cotangent.map_comp` / 引理 `Cotangent.map_comp`

English:
lemma Cotangent.map_comp
  given: (f : Hom P P') (g : Hom P' P'')
  proof: by
  ext x
  obtain ⟨x, rfl⟩ := Cotangent.mk_surjective x
  simp only [map_mk, Hom.toAlgHom_apply, Hom.comp_toRingHom, RingHom.coe_comp, Function.comp_apply,
    val_mk, LinearMap.coe_comp, LinearMap.coe_restrictScalars]

中文:
引理 余切.map_comp
  条件: (f : 态射 P P') (g : 态射 P' P'')
  证明: by
  ext x
  obtain ⟨x, rfl⟩ := Cotangent.mk_surjective x
  simp only [map_mk, Hom.toAlgHom_apply, Hom.comp_toRingHom, RingHom.coe_comp, Function.comp_apply,
    val_mk, LinearMap.coe_comp, LinearMap.coe_restrictScalars]

Depends on / 依赖: Cotangent, Cotangent.mk_surjective, Function, Function.comp_apply, Hom.comp_toRingHom, Hom.toAlgHom_apply, LinearMap, LinearMap.coe_comp, LinearMap.coe_restrictScalars, RingHom, RingHom.coe_comp, coe_comp, coe_restrictScalars, comp_apply, comp_toRingHom, map_mk, mk_surjective, toAlgHom_apply, val_mk
-/
lemma Cotangent.map_comp (f : Hom P P') (g : Hom P' P'') :
    Cotangent.map (g.comp f) = (map g).restrictScalars S ∘ₗ map f := by
  ext x
  obtain ⟨x, rfl⟩ := Cotangent.mk_surjective x
  simp only [map_mk, Hom.toAlgHom_apply, Hom.comp_toRingHom, RingHom.coe_comp, Function.comp_apply,
    val_mk, LinearMap.coe_comp, LinearMap.coe_restrictScalars]

/--
lemma `Cotangent.finite` / 引理 `Cotangent.finite`

English:
lemma Cotangent.finite
  given: (hP : P.ker.FG)
  proof: by
  refine ⟨.of_restrictScalars (R := P.Ring) ?_⟩
  rw [Submodule.restrictScalars_top]; rw [← LinearMap.range_eq_top.mpr Extension.Cotangent.mk_surjective]; rw [← Submodule.map_top]
  exact ((Submodule.fg_top P.ker).mpr hP).map _

中文:
引理 余切.finite
  条件: (hP : P.ker.FG)
  证明: by
  refine ⟨.of_restrictScalars (R := P.Ring) ?_⟩
  rw [Submodule.restrictScalars_top]; rw [← LinearMap.range_eq_top.mpr Extension.Cotangent.mk_surjective]; rw [← Submodule.map_top]
  exact ((Submodule.fg_top P.ker).mpr hP).map _

Depends on / 依赖: Cotangent, Extension, Extension.Cotangent.mk_surjective, LinearMap, LinearMap.range_eq_top.mpr, P.Ring, P.ker, Submodule, Submodule.fg_top, Submodule.map_top, Submodule.restrictScalars_top, fg_top, map_top, mk_surjective, of_restrictScalars, range_eq_top, restrictScalars_top
-/
lemma Cotangent.finite (hP : P.ker.FG) :
    Module.Finite S P.Cotangent := by
  refine ⟨.of_restrictScalars (R := P.Ring) ?_⟩
  rw [Submodule.restrictScalars_top]; rw [← LinearMap.range_eq_top.mpr Extension.Cotangent.mk_surjective]; rw [← Submodule.map_top]
  exact ((Submodule.fg_top P.ker).mpr hP).map _

/--
lemma `Cotangent.map_surjective_of_comap_eq` / 引理 `Cotangent.map_surjective_of_comap_eq`

English:
lemma Cotangent.map_surjective_of_comap_eq
  statement: {P P' : Extension R S} {f : P.Hom P'}
  proof: fun x => by
  obtain ⟨x, rfl⟩ := Cotangent.mk_surjective x
  obtain ⟨y, y_in, hy⟩ := Ideal.exists_of_comap_eq_ker_sup _ h eq x.prop
  exact ⟨Cotangent.mk ⟨y, y_in⟩, by simp [hy]⟩

中文:
引理 余切.map_surjective_of_comap_eq
  结论: {P P' : 扩张 R S} {f : P.态射 P'}
  证明: fun x => by
  obtain ⟨x, rfl⟩ := Cotangent.mk_surjective x
  obtain ⟨y, y_in, hy⟩ := Ideal.exists_of_comap_eq_ker_sup _ h eq x.prop
  exact ⟨Cotangent.mk ⟨y, y_in⟩, by simp [hy]⟩

Depends on / 依赖: Cotangent, Cotangent.mk, Cotangent.mk_surjective, Ideal.exists_of_comap_eq_ker_sup, exists_of_comap_eq_ker_sup, mk_surjective, x.prop, y_in
-/
lemma Cotangent.map_surjective_of_comap_eq {P P' : Extension R S} {f : P.Hom P'}
    (h : Function.Surjective f) (eq : P'.ker.comap f.toRingHom = RingHom.ker f.toRingHom ⊔ P.ker) :
    Function.Surjective (Cotangent.map f) := fun x => by
  obtain ⟨x, rfl⟩ := Cotangent.mk_surjective x
  obtain ⟨y, y_in, hy⟩ := Ideal.exists_of_comap_eq_ker_sup _ h eq x.prop
  exact ⟨Cotangent.mk ⟨y, y_in⟩, by simp [hy]⟩

/--
lemma `Cotangent.map_ker_of_surjective` / 引理 `Cotangent.map_ker_of_surjective`

English:
lemma Cotangent.map_ker_of_surjective
  statement: {P P' : Extension R S} {f : P.Hom P'}
  proof: by
  have eq_map := Ideal.eq_map_of_comap_eq_ker_sup _ h eq
  refine le_antisymm (fun x hx => ?_) (fun x hx => ?_)
  · obtain ⟨x, rfl⟩ := Cotangent.mk_surjective x
    simp only [Submodule.restrictScalars_mem, LinearMap.mem_ker, map_mk, Hom.toAlgHom_apply,
      mk_eq_zero_iff] at hx
    rw [eq_map]

中文:
引理 余切.map_ker_of_surjective
  结论: {P P' : 扩张 R S} {f : P.态射 P'}
  证明: by
  have eq_map := Ideal.eq_map_of_comap_eq_ker_sup _ h eq
  refine le_antisymm (fun x hx => ?_) (fun x hx => ?_)
  · obtain ⟨x, rfl⟩ := Cotangent.mk_surjective x
    simp only [Submodule.restrictScalars_mem, LinearMap.mem_ker, map_mk, Hom.toAlgHom_apply,
      mk_eq_zero_iff] at hx
    rw [eq_map]

Depends on / 依赖: Cotangent, Cotangent.mk_surjective, Hom.toAlgHom_apply, Ideal.comap_map_of_surjective, Ideal.eq_map_of_comap_eq_ker_sup, Ideal.map_pow, Ideal.mem_comap, LinearMap, LinearMap.mem_ker, RingHom, RingHom.ker, Submodule, Submodule.mem_sup, Submodule.restrictScalars_mem, comap_map_of_surjective, eq_map, eq_map_of_comap_eq_ker_sup, f.toRingHom, le_antisymm, map_mk
-/
lemma Cotangent.map_ker_of_surjective {P P' : Extension R S} {f : P.Hom P'}
    (h : Function.Surjective f) (eq : P'.ker.comap f.toRingHom = RingHom.ker f.toRingHom ⊔ P.ker) :
    (Cotangent.map f).ker.restrictScalars P.Ring =
      (Submodule.comap P.ker.subtype (RingHom.ker f.toRingHom ⊓ P.ker)).map Cotangent.mk := by
  have eq_map := Ideal.eq_map_of_comap_eq_ker_sup _ h eq
  refine le_antisymm (fun x hx => ?_) (fun x hx => ?_)
  · obtain ⟨x, rfl⟩ := Cotangent.mk_surjective x
    simp only [Submodule.restrictScalars_mem, LinearMap.mem_ker, map_mk, Hom.toAlgHom_apply,
      mk_eq_zero_iff] at hx
    rw [eq_map]; rw [← Ideal.map_pow]; rw [← Ideal.mem_comap]; rw [Ideal.comap_map_of_surjective' f.toRingHom h]; rw [Submodule.mem_sup] at hx
    rcases hx with ⟨y, y_in, z, z_in, hyz⟩
    suffices exists a, a in RingHom.ker f.toRingHom ∧ a in P.ker ∧ a - x in P.ker ^ 2 by
      simpa [mk_eq_mk_iff_sub_mem]
    refine ⟨z, z_in, ?_, by simpa [← hyz]⟩
    rw [← eq_sub_iff_add_eq'] at hyz
    exact hyz ▸ Ideal.sub_mem _ x.prop (Ideal.pow_le_self (show 2 != 0 by lia) y_in)
  · obtain ⟨x, rfl⟩ := Cotangent.mk_surjective x
    obtain ⟨y, y_in, y_in', hy⟩ : exists a in RingHom.ker f.toRingHom, a in P.ker ∧
      a - x in P.ker ^ 2 := by simpa [mk_eq_mk_iff_sub_mem] using hx
    suffices f.toRingHom x in P'.ker ^ 2 by simpa [mk_eq_zero_iff]
    rw [eq_map]; rw [← Ideal.map_pow]; rw [← Ideal.mem_comap]; rw [Ideal.comap_map_of_surjective' f.toRingHom h]; rw [Submodule.mem_sup]
    exact ⟨x - y, by rwa [← Submodule.neg_mem_iff, neg_sub], y, y_in, by ring⟩

variable (P) in
/--
Definition of `cotangentEquiv` / `cotangentEquiv` 的定义

English:
definition cotangentEquiv
  signature: : S otimes[P.Ring] P.ker ≃ₗ[S] P.Cotangent
  body: by
  refine .ofBijective (Cotangent.mk.liftBaseChange _) ⟨?_, ?_⟩
  · refine (injective_iff_map_eq_zero _).mpr fun x hx => ?_
    obtain ⟨x, rfl⟩ := TensorProduct.mk_surjective P.Ring P.ker S P.algebraMap_surjective x
    simp only [mk_apply, LinearMap.liftBaseChange_tmul, one_smul, Cotangent.mk_eq_

中文:
定义 cotangentEquiv
  签名: : S otimes[P.环] P.ker ≃ₗ[S] P.余切
  定义体: by
  refine .ofBijective (Cotangent.mk.liftBaseChange _) ⟨?_, ?_⟩
  · refine (injective_iff_map_eq_zero _).mpr fun x hx => ?_
    obtain ⟨x, rfl⟩ := TensorProduct.mk_surjective P.Ring P.ker S P.algebraMap_surjective x
    simp only [mk_apply, LinearMap.liftBaseChange_tmul, one_smul, Cotangent.mk_eq_

Depends on / 依赖: Cotangent, Cotangent.mk.liftBaseChange, Cotangent.mk_eq_zero_iff, Ideal.mul_le_left, LinearMap, LinearMap.liftBaseChange_tmul, P.Ring, P.algebraMap_surjective, P.ker, Submodule, Submodule.smul_induction_on, TensorProduct, TensorProduct.mk_surjective, algebraMap_surjective, injective_iff_map_eq_zero, liftBaseChange, liftBaseChange_tmul, mk_apply, mk_eq_zero_iff, mk_surjective
-/
noncomputable def cotangentEquiv : S otimes[P.Ring] P.ker ≃ₗ[S] P.Cotangent := by
  refine .ofBijective (Cotangent.mk.liftBaseChange _) ⟨?_, ?_⟩
  · refine (injective_iff_map_eq_zero _).mpr fun x hx => ?_
    obtain ⟨x, rfl⟩ := TensorProduct.mk_surjective P.Ring P.ker S P.algebraMap_surjective x
    simp only [mk_apply, LinearMap.liftBaseChange_tmul, one_smul, Cotangent.mk_eq_zero_iff,
      pow_two] at hx ⊢
    refine Submodule.smul_induction_on' (p := fun x (hx : x in P.ker * P.ker) =>
      (1 : S) otimesₜ[P.Ring] (⟨x, Ideal.mul_le_left hx⟩ : P.ker) = 0) (hx := hx) ?_ ?_
    · intro r hr s hs
      trans (r • 1) otimesₜ[P.Ring] ⟨s, hs⟩
      · rw [smul_tmul]; rfl
      · simp_all [Algebra.smul_def]
    · intro a ha b hb ha' hb'
      convert! congr($ha' + $hb')
      rw [← tmul_add]
      rfl
  · intro x
    obtain ⟨x, rfl⟩ := Cotangent.mk_surjective x
    exact ⟨1 otimesₜ x, by simp⟩

@[simp]
/--
lemma `contangentEquiv_tmul` / 引理 `contangentEquiv_tmul`

English:
lemma contangentEquiv_tmul
  given: (s : S) (x : P.ker)
  statement: P.cotangentEquiv (s otimesₜ x) = s • .mk x
  proof: rfl

中文:
引理 contangentEquiv_tmul
  条件: (s : S) (x : P.ker)
  结论: P.cotangentEquiv (s otimesₜ x) = s • .mk x
  证明: rfl
-/
lemma contangentEquiv_tmul (s : S) (x : P.ker) : P.cotangentEquiv (s otimesₜ x) = s • .mk x := rfl

end Cotangent

end Algebra.Extension
