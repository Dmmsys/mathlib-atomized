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
  |          |
  ↓          ↓
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
An extension of an `R`-algebra `S` is an `R` algebra `P` together with a surjection `P →ₐ[R] S`.
Also see `Algebra.Extension.ofSurjective`.
-/
/-
**Algebra.Extension** 是 Mathlib 中的一个归纳类型，位于命名空间 `Algebra`。
形式化陈述：(R : Type u) → (S : Type v) → [inst : CommRing R] → [inst_1 : CommRing S] 
→ [Algebra R S] → Type (max (max u v) (w + 1))
参数：max u v；w + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An extension of an `R`-algebra `S` is an `R` algebra `P` together with a surject
ion `P →ₐ[R] S`.
Also see `Algebra.Extension.ofSurjective`.
-/
structure Algebra.Extension where
  /-- The underlying algebra of an extension. -/
  Ring : Type w
  [commRing : CommRing Ring]
  [algebra₁ : Algebra R Ring]
  [algebra₂ : Algebra Ring S]
  [isScalarTower : IsScalarTower R Ring S]
  /-- A chosen (set-theoretic) section of an extension. -/
  σ : S → Ring
  algebraMap_σ : ∀ x, algebraMap Ring S (σ x) = x

namespace Algebra.Extension

variable {R S}
variable (P : Extension.{w} R S)

attribute [instance] commRing algebra₁ algebra₂ isScalarTower

attribute [simp] algebraMap_σ

-- We want to make sure `R₀` acts compatibly on `R` and `S` to avoid nonsensical instances
@[nolint unusedArguments]
/-
**Algebra.Extension.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra.Extension`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance {R₀} [CommRing R₀] [Algebra R₀ R] [Algebra R₀ S] [IsScalarTower R₀ R S] :
    Algebra R₀ P.Ring := Algebra.compHom P.Ring (algebraMap R₀ R)
/-
**Algebra.Extension.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra.Extension`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R₀} [CommRing R₀] [Algebra R₀ R] [Algebra R₀ S] [IsScalarTower R₀ R S] :
    IsScalarTower R₀ R P.Ring := IsScalarTower.of_algebraMap_eq' rfl
/-
**Algebra.Extension.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra.Extension`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R₀} [CommRing R₀] [Algebra R₀ R] [Algebra R₀ S] [IsScalarTower R₀ R S]
    {R₁} [CommRing R₁] [Algebra R₁ R] [Algebra R₁ S] [IsScalarTower R₁ R S]
    [Algebra R₀ R₁] [IsScalarTower R₀ R₁ R] :
    IsScalarTower R₀ R₁ P.Ring := IsScalarTower.of_algebraMap_eq' <| by
  rw [IsScalarTower.algebraMap_eq R₀ R, IsScalarTower.algebraMap_eq R₁ R,
    RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq R₀ R₁ R]
/-
**Algebra.Extension.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra.Extension`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R₀} [CommRing R₀] [Algebra R₀ R] [Algebra R₀ S] [IsScalarTower R₀ R S] :
    IsScalarTower R₀ P.Ring S := IsScalarTower.of_algebraMap_eq' <| by
  rw [IsScalarTower.algebraMap_eq R₀ R P.Ring, ← RingHom.comp_assoc,
    ← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq]

@[simp]
/-
**Algebra.Extension.** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.Extension`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma σ_smul (x y) : P.σ x • y = x * y := by
  rw [Algebra.smul_def, algebraMap_σ]
/-
**Algebra.Extension.** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.Extension`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma σ_injective : P.σ.Injective := by
  intro x y e
  rw [← P.algebraMap_σ x, ← P.algebraMap_σ y, e]
/-
**Algebra.Extension.algebraMap_surjective** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.Ext
ension`。
形式化陈述：algebraMap_surjective : Function.Surjective (algebraMap P.Ring S)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.Extension.algebraMap_σ`：∀ {R : Type u} {S : Type v} [inst : Comm
Ring R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   (self : Algebra.Extension
 R S) (x : S), (alge…
-/
lemma algebraMap_surjective : Function.Surjective (algebraMap P.Ring S) := (⟨_, P.algebraMap_σ ·⟩)

section Construction

/-- Construct `Extension` from a surjective algebra homomorphism. -/
@[simps -isSimp Ring σ]
noncomputable
/-
**Algebra.Extension.ofSurjective** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.Extension`。
形式化陈述：ofSurjective {P : Type w} [CommRing P] [Algebra R P] (f : P ->ₐ[R] S) (h :
 Function.Surjective f) : Extension.{w} R S where Ring
参数：f : P ->ₐ[R] S；h : Function.Surjective f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def ofSurjective {P : Type w} [CommRing P] [Algebra R P] (f : P →ₐ[R] S)
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
/-
**Algebra.Extension.self** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.Extension`。
形式化陈述：self : Extension R S where Ring
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def self : Extension R S where
  Ring := S
  σ := _root_.id
  algebraMap_σ _ := rfl

/-- The kernel of an extension. -/
/-
**Algebra.Extension.ker** 是 Mathlib 中的一个缩写定义，位于命名空间 `Algebra.Extension`。
形式化陈述：ker : Ideal P.Ring
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The kernel of an extension.
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
/-
**Algebra.Extension.localization** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.Extension`。
形式化陈述：localization (P : Extension.{w} R S) : Extension R S' where Ring
参数：P : Extension.{w} R S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def localization (P : Extension.{w} R S) : Extension R S' where
  Ring := Localization (M.comap (algebraMap P.Ring S))
  algebra₂ := (IsLocalization.lift (M := (M.comap (algebraMap P.Ring S)))
      (g := (algebraMap S S').comp (algebraMap P.Ring S))
      (by simpa using fun x hx ↦ IsLocalization.map_units S' ⟨_, hx⟩)).toAlgebra
  isScalarTower := by
    let : Algebra (Localization (M.comap (algebraMap P.Ring S))) S' :=
      (IsLocalization.lift (M := (M.comap (algebraMap P.Ring S)))
        (g := (algebraMap S S').comp (algebraMap P.Ring S))
        (by simpa using fun x hx ↦ IsLocalization.map_units S' ⟨_, hx⟩)).toAlgebra
    apply IsScalarTower.of_algebraMap_eq'
    rw [RingHom.algebraMap_toAlgebra, IsScalarTower.algebraMap_eq R P.Ring (Localization _),
      ← RingHom.comp_assoc, IsLocalization.lift_comp, RingHom.comp_assoc,
      ← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq]
  σ s := Localization.mk (P.σ (IsLocalization.sec M s).1) ⟨P.σ (IsLocalization.sec M s).2, by simp⟩
  algebraMap_σ s := by
    simp [RingHom.algebraMap_toAlgebra, Localization.mk_eq_mk', IsLocalization.lift_mk',
      Units.mul_inv_eq_iff_eq_mul, IsUnit.coe_liftRight, IsLocalization.sec_spec]

end Localization

variable {T} [CommRing T] [Algebra R T]

/-- The base change of an `R`-extension of `S` to `T` gives a `T`-extension of `T ⊗[R] S`. -/
noncomputable
/-
**Algebra.Extension.baseChange** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.Extension`。
形式化陈述：baseChange {T} [CommRing T] [Algebra R T] (P : Extension R S) : Extension 
T (T otimes[R] S) where Ring
参数：P : Extension R S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def baseChange {T} [CommRing T] [Algebra R T] (P : Extension R S) : Extension T (T ⊗[R] S) where
  Ring := T ⊗[R] P.Ring
  __ := ofSurjective (P := T ⊗[R] P.Ring) (Algebra.TensorProduct.map (AlgHom.id T T)
    (IsScalarTower.toAlgHom _ _ _)) (LinearMap.lTensor_surjective T
    (g := (IsScalarTower.toAlgHom R P.Ring S).toLinearMap) P.algebraMap_surjective)

variable (T) in
/-
**Algebra.Extension.ker_baseChange** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.Extension`
。
形式化陈述：ker_baseChange : (P.baseChange (T
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Algebra.TensorProduct.lTensor_ker`：Algebra.TensorProduct.lTensor_ker (hg
 : Function.Surjective g) : RingHom.ker (map (AlgHom.id R A) g) = (RingHom.ker g
).map (Algebra.TensorPr…
· 使用定理 `Algebra.Extension.instIsScalarTowerRing_2`：∀ {R : Type u} {S : Type v} [
inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] (P : Algebra.Ext
ension R S)   {R₀ : Type u_1} […
· 使用引理 `Algebra.Extension.algebraMap_surjective`：algebraMap_surjective : Functio
n.Surjective (algebraMap P.Ring S)
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
/-
**Algebra.Extension.algebraBaseChange** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.Extensi
on`。
形式化陈述：algebraBaseChange : Algebra P.Ring (P.baseChange (T
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The ring `T ⊗[R] P.Ring` underlying the extension `P.baseChange T` is a `P.Ring`
-algebra
by action on the right. This causes a (mathematical) diamond when `T = P.Ring`, 
so it is
not an instance.
-/
noncomputable def algebraBaseChange : Algebra P.Ring (P.baseChange (T := T)).Ring :=
  fast_instance% TensorProduct.rightAlgebra

set_option backward.isDefEq.respectTransparency false in
attribute [local instance] algebraBaseChange in
/-
**Algebra.Extension.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra.Extension`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsScalarTower R P.Ring (P.baseChange (T := T)).Ring :=
  .of_algebraMap_eq fun x ↦ by simp [baseChange, RingHom.algebraMap_toAlgebra]; rfl

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
|          |
↓          ↓
R' -→ P' → S
```
A hom between `P` and `P'` is a ring homomorphism that makes the two squares commute.
-/
@[ext]
/-
**Algebra.Extension.Hom** 是 Mathlib 中的一个归纳类型，位于命名空间 `Algebra.Extension`。
形式化陈述：{R : Type u} →   {S : Type v} →     [inst : CommRing R] →       [inst_1 : 
CommRing S] →         [inst_2 : Algebra R S] →           Algebra.Extension R S →
             {R' : Type u_1} →               {S' : Type u_2} →                 [
inst_3 : CommRing R'] →                   [inst_4 : CommRing S'] →              
       [inst_5 : Algebra R' S'] →                       Algebra.Extension R' S' 
→ [Algebra R R'] → [Algebra S S'] → Type (max u_3 w)
参数：max u_3 w。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a commuting square
```
R --→ P -→ S
|          |
↓          ↓
R' -→ P' → S
```
A hom between `P` and `P'` is a ring homomorphism that makes the two squares com
mute.
-/
structure Hom where
  /-- The underlying ring homomorphism of a hom between extensions. -/
  toRingHom : P.Ring →+* P'.Ring
  toRingHom_algebraMap :
    ∀ x, toRingHom (algebraMap R P.Ring x) = algebraMap R' P'.Ring (algebraMap R R' x)
  algebraMap_toRingHom :
    ∀ x, (algebraMap P'.Ring S' (toRingHom x)) = algebraMap S S' (algebraMap P.Ring S x)

attribute [simp] Hom.toRingHom_algebraMap Hom.algebraMap_toRingHom

variable {P P'}

/-- A hom between extensions as an algebra homomorphism. -/
noncomputable
/-
**Algebra.Extension.Hom.toAlgHom** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.Extension.Ho
m`。
形式化陈述：{R : Type u} →   {S : Type v} →     [inst : CommRing R] →       [inst_1 : 
CommRing S] →         [inst_2 : Algebra R S] →           {P : Algebra.Extension 
R S} →             {R' : Type u_1} →               {S' : Type u_2} →            
     [inst_3 : CommRing R'] →                   [inst_4 : CommRing S'] →        
             [inst_5 : Algebra R' S'] →                       {P' : Algebra.Exte
nsion R' S'} →                         [inst_6 : Algebra R R'] →                
           [inst_7 : Algebra S S'] →                             [inst_8 : Algeb
ra R S'] → [inst_9 : IsScalarTower R R' S'] → P.Hom P' → P.Ring →ₐ[R] P'.Ring
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def Hom.toAlgHom [Algebra R S'] [IsScalarTower R R' S'] (f : Hom P P') :
    P.Ring →ₐ[R] P'.Ring where
  __ := f.toRingHom
  commutes' := by simp [← IsScalarTower.algebraMap_apply]

@[simp]
/-
**Algebra.Extension.Hom.toAlgHom_apply** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.Extens
ion.Hom`。
形式化陈述：∀ {R : Type u} {S : Type v} [inst : CommRing R] [inst_1 : CommRing S] [ins
t_2 : Algebra R S] {P : Algebra.Extension R S}   {R' : Type u_2} {S' : Type u_1}
 [inst_3 : CommRing R'] [inst_4 : CommRing S'] [inst_5 : Algebra R' S']   {P' : 
Algebra.Extension R' S'} [inst_6 : Algebra R R'] [inst_7 : Algebra S S'] [inst_8
 : Algebra R S']   [inst_9 : IsScalarTower R R' S'] (f : P.Hom P') (x : P.Ring),
 f.toAlgHom x = f.toRingHom x
参数：f : P.Hom P'；x : P.Ring。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Hom.toAlgHom_apply [Algebra R S'] [IsScalarTower R R' S'] (f : Hom P P') (x) :
    f.toAlgHom x = f.toRingHom x := rfl

/-- A hom of extensions `P → P'` can be constructed from an algebra map
`P.Ring →ₐ[R] P'.Ring`. -/
@[simps]
/-
**Algebra.Extension.Hom.ofAlgHom** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.Extension.Ho
m`。
形式化陈述：{R : Type u} →   {S : Type v} →     [inst : CommRing R] →       [inst_1 : 
CommRing S] →         [inst_2 : Algebra R S] →           {P : Algebra.Extension 
R S} →             {R' : Type u_1} →               {S' : Type u_2} →            
     [inst_3 : CommRing R'] →                   [inst_4 : CommRing S'] →        
             [inst_5 : Algebra R' S'] →                       {P' : Algebra.Exte
nsion R' S'} →                         [inst_6 : Algebra R R'] →                
           [inst_7 : Algebra S S'] →                             [inst_8 : Algeb
ra R S'] →                               [inst_9 : IsScalarTower R R' S'] →     
                            [inst_10 : IsScalarTower R S S'] →                  
                 (f : P.Ring →ₐ[R] P'.Ring) →                                   
  (IsScalarTower.toAlgHom R P'.Ring S').comp f =                                
         (IsScalarTower.toAlgHom R S S').comp (IsScalarTower.toAlgHom R P.Ring S
) →                                       P.Hom P'
参数：f : P.Ring →ₐ[R] P'.Ring；IsScalarTower.toAlgHom R P'.Ring S'；IsScalarTower.to
AlgHom R S S'；IsScalarTower.toAlgHom R P.Ring S。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.Extension.instIsScalarTowerRing_2`：∀ {R : Type u} {S : Type v} [
inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] (P : Algebra.Ext
ension R S)   {R₀ : Type u_1} […

--- 原说明 ---
A hom of extensions `P → P'` can be constructed from an algebra map
`P.Ring →ₐ[R] P'.Ring`.
-/
def Hom.ofAlgHom [Algebra R S'] [IsScalarTower R R' S'] [IsScalarTower R S S']
    (f : P.Ring →ₐ[R] P'.Ring)
    (H : (IsScalarTower.toAlgHom R P'.Ring S').comp f =
      (IsScalarTower.toAlgHom R S S').comp (IsScalarTower.toAlgHom R P.Ring S)) :
    P.Hom P' where
  toRingHom := f.toRingHom
  toRingHom_algebraMap := f.commutes'
  algebraMap_toRingHom x := congr($H x)

@[simp]
/-
**Algebra.Extension.Hom.toAlgHom_ofAlgHom** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.Ext
ension.Hom`。
形式化陈述：∀ {R : Type u} {S : Type v} [inst : CommRing R] [inst_1 : CommRing S] [ins
t_2 : Algebra R S] {P : Algebra.Extension R S}   {R' : Type u_2} {S' : Type u_1}
 [inst_3 : CommRing R'] [inst_4 : CommRing S'] [inst_5 : Algebra R' S']   {P' : 
Algebra.Extension R' S'} [inst_6 : Algebra R R'] [inst_7 : Algebra S S'] [inst_8
 : Algebra R S']   [inst_9 : IsScalarTower R R' S'] [inst_10 : IsScalarTower R S
 S'] (f : P.Ring →ₐ[R] P'.Ring)   (H :     (IsScalarTower.toAlgHom R P'.Ring S')
.comp f =       (IsScalarTower.toAlgHom R S S').comp (IsScalarTower.toAlgHom R P
.Ring S)),   (Algebra.Extension.Hom.ofAlgHom f H).toAlgHom = f
参数：f : P.Ring →ₐ[R] P'.Ring；H :     (IsScalarTower.toAlgHom R P'.Ring S').comp f
 =       (IsScalarTower.toAlgHom R S S').comp (IsScalarTower.toAlgHom R P.Ring S
)；Algebra.Extension.Hom.ofAlgHom f H。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.Extension.instIsScalarTowerRing_2`：∀ {R : Type u} {S : Type v} [
inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] (P : Algebra.Ext
ension R S)   {R₀ : Type u_1} […
-/
lemma Hom.toAlgHom_ofAlgHom [Algebra R S'] [IsScalarTower R R' S'] [IsScalarTower R S S']
    (f : P.Ring →ₐ[R] P'.Ring)
    (H : (IsScalarTower.toAlgHom R P'.Ring S').comp f =
      (IsScalarTower.toAlgHom R S S').comp (IsScalarTower.toAlgHom R P.Ring S)) :
    (Hom.ofAlgHom f H).toAlgHom = f :=
  rfl

variable (P P')

/-- The identity hom. -/
@[simps]
/-
**Algebra.Extension.Hom.id** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.Extension.Hom`。
形式化陈述：{R : Type u} →   {S : Type v} →     [inst : CommRing R] → [inst_1 : CommRi
ng S] → [inst_2 : Algebra R S] → (P : Algebra.Extension R S) → P.Hom P
参数：P : Algebra.Extension R S。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity hom.
-/
protected noncomputable def Hom.id : Hom P P := ⟨RingHom.id _, by simp, by simp⟩

@[simp]
/-
**Algebra.Extension.Hom.toAlgHom_id** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.Extension
.Hom`。
形式化陈述：∀ {R : Type u} {S : Type v} [inst : CommRing R] [inst_1 : CommRing S] [ins
t_2 : Algebra R S]   (P : Algebra.Extension R S), (Algebra.Extension.Hom.id P).t
oAlgHom = AlgHom.id R P.Ring
参数：P : Algebra.Extension R S；Algebra.Extension.Hom.id P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.Extension.Hom.id_toRingHom`：∀ {R : Type u} {S : Type v} [inst : 
CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   (P : Algebra.Extensio
n R S), (Algebra.Extensi…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Hom.toAlgHom_id : Hom.toAlgHom (.id P) = AlgHom.id _ _ := by ext1; simp

variable {P P' P''}

variable [IsScalarTower R R' R''] [IsScalarTower S S' S''] in
/-- The composition of two homs. -/
@[simps]
/-
**Algebra.Extension.Hom.comp** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.Extension.Hom`。
形式化陈述：{R : Type u} →   {S : Type v} →     [inst : CommRing R] →       [inst_1 : 
CommRing S] →         [inst_2 : Algebra R S] →           {P : Algebra.Extension 
R S} →             {R' : Type u_1} →               {S' : Type u_2} →            
     [inst_3 : CommRing R'] →                   [inst_4 : CommRing S'] →        
             [inst_5 : Algebra R' S'] →                       {P' : Algebra.Exte
nsion R' S'} →                         {R'' : Type u_4} →                       
    {S'' : Type u_5} →                             [inst_6 : CommRing R''] →    
                           [inst_7 : CommRing S''] →                            
     [inst_8 : Algebra R'' S''] →                                   {P'' : Algeb
ra.Extension R'' S''} →                                     [inst_9 : Algebra R 
R'] →                                       [inst_10 : Algebra R' R''] →        
                                 [inst_11 : Algebra R R''] →                    
                       [inst_12 : Algebra S S'] →                               
              [inst_13 : Algebra S' S''] →                                      
         [inst_14 : Algebra S S''] →                                            
     [IsScalarTower R R' R''] →                                                 
  [IsScalarTower S S' S''] → P'.Hom P'' → P.Hom P' → P.Hom P''
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The composition of two homs.
-/
noncomputable def Hom.comp (f : Hom P' P'') (g : Hom P P') : Hom P P'' where
  toRingHom := f.toRingHom.comp g.toRingHom
  toRingHom_algebraMap := by simp [← IsScalarTower.algebraMap_apply]
  algebraMap_toRingHom := by simp [← IsScalarTower.algebraMap_apply]

@[simp]
/-
**Algebra.Extension.Hom.comp_id** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.Extension.Hom
`。
形式化陈述：∀ {R : Type u} {S : Type v} [inst : CommRing R] [inst_1 : CommRing S] [ins
t_2 : Algebra R S] {P : Algebra.Extension R S}   {R' : Type u_1} {S' : Type u_2}
 [inst_3 : CommRing R'] [inst_4 : CommRing S'] [inst_5 : Algebra R' S']   {P' : 
Algebra.Extension R' S'} [inst_6 : Algebra R R'] [inst_7 : Algebra S S'] (f : P.
Hom P'),   f.comp (Algebra.Extension.Hom.id P) = f
参数：f : P.Hom P'；Algebra.Extension.Hom.id P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.Extension.Hom.ext`：∀ {R : Type u} {S : Type v} {inst : CommRing 
R} {inst_1 : CommRing S} {inst_2 : Algebra R S} {P : Algebra.Extension R S}   {R
' : Type u_1} {…
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.Extension.Hom.comp_toRingHom`：∀ {R : Type u} {S : Type v} [inst 
: CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {P : Algebra.Extensio
n R S}   {R' : Type u_1} {…
· 使用定理 `Algebra.Extension.Hom.id_toRingHom`：∀ {R : Type u} {S : Type v} [inst : 
CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   (P : Algebra.Extensio
n R S), (Algebra.Extensi…
· 使用定理 `RingHomCompTriple.comp_eq`：∀ {R₁ : Type u_1} {R₂ : Type u_2} {R₃ : Type 
u_3} {inst : Semiring R₁} {inst_1 : Semiring R₂} {inst_2 : Semiring R₃}   {σ₁₂ :
 R₁ →+* R₂} {σ₂…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Hom.comp_id (f : Hom P P') : f.comp (Hom.id P) = f := by ext; simp

@[simp]
/-
**Algebra.Extension.Hom.id_comp** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.Extension.Hom
`。
形式化陈述：∀ {R : Type u} {S : Type v} [inst : CommRing R] [inst_1 : CommRing S] [ins
t_2 : Algebra R S] {P : Algebra.Extension R S}   {R' : Type u_1} {S' : Type u_2}
 [inst_3 : CommRing R'] [inst_4 : CommRing S'] [inst_5 : Algebra R' S']   {P' : 
Algebra.Extension R' S'} [inst_6 : Algebra R R'] [inst_7 : Algebra S S'] (f : P.
Hom P'),   (Algebra.Extension.Hom.id P').comp f = f
参数：f : P.Hom P'；Algebra.Extension.Hom.id P'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.Extension.Hom.ext`：∀ {R : Type u} {S : Type v} {inst : CommRing 
R} {inst_1 : CommRing S} {inst_2 : Algebra R S} {P : Algebra.Extension R S}   {R
' : Type u_1} {…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.Extension.Hom.comp_toRingHom`：∀ {R : Type u} {S : Type v} [inst 
: CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {P : Algebra.Extensio
n R S}   {R' : Type u_1} {…
· 使用定理 `RingHomCompTriple.comp_eq`：∀ {R₁ : Type u_1} {R₂ : Type u_2} {R₃ : Type 
u_3} {inst : Semiring R₁} {inst_1 : Semiring R₂} {inst_2 : Semiring R₃}   {σ₁₂ :
 R₁ →+* R₂} {σ₂…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Hom.id_comp (f : Hom P P') : (Hom.id P').comp f = f := by
  ext; simp [Hom.id]

/-- A map between extensions induce a map between kernels. -/
@[simps]
/-
**Algebra.Extension.Hom.mapKer** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.Extension.Hom`
。
形式化陈述：{R : Type u} →   {S : Type v} →     [inst : CommRing R] →       [inst_1 : 
CommRing S] →         [inst_2 : Algebra R S] →           {P : Algebra.Extension 
R S} →             {R' : Type u_1} →               {S' : Type u_2} →            
     [inst_3 : CommRing R'] →                   [inst_4 : CommRing S'] →        
             [inst_5 : Algebra R' S'] →                       {P' : Algebra.Exte
nsion R' S'} →                         [inst_6 : Algebra R R'] →                
           [inst_7 : Algebra S S'] →                             (f : P.Hom P') 
→                               [alg : Algebra P.Ring P'.Ring] →                
                 algebraMap P.Ring P'.Ring = f.toRingHom → ↥P.ker →ₗ[P.Ring] ↥P'
.ker
参数：f : P.Hom P'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A map between extensions induce a map between kernels.
-/
def Hom.mapKer (f : P.Hom P')
    [alg : Algebra P.Ring P'.Ring] (halg : algebraMap P.Ring P'.Ring = f.toRingHom) :
    P.ker →ₗ[P.Ring] P'.ker where
  toFun x := ⟨f.toRingHom x, by simp [show algebraMap P.Ring S x = 0 from x.2]⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' := by simp [Algebra.smul_def, ← halg]

set_option backward.isDefEq.respectTransparency false in
attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- The canonical hom from `P` to its base change `P.baseChange`. -/
@[simps]
/-
**Algebra.Extension.toBaseChange** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.Extension`。
形式化陈述：toBaseChange (T : Type*) [CommRing T] [Algebra R T] : P.Hom (P.baseChange 
(T
参数：T : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical hom from `P` to its base change `P.baseChange`.
-/
noncomputable def toBaseChange (T : Type*) [CommRing T] [Algebra R T] :
    P.Hom (P.baseChange (T := T)) where
  toRingHom := TensorProduct.includeRight.toRingHom
  toRingHom_algebraMap x := by simp [baseChange]
  algebraMap_toRingHom x := rfl

end

/-
**Algebra.Extension.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra.Extension`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {P P' : Extension R S} : FunLike (P.Hom P') P.Ring P'.Ring where
  coe f := f.toRingHom
  coe_injective _ _ h := Extension.Hom.ext (DFunLike.coe_fn_eq.mp h)

end Hom

section Infinitesimal

/-- Given an `R`-algebra extension `0 → I → P → S → 0` of `S`,
the infinitesimal extension associated to it is `0 → I/I² → P/I² → S → 0`. -/
noncomputable
/-
**Algebra.Extension.infinitesimal** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.Extension`。
形式化陈述：infinitesimal (P : Extension R S) : Extension R S where Ring
参数：P : Extension R S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def infinitesimal (P : Extension R S) : Extension R S where
  Ring := P.Ring ⧸ P.ker ^ 2
  σ := Ideal.Quotient.mk _ ∘ P.σ
  algebraMap_σ x := by dsimp; exact P.algebraMap_σ x

/-- The canonical map `P → P/I²` as maps between extensions. -/
noncomputable
/-
**Algebra.Extension.toInfinitesimal** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.Extension
`。
形式化陈述：toInfinitesimal (P : Extension R S) : P.Hom P.infinitesimal where toRingHo
m
参数：P : Extension R S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def toInfinitesimal (P : Extension R S) : P.Hom P.infinitesimal where
  toRingHom := Ideal.Quotient.mk _
  toRingHom_algebraMap _ := rfl
  algebraMap_toRingHom _ := rfl
/-
**Algebra.Extension.ker_infinitesimal** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.Extensi
on`。
形式化陈述：ker_infinitesimal (P : Extension R S) : P.infinitesimal.ker = P.ker.cotang
entIdeal
参数：P : Extension R S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.ker_kerSquareLift`：∀ {R : Type u} [inst : CommRing R] {A : Type u
_1} {B : Type u_2} [inst_1 : CommRing A] [inst_2 : CommRing B]   [inst_3 : Algeb
ra R A] [inst_…
-/
lemma ker_infinitesimal (P : Extension R S) :
    P.infinitesimal.ker = P.ker.cotangentIdeal :=
  AlgHom.ker_kerSquareLift _

end Infinitesimal

section Cotangent

/-- The cotangent space of an extension.
This is a type synonym so that `P.Ring` can act on it through the action of `S` without creating
a diamond. -/
/-
**Algebra.Extension.Cotangent** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.Extension`。
形式化陈述：Cotangent : Type _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cotangent space of an extension.
This is a type synonym so that `P.Ring` can act on it through the action of `S` 
without creating
a diamond.
-/
def Cotangent : Type _ := P.ker.Cotangent

noncomputable
/-
**Algebra.Extension.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra.Extension`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddCommGroup P.Cotangent := inferInstanceAs (AddCommGroup P.ker.Cotangent)

variable {P}

/-- The identity map `P.ker.Cotangent → P.Cotangent` into the type synonym. -/
/-
**Algebra.Extension.Cotangent.of** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.Extension.Co
tangent`。
形式化陈述：{R : Type u} →   {S : Type v} →     [inst : CommRing R] →       [inst_1 : 
CommRing S] → [inst_2 : Algebra R S] → {P : Algebra.Extension R S} → P.ker.Cotan
gent → P.Cotangent
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity map `P.ker.Cotangent → P.Cotangent` into the type synonym.
-/
def Cotangent.of (x : P.ker.Cotangent) : P.Cotangent := x

/-- The identity map `P.Cotangent → P.ker.Cotangent` from the type synonym. -/
/-
**Algebra.Extension.Cotangent.val** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.Extension.C
otangent`。
形式化陈述：{R : Type u} →   {S : Type v} →     [inst : CommRing R] →       [inst_1 : 
CommRing S] → [inst_2 : Algebra R S] → {P : Algebra.Extension R S} → P.Cotangent
 → P.ker.Cotangent
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity map `P.Cotangent → P.ker.Cotangent` from the type synonym.
-/
def Cotangent.val (x : P.Cotangent) : P.ker.Cotangent := x

@[ext]
/-
**Algebra.Extension.Cotangent.ext** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.Extension.C
otangent`。
形式化陈述：∀ {R : Type u} {S : Type v} [inst : CommRing R] [inst_1 : CommRing S] [ins
t_2 : Algebra R S] {P : Algebra.Extension R S}   {x y : P.Cotangent}, x.val = y.
val → x = y
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Cotangent.ext {x y : P.Cotangent} (e : x.val = y.val) : x = y := e

namespace Cotangent

variable (x y : P.Cotangent) (w z : P.ker.Cotangent)

/-
**Algebra.Extension.Cotangent.val_add** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.Extensi
on.Cotangent`。
形式化陈述：∀ {R : Type u} {S : Type v} [inst : CommRing R] [inst_1 : CommRing S] [ins
t_2 : Algebra R S] {P : Algebra.Extension R S}   (x y : P.Cotangent), (x + y).va
l = x.val + y.val
参数：x y : P.Cotangent；x + y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma val_add : (x + y).val = x.val + y.val := rfl
/-
**Algebra.Extension.Cotangent.val_zero** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.Extens
ion.Cotangent`。
形式化陈述：∀ {R : Type u} {S : Type v} [inst : CommRing R] [inst_1 : CommRing S] [ins
t_2 : Algebra R S]   {P : Algebra.Extension R S}, Algebra.Extension.Cotangent.va
l 0 = 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma val_zero : (0 : P.Cotangent).val = 0 := rfl
/-
**Algebra.Extension.Cotangent.of_add** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.Extensio
n.Cotangent`。
形式化陈述：∀ {R : Type u} {S : Type v} [inst : CommRing R] [inst_1 : CommRing S] [ins
t_2 : Algebra R S] {P : Algebra.Extension R S}   (w z : P.ker.Cotangent),   Alge
bra.Extension.Cotangent.of (w + z) = Algebra.Extension.Cotangent.of w + Algebra.
Extension.Cotangent.of z
参数：w z : P.ker.Cotangent；w + z。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma of_add : of (w + z) = of w + of z := rfl
/-
**Algebra.Extension.Cotangent.of_zero** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.Extensi
on.Cotangent`。
形式化陈述：∀ {R : Type u} {S : Type v} [inst : CommRing R] [inst_1 : CommRing S] [ins
t_2 : Algebra R S]   {P : Algebra.Extension R S}, Algebra.Extension.Cotangent.of
 0 = 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma of_zero : (of 0 : P.Cotangent) = 0 := rfl
/-
**Algebra.Extension.Cotangent.of_val** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.Extensio
n.Cotangent`。
形式化陈述：∀ {R : Type u} {S : Type v} [inst : CommRing R] [inst_1 : CommRing S] [ins
t_2 : Algebra R S] {P : Algebra.Extension R S}   (x : P.Cotangent), Algebra.Exte
nsion.Cotangent.of x.val = x
参数：x : P.Cotangent。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma of_val : of x.val = x := rfl
/-
**Algebra.Extension.Cotangent.val_of** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.Extensio
n.Cotangent`。
形式化陈述：∀ {R : Type u} {S : Type v} [inst : CommRing R] [inst_1 : CommRing S] [ins
t_2 : Algebra R S] {P : Algebra.Extension R S}   (w : P.ker.Cotangent), (Algebra
.Extension.Cotangent.of w).val = w
参数：w : P.ker.Cotangent；Algebra.Extension.Cotangent.of w。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma val_of : (of w).val = w := rfl
/-
**Algebra.Extension.Cotangent.val_sub** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.Extensi
on.Cotangent`。
形式化陈述：∀ {R : Type u} {S : Type v} [inst : CommRing R] [inst_1 : CommRing S] [ins
t_2 : Algebra R S] {P : Algebra.Extension R S}   (x y : P.Cotangent), (x - y).va
l = x.val - y.val
参数：x y : P.Cotangent；x - y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma val_sub : (x - y).val = x.val - y.val := rfl

end Cotangent

/-
**Algebra.Extension.Cotangent.smul_eq_zero_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Alg
ebra.Extension.Cotangent`。
形式化陈述：∀ {R : Type u} {S : Type v} [inst : CommRing R] [inst_1 : CommRing S] [ins
t_2 : Algebra R S]   {P : Algebra.Extension R S}, ∀ p ∈ P.ker, ∀ (m : P.ker.Cota
ngent), p • m = 0
参数：m : P.ker.Cotangent。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.Cotangent.smul_eq_zero_of_mem`：∀ {R : Type u} [inst : CommRing R] 
{I : Ideal R} {x : R}, x ∈ I → ∀ (m : I.Cotangent), x • m = 0
-/
lemma Cotangent.smul_eq_zero_of_mem (p : P.Ring) (hp : p ∈ P.ker) (m : P.ker.Cotangent) :
    p • m = 0 :=
  Ideal.Cotangent.smul_eq_zero_of_mem hp m

attribute [local simp] RingHom.mem_ker

set_option backward.isDefEq.respectTransparency.types false in
noncomputable
/-
**Algebra.Extension.Cotangent.module** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.Extensio
n.Cotangent`。
形式化陈述：{R : Type u} →   {S : Type v} →     [inst : CommRing R] →       [inst_1 : 
CommRing S] → [inst_2 : Algebra R S] → {P : Algebra.Extension R S} → _root_.Modu
le S P.Cotangent
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Cotangent.module : Module S P.Cotangent where
  smul := fun r s ↦ .of (P.σ r • s.val)
  smul_zero := fun r ↦ ext (smul_zero (P.σ r))
  smul_add := fun r x y ↦ ext (smul_add (P.σ r) x.val y.val)
  add_smul := fun r s x ↦ by
    have := smul_eq_zero_of_mem (P.σ (r + s) - (P.σ r + P.σ s) : P.Ring) (by simp) x
    simpa only [sub_smul, add_smul, sub_eq_zero]
  zero_smul := fun x ↦ smul_eq_zero_of_mem (P.σ 0 : P.Ring) (by simp) x
  one_smul := fun x ↦ by
    have := smul_eq_zero_of_mem (P.σ 1 - 1 : P.Ring) (by simp) x
    simpa [sub_eq_zero, sub_smul]
  mul_smul := fun r s x ↦ by
    have := smul_eq_zero_of_mem (P.σ (r * s) - (P.σ r * P.σ s) : P.Ring) (by simp) x
    simpa only [sub_smul, mul_smul, sub_eq_zero] using! this

noncomputable
/-
**Algebra.Extension.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra.Extension`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R₀} [CommRing R₀] [Algebra R₀ S] : Module R₀ P.Cotangent :=
  Module.compHom P.Cotangent (algebraMap R₀ S)
/-
**Algebra.Extension.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra.Extension`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R₁ R₂} [CommRing R₁] [CommRing R₂] [Algebra R₁ S] [Algebra R₂ S] [Algebra R₁ R₂]
    [IsScalarTower R₁ R₂ S] :
    IsScalarTower R₁ R₂ P.Cotangent := by
  constructor
  intro r s m
  change algebraMap R₂ S (r • s) • m = (algebraMap _ S r) • (algebraMap _ S s) • m
  rw [Algebra.smul_def, map_mul, mul_smul, ← IsScalarTower.algebraMap_apply]

set_option backward.isDefEq.respectTransparency.types false in
/-- The action of `R₀` on `P.Cotangent` for an extension `P → S`, if `S` is an `R₀` algebra. -/
/-
**Algebra.Extension.Cotangent.val_smul'''** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.Ext
ension.Cotangent`。
形式化陈述：∀ {R : Type u} {S : Type v} [inst : CommRing R] [inst_1 : CommRing S] [ins
t_2 : Algebra R S] {P : Algebra.Extension R S}   {R₀ : Type u_1} [inst_3 : CommR
ing R₀] [inst_4 : Algebra R₀ S] (r : R₀) (x : P.Cotangent),   (r • x).val = P.σ 
((algebraMap R₀ S) r) • x.val
参数：r : R₀；x : P.Cotangent；r • x；(algebraMap R₀ S) r。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The action of `R₀` on `P.Cotangent` for an extension `P → S`, if `S` is an `R₀` 
algebra.
-/
lemma Cotangent.val_smul''' {R₀} [CommRing R₀] [Algebra R₀ S] (r : R₀) (x : P.Cotangent) :
    (r • x).val = P.σ (algebraMap R₀ S r) • x.val := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- The action of `S` on `P.Cotangent` for an extension `P → S`. -/
@[simp]
/-
**Algebra.Extension.Cotangent.val_smul** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.Extens
ion.Cotangent`。
形式化陈述：∀ {R : Type u} {S : Type v} [inst : CommRing R] [inst_1 : CommRing S] [ins
t_2 : Algebra R S] {P : Algebra.Extension R S}   (r : S) (x : P.Cotangent), (r •
 x).val = P.σ r • x.val
参数：r : S；x : P.Cotangent；r • x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The action of `S` on `P.Cotangent` for an extension `P → S`.
-/
lemma Cotangent.val_smul (r : S) (x : P.Cotangent) : (r • x).val = P.σ r • x.val := rfl

/-- The action of `P` on `P.Cotangent` for an extension `P → S`. -/
@[simp]
/-
**Algebra.Extension.Cotangent.val_smul'** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.Exten
sion.Cotangent`。
形式化陈述：∀ {R : Type u} {S : Type v} [inst : CommRing R] [inst_1 : CommRing S] [ins
t_2 : Algebra R S] {P : Algebra.Extension R S}   (r : P.Ring) (x : P.Cotangent),
 (r • x).val = r • x.val
参数：r : P.Ring；x : P.Cotangent；r • x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.Extension.Cotangent.val_smul'''`：∀ {R : Type u} {S : Type v} [in
st : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {P : Algebra.Exten
sion R S}   {R₀ : Type u_1} […
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `sub_smul`：sub_smul (r s : R) (y : M) : (r - s) • y = r • y - s • y
· 使用定理 `Algebra.Extension.Cotangent.smul_eq_zero_of_mem`：∀ {R : Type u} {S : Typ
e v} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   {P : Alg
ebra.Extension R S}, ∀ p ∈ P.ker, ∀ (…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `Algebra.Extension.algebraMap_σ`：∀ {R : Type u} {S : Type v} [inst : Comm
Ring R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   (self : Algebra.Extension
 R S) (x : S), (alge…
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The action of `P` on `P.Cotangent` for an extension `P → S`.
-/
lemma Cotangent.val_smul' (r : P.Ring) (x : P.Cotangent) : (r • x).val = r • x.val := by
  rw [val_smul''', ← sub_eq_zero, ← sub_smul]
  exact Cotangent.smul_eq_zero_of_mem _ (by simp) _

/-- The action of `R` on `P.Cotangent` for an `R`-extension `P → S`. -/
@[simp]
/-
**Algebra.Extension.Cotangent.val_smul''** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.Exte
nsion.Cotangent`。
形式化陈述：∀ {R : Type u} {S : Type v} [inst : CommRing R] [inst_1 : CommRing S] [ins
t_2 : Algebra R S] {P : Algebra.Extension R S}   (r : R) (x : P.Cotangent), (r •
 x).val = r • x.val
参数：r : R；x : P.Cotangent；r • x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `algebraMap_smul`：algebraMap_smul (r : R) (m : M) : (algebraMap R A) r • 
m = r • m
· 使用定理 `Algebra.Extension.instIsScalarTowerCotangent`：∀ {R : Type u} {S : Type v
} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {P : Algebra.
Extension R S}   {R₁ : Type u_1} {…
· 使用定理 `Algebra.Extension.instIsScalarTowerRing_2`：∀ {R : Type u} {S : Type v} [
inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] (P : Algebra.Ext
ension R S)   {R₀ : Type u_1} […
· 使用定理 `Algebra.Extension.Cotangent.val_smul'`：∀ {R : Type u} {S : Type v} [inst
 : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {P : Algebra.Extensi
on R S}   (r : P.Ring) (x :…
· 使用定理 `Ideal.instIsScalarTowerCotangent`：∀ {R : Type u_3} {S : Type u_1} {S' : 
Type u_2} [inst : CommRing R] [inst_1 : CommSemiring S] [inst_2 : Algebra S R]  
 [inst_3 : CommSemirin…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A

--- 原说明 ---
The action of `R` on `P.Cotangent` for an `R`-extension `P → S`.
-/
lemma Cotangent.val_smul'' (r : R) (x : P.Cotangent) : (r • x).val = r • x.val := by
  rw [← algebraMap_smul P.Ring, val_smul', algebraMap_smul]

/-- `Cotangent.val` as a linear isomorphism. -/
@[simps]
/-
**Algebra.Extension.cotangentEquivCotangentKer** 是 Mathlib 中的一个定义，位于命名空间 `Algebr
a.Extension`。
形式化陈述：cotangentEquivCotangentKer : P.Cotangent ≃ₗ[P.Ring] P.ker.Cotangent where 
toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Cotangent.val` as a linear isomorphism.
-/
def cotangentEquivCotangentKer : P.Cotangent ≃ₗ[P.Ring] P.ker.Cotangent where
  toFun := Cotangent.val
  invFun := Cotangent.of
  map_add' x y := by simp
  map_smul' x y := by simp

/-- The quotient map from the kernel of `P → S` onto the cotangent space. -/
/-
**Algebra.Extension.Cotangent.mk** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.Extension.Co
tangent`。
形式化陈述：{R : Type u} →   {S : Type v} →     [inst : CommRing R] →       [inst_1 : 
CommRing S] → [inst_2 : Algebra R S] → {P : Algebra.Extension R S} → ↥P.ker →ₗ[P
.Ring] P.Cotangent
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The quotient map from the kernel of `P → S` onto the cotangent space.
-/
noncomputable def Cotangent.mk : P.ker →ₗ[P.Ring] P.Cotangent where
  toFun x := .of (Ideal.toCotangent _ x)
  map_add' x y := by simp
  map_smul' x y := ext <| by simp

@[simp]
/-
**Algebra.Extension.Cotangent.val_mk** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.Extensio
n.Cotangent`。
形式化陈述：∀ {R : Type u} {S : Type v} [inst : CommRing R] [inst_1 : CommRing S] [ins
t_2 : Algebra R S] {P : Algebra.Extension R S}   (x : ↥P.ker), (Algebra.Extensio
n.Cotangent.mk x).val = P.ker.toCotangent x
参数：x : ↥P.ker；Algebra.Extension.Cotangent.mk x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Cotangent.val_mk (x : P.ker) : (mk x).val = Ideal.toCotangent _ x := rfl
/-
**Algebra.Extension.Cotangent.mk_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.E
xtension.Cotangent`。
形式化陈述：∀ {R : Type u} {S : Type v} [inst : CommRing R] [inst_1 : CommRing S] [ins
t_2 : Algebra R S]   {P : Algebra.Extension R S}, Function.Surjective ⇑Algebra.E
xtension.Cotangent.mk
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.toCotangent_surjective`：toCotangent_surjective : Function.Surjecti
ve I.toCotangent
-/
lemma Cotangent.mk_surjective : Function.Surjective (mk (P := P)) :=
  fun x ↦ Ideal.toCotangent_surjective P.ker x.val
/-
**Algebra.Extension.Cotangent.mk_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.
Extension.Cotangent`。
形式化陈述：∀ {R : Type u} {S : Type v} [inst : CommRing R] [inst_1 : CommRing S] [ins
t_2 : Algebra R S] {P : Algebra.Extension R S}   (x : ↥P.ker), Algebra.Extension
.Cotangent.mk x = 0 ↔ ↑x ∈ P.ker ^ 2
参数：x : ↥P.ker。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma Cotangent.mk_eq_zero_iff {P : Extension R S} (x : P.ker) :
    Cotangent.mk x = 0 ↔ x.val ∈ P.ker ^ 2 := by
  simp [Cotangent.ext_iff, Ideal.toCotangent_eq_zero]
/-
**Algebra.Extension.Cotangent.mk_eq_mk_iff_sub_mem** 是 Mathlib 中的一个定理，位于命名空间 `Al
gebra.Extension.Cotangent`。
形式化陈述：∀ {R : Type u} {S : Type v} [inst : CommRing R] [inst_1 : CommRing S] [ins
t_2 : Algebra R S] {P : Algebra.Extension R S}   (x y : ↥P.ker), Algebra.Extensi
on.Cotangent.mk x = Algebra.Extension.Cotangent.mk y ↔ ↑x - ↑y ∈ P.ker ^ 2
参数：x y : ↥P.ker。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma Cotangent.mk_eq_mk_iff_sub_mem (x y : P.ker) :
    mk x = mk y ↔ x.val - y.val ∈ P.ker ^ 2 := by
  simp [Extension.Cotangent.ext_iff, Ideal.toCotangent_eq]

variable (P) in
/-
**Algebra.Extension.Cotangent.ker_mk** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.Extensio
n.Cotangent`。
形式化陈述：∀ {R : Type u} {S : Type v} [inst : CommRing R] [inst_1 : CommRing S] [ins
t_2 : Algebra R S]   (P : Algebra.Extension R S), Algebra.Extension.Cotangent.mk
.ker = P.ker • ⊤
参数：P : Algebra.Extension R S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma Cotangent.ker_mk : LinearMap.ker (mk (P := P)) = P.ker • ⊤ := by
  ext ⟨x, hx⟩
  simp [LinearMap.mem_ker, mk_eq_zero_iff, Submodule.mem_smul_top_iff, sq]
/-
**Algebra.Extension.Cotangent.span_eq_top_of_span_eq_ker** 是 Mathlib 中的一个定理，位于命名
空间 `Algebra.Extension.Cotangent`。
形式化陈述：∀ {R : Type u} {S : Type v} [inst : CommRing R] [inst_1 : CommRing S] [ins
t_2 : Algebra R S] {P : Algebra.Extension R S}   {ι : Type u_1} (s : ι → P.Ring)
 (hs : Ideal.span (Set.range s) = P.ker),   Submodule.span S (Set.range fun i =>
 Algebra.Extension.Cotangent.mk ⟨s i, ⋯⟩) = ⊤
参数：s : ι → P.Ring；hs : Ideal.span (Set.range s) = P.ker；Set.range fun i => Algeb
ra.Extension.Cotangent.mk ⟨s i, ⋯⟩。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.span_eq_top_of_span_eq_top`：span_eq_top_of_span_eq_top (s : Se
t M) (hs : span R s = ⊤) : span S s = ⊤
· 使用定理 `Algebra.Extension.instIsScalarTowerCotangent`：∀ {R : Type u} {S : Type v
} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {P : Algebra.
Extension R S}   {R₁ : Type u_1} {…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Ideal.subset_span`：subset_span {s : Set α} : s subseteq span s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `Submodule.map_span`：map_span [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂] M₂
) (s : Set M) : (span R s).map f = span R₂ (f '' s)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Ideal.span.eq_1`：∀ {α : Type u} [inst : Semiring α] (s : Set α), Ideal.s
pan s = Submodule.span α s
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用引理 `Submodule.span_range_subtype_eq_top_iff`：span_range_subtype_eq_top_iff {
ι : Type*} (p : Submodule R M) {s : ι -> M} (hs : forall i, s i in p) : span R (
Set.range fun i => (⟨s i, hs …
· 使用定理 `Submodule.map_top`：map_top [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) 
: map f ⊤ = range f
· 使用定理 `LinearMap.range_eq_top_of_surjective`：range_eq_top_of_surjective [RingHo
mSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) (hf : Surjective f) : range f = ⊤
· 使用定理 `Algebra.Extension.Cotangent.mk_surjective`：∀ {R : Type u} {S : Type v} [
inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   {P : Algebra.E
xtension R S}, Function.Surject…
-/
lemma Cotangent.span_eq_top_of_span_eq_ker {ι : Type*} (s : ι → P.Ring)
    (hs : Ideal.span (Set.range s) = P.ker) :
    Submodule.span S (.range (fun i ↦ mk ⟨s i, hs.le (Ideal.subset_span ⟨i, rfl⟩)⟩)) = ⊤ := by
  rw [Ideal.span, ← Submodule.span_range_subtype_eq_top_iff] at hs
  · apply Submodule.span_eq_top_of_span_eq_top (R := P.Ring)
    rw [← Function.comp_def, Set.range_comp, ← Submodule.map_span, hs, Submodule.map_top,
      LinearMap.range_eq_top_of_surjective _ mk_surjective]
  · simp [← hs, Ideal.mem_span_range_self]

variable {P'}
variable [Algebra R R'] [Algebra R' R''] [Algebra R' S'']
variable [Algebra S S'] [Algebra S' S''] [Algebra S S'']
variable [Algebra R S'] [IsScalarTower R R' S']

/-- A hom between two extensions induces a map between cotangent spaces. -/
noncomputable
/-
**Algebra.Extension.Cotangent.map** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.Extension.C
otangent`。
形式化陈述：{R : Type u} →   {S : Type v} →     [inst : CommRing R] →       [inst_1 : 
CommRing S] →         [inst_2 : Algebra R S] →           {P : Algebra.Extension 
R S} →             {R' : Type u_1} →               {S' : Type u_2} →            
     [inst_3 : CommRing R'] →                   [inst_4 : CommRing S'] →        
             [inst_5 : Algebra R' S'] →                       {P' : Algebra.Exte
nsion R' S'} →                         [inst_6 : Algebra R R'] →                
           [inst_7 : Algebra S S'] →                             [inst_8 : Algeb
ra R S'] →                               [IsScalarTower R R' S'] → P.Hom P' → P.
Cotangent →ₗ[S] P'.Cotangent
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def Cotangent.map (f : Hom P P') : P.Cotangent →ₗ[S] P'.Cotangent where
  toFun x := .of (Ideal.mapCotangent (R := R) _ _ f.toAlgHom
    (fun x hx ↦ by simpa using RingHom.congr_arg (algebraMap S S') hx) x.val)
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
/-
**Algebra.Extension.Cotangent.map_mk** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.Extensio
n.Cotangent`。
形式化陈述：∀ {R : Type u} {S : Type v} [inst : CommRing R] [inst_1 : CommRing S] [ins
t_2 : Algebra R S] {P : Algebra.Extension R S}   {R' : Type u_1} {S' : Type u_2}
 [inst_3 : CommRing R'] [inst_4 : CommRing S'] [inst_5 : Algebra R' S']   {P' : 
Algebra.Extension R' S'} [inst_6 : Algebra R R'] [inst_7 : Algebra S S'] [inst_8
 : Algebra R S']   [inst_9 : IsScalarTower R R' S'] (f : P.Hom P') (x : ↥P.ker),
   (Algebra.Extension.Cotangent.map f) (Algebra.Extension.Cotangent.mk x) =     
Algebra.Extension.Cotangent.mk ⟨f.toAlgHom ↑x, ⋯⟩
参数：f : P.Hom P'；x : ↥P.ker；Algebra.Extension.Cotangent.map f；Algebra.Extension.C
otangent.mk x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Cotangent.map_mk (f : Hom P P') (x) :
    Cotangent.map f (.mk x) =
      .mk ⟨f.toAlgHom x, by simpa [-map_aeval] using RingHom.congr_arg (algebraMap S S') x.2⟩ :=
  rfl

@[simp]
/-
**Algebra.Extension.Cotangent.map_id** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.Extensio
n.Cotangent`。
形式化陈述：∀ {R : Type u} {S : Type v} [inst : CommRing R] [inst_1 : CommRing S] [ins
t_2 : Algebra R S]   {P : Algebra.Extension R S}, Algebra.Extension.Cotangent.ma
p (Algebra.Extension.Hom.id P) = LinearMap.id
参数：Algebra.Extension.Hom.id P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Algebra.Extension.Cotangent.ext`：∀ {R : Type u} {S : Type v} [inst : Com
mRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {P : Algebra.Extension R S
}   {x y : P.Cotangen…
· 使用定理 `Algebra.Extension.Cotangent.mk_surjective`：∀ {R : Type u} {S : Type v} [
inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   {P : Algebra.E
xtension R S}, Function.Surject…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.Extension.Hom.toAlgHom_id`：∀ {R : Type u} {S : Type v} [inst : C
ommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   (P : Algebra.Extension
 R S), (Algebra.Extensi…
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `Subtype.coe_eta`：coe_eta (a : { a // p a }) (h : p a) : mk (↑a) h = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Cotangent.map_id :
    Cotangent.map (.id P) = LinearMap.id := by
  ext x
  obtain ⟨x, rfl⟩ := Cotangent.mk_surjective x
  simp only [map_mk, Hom.toAlgHom_id, AlgHom.coe_id, id_eq, Subtype.coe_eta, val_mk,
    LinearMap.id_coe]

variable [Algebra R R''] [IsScalarTower R R' R''] [IsScalarTower R' R'' S'']
  [Algebra R S''] [IsScalarTower R R'' S''] [IsScalarTower S S' S'']
/-
**Algebra.Extension.Cotangent.map_comp** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.Extens
ion.Cotangent`。
形式化陈述：∀ {R : Type u} {S : Type v} [inst : CommRing R] [inst_1 : CommRing S] [ins
t_2 : Algebra R S] {P : Algebra.Extension R S}   {R' : Type u_1} {S' : Type u_2}
 [inst_3 : CommRing R'] [inst_4 : CommRing S'] [inst_5 : Algebra R' S']   {P' : 
Algebra.Extension R' S'} {R'' : Type u_4} {S'' : Type u_5} [inst_6 : CommRing R'
'] [inst_7 : CommRing S'']   [inst_8 : Algebra R'' S''] (P'' : Algebra.Extension
 R'' S'') [inst_9 : Algebra R R'] [inst_10 : Algebra R' R'']   [inst_11 : Algebr
a R' S''] [inst_12 : Algebra S S'] [inst_13 : Algebra S' S''] [inst_14 : Algebra
 S S'']   [inst_15 : Algebra R S'] [inst_16 : IsScalarTower R R' S'] [inst_17 : 
Algebra R R'']   [inst_18 : IsScalarTower R R' R''] [inst_19 : IsScalarTower R' 
R'' S''] [inst_20 : Algebra R S'']   [inst_21 : IsScalarTower R R'' S''] [inst_2
2 : IsScalarTower S S' S''] (f : P.Hom P') (g : P'.Hom P''),   Algebra.Extension
.Cotangent.map (g.comp f) =     ↑S (Algebra.Extension.Cotangent.map g) ∘ₗ Algebr
a.Extension.Cotangent.map f
参数：P'' : Algebra.Extension R'' S''；f : P.Hom P'；g : P'.Hom P''；g.comp f；Algebra.
Extension.Cotangent.map g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `Algebra.Extension.instIsScalarTowerCotangent`：∀ {R : Type u} {S : Type v
} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {P : Algebra.
Extension R S}   {R₁ : Type u_1} {…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.Extension.Cotangent.ext`：∀ {R : Type u} {S : Type v} [inst : Com
mRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {P : Algebra.Extension R S
}   {x y : P.Cotangen…
· 使用定理 `Algebra.Extension.Cotangent.mk_surjective`：∀ {R : Type u} {S : Type v} [
inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   {P : Algebra.E
xtension R S}, Function.Surject…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.Extension.Hom.comp_toRingHom`：∀ {R : Type u} {S : Type v} [inst 
: CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {P : Algebra.Extensio
n R S}   {R' : Type u_1} {…
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Cotangent.map_comp (f : Hom P P') (g : Hom P' P'') :
    Cotangent.map (g.comp f) = (map g).restrictScalars S ∘ₗ map f := by
  ext x
  obtain ⟨x, rfl⟩ := Cotangent.mk_surjective x
  simp only [map_mk, Hom.toAlgHom_apply, Hom.comp_toRingHom, RingHom.coe_comp, Function.comp_apply,
    val_mk, LinearMap.coe_comp, LinearMap.coe_restrictScalars]
/-
**Algebra.Extension.Cotangent.finite** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.Extensio
n.Cotangent`。
形式化陈述：∀ {R : Type u} {S : Type v} [inst : CommRing R] [inst_1 : CommRing S] [ins
t_2 : Algebra R S]   {P : Algebra.Extension R S}, P.ker.FG → Module.Finite S P.C
otangent
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.FG.of_restrictScalars`：∀ {A : Type u_5} {M : Type u_6} [inst :
 Semiring A] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module A M]   {S : Subm
odule A M} (R : Type …
· 使用定理 `Algebra.Extension.instIsScalarTowerCotangent`：∀ {R : Type u} {S : Type v
} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {P : Algebra.
Extension R S}   {R₁ : Type u_1} {…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.restrictScalars_top`：restrictScalars_top : restrictScalars S (
⊤ : Submodule R M) = ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LinearMap.range_eq_top`：range_eq_top [RingHomSurjective τ₁₂] {f : M ->ₛₗ
[τ₁₂] M₂} : range f = ⊤ ↔ Surjective f
· 使用定理 `Algebra.Extension.Cotangent.mk_surjective`：∀ {R : Type u} {S : Type v} [
inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   {P : Algebra.E
xtension R S}, Function.Surject…
· 使用定理 `Submodule.map_top`：map_top [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) 
: map f ⊤ = range f
· 使用定理 `Submodule.FG.map`：∀ {R : Type u_1} {M : Type u_2} [inst : Semiring R] [i
nst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {S : Type u_3} {P : Type
 u_4} …
· 使用定理 `Submodule.fg_top`：∀ {R : Type u_1} {M : Type u_2} [inst : Semiring R] [i
nst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (N : Submodule R M), ⊤.F
G ↔ N.…
-/
lemma Cotangent.finite (hP : P.ker.FG) :
    Module.Finite S P.Cotangent := by
  refine ⟨.of_restrictScalars (R := P.Ring) ?_⟩
  rw [Submodule.restrictScalars_top, ← LinearMap.range_eq_top.mpr Extension.Cotangent.mk_surjective,
    ← Submodule.map_top]
  exact ((Submodule.fg_top P.ker).mpr hP).map _
/-
**Algebra.Extension.Cotangent.map_surjective_of_comap_eq** 是 Mathlib 中的一个定理，位于命名
空间 `Algebra.Extension.Cotangent`。
形式化陈述：∀ {R : Type u} {S : Type v} [inst : CommRing R] [inst_1 : CommRing S] [ins
t_2 : Algebra R S] {P : Algebra.Extension R S}   {P' : Algebra.Extension R S} {f
 : P.Hom P'},   Function.Surjective ⇑f →     Ideal.comap f.toRingHom P'.ker = Ri
ngHom.ker f.toRingHom ⊔ P.ker →       Function.Surjective ⇑(Algebra.Extension.Co
tangent.map f)
参数：Algebra.Extension.Cotangent.map f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.Extension.Cotangent.mk_surjective`：∀ {R : Type u} {S : Type v} [
inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   {P : Algebra.E
xtension R S}, Function.Surject…
· 使用引理 `Ideal.exists_of_comap_eq_ker_sup`：Ideal.exists_of_comap_eq_ker_sup {A B 
: Type*} [Ring A] [Ring B] (f : A ->+* B) (surj : Function.Surjective f) {I : Id
eal B} {J : Ideal A} (…
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `Subtype.coe_eta`：coe_eta (a : { a // p a }) (h : p a) : mk (↑a) h = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Cotangent.map_surjective_of_comap_eq {P P' : Extension R S} {f : P.Hom P'}
    (h : Function.Surjective f) (eq : P'.ker.comap f.toRingHom = RingHom.ker f.toRingHom ⊔ P.ker) :
    Function.Surjective (Cotangent.map f) := fun x ↦ by
  obtain ⟨x, rfl⟩ := Cotangent.mk_surjective x
  obtain ⟨y, y_in, hy⟩ := Ideal.exists_of_comap_eq_ker_sup _ h eq x.prop
  exact ⟨Cotangent.mk ⟨y, y_in⟩, by simp [hy]⟩
/-
**Algebra.Extension.Cotangent.map_ker_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `A
lgebra.Extension.Cotangent`。
形式化陈述：∀ {R : Type u} {S : Type v} [inst : CommRing R] [inst_1 : CommRing S] [ins
t_2 : Algebra R S] {P : Algebra.Extension R S}   {P' : Algebra.Extension R S} {f
 : P.Hom P'},   Function.Surjective ⇑f →     Ideal.comap f.toRingHom P'.ker = Ri
ngHom.ker f.toRingHom ⊔ P.ker →       Submodule.restrictScalars P.Ring (Algebra.
Extension.Cotangent.map f).ker =         Submodule.map Algebra.Extension.Cotange
nt.mk           (Submodule.comap (Submodule.subtype P.ker) (RingHom.ker f.toRing
Hom ⊓ P.ker))
参数：Algebra.Extension.Cotangent.map f；Submodule.comap (Submodule.subtype P.ker) (
RingHom.ker f.toRingHom ⊓ P.ker)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Ideal.eq_map_of_comap_eq_ker_sup`：Ideal.eq_map_of_comap_eq_ker_sup {A B 
: Type*} [CommRing A] [CommRing B] (f : A ->+* B) (surj : Function.Surjective f)
 {I : Ideal B} {J : Id…
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Algebra.Extension.instIsScalarTowerCotangent`：∀ {R : Type u} {S : Type v
} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {P : Algebra.
Extension R S}   {R₁ : Type u_1} {…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.Extension.Cotangent.mk_surjective`：∀ {R : Type u} {S : Type v} [
inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   {P : Algebra.E
xtension R S}, Function.Surject…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.mem_sup`：mem_sup : x in p ⊔ p' ↔ exists y in p, exists z in p'
, y + z = x
· 使用引理 `Ideal.comap_map_of_surjective'`：comap_map_of_surjective' (f : F) (hf : F
unction.Surjective f) (I : Ideal R) : (I.map f).comap f = I ⊔ RingHom.ker f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.mem_comap`：mem_comap [RingHomClass F R S] {x} : x in comap f K ↔ f
 x in K
· 使用定理 `Ideal.map_pow`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : CommSe
miring R] [inst_1 : CommSemiring S] [inst_2 : FunLike F R S]   [rc : RingHomClas
s F…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Ideal.sub_mem`：∀ {α : Type u} [inst : Ring α] (I : Ideal α) {a b : α}, a
 ∈ I → b ∈ I → a - b ∈ I
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `Ideal.pow_le_self`：pow_le_self {n : Nat} (hn : n != 0) : I ^ n <= I
· 使用定理 `eq_sub_iff_add_eq'`：∀ {G : Type u_3} [inst : AddCommGroup G] {a b c : G}
, a = b - c ↔ c + a = b
· 使用定理 `sub_add_cancel_right`：∀ {G : Type u_3} [inst : AddGroup G] (a b : G), a 
- (b + a) = -b
· 使用定理 `NonUnitalSubringClass.toNegMemClass`：∀ {S : Type u_1} {R : Type u} {inst
 : NonUnitalNonAssocRing R} {inst_1 : SetLike S R}   [self : NonUnitalSubringCla
ss S R], NegMemClass S R
· 使用定理 `instNonUnitalSubringClassIdeal`：∀ {R : Type u_1} [inst : Ring R], NonUni
talSubringClass (Ideal R) R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Submodule.map.congr_simp`：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5
} {M₂ : Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddComm
Monoid M] [ins…
· 使用定理 `Submodule.comap_subtype_self`：comap_subtype_self : comap p.subtype p = ⊤
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Submodule.neg_mem_iff`：∀ {R : Type u} {M : Type v} [inst : Ring R] [inst
_1 : AddCommGroup M] {module_M : _root_.Module R M} (p : Submodule R M)   {x : M
}, -x ∈ p ↔…
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
（共 49 条，此处仅展示前 30 条）
-/
lemma Cotangent.map_ker_of_surjective {P P' : Extension R S} {f : P.Hom P'}
    (h : Function.Surjective f) (eq : P'.ker.comap f.toRingHom = RingHom.ker f.toRingHom ⊔ P.ker) :
    (Cotangent.map f).ker.restrictScalars P.Ring =
      (Submodule.comap P.ker.subtype (RingHom.ker f.toRingHom ⊓ P.ker)).map Cotangent.mk := by
  have eq_map := Ideal.eq_map_of_comap_eq_ker_sup _ h eq
  refine le_antisymm (fun x hx ↦ ?_) (fun x hx ↦ ?_)
  · obtain ⟨x, rfl⟩ := Cotangent.mk_surjective x
    simp only [Submodule.restrictScalars_mem, LinearMap.mem_ker, map_mk, Hom.toAlgHom_apply,
      mk_eq_zero_iff] at hx
    rw [eq_map, ← Ideal.map_pow, ← Ideal.mem_comap,
      Ideal.comap_map_of_surjective' f.toRingHom h, Submodule.mem_sup] at hx
    rcases hx with ⟨y, y_in, z, z_in, hyz⟩
    suffices ∃ a, a ∈ RingHom.ker f.toRingHom ∧ a ∈ P.ker ∧ a - x ∈ P.ker ^ 2 by
      simpa [mk_eq_mk_iff_sub_mem]
    refine ⟨z, z_in, ?_, by simpa [← hyz]⟩
    rw [← eq_sub_iff_add_eq'] at hyz
    exact hyz ▸ Ideal.sub_mem _ x.prop (Ideal.pow_le_self (show 2 ≠ 0 by lia) y_in)
  · obtain ⟨x, rfl⟩ := Cotangent.mk_surjective x
    obtain ⟨y, y_in, y_in', hy⟩ : ∃ a ∈ RingHom.ker f.toRingHom, a ∈ P.ker ∧
      a - x ∈ P.ker ^ 2 := by simpa [mk_eq_mk_iff_sub_mem] using hx
    suffices f.toRingHom x ∈ P'.ker ^ 2 by simpa [mk_eq_zero_iff]
    rw [eq_map, ← Ideal.map_pow, ← Ideal.mem_comap,
      Ideal.comap_map_of_surjective' f.toRingHom h, Submodule.mem_sup]
    exact ⟨x - y, by rwa [← Submodule.neg_mem_iff, neg_sub], y, y_in, by ring⟩

variable (P) in
/-- The cotangent is isomorphic to `S ⊗[P] I`. -/
/-
**Algebra.Extension.cotangentEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.Extension`
。
形式化陈述：cotangentEquiv : S otimes[P.Ring] P.ker ≃ₗ[S] P.Cotangent
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cotangent is isomorphic to `S ⊗[P] I`.
-/
noncomputable def cotangentEquiv : S ⊗[P.Ring] P.ker ≃ₗ[S] P.Cotangent := by
  refine .ofBijective (Cotangent.mk.liftBaseChange _) ⟨?_, ?_⟩
  · refine (injective_iff_map_eq_zero _).mpr fun x hx ↦ ?_
    obtain ⟨x, rfl⟩ := TensorProduct.mk_surjective P.Ring P.ker S P.algebraMap_surjective x
    simp only [mk_apply, LinearMap.liftBaseChange_tmul, one_smul, Cotangent.mk_eq_zero_iff,
      pow_two] at hx ⊢
    refine Submodule.smul_induction_on' (p := fun x (hx : x ∈ P.ker * P.ker) ↦
      (1 : S) ⊗ₜ[P.Ring] (⟨x, Ideal.mul_le_left hx⟩ : P.ker) = 0) (hx := hx) ?_ ?_
    · intro r hr s hs
      trans (r • 1) ⊗ₜ[P.Ring] ⟨s, hs⟩
      · rw [smul_tmul]; rfl
      · simp_all [Algebra.smul_def]
    · intro a ha b hb ha' hb'
      convert! congr($ha' + $hb')
      rw [← tmul_add]
      rfl
  · intro x
    obtain ⟨x, rfl⟩ := Cotangent.mk_surjective x
    exact ⟨1 ⊗ₜ x, by simp⟩

@[simp]
/-
**Algebra.Extension.contangentEquiv_tmul** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.Exte
nsion`。
形式化陈述：contangentEquiv_tmul (s : S) (x : P.ker) : P.cotangentEquiv (s otimesₜ x) 
= s • .mk x
参数：s : S；x : P.ker。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
lemma contangentEquiv_tmul (s : S) (x : P.ker) : P.cotangentEquiv (s ⊗ₜ x) = s • .mk x := rfl

end Cotangent

end Algebra.Extension

