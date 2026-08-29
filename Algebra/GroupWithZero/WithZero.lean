/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johan Commelin
-/
module

public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Algebra.GroupWithZero.Equiv
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Option.NAry

/-!
# Adjoining a zero to a group

This file proves that one can adjoin a new zero element to a group and get a group with zero.

In valuation theory, valuations have codomain `{0} ∪ {c ^ n | n : ℤ}` for some `c > 1`, which we can
formalise as `ℤᵐ⁰ := WithZero (Multiplicative ℤ)`. It is important to be able to talk about the maps
`n ↦ c ^ n` and `c ^ n ↦ n`. We define these as `exp : ℤ → ℤᵐ⁰` and `log : ℤᵐ⁰ → ℤ` with junk value
`log 0 = 0`. Junkless versions are defined as `expEquiv : ℤ ≃ ℤᵐ⁰ˣ` and `logEquiv : ℤᵐ⁰ˣ ≃ ℤ`.

## Notation

In scope `WithZero`:
* `Mᵐ⁰` for `WithZero (Multiplicative M)`

## Main definitions

* `WithZero.map'`: the `MonoidWithZero` homomorphism `WithZero α →* WithZero β` induced by
  a monoid homomorphism `f : α →* β`.
* `WithZero.exp`: The "exponential map" `M → Mᵐ⁰`
* `WithZero.exp`: The "logarithm" `Mᵐ⁰ → M`
-/

@[expose] public section

open Function

assert_not_exists DenselyOrdered Ring

namespace WithZero
variable {α β γ : Type*}

section One
variable [One α]

/--
Instance `one` / 实例 `one`

English:
instance one
  signature: : One (WithZero α) where
  body: ‹One α›

中文:
实例 one
  签名: : 幺 (WithZero α) where
  定义体: ‹One α›
-/
instance one : One (WithZero α) where
  __ := ‹One α›

/--
lemma `coe_one` / 引理 `coe_one`

English:
lemma coe_one
  statement: ((1 : α) : WithZero α) = 1
  proof: rfl

@[simp]

中文:
引理 coe_one
  结论: ((1 : α) : WithZero α) = 1
  证明: rfl

@[simp]
-/
@[simp, norm_cast] lemma coe_one : ((1 : α) : WithZero α) = 1 := rfl

@[simp]
/--
lemma `recZeroCoe_one` / 引理 `recZeroCoe_one`

English:
lemma recZeroCoe_one
  given: {M N : Type*} [One M] (f : M -> N) (z : N)
  proof: rfl

中文:
引理 recZeroCoe_one
  条件: {M N : 类型} [幺 M] (f : M -> N) (z : N)
  证明: rfl
-/
lemma recZeroCoe_one {M N : Type*} [One M] (f : M -> N) (z : N) :
    recZeroCoe z f 1 = f 1 :=
  rfl

end One

section Mul
variable [Mul α]

/--
Instance `instMulZeroClass` / 实例 `instMulZeroClass`

English:
instance instMulZeroClass
  signature: : MulZeroClass (WithZero α) where
  body: Option.map₂ (· * ·)
  zero_mul := Option.map₂_none_left (· * ·)
  mul_zero := Option.map₂_none_right (· * ·)

中文:
实例 instMulZeroClass
  签名: : 乘零类 (WithZero α) where
  定义体: Option.map₂ (· * ·)
  zero_mul := Option.map₂_none_left (· * ·)
  mul_zero := Option.map₂_none_right (· * ·)

Depends on / 依赖: Option.map
-/
instance instMulZeroClass : MulZeroClass (WithZero α) where
  mul := Option.map₂ (· * ·)
  zero_mul := Option.map₂_none_left (· * ·)
  mul_zero := Option.map₂_none_right (· * ·)

/--
lemma `coe_mul` / 引理 `coe_mul`

English:
lemma coe_mul
  given: (a b : α)
  statement: (↑(a * b) : WithZero α) = a * b
  proof: rfl

中文:
引理 coe_mul
  条件: (a b : α)
  结论: (↑(a * b) : WithZero α) = a * b
  证明: rfl
-/
@[simp, norm_cast] lemma coe_mul (a b : α) : (↑(a * b) : WithZero α) = a * b := rfl

/--
lemma `unzero_mul` / 引理 `unzero_mul`

English:
lemma unzero_mul
  given: {x y : WithZero α} (hxy : x * y != 0)
  proof: by
  simp only [← coe_inj, coe_mul, coe_unzero]

中文:
引理 unzero_mul
  条件: {x y : WithZero α} (hxy : x * y != 0)
  证明: by
  simp only [← coe_inj, coe_mul, coe_unzero]

Depends on / 依赖: coe_inj, coe_mul, coe_unzero
-/
lemma unzero_mul {x y : WithZero α} (hxy : x * y != 0) :
    unzero hxy = unzero (left_ne_zero_of_mul hxy) * unzero (right_ne_zero_of_mul hxy) := by
  simp only [← coe_inj, coe_mul, coe_unzero]

/--
Instance `instNoZeroDivisors` / 实例 `instNoZeroDivisors`

English:
instance instNoZeroDivisors
  signature: : NoZeroDivisors (WithZero α)
  body: ⟨Option.map₂_eq_none_iff.1⟩

中文:
实例 instNoZeroDivisors
  签名: : 无零因子 (WithZero α)
  定义体: ⟨Option.map₂_eq_none_iff.1⟩

Depends on / 依赖: Option.map
-/
instance instNoZeroDivisors : NoZeroDivisors (WithZero α) := ⟨Option.map₂_eq_none_iff.1⟩

end Mul

/--
Instance `instSemigroupWithZero` / 实例 `instSemigroupWithZero`

English:
instance instSemigroupWithZero
  signature: [Semigroup α]
  body: Option.map₂_assoc mul_assoc

中文:
实例 instSemigroupWithZero
  签名: [半群 α]
  定义体: Option.map₂_assoc mul_assoc

Depends on / 依赖: Option.map, mul_assoc
-/
instance instSemigroupWithZero [Semigroup α] : SemigroupWithZero (WithZero α) where
  mul_assoc _ _ _ := Option.map₂_assoc mul_assoc

/--
Instance `instCommSemigroup` / 实例 `instCommSemigroup`

English:
instance instCommSemigroup
  signature: [CommSemigroup α]
  body: Option.map₂_comm mul_comm

中文:
实例 instCommSemigroup
  签名: [交换半群 α]
  定义体: Option.map₂_comm mul_comm

Depends on / 依赖: Option.map, mul_comm
-/
instance instCommSemigroup [CommSemigroup α] : CommSemigroup (WithZero α) where
  mul_comm _ _ := Option.map₂_comm mul_comm

section MulOneClass

/--
Instance `instMulZeroOneClass` / 实例 `instMulZeroOneClass`

English:
instance instMulZeroOneClass
  signature: [MulOneClass α]
  body: Option.map₂_left_identity one_mul
  mul_one := Option.map₂_right_identity mul_one

中文:
实例 instMulZeroOneClass
  签名: [MulOne类 α]
  定义体: Option.map₂_left_identity one_mul
  mul_one := Option.map₂_right_identity mul_one

Depends on / 依赖: Option.map, one_mul
-/
instance instMulZeroOneClass [MulOneClass α] : MulZeroOneClass (WithZero α) where
  one_mul := Option.map₂_left_identity one_mul
  mul_one := Option.map₂_right_identity mul_one

variable [MulOneClass α]

set_option linter.style.whitespace false in -- manual alignment is not recognised
/-- Coercion as a monoid hom. -/
@[simps apply]
/--
Definition of `coeMonoidHom` / `coeMonoidHom` 的定义

English:
definition coeMonoidHom
  signature: : α ->* WithZero α where
  body: (↑)
  map_one' := rfl
  map_mul' _ _ := rfl

中文:
定义 coeMonoidHom
  签名: : α ->* WithZero α where
  定义体: (↑)
  map_one' := rfl
  map_mul' _ _ := rfl
-/
def coeMonoidHom : α ->* WithZero α where
  toFun := (↑)
  map_one' := rfl
  map_mul' _ _ := rfl

section lift
variable [MulZeroOneClass β]

-- See note [partially-applied ext lemmas]
@[ext high]
/--
theorem `monoidWithZeroHom_ext` / 定理 `monoidWithZeroHom_ext`

English:
theorem monoidWithZeroHom_ext
  given: ⦃f g
  statement: WithZero α ->*₀ β⦄
  proof: DFunLike.ext _ _ fun
    | 0 => (map_zero f).trans (map_zero g).symm
    | (g : α) => DFunLike.congr_fun h g

中文:
定理 monoidWithZeroHom_ext
  条件: ⦃f g
  结论: WithZero α ->*₀ β⦄
  证明: DFunLike.ext _ _ fun
    | 0 => (map_zero f).trans (map_zero g).symm
    | (g : α) => DFunLike.congr_fun h g

Depends on / 依赖: DFunLike, DFunLike.congr_fun, DFunLike.ext, congr_fun, map_zero
-/
theorem monoidWithZeroHom_ext ⦃f g : WithZero α ->*₀ β⦄
    (h : f.toMonoidHom.comp coeMonoidHom = g.toMonoidHom.comp coeMonoidHom) :
    f = g :=
  DFunLike.ext _ _ fun
    | 0 => (map_zero f).trans (map_zero g).symm
    | (g : α) => DFunLike.congr_fun h g

/-- The (multiplicative) universal property of `WithZero`. -/
@[simps! symm_apply_apply]
nonrec def lift' : (α ->* β) ≃ (WithZero α ->*₀ β) where
  toFun f :=
    { toFun := recZeroCoe 0 f
      map_zero' := rfl
      map_one' := by simp
      map_mul' := fun
        | 0, _ => (zero_mul _).symm
        | (_ : α), 0 => (mul_zero _).symm
        | (_ : α), (_ : α) => map_mul f _ _ }
  invFun F := F.toMonoidHom.comp coeMonoidHom

/--
lemma `lift'_zero` / 引理 `lift'_zero`

English:
lemma lift'_zero
  given: (f : α ->* β)
  statement: lift' f (0 : WithZero α) = 0
  proof: rfl

中文:
引理 lift'_zero
  条件: (f : α ->* β)
  结论: lift' f (0 : WithZero α) = 0
  证明: rfl
-/
lemma lift'_zero (f : α ->* β) : lift' f (0 : WithZero α) = 0 := rfl

/--
lemma `lift'_coe` / 引理 `lift'_coe`

English:
lemma lift'_coe
  given: (f : α ->* β) (x : α)
  statement: lift' f (x : WithZero α) = f x
  proof: rfl

中文:
引理 lift'_coe
  条件: (f : α ->* β) (x : α)
  结论: lift' f (x : WithZero α) = f x
  证明: rfl
-/
@[simp] lemma lift'_coe (f : α ->* β) (x : α) : lift' f (x : WithZero α) = f x := rfl

/--
lemma `lift'_unique` / 引理 `lift'_unique`

English:
lemma lift'_unique
  given: (f : WithZero α ->*₀ β)
  statement: f = lift' (f.toMonoidHom.comp coeMonoidHom)
  proof: (lift'.apply_symm_apply f).symm

中文:
引理 lift'_unique
  条件: (f : WithZero α ->*₀ β)
  结论: f = lift' (f.toMonoidHom.comp coeMonoidHom)
  证明: (lift'.apply_symm_apply f).symm
-/
lemma lift'_unique (f : WithZero α ->*₀ β) : f = lift' (f.toMonoidHom.comp coeMonoidHom) :=
  (lift'.apply_symm_apply f).symm

/--
lemma `lift'_surjective` / 引理 `lift'_surjective`

English:
lemma lift'_surjective
  given: {f : α ->* β} (hf : Surjective f)
  proof: by
  intro b
  obtain ⟨a, rfl⟩ := hf b
  exact ⟨a, by simp⟩

中文:
引理 lift'_surjective
  条件: {f : α ->* β} (hf : 满射 f)
  证明: by
  intro b
  obtain ⟨a, rfl⟩ := hf b
  exact ⟨a, by simp⟩
-/
lemma lift'_surjective {f : α ->* β} (hf : Surjective f) :
    Surjective (lift' f) := by
  intro b
  obtain ⟨a, rfl⟩ := hf b
  exact ⟨a, by simp⟩

end lift

variable [MulOneClass β] [MulOneClass γ]

/--
Definition of `map'` / `map'` 的定义

English:
definition map'
  signature: (f : α ->* β)
  body: lift' (coeMonoidHom.comp f)

中文:
定义 map'
  签名: (f : α ->* β)
  定义体: lift' (coeMonoidHom.comp f)

Depends on / 依赖: coeMonoidHom, coeMonoidHom.comp
-/
def map' (f : α ->* β) : WithZero α ->*₀ WithZero β := lift' (coeMonoidHom.comp f)

/--
lemma `map'_zero` / 引理 `map'_zero`

English:
lemma map'_zero
  given: (f : α ->* β)
  statement: map' f 0 = 0
  proof: rfl

中文:
引理 map'_zero
  条件: (f : α ->* β)
  结论: map' f 0 = 0
  证明: rfl
-/
lemma map'_zero (f : α ->* β) : map' f 0 = 0 := rfl

/--
lemma `map'_coe` / 引理 `map'_coe`

English:
lemma map'_coe
  given: (f : α ->* β) (x : α)
  statement: map' f (x : WithZero α) = f x
  proof: rfl

@[simp]

中文:
引理 map'_coe
  条件: (f : α ->* β) (x : α)
  结论: map' f (x : WithZero α) = f x
  证明: rfl

@[simp]
-/
@[simp] lemma map'_coe (f : α ->* β) (x : α) : map' f (x : WithZero α) = f x := rfl

@[simp]
/--
lemma `map'_id` / 引理 `map'_id`

English:
lemma map'_id
  statement: map' (MonoidHom.id β) = MonoidHom.id (WithZero β)
  proof: by
  ext x; induction x <;> rfl

中文:
引理 map'_id
  结论: map' (幺半群态射.id β) = 幺半群态射.id (WithZero β)
  证明: by
  ext x; induction x <;> rfl
-/
lemma map'_id : map' (MonoidHom.id β) = MonoidHom.id (WithZero β) := by
  ext x; induction x <;> rfl

/--
lemma `map'_map'` / 引理 `map'_map'`

English:
lemma map'_map'
  given: (f : α ->* β) (g : β ->* γ) (x)
  statement: map' g (map' f x) = map' (g.comp f) x
  proof: by
  induction x <;> rfl

@[simp]

中文:
引理 map'_map'
  条件: (f : α ->* β) (g : β ->* γ) (x)
  结论: map' g (map' f x) = map' (g.comp f) x
  证明: by
  induction x <;> rfl

@[simp]
-/
lemma map'_map' (f : α ->* β) (g : β ->* γ) (x) : map' g (map' f x) = map' (g.comp f) x := by
  induction x <;> rfl

@[simp]
/--
lemma `map'_comp` / 引理 `map'_comp`

English:
lemma map'_comp
  given: (f : α ->* β) (g : β ->* γ)
  statement: map' (g.comp f) = (map' g).comp (map' f)
  proof: MonoidWithZeroHom.ext fun x => (map'_map' f g x).symm

中文:
引理 map'_comp
  条件: (f : α ->* β) (g : β ->* γ)
  结论: map' (g.comp f) = (map' g).comp (map' f)
  证明: MonoidWithZeroHom.ext fun x => (map'_map' f g x).symm
-/
lemma map'_comp (f : α ->* β) (g : β ->* γ) : map' (g.comp f) = (map' g).comp (map' f) :=
  MonoidWithZeroHom.ext fun x => (map'_map' f g x).symm

/--
lemma `map'_injective_iff` / 引理 `map'_injective_iff`

English:
lemma map'_injective_iff
  given: {f : α ->* β}
  statement: Injective (map' f) ↔ Injective f
  proof: by
  simp [Injective, WithZero.forall]

alias ⟨_, map'_injective⟩ := map'_injective_iff

中文:
引理 map'_injective_iff
  条件: {f : α ->* β}
  结论: 单射 (map' f) ↔ 单射 f
  证明: by
  simp [Injective, WithZero.forall]

alias ⟨_, map'_injective⟩ := map'_injective_iff
-/
lemma map'_injective_iff {f : α ->* β} : Injective (map' f) ↔ Injective f := by
  simp [Injective, WithZero.forall]

alias ⟨_, map'_injective⟩ := map'_injective_iff

/--
lemma `map'_surjective_iff` / 引理 `map'_surjective_iff`

English:
lemma map'_surjective_iff
  given: {f : α ->* β}
  statement: Surjective (map' f) ↔ Surjective f
  proof: by
  simp only [Surjective, «forall»]
  refine ⟨fun h b => ?_, fun h => ⟨⟨0, by simp⟩, fun b => ?_⟩⟩
  · obtain ⟨a, hab⟩ := h.2 b
    induction a using WithZero.recZeroCoe <;>
    simp at hab
    grind
  · obtain ⟨a, ha⟩ := h b
    use a
    simp [ha]

alias ⟨_, map'_surjective⟩ := map'_surjective_i

中文:
引理 map'_surjective_iff
  条件: {f : α ->* β}
  结论: 满射 (map' f) ↔ 满射 f
  证明: by
  simp only [Surjective, «forall»]
  refine ⟨fun h b => ?_, fun h => ⟨⟨0, by simp⟩, fun b => ?_⟩⟩
  · obtain ⟨a, hab⟩ := h.2 b
    induction a using WithZero.recZeroCoe <;>
    simp at hab
    grind
  · obtain ⟨a, ha⟩ := h b
    use a
    simp [ha]

alias ⟨_, map'_surjective⟩ := map'_surjective_i
-/
lemma map'_surjective_iff {f : α ->* β} : Surjective (map' f) ↔ Surjective f := by
  simp only [Surjective, «forall»]
  refine ⟨fun h b => ?_, fun h => ⟨⟨0, by simp⟩, fun b => ?_⟩⟩
  · obtain ⟨a, hab⟩ := h.2 b
    induction a using WithZero.recZeroCoe <;>
    simp at hab
    grind
  · obtain ⟨a, ha⟩ := h b
    use a
    simp [ha]

alias ⟨_, map'_surjective⟩ := map'_surjective_iff

end MulOneClass

section Pow
variable [One α] [Pow α Nat]

/--
Instance `pow` / 实例 `pow`

English:
instance pow
  signature: : Pow (WithZero α) Nat where

中文:
实例 pow
  签名: : 幂 (WithZero α) 自然数 where
-/
instance pow : Pow (WithZero α) Nat where
  pow
    | none, 0 => 1
    | none, _ + 1 => 0
    | some x, n => ↑(x ^ n)

/--
lemma `coe_pow` / 引理 `coe_pow`

English:
lemma coe_pow
  given: (a : α) (n : Nat)
  statement: (↑(a ^ n) : WithZero α) = a ^ n
  proof: rfl

中文:
引理 coe_pow
  条件: (a : α) (n : 自然数)
  结论: (↑(a ^ n) : WithZero α) = a ^ n
  证明: rfl
-/
@[simp, norm_cast] lemma coe_pow (a : α) (n : Nat) : (↑(a ^ n) : WithZero α) = a ^ n := rfl

end Pow

/--
Instance `instMonoidWithZero` / 实例 `instMonoidWithZero`

English:
instance instMonoidWithZero
  signature: [Monoid α]
  body: a ^ n
  npow_zero
    | 0 => rfl
    | some _ => congr_arg some (pow_zero _)
  npow_succ
    | n, 0 => by simp only [mul_zero]; rfl
| n, some _ => congr_arg some pow_succ _ _

中文:
实例 instMonoidWithZero
  签名: [幺半群 α]
  定义体: a ^ n
  npow_zero
    | 0 => rfl
    | some _ => congr_arg some (pow_zero _)
  npow_succ
    | n, 0 => by simp only [mul_zero]; rfl
| n, some _ => congr_arg some pow_succ _ _
-/
instance instMonoidWithZero [Monoid α] : MonoidWithZero (WithZero α) where
  npow n a := a ^ n
  npow_zero
    | 0 => rfl
    | some _ => congr_arg some (pow_zero _)
  npow_succ
    | n, 0 => by simp only [mul_zero]; rfl
| n, some _ => congr_arg some pow_succ _ _

/--
Instance `instCommMonoidWithZero` / 实例 `instCommMonoidWithZero`

English:
instance instCommMonoidWithZero
  signature: [CommMonoid α]
  body: { WithZero.instMonoidWithZero, WithZero.instCommSemigroup with }

中文:
实例 instCommMonoidWithZero
  签名: [交换幺半群 α]
  定义体: { WithZero.instMonoidWithZero, WithZero.instCommSemigroup with }

Depends on / 依赖: WithZero, WithZero.instCommSemigroup, WithZero.instMonoidWithZero, instCommSemigroup, instMonoidWithZero
-/
instance instCommMonoidWithZero [CommMonoid α] : CommMonoidWithZero (WithZero α) :=
  { WithZero.instMonoidWithZero, WithZero.instCommSemigroup with }

section Inv
variable [Inv α]

/--
Instance `inv` / 实例 `inv`

English:
instance inv
  signature: : Inv (WithZero α) where inv a
  body: Option.map (·⁻¹) a

中文:
实例 inv
  签名: : 取逆 (WithZero α) where inv a
  定义体: Option.map (·⁻¹) a

Depends on / 依赖: Option.map
-/
instance inv : Inv (WithZero α) where inv a := Option.map (·⁻¹) a

/--
lemma `coe_inv` / 引理 `coe_inv`

English:
lemma coe_inv
  given: (a : α)
  statement: ((a⁻¹ : α) : WithZero α) = (↑a)⁻¹
  proof: rfl

中文:
引理 coe_inv
  条件: (a : α)
  结论: ((a⁻¹ : α) : WithZero α) = (↑a)⁻¹
  证明: rfl
-/
@[simp, norm_cast] lemma coe_inv (a : α) : ((a⁻¹ : α) : WithZero α) = (↑a)⁻¹ := rfl

/--
lemma `inv_zero` / 引理 `inv_zero`

English:
lemma inv_zero
  statement: (0 : WithZero α)⁻¹ = 0
  proof: rfl

中文:
引理 inv_zero
  结论: (0 : WithZero α)⁻¹ = 0
  证明: rfl
-/
@[simp] protected lemma inv_zero : (0 : WithZero α)⁻¹ = 0 := rfl

end Inv

/--
Instance `invOneClass` / 实例 `invOneClass`

English:
instance invOneClass
  signature: [InvOneClass α]
  body: show ((1⁻¹ : α) : WithZero α) = 1 by simp

中文:
实例 invOneClass
  签名: [InvOne类 α]
  定义体: show ((1⁻¹ : α) : WithZero α) = 1 by simp

Depends on / 依赖: WithZero
-/
instance invOneClass [InvOneClass α] : InvOneClass (WithZero α) where
  inv_one := show ((1⁻¹ : α) : WithZero α) = 1 by simp

section Div
variable [Div α]

/--
Instance `div` / 实例 `div`

English:
instance div
  signature: : Div (WithZero α) where div
  body: Option.map₂ (· / ·)

中文:
实例 div
  签名: : 除法 (WithZero α) where div
  定义体: Option.map₂ (· / ·)

Depends on / 依赖: Option.map
-/
instance div : Div (WithZero α) where div := Option.map₂ (· / ·)

/--
lemma `coe_div` / 引理 `coe_div`

English:
lemma coe_div
  given: (a b : α)
  statement: ↑(a / b : α) = (a / b : WithZero α)
  proof: rfl

中文:
引理 coe_div
  条件: (a b : α)
  结论: ↑(a / b : α) = (a / b : WithZero α)
  证明: rfl
-/
@[norm_cast] lemma coe_div (a b : α) : ↑(a / b : α) = (a / b : WithZero α) := rfl

end Div

section ZPow
variable [One α] [Pow α Int]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Pow (WithZero α) Int

中文:
实例 :
  签名: 幂 (WithZero α) 整数
-/
instance : Pow (WithZero α) Int where
  pow
    | none, Int.ofNat 0 => 1
    | none, Int.ofNat (Nat.succ _) => 0
    | none, Int.negSucc _ => 0
    | some x, n => ↑(x ^ n)

/--
lemma `coe_zpow` / 引理 `coe_zpow`

English:
lemma coe_zpow
  given: (a : α) (n : Int)
  statement: ↑(a ^ n) = (↑a : WithZero α) ^ n
  proof: rfl

中文:
引理 coe_zpow
  条件: (a : α) (n : 整数)
  结论: ↑(a ^ n) = (↑a : WithZero α) ^ n
  证明: rfl
-/
@[simp, norm_cast] lemma coe_zpow (a : α) (n : Int) : ↑(a ^ n) = (↑a : WithZero α) ^ n := rfl

end ZPow

/--
Instance `instDivInvMonoid` / 实例 `instDivInvMonoid`

English:
instance instDivInvMonoid
  signature: [DivInvMonoid α]
  body: a ^ n
  zpow_zero'
    | none => rfl
    | some _ => congr_arg some (zpow_zero _)
  zpow_succ'
    | n, none => by change 0 ^ _ = 0 ^ _ * 0; simp only [mul_zero]; rfl
    | n, some _ => congr_arg some (DivInvMonoid.zpow_succ' _ _)
  zpow_neg'
    | n, none => rfl
    | n, some _ => congr_arg some (D

中文:
实例 instDivInvMonoid
  签名: [除逆幺半群 α]
  定义体: a ^ n
  zpow_zero'
    | none => rfl
    | some _ => congr_arg some (zpow_zero _)
  zpow_succ'
    | n, none => by change 0 ^ _ = 0 ^ _ * 0; simp only [mul_zero]; rfl
    | n, some _ => congr_arg some (DivInvMonoid.zpow_succ' _ _)
  zpow_neg'
    | n, none => rfl
    | n, some _ => congr_arg some (D
-/
instance instDivInvMonoid [DivInvMonoid α] : DivInvMonoid (WithZero α) where
  div_eq_mul_inv
    | none, _ => rfl
    | some _, none => rfl
    | some a, some b => congr_arg some (div_eq_mul_inv a b)
  zpow n a := a ^ n
  zpow_zero'
    | none => rfl
    | some _ => congr_arg some (zpow_zero _)
  zpow_succ'
    | n, none => by change 0 ^ _ = 0 ^ _ * 0; simp only [mul_zero]; rfl
    | n, some _ => congr_arg some (DivInvMonoid.zpow_succ' _ _)
  zpow_neg'
    | n, none => rfl
    | n, some _ => congr_arg some (DivInvMonoid.zpow_neg' _ _)

/--
Instance `instDivInvOneMonoid` / 实例 `instDivInvOneMonoid`

English:
instance instDivInvOneMonoid
  signature: [DivInvOneMonoid α]

中文:
实例 instDivInvOneMonoid
  签名: [DivInvOne幺半群 α]
-/
instance instDivInvOneMonoid [DivInvOneMonoid α] : DivInvOneMonoid (WithZero α) where

set_option backward.isDefEq.respectTransparency false in
/--
Instance `instInvolutiveInv` / 实例 `instInvolutiveInv`

English:
instance instInvolutiveInv
  signature: [InvolutiveInv α]
  body: (Option.map_map _ _ _).trans by simp

中文:
实例 instInvolutiveInv
  签名: [InvolutiveInv α]
  定义体: (Option.map_map _ _ _).trans by simp

Depends on / 依赖: Option.map_map, map_map
-/
instance instInvolutiveInv [InvolutiveInv α] : InvolutiveInv (WithZero α) where
inv_inv a := (Option.map_map _ _ _).trans by simp

/--
Instance `instDivisionMonoid` / 实例 `instDivisionMonoid`

English:
instance instDivisionMonoid
  signature: [DivisionMonoid α]

中文:
实例 instDivisionMonoid
  签名: [Division幺半群 α]
-/
instance instDivisionMonoid [DivisionMonoid α] : DivisionMonoid (WithZero α) where
  mul_inv_rev
    | none, none => rfl
    | none, some _ => rfl
    | some _, none => rfl
    | some _, some _ => congr_arg some (mul_inv_rev _ _)
  inv_eq_of_mul
    | none, none, _ => rfl
    | some _, some _, h =>
congr_arg some inv_eq_of_mul_eq_one_right Option.some_injective _ h

/--
Instance `instDivisionCommMonoid` / 实例 `instDivisionCommMonoid`

English:
instance instDivisionCommMonoid
  signature: [DivisionCommMonoid α]

中文:
实例 instDivisionCommMonoid
  签名: [DivisionComm幺半群 α]
-/
instance instDivisionCommMonoid [DivisionCommMonoid α] : DivisionCommMonoid (WithZero α) where

section Group
variable [Group α]

/--
Instance `instGroupWithZero` / 实例 `instGroupWithZero`

English:
instance instGroupWithZero
  signature: : GroupWithZero (WithZero α) where
  body: WithZero.inv_zero
  mul_inv_cancel a ha := by
    lift a to α using ha
    norm_cast
    apply mul_inv_cancel

中文:
实例 instGroupWithZero
  签名: : 带零群 (WithZero α) where
  定义体: WithZero.inv_zero
  mul_inv_cancel a ha := by
    lift a to α using ha
    norm_cast
    apply mul_inv_cancel

Depends on / 依赖: WithZero, WithZero.inv_zero, inv_zero
-/
instance instGroupWithZero : GroupWithZero (WithZero α) where
  inv_zero := WithZero.inv_zero
  mul_inv_cancel a ha := by
    lift a to α using ha
    norm_cast
    apply mul_inv_cancel

/-- Any group is isomorphic to the units of itself adjoined with `0`. -/
@[simps]
/--
Definition of `unitsWithZeroEquiv` / `unitsWithZeroEquiv` 的定义

English:
definition unitsWithZeroEquiv
  signature: : (WithZero α)ˣ ≃* α where
  body: unzero a.ne_zero
  invFun a := Units.mk0 a coe_ne_zero
left_inv _ := Units.ext by simp only [coe_unzero, Units.mk0_val]
map_mul' _ _ := coe_inj.mp by simp only [Units.val_mul, coe_unzero, coe_mul]

中文:
定义 unitsWithZeroEquiv
  签名: : (WithZero α)ˣ ≃* α where
  定义体: unzero a.ne_zero
  invFun a := Units.mk0 a coe_ne_zero
left_inv _ := Units.ext by simp only [coe_unzero, Units.mk0_val]
map_mul' _ _ := coe_inj.mp by simp only [Units.val_mul, coe_unzero, coe_mul]

Depends on / 依赖: a.ne_zero, ne_zero, unzero
-/
def unitsWithZeroEquiv : (WithZero α)ˣ ≃* α where
  toFun a := unzero a.ne_zero
  invFun a := Units.mk0 a coe_ne_zero
left_inv _ := Units.ext by simp only [coe_unzero, Units.mk0_val]
map_mul' _ _ := coe_inj.mp by simp only [Units.val_mul, coe_unzero, coe_mul]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nontrivial
  signature: α] : Nontrivial (WithZero α)ˣ
  body: unitsWithZeroEquiv.toEquiv.surjective.nontrivial

中文:
实例 [非平凡
  签名: α] : 非平凡 (WithZero α)ˣ
  定义体: unitsWithZeroEquiv.toEquiv.surjective.nontrivial

Depends on / 依赖: nontrivial, surjective, toEquiv, unitsWithZeroEquiv, unitsWithZeroEquiv.toEquiv.surjective.nontrivial
-/
instance [Nontrivial α] : Nontrivial (WithZero α)ˣ :=
  unitsWithZeroEquiv.toEquiv.surjective.nontrivial

set_option backward.isDefEq.respectTransparency false in
/--
theorem `coe_unitsWithZeroEquiv_eq_units_val` / 定理 `coe_unitsWithZeroEquiv_eq_units_val`

English:
theorem coe_unitsWithZeroEquiv_eq_units_val
  given: (γ : (WithZero α)ˣ)
  proof: by
  simp only [WithZero.unitsWithZeroEquiv, MulEquiv.coe_mk, Equiv.coe_fn_mk, WithZero.coe_unzero]

中文:
定理 coe_unitsWithZeroEquiv_eq_units_val
  条件: (γ : (WithZero α)ˣ)
  证明: by
  simp only [WithZero.unitsWithZeroEquiv, MulEquiv.coe_mk, Equiv.coe_fn_mk, WithZero.coe_unzero]

Depends on / 依赖: Equiv.coe_fn_mk, MulEquiv, MulEquiv.coe_mk, WithZero, WithZero.coe_unzero, WithZero.unitsWithZeroEquiv, coe_fn_mk, coe_mk, coe_unzero, unitsWithZeroEquiv
-/
theorem coe_unitsWithZeroEquiv_eq_units_val (γ : (WithZero α)ˣ) :
    ↑(unitsWithZeroEquiv γ) = γ.val := by
  simp only [WithZero.unitsWithZeroEquiv, MulEquiv.coe_mk, Equiv.coe_fn_mk, WithZero.coe_unzero]

/-- Any group with zero is isomorphic to adjoining `0` to the units of itself. -/
@[simps]
/--
Definition of `withZeroUnitsEquiv` / `withZeroUnitsEquiv` 的定义

English:
definition withZeroUnitsEquiv
  signature: {G : Type*} [GroupWithZero G]
  body: WithZero.recZeroCoe 0 Units.val
  invFun a := if h : a = 0 then 0 else (Units.mk0 a h : Gˣ)
  left_inv := (by induction · <;> simp)
  right_inv _ := by simp only; split <;> simp_all
  map_mul' := (by induction · <;> induction · <;> simp [← WithZero.coe_mul])

中文:
定义 withZeroUnitsEquiv
  签名: {G : 类型} [带零群 G]
  定义体: WithZero.recZeroCoe 0 Units.val
  invFun a := if h : a = 0 then 0 else (Units.mk0 a h : Gˣ)
  left_inv := (by induction · <;> simp)
  right_inv _ := by simp only; split <;> simp_all
  map_mul' := (by induction · <;> induction · <;> simp [← WithZero.coe_mul])

Depends on / 依赖: Units.val, WithZero, WithZero.recZeroCoe, recZeroCoe
-/
def withZeroUnitsEquiv {G : Type*} [GroupWithZero G]
    [DecidablePred (fun a : G => a = 0)] :
    WithZero Gˣ ≃* G where
  toFun := WithZero.recZeroCoe 0 Units.val
  invFun a := if h : a = 0 then 0 else (Units.mk0 a h : Gˣ)
  left_inv := (by induction · <;> simp)
  right_inv _ := by simp only; split <;> simp_all
  map_mul' := (by induction · <;> induction · <;> simp [← WithZero.coe_mul])

/--
lemma `withZeroUnitsEquiv_symm_apply_coe` / 引理 `withZeroUnitsEquiv_symm_apply_coe`

English:
lemma withZeroUnitsEquiv_symm_apply_coe
  statement: {G : Type*} [GroupWithZero G]
  proof: by
  simp

中文:
引理 withZeroUnitsEquiv_symm_apply_coe
  结论: {G : 类型} [带零群 G]
  证明: by
  simp
-/
lemma withZeroUnitsEquiv_symm_apply_coe {G : Type*} [GroupWithZero G]
    [DecidablePred (fun a : G => a = 0)] (a : Gˣ) :
    WithZero.withZeroUnitsEquiv.symm (a : G) = a := by
  simp

set_option backward.isDefEq.respectTransparency false in
/-- A version of `Equiv.optionCongr` for `WithZero`. -/
@[simps!]
/--
Definition of `_root_.MulEquiv.withZero` / `_root_.MulEquiv.withZero` 的定义

English:
definition _root_.MulEquiv.withZero
  signature: [Group β]
  body: ⟨⟨map' e, map' e.symm, (by induction · <;> simp), (by induction · <;> simp)⟩,
    (by induction · <;> induction · <;> simp)⟩
  invFun e := ⟨⟨
    fun x => unzero (x := e x) (by simp [ne_eq, ← e.eq_symm_apply]),
    fun x => unzero (x := e.symm x) (by simp [e.symm_apply_eq]),
    by intro; simp, by i

中文:
定义 _root_.乘法等价.withZero
  签名: [群 β]
  定义体: ⟨⟨map' e, map' e.symm, (by induction · <;> simp), (by induction · <;> simp)⟩,
    (by induction · <;> induction · <;> simp)⟩
  invFun e := ⟨⟨
    fun x => unzero (x := e x) (by simp [ne_eq, ← e.eq_symm_apply]),
    fun x => unzero (x := e.symm x) (by simp [e.symm_apply_eq]),
    by intro; simp, by i

Depends on / 依赖: e.symm
-/
def _root_.MulEquiv.withZero [Group β] :
    (α ≃* β) ≃ (WithZero α ≃* WithZero β) where
  toFun e := ⟨⟨map' e, map' e.symm, (by induction · <;> simp), (by induction · <;> simp)⟩,
    (by induction · <;> induction · <;> simp)⟩
  invFun e := ⟨⟨
    fun x => unzero (x := e x) (by simp [ne_eq, ← e.eq_symm_apply]),
    fun x => unzero (x := e.symm x) (by simp [e.symm_apply_eq]),
    by intro; simp, by intro; simp⟩,
    by intro; simp [← coe_inj]⟩
  left_inv _ := by ext; simp
  right_inv _ := by ext x; cases x <;> simp

/--
Definition of `_root_.MulEquiv.unzero` / `_root_.MulEquiv.unzero` 的定义

English:
abbreviation _root_.MulEquiv.unzero
  signature: [Group β] (e : WithZero α ≃* WithZero β)
  body: _root_.MulEquiv.withZero.symm e

中文:
缩写 _root_.乘法等价.unzero
  签名: [群 β] (e : WithZero α ≃* WithZero β)
  定义体: _root_.MulEquiv.withZero.symm e

Depends on / 依赖: MulEquiv, _root_, _root_.MulEquiv.withZero.symm, withZero
-/
abbrev _root_.MulEquiv.unzero [Group β] (e : WithZero α ≃* WithZero β) :
    α ≃* β :=
  _root_.MulEquiv.withZero.symm e

end Group

/--
Instance `instCommGroupWithZero` / 实例 `instCommGroupWithZero`

English:
instance instCommGroupWithZero
  signature: [CommGroup α]

中文:
实例 instCommGroupWithZero
  签名: [交换群 α]

Depends on / 依赖: cancel_epi, cancel_mono, singleObjXSelf, single_map_f_self
-/
instance instCommGroupWithZero [CommGroup α] : CommGroupWithZero (WithZero α) where

/--
Instance `instAddMonoidWithOne` / 实例 `instAddMonoidWithOne`

English:
instance instAddMonoidWithOne
  signature: [AddMonoidWithOne α]
  body: if n = 0 then 0 else (n : α)
  natCast_zero := rfl
  natCast_succ n := by cases n <;> simp

中文:
实例 instAddMonoidWithOne
  签名: [加法带幺幺半群 α]
  定义体: if n = 0 then 0 else (n : α)
  natCast_zero := rfl
  natCast_succ n := by cases n <;> simp

Depends on / 依赖: singleObjXSelf, single_map_f_self
-/
instance instAddMonoidWithOne [AddMonoidWithOne α] : AddMonoidWithOne (WithZero α) where
  natCast n := if n = 0 then 0 else (n : α)
  natCast_zero := rfl
  natCast_succ n := by cases n <;> simp

/-! ### Exponential and logarithm -/

variable {M G : Type*}

/-- `Mᵐ⁰` is notation for `WithZero (Multiplicative M)`.

This naturally shows up as the codomain of valuations in valuation theory. -/
scoped notation:1024 M:1024 "ᵐ⁰" => WithZero Multiplicative M

section AddMonoid

/--
Definition of `exp` / `exp` 的定义

English:
definition exp
  signature: (a : M)
  body: coe .ofAdd a

中文:
定义 exp
  签名: (a : M)
  定义体: coe .ofAdd a
-/
def exp (a : M) : Mᵐ⁰ := coe .ofAdd a

/--
lemma `exp_ne_zero` / 引理 `exp_ne_zero`

English:
lemma exp_ne_zero
  given: {a : M}
  statement: exp a != 0
  proof: by simp [exp]

中文:
引理 exp_ne_zero
  条件: {a : M}
  结论: exp a != 0
  证明: by simp [exp]
-/
@[simp] lemma exp_ne_zero {a : M} : exp a != 0 := by simp [exp]

/--
lemma `exp_eq_coe_ofAdd` / 引理 `exp_eq_coe_ofAdd`

English:
lemma exp_eq_coe_ofAdd
  given: (a : M)
  statement: exp a = coe (Multiplicative.ofAdd a)
  proof: rfl

中文:
引理 exp_eq_coe_ofAdd
  条件: (a : M)
  结论: exp a = coe (Multiplicative.ofAdd a)
  证明: rfl
-/
lemma exp_eq_coe_ofAdd (a : M) : exp a = coe (Multiplicative.ofAdd a) := rfl

/--
lemma `exp_injective` / 引理 `exp_injective`

English:
lemma exp_injective
  statement: Injective (exp : M -> Mᵐ⁰)
  proof: Multiplicative.ofAdd.injective.comp WithZero.coe_injective

中文:
引理 exp_injective
  结论: 单射 (exp : M -> Mᵐ⁰)
  证明: Multiplicative.ofAdd.injective.comp WithZero.coe_injective

Depends on / 依赖: Multiplicative, Multiplicative.ofAdd.injective.comp, WithZero, WithZero.coe_injective, coe_injective, injective
-/
lemma exp_injective : Injective (exp : M -> Mᵐ⁰) :=
  Multiplicative.ofAdd.injective.comp WithZero.coe_injective

/--
lemma `exp_inj` / 引理 `exp_inj`

English:
lemma exp_inj
  given: {x y : M}
  statement: exp x = exp y ↔ x = y
  proof: exp_injective.eq_iff

中文:
引理 exp_inj
  条件: {x y : M}
  结论: exp x = exp y ↔ x = y
  证明: exp_injective.eq_iff
-/
@[simp] lemma exp_inj {x y : M} : exp x = exp y ↔ x = y := exp_injective.eq_iff

/-- Recursion principle for `Mᵐ⁰`. To construct predicate for all elements of `Mᵐ⁰`, it is enough to
construct its value at `0` and its value at `exp a` for all `a : M`. -/
-- TODO: Uncomment once it stops firing on `WithZero M`.
-- See https://github.com/leanprover-community/mathlib4/issues/31213
@[elab_as_elim] -- , induction_eliminator, cases_eliminator]
/--
Definition of `expRecOn` / `expRecOn` 的定义

English:
definition expRecOn
  signature: {motive : Mᵐ⁰ -> Sort*} (x : Mᵐ⁰) (zero : motive 0) (exp : forall a, motive (exp a))
  body: Option.recOn x zero exp

中文:
定义 expRecOn
  签名: {motive : Mᵐ⁰ -> 类型层*} (x : Mᵐ⁰) (zero : motive 0) (exp : 对任意 a, motive (exp a))
  定义体: Option.recOn x zero exp

Depends on / 依赖: Option.recOn
-/
def expRecOn {motive : Mᵐ⁰ -> Sort*} (x : Mᵐ⁰) (zero : motive 0) (exp : forall a, motive (exp a)) :
    motive x := Option.recOn x zero exp

/--
lemma `expRecOn_zero` / 引理 `expRecOn_zero`

English:
lemma expRecOn_zero
  given: {motive : Mᵐ⁰ -> Sort*} (zero : motive 0) (exp : forall a, motive (exp a))
  proof: rfl

中文:
引理 expRecOn_zero
  条件: {motive : Mᵐ⁰ -> 类型层*} (zero : motive 0) (exp : 对任意 a, motive (exp a))
  证明: rfl
-/
@[simp] lemma expRecOn_zero {motive : Mᵐ⁰ -> Sort*} (zero : motive 0) (exp : forall a, motive (exp a)) :
    expRecOn 0 zero exp = zero := rfl

/--
lemma `expRecOn_exp` / 引理 `expRecOn_exp`

English:
lemma expRecOn_exp
  statement: {motive : Mᵐ⁰ -> Sort*} (x : M) (zero : motive 0)
  proof: rfl

中文:
引理 expRecOn_exp
  结论: {motive : Mᵐ⁰ -> 类型层*} (x : M) (zero : motive 0)
  证明: rfl
-/
@[simp] lemma expRecOn_exp {motive : Mᵐ⁰ -> Sort*} (x : M) (zero : motive 0)
    (exp : forall a, motive (exp a)) :
    expRecOn (M := M) (motive := motive) (.exp x) zero exp = exp x := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CanLift Mᵐ⁰ M exp (· != 0)

中文:
实例 :
  签名: CanLift Mᵐ⁰ M exp (· != 0)
-/
instance : CanLift Mᵐ⁰ M exp (· != 0) where prf | (.exp a : Mᵐ⁰), _ => ⟨a, rfl⟩

variable [AddMonoid M]

/--
Definition of `log` / `log` 的定义

English:
definition log
  signature: (x : Mᵐ⁰)
  body: x.recZeroCoe 0 Multiplicative.toAdd

中文:
定义 log
  签名: (x : Mᵐ⁰)
  定义体: x.recZeroCoe 0 Multiplicative.toAdd

Depends on / 依赖: Multiplicative, Multiplicative.toAdd, recZeroCoe, x.recZeroCoe
-/
def log (x : Mᵐ⁰) : M := x.recZeroCoe 0 Multiplicative.toAdd

/--
lemma `log_exp` / 引理 `log_exp`

English:
lemma log_exp
  given: (a : M)
  statement: log (exp a) = a
  proof: rfl

中文:
引理 log_exp
  条件: (a : M)
  结论: log (exp a) = a
  证明: rfl
-/
@[simp] lemma log_exp (a : M) : log (exp a) = a := rfl
/--
lemma `exp_log` / 引理 `exp_log`

English:
lemma exp_log
  given: {x : Mᵐ⁰} (hx : x != 0)
  statement: exp (log x) = x
  proof: by
  lift x to Multiplicative M using hx; rfl

中文:
引理 exp_log
  条件: {x : Mᵐ⁰} (hx : x != 0)
  结论: exp (log x) = x
  证明: by
  lift x to Multiplicative M using hx; rfl
-/
@[simp] lemma exp_log {x : Mᵐ⁰} (hx : x != 0) : exp (log x) = x := by
  lift x to Multiplicative M using hx; rfl

/--
lemma `log_zero` / 引理 `log_zero`

English:
lemma log_zero
  statement: log 0 = (0 : M)
  proof: rfl

中文:
引理 log_zero
  结论: log 0 = (0 : M)
  证明: rfl
-/
@[simp] lemma log_zero : log 0 = (0 : M) := rfl

/--
lemma `exp_zero` / 引理 `exp_zero`

English:
lemma exp_zero
  statement: exp (0 : M) = 1
  proof: rfl

中文:
引理 exp_zero
  结论: exp (0 : M) = 1
  证明: rfl
-/
@[simp] lemma exp_zero : exp (0 : M) = 1 := rfl
/--
lemma `exp_eq_one` / 引理 `exp_eq_one`

English:
lemma exp_eq_one
  given: {x : M}
  statement: exp x = 1 ↔ x = 0
  proof: by
  rw [← exp_zero]; rw [exp_inj]

中文:
引理 exp_eq_one
  条件: {x : M}
  结论: exp x = 1 ↔ x = 0
  证明: by
  rw [← exp_zero]; rw [exp_inj]
-/
@[simp] lemma exp_eq_one {x : M} : exp x = 1 ↔ x = 0 := by
  rw [← exp_zero]; rw [exp_inj]

/--
lemma `log_one` / 引理 `log_one`

English:
lemma log_one
  statement: log 1 = (0 : M)
  proof: rfl

中文:
引理 log_one
  结论: log 1 = (0 : M)
  证明: rfl
-/
@[simp] lemma log_one : log 1 = (0 : M) := rfl

/--
lemma `exp_add` / 引理 `exp_add`

English:
lemma exp_add
  given: (a b : M)
  statement: exp (a + b) = exp a * exp b
  proof: rfl

@[simp]

中文:
引理 exp_add
  条件: (a b : M)
  结论: exp (a + b) = exp a * exp b
  证明: rfl

@[simp]
-/
@[simp] lemma exp_add (a b : M) : exp (a + b) = exp a * exp b := rfl

@[simp]
/--
lemma `log_mul` / 引理 `log_mul`

English:
lemma log_mul
  given: {x y : Mᵐ⁰} (hx : x != 0) (hy : y != 0)
  statement: log (x * y) = log x + log y
  proof: by
  lift x to Multiplicative M using hx; lift y to Multiplicative M using hy; rfl

中文:
引理 log_mul
  条件: {x y : Mᵐ⁰} (hx : x != 0) (hy : y != 0)
  结论: log (x * y) = log x + log y
  证明: by
  lift x to Multiplicative M using hx; lift y to Multiplicative M using hy; rfl

Depends on / 依赖: Multiplicative
-/
lemma log_mul {x y : Mᵐ⁰} (hx : x != 0) (hy : y != 0) : log (x * y) = log x + log y := by
  lift x to Multiplicative M using hx; lift y to Multiplicative M using hy; rfl

/--
lemma `exp_nsmul` / 引理 `exp_nsmul`

English:
lemma exp_nsmul
  given: (n : Nat) (a : M)
  statement: exp (n • a) = exp a ^ n
  proof: rfl

@[simp]

中文:
引理 exp_nsmul
  条件: (n : 自然数) (a : M)
  结论: exp (n • a) = exp a ^ n
  证明: rfl

@[simp]
-/
@[simp← ] lemma exp_nsmul (n : Nat) (a : M) : exp (n • a) = exp a ^ n := rfl

@[simp]
/--
lemma `log_pow` / 引理 `log_pow`

English:
lemma log_pow
  statement: forall (x : Mᵐ⁰) (n : Nat), log (x ^ n) = n • log x

中文:
引理 log_pow
  结论: 对任意 (x : Mᵐ⁰) (n : 自然数), log (x ^ n) = n • log x
-/
lemma log_pow : forall (x : Mᵐ⁰) (n : Nat), log (x ^ n) = n • log x
  | 0, 0 => by simp
  | 0, n + 1 => by simp
  | (x : Multiplicative M), n => rfl

/--
lemma `toAdd_unzero_eq_log` / 引理 `toAdd_unzero_eq_log`

English:
lemma toAdd_unzero_eq_log
  given: {x : Mᵐ⁰} (hx : x != 0)
  statement: (unzero hx).toAdd = log x
  proof: by
  lift x to Multiplicative M using hx
  simp [log]

中文:
引理 toAdd_unzero_eq_log
  条件: {x : Mᵐ⁰} (hx : x != 0)
  结论: (unzero hx).toAdd = log x
  证明: by
  lift x to Multiplicative M using hx
  simp [log]

Depends on / 依赖: Multiplicative
-/
lemma toAdd_unzero_eq_log {x : Mᵐ⁰} (hx : x != 0) : (unzero hx).toAdd = log x := by
  lift x to Multiplicative M using hx
  simp [log]

end AddMonoid

section AddGroup
variable [AddGroup G]

/--
Definition of `expEquiv` / `expEquiv` 的定义

English:
definition expEquiv
  signature: : G ≃ (Gᵐ⁰)ˣ
  body: Multiplicative.ofAdd.trans unitsWithZeroEquiv.symm.toEquiv

中文:
定义 expEquiv
  签名: : G ≃ (Gᵐ⁰)ˣ
  定义体: Multiplicative.ofAdd.trans unitsWithZeroEquiv.symm.toEquiv

Depends on / 依赖: Multiplicative, Multiplicative.ofAdd.trans, toEquiv, unitsWithZeroEquiv, unitsWithZeroEquiv.symm.toEquiv
-/
def expEquiv : G ≃ (Gᵐ⁰)ˣ := Multiplicative.ofAdd.trans unitsWithZeroEquiv.symm.toEquiv

/--
Definition of `logEquiv` / `logEquiv` 的定义

English:
definition logEquiv
  signature: : (Gᵐ⁰)ˣ ≃ G
  body: unitsWithZeroEquiv.toEquiv.trans Multiplicative.toAdd

中文:
定义 logEquiv
  签名: : (Gᵐ⁰)ˣ ≃ G
  定义体: unitsWithZeroEquiv.toEquiv.trans Multiplicative.toAdd

Depends on / 依赖: Multiplicative, Multiplicative.toAdd, ShortComplex, ShortComplex.hasHomology_of_zeros, hasHomology_of_zeros, toEquiv, unitsWithZeroEquiv, unitsWithZeroEquiv.toEquiv.trans
-/
def logEquiv : (Gᵐ⁰)ˣ ≃ G := unitsWithZeroEquiv.toEquiv.trans Multiplicative.toAdd

/--
lemma `logEquiv_symm` / 引理 `logEquiv_symm`

English:
lemma logEquiv_symm
  statement: (logEquiv (G := G)).symm = expEquiv
  proof: rfl

中文:
引理 logEquiv_symm
  结论: (logEquiv (G := G)).symm = expEquiv
  证明: rfl
-/
@[simp] lemma logEquiv_symm : (logEquiv (G := G)).symm = expEquiv := rfl
/--
lemma `expEquiv_symm` / 引理 `expEquiv_symm`

English:
lemma expEquiv_symm
  statement: (expEquiv (G := G)).symm = logEquiv
  proof: rfl

中文:
引理 expEquiv_symm
  结论: (expEquiv (G := G)).symm = logEquiv
  证明: rfl
-/
@[simp] lemma expEquiv_symm : (expEquiv (G := G)).symm = logEquiv := rfl

/--
lemma `coe_expEquiv_apply` / 引理 `coe_expEquiv_apply`

English:
lemma coe_expEquiv_apply
  given: (a : G)
  statement: expEquiv a = exp a
  proof: rfl

中文:
引理 coe_expEquiv_apply
  条件: (a : G)
  结论: expEquiv a = exp a
  证明: rfl
-/
@[simp] lemma coe_expEquiv_apply (a : G) : expEquiv a = exp a := rfl

/--
lemma `logEquiv_apply` / 引理 `logEquiv_apply`

English:
lemma logEquiv_apply
  given: (x : (Gᵐ⁰)ˣ)
  statement: logEquiv x = log x
  proof: toAdd_unzero_eq_log x.ne_zero

中文:
引理 logEquiv_apply
  条件: (x : (Gᵐ⁰)ˣ)
  结论: logEquiv x = log x
  证明: toAdd_unzero_eq_log x.ne_zero
-/
@[simp] lemma logEquiv_apply (x : (Gᵐ⁰)ˣ) : logEquiv x = log x := toAdd_unzero_eq_log x.ne_zero

/--
lemma `logEquiv_unitsMk0` / 引理 `logEquiv_unitsMk0`

English:
lemma logEquiv_unitsMk0
  given: (x : Gᵐ⁰) (hx)
  statement: logEquiv (.mk0 x hx) = log x
  proof: logEquiv_apply _

中文:
引理 logEquiv_unitsMk0
  条件: (x : Gᵐ⁰) (hx)
  结论: logEquiv (.mk0 x hx) = log x
  证明: logEquiv_apply _

Depends on / 依赖: logEquiv_apply
-/
lemma logEquiv_unitsMk0 (x : Gᵐ⁰) (hx) : logEquiv (.mk0 x hx) = log x := logEquiv_apply _

/--
lemma `exp_sub` / 引理 `exp_sub`

English:
lemma exp_sub
  given: (a b : G)
  statement: exp (a - b) = exp a / exp b
  proof: rfl

@[simp]

中文:
引理 exp_sub
  条件: (a b : G)
  结论: exp (a - b) = exp a / exp b
  证明: rfl

@[simp]
-/
@[simp] lemma exp_sub (a b : G) : exp (a - b) = exp a / exp b := rfl

@[simp]
/--
lemma `log_div` / 引理 `log_div`

English:
lemma log_div
  given: {x y : Gᵐ⁰} (hx : x != 0) (hy : y != 0)
  statement: log (x / y) = log x - log y
  proof: by
  lift x to Multiplicative G using hx; lift y to Multiplicative G using hy; rfl

中文:
引理 log_div
  条件: {x y : Gᵐ⁰} (hx : x != 0) (hy : y != 0)
  结论: log (x / y) = log x - log y
  证明: by
  lift x to Multiplicative G using hx; lift y to Multiplicative G using hy; rfl

Depends on / 依赖: Multiplicative
-/
lemma log_div {x y : Gᵐ⁰} (hx : x != 0) (hy : y != 0) : log (x / y) = log x - log y := by
  lift x to Multiplicative G using hx; lift y to Multiplicative G using hy; rfl

/--
lemma `exp_neg` / 引理 `exp_neg`

English:
lemma exp_neg
  given: (a : G)
  statement: exp (-a) = (exp a)⁻¹
  proof: rfl

@[simp]

中文:
引理 exp_neg
  条件: (a : G)
  结论: exp (-a) = (exp a)⁻¹
  证明: rfl

@[simp]
-/
@[simp] lemma exp_neg (a : G) : exp (-a) = (exp a)⁻¹ := rfl

@[simp]
/--
lemma `log_inv` / 引理 `log_inv`

English:
lemma log_inv
  statement: forall x : Gᵐ⁰, log x⁻¹ = -log x

中文:
引理 log_inv
  结论: 对任意 x : Gᵐ⁰, log x⁻¹ = -log x
-/
lemma log_inv : forall x : Gᵐ⁰, log x⁻¹ = -log x
  | 0 => by simp
  | (x : Multiplicative G) => rfl

/--
lemma `exp_zsmul` / 引理 `exp_zsmul`

English:
lemma exp_zsmul
  given: (n : Int) (a : G)
  statement: exp (n • a) = exp a ^ n
  proof: rfl

@[simp]

中文:
引理 exp_zsmul
  条件: (n : 整数) (a : G)
  结论: exp (n • a) = exp a ^ n
  证明: rfl

@[simp]
-/
@[simp← ] lemma exp_zsmul (n : Int) (a : G) : exp (n • a) = exp a ^ n := rfl

@[simp]
/--
lemma `log_zpow` / 引理 `log_zpow`

English:
lemma log_zpow
  given: (x : Gᵐ⁰) (n : Int)
  statement: log (x ^ n) = n • log x
  proof: by cases n <;> simp [log_pow, log_inv]

中文:
引理 log_zpow
  条件: (x : Gᵐ⁰) (n : 整数)
  结论: log (x ^ n) = n • log x
  证明: by cases n <;> simp [log_pow, log_inv]

Depends on / 依赖: log_inv, log_pow
-/
lemma log_zpow (x : Gᵐ⁰) (n : Int) : log (x ^ n) = n • log x := by cases n <;> simp [log_pow, log_inv]

end AddGroup
end WithZero

namespace MonoidWithZeroHom

/--
lemma `map_eq_zero_iff` / 引理 `map_eq_zero_iff`

English:
lemma map_eq_zero_iff
  statement: {G₀ M₀ : Type*} [GroupWithZero G₀] [MulZeroOneClass M₀]
  proof: by
  refine ⟨?_, by simp +contextual⟩
  contrapose!
  intro hx H
  lift x to G₀ˣ using isUnit_iff_ne_zero.mpr hx
  apply one_ne_zero (α := M₀)
  rw [← map_one f]; rw [← Units.mul_inv x]; rw [map_mul]; rw [H]; rw [zero_mul]

@[simp]

中文:
引理 map_eq_zero_iff
  结论: {G₀ M₀ : 类型} [带零群 G₀] [乘零幺类 M₀]
  证明: by
  refine ⟨?_, by simp +contextual⟩
  contrapose!
  intro hx H
  lift x to G₀ˣ using isUnit_iff_ne_zero.mpr hx
  apply one_ne_zero (α := M₀)
  rw [← map_one f]; rw [← Units.mul_inv x]; rw [map_mul]; rw [H]; rw [zero_mul]

@[simp]
-/
protected lemma map_eq_zero_iff {G₀ M₀ : Type*} [GroupWithZero G₀] [MulZeroOneClass M₀]
    [Nontrivial M₀] {f : G₀ ->*₀ M₀} {x : G₀} : f x = 0 ↔ x = 0 := by
  refine ⟨?_, by simp +contextual⟩
  contrapose!
  intro hx H
  lift x to G₀ˣ using isUnit_iff_ne_zero.mpr hx
  apply one_ne_zero (α := M₀)
  rw [← map_one f]; rw [← Units.mul_inv x]; rw [map_mul]; rw [H]; rw [zero_mul]

@[simp]
/--
lemma `one_apply_val_unit` / 引理 `one_apply_val_unit`

English:
lemma one_apply_val_unit
  statement: {M₀ N₀ : Type*} [MonoidWithZero M₀] [MulZeroOneClass N₀]
  proof: one_apply_of_ne_zero x.ne_zero

中文:
引理 one_apply_val_unit
  结论: {M₀ N₀ : 类型} [带零幺半群 M₀] [乘零幺类 N₀]
  证明: one_apply_of_ne_zero x.ne_zero

Depends on / 依赖: ne_zero, one_apply_of_ne_zero, x.ne_zero
-/
lemma one_apply_val_unit {M₀ N₀ : Type*} [MonoidWithZero M₀] [MulZeroOneClass N₀]
    [DecidablePred fun x : M₀ => x = 0] [Nontrivial M₀] [NoZeroDivisors M₀] (x : M₀ˣ) :
    (1 : M₀ ->*₀ N₀) x = (1 : N₀) :=
  one_apply_of_ne_zero x.ne_zero

/-- The trivial group-with-zero hom is absorbing for composition. -/
@[simp]
/--
lemma `apply_one_apply_eq` / 引理 `apply_one_apply_eq`

English:
lemma apply_one_apply_eq
  statement: {M₀ N₀ G₀ : Type*} [MulZeroOneClass M₀] [Nontrivial M₀] [NoZeroDivisors M₀]
  proof: by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [one_apply_of_ne_zero hx, one_apply_of_ne_zero hx, map_one]

中文:
引理 apply_one_apply_eq
  结论: {M₀ N₀ G₀ : 类型} [乘零幺类 M₀] [非平凡 M₀] [无零因子 M₀]
  证明: by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [one_apply_of_ne_zero hx, one_apply_of_ne_zero hx, map_one]

Depends on / 依赖: eq_or_ne, map_one, one_apply_of_ne_zero
-/
lemma apply_one_apply_eq {M₀ N₀ G₀ : Type*} [MulZeroOneClass M₀] [Nontrivial M₀] [NoZeroDivisors M₀]
    [MulZeroOneClass N₀] [MulZeroOneClass G₀] [DecidablePred fun x : M₀ => x = 0]
    (f : N₀ ->*₀ G₀) (x : M₀) :
    f ((1 : M₀ ->*₀ N₀) x) = (1 : M₀ ->*₀ G₀) x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [one_apply_of_ne_zero hx, one_apply_of_ne_zero hx, map_one]

/-- The trivial group-with-zero hom is absorbing for composition. -/
@[simp]
/--
lemma `comp_one` / 引理 `comp_one`

English:
lemma comp_one
  statement: {M₀ N₀ G₀ : Type*} [MulZeroOneClass M₀] [Nontrivial M₀] [NoZeroDivisors M₀]
  proof: ext apply_one_apply_eq _

中文:
引理 comp_one
  结论: {M₀ N₀ G₀ : 类型} [乘零幺类 M₀] [非平凡 M₀] [无零因子 M₀]
  证明: ext apply_one_apply_eq _

Depends on / 依赖: apply_one_apply_eq
-/
lemma comp_one {M₀ N₀ G₀ : Type*} [MulZeroOneClass M₀] [Nontrivial M₀] [NoZeroDivisors M₀]
    [MulZeroOneClass N₀] [MulZeroOneClass G₀] [DecidablePred fun x : M₀ => x = 0]
    (f : N₀ ->*₀ G₀) :
    f.comp (1 : M₀ ->*₀ N₀) = (1 : M₀ ->*₀ G₀) :=
ext apply_one_apply_eq _

end MonoidWithZeroHom
