/-
Copyright (c) 2025 Michal Staromiejski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Staromiejski
-/
module

public import Mathlib.Algebra.Ring.Subsemiring.Basic
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.RingTheory.LocalRing.Defs

/-!
# Subrings of local rings

We prove basic properties of subrings of local rings.
-/

public section

namespace IsLocalRing

variable {R S} [Semiring R] [Semiring S]

open nonZeroDivisors

/-- If a (semi)ring `R` in which every element is either invertible or a zero divisor
embeds in a local (semi)ring `S`, then `R` is local. -/
/-
**IsLocalRing.of_injective** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalRing`。
形式化陈述：of_injective [IsLocalRing S] {f : R ->+* S} (hf : Function.Injective f) (h
 : forall a, a in R⁰ -> IsUnit a) : IsLocalRing R
参数：hf : Function.Injective f；h : forall a, a in R⁰ -> IsUnit a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.domain_nontrivial`：domain_nontrivial [Nontrivial β] : Nontrivial
 α
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `mem_nonZeroDivisors_of_injective`：mem_nonZeroDivisors_of_injective [Mono
idWithZeroHomClass F M₀ M₀'] {f : F} (hf : Injective f) (hx : f x in M₀'⁰) : x i
n M₀⁰
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用引理 `IsUnit.mem_nonZeroDivisors`：IsUnit.mem_nonZeroDivisors (hx : IsUnit x) :
 x in M₀⁰
· 使用定理 `IsLocalRing.isUnit_or_isUnit_of_add_one`：∀ {R : Type u_1} {inst : Semiri
ng R} [self : IsLocalRing R] {a b : R}, a + b = 1 → IsUnit a ∨ IsUnit b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…

--- 原说明 ---
If a (semi)ring `R` in which every element is either invertible or a zero diviso
r
embeds in a local (semi)ring `S`, then `R` is local.
-/
theorem of_injective [IsLocalRing S] {f : R →+* S} (hf : Function.Injective f)
    (h : ∀ a, a ∈ R⁰ → IsUnit a) : IsLocalRing R := by
  have : Nontrivial R := f.domain_nontrivial
  refine .of_is_unit_or_is_unit_of_add_one fun {a b} hab ↦
    (IsLocalRing.isUnit_or_isUnit_of_add_one (map_add f .. ▸ map_one f ▸ congrArg f hab)).imp ?_ ?_
  <;> exact h _ ∘ mem_nonZeroDivisors_of_injective hf ∘ IsUnit.mem_nonZeroDivisors

/-- If in a sub(semi)ring `R` of a local (semi)ring `S` every element is either
invertible or a zero divisor, then `R` is local. -/
/-
**IsLocalRing.of_subring** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalRing`。
形式化陈述：of_subring [IsLocalRing S] {R : Subsemiring S} (h : forall a, a in R⁰ -> I
sUnit a) : IsLocalRing R
参数：h : forall a, a in R⁰ -> IsUnit a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalRing.of_injective`：of_injective [IsLocalRing S] {f : R ->+* S} (h
f : Function.Injective f) (h : forall a, a in R⁰ -> IsUnit a) : IsLocalRing R
· 使用引理 `Subsemiring.subtype_injective`：subtype_injective : Function.Injective s.
subtype

--- 原说明 ---
If in a sub(semi)ring `R` of a local (semi)ring `S` every element is either
invertible or a zero divisor, then `R` is local.
-/
theorem of_subring [IsLocalRing S] {R : Subsemiring S} (h : ∀ a, a ∈ R⁰ → IsUnit a) :
    IsLocalRing R :=
  of_injective R.subtype_injective h

/-- If in a sub(semi)ring `R` of a local (semi)ring `R'` every element is either
invertible or a zero divisor, then `R` is local.
This version is for `R` and `R'` that are both sub(semi)rings of a (semi)ring `S`. -/
/-
**IsLocalRing.of_subring'** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalRing`。
形式化陈述：of_subring' {R R' : Subsemiring S} [IsLocalRing R'] (inc : R <= R') (h : f
orall a, a in R⁰ -> IsUnit a) : IsLocalRing R
参数：inc : R <= R'；h : forall a, a in R⁰ -> IsUnit a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalRing.of_injective`：of_injective [IsLocalRing S] {f : R ->+* S} (h
f : Function.Injective f) (h : forall a, a in R⁰ -> IsUnit a) : IsLocalRing R
· 使用定理 `Subsemiring.inclusion_injective`：inclusion_injective {S T : Subsemiring 
R} (h : S <= T) : Function.Injective (inclusion h)

--- 原说明 ---
If in a sub(semi)ring `R` of a local (semi)ring `R'` every element is either
invertible or a zero divisor, then `R` is local.
This version is for `R` and `R'` that are both sub(semi)rings of a (semi)ring `S
`.
-/
theorem of_subring' {R R' : Subsemiring S} [IsLocalRing R'] (inc : R ≤ R')
    (h : ∀ a, a ∈ R⁰ → IsUnit a) : IsLocalRing R :=
  of_injective (Subsemiring.inclusion_injective inc) h

end IsLocalRing

