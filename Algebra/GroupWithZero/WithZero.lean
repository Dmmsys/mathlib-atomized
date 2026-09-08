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

/-
**WithZero.one** 是 Mathlib 中的一个实例，位于命名空间 `WithZero`。
形式化陈述：one : One (WithZero α) where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance one : One (WithZero α) where
  __ := ‹One α›
/-
**WithZero.coe_one** 是 Mathlib 中的一个定理，位于命名空间 `WithZero`。
形式化陈述：∀ {α : Type u_1} [inst : One α], ↑1 = 1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_one : ((1 : α) : WithZero α) = 1 := rfl

@[simp]
/-
**WithZero.recZeroCoe_one** 是 Mathlib 中的一个引理，位于命名空间 `WithZero`。
形式化陈述：recZeroCoe_one {M N : Type*} [One M] (f : M -> N) (z : N) : recZeroCoe z f
 1 = f 1
参数：f : M -> N；z : N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma recZeroCoe_one {M N : Type*} [One M] (f : M → N) (z : N) :
    recZeroCoe z f 1 = f 1 :=
  rfl

end One

section Mul
variable [Mul α]

/-
**WithZero.instMulZeroClass** 是 Mathlib 中的一个实例，位于命名空间 `WithZero`。
形式化陈述：instMulZeroClass : MulZeroClass (WithZero α) where mul
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMulZeroClass : MulZeroClass (WithZero α) where
  mul := Option.map₂ (· * ·)
  zero_mul := Option.map₂_none_left (· * ·)
  mul_zero := Option.map₂_none_right (· * ·)
/-
**WithZero.coe_mul** 是 Mathlib 中的一个定理，位于命名空间 `WithZero`。
形式化陈述：∀ {α : Type u_1} [inst : Mul α] (a b : α), ↑(a * b) = ↑a * ↑b
参数：a b : α；a * b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_mul (a b : α) : (↑(a * b) : WithZero α) = a * b := rfl
/-
**WithZero.unzero_mul** 是 Mathlib 中的一个引理，位于命名空间 `WithZero`。
形式化陈述：unzero_mul {x y : WithZero α} (hxy : x * y != 0) : unzero hxy = unzero (le
ft_ne_zero_of_mul hxy) * unzero (right_ne_zero_of_mul hxy)
参数：hxy : x * y != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `left_ne_zero_of_mul`：left_ne_zero_of_mul : a * b != 0 -> a != 0
· 使用定理 `right_ne_zero_of_mul`：right_ne_zero_of_mul : a * b != 0 -> b != 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithZero.coe_unzero`：∀ {α : Type u} {x : WithZero α} (hx : x ≠ 0), ↑(Wit
hZero.unzero hx) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma unzero_mul {x y : WithZero α} (hxy : x * y ≠ 0) :
    unzero hxy = unzero (left_ne_zero_of_mul hxy) * unzero (right_ne_zero_of_mul hxy) := by
  simp only [← coe_inj, coe_mul, coe_unzero]
/-
**WithZero.instNoZeroDivisors** 是 Mathlib 中的一个实例，位于命名空间 `WithZero`。
形式化陈述：instNoZeroDivisors : NoZeroDivisors (WithZero α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Option.map₂_eq_none_iff`：map₂_eq_none_iff : map₂ f a b = none ↔ a = none
 ∨ b = none
-/
instance instNoZeroDivisors : NoZeroDivisors (WithZero α) := ⟨Option.map₂_eq_none_iff.1⟩

end Mul

/-
**WithZero.instSemigroupWithZero** 是 Mathlib 中的一个实例，位于命名空间 `WithZero`。
形式化陈述：instSemigroupWithZero [Semigroup α] : SemigroupWithZero (WithZero α) where
 mul_assoc _ _ _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSemigroupWithZero [Semigroup α] : SemigroupWithZero (WithZero α) where
  mul_assoc _ _ _ := Option.map₂_assoc mul_assoc
/-
**WithZero.instCommSemigroup** 是 Mathlib 中的一个实例，位于命名空间 `WithZero`。
形式化陈述：instCommSemigroup [CommSemigroup α] : CommSemigroup (WithZero α) where mul
_comm _ _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCommSemigroup [CommSemigroup α] : CommSemigroup (WithZero α) where
  mul_comm _ _ := Option.map₂_comm mul_comm

section MulOneClass

/-
**WithZero.instMulZeroOneClass** 是 Mathlib 中的一个实例，位于命名空间 `WithZero`。
形式化陈述：instMulZeroOneClass [MulOneClass α] : MulZeroOneClass (WithZero α) where o
ne_mul
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMulZeroOneClass [MulOneClass α] : MulZeroOneClass (WithZero α) where
  one_mul := Option.map₂_left_identity one_mul
  mul_one := Option.map₂_right_identity mul_one

variable [MulOneClass α]

set_option linter.style.whitespace false in -- manual alignment is not recognised
/-- Coercion as a monoid hom. -/
@[simps apply]
/-
**WithZero.coeMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `WithZero`。
形式化陈述：coeMonoidHom : α ->* WithZero α where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Coercion as a monoid hom.
-/
def coeMonoidHom : α →* WithZero α where
  toFun        := (↑)
  map_one'     := rfl
  map_mul' _ _ := rfl

section lift
variable [MulZeroOneClass β]

-- See note [partially-applied ext lemmas]
@[ext high]
/-
**WithZero.monoidWithZeroHom_ext** 是 Mathlib 中的一个定理，位于命名空间 `WithZero`。
形式化陈述：monoidWithZeroHom_ext ⦃f g : WithZero α ->*₀ β⦄ (h : f.toMonoidHom.comp co
eMonoidHom = g.toMonoidHom.comp coeMonoidHom) : f = g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
-/
theorem monoidWithZeroHom_ext ⦃f g : WithZero α →*₀ β⦄
    (h : f.toMonoidHom.comp coeMonoidHom = g.toMonoidHom.comp coeMonoidHom) :
    f = g :=
  DFunLike.ext _ _ fun
    | 0 => (map_zero f).trans (map_zero g).symm
    | (g : α) => DFunLike.congr_fun h g

/-- The (multiplicative) universal property of `WithZero`. -/
@[simps! symm_apply_apply]
nonrec def lift' : (α →* β) ≃ (WithZero α →*₀ β) where
  toFun f :=
    { toFun := recZeroCoe 0 f
      map_zero' := rfl
      map_one' := by simp
      map_mul' := fun
        | 0, _ => (zero_mul _).symm
        | (_ : α), 0 => (mul_zero _).symm
        | (_ : α), (_ : α) => map_mul f _ _ }
  invFun F := F.toMonoidHom.comp coeMonoidHom

/-
**WithZero.lift'_zero** 是 Mathlib 中的一个定理，位于命名空间 `WithZero`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : MulOneClass α] [inst_1 : MulZeroOn
eClass β] (f : α →* β),   (WithZero.lift' f) 0 = 0
参数：f : α →* β；WithZero.lift' f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WithZero.lift'`：lift'_zero (f : α ->* β) : lift' f (0 : WithZero α) = 0
-/
lemma lift'_zero (f : α →* β) : lift' f (0 : WithZero α) = 0 := rfl
/-
**WithZero.lift'_coe** 是 Mathlib 中的一个定理，位于命名空间 `WithZero`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : MulOneClass α] [inst_1 : MulZeroOn
eClass β] (f : α →* β) (x : α),   (WithZero.lift' f) ↑x = f x
参数：f : α →* β；x : α；WithZero.lift' f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WithZero.lift'`：lift'_zero (f : α ->* β) : lift' f (0 : WithZero α) = 0
-/
@[simp] lemma lift'_coe (f : α →* β) (x : α) : lift' f (x : WithZero α) = f x := rfl
/-
**WithZero.lift'_unique** 是 Mathlib 中的一个定理，位于命名空间 `WithZero`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : MulOneClass α] [inst_1 : MulZeroOn
eClass β] (f : WithZero α →*₀ β),   f = WithZero.lift' ((↑f).comp WithZero.coeMo
noidHom)
参数：f : WithZero α →*₀ β；(↑f).comp WithZero.coeMonoidHom。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `WithZero.lift'`：lift'_zero (f : α ->* β) : lift' f (0 : WithZero α) = 0
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
-/
lemma lift'_unique (f : WithZero α →*₀ β) : f = lift' (f.toMonoidHom.comp coeMonoidHom) :=
  (lift'.apply_symm_apply f).symm
/-
**WithZero.lift'_surjective** 是 Mathlib 中的一个定理，位于命名空间 `WithZero`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : MulOneClass α] [inst_1 : MulZeroOn
eClass β] {f : α →* β},   Function.Surjective ⇑f → Function.Surjective ⇑(WithZer
o.lift' f)
参数：WithZero.lift' f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WithZero.lift'`：lift'_zero (f : α ->* β) : lift' f (0 : WithZero α) = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma lift'_surjective {f : α →* β} (hf : Surjective f) :
    Surjective (lift' f) := by
  intro b
  obtain ⟨a, rfl⟩ := hf b
  exact ⟨a, by simp⟩

end lift

variable [MulOneClass β] [MulOneClass γ]

/-- The `MonoidWithZero` homomorphism `WithZero α →* WithZero β` induced by a monoid homomorphism
  `f : α →* β`. -/
/-
**WithZero.map'** 是 Mathlib 中的一个定义，位于命名空间 `WithZero`。
形式化陈述：map' (f : α ->* β) : WithZero α ->*₀ WithZero β
参数：f : α ->* β。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `WithZero.lift'`：lift'_zero (f : α ->* β) : lift' f (0 : WithZero α) = 0

--- 原说明 ---
The `MonoidWithZero` homomorphism `WithZero α →* WithZero β` induced by a monoid
 homomorphism
  `f : α →* β`.
-/
def map' (f : α →* β) : WithZero α →*₀ WithZero β := lift' (coeMonoidHom.comp f)
/-
**WithZero.map'_zero** 是 Mathlib 中的一个定理，位于命名空间 `WithZero`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : MulOneClass α] [inst_1 : MulOneCla
ss β] (f : α →* β), (WithZero.map' f) 0 = 0
参数：f : α →* β；WithZero.map' f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map'_zero (f : α →* β) : map' f 0 = 0 := rfl
/-
**WithZero.map'_coe** 是 Mathlib 中的一个定理，位于命名空间 `WithZero`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : MulOneClass α] [inst_1 : MulOneCla
ss β] (f : α →* β) (x : α),   (WithZero.map' f) ↑x = ↑(f x)
参数：f : α →* β；x : α；WithZero.map' f；f x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma map'_coe (f : α →* β) (x : α) : map' f (x : WithZero α) = f x := rfl

@[simp]
/-
**WithZero.map'_id** 是 Mathlib 中的一个定理，位于命名空间 `WithZero`。
形式化陈述：∀ {β : Type u_2} [inst : MulOneClass β], ↑(WithZero.map' (MonoidHom.id β))
 = MonoidHom.id (WithZero β)
参数：WithZero.map' (MonoidHom.id β)；WithZero β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.ext`：MonoidHom.ext [MulOne M] [MulOne N] ⦃f g : M ->* N⦄ (h : 
forall x, f x = g x) : f = g
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
-/
lemma map'_id : map' (MonoidHom.id β) = MonoidHom.id (WithZero β) := by
  ext x; induction x <;> rfl
/-
**WithZero.map'_map'** 是 Mathlib 中的一个定理，位于命名空间 `WithZero`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : MulOneClass α] [ins
t_1 : MulOneClass β] [inst_2 : MulOneClass γ]   (f : α →* β) (g : β →* γ) (x : W
ithZero α), (WithZero.map' g) ((WithZero.map' f) x) = (WithZero.map' (g.comp f))
 x
参数：f : α →* β；g : β →* γ；x : WithZero α；WithZero.map' g；(WithZero.map' f) x；With
Zero.map' (g.comp f)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map'_map' (f : α →* β) (g : β →* γ) (x) : map' g (map' f x) = map' (g.comp f) x := by
  induction x <;> rfl

@[simp]
/-
**WithZero.map'_comp** 是 Mathlib 中的一个定理，位于命名空间 `WithZero`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : MulOneClass α] [ins
t_1 : MulOneClass β] [inst_2 : MulOneClass γ]   (f : α →* β) (g : β →* γ), WithZ
ero.map' (g.comp f) = (WithZero.map' g).comp (WithZero.map' f)
参数：f : α →* β；g : β →* γ；g.comp f；WithZero.map' g；WithZero.map' f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHom.ext`：∀ {α : Type u_2} {β : Type u_3} [inst : MulZeroOn
eClass α] [inst_1 : MulZeroOneClass β] ⦃f g : α →*₀ β⦄,   (∀ (x : α), f x = g x)
 → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithZero.map'_map'`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst
 : MulOneClass α] [inst_1 : MulOneClass β] [inst_2 : MulOneClass γ]   (f : α →* 
β) (g : …
-/
lemma map'_comp (f : α →* β) (g : β →* γ) : map' (g.comp f) = (map' g).comp (map' f) :=
  MonoidWithZeroHom.ext fun x => (map'_map' f g x).symm
/-
**WithZero.map'_injective_iff** 是 Mathlib 中的一个定理，位于命名空间 `WithZero`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : MulOneClass α] [inst_1 : MulOneCla
ss β] {f : α →* β},   Function.Injective ⇑(WithZero.map' f) ↔ Function.Injective
 ⇑f
参数：WithZero.map' f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma map'_injective_iff {f : α →* β} : Injective (map' f) ↔ Injective f := by
  simp [Injective, WithZero.forall]

alias ⟨_, map'_injective⟩ := map'_injective_iff
/-
**WithZero.map'_surjective_iff** 是 Mathlib 中的一个定理，位于命名空间 `WithZero`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : MulOneClass α] [inst_1 : MulOneCla
ss β] {f : α →* β},   Function.Surjective ⇑(WithZero.map' f) ↔ Function.Surjecti
ve ⇑f
参数：WithZero.map' f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map'_surjective_iff {f : α →* β} : Surjective (map' f) ↔ Surjective f := by
  simp only [Surjective, «forall»]
  refine ⟨fun h b ↦ ?_, fun h ↦ ⟨⟨0, by simp⟩, fun b ↦ ?_⟩⟩
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
variable [One α] [Pow α ℕ]

/-
**WithZero.pow** 是 Mathlib 中的一个定义，位于命名空间 `WithZero`。
形式化陈述：{α : Type u_1} → [One α] → [Pow α ℕ] → Pow (WithZero α) ℕ
参数：WithZero α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance pow : Pow (WithZero α) ℕ where
  pow
    | none, 0 => 1
    | none, _ + 1 => 0
    | some x, n => ↑(x ^ n)
/-
**WithZero.coe_pow** 是 Mathlib 中的一个定理，位于命名空间 `WithZero`。
形式化陈述：∀ {α : Type u_1} [inst : One α] [inst_1 : Pow α ℕ] (a : α) (n : ℕ), ↑(a ^ 
n) = ↑a ^ n
参数：a : α；n : ℕ；a ^ n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_pow (a : α) (n : ℕ) : (↑(a ^ n) : WithZero α) = a ^ n := rfl

end Pow

/-
**WithZero.instMonoidWithZero** 是 Mathlib 中的一个实例，位于命名空间 `WithZero`。
形式化陈述：instMonoidWithZero [Monoid α] : MonoidWithZero (WithZero α) where npow n a
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMonoidWithZero [Monoid α] : MonoidWithZero (WithZero α) where
  npow n a := a ^ n
  npow_zero
    | 0 => rfl
    | some _ => congr_arg some (pow_zero _)
  npow_succ
    | n, 0 => by simp only [mul_zero]; rfl
    | n, some _ => congr_arg some <| pow_succ _ _
/-
**WithZero.instCommMonoidWithZero** 是 Mathlib 中的一个实例，位于命名空间 `WithZero`。
形式化陈述：instCommMonoidWithZero [CommMonoid α] : CommMonoidWithZero (WithZero α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCommMonoidWithZero [CommMonoid α] : CommMonoidWithZero (WithZero α) :=
  { WithZero.instMonoidWithZero, WithZero.instCommSemigroup with }

section Inv
variable [Inv α]

/-- Extend the inverse operation on `α` to `WithZero α` by sending `0` to `0`. -/
/-
**WithZero.inv** 是 Mathlib 中的一个实例，位于命名空间 `WithZero`。
形式化陈述：inv : Inv (WithZero α) where inv a
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Extend the inverse operation on `α` to `WithZero α` by sending `0` to `0`.
-/
instance inv : Inv (WithZero α) where inv a := Option.map (·⁻¹) a
/-
**WithZero.coe_inv** 是 Mathlib 中的一个定理，位于命名空间 `WithZero`。
形式化陈述：∀ {α : Type u_1} [inst : Inv α] (a : α), ↑a⁻¹ = (↑a)⁻¹
参数：a : α；↑a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_inv (a : α) : ((a⁻¹ : α) : WithZero α) = (↑a)⁻¹ := rfl
/-
**WithZero.inv_zero** 是 Mathlib 中的一个定理，位于命名空间 `WithZero`。
形式化陈述：∀ {α : Type u_1} [inst : Inv α], 0⁻¹ = 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] protected lemma inv_zero : (0 : WithZero α)⁻¹ = 0 := rfl

end Inv

/-
**WithZero.invOneClass** 是 Mathlib 中的一个实例，位于命名空间 `WithZero`。
形式化陈述：invOneClass [InvOneClass α] : InvOneClass (WithZero α) where inv_one
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance invOneClass [InvOneClass α] : InvOneClass (WithZero α) where
  inv_one := show ((1⁻¹ : α) : WithZero α) = 1 by simp

section Div
variable [Div α]

/-
**WithZero.div** 是 Mathlib 中的一个实例，位于命名空间 `WithZero`。
形式化陈述：div : Div (WithZero α) where div
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance div : Div (WithZero α) where div := Option.map₂ (· / ·)
/-
**WithZero.coe_div** 是 Mathlib 中的一个定理，位于命名空间 `WithZero`。
形式化陈述：∀ {α : Type u_1} [inst : Div α] (a b : α), ↑(a / b) = ↑a / ↑b
参数：a b : α；a / b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[norm_cast] lemma coe_div (a b : α) : ↑(a / b : α) = (a / b : WithZero α) := rfl

end Div

section ZPow
variable [One α] [Pow α ℤ]

/-
**WithZero.** 是 Mathlib 中的一个实例，位于命名空间 `WithZero`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Pow (WithZero α) ℤ where
  pow
    | none, Int.ofNat 0 => 1
    | none, Int.ofNat (Nat.succ _) => 0
    | none, Int.negSucc _ => 0
    | some x, n => ↑(x ^ n)
/-
**WithZero.coe_zpow** 是 Mathlib 中的一个定理，位于命名空间 `WithZero`。
形式化陈述：∀ {α : Type u_1} [inst : One α] [inst_1 : Pow α ℤ] (a : α) (n : ℤ), ↑(a ^ 
n) = ↑a ^ n
参数：a : α；n : ℤ；a ^ n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_zpow (a : α) (n : ℤ) : ↑(a ^ n) = (↑a : WithZero α) ^ n := rfl

end ZPow

/-
**WithZero.instDivInvMonoid** 是 Mathlib 中的一个实例，位于命名空间 `WithZero`。
形式化陈述：instDivInvMonoid [DivInvMonoid α] : DivInvMonoid (WithZero α) where div_eq
_mul_inv | none, _ => rfl | some _, none => rfl | some a, some b => congr_arg so
me (div_eq_mul_inv a b) zpow n a
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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
/-
**WithZero.instDivInvOneMonoid** 是 Mathlib 中的一个定义，位于命名空间 `WithZero`。
形式化陈述：{α : Type u_1} → [DivInvOneMonoid α] → DivInvOneMonoid (WithZero α)
参数：WithZero α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instDivInvOneMonoid [DivInvOneMonoid α] : DivInvOneMonoid (WithZero α) where

set_option backward.isDefEq.respectTransparency false in
/-
**WithZero.instInvolutiveInv** 是 Mathlib 中的一个实例，位于命名空间 `WithZero`。
形式化陈述：instInvolutiveInv [InvolutiveInv α] : InvolutiveInv (WithZero α) where inv
_inv a
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instInvolutiveInv [InvolutiveInv α] : InvolutiveInv (WithZero α) where
  inv_inv a := (Option.map_map _ _ _).trans <| by simp
/-
**WithZero.instDivisionMonoid** 是 Mathlib 中的一个定义，位于命名空间 `WithZero`。
形式化陈述：{α : Type u_1} → [DivisionMonoid α] → DivisionMonoid (WithZero α)
参数：WithZero α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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
      congr_arg some <| inv_eq_of_mul_eq_one_right <| Option.some_injective _ h
/-
**WithZero.instDivisionCommMonoid** 是 Mathlib 中的一个定义，位于命名空间 `WithZero`。
形式化陈述：{α : Type u_1} → [DivisionCommMonoid α] → DivisionCommMonoid (WithZero α)
参数：WithZero α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instDivisionCommMonoid [DivisionCommMonoid α] : DivisionCommMonoid (WithZero α) where

section Group
variable [Group α]

/-- If `α` is a group then `WithZero α` is a group with zero. -/
/-
**WithZero.instGroupWithZero** 是 Mathlib 中的一个实例，位于命名空间 `WithZero`。
形式化陈述：instGroupWithZero : GroupWithZero (WithZero α) where inv_zero
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `α` is a group then `WithZero α` is a group with zero.
-/
instance instGroupWithZero : GroupWithZero (WithZero α) where
  inv_zero := WithZero.inv_zero
  mul_inv_cancel a ha := by
    lift a to α using ha
    norm_cast
    apply mul_inv_cancel

/-- Any group is isomorphic to the units of itself adjoined with `0`. -/
@[simps]
/-
**WithZero.unitsWithZeroEquiv** 是 Mathlib 中的一个定义，位于命名空间 `WithZero`。
形式化陈述：unitsWithZeroEquiv : (WithZero α)ˣ ≃* α where toFun a
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `WithZero.coe_ne_zero`：∀ {α : Type u} {a : α}, ↑a ≠ 0

--- 原说明 ---
Any group is isomorphic to the units of itself adjoined with `0`.
-/
def unitsWithZeroEquiv : (WithZero α)ˣ ≃* α where
  toFun a := unzero a.ne_zero
  invFun a := Units.mk0 a coe_ne_zero
  left_inv _ := Units.ext <| by simp only [coe_unzero, Units.mk0_val]
  map_mul' _ _ := coe_inj.mp <| by simp only [Units.val_mul, coe_unzero, coe_mul]
/-
**WithZero.** 是 Mathlib 中的一个实例，位于命名空间 `WithZero`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Nontrivial α] : Nontrivial (WithZero α)ˣ :=
  unitsWithZeroEquiv.toEquiv.surjective.nontrivial

set_option backward.isDefEq.respectTransparency false in
/-
**WithZero.coe_unitsWithZeroEquiv_eq_units_val** 是 Mathlib 中的一个定理，位于命名空间 `WithZe
ro`。
形式化陈述：coe_unitsWithZeroEquiv_eq_units_val (γ : (WithZero α)ˣ) : ↑(unitsWithZeroE
quiv γ) = γ.val
参数：γ : (WithZero α)ˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithZero.coe_unzero`：∀ {α : Type u} {x : WithZero α} (hx : x ≠ 0), ↑(Wit
hZero.unzero hx) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coe_unitsWithZeroEquiv_eq_units_val (γ : (WithZero α)ˣ) :
    ↑(unitsWithZeroEquiv γ) = γ.val := by
  simp only [WithZero.unitsWithZeroEquiv, MulEquiv.coe_mk, Equiv.coe_fn_mk, WithZero.coe_unzero]

/-- Any group with zero is isomorphic to adjoining `0` to the units of itself. -/
@[simps]
/-
**WithZero.withZeroUnitsEquiv** 是 Mathlib 中的一个定义，位于命名空间 `WithZero`。
形式化陈述：withZeroUnitsEquiv {G : Type*} [GroupWithZero G] [DecidablePred (fun a : G
 => a = 0)] : WithZero Gˣ ≃* G where toFun
参数：fun a : G => a = 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any group with zero is isomorphic to adjoining `0` to the units of itself.
-/
def withZeroUnitsEquiv {G : Type*} [GroupWithZero G]
    [DecidablePred (fun a : G ↦ a = 0)] :
    WithZero Gˣ ≃* G where
  toFun := WithZero.recZeroCoe 0 Units.val
  invFun a := if h : a = 0 then 0 else (Units.mk0 a h : Gˣ)
  left_inv := (by induction · <;> simp)
  right_inv _ := by simp only; split <;> simp_all
  map_mul' := (by induction · <;> induction · <;> simp [← WithZero.coe_mul])
/-
**WithZero.withZeroUnitsEquiv_symm_apply_coe** 是 Mathlib 中的一个引理，位于命名空间 `WithZero
`。
形式化陈述：withZeroUnitsEquiv_symm_apply_coe {G : Type*} [GroupWithZero G] [Decidable
Pred (fun a : G => a = 0)] (a : Gˣ) : WithZero.withZeroUnitsEquiv.symm (a : G) =
 a
参数：fun a : G => a = 0；a : Gˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithZero.withZeroUnitsEquiv_symm_apply`：∀ {G : Type u_4} [inst : GroupWi
thZero G] [inst_1 : DecidablePred fun a => a = 0] (a : G),   WithZero.withZeroUn
itsEquiv.symm a = if h : a =…
· 使用定理 `of_eq_false`：∀ {p : Prop}, p = False → ¬p
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `Units.mk0_val`：mk0_val (u : G₀ˣ) (h : (u : G₀) != 0) : mk0 (u : G₀) h = 
u
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma withZeroUnitsEquiv_symm_apply_coe {G : Type*} [GroupWithZero G]
    [DecidablePred (fun a : G ↦ a = 0)] (a : Gˣ) :
    WithZero.withZeroUnitsEquiv.symm (a : G) = a := by
  simp

set_option backward.isDefEq.respectTransparency false in
/-- A version of `Equiv.optionCongr` for `WithZero`. -/
@[simps!]
/-
**WithZero._root_.MulEquiv.withZero** 是 Mathlib 中的一个定义，位于命名空间 `WithZero`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A version of `Equiv.optionCongr` for `WithZero`.
-/
def _root_.MulEquiv.withZero [Group β] :
    (α ≃* β) ≃ (WithZero α ≃* WithZero β) where
  toFun e := ⟨⟨map' e, map' e.symm, (by induction · <;> simp), (by induction · <;> simp)⟩,
    (by induction · <;> induction · <;> simp)⟩
  invFun e := ⟨⟨
    fun x ↦ unzero (x := e x) (by simp [ne_eq, ← e.eq_symm_apply]),
    fun x ↦ unzero (x := e.symm x) (by simp [e.symm_apply_eq]),
    by intro; simp, by intro; simp⟩,
    by intro; simp [← coe_inj]⟩
  left_inv _ := by ext; simp
  right_inv _ := by ext x; cases x <;> simp

/-- The inverse of `MulEquiv.withZero`. -/
/-
**WithZero._root_.MulEquiv.unzero** 是 Mathlib 中的一个缩写定义，位于命名空间 `WithZero`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inverse of `MulEquiv.withZero`.
-/
abbrev _root_.MulEquiv.unzero [Group β] (e : WithZero α ≃* WithZero β) :
    α ≃* β :=
  _root_.MulEquiv.withZero.symm e

end Group

/-
**WithZero.instCommGroupWithZero** 是 Mathlib 中的一个定义，位于命名空间 `WithZero`。
形式化陈述：{α : Type u_1} → [CommGroup α] → CommGroupWithZero (WithZero α)
参数：WithZero α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCommGroupWithZero [CommGroup α] : CommGroupWithZero (WithZero α) where
/-
**WithZero.instAddMonoidWithOne** 是 Mathlib 中的一个实例，位于命名空间 `WithZero`。
形式化陈述：instAddMonoidWithOne [AddMonoidWithOne α] : AddMonoidWithOne (WithZero α) 
where natCast n
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAddMonoidWithOne [AddMonoidWithOne α] : AddMonoidWithOne (WithZero α) where
  natCast n := if n = 0 then 0 else (n : α)
  natCast_zero := rfl
  natCast_succ n := by cases n <;> simp

/-! ### Exponential and logarithm -/

variable {M G : Type*}

/-- `Mᵐ⁰` is notation for `WithZero (Multiplicative M)`.

This naturally shows up as the codomain of valuations in valuation theory. -/
scoped notation:1024 M:1024 "ᵐ⁰" => WithZero <| Multiplicative M

section AddMonoid

/-- The exponential map as a function `M → Mᵐ⁰`. -/
/-
**WithZero.exp** 是 Mathlib 中的一个定义，位于命名空间 `WithZero`。
形式化陈述：exp (a : M) : Mᵐ⁰
参数：a : M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The exponential map as a function `M → Mᵐ⁰`.
-/
def exp (a : M) : Mᵐ⁰ := coe <| .ofAdd a
/-
**WithZero.exp_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `WithZero`。
形式化陈述：∀ {M : Type u_4} {a : M}, WithZero.exp a ≠ 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
@[simp] lemma exp_ne_zero {a : M} : exp a ≠ 0 := by simp [exp]
/-
**WithZero.exp_eq_coe_ofAdd** 是 Mathlib 中的一个引理，位于命名空间 `WithZero`。
形式化陈述：exp_eq_coe_ofAdd (a : M) : exp a = coe (Multiplicative.ofAdd a)
参数：a : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma exp_eq_coe_ofAdd (a : M) : exp a = coe (Multiplicative.ofAdd a) := rfl
/-
**WithZero.exp_injective** 是 Mathlib 中的一个引理，位于命名空间 `WithZero`。
形式化陈述：exp_injective : Injective (exp : M -> Mᵐ⁰)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `WithZero.coe_injective`：∀ {α : Type u}, Function.Injective WithZero.coe
-/
lemma exp_injective : Injective (exp : M → Mᵐ⁰) :=
  Multiplicative.ofAdd.injective.comp WithZero.coe_injective
/-
**WithZero.exp_inj** 是 Mathlib 中的一个定理，位于命名空间 `WithZero`。
形式化陈述：∀ {M : Type u_4} {x y : M}, WithZero.exp x = WithZero.exp y ↔ x = y
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用引理 `WithZero.exp_injective`：exp_injective : Injective (exp : M -> Mᵐ⁰)
-/
@[simp] lemma exp_inj {x y : M} : exp x = exp y ↔ x = y := exp_injective.eq_iff

/-- Recursion principle for `Mᵐ⁰`. To construct predicate for all elements of `Mᵐ⁰`, it is enough to
construct its value at `0` and its value at `exp a` for all `a : M`. -/
-- TODO: Uncomment once it stops firing on `WithZero M`.
-- See https://github.com/leanprover-community/mathlib4/issues/31213
@[elab_as_elim] -- , induction_eliminator, cases_eliminator]
/-
**WithZero.expRecOn** 是 Mathlib 中的一个定义，位于命名空间 `WithZero`。
形式化陈述：expRecOn {motive : Mᵐ⁰ -> Sort*} (x : Mᵐ⁰) (zero : motive 0) (exp : forall
 a, motive (exp a)) : motive x
参数：x : Mᵐ⁰；zero : motive 0；exp : forall a, motive (exp a)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def expRecOn {motive : Mᵐ⁰ → Sort*} (x : Mᵐ⁰) (zero : motive 0) (exp : ∀ a, motive (exp a)) :
    motive x := Option.recOn x zero exp
/-
**WithZero.expRecOn_zero** 是 Mathlib 中的一个定理，位于命名空间 `WithZero`。
形式化陈述：∀ {M : Type u_4} {motive : WithZero (Multiplicative M) → Sort u_6} (zero :
 motive 0)   (exp : (a : M) → motive (WithZero.exp a)), WithZero.expRecOn 0 zero
 exp = zero
参数：Multiplicative M；zero : motive 0；exp : (a : M) → motive (WithZero.exp a)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma expRecOn_zero {motive : Mᵐ⁰ → Sort*} (zero : motive 0) (exp : ∀ a, motive (exp a)) :
    expRecOn 0 zero exp = zero := rfl
/-
**WithZero.expRecOn_exp** 是 Mathlib 中的一个定理，位于命名空间 `WithZero`。
形式化陈述：∀ {M : Type u_4} {motive : WithZero (Multiplicative M) → Sort u_6} (x : M)
 (zero : motive 0)   (exp : (a : M) → motive (WithZero.exp a)), WithZero.expRecO
n (WithZero.exp x) zero exp = exp x
参数：Multiplicative M；x : M；zero : motive 0；exp : (a : M) → motive (WithZero.exp a
)；WithZero.exp x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma expRecOn_exp {motive : Mᵐ⁰ → Sort*} (x : M) (zero : motive 0)
    (exp : ∀ a, motive (exp a)) :
    expRecOn (M := M) (motive := motive) (.exp x) zero exp = exp x := rfl
/-
**WithZero.** 是 Mathlib 中的一个实例，位于命名空间 `WithZero`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CanLift Mᵐ⁰ M exp (· ≠ 0) where prf | (.exp a : Mᵐ⁰), _ => ⟨a, rfl⟩

variable [AddMonoid M]

/-- The logarithm as a function `Mᵐ⁰ → M` with junk value `log 0 = 0`. -/
/-
**WithZero.log** 是 Mathlib 中的一个定义，位于命名空间 `WithZero`。
形式化陈述：log (x : Mᵐ⁰) : M
参数：x : Mᵐ⁰。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The logarithm as a function `Mᵐ⁰ → M` with junk value `log 0 = 0`.
-/
def log (x : Mᵐ⁰) : M := x.recZeroCoe 0 Multiplicative.toAdd
/-
**WithZero.log_exp** 是 Mathlib 中的一个定理，位于命名空间 `WithZero`。
形式化陈述：∀ {M : Type u_4} [inst : AddMonoid M] (a : M), (WithZero.exp a).log = a
参数：a : M；WithZero.exp a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma log_exp (a : M) : log (exp a) = a := rfl
/-
**WithZero.exp_log** 是 Mathlib 中的一个定理，位于命名空间 `WithZero`。
形式化陈述：∀ {M : Type u_4} [inst : AddMonoid M] {x : WithZero (Multiplicative M)}, x
 ≠ 0 → WithZero.exp x.log = x
参数：Multiplicative M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `WithZero.instCanLift`：∀ {α : Type u}, CanLift (WithZero α) α WithZero.co
e fun a => a ≠ 0
-/
@[simp] lemma exp_log {x : Mᵐ⁰} (hx : x ≠ 0) : exp (log x) = x := by
  lift x to Multiplicative M using hx; rfl
/-
**WithZero.log_zero** 是 Mathlib 中的一个定理，位于命名空间 `WithZero`。
形式化陈述：∀ {M : Type u_4} [inst : AddMonoid M], WithZero.log 0 = 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma log_zero : log 0 = (0 : M) := rfl
/-
**WithZero.exp_zero** 是 Mathlib 中的一个定理，位于命名空间 `WithZero`。
形式化陈述：∀ {M : Type u_4} [inst : AddMonoid M], WithZero.exp 0 = 1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma exp_zero : exp (0 : M) = 1 := rfl
/-
**WithZero.exp_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `WithZero`。
形式化陈述：∀ {M : Type u_4} [inst : AddMonoid M] {x : M}, WithZero.exp x = 1 ↔ x = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithZero.exp_zero`：∀ {M : Type u_4} [inst : AddMonoid M], WithZero.exp 0
 = 1
· 使用定理 `WithZero.exp_inj`：∀ {M : Type u_4} {x y : M}, WithZero.exp x = WithZero.
exp y ↔ x = y
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma exp_eq_one {x : M} : exp x = 1 ↔ x = 0 := by
  rw [← exp_zero, exp_inj]
/-
**WithZero.log_one** 是 Mathlib 中的一个定理，位于命名空间 `WithZero`。
形式化陈述：∀ {M : Type u_4} [inst : AddMonoid M], WithZero.log 1 = 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma log_one : log 1 = (0 : M) := rfl
/-
**WithZero.exp_add** 是 Mathlib 中的一个定理，位于命名空间 `WithZero`。
形式化陈述：∀ {M : Type u_4} [inst : AddMonoid M] (a b : M), WithZero.exp (a + b) = Wi
thZero.exp a * WithZero.exp b
参数：a b : M；a + b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma exp_add (a b : M) : exp (a + b) = exp a * exp b := rfl

@[simp]
/-
**WithZero.log_mul** 是 Mathlib 中的一个引理，位于命名空间 `WithZero`。
形式化陈述：log_mul {x y : Mᵐ⁰} (hx : x != 0) (hy : y != 0) : log (x * y) = log x + lo
g y
参数：hx : x != 0；hy : y != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `WithZero.instCanLift`：∀ {α : Type u}, CanLift (WithZero α) α WithZero.co
e fun a => a ≠ 0
-/
lemma log_mul {x y : Mᵐ⁰} (hx : x ≠ 0) (hy : y ≠ 0) : log (x * y) = log x + log y := by
  lift x to Multiplicative M using hx; lift y to Multiplicative M using hy; rfl
/-
**WithZero.exp_nsmul** 是 Mathlib 中的一个定理，位于命名空间 `WithZero`。
形式化陈述：∀ {M : Type u_4} [inst : AddMonoid M] (n : ℕ) (a : M), WithZero.exp (n • a
) = WithZero.exp a ^ n
参数：n : ℕ；a : M；n • a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp← ] lemma exp_nsmul (n : ℕ) (a : M) : exp (n • a) = exp a ^ n := rfl

@[simp]
/-
**WithZero.log_pow** 是 Mathlib 中的一个定理，位于命名空间 `WithZero`。
形式化陈述：∀ {M : Type u_4} [inst : AddMonoid M] (x : WithZero (Multiplicative M)) (n
 : ℕ), (x ^ n).log = n • x.log
参数：x : WithZero (Multiplicative M)；n : ℕ；x ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `nsmul_zero`：∀ {M : Type u_2} [inst : AddMonoid M] (n : ℕ), n • 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma log_pow : ∀ (x : Mᵐ⁰) (n : ℕ), log (x ^ n) = n • log x
  | 0, 0 => by simp
  | 0, n + 1 => by simp
  | (x : Multiplicative M), n => rfl
/-
**WithZero.toAdd_unzero_eq_log** 是 Mathlib 中的一个引理，位于命名空间 `WithZero`。
形式化陈述：toAdd_unzero_eq_log {x : Mᵐ⁰} (hx : x != 0) : (unzero hx).toAdd = log x
参数：hx : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `WithZero.instCanLift`：∀ {α : Type u}, CanLift (WithZero α) α WithZero.co
e fun a => a ≠ 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma toAdd_unzero_eq_log {x : Mᵐ⁰} (hx : x ≠ 0) : (unzero hx).toAdd = log x := by
  lift x to Multiplicative M using hx
  simp [log]

end AddMonoid

section AddGroup
variable [AddGroup G]

/-- The exponential map as an equivalence between `G` and `(Gᵐ⁰)ˣ`. -/
/-
**WithZero.expEquiv** 是 Mathlib 中的一个定义，位于命名空间 `WithZero`。
形式化陈述：expEquiv : G ≃ (Gᵐ⁰)ˣ
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
The exponential map as an equivalence between `G` and `(Gᵐ⁰)ˣ`.
-/
def expEquiv : G ≃ (Gᵐ⁰)ˣ := Multiplicative.ofAdd.trans unitsWithZeroEquiv.symm.toEquiv

/-- The logarithm as an equivalence between `(Gᵐ⁰)ˣ` and `G`. -/
/-
**WithZero.logEquiv** 是 Mathlib 中的一个定义，位于命名空间 `WithZero`。
形式化陈述：logEquiv : (Gᵐ⁰)ˣ ≃ G
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
The logarithm as an equivalence between `(Gᵐ⁰)ˣ` and `G`.
-/
def logEquiv : (Gᵐ⁰)ˣ ≃ G := unitsWithZeroEquiv.toEquiv.trans Multiplicative.toAdd
/-
**WithZero.logEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `WithZero`。
形式化陈述：∀ {G : Type u_5} [inst : AddGroup G], WithZero.logEquiv.symm = WithZero.ex
pEquiv
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
@[simp] lemma logEquiv_symm : (logEquiv (G := G)).symm = expEquiv := rfl
/-
**WithZero.expEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `WithZero`。
形式化陈述：∀ {G : Type u_5} [inst : AddGroup G], WithZero.expEquiv.symm = WithZero.lo
gEquiv
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
@[simp] lemma expEquiv_symm : (expEquiv (G := G)).symm = logEquiv := rfl
/-
**WithZero.coe_expEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `WithZero`。
形式化陈述：∀ {G : Type u_5} [inst : AddGroup G] (a : G), ↑(WithZero.expEquiv a) = Wit
hZero.exp a
参数：a : G；WithZero.expEquiv a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_expEquiv_apply (a : G) : expEquiv a = exp a := rfl
/-
**WithZero.logEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `WithZero`。
形式化陈述：∀ {G : Type u_5} [inst : AddGroup G] (x : (WithZero (Multiplicative G))ˣ),
 WithZero.logEquiv x = (↑x).log
参数：x : (WithZero (Multiplicative G))ˣ；↑x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WithZero.toAdd_unzero_eq_log`：toAdd_unzero_eq_log {x : Mᵐ⁰} (hx : x != 0
) : (unzero hx).toAdd = log x
· 使用定理 `Units.ne_zero`：ne_zero [Nontrivial M₀] (u : M₀ˣ) : (u : M₀) != 0
· 使用定理 `WithZero.instNontrivial`：∀ {α : Type u} [Nonempty α], Nontrivial (WithZe
ro α)
· 使用定理 `One.instNonempty`：∀ {α : Type u} [One α], Nonempty α
-/
@[simp] lemma logEquiv_apply (x : (Gᵐ⁰)ˣ) : logEquiv x = log x := toAdd_unzero_eq_log x.ne_zero
/-
**WithZero.logEquiv_unitsMk0** 是 Mathlib 中的一个引理，位于命名空间 `WithZero`。
形式化陈述：logEquiv_unitsMk0 (x : Gᵐ⁰) (hx) : logEquiv (.mk0 x hx) = log x
参数：x : Gᵐ⁰；hx。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WithZero.logEquiv_apply`：∀ {G : Type u_5} [inst : AddGroup G] (x : (With
Zero (Multiplicative G))ˣ), WithZero.logEquiv x = (↑x).log
-/
lemma logEquiv_unitsMk0 (x : Gᵐ⁰) (hx) : logEquiv (.mk0 x hx) = log x := logEquiv_apply _
/-
**WithZero.exp_sub** 是 Mathlib 中的一个定理，位于命名空间 `WithZero`。
形式化陈述：∀ {G : Type u_5} [inst : AddGroup G] (a b : G), WithZero.exp (a - b) = Wit
hZero.exp a / WithZero.exp b
参数：a b : G；a - b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma exp_sub (a b : G) : exp (a - b) = exp a / exp b := rfl

@[simp]
/-
**WithZero.log_div** 是 Mathlib 中的一个引理，位于命名空间 `WithZero`。
形式化陈述：log_div {x y : Gᵐ⁰} (hx : x != 0) (hy : y != 0) : log (x / y) = log x - lo
g y
参数：hx : x != 0；hy : y != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `WithZero.instCanLift`：∀ {α : Type u}, CanLift (WithZero α) α WithZero.co
e fun a => a ≠ 0
-/
lemma log_div {x y : Gᵐ⁰} (hx : x ≠ 0) (hy : y ≠ 0) : log (x / y) = log x - log y := by
  lift x to Multiplicative G using hx; lift y to Multiplicative G using hy; rfl
/-
**WithZero.exp_neg** 是 Mathlib 中的一个定理，位于命名空间 `WithZero`。
形式化陈述：∀ {G : Type u_5} [inst : AddGroup G] (a : G), WithZero.exp (-a) = (WithZer
o.exp a)⁻¹
参数：a : G；-a；WithZero.exp a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma exp_neg (a : G) : exp (-a) = (exp a)⁻¹ := rfl

@[simp]
/-
**WithZero.log_inv** 是 Mathlib 中的一个定理，位于命名空间 `WithZero`。
形式化陈述：∀ {G : Type u_5} [inst : AddGroup G] (x : WithZero (Multiplicative G)), x⁻
¹.log = -x.log
参数：x : WithZero (Multiplicative G)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma log_inv : ∀ x : Gᵐ⁰, log x⁻¹ = -log x
  | 0 => by simp
  | (x : Multiplicative G) => rfl
/-
**WithZero.exp_zsmul** 是 Mathlib 中的一个定理，位于命名空间 `WithZero`。
形式化陈述：∀ {G : Type u_5} [inst : AddGroup G] (n : ℤ) (a : G), WithZero.exp (n • a)
 = WithZero.exp a ^ n
参数：n : ℤ；a : G；n • a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp← ] lemma exp_zsmul (n : ℤ) (a : G) : exp (n • a) = exp a ^ n := rfl

@[simp]
/-
**WithZero.log_zpow** 是 Mathlib 中的一个引理，位于命名空间 `WithZero`。
形式化陈述：log_zpow (x : Gᵐ⁰) (n : Int) : log (x ^ n) = n • log x
参数：x : Gᵐ⁰；n : Int。
该定理/引理给出了一组等式。
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
· 使用定理 `WithZero.log_pow`：∀ {M : Type u_4} [inst : AddMonoid M] (x : WithZero (M
ultiplicative M)) (n : ℕ), (x ^ n).log = n • x.log
· 使用定理 `natCast_zsmul`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G) (n : ℕ),
 ↑n • a = n • a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zpow_negSucc`：zpow_negSucc (a : G) (n : Nat) : a ^ (Int.negSucc n) = (a 
^ (n + 1))⁻¹
· 使用定理 `WithZero.log_inv`：∀ {G : Type u_5} [inst : AddGroup G] (x : WithZero (Mu
ltiplicative G)), x⁻¹.log = -x.log
· 使用定理 `negSucc_zsmul`：negSucc_zsmul {G} [SubNegMonoid G] (a : G) (n : Nat) : In
t.negSucc n • a = -((n + 1) • a)
-/
lemma log_zpow (x : Gᵐ⁰) (n : ℤ) : log (x ^ n) = n • log x := by cases n <;> simp [log_pow, log_inv]

end AddGroup
end WithZero

namespace MonoidWithZeroHom

/-
**MonoidWithZeroHom.map_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `MonoidWithZeroHom
`。
形式化陈述：∀ {G₀ : Type u_1} {M₀ : Type u_2} [inst : GroupWithZero G₀] [inst_1 : MulZ
eroOneClass M₀] [Nontrivial M₀]   {f : G₀ →*₀ M₀} {x : G₀}, f x = 0 ↔ x = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `instCanLiftUnitsValIsUnit`：∀ {M : Type u_1} [inst : Monoid M], CanLift M
 Mˣ Units.val IsUnit
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isUnit_iff_ne_zero`：isUnit_iff_ne_zero : IsUnit a ↔ a != 0
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `Units.mul_inv`：mul_inv : (a * ↑a⁻¹ : α) = 1
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
protected lemma map_eq_zero_iff {G₀ M₀ : Type*} [GroupWithZero G₀] [MulZeroOneClass M₀]
    [Nontrivial M₀] {f : G₀ →*₀ M₀} {x : G₀} : f x = 0 ↔ x = 0 := by
  refine ⟨?_, by simp +contextual⟩
  contrapose!
  intro hx H
  lift x to G₀ˣ using isUnit_iff_ne_zero.mpr hx
  apply one_ne_zero (α := M₀)
  rw [← map_one f, ← Units.mul_inv x, map_mul, H, zero_mul]

@[simp]
/-
**MonoidWithZeroHom.one_apply_val_unit** 是 Mathlib 中的一个引理，位于命名空间 `MonoidWithZero
Hom`。
形式化陈述：one_apply_val_unit {M₀ N₀ : Type*} [MonoidWithZero M₀] [MulZeroOneClass N₀
] [DecidablePred fun x : M₀ => x = 0] [Nontrivial M₀] [NoZeroDivisors M₀] (x : M
₀ˣ) : (1 : M₀ ->*₀ N₀) x = (1 : N₀)
参数：x : M₀ˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MonoidWithZeroHom.one_apply_of_ne_zero`：one_apply_of_ne_zero {M₀ N₀ : Ty
pe*} [MulZeroOneClass M₀] [MulZeroOneClass N₀] [DecidablePred fun x : M₀ => x = 
0] [Nontrivial M₀] [NoZeroDi…
· 使用定理 `Units.ne_zero`：ne_zero [Nontrivial M₀] (u : M₀ˣ) : (u : M₀) != 0
-/
lemma one_apply_val_unit {M₀ N₀ : Type*} [MonoidWithZero M₀] [MulZeroOneClass N₀]
    [DecidablePred fun x : M₀ ↦ x = 0] [Nontrivial M₀] [NoZeroDivisors M₀] (x : M₀ˣ) :
    (1 : M₀ →*₀ N₀) x = (1 : N₀) :=
  one_apply_of_ne_zero x.ne_zero

/-- The trivial group-with-zero hom is absorbing for composition. -/
@[simp]
/-
**MonoidWithZeroHom.apply_one_apply_eq** 是 Mathlib 中的一个引理，位于命名空间 `MonoidWithZero
Hom`。
形式化陈述：apply_one_apply_eq {M₀ N₀ G₀ : Type*} [MulZeroOneClass M₀] [Nontrivial M₀]
 [NoZeroDivisors M₀] [MulZeroOneClass N₀] [MulZeroOneClass G₀] [DecidablePred fu
n x : M₀ => x = 0] (f : N₀ ->*₀ G₀) (x : M₀) : f ((1 : M₀ ->*₀ N₀) x) = (1 : M₀ 
->*₀ G₀) x
参数：f : N₀ ->*₀ G₀；x : M₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MonoidWithZeroHom.one_apply_zero`：one_apply_zero {M₀ N₀ : Type*} [MulZer
oOneClass M₀] [MulZeroOneClass N₀] [DecidablePred fun x : M₀ => x = 0] [Nontrivi
al M₀] [NoZeroDivisors…
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MonoidWithZeroHom.one_apply_of_ne_zero`：one_apply_of_ne_zero {M₀ N₀ : Ty
pe*} [MulZeroOneClass M₀] [MulZeroOneClass N₀] [DecidablePred fun x : M₀ => x = 
0] [Nontrivial M₀] [NoZeroDi…
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…

--- 原说明 ---
The trivial group-with-zero hom is absorbing for composition.
-/
lemma apply_one_apply_eq {M₀ N₀ G₀ : Type*} [MulZeroOneClass M₀] [Nontrivial M₀] [NoZeroDivisors M₀]
    [MulZeroOneClass N₀] [MulZeroOneClass G₀] [DecidablePred fun x : M₀ ↦ x = 0]
    (f : N₀ →*₀ G₀) (x : M₀) :
    f ((1 : M₀ →*₀ N₀) x) = (1 : M₀ →*₀ G₀) x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [one_apply_of_ne_zero hx, one_apply_of_ne_zero hx, map_one]

/-- The trivial group-with-zero hom is absorbing for composition. -/
@[simp]
/-
**MonoidWithZeroHom.comp_one** 是 Mathlib 中的一个引理，位于命名空间 `MonoidWithZeroHom`。
形式化陈述：comp_one {M₀ N₀ G₀ : Type*} [MulZeroOneClass M₀] [Nontrivial M₀] [NoZeroDi
visors M₀] [MulZeroOneClass N₀] [MulZeroOneClass G₀] [DecidablePred fun x : M₀ =
> x = 0] (f : N₀ ->*₀ G₀) : f.comp (1 : M₀ ->*₀ N₀) = (1 : M₀ ->*₀ G₀)
参数：f : N₀ ->*₀ G₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHom.ext`：∀ {α : Type u_2} {β : Type u_3} [inst : MulZeroOn
eClass α] [inst_1 : MulZeroOneClass β] ⦃f g : α →*₀ β⦄,   (∀ (x : α), f x = g x)
 → f = g
· 使用引理 `MonoidWithZeroHom.apply_one_apply_eq`：apply_one_apply_eq {M₀ N₀ G₀ : Typ
e*} [MulZeroOneClass M₀] [Nontrivial M₀] [NoZeroDivisors M₀] [MulZeroOneClass N₀
] [MulZeroOneClass G₀] [De…

--- 原说明 ---
The trivial group-with-zero hom is absorbing for composition.
-/
lemma comp_one {M₀ N₀ G₀ : Type*} [MulZeroOneClass M₀] [Nontrivial M₀] [NoZeroDivisors M₀]
    [MulZeroOneClass N₀] [MulZeroOneClass G₀] [DecidablePred fun x : M₀ ↦ x = 0]
    (f : N₀ →*₀ G₀) :
    f.comp (1 : M₀ →*₀ N₀) = (1 : M₀ →*₀ G₀) :=
  ext <| apply_one_apply_eq _

end MonoidWithZeroHom

