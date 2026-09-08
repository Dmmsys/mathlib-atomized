/-
Copyright (c) 2024 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# Fixed-point-free automorphisms

This file defines fixed-point-free automorphisms and proves some basic properties.

An automorphism `φ` of a group `G` is fixed-point-free if `1 : G` is the only fixed point of `φ`.
-/

@[expose] public section

namespace MonoidHom

variable {F G : Type*}

section Definitions

variable (φ : G → G)

/-- A function `φ : G → G` is fixed-point-free if `1 : G` is the only fixed point of `φ`. -/
/-
**MonoidHom.FixedPointFree** 是 Mathlib 中的一个定义，位于命名空间 `MonoidHom`。
形式化陈述：FixedPointFree [One G]
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function `φ : G → G` is fixed-point-free if `1 : G` is the only fixed point of
 `φ`.
-/
def FixedPointFree [One G] := ∀ g, φ g = g → g = 1

/-- The commutator map `g ↦ g / φ g`. If `φ g = h * g * h⁻¹`, then `g / φ g` is exactly the
  commutator `[g, h] = g * h * g⁻¹ * h⁻¹`. -/
/-
**MonoidHom.commutatorMap** 是 Mathlib 中的一个定义，位于命名空间 `MonoidHom`。
形式化陈述：commutatorMap [Div G] (g : G)
参数：g : G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The commutator map `g ↦ g / φ g`. If `φ g = h * g * h⁻¹`, then `g / φ g` is exac
tly the
  commutator `[g, h] = g * h * g⁻¹ * h⁻¹`.
-/
def commutatorMap [Div G] (g : G) := g / φ g
/-
**MonoidHom.commutatorMap_apply** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom`。
形式化陈述：∀ {G : Type u_2} (φ : G → G) [inst : Div G] (g : G), MonoidHom.commutatorM
ap φ g = g / φ g
参数：φ : G → G；g : G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem commutatorMap_apply [Div G] (g : G) : commutatorMap φ g = g / φ g := rfl

end Definitions

namespace FixedPointFree
variable [Group G] [FunLike F G G] [MonoidHomClass F G G] {φ : F}

/-
**MonoidHom.FixedPointFree.commutatorMap_injective** 是 Mathlib 中的一个定理，位于命名空间 `Mo
noidHom.FixedPointFree`。
形式化陈述：commutatorMap_injective (hφ : FixedPointFree φ) : Function.Injective (comm
utatorMap φ)
参数：hφ : FixedPointFree φ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `inv_mul_eq_one`：inv_mul_eq_one : a⁻¹ * b = 1 ↔ a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `map_inv`：map_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f 
: F) (a : G) : f a⁻¹ = (f a)⁻¹
· 使用定理 `eq_inv_mul_iff_mul_eq`：eq_inv_mul_iff_mul_eq : a = b⁻¹ * c ↔ b * a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `eq_div_iff_mul_eq'`：eq_div_iff_mul_eq' : a = b / c ↔ a * c = b
· 使用定理 `division_def`：∀ {G : Type u_1} [inst : DivInvMonoid G] (a b : G), a / b 
= a * b⁻¹
-/
theorem commutatorMap_injective (hφ : FixedPointFree φ) : Function.Injective (commutatorMap φ) := by
  refine fun x y h ↦ inv_mul_eq_one.mp <| hφ _ ?_
  rwa [map_mul, map_inv, eq_inv_mul_iff_mul_eq, ← mul_assoc, ← eq_div_iff_mul_eq', ← division_def]

variable [Finite G]
/-
**MonoidHom.FixedPointFree.commutatorMap_surjective** 是 Mathlib 中的一个定理，位于命名空间 `M
onoidHom.FixedPointFree`。
形式化陈述：commutatorMap_surjective (hφ : FixedPointFree φ) : Function.Surjective (co
mmutatorMap φ)
参数：hφ : FixedPointFree φ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.surjective_of_injective`：surjective_of_injective {f : α -> α} (hi
nj : Injective f) : Surjective f
· 使用定理 `MonoidHom.FixedPointFree.commutatorMap_injective`：commutatorMap_injectiv
e (hφ : FixedPointFree φ) : Function.Injective (commutatorMap φ)
-/
theorem commutatorMap_surjective (hφ : FixedPointFree φ) : Function.Surjective (commutatorMap φ) :=
  Finite.surjective_of_injective hφ.commutatorMap_injective
/-
**MonoidHom.FixedPointFree.prod_pow_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `MonoidHom.
FixedPointFree`。
形式化陈述：prod_pow_eq_one (hφ : FixedPointFree φ) {n : Nat} (hn : φ^[n] = _root_.id)
 (g : G) : ((List.range n).map (fun k => φ^[k] g)).prod = 1
参数：hφ : FixedPointFree φ；hn : φ^[n] = _root_.id；g : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.FixedPointFree.commutatorMap_surjective`：commutatorMap_surject
ive (hφ : FixedPointFree φ) : Function.Surjective (commutatorMap φ)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `iterate_map_div`：iterate_map_div {M F : Type*} [Group M] [FunLike F M M]
 [MonoidHomClass F M M] (f : F) (n : Nat) (x y : M) : f^[n] (x / y) = f^[n] x / 
f^[n]…
· 使用定理 `List.prod_range_div'`：prod_range_div' (n : Nat) (f : Nat -> G) : ((range
 n).map fun k => f k / f (k + 1)).prod = f 0 / f n
· 使用定理 `Function.iterate_zero_apply`：iterate_zero_apply (x : α) : f^[0] x = x
· 使用定理 `Function.id_def`：∀ {α : Sort u_1}, id = fun x => x
· 使用定理 `div_self'`：div_self' (a : G) : a / a = 1
-/
theorem prod_pow_eq_one (hφ : FixedPointFree φ) {n : ℕ} (hn : φ^[n] = _root_.id) (g : G) :
    ((List.range n).map (fun k ↦ φ^[k] g)).prod = 1 := by
  obtain ⟨g, rfl⟩ := commutatorMap_surjective hφ g
  simp only [commutatorMap_apply, iterate_map_div, ← Function.iterate_succ_apply]
  rw [List.prod_range_div', Function.iterate_zero_apply, hn, Function.id_def, div_self']
/-
**MonoidHom.FixedPointFree.coe_eq_inv_of_sq_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Mo
noidHom.FixedPointFree`。
形式化陈述：coe_eq_inv_of_sq_eq_one (hφ : FixedPointFree φ) (h2 : φ^[2] = _root_.id) :
 ⇑φ = (·⁻¹)
参数：hφ : FixedPointFree φ；h2 : φ^[2] = _root_.id。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `List.range_succ`：∀ {n : ℕ}, List.range n.succ = List.range n ++ [n]
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Function.iterate_one`：iterate_one : f^[1] = f
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MonoidHom.FixedPointFree.prod_pow_eq_one`：prod_pow_eq_one (hφ : FixedPoi
ntFree φ) {n : Nat} (hn : φ^[n] = _root_.id) (g : G) : ((List.range n).map (fun 
k => φ^[k] g)).prod = 1
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inv_eq_iff_mul_eq_one`：inv_eq_iff_mul_eq_one : a⁻¹ = b ↔ a * b = 1
-/
theorem coe_eq_inv_of_sq_eq_one (hφ : FixedPointFree φ) (h2 : φ^[2] = _root_.id) : ⇑φ = (·⁻¹) := by
  ext g
  have key : g * φ g = 1 := by simpa [List.range_succ] using hφ.prod_pow_eq_one h2 g
  rwa [← inv_eq_iff_mul_eq_one, eq_comm] at key

section Involutive

/-
**MonoidHom.FixedPointFree.coe_eq_inv_of_involutive** 是 Mathlib 中的一个定理，位于命名空间 `M
onoidHom.FixedPointFree`。
形式化陈述：coe_eq_inv_of_involutive (hφ : FixedPointFree φ) (h2 : Function.Involutive
 φ) : ⇑φ = (·⁻¹)
参数：hφ : FixedPointFree φ；h2 : Function.Involutive φ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.FixedPointFree.coe_eq_inv_of_sq_eq_one`：coe_eq_inv_of_sq_eq_on
e (hφ : FixedPointFree φ) (h2 : φ^[2] = _root_.id) : ⇑φ = (·⁻¹)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem coe_eq_inv_of_involutive (hφ : FixedPointFree φ) (h2 : Function.Involutive φ) :
    ⇑φ = (·⁻¹) :=
  coe_eq_inv_of_sq_eq_one hφ (funext h2)
/-
**MonoidHom.FixedPointFree.commute_all_of_involutive** 是 Mathlib 中的一个定理，位于命名空间 `
MonoidHom.FixedPointFree`。
形式化陈述：commute_all_of_involutive (hφ : FixedPointFree φ) (h2 : Function.Involutiv
e φ) (g h : G) : Commute g h
参数：hφ : FixedPointFree φ；h2 : Function.Involutive φ；g h : G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `inv_eq_iff_eq_inv`：inv_eq_iff_eq_inv : a⁻¹ = b ↔ a = b⁻¹
· 使用定理 `MonoidHom.FixedPointFree.coe_eq_inv_of_involutive`：coe_eq_inv_of_involut
ive (hφ : FixedPointFree φ) (h2 : Function.Involutive φ) : ⇑φ = (·⁻¹)
-/
theorem commute_all_of_involutive (hφ : FixedPointFree φ) (h2 : Function.Involutive φ) (g h : G) :
    Commute g h := by
  have key := map_mul φ g h
  rwa [hφ.coe_eq_inv_of_involutive h2, inv_eq_iff_eq_inv, mul_inv_rev, inv_inv, inv_inv] at key

/-- If a finite group admits a fixed-point-free involution, then it is commutative. -/
@[instance_reducible]
/-
**MonoidHom.FixedPointFree.commGroupOfInvolutive** 是 Mathlib 中的一个定义，位于命名空间 `Mono
idHom.FixedPointFree`。
形式化陈述：commGroupOfInvolutive (hφ : FixedPointFree φ) (h2 : Function.Involutive φ)
 : CommGroup G
参数：hφ : FixedPointFree φ；h2 : Function.Involutive φ。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.FixedPointFree.commute_all_of_involutive`：commute_all_of_invol
utive (hφ : FixedPointFree φ) (h2 : Function.Involutive φ) (g h : G) : Commute g
 h

--- 原说明 ---
If a finite group admits a fixed-point-free involution, then it is commutative.
-/
def commGroupOfInvolutive (hφ : FixedPointFree φ) (h2 : Function.Involutive φ) :
    CommGroup G := .mk (hφ.commute_all_of_involutive h2)
/-
**MonoidHom.FixedPointFree.orderOf_ne_two_of_involutive** 是 Mathlib 中的一个定理，位于命名空
间 `MonoidHom.FixedPointFree`。
形式化陈述：orderOf_ne_two_of_involutive (hφ : FixedPointFree φ) (h2 : Function.Involu
tive φ) (g : G) : orderOf g != 2
参数：hφ : FixedPointFree φ；h2 : Function.Involutive φ；g : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonoidHom.FixedPointFree.coe_eq_inv_of_involutive`：coe_eq_inv_of_involut
ive (hφ : FixedPointFree φ) (h2 : Function.Involutive φ) : ⇑φ = (·⁻¹)
· 使用定理 `inv_eq_iff_mul_eq_one`：inv_eq_iff_mul_eq_one : a⁻¹ = b ↔ a * b = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `pow_orderOf_eq_one`：pow_orderOf_eq_one (x : G) : x ^ orderOf x = 1
· 使用定理 `orderOf_one`：orderOf_one : orderOf (1 : G) = 1
· 使用定理 `of_decide_eq_false`：∀ {p : Prop} [inst : Decidable p], decide p = false 
→ ¬p
-/
theorem orderOf_ne_two_of_involutive (hφ : FixedPointFree φ) (h2 : Function.Involutive φ) (g : G) :
    orderOf g ≠ 2 := by
  intro hg
  have key : φ g = g := by
    rw [hφ.coe_eq_inv_of_involutive h2, inv_eq_iff_mul_eq_one, ← sq, ← hg, pow_orderOf_eq_one]
  rw [hφ g key, orderOf_one] at hg
  contradiction
/-
**MonoidHom.FixedPointFree.odd_card_of_involutive** 是 Mathlib 中的一个定理，位于命名空间 `Mon
oidHom.FixedPointFree`。
形式化陈述：odd_card_of_involutive (hφ : FixedPointFree φ) (h2 : Function.Involutive φ
) : Odd (Nat.card G)
参数：hφ : FixedPointFree φ；h2 : Function.Involutive φ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `exists_prime_orderOf_dvd_card`：∀ {G : Type u_3} [inst : Group G] [inst_1
 : Fintype G] (p : ℕ) [hp : Fact (Nat.Prime p)],   p ∣ Fintype.card G → ∃ x, ord
erOf x = p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用引理 `even_iff_two_dvd`：even_iff_two_dvd : Even a ↔ 2 ∣ a
· 使用定理 `Nat.not_odd_iff_even`：∀ {n : ℕ}, ¬Odd n ↔ Even n
· 使用定理 `MonoidHom.FixedPointFree.orderOf_ne_two_of_involutive`：orderOf_ne_two_of
_involutive (hφ : FixedPointFree φ) (h2 : Function.Involutive φ) (g : G) : order
Of g != 2
-/
theorem odd_card_of_involutive (hφ : FixedPointFree φ) (h2 : Function.Involutive φ) :
    Odd (Nat.card G) := by
  have := Fintype.ofFinite G
  by_contra h
  rw [Nat.not_odd_iff_even, even_iff_two_dvd, Nat.card_eq_fintype_card] at h
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card 2 h
  exact hφ.orderOf_ne_two_of_involutive h2 g hg
/-
**MonoidHom.FixedPointFree.odd_orderOf_of_involutive** 是 Mathlib 中的一个定理，位于命名空间 `
MonoidHom.FixedPointFree`。
形式化陈述：odd_orderOf_of_involutive (hφ : FixedPointFree φ) (h2 : Function.Involutiv
e φ) (g : G) : Odd (orderOf g)
参数：hφ : FixedPointFree φ；h2 : Function.Involutive φ；g : G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Odd.of_dvd_nat`：Odd.of_dvd_nat (hn : Odd n) (hm : m ∣ n) : Odd m
· 使用定理 `MonoidHom.FixedPointFree.odd_card_of_involutive`：odd_card_of_involutive 
(hφ : FixedPointFree φ) (h2 : Function.Involutive φ) : Odd (Nat.card G)
· 使用定理 `orderOf_dvd_natCard`：orderOf_dvd_natCard {G : Type*} [Group G] (x : G) :
 orderOf x ∣ Nat.card G
-/
theorem odd_orderOf_of_involutive (hφ : FixedPointFree φ) (h2 : Function.Involutive φ) (g : G) :
    Odd (orderOf g) :=
  Odd.of_dvd_nat (hφ.odd_card_of_involutive h2) (orderOf_dvd_natCard g)

end Involutive

end FixedPointFree

end MonoidHom

