/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Robert Y. Lewis
-/
module

public import Mathlib.Algebra.MvPolynomial.Counit
public import Mathlib.Algebra.MvPolynomial.Invertible
public import Mathlib.RingTheory.WittVector.Defs

/-!
# Witt vectors

This file verifies that the ring operations on `WittVector p R`
satisfy the axioms of a commutative ring.

## Main definitions

* `WittVector.map`: lifts a ring homomorphism `R →+* S` to a ring homomorphism `𝕎 R →+* 𝕎 S`.
* `WittVector.ghostComponent n x`: evaluates the `n`th Witt polynomial
  on the first `n` coefficients of `x`, producing a value in `R`.
  This is a ring homomorphism.
* `WittVector.ghostMap`: a ring homomorphism `𝕎 R →+* (ℕ → R)`, obtained by packaging
  all the ghost components together.
  If `p` is invertible in `R`, then the ghost map is an equivalence,
  which we use to define the ring operations on `𝕎 R`.
* `WittVector.CommRing`: the ring structure induced by the ghost components.

## Notation

We use notation `𝕎 R`, entered `\bbW`, for the Witt vectors over `R`.

## Implementation details

As we prove that the ghost components respect the ring operations, we face a number of repetitive
proofs. To avoid duplicating code we factor these proofs into a custom tactic, only slightly more
powerful than a tactic macro. This tactic is not particularly useful outside of its applications
in this file.

## References

* [Hazewinkel, *Witt Vectors*][Haze09]

* [Commelin and Lewis, *Formalizing the Ring of Witt Vectors*][CL21]

-/

@[expose] public section


noncomputable section

open MvPolynomial Function

variable {p : ℕ} {R S : Type*} [CommRing R] [CommRing S]
variable {α : Type*} {β : Type*}

local notation "𝕎" => WittVector p
local notation "W_" => wittPolynomial p

-- type as `\bbW`
open scoped Witt

namespace WittVector

/-- `f : α → β` induces a map from `𝕎 α` to `𝕎 β` by applying `f` componentwise.
If `f` is a ring homomorphism, then so is `f`, see `WittVector.map f`. -/
/-
**WittVector.mapFun** 是 Mathlib 中的一个定义，位于命名空间 `WittVector`。
形式化陈述：mapFun (f : α -> β) : 𝕎 α -> 𝕎 β
参数：f : α -> β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`f : α → β` induces a map from `𝕎 α` to `𝕎 β` by applying `f` componentwise.
If `f` is a ring homomorphism, then so is `f`, see `WittVector.map f`.
-/
def mapFun (f : α → β) : 𝕎 α → 𝕎 β := fun x => mk _ (f ∘ x.coeff)

namespace mapFun

/-
**WittVector.mapFun.injective** 是 Mathlib 中的一个定理，位于命名空间 `WittVector.mapFun`。
形式化陈述：injective (f : α -> β) (hf : Injective f) : Injective (mapFun f : 𝕎 α -> 𝕎
 β)
参数：f : α -> β；hf : Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WittVector.ext`：ext {x y : 𝕎 R} (h : forall n, x.coeff n = y.coeff n) : 
x = y
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem injective (f : α → β) (hf : Injective f) : Injective (mapFun f : 𝕎 α → 𝕎 β) :=
  fun _ _ h => ext fun n => hf (congr_arg (fun x => coeff x n) h :)
/-
**WittVector.mapFun.surjective** 是 Mathlib 中的一个定理，位于命名空间 `WittVector.mapFun`。
形式化陈述：surjective (f : α -> β) (hf : Surjective f) : Surjective (mapFun f : 𝕎 α -
> 𝕎 β)
参数：f : α -> β；hf : Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WittVector.ext`：ext {x y : 𝕎 R} (h : forall n, x.coeff n = y.coeff n) : 
x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem surjective (f : α → β) (hf : Surjective f) : Surjective (mapFun f : 𝕎 α → 𝕎 β) := fun x =>
  ⟨mk _ fun n => Classical.choose <| hf <| x.coeff n,
    by ext n; simp only [mapFun, coeff_mk, comp_apply, Classical.choose_spec (hf (x.coeff n))]⟩

/-- Auxiliary tactic for showing that `mapFun` respects the ring operations. -/
macro "map_fun_tac" : tactic => `(tactic| (
  -- TODO: the Lean 3 version of this tactic was more functional
  ext n
  simp only [mapFun, mk, comp_apply, zero_coeff, map_zero,
    -- the lemmas on the next line do not have the `simp` tag in mathlib4
    add_coeff, sub_coeff, mul_coeff, neg_coeff, nsmul_coeff, zsmul_coeff, pow_coeff,
    peval, map_aeval, algebraMap_int_eq, coe_eval₂Hom] <;>
  try { cases n <;> simp <;> done } <;> -- this line solves `one`
  apply eval₂Hom_congr (RingHom.ext_int _ _) _ rfl <;>
  ext ⟨i, k⟩ <;>
    fin_cases i <;> rfl))

variable [Fact p.Prime]
-- Porting note: using `(x y : 𝕎 R)` instead of `(x y : WittVector p R)` produced sorries.
variable (f : R →+* S) (x y : WittVector p R)

--  and until `pow`.
-- We do not tag these lemmas as `@[simp]` because they will be bundled in `map` later on.
/-
**WittVector.mapFun.zero** 是 Mathlib 中的一个定理，位于命名空间 `WittVector.mapFun`。
形式化陈述：zero : mapFun f (0 : 𝕎 R) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WittVector.ext`：ext {x y : 𝕎 R} (h : forall n, x.coeff n = y.coeff n) : 
x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WittVector.zero_coeff`：zero_coeff (n : Nat) : (0 : 𝕎 R).coeff n = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem zero : mapFun f (0 : 𝕎 R) = 0 := by map_fun_tac
/-
**WittVector.mapFun.one** 是 Mathlib 中的一个定理，位于命名空间 `WittVector.mapFun`。
形式化陈述：one : mapFun f (1 : 𝕎 R) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WittVector.ext`：ext {x y : 𝕎 R} (h : forall n, x.coeff n = y.coeff n) : 
x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WittVector.one_coeff_zero`：one_coeff_zero : (1 : 𝕎 R).coeff 0 = 1
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WittVector.one_coeff_eq_of_pos`：one_coeff_eq_of_pos (n : Nat) (hn : 0 < 
n) : coeff (1 : 𝕎 R) n = 0
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
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
-/
theorem one : mapFun f (1 : 𝕎 R) = 1 := by map_fun_tac
/-
**WittVector.mapFun.add** 是 Mathlib 中的一个定理，位于命名空间 `WittVector.mapFun`。
形式化陈述：add : mapFun f (x + y) = mapFun f x + mapFun f y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WittVector.ext`：ext {x y : 𝕎 R} (h : forall n, x.coeff n = y.coeff n) : 
x = y
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `WittVector.add_coeff`：add_coeff (x y : 𝕎 R) (n : Nat) : (x + y).coeff n 
= peval (wittAdd p n) ![x.coeff, y.coeff]
· 使用定理 `MvPolynomial.map_aeval`：map_aeval {B : Type*} [CommSemiring B] (g : σ ->
 S₁) (φ : S₁ ->+* B) (p : MvPolynomial σ R) : φ (aeval g p) = eval₂Hom (φ.comp (
algebraMap R…
· 使用定理 `MvPolynomial.eval₂Hom_congr`：eval₂Hom_congr {f₁ f₂ : R ->+* S₁} {g₁ g₂ :
 σ -> S₁} {p₁ p₂ : MvPolynomial σ R} : f₁ = f₂ -> g₁ = g₂ -> p₁ = p₂ -> eval₂Hom
 f₁ g₁ p₁ = eval₂…
· 使用定理 `RingHom.ext_int`：ext_int {R : Type*} [NonAssocSemiring R] (f g : Int ->+
* R) : f = g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
theorem add : mapFun f (x + y) = mapFun f x + mapFun f y := by map_fun_tac
/-
**WittVector.mapFun.sub** 是 Mathlib 中的一个定理，位于命名空间 `WittVector.mapFun`。
形式化陈述：sub : mapFun f (x - y) = mapFun f x - mapFun f y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WittVector.ext`：ext {x y : 𝕎 R} (h : forall n, x.coeff n = y.coeff n) : 
x = y
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `WittVector.sub_coeff`：sub_coeff (x y : 𝕎 R) (n : Nat) : (x - y).coeff n 
= peval (wittSub p n) ![x.coeff, y.coeff]
· 使用定理 `MvPolynomial.map_aeval`：map_aeval {B : Type*} [CommSemiring B] (g : σ ->
 S₁) (φ : S₁ ->+* B) (p : MvPolynomial σ R) : φ (aeval g p) = eval₂Hom (φ.comp (
algebraMap R…
· 使用定理 `MvPolynomial.eval₂Hom_congr`：eval₂Hom_congr {f₁ f₂ : R ->+* S₁} {g₁ g₂ :
 σ -> S₁} {p₁ p₂ : MvPolynomial σ R} : f₁ = f₂ -> g₁ = g₂ -> p₁ = p₂ -> eval₂Hom
 f₁ g₁ p₁ = eval₂…
· 使用定理 `RingHom.ext_int`：ext_int {R : Type*} [NonAssocSemiring R] (f g : Int ->+
* R) : f = g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
theorem sub : mapFun f (x - y) = mapFun f x - mapFun f y := by map_fun_tac
/-
**WittVector.mapFun.mul** 是 Mathlib 中的一个定理，位于命名空间 `WittVector.mapFun`。
形式化陈述：mul : mapFun f (x * y) = mapFun f x * mapFun f y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WittVector.ext`：ext {x y : 𝕎 R} (h : forall n, x.coeff n = y.coeff n) : 
x = y
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `WittVector.mul_coeff`：mul_coeff (x y : 𝕎 R) (n : Nat) : (x * y).coeff n 
= peval (wittMul p n) ![x.coeff, y.coeff]
· 使用定理 `MvPolynomial.map_aeval`：map_aeval {B : Type*} [CommSemiring B] (g : σ ->
 S₁) (φ : S₁ ->+* B) (p : MvPolynomial σ R) : φ (aeval g p) = eval₂Hom (φ.comp (
algebraMap R…
· 使用定理 `MvPolynomial.eval₂Hom_congr`：eval₂Hom_congr {f₁ f₂ : R ->+* S₁} {g₁ g₂ :
 σ -> S₁} {p₁ p₂ : MvPolynomial σ R} : f₁ = f₂ -> g₁ = g₂ -> p₁ = p₂ -> eval₂Hom
 f₁ g₁ p₁ = eval₂…
· 使用定理 `RingHom.ext_int`：ext_int {R : Type*} [NonAssocSemiring R] (f g : Int ->+
* R) : f = g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
theorem mul : mapFun f (x * y) = mapFun f x * mapFun f y := by map_fun_tac
/-
**WittVector.mapFun.neg** 是 Mathlib 中的一个定理，位于命名空间 `WittVector.mapFun`。
形式化陈述：neg : mapFun f (-x) = -mapFun f x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WittVector.ext`：ext {x y : 𝕎 R} (h : forall n, x.coeff n = y.coeff n) : 
x = y
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `WittVector.neg_coeff`：neg_coeff (x : 𝕎 R) (n : Nat) : (-x).coeff n = pev
al (wittNeg p n) ![x.coeff]
· 使用定理 `MvPolynomial.map_aeval`：map_aeval {B : Type*} [CommSemiring B] (g : σ ->
 S₁) (φ : S₁ ->+* B) (p : MvPolynomial σ R) : φ (aeval g p) = eval₂Hom (φ.comp (
algebraMap R…
· 使用定理 `MvPolynomial.eval₂Hom_congr`：eval₂Hom_congr {f₁ f₂ : R ->+* S₁} {g₁ g₂ :
 σ -> S₁} {p₁ p₂ : MvPolynomial σ R} : f₁ = f₂ -> g₁ = g₂ -> p₁ = p₂ -> eval₂Hom
 f₁ g₁ p₁ = eval₂…
· 使用定理 `RingHom.ext_int`：ext_int {R : Type*} [NonAssocSemiring R] (f g : Int ->+
* R) : f = g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
theorem neg : mapFun f (-x) = -mapFun f x := by map_fun_tac
/-
**WittVector.mapFun.nsmul** 是 Mathlib 中的一个定理，位于命名空间 `WittVector.mapFun`。
形式化陈述：nsmul (n : Nat) (x : WittVector p R) : mapFun f (n • x) = n • mapFun f x
参数：n : Nat；x : WittVector p R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WittVector.ext`：ext {x y : 𝕎 R} (h : forall n, x.coeff n = y.coeff n) : 
x = y
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `WittVector.nsmul_coeff`：nsmul_coeff (m : Nat) (x : 𝕎 R) (n : Nat) : (m •
 x).coeff n = peval (wittNSMul p m n) ![x.coeff]
· 使用定理 `MvPolynomial.map_aeval`：map_aeval {B : Type*} [CommSemiring B] (g : σ ->
 S₁) (φ : S₁ ->+* B) (p : MvPolynomial σ R) : φ (aeval g p) = eval₂Hom (φ.comp (
algebraMap R…
· 使用定理 `MvPolynomial.eval₂Hom_congr`：eval₂Hom_congr {f₁ f₂ : R ->+* S₁} {g₁ g₂ :
 σ -> S₁} {p₁ p₂ : MvPolynomial σ R} : f₁ = f₂ -> g₁ = g₂ -> p₁ = p₂ -> eval₂Hom
 f₁ g₁ p₁ = eval₂…
· 使用定理 `RingHom.ext_int`：ext_int {R : Type*} [NonAssocSemiring R] (f g : Int ->+
* R) : f = g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
theorem nsmul (n : ℕ) (x : WittVector p R) : mapFun f (n • x) = n • mapFun f x := by map_fun_tac
/-
**WittVector.mapFun.zsmul** 是 Mathlib 中的一个定理，位于命名空间 `WittVector.mapFun`。
形式化陈述：zsmul (z : Int) (x : WittVector p R) : mapFun f (z • x) = z • mapFun f x
参数：z : Int；x : WittVector p R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WittVector.ext`：ext {x y : 𝕎 R} (h : forall n, x.coeff n = y.coeff n) : 
x = y
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `WittVector.zsmul_coeff`：zsmul_coeff (m : Int) (x : 𝕎 R) (n : Nat) : (m •
 x).coeff n = peval (wittZSMul p m n) ![x.coeff]
· 使用定理 `MvPolynomial.map_aeval`：map_aeval {B : Type*} [CommSemiring B] (g : σ ->
 S₁) (φ : S₁ ->+* B) (p : MvPolynomial σ R) : φ (aeval g p) = eval₂Hom (φ.comp (
algebraMap R…
· 使用定理 `MvPolynomial.eval₂Hom_congr`：eval₂Hom_congr {f₁ f₂ : R ->+* S₁} {g₁ g₂ :
 σ -> S₁} {p₁ p₂ : MvPolynomial σ R} : f₁ = f₂ -> g₁ = g₂ -> p₁ = p₂ -> eval₂Hom
 f₁ g₁ p₁ = eval₂…
· 使用定理 `RingHom.ext_int`：ext_int {R : Type*} [NonAssocSemiring R] (f g : Int ->+
* R) : f = g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
theorem zsmul (z : ℤ) (x : WittVector p R) : mapFun f (z • x) = z • mapFun f x := by map_fun_tac
/-
**WittVector.mapFun.pow** 是 Mathlib 中的一个定理，位于命名空间 `WittVector.mapFun`。
形式化陈述：pow (n : Nat) : mapFun f (x ^ n) = mapFun f x ^ n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WittVector.ext`：ext {x y : 𝕎 R} (h : forall n, x.coeff n = y.coeff n) : 
x = y
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `WittVector.pow_coeff`：pow_coeff (m : Nat) (x : 𝕎 R) (n : Nat) : (x ^ m).
coeff n = peval (wittPow p m n) ![x.coeff]
· 使用定理 `MvPolynomial.map_aeval`：map_aeval {B : Type*} [CommSemiring B] (g : σ ->
 S₁) (φ : S₁ ->+* B) (p : MvPolynomial σ R) : φ (aeval g p) = eval₂Hom (φ.comp (
algebraMap R…
· 使用定理 `MvPolynomial.eval₂Hom_congr`：eval₂Hom_congr {f₁ f₂ : R ->+* S₁} {g₁ g₂ :
 σ -> S₁} {p₁ p₂ : MvPolynomial σ R} : f₁ = f₂ -> g₁ = g₂ -> p₁ = p₂ -> eval₂Hom
 f₁ g₁ p₁ = eval₂…
· 使用定理 `RingHom.ext_int`：ext_int {R : Type*} [NonAssocSemiring R] (f g : Int ->+
* R) : f = g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
theorem pow (n : ℕ) : mapFun f (x ^ n) = mapFun f x ^ n := by map_fun_tac
/-
**WittVector.mapFun.natCast** 是 Mathlib 中的一个定理，位于命名空间 `WittVector.mapFun`。
形式化陈述：natCast (n : Nat) : mapFun f (n : 𝕎 R) = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WittVector.mapFun.zero`：zero : mapFun f (0 : 𝕎 R) = 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `WittVector.mapFun.add`：add : mapFun f (x + y) = mapFun f x + mapFun f y
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `WittVector.mapFun.one`：one : mapFun f (1 : 𝕎 R) = 1
-/
theorem natCast (n : ℕ) : mapFun f (n : 𝕎 R) = n :=
  show mapFun f n.unaryCast = (n : WittVector p S) by
    induction n <;> simp [*, Nat.unaryCast, add, one, zero] <;> rfl
/-
**WittVector.mapFun.intCast** 是 Mathlib 中的一个定理，位于命名空间 `WittVector.mapFun`。
形式化陈述：intCast (n : Int) : mapFun f (n : 𝕎 R) = n
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WittVector.mapFun.natCast`：natCast (n : Nat) : mapFun f (n : 𝕎 R) = n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `WittVector.mapFun.neg`：neg : mapFun f (-x) = -mapFun f x
-/
theorem intCast (n : ℤ) : mapFun f (n : 𝕎 R) = n :=
  show mapFun f n.castDef = (n : WittVector p S) by
    cases n <;> simp [*, Int.castDef, neg, natCast] <;> rfl

end mapFun

end WittVector

namespace WittVector

set_option backward.privateInPublic true in
/-- Evaluates the `n`th Witt polynomial on the first `n` coefficients of `x`,
producing a value in `R`.
This function will be bundled as the ring homomorphism `WittVector.ghostMap`
once the ring structure is available,
but we rely on it to set up the ring structure in the first place. -/
/-
**WittVector.ghostFun** 是 Mathlib 中的一个定义，位于命名空间 `WittVector`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Evaluates the `n`th Witt polynomial on the first `n` coefficients of `x`,
producing a value in `R`.
This function will be bundled as the ring homomorphism `WittVector.ghostMap`
once the ring structure is available,
but we rely on it to set up the ring structure in the first place.
-/
private def ghostFun : 𝕎 R → ℕ → R := fun x n => aeval x.coeff (W_ ℤ n)

section Tactic
open Lean Elab Tactic

/-- An auxiliary tactic for proving that `ghostFun` respects the ring operations. -/
elab "ghost_fun_tac " φ:term ", " fn:term : tactic => do
  evalTactic (← `(tactic| (
  ext n
  have := congr_fun (congr_arg (@peval R _ _) (wittStructureInt_prop p $φ n)) $fn
  simp only [wittZero, OfNat.ofNat, Zero.zero, wittOne, One.one,
    HAdd.hAdd, Add.add, HSub.hSub, Sub.sub, Neg.neg, HMul.hMul, Mul.mul, HPow.hPow, Pow.pow,
    wittNSMul, wittZSMul, HSMul.hSMul, SMul.smul]
  simpa +unfoldPartialApp [WittVector.ghostFun, aeval_rename, aeval_bind₁,
    comp, uncurry, peval, eval] using! this
  )))

end Tactic

section GhostFun

-- The following lemmas are not `@[simp]` because they will be bundled in `ghostMap` later on.

@[local simp]
/-
**WittVector.matrix_vecEmpty_coeff** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：matrix_vecEmpty_coeff {R} (i j) : @coeff p R (Matrix.vecEmpty i) j = (Matr
ix.vecEmpty i : Nat -> R) j
参数：i j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
theorem matrix_vecEmpty_coeff {R} (i j) :
    @coeff p R (Matrix.vecEmpty i) j = (Matrix.vecEmpty i : ℕ → R) j := by
  rcases i with ⟨_ | _ | _ | _ | i_val, ⟨⟩⟩

variable [Fact p.Prime]
variable (x y : WittVector p R)

set_option backward.privateInPublic true in
/-
**WittVector.ghostFun_zero** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem ghostFun_zero : ghostFun (0 : 𝕎 R) = 0 := by
  ghost_fun_tac 0, ![]

set_option backward.privateInPublic true in
/-
**WittVector.ghostFun_one** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem ghostFun_one : ghostFun (1 : 𝕎 R) = 1 := by
  ghost_fun_tac 1, ![]

set_option backward.privateInPublic true in
/-
**WittVector.ghostFun_add** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem ghostFun_add : ghostFun (x + y) = ghostFun x + ghostFun y := by
  ghost_fun_tac X 0 + X 1, ![x.coeff, y.coeff]
/-
**WittVector.ghostFun_natCast** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem ghostFun_natCast (i : ℕ) : ghostFun (i : 𝕎 R) = i :=
  show ghostFun i.unaryCast = _ by
    induction i <;> simp [*, Nat.unaryCast, ghostFun_zero, ghostFun_one, ghostFun_add]
/-
**WittVector.ghostFun_sub** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem ghostFun_sub : ghostFun (x - y) = ghostFun x - ghostFun y := by
  ghost_fun_tac X 0 - X 1, ![x.coeff, y.coeff]

set_option backward.privateInPublic true in
/-
**WittVector.ghostFun_mul** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem ghostFun_mul : ghostFun (x * y) = ghostFun x * ghostFun y := by
  ghost_fun_tac X 0 * X 1, ![x.coeff, y.coeff]
/-
**WittVector.ghostFun_neg** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem ghostFun_neg : ghostFun (-x) = -ghostFun x := by ghost_fun_tac -X 0, ![x.coeff]
/-
**WittVector.ghostFun_intCast** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem ghostFun_intCast (i : ℤ) : ghostFun (i : 𝕎 R) = i :=
  show ghostFun i.castDef = _ by
    cases i <;> simp [*, Int.castDef, ghostFun_natCast, ghostFun_neg]
/-
**WittVector.ghostFun_nsmul** 是 Mathlib 中的一个引理，位于命名空间 `WittVector`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma ghostFun_nsmul (m : ℕ) (x : WittVector p R) : ghostFun (m • x) = m • ghostFun x := by
  ghost_fun_tac m • (X 0), ![x.coeff]
/-
**WittVector.ghostFun_zsmul** 是 Mathlib 中的一个引理，位于命名空间 `WittVector`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma ghostFun_zsmul (m : ℤ) (x : WittVector p R) : ghostFun (m • x) = m • ghostFun x := by
  ghost_fun_tac m • (X 0), ![x.coeff]
/-
**WittVector.ghostFun_pow** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem ghostFun_pow (m : ℕ) : ghostFun (x ^ m) = ghostFun x ^ m := by
  ghost_fun_tac X 0 ^ m, ![x.coeff]

end GhostFun

variable (p) (R)

set_option backward.privateInPublic true in
/-- The bijection between `𝕎 R` and `ℕ → R`, under the assumption that `p` is invertible in `R`.
In `WittVector.ghostEquiv` we upgrade this to an isomorphism of rings. -/
/-
**WittVector.ghostEquiv'** 是 Mathlib 中的一个定义，位于命名空间 `WittVector`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The bijection between `𝕎 R` and `ℕ → R`, under the assumption that `p` is invert
ible in `R`.
In `WittVector.ghostEquiv` we upgrade this to an isomorphism of rings.
-/
private def ghostEquiv' [Invertible (p : R)] : 𝕎 R ≃ (ℕ → R) where
  toFun := ghostFun
  invFun x := mk p fun n => aeval x (xInTermsOfW p R n)
  left_inv := by
    intro x
    ext n
    have := bind₁_wittPolynomial_xInTermsOfW p R n
    apply_fun aeval x.coeff at this
    simpa +unfoldPartialApp only [aeval_bind₁, aeval_X, ghostFun,
      aeval_wittPolynomial]
  right_inv := by
    intro x
    ext n
    have := bind₁_xInTermsOfW_wittPolynomial p R n
    apply_fun aeval x at this
    simpa only [aeval_bind₁, aeval_X, ghostFun, aeval_wittPolynomial]

variable [Fact p.Prime]

private local instance comm_ring_aux₁ : CommRing (𝕎 (MvPolynomial R ℚ)) :=
  (ghostEquiv' p (MvPolynomial R ℚ)).injective.commRing ghostFun ghostFun_zero ghostFun_one
    ghostFun_add ghostFun_mul ghostFun_neg ghostFun_sub ghostFun_nsmul ghostFun_zsmul
    ghostFun_pow ghostFun_natCast ghostFun_intCast

set_option backward.privateInPublic true in
private local instance comm_ring_aux₂ : CommRing (𝕎 (MvPolynomial R ℤ)) :=
  (mapFun.injective _ <| map_injective (Int.castRingHom ℚ) Int.cast_injective).commRing _
    (mapFun.zero _) (mapFun.one _) (mapFun.add _) (mapFun.mul _) (mapFun.neg _) (mapFun.sub _)
    (mapFun.nsmul _) (mapFun.zsmul _) (mapFun.pow _) (mapFun.natCast _) (mapFun.intCast _)

/-- The commutative ring structure on `𝕎 R`. -/
/-
**WittVector.** 是 Mathlib 中的一个实例，位于命名空间 `WittVector`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The commutative ring structure on `𝕎 R`.
-/
instance : CommRing (𝕎 R) :=
  (mapFun.surjective _ <| counit_surjective _).commRing (mapFun <| MvPolynomial.counit _)
    (mapFun.zero _) (mapFun.one _) (mapFun.add _) (mapFun.mul _) (mapFun.neg _) (mapFun.sub _)
    (mapFun.nsmul _) (mapFun.zsmul _) (mapFun.pow _) (mapFun.natCast _) (mapFun.intCast _)

variable {p R}

/-- `WittVector.map f` is the ring homomorphism `𝕎 R →+* 𝕎 S` naturally induced
by a ring homomorphism `f : R →+* S`. It acts coefficientwise. -/
/-
**WittVector.map** 是 Mathlib 中的一个定义，位于命名空间 `WittVector`。
形式化陈述：map (f : R ->+* S) : 𝕎 R ->+* 𝕎 S where toFun
参数：f : R ->+* S。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `WittVector.mapFun.one`：one : mapFun f (1 : 𝕎 R) = 1
· 使用定理 `WittVector.mapFun.mul`：mul : mapFun f (x * y) = mapFun f x * mapFun f y
· 使用定理 `WittVector.mapFun.zero`：zero : mapFun f (0 : 𝕎 R) = 0
· 使用定理 `WittVector.mapFun.add`：add : mapFun f (x + y) = mapFun f x + mapFun f y

--- 原说明 ---
`WittVector.map f` is the ring homomorphism `𝕎 R →+* 𝕎 S` naturally induced
by a ring homomorphism `f : R →+* S`. It acts coefficientwise.
-/
noncomputable def map (f : R →+* S) : 𝕎 R →+* 𝕎 S where
  toFun := mapFun f
  map_zero' := mapFun.zero f
  map_one' := mapFun.one f
  map_add' := mapFun.add f
  map_mul' := mapFun.mul f
/-
**WittVector.map_injective** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：map_injective (f : R ->+* S) (hf : Injective f) : Injective (map f : 𝕎 R -
> 𝕎 S)
参数：f : R ->+* S；hf : Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WittVector.mapFun.injective`：injective (f : α -> β) (hf : Injective f) :
 Injective (mapFun f : 𝕎 α -> 𝕎 β)
-/
theorem map_injective (f : R →+* S) (hf : Injective f) : Injective (map f : 𝕎 R → 𝕎 S) :=
  mapFun.injective f hf
/-
**WittVector.map_surjective** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：map_surjective (f : R ->+* S) (hf : Surjective f) : Surjective (map f : 𝕎 
R -> 𝕎 S)
参数：f : R ->+* S；hf : Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WittVector.mapFun.surjective`：surjective (f : α -> β) (hf : Surjective f
) : Surjective (mapFun f : 𝕎 α -> 𝕎 β)
-/
theorem map_surjective (f : R →+* S) (hf : Surjective f) : Surjective (map f : 𝕎 R → 𝕎 S) :=
  mapFun.surjective f hf

@[simp]
/-
**WittVector.map_coeff** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：map_coeff (f : R ->+* S) (x : 𝕎 R) (n : Nat) : (map f x).coeff n = f (x.co
eff n)
参数：f : R ->+* S；x : 𝕎 R；n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_coeff (f : R →+* S) (x : 𝕎 R) (n : ℕ) : (map f x).coeff n = f (x.coeff n) :=
  rfl

variable (R) in
@[simp]
/-
**WittVector.map_id** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：map_id : WittVector.map (RingHom.id R) = RingHom.id (𝕎 R)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `WittVector.ext`：ext {x y : 𝕎 R} (h : forall n, x.coeff n = y.coeff n) : 
x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_id : WittVector.map (RingHom.id R) = RingHom.id (𝕎 R) := by
  ext; simp
/-
**WittVector.map_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：map_eq_zero_iff (f : R ->+* S) {x : WittVector p R} : ((map f) x) = 0 ↔ fo
rall n, f (x.coeff n) = 0
参数：f : R ->+* S。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WittVector.zero_coeff`：zero_coeff (n : Nat) : (0 : 𝕎 R).coeff n = 0
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WittVector.ext`：ext {x y : 𝕎 R} (h : forall n, x.coeff n = y.coeff n) : 
x = y
-/
theorem map_eq_zero_iff (f : R →+* S) {x : WittVector p R} :
    ((map f) x) = 0 ↔ ∀ n, f (x.coeff n) = 0 := by
  refine ⟨fun h n ↦ ?_, fun h ↦ ?_⟩
  · apply_fun (·.coeff n) at h
    simpa using h
  · ext n
    simpa using h n

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- `WittVector.ghostMap` is a ring homomorphism that maps each Witt vector
to the sequence of its ghost components. -/
/-
**WittVector.ghostMap** 是 Mathlib 中的一个定义，位于命名空间 `WittVector`。
形式化陈述：ghostMap : 𝕎 R ->+* Nat -> R where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.RingTheory.WittVector.Basic.0.WittVector.ghostFun_one`：
∀ {p : ℕ} {R : Type u_1} [inst : CommRing R] [inst_1 : Fact (Nat.Prime p)], Witt
Vector.ghostFun✝ 1 = 1
· 使用定理 `_private.Mathlib.RingTheory.WittVector.Basic.0.WittVector.ghostFun_mul`：
∀ {p : ℕ} {R : Type u_1} [inst : CommRing R] [inst_1 : Fact (Nat.Prime p)] (x y 
: WittVector p R),   WittVector.ghostFun✝ (x * y) = WittVect…
· 使用定理 `_private.Mathlib.RingTheory.WittVector.Basic.0.WittVector.ghostFun_zero`
：∀ {p : ℕ} {R : Type u_1} [inst : CommRing R] [inst_1 : Fact (Nat.Prime p)], Wit
tVector.ghostFun✝ 0 = 0
· 使用定理 `_private.Mathlib.RingTheory.WittVector.Basic.0.WittVector.ghostFun_add`：
∀ {p : ℕ} {R : Type u_1} [inst : CommRing R] [inst_1 : Fact (Nat.Prime p)] (x y 
: WittVector p R),   WittVector.ghostFun✝ (x + y) = WittVect…

--- 原说明 ---
`WittVector.ghostMap` is a ring homomorphism that maps each Witt vector
to the sequence of its ghost components.
-/
def ghostMap : 𝕎 R →+* ℕ → R where
  toFun := ghostFun
  map_zero' := ghostFun_zero
  map_one' := ghostFun_one
  map_add' := ghostFun_add
  map_mul' := ghostFun_mul

/-- Evaluates the `n`th Witt polynomial on the first `n` coefficients of `x`,
producing a value in `R`. -/
/-
**WittVector.ghostComponent** 是 Mathlib 中的一个定义，位于命名空间 `WittVector`。
形式化陈述：ghostComponent (n : Nat) : 𝕎 R ->+* R
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Evaluates the `n`th Witt polynomial on the first `n` coefficients of `x`,
producing a value in `R`.
-/
def ghostComponent (n : ℕ) : 𝕎 R →+* R :=
  (Pi.evalRingHom _ n).comp ghostMap
/-
**WittVector.ghostComponent_apply** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：ghostComponent_apply (n : Nat) (x : 𝕎 R) : ghostComponent n x = aeval x.co
eff (W_ Int n)
参数：n : Nat；x : 𝕎 R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ghostComponent_apply (n : ℕ) (x : 𝕎 R) : ghostComponent n x = aeval x.coeff (W_ ℤ n) :=
  rfl
/-
**WittVector.pow_dvd_ghostComponent_of_dvd_coeff** 是 Mathlib 中的一个定理，位于命名空间 `Witt
Vector`。
形式化陈述：pow_dvd_ghostComponent_of_dvd_coeff {x : 𝕎 R} {n : Nat} (hx : forall i <= 
n, (p : R) ∣ x.coeff i) : (p : R) ^ (n + 1) ∣ ghostComponent n x
参数：hx : forall i <= n, (p : R) ∣ x.coeff i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WittVector.ghostComponent_apply`：ghostComponent_apply (n : Nat) (x : 𝕎 R
) : ghostComponent n x = aeval x.coeff (W_ Int n)
· 使用定理 `wittPolynomial.eq_1`：∀ (p : ℕ) (R : Type u_1) [inst : CommRing R] (n : ℕ
),   wittPolynomial p R n = ∑ i ∈ Finset.range (n + 1), (MvPolynomial.monomial f
un₀ | i =…
· 使用定理 `MvPolynomial.aeval_sum`：aeval_sum {ι : Type*} (s : Finset ι) (φ : ι -> M
vPolynomial σ R) : aeval f (∑ i in s, φ i) = ∑ i in s, aeval f (φ i)
· 使用引理 `Finset.dvd_sum`：dvd_sum (h : forall i in s, a ∣ f i) : a ∣ ∑ i in s, f i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MvPolynomial.aeval_monomial`：aeval_monomial (g : σ -> S₁) (d : σ ->₀ Nat
) (r : R) : aeval g (monomial d r) = algebraMap _ _ r * d.prod fun i k => g i ^ 
k
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `map_natCast`：map_natCast [FunLike F R S] [RingHomClass F R S] (f : F) : 
forall n : Nat, f (n : R) = n
· 使用定理 `Finsupp.prod_single_index`：prod_single_index {a : α} {b : M} {h : α -> M
 -> N} (h_zero : h a 0 = 1) : (single a b).prod h = h a b
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_dvd_mul_left`：mul_dvd_mul_left (a : α) (h : b ∣ c) : a * b ∣ a * c
· 使用引理 `pow_dvd_pow_of_dvd_of_le`：pow_dvd_pow_of_dvd_of_le {m n : Nat} (hab : a 
∣ b) (hmn : m <= n) : a ^ m ∣ b ^ n
· 使用定理 `Nat.le_of_lt_succ`：∀ {m n : ℕ}, m < n.succ → m ≤ n
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LT.lt.succ_le`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : SuccOrder 
α] {a b : α}, a < b → Order.succ a ≤ b
· 使用定理 `Nat.lt_two_pow_self`：∀ {n : ℕ}, n < 2 ^ n
· 使用定理 `pow_left_mono`：pow_left_mono (n : Nat) : Monotone fun a : M => a ^ n
· 使用定理 `Nat.Prime.two_le`：∀ {p : ℕ}, Nat.Prime p → 2 ≤ p
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
-/
theorem pow_dvd_ghostComponent_of_dvd_coeff {x : 𝕎 R} {n : ℕ}
    (hx : ∀ i ≤ n, (p : R) ∣ x.coeff i) : (p : R) ^ (n + 1) ∣ ghostComponent n x := by
  rw [WittVector.ghostComponent_apply, wittPolynomial, MvPolynomial.aeval_sum]
  apply Finset.dvd_sum
  intro i hi
  simp only [Finset.mem_range] at hi
  have : (MvPolynomial.aeval x.coeff) ((MvPolynomial.monomial (R := ℤ)
      (Finsupp.single i (p ^ (n - i)))) (p ^ i)) = ((p : R) ^ i) * (x.coeff i) ^ (p ^ (n - i)) := by
    simp [MvPolynomial.aeval_monomial, map_pow]
  rw [this, show n + 1 = (n - i) + 1 + i by lia, pow_add, mul_comm]
  gcongr
  · exact hx i (Nat.le_of_lt_succ hi)
  · exact ((n - i).lt_two_pow_self).succ_le.trans
        (pow_left_mono (n - i) (Nat.Prime.two_le Fact.out))

@[simp]
/-
**WittVector.ghostMap_apply** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：ghostMap_apply (x : 𝕎 R) (n : Nat) : ghostMap x n = ghostComponent n x
参数：x : 𝕎 R；n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ghostMap_apply (x : 𝕎 R) (n : ℕ) : ghostMap x n = ghostComponent n x :=
  rfl

section Invertible

variable (p R)
variable [Invertible (p : R)]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- `WittVector.ghostMap` is a ring isomorphism when `p` is invertible in `R`. -/
/-
**WittVector.ghostEquiv** 是 Mathlib 中的一个定义，位于命名空间 `WittVector`。
形式化陈述：ghostEquiv : 𝕎 R ≃+* (Nat -> R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`WittVector.ghostMap` is a ring isomorphism when `p` is invertible in `R`.
-/
def ghostEquiv : 𝕎 R ≃+* (ℕ → R) :=
  { (ghostMap : 𝕎 R →+* ℕ → R), ghostEquiv' p R with }

@[simp]
/-
**WittVector.ghostEquiv_coe** 是 Mathlib 中的一个定理，位于命名空间 `WittVector`。
形式化陈述：ghostEquiv_coe : (ghostEquiv p R : 𝕎 R ->+* Nat -> R) = ghostMap
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
-/
theorem ghostEquiv_coe : (ghostEquiv p R : 𝕎 R →+* ℕ → R) = ghostMap :=
  rfl
/-
**WittVector.ghostMap.bijective_of_invertible** 是 Mathlib 中的一个定理，位于命名空间 `WittVec
tor.ghostMap`。
形式化陈述：∀ (p : ℕ) (R : Type u_1) [inst : CommRing R] [inst_1 : Fact (Nat.Prime p)]
 [Invertible ↑p],   Function.Bijective ⇑WittVector.ghostMap
参数：p : ℕ；R : Type u_1；Nat.Prime p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquiv.bijective`：∀ {R : Type u_4} {S : Type u_5} [inst : Mul R] [ins
t_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S] (e : R ≃+* S),   Function.Bijecti
ve ⇑e
-/
theorem ghostMap.bijective_of_invertible : Function.Bijective (ghostMap : 𝕎 R → ℕ → R) :=
  (ghostEquiv p R).bijective

end Invertible

/-- `WittVector.coeff x 0` as a `RingHom` -/
@[simps]
/-
**WittVector.constantCoeff** 是 Mathlib 中的一个定义，位于命名空间 `WittVector`。
形式化陈述：constantCoeff : 𝕎 R ->+* R where toFun x
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `WittVector.mul_coeff_zero`：mul_coeff_zero (x y : 𝕎 R) : (x * y).coeff 0 
= x.coeff 0 * y.coeff 0
· 使用定理 `WittVector.add_coeff_zero`：add_coeff_zero (x y : 𝕎 R) : (x + y).coeff 0 
= x.coeff 0 + y.coeff 0

--- 原说明 ---
`WittVector.coeff x 0` as a `RingHom`
-/
noncomputable def constantCoeff : 𝕎 R →+* R where
  toFun x := x.coeff 0
  map_zero' := by simp
  map_one' := by simp
  map_add' := add_coeff_zero
  map_mul' := mul_coeff_zero
/-
**WittVector.** 是 Mathlib 中的一个实例，位于命名空间 `WittVector`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Nontrivial R] : Nontrivial (𝕎 R) :=
  constantCoeff.domain_nontrivial

end WittVector

