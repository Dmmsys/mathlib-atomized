/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.LinearAlgebra.Finsupp.LSum
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Algebra.Order.Group.Nat

/-!
# Properties of the module `α →₀ M`

* `Finsupp.linearEquivFunOnFinite`: `α →₀ β` and `a → β` are equivalent if `α` is finite
* `FunOnFinite.map`: the map `(X → M) → (Y → M)` induced by a map `f : X ⟶ Y` when
  `X` and `Y` are finite.
* `FunOnFinite.linearMmap`: the linear map `(X → M) →ₗ[R] (Y → M)` induced
  by a map `f : X ⟶ Y` when `X` and `Y` are finite.

## Tags

function with finite support, module, linear algebra
-/

@[expose] public section

noncomputable section

open Set LinearMap Submodule

namespace Finsupp

section uniqueLinearEquiv

variable (R : Type*) {S α : Type*} (M : Type*)
variable [AddCommMonoid M] [Semiring R] [Module R M]

/-- If `α` has a unique term, then the type of finitely supported functions `α →₀ M` is
`R`-linearly equivalent to `M`. -/
@[simps! apply symm_apply]
/-
**Finsupp.uniqueLinearEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp`。
形式化陈述：uniqueLinearEquiv [Subsingleton α] (a : α) : (α ->₀ M) ≃ₗ[R] M where toAdd
Equiv
参数：a : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `α` has a unique term, then the type of finitely supported functions `α →₀ M`
 is
`R`-linearly equivalent to `M`.
-/
noncomputable def uniqueLinearEquiv [Subsingleton α] (a : α) : (α →₀ M) ≃ₗ[R] M where
  toAddEquiv := uniqueAddEquiv a
  map_smul' _ _ := rfl

-- We want this lemma to fire before `uniqueRingEquiv_symm_apply`.
/-
**Finsupp.uniqueLinearEquiv_symm_apply_apply** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`
。
形式化陈述：∀ (R : Type u_1) {α : Type u_3} (M : Type u_4) [inst : AddCommMonoid M] [i
nst_1 : Semiring R]   [inst_2 : _root_.Module R M] (a : α) [inst_3 : Subsingleto
n α] (m : M) (b : α),   ((Finsupp.uniqueLinearEquiv R M a).symm m) b = m
参数：R : Type u_1；M : Type u_4；a : α；m : M；b : α；(Finsupp.uniqueLinearEquiv R M a)
.symm m。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finsupp.uniqueLinearEquiv_symm_apply`：∀ (R : Type u_1) {α : Type u_3} (M
 : Type u_4) [inst : AddCommMonoid M] [inst_1 : Semiring R]   [inst_2 : _root_.M
odule R M] [inst_3 : Subsi…
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp↓ high] lemma uniqueLinearEquiv_symm_apply_apply (a : α) [Subsingleton α] (m : M) (b : α) :
    (uniqueLinearEquiv R M a).symm m b = m := by simp [Subsingleton.elim b a]

/-- If `α` has a unique term, then the type of finitely supported functions `α →₀ M` is
`R`-linearly equivalent to `M`. -/
@[deprecated uniqueLinearEquiv (since := "2026-05-06")]
/-
**Finsupp.LinearEquiv.finsuppUnique** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp.LinearEqu
iv`。
形式化陈述：(R : Type u_1) →   (M : Type u_4) →     [inst : AddCommMonoid M] →       [
inst_1 : Semiring R] → [inst_2 : _root_.Module R M] → (α : Type u_5) → [Unique α
] → (α →₀ M) ≃ₗ[R] M
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
If `α` has a unique term, then the type of finitely supported functions `α →₀ M`
 is
`R`-linearly equivalent to `M`.
-/
noncomputable def LinearEquiv.finsuppUnique (α : Type*) [Unique α] : (α →₀ M) ≃ₗ[R] M :=
  { Finsupp.equivFunOnFinite.trans (Equiv.funUnique α M) with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

variable {R M}

@[deprecated uniqueLinearEquiv_apply (since := "2026-05-06")]
/-
**Finsupp.LinearEquiv.finsuppUnique_apply** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp.Lin
earEquiv`。
形式化陈述：∀ {R : Type u_1} {M : Type u_4} [inst : AddCommMonoid M] [inst_1 : Semirin
g R] [inst_2 : _root_.Module R M]   (α : Type u_5) [inst_3 : Unique α] (f : α →₀
 M), (Finsupp.LinearEquiv.finsuppUnique R M α) f = f default
参数：α : Type u_5；f : α →₀ M；Finsupp.LinearEquiv.finsuppUnique R M α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem LinearEquiv.finsuppUnique_apply (α : Type*) [Unique α] (f : α →₀ M) :
    LinearEquiv.finsuppUnique R M α f = f default :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
@[deprecated uniqueLinearEquiv_symm_apply (since := "2026-05-06")]
/-
**Finsupp.LinearEquiv.finsuppUnique_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Finsup
p.LinearEquiv`。
形式化陈述：∀ {R : Type u_1} {M : Type u_4} [inst : AddCommMonoid M] [inst_1 : Semirin
g R] [inst_2 : _root_.Module R M]   (α : Type u_5) [inst_3 : Unique α] (m : M), 
(Finsupp.LinearEquiv.finsuppUnique R M α).symm m = fun₀ | default => m
参数：α : Type u_5；m : M；Finsupp.LinearEquiv.finsuppUnique R M α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.unique_ext`：unique_ext [Unique α] {f g : α ->₀ M} (h : f default
 = g default) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AddHom.map_add'`：∀ {M : Type u_10} {N : Type u_11} [inst : Add M] [inst_
1 : Add N] (self : M →ₙ+ N) (x y : M),   self.toFun (x + y) = self.toFun x + sel
f.toF…
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.piUnique_apply`：∀ {α : Sort u} [inst : Unique α] (β : α → Sort u_1
), ⇑(Equiv.piUnique β) = fun f => f default
· 使用定理 `AddHom.mk.congr_simp`：∀ {M : Type u_10} {N : Type u_11} [inst : Add M] [
inst_1 : Add N] (toFun toFun_1 : M → N) (e_toFun : toFun = toFun_1)   (map_add' 
: ∀ (x y :…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.piUnique_symm_apply`：∀ {α : Sort u} [inst : Unique α] (β : α → Sor
t u_1), ⇑(Equiv.piUnique β).symm = uniqueElim
· 使用定理 `LinearMap.mk.congr_simp`：∀ {R : Type u_14} {S : Type u_15} [inst : Semir
ing R] [inst_1 : Semiring S] {σ : R →+* S} {M : Type u_16}   {M₂ : Type u_17} [i
nst_2 : AddCo…
· 使用定理 `LinearMap.map_smul'`：∀ {R : Type u_14} {S : Type u_15} [inst : Semiring 
R] [inst_1 : Semiring S] {σ : R →+* S} {M : Type u_16}   {M₂ : Type u_17} [inst_
2 : AddCo…
· 使用定理 `LinearEquiv.left_inv`：∀ {R : Type u_14} {S : Type u_15} [inst : Semiring
 R] [inst_1 : Semiring S] {σ : R →+* S} {σ' : S →+* R}   [inst_2 : RingHomInvPai
r σ σ'] [i…
· 使用定理 `LinearEquiv.right_inv`：∀ {R : Type u_14} {S : Type u_15} [inst : Semirin
g R] [inst_1 : Semiring S] {σ : R →+* S} {σ' : S →+* R}   [inst_2 : RingHomInvPa
ir σ σ'] [i…
· 使用定理 `LinearEquiv.mk.congr_simp`：∀ {R : Type u_14} {S : Type u_15} [inst : Sem
iring R] [inst_1 : Semiring S] {σ : R →+* S} {σ' : S →+* R}   [inst_2 : RingHomI
nvPair σ σ'] [i…
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem LinearEquiv.finsuppUnique_symm_apply (α : Type*) [Unique α] (m : M) :
    (LinearEquiv.finsuppUnique R M α).symm m = Finsupp.single default m := by
  ext; simp [LinearEquiv.finsuppUnique, Equiv.funUnique, single, Pi.single,
    equivFunOnFinite, Function.update]

end uniqueLinearEquiv

variable {α : Type*} {M : Type*} {N : Type*} {P : Type*} {R : Type*} {S : Type*}
variable [Semiring R] [Semiring S] [AddCommMonoid M] [Module R M]
variable [AddCommMonoid N] [Module R N]
variable [AddCommMonoid P] [Module R P]

/-- Forget that a function is finitely supported.

This is the linear version of `Finsupp.toFun`. -/
/-
**Finsupp.lcoeFun** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp`。
形式化陈述：lcoeFun : (α ->₀ M) ->ₗ[R] α -> M where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Forget that a function is finitely supported.

This is the linear version of `Finsupp.toFun`.
-/
def lcoeFun : (α →₀ M) →ₗ[R] α → M where
  toFun := (⇑)
  map_add' x y := by
    ext
    simp
  map_smul' x y := by
    ext
    simp
/-
**Finsupp.lcoeFun_apply** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：∀ {α : Type u_1} {M : Type u_2} {R : Type u_5} [inst : Semiring R] [inst_1
 : AddCommMonoid M]   [inst_2 : _root_.Module R M] (f : α →₀ M), Finsupp.lcoeFun
 f = ⇑f
参数：f : α →₀ M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem lcoeFun_apply (f : α →₀ M) : lcoeFun (R := R) f = ⇑f := rfl
/-
**Finsupp.lcoeFun_comp_lsingle** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：∀ {α : Type u_1} {M : Type u_2} {R : Type u_5} [inst : Semiring R] [inst_1
 : AddCommMonoid M]   [inst_2 : _root_.Module R M] [inst_3 : DecidableEq α] (x :
 α),   Finsupp.lcoeFun ∘ₗ Finsupp.lsingle x = LinearMap.single R (fun x => M) x
参数：x : α；fun x => M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Finsupp.single_eq_pi_single`：single_eq_pi_single [DecidableEq α] (a : α)
 (b : M) : ⇑(single a b) = Pi.single a b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem lcoeFun_comp_lsingle [DecidableEq α] (x : α) :
    lcoeFun ∘ₗ lsingle x = .single R (fun _ ↦ M) x := by
  ext; simp [single_eq_pi_single]

end Finsupp

variable {R M N P : Type*}
variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
variable [AddCommMonoid P] [Module R P]

open Finsupp

namespace LinearMap

section prodOfFinsuppNat

open Function

variable (f : P × M →ₗ[R] M)

/-- A linear map from a product module `P × M` to `M` induces a linear map from `P^(ℕ)` to `M`,
where the `n`th component is given by `P —ι₁→ P × M` composed with `P × M —f→ M —ι₂→ P × M`
`n` times. -/
/-
**LinearMap.prodOfFinsuppNat** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：prodOfFinsuppNat : (Nat ->₀ P) ->ₗ[R] P × M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A linear map from a product module `P × M` to `M` induces a linear map from `P^(
ℕ)` to `M`,
where the `n`th component is given by `P —ι₁→ P × M` composed with `P × M —f→ M 
—ι₂→ P × M`
`n` times.
-/
def prodOfFinsuppNat : (ℕ →₀ P) →ₗ[R] P × M :=
  Finsupp.lsum ℕ fun n ↦ ((.inr .. ∘ₗ f) ^ n) ∘ₗ .inl ..
/-
**LinearMap.fst_prodOfFinsuppNat** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：fst_prodOfFinsuppNat (x : Nat ->₀ P) : (prodOfFinsuppNat f x).1 = x 0
参数：x : Nat ->₀ P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Prod.fst_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : Add
CommMonoid M] [inst_1 : AddCommMonoid N] {s : Finset ι}   {f : ι → M × N}, (∑ c 
∈ …
· 使用定理 `Finset.sum_eq_single`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] {s : Finset ι} {f : ι → M} (a : ι),   (∀ b ∈ s, b ≠ a → f b = 0) → (a ∉ s
 → f a = 0…
· 使用定理 `Nat.exists_eq_succ_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → ∃ k, n = k.succ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
-/
theorem fst_prodOfFinsuppNat (x : ℕ →₀ P) : (prodOfFinsuppNat f x).1 = x 0 := by
  simp_rw [prodOfFinsuppNat, coe_lsum, sum, Prod.fst_sum]
  rw [Finset.sum_eq_single 0 (fun n _ hn ↦ ?_) (by simp)]
  · simp
  obtain ⟨n, rfl⟩ := n.exists_eq_succ_of_ne_zero hn
  simp [pow_succ']
/-
**LinearMap.snd_prodOfFinsuppNat** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：snd_prodOfFinsuppNat (x : Nat ->₀ P) : (prodOfFinsuppNat f x).2 = f (prodO
fFinsuppNat f <| comapDomain.addMonoidHom (add_left_injective 1) x)
参数：x : Nat ->₀ P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `add_left_injective`：∀ {G : Type u_1} [inst : Add G] [IsRightCancelAdd G]
 (a : G), Function.Injective fun x => x + a
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
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Prod.snd_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : Add
CommMonoid M] [inst_1 : AddCommMonoid N] {s : Finset ι}   {f : ι → M × N}, (∑ c 
∈ …
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_preimage`：∀ {ι : Type u_1} {κ : Type u_2} {β : Type u_3} [ins
t : AddCommMonoid β] (f : ι → κ) (s : Finset κ)   (hf : Set.InjOn f (f ⁻¹' ↑s)) 
(g : κ → …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `Finsupp.comapDomain.addMonoidHom_apply`：∀ {α : Type u_1} {β : Type u_2} 
{M : Type u_5} [inst : AddZeroClass M] {f : α → β} (hf : Function.Injective f)  
 (x : β →₀ M), (Finsupp.coma…
· 使用定理 `Finsupp.comapDomain_support`：∀ {α : Type u_1} {β : Type u_2} {M : Type u
_5} [inst : Zero M] (f : α → β) (l : β →₀ M)   (hf : Set.InjOn f (f ⁻¹' ↑l.suppo
rt)), (Finsupp.co…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
-/
theorem snd_prodOfFinsuppNat (x : ℕ →₀ P) :
    (prodOfFinsuppNat f x).2 =
    f (prodOfFinsuppNat f <| comapDomain.addMonoidHom (add_left_injective 1) x) := by
  simp_rw [prodOfFinsuppNat, coe_lsum, sum, Prod.snd_sum]
  rw [← Finset.sum_preimage (· + 1) _ (add_left_injective 1).injOn _ (by simp_all)]
  simp [pow_succ']

variable {f}
/-
**LinearMap.prodOfFinsuppNat_injective** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：prodOfFinsuppNat_injective (inj : Injective f) : Injective (prodOfFinsuppN
at f)
参数：inj : Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Finset α) : s = ∅
 ∨ s.Nonempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Finset.max'`：max'_one [LinearOrder α] : (1 : Finset α).max' one_nonempty
 = 1
· 使用定理 `Nat.strong_induction_on`：∀ {p : ℕ → Prop} (n : ℕ), (∀ (n : ℕ), (∀ m < n,
 p m) → p n) → p n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Finsupp.single_add_erase`：single_add_erase (a : ι) (f : ι ->₀ M) : singl
e a (f a) + f.erase a = f
· 使用定理 `add_left_injective`：∀ {G : Type u_1} [inst : Add G] [IsRightCancelAdd G]
 (a : G), Function.Injective fun x => x + a
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.fst_prodOfFinsuppNat`：fst_prodOfFinsuppNat (x : Nat ->₀ P) : (
prodOfFinsuppNat f x).1 = x 0
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Finsupp.comapDomain.addMonoidHom_apply`：∀ {α : Type u_1} {β : Type u_2} 
{M : Type u_5} [inst : AddZeroClass M] {f : α → β} (hf : Function.Injective f)  
 (x : β →₀ M), (Finsupp.coma…
· 使用定理 `Finsupp.comapDomain_support`：∀ {α : Type u_1} {β : Type u_2} {M : Type u
_5} [inst : Zero M] (f : α → β) (l : β →₀ M)   (hf : Set.InjOn f (f ⁻¹' ↑l.suppo
rt)), (Finsupp.co…
· 使用定理 `Finset.max'.congr_simp`：∀ {α : Type u_2} [inst : LinearOrder α] (s s_1 :
 Finset α) (e_s : s = s_1) (H : s.Nonempty), s.max' H = s_1.max' ⋯
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem prodOfFinsuppNat_injective (inj : Injective f) : Injective (prodOfFinsuppNat f) := by
  intro x y
  let s := x.support ∪ y.support
  obtain eq | ne := s.eq_empty_or_nonempty
  · simp_all [s]
  set n := s.max' ne with hn
  clear_value n; revert x y
  induction n using Nat.strong_induction_on with | h n ih =>
  intro x y s _ hn eq
  rw [← x.single_add_erase 0, ← y.single_add_erase 0]
  simp_rw [← mapDomain_comapDomain_nat_add_one, ← f.fst_prodOfFinsuppNat, eq]
  congr 2
  by_contra ne
  apply ne (ih _ _ _ rfl (inj _))
  · contrapose! ne; simp_all [-comapDomain_support]
  · simp +contextual [hn, s, ← Nat.succ_le_iff, Finset.le_max']
  simp_rw [← snd_prodOfFinsuppNat, eq]
/-
**LinearMap.exists_finsupp_nat_of_prod_injective** 是 Mathlib 中的一个定理，位于命名空间 `Line
arMap`。
形式化陈述：exists_finsupp_nat_of_prod_injective (inj : Injective f) : exists g : (Nat
 ->₀ P) ->ₗ[R] M, Injective g
参数：inj : Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `LinearMap.prodOfFinsuppNat_injective`：prodOfFinsuppNat_injective (inj : 
Injective f) : Injective (prodOfFinsuppNat f)
-/
theorem exists_finsupp_nat_of_prod_injective (inj : Injective f) :
    ∃ g : (ℕ →₀ P) →ₗ[R] M, Injective g :=
  ⟨f ∘ₗ prodOfFinsuppNat f, inj.comp (prodOfFinsuppNat_injective inj)⟩
/-
**LinearMap.exists_finsupp_nat_of_fin_fun_injective** 是 Mathlib 中的一个定理，位于命名空间 `L
inearMap`。
形式化陈述：exists_finsupp_nat_of_fin_fun_injective {n : Nat} {f : (Fin (n + 1) -> P) 
->ₗ[R] Fin n -> P} (inj : Injective f) : exists g : (Nat ->₀ P) ->ₗ[R] Fin n -> 
P, Injective g
参数：Fin (n + 1) -> P；inj : Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.exists_finsupp_nat_of_prod_injective`：exists_finsupp_nat_of_pr
od_injective (inj : Injective f) : exists g : (Nat ->₀ P) ->ₗ[R] M, Injective g
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
-/
theorem exists_finsupp_nat_of_fin_fun_injective {n : ℕ}
    {f : (Fin (n + 1) → P) →ₗ[R] Fin n → P} (inj : Injective f) :
    ∃ g : (ℕ →₀ P) →ₗ[R] Fin n → P, Injective g :=
  have e := LinearEquiv.piCongrLeft R (fun _ ↦ P) (finSuccEquiv n) ≪≫ₗ .piOptionEquivProd _
  exists_finsupp_nat_of_prod_injective (f := f ∘ₗ e.symm.toLinearMap) <| inj.comp e.symm.injective

end prodOfFinsuppNat

variable {α : Type*}

open Finsupp Function

-- See also `LinearMap.splittingOfFinsuppSurjective`
/-- A surjective linear map to functions on a finite type has a splitting. -/
/-
**LinearMap.splittingOfFunOnFintypeSurjective** 是 Mathlib 中的一个定义，位于命名空间 `LinearM
ap`。
形式化陈述：splittingOfFunOnFintypeSurjective [Finite α] (f : M ->ₗ[R] α -> R) (s : Su
rjective f) : (α -> R) ->ₗ[R] M
参数：f : M ->ₗ[R] α -> R；s : Surjective f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A surjective linear map to functions on a finite type has a splitting.
-/
def splittingOfFunOnFintypeSurjective [Finite α] (f : M →ₗ[R] α → R) (s : Surjective f) :
    (α → R) →ₗ[R] M :=
  (Finsupp.lift _ _ _ fun x : α => (s (Finsupp.single x 1)).choose).comp
    (linearEquivFunOnFinite R R α).symm.toLinearMap
/-
**LinearMap.splittingOfFunOnFintypeSurjective_splits** 是 Mathlib 中的一个定理，位于命名空间 `
LinearMap`。
形式化陈述：splittingOfFunOnFintypeSurjective_splits [Finite α] (f : M ->ₗ[R] α -> R) 
(s : Surjective f) : f.comp (splittingOfFunOnFintypeSurjective f s) = LinearMap.
id
参数：f : M ->ₗ[R] α -> R；s : Surjective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.pi_ext'`：pi_ext' (h : forall i, f.comp (single R φ i) = g.comp
 (single R φ i)) : f = g
· 使用定理 `LinearMap.ext_ring`：ext_ring {f g : R ->ₛₗ[σ] M₃} (h : f 1 = g 1) : f = 
g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.linearEquivFunOnFinite_symm_single`：linearEquivFunOnFinite_symm_
single [DecidableEq α] (x : α) (m : M) : (linearEquivFunOnFinite R M α).symm (Pi
.single x m) = single x m
· 使用定理 `Finsupp.sum_single_index`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10
} [inst : Zero M] [inst_1 : AddCommMonoid N] {a : α} {b : M}   {h : α → M → N}, 
h a 0 = 0 → (f…
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `Finsupp.single_eq_pi_single`：single_eq_pi_single [DecidableEq α] (a : α)
 (b : M) : ⇑(single a b) = Pi.single a b
-/
theorem splittingOfFunOnFintypeSurjective_splits [Finite α] (f : M →ₗ[R] α → R)
    (s : Surjective f) : f.comp (splittingOfFunOnFintypeSurjective f s) = LinearMap.id := by
  classical
  ext x y
  dsimp [splittingOfFunOnFintypeSurjective]
  rw [linearEquivFunOnFinite_symm_single, Finsupp.sum_single_index, one_smul,
    (s (Finsupp.single x 1)).choose_spec, Finsupp.single_eq_pi_single]
  rw [zero_smul]
/-
**LinearMap.leftInverse_splittingOfFunOnFintypeSurjective** 是 Mathlib 中的一个定理，位于命
名空间 `LinearMap`。
形式化陈述：leftInverse_splittingOfFunOnFintypeSurjective [Finite α] (f : M ->ₗ[R] α -
> R) (s : Surjective f) : LeftInverse f (splittingOfFunOnFintypeSurjective f s)
参数：f : M ->ₗ[R] α -> R；s : Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.congr_fun`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ 
: Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid
 M] [inst…
· 使用定理 `LinearMap.splittingOfFunOnFintypeSurjective_splits`：splittingOfFunOnFint
ypeSurjective_splits [Finite α] (f : M ->ₗ[R] α -> R) (s : Surjective f) : f.com
p (splittingOfFunOnFintypeSurjective f s…
-/
theorem leftInverse_splittingOfFunOnFintypeSurjective [Finite α] (f : M →ₗ[R] α → R)
    (s : Surjective f) : LeftInverse f (splittingOfFunOnFintypeSurjective f s) := fun g =>
  LinearMap.congr_fun (splittingOfFunOnFintypeSurjective_splits f s) g
/-
**LinearMap.splittingOfFunOnFintypeSurjective_injective** 是 Mathlib 中的一个定理，位于命名空
间 `LinearMap`。
形式化陈述：splittingOfFunOnFintypeSurjective_injective [Finite α] (f : M ->ₗ[R] α -> 
R) (s : Surjective f) : Injective (splittingOfFunOnFintypeSurjective f s)
参数：f : M ->ₗ[R] α -> R；s : Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.LeftInverse.injective`：∀ {α : Sort u_1} {β : Sort u_2} {g : β →
 α} {f : α → β}, Function.LeftInverse g f → Function.Injective f
· 使用定理 `LinearMap.leftInverse_splittingOfFunOnFintypeSurjective`：leftInverse_spl
ittingOfFunOnFintypeSurjective [Finite α] (f : M ->ₗ[R] α -> R) (s : Surjective 
f) : LeftInverse f (splittingOfFunOnFintypeSu…
-/
theorem splittingOfFunOnFintypeSurjective_injective [Finite α] (f : M →ₗ[R] α → R)
    (s : Surjective f) : Injective (splittingOfFunOnFintypeSurjective f s) :=
  (leftInverse_splittingOfFunOnFintypeSurjective f s).injective

end LinearMap

namespace Finsupp

variable {α : Type*}

/-- Given a family `Sᵢ` of `R`-submodules of `M` indexed by a type `α`, this is the `R`-submodule
of `α →₀ M` of functions `f` such that `f i ∈ Sᵢ` for all `i : α`. -/
/-
**Finsupp.submodule** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp`。
形式化陈述：submodule (S : α -> Submodule R M) : Submodule R (α ->₀ M) where carrier
参数：S : α -> Submodule R M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a family `Sᵢ` of `R`-submodules of `M` indexed by a type `α`, this is the 
`R`-submodule
of `α →₀ M` of functions `f` such that `f i ∈ Sᵢ` for all `i : α`.
-/
def submodule (S : α → Submodule R M) : Submodule R (α →₀ M) where
  carrier := { x | ∀ i, x i ∈ S i }
  add_mem' hx hy i := (S i).add_mem (hx i) (hy i)
  zero_mem' i := (S i).zero_mem
  smul_mem' r _ hx i := (S i).smul_mem r (hx i)

@[simp]
/-
**Finsupp.mem_submodule_iff** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：mem_submodule_iff (S : α -> Submodule R M) (x : α ->₀ M) : x in submodule 
S ↔ forall i, x i in S i
参数：S : α -> Submodule R M；x : α ->₀ M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_submodule_iff (S : α → Submodule R M) (x : α →₀ M) :
    x ∈ submodule S ↔ ∀ i, x i ∈ S i := by
  rfl

@[simp]
/-
**Finsupp.comap_lsingle_submodule** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：comap_lsingle_submodule (p : α -> Submodule R M) (i : α) : Submodule.comap
 (lsingle i) (submodule p) = p i
参数：p : α -> Submodule R M；i : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Finsupp.single_eq_of_ne'`：single_eq_of_ne' (h : a != a') : (single a b :
 α ->₀ M) a' = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
-/
lemma comap_lsingle_submodule (p : α → Submodule R M) (i : α) :
    Submodule.comap (lsingle i) (submodule p) = p i := by
  ext x
  refine ⟨fun hx ↦ by simpa using hx i, fun hx j ↦ ?_⟩
  rcases eq_or_ne i j with rfl|h <;> simp_all
/-
**Finsupp.submodule_eq_iSup** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：submodule_eq_iSup (p : α -> Submodule R M) : Finsupp.submodule p = ⨆ i, Su
bmodule.map (Finsupp.lsingle i) (p i)
参数：p : α -> Submodule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finsupp.sum_single`：sum_single [AddCommMonoid M] (f : α ->₀ M) : f.sum s
ingle = f
· 使用定理 `Submodule.sum_mem`：∀ {R : Type u} {M : Type v} {ι : Type w} [inst : Semi
ring R] [inst_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodu
le R M)…
· 使用定理 `Submodule.mem_iSup_of_mem`：mem_iSup_of_mem {ι : Sort*} {b : M} {p : ι ->
 Submodule R M} (i : ι) (h : b in p i) : b in ⨆ i, p i
· 使用定理 `Submodule.mem_map_of_mem`：mem_map_of_mem {f : M ->ₛₗ[σ₁₂] M₂} {p : Submo
dule R M} {r} (h : r in p) : f r in map f p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用引理 `Finsupp.comap_lsingle_submodule`：comap_lsingle_submodule (p : α -> Submo
dule R M) (i : α) : Submodule.comap (lsingle i) (submodule p) = p i
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma submodule_eq_iSup (p : α → Submodule R M) :
    Finsupp.submodule p = ⨆ i, Submodule.map (Finsupp.lsingle i) (p i) := by
  refine le_antisymm ?_ ?_
  · intro x hx
    rw [← Finsupp.sum_single x]
    refine Submodule.sum_mem _ (fun i _ ↦ ?_)
    exact Submodule.mem_iSup_of_mem i (Submodule.mem_map_of_mem (hx i))
  · simp [iSup_le_iff, Submodule.map_le_iff_le_comap]

@[simp]
/-
**Finsupp.submodule_top** 是 Mathlib 中的一个引理，位于命名空间 `Finsupp`。
形式化陈述：submodule_top : Finsupp.submodule (fun _ : α => (⊤ : Submodule R M)) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma submodule_top : Finsupp.submodule (fun _ : α ↦ (⊤ : Submodule R M)) = ⊤ := by
  ext
  simp
/-
**Finsupp.ker_mapRange** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：ker_mapRange (f : M ->ₗ[R] N) (I : Type*) : LinearMap.ker (mapRange.linear
Map (α
参数：f : M ->ₗ[R] N；I : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.map_zero`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ :
 Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid 
M] [inst…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finsupp.mapRange.linearMap_apply`：∀ {α : Type u_1} {M : Type u_2} {N : T
ype u_3} {R : Type u_5} {R₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R
₂]   [inst_2 : AddComm…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem ker_mapRange (f : M →ₗ[R] N) (I : Type*) :
    LinearMap.ker (mapRange.linearMap (α := I) f) = submodule (fun _ => LinearMap.ker f) := by
  ext x
  simp [Finsupp.ext_iff]
/-
**Finsupp.range_mapRange_linearMap** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：range_mapRange_linearMap (f : M ->ₗ[R] N) (hf : LinearMap.ker f = ⊥) (I : 
Type*) : LinearMap.range (mapRange.linearMap (α
参数：f : M ->ₗ[R] N；hf : LinearMap.ker f = ⊥；I : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LinearMap.map_zero`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ :
 Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid 
M] [inst…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finsupp.mapRange.linearMap_apply`：∀ {α : Type u_1} {M : Type u_2} {N : T
ype u_3} {R : Type u_5} {R₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R
₂]   [inst_2 : AddComm…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₃`：contrapose₃ {p q : Prop} : (q -> 
¬ p) -> (p -> ¬ q)
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearMap.ker_eq_bot'`：ker_eq_bot' {f : M ->ₛₗ[τ₁₂] M₂} : ker f = ⊥ ↔ fo
rall m, f m = 0 -> m = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem range_mapRange_linearMap (f : M →ₗ[R] N) (hf : LinearMap.ker f = ⊥) (I : Type*) :
    LinearMap.range (mapRange.linearMap (α := I) f) = submodule (fun _ => LinearMap.range f) := by
  ext x
  constructor
  · rintro ⟨y, hy⟩
    simp [← hy]
  · intro hx
    choose y hy using hx
    refine ⟨⟨x.support, y, fun i => ?_⟩, by ext; simp_all⟩
    constructor
    <;> contrapose
    <;> simp_all +contextual [← hy, map_zero, LinearMap.ker_eq_bot'.1 hf]

end Finsupp

namespace FunOnFinite

section

variable {M : Type*} [AddCommMonoid M] {X Y Z : Type*}

/-- The map `(X → M) → (Y → M)` induced by a map `X → Y` between finite types. -/
/-
**FunOnFinite.map** 是 Mathlib 中的一个定义，位于命名空间 `FunOnFinite`。
形式化陈述：map [Finite X] [Finite Y] (f : X -> Y) (s : X -> M) : Y -> M
参数：f : X -> Y；s : X -> M。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The map `(X → M) → (Y → M)` induced by a map `X → Y` between finite types.
-/
noncomputable def map [Finite X] [Finite Y] (f : X → Y) (s : X → M) : Y → M :=
  Finsupp.equivFunOnFinite (Finsupp.mapDomain f (Finsupp.equivFunOnFinite.symm s))
/-
**FunOnFinite.map_apply_apply** 是 Mathlib 中的一个引理，位于命名空间 `FunOnFinite`。
形式化陈述：map_apply_apply [Fintype X] [Finite Y] [DecidableEq Y] (f : X -> Y) (s : X
 -> M) (y : Y) : map f s y = ∑ x with f x = y, s x
参数：f : X -> Y；s : X -> M；y : Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finsupp.univ_sum_single`：univ_sum_single [Fintype α] [AddCommMonoid M] (
f : α ->₀ M) : ∑ a : α, single a (f a) = f
· 使用定理 `Finsupp.mapDomain_finsetSum`：mapDomain_finsetSum {f : α -> β} {s : Finse
t ι} {v : ι -> α ->₀ M} : mapDomain f (∑ i in s, v i) = ∑ i in s, mapDomain f (v
 i)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finsupp.mapDomain_single`：mapDomain_single {f : α -> β} {a : α} {b : M} 
: mapDomain f (single a b) = single (f a) b
· 使用定理 `Finsupp.equivFunOnFinite_apply`：∀ {α : Type u_1} {M : Type u_4} [inst : 
Zero M] [inst_1 : Finite α] (a : α →₀ M) (a_1 : α),   Finsupp.equivFunOnFinite a
 a_1 = a a_1
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Finsupp.coe_finsetSum`：∀ {α : Type u_1} {ι : Type u_2} {N : Type u_10} [
inst : AddCommMonoid N] (S : Finset ι) (f : ι → α →₀ N),   ⇑(∑ i ∈ S, f i) = ∑ i
 ∈ S, ⇑(f i…
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `Finset.sum_filter`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst 
: AddCommMonoid M] (p : ι → Prop) [inst_1 : DecidablePred p]   (f : ι → M), ∑ a 
∈ s wit…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Finsupp.single_eq_of_ne'`：single_eq_of_ne' (h : a != a') : (single a b :
 α ->₀ M) a' = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
-/
lemma map_apply_apply [Fintype X] [Finite Y] [DecidableEq Y] (f : X → Y) (s : X → M) (y : Y) :
    map f s y = ∑ x with f x = y, s x := by
  obtain ⟨s, rfl⟩ := Finsupp.equivFunOnFinite.surjective s
  dsimp [map]
  simp only [Equiv.symm_apply_apply]
  nth_rw 1 [← Finsupp.univ_sum_single s]
  rw [Finsupp.mapDomain_finsetSum]
  simp [Finset.sum_filter]
  congr
  aesop

@[simp]
/-
**FunOnFinite.map_piSingle** 是 Mathlib 中的一个引理，位于命名空间 `FunOnFinite`。
形式化陈述：map_piSingle [Finite X] [Finite Y] [DecidableEq X] [DecidableEq Y] (f : X 
-> Y) (x : X) (m : M) : map f (Pi.single x m) = Pi.single (f x) m
参数：f : X -> Y；x : X；m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Finsupp.equivFunOnFinite_symm_single`：equivFunOnFinite_symm_single [Deci
dableEq α] [Finite α] (x : α) (m : M) : Finsupp.equivFunOnFinite.symm (Pi.single
 x m) = Finsupp.single x m
· 使用定理 `Finsupp.mapDomain_single`：mapDomain_single {f : α -> β} {a : α} {b : M} 
: mapDomain f (single a b) = single (f a) b
· 使用定理 `Finsupp.equivFunOnFinite_single`：equivFunOnFinite_single [DecidableEq α]
 [Finite α] (x : α) (m : M) : Finsupp.equivFunOnFinite (Finsupp.single x m) = Pi
.single x m
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_piSingle [Finite X] [Finite Y] [DecidableEq X] [DecidableEq Y]
    (f : X → Y) (x : X) (m : M) :
    map f (Pi.single x m) = Pi.single (f x) m := by
  simp [map]

variable (M) in
/-
**FunOnFinite.map_id** 是 Mathlib 中的一个引理，位于命名空间 `FunOnFinite`。
形式化陈述：map_id [Finite X] : map (_root_.id : X -> X) (M
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Finsupp.mapDomain_id`：mapDomain_id : mapDomain id v = v
· 使用定理 `Finsupp.equivFunOnFinite_apply`：∀ {α : Type u_1} {M : Type u_4} [inst : 
Zero M] [inst_1 : Finite α] (a : α →₀ M) (a_1 : α),   Finsupp.equivFunOnFinite a
 a_1 = a a_1
· 使用定理 `Finsupp.equivFunOnFinite_symm_apply_apply`：∀ {α : Type u_1} {M : Type u_
4} [inst : Zero M] [inst_1 : Finite α] (f : α → M) (a : α),   (Finsupp.equivFunO
nFinite.symm f) a = f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_id [Finite X] : map (_root_.id : X → X) (M := M) = _root_.id := by
  ext s
  simp [map]
/-
**FunOnFinite.map_comp** 是 Mathlib 中的一个引理，位于命名空间 `FunOnFinite`。
形式化陈述：map_comp [Finite X] [Finite Y] [Finite Z] (g : Y -> Z) (f : X -> Y) : map 
(g.comp f) (M
参数：g : Y -> Z；f : X -> Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finsupp.mapDomain_comp`：mapDomain_comp {f : α -> β} {g : β -> γ} : mapDo
main (g ∘ f) v = mapDomain g (mapDomain f v)
· 使用定理 `Finsupp.equivFunOnFinite_apply`：∀ {α : Type u_1} {M : Type u_4} [inst : 
Zero M] [inst_1 : Finite α] (a : α →₀ M) (a_1 : α),   Finsupp.equivFunOnFinite a
 a_1 = a a_1
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_comp [Finite X] [Finite Y] [Finite Z] (g : Y → Z) (f : X → Y) :
    map (g.comp f) (M := M) = (map g).comp (map f) := by
  ext s
  simp [map, Finsupp.mapDomain_comp]

end

section

variable (R M : Type*) [Semiring R] [AddCommMonoid M] [Module R M] {X Y Z : Type*}

/-- The linear map `(X → M) →ₗ[R] (Y → M)` induced by a map `X → Y` between finite types. -/
/-
**FunOnFinite.linearMap** 是 Mathlib 中的一个定义，位于命名空间 `FunOnFinite`。
形式化陈述：linearMap [Finite X] [Finite Y] (f : X -> Y) : (X -> M) ->ₗ[R] (Y -> M)
参数：f : X -> Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The linear map `(X → M) →ₗ[R] (Y → M)` induced by a map `X → Y` between finite t
ypes.
-/
noncomputable def linearMap [Finite X] [Finite Y] (f : X → Y) :
    (X → M) →ₗ[R] (Y → M) :=
  (((Finsupp.linearEquivFunOnFinite R M Y)).comp (Finsupp.lmapDomain M R f)).comp
    (Finsupp.linearEquivFunOnFinite R M X).symm.toLinearMap
/-
**FunOnFinite.linearMap_apply_apply** 是 Mathlib 中的一个引理，位于命名空间 `FunOnFinite`。
形式化陈述：linearMap_apply_apply [Fintype X] [Finite Y] [DecidableEq Y] (f : X -> Y) 
(s : X -> M) (y : Y) : linearMap R M f s y = (Finset.univ.filter (fun (x : X) =>
 f x = y)).sum s
参数：f : X -> Y；s : X -> M；y : Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `FunOnFinite.map_apply_apply`：map_apply_apply [Fintype X] [Finite Y] [Dec
idableEq Y] (f : X -> Y) (s : X -> M) (y : Y) : map f s y = ∑ x with f x = y, s 
x
-/
lemma linearMap_apply_apply
    [Fintype X] [Finite Y] [DecidableEq Y] (f : X → Y) (s : X → M) (y : Y) :
    linearMap R M f s y = (Finset.univ.filter (fun (x : X) ↦ f x = y)).sum s := by
  apply map_apply_apply

@[simp]
/-
**FunOnFinite.linearMap_piSingle** 是 Mathlib 中的一个引理，位于命名空间 `FunOnFinite`。
形式化陈述：linearMap_piSingle [Finite X] [Finite Y] [DecidableEq X] [DecidableEq Y] (
f : X -> Y) (x : X) (m : M) : linearMap R M f (Pi.single x m) = Pi.single (f x) 
m
参数：f : X -> Y；x : X；m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `FunOnFinite.map_piSingle`：map_piSingle [Finite X] [Finite Y] [DecidableE
q X] [DecidableEq Y] (f : X -> Y) (x : X) (m : M) : map f (Pi.single x m) = Pi.s
ingle (f x) m
-/
lemma linearMap_piSingle [Finite X] [Finite Y] [DecidableEq X] [DecidableEq Y]
    (f : X → Y) (x : X) (m : M) :
    linearMap R M f (Pi.single x m) = Pi.single (f x) m := by
  apply map_piSingle

variable (X) in
@[simp]
/-
**FunOnFinite.linearMap_id** 是 Mathlib 中的一个引理，位于命名空间 `FunOnFinite`。
形式化陈述：linearMap_id [Finite X] : linearMap R M (_root_.id : X -> X) = .id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.pi_ext'`：pi_ext' (h : forall i, f.comp (single R φ i) = g.comp
 (single R φ i)) : f = g
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `FunOnFinite.linearMap_piSingle`：linearMap_piSingle [Finite X] [Finite Y]
 [DecidableEq X] [DecidableEq Y] (f : X -> Y) (x : X) (m : M) : linearMap R M f 
(Pi.single x m) = Pi…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma linearMap_id [Finite X] : linearMap R M (_root_.id : X → X) = .id := by
  classical
  aesop
/-
**FunOnFinite.linearMap_comp** 是 Mathlib 中的一个引理，位于命名空间 `FunOnFinite`。
形式化陈述：linearMap_comp [Finite X] [Finite Y] [Finite Z] (f : X -> Y) (g : Y -> Z) 
: linearMap R M (g.comp f) = (linearMap R M g).comp (linearMap R M f)
参数：f : X -> Y；g : Y -> Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.pi_ext'`：pi_ext' (h : forall i, f.comp (single R φ i) = g.comp
 (single R φ i)) : f = g
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `FunOnFinite.linearMap_piSingle`：linearMap_piSingle [Finite X] [Finite Y]
 [DecidableEq X] [DecidableEq Y] (f : X -> Y) (x : X) (m : M) : linearMap R M f 
(Pi.single x m) = Pi…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma linearMap_comp [Finite X] [Finite Y] [Finite Z] (f : X → Y) (g : Y → Z) :
    linearMap R M (g.comp f) = (linearMap R M g).comp (linearMap R M f) := by
  classical
  aesop

end

end FunOnFinite

