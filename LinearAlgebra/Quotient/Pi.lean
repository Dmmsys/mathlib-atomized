/-
Copyright (c) 2022 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Alex J. Best
-/
module

public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Submodule quotients and direct sums

This file contains some results on the quotient of a module by a direct sum of submodules,
and the direct sum of quotients of modules by submodules.

## Main definitions

* `Submodule.piQuotientLift`: create a map out of the direct sum of quotients
* `Submodule.quotientPiLift`: create a map out of the quotient of a direct sum
* `Submodule.quotientPi`: the quotient of a direct sum is the direct sum of quotients.

-/

@[expose] public section


namespace Submodule

open LinearMap

variable {ι R : Type*} [CommRing R]
variable {Ms : ι → Type*} [∀ i, AddCommGroup (Ms i)] [∀ i, Module R (Ms i)]
variable {N : Type*} [AddCommGroup N] [Module R N]
variable {Ns : ι → Type*} [∀ i, AddCommGroup (Ns i)] [∀ i, Module R (Ns i)]

/-- Lift a family of maps to the direct sum of quotients. -/
/-
**Submodule.piQuotientLift** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：piQuotientLift [Fintype ι] [DecidableEq ι] (p : forall i, Submodule R (Ms 
i)) (q : Submodule R N) (f : forall i, Ms i ->ₗ[R] N) (hf : forall i, p i <= q.c
omap (f i)) : (forall i, Ms i ⧸ p i) ->ₗ[R] N ⧸ q
参数：p : forall i, Submodule R (Ms i)；q : Submodule R N；f : forall i, Ms i ->ₗ[R] 
N；hf : forall i, p i <= q.comap (f i)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lift a family of maps to the direct sum of quotients.
-/
def piQuotientLift [Fintype ι] [DecidableEq ι] (p : ∀ i, Submodule R (Ms i)) (q : Submodule R N)
    (f : ∀ i, Ms i →ₗ[R] N) (hf : ∀ i, p i ≤ q.comap (f i)) : (∀ i, Ms i ⧸ p i) →ₗ[R] N ⧸ q :=
  lsum R (fun i => Ms i ⧸ p i) R fun i => (p i).mapQ q (f i) (hf i)

@[simp]
/-
**Submodule.piQuotientLift_mk** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：piQuotientLift_mk [Fintype ι] [DecidableEq ι] (p : forall i, Submodule R (
Ms i)) (q : Submodule R N) (f : forall i, Ms i ->ₗ[R] N) (hf : forall i, p i <= 
q.comap (f i)) (x : forall i, Ms i) : (piQuotientLift p q f hf fun i => Quotient
.mk (x i)) = Quotient.mk (lsum _ _ R f x)
参数：p : forall i, Submodule R (Ms i)；q : Submodule R N；f : forall i, Ms i ->ₗ[R] 
N；hf : forall i, p i <= q.comap (f i)；x : forall i, Ms i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.piQuotientLift.eq_1`：∀ {ι : Type u_1} {R : Type u_2} [inst : C
ommRing R] {Ms : ι → Type u_3} [inst_1 : (i : ι) → AddCommGroup (Ms i)]   [inst_
2 : (i : ι) → _root…
· 使用定理 `LinearMap.lsum_apply`：lsum_apply (S) [AddCommMonoid M] [Module R M] [Fin
type ι] [Semiring S] [Module S M] [SMulCommClass R S M] (f : (i : ι) -> φ i ->ₗ[
R] M) : ls…
· 使用定理 `LinearMap.sum_apply`：sum_apply (t : Finset ι) (f : ι -> M ->ₛₗ[σ₁₂] M₂) 
(b : M) : (∑ d in t, f d) b = ∑ d in t, f d b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.mkQ_apply`：mkQ_apply (x : M) : p.mkQ x = Quotient.mk x
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem piQuotientLift_mk [Fintype ι] [DecidableEq ι] (p : ∀ i, Submodule R (Ms i))
    (q : Submodule R N) (f : ∀ i, Ms i →ₗ[R] N) (hf : ∀ i, p i ≤ q.comap (f i)) (x : ∀ i, Ms i) :
    (piQuotientLift p q f hf fun i => Quotient.mk (x i)) = Quotient.mk (lsum _ _ R f x) := by
  rw [piQuotientLift, lsum_apply, sum_apply, ← mkQ_apply, lsum_apply, sum_apply, _root_.map_sum]
  simp only [coe_proj, mapQ_apply, mkQ_apply, comp_apply]

@[simp]
/-
**Submodule.piQuotientLift_single** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：piQuotientLift_single [Fintype ι] [DecidableEq ι] (p : forall i, Submodule
 R (Ms i)) (q : Submodule R N) (f : forall i, Ms i ->ₗ[R] N) (hf : forall i, p i
 <= q.comap (f i)) (i) (x : Ms i ⧸ p i) : piQuotientLift p q f hf (Pi.single i x
) = mapQ _ _ (f i) (hf i) x
参数：p : forall i, Submodule R (Ms i)；q : Submodule R N；f : forall i, Ms i ->ₗ[R] 
N；hf : forall i, p i <= q.comap (f i)；i；x : Ms i ⧸ p i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.sum_apply`：sum_apply (t : Finset ι) (f : ι -> M ->ₛₗ[σ₁₂] M₂) 
(b : M) : (∑ d in t, f d) b = ∑ d in t, f d b
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_eq_single`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] {s : Finset ι} {f : ι → M} (a : ι),   (∀ b ∈ s, b ≠ a → f b = 0) → (a ∉ s
 → f a = 0…
· 使用定理 `Pi.single_eq_of_ne`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) 
→ Zero (M i)] [inst_1 : DecidableEq ι] {i i' : ι},   i' ≠ i → ∀ (x : M i), Pi.si
ngle i x…
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
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `Pi.single_eq_same`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) →
 Zero (M i)] [inst_1 : DecidableEq ι] (i : ι) (x : M i),   Pi.single i x i = x
-/
theorem piQuotientLift_single [Fintype ι] [DecidableEq ι] (p : ∀ i, Submodule R (Ms i))
    (q : Submodule R N) (f : ∀ i, Ms i →ₗ[R] N) (hf : ∀ i, p i ≤ q.comap (f i)) (i)
    (x : Ms i ⧸ p i) : piQuotientLift p q f hf (Pi.single i x) = mapQ _ _ (f i) (hf i) x := by
  simp_rw [piQuotientLift, lsum_apply, sum_apply, comp_apply, proj_apply]
  rw [Finset.sum_eq_single i]
  · rw [Pi.single_eq_same]
  · rintro j - hj
    rw [Pi.single_eq_of_ne hj, map_zero]
  · intros
    have := Finset.mem_univ i
    contradiction

/-- Lift a family of maps to a quotient of direct sums. -/
/-
**Submodule.quotientPiLift** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：quotientPiLift (p : forall i, Submodule R (Ms i)) (f : forall i, Ms i ->ₗ[
R] Ns i) (hf : forall i, p i <= ker (f i)) : (forall i, Ms i) ⧸ pi Set.univ p ->
ₗ[R] forall i, Ns i
参数：p : forall i, Submodule R (Ms i)；f : forall i, Ms i ->ₗ[R] Ns i；hf : forall i
, p i <= ker (f i)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lift a family of maps to a quotient of direct sums.
-/
def quotientPiLift (p : ∀ i, Submodule R (Ms i)) (f : ∀ i, Ms i →ₗ[R] Ns i)
    (hf : ∀ i, p i ≤ ker (f i)) : (∀ i, Ms i) ⧸ pi Set.univ p →ₗ[R] ∀ i, Ns i :=
  (pi Set.univ p).liftQ (LinearMap.pi fun i => (f i).comp (proj i)) fun x hx =>
    mem_ker.mpr <| by
      ext i
      simpa using hf i (mem_pi.mp hx i (Set.mem_univ i))

@[simp]
/-
**Submodule.quotientPiLift_mk** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：quotientPiLift_mk (p : forall i, Submodule R (Ms i)) (f : forall i, Ms i -
>ₗ[R] Ns i) (hf : forall i, p i <= ker (f i)) (x : forall i, Ms i) : quotientPiL
ift p f hf (Quotient.mk x) = fun i => f i (x i)
参数：p : forall i, Submodule R (Ms i)；f : forall i, Ms i ->ₗ[R] Ns i；hf : forall i
, p i <= ker (f i)；x : forall i, Ms i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem quotientPiLift_mk (p : ∀ i, Submodule R (Ms i)) (f : ∀ i, Ms i →ₗ[R] Ns i)
    (hf : ∀ i, p i ≤ ker (f i)) (x : ∀ i, Ms i) :
    quotientPiLift p f hf (Quotient.mk x) = fun i => f i (x i) :=
  rfl

namespace quotientPi_aux

variable (p : ∀ i, Submodule R (Ms i))

@[simp]
/-
**Submodule.quotientPi_aux.toFun** 是 Mathlib 中的一个定义，位于命名空间 `Submodule.quotientPi
_aux`。
形式化陈述：toFun : ((forall i, Ms i) ⧸ pi Set.univ p) -> forall i, Ms i ⧸ p i
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def toFun : ((∀ i, Ms i) ⧸ pi Set.univ p) → ∀ i, Ms i ⧸ p i :=
  quotientPiLift p (fun i => (p i).mkQ) fun i => (ker_mkQ (p i)).ge
/-
**Submodule.quotientPi_aux.map_add** 是 Mathlib 中的一个定理，位于命名空间 `Submodule.quotient
Pi_aux`。
形式化陈述：map_add (x y : ((i : ι) -> Ms i) ⧸ pi Set.univ p) : toFun p (x + y) = toFu
n p x + toFun p y
参数：x y : ((i : ι) -> Ms i) ⧸ pi Set.univ p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.map_add`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ : 
Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid M
] [inst…
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Submodule.ker_mkQ`：ker_mkQ : ker p.mkQ = p
-/
theorem map_add (x y : ((i : ι) → Ms i) ⧸ pi Set.univ p) :
    toFun p (x + y) = toFun p x + toFun p y :=
  LinearMap.map_add (quotientPiLift p (fun i => (p i).mkQ) fun i => (ker_mkQ (p i)).ge) x y
/-
**Submodule.quotientPi_aux.map_smul** 是 Mathlib 中的一个定理，位于命名空间 `Submodule.quotien
tPi_aux`。
形式化陈述：map_smul (r : R) (x : ((i : ι) -> Ms i) ⧸ pi Set.univ p) : toFun p (r • x)
 = (RingHom.id R r) • toFun p x
参数：r : R；x : ((i : ι) -> Ms i) ⧸ pi Set.univ p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.map_smul`：∀ {R : Type u_1} {M : Type u_8} {M₂ : Type u_10} [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid M₂] [inst_
3 : _roo…
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Submodule.ker_mkQ`：ker_mkQ : ker p.mkQ = p
-/
theorem map_smul (r : R) (x : ((i : ι) → Ms i) ⧸ pi Set.univ p) :
    toFun p (r • x) = (RingHom.id R r) • toFun p x :=
  LinearMap.map_smul (quotientPiLift p (fun i => (p i).mkQ) fun i => (ker_mkQ (p i)).ge) r x

variable [Fintype ι] [DecidableEq ι]

@[simp]
/-
**Submodule.quotientPi_aux.invFun** 是 Mathlib 中的一个定义，位于命名空间 `Submodule.quotientP
i_aux`。
形式化陈述：invFun : (forall i, Ms i ⧸ p i) -> (forall i, Ms i) ⧸ pi Set.univ p
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def invFun : (∀ i, Ms i ⧸ p i) → (∀ i, Ms i) ⧸ pi Set.univ p :=
  piQuotientLift p (pi Set.univ p) _ fun _ => le_comap_single_pi p
/-
**Submodule.quotientPi_aux.left_inv** 是 Mathlib 中的一个定理，位于命名空间 `Submodule.quotien
tPi_aux`。
形式化陈述：left_inv : Function.LeftInverse (invFun p) (toFun p)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.Quotient.induction_on`：induction_on {C : M ⧸ p -> Prop} (x : M
 ⧸ p) (H : forall z, C (Submodule.Quotient.mk z)) : C x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.quotientPiLift_mk`：quotientPiLift_mk (p : forall i, Submodule 
R (Ms i)) (f : forall i, Ms i ->ₗ[R] Ns i) (hf : forall i, p i <= ker (f i)) (x 
: forall i, Ms i)…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Submodule.mkQ_apply`：mkQ_apply (x : M) : p.mkQ x = Quotient.mk x
· 使用定理 `Submodule.piQuotientLift_mk`：piQuotientLift_mk [Fintype ι] [DecidableEq 
ι] (p : forall i, Submodule R (Ms i)) (q : Submodule R N) (f : forall i, Ms i ->
ₗ[R] N) (hf : for…
· 使用定理 `LinearMap.lsum_single`：lsum_single (S) [Fintype ι] [Semiring S] [forall 
i, Module S (φ i)] [forall i, SMulCommClass R S (φ i)] : LinearMap.lsum R φ S (L
inearMap.si…
· 使用定理 `LinearMap.id_apply`：id_apply (x : M) : @id R M _ _ _ x = x
-/
theorem left_inv : Function.LeftInverse (invFun p) (toFun p) := fun x =>
  Submodule.Quotient.induction_on _ x fun x' => by
    dsimp only [toFun, invFun]
    rw [quotientPiLift_mk p, funext fun i => (mkQ_apply (p i) (x' i)), piQuotientLift_mk p,
      lsum_single, id_apply]
/-
**Submodule.quotientPi_aux.right_inv** 是 Mathlib 中的一个定理，位于命名空间 `Submodule.quotie
ntPi_aux`。
形式化陈述：right_inv : Function.RightInverse (invFun p) (toFun p)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.rightInverse_iff_comp`：rightInverse_iff_comp {f : α -> β} {g : 
β -> α} : RightInverse f g ↔ g ∘ f = id
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.coe_comp`：coe_comp : (f.comp g : M₁ -> M₃) = f ∘ g
· 使用定理 `LinearMap.id_coe`：id_coe : ((LinearMap.id : M ->ₗ[R] M) : M -> M) = _roo
t_.id
· 使用定理 `LinearMap.pi_ext`：pi_ext (h : forall i x, f (Pi.single i x) = g (Pi.sing
le i x)) : f = g
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Submodule.Quotient.induction_on`：induction_on {C : M ⧸ p -> Prop} (x : M
 ⧸ p) (H : forall z, C (Submodule.Quotient.mk z)) : C x
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LinearMap.comp_apply`：comp_apply (x : M₁) : f.comp g x = f (g x)
· 使用定理 `Submodule.piQuotientLift_single`：piQuotientLift_single [Fintype ι] [Deci
dableEq ι] (p : forall i, Submodule R (Ms i)) (q : Submodule R N) (f : forall i,
 Ms i ->ₗ[R] N) (hf :…
· 使用定理 `Submodule.mapQ_apply`：mapQ_apply (f : M ->ₛₗ[τ₁₂] M₂) {h} (x : M) : mapQ
 p q f h (Quotient.mk x) = Quotient.mk (f x)
· 使用定理 `Submodule.quotientPiLift_mk`：quotientPiLift_mk (p : forall i, Submodule 
R (Ms i)) (f : forall i, Ms i ->ₗ[R] Ns i) (hf : forall i, p i <= ker (f i)) (x 
: forall i, Ms i)…
· 使用定理 `LinearMap.id_apply`：id_apply (x : M) : @id R M _ _ _ x = x
· 使用定理 `Pi.single_eq_same`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) →
 Zero (M i)] [inst_1 : DecidableEq ι] (i : ι) (x : M i),   Pi.single i x i = x
· 使用定理 `Pi.single_eq_of_ne`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) 
→ Zero (M i)] [inst_1 : DecidableEq ι] {i i' : ι},   i' ≠ i → ∀ (x : M i), Pi.si
ngle i x…
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Submodule.Quotient.mk_zero`：mk_zero : mk 0 = (0 : M ⧸ p)
-/
theorem right_inv : Function.RightInverse (invFun p) (toFun p) := by
  dsimp only [toFun, invFun]
  rw [Function.rightInverse_iff_comp, ← coe_comp, ← @id_coe R]
  congr
  refine pi_ext fun i x ↦ ?_
  induction x using Submodule.Quotient.induction_on with | _ x'
  refine funext fun j ↦ ?_
  rw [comp_apply, piQuotientLift_single, mapQ_apply,
    quotientPiLift_mk, id_apply]
  by_cases hij : i = j <;> simp only [mkQ_apply, coe_single]
  · subst hij
    rw [Pi.single_eq_same, Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne (Ne.symm hij), Pi.single_eq_of_ne (Ne.symm hij), Quotient.mk_zero]

end quotientPi_aux

open quotientPi_aux in
/-- The quotient of a direct sum is the direct sum of quotients. -/
@[simps!]
/-
**Submodule.quotientPi** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：quotientPi [Fintype ι] [DecidableEq ι] (p : forall i, Submodule R (Ms i)) 
: ((forall i, Ms i) ⧸ pi Set.univ p) ≃ₗ[R] forall i, Ms i ⧸ p i where toFun
参数：p : forall i, Submodule R (Ms i)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.quotientPi_aux.map_add`：map_add (x y : ((i : ι) -> Ms i) ⧸ pi 
Set.univ p) : toFun p (x + y) = toFun p x + toFun p y
· 使用定理 `Submodule.quotientPi_aux.map_smul`：map_smul (r : R) (x : ((i : ι) -> Ms 
i) ⧸ pi Set.univ p) : toFun p (r • x) = (RingHom.id R r) • toFun p x
· 使用定理 `Submodule.quotientPi_aux.left_inv`：left_inv : Function.LeftInverse (invF
un p) (toFun p)
· 使用定理 `Submodule.quotientPi_aux.right_inv`：right_inv : Function.RightInverse (i
nvFun p) (toFun p)

--- 原说明 ---
The quotient of a direct sum is the direct sum of quotients.
-/
def quotientPi [Fintype ι] [DecidableEq ι] (p : ∀ i, Submodule R (Ms i)) :
    ((∀ i, Ms i) ⧸ pi Set.univ p) ≃ₗ[R] ∀ i, Ms i ⧸ p i where
  toFun := toFun p
  invFun := invFun p
  map_add' := map_add p
  map_smul' := quotientPi_aux.map_smul p
  left_inv := left_inv p
  right_inv := right_inv p

end Submodule

