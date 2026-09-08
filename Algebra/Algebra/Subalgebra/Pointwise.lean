/-
Copyright (c) 2021 Eric Weiser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.Algebra.Ring.Subring.Pointwise

/-!
# Pointwise actions on subalgebras.

If `R'` acts on an `R`-algebra `A` (so that `R'` and `R` actions commute)
then we get an `R'` action on the collection of `R`-subalgebras.
-/

@[expose] public section


namespace Subalgebra

section Pointwise

variable {R : Type*} {A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

/-
**Subalgebra.mul_toSubmodule_le** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：mul_toSubmodule_le (S T : Subalgebra R A) : Subalgebra.toSubmodule S * Sub
algebra.toSubmodule T <= Subalgebra.toSubmodule (S ⊔ T)
参数：S T : Subalgebra R A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.mul_le`：mul_le : M * N <= P ↔ forall m in M, forall n in N, m 
* n in P
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `SubsemiringClass.toSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Type 
u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringClas
s S R], SubmonoidClass …
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A
· 使用定理 `Algebra.mem_sup_left`：mem_sup_left {S T : Subalgebra R A} : forall {x : 
A}, x in S -> x in S ⊔ T
· 使用定理 `Algebra.mem_sup_right`：mem_sup_right {S T : Subalgebra R A} : forall {x 
: A}, x in T -> x in S ⊔ T
-/
theorem mul_toSubmodule_le (S T : Subalgebra R A) :
    Subalgebra.toSubmodule S * Subalgebra.toSubmodule T ≤ Subalgebra.toSubmodule (S ⊔ T) := by
  rw [Submodule.mul_le]
  intro y hy z hz
  simp only [mem_toSubmodule]
  exact mul_mem (Algebra.mem_sup_left hy) (Algebra.mem_sup_right hz)

/-- As submodules, subalgebras are idempotent. -/
@[simp]
/-
**Subalgebra.isIdempotentElem_toSubmodule** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`
。
形式化陈述：isIdempotentElem_toSubmodule (S : Subalgebra R A) : IsIdempotentElem S.toS
ubmodule
参数：S : Subalgebra R A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `Subalgebra.mul_toSubmodule_le`：mul_toSubmodule_le (S T : Subalgebra R A)
 : Subalgebra.toSubmodule S * Subalgebra.toSubmodule T <= Subalgebra.toSubmodule
 (S ⊔ T)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_idem`：sup_idem (a : α) : a ⊔ a = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Submodule.mul_mem_mul`：mul_mem_mul (hm : m in M) (hn : n in N) : m * n i
n M * N
· 使用定理 `OneMemClass.one_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
One M} {inst_1 : SetLike S M} [self : OneMemClass S M] (s : S), 1 ∈ s
· 使用定理 `AddSubmonoidWithOneClass.toOneMemClass`：∀ {S : Type u_1} {R : outParam (
Type u_2)} {inst : AddMonoidWithOne R} {inst_1 : SetLike S R}   [self : AddSubmo
noidWithOneClass S R], OneMe…
· 使用定理 `SubsemiringClass.addSubmonoidWithOneClass`：∀ (S : Type u_1) (R : Type u)
 {x : NonAssocSemiring R} [inst : SetLike S R] [h : SubsemiringClass S R],   Add
SubmonoidWithOneClass S R
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A

--- 原说明 ---
As submodules, subalgebras are idempotent.
-/
theorem isIdempotentElem_toSubmodule (S : Subalgebra R A) :
    IsIdempotentElem S.toSubmodule := by
  apply le_antisymm
  · refine (mul_toSubmodule_le _ _).trans_eq ?_
    rw [sup_idem]
  · intro x hx1
    rw [← mul_one x]
    exact Submodule.mul_mem_mul hx1 (show (1 : A) ∈ S from one_mem S)

/-- When `A` is commutative, `Subalgebra.mul_toSubmodule_le` is strict. -/
/-
**Subalgebra.mul_toSubmodule** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：mul_toSubmodule {R : Type*} {A : Type*} [CommSemiring R] [CommSemiring A] 
[Algebra R A] (S T : Subalgebra R A) : (Subalgebra.toSubmodule S) * (Subalgebra.
toSubmodule T) = Subalgebra.toSubmodule (S ⊔ T)
参数：S T : Subalgebra R A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Subalgebra.mul_toSubmodule_le`：mul_toSubmodule_le (S T : Subalgebra R A)
 : Subalgebra.toSubmodule S * Subalgebra.toSubmodule T <= Subalgebra.toSubmodule
 (S ⊔ T)
· 使用定理 `Algebra.adjoin_induction`：adjoin_induction {p : (x : A) -> x in adjoin R
 s -> Prop} (mem : forall (x) (hx : x in s), p x (subset_adjoin hx)) (algebraMap
 : forall r, p…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Submodule.mul_mem_mul`：mul_mem_mul (hm : m in M) (hn : n in N) : m * n i
n M * N
· 使用定理 `OneMemClass.one_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
One M} {inst_1 : SetLike S M} [self : OneMemClass S M] (s : S), 1 ∈ s
· 使用定理 `AddSubmonoidWithOneClass.toOneMemClass`：∀ {S : Type u_1} {R : outParam (
Type u_2)} {inst : AddMonoidWithOne R} {inst_1 : SetLike S R}   [self : AddSubmo
noidWithOneClass S R], OneMe…
· 使用定理 `SubsemiringClass.addSubmonoidWithOneClass`：∀ (S : Type u_1) (R : Type u)
 {x : NonAssocSemiring R} [inst : SetLike S R] [h : SubsemiringClass S R],   Add
SubmonoidWithOneClass S R
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `algebraMap_mem`：∀ {S : Type u_1} {R : Type u_2} {A : Type u_3} [inst : C
ommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_3 : SetLike 
S A]…
· 使用定理 `Submodule.add_mem`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [inst
_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodule R M) {x y 
: M}, x…
· 使用定理 `Subalgebra.isIdempotentElem_toSubmodule`：isIdempotentElem_toSubmodule (S
 : Subalgebra R A) : IsIdempotentElem S.toSubmodule
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a

--- 原说明 ---
When `A` is commutative, `Subalgebra.mul_toSubmodule_le` is strict.
-/
theorem mul_toSubmodule {R : Type*} {A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
    (S T : Subalgebra R A) : (Subalgebra.toSubmodule S) * (Subalgebra.toSubmodule T)
        = Subalgebra.toSubmodule (S ⊔ T) := by
  refine le_antisymm (mul_toSubmodule_le _ _) ?_
  rintro x (hx : x ∈ Algebra.adjoin R (S ∪ T : Set A))
  refine
    Algebra.adjoin_induction (fun x hx => ?_) (fun r => ?_) (fun _ _ _ _ => Submodule.add_mem _)
      (fun x y _ _ hx hy => ?_) hx
  · rcases hx with hxS | hxT
    · rw [← mul_one x]
      exact Submodule.mul_mem_mul hxS (show (1 : A) ∈ T from one_mem T)
    · rw [← one_mul x]
      exact Submodule.mul_mem_mul (show (1 : A) ∈ S from one_mem S) hxT
  · rw [← one_mul (algebraMap _ _ _)]
    exact Submodule.mul_mem_mul (show (1 : A) ∈ S from one_mem S) (algebraMap_mem T _)
  have := Submodule.mul_mem_mul hx hy
  rwa [mul_assoc, mul_comm _ (Subalgebra.toSubmodule T), ← mul_assoc _ _ (Subalgebra.toSubmodule S),
    isIdempotentElem_toSubmodule, mul_comm T.toSubmodule, ← mul_assoc,
    isIdempotentElem_toSubmodule] at this

variable {R' : Type*} [Semiring R'] [MulSemiringAction R' A] [SMulCommClass R' R A]

/-- The action on a subalgebra corresponding to applying the action to every element.

This is available as an instance in the `Pointwise` locale. -/
@[instance_reducible]
/-
**Subalgebra.pointwiseMulAction** 是 Mathlib 中的一个定义，位于命名空间 `Subalgebra`。
形式化陈述：{R : Type u_1} →   {A : Type u_2} →     [inst : CommSemiring R] →       [i
nst_1 : Semiring A] →         [inst_2 : Algebra R A] →           {R' : Type u_3}
 →             [inst_3 : Semiring R'] →               [inst_4 : MulSemiringActio
n R' A] → [SMulCommClass R' R A] → MulAction R' (Subalgebra R A)
参数：Subalgebra R A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The action on a subalgebra corresponding to applying the action to every element
.

This is available as an instance in the `Pointwise` locale.
-/
protected def pointwiseMulAction : MulAction R' (Subalgebra R A) where
  smul a S := S.map (MulSemiringAction.toAlgHom _ _ a)
  one_smul S := (congr_arg (fun f => S.map f) (AlgHom.ext <| one_smul R')).trans S.map_id
  mul_smul _a₁ _a₂ S :=
    (congr_arg (fun f => S.map f) (AlgHom.ext <| mul_smul _ _)).trans (S.map_map _ _).symm

scoped[Pointwise] attribute [instance] Subalgebra.pointwiseMulAction

open scoped Pointwise

@[simp, norm_cast]
/-
**Subalgebra.coe_pointwise_smul** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：coe_pointwise_smul (m : R') (S : Subalgebra R A) : ↑(m • S) = m • (S : Set
 A)
参数：m : R'；S : Subalgebra R A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_pointwise_smul (m : R') (S : Subalgebra R A) : ↑(m • S) = m • (S : Set A) :=
  rfl

@[simp]
/-
**Subalgebra.pointwise_smul_toSubsemiring** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`
。
形式化陈述：pointwise_smul_toSubsemiring (m : R') (S : Subalgebra R A) : (m • S).toSub
semiring = m • S.toSubsemiring
参数：m : R'；S : Subalgebra R A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pointwise_smul_toSubsemiring (m : R') (S : Subalgebra R A) :
    (m • S).toSubsemiring = m • S.toSubsemiring :=
  rfl

@[simp]
/-
**Subalgebra.pointwise_smul_toSubmodule** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：pointwise_smul_toSubmodule (m : R') (S : Subalgebra R A) : Subalgebra.toSu
bmodule (m • S) = m • Subalgebra.toSubmodule S
参数：m : R'；S : Subalgebra R A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pointwise_smul_toSubmodule (m : R') (S : Subalgebra R A) :
    Subalgebra.toSubmodule (m • S) = m • Subalgebra.toSubmodule S :=
  rfl

@[simp]
/-
**Subalgebra.pointwise_smul_toSubring** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：pointwise_smul_toSubring {R' R A : Type*} [Semiring R'] [CommRing R] [Ring
 A] [MulSemiringAction R' A] [Algebra R A] [SMulCommClass R' R A] (m : R') (S : 
Subalgebra R A) : (m • S).toSubring = m • S.toSubring
参数：m : R'；S : Subalgebra R A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pointwise_smul_toSubring {R' R A : Type*} [Semiring R'] [CommRing R] [Ring A]
    [MulSemiringAction R' A] [Algebra R A] [SMulCommClass R' R A] (m : R') (S : Subalgebra R A) :
    (m • S).toSubring = m • S.toSubring :=
  rfl
/-
**Subalgebra.smul_mem_pointwise_smul** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：smul_mem_pointwise_smul (m : R') (r : A) (S : Subalgebra R A) : r in S -> 
m • r in m • S
参数：m : R'；r : A；S : Subalgebra R A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.smul_mem_smul_set`：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β]
 {s : Set β} {a : α} {b : β}, b ∈ s → a • b ∈ a • s
-/
theorem smul_mem_pointwise_smul (m : R') (r : A) (S : Subalgebra R A) : r ∈ S → m • r ∈ m • S :=
  (Set.smul_mem_smul_set : _ → _ ∈ m • (S : Set A))
/-
**Subalgebra.** 是 Mathlib 中的一个实例，位于命名空间 `Subalgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CovariantClass R' (Subalgebra R A) HSMul.hSMul LE.le :=
  ⟨fun _ _ => map_mono⟩

end Pointwise

end Subalgebra

