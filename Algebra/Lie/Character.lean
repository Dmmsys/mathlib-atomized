/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.Lie.Abelian
public import Mathlib.Algebra.Lie.Solvable
public import Mathlib.LinearAlgebra.Dual.Defs

/-!
# Characters of Lie algebras

A character of a Lie algebra `L` over a commutative ring `R` is a morphism of Lie algebras `L → R`,
where `R` is regarded as a Lie algebra over itself via the ring commutator. For an Abelian Lie
algebra (e.g., a Cartan subalgebra of a semisimple Lie algebra) a character is just a linear form.

## Main definitions

  * `LieAlgebra.LieCharacter`
  * `LieAlgebra.lieCharacterEquivLinearDual`

## Tags

lie algebra, lie character
-/

@[expose] public section


universe u v w w₁

namespace LieAlgebra

variable (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L]
attribute [local instance 100] LieRing.ofAssociativeRing

/-- A character of a Lie algebra is a morphism to the scalars. -/
/-
**LieAlgebra.LieCharacter** 是 Mathlib 中的一个缩写定义，位于命名空间 `LieAlgebra`。
形式化陈述：LieCharacter
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A character of a Lie algebra is a morphism to the scalars.
-/
abbrev LieCharacter :=
  L →ₗ⁅R⁆ R

variable {R L}
/-
**LieAlgebra.lieCharacter_apply_lie** 是 Mathlib 中的一个定理，位于命名空间 `LieAlgebra`。
形式化陈述：lieCharacter_apply_lie (χ : LieCharacter R L) (x y : L) : χ ⁅x, y⁆ = 0
参数：χ : LieCharacter R L；x y : L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieHom.map_lie`：map_lie (f : L₁ ->ₗ⁅R⁆ L₂) (x y : L₁) : f ⁅x, y⁆ = ⁅f x,
 f y⁆
· 使用定理 `LieRing.of_associative_ring_bracket`：of_associative_ring_bracket (x y : 
A) : ⁅x, y⁆ = x * y - y * x
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
-/
theorem lieCharacter_apply_lie (χ : LieCharacter R L) (x y : L) : χ ⁅x, y⁆ = 0 := by
  rw [LieHom.map_lie, LieRing.of_associative_ring_bracket, mul_comm, sub_self]

@[simp]
/-
**LieAlgebra.lieCharacter_apply_lie'** 是 Mathlib 中的一个定理，位于命名空间 `LieAlgebra`。
形式化陈述：lieCharacter_apply_lie' (χ : LieCharacter R L) (x y : L) : ⁅χ x, χ y⁆ = 0
参数：χ : LieCharacter R L；x y : L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieRing.of_associative_ring_bracket`：of_associative_ring_bracket (x y : 
A) : ⁅x, y⁆ = x * y - y * x
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
-/
theorem lieCharacter_apply_lie' (χ : LieCharacter R L) (x y : L) : ⁅χ x, χ y⁆ = 0 := by
  rw [LieRing.of_associative_ring_bracket, mul_comm, sub_self]
/-
**LieAlgebra.lieCharacter_apply_of_mem_derived** 是 Mathlib 中的一个定理，位于命名空间 `LieAlg
ebra`。
形式化陈述：lieCharacter_apply_of_mem_derived (χ : LieCharacter R L) {x : L} (h : x in
 derivedSeries R L 1) : χ x = 0
参数：χ : LieCharacter R L；h : x in derivedSeries R L 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.span_induction`：span_induction {p : (x : M) -> x in span R s -
> Prop} (mem : forall (x) (h : x in s), p x (subset_span h)) (zero : p 0 (Submod
ule.zero_mem _…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `LieAlgebra.lieCharacter_apply_lie`：lieCharacter_apply_lie (χ : LieCharac
ter R L) (x y : L) : χ ⁅x, y⁆ = 0
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
· 使用定理 `LieHom.instLinearMapClass`：∀ {R : Type u} {L₁ : Type v} {L₂ : Type w} [i
nst : CommRing R] [inst_1 : LieRing L₁] [inst_2 : LieAlgebra R L₁]   [inst_3 : L
ieRing L₂] [ins…
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `LieSubmodule.lieIdeal_oper_eq_linear_span`：lieIdeal_oper_eq_linear_span 
[LieModule R L M] : (↑⁅I, N⁆ : Submodule R M) = Submodule.span R { ⁅(x : L), (n 
: M)⁆ | (x : I) (n : N) }
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieSubmodule.mem_toSubmodule`：mem_toSubmodule {x : M} : x in (N : Submod
ule R M) ↔ x in N
· 使用定理 `LieAlgebra.derivedSeriesOfIdeal_zero`：derivedSeriesOfIdeal_zero : derive
dSeriesOfIdeal R L 0 I = I
· 使用定理 `LieAlgebra.derivedSeriesOfIdeal_succ`：derivedSeriesOfIdeal_succ (k : Nat
) : derivedSeriesOfIdeal R L (k + 1) I = ⁅derivedSeriesOfIdeal R L k I, derivedS
eriesOfIdeal R L k I⁆
· 使用定理 `LieAlgebra.derivedSeries_def`：derivedSeries_def (k : Nat) : derivedSerie
s R L k = derivedSeriesOfIdeal R L k ⊤
-/
theorem lieCharacter_apply_of_mem_derived (χ : LieCharacter R L) {x : L}
    (h : x ∈ derivedSeries R L 1) : χ x = 0 := by
  rw [derivedSeries_def, derivedSeriesOfIdeal_succ, derivedSeriesOfIdeal_zero, ←
    LieSubmodule.mem_toSubmodule, LieSubmodule.lieIdeal_oper_eq_linear_span] at h
  induction h using Submodule.span_induction with
  | mem y h =>
    simp only [Subtype.exists, LieSubmodule.mem_top, exists_const, Set.mem_ofPred_eq] at h
    obtain ⟨z, w, rfl⟩ := h
    exact lieCharacter_apply_lie ..
  | zero => exact map_zero _
  | add y z _ _ hy hz => rw [map_add, hy, hz, add_zero]
  | smul t y _ hy => rw [map_smul, hy, smul_zero]

/-- For an Abelian Lie algebra, characters are just linear forms. -/
@[simps! apply symm_apply]
/-
**LieAlgebra.lieCharacterEquivLinearDual** 是 Mathlib 中的一个定义，位于命名空间 `LieAlgebra`。
形式化陈述：lieCharacterEquivLinearDual [IsLieAbelian L] : LieCharacter R L ≃ Module.D
ual R L where toFun χ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For an Abelian Lie algebra, characters are just linear forms.
-/
def lieCharacterEquivLinearDual [IsLieAbelian L] : LieCharacter R L ≃ Module.Dual R L where
  toFun χ := (χ : L →ₗ[R] R)
  invFun ψ :=
    { ψ with
      map_lie' := fun {x y} => by
        rw [LieModule.IsTrivial.trivial, LieRing.of_associative_ring_bracket, mul_comm, sub_self,
          LinearMap.toFun_eq_coe, map_zero] }

end LieAlgebra

