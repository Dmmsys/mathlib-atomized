/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Lie.IdealOperations

/-!
# Trivial Lie modules and Abelian Lie algebras

The action of a Lie algebra `L` on a module `M` is trivial if `⁅x, m⁆ = 0` for all `x ∈ L` and
`m ∈ M`. In the special case that `M = L` with the adjoint action, triviality corresponds to the
concept of an Abelian Lie algebra.

In this file we define these concepts and provide some related definitions and results.

## Main definitions

  * `LieModule.IsTrivial`
  * `IsLieAbelian`
  * `isMulCommutative_iff_isLieAbelian`
  * `LieModule.ker`
  * `LieModule.maxTrivSubmodule`
  * `LieAlgebra.center`

## Tags

lie algebra, abelian, commutative, center
-/

@[expose] public section


universe u v w w₁ w₂

/-- A Lie (ring) module is trivial iff all brackets vanish. -/
/-
**LieModule.IsTrivial** 是 Mathlib 中的一个归纳类型，位于命名空间 `LieModule`。
形式化陈述：(L : Type v) → (M : Type w) → [Bracket L M] → [Zero M] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A Lie (ring) module is trivial iff all brackets vanish.
-/
class LieModule.IsTrivial (L : Type v) (M : Type w) [Bracket L M] [Zero M] : Prop where
  trivial : ∀ (x : L) (m : M), ⁅x, m⁆ = 0
/-
**trivial_lie_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：trivial_lie_zero (L : Type v) (M : Type w) [Bracket L M] [Zero M] [LieModu
le.IsTrivial L M] (x : L) (m : M) : ⁅x, m⁆ = 0
参数：L : Type v；M : Type w；x : L；m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieModule.IsTrivial.trivial`：∀ {L : Type v} {M : Type w} {inst : Bracket
 L M} {inst_1 : Zero M} [self : LieModule.IsTrivial L M] (x : L) (m : M),   ⁅x, 
m⁆ = 0
-/
theorem trivial_lie_zero (L : Type v) (M : Type w) [Bracket L M] [Zero M] [LieModule.IsTrivial L M]
    (x : L) (m : M) : ⁅x, m⁆ = 0 :=
  LieModule.IsTrivial.trivial x m
/-
**LieModule.instIsTrivialOfSubsingleton** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：LieModule.instIsTrivialOfSubsingleton {L M : Type*} [LieRing L] [AddCommGr
oup M] [LieRingModule L M] [Subsingleton L] : LieModule.IsTrivial L M
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsingleton.eq_zero`：∀ {α : Type u} [inst : Zero α] [Subsingleton α] (a
 : α), a = 0
· 使用定理 `zero_lie`：zero_lie : ⁅(0 : L), m⁆ = 0
-/
instance LieModule.instIsTrivialOfSubsingleton {L M : Type*}
    [LieRing L] [AddCommGroup M] [LieRingModule L M] [Subsingleton L] : LieModule.IsTrivial L M :=
  ⟨fun x m ↦ by rw [Subsingleton.eq_zero x, zero_lie]⟩
/-
**LieModule.instIsTrivialOfSubsingleton'** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：LieModule.instIsTrivialOfSubsingleton' {L M : Type*} [LieRing L] [AddCommG
roup M] [LieRingModule L M] [Subsingleton M] : LieModule.IsTrivial L M
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsingleton.eq_zero`：∀ {α : Type u} [inst : Zero α] [Subsingleton α] (a
 : α), a = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `lie_zero`：lie_zero : ⁅x, 0⁆ = (0 : M)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance LieModule.instIsTrivialOfSubsingleton' {L M : Type*}
    [LieRing L] [AddCommGroup M] [LieRingModule L M] [Subsingleton M] : LieModule.IsTrivial L M :=
  ⟨fun x m ↦ by simp_rw [Subsingleton.eq_zero m, lie_zero]⟩

/-- A Lie algebra is Abelian iff it is trivial as a Lie module over itself. -/
/-
**IsLieAbelian** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：IsLieAbelian (L : Type v) [Bracket L L] [Zero L] : Prop
参数：L : Type v。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A Lie algebra is Abelian iff it is trivial as a Lie module over itself.
-/
abbrev IsLieAbelian (L : Type v) [Bracket L L] [Zero L] : Prop :=
  LieModule.IsTrivial L L
/-
**LieIdeal.isLieAbelian_of_trivial** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：LieIdeal.isLieAbelian_of_trivial (R : Type u) (L : Type v) [CommRing R] [L
ieRing L] [LieAlgebra R L] (I : LieIdeal R L) [h : LieModule.IsTrivial L I] : Is
LieAbelian I where trivial x y
参数：R : Type u；L : Type v；I : LieIdeal R L。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `LieModule.IsTrivial.trivial`：∀ {L : Type v} {M : Type w} {inst : Bracket
 L M} {inst_1 : Zero M} [self : LieModule.IsTrivial L M] (x : L) (m : M),   ⁅x, 
m⁆ = 0
-/
instance LieIdeal.isLieAbelian_of_trivial (R : Type u) (L : Type v) [CommRing R] [LieRing L]
    [LieAlgebra R L] (I : LieIdeal R L) [h : LieModule.IsTrivial L I] : IsLieAbelian I where
  trivial x y := by apply h.trivial
/-
**Function.Injective.isLieAbelian** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Function.Injective.isLieAbelian {R : Type u} {L₁ : Type v} {L₂ : Type w} [
CommRing R] [LieRing L₁] [LieRing L₂] [LieAlgebra R L₁] [LieAlgebra R L₂] {f : L
₁ ->ₗ⁅R⁆ L₂} (h₁ : Function.Injective f) (_ : IsLieAbelian L₂) : IsLieAbelian L₁
参数：h₁ : Function.Injective f；_ : IsLieAbelian L₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieHom.map_lie`：map_lie (f : L₁ ->ₗ⁅R⁆ L₂) (x y : L₁) : f ⁅x, y⁆ = ⁅f x,
 f y⁆
· 使用定理 `trivial_lie_zero`：trivial_lie_zero (L : Type v) (M : Type w) [Bracket L 
M] [Zero M] [LieModule.IsTrivial L M] (x : L) (m : M) : ⁅x, m⁆ = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
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
-/
theorem Function.Injective.isLieAbelian {R : Type u} {L₁ : Type v} {L₂ : Type w} [CommRing R]
    [LieRing L₁] [LieRing L₂] [LieAlgebra R L₁] [LieAlgebra R L₂] {f : L₁ →ₗ⁅R⁆ L₂}
    (h₁ : Function.Injective f) (_ : IsLieAbelian L₂) : IsLieAbelian L₁ :=
  { trivial := fun x y => h₁ <|
      calc
        f ⁅x, y⁆ = ⁅f x, f y⁆ := LieHom.map_lie f x y
        _ = 0 := trivial_lie_zero _ _ _ _
        _ = f 0 := (map_zero _).symm }
/-
**Function.Surjective.isLieAbelian** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Function.Surjective.isLieAbelian {R : Type u} {L₁ : Type v} {L₂ : Type w} 
[CommRing R] [LieRing L₁] [LieRing L₂] [LieAlgebra R L₁] [LieAlgebra R L₂] {f : 
L₁ ->ₗ⁅R⁆ L₂} (h₁ : Function.Surjective f) (h₂ : IsLieAbelian L₁) : IsLieAbelian
 L₂
参数：h₁ : Function.Surjective f；h₂ : IsLieAbelian L₁。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieHom.map_lie`：map_lie (f : L₁ ->ₗ⁅R⁆ L₂) (x y : L₁) : f ⁅x, y⁆ = ⁅f x,
 f y⁆
· 使用定理 `trivial_lie_zero`：trivial_lie_zero (L : Type v) (M : Type w) [Bracket L 
M] [Zero M] [LieModule.IsTrivial L M] (x : L) (m : M) : ⁅x, m⁆ = 0
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
-/
theorem Function.Surjective.isLieAbelian {R : Type u} {L₁ : Type v} {L₂ : Type w} [CommRing R]
    [LieRing L₁] [LieRing L₂] [LieAlgebra R L₁] [LieAlgebra R L₂] {f : L₁ →ₗ⁅R⁆ L₂}
    (h₁ : Function.Surjective f) (h₂ : IsLieAbelian L₁) : IsLieAbelian L₂ :=
  { trivial := fun x y => by
      obtain ⟨u, rfl⟩ := h₁ x
      obtain ⟨v, rfl⟩ := h₁ y
      rw [← LieHom.map_lie, trivial_lie_zero, map_zero] }
/-
**lie_abelian_iff_equiv_lie_abelian** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lie_abelian_iff_equiv_lie_abelian {R : Type u} {L₁ : Type v} {L₂ : Type w}
 [CommRing R] [LieRing L₁] [LieRing L₂] [LieAlgebra R L₁] [LieAlgebra R L₂] (e :
 L₁ ≃ₗ⁅R⁆ L₂) : IsLieAbelian L₁ ↔ IsLieAbelian L₂
参数：e : L₁ ≃ₗ⁅R⁆ L₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.isLieAbelian`：Function.Injective.isLieAbelian {R : Ty
pe u} {L₁ : Type v} {L₂ : Type w} [CommRing R] [LieRing L₁] [LieRing L₂] [LieAlg
ebra R L₁] [LieAlgebr…
· 使用定理 `LieEquiv.injective`：∀ {R : Type u} {L₁ : Type v} {L₂ : Type w} [inst : C
ommRing R] [inst_1 : LieRing L₁] [inst_2 : LieRing L₂]   [inst_3 : LieAlgebra R 
L₁] [ins…
-/
theorem lie_abelian_iff_equiv_lie_abelian {R : Type u} {L₁ : Type v} {L₂ : Type w} [CommRing R]
    [LieRing L₁] [LieRing L₂] [LieAlgebra R L₁] [LieAlgebra R L₂] (e : L₁ ≃ₗ⁅R⁆ L₂) :
    IsLieAbelian L₁ ↔ IsLieAbelian L₂ :=
  ⟨e.symm.injective.isLieAbelian, e.injective.isLieAbelian⟩
/-
**isMulCommutative_iff_isLieAbelian** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isMulCommutative_iff_isLieAbelian {A : Type v} [Ring A] : IsMulCommutative
 A ↔ IsLieAbelian A
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieModule.IsTrivial.trivial`：∀ {L : Type v} {M : Type w} {inst : Bracket
 L M} {inst_1 : Zero M} [self : LieModule.IsTrivial L M] (x : L) (m : M),   ⁅x, 
m⁆ = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isMulCommutative_iff_isLieAbelian {A : Type v} [Ring A] :
    IsMulCommutative A ↔ IsLieAbelian A := by
  have : IsLieAbelian A ↔ ∀ a b : A, ⁅a, b⁆ = 0 := ⟨(·.trivial), (⟨·⟩)⟩
  simp [this, isMulCommutative_iff, LieRing.of_associative_ring_bracket, sub_eq_zero]

@[deprecated (since := "2026-04-01")]
alias commutative_ring_iff_abelian_lie_ring := isMulCommutative_iff_isLieAbelian
/-
**LieSubalgebra.isLieAbelian_lieSpan_iff** 是 Mathlib 中的一个定理，位于命名空间 `LieSubalgebr
a`。
形式化陈述：∀ {R : Type u_1} {L : Type u_2} [inst : CommRing R] [inst_1 : LieRing L] [
inst_2 : LieAlgebra R L] {s : Set L},   IsLieAbelian ↥(LieSubalgebra.lieSpan R L
 s) ↔ ∀ x ∈ s, ∀ y ∈ s, ⁅x, y⁆ = 0
参数：LieSubalgebra.lieSpan R L s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `LieSubalgebra.instAddSubgroupClass`：∀ (R : Type u) (L : Type v) [inst : 
CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L],   AddSubgroupClass (
LieSubalgebra R L) L
· 使用定理 `LieSubalgebra.subset_lieSpan`：subset_lieSpan : s subseteq lieSpan R L s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `trivial_lie_zero`：trivial_lie_zero (L : Type v) (M : Type w) [Bracket L 
M] [Zero M] [LieModule.IsTrivial L M] (x : L) (m : M) : ⁅x, m⁆ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LieSubalgebra.lieSpan_induction`：lieSpan_induction {p : (x : L) -> x in 
lieSpan R L s -> Prop} (mem : forall (x) (h : x in s), p x (subset_lieSpan h)) (
zero : p 0 (LieSubalg…
· 使用定理 `LieSubalgebra.zero_mem`：∀ {R : Type u} {L : Type v} [inst : CommRing R] 
[inst_1 : LieRing L] [inst_2 : LieAlgebra R L] (L' : LieSubalgebra R L),   0 ∈ L
'
· 使用定理 `lie_zero`：lie_zero : ⁅x, 0⁆ = (0 : M)
· 使用定理 `LieSubalgebra.add_mem`：∀ {R : Type u} {L : Type v} [inst : CommRing R] [
inst_1 : LieRing L] [inst_2 : LieAlgebra R L] (L' : LieSubalgebra R L)   {x y : 
L}, x ∈ L' …
· 使用定理 `lie_add`：lie_add : ⁅x, m + n⁆ = ⁅x, m⁆ + ⁅x, n⁆
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `LieSubalgebra.smul_mem`：∀ {R : Type u} {L : Type v} [inst : CommRing R] 
[inst_1 : LieRing L] [inst_2 : LieAlgebra R L] (L' : LieSubalgebra R L)   (t : R
) {x : L}, x…
· 使用定理 `lie_smul`：lie_smul : ⁅x, t • m⁆ = t • ⁅x, m⁆
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `LieSubalgebra.lie_mem`：lie_mem {x y : L} (hx : x in L') (hy : y in L') :
 (⁅x, y⁆ : L) in L'
· 使用引理 `leibniz_lie`：leibniz_lie [Add M] [IsLieTower L₁ L₂ M] (x : L₁) (y : L₂) 
(m : M) : ⁅x, ⁅y, m⁆⁆ = ⁅⁅x, y⁆, m⁆ + ⁅y, ⁅x, m⁆⁆
· 使用定理 `instIsLieTower`：∀ {L : Type v} {M : Type w} [inst : LieRing L] [inst_1 :
 AddCommGroup M] [inst_2 : LieRingModule L M], IsLieTower L L M
· 使用定理 `zero_lie`：zero_lie : ⁅(0 : L), m⁆ = 0
· 使用定理 `add_lie`：add_lie : ⁅x + y, m⁆ = ⁅x, m⁆ + ⁅y, m⁆
· 使用定理 `smul_lie`：smul_lie : ⁅t • x, m⁆ = t • ⁅x, m⁆
· 使用引理 `lie_lie`：lie_lie : ⁅⁅x, y⁆, m⁆ = ⁅x, ⁅y, m⁆⁆ - ⁅y, ⁅x, m⁆⁆
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
-/
@[simp] theorem LieSubalgebra.isLieAbelian_lieSpan_iff
    {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] {s : Set L} :
    IsLieAbelian (lieSpan R L s) ↔ ∀ᵉ (x ∈ s) (y ∈ s), ⁅x, y⁆ = 0 := by
  refine ⟨fun h x hx y hy ↦ ?_, fun h ↦ ⟨fun ⟨x, hx⟩ ⟨y, hy⟩ ↦ ?_⟩⟩
  · let x' : lieSpan R L s := ⟨x, subset_lieSpan hx⟩
    let y' : lieSpan R L s := ⟨y, subset_lieSpan hy⟩
    suffices ⁅x', y'⁆ = 0 by simpa [x', y', Subtype.ext_iff] using this
    simp [trivial_lie_zero]
  · induction hx using lieSpan_induction with
    | mem w hw =>
      induction hy using lieSpan_induction with
      | mem u hu => simpa [Subtype.ext_iff] using h w hw u hu
      | zero => simp [Subtype.ext_iff]
      | add u v _ _ hu hv =>
        simp only [Subtype.ext_iff, coe_bracket, ZeroMemClass.coe_zero, lie_add] at hu hv ⊢
        simp [hu, hv]
      | smul t u _ hu =>
        simp only [Subtype.ext_iff, coe_bracket, ZeroMemClass.coe_zero] at hu
        simp [Subtype.ext_iff, hu]
      | lie u v _ _ hu hv =>
        simp only [Subtype.ext_iff, coe_bracket, ZeroMemClass.coe_zero] at hu hv ⊢
        rw [leibniz_lie]
        simp [hu, hv]
    | zero => simp [Subtype.ext_iff]
    | add u v _ _ hu hv =>
      simp only [Subtype.ext_iff, coe_bracket, ZeroMemClass.coe_zero, add_lie] at hu hv ⊢
      simp [hu, hv]
    | smul t u _ hu =>
      simp only [Subtype.ext_iff, coe_bracket, ZeroMemClass.coe_zero] at hu
      simp [Subtype.ext_iff, hu]
    | lie u v _ _ hu hv =>
      simp only [Subtype.ext_iff, coe_bracket, ZeroMemClass.coe_zero] at hu hv ⊢
      simp [hu, hv]

section Center

variable (R : Type u) (L : Type v) (M : Type w) (N : Type w₁)
variable [CommRing R] [LieRing L] [LieAlgebra R L]
variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
variable [AddCommGroup N] [Module R N] [LieRingModule L N] [LieModule R L N]

namespace LieModule

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The kernel of the action of a Lie algebra `L` on a Lie module `M` as a Lie ideal in `L`. -/
/-
**LieModule.ker** 是 Mathlib 中的一个定义，位于命名空间 `LieModule`。
形式化陈述：(R : Type u) →   (L : Type v) →     (M : Type w) →       [inst : CommRing 
R] →         [inst_1 : LieRing L] →           [inst_2 : LieAlgebra R L] →       
      [inst_3 : AddCommGroup M] →               [inst_4 : _root_.Module R M] → [
inst_5 : LieRingModule L M] → [LieModule R L M] → LieIdeal R L
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The kernel of the action of a Lie algebra `L` on a Lie module `M` as a Lie ideal
 in `L`.
-/
protected def ker : LieIdeal R L :=
  (toEnd R L M).ker

@[simp]
/-
**LieModule.mem_ker** 是 Mathlib 中的一个定理，位于命名空间 `LieModule`。
形式化陈述：∀ (R : Type u) (L : Type v) (M : Type w) [inst : CommRing R] [inst_1 : Lie
Ring L] [inst_2 : LieAlgebra R L]   [inst_3 : AddCommGroup M] [inst_4 : _root_.M
odule R M] [inst_5 : LieRingModule L M] [inst_6 : LieModule R L M]   (x : L), x 
∈ LieModule.ker R L M ↔ ∀ (m : M), ⁅x, m⁆ = 0
参数：R : Type u；L : Type v；M : Type w；x : L；m : M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `LieModule.toEnd_apply_apply`：∀ (R : Type u) (L : Type v) (M : Type w) [i
nst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 : Add
CommGroup M] [ins…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
protected theorem mem_ker (x : L) : x ∈ LieModule.ker R L M ↔ ∀ m : M, ⁅x, m⁆ = 0 := by
  simp only [LieModule.ker, LieHom.mem_ker, LinearMap.ext_iff, LinearMap.zero_apply,
    toEnd_apply_apply]
/-
**LieModule._root_.LieIdeal.isLieAbelian_iff** 是 Mathlib 中的一个引理，位于命名空间 `LieModul
e`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.LieIdeal.isLieAbelian_iff {I : LieIdeal R L} :
    IsLieAbelian I ↔ I ≤ LieModule.ker R L I := by
  refine ⟨fun hI x hx ↦ LieHom.mem_ker.mpr ?_, fun h ↦ ⟨fun ⟨x, hx⟩ ⟨y, hy⟩ ↦ ?_⟩⟩
  · ext y
    have := IsTrivial.trivial (⟨x, hx⟩ : I) y
    rw [LieIdeal.coe_bracket_of_module] at this
    simp [this]
  · simpa using LinearMap.congr_fun (h hx) ⟨y, hy⟩
/-
**LieModule.isFaithful_iff_ker_eq_bot** 是 Mathlib 中的一个引理，位于命名空间 `LieModule`。
形式化陈述：isFaithful_iff_ker_eq_bot : IsFaithful R L M ↔ LieModule.ker R L M = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LieModule.isFaithful_iff'`：isFaithful_iff' : IsFaithful R L M ↔ forall x
 : L, (forall m : M, ⁅x, m⁆ = 0) -> x = 0
· 使用定理 `LieSubmodule.ext_iff`：∀ {R : Type u} {L : Type v} {M : Type w} [inst : C
ommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3 : _root_.Mod
ule R M] […
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `zero_lie`：zero_lie : ⁅(0 : L), m⁆ = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma isFaithful_iff_ker_eq_bot : IsFaithful R L M ↔ LieModule.ker R L M = ⊥ := by
  rw [isFaithful_iff', LieSubmodule.ext_iff]
  aesop
/-
**LieModule.ker_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `LieModule`。
形式化陈述：∀ (R : Type u) (L : Type v) (M : Type w) [inst : CommRing R] [inst_1 : Lie
Ring L] [inst_2 : LieAlgebra R L]   [inst_3 : AddCommGroup M] [inst_4 : _root_.M
odule R M] [inst_5 : LieRingModule L M] [inst_6 : LieModule R L M]   [LieModule.
IsFaithful R L M], LieModule.ker R L M = ⊥
参数：R : Type u；L : Type v；M : Type w。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `LieModule.isFaithful_iff_ker_eq_bot`：isFaithful_iff_ker_eq_bot : IsFaith
ful R L M ↔ LieModule.ker R L M = ⊥
-/
@[simp] lemma ker_eq_bot [IsFaithful R L M] :
    LieModule.ker R L M = ⊥ :=
  (isFaithful_iff_ker_eq_bot R L M).mp inferInstance

/-- The largest submodule of a Lie module `M` on which the Lie algebra `L` acts trivially. -/
/-
**LieModule.maxTrivSubmodule** 是 Mathlib 中的一个定义，位于命名空间 `LieModule`。
形式化陈述：maxTrivSubmodule : LieSubmodule R L M where carrier
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `lie_zero`：lie_zero : ⁅x, 0⁆ = (0 : M)

--- 原说明 ---
The largest submodule of a Lie module `M` on which the Lie algebra `L` acts triv
ially.
-/
def maxTrivSubmodule : LieSubmodule R L M where
  carrier := { m | ∀ x : L, ⁅x, m⁆ = 0 }
  zero_mem' x := lie_zero x
  add_mem' {x y} hx hy z := by rw [lie_add, hx, hy, add_zero]
  smul_mem' c x hx y := by rw [lie_smul, hx, smul_zero]
  lie_mem {x m} hm y := by rw [hm, lie_zero]

@[simp]
/-
**LieModule.mem_maxTrivSubmodule** 是 Mathlib 中的一个定理，位于命名空间 `LieModule`。
形式化陈述：mem_maxTrivSubmodule (m : M) : m in maxTrivSubmodule R L M ↔ forall x : L,
 ⁅x, m⁆ = 0
参数：m : M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_maxTrivSubmodule (m : M) : m ∈ maxTrivSubmodule R L M ↔ ∀ x : L, ⁅x, m⁆ = 0 :=
  Iff.rfl
/-
**LieModule.** 是 Mathlib 中的一个实例，位于命名空间 `LieModule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsTrivial L (maxTrivSubmodule R L M) where trivial x m := Subtype.ext (m.property x)

@[simp]
/-
**LieModule.ideal_oper_maxTrivSubmodule_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `LieMod
ule`。
形式化陈述：ideal_oper_maxTrivSubmodule_eq_bot (I : LieIdeal R L) : ⁅I, maxTrivSubmodu
le R L M⁆ = ⊥
参数：I : LieIdeal R L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieSubmodule.toSubmodule_inj`：toSubmodule_inj : (N : Submodule R M) = (N
' : Submodule R M) ↔ N = N'
· 使用定理 `LieSubmodule.lieIdeal_oper_eq_linear_span`：lieIdeal_oper_eq_linear_span 
[LieModule R L M] : (↑⁅I, N⁆ : Submodule R M) = Submodule.span R { ⁅(x : L), (n 
: M)⁆ | (x : I) (n : N) }
· 使用定理 `LieSubmodule.bot_toSubmodule`：bot_toSubmodule : ((⊥ : LieSubmodule R L M
) : Submodule R M) = ⊥
· 使用定理 `Submodule.span_eq_bot`：span_eq_bot : span R (s : Set M) = ⊥ ↔ forall x i
n s, (x : M) = 0
-/
theorem ideal_oper_maxTrivSubmodule_eq_bot (I : LieIdeal R L) :
    ⁅I, maxTrivSubmodule R L M⁆ = ⊥ := by
  rw [← LieSubmodule.toSubmodule_inj, LieSubmodule.lieIdeal_oper_eq_linear_span,
    LieSubmodule.bot_toSubmodule, Submodule.span_eq_bot]
  rintro m ⟨⟨x, hx⟩, ⟨⟨m, hm⟩, rfl⟩⟩
  exact hm x
/-
**LieModule.le_max_triv_iff_bracket_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `LieModule`
。
形式化陈述：le_max_triv_iff_bracket_eq_bot {N : LieSubmodule R L M} : N <= maxTrivSubm
odule R L M ↔ ⁅(⊤ : LieIdeal R L), N⁆ = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `le_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ ↔ a = ⊥
· 使用定理 `LieModule.ideal_oper_maxTrivSubmodule_eq_bot`：ideal_oper_maxTrivSubmodul
e_eq_bot (I : LieIdeal R L) : ⁅I, maxTrivSubmodule R L M⁆ = ⊥
· 使用定理 `LieSubmodule.mono_lie_right`：mono_lie_right (h : N <= N') : ⁅I, N⁆ <= ⁅I
, N'⁆
· 使用定理 `LieModule.mem_maxTrivSubmodule`：mem_maxTrivSubmodule (m : M) : m in maxT
rivSubmodule R L M ↔ forall x : L, ⁅x, m⁆ = 0
· 使用定理 `LieSubmodule.lie_eq_bot_iff`：lie_eq_bot_iff : ⁅I, N⁆ = ⊥ ↔ forall x in I
, forall m in N, ⁅(x : L), m⁆ = 0
· 使用定理 `LieSubmodule.mem_top`：mem_top (x : M) : x in (⊤ : LieSubmodule R L M)
-/
theorem le_max_triv_iff_bracket_eq_bot {N : LieSubmodule R L M} :
    N ≤ maxTrivSubmodule R L M ↔ ⁅(⊤ : LieIdeal R L), N⁆ = ⊥ := by
  refine ⟨fun h => ?_, fun h m hm => ?_⟩
  · rw [← le_bot_iff, ← ideal_oper_maxTrivSubmodule_eq_bot R L M ⊤]
    exact LieSubmodule.mono_lie_right ⊤ h
  · rw [mem_maxTrivSubmodule]
    rw [LieSubmodule.lie_eq_bot_iff] at h
    exact fun x => h x (LieSubmodule.mem_top x) m hm
/-
**LieModule.trivial_iff_le_maximal_trivial** 是 Mathlib 中的一个定理，位于命名空间 `LieModule`
。
形式化陈述：trivial_iff_le_maximal_trivial (N : LieSubmodule R L M) : IsTrivial L N ↔ 
N <= maxTrivSubmodule R L M
参数：N : LieSubmodule R L M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem trivial_iff_le_maximal_trivial (N : LieSubmodule R L M) :
    IsTrivial L N ↔ N ≤ maxTrivSubmodule R L M :=
  ⟨fun h m hm x => IsTrivial.casesOn h fun h => Subtype.ext_iff.mp (h x ⟨m, hm⟩), fun h =>
    { trivial := fun x m => Subtype.ext (h m.2 x) }⟩
/-
**LieModule.isTrivial_iff_max_triv_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `LieModule`。
形式化陈述：isTrivial_iff_max_triv_eq_top : IsTrivial L M ↔ maxTrivSubmodule R L M = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubmodule.ext`：ext (h : forall m, m in N ↔ m in N') : N = N'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieModule.mem_maxTrivSubmodule`：mem_maxTrivSubmodule (m : M) : m in maxT
rivSubmodule R L M ↔ forall x : L, ⁅x, m⁆ = 0
· 使用定理 `LieSubmodule.mem_top`：mem_top (x : M) : x in (⊤ : LieSubmodule R L M)
-/
theorem isTrivial_iff_max_triv_eq_top : IsTrivial L M ↔ maxTrivSubmodule R L M = ⊤ := by
  constructor
  · rintro ⟨h⟩; ext; simp only [mem_maxTrivSubmodule, h, forall_const, LieSubmodule.mem_top]
  · intro h; constructor; intro x m; revert x
    rw [← mem_maxTrivSubmodule R L M, h]; exact LieSubmodule.mem_top m

variable {R L M N}

set_option backward.isDefEq.respectTransparency false in
/-- `maxTrivSubmodule` is functorial. -/
/-
**LieModule.maxTrivHom** 是 Mathlib 中的一个定义，位于命名空间 `LieModule`。
形式化陈述：maxTrivHom (f : M ->ₗ⁅R,L⁆ N) : maxTrivSubmodule R L M ->ₗ⁅R,L⁆ maxTrivSub
module R L N where toFun m
参数：f : M ->ₗ⁅R,L⁆ N。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […

--- 原说明 ---
`maxTrivSubmodule` is functorial.
-/
def maxTrivHom (f : M →ₗ⁅R,L⁆ N) : maxTrivSubmodule R L M →ₗ⁅R,L⁆ maxTrivSubmodule R L N where
  toFun m := ⟨f m, fun x =>
    (LieModuleHom.map_lie _ _ _).symm.trans <|
      (congr_arg f (m.property x)).trans (map_zero _)⟩
  map_add' m n := by ext; simp
  map_smul' t m := by ext; simp
  map_lie' {x m} := by simp [trivial_lie_zero]

@[norm_cast, simp]
/-
**LieModule.coe_maxTrivHom_apply** 是 Mathlib 中的一个定理，位于命名空间 `LieModule`。
形式化陈述：coe_maxTrivHom_apply (f : M ->ₗ⁅R,L⁆ N) (m : maxTrivSubmodule R L M) : (ma
xTrivHom f m : N) = f m
参数：f : M ->ₗ⁅R,L⁆ N；m : maxTrivSubmodule R L M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
-/
theorem coe_maxTrivHom_apply (f : M →ₗ⁅R,L⁆ N) (m : maxTrivSubmodule R L M) :
    (maxTrivHom f m : N) = f m :=
  rfl

/-- The maximal trivial submodules of Lie-equivalent Lie modules are Lie-equivalent. -/
/-
**LieModule.maxTrivEquiv** 是 Mathlib 中的一个定义，位于命名空间 `LieModule`。
形式化陈述：maxTrivEquiv (e : M ≃ₗ⁅R,L⁆ N) : maxTrivSubmodule R L M ≃ₗ⁅R,L⁆ maxTrivSub
module R L N
参数：e : M ≃ₗ⁅R,L⁆ N。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […

--- 原说明 ---
The maximal trivial submodules of Lie-equivalent Lie modules are Lie-equivalent.
-/
def maxTrivEquiv (e : M ≃ₗ⁅R,L⁆ N) : maxTrivSubmodule R L M ≃ₗ⁅R,L⁆ maxTrivSubmodule R L N :=
  { maxTrivHom (e : M →ₗ⁅R,L⁆ N) with
    toFun := maxTrivHom (e : M →ₗ⁅R,L⁆ N)
    invFun := maxTrivHom (e.symm : N →ₗ⁅R,L⁆ M)
    left_inv := fun m => by ext; simp
    right_inv := fun n => by ext; simp }

@[norm_cast, simp]
/-
**LieModule.coe_maxTrivEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `LieModule`。
形式化陈述：coe_maxTrivEquiv_apply (e : M ≃ₗ⁅R,L⁆ N) (m : maxTrivSubmodule R L M) : (m
axTrivEquiv e m : N) = e ↑m
参数：e : M ≃ₗ⁅R,L⁆ N；m : maxTrivSubmodule R L M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
-/
theorem coe_maxTrivEquiv_apply (e : M ≃ₗ⁅R,L⁆ N) (m : maxTrivSubmodule R L M) :
    (maxTrivEquiv e m : N) = e ↑m :=
  rfl

@[simp]
/-
**LieModule.maxTrivEquiv_of_refl_eq_refl** 是 Mathlib 中的一个定理，位于命名空间 `LieModule`。
形式化陈述：maxTrivEquiv_of_refl_eq_refl : maxTrivEquiv (LieModuleEquiv.refl : M ≃ₗ⁅R,
L⁆ M) = LieModuleEquiv.refl
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieModuleEquiv.ext`：ext (e₁ e₂ : M ≃ₗ⁅R,L⁆ N) (h : forall m, e₁ m = e₂ m
) : e₁ = e₂
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem maxTrivEquiv_of_refl_eq_refl :
    maxTrivEquiv (LieModuleEquiv.refl : M ≃ₗ⁅R,L⁆ M) = LieModuleEquiv.refl := by
  ext; simp only [coe_maxTrivEquiv_apply, LieModuleEquiv.refl_apply]

@[simp]
/-
**LieModule.maxTrivEquiv_of_equiv_symm_eq_symm** 是 Mathlib 中的一个定理，位于命名空间 `LieMod
ule`。
形式化陈述：maxTrivEquiv_of_equiv_symm_eq_symm (e : M ≃ₗ⁅R,L⁆ N) : (maxTrivEquiv e).sy
mm = maxTrivEquiv e.symm
参数：e : M ≃ₗ⁅R,L⁆ N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
-/
theorem maxTrivEquiv_of_equiv_symm_eq_symm (e : M ≃ₗ⁅R,L⁆ N) :
    (maxTrivEquiv e).symm = maxTrivEquiv e.symm :=
  rfl

/-- A linear map between two Lie modules is a morphism of Lie modules iff the Lie algebra action
on it is trivial. -/
/-
**LieModule.maxTrivLinearMapEquivLieModuleHom** 是 Mathlib 中的一个定义，位于命名空间 `LieModu
le`。
形式化陈述：maxTrivLinearMapEquivLieModuleHom : maxTrivSubmodule R L (M ->ₗ[R] N) ≃ₗ[R
] M ->ₗ⁅R,L⁆ N where toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A linear map between two Lie modules is a morphism of Lie modules iff the Lie al
gebra action
on it is trivial.
-/
def maxTrivLinearMapEquivLieModuleHom : maxTrivSubmodule R L (M →ₗ[R] N) ≃ₗ[R] M →ₗ⁅R,L⁆ N where
  toFun f :=
    { toLinearMap := f.val
      map_lie' := fun {x m} => by
        have hf : ⁅x, f.val⁆ m = 0 := by rw [f.property x, LinearMap.zero_apply]
        rw [LieHom.lie_apply, sub_eq_zero, ← LinearMap.toFun_eq_coe] at hf; exact hf.symm }
  map_add' f g := by ext; simp
  map_smul' F G := by ext; simp
  invFun F := ⟨F, fun x => by ext; simp⟩
  left_inv f := by simp
  right_inv F := by simp

@[simp]
/-
**LieModule.coe_maxTrivLinearMapEquivLieModuleHom** 是 Mathlib 中的一个定理，位于命名空间 `Lie
Module`。
形式化陈述：coe_maxTrivLinearMapEquivLieModuleHom (f : maxTrivSubmodule R L (M ->ₗ[R] 
N)) : (maxTrivLinearMapEquivLieModuleHom (M
参数：f : maxTrivSubmodule R L (M ->ₗ[R] N)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
-/
theorem coe_maxTrivLinearMapEquivLieModuleHom (f : maxTrivSubmodule R L (M →ₗ[R] N)) :
    (maxTrivLinearMapEquivLieModuleHom (M := M) (N := N) f : M → N) = f := by ext; rfl

@[simp]
/-
**LieModule.coe_maxTrivLinearMapEquivLieModuleHom_symm** 是 Mathlib 中的一个定理，位于命名空间
 `LieModule`。
形式化陈述：coe_maxTrivLinearMapEquivLieModuleHom_symm (f : M ->ₗ⁅R,L⁆ N) : (maxTrivLi
nearMapEquivLieModuleHom (M
参数：f : M ->ₗ⁅R,L⁆ N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
-/
theorem coe_maxTrivLinearMapEquivLieModuleHom_symm (f : M →ₗ⁅R,L⁆ N) :
    (maxTrivLinearMapEquivLieModuleHom (M := M) (N := N) |>.symm f : M → N) = f :=
  rfl

@[simp]
/-
**LieModule.toLinearMap_maxTrivLinearMapEquivLieModuleHom** 是 Mathlib 中的一个定理，位于命
名空间 `LieModule`。
形式化陈述：toLinearMap_maxTrivLinearMapEquivLieModuleHom (f : maxTrivSubmodule R L (M
 ->ₗ[R] N)) : (maxTrivLinearMapEquivLieModuleHom (M
参数：f : maxTrivSubmodule R L (M ->ₗ[R] N)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
-/
theorem toLinearMap_maxTrivLinearMapEquivLieModuleHom (f : maxTrivSubmodule R L (M →ₗ[R] N)) :
    (maxTrivLinearMapEquivLieModuleHom (M := M) (N := N) f : M →ₗ[R] N) = (f : M →ₗ[R] N) := by
  ext; rfl

@[simp]
/-
**LieModule.toLinearMap_maxTrivLinearMapEquivLieModuleHom_symm** 是 Mathlib 中的一个定
理，位于命名空间 `LieModule`。
形式化陈述：toLinearMap_maxTrivLinearMapEquivLieModuleHom_symm (f : M ->ₗ⁅R,L⁆ N) : (m
axTrivLinearMapEquivLieModuleHom (M
参数：f : M ->ₗ⁅R,L⁆ N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
-/
theorem toLinearMap_maxTrivLinearMapEquivLieModuleHom_symm (f : M →ₗ⁅R,L⁆ N) :
    (maxTrivLinearMapEquivLieModuleHom (M := M) (N := N) |>.symm f : M →ₗ[R] N) = (f : M →ₗ[R] N) :=
  rfl

end LieModule

namespace LieAlgebra

/-- The center of a Lie algebra is the set of elements that commute with everything. It can
be viewed as the maximal trivial submodule of the Lie algebra as a Lie module over itself via the
adjoint representation. -/
/-
**LieAlgebra.center** 是 Mathlib 中的一个缩写定义，位于命名空间 `LieAlgebra`。
形式化陈述：center : LieIdeal R L
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The center of a Lie algebra is the set of elements that commute with everything.
 It can
be viewed as the maximal trivial submodule of the Lie algebra as a Lie module ov
er itself via the
adjoint representation.
-/
abbrev center : LieIdeal R L :=
  LieModule.maxTrivSubmodule R L L
/-
**LieAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `LieAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsLieAbelian (center R L) :=
  inferInstance

attribute [local instance 100] LieRing.ofAssociativeRing

@[simp]
/-
**LieAlgebra.ad_ker_eq_self_module_ker** 是 Mathlib 中的一个定理，位于命名空间 `LieAlgebra`。
形式化陈述：ad_ker_eq_self_module_ker : (ad R L).ker = LieModule.ker R L L
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ad_ker_eq_self_module_ker : (ad R L).ker = LieModule.ker R L L :=
  rfl

@[simp]
/-
**LieAlgebra.self_module_ker_eq_center** 是 Mathlib 中的一个定理，位于命名空间 `LieAlgebra`。
形式化陈述：self_module_ker_eq_center : LieModule.ker R L L = center R L
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubmodule.ext`：ext (h : forall m, m in N ↔ m in N') : N = N'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `lie_skew`：lie_skew : -⁅y, x⁆ = ⁅x, y⁆
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem self_module_ker_eq_center : LieModule.ker R L L = center R L := by
  ext y
  simp only [LieModule.mem_maxTrivSubmodule, LieModule.mem_ker, ← lie_skew _ y, neg_eq_zero]
/-
**LieAlgebra.abelian_of_le_center** 是 Mathlib 中的一个定理，位于命名空间 `LieAlgebra`。
形式化陈述：abelian_of_le_center (I : LieIdeal R L) (h : I <= center R L) : IsLieAbeli
an I
参数：I : LieIdeal R L；h : I <= center R L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `LieModule.trivial_iff_le_maximal_trivial`：trivial_iff_le_maximal_trivial
 (N : LieSubmodule R L M) : IsTrivial L N ↔ N <= maxTrivSubmodule R L M
-/
theorem abelian_of_le_center (I : LieIdeal R L) (h : I ≤ center R L) : IsLieAbelian I :=
  haveI : LieModule.IsTrivial L I := (LieModule.trivial_iff_le_maximal_trivial R L L I).mpr h
  LieIdeal.isLieAbelian_of_trivial R L I
/-
**LieAlgebra.isLieAbelian_iff_center_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `LieAlgebr
a`。
形式化陈述：isLieAbelian_iff_center_eq_top : IsLieAbelian L ↔ center R L = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieModule.isTrivial_iff_max_triv_eq_top`：isTrivial_iff_max_triv_eq_top :
 IsTrivial L M ↔ maxTrivSubmodule R L M = ⊤
-/
theorem isLieAbelian_iff_center_eq_top : IsLieAbelian L ↔ center R L = ⊤ :=
  LieModule.isTrivial_iff_max_triv_eq_top R L L
/-
**LieAlgebra.isFaithful_self_iff** 是 Mathlib 中的一个定理，位于命名空间 `LieAlgebra`。
形式化陈述：isFaithful_self_iff : LieModule.IsFaithful R L L ↔ center R L = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LieModule.isFaithful_iff_ker_eq_bot`：isFaithful_iff_ker_eq_bot : IsFaith
ful R L M ↔ LieModule.ker R L M = ⊥
· 使用定理 `LieAlgebra.self_module_ker_eq_center`：self_module_ker_eq_center : LieMod
ule.ker R L L = center R L
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isFaithful_self_iff : LieModule.IsFaithful R L L ↔ center R L = ⊥ := by
  rw [LieModule.isFaithful_iff_ker_eq_bot, self_module_ker_eq_center]

@[simp]
/-
**LieAlgebra.center_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `LieAlgebra`。
形式化陈述：center_eq_bot [LieModule.IsFaithful R L L] : center R L = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LieAlgebra.isFaithful_self_iff`：isFaithful_self_iff : LieModule.IsFaithf
ul R L L ↔ center R L = ⊥
-/
theorem center_eq_bot [LieModule.IsFaithful R L L] :
    center R L = ⊥ :=
  (isFaithful_self_iff R L).mp inferInstance

end LieAlgebra

namespace LieModule

variable {R L}
variable {x : L} (hx : x ∈ LieAlgebra.center R L) (y : L)
include hx

attribute [local instance 100] LieRing.ofAssociativeRing

/-
**LieModule.commute_toEnd_of_mem_center_left** 是 Mathlib 中的一个引理，位于命名空间 `LieModul
e`。
形式化陈述：commute_toEnd_of_mem_center_left : Commute (toEnd R L M x) (toEnd R L M y)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Commute.symm_iff`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b
 ↔ Commute b a
· 使用定理 `commute_iff_lie_eq`：commute_iff_lie_eq {x y : R} : Commute x y ↔ ⁅x, y⁆ 
= 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieHom.map_lie`：map_lie (f : L₁ ->ₗ⁅R⁆ L₂) (x y : L₁) : f ⁅x, y⁆ = ⁅f x,
 f y⁆
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
-/
lemma commute_toEnd_of_mem_center_left :
    Commute (toEnd R L M x) (toEnd R L M y) := by
  rw [Commute.symm_iff, commute_iff_lie_eq, ← LieHom.map_lie, hx y, map_zero]
/-
**LieModule.commute_toEnd_of_mem_center_right** 是 Mathlib 中的一个引理，位于命名空间 `LieModu
le`。
形式化陈述：commute_toEnd_of_mem_center_right : Commute (toEnd R L M y) (toEnd R L M x
)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Commute.symm`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → C
ommute b a
· 使用引理 `LieModule.commute_toEnd_of_mem_center_left`：commute_toEnd_of_mem_center_
left : Commute (toEnd R L M x) (toEnd R L M y)
-/
lemma commute_toEnd_of_mem_center_right :
    Commute (toEnd R L M y) (toEnd R L M x) :=
  (LieModule.commute_toEnd_of_mem_center_left M hx y).symm

end LieModule

end Center

section IdealOperations

open LieSubmodule LieSubalgebra

variable {R : Type u} {L : Type v} {M : Type w}
variable [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M]
variable [LieRingModule L M] (N N' : LieSubmodule R L M) (I J : LieIdeal R L)

@[simp]
/-
**LieSubmodule.trivial_lie_oper_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LieSubmodule.trivial_lie_oper_zero [LieModule.IsTrivial L M] : ⁅I, N⁆ = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieSubmodule.lieIdeal_oper_eq_span`：lieIdeal_oper_eq_span : ⁅I, N⁆ = lie
Span R L { ⁅(x : L), (n : M)⁆ | (x : I) (n : N) }
· 使用定理 `LieSubmodule.lieSpan_le`：lieSpan_le {N} : lieSpan R L s <= N ↔ s subsete
q N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `trivial_lie_zero`：trivial_lie_zero (L : Type v) (M : Type w) [Bracket L 
M] [Zero M] [LieModule.IsTrivial L M] (x : L) (m : M) : ⁅x, m⁆ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `le_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ ↔ a = ⊥
-/
theorem LieSubmodule.trivial_lie_oper_zero [LieModule.IsTrivial L M] : ⁅I, N⁆ = ⊥ := by
  suffices ⁅I, N⁆ ≤ ⊥ from le_bot_iff.mp this
  rw [lieIdeal_oper_eq_span, LieSubmodule.lieSpan_le]
  rintro m ⟨x, n, h⟩; rw [trivial_lie_zero] at h; simp [← h]
/-
**LieSubmodule.lie_abelian_iff_lie_self_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LieSubmodule.lie_abelian_iff_lie_self_eq_bot : IsLieAbelian I ↔ ⁅I, I⁆ = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieSubalgebra.coe_bracket`：coe_bracket (x y : L') : (↑⁅x, y⁆ : L) = ⁅(↑x
 : L), ↑y⁆
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LieSubalgebra.instAddSubgroupClass`：∀ (R : Type u) (L : Type v) [inst : 
CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L],   AddSubgroupClass (
LieSubalgebra R L) L
· 使用定理 `LieSubalgebra.coe_zero_iff_zero`：coe_zero_iff_zero (x : L') : (x : L) = 
0 ↔ x = 0
· 使用定理 `LieModule.IsTrivial.trivial`：∀ {L : Type v} {M : Type w} {inst : Bracket
 L M} {inst_1 : Zero M} [self : LieModule.IsTrivial L M] (x : L) (m : M),   ⁅x, 
m⁆ = 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem LieSubmodule.lie_abelian_iff_lie_self_eq_bot : IsLieAbelian I ↔ ⁅I, I⁆ = ⊥ := by
  simp only [_root_.eq_bot_iff, lieIdeal_oper_eq_span, LieSubmodule.lieSpan_le,
    LieSubmodule.bot_coe, Set.subset_singleton_iff, Set.mem_ofPred_eq, exists_imp]
  refine
    ⟨fun h z x y hz =>
      hz.symm.trans
        (((I : LieSubalgebra R L).coe_bracket x y).symm.trans
          ((coe_zero_iff_zero _ _).mpr (by apply h.trivial))),
      fun h => ⟨fun x y => ((I : LieSubalgebra R L).coe_zero_iff_zero _).mp (h _ x y rfl)⟩⟩

variable {I N} in
/-
**lie_eq_self_of_isAtom_of_ne_bot** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：lie_eq_self_of_isAtom_of_ne_bot (hN : IsAtom N) (h : ⁅I, N⁆ != ⊥) : ⁅I, N⁆
 = N
参数：hN : IsAtom N；h : ⁅I, N⁆ != ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `IsAtom.le_iff_eq`：IsAtom.le_iff_eq (ha : IsAtom a) (hb : b != ⊥) : b <= 
a ↔ b = a
· 使用定理 `LieSubmodule.lie_le_right`：lie_le_right : ⁅I, N⁆ <= N
-/
lemma lie_eq_self_of_isAtom_of_ne_bot (hN : IsAtom N) (h : ⁅I, N⁆ ≠ ⊥) : ⁅I, N⁆ = N :=
  (hN.le_iff_eq h).mp <| LieSubmodule.lie_le_right N I

-- TODO: introduce typeclass for perfect Lie algebras and use it here in the conclusion
/-
**lie_eq_self_of_isAtom_of_nonabelian** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：lie_eq_self_of_isAtom_of_nonabelian {R L : Type*} [CommRing R] [LieRing L]
 [LieAlgebra R L] (I : LieIdeal R L) (hI : IsAtom I) (h : ¬IsLieAbelian I) : ⁅I,
 I⁆ = I
参数：I : LieIdeal R L；hI : IsAtom I；h : ¬IsLieAbelian I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用引理 `lie_eq_self_of_isAtom_of_ne_bot`：lie_eq_self_of_isAtom_of_ne_bot (hN : I
sAtom N) (h : ⁅I, N⁆ != ⊥) : ⁅I, N⁆ = N
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_imp_not`：not_imp_not : ¬a -> ¬b ↔ b -> a
· 使用定理 `LieSubmodule.lie_abelian_iff_lie_self_eq_bot`：LieSubmodule.lie_abelian_i
ff_lie_self_eq_bot : IsLieAbelian I ↔ ⁅I, I⁆ = ⊥
-/
lemma lie_eq_self_of_isAtom_of_nonabelian {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
    (I : LieIdeal R L) (hI : IsAtom I) (h : ¬IsLieAbelian I) :
    ⁅I, I⁆ = I :=
  lie_eq_self_of_isAtom_of_ne_bot hI <| not_imp_not.mpr (lie_abelian_iff_lie_self_eq_bot I).mpr h

end IdealOperations

section TrivialLieModule

set_option linter.unusedVariables false in
/-- A type synonym for an `R`-module to have a trivial Lie module structure. -/
@[nolint unusedArguments]
/-
**TrivialLieModule** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：TrivialLieModule (R L M : Type*)
参数：R L M : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A type synonym for an `R`-module to have a trivial Lie module structure.
-/
def TrivialLieModule (R L M : Type*) := M

namespace TrivialLieModule

variable (R L M : Type*) [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M]

/-
**TrivialLieModule.** 是 Mathlib 中的一个实例，位于命名空间 `TrivialLieModule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddCommGroup (TrivialLieModule R L M) := inferInstanceAs (AddCommGroup M)
/-
**TrivialLieModule.** 是 Mathlib 中的一个实例，位于命名空间 `TrivialLieModule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Module R (TrivialLieModule R L M) := inferInstanceAs (Module R M)

/-- The linear equivalence between a trivial Lie module and its underlying `R`-module. -/
/-
**TrivialLieModule.equiv** 是 Mathlib 中的一个定义，位于命名空间 `TrivialLieModule`。
形式化陈述：equiv : (TrivialLieModule R L M) ≃ₗ[R] M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The linear equivalence between a trivial Lie module and its underlying `R`-modul
e.
-/
def equiv : (TrivialLieModule R L M) ≃ₗ[R] M := LinearEquiv.refl R M
/-
**TrivialLieModule.** 是 Mathlib 中的一个实例，位于命名空间 `TrivialLieModule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LieRingModule L (TrivialLieModule R L M) where
  bracket x m := 0
  add_lie := by simp
  lie_add := by simp
  leibniz_lie := by simp
/-
**TrivialLieModule.** 是 Mathlib 中的一个实例，位于命名空间 `TrivialLieModule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LieModule.IsTrivial L (TrivialLieModule R L M) where
  trivial _ _ := rfl
/-
**TrivialLieModule.** 是 Mathlib 中的一个实例，位于命名空间 `TrivialLieModule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LieModule R L (TrivialLieModule R L M) where
  smul_lie := by simp [trivial_lie_zero]
  lie_smul := by simp [trivial_lie_zero]

end TrivialLieModule

end TrivialLieModule

