/-
Copyright (c) 2022 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
module

public import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!

# Projective Spaces

This file contains the definition of the projectivization of a vector space over a field,
as well as the bijection between said projectivization and the collection of all one
dimensional subspaces of the vector space.

## Notation
`ℙ K V` is localized notation for `Projectivization K V`, the projectivization of a `K`-vector
space `V`.

## Constructing terms of `ℙ K V`.
We have three ways to construct terms of `ℙ K V`:
- `Projectivization.mk K v hv` where `v : V` and `hv : v ≠ 0`.
- `Projectivization.mk' K v` where `v : { w : V // w ≠ 0 }`.
- `Projectivization.mk'' H h` where `H : Submodule K V` and `h : finrank H = 1`.

## Other definitions
- For `v : ℙ K V`, `v.submodule` gives the corresponding submodule of `V`.
- `Projectivization.equivSubmodule` is the equivalence between `ℙ K V`
  and `{ H : Submodule K V // finrank H = 1 }`.
- For `v : ℙ K V`, `v.rep : V` is a representative of `v`.

-/

@[expose] public section

variable (K V : Type*) [DivisionRing K] [AddCommGroup V] [Module K V]

/-- The setoid whose quotient is the projectivization of `V`. -/
@[instance_reducible]
/-
**projectivizationSetoid** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：projectivizationSetoid : Setoid { v : V // v != 0 }
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The setoid whose quotient is the projectivization of `V`.
-/
def projectivizationSetoid : Setoid { v : V // v ≠ 0 } :=
  (MulAction.orbitRel Kˣ V).comap (↑)

/-- The projectivization of the `K`-vector space `V`.
The notation `ℙ K V` is preferred. -/
/-
**Projectivization** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Projectivization
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The projectivization of the `K`-vector space `V`.
The notation `ℙ K V` is preferred.
-/
def Projectivization := Quotient (projectivizationSetoid K V)

/-- We define notations `ℙ K V` for the projectivization of the `K`-vector space `V`. -/
scoped[LinearAlgebra.Projectivization] notation "ℙ" => Projectivization

namespace Projectivization

open scoped LinearAlgebra.Projectivization

variable {V}

/-- Construct an element of the projectivization from a nonzero vector. -/
/-
**Projectivization.mk** 是 Mathlib 中的一个定义，位于命名空间 `Projectivization`。
形式化陈述：mk (v : V) (hv : v != 0) : ℙ K V
参数：v : V；hv : v != 0。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)

--- 原说明 ---
Construct an element of the projectivization from a nonzero vector.
-/
def mk (v : V) (hv : v ≠ 0) : ℙ K V :=
  Quotient.mk'' ⟨v, hv⟩

/-- A variant of `Projectivization.mk` in terms of a subtype. `mk` is preferred. -/
/-
**Projectivization.mk'** 是 Mathlib 中的一个定义，位于命名空间 `Projectivization`。
形式化陈述：mk' (v : { v : V // v != 0 }) : ℙ K V
参数：v : { v : V // v != 0 }。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)

--- 原说明 ---
A variant of `Projectivization.mk` in terms of a subtype. `mk` is preferred.
-/
def mk' (v : { v : V // v ≠ 0 }) : ℙ K V :=
  Quotient.mk'' v

@[simp]
/-
**Projectivization.mk'_eq_mk** 是 Mathlib 中的一个定理，位于命名空间 `Projectivization`。
形式化陈述：∀ (K : Type u_1) {V : Type u_2} [inst : DivisionRing K] [inst_1 : AddCommG
roup V] [inst_2 : _root_.Module K V]   (v : { v // v ≠ 0 }), Projectivization.mk
' K v = Projectivization.mk K ↑v ⋯
参数：K : Type u_1；v : { v // v ≠ 0 }。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk'_eq_mk (v : { v : V // v ≠ 0 }) : mk' K v = mk K ↑v v.2 := rfl
/-
**Projectivization.** 是 Mathlib 中的一个实例，位于命名空间 `Projectivization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Nontrivial V] : Nonempty (ℙ K V) :=
  let ⟨v, hv⟩ := exists_ne (0 : V)
  ⟨mk K v hv⟩

variable {K}

/-- A function on non-zero vectors which is independent of scale, descends to a function on the
projectivization. -/
/-
**Projectivization.lift** 是 Mathlib 中的一个定义，位于命名空间 `Projectivization`。
形式化陈述：{K : Type u_1} →   {V : Type u_2} →     [inst : DivisionRing K] →       [i
nst_1 : AddCommGroup V] →         [inst_2 : _root_.Module K V] →           {α : 
Type u_3} →             (f : { v // v ≠ 0 } → α) →               (∀ (a b : { v /
/ v ≠ 0 }) (t : K), ↑a = t • ↑b → f a = f b) → Projectivization K V → α
参数：f : { v // v ≠ 0 } → α；∀ (a b : { v // v ≠ 0 }) (t : K), ↑a = t • ↑b → f a = 
f b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function on non-zero vectors which is independent of scale, descends to a func
tion on the
projectivization.
-/
protected def lift {α : Type*} (f : { v : V // v ≠ 0 } → α)
    (hf : ∀ (a b : { v : V // v ≠ 0 }) (t : K), a = t • (b : V) → f a = f b)
    (x : ℙ K V) : α :=
  Quotient.lift f (by rintro ⟨-, hv⟩ ⟨w, hw⟩ ⟨⟨t, -⟩, rfl⟩; exact hf ⟨_, hv⟩ ⟨w, hw⟩ t rfl) x

@[simp]
/-
**Projectivization.lift_mk** 是 Mathlib 中的一个定理，位于命名空间 `Projectivization`。
形式化陈述：∀ {K : Type u_1} {V : Type u_2} [inst : DivisionRing K] [inst_1 : AddCommG
roup V] [inst_2 : _root_.Module K V]   {α : Type u_3} (f : { v // v ≠ 0 } → α) (
hf : ∀ (a b : { v // v ≠ 0 }) (t : K), ↑a = t • ↑b → f a = f b) (v : V)   (hv : 
v ≠ 0), Projectivization.lift f hf (Projectivization.mk K v hv) = f ⟨v, hv⟩
参数：f : { v // v ≠ 0 } → α；hf : ∀ (a b : { v // v ≠ 0 }) (t : K), ↑a = t • ↑b → f
 a = f b；v : V；hv : v ≠ 0；Projectivization.mk K v hv。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected lemma lift_mk {α : Type*} (f : { v : V // v ≠ 0 } → α)
    (hf : ∀ (a b : { v : V // v ≠ 0 }) (t : K), a = t • (b : V) → f a = f b)
    (v : V) (hv : v ≠ 0) :
    Projectivization.lift f hf (mk K v hv) = f ⟨v, hv⟩ :=
  rfl

/-- Choose a representative of `v : Projectivization K V` in `V`. -/
/-
**Projectivization.rep** 是 Mathlib 中的一个定义，位于命名空间 `Projectivization`。
形式化陈述：{K : Type u_1} →   {V : Type u_2} →     [inst : DivisionRing K] → [inst_1 
: AddCommGroup V] → [inst_2 : _root_.Module K V] → Projectivization K V → V
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Choose a representative of `v : Projectivization K V` in `V`.
-/
protected noncomputable def rep (v : ℙ K V) : V :=
  v.out
/-
**Projectivization.rep_nonzero** 是 Mathlib 中的一个定理，位于命名空间 `Projectivization`。
形式化陈述：rep_nonzero (v : ℙ K V) : v.rep != 0
参数：v : ℙ K V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem rep_nonzero (v : ℙ K V) : v.rep ≠ 0 :=
  v.out.2

@[simp]
/-
**Projectivization.mk_rep** 是 Mathlib 中的一个定理，位于命名空间 `Projectivization`。
形式化陈述：mk_rep (v : ℙ K V) : mk K v.rep v.rep_nonzero = v
参数：v : ℙ K V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.out_eq'`：out_eq' (q : Quotient s₁) : Quotient.mk'' q.out = q
-/
theorem mk_rep (v : ℙ K V) : mk K v.rep v.rep_nonzero = v := Quotient.out_eq' _

open Module

/-- Consider an element of the projectivization as a submodule of `V`. -/
/-
**Projectivization.submodule** 是 Mathlib 中的一个定义，位于命名空间 `Projectivization`。
形式化陈述：{K : Type u_1} →   {V : Type u_2} →     [inst : DivisionRing K] →       [i
nst_1 : AddCommGroup V] → [inst_2 : _root_.Module K V] → Projectivization K V → 
Submodule K V
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Consider an element of the projectivization as a submodule of `V`.
-/
protected def submodule (v : ℙ K V) : Submodule K V :=
  (Quotient.liftOn' v fun v => K ∙ (v : V)) <| by
    rintro ⟨a, ha⟩ ⟨b, hb⟩ ⟨x, rfl : x • b = a⟩
    exact Submodule.span_singleton_group_smul_eq _ x _

variable (K)
/-
**Projectivization.mk_eq_mk_iff** 是 Mathlib 中的一个定理，位于命名空间 `Projectivization`。
形式化陈述：mk_eq_mk_iff (v w : V) (hv : v != 0) (hw : w != 0) : mk K v hv = mk K w hw
 ↔ exists a : Kˣ, a • w = v
参数：v w : V；hv : v != 0；hw : w != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.eq''`：∀ {α : Sort u_1} {s₁ : Setoid α} {a b : α}, Quotient.mk''
 a = Quotient.mk'' b ↔ s₁ a b
-/
theorem mk_eq_mk_iff (v w : V) (hv : v ≠ 0) (hw : w ≠ 0) :
    mk K v hv = mk K w hw ↔ ∃ a : Kˣ, a • w = v :=
  Quotient.eq''

/-- Two nonzero vectors go to the same point in projective space if and only if one is
a scalar multiple of the other. -/
/-
**Projectivization.mk_eq_mk_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Projectivization`。
形式化陈述：mk_eq_mk_iff' (v w : V) (hv : v != 0) (hw : w != 0) : mk K v hv = mk K w h
w ↔ exists a : K, a • w = v
参数：v w : V；hv : v != 0；hw : w != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Projectivization.mk_eq_mk_iff`：mk_eq_mk_iff (v w : V) (hv : v != 0) (hw 
: w != 0) : mk K v hv = mk K w hw ↔ exists a : Kˣ, a • w = v
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0

--- 原说明 ---
Two nonzero vectors go to the same point in projective space if and only if one 
is
a scalar multiple of the other.
-/
theorem mk_eq_mk_iff' (v w : V) (hv : v ≠ 0) (hw : w ≠ 0) :
    mk K v hv = mk K w hw ↔ ∃ a : K, a • w = v := by
  rw [mk_eq_mk_iff K v w hv hw]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, ha⟩
  · rintro ⟨a, ha⟩
    refine ⟨Units.mk0 a fun c => hv.symm ?_, ha⟩
    rwa [c, zero_smul] at ha
/-
**Projectivization.exists_smul_eq_mk_rep** 是 Mathlib 中的一个定理，位于命名空间 `Projectiviza
tion`。
形式化陈述：exists_smul_eq_mk_rep (v : V) (hv : v != 0) : exists a : Kˣ, a • v = (mk K
 v hv).rep
参数：v : V；hv : v != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Projectivization.rep_nonzero`：rep_nonzero (v : ℙ K V) : v.rep != 0
· 使用定理 `Projectivization.mk_eq_mk_iff`：mk_eq_mk_iff (v w : V) (hv : v != 0) (hw 
: w != 0) : mk K v hv = mk K w hw ↔ exists a : Kˣ, a • w = v
· 使用定理 `Projectivization.mk_rep`：mk_rep (v : ℙ K V) : mk K v.rep v.rep_nonzero =
 v
-/
theorem exists_smul_eq_mk_rep (v : V) (hv : v ≠ 0) : ∃ a : Kˣ, a • v = (mk K v hv).rep :=
  (mk_eq_mk_iff K _ _ (rep_nonzero _) hv).1 (mk_rep _)

variable {K}

/-- An induction principle for `Projectivization`. Use as `induction v`. -/
@[elab_as_elim, cases_eliminator, induction_eliminator]
/-
**Projectivization.ind** 是 Mathlib 中的一个定理，位于命名空间 `Projectivization`。
形式化陈述：ind {P : ℙ K V -> Prop} (h : forall (v : V) (h : v != 0), P (mk K v h)) : 
forall p, P p
参数：h : forall (v : V) (h : v != 0), P (mk K v h)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.ind'`：∀ {α : Sort u_1} {s₁ : Setoid α} {p : Quotient s₁ → Prop}
, (∀ (a : α), p (Quotient.mk'' a)) → ∀ (q : Quotient s₁), p q
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)

--- 原说明 ---
An induction principle for `Projectivization`. Use as `induction v`.
-/
theorem ind {P : ℙ K V → Prop} (h : ∀ (v : V) (h : v ≠ 0), P (mk K v h)) : ∀ p, P p :=
  Quotient.ind' <| Subtype.rec <| h

@[simp]
/-
**Projectivization.submodule_mk** 是 Mathlib 中的一个定理，位于命名空间 `Projectivization`。
形式化陈述：submodule_mk (v : V) (hv : v != 0) : (mk K v hv).submodule = K ∙ v
参数：v : V；hv : v != 0。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem submodule_mk (v : V) (hv : v ≠ 0) : (mk K v hv).submodule = K ∙ v :=
  rfl
/-
**Projectivization.submodule_eq** 是 Mathlib 中的一个定理，位于命名空间 `Projectivization`。
形式化陈述：submodule_eq (v : ℙ K V) : v.submodule = K ∙ v.rep
参数：v : ℙ K V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Projectivization.rep_nonzero`：rep_nonzero (v : ℙ K V) : v.rep != 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Projectivization.mk_rep`：mk_rep (v : ℙ K V) : mk K v.rep v.rep_nonzero =
 v
-/
theorem submodule_eq (v : ℙ K V) : v.submodule = K ∙ v.rep := by
  conv_lhs => rw [← v.mk_rep]
  rfl
/-
**Projectivization.finrank_submodule** 是 Mathlib 中的一个定理，位于命名空间 `Projectivization
`。
形式化陈述：finrank_submodule (v : ℙ K V) : finrank K v.submodule = 1
参数：v : ℙ K V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Projectivization.submodule_eq`：submodule_eq (v : ℙ K V) : v.submodule = 
K ∙ v.rep
· 使用定理 `finrank_span_singleton`：finrank_span_singleton {v : V} (hv : v != 0) : f
inrank K (K ∙ v) = 1
· 使用定理 `Projectivization.rep_nonzero`：rep_nonzero (v : ℙ K V) : v.rep != 0
-/
theorem finrank_submodule (v : ℙ K V) : finrank K v.submodule = 1 := by
  rw [submodule_eq]
  exact finrank_span_singleton v.rep_nonzero
/-
**Projectivization.** 是 Mathlib 中的一个实例，位于命名空间 `Projectivization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (v : ℙ K V) : FiniteDimensional K v.submodule := by
  rw [← v.mk_rep]
  change FiniteDimensional K (K ∙ v.rep)
  infer_instance
/-
**Projectivization.submodule_injective** 是 Mathlib 中的一个定理，位于命名空间 `Projectivizati
on`。
形式化陈述：submodule_injective : Function.Injective (Projectivization.submodule : ℙ K
 V -> Submodule K V)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Projectivization.ind`：ind {P : ℙ K V -> Prop} (h : forall (v : V) (h : v
 != 0), P (mk K v h)) : forall p, P p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Projectivization.mk_eq_mk_iff`：mk_eq_mk_iff (v w : V) (hv : v != 0) (hw 
: w != 0) : mk K v hv = mk K w hw ↔ exists a : Kˣ, a • w = v
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.span_singleton_eq_span_singleton`：span_singleton_eq_span_singl
eton {R M : Type*} [Ring R] [IsDomain R] [AddCommGroup M] [Module R M] [Module.I
sTorsionFree R M] {x y : M} : (R…
· 使用定理 `DivisionRing.isDomain`：∀ {K : Type u_1} [inst : DivisionRing K], IsDomai
n K
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `Projectivization.submodule_mk`：submodule_mk (v : V) (hv : v != 0) : (mk 
K v hv).submodule = K ∙ v
-/
theorem submodule_injective :
    Function.Injective (Projectivization.submodule : ℙ K V → Submodule K V) := fun u v h ↦ by
  induction u using ind with | h u hu =>
  induction v using ind with | h v hv =>
  rw [submodule_mk, submodule_mk, Submodule.span_singleton_eq_span_singleton] at h
  exact ((mk_eq_mk_iff K v u hv hu).2 h).symm

variable (K V)

/-- The equivalence between the projectivization and the
collection of subspaces of dimension 1. -/
/-
**Projectivization.equivSubmodule** 是 Mathlib 中的一个定义，位于命名空间 `Projectivization`。
形式化陈述：equivSubmodule : ℙ K V ≃ { H : Submodule K V // finrank K H = 1 }
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Projectivization.submodule_injective`：submodule_injective : Function.Inj
ective (Projectivization.submodule : ℙ K V -> Submodule K V)
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
The equivalence between the projectivization and the
collection of subspaces of dimension 1.
-/
noncomputable def equivSubmodule : ℙ K V ≃ { H : Submodule K V // finrank K H = 1 } :=
  (Equiv.ofInjective _ submodule_injective).trans <| .subtypeEquiv (.refl _) fun H ↦ by
    refine ⟨fun ⟨v, hv⟩ ↦ hv ▸ v.finrank_submodule, fun h ↦ ?_⟩
    rcases finrank_eq_one_iff'.1 h with ⟨v : H, hv₀, hv : ∀ w : H, _⟩
    use mk K (v : V) (Subtype.coe_injective.ne hv₀)
    rw [submodule_mk, SetLike.ext'_iff, Submodule.span_singleton_eq_range]
    refine (Set.range_subset_iff.2 fun _ ↦ H.smul_mem _ v.2).antisymm fun x hx ↦ ?_
    rcases hv ⟨x, hx⟩ with ⟨c, hc⟩
    exact ⟨c, congr_arg Subtype.val hc⟩

variable {K V}

/-- Construct an element of the projectivization from a subspace of dimension 1. -/
/-
**Projectivization.mk''** 是 Mathlib 中的一个定义，位于命名空间 `Projectivization`。
形式化陈述：mk'' (H : Submodule K V) (h : finrank K H = 1) : ℙ K V
参数：H : Submodule K V；h : finrank K H = 1。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Construct an element of the projectivization from a subspace of dimension 1.
-/
noncomputable def mk'' (H : Submodule K V) (h : finrank K H = 1) : ℙ K V :=
  (equivSubmodule K V).symm ⟨H, h⟩

@[simp]
/-
**Projectivization.submodule_mk''** 是 Mathlib 中的一个定理，位于命名空间 `Projectivization`。
形式化陈述：submodule_mk'' (H : Submodule K V) (h : finrank K H = 1) : (mk'' H h).subm
odule = H
参数：H : Submodule K V；h : finrank K H = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
-/
theorem submodule_mk'' (H : Submodule K V) (h : finrank K H = 1) : (mk'' H h).submodule = H :=
  congr_arg Subtype.val <| (equivSubmodule K V).apply_symm_apply ⟨H, h⟩

@[simp]
/-
**Projectivization.mk''_submodule** 是 Mathlib 中的一个定理，位于命名空间 `Projectivization`。
形式化陈述：∀ {K : Type u_1} {V : Type u_2} [inst : DivisionRing K] [inst_1 : AddCommG
roup V] [inst_2 : _root_.Module K V]   (v : Projectivization K V), Projectivizat
ion.mk'' v.submodule ⋯ = v
参数：v : Projectivization K V。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
-/
theorem mk''_submodule (v : ℙ K V) : mk'' v.submodule v.finrank_submodule = v :=
  (equivSubmodule K V).symm_apply_apply v

section Map

variable {L W : Type*} [DivisionRing L] [AddCommGroup W] [Module L W]

/-- An injective semilinear map of vector spaces induces a map on projective spaces. -/
/-
**Projectivization.map** 是 Mathlib 中的一个定义，位于命名空间 `Projectivization`。
形式化陈述：map {σ : K ->+* L} (f : V ->ₛₗ[σ] W) (hf : Function.Injective f) : ℙ K V -
> ℙ L W
参数：f : V ->ₛₗ[σ] W；hf : Function.Injective f。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.map'`：map'_mk'' (f : α -> β) (h) (x : α) : (Quotient.mk'' x : Q
uotient s₁).map' f h = (Quotient.mk'' (f x) : Quotient s₂)

--- 原说明 ---
An injective semilinear map of vector spaces induces a map on projective spaces.
-/
def map {σ : K →+* L} (f : V →ₛₗ[σ] W) (hf : Function.Injective f) : ℙ K V → ℙ L W :=
  Quotient.map' (fun v => ⟨f v, fun c => v.2 (hf (by simp [c]))⟩)
    (by
      rintro ⟨u, hu⟩ ⟨v, hv⟩ ⟨a, ha⟩
      use Units.map σ.toMonoidHom a
      dsimp at ha ⊢
      simp [f.map_smulₛₗ, ← ha, Units.smul_def])
/-
**Projectivization.map_mk** 是 Mathlib 中的一个定理，位于命名空间 `Projectivization`。
形式化陈述：map_mk {σ : K ->+* L} (f : V ->ₛₗ[σ] W) (hf : Function.Injective f) (v : V
) (hv : v != 0) : map f hf (mk K v hv) = mk L (f v) (map_zero f ▸ hf.ne hv)
参数：f : V ->ₛₗ[σ] W；hf : Function.Injective f；v : V；hv : v != 0。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_mk {σ : K →+* L} (f : V →ₛₗ[σ] W) (hf : Function.Injective f) (v : V) (hv : v ≠ 0) :
    map f hf (mk K v hv) = mk L (f v) (map_zero f ▸ hf.ne hv) :=
  rfl

/-- Mapping with respect to a semilinear map over an isomorphism of fields yields
an injective map on projective spaces. -/
/-
**Projectivization.map_injective** 是 Mathlib 中的一个定理，位于命名空间 `Projectivization`。
形式化陈述：map_injective {σ : K ->+* L} {τ : L ->+* K} [RingHomInvPair σ τ] (f : V ->
ₛₗ[σ] W) (hf : Function.Injective f) : Function.Injective (map f hf)
参数：f : V ->ₛₗ[σ] W；hf : Function.Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Projectivization.ind`：ind {P : ℙ K V -> Prop} (h : forall (v : V) (h : v
 != 0), P (mk K v h)) : forall p, P p
· 使用定理 `Function.Injective.ne`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Func
tion.Injective f → ∀ {a₁ a₂ : α}, a₁ ≠ a₂ → f a₁ ≠ f a₂
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.map_smulₛₗ`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃
 : Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst…
· 使用定理 `RingHomInvPair.comp_apply_eq₂`：comp_apply_eq₂ {x : R₂} : σ (σ' x) = x

--- 原说明 ---
Mapping with respect to a semilinear map over an isomorphism of fields yields
an injective map on projective spaces.
-/
theorem map_injective {σ : K →+* L} {τ : L →+* K} [RingHomInvPair σ τ] (f : V →ₛₗ[σ] W)
    (hf : Function.Injective f) : Function.Injective (map f hf) := fun u v h ↦ by
  induction u using ind with | h u hu => induction v using ind with | h v hv =>
  simp only [map_mk, mk_eq_mk_iff'] at h ⊢
  rcases h with ⟨a, ha⟩
  refine ⟨τ a, hf ?_⟩
  rwa [f.map_smulₛₗ, RingHomInvPair.comp_apply_eq₂]

@[simp]
/-
**Projectivization.map_id** 是 Mathlib 中的一个定理，位于命名空间 `Projectivization`。
形式化陈述：map_id : map (LinearMap.id : V ->ₗ[K] V) (LinearEquiv.refl K V).injective 
= id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
-/
theorem map_id : map (LinearMap.id : V →ₗ[K] V) (LinearEquiv.refl K V).injective = id := by
  ext ⟨v⟩
  rfl

@[simp]
/-
**Projectivization.map_comp** 是 Mathlib 中的一个定理，位于命名空间 `Projectivization`。
形式化陈述：map_comp {F U : Type*} [DivisionRing F] [AddCommGroup U] [Module F U] {σ :
 K ->+* L} {τ : L ->+* F} {γ : K ->+* F} [RingHomCompTriple σ τ γ] (f : V ->ₛₗ[σ
] W) (hf : Function.Injective f) (g : W ->ₛₗ[τ] U) (hg : Function.Injective g) (
hgf : Function.Injective (g.comp f)
参数：f : V ->ₛₗ[σ] W；hf : Function.Injective f；g : W ->ₛₗ[τ] U；hg : Function.Injec
tive g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem map_comp {F U : Type*} [DivisionRing F] [AddCommGroup U] [Module F U] {σ : K →+* L}
    {τ : L →+* F} {γ : K →+* F} [RingHomCompTriple σ τ γ] (f : V →ₛₗ[σ] W)
    (hf : Function.Injective f) (g : W →ₛₗ[τ] U) (hg : Function.Injective g)
    (hgf : Function.Injective (g.comp f) := hg.comp hf) :
    map (g.comp f) hgf = map g hg ∘ map f hf := by
  ext ⟨v⟩
  rfl

end Map

section linearIndependent

/-
**Projectivization.linearIndependent_pair_iff_ne** 是 Mathlib 中的一个定理，位于命名空间 `Proj
ectivization`。
形式化陈述：linearIndependent_pair_iff_ne {D D' : ℙ K V} : LinearIndependent K ![D.rep
, D'.rep] ↔ D != D'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearIndependent.pair_iff'`：LinearIndependent.pair_iff' {x y : V} (hx :
 x != 0) : LinearIndependent K ![x, y] ↔ forall a : K, a • x != y
· 使用定理 `Projectivization.rep_nonzero`：rep_nonzero (v : ℙ K V) : v.rep != 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Projectivization.mk_rep`：mk_rep (v : ℙ K V) : mk K v.rep v.rep_nonzero =
 v
· 使用定理 `Projectivization.mk_eq_mk_iff`：mk_eq_mk_iff (v w : V) (hv : v != 0) (hw 
: w != 0) : mk K v hv = mk K w hw ↔ exists a : Kˣ, a • w = v
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `Ne.isUnit`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 →
 IsUnit a
-/
theorem linearIndependent_pair_iff_ne {D D' : ℙ K V} :
  LinearIndependent K ![D.rep, D'.rep] ↔ D ≠ D' := by
    rw [LinearIndependent.pair_iff' (rep_nonzero _)]
    refine ⟨fun h hD ↦ h 1 (by simp [hD]), fun h a hD ↦ h ?_⟩
    rw [eq_comm, ← mk_rep D, ← mk_rep D', mk_eq_mk_iff]
    suffices a ≠ 0 by refine ⟨(Ne.isUnit this).unit, by simp [← hD]⟩
    exact fun ha ↦ D'.rep_nonzero (by simp [← hD, ha])
/-
**Projectivization.linearIndepOn_pair** 是 Mathlib 中的一个定理，位于命名空间 `Projectivizatio
n`。
形式化陈述：linearIndepOn_pair (D D' : ℙ K V) : LinearIndepOn K id {D.rep, D'.rep}
参数：D D' : ℙ K V。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.insert_eq_of_mem`：insert_eq_of_mem {a : α} {s : Set α} (h : a in s) 
: insert a s = s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `DivisionRing.isDomain`：∀ {K : Type u_1} [inst : DivisionRing K], IsDomai
n K
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `Projectivization.rep_nonzero`：rep_nonzero (v : ℙ K V) : v.rep != 0
· 使用定理 `Matrix.range_cons`：range_cons (x : α) (u : Fin n -> α) : Set.range (vecC
ons x u) = {x} union Set.range u
· 使用定理 `Matrix.range_empty`：range_empty (u : Fin 0 -> α) : Set.range u = ∅
· 使用定理 `Set.union_empty`：union_empty (a : Set α) : a union ∅ = a
· 使用定理 `Set.union_singleton`：union_singleton : s union {a} = insert a s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `linearIndepOn_id_range_iff`：linearIndepOn_id_range_iff {ι} {f : ι -> M} 
(hf : Injective f) : LinearIndepOn R id (range f) ↔ LinearIndependent R f
· 使用定理 `LinearIndependent.injective`：LinearIndependent.injective [Nontrivial R] 
(hv : LinearIndependent R v) : Injective v
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用引理 `LinearIndependent.pair_symm_iff`：LinearIndependent.pair_symm_iff : Linea
rIndependent R ![x, y] ↔ LinearIndependent R ![y, x]
· 使用定理 `Projectivization.linearIndependent_pair_iff_ne`：linearIndependent_pair_i
ff_ne {D D' : ℙ K V} : LinearIndependent K ![D.rep, D'.rep] ↔ D != D'
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
-/
theorem linearIndepOn_pair (D D' : ℙ K V) :
    LinearIndepOn K id {D.rep, D'.rep} := by
  by_cases h : D = D'
  · simpa [h] using D'.rep_nonzero
  rw [← ne_eq, ← linearIndependent_pair_iff_ne, LinearIndependent.pair_symm_iff,
    ← linearIndepOn_id_range_iff] at h
  · simpa using h
  · simpa [injective_pair_iff_ne, injective_pair_iff_ne, ne_eq] using h.injective

end linearIndependent

end Projectivization

