/-
Copyright (c) 2025 Jiedong Jiang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan, Jiedong Jiang
-/
module

public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Ideal.Maps

/-!
# The quotient map from `R ⧸ I ^ m` to `R ⧸ I ^ n` where `m ≥ n`

In this file we define the canonical quotient linear map from
`M ⧸ I ^ m • ⊤` to `M ⧸ I ^ n • ⊤` and canonical quotient ring map from
`R ⧸ I ^ m` to `R ⧸ I ^ n`. These definitions will be used in theorems
related to `IsAdicComplete` to find a lift element from compatible sequences in the quotients.
We also include results about the relation between quotients of submodules and quotients of
ideals here.

## Main definitions
- `Submodule.factorPow`: the linear map from `M ⧸ I ^ m • ⊤` to `M ⧸ I ^ n • ⊤` induced by
  the natural inclusion `I ^ n • ⊤ → I ^ m • ⊤`.
- `Ideal.Quotient.factorPow`: the ring homomorphism from `R ⧸ I ^ m`
  to `R ⧸ I ^ n` induced by the natural inclusion `I ^ n → I ^ m`.

## Main results
-/

@[expose] public section

/- Since `Mathlib/LinearAlgebra/Quotient/Basic.lean` and
`Mathlib/RingTheory/Ideal/Quotient/Defs.lean` do not import each other, and the first file that
imports both of them is `Mathlib/RingTheory/Ideal/Quotient/Operations.lean`, which has already
established the first isomorphism theorem and Chinese remainder theorem, we put these pure technical
lemmas that involves both `Submodule.mapQ` and `Ideal.Quotient.factor` in this file. -/

open Ideal Quotient

variable {R : Type*} [Ring R] {I J K : Ideal R}
    {M : Type*} [AddCommGroup M] [Module R M]

/-
**Ideal.Quotient.factor_ker** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.Quotient.factor_ker (H : I <= J) [I.IsTwoSided] [J.IsTwoSided] : Rin
gHom.ker (factor H) = J.map (Ideal.Quotient.mk I)
参数：H : I <= J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.ext`：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
· 使用定理 `Ideal.Quotient.mk_surjective`：mk_surjective : Function.Surjective (mk I)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.mem_map_of_mem`：mem_map_of_mem (f : F) {I : Ideal R} {x : R} (h : 
x in I) : f x in map f I
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Ideal.mem_image_of_mem_map_of_surjective`：mem_image_of_mem_map_of_surjec
tive {I : Ideal R} {y} (H : y in map f I) : y in f '' I
-/
lemma Ideal.Quotient.factor_ker (H : I ≤ J) [I.IsTwoSided] [J.IsTwoSided] :
    RingHom.ker (factor H) = J.map (Ideal.Quotient.mk I) := by
  ext x
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rcases Ideal.Quotient.mk_surjective x with ⟨r, hr⟩
    rw [← hr] at h ⊢
    simp only [factor, RingHom.mem_ker, lift_mk, eq_zero_iff_mem] at h
    exact Ideal.mem_map_of_mem _ h
  · rcases mem_image_of_mem_map_of_surjective _ Ideal.Quotient.mk_surjective h with ⟨r, hr, eq⟩
    simpa [← eq, Ideal.Quotient.eq_zero_iff_mem] using hr

set_option backward.isDefEq.respectTransparency false in
/-
**Submodule.eq_factor_of_eq_factor_succ** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Submodule.eq_factor_of_eq_factor_succ {p : Nat -> Submodule R M} (hp : Ant
itone p) (x : (n : Nat) -> M ⧸ (p n)) (h : forall m, x m = factor (hp m.le_succ)
 (x (m + 1))) {m n : Nat} (g : m <= n) : x m = factor (hp g) (x n)
参数：hp : Antitone p；x : (n : Nat) -> M ⧸ (p n)；h : forall m, x m = factor (hp m.l
e_succ) (x (m + 1))；g : m <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.add_sub_of_le`：∀ {a b : ℕ}, a ≤ b → a + (b - a) = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Submodule.mapQ_id`：mapQ_id (h : p <= p.comap LinearMap.id
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.add_zero`：∀ (n : ℕ), n + 0 = n
· 使用定理 `Nat.le_add_right`：∀ (n k : ℕ), n ≤ n + k
· 使用定理 `add_tsub_cancel_left`：add_tsub_cancel_left (a b : α) : a + b - a = b
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Submodule.factor_comp_apply`：factor_comp_apply (H1 : p <= p') (H2 : p' <
= p'') (x : M ⧸ p) : factor H2 (factor H1 x) = factor (H1.trans H2) x
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
-/
lemma Submodule.eq_factor_of_eq_factor_succ {p : ℕ → Submodule R M}
    (hp : Antitone p) (x : (n : ℕ) → M ⧸ (p n)) (h : ∀ m, x m = factor (hp m.le_succ) (x (m + 1)))
    {m n : ℕ} (g : m ≤ n) : x m = factor (hp g) (x n) := by
  have : n = m + (n - m) := (Nat.add_sub_of_le g).symm
  induction hmn : n - m generalizing m n with
  | zero =>
    rw [hmn, Nat.add_zero] at this
    subst this
    simp
  | succ k ih =>
    rw [hmn, ← add_assoc] at this
    subst this
    rw [ih (m.le_add_right k) (by simp), h]
    · simp
    · lia
/-
**Ideal.Quotient.eq_factor_of_eq_factor_succ** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.Quotient.eq_factor_of_eq_factor_succ {I : Nat -> Ideal R} [forall n,
 (I n).IsTwoSided] (hI : Antitone I) (x : (n : Nat) -> R ⧸ (I n)) (h : forall m,
 x m = factor (hI m.le_succ) (x (m + 1))) {m n : Nat} (g : m <= n) : x m = facto
r (hI g) (x n)
参数：I n；hI : Antitone I；x : (n : Nat) -> R ⧸ (I n)；h : forall m, x m = factor (hI
 m.le_succ) (x (m + 1))；g : m <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
· 使用引理 `Submodule.eq_factor_of_eq_factor_succ`：Submodule.eq_factor_of_eq_factor_
succ {p : Nat -> Submodule R M} (hp : Antitone p) (x : (n : Nat) -> M ⧸ (p n)) (
h : forall m, x m = factor …
-/
lemma Ideal.Quotient.eq_factor_of_eq_factor_succ {I : ℕ → Ideal R} [∀ n, (I n).IsTwoSided]
    (hI : Antitone I) (x : (n : ℕ) → R ⧸ (I n)) (h : ∀ m, x m = factor (hI m.le_succ) (x (m + 1)))
    {m n : ℕ} (g : m ≤ n) : x m = factor (hI g) (x n) :=
  Submodule.eq_factor_of_eq_factor_succ hI x h g
/-
**Ideal.map_mk_comap_factor** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.map_mk_comap_factor [J.IsTwoSided] [K.IsTwoSided] (hIJ : J <= I) (hJ
K : K <= J) : (I.map (mk J)).comap (factor hJK) = I.map (mk K)
参数：hIJ : J <= I；hJK : K <= J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.ext`：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
· 使用定理 `Ideal.mem_image_of_mem_map_of_surjective`：mem_image_of_mem_map_of_surjec
tive {I : Ideal R} {y} (H : y in map f I) : y in f '' I
· 使用定理 `Ideal.Quotient.mk_surjective`：mk_surjective : Function.Surjective (mk I)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Ideal.Quotient.factor_ker`：Ideal.Quotient.factor_ker (H : I <= J) [I.IsT
woSided] [J.IsTwoSided] : RingHom.ker (factor H) = J.map (Ideal.Quotient.mk I)
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `Ideal.mem_map_of_mem`：mem_map_of_mem (f : F) {I : Ideal R} {x : R} (h : 
x in I) : f x in map f I
· 使用定理 `Submodule.add_mem`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [inst
_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodule R M) {x y 
: M}, x…
-/
lemma Ideal.map_mk_comap_factor [J.IsTwoSided] [K.IsTwoSided] (hIJ : J ≤ I) (hJK : K ≤ J) :
    (I.map (mk J)).comap (factor hJK) = I.map (mk K) := by
  ext x
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rcases mem_image_of_mem_map_of_surjective (mk J) Quotient.mk_surjective h with ⟨r, hr, eq⟩
    have : x - ((mk K) r) ∈ J.map (mk K) := by
      simp [← factor_ker hJK, ← eq]
    rcases mem_image_of_mem_map_of_surjective (mk K) Quotient.mk_surjective this with ⟨s, hs, eq'⟩
    rw [← add_sub_cancel ((mk K) r) x, ← eq', ← map_add]
    exact mem_map_of_mem (mk K) (Submodule.add_mem _ hr (hIJ hs))
  · rcases mem_image_of_mem_map_of_surjective (mk K) Quotient.mk_surjective h with ⟨r, hr, eq⟩
    simpa only [← eq] using! mem_map_of_mem (mk J) hr

namespace Submodule

open Submodule

section

@[simp]
/-
**Submodule.mapQ_eq_factor** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：mapQ_eq_factor (h : I <= J) (x : R ⧸ I) : mapQ I J LinearMap.id h x = fact
or h x
参数：h : I <= J；x : R ⧸ I。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapQ_eq_factor (h : I ≤ J) (x : R ⧸ I) :
    mapQ I J LinearMap.id h x = factor h x := rfl

@[simp]
/-
**Submodule.factor_eq_factor** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：factor_eq_factor [I.IsTwoSided] [J.IsTwoSided] (h : I <= J) (x : R ⧸ I) : 
Submodule.factor h x = Ideal.Quotient.factor h x
参数：h : I <= J；x : R ⧸ I。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem factor_eq_factor [I.IsTwoSided] [J.IsTwoSided] (h : I ≤ J) (x : R ⧸ I) :
    Submodule.factor h x = Ideal.Quotient.factor h x := rfl

end

variable (I M)

/-
**Submodule.pow_smul_top_le** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：pow_smul_top_le {m n : Nat} (h : m <= n) : (I ^ n • ⊤ : Submodule R M) <= 
I ^ m • ⊤
参数：h : m <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.smul_mono_left`：smul_mono_left (h : I <= J) : I • N <= J • N
· 使用定理 `Ideal.pow_le_pow_right`：pow_le_pow_right {m n : Nat} (h : m <= n) : I ^ 
n <= I ^ m
-/
lemma pow_smul_top_le {m n : ℕ} (h : m ≤ n) : (I ^ n • ⊤ : Submodule R M) ≤ I ^ m • ⊤ :=
  smul_mono_left (Ideal.pow_le_pow_right h)

/--
The linear map from `M ⧸ I ^ m • ⊤` to `M ⧸ I ^ n • ⊤` induced by
the natural inclusion `I ^ n • ⊤ → I ^ m • ⊤`.

To future contributors: Before adding lemmas related to `Submodule.factorPow`, please
check whether it can be generalized to `Submodule.factor` and whether the
corresponding (more general) lemma for `Submodule.factor` already exists.
-/
/-
**Submodule.factorPow** 是 Mathlib 中的一个缩写定义，位于命名空间 `Submodule`。
形式化陈述：factorPow {m n : Nat} (le : m <= n) : M ⧸ (I ^ n • ⊤ : Submodule R M) ->ₗ[
R] M ⧸ (I ^ m • ⊤ : Submodule R M)
参数：le : m <= n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The linear map from `M ⧸ I ^ m • ⊤` to `M ⧸ I ^ n • ⊤` induced by
the natural inclusion `I ^ n • ⊤ → I ^ m • ⊤`.

To future contributors: Before adding lemmas related to `Submodule.factorPow`, p
lease
check whether it can be generalized to `Submodule.factor` and whether the
corresponding (more general) lemma for `Submodule.factor` already exists.
-/
abbrev factorPow {m n : ℕ} (le : m ≤ n) :
    M ⧸ (I ^ n • ⊤ : Submodule R M) →ₗ[R] M ⧸ (I ^ m • ⊤ : Submodule R M) :=
  factor (smul_mono_left (Ideal.pow_le_pow_right le))

/-- `factorPow` for `n = m + 1` -/
/-
**Submodule.factorPowSucc** 是 Mathlib 中的一个缩写定义，位于命名空间 `Submodule`。
形式化陈述：factorPowSucc (m : Nat) : M ⧸ (I ^ (m + 1) • ⊤ : Submodule R M) ->ₗ[R] M ⧸
 (I ^ m • ⊤ : Submodule R M)
参数：m : Nat。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ

--- 原说明 ---
`factorPow` for `n = m + 1`
-/
abbrev factorPowSucc (m : ℕ) : M ⧸ (I ^ (m + 1) • ⊤ : Submodule R M) →ₗ[R]
    M ⧸ (I ^ m • ⊤ : Submodule R M) := factorPow I M (Nat.le_succ m)

end Submodule

namespace Ideal

namespace Quotient

variable [I.IsTwoSided]

variable (I)

/--
The ring homomorphism from `R ⧸ I ^ m`
to `R ⧸ I ^ n` induced by the natural inclusion `I ^ n → I ^ m`.

To future contributors: Before adding lemmas related to `Ideal.factorPow`, please
check whether it can be generalized to `Ideal.factor` and whether the corresponding
(more general) lemma for `Ideal.factor` already exists.
-/
/-
**Ideal.Quotient.factorPow** 是 Mathlib 中的一个缩写定义，位于命名空间 `Ideal.Quotient`。
形式化陈述：factorPow {m n : Nat} (le : n <= m) : R ⧸ I ^ m ->+* R ⧸ I ^ n
参数：le : n <= m。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The ring homomorphism from `R ⧸ I ^ m`
to `R ⧸ I ^ n` induced by the natural inclusion `I ^ n → I ^ m`.

To future contributors: Before adding lemmas related to `Ideal.factorPow`, pleas
e
check whether it can be generalized to `Ideal.factor` and whether the correspond
ing
(more general) lemma for `Ideal.factor` already exists.
-/
abbrev factorPow {m n : ℕ} (le : n ≤ m) : R ⧸ I ^ m →+* R ⧸ I ^ n :=
  factor (pow_le_pow_right le)

/-- `factorPow` for `m = n + 1` -/
/-
**Ideal.Quotient.factorPowSucc** 是 Mathlib 中的一个缩写定义，位于命名空间 `Ideal.Quotient`。
形式化陈述：factorPowSucc (n : Nat) : R ⧸ I ^ (n + 1) ->+* R ⧸ I ^ n
参数：n : Nat。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ

--- 原说明 ---
`factorPow` for `m = n + 1`
-/
abbrev factorPowSucc (n : ℕ) : R ⧸ I ^ (n + 1) →+* R ⧸ I ^ n :=
  factorPow I (Nat.le_succ n)

end Quotient

end Ideal

variable {R : Type*} [CommRing R] (I : Ideal R)

/-
**Ideal.map_mk_comap_factorPow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.map_mk_comap_factorPow {a b : Nat} (apos : 0 < a) (le : a <= b) : (I
.map (mk (I ^ a))).comap (factorPow I le) = I.map (mk (I ^ b))
参数：apos : 0 < a；le : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Ideal.map_mk_comap_factor`：Ideal.map_mk_comap_factor [J.IsTwoSided] [K.I
sTwoSided] (hIJ : J <= I) (hJK : K <= J) : (I.map (mk J)).comap (factor hJK) = I
.map (mk K)
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Ideal.pow_le_self`：pow_le_self {n : Nat} (hn : n != 0) : I ^ n <= I
· 使用定理 `Nat.ne_zero_of_lt`：∀ {b a : ℕ}, b < a → a ≠ 0
-/
lemma Ideal.map_mk_comap_factorPow {a b : ℕ} (apos : 0 < a) (le : a ≤ b) :
    (I.map (mk (I ^ a))).comap (factorPow I le) = I.map (mk (I ^ b)) := by
  apply Ideal.map_mk_comap_factor
  exact pow_le_self (Nat.ne_zero_of_lt apos)

variable {I} in
/-
**factorPowSucc.isUnit_of_isUnit_image** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：factorPowSucc.isUnit_of_isUnit_image {n : Nat} (npos : n > 0) {a : R ⧸ I ^
 (n + 1)} (h : IsUnit (factorPow I n.le_succ a)) : IsUnit a
参数：npos : n > 0；n + 1；h : IsUnit (factorPow I n.le_succ a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.IsTwoSided.instHPowNat`：∀ {R : Type u} [inst : Semiring R] {I : Id
eal R} [I.IsTwoSided] (n : ℕ), (I ^ n).IsTwoSided
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `isUnit_iff_exists`：isUnit_iff_exists [Monoid M] {x : M} : IsUnit x ↔ exi
sts b, x * b = 1 ∧ b * x = 1
· 使用定理 `Ideal.pow_le_pow_right`：pow_le_pow_right {m n : Nat} (h : m <= n) : I ^ 
n <= I ^ m
· 使用引理 `Ideal.Quotient.factor_surjective`：factor_surjective (H : S <= T) : Funct
ion.Surjective (factor H)
· 使用定理 `Ideal.mem_image_of_mem_map_of_surjective`：mem_image_of_mem_map_of_surjec
tive {I : Ideal R} {y} (H : y in map f I) : y in f '' I
· 使用定理 `Ideal.Quotient.mk_surjective`：mk_surjective : Function.Surjective (mk I)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Ideal.Quotient.factor_ker`：Ideal.Quotient.factor_ker (H : I <= J) [I.IsT
woSided] [J.IsTwoSided] : RingHom.ker (factor H) = J.map (Ideal.Quotient.mk I)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `RingHom.sub_mem_ker_iff`：sub_mem_ker_iff {x y} : x - y in ker f ↔ f x = 
f y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
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
· 使用定理 `IsUnit.of_mul_eq_one`：IsUnit.of_mul_eq_one [Monoid M] [IsDedekindFiniteM
onoid M] {a : M} (b : M) (h : a * b = 1) : IsUnit a
· 使用定理 `instIsDedekindFiniteMonoid`：∀ (M : Type u_2) [inst : CommMonoid M], IsDe
dekindFiniteMonoid M
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
（共 69 条，此处仅展示前 30 条）
-/
lemma factorPowSucc.isUnit_of_isUnit_image {n : ℕ} (npos : n > 0) {a : R ⧸ I ^ (n + 1)}
    (h : IsUnit (factorPow I n.le_succ a)) : IsUnit a := by
  rcases isUnit_iff_exists.mp h with ⟨b, hb, _⟩
  rcases factor_surjective (pow_le_pow_right n.le_succ) b with ⟨b', hb'⟩
  rw [← hb', ← map_one (factorPow I n.le_succ), ← map_mul] at hb
  apply (RingHom.sub_mem_ker_iff (factorPow I n.le_succ)).mpr at hb
  rw [factor_ker (pow_le_pow_right n.le_succ)] at hb
  rcases Ideal.mem_image_of_mem_map_of_surjective (Ideal.Quotient.mk (I ^ (n + 1)))
    Ideal.Quotient.mk_surjective hb with ⟨c, hc, eq⟩
  refine .of_mul_eq_one (b' * (1 - Ideal.Quotient.mk (I ^ (n + 1)) c)) ?_
  calc
    _ = (a * b' - 1) * (1 - Ideal.Quotient.mk (I ^ (n + 1)) c) +
        (1 - Ideal.Quotient.mk (I ^ (n + 1)) c) := by ring
    _ = 1 := by
      rw [← eq, mul_sub, mul_one, sub_add_sub_cancel', sub_eq_self, ← map_mul,
        Ideal.Quotient.eq_zero_iff_mem, pow_add]
      apply Ideal.mul_mem_mul hc (Ideal.mul_le_right (I := I ^ (n - 1)) _)
      simpa only [← pow_add, Nat.sub_add_cancel npos] using! hc

section powSMulQuotInclusion

variable {M : Type*} [AddCommGroup M] [Module R M] {a b c : ℕ}

namespace Submodule

variable (M) in
/-- The canonical inclusion from `I ^ a • N ⧸ I ^ b • (I ^ a • N)` to `M ⧸ I ^ c • N`
when `c = b + a`. -/
/-
**Submodule.powSMulQuotInclusion** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：powSMulQuotInclusion (h : c = b + a) (N : Submodule R M) : ↑(I ^ a • N) ⧸ 
(I ^ b • ⊤ : Submodule R ↑(I ^ a • N)) ->ₗ[R] M ⧸ (I ^ c • N)
参数：h : c = b + a；N : Submodule R M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical inclusion from `I ^ a • N ⧸ I ^ b • (I ^ a • N)` to `M ⧸ I ^ c • N
`
when `c = b + a`.
-/
def powSMulQuotInclusion (h : c = b + a) (N : Submodule R M) :
    ↑(I ^ a • N) ⧸ (I ^ b • ⊤ : Submodule R ↑(I ^ a • N)) →ₗ[R] M ⧸ (I ^ c • N) :=
  mapQ _ _ (I ^ a • N).subtype <| by simp [← map_le_iff_le_comap, h, pow_add, mul_smul]

@[simp]
/-
**Submodule.powSMulQuotInclusion_mk** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：powSMulQuotInclusion_mk (h : c = b + a) (N : Submodule R M) (x : ↑(I ^ a •
 N)) : powSMulQuotInclusion I M h N (Quotient.mk x) = Quotient.mk (x : M)
参数：h : c = b + a；N : Submodule R M；x : ↑(I ^ a • N)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
theorem powSMulQuotInclusion_mk (h : c = b + a) (N : Submodule R M)
    (x : ↑(I ^ a • N)) : powSMulQuotInclusion I M h N (Quotient.mk x) = Quotient.mk (x : M) := rfl
/-
**Submodule.powSMulQuotInclusion_injective** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`
。
形式化陈述：powSMulQuotInclusion_injective {a b c : Nat} (h : c = b + a) (N : Submodul
e R M) : Function.Injective (powSMulQuotInclusion I M h N)
参数：h : c = b + a；N : Submodule R M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.ker_eq_bot`：ker_eq_bot {f : M ->ₛₗ[τ₁₂] M₂} : ker f = ⊥ ↔ Inje
ctive f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Submodule.ker_liftQ`：ker_liftQ (f : M ->ₛₗ[τ₁₂] M₂) (h) : ker (p.liftQ f
 h) = (ker f).map (mkQ p)
· 使用定理 `Submodule.map.congr_simp`：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5
} {M₂ : Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddComm
Monoid M] [ins…
· 使用定理 `Submodule.ker_mkQ`：ker_mkQ : ker p.mkQ = p
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `Submodule.map_le_map_iff_of_injective`：map_le_map_iff_of_injective (p q 
: Submodule R M) : p.map f <= q.map f ↔ p <= q
· 使用引理 `Submodule.subtype_injective`：subtype_injective : Function.Injective p.su
btype
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Submodule.map_comap_subtype`：map_comap_subtype : map p.subtype (comap p.
subtype p') = p ⊓ p'
· 使用定理 `Submodule.map_smul''`：map_smul'' (f : M ->ₗ[R] M') : (I • N).map f = I •
 N.map f
· 使用定理 `Submodule.map_top`：map_top [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) 
: map f ⊤ = range f
· 使用定理 `Submodule.range_subtype`：range_subtype : range p.subtype = p
-/
theorem powSMulQuotInclusion_injective {a b c : ℕ} (h : c = b + a) (N : Submodule R M) :
    Function.Injective (powSMulQuotInclusion I M h N) := by
  rw [← LinearMap.ker_eq_bot]
  simp [powSMulQuotInclusion, mapQ, ← le_bot_iff, ker_liftQ, LinearMap.ker_comp, pow_add, mul_smul,
    map_le_iff_le_comap, ← Submodule.map_le_map_iff_of_injective (I ^ a • N).subtype_injective, h]
/-
**Submodule.factorPow_comp_powSMulQuotInclusion** 是 Mathlib 中的一个定理，位于命名空间 `Submo
dule`。
形式化陈述：factorPow_comp_powSMulQuotInclusion {d e : Nat} (h : c = b + a) (h' : e = 
d + c) : factorPow I M (show c <= e by lia) ∘ₗ powSMulQuotInclusion I M (show e 
= (b + d) + a by lia) ⊤ = powSMulQuotInclusion I M h ⊤ ∘ₗ factorPow I ↥(I ^ a • 
⊤ : Submodule R M) (b.le_add_right d)
参数：h : c = b + a；h' : e = d + c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.linearMap_qext`：linearMap_qext ⦃f g : M ⧸ p ->ₛₗ[τ₁₂] M₂⦄ (h :
 f.comp p.mkQ = g.comp p.mkQ) : f = g
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Nat.le_add_right`：∀ (n k : ℕ), n ≤ n + k
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
-/
theorem factorPow_comp_powSMulQuotInclusion {d e : ℕ} (h : c = b + a) (h' : e = d + c) :
    factorPow I M (show c ≤ e by lia) ∘ₗ
      powSMulQuotInclusion I M (show e = (b + d) + a by lia) ⊤ =
    powSMulQuotInclusion I M h ⊤ ∘ₗ
      factorPow I ↥(I ^ a • ⊤ : Submodule R M) (b.le_add_right d) := by
  ext; rfl
/-
**Submodule.range_powSMulQuotInclusion** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：range_powSMulQuotInclusion (h : c = b + a) (N : Submodule R M) : (powSMulQ
uotInclusion I M h N).range = (I ^ a • N).map (mkQ (I ^ c • N))
参数：h : c = b + a；N : Submodule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.range_liftQ`：range_liftQ [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ
₁₂] M₂) (h) : range (p.liftQ f h) = range f
· 使用定理 `LinearMap.range_comp`：range_comp [RingHomSurjective τ₁₂] [RingHomSurject
ive τ₂₃] [RingHomSurjective τ₁₃] (f : M ->ₛₗ[τ₁₂] M₂) (g : M₂ ->ₛₗ[τ₂₃] M₃) : ra
nge (g.com…
· 使用定理 `Submodule.map.congr_simp`：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5
} {M₂ : Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddComm
Monoid M] [ins…
· 使用定理 `Submodule.range_subtype`：range_subtype : range p.subtype = p
· 使用定理 `Submodule.map_smul''`：map_smul'' (f : M ->ₗ[R] M') : (I • N).map f = I •
 N.map f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem range_powSMulQuotInclusion (h : c = b + a) (N : Submodule R M) :
    (powSMulQuotInclusion I M h N).range = (I ^ a • N).map (mkQ (I ^ c • N)) := by
  simp [powSMulQuotInclusion, mapQ, range_liftQ, LinearMap.range_comp]

end Submodule

end powSMulQuotInclusion

