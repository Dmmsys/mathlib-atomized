/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Judith Ludwig, Christian Merten, Jiedong Jiang
-/
module

public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.LinearAlgebra.SModEq.Basic
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.Tactic.SuppressCompilation

/-!
# Completion of a module with respect to an ideal.

In this file we define the notions of Hausdorff, precomplete, and complete for an `R`-module `M`
with respect to an ideal `I`:

## Main definitions

- `IsHausdorff I M`: this says that the intersection of `I^n M` is `0`.
- `IsPrecomplete I M`: this says that every Cauchy sequence converges.
- `IsAdicComplete I M`: this says that `M` is Hausdorff and precomplete.
- `Hausdorffification I M`: this is the universal Hausdorff module with a map from `M`.
- `AdicCompletion I M`: if `I` is finitely generated, then this is the universal complete module
  with a linear map `AdicCompletion.lift` from `M`. This map is injective iff `M` is Hausdorff
  and surjective iff `M` is precomplete.
- `IsAdicComplete.lift`: if `N` is `I`-adically complete, then a compatible family of
  linear maps `M →ₗ[R] N ⧸ (I ^ n • ⊤)` can be lifted to a unique linear map `M →ₗ[R] N`.
  Together with `mk_lift_apply` and `eq_lift`, it gives the universal property of being
  `I`-adically complete.
-/

@[expose] public section

suppress_compilation

open Submodule Ideal Quotient

variable {R S T : Type*} [CommRing R] (I : Ideal R)
variable (M : Type*) [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]

/-- A module `M` is Hausdorff with respect to an ideal `I` if `⋂ I^n M = 0`. -/
/-
**IsHausdorff** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{R : Type u_1} → [inst : CommRing R] → Ideal R → (M : Type u_4) → [inst_1 
: AddCommGroup M] → [_root_.Module R M] → Prop
参数：M : Type u_4。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A module `M` is Hausdorff with respect to an ideal `I` if `⋂ I^n M = 0`.
-/
class IsHausdorff : Prop where
  haus' : ∀ x : M, (∀ n : ℕ, x ≡ 0 [SMOD (I ^ n • ⊤ : Submodule R M)]) → x = 0

/-- A module `M` is precomplete with respect to an ideal `I` if every Cauchy sequence converges. -/
/-
**IsPrecomplete** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{R : Type u_1} → [inst : CommRing R] → Ideal R → (M : Type u_4) → [inst_1 
: AddCommGroup M] → [_root_.Module R M] → Prop
参数：M : Type u_4。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A module `M` is precomplete with respect to an ideal `I` if every Cauchy sequenc
e converges.
-/
class IsPrecomplete : Prop where
  prec' : ∀ f : ℕ → M, (∀ {m n}, m ≤ n → f m ≡ f n [SMOD (I ^ m • ⊤ : Submodule R M)]) →
    ∃ L : M, ∀ n, f n ≡ L [SMOD (I ^ n • ⊤ : Submodule R M)]

/-- A module `M` is `I`-adically complete if it is Hausdorff and precomplete. -/
@[mk_iff, stacks 0317 "see also `IsAdicComplete.of_bijective_iff`"]
/-
**IsAdicComplete** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{R : Type u_1} → [inst : CommRing R] → Ideal R → (M : Type u_4) → [inst_1 
: AddCommGroup M] → [_root_.Module R M] → Prop
参数：M : Type u_4。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A module `M` is `I`-adically complete if it is Hausdorff and precomplete.
-/
class IsAdicComplete : Prop extends IsHausdorff I M, IsPrecomplete I M

variable {I M}
/-
**IsHausdorff.haus** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsHausdorff.haus (_ : IsHausdorff I M) : forall x : M, (forall n : Nat, x 
≡ 0 [SMOD (I ^ n • ⊤ : Submodule R M)]) -> x = 0
参数：_ : IsHausdorff I M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsHausdorff.haus'`：∀ {R : Type u_1} {inst : CommRing R} {I : Ideal R} {M
 : Type u_4} {inst_1 : AddCommGroup M} {inst_2 : _root_.Module R M}   [self : Is
Hausdor…
-/
theorem IsHausdorff.haus (_ : IsHausdorff I M) :
    ∀ x : M, (∀ n : ℕ, x ≡ 0 [SMOD (I ^ n • ⊤ : Submodule R M)]) → x = 0 :=
  IsHausdorff.haus'
/-
**isHausdorff_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isHausdorff_iff : IsHausdorff I M ↔ forall x : M, (forall n : Nat, x ≡ 0 [
SMOD (I ^ n • ⊤ : Submodule R M)]) -> x = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsHausdorff.haus`：IsHausdorff.haus (_ : IsHausdorff I M) : forall x : M,
 (forall n : Nat, x ≡ 0 [SMOD (I ^ n • ⊤ : Submodule R M)]) -> x = 0
-/
theorem isHausdorff_iff :
    IsHausdorff I M ↔ ∀ x : M, (∀ n : ℕ, x ≡ 0 [SMOD (I ^ n • ⊤ : Submodule R M)]) → x = 0 :=
  ⟨IsHausdorff.haus, fun h => ⟨h⟩⟩
/-
**IsHausdorff.eq_iff_smodEq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsHausdorff.eq_iff_smodEq [IsHausdorff I M] {x y : M} : x = y ↔ forall n, 
x ≡ y [SMOD (I ^ n • ⊤ : Submodule R M)]
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `IsHausdorff.haus'`：∀ {R : Type u_1} {inst : CommRing R} {I : Ideal R} {M
 : Type u_4} {inst_1 : AddCommGroup M} {inst_2 : _root_.Module R M}   [self : Is
Hausdor…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
-/
theorem IsHausdorff.eq_iff_smodEq [IsHausdorff I M] {x y : M} :
    x = y ↔ ∀ n, x ≡ y [SMOD (I ^ n • ⊤ : Submodule R M)] := by
  refine ⟨fun h _ ↦ h ▸ rfl, fun h ↦ ?_⟩
  rw [← sub_eq_zero]
  apply IsHausdorff.haus' (I := I) (x - y)
  simpa [SModEq.sub_mem] using h
/-
**IsHausdorff.map_algebraMap_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsHausdorff.map_algebraMap_iff [CommRing S] [Module S M] [Algebra R S] [Is
ScalarTower R S M] : IsHausdorff (I.map (algebraMap R S)) M ↔ IsHausdorff I M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SModEq.restrictScalars`：restrictScalars [SMul S R] [IsScalarTower S R M]
 : x ≡ y [SMOD U.restrictScalars S] ↔ x ≡ y [SMOD U]
· 使用定理 `Submodule.restrictScalars_map_smul_eq`：restrictScalars_map_smul_eq {S M 
: Type*} [CommSemiring S] [Algebra S R] [AddCommMonoid M] [Module R M] [Module S
 M] [IsScalarTower S R M] (…
· 使用定理 `Submodule.restrictScalars_self`：restrictScalars_self (V : Submodule R M)
 : V.restrictScalars R = V
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem IsHausdorff.map_algebraMap_iff [CommRing S] [Module S M] [Algebra R S]
    [IsScalarTower R S M] : IsHausdorff (I.map (algebraMap R S)) M ↔ IsHausdorff I M := by
  simp [isHausdorff_iff, ← Ideal.map_pow, ← SModEq.restrictScalars R,
    restrictScalars_map_smul_eq]
/-
**IsHausdorff.of_map** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsHausdorff.of_map [CommRing S] [Module S M] {J : Ideal S} [Algebra R S] [
IsScalarTower R S M] (hIJ : I.map (algebraMap R S) <= J) [IsHausdorff J M] : IsH
ausdorff I M
参数：hIJ : I.map (algebraMap R S) <= J。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsHausdorff.haus`：IsHausdorff.haus (_ : IsHausdorff I M) : forall x : M,
 (forall n : Nat, x ≡ 0 [SMOD (I ^ n • ⊤ : Submodule R M)]) -> x = 0
· 使用引理 `SModEq.of_toAddSubgroup_le`：of_toAddSubgroup_le {U : Submodule R M} {V :
 Submodule S M} (h : U.toAddSubgroup <= V.toAddSubgroup) {x y : M} (hxy : x ≡ y 
[SMOD U]) : x ≡ …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AddSubgroup.toAddSubmonoid_le`：∀ {G : Type u_1} [inst : AddGroup G] {p q
 : AddSubgroup G}, p.toAddSubmonoid ≤ q.toAddSubmonoid ↔ p ≤ q
· 使用引理 `AddSubmonoid.smul_le`：smul_le : M • N <= P ↔ forall m in M, forall n in 
N, m • n in P
· 使用定理 `algebraMap_smul`：algebraMap_smul (r : R) (m : M) : (algebraMap R A) r • 
m = r • m
· 使用引理 `AddSubmonoid.smul_mem_smul`：smul_mem_smul (hm : m in M) (hn : n in N) : 
m • n in M • N
· 使用定理 `Ideal.mem_map_of_mem`：mem_map_of_mem (f : F) {I : Ideal R} {x : R} (h : 
x in I) : f x in map f I
· 使用定理 `Ideal.pow_right_mono`：pow_right_mono (e : I <= J) (n : Nat) : I ^ n <= J
 ^ n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Ideal.map_pow`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : CommSe
miring R] [inst_1 : CommSemiring S] [inst_2 : FunLike F R S]   [rc : RingHomClas
s F…
-/
theorem IsHausdorff.of_map [CommRing S] [Module S M] {J : Ideal S} [Algebra R S]
    [IsScalarTower R S M] (hIJ : I.map (algebraMap R S) ≤ J) [IsHausdorff J M] :
    IsHausdorff I M := by
  refine ⟨fun x h ↦ IsHausdorff.haus ‹_› x fun n ↦ ?_⟩
  apply SModEq.of_toAddSubgroup_le
      (U := (I ^ n • ⊤ : Submodule R M)) (V := (J ^ n • ⊤ : Submodule S M))
  · rw [← AddSubgroup.toAddSubmonoid_le]
    simp only [Submodule.smul_toAddSubmonoid, Submodule.top_toAddSubmonoid]
    rw [AddSubmonoid.smul_le]
    intro r hr m hm
    rw [← algebraMap_smul S r m]
    apply AddSubmonoid.smul_mem_smul ?_ hm
    have := Ideal.mem_map_of_mem (algebraMap R S) hr
    simp only [Ideal.map_pow] at this
    exact Ideal.pow_right_mono hIJ n this
  · exact h n

variable (I) in
/-
**IsHausdorff.funext** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsHausdorff.funext {M : Type*} [IsHausdorff I N] {f g : M -> N} (h : foral
l n m, Submodule.Quotient.mk (p
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsHausdorff.eq_iff_smodEq`：IsHausdorff.eq_iff_smodEq [IsHausdorff I M] {
x y : M} : x = y ↔ forall n, x ≡ y [SMOD (I ^ n • ⊤ : Submodule R M)]
-/
theorem IsHausdorff.funext {M : Type*} [IsHausdorff I N] {f g : M → N}
    (h : ∀ n m, Submodule.Quotient.mk (p := (I ^ n • ⊤ : Submodule R N)) (f m) =
    Submodule.Quotient.mk (g m)) :
    f = g := by
  ext m
  rw [IsHausdorff.eq_iff_smodEq (I := I)]
  intro n
  exact h n m

variable (I) in
/-
**IsHausdorff.StrictMono.funext** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsHausdorff.StrictMono.funext {M : Type*} [IsHausdorff I N] {f g : M -> N}
 {a : Nat -> Nat} (ha : StrictMono a) (h : forall n m, Submodule.Quotient.mk (p
参数：ha : StrictMono a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsHausdorff.eq_iff_smodEq`：IsHausdorff.eq_iff_smodEq [IsHausdorff I M] {
x y : M} : x = y ↔ forall n, x ≡ y [SMOD (I ^ n • ⊤ : Submodule R M)]
· 使用定理 `SModEq.mono`：mono (HU : U₁ <= U₂) (hxy : x ≡ y [SMOD U₁]) : x ≡ y [SMOD 
U₂]
· 使用引理 `Submodule.pow_smul_top_le`：pow_smul_top_le {m n : Nat} (h : m <= n) : (I
 ^ n • ⊤ : Submodule R M) <= I ^ m • ⊤
· 使用定理 `StrictMono.le_apply`：StrictMono.le_apply [WellFoundedLT β] {f : β -> β} 
(hf : StrictMono f) {x} : x <= f x
· 使用定理 `instWellFoundedLTNat`：WellFoundedLT ℕ
-/
theorem IsHausdorff.StrictMono.funext {M : Type*} [IsHausdorff I N] {f g : M → N} {a : ℕ → ℕ}
    (ha : StrictMono a) (h : ∀ n m, Submodule.Quotient.mk (p := (I ^ a n • ⊤ : Submodule R N))
    (f m) = Submodule.Quotient.mk (g m)) : f = g := by
  ext m
  rw [IsHausdorff.eq_iff_smodEq (I := I)]
  intro n
  apply SModEq.mono (Submodule.pow_smul_top_le I N ha.le_apply)
  exact h n m

/--
A variant of `IsHausdorff.funext`, where the target is a ring instead of a module.
-/
/-
**IsHausdorff.funext'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsHausdorff.funext' {R S : Type*} [CommRing S] (I : Ideal S) [IsHausdorff 
I S] {f g : R -> S} (h : forall n r, Ideal.Quotient.mk (I ^ n) (f r) = Ideal.Quo
tient.mk (I ^ n) (g r)) : f = g
参数：I : Ideal S；h : forall n r, Ideal.Quotient.mk (I ^ n) (f r) = Ideal.Quotient.
mk (I ^ n) (g r)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsHausdorff.eq_iff_smodEq`：IsHausdorff.eq_iff_smodEq [IsHausdorff I M] {
x y : M} : x = y ↔ forall n, x ≡ y [SMOD (I ^ n • ⊤ : Submodule R M)]
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Ideal.mul_top`：mul_top [I.IsTwoSided] : I * ⊤ = I

--- 原说明 ---
A variant of `IsHausdorff.funext`, where the target is a ring instead of a modul
e.
-/
theorem IsHausdorff.funext' {R S : Type*} [CommRing S] (I : Ideal S) [IsHausdorff I S]
    {f g : R → S} (h : ∀ n r, Ideal.Quotient.mk (I ^ n) (f r) = Ideal.Quotient.mk (I ^ n) (g r)) :
    f = g := by
  ext r
  rw [IsHausdorff.eq_iff_smodEq (I := I)]
  intro n
  simpa using! h n r

/--
A variant of `IsHausdorff.StrictMono.funext`, where the target is a ring instead of a module.
-/
/-
**IsHausdorff.StrictMono.funext'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsHausdorff.StrictMono.funext' {R S : Type*} [CommRing S] (I : Ideal S) [I
sHausdorff I S] {f g : R -> S} {a : Nat -> Nat} (ha : StrictMono a) (h : forall 
n r, Ideal.Quotient.mk (I ^ a n) (f r) = Ideal.Quotient.mk (I ^ a n) (g r)) : f 
= g
参数：I : Ideal S；ha : StrictMono a；h : forall n r, Ideal.Quotient.mk (I ^ a n) (f 
r) = Ideal.Quotient.mk (I ^ a n) (g r)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsHausdorff.eq_iff_smodEq`：IsHausdorff.eq_iff_smodEq [IsHausdorff I M] {
x y : M} : x = y ↔ forall n, x ≡ y [SMOD (I ^ n • ⊤ : Submodule R M)]
· 使用定理 `SModEq.mono`：mono (HU : U₁ <= U₂) (hxy : x ≡ y [SMOD U₁]) : x ≡ y [SMOD 
U₂]
· 使用引理 `Submodule.pow_smul_top_le`：pow_smul_top_le {m n : Nat} (h : m <= n) : (I
 ^ n • ⊤ : Submodule R M) <= I ^ m • ⊤
· 使用定理 `StrictMono.le_apply`：StrictMono.le_apply [WellFoundedLT β] {f : β -> β} 
(hf : StrictMono f) {x} : x <= f x
· 使用定理 `instWellFoundedLTNat`：WellFoundedLT ℕ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Ideal.mul_top`：mul_top [I.IsTwoSided] : I * ⊤ = I

--- 原说明 ---
A variant of `IsHausdorff.StrictMono.funext`, where the target is a ring instead
 of a module.
-/
theorem IsHausdorff.StrictMono.funext' {R S : Type*} [CommRing S] (I : Ideal S) [IsHausdorff I S]
    {f g : R → S} {a : ℕ → ℕ} (ha : StrictMono a) (h : ∀ n r, Ideal.Quotient.mk (I ^ a n) (f r) =
    Ideal.Quotient.mk (I ^ a n) (g r)) : f = g := by
  ext m
  rw [IsHausdorff.eq_iff_smodEq (I := I)]
  intro n
  apply SModEq.mono (Submodule.pow_smul_top_le I S ha.le_apply)
  simpa using! h n m
/-
**IsPrecomplete.prec** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsPrecomplete.prec (_ : IsPrecomplete I M) {f : Nat -> M} : (forall {m n},
 m <= n -> f m ≡ f n [SMOD (I ^ m • ⊤ : Submodule R M)]) -> exists L : M, forall
 n, f n ≡ L [SMOD (I ^ n • ⊤ : Submodule R M)]
参数：_ : IsPrecomplete I M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPrecomplete.prec'`：∀ {R : Type u_1} {inst : CommRing R} {I : Ideal R} 
{M : Type u_4} {inst_1 : AddCommGroup M} {inst_2 : _root_.Module R M}   [self : 
IsPrecomp…
-/
theorem IsPrecomplete.prec (_ : IsPrecomplete I M) {f : ℕ → M} :
    (∀ {m n}, m ≤ n → f m ≡ f n [SMOD (I ^ m • ⊤ : Submodule R M)]) →
      ∃ L : M, ∀ n, f n ≡ L [SMOD (I ^ n • ⊤ : Submodule R M)] :=
  IsPrecomplete.prec' _
/-
**isPrecomplete_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isPrecomplete_iff : IsPrecomplete I M ↔ forall f : Nat -> M, (forall {m n}
, m <= n -> f m ≡ f n [SMOD (I ^ m • ⊤ : Submodule R M)]) -> exists L : M, foral
l n, f n ≡ L [SMOD (I ^ n • ⊤ : Submodule R M)]
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsPrecomplete.prec'`：∀ {R : Type u_1} {inst : CommRing R} {I : Ideal R} 
{M : Type u_4} {inst_1 : AddCommGroup M} {inst_2 : _root_.Module R M}   [self : 
IsPrecomp…
-/
theorem isPrecomplete_iff :
    IsPrecomplete I M ↔
      ∀ f : ℕ → M,
        (∀ {m n}, m ≤ n → f m ≡ f n [SMOD (I ^ m • ⊤ : Submodule R M)]) →
          ∃ L : M, ∀ n, f n ≡ L [SMOD (I ^ n • ⊤ : Submodule R M)] :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩
/-
**IsPrecomplete.map_algebraMap_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsPrecomplete.map_algebraMap_iff [CommRing S] [Module S M] [Algebra R S] [
IsScalarTower R S M] : IsPrecomplete (I.map (algebraMap R S)) M ↔ IsPrecomplete 
I M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SModEq.restrictScalars`：restrictScalars [SMul S R] [IsScalarTower S R M]
 : x ≡ y [SMOD U.restrictScalars S] ↔ x ≡ y [SMOD U]
· 使用定理 `Submodule.restrictScalars_map_smul_eq`：restrictScalars_map_smul_eq {S M 
: Type*} [CommSemiring S] [Algebra S R] [AddCommMonoid M] [Module R M] [Module S
 M] [IsScalarTower S R M] (…
· 使用定理 `Submodule.restrictScalars_self`：restrictScalars_self (V : Submodule R M)
 : V.restrictScalars R = V
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem IsPrecomplete.map_algebraMap_iff [CommRing S] [Module S M] [Algebra R S]
    [IsScalarTower R S M] : IsPrecomplete (I.map (algebraMap R S)) M ↔ IsPrecomplete I M := by
  simp [isPrecomplete_iff, ← Ideal.map_pow, ← SModEq.restrictScalars R,
    restrictScalars_map_smul_eq]

variable (I M)

/-- The Hausdorffification of a module with respect to an ideal. -/
/-
**Hausdorffification** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：Hausdorffification : Type _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Hausdorffification of a module with respect to an ideal.
-/
abbrev Hausdorffification : Type _ :=
  M ⧸ (⨅ n : ℕ, I ^ n • ⊤ : Submodule R M)

/-- The canonical linear map `M ⧸ (I ^ n • ⊤) →ₗ[R] M ⧸ (I ^ m • ⊤)` for `m ≤ n` used
to define `AdicCompletion`. -/
/-
**AdicCompletion.transitionMap** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：AdicCompletion.transitionMap {m n : Nat} (hmn : m <= n)
参数：hmn : m <= n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical linear map `M ⧸ (I ^ n • ⊤) →ₗ[R] M ⧸ (I ^ m • ⊤)` for `m ≤ n` use
d
to define `AdicCompletion`.
-/
abbrev AdicCompletion.transitionMap {m n : ℕ} (hmn : m ≤ n) := factorPow I M hmn

/-- The completion of a module with respect to an ideal.

This is Hausdorff but not necessarily complete: a classical sufficient condition for
completeness is that `I` be finitely generated [Stacks, 05GG]. -/
/-
**AdicCompletion** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：AdicCompletion : Type _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The completion of a module with respect to an ideal.

This is Hausdorff but not necessarily complete: a classical sufficient condition
 for
completeness is that `I` be finitely generated [Stacks, 05GG].
-/
def AdicCompletion : Type _ :=
  { f : ∀ n : ℕ, M ⧸ (I ^ n • ⊤ : Submodule R M) //
    ∀ {m n} (hmn : m ≤ n), AdicCompletion.transitionMap I M hmn (f n) = f m }

namespace IsHausdorff

/-
**IsHausdorff.bot** 是 Mathlib 中的一个实例，位于命名空间 `IsHausdorff`。
形式化陈述：bot : IsHausdorff (⊥ : Ideal R) M
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `Submodule.bot_smul`：bot_smul : (⊥ : Submodule R A) • N = ⊥
-/
instance bot : IsHausdorff (⊥ : Ideal R) M :=
  ⟨fun x hx => by simpa only [pow_one ⊥, bot_smul, SModEq.bot] using hx 1⟩

variable {M} in
/-
**IsHausdorff.subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `IsHausdorff`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {M : Type u_4} [inst_1 : AddCommGroup
 M] [inst_2 : _root_.Module R M],   IsHausdorff ⊤ M → Subsingleton M
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_sub_eq_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a b : 
α}, a - b = 0 → a = b
· 使用定理 `IsHausdorff.haus`：IsHausdorff.haus (_ : IsHausdorff I M) : forall x : M,
 (forall n : Nat, x ≡ 0 [SMOD (I ^ n • ⊤ : Submodule R M)]) -> x = 0
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.top_pow`：top_pow (n : Nat) : (⊤ ^ n : Ideal R) = ⊤
· 使用定理 `Submodule.top_smul`：top_smul : (⊤ : Ideal R) • N = N
· 使用定理 `SModEq.top`：top : x ≡ y [SMOD (⊤ : Submodule R M)]
-/
protected theorem subsingleton (h : IsHausdorff (⊤ : Ideal R) M) : Subsingleton M :=
  ⟨fun x y => eq_of_sub_eq_zero <| h.haus (x - y) fun n => by
    rw [Ideal.top_pow, top_smul]
    exact SModEq.top⟩
/-
**IsHausdorff.** 是 Mathlib 中的一个实例，位于命名空间 `IsHausdorff`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) of_subsingleton [Subsingleton M] : IsHausdorff I M :=
  ⟨fun _ _ => Subsingleton.elim _ _⟩

variable {I M}
/-
**IsHausdorff.iInf_pow_smul** 是 Mathlib 中的一个定理，位于命名空间 `IsHausdorff`。
形式化陈述：iInf_pow_smul (h : IsHausdorff I M) : (⨅ n : Nat, I ^ n • ⊤ : Submodule R 
M) = ⊥
参数：h : IsHausdorff I M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用定理 `Submodule.mem_bot`：mem_bot {x : M} : x in (⊥ : Submodule R M) ↔ x = 0
· 使用定理 `IsHausdorff.haus`：IsHausdorff.haus (_ : IsHausdorff I M) : forall x : M,
 (forall n : Nat, x ≡ 0 [SMOD (I ^ n • ⊤ : Submodule R M)]) -> x = 0
· 使用定理 `SModEq.zero`：zero : x ≡ 0 [SMOD U] ↔ x in U
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.mem_iInf`：mem_iInf {ι} (p : ι -> Submodule R M) {x} : x in ⨅ i
, p i ↔ forall i, x in p i
-/
theorem iInf_pow_smul (h : IsHausdorff I M) : (⨅ n : ℕ, I ^ n • ⊤ : Submodule R M) = ⊥ :=
  eq_bot_iff.2 fun x hx =>
    (mem_bot _).2 <| h.haus x fun n => SModEq.zero.2 <| (mem_iInf fun n : ℕ => I ^ n • ⊤).1 hx n

end IsHausdorff

namespace Hausdorffification

/-- The canonical linear map to the Hausdorffification. -/
/-
**Hausdorffification.of** 是 Mathlib 中的一个定义，位于命名空间 `Hausdorffification`。
形式化陈述：of : M ->ₗ[R] Hausdorffification I M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical linear map to the Hausdorffification.
-/
def of : M →ₗ[R] Hausdorffification I M :=
  mkQ _

variable {I M}

@[elab_as_elim]
/-
**Hausdorffification.induction_on** 是 Mathlib 中的一个定理，位于命名空间 `Hausdorffification`
。
形式化陈述：induction_on {C : Hausdorffification I M -> Prop} (x : Hausdorffification 
I M) (ih : forall x, C (of I M x)) : C x
参数：x : Hausdorffification I M；ih : forall x, C (of I M x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn'`：∀ {α : Sort u_1} {s₁ : Setoid α} {p : Quotient s₁
 → Prop} (q : Quotient s₁), (∀ (a : α), p (Quotient.mk'' a)) → p q
-/
theorem induction_on {C : Hausdorffification I M → Prop} (x : Hausdorffification I M)
    (ih : ∀ x, C (of I M x)) : C x :=
  Quotient.inductionOn' x ih

variable (I M)
/-
**Hausdorffification.** 是 Mathlib 中的一个实例，位于命名空间 `Hausdorffification`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsHausdorff I (Hausdorffification I M) :=
  ⟨fun x => Quotient.inductionOn' x fun x hx =>
    (Quotient.mk_eq_zero _).2 <| (mem_iInf _).2 fun n => by
      have := comap_map_mkQ (⨅ n : ℕ, I ^ n • ⊤ : Submodule R M) (I ^ n • ⊤)
      simp only [sup_of_le_right (iInf_le (fun n => (I ^ n • ⊤ : Submodule R M)) n)] at this
      rw [← this, map_smul'', Submodule.mem_comap, Submodule.map_top, range_mkQ, ← SModEq.zero]
      exact hx n⟩

variable {M} [h : IsHausdorff I N]

/-- Universal property of Hausdorffification: any linear map to a Hausdorff module extends to a
unique map from the Hausdorffification. -/
/-
**Hausdorffification.lift** 是 Mathlib 中的一个定义，位于命名空间 `Hausdorffification`。
形式化陈述：lift (f : M ->ₗ[R] N) : Hausdorffification I M ->ₗ[R] N
参数：f : M ->ₗ[R] N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Universal property of Hausdorffification: any linear map to a Hausdorff module e
xtends to a
unique map from the Hausdorffification.
-/
def lift (f : M →ₗ[R] N) : Hausdorffification I M →ₗ[R] N :=
  liftQ _ f <| map_le_iff_le_comap.1 <| h.iInf_pow_smul ▸ le_iInf fun n =>
    le_trans (map_mono <| iInf_le _ n) <| by
      rw [map_smul'']
      exact smul_mono le_rfl le_top
/-
**Hausdorffification.lift_of** 是 Mathlib 中的一个定理，位于命名空间 `Hausdorffification`。
形式化陈述：lift_of (f : M ->ₗ[R] N) (x : M) : lift I f (of I M x) = f x
参数：f : M ->ₗ[R] N；x : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lift_of (f : M →ₗ[R] N) (x : M) : lift I f (of I M x) = f x :=
  rfl
/-
**Hausdorffification.lift_comp_of** 是 Mathlib 中的一个定理，位于命名空间 `Hausdorffification`
。
形式化陈述：lift_comp_of (f : M ->ₗ[R] N) : (lift I f).comp (of I M) = f
参数：f : M ->ₗ[R] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
-/
theorem lift_comp_of (f : M →ₗ[R] N) : (lift I f).comp (of I M) = f :=
  LinearMap.ext fun _ => rfl

/-- Uniqueness of lift. -/
/-
**Hausdorffification.lift_eq** 是 Mathlib 中的一个定理，位于命名空间 `Hausdorffification`。
形式化陈述：lift_eq (f : M ->ₗ[R] N) (g : Hausdorffification I M ->ₗ[R] N) (hg : g.com
p (of I M) = f) : g = lift I f
参数：f : M ->ₗ[R] N；g : Hausdorffification I M ->ₗ[R] N；hg : g.comp (of I M) = f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Hausdorffification.induction_on`：induction_on {C : Hausdorffification I 
M -> Prop} (x : Hausdorffification I M) (ih : forall x, C (of I M x)) : C x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Hausdorffification.lift_of`：lift_of (f : M ->ₗ[R] N) (x : M) : lift I f 
(of I M x) = f x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.comp_apply`：comp_apply (x : M₁) : f.comp g x = f (g x)

--- 原说明 ---
Uniqueness of lift.
-/
theorem lift_eq (f : M →ₗ[R] N) (g : Hausdorffification I M →ₗ[R] N) (hg : g.comp (of I M) = f) :
    g = lift I f :=
  LinearMap.ext fun x => induction_on x fun x => by rw [lift_of, ← hg, LinearMap.comp_apply]

end Hausdorffification

namespace IsPrecomplete

/-
**IsPrecomplete.bot** 是 Mathlib 中的一个实例，位于命名空间 `IsPrecomplete`。
形式化陈述：bot : IsPrecomplete (⊥ : Ideal R) M
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Ideal.one_eq_top`：one_eq_top : (1 : Ideal R) = ⊤
· 使用定理 `Submodule.top_smul`：top_smul : (⊤ : Ideal R) • N = N
· 使用定理 `SModEq.top`：top : x ≡ y [SMOD (⊤ : Submodule R M)]
· 使用定理 `SModEq.bot`：bot : x ≡ y [SMOD (⊥ : Submodule R M)] ↔ x = y
· 使用定理 `Submodule.bot_smul`：bot_smul : (⊥ : Submodule R A) • N = ⊥
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `Nat.le_add_left`：∀ (n m : ℕ), n ≤ m + n
· 使用定理 `SModEq.refl`：∀ {R : Type u_1} [inst : Ring R] {M : Type u_4} [inst_1 : A
ddCommGroup M] [inst_2 : _root_.Module R M]   {U : Submodule R M} (x : M), x ≡ x
 …
-/
instance bot : IsPrecomplete (⊥ : Ideal R) M := by
  refine ⟨fun f hf => ⟨f 1, fun n => ?_⟩⟩
  rcases n with - | n
  · rw [pow_zero, Ideal.one_eq_top, top_smul]
    exact SModEq.top
  specialize hf (Nat.le_add_left 1 n)
  rw [pow_one, bot_smul, SModEq.bot] at hf; rw [hf]
/-
**IsPrecomplete.top** 是 Mathlib 中的一个实例，位于命名空间 `IsPrecomplete`。
形式化陈述：top : IsPrecomplete (⊤ : Ideal R) M
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.top_pow`：top_pow (n : Nat) : (⊤ ^ n : Ideal R) = ⊤
· 使用定理 `Submodule.top_smul`：top_smul : (⊤ : Ideal R) • N = N
· 使用定理 `SModEq.top`：top : x ≡ y [SMOD (⊤ : Submodule R M)]
-/
instance top : IsPrecomplete (⊤ : Ideal R) M :=
  ⟨fun f _ =>
    ⟨0, fun n => by
      rw [Ideal.top_pow, top_smul]
      exact SModEq.top⟩⟩
/-
**IsPrecomplete.** 是 Mathlib 中的一个实例，位于命名空间 `IsPrecomplete`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) of_subsingleton [Subsingleton M] : IsPrecomplete I M :=
  ⟨fun f _ => ⟨0, fun n => by rw [Subsingleton.elim (f n) 0]⟩⟩

end IsPrecomplete

namespace AdicCompletion

/-- `AdicCompletion` is the submodule of compatible families in
`∀ n : ℕ, M ⧸ (I ^ n • ⊤)`. -/
/-
**AdicCompletion.submodule** 是 Mathlib 中的一个定义，位于命名空间 `AdicCompletion`。
形式化陈述：submodule : Submodule R (forall n : Nat, M ⧸ (I ^ n • ⊤ : Submodule R M)) 
where carrier
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`AdicCompletion` is the submodule of compatible families in
`∀ n : ℕ, M ⧸ (I ^ n • ⊤)`.
-/
def submodule : Submodule R (∀ n : ℕ, M ⧸ (I ^ n • ⊤ : Submodule R M)) where
  carrier := { f | ∀ {m n} (hmn : m ≤ n), AdicCompletion.transitionMap I M hmn (f n) = f m }
  zero_mem' hmn := by rw [Pi.zero_apply, Pi.zero_apply, map_zero]
  add_mem' hf hg m n hmn := by
    rw [Pi.add_apply, Pi.add_apply, map_add, hf hmn, hg hmn]
  smul_mem' c f hf m n hmn := by rw [Pi.smul_apply, Pi.smul_apply, map_smul, hf hmn]
/-
**AdicCompletion.** 是 Mathlib 中的一个实例，位于命名空间 `AdicCompletion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Zero (AdicCompletion I M) where
  zero := ⟨0, by simp⟩
/-
**AdicCompletion.** 是 Mathlib 中的一个实例，位于命名空间 `AdicCompletion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Add (AdicCompletion I M) where
  add x y := ⟨x.val + y.val, by simp [x.property, y.property]⟩
/-
**AdicCompletion.** 是 Mathlib 中的一个实例，位于命名空间 `AdicCompletion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Neg (AdicCompletion I M) where
  neg x := ⟨- x.val, by simp [x.property]⟩
/-
**AdicCompletion.** 是 Mathlib 中的一个实例，位于命名空间 `AdicCompletion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Sub (AdicCompletion I M) where
  sub x y := ⟨x.val - y.val, by simp [x.property, y.property]⟩
/-
**AdicCompletion.instSMul** 是 Mathlib 中的一个实例，位于命名空间 `AdicCompletion`。
形式化陈述：instSMul [SMul S R] [SMul S M] [IsScalarTower S R M] : SMul S (AdicComplet
ion I M) where smul r x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSMul [SMul S R] [SMul S M] [IsScalarTower S R M] : SMul S (AdicCompletion I M) where
  smul r x := ⟨r • x.val, by simp [x.property]⟩
/-
**AdicCompletion.val_zero** 是 Mathlib 中的一个定理，位于命名空间 `AdicCompletion`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] (I : Ideal R) (M : Type u_4) [inst_1 
: AddCommGroup M]   [inst_2 : _root_.Module R M], ↑0 = 0
参数：I : Ideal R；M : Type u_4。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma val_zero : (0 : AdicCompletion I M).val = 0 := rfl
/-
**AdicCompletion.val_zero_apply** 是 Mathlib 中的一个引理，位于命名空间 `AdicCompletion`。
形式化陈述：val_zero_apply (n : Nat) : (0 : AdicCompletion I M).val n = 0
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma val_zero_apply (n : ℕ) : (0 : AdicCompletion I M).val n = 0 := rfl

variable {I M}
/-
**AdicCompletion.val_add** 是 Mathlib 中的一个定理，位于命名空间 `AdicCompletion`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {I : Ideal R} {M : Type u_4} [inst_1 
: AddCommGroup M] [inst_2 : _root_.Module R M]   (f g : AdicCompletion I M), ↑(f
 + g) = ↑f + ↑g
参数：f g : AdicCompletion I M；f + g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma val_add (f g : AdicCompletion I M) : (f + g).val = f.val + g.val := rfl
/-
**AdicCompletion.val_sub** 是 Mathlib 中的一个定理，位于命名空间 `AdicCompletion`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {I : Ideal R} {M : Type u_4} [inst_1 
: AddCommGroup M] [inst_2 : _root_.Module R M]   (f g : AdicCompletion I M), ↑(f
 - g) = ↑f - ↑g
参数：f g : AdicCompletion I M；f - g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma val_sub (f g : AdicCompletion I M) : (f - g).val = f.val - g.val := rfl
/-
**AdicCompletion.val_neg** 是 Mathlib 中的一个定理，位于命名空间 `AdicCompletion`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {I : Ideal R} {M : Type u_4} [inst_1 
: AddCommGroup M] [inst_2 : _root_.Module R M]   (f : AdicCompletion I M), ↑(-f)
 = -↑f
参数：f : AdicCompletion I M；-f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma val_neg (f : AdicCompletion I M) : (-f).val = -f.val := rfl
/-
**AdicCompletion.val_add_apply** 是 Mathlib 中的一个引理，位于命名空间 `AdicCompletion`。
形式化陈述：val_add_apply (f g : AdicCompletion I M) (n : Nat) : (f + g).val n = f.val
 n + g.val n
参数：f g : AdicCompletion I M；n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma val_add_apply (f g : AdicCompletion I M) (n : ℕ) : (f + g).val n = f.val n + g.val n := rfl
/-
**AdicCompletion.val_sub_apply** 是 Mathlib 中的一个引理，位于命名空间 `AdicCompletion`。
形式化陈述：val_sub_apply (f g : AdicCompletion I M) (n : Nat) : (f - g).val n = f.val
 n - g.val n
参数：f g : AdicCompletion I M；n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma val_sub_apply (f g : AdicCompletion I M) (n : ℕ) : (f - g).val n = f.val n - g.val n := rfl
/-
**AdicCompletion.val_neg_apply** 是 Mathlib 中的一个引理，位于命名空间 `AdicCompletion`。
形式化陈述：val_neg_apply (f : AdicCompletion I M) (n : Nat) : (-f).val n = -f.val n
参数：f : AdicCompletion I M；n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma val_neg_apply (f : AdicCompletion I M) (n : ℕ) : (-f).val n = -f.val n := rfl

/- No `simp` attribute, since it causes `simp` unification timeouts when considering
the `Module (AdicCompletion I R) (AdicCompletion I M)` instance (see `AdicCompletion/Algebra`). -/
@[norm_cast]
/-
**AdicCompletion.val_smul** 是 Mathlib 中的一个引理，位于命名空间 `AdicCompletion`。
形式化陈述：val_smul [SMul S R] [SMul S M] [IsScalarTower S R M] (s : S) (f : AdicComp
letion I M) : (s • f).val = s • f.val
参数：s : S；f : AdicCompletion I M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
No `simp` attribute, since it causes `simp` unification timeouts when considerin
g
the `Module (AdicCompletion I R) (AdicCompletion I M)` instance (see `AdicComple
tion/Algebra`).
-/
lemma val_smul [SMul S R] [SMul S M] [IsScalarTower S R M] (s : S) (f : AdicCompletion I M) :
    (s • f).val = s • f.val := rfl
/-
**AdicCompletion.val_smul_apply** 是 Mathlib 中的一个引理，位于命名空间 `AdicCompletion`。
形式化陈述：val_smul_apply [SMul S R] [SMul S M] [IsScalarTower S R M] (s : S) (f : Ad
icCompletion I M) (n : Nat) : (s • f).val n = s • f.val n
参数：s : S；f : AdicCompletion I M；n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma val_smul_apply [SMul S R] [SMul S M] [IsScalarTower S R M] (s : S) (f : AdicCompletion I M)
    (n : ℕ) : (s • f).val n = s • f.val n := rfl

@[ext]
/-
**AdicCompletion.ext** 是 Mathlib 中的一个引理，位于命名空间 `AdicCompletion`。
形式化陈述：ext {x y : AdicCompletion I M} (h : forall n, x.val n = y.val n) : x = y
参数：h : forall n, x.val n = y.val n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
lemma ext {x y : AdicCompletion I M} (h : ∀ n, x.val n = y.val n) : x = y := Subtype.ext <| funext h

variable (I M)
/-
**AdicCompletion.** 是 Mathlib 中的一个实例，位于命名空间 `AdicCompletion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddCommGroup (AdicCompletion I M) :=
  let f : AdicCompletion I M → ∀ n, M ⧸ (I ^ n • ⊤ : Submodule R M) := Subtype.val
  Subtype.val_injective.addCommGroup f rfl val_add val_neg val_sub (fun _ _ ↦ val_smul ..)
    (fun _ _ ↦ val_smul ..)
/-
**AdicCompletion.** 是 Mathlib 中的一个实例，位于命名空间 `AdicCompletion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Semiring S] [SMul S R] [Module S M] [IsScalarTower S R M] :
    Module S (AdicCompletion I M) :=
  let f : AdicCompletion I M →+ ∀ n, M ⧸ (I ^ n • ⊤ : Submodule R M) :=
    { toFun := Subtype.val, map_zero' := rfl, map_add' := fun _ _ ↦ rfl }
  Subtype.val_injective.module S f val_smul
/-
**AdicCompletion.instIsScalarTower** 是 Mathlib 中的一个实例，位于命名空间 `AdicCompletion`。
形式化陈述：instIsScalarTower [SMul S T] [SMul S R] [SMul T R] [SMul S M] [SMul T M] [
IsScalarTower S R M] [IsScalarTower T R M] [IsScalarTower S T M] : IsScalarTower
 S T (AdicCompletion I M) where smul_assoc s t f
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `AdicCompletion.ext`：ext {x y : AdicCompletion I M} (h : forall n, x.val 
n = y.val n) : x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance instIsScalarTower [SMul S T] [SMul S R] [SMul T R] [SMul S M] [SMul T M]
    [IsScalarTower S R M] [IsScalarTower T R M] [IsScalarTower S T M] :
    IsScalarTower S T (AdicCompletion I M) where
  smul_assoc s t f := by ext; simp [val_smul]
/-
**AdicCompletion.instSMulCommClass** 是 Mathlib 中的一个实例，位于命名空间 `AdicCompletion`。
形式化陈述：instSMulCommClass [SMul S R] [SMul T R] [SMul S M] [SMul T M] [IsScalarTow
er S R M] [IsScalarTower T R M] [SMulCommClass S T M] : SMulCommClass S T (AdicC
ompletion I M) where smul_comm s t f
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `AdicCompletion.ext`：ext {x y : AdicCompletion I M} (h : forall n, x.val 
n = y.val n) : x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance instSMulCommClass [SMul S R] [SMul T R] [SMul S M] [SMul T M]
    [IsScalarTower S R M] [IsScalarTower T R M] [SMulCommClass S T M] :
    SMulCommClass S T (AdicCompletion I M) where
  smul_comm s t f := by ext; simp [val_smul, smul_comm]
/-
**AdicCompletion.instIsCentralScalar** 是 Mathlib 中的一个实例，位于命名空间 `AdicCompletion`。
形式化陈述：instIsCentralScalar [SMul S R] [SMul Sᵐᵒᵖ R] [SMul S M] [SMul Sᵐᵒᵖ M] [IsS
calarTower S R M] [IsScalarTower Sᵐᵒᵖ R M] [IsCentralScalar S M] : IsCentralScal
ar S (AdicCompletion I M) where op_smul_eq_smul s f
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `AdicCompletion.ext`：ext {x y : AdicCompletion I M} (h : forall n, x.val 
n = y.val n) : x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsCentralScalar.op_smul_eq_smul`：∀ {M : Type u_9} {α : Type u_10} {inst 
: SMul M α} {inst_1 : SMul Mᵐᵒᵖ α} [self : IsCentralScalar M α] (m : M) (a : α),
   MulOpposite.op m •…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance instIsCentralScalar [SMul S R] [SMul Sᵐᵒᵖ R] [SMul S M] [SMul Sᵐᵒᵖ M]
    [IsScalarTower S R M] [IsScalarTower Sᵐᵒᵖ R M] [IsCentralScalar S M] :
    IsCentralScalar S (AdicCompletion I M) where
  op_smul_eq_smul s f := by ext; simp [val_smul, op_smul_eq_smul]

/-- The canonical inclusion from the completion to the product. -/
@[simps]
/-
**AdicCompletion.incl** 是 Mathlib 中的一个定义，位于命名空间 `AdicCompletion`。
形式化陈述：incl : AdicCompletion I M ->ₗ[R] (forall n, M ⧸ (I ^ n • ⊤ : Submodule R M
)) where toFun x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical inclusion from the completion to the product.
-/
def incl : AdicCompletion I M →ₗ[R] (∀ n, M ⧸ (I ^ n • ⊤ : Submodule R M)) where
  toFun x := x.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable {I M}

@[simp, norm_cast]
/-
**AdicCompletion.val_sum** 是 Mathlib 中的一个引理，位于命名空间 `AdicCompletion`。
形式化陈述：val_sum {ι : Type*} (s : Finset ι) (f : ι -> AdicCompletion I M) : (∑ i in
 s, f i).val = ∑ i in s, (f i).val
参数：s : Finset ι；f : ι -> AdicCompletion I M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `AdicCompletion.incl_apply`：∀ {R : Type u_1} [inst : CommRing R] (I : Ide
al R) (M : Type u_4) [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   (x
 : AdicCompleti…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma val_sum {ι : Type*} (s : Finset ι) (f : ι → AdicCompletion I M) :
    (∑ i ∈ s, f i).val = ∑ i ∈ s, (f i).val := by
  simp_rw [← funext (incl_apply _ _ _), map_sum]
/-
**AdicCompletion.val_sum_apply** 是 Mathlib 中的一个引理，位于命名空间 `AdicCompletion`。
形式化陈述：val_sum_apply {ι : Type*} (s : Finset ι) (f : ι -> AdicCompletion I M) (n 
: Nat) : (∑ i in s, f i).val n = ∑ i in s, (f i).val n
参数：s : Finset ι；f : ι -> AdicCompletion I M；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `AdicCompletion.val_sum`：val_sum {ι : Type*} (s : Finset ι) (f : ι -> Adi
cCompletion I M) : (∑ i in s, f i).val = ∑ i in s, (f i).val
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma val_sum_apply {ι : Type*} (s : Finset ι) (f : ι → AdicCompletion I M) (n : ℕ) :
    (∑ i ∈ s, f i).val n = ∑ i ∈ s, (f i).val n := by simp

variable (I M)

/-- The canonical linear map to the completion. -/
/-
**AdicCompletion.of** 是 Mathlib 中的一个定义，位于命名空间 `AdicCompletion`。
形式化陈述：of : M ->ₗ[R] AdicCompletion I M where toFun x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical linear map to the completion.
-/
def of : M →ₗ[R] AdicCompletion I M where
  toFun x := ⟨fun n => mkQ (I ^ n • ⊤ : Submodule R M) x, fun _ => rfl⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
/-
**AdicCompletion.of_apply** 是 Mathlib 中的一个定理，位于命名空间 `AdicCompletion`。
形式化陈述：of_apply (x : M) (n : Nat) : (of I M x).1 n = mkQ (I ^ n • ⊤ : Submodule R
 M) x
参数：x : M；n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem of_apply (x : M) (n : ℕ) : (of I M x).1 n = mkQ (I ^ n • ⊤ : Submodule R M) x :=
  rfl

/-- Linearly evaluating a sequence in the completion at a given input. -/
/-
**AdicCompletion.eval** 是 Mathlib 中的一个定义，位于命名空间 `AdicCompletion`。
形式化陈述：eval (n : Nat) : AdicCompletion I M ->ₗ[R] M ⧸ (I ^ n • ⊤ : Submodule R M)
 where toFun f
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Linearly evaluating a sequence in the completion at a given input.
-/
def eval (n : ℕ) : AdicCompletion I M →ₗ[R] M ⧸ (I ^ n • ⊤ : Submodule R M) where
  toFun f := f.1 n
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
/-
**AdicCompletion.coe_eval** 是 Mathlib 中的一个定理，位于命名空间 `AdicCompletion`。
形式化陈述：coe_eval (n : Nat) : (eval I M n : AdicCompletion I M -> M ⧸ (I ^ n • ⊤ : 
Submodule R M)) = fun f => f.1 n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
theorem coe_eval (n : ℕ) :
    (eval I M n : AdicCompletion I M → M ⧸ (I ^ n • ⊤ : Submodule R M)) = fun f => f.1 n :=
  rfl
/-
**AdicCompletion.eval_apply** 是 Mathlib 中的一个定理，位于命名空间 `AdicCompletion`。
形式化陈述：eval_apply (n : Nat) (f : AdicCompletion I M) : eval I M n f = f.1 n
参数：n : Nat；f : AdicCompletion I M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
theorem eval_apply (n : ℕ) (f : AdicCompletion I M) : eval I M n f = f.1 n :=
  rfl
/-
**AdicCompletion.eval_of** 是 Mathlib 中的一个定理，位于命名空间 `AdicCompletion`。
形式化陈述：eval_of (n : Nat) (x : M) : eval I M n (of I M x) = mkQ (I ^ n • ⊤ : Submo
dule R M) x
参数：n : Nat；x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
theorem eval_of (n : ℕ) (x : M) : eval I M n (of I M x) = mkQ (I ^ n • ⊤ : Submodule R M) x :=
  rfl

@[simp]
/-
**AdicCompletion.eval_comp_of** 是 Mathlib 中的一个定理，位于命名空间 `AdicCompletion`。
形式化陈述：eval_comp_of (n : Nat) : (eval I M n).comp (of I M) = mkQ _
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
theorem eval_comp_of (n : ℕ) : (eval I M n).comp (of I M) = mkQ _ :=
  rfl
/-
**AdicCompletion.eval_surjective** 是 Mathlib 中的一个定理，位于命名空间 `AdicCompletion`。
形式化陈述：eval_surjective (n : Nat) : Function.Surjective (eval I M n)
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Quotient.inductionOn'`：∀ {α : Sort u_1} {s₁ : Setoid α} {p : Quotient s₁
 → Prop} (q : Quotient s₁), (∀ (a : α), p (Quotient.mk'' a)) → p q
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
-/
theorem eval_surjective (n : ℕ) : Function.Surjective (eval I M n) := fun x ↦
  Quotient.inductionOn' x fun x ↦ ⟨of I M x, rfl⟩

@[simp]
/-
**AdicCompletion.range_eval** 是 Mathlib 中的一个定理，位于命名空间 `AdicCompletion`。
形式化陈述：range_eval (n : Nat) : LinearMap.range (eval I M n) = ⊤
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `LinearMap.range_eq_top`：range_eq_top [RingHomSurjective τ₁₂] {f : M ->ₛₗ
[τ₁₂] M₂} : range f = ⊤ ↔ Surjective f
· 使用定理 `AdicCompletion.eval_surjective`：eval_surjective (n : Nat) : Function.Sur
jective (eval I M n)
-/
theorem range_eval (n : ℕ) : LinearMap.range (eval I M n) = ⊤ :=
  LinearMap.range_eq_top.2 (eval_surjective I M n)

variable {I M}

variable (I M)
/-
**AdicCompletion.** 是 Mathlib 中的一个实例，位于命名空间 `AdicCompletion`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsHausdorff I (AdicCompletion I M) where
  haus' x h := ext fun n ↦ by
    refine smul_induction_on (SModEq.zero.1 <| h n) (fun r hr x _ ↦ ?_) (fun x y hx hy ↦ ?_)
    · simp only [val_smul_apply, val_zero]
      induction x.val n using Quotient.inductionOn' with | _ a
      exact SModEq.zero.2 <| smul_mem_smul hr mem_top
    · simp only [val_add_apply, hx, val_zero_apply, hy, add_zero]

@[simp]
/-
**AdicCompletion.transitionMap_comp_eval_apply** 是 Mathlib 中的一个定理，位于命名空间 `AdicCo
mpletion`。
形式化陈述：transitionMap_comp_eval_apply {m n : Nat} (hmn : m <= n) (x : AdicCompleti
on I M) : transitionMap I M hmn (x.val n) = x.val m
参数：hmn : m <= n；x : AdicCompletion I M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem transitionMap_comp_eval_apply {m n : ℕ} (hmn : m ≤ n) (x : AdicCompletion I M) :
    transitionMap I M hmn (x.val n) = x.val m :=
  x.property hmn

@[simp]
/-
**AdicCompletion.transitionMap_comp_eval** 是 Mathlib 中的一个定理，位于命名空间 `AdicCompleti
on`。
形式化陈述：transitionMap_comp_eval {m n : Nat} (hmn : m <= n) : transitionMap I M hmn
 ∘ₗ eval I M n = eval I M m
参数：hmn : m <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AdicCompletion.transitionMap_comp_eval_apply`：transitionMap_comp_eval_ap
ply {m n : Nat} (hmn : m <= n) (x : AdicCompletion I M) : transitionMap I M hmn 
(x.val n) = x.val m
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem transitionMap_comp_eval {m n : ℕ} (hmn : m ≤ n) :
    transitionMap I M hmn ∘ₗ eval I M n = eval I M m := by
  ext x
  simp

/-- A sequence `ℕ → M` is an `I`-adic Cauchy sequence if for every `m ≤ n`,
`f m ≡ f n` modulo `I ^ m • ⊤`. -/
/-
**AdicCompletion.IsAdicCauchy** 是 Mathlib 中的一个定义，位于命名空间 `AdicCompletion`。
形式化陈述：IsAdicCauchy (f : Nat -> M) : Prop
参数：f : Nat -> M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A sequence `ℕ → M` is an `I`-adic Cauchy sequence if for every `m ≤ n`,
`f m ≡ f n` modulo `I ^ m • ⊤`.
-/
def IsAdicCauchy (f : ℕ → M) : Prop :=
  ∀ {m n}, m ≤ n → f m ≡ f n [SMOD (I ^ m • ⊤ : Submodule R M)]

/-- The type of `I`-adic Cauchy sequences. -/
/-
**AdicCompletion.AdicCauchySequence** 是 Mathlib 中的一个定义，位于命名空间 `AdicCompletion`。
形式化陈述：AdicCauchySequence : Type _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of `I`-adic Cauchy sequences.
-/
def AdicCauchySequence : Type _ := { f : ℕ → M // IsAdicCauchy I M f }

namespace AdicCauchySequence

/-- The type of `I`-adic Cauchy sequences is a submodule of the product `ℕ → M`. -/
/-
**AdicCompletion.AdicCauchySequence.submodule** 是 Mathlib 中的一个定义，位于命名空间 `AdicCom
pletion.AdicCauchySequence`。
形式化陈述：submodule : Submodule R (Nat -> M) where carrier
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of `I`-adic Cauchy sequences is a submodule of the product `ℕ → M`.
-/
def submodule : Submodule R (ℕ → M) where
  carrier := { f | IsAdicCauchy I M f }
  add_mem' := by
    intro f g hf hg m n hmn
    exact SModEq.add (hf hmn) (hg hmn)
  zero_mem' := by
    intro _ _ _
    rfl
  smul_mem' := by
    intro r f hf m n hmn
    exact SModEq.smul (hf hmn) r
/-
**AdicCompletion.AdicCauchySequence.** 是 Mathlib 中的一个实例，位于命名空间 `AdicCompletion.A
dicCauchySequence`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Zero (AdicCauchySequence I M) where
  zero := ⟨0, fun _ ↦ rfl⟩
/-
**AdicCompletion.AdicCauchySequence.** 是 Mathlib 中的一个实例，位于命名空间 `AdicCompletion.A
dicCauchySequence`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Add (AdicCauchySequence I M) where
  add x y := ⟨x.val + y.val, fun hmn ↦ SModEq.add (x.property hmn) (y.property hmn)⟩
/-
**AdicCompletion.AdicCauchySequence.** 是 Mathlib 中的一个实例，位于命名空间 `AdicCompletion.A
dicCauchySequence`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Neg (AdicCauchySequence I M) where
  neg x := ⟨- x.val, fun hmn ↦ SModEq.neg (x.property hmn)⟩
/-
**AdicCompletion.AdicCauchySequence.** 是 Mathlib 中的一个实例，位于命名空间 `AdicCompletion.A
dicCauchySequence`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Sub (AdicCauchySequence I M) where
  sub x y := ⟨x.val - y.val, fun hmn ↦ SModEq.sub (x.property hmn) (y.property hmn)⟩
/-
**AdicCompletion.AdicCauchySequence.** 是 Mathlib 中的一个实例，位于命名空间 `AdicCompletion.A
dicCauchySequence`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMul ℕ (AdicCauchySequence I M) where
  smul n x := ⟨n • x.val, fun hmn ↦ SModEq.nsmul (x.property hmn) n⟩
/-
**AdicCompletion.AdicCauchySequence.** 是 Mathlib 中的一个实例，位于命名空间 `AdicCompletion.A
dicCauchySequence`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMul ℤ (AdicCauchySequence I M) where
  smul n x := ⟨n • x.val, fun hmn ↦ SModEq.zsmul (x.property hmn) n⟩
/-
**AdicCompletion.AdicCauchySequence.** 是 Mathlib 中的一个实例，位于命名空间 `AdicCompletion.A
dicCauchySequence`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddCommGroup (AdicCauchySequence I M) := by
  let f : AdicCauchySequence I M → (ℕ → M) := Subtype.val
  apply Subtype.val_injective.addCommGroup f rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
/-
**AdicCompletion.AdicCauchySequence.** 是 Mathlib 中的一个实例，位于命名空间 `AdicCompletion.A
dicCauchySequence`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMul R (AdicCauchySequence I M) where
  smul r x := ⟨r • x.val, fun hmn ↦ SModEq.smul (x.property hmn) r⟩
/-
**AdicCompletion.AdicCauchySequence.** 是 Mathlib 中的一个实例，位于命名空间 `AdicCompletion.A
dicCauchySequence`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Module R (AdicCauchySequence I M) :=
  let f : AdicCauchySequence I M →+ (ℕ → M) :=
    { toFun := Subtype.val, map_zero' := rfl, map_add' := fun _ _ ↦ rfl }
  Subtype.val_injective.module R f (fun _ _ ↦ rfl)
/-
**AdicCompletion.AdicCauchySequence.** 是 Mathlib 中的一个实例，位于命名空间 `AdicCompletion.A
dicCauchySequence`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeFun (AdicCauchySequence I M) (fun _ ↦ ℕ → M) where
  coe f := f.val

@[simp]
/-
**AdicCompletion.AdicCauchySequence.zero_apply** 是 Mathlib 中的一个定理，位于命名空间 `AdicCo
mpletion.AdicCauchySequence`。
形式化陈述：zero_apply (n : Nat) : (0 : AdicCauchySequence I M) n = 0
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zero_apply (n : ℕ) : (0 : AdicCauchySequence I M) n = 0 :=
  rfl

variable {I M}

@[simp]
/-
**AdicCompletion.AdicCauchySequence.add_apply** 是 Mathlib 中的一个定理，位于命名空间 `AdicCom
pletion.AdicCauchySequence`。
形式化陈述：add_apply (n : Nat) (f g : AdicCauchySequence I M) : (f + g) n = f n + g n
参数：n : Nat；f g : AdicCauchySequence I M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem add_apply (n : ℕ) (f g : AdicCauchySequence I M) : (f + g) n = f n + g n :=
  rfl

@[simp]
/-
**AdicCompletion.AdicCauchySequence.sub_apply** 是 Mathlib 中的一个定理，位于命名空间 `AdicCom
pletion.AdicCauchySequence`。
形式化陈述：sub_apply (n : Nat) (f g : AdicCauchySequence I M) : (f - g) n = f n - g n
参数：n : Nat；f g : AdicCauchySequence I M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sub_apply (n : ℕ) (f g : AdicCauchySequence I M) : (f - g) n = f n - g n :=
  rfl

@[simp]
/-
**AdicCompletion.AdicCauchySequence.smul_apply** 是 Mathlib 中的一个定理，位于命名空间 `AdicCo
mpletion.AdicCauchySequence`。
形式化陈述：smul_apply (n : Nat) (r : R) (f : AdicCauchySequence I M) : (r • f) n = r 
• f n
参数：n : Nat；r : R；f : AdicCauchySequence I M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_apply (n : ℕ) (r : R) (f : AdicCauchySequence I M) : (r • f) n = r • f n :=
  rfl

@[ext]
/-
**AdicCompletion.AdicCauchySequence.ext** 是 Mathlib 中的一个定理，位于命名空间 `AdicCompletio
n.AdicCauchySequence`。
形式化陈述：ext {x y : AdicCauchySequence I M} (h : forall n, x n = y n) : x = y
参数：h : forall n, x n = y n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem ext {x y : AdicCauchySequence I M} (h : ∀ n, x n = y n) : x = y :=
  Subtype.ext <| funext h

/-- The defining property of an adic Cauchy sequence unwrapped. -/
/-
**AdicCompletion.AdicCauchySequence.mk_eq_mk** 是 Mathlib 中的一个定理，位于命名空间 `AdicComp
letion.AdicCauchySequence`。
形式化陈述：mk_eq_mk {m n : Nat} (hmn : m <= n) (f : AdicCauchySequence I M) : Submodu
le.Quotient.mk (p
参数：hmn : m <= n；f : AdicCauchySequence I M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SModEq.symm`：∀ {R : Type u_1} [inst : Ring R] {M : Type u_4} [inst_1 : A
ddCommGroup M] [inst_2 : _root_.Module R M]   {U : Submodule R M} {x y : M}, x ≡
 …
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf

--- 原说明 ---
The defining property of an adic Cauchy sequence unwrapped.
-/
theorem mk_eq_mk {m n : ℕ} (hmn : m ≤ n) (f : AdicCauchySequence I M) :
    Submodule.Quotient.mk (p := (I ^ m • ⊤ : Submodule R M)) (f n) =
      Submodule.Quotient.mk (p := (I ^ m • ⊤ : Submodule R M)) (f m) :=
  (f.property hmn).symm

end AdicCauchySequence

/-- The `I`-adic Cauchy condition can be checked on successive `n`. -/
/-
**AdicCompletion.isAdicCauchy_iff** 是 Mathlib 中的一个定理，位于命名空间 `AdicCompletion`。
形式化陈述：isAdicCauchy_iff (f : Nat -> M) : IsAdicCauchy I M f ↔ forall n, f n ≡ f (
n + 1) [SMOD (I ^ n • ⊤ : Submodule R M)]
参数：f : Nat -> M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
· 使用引理 `Nat.le_induction`：le_induction {m : Nat} {P : forall n, m <= n -> Prop} 
(base : P m m.le_refl) (succ : forall n hmn, P n hmn -> P (n + 1) (le_succ_of_le
 hmn))…
· 使用定理 `SModEq.trans`：∀ {R : Type u_1} [inst : Ring R] {M : Type u_4} [inst_1 : 
AddCommGroup M] [inst_2 : _root_.Module R M]   {U : Submodule R M} {x y z : M}, 
x …
· 使用定理 `SModEq.mono`：mono (HU : U₁ <= U₂) (hxy : x ≡ y [SMOD U₁]) : x ≡ y [SMOD 
U₂]
· 使用定理 `Submodule.smul_mono`：smul_mono (hij : I <= J) (hnp : N <= P) : I • N <= 
J • P
· 使用定理 `Ideal.pow_le_pow_right`：pow_le_pow_right {m n : Nat} (h : m <= n) : I ^ 
n <= I ^ m
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a

--- 原说明 ---
The `I`-adic Cauchy condition can be checked on successive `n`.
-/
theorem isAdicCauchy_iff (f : ℕ → M) :
    IsAdicCauchy I M f ↔ ∀ n, f n ≡ f (n + 1) [SMOD (I ^ n • ⊤ : Submodule R M)] := by
  constructor
  · intro h n
    exact h (Nat.le_succ n)
  · intro h m n hmn
    induction n, hmn using Nat.le_induction with
    | base => rfl
    | succ n hmn ih =>
        trans
        · exact ih
        · refine SModEq.mono (smul_mono (Ideal.pow_le_pow_right hmn) (by rfl)) (h n)

/-- Construct `I`-adic Cauchy sequence from sequence satisfying the successive Cauchy condition. -/
@[simps]
/-
**AdicCompletion.AdicCauchySequence.mk** 是 Mathlib 中的一个定义，位于命名空间 `AdicCompletion
.AdicCauchySequence`。
形式化陈述：{R : Type u_1} →   [inst : CommRing R] →     (I : Ideal R) →       (M : Ty
pe u_4) →         [inst_1 : AddCommGroup M] →           [inst_2 : _root_.Module 
R M] →             (f : ℕ → M) → (∀ (n : ℕ), f n ≡ f (n + 1) [SMOD I ^ n • ⊤]) →
 AdicCompletion.AdicCauchySequence I M
参数：I : Ideal R；M : Type u_4；f : ℕ → M；∀ (n : ℕ), f n ≡ f (n + 1) [SMOD I ^ n • ⊤
]。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct `I`-adic Cauchy sequence from sequence satisfying the successive Cauch
y condition.
-/
def AdicCauchySequence.mk (f : ℕ → M)
    (h : ∀ n, f n ≡ f (n + 1) [SMOD (I ^ n • ⊤ : Submodule R M)]) : AdicCauchySequence I M where
  val := f
  property := by rwa [isAdicCauchy_iff]

/-- The canonical linear map from Cauchy sequences to the completion. -/
@[simps]
/-
**AdicCompletion.mk** 是 Mathlib 中的一个定义，位于命名空间 `AdicCompletion`。
形式化陈述：mk : AdicCauchySequence I M ->ₗ[R] AdicCompletion I M where toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical linear map from Cauchy sequences to the completion.
-/
def mk : AdicCauchySequence I M →ₗ[R] AdicCompletion I M where
  toFun f := ⟨fun n ↦ Submodule.mkQ (I ^ n • ⊤ : Submodule R M) (f n), by
    intro m n hmn
    simp only [mkQ_apply]
    exact (f.property hmn).symm⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Criterion for checking that an adic Cauchy sequence is mapped to zero in the adic completion. -/
/-
**AdicCompletion.mk_zero_of** 是 Mathlib 中的一个定理，位于命名空间 `AdicCompletion`。
形式化陈述：mk_zero_of (f : AdicCauchySequence I M) (h : exists k : Nat, forall n >= k
, exists m >= n, exists l >= n, f m in (I ^ l • ⊤ : Submodule R M)) : AdicComple
tion.mk I M f = 0
参数：f : AdicCauchySequence I M；h : exists k : Nat, forall n >= k, exists m >= n, 
exists l >= n, f m in (I ^ l • ⊤ : Submodule R M)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `AdicCompletion.ext`：ext {x y : AdicCompletion I M} (h : forall n, x.val 
n = y.val n) : x = y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AdicCompletion.mk_apply_coe`：∀ {R : Type u_1} [inst : CommRing R] (I : I
deal R) (M : Type u_4) [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   
(f : AdicCompleti…
· 使用定理 `Submodule.mkQ_apply`：mkQ_apply (x : M) : p.mkQ x = Quotient.mk x
· 使用定理 `AdicCompletion.val_zero`：∀ {R : Type u_1} [inst : CommRing R] (I : Ideal
 R) (M : Type u_4) [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M], ↑0 
= 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AdicCompletion.AdicCauchySequence.mk_eq_mk`：mk_eq_mk {m n : Nat} (hmn : 
m <= n) (f : AdicCauchySequence I M) : Submodule.Quotient.mk (p
· 使用定理 `Submodule.smul_mono_left`：smul_mono_left (h : I <= J) : I • N <= J • N
· 使用定理 `Ideal.pow_le_pow_right`：pow_le_pow_right {m n : Nat} (h : m <= n) : I ^ 
n <= I ^ m

--- 原说明 ---
Criterion for checking that an adic Cauchy sequence is mapped to zero in the adi
c completion.
-/
theorem mk_zero_of (f : AdicCauchySequence I M)
    (h : ∃ k : ℕ, ∀ n ≥ k, ∃ m ≥ n, ∃ l ≥ n, f m ∈ (I ^ l • ⊤ : Submodule R M)) :
    AdicCompletion.mk I M f = 0 := by
  obtain ⟨k, h⟩ := h
  ext n
  obtain ⟨m, hnm, l, hnl, hl⟩ := h (n + k) (by lia)
  rw [mk_apply_coe, Submodule.mkQ_apply, val_zero,
    ← AdicCauchySequence.mk_eq_mk (show n ≤ m by lia)]
  simpa using (Submodule.smul_mono_left (Ideal.pow_le_pow_right (by lia))) hl

set_option backward.isDefEq.respectTransparency false in
/-- Every element in the adic completion is represented by a Cauchy sequence. -/
/-
**AdicCompletion.mk_surjective** 是 Mathlib 中的一个定理，位于命名空间 `AdicCompletion`。
形式化陈述：mk_surjective : Function.Surjective (mk I M)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SModEq.def`：∀ {R : Type u_1} [inst : Ring R] {M : Type u_4} [inst_1 : Ad
dCommGroup M] [inst_2 : _root_.Module R M]   {U : Submodule R M} {x y : M}, x ≡ 
…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.mkQ_apply`：mkQ_apply (x : M) : p.mkQ x = Quotient.mk x
· 使用定理 `Submodule.smul_mono_left`：smul_mono_left (h : I <= J) : I • N <= J • N
· 使用定理 `Ideal.pow_le_pow_right`：pow_le_pow_right {m n : Nat} (h : m <= n) : I ^ 
n <= I ^ m
· 使用定理 `Submodule.factor_mk`：factor_mk (H : p <= p') (x : M) : factor H (mkQ p x
) = mkQ p' x
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用引理 `AdicCompletion.ext`：ext {x y : AdicCompletion I M} (h : forall n, x.val 
n = y.val n) : x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AdicCompletion.mk_apply_coe`：∀ {R : Type u_1} [inst : CommRing R] (I : I
deal R) (M : Type u_4) [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   
(f : AdicCompleti…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Submodule.Quotient.mk_surjective`：mk_surjective : Function.Surjective (@
mk _ _ _ _ _ p)
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
Every element in the adic completion is represented by a Cauchy sequence.
-/
theorem mk_surjective : Function.Surjective (mk I M) := by
  intro x
  choose a ha using fun n ↦ Submodule.Quotient.mk_surjective _ (x.val n)
  refine ⟨⟨a, ?_⟩, ?_⟩
  · intro m n hmn
    rw [SModEq.def, ha m, ← mkQ_apply,
      ← factor_mk (Submodule.smul_mono_left (Ideal.pow_le_pow_right hmn)) (a n),
      mkQ_apply, ha n, x.property hmn]
  · ext n
    simp [ha n]

/-- To show a statement about an element of `adicCompletion I M`, it suffices to check it
on Cauchy sequences. -/
/-
**AdicCompletion.induction_on** 是 Mathlib 中的一个定理，位于命名空间 `AdicCompletion`。
形式化陈述：induction_on {p : AdicCompletion I M -> Prop} (x : AdicCompletion I M) (h 
: forall (f : AdicCauchySequence I M), p (mk I M f)) : p x
参数：x : AdicCompletion I M；h : forall (f : AdicCauchySequence I M), p (mk I M f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AdicCompletion.mk_surjective`：mk_surjective : Function.Surjective (mk I 
M)

--- 原说明 ---
To show a statement about an element of `adicCompletion I M`, it suffices to che
ck it
on Cauchy sequences.
-/
theorem induction_on {p : AdicCompletion I M → Prop} (x : AdicCompletion I M)
    (h : ∀ (f : AdicCauchySequence I M), p (mk I M f)) : p x := by
  obtain ⟨f, rfl⟩ := mk_surjective I M x
  exact h f

variable {M}

/-- Lift a compatible family of linear maps `M →ₗ[R] N ⧸ (I ^ n • ⊤ : Submodule R N)` to
the `I`-adic completion of `M`. -/
/-
**AdicCompletion.lift** 是 Mathlib 中的一个定义，位于命名空间 `AdicCompletion`。
形式化陈述：lift (f : forall (n : Nat), M ->ₗ[R] N ⧸ (I ^ n • ⊤ : Submodule R N)) (h :
 forall {m n : Nat} (hle : m <= n), transitionMap I N hle ∘ₗ f n = f m) : M ->ₗ[
R] AdicCompletion I N where toFun
参数：f : forall (n : Nat), M ->ₗ[R] N ⧸ (I ^ n • ⊤ : Submodule R N)；h : forall {m 
n : Nat} (hle : m <= n), transitionMap I N hle ∘ₗ f n = f m。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lift a compatible family of linear maps `M →ₗ[R] N ⧸ (I ^ n • ⊤ : Submodule R N)
` to
the `I`-adic completion of `M`.
-/
def lift (f : ∀ (n : ℕ), M →ₗ[R] N ⧸ (I ^ n • ⊤ : Submodule R N))
    (h : ∀ {m n : ℕ} (hle : m ≤ n), transitionMap I N hle ∘ₗ f n = f m) :
    M →ₗ[R] AdicCompletion I N where
  toFun := fun x ↦ ⟨fun n ↦ f n x, fun hkl ↦ LinearMap.congr_fun (h hkl) x⟩
  map_add' x y := by
    simp only [map_add]
    rfl
  map_smul' r x := by
    simp only [LinearMapClass.map_smul, RingHom.id_apply]
    rfl

@[simp]
/-
**AdicCompletion.eval_lift** 是 Mathlib 中的一个引理，位于命名空间 `AdicCompletion`。
形式化陈述：eval_lift (f : forall (n : Nat), M ->ₗ[R] N ⧸ (I ^ n • ⊤ : Submodule R N))
 (h : forall {m n : Nat} (hle : m <= n), transitionMap I N hle ∘ₗ f n = f m) (n 
: Nat) : eval I N n ∘ₗ lift I f h = f n
参数：f : forall (n : Nat), M ->ₗ[R] N ⧸ (I ^ n • ⊤ : Submodule R N)；h : forall {m 
n : Nat} (hle : m <= n), transitionMap I N hle ∘ₗ f n = f m；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
lemma eval_lift (f : ∀ (n : ℕ), M →ₗ[R] N ⧸ (I ^ n • ⊤ : Submodule R N))
    (h : ∀ {m n : ℕ} (hle : m ≤ n), transitionMap I N hle ∘ₗ f n = f m)
    (n : ℕ) : eval I N n ∘ₗ lift I f h = f n :=
  rfl

@[simp]
/-
**AdicCompletion.eval_lift_apply** 是 Mathlib 中的一个引理，位于命名空间 `AdicCompletion`。
形式化陈述：eval_lift_apply (f : forall (n : Nat), M ->ₗ[R] N ⧸ (I ^ n • ⊤ : Submodule
 R N)) (h : forall {m n : Nat} (hle : m <= n), transitionMap I N hle ∘ₗ f n = f 
m) (n : Nat) (x : M) : (lift I f h x).val n = f n x
参数：f : forall (n : Nat), M ->ₗ[R] N ⧸ (I ^ n • ⊤ : Submodule R N)；h : forall {m 
n : Nat} (hle : m <= n), transitionMap I N hle ∘ₗ f n = f m；n : Nat；x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
lemma eval_lift_apply (f : ∀ (n : ℕ), M →ₗ[R] N ⧸ (I ^ n • ⊤ : Submodule R N))
    (h : ∀ {m n : ℕ} (hle : m ≤ n), transitionMap I N hle ∘ₗ f n = f m)
    (n : ℕ) (x : M) : (lift I f h x).val n = f n x :=
  rfl

section Bijective

variable {I}

set_option backward.isDefEq.respectTransparency false in
/-
**AdicCompletion.of_injective_iff** 是 Mathlib 中的一个定理，位于命名空间 `AdicCompletion`。
形式化陈述：of_injective_iff : Function.Injective (of I M) ↔ IsHausdorff I M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `AdicCompletion.ext`：ext {x y : AdicCompletion I M} (h : forall n, x.val 
n = y.val n) : x = y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.ker_eq_bot`：ker_eq_bot {f : M ->ₛₗ[τ₁₂] M₂} : ker f = ⊥ ↔ Inje
ctive f
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `IsHausdorff.haus`：IsHausdorff.haus (_ : IsHausdorff I M) : forall x : M,
 (forall n : Nat, x ≡ 0 [SMOD (I ^ n • ⊤ : Submodule R M)]) -> x = 0
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
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
-/
theorem of_injective_iff : Function.Injective (of I M) ↔ IsHausdorff I M := by
  constructor
  · refine fun h ↦ ⟨fun x hx ↦ h ?_⟩
    ext n
    simpa [of, SModEq.zero] using hx n
  · intro h
    rw [← LinearMap.ker_eq_bot]
    ext x
    simp only [LinearMap.mem_ker, Submodule.mem_bot]
    refine ⟨fun hx ↦ h.haus x fun n ↦ ?_, fun hx ↦ by simp [hx]⟩
    rw [Subtype.ext_iff] at hx
    simpa [SModEq.zero] using congrFun hx n

variable (I M) in
/-
**AdicCompletion.of_injective** 是 Mathlib 中的一个定理，位于命名空间 `AdicCompletion`。
形式化陈述：of_injective [IsHausdorff I M] : Function.Injective (of I M)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `AdicCompletion.of_injective_iff`：of_injective_iff : Function.Injective (
of I M) ↔ IsHausdorff I M
-/
theorem of_injective [IsHausdorff I M] : Function.Injective (of I M) :=
  of_injective_iff.mpr ‹_›

@[simp]
/-
**AdicCompletion.of_inj** 是 Mathlib 中的一个定理，位于命名空间 `AdicCompletion`。
形式化陈述：of_inj [IsHausdorff I M] {a b : M} : of I M a = of I M b ↔ a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `AdicCompletion.of_injective`：of_injective [IsHausdorff I M] : Function.I
njective (of I M)
-/
theorem of_inj [IsHausdorff I M] {a b : M} : of I M a = of I M b ↔ a = b :=
  (of_injective I M).eq_iff

set_option backward.isDefEq.respectTransparency false in
/-
**AdicCompletion.of_surjective_iff** 是 Mathlib 中的一个定理，位于命名空间 `AdicCompletion`。
形式化陈述：of_surjective_iff : Function.Surjective (of I M) ↔ IsPrecomplete I M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `SModEq.symm`：∀ {R : Type u_1} [inst : Ring R] {M : Type u_4} [inst_1 : A
ddCommGroup M] [inst_2 : _root_.Module R M]   {U : Submodule R M} {x y : M}, x ≡
 …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.mkQ_apply`：mkQ_apply (x : M) : p.mkQ x = Quotient.mk x
· 使用定理 `AdicCompletion.eval_of`：eval_of (n : Nat) (x : M) : eval I M n (of I M x
) = mkQ (I ^ n • ⊤ : Submodule R M) x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsPrecomplete.prec`：IsPrecomplete.prec (_ : IsPrecomplete I M) {f : Nat 
-> M} : (forall {m n}, m <= n -> f m ≡ f n [SMOD (I ^ m • ⊤ : Submodule R M)]) -
> exists…
· 使用定理 `SModEq.eq_1`：∀ {R : Type u_1} [inst : Ring R] {M : Type u_4} [inst_1 : A
ddCommGroup M] [inst_2 : _root_.Module R M]   (U : Submodule R M) (x y : M), (x 
≡…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用引理 `AdicCompletion.ext`：ext {x y : AdicCompletion I M} (h : forall n, x.val 
n = y.val n) : x = y
· 使用定理 `Submodule.Quotient.mk_surjective`：mk_surjective : Function.Surjective (@
mk _ _ _ _ _ p)
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem of_surjective_iff : Function.Surjective (of I M) ↔ IsPrecomplete I M := by
  constructor
  · refine fun h ↦ ⟨fun f hmn ↦ ?_⟩
    let u : AdicCompletion I M := ⟨fun n ↦ Submodule.Quotient.mk (f n), fun c ↦ (hmn c).symm⟩
    obtain ⟨x, hx⟩ := h u
    refine ⟨x, fun n ↦ ?_⟩
    simp only [SModEq]
    rw [← mkQ_apply _ x, ← eval_of, hx]
    simp [u]
  · intro h u
    choose x hx using (fun n ↦ Submodule.Quotient.mk_surjective (I ^ n • ⊤ : Submodule R M) (u.1 n))
    obtain ⟨a, ha⟩ := h.prec (f := x) (fun hmn ↦ by rw [SModEq, hx, ← u.2 hmn, ← hx]; simp)
    use a
    ext n
    simpa [SModEq, ← eval_of, ha, ← hx] using (ha n).symm

variable (I M) in
/-
**AdicCompletion.of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `AdicCompletion`。
形式化陈述：of_surjective [IsPrecomplete I M] : Function.Surjective (of I M)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `AdicCompletion.of_surjective_iff`：of_surjective_iff : Function.Surjectiv
e (of I M) ↔ IsPrecomplete I M
-/
theorem of_surjective [IsPrecomplete I M] : Function.Surjective (of I M) :=
  of_surjective_iff.mpr ‹_›
/-
**AdicCompletion.of_bijective_iff** 是 Mathlib 中的一个定理，位于命名空间 `AdicCompletion`。
形式化陈述：of_bijective_iff : Function.Bijective (of I M) ↔ IsAdicComplete I M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AdicCompletion.of_injective_iff`：of_injective_iff : Function.Injective (
of I M) ↔ IsHausdorff I M
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `AdicCompletion.of_surjective_iff`：of_surjective_iff : Function.Surjectiv
e (of I M) ↔ IsPrecomplete I M
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsAdicComplete.toIsHausdorff`：∀ {R : Type u_1} {inst : CommRing R} {I : 
Ideal R} {M : Type u_4} {inst_1 : AddCommGroup M} {inst_2 : _root_.Module R M}  
 [self : IsAdicCom…
· 使用定理 `IsAdicComplete.toIsPrecomplete`：∀ {R : Type u_1} {inst : CommRing R} {I 
: Ideal R} {M : Type u_4} {inst_1 : AddCommGroup M} {inst_2 : _root_.Module R M}
   [self : IsAdicCom…
-/
theorem of_bijective_iff : Function.Bijective (of I M) ↔ IsAdicComplete I M :=
  ⟨fun h ↦
    { toIsHausdorff := of_injective_iff.mp h.1,
      toIsPrecomplete := of_surjective_iff.mp h.2 },
   fun h ↦ ⟨of_injective_iff.mpr h.1, of_surjective_iff.mpr h.2⟩⟩

variable (I M)

variable [IsAdicComplete I M]
/-
**AdicCompletion.of_bijective** 是 Mathlib 中的一个定理，位于命名空间 `AdicCompletion`。
形式化陈述：of_bijective : Function.Bijective (of I M)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `AdicCompletion.of_bijective_iff`：of_bijective_iff : Function.Bijective (
of I M) ↔ IsAdicComplete I M
-/
theorem of_bijective : Function.Bijective (of I M) :=
  of_bijective_iff.mpr ‹_›

/--
When `M` is `I`-adic complete, the canonical map from `M` to its `I`-adic completion is a linear
equivalence.
-/
@[simps! apply]
/-
**AdicCompletion.ofLinearEquiv** 是 Mathlib 中的一个定义，位于命名空间 `AdicCompletion`。
形式化陈述：ofLinearEquiv : M ≃ₗ[R] AdicCompletion I M
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AdicCompletion.of_bijective`：of_bijective : Function.Bijective (of I M)

--- 原说明 ---
When `M` is `I`-adic complete, the canonical map from `M` to its `I`-adic comple
tion is a linear
equivalence.
-/
def ofLinearEquiv : M ≃ₗ[R] AdicCompletion I M :=
  LinearEquiv.ofBijective (of I M) (of_bijective I M)

variable {M}

@[simp]
/-
**AdicCompletion.ofLinearEquiv_symm_of** 是 Mathlib 中的一个定理，位于命名空间 `AdicCompletion
`。
形式化陈述：ofLinearEquiv_symm_of (x : M) : (ofLinearEquiv I M).symm (of I M x) = x
参数：x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.ofBijective_symm_apply_apply`：ofBijective_symm_apply_apply [
RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂] {h} (x : M) : (ofBijective f h)
.symm (f x) = x
· 使用定理 `AdicCompletion.of_bijective`：of_bijective : Function.Bijective (of I M)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofLinearEquiv_symm_of (x : M) : (ofLinearEquiv I M).symm (of I M x) = x := by
  simp [ofLinearEquiv]

@[simp]
/-
**AdicCompletion.of_ofLinearEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `AdicCompletion
`。
形式化陈述：of_ofLinearEquiv_symm (x : AdicCompletion I M) : of I M ((ofLinearEquiv I 
M).symm x) = x
参数：x : AdicCompletion I M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.apply_ofBijective_symm_apply`：apply_ofBijective_symm_apply [
RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂] {h} (x : M₂) : f ((ofBijective 
f h).symm x) = x
· 使用定理 `AdicCompletion.of_bijective`：of_bijective : Function.Bijective (of I M)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem of_ofLinearEquiv_symm (x : AdicCompletion I M) :
    of I M ((ofLinearEquiv I M).symm x) = x := by
  simp [ofLinearEquiv]

end Bijective

set_option backward.isDefEq.respectTransparency false in
/-
**AdicCompletion.pow_smul_top_le_ker_eval** 是 Mathlib 中的一个定理，位于命名空间 `AdicComplet
ion`。
形式化陈述：pow_smul_top_le_ker_eval (n : Nat) : I ^ n • ⊤ <= (eval I M n).ker
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.Quotient.mk_out`：mk_out (m : M ⧸ p) : Submodule.Quotient.mk (Q
uotient.out m) = m
· 使用定理 `Submodule.Quotient.mk_smul`：mk_smul (r : S) (x : M) : (mk (r • x) : M ⧸ 
p) = r • mk x
· 使用定理 `Submodule.Quotient.mk_eq_zero`：mk_eq_zero : (mk x : M ⧸ p) = 0 ↔ x in p
· 使用定理 `Submodule.smul_mem_smul`：smul_mem_smul {r} {n} (hr : r in I) (hn : n in 
N) : r • n in I • N
· 使用定理 `Submodule.mem_top`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R] [
inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {x : M},   x ∈ ⊤
-/
theorem pow_smul_top_le_ker_eval (n : ℕ) : I ^ n • ⊤ ≤ (eval I M n).ker := by
  simp only [smul_le, mem_top, LinearMap.mem_ker, map_smul, coe_eval, forall_const]
  intro r r_in x
  rw [← Submodule.Quotient.mk_out (x.val n), ← Quotient.mk_smul, Quotient.mk_eq_zero]
  exact smul_mem_smul r_in mem_top

set_option backward.isDefEq.respectTransparency false in
/-
**AdicCompletion.val_apply_mem_smul_top_iff** 是 Mathlib 中的一个引理，位于命名空间 `AdicCompl
etion`。
形式化陈述：val_apply_mem_smul_top_iff {m n : Nat} {x : AdicCompletion I M} (m_ge : n 
<= m) : x.val m in I ^ n • (⊤ : Submodule R (M ⧸ I ^ m • ⊤)) ↔ x.val n = 0
参数：m_ge : n <= m。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `AdicCompletion.transitionMap.eq_1`：∀ {R : Type u_1} [inst : CommRing R] 
(I : Ideal R) (M : Type u_4) [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R
 M]   {m n : ℕ} (hmn : …
· 使用定理 `Submodule.factorPow.eq_1`：∀ {R : Type u_1} [inst : Ring R] (I : Ideal R)
 (M : Type u_2) [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {m n : 
ℕ} (le : m ≤ n…
· 使用定理 `Submodule.factor.eq_1`：∀ {R : Type u_1} {M : Type u_2} [inst : Ring R] [
inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {p p' : Submodule R M} (
H : p ≤ p')…
· 使用定理 `Submodule.mapQ.eq_1`：∀ {R : Type u_1} {M : Type u_2} [inst : Ring R] [in
st_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   (p : Submodule R M) {R₂ : 
Type u_3}…
· 使用定理 `LinearMap.mem_ker`：mem_ker {f : M ->ₛₗ[τ₁₂] M₂} {y} : y in ker f ↔ f y =
 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Submodule.ker_liftQ`：ker_liftQ (f : M ->ₛₗ[τ₁₂] M₂) (h) : ker (p.liftQ f
 h) = (ker f).map (mkQ p)
· 使用定理 `Submodule.map.congr_simp`：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5
} {M₂ : Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddComm
Monoid M] [ins…
· 使用定理 `Submodule.ker_mkQ`：ker_mkQ : ker p.mkQ = p
· 使用定理 `Submodule.map_smul''`：map_smul'' (f : M ->ₗ[R] M') : (I • N).map f = I •
 N.map f
· 使用定理 `Submodule.map_top`：map_top [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) 
: map f ⊤ = range f
· 使用定理 `Submodule.range_mkQ`：range_mkQ : range p.mkQ = ⊤
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
-/
lemma val_apply_mem_smul_top_iff {m n : ℕ} {x : AdicCompletion I M}
    (m_ge : n ≤ m) : x.val m ∈ I ^ n • (⊤ : Submodule R (M ⧸ I ^ m • ⊤)) ↔ x.val n = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [← x.prop m_ge, transitionMap, Submodule.factorPow, Submodule.factor, mapQ,
      ← LinearMap.mem_ker]
    simpa [ker_liftQ]
  simpa [mapQ, h, ← LinearMap.mem_ker, ker_liftQ] using x.prop m_ge

end AdicCompletion

namespace IsAdicComplete

open AdicCompletion

/-
**IsAdicComplete.map_algebraMap_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsAdicComplete`。
形式化陈述：map_algebraMap_iff [CommRing S] [Module S M] [Algebra R S] [IsScalarTower 
R S M] : IsAdicComplete (I.map (algebraMap R S)) M ↔ IsAdicComplete I M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem map_algebraMap_iff [CommRing S] [Module S M] [Algebra R S]
    [IsScalarTower R S M] : IsAdicComplete (I.map (algebraMap R S)) M ↔ IsAdicComplete I M := by
  simp [isAdicComplete_iff, IsPrecomplete.map_algebraMap_iff, IsHausdorff.map_algebraMap_iff]

section lift

variable [IsAdicComplete I N]

variable {M}

/--
Universal property of `IsAdicComplete`.
The lift linear map `lift I f h : M →ₗ[R] N` of a sequence of compatible
linear maps `f n : M →ₗ[R] N ⧸ (I ^ n • ⊤)`.
-/
/-
**IsAdicComplete.lift** 是 Mathlib 中的一个定义，位于命名空间 `IsAdicComplete`。
形式化陈述：lift (f : forall (n : Nat), M ->ₗ[R] N ⧸ (I ^ n • ⊤ : Submodule R N)) (h :
 forall {m n : Nat} (hle : m <= n), factorPow I N hle ∘ₗ f n = f m) : M ->ₗ[R] N
参数：f : forall (n : Nat), M ->ₗ[R] N ⧸ (I ^ n • ⊤ : Submodule R N)；h : forall {m 
n : Nat} (hle : m <= n), factorPow I N hle ∘ₗ f n = f m。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Universal property of `IsAdicComplete`.
The lift linear map `lift I f h : M →ₗ[R] N` of a sequence of compatible
linear maps `f n : M →ₗ[R] N ⧸ (I ^ n • ⊤)`.
-/
def lift (f : ∀ (n : ℕ), M →ₗ[R] N ⧸ (I ^ n • ⊤ : Submodule R N))
    (h : ∀ {m n : ℕ} (hle : m ≤ n), factorPow I N hle ∘ₗ f n = f m) :
    M →ₗ[R] N := (ofLinearEquiv I N).symm ∘ₗ AdicCompletion.lift I f h

@[simp]
/-
**IsAdicComplete.of_lift** 是 Mathlib 中的一个定理，位于命名空间 `IsAdicComplete`。
形式化陈述：of_lift (f : forall (n : Nat), M ->ₗ[R] N ⧸ (I ^ n • ⊤ : Submodule R N)) (
h : forall {m n : Nat} (hle : m <= n), factorPow I N hle ∘ₗ f n = f m) (x : M) :
 of I N (lift I f h x) = AdicCompletion.lift I f h x
参数：f : forall (n : Nat), M ->ₗ[R] N ⧸ (I ^ n • ⊤ : Submodule R N)；h : forall {m 
n : Nat} (hle : m <= n), factorPow I N hle ∘ₗ f n = f m；x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AdicCompletion.of_ofLinearEquiv_symm`：of_ofLinearEquiv_symm (x : AdicCom
pletion I M) : of I M ((ofLinearEquiv I M).symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem of_lift (f : ∀ (n : ℕ), M →ₗ[R] N ⧸ (I ^ n • ⊤ : Submodule R N))
    (h : ∀ {m n : ℕ} (hle : m ≤ n), factorPow I N hle ∘ₗ f n = f m) (x : M) :
    of I N (lift I f h x) = AdicCompletion.lift I f h x := by
  simp [lift]

@[simp]
/-
**IsAdicComplete.of_comp_lift** 是 Mathlib 中的一个定理，位于命名空间 `IsAdicComplete`。
形式化陈述：of_comp_lift (f : forall (n : Nat), M ->ₗ[R] N ⧸ (I ^ n • ⊤ : Submodule R 
N)) (h : forall {m n : Nat} (hle : m <= n), factorPow I N hle ∘ₗ f n = f m) : of
 I N ∘ₗ lift I f h = AdicCompletion.lift I f h
参数：f : forall (n : Nat), M ->ₗ[R] N ⧸ (I ^ n • ⊤ : Submodule R N)；h : forall {m 
n : Nat} (hle : m <= n), factorPow I N hle ∘ₗ f n = f m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsAdicComplete.of_lift`：of_lift (f : forall (n : Nat), M ->ₗ[R] N ⧸ (I ^
 n • ⊤ : Submodule R N)) (h : forall {m n : Nat} (hle : m <= n), factorPow I N h
le ∘ₗ f n = …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem of_comp_lift (f : ∀ (n : ℕ), M →ₗ[R] N ⧸ (I ^ n • ⊤ : Submodule R N))
    (h : ∀ {m n : ℕ} (hle : m ≤ n), factorPow I N hle ∘ₗ f n = f m) :
    of I N ∘ₗ lift I f h = AdicCompletion.lift I f h := by
  ext1; simp

/--
The composition of lift linear map `lift I f h : M →ₗ[R] N` with the canonical
projection `N → N ⧸ (I ^ n • ⊤)` is `f n` .
-/
@[simp]
/-
**IsAdicComplete.mk_lift** 是 Mathlib 中的一个定理，位于命名空间 `IsAdicComplete`。
形式化陈述：mk_lift {f : (n : Nat) -> M ->ₗ[R] N ⧸ (I ^ n • ⊤)} (h : forall {m n : Nat
} (hle : m <= n), factorPow I N hle ∘ₗ f n = f m) (n : Nat) (x : M) : Submodule.
Quotient.mk (lift I f h x) = f n x
参数：n : Nat；I ^ n • ⊤；h : forall {m n : Nat} (hle : m <= n), factorPow I N hle ∘ₗ
 f n = f m；n : Nat；x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.mkQ_apply`：mkQ_apply (x : M) : p.mkQ x = Quotient.mk x
· 使用定理 `AdicCompletion.eval_of`：eval_of (n : Nat) (x : M) : eval I M n (of I M x
) = mkQ (I ^ n • ⊤ : Submodule R M) x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AdicCompletion.of_ofLinearEquiv_symm`：of_ofLinearEquiv_symm (x : AdicCom
pletion I M) : of I M ((ofLinearEquiv I M).symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The composition of lift linear map `lift I f h : M →ₗ[R] N` with the canonical
projection `N → N ⧸ (I ^ n • ⊤)` is `f n` .
-/
theorem mk_lift {f : (n : ℕ) → M →ₗ[R] N ⧸ (I ^ n • ⊤)}
    (h : ∀ {m n : ℕ} (hle : m ≤ n), factorPow I N hle ∘ₗ f n = f m) (n : ℕ) (x : M) :
    Submodule.Quotient.mk (lift I f h x) = f n x := by
  simp only [lift, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
  rw [← mkQ_apply, ← eval_of]
  simp

/--
The composition of lift linear map `lift I f h : M →ₗ[R] N` with the canonical
projection `N →ₗ[R] N ⧸ (I ^ n • ⊤)` is `f n`.
-/
@[simp]
/-
**IsAdicComplete.mkQ_comp_lift** 是 Mathlib 中的一个定理，位于命名空间 `IsAdicComplete`。
形式化陈述：mkQ_comp_lift {f : (n : Nat) -> M ->ₗ[R] N ⧸ (I ^ n • ⊤)} (h : forall {m n
 : Nat} (hle : m <= n), factorPow I N hle ∘ₗ f n = f m) (n : Nat) : mkQ (I ^ n •
 ⊤ : Submodule R N) ∘ₗ lift I f h = f n
参数：n : Nat；I ^ n • ⊤；h : forall {m n : Nat} (hle : m <= n), factorPow I N hle ∘ₗ
 f n = f m；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsAdicComplete.mk_lift`：mk_lift {f : (n : Nat) -> M ->ₗ[R] N ⧸ (I ^ n • 
⊤)} (h : forall {m n : Nat} (hle : m <= n), factorPow I N hle ∘ₗ f n = f m) (n :
 Nat) (x : M…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The composition of lift linear map `lift I f h : M →ₗ[R] N` with the canonical
projection `N →ₗ[R] N ⧸ (I ^ n • ⊤)` is `f n`.
-/
theorem mkQ_comp_lift {f : (n : ℕ) → M →ₗ[R] N ⧸ (I ^ n • ⊤)}
    (h : ∀ {m n : ℕ} (hle : m ≤ n), factorPow I N hle ∘ₗ f n = f m) (n : ℕ) :
    mkQ (I ^ n • ⊤ : Submodule R N) ∘ₗ lift I f h = f n := by
  ext; simp

/--
Uniqueness of the lift.
Given a compatible family of linear maps `f n : M →ₗ[R] N ⧸ (I ^ n • ⊤)`.
If `F : M →ₗ[R] N` makes the following diagram commute
```
  N
  | \
 F|  \ f n
  |   \
  v    v
  M --> M ⧸ (I ^ n • ⊤)
```
Then it is the map `IsAdicComplete.lift`.
-/
/-
**IsAdicComplete.eq_lift** 是 Mathlib 中的一个定理，位于命名空间 `IsAdicComplete`。
形式化陈述：eq_lift {f : (n : Nat) -> M ->ₗ[R] N ⧸ (I ^ n • ⊤)} (h : forall {m n : Nat
} (hle : m <= n), factorPow I N hle ∘ₗ f n = f m) {F : M ->ₗ[R] N} (hF : forall 
n, mkQ _ ∘ₗ F = f n) : F = lift I f h
参数：n : Nat；I ^ n • ⊤；h : forall {m n : Nat} (hle : m <= n), factorPow I N hle ∘ₗ
 f n = f m；hF : forall n, mkQ _ ∘ₗ F = f n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
· 使用定理 `IsHausdorff.funext`：IsHausdorff.funext {M : Type*} [IsHausdorff I N] {f 
g : M -> N} (h : forall n m, Submodule.Quotient.mk (p
· 使用定理 `IsAdicComplete.toIsHausdorff`：∀ {R : Type u_1} {inst : CommRing R} {I : 
Ideal R} {M : Type u_4} {inst_1 : AddCommGroup M} {inst_2 : _root_.Module R M}  
 [self : IsAdicCom…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsAdicComplete.mk_lift`：mk_lift {f : (n : Nat) -> M ->ₗ[R] N ⧸ (I ^ n • 
⊤)} (h : forall {m n : Nat} (hle : m <= n), factorPow I N hle ∘ₗ f n = f m) (n :
 Nat) (x : M…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Uniqueness of the lift.
Given a compatible family of linear maps `f n : M →ₗ[R] N ⧸ (I ^ n • ⊤)`.
If `F : M →ₗ[R] N` makes the following diagram commute
```
  N
  | \
 F|  \ f n
  |   \
  v    v
  M --> M ⧸ (I ^ n • ⊤)
```
Then it is the map `IsAdicComplete.lift`.
-/
theorem eq_lift {f : (n : ℕ) → M →ₗ[R] N ⧸ (I ^ n • ⊤)}
    (h : ∀ {m n : ℕ} (hle : m ≤ n), factorPow I N hle ∘ₗ f n = f m) {F : M →ₗ[R] N}
    (hF : ∀ n, mkQ _ ∘ₗ F = f n) : F = lift I f h := by
  apply DFunLike.coe_injective
  apply IsHausdorff.funext I
  intro n m
  simp [← hF n]

end lift

namespace StrictMono

variable {a : ℕ → ℕ} (ha : StrictMono a)
    (f : (n : ℕ) → M →ₗ[R] N ⧸ (I ^ (a n) • ⊤ : Submodule R N))

variable {I M}
/--
Instead of providing all `M →ₗ[R] N ⧸ (I ^ n • ⊤)`, one can just provide
`M →ₗ[R] N ⧸ (I ^ (a n) • ⊤)` for a strictly increasing sequence `a n` to recover all
`M →ₗ[R] N ⧸ (I ^ n • ⊤)`.
-/
/-
**IsAdicComplete.StrictMono.extend** 是 Mathlib 中的一个定义，位于命名空间 `IsAdicComplete.Str
ictMono`。
形式化陈述：extend (n : Nat) : M ->ₗ[R] N ⧸ (I ^ n • ⊤ : Submodule R N)
参数：n : Nat。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.id_le`：StrictMono.id_le [WellFoundedLT β] {f : β -> β} (hf : 
StrictMono f) : id <= f
· 使用定理 `instWellFoundedLTNat`：WellFoundedLT ℕ

--- 原说明 ---
Instead of providing all `M →ₗ[R] N ⧸ (I ^ n • ⊤)`, one can just provide
`M →ₗ[R] N ⧸ (I ^ (a n) • ⊤)` for a strictly increasing sequence `a n` to recove
r all
`M →ₗ[R] N ⧸ (I ^ n • ⊤)`.
-/
def extend (n : ℕ) :
    M →ₗ[R] N ⧸ (I ^ n • ⊤ : Submodule R N) :=
  factorPow I N (ha.id_le n) ∘ₗ f n

variable (hf : ∀ {m}, factorPow I N (ha.monotone m.le_succ) ∘ₗ (f (m + 1)) = f m)

include hf in
/-
**IsAdicComplete.StrictMono.factorPow_comp_eq_of_factorPow_comp_succ_eq** 是 Math
lib 中的一个定理，位于命名空间 `IsAdicComplete.StrictMono`。
形式化陈述：factorPow_comp_eq_of_factorPow_comp_succ_eq {m n : Nat} (hle : m <= n) : f
actorPow I N (ha.monotone hle) ∘ₗ f n = f m
参数：hle : m <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `StrictMono.monotone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictMono f → Monotone f
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Submodule.eq_factor_of_eq_factor_succ`：Submodule.eq_factor_of_eq_factor_
succ {p : Nat -> Submodule R M} (hp : Antitone p) (x : (n : Nat) -> M ⧸ (p n)) (
h : forall m, x m = factor …
· 使用定理 `Submodule.smul_mono_left`：smul_mono_left (h : I <= J) : I • N <= J • N
· 使用定理 `Ideal.pow_le_pow_right`：pow_le_pow_right {m n : Nat} (h : m <= n) : I ^ 
n <= I ^ m
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
-/
theorem factorPow_comp_eq_of_factorPow_comp_succ_eq
    {m n : ℕ} (hle : m ≤ n) : factorPow I N (ha.monotone hle) ∘ₗ f n = f m := by
  ext x
  symm
  refine Submodule.eq_factor_of_eq_factor_succ ?_ (fun n ↦ f n x) ?_ hle
  · exact fun _ _ le ↦ smul_mono_left (Ideal.pow_le_pow_right (ha.monotone le))
  · intro s
    simp only [LinearMap.ext_iff] at hf
    simpa using (hf x).symm

include hf in
/-
**IsAdicComplete.StrictMono.extend_eq** 是 Mathlib 中的一个定理，位于命名空间 `IsAdicComplete.
StrictMono`。
形式化陈述：extend_eq (n : Nat) : extend ha f (a n) = f n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `StrictMono.monotone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictMono f → Monotone f
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
· 使用定理 `IsAdicComplete.StrictMono.factorPow_comp_eq_of_factorPow_comp_succ_eq`：f
actorPow_comp_eq_of_factorPow_comp_succ_eq {m n : Nat} (hle : m <= n) : factorPo
w I N (ha.monotone hle) ∘ₗ f n = f m
· 使用定理 `StrictMono.id_le`：StrictMono.id_le [WellFoundedLT β] {f : β -> β} (hf : 
StrictMono f) : id <= f
· 使用定理 `instWellFoundedLTNat`：WellFoundedLT ℕ
-/
theorem extend_eq (n : ℕ) : extend ha f (a n) = f n :=
  factorPow_comp_eq_of_factorPow_comp_succ_eq ha f hf (ha.id_le n)

include hf in
/-
**IsAdicComplete.StrictMono.factorPow_comp_extend** 是 Mathlib 中的一个定理，位于命名空间 `IsA
dicComplete.StrictMono`。
形式化陈述：factorPow_comp_extend {m n : Nat} (hle : m <= n) : factorPow I N hle ∘ₗ ex
tend ha f n = extend ha f m
参数：hle : m <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `StrictMono.monotone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictMono f → Monotone f
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `StrictMono.id_le`：StrictMono.id_le [WellFoundedLT β] {f : β -> β} (hf : 
StrictMono f) : id <= f
· 使用定理 `instWellFoundedLTNat`：WellFoundedLT ℕ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.factor_comp_apply`：factor_comp_apply (H1 : p <= p') (H2 : p' <
= p'') (x : M ⧸ p) : factor H2 (factor H1 x) = factor (H1.trans H2) x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsAdicComplete.StrictMono.factorPow_comp_eq_of_factorPow_comp_succ_eq`：f
actorPow_comp_eq_of_factorPow_comp_succ_eq {m n : Nat} (hle : m <= n) : factorPo
w I N (ha.monotone hle) ∘ₗ f n = f m
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem factorPow_comp_extend {m n : ℕ} (hle : m ≤ n) :
    factorPow I N hle ∘ₗ extend ha f n = extend ha f m := by
  ext
  simp [extend, ← factorPow_comp_eq_of_factorPow_comp_succ_eq ha f hf hle]

variable [IsAdicComplete I N]

variable (I)

/--
A variant of `IsAdicComplete.lift`. Only takes `f n : M →ₗ[R] N ⧸ (I ^ (a n) • ⊤)`
from a strictly increasing sequence `a n`.
-/
/-
**IsAdicComplete.StrictMono.lift** 是 Mathlib 中的一个定义，位于命名空间 `IsAdicComplete.Stric
tMono`。
形式化陈述：lift : M ->ₗ[R] N
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A variant of `IsAdicComplete.lift`. Only takes `f n : M →ₗ[R] N ⧸ (I ^ (a n) • ⊤
)`
from a strictly increasing sequence `a n`.
-/
def lift : M →ₗ[R] N :=
  IsAdicComplete.lift I (extend ha f) (factorPow_comp_extend ha f hf)
/-
**IsAdicComplete.StrictMono.of_lift** 是 Mathlib 中的一个定理，位于命名空间 `IsAdicComplete.St
rictMono`。
形式化陈述：of_lift (x : M) : of I N (lift I ha f hf x) = AdicCompletion.lift I (exten
d ha f) (factorPow_comp_extend ha f hf) x
参数：x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `StrictMono.monotone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictMono f → Monotone f
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
· 使用定理 `IsAdicComplete.of_lift`：of_lift (f : forall (n : Nat), M ->ₗ[R] N ⧸ (I ^
 n • ⊤ : Submodule R N)) (h : forall {m n : Nat} (hle : m <= n), factorPow I N h
le ∘ₗ f n = …
· 使用定理 `IsAdicComplete.StrictMono.factorPow_comp_extend`：factorPow_comp_extend {
m n : Nat} (hle : m <= n) : factorPow I N hle ∘ₗ extend ha f n = extend ha f m
-/
theorem of_lift (x : M) :
    of I N (lift I ha f hf x) =
    AdicCompletion.lift I (extend ha f) (factorPow_comp_extend ha f hf) x :=
  IsAdicComplete.of_lift I (extend ha f) (factorPow_comp_extend ha f hf) x
/-
**IsAdicComplete.StrictMono.of_comp_lift** 是 Mathlib 中的一个定理，位于命名空间 `IsAdicComple
te.StrictMono`。
形式化陈述：of_comp_lift : of I N ∘ₗ lift I ha f hf = AdicCompletion.lift I (extend ha
 f) (factorPow_comp_extend ha f hf)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `StrictMono.monotone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictMono f → Monotone f
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
· 使用定理 `IsAdicComplete.of_comp_lift`：of_comp_lift (f : forall (n : Nat), M ->ₗ[R
] N ⧸ (I ^ n • ⊤ : Submodule R N)) (h : forall {m n : Nat} (hle : m <= n), facto
rPow I N hle ∘ₗ f…
· 使用定理 `IsAdicComplete.StrictMono.factorPow_comp_extend`：factorPow_comp_extend {
m n : Nat} (hle : m <= n) : factorPow I N hle ∘ₗ extend ha f n = extend ha f m
-/
theorem of_comp_lift :
    of I N ∘ₗ lift I ha f hf =
      AdicCompletion.lift I (extend ha f) (factorPow_comp_extend ha f hf) :=
  IsAdicComplete.of_comp_lift I (extend ha f) (factorPow_comp_extend ha f hf)

@[simp]
/-
**IsAdicComplete.StrictMono.mk_lift** 是 Mathlib 中的一个定理，位于命名空间 `IsAdicComplete.St
rictMono`。
形式化陈述：mk_lift {n : Nat} (x : M) : (Submodule.Quotient.mk (lift I ha f hf x)) = f
 n x
参数：x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `StrictMono.monotone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictMono f → Monotone f
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
· 使用定理 `AdicCompletion.of_bijective`：of_bijective : Function.Bijective (of I M)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.mkQ_apply`：mkQ_apply (x : M) : p.mkQ x = Quotient.mk x
· 使用定理 `AdicCompletion.eval_of`：eval_of (n : Nat) (x : M) : eval I M n (of I M x
) = mkQ (I ^ n • ⊤ : Submodule R M) x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearEquiv.apply_ofBijective_symm_apply`：apply_ofBijective_symm_apply [
RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂] {h} (x : M₂) : f ((ofBijective 
f h).symm x) = x
· 使用定理 `IsAdicComplete.StrictMono.extend_eq`：extend_eq (n : Nat) : extend ha f (
a n) = f n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mk_lift {n : ℕ} (x : M) :
    (Submodule.Quotient.mk (lift I ha f hf x)) = f n x := by
  simp only [lift, IsAdicComplete.lift, ofLinearEquiv, LinearMap.coe_comp, LinearEquiv.coe_coe,
    Function.comp_apply]
  rw [← mkQ_apply, ← eval_of]
  simp [extend_eq ha f hf]

@[simp]
/-
**IsAdicComplete.StrictMono.mkQ_comp_lift** 是 Mathlib 中的一个定理，位于命名空间 `IsAdicCompl
ete.StrictMono`。
形式化陈述：mkQ_comp_lift {n : Nat} : mkQ (I ^ (a n) • ⊤ : Submodule R N) ∘ₗ (lift I h
a f hf) = f n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `StrictMono.monotone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictMono f → Monotone f
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsAdicComplete.StrictMono.mk_lift`：mk_lift {n : Nat} (x : M) : (Submodul
e.Quotient.mk (lift I ha f hf x)) = f n x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mkQ_comp_lift {n : ℕ} :
    mkQ (I ^ (a n) • ⊤ : Submodule R N) ∘ₗ (lift I ha f hf) = f n := by
  ext; simp
/-
**IsAdicComplete.StrictMono.eq_lift** 是 Mathlib 中的一个定理，位于命名空间 `IsAdicComplete.St
rictMono`。
形式化陈述：eq_lift {F : M ->ₗ[R] N} (hF : forall n, mkQ _ ∘ₗ F = f n) : F = lift I ha
 f hf
参数：hF : forall n, mkQ _ ∘ₗ F = f n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `StrictMono.monotone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictMono f → Monotone f
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
· 使用定理 `IsHausdorff.StrictMono.funext`：IsHausdorff.StrictMono.funext {M : Type*}
 [IsHausdorff I N] {f g : M -> N} {a : Nat -> Nat} (ha : StrictMono a) (h : fora
ll n m, Submodule.Q…
· 使用定理 `IsAdicComplete.toIsHausdorff`：∀ {R : Type u_1} {inst : CommRing R} {I : 
Ideal R} {M : Type u_4} {inst_1 : AddCommGroup M} {inst_2 : _root_.Module R M}  
 [self : IsAdicCom…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsAdicComplete.StrictMono.mk_lift`：mk_lift {n : Nat} (x : M) : (Submodul
e.Quotient.mk (lift I ha f hf x)) = f n x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eq_lift {F : M →ₗ[R] N}
    (hF : ∀ n, mkQ _ ∘ₗ F = f n) : F = lift I ha f hf := by
  apply DFunLike.coe_injective
  apply IsHausdorff.StrictMono.funext I ha
  intro n m
  simp [← hF n]

end StrictMono

/-
**IsAdicComplete.bot** 是 Mathlib 中的一个实例，位于命名空间 `IsAdicComplete`。
形式化陈述：bot : IsAdicComplete (⊥ : Ideal R) M where  protected theorem subsingleton
 (h : IsAdicComplete (⊤ : Ideal R) M) : Subsingleton M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance bot : IsAdicComplete (⊥ : Ideal R) M where
/-
**IsAdicComplete.subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `IsAdicComplete`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] (M : Type u_4) [inst_1 : AddCommGroup
 M] [inst_2 : _root_.Module R M],   IsAdicComplete ⊤ M → Subsingleton M
参数：M : Type u_4。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsHausdorff.subsingleton`：∀ {R : Type u_1} [inst : CommRing R] {M : Type
 u_4} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M],   IsHausdorff ⊤ M 
→ Subsingleton…
· 使用定理 `IsAdicComplete.toIsHausdorff`：∀ {R : Type u_1} {inst : CommRing R} {I : 
Ideal R} {M : Type u_4} {inst_1 : AddCommGroup M} {inst_2 : _root_.Module R M}  
 [self : IsAdicCom…
-/
protected theorem subsingleton (h : IsAdicComplete (⊤ : Ideal R) M) : Subsingleton M :=
  h.1.subsingleton
/-
**IsAdicComplete.** 是 Mathlib 中的一个实例，位于命名空间 `IsAdicComplete`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) of_subsingleton [Subsingleton M] : IsAdicComplete I M where

open Finset
/-
**IsAdicComplete.le_jacobson_bot** 是 Mathlib 中的一个定理，位于命名空间 `IsAdicComplete`。
形式化陈述：le_jacobson_bot [IsAdicComplete I R] : I <= (⊥ : Ideal R).jacobson
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.neg_mem_iff`：∀ {α : Type u} [inst : Ring α] (I : Ideal α) {a : α},
 -a ∈ I ↔ a ∈ I
· 使用定理 `Ideal.mem_jacobson_bot`：mem_jacobson_bot {x : R} : x in jacobson (⊥ : Id
eal R) ↔ forall y, IsUnit (x * y + 1)
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Ideal.mul_top`：mul_top [I.IsTwoSided] : I * ⊤ = I
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `add_tsub_cancel_of_le`：add_tsub_cancel_of_le (h : a <= b) : a + (b - a) 
= b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Finset.sum_range_add`：∀ {M : Type u_4} [inst : AddCommMonoid M] (f : ℕ →
 M) (n m : ℕ),   ∑ x ∈ Finset.range (n + m), f x = ∑ x ∈ Finset.range n, f x + ∑
 x ∈ Finse…
· 使用定理 `sub_sub`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b c : α), 
a - b - c = a - (b + c)
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `neg_mem_iff`：∀ {S : Type u_3} {G : Type u_4} [inst : InvolutiveNeg G] {x
 : SetLike S G} [NegMemClass S G] {H : S} {x_1 : G},   -x_1 ∈ H ↔ x_1 ∈ H
· 使用定理 `NonUnitalSubringClass.toNegMemClass`：∀ {S : Type u_1} {R : Type u} {inst
 : NonUnitalNonAssocRing R} {inst_1 : SetLike S R}   [self : NonUnitalSubringCla
ss S R], NegMemClass S R
· 使用定理 `instNonUnitalSubringClassIdeal`：∀ {R : Type u_1} [inst : Ring R], NonUni
talSubringClass (Ideal R) R
· 使用定理 `Submodule.sum_mem`：∀ {R : Type u} {M : Type v} {ι : Type w} [inst : Semi
ring R] [inst_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodu
le R M)…
· 使用定理 `mul_pow`：mul_pow {ea₁ b c₁ : Nat} {xa₁ : R} (_ : ea₁ * b = c₁) (_ : a₂ ^
 b = c₂) : (xa₁ ^ ea₁ * a₂ : R) ^ b = xa₁ ^ c₁ * c₂
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Ideal.mul_mem_right`：mul_mem_right {α} {a : α} (b : α) [Semiring α] (I :
 Ideal α) [I.IsTwoSided] (h : a in I) : a * b in I
· 使用定理 `Ideal.pow_mem_pow`：pow_mem_pow {x : R} (hx : x in I) (n : Nat) : x ^ n i
n I ^ n
· 使用定理 `IsPrecomplete.prec`：IsPrecomplete.prec (_ : IsPrecomplete I M) {f : Nat 
-> M} : (forall {m n}, m <= n -> f m ≡ f n [SMOD (I ^ m • ⊤ : Submodule R M)]) -
> exists…
· 使用定理 `IsAdicComplete.toIsPrecomplete`：∀ {R : Type u_1} {inst : CommRing R} {I 
: Ideal R} {M : Type u_4} {inst_1 : AddCommGroup M} {inst_2 : _root_.Module R M}
   [self : IsAdicCom…
· 使用定理 `isUnit_iff_exists_inv`：isUnit_iff_exists_inv [Monoid M] [IsDedekindFinit
eMonoid M] {a : M} : IsUnit a ↔ exists b, a * b = 1
· 使用定理 `instIsDedekindFiniteMonoid`：∀ (M : Type u_2) [inst : CommMonoid M], IsDe
dekindFiniteMonoid M
（共 80 条，此处仅展示前 30 条）
-/
theorem le_jacobson_bot [IsAdicComplete I R] : I ≤ (⊥ : Ideal R).jacobson := by
  intro x hx
  rw [← Ideal.neg_mem_iff, Ideal.mem_jacobson_bot]
  intro y
  rw [add_comm]
  let f : ℕ → R := fun n => ∑ i ∈ range n, (x * y) ^ i
  have hf : ∀ m n, m ≤ n → f m ≡ f n [SMOD I ^ m • (⊤ : Submodule R R)] := by
    intro m n h
    simp only [f, smul_eq_mul, Ideal.mul_top, SModEq.sub_mem]
    rw [← add_tsub_cancel_of_le h, Finset.sum_range_add, ← sub_sub, sub_self, zero_sub,
      @neg_mem_iff]
    apply Submodule.sum_mem
    intro n _
    rw [mul_pow, pow_add, mul_assoc]
    exact Ideal.mul_mem_right _ (I ^ m) (Ideal.pow_mem_pow hx m)
  obtain ⟨L, hL⟩ := IsPrecomplete.prec toIsPrecomplete @hf
  rw [isUnit_iff_exists_inv]
  use L
  rw [← sub_eq_zero, neg_mul]
  apply IsHausdorff.haus (toIsHausdorff : IsHausdorff I R)
  intro n
  specialize hL n
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at hL ⊢
  rw [sub_zero]
  suffices (1 - x * y) * f n - 1 ∈ I ^ n by
    convert! Ideal.sub_mem _ this (Ideal.mul_mem_left _ (1 + -(x * y)) hL) using 1
    ring
  cases n
  · simp only [Ideal.one_eq_top, pow_zero, mem_top]
  · rw [← neg_sub _ (1 : R), neg_mul, mul_geom_sum, neg_sub, sub_sub, add_comm (_ ^ _), ← sub_sub,
      sub_self, zero_sub, @neg_mem_iff, mul_pow]
    exact Ideal.mul_mem_right _ (I ^ _) (Ideal.pow_mem_pow hx _)

end IsAdicComplete

