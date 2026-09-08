/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Nilpotent.Lemmas

import Mathlib.Data.Fintype.Order

/-!
# Nilpotent maps on finite modules

-/

public section

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

/-
**Module.End.isNilpotent_iff_of_finite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.End.isNilpotent_iff_of_finite [Module.Finite R M] {f : End R M} : I
sNilpotent f ↔ forall m : M, exists n : Nat, (f ^ n) m = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Module.Finite.fg_top`：∀ {R : Type u_1} {M : Type u_4} {inst : Semiring R
} {inst_1 : AddCommMonoid M} {inst_2 : _root_.Module R M}   [self : Module.Finit
e R M], ⊤.…
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Submodule.span_induction`：span_induction {p : (x : M) -> x in span R s -
> Prop} (mem : forall (x) (h : x in s), p x (subset_span h)) (zero : p 0 (Submod
ule.zero_mem _…
· 使用定理 `Module.End.pow_map_zero_of_le`：pow_map_zero_of_le {f : End R M} {m : M} 
{k l : Nat} (hk : k <= l) (hm : (f ^ k) m = 0) : (f ^ l) m = 0
· 使用定理 `Finset.le_sup`：le_sup {b : β} (hb : b in s) : f b <= s.sup f
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
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem Module.End.isNilpotent_iff_of_finite [Module.Finite R M] {f : End R M} :
    IsNilpotent f ↔ ∀ m : M, ∃ n : ℕ, (f ^ n) m = 0 := by
  refine ⟨fun ⟨n, hn⟩ m ↦ ⟨n, by simp [hn]⟩, fun h ↦ ?_⟩
  rcases Module.Finite.fg_top (R := R) (M := M) with ⟨S, hS⟩
  choose g hg using h
  use Finset.sup S g
  ext m
  have hm : m ∈ Submodule.span R S := by simp [hS]
  induction hm using Submodule.span_induction with
  | mem x hx => exact pow_map_zero_of_le (Finset.le_sup hx) (hg x)
  | zero => simp
  | add => simp_all
  | smul => simp_all

namespace Matrix

open scoped Matrix

variable {ι : Type*} [DecidableEq ι] [Fintype ι] {A : Matrix ι ι R}

@[simp]
/-
**Matrix.isNilpotent_transpose_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：isNilpotent_transpose_iff : IsNilpotent Aᵀ ↔ IsNilpotent A
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isNilpotent_transpose_iff :
    IsNilpotent Aᵀ ↔ IsNilpotent A := by
  simp_rw [IsNilpotent, ← transpose_pow, transpose_eq_zero]
/-
**Matrix.isNilpotent_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：isNilpotent_iff : IsNilpotent A ↔ forall v, exists n : Nat, A ^ n *ᵥ v = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isNilpotent_iff :
    IsNilpotent A ↔ ∀ v, ∃ n : ℕ, A ^ n *ᵥ v = 0 := by
  simp_rw [← isNilpotent_toLin'_iff, Module.End.isNilpotent_iff_of_finite, ← toLin'_pow,
    toLin'_apply]
/-
**Matrix.isNilpotent_iff_forall_row** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：isNilpotent_iff_forall_row : IsNilpotent A ↔ forall i, exists n : Nat, (A 
^ n).row i = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.isNilpotent_transpose_iff`：isNilpotent_transpose_iff : IsNilpoten
t Aᵀ ↔ IsNilpotent A
· 使用定理 `Matrix.isNilpotent_iff`：isNilpotent_iff : IsNilpotent A ↔ forall v, exis
ts n : Nat, A ^ n *ᵥ v = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matrix.mulVec_single`：mulVec_single [Fintype n] [DecidableEq n] [NonUnit
alNonAssocSemiring R] (M : Matrix m n R) (j : n) (x : R) : M *ᵥ Pi.single j x = 
MulOpposit…
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用引理 `Matrix.pow_row_eq_zero_of_le`：pow_row_eq_zero_of_le [Fintype n] [Decidab
leEq n] {M : Matrix n n R} {k l : Nat} {i : n} (h : (M ^ k).row i = 0) (h' : k <
= l) : (M ^ l).row…
· 使用引理 `Finite.le_ciSup`：le_ciSup (f : ι -> α) (i : ι) : f i <= ⨆ j, f j
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Matrix.mulVec_eq_sum`：mulVec_eq_sum [Fintype n] (v : n -> α) (M : Matrix
 m n α) : M *ᵥ v = ∑ i, MulOpposite.op (v i) • Mᵀ i
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Matrix.transpose_pow`：transpose_pow [CommSemiring α] [Fintype m] [Decida
bleEq m] (M : Matrix m m α) (k : Nat) : (M ^ k)ᵀ = Mᵀ ^ k
· 使用定理 `Matrix.transpose_transpose`：transpose_transpose (M : Matrix m n α) : Mᵀᵀ
 = M
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem isNilpotent_iff_forall_row :
    IsNilpotent A ↔ ∀ i, ∃ n : ℕ, (A ^ n).row i = 0 := by
  rw [← isNilpotent_transpose_iff, isNilpotent_iff]
  refine ⟨fun h i ↦ ?_, fun h v ↦ ?_⟩
  · obtain ⟨n, hn⟩ := h (Pi.single i 1)
    exact ⟨n, by simpa [← transpose_pow] using hn⟩
  · choose n hn using h
    suffices ∀ i, (A ^ ⨆ j, n j) i = 0 from ⟨⨆ j, n j, by simp [mulVec_eq_sum, this]⟩
    exact fun i ↦ pow_row_eq_zero_of_le (hn i) (Finite.le_ciSup n i)
/-
**Matrix.isNilpotent_iff_forall_col** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：isNilpotent_iff_forall_col : IsNilpotent A ↔ forall i, exists n : Nat, (A 
^ n).col i = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.isNilpotent_transpose_iff`：isNilpotent_transpose_iff : IsNilpoten
t Aᵀ ↔ IsNilpotent A
· 使用定理 `Matrix.isNilpotent_iff_forall_row`：isNilpotent_iff_forall_row : IsNilpot
ent A ↔ forall i, exists n : Nat, (A ^ n).row i = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isNilpotent_iff_forall_col :
    IsNilpotent A ↔ ∀ i, ∃ n : ℕ, (A ^ n).col i = 0 := by
  rw [← isNilpotent_transpose_iff, isNilpotent_iff_forall_row]
  simp_rw [← transpose_pow, row_transpose]

end Matrix

