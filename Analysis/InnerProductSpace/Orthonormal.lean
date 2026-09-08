/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Sébastien Gouëzel, Frédéric Dupuis
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.RingTheory.LocalRing.Basic

/-!
# Orthonormal sets

This file defines orthonormal sets in inner product spaces.

## Main results

- We define `Orthonormal`, a predicate on a function `v : ι → E`, and prove the existence of a
  maximal orthonormal set, `exists_maximal_orthonormal`.
- Bessel's inequality, `Orthonormal.tsum_inner_products_le`, states that given an orthonormal set
  `v` and a vector `x`, the sum of the norm-squares of the inner products `⟪v i, x⟫` is no more
  than the norm-square of `x`.

For the existence of orthonormal bases, Hilbert bases, etc., see the file
`Analysis.InnerProductSpace.projection`.
-/

@[expose] public section

noncomputable section

open RCLike Real Filter Module Topology ComplexConjugate Finsupp

open LinearMap (BilinForm)

variable {𝕜 E F : Type*} [RCLike 𝕜]

section OrthonormalSets_Seminormed

variable [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [SeminormedAddCommGroup F] [InnerProductSpace ℝ F]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

variable {ι : Type*} (𝕜)

/-- An orthonormal set of vectors in an `InnerProductSpace` -/
/-
**Orthonormal** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Orthonormal (v : ι -> E) : Prop
参数：v : ι -> E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An orthonormal set of vectors in an `InnerProductSpace`
-/
def Orthonormal (v : ι → E) : Prop :=
  (∀ i, ‖v i‖ = 1) ∧ Pairwise fun i j => ⟪v i, v j⟫ = 0

variable {𝕜}

@[simp]
/-
**Orthonormal.of_isEmpty** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Orthonormal.of_isEmpty [IsEmpty ι] (v : ι -> E) : Orthonormal 𝕜 v
参数：v : ι -> E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.pairwise`：∀ {α : Type u_1} {r : α → α → Prop} [Subsingleton
 α], Pairwise r
· 使用定理 `IsEmpty.instSubsingleton`：∀ {α : Sort u} [IsEmpty α], Subsingleton α
-/
lemma Orthonormal.of_isEmpty [IsEmpty ι] (v : ι → E) : Orthonormal 𝕜 v :=
  ⟨IsEmpty.elim ‹_›, Subsingleton.pairwise⟩

@[simp]
/-
**orthonormal_vecCons_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：orthonormal_vecCons_iff {n : Nat} {v : E} {vs : Fin n -> E} : Orthonormal 
𝕜 (Matrix.vecCons v vs) ↔ ‖v‖ = 1 ∧ (forall i, ⟪v, vs i⟫ = 0) ∧ Orthonormal 𝕜 vs
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instSymmEqInnerOfNat`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] 
[inst_1 : SeminormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E]   {ι : Sort
 u_4} (v :…
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
-/
lemma orthonormal_vecCons_iff {n : ℕ} {v : E} {vs : Fin n → E} :
    Orthonormal 𝕜 (Matrix.vecCons v vs) ↔ ‖v‖ = 1 ∧ (∀ i, ⟪v, vs i⟫ = 0) ∧ Orthonormal 𝕜 vs := by
  simp_rw [Orthonormal, pairwise_fin_succ_iff_of_isSymm, Fin.forall_fin_succ]
  tauto
/-
**Orthonormal.norm_eq_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Orthonormal.norm_eq_one {v : ι -> E} (h : Orthonormal 𝕜 v) (i : ι) : ‖v i‖
 = 1
参数：h : Orthonormal 𝕜 v；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma Orthonormal.norm_eq_one {v : ι → E} (h : Orthonormal 𝕜 v) (i : ι) :
    ‖v i‖ = 1 := h.1 i
/-
**Orthonormal.nnnorm_eq_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Orthonormal.nnnorm_eq_one {v : ι -> E} (h : Orthonormal 𝕜 v) (i : ι) : ‖v 
i‖₊ = 1
参数：h : Orthonormal 𝕜 v；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Orthonormal.norm_eq_one`：Orthonormal.norm_eq_one {v : ι -> E} (h : Ortho
normal 𝕜 v) (i : ι) : ‖v i‖ = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
-/
lemma Orthonormal.nnnorm_eq_one {v : ι → E} (h : Orthonormal 𝕜 v) (i : ι) :
    ‖v i‖₊ = 1 := by
  suffices (‖v i‖₊ : ℝ) = 1 by norm_cast at this
  simp [h.norm_eq_one]
/-
**Orthonormal.enorm_eq_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Orthonormal.enorm_eq_one {v : ι -> E} (h : Orthonormal 𝕜 v) (i : ι) : ‖v i
‖ₑ = 1
参数：h : Orthonormal 𝕜 v；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ofReal_norm`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (x : E), ENN
Real.ofReal ‖x‖ = ‖x‖ₑ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Orthonormal.norm_eq_one`：Orthonormal.norm_eq_one {v : ι -> E} (h : Ortho
normal 𝕜 v) (i : ι) : ‖v i‖ = 1
· 使用定理 `ENNReal.ofReal_one`：ENNReal.ofReal 1 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Orthonormal.enorm_eq_one {v : ι → E} (h : Orthonormal 𝕜 v) (i : ι) :
    ‖v i‖ₑ = 1 := by rw [← ofReal_norm]; simp [h.norm_eq_one]
/-
**Orthonormal.inner_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Orthonormal.inner_eq_zero {v : ι -> E} {i j : ι} (h : Orthonormal 𝕜 v) (hi
j : i != j) : ⟪v i, v j⟫ = 0
参数：h : Orthonormal 𝕜 v；hij : i != j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma Orthonormal.inner_eq_zero {v : ι → E} {i j : ι} (h : Orthonormal 𝕜 v) (hij : i ≠ j) :
    ⟪v i, v j⟫ = 0 := h.2 hij

/-- `if ... then ... else` characterization of an indexed set of vectors being orthonormal.  (Inner
product equals Kronecker delta.) -/
/-
**orthonormal_iff_ite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：orthonormal_iff_ite [DecidableEq ι] {v : ι -> E} : Orthonormal 𝕜 v ↔ foral
l i j, ⟪v i, v j⟫ = if i = j then (1 : 𝕜) else (0 : 𝕜)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inner_self_eq_norm_sq_to_K`：inner_self_eq_norm_sq_to_K (x : E) : ⟪x, x⟫ 
= (‖x‖ : 𝕜) ^ 2
· 使用引理 `Orthonormal.norm_eq_one`：Orthonormal.norm_eq_one {v : ι -> E} (h : Ortho
normal 𝕜 v) (i : ι) : ‖v i‖ = 1
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
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用引理 `Orthonormal.inner_eq_zero`：Orthonormal.inner_eq_zero {v : ι -> E} {i j :
 ι} (h : Orthonormal 𝕜 v) (hij : i != j) : ⟪v i, v j⟫ = 0
· 使用定理 `InnerProductSpace.norm_sq_eq_re_inner`：∀ {𝕜 : Type u_4} {E : Type u_5} {
inst : RCLike 𝕜} {inst_1 : SeminormedAddCommGroup E} [self : InnerProductSpace 𝕜
 E]   (x : E), ‖x‖ ^ 2 = RC…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `RCLike.one_re`：one_re : re (1 : K) = 1
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用引理 `sq_eq_sq₀`：sq_eq_sq₀ (ha : 0 <= a) (hb : 0 <= b) : a ^ 2 = b ^ 2 ↔ a = b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False

--- 原说明 ---
`if ... then ... else` characterization of an indexed set of vectors being ortho
normal.  (Inner
product equals Kronecker delta.)
-/
theorem orthonormal_iff_ite [DecidableEq ι] {v : ι → E} :
    Orthonormal 𝕜 v ↔ ∀ i j, ⟪v i, v j⟫ = if i = j then (1 : 𝕜) else (0 : 𝕜) := by
  constructor
  · intro hv i j
    split_ifs with h
    · simp [h, inner_self_eq_norm_sq_to_K, hv.norm_eq_one]
    · exact hv.inner_eq_zero h
  · intro h
    constructor
    · intro i
      have h' : ‖v i‖ ^ 2 = 1 ^ 2 := by
        rw [@norm_sq_eq_re_inner 𝕜, h i i]; simp
      have h₁ : 0 ≤ ‖v i‖ := norm_nonneg _
      have h₂ : (0 : ℝ) ≤ 1 := zero_le_one
      rwa [sq_eq_sq₀ h₁ h₂] at h'
    · intro i j hij
      simpa [hij] using h i j

@[simp]
/-
**orthonormal_subsingleton_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：orthonormal_subsingleton_iff [Subsingleton ι] {v : ι -> E} : Orthonormal 𝕜
 v ↔ forall i, ‖v i‖ = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `inner_self_eq_norm_sq_to_K`：inner_self_eq_norm_sq_to_K (x : E) : ⟪x, x⟫ 
= (‖x‖ : 𝕜) ^ 2
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Module.Free.instFaithfulSMulOfNontrivial`：∀ (R : Type u) (M : Type v) [i
nst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Mod
ule.Free R M] [Nontrivial M], …
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem orthonormal_subsingleton_iff [Subsingleton ι] {v : ι → E} :
    Orthonormal 𝕜 v ↔ ∀ i, ‖v i‖ = 1 := by
  simp [orthonormal_iff_ite, ← map_pow, pow_eq_one_iff_of_nonneg]

/-- `if ... then ... else` characterization of a set of vectors being orthonormal.  (Inner product
equals Kronecker delta.) -/
/-
**orthonormal_subtype_iff_ite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：orthonormal_subtype_iff_ite [DecidableEq E] {s : Set E} : Orthonormal 𝕜 (S
ubtype.val : s -> E) ↔ forall v in s, forall w in s, ⟪v, w⟫ = if v = w then 1 el
se 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `orthonormal_iff_ite`：orthonormal_iff_ite [DecidableEq ι] {v : ι -> E} : 
Orthonormal 𝕜 v ↔ forall i j, ⟪v i, v j⟫ = if i = j then (1 : 𝕜) else (0 : 𝕜)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
`if ... then ... else` characterization of a set of vectors being orthonormal.  
(Inner product
equals Kronecker delta.)
-/
theorem orthonormal_subtype_iff_ite [DecidableEq E] {s : Set E} :
    Orthonormal 𝕜 (Subtype.val : s → E) ↔ ∀ v ∈ s, ∀ w ∈ s, ⟪v, w⟫ = if v = w then 1 else 0 := by
  rw [orthonormal_iff_ite]
  simp

/-- The inner product of a linear combination of a set of orthonormal vectors with one of those
vectors picks out the coefficient of that vector. -/
/-
**Orthonormal.inner_right_finsupp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Orthonormal.inner_right_finsupp {v : ι -> E} (hv : Orthonormal 𝕜 v) (l : ι
 ->₀ 𝕜) (i : ι) : ⟪v i, linearCombination 𝕜 v l⟫ = l i
参数：hv : Orthonormal 𝕜 v；l : ι ->₀ 𝕜；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.inner_sum`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [in
st_1 : SeminormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E]   {ι : Type u_
4} {M :…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `inner_smul_right`：inner_smul_right (x y : E) (r : 𝕜) : ⟪x, r • y⟫ = r * 
⟪x, y⟫
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `orthonormal_iff_ite`：orthonormal_iff_ite [DecidableEq ι] {v : ι -> E} : 
Orthonormal 𝕜 v ↔ forall i j, ⟪v i, v j⟫ = if i = j then (1 : 𝕜) else (0 : 𝕜)
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Finsupp.sum_ite_eq`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [ins
t : Zero M] [inst_1 : AddCommMonoid N] [inst_2 : DecidableEq α]   (f : α →₀ M) (
a : α) (…
· 使用定理 `ite_not`：∀ {α : Sort u_1} (p : Prop) [inst : Decidable p] (x y : α), (if
 ¬p then x else y) = if p then y else x
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)

--- 原说明 ---
The inner product of a linear combination of a set of orthonormal vectors with o
ne of those
vectors picks out the coefficient of that vector.
-/
theorem Orthonormal.inner_right_finsupp {v : ι → E} (hv : Orthonormal 𝕜 v) (l : ι →₀ 𝕜) (i : ι) :
    ⟪v i, linearCombination 𝕜 v l⟫ = l i := by
  classical
  simp [linearCombination_apply, Finsupp.inner_sum, orthonormal_iff_ite.mp hv, inner_smul_right,
    eq_comm]

/-- The inner product of a linear combination of a set of orthonormal vectors with one of those
vectors picks out the coefficient of that vector. -/
/-
**Orthonormal.inner_right_sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Orthonormal.inner_right_sum {v : ι -> E} (hv : Orthonormal 𝕜 v) (l : ι -> 
𝕜) {s : Finset ι} {i : ι} (hi : i in s) : ⟪v i, ∑ i in s, l i • v i⟫ = l i
参数：hv : Orthonormal 𝕜 v；l : ι -> 𝕜；hi : i in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inner_sum`：inner_sum {ι : Type*} (s : Finset ι) (f : ι -> E) (x : E) : ⟪
x, ∑ i in s, f i⟫ = ∑ i in s, ⟪x, f i⟫
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `inner_smul_right`：inner_smul_right (x y : E) (r : 𝕜) : ⟪x, r • y⟫ = r * 
⟪x, y⟫
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `orthonormal_iff_ite`：orthonormal_iff_ite [DecidableEq ι] {v : ι -> E} : 
Orthonormal 𝕜 v ↔ forall i j, ⟪v i, v j⟫ = if i = j then (1 : 𝕜) else (0 : 𝕜)
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Finset.sum_ite_eq`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoid
 M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if 
a = x t…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The inner product of a linear combination of a set of orthonormal vectors with o
ne of those
vectors picks out the coefficient of that vector.
-/
theorem Orthonormal.inner_right_sum {v : ι → E} (hv : Orthonormal 𝕜 v) (l : ι → 𝕜) {s : Finset ι}
    {i : ι} (hi : i ∈ s) : ⟪v i, ∑ i ∈ s, l i • v i⟫ = l i := by
  classical
  simp [inner_sum, inner_smul_right, orthonormal_iff_ite.mp hv, hi]

/-- The inner product of a linear combination of a set of orthonormal vectors with one of those
vectors picks out the coefficient of that vector. -/
/-
**Orthonormal.inner_right_fintype** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Orthonormal.inner_right_fintype [Fintype ι] {v : ι -> E} (hv : Orthonormal
 𝕜 v) (l : ι -> 𝕜) (i : ι) : ⟪v i, ∑ i : ι, l i • v i⟫ = l i
参数：hv : Orthonormal 𝕜 v；l : ι -> 𝕜；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Orthonormal.inner_right_sum`：Orthonormal.inner_right_sum {v : ι -> E} (h
v : Orthonormal 𝕜 v) (l : ι -> 𝕜) {s : Finset ι} {i : ι} (hi : i in s) : ⟪v i, ∑
 i in s, l i • v …
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)

--- 原说明 ---
The inner product of a linear combination of a set of orthonormal vectors with o
ne of those
vectors picks out the coefficient of that vector.
-/
theorem Orthonormal.inner_right_fintype [Fintype ι] {v : ι → E} (hv : Orthonormal 𝕜 v) (l : ι → 𝕜)
    (i : ι) : ⟪v i, ∑ i : ι, l i • v i⟫ = l i :=
  hv.inner_right_sum l (Finset.mem_univ _)

/-- The inner product of a linear combination of a set of orthonormal vectors with one of those
vectors picks out the coefficient of that vector. -/
/-
**Orthonormal.inner_left_finsupp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Orthonormal.inner_left_finsupp {v : ι -> E} (hv : Orthonormal 𝕜 v) (l : ι 
->₀ 𝕜) (i : ι) : ⟪linearCombination 𝕜 v l, v i⟫ = conj (l i)
参数：hv : Orthonormal 𝕜 v；l : ι ->₀ 𝕜；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inner_conj_symm`：inner_conj_symm (x y : E) : ⟪y, x⟫† = ⟪x, y⟫
· 使用定理 `Orthonormal.inner_right_finsupp`：Orthonormal.inner_right_finsupp {v : ι 
-> E} (hv : Orthonormal 𝕜 v) (l : ι ->₀ 𝕜) (i : ι) : ⟪v i, linearCombination 𝕜 v
 l⟫ = l i

--- 原说明 ---
The inner product of a linear combination of a set of orthonormal vectors with o
ne of those
vectors picks out the coefficient of that vector.
-/
theorem Orthonormal.inner_left_finsupp {v : ι → E} (hv : Orthonormal 𝕜 v) (l : ι →₀ 𝕜) (i : ι) :
    ⟪linearCombination 𝕜 v l, v i⟫ = conj (l i) := by rw [← inner_conj_symm, hv.inner_right_finsupp]

/-- The inner product of a linear combination of a set of orthonormal vectors with one of those
vectors picks out the coefficient of that vector. -/
/-
**Orthonormal.inner_left_sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Orthonormal.inner_left_sum {v : ι -> E} (hv : Orthonormal 𝕜 v) (l : ι -> 𝕜
) {s : Finset ι} {i : ι} (hi : i in s) : ⟪∑ i in s, l i • v i, v i⟫ = conj (l i)
参数：hv : Orthonormal 𝕜 v；l : ι -> 𝕜；hi : i in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sum_inner`：sum_inner {ι : Type*} (s : Finset ι) (f : ι -> E) (x : E) : ⟪
∑ i in s, f i, x⟫ = ∑ i in s, ⟪f i, x⟫
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `inner_smul_left`：inner_smul_left (x y : E) (r : 𝕜) : ⟪r • x, y⟫ = r† * ⟪
x, y⟫
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `orthonormal_iff_ite`：orthonormal_iff_ite [DecidableEq ι] {v : ι -> E} : 
Orthonormal 𝕜 v ↔ forall i j, ⟪v i, v j⟫ = if i = j then (1 : 𝕜) else (0 : 𝕜)
· 使用定理 `mul_boole`：mul_boole {α} [MulZeroOneClass α] (P : Prop) [Decidable P] (a
 : α) : (a * if P then 1 else 0) = if P then a else 0
· 使用定理 `Finset.sum_ite_eq'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoi
d M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if
 x = a t…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `if_true`：∀ {α : Sort u_1} {x : Decidable True} (t e : α), (if True then 
t else e) = t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The inner product of a linear combination of a set of orthonormal vectors with o
ne of those
vectors picks out the coefficient of that vector.
-/
theorem Orthonormal.inner_left_sum {v : ι → E} (hv : Orthonormal 𝕜 v) (l : ι → 𝕜) {s : Finset ι}
    {i : ι} (hi : i ∈ s) : ⟪∑ i ∈ s, l i • v i, v i⟫ = conj (l i) := by
  classical
  simp only [sum_inner, inner_smul_left, orthonormal_iff_ite.mp hv, hi, mul_boole,
    Finset.sum_ite_eq', if_true]

/-- The inner product of a linear combination of a set of orthonormal vectors with one of those
vectors picks out the coefficient of that vector. -/
/-
**Orthonormal.inner_left_fintype** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Orthonormal.inner_left_fintype [Fintype ι] {v : ι -> E} (hv : Orthonormal 
𝕜 v) (l : ι -> 𝕜) (i : ι) : ⟪∑ i : ι, l i • v i, v i⟫ = conj (l i)
参数：hv : Orthonormal 𝕜 v；l : ι -> 𝕜；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Orthonormal.inner_left_sum`：Orthonormal.inner_left_sum {v : ι -> E} (hv 
: Orthonormal 𝕜 v) (l : ι -> 𝕜) {s : Finset ι} {i : ι} (hi : i in s) : ⟪∑ i in s
, l i • v i, v i…
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)

--- 原说明 ---
The inner product of a linear combination of a set of orthonormal vectors with o
ne of those
vectors picks out the coefficient of that vector.
-/
theorem Orthonormal.inner_left_fintype [Fintype ι] {v : ι → E} (hv : Orthonormal 𝕜 v) (l : ι → 𝕜)
    (i : ι) : ⟪∑ i : ι, l i • v i, v i⟫ = conj (l i) :=
  hv.inner_left_sum l (Finset.mem_univ _)

/-- The inner product of two linear combinations of a set of orthonormal vectors, expressed as
a sum over the first `Finsupp`. -/
/-
**Orthonormal.inner_finsupp_eq_sum_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Orthonormal.inner_finsupp_eq_sum_left {v : ι -> E} (hv : Orthonormal 𝕜 v) 
(l₁ l₂ : ι ->₀ 𝕜) : ⟪linearCombination 𝕜 v l₁, linearCombination 𝕜 v l₂⟫ = l₁.su
m fun i y => conj y * l₂ i
参数：hv : Orthonormal 𝕜 v；l₁ l₂ : ι ->₀ 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.linearCombination_apply`：linearCombination_apply (l : α ->₀ R) :
 linearCombination R v l = l.sum fun i a => a • v i
· 使用定理 `Finsupp.sum_inner`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [in
st_1 : SeminormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E]   {ι : Type u_
4} {M :…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `inner_smul_left`：inner_smul_left (x y : E) (r : 𝕜) : ⟪r • x, y⟫ = r† * ⟪
x, y⟫
· 使用定理 `Orthonormal.inner_right_finsupp`：Orthonormal.inner_right_finsupp {v : ι 
-> E} (hv : Orthonormal 𝕜 v) (l : ι ->₀ 𝕜) (i : ι) : ⟪v i, linearCombination 𝕜 v
 l⟫ = l i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The inner product of two linear combinations of a set of orthonormal vectors, ex
pressed as
a sum over the first `Finsupp`.
-/
theorem Orthonormal.inner_finsupp_eq_sum_left {v : ι → E} (hv : Orthonormal 𝕜 v) (l₁ l₂ : ι →₀ 𝕜) :
    ⟪linearCombination 𝕜 v l₁, linearCombination 𝕜 v l₂⟫ = l₁.sum fun i y => conj y * l₂ i := by
  simp [l₁.linearCombination_apply, Finsupp.sum_inner, hv.inner_right_finsupp, inner_smul_left]

/-- The inner product of two linear combinations of a set of orthonormal vectors, expressed as
a sum over the second `Finsupp`. -/
/-
**Orthonormal.inner_finsupp_eq_sum_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Orthonormal.inner_finsupp_eq_sum_right {v : ι -> E} (hv : Orthonormal 𝕜 v)
 (l₁ l₂ : ι ->₀ 𝕜) : ⟪linearCombination 𝕜 v l₁, linearCombination 𝕜 v l₂⟫ = l₂.s
um fun i y => conj (l₁ i) * y
参数：hv : Orthonormal 𝕜 v；l₁ l₂ : ι ->₀ 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.linearCombination_apply`：linearCombination_apply (l : α ->₀ R) :
 linearCombination R v l = l.sum fun i a => a • v i
· 使用定理 `Finsupp.inner_sum`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [in
st_1 : SeminormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E]   {ι : Type u_
4} {M :…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `inner_smul_right`：inner_smul_right (x y : E) (r : 𝕜) : ⟪x, r • y⟫ = r * 
⟪x, y⟫
· 使用定理 `Orthonormal.inner_left_finsupp`：Orthonormal.inner_left_finsupp {v : ι ->
 E} (hv : Orthonormal 𝕜 v) (l : ι ->₀ 𝕜) (i : ι) : ⟪linearCombination 𝕜 v l, v i
⟫ = conj (l i)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The inner product of two linear combinations of a set of orthonormal vectors, ex
pressed as
a sum over the second `Finsupp`.
-/
theorem Orthonormal.inner_finsupp_eq_sum_right {v : ι → E} (hv : Orthonormal 𝕜 v) (l₁ l₂ : ι →₀ 𝕜) :
    ⟪linearCombination 𝕜 v l₁, linearCombination 𝕜 v l₂⟫ = l₂.sum fun i y => conj (l₁ i) * y := by
  simp [l₂.linearCombination_apply, Finsupp.inner_sum, hv.inner_left_finsupp, mul_comm,
    inner_smul_right]

/-- The inner product of two linear combinations of a set of orthonormal vectors, expressed as
a sum. -/
/-
**Orthonormal.inner_sum** 是 Mathlib 中的一个定理，位于命名空间 `Orthonormal`。
形式化陈述：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLike 𝕜] [inst_1 : SeminormedAddC
ommGroup E] [inst_2 : InnerProductSpace 𝕜 E]   {ι : Type u_4} {v : ι → E},   Ort
honormal 𝕜 v →     ∀ (l₁ l₂ : ι → 𝕜) (s : Finset ι),       inner 𝕜 (∑ i ∈ s, l₁ 
i • v i) (∑ i ∈ s, l₂ i • v i) = ∑ i ∈ s, (starRingEnd 𝕜) (l₁ i) * l₂ i
参数：l₁ l₂ : ι → 𝕜；s : Finset ι；∑ i ∈ s, l₁ i • v i；∑ i ∈ s, l₂ i • v i；starRingEn
d 𝕜；l₁ i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sum_inner`：sum_inner {ι : Type*} (s : Finset ι) (f : ι -> E) (x : E) : ⟪
∑ i in s, f i, x⟫ = ∑ i in s, ⟪f i, x⟫
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `inner_smul_left`：inner_smul_left (x y : E) (r : 𝕜) : ⟪r • x, y⟫ = r† * ⟪
x, y⟫
· 使用定理 `Orthonormal.inner_right_sum`：Orthonormal.inner_right_sum {v : ι -> E} (h
v : Orthonormal 𝕜 v) (l : ι -> 𝕜) {s : Finset ι} {i : ι} (hi : i in s) : ⟪v i, ∑
 i in s, l i • v …

--- 原说明 ---
The inner product of two linear combinations of a set of orthonormal vectors, ex
pressed as
a sum.
-/
protected theorem Orthonormal.inner_sum {v : ι → E} (hv : Orthonormal 𝕜 v) (l₁ l₂ : ι → 𝕜)
    (s : Finset ι) : ⟪∑ i ∈ s, l₁ i • v i, ∑ i ∈ s, l₂ i • v i⟫ = ∑ i ∈ s, conj (l₁ i) * l₂ i := by
  simp_rw [sum_inner, inner_smul_left]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [hv.inner_right_sum l₂ hi]

/--
The double sum of weighted inner products of pairs of vectors from an orthonormal sequence is the
sum of the weights.
-/
/-
**Orthonormal.inner_left_right_finset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Orthonormal.inner_left_right_finset {s : Finset ι} {v : ι -> E} (hv : Orth
onormal 𝕜 v) {a : ι -> ι -> 𝕜} : (∑ i in s, ∑ j in s, a i j • ⟪v j, v i⟫) = ∑ k 
in s, a k k
参数：hv : Orthonormal 𝕜 v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `orthonormal_iff_ite`：orthonormal_iff_ite [DecidableEq ι] {v : ι -> E} : 
Orthonormal 𝕜 v ↔ forall i j, ⟪v i, v j⟫ = if i = j then (1 : 𝕜) else (0 : 𝕜)
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Finset.sum_ite_eq'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoi
d M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if
 x = a t…
· 使用定理 `Finset.sum_ite_mem`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoi
d M] [inst_1 : DecidableEq ι] (s t : Finset ι) (f : ι → M),   (∑ i ∈ s, if i ∈ t
 then f …
· 使用定理 `Finset.inter_self`：inter_self (s : Finset α) : s inter s = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The double sum of weighted inner products of pairs of vectors from an orthonorma
l sequence is the
sum of the weights.
-/
theorem Orthonormal.inner_left_right_finset {s : Finset ι} {v : ι → E} (hv : Orthonormal 𝕜 v)
    {a : ι → ι → 𝕜} : (∑ i ∈ s, ∑ j ∈ s, a i j • ⟪v j, v i⟫) = ∑ k ∈ s, a k k := by
  classical
  simp [orthonormal_iff_ite.mp hv]

/-- An orthonormal set is linearly independent. -/
/-
**Orthonormal.linearIndependent** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Orthonormal.linearIndependent {v : ι -> E} (hv : Orthonormal 𝕜 v) : Linear
Independent 𝕜 v
参数：hv : Orthonormal 𝕜 v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `linearIndependent_iff`：linearIndependent_iff : LinearIndependent R v ↔ f
orall l, Finsupp.linearCombination R v l = 0 -> l = 0
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Orthonormal.inner_right_finsupp`：Orthonormal.inner_right_finsupp {v : ι 
-> E} (hv : Orthonormal 𝕜 v) (l : ι ->₀ 𝕜) (i : ι) : ⟪v i, linearCombination 𝕜 v
 l⟫ = l i
· 使用定理 `inner_zero_right`：inner_zero_right (x : E) : ⟪x, 0⟫ = 0

--- 原说明 ---
An orthonormal set is linearly independent.
-/
theorem Orthonormal.linearIndependent {v : ι → E} (hv : Orthonormal 𝕜 v) :
    LinearIndependent 𝕜 v := by
  rw [linearIndependent_iff]
  intro l hl
  ext i
  have key : ⟪v i, Finsupp.linearCombination 𝕜 v l⟫ = ⟪v i, 0⟫ := by rw [hl]
  simpa only [hv.inner_right_finsupp, inner_zero_right] using! key

/-- A subfamily of an orthonormal family (i.e., a composition with an injective map) is an
orthonormal family. -/
/-
**Orthonormal.comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Orthonormal.comp {ι' : Type*} {v : ι -> E} (hv : Orthonormal 𝕜 v) (f : ι' 
-> ι) (hf : Function.Injective f) : Orthonormal 𝕜 (v ∘ f)
参数：hv : Orthonormal 𝕜 v；f : ι' -> ι；hf : Function.Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `orthonormal_iff_ite`：orthonormal_iff_ite [DecidableEq ι] {v : ι -> E} : 
Orthonormal 𝕜 v ↔ forall i j, ⟪v i, v j⟫ = if i = j then (1 : 𝕜) else (0 : 𝕜)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A subfamily of an orthonormal family (i.e., a composition with an injective map)
 is an
orthonormal family.
-/
theorem Orthonormal.comp {ι' : Type*} {v : ι → E} (hv : Orthonormal 𝕜 v) (f : ι' → ι)
    (hf : Function.Injective f) : Orthonormal 𝕜 (v ∘ f) := by
  classical
  rw [orthonormal_iff_ite] at hv ⊢
  intro i j
  convert! hv (f i) (f j) using 1
  simp [hf.eq_iff]

/-- An injective family `v : ι → E` is orthonormal if and only if `Subtype.val : (range v) → E` is
orthonormal. -/
/-
**orthonormal_subtype_range** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：orthonormal_subtype_range {v : ι -> E} (hv : Function.Injective v) : Ortho
normal 𝕜 (Subtype.val : Set.range v -> E) ↔ Orthonormal 𝕜 v
参数：hv : Function.Injective v。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Orthonormal.comp`：Orthonormal.comp {ι' : Type*} {v : ι -> E} (hv : Ortho
normal 𝕜 v) (f : ι' -> ι) (hf : Function.Injective f) : Orthonormal 𝕜 (v ∘ f)
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.self_comp_ofInjective_symm`：self_comp_ofInjective_symm {α β} {f : 
α -> β} (hf : Injective f) : f ∘ (ofInjective f hf).symm = Subtype.val

--- 原说明 ---
An injective family `v : ι → E` is orthonormal if and only if `Subtype.val : (ra
nge v) → E` is
orthonormal.
-/
theorem orthonormal_subtype_range {v : ι → E} (hv : Function.Injective v) :
    Orthonormal 𝕜 (Subtype.val : Set.range v → E) ↔ Orthonormal 𝕜 v := by
  let f : ι ≃ Set.range v := Equiv.ofInjective v hv
  refine ⟨fun h => h.comp f f.injective, fun h => ?_⟩
  rw [← Equiv.self_comp_ofInjective_symm hv]
  exact h.comp f.symm f.symm.injective

/-- If `v : ι → E` is an orthonormal family, then `Subtype.val : (range v) → E` is an orthonormal
family. -/
/-
**Orthonormal.toSubtypeRange** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Orthonormal.toSubtypeRange {v : ι -> E} (hv : Orthonormal 𝕜 v) : Orthonorm
al 𝕜 (Subtype.val : Set.range v -> E)
参数：hv : Orthonormal 𝕜 v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `orthonormal_subtype_range`：orthonormal_subtype_range {v : ι -> E} (hv : 
Function.Injective v) : Orthonormal 𝕜 (Subtype.val : Set.range v -> E) ↔ Orthono
rmal 𝕜 v
· 使用定理 `LinearIndependent.injective`：LinearIndependent.injective [Nontrivial R] 
(hv : LinearIndependent R v) : Injective v
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Orthonormal.linearIndependent`：Orthonormal.linearIndependent {v : ι -> E
} (hv : Orthonormal 𝕜 v) : LinearIndependent 𝕜 v

--- 原说明 ---
If `v : ι → E` is an orthonormal family, then `Subtype.val : (range v) → E` is a
n orthonormal
family.
-/
theorem Orthonormal.toSubtypeRange {v : ι → E} (hv : Orthonormal 𝕜 v) :
    Orthonormal 𝕜 (Subtype.val : Set.range v → E) :=
  (orthonormal_subtype_range hv.linearIndependent.injective).2 hv

/-- A linear combination of some subset of an orthonormal set is orthogonal to other members of the
set. -/
/-
**Orthonormal.inner_finsupp_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Orthonormal.inner_finsupp_eq_zero {v : ι -> E} (hv : Orthonormal 𝕜 v) {s :
 Set ι} {i : ι} (hi : i ∉ s) {l : ι ->₀ 𝕜} (hl : l in Finsupp.supported 𝕜 𝕜 s) :
 ⟪Finsupp.linearCombination 𝕜 v l, v i⟫ = 0
参数：hv : Orthonormal 𝕜 v；hi : i ∉ s；hl : l in Finsupp.supported 𝕜 𝕜 s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orthonormal.inner_left_finsupp`：Orthonormal.inner_left_finsupp {v : ι ->
 E} (hv : Orthonormal 𝕜 v) (l : ι ->₀ 𝕜) (i : ι) : ⟪linearCombination 𝕜 v l, v i
⟫ = conj (l i)
· 使用定理 `Finsupp.mem_supported'`：mem_supported' {s : Set α} (p : α ->₀ M) : p in 
supported M R s ↔ forall x ∉ s, p x = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A linear combination of some subset of an orthonormal set is orthogonal to other
 members of the
set.
-/
theorem Orthonormal.inner_finsupp_eq_zero {v : ι → E} (hv : Orthonormal 𝕜 v) {s : Set ι} {i : ι}
    (hi : i ∉ s) {l : ι →₀ 𝕜} (hl : l ∈ Finsupp.supported 𝕜 𝕜 s) :
    ⟪Finsupp.linearCombination 𝕜 v l, v i⟫ = 0 := by
  rw [Finsupp.mem_supported'] at hl
  simp only [hv.inner_left_finsupp, hl i hi, map_zero]

/-- Given an orthonormal family, a second family of vectors is orthonormal if every vector equals
the corresponding vector in the original family or its negation. -/
/-
**Orthonormal.orthonormal_of_forall_eq_or_eq_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Orthonormal.orthonormal_of_forall_eq_or_eq_neg {v w : ι -> E} (hv : Orthon
ormal 𝕜 v) (hw : forall i, w i = v i ∨ w i = -v i) : Orthonormal 𝕜 w
参数：hv : Orthonormal 𝕜 v；hw : forall i, w i = v i ∨ w i = -v i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `orthonormal_iff_ite`：orthonormal_iff_ite [DecidableEq ι] {v : ι -> E} : 
Orthonormal 𝕜 v ↔ forall i j, ⟪v i, v j⟫ = if i = j then (1 : 𝕜) else (0 : 𝕜)
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `inner_neg_right`：inner_neg_right (x y : E) : ⟪x, -y⟫ = -⟪x, y⟫
· 使用定理 `inner_neg_left`：inner_neg_left (x y : E) : ⟪-x, y⟫ = -⟪x, y⟫
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a

--- 原说明 ---
Given an orthonormal family, a second family of vectors is orthonormal if every 
vector equals
the corresponding vector in the original family or its negation.
-/
theorem Orthonormal.orthonormal_of_forall_eq_or_eq_neg {v w : ι → E} (hv : Orthonormal 𝕜 v)
    (hw : ∀ i, w i = v i ∨ w i = -v i) : Orthonormal 𝕜 w := by
  classical
  rw [orthonormal_iff_ite] at *
  intro i j
  rcases hw i with hi | hi <;> rcases hw j with hj | hj <;>
    replace hv := hv i j <;> split_ifs at hv ⊢ with h <;>
    simpa only [hi, hj, h, inner_neg_right, inner_neg_left, neg_neg, eq_self_iff_true,
      neg_eq_zero] using hv

/- The material that follows, culminating in the existence of a maximal orthonormal subset, is
adapted from the corresponding development of the theory of linearly independent sets. See
`exists_linearIndependent` in particular. -/
variable (𝕜 E)

/-
**orthonormal_empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：orthonormal_empty : Orthonormal 𝕜 (fun x => x : (∅ : Set E) -> E)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Set.instIsEmptyElemEmptyCollection`：∀ (α : Type u), IsEmpty ↑∅
-/
theorem orthonormal_empty : Orthonormal 𝕜 (fun x => x : (∅ : Set E) → E) := by
  simp

variable {𝕜 E}
/-
**orthonormal_iUnion_of_directed** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：orthonormal_iUnion_of_directed {η : Type*} {s : η -> Set E} (hs : Directed
 (· subseteq ·) s) (h : forall i, Orthonormal 𝕜 (fun x => x : s i -> E)) : Ortho
normal 𝕜 (fun x => x : (⋃ i, s i) -> E)
参数：hs : Directed (· subseteq ·) s；h : forall i, Orthonormal 𝕜 (fun x => x : s i 
-> E)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `orthonormal_subtype_iff_ite`：orthonormal_subtype_iff_ite [DecidableEq E]
 {s : Set E} : Orthonormal 𝕜 (Subtype.val : s -> E) ↔ forall v in s, forall w in
 s, ⟪v, w⟫ = if v…
-/
theorem orthonormal_iUnion_of_directed {η : Type*} {s : η → Set E} (hs : Directed (· ⊆ ·) s)
    (h : ∀ i, Orthonormal 𝕜 (fun x => x : s i → E)) :
    Orthonormal 𝕜 (fun x => x : (⋃ i, s i) → E) := by
  classical
  rw [orthonormal_subtype_iff_ite]
  rintro x ⟨_, ⟨i, rfl⟩, hxi⟩ y ⟨_, ⟨j, rfl⟩, hyj⟩
  obtain ⟨k, hik, hjk⟩ := hs i j
  have h_orth : Orthonormal 𝕜 (fun x => x : s k → E) := h k
  rw [orthonormal_subtype_iff_ite] at h_orth
  exact h_orth x (hik hxi) y (hjk hyj)
/-
**orthonormal_sUnion_of_directed** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：orthonormal_sUnion_of_directed {s : Set (Set E)} (hs : DirectedOn (· subse
teq ·) s) (h : forall a in s, Orthonormal 𝕜 (fun x => ((x : a) : E))) : Orthonor
mal 𝕜 (fun x => x : ⋃₀ s -> E)
参数：Set E；hs : DirectedOn (· subseteq ·) s；h : forall a in s, Orthonormal 𝕜 (fun 
x => ((x : a) : E))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sUnion_eq_iUnion`：sUnion_eq_iUnion {s : Set (Set α)} : ⋃₀ s = ⋃ i : 
s, i
· 使用定理 `orthonormal_iUnion_of_directed`：orthonormal_iUnion_of_directed {η : Type
*} {s : η -> Set E} (hs : Directed (· subseteq ·) s) (h : forall i, Orthonormal 
𝕜 (fun x => x : s i …
· 使用定理 `DirectedOn.directed_val`：∀ {α : Type u_1} {r : α → α → Prop} {s : Set α}
, DirectedOn r s → Directed r Subtype.val
-/
theorem orthonormal_sUnion_of_directed {s : Set (Set E)} (hs : DirectedOn (· ⊆ ·) s)
    (h : ∀ a ∈ s, Orthonormal 𝕜 (fun x => ((x : a) : E))) :
    Orthonormal 𝕜 (fun x => x : ⋃₀ s → E) := by
  rw [Set.sUnion_eq_iUnion]; exact orthonormal_iUnion_of_directed hs.directed_val (by simpa using h)

/-- Given an orthonormal set `v` of vectors in `E`, there exists a maximal orthonormal set
containing it. -/
/-
**exists_maximal_orthonormal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_maximal_orthonormal {s : Set E} (hs : Orthonormal 𝕜 (Subtype.val : 
s -> E)) : exists w ⊇ s, Orthonormal 𝕜 (Subtype.val : w -> E) ∧ forall u ⊇ w, Or
thonormal 𝕜 (Subtype.val : u -> E) -> u = w
参数：hs : Orthonormal 𝕜 (Subtype.val : s -> E)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `zorn_subset_nonempty`：zorn_subset_nonempty (S : Set (Set α)) (H : forall
 c subseteq S, IsChain (· subseteq ·) c -> c.Nonempty -> exists ub in S, forall 
s in c, s …
· 使用定理 `orthonormal_sUnion_of_directed`：orthonormal_sUnion_of_directed {s : Set 
(Set E)} (hs : DirectedOn (· subseteq ·) s) (h : forall a in s, Orthonormal 𝕜 (f
un x => ((x : a) : E…
· 使用定理 `IsChain.directedOn`：IsChain.directedOn (H : IsChain r s) : DirectedOn r 
s
· 使用定理 `Set.subset_sUnion_of_mem`：subset_sUnion_of_mem {S : Set (Set α)} {t : Se
t α} (tS : t in S) : t subseteq ⋃₀ S
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Maximal.eq_of_ge`：∀ {α : Type u_2} {P : α → Prop} {x y : α} [inst : Part
ialOrder α], Maximal P x → P y → x ≤ y → y = x

--- 原说明 ---
Given an orthonormal set `v` of vectors in `E`, there exists a maximal orthonorm
al set
containing it.
-/
theorem exists_maximal_orthonormal {s : Set E} (hs : Orthonormal 𝕜 (Subtype.val : s → E)) :
    ∃ w ⊇ s, Orthonormal 𝕜 (Subtype.val : w → E) ∧
      ∀ u ⊇ w, Orthonormal 𝕜 (Subtype.val : u → E) → u = w := by
  have := zorn_subset_nonempty { b | Orthonormal 𝕜 (Subtype.val : b → E) } ?_ _ hs
  · obtain ⟨b, hb⟩ := this
    exact ⟨b, hb.1, hb.2.1, fun u hus hu => hb.2.eq_of_ge hu hus⟩
  · refine fun c hc cc _c0 => ⟨⋃₀ c, ?_, ?_⟩
    · exact orthonormal_sUnion_of_directed cc.directedOn fun x xc => hc xc
    · exact fun _ => Set.subset_sUnion_of_mem

open Module

/-- A family of orthonormal vectors with the correct cardinality forms a basis. -/
/-
**basisOfOrthonormalOfCardEqFinrank** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：basisOfOrthonormalOfCardEqFinrank [Fintype ι] [Nonempty ι] {v : ι -> E} (h
v : Orthonormal 𝕜 v) (card_eq : Fintype.card ι = finrank 𝕜 E) : Basis ι 𝕜 E
参数：hv : Orthonormal 𝕜 v；card_eq : Fintype.card ι = finrank 𝕜 E。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Orthonormal.linearIndependent`：Orthonormal.linearIndependent {v : ι -> E
} (hv : Orthonormal 𝕜 v) : LinearIndependent 𝕜 v

--- 原说明 ---
A family of orthonormal vectors with the correct cardinality forms a basis.
-/
def basisOfOrthonormalOfCardEqFinrank [Fintype ι] [Nonempty ι] {v : ι → E} (hv : Orthonormal 𝕜 v)
    (card_eq : Fintype.card ι = finrank 𝕜 E) : Basis ι 𝕜 E :=
  basisOfLinearIndependentOfCardEqFinrank hv.linearIndependent card_eq

@[simp]
/-
**coe_basisOfOrthonormalOfCardEqFinrank** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：coe_basisOfOrthonormalOfCardEqFinrank [Fintype ι] [Nonempty ι] {v : ι -> E
} (hv : Orthonormal 𝕜 v) (card_eq : Fintype.card ι = finrank 𝕜 E) : (basisOfOrth
onormalOfCardEqFinrank hv card_eq : ι -> E) = v
参数：hv : Orthonormal 𝕜 v；card_eq : Fintype.card ι = finrank 𝕜 E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `coe_basisOfLinearIndependentOfCardEqFinrank`：coe_basisOfLinearIndependen
tOfCardEqFinrank [Nonempty ι] {b : ι -> V} (lin_ind : LinearIndependent K b) (ca
rd_eq : Fintype.card ι = finrank …
· 使用定理 `Orthonormal.linearIndependent`：Orthonormal.linearIndependent {v : ι -> E
} (hv : Orthonormal 𝕜 v) : LinearIndependent 𝕜 v
-/
theorem coe_basisOfOrthonormalOfCardEqFinrank [Fintype ι] [Nonempty ι] {v : ι → E}
    (hv : Orthonormal 𝕜 v) (card_eq : Fintype.card ι = finrank 𝕜 E) :
    (basisOfOrthonormalOfCardEqFinrank hv card_eq : ι → E) = v :=
  coe_basisOfLinearIndependentOfCardEqFinrank _ _
/-
**Orthonormal.ne_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Orthonormal.ne_zero {v : ι -> E} (hv : Orthonormal 𝕜 v) (i : ι) : v i != 0
参数：hv : Orthonormal 𝕜 v；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ne_of_apply_ne`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) {x y : α}, f
 x ≠ f y → x ≠ y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem Orthonormal.ne_zero {v : ι → E} (hv : Orthonormal 𝕜 v) (i : ι) : v i ≠ 0 := by
  refine ne_of_apply_ne norm ?_
  rw [hv.1 i, norm_zero]
  simp

end OrthonormalSets_Seminormed

section Norm_Seminormed

open scoped InnerProductSpace

variable [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [SeminormedAddCommGroup F] [InnerProductSpace ℝ F]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

section

variable {ι : Type*} {ι' : Type*} {ι'' : Type*}
variable {E' : Type*} [SeminormedAddCommGroup E'] [InnerProductSpace 𝕜 E']
variable {E'' : Type*} [SeminormedAddCommGroup E''] [InnerProductSpace 𝕜 E'']

/-- A linear isometry preserves the property of being orthonormal. -/
/-
**LinearIsometry.orthonormal_comp_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearIsometry.orthonormal_comp_iff {v : ι -> E} (f : E ->ₗᵢ[𝕜] E') : Orth
onormal 𝕜 (f ∘ v) ↔ Orthonormal 𝕜 v
参数：f : E ->ₗᵢ[𝕜] E'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `LinearIsometry.inner_map_map`：LinearIsometry.inner_map_map (f : E ->ₗᵢ[𝕜
] E') (x y : E) : ⟪f x, f y⟫ = ⟪x, y⟫
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A linear isometry preserves the property of being orthonormal.
-/
theorem LinearIsometry.orthonormal_comp_iff {v : ι → E} (f : E →ₗᵢ[𝕜] E') :
    Orthonormal 𝕜 (f ∘ v) ↔ Orthonormal 𝕜 v := by
  classical simp_rw [orthonormal_iff_ite, Function.comp_apply, LinearIsometry.inner_map_map]

/-- A linear isometry preserves the property of being orthonormal. -/
/-
**Orthonormal.comp_linearIsometry** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Orthonormal.comp_linearIsometry {v : ι -> E} (hv : Orthonormal 𝕜 v) (f : E
 ->ₗᵢ[𝕜] E') : Orthonormal 𝕜 (f ∘ v)
参数：hv : Orthonormal 𝕜 v；f : E ->ₗᵢ[𝕜] E'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearIsometry.orthonormal_comp_iff`：LinearIsometry.orthonormal_comp_iff
 {v : ι -> E} (f : E ->ₗᵢ[𝕜] E') : Orthonormal 𝕜 (f ∘ v) ↔ Orthonormal 𝕜 v

--- 原说明 ---
A linear isometry preserves the property of being orthonormal.
-/
theorem Orthonormal.comp_linearIsometry {v : ι → E} (hv : Orthonormal 𝕜 v) (f : E →ₗᵢ[𝕜] E') :
    Orthonormal 𝕜 (f ∘ v) := by rwa [f.orthonormal_comp_iff]

/-- A linear isometric equivalence preserves the property of being orthonormal. -/
/-
**Orthonormal.comp_linearIsometryEquiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Orthonormal.comp_linearIsometryEquiv {v : ι -> E} (hv : Orthonormal 𝕜 v) (
f : E ≃ₗᵢ[𝕜] E') : Orthonormal 𝕜 (f ∘ v)
参数：hv : Orthonormal 𝕜 v；f : E ≃ₗᵢ[𝕜] E'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Orthonormal.comp_linearIsometry`：Orthonormal.comp_linearIsometry {v : ι 
-> E} (hv : Orthonormal 𝕜 v) (f : E ->ₗᵢ[𝕜] E') : Orthonormal 𝕜 (f ∘ v)

--- 原说明 ---
A linear isometric equivalence preserves the property of being orthonormal.
-/
theorem Orthonormal.comp_linearIsometryEquiv {v : ι → E} (hv : Orthonormal 𝕜 v) (f : E ≃ₗᵢ[𝕜] E') :
    Orthonormal 𝕜 (f ∘ v) :=
  hv.comp_linearIsometry f.toLinearIsometry

/-- A linear isometric equivalence, applied with `Basis.map`, preserves the property of being
orthonormal. -/
/-
**Orthonormal.mapLinearIsometryEquiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Orthonormal.mapLinearIsometryEquiv {v : Basis ι 𝕜 E} (hv : Orthonormal 𝕜 v
) (f : E ≃ₗᵢ[𝕜] E') : Orthonormal 𝕜 (v.map f.toLinearEquiv)
参数：hv : Orthonormal 𝕜 v；f : E ≃ₗᵢ[𝕜] E'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Orthonormal.comp_linearIsometryEquiv`：Orthonormal.comp_linearIsometryEqu
iv {v : ι -> E} (hv : Orthonormal 𝕜 v) (f : E ≃ₗᵢ[𝕜] E') : Orthonormal 𝕜 (f ∘ v)

--- 原说明 ---
A linear isometric equivalence, applied with `Basis.map`, preserves the property
 of being
orthonormal.
-/
theorem Orthonormal.mapLinearIsometryEquiv {v : Basis ι 𝕜 E} (hv : Orthonormal 𝕜 v)
    (f : E ≃ₗᵢ[𝕜] E') : Orthonormal 𝕜 (v.map f.toLinearEquiv) :=
  hv.comp_linearIsometryEquiv f

/-- A linear map that sends an orthonormal basis to orthonormal vectors is a linear isometry. -/
/-
**LinearMap.isometryOfOrthonormal** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LinearMap.isometryOfOrthonormal (f : E ->ₗ[𝕜] E') {v : Basis ι 𝕜 E} (hv : 
Orthonormal 𝕜 v) (hf : Orthonormal 𝕜 (f ∘ v)) : E ->ₗᵢ[𝕜] E'
参数：f : E ->ₗ[𝕜] E'；hv : Orthonormal 𝕜 v；hf : Orthonormal 𝕜 (f ∘ v)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A linear map that sends an orthonormal basis to orthonormal vectors is a linear 
isometry.
-/
def LinearMap.isometryOfOrthonormal (f : E →ₗ[𝕜] E') {v : Basis ι 𝕜 E} (hv : Orthonormal 𝕜 v)
    (hf : Orthonormal 𝕜 (f ∘ v)) : E →ₗᵢ[𝕜] E' :=
  f.isometryOfInner fun x y => by
    rw [← v.linearCombination_repr x, ← v.linearCombination_repr y,
      Finsupp.apply_linearCombination, Finsupp.apply_linearCombination,
      hv.inner_finsupp_eq_sum_left, hf.inner_finsupp_eq_sum_left]

@[simp]
/-
**LinearMap.coe_isometryOfOrthonormal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.coe_isometryOfOrthonormal (f : E ->ₗ[𝕜] E') {v : Basis ι 𝕜 E} (h
v : Orthonormal 𝕜 v) (hf : Orthonormal 𝕜 (f ∘ v)) : ⇑(f.isometryOfOrthonormal hv
 hf) = f
参数：f : E ->ₗ[𝕜] E'；hv : Orthonormal 𝕜 v；hf : Orthonormal 𝕜 (f ∘ v)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem LinearMap.coe_isometryOfOrthonormal (f : E →ₗ[𝕜] E') {v : Basis ι 𝕜 E}
    (hv : Orthonormal 𝕜 v) (hf : Orthonormal 𝕜 (f ∘ v)) : ⇑(f.isometryOfOrthonormal hv hf) = f :=
  rfl

@[simp]
/-
**LinearMap.isometryOfOrthonormal_toLinearMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.isometryOfOrthonormal_toLinearMap (f : E ->ₗ[𝕜] E') {v : Basis ι
 𝕜 E} (hv : Orthonormal 𝕜 v) (hf : Orthonormal 𝕜 (f ∘ v)) : (f.isometryOfOrthono
rmal hv hf).toLinearMap = f
参数：f : E ->ₗ[𝕜] E'；hv : Orthonormal 𝕜 v；hf : Orthonormal 𝕜 (f ∘ v)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem LinearMap.isometryOfOrthonormal_toLinearMap (f : E →ₗ[𝕜] E') {v : Basis ι 𝕜 E}
    (hv : Orthonormal 𝕜 v) (hf : Orthonormal 𝕜 (f ∘ v)) :
    (f.isometryOfOrthonormal hv hf).toLinearMap = f :=
  rfl

/-- A linear equivalence that sends an orthonormal basis to orthonormal vectors is a linear
isometric equivalence. -/
/-
**LinearEquiv.isometryOfOrthonormal** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LinearEquiv.isometryOfOrthonormal (f : E ≃ₗ[𝕜] E') {v : Basis ι 𝕜 E} (hv :
 Orthonormal 𝕜 v) (hf : Orthonormal 𝕜 (f ∘ v)) : E ≃ₗᵢ[𝕜] E'
参数：f : E ≃ₗ[𝕜] E'；hv : Orthonormal 𝕜 v；hf : Orthonormal 𝕜 (f ∘ v)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A linear equivalence that sends an orthonormal basis to orthonormal vectors is a
 linear
isometric equivalence.
-/
def LinearEquiv.isometryOfOrthonormal (f : E ≃ₗ[𝕜] E') {v : Basis ι 𝕜 E} (hv : Orthonormal 𝕜 v)
    (hf : Orthonormal 𝕜 (f ∘ v)) : E ≃ₗᵢ[𝕜] E' :=
  f.isometryOfInner fun x y => by
    rw [← LinearEquiv.coe_coe] at hf
    rw [← v.linearCombination_repr x, ← v.linearCombination_repr y,
      ← LinearEquiv.coe_coe f, Finsupp.apply_linearCombination,
      Finsupp.apply_linearCombination, hv.inner_finsupp_eq_sum_left, hf.inner_finsupp_eq_sum_left]

@[simp]
/-
**LinearEquiv.coe_isometryOfOrthonormal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearEquiv.coe_isometryOfOrthonormal (f : E ≃ₗ[𝕜] E') {v : Basis ι 𝕜 E} (
hv : Orthonormal 𝕜 v) (hf : Orthonormal 𝕜 (f ∘ v)) : ⇑(f.isometryOfOrthonormal h
v hf) = f
参数：f : E ≃ₗ[𝕜] E'；hv : Orthonormal 𝕜 v；hf : Orthonormal 𝕜 (f ∘ v)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem LinearEquiv.coe_isometryOfOrthonormal (f : E ≃ₗ[𝕜] E') {v : Basis ι 𝕜 E}
    (hv : Orthonormal 𝕜 v) (hf : Orthonormal 𝕜 (f ∘ v)) : ⇑(f.isometryOfOrthonormal hv hf) = f :=
  rfl

@[simp]
/-
**LinearEquiv.isometryOfOrthonormal_toLinearEquiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearEquiv.isometryOfOrthonormal_toLinearEquiv (f : E ≃ₗ[𝕜] E') {v : Basi
s ι 𝕜 E} (hv : Orthonormal 𝕜 v) (hf : Orthonormal 𝕜 (f ∘ v)) : (f.isometryOfOrth
onormal hv hf).toLinearEquiv = f
参数：f : E ≃ₗ[𝕜] E'；hv : Orthonormal 𝕜 v；hf : Orthonormal 𝕜 (f ∘ v)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem LinearEquiv.isometryOfOrthonormal_toLinearEquiv (f : E ≃ₗ[𝕜] E') {v : Basis ι 𝕜 E}
    (hv : Orthonormal 𝕜 v) (hf : Orthonormal 𝕜 (f ∘ v)) :
    (f.isometryOfOrthonormal hv hf).toLinearEquiv = f :=
  rfl

/-- A linear isometric equivalence that sends an orthonormal basis to a given orthonormal basis. -/
/-
**Orthonormal.equiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Orthonormal.equiv {v : Basis ι 𝕜 E} (hv : Orthonormal 𝕜 v) {v' : Basis ι' 
𝕜 E'} (hv' : Orthonormal 𝕜 v') (e : ι ≃ ι') : E ≃ₗᵢ[𝕜] E'
参数：hv : Orthonormal 𝕜 v；hv' : Orthonormal 𝕜 v'；e : ι ≃ ι'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A linear isometric equivalence that sends an orthonormal basis to a given orthon
ormal basis.
-/
def Orthonormal.equiv {v : Basis ι 𝕜 E} (hv : Orthonormal 𝕜 v) {v' : Basis ι' 𝕜 E'}
    (hv' : Orthonormal 𝕜 v') (e : ι ≃ ι') : E ≃ₗᵢ[𝕜] E' :=
  (v.equiv v' e).isometryOfOrthonormal hv
    (by
      have h : v.equiv v' e ∘ v = v' ∘ e := by
        ext i
        simp
      rw [h]
      exact hv'.comp _ e.injective)

@[simp]
/-
**Orthonormal.equiv_toLinearEquiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Orthonormal.equiv_toLinearEquiv {v : Basis ι 𝕜 E} (hv : Orthonormal 𝕜 v) {
v' : Basis ι' 𝕜 E'} (hv' : Orthonormal 𝕜 v') (e : ι ≃ ι') : (hv.equiv hv' e).toL
inearEquiv = v.equiv v' e
参数：hv : Orthonormal 𝕜 v；hv' : Orthonormal 𝕜 v'；e : ι ≃ ι'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Orthonormal.equiv_toLinearEquiv {v : Basis ι 𝕜 E} (hv : Orthonormal 𝕜 v)
    {v' : Basis ι' 𝕜 E'} (hv' : Orthonormal 𝕜 v') (e : ι ≃ ι') :
    (hv.equiv hv' e).toLinearEquiv = v.equiv v' e :=
  rfl

@[simp]
/-
**Orthonormal.equiv_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Orthonormal.equiv_apply {ι' : Type*} {v : Basis ι 𝕜 E} (hv : Orthonormal 𝕜
 v) {v' : Basis ι' 𝕜 E'} (hv' : Orthonormal 𝕜 v') (e : ι ≃ ι') (i : ι) : hv.equi
v hv' e (v i) = v' (e i)
参数：hv : Orthonormal 𝕜 v；hv' : Orthonormal 𝕜 v'；e : ι ≃ ι'；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.equiv_apply`：equiv_apply : b.equiv b' e (b i) = b' (e i)
-/
theorem Orthonormal.equiv_apply {ι' : Type*} {v : Basis ι 𝕜 E} (hv : Orthonormal 𝕜 v)
    {v' : Basis ι' 𝕜 E'} (hv' : Orthonormal 𝕜 v') (e : ι ≃ ι') (i : ι) :
    hv.equiv hv' e (v i) = v' (e i) :=
  Basis.equiv_apply _ _ _ _

@[simp]
/-
**Orthonormal.equiv_trans** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Orthonormal.equiv_trans {v : Basis ι 𝕜 E} (hv : Orthonormal 𝕜 v) {v' : Bas
is ι' 𝕜 E'} (hv' : Orthonormal 𝕜 v') (e : ι ≃ ι') {v'' : Basis ι'' 𝕜 E''} (hv'' 
: Orthonormal 𝕜 v'') (e' : ι' ≃ ι'') : (hv.equiv hv' e).trans (hv'.equiv hv'' e'
) = hv.equiv hv'' (e.trans e')
参数：hv : Orthonormal 𝕜 v；hv' : Orthonormal 𝕜 v'；e : ι ≃ ι'；hv'' : Orthonormal 𝕜 v
''；e' : ι' ≃ ι''。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.ext_linearIsometryEquiv`：Module.Basis.ext_linearIsometryEqu
iv {ι : Type*} (b : Basis ι R E) {f₁ f₂ : E ≃ₛₗᵢ[σ₁₂] E₂} (h : forall i, f₁ (b i
) = f₂ (b i)) : f₁ = f₂
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orthonormal.equiv_apply`：Orthonormal.equiv_apply {ι' : Type*} {v : Basis
 ι 𝕜 E} (hv : Orthonormal 𝕜 v) {v' : Basis ι' 𝕜 E'} (hv' : Orthonormal 𝕜 v') (e 
: ι ≃ ι') (i …
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Equiv.coe_trans`：∀ {α : Sort u} {β : Sort v} {γ : Sort w} (f : α ≃ β) (g
 : β ≃ γ), ⇑(f.trans g) = ⇑g ∘ ⇑f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Orthonormal.equiv_trans {v : Basis ι 𝕜 E} (hv : Orthonormal 𝕜 v) {v' : Basis ι' 𝕜 E'}
    (hv' : Orthonormal 𝕜 v') (e : ι ≃ ι') {v'' : Basis ι'' 𝕜 E''} (hv'' : Orthonormal 𝕜 v'')
    (e' : ι' ≃ ι'') : (hv.equiv hv' e).trans (hv'.equiv hv'' e') = hv.equiv hv'' (e.trans e') :=
  v.ext_linearIsometryEquiv fun i => by
    simp only [LinearIsometryEquiv.trans_apply, Orthonormal.equiv_apply, e.coe_trans,
      Function.comp_apply]
/-
**Orthonormal.map_equiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Orthonormal.map_equiv {v : Basis ι 𝕜 E} (hv : Orthonormal 𝕜 v) {v' : Basis
 ι' 𝕜 E'} (hv' : Orthonormal 𝕜 v') (e : ι ≃ ι') : v.map (hv.equiv hv' e).toLinea
rEquiv = v'.reindex e.symm
参数：hv : Orthonormal 𝕜 v；hv' : Orthonormal 𝕜 v'；e : ι ≃ ι'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.map_equiv`：map_equiv (b : Basis ι R M) (b' : Basis ι' R M')
 (e : ι ≃ ι') : b.map (b.equiv b' e) = b'.reindex e.symm
-/
theorem Orthonormal.map_equiv {v : Basis ι 𝕜 E} (hv : Orthonormal 𝕜 v) {v' : Basis ι' 𝕜 E'}
    (hv' : Orthonormal 𝕜 v') (e : ι ≃ ι') :
    v.map (hv.equiv hv' e).toLinearEquiv = v'.reindex e.symm :=
  v.map_equiv _ _

end

section

variable {ι : Type*} {ι' : Type*} {E' : Type*} [SeminormedAddCommGroup E'] [InnerProductSpace 𝕜 E']

@[simp]
/-
**Orthonormal.equiv_refl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Orthonormal.equiv_refl {v : Basis ι 𝕜 E} (hv : Orthonormal 𝕜 v) : hv.equiv
 hv (Equiv.refl ι) = LinearIsometryEquiv.refl 𝕜 E
参数：hv : Orthonormal 𝕜 v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.ext_linearIsometryEquiv`：Module.Basis.ext_linearIsometryEqu
iv {ι : Type*} (b : Basis ι R E) {f₁ f₂ : E ≃ₛₗᵢ[σ₁₂] E₂} (h : forall i, f₁ (b i
) = f₂ (b i)) : f₁ = f₂
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orthonormal.equiv_apply`：Orthonormal.equiv_apply {ι' : Type*} {v : Basis
 ι 𝕜 E} (hv : Orthonormal 𝕜 v) {v' : Basis ι' 𝕜 E'} (hv' : Orthonormal 𝕜 v') (e 
: ι ≃ ι') (i …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Orthonormal.equiv_refl {v : Basis ι 𝕜 E} (hv : Orthonormal 𝕜 v) :
    hv.equiv hv (Equiv.refl ι) = LinearIsometryEquiv.refl 𝕜 E :=
  v.ext_linearIsometryEquiv fun i => by
    simp only [Orthonormal.equiv_apply, Equiv.coe_refl, id, LinearIsometryEquiv.coe_refl]

@[simp]
/-
**Orthonormal.equiv_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Orthonormal.equiv_symm {v : Basis ι 𝕜 E} (hv : Orthonormal 𝕜 v) {v' : Basi
s ι' 𝕜 E'} (hv' : Orthonormal 𝕜 v') (e : ι ≃ ι') : (hv.equiv hv' e).symm = hv'.e
quiv hv e.symm
参数：hv : Orthonormal 𝕜 v；hv' : Orthonormal 𝕜 v'；e : ι ≃ ι'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.ext_linearIsometryEquiv`：Module.Basis.ext_linearIsometryEqu
iv {ι : Type*} (b : Basis ι R E) {f₁ f₂ : E ≃ₛₗᵢ[σ₁₂] E₂} (h : forall i, f₁ (b i
) = f₂ (b i)) : f₁ = f₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `LinearIsometryEquiv.injective`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Typ
e u_5} {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+*
 R₂} {σ₂₁ : R₂ →+* …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearIsometryEquiv.apply_symm_apply`：apply_symm_apply (x : E₂) : e (e.s
ymm x) = x
· 使用定理 `Orthonormal.equiv_apply`：Orthonormal.equiv_apply {ι' : Type*} {v : Basis
 ι 𝕜 E} (hv : Orthonormal 𝕜 v) {v' : Basis ι' 𝕜 E'} (hv' : Orthonormal 𝕜 v') (e 
: ι ≃ ι') (i …
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Orthonormal.equiv_symm {v : Basis ι 𝕜 E} (hv : Orthonormal 𝕜 v) {v' : Basis ι' 𝕜 E'}
    (hv' : Orthonormal 𝕜 v') (e : ι ≃ ι') : (hv.equiv hv' e).symm = hv'.equiv hv e.symm :=
  v'.ext_linearIsometryEquiv fun i =>
    (hv.equiv hv' e).injective <| by
      simp only [LinearIsometryEquiv.apply_symm_apply, Orthonormal.equiv_apply, e.apply_symm_apply]

end

end Norm_Seminormed

section BesselsInequality

variable [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

variable {ι : Type*} (x : E) {v : ι → E}

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-- Bessel's inequality for finite sums. -/
/-
**Orthonormal.sum_inner_products_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Orthonormal.sum_inner_products_le {s : Finset ι} (hv : Orthonormal 𝕜 v) : 
∑ i in s, ‖⟪v i, x⟫‖ ^ 2 <= ‖x‖ ^ 2
参数：hv : Orthonormal 𝕜 v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Orthonormal.inner_left_right_finset`：Orthonormal.inner_left_right_finset
 {s : Finset ι} {v : ι -> E} (hv : Orthonormal 𝕜 v) {a : ι -> ι -> 𝕜} : (∑ i in 
s, ∑ j in s, a i j • ⟪v j…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RCLike.mul_conj`：mul_conj (z : K) : z * conj z = ‖z‖ ^ 2
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `RCLike.ofReal_re`：ofReal_re : forall r : Real, re (r : K) = r
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `norm_sub_sq`：norm_sub_sq (x y : E) : ‖x - y‖ ^ 2 = ‖x‖ ^ 2 - 2 * re ⟪x, 
y⟫ + ‖y‖ ^ 2
· 使用定理 `sub_add`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b c : α), 
a - b + c = a - (b - c)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `InnerProductSpace.norm_sq_eq_re_inner`：∀ {𝕜 : Type u_4} {E : Type u_5} {
inst : RCLike 𝕜} {inst_1 : SeminormedAddCommGroup E} [self : InnerProductSpace 𝕜
 E]   (x : E), ‖x‖ ^ 2 = RC…
· 使用定理 `inner_sum`：inner_sum {ι : Type*} (s : Finset ι) (f : ι -> E) (x : E) : ⟪
x, ∑ i in s, f i⟫ = ∑ i in s, ⟪x, f i⟫
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `sum_inner`：sum_inner {ι : Type*} (s : Finset ι) (f : ι -> E) (x : E) : ⟪
∑ i in s, f i, x⟫ = ∑ i in s, ⟪f i, x⟫
· 使用定理 `inner_smul_right`：inner_smul_right (x y : E) (r : 𝕜) : ⟪x, r • y⟫ = r * 
⟪x, y⟫
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `inner_smul_left`：inner_smul_left (x y : E) (r : 𝕜) : ⟪r • x, y⟫ = r† * ⟪
x, y⟫
· 使用定理 `inner_conj_symm`：inner_conj_symm (x y : E) : ⟪y, x⟫† = ⟪x, y⟫
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `sub_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddRight
Mono α] {a b : α}, 0 ≤ a - b ↔ b ≤ a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R

--- 原说明 ---
Bessel's inequality for finite sums.
-/
theorem Orthonormal.sum_inner_products_le {s : Finset ι} (hv : Orthonormal 𝕜 v) :
    ∑ i ∈ s, ‖⟪v i, x⟫‖ ^ 2 ≤ ‖x‖ ^ 2 := by
  have h₂ :
    (∑ i ∈ s, ∑ j ∈ s, ⟪v i, x⟫ * ⟪x, v j⟫ * ⟪v j, v i⟫) = (∑ k ∈ s, ⟪v k, x⟫ * ⟪x, v k⟫ : 𝕜) := by
    exact hv.inner_left_right_finset
  have h₃ : ∀ z : 𝕜, re (z * conj z) = ‖z‖ ^ 2 := by
    intro z
    simp only [mul_conj]
    norm_cast
  suffices hbf : ‖x - ∑ i ∈ s, ⟪v i, x⟫ • v i‖ ^ 2 = ‖x‖ ^ 2 - ∑ i ∈ s, ‖⟪v i, x⟫‖ ^ 2 by
    rw [← sub_nonneg, ← hbf]
    simp only [norm_nonneg, pow_nonneg]
  rw [@norm_sub_sq 𝕜, sub_add]
  simp only [@InnerProductSpace.norm_sq_eq_re_inner 𝕜 E, inner_sum, sum_inner]
  simp only [inner_smul_right, two_mul, inner_smul_left, inner_conj_symm, ← mul_assoc, h₂,
    add_sub_cancel_right, sub_right_inj]
  simp only [map_sum, ← inner_conj_symm x, ← h₃]

/-- Bessel's inequality. -/
/-
**Orthonormal.tsum_inner_products_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Orthonormal.tsum_inner_products_le (hv : Orthonormal 𝕜 v) : ∑' i, ‖⟪v i, x
⟫‖ ^ 2 <= ‖x‖ ^ 2
参数：hv : Orthonormal 𝕜 v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tsum_le_of_sum_le'`：∀ {ι : Type u_1} {α : Type u_3} {L : SummationFilter
 ι} [inst : AddCommMonoid α] [inst_1 : Preorder α]   [inst_2 : TopologicalSpace 
α] [Orde…
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Orthonormal.sum_inner_products_le`：Orthonormal.sum_inner_products_le {s 
: Finset ι} (hv : Orthonormal 𝕜 v) : ∑ i in s, ‖⟪v i, x⟫‖ ^ 2 <= ‖x‖ ^ 2

--- 原说明 ---
Bessel's inequality.
-/
theorem Orthonormal.tsum_inner_products_le (hv : Orthonormal 𝕜 v) :
    ∑' i, ‖⟪v i, x⟫‖ ^ 2 ≤ ‖x‖ ^ 2 := by
  refine tsum_le_of_sum_le' ?_ fun s => hv.sum_inner_products_le x
  simp only [norm_nonneg, pow_nonneg]

/-- The sum defined in Bessel's inequality is summable. -/
/-
**Orthonormal.inner_products_summable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Orthonormal.inner_products_summable (hv : Orthonormal 𝕜 v) : Summable fun 
i => ‖⟪v i, x⟫‖ ^ 2
参数：hv : Orthonormal 𝕜 v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasSum_of_isLUB_of_nonneg`：∀ {ι : Type u_1} {α : Type u_3} [inst : AddCo
mmMonoid α] [inst_1 : LinearOrder α] [IsOrderedAddMonoid α]   [inst_3 : Topologi
calSpace α] [Or…
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `isLUB_ciSup`：isLUB_ciSup [Nonempty ι] {f : ι -> α} (H : BddAbove (range 
f)) : IsLUB (range f) (⨆ i, f i)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Orthonormal.sum_inner_products_le`：Orthonormal.sum_inner_products_le {s 
: Finset ι} (hv : Orthonormal 𝕜 v) : ∑ i in s, ‖⟪v i, x⟫‖ ^ 2 <= ‖x‖ ^ 2

--- 原说明 ---
The sum defined in Bessel's inequality is summable.
-/
theorem Orthonormal.inner_products_summable (hv : Orthonormal 𝕜 v) :
    Summable fun i => ‖⟪v i, x⟫‖ ^ 2 := by
  use ⨆ s : Finset ι, ∑ i ∈ s, ‖⟪v i, x⟫‖ ^ 2
  apply hasSum_of_isLUB_of_nonneg
  · intro b
    simp only [norm_nonneg, pow_nonneg]
  · refine isLUB_ciSup ?_
    use ‖x‖ ^ 2
    rintro y ⟨s, rfl⟩
    exact hv.sum_inner_products_le x

end BesselsInequality

