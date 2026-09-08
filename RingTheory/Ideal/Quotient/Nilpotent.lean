/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Nilpotent.Lemmas

/-!
# Nilpotent elements in quotient rings
-/

public section

/-
**Ideal.isRadical_iff_quotient_reduced** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ideal.isRadical_iff_quotient_reduced {R : Type*} [CommRing R] (I : Ideal R
) : I.IsRadical ↔ IsReduced (R ⧸ I)
参数：I : Ideal R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.mk_ker`：mk_ker {I : Ideal R} [I.IsTwoSided] : ker (Quotient.mk I) 
= I
· 使用定理 `RingHom.ker_isRadical_iff_reduced_of_surjective`：RingHom.ker_isRadical_i
ff_reduced_of_surjective {S F} [CommSemiring R] [Semiring S] [FunLike F R S] [Ri
ngHomClass F R S] {f : F} (hf : Funct…
· 使用定理 `Ideal.Quotient.mk_surjective`：mk_surjective : Function.Surjective (mk I)
-/
theorem Ideal.isRadical_iff_quotient_reduced {R : Type*} [CommRing R] (I : Ideal R) :
    I.IsRadical ↔ IsReduced (R ⧸ I) := by
  conv_lhs => rw [← @Ideal.mk_ker R _ I]
  exact RingHom.ker_isRadical_iff_reduced_of_surjective Quotient.mk_surjective

variable {S : Type*} [CommRing S] (I : Ideal S)

/-- Let `P` be a property on ideals. If `P` holds for square-zero ideals, and if
  `P I → P (J ⧸ I) → P J`, then `P` holds for all nilpotent ideals. -/
/-
**Ideal.IsNilpotent.induction_on** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ideal.IsNilpotent.induction_on (hI : IsNilpotent I) {P : forall ⦃S : Type 
_⦄ [CommRing S], Ideal S -> Prop} (h₁ : forall ⦃S : Type _⦄ [CommRing S], forall
 I : Ideal S, I ^ 2 = ⊥ -> P I) (h₂ : forall ⦃S : Type _⦄ [CommRing S], forall I
 J : Ideal S, I <= J -> P I -> P (J.map (Ideal.Quotient.mk I)) -> P J) : P I
参数：hI : IsNilpotent I；h₁ : forall ⦃S : Type _⦄ [CommRing S], forall I : Ideal S,
 I ^ 2 = ⊥ -> P I；h₂ : forall ⦃S : Type _⦄ [CommRing S], forall I J : Ideal S, I
 <= J -> P I -> P (J.map (Ideal.Quotient.mk I)) -> P J。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Nat.strong_induction_on`：∀ {p : ℕ → Prop} (n : ℕ), (∀ (n : ℕ), (∀ m < n,
 p m) → p n) → p n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.zero_eq_bot`：zero_eq_bot : (0 : Ideal R) = ⊥
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `subsingleton_of_bot_eq_top`：subsingleton_of_bot_eq_top (hα : (⊥ : α) = (
⊤ : α)) : Subsingleton α
· 使用定理 `Ideal.one_eq_top`：one_eq_top : (1 : Ideal R) = ⊤
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `Ideal.pow_le_self`：pow_le_self {n : Nat} (hn : n != 0) : I ^ n <= I
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用定理 `Nat.succ_eq_add_one`：∀ (n : ℕ), n.succ = n + 1
· 使用定理 `Ideal.pow_le_pow_right`：pow_le_pow_right {m n : Nat} (h : m <= n) : I ^ 
n <= I ^ m
· 使用定理 `Ideal.map_pow`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : CommSe
miring R] [inst_1 : CommSemiring S] [inst_2 : FunLike F R S]   [rc : RingHomClas
s F…
· 使用定理 `Ideal.map_quotient_self`：map_quotient_self (I : Ideal R) [I.IsTwoSided] 
: map (Quotient.mk I) I = ⊥

--- 原说明 ---
Let `P` be a property on ideals. If `P` holds for square-zero ideals, and if
  `P I → P (J ⧸ I) → P J`, then `P` holds for all nilpotent ideals.
-/
theorem Ideal.IsNilpotent.induction_on (hI : IsNilpotent I)
    {P : ∀ ⦃S : Type _⦄ [CommRing S], Ideal S → Prop}
    (h₁ : ∀ ⦃S : Type _⦄ [CommRing S], ∀ I : Ideal S, I ^ 2 = ⊥ → P I)
    (h₂ : ∀ ⦃S : Type _⦄ [CommRing S], ∀ I J : Ideal S, I ≤ J → P I →
      P (J.map (Ideal.Quotient.mk I)) → P J) :
    P I := by
  obtain ⟨n, hI : I ^ n = ⊥⟩ := hI
  induction n using Nat.strong_induction_on generalizing S with | _ n H
  by_cases hI' : I = ⊥
  · subst hI'
    apply h₁
    rw [← Ideal.zero_eq_bot, zero_pow two_ne_zero]
  rcases n with - | n
  · rw [pow_zero, Ideal.one_eq_top] at hI
    have := subsingleton_of_bot_eq_top hI.symm
    exact (hI' (Subsingleton.elim _ _)).elim
  rcases n with - | n
  · rw [pow_one] at hI
    exact (hI' hI).elim
  apply h₂ (I ^ 2) _ (Ideal.pow_le_self two_ne_zero)
  · apply H n.succ _ (I ^ 2)
    · rw [← pow_mul, eq_bot_iff, ← hI, Nat.succ_eq_add_one]
      apply Ideal.pow_le_pow_right (by lia)
    · exact n.succ.lt_succ_self
  · apply h₁
    rw [← Ideal.map_pow, Ideal.map_quotient_self]
/-
**IsNilpotent.isUnit_quotient_mk_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsNilpotent.isUnit_quotient_mk_iff {R : Type*} [CommRing R] {I : Ideal R} 
(hI : IsNilpotent I) {x : R} : IsUnit (Ideal.Quotient.mk I x) ↔ IsUnit x
参数：hI : IsNilpotent I。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Ideal.IsNilpotent.induction_on`：Ideal.IsNilpotent.induction_on (hI : IsN
ilpotent I) {P : forall ⦃S : Type _⦄ [CommRing S], Ideal S -> Prop} (h₁ : forall
 ⦃S : Type _⦄ [CommR…
· 使用定理 `Ideal.Quotient.mk_surjective`：mk_surjective : Function.Surjective (mk I)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
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
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `IsUnit.mul_val_inv`：mul_val_inv (h : IsUnit a) : a * ↑h.unit⁻¹ = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.mem_bot`：mem_bot {x : R} : x in (⊥ : Ideal R) ↔ x = 0
· 使用定理 `Ideal.pow_mem_pow`：pow_mem_pow {x : R} (hx : x in I) (n : Nat) : x ^ n i
n I ^ n
· 使用定理 `Ideal.Quotient.eq`：∀ {R : Type u} [inst : Ring R] {I : Ideal R} {x y : R
} [inst_1 : I.IsTwoSided],   (Ideal.Quotient.mk I) x = (Ideal.Quotient.mk I) y ↔
 x - y …
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
（共 70 条，此处仅展示前 30 条）
-/
theorem IsNilpotent.isUnit_quotient_mk_iff {R : Type*} [CommRing R] {I : Ideal R}
    (hI : IsNilpotent I) {x : R} : IsUnit (Ideal.Quotient.mk I x) ↔ IsUnit x := by
  refine ⟨?_, fun h => h.map <| Ideal.Quotient.mk I⟩
  revert x
  apply Ideal.IsNilpotent.induction_on (S := R) I hI <;> clear hI I
  swap
  · introv e h₁ h₂ h₃
    apply h₁
    apply h₂
    exact
      h₃.map
        ((DoubleQuot.quotQuotEquivQuotSup I J).trans
              (Ideal.quotEquivOfEq (sup_eq_right.mpr e))).symm.toRingHom
  · introv e H
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (↑H.unit⁻¹ : S ⧸ I)
    have : Ideal.Quotient.mk I (x * y) = Ideal.Quotient.mk I 1 := by
      rw [map_one, map_mul, hy, IsUnit.mul_val_inv]
    rw [Ideal.Quotient.eq] at this
    have : (x * y - 1) ^ 2 = 0 := by
      rw [← Ideal.mem_bot, ← e]
      exact Ideal.pow_mem_pow this _
    have : x * (y * (2 - x * y)) = 1 := by
      rw [eq_comm, ← sub_eq_zero, ← this]
      ring
    exact .of_mul_eq_one _ this
/-
**Ideal.Quotient.isUnit_mk_pow_iff_isUnit_mk** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ideal.Quotient.isUnit_mk_pow_iff_isUnit_mk {x : S} {n : Nat} (hn : n != 0)
 : IsUnit (Ideal.Quotient.mk (I ^ n) x) ↔ IsUnit (Ideal.Quotient.mk I x)
参数：hn : n != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsNilpotent.isUnit_quotient_mk_iff`：IsNilpotent.isUnit_quotient_mk_iff {
R : Type*} [CommRing R] {I : Ideal R} (hI : IsNilpotent I) {x : R} : IsUnit (Ide
al.Quotient.mk I x) ↔ Is…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Ideal.map_quotient_self`：map_quotient_self (I : Ideal R) [I.IsTwoSided] 
: map (Quotient.mk I) I = ⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Ideal.pow_le_self`：pow_le_self {n : Nat} (hn : n != 0) : I ^ n <= I
· 使用定理 `isUnit_map_iff`：isUnit_map_iff (f : F) [IsLocalHom f] (a : R) : IsUnit (
f a) ↔ IsUnit a
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `isLocalHom_equiv`：∀ {F : Type u_1} {M : Type u_3} {N : Type u_4} [inst :
 Monoid M] [inst_1 : Monoid N] [inst_2 : EquivLike F M N]   [MulEquivClass F M N
] (f :…
· 使用定理 `RingEquivClass.toMulEquivClass`：∀ {F : Type u_7} {R : Type u_8} {S : Typ
e u_9} {inst : Mul R} {inst_1 : Add R} {inst_2 : Mul S} {inst_3 : Add S}   {inst
_4 : EquivLike F R S…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Ideal.Quotient.isUnit_mk_pow_iff_isUnit_mk {x : S} {n : ℕ} (hn : n ≠ 0) :
    IsUnit (Ideal.Quotient.mk (I ^ n) x) ↔ IsUnit (Ideal.Quotient.mk I x) := by
  rw [← IsNilpotent.isUnit_quotient_mk_iff (I := Ideal.map (Ideal.Quotient.mk (I ^ n)) I)]
  · rw [← isUnit_map_iff (DoubleQuot.quotQuotEquivQuotOfLE (Ideal.pow_le_self hn))]
    rfl
  · use n
    simp [← Ideal.map_pow]
/-
**Ideal.Quotient.isUnit_mk_pow_iff_notMem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ideal.Quotient.isUnit_mk_pow_iff_notMem [I.IsMaximal] {n : Nat} (hn : n !=
 0) {x : S} : IsUnit (mk (I ^ n) x) ↔ x ∉ I
参数：hn : n != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.Quotient.isUnit_mk_pow_iff_isUnit_mk`：Ideal.Quotient.isUnit_mk_pow
_iff_isUnit_mk {x : S} {n : Nat} (hn : n != 0) : IsUnit (Ideal.Quotient.mk (I ^ 
n) x) ↔ IsUnit (Ideal.Quotient.m…
· 使用定理 `isUnit_iff_ne_zero`：isUnit_iff_ne_zero : IsUnit a ↔ a != 0
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Ideal.Quotient.eq_zero_iff_mem`：eq_zero_iff_mem : mk I a = 0 ↔ a in I
-/
theorem Ideal.Quotient.isUnit_mk_pow_iff_notMem [I.IsMaximal] {n : ℕ} (hn : n ≠ 0) {x : S} :
    IsUnit (mk (I ^ n) x) ↔ x ∉ I := by
  let := Ideal.Quotient.field I
  rw [isUnit_mk_pow_iff_isUnit_mk I hn, isUnit_iff_ne_zero]
  exact Ideal.Quotient.eq_zero_iff_mem.not
/-
**Ideal.Quotient.isUnit_mk_pow_of_notMem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ideal.Quotient.isUnit_mk_pow_of_notMem [I.IsMaximal] {n : Nat} {x : S} (hx
 : x ∉ I) : IsUnit (mk (I ^ n) x)
参数：hx : x ∉ I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.pow_eq_top_iff`：pow_eq_top_iff {n : Nat} : I ^ n = ⊤ ↔ I = ⊤ ∨ n =
 0
· 使用定理 `isUnit_of_subsingleton`：isUnit_of_subsingleton [Monoid M] [Subsingleton 
M] (a : M) : IsUnit a
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Ideal.Quotient.isUnit_mk_pow_iff_notMem`：Ideal.Quotient.isUnit_mk_pow_if
f_notMem [I.IsMaximal] {n : Nat} (hn : n != 0) {x : S} : IsUnit (mk (I ^ n) x) ↔
 x ∉ I
-/
theorem Ideal.Quotient.isUnit_mk_pow_of_notMem [I.IsMaximal] {n : ℕ} {x : S} (hx : x ∉ I) :
    IsUnit (mk (I ^ n) x) := by
  by_cases! hn : n = 0
  · rw [pow_eq_top_iff.mpr (Or.inr hn)]
    exact isUnit_of_subsingleton _
  exact (isUnit_mk_pow_iff_notMem I hn).mpr hx
