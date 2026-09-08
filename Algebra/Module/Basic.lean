/-
Copyright (c) 2015 Nathaniel Thomas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaniel Thomas, Jeremy Avigad, Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.GroupWithZero.Action.Units
public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Algebra.Ring.Invertible

/-!
# Further basic results about modules.

-/

public section

assert_not_exists Nonneg.inv Multiset

open Function Set

universe u v

variable {α R M M₂ : Type*}

@[simp]
/-
**Units.neg_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Units.neg_smul [Ring R] [AddCommGroup M] [Module R M] (u : Rˣ) (x : M) : -
u • x = -(u • x)
参数：u : Rˣ；x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Units.smul_def`：∀ {M : Type u_3} {α : Type u_5} [inst : Monoid M] [inst_
1 : SMul M α] (m : Mˣ) (a : α), m • a = ↑m • a
· 使用定理 `Units.val_neg`：∀ {α : Type u} [inst : Monoid α] [inst_1 : HasDistribNeg 
α] (u : αˣ), ↑(-u) = -↑u
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
-/
theorem Units.neg_smul [Ring R] [AddCommGroup M] [Module R M] (u : Rˣ) (x : M) :
    -u • x = -(u • x) := by
  rw [Units.smul_def, Units.val_neg, _root_.neg_smul, Units.smul_def]

@[simp]
/-
**invOf_two_smul_add_invOf_two_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：invOf_two_smul_add_invOf_two_smul (R) [Semiring R] [AddCommMonoid M] [Modu
le R M] [Invertible (2 : R)] (x : M) : (⅟2 : R) • x + (⅟2 : R) • x = x
参数：R；2 : R；x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Convex.combo_self`：Convex.combo_self {a b : R} (h : a + b = 1) (x : M) :
 a • x + b • x = x
· 使用定理 `invOf_two_add_invOf_two`：invOf_two_add_invOf_two [NonAssocSemiring R] [I
nvertible (2 : R)] : (⅟2 : R) + (⅟2 : R) = 1
-/
theorem invOf_two_smul_add_invOf_two_smul (R) [Semiring R] [AddCommMonoid M] [Module R M]
    [Invertible (2 : R)] (x : M) :
    (⅟2 : R) • x + (⅟2 : R) • x = x :=
  Convex.combo_self invOf_two_add_invOf_two _
/-
**map_inv_natCast_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_inv_natCast_smul [AddCommMonoid M] [AddCommMonoid M₂] {F : Type*} [Fun
Like F M M₂] [AddMonoidHomClass F M M₂] (f : F) (R S : Type*) [DivisionSemiring 
R] [DivisionSemiring S] [Module R M] [Module S M₂] (n : Nat) (x : M) : f ((n⁻¹ :
 R) • x) = (n⁻¹ : S) • f x
参数：f : F；R S : Type*；n : Nat；x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inv_smul_smul₀`：∀ {α : Type u_4} {β : Type u_5} [inst : GroupWithZero α]
 [inst_1 : MulAction α β] {a : α},   a ≠ 0 → ∀ (x : β), a⁻¹ • a • x = x
· 使用定理 `map_natCast_smul`：map_natCast_smul [AddCommMonoid M] [AddCommMonoid M₂] 
{F : Type*} [FunLike F M M₂] [AddMonoidHomClass F M M₂] (f : F) (R S : Type*) [S
emirin…
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用引理 `smul_inv_smul₀`：smul_inv_smul₀ (ha : a != 0) (x : β) : a • a⁻¹ • x = x
-/
theorem map_inv_natCast_smul [AddCommMonoid M] [AddCommMonoid M₂] {F : Type*} [FunLike F M M₂]
    [AddMonoidHomClass F M M₂] (f : F) (R S : Type*)
    [DivisionSemiring R] [DivisionSemiring S] [Module R M]
    [Module S M₂] (n : ℕ) (x : M) : f ((n⁻¹ : R) • x) = (n⁻¹ : S) • f x := by
  by_cases hR : (n : R) = 0 <;> by_cases hS : (n : S) = 0
  · simp [hR, hS, map_zero f]
  · suffices ∀ y, f y = 0 by rw [this, this, smul_zero]
    clear x
    intro x
    rw [← inv_smul_smul₀ hS (f x), ← map_natCast_smul f R S]
    simp [hR, map_zero f]
  · suffices ∀ y, f y = 0 by simp [this]
    clear x
    intro x
    rw [← smul_inv_smul₀ hR x, map_natCast_smul f R S, hS, zero_smul]
  · rw [← inv_smul_smul₀ hS (f _), ← map_natCast_smul f R S, smul_inv_smul₀ hR]
/-
**map_inv_intCast_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_inv_intCast_smul [AddCommGroup M] [AddCommGroup M₂] {F : Type*} [FunLi
ke F M M₂] [AddMonoidHomClass F M M₂] (f : F) (R S : Type*) [DivisionRing R] [Di
visionRing S] [Module R M] [Module S M₂] (z : Int) (x : M) : f ((z⁻¹ : R) • x) =
 (z⁻¹ : S) • f x
参数：f : F；R S : Type*；z : Int；x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.eq_nat_or_neg`：∀ (a : ℤ), ∃ n, a = ↑n ∨ a = -↑n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `map_inv_natCast_smul`：map_inv_natCast_smul [AddCommMonoid M] [AddCommMon
oid M₂] {F : Type*} [FunLike F M M₂] [AddMonoidHomClass F M M₂] (f : F) (R S : T
ype*) [Div…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
· 使用引理 `inv_neg`：inv_neg : (-a)⁻¹ = -a⁻¹
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_inv_intCast_smul [AddCommGroup M] [AddCommGroup M₂] {F : Type*} [FunLike F M M₂]
    [AddMonoidHomClass F M M₂] (f : F) (R S : Type*) [DivisionRing R] [DivisionRing S] [Module R M]
    [Module S M₂] (z : ℤ) (x : M) : f ((z⁻¹ : R) • x) = (z⁻¹ : S) • f x := by
  obtain ⟨n, rfl | rfl⟩ := z.eq_nat_or_neg
  · rw [Int.cast_natCast, Int.cast_natCast, map_inv_natCast_smul _ R S]
  · simp_rw [Int.cast_neg, Int.cast_natCast, inv_neg, neg_smul, map_neg,
      map_inv_natCast_smul _ R S]

/-- If `E` is a vector space over two division semirings `R` and `S`, then scalar multiplications
agree on inverses of natural numbers in `R` and `S`. -/
/-
**inv_natCast_smul_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inv_natCast_smul_eq {E : Type*} (R S : Type*) [AddCommMonoid E] [DivisionS
emiring R] [DivisionSemiring S] [Module R E] [Module S E] (n : Nat) (x : E) : (n
⁻¹ : R) • x = (n⁻¹ : S) • x
参数：R S : Type*；n : Nat；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_inv_natCast_smul`：map_inv_natCast_smul [AddCommMonoid M] [AddCommMon
oid M₂] {F : Type*} [FunLike F M M₂] [AddMonoidHomClass F M M₂] (f : F) (R S : T
ype*) [Div…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N

--- 原说明 ---
If `E` is a vector space over two division semirings `R` and `S`, then scalar mu
ltiplications
agree on inverses of natural numbers in `R` and `S`.
-/
theorem inv_natCast_smul_eq {E : Type*} (R S : Type*) [AddCommMonoid E] [DivisionSemiring R]
    [DivisionSemiring S] [Module R E] [Module S E] (n : ℕ) (x : E) :
    (n⁻¹ : R) • x = (n⁻¹ : S) • x :=
  map_inv_natCast_smul (AddMonoidHom.id E) R S n x

/-- If `E` is a vector space over two division rings `R` and `S`, then scalar multiplications
agree on inverses of integer numbers in `R` and `S`. -/
/-
**inv_intCast_smul_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inv_intCast_smul_eq {E : Type*} (R S : Type*) [AddCommGroup E] [DivisionRi
ng R] [DivisionRing S] [Module R E] [Module S E] (n : Int) (x : E) : (n⁻¹ : R) •
 x = (n⁻¹ : S) • x
参数：R S : Type*；n : Int；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_inv_intCast_smul`：map_inv_intCast_smul [AddCommGroup M] [AddCommGrou
p M₂] {F : Type*} [FunLike F M M₂] [AddMonoidHomClass F M M₂] (f : F) (R S : Typ
e*) [Divis…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N

--- 原说明 ---
If `E` is a vector space over two division rings `R` and `S`, then scalar multip
lications
agree on inverses of integer numbers in `R` and `S`.
-/
theorem inv_intCast_smul_eq {E : Type*} (R S : Type*) [AddCommGroup E] [DivisionRing R]
    [DivisionRing S] [Module R E] [Module S E] (n : ℤ) (x : E) : (n⁻¹ : R) • x = (n⁻¹ : S) • x :=
  map_inv_intCast_smul (AddMonoidHom.id E) R S n x

/-- If `E` is a vector space over a division semiring `R` and has a monoid action by `α`, then that
action commutes by scalar multiplication of inverses of natural numbers in `R`. -/
/-
**inv_natCast_smul_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inv_natCast_smul_comm {α E : Type*} (R : Type*) [AddCommMonoid E] [Divisio
nSemiring R] [Module R E] [DistribSMul α E] (n : Nat) (s : α) (x : E) : (n⁻¹ : R
) • s • x = s • (n⁻¹ : R) • x
参数：R : Type*；n : Nat；s : α；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_inv_natCast_smul`：map_inv_natCast_smul [AddCommMonoid M] [AddCommMon
oid M₂] {F : Type*} [FunLike F M M₂] [AddMonoidHomClass F M M₂] (f : F) (R S : T
ype*) [Div…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N

--- 原说明 ---
If `E` is a vector space over a division semiring `R` and has a monoid action by
 `α`, then that
action commutes by scalar multiplication of inverses of natural numbers in `R`.
-/
theorem inv_natCast_smul_comm {α E : Type*} (R : Type*) [AddCommMonoid E] [DivisionSemiring R]
    [Module R E] [DistribSMul α E] (n : ℕ) (s : α) (x : E) :
    (n⁻¹ : R) • s • x = s • (n⁻¹ : R) • x :=
  (map_inv_natCast_smul (DistribSMul.toAddMonoidHom E s) R R n x).symm

/-- If `E` is a vector space over a division ring `R` and has a monoid action by `α`, then that
action commutes by scalar multiplication of inverses of integers in `R` -/
/-
**inv_intCast_smul_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inv_intCast_smul_comm {α E : Type*} (R : Type*) [AddCommGroup E] [Division
Ring R] [Module R E] [DistribSMul α E] (n : Int) (s : α) (x : E) : (n⁻¹ : R) • s
 • x = s • (n⁻¹ : R) • x
参数：R : Type*；n : Int；s : α；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_inv_intCast_smul`：map_inv_intCast_smul [AddCommGroup M] [AddCommGrou
p M₂] {F : Type*} [FunLike F M M₂] [AddMonoidHomClass F M M₂] (f : F) (R S : Typ
e*) [Divis…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N

--- 原说明 ---
If `E` is a vector space over a division ring `R` and has a monoid action by `α`
, then that
action commutes by scalar multiplication of inverses of integers in `R`
-/
theorem inv_intCast_smul_comm {α E : Type*} (R : Type*) [AddCommGroup E] [DivisionRing R]
    [Module R E] [DistribSMul α E] (n : ℤ) (s : α) (x : E) :
    (n⁻¹ : R) • s • x = s • (n⁻¹ : R) • x :=
  (map_inv_intCast_smul (DistribSMul.toAddMonoidHom E s) R R n x).symm

namespace Function

/-
**Function.support_smul_subset_left** 是 Mathlib 中的一个引理，位于命名空间 `Function`。
形式化陈述：support_smul_subset_left [Zero R] [Zero M] [SMulWithZero R M] (f : α -> R)
 (g : α -> M) : support (f • g) subseteq support f
参数：f : α -> R；g : α -> M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Pi.smul_apply'`：smul_apply' [forall i, SMul (α i) (β i)] (s : forall i, 
α i) (x : forall i, β i) : (s • x) i = s i • x i
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
-/
lemma support_smul_subset_left [Zero R] [Zero M] [SMulWithZero R M] (f : α → R) (g : α → M) :
    support (f • g) ⊆ support f := fun x hfg hf ↦
  hfg <| by rw [Pi.smul_apply', hf, zero_smul]

-- Changed (2024-01-21): this lemma was generalised;
-- the old version is now called `support_const_smul_subset`.
/-
**Function.support_smul_subset_right** 是 Mathlib 中的一个引理，位于命名空间 `Function`。
形式化陈述：support_smul_subset_right [Zero M] [SMulZeroClass R M] (f : α -> R) (g : α
 -> M) : support (f • g) subseteq support g
参数：f : α -> R；g : α -> M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Pi.smul_apply'`：smul_apply' [forall i, SMul (α i) (β i)] (s : forall i, 
α i) (x : forall i, β i) : (s • x) i = s i • x i
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
-/
lemma support_smul_subset_right [Zero M] [SMulZeroClass R M] (f : α → R) (g : α → M) :
    support (f • g) ⊆ support g :=
  fun x hbf hf ↦ hbf <| by rw [Pi.smul_apply', hf, smul_zero]
/-
**Function.support_const_smul_of_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Function`。
形式化陈述：support_const_smul_of_ne_zero [Semiring R] [IsDomain R] [AddCommMonoid M] 
[Module R M] [Module.IsTorsionFree R M] (c : R) (g : α -> M) (hc : c != 0) : sup
port (c • g) = support g
参数：c : R；g : α -> M；hc : c != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用引理 `smul_ne_zero_iff_right`：smul_ne_zero_iff_right (hr : r != 0) : r • m != 
0 ↔ m != 0
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
-/
lemma support_const_smul_of_ne_zero [Semiring R] [IsDomain R] [AddCommMonoid M] [Module R M]
    [Module.IsTorsionFree R M] (c : R) (g : α → M) (hc : c ≠ 0) : support (c • g) = support g :=
  ext fun _ ↦ smul_ne_zero_iff_right hc
/-
**Function.support_smul** 是 Mathlib 中的一个引理，位于命名空间 `Function`。
形式化陈述：support_smul [Semiring R] [IsDomain R] [AddCommMonoid M] [Module R M] [Mod
ule.IsTorsionFree R M] (f : α -> R) (g : α -> M) : support (f • g) = support f i
nter support g
参数：f : α -> R；g : α -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用引理 `smul_ne_zero_iff`：smul_ne_zero_iff : r • m != 0 ↔ r != 0 ∧ m != 0
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
-/
lemma support_smul [Semiring R] [IsDomain R] [AddCommMonoid M] [Module R M]
    [Module.IsTorsionFree R M] (f : α → R) (g : α → M) : support (f • g) = support f ∩ support g :=
  ext fun _ => smul_ne_zero_iff
/-
**Function.support_const_smul_subset** 是 Mathlib 中的一个引理，位于命名空间 `Function`。
形式化陈述：support_const_smul_subset [Zero M] [SMulZeroClass R M] (a : R) (f : α -> M
) : support (a • f) subseteq support f
参数：a : R；f : α -> M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Function.support_smul_subset_right`：support_smul_subset_right [Zero M] [
SMulZeroClass R M] (f : α -> R) (g : α -> M) : support (f • g) subseteq support 
g
-/
lemma support_const_smul_subset [Zero M] [SMulZeroClass R M] (a : R) (f : α → M) :
    support (a • f) ⊆ support f := support_smul_subset_right (fun _ ↦ a) f

end Function

namespace Set
section SMulZeroClass
variable [Zero M] [SMulZeroClass R M]

/-
**Set.indicator_smul_apply** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：indicator_smul_apply (s : Set α) (r : α -> R) (f : α -> M) (a : α) : indic
ator s (fun a => r a • f a) a = r a • indicator s f a
参数：s : Set α；r : α -> R；f : α -> M；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
-/
lemma indicator_smul_apply (s : Set α) (r : α → R) (f : α → M) (a : α) :
    indicator s (fun a ↦ r a • f a) a = r a • indicator s f a := by
  dsimp only [indicator]
  split_ifs
  exacts [rfl, (smul_zero (r a)).symm]
/-
**Set.indicator_smul** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：indicator_smul (s : Set α) (r : α -> R) (f : α -> M) : indicator s (fun a 
=> r a • f a) = fun a => r a • indicator s f a
参数：s : Set α；r : α -> R；f : α -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Set.indicator_smul_apply`：indicator_smul_apply (s : Set α) (r : α -> R) 
(f : α -> M) (a : α) : indicator s (fun a => r a • f a) a = r a • indicator s f 
a
-/
lemma indicator_smul (s : Set α) (r : α → R) (f : α → M) :
    indicator s (fun a ↦ r a • f a) = fun a ↦ r a • indicator s f a :=
  funext <| indicator_smul_apply s r f
/-
**Set.indicator_const_smul_apply** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：indicator_const_smul_apply (s : Set α) (r : R) (f : α -> M) (a : α) : indi
cator s (r • f ·) a = r • indicator s f a
参数：s : Set α；r : R；f : α -> M；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.indicator_smul_apply`：indicator_smul_apply (s : Set α) (r : α -> R) 
(f : α -> M) (a : α) : indicator s (fun a => r a • f a) a = r a • indicator s f 
a
-/
lemma indicator_const_smul_apply (s : Set α) (r : R) (f : α → M) (a : α) :
    indicator s (r • f ·) a = r • indicator s f a :=
  indicator_smul_apply s (fun _ ↦ r) f a
/-
**Set.indicator_const_smul** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：indicator_const_smul (s : Set α) (r : R) (f : α -> M) : indicator s (r • f
 ·) = (r • indicator s f ·)
参数：s : Set α；r : R；f : α -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Set.indicator_const_smul_apply`：indicator_const_smul_apply (s : Set α) (
r : R) (f : α -> M) (a : α) : indicator s (r • f ·) a = r • indicator s f a
-/
lemma indicator_const_smul (s : Set α) (r : R) (f : α → M) :
    indicator s (r • f ·) = (r • indicator s f ·) :=
  funext <| indicator_const_smul_apply s r f

end SMulZeroClass

section SMulWithZero
variable [Zero R] [Zero M] [SMulWithZero R M]

/-
**Set.indicator_smul_apply_left** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：indicator_smul_apply_left (s : Set α) (r : α -> R) (f : α -> M) (a : α) : 
indicator s (fun a => r a • f a) a = indicator s r a • f a
参数：s : Set α；r : α -> R；f : α -> M；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
-/
lemma indicator_smul_apply_left (s : Set α) (r : α → R) (f : α → M) (a : α) :
    indicator s (fun a ↦ r a • f a) a = indicator s r a • f a := by
  dsimp only [indicator]
  split_ifs
  exacts [rfl, (zero_smul _ (f a)).symm]
/-
**Set.indicator_smul_left** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：indicator_smul_left (s : Set α) (r : α -> R) (f : α -> M) : indicator s (f
un a => r a • f a) = fun a => indicator s r a • f a
参数：s : Set α；r : α -> R；f : α -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Set.indicator_smul_apply_left`：indicator_smul_apply_left (s : Set α) (r 
: α -> R) (f : α -> M) (a : α) : indicator s (fun a => r a • f a) a = indicator 
s r a • f a
-/
lemma indicator_smul_left (s : Set α) (r : α → R) (f : α → M) :
    indicator s (fun a ↦ r a • f a) = fun a ↦ indicator s r a • f a :=
  funext <| indicator_smul_apply_left _ _ _
/-
**Set.indicator_smul_const_apply** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：indicator_smul_const_apply (s : Set α) (r : α -> R) (m : M) (a : α) : indi
cator s (r · • m) a = indicator s r a • m
参数：s : Set α；r : α -> R；m : M；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.indicator_smul_apply_left`：indicator_smul_apply_left (s : Set α) (r 
: α -> R) (f : α -> M) (a : α) : indicator s (fun a => r a • f a) a = indicator 
s r a • f a
-/
lemma indicator_smul_const_apply (s : Set α) (r : α → R) (m : M) (a : α) :
    indicator s (r · • m) a = indicator s r a • m := indicator_smul_apply_left _ _ _ _
/-
**Set.indicator_smul_const** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：indicator_smul_const (s : Set α) (r : α -> R) (m : M) : indicator s (r · •
 m) = (indicator s r · • m)
参数：s : Set α；r : α -> R；m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Set.indicator_smul_const_apply`：indicator_smul_const_apply (s : Set α) (
r : α -> R) (m : M) (a : α) : indicator s (r · • m) a = indicator s r a • m
-/
lemma indicator_smul_const (s : Set α) (r : α → R) (m : M) :
    indicator s (r · • m) = (indicator s r · • m) :=
  funext <| indicator_smul_const_apply _ _ _

end SMulWithZero

section MulZeroOneClass

variable [MulZeroOneClass R]

/-
**Set.smul_indicator_one_apply** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：smul_indicator_one_apply (s : Set α) (r : R) (a : α) : r • s.indicator (1 
: α -> R) a = s.indicator (fun _ => r) a
参数：s : Set α；r : R；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma smul_indicator_one_apply (s : Set α) (r : R) (a : α) :
    r • s.indicator (1 : α → R) a = s.indicator (fun _ ↦ r) a := by
  simp_rw [← indicator_const_smul_apply, Pi.one_apply, smul_eq_mul, mul_one]

end MulZeroOneClass
end Set

