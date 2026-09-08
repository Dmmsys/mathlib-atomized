/-
Copyright (c) 2025 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
public import Mathlib.Algebra.Order.Hom.Monoid
public import Mathlib.Algebra.Order.Module.Defs

/-!
# Embedding of archimedean groups into reals

This file provides embedding of any archimedean groups into reals.

## Main declarations
* `Archimedean.embedReal` defines an injective `M →+o ℝ` for archimedean group `M` with a positive
  `1` element. `1` is preserved by the map.
* `Archimedean.exists_orderAddMonoidHom_real_injective` states there exists an injective `M →+o ℝ`
  for any archimedean group `M` without specifying the `1` element in `M`.
-/

@[expose] public section


variable {M : Type*}
variable [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M] [One M]

/-
**mul_smul_one_lt_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_smul_one_lt_iff {num : Int} {n den : Nat} (hn : 0 < n) {x : M} : (num 
* n) • 1 < (n * den : Int) • x ↔ num • 1 < den • x
参数：hn : 0 < n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `natCast_zsmul`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G) (n : ℕ),
 ↑n • a = n • a
· 使用引理 `lt_of_smul_lt_smul_left`：lt_of_smul_lt_smul_left [PosSMulReflectLT α β] 
(h : a • b₁ < a • b₂) (ha : 0 <= a) : b₁ < b₂
· 使用定理 `PosSMulStrictMono.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} [inst :
 Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : PartialOrder α]
   [inst_4 : PartialO…
· 使用定理 `instPosSMulStrictMonoIntOfIsOrderedAddMonoid`：∀ {G : Type u_3} [inst : P
artialOrder G] [inst_1 : AddCommGroup G] [IsOrderedAddMonoid G], PosSMulStrictMo
no ℤ G
· 使用定理 `Int.natCast_nonneg`：∀ (n : ℕ), 0 ≤ ↑n
· 使用定理 `zsmul_lt_zsmul_right`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 :
 PartialOrder α] [IsOrderedAddMonoid α] {n : ℤ} {a b : α},   0 < n → a < b → n •
 a < n • b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Int.natCast_pos`：∀ {n : ℕ}, 0 < ↑n ↔ 0 < n
-/
theorem mul_smul_one_lt_iff {num : ℤ} {n den : ℕ} (hn : 0 < n) {x : M} :
    (num * n) • 1 < (n * den : ℤ) • x ↔ num • 1 < den • x := by
  rw [mul_comm num, mul_smul, mul_smul, natCast_zsmul x den]
  exact ⟨fun h ↦ lt_of_smul_lt_smul_left h (Int.natCast_nonneg n),
    fun h ↦ zsmul_lt_zsmul_right (Int.natCast_pos.mpr hn) h⟩

/-- For `u v : ℚ` and `x y : M`, one can informally write
`u < x → v < y → u + v < x + y`. We formalize this using smul. -/
/-
**num_smul_one_lt_den_smul_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：num_smul_one_lt_den_smul_add {u v : Rat} {x y : M} (hu : u.num • 1 < u.den
 • x) (hv : v.num • 1 < v.den • y) : (u + v).num • 1 < (u + v).den • (x + y)
参数：hu : u.num • 1 < u.den • x；hv : v.num • 1 < v.den • y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mul_smul_one_lt_iff`：mul_smul_one_lt_iff {num : Int} {n den : Nat} (hn :
 0 < n) {x : M} : (num * n) • 1 < (n * den : Int) • x ↔ num • 1 < den • x
· 使用定理 `Rat.den_pos`：∀ (self : ℚ), 0 < self.den
· 使用定理 `Rat.add_num_den'`：add_num_den' (q r : Rat) : (q + r).num * q.den * r.den
 = (q.num * r.den + r.num * q.den) * (q + r).den
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用引理 `smul_lt_smul_iff_of_pos_left`：smul_lt_smul_iff_of_pos_left [PosSMulStric
tMono α β] [PosSMulReflectLT α β] (ha : 0 < a) : a • b₁ < a • b₂ ↔ b₁ < b₂
· 使用定理 `instPosSMulStrictMonoIntOfIsOrderedAddMonoid`：∀ {G : Type u_3} [inst : P
artialOrder G] [inst_1 : AddCommGroup G] [IsOrderedAddMonoid G], PosSMulStrictMo
no ℤ G
· 使用定理 `PosSMulStrictMono.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} [inst :
 Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : PartialOrder α]
   [inst_4 : PartialO…
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `add_lt_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftStrictMono α] [AddRightStrictMono α] {a b c d : α},   a < b → c < d → a + c < 
…
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
（共 32 条，此处仅展示前 30 条）

--- 原说明 ---
For `u v : ℚ` and `x y : M`, one can informally write
`u < x → v < y → u + v < x + y`. We formalize this using smul.
-/
theorem num_smul_one_lt_den_smul_add {u v : ℚ} {x y : M}
    (hu : u.num • 1 < u.den • x) (hv : v.num • 1 < v.den • y) :
    (u + v).num • 1 < (u + v).den • (x + y) := by
  have hu' : (u.num * v.den) • 1 < (u.den * v.den : ℤ) • x := by
    simpa [mul_comm] using (mul_smul_one_lt_iff v.den_pos).mpr hu
  suffices ((u + v).num * u.den * v.den) • 1 <
      ((u + v).den : ℤ) • (u.den * v.den : ℤ) • (x + y) by
    refine (mul_smul_one_lt_iff (mul_pos u.den_pos v.den_pos)).mp ?_
    rwa [Nat.cast_mul, ← mul_assoc, mul_comm _ ((u + v).den : ℤ), ← smul_eq_mul ((u + v).den : ℤ),
      smul_assoc]
  rw [Rat.add_num_den', mul_comm, ← smul_smul]
  rw [smul_lt_smul_iff_of_pos_left (by simpa using (u + v).den_pos)]
  rw [add_smul, smul_add]
  exact add_lt_add hu' ((mul_smul_one_lt_iff u.den_pos).mpr hv)

/-- Given `x` from `M`, one can informally write that, by transitivity,
`num / den ≤ x → x ≤ n → num / den ≤ n` for `den : ℕ` and `num n : ℕ`.
To avoid writing division for integer `num` and `den`, we express this in terms of
multiplication. -/
/-
**num_le_nat_mul_den** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：num_le_nat_mul_den [ZeroLEOneClass M] [NeZero (1 : M)] {num : Int} {den : 
Nat} {x : M} (h : num • 1 <= den • x) {n : Int} (hn : x <= n • 1) : num <= n * d
en
参数：1 : M；h : num • 1 <= den • x；hn : x <= n • 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_of_smul_le_smul_right`：le_of_smul_le_smul_right [SMulPosReflectLE α β
] (h : a₁ • b <= a₂ • b) (hb : 0 < b) : a₁ <= a₂
· 使用定理 `SMulPosStrictMono.toSMulPosReflectLE`：∀ {α : Type u_1} {β : Type u_2} [i
nst : SMul α β] [inst_1 : LinearOrder α] [inst_2 : Preorder β] [inst_3 : Zero β]
   [SMulPosStrictMono α β]…
· 使用定理 `instSMulPosStrictMonoIntOfIsOrderedAddMonoid`：∀ {G : Type u_3} [inst : P
artialOrder G] [inst_1 : AddCommGroup G] [IsOrderedAddMonoid G], SMulPosStrictMo
no ℤ G
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `natCast_zsmul`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G) (n : ℕ),
 ↑n • a = n • a
· 使用定理 `nsmul_le_nsmul_right`：∀ {M : Type u_3} [inst : AddMonoid M] [inst_1 : Pr
eorder M] [AddLeftMono M] [AddRightMono M] {a b : M},   a ≤ b → ∀ (i : ℕ), i • a
 ≤ i • b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p

--- 原说明 ---
Given `x` from `M`, one can informally write that, by transitivity,
`num / den ≤ x → x ≤ n → num / den ≤ n` for `den : ℕ` and `num n : ℕ`.
To avoid writing division for integer `num` and `den`, we express this in terms 
of
multiplication.
-/
theorem num_le_nat_mul_den [ZeroLEOneClass M] [NeZero (1 : M)]
    {num : ℤ} {den : ℕ} {x : M} (h : num • 1 ≤ den • x)
    {n : ℤ} (hn : x ≤ n • 1) : num ≤ n * den := by
  refine le_of_smul_le_smul_right (h.trans ?_) (by simp)
  rw [mul_comm, ← smul_smul]
  simpa using nsmul_le_nsmul_right hn den

namespace Archimedean

/-- Set of rational numbers that are less than the "number" `x / 1`.
Formally, these are numbers `p / q` such that `p • 1 < q • x`. -/
/-
**Archimedean.ratLt** 是 Mathlib 中的一个缩写定义，位于命名空间 `Archimedean`。
形式化陈述：ratLt (x : M) : Set Rat
参数：x : M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Set of rational numbers that are less than the "number" `x / 1`.
Formally, these are numbers `p / q` such that `p • 1 < q • x`.
-/
abbrev ratLt (x : M) : Set ℚ := {r | r.num • 1 < r.den • x}
/-
**Archimedean.mkRat_mem_ratLt** 是 Mathlib 中的一个定理，位于命名空间 `Archimedean`。
形式化陈述：mkRat_mem_ratLt {num : Int} {den : Nat} (hden : den != 0) {x : M} : mkRat 
num den in ratLt x ↔ num • 1 < den • x
参数：hden : den != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_ofPred`：mem_ofPred {a : α} {p : α -> Prop} : a in { x | p x } ↔ 
p a
· 使用引理 `Rat.mk'`：mk'_num_den (q : Rat) : mk' q.num q.den q.den_nz q.reduced = q
· 使用定理 `Rat.mkRat_num_den`：∀ {d : ℕ} {n n' : ℤ} {d' : ℕ} {z' : d' ≠ 0} {c : n'.n
atAbs.Coprime d'},   d ≠ 0 → mkRat n d = { num := n', den := d', den_nz := z', r
educed …
· 使用定理 `Rat.den_nz`：∀ (self : ℚ), self.den ≠ 0
· 使用定理 `Rat.reduced`：∀ (self : ℚ), self.num.natAbs.Coprime self.den
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `natCast_zsmul`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G) (n : ℕ),
 ↑n • a = n • a
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用引理 `smul_lt_smul_iff_of_pos_left`：smul_lt_smul_iff_of_pos_left [PosSMulStric
tMono α β] [PosSMulReflectLT α β] (ha : 0 < a) : a • b₁ < a • b₂ ↔ b₁ < b₂
· 使用定理 `instPosSMulStrictMonoNatOfIsOrderedAddMonoid`：∀ {M : Type u_3} [inst : P
artialOrder M] [inst_1 : AddCancelCommMonoid M] [IsOrderedAddMonoid M], PosSMulS
trictMono ℕ M
· 使用定理 `instPosSMulMonoNatOfIsOrderedAddMonoid`：∀ {M : Type u_3} [inst : Partial
Order M] [inst_1 : AddCommMonoid M] [IsOrderedAddMonoid M], PosSMulMono ℕ M
· 使用定理 `Nat.zero_lt_of_ne_zero`：∀ {a : ℕ}, a ≠ 0 → 0 < a
-/
theorem mkRat_mem_ratLt {num : ℤ} {den : ℕ} (hden : den ≠ 0) {x : M} :
    mkRat num den ∈ ratLt x ↔ num • 1 < den • x := by
  rw [Set.mem_ofPred]
  obtain ⟨m, hm0, hnum, hden⟩ := Rat.mkRat_num_den hden (show mkRat num den = _ by rfl)
  conv in num • 1 => rw [hnum, mul_comm, ← smul_smul, natCast_zsmul]
  conv in den • x => rw [hden, mul_comm, ← smul_smul]
  exact (smul_lt_smul_iff_of_pos_left (Nat.zero_lt_of_ne_zero hm0)).symm

/-- `ratLt` as a set of real numbers. -/
-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/-
**Archimedean.ratLt'** 是 Mathlib 中的一个缩写定义，位于命名空间 `Archimedean`。
形式化陈述：ratLt' (x : M) : Set Real
参数：x : M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable abbrev ratLt' (x : M) : Set ℝ := (Rat.castHom ℝ) '' (ratLt x)

/-- Mapping `M` to `ℝ`, defined as the supremum of `ratLt' x`. -/
noncomputable
/-
**Archimedean.embedRealFun** 是 Mathlib 中的一个缩写定义，位于命名空间 `Archimedean`。
形式化陈述：embedRealFun (x : M)
参数：x : M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
abbrev embedRealFun (x : M) := sSup (ratLt' x)

variable [ZeroLEOneClass M] [NeZero (1 : M)] [Archimedean M]
/-
**Archimedean.ratLt_bddAbove** 是 Mathlib 中的一个定理，位于命名空间 `Archimedean`。
形式化陈述：ratLt_bddAbove (x : M) : BddAbove (ratLt x)
参数：x : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Archimedean.arch`：∀ {R : Type u_2} {inst : AddCommMonoid R} {inst_1 : Pa
rtialOrder R} [self : Archimedean R] (x : R) {y : R},   0 < y → ∃ n, x ≤ n • y
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Archimedean.ratLt.eq_1`：∀ {M : Type u_1} [inst : AddCommGroup M] [inst_1
 : LinearOrder M] [inst_2 : One M] (x : M),   Archimedean.ratLt x = {r | r.num •
 1 < r.den •…
· 使用定理 `mem_upperBounds`：mem_upperBounds : a in upperBounds s ↔ forall x in s, x
 <= a
· 使用引理 `Rat.mk'`：mk'_num_den (q : Rat) : mk' q.num q.den q.den_nz q.reduced = q
· 使用定理 `Rat.le_iff`：∀ (a b : ℚ), a ≤ b ↔ a.num * ↑b.den ≤ b.num * ↑a.den
· 使用定理 `num_le_nat_mul_den`：num_le_nat_mul_den [ZeroLEOneClass M] [NeZero (1 : M
)] {num : Int} {den : Nat} {x : M} (h : num • 1 <= den • x) {n : Int} (hn : x <=
 n • 1) …
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `natCast_zsmul`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G) (n : ℕ),
 ↑n • a = n • a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem ratLt_bddAbove (x : M) : BddAbove (ratLt x) := by
  obtain ⟨n, hn⟩ := Archimedean.arch x zero_lt_one
  use n
  rw [ratLt, mem_upperBounds]
  intro ⟨num, den, _, _⟩
  rw [Rat.le_iff]
  suffices num • 1 < den • x → num ≤ n * den by simpa using this
  intro h
  exact num_le_nat_mul_den h.le (by simpa using hn)
/-
**Archimedean.ratLt_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Archimedean`。
形式化陈述：ratLt_nonempty (x : M) : (ratLt x).Nonempty
参数：x : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `Archimedean.arch`：∀ {R : Type u_2} {inst : AddCommMonoid R} {inst_1 : Pa
rtialOrder R} [self : Archimedean R] (x : R) {y : R},   0 < y → ∃ n, x ≤ n • y
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_lt`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddLeftStric
tMono α] {a b : α} [AddRightStrictMono α],   -a < b ↔ -b < a
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_neg_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a + -a = 0
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `natCast_zsmul`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G) (n : ℕ),
 ↑n • a = n • a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `nsmul_zero`：∀ {M : Type u_2} [inst : AddMonoid M] (n : ℕ), n • 0 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Rat.mk'`：mk'_num_den (q : Rat) : mk' q.num q.den q.den_nz q.reduced = q
（共 39 条，此处仅展示前 30 条）
-/
theorem ratLt_nonempty (x : M) : (ratLt x).Nonempty := by
  obtain hneg | rfl | hxpos := lt_trichotomy x 0
  · obtain ⟨n, hn⟩ := Archimedean.arch (-x - x) zero_lt_one
    use Rat.ofInt (-n)
    suffices -(n • 1) < x by simpa using this
    exact neg_lt.mpr (lt_of_lt_of_le (by simpa using hneg) hn)
  · exact ⟨Rat.ofInt (-1), by simp⟩
  · obtain ⟨n, hn⟩ := Archimedean.arch 1 hxpos
    use Rat.mk' 1 (n + 1) (by simp) (by simp)
    simpa using hn.trans_lt <| (nsmul_lt_nsmul_iff_left hxpos).mpr (by simp)

open scoped Pointwise in
/-
**Archimedean.ratLt_add** 是 Mathlib 中的一个定理，位于命名空间 `Archimedean`。
形式化陈述：ratLt_add (x y : M) : ratLt (x + y) = ratLt x + ratLt y
参数：x y : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_add`：∀ {α : Type u_2} [inst : Add α] {s t : Set α} {a : α}, a ∈ 
s + t ↔ ∃ x ∈ s, ∃ y ∈ t, x + y = a
· 使用定理 `Archimedean.arch`：∀ {R : Type u_2} {inst : AddCommMonoid R} {inst_1 : Pa
rtialOrder R} [self : Archimedean R] (x : R) {y : R},   0 < y → ∃ n, x ≤ n • y
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddRightStr
ictMono α] {a b : α}, 0 < a - b ↔ b < a
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Set.mem_ofPred_eq`：mem_ofPred_eq {x : α} {p : α -> Prop} : (x in {y | p 
y}) = p x
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₃`：contrapose₃ {p q : Prop} : (q -> 
¬ p) -> (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M), 0 • a = 0
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Nat.instIsDomain`：IsDomain ℕ
· 使用定理 `Rat.den_ne_zero`：∀ (q : ℚ), q.den ≠ 0
· 使用定理 `existsUnique_add_zsmul_mem_Ico`：∀ {G : Type u_1} [inst : AddCommGroup G]
 [inst_1 : LinearOrder G] [IsOrderedAddMonoid G] [Archimedean G] {a : G},   0 < 
a → ∀ (b c : G), ∃! …
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `Archimedean.mkRat_mem_ratLt`：mkRat_mem_ratLt {num : Int} {den : Nat} (hd
en : den != 0) {x : M} : mkRat num den in ratLt x ↔ num • 1 < den • x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
（共 52 条，此处仅展示前 30 条）
-/
theorem ratLt_add (x y : M) : ratLt (x + y) = ratLt x + ratLt y := by
  ext a
  rw [Set.mem_add]
  constructor
  · /- Given `a ∈ ratLt 1 (x + y)`, find `u ∈ ratLt 1 x`, `v ∈ ratLt 1 y`
      such that `u + v = a`.
      In a naive attempt, one can take the denominator `d` of `a`,
      and find the largest `u = p / d < x / 1`.
      However, `d` could be too "coarse", and `v = a - u` could be 1/d too large than `y / 1`.
      To ensure a large enough denominator, we take `d * k`, where
      `1 + 1 ≤ k • (d • (x + y) - a.num • 1)`. -/
    intro h
    rw [Set.mem_ofPred_eq] at h
    obtain ⟨k, hk⟩ := Archimedean.arch (1 + 1) <| sub_pos.mpr h
    have hk0 : k ≠ 0 := by
      contrapose! hk
      simp [hk]
    have hka0 : k * a.den ≠ 0 := mul_ne_zero hk0 a.den_ne_zero
    obtain ⟨m, ⟨hm1, hm2⟩, _⟩ := existsUnique_add_zsmul_mem_Ico zero_lt_one 0 (k • a.den • x - 1)
    refine ⟨mkRat m (k * a.den), ?_, mkRat (k * a.num - m) (k * a.den), ?_, ?_⟩
    · rw [mkRat_mem_ratLt hka0, ← smul_smul]
      simpa using hm2
    · have hk' : 1 + (k • a.num • 1 - k • a.den • y) ≤ k • a.den • x - 1 := by
        rw [smul_add, smul_sub, smul_add, le_sub_iff_add_le, ← sub_le_iff_le_add] at hk
        rw [le_sub_iff_add_le]
        convert! hk using 1
        abel
      have : k • a.num • 1 - k • a.den • y < m • 1 :=
        lt_of_lt_of_le (lt_add_of_pos_left _ zero_lt_one) (by simpa using hk'.trans hm1)
      rw [mkRat_mem_ratLt hka0, sub_smul, sub_lt_comm, ← smul_smul, ← smul_smul, natCast_zsmul]
      exact this
    · rw [Rat.mkRat_add_mkRat_of_den _ _ hka0]
      rw [add_sub_cancel, Rat.mkRat_mul_left hk0, Rat.mkRat_num_den']
  · -- `u ∈ ratLt 1 x`, `v ∈ ratLt 1 y` → `u + v ∈ ratLt 1 (x + y)`
    intro ⟨u, hu, v, hv, huv⟩
    rw [← huv]
    rw [Set.mem_ofPred_eq] at hu hv ⊢
    exact num_smul_one_lt_den_smul_add hu hv
/-
**Archimedean.ratLt'_bddAbove** 是 Mathlib 中的一个定理，位于命名空间 `Archimedean`。
形式化陈述：∀ {M : Type u_1} [inst : AddCommGroup M] [inst_1 : LinearOrder M] [IsOrder
edAddMonoid M] [inst_3 : One M]   [ZeroLEOneClass M] [NeZero 1] [Archimedean M] 
(x : M), BddAbove (Archimedean.ratLt' x)
参数：x : M；Archimedean.ratLt' x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.map_bddAbove`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [
inst_1 : Preorder β] {f : α → β},   Monotone f → ∀ {s : Set α}, BddAbove s → Bdd
Above (f ''…
· 使用定理 `Rat.cast_mono`：cast_mono : Monotone ((↑) : Rat -> K)
· 使用定理 `Archimedean.ratLt_bddAbove`：ratLt_bddAbove (x : M) : BddAbove (ratLt x)
-/
theorem ratLt'_bddAbove (x : M) : BddAbove (ratLt' x) :=
  Monotone.map_bddAbove Rat.cast_mono <| ratLt_bddAbove x
/-
**Archimedean.ratLt'_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Archimedean`。
形式化陈述：∀ {M : Type u_1} [inst : AddCommGroup M] [inst_1 : LinearOrder M] [IsOrder
edAddMonoid M] [inst_3 : One M]   [ZeroLEOneClass M] [NeZero 1] [Archimedean M] 
(x : M), (Archimedean.ratLt' x).Nonempty
参数：x : M；Archimedean.ratLt' x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.image_nonempty`：image_nonempty {f : α -> β} {s : Set α} : (f '' s).N
onempty ↔ s.Nonempty
· 使用定理 `Archimedean.ratLt_nonempty`：ratLt_nonempty (x : M) : (ratLt x).Nonempty
-/
theorem ratLt'_nonempty (x : M) : (ratLt' x).Nonempty := Set.image_nonempty.mpr (ratLt_nonempty x)

open scoped Pointwise in
/-
**Archimedean.ratLt'_add** 是 Mathlib 中的一个定理，位于命名空间 `Archimedean`。
形式化陈述：∀ {M : Type u_1} [inst : AddCommGroup M] [inst_1 : LinearOrder M] [IsOrder
edAddMonoid M] [inst_3 : One M]   [ZeroLEOneClass M] [NeZero 1] [Archimedean M] 
(x y : M),   Archimedean.ratLt' (x + y) = Archimedean.ratLt' x + Archimedean.rat
Lt' y
参数：x y : M；x + y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Archimedean.ratLt'.eq_1`：∀ {M : Type u_1} [inst : AddCommGroup M] [inst_
1 : LinearOrder M] [inst_2 : One M] (x : M),   Archimedean.ratLt' x = ⇑(Rat.cast
Hom ℝ) '' Arc…
· 使用定理 `Archimedean.ratLt_add`：ratLt_add (x y : M) : ratLt (x + y) = ratLt x + r
atLt y
· 使用定理 `Set.image_add`：∀ {F : Type u_1} {α : Type u_2} {β : Type u_3} [inst : Ad
d α] [inst_1 : Add β] [inst_2 : FunLike F α β]   [AddHomClass F α β] (m : F) {s 
t :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
-/
theorem ratLt'_add (x y : M) : ratLt' (x + y) = ratLt' x + ratLt' y := by
  rw [ratLt', ratLt_add, Set.image_add]

variable (M) in
/-
**Archimedean.embedRealFun_zero** 是 Mathlib 中的一个定理，位于命名空间 `Archimedean`。
形式化陈述：embedRealFun_zero : embedRealFun (0 : M) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `csSup_le`：csSup_le (h₁ : s.Nonempty) (h₂ : forall b in s, b <= a) : sSup
 s <= a
· 使用定理 `Archimedean.ratLt'_nonempty`：∀ {M : Type u_1} [inst : AddCommGroup M] [i
nst_1 : LinearOrder M] [IsOrderedAddMonoid M] [inst_3 : One M]   [ZeroLEOneClass
 M] [NeZero 1] [A…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Rat.cast_nonpos`：∀ {q : ℚ} {K : Type u_5} [inst : Field K] [inst_1 : Lin
earOrder K] [IsStrictOrderedRing K], ↑q ≤ 0 ↔ q ≤ 0
· 使用定理 `Rat.num_nonpos`：∀ {a : ℚ}, a.num ≤ 0 ↔ a ≤ 0
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `neg_of_smul_neg_right`：neg_of_smul_neg_right [SMulPosReflectLT α β] (h :
 a • b < 0) (hb : 0 <= b) : a < 0
· 使用定理 `SMulPosReflectLE.toSMulPosReflectLT`：∀ {α : Type u_1} {β : Type u_2} [in
st : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : PartialOrde
r α]   [inst_4 : PartialO…
· 使用定理 `SMulPosStrictMono.toSMulPosReflectLE`：∀ {α : Type u_1} {β : Type u_2} [i
nst : SMul α β] [inst_1 : LinearOrder α] [inst_2 : Preorder β] [inst_3 : Zero β]
   [SMulPosStrictMono α β]…
· 使用定理 `instSMulPosStrictMonoIntOfIsOrderedAddMonoid`：∀ {G : Type u_3} [inst : P
artialOrder G] [inst_1 : AddCommGroup G] [IsOrderedAddMonoid G], SMulPosStrictMo
no ℤ G
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `eq_ratCast`：∀ {F : Type u_1} {α : Type u_3} [inst : DivisionRing α] [ins
t_1 : FunLike F ℚ α] [RingHomClass F ℚ α] (f : F) (q : ℚ),   f q = ↑q
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `nsmul_zero`：∀ {M : Type u_2} [inst : AddMonoid M] (n : ℕ), n • 0 = 0
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `le_csSup_iff`：le_csSup_iff (h : BddAbove s) (hs : s.Nonempty) : a <= sSu
p s ↔ forall b in upperBounds s, a <= b
· 使用定理 `Archimedean.ratLt'_bddAbove`：∀ {M : Type u_1} [inst : AddCommGroup M] [i
nst_1 : LinearOrder M] [IsOrderedAddMonoid M] [inst_3 : One M]   [ZeroLEOneClass
 M] [NeZero 1] [A…
· 使用定理 `mem_upperBounds`：mem_upperBounds : a in upperBounds s ↔ forall x in s, x
 <= a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `smul_neg_iff_of_neg_left`：smul_neg_iff_of_neg_left (ha : a < 0) : a • b 
< 0 ↔ 0 < b
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instPosSMulStrictMonoIntOfIsOrderedAddMonoid`：∀ {G : Type u_3} [inst : P
artialOrder G] [inst_1 : AddCommGroup G] [IsOrderedAddMonoid G], PosSMulStrictMo
no ℤ G
· 使用定理 `PosSMulStrictMono.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} [inst :
 Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : PartialOrder α]
   [inst_4 : PartialO…
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
（共 34 条，此处仅展示前 30 条）
-/
theorem embedRealFun_zero : embedRealFun (0 : M) = 0 := by
  apply le_antisymm
  · apply csSup_le (ratLt'_nonempty 0)
    intro x
    unfold ratLt' ratLt
    suffices ∀ (y : ℚ), y.num • (1 : M) < 0 → y = x → x ≤ 0 by simpa using this
    intro y hy hyx
    rw [← hyx, Rat.cast_nonpos, ← Rat.num_nonpos]
    exact (neg_of_smul_neg_right hy zero_le_one).le
  · rw [le_csSup_iff (ratLt'_bddAbove (0 : M)) (ratLt'_nonempty 0)]
    intro x
    rw [mem_upperBounds]
    suffices (∀ (y : ℚ), y.num • (1 : M) < 0 → y ≤ x) → 0 ≤ x by simpa using this
    intro h
    have h' (y : ℚ) (hy : y < 0) : y ≤ x := by
      exact h _ <| (smul_neg_iff_of_neg_left (by simpa using hy)).mpr zero_lt_one
    contrapose! h'
    obtain ⟨y, hxy, hy⟩ := exists_rat_btwn h'
    exact ⟨y, by simpa using hy, hxy⟩
/-
**Archimedean.embedRealFun_add** 是 Mathlib 中的一个定理，位于命名空间 `Archimedean`。
形式化陈述：embedRealFun_add (x y : M) : embedRealFun (x + y) = embedRealFun x + embed
RealFun y
参数：x y : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Archimedean.embedRealFun.eq_1`：∀ {M : Type u_1} [inst : AddCommGroup M] 
[inst_1 : LinearOrder M] [inst_2 : One M] (x : M),   Archimedean.embedRealFun x 
= sSup (Archimedean…
· 使用定理 `Archimedean.ratLt'_add`：∀ {M : Type u_1} [inst : AddCommGroup M] [inst_1
 : LinearOrder M] [IsOrderedAddMonoid M] [inst_3 : One M]   [ZeroLEOneClass M] [
NeZero 1] [A…
· 使用定理 `csSup_add`：∀ {M : Type u_1} [inst : ConditionallyCompleteLattice M] [ins
t_1 : AddGroup M] [AddLeftMono M] [AddRightMono M]   {s t : Set M}, s.Nonempty …
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Archimedean.ratLt'_nonempty`：∀ {M : Type u_1} [inst : AddCommGroup M] [i
nst_1 : LinearOrder M] [IsOrderedAddMonoid M] [inst_3 : One M]   [ZeroLEOneClass
 M] [NeZero 1] [A…
· 使用定理 `Archimedean.ratLt'_bddAbove`：∀ {M : Type u_1} [inst : AddCommGroup M] [i
nst_1 : LinearOrder M] [IsOrderedAddMonoid M] [inst_3 : One M]   [ZeroLEOneClass
 M] [NeZero 1] [A…
-/
theorem embedRealFun_add (x y : M) : embedRealFun (x + y) = embedRealFun x + embedRealFun y := by
  rw [embedRealFun, ratLt'_add, csSup_add (ratLt'_nonempty x) (ratLt'_bddAbove x)
    (ratLt'_nonempty y) (ratLt'_bddAbove y)]

variable (M) in
/-
**Archimedean.embedRealFun_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `Archimedean`。
形式化陈述：embedRealFun_strictMono : StrictMono (embedRealFun (M
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddRightStr
ictMono α] {a b : α}, 0 < a - b ↔ b < a
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `lt_of_sub_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddRi
ghtStrictMono α] {a b : α}, 0 < a - b → b < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Archimedean.embedRealFun_add`：embedRealFun_add (x y : M) : embedRealFun 
(x + y) = embedRealFun x + embedRealFun y
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
· 使用定理 `Archimedean.arch`：∀ {R : Type u_2} {inst : AddCommMonoid R} {inst_1 : Pa
rtialOrder R} [self : Archimedean R] (x : R) {y : R},   0 < y → ∃ n, x ≤ n • y
· 使用引理 `Rat.mk'`：mk'_num_den (q : Rat) : mk' q.num q.den q.den_nz q.reduced = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Int.natAbs_of_isUnit`：∀ {u : ℤ}, IsUnit u → u.natAbs = 1
· 使用定理 `Nat.coprime_one_left_eq_true`：∀ (n : ℕ), Nat.Coprime 1 n = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_ratCast`：∀ {F : Type u_1} {α : Type u_3} [inst : DivisionRing α] [ins
t_1 : FunLike F ℚ α] [RingHomClass F ℚ α] (f : F) (q : ℚ),   f q = ↑q
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
（共 38 条，此处仅展示前 30 条）
-/
theorem embedRealFun_strictMono : StrictMono (embedRealFun (M := M)) := by
  intro x y h
  have hyz : 0 < y - x := sub_pos.mpr h
  have hy : y = y - x + x := (sub_add_cancel y x).symm
  apply lt_of_sub_pos
  rw [hy, embedRealFun_add, add_sub_cancel_right]
  obtain ⟨n, hn⟩ := Archimedean.arch 1 hyz
  have : (Rat.mk' 1 (n + 1) (by simp) (by simp) : ℝ) ∈ ratLt' (y - x) := by
    simpa using hn.trans_lt <| nsmul_lt_nsmul_left hyz (show n < n + 1 by simp)
  exact lt_csSup_of_lt (ratLt'_bddAbove (y - x)) this (by simp [← Rat.num_pos])

variable (M) in
/-- The bundled `M →+o ℝ` for archimedean `M` that preserves `1`. -/
noncomputable
/-
**Archimedean.embedReal** 是 Mathlib 中的一个定义，位于命名空间 `Archimedean`。
形式化陈述：embedReal : M ->+o Real where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Archimedean.embedRealFun_zero`：embedRealFun_zero : embedRealFun (0 : M) 
= 0
· 使用定理 `Archimedean.embedRealFun_add`：embedRealFun_add (x y : M) : embedRealFun 
(x + y) = embedRealFun x + embedRealFun y
-/
def embedReal : M →+o ℝ where
  toFun := embedRealFun
  map_zero' := embedRealFun_zero M
  map_add' := embedRealFun_add
  monotone' := (embedRealFun_strictMono M).monotone
/-
**Archimedean.embedReal_apply** 是 Mathlib 中的一个定理，位于命名空间 `Archimedean`。
形式化陈述：embedReal_apply (a : M) : embedReal M a = embedRealFun a
参数：a : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem embedReal_apply (a : M) : embedReal M a = embedRealFun a := by rfl

variable (M) in
/-
**Archimedean.embedReal_injective** 是 Mathlib 中的一个定理，位于命名空间 `Archimedean`。
形式化陈述：embedReal_injective : Function.Injective (embedReal M)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.injective`：StrictMono.injective (hf : StrictMono f) : Injecti
ve f
· 使用定理 `Archimedean.embedRealFun_strictMono`：embedRealFun_strictMono : StrictMon
o (embedRealFun (M
-/
theorem embedReal_injective : Function.Injective (embedReal M) :=
  (embedRealFun_strictMono M).injective

@[simp]
/-
**Archimedean.embedReal_one** 是 Mathlib 中的一个定理，位于命名空间 `Archimedean`。
形式化陈述：embedReal_one : (embedReal M) 1 = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Archimedean.embedReal_apply`：embedReal_apply (a : M) : embedReal M a = e
mbedRealFun a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `csSup_le`：csSup_le (h₁ : s.Nonempty) (h₂ : forall b in s, b <= a) : sSup
 s <= a
· 使用定理 `Archimedean.ratLt'_nonempty`：∀ {M : Type u_1} [inst : AddCommGroup M] [i
nst_1 : LinearOrder M] [IsOrderedAddMonoid M] [inst_3 : One M]   [ZeroLEOneClass
 M] [NeZero 1] [A…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `smul_lt_smul_iff_of_pos_right`：smul_lt_smul_iff_of_pos_right [SMulPosStr
ictMono α β] [SMulPosReflectLT α β] (hb : 0 < b) : a₁ • b < a₂ • b ↔ a₁ < a₂
· 使用定理 `instSMulPosStrictMonoIntOfIsOrderedAddMonoid`：∀ {G : Type u_3} [inst : P
artialOrder G] [inst_1 : AddCommGroup G] [IsOrderedAddMonoid G], SMulPosStrictMo
no ℤ G
· 使用定理 `SMulPosReflectLE.toSMulPosReflectLT`：∀ {α : Type u_1} {β : Type u_2} [in
st : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : PartialOrde
r α]   [inst_4 : PartialO…
· 使用定理 `SMulPosStrictMono.toSMulPosReflectLE`：∀ {α : Type u_1} {β : Type u_2} [i
nst : SMul α β] [inst_1 : LinearOrder α] [inst_2 : Preorder β] [inst_3 : Zero β]
   [SMulPosStrictMono α β]…
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_ratCast`：∀ {F : Type u_1} {α : Type u_3} [inst : DivisionRing α] [ins
t_1 : FunLike F ℚ α] [RingHomClass F ℚ α] (f : F) (q : ℚ),   f q = ↑q
· 使用定理 `natCast_zsmul`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G) (n : ℕ),
 ↑n • a = n • a
· 使用定理 `le_csSup_iff`：le_csSup_iff (h : BddAbove s) (hs : s.Nonempty) : a <= sSu
p s ↔ forall b in upperBounds s, a <= b
· 使用定理 `Archimedean.ratLt'_bddAbove`：∀ {M : Type u_1} [inst : AddCommGroup M] [i
nst_1 : LinearOrder M] [IsOrderedAddMonoid M] [inst_3 : One M]   [ZeroLEOneClass
 M] [NeZero 1] [A…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Rat.lt_iff`：∀ (a b : ℚ), a < b ↔ a.num * ↑b.den < b.num * ↑a.den
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
（共 31 条，此处仅展示前 30 条）
-/
theorem embedReal_one : (embedReal M) 1 = 1 := by
  rw [embedReal_apply]
  apply le_antisymm
  · apply csSup_le (ratLt'_nonempty 1)
    suffices ∀ (x : ℚ), x.num • (1 : M) < (x.den : ℤ) • (1 : M) → (x : ℝ) ≤ 1 by simpa using this
    intro x hx
    suffices x ≤ 1 by norm_cast
    simpa [Rat.le_iff] using ((smul_lt_smul_iff_of_pos_right zero_lt_one).mp hx).le
  · rw [le_csSup_iff (ratLt'_bddAbove (1 : M)) (ratLt'_nonempty 1)]
    simp_rw [mem_upperBounds]
    suffices ∀ (x : ℝ), (∀ (y : ℚ), y.num • (1 : M) < (y.den : ℤ) • 1 → y ≤ x) → 1 ≤ x by
      simpa using this
    intro x h
    have h' (y : ℚ) (hy : y < 1) : y ≤ x :=
      h _ ((smul_lt_smul_iff_of_pos_right zero_lt_one).mpr (by simpa using (Rat.lt_iff _ _).mp hy))
    contrapose! h'
    obtain ⟨y, hxy, hy⟩ := exists_rat_btwn h'
    exact ⟨y, (by norm_cast at hy), hxy⟩

omit [One M] [ZeroLEOneClass M] [NeZero (1 : M)] in
variable (M) in
/-
**Archimedean.exists_orderAddMonoidHom_real_injective** 是 Mathlib 中的一个定理，位于命名空间 
`Archimedean`。
形式化陈述：exists_orderAddMonoidHom_real_injective : exists f : M ->+o Real, Function
.Injective f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `Function.injective_of_subsingleton`：∀ {α : Sort u_1} {β : Sort u_2} [Sub
singleton α] (f : α → β), Function.Injective f
· 使用定理 `exists_ne`：exists_ne [Nontrivial α] (x : α) : exists y, y != x
· 使用定理 `abs_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [A
ddLeftMono α] [AddRightMono α] (a : α), 0 ≤ |a|
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `abs_ne_zero`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LinearOrder 
α] [AddLeftMono α] {a : α} [AddRightMono α], |a| ≠ 0 ↔ a ≠ 0
· 使用定理 `Archimedean.embedReal_injective`：embedReal_injective : Function.Injectiv
e (embedReal M)
-/
theorem exists_orderAddMonoidHom_real_injective :
    ∃ f : M →+o ℝ, Function.Injective f := by
  cases subsingleton_or_nontrivial M
  · exact ⟨0, Function.injective_of_subsingleton _⟩
  · obtain ⟨a, ha⟩ := exists_ne (0 : M)
    let one : One M := ⟨|a|⟩
    have : ZeroLEOneClass M := ⟨abs_nonneg a⟩
    have : NeZero (1 : M) := ⟨abs_ne_zero.mpr ha⟩
    exact ⟨embedReal M, embedReal_injective M⟩

end Archimedean

