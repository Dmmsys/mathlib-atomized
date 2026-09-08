/-
Copyright (c) 2024 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.Algebra.Lie.Weights.Basic

/-!

# The Lie algebra `sl₂` and its representations

The Lie algebra `sl₂` is the unique simple Lie algebra of minimal rank, 1, and as such occupies a
distinguished position in the general theory. This file provides some basic definitions and results
about `sl₂`.

## Main definitions:
* `IsSl2Triple`: a structure representing a triple of elements in a Lie algebra which satisfy the
  standard relations for `sl₂`.
* `IsSl2Triple.HasPrimitiveVectorWith`: a structure representing a primitive vector in a
  representation of a Lie algebra relative to a distinguished `sl₂` triple.
* `IsSl2Triple.HasPrimitiveVectorWith.exists_nat`: the eigenvalue of a primitive vector must be a
  natural number if the representation is finite-dimensional.

-/

@[expose] public section

variable (R L M : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

open LieModule Module Set

variable {L} in
/-- An `sl₂` triple within a Lie ring `L` is a triple of elements `h`, `e`, `f` obeying relations
which ensure that the Lie subalgebra they generate is equivalent to `sl₂`. -/
/-
**IsSl2Triple** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{L : Type u_2} → [LieRing L] → L → L → L → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An `sl₂` triple within a Lie ring `L` is a triple of elements `h`, `e`, `f` obey
ing relations
which ensure that the Lie subalgebra they generate is equivalent to `sl₂`.
-/
structure IsSl2Triple (h e f : L) : Prop where
  h_ne_zero : h ≠ 0
  lie_e_f : ⁅e, f⁆ = h
  lie_h_e_nsmul : ⁅h, e⁆ = 2 • e
  lie_h_f_nsmul : ⁅h, f⁆ = -(2 • f)

namespace IsSl2Triple

variable {L M}
variable {h e f : L}

/-
**IsSl2Triple.symm** 是 Mathlib 中的一个引理，位于命名空间 `IsSl2Triple`。
形式化陈述：symm (ht : IsSl2Triple h e f) : IsSl2Triple (-h) f e where h_ne_zero
参数：ht : IsSl2Triple h e f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsSl2Triple.h_ne_zero`：∀ {L : Type u_2} [inst : LieRing L] {h e f : L}, 
IsSl2Triple h e f → h ≠ 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_eq_iff_eq_neg`：∀ {G : Type u_3} [inst : InvolutiveNeg G] {a b : G}, 
-a = b ↔ a = -b
· 使用定理 `lie_skew`：lie_skew : -⁅y, x⁆ = ⁅x, y⁆
· 使用定理 `IsSl2Triple.lie_e_f`：∀ {L : Type u_2} [inst : LieRing L] {h e f : L}, Is
Sl2Triple h e f → ⁅e, f⁆ = h
· 使用定理 `neg_lie`：neg_lie : ⁅-x, m⁆ = -⁅x, m⁆
· 使用定理 `IsSl2Triple.lie_h_f_nsmul`：∀ {L : Type u_2} [inst : LieRing L] {h e f : 
L}, IsSl2Triple h e f → ⁅h, f⁆ = -(2 • f)
· 使用定理 `neg_inj`：∀ {G : Type u_3} [inst : InvolutiveNeg G] {a b : G}, -a = -b ↔ 
a = b
· 使用定理 `IsSl2Triple.lie_h_e_nsmul`：∀ {L : Type u_2} [inst : LieRing L] {h e f : 
L}, IsSl2Triple h e f → ⁅h, e⁆ = 2 • e
-/
lemma symm (ht : IsSl2Triple h e f) : IsSl2Triple (-h) f e where
  h_ne_zero := by simpa using ht.h_ne_zero
  lie_e_f := by rw [← neg_eq_iff_eq_neg, lie_skew, ht.lie_e_f]
  lie_h_e_nsmul := by rw [neg_lie, neg_eq_iff_eq_neg, ht.lie_h_f_nsmul]
  lie_h_f_nsmul := by rw [neg_lie, neg_inj, ht.lie_h_e_nsmul]
/-
**IsSl2Triple.symm_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsSl2Triple`。
形式化陈述：∀ {L : Type u_2} [inst : LieRing L] {h e f : L}, IsSl2Triple (-h) f e ↔ Is
Sl2Triple h e f
参数：-h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsSl2Triple.symm`：symm (ht : IsSl2Triple h e f) : IsSl2Triple (-h) f e w
here h_ne_zero
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
-/
@[simp] lemma symm_iff : IsSl2Triple (-h) f e ↔ IsSl2Triple h e f :=
  ⟨fun t ↦ neg_neg h ▸ t.symm, symm⟩
/-
**IsSl2Triple.lie_h_e_smul** 是 Mathlib 中的一个引理，位于命名空间 `IsSl2Triple`。
形式化陈述：lie_h_e_smul (t : IsSl2Triple h e f) : ⁅h, e⁆ = (2 : R) • e
参数：t : IsSl2Triple h e f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsSl2Triple.lie_h_e_nsmul`：∀ {L : Type u_2} [inst : LieRing L] {h e f : 
L}, IsSl2Triple h e f → ⁅h, e⁆ = 2 • e
· 使用定理 `two_smul`：two_smul : (2 : R) • x = x + x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma lie_h_e_smul (t : IsSl2Triple h e f) : ⁅h, e⁆ = (2 : R) • e := by
  simp [t.lie_h_e_nsmul, two_smul]
/-
**IsSl2Triple.lie_lie_smul_f** 是 Mathlib 中的一个引理，位于命名空间 `IsSl2Triple`。
形式化陈述：lie_lie_smul_f (t : IsSl2Triple h e f) : ⁅h, f⁆ = -((2 : R) • f)
参数：t : IsSl2Triple h e f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsSl2Triple.lie_h_f_nsmul`：∀ {L : Type u_2} [inst : LieRing L] {h e f : 
L}, IsSl2Triple h e f → ⁅h, f⁆ = -(2 • f)
· 使用定理 `two_smul`：two_smul : (2 : R) • x = x + x
· 使用定理 `neg_add_rev`：∀ {G : Type u_1} [inst : SubtractionMonoid G] (a b : G), -(
a + b) = -b + -a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma lie_lie_smul_f (t : IsSl2Triple h e f) : ⁅h, f⁆ = -((2 : R) • f) := by
  simp [t.lie_h_f_nsmul, two_smul]
/-
**IsSl2Triple.e_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `IsSl2Triple`。
形式化陈述：e_ne_zero (t : IsSl2Triple h e f) : e != 0
参数：t : IsSl2Triple h e f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSl2Triple.h_ne_zero`：∀ {L : Type u_2} [inst : LieRing L] {h e f : L}, 
IsSl2Triple h e f → h ≠ 0
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_lie`：zero_lie : ⁅(0 : L), m⁆ = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsSl2Triple.lie_e_f`：∀ {L : Type u_2} [inst : LieRing L] {h e f : L}, Is
Sl2Triple h e f → ⁅e, f⁆ = h
-/
lemma e_ne_zero (t : IsSl2Triple h e f) : e ≠ 0 := by
  have := t.h_ne_zero
  contrapose this
  simpa [this] using t.lie_e_f.symm
/-
**IsSl2Triple.f_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `IsSl2Triple`。
形式化陈述：f_ne_zero (t : IsSl2Triple h e f) : f != 0
参数：t : IsSl2Triple h e f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSl2Triple.h_ne_zero`：∀ {L : Type u_2} [inst : LieRing L] {h e f : L}, 
IsSl2Triple h e f → h ≠ 0
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `lie_zero`：lie_zero : ⁅x, 0⁆ = (0 : M)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsSl2Triple.lie_e_f`：∀ {L : Type u_2} [inst : LieRing L] {h e f : L}, Is
Sl2Triple h e f → ⁅e, f⁆ = h
-/
lemma f_ne_zero (t : IsSl2Triple h e f) : f ≠ 0 := by
  have := t.h_ne_zero
  contrapose this
  simpa [this] using t.lie_e_f.symm

variable {R}

/-- Given a representation of a Lie algebra with distinguished `sl₂` triple, a vector is said to be
primitive if it is a simultaneous eigenvector for the action of both `h` and `e`, and the eigenvalue
for `e` is zero. -/
/-
**IsSl2Triple.HasPrimitiveVectorWith** 是 Mathlib 中的一个归纳类型，位于命名空间 `IsSl2Triple`。
形式化陈述：{R : Type u_1} →   {L : Type u_2} →     {M : Type u_3} →       [inst : Com
mRing R] →         [inst_1 : LieRing L] →           [inst_2 : AddCommGroup M] → 
            [_root_.Module R M] → [LieRingModule L M] → {h e f : L} → IsSl2Tripl
e h e f → M → R → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a representation of a Lie algebra with distinguished `sl₂` triple, a vecto
r is said to be
primitive if it is a simultaneous eigenvector for the action of both `h` and `e`
, and the eigenvalue
for `e` is zero.
-/
structure HasPrimitiveVectorWith (t : IsSl2Triple h e f) (m : M) (μ : R) : Prop where
  ne_zero : m ≠ 0
  lie_h : ⁅h, m⁆ = μ • m
  lie_e : ⁅e, m⁆ = 0

/-- Given a representation of a Lie algebra with distinguished `sl₂` triple, a simultaneous
eigenvector for the action of both `h` and `e` necessarily has eigenvalue zero for `e`. -/
/-
**IsSl2Triple.HasPrimitiveVectorWith.mk'** 是 Mathlib 中的一个定理，位于命名空间 `IsSl2Triple.
HasPrimitiveVectorWith`。
形式化陈述：∀ {R : Type u_1} {L : Type u_2} {M : Type u_3} [inst : CommRing R] [inst_1
 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 : AddCommGroup M] [inst_4 : _r
oot_.Module R M] [inst_5 : LieRingModule L M] [LieModule R L M] {h e f : L}   [I
sAddTorsionFree M] (t : IsSl2Triple h e f) (m : M) (μ ρ : R),   m ≠ 0 → ⁅h, m⁆ =
 μ • m → ⁅e, m⁆ = ρ • m → t.HasPrimitiveVectorWith m μ
参数：t : IsSl2Triple h e f；m : M；μ ρ : R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nsmul_lie`：nsmul_lie (n : Nat) : ⁅n • x, m⁆ = n • ⁅x, m⁆
· 使用定理 `IsSl2Triple.lie_h_e_nsmul`：∀ {L : Type u_2} [inst : LieRing L] {h e f : 
L}, IsSl2Triple h e f → ⁅h, e⁆ = 2 • e
· 使用引理 `lie_lie`：lie_lie : ⁅⁅x, y⁆, m⁆ = ⁅x, ⁅y, m⁆⁆ - ⁅y, ⁅x, m⁆⁆
· 使用定理 `lie_smul`：lie_smul : ⁅x, t • m⁆ = t • ⁅x, m⁆
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p

--- 原说明 ---
Given a representation of a Lie algebra with distinguished `sl₂` triple, a simul
taneous
eigenvector for the action of both `h` and `e` necessarily has eigenvalue zero f
or `e`.
-/
lemma HasPrimitiveVectorWith.mk' [IsAddTorsionFree M] (t : IsSl2Triple h e f) (m : M) (μ ρ : R)
    (hm : m ≠ 0) (hm' : ⁅h, m⁆ = μ • m) (he : ⁅e, m⁆ = ρ • m) :
    HasPrimitiveVectorWith t m μ where
  ne_zero := hm
  lie_h := hm'
  lie_e := by
    suffices 2 • ⁅e, m⁆ = 0 by simpa using this
    rw [← nsmul_lie, ← t.lie_h_e_nsmul, lie_lie, hm', lie_smul, he, lie_smul, hm',
      smul_smul, smul_smul, mul_comm ρ μ, sub_self]

variable (R) in
open Submodule in
/-- The subalgebra associated to an `sl₂` triple. -/
/-
**IsSl2Triple.toLieSubalgebra** 是 Mathlib 中的一个定义，位于命名空间 `IsSl2Triple`。
形式化陈述：toLieSubalgebra (t : IsSl2Triple h e f) : LieSubalgebra R L where __
参数：t : IsSl2Triple h e f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The subalgebra associated to an `sl₂` triple.
-/
def toLieSubalgebra (t : IsSl2Triple h e f) :
    LieSubalgebra R L where
  __ := span R {e, f, h}
  lie_mem' {x y} hx hy := by
    simp only [carrier_eq_coe, SetLike.mem_coe] at hx hy ⊢
    induction hx using span_induction with
    | zero => simp
    | add u v hu hv hu' hv' => simpa only [add_lie] using add_mem hu' hv'
    | smul t u hu hu' => simpa only [smul_lie] using smul_mem _ t hu'
    | mem u hu =>
      induction hy using span_induction with
      | zero => simp
      | add u v hu hv hu' hv' => simpa only [lie_add] using add_mem hu' hv'
      | smul t u hv hv' => simpa only [lie_smul] using smul_mem _ t hv'
      | mem v hv =>
        push _ ∈ _ at hu hv
        rcases hu with rfl | rfl | rfl <;>
        rcases hv with rfl | rfl | rfl <;> (try simp only [lie_self, zero_mem])
        · rw [t.lie_e_f]
          apply subset_span
          simp
        · rw [← lie_skew, t.lie_h_e_nsmul, neg_mem_iff]
          apply nsmul_mem <| subset_span _
          simp
        · rw [← lie_skew, t.lie_e_f, neg_mem_iff]
          apply subset_span
          simp
        · rw [← lie_skew, t.lie_h_f_nsmul, neg_neg]
          apply nsmul_mem <| subset_span _
          simp
        · rw [t.lie_h_e_nsmul]
          apply nsmul_mem <| subset_span _
          simp
        · rw [t.lie_h_f_nsmul, neg_mem_iff]
          apply nsmul_mem <| subset_span _
          simp
/-
**IsSl2Triple.mem_toLieSubalgebra_iff** 是 Mathlib 中的一个引理，位于命名空间 `IsSl2Triple`。
形式化陈述：mem_toLieSubalgebra_iff {x : L} {t : IsSl2Triple h e f} : x in t.toLieSuba
lgebra R ↔ exists c₁ c₂ c₃ : R, x = c₁ • e + c₂ • f + c₃ • ⁅e, f⁆
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsSl2Triple.lie_e_f`：∀ {L : Type u_2} [inst : LieRing L] {h e f : L}, Is
Sl2Triple h e f → ⁅e, f⁆ = h
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mem_toLieSubalgebra_iff {x : L} {t : IsSl2Triple h e f} :
    x ∈ t.toLieSubalgebra R ↔ ∃ c₁ c₂ c₃ : R, x = c₁ • e + c₂ • f + c₃ • ⁅e, f⁆ := by
  simp_rw [t.lie_e_f, toLieSubalgebra, ← LieSubalgebra.mem_toSubmodule, Submodule.mem_span_triple,
    eq_comm]

namespace HasPrimitiveVectorWith

variable {m : M} {μ : R} {t : IsSl2Triple h e f}
local notation "ψ " n => ((toEnd R L M f) ^ n) m

-- Although this is true by definition, we include this lemma (and the assumption) to mirror the API
-- for `lie_h_pow_toEnd_f` and `lie_e_pow_succ_toEnd_f`.
set_option linter.unusedVariables false in
@[nolint unusedArguments]
/-
**IsSl2Triple.HasPrimitiveVectorWith.lie_f_pow_toEnd_f** 是 Mathlib 中的一个引理，位于命名空间
 `IsSl2Triple.HasPrimitiveVectorWith`。
形式化陈述：lie_f_pow_toEnd_f (P : HasPrimitiveVectorWith t m μ) (n : Nat) : ⁅f, ψ n⁆ 
= ψ (n + 1)
参数：P : HasPrimitiveVectorWith t m μ；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `LieModule.toEnd_apply_apply`：∀ (R : Type u) (L : Type v) (M : Type w) [i
nst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 : Add
CommGroup M] [ins…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma lie_f_pow_toEnd_f (P : HasPrimitiveVectorWith t m μ) (n : ℕ) :
    ⁅f, ψ n⁆ = ψ (n + 1) := by
  simp [pow_succ']

variable (P : HasPrimitiveVectorWith t m μ)
include P
/-
**IsSl2Triple.HasPrimitiveVectorWith.lie_h_pow_toEnd_f** 是 Mathlib 中的一个引理，位于命名空间
 `IsSl2Triple.HasPrimitiveVectorWith`。
形式化陈述：lie_h_pow_toEnd_f (n : Nat) : ⁅h, ψ n⁆ = (μ - 2 * n) • ψ n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `IsSl2Triple.HasPrimitiveVectorWith.lie_h`：∀ {R : Type u_1} {L : Type u_2
} {M : Type u_3} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup
 M]   [inst_3 : _root_.Module …
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `Module.End.mul_apply`：mul_apply (f g : Module.End R M) (x : M) : (f * g)
 x = f (g x)
· 使用定理 `LieModule.toEnd_apply_apply`：∀ (R : Type u) (L : Type v) (M : Type w) [i
nst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 : Add
CommGroup M] [ins…
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用引理 `leibniz_lie`：leibniz_lie [Add M] [IsLieTower L₁ L₂ M] (x : L₁) (y : L₂) 
(m : M) : ⁅x, ⁅y, m⁆⁆ = ⁅⁅x, y⁆, m⁆ + ⁅y, ⁅x, m⁆⁆
· 使用定理 `instIsLieTower`：∀ {L : Type v} {M : Type w} [inst : LieRing L] [inst_1 :
 AddCommGroup M] [inst_2 : LieRingModule L M], IsLieTower L L M
· 使用引理 `IsSl2Triple.lie_lie_smul_f`：lie_lie_smul_f (t : IsSl2Triple h e f) : ⁅h,
 f⁆ = -((2 : R) • f)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `lie_smul`：lie_smul : ⁅x, t • m⁆ = t • ⁅x, m⁆
· 使用定理 `smul_lie`：smul_lie : ⁅t • x, m⁆ = t • ⁅x, m⁆
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
（共 52 条，此处仅展示前 30 条）
-/
lemma lie_h_pow_toEnd_f (n : ℕ) :
    ⁅h, ψ n⁆ = (μ - 2 * n) • ψ n := by
  induction n with
  | zero => simpa using P.lie_h
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, toEnd_apply_apply, Nat.cast_add, Nat.cast_one,
      leibniz_lie h, t.lie_lie_smul_f R, ← neg_smul, ih, lie_smul, smul_lie, ← add_smul]
    congr
    ring
/-
**IsSl2Triple.HasPrimitiveVectorWith.lie_e_pow_succ_toEnd_f** 是 Mathlib 中的一个引理，位
于命名空间 `IsSl2Triple.HasPrimitiveVectorWith`。
形式化陈述：lie_e_pow_succ_toEnd_f (n : Nat) : ⁅e, ψ (n + 1)⁆ = ((n + 1) * (μ - n)) • 
ψ n
参数：n : Nat。
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
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `LieModule.toEnd_apply_apply`：∀ (R : Type u) (L : Type v) (M : Type w) [i
nst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 : Add
CommGroup M] [ins…
· 使用引理 `leibniz_lie`：leibniz_lie [Add M] [IsLieTower L₁ L₂ M] (x : L₁) (y : L₂) 
(m : M) : ⁅x, ⁅y, m⁆⁆ = ⁅⁅x, y⁆, m⁆ + ⁅y, ⁅x, m⁆⁆
· 使用定理 `instIsLieTower`：∀ {L : Type v} {M : Type w} [inst : LieRing L] [inst_1 :
 AddCommGroup M] [inst_2 : LieRingModule L M], IsLieTower L L M
· 使用定理 `IsSl2Triple.lie_e_f`：∀ {L : Type u_2} [inst : LieRing L] {h e f : L}, Is
Sl2Triple h e f → ⁅e, f⁆ = h
· 使用定理 `IsSl2Triple.HasPrimitiveVectorWith.lie_h`：∀ {R : Type u_1} {L : Type u_2
} {M : Type u_3} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup
 M]   [inst_3 : _root_.Module …
· 使用定理 `IsSl2Triple.HasPrimitiveVectorWith.lie_e`：∀ {R : Type u_1} {L : Type u_2
} {M : Type u_3} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup
 M]   [inst_3 : _root_.Module …
· 使用定理 `lie_zero`：lie_zero : ⁅x, 0⁆ = (0 : M)
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `Module.End.mul_apply`：mul_apply (f g : Module.End R M) (x : M) : (f * g)
 x = f (g x)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `IsSl2Triple.HasPrimitiveVectorWith.lie_h_pow_toEnd_f`：lie_h_pow_toEnd_f 
(n : Nat) : ⁅h, ψ n⁆ = (μ - 2 * n) • ψ n
· 使用定理 `lie_smul`：lie_smul : ⁅x, t • m⁆ = t • ⁅x, m⁆
· 使用引理 `IsSl2Triple.HasPrimitiveVectorWith.lie_f_pow_toEnd_f`：lie_f_pow_toEnd_f 
(P : HasPrimitiveVectorWith t m μ) (n : Nat) : ⁅f, ψ n⁆ = ψ (n + 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
（共 66 条，此处仅展示前 30 条）
-/
lemma lie_e_pow_succ_toEnd_f (n : ℕ) :
    ⁅e, ψ (n + 1)⁆ = ((n + 1) * (μ - n)) • ψ n := by
  induction n with
  | zero =>
      simp only [zero_add, pow_one, toEnd_apply_apply, Nat.cast_zero, sub_zero, one_mul,
        pow_zero, Module.End.one_apply, leibniz_lie e, t.lie_e_f, P.lie_e, P.lie_h, lie_zero,
        add_zero]
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, toEnd_apply_apply, leibniz_lie e, t.lie_e_f,
      lie_h_pow_toEnd_f P, ih, lie_smul, lie_f_pow_toEnd_f P, ← add_smul,
      Nat.cast_add, Nat.cast_one]
    congr
    ring

/-- The eigenvalue of a primitive vector must be a natural number if the representation is
finite-dimensional. -/
/-
**IsSl2Triple.HasPrimitiveVectorWith.exists_nat** 是 Mathlib 中的一个引理，位于命名空间 `IsSl2
Triple.HasPrimitiveVectorWith`。
形式化陈述：exists_nat [IsNoetherian R M] [IsTorsionFree R M] [IsDomain R] [CharZero R
] : exists n : Nat, μ = n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.infinite_range_iff`：infinite_range_iff {f : α -> β} (hf : Injective 
f) : (range f).Infinite ↔ Infinite α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `instInfiniteNat`：Infinite ℕ
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `LinearIndependent.finite`：finite [Module.Finite R M] {ι : Type*} {f : ι 
-> M} (h : LinearIndependent R f) : Finite ι
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `instNontrivialOfCharZero`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [
CharZero α], Nontrivial α
· 使用定理 `Module.IsNoetherian.finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semi
ring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [IsNoetherian 
R M], Module.Fin…
· 使用定理 `Module.End.eigenvectors_linearIndependent`：eigenvectors_linearIndependen
t [IsDomain R] [IsTorsionFree R M] (f : End R M) (μs : Set R) (xs : μs -> M) (h_
eigenvec : forall μ : μs, f.Has…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LieModule.toEnd_apply_apply`：∀ (R : Type u) (L : Type v) (M : Type w) [i
nst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 : Add
CommGroup M] [ins…
· 使用引理 `IsSl2Triple.HasPrimitiveVectorWith.lie_h_pow_toEnd_f`：lie_h_pow_toEnd_f 
(n : Nat) : ⁅h, ψ n⁆ = (μ - 2 * n) • ψ n
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用引理 `Nat.exists_not_and_succ_of_not_zero_of_exists`：exists_not_and_succ_of_no
t_zero_of_exists {p : Nat -> Prop} (H' : ¬ p 0) (H : exists n, p n) : exists n, 
¬ p n ∧ p (n + 1)
· 使用定理 `IsSl2Triple.HasPrimitiveVectorWith.ne_zero`：∀ {R : Type u_1} {L : Type u
_2} {M : Type u_3} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGro
up M]   [inst_3 : _root_.Module …
· 使用引理 `IsSl2Triple.HasPrimitiveVectorWith.lie_e_pow_succ_toEnd_f`：lie_e_pow_suc
c_toEnd_f (n : Nat) : ⁅e, ψ (n + 1)⁆ = ((n + 1) * (μ - n)) • ψ n
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
（共 37 条，此处仅展示前 30 条）

--- 原说明 ---
The eigenvalue of a primitive vector must be a natural number if the representat
ion is
finite-dimensional.
-/
lemma exists_nat [IsNoetherian R M] [IsTorsionFree R M] [IsDomain R] [CharZero R] :
    ∃ n : ℕ, μ = n := by
  suffices ∃ n : ℕ, (ψ n) = 0 by
    obtain ⟨n, hn₁, hn₂⟩ := Nat.exists_not_and_succ_of_not_zero_of_exists P.ne_zero this
    refine ⟨n, ?_⟩
    have := lie_e_pow_succ_toEnd_f P n
    rw [hn₂, lie_zero, eq_comm, smul_eq_zero_iff_left hn₁, mul_eq_zero, sub_eq_zero] at this
    exact this.resolve_left <| Nat.cast_add_one_ne_zero n
  have hs : (range <| fun (n : ℕ) ↦ μ - 2 * n).Infinite := by
    rw [infinite_range_iff (fun n m ↦ by simp)]; infer_instance
  by_contra! contra
  exact hs ((toEnd R L M h).eigenvectors_linearIndependent
    {μ - 2 * n | n : ℕ}
    (fun ⟨s, hs⟩ ↦ ψ Classical.choose hs)
    (fun ⟨r, hr⟩ ↦ by simp [lie_h_pow_toEnd_f P, Classical.choose_spec hr, contra,
      Module.End.hasEigenvector_iff])).finite
/-
**IsSl2Triple.HasPrimitiveVectorWith.pow_toEnd_f_ne_zero_of_eq_nat** 是 Mathlib 中
的一个引理，位于命名空间 `IsSl2Triple.HasPrimitiveVectorWith`。
形式化陈述：pow_toEnd_f_ne_zero_of_eq_nat [CharZero R] [IsDomain R] [IsTorsionFree R M
] {n : Nat} (hn : μ = n) {i} (hi : i <= n) : (ψ i) != 0
参数：hn : μ = n；hi : i <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSl2Triple.HasPrimitiveVectorWith.ne_zero`：∀ {R : Type u_1} {L : Type u
_2} {M : Type u_3} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGro
up M]   [inst_3 : _root_.Module …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Int.cast_smul_eq_zsmul`：Int.cast_smul_eq_zsmul (n : Int) (b : M) : (n : 
R) • b = n • b
· 使用引理 `Int.cast_mul`：cast_mul {α : Type*} [NonAssocRing α] : forall m n, ((m * 
n : Int) : α) = m * n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Int.cast_add`：∀ {R : Type u} [inst : AddGroupWithOne R] (m n : ℤ), ↑(m +
 n) = ↑m + ↑n
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `Int.cast_sub`：cast_sub (m n) : ((m - n : Int) : R) = m - n
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用引理 `IsSl2Triple.HasPrimitiveVectorWith.lie_e_pow_succ_toEnd_f`：lie_e_pow_suc
c_toEnd_f (n : Nat) : ⁅e, ψ (n + 1)⁆ = ((n + 1) * (μ - n)) • ψ n
· 使用定理 `lie_zero`：lie_zero : ⁅x, 0⁆ = (0 : M)
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `Nat.cast_eq_zero`：cast_eq_zero {n : Nat} : (n : R) = 0 ↔ n = 0
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Nat.cast_inj`：cast_inj {m n : Nat} : (m : R) = n ↔ m = n
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
（共 38 条，此处仅展示前 30 条）
-/
lemma pow_toEnd_f_ne_zero_of_eq_nat [CharZero R] [IsDomain R] [IsTorsionFree R M]
    {n : ℕ} (hn : μ = n) {i} (hi : i ≤ n) : (ψ i) ≠ 0 := by
  intro H
  induction i
  · exact P.ne_zero (by simpa using H)
  · next i IH =>
    have : ((i + 1) * (n - i) : ℤ) • (toEnd R L M f ^ i) m = 0 := by
      have := congr_arg (⁅e, ·⁆) H
      simpa [← Int.cast_smul_eq_zsmul R, P.lie_e_pow_succ_toEnd_f, hn] using this
    rw [← Int.cast_smul_eq_zsmul R, smul_eq_zero, Int.cast_eq_zero, mul_eq_zero, sub_eq_zero,
      Nat.cast_inj, ← @Nat.cast_one ℤ, ← Nat.cast_add, Nat.cast_eq_zero] at this
    simp only [add_eq_zero, one_ne_zero, and_false, false_or] at this
    exact (hi.trans_eq (this.resolve_right (IH (i.le_succ.trans hi)))).not_gt i.lt_succ_self
/-
**IsSl2Triple.HasPrimitiveVectorWith.pow_toEnd_f_eq_zero_of_eq_nat** 是 Mathlib 中
的一个引理，位于命名空间 `IsSl2Triple.HasPrimitiveVectorWith`。
形式化陈述：pow_toEnd_f_eq_zero_of_eq_nat [IsDomain R] [CharZero R] [IsNoetherian R M]
 [IsTorsionFree R M] {n : Nat} (hn : μ = n) : (ψ (n + 1)) = 0
参数：hn : μ = n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `IsSl2Triple.HasPrimitiveVectorWith.lie_h_pow_toEnd_f`：lie_h_pow_toEnd_f 
(n : Nat) : ⁅h, ψ n⁆ = (μ - 2 * n) • ψ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `IsSl2Triple.HasPrimitiveVectorWith.lie_e_pow_succ_toEnd_f`：lie_e_pow_suc
c_toEnd_f (n : Nat) : ⁅e, ψ (n + 1)⁆ = ((n + 1) * (μ - n)) • ψ n
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用引理 `IsSl2Triple.HasPrimitiveVectorWith.exists_nat`：exists_nat [IsNoetherian 
R M] [IsTorsionFree R M] [IsDomain R] [CharZero R] : exists n : Nat, μ = n
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用引理 `Int.cast_injective`：cast_injective : Injective (Int.cast : Int -> α)
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `Int.cast_add`：∀ {R : Type u} [inst : AddGroupWithOne R] (m n : ℤ), ↑(m +
 n) = ↑m + ↑n
· 使用引理 `Int.cast_mul`：cast_mul {α : Type*} [NonAssocRing α] : forall m n, ((m * 
n : Int) : α) = m * n
· 使用定理 `Int.cast_ofNat`：cast_ofNat (n : Nat) [n.AtLeastTwo] : ((ofNat(n) : Int) 
: R) = ofNat(n)
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
-/
lemma pow_toEnd_f_eq_zero_of_eq_nat [IsDomain R] [CharZero R] [IsNoetherian R M] [IsTorsionFree R M]
    {n : ℕ} (hn : μ = n) : (ψ (n + 1)) = 0 := by
  by_contra h
  have : t.HasPrimitiveVectorWith (ψ (n + 1)) (n - 2 * (n + 1) : R) :=
    { ne_zero := h
      lie_h := (P.lie_h_pow_toEnd_f _).trans (by simp [hn])
      lie_e := (P.lie_e_pow_succ_toEnd_f _).trans (by simp [hn]) }
  obtain ⟨m, hm⟩ := this.exists_nat
  have : (n : ℤ) < m + 2 * (n + 1) := by lia
  exact this.ne (Int.cast_injective (α := R) <| by simpa [sub_eq_iff_eq_add] using hm)

end HasPrimitiveVectorWith

variable {m : M} {μ : R}
local notation "φ " n => ((toEnd R L M e) ^ n) m

/-
**IsSl2Triple.lie_e_pow_toEnd_e** 是 Mathlib 中的一个引理，位于命名空间 `IsSl2Triple`。
形式化陈述：lie_e_pow_toEnd_e (n : Nat) : ⁅e, φ n⁆ = φ (n + 1)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `LieModule.toEnd_apply_apply`：∀ (R : Type u) (L : Type v) (M : Type w) [i
nst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 : Add
CommGroup M] [ins…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma lie_e_pow_toEnd_e (n : ℕ) :
    ⁅e, φ n⁆ = φ (n + 1) := by
  simp [pow_succ']
/-
**IsSl2Triple.lie_h_pow_toEnd_e** 是 Mathlib 中的一个引理，位于命名空间 `IsSl2Triple`。
形式化陈述：lie_h_pow_toEnd_e (t : IsSl2Triple h e f) (hm : ⁅h, m⁆ = μ • m) (n : Nat) 
: ⁅h, φ n⁆ = (μ + 2 * n) • φ n
参数：t : IsSl2Triple h e f；hm : ⁅h, m⁆ = μ • m；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `Module.End.mul_apply`：mul_apply (f g : Module.End R M) (x : M) : (f * g)
 x = f (g x)
· 使用定理 `LieModule.toEnd_apply_apply`：∀ (R : Type u) (L : Type v) (M : Type w) [i
nst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 : Add
CommGroup M] [ins…
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用引理 `leibniz_lie`：leibniz_lie [Add M] [IsLieTower L₁ L₂ M] (x : L₁) (y : L₂) 
(m : M) : ⁅x, ⁅y, m⁆⁆ = ⁅⁅x, y⁆, m⁆ + ⁅y, ⁅x, m⁆⁆
· 使用定理 `instIsLieTower`：∀ {L : Type v} {M : Type w} [inst : LieRing L] [inst_1 :
 AddCommGroup M] [inst_2 : LieRingModule L M], IsLieTower L L M
· 使用引理 `IsSl2Triple.lie_h_e_smul`：lie_h_e_smul (t : IsSl2Triple h e f) : ⁅h, e⁆ 
= (2 : R) • e
· 使用定理 `smul_lie`：smul_lie : ⁅t • x, m⁆ = t • ⁅x, m⁆
· 使用定理 `lie_smul`：lie_smul : ⁅x, t • m⁆ = t • ⁅x, m⁆
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
（共 41 条，此处仅展示前 30 条）
-/
lemma lie_h_pow_toEnd_e (t : IsSl2Triple h e f)
    (hm : ⁅h, m⁆ = μ • m) (n : ℕ) :
    ⁅h, φ n⁆ = (μ + 2 * n) • φ n := by
  induction n with
  | zero => simpa using hm
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, toEnd_apply_apply, Nat.cast_add, Nat.cast_one,
      leibniz_lie h, IsSl2Triple.lie_h_e_smul R t, smul_lie, ih, lie_smul, ← add_smul]
    congr 1
    ring

section CharZero

variable [IsDomain R] [CharZero R]
  [Nontrivial M] [IsTorsionFree R M] [Module.Finite R M] [IsTriangularizable R L M]
  (t : IsSl2Triple h e f)

/-
**IsSl2Triple.exists_hasPrimitiveVectorWith** 是 Mathlib 中的一个引理，位于命名空间 `IsSl2Trip
le`。
形式化陈述：exists_hasPrimitiveVectorWith : exists (μ : R) (m : M), m != 0 ∧ HasPrimit
iveVectorWith t m μ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieModule.IsTriangularizable.exists_hasEigenvalue`：∀ (R : Type u_2) (L :
 Type u_3) (M : Type u_4) [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : Lie
Algebra R L]   [inst_3 : AddCommGroup M…
· 使用定理 `Module.End.HasEigenvalue.exists_hasEigenvector`：∀ {R : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]  
 {f : Module.End R M} {μ : R}, f.Has…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Module.End.mem_eigenspace_iff`：mem_eigenspace_iff {f : End R M} {μ : R} 
{x : M} : x in eigenspace f μ ↔ f x = μ • x
· 使用定理 `LieModule.toEnd_apply_apply`：∀ (R : Type u) (L : Type v) (M : Type w) [i
nst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 : Add
CommGroup M] [ins…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用引理 `IsSl2Triple.lie_h_pow_toEnd_e`：lie_h_pow_toEnd_e (t : IsSl2Triple h e f)
 (hm : ⁅h, m⁆ = μ • m) (n : Nat) : ⁅h, φ n⁆ = (μ + 2 * n) • φ n
· 使用定理 `Module.End.HasEigenvector.apply_eq_smul`：∀ {R : Type v} {M : Type w} [in
st : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {f : M
odule.End R M} {μ : R} {x : M…
· 使用定理 `LinearIndependent.finite`：finite [Module.Finite R M] {ι : Type*} {f : ι 
-> M} (h : LinearIndependent R f) : Finite ι
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `instNontrivialOfCharZero`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [
CharZero α], Nontrivial α
· 使用定理 `Module.End.eigenvectors_linearIndependent`：eigenvectors_linearIndependen
t [IsDomain R] [IsTorsionFree R M] (f : End R M) (μs : Set R) (xs : μs -> M) (h_
eigenvec : forall μ : μs, f.Has…
· 使用定理 `Set.infinite_range_of_injective`：infinite_range_of_injective [Infinite α
] {f : α -> β} (hi : Injective f) : (range f).Infinite
· 使用定理 `instInfiniteNat`：Infinite ℕ
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
· 使用引理 `Nat.exists_not_and_succ_of_not_zero_of_exists`：exists_not_and_succ_of_no
t_zero_of_exists {p : Nat -> Prop} (H' : ¬ p 0) (H : exists n, p n) : exists n, 
¬ p n ∧ p (n + 1)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `IsSl2Triple.lie_e_pow_toEnd_e`：lie_e_pow_toEnd_e (n : Nat) : ⁅e, φ n⁆ = 
φ (n + 1)
-/
lemma exists_hasPrimitiveVectorWith :
    ∃ (μ : R) (m : M), m ≠ 0 ∧ HasPrimitiveVectorWith t m μ := by
  obtain ⟨μ₀, hμ₀⟩ := IsTriangularizable.exists_hasEigenvalue R L M h
  obtain ⟨m₀, hm₀⟩ := hμ₀.exists_hasEigenvector
  let evals (n : ℕ) : R := μ₀ + 2 * (n : R)
  let e_vecs (n : ℕ) : M := ((toEnd R L M e) ^ n) m₀
  have h_exists_zero : ∃ k, e_vecs k = 0 := by
    by_contra! contra
    have h_inj : Function.Injective evals := fun a b hab ↦ by
      simpa [evals, add_right_inj, mul_eq_mul_left_iff, Nat.cast_inj] using hab
    have aux (μ : range evals) : (toEnd R L M h).HasEigenvector μ (e_vecs μ.property.choose) := by
      set n := μ.property.choose
      refine ⟨?_, contra n⟩
      rw [Module.End.mem_eigenspace_iff, toEnd_apply_apply, ← μ.property.choose_spec]
      exact t.lie_h_pow_toEnd_e hm₀.apply_eq_smul n
    have _i := ((toEnd R L M h).eigenvectors_linearIndependent (range evals) _ aux).finite
    exact (Set.infinite_range_of_injective h_inj) (Set.toFinite _)
  obtain ⟨n, hn_ne, hn_zero⟩ := Nat.exists_not_and_succ_of_not_zero_of_exists hm₀.2 h_exists_zero
  exact ⟨evals n, e_vecs n, hn_ne,
    { ne_zero := hn_ne
      lie_h := t.lie_h_pow_toEnd_e hm₀.apply_eq_smul n
      lie_e := by rwa [lie_e_pow_toEnd_e n] }⟩

end CharZero

end IsSl2Triple

