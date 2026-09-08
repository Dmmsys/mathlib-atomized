/-
Copyright (c) 2025 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.Algebra.Order.Module.Archimedean
public import Mathlib.Algebra.Order.Monoid.PNat
public import Mathlib.Data.Sign.Defs
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# Divisible Hull of an abelian group

This file constructs the divisible hull of an `AddCommMonoid` as a `ℕ`-module localized at
`ℕ+` (implemented using `nonZeroDivisors ℕ`), which is a `ℚ≥0`-module.

Furthermore, we show that

* when `M` is a group, so is `DivisibleHull M`, which is also a `ℚ`-module
* when `M` is linearly ordered and cancellative, so is `DivisibleHull M`, which is also an
  ordered `ℚ≥0`-module.
* when `M` is a linearly ordered group, `DivisibleHull M` is an ordered `ℚ`-module, and
  `ArchimedeanClass` is preserved.

Despite the name, this file doesn't implement a `DivisibleBy` instance on `DivisibleHull`. This
should be implemented on `LocalizedModule` in a more general setting (TODO: implement this).
This file mainly focuses on the specialization to `ℕ` and the linear order property introduced by
it.

## Main declarations

* `DivisibleHull M` is the divisible hull of an abelian group.
* `DivisibleHull.archimedeanClassOrderIso M` is the equivalence between `ArchimedeanClass M` and
  `ArchimedeanClass (DivisibleHull M)`.

-/

@[expose] public section

variable {M : Type*} [AddCommMonoid M]

local notation "↑ⁿ" => PNat.equivNonZeroDivisorsNat

variable (M) in
/-- The divisible hull of an `AddCommMonoid` (as a ℕ-module) is the localized module by
`ℕ+` (implemented using `nonZeroDivisors ℕ`), thus a ℕ-divisible group, or a `ℚ≥0`-module. -/
/-
**DivisibleHull** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：DivisibleHull
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The divisible hull of an `AddCommMonoid` (as a ℕ-module) is the localized module
 by
`ℕ+` (implemented using `nonZeroDivisors ℕ`), thus a ℕ-divisible group, or a `ℚ≥
0`-module.
-/
abbrev DivisibleHull := LocalizedModule (nonZeroDivisors ℕ) M

namespace DivisibleHull

/-- Create an element `m / s`. -/
/-
**DivisibleHull.mk** 是 Mathlib 中的一个定义，位于命名空间 `DivisibleHull`。
形式化陈述：mk (m : M) (s : Nat+) : DivisibleHull M
参数：m : M；s : Nat+。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Create an element `m / s`.
-/
def mk (m : M) (s : ℕ+) : DivisibleHull M := LocalizedModule.mk m (↑ⁿ s)
/-
**DivisibleHull.** 是 Mathlib 中的一个实例，位于命名空间 `DivisibleHull`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : Module ℚ≥0 (DivisibleHull M) := LocalizedModule.moduleOfIsLocalization ..

/-- Define coercion as `m ↦ m / 1`. -/
@[coe]
/-
**DivisibleHull.coe** 是 Mathlib 中的一个缩写定义，位于命名空间 `DivisibleHull`。
形式化陈述：coe (m : M)
参数：m : M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Define coercion as `m ↦ m / 1`.
-/
abbrev coe (m : M) := mk m 1

/-- Coercion from `M` to `DivisibleHull M` defined as `m ↦ m / 1`. -/
/-
**DivisibleHull.** 是 Mathlib 中的一个实例，位于命名空间 `DivisibleHull`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Coercion from `M` to `DivisibleHull M` defined as `m ↦ m / 1`.
-/
instance : Coe M (DivisibleHull M) where
  coe := coe

@[simp]
/-
**DivisibleHull.mk_zero** 是 Mathlib 中的一个定理，位于命名空间 `DivisibleHull`。
形式化陈述：mk_zero (s : Nat+) : mk (0 : M) s = 0
参数：s : Nat+。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OreLocalization.zero_oreDiv`：zero_oreDiv (s : S) : (0 : X) /ₒ s = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mk_zero (s : ℕ+) : mk (0 : M) s = 0 := by simp [mk]

@[elab_as_elim, induction_eliminator]
/-
**DivisibleHull.ind** 是 Mathlib 中的一个定理，位于命名空间 `DivisibleHull`。
形式化陈述：ind {motive : DivisibleHull M -> Prop} (mk : forall num den, motive (.mk n
um den)) : forall x, motive x
参数：mk : forall num den, motive (.mk num den)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LocalizedModule.induction_on`：induction_on {β : LocalizedModule S M -> P
rop} (h : forall (m : M) (s : S), β (mk m s)) : forall x : LocalizedModule S M, 
β x
-/
theorem ind {motive : DivisibleHull M → Prop} (mk : ∀ num den, motive (.mk num den)) :
    ∀ x, motive x :=
  LocalizedModule.induction_on fun m s ↦ mk m (↑ⁿ.symm s)
/-
**DivisibleHull.mk_eq_mk** 是 Mathlib 中的一个定理，位于命名空间 `DivisibleHull`。
形式化陈述：mk_eq_mk {m m' : M} {s s' : Nat+} : mk m s = mk m' s' ↔ exists u : Nat+, u
.val • s'.val • m = u.val • s.val • m'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LocalizedModule.mk_eq`：mk_eq {m m' : M} {s s' : S} : mk m s = mk m' s' ↔
 exists u : S, u • s' • m = u • s • m'
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.exists_congr_left`：∀ {α : Sort u} {β : Sort v} {p : α → Prop} (e :
 α ≃ β), (∃ a, p a) ↔ ∃ b, p (e.symm b)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mk_eq_mk {m m' : M} {s s' : ℕ+} :
    mk m s = mk m' s' ↔ ∃ u : ℕ+, u.val • s'.val • m = u.val • s.val • m' := by
  unfold mk
  rw [LocalizedModule.mk_eq, ↑ⁿ.exists_congr_left]
  rfl

/-- If `f : M → ℕ+ → α` respects the equivalence on localization,
lift it to a function `DivisibleHull M → α`. -/
/-
**DivisibleHull.liftOn** 是 Mathlib 中的一个定义，位于命名空间 `DivisibleHull`。
形式化陈述：liftOn {α : Type*} (x : DivisibleHull M) (f : M -> Nat+ -> α) (h : forall 
(m m' : M) (s s' : Nat+), mk m s = mk m' s' -> f m s = f m' s') : α
参数：x : DivisibleHull M；f : M -> Nat+ -> α；h : forall (m m' : M) (s s' : Nat+), m
k m s = mk m' s' -> f m s = f m' s'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f : M → ℕ+ → α` respects the equivalence on localization,
lift it to a function `DivisibleHull M → α`.
-/
def liftOn {α : Type*} (x : DivisibleHull M)
    (f : M → ℕ+ → α)
    (h : ∀ (m m' : M) (s s' : ℕ+), mk m s = mk m' s' → f m s = f m' s') : α :=
  LocalizedModule.liftOn x (fun p ↦ f p.1 (↑ⁿ.symm p.2)) fun p p' heq ↦
    h p.1 p'.1 (↑ⁿ.symm p.2) (↑ⁿ.symm p'.2) <| by
      obtain ⟨u, hu⟩ := heq
      exact mk_eq_mk.mpr ⟨↑ⁿ.symm u, hu⟩

@[simp]
/-
**DivisibleHull.liftOn_mk** 是 Mathlib 中的一个定理，位于命名空间 `DivisibleHull`。
形式化陈述：liftOn_mk {α : Type*} (m : M) (s : Nat+) (f : M -> Nat+ -> α) (h : forall 
(m m' : M) (s s' : Nat+), mk m s = mk m' s' -> f m s = f m' s') : liftOn (mk m s
) f h = f m s
参数：m : M；s : Nat+；f : M -> Nat+ -> α；h : forall (m m' : M) (s s' : Nat+), mk m s
 = mk m' s' -> f m s = f m' s'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem liftOn_mk {α : Type*} (m : M) (s : ℕ+)
    (f : M → ℕ+ → α)
    (h : ∀ (m m' : M) (s s' : ℕ+), mk m s = mk m' s' → f m s = f m' s') :
    liftOn (mk m s) f h = f m s := rfl

/-- If `f : M → ℕ+ → M → ℕ+ → α` respects the equivalence on
localization, lift it to a function `DivisibleHull M → DivisibleHull M → α`. -/
/-
**DivisibleHull.liftOn** 是 Mathlib 中的一个定义，位于命名空间 `DivisibleHull`。
形式化陈述：liftOn {α : Type*} (x : DivisibleHull M) (f : M -> Nat+ -> α) (h : forall 
(m m' : M) (s s' : Nat+), mk m s = mk m' s' -> f m s = f m' s') : α
参数：x : DivisibleHull M；f : M -> Nat+ -> α；h : forall (m m' : M) (s s' : Nat+), m
k m s = mk m' s' -> f m s = f m' s'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f : M → ℕ+ → M → ℕ+ → α` respects the equivalence on
localization, lift it to a function `DivisibleHull M → DivisibleHull M → α`.
-/
def liftOn₂ {α : Type*} (x y : DivisibleHull M)
    (f : M → ℕ+ → M → ℕ+ → α)
    (h : ∀ (m n m' n' : M) (s t s' t' : ℕ+),
      mk m s = mk m' s' → mk n t = mk n' t' → f m s n t = f m' s' n' t') : α :=
  LocalizedModule.liftOn₂ x y (fun p q ↦ f p.1 (↑ⁿ.symm p.2) q.1 (↑ⁿ.symm q.2))
    fun p q p' q' heq heq' ↦
    h p.1 q.1 p'.1 q'.1 (↑ⁿ.symm p.2) (↑ⁿ.symm q.2) (↑ⁿ.symm p'.2) (↑ⁿ.symm q'.2)
      (by
        obtain ⟨u, hu⟩ := heq
        exact mk_eq_mk.mpr ⟨↑ⁿ.symm u, hu⟩)
      (by
        obtain ⟨u, hu⟩ := heq'
        exact mk_eq_mk.mpr ⟨↑ⁿ.symm u, hu⟩)

@[simp]
/-
**DivisibleHull.liftOn** 是 Mathlib 中的一个定义，位于命名空间 `DivisibleHull`。
形式化陈述：liftOn {α : Type*} (x : DivisibleHull M) (f : M -> Nat+ -> α) (h : forall 
(m m' : M) (s s' : Nat+), mk m s = mk m' s' -> f m s = f m' s') : α
参数：x : DivisibleHull M；f : M -> Nat+ -> α；h : forall (m m' : M) (s s' : Nat+), m
k m s = mk m' s' -> f m s = f m' s'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem liftOn₂_mk {α : Type*} (m m' : M) (s s' : ℕ+)
    (f : M → ℕ+ → M → ℕ+ → α)
    (h : ∀ (m n m' n' : M) (s t s' t' : ℕ+),
      mk m s = mk m' s' → mk n t = mk n' t' → f m s n t = f m' s' n' t') :
    liftOn₂ (mk m s) (mk m' s') f h = f m s m' s' := rfl
/-
**DivisibleHull.mk_add_mk** 是 Mathlib 中的一个定理，位于命名空间 `DivisibleHull`。
形式化陈述：mk_add_mk {m1 m2 : M} {s1 s2 : Nat+} : mk m1 s1 + mk m2 s2 = mk (s2.val • 
m1 + s1.val • m2) (s1 * s2)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LocalizedModule.mk_add_mk`：mk_add_mk {m1 m2 : M} {s1 s2 : S} : mk m1 s1 
+ mk m2 s2 = mk (s2 • m1 + s1 • m2) (s1 * s2)
-/
theorem mk_add_mk {m1 m2 : M} {s1 s2 : ℕ+} :
    mk m1 s1 + mk m2 s2 = mk (s2.val • m1 + s1.val • m2) (s1 * s2) := LocalizedModule.mk_add_mk
/-
**DivisibleHull.mk_add_mk_left** 是 Mathlib 中的一个定理，位于命名空间 `DivisibleHull`。
形式化陈述：mk_add_mk_left {m1 m2 : M} {s : Nat+} : mk m1 s + mk m2 s = mk (m1 + m2) s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DivisibleHull.mk_add_mk`：mk_add_mk {m1 m2 : M} {s1 s2 : Nat+} : mk m1 s1
 + mk m2 s2 = mk (s2.val • m1 + s1.val • m2) (s1 * s2)
· 使用定理 `DivisibleHull.mk_eq_mk`：mk_eq_mk {m m' : M} {s s' : Nat+} : mk m s = mk 
m' s' ↔ exists u : Nat+, u.val • s'.val • m = u.val • s.val • m'
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mk_add_mk_left {m1 m2 : M} {s : ℕ+} :
    mk m1 s + mk m2 s = mk (m1 + m2) s := by
  rw [mk_add_mk, mk_eq_mk]
  exact ⟨1, by simp [smul_smul]⟩

@[simp, norm_cast]
/-
**DivisibleHull.coe_add** 是 Mathlib 中的一个定理，位于命名空间 `DivisibleHull`。
形式化陈述：coe_add {m1 m2 : M} : ↑(m1 + m2) = (↑m1 + ↑m2 : DivisibleHull M)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DivisibleHull.mk_add_mk_left`：mk_add_mk_left {m1 m2 : M} {s : Nat+} : mk
 m1 s + mk m2 s = mk (m1 + m2) s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coe_add {m1 m2 : M} : ↑(m1 + m2) = (↑m1 + ↑m2 : DivisibleHull M) := by simp [mk_add_mk_left]

variable (M) in
/-- Coercion from `M` to `DivisibleHull M` as an `AddMonoidHom`. -/
@[simps]
/-
**DivisibleHull.coeAddMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `DivisibleHull`。
形式化陈述：coeAddMonoidHom : M ->+ DivisibleHull M where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Coercion from `M` to `DivisibleHull M` as an `AddMonoidHom`.
-/
def coeAddMonoidHom : M →+ DivisibleHull M where
  toFun := (↑)
  map_zero' := by simp
  map_add' := by simp
/-
**DivisibleHull.nsmul_mk** 是 Mathlib 中的一个定理，位于命名空间 `DivisibleHull`。
形式化陈述：nsmul_mk (a : Nat) (m : M) (s : Nat+) : a • mk m s = mk (a • m) s
参数：a : Nat；m : M；s : Nat+。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M), 0 • a = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `DivisibleHull.mk_zero`：mk_zero (s : Nat+) : mk (0 : M) s = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `add_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M) (m n : ℕ), (m +
 n) • a = m • a + n • a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `DivisibleHull.mk_add_mk_left`：mk_add_mk_left {m1 m2 : M} {s : Nat+} : mk
 m1 s + mk m2 s = mk (m1 + m2) s
-/
theorem nsmul_mk (a : ℕ) (m : M) (s : ℕ+) : a • mk m s = mk (a • m) s := by
  induction a with
  | zero => simp
  | succ n h => simp [add_nsmul, mk_add_mk_left, h]
/-
**DivisibleHull.nnqsmul_mk** 是 Mathlib 中的一个定理，位于命名空间 `DivisibleHull`。
形式化陈述：nnqsmul_mk (a : Rat>=0) (m : M) (s : Nat+) : a • mk m s = mk (a.num • m) (
⟨a.den, a.den_pos⟩ * s)
参数：a : Rat>=0；m : M；s : Nat+。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNRat.den_pos`：∀ (q : ℚ≥0), 0 < q.den
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_natCast`：eq_natCast [FunLike F Nat R] [RingHomClass F Nat R] (f : F) 
: forall n, f n = n
· 使用定理 `NNRat.mul_den_eq_num`：∀ (q : ℚ≥0), q * ↑q.den = ↑q.num
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LocalizedModule.mk'_smul_mk`：∀ {R : Type u} [inst : CommSemiring R] {S :
 Submonoid R} {M : Type v} [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module 
R M] (T : Type u_…
-/
theorem nnqsmul_mk (a : ℚ≥0) (m : M) (s : ℕ+) :
    a • mk m s = mk (a.num • m) (⟨a.den, a.den_pos⟩ * s) := by
  convert! LocalizedModule.mk'_smul_mk ℚ≥0 a.num m ⟨a.den, by simp⟩ (↑ⁿ s)
  simp [IsLocalization.eq_mk'_iff_mul_eq]

section TorsionFree
variable [IsAddTorsionFree M]

/-
**DivisibleHull.mk_eq_mk_iff_smul_eq_smul** 是 Mathlib 中的一个定理，位于命名空间 `DivisibleHu
ll`。
形式化陈述：mk_eq_mk_iff_smul_eq_smul {m m' : M} {s s' : Nat+} : mk m s = mk m' s' ↔ s
'.val • m = s.val • m'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mk_eq_mk_iff_smul_eq_smul {m m' : M} {s s' : ℕ+} :
    mk m s = mk m' s' ↔ s'.val • m = s.val • m' := by
  aesop (add simp [mk_eq_mk, nsmul_right_inj])
/-
**DivisibleHull.mk_left_injective** 是 Mathlib 中的一个定理，位于命名空间 `DivisibleHull`。
形式化陈述：mk_left_injective (s : Nat+) : Function.Injective (fun (m : M) => mk m s)
参数：s : Nat+。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nsmul_right_injective`：∀ {M : Type u_1} [inst : AddMonoid M] [IsAddTorsi
onFree M] {n : ℕ}, n ≠ 0 → Function.Injective fun a => n • a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem mk_left_injective (s : ℕ+) : Function.Injective (fun (m : M) ↦ mk m s) := by
  intro m n h
  simp_rw [mk_eq_mk_iff_smul_eq_smul] at h
  exact nsmul_right_injective (by simp) h
/-
**DivisibleHull.coe_injective** 是 Mathlib 中的一个定理，位于命名空间 `DivisibleHull`。
形式化陈述：coe_injective : Function.Injective ((↑) : M -> DivisibleHull M)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DivisibleHull.mk_left_injective`：mk_left_injective (s : Nat+) : Function
.Injective (fun (m : M) => mk m s)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem coe_injective : Function.Injective ((↑) : M → DivisibleHull M) :=
  mk_left_injective 1

@[simp, norm_cast]
/-
**DivisibleHull.coe_inj** 是 Mathlib 中的一个定理，位于命名空间 `DivisibleHull`。
形式化陈述：coe_inj {m m' : M} : (m : DivisibleHull M) = ↑m' ↔ m = m'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `DivisibleHull.coe_injective`：coe_injective : Function.Injective ((↑) : M
 -> DivisibleHull M)
-/
theorem coe_inj {m m' : M} : (m : DivisibleHull M) = ↑m' ↔ m = m' :=
  coe_injective.eq_iff

end TorsionFree

section Group
variable {M : Type*} [AddCommGroup M]

/-
**DivisibleHull.neg_mk** 是 Mathlib 中的一个定理，位于命名空间 `DivisibleHull`。
形式化陈述：neg_mk (m : M) (s : Nat+) : -mk m s = mk (-m) s
参数：m : M；s : Nat+。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_neg_of_add_eq_zero_left`：∀ {G : Type u_1} [inst : SubtractionMonoid G
] {a b : G}, a + b = 0 → a = -b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DivisibleHull.mk_add_mk_left`：mk_add_mk_left {m1 m2 : M} {s : Nat+} : mk
 m1 s + mk m2 s = mk (m1 + m2) s
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
· 使用定理 `DivisibleHull.mk_zero`：mk_zero (s : Nat+) : mk (0 : M) s = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem neg_mk (m : M) (s : ℕ+) : -mk m s = mk (-m) s :=
  (eq_neg_of_add_eq_zero_left (by simp [mk_add_mk_left])).symm

noncomputable
/-
**DivisibleHull.** 是 Mathlib 中的一个实例，位于命名空间 `DivisibleHull`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMul ℚ (DivisibleHull M) where
  smul a x := (SignType.sign a : ℤ) • (show ℚ≥0 from ⟨|a|, abs_nonneg _⟩) • x
/-
**DivisibleHull.qsmul_def** 是 Mathlib 中的一个定理，位于命名空间 `DivisibleHull`。
形式化陈述：qsmul_def (a : Rat) (x : DivisibleHull M) : a • x = (SignType.sign a : Int
) • (show Rat>=0 from ⟨|a|, abs_nonneg _⟩) • x
参数：a : Rat；x : DivisibleHull M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem qsmul_def (a : ℚ) (x : DivisibleHull M) :
    a • x = (SignType.sign a : ℤ) • (show ℚ≥0 from ⟨|a|, abs_nonneg _⟩) • x :=
  rfl
/-
**DivisibleHull.zero_qsmul** 是 Mathlib 中的一个定理，位于命名空间 `DivisibleHull`。
形式化陈述：zero_qsmul (x : DivisibleHull M) : (0 : Rat) • x = 0
参数：x : DivisibleHull M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `abs_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [A
ddLeftMono α] [AddRightMono α] (a : α), 0 ≤ |a|
· 使用定理 `Rat.instAddLeftMono`：AddLeftMono ℚ
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `sign_zero`：sign_zero : sign (0 : α) = 0
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `abs_zero`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [Add
LeftMono α], |0| = 0
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem zero_qsmul (x : DivisibleHull M) : (0 : ℚ) • x = 0 := by
  simp [qsmul_def]

set_option backward.isDefEq.respectTransparency false in
/-
**DivisibleHull.qsmul_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `DivisibleHull`。
形式化陈述：qsmul_of_nonneg {a : Rat} (h : 0 <= a) (x : DivisibleHull M) : a • x = (sh
ow Rat>=0 from ⟨a, h⟩) • x
参数：h : 0 <= a；x : DivisibleHull M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `abs_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [A
ddLeftMono α] [AddRightMono α] (a : α), 0 ≤ |a|
· 使用定理 `Rat.instAddLeftMono`：AddLeftMono ℚ
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sign_zero`：sign_zero : sign (0 : α) = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `abs_zero`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [Add
LeftMono α], |0| = 0
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `abs_of_pos`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] {a
 : α} [AddLeftMono α], 0 < a → |a| = a
· 使用定理 `sign_pos`：sign_pos (ha : 0 < a) : sign a = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
theorem qsmul_of_nonneg {a : ℚ} (h : 0 ≤ a) (x : DivisibleHull M) :
    a • x = (show ℚ≥0 from ⟨a, h⟩) • x := by
  have := h.eq_or_lt
  aesop (add simp [qsmul_def, abs_of_pos])

set_option backward.isDefEq.respectTransparency false in
/-
**DivisibleHull.qsmul_of_nonpos** 是 Mathlib 中的一个定理，位于命名空间 `DivisibleHull`。
形式化陈述：qsmul_of_nonpos {a : Rat} (h : a <= 0) (x : DivisibleHull M) : a • x = -((
show Rat>=0 from ⟨-a, Left.nonneg_neg_iff.mpr h⟩) • x)
参数：h : a <= 0；x : DivisibleHull M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Left.nonneg_neg_iff`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] 
[AddLeftMono α] {a : α}, 0 ≤ -a ↔ a ≤ 0
· 使用定理 `Rat.instAddLeftMono`：AddLeftMono ℚ
· 使用定理 `abs_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [A
ddLeftMono α] [AddRightMono α] (a : α), 0 ≤ |a|
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sign_zero`：sign_zero : sign (0 : α) = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `abs_zero`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [Add
LeftMono α], |0| = 0
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `abs_of_neg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] {a
 : α} [AddLeftMono α], a < 0 → |a| = -a
· 使用定理 `sign_neg`：sign_neg (ha : a < 0) : sign a = -1
· 使用引理 `SignType.coe_neg`：coe_neg {α : Type*} [One α] [SubtractionMonoid α] (s :
 SignType) : (↑(-s) : α) = -↑s
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
theorem qsmul_of_nonpos {a : ℚ} (h : a ≤ 0) (x : DivisibleHull M) :
    a • x = -((show ℚ≥0 from ⟨-a, Left.nonneg_neg_iff.mpr h⟩) • x) := by
  have := h.eq_or_lt
  aesop (add simp [qsmul_def, abs_of_neg])

set_option backward.isDefEq.respectTransparency false in
/-
**DivisibleHull.qsmul_mk** 是 Mathlib 中的一个定理，位于命名空间 `DivisibleHull`。
形式化陈述：qsmul_mk (a : Rat) (m : M) (s : Nat+) : a • mk m s = mk (a.num • m) (⟨a.de
n, a.den_pos⟩ * s)
参数：a : Rat；m : M；s : Nat+。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Rat.den_pos`：∀ (self : ℚ), 0 < self.den
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DivisibleHull.qsmul_of_nonneg`：qsmul_of_nonneg {a : Rat} (h : 0 <= a) (x
 : DivisibleHull M) : a • x = (show Rat>=0 from ⟨a, h⟩) • x
· 使用定理 `NNRat.den_pos`：∀ (q : ℚ≥0), 0 < q.den
· 使用定理 `DivisibleHull.nnqsmul_mk`：nnqsmul_mk (a : Rat>=0) (m : M) (s : Nat+) : a
 • mk m s = mk (a.num • m) (⟨a.den, a.den_pos⟩ * s)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `natCast_zsmul`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G) (n : ℕ),
 ↑n • a = n • a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_natAbs`：∀ {α : Type u_1} [inst : AddGroupWithOne α] (n : ℤ), ↑n
.natAbs = ↑|n|
· 使用引理 `Int.cast_abs`：cast_abs : (↑|a| : R) = |(a : R)|
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Left.nonneg_neg_iff`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] 
[AddLeftMono α] {a : α}, 0 ≤ -a ↔ a ≤ 0
· 使用定理 `Rat.instAddLeftMono`：AddLeftMono ℚ
· 使用定理 `DivisibleHull.qsmul_of_nonpos`：qsmul_of_nonpos {a : Rat} (h : a <= 0) (x
 : DivisibleHull M) : a • x = -((show Rat>=0 from ⟨-a, Left.nonneg_neg_iff.mpr h
⟩) • x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Int.natAbs_neg`：∀ (a : ℤ), (-a).natAbs = a.natAbs
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem qsmul_mk (a : ℚ) (m : M) (s : ℕ+) :
    a • mk m s = mk (a.num • m) (⟨a.den, a.den_pos⟩ * s) := by
  obtain h | h := le_total 0 a
  · rw [qsmul_of_nonneg h, nnqsmul_mk, ← natCast_zsmul]
    congr
    simpa using h
  · rw [qsmul_of_nonpos h]
    have : a.num.natAbs • m = -a.num • m := by
      rw [← natCast_zsmul]
      congr
      simpa using h
    simp [nnqsmul_mk, this, ← neg_mk]

set_option backward.isDefEq.respectTransparency false in
noncomputable
/-
**DivisibleHull.** 是 Mathlib 中的一个实例，位于命名空间 `DivisibleHull`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Module ℚ (DivisibleHull M) where
  one_smul x := by
    induction x with | mk m s
    simp [qsmul_of_nonneg zero_le_one, nnqsmul_mk]
  zero_smul := zero_qsmul
  smul_zero a := by simp [qsmul_def]
  smul_add a x y := by simp [qsmul_def, smul_add]
  add_smul a b x := by
    induction x with | mk m s
    simp_rw [qsmul_mk, mk_add_mk, mk_eq_mk]
    use 1
    suffices ((a + b).num * a.den * b.den * (s * s)) • m =
        ((a.num * b.den + b.num * a.den) * (a + b).den * (s * s)) • m by
      convert! this using 1
      all_goals
      simp [← natCast_zsmul, smul_smul, ← add_smul]
      ring_nf
    rw [Rat.add_num_den']
  mul_smul a b x := by
    induction x with | mk m s
    simp_rw [qsmul_mk, mk_eq_mk]
    use 1
    suffices ((a * b).num * a.den * b.den * s) • m = (a.num * b.num * (a * b).den * s) • m by
      convert! this using 1
      all_goals
      simp [← natCast_zsmul, smul_smul]
      ring_nf
    rw [Rat.mul_num_den']
/-
**DivisibleHull.zsmul_mk** 是 Mathlib 中的一个定理，位于命名空间 `DivisibleHull`。
形式化陈述：zsmul_mk (a : Int) (m : M) (s : Nat+) : a • mk m s = mk (a • m) s
参数：a : Int；m : M；s : Nat+。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Int.cast_smul_eq_zsmul`：Int.cast_smul_eq_zsmul (n : Int) (b : M) : (n : 
R) • b = n • b
· 使用定理 `Rat.den_pos`：∀ (self : ℚ), 0 < self.den
· 使用定理 `DivisibleHull.qsmul_mk`：qsmul_mk (a : Rat) (m : M) (s : Nat+) : a • mk m
 s = mk (a.num • m) (⟨a.den, a.den_pos⟩ * s)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem zsmul_mk (a : ℤ) (m : M) (s : ℕ+) : a • mk m s = mk (a • m) s := by
  simp [← Int.cast_smul_eq_zsmul ℚ a, qsmul_mk]

end Group

section LinearOrder
variable {M : Type*} [AddCommMonoid M] [LinearOrder M] [IsOrderedCancelAddMonoid M]

set_option backward.privateInPublic true in
/-
**DivisibleHull.lift_aux** 是 Mathlib 中的一个定理，位于命名空间 `DivisibleHull`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem lift_aux (m n m' n' : M) (s t s' t' : ℕ+)
    (h : mk m s = mk m' s') (h' : mk n t = mk n' t') :
    (t.val • m ≤ s.val • n) = (t'.val • m' ≤ s'.val • n') := by
  rw [mk_eq_mk_iff_smul_eq_smul] at h h'
  rw [propext_iff, ← nsmul_le_nsmul_iff_right (mul_ne_zero s'.ne_zero t'.ne_zero)]
  convert! (nsmul_le_nsmul_iff_right (M := M) (mul_ne_zero s.ne_zero t.ne_zero)) using 2
  · simp_rw [smul_smul, mul_rotate s'.val, ← smul_smul, h, smul_smul]
    ring_nf
  · simp_rw [smul_smul, ← mul_rotate s'.val, ← smul_smul, ← h', smul_smul]
    ring_nf

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**DivisibleHull.** 是 Mathlib 中的一个实例，位于命名空间 `DivisibleHull`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LE (DivisibleHull M) where
  le x y := liftOn₂ x y (fun m s n t ↦ t.val • m ≤ s.val • n) lift_aux

@[simp]
/-
**DivisibleHull.mk_le_mk** 是 Mathlib 中的一个定理，位于命名空间 `DivisibleHull`。
形式化陈述：mk_le_mk {m m' : M} {s s' : Nat+} : mk m s <= mk m' s' ↔ s'.val • m <= s.v
al • m'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mk_le_mk {m m' : M} {s s' : ℕ+} :
    mk m s ≤ mk m' s' ↔ s'.val • m ≤ s.val • m' := by rfl

set_option backward.isDefEq.respectTransparency false in
/-
**DivisibleHull.** 是 Mathlib 中的一个实例，位于命名空间 `DivisibleHull`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LinearOrder (DivisibleHull M) where
  le_refl a := by
    induction a with | mk m s
    simp
  le_trans a b c hab hbc := by
    induction a with | mk ma sa
    induction b with | mk mb sb
    induction c with | mk mc sc
    rw [mk_le_mk] at ⊢ hab hbc
    rw [← nsmul_le_nsmul_iff_right (show sb.val ≠ 0 by simp), smul_comm _ _ ma, smul_comm _ _ mc]
    rw [← nsmul_le_nsmul_iff_right (show sc.val ≠ 0 by simp), smul_comm _ _ mb] at hab
    rw [← nsmul_le_nsmul_iff_right (show sa.val ≠ 0 by simp)] at hbc
    exact hab.trans hbc
  le_antisymm a b h h' := by
    induction a with | mk ma sa
    induction b with | mk mb sb
    rw [mk_le_mk] at h h'
    rw [mk_eq_mk_iff_smul_eq_smul]
    exact le_antisymm h h'
  le_total a b := by
    induction a with | mk ma sa
    induction b with | mk mb sb
    simp_rw [mk_le_mk]
    exact le_total _ _
  toDecidableLE := by
    unfold DecidableLE LE.le instLE liftOn₂ LocalizedModule.liftOn₂
    infer_instance

@[simp]
/-
**DivisibleHull.mk_lt_mk** 是 Mathlib 中的一个定理，位于命名空间 `DivisibleHull`。
形式化陈述：mk_lt_mk {m m' : M} {s s' : Nat+} : mk m s < mk m' s' ↔ s'.val • m < s.val
 • m'
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mk_lt_mk {m m' : M} {s s' : ℕ+} : mk m s < mk m' s' ↔ s'.val • m < s.val • m' := by
  simp_rw [lt_iff_not_ge, mk_le_mk]
/-
**DivisibleHull.** 是 Mathlib 中的一个实例，位于命名空间 `DivisibleHull`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsOrderedCancelAddMonoid (DivisibleHull M) :=
  .of_add_lt_add_left (fun a b c h ↦ by
    induction a with | mk ma sa
    induction b with | mk mb sb
    induction c with | mk mc sc
    simp_rw [mk_add_mk]
    rw [mk_lt_mk] at ⊢ h
    simp_rw [PNat.mul_coe, mul_smul, smul_add, smul_smul]
    have := add_lt_add_right (nsmul_lt_nsmul_right (sa * sa).ne_zero h) ((sa * sb * sc.val) • ma)
    simp_rw [PNat.mul_coe, smul_smul] at this
    convert! this using 3 <;> ring)

set_option backward.isDefEq.respectTransparency false in
/-
**DivisibleHull.** 是 Mathlib 中的一个实例，位于命名空间 `DivisibleHull`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsStrictOrderedModule ℚ≥0 (DivisibleHull M) where
  smul_lt_smul_of_pos_left a ha b c h := by
    induction b with | mk mb sb
    induction c with | mk mc sc
    simp_rw [mk_lt_mk] at h
    simp_rw [nnqsmul_mk, mk_lt_mk, smul_smul, PNat.mul_coe]
    simp_rw [mul_right_comm _ _ a.num, mul_smul _ _ mc, mul_smul _ _ mb]
    exact (nsmul_right_strictMono (by simpa using ha.ne.symm)).lt_iff_lt.mpr h
  smul_lt_smul_of_pos_right a ha b c h := by
    induction a with | mk m s
    simp_rw [nnqsmul_mk, mk_lt_mk, smul_smul, PNat.mul_coe, PNat.mk_coe]
    refine smul_lt_smul_of_pos_right ?_ ?_
    · convert! mul_lt_mul_of_pos_right (NNRat.lt_def.mp h) (show 0 < s.val by simp) using 1 <;> ring
    · rw [← mk_zero 1, mk_lt_mk] at ha
      simpa using ha

end LinearOrder

section OrderedGroup
variable {M : Type*} [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M]

set_option backward.isDefEq.respectTransparency false in
/-
**DivisibleHull.** 是 Mathlib 中的一个实例，位于命名空间 `DivisibleHull`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsStrictOrderedModule ℚ (DivisibleHull M) where
  smul_lt_smul_of_pos_left a ha b c h := by
    simp_rw [qsmul_of_nonneg ha.le]
    apply smul_lt_smul_of_pos_left h (by simpa using! ha)
  smul_lt_smul_of_pos_right a ha b c h := by
    apply lt_of_sub_pos
    rw [← sub_smul]
    simp_rw [qsmul_of_nonneg (sub_pos_of_lt h).le]
    apply smul_pos (by simpa [← NNRat.coe_pos] using! h) ha

variable (M) in
/-- Coercion from `M` to `DivisibleHull M` as an `OrderAddMonoidHom`. -/
@[simps!]
/-
**DivisibleHull.coeOrderAddMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `DivisibleHull`。
形式化陈述：coeOrderAddMonoidHom : M ->+o DivisibleHull M where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Coercion from `M` to `DivisibleHull M` as an `OrderAddMonoidHom`.
-/
def coeOrderAddMonoidHom : M →+o DivisibleHull M where
  __ := coeAddMonoidHom M
  monotone' a b h := by simpa using h

/-- `ArchimedeanClass.mk` of an element from `DivisibleHull` only depends on the numerator. -/
/-
**DivisibleHull.archimedeanClassMk_mk_eq** 是 Mathlib 中的一个定理，位于命名空间 `DivisibleHul
l`。
形式化陈述：archimedeanClassMk_mk_eq (m : M) (s s' : Nat+) : ArchimedeanClass.mk (mk m
 s) = ArchimedeanClass.mk (mk m s')
参数：m : M；s s' : Nat+。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DivisibleHull.zsmul_mk`：zsmul_mk (a : Int) (m : M) (s : Nat+) : a • mk m
 s = mk (a • m) s
· 使用定理 `instIsAddTorsionFreeOfAddLeftStrictMonoOfAddRightStrictMono`：∀ {M : Type
 u_3} [inst : AddMonoid M] [inst_1 : LinearOrder M] [AddLeftStrictMono M] [AddRi
ghtStrictMono M],   IsAddTorsionFree M
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
· 使用定理 `natCast_zsmul`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G) (n : ℕ),
 ↑n • a = n • a
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsOrderedAddMonoid.toIsOrderedCancelAddMonoid`：∀ {α : Type u} [inst : Ad
dCommGroup α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedCancelAddMo
noid α
· 使用定理 `IsOrderedCancelAddMonoid.toIsOrderedAddMonoid`：∀ {α : Type u_2} {inst : 
AddCommMonoid α} {inst_1 : Preorder α} [self : IsOrderedCancelAddMonoid α],   Is
OrderedAddMonoid α
· 使用定理 `DivisibleHull.instIsOrderedCancelAddMonoid`：∀ {M : Type u_2} [inst : Add
CommMonoid M] [inst_1 : LinearOrder M] [inst_2 : IsOrderedCancelAddMonoid M],   
IsOrderedCancelAddMonoid (Divisi…
· 使用定理 `ArchimedeanClass.mk_smul`：mk_smul (a : M) {k : K} (h : k != 0) : mk (k •
 a) = mk a
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanInt`：Archimedean ℤ
· 使用定理 `PosSMulStrictMono.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} [inst :
 Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : PartialOrder α]
   [inst_4 : PartialO…
· 使用定理 `instPosSMulStrictMonoIntOfIsOrderedAddMonoid`：∀ {G : Type u_3} [inst : P
artialOrder G] [inst_1 : AddCommGroup G] [IsOrderedAddMonoid G], PosSMulStrictMo
no ℤ G
· 使用定理 `not_false_eq_true`：(¬False) = True
（共 32 条，此处仅展示前 30 条）

--- 原说明 ---
`ArchimedeanClass.mk` of an element from `DivisibleHull` only depends on the num
erator.
-/
theorem archimedeanClassMk_mk_eq (m : M) (s s' : ℕ+) :
    ArchimedeanClass.mk (mk m s) = ArchimedeanClass.mk (mk m s') := by
  suffices (s : ℤ) • mk m s = (s' : ℤ) • mk m s' by
    apply_fun ArchimedeanClass.mk at this
    rw [ArchimedeanClass.mk_smul _ (by simp)] at this
    rw [ArchimedeanClass.mk_smul _ (by simp)] at this
    exact this
  simp_rw [zsmul_mk, mk_eq_mk_iff_smul_eq_smul, natCast_zsmul, smul_smul, mul_comm s'.val]

set_option backward.privateInPublic true in
variable (M) in
/-- Forward direction of `archimedeanClassOrderIso`. -/
private noncomputable
/-
**DivisibleHull.archimedeanClassOrderHom** 是 Mathlib 中的一个定义，位于命名空间 `DivisibleHul
l`。
形式化陈述：archimedeanClassOrderHom : ArchimedeanClass M ->o ArchimedeanClass (Divisi
bleHull M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def archimedeanClassOrderHom : ArchimedeanClass M →o ArchimedeanClass (DivisibleHull M) :=
  ArchimedeanClass.orderHom (coeOrderAddMonoidHom M)

set_option backward.privateInPublic true in
/-- See `archimedeanClassOrderIso_symm_apply` for public API. -/
/-
**DivisibleHull.aux_archimedeanClassMk_mk** 是 Mathlib 中的一个定理，位于命名空间 `DivisibleHu
ll`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See `archimedeanClassOrderIso_symm_apply` for public API.
-/
private theorem aux_archimedeanClassMk_mk (m : M) (s : ℕ+) :
    ArchimedeanClass.mk (mk m s) = archimedeanClassOrderHom M (ArchimedeanClass.mk m) := by
  rw [archimedeanClassOrderHom, ArchimedeanClass.orderHom_mk, coeOrderAddMonoidHom_apply]
  apply archimedeanClassMk_mk_eq

/-- Use `Equiv.injective archimedeanClassOrderIso` for public API. -/
/-
**DivisibleHull.aux_archimedeanClassOrderHom_injective** 是 Mathlib 中的一个定理，位于命名空间
 `DivisibleHull`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Use `Equiv.injective archimedeanClassOrderIso` for public API.
-/
private theorem aux_archimedeanClassOrderHom_injective :
    Function.Injective (archimedeanClassOrderHom M) :=
  ArchimedeanClass.orderHom_injective coe_injective

set_option backward.privateInPublic true in
variable (M) in
/-- Backward direction of `archimedeanClassOrderIso`. -/
private noncomputable
/-
**DivisibleHull.archimedeanClassOrderHomInv** 是 Mathlib 中的一个定义，位于命名空间 `Divisible
Hull`。
形式化陈述：archimedeanClassOrderHomInv : ArchimedeanClass (DivisibleHull M) ->o Archi
medeanClass M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def archimedeanClassOrderHomInv : ArchimedeanClass (DivisibleHull M) →o ArchimedeanClass M :=
  ArchimedeanClass.liftOrderHom (fun x ↦ x.liftOn (fun m s ↦ ArchimedeanClass.mk m)
    (fun _ _ _ _ h ↦ by
      apply aux_archimedeanClassOrderHom_injective
      apply_fun ArchimedeanClass.mk at h
      simpa [aux_archimedeanClassMk_mk] using h))
    (fun a b h ↦ by
      induction a with | mk _ _
      induction b with | mk _ _
      simp_rw [aux_archimedeanClassMk_mk] at h
      simpa using ((archimedeanClassOrderHom M).monotone.strictMono_of_injective
        aux_archimedeanClassOrderHom_injective).le_iff_le.mp h)

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
variable (M) in
/-- The Archimedean classes of `DivisibleHull M` are the same as those of `M`. -/
noncomputable
/-
**DivisibleHull.archimedeanClassOrderIso** 是 Mathlib 中的一个定义，位于命名空间 `DivisibleHul
l`。
形式化陈述：archimedeanClassOrderIso : ArchimedeanClass M ≃o ArchimedeanClass (Divisib
leHull M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def archimedeanClassOrderIso : ArchimedeanClass M ≃o ArchimedeanClass (DivisibleHull M) := by
  apply OrderIso.ofHomInv (archimedeanClassOrderHom M) (archimedeanClassOrderHomInv M)
  · ext a
    induction a with | mk a
    induction a with | mk m s
    suffices ArchimedeanClass.mk (mk m 1) = ArchimedeanClass.mk (mk m s) by
      simpa [archimedeanClassOrderHom, archimedeanClassOrderHomInv]
    simp_rw [aux_archimedeanClassMk_mk]
  · ext a
    induction a with | mk _
    simp [archimedeanClassOrderHom, archimedeanClassOrderHomInv]

@[simp]
/-
**DivisibleHull.archimedeanClassOrderIso_apply** 是 Mathlib 中的一个定理，位于命名空间 `Divisi
bleHull`。
形式化陈述：archimedeanClassOrderIso_apply (a : ArchimedeanClass M) : archimedeanClass
OrderIso M a = ArchimedeanClass.orderHom (coeOrderAddMonoidHom M) a
参数：a : ArchimedeanClass M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedAddMonoid.toIsOrderedCancelAddMonoid`：∀ {α : Type u} [inst : Ad
dCommGroup α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedCancelAddMo
noid α
· 使用定理 `IsOrderedCancelAddMonoid.toIsOrderedAddMonoid`：∀ {α : Type u_2} {inst : 
AddCommMonoid α} {inst_1 : Preorder α} [self : IsOrderedCancelAddMonoid α],   Is
OrderedAddMonoid α
· 使用定理 `DivisibleHull.instIsOrderedCancelAddMonoid`：∀ {M : Type u_2} [inst : Add
CommMonoid M] [inst_1 : LinearOrder M] [inst_2 : IsOrderedCancelAddMonoid M],   
IsOrderedCancelAddMonoid (Divisi…
-/
theorem archimedeanClassOrderIso_apply (a : ArchimedeanClass M) :
    archimedeanClassOrderIso M a = ArchimedeanClass.orderHom (coeOrderAddMonoidHom M) a := rfl

@[simp]
/-
**DivisibleHull.archimedeanClassOrderIso_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `D
ivisibleHull`。
形式化陈述：archimedeanClassOrderIso_symm_apply (m : M) (s : Nat+) : (archimedeanClass
OrderIso M).symm (ArchimedeanClass.mk (mk m s)) = ArchimedeanClass.mk m
参数：m : M；s : Nat+。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedAddMonoid.toIsOrderedCancelAddMonoid`：∀ {α : Type u} [inst : Ad
dCommGroup α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedCancelAddMo
noid α
· 使用定理 `IsOrderedCancelAddMonoid.toIsOrderedAddMonoid`：∀ {α : Type u_2} {inst : 
AddCommMonoid α} {inst_1 : Preorder α} [self : IsOrderedCancelAddMonoid α],   Is
OrderedAddMonoid α
· 使用定理 `DivisibleHull.instIsOrderedCancelAddMonoid`：∀ {M : Type u_2} [inst : Add
CommMonoid M] [inst_1 : LinearOrder M] [inst_2 : IsOrderedCancelAddMonoid M],   
IsOrderedCancelAddMonoid (Divisi…
-/
theorem archimedeanClassOrderIso_symm_apply (m : M) (s : ℕ+) :
    (archimedeanClassOrderIso M).symm (ArchimedeanClass.mk (mk m s)) = ArchimedeanClass.mk m := rfl

end OrderedGroup

end DivisibleHull

