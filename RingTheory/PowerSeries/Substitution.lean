/-
Copyright (c) 2025 Antoine Chambert-Loir, María Inés de Frutos Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos Fernández
-/
module

public import Mathlib.Algebra.MvPolynomial.Coeff
public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import Mathlib.RingTheory.PowerSeries.Evaluation
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Tactic.Ring.NamePowerVars

/-! # Substitutions in power series

A (possibly multivariate) power series can be substituted into
a (univariate) power series if and only if its constant coefficient is nilpotent.

This is a particularization of the substitution of multivariate power series
to the case of univariate power series.

Because of the special API for `PowerSeries`, some results for `MvPowerSeries`
do not immediately apply and a “primed” version is provided here.

-/

@[expose] public section

namespace PowerSeries

variable
  {A : Type*} [CommRing A]
  {R : Type*} [CommRing R] [Algebra A R]
  {τ : Type*}
  {S : Type*} [CommRing S]

open MvPowerSeries.WithPiTopology

/-- (Possibly multivariate) power series which can be substituted in a `PowerSeries`. -/
/-
**PowerSeries.HasSubst** 是 Mathlib 中的一个缩写定义，位于命名空间 `PowerSeries`。
形式化陈述：HasSubst (a : MvPowerSeries τ S) : Prop
参数：a : MvPowerSeries τ S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(Possibly multivariate) power series which can be substituted in a `PowerSeries`
.
-/
abbrev HasSubst (a : MvPowerSeries τ S) : Prop :=
  IsNilpotent (MvPowerSeries.constantCoeff a)
/-
**PowerSeries.hasSubst_iff** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：hasSubst_iff {a : MvPowerSeries τ S} : HasSubst a ↔ MvPowerSeries.HasSubst
 (Function.const Unit a)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.hasSubst_of_constantCoeff_nilpotent`：hasSubst_of_constantC
oeff_nilpotent [Finite σ] {a : σ -> MvPowerSeries τ S} (ha : forall s, IsNilpote
nt (constantCoeff (a s))) : HasSubst a …
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `MvPowerSeries.HasSubst.const_coeff`：∀ {σ : Type u_1} {τ : Type u_4} {S :
 Type u_5} [inst : CommRing S] {a : σ → MvPowerSeries τ S},   MvPowerSeries.HasS
ubst a → ∀ (s : σ), IsNi…
-/
theorem hasSubst_iff {a : MvPowerSeries τ S} :
    HasSubst a ↔ MvPowerSeries.HasSubst (Function.const Unit a) :=
  ⟨fun ha ↦ MvPowerSeries.hasSubst_of_constantCoeff_nilpotent (Function.const Unit ha),
   fun ha ↦ (ha.const_coeff ())⟩
/-
**PowerSeries.HasSubst.const** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries.HasSubst`。
形式化陈述：∀ {τ : Type u_3} {S : Type u_4} [inst : CommRing S] {a : MvPowerSeries τ S
},   PowerSeries.HasSubst a → MvPowerSeries.HasSubst fun x => a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `PowerSeries.hasSubst_iff`：hasSubst_iff {a : MvPowerSeries τ S} : HasSubs
t a ↔ MvPowerSeries.HasSubst (Function.const Unit a)
-/
theorem HasSubst.const {a : MvPowerSeries τ S} (ha : HasSubst a) :
    MvPowerSeries.HasSubst (fun () ↦ a) :=
  hasSubst_iff.mp ha
/-
**PowerSeries.hasSubst_iff_hasEval_of_discreteTopology** 是 Mathlib 中的一个定理，位于命名空间
 `PowerSeries`。
形式化陈述：hasSubst_iff_hasEval_of_discreteTopology [TopologicalSpace S] [DiscreteTop
ology S] {a : MvPowerSeries τ S} : HasSubst a ↔ PowerSeries.HasEval a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.hasSubst_iff`：hasSubst_iff {a : MvPowerSeries τ S} : HasSubs
t a ↔ MvPowerSeries.HasSubst (Function.const Unit a)
· 使用引理 `MvPowerSeries.hasSubst_iff_hasEval_of_discreteTopology`：hasSubst_iff_has
Eval_of_discreteTopology [TopologicalSpace S] [DiscreteTopology S] : HasSubst a 
↔ HasEval a
· 使用定理 `PowerSeries.hasEval_iff`：hasEval_iff {a : S} : HasEval a ↔ MvPowerSeries
.HasEval (fun (_ : Unit) => a)
· 使用定理 `Function.const_def`：const_def {y : β} : (fun _ : α => y) = const α y
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem hasSubst_iff_hasEval_of_discreteTopology
    [TopologicalSpace S] [DiscreteTopology S] {a : MvPowerSeries τ S} :
    HasSubst a ↔ PowerSeries.HasEval a := by
  rw [hasSubst_iff, MvPowerSeries.hasSubst_iff_hasEval_of_discreteTopology, hasEval_iff,
    Function.const_def]
/-
**PowerSeries.HasSubst.hasEval** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries.HasSubst`。
形式化陈述：∀ {τ : Type u_3} {S : Type u_4} [inst : CommRing S] [inst_1 : TopologicalS
pace S] {a : MvPowerSeries τ S},   PowerSeries.HasSubst a → PowerSeries.HasEval 
a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.WithPiTopology.isTopologicallyNilpotent_of_constantCoeff_i
sNilpotent`：isTopologicallyNilpotent_of_constantCoeff_isNilpotent [CommSemiring 
R] {f : MvPowerSeries σ R} (hf : IsNilpotent (constantCoeff f)) : IsTopo…
-/
theorem HasSubst.hasEval [TopologicalSpace S] {a : MvPowerSeries τ S} (ha : HasSubst a) :
    HasEval a := isTopologicallyNilpotent_of_constantCoeff_isNilpotent ha
/-
**PowerSeries.HasSubst.of_constantCoeff_zero** 是 Mathlib 中的一个定理，位于命名空间 `PowerSer
ies.HasSubst`。
形式化陈述：∀ {τ : Type u_3} {S : Type u_4} [inst : CommRing S] {a : MvPowerSeries τ S
},   MvPowerSeries.constantCoeff a = 0 → PowerSeries.HasSubst a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem HasSubst.of_constantCoeff_zero {a : MvPowerSeries τ S}
    (ha : MvPowerSeries.constantCoeff a = 0) : HasSubst a := by
  simp [HasSubst, ha]

/-- A variant of `HasSubst.of_constantCoeff_zero` for `PowerSeries`
to avoid the expansion of `Unit`. -/
/-
**PowerSeries.HasSubst.of_constantCoeff_zero'** 是 Mathlib 中的一个定理，位于命名空间 `PowerSe
ries.HasSubst`。
形式化陈述：∀ {S : Type u_4} [inst : CommRing S] {a : PowerSeries S}, PowerSeries.cons
tantCoeff a = 0 → PowerSeries.HasSubst a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.HasSubst.of_constantCoeff_zero`：∀ {τ : Type u_3} {S : Type u
_4} [inst : CommRing S] {a : MvPowerSeries τ S},   MvPowerSeries.constantCoeff a
 = 0 → PowerSeries.HasSubst a

--- 原说明 ---
A variant of `HasSubst.of_constantCoeff_zero` for `PowerSeries`
to avoid the expansion of `Unit`.
-/
theorem HasSubst.of_constantCoeff_zero' {a : PowerSeries S}
    (ha : PowerSeries.constantCoeff a = 0) : HasSubst a :=
  HasSubst.of_constantCoeff_zero ha
/-
**PowerSeries.HasSubst.X** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries.HasSubst`。
形式化陈述：∀ {τ : Type u_3} {S : Type u_4} [inst : CommRing S] (t : τ), PowerSeries.H
asSubst (MvPowerSeries.X t)
参数：t : τ；MvPowerSeries.X t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.constantCoeff_X`：constantCoeff_X (s : σ) : constantCoeff (
R
-/
protected theorem HasSubst.X (t : τ) :
    HasSubst (MvPowerSeries.X t : MvPowerSeries τ S) := by
  simp [HasSubst]

/-- The univariate `X : R⟦X⟧` can be substituted in power series

This lemma is added because `simp` doesn't find it from `HasSubst.X`. -/
/-
**PowerSeries.HasSubst.X'** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries.HasSubst`。
形式化陈述：∀ {R : Type u_2} [inst : CommRing R], PowerSeries.HasSubst PowerSeries.X
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.HasSubst.X`：∀ {τ : Type u_3} {S : Type u_4} [inst : CommRing
 S] (t : τ), PowerSeries.HasSubst (MvPowerSeries.X t)

--- 原说明 ---
The univariate `X : R⟦X⟧` can be substituted in power series

This lemma is added because `simp` doesn't find it from `HasSubst.X`.
-/
protected theorem HasSubst.X' : HasSubst (X : R⟦X⟧) :=
  HasSubst.X _
/-
**PowerSeries.HasSubst.X_pow** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries.HasSubst`。
形式化陈述：∀ {R : Type u_2} [inst : CommRing R] {n : ℕ}, n ≠ 0 → PowerSeries.HasSubst
 (PowerSeries.X ^ n)
参数：PowerSeries.X ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.HasSubst.of_constantCoeff_zero'`：∀ {S : Type u_4} [inst : Co
mmRing S] {a : PowerSeries S}, PowerSeries.constantCoeff a = 0 → PowerSeries.Has
Subst a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `PowerSeries.constantCoeff_X`：constantCoeff_X : constantCoeff (R
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem HasSubst.X_pow {n : ℕ} (hn : n ≠ 0) : HasSubst (X ^ n : R⟦X⟧) :=
  HasSubst.of_constantCoeff_zero' (by simp [hn])
/-
**PowerSeries.HasSubst.monomial** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries.HasSubst`
。
形式化陈述：∀ {τ : Type u_3} {S : Type u_4} [inst : CommRing S] {n : τ →₀ ℕ},   n ≠ 0 
→ ∀ (s : S), PowerSeries.HasSubst ((MvPowerSeries.monomial n) s)
参数：s : S；(MvPowerSeries.monomial n) s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.HasSubst.of_constantCoeff_zero`：∀ {τ : Type u_3} {S : Type u
_4} [inst : CommRing S] {a : MvPowerSeries τ S},   MvPowerSeries.constantCoeff a
 = 0 → PowerSeries.HasSubst a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPowerSeries.coeff_zero_eq_constantCoeff`：coeff_zero_eq_constantCoeff :
 ⇑(coeff (R
· 使用定理 `MvPowerSeries.coeff_monomial`：coeff_monomial [DecidableEq σ] (m n : σ ->
₀ Nat) (a : R) : coeff m (monomial n a) = if m = n then a else 0
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
-/
protected theorem HasSubst.monomial {n : τ →₀ ℕ} (hn : n ≠ 0) (s : S) :
    HasSubst (MvPowerSeries.monomial n s) := by
  classical
  apply HasSubst.of_constantCoeff_zero
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff, MvPowerSeries.coeff_monomial,
    if_neg hn.symm]

/-- A variant of `HasSubst.monomial` to avoid the expansion of `Unit`. -/
/-
**PowerSeries.HasSubst.monomial'** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries.HasSubst
`。
形式化陈述：∀ {S : Type u_4} [inst : CommRing S] {n : ℕ}, n ≠ 0 → ∀ (s : S), PowerSeri
es.HasSubst ((PowerSeries.monomial n) s)
参数：s : S；(PowerSeries.monomial n) s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.HasSubst.monomial`：∀ {τ : Type u_3} {S : Type u_4} [inst : C
ommRing S] {n : τ →₀ ℕ},   n ≠ 0 → ∀ (s : S), PowerSeries.HasSubst ((MvPowerSeri
es.monomial n) s)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finsupp.single_ne_zero`：single_ne_zero : single a b != 0 ↔ b != 0

--- 原说明 ---
A variant of `HasSubst.monomial` to avoid the expansion of `Unit`.
-/
protected theorem HasSubst.monomial' {n : ℕ} (hn : n ≠ 0) (s : S) :
    HasSubst (monomial n s) :=
  HasSubst.monomial (Finsupp.single_ne_zero.mpr hn) s
/-
**PowerSeries.HasSubst.zero** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries.HasSubst`。
形式化陈述：∀ {R : Type u_2} [inst : CommRing R] {τ : Type u_3}, PowerSeries.HasSubst 
0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.hasSubst_iff`：hasSubst_iff {a : MvPowerSeries τ S} : HasSubs
t a ↔ MvPowerSeries.HasSubst (Function.const Unit a)
· 使用定理 `MvPowerSeries.HasSubst.zero`：∀ {σ : Type u_1} {τ : Type u_4} {S : Type u
_5} [inst : CommRing S], MvPowerSeries.HasSubst fun x => 0
-/
theorem HasSubst.zero : HasSubst (0 : MvPowerSeries τ R) := by
  rw [hasSubst_iff]
  exact MvPowerSeries.HasSubst.zero

/-- A variant of `HasSubst.zero` to avoid the expansion of `Unit`. -/
/-
**PowerSeries.HasSubst.zero'** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries.HasSubst`。
形式化陈述：∀ {R : Type u_2} [inst : CommRing R], PowerSeries.HasSubst 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.HasSubst.zero`：∀ {R : Type u_2} [inst : CommRing R] {τ : Typ
e u_3}, PowerSeries.HasSubst 0

--- 原说明 ---
A variant of `HasSubst.zero` to avoid the expansion of `Unit`.
-/
theorem HasSubst.zero' : HasSubst (0 : PowerSeries R) :=
  PowerSeries.HasSubst.zero

variable {f g : MvPowerSeries τ R}
/-
**PowerSeries.HasSubst.add** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries.HasSubst`。
形式化陈述：∀ {R : Type u_2} [inst : CommRing R] {τ : Type u_3} {f g : MvPowerSeries τ
 R},   PowerSeries.HasSubst f → PowerSeries.HasSubst g → PowerSeries.HasSubst (f
 + g)
参数：f + g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Commute.isNilpotent_add`：isNilpotent_add (h_comm : Commute x y) (hx : Is
Nilpotent x) (hy : IsNilpotent y) : IsNilpotent (x + y)
· 使用定理 `Commute.all`：∀ {S : Type u_3} [inst : CommMagma S] (a b : S), Commute a 
b
-/
theorem HasSubst.add (hf : HasSubst f) (hg : HasSubst g) :
    HasSubst (f + g) :=
  (Commute.all _ _).isNilpotent_add hf hg
/-
**PowerSeries.HasSubst.mul_left** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries.HasSubst`
。
形式化陈述：∀ {R : Type u_2} [inst : CommRing R] {τ : Type u_3} {f g : MvPowerSeries τ
 R},   PowerSeries.HasSubst f → PowerSeries.HasSubst (f * g)
参数：f * g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `Commute.isNilpotent_mul_right`：isNilpotent_mul_right (h_comm : Commute x
 y) (h : IsNilpotent x) : IsNilpotent (x * y)
· 使用定理 `Commute.all`：∀ {S : Type u_3} [inst : CommMagma S] (a b : S), Commute a 
b
-/
theorem HasSubst.mul_left (hf : HasSubst f) :
    HasSubst (f * g) := by
  simp only [HasSubst, map_mul]
  exact (Commute.all _ _).isNilpotent_mul_right hf
/-
**PowerSeries.HasSubst.mul_right** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries.HasSubst
`。
形式化陈述：∀ {R : Type u_2} [inst : CommRing R] {τ : Type u_3} {f g : MvPowerSeries τ
 R},   PowerSeries.HasSubst f → PowerSeries.HasSubst (g * f)
参数：g * f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `Commute.isNilpotent_mul_left`：isNilpotent_mul_left (h_comm : Commute x y
) (h : IsNilpotent y) : IsNilpotent (x * y)
· 使用定理 `Commute.all`：∀ {S : Type u_3} [inst : CommMagma S] (a b : S), Commute a 
b
-/
theorem HasSubst.mul_right (hf : HasSubst f) :
    HasSubst (g * f) := by
  simp only [HasSubst, map_mul]
  exact (Commute.all _ _).isNilpotent_mul_left hf
/-
**PowerSeries.HasSubst.smul** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries.HasSubst`。
形式化陈述：∀ {τ : Type u_3} {S : Type u_4} [inst : CommRing S] (r : MvPowerSeries τ S
) {a : MvPowerSeries τ S},   PowerSeries.HasSubst a → PowerSeries.HasSubst (r • 
a)
参数：r : MvPowerSeries τ S；r • a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.HasSubst.mul_right`：∀ {R : Type u_2} [inst : CommRing R] {τ 
: Type u_3} {f g : MvPowerSeries τ R},   PowerSeries.HasSubst f → PowerSeries.Ha
sSubst (g * f)
-/
theorem HasSubst.smul (r : MvPowerSeries τ S) {a : MvPowerSeries τ S} (ha : HasSubst a) :
    HasSubst (r • a) :=
  ha.mul_right

/-- Families of `PowerSeries` that can be substituted, as an `Ideal`. -/
/-
**PowerSeries.HasSubst.ideal** 是 Mathlib 中的一个定义，位于命名空间 `PowerSeries.HasSubst`。
形式化陈述：{τ : Type u_3} → {S : Type u_4} → [inst : CommRing S] → Ideal (MvPowerSeri
es τ S)
参数：MvPowerSeries τ S。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.HasSubst.add`：∀ {R : Type u_2} [inst : CommRing R] {τ : Type
 u_3} {f g : MvPowerSeries τ R},   PowerSeries.HasSubst f → PowerSeries.HasSubst
 g → PowerSeri…
· 使用定理 `PowerSeries.HasSubst.zero`：∀ {R : Type u_2} [inst : CommRing R] {τ : Typ
e u_3}, PowerSeries.HasSubst 0
· 使用定理 `PowerSeries.HasSubst.smul`：∀ {τ : Type u_3} {S : Type u_4} [inst : CommR
ing S] (r : MvPowerSeries τ S) {a : MvPowerSeries τ S},   PowerSeries.HasSubst a
 → PowerSeries.…

--- 原说明 ---
Families of `PowerSeries` that can be substituted, as an `Ideal`.
-/
noncomputable def HasSubst.ideal : Ideal (MvPowerSeries τ S) where
  carrier := Set.ofPred HasSubst
  add_mem' := HasSubst.add
  zero_mem' := HasSubst.zero
  smul_mem' := HasSubst.smul

/-- A more general version of `HasSubst.smul`. -/
/-
**PowerSeries.HasSubst.smul'** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries.HasSubst`。
形式化陈述：∀ {A : Type u_1} [inst : CommRing A] {R : Type u_2} [inst_1 : CommRing R] 
[inst_2 : Algebra A R] {τ : Type u_3}   {f : MvPowerSeries τ R} (a : A), PowerSe
ries.HasSubst f → PowerSeries.HasSubst (a • f)
参数：a : A；a • f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsNilpotent.smul`：IsNilpotent.smul [MonoidWithZero R] [MonoidWithZero S]
 [MulActionWithZero R S] [SMulCommClass R S S] [IsScalarTower R S S] {a : S} (ha
 : IsN…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A

--- 原说明 ---
A more general version of `HasSubst.smul`.
-/
theorem HasSubst.smul' (a : A) (hf : HasSubst f) :
    HasSubst (a • f) := by
  simp only [HasSubst, MvPowerSeries.constantCoeff_smul]
  exact IsNilpotent.smul hf _
/-
**PowerSeries.HasSubst.smul_X** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries.HasSubst`。
形式化陈述：∀ {A : Type u_1} [inst : CommRing A] {R : Type u_2} [inst_1 : CommRing R] 
[inst_2 : Algebra A R] {τ : Type u_3} (a : A)   (t : τ), PowerSeries.HasSubst (a
 • MvPowerSeries.X t)
参数：a : A；t : τ；a • MvPowerSeries.X t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.HasSubst.smul'`：∀ {A : Type u_1} [inst : CommRing A] {R : Ty
pe u_2} [inst_1 : CommRing R] [inst_2 : Algebra A R] {τ : Type u_3}   {f : MvPow
erSeries τ R} (a…
· 使用定理 `PowerSeries.HasSubst.X`：∀ {τ : Type u_3} {S : Type u_4} [inst : CommRing
 S] (t : τ), PowerSeries.HasSubst (MvPowerSeries.X t)
-/
theorem HasSubst.smul_X (a : A) (t : τ) :
    HasSubst (a • (MvPowerSeries.X t) : MvPowerSeries τ R) :=
  (HasSubst.X t).smul' _
/-
**PowerSeries.HasSubst.smul_X'** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries.HasSubst`。
形式化陈述：∀ {A : Type u_1} [inst : CommRing A] {R : Type u_2} [inst_1 : CommRing R] 
[inst_2 : Algebra A R] (a : A),   PowerSeries.HasSubst (a • PowerSeries.X)
参数：a : A；a • PowerSeries.X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.HasSubst.smul'`：∀ {A : Type u_1} [inst : CommRing A] {R : Ty
pe u_2} [inst_1 : CommRing R] [inst_2 : Algebra A R] {τ : Type u_3}   {f : MvPow
erSeries τ R} (a…
· 使用定理 `PowerSeries.HasSubst.X'`：∀ {R : Type u_2} [inst : CommRing R], PowerSeri
es.HasSubst PowerSeries.X
-/
theorem HasSubst.smul_X' (a : A) : HasSubst (a • X : R⟦X⟧) :=
  HasSubst.X'.smul' _
/-
**PowerSeries.HasSubst.eventually_coeff_pow_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `P
owerSeries.HasSubst`。
形式化陈述：∀ {A : Type u_1} [inst : CommRing A] {f : PowerSeries A},   PowerSeries.Ha
sSubst f → ∀ (n : ℕ), ∀ᶠ (m : ℕ) in Filter.atTop, ∀ n' ≤ n, (PowerSeries.coeff n
') (f ^ m) = 0
参数：n : ℕ；m : ℕ；PowerSeries.coeff n'；f ^ m。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.eventually_of_mem`：eventually_of_mem {f : Filter α} {P : α -> Pro
p} {U : Set α} (hU : U in f) (h : forall x in U, P x) : forallᶠ x in f, P x
· 使用定理 `Filter.Ici_mem_atTop`：Ici_mem_atTop [Preorder α] (a : α) : Ici a in (atT
op : Filter α)
· 使用定理 `PowerSeries.coeff_of_lt_order`：coeff_of_lt_order (n : Nat) (h : ↑n < ord
er φ) : coeff n φ = 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `le_iff_exists_add`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [Canoni
callyOrderedAdd α] {a b : α}, a ≤ b ↔ ∃ c, b = a + c
· 使用定理 `Set.mem_Ici`：∀ {α : Type u_1} [inst : Preorder α] {b x : α}, x ∈ Set.Ici
 b ↔ b ≤ x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `lt_imp_lt_of_le_of_le`：lt_imp_lt_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a < b -> c < d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `PowerSeries.order_mul_ge`：∀ {R : Type u_1} [inst : Semiring R] (φ ψ : Po
werSeries R), φ.order + ψ.order ≤ (φ * ψ).order
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LinearOrderedAddCommMonoidWithTop.toIsOrderedAddMonoid`：∀ {α : Type u_3}
 [self : LinearOrderedAddCommMonoidWithTop α], IsOrderedAddMonoid α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `PowerSeries.le_order_pow_of_constantCoeff_eq_zero`：le_order_pow_of_const
antCoeff_eq_zero (n : Nat) (hf : φ.constantCoeff = 0) : n <= (φ ^ n).order
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `le_add_right`：∀ {α : Type u} [inst : Add α] [inst_1 : Preorder α] [Canon
icallyOrderedAdd α] {a b c : α}, a ≤ b → a ≤ b + c
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Nat.cast_lt`：cast_lt : (m : α) < n ↔ m < n
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma HasSubst.eventually_coeff_pow_eq_zero {f : A⟦X⟧} (hf : HasSubst f) (n : ℕ) :
    ∀ᶠ m in .atTop, ∀ n' ≤ n, coeff n' (f ^ m) = 0 := by
  obtain ⟨k, hk⟩ := id hf
  refine Filter.eventually_of_mem (Filter.Ici_mem_atTop (k * (n + 1))) fun m hm n' hn' ↦
    coeff_of_lt_order _ ?_
  obtain ⟨m, rfl⟩ := le_iff_exists_add.mp (Set.mem_Ici.mp hm)
  grw [pow_add, ← order_mul_ge, pow_mul, ← le_order_pow_of_constantCoeff_eq_zero _
    (by rwa [map_pow]), ← _root_.le_add_right le_rfl, Nat.cast_lt]
  lia

variable {υ : Type*} {T : Type*} [CommRing T] [Algebra R S] [Algebra R T] [Algebra S T]

/-- Substitution of power series into a power series. -/
/-
**PowerSeries.subst** 是 Mathlib 中的一个定义，位于命名空间 `PowerSeries`。
形式化陈述：subst (a : MvPowerSeries τ S) (f : PowerSeries R) : MvPowerSeries τ S
参数：a : MvPowerSeries τ S；f : PowerSeries R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Substitution of power series into a power series.
-/
noncomputable def subst (a : MvPowerSeries τ S) (f : PowerSeries R) :
    MvPowerSeries τ S :=
  MvPowerSeries.subst (fun _ ↦ a) f
/-
**PowerSeries.subst_def** 是 Mathlib 中的一个引理，位于命名空间 `PowerSeries`。
形式化陈述：subst_def (a : MvPowerSeries τ S) (f : PowerSeries R) : subst a f = MvPowe
rSeries.subst (fun _ => a) f
参数：a : MvPowerSeries τ S；f : PowerSeries R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma subst_def (a : MvPowerSeries τ S) (f : PowerSeries R) :
    subst a f = MvPowerSeries.subst (fun _ ↦ a) f := rfl
/-
**PowerSeries.subst_X_comp_const** 是 Mathlib 中的一个引理，位于命名空间 `PowerSeries`。
形式化陈述：subst_X_comp_const {f : R⟦X⟧} {i : τ} : .subst (.X (R
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma subst_X_comp_const {f : R⟦X⟧} {i : τ} :
    .subst (.X (R := R) ∘ fun _ ↦ i) f = f.subst (.X i) := rfl

variable {a : MvPowerSeries τ S} {b : S⟦X⟧}

/-- Substitution of power series into a power series, as an `AlgHom`. -/
/-
**PowerSeries.substAlgHom** 是 Mathlib 中的一个定义，位于命名空间 `PowerSeries`。
形式化陈述：substAlgHom (ha : HasSubst a) : PowerSeries R ->ₐ[R] MvPowerSeries τ S
参数：ha : HasSubst a。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.HasSubst.const`：∀ {τ : Type u_3} {S : Type u_4} [inst : Comm
Ring S] {a : MvPowerSeries τ S},   PowerSeries.HasSubst a → MvPowerSeries.HasSub
st fun x => a

--- 原说明 ---
Substitution of power series into a power series, as an `AlgHom`.
-/
noncomputable def substAlgHom (ha : HasSubst a) :
    PowerSeries R →ₐ[R] MvPowerSeries τ S :=
  MvPowerSeries.substAlgHom ha.const
/-
**PowerSeries.coe_substAlgHom** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：coe_substAlgHom (ha : HasSubst a) : ⇑(substAlgHom ha) = subst (R
参数：ha : HasSubst a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.coe_substAlgHom`：coe_substAlgHom (ha : HasSubst a) : ⇑(sub
stAlgHom ha) = subst (R
· 使用定理 `PowerSeries.HasSubst.const`：∀ {τ : Type u_3} {S : Type u_4} [inst : Comm
Ring S] {a : MvPowerSeries τ S},   PowerSeries.HasSubst a → MvPowerSeries.HasSub
st fun x => a
-/
theorem coe_substAlgHom (ha : HasSubst a) :
    ⇑(substAlgHom ha) = subst (R := R) a :=
  MvPowerSeries.coe_substAlgHom ha.const

attribute [local instance] DiscreteTopology.instContinuousSMul in
/-- Rewrite `PowerSeries.substAlgHom` as `PowerSeries.aeval`.

Its use is discouraged because it introduces a topology and might lead
into awkward comparisons. -/
/-
**PowerSeries.substAlgHom_eq_aeval** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：substAlgHom_eq_aeval [UniformSpace R] [DiscreteUniformity R] [UniformSpace
 S] [DiscreteUniformity S] (ha : HasSubst a) : (substAlgHom ha : R⟦X⟧ ->ₐ[R] MvP
owerSeries τ S) = PowerSeries.aeval ha.hasEval
参数：ha : HasSubst a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `instIsUniformAddGroupOfDiscreteUniformity`：∀ {G : Type u_1} [inst : AddG
roup G] [inst_1 : UniformSpace G] [DiscreteUniformity G], IsUniformAddGroup G
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `DiscreteTopology.topologicalRing`：∀ {R : Type u_1} [inst : TopologicalSp
ace R] [inst_1 : NonUnitalNonAssocRing R] [DiscreteTopology R],   IsTopologicalR
ing R
· 使用定理 `DiscreteUniformity.instDiscreteTopology`：∀ (X : Type u_1) [u : UniformSp
ace X] [DiscreteUniformity X], DiscreteTopology X
· 使用定理 `MvPowerSeries.WithPiTopology.instIsUniformAddGroup`：instIsUniformAddGrou
p [AddGroup R] [IsUniformAddGroup R] : IsUniformAddGroup (MvPowerSeries σ R)
· 使用定理 `MvPowerSeries.WithPiTopology.instT2Space`：instT2Space [T2Space R] : T2Sp
ace (MvPowerSeries σ R)
· 使用定理 `T25Space.t2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T25Space
 X], T2Space X
· 使用定理 `T3Space.t25Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T3Space 
X], T25Space X
· 使用定理 `instT3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T0Space X] [R
egularSpace X], T3Space X
· 使用定理 `T1Space.t0Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T1Space X
], T0Space X
· 使用定理 `instT1SpaceOfDiscreteTopology`：∀ {X : Type u_1} [inst : TopologicalSpace
 X] [DiscreteTopology X], T1Space X
· 使用定理 `UniformSpace.to_regularSpace`：∀ {α : Type u} [inst : UniformSpace α], Re
gularSpace α
· 使用定理 `MvPowerSeries.WithPiTopology.instCompleteSpace`：instCompleteSpace [Compl
eteSpace R] : CompleteSpace (MvPowerSeries σ R)
· 使用定理 `DiscreteUniformity.instCompleteSpace`：∀ {α : Type u} [uniformSpace : Uni
formSpace α] [DiscreteUniformity α], CompleteSpace α
· 使用定理 `MvPowerSeries.WithPiTopology.instIsTopologicalRing`：instIsTopologicalRin
g [Ring R] [IsTopologicalRing R] : IsTopologicalRing (MvPowerSeries σ R)
· 使用定理 `MvPowerSeries.LinearTopology.instIsLinearTopologyOfMulOpposite`：∀ {σ : T
ype u_1} {R : Type u_2} [inst : Ring R] [inst_1 : TopologicalSpace R] [IsLinearT
opology R R]   [IsLinearTopology Rᵐᵒᵖ R], IsLinearTo…
· 使用定理 `IsLinearTopology.instOfDiscreteTopology`：∀ {R : Type u_1} {M : Type u_3}
 [inst : Ring R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [inst_
3 : TopologicalSpace M] [Disc…
· 使用定理 `MvPowerSeries.WithPiTopology.instContinuousSMul`：∀ {σ : Type u_1} {R : T
ype u_2} [inst : TopologicalSpace R] {S : Type u_3} [inst_1 : Semiring S]   [ins
t_2 : TopologicalSpace S] [inst_3 : C…
· 使用定理 `DiscreteTopology.instContinuousSMul`：DiscreteTopology.instContinuousSMul
 [IsTopologicalSemiring A] [DiscreteTopology R] : ContinuousSMul R A
· 使用定理 `PowerSeries.HasSubst.hasEval`：∀ {τ : Type u_3} {S : Type u_4} [inst : Co
mmRing S] [inst_1 : TopologicalSpace S] {a : MvPowerSeries τ S},   PowerSeries.H
asSubst a → PowerS…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.substAlgHom_apply`：substAlgHom_apply (ha : HasSubst a) (f 
: MvPowerSeries σ R) : substAlgHom ha f = subst a f
· 使用定理 `PowerSeries.HasSubst.const`：∀ {τ : Type u_3} {S : Type u_4} [inst : Comm
Ring S] {a : MvPowerSeries τ S},   PowerSeries.HasSubst a → MvPowerSeries.HasSub
st fun x => a
· 使用定理 `MvPowerSeries.HasSubst.hasEval`：∀ {σ : Type u_1} {τ : Type u_4} {S : Typ
e u_5} [inst : CommRing S] {a : σ → MvPowerSeries τ S}   [inst_1 : TopologicalSp
ace S], MvPowerSerie…
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `MvPowerSeries.substAlgHom_eq_aeval`：substAlgHom_eq_aeval [UniformSpace R
] [DiscreteUniformity R] [UniformSpace S] [DiscreteUniformity S] (ha : HasSubst 
a) : (substAlgHom ha : M…

--- 原说明 ---
Rewrite `PowerSeries.substAlgHom` as `PowerSeries.aeval`.

Its use is discouraged because it introduces a topology and might lead
into awkward comparisons.
-/
theorem substAlgHom_eq_aeval
    [UniformSpace R] [DiscreteUniformity R] [UniformSpace S] [DiscreteUniformity S]
    (ha : HasSubst a) :
    (substAlgHom ha : R⟦X⟧ →ₐ[R] MvPowerSeries τ S) = PowerSeries.aeval ha.hasEval := by
  ext1 f
  simpa [substAlgHom] using! congr_fun (MvPowerSeries.substAlgHom_eq_aeval ha.const) f
/-
**PowerSeries.subst_add** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：subst_add (ha : HasSubst a) (f g : PowerSeries R) : subst a (f + g) = subs
t a f + subst a g
参数：ha : HasSubst a；f g : PowerSeries R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PowerSeries.coe_substAlgHom`：coe_substAlgHom (ha : HasSubst a) : ⇑(subst
AlgHom ha) = subst (R
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
-/
theorem subst_add (ha : HasSubst a) (f g : PowerSeries R) :
    subst a (f + g) = subst a f + subst a g := by
  rw [← coe_substAlgHom ha, map_add]
/-
**PowerSeries.subst_sub** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：subst_sub (ha : HasSubst a) (f g : PowerSeries R) : subst a (f - g) = subs
t a f - subst a g
参数：ha : HasSubst a；f g : PowerSeries R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PowerSeries.coe_substAlgHom`：coe_substAlgHom (ha : HasSubst a) : ⇑(subst
AlgHom ha) = subst (R
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
-/
theorem subst_sub (ha : HasSubst a) (f g : PowerSeries R) :
    subst a (f - g) = subst a f - subst a g := by
  rw [← coe_substAlgHom ha, map_sub]
/-
**PowerSeries.subst_zero_eq_C_constantCoeff** 是 Mathlib 中的一个引理，位于命名空间 `PowerSeri
es`。
形式化陈述：subst_zero_eq_C_constantCoeff {f : PowerSeries R} : f.subst 0 = (MvPowerSe
ries.C f.constantCoeff (σ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MvPowerSeries.subst_zero_eq_C_constantCoeff`：subst_zero_eq_C_constantCoe
ff {f : MvPowerSeries σ R} : f.subst (0 : σ -> MvPowerSeries τ S) = (C f.constan
tCoeff).map (algebraMap R S)
-/
lemma subst_zero_eq_C_constantCoeff {f : PowerSeries R} :
    f.subst 0 = (MvPowerSeries.C f.constantCoeff (σ := τ)).map (algebraMap R S) :=
  MvPowerSeries.subst_zero_eq_C_constantCoeff

@[simp]
/-
**PowerSeries.subst_zero_of_constantCoeff_zero** 是 Mathlib 中的一个定理，位于命名空间 `PowerS
eries`。
形式化陈述：subst_zero_of_constantCoeff_zero {f : PowerSeries R} (hf : f.constantCoeff
 = 0) : subst (0 : MvPowerSeries τ S) f = 0
参数：hf : f.constantCoeff = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MvPowerSeries.subst_zero_of_constantCoeff_zero`：subst_zero_of_constantCo
eff_zero {f : MvPowerSeries σ R} (hf : f.constantCoeff = 0) : f.subst (0 : σ -> 
MvPowerSeries τ S) = 0
-/
theorem subst_zero_of_constantCoeff_zero {f : PowerSeries R} (hf : f.constantCoeff = 0) :
    subst (0 : MvPowerSeries τ S) f = 0 :=
  MvPowerSeries.subst_zero_of_constantCoeff_zero hf
/-
**PowerSeries.subst_pow** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：subst_pow (ha : HasSubst a) (f : PowerSeries R) (n : Nat) : subst a (f ^ n
) = (subst a f) ^ n
参数：ha : HasSubst a；f : PowerSeries R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PowerSeries.coe_substAlgHom`：coe_substAlgHom (ha : HasSubst a) : ⇑(subst
AlgHom ha) = subst (R
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
-/
theorem subst_pow (ha : HasSubst a) (f : PowerSeries R) (n : ℕ) :
    subst a (f ^ n) = (subst a f) ^ n := by
  rw [← coe_substAlgHom ha, map_pow]
/-
**PowerSeries.subst_mul** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：subst_mul (ha : HasSubst a) (f g : PowerSeries R) : subst a (f * g) = subs
t a f * subst a g
参数：ha : HasSubst a；f g : PowerSeries R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PowerSeries.coe_substAlgHom`：coe_substAlgHom (ha : HasSubst a) : ⇑(subst
AlgHom ha) = subst (R
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
-/
theorem subst_mul (ha : HasSubst a) (f g : PowerSeries R) :
    subst a (f * g) = subst a f * subst a g := by
  rw [← coe_substAlgHom ha, map_mul]
/-
**PowerSeries.subst_smul** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：subst_smul [Algebra A S] [IsScalarTower A R S] (ha : HasSubst a) (r : A) (
f : PowerSeries R) : subst a (r • f) = r • (subst a f)
参数：ha : HasSubst a；r : A；f : PowerSeries R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PowerSeries.coe_substAlgHom`：coe_substAlgHom (ha : HasSubst a) : ⇑(subst
AlgHom ha) = subst (R
· 使用定理 `AlgHom.map_smul_of_tower`：map_smul_of_tower {R'} [SMul R' A] [SMul R' B]
 [LinearMap.CompatibleSMul A B R' R] (r : R') (x : A) : φ (r • x) = r • φ x
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `MvPowerSeries.instIsScalarTower`：∀ {σ : Type u_1} {R : Type u_2} {A : Ty
pe u_3} {S : Type u_4} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : Add
CommMonoid A] [inst_3…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
theorem subst_smul [Algebra A S] [IsScalarTower A R S]
    (ha : HasSubst a) (r : A) (f : PowerSeries R) :
    subst a (r • f) = r • (subst a f) := by
  rw [← coe_substAlgHom ha, AlgHom.map_smul_of_tower]
/-
**PowerSeries.coeff_subst_finite** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：coeff_subst_finite (ha : HasSubst a) (f : PowerSeries R) (e : τ ->₀ Nat) :
 (fun (d : Nat) => coeff d f • MvPowerSeries.coeff e (a ^ d)).HasFiniteSupport
参数：ha : HasSubst a；f : PowerSeries R；e : τ ->₀ Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.HasFiniteSupport.eq_1`：∀ {α : Type u_1} {M : Type u_2} [inst : 
Zero M] (f : α → M), Function.HasFiniteSupport f = (Function.support f).Finite
· 使用定理 `instSubsingletonPUnit`：Subsingleton PUnit.{u_1}
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.preimage_eq_iff_eq_image`：preimage_eq_iff_eq_image {α β} (e : α ≃ 
β) (s t) : e ⁻¹' s = t ↔ s = e '' t
· 使用定理 `Function.support_comp_eq_preimage`：∀ {ι : Type u_1} {κ : Type u_2} {M : 
Type u_3} [inst : Zero M] (g : κ → M) (f : ι → κ),   Function.support (g ∘ f) = 
f ⁻¹' Function.support …
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.eq_comp_symm`：eq_comp_symm {α β γ} (e : α ≃ β) (f : β -> γ) (g : α
 -> γ) : f = g ∘ e.symm ↔ f ∘ e = g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finsupp.prod_pow`：prod_pow [Fintype α] (f : α ->₀ Nat) (g : α -> N) : (f
.prod fun a b => g a ^ b) = ∏ a, g a ^ f a
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.univ_unique`：univ_unique [Unique α] : (univ : Finset α) = {defaul
t}
· 使用定理 `Finset.prod_singleton`：prod_singleton (f : ι -> M) (a : ι) : ∏ x in sing
leton a, f x = f a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finsupp.uniqueLinearEquiv_symm_apply`：∀ (R : Type u_1) {α : Type u_3} (M
 : Type u_4) [inst : AddCommMonoid M] [inst_1 : Semiring R]   [inst_2 : _root_.M
odule R M] [inst_3 : Subsi…
· 使用定理 `Finsupp.uniqueLinearEquiv_symm_apply_apply`：∀ (R : Type u_1) {α : Type u
_3} (M : Type u_4) [inst : AddCommMonoid M] [inst_1 : Semiring R]   [inst_2 : _r
oot_.Module R M] (a : α) [inst_3…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.Finite.image`：∀ {α : Type u} {β : Type v} {s : Set α} (f : α → β), s
.Finite → (f '' s).Finite
· 使用定理 `MvPowerSeries.coeff_subst_finite`：coeff_subst_finite (ha : HasSubst a) (
f : MvPowerSeries σ R) (e : τ ->₀ Nat) : (fun d => coeff d f • (coeff e (d.prod 
fun s e => (a s) ^ e))…
· 使用定理 `PowerSeries.HasSubst.const`：∀ {τ : Type u_3} {S : Type u_4} [inst : Comm
Ring S] {a : MvPowerSeries τ S},   PowerSeries.HasSubst a → MvPowerSeries.HasSub
st fun x => a
-/
theorem coeff_subst_finite (ha : HasSubst a) (f : PowerSeries R) (e : τ →₀ ℕ) :
    (fun (d : ℕ) ↦ coeff d f • MvPowerSeries.coeff e (a ^ d)).HasFiniteSupport := by
  rw [Function.HasFiniteSupport]
  convert (MvPowerSeries.coeff_subst_finite ha.const f e).image
    (Finsupp.uniqueLinearEquiv ℕ ℕ ()).toEquiv
  rw [← Equiv.preimage_eq_iff_eq_image, ← Function.support_comp_eq_preimage]
  apply congr_arg
  rw [← Equiv.eq_comp_symm]
  ext
  simp [coeff]
/-
**PowerSeries.coeff_subst_finite'** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：coeff_subst_finite' (hb : HasSubst b) (f : PowerSeries R) (e : Nat) : (fun
 (d : Nat) => coeff d f • (PowerSeries.coeff e (b ^ d))).HasFiniteSupport
参数：hb : HasSubst b；f : PowerSeries R；e : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.coeff_subst_finite`：coeff_subst_finite (ha : HasSubst a) (f 
: PowerSeries R) (e : τ ->₀ Nat) : (fun (d : Nat) => coeff d f • MvPowerSeries.c
oeff e (a ^ d)).HasF…
-/
theorem coeff_subst_finite' (hb : HasSubst b) (f : PowerSeries R) (e : ℕ) :
    (fun (d : ℕ) ↦ coeff d f • (PowerSeries.coeff e (b ^ d))).HasFiniteSupport :=
  coeff_subst_finite hb f _
/-
**PowerSeries.coeff_subst** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：coeff_subst (ha : HasSubst a) (f : PowerSeries R) (e : τ ->₀ Nat) : MvPowe
rSeries.coeff e (subst a f) = finsum (fun (d : Nat) => coeff d f • (MvPowerSerie
s.coeff e (a ^ d)))
参数：ha : HasSubst a；f : PowerSeries R；e : τ ->₀ Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.subst.eq_1`：∀ {R : Type u_2} [inst : CommRing R] {τ : Type u
_3} {S : Type u_4} [inst_1 : CommRing S] [inst_2 : Algebra R S]   (a : MvPowerSe
ries τ S) (f…
· 使用定理 `MvPowerSeries.coeff_subst`：coeff_subst (ha : HasSubst a) (f : MvPowerSer
ies σ R) (e : τ ->₀ Nat) : coeff e (subst a f) = finsum (fun d => coeff d f • (c
oeff e (d.prod …
· 使用定理 `PowerSeries.HasSubst.const`：∀ {τ : Type u_3} {S : Type u_4} [inst : Comm
Ring S] {a : MvPowerSeries τ S},   PowerSeries.HasSubst a → MvPowerSeries.HasSub
st fun x => a
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `instSubsingletonPUnit`：Subsingleton PUnit.{u_1}
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `finsum_comp_equiv`：∀ {α : Type u_1} {β : Type u_2} {M : Type u_5} [inst 
: AddCommMonoid M] (e : α ≃ β) {f : β → M},   ∑ᶠ (i : α), f (e i) = ∑ᶠ (i' : β),
 f i'
· 使用定理 `finsum_congr`：∀ {M : Type u_2} {α : Sort u_4} [inst : AddCommMonoid M] {
f g : α → M}, (∀ (x : α), f x = g x) → finsum f = finsum g
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finsupp.uniqueLinearEquiv_symm_apply`：∀ (R : Type u_1) {α : Type u_3} (M
 : Type u_4) [inst : AddCommMonoid M] [inst_1 : Semiring R]   [inst_2 : _root_.M
odule R M] [inst_3 : Subsi…
· 使用定理 `Finsupp.prod_single_index`：prod_single_index {a : α} {b : M} {h : α -> M
 -> N} (h_zero : h a 0 = 1) : (single a b).prod h = h a b
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coeff_subst (ha : HasSubst a) (f : PowerSeries R) (e : τ →₀ ℕ) :
    MvPowerSeries.coeff e (subst a f) =
      finsum (fun (d : ℕ) ↦
        coeff d f • (MvPowerSeries.coeff e (a ^ d))) := by
  rw [subst, MvPowerSeries.coeff_subst ha.const f e, ← finsum_comp_equiv
    (Finsupp.uniqueLinearEquiv ℕ ℕ ()).toEquiv.symm]
  apply finsum_congr
  intro
  congr
  simp
/-
**PowerSeries.coeff_subst'** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：coeff_subst' {b : S⟦X⟧} (hb : HasSubst b) (f : R⟦X⟧) (e : Nat) : coeff e (
f.subst b) = finsum (fun (d : Nat) => coeff d f • PowerSeries.coeff e (b ^ d))
参数：hb : HasSubst b；f : R⟦X⟧；e : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.coeff_subst`：coeff_subst (ha : HasSubst a) (f : PowerSeries 
R) (e : τ ->₀ Nat) : MvPowerSeries.coeff e (subst a f) = finsum (fun (d : Nat) =
> coeff d f •…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coeff_subst' {b : S⟦X⟧} (hb : HasSubst b) (f : R⟦X⟧) (e : ℕ) :
    coeff e (f.subst b) =
      finsum (fun (d : ℕ) ↦
        coeff d f • PowerSeries.coeff e (b ^ d)) := by
  simp [PowerSeries.coeff, coeff_subst hb]
/-
**PowerSeries.constantCoeff_subst** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：constantCoeff_subst (ha : HasSubst a) (f : PowerSeries R) : MvPowerSeries.
constantCoeff (subst a f) = finsum (fun d => coeff d f • MvPowerSeries.constantC
oeff (a ^ d))
参数：ha : HasSubst a；f : PowerSeries R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.coeff_subst`：coeff_subst (ha : HasSubst a) (f : PowerSeries 
R) (e : τ ->₀ Nat) : MvPowerSeries.coeff e (subst a f) = finsum (fun (d : Nat) =
> coeff d f •…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem constantCoeff_subst (ha : HasSubst a) (f : PowerSeries R) :
    MvPowerSeries.constantCoeff (subst a f) =
      finsum (fun d ↦ coeff d f • MvPowerSeries.constantCoeff (a ^ d)) := by
  simp only [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_subst ha f 0]

@[simp]
/-
**PowerSeries.coeff_subst_X_pow** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：coeff_subst_X_pow {k : Nat} (hk : k != 0) (f : PowerSeries R) (n : Nat) : 
coeff n (subst (X ^ k) f) = ite (k ∣ n) (algebraMap R S (coeff (n / k) f)) 0
参数：hk : k != 0；f : PowerSeries R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `PowerSeries.coeff_subst'`：coeff_subst' {b : S⟦X⟧} (hb : HasSubst b) (f :
 R⟦X⟧) (e : Nat) : coeff e (f.subst b) = finsum (fun (d : Nat) => coeff d f • Po
werSeries.coef…
· 使用定理 `PowerSeries.HasSubst.X_pow`：∀ {R : Type u_2} [inst : CommRing R] {n : ℕ}
, n ≠ 0 → PowerSeries.HasSubst (PowerSeries.X ^ n)
· 使用定理 `finsum_eq_single`：∀ {M : Type u_2} {α : Sort u_4} [inst : AddCommMonoid 
M] (f : α → M) (a : α),   (∀ (x : α), x ≠ a → f x = 0) → ∑ᶠ (x : α), f x = f a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `PowerSeries.coeff_X_pow`：coeff_X_pow (m n : Nat) : coeff m ((X : R⟦X⟧) ^
 n) = if m = n then 1 else 0
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `Nat.mul_div_cancel_left`：∀ (m : ℕ) {n : ℕ}, 0 < n → n * m / n = m
· 使用定理 `Ne.pos`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_1 : Zero 
α] [IsBotZeroClass α], a ≠ 0 → 0 < a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `Nat.mul_div_cancel'`：∀ {n m : ℕ}, n ∣ m → n * (m / n) = m
· 使用定理 `PowerSeries.coeff_X_pow_self`：coeff_X_pow_self (n : Nat) : coeff n ((X :
 R⟦X⟧) ^ n) = 1
· 使用定理 `Algebra.algebraMap_eq_smul_one`：algebraMap_eq_smul_one (r : R) : algebra
Map R A r = r • (1 : A)
· 使用定理 `finsum_eq_zero_of_forall_eq_zero`：∀ {α : Type u_1} {M : Type u_5} [inst 
: AddCommMonoid M] {f : α → M}, (∀ (x : α), f x = 0) → ∑ᶠ (i : α), f i = 0
-/
theorem coeff_subst_X_pow {k : ℕ} (hk : k ≠ 0) (f : PowerSeries R) (n : ℕ) :
    coeff n (subst (X ^ k) f) = ite (k ∣ n) (algebraMap R S (coeff (n / k) f)) 0 := by
  split_ifs with h
  · rw [coeff_subst' (.X_pow hk), finsum_eq_single _ (n / k), ← pow_mul, Nat.mul_div_cancel' h,
      coeff_X_pow_self, Algebra.algebraMap_eq_smul_one]
    intro j hj
    rw [← pow_mul, coeff_X_pow, if_neg, smul_zero]
    contrapose hj
    rw [hj, Nat.mul_div_cancel_left j hk.pos]
  · rw [coeff_subst' (.X_pow hk), finsum_eq_zero_of_forall_eq_zero]
    intro j
    rw [← pow_mul, coeff_X_pow, if_neg, smul_zero]
    contrapose h
    use j

@[simp]
/-
**PowerSeries.constantCoeff_subst_X_pow** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：constantCoeff_subst_X_pow {k : Nat} (hk : k != 0) (f : PowerSeries R) : co
nstantCoeff (subst (X ^ k) f) = algebraMap R S f.constantCoeff
参数：hk : k != 0；f : PowerSeries R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PowerSeries.coeff_zero_eq_constantCoeff`：coeff_zero_eq_constantCoeff : ⇑
(coeff (R
· 使用定理 `PowerSeries.coeff_subst_X_pow`：coeff_subst_X_pow {k : Nat} (hk : k != 0)
 (f : PowerSeries R) (n : Nat) : coeff n (subst (X ^ k) f) = ite (k ∣ n) (algebr
aMap R S (coeff (n …
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `dvd_zero`：dvd_zero (a : α) : a ∣ 0
· 使用定理 `Nat.zero_div`：∀ (b : ℕ), 0 / b = 0
-/
theorem constantCoeff_subst_X_pow {k : ℕ} (hk : k ≠ 0) (f : PowerSeries R) :
    constantCoeff (subst (X ^ k) f) = algebraMap R S f.constantCoeff := by
  rw [← coeff_zero_eq_constantCoeff, coeff_subst_X_pow hk, if_pos (dvd_zero k),
    Nat.zero_div, coeff_zero_eq_constantCoeff]
/-
**PowerSeries.constantCoeff_subst_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries
`。
形式化陈述：constantCoeff_subst_eq_zero (ha : a.constantCoeff = 0) (f : PowerSeries R)
 (hf : f.constantCoeff = 0) : MvPowerSeries.constantCoeff (subst a f) = 0
参数：ha : a.constantCoeff = 0；f : PowerSeries R；hf : f.constantCoeff = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.constantCoeff_subst_eq_zero`：constantCoeff_subst_eq_zero (
ha : HasSubst a) (ha' : forall i, (a i).constantCoeff = 0) {f : MvPowerSeries σ 
R} (hf : f.constantCoeff = 0) :…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `PowerSeries.hasSubst_iff`：hasSubst_iff {a : MvPowerSeries τ S} : HasSubs
t a ↔ MvPowerSeries.HasSubst (Function.const Unit a)
· 使用定理 `PowerSeries.HasSubst.of_constantCoeff_zero`：∀ {τ : Type u_3} {S : Type u
_4} [inst : CommRing S] {a : MvPowerSeries τ S},   MvPowerSeries.constantCoeff a
 = 0 → PowerSeries.HasSubst a
-/
theorem constantCoeff_subst_eq_zero (ha : a.constantCoeff = 0) (f : PowerSeries R)
    (hf : f.constantCoeff = 0) : MvPowerSeries.constantCoeff (subst a f) = 0 := by
  have := MvPowerSeries.constantCoeff_subst_eq_zero
    (hasSubst_iff.mp <| HasSubst.of_constantCoeff_zero ha) (fun _ ↦ ha) hf
  simpa [hasSubst_iff]
/-
**PowerSeries.map_algebraMap_eq_subst_X** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：map_algebraMap_eq_subst_X (f : R⟦X⟧) : map (algebraMap R S) f = subst X f
参数：f : R⟦X⟧。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.map_algebraMap_eq_subst_X`：map_algebraMap_eq_subst_X (f : 
MvPowerSeries σ R) : map (algebraMap R S) f = subst X f
-/
theorem map_algebraMap_eq_subst_X (f : R⟦X⟧) :
    map (algebraMap R S) f = subst X f :=
  MvPowerSeries.map_algebraMap_eq_subst_X f
/-
**PowerSeries.coeff_subst_single** 是 Mathlib 中的一个引理，位于命名空间 `PowerSeries`。
形式化陈述：coeff_subst_single {σ : Type*} [DecidableEq σ] (s : σ) (f : R⟦X⟧) (e : σ -
>₀ Nat) : MvPowerSeries.coeff e (subst (MvPowerSeries.X s) f) = if e = Finsupp.s
ingle s (e s) then coeff (e s) f else 0
参数：s : σ；f : R⟦X⟧；e : σ ->₀ Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.coeff_subst`：coeff_subst (ha : HasSubst a) (f : PowerSeries 
R) (e : τ ->₀ Nat) : MvPowerSeries.coeff e (subst a f) = finsum (fun (d : Nat) =
> coeff d f •…
· 使用定理 `PowerSeries.HasSubst.X`：∀ {τ : Type u_3} {S : Type u_4} [inst : CommRing
 S] (t : τ), PowerSeries.HasSubst (MvPowerSeries.X t)
· 使用定理 `finsum_eq_single`：∀ {M : Type u_2} {α : Sort u_4} [inst : AddCommMonoid 
M] (f : α → M) (a : α),   (∀ (x : α), x ≠ a → f x = 0) → ∑ᶠ (x : α), f x = f a
-/
lemma coeff_subst_single {σ : Type*} [DecidableEq σ] (s : σ) (f : R⟦X⟧) (e : σ →₀ ℕ) :
    MvPowerSeries.coeff e (subst (MvPowerSeries.X s) f) =
      if e = Finsupp.single s (e s) then coeff (e s) f else 0 := by
  rw [coeff_subst (HasSubst.X s), finsum_eq_single _ (e s)] <;>
  grind [MvPowerSeries.coeff_X_pow, smul_eq_mul]

@[simp]
/-
**PowerSeries.X_subst** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：X_subst (f : R⟦X⟧) : f.subst (X : R⟦X⟧) = f
参数：f : R⟦X⟧。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PowerSeries.map_algebraMap_eq_subst_X`：map_algebraMap_eq_subst_X (f : R⟦
X⟧) : map (algebraMap R S) f = subst X f
· 使用定理 `Algebra.algebraMap_self`：∀ {R : Type u} [inst : CommSemiring R], algebra
Map R R = RingHom.id R
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `PowerSeries.map_id`：map_id : (map (RingHom.id R) : R⟦X⟧ -> R⟦X⟧) = id
-/
theorem X_subst (f : R⟦X⟧) : f.subst (X : R⟦X⟧) = f := by
  rw [← map_algebraMap_eq_subst_X (S := R), Algebra.algebraMap_self]
  exact congr_fun map_id f
/-
**PowerSeries._root_.Polynomial.toPowerSeries_toMvPowerSeries** 是 Mathlib 中的一个定理
，位于命名空间 `PowerSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Polynomial.toPowerSeries_toMvPowerSeries (p : Polynomial R) : (p : PowerSeries R) =
    ((Polynomial.aeval (MvPolynomial.X ()) p : MvPolynomial Unit R) : MvPowerSeries Unit R) :=
  Polynomial.pUnitAlgEquiv_symm_toPowerSeries
/-
**PowerSeries.substAlgHom_coe** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：substAlgHom_coe (ha : HasSubst a) (p : Polynomial R) : substAlgHom ha (p :
 PowerSeries R) = ↑(Polynomial.aeval a p)
参数：ha : HasSubst a；p : Polynomial R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.toPowerSeries_toMvPowerSeries`：∀ {R : Type u_2} [inst : CommR
ing R] (p : Polynomial R), ↑p = ↑((Polynomial.aeval (MvPolynomial.X ())) p)
· 使用定理 `PowerSeries.HasSubst.const`：∀ {τ : Type u_3} {S : Type u_4} [inst : Comm
Ring S] {a : MvPowerSeries τ S},   PowerSeries.HasSubst a → MvPowerSeries.HasSub
st fun x => a
· 使用定理 `PowerSeries.substAlgHom.eq_1`：∀ {R : Type u_2} [inst : CommRing R] {τ : 
Type u_3} {S : Type u_4} [inst_1 : CommRing S] [inst_2 : Algebra R S]   {a : MvP
owerSeries τ S} (h…
· 使用定理 `MvPowerSeries.coe_substAlgHom`：coe_substAlgHom (ha : HasSubst a) : ⇑(sub
stAlgHom ha) = subst (R
· 使用定理 `MvPowerSeries.subst_coe`：subst_coe (p : MvPolynomial σ R) : subst (R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgHom.comp_apply`：comp_apply (φ₁ : B ->ₐ[R] C) (φ₂ : A ->ₐ[R] B) (p : A
) : φ₁.comp φ₂ p = φ₁ (φ₂ p)
· 使用定理 `AlgHom.congr_fun`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : CommS
emiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra R A] 
[inst_…
· 使用定理 `Polynomial.algHom_ext`：algHom_ext {f g : R[X] ->ₐ[R] B} (hX : f X = g X)
 : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.aeval_X`：aeval_X : aeval x (X : R[X]) = x
· 使用定理 `MvPolynomial.aeval_X`：aeval_X (s : σ) : aeval f (X s : MvPolynomial σ R)
 = f s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem substAlgHom_coe (ha : HasSubst a) (p : Polynomial R) :
    substAlgHom ha (p : PowerSeries R) = ↑(Polynomial.aeval a p) := by
  rw [p.toPowerSeries_toMvPowerSeries, substAlgHom, MvPowerSeries.coe_substAlgHom,
    MvPowerSeries.subst_coe, ← AlgHom.comp_apply]
  apply AlgHom.congr_fun
  apply Polynomial.algHom_ext
  simp
/-
**PowerSeries.substAlgHom_X** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：substAlgHom_X (ha : HasSubst a) : substAlgHom ha (X : R⟦X⟧) = a
参数：ha : HasSubst a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.coe_X`：coe_X : ((X : R[X]) : PowerSeries R) = PowerSeries.X
· 使用定理 `PowerSeries.substAlgHom_coe`：substAlgHom_coe (ha : HasSubst a) (p : Poly
nomial R) : substAlgHom ha (p : PowerSeries R) = ↑(Polynomial.aeval a p)
· 使用定理 `Polynomial.aeval_X`：aeval_X : aeval x (X : R[X]) = x
-/
theorem substAlgHom_X (ha : HasSubst a) :
    substAlgHom ha (X : R⟦X⟧) = a := by
  rw [← Polynomial.coe_X, substAlgHom_coe, Polynomial.aeval_X]
/-
**PowerSeries.subst_coe** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：subst_coe (ha : HasSubst a) (p : Polynomial R) : subst a (p : PowerSeries 
R) = (Polynomial.aeval a p)
参数：ha : HasSubst a；p : Polynomial R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PowerSeries.coe_substAlgHom`：coe_substAlgHom (ha : HasSubst a) : ⇑(subst
AlgHom ha) = subst (R
· 使用定理 `PowerSeries.substAlgHom_coe`：substAlgHom_coe (ha : HasSubst a) (p : Poly
nomial R) : substAlgHom ha (p : PowerSeries R) = ↑(Polynomial.aeval a p)
-/
theorem subst_coe (ha : HasSubst a) (p : Polynomial R) :
    subst a (p : PowerSeries R) = (Polynomial.aeval a p) := by
  rw [← coe_substAlgHom ha, substAlgHom_coe]

@[simp]
/-
**PowerSeries.subst_C** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：subst_C (r : S) : (C r).subst a = MvPowerSeries.C r
参数：r : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.subst_C`：subst_C (r : S) : (C r).subst a = MvPowerSeries.C
 r
-/
theorem subst_C (r : S) : (C r).subst a = MvPowerSeries.C r := MvPowerSeries.subst_C _
/-
**PowerSeries.subst_X** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：subst_X (ha : HasSubst a) : subst a (X : R⟦X⟧) = a
参数：ha : HasSubst a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PowerSeries.coe_substAlgHom`：coe_substAlgHom (ha : HasSubst a) : ⇑(subst
AlgHom ha) = subst (R
· 使用定理 `PowerSeries.substAlgHom_X`：substAlgHom_X (ha : HasSubst a) : substAlgHom
 ha (X : R⟦X⟧) = a
-/
theorem subst_X (ha : HasSubst a) :
    subst a (X : R⟦X⟧) = a := by
  rw [← coe_substAlgHom ha, substAlgHom_X]

omit [Algebra R S] in
/-
**PowerSeries.map_subst** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：map_subst {a : MvPowerSeries τ R} (ha : HasSubst a) {h : R ->+* S} (f : Po
werSeries R) : (f.subst a).map h = (f.map h).subst (a.map h)
参数：ha : HasSubst a；f : PowerSeries R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.map_subst`：map_subst {a : σ -> MvPowerSeries τ R} (ha : Ha
sSubst a) {h : R ->+* S} (f : MvPowerSeries σ R) : (f.subst a).map h = (f.map h)
.subst (fun i…
· 使用定理 `PowerSeries.HasSubst.const`：∀ {τ : Type u_3} {S : Type u_4} [inst : Comm
Ring S] {a : MvPowerSeries τ S},   PowerSeries.HasSubst a → MvPowerSeries.HasSub
st fun x => a
-/
theorem map_subst {a : MvPowerSeries τ R} (ha : HasSubst a) {h : R →+* S} (f : PowerSeries R) :
    (f.subst a).map h = (f.map h).subst (a.map h) :=
  MvPowerSeries.map_subst (HasSubst.const ha) f

section

/-
**PowerSeries.le_weightedOrder_subst** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：le_weightedOrder_subst (w : τ -> Nat) (ha : HasSubst a) (f : PowerSeries R
) : f.order * a.weightedOrder w <= (f.subst a).weightedOrder w
参数：w : τ -> Nat；ha : HasSubst a；f : PowerSeries R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `mul_le_mul_left`：mul_le_mul_left [i : MulRightMono α] {b c : α} (bc : b 
<= c) (a : α) : b * a <= c * a
· 使用定理 `CanonicallyOrderedAdd.toMulLeftMono`：∀ {R : Type u} [inst : NonUnitalNon
AssocSemiring R] [inst_1 : LE R] [CanonicallyOrderedAdd R], MulLeftMono R
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `PowerSeries.order_le`：order_le (n : Nat) (h : coeff n φ != 0) : order φ 
<= n
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finsupp.unique_ext`：unique_ext [Unique α] {f g : α ->₀ M} (h : f default
 = g default) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `Finsupp.sum_fintype`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [in
st : Zero M] [inst_1 : AddCommMonoid N] [inst_2 : Fintype α]   (f : α →₀ M) (g :
 α → M → …
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.univ_unique`：univ_unique [Unique α] : (univ : Finset α) = {defaul
t}
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `MvPowerSeries.le_weightedOrder_subst`：le_weightedOrder_subst (ha : HasSu
bst a) (f : MvPowerSeries σ R) : ⨅ (d : σ ->₀ Nat) (_ : coeff d f != 0), d.weigh
t (weightedOrder w ∘ a) <=…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `PowerSeries.hasSubst_iff`：hasSubst_iff {a : MvPowerSeries τ S} : HasSubs
t a ↔ MvPowerSeries.HasSubst (Function.const Unit a)
-/
theorem le_weightedOrder_subst (w : τ → ℕ) (ha : HasSubst a) (f : PowerSeries R) :
    f.order * a.weightedOrder w ≤ (f.subst a).weightedOrder w := by
  refine .trans ?_ (MvPowerSeries.le_weightedOrder_subst _ (PowerSeries.hasSubst_iff.mp ha) _)
  simp only [ne_eq, Function.comp_const, le_iInf_iff]
  intro i hi
  trans i () * MvPowerSeries.weightedOrder w a
  · exact mul_le_mul_left (f.order_le (i ()) (by delta PowerSeries.coeff; convert! hi; aesop)) _
  · simp [Finsupp.weight_apply, Finsupp.sum_fintype]
/-
**PowerSeries.le_order_subst** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：le_order_subst (a : MvPowerSeries τ S) (ha : HasSubst a) (f : PowerSeries 
R) : a.order * f.order <= (f.subst a).order
参数：a : MvPowerSeries τ S；ha : HasSubst a；f : PowerSeries R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.order_eq_order`：order_eq_order {φ : R⟦X⟧} : φ.order = MvPowe
rSeries.order φ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ciInf_unique`：∀ {α : Type u_1} {ι : Sort u_4} [inst : ConditionallyCompl
etePartialOrderInf α] [inst_1 : Unique ι] {s : ι → α},   ⨅ i, s i = s default
· 使用定理 `MvPowerSeries.le_order_subst`：le_order_subst (ha : HasSubst a) (f : MvPo
werSeries σ R) : (⨅ i, (a i).order) * f.order <= (f.subst a).order
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `PowerSeries.hasSubst_iff`：hasSubst_iff {a : MvPowerSeries τ S} : HasSubs
t a ↔ MvPowerSeries.HasSubst (Function.const Unit a)
-/
theorem le_order_subst (a : MvPowerSeries τ S) (ha : HasSubst a) (f : PowerSeries R) :
    a.order * f.order ≤ (f.subst a).order := by
  refine .trans ?_ (MvPowerSeries.le_order_subst (PowerSeries.hasSubst_iff.mp ha) _)
  simp [order_eq_order]
/-
**PowerSeries.le_order_subst_left** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：le_order_subst_left {f : MvPowerSeries τ R} {φ : PowerSeries R} (hf : f.co
nstantCoeff = 0) : φ.order <= (φ.subst f).order
参数：hf : f.constantCoeff = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `ENat.self_le_mul_left`：self_le_mul_left (a : Nat∞) (hc : c != 0) : a <= 
c * a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MvPowerSeries.order_ne_zero_iff_constCoeff_eq_zero`：order_ne_zero_iff_co
nstCoeff_eq_zero : f.order != 0 ↔ f.constantCoeff = 0
· 使用定理 `PowerSeries.le_order_subst`：le_order_subst (a : MvPowerSeries τ S) (ha :
 HasSubst a) (f : PowerSeries R) : a.order * f.order <= (f.subst a).order
· 使用定理 `PowerSeries.HasSubst.of_constantCoeff_zero`：∀ {τ : Type u_3} {S : Type u
_4} [inst : CommRing S] {a : MvPowerSeries τ S},   MvPowerSeries.constantCoeff a
 = 0 → PowerSeries.HasSubst a
-/
theorem le_order_subst_left {f : MvPowerSeries τ R} {φ : PowerSeries R}
    (hf : f.constantCoeff = 0) : φ.order ≤ (φ.subst f).order :=
  .trans (ENat.self_le_mul_left φ.order (f.order_ne_zero_iff_constCoeff_eq_zero.mpr hf))
    (PowerSeries.le_order_subst f (HasSubst.of_constantCoeff_zero hf) _)
/-
**PowerSeries.le_order_subst_right** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：le_order_subst_right {f : MvPowerSeries τ R} {φ : PowerSeries R} (hf : f.c
onstantCoeff = 0) (hφ : φ.constantCoeff = 0) : f.order <= (φ.subst f).order
参数：hf : f.constantCoeff = 0；hφ : φ.constantCoeff = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `ENat.self_le_mul_right`：self_le_mul_right (a : Nat∞) (hc : c != 0) : a <
= a * c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `PowerSeries.order_ne_zero_iff_constCoeff_eq_zero`：order_ne_zero_iff_cons
tCoeff_eq_zero {φ : R⟦X⟧} : φ.order != 0 ↔ φ.constantCoeff = 0
· 使用定理 `PowerSeries.le_order_subst`：le_order_subst (a : MvPowerSeries τ S) (ha :
 HasSubst a) (f : PowerSeries R) : a.order * f.order <= (f.subst a).order
· 使用定理 `PowerSeries.HasSubst.of_constantCoeff_zero`：∀ {τ : Type u_3} {S : Type u
_4} [inst : CommRing S] {a : MvPowerSeries τ S},   MvPowerSeries.constantCoeff a
 = 0 → PowerSeries.HasSubst a
-/
theorem le_order_subst_right {f : MvPowerSeries τ R} {φ : PowerSeries R}
    (hf : f.constantCoeff = 0) (hφ : φ.constantCoeff = 0) : f.order ≤ (φ.subst f).order :=
  .trans (ENat.self_le_mul_right _ (order_ne_zero_iff_constCoeff_eq_zero.mpr hφ))
    (PowerSeries.le_order_subst f (HasSubst.of_constantCoeff_zero hf) _)
/-
**PowerSeries.le_order_subst_left'** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：le_order_subst_left' {f φ : PowerSeries R} (hf : f.constantCoeff = 0) : φ.
order <= PowerSeries.order (φ.subst f)
参数：hf : f.constantCoeff = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.order_eq_order`：order_eq_order {φ : R⟦X⟧} : φ.order = MvPowe
rSeries.order φ
· 使用定理 `PowerSeries.le_order_subst_left`：le_order_subst_left {f : MvPowerSeries 
τ R} {φ : PowerSeries R} (hf : f.constantCoeff = 0) : φ.order <= (φ.subst f).ord
er
-/
theorem le_order_subst_left' {f φ : PowerSeries R} (hf : f.constantCoeff = 0) :
    φ.order ≤ PowerSeries.order (φ.subst f) := by
  conv_rhs => rw [order_eq_order]
  exact le_order_subst_left hf
/-
**PowerSeries.le_order_subst_right'** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：le_order_subst_right' {f φ : PowerSeries R} (hf : f.constantCoeff = 0) (hφ
 : φ.constantCoeff = 0) : f.order <= PowerSeries.order (φ.subst f)
参数：hf : f.constantCoeff = 0；hφ : φ.constantCoeff = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.order_eq_order`：order_eq_order {φ : R⟦X⟧} : φ.order = MvPowe
rSeries.order φ
· 使用定理 `PowerSeries.le_order_subst_right`：le_order_subst_right {f : MvPowerSerie
s τ R} {φ : PowerSeries R} (hf : f.constantCoeff = 0) (hφ : φ.constantCoeff = 0)
 : f.order <= (φ.subst…
-/
theorem le_order_subst_right' {f φ : PowerSeries R} (hf : f.constantCoeff = 0)
    (hφ : φ.constantCoeff = 0) : f.order ≤ PowerSeries.order (φ.subst f) := by
  simp_rw [order_eq_order]
  exact le_order_subst_right hf hφ

end

/-
**PowerSeries.HasSubst.comp** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries.HasSubst`。
形式化陈述：∀ {S : Type u_4} [inst : CommRing S] {υ : Type u_5} {T : Type u_6} [inst_1
 : CommRing T] [inst_2 : Algebra S T]   {a : PowerSeries S},   PowerSeries.HasSu
bst a →     ∀ {b : MvPowerSeries υ T} (hb : PowerSeries.HasSubst b), PowerSeries
.HasSubst ((PowerSeries.substAlgHom hb) a)
参数：hb : PowerSeries.HasSubst b；(PowerSeries.substAlgHom hb) a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.IsNilpotent_substAlgHom`：IsNilpotent_substAlgHom (ha : Has
Subst a) {f : MvPowerSeries σ R} (hf : IsNilpotent (constantCoeff f)) : IsNilpot
ent (constantCoeff (substAl…
· 使用定理 `PowerSeries.HasSubst.const`：∀ {τ : Type u_3} {S : Type u_4} [inst : Comm
Ring S] {a : MvPowerSeries τ S},   PowerSeries.HasSubst a → MvPowerSeries.HasSub
st fun x => a
-/
theorem HasSubst.comp
    {a : PowerSeries S} (ha : HasSubst a) {b : MvPowerSeries υ T} (hb : HasSubst b) :
    HasSubst (substAlgHom hb a) :=
  MvPowerSeries.IsNilpotent_substAlgHom hb.const ha

variable {a : PowerSeries S} {b : MvPowerSeries υ T} {a' : MvPowerSeries τ S}
  {b' : τ → MvPowerSeries υ T} [IsScalarTower R S T]
/-
**PowerSeries.substAlgHom_comp_substAlgHom** 是 Mathlib 中的一个定理，位于命名空间 `PowerSerie
s`。
形式化陈述：substAlgHom_comp_substAlgHom (ha : HasSubst a) (hb : HasSubst b) : ((subst
AlgHom hb).restrictScalars R).comp (substAlgHom ha) = substAlgHom (ha.comp hb)
参数：ha : HasSubst a；hb : HasSubst b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.substAlgHom_comp_substAlgHom`：substAlgHom_comp_substAlgHom
 (ha : HasSubst a) (hb : HasSubst b) : ((substAlgHom hb).restrictScalars R).comp
 (substAlgHom ha) = substAlgHom …
· 使用定理 `PowerSeries.HasSubst.const`：∀ {τ : Type u_3} {S : Type u_4} [inst : Comm
Ring S] {a : MvPowerSeries τ S},   PowerSeries.HasSubst a → MvPowerSeries.HasSub
st fun x => a
-/
theorem substAlgHom_comp_substAlgHom (ha : HasSubst a) (hb : HasSubst b) :
    ((substAlgHom hb).restrictScalars R).comp (substAlgHom ha) = substAlgHom (ha.comp hb) :=
  MvPowerSeries.substAlgHom_comp_substAlgHom _ _
/-
**PowerSeries.substAlgHom_comp_substAlgHom_apply** 是 Mathlib 中的一个定理，位于命名空间 `Powe
rSeries`。
形式化陈述：substAlgHom_comp_substAlgHom_apply (ha : HasSubst a) (hb : HasSubst b) (f 
: PowerSeries R) : (substAlgHom hb) (substAlgHom ha f) = substAlgHom (ha.comp hb
) f
参数：ha : HasSubst a；hb : HasSubst b；f : PowerSeries R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用定理 `MvPowerSeries.instIsScalarTower`：∀ {σ : Type u_1} {R : Type u_2} {A : Ty
pe u_3} {S : Type u_4} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : Add
CommMonoid A] [inst_3…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `PowerSeries.HasSubst.comp`：∀ {S : Type u_4} [inst : CommRing S] {υ : Typ
e u_5} {T : Type u_6} [inst_1 : CommRing T] [inst_2 : Algebra S T]   {a : PowerS
eries S},   Pow…
· 使用定理 `PowerSeries.substAlgHom_comp_substAlgHom`：substAlgHom_comp_substAlgHom (
ha : HasSubst a) (hb : HasSubst b) : ((substAlgHom hb).restrictScalars R).comp (
substAlgHom ha) = substAlgHom …
-/
theorem substAlgHom_comp_substAlgHom_apply (ha : HasSubst a) (hb : HasSubst b) (f : PowerSeries R) :
    (substAlgHom hb) (substAlgHom ha f) = substAlgHom (ha.comp hb) f :=
  DFunLike.congr_fun (substAlgHom_comp_substAlgHom ha hb) f
/-
**PowerSeries.subst_comp_subst** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：subst_comp_subst (ha : HasSubst a) (hb : HasSubst b) : (subst b) ∘ (subst 
a) = subst (R
参数：ha : HasSubst a；hb : HasSubst b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.instIsScalarTower`：∀ {σ : Type u_1} {R : Type u_2} {A : Ty
pe u_3} {S : Type u_4} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : Add
CommMonoid A] [inst_3…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `PowerSeries.HasSubst.comp`：∀ {S : Type u_4} [inst : CommRing S] {υ : Typ
e u_5} {T : Type u_6} [inst_1 : CommRing T] [inst_2 : Algebra S T]   {a : PowerS
eries S},   Pow…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `PowerSeries.coe_substAlgHom`：coe_substAlgHom (ha : HasSubst a) : ⇑(subst
AlgHom ha) = subst (R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.substAlgHom.congr_simp`：∀ {R : Type u_2} [inst : CommRing R]
 {τ : Type u_3} {S : Type u_4} [inst_1 : CommRing S] [inst_2 : Algebra R S]   {a
 a_1 : MvPowerSeries τ S…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `PowerSeries.substAlgHom_comp_substAlgHom`：substAlgHom_comp_substAlgHom (
ha : HasSubst a) (hb : HasSubst b) : ((substAlgHom hb).restrictScalars R).comp (
substAlgHom ha) = substAlgHom …
-/
theorem subst_comp_subst (ha : HasSubst a) (hb : HasSubst b) :
    (subst b) ∘ (subst a) = subst (R := R) (subst b a) := by
  simpa [funext_iff, DFunLike.ext_iff, coe_substAlgHom] using substAlgHom_comp_substAlgHom ha hb
/-
**PowerSeries.subst_comp_subst_apply** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：subst_comp_subst_apply (ha : HasSubst a) (hb : HasSubst b) (f : PowerSerie
s R) : subst b (subst a f) = subst (subst b a) f
参数：ha : HasSubst a；hb : HasSubst b；f : PowerSeries R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `PowerSeries.subst_comp_subst`：subst_comp_subst (ha : HasSubst a) (hb : H
asSubst b) : (subst b) ∘ (subst a) = subst (R
-/
theorem subst_comp_subst_apply (ha : HasSubst a) (hb : HasSubst b) (f : PowerSeries R) :
    subst b (subst a f) = subst (subst b a) f :=
  congr_fun (subst_comp_subst ha hb) f
/-
**PowerSeries.rescale_eq** 是 Mathlib 中的一个引理，位于命名空间 `PowerSeries`。
形式化陈述：rescale_eq (r : R) (f : PowerSeries R) : rescale r f = MvPowerSeries.resca
le (fun _ => r) f
参数：r : R；f : PowerSeries R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.ext`：ext {φ ψ : R⟦X⟧} (h : forall n, coeff n φ = coeff n ψ) 
: φ = ψ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.coeff_rescale`：coeff_rescale (f : R⟦X⟧) (a : R) (n : Nat) : 
coeff n (rescale a f) = a ^ n * coeff n f
· 使用定理 `PowerSeries.coeff.eq_1`：∀ {R : Type u_1} [inst : Semiring R] (n : ℕ), Po
werSeries.coeff n = MvPowerSeries.coeff fun₀ | () => n
· 使用定理 `MvPowerSeries.coeff_rescale`：coeff_rescale (f : MvPowerSeries σ R) (a : 
σ -> R) (n : σ ->₀ Nat) : coeff n (rescale a f) = (n.prod fun s m => a s ^ m) * 
f.coeff n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finsupp.prod_single_index`：prod_single_index {a : α} {b : M} {h : α -> M
 -> N} (h_zero : h a 0 = 1) : (single a b).prod h = h a b
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma rescale_eq (r : R) (f : PowerSeries R) :
    rescale r f = MvPowerSeries.rescale (fun _ ↦ r) f := by
  ext n
  rw [coeff_rescale, coeff, MvPowerSeries.coeff_rescale]
  simp [pow_zero, Finsupp.prod_single_index]

@[deprecated (since := "2026-02-27")] alias _root_.MvPowerSeries.rescaleUnit := rescale_eq
/-
**PowerSeries.rescale_eq_subst** 是 Mathlib 中的一个引理，位于命名空间 `PowerSeries`。
形式化陈述：rescale_eq_subst (r : R) (f : PowerSeries R) : PowerSeries.rescale r f = P
owerSeries.subst (r • X : R⟦X⟧) f
参数：r : R；f : PowerSeries R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `PowerSeries.rescale_eq`：rescale_eq (r : R) (f : PowerSeries R) : rescale
 r f = MvPowerSeries.rescale (fun _ => r) f
· 使用定理 `MvPowerSeries.rescale_eq_subst`：rescale_eq_subst (a : σ -> R) (f : MvPow
erSeries σ R) : rescale a f = subst (a • X) f
· 使用定理 `PowerSeries.X.eq_1`：∀ {R : Type u_1} [inst : Semiring R], PowerSeries.X 
= MvPowerSeries.X ()
· 使用定理 `PowerSeries.subst.eq_1`：∀ {R : Type u_2} [inst : CommRing R] {τ : Type u
_3} {S : Type u_4} [inst_1 : CommRing S] [inst_2 : Algebra R S]   (a : MvPowerSe
ries τ S) (f…
· 使用引理 `Pi.smul_def'`：smul_def' [forall i, SMul (α i) (β i)] (s : forall i, α i)
 (x : forall i, β i) : s • x = fun i => s i • x i
-/
lemma rescale_eq_subst (r : R) (f : PowerSeries R) :
    PowerSeries.rescale r f = PowerSeries.subst (r • X : R⟦X⟧) f := by
  rw [rescale_eq, MvPowerSeries.rescale_eq_subst, X, subst, Pi.smul_def']

/-- Rescale power series, as an `AlgHom` -/
/-
**PowerSeries.rescaleAlgHom** 是 Mathlib 中的一个缩写定义，位于命名空间 `PowerSeries`。
形式化陈述：rescaleAlgHom (r : R) : R⟦X⟧ ->ₐ[R] R⟦X⟧
参数：r : R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Rescale power series, as an `AlgHom`
-/
noncomputable abbrev rescaleAlgHom (r : R) : R⟦X⟧ →ₐ[R] R⟦X⟧ :=
  MvPowerSeries.rescaleAlgHom (fun _ ↦ r)
/-
**PowerSeries.coe_rescaleAlgHom** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries`。
形式化陈述：coe_rescaleAlgHom (r : R) : rescaleAlgHom r = rescale r
参数：r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `PowerSeries.ext`：ext {φ ψ : R⟦X⟧} (h : forall n, coeff n φ = coeff n ψ) 
: φ = ψ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `PowerSeries.rescale_eq`：rescale_eq (r : R) (f : PowerSeries R) : rescale
 r f = MvPowerSeries.rescale (fun _ => r) f
· 使用定理 `RingHom.coe_coe`：coe_coe {F : Type*} [FunLike F α β] [RingHomClass F α β
] (f : F) : ((f : α ->+* β) : α -> β) = f
· 使用定理 `MvPowerSeries.rescaleAlgHom_apply`：rescaleAlgHom_apply (a : σ -> R) (f :
 MvPowerSeries σ R) : rescaleAlgHom a f = rescale a f
-/
theorem coe_rescaleAlgHom (r : R) : rescaleAlgHom r = rescale r := by
  ext f
  rw [rescale_eq, RingHom.coe_coe, MvPowerSeries.rescaleAlgHom_apply]

/-- Substitution by `p` commutes with scalar homothety. -/
/-
**PowerSeries.subst_rescale_of_degree_eq_one** 是 Mathlib 中的一个引理，位于命名空间 `PowerSer
ies`。
形式化陈述：subst_rescale_of_degree_eq_one (a : R) {σ : Type*} (p : MvPowerSeries σ R)
 (hp_lin : forall d in Function.support p, d.degree = 1) (f : PowerSeries R) : s
ubst p (rescale a f) = MvPowerSeries.rescale (Function.const σ a) (subst p f)
参数：a : R；p : MvPowerSeries σ R；hp_lin : forall d in Function.support p, d.degree
 = 1；f : PowerSeries R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.HasSubst.of_constantCoeff_zero`：∀ {τ : Type u_3} {S : Type u
_4} [inst : CommRing S] {a : MvPowerSeries τ S},   MvPowerSeries.constantCoeff a
 = 0 → PowerSeries.HasSubst a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPowerSeries.coeff_zero_eq_constantCoeff_apply`：coeff_zero_eq_constantC
oeff_apply (φ : MvPowerSeries σ R) : coeff (0 : σ ->₀ Nat) φ = constantCoeff φ
· 使用定理 `MvPowerSeries.coeff_apply`：coeff_apply (f : MvPowerSeries σ R) (d : σ ->
₀ Nat) : coeff d f = f d
· 使用引理 `PowerSeries.rescale_eq_subst`：rescale_eq_subst (r : R) (f : PowerSeries 
R) : PowerSeries.rescale r f = PowerSeries.subst (r • X : R⟦X⟧) f
· 使用定理 `MvPowerSeries.rescale_eq_subst`：rescale_eq_subst (a : σ -> R) (f : MvPow
erSeries σ R) : rescale a f = subst (a • X) f
· 使用定理 `PowerSeries.subst_comp_subst_apply`：subst_comp_subst_apply (ha : HasSubs
t a) (hb : HasSubst b) (f : PowerSeries R) : subst b (subst a f) = subst (subst 
b a) f
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `PowerSeries.HasSubst.smul_X'`：∀ {A : Type u_1} [inst : CommRing A] {R : 
Type u_2} [inst_1 : CommRing R] [inst_2 : Algebra A R] (a : A),   PowerSeries.Ha
sSubst (a • PowerS…
· 使用定理 `PowerSeries.subst.eq_1`：∀ {R : Type u_2} [inst : CommRing R] {τ : Type u
_3} {S : Type u_4} [inst_1 : CommRing S] [inst_2 : Algebra R S]   (a : MvPowerSe
ries τ S) (f…
· 使用定理 `MvPowerSeries.subst_comp_subst_apply`：subst_comp_subst_apply (ha : HasSu
bst a) (hb : HasSubst b) (f : MvPowerSeries σ R) : subst b (subst a f) = subst (
fun s => subst b (a s)) f
· 使用定理 `PowerSeries.HasSubst.const`：∀ {τ : Type u_3} {S : Type u_4} [inst : Comm
Ring S] {a : MvPowerSeries τ S},   PowerSeries.HasSubst a → MvPowerSeries.HasSub
st fun x => a
· 使用定理 `MvPowerSeries.HasSubst.smul_X`：∀ {σ : Type u_1} {R : Type u_3} [inst : C
ommRing R] (a : σ → R), MvPowerSeries.HasSubst (a • MvPowerSeries.X)
· 使用定理 `MvPowerSeries.ext_iff`：∀ {σ : Type u_1} {R : Type u_2} [inst : Semiring 
R] {φ ψ : MvPowerSeries σ R},   φ = ψ ↔ ∀ (n : σ →₀ ℕ), (MvPowerSeries.coeff n) 
φ = (MvPowe…
· 使用定理 `PowerSeries.subst_smul`：subst_smul [Algebra A S] [IsScalarTower A R S] (
ha : HasSubst a) (r : A) (f : PowerSeries R) : subst a (r • f) = r • (subst a f)
· 使用定理 `Polynomial.coe_X`：coe_X : ((X : R[X]) : PowerSeries R) = PowerSeries.X
· 使用定理 `PowerSeries.subst_coe`：subst_coe (ha : HasSubst a) (p : Polynomial R) : 
subst a (p : PowerSeries R) = (Polynomial.aeval a p)
· 使用定理 `Polynomial.aeval_X`：aeval_X : aeval x (X : R[X]) = x
· 使用引理 `MvPowerSeries.rescale_homogeneous_eq_smul`：rescale_homogeneous_eq_smul {
n : Nat} {r : R} {f : MvPowerSeries σ R} (hf : forall d in f.support, d.degree =
 n) : MvPowerSeries.rescale (Fu…
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a

--- 原说明 ---
Substitution by `p` commutes with scalar homothety.
-/
lemma subst_rescale_of_degree_eq_one (a : R) {σ : Type*} (p : MvPowerSeries σ R)
    (hp_lin : ∀ d ∈ Function.support p, d.degree = 1) (f : PowerSeries R) :
    subst p (rescale a f) = MvPowerSeries.rescale (Function.const σ a) (subst p f) := by
  have hp : PowerSeries.HasSubst p := by
    apply HasSubst.of_constantCoeff_zero
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_apply]
    have : (p 0 ≠ 0) → (0 : σ →₀ ℕ).degree = 1 := hp_lin 0
    grind
  rw [rescale_eq_subst, MvPowerSeries.rescale_eq_subst,
    subst_comp_subst_apply (HasSubst.smul_X' a) hp]
  nth_rewrite 3 [subst]
  rw [MvPowerSeries.subst_comp_subst_apply hp.const (MvPowerSeries.HasSubst.smul_X _),
    MvPowerSeries.ext_iff]
  intro _
  rw [subst_smul hp, ← Polynomial.coe_X, subst_coe hp, Polynomial.aeval_X,
    ← MvPowerSeries.rescale_eq_subst, MvPowerSeries.rescale_homogeneous_eq_smul hp_lin,
    subst, pow_one]

section substInv

section Invertible

variable (P : R⟦X⟧) (hP : P.constantCoeff = 0) [Invertible (coeff 1 P)]

open PowerSeries

/-- Given a power series `P = u • X + O(X²)` with `u` invertible,
this is the construction of a power series `Q` such that `P(Q(X)) = X`. -/
noncomputable
/-
**PowerSeries.substInvFun** 是 Mathlib 中的一个定义，位于命名空间 `PowerSeries`。
形式化陈述：{R : Type u_2} → [inst : CommRing R] → (P : PowerSeries R) → [Invertible (
(PowerSeries.coeff 1) P)] → ℕ → R
参数：P : PowerSeries R；(PowerSeries.coeff 1) P。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def substInvFun : ℕ → R
  | 0 => 0
  | 1 => ⅟(P.coeff 1)
  | n + 1 => - ⅟(P.coeff 1) *
      (coeff (n + 1) (P.subst (∑ i : Fin (n + 1), C (substInvFun i.1) * X ^ i.1)))

/-- Given a power series `P = u • X + O(X²)` with `u` invertible,
this is the power series `Q` such that `P(Q(X)) = X`. See `PowerSeries.subst_substInv_right`.

See also `PowerSeries.substInvOfIsUnit` for a variant using `IsUnit`. -/
noncomputable
/-
**PowerSeries.substInv** 是 Mathlib 中的一个定义，位于命名空间 `PowerSeries`。
形式化陈述：substInv : PowerSeries R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def substInv : PowerSeries R := .mk (substInvFun P)

include hP in
/-
**PowerSeries.coeff_subst_sum_C_substInvFun_mul_X_pow_sub_X** 是 Mathlib 中的一个引理，位
于命名空间 `PowerSeries`。
形式化陈述：coeff_subst_sum_C_substInvFun_mul_X_pow_sub_X (n : Nat) : coeff n (P.subst
 (∑ i : Fin (n + 1), C (substInvFun P i.1) * X ^ i.1) - X) = 0
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `PowerSeries.coeff_subst'`：coeff_subst' {b : S⟦X⟧} (hb : HasSubst b) (f :
 R⟦X⟧) (e : Nat) : coeff e (f.subst b) = finsum (fun (d : Nat) => coeff d f • Po
werSeries.coef…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.univ_unique`：univ_unique [Unique α] : (univ : Finset α) = {defaul
t}
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Fin.val_eq_zero`：∀ (a : Fin 1), ↑a = 0
· 使用定理 `PowerSeries.substInvFun.eq_1`：∀ {R : Type u_2} [inst : CommRing R] (P : 
PowerSeries R) [inst_1 : Invertible ((PowerSeries.coeff 1) P)],   P.substInvFun 
0 = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `zero_pow_eq`：zero_pow_eq (n : Nat) : (0 : M₀) ^ n = if n = 0 then 1 else
 0
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `PowerSeries.coeff_zero_eq_constantCoeff`：coeff_zero_eq_constantCoeff : ⇑
(coeff (R
· 使用定理 `MonoidWithZeroHom.map_ite_one_zero`：map_ite_one_zero {F : Type*} [FunLik
e F α β] [MonoidWithZeroHomClass F α β] (f : F) (p : Prop) [Decidable p] : f (it
e p 1 0) = ite p 1 0
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
· 使用定理 `finsum_eq_single`：∀ {M : Type u_2} {α : Sort u_4} [inst : AddCommMonoid 
M] (f : α → M) (a : α),   (∀ (x : α), x ≠ a → f x = 0) → ∑ᶠ (x : α), f x = f a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
（共 128 条，此处仅展示前 30 条）
-/
lemma coeff_subst_sum_C_substInvFun_mul_X_pow_sub_X (n : ℕ) :
    coeff n (P.subst (∑ i : Fin (n + 1), C (substInvFun P i.1) * X ^ i.1) - X) = 0 := by
  obtain (_ | _ | n) := n
  · rw [map_sub, coeff_subst']
    · simp +contextual [finsum_eq_single (a := 0), substInvFun, zero_pow_eq, hP]
    · simp [substInvFun, HasSubst]
  · rw [map_sub, coeff_subst']
    · rw [finsum_eq_single (a := 1)]
      · simp [substInvFun]
      · rintro (_ | _ | _) _ <;> simp_all [substInvFun, mul_pow, coeff_mul_X_pow']
    · simp [HasSubst, X, substInvFun]
  · rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, map_sub, substInvFun]
    generalize hB : ∑ i : Fin (n + 2), C (substInvFun P i) * X ^ i.1 = B
    have hB' : B.constantCoeff = 0 := by simp [← hB, zero_pow_eq, substInvFun]
    simp only [neg_mul, map_neg, map_mul, coeff_X, Nat.add_eq_right, Nat.add_eq_zero_iff,
      one_ne_zero, and_false, ↓reduceIte, sub_zero]
    rw [coeff_subst']
    · simp only [smul_eq_mul, ← map_mul]
      generalize hk : ⅟(P.coeff 1) * coeff (n + 1 + 1) (subst B P) = k
      trans ∑ᶠ d, P.coeff d * (coeff (n + 1 + 1) (B ^ d) - if d = 1 then k else 0)
      · refine finsum_congr fun i ↦ ?_
        · congr 1
          obtain (_ | _ | i) := i
          · simp
          · simp [← sub_eq_add_neg]
          · simp only [add_assoc, Nat.reduceAdd]
            rw [add_comm B, add_pow, map_sum, Finset.sum_eq_single (a := 0)]
            · simp
            · rintro (_ | _ | j) hj hj'
              · simp at hj'
              · simp [mul_comm (C k), hB', mul_assoc, coeff_X_pow_mul']
              · rw [← neg_mul, mul_pow, ← pow_mul, mul_comm (_ ^ _)]
                simp [mul_assoc, coeff_X_pow_mul']
            · simp
      · simp_rw [mul_sub]
        rw [finsum_sub_distrib]
        · simp only [mul_ite, mul_zero]
          nth_rw 2 [finsum_eq_single (a := 1)]
          · simp only [↓reduceIte, ← hk, mul_invOf_cancel_left', sub_eq_zero]
            rw [coeff_subst']
            · rfl
            · simp [HasSubst, ← PowerSeries.constantCoeff.eq_def, hB']
          · simp +contextual
        · refine .subset (Set.finite_Iio (n + 3)) fun i ↦ ?_
          obtain ⟨B, rfl⟩ : X ∣ B := by rwa [X_dvd_iff]
          simp +contextual [mul_pow, coeff_X_pow_mul', Nat.lt_succ_iff]
        · exact .subset (Set.finite_singleton 1) (fun _ ↦ by simp +contextual)
    · simp [HasSubst, ← PowerSeries.constantCoeff.eq_def, hB']

include hP in
/-
**PowerSeries.subst_substInv_right** 是 Mathlib 中的一个引理，位于命名空间 `PowerSeries`。
形式化陈述：subst_substInv_right : P.subst (substInv P) = X
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.ext`：ext {φ ψ : R⟦X⟧} (h : forall n, coeff n φ = coeff n ψ) 
: φ = ψ
· 使用引理 `PowerSeries.coeff_subst_sum_C_substInvFun_mul_X_pow_sub_X`：coeff_subst_s
um_C_substInvFun_mul_X_pow_sub_X (n : Nat) : coeff n (P.subst (∑ i : Fin (n + 1)
, C (substInvFun P i.1) * X ^ i.1) - X) = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `PowerSeries.coeff_subst'`：coeff_subst' {b : S⟦X⟧} (hb : HasSubst b) (f :
 R⟦X⟧) (e : Nat) : coeff e (f.subst b) = finsum (fun (d : Nat) => coeff d f • Po
werSeries.coef…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `PowerSeries.substInvFun.eq_1`：∀ {R : Type u_2} [inst : CommRing R] (P : 
PowerSeries R) [inst_1 : Invertible ((PowerSeries.coeff 1) P)],   P.substInvFun 
0 = 0
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `MvPowerSeries.constantCoeff_X`：constantCoeff_X (s : σ) : constantCoeff (
R
· 使用引理 `zero_pow_eq`：zero_pow_eq (n : Nat) : (0 : M₀) ^ n = if n = 0 then 1 else
 0
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
（共 63 条，此处仅展示前 30 条）
-/
lemma subst_substInv_right :
    P.subst (substInv P) = X := by
  ext n
  have := coeff_subst_sum_C_substInvFun_mul_X_pow_sub_X P hP n
  rw [map_sub, sub_eq_zero] at this
  rw [← this, coeff_subst', coeff_subst']
  · congr! 3 with m
    generalize hB : (∑ i : Fin (n + 1), C (substInvFun P ↑i) * X ^ i.1) = B
    have : X ^ (n + 1) ∣ mk (substInvFun P) - B := by
      rw [X_pow_dvd_iff]
      intro m hm
      simp +contextual [← hB, coeff_X_pow, Finset.sum_eq_single (⟨m, hm⟩ : Fin (n + 1)),
        Fin.ext_iff, @eq_comm _ m]
    obtain ⟨Q, hQ⟩ := this.trans (sub_dvd_pow_sub_pow _ _ m)
    simp [substInv, sub_eq_iff_eq_add.mp hQ, coeff_X_pow_mul']
  · simp [HasSubst, X, zero_pow_eq, C, substInvFun]
  · simp [HasSubst, ← constantCoeff.eq_def, substInvFun, substInv]

@[simp]
/-
**PowerSeries.constantCoeff_substInv** 是 Mathlib 中的一个引理，位于命名空间 `PowerSeries`。
形式化陈述：constantCoeff_substInv : P.substInv.constantCoeff = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.substInvFun.eq_1`：∀ {R : Type u_2} [inst : CommRing R] (P : 
PowerSeries R) [inst_1 : Invertible ((PowerSeries.coeff 1) P)],   P.substInvFun 
0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma constantCoeff_substInv : P.substInv.constantCoeff = 0 := by
  simp [substInv, substInvFun]
/-
**PowerSeries.HasSubst.substInv** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries.HasSubst`
。
形式化陈述：∀ {R : Type u_2} [inst : CommRing R] (P : PowerSeries R) [inst_1 : Inverti
ble ((PowerSeries.coeff 1) P)],   PowerSeries.HasSubst P.substInv
参数：P : PowerSeries R；(PowerSeries.coeff 1) P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `PowerSeries.constantCoeff_substInv`：constantCoeff_substInv : P.substInv.
constantCoeff = 0
-/
lemma HasSubst.substInv : HasSubst P.substInv := by simp [HasSubst, ← constantCoeff.eq_def]

@[deprecated (since := "2026-04-27")]
alias hasSubst_substInv := HasSubst.substInv

@[simp]
/-
**PowerSeries.coeff_one_substInv** 是 Mathlib 中的一个引理，位于命名空间 `PowerSeries`。
形式化陈述：coeff_one_substInv : P.substInv.coeff 1 = ⅟(P.coeff 1)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.coeff_mk`：coeff_mk (n : Nat) (f : Nat -> R) : coeff n (mk f)
 = f n
· 使用定理 `PowerSeries.substInvFun.eq_2`：∀ {R : Type u_2} [inst : CommRing R] (P : 
PowerSeries R) [inst_1 : Invertible ((PowerSeries.coeff 1) P)],   P.substInvFun 
1 = ⅟((PowerSeries…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma coeff_one_substInv : P.substInv.coeff 1 = ⅟(P.coeff 1) := by
  simp [substInv, substInvFun]

include hP in
/-
**PowerSeries.subst_substInv_left** 是 Mathlib 中的一个引理，位于命名空间 `PowerSeries`。
形式化陈述：subst_substInv_left : P.substInv.subst P = X
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `PowerSeries.coeff_one_substInv`：coeff_one_substInv : P.substInv.coeff 1 
= ⅟(P.coeff 1)
· 使用定理 `PowerSeries.HasSubst.substInv`：∀ {R : Type u_2} [inst : CommRing R] (P :
 PowerSeries R) [inst_1 : Invertible ((PowerSeries.coeff 1) P)],   PowerSeries.H
asSubst P.substInv
· 使用引理 `PowerSeries.subst_substInv_right`：subst_substInv_right : P.subst (substI
nv P) = X
· 使用引理 `PowerSeries.constantCoeff_substInv`：constantCoeff_substInv : P.substInv.
constantCoeff = 0
· 使用定理 `PowerSeries.subst_X`：subst_X (ha : HasSubst a) : subst a (X : R⟦X⟧) = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `PowerSeries.subst_comp_subst_apply`：subst_comp_subst_apply (ha : HasSubs
t a) (hb : HasSubst b) (f : PowerSeries R) : subst b (subst a f) = subst (subst 
b a) f
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `PowerSeries.X_subst`：X_subst (f : R⟦X⟧) : f.subst (X : R⟦X⟧) = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma subst_substInv_left : P.substInv.subst P = X := by
  have : Invertible (P.substInv.coeff 1) := by simpa using invertibleInvOf
  let Q := P.substInv.substInv
  have hQ : HasSubst Q := HasSubst.substInv P.substInv
  have eq_aux : P.substInv.subst Q = X := subst_substInv_right P.substInv P.constantCoeff_substInv
  suffices h : Q = P from by simp_rw [← h, eq_aux]
  calc
    _ = PowerSeries.subst Q (P.subst P.substInv) := by
      rw [subst_substInv_right _ hP, subst_X hQ]
    _ = P := by
      simp [subst_comp_subst_apply (HasSubst.substInv P) hQ, eq_aux]

end Invertible

section IsUnit

variable (P : R⟦X⟧) (hP : P.constantCoeff = 0) (hP' : IsUnit (P.coeff 1))

/-- Given a power series `P = u • X + O(X²)` with `u` is an unit in ring `R`,
this is the power series `Q` such that `P(Q(X)) = X`.
See `PowerSeries.subst_substInvOfIsUnit_right`.

See also `PowerSeries.substInv` for a variant using `Invertible`. -/
noncomputable
/-
**PowerSeries.substInvOfIsUnit** 是 Mathlib 中的一个定义，位于命名空间 `PowerSeries`。
形式化陈述：substInvOfIsUnit : PowerSeries R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def substInvOfIsUnit : PowerSeries R :=
  letI := hP'.invertible
  substInv P
/-
**PowerSeries.substInvOfIsUnit_eq_substInv** 是 Mathlib 中的一个引理，位于命名空间 `PowerSerie
s`。
形式化陈述：substInvOfIsUnit_eq_substInv : letI
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma substInvOfIsUnit_eq_substInv :
    letI := hP'.invertible
    P.substInvOfIsUnit hP' = P.substInv := rfl

@[simp]
/-
**PowerSeries.constantCoeff_substInvOfIsUnit** 是 Mathlib 中的一个引理，位于命名空间 `PowerSer
ies`。
形式化陈述：constantCoeff_substInvOfIsUnit : (P.substInvOfIsUnit hP').constantCoeff = 
0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `PowerSeries.constantCoeff_substInv`：constantCoeff_substInv : P.substInv.
constantCoeff = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma constantCoeff_substInvOfIsUnit : (P.substInvOfIsUnit hP').constantCoeff = 0 := by
  simp [substInvOfIsUnit_eq_substInv]
/-
**PowerSeries.HasSubst.substInvOfIsUnit** 是 Mathlib 中的一个定理，位于命名空间 `PowerSeries.H
asSubst`。
形式化陈述：∀ {R : Type u_2} [inst : CommRing R] (P : PowerSeries R) (hP' : IsUnit ((P
owerSeries.coeff 1) P)),   PowerSeries.HasSubst (P.substInvOfIsUnit hP')
参数：P : PowerSeries R；hP' : IsUnit ((PowerSeries.coeff 1) P)；P.substInvOfIsUnit h
P'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `PowerSeries.constantCoeff_substInvOfIsUnit`：constantCoeff_substInvOfIsUn
it : (P.substInvOfIsUnit hP').constantCoeff = 0
-/
lemma HasSubst.substInvOfIsUnit : HasSubst (P.substInvOfIsUnit hP') := by
  simp [HasSubst, ← constantCoeff.eq_def]

@[simp]
/-
**PowerSeries.coeff_one_substInvOfIsUnit** 是 Mathlib 中的一个引理，位于命名空间 `PowerSeries`
。
形式化陈述：coeff_one_substInvOfIsUnit : (P.substInvOfIsUnit hP').coeff 1 = hP'.unit⁻¹
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `PowerSeries.substInvOfIsUnit_eq_substInv`：substInvOfIsUnit_eq_substInv :
 letI
· 使用引理 `PowerSeries.coeff_one_substInv`：coeff_one_substInv : P.substInv.coeff 1 
= ⅟(P.coeff 1)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Units.mul_eq_one_iff_eq_inv`：mul_eq_one_iff_eq_inv {a : α} : a * u = 1 ↔
 a = ↑u⁻¹
· 使用定理 `Invertible.invOf_mul_self`：∀ {α : Type u} {inst : Mul α} {inst_1 : One α
} {a : α} [self : Invertible a], ⅟a * a = 1
-/
lemma coeff_one_substInvOfIsUnit : (P.substInvOfIsUnit hP').coeff 1 = hP'.unit⁻¹ := by
  let := hP'.invertible
  rw [substInvOfIsUnit_eq_substInv, coeff_one_substInv]
  exact Units.mul_eq_one_iff_eq_inv.mp Invertible.invOf_mul_self

include hP in
/-
**PowerSeries.subst_substInvOfIsUnit_right** 是 Mathlib 中的一个引理，位于命名空间 `PowerSerie
s`。
形式化陈述：subst_substInvOfIsUnit_right : P.subst (substInvOfIsUnit P hP') = X
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `PowerSeries.substInvOfIsUnit_eq_substInv`：substInvOfIsUnit_eq_substInv :
 letI
· 使用引理 `PowerSeries.subst_substInv_right`：subst_substInv_right : P.subst (substI
nv P) = X
-/
lemma subst_substInvOfIsUnit_right : P.subst (substInvOfIsUnit P hP') = X := by
  let := hP'.invertible
  rw [P.substInvOfIsUnit_eq_substInv hP', P.subst_substInv_right hP]

include hP in
/-
**PowerSeries.subst_substInvOfIsUnit_left** 是 Mathlib 中的一个引理，位于命名空间 `PowerSeries
`。
形式化陈述：subst_substInvOfIsUnit_left : (P.substInvOfIsUnit hP').subst P = X
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `PowerSeries.substInvOfIsUnit_eq_substInv`：substInvOfIsUnit_eq_substInv :
 letI
· 使用引理 `PowerSeries.subst_substInv_left`：subst_substInv_left : P.substInv.subst 
P = X
-/
lemma subst_substInvOfIsUnit_left : (P.substInvOfIsUnit hP').subst P = X := by
  let := hP'.invertible
  rw [P.substInvOfIsUnit_eq_substInv hP', P.subst_substInv_left hP]

end IsUnit

end substInv

section

attribute [local instance] DiscreteTopology.instContinuousSMul

variable {x : ℕ → PowerSeries R} {a : MvPowerSeries τ S}
  [UniformSpace R] [DiscreteUniformity R] [UniformSpace S] [DiscreteUniformity S]

/-
**PowerSeries.subst_tsum** 是 Mathlib 中的一个引理，位于命名空间 `PowerSeries`。
形式化陈述：subst_tsum (hx : Summable x) (ha : HasSubst a) : (∑' i, x i).subst a = ∑' 
i, ((x i).subst a)
参数：hx : Summable x；ha : HasSubst a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PowerSeries.coe_substAlgHom`：coe_substAlgHom (ha : HasSubst a) : ⇑(subst
AlgHom ha) = subst (R
· 使用定理 `instIsUniformAddGroupOfDiscreteUniformity`：∀ {G : Type u_1} [inst : AddG
roup G] [inst_1 : UniformSpace G] [DiscreteUniformity G], IsUniformAddGroup G
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `DiscreteTopology.topologicalRing`：∀ {R : Type u_1} [inst : TopologicalSp
ace R] [inst_1 : NonUnitalNonAssocRing R] [DiscreteTopology R],   IsTopologicalR
ing R
· 使用定理 `DiscreteUniformity.instDiscreteTopology`：∀ (X : Type u_1) [u : UniformSp
ace X] [DiscreteUniformity X], DiscreteTopology X
· 使用定理 `MvPowerSeries.WithPiTopology.instIsUniformAddGroup`：instIsUniformAddGrou
p [AddGroup R] [IsUniformAddGroup R] : IsUniformAddGroup (MvPowerSeries σ R)
· 使用定理 `MvPowerSeries.WithPiTopology.instT2Space`：instT2Space [T2Space R] : T2Sp
ace (MvPowerSeries σ R)
· 使用定理 `T25Space.t2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T25Space
 X], T2Space X
· 使用定理 `T3Space.t25Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T3Space 
X], T25Space X
· 使用定理 `instT3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T0Space X] [R
egularSpace X], T3Space X
· 使用定理 `T1Space.t0Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T1Space X
], T0Space X
· 使用定理 `instT1SpaceOfDiscreteTopology`：∀ {X : Type u_1} [inst : TopologicalSpace
 X] [DiscreteTopology X], T1Space X
· 使用定理 `UniformSpace.to_regularSpace`：∀ {α : Type u} [inst : UniformSpace α], Re
gularSpace α
· 使用定理 `MvPowerSeries.WithPiTopology.instCompleteSpace`：instCompleteSpace [Compl
eteSpace R] : CompleteSpace (MvPowerSeries σ R)
· 使用定理 `DiscreteUniformity.instCompleteSpace`：∀ {α : Type u} [uniformSpace : Uni
formSpace α] [DiscreteUniformity α], CompleteSpace α
· 使用定理 `MvPowerSeries.WithPiTopology.instIsTopologicalRing`：instIsTopologicalRin
g [Ring R] [IsTopologicalRing R] : IsTopologicalRing (MvPowerSeries σ R)
· 使用定理 `MvPowerSeries.LinearTopology.instIsLinearTopologyOfMulOpposite`：∀ {σ : T
ype u_1} {R : Type u_2} [inst : Ring R] [inst_1 : TopologicalSpace R] [IsLinearT
opology R R]   [IsLinearTopology Rᵐᵒᵖ R], IsLinearTo…
· 使用定理 `IsLinearTopology.instOfDiscreteTopology`：∀ {R : Type u_1} {M : Type u_3}
 [inst : Ring R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [inst_
3 : TopologicalSpace M] [Disc…
· 使用定理 `MvPowerSeries.WithPiTopology.instContinuousSMul`：∀ {σ : Type u_1} {R : T
ype u_2} [inst : TopologicalSpace R] {S : Type u_3} [inst_1 : Semiring S]   [ins
t_2 : TopologicalSpace S] [inst_3 : C…
· 使用定理 `DiscreteTopology.instContinuousSMul`：DiscreteTopology.instContinuousSMul
 [IsTopologicalSemiring A] [DiscreteTopology R] : ContinuousSMul R A
· 使用定理 `PowerSeries.HasSubst.hasEval`：∀ {τ : Type u_3} {S : Type u_4} [inst : Co
mmRing S] [inst_1 : TopologicalSpace S] {a : MvPowerSeries τ S},   PowerSeries.H
asSubst a → PowerS…
· 使用定理 `PowerSeries.substAlgHom_eq_aeval`：substAlgHom_eq_aeval [UniformSpace R] 
[DiscreteUniformity R] [UniformSpace S] [DiscreteUniformity S] (ha : HasSubst a)
 : (substAlgHom ha : R…
· 使用定理 `Summable.map_tsum`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst 
: AddCommMonoid α] [inst_1 : TopologicalSpace α] {f : β → α}   {L : SummationFil
ter β} …
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `PowerSeries.continuous_aeval`：continuous_aeval (ha : HasEval a) : Contin
uous (aeval ha : PowerSeries R -> S)
-/
lemma subst_tsum (hx : Summable x) (ha : HasSubst a) :
    (∑' i, x i).subst a = ∑' i, ((x i).subst a) := by
  rw [← coe_substAlgHom ha, substAlgHom_eq_aeval ha, hx.map_tsum _]
  exact continuous_aeval _
/-
**PowerSeries.summable_subst** 是 Mathlib 中的一个引理，位于命名空间 `PowerSeries`。
形式化陈述：summable_subst (hx : Summable x) (ha : HasSubst a) : Summable fun i => (x 
i).subst a
参数：hx : Summable x；ha : HasSubst a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PowerSeries.coe_substAlgHom`：coe_substAlgHom (ha : HasSubst a) : ⇑(subst
AlgHom ha) = subst (R
· 使用定理 `instIsUniformAddGroupOfDiscreteUniformity`：∀ {G : Type u_1} [inst : AddG
roup G] [inst_1 : UniformSpace G] [DiscreteUniformity G], IsUniformAddGroup G
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `DiscreteTopology.topologicalRing`：∀ {R : Type u_1} [inst : TopologicalSp
ace R] [inst_1 : NonUnitalNonAssocRing R] [DiscreteTopology R],   IsTopologicalR
ing R
· 使用定理 `DiscreteUniformity.instDiscreteTopology`：∀ (X : Type u_1) [u : UniformSp
ace X] [DiscreteUniformity X], DiscreteTopology X
· 使用定理 `MvPowerSeries.WithPiTopology.instIsUniformAddGroup`：instIsUniformAddGrou
p [AddGroup R] [IsUniformAddGroup R] : IsUniformAddGroup (MvPowerSeries σ R)
· 使用定理 `MvPowerSeries.WithPiTopology.instT2Space`：instT2Space [T2Space R] : T2Sp
ace (MvPowerSeries σ R)
· 使用定理 `T25Space.t2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T25Space
 X], T2Space X
· 使用定理 `T3Space.t25Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T3Space 
X], T25Space X
· 使用定理 `instT3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T0Space X] [R
egularSpace X], T3Space X
· 使用定理 `T1Space.t0Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T1Space X
], T0Space X
· 使用定理 `instT1SpaceOfDiscreteTopology`：∀ {X : Type u_1} [inst : TopologicalSpace
 X] [DiscreteTopology X], T1Space X
· 使用定理 `UniformSpace.to_regularSpace`：∀ {α : Type u} [inst : UniformSpace α], Re
gularSpace α
· 使用定理 `MvPowerSeries.WithPiTopology.instCompleteSpace`：instCompleteSpace [Compl
eteSpace R] : CompleteSpace (MvPowerSeries σ R)
· 使用定理 `DiscreteUniformity.instCompleteSpace`：∀ {α : Type u} [uniformSpace : Uni
formSpace α] [DiscreteUniformity α], CompleteSpace α
· 使用定理 `MvPowerSeries.WithPiTopology.instIsTopologicalRing`：instIsTopologicalRin
g [Ring R] [IsTopologicalRing R] : IsTopologicalRing (MvPowerSeries σ R)
· 使用定理 `MvPowerSeries.LinearTopology.instIsLinearTopologyOfMulOpposite`：∀ {σ : T
ype u_1} {R : Type u_2} [inst : Ring R] [inst_1 : TopologicalSpace R] [IsLinearT
opology R R]   [IsLinearTopology Rᵐᵒᵖ R], IsLinearTo…
· 使用定理 `IsLinearTopology.instOfDiscreteTopology`：∀ {R : Type u_1} {M : Type u_3}
 [inst : Ring R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [inst_
3 : TopologicalSpace M] [Disc…
· 使用定理 `MvPowerSeries.WithPiTopology.instContinuousSMul`：∀ {σ : Type u_1} {R : T
ype u_2} [inst : TopologicalSpace R] {S : Type u_3} [inst_1 : Semiring S]   [ins
t_2 : TopologicalSpace S] [inst_3 : C…
· 使用定理 `DiscreteTopology.instContinuousSMul`：DiscreteTopology.instContinuousSMul
 [IsTopologicalSemiring A] [DiscreteTopology R] : ContinuousSMul R A
· 使用定理 `PowerSeries.HasSubst.hasEval`：∀ {τ : Type u_3} {S : Type u_4} [inst : Co
mmRing S] [inst_1 : TopologicalSpace S] {a : MvPowerSeries τ S},   PowerSeries.H
asSubst a → PowerS…
· 使用定理 `PowerSeries.substAlgHom_eq_aeval`：substAlgHom_eq_aeval [UniformSpace R] 
[DiscreteUniformity R] [UniformSpace S] [DiscreteUniformity S] (ha : HasSubst a)
 : (substAlgHom ha : R…
· 使用定理 `Summable.map`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : Add
CommMonoid α] [inst_1 : TopologicalSpace α] {f : β → α}   {L : SummationFilter β
} …
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `PowerSeries.continuous_aeval`：continuous_aeval (ha : HasEval a) : Contin
uous (aeval ha : PowerSeries R -> S)
-/
lemma summable_subst (hx : Summable x) (ha : HasSubst a) :
    Summable fun i ↦ (x i).subst a := by
  rw [← coe_substAlgHom ha, substAlgHom_eq_aeval ha]
  exact hx.map _ (continuous_aeval _)

end

section Bivariate

open Finset Finsupp Nat

name_power_vars X₀, X₁ over R

/-
**PowerSeries.coeff_subst_X_zero_add_X_one** 是 Mathlib 中的一个引理，位于命名空间 `PowerSerie
s`。
形式化陈述：coeff_subst_X_zero_add_X_one (f : R⟦X⟧) (e : Fin 2 ->₀ Nat) : MvPowerSerie
s.coeff e (subst (X₀ + X₁) f) = (e 0 + e 1).choose (e 0) * coeff (e 0 + e 1) f
参数：f : R⟦X⟧；e : Fin 2 ->₀ Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.subst.eq_1`：∀ {R : Type u_2} [inst : CommRing R] {τ : Type u
_3} {S : Type u_4} [inst_1 : CommRing S] [inst_2 : Algebra R S]   (a : MvPowerSe
ries τ S) (f…
· 使用定理 `MvPowerSeries.coeff_subst`：coeff_subst (ha : HasSubst a) (f : MvPowerSer
ies σ R) (e : τ ->₀ Nat) : coeff e (subst a f) = finsum (fun d => coeff d f • (c
oeff e (d.prod …
· 使用定理 `MvPowerSeries.hasSubst_of_constantCoeff_zero`：hasSubst_of_constantCoeff_
zero [Finite σ] {a : σ -> MvPowerSeries τ S} (ha : forall s, constantCoeff (a s)
 = 0) : HasSubst a
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MvPowerSeries.constantCoeff_X`：constantCoeff_X (s : σ) : constantCoeff (
R
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finsupp.prod_pow`：prod_pow [Fintype α] (f : α ->₀ Nat) (g : α -> N) : (f
.prod fun a b => g a ^ b) = ∏ a, g a ^ f a
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.univ_unique`：univ_unique [Unique α] : (univ : Finset α) = {defaul
t}
· 使用定理 `Finset.prod_singleton`：prod_singleton (f : ι -> M) (a : ι) : ∏ x in sing
leton a, f x = f a
· 使用定理 `finsum_eq_single`：∀ {M : Type u_2} {α : Sort u_4} [inst : AddCommMonoid 
M] (f : α → M) (a : α),   (∀ (x : α), x ≠ a → f x = 0) → ∑ᶠ (x : α), f x = f a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `MvPolynomial.coeff_add_pow`：coeff_add_pow (d : Fin 2 ->₀ Nat) (n : Nat) 
: coeff d ((X 0 + X 1 : MvPolynomial (Fin 2) R) ^ n) = if (d 0, d 1) in Finset.a
ntidiagonal n th…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Nat.cast_ite`：cast_ite (P : Prop) [Decidable P] (m n : Nat) : ((ite P m 
n : Nat) : R) = ite P (m : R) (n : R)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用引理 `Finsupp.single_add`：single_add (a : ι) (b₁ b₂ : M) : single a (b₁ + b₂) 
= single a b₁ + single a b₂
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
（共 31 条，此处仅展示前 30 条）
-/
lemma coeff_subst_X_zero_add_X_one (f : R⟦X⟧) (e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff e (subst (X₀ + X₁) f) =
      (e 0 + e 1).choose (e 0) * coeff (e 0 + e 1) f := by
  rw [PowerSeries.subst, MvPowerSeries.coeff_subst
    (MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ ↦ by simp))]
  simp_rw [Finsupp.prod_pow, univ_unique, PUnit.default_eq_unit, prod_singleton,
    smul_eq_mul, ← MvPolynomial.coe_X, ← MvPolynomial.coe_add, ← MvPolynomial.coe_pow,
    MvPolynomial.coeff_coe]
  rw [finsum_eq_single _ (single () (e 0 + e 1)), mul_comm]
  · simp [MvPolynomial.coeff_add_pow, coeff]
  · simp only [MvPolynomial.coeff_add_pow, mem_antidiagonal, cast_ite]
    grind
/-
**PowerSeries.coeff_subst_X_zero_subst_mul_X_one** 是 Mathlib 中的一个引理，位于命名空间 `Powe
rSeries`。
形式化陈述：coeff_subst_X_zero_subst_mul_X_one (f : R⟦X⟧) (e : Fin 2 ->₀ Nat) : MvPowe
rSeries.coeff e (subst X₀ f * subst X₁ f) = coeff (e 0) f * coeff (e 1) f
参数：f : R⟦X⟧；e : Fin 2 ->₀ Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.coeff_mul`：coeff_mul [DecidableEq σ] : coeff n (φ * ψ) = ∑
 p in antidiagonal n, coeff p.1 φ * coeff p.2 ψ
· 使用定理 `Finset.sum_eq_single`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] {s : Finset ι} {f : ι → M} (a : ι),   (∀ b ∈ s, b ≠ a → f b = 0) → (a ∉ s
 → f a = 0…
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `ne_zero_and_ne_zero_of_mul`：ne_zero_and_ne_zero_of_mul (h : a * b != 0) 
: a != 0 ∧ b != 0
· 使用定理 `Prod.ext_iff`：∀ {α : Type u} {β : Type v} {x y : α × β}, x = y ↔ x.1 = y
.1 ∧ x.2 = y.2
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.HasAntidiagonal.mem_antidiagonal`：∀ {A : Type u_1} {inst : AddMon
oid A} [self : Finset.HasAntidiagonal A] {n : A} {a : A × A},   a ∈ Finset.HasAn
tidiagonal.antidiagonal n ↔ a…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `PowerSeries.coeff_subst_single`：coeff_subst_single {σ : Type*} [Decidabl
eEq σ] (s : σ) (f : R⟦X⟧) (e : σ ->₀ Nat) : MvPowerSeries.coeff e (subst (MvPowe
rSeries.X s) f) = if…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
· 使用定理 `Finsupp.single_eq_of_ne`：single_eq_of_ne (h : a' != a) : (single a b : α
 ->₀ M) a' = 0
· 使用定理 `Fin.instNeZeroHAddNatOfNat_mathlib_1`：∀ (n : ℕ) [NeZero n], NeZero 1
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
（共 32 条，此处仅展示前 30 条）
-/
lemma coeff_subst_X_zero_subst_mul_X_one (f : R⟦X⟧) (e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff e (subst X₀ f * subst X₁ f) = coeff (e 0) f * coeff (e 1) f := by
  rw [MvPowerSeries.coeff_mul, Finset.sum_eq_single (single 0 (e 0), single 1 (e 1)) ?_ ?_]
  · grind [coeff_subst_single]
  · intro b hb hb'
    by_contra hmul_ne_zero
    rcases ne_zero_and_ne_zero_of_mul hmul_ne_zero with ⟨h0, h1⟩
    simp only [Fin.isValue, coeff_subst_single, ne_eq, ite_eq_right_iff,
      not_forall, exists_prop] at h0 h1
    apply hb'
    rw [Prod.ext_iff, ← mem_antidiagonal.mp hb, h0.1, h1.1]
    simp
  · intro he
    have he' : single 0 (e 0) + single 1 (e 1) = e := by
      ext i
      fin_cases i <;> simp
    exact absurd (mem_antidiagonal.mpr he') he

end Bivariate

end PowerSeries

