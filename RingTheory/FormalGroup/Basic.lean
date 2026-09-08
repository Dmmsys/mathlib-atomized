/-
Copyright (c) 2026 Wenrong Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wenrong Zou
-/
module

public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.Tactic.Ring.NamePowerVars

/-! # Formal group laws over commutative ring

Let `R` be a commutative ring, a one dimensional formal group law is a formal power series
`F(X,Y) ∈ R⟦X,Y⟧` such that
  * `F(X,Y) = X + Y + higher order terms`.
  * `F(F(X,Y),Z) = F(X,F(Y,Z))`.

Under this definition, we can prove that `F(X,0) = X` and `F(0,X) = X`. Moreover, there is a
unique power series `i(X)` such that `F(X, i(X)) = 0`, which is considered to be the inverse
of the formal group law `F(X,Y)`.

## Main definitions/lemmas

* `FormalGroup R`: definition of one dimensional formal group law over commutative ring `R`.

* Properties: `F(X,0) = X` and `F(0,X) = X`.

* Additive formal group laws `𝔾ₐ` and multiplicative formal group laws `𝔾ₘ`.

* `F.Point σ` taking values in the formal power series ring `MvPowerSeries σ R` with the property
that constant coefficient is nilpotent. We have the following typeclass:
- `AddMonoid (F.Point σ)`
when `F` is a commutative formal group law
- `AddCommMonoid (F.Point σ)`

## References
* [Hazewinkel, Michiel. Formal Groups and Applications][hazewinkel1978]

-/

@[expose] public section

variable {R : Type*} [CommRing R] {S : Type*} [CommRing S] {σ τ : Type*}

noncomputable section

open MvPowerSeries Finsupp

name_power_vars X₀, X₁ over R

name_power_vars Y₀, Y₁, Y₂ over R

variable (R) in
/-- A structure for a 1-dimensional formal group law over `R`. -/
@[ext]
/-
**FormalGroup** 是 Mathlib 中的一个结构，位于命名空间 ``。
形式化陈述：FormalGroup where /-- The underlying power series $F(X, Y)$ in two variabl
es. -/ toPowerSeries : MvPowerSeries (Fin 2) R /-- The constant coefficient of t
he formal group law is zero. -/ zero_constantCoeff : toPowerSeries.constantCoeff
 = 0 /-- The coefficient of $X$ in $F(X, Y)$ is 1. -/ lin_coeff_X : toPowerSerie
s.coeff (single 0 1) = 1 /-- The coefficient of $Y$ in $F(X, Y)$ is 1. -/ lin_co
eff_Y : toPowerSeries.coeff (single 1 1) = 1 /-- Associativity condition: $F(F(X
, Y), Z) = F(X, F(Y, Z))$.
参数：X, Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A structure for a 1-dimensional formal group law over `R`. -/
-/
structure FormalGroup where
  /-- The underlying power series $F(X, Y)$ in two variables. -/
  toPowerSeries : MvPowerSeries (Fin 2) R
  /-- The constant coefficient of the formal group law is zero. -/
  zero_constantCoeff : toPowerSeries.constantCoeff = 0
  /-- The coefficient of $X$ in $F(X, Y)$ is 1. -/
  lin_coeff_X : toPowerSeries.coeff (single 0 1) = 1
  /-- The coefficient of $Y$ in $F(X, Y)$ is 1. -/
  lin_coeff_Y : toPowerSeries.coeff (single 1 1) = 1
  /-- Associativity condition: $F(F(X, Y), Z) = F(X, F(Y, Z))$. -/
  assoc : toPowerSeries.subst ![toPowerSeries.subst ![Y₀, Y₁], Y₂]
    = toPowerSeries.subst ![Y₀, toPowerSeries.subst ![Y₁, Y₂]] (S := R)

/-- The natural inclusion from formal group law into formal power series. -/
/-
**FormalGroup.coeToPowerSeries** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：FormalGroup.coeToPowerSeries : Coe (FormalGroup R) (MvPowerSeries (Fin 2) 
R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural inclusion from formal group law into formal power series.
-/
instance FormalGroup.coeToPowerSeries : Coe (FormalGroup R) (MvPowerSeries (Fin 2) R) :=
  ⟨toPowerSeries⟩

/-- Given a formal group `F`, `F.IsComm` is a proposition that $F(X,Y) = F(Y,X)$. -/
/-
**FormalGroup.IsComm** 是 Mathlib 中的一个归纳类型，位于命名空间 `FormalGroup`。
形式化陈述：{R : Type u_1} → [inst : CommRing R] → FormalGroup R → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a formal group `F`, `F.IsComm` is a proposition that $F(X,Y) = F(Y,X)$.
-/
class FormalGroup.IsComm (F : FormalGroup R) : Prop where
  comm : F = (F : MvPowerSeries (Fin 2) R).subst ![X₁, X₀]
/-
**FormalGroup.assoc'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：FormalGroup.assoc' (F : FormalGroup R) {f₀ f₁ f₂ : MvPowerSeries σ R} (h₀ 
: PowerSeries.HasSubst f₀) (h₁ : PowerSeries.HasSubst f₁) (h₂ : PowerSeries.HasS
ubst f₂) : F.toPowerSeries.subst ![F.toPowerSeries.subst ![f₀, f₁], f₂] = F.toPo
werSeries.subst ![f₀, F.toPowerSeries.subst ![f₁, f₂]]
参数：F : FormalGroup R；h₀ : PowerSeries.HasSubst f₀；h₁ : PowerSeries.HasSubst f₁；h
₂ : PowerSeries.HasSubst f₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.hasSubst_of_constantCoeff_nilpotent`：hasSubst_of_constantC
oeff_nilpotent [Finite σ] {a : σ -> MvPowerSeries τ S} (ha : forall s, IsNilpote
nt (constantCoeff (a s))) : HasSubst a …
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.subst_comp_subst_apply`：subst_comp_subst_apply (ha : HasSu
bst a) (hb : HasSubst b) (f : MvPowerSeries σ R) : subst b (subst a f) = subst (
fun s => subst b (a s)) f
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MvPowerSeries.HasSubst.cons_subst_zero_left`：∀ {σ : Type u_1} {R : Type 
u_3} [inst : CommRing R] {f : MvPowerSeries (Fin 2) R} (i j k : σ),   MvPowerSer
ies.constantCoeff f = 0 →     MvP…
· 使用定理 `FormalGroup.zero_constantCoeff`：∀ {R : Type u_1} [inst : CommRing R] (se
lf : FormalGroup R), MvPowerSeries.constantCoeff self.toPowerSeries = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MvPowerSeries.HasSubst.X_X`：∀ {σ : Type u_1} {R : Type u_3} [inst : Comm
Ring R] {i j : σ},   MvPowerSeries.HasSubst ![MvPowerSeries.X i, MvPowerSeries.X
 j]
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MvPowerSeries.subst_X`：subst_X (ha : HasSubst a) (s : σ) : subst (R
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `FormalGroup.assoc`：∀ {R : Type u_1} [inst : CommRing R] (self : FormalGr
oup R),   MvPowerSeries.subst       ![MvPowerSeries.subst ![MvPowerSeries.X 0, M
vPowerS…
· 使用定理 `MvPowerSeries.HasSubst.cons_subst_zero_right`：∀ {σ : Type u_1} {R : Type
 u_3} [inst : CommRing R] {f : MvPowerSeries (Fin 2) R} (i j k : σ),   MvPowerSe
ries.constantCoeff f = 0 →     MvP…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MvPowerSeries.eval₂_X`：eval₂_X (s : σ) : eval₂ φ a (X s) = a s
-/
lemma FormalGroup.assoc' (F : FormalGroup R) {f₀ f₁ f₂ : MvPowerSeries σ R}
    (h₀ : PowerSeries.HasSubst f₀) (h₁ : PowerSeries.HasSubst f₁) (h₂ : PowerSeries.HasSubst f₂) :
    F.toPowerSeries.subst ![F.toPowerSeries.subst ![f₀, f₁], f₂] =
      F.toPowerSeries.subst ![f₀, F.toPowerSeries.subst ![f₁, f₂]] := by
  obtain aux₁ := HasSubst.cons_subst_zero_left (0 : Fin 3) 1 2 F.zero_constantCoeff
  obtain aux₂ := HasSubst.cons_subst_zero_right (0 : Fin 3) 1 2 F.zero_constantCoeff
  have : HasSubst ![f₀, f₁, f₂] :=
    hasSubst_of_constantCoeff_nilpotent fun s => by fin_cases s <;> simpa
  calc
    _ = (F.toPowerSeries.subst ![F.toPowerSeries.subst ![Y₀, Y₁], Y₂]).subst ![f₀, f₁, f₂] := by
      rw [subst_comp_subst_apply aux₁ this]
      congr! 2 with s
      fin_cases s
      · simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.zero_eta, Fin.isValue,
          Matrix.cons_val_zero, subst_comp_subst_apply HasSubst.X_X this]
        congr! 2 with s
        fin_cases s <;> simp [subst_X this]
      · simp [subst_X this]
    _ = _ := by
      rw [F.assoc, subst_comp_subst_apply aux₂ this]
      congr! 2 with s
      fin_cases s
      · simp [subst_X this]
      · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one,
          subst_comp_subst_apply HasSubst.X_X this]
        congr! 2 with s
        fin_cases s <;> simp [subst]
/-
**FormalGroup.comm'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：FormalGroup.comm' (F : FormalGroup R) [F.IsComm] {f g : MvPowerSeries σ R}
 (hf : PowerSeries.HasSubst f) (hg : PowerSeries.HasSubst g) : F.toPowerSeries.s
ubst ![f, g] = F.toPowerSeries.subst ![g, f]
参数：F : FormalGroup R；hf : PowerSeries.HasSubst f；hg : PowerSeries.HasSubst g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FormalGroup.IsComm.comm`：∀ {R : Type u_1} {inst : CommRing R} {F : Forma
lGroup R} [self : F.IsComm],   F.toPowerSeries = MvPowerSeries.subst ![MvPowerSe
ries.X 1, MvP…
· 使用定理 `MvPowerSeries.subst_comp_subst_apply`：subst_comp_subst_apply (ha : HasSu
bst a) (hb : HasSubst b) (f : MvPowerSeries σ R) : subst b (subst a f) = subst (
fun s => subst b (a s)) f
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MvPowerSeries.HasSubst.X_X`：∀ {σ : Type u_1} {R : Type u_3} [inst : Comm
Ring R] {i j : σ},   MvPowerSeries.HasSubst ![MvPowerSeries.X i, MvPowerSeries.X
 j]
· 使用定理 `MvPowerSeries.hasSubst_of_constantCoeff_nilpotent`：hasSubst_of_constantC
oeff_nilpotent [Finite σ] {a : σ -> MvPowerSeries τ S} (ha : forall s, IsNilpote
nt (constantCoeff (a s))) : HasSubst a …
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MvPowerSeries.eval₂_X`：eval₂_X (s : σ) : eval₂ φ a (X s) = a s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
lemma FormalGroup.comm' (F : FormalGroup R) [F.IsComm] {f g : MvPowerSeries σ R}
    (hf : PowerSeries.HasSubst f) (hg : PowerSeries.HasSubst g) :
    F.toPowerSeries.subst ![f, g] = F.toPowerSeries.subst ![g, f] := by
  nth_rw 1 [IsComm.comm]
  rw [subst_comp_subst_apply HasSubst.X_X <| hasSubst_of_constantCoeff_nilpotent (by simp [hf, hg])]
  congr! 2 with s
  fin_cases s <;> simp [subst]

namespace FormalGroup

variable {σ : Type*} (F : FormalGroup R)

set_option linter.unusedVariables false in
/-- `F.Point σ` represents the mathematical space of points of a formal group $F$
taking values in the formal power series ring `MvPowerSeries σ R` with the property
that constant coefficient is nilpotent.

TODO: Mathematically, a 1-dimensional formal group law $F$ over a ring $R$ defines a group
structure on the elements of a complete local $R$-algebra (specifically, its maximal ideal)
via the substitution operation $x +_F y = F(x, y)$. -/
@[nolint unusedArguments]
/-
**FormalGroup.Point** 是 Mathlib 中的一个定义，位于命名空间 `FormalGroup`。
形式化陈述：Point (F : FormalGroup R) (σ : Type*)
参数：F : FormalGroup R；σ : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`F.Point σ` represents the mathematical space of points of a formal group $F$
taking values in the formal power series ring `MvPowerSeries σ R` with the prope
rty
that constant coefficient is nilpotent.

TODO: Mathematically, a 1-dimensional formal group law $F$ over a ring $R$ defin
es a group
structure on the elements of a complete local $R$-algebra (specifically, its max
imal ideal)
via the substitution operation $x +_F y = F(x, y)$.
-/
def Point (F : FormalGroup R) (σ : Type*) := {f : MvPowerSeries σ R // PowerSeries.HasSubst f}
/-
**FormalGroup.** 是 Mathlib 中的一个实例，位于命名空间 `FormalGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Add (F.Point σ) where
  add x y := ⟨F.toPowerSeries.subst ![x.val, y.val],
    IsNilpotent_subst (by simp [hasSubst_of_constantCoeff_nilpotent, x.prop, y.prop])
      (F.zero_constantCoeff ▸ IsNilpotent.zero)⟩

@[simp]
/-
**FormalGroup.add_apply** 是 Mathlib 中的一个引理，位于命名空间 `FormalGroup`。
形式化陈述：add_apply {x y : F.Point σ} : (x + y).val = F.toPowerSeries.subst ![x.val,
 y.val]
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma add_apply {x y : F.Point σ} : (x + y).val = F.toPowerSeries.subst ![x.val, y.val] := by
  rfl
/-
**FormalGroup.** 是 Mathlib 中的一个实例，位于命名空间 `FormalGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Zero (F.Point σ) where
  zero := ⟨0, PowerSeries.HasSubst.zero⟩

@[simp]
/-
**FormalGroup.zero_apply** 是 Mathlib 中的一个引理，位于命名空间 `FormalGroup`。
形式化陈述：zero_apply : (0 : F.Point σ).val = (0 : MvPowerSeries σ R)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma zero_apply : (0 : F.Point σ).val = (0 : MvPowerSeries σ R) := rfl

/-- Additive formal group law `𝔾ₐ(X,Y) = X + Y`. -/
@[simps]
/-
**FormalGroup.** 是 Mathlib 中的一个定义，位于命名空间 `FormalGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Additive formal group law `𝔾ₐ(X,Y) = X + Y`.
-/
def 𝔾ₐ : FormalGroup R where
  toPowerSeries := X₀ + X₁
  zero_constantCoeff := by simp
  lin_coeff_X := by simp [coeff_index_single_X]
  lin_coeff_Y := by simp [coeff_index_single_X]
  assoc := by
    obtain aux₁ := HasSubst.cons_subst_zero_left (f := X₀ + X₁) (0 : Fin 3) 1 2 (by simp)
    obtain aux₂ := HasSubst.cons_subst_zero_right (f := X₀ + X₁) (0 : Fin 3) 1 2 (by simp)
    simp_rw [subst_add aux₁, subst_X aux₁, subst_add aux₂, subst_X aux₂]
    simp [subst_add .X_X, subst_X .X_X, add_assoc]
/-
**FormalGroup.** 是 Mathlib 中的一个实例，位于命名空间 `FormalGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (𝔾ₐ (R := R)).IsComm where
  comm := by simp [subst_add .X_X, subst_X .X_X, add_comm]

/-- Multiplicative formal group law `𝔾ₘ(X,Y) = X + Y + XY`. -/
@[simps]
/-
**FormalGroup.** 是 Mathlib 中的一个定义，位于命名空间 `FormalGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Multiplicative formal group law `𝔾ₘ(X,Y) = X + Y + XY`.
-/
def 𝔾ₘ : FormalGroup R where
  toPowerSeries := X₀ + X₁ + X₀ * X₁
  zero_constantCoeff := by simp
  lin_coeff_X := by
    simp [X, monomial_mul_monomial, coeff_monomial, single_left_inj (one_ne_zero : (1 : ℕ) ≠ 0)]
  lin_coeff_Y := by
    simp [X, monomial_mul_monomial, coeff_monomial, single_left_inj (one_ne_zero : (1 : ℕ) ≠ 0)]
  assoc := by
    obtain aux₁ := HasSubst.cons_subst_zero_left (f := X₀ + X₁ + X₀ * X₁) (0 : Fin 3) 1 2 (by simp)
    obtain aux₂ := HasSubst.cons_subst_zero_right (f := X₀ + X₁ + X₀ * X₁) (0 : Fin 3) 1 2 (by simp)
    simp_rw [subst_add aux₁, subst_mul aux₁, subst_X aux₁, subst_add aux₂, subst_mul aux₂,
      subst_X aux₂]
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, subst_add .X_X, Fin.isValue, subst_X .X_X,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, subst_mul .X_X]
    ring
/-
**FormalGroup.** 是 Mathlib 中的一个实例，位于命名空间 `FormalGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (𝔾ₘ (R := R)).IsComm where
  comm := by simp [subst_add .X_X, subst_mul .X_X, subst_X .X_X, add_comm, mul_comm]

/-- Given an algebra map `f : R →+* S` and a formal group law `F` over `R`, then `f_* F` is a
formal group law formal group law over `S`. This is constructed by applying `f` to all coefficients
of the underlying power series. -/
@[simps]
/-
**FormalGroup.map** 是 Mathlib 中的一个定义，位于命名空间 `FormalGroup`。
形式化陈述：map (f : R ->+* S) : FormalGroup S where toPowerSeries
参数：f : R ->+* S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an algebra map `f : R →+* S` and a formal group law `F` over `R`, then `f_
* F` is a
formal group law formal group law over `S`. This is constructed by applying `f` 
to all coefficients
of the underlying power series.
-/
def map (f : R →+* S) : FormalGroup S where
  toPowerSeries := (F : MvPowerSeries (Fin 2) R).map f
  zero_constantCoeff := by simp [constantCoeff_map, F.zero_constantCoeff, map_zero]
  lin_coeff_X := by simp [F.lin_coeff_X]
  lin_coeff_Y := by simp [F.lin_coeff_Y]
  assoc := by
    have (g₁ g₂ : MvPowerSeries (Fin 3) R) : ![g₁.map f, g₂.map f] =
      fun i => (![g₁, g₂] i).map f := by ext1 i; fin_cases i <;> simp
    simp_rw [(map_X f _).symm, this, ← map_subst .X_X, this, ← map_subst
      (HasSubst.cons_subst_zero_left (0 : Fin 3) 1 2 F.zero_constantCoeff), F.assoc,
      ← map_subst (HasSubst.cons_subst_zero_right (0 : Fin 3) 1 2 F.zero_constantCoeff)]

end FormalGroup

section

namespace FormalGroup

variable (F : FormalGroup R)

/-- An abbreviation of $F(X,0)$ for a formal group $F$. -/
/-
**FormalGroup.Xzero** 是 Mathlib 中的一个缩写定义，位于命名空间 `FormalGroup`。
形式化陈述：Xzero : PowerSeries R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An abbreviation of $F(X,0)$ for a formal group $F$.
-/
abbrev Xzero : PowerSeries R := subst ![PowerSeries.X, 0] F.toPowerSeries
/-
**FormalGroup.constantCoeff_Xzero** 是 Mathlib 中的一个引理，位于命名空间 `FormalGroup`。
形式化陈述：constantCoeff_Xzero : F.Xzero.constantCoeff = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.constantCoeff_subst_eq_zero`：constantCoeff_subst_eq_zero (
ha : HasSubst a) (ha' : forall i, (a i).constantCoeff = 0) {f : MvPowerSeries σ 
R} (hf : f.constantCoeff = 0) :…
· 使用定理 `MvPowerSeries.HasSubst.X_zero`：∀ {σ : Type u_1} {R : Type u_3} [inst : C
ommRing R] {i : σ}, MvPowerSeries.HasSubst ![MvPowerSeries.X i, 0]
· 使用定理 `FormalGroup.zero_constantCoeff`：∀ {R : Type u_1} [inst : CommRing R] (se
lf : FormalGroup R), MvPowerSeries.constantCoeff self.toPowerSeries = 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MvPowerSeries.constantCoeff_X`：constantCoeff_X (s : σ) : constantCoeff (
R
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
lemma constantCoeff_Xzero : F.Xzero.constantCoeff = 0 := by
  simp [PowerSeries.constantCoeff, Xzero, PowerSeries.X, MvPowerSeries.constantCoeff_subst_eq_zero
    HasSubst.X_zero _ F.zero_constantCoeff]

@[simp]
/-
**FormalGroup.coeff_one_Xzero** 是 Mathlib 中的一个引理，位于命名空间 `FormalGroup`。
形式化陈述：coeff_one_Xzero : F.Xzero.coeff 1 = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.coeff.eq_1`：∀ {R : Type u_1} [inst : Semiring R] (n : ℕ), Po
werSeries.coeff n = MvPowerSeries.coeff fun₀ | () => n
· 使用定理 `MvPowerSeries.coeff_subst`：coeff_subst (ha : HasSubst a) (f : MvPowerSer
ies σ R) (e : τ ->₀ Nat) : coeff e (subst a f) = finsum (fun d => coeff d f • (c
oeff e (d.prod …
· 使用定理 `MvPowerSeries.HasSubst.X_zero`：∀ {σ : Type u_1} {R : Type u_3} [inst : C
ommRing R] {i : σ}, MvPowerSeries.HasSubst ![MvPowerSeries.X i, 0]
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `finsum_eq_single`：∀ {M : Type u_2} {α : Sort u_4} [inst : AddCommMonoid 
M] (f : α → M) (a : α),   (∀ (x : α), x ≠ a → f x = 0) → ∑ᶠ (x : α), f x = f a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finsupp.prod_pow`：prod_pow [Fintype α] (f : α ->₀ Nat) (g : α -> N) : (f
.prod fun a b => g a ^ b) = ∏ a, g a ^ f a
· 使用定理 `Fin.prod_univ_two`：prod_univ_two (f : Fin 2 -> M) : ∏ i, f i = f 0 * f 1
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `PowerSeries.coeff_one`：coeff_one (n : Nat) : coeff n (1 : R⟦X⟧) = if n =
 0 then 1 else 0
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `PowerSeries.coeff_X_pow`：coeff_X_pow (m n : Nat) : coeff m ((X : R⟦X⟧) ^
 n) = if m = n then 1 else 0
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `FormalGroup.lin_coeff_X`：∀ {R : Type u_1} [inst : CommRing R] (self : Fo
rmalGroup R), (MvPowerSeries.coeff fun₀ | 0 => 1) self.toPowerSeries = 1
· 使用定理 `Finsupp.prod_single_index`：prod_single_index {a : α} {b : M} {h : α -> M
 -> N} (h_zero : h a 0 = 1) : (single a b).prod h = h a b
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `PowerSeries.coeff_one_X`：coeff_one_X : coeff 1 (X : R⟦X⟧) = 1
-/
lemma coeff_one_Xzero : F.Xzero.coeff 1 = 1 := by
  rw [PowerSeries.coeff, coeff_subst, finsum_eq_single _ (single 0 1)]
  · simp [F.lin_coeff_X]
  · intro d hd
    by_cases hd₁ : d 1 = 0
    · by_cases hd₀ : d 0 = 0
      · simp [hd₀, hd₁]
      simp [hd₁, PowerSeries.coeff_X_pow]
      grind
    simp [hd₁]
  · exact HasSubst.X_zero

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**FormalGroup.Xzero_subst_Xzero** 是 Mathlib 中的一个引理，位于命名空间 `FormalGroup`。
形式化陈述：Xzero_subst_Xzero : F.Xzero.subst F.Xzero = F.Xzero
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.HasSubst.of_constantCoeff_zero'`：∀ {S : Type u_4} [inst : Co
mmRing S] {a : PowerSeries S}, PowerSeries.constantCoeff a = 0 → PowerSeries.Has
Subst a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.constantCoeff.eq_1`：∀ {R : Type u_1} [inst : Semiring R], Po
werSeries.constantCoeff = MvPowerSeries.constantCoeff
· 使用定理 `PowerSeries.X.eq_1`：∀ {R : Type u_1} [inst : Semiring R], PowerSeries.X 
= MvPowerSeries.X ()
· 使用定理 `MvPowerSeries.constantCoeff_subst_eq_zero`：constantCoeff_subst_eq_zero (
ha : HasSubst a) (ha' : forall i, (a i).constantCoeff = 0) {f : MvPowerSeries σ 
R} (hf : f.constantCoeff = 0) :…
· 使用定理 `MvPowerSeries.HasSubst.X_zero`：∀ {σ : Type u_1} {R : Type u_3} [inst : C
ommRing R] {i : σ}, MvPowerSeries.HasSubst ![MvPowerSeries.X i, 0]
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MvPowerSeries.constantCoeff_X`：constantCoeff_X (s : σ) : constantCoeff (
R
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `FormalGroup.zero_constantCoeff`：∀ {R : Type u_1} [inst : CommRing R] (se
lf : FormalGroup R), MvPowerSeries.constantCoeff self.toPowerSeries = 0
· 使用定理 `PowerSeries.subst.eq_1`：∀ {R : Type u_2} [inst : CommRing R] {τ : Type u
_3} {S : Type u_4} [inst_1 : CommRing S] [inst_2 : Algebra R S]   (a : MvPowerSe
ries τ S) (f…
· 使用定理 `MvPowerSeries.subst_comp_subst_apply`：subst_comp_subst_apply (ha : HasSu
bst a) (hb : HasSubst b) (f : MvPowerSeries σ R) : subst b (subst a f) = subst (
fun s => subst b (a s)) f
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `PowerSeries.HasSubst.const`：∀ {τ : Type u_3} {S : Type u_4} [inst : Comm
Ring S] {a : MvPowerSeries τ S},   PowerSeries.HasSubst a → MvPowerSeries.HasSub
st fun x => a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `PowerSeries.subst_X`：subst_X (ha : HasSubst a) : subst a (X : R⟦X⟧) = a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `PowerSeries.coe_substAlgHom`：coe_substAlgHom (ha : HasSubst a) : ⇑(subst
AlgHom ha) = subst (R
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
（共 36 条，此处仅展示前 30 条）
-/
lemma Xzero_subst_Xzero : F.Xzero.subst F.Xzero = F.Xzero := by
  calc
    _ = F.toPowerSeries.subst ![F.toPowerSeries.subst ![PowerSeries.X, 0], 0] := by
      have : PowerSeries.HasSubst (subst ![PowerSeries.X (R := R), 0] F.toPowerSeries) := by
        refine PowerSeries.HasSubst.of_constantCoeff_zero' ?_
        rw [PowerSeries.constantCoeff, PowerSeries.X, constantCoeff_subst_eq_zero HasSubst.X_zero
          (by simp) F.zero_constantCoeff]
      rw [PowerSeries.subst, subst_comp_subst_apply _ this.const]
      · congr! 2 with d
        fin_cases d
        · simp [← PowerSeries.subst_def, PowerSeries.subst_X this]
        · simp [← PowerSeries.subst_def, ← PowerSeries.coe_substAlgHom this]
      · exact HasSubst.X_zero
    _ = _ := by
      have : ![0, 0] = (0 : Fin 2 → PowerSeries R) := by
        ext x : 1; fin_cases x <;> rfl
      simp [F.assoc', this, subst_zero_of_constantCoeff_zero F.zero_constantCoeff,
        PowerSeries.HasSubst.X', PowerSeries.HasSubst]
/-
**FormalGroup.Xzero_eq_X** 是 Mathlib 中的一个引理，位于命名空间 `FormalGroup`。
形式化陈述：Xzero_eq_X : F.Xzero = PowerSeries.X
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `FormalGroup.coeff_one_Xzero`：coeff_one_Xzero : F.Xzero.coeff 1 = 1
· 使用定理 `PowerSeries.HasSubst.of_constantCoeff_zero'`：∀ {S : Type u_4} [inst : Co
mmRing S] {a : PowerSeries S}, PowerSeries.constantCoeff a = 0 → PowerSeries.Has
Subst a
· 使用引理 `FormalGroup.constantCoeff_Xzero`：constantCoeff_Xzero : F.Xzero.constantC
oeff = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.subst_comp_subst_apply`：subst_comp_subst_apply (ha : HasSubs
t a) (hb : HasSubst b) (f : PowerSeries R) : subst b (subst a f) = subst (subst 
b a) f
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `PowerSeries.subst_substInv_left`：subst_substInv_left : P.substInv.subst 
P = X
· 使用定理 `PowerSeries.subst_X`：subst_X (ha : HasSubst a) : subst a (X : R⟦X⟧) = a
· 使用定理 `FormalGroup.Xzero.eq_1`：∀ {R : Type u_1} [inst : CommRing R] (F : Formal
Group R),   F.Xzero = MvPowerSeries.subst ![PowerSeries.X, 0] F.toPowerSeries
· 使用引理 `FormalGroup.Xzero_subst_Xzero`：Xzero_subst_Xzero : F.Xzero.subst F.Xzero
 = F.Xzero
-/
lemma Xzero_eq_X : F.Xzero = PowerSeries.X := by
  have : Invertible (F.Xzero.coeff 1) := (coeff_one_Xzero F) ▸ invertibleOne
  calc
    _ = F.Xzero.substInv.subst (F.Xzero.subst F.Xzero) := by
      have aux₀ : PowerSeries.HasSubst F.Xzero :=
        PowerSeries.HasSubst.of_constantCoeff_zero' <| constantCoeff_Xzero F
      rw [← PowerSeries.subst_comp_subst_apply aux₀ aux₀, PowerSeries.subst_substInv_left _
        F.constantCoeff_Xzero , PowerSeries.subst_X aux₀, Xzero]
    _ = _ := by
      rw [Xzero_subst_Xzero, F.Xzero.subst_substInv_left F.constantCoeff_Xzero]

/-- An abbreviation of $F(0,X)$ for a formal group $F$. -/
/-
**FormalGroup.zeroX** 是 Mathlib 中的一个缩写定义，位于命名空间 `FormalGroup`。
形式化陈述：zeroX : PowerSeries R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An abbreviation of $F(0,X)$ for a formal group $F$.
-/
abbrev zeroX : PowerSeries R := subst ![0, PowerSeries.X] F.toPowerSeries
/-
**FormalGroup.constantCoeff_zeroX** 是 Mathlib 中的一个引理，位于命名空间 `FormalGroup`。
形式化陈述：constantCoeff_zeroX : F.zeroX.constantCoeff = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.constantCoeff_subst_eq_zero`：constantCoeff_subst_eq_zero (
ha : HasSubst a) (ha' : forall i, (a i).constantCoeff = 0) {f : MvPowerSeries σ 
R} (hf : f.constantCoeff = 0) :…
· 使用定理 `MvPowerSeries.HasSubst.zero_X`：∀ {σ : Type u_1} {R : Type u_3} [inst : C
ommRing R] {i : σ}, MvPowerSeries.HasSubst ![0, MvPowerSeries.X i]
· 使用定理 `FormalGroup.zero_constantCoeff`：∀ {R : Type u_1} [inst : CommRing R] (se
lf : FormalGroup R), MvPowerSeries.constantCoeff self.toPowerSeries = 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `MvPowerSeries.constantCoeff_X`：constantCoeff_X (s : σ) : constantCoeff (
R
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
lemma constantCoeff_zeroX : F.zeroX.constantCoeff = 0 := by
  simp [PowerSeries.constantCoeff, zeroX, PowerSeries.X, MvPowerSeries.constantCoeff_subst_eq_zero
    HasSubst.zero_X _ F.zero_constantCoeff]

@[simp]
/-
**FormalGroup.coeff_one_zeroX** 是 Mathlib 中的一个引理，位于命名空间 `FormalGroup`。
形式化陈述：coeff_one_zeroX : F.zeroX.coeff 1 = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.coeff.eq_1`：∀ {R : Type u_1} [inst : Semiring R] (n : ℕ), Po
werSeries.coeff n = MvPowerSeries.coeff fun₀ | () => n
· 使用定理 `MvPowerSeries.coeff_subst`：coeff_subst (ha : HasSubst a) (f : MvPowerSer
ies σ R) (e : τ ->₀ Nat) : coeff e (subst a f) = finsum (fun d => coeff d f • (c
oeff e (d.prod …
· 使用定理 `MvPowerSeries.HasSubst.zero_X`：∀ {σ : Type u_1} {R : Type u_3} [inst : C
ommRing R] {i : σ}, MvPowerSeries.HasSubst ![0, MvPowerSeries.X i]
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `finsum_eq_single`：∀ {M : Type u_2} {α : Sort u_4} [inst : AddCommMonoid 
M] (f : α → M) (a : α),   (∀ (x : α), x ≠ a → f x = 0) → ∑ᶠ (x : α), f x = f a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finsupp.prod_pow`：prod_pow [Fintype α] (f : α ->₀ Nat) (g : α -> N) : (f
.prod fun a b => g a ^ b) = ∏ a, g a ^ f a
· 使用定理 `Fin.prod_univ_two`：prod_univ_two (f : Fin 2 -> M) : ∏ i, f i = f 0 * f 1
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `PowerSeries.coeff_one`：coeff_one (n : Nat) : coeff n (1 : R⟦X⟧) = if n =
 0 then 1 else 0
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `PowerSeries.coeff_X_pow`：coeff_X_pow (m n : Nat) : coeff m ((X : R⟦X⟧) ^
 n) = if m = n then 1 else 0
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `FormalGroup.lin_coeff_Y`：∀ {R : Type u_1} [inst : CommRing R] (self : Fo
rmalGroup R), (MvPowerSeries.coeff fun₀ | 1 => 1) self.toPowerSeries = 1
· 使用定理 `Finsupp.prod_single_index`：prod_single_index {a : α} {b : M} {h : α -> M
 -> N} (h_zero : h a 0 = 1) : (single a b).prod h = h a b
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
（共 31 条，此处仅展示前 30 条）
-/
lemma coeff_one_zeroX : F.zeroX.coeff 1 = 1 := by
  rw [PowerSeries.coeff, coeff_subst, finsum_eq_single _ (single 1 1)]
  · simp [F.lin_coeff_Y]
  · intro d hd
    by_cases hd₁ : d 0 = 0
    · by_cases hd₀ : d 1 = 0
      · simp [hd₀, hd₁]
      simp [hd₁, PowerSeries.coeff_X_pow]
      grind
    simp [hd₁]
  · exact HasSubst.zero_X

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**FormalGroup.zeroX_subst_zeroX** 是 Mathlib 中的一个引理，位于命名空间 `FormalGroup`。
形式化陈述：zeroX_subst_zeroX : F.zeroX.subst F.zeroX = F.zeroX
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PowerSeries.HasSubst.of_constantCoeff_zero'`：∀ {S : Type u_4} [inst : Co
mmRing S] {a : PowerSeries S}, PowerSeries.constantCoeff a = 0 → PowerSeries.Has
Subst a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.constantCoeff.eq_1`：∀ {R : Type u_1} [inst : Semiring R], Po
werSeries.constantCoeff = MvPowerSeries.constantCoeff
· 使用定理 `PowerSeries.X.eq_1`：∀ {R : Type u_1} [inst : Semiring R], PowerSeries.X 
= MvPowerSeries.X ()
· 使用定理 `MvPowerSeries.constantCoeff_subst_eq_zero`：constantCoeff_subst_eq_zero (
ha : HasSubst a) (ha' : forall i, (a i).constantCoeff = 0) {f : MvPowerSeries σ 
R} (hf : f.constantCoeff = 0) :…
· 使用定理 `MvPowerSeries.HasSubst.zero_X`：∀ {σ : Type u_1} {R : Type u_3} [inst : C
ommRing R] {i : σ}, MvPowerSeries.HasSubst ![0, MvPowerSeries.X i]
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `MvPowerSeries.constantCoeff_X`：constantCoeff_X (s : σ) : constantCoeff (
R
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `FormalGroup.zero_constantCoeff`：∀ {R : Type u_1} [inst : CommRing R] (se
lf : FormalGroup R), MvPowerSeries.constantCoeff self.toPowerSeries = 0
· 使用定理 `PowerSeries.subst.eq_1`：∀ {R : Type u_2} [inst : CommRing R] {τ : Type u
_3} {S : Type u_4} [inst_1 : CommRing S] [inst_2 : Algebra R S]   (a : MvPowerSe
ries τ S) (f…
· 使用定理 `MvPowerSeries.subst_comp_subst_apply`：subst_comp_subst_apply (ha : HasSu
bst a) (hb : HasSubst b) (f : MvPowerSeries σ R) : subst b (subst a f) = subst (
fun s => subst b (a s)) f
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `PowerSeries.HasSubst.const`：∀ {τ : Type u_3} {S : Type u_4} [inst : Comm
Ring S] {a : MvPowerSeries τ S},   PowerSeries.HasSubst a → MvPowerSeries.HasSub
st fun x => a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `PowerSeries.coe_substAlgHom`：coe_substAlgHom (ha : HasSubst a) : ⇑(subst
AlgHom ha) = subst (R
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
（共 36 条，此处仅展示前 30 条）
-/
lemma zeroX_subst_zeroX : F.zeroX.subst F.zeroX = F.zeroX := by
  calc
    _ = F.toPowerSeries.subst ![0, F.toPowerSeries.subst ![0, PowerSeries.X]] := by
      have : PowerSeries.HasSubst (subst ![0, PowerSeries.X (R := R)] F.toPowerSeries) := by
        refine PowerSeries.HasSubst.of_constantCoeff_zero' ?_
        rw [PowerSeries.constantCoeff, PowerSeries.X, constantCoeff_subst_eq_zero HasSubst.zero_X
          (by simp) F.zero_constantCoeff]
      rw [PowerSeries.subst, subst_comp_subst_apply _ this.const]
      · congr! 2 with d
        fin_cases d
        · simp [← PowerSeries.subst_def, ← PowerSeries.coe_substAlgHom this]
        · simp [← PowerSeries.subst_def, PowerSeries.subst_X this]
      · exact HasSubst.zero_X
    _ = _ := by
      have : ![0, 0] = (0 : Fin 2 → PowerSeries R) := by ext x : 1; fin_cases x <;> rfl
      simp [← F.assoc', this, subst_zero_of_constantCoeff_zero F.zero_constantCoeff,
        PowerSeries.HasSubst.X', PowerSeries.HasSubst]
/-
**FormalGroup.zeroX_eq_X** 是 Mathlib 中的一个引理，位于命名空间 `FormalGroup`。
形式化陈述：zeroX_eq_X : F.zeroX = PowerSeries.X
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `FormalGroup.coeff_one_zeroX`：coeff_one_zeroX : F.zeroX.coeff 1 = 1
· 使用定理 `PowerSeries.HasSubst.of_constantCoeff_zero'`：∀ {S : Type u_4} [inst : Co
mmRing S] {a : PowerSeries S}, PowerSeries.constantCoeff a = 0 → PowerSeries.Has
Subst a
· 使用引理 `FormalGroup.constantCoeff_zeroX`：constantCoeff_zeroX : F.zeroX.constantC
oeff = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.subst_comp_subst_apply`：subst_comp_subst_apply (ha : HasSubs
t a) (hb : HasSubst b) (f : PowerSeries R) : subst b (subst a f) = subst (subst 
b a) f
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `PowerSeries.subst_substInv_left`：subst_substInv_left : P.substInv.subst 
P = X
· 使用定理 `PowerSeries.subst_X`：subst_X (ha : HasSubst a) : subst a (X : R⟦X⟧) = a
· 使用定理 `FormalGroup.zeroX.eq_1`：∀ {R : Type u_1} [inst : CommRing R] (F : Formal
Group R),   F.zeroX = MvPowerSeries.subst ![0, PowerSeries.X] F.toPowerSeries
· 使用引理 `FormalGroup.zeroX_subst_zeroX`：zeroX_subst_zeroX : F.zeroX.subst F.zeroX
 = F.zeroX
-/
lemma zeroX_eq_X : F.zeroX = PowerSeries.X := by
  have : Invertible (F.zeroX.coeff 1) := (coeff_one_zeroX F) ▸ invertibleOne
  calc
    _ = F.zeroX.substInv.subst (F.zeroX.subst F.zeroX) := by
      have aux₀ : PowerSeries.HasSubst F.zeroX :=
        PowerSeries.HasSubst.of_constantCoeff_zero' <| F.constantCoeff_zeroX
      rw [← PowerSeries.subst_comp_subst_apply aux₀ aux₀, PowerSeries.subst_substInv_left _
        F.constantCoeff_zeroX, PowerSeries.subst_X aux₀, zeroX]
    _ = _ := by
      rw [zeroX_subst_zeroX, F.zeroX.subst_substInv_left F.constantCoeff_zeroX]
/-
**FormalGroup.add_zero** 是 Mathlib 中的一个定理，位于命名空间 `FormalGroup`。
形式化陈述：add_zero {f : MvPowerSeries σ R} (hf : PowerSeries.HasSubst f) : F.toPower
Series.subst ![f, 0] = f
参数：hf : PowerSeries.HasSubst f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.subst.eq_1`：∀ {R : Type u_2} [inst : CommRing R] {τ : Type u
_3} {S : Type u_4} [inst_1 : CommRing S] [inst_2 : Algebra R S]   (a : MvPowerSe
ries τ S) (f…
· 使用定理 `MvPowerSeries.subst_comp_subst_apply`：subst_comp_subst_apply (ha : HasSu
bst a) (hb : HasSubst b) (f : MvPowerSeries σ R) : subst b (subst a f) = subst (
fun s => subst b (a s)) f
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MvPowerSeries.HasSubst.X_zero`：∀ {σ : Type u_1} {R : Type u_3} [inst : C
ommRing R] {i : σ}, MvPowerSeries.HasSubst ![MvPowerSeries.X i, 0]
· 使用定理 `PowerSeries.HasSubst.const`：∀ {τ : Type u_3} {S : Type u_4} [inst : Comm
Ring S] {a : MvPowerSeries τ S},   PowerSeries.HasSubst a → MvPowerSeries.HasSub
st fun x => a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MvPowerSeries.eval₂_X`：eval₂_X (s : σ) : eval₂ φ a (X s) = a s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `MvPolynomial.toMvPowerSeries_isDenseInducing`：∀ {σ : Type u_1} {R : Type
 u_2} [inst : CommRing R] [inst_1 : UniformSpace R],   IsDenseInducing MvPolynom
ial.toMvPowerSeries
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `Exists.choose.congr_simp`：∀ {α : Sort u_1} {p p_1 : α → Prop} (e_p : p =
 p_1) (P : ∃ a, p a), P.choose = ⋯.choose
· 使用定理 `Classical.choose_eq`：∀ {α : Sort u_1} (a : α), ⋯.choose = a
· 使用定理 `MvPolynomial.eval₂_zero`：eval₂_zero : (0 : MvPolynomial σ R).eval₂ f g =
 0
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `FormalGroup.Xzero_eq_X`：Xzero_eq_X : F.Xzero = PowerSeries.X
· 使用定理 `PowerSeries.subst_X`：subst_X (ha : HasSubst a) : subst a (X : R⟦X⟧) = a
-/
theorem add_zero {f : MvPowerSeries σ R} (hf : PowerSeries.HasSubst f) :
    F.toPowerSeries.subst ![f, 0] = f := by
  calc
    _ = PowerSeries.subst f (F.toPowerSeries.subst ![PowerSeries.X (R := R), 0]) := by
      rw [PowerSeries.subst, subst_comp_subst_apply _ hf.const]
      · congr! 2 with s
        fin_cases s
        · simp [PowerSeries.X, subst]
        · simp [subst, eval₂]
      exact HasSubst.X_zero
    _ = _ := by
      simp [Xzero_eq_X, PowerSeries.subst_X hf]
/-
**FormalGroup.zero_add** 是 Mathlib 中的一个定理，位于命名空间 `FormalGroup`。
形式化陈述：zero_add {f : MvPowerSeries σ R} (hf : PowerSeries.HasSubst f) : F.toPower
Series.subst ![0, f] = f
参数：hf : PowerSeries.HasSubst f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerSeries.subst.eq_1`：∀ {R : Type u_2} [inst : CommRing R] {τ : Type u
_3} {S : Type u_4} [inst_1 : CommRing S] [inst_2 : Algebra R S]   (a : MvPowerSe
ries τ S) (f…
· 使用定理 `MvPowerSeries.subst_comp_subst_apply`：subst_comp_subst_apply (ha : HasSu
bst a) (hb : HasSubst b) (f : MvPowerSeries σ R) : subst b (subst a f) = subst (
fun s => subst b (a s)) f
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MvPowerSeries.HasSubst.zero_X`：∀ {σ : Type u_1} {R : Type u_3} [inst : C
ommRing R] {i : σ}, MvPowerSeries.HasSubst ![0, MvPowerSeries.X i]
· 使用定理 `PowerSeries.HasSubst.const`：∀ {τ : Type u_3} {S : Type u_4} [inst : Comm
Ring S] {a : MvPowerSeries τ S},   PowerSeries.HasSubst a → MvPowerSeries.HasSub
st fun x => a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MvPolynomial.toMvPowerSeries_isDenseInducing`：∀ {σ : Type u_1} {R : Type
 u_2} [inst : CommRing R] [inst_1 : UniformSpace R],   IsDenseInducing MvPolynom
ial.toMvPowerSeries
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `Exists.choose.congr_simp`：∀ {α : Sort u_1} {p p_1 : α → Prop} (e_p : p =
 p_1) (P : ∃ a, p a), P.choose = ⋯.choose
· 使用定理 `Classical.choose_eq`：∀ {α : Sort u_1} (a : α), ⋯.choose = a
· 使用定理 `MvPolynomial.eval₂_zero`：eval₂_zero : (0 : MvPolynomial σ R).eval₂ f g =
 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `MvPowerSeries.eval₂_X`：eval₂_X (s : σ) : eval₂ φ a (X s) = a s
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `FormalGroup.zeroX_eq_X`：zeroX_eq_X : F.zeroX = PowerSeries.X
· 使用定理 `PowerSeries.subst_X`：subst_X (ha : HasSubst a) : subst a (X : R⟦X⟧) = a
-/
theorem zero_add {f : MvPowerSeries σ R} (hf : PowerSeries.HasSubst f) :
    F.toPowerSeries.subst ![0, f] = f := by
  calc
    _ = PowerSeries.subst f (F.toPowerSeries.subst ![0, PowerSeries.X (R := R)]) := by
      rw [PowerSeries.subst, subst_comp_subst_apply _ hf.const]
      · congr! 2 with s
        fin_cases s
        · simp [subst, eval₂]
        · simp [PowerSeries.X, subst]
      · exact HasSubst.zero_X
    _ = _ := by
      simp [zeroX_eq_X, PowerSeries.subst_X hf]
/-
**FormalGroup.** 是 Mathlib 中的一个实例，位于命名空间 `FormalGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddMonoid (F.Point σ) where
  zero_add x := Subtype.ext (zero_add F x.prop)
  add_zero x := Subtype.ext (add_zero F x.prop)
  nsmul := nsmulRec
  add_assoc x y z := Subtype.ext <| F.assoc' x.prop y.prop z.prop
/-
**FormalGroup.** 是 Mathlib 中的一个实例，位于命名空间 `FormalGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [F.IsComm] : AddCommMonoid (F.Point σ) where
  add_comm x y := Subtype.ext <| F.comm' x.prop y.prop

end FormalGroup

end

