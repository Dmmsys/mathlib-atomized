/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Jujian Zhang
-/
module

public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.RingTheory.Localization.Defs
public import Mathlib.RingTheory.OreLocalization.Ring

/-!
# Localized Module

Given a commutative semiring `R`, a multiplicative subset `S ⊆ R` and an `R`-module `M`, we can
localize `M` by `S`. This gives us a `Localization S`-module.

## Main definitions

* `LocalizedModule.r`: the equivalence relation defining this localization, namely
  `(m, s) ≈ (m', s')` if and only if there is some `u : S` such that `u • s' • m = u • s • m'`.
* `LocalizedModule M S`: the localized module by `S`.
* `LocalizedModule.mk`: the canonical map sending `(m, s) : M × S ↦ m/s : LocalizedModule M S`
* `LocalizedModule.liftOn`: any well-defined function `f : M × S → α` respecting `r` descents to
  a function `LocalizedModule M S → α`
* `LocalizedModule.liftOn₂`: any well-defined function `f : M × S → M × S → α` respecting `r`
  descents to a function `LocalizedModule M S → LocalizedModule M S`
* `LocalizedModule.mk_add_mk`: in the localized module
  `mk m s + mk m' s' = mk (s' • m + s • m') (s * s')`
* `LocalizedModule.mk_smul_mk` : in the localized module, for any `r : R`, `s t : S`, `m : M`,
  we have `mk r s • mk m t = mk (r • m) (s * t)` where `mk r s : Localization S` is localized ring
  by `S`.
* `LocalizedModule.isModule` : `LocalizedModule M S` is a `Localization S`-module.

## Future work

* Redefine `Localization` for monoids and rings to coincide with `LocalizedModule`.
-/

@[expose] public section

open Module

namespace LocalizedModule

universe u v

variable {R : Type u} [CommSemiring R] (S : Submonoid R)
variable (M : Type v) [AddCommMonoid M] [Module R M]
variable (T : Type*) [CommSemiring T] [Algebra R T] [IsLocalization S T]
variable (T' : Type*) [CommSemiring T'] [Algebra R T'] [IsLocalization S T']

/-- The equivalence relation on `M × S` where `(m1, s1) ≈ (m2, s2)` if and only if
for some (u : S), u * (s2 • m1 - s1 • m2) = 0 -/
/-
**LocalizedModule.r** 是 Mathlib 中的一个定义，位于命名空间 `LocalizedModule`。
形式化陈述：r (a b : M × S) : Prop
参数：a b : M × S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence relation on `M × S` where `(m1, s1) ≈ (m2, s2)` if and only if
for some (u : S), u * (s2 • m1 - s1 • m2) = 0
-/
def r (a b : M × S) : Prop :=
  ∃ u : S, u • b.2 • a.1 = u • a.2 • b.1
/-
**LocalizedModule.oreEqv_eq_r** 是 Mathlib 中的一个引理，位于命名空间 `LocalizedModule`。
形式化陈述：oreEqv_eq_r : (OreLocalization.oreEqv S M).r = r S M
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submonoid.smul_def`：∀ {M' : Type u_1} {α : Type u_2} [inst : MulOneClass
 M'] [inst_1 : SMul M' α] {S : Submonoid M'} (g : ↥S) (a : α),   g • a = ↑g • a
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `Submonoid.coe_mul`：coe_mul (x y : S) : (↑(x * y) : M) = ↑x * ↑y
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
lemma oreEqv_eq_r : (OreLocalization.oreEqv S M).r = r S M := by
  ext a b
  constructor
  · rintro ⟨u, v, h₁, h₂⟩
    use u
    simp only [Submonoid.smul_def, smul_smul, h₂]
    rw [mul_comm, mul_smul, ← h₁, mul_comm, mul_smul, Submonoid.smul_def]
  · rintro ⟨u, hu⟩
    use u * a.2, u * b.2
    rw [mul_smul, ← hu, mul_smul, Submonoid.coe_mul, mul_assoc, mul_assoc, mul_comm (a.2 : R)]
    simp [Submonoid.smul_def]
/-
**LocalizedModule.r.isEquiv** 是 Mathlib 中的一个定理，位于命名空间 `LocalizedModule.r`。
形式化陈述：∀ {R : Type u} [inst : CommSemiring R] (S : Submonoid R) (M : Type v) [ins
t_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M], IsEquiv (M × ↥S) (Localiz
edModule.r S M)
参数：S : Submonoid R；M : Type v；M × ↥S；LocalizedModule.r S M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
-/
theorem r.isEquiv : IsEquiv _ (r S M) :=
  { refl := fun ⟨m, s⟩ => ⟨1, by rw [one_smul]⟩
    trans := fun ⟨m1, s1⟩ ⟨m2, s2⟩ ⟨m3, s3⟩ ⟨u1, hu1⟩ ⟨u2, hu2⟩ => by
      use u1 * u2 * s2
      -- Put everything in the same shape, sorting the terms using `simp`
      have hu1' := congr_arg ((u2 * s3) • ·) hu1.symm
      have hu2' := congr_arg ((u1 * s1) • ·) hu2.symm
      simp only [← mul_smul, mul_comm, mul_left_comm] at hu1' hu2' ⊢
      rw [hu2', hu1']
    symm := fun ⟨_, _⟩ ⟨_, _⟩ ⟨u, hu⟩ => ⟨u, hu.symm⟩ }
/-
**LocalizedModule.r.setoid** 是 Mathlib 中的一个定义，位于命名空间 `LocalizedModule.r`。
形式化陈述：{R : Type u} →   [inst : CommSemiring R] →     (S : Submonoid R) → (M : Ty
pe v) → [inst_1 : AddCommMonoid M] → [_root_.Module R M] → Setoid (M × ↥S)
参数：S : Submonoid R；M : Type v；M × ↥S。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance r.setoid : Setoid (M × S) where
  r := r S M
  iseqv := ⟨(r.isEquiv S M).refl, (r.isEquiv S M).symm _ _, (r.isEquiv S M).trans _ _ _⟩

/-- If `S` is a multiplicative subset of a ring `R` and `M` an `R`-module, then
we can localize `M` by `S`.
-/
/-
**LocalizedModule._root_.LocalizedModule** 是 Mathlib 中的一个缩写定义，位于命名空间 `LocalizedM
odule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `S` is a multiplicative subset of a ring `R` and `M` an `R`-module, then
we can localize `M` by `S`.
-/
abbrev _root_.LocalizedModule : Type max u v :=
  OreLocalization S M
/-
**LocalizedModule.example_localization_eq_localizedModule** 是 Mathlib 中的一个引理，位于命
名空间 `LocalizedModule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma example_localization_eq_localizedModule
    {R} [CommSemiring R] (S : Submonoid R) : Localization S = LocalizedModule S R := by
  with_reducible rfl

section

variable {M S}

/-- The canonical map sending `(m, s) ↦ m/s` -/
/-
**LocalizedModule.mk** 是 Mathlib 中的一个缩写定义，位于命名空间 `LocalizedModule`。
形式化陈述：mk (m : M) (s : S) : LocalizedModule S M
参数：m : M；s : S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical map sending `(m, s) ↦ m/s`
-/
abbrev mk (m : M) (s : S) : LocalizedModule S M := m /ₒ s
/-
**LocalizedModule.mk_eq** 是 Mathlib 中的一个定理，位于命名空间 `LocalizedModule`。
形式化陈述：mk_eq {m m' : M} {s s' : S} : mk m s = mk m' s' ↔ exists u : S, u • s' • m
 = u • s • m'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LocalizedModule.mk.eq_1`：∀ {R : Type u} [inst : CommSemiring R] {S : Sub
monoid R} {M : Type v} [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M]
 (m : M) (s :…
· 使用定理 `OreLocalization.oreDiv_eq_iff`：oreDiv_eq_iff {r₁ r₂ : X} {s₁ s₂ : S} : r
₁ /ₒ s₁ = r₂ /ₒ s₂ ↔ exists (u : S) (v : R), u • r₂ = v • r₁ ∧ u * s₂ = v * s₁
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用引理 `LocalizedModule.oreEqv_eq_r`：oreEqv_eq_r : (OreLocalization.oreEqv S M).
r = r S M
-/
theorem mk_eq {m m' : M} {s s' : S} : mk m s = mk m' s' ↔ ∃ u : S, u • s' • m = u • s • m' := by
  rw [mk, mk, OreLocalization.oreDiv_eq_iff]
  exact congr($(oreEqv_eq_r S M) ⟨m, s⟩ ⟨m', s'⟩)

@[elab_as_elim, induction_eliminator, cases_eliminator]
/-
**LocalizedModule.induction_on** 是 Mathlib 中的一个定理，位于命名空间 `LocalizedModule`。
形式化陈述：induction_on {β : LocalizedModule S M -> Prop} (h : forall (m : M) (s : S)
, β (mk m s)) : forall x : LocalizedModule S M, β x
参数：h : forall (m : M) (s : S), β (mk m s)。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem induction_on {β : LocalizedModule S M → Prop} (h : ∀ (m : M) (s : S), β (mk m s)) :
    ∀ x : LocalizedModule S M, β x := by
  rintro ⟨⟨m, s⟩⟩
  exact h m s

@[elab_as_elim]
/-
**LocalizedModule.induction_on** 是 Mathlib 中的一个定理，位于命名空间 `LocalizedModule`。
形式化陈述：induction_on {β : LocalizedModule S M -> Prop} (h : forall (m : M) (s : S)
, β (mk m s)) : forall x : LocalizedModule S M, β x
参数：h : forall (m : M) (s : S), β (mk m s)。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem induction_on₂ {β : LocalizedModule S M → LocalizedModule S M → Prop}
    (h : ∀ (m m' : M) (s s' : S), β (mk m s) (mk m' s')) : ∀ x y, β x y := by
  rintro ⟨⟨m, s⟩⟩ ⟨⟨m', s'⟩⟩
  exact h m m' s s'

/-- If `f : M × S → α` respects the equivalence relation `LocalizedModule.r`, then
`f` descents to a map `LocalizedModule M S → α`.
-/
/-
**LocalizedModule.liftOn** 是 Mathlib 中的一个定义，位于命名空间 `LocalizedModule`。
形式化陈述：liftOn {α : Type*} (x : LocalizedModule S M) (f : M × S -> α) (wd : forall
 (p p' : M × S), p ≈ p' -> f p = f p') : α
参数：x : LocalizedModule S M；f : M × S -> α；wd : forall (p p' : M × S), p ≈ p' -> 
f p = f p'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f : M × S → α` respects the equivalence relation `LocalizedModule.r`, then
`f` descents to a map `LocalizedModule M S → α`.
-/
def liftOn {α : Type*} (x : LocalizedModule S M) (f : M × S → α)
    (wd : ∀ (p p' : M × S), p ≈ p' → f p = f p') : α :=
  Quotient.liftOn x f (by simpa +instances only [r.setoid, ← oreEqv_eq_r S M] using wd)
/-
**LocalizedModule.liftOn_mk** 是 Mathlib 中的一个定理，位于命名空间 `LocalizedModule`。
形式化陈述：liftOn_mk {α : Type*} {f : M × S -> α} (wd : forall (p p' : M × S), p ≈ p'
 -> f p = f p') (m : M) (s : S) : liftOn (mk m s) f wd = f ⟨m, s⟩
参数：wd : forall (p p' : M × S), p ≈ p' -> f p = f p'；m : M；s : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Quotient.liftOn_mk`：Quotient.liftOn_mk {s : Setoid α} (f : α -> β) (h : 
forall a b : α, a ≈ b -> f a = f b) (x : α) : Quotient.liftOn (Quotient.mk s x) 
f h = f …
-/
theorem liftOn_mk {α : Type*} {f : M × S → α} (wd : ∀ (p p' : M × S), p ≈ p' → f p = f p')
    (m : M) (s : S) : liftOn (mk m s) f wd = f ⟨m, s⟩ := by convert! Quotient.liftOn_mk f wd ⟨m, s⟩

/-- If `f : M × S → M × S → α` respects the equivalence relation `LocalizedModule.r`, then
`f` descents to a map `LocalizedModule M S → LocalizedModule M S → α`.
-/
/-
**LocalizedModule.liftOn** 是 Mathlib 中的一个定义，位于命名空间 `LocalizedModule`。
形式化陈述：liftOn {α : Type*} (x : LocalizedModule S M) (f : M × S -> α) (wd : forall
 (p p' : M × S), p ≈ p' -> f p = f p') : α
参数：x : LocalizedModule S M；f : M × S -> α；wd : forall (p p' : M × S), p ≈ p' -> 
f p = f p'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f : M × S → M × S → α` respects the equivalence relation `LocalizedModule.r`
, then
`f` descents to a map `LocalizedModule M S → LocalizedModule M S → α`.
-/
def liftOn₂ {α : Type*} (x y : LocalizedModule S M) (f : M × S → M × S → α)
    (wd : ∀ (p q p' q' : M × S), p ≈ p' → q ≈ q' → f p q = f p' q') : α :=
  Quotient.liftOn₂ x y f (by simpa +instances only [r.setoid, ← oreEqv_eq_r S M] using wd)
/-
**LocalizedModule.liftOn** 是 Mathlib 中的一个定义，位于命名空间 `LocalizedModule`。
形式化陈述：liftOn {α : Type*} (x : LocalizedModule S M) (f : M × S -> α) (wd : forall
 (p p' : M × S), p ≈ p' -> f p = f p') : α
参数：x : LocalizedModule S M；f : M × S -> α；wd : forall (p p' : M × S), p ≈ p' -> 
f p = f p'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem liftOn₂_mk {α : Type*} (f : M × S → M × S → α)
    (wd : ∀ (p q p' q' : M × S), p ≈ p' → q ≈ q' → f p q = f p' q') (m m' : M)
    (s s' : S) : liftOn₂ (mk m s) (mk m' s') f wd = f ⟨m, s⟩ ⟨m', s'⟩ := by
  convert! Quotient.liftOn₂_mk f wd _ _

/-- If `S` contains `0` then the localization at `S` is trivial. -/
/-
**LocalizedModule.subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `LocalizedModule`。
形式化陈述：subsingleton (h : 0 in S) : Subsingleton (LocalizedModule S M)
参数：h : 0 in S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LocalizedModule.induction_on₂`：induction_on₂ {β : LocalizedModule S M ->
 LocalizedModule S M -> Prop} (h : forall (m m' : M) (s s' : S), β (mk m s) (mk 
m' s')) : forall x …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LocalizedModule.mk_eq`：mk_eq {m m' : M} {s s' : S} : mk m s = mk m' s' ↔
 exists u : S, u • s' • m = u • s • m'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `S` contains `0` then the localization at `S` is trivial.
-/
theorem subsingleton (h : 0 ∈ S) : Subsingleton (LocalizedModule S M) := by
  refine ⟨fun a b ↦ ?_⟩
  induction a, b using LocalizedModule.induction_on₂
  exact mk_eq.mpr ⟨⟨0, h⟩, by simp only [Submonoid.mk_smul, zero_smul]⟩
/-
**LocalizedModule.zero_mk** 是 Mathlib 中的一个定理，位于命名空间 `LocalizedModule`。
形式化陈述：zero_mk (s : S) : mk (0 : M) s = 0
参数：s : S。
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
theorem zero_mk (s : S) : mk (0 : M) s = 0 := by simp [mk]
/-
**LocalizedModule.mk_add_mk** 是 Mathlib 中的一个定理，位于命名空间 `LocalizedModule`。
形式化陈述：mk_add_mk {m1 m2 : M} {s1 s2 : S} : mk m1 s1 + mk m2 s2 = mk (s2 • m1 + s1
 • m2) (s1 * s2)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OreLocalization.oreDiv_add_oreDiv`：oreDiv_add_oreDiv {r r' : X} {s s' : 
S} : r /ₒ s + r' /ₒ s' = (oreDenom (s : R) s' • r + oreNum (s : R) s' • r') /ₒ (
oreDenom (s : R) s' * s…
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mk_add_mk {m1 m2 : M} {s1 s2 : S} :
    mk m1 s1 + mk m2 s2 = mk (s2 • m1 + s1 • m2) (s1 * s2) := by
  simp [mk, OreLocalization.oreDiv_add_oreDiv, mul_comm s1 s2, Submonoid.smul_def]
/-
**LocalizedModule.mk_neg** 是 Mathlib 中的一个定理，位于命名空间 `LocalizedModule`。
形式化陈述：mk_neg {M : Type*} [AddCommGroup M] [Module R M] {m : M} {s : S} : mk (-m)
 s = -mk m s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OreLocalization.neg_def`：∀ {R : Type u_1} [inst : Monoid R] {S : Submono
id R} [inst_1 : OreLocalization.OreSet S] {X : Type u_2}   [inst_2 : AddGroup X]
 [inst_3 : Di…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mk_neg {M : Type*} [AddCommGroup M] [Module R M] {m : M} {s : S} :
    mk (-m) s = -mk m s := by simp [mk]

/--
The multiplication on the localized module.
Note that this gives a diamond with the instance on `R[S⁻¹]` (which does not require commutativity),
but is defeq to it under `with_reducible_and_instances`.
See https://github.com/leanprover-community/mathlib4/pull/25671 for an approach to generalize this
but it requires right `R` actions on `R`-algebras.
-/
/-
**LocalizedModule.mul** 是 Mathlib 中的一个定义，位于命名空间 `LocalizedModule`。
形式化陈述：{R : Type u} →   [inst : CommSemiring R] →     {A : Type u_3} →       [ins
t_1 : Semiring A] →         [inst_2 : Algebra R A] → {S : Submonoid R} → Localiz
edModule S A → LocalizedModule S A → LocalizedModule S A
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The multiplication on the localized module.
Note that this gives a diamond with the instance on `R[S⁻¹]` (which does not req
uire commutativity),
but is defeq to it under `with_reducible_and_instances`.
See https://github.com/leanprover-community/mathlib4/pull/25671 for an approach 
to generalize this
but it requires right `R` actions on `R`-algebras.
-/
protected def mul {A : Type*} [Semiring A] [Algebra R A] {S : Submonoid R}
    (m₁ m₂ : LocalizedModule S A) : LocalizedModule S A :=
  liftOn₂ m₁ m₂ (fun x₁ x₂ => LocalizedModule.mk (x₁.1 * x₂.1) (x₂.2 * x₁.2)) (by
    rintro ⟨a₁, s₁⟩ ⟨a₂, s₂⟩ ⟨b₁, t₁⟩ ⟨b₂, t₂⟩ ⟨u₁, e₁⟩ ⟨u₂, e₂⟩
    simp only [mul_comm s₂ s₁, mul_comm t₂ t₁]
    rw [mk_eq]
    use u₁ * u₂
    dsimp [Submonoid.smul_def] at *
    simp only [mul_smul_mul_comm, e₁, e₂])
/-
**LocalizedModule.** 是 Mathlib 中的一个实例，位于命名空间 `LocalizedModule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 900) {A : Type*} [Semiring A] [Algebra R A] {S : Submonoid R} :
    Monoid (LocalizedModule S A) :=
  fast_instance%
  { __ := (inferInstance : One (LocalizedModule S A))
    mul := LocalizedModule.mul
    one_mul := by
      rintro ⟨a, s⟩
      with_unfolding_all exact mk_eq.mpr ⟨1, by simp only [one_mul, mul_one, one_smul]⟩
    mul_one := by
      rintro ⟨a, s⟩
      with_unfolding_all exact mk_eq.mpr ⟨1, by simp only [mul_one, one_smul, one_mul]⟩
    mul_assoc := by with_unfolding_all
      rintro ⟨a₁, s₁⟩ ⟨a₂, s₂⟩ ⟨a₃, s₃⟩
      apply mk_eq.mpr _
      use 1
      simp only [one_mul, smul_smul, ← mul_assoc, mul_right_comm] }

set_option backward.isDefEq.respectTransparency false in
/-
**LocalizedModule.example_oreLocalizationInstMonoid_eq_localizedModuleInstMonoid
** 是 Mathlib 中的一个引理，位于命名空间 `LocalizedModule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma example_oreLocalizationInstMonoid_eq_localizedModuleInstMonoid :
    OreLocalization.instMonoid = LocalizedModule.instMonoid (A := R) (S := S) := by
  with_reducible_and_instances rfl

/-- A variant of `mk_mul_mk` that is `rfl` but has a stranger multiplication order. -/
/-
**LocalizedModule.mk_mul_mk'** 是 Mathlib 中的一个定理，位于命名空间 `LocalizedModule`。
形式化陈述：mk_mul_mk' {A : Type*} [Semiring A] [Algebra R A] {a₁ a₂ : A} {s₁ s₂ : S} 
: mk a₁ s₁ * mk a₂ s₂ = mk (a₁ * a₂) (s₂ * s₁)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A variant of `mk_mul_mk` that is `rfl` but has a stranger multiplication order.
-/
theorem mk_mul_mk' {A : Type*} [Semiring A] [Algebra R A] {a₁ a₂ : A} {s₁ s₂ : S} :
    mk a₁ s₁ * mk a₂ s₂ = mk (a₁ * a₂) (s₂ * s₁) := rfl
/-
**LocalizedModule.mk_mul_mk** 是 Mathlib 中的一个定理，位于命名空间 `LocalizedModule`。
形式化陈述：mk_mul_mk {A : Type*} [Semiring A] [Algebra R A] {a₁ a₂ : A} {s₁ s₂ : S} :
 mk a₁ s₁ * mk a₂ s₂ = mk (a₁ * a₂) (s₁ * s₂)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LocalizedModule.mk_mul_mk'`：mk_mul_mk' {A : Type*} [Semiring A] [Algebra
 R A] {a₁ a₂ : A} {s₁ s₂ : S} : mk a₁ s₁ * mk a₂ s₂ = mk (a₁ * a₂) (s₂ * s₁)
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem mk_mul_mk {A : Type*} [Semiring A] [Algebra R A] {a₁ a₂ : A} {s₁ s₂ : S} :
    mk a₁ s₁ * mk a₂ s₂ = mk (a₁ * a₂) (s₁ * s₂) := by rw [mk_mul_mk', mul_comm s₁ s₂]
/-
**LocalizedModule.mk_pow** 是 Mathlib 中的一个定理，位于命名空间 `LocalizedModule`。
形式化陈述：mk_pow {A : Type*} [Semiring A] [Algebra R A] {S : Submonoid R} (n : Nat) 
(a : A) (s : S) : mk a s ^ n = mk (a ^ n) (s ^ n)
参数：n : Nat；a : A；s : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `OreLocalization.one_def`：∀ {R : Type u_1} [inst : Monoid R] {S : Submono
id R} [inst_1 : OreLocalization.OreSet S] {X : Type u_2}   [inst_2 : MulAction R
 X] [inst_3 :…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `LocalizedModule.mk_mul_mk`：mk_mul_mk {A : Type*} [Semiring A] [Algebra R
 A] {a₁ a₂ : A} {s₁ s₂ : S} : mk a₁ s₁ * mk a₂ s₂ = mk (a₁ * a₂) (s₁ * s₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mk_pow {A : Type*} [Semiring A] [Algebra R A] {S : Submonoid R} (n : ℕ) (a : A) (s : S) :
    mk a s ^ n = mk (a ^ n) (s ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero, pow_zero, OreLocalization.one_def]
  | succ n ih =>
    simp only [pow_succ', ih, LocalizedModule.mk_mul_mk]

-- For the instance on `Localization S`, we prefer `OreLocalization.instSemiring`.
-- They are defeq but Lean needs to unfold a bunch to verify it.
/-
**LocalizedModule.** 是 Mathlib 中的一个实例，位于命名空间 `LocalizedModule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 900) {A : Type*} [Semiring A] [Algebra R A] {S : Submonoid R} :
    Semiring (LocalizedModule S A) :=
  fast_instance%
  { __ := (inferInstance : AddCommMonoid (LocalizedModule S A))
    __ := (inferInstance : Monoid (LocalizedModule S A))
    left_distrib := by
      rintro ⟨a₁, s₁⟩ ⟨a₂, s₂⟩ ⟨a₃, s₃⟩
      change a₁ /ₒ s₁ * (a₂ /ₒ s₂ + a₃ /ₒ s₃) = a₁ /ₒ s₁ * (a₂ /ₒ s₂) + a₁ /ₒ s₁ * (a₃ /ₒ s₃)
      rw [← mk, ← mk, ← mk, mk_mul_mk, mk_mul_mk, mk_add_mk, mk_mul_mk, mk_add_mk]
      apply mk_eq.mpr _
      use 1
      simp only [← mul_assoc, mul_right_comm, mul_add, mul_smul_comm, smul_add, smul_smul, one_mul]
    right_distrib := by
      rintro ⟨a₁, s₁⟩ ⟨a₂, s₂⟩ ⟨a₃, s₃⟩
      change (a₁ /ₒ s₁ + a₂ /ₒ s₂) * (a₃ /ₒ s₃) = a₁ /ₒ s₁ * (a₃ /ₒ s₃) + a₂ /ₒ s₂ * (a₃ /ₒ s₃)
      rw [← mk, ← mk, ← mk, mk_mul_mk, mk_mul_mk, mk_add_mk, mk_mul_mk, mk_add_mk]
      apply mk_eq.mpr _
      use 1
      simp only [one_mul, smul_add, add_mul, smul_smul, ← mul_assoc, smul_mul_assoc,
        mul_right_comm]
    zero_mul := by with_unfolding_all
      rintro ⟨a, s⟩
      exact mk_eq.mpr ⟨1, by simp only [zero_mul, smul_zero]⟩
    mul_zero := by with_unfolding_all
      rintro ⟨a, s⟩
      exact mk_eq.mpr ⟨1, by simp only [mul_zero, smul_zero]⟩ }

-- For the instance on `Localization S`, we prefer `OreLocalization.instCommSemiring`.
-- They are defeq but Lean needs to unfold a bunch to verify it.
/-
**LocalizedModule.** 是 Mathlib 中的一个实例，位于命名空间 `LocalizedModule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 900) {A : Type*} [CommSemiring A] [Algebra R A] {S : Submonoid R} :
    CommSemiring (LocalizedModule S A) :=
  fast_instance%
  { __ := (inferInstance : Semiring (LocalizedModule S A))
    mul_comm := by
      rintro ⟨a₁, s₁⟩ ⟨a₂, s₂⟩
      exact mk_eq.mpr ⟨1, by simp only [one_smul, mul_comm]⟩ }

-- For the instance on `Localization S`, we prefer `OreLocalization.instRing`.
-- They are defeq but Lean needs to unfold a bunch to verify it.
/-
**LocalizedModule.** 是 Mathlib 中的一个实例，位于命名空间 `LocalizedModule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 900) {A : Type*} [Ring A] [Algebra R A] {S : Submonoid R} :
    Ring (LocalizedModule S A) :=
  fast_instance%
  { __ := (inferInstance : AddCommGroup (LocalizedModule S A))
    __ := (inferInstance : Semiring (LocalizedModule S A)) }

-- For the instance on `Localization S`, we prefer `OreLocalization.instCommRing`.
-- They are defeq but Lean needs to unfold a bunch to verify it.
/-
**LocalizedModule.** 是 Mathlib 中的一个实例，位于命名空间 `LocalizedModule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 900) {A : Type*} [CommRing A] [Algebra R A] {S : Submonoid R} :
    CommRing (LocalizedModule S A) :=
  fast_instance%
  { __ := (inferInstance : Ring (LocalizedModule S A))
    __ := (inferInstance : CommSemiring (LocalizedModule S A)) }

set_option backward.isDefEq.respectTransparency false in
/-
**LocalizedModule.example_oreLocalizationInstCommRing_eq_localizedModuleInstComm
Ring** 是 Mathlib 中的一个引理，位于命名空间 `LocalizedModule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma example_oreLocalizationInstCommRing_eq_localizedModuleInstCommRing
    {R : Type*} [CommRing R] {S : Submonoid R} :
    OreLocalization.instCommRing = (LocalizedModule.instCommRing : CommRing R[S⁻¹]) := by
  with_reducible_and_instances rfl
/-
**LocalizedModule.smul'_mk** 是 Mathlib 中的一个定理，位于命名空间 `LocalizedModule`。
形式化陈述：∀ {R : Type u} [inst : CommSemiring R] {S : Submonoid R} {M : Type v} [ins
t_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] {R₀ : Type u_3} [inst_3 : 
SMul R₀ R] [inst_4 : SMul R₀ M] [inst_5 : IsScalarTower R₀ R R]   [inst_6 : IsSc
alarTower R₀ R M] (r : R₀) (m : M) (s : ↥S), r • LocalizedModule.mk m s = Locali
zedModule.mk (r • m) s
参数：r : R₀；m : M；s : ↥S；r • m。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OreLocalization.smul_oreDiv`：smul_oreDiv (r : R) (x : X) (s : S) : r • (
x /ₒ s) = oreNum (r • 1) s • x /ₒ oreDenom (r • 1) s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem smul'_mk
    {R₀ : Type*} [SMul R₀ R] [SMul R₀ M] [IsScalarTower R₀ R R] [IsScalarTower R₀ R M]
    (r : R₀) (m : M) (s : S) :
    r • LocalizedModule.mk m s = LocalizedModule.mk (r • m) s := by
  rw [OreLocalization.smul_oreDiv]
  simp
/-
**LocalizedModule.prod_mk** 是 Mathlib 中的一个定理，位于命名空间 `LocalizedModule`。
形式化陈述：prod_mk {ι A : Type*} [CommSemiring A] [Algebra R A] {S : Submonoid R} (t 
: Finset ι) (a : ι -> A) (s : ι -> S) : ∏ i in t, mk (a i) (s i) = mk (∏ i in t,
 a i) (∏ i in t, s i)
参数：t : Finset ι；a : ι -> A；s : ι -> S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.cons_induction`：∀ {α : Type u_3} {motive : Finset α → Prop},   mo
tive ∅ → (∀ (a : α) (s : Finset α) (h : a ∉ s), motive s → motive (Finset.cons a
 s h)) → ∀ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OreLocalization.one_def`：∀ {R : Type u_1} [inst : Monoid R] {S : Submono
id R} [inst_1 : OreLocalization.OreSet S] {X : Type u_2}   [inst_2 : MulAction R
 X] [inst_3 :…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.prod_cons`：prod_cons (h : a ∉ s) : ∏ x in cons a s h, f x = f a *
 ∏ x in s, f x
· 使用定理 `LocalizedModule.mk_mul_mk`：mk_mul_mk {A : Type*} [Semiring A] [Algebra R
 A] {a₁ a₂ : A} {s₁ s₂ : S} : mk a₁ s₁ * mk a₂ s₂ = mk (a₁ * a₂) (s₁ * s₂)
-/
theorem prod_mk {ι A : Type*} [CommSemiring A] [Algebra R A] {S : Submonoid R}
    (t : Finset ι) (a : ι → A) (s : ι → S) :
    ∏ i ∈ t, mk (a i) (s i) = mk (∏ i ∈ t, a i) (∏ i ∈ t, s i) := by
  induction t using Finset.cons_induction <;> simp [OreLocalization.one_def, *, mk_mul_mk]

/-- If `IsLocalization S T`, then `M[S⁻¹]` has a `T`-action.
This should eventually be replaced with `IsLocalizedModule f N` and `SMul T N`. -/
/-
**LocalizedModule.smulOfIsLocalization** 是 Mathlib 中的一个缩写定义，位于命名空间 `LocalizedMod
ule`。
形式化陈述：smulOfIsLocalization : SMul T (LocalizedModule S M) where smul x p
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `IsLocalization S T`, then `M[S⁻¹]` has a `T`-action.
This should eventually be replaced with `IsLocalizedModule f N` and `SMul T N`.
-/
noncomputable abbrev smulOfIsLocalization : SMul T (LocalizedModule S M) where
  smul x p :=
    let a := IsLocalization.sec S x
    liftOn p (fun p ↦ mk (a.1 • p.1) (a.2 * p.2))
      (by
        rintro p p' ⟨s, h⟩
        refine mk_eq.mpr ⟨s, ?_⟩
        calc
          _ = a.2 • a.1 • s • p'.2 • p.1 := by
            simp_rw [Submonoid.smul_def, Submonoid.coe_mul, ← mul_smul]; ring_nf
          _ = a.2 • a.1 • s • p.2 • p'.1 := by rw [h]
          _ = s • (a.2 * p.2) • a.1 • p'.1 := by
            simp_rw [Submonoid.smul_def, ← mul_smul, Submonoid.coe_mul]; ring_nf)

attribute [local instance] smulOfIsLocalization
/-
**LocalizedModule.smul_def** 是 Mathlib 中的一个定理，位于命名空间 `LocalizedModule`。
形式化陈述：smul_def (x : T) (m : M) (s : S) : x • mk m s = mk ((IsLocalization.sec S 
x).1 • m) ((IsLocalization.sec S x).2 * s)
参数：x : T；m : M；s : S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_def (x : T) (m : M) (s : S) :
    x • mk m s = mk ((IsLocalization.sec S x).1 • m) ((IsLocalization.sec S x).2 * s) := rfl
/-
**LocalizedModule.mk'_smul_mk** 是 Mathlib 中的一个定理，位于命名空间 `LocalizedModule`。
形式化陈述：∀ {R : Type u} [inst : CommSemiring R] {S : Submonoid R} {M : Type v} [ins
t_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] (T : Type u_1) [inst_3 : C
ommSemiring T] [inst_4 : Algebra R T]   [inst_5 : IsLocalization S T] (r : R) (m
 : M) (s s' : ↥S),   IsLocalization.mk' T r s • LocalizedModule.mk m s' = Locali
zedModule.mk (r • m) (s * s')
参数：T : Type u_1；r : R；m : M；s s' : ↥S；r • m；s * s'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LocalizedModule.smul_def`：smul_def (x : T) (m : M) (s : S) : x • mk m s 
= mk ((IsLocalization.sec S x).1 • m) ((IsLocalization.sec S x).2 * s)
· 使用定理 `LocalizedModule.mk_eq`：mk_eq {m m' : M} {s s' : S} : mk m s = mk m' s' ↔
 exists u : S, u • s' • m = u • s • m'
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsLocalization.eq`：∀ {R : Type u_1} [inst : CommSemiring R] {M : Submono
id R} {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [inst_3 
: IsLoc…
· 使用定理 `IsLocalization.mk'_sec`：∀ {R : Type u_1} [inst : CommSemiring R] {M : Su
bmonoid R} (S : Type u_2) [inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [in
st_3 : IsLoc…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mk'_smul_mk (r : R) (m : M) (s s' : S) :
    IsLocalization.mk' T r s • mk m s' = mk (r • m) (s * s') := by
  rw [smul_def, mk_eq]
  obtain ⟨c, hc⟩ := IsLocalization.eq.mp <| IsLocalization.mk'_sec T (IsLocalization.mk' T r s)
  use c
  simp_rw [← mul_smul, Submonoid.smul_def, Submonoid.coe_mul, ← mul_smul, ← mul_assoc,
    mul_comm _ (s' : R), mul_assoc, hc]
/-
**LocalizedModule.mk_smul_mk** 是 Mathlib 中的一个定理，位于命名空间 `LocalizedModule`。
形式化陈述：mk_smul_mk (r : R) (m : M) (s t : S) : Localization.mk r s • mk m t = mk (
r • m) (s * t)
参数：r : R；m : M；s t : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `OreLocalization.oreDiv_smul_char`：oreDiv_smul_char (r₁ : R) (r₂ : X) (s₁
 s₂ : S) (r' : R) (s' : S) (huv : s' * r₁ = r' * s₂) : (r₁ /ₒ s₁) • (r₂ /ₒ s₂) =
 r' • r₂ /ₒ (s' * s₁)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem mk_smul_mk (r : R) (m : M) (s t : S) :
    Localization.mk r s • mk m t = mk (r • m) (s * t) :=
  (OreLocalization.oreDiv_smul_char _ _ _ _ _ _ (mul_comm _ _)).trans (by rw [mul_comm])
/-
**LocalizedModule.** 是 Mathlib 中的一个实例，位于命名空间 `LocalizedModule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMulCommClass T T' (LocalizedModule S M) where
  smul_comm t t' p := by
    induction p with | _ m s
    simp_rw [smul_def, smul_smul, mul_left_comm, mul_comm]

variable {T}

set_option backward.privateInPublic true in
/-
**LocalizedModule.one_smul_aux** 是 Mathlib 中的一个定理，位于命名空间 `LocalizedModule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem one_smul_aux (p : LocalizedModule S M) : (1 : T) • p = p := by
  induction p with | _ m s
  rw [show (1 : T) = IsLocalization.mk' T (1 : R) (1 : S) by rw [IsLocalization.mk'_one, map_one]]
  rw [mk'_smul_mk, one_smul, one_mul]

set_option backward.privateInPublic true in
/-
**LocalizedModule.mul_smul_aux** 是 Mathlib 中的一个定理，位于命名空间 `LocalizedModule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem mul_smul_aux (x y : T) (p : LocalizedModule S M) :
    (x * y) • p = x • y • p := by
  induction p with | _ m s
  rw [← IsLocalization.mk'_sec (M := S) T x, ← IsLocalization.mk'_sec (M := S) T y]
  simp_rw [← IsLocalization.mk'_mul, mk'_smul_mk, ← mul_smul, mul_assoc]

set_option backward.privateInPublic true in
/-
**LocalizedModule.smul_add_aux** 是 Mathlib 中的一个定理，位于命名空间 `LocalizedModule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem smul_add_aux (x : T) (p q : LocalizedModule S M) :
    x • (p + q) = x • p + x • q := by
  induction p with | _ m s
  induction q with | _ n t
  rw [smul_def, smul_def, mk_add_mk, mk_add_mk]
  rw [show x • _ = IsLocalization.mk' T _ _ • _ by rw [IsLocalization.mk'_sec (M := S) T]]
  rw [← IsLocalization.mk'_cancel _ _ (IsLocalization.sec S x).2, mk'_smul_mk]
  congr 1
  · simp only [Submonoid.smul_def, smul_add, ← mul_smul, Submonoid.coe_mul]; ring_nf
  · rw [mul_mul_mul_comm] -- ring does not work here

set_option backward.privateInPublic true in
/-
**LocalizedModule.smul_zero_aux** 是 Mathlib 中的一个定理，位于命名空间 `LocalizedModule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem smul_zero_aux (x : T) : x • (0 : LocalizedModule S M) = 0 := by
  conv => lhs; rw [← zero_mk 1, smul_def, smul_zero, zero_mk]

set_option backward.privateInPublic true in
/-
**LocalizedModule.add_smul_aux** 是 Mathlib 中的一个定理，位于命名空间 `LocalizedModule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem add_smul_aux (x y : T) (p : LocalizedModule S M) :
    (x + y) • p = x • p + y • p := by
  induction p with | _ m s
  rw [smul_def T x, smul_def T y, mk_add_mk, show (x + y) • _ = IsLocalization.mk' T _ _ • _ by
    rw [← IsLocalization.mk'_sec (M := S) T x, ← IsLocalization.mk'_sec (M := S) T y,
      ← IsLocalization.mk'_add, IsLocalization.mk'_cancel _ _ s], mk'_smul_mk, ← smul_assoc,
    ← smul_assoc, ← add_smul]
  congr 1
  · simp only [Submonoid.smul_def, Submonoid.coe_mul, smul_eq_mul]; ring_nf
  · rw [mul_mul_mul_comm, mul_assoc] -- ring does not work here

set_option backward.privateInPublic true in
/-
**LocalizedModule.zero_smul_aux** 是 Mathlib 中的一个定理，位于命名空间 `LocalizedModule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem zero_smul_aux (p : LocalizedModule S M) : (0 : T) • p = 0 := by
  induction p with | _ m s
  rw [show (0 : T) = IsLocalization.mk' T (0 : R) (1 : S) by rw [IsLocalization.mk'_zero],
    mk'_smul_mk, zero_smul, zero_mk]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- If `IsLocalization S T`, then `M[S⁻¹]` is a `T`-module.
This should eventually be replaced with `IsLocalizedModule f N` and `Module T N`. -/
/-
**LocalizedModule.moduleOfIsLocalization** 是 Mathlib 中的一个缩写定义，位于命名空间 `LocalizedM
odule`。
形式化陈述：moduleOfIsLocalization : Module T (LocalizedModule S M) where one_smul
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Algebra.Module.LocalizedModule.Basic.0.LocalizedModule.
mul_smul_aux`：∀ {R : Type u} [inst : CommSemiring R] {S : Submonoid R} {M : Type
 v} [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] {T : Type u_…
· 使用定理 `_private.Mathlib.Algebra.Module.LocalizedModule.Basic.0.LocalizedModule.
one_smul_aux`：∀ {R : Type u} [inst : CommSemiring R] {S : Submonoid R} {M : Type
 v} [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] {T : Type u_…
· 使用定理 `_private.Mathlib.Algebra.Module.LocalizedModule.Basic.0.LocalizedModule.
smul_zero_aux`：∀ {R : Type u} [inst : CommSemiring R] {S : Submonoid R} {M : Typ
e v} [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] {T : Type u_…
· 使用定理 `_private.Mathlib.Algebra.Module.LocalizedModule.Basic.0.LocalizedModule.
smul_add_aux`：∀ {R : Type u} [inst : CommSemiring R] {S : Submonoid R} {M : Type
 v} [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] {T : Type u_…
· 使用定理 `_private.Mathlib.Algebra.Module.LocalizedModule.Basic.0.LocalizedModule.
add_smul_aux`：∀ {R : Type u} [inst : CommSemiring R] {S : Submonoid R} {M : Type
 v} [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] {T : Type u_…
· 使用定理 `_private.Mathlib.Algebra.Module.LocalizedModule.Basic.0.LocalizedModule.
zero_smul_aux`：∀ {R : Type u} [inst : CommSemiring R] {S : Submonoid R} {M : Typ
e v} [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] {T : Type u_…

--- 原说明 ---
If `IsLocalization S T`, then `M[S⁻¹]` is a `T`-module.
This should eventually be replaced with `IsLocalizedModule f N` and `Module T N`
.
-/
noncomputable abbrev moduleOfIsLocalization : Module T (LocalizedModule S M) where
  one_smul := one_smul_aux
  mul_smul := mul_smul_aux
  smul_add := smul_add_aux
  smul_zero := smul_zero_aux
  add_smul := add_smul_aux
  zero_smul := zero_smul_aux

@[simp]
/-
**LocalizedModule.mk_cancel_common_left** 是 Mathlib 中的一个定理，位于命名空间 `LocalizedModu
le`。
形式化陈述：mk_cancel_common_left (s' s : S) (m : M) : mk (s' • m) (s' * s) = mk m s
参数：s' s : S；m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LocalizedModule.mk_eq`：mk_eq {m m' : M} {s s' : S} : mk m s = mk m' s' ↔
 exists u : S, u • s' • m = u • s • m'
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
-/
theorem mk_cancel_common_left (s' s : S) (m : M) : mk (s' • m) (s' * s) = mk m s :=
  mk_eq.mpr
    ⟨1, by
      simp only [mul_smul, one_smul]
      rw [smul_comm]⟩

@[simp]
/-
**LocalizedModule.mk_cancel** 是 Mathlib 中的一个定理，位于命名空间 `LocalizedModule`。
形式化陈述：mk_cancel (s : S) (m : M) : mk (s • m) s = mk m 1
参数：s : S；m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LocalizedModule.mk_eq`：mk_eq {m m' : M} {s s' : S} : mk m s = mk m' s' ↔
 exists u : S, u • s' • m = u • s • m'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mk_cancel (s : S) (m : M) : mk (s • m) s = mk m 1 :=
  mk_eq.mpr ⟨1, by simp⟩

@[simp]
/-
**LocalizedModule.mk_cancel_common_right** 是 Mathlib 中的一个定理，位于命名空间 `LocalizedMod
ule`。
形式化陈述：mk_cancel_common_right (s s' : S) (m : M) : mk (s' • m) (s * s') = mk m s
参数：s s' : S；m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LocalizedModule.mk_eq`：mk_eq {m m' : M} {s s' : S} : mk m s = mk m' s' ↔
 exists u : S, u • s' • m = u • s • m'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mk_cancel_common_right (s s' : S) (m : M) : mk (s' • m) (s * s') = mk m s :=
  mk_eq.mpr ⟨1, by simp [mul_smul]⟩
/-
**LocalizedModule.smul_eq_iff_of_mem** 是 Mathlib 中的一个引理，位于命名空间 `LocalizedModule`
。
形式化陈述：smul_eq_iff_of_mem (r : R) (hr : r in S) (x y : LocalizedModule S M) : r •
 x = y ↔ x = Localization.mk 1 ⟨r, hr⟩ • y
参数：r : R；hr : r in S；x y : LocalizedModule S M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LocalizedModule.induction_on`：induction_on {β : LocalizedModule S M -> P
rop} (h : forall (m : M) (s : S), β (mk m s)) : forall x : LocalizedModule S M, 
β x
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LocalizedModule.smul'_mk`：∀ {R : Type u} [inst : CommSemiring R] {S : Su
bmonoid R} {M : Type v} [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M
] {R₀ : Type u…
· 使用定理 `LocalizedModule.mk_smul_mk`：mk_smul_mk (r : R) (m : M) (s t : S) : Local
ization.mk r s • mk m t = mk (r • m) (s * t)
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `LocalizedModule.mk_eq`：mk_eq {m m' : M} {s s' : S} : mk m s = mk m' s' ↔
 exists u : S, u • s' • m = u • s • m'
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Submonoid.mk_smul`：mk_smul (g : M') (hg : g in S) (a : α) : (⟨g, hg⟩ : S
) • a = g • a
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Submonoid.smul_def`：∀ {M' : Type u_1} {α : Type u_2} [inst : MulOneClass
 M'] [inst_1 : SMul M' α] {S : Submonoid M'} (g : ↥S) (a : α),   g • a = ↑g • a
-/
lemma smul_eq_iff_of_mem
    (r : R) (hr : r ∈ S) (x y : LocalizedModule S M) :
    r • x = y ↔ x = Localization.mk 1 ⟨r, hr⟩ • y := by
  induction x using induction_on with
  | h m s =>
    induction y using induction_on with
    | h n t =>
      rw [smul'_mk, mk_smul_mk, one_smul, mk_eq, mk_eq]
      simp only [Subtype.exists, Submonoid.mk_smul, exists_prop]
      fconstructor
      · rintro ⟨a, ha, eq1⟩
        refine ⟨a, ha, ?_⟩
        rw [mul_smul, ← eq1, Submonoid.mk_smul, smul_comm r t]
      · rintro ⟨a, ha, eq1⟩
        refine ⟨a, ha, ?_⟩
        rw [← eq1, mul_comm, mul_smul, Submonoid.mk_smul, Submonoid.smul_def, Submonoid.mk_smul]
/-
**LocalizedModule.eq_zero_of_smul_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `LocalizedMo
dule`。
形式化陈述：eq_zero_of_smul_eq_zero (r : R) (hr : r in S) (x : LocalizedModule S M) (h
x : r • x = 0) : x = 0
参数：r : R；hr : r in S；x : LocalizedModule S M；hx : r • x = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LocalizedModule.smul_eq_iff_of_mem`：smul_eq_iff_of_mem (r : R) (hr : r i
n S) (x y : LocalizedModule S M) : r • x = y ↔ x = Localization.mk 1 ⟨r, hr⟩ • y
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
-/
lemma eq_zero_of_smul_eq_zero
    (r : R) (hr : r ∈ S) (x : LocalizedModule S M) (hx : r • x = 0) : x = 0 := by
  rw [smul_eq_iff_of_mem (hr := hr)] at hx
  rw [hx, smul_zero]
/-
**LocalizedModule.smul'_mul** 是 Mathlib 中的一个定理，位于命名空间 `LocalizedModule`。
形式化陈述：∀ {R : Type u} [inst : CommSemiring R] {S : Submonoid R} {T : Type u_1} [i
nst_1 : CommSemiring T] [inst_2 : Algebra R T]   [inst_3 : IsLocalization S T] {
A : Type u_3} [inst_4 : Semiring A] [inst_5 : Algebra R A] (x : T)   (p₁ p₂ : Lo
calizedModule S A), x • p₁ * p₂ = x • (p₁ * p₂)
参数：x : T；p₁ p₂ : LocalizedModule S A；p₁ * p₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LocalizedModule.induction_on₂`：induction_on₂ {β : LocalizedModule S M ->
 LocalizedModule S M -> Prop} (h : forall (m m' : M) (s s' : S), β (mk m s) (mk 
m' s')) : forall x …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LocalizedModule.mk_mul_mk`：mk_mul_mk {A : Type*} [Semiring A] [Algebra R
 A] {a₁ a₂ : A} {s₁ s₂ : S} : mk a₁ s₁ * mk a₂ s₂ = mk (a₁ * a₂) (s₁ * s₂)
· 使用定理 `LocalizedModule.smul_def`：smul_def (x : T) (m : M) (s : S) : x • mk m s 
= mk ((IsLocalization.sec S x).1 • m) ((IsLocalization.sec S x).2 * s)
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用引理 `smul_mul_assoc`：smul_mul_assoc [Mul β] [SMul α β] [IsScalarTower α β β] 
(r : α) (x y : β) : r • x * y = r • (x * y)
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
theorem smul'_mul {A : Type*} [Semiring A] [Algebra R A] (x : T) (p₁ p₂ : LocalizedModule S A) :
    x • p₁ * p₂ = x • (p₁ * p₂) := by
  induction p₁, p₂ using induction_on₂ with | _ a₁ s₁ a₂ s₂ => _
  rw [mk_mul_mk, smul_def, smul_def, mk_mul_mk, mul_assoc, smul_mul_assoc]
/-
**LocalizedModule.mul_smul'** 是 Mathlib 中的一个定理，位于命名空间 `LocalizedModule`。
形式化陈述：mul_smul' {A : Type*} [Semiring A] [Algebra R A] (x : T) (p₁ p₂ : Localize
dModule S A) : p₁ * x • p₂ = x • (p₁ * p₂)
参数：x : T；p₁ p₂ : LocalizedModule S A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LocalizedModule.induction_on₂`：induction_on₂ {β : LocalizedModule S M ->
 LocalizedModule S M -> Prop} (h : forall (m m' : M) (s s' : S), β (mk m s) (mk 
m' s')) : forall x …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LocalizedModule.smul_def`：smul_def (x : T) (m : M) (s : S) : x • mk m s 
= mk ((IsLocalization.sec S x).1 • m) ((IsLocalization.sec S x).2 * s)
· 使用定理 `LocalizedModule.mk_mul_mk`：mk_mul_mk {A : Type*} [Semiring A] [Algebra R
 A] {a₁ a₂ : A} {s₁ s₂ : S} : mk a₁ s₁ * mk a₂ s₂ = mk (a₁ * a₂) (s₁ * s₂)
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
· 使用引理 `mul_smul_comm`：mul_smul_comm [Mul β] [SMul α β] [SMulCommClass α β β] (s
 : α) (x y : β) : x * s • y = s • (x * y)
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
theorem mul_smul' {A : Type*} [Semiring A] [Algebra R A] (x : T) (p₁ p₂ : LocalizedModule S A) :
    p₁ * x • p₂ = x • (p₁ * p₂) := by
  induction p₁, p₂ using induction_on₂ with | _ a₁ s₁ a₂ s₂ => _
  rw [smul_def, mk_mul_mk, mk_mul_mk, smul_def, mul_left_comm, mul_smul_comm]

variable (T)

attribute [local instance] moduleOfIsLocalization in
/-- If `IsLocalization S T`, then `A[S⁻¹]` is a `T`-algebra.
This should eventually be replaced with `IsLocalizedModule f N` and `Algebra T N`. -/
/-
**LocalizedModule.algebraOfIsLocalization** 是 Mathlib 中的一个缩写定义，位于命名空间 `Localized
Module`。
形式化陈述：algebraOfIsLocalization {A : Type*} [Semiring A] [Algebra R A] : Algebra T
 (LocalizedModule S A)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `LocalizedModule.smul'_mul`：∀ {R : Type u} [inst : CommSemiring R] {S : S
ubmonoid R} {T : Type u_1} [inst_1 : CommSemiring T] [inst_2 : Algebra R T]   [i
nst_3 : IsLocal…
· 使用定理 `LocalizedModule.mul_smul'`：mul_smul' {A : Type*} [Semiring A] [Algebra R
 A] (x : T) (p₁ p₂ : LocalizedModule S A) : p₁ * x • p₂ = x • (p₁ * p₂)

--- 原说明 ---
If `IsLocalization S T`, then `A[S⁻¹]` is a `T`-algebra.
This should eventually be replaced with `IsLocalizedModule f N` and `Algebra T N
`.
-/
noncomputable abbrev algebraOfIsLocalization {A : Type*} [Semiring A] [Algebra R A] :
    Algebra T (LocalizedModule S A) :=
  Algebra.ofModule smul'_mul mul_smul'

attribute [local instance] algebraOfIsLocalization
/-
**LocalizedModule.algebraMap_mk'** 是 Mathlib 中的一个定理，位于命名空间 `LocalizedModule`。
形式化陈述：algebraMap_mk' {A : Type*} [Semiring A] [Algebra R A] (a : R) (s : S) : al
gebraMap _ _ (IsLocalization.mk' T a s) = mk (algebraMap R A a) s
参数：a : R；s : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.algebraMap_eq_smul_one`：algebraMap_eq_smul_one (r : R) : algebra
Map R A r = r • (1 : A)
· 使用定理 `LocalizedModule.mk'_smul_mk`：∀ {R : Type u} [inst : CommSemiring R] {S :
 Submonoid R} {M : Type v} [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module 
R M] (T : Type u_…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem algebraMap_mk' {A : Type*} [Semiring A] [Algebra R A] (a : R) (s : S) :
    algebraMap _ _ (IsLocalization.mk' T a s) = mk (algebraMap R A a) s := by
  with_unfolding_all
  rw [Algebra.algebraMap_eq_smul_one]
  change _ • mk _ _ = _
  rw [mk'_smul_mk, Algebra.algebraMap_eq_smul_one, mul_one]
/-
**LocalizedModule.algebraMap_mk** 是 Mathlib 中的一个定理，位于命名空间 `LocalizedModule`。
形式化陈述：algebraMap_mk {A : Type*} [Semiring A] [Algebra R A] (a : R) (s : S) : alg
ebraMap _ _ (Localization.mk a s) = mk (algebraMap R A a) s
参数：a : R；s : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Localization.mk_eq_mk'`：mk_eq_mk'_apply (x y) : mk x y = IsLocalization.
mk' (Localization M) x y
· 使用定理 `LocalizedModule.algebraMap_mk'`：algebraMap_mk' {A : Type*} [Semiring A] 
[Algebra R A] (a : R) (s : S) : algebraMap _ _ (IsLocalization.mk' T a s) = mk (
algebraMap R A a) s
-/
theorem algebraMap_mk {A : Type*} [Semiring A] [Algebra R A] (a : R) (s : S) :
    algebraMap _ _ (Localization.mk a s) = mk (algebraMap R A a) s := by
  rw [Localization.mk_eq_mk']
  exact algebraMap_mk' ..
/-
**LocalizedModule.** 是 Mathlib 中的一个实例，位于命名空间 `LocalizedModule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsScalarTower R T (LocalizedModule S M) where
  smul_assoc r x p := by
    induction p with | _ m s
    rw [← IsLocalization.mk'_sec (M := S) T x, IsLocalization.smul_mk', mk'_smul_mk, mk'_smul_mk,
      smul'_mk, mul_smul]

/-- The ring homomorphism from `R` to `R[S⁻¹]`, mapping `r : R` to the fraction `r /ₒ 1`. -/
/-
**LocalizedModule.numeratorRingHom** 是 Mathlib 中的一个缩写定义，位于命名空间 `LocalizedModule`
。
形式化陈述：numeratorRingHom {A : Type*} [Semiring A] [Algebra R A] : A ->+* A[S⁻¹] wh
ere toFun r
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The ring homomorphism from `R` to `R[S⁻¹]`, mapping `r : R` to the fraction `r /
ₒ 1`.
-/
abbrev numeratorRingHom {A : Type*} [Semiring A] [Algebra R A] : A →+* A[S⁻¹] where
  toFun r := mk r 1
  map_one' := by simp [OreLocalization.one_def]
  map_mul' := by simp [mk_mul_mk]
  map_zero' := by simp
  map_add' := by simp
/-
**LocalizedModule.** 是 Mathlib 中的一个实例，位于命名空间 `LocalizedModule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance (priority := 900) algebra' {A : Type*} [Semiring A] [Algebra R A] :
    Algebra R (LocalizedModule S A) where
  algebraMap := numeratorRingHom.comp (algebraMap R A)
  commutes' r x := by
    induction x using induction_on with | _ a s => _
    simp only [RingHom.coe_comp, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
      Function.comp_apply]
    rw [mk_mul_mk, mk_mul_mk, mul_comm, Algebra.commutes]
  smul_def' r x := by
    induction x using induction_on with | _ a s => _
    simp only [RingHom.coe_comp, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
      Function.comp_apply]
    rw [mk_mul_mk, smul'_mk, Algebra.smul_def, one_mul]

set_option backward.isDefEq.respectTransparency false in
/-
**LocalizedModule.example_oreLocalizationInstAlgebra_eq_localizedModuleAlgebra'*
* 是 Mathlib 中的一个引理，位于命名空间 `LocalizedModule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma example_oreLocalizationInstAlgebra_eq_localizedModuleAlgebra' :
    OreLocalization.instAlgebra = (algebra' : Algebra R (LocalizedModule S R)) := by
  with_reducible_and_instances rfl

section

variable (S M)

/-- The function `m ↦ m / 1` as an `R`-linear map.
-/
@[simps]
/-
**LocalizedModule.mkLinearMap** 是 Mathlib 中的一个定义，位于命名空间 `LocalizedModule`。
形式化陈述：mkLinearMap : M ->ₗ[R] LocalizedModule S M where toFun m
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The function `m ↦ m / 1` as an `R`-linear map.
-/
noncomputable def mkLinearMap : M →ₗ[R] LocalizedModule S M where
  toFun m := mk m 1
  map_add' x y := by simp
  map_smul' _ _ := by simp [mk, OreLocalization.smul_oreDiv]

end

/-- For any `s : S`, there is an `R`-linear map given by `a/b ↦ a/(b*s)`.
-/
@[simps]
/-
**LocalizedModule.divBy** 是 Mathlib 中的一个定义，位于命名空间 `LocalizedModule`。
形式化陈述：divBy (s : S) : LocalizedModule S M ->ₗ[R] LocalizedModule S M where toFun
 p
参数：s : S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For any `s : S`, there is an `R`-linear map given by `a/b ↦ a/(b*s)`.
-/
noncomputable def divBy (s : S) : LocalizedModule S M →ₗ[R] LocalizedModule S M where
  toFun p :=
    p.liftOn (fun p => mk p.1 (p.2 * s)) fun ⟨a, b⟩ ⟨a', b'⟩ ⟨c, eq1⟩ =>
      mk_eq.mpr ⟨c, by rw [mul_smul, mul_smul, smul_comm _ s, smul_comm _ s, eq1, smul_comm _ s,
        smul_comm _ s]⟩
  map_add' x y := by
    refine x.induction_on₂ ?_ y
    intro m₁ m₂ t₁ t₂
    simp_rw [mk_add_mk, LocalizedModule.liftOn_mk, mk_add_mk, mul_smul, mul_comm _ s, mul_assoc,
      smul_comm _ s, ← smul_add, mul_left_comm s t₁ t₂, mk_cancel_common_left s]
  map_smul' r x := by
    refine x.induction_on (fun _ _ ↦ ?_)
    simp_rw [smul'_mk, liftOn_mk, smul'_mk]
    congr!
/-
**LocalizedModule.divBy_mul_by** 是 Mathlib 中的一个定理，位于命名空间 `LocalizedModule`。
形式化陈述：divBy_mul_by (s : S) (p : LocalizedModule S M) : divBy s (algebraMap R (Mo
dule.End R (LocalizedModule S M)) s p) = p
参数：s : S；p : LocalizedModule S M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LocalizedModule.induction_on`：induction_on {β : LocalizedModule S M -> P
rop} (h : forall (m : M) (s : S), β (mk m s)) : forall x : LocalizedModule S M, 
β x
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `OreLocalization.instSMulCommClass`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.algebraMap_end_apply`：algebraMap_end_apply (a : R) (m : M) : alge
braMap R (End S M) a m = a • m
· 使用定理 `LocalizedModule.divBy_apply`：∀ {R : Type u} [inst : CommSemiring R] {S :
 Submonoid R} {M : Type v} [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module 
R M] (s : ↥S) (p …
· 使用定理 `LocalizedModule.smul'_mk`：∀ {R : Type u} [inst : CommSemiring R] {S : Su
bmonoid R} {M : Type v} [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M
] {R₀ : Type u…
· 使用定理 `LocalizedModule.liftOn_mk`：liftOn_mk {α : Type*} {f : M × S -> α} (wd : 
forall (p p' : M × S), p ≈ p' -> f p = f p') (m : M) (s : S) : liftOn (mk m s) f
 wd = f ⟨m, s⟩
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submonoid.smul_def`：∀ {M' : Type u_1} {α : Type u_2} [inst : MulOneClass
 M'] [inst_1 : SMul M' α] {S : Submonoid M'} (g : ↥S) (a : α),   g • a = ↑g • a
· 使用定理 `LocalizedModule.mk_cancel_common_right`：mk_cancel_common_right (s s' : S
) (m : M) : mk (s' • m) (s * s') = mk m s
-/
theorem divBy_mul_by (s : S) (p : LocalizedModule S M) :
    divBy s (algebraMap R (Module.End R (LocalizedModule S M)) s p) = p :=
  p.induction_on fun m t => by
    rw [Module.algebraMap_end_apply, divBy_apply, smul'_mk, liftOn_mk,
      ← Submonoid.smul_def, mk_cancel_common_right _ s]
/-
**LocalizedModule.mul_by_divBy** 是 Mathlib 中的一个定理，位于命名空间 `LocalizedModule`。
形式化陈述：mul_by_divBy (s : S) (p : LocalizedModule S M) : algebraMap R (Module.End 
R (LocalizedModule S M)) s (divBy s p) = p
参数：s : S；p : LocalizedModule S M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LocalizedModule.induction_on`：induction_on {β : LocalizedModule S M -> P
rop} (h : forall (m : M) (s : S), β (mk m s)) : forall x : LocalizedModule S M, 
β x
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `OreLocalization.instSMulCommClass`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LocalizedModule.divBy_apply`：∀ {R : Type u} [inst : CommSemiring R] {S :
 Submonoid R} {M : Type v} [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module 
R M] (s : ↥S) (p …
· 使用定理 `Module.algebraMap_end_apply`：algebraMap_end_apply (a : R) (m : M) : alge
braMap R (End S M) a m = a • m
· 使用定理 `LocalizedModule.liftOn_mk`：liftOn_mk {α : Type*} {f : M × S -> α} (wd : 
forall (p p' : M × S), p ≈ p' -> f p = f p') (m : M) (s : S) : liftOn (mk m s) f
 wd = f ⟨m, s⟩
· 使用定理 `LocalizedModule.smul'_mk`：∀ {R : Type u} [inst : CommSemiring R] {S : Su
bmonoid R} {M : Type v} [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M
] {R₀ : Type u…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submonoid.smul_def`：∀ {M' : Type u_1} {α : Type u_2} [inst : MulOneClass
 M'] [inst_1 : SMul M' α] {S : Submonoid M'} (g : ↥S) (a : α),   g • a = ↑g • a
· 使用定理 `LocalizedModule.mk_cancel_common_right`：mk_cancel_common_right (s s' : S
) (m : M) : mk (s' • m) (s * s') = mk m s
-/
theorem mul_by_divBy (s : S) (p : LocalizedModule S M) :
    algebraMap R (Module.End R (LocalizedModule S M)) s (divBy s p) = p :=
  p.induction_on fun m t => by
    rw [divBy_apply, Module.algebraMap_end_apply, LocalizedModule.liftOn_mk, smul'_mk,
      ← Submonoid.smul_def, mk_cancel_common_right _ s]

end

end LocalizedModule

section IsLocalizedModule

universe u v

variable {R : Type*} [CommSemiring R] (S : Submonoid R)
variable {M M' M'' : Type*} [AddCommMonoid M] [AddCommMonoid M'] [AddCommMonoid M'']
variable {A : Type*} [CommSemiring A] [Algebra R A] [Module A M'] [IsLocalization S A]
variable [Module R M] [Module R M'] [Module R M''] [IsScalarTower R A M']
variable (f : M →ₗ[R] M') (g : M →ₗ[R] M'')

/-- The characteristic predicate for localized module.
`IsLocalizedModule S f` describes that `f : M ⟶ M'` is the localization map identifying `M'` as
`LocalizedModule S M`.
-/
/-
**IsLocalizedModule** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{R : Type u_1} →   [inst : CommSemiring R] →     {M : Type u_2} →       {M
' : Type u_3} →         [inst_1 : AddCommMonoid M] →           [inst_2 : AddComm
Monoid M'] →             [inst_3 : _root_.Module R M] → [inst_4 : _root_.Module 
R M'] → Submonoid R → (M →ₗ[R] M') → Prop
参数：M →ₗ[R] M'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The characteristic predicate for localized module.
`IsLocalizedModule S f` describes that `f : M ⟶ M'` is the localization map iden
tifying `M'` as
`LocalizedModule S M`.
-/
@[mk_iff] class IsLocalizedModule (S : Submonoid R) (f : M →ₗ[R] M') : Prop where
  map_units : ∀ x : S, IsUnit (algebraMap R (Module.End R M') x)
  surj (S f) : ∀ y : M', ∃ x : M × S, x.2 • y = f x.1
  exists_of_eq : ∀ {x₁ x₂}, f x₁ = f x₂ → ∃ c : S, c • x₁ = c • x₂

attribute [nolint docBlame] IsLocalizedModule.map_units IsLocalizedModule.surj
  IsLocalizedModule.exists_of_eq
/-
**IsLocalizedModule.eq_iff_exists** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsLocalizedModule.eq_iff_exists [IsLocalizedModule S f] {x₁ x₂} : f x₁ = f
 x₂ ↔ exists c : S, c • x₁ = c • x₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalizedModule.exists_of_eq`：∀ {R : Type u_1} {inst : CommSemiring R}
 {M : Type u_2} {M' : Type u_3} {inst_1 : AddCommMonoid M}   {inst_2 : AddCommMo
noid M'} {inst_3 : _…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Module.End.isUnit_iff`：∀ {R : Type u_1} {M : Type u_5} [inst : Semiring 
R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (f : Module.End R M
), IsUnit f…
· 使用定理 `IsLocalizedModule.map_units`：∀ {R : Type u_1} {inst : CommSemiring R} {M
 : Type u_2} {M' : Type u_3} {inst_1 : AddCommMonoid M}   {inst_2 : AddCommMonoi
d M'} {inst_3 : _…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.map_smul_of_tower`：map_smul_of_tower [CompatibleSMul M M₂ R S]
 (fₗ : M ->ₗ[S] M₂) (c : R) (x : M) : fₗ (c • x) = c • fₗ x
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma IsLocalizedModule.eq_iff_exists [IsLocalizedModule S f] {x₁ x₂} :
    f x₁ = f x₂ ↔ ∃ c : S, c • x₁ = c • x₂ :=
  Iff.intro exists_of_eq fun ⟨c, h⟩ ↦ by
    apply_fun f at h
    simp_rw [f.map_smul_of_tower, Submonoid.smul_def, ← Module.algebraMap_end_apply R R] at h
    exact ((Module.End.isUnit_iff _).mp <| map_units f c).1 h
/-
**IsLocalizedModule.injective_iff_isRegular** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsLocalizedModule.injective_iff_isRegular [IsLocalizedModule S f] : Functi
on.Injective f ↔ forall c : S, IsSMulRegular M c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `IsLocalizedModule.eq_iff_exists`：IsLocalizedModule.eq_iff_exists [IsLoca
lizedModule S f] {x₁ x₂} : f x₁ = f x₂ ↔ exists c : S, c • x₁ = c • x₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma IsLocalizedModule.injective_iff_isRegular [IsLocalizedModule S f] :
    Function.Injective f ↔ ∀ c : S, IsSMulRegular M c := by
  simp_rw [IsSMulRegular, Function.Injective, eq_iff_exists S, exists_imp, forall_comm (α := S)]

set_option backward.isDefEq.respectTransparency false in
/-
**IsLocalizedModule.of_linearEquiv** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：IsLocalizedModule.of_linearEquiv (e : M' ≃ₗ[R] M'') [hf : IsLocalizedModul
e S f] : IsLocalizedModule S (e ∘ₗ f : M ->ₗ[R] M'') where map_units s
参数：e : M' ≃ₗ[R] M''。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `LinearEquiv.apply_symm_apply`：apply_symm_apply (c : M₂) : e (e.symm c) =
 c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Module.End.isUnit_iff`：∀ {R : Type u_1} {M : Type u_5} [inst : Semiring 
R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (f : Module.End R M
), IsUnit f…
· 使用定理 `LinearMap.coe_comp`：coe_comp : (f.comp g : M₁ -> M₃) = f ∘ g
· 使用定理 `LinearEquiv.coe_coe`：coe_coe : ⇑(e : M ->ₛₗ[σ] M₂) = e
· 使用定理 `EquivLike.comp_bijective`：comp_bijective (f : α -> β) (e : F) : Function
.Bijective (e ∘ f) ↔ Function.Bijective f
· 使用定理 `EquivLike.bijective_comp`：bijective_comp (e : E) (f : β -> γ) : Function
.Bijective (f ∘ e) ↔ Function.Bijective f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsLocalizedModule.map_units`：∀ {R : Type u_1} {inst : CommSemiring R} {M
 : Type u_2} {M' : Type u_3} {inst_1 : AddCommMonoid M}   {inst_2 : AddCommMonoi
d M'} {inst_3 : _…
· 使用定理 `IsLocalizedModule.surj`：∀ {R : Type u_1} {inst : CommSemiring R} {M : Ty
pe u_2} {M' : Type u_3} {inst_1 : AddCommMonoid M}   {inst_2 : AddCommMonoid M'}
 {inst_3 : _…
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearEquiv.congr_arg`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用定理 `Submonoid.smul_def`：∀ {M' : Type u_1} {α : Type u_2} [inst : MulOneClass
 M'] [inst_1 : SMul M' α] {S : Submonoid M'} (g : ↥S) (a : α),   g • a = ↑g • a
· 使用定理 `IsLocalizedModule.exists_of_eq`：∀ {R : Type u_1} {inst : CommSemiring R}
 {M : Type u_2} {M' : Type u_3} {inst_1 : AddCommMonoid M}   {inst_2 : AddCommMo
noid M'} {inst_3 : _…
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
-/
instance IsLocalizedModule.of_linearEquiv (e : M' ≃ₗ[R] M'') [hf : IsLocalizedModule S f] :
    IsLocalizedModule S (e ∘ₗ f : M →ₗ[R] M'') where
  map_units s := by
    rw [show algebraMap R (Module.End R M'') s = e ∘ₗ (algebraMap R (Module.End R M') s) ∘ₗ e.symm
      by ext; simp, Module.End.isUnit_iff, LinearMap.coe_comp, LinearMap.coe_comp,
      LinearEquiv.coe_coe, LinearEquiv.coe_coe, EquivLike.comp_bijective, EquivLike.bijective_comp]
    exact (Module.End.isUnit_iff _).mp <| hf.map_units s
  surj x := by
    obtain ⟨p, h⟩ := hf.surj (e.symm x)
    exact ⟨p, by rw [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, ← e.congr_arg h,
      Submonoid.smul_def, Submonoid.smul_def, map_smul, LinearEquiv.apply_symm_apply]⟩
  exists_of_eq h := by
    simp_rw [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      EmbeddingLike.apply_eq_iff_eq] at h
    exact hf.exists_of_eq h

set_option backward.isDefEq.respectTransparency false in
/-
**IsLocalizedModule.of_linearEquiv_right** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：IsLocalizedModule.of_linearEquiv_right (e : M'' ≃ₗ[R] M) [hf : IsLocalized
Module S f] : IsLocalizedModule S (f ∘ₗ e : M'' ->ₗ[R] M') where map_units s
参数：e : M'' ≃ₗ[R] M。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalizedModule.map_units`：∀ {R : Type u_1} {inst : CommSemiring R} {M
 : Type u_2} {M' : Type u_3} {inst_1 : AddCommMonoid M}   {inst_2 : AddCommMonoi
d M'} {inst_3 : _…
· 使用定理 `IsLocalizedModule.surj`：∀ {R : Type u_1} {inst : CommSemiring R} {M : Ty
pe u_2} {M' : Type u_3} {inst_1 : AddCommMonoid M}   {inst_2 : AddCommMonoid M'}
 {inst_3 : _…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.apply_symm_apply`：apply_symm_apply (c : M₂) : e (e.symm c) =
 c
· 使用定理 `IsLocalizedModule.exists_of_eq`：∀ {R : Type u_1} {inst : CommSemiring R}
 {M : Type u_2} {M' : Type u_3} {inst_1 : AddCommMonoid M}   {inst_2 : AddCommMo
noid M'} {inst_3 : _…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `LinearEquiv.symm_apply_apply`：symm_apply_apply (b : M) : e.symm (e b) = 
b
-/
instance IsLocalizedModule.of_linearEquiv_right (e : M'' ≃ₗ[R] M) [hf : IsLocalizedModule S f] :
    IsLocalizedModule S (f ∘ₗ e : M'' →ₗ[R] M') where
  map_units s := hf.map_units s
  surj x := by
    obtain ⟨⟨p, s⟩, h⟩ := hf.surj x
    exact ⟨⟨e.symm p, s⟩, by simpa using h⟩
  exists_of_eq h := by
    simp_rw [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply] at h
    obtain ⟨c, hc⟩ := hf.exists_of_eq h
    exact ⟨c, by simpa only [Submonoid.smul_def, map_smul, e.symm_apply_apply]
      using congr(e.symm $hc)⟩
/-
**IsLocalizedModule.comp_iff_of_bijective_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsLocalizedModule.comp_iff_of_bijective_left {f : M ->ₗ[R] M'} (e : M' ->ₗ
[R] M'') (he : Function.Bijective e) : IsLocalizedModule S (e ∘ₗ f) ↔ IsLocalize
dModule S f
参数：e : M' ->ₗ[R] M''；he : Function.Bijective e。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.ofBijective_symm_apply_apply`：ofBijective_symm_apply_apply [
RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂] {h} (x : M) : (ofBijective f h)
.symm (f x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma IsLocalizedModule.comp_iff_of_bijective_left {f : M →ₗ[R] M'} (e : M' →ₗ[R] M'')
    (he : Function.Bijective e) :
    IsLocalizedModule S (e ∘ₗ f) ↔ IsLocalizedModule S f := by
  refine ⟨fun h ↦ ?_, fun h ↦ .of_linearEquiv _ _ (.ofBijective _ he)⟩
  have : (LinearEquiv.ofBijective _ he).symm.toLinearMap ∘ₗ e ∘ₗ f = f := by ext; simp
  rw [← this]
  exact .of_linearEquiv _ _ _
/-
**IsLocalizedModule.comp_iff_of_bijective_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsLocalizedModule.comp_iff_of_bijective_right (e : M ->ₗ[R] M') {f : M' ->
ₗ[R] M''} (he : Function.Bijective e) : IsLocalizedModule S (f ∘ₗ e) ↔ IsLocaliz
edModule S f
参数：e : M ->ₗ[R] M'；he : Function.Bijective e。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.apply_ofBijective_symm_apply`：apply_ofBijective_symm_apply [
RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂] {h} (x : M₂) : f ((ofBijective 
f h).symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma IsLocalizedModule.comp_iff_of_bijective_right (e : M →ₗ[R] M') {f : M' →ₗ[R] M''}
    (he : Function.Bijective e) :
    IsLocalizedModule S (f ∘ₗ e) ↔ IsLocalizedModule S f := by
  refine ⟨fun h ↦ ?_, fun h ↦ .of_linearEquiv_right _ _ (.ofBijective _ he)⟩
  have : (f ∘ₗ e) ∘ₗ (LinearEquiv.ofBijective _ he).symm.toLinearMap = f := by ext; simp
  rw [← this]
  exact .of_linearEquiv_right _ _ _

variable (M) in
/-
**isLocalizedModule_id** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isLocalizedModule_id (R') [CommSemiring R'] [Algebra R R'] [IsLocalization
 S R'] [Module R' M] [IsScalarTower R R' M] : IsLocalizedModule S (.id : M ->ₗ[R
] M) where map_units s
参数：R'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgHom.commutes`：commutes (r : R) : φ (algebraMap R A r) = algebraMap R 
B r
· 使用定理 `IsUnit.map`：map [MonoidHomClass F M N] (f : F) {x : M} (h : IsUnit x) : 
IsUnit (f x)
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `IsLocalization.map_units`：map_units : forall y : M, IsUnit (algebraMap R
 S y)
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
lemma isLocalizedModule_id (R') [CommSemiring R'] [Algebra R R'] [IsLocalization S R'] [Module R' M]
    [IsScalarTower R R' M] : IsLocalizedModule S (.id : M →ₗ[R] M) where
  map_units s := by
    rw [← (Algebra.lsmul R (A := R') R M).commutes]; exact (IsLocalization.map_units R' s).map _
  surj m := ⟨(m, 1), one_smul _ _⟩
  exists_of_eq h := ⟨1, congr_arg _ h⟩

namespace LocalizedModule

/--
If `g` is a linear map `M → M''` such that all scalar multiplication by `s : S` is invertible, then
there is a linear map `LocalizedModule S M → M''`.
-/
/-
**LocalizedModule.lift'** 是 Mathlib 中的一个定义，位于命名空间 `LocalizedModule`。
形式化陈述：lift' (g : M ->ₗ[R] M'') (h : forall x : S, IsUnit (algebraMap R (Module.E
nd R M'') x)) : LocalizedModule S M -> M''
参数：g : M ->ₗ[R] M''；h : forall x : S, IsUnit (algebraMap R (Module.End R M'') x)
。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `g` is a linear map `M → M''` such that all scalar multiplication by `s : S` 
is invertible, then
there is a linear map `LocalizedModule S M → M''`.
-/
noncomputable def lift' (g : M →ₗ[R] M'')
    (h : ∀ x : S, IsUnit (algebraMap R (Module.End R M'') x)) : LocalizedModule S M → M'' :=
  fun m =>
  m.liftOn (fun p => (h p.2).unit⁻¹.val <| g p.1) fun ⟨m, s⟩ ⟨m', s'⟩ ⟨c, eq1⟩ => by
    dsimp only
    simp only [Submonoid.smul_def] at eq1
    rw [Module.End.algebraMap_isUnit_inv_apply_eq_iff, ← map_smul, eq_comm,
      Module.End.algebraMap_isUnit_inv_apply_eq_iff]
    have : c • s • g m' = c • s' • g m := by
      simp only [Submonoid.smul_def, ← g.map_smul, eq1]
    have : Function.Injective (h c).unit.inv := ((Module.End.isUnit_iff _).1 (by simp)).1
    apply_fun (h c).unit.inv
    rw [Units.inv_eq_val_inv, Module.End.algebraMap_isUnit_inv_apply_eq_iff, ←
      (h c).unit⁻¹.val.map_smul]
    symm
    rw [Module.End.algebraMap_isUnit_inv_apply_eq_iff, ← g.map_smul, ← g.map_smul, ← g.map_smul, ←
      g.map_smul, eq1]
/-
**LocalizedModule.lift'_mk** 是 Mathlib 中的一个定理，位于命名空间 `LocalizedModule`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] (S : Submonoid R) {M : Type u_2} 
{M'' : Type u_4} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid M''] [inst
_3 : _root_.Module R M] [inst_4 : _root_.Module R M''] (g : M →ₗ[R] M'')   (h : 
∀ (x : ↥S), IsUnit ((algebraMap R (Module.End R M'')) ↑x)) (m : M) (s : ↥S),   L
ocalizedModule.lift' S g h (LocalizedModule.mk m s) = ↑⋯.unit⁻¹ (g m)
参数：S : Submonoid R；g : M →ₗ[R] M''；h : ∀ (x : ↥S), IsUnit ((algebraMap R (Module
.End R M'')) ↑x)；m : M；s : ↥S；LocalizedModule.mk m s；g m。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lift'_mk (g : M →ₗ[R] M'') (h : ∀ x : S, IsUnit ((algebraMap R (Module.End R M'')) x))
    (m : M) (s : S) :
    LocalizedModule.lift' S g h (LocalizedModule.mk m s) = (h s).unit⁻¹.val (g m) :=
  rfl
/-
**LocalizedModule.lift'_add** 是 Mathlib 中的一个定理，位于命名空间 `LocalizedModule`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] (S : Submonoid R) {M : Type u_2} 
{M'' : Type u_4} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid M''] [inst
_3 : _root_.Module R M] [inst_4 : _root_.Module R M''] (g : M →ₗ[R] M'')   (h : 
∀ (x : ↥S), IsUnit ((algebraMap R (Module.End R M'')) ↑x)) (x y : LocalizedModul
e S M),   LocalizedModule.lift' S g h (x + y) = LocalizedModule.lift' S g h x + 
LocalizedModule.lift' S g h y
参数：S : Submonoid R；g : M →ₗ[R] M''；h : ∀ (x : ↥S), IsUnit ((algebraMap R (Module
.End R M'')) ↑x)；x y : LocalizedModule S M；x + y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LocalizedModule.induction_on₂`：induction_on₂ {β : LocalizedModule S M ->
 LocalizedModule S M -> Prop} (h : forall (m m' : M) (s s' : S), β (mk m s) (mk 
m' s')) : forall x …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LocalizedModule.mk_add_mk`：mk_add_mk {m1 m2 : M} {s1 s2 : S} : mk m1 s1 
+ mk m2 s2 = mk (s2 • m1 + s1 • m2) (s1 * s2)
· 使用定理 `LocalizedModule.lift'_mk`：∀ {R : Type u_1} [inst : CommSemiring R] (S : 
Submonoid R) {M : Type u_2} {M'' : Type u_4} [inst_1 : AddCommMonoid M]   [inst_
2 : AddCommMon…
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `Module.End.algebraMap_isUnit_inv_apply_eq_iff`：∀ {R : Type u} (S : Type 
v) {M : Type w} [inst : CommSemiring R] [inst_1 : Semiring S] [inst_2 : AddCommM
onoid M]   [inst_3 : _root_.Module …
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `LinearMap.map_smul_of_tower`：map_smul_of_tower [CompatibleSMul M M₂ R S]
 (fₗ : M ->ₗ[S] M₂) (c : R) (x : M) : fₗ (c • x) = c • fₗ x
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `Submonoid.smul_def`：∀ {M' : Type u_1} {α : Type u_2} [inst : MulOneClass
 M'] [inst_1 : SMul M' α] {S : Submonoid M'} (g : ↥S) (a : α),   g • a = ↑g • a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem lift'_add (g : M →ₗ[R] M'') (h : ∀ x : S, IsUnit ((algebraMap R (Module.End R M'')) x))
    (x y) :
    LocalizedModule.lift' S g h (x + y) =
      LocalizedModule.lift' S g h x + LocalizedModule.lift' S g h y :=
  LocalizedModule.induction_on₂
    (by
      intro a a' b b'
      rw [mk_add_mk, LocalizedModule.lift'_mk, LocalizedModule.lift'_mk, LocalizedModule.lift'_mk]
      rw [map_add, Module.End.algebraMap_isUnit_inv_apply_eq_iff, smul_add, ← map_smul,
        ← map_smul, ← map_smul]
      congr 1 <;> symm
      · rw [Module.End.algebraMap_isUnit_inv_apply_eq_iff]
        simp only [Submonoid.coe_mul, LinearMap.map_smul_of_tower]
        rw [mul_smul, Submonoid.smul_def]
      · dsimp
        rw [Module.End.algebraMap_isUnit_inv_apply_eq_iff, mul_comm, mul_smul, ← map_smul]
        rfl)
    x y
/-
**LocalizedModule.lift'_smul** 是 Mathlib 中的一个定理，位于命名空间 `LocalizedModule`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] (S : Submonoid R) {M : Type u_2} 
{M'' : Type u_4} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid M''] [inst
_3 : _root_.Module R M] [inst_4 : _root_.Module R M''] (g : M →ₗ[R] M'')   (h : 
∀ (x : ↥S), IsUnit ((algebraMap R (Module.End R M'')) ↑x)) (r : R) (m : Localize
dModule S M),   r • LocalizedModule.lift' S g h m = LocalizedModule.lift' S g h 
(r • m)
参数：S : Submonoid R；g : M →ₗ[R] M''；h : ∀ (x : ↥S), IsUnit ((algebraMap R (Module
.End R M'')) ↑x)；r : R；m : LocalizedModule S M；r • m。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LocalizedModule.induction_on`：induction_on {β : LocalizedModule S M -> P
rop} (h : forall (m : M) (s : S), β (mk m s)) : forall x : LocalizedModule S M, 
β x
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LocalizedModule.lift'_mk`：∀ {R : Type u_1} [inst : CommSemiring R] (S : 
Submonoid R) {M : Type u_2} {M'' : Type u_4} [inst_1 : AddCommMonoid M]   [inst_
2 : AddCommMon…
· 使用定理 `LocalizedModule.smul'_mk`：∀ {R : Type u} [inst : CommSemiring R] {S : Su
bmonoid R} {M : Type v} [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M
] {R₀ : Type u…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `LinearMap.map_smul`：∀ {R : Type u_1} {M : Type u_8} {M₂ : Type u_10} [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid M₂] [inst_
3 : _roo…
-/
theorem lift'_smul (g : M →ₗ[R] M'') (h : ∀ x : S, IsUnit ((algebraMap R (Module.End R M'')) x))
    (r : R) (m) : r • LocalizedModule.lift' S g h m = LocalizedModule.lift' S g h (r • m) :=
  m.induction_on fun a b => by
    rw [LocalizedModule.lift'_mk, LocalizedModule.smul'_mk, LocalizedModule.lift'_mk,
      ← map_smul, ← g.map_smul]

/--
If `g` is a linear map `M → M''` such that all scalar multiplication by `s : S` is invertible, then
there is a linear map `LocalizedModule S M → M''`.
-/
/-
**LocalizedModule.lift** 是 Mathlib 中的一个定义，位于命名空间 `LocalizedModule`。
形式化陈述：lift (g : M ->ₗ[R] M'') (h : forall x : S, IsUnit ((algebraMap R (Module.E
nd R M'')) x)) : LocalizedModule S M ->ₗ[R] M'' where toFun
参数：g : M ->ₗ[R] M''；h : forall x : S, IsUnit ((algebraMap R (Module.End R M'')) 
x)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `LocalizedModule.lift'_add`：∀ {R : Type u_1} [inst : CommSemiring R] (S :
 Submonoid R) {M : Type u_2} {M'' : Type u_4} [inst_1 : AddCommMonoid M]   [inst
_2 : AddCommMon…

--- 原说明 ---
If `g` is a linear map `M → M''` such that all scalar multiplication by `s : S` 
is invertible, then
there is a linear map `LocalizedModule S M → M''`.
-/
noncomputable def lift (g : M →ₗ[R] M'')
    (h : ∀ x : S, IsUnit ((algebraMap R (Module.End R M'')) x)) :
    LocalizedModule S M →ₗ[R] M'' where
  toFun := LocalizedModule.lift' S g h
  map_add' := LocalizedModule.lift'_add S g h
  map_smul' r x := by rw [LocalizedModule.lift'_smul, RingHom.id_apply]

/--
If `g` is a linear map `M → M''` such that all scalar multiplication by `s : S` is invertible, then
`lift g m s = s⁻¹ • g m`.
-/
/-
**LocalizedModule.lift_mk** 是 Mathlib 中的一个定理，位于命名空间 `LocalizedModule`。
形式化陈述：lift_mk (g : M ->ₗ[R] M'') (h : forall x : S, IsUnit (algebraMap R (Module
.End R M'') x)) (m : M) (s : S) : LocalizedModule.lift S g h (LocalizedModule.mk
 m s) = (h s).unit⁻¹.val (g m)
参数：g : M ->ₗ[R] M''；h : forall x : S, IsUnit (algebraMap R (Module.End R M'') x)
；m : M；s : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A

--- 原说明 ---
If `g` is a linear map `M → M''` such that all scalar multiplication by `s : S` 
is invertible, then
`lift g m s = s⁻¹ • g m`.
-/
theorem lift_mk
    (g : M →ₗ[R] M'') (h : ∀ x : S, IsUnit (algebraMap R (Module.End R M'') x)) (m : M) (s : S) :
    LocalizedModule.lift S g h (LocalizedModule.mk m s) = (h s).unit⁻¹.val (g m) :=
  rfl

@[simp]
/-
**LocalizedModule.lift_mk_one** 是 Mathlib 中的一个引理，位于命名空间 `LocalizedModule`。
形式化陈述：lift_mk_one (h : forall (x : S), IsUnit ((algebraMap R (Module.End R M''))
 x)) (m : M) : (LocalizedModule.lift S g h) (LocalizedModule.mk m 1) = g m
参数：h : forall (x : S), IsUnit ((algebraMap R (Module.End R M'')) x)；m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
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
· 使用定理 `IsUnit.unit.congr_simp`：∀ {M : Type u_1} [inst : Monoid M] {a a_1 : M} (
e_a : a = a_1) (h : IsUnit a), h.unit = ⋯.unit
· 使用定理 `IsUnit.unit_one`：unit_one (h : IsUnit (1 : M)) : h.unit = 1
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma lift_mk_one (h : ∀ (x : S), IsUnit ((algebraMap R (Module.End R M'')) x)) (m : M) :
    (LocalizedModule.lift S g h) (LocalizedModule.mk m 1) = g m := by
  simp [lift_mk]

/--
If `g` is a linear map `M → M''` such that all scalar multiplication by `s : S` is invertible, then
there is a linear map `lift g ∘ mkLinearMap = g`.
-/
/-
**LocalizedModule.lift_comp** 是 Mathlib 中的一个定理，位于命名空间 `LocalizedModule`。
形式化陈述：lift_comp (g : M ->ₗ[R] M'') (h : forall x : S, IsUnit ((algebraMap R (Mod
ule.End R M'')) x)) : (lift S g h).comp (mkLinearMap S M) = g
参数：g : M ->ₗ[R] M''；h : forall x : S, IsUnit ((algebraMap R (Module.End R M'')) 
x)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LocalizedModule.mkLinearMap_apply`：∀ {R : Type u} [inst : CommSemiring R
] (S : Submonoid R) (M : Type v) [inst_1 : AddCommMonoid M]   [inst_2 : _root_.M
odule R M] (m : M), (Lo…
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
· 使用定理 `IsUnit.unit.congr_simp`：∀ {M : Type u_1} [inst : Monoid M] {a a_1 : M} (
e_a : a = a_1) (h : IsUnit a), h.unit = ⋯.unit
· 使用定理 `IsUnit.unit_one`：unit_one (h : IsUnit (1 : M)) : h.unit = 1
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `g` is a linear map `M → M''` such that all scalar multiplication by `s : S` 
is invertible, then
there is a linear map `lift g ∘ mkLinearMap = g`.
-/
theorem lift_comp (g : M →ₗ[R] M'') (h : ∀ x : S, IsUnit ((algebraMap R (Module.End R M'')) x)) :
    (lift S g h).comp (mkLinearMap S M) = g := by
  ext x
  simp [LocalizedModule.lift_mk]

/--
If `g` is a linear map `M → M''` such that all scalar multiplication by `s : S` is invertible and
`l` is another linear map `LocalizedModule S M ⟶ M''` such that `l ∘ mkLinearMap = g` then
`l = lift g`
-/
/-
**LocalizedModule.lift_unique** 是 Mathlib 中的一个定理，位于命名空间 `LocalizedModule`。
形式化陈述：lift_unique (g : M ->ₗ[R] M'') (h : forall x : S, IsUnit ((algebraMap R (M
odule.End R M'')) x)) (l : LocalizedModule S M ->ₗ[R] M'') (hl : l.comp (Localiz
edModule.mkLinearMap S M) = g) : LocalizedModule.lift S g h = l
参数：g : M ->ₗ[R] M''；h : forall x : S, IsUnit ((algebraMap R (Module.End R M'')) 
x)；l : LocalizedModule S M ->ₗ[R] M''；hl : l.comp (LocalizedModule.mkLinearMap S
 M) = g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `LocalizedModule.induction_on`：induction_on {β : LocalizedModule S M -> P
rop} (h : forall (m : M) (s : S), β (mk m s)) : forall x : LocalizedModule S M, 
β x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LocalizedModule.lift_mk`：lift_mk (g : M ->ₗ[R] M'') (h : forall x : S, I
sUnit (algebraMap R (Module.End R M'') x)) (m : M) (s : S) : LocalizedModule.lif
t S g h (Loca…
· 使用定理 `Module.End.algebraMap_isUnit_inv_apply_eq_iff`：∀ {R : Type u} (S : Type 
v) {M : Type w} [inst : CommSemiring R] [inst_1 : Semiring S] [inst_2 : AddCommM
onoid M]   [inst_3 : _root_.Module …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.coe_comp`：coe_comp : (f.comp g : M₁ -> M₃) = f ∘ g
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `LocalizedModule.mkLinearMap_apply`：∀ {R : Type u} [inst : CommSemiring R
] (S : Submonoid R) (M : Type v) [inst_1 : AddCommMonoid M]   [inst_2 : _root_.M
odule R M] (m : M), (Lo…
· 使用定理 `LinearMap.map_smul`：∀ {R : Type u_1} {M : Type u_8} {M₂ : Type u_10} [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid M₂] [inst_
3 : _roo…
· 使用定理 `LocalizedModule.smul'_mk`：∀ {R : Type u} [inst : CommSemiring R] {S : Su
bmonoid R} {M : Type v} [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M
] {R₀ : Type u…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `LocalizedModule.mk_eq`：mk_eq {m m' : M} {s s' : S} : mk m s = mk m' s' ↔
 exists u : S, u • s' • m = u • s • m'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `g` is a linear map `M → M''` such that all scalar multiplication by `s : S` 
is invertible and
`l` is another linear map `LocalizedModule S M ⟶ M''` such that `l ∘ mkLinearMap
 = g` then
`l = lift g`
-/
theorem lift_unique (g : M →ₗ[R] M'') (h : ∀ x : S, IsUnit ((algebraMap R (Module.End R M'')) x))
    (l : LocalizedModule S M →ₗ[R] M'') (hl : l.comp (LocalizedModule.mkLinearMap S M) = g) :
    LocalizedModule.lift S g h = l := by
  ext x; induction x with | _ m s
  rw [LocalizedModule.lift_mk]
  rw [Module.End.algebraMap_isUnit_inv_apply_eq_iff, ← hl, LinearMap.coe_comp,
    Function.comp_apply, LocalizedModule.mkLinearMap_apply, ← l.map_smul, LocalizedModule.smul'_mk]
  congr 1; rw [LocalizedModule.mk_eq]
  refine ⟨1, ?_⟩; simp only [one_smul, Submonoid.smul_def]

end LocalizedModule

/-
**localizedModuleIsLocalizedModule** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：localizedModuleIsLocalizedModule : IsLocalizedModule S (LocalizedModule.mk
LinearMap S M) where map_units s
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `OreLocalization.instSMulCommClass`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
· 使用定理 `LocalizedModule.mul_by_divBy`：mul_by_divBy (s : S) (p : LocalizedModule 
S M) : algebraMap R (Module.End R (LocalizedModule S M)) s (divBy s p) = p
· 使用定理 `LocalizedModule.divBy_mul_by`：divBy_mul_by (s : S) (p : LocalizedModule 
S M) : divBy s (algebraMap R (Module.End R (LocalizedModule S M)) s p) = p
· 使用定理 `LocalizedModule.induction_on`：induction_on {β : LocalizedModule S M -> P
rop} (h : forall (m : M) (s : S), β (mk m s)) : forall x : LocalizedModule S M, 
β x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submonoid.smul_def`：∀ {M' : Type u_1} {α : Type u_2} [inst : MulOneClass
 M'] [inst_1 : SMul M' α] {S : Submonoid M'} (g : ↥S) (a : α),   g • a = ↑g • a
· 使用定理 `LocalizedModule.smul'_mk`：∀ {R : Type u} [inst : CommSemiring R] {S : Su
bmonoid R} {M : Type v} [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M
] {R₀ : Type u…
· 使用定理 `LocalizedModule.mkLinearMap_apply`：∀ {R : Type u} [inst : CommSemiring R
] (S : Submonoid R) (M : Type v) [inst_1 : AddCommMonoid M]   [inst_2 : _root_.M
odule R M] (m : M), (Lo…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LocalizedModule.mk_cancel`：mk_cancel (s : S) (m : M) : mk (s • m) s = mk
 m 1
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LocalizedModule.mk_eq`：mk_eq {m m' : M} {s s' : S} : mk m s = mk m' s' ↔
 exists u : S, u • s' • m = u • s • m'
-/
instance localizedModuleIsLocalizedModule :
    IsLocalizedModule S (LocalizedModule.mkLinearMap S M) where
  map_units s :=
    ⟨⟨algebraMap R (Module.End R (LocalizedModule S M)) s, LocalizedModule.divBy s,
        DFunLike.ext _ _ <| LocalizedModule.mul_by_divBy s,
        DFunLike.ext _ _ <| LocalizedModule.divBy_mul_by s⟩,
      DFunLike.ext _ _ fun p =>
        p.induction_on <| by
          intros
          rfl⟩
  surj p :=
    p.induction_on fun m t => by
      refine ⟨⟨m, t⟩, ?_⟩
      rw [Submonoid.smul_def, LocalizedModule.smul'_mk, LocalizedModule.mkLinearMap_apply,
        ← Submonoid.smul_def, LocalizedModule.mk_cancel t]
  exists_of_eq eq1 := by simpa only [eq_comm, one_smul] using LocalizedModule.mk_eq.mp eq1
/-
**IsLocalizedModule.restrictScalars** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsLocalizedModule.restrictScalars (S : Submonoid R) [Module A M] {N : Type
*} [AddCommMonoid N] [Module R N] [Module A N] [IsScalarTower R A M] [IsScalarTo
wer R A N] (f : M ->ₗ[A] N) [h : IsLocalizedModule (Algebra.algebraMapSubmonoid 
A S) f] : IsLocalizedModule S (f.restrictScalars R) where map_units s
参数：S : Submonoid R；f : M ->ₗ[A] N；Algebra.algebraMapSubmonoid A S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `Algebra.mem_algebraMapSubmonoid_of_mem`：mem_algebraMapSubmonoid_of_mem {
M : Submonoid R} (x : M) : algebraMap R S x in algebraMapSubmonoid S M
· 使用定理 `IsLocalizedModule.map_units`：∀ {R : Type u_1} {inst : CommSemiring R} {M
 : Type u_2} {M' : Type u_3} {inst_1 : AddCommMonoid M}   {inst_2 : AddCommMonoi
d M'} {inst_3 : _…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.instIsScalarTower`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `IsLocalizedModule.surj`：∀ {R : Type u_1} {inst : CommSemiring R} {M : Ty
pe u_2} {M' : Type u_3} {inst_1 : AddCommMonoid M}   {inst_2 : AddCommMonoid M'}
 {inst_3 : _…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `algebraMap_smul`：algebraMap_smul (r : R) (m : M) : (algebraMap R A) r • 
m = r • m
· 使用定理 `IsLocalizedModule.exists_of_eq`：∀ {R : Type u_1} {inst : CommSemiring R}
 {M : Type u_2} {M' : Type u_3} {inst_1 : AddCommMonoid M}   {inst_2 : AddCommMo
noid M'} {inst_3 : _…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
-/
lemma IsLocalizedModule.restrictScalars (S : Submonoid R) [Module A M]
    {N : Type*} [AddCommMonoid N] [Module R N] [Module A N]
    [IsScalarTower R A M] [IsScalarTower R A N]
    (f : M →ₗ[A] N) [h : IsLocalizedModule (Algebra.algebraMapSubmonoid A S) f] :
    IsLocalizedModule S (f.restrictScalars R) where
  map_units s := by
    have := h.1 ⟨algebraMap R A s, Algebra.mem_algebraMapSubmonoid_of_mem s⟩
    simp only [← IsScalarTower.algebraMap_apply, Module.End.isUnit_iff] at this ⊢
    exact this
  surj y := by
    obtain ⟨⟨x, ⟨_, ⟨r, ⟨hr₁, rfl⟩⟩⟩⟩, hx⟩ := h.2 y
    exact ⟨⟨x, ⟨r, hr₁⟩⟩, by simpa [Submonoid.smul_def] using hx⟩
  exists_of_eq {x₁ x₂} e := by
    obtain ⟨⟨_, ⟨r, ⟨hr, rfl⟩⟩⟩, hc⟩ := h.3 e
    exact ⟨⟨r, hr⟩, by simpa [Submonoid.smul_def] using hc⟩
/-
**IsLocalizedModule.restrictScalars_powers** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsLocalizedModule.restrictScalars_powers [Module A M] {N : Type*} [AddComm
Monoid N] [Module R N] [Module A N] [IsScalarTower R A M] [IsScalarTower R A N] 
(r : R) (f : M ->ₗ[A] N) [h : IsLocalizedModule (.powers (algebraMap R A r)) f] 
: IsLocalizedModule (.powers r) (f.restrictScalars R)
参数：r : R；f : M ->ₗ[A] N；.powers (algebraMap R A r)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalizedModule.restrictScalars`：IsLocalizedModule.restrictScalars (S 
: Submonoid R) [Module A M] {N : Type*} [AddCommMonoid N] [Module R N] [Module A
 N] [IsScalarTower R A …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Algebra.algebraMapSubmonoid_powers`：algebraMapSubmonoid_powers (r : R) :
 Algebra.algebraMapSubmonoid S (.powers r) = Submonoid.powers (algebraMap R S r)
-/
lemma IsLocalizedModule.restrictScalars_powers [Module A M]
    {N : Type*} [AddCommMonoid N] [Module R N] [Module A N]
    [IsScalarTower R A M] [IsScalarTower R A N]
    (r : R) (f : M →ₗ[A] N) [h : IsLocalizedModule (.powers (algebraMap R A r)) f] :
    IsLocalizedModule (.powers r) (f.restrictScalars R) := by
  rw [← Algebra.algebraMapSubmonoid_powers] at h
  exact IsLocalizedModule.restrictScalars _ f
/-
**IsLocalizedModule.of_restrictScalars** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsLocalizedModule.of_restrictScalars (S : Submonoid R) {N : Type*} [AddCom
mMonoid N] [Module R N] [Module A M] [Module A N] [IsScalarTower R A M] [IsScala
rTower R A N] (f : M ->ₗ[A] N) [IsLocalizedModule S (f.restrictScalars R)] : IsL
ocalizedModule (Algebra.algebraMapSubmonoid A S) f where map_units x
参数：S : Submonoid R；f : M ->ₗ[A] N；f.restrictScalars R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `IsLocalizedModule.map_units`：∀ {R : Type u_1} {inst : CommSemiring R} {M
 : Type u_2} {M' : Type u_3} {inst_1 : AddCommMonoid M}   {inst_2 : AddCommMonoi
d M'} {inst_3 : _…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.instIsScalarTower`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `IsLocalizedModule.surj`：∀ {R : Type u_1} {inst : CommSemiring R} {M : Ty
pe u_2} {M' : Type u_3} {inst_1 : AddCommMonoid M}   {inst_2 : AddCommMonoid M'}
 {inst_3 : _…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `algebraMap_smul`：algebraMap_smul (r : R) (m : M) : (algebraMap R A) r • 
m = r • m
· 使用定理 `IsLocalizedModule.exists_of_eq`：∀ {R : Type u_1} {inst : CommSemiring R}
 {M : Type u_2} {M' : Type u_3} {inst_1 : AddCommMonoid M}   {inst_2 : AddCommMo
noid M'} {inst_3 : _…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
-/
lemma IsLocalizedModule.of_restrictScalars (S : Submonoid R)
    {N : Type*} [AddCommMonoid N] [Module R N] [Module A M] [Module A N]
    [IsScalarTower R A M] [IsScalarTower R A N]
    (f : M →ₗ[A] N) [IsLocalizedModule S (f.restrictScalars R)] :
    IsLocalizedModule (Algebra.algebraMapSubmonoid A S) f where
  map_units x := by
    obtain ⟨_, x, hx, rfl⟩ := x
    have := IsLocalizedModule.map_units (f.restrictScalars R) ⟨x, hx⟩
    simp only [← IsScalarTower.algebraMap_apply, Module.End.isUnit_iff] at this ⊢
    exact this
  surj y := by
    obtain ⟨⟨x, t⟩, e⟩ := IsLocalizedModule.surj S (f.restrictScalars R) y
    exact ⟨⟨x, ⟨_, t, t.2, rfl⟩⟩, by simpa [Submonoid.smul_def] using e⟩
  exists_of_eq {x₁ x₂} e := by
    obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := S) (f := f.restrictScalars R) e
    refine ⟨⟨_, c, c.2, rfl⟩, by simpa [Submonoid.smul_def]⟩
/-
**IsLocalizedModule.restrictScalars_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsLocalizedModule.restrictScalars_iff (S : Submonoid R) {N : Type*} [AddCo
mmMonoid N] [Module R N] [Module A M] [Module A N] [IsScalarTower R A M] [IsScal
arTower R A N] (f : M ->ₗ[A] N) : IsLocalizedModule (Algebra.algebraMapSubmonoid
 A S) f ↔ IsLocalizedModule S (f.restrictScalars R)
参数：S : Submonoid R；f : M ->ₗ[A] N。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用引理 `IsLocalizedModule.restrictScalars`：IsLocalizedModule.restrictScalars (S 
: Submonoid R) [Module A M] {N : Type*} [AddCommMonoid N] [Module R N] [Module A
 N] [IsScalarTower R A …
· 使用引理 `IsLocalizedModule.of_restrictScalars`：IsLocalizedModule.of_restrictScala
rs (S : Submonoid R) {N : Type*} [AddCommMonoid N] [Module R N] [Module A M] [Mo
dule A N] [IsScalarTower R…
-/
lemma IsLocalizedModule.restrictScalars_iff (S : Submonoid R)
    {N : Type*} [AddCommMonoid N] [Module R N] [Module A M] [Module A N]
    [IsScalarTower R A M] [IsScalarTower R A N] (f : M →ₗ[A] N) :
    IsLocalizedModule (Algebra.algebraMapSubmonoid A S) f ↔
    IsLocalizedModule S (f.restrictScalars R) :=
  ⟨fun _ => restrictScalars _ _, fun _ => of_restrictScalars _ _⟩
/-
**IsLocalizedModule.of_exists_mul_mem** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsLocalizedModule.of_exists_mul_mem {N : Type*} [AddCommMonoid N] [Module 
R N] (S T : Submonoid R) (h : S <= T) (h' : forall x : T, exists m : R, m * x in
 S) (f : M ->ₗ[R] N) [IsLocalizedModule S f] : IsLocalizedModule T f where map_u
nits x
参数：S T : Submonoid R；h : S <= T；h' : forall x : T, exists m : R, m * x in S；f : 
M ->ₗ[R] N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalizedModule.map_units`：∀ {R : Type u_1} {inst : CommSemiring R} {M
 : Type u_2} {M' : Type u_3} {inst_1 : AddCommMonoid M}   {inst_2 : AddCommMonoi
d M'} {inst_3 : _…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Commute.isUnit_mul_iff`：Commute.isUnit_mul_iff (h : Commute a b) : IsUni
t (a * b) ↔ IsUnit a ∧ IsUnit b
· 使用引理 `Algebra.commute_algebraMap_left`：commute_algebraMap_left (r : R) (x : A)
 : Commute (algebraMap R A r) x
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `IsLocalizedModule.surj`：∀ {R : Type u_1} {inst : CommSemiring R} {M : Ty
pe u_2} {M' : Type u_3} {inst_1 : AddCommMonoid M}   {inst_2 : AddCommMonoid M'}
 {inst_3 : _…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `IsLocalizedModule.exists_of_eq`：∀ {R : Type u_1} {inst : CommSemiring R}
 {M : Type u_2} {M' : Type u_3} {inst_1 : AddCommMonoid M}   {inst_2 : AddCommMo
noid M'} {inst_3 : _…
-/
lemma IsLocalizedModule.of_exists_mul_mem {N : Type*} [AddCommMonoid N] [Module R N]
    (S T : Submonoid R) (h : S ≤ T) (h' : ∀ x : T, ∃ m : R, m * x ∈ S)
    (f : M →ₗ[R] N) [IsLocalizedModule S f] :
    IsLocalizedModule T f where
  map_units x := by
    obtain ⟨m, mx⟩ := h' x
    have := IsLocalizedModule.map_units f ⟨_, mx⟩
    rw [map_mul, (Algebra.commute_algebraMap_left _ _).isUnit_mul_iff] at this
    exact this.2
  surj y := by
    obtain ⟨⟨x, t⟩, e⟩ := IsLocalizedModule.surj S f y
    exact ⟨⟨x, ⟨t, h t.2⟩⟩, e⟩
  exists_of_eq {x₁ x₂} e := by
    obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := S) (f := f) e
    exact ⟨⟨c, h c.2⟩, hc⟩

namespace IsLocalizedModule

variable [IsLocalizedModule S f]

/-- If `(M', f : M ⟶ M')` satisfies universal property of localized module, there is a canonical
map `LocalizedModule S M ⟶ M'`.
-/
/-
**IsLocalizedModule.fromLocalizedModule'** 是 Mathlib 中的一个定义，位于命名空间 `IsLocalizedM
odule`。
形式化陈述：fromLocalizedModule' : LocalizedModule S M -> M'
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `(M', f : M ⟶ M')` satisfies universal property of localized module, there is
 a canonical
map `LocalizedModule S M ⟶ M'`.
-/
noncomputable def fromLocalizedModule' : LocalizedModule S M → M' := fun p =>
  p.liftOn (fun x => (IsLocalizedModule.map_units f x.2).unit⁻¹.val (f x.1))
    (by
      rintro ⟨a, b⟩ ⟨a', b'⟩ ⟨c, eq1⟩
      dsimp
      rw [Module.End.algebraMap_isUnit_inv_apply_eq_iff, ← map_smul, ← map_smul,
        Module.End.algebraMap_isUnit_inv_apply_eq_iff', ← map_smul]
      exact (IsLocalizedModule.eq_iff_exists S f).mpr ⟨c, eq1.symm⟩)

@[simp]
/-
**IsLocalizedModule.fromLocalizedModule'_mk** 是 Mathlib 中的一个定理，位于命名空间 `IsLocaliz
edModule`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] (S : Submonoid R) {M : Type u_2} 
{M' : Type u_3} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid M'] [inst_3
 : _root_.Module R M] [inst_4 : _root_.Module R M'] (f : M →ₗ[R] M')   [inst_5 :
 IsLocalizedModule S f] (m : M) (s : ↥S),   IsLocalizedModule.fromLocalizedModul
e' S f (LocalizedModule.mk m s) = ↑⋯.unit⁻¹ (f m)
参数：S : Submonoid R；f : M →ₗ[R] M'；m : M；s : ↥S；LocalizedModule.mk m s；f m。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fromLocalizedModule'_mk (m : M) (s : S) :
    fromLocalizedModule' S f (LocalizedModule.mk m s) =
      (IsLocalizedModule.map_units f s).unit⁻¹.val (f m) :=
  rfl
/-
**IsLocalizedModule.fromLocalizedModule'_add** 是 Mathlib 中的一个定理，位于命名空间 `IsLocali
zedModule`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] (S : Submonoid R) {M : Type u_2} 
{M' : Type u_3} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid M'] [inst_3
 : _root_.Module R M] [inst_4 : _root_.Module R M'] (f : M →ₗ[R] M')   [inst_5 :
 IsLocalizedModule S f] (x y : LocalizedModule S M),   IsLocalizedModule.fromLoc
alizedModule' S f (x + y) =     IsLocalizedModule.fromLocalizedModule' S f x + I
sLocalizedModule.fromLocalizedModule' S f y
参数：S : Submonoid R；f : M →ₗ[R] M'；x y : LocalizedModule S M；x + y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LocalizedModule.induction_on₂`：induction_on₂ {β : LocalizedModule S M ->
 LocalizedModule S M -> Prop} (h : forall (m m' : M) (s s' : S), β (mk m s) (mk 
m' s')) : forall x …
· 使用定理 `IsLocalizedModule.map_units`：∀ {R : Type u_1} {inst : CommSemiring R} {M
 : Type u_2} {M' : Type u_3} {inst_1 : AddCommMonoid M}   {inst_2 : AddCommMonoi
d M'} {inst_3 : _…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsLocalizedModule.fromLocalizedModule'.congr_simp`：∀ {R : Type u_1} [ins
t : CommSemiring R] (S : Submonoid R) {M : Type u_2} {M' : Type u_3} [inst_1 : A
ddCommMonoid M]   [inst_2 : AddCommMono…
· 使用定理 `LocalizedModule.mk_add_mk`：mk_add_mk {m1 m2 : M} {s1 s2 : S} : mk m1 s1 
+ mk m2 s2 = mk (s2 • m1 + s1 • m2) (s1 * s2)
· 使用定理 `Module.End.algebraMap_isUnit_inv_apply_eq_iff`：∀ {R : Type u} (S : Type 
v) {M : Type w} [inst : CommSemiring R] [inst_1 : Semiring S] [inst_2 : AddCommM
onoid M]   [inst_3 : _root_.Module …
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `Module.End.algebraMap_isUnit_inv_apply_eq_iff'`：∀ {R : Type u} (S : Type
 v) {M : Type w} [inst : CommSemiring R] [inst_1 : Semiring S] [inst_2 : AddComm
Monoid M]   [inst_3 : _root_.Module …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Submonoid.coe_mul`：coe_mul (x y : S) : (↑(x * y) : M) = ↑x * ↑y
· 使用定理 `LinearMap.map_smul_of_tower`：map_smul_of_tower [CompatibleSMul M M₂ R S]
 (fₗ : M ->ₗ[S] M₂) (c : R) (x : M) : fₗ (c • x) = c • fₗ x
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Submonoid.smul_def`：∀ {M' : Type u_1} {α : Type u_2} [inst : MulOneClass
 M'] [inst_1 : SMul M' α] {S : Submonoid M'} (g : ↥S) (a : α),   g • a = ↑g • a
-/
theorem fromLocalizedModule'_add (x y : LocalizedModule S M) :
    fromLocalizedModule' S f (x + y) = fromLocalizedModule' S f x + fromLocalizedModule' S f y :=
  LocalizedModule.induction_on₂
    (by
      intro a a' b b'
      simp only [LocalizedModule.mk_add_mk, fromLocalizedModule'_mk]
      rw [Module.End.algebraMap_isUnit_inv_apply_eq_iff, smul_add, ← map_smul, ← map_smul,
        ← map_smul, map_add]
      congr 1
      all_goals rw [Module.End.algebraMap_isUnit_inv_apply_eq_iff']
      · simp [mul_smul, Submonoid.smul_def]
      · rw [Submonoid.coe_mul, LinearMap.map_smul_of_tower, mul_comm, mul_smul, Submonoid.smul_def])
    x y
/-
**IsLocalizedModule.fromLocalizedModule'_smul** 是 Mathlib 中的一个定理，位于命名空间 `IsLocal
izedModule`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] (S : Submonoid R) {M : Type u_2} 
{M' : Type u_3} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid M'] [inst_3
 : _root_.Module R M] [inst_4 : _root_.Module R M'] (f : M →ₗ[R] M')   [inst_5 :
 IsLocalizedModule S f] (r : R) (x : LocalizedModule S M),   r • IsLocalizedModu
le.fromLocalizedModule' S f x = IsLocalizedModule.fromLocalizedModule' S f (r • 
x)
参数：S : Submonoid R；f : M →ₗ[R] M'；r : R；x : LocalizedModule S M；r • x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LocalizedModule.induction_on`：induction_on {β : LocalizedModule S M -> P
rop} (h : forall (m : M) (s : S), β (mk m s)) : forall x : LocalizedModule S M, 
β x
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsLocalizedModule.map_units`：∀ {R : Type u_1} {inst : CommSemiring R} {M
 : Type u_2} {M' : Type u_3} {inst_1 : AddCommMonoid M}   {inst_2 : AddCommMonoi
d M'} {inst_3 : _…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsLocalizedModule.fromLocalizedModule'_mk`：∀ {R : Type u_1} [inst : Comm
Semiring R] (S : Submonoid R) {M : Type u_2} {M' : Type u_3} [inst_1 : AddCommMo
noid M]   [inst_2 : AddCommMono…
· 使用定理 `LocalizedModule.smul'_mk`：∀ {R : Type u} [inst : CommSemiring R] {S : Su
bmonoid R} {M : Type v} [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M
] {R₀ : Type u…
· 使用定理 `LinearMap.map_smul`：∀ {R : Type u_1} {M : Type u_8} {M₂ : Type u_10} [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid M₂] [inst_
3 : _roo…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
-/
theorem fromLocalizedModule'_smul (r : R) (x : LocalizedModule S M) :
    r • fromLocalizedModule' S f x = fromLocalizedModule' S f (r • x) :=
  LocalizedModule.induction_on
    (by
      intro a b
      rw [fromLocalizedModule'_mk, LocalizedModule.smul'_mk, fromLocalizedModule'_mk,
        f.map_smul, map_smul])
    x

/-- If `(M', f : M ⟶ M')` satisfies universal property of localized module, there is a canonical
map `LocalizedModule S M ⟶ M'`.
-/
/-
**IsLocalizedModule.fromLocalizedModule** 是 Mathlib 中的一个定义，位于命名空间 `IsLocalizedMo
dule`。
形式化陈述：fromLocalizedModule : LocalizedModule S M ->ₗ[R] M' where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalizedModule.fromLocalizedModule'_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (S : Submonoid R) {M : Type u_2} {M' : Type u_3} [inst_1 : AddCommM
onoid M]   [inst_2 : AddCommMono…

--- 原说明 ---
If `(M', f : M ⟶ M')` satisfies universal property of localized module, there is
 a canonical
map `LocalizedModule S M ⟶ M'`.
-/
noncomputable def fromLocalizedModule : LocalizedModule S M →ₗ[R] M' where
  toFun := fromLocalizedModule' S f
  map_add' := fromLocalizedModule'_add S f
  map_smul' r x := by rw [fromLocalizedModule'_smul, RingHom.id_apply]
/-
**IsLocalizedModule.fromLocalizedModule_mk** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalize
dModule`。
形式化陈述：fromLocalizedModule_mk (m : M) (s : S) : fromLocalizedModule S f (Localize
dModule.mk m s) = (IsLocalizedModule.map_units f s).unit⁻¹.val (f m)
参数：m : M；s : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
theorem fromLocalizedModule_mk (m : M) (s : S) :
    fromLocalizedModule S f (LocalizedModule.mk m s) =
      (IsLocalizedModule.map_units f s).unit⁻¹.val (f m) :=
  rfl
/-
**IsLocalizedModule.fromLocalizedModule.inj** 是 Mathlib 中的一个定理，位于命名空间 `IsLocaliz
edModule.fromLocalizedModule`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] (S : Submonoid R) {M : Type u_2} 
{M' : Type u_3} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid M'] [inst_3
 : _root_.Module R M] [inst_4 : _root_.Module R M'] (f : M →ₗ[R] M')   [inst_5 :
 IsLocalizedModule S f], Function.Injective ⇑(IsLocalizedModule.fromLocalizedMod
ule S f)
参数：S : Submonoid R；f : M →ₗ[R] M'；IsLocalizedModule.fromLocalizedModule S f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `LocalizedModule.induction_on`：induction_on {β : LocalizedModule S M -> P
rop} (h : forall (m : M) (s : S), β (mk m s)) : forall x : LocalizedModule S M, 
β x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LocalizedModule.mk_eq`：mk_eq {m m' : M} {s s' : S} : mk m s = mk m' s' ↔
 exists u : S, u • s' • m = u • s • m'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `IsLocalizedModule.eq_iff_exists`：IsLocalizedModule.eq_iff_exists [IsLoca
lizedModule S f] {x₁ x₂} : f x₁ = f x₂ ↔ exists c : S, c • x₁ = c • x₂
· 使用定理 `Submonoid.smul_def`：∀ {M' : Type u_1} {α : Type u_2} [inst : MulOneClass
 M'] [inst_1 : SMul M' α] {S : Submonoid M'} (g : ↥S) (a : α),   g • a = ↑g • a
· 使用定理 `LinearMap.map_smul`：∀ {R : Type u_1} {M : Type u_8} {M₂ : Type u_10} [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid M₂] [inst_
3 : _roo…
· 使用定理 `IsLocalizedModule.map_units`：∀ {R : Type u_1} {inst : CommSemiring R} {M
 : Type u_2} {M' : Type u_3} {inst_1 : AddCommMonoid M}   {inst_2 : AddCommMonoi
d M'} {inst_3 : _…
· 使用定理 `Module.End.algebraMap_isUnit_inv_apply_eq_iff'`：∀ {R : Type u} (S : Type
 v) {M : Type w} [inst : CommSemiring R] [inst_1 : Semiring S] [inst_2 : AddComm
Monoid M]   [inst_3 : _root_.Module …
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `Module.End.algebraMap_isUnit_inv_apply_eq_iff`：∀ {R : Type u} (S : Type 
v) {M : Type w} [inst : CommSemiring R] [inst_1 : Semiring S] [inst_2 : AddCommM
onoid M]   [inst_3 : _root_.Module …
-/
theorem fromLocalizedModule.inj : Function.Injective <| fromLocalizedModule S f := fun x y eq1 => by
  induction x with | _ a b
  induction y with | _ a' b'
  simp only [fromLocalizedModule_mk] at eq1
  rw [Module.End.algebraMap_isUnit_inv_apply_eq_iff, ← map_smul,
    Module.End.algebraMap_isUnit_inv_apply_eq_iff'] at eq1
  rw [LocalizedModule.mk_eq, ← IsLocalizedModule.eq_iff_exists S f, Submonoid.smul_def,
    Submonoid.smul_def, f.map_smul, f.map_smul, eq1]
/-
**IsLocalizedModule.fromLocalizedModule.surj** 是 Mathlib 中的一个定理，位于命名空间 `IsLocali
zedModule.fromLocalizedModule`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] (S : Submonoid R) {M : Type u_2} 
{M' : Type u_3} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid M'] [inst_3
 : _root_.Module R M] [inst_4 : _root_.Module R M'] (f : M →ₗ[R] M')   [inst_5 :
 IsLocalizedModule S f], Function.Surjective ⇑(IsLocalizedModule.fromLocalizedMo
dule S f)
参数：S : Submonoid R；f : M →ₗ[R] M'；IsLocalizedModule.fromLocalizedModule S f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsLocalizedModule.surj`：∀ {R : Type u_1} {inst : CommSemiring R} {M : Ty
pe u_2} {M' : Type u_3} {inst_1 : AddCommMonoid M}   {inst_2 : AddCommMonoid M'}
 {inst_3 : _…
· 使用定理 `IsLocalizedModule.map_units`：∀ {R : Type u_1} {inst : CommSemiring R} {M
 : Type u_2} {M' : Type u_3} {inst_1 : AddCommMonoid M}   {inst_2 : AddCommMonoi
d M'} {inst_3 : _…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsLocalizedModule.fromLocalizedModule_mk`：fromLocalizedModule_mk (m : M)
 (s : S) : fromLocalizedModule S f (LocalizedModule.mk m s) = (IsLocalizedModule
.map_units f s).unit⁻¹.val (f …
· 使用定理 `Module.End.algebraMap_isUnit_inv_apply_eq_iff`：∀ {R : Type u} (S : Type 
v) {M : Type w} [inst : CommSemiring R] [inst_1 : Semiring S] [inst_2 : AddCommM
onoid M]   [inst_3 : _root_.Module …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submonoid.smul_def`：∀ {M' : Type u_1} {α : Type u_2} [inst : MulOneClass
 M'] [inst_1 : SMul M' α] {S : Submonoid M'} (g : ↥S) (a : α),   g • a = ↑g • a
-/
theorem fromLocalizedModule.surj : Function.Surjective <| fromLocalizedModule S f := fun x =>
  let ⟨⟨m, s⟩, eq1⟩ := IsLocalizedModule.surj S f x
  ⟨LocalizedModule.mk m s, by
    rw [fromLocalizedModule_mk, Module.End.algebraMap_isUnit_inv_apply_eq_iff, ← eq1,
      Submonoid.smul_def]⟩
/-
**IsLocalizedModule.fromLocalizedModule.bij** 是 Mathlib 中的一个定理，位于命名空间 `IsLocaliz
edModule.fromLocalizedModule`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] (S : Submonoid R) {M : Type u_2} 
{M' : Type u_3} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid M'] [inst_3
 : _root_.Module R M] [inst_4 : _root_.Module R M'] (f : M →ₗ[R] M')   [inst_5 :
 IsLocalizedModule S f], Function.Bijective ⇑(IsLocalizedModule.fromLocalizedMod
ule S f)
参数：S : Submonoid R；f : M →ₗ[R] M'；IsLocalizedModule.fromLocalizedModule S f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsLocalizedModule.fromLocalizedModule.inj`：∀ {R : Type u_1} [inst : Comm
Semiring R] (S : Submonoid R) {M : Type u_2} {M' : Type u_3} [inst_1 : AddCommMo
noid M]   [inst_2 : AddCommMono…
· 使用定理 `IsLocalizedModule.fromLocalizedModule.surj`：∀ {R : Type u_1} [inst : Com
mSemiring R] (S : Submonoid R) {M : Type u_2} {M' : Type u_3} [inst_1 : AddCommM
onoid M]   [inst_2 : AddCommMono…
-/
theorem fromLocalizedModule.bij : Function.Bijective <| fromLocalizedModule S f :=
  ⟨fromLocalizedModule.inj _ _, fromLocalizedModule.surj _ _⟩

/--
If `(M', f : M ⟶ M')` satisfies universal property of localized module, then `M'` is isomorphic to
`LocalizedModule S M` as an `R`-module.
-/
/-
**IsLocalizedModule.iso** 是 Mathlib 中的一个定义，位于命名空间 `IsLocalizedModule`。
形式化陈述：iso : LocalizedModule S M ≃ₗ[R] M'
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalizedModule.fromLocalizedModule.bij`：∀ {R : Type u_1} [inst : Comm
Semiring R] (S : Submonoid R) {M : Type u_2} {M' : Type u_3} [inst_1 : AddCommMo
noid M]   [inst_2 : AddCommMono…

--- 原说明 ---
If `(M', f : M ⟶ M')` satisfies universal property of localized module, then `M'
` is isomorphic to
`LocalizedModule S M` as an `R`-module.
-/
noncomputable def iso : LocalizedModule S M ≃ₗ[R] M' :=
  { fromLocalizedModule S f,
    Equiv.ofBijective (fromLocalizedModule S f) <| fromLocalizedModule.bij _ _ with }
/-
**IsLocalizedModule.iso_apply_mk** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalizedModule`。
形式化陈述：iso_apply_mk (m : M) (s : S) : iso S f (LocalizedModule.mk m s) = (IsLocal
izedModule.map_units f s).unit⁻¹.val (f m)
参数：m : M；s : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
theorem iso_apply_mk (m : M) (s : S) :
    iso S f (LocalizedModule.mk m s) = (IsLocalizedModule.map_units f s).unit⁻¹.val (f m) :=
  rfl

@[simp]
/-
**IsLocalizedModule.iso_mk_one** 是 Mathlib 中的一个引理，位于命名空间 `IsLocalizedModule`。
形式化陈述：iso_mk_one (x : M) : (iso S f) (LocalizedModule.mk x 1) = f x
参数：x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsLocalizedModule.map_units`：∀ {R : Type u_1} {inst : CommSemiring R} {M
 : Type u_2} {M' : Type u_3} {inst_1 : AddCommMonoid M}   {inst_2 : AddCommMonoi
d M'} {inst_3 : _…
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
· 使用定理 `IsUnit.unit.congr_simp`：∀ {M : Type u_1} [inst : Monoid M] {a a_1 : M} (
e_a : a = a_1) (h : IsUnit a), h.unit = ⋯.unit
· 使用定理 `IsUnit.unit_one`：unit_one (h : IsUnit (1 : M)) : h.unit = 1
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma iso_mk_one (x : M) : (iso S f) (LocalizedModule.mk x 1) = f x := by
  simp [iso_apply_mk]
/-
**IsLocalizedModule.iso_symm_apply_aux** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalizedMod
ule`。
形式化陈述：iso_symm_apply_aux (m : M') : (iso S f).symm m = LocalizedModule.mk (IsLoc
alizedModule.surj S f m).choose.1 (IsLocalizedModule.surj S f m).choose.2
参数：m : M'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsLocalizedModule.surj`：∀ {R : Type u_1} {inst : CommSemiring R} {M : Ty
pe u_2} {M' : Type u_3} {inst_1 : AddCommMonoid M}   {inst_2 : AddCommMonoid M'}
 {inst_3 : _…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.apply_symm_apply`：apply_symm_apply (c : M₂) : e (e.symm c) =
 c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsLocalizedModule.map_units`：∀ {R : Type u_1} {inst : CommSemiring R} {M
 : Type u_2} {M' : Type u_3} {inst_1 : AddCommMonoid M}   {inst_2 : AddCommMonoi
d M'} {inst_3 : _…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iso_symm_apply_aux (m : M') :
    (iso S f).symm m =
      LocalizedModule.mk (IsLocalizedModule.surj S f m).choose.1
        (IsLocalizedModule.surj S f m).choose.2 := by
  apply_fun iso S f using LinearEquiv.injective (iso S f)
  rw [LinearEquiv.apply_symm_apply]
  simp [iso, fromLocalizedModule, Module.End.algebraMap_isUnit_inv_apply_eq_iff',
    ← Submonoid.smul_def, (surj _ _ _).choose_spec]
/-
**IsLocalizedModule.iso_symm_apply'** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalizedModule
`。
形式化陈述：iso_symm_apply' (m : M') (a : M) (b : S) (eq1 : b • m = f a) : (iso S f).s
ymm m = LocalizedModule.mk a b
参数：m : M'；a : M；b : S；eq1 : b • m = f a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsLocalizedModule.surj`：∀ {R : Type u_1} {inst : CommSemiring R} {M : Ty
pe u_2} {M' : Type u_3} {inst_1 : AddCommMonoid M}   {inst_2 : AddCommMonoid M'}
 {inst_3 : _…
· 使用定理 `IsLocalizedModule.iso_symm_apply_aux`：iso_symm_apply_aux (m : M') : (iso
 S f).symm m = LocalizedModule.mk (IsLocalizedModule.surj S f m).choose.1 (IsLoc
alizedModule.surj S f m).c…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LocalizedModule.mk_eq`：mk_eq {m m' : M} {s s' : S} : mk m s = mk m' s' ↔
 exists u : S, u • s' • m = u • s • m'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `IsLocalizedModule.eq_iff_exists`：IsLocalizedModule.eq_iff_exists [IsLoca
lizedModule S f] {x₁ x₂} : f x₁ = f x₂ ↔ exists c : S, c • x₁ = c • x₂
· 使用定理 `Submonoid.smul_def`：∀ {M' : Type u_1} {α : Type u_2} [inst : MulOneClass
 M'] [inst_1 : SMul M' α] {S : Submonoid M'} (g : ↥S) (a : α),   g • a = ↑g • a
· 使用定理 `LinearMap.map_smul`：∀ {R : Type u_1} {M : Type u_8} {M₂ : Type u_10} [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid M₂] [inst_
3 : _roo…
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem iso_symm_apply' (m : M') (a : M) (b : S) (eq1 : b • m = f a) :
    (iso S f).symm m = LocalizedModule.mk a b :=
  (iso_symm_apply_aux S f m).trans <|
    LocalizedModule.mk_eq.mpr <| by
      rw [← IsLocalizedModule.eq_iff_exists S f, Submonoid.smul_def, Submonoid.smul_def, f.map_smul,
        f.map_smul, ← (surj _ _ _).choose_spec, ← Submonoid.smul_def, ← Submonoid.smul_def,
        ← mul_smul, mul_comm, mul_smul, eq1]
/-
**IsLocalizedModule.iso_symm_comp** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalizedModule`。
形式化陈述：iso_symm_comp : (iso S f).symm.toLinearMap.comp f = LocalizedModule.mkLine
arMap S M
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.comp_apply`：comp_apply (x : M₁) : f.comp g x = f (g x)
· 使用定理 `LocalizedModule.mkLinearMap_apply`：∀ {R : Type u} [inst : CommSemiring R
] (S : Submonoid R) (M : Type v) [inst_1 : AddCommMonoid M]   [inst_2 : _root_.M
odule R M] (m : M), (Lo…
· 使用定理 `LinearEquiv.coe_coe`：coe_coe : ⇑(e : M ->ₛₗ[σ] M₂) = e
· 使用定理 `IsLocalizedModule.iso_symm_apply'`：iso_symm_apply' (m : M') (a : M) (b :
 S) (eq1 : b • m = f a) : (iso S f).symm m = LocalizedModule.mk a b
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
theorem iso_symm_comp : (iso S f).symm.toLinearMap.comp f = LocalizedModule.mkLinearMap S M := by
  ext m
  rw [LinearMap.comp_apply, LocalizedModule.mkLinearMap_apply, LinearEquiv.coe_coe, iso_symm_apply']
  exact one_smul _ _

@[simp]
/-
**IsLocalizedModule.iso_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 `IsLocalizedModule`
。
形式化陈述：iso_symm_apply (x) : (iso S f).symm (f x) = LocalizedModule.mk x 1
参数：x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsLocalizedModule.iso_symm_comp`：iso_symm_comp : (iso S f).symm.toLinear
Map.comp f = LocalizedModule.mkLinearMap S M
-/
lemma iso_symm_apply (x) : (iso S f).symm (f x) = LocalizedModule.mk x 1 :=
  DFunLike.congr_fun (iso_symm_comp S f) x

/--
If `M'` is a localized module and `g` is a linear map `M → M''` such that all scalar multiplication
by `s : S` is invertible, then there is a linear map `M' → M''`.
-/
/-
**IsLocalizedModule.lift** 是 Mathlib 中的一个定义，位于命名空间 `IsLocalizedModule`。
形式化陈述：lift (g : M ->ₗ[R] M'') (h : forall x : S, IsUnit ((algebraMap R (Module.E
nd R M'')) x)) : M' ->ₗ[R] M''
参数：g : M ->ₗ[R] M''；h : forall x : S, IsUnit ((algebraMap R (Module.End R M'')) 
x)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `M'` is a localized module and `g` is a linear map `M → M''` such that all sc
alar multiplication
by `s : S` is invertible, then there is a linear map `M' → M''`.
-/
noncomputable def lift (g : M →ₗ[R] M'')
    (h : ∀ x : S, IsUnit ((algebraMap R (Module.End R M'')) x)) : M' →ₗ[R] M'' :=
  (LocalizedModule.lift S g h).comp (iso S f).symm.toLinearMap
/-
**IsLocalizedModule.lift_comp** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalizedModule`。
形式化陈述：lift_comp (g : M ->ₗ[R] M'') (h : forall x : S, IsUnit ((algebraMap R (Mod
ule.End R M'')) x)) : (lift S f g h).comp f = g
参数：g : M ->ₗ[R] M''；h : forall x : S, IsUnit ((algebraMap R (Module.End R M'')) 
x)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.comp_assoc`：comp_assoc {R₄ M₄ : Type*} [Semiring R₄] [AddCommM
onoid M₄] [Module R₄ M₄] {σ₃₄ : R₃ ->+* R₄} {σ₂₄ : R₂ ->+* R₄} {σ₁₄ : R₁ ->+* R₄
} [RingHom…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsLocalizedModule.iso_symm_comp`：iso_symm_comp : (iso S f).symm.toLinear
Map.comp f = LocalizedModule.mkLinearMap S M
· 使用定理 `LocalizedModule.lift_comp`：lift_comp (g : M ->ₗ[R] M'') (h : forall x : 
S, IsUnit ((algebraMap R (Module.End R M'')) x)) : (lift S g h).comp (mkLinearMa
p S M) = g
-/
theorem lift_comp (g : M →ₗ[R] M'') (h : ∀ x : S, IsUnit ((algebraMap R (Module.End R M'')) x)) :
    (lift S f g h).comp f = g := by
  dsimp only [IsLocalizedModule.lift]
  rw [LinearMap.comp_assoc, iso_symm_comp, LocalizedModule.lift_comp S g h]

@[simp]
/-
**IsLocalizedModule.lift_iso** 是 Mathlib 中的一个引理，位于命名空间 `IsLocalizedModule`。
形式化陈述：lift_iso (h : forall (x : S), IsUnit ((algebraMap R (Module.End R M'')) x)
) (x : LocalizedModule S M) : IsLocalizedModule.lift S f g h ((iso S f) x) = Loc
alizedModule.lift S g h x
参数：h : forall (x : S), IsUnit ((algebraMap R (Module.End R M'')) x)；x : Localize
dModule S M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.symm_apply_apply`：symm_apply_apply (b : M) : e.symm (e b) = 
b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma lift_iso (h : ∀ (x : S), IsUnit ((algebraMap R (Module.End R M'')) x))
    (x : LocalizedModule S M) :
    IsLocalizedModule.lift S f g h ((iso S f) x) = LocalizedModule.lift S g h x := by
  simp [lift]

@[simp]
/-
**IsLocalizedModule.lift_comp_iso** 是 Mathlib 中的一个引理，位于命名空间 `IsLocalizedModule`。
形式化陈述：lift_comp_iso (h : forall (x : S), IsUnit ((algebraMap R (Module.End R M''
)) x)) : IsLocalizedModule.lift S f g h ∘ₗ iso S f = LocalizedModule.lift S g h
参数：h : forall (x : S), IsUnit ((algebraMap R (Module.End R M'')) x)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `IsLocalizedModule.lift_iso`：lift_iso (h : forall (x : S), IsUnit ((algeb
raMap R (Module.End R M'')) x)) (x : LocalizedModule S M) : IsLocalizedModule.li
ft S f g h ((iso…
-/
lemma lift_comp_iso (h : ∀ (x : S), IsUnit ((algebraMap R (Module.End R M'')) x)) :
    IsLocalizedModule.lift S f g h ∘ₗ iso S f = LocalizedModule.lift S g h :=
  LinearMap.ext fun x ↦ lift_iso S f g h x

@[simp]
/-
**IsLocalizedModule.lift_apply** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalizedModule`。
形式化陈述：lift_apply (g : M ->ₗ[R] M'') (h) (x) : lift S f g h (f x) = g x
参数：g : M ->ₗ[R] M''；h；x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.congr_fun`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ 
: Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid
 M] [inst…
· 使用定理 `IsLocalizedModule.lift_comp`：lift_comp (g : M ->ₗ[R] M'') (h : forall x 
: S, IsUnit ((algebraMap R (Module.End R M'')) x)) : (lift S f g h).comp f = g
-/
theorem lift_apply (g : M →ₗ[R] M'') (h) (x) :
    lift S f g h (f x) = g x := LinearMap.congr_fun (lift_comp S f g h) x
/-
**IsLocalizedModule.lift_unique** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalizedModule`。
形式化陈述：lift_unique (g : M ->ₗ[R] M'') (h : forall x : S, IsUnit ((algebraMap R (M
odule.End R M'')) x)) (l : M' ->ₗ[R] M'') (hl : l.comp f = g) : lift S f g h = l
参数：g : M ->ₗ[R] M''；h : forall x : S, IsUnit ((algebraMap R (Module.End R M'')) 
x)；l : M' ->ₗ[R] M''；hl : l.comp f = g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LocalizedModule.lift_unique`：lift_unique (g : M ->ₗ[R] M'') (h : forall 
x : S, IsUnit ((algebraMap R (Module.End R M'')) x)) (l : LocalizedModule S M ->
ₗ[R] M'') (hl : l…
· 使用定理 `LinearMap.comp_assoc`：comp_assoc {R₄ M₄ : Type*} [Semiring R₄] [AddCommM
onoid M₄] [Module R₄ M₄] {σ₃₄ : R₃ ->+* R₄} {σ₂₄ : R₂ ->+* R₄} {σ₁₄ : R₁ ->+* R₄
} [RingHom…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LocalizedModule.mkLinearMap_apply`：∀ {R : Type u} [inst : CommSemiring R
] (S : Submonoid R) (M : Type v) [inst_1 : AddCommMonoid M]   [inst_2 : _root_.M
odule R M] (m : M), (Lo…
· 使用引理 `IsLocalizedModule.iso_mk_one`：iso_mk_one (x : M) : (iso S f) (LocalizedM
odule.mk x 1) = f x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LinearEquiv.comp_coe`：comp_coe (f : M₁ ≃ₛₗ[σ₁₂] M₂) (f' : M₂ ≃ₛₗ[σ₂₃] M₃
) : (f' : M₂ ->ₛₗ[σ₂₃] M₃).comp (f : M₁ ->ₛₗ[σ₁₂] M₂) = (f.trans f' : M₁ ≃ₛₗ[σ₁₃
] M₃)
· 使用定理 `LinearEquiv.symm_trans_self`：symm_trans_self (f : M₁ ≃ₛₗ[σ₁₂] M₂) : f.sy
mm.trans f = LinearEquiv.refl R₂ M₂
· 使用定理 `LinearEquiv.refl_toLinearMap`：refl_toLinearMap [Module R M] : (LinearEqu
iv.refl R M : M ->ₗ[R] M) = LinearMap.id
· 使用定理 `LinearMap.comp_id`：comp_id : f.comp id = f
-/
theorem lift_unique (g : M →ₗ[R] M'') (h : ∀ x : S, IsUnit ((algebraMap R (Module.End R M'')) x))
    (l : M' →ₗ[R] M'') (hl : l.comp f = g) : lift S f g h = l := by
  dsimp only [IsLocalizedModule.lift]
  rw [LocalizedModule.lift_unique S g h (l.comp (iso S f).toLinearMap), LinearMap.comp_assoc,
    LinearEquiv.comp_coe, LinearEquiv.symm_trans_self, LinearEquiv.refl_toLinearMap,
    LinearMap.comp_id]
  rw [LinearMap.comp_assoc, ← hl]
  ext x
  simp

/-- Universal property from localized module:
If `(M', f : M ⟶ M')` is a localized module then it satisfies the following universal property:
For every `R`-module `M''` which every `s : S`-scalar multiplication is invertible and for every
`R`-linear map `g : M ⟶ M''`, there is a unique `R`-linear map `l : M' ⟶ M''` such that
`l ∘ f = g`.
```
M -----f----> M'
|           /
|g       /
|     /   l
v   /
M''
```
-/
/-
**IsLocalizedModule.is_universal** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalizedModule`。
形式化陈述：is_universal : forall (g : M ->ₗ[R] M'') (_ : forall x : S, IsUnit ((algeb
raMap R (Module.End R M'')) x)), exists! l : M' ->ₗ[R] M'', l.comp f = g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalizedModule.lift_comp`：lift_comp (g : M ->ₗ[R] M'') (h : forall x 
: S, IsUnit ((algebraMap R (Module.End R M'')) x)) : (lift S f g h).comp f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsLocalizedModule.lift_unique`：lift_unique (g : M ->ₗ[R] M'') (h : foral
l x : S, IsUnit ((algebraMap R (Module.End R M'')) x)) (l : M' ->ₗ[R] M'') (hl :
 l.comp f = g) : li…

--- 原说明 ---
Universal property from localized module:
If `(M', f : M ⟶ M')` is a localized module then it satisfies the following univ
ersal property:
For every `R`-module `M''` which every `s : S`-scalar multiplication is invertib
le and for every
`R`-linear map `g : M ⟶ M''`, there is a unique `R`-linear map `l : M' ⟶ M''` su
ch that
`l ∘ f = g`.
```
M -----f----> M'
|           /
|g       /
|     /   l
v   /
M''
```
-/
theorem is_universal :
    ∀ (g : M →ₗ[R] M'') (_ : ∀ x : S, IsUnit ((algebraMap R (Module.End R M'')) x)),
      ∃! l : M' →ₗ[R] M'', l.comp f = g :=
  fun g h => ⟨lift S f g h, lift_comp S f g h, fun l hl => (lift_unique S f g h l hl).symm⟩
/-
**IsLocalizedModule.linearMap_ext** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalizedModule`。
形式化陈述：linearMap_ext {N N'} [AddCommMonoid N] [Module R N] [AddCommMonoid N'] [Mo
dule R N'] (f' : N ->ₗ[R] N') [IsLocalizedModule S f'] ⦃g g' : M' ->ₗ[R] N'⦄ (h 
: g ∘ₗ f = g' ∘ₗ f) : g = g'
参数：f' : N ->ₗ[R] N'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ExistsUnique.unique`：ExistsUnique.unique {p : α -> Prop} (h : exists! x,
 p x) {y₁ y₂ : α} (py₁ : p y₁) (py₂ : p y₂) : y₁ = y₂
· 使用定理 `IsLocalizedModule.is_universal`：is_universal : forall (g : M ->ₗ[R] M'')
 (_ : forall x : S, IsUnit ((algebraMap R (Module.End R M'')) x)), exists! l : M
' ->ₗ[R] M'', l.comp…
· 使用定理 `IsLocalizedModule.map_units`：∀ {R : Type u_1} {inst : CommSemiring R} {M
 : Type u_2} {M' : Type u_3} {inst_1 : AddCommMonoid M}   {inst_2 : AddCommMonoi
d M'} {inst_3 : _…
-/
theorem linearMap_ext {N N'} [AddCommMonoid N] [Module R N] [AddCommMonoid N'] [Module R N']
    (f' : N →ₗ[R] N') [IsLocalizedModule S f'] ⦃g g' : M' →ₗ[R] N'⦄
    (h : g ∘ₗ f = g' ∘ₗ f) : g = g' :=
  (is_universal S f _ <| map_units f').unique h rfl
/-
**IsLocalizedModule.ext** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalizedModule`。
形式化陈述：ext (map_unit : forall x : S, IsUnit ((algebraMap R (Module.End R M'')) x)
) ⦃j k : M' ->ₗ[R] M''⦄ (h : j.comp f = k.comp f) : j = k
参数：map_unit : forall x : S, IsUnit ((algebraMap R (Module.End R M'')) x)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsLocalizedModule.lift_unique`：lift_unique (g : M ->ₗ[R] M'') (h : foral
l x : S, IsUnit ((algebraMap R (Module.End R M'')) x)) (l : M' ->ₗ[R] M'') (hl :
 l.comp f = g) : li…
-/
theorem ext (map_unit : ∀ x : S, IsUnit ((algebraMap R (Module.End R M'')) x))
    ⦃j k : M' →ₗ[R] M''⦄ (h : j.comp f = k.comp f) : j = k := by
  rw [← lift_unique S f (k.comp f) map_unit j h, lift_unique]
  rfl

/-- If `(M', f)` and `(M'', g)` both satisfy universal property of localized module, then `M', M''`
are isomorphic as `R`-module
-/
/-
**IsLocalizedModule.linearEquiv** 是 Mathlib 中的一个定义，位于命名空间 `IsLocalizedModule`。
形式化陈述：linearEquiv [IsLocalizedModule S g] : M' ≃ₗ[R] M''
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `(M', f)` and `(M'', g)` both satisfy universal property of localized module,
 then `M', M''`
are isomorphic as `R`-module
-/
noncomputable def linearEquiv [IsLocalizedModule S g] : M' ≃ₗ[R] M'' :=
  (iso S f).symm.trans (iso S g)

@[simp]
/-
**IsLocalizedModule.linearEquiv_apply** 是 Mathlib 中的一个引理，位于命名空间 `IsLocalizedModu
le`。
形式化陈述：linearEquiv_apply [IsLocalizedModule S g] (x : M) : (linearEquiv S f g) (f
 x) = g x
参数：x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `IsLocalizedModule.iso_symm_apply`：iso_symm_apply (x) : (iso S f).symm (f
 x) = LocalizedModule.mk x 1
· 使用引理 `IsLocalizedModule.iso_mk_one`：iso_mk_one (x : M) : (iso S f) (LocalizedM
odule.mk x 1) = f x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma linearEquiv_apply [IsLocalizedModule S g] (x : M) :
    (linearEquiv S f g) (f x) = g x := by
  simp [linearEquiv]

@[simp]
/-
**IsLocalizedModule.linearEquiv_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 `IsLocalize
dModule`。
形式化陈述：linearEquiv_symm_apply [IsLocalizedModule S g] (x : M) : (linearEquiv S f 
g).symm (g x) = f x
参数：x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `IsLocalizedModule.iso_symm_apply`：iso_symm_apply (x) : (iso S f).symm (f
 x) = LocalizedModule.mk x 1
· 使用引理 `IsLocalizedModule.iso_mk_one`：iso_mk_one (x : M) : (iso S f) (LocalizedM
odule.mk x 1) = f x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma linearEquiv_symm_apply [IsLocalizedModule S g] (x : M) :
    (linearEquiv S f g).symm (g x) = f x := by
  simp [linearEquiv]
/-
**IsLocalizedModule.linearEquiv_of_isLocalizedModule_comp** 是 Mathlib 中的一个引理，位于命
名空间 `IsLocalizedModule`。
形式化陈述：linearEquiv_of_isLocalizedModule_comp (g : M' ->ₗ[R] M'') [IsLocalizedModu
le S (g ∘ₗ f)] : linearEquiv S f (g ∘ₗ f) = g
参数：g : M' ->ₗ[R] M''；g ∘ₗ f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalizedModule.ext`：ext (map_unit : forall x : S, IsUnit ((algebraMap
 R (Module.End R M'')) x)) ⦃j k : M' ->ₗ[R] M''⦄ (h : j.comp f = k.comp f) : j =
 k
· 使用定理 `IsLocalizedModule.map_units`：∀ {R : Type u_1} {inst : CommSemiring R} {M
 : Type u_2} {M' : Type u_3} {inst_1 : AddCommMonoid M}   {inst_2 : AddCommMonoi
d M'} {inst_3 : _…
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `IsLocalizedModule.linearEquiv_apply`：linearEquiv_apply [IsLocalizedModul
e S g] (x : M) : (linearEquiv S f g) (f x) = g x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma linearEquiv_of_isLocalizedModule_comp (g : M' →ₗ[R] M'') [IsLocalizedModule S (g ∘ₗ f)] :
    linearEquiv S f (g ∘ₗ f) = g  := by
  refine ext S f (IsLocalizedModule.map_units (g ∘ₗ f)) ?_
  ext
  simp

variable {S}

include f in
/-
**IsLocalizedModule.smul_injective** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalizedModule`
。
形式化陈述：smul_injective (s : S) : Function.Injective fun m : M' => s • m
参数：s : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Bijective.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β
}, Function.Bijective f → Function.Injective f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Module.End.isUnit_iff`：∀ {R : Type u_1} {M : Type u_5} [inst : Semiring 
R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (f : Module.End R M
), IsUnit f…
· 使用定理 `IsLocalizedModule.map_units`：∀ {R : Type u_1} {inst : CommSemiring R} {M
 : Type u_2} {M' : Type u_3} {inst_1 : AddCommMonoid M}   {inst_2 : AddCommMonoi
d M'} {inst_3 : _…
-/
theorem smul_injective (s : S) : Function.Injective fun m : M' => s • m :=
  ((Module.End.isUnit_iff _).mp (IsLocalizedModule.map_units f s)).injective

include f in
/-
**IsLocalizedModule.smul_inj** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalizedModule`。
形式化陈述：smul_inj (s : S) (m₁ m₂ : M') : s • m₁ = s • m₂ ↔ m₁ = m₂
参数：s : S；m₁ m₂ : M'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `IsLocalizedModule.smul_injective`：smul_injective (s : S) : Function.Inje
ctive fun m : M' => s • m
-/
theorem smul_inj (s : S) (m₁ m₂ : M') : s • m₁ = s • m₂ ↔ m₁ = m₂ :=
  (smul_injective f s).eq_iff

include f in
/-
**IsLocalizedModule.isRegular_of_smul_left_injective** 是 Mathlib 中的一个引理，位于命名空间 `
IsLocalizedModule`。
形式化陈述：isRegular_of_smul_left_injective {m : M'} (inj : Function.Injective fun r 
: R => r • m) (s : S) : IsRegular (s : R)
参数：inj : Function.Injective fun r : R => r • m；s : S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Commute.isRegular_iff`：Commute.isRegular_iff {a : R} (ca : forall b, Com
mute a b) : IsRegular a ↔ IsLeftRegular a
· 使用定理 `Commute.all`：∀ {S : Type u_3} [inst : CommMagma S] (a b : S), Commute a 
b
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `IsLocalizedModule.smul_inj`：smul_inj (s : S) (m₁ m₂ : M') : s • m₁ = s •
 m₂ ↔ m₁ = m₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
-/
lemma isRegular_of_smul_left_injective {m : M'} (inj : Function.Injective fun r : R ↦ r • m)
    (s : S) : IsRegular (s : R) :=
  (Commute.isRegular_iff (Commute.all _)).mpr fun r r' eq ↦ by
    have := congr_arg (· • m) eq
    simp_rw [mul_smul, ← Submonoid.smul_def, smul_inj f] at this
    exact inj this

/-- `mk' f m s` is the fraction `m/s` with respect to the localization map `f`. -/
/-
**IsLocalizedModule.mk'** 是 Mathlib 中的一个定义，位于命名空间 `IsLocalizedModule`。
形式化陈述：mk' (m : M) (s : S) : M'
参数：m : M；s : S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`mk' f m s` is the fraction `m/s` with respect to the localization map `f`.
-/
noncomputable def mk' (m : M) (s : S) : M' :=
  fromLocalizedModule S f (LocalizedModule.mk m s)
/-
**IsLocalizedModule.mk'_smul** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalizedModule`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {S : Submonoid R} {M : Type u_2} 
{M' : Type u_3} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid M'] [inst_3
 : _root_.Module R M] [inst_4 : _root_.Module R M'] (f : M →ₗ[R] M')   [inst_5 :
 IsLocalizedModule S f] {R₀ : Type u_6} [inst_6 : SMul R₀ R] [inst_7 : SMul R₀ M
] [inst_8 : SMul R₀ M']   [IsScalarTower R₀ R R] [IsScalarTower R₀ R M] [IsScala
rTower R₀ R M'] (r : R₀) (m : M) (s : ↥S),   IsLocalizedModule.mk' f (r • m) s =
 r • IsLocalizedModule.mk' f m s
参数：f : M →ₗ[R] M'；r : R₀；m : M；s : ↥S；r • m。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LocalizedModule.smul'_mk`：∀ {R : Type u} [inst : CommSemiring R] {S : Su
bmonoid R} {M : Type v} [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M
] {R₀ : Type u…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `LinearMap.map_smul_of_tower`：map_smul_of_tower [CompatibleSMul M M₂ R S]
 (fₗ : M ->ₗ[S] M₂) (c : R) (x : M) : fₗ (c • x) = c • fₗ x
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
-/
theorem mk'_smul {R₀ : Type*} [SMul R₀ R] [SMul R₀ M] [SMul R₀ M']
    [IsScalarTower R₀ R R] [IsScalarTower R₀ R M] [IsScalarTower R₀ R M']
    (r : R₀) (m : M) (s : S) : mk' f (r • m) s = r • mk' f m s := by
  delta mk'
  rw [← LocalizedModule.smul'_mk, LinearMap.map_smul_of_tower]
/-
**IsLocalizedModule.mk'_add_mk'** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalizedModule`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {S : Submonoid R} {M : Type u_2} 
{M' : Type u_3} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid M'] [inst_3
 : _root_.Module R M] [inst_4 : _root_.Module R M'] (f : M →ₗ[R] M')   [inst_5 :
 IsLocalizedModule S f] (m₁ m₂ : M) (s₁ s₂ : ↥S),   IsLocalizedModule.mk' f m₁ s
₁ + IsLocalizedModule.mk' f m₂ s₂ = IsLocalizedModule.mk' f (s₂ • m₁ + s₁ • m₂) 
(s₁ * s₂)
参数：f : M →ₗ[R] M'；m₁ m₂ : M；s₁ s₂ : ↥S；s₂ • m₁ + s₁ • m₂；s₁ * s₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `LocalizedModule.mk_add_mk`：mk_add_mk {m1 m2 : M} {s1 s2 : S} : mk m1 s1 
+ mk m2 s2 = mk (s2 • m1 + s1 • m2) (s1 * s2)
-/
theorem mk'_add_mk' (m₁ m₂ : M) (s₁ s₂ : S) :
    mk' f m₁ s₁ + mk' f m₂ s₂ = mk' f (s₂ • m₁ + s₁ • m₂) (s₁ * s₂) := by
  delta mk'
  rw [← map_add, LocalizedModule.mk_add_mk]

@[simp]
/-
**IsLocalizedModule.mk'_zero** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalizedModule`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {S : Submonoid R} {M : Type u_2} 
{M' : Type u_3} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid M'] [inst_3
 : _root_.Module R M] [inst_4 : _root_.Module R M'] (f : M →ₗ[R] M')   [inst_5 :
 IsLocalizedModule S f] (s : ↥S), IsLocalizedModule.mk' f 0 s = 0
参数：f : M →ₗ[R] M'；s : ↥S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `IsLocalizedModule.mk'_smul`：∀ {R : Type u_1} [inst : CommSemiring R] {S 
: Submonoid R} {M : Type u_2} {M' : Type u_3} [inst_1 : AddCommMonoid M]   [inst
_2 : AddCommMono…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
theorem mk'_zero (s : S) : mk' f 0 s = 0 := by rw [← zero_smul R (0 : M), mk'_smul, zero_smul]

variable (S) in
@[simp]
/-
**IsLocalizedModule.mk'_one** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalizedModule`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] (S : Submonoid R) {M : Type u_2} 
{M' : Type u_3} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid M'] [inst_3
 : _root_.Module R M] [inst_4 : _root_.Module R M'] (f : M →ₗ[R] M')   [inst_5 :
 IsLocalizedModule S f] (m : M), IsLocalizedModule.mk' f m 1 = f m
参数：S : Submonoid R；f : M →ₗ[R] M'；m : M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalizedModule.map_units`：∀ {R : Type u_1} {inst : CommSemiring R} {M
 : Type u_2} {M' : Type u_3} {inst_1 : AddCommMonoid M}   {inst_2 : AddCommMonoi
d M'} {inst_3 : _…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsLocalizedModule.fromLocalizedModule_mk`：fromLocalizedModule_mk (m : M)
 (s : S) : fromLocalizedModule S f (LocalizedModule.mk m s) = (IsLocalizedModule
.map_units f s).unit⁻¹.val (f …
· 使用定理 `Module.End.algebraMap_isUnit_inv_apply_eq_iff`：∀ {R : Type u} (S : Type 
v) {M : Type w} [inst : CommSemiring R] [inst_1 : Semiring S] [inst_2 : AddCommM
onoid M]   [inst_3 : _root_.Module …
· 使用定理 `Submonoid.coe_one`：coe_one : ((1 : S) : M) = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
theorem mk'_one (m : M) : mk' f m (1 : S) = f m := by
  delta mk'
  rw [fromLocalizedModule_mk, Module.End.algebraMap_isUnit_inv_apply_eq_iff, Submonoid.coe_one,
    one_smul]

@[simp]
/-
**IsLocalizedModule.mk'_cancel** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalizedModule`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {S : Submonoid R} {M : Type u_2} 
{M' : Type u_3} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid M'] [inst_3
 : _root_.Module R M] [inst_4 : _root_.Module R M'] (f : M →ₗ[R] M')   [inst_5 :
 IsLocalizedModule S f] (m : M) (s : ↥S), IsLocalizedModule.mk' f (s • m) s = f 
m
参数：f : M →ₗ[R] M'；m : M；s : ↥S；s • m。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LocalizedModule.mk_cancel`：mk_cancel (s : S) (m : M) : mk (s • m) s = mk
 m 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsLocalizedModule.mk'_one`：∀ {R : Type u_1} [inst : CommSemiring R] (S :
 Submonoid R) {M : Type u_2} {M' : Type u_3} [inst_1 : AddCommMonoid M]   [inst_
2 : AddCommMono…
· 使用定理 `IsLocalizedModule.map_units`：∀ {R : Type u_1} {inst : CommSemiring R} {M
 : Type u_2} {M' : Type u_3} {inst_1 : AddCommMonoid M}   {inst_2 : AddCommMonoi
d M'} {inst_3 : _…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsLocalizedModule.fromLocalizedModule_mk`：fromLocalizedModule_mk (m : M)
 (s : S) : fromLocalizedModule S f (LocalizedModule.mk m s) = (IsLocalizedModule
.map_units f s).unit⁻¹.val (f …
· 使用定理 `Module.End.algebraMap_isUnit_inv_apply_eq_iff`：∀ {R : Type u} (S : Type 
v) {M : Type w} [inst : CommSemiring R] [inst_1 : Semiring S] [inst_2 : AddCommM
onoid M]   [inst_3 : _root_.Module …
· 使用定理 `SubmonoidClass.toOneMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   On
eMemClass S M
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `OneMemClass.coe_one`：coe_one : ((1 : S') : M₁) = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
theorem mk'_cancel (m : M) (s : S) : mk' f (s • m) s = f m := by
  delta mk'
  rw [LocalizedModule.mk_cancel, ← mk'_one S f, fromLocalizedModule_mk,
    Module.End.algebraMap_isUnit_inv_apply_eq_iff, OneMemClass.coe_one, mk'_one, one_smul]

@[simp]
/-
**IsLocalizedModule.mk'_cancel'** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalizedModule`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {S : Submonoid R} {M : Type u_2} 
{M' : Type u_3} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid M'] [inst_3
 : _root_.Module R M] [inst_4 : _root_.Module R M'] (f : M →ₗ[R] M')   [inst_5 :
 IsLocalizedModule S f] (m : M) (s : ↥S), s • IsLocalizedModule.mk' f m s = f m
参数：f : M →ₗ[R] M'；m : M；s : ↥S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submonoid.smul_def`：∀ {M' : Type u_1} {α : Type u_2} [inst : MulOneClass
 M'] [inst_1 : SMul M' α] {S : Submonoid M'} (g : ↥S) (a : α),   g • a = ↑g • a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsLocalizedModule.mk'_smul`：∀ {R : Type u_1} [inst : CommSemiring R] {S 
: Submonoid R} {M : Type u_2} {M' : Type u_3} [inst_1 : AddCommMonoid M]   [inst
_2 : AddCommMono…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsLocalizedModule.mk'_cancel`：∀ {R : Type u_1} [inst : CommSemiring R] {
S : Submonoid R} {M : Type u_2} {M' : Type u_3} [inst_1 : AddCommMonoid M]   [in
st_2 : AddCommMono…
-/
theorem mk'_cancel' (m : M) (s : S) : s • mk' f m s = f m := by
  rw [Submonoid.smul_def, ← mk'_smul, ← Submonoid.smul_def, mk'_cancel]

@[simp]
/-
**IsLocalizedModule.mk'_cancel_left** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalizedModule
`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {S : Submonoid R} {M : Type u_2} 
{M' : Type u_3} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid M'] [inst_3
 : _root_.Module R M] [inst_4 : _root_.Module R M'] (f : M →ₗ[R] M')   [inst_5 :
 IsLocalizedModule S f] (m : M) (s₁ s₂ : ↥S),   IsLocalizedModule.mk' f (s₁ • m)
 (s₁ * s₂) = IsLocalizedModule.mk' f m s₂
参数：f : M →ₗ[R] M'；m : M；s₁ s₂ : ↥S；s₁ • m；s₁ * s₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LocalizedModule.mk_cancel_common_left`：mk_cancel_common_left (s' s : S) 
(m : M) : mk (s' • m) (s' * s) = mk m s
-/
theorem mk'_cancel_left (m : M) (s₁ s₂ : S) : mk' f (s₁ • m) (s₁ * s₂) = mk' f m s₂ := by
  delta mk'
  rw [LocalizedModule.mk_cancel_common_left]

@[simp]
/-
**IsLocalizedModule.mk'_cancel_right** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalizedModul
e`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {S : Submonoid R} {M : Type u_2} 
{M' : Type u_3} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid M'] [inst_3
 : _root_.Module R M] [inst_4 : _root_.Module R M'] (f : M →ₗ[R] M')   [inst_5 :
 IsLocalizedModule S f] (m : M) (s₁ s₂ : ↥S),   IsLocalizedModule.mk' f (s₂ • m)
 (s₁ * s₂) = IsLocalizedModule.mk' f m s₁
参数：f : M →ₗ[R] M'；m : M；s₁ s₂ : ↥S；s₂ • m；s₁ * s₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LocalizedModule.mk_cancel_common_right`：mk_cancel_common_right (s s' : S
) (m : M) : mk (s' • m) (s * s') = mk m s
-/
theorem mk'_cancel_right (m : M) (s₁ s₂ : S) : mk' f (s₂ • m) (s₁ * s₂) = mk' f m s₁ := by
  delta mk'
  rw [LocalizedModule.mk_cancel_common_right]
/-
**IsLocalizedModule.mk'_add** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalizedModule`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {S : Submonoid R} {M : Type u_2} 
{M' : Type u_3} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid M'] [inst_3
 : _root_.Module R M] [inst_4 : _root_.Module R M'] (f : M →ₗ[R] M')   [inst_5 :
 IsLocalizedModule S f] (m₁ m₂ : M) (s : ↥S),   IsLocalizedModule.mk' f (m₁ + m₂
) s = IsLocalizedModule.mk' f m₁ s + IsLocalizedModule.mk' f m₂ s
参数：f : M →ₗ[R] M'；m₁ m₂ : M；s : ↥S；m₁ + m₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsLocalizedModule.mk'_add_mk'`：∀ {R : Type u_1} [inst : CommSemiring R] 
{S : Submonoid R} {M : Type u_2} {M' : Type u_3} [inst_1 : AddCommMonoid M]   [i
nst_2 : AddCommMono…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `IsLocalizedModule.mk'_cancel_left`：∀ {R : Type u_1} [inst : CommSemiring
 R] {S : Submonoid R} {M : Type u_2} {M' : Type u_3} [inst_1 : AddCommMonoid M] 
  [inst_2 : AddCommMono…
-/
theorem mk'_add (m₁ m₂ : M) (s : S) : mk' f (m₁ + m₂) s = mk' f m₁ s + mk' f m₂ s := by
  rw [mk'_add_mk', ← smul_add, mk'_cancel_left]
/-
**IsLocalizedModule.mk'_eq_mk'_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalizedModule`
。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {S : Submonoid R} {M : Type u_2} 
{M' : Type u_3} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid M'] [inst_3
 : _root_.Module R M] [inst_4 : _root_.Module R M'] (f : M →ₗ[R] M')   [inst_5 :
 IsLocalizedModule S f] (m₁ m₂ : M) (s₁ s₂ : ↥S),   IsLocalizedModule.mk' f m₁ s
₁ = IsLocalizedModule.mk' f m₂ s₂ ↔ ∃ s, s • s₁ • m₂ = s • s₂ • m₁
参数：f : M →ₗ[R] M'；m₁ m₂ : M；s₁ s₂ : ↥S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `IsLocalizedModule.fromLocalizedModule.inj`：∀ {R : Type u_1} [inst : Comm
Semiring R] (S : Submonoid R) {M : Type u_2} {M' : Type u_3} [inst_1 : AddCommMo
noid M]   [inst_2 : AddCommMono…
· 使用定理 `LocalizedModule.mk_eq`：mk_eq {m m' : M} {s s' : S} : mk m s = mk m' s' ↔
 exists u : S, u • s' • m = u • s • m'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mk'_eq_mk'_iff (m₁ m₂ : M) (s₁ s₂ : S) :
    mk' f m₁ s₁ = mk' f m₂ s₂ ↔ ∃ s : S, s • s₁ • m₂ = s • s₂ • m₁ := by
  delta mk'
  rw [(fromLocalizedModule.inj S f).eq_iff, LocalizedModule.mk_eq]
  simp_rw [eq_comm]
/-
**IsLocalizedModule.mk'_neg** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalizedModule`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {S : Submonoid R} {M : Type u_6} 
{M' : Type u_7} [inst_1 : AddCommGroup M]   [inst_2 : SubtractionCommMonoid M'] 
[inst_3 : _root_.Module R M] [inst_4 : _root_.Module R M'] (f : M →ₗ[R] M')   [i
nst_5 : IsLocalizedModule S f] (m : M) (s : ↥S), IsLocalizedModule.mk' f (-m) s 
= -IsLocalizedModule.mk' f m s
参数：f : M →ₗ[R] M'；m : M；s : ↥S；-m。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LocalizedModule.mk_neg`：mk_neg {M : Type*} [AddCommGroup M] [Module R M]
 {m : M} {s : S} : mk (-m) s = -mk m s
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
-/
theorem mk'_neg {M M' : Type*} [AddCommGroup M] [SubtractionCommMonoid M'] [Module R M]
    [Module R M'] (f : M →ₗ[R] M') [IsLocalizedModule S f] (m : M) (s : S) :
    mk' f (-m) s = -mk' f m s := by
  delta mk'
  rw [LocalizedModule.mk_neg, map_neg]
/-
**IsLocalizedModule.mk'_sub** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalizedModule`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {S : Submonoid R} {M : Type u_6} 
{M' : Type u_7} [inst_1 : AddCommGroup M]   [inst_2 : SubtractionCommMonoid M'] 
[inst_3 : _root_.Module R M] [inst_4 : _root_.Module R M'] (f : M →ₗ[R] M')   [i
nst_5 : IsLocalizedModule S f] (m₁ m₂ : M) (s : ↥S),   IsLocalizedModule.mk' f (
m₁ - m₂) s = IsLocalizedModule.mk' f m₁ s - IsLocalizedModule.mk' f m₂ s
参数：f : M →ₗ[R] M'；m₁ m₂ : M；s : ↥S；m₁ - m₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `IsLocalizedModule.mk'_add`：∀ {R : Type u_1} [inst : CommSemiring R] {S :
 Submonoid R} {M : Type u_2} {M' : Type u_3} [inst_1 : AddCommMonoid M]   [inst_
2 : AddCommMono…
· 使用定理 `IsLocalizedModule.mk'_neg`：∀ {R : Type u_1} [inst : CommSemiring R] {S :
 Submonoid R} {M : Type u_6} {M' : Type u_7} [inst_1 : AddCommGroup M]   [inst_2
 : SubtractionC…
-/
theorem mk'_sub {M M' : Type*} [AddCommGroup M] [SubtractionCommMonoid M'] [Module R M]
    [Module R M'] (f : M →ₗ[R] M') [IsLocalizedModule S f] (m₁ m₂ : M) (s : S) :
    mk' f (m₁ - m₂) s = mk' f m₁ s - mk' f m₂ s := by
  rw [sub_eq_add_neg, sub_eq_add_neg, mk'_add, mk'_neg]
/-
**IsLocalizedModule.mk'_sub_mk'** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalizedModule`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {S : Submonoid R} {M : Type u_6} 
{M' : Type u_7} [inst_1 : AddCommGroup M]   [inst_2 : SubtractionCommMonoid M'] 
[inst_3 : _root_.Module R M] [inst_4 : _root_.Module R M'] (f : M →ₗ[R] M')   [i
nst_5 : IsLocalizedModule S f] (m₁ m₂ : M) (s₁ s₂ : ↥S),   IsLocalizedModule.mk'
 f m₁ s₁ - IsLocalizedModule.mk' f m₂ s₂ = IsLocalizedModule.mk' f (s₂ • m₁ - s₁
 • m₂) (s₁ * s₂)
参数：f : M →ₗ[R] M'；m₁ m₂ : M；s₁ s₂ : ↥S；s₂ • m₁ - s₁ • m₂；s₁ * s₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsLocalizedModule.mk'_neg`：∀ {R : Type u_1} [inst : CommSemiring R] {S :
 Submonoid R} {M : Type u_6} {M' : Type u_7} [inst_1 : AddCommGroup M]   [inst_2
 : SubtractionC…
· 使用定理 `IsLocalizedModule.mk'_add_mk'`：∀ {R : Type u_1} [inst : CommSemiring R] 
{S : Submonoid R} {M : Type u_2} {M' : Type u_3} [inst_1 : AddCommMonoid M]   [i
nst_2 : AddCommMono…
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
-/
theorem mk'_sub_mk' {M M' : Type*} [AddCommGroup M] [SubtractionCommMonoid M'] [Module R M]
    [Module R M'] (f : M →ₗ[R] M') [IsLocalizedModule S f] (m₁ m₂ : M) (s₁ s₂ : S) :
    mk' f m₁ s₁ - mk' f m₂ s₂ = mk' f (s₂ • m₁ - s₁ • m₂) (s₁ * s₂) := by
  rw [sub_eq_add_neg, ← mk'_neg, mk'_add_mk', smul_neg, ← sub_eq_add_neg]
/-
**IsLocalizedModule.mk'_mul_mk'_of_map_mul** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalize
dModule`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {S : Submonoid R} {M : Type u_6} 
{M' : Type u_7}   [inst_1 : NonUnitalNonAssocSemiring M] [inst_2 : Semiring M'] 
[inst_3 : _root_.Module R M] [inst_4 : Algebra R M']   (f : M →ₗ[R] M'),   (∀ (m
₁ m₂ : M), f (m₁ * m₂) = f m₁ * f m₂) →     ∀ [inst_5 : IsLocalizedModule S f] (
m₁ m₂ : M) (s₁ s₂ : ↥S),       IsLocalizedModule.mk' f m₁ s₁ * IsLocalizedModule
.mk' f m₂ s₂ = IsLocalizedModule.mk' f (m₁ * m₂) (s₁ * s₂)
参数：f : M →ₗ[R] M'；∀ (m₁ m₂ : M), f (m₁ * m₂) = f m₁ * f m₂；m₁ m₂ : M；s₁ s₂ : ↥S；
m₁ * m₂；s₁ * s₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Module.End.algebraMap_isUnit_inv_apply_eq_iff`：∀ {R : Type u} (S : Type 
v) {M : Type w} [inst : CommSemiring R] [inst_1 : Semiring S] [inst_2 : AddCommM
onoid M]   [inst_3 : _root_.Module …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `smul_smul_smul_comm`：smul_smul_smul_comm [SMul α β] [SMul α γ] [SMul β δ
] [SMul α δ] [SMul γ δ] [IsScalarTower α β δ] [IsScalarTower α γ δ] [SMulCommCla
ss β γ δ]…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsLocalizedModule.mk'_smul`：∀ {R : Type u_1} [inst : CommSemiring R] {S 
: Submonoid R} {M : Type u_2} {M' : Type u_3} [inst_1 : AddCommMonoid M]   [inst
_2 : AddCommMono…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `IsLocalizedModule.mk'_cancel`：∀ {R : Type u_1} [inst : CommSemiring R] {
S : Submonoid R} {M : Type u_2} {M' : Type u_3} [inst_1 : AddCommMonoid M]   [in
st_2 : AddCommMono…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mk'_mul_mk'_of_map_mul {M M' : Type*} [NonUnitalNonAssocSemiring M] [Semiring M']
    [Module R M] [Algebra R M'] (f : M →ₗ[R] M') (hf : ∀ m₁ m₂, f (m₁ * m₂) = f m₁ * f m₂)
    [IsLocalizedModule S f] (m₁ m₂ : M) (s₁ s₂ : S) :
    mk' f m₁ s₁ * mk' f m₂ s₂ = mk' f (m₁ * m₂) (s₁ * s₂) := by
  symm
  apply (Module.End.algebraMap_isUnit_inv_apply_eq_iff _ _ _ _).mpr
  simp_rw [Submonoid.coe_mul, ← smul_eq_mul]
  rw [smul_smul_smul_comm, ← mk'_smul, ← mk'_smul]
  simp_rw [← Submonoid.smul_def, mk'_cancel, smul_eq_mul, hf]
/-
**IsLocalizedModule.mk'_mul_mk'** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalizedModule`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {S : Submonoid R} {M : Type u_6} 
{M' : Type u_7} [inst_1 : Semiring M]   [inst_2 : Semiring M'] [inst_3 : Algebra
 R M] [inst_4 : Algebra R M'] (f : M →ₐ[R] M')   [inst_5 : IsLocalizedModule S f
.toLinearMap] (m₁ m₂ : M) (s₁ s₂ : ↥S),   IsLocalizedModule.mk' f.toLinearMap m₁
 s₁ * IsLocalizedModule.mk' f.toLinearMap m₂ s₂ =     IsLocalizedModule.mk' f.to
LinearMap (m₁ * m₂) (s₁ * s₂)
参数：f : M →ₐ[R] M'；m₁ m₂ : M；s₁ s₂ : ↥S；m₁ * m₂；s₁ * s₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalizedModule.mk'_mul_mk'_of_map_mul`：∀ {R : Type u_1} [inst : CommS
emiring R] {S : Submonoid R} {M : Type u_6} {M' : Type u_7}   [inst_1 : NonUnita
lNonAssocSemiring M] [inst_2 :…
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
-/
theorem mk'_mul_mk' {M M' : Type*} [Semiring M] [Semiring M'] [Algebra R M] [Algebra R M']
    (f : M →ₐ[R] M') [IsLocalizedModule S f.toLinearMap] (m₁ m₂ : M) (s₁ s₂ : S) :
    mk' f.toLinearMap m₁ s₁ * mk' f.toLinearMap m₂ s₂ = mk' f.toLinearMap (m₁ * m₂) (s₁ * s₂) :=
  mk'_mul_mk'_of_map_mul f.toLinearMap (map_mul f) m₁ m₂ s₁ s₂

variable {f}
/-
**IsLocalizedModule.mk'_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalizedModule`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {S : Submonoid R} {M : Type u_2} 
{M' : Type u_3} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid M'] [inst_3
 : _root_.Module R M] [inst_4 : _root_.Module R M'] {f : M →ₗ[R] M'}   [inst_5 :
 IsLocalizedModule S f] {m : M} {s : ↥S} {m' : M'}, IsLocalizedModule.mk' f m s 
= m' ↔ f m = s • m'
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsLocalizedModule.smul_inj`：smul_inj (s : S) (m₁ m₂ : M') : s • m₁ = s •
 m₂ ↔ m₁ = m₂
· 使用定理 `Submonoid.smul_def`：∀ {M' : Type u_1} {α : Type u_2} [inst : MulOneClass
 M'] [inst_1 : SMul M' α] {S : Submonoid M'} (g : ↥S) (a : α),   g • a = ↑g • a
· 使用定理 `IsLocalizedModule.mk'_smul`：∀ {R : Type u_1} [inst : CommSemiring R] {S 
: Submonoid R} {M : Type u_2} {M' : Type u_3} [inst_1 : AddCommMonoid M]   [inst
_2 : AddCommMono…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsLocalizedModule.mk'_cancel`：∀ {R : Type u_1} [inst : CommSemiring R] {
S : Submonoid R} {M : Type u_2} {M' : Type u_3} [inst_1 : AddCommMonoid M]   [in
st_2 : AddCommMono…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mk'_eq_iff {m : M} {s : S} {m' : M'} : mk' f m s = m' ↔ f m = s • m' := by
  rw [← smul_inj f s, Submonoid.smul_def, ← mk'_smul, ← Submonoid.smul_def, mk'_cancel]

@[simp]
/-
**IsLocalizedModule.mk'_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalizedModule`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {S : Submonoid R} {M : Type u_2} 
{M' : Type u_3} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid M'] [inst_3
 : _root_.Module R M] [inst_4 : _root_.Module R M'] {f : M →ₗ[R] M'}   [inst_5 :
 IsLocalizedModule S f] {m : M} (s : ↥S), IsLocalizedModule.mk' f m s = 0 ↔ f m 
= 0
参数：s : ↥S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsLocalizedModule.mk'_eq_iff`：∀ {R : Type u_1} [inst : CommSemiring R] {
S : Submonoid R} {M : Type u_2} {M' : Type u_3} [inst_1 : AddCommMonoid M]   [in
st_2 : AddCommMono…
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mk'_eq_zero {m : M} (s : S) : mk' f m s = 0 ↔ f m = 0 := by rw [mk'_eq_iff, smul_zero]

variable (f)
/-
**IsLocalizedModule.mk'_eq_zero'** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalizedModule`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {S : Submonoid R} {M : Type u_2} 
{M' : Type u_3} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid M'] [inst_3
 : _root_.Module R M] [inst_4 : _root_.Module R M'] (f : M →ₗ[R] M')   [inst_5 :
 IsLocalizedModule S f] {m : M} (s : ↥S), IsLocalizedModule.mk' f m s = 0 ↔ ∃ s'
, s' • m = 0
参数：f : M →ₗ[R] M'；s : ↥S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsLocalizedModule.mk'_zero`：∀ {R : Type u_1} [inst : CommSemiring R] {S 
: Submonoid R} {M : Type u_2} {M' : Type u_3} [inst_1 : AddCommMonoid M]   [inst
_2 : AddCommMono…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mk'_eq_zero' {m : M} (s : S) : mk' f m s = 0 ↔ ∃ s' : S, s' • m = 0 := by
  simp_rw [← mk'_zero f (1 : S), mk'_eq_mk'_iff, smul_zero, one_smul, eq_comm]
/-
**IsLocalizedModule.mk_eq_mk'** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalizedModule`。
形式化陈述：mk_eq_mk' (s : S) (m : M) : LocalizedModule.mk m s = mk' (LocalizedModule.
mkLinearMap S M) m s
参数：s : S；m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `IsLocalizedModule.mk'_eq_iff`：∀ {R : Type u_1} [inst : CommSemiring R] {
S : Submonoid R} {M : Type u_2} {M' : Type u_3} [inst_1 : AddCommMonoid M]   [in
st_2 : AddCommMono…
· 使用定理 `Submonoid.smul_def`：∀ {M' : Type u_1} {α : Type u_2} [inst : MulOneClass
 M'] [inst_1 : SMul M' α] {S : Submonoid M'} (g : ↥S) (a : α),   g • a = ↑g • a
· 使用定理 `LocalizedModule.smul'_mk`：∀ {R : Type u} [inst : CommSemiring R] {S : Su
bmonoid R} {M : Type v} [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M
] {R₀ : Type u…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LocalizedModule.mk_cancel`：mk_cancel (s : S) (m : M) : mk (s • m) s = mk
 m 1
· 使用定理 `LocalizedModule.mkLinearMap_apply`：∀ {R : Type u} [inst : CommSemiring R
] (S : Submonoid R) (M : Type v) [inst_1 : AddCommMonoid M]   [inst_2 : _root_.M
odule R M] (m : M), (Lo…
-/
theorem mk_eq_mk' (s : S) (m : M) :
    LocalizedModule.mk m s = mk' (LocalizedModule.mkLinearMap S M) m s := by
  rw [eq_comm, mk'_eq_iff, Submonoid.smul_def, LocalizedModule.smul'_mk, ← Submonoid.smul_def,
    LocalizedModule.mk_cancel, LocalizedModule.mkLinearMap_apply]

set_option backward.isDefEq.respectTransparency false in
variable (A) in
/-
**IsLocalizedModule.mk'_smul_mk'** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalizedModule`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {S : Submonoid R} {M : Type u_2} 
{M' : Type u_3} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid M'] (A : Ty
pe u_5) [inst_3 : CommSemiring A] [inst_4 : Algebra R A]   [inst_5 : _root_.Modu
le A M'] [inst_6 : IsLocalization S A] [inst_7 : _root_.Module R M] [inst_8 : _r
oot_.Module R M']   [IsScalarTower R A M'] (f : M →ₗ[R] M') [inst_10 : IsLocaliz
edModule S f] (x : R) (m : M) (s t : ↥S),   IsLocalization.mk' A x s • IsLocaliz
edModule.mk' f m t = IsLocalizedModule.mk' f (x • m) (s * t)
参数：A : Type u_5；f : M →ₗ[R] M'；x : R；m : M；s t : ↥S；x • m；s * t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalizedModule.smul_injective`：smul_injective (s : S) : Function.Inje
ctive fun m : M' => s • m
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `IsLocalizedModule.mk'_cancel'`：∀ {R : Type u_1} [inst : CommSemiring R] 
{S : Submonoid R} {M : Type u_2} {M' : Type u_3} [inst_1 : AddCommMonoid M]   [i
nst_2 : AddCommMono…
· 使用定理 `Submonoid.smul_def`：∀ {M' : Type u_1} {α : Type u_2} [inst : MulOneClass
 M'] [inst_1 : SMul M' α] {S : Submonoid M'} (g : ↥S) (a : α),   g • a = ↑g • a
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用定理 `IsLocalization.smul_mk'_self`：∀ {R : Type u_1} [inst : CommSemiring R] {
M : Submonoid R} {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebra R 
S] [inst_3 : IsLoc…
· 使用定理 `algebraMap_smul`：algebraMap_smul (r : R) (m : M) : (algebraMap R A) r • 
m = r • m
-/
lemma mk'_smul_mk' (x : R) (m : M) (s t : S) :
    IsLocalization.mk' A x s • mk' f m t = mk' f (x • m) (s * t) := by
  apply smul_injective f (s * t)
  conv_lhs => simp only [smul_assoc, mul_smul, smul_comm t]
  simp only [mk'_cancel', map_smul, Submonoid.smul_def s]
  rw [← smul_assoc, IsLocalization.smul_mk'_self, algebraMap_smul]

variable (S)
/-
**IsLocalizedModule.eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalizedModule`。
形式化陈述：eq_zero_iff {m : M} : f m = 0 ↔ exists s' : S, s' • m = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `IsLocalizedModule.mk'_eq_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{S : Submonoid R} {M : Type u_2} {M' : Type u_3} [inst_1 : AddCommMonoid M]   [i
nst_2 : AddCommMono…
· 使用定理 `IsLocalizedModule.mk'_eq_zero'`：∀ {R : Type u_1} [inst : CommSemiring R]
 {S : Submonoid R} {M : Type u_2} {M' : Type u_3} [inst_1 : AddCommMonoid M]   [
inst_2 : AddCommMono…
-/
theorem eq_zero_iff {m : M} : f m = 0 ↔ ∃ s' : S, s' • m = 0 :=
  (mk'_eq_zero (1 : S)).symm.trans (mk'_eq_zero' f _)
/-
**IsLocalizedModule.mk'_surjective** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalizedModule`
。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] (S : Submonoid R) {M : Type u_2} 
{M' : Type u_3} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid M'] [inst_3
 : _root_.Module R M] [inst_4 : _root_.Module R M'] (f : M →ₗ[R] M')   [inst_5 :
 IsLocalizedModule S f], Function.Surjective (Function.uncurry (IsLocalizedModul
e.mk' f))
参数：S : Submonoid R；f : M →ₗ[R] M'；Function.uncurry (IsLocalizedModule.mk' f)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalizedModule.surj`：∀ {R : Type u_1} {inst : CommSemiring R} {M : Ty
pe u_2} {M' : Type u_3} {inst_1 : AddCommMonoid M}   {inst_2 : AddCommMonoid M'}
 {inst_3 : _…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsLocalizedModule.mk'_eq_iff`：∀ {R : Type u_1} [inst : CommSemiring R] {
S : Submonoid R} {M : Type u_2} {M' : Type u_3} [inst_1 : AddCommMonoid M]   [in
st_2 : AddCommMono…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem mk'_surjective : Function.Surjective (Function.uncurry <| mk' f : M × S → M') := by
  intro x
  obtain ⟨⟨m, s⟩, e : s • x = f m⟩ := IsLocalizedModule.surj S f x
  exact ⟨⟨m, s⟩, mk'_eq_iff.mpr e.symm⟩

section liftOfLE

variable {M₁ M₂} [AddCommMonoid M₁] [AddCommMonoid M₂] [Module R M₁] [Module R M₂]
variable (S₁ S₂ : Submonoid R) (h : S₁ ≤ S₂) (f₁ : M →ₗ[R] M₁) (f₂ : M →ₗ[R] M₂)
variable [IsLocalizedModule S₁ f₁] [IsLocalizedModule S₂ f₂]

/-- The natural map `Mₛ →ₗ[R] Mₜ` if `s ≤ t` (in `Submonoid R`). -/
noncomputable
/-
**IsLocalizedModule.liftOfLE** 是 Mathlib 中的一个定义，位于命名空间 `IsLocalizedModule`。
形式化陈述：liftOfLE : M₁ ->ₗ[R] M₂
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def liftOfLE : M₁ →ₗ[R] M₂ :=
  lift S₁ f₁ f₂ fun x ↦ map_units f₂ ⟨x.1, h x.2⟩

/-- The natural map `Mₛ →ₗ[R] Mₜ` if `s ≤ t` (in `Submonoid R`). -/
noncomputable
/-
**IsLocalizedModule._root_.LocalizedModule.liftOfLE** 是 Mathlib 中的一个缩写定义，位于命名空间 
`IsLocalizedModule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
abbrev _root_.LocalizedModule.liftOfLE : LocalizedModule S₁ M →ₗ[R] LocalizedModule S₂ M :=
  IsLocalizedModule.liftOfLE S₁ S₂ h
    (LocalizedModule.mkLinearMap S₁ M) (LocalizedModule.mkLinearMap S₂ M)
/-
**IsLocalizedModule.liftOfLE_comp** 是 Mathlib 中的一个引理，位于命名空间 `IsLocalizedModule`。
形式化陈述：liftOfLE_comp : (liftOfLE S₁ S₂ h f₁ f₂).comp f₁ = f₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalizedModule.lift_comp`：lift_comp (g : M ->ₗ[R] M'') (h : forall x 
: S, IsUnit ((algebraMap R (Module.End R M'')) x)) : (lift S f g h).comp f = g
-/
lemma liftOfLE_comp : (liftOfLE S₁ S₂ h f₁ f₂).comp f₁ = f₂ := lift_comp ..
/-
**IsLocalizedModule.liftOfLE_apply** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalizedModule`
。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {M : Type u_2} [inst_1 : AddCommM
onoid M] [inst_2 : _root_.Module R M]   {M₁ : Type u_7} {M₂ : Type u_6} [inst_3 
: AddCommMonoid M₁] [inst_4 : AddCommMonoid M₂] [inst_5 : _root_.Module R M₁]   
[inst_6 : _root_.Module R M₂] (S₁ S₂ : Submonoid R) (h : S₁ ≤ S₂) (f₁ : M →ₗ[R] 
M₁) (f₂ : M →ₗ[R] M₂)   [inst_7 : IsLocalizedModule S₁ f₁] [inst_8 : IsLocalized
Module S₂ f₂] (x : M),   (IsLocalizedModule.liftOfLE S₁ S₂ h f₁ f₂) (f₁ x) = f₂ 
x
参数：S₁ S₂ : Submonoid R；h : S₁ ≤ S₂；f₁ : M →ₗ[R] M₁；f₂ : M →ₗ[R] M₂；x : M；IsLocal
izedModule.liftOfLE S₁ S₂ h f₁ f₂；f₁ x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalizedModule.lift_apply`：lift_apply (g : M ->ₗ[R] M'') (h) (x) : li
ft S f g h (f x) = g x
-/
@[simp] lemma liftOfLE_apply (x) : liftOfLE S₁ S₂ h f₁ f₂ (f₁ x) = f₂ x := lift_apply ..

set_option backward.isDefEq.respectTransparency false in
/-- The image of `m/s` under `liftOfLE` is `m/s`. -/
@[simp]
/-
**IsLocalizedModule.liftOfLE_mk'** 是 Mathlib 中的一个引理，位于命名空间 `IsLocalizedModule`。
形式化陈述：liftOfLE_mk' (m : M) (s : S₁) : liftOfLE S₁ S₂ h f₁ f₂ (mk' f₁ m s) = mk' 
f₂ m ⟨s.1, h s.2⟩
参数：m : M；s : S₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Module.End.isUnit_iff`：∀ {R : Type u_1} {M : Type u_5} [inst : Semiring 
R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (f : Module.End R M
), IsUnit f…
· 使用定理 `IsLocalizedModule.map_units`：∀ {R : Type u_1} {inst : CommSemiring R} {M
 : Type u_2} {M' : Type u_3} {inst_1 : AddCommMonoid M}   {inst_2 : AddCommMonoi
d M'} {inst_3 : _…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `IsLocalizedModule.mk'_cancel'`：∀ {R : Type u_1} [inst : CommSemiring R] 
{S : Submonoid R} {M : Type u_2} {M' : Type u_3} [inst_1 : AddCommMonoid M]   [i
nst_2 : AddCommMono…
· 使用定理 `IsLocalizedModule.liftOfLE.eq_1`：∀ {R : Type u_1} [inst : CommSemiring R
] {M : Type u_2} [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {M₁ :
 Type u_6} {M₂ : Type…
· 使用定理 `IsLocalizedModule.lift_apply`：lift_apply (g : M ->ₗ[R] M'') (h) (x) : li
ft S f g h (f x) = g x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
The image of `m/s` under `liftOfLE` is `m/s`.
-/
lemma liftOfLE_mk' (m : M) (s : S₁) :
    liftOfLE S₁ S₂ h f₁ f₂ (mk' f₁ m s) = mk' f₂ m ⟨s.1, h s.2⟩ := by
  apply ((Module.End.isUnit_iff _).mp (map_units f₂ ⟨s, h s.2⟩)).1
  simp only [Module.algebraMap_end_apply, ← map_smul, ← Submonoid.smul_def, mk'_cancel']
  rw [liftOfLE, lift_apply]
  exact (mk'_cancel' (S := S₂) f₂ m ⟨s.1, h s.2⟩).symm
/-
**IsLocalizedModule.** 是 Mathlib 中的一个实例，位于命名空间 `IsLocalizedModule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsLocalizedModule S₂ (liftOfLE S₁ S₂ h f₁ f₂) where
  map_units := map_units f₂
  surj y := by
    obtain ⟨⟨y', s⟩, e⟩ := IsLocalizedModule.surj S₂ f₂ y
    exact ⟨⟨f₁ y', s⟩, by simpa⟩
  exists_of_eq := by
    intro x₁ x₂ e
    obtain ⟨x₁, s₁, rfl⟩ := mk'_surjective S₁ f₁ x₁
    obtain ⟨x₂, s₂, rfl⟩ := mk'_surjective S₁ f₁ x₂
    simp only [Function.uncurry, liftOfLE_mk', mk'_eq_mk'_iff,
      Submonoid.smul_def, ← mk'_smul] at e ⊢
    obtain ⟨c, e⟩ := e
    exact ⟨c, 1, by simpa [← smul_comm c.1]⟩

end liftOfLE

include S in
/-
**IsLocalizedModule.injective_of_map_eq** 是 Mathlib 中的一个引理，位于命名空间 `IsLocalizedMo
dule`。
形式化陈述：injective_of_map_eq {N : Type*} [AddCommMonoid N] [Module R N] {g : M' ->ₗ
[R] N} (H : forall {x y}, g (f x) = g (f y) -> f x = f y) : Function.Injective g
参数：H : forall {x y}, g (f x) = g (f y) -> f x = f y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalizedModule.surj`：∀ {R : Type u_1} {inst : CommSemiring R} {M : Ty
pe u_2} {M' : Type u_3} {inst_1 : AddCommMonoid M}   {inst_2 : AddCommMonoid M'}
 {inst_3 : _…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submonoid.smul_def`：∀ {M' : Type u_1} {α : Type u_2} [inst : MulOneClass
 M'] [inst_1 : SMul M' α] {S : Submonoid M'} (g : ↥S) (a : α),   g • a = ↑g • a
· 使用定理 `LinearMap.map_smul_of_tower`：map_smul_of_tower [CompatibleSMul M M₂ R S]
 (fₗ : M ->ₗ[S] M₂) (c : R) (x : M) : fₗ (c • x) = c • fₗ x
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsLocalizedModule.smul_inj`：smul_inj (s : S) (m₁ m₂ : M') : s • m₁ = s •
 m₂ ↔ m₁ = m₂
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
-/
lemma injective_of_map_eq {N : Type*} [AddCommMonoid N] [Module R N]
    {g : M' →ₗ[R] N} (H : ∀ {x y}, g (f x) = g (f y) → f x = f y) :
    Function.Injective g := by
  intro a b hab
  obtain ⟨⟨x, m⟩, (hxm : m • a = f x)⟩ := IsLocalizedModule.surj S f a
  obtain ⟨⟨y, n⟩, (hym : n • b = f y)⟩ := IsLocalizedModule.surj S f b
  suffices h : g (f (n.val • x)) = g (f (m.val • y)) by
    apply H at h
    rw [map_smul, map_smul] at h
    rwa [← IsLocalizedModule.smul_inj f (n * m), mul_smul, mul_comm, mul_smul, hxm, hym]
  simp [← hxm, ← hym, hab, ← S.smul_def, ← mul_smul, mul_comm, ← mul_smul]
/-
**IsLocalizedModule.injective_of_map_zero** 是 Mathlib 中的一个引理，位于命名空间 `IsLocalized
Module`。
形式化陈述：injective_of_map_zero {M M' N : Type*} [AddCommGroup M] [AddCommGroup M'] 
[Module R M] [Module R M'] (f : M ->ₗ[R] M') [IsLocalizedModule S f] [AddCommGro
up N] [Module R N] {g : M' ->ₗ[R] N} (H : forall m, g (f m) = 0 -> f m = 0) : Fu
nction.Injective g
参数：f : M ->ₗ[R] M'；H : forall m, g (f m) = 0 -> f m = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalizedModule.injective_of_map_eq`：injective_of_map_eq {N : Type*} [
AddCommMonoid N] [Module R N] {g : M' ->ₗ[R] N} (H : forall {x y}, g (f x) = g (
f y) -> f x = f y) : Functi…
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
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
lemma injective_of_map_zero {M M' N : Type*} [AddCommGroup M] [AddCommGroup M']
    [Module R M] [Module R M'] (f : M →ₗ[R] M') [IsLocalizedModule S f]
    [AddCommGroup N] [Module R N] {g : M' →ₗ[R] N} (H : ∀ m, g (f m) = 0 → f m = 0) :
    Function.Injective g := by
  refine IsLocalizedModule.injective_of_map_eq S f (fun hxy ↦ ?_)
  rw [← sub_eq_zero, ← map_sub]
  apply H
  simpa [sub_eq_zero]

variable {N N'} [AddCommMonoid N] [AddCommMonoid N'] [Module R N] [Module R N']
variable (g : N →ₗ[R] N') [IsLocalizedModule S g]

/-- A linear map `M →ₗ[R] N` gives a map between localized modules `Mₛ →ₗ[R] Nₛ`. -/
noncomputable
/-
**IsLocalizedModule.map** 是 Mathlib 中的一个定义，位于命名空间 `IsLocalizedModule`。
形式化陈述：map : (M ->ₗ[R] N) ->ₗ[R] (M' ->ₗ[R] N') where toFun h
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalizedModule.map_units`：∀ {R : Type u_1} {inst : CommSemiring R} {M
 : Type u_2} {M' : Type u_3} {inst_1 : AddCommMonoid M}   {inst_2 : AddCommMonoi
d M'} {inst_3 : _…
-/
def map : (M →ₗ[R] N) →ₗ[R] (M' →ₗ[R] N') where
  toFun h := lift S f (g ∘ₗ h) (IsLocalizedModule.map_units g)
  map_add' h₁ h₂ := by
    apply IsLocalizedModule.ext S f (IsLocalizedModule.map_units g)
    simp only [lift_comp, LinearMap.add_comp, LinearMap.comp_add]
  map_smul' r h := by
    apply IsLocalizedModule.ext S f (IsLocalizedModule.map_units g)
    simp only [lift_comp, LinearMap.smul_comp, LinearMap.comp_smul, RingHom.id_apply]
/-
**IsLocalizedModule.map_comp** 是 Mathlib 中的一个引理，位于命名空间 `IsLocalizedModule`。
形式化陈述：map_comp (h : M ->ₗ[R] N) : (map S f g h) ∘ₗ f = g ∘ₗ h
参数：h : M ->ₗ[R] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalizedModule.lift_comp`：lift_comp (g : M ->ₗ[R] M'') (h : forall x 
: S, IsUnit ((algebraMap R (Module.End R M'')) x)) : (lift S f g h).comp f = g
· 使用定理 `IsLocalizedModule.map_units`：∀ {R : Type u_1} {inst : CommSemiring R} {M
 : Type u_2} {M' : Type u_3} {inst_1 : AddCommMonoid M}   {inst_2 : AddCommMonoi
d M'} {inst_3 : _…
-/
lemma map_comp (h : M →ₗ[R] N) : (map S f g h) ∘ₗ f = g ∘ₗ h :=
  lift_comp S f (g ∘ₗ h) (IsLocalizedModule.map_units g)

@[simp]
/-
**IsLocalizedModule.map_apply** 是 Mathlib 中的一个引理，位于命名空间 `IsLocalizedModule`。
形式化陈述：map_apply (h : M ->ₗ[R] N) (x) : map S f g h (f x) = g (h x)
参数：h : M ->ₗ[R] N；x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalizedModule.lift_apply`：lift_apply (g : M ->ₗ[R] M'') (h) (x) : li
ft S f g h (f x) = g x
· 使用定理 `IsLocalizedModule.map_units`：∀ {R : Type u_1} {inst : CommSemiring R} {M
 : Type u_2} {M' : Type u_3} {inst_1 : AddCommMonoid M}   {inst_2 : AddCommMonoi
d M'} {inst_3 : _…
-/
lemma map_apply (h : M →ₗ[R] N) (x) : map S f g h (f x) = g (h x) :=
  lift_apply S f (g ∘ₗ h) (IsLocalizedModule.map_units g) x

@[simp]
/-
**IsLocalizedModule.map_mk'** 是 Mathlib 中的一个引理，位于命名空间 `IsLocalizedModule`。
形式化陈述：map_mk' (h : M ->ₗ[R] N) (x) (s : S) : map S f g h (IsLocalizedModule.mk' 
f x s) = (IsLocalizedModule.mk' g (h x) s)
参数：h : M ->ₗ[R] N；x；s : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalizedModule.map_units`：∀ {R : Type u_1} {inst : CommSemiring R} {M
 : Type u_2} {M' : Type u_3} {inst_1 : AddCommMonoid M}   {inst_2 : AddCommMonoi
d M'} {inst_3 : _…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsLocalizedModule.iso_symm_apply'`：iso_symm_apply' (m : M') (a : M) (b :
 S) (eq1 : b • m = f a) : (iso S f).symm m = LocalizedModule.mk a b
· 使用定理 `IsLocalizedModule.mk'_cancel'`：∀ {R : Type u_1} [inst : CommSemiring R] 
{S : Submonoid R} {M : Type u_2} {M' : Type u_3} [inst_1 : AddCommMonoid M]   [i
nst_2 : AddCommMono…
· 使用定理 `LocalizedModule.lift_mk`：lift_mk (g : M ->ₗ[R] M'') (h : forall x : S, I
sUnit (algebraMap R (Module.End R M'') x)) (m : M) (s : S) : LocalizedModule.lif
t S g h (Loca…
-/
lemma map_mk' (h : M →ₗ[R] N) (x) (s : S) :
    map S f g h (IsLocalizedModule.mk' f x s) = (IsLocalizedModule.mk' g (h x) s) := by
  simp only [map, lift, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.coe_comp, LinearEquiv.coe_coe,
    Function.comp_apply]
  rw [iso_symm_apply' S f (mk' f x s) x s (mk'_cancel' f x s), LocalizedModule.lift_mk]
  rfl

@[simp]
/-
**IsLocalizedModule.map_id** 是 Mathlib 中的一个引理，位于命名空间 `IsLocalizedModule`。
形式化陈述：map_id : map S f f .id = .id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `IsLocalizedModule.mk'_surjective`：∀ {R : Type u_1} [inst : CommSemiring 
R] (S : Submonoid R) {M : Type u_2} {M' : Type u_3} [inst_1 : AddCommMonoid M]  
 [inst_2 : AddCommMono…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `IsLocalizedModule.map_mk'`：map_mk' (h : M ->ₗ[R] N) (x) (s : S) : map S 
f g h (IsLocalizedModule.mk' f x s) = (IsLocalizedModule.mk' g (h x) s)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_id : map S f f .id = .id := by
  ext x
  obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective S f x
  simp

@[simp]
/-
**IsLocalizedModule.map_injective** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalizedModule`。
形式化陈述：map_injective (h : M ->ₗ[R] N) (h_inj : Function.Injective h) : Function.I
njective (map S f g h)
参数：h : M ->ₗ[R] N；h_inj : Function.Injective h。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalizedModule.mk'_surjective`：∀ {R : Type u_1} [inst : CommSemiring 
R] (S : Submonoid R) {M : Type u_2} {M' : Type u_3} [inst_1 : AddCommMonoid M]  
 [inst_2 : AddCommMono…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `IsLocalizedModule.map_mk'`：map_mk' (h : M ->ₗ[R] N) (x) (s : S) : map S 
f g h (IsLocalizedModule.mk' f x s) = (IsLocalizedModule.mk' g (h x) s)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `LinearMap.map_smul_of_tower`：map_smul_of_tower [CompatibleSMul M M₂ R S]
 (fₗ : M ->ₗ[S] M₂) (c : R) (x : M) : fₗ (c • x) = c • fₗ x
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
-/
theorem map_injective (h : M →ₗ[R] N) (h_inj : Function.Injective h) :
    Function.Injective (map S f g h) := by
  intro x y
  obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective S f x
  obtain ⟨⟨y, t⟩, rfl⟩ := IsLocalizedModule.mk'_surjective S f y
  simp only [Function.uncurry_apply_pair, map_mk', mk'_eq_mk'_iff, Subtype.exists,
    Submonoid.mk_smul, exists_prop, forall_exists_index, and_imp]
  intro c hc e
  exact ⟨c, hc, h_inj (by simpa)⟩

@[simp]
/-
**IsLocalizedModule.map_surjective** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalizedModule`
。
形式化陈述：map_surjective (h : M ->ₗ[R] N) (h_surj : Function.Surjective h) : Functio
n.Surjective (map S f g h)
参数：h : M ->ₗ[R] N；h_surj : Function.Surjective h。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalizedModule.mk'_surjective`：∀ {R : Type u_1} [inst : CommSemiring 
R] (S : Submonoid R) {M : Type u_2} {M' : Type u_3} [inst_1 : AddCommMonoid M]  
 [inst_2 : AddCommMono…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `IsLocalizedModule.map_mk'`：map_mk' (h : M ->ₗ[R] N) (x) (s : S) : map S 
f g h (IsLocalizedModule.mk' f x s) = (IsLocalizedModule.mk' g (h x) s)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_surjective (h : M →ₗ[R] N) (h_surj : Function.Surjective h) :
    Function.Surjective (map S f g h) := by
  intro x
  obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective S g x
  obtain ⟨x, rfl⟩ := h_surj x
  exact ⟨mk' f x s, by simp⟩

open LocalizedModule LinearEquiv LinearMap Submonoid

variable (M)

/-- The linear map `(LocalizedModule S M) → (LocalizedModule S M)` from `iso` is the identity. -/
/-
**IsLocalizedModule.iso_localizedModule_eq_refl** 是 Mathlib 中的一个引理，位于命名空间 `IsLoc
alizedModule`。
形式化陈述：iso_localizedModule_eq_refl : iso S (mkLinearMap S M) = refl R (LocalizedM
odule S M)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsLocalizedModule.is_universal`：is_universal : forall (g : M ->ₗ[R] M'')
 (_ : forall x : S, IsUnit ((algebraMap R (Module.End R M'')) x)), exists! l : M
' ->ₗ[R] M'', l.comp…
· 使用定理 `IsLocalizedModule.map_units`：∀ {R : Type u_1} {inst : CommSemiring R} {M
 : Type u_2} {M' : Type u_3} {inst_1 : AddCommMonoid M}   {inst_2 : AddCommMonoi
d M'} {inst_3 : _…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearEquiv.toLinearMap_inj`：toLinearMap_inj {e₁ e₂ : M ≃ₛₗ[σ] M₂} : (↑e
₁ : M ->ₛₗ[σ] M₂) = e₂ ↔ e₁ = e₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearEquiv.eq_toLinearMap_symm_comp`：eq_toLinearMap_symm_comp (f : M₃ -
>ₛₗ[σ₃₁] M₁) (g : M₃ ->ₛₗ[σ₃₂] M₂) : f = e₁₂.symm.toLinearMap.comp g ↔ e₁₂.toLin
earMap.comp f = g
· 使用定理 `IsLocalizedModule.iso_symm_comp`：iso_symm_comp : (iso S f).symm.toLinear
Map.comp f = LocalizedModule.mkLinearMap S M
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The linear map `(LocalizedModule S M) → (LocalizedModule S M)` from `iso` is the
 identity.
-/
lemma iso_localizedModule_eq_refl : iso S (mkLinearMap S M) = refl R (LocalizedModule S M) := by
  let f := mkLinearMap S M
  obtain ⟨e, _, univ⟩ := is_universal S f f (map_units f)
  rw [← toLinearMap_inj, univ (iso S f) ((eq_toLinearMap_symm_comp f f).1 (iso_symm_comp S f).symm)]
  exact Eq.symm <| univ (refl R (LocalizedModule S M)) (by simp)

variable {M₀ M₀'} [AddCommMonoid M₀] [AddCommMonoid M₀'] [Module R M₀] [Module R M₀']
variable (f₀ : M₀ →ₗ[R] M₀') [IsLocalizedModule S f₀]
variable {M₁ M₁'} [AddCommMonoid M₁] [AddCommMonoid M₁'] [Module R M₁] [Module R M₁']
variable (f₁ : M₁ →ₗ[R] M₁') [IsLocalizedModule S f₁]

/-- Formula for `IsLocalizedModule.map` when each localized module is a `LocalizedModule`. -/
/-
**IsLocalizedModule.map_LocalizedModules** 是 Mathlib 中的一个引理，位于命名空间 `IsLocalizedM
odule`。
形式化陈述：map_LocalizedModules (g : M₀ ->ₗ[R] M₁) (m : M₀) (s : S) : ((map S (mkLine
arMap S M₀) (mkLinearMap S M₁)) g) (LocalizedModule.mk m s) = LocalizedModule.mk
 (g m) s
参数：g : M₀ ->ₗ[R] M₁；m : M₀；s : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsLocalizedModule.map_units`：∀ {R : Type u_1} {inst : CommSemiring R} {M
 : Type u_2} {M' : Type u_3} {inst_1 : AddCommMonoid M}   {inst_2 : AddCommMonoi
d M'} {inst_3 : _…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsLocalizedModule.iso_apply_mk`：iso_apply_mk (m : M) (s : S) : iso S f (
LocalizedModule.mk m s) = (IsLocalizedModule.map_units f s).unit⁻¹.val (f m)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用引理 `IsLocalizedModule.iso_localizedModule_eq_refl`：iso_localizedModule_eq_re
fl : iso S (mkLinearMap S M) = refl R (LocalizedModule S M)
· 使用定理 `AddHom.mk.congr_simp`：∀ {M : Type u_10} {N : Type u_11} [inst : Add M] [
inst_1 : Add N] (toFun toFun_1 : M → N) (e_toFun : toFun = toFun_1)   (map_add' 
: ∀ (x y :…
· 使用定理 `LinearMap.mk.congr_simp`：∀ {R : Type u_14} {S : Type u_15} [inst : Semir
ing R] [inst_1 : Semiring S] {σ : R →+* S} {M : Type u_16}   {M₂ : Type u_17} [i
nst_2 : AddCo…
· 使用定理 `LocalizedModule.mkLinearMap_apply`：∀ {R : Type u} [inst : CommSemiring R
] (S : Submonoid R) (M : Type v) [inst_1 : AddCommMonoid M]   [inst_2 : _root_.M
odule R M] (m : M), (Lo…
· 使用定理 `LinearEquiv.refl_apply`：refl_apply [Module R M] (x : M) : refl R M x = x

--- 原说明 ---
Formula for `IsLocalizedModule.map` when each localized module is a `LocalizedMo
dule`.
-/
lemma map_LocalizedModules (g : M₀ →ₗ[R] M₁) (m : M₀) (s : S) :
    ((map S (mkLinearMap S M₀) (mkLinearMap S M₁)) g)
    (LocalizedModule.mk m s) = LocalizedModule.mk (g m) s := by
  have := (iso_apply_mk S (mkLinearMap S M₁) (g m) s).symm
  rw [iso_localizedModule_eq_refl, refl_apply] at this
  simpa [map, lift, iso_localizedModule_eq_refl S M₀]
/-
**IsLocalizedModule.map_iso_commute** 是 Mathlib 中的一个引理，位于命名空间 `IsLocalizedModule
`。
形式化陈述：map_iso_commute (g : M₀ ->ₗ[R] M₁) : (map S f₀ f₁) g ∘ₗ (iso S f₀) = (iso 
S f₁) ∘ₗ (map S (mkLinearMap S M₀) (mkLinearMap S M₁)) g
参数：g : M₀ ->ₗ[R] M₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `LocalizedModule.induction_on`：induction_on {β : LocalizedModule S M -> P
rop} (h : forall (m : M) (s : S), β (mk m s)) : forall x : LocalizedModule S M, 
β x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Module.End.isUnit_iff`：∀ {R : Type u_1} {M : Type u_5} [inst : Semiring 
R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (f : Module.End R M
), IsUnit f…
· 使用定理 `IsLocalizedModule.map_units`：∀ {R : Type u_1} {inst : CommSemiring R} {M
 : Type u_2} {M' : Type u_3} {inst_1 : AddCommMonoid M}   {inst_2 : AddCommMonoi
d M'} {inst_3 : _…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.algebraMap_end_apply`：algebraMap_end_apply (a : R) (m : M) : alge
braMap R (End S M) a m = a • m
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.CompatibleSMul.map_smul`：∀ {M : Type u_8} {M₂ : Type u_10} {in
st : AddCommMonoid M} {inst_1 : AddCommMonoid M₂} {R : Type u_14} {S : Type u_15
}   {inst_2 : Semiring …
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `LocalizedModule.smul'_mk`：∀ {R : Type u} [inst : CommSemiring R] {S : Su
bmonoid R} {M : Type v} [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M
] {R₀ : Type u…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用引理 `Submonoid.mk_smul`：mk_smul (g : M') (hg : g in S) (a : α) : (⟨g, hg⟩ : S
) • a = g • a
· 使用定理 `LocalizedModule.mk_cancel`：mk_cancel (s : S) (m : M) : mk (s • m) s = mk
 m 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `IsLocalizedModule.iso_mk_one`：iso_mk_one (x : M) : (iso S f) (LocalizedM
odule.mk x 1) = f x
· 使用引理 `IsLocalizedModule.iso_symm_apply`：iso_symm_apply (x) : (iso S f).symm (f
 x) = LocalizedModule.mk x 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
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
· 使用定理 `IsUnit.unit.congr_simp`：∀ {M : Type u_1} [inst : Monoid M] {a a_1 : M} (
e_a : a = a_1) (h : IsUnit a), h.unit = ⋯.unit
· 使用定理 `IsUnit.unit_one`：unit_one (h : IsUnit (1 : M)) : h.unit = 1
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
（共 37 条，此处仅展示前 30 条）
-/
lemma map_iso_commute (g : M₀ →ₗ[R] M₁) : (map S f₀ f₁) g ∘ₗ (iso S f₀) =
    (iso S f₁) ∘ₗ (map S (mkLinearMap S M₀) (mkLinearMap S M₁)) g := by
  ext x
  induction x using induction_on with | _ m s
  refine ((Module.End.isUnit_iff _).1 (map_units f₁ s)).1 ?_
  rw [Module.algebraMap_end_apply, Module.algebraMap_end_apply,
    ← CompatibleSMul.map_smul, ← CompatibleSMul.map_smul, smul'_mk, ← mk_smul _ s.2, mk_cancel]
  simp [map, lift, iso_localizedModule_eq_refl, lift_mk]

end IsLocalizedModule

namespace IsLocalizedModule

variable {M₀ M₀'} [AddCommMonoid M₀] [AddCommMonoid M₀'] [Module R M₀] [Module R M₀']
variable (f₀ : M₀ →ₗ[R] M₀') [IsLocalizedModule S f₀]
variable {M₁ M₁'} [AddCommMonoid M₁] [AddCommMonoid M₁'] [Module R M₁] [Module R M₁']
variable (f₁ : M₁ →ₗ[R] M₁') [IsLocalizedModule S f₁]
variable {M₂ M₂'} [AddCommMonoid M₂] [AddCommMonoid M₂'] [Module R M₂] [Module R M₂']
variable (f₂ : M₂ →ₗ[R] M₂') [IsLocalizedModule S f₂]

/-- Localization of composition is the composition of localization -/
/-
**IsLocalizedModule.map_comp'** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalizedModule`。
形式化陈述：map_comp' (g : M₀ ->ₗ[R] M₁) (h : M₁ ->ₗ[R] M₂) : map S f₀ f₂ (h ∘ₗ g) = m
ap S f₁ f₂ h ∘ₗ map S f₀ f₁ g
参数：g : M₀ ->ₗ[R] M₁；h : M₁ ->ₗ[R] M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `IsLocalizedModule.mk'_surjective`：∀ {R : Type u_1} [inst : CommSemiring 
R] (S : Submonoid R) {M : Type u_2} {M' : Type u_3} [inst_1 : AddCommMonoid M]  
 [inst_2 : AddCommMono…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `IsLocalizedModule.map_mk'`：map_mk' (h : M ->ₗ[R] N) (x) (s : S) : map S 
f g h (IsLocalizedModule.mk' f x s) = (IsLocalizedModule.mk' g (h x) s)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Localization of composition is the composition of localization
-/
theorem map_comp' (g : M₀ →ₗ[R] M₁) (h : M₁ →ₗ[R] M₂) :
    map S f₀ f₂ (h ∘ₗ g) = map S f₁ f₂ h ∘ₗ map S f₀ f₁ g := by
  ext x
  obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective S f₀ x
  simp

section Algebra

set_option backward.isDefEq.respectTransparency false in
/-
**IsLocalizedModule.mkOfAlgebra** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalizedModule`。
形式化陈述：mkOfAlgebra {R S S' : Type*} [CommSemiring R] [Ring S] [Ring S'] [Algebra 
R S] [Algebra R S'] (M : Submonoid R) (f : S ->ₐ[R] S') (h₁ : forall x in M, IsU
nit (algebraMap R S' x)) (h₂ : forall y, exists x : S × M, x.2 • y = f x.1) (h₃ 
: forall x, f x = 0 -> exists m : M, m • x = 0) : IsLocalizedModule M f.toLinear
Map
参数：M : Submonoid R；f : S ->ₐ[R] S'；h₁ : forall x in M, IsUnit (algebraMap R S' x
)；h₂ : forall y, exists x : S × M, x.2 • y = f x.1；h₃ : forall x, f x = 0 -> exi
sts m : M, m • x = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUnit.mul_left_cancel`：∀ {M : Type u_1} [inst : Monoid M] {a b c : M}, 
IsUnit a → a * b = a * c → b = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `AlgHomClass.linearMapClass`：∀ {R : Type u_1} {A : Type u_2} {B : Type u_
3} {F : Type u_4} [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Semi
ring B] [inst_3 …
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgHom.congr_arg`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : CommS
emiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra R A] 
[inst_…
· 使用定理 `Module.End.isUnit_iff`：∀ {R : Type u_1} {M : Type u_5} [inst : Semiring 
R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (f : Module.End R M
), IsUnit f…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Module.algebraMap_end_apply`：algebraMap_end_apply (a : R) (m : M) : alge
braMap R (End S M) a m = a • m
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `IsUnit.mul_val_inv`：mul_val_inv (h : IsUnit a) : a * ↑h.unit⁻¹ = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
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
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `smul_sub`：smul_sub (r : M) (x y : A) : r • (x - y) = r • x - r • y
-/
theorem mkOfAlgebra {R S S' : Type*} [CommSemiring R] [Ring S] [Ring S'] [Algebra R S]
    [Algebra R S'] (M : Submonoid R) (f : S →ₐ[R] S') (h₁ : ∀ x ∈ M, IsUnit (algebraMap R S' x))
    (h₂ : ∀ y, ∃ x : S × M, x.2 • y = f x.1) (h₃ : ∀ x, f x = 0 → ∃ m : M, m • x = 0) :
    IsLocalizedModule M f.toLinearMap := by
  replace h₃ := fun x =>
    Iff.intro (h₃ x) fun ⟨⟨m, hm⟩, e⟩ =>
      (h₁ m hm).mul_left_cancel <| by
        rw [← Algebra.smul_def]
        simpa [Submonoid.smul_def] using f.congr_arg e
  constructor
  · intro x
    rw [Module.End.isUnit_iff]
    constructor
    · rintro a b (e : x • a = x • b)
      simp_rw [Submonoid.smul_def, Algebra.smul_def] at e
      exact (h₁ x x.2).mul_left_cancel e
    · intro a
      refine ⟨((h₁ x x.2).unit⁻¹ :) * a, ?_⟩
      rw [Module.algebraMap_end_apply, Algebra.smul_def, ← mul_assoc, IsUnit.mul_val_inv, one_mul]
  · exact h₂
  · intro x y
    dsimp only [AlgHom.toLinearMap_apply]
    rw [← sub_eq_zero, ← map_sub, h₃]
    simp_rw [smul_sub, sub_eq_zero]
    exact id

end Algebra

variable {R A M M' : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A] (S : Submonoid R)
  [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']
  [IsLocalization S A]

attribute [local instance] LocalizedModule.moduleOfIsLocalization in
/-- If `M'` is the localization of `M` at `S` and `A = S⁻¹R`, then `M'` is an `A`-module. -/
/-
**IsLocalizedModule.module** 是 Mathlib 中的一个定义，位于命名空间 `IsLocalizedModule`。
形式化陈述：{R : Type u_6} →   {A : Type u_7} →     {M : Type u_8} →       {M' : Type 
u_9} →         [inst : CommSemiring R] →           [inst_1 : CommSemiring A] →  
           [inst_2 : Algebra R A] →               (S : Submonoid R) →           
      [inst_3 : AddCommMonoid M] →                   [inst_4 : _root_.Module R M
] →                     [inst_5 : AddCommMonoid M'] →                       [ins
t_6 : _root_.Module R M'] →                         [IsLocalization S A] → (f : 
M →ₗ[R] M') → [IsLocalizedModule S f] → _root_.Module A M'
参数：S : Submonoid R；f : M →ₗ[R] M'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `M'` is the localization of `M` at `S` and `A = S⁻¹R`, then `M'` is an `A`-mo
dule.
-/
@[reducible] noncomputable def module (f : M →ₗ[R] M') [IsLocalizedModule S f] : Module A M' :=
  (IsLocalizedModule.iso S f).symm.toAddEquiv.module A

attribute [local instance] LocalizedModule.moduleOfIsLocalization in
/-
**IsLocalizedModule.isScalarTower_module** 是 Mathlib 中的一个引理，位于命名空间 `IsLocalizedM
odule`。
形式化陈述：isScalarTower_module (f : M ->ₗ[R] M') [IsLocalizedModule S f] : letI : Mo
dule A M'
参数：f : M ->ₗ[R] M'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LinearEquiv.isScalarTower`：LinearEquiv.isScalarTower [Module R α] [Modul
e R β] [IsScalarTower R A β] (e : α ≃ₗ[R] β) : letI
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `LocalizedModule.instIsScalarTower`：∀ {R : Type u} [inst : CommSemiring R
] {S : Submonoid R} {M : Type v} [inst_1 : AddCommMonoid M]   [inst_2 : _root_.M
odule R M] (T : Type u_…
-/
lemma isScalarTower_module (f : M →ₗ[R] M') [IsLocalizedModule S f] :
    letI : Module A M' := IsLocalizedModule.module S f
    IsScalarTower R A M' :=
  (IsLocalizedModule.iso S f).symm.isScalarTower A

section Subsingleton

/-
**IsLocalizedModule.mem_ker_iff** 是 Mathlib 中的一个引理，位于命名空间 `IsLocalizedModule`。
形式化陈述：mem_ker_iff (S : Submonoid R) {g : M ->ₗ[R] M'} [IsLocalizedModule S g] {m
 : M} : m in LinearMap.ker g ↔ exists r in S, r • m = 0
参数：S : Submonoid R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `IsLocalizedModule.eq_zero_iff`：eq_zero_iff {m : M} : f m = 0 ↔ exists s'
 : S, s' • m = 0
-/
lemma mem_ker_iff (S : Submonoid R) {g : M →ₗ[R] M'}
    [IsLocalizedModule S g] {m : M} :
    m ∈ LinearMap.ker g ↔ ∃ r ∈ S, r • m = 0 := by
  simpa using IsLocalizedModule.eq_zero_iff S g
/-
**IsLocalizedModule.subsingleton_iff_ker_eq_top** 是 Mathlib 中的一个引理，位于命名空间 `IsLoc
alizedModule`。
形式化陈述：subsingleton_iff_ker_eq_top (S : Submonoid R) (g : M ->ₗ[R] M') [IsLocaliz
edModule S g] : Subsingleton M' ↔ LinearMap.ker g = ⊤
参数：S : Submonoid R；g : M ->ₗ[R] M'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `top_le_iff`：top_le_iff : ⊤ <= a ↔ a = ⊤
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `subsingleton_iff_forall_eq`：∀ {α : Sort u_1} (x : α), Subsingleton α ↔ ∀
 (y : α), y = x
· 使用定理 `IsLocalizedModule.mk'_surjective`：∀ {R : Type u_1} [inst : CommSemiring 
R] (S : Submonoid R) {M : Type u_2} {M' : Type u_3} [inst_1 : AddCommMonoid M]  
 [inst_2 : AddCommMono…
· 使用定理 `Submodule.mem_top`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R] [
inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {x : M},   x ∈ ⊤
-/
lemma subsingleton_iff_ker_eq_top (S : Submonoid R) (g : M →ₗ[R] M')
    [IsLocalizedModule S g] :
    Subsingleton M' ↔ LinearMap.ker g = ⊤ := by
  rw [← top_le_iff]
  refine ⟨fun H m _ ↦ Subsingleton.elim _ _, fun H ↦ (subsingleton_iff_forall_eq 0).mpr fun x ↦ ?_⟩
  obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective S g x
  simpa using @H x Submodule.mem_top
/-
**IsLocalizedModule.subsingleton_iff** 是 Mathlib 中的一个引理，位于命名空间 `IsLocalizedModul
e`。
形式化陈述：subsingleton_iff (S : Submonoid R) (g : M ->ₗ[R] M') [IsLocalizedModule S 
g] : Subsingleton M' ↔ forall m : M, exists r in S, r • m = 0
参数：S : Submonoid R；g : M ->ₗ[R] M'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `IsLocalizedModule.subsingleton_iff_ker_eq_top`：subsingleton_iff_ker_eq_t
op (S : Submonoid R) (g : M ->ₗ[R] M') [IsLocalizedModule S g] : Subsingleton M'
 ↔ LinearMap.ker g = ⊤
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `IsLocalizedModule.mem_ker_iff`：mem_ker_iff (S : Submonoid R) {g : M ->ₗ[
R] M'} [IsLocalizedModule S g] {m : M} : m in LinearMap.ker g ↔ exists r in S, r
 • m = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `true_implies`：∀ (p : Prop), (True → p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma subsingleton_iff (S : Submonoid R) (g : M →ₗ[R] M')
    [IsLocalizedModule S g] :
    Subsingleton M' ↔ ∀ m : M, ∃ r ∈ S, r • m = 0 := by
  simp_rw [subsingleton_iff_ker_eq_top S g, ← top_le_iff, SetLike.le_def,
    mem_ker_iff S, Submodule.mem_top, true_implies]
/-
**IsLocalizedModule.subsingleton_of_subsingleton** 是 Mathlib 中的一个引理，位于命名空间 `IsLo
calizedModule`。
形式化陈述：subsingleton_of_subsingleton (S : Submonoid R) (g : M ->ₗ[R] M') [IsLocali
zedModule S g] [Subsingleton M] : Subsingleton M'
参数：S : Submonoid R；g : M ->ₗ[R] M'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `IsLocalizedModule.subsingleton_iff`：subsingleton_iff (S : Submonoid R) (
g : M ->ₗ[R] M') [IsLocalizedModule S g] : Subsingleton M' ↔ forall m : M, exist
s r in S, r • m = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `SubmonoidClass.toOneMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   On
eMemClass S M
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
lemma subsingleton_of_subsingleton (S : Submonoid R) (g : M →ₗ[R] M') [IsLocalizedModule S g]
    [Subsingleton M] : Subsingleton M' := by
  rw [subsingleton_iff S g]
  intro m
  use 1
  simp [one_mem, Subsingleton.elim m 0]

end Subsingleton

end IsLocalizedModule

end IsLocalizedModule

namespace LocalizedModule

variable {R M : Type*} [CommRing R] [AddCommMonoid M] [Module R M]

/-
**LocalizedModule.mem_ker_mkLinearMap_iff** 是 Mathlib 中的一个引理，位于命名空间 `LocalizedMo
dule`。
形式化陈述：mem_ker_mkLinearMap_iff {S : Submonoid R} {m : M} : m in LinearMap.ker (mk
LinearMap S M) ↔ exists r in S, r • m = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalizedModule.mem_ker_iff`：mem_ker_iff (S : Submonoid R) {g : M ->ₗ[
R] M'} [IsLocalizedModule S g] {m : M} : m in LinearMap.ker g ↔ exists r in S, r
 • m = 0
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
lemma mem_ker_mkLinearMap_iff {S : Submonoid R} {m : M} :
    m ∈ LinearMap.ker (mkLinearMap S M) ↔ ∃ r ∈ S, r • m = 0 :=
  IsLocalizedModule.mem_ker_iff S
/-
**LocalizedModule.subsingleton_iff_ker_eq_top** 是 Mathlib 中的一个引理，位于命名空间 `Localiz
edModule`。
形式化陈述：subsingleton_iff_ker_eq_top {S : Submonoid R} : Subsingleton (LocalizedMod
ule S M) ↔ LinearMap.ker (LocalizedModule.mkLinearMap S M) = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalizedModule.subsingleton_iff_ker_eq_top`：subsingleton_iff_ker_eq_t
op (S : Submonoid R) (g : M ->ₗ[R] M') [IsLocalizedModule S g] : Subsingleton M'
 ↔ LinearMap.ker g = ⊤
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
lemma subsingleton_iff_ker_eq_top {S : Submonoid R} :
    Subsingleton (LocalizedModule S M) ↔
      LinearMap.ker (LocalizedModule.mkLinearMap S M) = ⊤ :=
  IsLocalizedModule.subsingleton_iff_ker_eq_top S _
/-
**LocalizedModule.subsingleton_iff** 是 Mathlib 中的一个引理，位于命名空间 `LocalizedModule`。
形式化陈述：subsingleton_iff {S : Submonoid R} : Subsingleton (LocalizedModule S M) ↔ 
forall m : M, exists r in S, r • m = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalizedModule.subsingleton_iff`：subsingleton_iff (S : Submonoid R) (
g : M ->ₗ[R] M') [IsLocalizedModule S g] : Subsingleton M' ↔ forall m : M, exist
s r in S, r • m = 0
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
lemma subsingleton_iff {S : Submonoid R} :
    Subsingleton (LocalizedModule S M) ↔ ∀ m : M, ∃ r ∈ S, r • m = 0 :=
  IsLocalizedModule.subsingleton_iff S (LocalizedModule.mkLinearMap S M)
/-
**LocalizedModule.** 是 Mathlib 中的一个实例，位于命名空间 `LocalizedModule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Subsingleton M] (S : Submonoid R) : Subsingleton (LocalizedModule S M) := by
  rw [IsLocalizedModule.subsingleton_iff S (LocalizedModule.mkLinearMap S M)]
  intro
  use 1, S.one_mem, Subsingleton.elim _ _

end LocalizedModule

namespace IsLocalizedModule

variable {R M A N : Type*} [CommRing R] [AddCommMonoid M] [Module R M]
  [CommRing A] [AddCommMonoid N] [Module A N] [Algebra R A] [Module R N] [IsScalarTower R A N]
  (f : M →ₗ[R] N)

/-
**IsLocalizedModule.isTorsionFree_of_forall_isRegular** 是 Mathlib 中的一个引理，位于命名空间 
`IsLocalizedModule`。
形式化陈述：isTorsionFree_of_forall_isRegular (S : Submonoid R) (hS : forall s in S, s
 != 0 -> IsRegular s) [IsTorsionFree R M] [IsLocalization S A] [IsLocalizedModul
e S f] : IsTorsionFree A N where isSMulRegular c hc x y hxy
参数：S : Submonoid R；hS : forall s in S, s != 0 -> IsRegular s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `IsLocalizedModule.subsingleton_iff`：subsingleton_iff (S : Submonoid R) (
g : M ->ₗ[R] M') [IsLocalizedModule S g] : Subsingleton M' ↔ forall m : M, exist
s r in S, r • m = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `IsLocalization.mk'_surjective`：∀ {R : Type u_1} [inst : CommSemiring R] 
(M : Submonoid R) {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebra R
 S] [inst_3 : IsLoc…
· 使用定理 `IsLocalizedModule.mk'_surjective`：∀ {R : Type u_1} [inst : CommSemiring 
R] (S : Submonoid R) {M : Type u_2} {M' : Type u_3} [inst_1 : AddCommMonoid M]  
 [inst_2 : AddCommMono…
· 使用定理 `ne_of_mem_of_not_mem`：∀ {α : Type u_1} {β : Type u_2} [inst : Membership
 α β] {s : β} {a b : α}, a ∈ s → b ∉ s → a ≠ b
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `IsRegular.isSMulRegular`：∀ {R : Type u_1} {M : Type u_3} {inst : Semirin
g R} {inst_1 : AddCommMonoid M} {inst_2 : _root_.Module R M}   [self : Module.Is
TorsionFree R…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `One.instNonempty`：∀ {α : Type u} [One α], Nonempty α
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
· 使用定理 `IsLocalization.isRegular_mk'`：∀ {R : Type u_1} [inst : CommSemiring R] {
M : Submonoid R} {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebra R 
S] [inst_3 : IsLoc…
· 使用定理 `IsLocalizedModule.mk'_smul_mk'`：∀ {R : Type u_1} [inst : CommSemiring R]
 {S : Submonoid R} {M : Type u_2} {M' : Type u_3} [inst_1 : AddCommMonoid M]   [
inst_2 : AddCommMono…
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
-/
lemma isTorsionFree_of_forall_isRegular (S : Submonoid R) (hS : ∀ s ∈ S, s ≠ 0 → IsRegular s)
    [IsTorsionFree R M] [IsLocalization S A] [IsLocalizedModule S f] : IsTorsionFree A N where
  isSMulRegular c hc x y hxy := by
    by_cases hS₀ : 0 ∈ S
    · have : Subsingleton N := (IsLocalizedModule.subsingleton_iff S f).2 fun _ ↦ ⟨0, hS₀, by simp⟩
      exact Subsingleton.elim ..
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective S c
    obtain ⟨⟨m₁, t₁⟩, rfl⟩ := IsLocalizedModule.mk'_surjective S f x
    obtain ⟨⟨m₂, t₂⟩, rfl⟩ := IsLocalizedModule.mk'_surjective S f y
    replace hS : ∀ s ∈ S, IsRegular s := fun s hs ↦ hS s hs <| ne_of_mem_of_not_mem hs hS₀
    rw [IsLocalization.isRegular_mk' hS] at hc
    have (s : S) (x y : M) : s • x = s • y ↔ x = y := (hS _ s.2).isSMulRegular.eq_iff
    simp only [Function.uncurry_apply_pair, mk'_smul_mk', mk'_eq_mk'_iff, mul_smul, this,
      exists_const] at hxy ⊢
    simpa [smul_comm _ a, hc.isSMulRegular.eq_iff] using hxy
/-
**IsLocalizedModule.isTorsionFree** 是 Mathlib 中的一个引理，位于命名空间 `IsLocalizedModule`。
形式化陈述：isTorsionFree [IsDomain R] [IsTorsionFree R M] (S : Submonoid R) [IsLocali
zation S A] [IsLocalizedModule S f] : Module.IsTorsionFree A N
参数：S : Submonoid R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalizedModule.isTorsionFree_of_forall_isRegular`：isTorsionFree_of_fo
rall_isRegular (S : Submonoid R) (hS : forall s in S, s != 0 -> IsRegular s) [Is
TorsionFree R M] [IsLocalization S A] [Is…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma isTorsionFree [IsDomain R] [IsTorsionFree R M] (S : Submonoid R)
    [IsLocalization S A] [IsLocalizedModule S f] : Module.IsTorsionFree A N :=
  isTorsionFree_of_forall_isRegular f S <| by simp [isRegular_iff_ne_zero]
/-
**IsLocalizedModule.** 是 Mathlib 中的一个实例，位于命名空间 `IsLocalizedModule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsDomain R] (S : Submonoid R) [IsTorsionFree R M] :
    IsTorsionFree (Localization S) (LocalizedModule S M) :=
  isTorsionFree (LocalizedModule.mkLinearMap S M) S

end IsLocalizedModule

/-!
## Localizations of modules away from an element
-/

/-- Given `x : R` and `f : M →ₗ[R] M'`, `IsLocalizedModule.Away x f` states that `M'`
  is isomorphic to the localization of `M` at the submonoid generated by `x`. -/
/-
**IsLocalizedModule.Away** 是 Mathlib 中的一个定义，位于命名空间 `IsLocalizedModule`。
形式化陈述：{R : Type u_1} →   {M : Type u_2} →     {M' : Type u_3} →       [inst : Co
mmSemiring R] →         R →           [inst_1 : AddCommMonoid M] →             [
inst_2 : _root_.Module R M] →               [inst_3 : AddCommMonoid M'] → [inst_
4 : _root_.Module R M'] → (M →ₗ[R] M') → Prop
参数：M →ₗ[R] M'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `x : R` and `f : M →ₗ[R] M'`, `IsLocalizedModule.Away x f` states that `M'
`
  is isomorphic to the localization of `M` at the submonoid generated by `x`.
-/
protected abbrev IsLocalizedModule.Away {R M M' : Type*} [CommSemiring R] (x : R) [AddCommMonoid M]
    [Module R M] [AddCommMonoid M'] [Module R M'] (f : M →ₗ[R] M') :=
  IsLocalizedModule (Submonoid.powers x) f

/-- Given `x : R`, `LocalizedModule.Away x M` is the localization of `M` at the
  submonoid generated by `x`. -/
/-
**LocalizedModule.Away** 是 Mathlib 中的一个定义，位于命名空间 `LocalizedModule`。
形式化陈述：{R : Type u_1} →   [inst : CommSemiring R] → R → (M : Type u_2) → [inst_1 
: AddCommMonoid M] → [_root_.Module R M] → Type (max u_1 u_2)
参数：M : Type u_2；max u_1 u_2。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `x : R`, `LocalizedModule.Away x M` is the localization of `M` at the
  submonoid generated by `x`.
-/
protected abbrev LocalizedModule.Away {R : Type*} [CommSemiring R] (x : R)
    (M : Type*) [AddCommMonoid M] [Module R M] :=
  LocalizedModule (Submonoid.powers x) M
