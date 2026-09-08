/-
Copyright (c) 2022 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer, Kevin Klinge, Andrew Yang
-/
module

public import Mathlib.Algebra.Group.Submonoid.DistribMulAction
public import Mathlib.GroupTheory.OreLocalization.Basic
public import Mathlib.Algebra.GroupWithZero.Defs

/-!

# Localization over left Ore sets.

This file proves results on the localization of rings (monoids with zeros) over a left Ore set.

## References

* <https://ncatlab.org/nlab/show/Ore+localization>
* [Zoran Škoda, *Noncommutative localization in noncommutative geometry*][skoda2006]


## Tags
localization, Ore, non-commutative

-/

@[expose] public section

assert_not_exists RelIso

universe u

namespace OreLocalization

section MonoidWithZero

variable {R : Type*} [MonoidWithZero R] {S : Submonoid R} [OreSet S]

@[simp]
/-
**OreLocalization.zero_oreDiv'** 是 Mathlib 中的一个定理，位于命名空间 `OreLocalization`。
形式化陈述：zero_oreDiv' (s : S) : (0 : R) /ₒ s = 0
参数：s : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OreLocalization.zero_def`：∀ {R : Type u_1} [inst : Monoid R] {S : Submon
oid R} [inst_1 : OreLocalization.OreSet S] {X : Type u_2}   [inst_2 : Zero X] [i
nst_3 : MulAct…
· 使用定理 `OreLocalization.oreDiv_eq_iff`：oreDiv_eq_iff {r₁ r₂ : X} {s₁ s₂ : S} : r
₁ /ₒ s₁ = r₂ /ₒ s₂ ↔ exists (u : S) (v : R), u • r₂ = v • r₁ ∧ u * s₂ = v * s₁
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem zero_oreDiv' (s : S) : (0 : R) /ₒ s = 0 := by
  rw [OreLocalization.zero_def, oreDiv_eq_iff]
  exact ⟨s, 1, by simp [Submonoid.smul_def]⟩
/-
**OreLocalization.** 是 Mathlib 中的一个实例，位于命名空间 `OreLocalization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MonoidWithZero R[S⁻¹] where
  zero_mul x := by
    induction x using OreLocalization.ind with | _ r s
    rw [OreLocalization.zero_def, oreDiv_mul_char 0 r 1 s 0 1 (by simp), zero_mul, one_mul]
  mul_zero x := by
    induction x using OreLocalization.ind with | _ r s
    rw [OreLocalization.zero_def, mul_div_one, mul_zero, zero_oreDiv', zero_oreDiv']
/-
**OreLocalization.subsingleton_iff** 是 Mathlib 中的一个定理，位于命名空间 `OreLocalization`。
形式化陈述：subsingleton_iff : Subsingleton R[S⁻¹] ↔ 0 in S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `subsingleton_iff_zero_eq_one`：subsingleton_iff_zero_eq_one : (0 : M₀) = 
1 ↔ Subsingleton M₀
· 使用定理 `OreLocalization.one_def`：∀ {R : Type u_1} [inst : Monoid R] {S : Submono
id R} [inst_1 : OreLocalization.OreSet S] {X : Type u_2}   [inst_2 : MulAction R
 X] [inst_3 :…
· 使用定理 `OreLocalization.zero_def`：∀ {R : Type u_1} [inst : Monoid R] {S : Submon
oid R} [inst_1 : OreLocalization.OreSet S] {X : Type u_2}   [inst_2 : Zero X] [i
nst_3 : MulAct…
· 使用定理 `OreLocalization.oreDiv_eq_iff`：oreDiv_eq_iff {r₁ r₂ : X} {s₁ s₂ : S} : r
₁ /ₒ s₁ = r₂ /ₒ s₂ ↔ exists (u : S) (v : R), u • r₂ = v • r₁ ∧ u * s₂ = v * s₁
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem subsingleton_iff :
    Subsingleton R[S⁻¹] ↔ 0 ∈ S := by
  rw [← subsingleton_iff_zero_eq_one, OreLocalization.one_def,
    OreLocalization.zero_def, oreDiv_eq_iff]
  simp
/-
**OreLocalization.nontrivial_iff** 是 Mathlib 中的一个定理，位于命名空间 `OreLocalization`。
形式化陈述：nontrivial_iff : Nontrivial R[S⁻¹] ↔ 0 ∉ S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `not_subsingleton_iff_nontrivial`：not_subsingleton_iff_nontrivial : ¬Subs
ingleton α ↔ Nontrivial α
· 使用定理 `OreLocalization.subsingleton_iff`：subsingleton_iff : Subsingleton R[S⁻¹]
 ↔ 0 in S
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem nontrivial_iff :
    Nontrivial R[S⁻¹] ↔ 0 ∉ S := by
  rw [← not_subsingleton_iff_nontrivial, subsingleton_iff]

end MonoidWithZero

section CommMonoidWithZero

variable {R : Type*} [CommMonoidWithZero R] {S : Submonoid R} [OreSet S]

/-
**OreLocalization.** 是 Mathlib 中的一个实例，位于命名空间 `OreLocalization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CommMonoidWithZero R[S⁻¹] where
  __ := (inferInstance : MonoidWithZero R[S⁻¹])
  __ := (inferInstance : CommMonoid R[S⁻¹])

end CommMonoidWithZero

section DistribMulAction

variable {R : Type*} [Monoid R] {S : Submonoid R} [OreSet S] {X : Type*} [AddMonoid X]
variable [DistribMulAction R X]

/-- Auxiliary definition for addition on the Ore localization. -/
/-
**OreLocalization.add''** 是 Mathlib 中的一个定义，位于命名空间 `OreLocalization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for addition on the Ore localization.
-/
private def add'' (r₁ : X) (s₁ : S) (r₂ : X) (s₂ : S) : X[S⁻¹] :=
  (oreDenom (s₁ : R) s₂ • r₁ + oreNum (s₁ : R) s₂ • r₂) /ₒ (oreDenom (s₁ : R) s₂ * s₁)
/-
**OreLocalization.add''_char** 是 Mathlib 中的一个定理，位于命名空间 `OreLocalization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem add''_char (r₁ : X) (s₁ : S) (r₂ : X) (s₂ : S) (rb : R) (sb : R)
    (hb : sb * s₁ = rb * s₂) (h : sb * s₁ ∈ S) :
    add'' r₁ s₁ r₂ s₂ = (sb • r₁ + rb • r₂) /ₒ ⟨sb * s₁, h⟩ := by
  simp only [add'']
  have ha := ore_eq (s₁ : R) s₂
  generalize oreNum (s₁ : R) s₂ = ra at *
  generalize oreDenom (s₁ : R) s₂ = sa at *
  rw [oreDiv_eq_iff]
  rcases oreCondition sb sa with ⟨rc, sc, hc⟩
  have : sc * rb * s₂ = rc * ra * s₂ := by
    rw [mul_assoc rc, ← ha, ← mul_assoc, ← hc, mul_assoc, mul_assoc, hb]
  rcases ore_right_cancel _ _ s₂ this with ⟨sd, hd⟩
  use sd * sc
  use sd * rc
  simp only [smul_add, smul_smul, Submonoid.smul_def, Submonoid.coe_mul]
  constructor
  · rw [mul_assoc _ _ rb, hd, mul_assoc, hc, mul_assoc, mul_assoc]
  · rw [mul_assoc, ← mul_assoc (sc : R), hc, mul_assoc, mul_assoc]

attribute [local instance] OreLocalization.oreEqv

/-- Auxiliary definition for addition on the Ore localization, with one argument fixed. -/
/-
**OreLocalization.add'** 是 Mathlib 中的一个定义，位于命名空间 `OreLocalization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for addition on the Ore localization, with one argument fix
ed.
-/
private def add' (r₂ : X) (s₂ : S) : X[S⁻¹] → X[S⁻¹] :=
  (--plus tilde
      Quotient.lift
      fun r₁s₁ : X × S => add'' r₁s₁.1 r₁s₁.2 r₂ s₂) <| by
    -- Porting note: `assoc_rw` & `noncomm_ring` were not ported yet
    rintro ⟨r₁', s₁'⟩ ⟨r₁, s₁⟩ ⟨sb, rb, hb, hb'⟩
    -- s*, r*
    rcases oreCondition (s₁' : R) s₂ with ⟨rc, sc, hc⟩
    --s~~, r~~
    rcases oreCondition rb sc with ⟨rd, sd, hd⟩
    -- s#, r#
    dsimp at *
    rw [add''_char _ _ _ _ rc sc hc (sc * s₁').2]
    have : sd * sb * s₁ = rd * rc * s₂ := by
      rw [mul_assoc, hb', ← mul_assoc, hd, mul_assoc, hc, ← mul_assoc]
    rw [add''_char _ _ _ _ (rd * rc : R) (sd * sb) this (sd * sb * s₁).2]
    rw [mul_smul, ← Submonoid.smul_def sb, hb, smul_smul, hd, oreDiv_eq_iff]
    use 1
    use rd
    simp only [mul_smul, smul_add, one_smul, OneMemClass.coe_one, one_mul, true_and]
    rw [this, hc, mul_assoc]

/-- The addition on the Ore localization. -/
@[irreducible]
/-
**OreLocalization.add** 是 Mathlib 中的一个定义，位于命名空间 `OreLocalization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The addition on the Ore localization.
-/
private def add : X[S⁻¹] → X[S⁻¹] → X[S⁻¹] := fun x =>
  Quotient.lift (fun rs : X × S => add' rs.1 rs.2 x)
    (by
      rintro ⟨r₁, s₁⟩ ⟨r₂, s₂⟩ ⟨sb, rb, hb, hb'⟩
      induction x with | _ r₃ s₃
      change add'' _ _ _ _ = add'' _ _ _ _
      dsimp only at *
      rcases oreCondition (s₃ : R) s₂ with ⟨rc, sc, hc⟩
      rcases oreCondition rc sb with ⟨rd, sd, hd⟩
      have : rd * rb * s₁ = sd * sc * s₃ := by
        rw [mul_assoc, ← hb', ← mul_assoc, ← hd, mul_assoc, ← hc, mul_assoc]
      rw [add''_char _ _ _ _ rc sc hc (sc * s₃).2]
      rw [add''_char _ _ _ _ _ _ this.symm (sd * sc * s₃).2]
      refine oreDiv_eq_iff.mpr ?_
      simp only [smul_add]
      use sd, 1
      simp only [one_smul, one_mul, mul_smul, ← hb, Submonoid.smul_def, ← mul_assoc, and_true]
      simp only [smul_smul, hd])

@[no_expose]
/-
**OreLocalization.** 是 Mathlib 中的一个实例，位于命名空间 `OreLocalization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Add X[S⁻¹] :=
  ⟨add⟩
/-
**OreLocalization.oreDiv_add_oreDiv** 是 Mathlib 中的一个定理，位于命名空间 `OreLocalization`。
形式化陈述：oreDiv_add_oreDiv {r r' : X} {s s' : S} : r /ₒ s + r' /ₒ s' = (oreDenom (s
 : R) s' • r + oreNum (s : R) s' • r') /ₒ (oreDenom (s : R) s' * s)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem oreDiv_add_oreDiv {r r' : X} {s s' : S} :
    r /ₒ s + r' /ₒ s' =
      (oreDenom (s : R) s' • r + oreNum (s : R) s' • r') /ₒ (oreDenom (s : R) s' * s) := by
  with_unfolding_all rfl
/-
**OreLocalization.oreDiv_add_char'** 是 Mathlib 中的一个定理，位于命名空间 `OreLocalization`。
形式化陈述：oreDiv_add_char' {r r' : X} (s s' : S) (rb : R) (sb : R) (h : sb * s = rb 
* s') (h' : sb * s in S) : r /ₒ s + r' /ₒ s' = (sb • r + rb • r') /ₒ ⟨sb * s, h'
⟩
参数：s s' : S；rb : R；sb : R；h : sb * s = rb * s'；h' : sb * s in S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.RingTheory.OreLocalization.Basic.0.OreLocalization.add'
'_char`：∀ {R : Type u_1} [inst : Monoid R] {S : Submonoid R} [inst_1 : OreLocali
zation.OreSet S] {X : Type u_2}   [inst_2 : AddMonoid X] [inst_3 : D…
-/
theorem oreDiv_add_char' {r r' : X} (s s' : S) (rb : R) (sb : R)
    (h : sb * s = rb * s') (h' : sb * s ∈ S) :
    r /ₒ s + r' /ₒ s' = (sb • r + rb • r') /ₒ ⟨sb * s, h'⟩ := by
  with_unfolding_all exact add''_char r s r' s' rb sb h h'

/-- A characterization of the addition on the Ore localization, allowing for arbitrary Ore
numerator and Ore denominator. -/
/-
**OreLocalization.oreDiv_add_char** 是 Mathlib 中的一个定理，位于命名空间 `OreLocalization`。
形式化陈述：oreDiv_add_char {r r' : X} (s s' : S) (rb : R) (sb : S) (h : sb * s = rb *
 s') : r /ₒ s + r' /ₒ s' = (sb • r + rb • r') /ₒ (sb * s)
参数：s s' : S；rb : R；sb : S；h : sb * s = rb * s'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OreLocalization.oreDiv_add_char'`：oreDiv_add_char' {r r' : X} (s s' : S)
 (rb : R) (sb : R) (h : sb * s = rb * s') (h' : sb * s in S) : r /ₒ s + r' /ₒ s'
 = (sb • r + rb • r') …
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf

--- 原说明 ---
A characterization of the addition on the Ore localization, allowing for arbitra
ry Ore
numerator and Ore denominator.
-/
theorem oreDiv_add_char {r r' : X} (s s' : S) (rb : R) (sb : S) (h : sb * s = rb * s') :
    r /ₒ s + r' /ₒ s' = (sb • r + rb • r') /ₒ (sb * s) :=
  oreDiv_add_char' s s' rb sb h (sb * s).2

/-- Another characterization of the addition on the Ore localization, bundling up all witnesses
and conditions into a sigma type. -/
/-
**OreLocalization.oreDivAddChar'** 是 Mathlib 中的一个定义，位于命名空间 `OreLocalization`。
形式化陈述：oreDivAddChar' (r r' : X) (s s' : S) : Σ' r'' : R, Σ' s'' : S, s'' * s = r
'' * s' ∧ r /ₒ s + r' /ₒ s' = (s'' • r + r'' • r') /ₒ (s'' * s)
参数：r r' : X；s s' : S。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Another characterization of the addition on the Ore localization, bundling up al
l witnesses
and conditions into a sigma type.
-/
def oreDivAddChar' (r r' : X) (s s' : S) :
    Σ' r'' : R,
      Σ' s'' : S, s'' * s = r'' * s' ∧ r /ₒ s + r' /ₒ s' = (s'' • r + r'' • r') /ₒ (s'' * s) :=
  ⟨oreNum (s : R) s', oreDenom (s : R) s', ore_eq (s : R) s', oreDiv_add_oreDiv⟩

@[simp]
/-
**OreLocalization.add_oreDiv** 是 Mathlib 中的一个定理，位于命名空间 `OreLocalization`。
形式化陈述：add_oreDiv {r r' : X} {s : S} : r /ₒ s + r' /ₒ s = (r + r') /ₒ s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OreLocalization.oreDiv_add_char`：oreDiv_add_char {r r' : X} (s s' : S) (
rb : R) (sb : S) (h : sb * s = rb * s') : r /ₒ s + r' /ₒ s' = (sb • r + rb • r')
 /ₒ (sb * s)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
theorem add_oreDiv {r r' : X} {s : S} : r /ₒ s + r' /ₒ s = (r + r') /ₒ s := by
  simp [oreDiv_add_char s s 1 1 (by simp)]
/-
**OreLocalization.add_assoc** 是 Mathlib 中的一个定理，位于命名空间 `OreLocalization`。
形式化陈述：∀ {R : Type u_1} [inst : Monoid R] {S : Submonoid R} [inst_1 : OreLocaliza
tion.OreSet S] {X : Type u_2}   [inst_2 : AddMonoid X] [inst_3 : DistribMulActio
n R X] (x y z : OreLocalization S X), x + y + z = x + (y + z)
参数：x y z : OreLocalization S X；y + z。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OreLocalization.ind`：∀ {R : Type u_1} [inst : Monoid R] {S : Submonoid R
} [inst_1 : OreLocalization.OreSet S] {X : Type u_2}   [inst_2 : MulAction R X] 
{β : OreL…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OreLocalization.expand`：∀ {R : Type u_1} [inst : Monoid R] {S : Submonoi
d R} [inst_1 : OreLocalization.OreSet S] {X : Type u_2}   [inst_2 : MulAction R 
X] (r : X) (…
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
-/
protected theorem add_assoc (x y z : X[S⁻¹]) : x + y + z = x + (y + z) := by
  induction x with | _ r₁ s₁
  induction y with | _ r₂ s₂
  induction z with | _ r₃ s₃
  rcases oreDivAddChar' r₁ r₂ s₁ s₂ with ⟨ra, sa, ha, ha'⟩; rw [ha']; clear ha'
  rcases oreDivAddChar' (sa • r₁ + ra • r₂) r₃ (sa * s₁) s₃ with ⟨rc, sc, hc, q⟩; rw [q]; clear q
  simp only [smul_add, add_assoc]
  simp_rw [← add_oreDiv, ← OreLocalization.expand']
  congr 2
  · rw [OreLocalization.expand r₂ s₂ ra (ha.symm ▸ (sa * s₁).2)]; congr; ext; exact ha
  · rw [OreLocalization.expand r₃ s₃ rc (hc.symm ▸ (sc * (sa * s₁)).2)]; congr; ext; exact hc

@[simp]
/-
**OreLocalization.zero_oreDiv** 是 Mathlib 中的一个定理，位于命名空间 `OreLocalization`。
形式化陈述：zero_oreDiv (s : S) : (0 : X) /ₒ s = 0
参数：s : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OreLocalization.zero_def`：∀ {R : Type u_1} [inst : Monoid R] {S : Submon
oid R} [inst_1 : OreLocalization.OreSet S] {X : Type u_2}   [inst_2 : Zero X] [i
nst_3 : MulAct…
· 使用定理 `OreLocalization.oreDiv_eq_iff`：oreDiv_eq_iff {r₁ r₂ : X} {s₁ s₂ : S} : r
₁ /ₒ s₁ = r₂ /ₒ s₂ ↔ exists (u : S) (v : R), u • r₂ = v • r₁ ∧ u * s₂ = v * s₁
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem zero_oreDiv (s : S) : (0 : X) /ₒ s = 0 := by
  rw [OreLocalization.zero_def, oreDiv_eq_iff]
  exact ⟨s, 1, by simp⟩
/-
**OreLocalization.zero_add** 是 Mathlib 中的一个定理，位于命名空间 `OreLocalization`。
形式化陈述：∀ {R : Type u_1} [inst : Monoid R] {S : Submonoid R} [inst_1 : OreLocaliza
tion.OreSet S] {X : Type u_2}   [inst_2 : AddMonoid X] [inst_3 : DistribMulActio
n R X] (x : OreLocalization S X), 0 + x = x
参数：x : OreLocalization S X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OreLocalization.ind`：∀ {R : Type u_1} [inst : Monoid R] {S : Submonoid R
} [inst_1 : OreLocalization.OreSet S] {X : Type u_2}   [inst_2 : MulAction R X] 
{β : OreL…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OreLocalization.zero_oreDiv`：zero_oreDiv (s : S) : (0 : X) /ₒ s = 0
· 使用定理 `OreLocalization.add_oreDiv`：add_oreDiv {r r' : X} {s : S} : r /ₒ s + r' 
/ₒ s = (r + r') /ₒ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem zero_add (x : X[S⁻¹]) : 0 + x = x := by
  induction x
  rw [← zero_oreDiv, add_oreDiv]; simp
/-
**OreLocalization.add_zero** 是 Mathlib 中的一个定理，位于命名空间 `OreLocalization`。
形式化陈述：∀ {R : Type u_1} [inst : Monoid R] {S : Submonoid R} [inst_1 : OreLocaliza
tion.OreSet S] {X : Type u_2}   [inst_2 : AddMonoid X] [inst_3 : DistribMulActio
n R X] (x : OreLocalization S X), x + 0 = x
参数：x : OreLocalization S X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OreLocalization.ind`：∀ {R : Type u_1} [inst : Monoid R] {S : Submonoid R
} [inst_1 : OreLocalization.OreSet S] {X : Type u_2}   [inst_2 : MulAction R X] 
{β : OreL…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OreLocalization.zero_oreDiv`：zero_oreDiv (s : S) : (0 : X) /ₒ s = 0
· 使用定理 `OreLocalization.add_oreDiv`：add_oreDiv {r r' : X} {s : S} : r /ₒ s + r' 
/ₒ s = (r + r') /ₒ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem add_zero (x : X[S⁻¹]) : x + 0 = x := by
  induction x
  rw [← zero_oreDiv, add_oreDiv]; simp

/-- Scalar multiplication by natural numbers on the Ore localization. -/
@[irreducible]
/-
**OreLocalization.nsmul** 是 Mathlib 中的一个定义，位于命名空间 `OreLocalization`。
形式化陈述：nsmul : Nat -> X[S⁻¹] -> X[S⁻¹]
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Scalar multiplication by natural numbers on the Ore localization.
-/
def nsmul : ℕ → X[S⁻¹] → X[S⁻¹] := nsmulRec
/-
**OreLocalization.** 是 Mathlib 中的一个实例，位于命名空间 `OreLocalization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddMonoid X[S⁻¹] where
    add_assoc := OreLocalization.add_assoc
    zero_add := OreLocalization.zero_add
    add_zero := OreLocalization.add_zero
    nsmul := nsmul
    nsmul_zero _ := by with_unfolding_all rfl
    nsmul_succ _ _ := by with_unfolding_all rfl
/-
**OreLocalization.smul_zero** 是 Mathlib 中的一个定理，位于命名空间 `OreLocalization`。
形式化陈述：∀ {R : Type u_1} [inst : Monoid R] {S : Submonoid R} [inst_1 : OreLocaliza
tion.OreSet S] {X : Type u_2}   [inst_2 : AddMonoid X] [inst_3 : DistribMulActio
n R X] (x : OreLocalization S R), x • 0 = 0
参数：x : OreLocalization S R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OreLocalization.ind`：∀ {R : Type u_1} [inst : Monoid R] {S : Submonoid R
} [inst_1 : OreLocalization.OreSet S] {X : Type u_2}   [inst_2 : MulAction R X] 
{β : OreL…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OreLocalization.zero_def`：∀ {R : Type u_1} [inst : Monoid R] {S : Submon
oid R} [inst_1 : OreLocalization.OreSet S] {X : Type u_2}   [inst_2 : Zero X] [i
nst_3 : MulAct…
· 使用定理 `OreLocalization.smul_div_one`：smul_div_one {p : R} {r : X} {s : S} : (p 
/ₒ s) • (r /ₒ 1) = (p • r) /ₒ s
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `OreLocalization.zero_oreDiv`：zero_oreDiv (s : S) : (0 : X) /ₒ s = 0
-/
protected theorem smul_zero (x : R[S⁻¹]) : x • (0 : X[S⁻¹]) = 0 := by
  induction x with | _ r s
  rw [OreLocalization.zero_def, smul_div_one, smul_zero, zero_oreDiv, zero_oreDiv]
/-
**OreLocalization.smul_add** 是 Mathlib 中的一个定理，位于命名空间 `OreLocalization`。
形式化陈述：∀ {R : Type u_1} [inst : Monoid R] {S : Submonoid R} [inst_1 : OreLocaliza
tion.OreSet S] {X : Type u_2}   [inst_2 : AddMonoid X] [inst_3 : DistribMulActio
n R X] (z : OreLocalization S R) (x y : OreLocalization S X),   z • (x + y) = z 
• x + z • y
参数：z : OreLocalization S R；x y : OreLocalization S X；x + y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OreLocalization.ind`：∀ {R : Type u_1} [inst : Monoid R] {S : Submonoid R
} [inst_1 : OreLocalization.OreSet S] {X : Type u_2}   [inst_2 : MulAction R X] 
{β : OreL…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OreLocalization.expand'`：∀ {R : Type u_1} [inst : Monoid R] {S : Submono
id R} [inst_1 : OreLocalization.OreSet S] {X : Type u_2}   [inst_2 : MulAction R
 X] (r : X) (…
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SetLike.coe_mem`：coe_mem (x : p) : (x : B) in p
· 使用定理 `OreLocalization.expand`：∀ {R : Type u_1} [inst : Monoid R] {S : Submonoi
d R} [inst_1 : OreLocalization.OreSet S] {X : Type u_2}   [inst_2 : MulAction R 
X] (r : X) (…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Subtype.coe_eq_of_eq_mk`：coe_eq_of_eq_mk {a : { a // p a }} {b : α} (h :
 ↑a = b) : a = ⟨b, h ▸ a.2⟩
· 使用定理 `OreLocalization.oreDiv_smul_oreDiv`：oreDiv_smul_oreDiv {r₁ : R} {r₂ : X}
 {s₁ s₂ : S} : (r₁ /ₒ s₁) • (r₂ /ₒ s₂) = oreNum r₁ s₂ • r₂ /ₒ (oreDenom r₁ s₂ * 
s₁)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `OreLocalization.add_oreDiv`：add_oreDiv {r r' : X} {s : S} : r /ₒ s + r' 
/ₒ s = (r + r') /ₒ s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem smul_add (z : R[S⁻¹]) (x y : X[S⁻¹]) :
    z • (x + y) = z • x + z • y := by
  induction x with | _ r₁ s₁
  induction y with | _ r₂ s₂
  induction z with | _ r₃ s₃
  rcases oreDivAddChar' r₁ r₂ s₁ s₂ with ⟨ra, sa, ha, ha'⟩; rw [ha']; clear ha'; norm_cast at ha
  rw [OreLocalization.expand' r₁ s₁ sa]
  rw [OreLocalization.expand r₂ s₂ ra (by rw [← ha]; apply SetLike.coe_mem)]
  rw [← Subtype.coe_eq_of_eq_mk ha]
  repeat rw [oreDiv_smul_oreDiv]
  simp only [smul_add, add_oreDiv]
/-
**OreLocalization.** 是 Mathlib 中的一个实例，位于命名空间 `OreLocalization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : DistribMulAction R[S⁻¹] X[S⁻¹] where
  smul_zero := OreLocalization.smul_zero
  smul_add := OreLocalization.smul_add
/-
**OreLocalization.** 是 Mathlib 中的一个实例，位于命名空间 `OreLocalization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R₀} [Monoid R₀] [MulAction R₀ X] [MulAction R₀ R]
    [IsScalarTower R₀ R X] [IsScalarTower R₀ R R] :
    DistribMulAction R₀ X[S⁻¹] where
  smul_zero _ := by rw [← smul_one_oreDiv_one_smul, smul_zero]
  smul_add _ _ _ := by simp only [← smul_one_oreDiv_one_smul, smul_add]

end DistribMulAction

section AddCommMonoid

variable {R : Type*} [Monoid R] {S : Submonoid R} [OreSet S]
variable {X : Type*} [AddCommMonoid X] [DistribMulAction R X]

/-
**OreLocalization.add_comm** 是 Mathlib 中的一个定理，位于命名空间 `OreLocalization`。
形式化陈述：∀ {R : Type u_1} [inst : Monoid R] {S : Submonoid R} [inst_1 : OreLocaliza
tion.OreSet S] {X : Type u_2}   [inst_2 : AddCommMonoid X] [inst_3 : DistribMulA
ction R X] (x y : OreLocalization S X), x + y = y + x
参数：x y : OreLocalization S X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OreLocalization.ind`：∀ {R : Type u_1} [inst : Monoid R] {S : Submonoid R
} [inst_1 : OreLocalization.OreSet S] {X : Type u_2}   [inst_2 : MulAction R X] 
{β : OreL…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `OreLocalization.oreDiv_add_char'`：oreDiv_add_char' {r r' : X} (s s' : S)
 (rb : R) (sb : R) (h : sb * s = rb * s') (h' : sb * s in S) : r /ₒ s + r' /ₒ s'
 = (sb • r + rb • r') …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
-/
protected theorem add_comm (x y : X[S⁻¹]) : x + y = y + x := by
  induction x with | _ r s
  induction y with | _ r' s'
  rcases oreDivAddChar' r r' s s' with ⟨ra, sa, ha, ha'⟩
  rw [ha', oreDiv_add_char' s' s _ _ ha.symm (ha ▸ (sa * s).2), add_comm]
  congr; ext; exact ha
/-
**OreLocalization.instAddCommMonoidOreLocalization** 是 Mathlib 中的一个实例，位于命名空间 `Or
eLocalization`。
形式化陈述：instAddCommMonoidOreLocalization : AddCommMonoid X[S⁻¹] where add_comm
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `OreLocalization.add_comm`：∀ {R : Type u_1} [inst : Monoid R] {S : Submon
oid R} [inst_1 : OreLocalization.OreSet S] {X : Type u_2}   [inst_2 : AddCommMon
oid X] [inst_3…
-/
instance instAddCommMonoidOreLocalization : AddCommMonoid X[S⁻¹] where
  add_comm := OreLocalization.add_comm

end AddCommMonoid

section AddGroup

variable {R : Type*} [Monoid R] {S : Submonoid R} [OreSet S]
variable {X : Type*} [AddGroup X] [DistribMulAction R X]

/-- Negation on the Ore localization is defined via negation on the numerator. -/
@[irreducible]
/-
**OreLocalization.neg** 是 Mathlib 中的一个定义，位于命名空间 `OreLocalization`。
形式化陈述：{R : Type u_1} →   [inst : Monoid R] →     {S : Submonoid R} →       [inst
_1 : OreLocalization.OreSet S] →         {X : Type u_2} →           [inst_2 : Ad
dGroup X] → [inst_3 : DistribMulAction R X] → OreLocalization S X → OreLocalizat
ion S X
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Negation on the Ore localization is defined via negation on the numerator.
-/
protected def neg : X[S⁻¹] → X[S⁻¹] :=
  liftExpand (fun (r : X) (s : S) => -r /ₒ s) fun r t s ht => by
    rw [← smul_neg, ← OreLocalization.expand]
/-
**OreLocalization.instNegOreLocalization** 是 Mathlib 中的一个实例，位于命名空间 `OreLocalizat
ion`。
形式化陈述：instNegOreLocalization : Neg X[S⁻¹]
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNegOreLocalization : Neg X[S⁻¹] :=
  ⟨OreLocalization.neg⟩

@[simp]
/-
**OreLocalization.neg_def** 是 Mathlib 中的一个定理，位于命名空间 `OreLocalization`。
形式化陈述：∀ {R : Type u_1} [inst : Monoid R] {S : Submonoid R} [inst_1 : OreLocaliza
tion.OreSet S] {X : Type u_2}   [inst_2 : AddGroup X] [inst_3 : DistribMulAction
 R X] (r : X) (s : ↥S), -(r /ₒ s) = -r /ₒ s
参数：r : X；s : ↥S；r /ₒ s。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem neg_def (r : X) (s : S) : -(r /ₒ s) = -r /ₒ s := by
  with_unfolding_all rfl
/-
**OreLocalization.neg_add_cancel** 是 Mathlib 中的一个定理，位于命名空间 `OreLocalization`。
形式化陈述：∀ {R : Type u_1} [inst : Monoid R] {S : Submonoid R} [inst_1 : OreLocaliza
tion.OreSet S] {X : Type u_2}   [inst_2 : AddGroup X] [inst_3 : DistribMulAction
 R X] (x : OreLocalization S X), -x + x = 0
参数：x : OreLocalization S X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OreLocalization.ind`：∀ {R : Type u_1} [inst : Monoid R] {S : Submonoid R
} [inst_1 : OreLocalization.OreSet S] {X : Type u_2}   [inst_2 : MulAction R X] 
{β : OreL…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OreLocalization.neg_def`：∀ {R : Type u_1} [inst : Monoid R] {S : Submono
id R} [inst_1 : OreLocalization.OreSet S] {X : Type u_2}   [inst_2 : AddGroup X]
 [inst_3 : Di…
· 使用定理 `OreLocalization.add_oreDiv`：add_oreDiv {r r' : X} {s : S} : r /ₒ s + r' 
/ₒ s = (r + r') /ₒ s
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
· 使用定理 `OreLocalization.zero_oreDiv`：zero_oreDiv (s : S) : (0 : X) /ₒ s = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem neg_add_cancel (x : X[S⁻¹]) : -x + x = 0 := by
  induction x with | _ r s; simp

/-- `zsmul` of `OreLocalization` -/
@[irreducible]
/-
**OreLocalization.zsmul** 是 Mathlib 中的一个定义，位于命名空间 `OreLocalization`。
形式化陈述：{R : Type u_1} →   [inst : Monoid R] →     {S : Submonoid R} →       [inst
_1 : OreLocalization.OreSet S] →         {X : Type u_2} →           [inst_2 : Ad
dGroup X] → [inst_3 : DistribMulAction R X] → ℤ → OreLocalization S X → OreLocal
ization S X
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`zsmul` of `OreLocalization`
-/
protected def zsmul : ℤ → X[S⁻¹] → X[S⁻¹] := zsmulRec

unseal OreLocalization.zsmul in
/-
**OreLocalization.instAddGroupOreLocalization** 是 Mathlib 中的一个实例，位于命名空间 `OreLoca
lization`。
形式化陈述：instAddGroupOreLocalization : AddGroup X[S⁻¹] where neg_add_cancel
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `OreLocalization.neg_add_cancel`：∀ {R : Type u_1} [inst : Monoid R] {S : 
Submonoid R} [inst_1 : OreLocalization.OreSet S] {X : Type u_2}   [inst_2 : AddG
roup X] [inst_3 : Di…
-/
instance instAddGroupOreLocalization : AddGroup X[S⁻¹] where
  neg_add_cancel := OreLocalization.neg_add_cancel
  zsmul := OreLocalization.zsmul

end AddGroup

section AddCommGroup

variable {R : Type*} [Monoid R] {S : Submonoid R} [OreSet S]
variable {X : Type*} [AddCommGroup X] [DistribMulAction R X]

/-
**OreLocalization.** 是 Mathlib 中的一个实例，位于命名空间 `OreLocalization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddCommGroup X[S⁻¹] where
  __ := (inferInstance : AddGroup X[S⁻¹])
  __ := (inferInstance : AddCommMonoid X[S⁻¹])

end AddCommGroup

end OreLocalization

