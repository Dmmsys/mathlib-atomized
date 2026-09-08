/-
Copyright (c) 2022 Hanting Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hanting Zhang
-/
module

public import Mathlib.Topology.MetricSpace.Antilipschitz
public import Mathlib.Topology.MetricSpace.Isometry
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Data.FunLike.Basic

/-!
# Dilations

We define dilations, i.e., maps between emetric spaces that satisfy
`edist (f x) (f y) = r * edist x y` for some `r ∉ {0, ∞}`.

The value `r = 0` is not allowed because we want dilations of (e)metric spaces to be automatically
injective. The value `r = ∞` is not allowed because this way we can define `Dilation.ratio f : ℝ≥0`,
not `Dilation.ratio f : ℝ≥0∞`. Also, we do not often need maps sending distinct points to points at
infinite distance.

## Main definitions

* `Dilation.ratio f : ℝ≥0`: the value of `r` in the relation above, defaulting to 1 in the case
  where it is not well-defined.

## Notation

- `α →ᵈ β`: notation for `Dilation α β`.

## Implementation notes

The type of dilations defined in this file are also referred to as "similarities" or "similitudes"
by other authors. The name `Dilation` was chosen to match the Wikipedia name.

Since a lot of elementary properties don't require `eq_of_dist_eq_zero` we start setting up the
theory for `PseudoEMetricSpace` and we specialize to `PseudoMetricSpace` and `MetricSpace` when
needed.

## TODO

- Introduce dilation equivs.
- Refactor the `Isometry` API to match the `*HomClass` API below.

## References

- https://en.wikipedia.org/wiki/Dilation_(metric_space)
- [Marcel Berger, *Geometry*][berger1987]
-/

@[expose] public section

noncomputable section

open Bornology Function Set Topology Metric
open scoped ENNReal NNReal

section Defs

variable (α : Type*) (β : Type*) [PseudoEMetricSpace α] [PseudoEMetricSpace β]

/-- A dilation is a map that uniformly scales the edistance between any two points. -/
/-
**Dilation** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_1) → (β : Type u_2) → [PseudoEMetricSpace α] → [PseudoEMetricS
pace β] → Type (max u_1 u_2)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A dilation is a map that uniformly scales the edistance between any two points.
-/
structure Dilation where
  /-- The underlying function.

  Do NOT use directly. Use the coercion instead. -/
  toFun : α → β
  edist_eq' : ∃ r : ℝ≥0, r ≠ 0 ∧ ∀ x y : α, edist (toFun x) (toFun y) = r * edist x y

@[inherit_doc] infixl:25 " →ᵈ " => Dilation

/-- `DilationClass F α β r` states that `F` is a type of `r`-dilations.
You should extend this typeclass when you extend `Dilation`. -/
/-
**DilationClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_3) →   (α : outParam (Type u_4)) →     (β : outParam (Type u_5
)) → [PseudoEMetricSpace α] → [PseudoEMetricSpace β] → [FunLike F α β] → Prop
参数：Type u_4；Type u_5。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`DilationClass F α β r` states that `F` is a type of `r`-dilations.
You should extend this typeclass when you extend `Dilation`.
-/
class DilationClass (F : Type*) (α β : outParam Type*) [PseudoEMetricSpace α] [PseudoEMetricSpace β]
    [FunLike F α β] : Prop where
  edist_eq' : ∀ f : F, ∃ r : ℝ≥0, r ≠ 0 ∧ ∀ x y : α, edist (f x) (f y) = r * edist x y

end Defs

namespace Dilation

variable {α : Type*} {β : Type*} {γ : Type*} {F : Type*}

section Setup

variable [PseudoEMetricSpace α] [PseudoEMetricSpace β]

/-
**Dilation.funLike** 是 Mathlib 中的一个实例，位于命名空间 `Dilation`。
形式化陈述：funLike : FunLike (α ->ᵈ β) α β where coe
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance funLike : FunLike (α →ᵈ β) α β where
  coe := toFun
  coe_injective f g h := by cases f; cases g; congr
/-
**Dilation.toDilationClass** 是 Mathlib 中的一个实例，位于命名空间 `Dilation`。
形式化陈述：toDilationClass : DilationClass (α ->ᵈ β) α β where edist_eq' f
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Dilation.edist_eq'`：∀ {α : Type u_1} {β : Type u_2} [inst : PseudoEMetri
cSpace α] [inst_1 : PseudoEMetricSpace β] (self : α →ᵈ β),   ∃ r, r ≠ 0 ∧ ∀ (x y
 : α), e…
-/
instance toDilationClass : DilationClass (α →ᵈ β) α β where
  edist_eq' f := edist_eq' f

@[simp]
/-
**Dilation.toFun_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `Dilation`。
形式化陈述：toFun_eq_coe {f : α ->ᵈ β} : f.toFun = (f : α -> β)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toFun_eq_coe {f : α →ᵈ β} : f.toFun = (f : α → β) :=
  rfl

@[simp]
/-
**Dilation.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `Dilation`。
形式化陈述：coe_mk (f : α -> β) (h) : ⇑(⟨f, h⟩ : α ->ᵈ β) = f
参数：f : α -> β；h。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mk (f : α → β) (h) : ⇑(⟨f, h⟩ : α →ᵈ β) = f :=
  rfl
/-
**Dilation.congr_fun** 是 Mathlib 中的一个定理，位于命名空间 `Dilation`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : PseudoEMetricSpace α] [inst_1 : Ps
eudoEMetricSpace β] {f g : α →ᵈ β},   f = g → ∀ (x : α), f x = g x
参数：x : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
-/
protected theorem congr_fun {f g : α →ᵈ β} (h : f = g) (x : α) : f x = g x :=
  DFunLike.congr_fun h x
/-
**Dilation.congr_arg** 是 Mathlib 中的一个定理，位于命名空间 `Dilation`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : PseudoEMetricSpace α] [inst_1 : Ps
eudoEMetricSpace β] (f : α →ᵈ β) {x y : α},   x = y → f x = f y
参数：f : α →ᵈ β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.congr_arg`：∀ {F : Sort u_1} {α : Sort u_2} {β : Sort u_3} [i : 
FunLike F α β] (f : F) {x y : α}, x = y → f x = f y
-/
protected theorem congr_arg (f : α →ᵈ β) {x y : α} (h : x = y) : f x = f y :=
  DFunLike.congr_arg f h

@[ext]
/-
**Dilation.ext** 是 Mathlib 中的一个定理，位于命名空间 `Dilation`。
形式化陈述：ext {f g : α ->ᵈ β} (h : forall x, f x = g x) : f = g
参数：h : forall x, f x = g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext {f g : α →ᵈ β} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h

@[simp]
/-
**Dilation.mk_coe** 是 Mathlib 中的一个定理，位于命名空间 `Dilation`。
形式化陈述：mk_coe (f : α ->ᵈ β) (h) : Dilation.mk f h = f
参数：f : α ->ᵈ β；h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dilation.ext`：ext {f g : α ->ᵈ β} (h : forall x, f x = g x) : f = g
-/
theorem mk_coe (f : α →ᵈ β) (h) : Dilation.mk f h = f :=
  ext fun _ => rfl

/-- Copy of a `Dilation` with a new `toFun` equal to the old one. Useful to fix definitional
equalities. -/
@[simps -fullyApplied]
/-
**Dilation.copy** 是 Mathlib 中的一个定义，位于命名空间 `Dilation`。
形式化陈述：{α : Type u_1} →   {β : Type u_2} →     [inst : PseudoEMetricSpace α] → [i
nst_1 : PseudoEMetricSpace β] → (f : α →ᵈ β) → (f' : α → β) → f' = ⇑f → α →ᵈ β
参数：f : α →ᵈ β；f' : α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Copy of a `Dilation` with a new `toFun` equal to the old one. Useful to fix defi
nitional
equalities.
-/
protected def copy (f : α →ᵈ β) (f' : α → β) (h : f' = ⇑f) : α →ᵈ β where
  toFun := f'
  edist_eq' := h.symm ▸ f.edist_eq'
/-
**Dilation.copy_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `Dilation`。
形式化陈述：copy_eq_self (f : α ->ᵈ β) {f' : α -> β} (h : f' = f) : f.copy f' h = f
参数：f : α ->ᵈ β；h : f' = f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext'`：ext' {f g : F} (h : (f : forall a : α, β a) = (g : forall
 a : α, β a)) : f = g
-/
theorem copy_eq_self (f : α →ᵈ β) {f' : α → β} (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

variable [FunLike F α β]

open scoped Classical in
/-- The ratio of a dilation `f`. If the ratio is undefined (i.e., the distance between any two
points in `α` is either zero or infinity), then we choose one as the ratio. -/
/-
**Dilation.ratio** 是 Mathlib 中的一个定义，位于命名空间 `Dilation`。
形式化陈述：ratio [DilationClass F α β] (f : F) : Real>=0
参数：f : F。
该定义给出了一等式。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `DilationClass.edist_eq'`：∀ {F : Type u_3} {α : outParam (Type u_4)} {β :
 outParam (Type u_5)} {inst : PseudoEMetricSpace α}   {inst_1 : PseudoEMetricSpa
ce β} {inst_2…

--- 原说明 ---
The ratio of a dilation `f`. If the ratio is undefined (i.e., the distance betwe
en any two
points in `α` is either zero or infinity), then we choose one as the ratio.
-/
def ratio [DilationClass F α β] (f : F) : ℝ≥0 :=
  if ∀ x y : α, edist x y = 0 ∨ edist x y = ⊤ then 1 else (DilationClass.edist_eq' f).choose
/-
**Dilation.ratio_of_trivial** 是 Mathlib 中的一个定理，位于命名空间 `Dilation`。
形式化陈述：ratio_of_trivial [DilationClass F α β] (f : F) (h : forall x y : α, edist 
x y = 0 ∨ edist x y = ∞) : ratio f = 1
参数：f : F；h : forall x y : α, edist x y = 0 ∨ edist x y = ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `DilationClass.edist_eq'`：∀ {F : Type u_3} {α : outParam (Type u_4)} {β :
 outParam (Type u_5)} {inst : PseudoEMetricSpace α}   {inst_1 : PseudoEMetricSpa
ce β} {inst_2…
-/
theorem ratio_of_trivial [DilationClass F α β] (f : F)
    (h : ∀ x y : α, edist x y = 0 ∨ edist x y = ∞) : ratio f = 1 :=
  if_pos h

@[nontriviality]
/-
**Dilation.ratio_of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Dilation`。
形式化陈述：ratio_of_subsingleton [Subsingleton α] [DilationClass F α β] (f : F) : rat
io f = 1
参数：f : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `PseudoEMetricSpace.edist_self`：∀ {α : Type u} [self : PseudoEMetricSpace
 α] (x : α), edist x x = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `DilationClass.edist_eq'`：∀ {F : Type u_3} {α : outParam (Type u_4)} {β :
 outParam (Type u_5)} {inst : PseudoEMetricSpace α}   {inst_1 : PseudoEMetricSpa
ce β} {inst_2…
-/
theorem ratio_of_subsingleton [Subsingleton α] [DilationClass F α β] (f : F) : ratio f = 1 :=
  if_pos fun x y ↦ by simp [Subsingleton.elim x y]
/-
**Dilation.ratio_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Dilation`。
形式化陈述：ratio_ne_zero [DilationClass F α β] (f : F) : ratio f != 0
参数：f : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DilationClass.edist_eq'`：∀ {F : Type u_3} {α : outParam (Type u_4)} {β :
 outParam (Type u_5)} {inst : PseudoEMetricSpace α}   {inst_1 : PseudoEMetricSpa
ce β} {inst_2…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Dilation.ratio.eq_1`：∀ {α : Type u_1} {β : Type u_2} {F : Type u_4} [ins
t : PseudoEMetricSpace α] [inst_1 : PseudoEMetricSpace β]   [inst_2 : FunLike F 
α β] [ins…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `NNReal.instIsStrictOrderedRing_1`：IsStrictOrderedRing NNReal
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
theorem ratio_ne_zero [DilationClass F α β] (f : F) : ratio f ≠ 0 := by
  rw [ratio]; split_ifs
  · exact one_ne_zero
  exact (DilationClass.edist_eq' f).choose_spec.1
/-
**Dilation.ratio_pos** 是 Mathlib 中的一个定理，位于命名空间 `Dilation`。
形式化陈述：ratio_pos [DilationClass F α β] (f : F) : 0 < ratio f
参数：f : F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ne.bot_lt`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α] 
{a : α}, a ≠ ⊥ → ⊥ < a
· 使用定理 `Dilation.ratio_ne_zero`：ratio_ne_zero [DilationClass F α β] (f : F) : ra
tio f != 0
-/
theorem ratio_pos [DilationClass F α β] (f : F) : 0 < ratio f :=
  (ratio_ne_zero f).bot_lt

@[simp]
/-
**Dilation.edist_eq** 是 Mathlib 中的一个定理，位于命名空间 `Dilation`。
形式化陈述：edist_eq [DilationClass F α β] (f : F) (x y : α) : edist (f x) (f y) = rat
io f * edist x y
参数：f : F；x y : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DilationClass.edist_eq'`：∀ {F : Type u_3} {α : outParam (Type u_4)} {β :
 outParam (Type u_5)} {inst : PseudoEMetricSpace α}   {inst_1 : PseudoEMetricSpa
ce β} {inst_2…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Dilation.ratio.eq_1`：∀ {α : Type u_1} {β : Type u_2} {F : Type u_4} [ins
t : PseudoEMetricSpace α] [inst_1 : PseudoEMetricSpace β]   [inst_2 : FunLike F 
α β] [ins…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ENNReal.mul_top`：∀ {a : ENNReal}, a ≠ 0 → a * ⊤ = ⊤
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
theorem edist_eq [DilationClass F α β] (f : F) (x y : α) :
    edist (f x) (f y) = ratio f * edist x y := by
  rw [ratio]; split_ifs with key
  · rcases DilationClass.edist_eq' f with ⟨r, hne, hr⟩
    replace hr := hr x y
    rcases key x y with h | h
    · simp only [hr, h, mul_zero]
    · simp [hr, h, hne]
  exact (DilationClass.edist_eq' f).choose_spec.2 x y

@[simp]
/-
**Dilation.nndist_eq** 是 Mathlib 中的一个定理，位于命名空间 `Dilation`。
形式化陈述：nndist_eq {α β F : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β] [Fun
Like F α β] [DilationClass F α β] (f : F) (x y : α) : nndist (f x) (f y) = ratio
 f * nndist x y
参数：f : F；x y : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Dilation.edist_eq`：edist_eq [DilationClass F α β] (f : F) (x y : α) : ed
ist (f x) (f y) = ratio f * edist x y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem nndist_eq {α β F : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β] [FunLike F α β]
    [DilationClass F α β] (f : F) (x y : α) :
    nndist (f x) (f y) = ratio f * nndist x y := by
  simp only [← ENNReal.coe_inj, ← edist_nndist, ENNReal.coe_mul, edist_eq]

@[simp]
/-
**Dilation.dist_eq** 是 Mathlib 中的一个定理，位于命名空间 `Dilation`。
形式化陈述：dist_eq {α β F : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β] [FunLi
ke F α β] [DilationClass F α β] (f : F) (x y : α) : dist (f x) (f y) = ratio f *
 dist x y
参数：f : F；x y : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Dilation.nndist_eq`：nndist_eq {α β F : Type*} [PseudoMetricSpace α] [Pse
udoMetricSpace β] [FunLike F α β] [DilationClass F α β] (f : F) (x y : α) : nndi
st (f x)…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem dist_eq {α β F : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β] [FunLike F α β]
    [DilationClass F α β] (f : F) (x y : α) :
    dist (f x) (f y) = ratio f * dist x y := by
  simp only [dist_nndist, nndist_eq, NNReal.coe_mul]

/-- The `ratio` is equal to the distance ratio for any two points with nonzero finite distance.
`dist` and `nndist` versions below -/
/-
**Dilation.ratio_unique** 是 Mathlib 中的一个定理，位于命名空间 `Dilation`。
形式化陈述：ratio_unique [DilationClass F α β] {f : F} {x y : α} {r : Real>=0} (h₀ : e
dist x y != 0) (htop : edist x y != ⊤) (hr : edist (f x) (f y) = r * edist x y) 
: r = ratio f
参数：h₀ : edist x y != 0；htop : edist x y != ⊤；hr : edist (f x) (f y) = r * edist 
x y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.mul_left_inj`：∀ {a b c : ENNReal}, c ≠ 0 → c ≠ ⊤ → (a * c = b * 
c ↔ a = b)
· 使用定理 `Dilation.edist_eq`：edist_eq [DilationClass F α β] (f : F) (x y : α) : ed
ist (f x) (f y) = ratio f * edist x y

--- 原说明 ---
The `ratio` is equal to the distance ratio for any two points with nonzero finit
e distance.
`dist` and `nndist` versions below
-/
theorem ratio_unique [DilationClass F α β] {f : F} {x y : α} {r : ℝ≥0} (h₀ : edist x y ≠ 0)
    (htop : edist x y ≠ ⊤) (hr : edist (f x) (f y) = r * edist x y) : r = ratio f := by
  simpa only [hr, ENNReal.mul_left_inj h₀ htop, ENNReal.coe_inj] using edist_eq f x y

/-- The `ratio` is equal to the distance ratio for any two points
with nonzero finite distance; `nndist` version -/
/-
**Dilation.ratio_unique_of_nndist_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Dilation`。
形式化陈述：ratio_unique_of_nndist_ne_zero {α β F : Type*} [PseudoMetricSpace α] [Pseu
doMetricSpace β] [FunLike F α β] [DilationClass F α β] {f : F} {x y : α} {r : Re
al>=0} (hxy : nndist x y != 0) (hr : nndist (f x) (f y) = r * nndist x y) : r = 
ratio f
参数：hxy : nndist x y != 0；hr : nndist (f x) (f y) = r * nndist x y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dilation.ratio_unique`：ratio_unique [DilationClass F α β] {f : F} {x y :
 α} {r : Real>=0} (h₀ : edist x y != 0) (htop : edist x y != ⊤) (hr : edist (f x
) (f y) = r…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `edist_nndist`：edist_nndist (x y : α) : edist x y = nndist x y
· 使用定理 `ENNReal.coe_ne_zero`：coe_ne_zero : (r : Real>=0∞) != 0 ↔ r != 0
· 使用定理 `edist_ne_top`：edist_ne_top (x y : α) : edist x y != ⊤
· 使用定理 `ENNReal.coe_mul`：∀ (x y : NNReal), ↑(x * y) = ↑x * ↑y

--- 原说明 ---
The `ratio` is equal to the distance ratio for any two points
with nonzero finite distance; `nndist` version
-/
theorem ratio_unique_of_nndist_ne_zero {α β F : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β]
    [FunLike F α β] [DilationClass F α β] {f : F} {x y : α} {r : ℝ≥0} (hxy : nndist x y ≠ 0)
    (hr : nndist (f x) (f y) = r * nndist x y) : r = ratio f :=
  ratio_unique (by rwa [edist_nndist, ENNReal.coe_ne_zero]) (edist_ne_top x y)
    (by rw [edist_nndist, edist_nndist, hr, ENNReal.coe_mul])

/-- The `ratio` is equal to the distance ratio for any two points
with nonzero finite distance; `dist` version -/
/-
**Dilation.ratio_unique_of_dist_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Dilation`。
形式化陈述：ratio_unique_of_dist_ne_zero {α β} {F : Type*} [PseudoMetricSpace α] [Pseu
doMetricSpace β] [FunLike F α β] [DilationClass F α β] {f : F} {x y : α} {r : Re
al>=0} (hxy : dist x y != 0) (hr : dist (f x) (f y) = r * dist x y) : r = ratio 
f
参数：hxy : dist x y != 0；hr : dist (f x) (f y) = r * dist x y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dilation.ratio_unique_of_nndist_ne_zero`：ratio_unique_of_nndist_ne_zero 
{α β F : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β] [FunLike F α β] [Dil
ationClass F α β] {f : F} {x …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `NNReal.coe_ne_zero`：∀ {r : NNReal}, ↑r ≠ 0 ↔ r ≠ 0
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `coe_nndist`：coe_nndist (x y : α) : ↑(nndist x y) = dist x y
· 使用定理 `NNReal.coe_mul`：∀ (r₁ r₂ : NNReal), ↑(r₁ * r₂) = ↑r₁ * ↑r₂

--- 原说明 ---
The `ratio` is equal to the distance ratio for any two points
with nonzero finite distance; `dist` version
-/
theorem ratio_unique_of_dist_ne_zero {α β} {F : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β]
    [FunLike F α β] [DilationClass F α β] {f : F} {x y : α} {r : ℝ≥0} (hxy : dist x y ≠ 0)
    (hr : dist (f x) (f y) = r * dist x y) : r = ratio f :=
  ratio_unique_of_nndist_ne_zero (NNReal.coe_ne_zero.1 hxy) <|
    NNReal.eq <| by rw [coe_nndist, hr, NNReal.coe_mul, coe_nndist]

/-- Alternative `Dilation` constructor when the distance hypothesis is over `nndist` -/
/-
**Dilation.mkOfNNDistEq** 是 Mathlib 中的一个定义，位于命名空间 `Dilation`。
形式化陈述：mkOfNNDistEq {α β} [PseudoMetricSpace α] [PseudoMetricSpace β] (f : α -> β
) (h : exists r : Real>=0, r != 0 ∧ forall x y : α, nndist (f x) (f y) = r * nnd
ist x y) : α ->ᵈ β where toFun
参数：f : α -> β；h : exists r : Real>=0, r != 0 ∧ forall x y : α, nndist (f x) (f y
) = r * nndist x y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Alternative `Dilation` constructor when the distance hypothesis is over `nndist`
-/
def mkOfNNDistEq {α β} [PseudoMetricSpace α] [PseudoMetricSpace β] (f : α → β)
    (h : ∃ r : ℝ≥0, r ≠ 0 ∧ ∀ x y : α, nndist (f x) (f y) = r * nndist x y) : α →ᵈ β where
  toFun := f
  edist_eq' := by
    rcases h with ⟨r, hne, h⟩
    refine ⟨r, hne, fun x y => ?_⟩
    rw [edist_nndist, edist_nndist, ← ENNReal.coe_mul, h x y]

@[simp]
/-
**Dilation.coe_mkOfNNDistEq** 是 Mathlib 中的一个定理，位于命名空间 `Dilation`。
形式化陈述：coe_mkOfNNDistEq {α β} [PseudoMetricSpace α] [PseudoMetricSpace β] (f : α 
-> β) (h) : ⇑(mkOfNNDistEq f h : α ->ᵈ β) = f
参数：f : α -> β；h。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mkOfNNDistEq {α β} [PseudoMetricSpace α] [PseudoMetricSpace β] (f : α → β) (h) :
    ⇑(mkOfNNDistEq f h : α →ᵈ β) = f :=
  rfl

@[simp]
/-
**Dilation.mk_coe_of_nndist_eq** 是 Mathlib 中的一个定理，位于命名空间 `Dilation`。
形式化陈述：mk_coe_of_nndist_eq {α β} [PseudoMetricSpace α] [PseudoMetricSpace β] (f :
 α ->ᵈ β) (h) : Dilation.mkOfNNDistEq f h = f
参数：f : α ->ᵈ β；h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dilation.ext`：ext {f g : α ->ᵈ β} (h : forall x, f x = g x) : f = g
-/
theorem mk_coe_of_nndist_eq {α β} [PseudoMetricSpace α] [PseudoMetricSpace β] (f : α →ᵈ β)
    (h) : Dilation.mkOfNNDistEq f h = f :=
  ext fun _ => rfl

/-- Alternative `Dilation` constructor when the distance hypothesis is over `dist` -/
/-
**Dilation.mkOfDistEq** 是 Mathlib 中的一个定义，位于命名空间 `Dilation`。
形式化陈述：mkOfDistEq {α β} [PseudoMetricSpace α] [PseudoMetricSpace β] (f : α -> β) 
(h : exists r : Real>=0, r != 0 ∧ forall x y : α, dist (f x) (f y) = r * dist x 
y) : α ->ᵈ β
参数：f : α -> β；h : exists r : Real>=0, r != 0 ∧ forall x y : α, dist (f x) (f y) 
= r * dist x y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Alternative `Dilation` constructor when the distance hypothesis is over `dist`
-/
def mkOfDistEq {α β} [PseudoMetricSpace α] [PseudoMetricSpace β] (f : α → β)
    (h : ∃ r : ℝ≥0, r ≠ 0 ∧ ∀ x y : α, dist (f x) (f y) = r * dist x y) : α →ᵈ β :=
  mkOfNNDistEq f <|
    h.imp fun r hr =>
      ⟨hr.1, fun x y => NNReal.eq <| by rw [coe_nndist, hr.2, NNReal.coe_mul, coe_nndist]⟩

@[simp]
/-
**Dilation.coe_mkOfDistEq** 是 Mathlib 中的一个定理，位于命名空间 `Dilation`。
形式化陈述：coe_mkOfDistEq {α β} [PseudoMetricSpace α] [PseudoMetricSpace β] (f : α ->
 β) (h) : ⇑(mkOfDistEq f h : α ->ᵈ β) = f
参数：f : α -> β；h。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mkOfDistEq {α β} [PseudoMetricSpace α] [PseudoMetricSpace β] (f : α → β) (h) :
    ⇑(mkOfDistEq f h : α →ᵈ β) = f :=
  rfl

@[simp]
/-
**Dilation.mk_coe_of_dist_eq** 是 Mathlib 中的一个定理，位于命名空间 `Dilation`。
形式化陈述：mk_coe_of_dist_eq {α β} [PseudoMetricSpace α] [PseudoMetricSpace β] (f : α
 ->ᵈ β) (h) : Dilation.mkOfDistEq f h = f
参数：f : α ->ᵈ β；h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dilation.ext`：ext {f g : α ->ᵈ β} (h : forall x, f x = g x) : f = g
-/
theorem mk_coe_of_dist_eq {α β} [PseudoMetricSpace α] [PseudoMetricSpace β] (f : α →ᵈ β) (h) :
    Dilation.mkOfDistEq f h = f :=
  ext fun _ => rfl

end Setup

section PseudoEMetricDilation

variable [PseudoEMetricSpace α] [PseudoEMetricSpace β] [PseudoEMetricSpace γ]
variable [FunLike F α β] [DilationClass F α β]
variable (f : F)

/-- Every isometry is a dilation of ratio `1`. -/
@[simps]
/-
**Dilation._root_.Isometry.toDilation** 是 Mathlib 中的一个定义，位于命名空间 `Dilation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every isometry is a dilation of ratio `1`.
-/
def _root_.Isometry.toDilation (f : α → β) (hf : Isometry f) : α →ᵈ β where
  toFun := f
  edist_eq' := ⟨1, one_ne_zero, by simpa using! hf⟩

@[simp]
/-
**Dilation._root_.Isometry.toDilation_ratio** 是 Mathlib 中的一个引理，位于命名空间 `Dilation`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Isometry.toDilation_ratio {f : α → β} {hf : Isometry f} : ratio hf.toDilation = 1 := by
  by_cases! h : ∀ x y : α, edist x y = 0 ∨ edist x y = ⊤
  · exact ratio_of_trivial hf.toDilation h
  · obtain ⟨x, y, h₁, h₂⟩ := h
    exact ratio_unique h₁ h₂ (by simp [hf x y]) |>.symm
/-
**Dilation.lipschitz** 是 Mathlib 中的一个定理，位于命名空间 `Dilation`。
形式化陈述：lipschitz : LipschitzWith (ratio f) (f : α -> β)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Dilation.edist_eq`：edist_eq [DilationClass F α β] (f : F) (x y : α) : ed
ist (f x) (f y) = ratio f * edist x y
-/
theorem lipschitz : LipschitzWith (ratio f) (f : α → β) := fun x y => (edist_eq f x y).le
/-
**Dilation.antilipschitz** 是 Mathlib 中的一个定理，位于命名空间 `Dilation`。
形式化陈述：antilipschitz : AntilipschitzWith (ratio f)⁻¹ (f : α -> β)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dilation.ratio_ne_zero`：ratio_ne_zero [DilationClass F α β] (f : F) : ra
tio f != 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ENNReal.mul_le_iff_le_inv`：mul_le_iff_le_inv {a b r : Real>=0∞} (hr₀ : r
 != 0) (hr₁ : r != ∞) : r * a <= b ↔ a <= r⁻¹ * b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.coe_ne_zero`：coe_ne_zero : (r : Real>=0∞) != 0 ↔ r != 0
· 使用定理 `ENNReal.coe_ne_top`：coe_ne_top : (r : Real>=0∞) != ∞
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Dilation.edist_eq`：edist_eq [DilationClass F α β] (f : F) (x y : α) : ed
ist (f x) (f y) = ratio f * edist x y
-/
theorem antilipschitz : AntilipschitzWith (ratio f)⁻¹ (f : α → β) := fun x y => by
  have hr : ratio f ≠ 0 := ratio_ne_zero f
  exact mod_cast
    (ENNReal.mul_le_iff_le_inv (ENNReal.coe_ne_zero.2 hr) ENNReal.coe_ne_top).1 (edist_eq f x y).ge

/-- A dilation from an emetric space is injective -/
/-
**Dilation.injective** 是 Mathlib 中的一个定理，位于命名空间 `Dilation`。
形式化陈述：∀ {β : Type u_2} {F : Type u_4} [inst : PseudoEMetricSpace β] {α : Type u_
5} [inst_1 : EMetricSpace α]   [inst_2 : FunLike F α β] [DilationClass F α β] (f
 : F), Function.Injective ⇑f
参数：f : F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AntilipschitzWith.injective`：∀ {α : Type u_4} {β : Type u_5} [inst : EMe
tricSpace α] [inst_1 : PseudoEMetricSpace β] {K : NNReal} {f : α → β},   Antilip
schitzWith K f → …
· 使用定理 `Dilation.antilipschitz`：antilipschitz : AntilipschitzWith (ratio f)⁻¹ (f
 : α -> β)

--- 原说明 ---
A dilation from an emetric space is injective
-/
protected theorem injective {α : Type*} [EMetricSpace α] [FunLike F α β] [DilationClass F α β]
    (f : F) :
    Injective f :=
  (antilipschitz f).injective

/-- The identity is a dilation -/
/-
**Dilation.id** 是 Mathlib 中的一个定义，位于命名空间 `Dilation`。
形式化陈述：(α : Type u_5) → [inst : PseudoEMetricSpace α] → α →ᵈ α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity is a dilation
-/
protected def id (α) [PseudoEMetricSpace α] : α →ᵈ α where
  toFun := id
  edist_eq' := ⟨1, one_ne_zero, fun x y => by simp only [id, ENNReal.coe_one, one_mul]⟩
/-
**Dilation.** 是 Mathlib 中的一个实例，位于命名空间 `Dilation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (α →ᵈ α) :=
  ⟨Dilation.id α⟩

@[simp]
/-
**Dilation.coe_id** 是 Mathlib 中的一个定理，位于命名空间 `Dilation`。
形式化陈述：∀ {α : Type u_1} [inst : PseudoEMetricSpace α], ⇑(Dilation.id α) = id
参数：Dilation.id α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem coe_id : ⇑(Dilation.id α) = id :=
  rfl
/-
**Dilation.ratio_id** 是 Mathlib 中的一个定理，位于命名空间 `Dilation`。
形式化陈述：ratio_id : ratio (Dilation.id α) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DilationClass.edist_eq'`：∀ {F : Type u_3} {α : outParam (Type u_4)} {β :
 outParam (Type u_5)} {inst : PseudoEMetricSpace α}   {inst_1 : PseudoEMetricSpa
ce β} {inst_2…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Dilation.ratio.eq_1`：∀ {α : Type u_1} {β : Type u_2} {F : Type u_4} [ins
t : PseudoEMetricSpace α] [inst_1 : PseudoEMetricSpace β]   [inst_2 : FunLike F 
α β] [ins…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Dilation.ratio_unique`：ratio_unique [DilationClass F α β] {f : F} {x y :
 α} {r : Real>=0} (h₀ : edist x y != 0) (htop : edist x y != ⊤) (hr : edist (f x
) (f y) = r…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ratio_id : ratio (Dilation.id α) = 1 := by
  by_cases! h : ∀ x y : α, edist x y = 0 ∨ edist x y = ∞
  · rw [ratio, if_pos h]
  · rcases h with ⟨x, y, hne⟩
    refine (ratio_unique hne.1 hne.2 ?_).symm
    simp

/-- The composition of dilations is a dilation -/
/-
**Dilation.comp** 是 Mathlib 中的一个定义，位于命名空间 `Dilation`。
形式化陈述：comp (g : β ->ᵈ γ) (f : α ->ᵈ β) : α ->ᵈ γ where toFun
参数：g : β ->ᵈ γ；f : α ->ᵈ β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The composition of dilations is a dilation
-/
def comp (g : β →ᵈ γ) (f : α →ᵈ β) : α →ᵈ γ where
  toFun := g ∘ f
  edist_eq' := ⟨ratio g * ratio f, mul_ne_zero (ratio_ne_zero g) (ratio_ne_zero f),
    fun x y => by simp_rw [Function.comp, edist_eq, ENNReal.coe_mul, mul_assoc]⟩
/-
**Dilation.comp_assoc** 是 Mathlib 中的一个定理，位于命名空间 `Dilation`。
形式化陈述：comp_assoc {δ : Type*} [PseudoEMetricSpace δ] (f : α ->ᵈ β) (g : β ->ᵈ γ) 
(h : γ ->ᵈ δ) : (h.comp g).comp f = h.comp (g.comp f)
参数：f : α ->ᵈ β；g : β ->ᵈ γ；h : γ ->ᵈ δ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_assoc {δ : Type*} [PseudoEMetricSpace δ] (f : α →ᵈ β) (g : β →ᵈ γ)
    (h : γ →ᵈ δ) : (h.comp g).comp f = h.comp (g.comp f) :=
  rfl

@[simp]
/-
**Dilation.coe_comp** 是 Mathlib 中的一个定理，位于命名空间 `Dilation`。
形式化陈述：coe_comp (g : β ->ᵈ γ) (f : α ->ᵈ β) : (g.comp f : α -> γ) = g ∘ f
参数：g : β ->ᵈ γ；f : α ->ᵈ β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_comp (g : β →ᵈ γ) (f : α →ᵈ β) : (g.comp f : α → γ) = g ∘ f :=
  rfl
/-
**Dilation.comp_apply** 是 Mathlib 中的一个定理，位于命名空间 `Dilation`。
形式化陈述：comp_apply (g : β ->ᵈ γ) (f : α ->ᵈ β) (x : α) : (g.comp f : α -> γ) x = g
 (f x)
参数：g : β ->ᵈ γ；f : α ->ᵈ β；x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_apply (g : β →ᵈ γ) (f : α →ᵈ β) (x : α) : (g.comp f : α → γ) x = g (f x) :=
  rfl

/-- Ratio of the composition `g.comp f` of two dilations is the product of their ratios. We assume
that there exist two points in `α` at extended distance neither `0` nor `∞` because otherwise
`Dilation.ratio (g.comp f) = Dilation.ratio f = 1` while `Dilation.ratio g` can be any number. This
version works for most general spaces, see also `Dilation.ratio_comp` for a version assuming that
`α` is a nontrivial metric space. -/
/-
**Dilation.ratio_comp'** 是 Mathlib 中的一个定理，位于命名空间 `Dilation`。
形式化陈述：ratio_comp' {g : β ->ᵈ γ} {f : α ->ᵈ β} (hne : exists x y : α, edist x y !
= 0 ∧ edist x y != ⊤) : ratio (g.comp f) = ratio g * ratio f
参数：hne : exists x y : α, edist x y != 0 ∧ edist x y != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Dilation.edist_eq`：edist_eq [DilationClass F α β] (f : F) (x y : α) : ed
ist (f x) (f y) = ratio f * edist x y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.coe_inj`：∀ {p q : NNReal}, ↑p = ↑q ↔ p = q
· 使用定理 `ENNReal.coe_mul`：∀ (x y : NNReal), ↑(x * y) = ↑x * ↑y
· 使用定理 `ENNReal.mul_left_inj`：∀ {a b c : ENNReal}, c ≠ 0 → c ≠ ⊤ → (a * c = b * 
c ↔ a = b)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c

--- 原说明 ---
Ratio of the composition `g.comp f` of two dilations is the product of their rat
ios. We assume
that there exist two points in `α` at extended distance neither `0` nor `∞` beca
use otherwise
`Dilation.ratio (g.comp f) = Dilation.ratio f = 1` while `Dilation.ratio g` can 
be any number. This
version works for most general spaces, see also `Dilation.ratio_comp` for a vers
ion assuming that
`α` is a nontrivial metric space.
-/
theorem ratio_comp' {g : β →ᵈ γ} {f : α →ᵈ β}
    (hne : ∃ x y : α, edist x y ≠ 0 ∧ edist x y ≠ ⊤) : ratio (g.comp f) = ratio g * ratio f := by
  rcases hne with ⟨x, y, hα⟩
  have hgf := (edist_eq (g.comp f) x y).symm
  simp_rw [coe_comp, Function.comp, edist_eq, ← mul_assoc, ENNReal.mul_left_inj hα.1 hα.2]
    at hgf
  rwa [← ENNReal.coe_inj, ENNReal.coe_mul]

@[simp]
/-
**Dilation.comp_id** 是 Mathlib 中的一个定理，位于命名空间 `Dilation`。
形式化陈述：comp_id (f : α ->ᵈ β) : f.comp (Dilation.id α) = f
参数：f : α ->ᵈ β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dilation.ext`：ext {f g : α ->ᵈ β} (h : forall x, f x = g x) : f = g
-/
theorem comp_id (f : α →ᵈ β) : f.comp (Dilation.id α) = f :=
  ext fun _ => rfl

@[simp]
/-
**Dilation.id_comp** 是 Mathlib 中的一个定理，位于命名空间 `Dilation`。
形式化陈述：id_comp (f : α ->ᵈ β) : (Dilation.id β).comp f = f
参数：f : α ->ᵈ β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dilation.ext`：ext {f g : α ->ᵈ β} (h : forall x, f x = g x) : f = g
-/
theorem id_comp (f : α →ᵈ β) : (Dilation.id β).comp f = f :=
  ext fun _ => rfl
/-
**Dilation.** 是 Mathlib 中的一个实例，位于命名空间 `Dilation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Monoid (α →ᵈ α) where
  one := Dilation.id α
  mul := comp
  mul_one := comp_id
  one_mul := id_comp
  mul_assoc _ _ _ := comp_assoc _ _ _
/-
**Dilation.one_def** 是 Mathlib 中的一个定理，位于命名空间 `Dilation`。
形式化陈述：one_def : (1 : α ->ᵈ α) = Dilation.id α
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem one_def : (1 : α →ᵈ α) = Dilation.id α :=
  rfl
/-
**Dilation.mul_def** 是 Mathlib 中的一个定理，位于命名空间 `Dilation`。
形式化陈述：mul_def (f g : α ->ᵈ α) : f * g = f.comp g
参数：f g : α ->ᵈ α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mul_def (f g : α →ᵈ α) : f * g = f.comp g :=
  rfl

@[simp]
/-
**Dilation.coe_one** 是 Mathlib 中的一个定理，位于命名空间 `Dilation`。
形式化陈述：coe_one : ⇑(1 : α ->ᵈ α) = id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_one : ⇑(1 : α →ᵈ α) = id :=
  rfl

@[simp]
/-
**Dilation.coe_mul** 是 Mathlib 中的一个定理，位于命名空间 `Dilation`。
形式化陈述：coe_mul (f g : α ->ᵈ α) : ⇑(f * g) = f ∘ g
参数：f g : α ->ᵈ α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mul (f g : α →ᵈ α) : ⇑(f * g) = f ∘ g :=
  rfl
/-
**Dilation.ratio_one** 是 Mathlib 中的一个定理，位于命名空间 `Dilation`。
形式化陈述：∀ {α : Type u_1} [inst : PseudoEMetricSpace α], Dilation.ratio 1 = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dilation.ratio_id`：ratio_id : ratio (Dilation.id α) = 1
-/
@[simp] theorem ratio_one : ratio (1 : α →ᵈ α) = 1 := ratio_id

@[simp]
/-
**Dilation.ratio_mul** 是 Mathlib 中的一个定理，位于命名空间 `Dilation`。
形式化陈述：ratio_mul (f g : α ->ᵈ α) : ratio (f * g) = ratio f * ratio g
参数：f g : α ->ᵈ α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Dilation.ratio_of_trivial`：ratio_of_trivial [DilationClass F α β] (f : F
) (h : forall x y : α, edist x y = 0 ∨ edist x y = ∞) : ratio f = 1
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Dilation.ratio_comp'`：ratio_comp' {g : β ->ᵈ γ} {f : α ->ᵈ β} (hne : exi
sts x y : α, edist x y != 0 ∧ edist x y != ⊤) : ratio (g.comp f) = ratio g * rat
io f
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem ratio_mul (f g : α →ᵈ α) : ratio (f * g) = ratio f * ratio g := by
  by_cases! h : ∀ x y : α, edist x y = 0 ∨ edist x y = ∞
  · simp [ratio_of_trivial, h]
  exact ratio_comp' h

/-- `Dilation.ratio` as a monoid homomorphism from `α →ᵈ α` to `ℝ≥0`. -/
@[simps]
/-
**Dilation.ratioHom** 是 Mathlib 中的一个定义，位于命名空间 `Dilation`。
形式化陈述：ratioHom : (α ->ᵈ α) ->* Real>=0
该定义给出了一等式。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Dilation.ratio_one`：∀ {α : Type u_1} [inst : PseudoEMetricSpace α], Dila
tion.ratio 1 = 1
· 使用定理 `Dilation.ratio_mul`：ratio_mul (f g : α ->ᵈ α) : ratio (f * g) = ratio f 
* ratio g

--- 原说明 ---
`Dilation.ratio` as a monoid homomorphism from `α →ᵈ α` to `ℝ≥0`.
-/
def ratioHom : (α →ᵈ α) →* ℝ≥0 := ⟨⟨ratio, ratio_one⟩, ratio_mul⟩

@[simp]
/-
**Dilation.ratio_pow** 是 Mathlib 中的一个定理，位于命名空间 `Dilation`。
形式化陈述：ratio_pow (f : α ->ᵈ α) (n : Nat) : ratio (f ^ n) = ratio f ^ n
参数：f : α ->ᵈ α；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.map_pow`：∀ {M : Type u_4} {N : Type u_5} [inst : Monoid M] [in
st_1 : Monoid N] (f : M →* N) (a : M) (n : ℕ), f (a ^ n) = f a ^ n
-/
theorem ratio_pow (f : α →ᵈ α) (n : ℕ) : ratio (f ^ n) = ratio f ^ n :=
  ratioHom.map_pow _ _

@[simp]
/-
**Dilation.cancel_right** 是 Mathlib 中的一个定理，位于命名空间 `Dilation`。
形式化陈述：cancel_right {g₁ g₂ : β ->ᵈ γ} {f : α ->ᵈ β} (hf : Surjective f) : g₁.comp
 f = g₂.comp f ↔ g₁ = g₂
参数：hf : Surjective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dilation.ext`：ext {f g : α ->ᵈ β} (h : forall x, f x = g x) : f = g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Dilation.ext_iff`：∀ {α : Type u_1} {β : Type u_2} [inst : PseudoEMetricS
pace α] [inst_1 : PseudoEMetricSpace β] {f g : α →ᵈ β},   f = g ↔ ∀ (x : α), f x
 = g x
-/
theorem cancel_right {g₁ g₂ : β →ᵈ γ} {f : α →ᵈ β} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => Dilation.ext <| hf.forall.2 (Dilation.ext_iff.1 h), fun h => h ▸ rfl⟩

@[simp]
/-
**Dilation.cancel_left** 是 Mathlib 中的一个定理，位于命名空间 `Dilation`。
形式化陈述：cancel_left {g : β ->ᵈ γ} {f₁ f₂ : α ->ᵈ β} (hg : Injective g) : g.comp f₁
 = g.comp f₂ ↔ f₁ = f₂
参数：hg : Injective g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dilation.ext`：ext {f g : α ->ᵈ β} (h : forall x, f x = g x) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Dilation.comp_apply`：comp_apply (g : β ->ᵈ γ) (f : α ->ᵈ β) (x : α) : (g
.comp f : α -> γ) x = g (f x)
-/
theorem cancel_left {g : β →ᵈ γ} {f₁ f₂ : α →ᵈ β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => Dilation.ext fun x => hg <| by rw [← comp_apply, h, comp_apply], fun h => h ▸ rfl⟩

/-- A dilation from a metric space is a uniform inducing map -/
/-
**Dilation.isUniformInducing** 是 Mathlib 中的一个定理，位于命名空间 `Dilation`。
形式化陈述：isUniformInducing : IsUniformInducing (f : α -> β)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AntilipschitzWith.isUniformInducing`：isUniformInducing (hf : Antilipschi
tzWith K f) (hfc : UniformContinuous f) : IsUniformInducing f
· 使用定理 `Dilation.antilipschitz`：antilipschitz : AntilipschitzWith (ratio f)⁻¹ (f
 : α -> β)
· 使用定理 `LipschitzWith.uniformContinuous`：∀ {α : Type u} {β : Type v} [inst : Pse
udoEMetricSpace α] [inst_1 : PseudoEMetricSpace β] {K : NNReal} {f : α → β},   L
ipschitzWith K f → Un…
· 使用定理 `Dilation.lipschitz`：lipschitz : LipschitzWith (ratio f) (f : α -> β)

--- 原说明 ---
A dilation from a metric space is a uniform inducing map
-/
theorem isUniformInducing : IsUniformInducing (f : α → β) :=
  (antilipschitz f).isUniformInducing (lipschitz f).uniformContinuous
/-
**Dilation.tendsto_nhds_iff** 是 Mathlib 中的一个定理，位于命名空间 `Dilation`。
形式化陈述：tendsto_nhds_iff {ι : Type*} {g : ι -> α} {a : Filter ι} {b : α} : Filter.
Tendsto g a (𝓝 b) ↔ Filter.Tendsto ((f : α -> β) ∘ g) a (𝓝 (f b))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Topology.IsInducing.tendsto_nhds_iff`：tendsto_nhds_iff {f : ι -> Y} {l :
 Filter ι} {y : Y} (hg : IsInducing g) : Tendsto f l (𝓝 y) ↔ Tendsto (g ∘ f) l (
𝓝 (g y))
· 使用定理 `IsUniformInducing.isInducing`：IsUniformInducing.isInducing {f : α -> β} 
(h : IsUniformInducing f) : IsInducing f
· 使用定理 `Dilation.isUniformInducing`：isUniformInducing : IsUniformInducing (f : α
 -> β)
-/
theorem tendsto_nhds_iff {ι : Type*} {g : ι → α} {a : Filter ι} {b : α} :
    Filter.Tendsto g a (𝓝 b) ↔ Filter.Tendsto ((f : α → β) ∘ g) a (𝓝 (f b)) :=
  (Dilation.isUniformInducing f).isInducing.tendsto_nhds_iff

/-- A dilation is continuous. -/
/-
**Dilation.toContinuous** 是 Mathlib 中的一个定理，位于命名空间 `Dilation`。
形式化陈述：toContinuous : Continuous (f : α -> β)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzWith.continuous`：∀ {α : Type u} {β : Type v} [inst : PseudoEMet
ricSpace α] [inst_1 : PseudoEMetricSpace β] {K : NNReal} {f : α → β},   Lipschit
zWith K f → Co…
· 使用定理 `Dilation.lipschitz`：lipschitz : LipschitzWith (ratio f) (f : α -> β)

--- 原说明 ---
A dilation is continuous.
-/
theorem toContinuous : Continuous (f : α → β) :=
  (lipschitz f).continuous

/-- Dilations scale the diameter by `ratio f` in pseudoemetric spaces. -/
/-
**Dilation.ediam_image** 是 Mathlib 中的一个定理，位于命名空间 `Dilation`。
形式化陈述：ediam_image (s : Set α) : ediam ((f : α -> β) '' s) = ratio f * ediam s
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `LipschitzWith.ediam_image_le`：ediam_image_le (hf : LipschitzWith K f) (s
 : Set α) : Metric.ediam (f '' s) <= K * Metric.ediam s
· 使用定理 `Dilation.lipschitz`：lipschitz : LipschitzWith (ratio f) (f : α -> β)
· 使用定理 `ENNReal.mul_le_of_le_div'`：mul_le_of_le_div' (h : a <= b / c) : c * a <=
 b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.coe_inv`：coe_inv (hr : r != 0) : (↑r⁻¹ : Real>=0∞) = (↑r)⁻¹
· 使用定理 `Dilation.ratio_ne_zero`：ratio_ne_zero [DilationClass F α β] (f : F) : ra
tio f != 0
· 使用定理 `AntilipschitzWith.le_mul_ediam_image`：le_mul_ediam_image (hf : Antilipsc
hitzWith K f) (s : Set α) : ediam s <= K * ediam (f '' s)
· 使用定理 `Dilation.antilipschitz`：antilipschitz : AntilipschitzWith (ratio f)⁻¹ (f
 : α -> β)

--- 原说明 ---
Dilations scale the diameter by `ratio f` in pseudoemetric spaces.
-/
theorem ediam_image (s : Set α) : ediam ((f : α → β) '' s) = ratio f * ediam s := by
  refine ((lipschitz f).ediam_image_le s).antisymm ?_
  apply ENNReal.mul_le_of_le_div'
  rw [div_eq_mul_inv, mul_comm, ← ENNReal.coe_inv]
  exacts [(antilipschitz f).le_mul_ediam_image s, ratio_ne_zero f]

/-- A dilation scales the diameter of the range by `ratio f`. -/
/-
**Dilation.ediam_range** 是 Mathlib 中的一个定理，位于命名空间 `Dilation`。
形式化陈述：ediam_range : ediam (range (f : α -> β)) = ratio f * ediam (univ : Set α)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Dilation.ediam_image`：ediam_image (s : Set α) : ediam ((f : α -> β) '' s
) = ratio f * ediam s

--- 原说明 ---
A dilation scales the diameter of the range by `ratio f`.
-/
theorem ediam_range : ediam (range (f : α → β)) = ratio f * ediam (univ : Set α) := by
  rw [← image_univ]; exact ediam_image f univ

/-- A dilation maps balls to balls and scales the radius by `ratio f`. -/
/-
**Dilation.mapsTo_eball** 是 Mathlib 中的一个定理，位于命名空间 `Dilation`。
形式化陈述：mapsTo_eball (x : α) (r : Real>=0∞) : MapsTo (f : α -> β) (Metric.eball x 
r) (Metric.eball (f x) (ratio f * r))
参数：x : α；r : Real>=0∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.mem_eball`：∀ {α : Type u} [inst : EDist α] {x y : α} {ε : ENNReal
}, y ∈ Metric.eball x ε ↔ edist y x < ε
· 使用定理 `Dilation.edist_eq`：edist_eq [DilationClass F α β] (f : F) (x y : α) : ed
ist (f x) (f y) = ratio f * edist x y
· 使用定理 `ENNReal.mul_lt_mul_right`：∀ {a b c : ENNReal}, a ≠ 0 → a ≠ ⊤ → b < c → a
 * b < a * c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `not_false_eq_true`：(¬False) = True

--- 原说明 ---
A dilation maps balls to balls and scales the radius by `ratio f`.
-/
theorem mapsTo_eball (x : α) (r : ℝ≥0∞) :
    MapsTo (f : α → β) (Metric.eball x r) (Metric.eball (f x) (ratio f * r)) :=
  fun y (hy : _ < r) ↦ by rw [Metric.mem_eball, edist_eq f y x]; gcongr <;> simp [ratio_ne_zero, *]

@[deprecated (since := "2026-01-24")]
alias mapsTo_emetric_ball := mapsTo_eball

/-- A dilation maps closed balls to closed balls and scales the radius by `ratio f`. -/
/-
**Dilation.mapsTo_closedEBall** 是 Mathlib 中的一个定理，位于命名空间 `Dilation`。
形式化陈述：mapsTo_closedEBall (x : α) (r' : Real>=0∞) : MapsTo (f : α -> β) (Metric.c
losedEBall x r') (Metric.closedEBall (f x) (ratio f * r'))
参数：x : α；r' : Real>=0∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ c →
 a ≤ c
· 使用定理 `Dilation.edist_eq`：edist_eq [DilationClass F α β] (f : F) (x y : α) : ed
ist (f x) (f y) = ratio f * edist x y
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `ENNReal.instIsOrderedMonoid`：IsOrderedMonoid ENNReal
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a

--- 原说明 ---
A dilation maps closed balls to closed balls and scales the radius by `ratio f`.
-/
theorem mapsTo_closedEBall (x : α) (r' : ℝ≥0∞) :
    MapsTo (f : α → β) (Metric.closedEBall x r') (Metric.closedEBall (f x) (ratio f * r')) :=
  fun y hy => (edist_eq f y x).trans_le <| by gcongr; exact hy

@[deprecated (since := "2026-01-24")]
alias mapsTo_emetric_closedBall := mapsTo_closedEBall
/-
**Dilation.comp_continuousOn_iff** 是 Mathlib 中的一个定理，位于命名空间 `Dilation`。
形式化陈述：comp_continuousOn_iff {γ} [TopologicalSpace γ] {g : γ -> α} {s : Set γ} : 
ContinuousOn ((f : α -> β) ∘ g) s ↔ ContinuousOn g s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用引理 `Topology.IsInducing.continuousOn_iff`：Topology.IsInducing.continuousOn_i
ff {f : α -> β} {g : β -> γ} (hg : IsInducing g) {s : Set α} : ContinuousOn f s 
↔ ContinuousOn (g ∘ f) s
· 使用定理 `IsUniformInducing.isInducing`：IsUniformInducing.isInducing {f : α -> β} 
(h : IsUniformInducing f) : IsInducing f
· 使用定理 `Dilation.isUniformInducing`：isUniformInducing : IsUniformInducing (f : α
 -> β)
-/
theorem comp_continuousOn_iff {γ} [TopologicalSpace γ] {g : γ → α} {s : Set γ} :
    ContinuousOn ((f : α → β) ∘ g) s ↔ ContinuousOn g s :=
  (Dilation.isUniformInducing f).isInducing.continuousOn_iff.symm
/-
**Dilation.comp_continuous_iff** 是 Mathlib 中的一个定理，位于命名空间 `Dilation`。
形式化陈述：comp_continuous_iff {γ} [TopologicalSpace γ] {g : γ -> α} : Continuous ((f
 : α -> β) ∘ g) ↔ Continuous g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用引理 `Topology.IsInducing.continuous_iff`：continuous_iff (hg : IsInducing g) :
 Continuous f ↔ Continuous (g ∘ f)
· 使用定理 `IsUniformInducing.isInducing`：IsUniformInducing.isInducing {f : α -> β} 
(h : IsUniformInducing f) : IsInducing f
· 使用定理 `Dilation.isUniformInducing`：isUniformInducing : IsUniformInducing (f : α
 -> β)
-/
theorem comp_continuous_iff {γ} [TopologicalSpace γ] {g : γ → α} :
    Continuous ((f : α → β) ∘ g) ↔ Continuous g :=
  (Dilation.isUniformInducing f).isInducing.continuous_iff.symm

end PseudoEMetricDilation

section EMetricDilation

variable [EMetricSpace α]
variable [FunLike F α β]

/-- A dilation from a metric space is a uniform embedding -/
/-
**Dilation.isUniformEmbedding** 是 Mathlib 中的一个引理，位于命名空间 `Dilation`。
形式化陈述：isUniformEmbedding [PseudoEMetricSpace β] [DilationClass F α β] (f : F) : 
IsUniformEmbedding f
参数：f : F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AntilipschitzWith.isUniformEmbedding`：isUniformEmbedding {α β : Type*} [
EMetricSpace α] [PseudoEMetricSpace β] {K : Real>=0} {f : α -> β} (hf : Antilips
chitzWith K f) (hfc : Unif…
· 使用定理 `Dilation.antilipschitz`：antilipschitz : AntilipschitzWith (ratio f)⁻¹ (f
 : α -> β)
· 使用定理 `LipschitzWith.uniformContinuous`：∀ {α : Type u} {β : Type v} [inst : Pse
udoEMetricSpace α] [inst_1 : PseudoEMetricSpace β] {K : NNReal} {f : α → β},   L
ipschitzWith K f → Un…
· 使用定理 `Dilation.lipschitz`：lipschitz : LipschitzWith (ratio f) (f : α -> β)

--- 原说明 ---
A dilation from a metric space is a uniform embedding
-/
lemma isUniformEmbedding [PseudoEMetricSpace β] [DilationClass F α β] (f : F) :
    IsUniformEmbedding f :=
  (antilipschitz f).isUniformEmbedding (lipschitz f).uniformContinuous

/-- A dilation from a metric space is an embedding -/
/-
**Dilation.isEmbedding** 是 Mathlib 中的一个定理，位于命名空间 `Dilation`。
形式化陈述：isEmbedding [PseudoEMetricSpace β] [DilationClass F α β] (f : F) : IsEmbed
ding (f : α -> β)
参数：f : F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUniformEmbedding.isEmbedding`：∀ {α : Type u} {β : Type v} [inst : Unif
ormSpace α] [inst_1 : UniformSpace β] {f : α → β},   IsUniformEmbedding f → Topo
logy.IsEmbedding f
· 使用引理 `Dilation.isUniformEmbedding`：isUniformEmbedding [PseudoEMetricSpace β] [
DilationClass F α β] (f : F) : IsUniformEmbedding f

--- 原说明 ---
A dilation from a metric space is an embedding
-/
theorem isEmbedding [PseudoEMetricSpace β] [DilationClass F α β] (f : F) :
    IsEmbedding (f : α → β) :=
  (Dilation.isUniformEmbedding f).isEmbedding

/-- A dilation from a complete emetric space is a closed embedding -/
/-
**Dilation.isClosedEmbedding** 是 Mathlib 中的一个引理，位于命名空间 `Dilation`。
形式化陈述：isClosedEmbedding [CompleteSpace α] [EMetricSpace β] [DilationClass F α β]
 (f : F) : IsClosedEmbedding f
参数：f : F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AntilipschitzWith.isClosedEmbedding`：isClosedEmbedding {α : Type*} {β : 
Type*} [EMetricSpace α] [EMetricSpace β] {K : Real>=0} {f : α -> β} [CompleteSpa
ce α] (hf : Antilipschitz…
· 使用定理 `Dilation.antilipschitz`：antilipschitz : AntilipschitzWith (ratio f)⁻¹ (f
 : α -> β)
· 使用定理 `LipschitzWith.uniformContinuous`：∀ {α : Type u} {β : Type v} [inst : Pse
udoEMetricSpace α] [inst_1 : PseudoEMetricSpace β] {K : NNReal} {f : α → β},   L
ipschitzWith K f → Un…
· 使用定理 `Dilation.lipschitz`：lipschitz : LipschitzWith (ratio f) (f : α -> β)

--- 原说明 ---
A dilation from a complete emetric space is a closed embedding
-/
lemma isClosedEmbedding [CompleteSpace α] [EMetricSpace β] [DilationClass F α β] (f : F) :
    IsClosedEmbedding f :=
  (antilipschitz f).isClosedEmbedding (lipschitz f).uniformContinuous

end EMetricDilation

/-- Ratio of the composition `g.comp f` of two dilations is the product of their ratios. We assume
that the domain `α` of `f` is a nontrivial metric space, otherwise
`Dilation.ratio f = Dilation.ratio (g.comp f) = 1` but `Dilation.ratio g` may have any value.

See also `Dilation.ratio_comp'` for a version that works for more general spaces. -/
@[simp]
/-
**Dilation.ratio_comp** 是 Mathlib 中的一个定理，位于命名空间 `Dilation`。
形式化陈述：ratio_comp [MetricSpace α] [Nontrivial α] [PseudoEMetricSpace β] [PseudoEM
etricSpace γ] {g : β ->ᵈ γ} {f : α ->ᵈ β} : ratio (g.comp f) = ratio g * ratio f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dilation.ratio_comp'`：ratio_comp' {g : β ->ᵈ γ} {f : α ->ᵈ β} (hne : exi
sts x y : α, edist x y != 0 ∧ edist x y != ⊤) : ratio (g.comp f) = ratio g * rat
io f
· 使用定理 `exists_pair_ne`：exists_pair_ne (α : Type*) [Nontrivial α] : exists x y :
 α, x != y
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `edist_eq_zero`：edist_eq_zero {x y : γ} : edist x y = 0 ↔ x = y
· 使用定理 `edist_ne_top`：edist_ne_top (x y : α) : edist x y != ⊤

--- 原说明 ---
Ratio of the composition `g.comp f` of two dilations is the product of their rat
ios. We assume
that the domain `α` of `f` is a nontrivial metric space, otherwise
`Dilation.ratio f = Dilation.ratio (g.comp f) = 1` but `Dilation.ratio g` may ha
ve any value.

See also `Dilation.ratio_comp'` for a version that works for more general spaces
.
-/
theorem ratio_comp [MetricSpace α] [Nontrivial α] [PseudoEMetricSpace β]
    [PseudoEMetricSpace γ] {g : β →ᵈ γ} {f : α →ᵈ β} : ratio (g.comp f) = ratio g * ratio f :=
  ratio_comp' <|
    let ⟨x, y, hne⟩ := exists_pair_ne α; ⟨x, y, mt edist_eq_zero.1 hne, edist_ne_top _ _⟩

section PseudoMetricDilation

variable [PseudoMetricSpace α] [PseudoMetricSpace β] [FunLike F α β] [DilationClass F α β] (f : F)

/-- A dilation scales the diameter by `ratio f` in pseudometric spaces. -/
/-
**Dilation.diam_image** 是 Mathlib 中的一个定理，位于命名空间 `Dilation`。
形式化陈述：diam_image (s : Set α) : diam ((f : α -> β) '' s) = ratio f * diam s
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Dilation.ediam_image`：ediam_image (s : Set α) : ediam ((f : α -> β) '' s
) = ratio f * ediam s
· 使用定理 `ENNReal.toReal_mul`：toReal_mul : (a * b).toReal = a.toReal * b.toReal
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A dilation scales the diameter by `ratio f` in pseudometric spaces.
-/
theorem diam_image (s : Set α) : diam ((f : α → β) '' s) = ratio f * diam s := by
  simp [diam, ediam_image, ENNReal.toReal_mul]
/-
**Dilation.diam_range** 是 Mathlib 中的一个定理，位于命名空间 `Dilation`。
形式化陈述：diam_range : diam (range (f : α -> β)) = ratio f * diam (univ : Set α)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Dilation.diam_image`：diam_image (s : Set α) : diam ((f : α -> β) '' s) =
 ratio f * diam s
-/
theorem diam_range : diam (range (f : α → β)) = ratio f * diam (univ : Set α) := by
  rw [← image_univ, diam_image]

/-- A dilation maps balls to balls and scales the radius by `ratio f`. -/
/-
**Dilation.mapsTo_ball** 是 Mathlib 中的一个定理，位于命名空间 `Dilation`。
形式化陈述：mapsTo_ball (x : α) (r' : Real) : MapsTo (f : α -> β) (Metric.ball x r') (
Metric.ball (f x) (ratio f * r'))
参数：x : α；r' : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans_lt`：∀ {α : Type u_1} {a b c : α} [inst : LT α], a = b → b < c →
 a < c
· 使用定理 `Dilation.dist_eq`：dist_eq {α β F : Type*} [PseudoMetricSpace α] [PseudoM
etricSpace β] [FunLike F α β] [DilationClass F α β] (f : F) (x y : α) : dist (f 
x) (f …
· 使用定理 `mul_lt_mul_of_pos_left`：mul_lt_mul_of_pos_left [PosMulStrictMono α] (hbc
 : b < c) (ha : 0 < a) : a * b < a * c
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Dilation.ratio_pos`：ratio_pos [DilationClass F α β] (f : F) : 0 < ratio 
f

--- 原说明 ---
A dilation maps balls to balls and scales the radius by `ratio f`.
-/
theorem mapsTo_ball (x : α) (r' : ℝ) :
    MapsTo (f : α → β) (Metric.ball x r') (Metric.ball (f x) (ratio f * r')) :=
  fun y hy => (dist_eq f y x).trans_lt <| by gcongr; exacts [ratio_pos _, hy]

/-- A dilation maps spheres to spheres and scales the radius by `ratio f`. -/
/-
**Dilation.mapsTo_sphere** 是 Mathlib 中的一个定理，位于命名空间 `Dilation`。
形式化陈述：mapsTo_sphere (x : α) (r' : Real) : MapsTo (f : α -> β) (Metric.sphere x r
') (Metric.sphere (f x) (ratio f * r'))
参数：x : α；r' : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dilation.dist_eq`：dist_eq {α β F : Type*} [PseudoMetricSpace α] [PseudoM
etricSpace β] [FunLike F α β] [DilationClass F α β] (f : F) (x y : α) : dist (f 
x) (f …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Metric.mem_sphere`：∀ {α : Type u} [inst : PseudoMetricSpace α] {x y : α}
 {ε : ℝ}, y ∈ Metric.sphere x ε ↔ dist y x = ε

--- 原说明 ---
A dilation maps spheres to spheres and scales the radius by `ratio f`.
-/
theorem mapsTo_sphere (x : α) (r' : ℝ) :
    MapsTo (f : α → β) (Metric.sphere x r') (Metric.sphere (f x) (ratio f * r')) :=
  fun y hy => Metric.mem_sphere.mp hy ▸ dist_eq f y x

/-- A dilation maps closed balls to closed balls and scales the radius by `ratio f`. -/
/-
**Dilation.mapsTo_closedBall** 是 Mathlib 中的一个定理，位于命名空间 `Dilation`。
形式化陈述：mapsTo_closedBall (x : α) (r' : Real) : MapsTo (f : α -> β) (Metric.closed
Ball x r') (Metric.closedBall (f x) (ratio f * r'))
参数：x : α；r' : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ c →
 a ≤ c
· 使用定理 `Dilation.dist_eq`：dist_eq {α β F : Type*} [PseudoMetricSpace α] [PseudoM
etricSpace β] [FunLike F α β] [DilationClass F α β] (f : F) (x y : α) : dist (f 
x) (f …
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `NNReal.coe_nonneg`：∀ (r : NNReal), 0 ≤ ↑r

--- 原说明 ---
A dilation maps closed balls to closed balls and scales the radius by `ratio f`.
-/
theorem mapsTo_closedBall (x : α) (r' : ℝ) :
    MapsTo (f : α → β) (Metric.closedBall x r') (Metric.closedBall (f x) (ratio f * r')) :=
  fun y hy => (dist_eq f y x).trans_le <| mul_le_mul_of_nonneg_left hy (NNReal.coe_nonneg _)
/-
**Dilation.tendsto_cobounded** 是 Mathlib 中的一个引理，位于命名空间 `Dilation`。
形式化陈述：tendsto_cobounded : Filter.Tendsto f (cobounded α) (cobounded β)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AntilipschitzWith.tendsto_cobounded`：tendsto_cobounded (hf : Antilipschi
tzWith K f) : Tendsto f (cobounded α) (cobounded β)
· 使用定理 `Dilation.antilipschitz`：antilipschitz : AntilipschitzWith (ratio f)⁻¹ (f
 : α -> β)
-/
lemma tendsto_cobounded : Filter.Tendsto f (cobounded α) (cobounded β) :=
  (Dilation.antilipschitz f).tendsto_cobounded

@[simp]
/-
**Dilation.comap_cobounded** 是 Mathlib 中的一个引理，位于命名空间 `Dilation`。
形式化陈述：comap_cobounded : Filter.comap f (cobounded β) = cobounded α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `LipschitzWith.comap_cobounded_le`：comap_cobounded_le (hf : LipschitzWith
 K f) : comap f (Bornology.cobounded β) <= Bornology.cobounded α
· 使用定理 `Dilation.lipschitz`：lipschitz : LipschitzWith (ratio f) (f : α -> β)
· 使用定理 `Filter.Tendsto.le_comap`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l₁
 : Filter α} {l₂ : Filter β},   Filter.Tendsto f l₁ l₂ → l₁ ≤ Filter.comap f l₂
· 使用引理 `Dilation.tendsto_cobounded`：tendsto_cobounded : Filter.Tendsto f (coboun
ded α) (cobounded β)
-/
lemma comap_cobounded : Filter.comap f (cobounded β) = cobounded α :=
  le_antisymm (lipschitz f).comap_cobounded_le (tendsto_cobounded f).le_comap

end PseudoMetricDilation

end Dilation

