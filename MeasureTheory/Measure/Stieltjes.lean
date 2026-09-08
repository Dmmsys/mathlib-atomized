/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov, Sébastien Gouëzel
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Topology.Order.LeftRightLim

/-!
# Stieltjes measures on the real line

Consider a function `f : ℝ → ℝ` which is monotone and right-continuous. Then one can define a
corresponding measure, giving mass `f b - f a` to the interval `(a, b]`. We implement more
generally this notion for `f : R → ℝ` where `R` is a conditionally complete dense linear order.

## Main definitions

* `StieltjesFunction R` is a structure containing a function from `R → ℝ`, together with the
  assertions that it is monotone and right-continuous. To `f : StieltjesFunction R`, one associates
  a Borel measure `f.measure`.
* `f.measure_Ioc` asserts that `f.measure (Ioc a b) = ofReal (f b - f a)`
* `f.measure_Ioo` asserts that `f.measure (Ioo a b) = ofReal (leftLim f b - f a)`.
* `f.measure_Icc` and `f.measure_Ico` are analogous.
* `Monotone.stieltjesFunction`: to a monotone function `f`, associate the Stieltjes function
  equal to the right limit of `f`. This makes it possible to associate a Stieltjes measure to
  any monotone function.

## Implementation

We define Stieltjes functions over any conditionally complete dense linear order, to be able
to cover the cases of `ℝ≥0` and `[0, T]` in addition to the classical case of `ℝ`. This creates
a few issues, mostly with the management of bottom and top elements. To handle these, we need
two technical definitions:
* `Iotop a b` is the interval `Ioo a b` if `b` is not top, and `Ioc a b` if `b` is top.
* `botSet` is the empty set if there is no bot element, and `{x}` if `x` is bot.

Note that the theory of Stieltjes measures is not completely satisfactory when there is a bot
element `x`: any Stieltjes measure gives zero mass to `{x}` in this case, so the Dirac mass at `x`
is not representable as a Stieltjes measure.
-/

@[expose] public section

noncomputable section

open Set Filter Function ENNReal NNReal Topology MeasureTheory

open ENNReal (ofReal)

section Prerequisites

variable {R : Type*} [LinearOrder R]

open scoped Classical in
/-- `Iotop a b` is the interval `Ioo a b` if `b` is not top, and `Ioc a b` if `b` is top.
This makes sure that any element which is not bot belongs to an interval `Iotop a b`, and also
that these intervals are all open. These two properties together are important in the proof of
`StieltjesFunction.outer_Ioc`. -/
/-
**Iotop** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Iotop (a b : R) : Set R
参数：a b : R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Iotop a b` is the interval `Ioo a b` if `b` is not top, and `Ioc a b` if `b` is
 top.
This makes sure that any element which is not bot belongs to an interval `Iotop 
a b`, and also
that these intervals are all open. These two properties together are important i
n the proof of
`StieltjesFunction.outer_Ioc`.
-/
def Iotop (a b : R) : Set R := if IsTop b then Ioc a b else Ioo a b
/-
**Iotop_subset_Ioc** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Iotop_subset_Ioc {a b : R} : Iotop a b subseteq Ioc a b
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
lemma Iotop_subset_Ioc {a b : R} : Iotop a b ⊆ Ioc a b := by
  simp only [Iotop]
  split_ifs with h <;> simp [Ioo_subset_Ioc_self]
/-
**Ioo_subset_Iotop** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ioo_subset_Iotop {a b : R} : Ioo a b subseteq Iotop a b
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
lemma Ioo_subset_Iotop {a b : R} : Ioo a b ⊆ Iotop a b := by
  simp only [Iotop]
  split_ifs with h <;> simp [Ioo_subset_Ioc_self]
/-
**isOpen_Iotop** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isOpen_Iotop [TopologicalSpace R] [OrderTopology R] (a b : R) : IsOpen (Io
top a b)
参数：a b : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
lemma isOpen_Iotop [TopologicalSpace R] [OrderTopology R] (a b : R) : IsOpen (Iotop a b) := by
  simp only [Iotop]
  split_ifs with h
  · have : Ioc a b = Ioi a := Subset.antisymm (fun x hx ↦ hx.1) (fun x hx ↦ by exact ⟨hx, h _⟩)
    simp [this, isOpen_Ioi]
  · simp [isOpen_Ioo]

/-- `botSet` is the set of all bottom elements. -/
/-
**botSet** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：botSet : Set R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`botSet` is the set of all bottom elements.
-/
def botSet : Set R := {x | IsBot x}
/-
**Ioc_sdiff_botSet** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {R : Type u_1} [inst : LinearOrder R] (a b : R), Set.Ioc a b \ botSet = 
Set.Ioc a b
参数：a b : R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sdiff_eq_left`：∀ {α : Type u} {x y : α} [inst : GeneralizedBooleanAlgebr
a α], x \ y = x ↔ Disjoint x y
· 使用引理 `Set.disjoint_iff_forall_ne`：disjoint_iff_forall_ne : Disjoint s t ↔ fora
ll ⦃a⦄, a in s -> forall ⦃b⦄, b in t -> a != b
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
-/
@[simp] lemma Ioc_sdiff_botSet (a b : R) : Ioc a b \ botSet = Ioc a b := by
  rw [sdiff_eq_left, disjoint_iff_forall_ne]
  rintro c ⟨hc, _⟩ _ hc' rfl
  exact (hc' a).not_gt hc

@[deprecated (since := "2026-06-03")] alias Ioc_diff_botSet := Ioc_sdiff_botSet
/-
**notMem_botSet_of_lt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：notMem_botSet_of_lt {x y : R} (h : x < y) : y ∉ botSet
参数：h : x < y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₃`：contrapose₃ {p q : Prop} : (q -> 
¬ p) -> (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
lemma notMem_botSet_of_lt {x y : R} (h : x < y) : y ∉ botSet := by
  contrapose! h
  exact h x
/-
**subsingleton_botSet** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：subsingleton_botSet : (botSet (R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.subsingleton_isBot`：∀ (α : Type u_1) [inst : PartialOrder α], {x | I
sBot x}.Subsingleton
-/
lemma subsingleton_botSet : (botSet (R := R)).Subsingleton :=
  subsingleton_isBot _
/-
**measurableSet_botSet** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：measurableSet_botSet [MeasurableSpace R] [MeasurableSingletonClass R] : Me
asurableSet (botSet (R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subsingleton.measurableSet`：Set.Subsingleton.measurableSet {s : Set 
α} (hs : s.Subsingleton) : MeasurableSet s
· 使用引理 `subsingleton_botSet`：subsingleton_botSet : (botSet (R
-/
lemma measurableSet_botSet [MeasurableSpace R] [MeasurableSingletonClass R] :
    MeasurableSet (botSet (R := R)) :=
  subsingleton_botSet.measurableSet
/-
**botSet_eq_singleton_of_isBot** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：botSet_eq_singleton_of_isBot {x : R} (hx : IsBot x) : botSet = {x}
参数：hx : IsBot x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subsingleton.eq_singleton_of_mem`：∀ {α : Type u} {s : Set α}, s.Subs
ingleton → ∀ {x : α}, x ∈ s → s = {x}
· 使用引理 `subsingleton_botSet`：subsingleton_botSet : (botSet (R
-/
lemma botSet_eq_singleton_of_isBot {x : R} (hx : IsBot x) : botSet = {x} :=
  (subsingleton_botSet (R := R)).eq_singleton_of_mem hx

end Prerequisites

variable (R : Type*) [LinearOrder R] [TopologicalSpace R]

/-! ### Basic properties of Stieltjes functions -/

/-- Bundled monotone right-continuous real functions, used to construct Stieltjes measures. -/
/-
**StieltjesFunction** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u_1) → [LinearOrder R] → [TopologicalSpace R] → Type u_1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Bundled monotone right-continuous real functions, used to construct Stieltjes me
asures.
-/
structure StieltjesFunction where
  /-- The underlying function `R → ℝ`.

  Do NOT use directly. Use the coercion instead. -/
  toFun : R → ℝ
  mono' : Monotone toFun
  right_continuous' : ∀ x, ContinuousWithinAt toFun (Ici x) x

namespace StieltjesFunction

variable {R}

attribute [coe] toFun

/-
**StieltjesFunction.instCoeFun** 是 Mathlib 中的一个实例，位于命名空间 `StieltjesFunction`。
形式化陈述：instCoeFun : CoeFun (StieltjesFunction R) fun _ => R -> Real
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCoeFun : CoeFun (StieltjesFunction R) fun _ => R → ℝ :=
  ⟨toFun⟩

initialize_simps_projections StieltjesFunction (toFun → apply)
/-
**StieltjesFunction.ext** 是 Mathlib 中的一个定理，位于命名空间 `StieltjesFunction`。
形式化陈述：∀ {R : Type u_1} [inst : LinearOrder R] [inst_1 : TopologicalSpace R] {f g
 : StieltjesFunction R},   (∀ (x : R), ↑f x = ↑g x) → f = g
参数：∀ (x : R), ↑f x = ↑g x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StieltjesFunction.mono'`：∀ {R : Type u_1} [inst : LinearOrder R] [inst_1
 : TopologicalSpace R] (self : StieltjesFunction R), Monotone ↑self
· 使用定理 `StieltjesFunction.right_continuous'`：∀ {R : Type u_1} [inst : LinearOrde
r R] [inst_1 : TopologicalSpace R] (self : StieltjesFunction R) (x : R),   Conti
nuousWithinAt (↑self) (Se…
· 使用定理 `StieltjesFunction.mk.injEq`：∀ {R : Type u_1} [inst : LinearOrder R] [ins
t_1 : TopologicalSpace R] (toFun : R → ℝ) (mono' : Monotone toFun)   (right_cont
inuous' : ∀ (x :…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
@[ext] lemma ext {f g : StieltjesFunction R} (h : ∀ x, f x = g x) : f = g := by
  exact (StieltjesFunction.mk.injEq ..).mpr (funext h)

variable (f : StieltjesFunction R)

@[gcongr]
/-
**StieltjesFunction.mono** 是 Mathlib 中的一个定理，位于命名空间 `StieltjesFunction`。
形式化陈述：mono : Monotone f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StieltjesFunction.mono'`：∀ {R : Type u_1} [inst : LinearOrder R] [inst_1
 : TopologicalSpace R] (self : StieltjesFunction R), Monotone ↑self
-/
theorem mono : Monotone f :=
  f.mono'
/-
**StieltjesFunction.right_continuous** 是 Mathlib 中的一个定理，位于命名空间 `StieltjesFunctio
n`。
形式化陈述：right_continuous (x : R) : ContinuousWithinAt f (Ici x) x
参数：x : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StieltjesFunction.right_continuous'`：∀ {R : Type u_1} [inst : LinearOrde
r R] [inst_1 : TopologicalSpace R] (self : StieltjesFunction R) (x : R),   Conti
nuousWithinAt (↑self) (Se…
-/
theorem right_continuous (x : R) : ContinuousWithinAt f (Ici x) x :=
  f.right_continuous' x
/-
**StieltjesFunction.rightLim_eq** 是 Mathlib 中的一个定理，位于命名空间 `StieltjesFunction`。
形式化陈述：rightLim_eq [OrderTopology R] (f : StieltjesFunction R) (x : R) : Function
.rightLim f x = f x
参数：f : StieltjesFunction R；x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Monotone.continuousWithinAt_Ioi_iff_rightLim_eq`：continuousWithinAt_Ioi_
iff_rightLim_eq : ContinuousWithinAt f (Ioi x) x ↔ rightLim f x = f x
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `StieltjesFunction.mono`：mono : Monotone f
· 使用定理 `continuousWithinAt_Ioi_iff_Ici`：continuousWithinAt_Ioi_iff_Ici {a : α} {
f : α -> β} : ContinuousWithinAt f (Ioi a) a ↔ ContinuousWithinAt f (Ici a) a
· 使用定理 `StieltjesFunction.right_continuous'`：∀ {R : Type u_1} [inst : LinearOrde
r R] [inst_1 : TopologicalSpace R] (self : StieltjesFunction R) (x : R),   Conti
nuousWithinAt (↑self) (Se…
-/
theorem rightLim_eq [OrderTopology R]
    (f : StieltjesFunction R) (x : R) : Function.rightLim f x = f x := by
  rw [← f.mono.continuousWithinAt_Ioi_iff_rightLim_eq, continuousWithinAt_Ioi_iff_Ici]
  exact f.right_continuous' x
/-
**StieltjesFunction.iInf_Ioi_eq** 是 Mathlib 中的一个定理，位于命名空间 `StieltjesFunction`。
形式化陈述：iInf_Ioi_eq [OrderTopology R] [DenselyOrdered R] [NoMaxOrder R] (f : Stiel
tjesFunction R) (x : R) : ⨅ r : Ioi x, f r = f x
参数：f : StieltjesFunction R；x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Monotone.rightLim_eq_sInf`：rightLim_eq_sInf [TopologicalSpace α] [OrderT
opology α] [(𝓝[>] x).NeBot] : rightLim f x = sInf (f '' Ioi x)
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `StieltjesFunction.mono`：mono : Monotone f
· 使用定理 `sInf_image'`：∀ {α : Type u_1} {β : Type u_2} [inst : InfSet α] {s : Set 
β} {f : β → α}, sInf (f '' s) = ⨅ a, f ↑a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `StieltjesFunction.rightLim_eq`：rightLim_eq [OrderTopology R] (f : Stielt
jesFunction R) (x : R) : Function.rightLim f x = f x
-/
theorem iInf_Ioi_eq [OrderTopology R] [DenselyOrdered R] [NoMaxOrder R]
     (f : StieltjesFunction R) (x : R) : ⨅ r : Ioi x, f r = f x := by
  suffices Function.rightLim f x = ⨅ r : Ioi x, f r by rw [← this, f.rightLim_eq]
  rw [f.mono.rightLim_eq_sInf, sInf_image']
/-
**StieltjesFunction.iInf_rat_gt_eq** 是 Mathlib 中的一个定理，位于命名空间 `StieltjesFunction`
。
形式化陈述：iInf_rat_gt_eq (f : StieltjesFunction Real) (x : Real) : ⨅ r : { r' : Rat 
// x < r' }, f r = f x
参数：f : StieltjesFunction Real；x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `StieltjesFunction.iInf_Ioi_eq`：iInf_Ioi_eq [OrderTopology R] [DenselyOrd
ered R] [NoMaxOrder R] (f : StieltjesFunction R) (x : R) : ⨅ r : Ioi x, f r = f 
x
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `Real.iInf_Ioi_eq_iInf_rat_gt`：iInf_Ioi_eq_iInf_rat_gt {f : Real -> Real}
 (x : Real) (hf : BddBelow (f '' Ioi x)) (hf_mono : Monotone f) : ⨅ r : Ioi x, f
 r = ⨅ q : { q' : …
· 使用定理 `StieltjesFunction.mono`：mono : Monotone f
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem iInf_rat_gt_eq (f : StieltjesFunction ℝ) (x : ℝ) :
    ⨅ r : { r' : ℚ // x < r' }, f r = f x := by
  rw [← iInf_Ioi_eq f x]
  refine (Real.iInf_Ioi_eq_iInf_rat_gt _ ?_ f.mono).symm
  refine ⟨f x, fun y => ?_⟩
  rintro ⟨y, hy_mem, rfl⟩
  exact f.mono (le_of_lt hy_mem)

/-- The identity of `ℝ` as a Stieltjes function, used to construct Lebesgue measure. -/
@[simps]
/-
**StieltjesFunction.id** 是 Mathlib 中的一个定义，位于命名空间 `StieltjesFunction`。
形式化陈述：StieltjesFunction ℝ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity of `ℝ` as a Stieltjes function, used to construct Lebesgue measure.
-/
protected def id : StieltjesFunction ℝ where
  toFun := id
  mono' _ _ := id
  right_continuous' _ := continuousWithinAt_id

@[simp]
/-
**StieltjesFunction.id_leftLim** 是 Mathlib 中的一个定理，位于命名空间 `StieltjesFunction`。
形式化陈述：id_leftLim (x : Real) : leftLim StieltjesFunction.id x = x
参数：x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.leftLim_eq`：ContinuousWithinAt.leftLim_eq [Topologica
lSpace α] [OrderTopology α] [T2Space β] {f : α -> β} {a : α} (hf : ContinuousWit
hinAt f (Iic a) a) …
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `continuousWithinAt_id`：continuousWithinAt_id {s : Set α} {x : α} : Conti
nuousWithinAt id s x
-/
theorem id_leftLim (x : ℝ) : leftLim StieltjesFunction.id x = x :=
  continuousWithinAt_id.leftLim_eq

variable (R) in
/-- A constant function is a Stieltjes function. -/
/-
**StieltjesFunction.const** 是 Mathlib 中的一个定义，位于命名空间 `StieltjesFunction`。
形式化陈述：(R : Type u_1) → [inst : LinearOrder R] → [inst_1 : TopologicalSpace R] → 
ℝ → StieltjesFunction R
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A constant function is a Stieltjes function.
-/
protected def const (c : ℝ) : StieltjesFunction R where
  toFun := fun _ ↦ c
  mono' _ _ := by simp
  right_continuous' _ := continuousWithinAt_const
/-
**StieltjesFunction.instInhabited** 是 Mathlib 中的一个实例，位于命名空间 `StieltjesFunction`。
形式化陈述：instInhabited : Inhabited (StieltjesFunction R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instInhabited : Inhabited (StieltjesFunction R) :=
  ⟨StieltjesFunction.const R 0⟩
/-
**StieltjesFunction.const_apply** 是 Mathlib 中的一个定理，位于命名空间 `StieltjesFunction`。
形式化陈述：∀ {R : Type u_1} [inst : LinearOrder R] [inst_1 : TopologicalSpace R] (c :
 ℝ) (x : R),   ↑(StieltjesFunction.const R c) x = c
参数：c : ℝ；x : R；StieltjesFunction.const R c。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma const_apply (c : ℝ) (x : R) : (StieltjesFunction.const R c) x = c := rfl

/-- The sum of two Stieltjes functions is a Stieltjes function. -/
/-
**StieltjesFunction.add** 是 Mathlib 中的一个定义，位于命名空间 `StieltjesFunction`。
形式化陈述：{R : Type u_1} →   [inst : LinearOrder R] →     [inst_1 : TopologicalSpace
 R] → StieltjesFunction R → StieltjesFunction R → StieltjesFunction R
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The sum of two Stieltjes functions is a Stieltjes function.
-/
protected def add (f g : StieltjesFunction R) : StieltjesFunction R where
  toFun := fun x => f x + g x
  mono' := f.mono.add g.mono
  right_continuous' := fun x => (f.right_continuous x).add (g.right_continuous x)
/-
**StieltjesFunction.** 是 Mathlib 中的一个实例，位于命名空间 `StieltjesFunction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddZeroClass (StieltjesFunction R) where
  add := StieltjesFunction.add
  zero := StieltjesFunction.const R 0
  zero_add _ := ext fun _ ↦ zero_add _
  add_zero _ := ext fun _ ↦ add_zero _
/-
**StieltjesFunction.** 是 Mathlib 中的一个实例，位于命名空间 `StieltjesFunction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddCommMonoid (StieltjesFunction R) where
  nsmul n f := nsmulRec n f
  add_assoc _ _ _ := ext fun _ ↦ add_assoc _ _ _
  add_comm _ _ := ext fun _ ↦ add_comm _ _
  __ := StieltjesFunction.instAddZeroClass
/-
**StieltjesFunction.** 是 Mathlib 中的一个实例，位于命名空间 `StieltjesFunction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Module ℝ≥0 (StieltjesFunction R) where
  smul c f := {
    toFun := fun x ↦ c * f x
    mono' := f.mono.const_mul c.2
    right_continuous' := fun x ↦ (f.right_continuous x).const_smul c.1 }
  one_smul _ := ext fun _ ↦ one_mul _
  mul_smul _ _ _ := ext fun _ ↦ mul_assoc _ _ _
  smul_zero _ := ext fun _ ↦ mul_zero _
  smul_add _ _ _ := ext fun _ ↦ mul_add _ _ _
  add_smul _ _ _ := ext fun _ ↦ add_mul _ _ _
  zero_smul _ := ext fun _ ↦ zero_mul _
/-
**StieltjesFunction.zero_apply** 是 Mathlib 中的一个定理，位于命名空间 `StieltjesFunction`。
形式化陈述：∀ {R : Type u_1} [inst : LinearOrder R] [inst_1 : TopologicalSpace R] (x :
 R), ↑0 x = 0
参数：x : R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma zero_apply (x : R) : (0 : StieltjesFunction R) x = 0 := rfl
/-
**StieltjesFunction.add_apply** 是 Mathlib 中的一个定理，位于命名空间 `StieltjesFunction`。
形式化陈述：∀ {R : Type u_1} [inst : LinearOrder R] [inst_1 : TopologicalSpace R] (f g
 : StieltjesFunction R) (x : R),   ↑(f + g) x = ↑f x + ↑g x
参数：f g : StieltjesFunction R；x : R；f + g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma add_apply (f g : StieltjesFunction R) (x : R) : (f + g) x = f x + g x := rfl

/-- If a function `f : R → ℝ` is monotone, then the function mapping `x` to the right limit of `f`
at `x` is a Stieltjes function, i.e., it is monotone and right-continuous. -/
/-
**StieltjesFunction._root_.Monotone.stieltjesFunction** 是 Mathlib 中的一个定义，位于命名空间 
`StieltjesFunction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a function `f : R → ℝ` is monotone, then the function mapping `x` to the righ
t limit of `f`
at `x` is a Stieltjes function, i.e., it is monotone and right-continuous.
-/
noncomputable def _root_.Monotone.stieltjesFunction [OrderTopology R]
    {f : R → ℝ} (hf : Monotone f) : StieltjesFunction R where
  toFun := rightLim f
  mono' _ _ hxy := hf.rightLim hxy
  right_continuous' := by
    intro x s hs
    change ∀ᶠ y in 𝓝[≥] x, rightLim f y ∈ s
    obtain ⟨l, u, hlu, lus⟩ : ∃ l u : ℝ, rightLim f x ∈ Ioo l u ∧ Ioo l u ⊆ s :=
      mem_nhds_iff_exists_Ioo_subset.1 hs
    by_cases! hx : ∀ y, y ≤ x
    · filter_upwards [self_mem_nhdsWithin] with y (hy : x ≤ y)
      rw [show y = x by exact le_antisymm (hx y) hy]
      exact lus hlu
    rcases hx with ⟨y₀, hy₀⟩
    obtain ⟨y, xy, h'y⟩ : ∃ (y : R), x < y ∧ Ioo x y ⊆ f ⁻¹' Ioo l u :=
      (mem_nhdsGT_iff_exists_Ioo_subset' hy₀).1 (hf.tendsto_rightLim x (Ioo_mem_nhds hlu.1 hlu.2))
    filter_upwards [Ico_mem_nhdsGE xy] with z hz
    apply lus
    refine ⟨hlu.1.trans_le (hf.rightLim hz.1), ?_⟩
    rcases hz.1.eq_or_lt with rfl | h''z
    · exact hlu.2
    rcases Filter.eq_or_neBot (𝓝[>] z) with h'z | h'z
    · rw [rightLim_eq_of_eq_bot _ h'z]
      have : z ∈ Ioo x y := ⟨h''z, hz.2⟩
      exact (h'y this).2
    · obtain ⟨a, za, ay⟩ : ∃ a : R, z < a ∧ a < y := Filter.nonempty_of_mem (Ioo_mem_nhdsGT hz.2)
      calc
        rightLim f z ≤ f a := hf.rightLim_le za
        _ < u := (h'y ⟨hz.1.trans_lt za, ay⟩).2
/-
**StieltjesFunction._root_.Monotone.stieltjesFunction_eq** 是 Mathlib 中的一个定理，位于命名
空间 `StieltjesFunction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Monotone.stieltjesFunction_eq
    [OrderTopology R] {f : R → ℝ} (hf : Monotone f) (x : R) :
    hf.stieltjesFunction x = rightLim f x :=
  rfl
/-
**StieltjesFunction.countable_leftLim_ne** 是 Mathlib 中的一个定理，位于命名空间 `StieltjesFun
ction`。
形式化陈述：countable_leftLim_ne [OrderTopology R] (f : StieltjesFunction R) : Set.Cou
ntable {x | leftLim f x != f x}
参数：f : StieltjesFunction R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Countable.mono`：∀ {α : Type u} {s₁ s₂ : Set α}, s₁ ⊆ s₂ → s₂.Countab
le → s₁.Countable
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Monotone.continuousWithinAt_Iio_iff_leftLim_eq`：continuousWithinAt_Iio_i
ff_leftLim_eq : ContinuousWithinAt f (Iio x) x ↔ leftLim f x = f x
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `StieltjesFunction.mono`：mono : Monotone f
· 使用定理 `ContinuousAt.continuousWithinAt`：ContinuousAt.continuousWithinAt (h : Co
ntinuousAt f x) : ContinuousWithinAt f s x
· 使用定理 `Monotone.countable_not_continuousAt`：Monotone.countable_not_continuousAt
 (hf : Monotone f) : Set.Countable {x | ¬ContinuousAt f x}
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
-/
theorem countable_leftLim_ne [OrderTopology R] (f : StieltjesFunction R) :
    Set.Countable {x | leftLim f x ≠ f x} := by
  refine Countable.mono ?_ f.mono.countable_not_continuousAt
  intro x hx h'x
  apply hx
  exact (Monotone.continuousWithinAt_Iio_iff_leftLim_eq f.mono).1 h'x.continuousWithinAt

/-! ### The outer measure associated to a Stieltjes function -/


open scoped Classical in
/-- Length of an interval. This is the largest monotone function which correctly measures all
intervals. -/
/-
**StieltjesFunction.length** 是 Mathlib 中的一个定义，位于命名空间 `StieltjesFunction`。
形式化陈述：length (s : Set R) : Real>=0∞
参数：s : Set R。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Length of an interval. This is the largest monotone function which correctly mea
sures all
intervals.
-/
def length (s : Set R) : ℝ≥0∞ :=
  -- we treat separately the empty case, where the formula below would give `∞`.
  if IsEmpty R then 0
  -- if there is a bot element `x`, it does not belong to any interval `Ioc a b`. So we remove it
  -- when measuring the size of a set (the set `{x}` will have measure `0` in our construction).
  else ⨅ (a) (b) (_ : s \ botSet ⊆ Ioc a b), ofReal (f b - f a)
/-
**StieltjesFunction.length_eq** 是 Mathlib 中的一个引理，位于命名空间 `StieltjesFunction`。
形式化陈述：length_eq [Nonempty R] (s : Set R) : f.length s = ⨅ (a) (b) (_ : s \ botSe
t subseteq Ioc a b), ofReal (f b - f a)
参数：s : Set R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma length_eq [Nonempty R] (s : Set R) :
    f.length s = ⨅ (a) (b) (_ : s \ botSet ⊆ Ioc a b), ofReal (f b - f a) := by
  simp [length]
/-
**StieltjesFunction.length_eq_of_isEmpty** 是 Mathlib 中的一个引理，位于命名空间 `StieltjesFun
ction`。
形式化陈述：length_eq_of_isEmpty [IsEmpty R] (s : Set R) : f.length s = 0
参数：s : Set R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma length_eq_of_isEmpty [IsEmpty R] (s : Set R) : f.length s = 0 := by
  simp only [length, if_pos]

@[simp]
/-
**StieltjesFunction.length_empty** 是 Mathlib 中的一个定理，位于命名空间 `StieltjesFunction`。
形式化陈述：length_empty : f.length ∅ = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `StieltjesFunction.length_eq_of_isEmpty`：length_eq_of_isEmpty [IsEmpty R]
 (s : Set R) : f.length s = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `StieltjesFunction.length_eq`：length_eq [Nonempty R] (s : Set R) : f.leng
th s = ⨅ (a) (b) (_ : s \ botSet subseteq Ioc a b), ofReal (f b - f a)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `nonpos_iff_eq_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [in
st_1 : Zero α] [IsBotZeroClass α], a ≤ 0 ↔ a = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `iInf_le_of_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α
] {f : ι → α} {a : α} (i : ι), f i ≤ a → iInf f ≤ a
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.empty_sdiff`：empty_sdiff (s : Set α) : (∅ \ s : Set α) = ∅
· 使用定理 `Set.Ioc_eq_empty`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, ¬b < a
 → Set.Ioc b a = ∅
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `ENNReal.ofReal_zero`：ENNReal.ofReal 0 = 0
· 使用定理 `iInf_pos`：∀ {α : Type u_1} [inst : CompleteLattice α] {p : Prop} {f : p 
→ α} (hp : p), ⨅ (h : p), f h = f hp
-/
theorem length_empty : f.length ∅ = 0 := by
  rcases isEmpty_or_nonempty R with hR | hR
  · simp [length_eq_of_isEmpty]
  inhabit R
  rw [length_eq]
  exact nonpos_iff_eq_zero.1 <| iInf_le_of_le default <| iInf_le_of_le default <| by simp

@[simp]
/-
**StieltjesFunction.length_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `StieltjesFunction`。
形式化陈述：length_Ioc (a b : R) : f.length (Ioc a b) = ofReal (f b - f a)
参数：a b : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `StieltjesFunction.length_eq`：length_eq [Nonempty R] (s : Set R) : f.leng
th s = ⨅ (a) (b) (_ : s \ botSet subseteq Ioc a b), ofReal (f b - f a)
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `iInf_le_of_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α
] {f : ι → α} {a : α} (i : ι), f i ≤ a → iInf f ≤ a
· 使用定理 `iInf₂_le`：∀ {α : Type u_1} {ι : Sort u_4} {κ : ι → Sort u_6} [inst : Com
pleteLattice α] {f : (i : ι) → κ i → α} (i : ι) (j : κ i),   ⨅ i, ⨅ j, f i j ≤…
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
· 使用定理 `le_iInf`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] {f :
 ι → α} {a : α}, (∀ (i : ι), a ≤ f i) → a ≤ iInf f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.coe_le_coe`：∀ {r q : NNReal}, ↑r ≤ ↑q ↔ r ≤ q
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `Real.toNNReal_of_nonpos`：toNNReal_of_nonpos {r : Real} : r <= 0 -> Real.
toNNReal r = 0
· 使用定理 `sub_nonpos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddRight
Mono α] {a b : α}, a - b ≤ 0 ↔ a ≤ b
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `StieltjesFunction.mono`：mono : Monotone f
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.Ioc_subset_Ioc_iff`：Ioc_subset_Ioc_iff (h₁ : a₁ < b₁) : Ioc a₁ b₁ su
bseteq Ioc a₂ b₂ ↔ b₁ <= b₂ ∧ a₂ <= a₁
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Ioc_sdiff_botSet`：∀ {R : Type u_1} [inst : LinearOrder R] (a b : R), Set
.Ioc a b \ botSet = Set.Ioc a b
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `Real.toNNReal_mono`：∀ {r₁ r₂ : ℝ}, r₁ ≤ r₂ → r₁.toNNReal ≤ r₂.toNNReal
· 使用定理 `sub_le_sub_right`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [Ad
dRightMono α] {a b : α}, a ≤ b → ∀ (c : α), a - c ≤ b - c
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `sub_le_sub_left`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [Add
LeftMono α] [AddRightMono α] {a b : α},   a ≤ b → ∀ (c : α), c - b ≤ c - a
-/
theorem length_Ioc (a b : R) : f.length (Ioc a b) = ofReal (f b - f a) := by
  have : Nonempty R := ⟨a⟩
  rw [length_eq]
  refine
    le_antisymm (iInf_le_of_le a <| iInf₂_le b sdiff_subset)
      (le_iInf fun a' => le_iInf fun b' => le_iInf fun h => ENNReal.coe_le_coe.2 ?_)
  rcases le_or_gt b a with ab | ab
  · rw [Real.toNNReal_of_nonpos (sub_nonpos.2 (f.mono ab))]
    apply zero_le
  simp only [Ioc_sdiff_botSet] at h
  obtain ⟨h₁, h₂⟩ := (Ioc_subset_Ioc_iff ab).1 h
  grw [h₁, h₂]

@[gcongr]
/-
**StieltjesFunction.length_mono** 是 Mathlib 中的一个定理，位于命名空间 `StieltjesFunction`。
形式化陈述：length_mono {s₁ s₂ : Set R} (h : s₁ subseteq s₂) : f.length s₁ <= f.length
 s₂
参数：h : s₁ subseteq s₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `StieltjesFunction.length_eq_of_isEmpty`：length_eq_of_isEmpty [IsEmpty R]
 (s : Set R) : f.length s = 0
· 使用引理 `StieltjesFunction.length_eq`：length_eq [Nonempty R] (s : Set R) : f.leng
th s = ⨅ (a) (b) (_ : s \ botSet subseteq Ioc a b), ofReal (f b - f a)
· 使用定理 `iInf_mono`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] {f
 g : ι → α}, (∀ (i : ι), g i ≤ f i) → iInf g ≤ iInf f
· 使用定理 `biInf_mono`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] {
f : ι → α} {p q : ι → Prop},   (∀ (i : ι), p i → q i) → ⨅ i, ⨅ (_ : q i), f i ≤ 
…
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `sdiff_le_sdiff`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] 
{a b c d : α}, d ≤ c → b ≤ a → d \ a ≤ c \ b
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem length_mono {s₁ s₂ : Set R} (h : s₁ ⊆ s₂) : f.length s₁ ≤ f.length s₂ := by
  rcases isEmpty_or_nonempty R with hR | hR
  · simp [length_eq_of_isEmpty]
  simp only [length_eq]
  exact iInf_mono fun a => biInf_mono fun b => by gcongr
/-
**StieltjesFunction.length_sdiff_botSet** 是 Mathlib 中的一个定理，位于命名空间 `StieltjesFunc
tion`。
形式化陈述：length_sdiff_botSet {s : Set R} : f.length (s \ botSet) = f.length s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `StieltjesFunction.length_eq_of_isEmpty`：length_eq_of_isEmpty [IsEmpty R]
 (s : Set R) : f.length s = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `StieltjesFunction.length_eq`：length_eq [Nonempty R] (s : Set R) : f.leng
th s = ⨅ (a) (b) (_ : s \ botSet subseteq Ioc a b), ofReal (f b - f a)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sdiff_idem`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] {a b
 : α}, (a \ b) \ b = a \ b
-/
theorem length_sdiff_botSet {s : Set R} : f.length (s \ botSet) = f.length s := by
  rcases isEmpty_or_nonempty R with hR | hR
  · simp [length_eq_of_isEmpty]
  · simp [length_eq]

@[deprecated (since := "2026-06-03")] alias length_diff_botSet := length_sdiff_botSet

open MeasureTheory

/-- The Stieltjes outer measure associated to a Stieltjes function. -/
/-
**StieltjesFunction.outer** 是 Mathlib 中的一个定义，位于命名空间 `StieltjesFunction`。
形式化陈述：{R : Type u_1} →   [inst : LinearOrder R] → [inst_1 : TopologicalSpace R] 
→ StieltjesFunction R → MeasureTheory.OuterMeasure R
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `StieltjesFunction.length_empty`：length_empty : f.length ∅ = 0

--- 原说明 ---
The Stieltjes outer measure associated to a Stieltjes function.
-/
protected def outer : OuterMeasure R :=
  OuterMeasure.ofFunction f.length f.length_empty
/-
**StieltjesFunction.outer_le_length** 是 Mathlib 中的一个定理，位于命名空间 `StieltjesFunction
`。
形式化陈述：outer_le_length (s : Set R) : f.outer s <= f.length s
参数：s : Set R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.OuterMeasure.ofFunction_le`：ofFunction_le (s : Set α) : Ou
terMeasure.ofFunction m m_empty s <= m s
· 使用定理 `StieltjesFunction.length_empty`：length_empty : f.length ∅ = 0
-/
theorem outer_le_length (s : Set R) : f.outer s ≤ f.length s :=
  OuterMeasure.ofFunction_le _

variable [OrderTopology R] [CompactIccSpace R]

/-- If a compact interval `[a, b]` is covered by a union of open interval `(c i, d i)`, then
`f b - f a ≤ ∑ f (d i) - f (c i)`. This is an auxiliary technical statement to prove the same
statement for half-open intervals, the point of the current statement being that one can use
compactness to reduce it to a finite sum, and argue by induction on the size of the covering set.

To be able to handle also the top element if there is one, we use `Iotop` instead of `Ioo` in the
statement. As these intervals are all open, this does not change the proof. -/
/-
**StieltjesFunction.length_subadditive_Icc_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Stielt
jesFunction`。
形式化陈述：length_subadditive_Icc_Ioo {a b : R} {c d : Nat -> R} (ss : Icc a b subset
eq ⋃ i, Iotop (c i) (d i)) : ofReal (f b - f a) <= ∑' i, ofReal (f (d i) - f (c 
i))
参数：ss : Icc a b subseteq ⋃ i, Iotop (c i) (d i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.ofReal_eq_zero`：ofReal_eq_zero {p : Real} : ENNReal.ofReal p = 0
 ↔ p <= 0
· 使用定理 `sub_nonpos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddRight
Mono α] {a b : α}, a - b ≤ 0 ↔ a ≤ b
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `StieltjesFunction.mono`：mono : Monotone f
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.insert_erase`：∀ {α : Type u_1} [inst : DecidableEq α] {s : Finset
 α} {a : α}, a ∈ s → insert a (s.erase a) = s
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `Finset.notMem_erase`：notMem_erase (a : α) (s : Finset α) : a ∉ erase s a
· 使用引理 `Iotop_subset_Ioc`：Iotop_subset_Ioc {a b : R} : Iotop a b subseteq Ioc a 
b
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `Finset.erase_ssubset`：erase_ssubset {a : α} {s : Finset α} (h : a in s) 
: s.erase a ⊂ s
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Set.biUnion_insert`：biUnion_insert (a : α) (s : Set α) (t : α -> Set β) 
: ⋃ x in insert a s, t x = t a union ⋃ x in s, t x
· 使用定理 `Finset.coe_insert`：coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (
insert a s : Set α)
（共 49 条，此处仅展示前 30 条）

--- 原说明 ---
If a compact interval `[a, b]` is covered by a union of open interval `(c i, d i
)`, then
`f b - f a ≤ ∑ f (d i) - f (c i)`. This is an auxiliary technical statement to p
rove the same
statement for half-open intervals, the point of the current statement being that
 one can use
compactness to reduce it to a finite sum, and argue by induction on the size of 
the covering set.

To be able to handle also the top element if there is one, we use `Iotop` instea
d of `Ioo` in the
statement. As these intervals are all open, this does not change the proof.
-/
theorem length_subadditive_Icc_Ioo {a b : R} {c d : ℕ → R} (ss : Icc a b ⊆ ⋃ i, Iotop (c i) (d i)) :
    ofReal (f b - f a) ≤ ∑' i, ofReal (f (d i) - f (c i)) := by
  suffices
    ∀ (s : Finset ℕ) (b), Icc a b ⊆ (⋃ i ∈ (s : Set ℕ), Iotop (c i) (d i)) →
      (ofReal (f b - f a) : ℝ≥0∞) ≤ ∑ i ∈ s, ofReal (f (d i) - f (c i)) by
    rcases isCompact_Icc.elim_finite_subcover_image
        (fun (i : ℕ) (_ : i ∈ univ) => @isOpen_Iotop _ _ _ _ (c i) (d i)) (by simpa using ss) with
      ⟨s, _, hf, hs⟩
    have e : ⋃ i ∈ (hf.toFinset : Set ℕ), Iotop (c i) (d i) = ⋃ i ∈ s, Iotop (c i) (d i) := by
      simp only [Finset.set_biUnion_coe,
        Finite.mem_toFinset]
    rw [ENNReal.tsum_eq_iSup_sum]
    refine le_trans ?_ (le_iSup _ hf.toFinset)
    exact this hf.toFinset _ (by simpa only [e])
  clear ss b
  refine fun s => Finset.strongInductionOn s fun s IH b cv => ?_
  rcases le_total b a with ab | ab
  · rw [ENNReal.ofReal_eq_zero.2 (sub_nonpos.2 (f.mono ab))]
    exact zero_le
  obtain ⟨i, is, bcd⟩ : ∃ i ∈ s, b ∈ Iotop (c i) (d i) := by
    simpa only [SetLike.mem_coe, mem_iUnion, exists_prop] using cv ⟨ab, le_rfl⟩
  rw [← Finset.insert_erase is] at cv ⊢
  rw [Finset.coe_insert, biUnion_insert] at cv
  rw [Finset.sum_insert (Finset.notMem_erase _ _)]
  replace bcd : b ∈ Ioc (c i) (d i) := Iotop_subset_Ioc bcd
  grw [← IH _ (Finset.erase_ssubset is) (c i), ← ENNReal.ofReal_add_le]
  · rw [sub_add_sub_cancel]
    grw [bcd.2]
  · rintro x ⟨h₁, h₂⟩
    apply (cv ⟨h₁, le_trans h₂ (le_of_lt bcd.1)⟩).resolve_left (fun h ↦ ?_)
    order [(Iotop_subset_Ioc h).1]

@[simp]
/-
**StieltjesFunction.outer_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `StieltjesFunction`。
形式化陈述：outer_Ioc [DenselyOrdered R] (a b : R) : f.outer (Ioc a b) = ofReal (f b -
 f a)
参数：a b : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `StieltjesFunction.length_Ioc`：length_Ioc (a b : R) : f.length (Ioc a b) 
= ofReal (f b - f a)
· 使用定理 `StieltjesFunction.outer_le_length`：outer_le_length (s : Set R) : f.outer
 s <= f.length s
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AddGroup.toOrderedSub`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LE
 α] [AddRightMono α], OrderedSub α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `StieltjesFunction.mono`：mono : Monotone f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `le_iInf₂`：∀ {α : Type u_1} {ι : Sort u_4} {κ : ι → Sort u_6} [inst : Com
pleteLattice α] {a : α} {f : (i : ι) → κ i → α},   (∀ (i : ι) (j : κ i), a ≤ f…
· 使用定理 `ENNReal.le_of_forall_pos_le_add`：le_of_forall_pos_le_add (h : forall ε :
 Real>=0, 0 < ε -> b < ∞ -> a <= b + ε) : a <= b
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `ENNReal.coe_div`：coe_div (hr : r != 0) : (↑(p / r) : Real>=0∞) = p / r
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `ENNReal.exists_pos_sum_of_countable`：exists_pos_sum_of_countable {ε : Re
al>=0∞} (hε : ε != 0) (ι) [Countable ι] : exists ε' : ι -> Real>=0, (forall i, 0
 < ε' i) ∧ (∑' i, (ε' i :…
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `ContinuousWithinAt.sub`：∀ {G : Type u_1} {X : Type u_3} [inst : Topologi
calSpace X] [inst_1 : TopologicalSpace G] [inst_2 : Sub G]   [ContinuousSub G] {
f g : X → G}…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
（共 88 条，此处仅展示前 30 条）
-/
theorem outer_Ioc [DenselyOrdered R] (a b : R) : f.outer (Ioc a b) = ofReal (f b - f a) := by
  /- It suffices to show that, if `(a, b]` is covered by sets `s i`, then `f b - f a` is bounded
    by `∑ f.length (s i) + ε`. The difficulty is that `f.length` is expressed in terms of half-open
    intervals, while we would like to have a compact interval covered by open intervals to use
    compactness and finite sums, as provided by `length_subadditive_Icc_Ioo`. The trick is to use
    the right-continuity of `f`. If `a'` is close enough to `a` on its right, then `[a', b]` is
    still covered by the sets `s i` and moreover `f b - f a'` is very close to `f b - f a`
    (up to `ε/2`).
    Also, by definition one can cover `s i` by a half-closed interval `(p i, q i]` with `f`-length
    very close to that of `s i` (within a suitably small `ε' i`, say). If one moves `q i` very
    slightly to the right, then the `f`-length will change very little by right continuity, and we
    will get an open interval `(p i, q' i)` covering `s i` with `f (q' i) - f (p i)` within `ε' i`
    of the `f`-length of `s i`. This is not possible if `q i` is top, but this is not an issue
    as the interval `(p i, q i]` is already open in this case. However, this means that we can
    not use `Ioo` in this proof -- instead, we use `Iotop` precisely to avoid this issue. -/
  refine le_antisymm ?_ ?_
  · rw [← f.length_Ioc]
    apply outer_le_length
  rcases le_or_gt b a with hab | hab
  · have : ofReal (f b - f a) = 0 := by simpa using f.mono hab
    simp [this]
  apply (le_iInf₂ fun s hs => ENNReal.le_of_forall_pos_le_add fun ε εpos h => ?_)
  let δ := ε / 2
  have δpos : 0 < (δ : ℝ≥0∞) := by simpa [δ] using εpos.ne'
  rcases ENNReal.exists_pos_sum_of_countable δpos.ne' ℕ with ⟨ε', ε'0, hε⟩
  obtain ⟨a', ha', aa'⟩ : ∃ a', f a' - f a < δ ∧ a < a' := by
    have A : ContinuousWithinAt (fun r => f r - f a) (Ioi a) a := by
      refine ContinuousWithinAt.sub ?_ continuousWithinAt_const
      exact (f.right_continuous a).mono Ioi_subset_Ici_self
    have B : f a - f a < δ := by rwa [sub_self, NNReal.coe_pos, ← ENNReal.coe_pos]
    have : (𝓝[>] a).NeBot := nhdsGT_neBot_of_exists_gt ⟨b, hab⟩
    exact (((tendsto_order.1 A).2 _ B).and self_mem_nhdsWithin).exists
  have : Nonempty R := ⟨a⟩
  have : ∀ i, ∃ p : R × R, Icc a' b ∩ s i ⊆ Iotop p.1 p.2 ∧
      (ofReal (f p.2 - f p.1) : ℝ≥0∞) < f.length (s i) + ε' i := by
    intro i
    have hl :=
      ENNReal.lt_add_right ((ENNReal.le_tsum i).trans_lt h).ne (ENNReal.coe_ne_zero.2 (ε'0 i).ne')
    conv at hl =>
      lhs
      rw [length_eq]
    simp only [iInf_lt_iff, exists_prop] at hl
    rcases hl with ⟨p, q', spq, hq'⟩
    have A : Icc a' b ∩ s i ⊆ Ioc p q' := by
      rintro x ⟨hx, h'x⟩
      apply spq
      simp [h'x, notMem_botSet_of_lt (aa'.trans_le hx.1)]
    by_cases htq' : IsTop q'
    · refine ⟨(p, q'), ?_, hq'⟩
      rintro x hx
      simp only [Iotop, htq', ↓reduceIte, mem_Ioc]
      exact ⟨(A hx).1, htq' _⟩
    have : (𝓝[>] q').NeBot := by simp [Filter.neBot_iff, nhdsGT_eq_bot_iff, htq', not_covBy]
    have : ContinuousWithinAt (fun r => ofReal (f r - f p)) (Ioi q') q' := by
      apply ENNReal.continuous_ofReal.continuousAt.comp_continuousWithinAt
      refine ContinuousWithinAt.sub ?_ continuousWithinAt_const
      exact (f.right_continuous q').mono Ioi_subset_Ici_self
    rcases (((tendsto_order.1 this).2 _ hq').and self_mem_nhdsWithin).exists with ⟨q, hq, q'q⟩
    exact ⟨⟨p, q⟩, A.trans ((Ioc_subset_Ioo_right q'q).trans Ioo_subset_Iotop), hq⟩
  choose g hg using this
  have I_subset : Icc a' b ⊆ ⋃ i, Iotop (g i).1 (g i).2 :=
    calc
      Icc a' b ⊆ Icc a' b ∩ Ioc a b := fun x hx => ⟨hx, aa'.trans_le hx.1, hx.2⟩
      _ ⊆ Icc a' b ∩ ⋃ i, s i := by gcongr
      _ = ⋃ i, Icc a' b ∩ s i := inter_iUnion (Icc a' b) s
      _ ⊆ ⋃ i, Iotop (g i).1 (g i).2 := iUnion_mono fun i => (hg i).1
  calc
    ofReal (f b - f a) = ofReal (f b - f a' + (f a' - f a)) := by rw [sub_add_sub_cancel]
    _ ≤ ofReal (f b - f a') + ofReal (f a' - f a) := ENNReal.ofReal_add_le
    _ ≤ ∑' i, ofReal (f (g i).2 - f (g i).1) + ofReal δ :=
      (add_le_add (f.length_subadditive_Icc_Ioo I_subset) (ENNReal.ofReal_le_ofReal ha'.le))
    _ ≤ ∑' i, (f.length (s i) + ε' i) + δ :=
      (add_le_add (ENNReal.tsum_le_tsum fun i => (hg i).2.le)
        (by simp only [ENNReal.ofReal_coe_nnreal, le_rfl]))
    _ = ∑' i, f.length (s i) + ∑' i, (ε' i : ℝ≥0∞) + δ := by rw [ENNReal.tsum_add]
    _ ≤ ∑' i, f.length (s i) + δ + δ := add_le_add (add_le_add le_rfl hε.le) le_rfl
    _ = ∑' i : ℕ, f.length (s i) + ε := by simp [δ, add_assoc, ENNReal.add_halves]

omit [OrderTopology R] [CompactIccSpace R] in
/-
**StieltjesFunction.measurableSet_Ioi** 是 Mathlib 中的一个定理，位于命名空间 `StieltjesFuncti
on`。
形式化陈述：measurableSet_Ioi {c : R} : MeasurableSet[f.outer.caratheodory] (Ioi c)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.OuterMeasure.ofFunction_caratheodory`：ofFunction_caratheod
ory {m : Set α -> Real>=0∞} {s : Set α} {h₀ : m ∅ = 0} (hs : forall t, m (t inte
r s) + m (t \ s) <= m t) : MeasurableSet…
· 使用定理 `StieltjesFunction.length_empty`：length_empty : f.length ∅ = 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `StieltjesFunction.length_eq`：length_eq [Nonempty R] (s : Set R) : f.leng
th s = ⨅ (a) (b) (_ : s \ botSet subseteq Ioc a b), ofReal (f b - f a)
· 使用定理 `le_iInf`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] {f :
 ι → α} {a : α}, (∀ (i : ι), a ≤ f i) → a ≤ iInf f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `StieltjesFunction.length_sdiff_botSet`：length_sdiff_botSet {s : Set R} :
 f.length (s \ botSet) = f.length s
· 使用定理 `Set.inter_sdiff_right_comm`：inter_sdiff_right_comm : (s inter t) \ u = s
 \ u inter t
· 使用定理 `Set.sdiff_sdiff_comm`：sdiff_sdiff_comm {s t u : Set α} : (s \ t) \ u = (
s \ u) \ t
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `StieltjesFunction.length_mono`：length_mono {s₁ s₂ : Set R} (h : s₁ subse
teq s₂) : f.length s₁ <= f.length s₂
· 使用定理 `Set.inter_subset_inter`：inter_subset_inter {s₁ s₂ t₁ t₂ : Set α} (h₁ : s
₁ subseteq t₁) (h₂ : s₂ subseteq t₂) : s₁ inter s₂ subseteq t₁ inter t₂
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `sdiff_le_sdiff`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] 
{a b c d : α}, d ≤ c → b ≤ a → d \ a ≤ c \ b
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.Ioc_inter_Ioi`：Ioc_inter_Ioi : Ioc a b inter Ioi c = Ioc (a ⊔ c) b
· 使用定理 `max_eq_right`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a ≤ b →
 max a b = b
· 使用定理 `Set.Ioc_eq_empty`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, ¬b < a
 → Set.Ioc b a = ∅
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Set.Ioc_sdiff_Ioi`：Ioc_sdiff_Ioi : Ioc a b \ Ioi c = Ioc a (min b c)
· 使用引理 `min_eq_left`：min_eq_left (h : a <= b) : min a b = a
· 使用定理 `StieltjesFunction.length_Ioc`：length_Ioc (a b : R) : f.length (Ioc a b) 
= ofReal (f b - f a)
（共 37 条，此处仅展示前 30 条）
-/
theorem measurableSet_Ioi {c : R} : MeasurableSet[f.outer.caratheodory] (Ioi c) := by
  refine OuterMeasure.ofFunction_caratheodory fun t => ?_
  have : Nonempty R := ⟨c⟩
  simp only [length_eq]
  refine le_iInf fun a => le_iInf fun b => le_iInf fun h => ?_
  simp only [← length_eq]
  rw [← length_sdiff_botSet, inter_sdiff_right_comm, ← length_sdiff_botSet (s := t \ Ioi c),
    sdiff_sdiff_comm]
  grw [h]
  rcases le_total a c with hac | hac <;> rcases le_total b c with hbc | hbc
  · simp only [Ioc_inter_Ioi, f.length_Ioc, hac, hbc, le_refl, Ioc_eq_empty,
      max_eq_right, min_eq_left, Ioc_sdiff_Ioi, f.length_empty, zero_add, not_lt]
  · simp only [hac, hbc, Ioc_inter_Ioi, Ioc_sdiff_Ioi, f.length_Ioc, min_eq_right,
      ← ENNReal.ofReal_add, f.mono hac, f.mono hbc, sub_nonneg,
      sub_add_sub_cancel, le_refl,
      max_eq_right]
  · simp only [hbc, le_refl, Ioc_eq_empty, Ioc_inter_Ioi, min_eq_left, Ioc_sdiff_Ioi,
      f.length_empty, zero_add, or_true, le_sup_iff, f.length_Ioc, not_lt]
  · simp only [hac, hbc, Ioc_inter_Ioi, Ioc_sdiff_Ioi, f.length_Ioc, min_eq_right,
      le_refl, Ioc_eq_empty, add_zero, max_eq_left, f.length_empty, not_lt]
/-
**StieltjesFunction.outer_trim** 是 Mathlib 中的一个定理，位于命名空间 `StieltjesFunction`。
形式化陈述：outer_trim [MeasurableSpace R] [BorelSpace R] [DenselyOrdered R] : f.outer
.trim = f.outer
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.OuterMeasure.trim_eq_iInf`：trim_eq_iInf (s : Set α) : m.tr
im s = ⨅ (t) (_ : s subseteq t) (_ : MeasurableSet t), m t
· 使用定理 `le_iInf`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] {f :
 ι → α} {a : α}, (∀ (i : ι), a ≤ f i) → a ≤ iInf f
· 使用定理 `ENNReal.le_of_forall_pos_le_add`：le_of_forall_pos_le_add (h : forall ε :
 Real>=0, 0 < ε -> b < ∞ -> a <= b + ε) : a <= b
· 使用定理 `ENNReal.exists_pos_sum_of_countable`：exists_pos_sum_of_countable {ε : Re
al>=0∞} (hε : ε != 0) (ι) [Countable ι] : exists ε' : ι -> Real>=0, (forall i, 0
 < ε' i) ∧ (∑' i, (ε' i :…
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.coe_pos`：∀ {r : NNReal}, 0 < ↑r ↔ 0 < r
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.tsum_add`：∀ {α : Type u_1} {f g : α → ENNReal}, ∑' (a : α), (f a
 + g a) = ∑' (a : α), f a + ∑' (a : α), g a
· 使用定理 `iInf_le_of_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α
] {f : ι → α} {a : α} (i : ι), f i ≤ a → iInf f ≤ a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.iUnion_mono`：iUnion_mono {s t : ι -> Set α} (h : forall i, s i subse
teq t i) : ⋃ i, s i subseteq ⋃ i, t i
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `ENNReal.ofReal_coe_nnreal`：∀ {p : NNReal}, ENNReal.ofReal ↑p = ↑p
· 使用定理 `MeasurableSet.iUnion`：∀ {α : Type u_1} {ι : Sort u_6} {m : MeasurableSpa
ce α} [Countable ι] ⦃f : ι → Set α⦄,   (∀ (b : ι), MeasurableSet (f b)) → Measur
ableSet (⋃…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `MeasureTheory.measure_iUnion_le`：measure_iUnion_le [Countable ι] (s : ι 
-> Set α) : μ (⋃ i, s i) <= ∑' i, μ (s i)
· 使用定理 `MeasureTheory.OuterMeasure.instOuterMeasureClass`：∀ {α : Type u_1}, Meas
ureTheory.OuterMeasureClass (MeasureTheory.OuterMeasure α) α
（共 67 条，此处仅展示前 30 条）
-/
theorem outer_trim [MeasurableSpace R] [BorelSpace R] [DenselyOrdered R] :
    f.outer.trim = f.outer := by
  refine le_antisymm (fun s => ?_) (OuterMeasure.le_trim _)
  rw [OuterMeasure.trim_eq_iInf]
  refine le_iInf fun t => le_iInf fun ht => ENNReal.le_of_forall_pos_le_add fun ε ε0 h => ?_
  rcases ENNReal.exists_pos_sum_of_countable (ENNReal.coe_pos.2 ε0).ne' ℕ with ⟨ε', ε'0, hε⟩
  grw [← hε]
  rw [← ENNReal.tsum_add]
  choose g hg using
    show ∀ i, ∃ s, t i ⊆ s ∧ MeasurableSet s ∧ f.outer s ≤ f.length (t i) + ofReal (ε' i) by
      intro i
      rcases isEmpty_or_nonempty R with hR | hR
      · exact ⟨∅, by simp, MeasurableSet.empty, by simp⟩
      have hl :=
        ENNReal.lt_add_right ((ENNReal.le_tsum i).trans_lt h).ne (ENNReal.coe_pos.2 (ε'0 i)).ne'
      conv at hl =>
        lhs
        rw [length_eq]
      simp only [iInf_lt_iff] at hl
      rcases hl with ⟨a, b, h₁, h₂⟩
      rw [← f.outer_Ioc] at h₂
      rw [sdiff_subset_iff] at h₁
      refine ⟨_, h₁, measurableSet_botSet.union measurableSet_Ioc, le_of_lt ?_⟩
      calc f.outer (botSet ∪ Ioc a b)
      _ ≤ f.outer botSet + f.outer (Ioc a b) := measure_union_le _ _
      _ ≤ f.length botSet + f.outer (Ioc a b) := by gcongr; apply outer_le_length
      _ = 0 + f.outer (Ioc a b) := by
        simp only [← length_sdiff_botSet, sdiff_self, empty_sdiff, outer_Ioc, zero_add]
        simp [empty_sdiff]
      _ = f.outer (Ioc a b) := by simp
      _ < f.length (t i) + ofReal ↑(ε' i) := by simpa using h₂
  simp only [ofReal_coe_nnreal] at hg
  apply iInf_le_of_le (iUnion g) _
  apply iInf_le_of_le (ht.trans <| iUnion_mono fun i => (hg i).1) _
  apply iInf_le_of_le (MeasurableSet.iUnion fun i => (hg i).2.1) _
  exact le_trans (measure_iUnion_le _) (ENNReal.tsum_le_tsum fun i => (hg i).2.2)

omit [CompactIccSpace R] in
/-
**StieltjesFunction.borel_le_measurable** 是 Mathlib 中的一个定理，位于命名空间 `StieltjesFunc
tion`。
形式化陈述：borel_le_measurable [SecondCountableTopology R] : borel R <= f.outer.carat
heodory
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `borel_eq_generateFrom_Ioi`：borel_eq_generateFrom_Ioi : borel α = .genera
teFrom (range Ioi)
· 使用定理 `MeasurableSpace.generateFrom_le`：generateFrom_le {s : Set (Set α)} {m : 
MeasurableSpace α} (h : forall t in s, MeasurableSet[m] t) : generateFrom s <= m
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `StieltjesFunction.measurableSet_Ioi`：measurableSet_Ioi {c : R} : Measura
bleSet[f.outer.caratheodory] (Ioi c)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem borel_le_measurable [SecondCountableTopology R] :
    borel R ≤ f.outer.caratheodory := by
  rw [borel_eq_generateFrom_Ioi]
  refine MeasurableSpace.generateFrom_le ?_
  simp +contextual [f.measurableSet_Ioi]

/-! ### The measure associated to a Stieltjes function -/

variable [MeasurableSpace R] [BorelSpace R] [SecondCountableTopology R] [DenselyOrdered R]

/-- The measure associated to a Stieltjes function, giving mass `f b - f a` to the
interval `(a, b]`. If there is a bot element, it gives zero mass to it. -/
protected irreducible_def measure : Measure R where
  toOuterMeasure := f.outer
  m_iUnion _s hs := f.outer.iUnion_eq_of_caratheodory fun i => f.borel_le_measurable _ <| by
    borelize R
    exact hs i
  trim_le := f.outer_trim.le

@[simp]
/-
**StieltjesFunction.measure_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `StieltjesFunction`。
形式化陈述：measure_Ioc (a b : R) : f.measure (Ioc a b) = ofReal (f b - f a)
参数：a b : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `StieltjesFunction.measure_def`：∀ {R : Type u_2} [inst : LinearOrder R] [
inst_1 : TopologicalSpace R] (f : StieltjesFunction R)   [inst_2 : OrderTopology
 R] [inst_3 : Compa…
· 使用定理 `StieltjesFunction.outer_Ioc`：outer_Ioc [DenselyOrdered R] (a b : R) : f.
outer (Ioc a b) = ofReal (f b - f a)
-/
theorem measure_Ioc (a b : R) : f.measure (Ioc a b) = ofReal (f b - f a) := by
  rw [StieltjesFunction.measure]
  exact f.outer_Ioc a b

@[simp]
/-
**StieltjesFunction.measure_singleton** 是 Mathlib 中的一个定理，位于命名空间 `StieltjesFuncti
on`。
形式化陈述：measure_singleton (a : R) : f.measure {a} = ofReal (f a - leftLim f a)
参数：a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `leftLim_eq_of_eq_bot`：leftLim_eq_of_eq_bot [hα : TopologicalSpace α] [h'
α : OrderTopology α] (f : α -> β) {a : α} (h : 𝓝[<] a = ⊥) : leftLim f a = f a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `ENNReal.ofReal_zero`：ENNReal.ofReal 0 = 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用定理 `StieltjesFunction.measure_def`：∀ {R : Type u_2} [inst : LinearOrder R] [
inst_1 : TopologicalSpace R] (f : StieltjesFunction R)   [inst_2 : OrderTopology
 R] [inst_3 : Compa…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `StieltjesFunction.outer_le_length`：outer_le_length (s : Set R) : f.outer
 s <= f.length s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `StieltjesFunction.length_sdiff_botSet`：length_sdiff_botSet {s : Set R} :
 f.length (s \ botSet) = f.length s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.Subsingleton.eq_singleton_of_mem`：∀ {α : Type u} {s : Set α}, s.Subs
ingleton → ∀ {x : α}, x ∈ s → s = {x}
· 使用引理 `subsingleton_botSet`：subsingleton_botSet : (botSet (R
· 使用定理 `sdiff_self`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] {a :
 α}, a \ a = ⊥
· 使用定理 `StieltjesFunction.length_empty`：length_empty : f.length ∅ = 0
· 使用定理 `bot_eq_zero'`：∀ {α : Type u} [inst : AddMonoid α] [inst_1 : LinearOrder 
α] [CanonicallyOrderedAdd α] [inst_3 : OrderBot α], ⊥ = 0
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_seq_strictMono_tendsto'`：exists_seq_strictMono_tendsto' {α : Type
*} [LinearOrder α] [TopologicalSpace α] [DenselyOrdered α] [OrderTopology α] [Fi
rstCountableTopology…
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_firstCountableTopology`：∀ (α
 : Type u) [t : TopologicalSpace α] [SecondCountableTopology α], FirstCountableT
opology α
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_singleton_iff`：mem_singleton_iff {a b : α} : a in ({b} : Set α) 
↔ a = b
（共 72 条，此处仅展示前 30 条）
-/
theorem measure_singleton (a : R) : f.measure {a} = ofReal (f a - leftLim f a) := by
  by_cases ha : IsBot a
  · have : leftLim f a = f a := by
      apply leftLim_eq_of_eq_bot
      simp [nhdsLT_eq_bot_iff, ha]
    simp only [this, sub_self, ofReal_zero]
    apply eq_bot_iff.2
    rw [StieltjesFunction.measure]
    apply (outer_le_length _ _).trans
    rw [← length_sdiff_botSet]
    simp [subsingleton_botSet.eq_singleton_of_mem ha]
  obtain ⟨b, hb⟩ : ∃ b, b < a := by simpa only [IsBot, not_forall, not_le] using ha
  obtain ⟨u, u_mono, u_lt_a, u_lim⟩ :
    ∃ u : ℕ → R, StrictMono u ∧ (∀ n : ℕ, u n ∈ Ioo b a) ∧ Tendsto u atTop (𝓝 a) :=
    exists_seq_strictMono_tendsto' hb
  replace u_lt_a n : u n < a := (u_lt_a n).2
  have A : {a} = ⋂ n, Ioc (u n) a := by
    refine Subset.antisymm (fun x hx => by simp [mem_singleton_iff.1 hx, u_lt_a]) fun x hx => ?_
    replace hx : ∀ (i : ℕ), u i < x ∧ x ≤ a := by simpa using hx
    have : a ≤ x := le_of_tendsto' u_lim fun n => (hx n).1.le
    simp [le_antisymm this (hx 0).2]
  have L1 : Tendsto (fun n => f.measure (Ioc (u n) a)) atTop (𝓝 (f.measure {a})) := by
    rw [A]
    refine tendsto_measure_iInter_atTop (fun n => nullMeasurableSet_Ioc)
      (fun m n hmn => ?_) ?_
    · exact Ioc_subset_Ioc_left (u_mono.monotone hmn)
    · exact ⟨0, by simpa only [measure_Ioc] using ENNReal.ofReal_ne_top⟩
  have L2 :
      Tendsto (fun n => f.measure (Ioc (u n) a)) atTop (𝓝 (ofReal (f a - leftLim f a))) := by
    simp only [measure_Ioc]
    have : Tendsto (fun n => f (u n)) atTop (𝓝 (leftLim f a)) := by
      apply (f.mono.tendsto_leftLim a).comp
      exact
        tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ u_lim
          (Eventually.of_forall fun n => u_lt_a n)
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp (tendsto_const_nhds.sub this)
  exact tendsto_nhds_unique L1 L2

@[simp]
/-
**StieltjesFunction.measure_Icc** 是 Mathlib 中的一个定理，位于命名空间 `StieltjesFunction`。
形式化陈述：measure_Icc (a b : R) : f.measure (Icc a b) = ofReal (f b - leftLim f a)
参数：a b : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Icc_union_Ioc_eq_Icc`：Icc_union_Ioc_eq_Icc (h₁ : a <= b) (h₂ : b <= 
c) : Icc a b union Ioc b c = Icc a c
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Set.Icc_self`：Icc_self (a : α) : Icc a a = {a}
· 使用定理 `MeasureTheory.measure_union`：measure_union (hd : Disjoint s₁ s₂) (h : Me
asurableSet s₂) : μ (s₁ union s₂) = μ s₁ + μ s₂
· 使用定理 `measurableSet_Ioc`：measurableSet_Ioc [ClosedIicTopology α] : MeasurableS
et (Ioc a b)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `StieltjesFunction.measure_singleton`：measure_singleton (a : R) : f.measu
re {a} = ofReal (f a - leftLim f a)
· 使用定理 `StieltjesFunction.measure_Ioc`：measure_Ioc (a b : R) : f.measure (Ioc a 
b) = ofReal (f b - f a)
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Monotone.leftLim_le`：leftLim_le (h : x <= y) : leftLim f x <= f y
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `StieltjesFunction.mono`：mono : Monotone f
· 使用定理 `sub_add_sub_cancel'`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b c : G
), a - b + (c - a) = c - b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.Icc_eq_empty`：Icc_eq_empty (h : ¬a <= b) : Icc a b = ∅
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
（共 33 条，此处仅展示前 30 条）
-/
theorem measure_Icc (a b : R) : f.measure (Icc a b) = ofReal (f b - leftLim f a) := by
  rcases le_or_gt a b with (hab | hab)
  · have A : Disjoint {a} (Ioc a b) := by simp
    simp [← Icc_union_Ioc_eq_Icc le_rfl hab, -singleton_union, ← ENNReal.ofReal_add,
      f.mono.leftLim_le, measure_union A measurableSet_Ioc, f.mono hab]
  · simp only [hab, measure_empty, Icc_eq_empty, not_le]
    symm
    simp [ENNReal.ofReal_eq_zero, f.mono.le_leftLim hab]

@[simp]
/-
**StieltjesFunction.measure_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `StieltjesFunction`。
形式化陈述：measure_Ioo {a b : R} : f.measure (Ioo a b) = ofReal (leftLim f b - f a)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.Ioo_eq_empty`：Ioo_eq_empty (h : ¬a < b) : Ioo a b = ∅
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AddGroup.toOrderedSub`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LE
 α] [AddRightMono α], OrderedSub α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Monotone.leftLim_le`：leftLim_le (h : x <= y) : leftLim f x <= f y
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `StieltjesFunction.mono`：mono : Monotone f
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `_private.Mathlib.MeasureTheory.Measure.Stieltjes.0.StieltjesFunction.mea
sure_Ioo._abel_1_4`：∀ {R : Type u_1} [inst : LinearOrder R] [inst_1 : Topologica
lSpace R] (f : StieltjesFunction R) {a b : R},   ↑f b - ↑f a = ↑f b - Function.l
…
· 使用定理 `StieltjesFunction.measure_Ioc`：measure_Ioc (a b : R) : f.measure (Ioc a 
b) = ofReal (f b - f a)
· 使用定理 `ENNReal.add_right_inj`：add_right_inj (h : a != ∞) : a + b = a + c ↔ b = 
c
· 使用定理 `ENNReal.ofReal_ne_top`：ofReal_ne_top {r : Real} : ENNReal.ofReal r != ∞
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `ENNReal.ofReal_add`：ofReal_add {p q : Real} (hp : 0 <= p) (hq : 0 <= q) 
: ENNReal.ofReal (p + q) = ENNReal.ofReal p + ENNReal.ofReal q
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Monotone.le_leftLim`：le_leftLim (h : x < y) : f x <= leftLim f y
· 使用定理 `Set.Ioo_union_Icc_eq_Ioc`：Ioo_union_Icc_eq_Ioc (h₁ : a < b) (h₂ : b <= c
) : Ioo a b union Icc b c = Ioc a c
· 使用定理 `Set.Icc_self`：Icc_self (a : α) : Icc a a = {a}
· 使用定理 `MeasureTheory.measure_union`：measure_union (hd : Disjoint s₁ s₂) (h : Me
asurableSet s₂) : μ (s₁ union s₂) = μ s₁ + μ s₂
（共 40 条，此处仅展示前 30 条）
-/
theorem measure_Ioo {a b : R} : f.measure (Ioo a b) = ofReal (leftLim f b - f a) := by
  rcases le_or_gt b a with (hab | hab)
  · simp only [hab, measure_empty, Ioo_eq_empty, not_lt]
    symm
    simp [ENNReal.ofReal_eq_zero, f.mono.leftLim_le hab]
  · have A : Disjoint (Ioo a b) {b} := by simp
    have D : f b - f a = f b - leftLim f b + (leftLim f b - f a) := by abel
    have := f.measure_Ioc a b
    simp only [← Ioo_union_Icc_eq_Ioc hab le_rfl, measure_singleton,
      measure_union A (measurableSet_singleton b), Icc_self] at this
    rw [D, ENNReal.ofReal_add, add_comm] at this
    · simpa only [ENNReal.add_right_inj ENNReal.ofReal_ne_top]
    · simp only [f.mono.leftLim_le le_rfl, sub_nonneg]
    · simp only [f.mono.le_leftLim hab, sub_nonneg]

@[simp]
/-
**StieltjesFunction.measure_Ico** 是 Mathlib 中的一个定理，位于命名空间 `StieltjesFunction`。
形式化陈述：measure_Ico (a b : R) : f.measure (Ico a b) = ofReal (leftLim f b - leftLi
m f a)
参数：a b : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.Ico_eq_empty`：Ico_eq_empty (h : ¬a < b) : Ico a b = ∅
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AddGroup.toOrderedSub`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LE
 α] [AddRightMono α], OrderedSub α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Monotone.leftLim`：∀ {α : Type u_1} {β : Type u_2} [inst : LinearOrder α]
 [inst_1 : ConditionallyCompleteLinearOrder β]   [inst_2 : TopologicalSpace β] [
OrderT…
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `StieltjesFunction.mono`：mono : Monotone f
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Set.Icc_union_Ioo_eq_Ico`：Icc_union_Ioo_eq_Ico (h₁ : a <= b) (h₂ : b < c
) : Icc a b union Ioo b c = Ico a c
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Set.Icc_self`：Icc_self (a : α) : Icc a a = {a}
· 使用定理 `MeasureTheory.measure_union`：measure_union (hd : Disjoint s₁ s₂) (h : Me
asurableSet s₂) : μ (s₁ union s₂) = μ s₁ + μ s₂
· 使用定理 `measurableSet_Ioo`：measurableSet_Ioo [OrderClosedTopology α] : Measurabl
eSet (Ioo a b)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `StieltjesFunction.measure_singleton`：measure_singleton (a : R) : f.measu
re {a} = ofReal (f a - leftLim f a)
· 使用定理 `StieltjesFunction.measure_Ioo`：measure_Ioo {a b : R} : f.measure (Ioo a 
b) = ofReal (leftLim f b - f a)
· 使用定理 `Monotone.leftLim_le`：leftLim_le (h : x <= y) : leftLim f x <= f y
（共 33 条，此处仅展示前 30 条）
-/
theorem measure_Ico (a b : R) : f.measure (Ico a b) = ofReal (leftLim f b - leftLim f a) := by
  rcases le_or_gt b a with (hab | hab)
  · simp only [hab, measure_empty, Ico_eq_empty, not_lt]
    symm
    simp [ENNReal.ofReal_eq_zero, f.mono.leftLim hab]
  · have A : Disjoint {a} (Ioo a b) := by simp
    simp [← Icc_union_Ioo_eq_Ico le_rfl hab, -singleton_union, f.mono.leftLim_le,
      measure_union A measurableSet_Ioo, f.mono.le_leftLim hab, ← ENNReal.ofReal_add]

@[simp]
/-
**StieltjesFunction.measure_botSet** 是 Mathlib 中的一个定理，位于命名空间 `StieltjesFunction`
。
形式化陈述：measure_botSet : f.measure botSet = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `botSet_eq_singleton_of_isBot`：botSet_eq_singleton_of_isBot {x : R} (hx :
 IsBot x) : botSet = {x}
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `StieltjesFunction.measure_singleton`：measure_singleton (a : R) : f.measu
re {a} = ofReal (f a - leftLim f a)
· 使用定理 `leftLim_eq_of_isBot`：leftLim_eq_of_isBot {f : α -> β} {a : α} (ha : IsBo
t a) : leftLim f a = f a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `ENNReal.ofReal_zero`：ENNReal.ofReal 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
-/
theorem measure_botSet : f.measure botSet = 0 := by
  by_cases! hx : ∃ x : R, IsBot x
  · simp [botSet_eq_singleton_of_isBot hx.choose_spec, leftLim_eq_of_isBot hx.choose_spec]
  · simp [botSet, hx]
/-
**StieltjesFunction.measure_Iic** 是 Mathlib 中的一个定理，位于命名空间 `StieltjesFunction`。
形式化陈述：measure_Iic {l : Real} (hf : Tendsto f atBot (𝓝 l)) (x : R) : f.measure (I
ic x) = ofReal (f x - l)
参数：hf : Tendsto f atBot (𝓝 l)；x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Icc_bot`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : OrderBot α] 
{a : α}, Set.Icc ⊥ a = Set.Iic a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `StieltjesFunction.measure_Icc`：measure_Icc (a b : R) : f.measure (Icc a 
b) = ofReal (f b - leftLim f a)
· 使用定理 `leftLim_eq_of_isBot`：leftLim_eq_of_isBot {f : α -> β} {a : α} (ha : IsBo
t a) : leftLim f a = f a
· 使用定理 `isBot_bot`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α], IsBot ⊥
· 使用定理 `tendsto_nhds_unique`：tendsto_nhds_unique [T2Space X] {f : Y -> X} {l : F
ilter Y} {a b : X} [NeBot l] (ha : Tendsto f l (𝓝 a)) (hb : Tendsto f l (𝓝 b)) :
 a = b
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Filter.atBot_eq_pure_of_isBot`：∀ {α : Type u} [inst : PartialOrder α] {x
 : α}, IsBot x → Filter.atBot = pure x
· 使用定理 `tendsto_pure_nhds`：tendsto_pure_nhds (f : α -> X) (a : α) : Tendsto f (p
ure a) (𝓝 (f a))
· 使用定理 `NoBotOrder.to_noMinOrder`：NoBotOrder.to_noMinOrder (α : Type*) [LinearOr
der α] [NoBotOrder α] : NoMinOrder α
· 使用定理 `ENNReal.instT2Space`：T2Space ENNReal
· 使用定理 `Filter.atBot_neBot`：∀ {α : Type u_3} [inst : Preorder α] [IsCodirectedOr
der α] [Nonempty α], Filter.atBot.NeBot
· 使用定理 `SemilatticeInf.instIsCodirectedOrder`：∀ {α : Type u_1} [inst : Semilatti
ceInf α], IsCodirectedOrder α
· 使用定理 `MeasureTheory.tendsto_measure_Ioc_atBot`：tendsto_measure_Ioc_atBot [Preo
rder α] [NoMinOrder α] [(atBot : Filter α).IsCountablyGenerated] (μ : Measure α)
 (a : α) : Tendsto (fun x => …
· 使用定理 `instIsCountablyGenerated_atBot`：∀ {α : Type u} [inst : TopologicalSpace 
α] [inst_1 : LinearOrder α] [OrderTopology α]   [TopologicalSpace.SeparableSpace
 α], Filter.atBot.Is…
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `StieltjesFunction.measure_Ioc`：measure_Ioc (a b : R) : f.measure (Ioc a 
b) = ofReal (f b - f a)
· 使用定理 `ENNReal.tendsto_ofReal`：tendsto_ofReal {f : Filter α} {m : α -> Real} {a
 : Real} (h : Tendsto m f (𝓝 a)) : Tendsto (fun a => ENNReal.ofReal (m a)) f (𝓝 
(ENNReal.ofR…
· 使用定理 `Filter.Tendsto.const_sub`：∀ {G : Type w} {α : Type u} [inst : Topologica
lSpace G] [inst_1 : Sub G] [ContinuousSub G] (b : G) {c : G} {f : α → G}   {l : 
Filter α}, Fil…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
-/
theorem measure_Iic {l : ℝ} (hf : Tendsto f atBot (𝓝 l)) (x : R) :
    f.measure (Iic x) = ofReal (f x - l) := by
  have : Nonempty R := ⟨x⟩
  cases botOrderOrNoBotOrder R
  · have : Iic x = Icc ⊥ x := by simp
    rw [atBot_eq_pure_of_isBot isBot_bot] at hf
    rw [this, measure_Icc, leftLim_eq_of_isBot isBot_bot,
      tendsto_nhds_unique hf (tendsto_pure_nhds f ⊥)]
  have : NoMinOrder R := NoBotOrder.to_noMinOrder R
  refine tendsto_nhds_unique (tendsto_measure_Ioc_atBot _ _) ?_
  simp_rw [measure_Ioc]
  exact ENNReal.tendsto_ofReal (Tendsto.const_sub _ hf)
/-
**StieltjesFunction.measure_Iio** 是 Mathlib 中的一个引理，位于命名空间 `StieltjesFunction`。
形式化陈述：measure_Iio {l : Real} (hf : Tendsto f atBot (𝓝 l)) (x : R) : f.measure (I
io x) = ofReal (leftLim f x - l)
参数：hf : Tendsto f atBot (𝓝 l)；x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Iic_sdiff_right`：Iic_sdiff_right : Iic a \ {a} = Iio a
· 使用定理 `MeasureTheory.measure_sdiff`：measure_sdiff (h : s₂ subseteq s₁) (h₂ : Nu
llMeasurableSet s₂ μ) (h_fin : μ s₂ != ∞) : μ (s₁ \ s₂) = μ s₁ - μ s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.nullMeasurableSet_singleton`：nullMeasurableSet_singleton (
x : α) : NullMeasurableSet {x} μ
· 使用定理 `instMeasurableSingletonClassOfMeasurableEq`：∀ {α : Type u_1} [inst : Mea
surableSpace α] [MeasurableEq α], MeasurableSingletonClass α
· 使用定理 `instMeasurableEqOfSecondCountableTopologyOfT2Space`：∀ {α : Type u_1} [in
st : TopologicalSpace α] [inst_1 : MeasurableSpace α] [OpensMeasurableSpace α]  
 [SecondCountableTopology α] [T2Space α]…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `T25Space.t2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T25Space
 X], T2Space X
· 使用定理 `T3Space.t25Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T3Space 
X], T25Space X
· 使用定理 `T4Space.t3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T4Space X
], T3Space X
· 使用定理 `T5Space.toT4Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T5Space
 X], T4Space X
· 使用定理 `OrderTopology.t5Space`：∀ {X : Type u_1} [inst : LinearOrder X] [inst_1 :
 TopologicalSpace X] [OrderTopology X], T5Space X
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `StieltjesFunction.measure_singleton`：measure_singleton (a : R) : f.measu
re {a} = ofReal (f a - leftLim f a)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `StieltjesFunction.measure_Iic`：measure_Iic {l : Real} (hf : Tendsto f at
Bot (𝓝 l)) (x : R) : f.measure (Iic x) = ofReal (f x - l)
· 使用定理 `ENNReal.ofReal_sub`：ofReal_sub (p : Real) {q : Real} (hq : 0 <= q) : ENN
Real.ofReal (p - q) = ENNReal.ofReal p - ENNReal.ofReal q
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddRight
Mono α] {a b : α}, 0 ≤ a - b ↔ b ≤ a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Monotone.leftLim_le`：leftLim_le (h : x <= y) : leftLim f x <= f y
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `StieltjesFunction.mono'`：∀ {R : Type u_1} [inst : LinearOrder R] [inst_1
 : TopologicalSpace R] (self : StieltjesFunction R), Monotone ↑self
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `sub_sub_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b c
 : G), c - a - (c - b) = b - a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma measure_Iio {l : ℝ} (hf : Tendsto f atBot (𝓝 l)) (x : R) :
    f.measure (Iio x) = ofReal (leftLim f x - l) := by
  have : Nonempty R := ⟨x⟩
  rw [← Iic_sdiff_right, measure_sdiff _ (nullMeasurableSet_singleton x), measure_singleton,
    f.measure_Iic hf, ← ofReal_sub _ (sub_nonneg.mpr <| Monotone.leftLim_le f.mono' le_rfl)]
    <;> simp
/-
**StieltjesFunction.measure_Ici** 是 Mathlib 中的一个定理，位于命名空间 `StieltjesFunction`。
形式化陈述：measure_Ici {l : Real} (hf : Tendsto f atTop (𝓝 l)) (x : R) : f.measure (I
ci x) = ofReal (l - leftLim f x)
参数：hf : Tendsto f atTop (𝓝 l)；x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Icc_top`：Icc_top : Icc a ⊤ = Ici a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `StieltjesFunction.measure_Icc`：measure_Icc (a b : R) : f.measure (Icc a 
b) = ofReal (f b - leftLim f a)
· 使用定理 `tendsto_nhds_unique`：tendsto_nhds_unique [T2Space X] {f : Y -> X} {l : F
ilter Y} {a b : X} [NeBot l] (ha : Tendsto f l (𝓝 a)) (hb : Tendsto f l (𝓝 b)) :
 a = b
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用引理 `Filter.atTop_eq_pure_of_isTop`：atTop_eq_pure_of_isTop [PartialOrder α] {
x : α} (hx : IsTop x) : (atTop : Filter α) = pure x
· 使用定理 `isTop_top`：isTop_top : IsTop (⊤ : α)
· 使用定理 `tendsto_pure_nhds`：tendsto_pure_nhds (f : α -> X) (a : α) : Tendsto f (p
ure a) (𝓝 (f a))
· 使用定理 `NoTopOrder.to_noMaxOrder`：∀ (α : Type u_3) [inst : LinearOrder α] [NoTop
Order α], NoMaxOrder α
· 使用定理 `ENNReal.instT2Space`：T2Space ENNReal
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `MeasureTheory.tendsto_measure_Ico_atTop`：tendsto_measure_Ico_atTop [Preo
rder α] [NoMaxOrder α] [(atTop : Filter α).IsCountablyGenerated] (μ : Measure α)
 (a : α) : Tendsto (fun x => …
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `StieltjesFunction.measure_Ico`：measure_Ico (a b : R) : f.measure (Ico a 
b) = ofReal (leftLim f b - leftLim f a)
· 使用定理 `ENNReal.tendsto_ofReal`：tendsto_ofReal {f : Filter α} {m : α -> Real} {a
 : Real} (h : Tendsto m f (𝓝 a)) : Tendsto (fun a => ENNReal.ofReal (m a)) f (𝓝 
(ENNReal.ofR…
· 使用定理 `Filter.Tendsto.sub_const`：∀ {G : Type w} {α : Type u} [inst : Topologica
lSpace G] [inst_1 : Sub G] [ContinuousSub G] {c : G} {f : α → G}   {l : Filter α
}, Filter.Tend…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `tendsto_leftLim_atTop_of_tendsto`：tendsto_leftLim_atTop_of_tendsto [Topo
logicalSpace α] [OrderTopology α] [NoTopOrder α] [T3Space β] {f : α -> β} {b : β
} (h : Tendsto f atTop…
· 使用定理 `T4Space.t3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T4Space X
], T3Space X
· 使用定理 `instT4SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T4Space X
-/
theorem measure_Ici {l : ℝ} (hf : Tendsto f atTop (𝓝 l)) (x : R) :
    f.measure (Ici x) = ofReal (l - leftLim f x) := by
  have : Nonempty R := ⟨x⟩
  cases topOrderOrNoTopOrder R
  · have : Ici x = Icc x ⊤ := by simp
    rw [atTop_eq_pure_of_isTop isTop_top] at hf
    rw [this, measure_Icc, tendsto_nhds_unique hf (tendsto_pure_nhds f ⊤)]
  have : NoMaxOrder R := NoTopOrder.to_noMaxOrder R
  refine tendsto_nhds_unique (tendsto_measure_Ico_atTop _ _) ?_
  simp_rw [measure_Ico]
  exact ENNReal.tendsto_ofReal (Tendsto.sub_const (tendsto_leftLim_atTop_of_tendsto hf) _)
/-
**StieltjesFunction.measure_Ioi** 是 Mathlib 中的一个引理，位于命名空间 `StieltjesFunction`。
形式化陈述：measure_Ioi {l : Real} (hf : Tendsto f atTop (𝓝 l)) (x : R) : f.measure (I
oi x) = ofReal (l - f x)
参数：hf : Tendsto f atTop (𝓝 l)；x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Ici_sdiff_left`：∀ {α : Type u_1} [inst : PartialOrder α] {a : α}, Se
t.Ici a \ {a} = Set.Ioi a
· 使用定理 `MeasureTheory.measure_sdiff`：measure_sdiff (h : s₂ subseteq s₁) (h₂ : Nu
llMeasurableSet s₂ μ) (h_fin : μ s₂ != ∞) : μ (s₁ \ s₂) = μ s₁ - μ s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.nullMeasurableSet_singleton`：nullMeasurableSet_singleton (
x : α) : NullMeasurableSet {x} μ
· 使用定理 `instMeasurableSingletonClassOfMeasurableEq`：∀ {α : Type u_1} [inst : Mea
surableSpace α] [MeasurableEq α], MeasurableSingletonClass α
· 使用定理 `instMeasurableEqOfSecondCountableTopologyOfT2Space`：∀ {α : Type u_1} [in
st : TopologicalSpace α] [inst_1 : MeasurableSpace α] [OpensMeasurableSpace α]  
 [SecondCountableTopology α] [T2Space α]…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `T25Space.t2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T25Space
 X], T2Space X
· 使用定理 `T3Space.t25Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T3Space 
X], T25Space X
· 使用定理 `T4Space.t3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T4Space X
], T3Space X
· 使用定理 `T5Space.toT4Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T5Space
 X], T4Space X
· 使用定理 `OrderTopology.t5Space`：∀ {X : Type u_1} [inst : LinearOrder X] [inst_1 :
 TopologicalSpace X] [OrderTopology X], T5Space X
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `StieltjesFunction.measure_singleton`：measure_singleton (a : R) : f.measu
re {a} = ofReal (f a - leftLim f a)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `StieltjesFunction.measure_Ici`：measure_Ici {l : Real} (hf : Tendsto f at
Top (𝓝 l)) (x : R) : f.measure (Ici x) = ofReal (l - leftLim f x)
· 使用定理 `ENNReal.ofReal_sub`：ofReal_sub (p : Real) {q : Real} (hq : 0 <= q) : ENN
Real.ofReal (p - q) = ENNReal.ofReal p - ENNReal.ofReal q
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddRight
Mono α] {a b : α}, 0 ≤ a - b ↔ b ≤ a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Monotone.leftLim_le`：leftLim_le (h : x <= y) : leftLim f x <= f y
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `StieltjesFunction.mono'`：∀ {R : Type u_1} [inst : LinearOrder R] [inst_1
 : TopologicalSpace R] (self : StieltjesFunction R), Monotone ↑self
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `sub_sub_sub_cancel_right`：∀ {G : Type u_3} [inst : AddGroup G] (a b c : 
G), a - c - (b - c) = a - b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma measure_Ioi {l : ℝ} (hf : Tendsto f atTop (𝓝 l)) (x : R) :
    f.measure (Ioi x) = ofReal (l - f x) := by
  rw [← Ici_sdiff_left, measure_sdiff _ (nullMeasurableSet_singleton x), measure_singleton,
    f.measure_Ici hf, ← ofReal_sub _ (sub_nonneg.mpr <| Monotone.leftLim_le f.mono' le_rfl)]
    <;> simp
/-
**StieltjesFunction.measure_Ioi_of_tendsto_atTop_atTop** 是 Mathlib 中的一个引理，位于命名空间
 `StieltjesFunction`。
形式化陈述：measure_Ioi_of_tendsto_atTop_atTop (hf : Tendsto f atTop atTop) (x : R) : 
f.measure (Ioi x) = ∞
参数：hf : Tendsto f atTop atTop；x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.eq_top_of_forall_nnreal_le`：eq_top_of_forall_nnreal_le {x : Real
>=0∞} (h : forall r : Real>=0, ↑r <= x) : x = ∞
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Filter.eventually_atTop`：eventually_atTop : (forallᶠ x in atTop, p x) ↔ 
exists a, forall b, a <= b -> p b
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `Filter.tendsto_atTop`：tendsto_atTop [Preorder β] {m : α -> β} {f : Filte
r α} : Tendsto m f atTop ↔ forall b, forallᶠ a in f, b <= m a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `ENNReal.ofReal_le_ofReal`：ofReal_le_ofReal {p q : Real} (h : p <= q) : E
NNReal.ofReal p <= ENNReal.ofReal q
· 使用定理 `le_tsub_of_add_le_right`：le_tsub_of_add_le_right (h : a + b <= c) : a <=
 c - b
· 使用定理 `AddGroup.toOrderedSub`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LE
 α] [AddRightMono α], OrderedSub α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.coe_nnreal_eq`：coe_nnreal_eq (r : Real>=0) : (r : Real>=0∞) = EN
NReal.ofReal r
· 使用定理 `StieltjesFunction.measure_Ioc`：measure_Ioc (a b : R) : f.measure (Ioc a 
b) = ofReal (f b - f a)
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.Ioc_subset_Ioi_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioc b a ⊆ Set.Ioi b
-/
lemma measure_Ioi_of_tendsto_atTop_atTop (hf : Tendsto f atTop atTop) (x : R) :
    f.measure (Ioi x) = ∞ := by
  have : Nonempty R := ⟨x⟩
  refine ENNReal.eq_top_of_forall_nnreal_le fun r ↦ ?_
  obtain ⟨N, hN⟩ := eventually_atTop.mp (tendsto_atTop.mp hf (r + f x))
  exact (f.measure_Ioc x (max x N) ▸ ENNReal.coe_nnreal_eq r ▸ (ENNReal.ofReal_le_ofReal <|
    le_tsub_of_add_le_right <| hN _ (le_max_right x N))).trans (measure_mono Ioc_subset_Ioi_self)
/-
**StieltjesFunction.measure_Ici_of_tendsto_atTop_atTop** 是 Mathlib 中的一个引理，位于命名空间
 `StieltjesFunction`。
形式化陈述：measure_Ici_of_tendsto_atTop_atTop (hf : Tendsto f atTop atTop) (x : R) : 
f.measure (Ici x) = ∞
参数：hf : Tendsto f atTop atTop；x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `top_le_iff`：top_le_iff : ⊤ <= a ↔ a = ⊤
· 使用引理 `StieltjesFunction.measure_Ioi_of_tendsto_atTop_atTop`：measure_Ioi_of_ten
dsto_atTop_atTop (hf : Tendsto f atTop atTop) (x : R) : f.measure (Ioi x) = ∞
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.Ioi_subset_Ici_self`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, S
et.Ioi a ⊆ Set.Ici a
-/
lemma measure_Ici_of_tendsto_atTop_atTop (hf : Tendsto f atTop atTop) (x : R) :
    f.measure (Ici x) = ∞ := by
  rw [← top_le_iff, ← f.measure_Ioi_of_tendsto_atTop_atTop hf x]
  exact measure_mono Ioi_subset_Ici_self
/-
**StieltjesFunction.measure_Iic_of_tendsto_atBot_atBot** 是 Mathlib 中的一个引理，位于命名空间
 `StieltjesFunction`。
形式化陈述：measure_Iic_of_tendsto_atBot_atBot (hf : Tendsto f atBot atBot) (x : R) : 
f.measure (Iic x) = ∞
参数：hf : Tendsto f atBot atBot；x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.eq_top_of_forall_nnreal_le`：eq_top_of_forall_nnreal_le {x : Real
>=0∞} (h : forall r : Real>=0, ↑r <= x) : x = ∞
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.eventually_atBot`：∀ {α : Type u_3} [inst : Preorder α] [IsCodirec
tedOrder α] {p : α → Prop} [Nonempty α],   (∀ᶠ (x : α) in Filter.atBot, p x) ↔ ∃
 a, ∀ b ≤ a, …
· 使用定理 `SemilatticeInf.instIsCodirectedOrder`：∀ {α : Type u_1} [inst : Semilatti
ceInf α], IsCodirectedOrder α
· 使用定理 `Filter.tendsto_atBot`：∀ {α : Type u_3} {β : Type u_4} [inst : Preorder β
] {m : α → β} {f : Filter α},   Filter.Tendsto m f Filter.atBot ↔ ∀ (b : β), ∀ᶠ 
(a : α) in…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `ENNReal.ofReal_le_ofReal`：ofReal_le_ofReal {p q : Real} (h : p <= q) : E
NNReal.ofReal p <= ENNReal.ofReal q
· 使用定理 `le_sub_comm`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : LE α] [Add
LeftMono α] {a b c : α}, a ≤ b - c ↔ c ≤ b - a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `min_le_right`：min_le_right (a b : α) : min a b <= b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.coe_nnreal_eq`：coe_nnreal_eq (r : Real>=0) : (r : Real>=0∞) = EN
NReal.ofReal r
· 使用定理 `StieltjesFunction.measure_Ioc`：measure_Ioc (a b : R) : f.measure (Ioc a 
b) = ofReal (f b - f a)
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.Ioc_subset_Iic_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioc a b ⊆ Set.Iic b
-/
lemma measure_Iic_of_tendsto_atBot_atBot (hf : Tendsto f atBot atBot) (x : R) :
    f.measure (Iic x) = ∞ := by
  have : Nonempty R := ⟨x⟩
  refine ENNReal.eq_top_of_forall_nnreal_le fun r ↦ ?_
  obtain ⟨N, hN⟩ := eventually_atBot.mp (tendsto_atBot.mp hf (f x - r))
  exact (f.measure_Ioc (min x N) x ▸ ENNReal.coe_nnreal_eq r ▸ (ENNReal.ofReal_le_ofReal <|
    le_sub_comm.mp <| hN _ (min_le_right x N))).trans (measure_mono Ioc_subset_Iic_self)
/-
**StieltjesFunction.measure_Iio_of_tendsto_atBot_atBot** 是 Mathlib 中的一个引理，位于命名空间
 `StieltjesFunction`。
形式化陈述：measure_Iio_of_tendsto_atBot_atBot (hf : Tendsto f atBot atBot) (x : R) : 
f.measure (Iio x) = ∞
参数：hf : Tendsto f atBot atBot；x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.tendsto_pure_left`：tendsto_pure_left {f : α -> β} {a : α} {l : Fi
lter β} : Tendsto f (pure a) l ↔ forall s in l, f a in s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.atBot_eq_pure_of_isBot`：∀ {α : Type u} [inst : PartialOrder α] {x
 : α}, IsBot x → Filter.atBot = pure x
· 使用定理 `isBot_bot`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α], IsBot ⊥
· 使用定理 `Filter.Iio_mem_atBot`：∀ {α : Type u_3} [inst : Preorder α] [NoBotOrder α
] (x : α), Set.Iio x ∈ Filter.atBot
· 使用定理 `instNoBotOrderOfNoMinOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMinO
rder α], NoBotOrder α
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R
· 使用定理 `NoBotOrder.to_noMinOrder`：NoBotOrder.to_noMinOrder (α : Type*) [LinearOr
der α] [NoBotOrder α] : NoMinOrder α
· 使用定理 `NoMinOrder.exists_lt`：∀ {α : Type u_3} {inst : LT α} [self : NoMinOrder 
α] (a : α), ∃ b, b < a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `top_le_iff`：top_le_iff : ⊤ <= a ↔ a = ⊤
· 使用引理 `StieltjesFunction.measure_Iic_of_tendsto_atBot_atBot`：measure_Iic_of_ten
dsto_atBot_atBot (hf : Tendsto f atBot atBot) (x : R) : f.measure (Iic x) = ∞
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.Iic_subset_Iio`：Iic_subset_Iio : Iic a subseteq Iio b ↔ a < b
-/
lemma measure_Iio_of_tendsto_atBot_atBot (hf : Tendsto f atBot atBot) (x : R) :
    f.measure (Iio x) = ∞ := by
  have : Nonempty R := ⟨x⟩
  cases botOrderOrNoBotOrder R
  · rw [atBot_eq_pure_of_isBot isBot_bot] at hf
    simpa using (tendsto_pure_left.1 hf) _ (Iio_mem_atBot (f ⊥))
  have : NoMinOrder R := NoBotOrder.to_noMinOrder R
  obtain ⟨y, hy⟩ : ∃ y, y < x := exists_lt x
  rw [← top_le_iff, ← f.measure_Iic_of_tendsto_atBot_atBot hf y]
  exact measure_mono <| Set.Iic_subset_Iio.mpr <| hy
/-
**StieltjesFunction.measure_univ** 是 Mathlib 中的一个定理，位于命名空间 `StieltjesFunction`。
形式化陈述：measure_univ [Nonempty R] {l u : Real} (hfl : Tendsto f atBot (𝓝 l)) (hfu 
: Tendsto f atTop (𝓝 u)) : f.measure univ = ofReal (u - l)
参数：hfl : Tendsto f atBot (𝓝 l)；hfu : Tendsto f atTop (𝓝 u)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_nhds_unique`：tendsto_nhds_unique [T2Space X] {f : Y -> X} {l : F
ilter Y} {a b : X} [NeBot l] (ha : Tendsto f l (𝓝 a)) (hb : Tendsto f l (𝓝 b)) :
 a = b
· 使用定理 `ENNReal.instT2Space`：T2Space ENNReal
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `MeasureTheory.tendsto_measure_Iic_atTop`：tendsto_measure_Iic_atTop [Preo
rder α] [(atTop : Filter α).IsCountablyGenerated] (μ : Measure α) : Tendsto (fun
 x => μ (Iic x)) atTop (𝓝 (μ …
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `StieltjesFunction.measure_Iic`：measure_Iic {l : Real} (hf : Tendsto f at
Bot (𝓝 l)) (x : R) : f.measure (Iic x) = ofReal (f x - l)
· 使用定理 `ENNReal.tendsto_ofReal`：tendsto_ofReal {f : Filter α} {m : α -> Real} {a
 : Real} (h : Tendsto m f (𝓝 a)) : Tendsto (fun a => ENNReal.ofReal (m a)) f (𝓝 
(ENNReal.ofR…
· 使用定理 `Filter.Tendsto.sub_const`：∀ {G : Type w} {α : Type u} [inst : Topologica
lSpace G] [inst_1 : Sub G] [ContinuousSub G] {c : G} {f : α → G}   {l : Filter α
}, Filter.Tend…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
-/
theorem measure_univ [Nonempty R]
    {l u : ℝ} (hfl : Tendsto f atBot (𝓝 l)) (hfu : Tendsto f atTop (𝓝 u)) :
    f.measure univ = ofReal (u - l) := by
  refine tendsto_nhds_unique (tendsto_measure_Iic_atTop _) ?_
  simp_rw [measure_Iic f hfl]
  exact ENNReal.tendsto_ofReal (Tendsto.sub_const hfu _)
/-
**StieltjesFunction.measure_univ_of_tendsto_atTop_atTop** 是 Mathlib 中的一个引理，位于命名空
间 `StieltjesFunction`。
形式化陈述：measure_univ_of_tendsto_atTop_atTop [Nonempty R] (hf : Tendsto f atTop atT
op) : f.measure univ = ∞
参数：hf : Tendsto f atTop atTop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `top_le_iff`：top_le_iff : ⊤ <= a ↔ a = ⊤
· 使用引理 `StieltjesFunction.measure_Ioi_of_tendsto_atTop_atTop`：measure_Ioi_of_ten
dsto_atTop_atTop (hf : Tendsto f atTop atTop) (x : R) : f.measure (Ioi x) = ∞
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
-/
lemma measure_univ_of_tendsto_atTop_atTop [Nonempty R] (hf : Tendsto f atTop atTop) :
    f.measure univ = ∞ := by
  inhabit R
  rw [← top_le_iff, ← f.measure_Ioi_of_tendsto_atTop_atTop hf default]
  exact measure_mono (subset_univ _)
/-
**StieltjesFunction.measure_univ_of_tendsto_atBot_atBot** 是 Mathlib 中的一个引理，位于命名空
间 `StieltjesFunction`。
形式化陈述：measure_univ_of_tendsto_atBot_atBot [Nonempty R] (hf : Tendsto f atBot atB
ot) : f.measure univ = ∞
参数：hf : Tendsto f atBot atBot。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `top_le_iff`：top_le_iff : ⊤ <= a ↔ a = ⊤
· 使用引理 `StieltjesFunction.measure_Iio_of_tendsto_atBot_atBot`：measure_Iio_of_ten
dsto_atBot_atBot (hf : Tendsto f atBot atBot) (x : R) : f.measure (Iio x) = ∞
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
-/
lemma measure_univ_of_tendsto_atBot_atBot [Nonempty R] (hf : Tendsto f atBot atBot) :
    f.measure univ = ∞ := by
  inhabit R
  rw [← top_le_iff, ← f.measure_Iio_of_tendsto_atBot_atBot hf default]
  exact measure_mono (subset_univ _)
/-
**StieltjesFunction.isFiniteMeasure** 是 Mathlib 中的一个引理，位于命名空间 `StieltjesFunction
`。
形式化陈述：isFiniteMeasure {l u : Real} (hfl : Tendsto f atBot (𝓝 l)) (hfu : Tendsto 
f atTop (𝓝 u)) : IsFiniteMeasure f.measure
参数：hfl : Tendsto f atBot (𝓝 l)；hfu : Tendsto f atTop (𝓝 u)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.eq_empty_of_isEmpty`：eq_empty_of_isEmpty (s : Set α) [IsEmpty s] : s
 = ∅
· 使用定理 `instIsEmptySubtype`：∀ {α : Sort u} [IsEmpty α] (p : α → Prop), IsEmpty (
Subtype p)
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `StieltjesFunction.measure_univ`：measure_univ [Nonempty R] {l u : Real} (
hfl : Tendsto f atBot (𝓝 l)) (hfu : Tendsto f atTop (𝓝 u)) : f.measure univ = of
Real (u - l)
-/
lemma isFiniteMeasure {l u : ℝ}
    (hfl : Tendsto f atBot (𝓝 l)) (hfu : Tendsto f atTop (𝓝 u)) :
    IsFiniteMeasure f.measure := by
  constructor
  cases isEmpty_or_nonempty R
  · simp [eq_empty_of_isEmpty]
  · simp [f.measure_univ hfl hfu]
/-
**StieltjesFunction.isFiniteMeasure_of_forall_abs_le** 是 Mathlib 中的一个引理，位于命名空间 `
StieltjesFunction`。
形式化陈述：isFiniteMeasure_of_forall_abs_le {C : Real} (h : forall x, |f x| <= C) : I
sFiniteMeasure f.measure
参数：h : forall x, |f x| <= C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `MeasureTheory.isFiniteMeasureOfIsEmpty`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [IsEmpty α], MeasureTheory.IsFiniteMeasu
re μ
· 使用定理 `tendsto_atTop_of_monotone`：tendsto_atTop_of_monotone {ι α : Type*} [Preo
rder ι] [TopologicalSpace α] [ConditionallyCompleteLinearOrder α] [OrderTopology
 α] {f : ι -> α…
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `StieltjesFunction.mono`：mono : Monotone f
· 使用定理 `Filter.Eventually.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α} [
f.NeBot], (∀ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.tendsto_atTop`：tendsto_atTop [Preorder β] {m : α -> β} {f : Filte
r α} : Tendsto m f atTop ↔ forall b, forallᶠ a in f, b <= m a
· 使用定理 `tendsto_atBot_of_monotone`：tendsto_atBot_of_monotone {ι α : Type*} [Preo
rder ι] [TopologicalSpace α] [ConditionallyCompleteLinearOrder α] [OrderTopology
 α] {f : ι -> α…
· 使用定理 `Filter.atBot_neBot`：∀ {α : Type u_3} [inst : Preorder α] [IsCodirectedOr
der α] [Nonempty α], Filter.atBot.NeBot
· 使用定理 `SemilatticeInf.instIsCodirectedOrder`：∀ {α : Type u_1} [inst : Semilatti
ceInf α], IsCodirectedOrder α
· 使用定理 `Filter.tendsto_atBot`：∀ {α : Type u_3} {β : Type u_4} [inst : Preorder β
] {m : α → β} {f : Filter α},   Filter.Tendsto m f Filter.atBot ↔ ∀ (b : β), ∀ᶠ 
(a : α) in…
· 使用引理 `StieltjesFunction.isFiniteMeasure`：isFiniteMeasure {l u : Real} (hfl : T
endsto f atBot (𝓝 l)) (hfu : Tendsto f atTop (𝓝 u)) : IsFiniteMeasure f.measure
-/
lemma isFiniteMeasure_of_forall_abs_le {C : ℝ} (h : ∀ x, |f x| ≤ C) :
    IsFiniteMeasure f.measure := by
  cases isEmpty_or_nonempty R
  · infer_instance
  obtain ⟨u, hu⟩ : ∃ u, Tendsto f atTop (𝓝 u) := by
    rcases tendsto_atTop_of_monotone f.mono with H | H
    · obtain ⟨x, hx⟩ : ∃ x, C + 1 ≤ f x := (tendsto_atTop.1 H (C + 1)).exists
      grind
    exact H
  obtain ⟨l, hl⟩ : ∃ l, Tendsto f atBot (𝓝 l) := by
    rcases tendsto_atBot_of_monotone f.mono with H | H
    · obtain ⟨x, hx⟩ : ∃ x, f x ≤ - C - 1 := (tendsto_atBot.1 H (-C - 1)).exists
      grind
    exact H
  exact f.isFiniteMeasure hl hu
/-
**StieltjesFunction.isProbabilityMeasure** 是 Mathlib 中的一个引理，位于命名空间 `StieltjesFun
ction`。
形式化陈述：isProbabilityMeasure [Nonempty R] (hf_bot : Tendsto f atBot (𝓝 0)) (hf_top
 : Tendsto f atTop (𝓝 1)) : IsProbabilityMeasure f.measure
参数：hf_bot : Tendsto f atBot (𝓝 0)；hf_top : Tendsto f atTop (𝓝 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `StieltjesFunction.measure_univ`：measure_univ [Nonempty R] {l u : Real} (
hfl : Tendsto f atBot (𝓝 l)) (hfu : Tendsto f atTop (𝓝 u)) : f.measure univ = of
Real (u - l)
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `ENNReal.ofReal_one`：ENNReal.ofReal 1 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma isProbabilityMeasure [Nonempty R]
    (hf_bot : Tendsto f atBot (𝓝 0)) (hf_top : Tendsto f atTop (𝓝 1)) :
    IsProbabilityMeasure f.measure := ⟨by simp [f.measure_univ hf_bot hf_top]⟩
/-
**StieltjesFunction.instIsLocallyFiniteMeasure** 是 Mathlib 中的一个实例，位于命名空间 `Stielt
jesFunction`。
形式化陈述：instIsLocallyFiniteMeasure : IsLocallyFiniteMeasure f.measure
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_Icc_mem_subset_of_mem_nhds`：exists_Icc_mem_subset_of_mem_nhds {a 
: α} {s : Set α} (hs : s in 𝓝 a) : exists b c, a in Icc b c ∧ Icc b c in 𝓝 a ∧ I
cc b c subseteq s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `StieltjesFunction.measure_Icc`：measure_Icc (a b : R) : f.measure (Icc a 
b) = ofReal (f b - leftLim f a)
-/
instance instIsLocallyFiniteMeasure : IsLocallyFiniteMeasure f.measure := by
  refine ⟨fun x ↦ ?_⟩
  obtain ⟨b, c, -, h, -⟩ : ∃ b c, x ∈ Icc b c ∧ Icc b c ∈ 𝓝 x ∧ Icc b c ⊆ univ :=
    exists_Icc_mem_subset_of_mem_nhds (by simp)
  exact ⟨Icc b c, h, by simp⟩
/-
**StieltjesFunction.eq_of_measure_of_tendsto_atBot** 是 Mathlib 中的一个引理，位于命名空间 `St
ieltjesFunction`。
形式化陈述：eq_of_measure_of_tendsto_atBot (g : StieltjesFunction R) {l : Real} (hfg :
 f.measure = g.measure) (hfl : Tendsto f atBot (𝓝 l)) (hgl : Tendsto g atBot (𝓝 
l)) : f = g
参数：g : StieltjesFunction R；hfg : f.measure = g.measure；hfl : Tendsto f atBot (𝓝 
l)；hgl : Tendsto g atBot (𝓝 l)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StieltjesFunction.ext`：∀ {R : Type u_1} [inst : LinearOrder R] [inst_1 :
 TopologicalSpace R] {f g : StieltjesFunction R},   (∀ (x : R), ↑f x = ↑g x) → f
 = g
· 使用定理 `StieltjesFunction.measure_Iic`：measure_Iic {l : Real} (hf : Tendsto f at
Bot (𝓝 l)) (x : R) : f.measure (Iic x) = ofReal (f x - l)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `ENNReal.ofReal_eq_ofReal_iff`：ofReal_eq_ofReal_iff {p q : Real} (hp : 0 
<= p) (hq : 0 <= q) : ENNReal.ofReal p = ENNReal.ofReal q ↔ p = q
· 使用定理 `sub_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddRight
Mono α] {a b : α}, 0 ≤ a - b ↔ b ≤ a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Monotone.le_of_tendsto`：Monotone.le_of_tendsto [TopologicalSpace α] [Pre
order α] [OrderClosedTopology α] [Preorder β] [IsCodirectedOrder β] {f : β -> α}
 {a : α} (hf…
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `SemilatticeInf.instIsCodirectedOrder`：∀ {α : Type u_1} [inst : Semilatti
ceInf α], IsCodirectedOrder α
· 使用定理 `StieltjesFunction.mono`：mono : Monotone f
-/
lemma eq_of_measure_of_tendsto_atBot (g : StieltjesFunction R) {l : ℝ}
    (hfg : f.measure = g.measure) (hfl : Tendsto f atBot (𝓝 l)) (hgl : Tendsto g atBot (𝓝 l)) :
    f = g := by
  ext x
  have hf := measure_Iic f hfl x
  rw [hfg, measure_Iic g hgl x, ENNReal.ofReal_eq_ofReal_iff, eq_comm] at hf
  · simpa using hf
  · rw [sub_nonneg]
    exact Monotone.le_of_tendsto g.mono hgl x
  · rw [sub_nonneg]
    exact Monotone.le_of_tendsto f.mono hfl x
/-
**StieltjesFunction.eq_of_measure_of_eq** 是 Mathlib 中的一个引理，位于命名空间 `StieltjesFunc
tion`。
形式化陈述：eq_of_measure_of_eq (g : StieltjesFunction R) {y : R} (hfg : f.measure = g
.measure) (hy : f y = g y) : f = g
参数：g : StieltjesFunction R；hfg : f.measure = g.measure；hy : f y = g y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StieltjesFunction.ext`：∀ {R : Type u_1} [inst : LinearOrder R] [inst_1 :
 TopologicalSpace R] {f g : StieltjesFunction R},   (∀ (x : R), ↑f x = ↑g x) → f
 = g
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `StieltjesFunction.measure_Ioc`：measure_Ioc (a b : R) : f.measure (Ioc a 
b) = ofReal (f b - f a)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `ENNReal.ofReal_eq_ofReal_iff`：ofReal_eq_ofReal_iff {p q : Real} (hp : 0 
<= p) (hq : 0 <= q) : ENNReal.ofReal p = ENNReal.ofReal q ↔ p = q
· 使用定理 `sub_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddRight
Mono α] {a b : α}, 0 ≤ a - b ↔ b ≤ a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `StieltjesFunction.mono`：mono : Monotone f
-/
lemma eq_of_measure_of_eq (g : StieltjesFunction R) {y : R}
    (hfg : f.measure = g.measure) (hy : f y = g y) :
    f = g := by
  ext x
  cases le_total x y with
  | inl hxy =>
    have hf := measure_Ioc f x y
    rw [hfg, measure_Ioc g x y, ENNReal.ofReal_eq_ofReal_iff, eq_comm, hy] at hf
    · simpa using hf
    · rw [sub_nonneg]
      exact g.mono hxy
    · rw [sub_nonneg]
      exact f.mono hxy
  | inr hxy =>
    have hf := measure_Ioc f y x
    rw [hfg, measure_Ioc g y x, ENNReal.ofReal_eq_ofReal_iff, eq_comm, hy] at hf
    · simpa using hf
    · rw [sub_nonneg]
      exact g.mono hxy
    · rw [sub_nonneg]
      exact f.mono hxy

@[simp]
/-
**StieltjesFunction.measure_const** 是 Mathlib 中的一个引理，位于命名空间 `StieltjesFunction`。
形式化陈述：measure_const (c : Real) : (StieltjesFunction.const R c).measure = 0
参数：c : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext_of_Icc`：ext_of_Icc {α : Type*} [TopologicalSpa
ce α] {_m : MeasurableSpace α} [SecondCountableTopology α] [LinearOrder α] [Orde
rTopology α] [CompactI…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `StieltjesFunction.measure_Icc`：measure_Icc (a b : R) : f.measure (Icc a 
b) = ofReal (f b - leftLim f a)
· 使用定理 `AddGroup.toOrderedSub`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LE
 α] [AddRightMono α], OrderedSub α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `ContinuousWithinAt.leftLim_eq`：ContinuousWithinAt.leftLim_eq [Topologica
lSpace α] [OrderTopology α] [T2Space β] {f : α -> β} {a : α} (hf : ContinuousWit
hinAt f (Iic a) a) …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `continuousWithinAt_const`：continuousWithinAt_const {b : β} {s : Set α} {
x : α} : ContinuousWithinAt (fun _ : α => b) s x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
lemma measure_const (c : ℝ) : (StieltjesFunction.const R c).measure = 0 := by
  apply Measure.ext_of_Icc _ _ (fun a b hab ↦ ?_)
  simp only [measure_Icc, const_apply, Measure.coe_zero, Pi.ofNat_apply, ofReal_eq_zero,
    tsub_le_iff_right, zero_add]
  rw [ContinuousWithinAt.leftLim_eq]
  · simp
  · exact continuousWithinAt_const

@[simp]
/-
**StieltjesFunction.measure_zero** 是 Mathlib 中的一个引理，位于命名空间 `StieltjesFunction`。
形式化陈述：measure_zero : (0 : StieltjesFunction R).measure = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `StieltjesFunction.measure_const`：measure_const (c : Real) : (StieltjesFu
nction.const R c).measure = 0
-/
lemma measure_zero : (0 : StieltjesFunction R).measure = 0 := measure_const 0

@[simp]
/-
**StieltjesFunction.measure_add** 是 Mathlib 中的一个引理，位于命名空间 `StieltjesFunction`。
形式化陈述：measure_add (f g : StieltjesFunction R) : (f + g).measure = f.measure + g.
measure
参数：f g : StieltjesFunction R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext_of_Icc`：ext_of_Icc {α : Type*} [TopologicalSpa
ce α] {_m : MeasurableSpace α} [SecondCountableTopology α] [LinearOrder α] [Orde
rTopology α] [CompactI…
· 使用定理 `Filter.eq_or_neBot`：eq_or_neBot (f : Filter α) : f = ⊥ ∨ NeBot f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `leftLim_eq_of_eq_bot`：leftLim_eq_of_eq_bot [hα : TopologicalSpace α] [h'
α : OrderTopology α] (f : α -> β) {a : α} (h : 𝓝[<] a = ⊥) : leftLim f a = f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `tendsto_nhds_unique`：tendsto_nhds_unique [T2Space X] {f : Y -> X} {l : F
ilter Y} {a b : X} [NeBot l] (ha : Tendsto f l (𝓝 a)) (hb : Tendsto f l (𝓝 b)) :
 a = b
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Monotone.tendsto_leftLim`：tendsto_leftLim (x : α) : Tendsto f (𝓝[<] x) (
𝓝 (leftLim f x))
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `StieltjesFunction.mono`：mono : Monotone f
· 使用定理 `Filter.Tendsto.add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst_1
 : Add M] [ContinuousAdd M] {α : Type u_2} {f g : α → M}   {x : Filter α} {a b :
 M},   F…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `StieltjesFunction.measure_Icc`：measure_Icc (a b : R) : f.measure (Icc a 
b) = ofReal (f b - leftLim f a)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.ofReal_add`：ofReal_add {p q : Real} (hp : 0 <= p) (hq : 0 <= q) 
: ENNReal.ofReal (p + q) = ENNReal.ofReal p + ENNReal.ofReal q
· 使用定理 `sub_nonneg_of_le`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [Ad
dRightMono α] {a b : α}, b ≤ a → 0 ≤ a - b
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Monotone.leftLim_le`：leftLim_le (h : x <= y) : leftLim f x <= f y
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
（共 49 条，此处仅展示前 30 条）
-/
lemma measure_add (f g : StieltjesFunction R) : (f + g).measure = f.measure + g.measure := by
  refine Measure.ext_of_Icc _ _ (fun a b h ↦ ?_)
  have : leftLim (f + g) a = leftLim f a + leftLim g a := by
    rcases Filter.eq_or_neBot (𝓝[<] a) with ha | ha
    · simp [leftLim_eq_of_eq_bot _ ha]
    · exact tendsto_nhds_unique ((f + g).mono.tendsto_leftLim a)
        ((f.mono.tendsto_leftLim a).add (g.mono.tendsto_leftLim a))
  simp only [measure_Icc, add_apply, Measure.coe_add, Pi.add_apply, this]
  rw [← ENNReal.ofReal_add (sub_nonneg_of_le (f.mono.leftLim_le h))
    (sub_nonneg_of_le (g.mono.leftLim_le h))]
  ring_nf

@[simp]
/-
**StieltjesFunction.measure_smul** 是 Mathlib 中的一个引理，位于命名空间 `StieltjesFunction`。
形式化陈述：measure_smul (c : Real>=0) (f : StieltjesFunction R) : (c • f).measure = c
 • f.measure
参数：c : Real>=0；f : StieltjesFunction R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext_of_Icc`：ext_of_Icc {α : Type*} [TopologicalSpa
ce α] {_m : MeasurableSpace α} [SecondCountableTopology α] [LinearOrder α] [Orde
rTopology α] [CompactI…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `StieltjesFunction.measure_Icc`：measure_Icc (a b : R) : f.measure (Icc a 
b) = ofReal (f b - leftLim f a)
· 使用定理 `Filter.eq_or_neBot`：eq_or_neBot (f : Filter α) : f = ⊥ ∨ NeBot f
· 使用定理 `leftLim_eq_of_eq_bot`：leftLim_eq_of_eq_bot [hα : TopologicalSpace α] [h'
α : OrderTopology α] (f : α -> β) {a : α} (h : 𝓝[<] a = ⊥) : leftLim f a = f a
· 使用定理 `tendsto_nhds_unique`：tendsto_nhds_unique [T2Space X] {f : Y -> X} {l : F
ilter Y} {a b : X} [NeBot l] (ha : Tendsto f l (𝓝 a)) (hb : Tendsto f l (𝓝 b)) :
 a = b
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Monotone.tendsto_leftLim`：tendsto_leftLim (x : α) : Tendsto f (𝓝[<] x) (
𝓝 (leftLim f x))
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `StieltjesFunction.mono`：mono : Monotone f
· 使用定理 `Filter.Tendsto.const_smul`：Filter.Tendsto.const_smul {f : β -> α} {l : F
ilter β} {a : α} (hf : Tendsto f l (𝓝 a)) (c : M) : Tendsto (fun x => c • f x) l
 (𝓝 (c • a))
· 使用定理 `SMulCommClass.continuousConstSMul`：∀ {R : Type u_6} {A : Type u_7} [inst
 : Monoid A] [inst_1 : SMul R A] [SMulCommClass R A A]   [inst_3 : TopologicalSp
ace A] [SeparatelyConti…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用定理 `ENNReal.ofReal_mul`：ofReal_mul {p q : Real} (hp : 0 <= p) : ENNReal.ofRe
al (p * q) = ENNReal.ofReal p * ENNReal.ofReal q
· 使用定理 `NNReal.zero_le_coe`：zero_le_coe {q : Real>=0} : 0 <= (q : Real)
· 使用定理 `ENNReal.ofReal_coe_nnreal`：∀ {p : NNReal}, ENNReal.ofReal ↑p = ↑p
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
-/
lemma measure_smul (c : ℝ≥0) (f : StieltjesFunction R) : (c • f).measure = c • f.measure := by
  refine Measure.ext_of_Icc _ _ (fun a b h ↦ ?_)
  simp only [measure_Icc, Measure.smul_apply]
  change ofReal (c * f b - leftLim (c • f) a) = c • ofReal (f b - leftLim f a)
  have : leftLim (c • f) a = c * leftLim f a := by
    rcases Filter.eq_or_neBot (𝓝[<] a) with ha | ha
    · simp [leftLim_eq_of_eq_bot _ ha]
      rfl
    · exact tendsto_nhds_unique ((c • f).mono.tendsto_leftLim a)
        ((f.mono.tendsto_leftLim a).const_smul c)
  rw [this, ← _root_.mul_sub, ENNReal.ofReal_mul zero_le_coe, ofReal_coe_nnreal, ← smul_eq_mul]
  rfl

end StieltjesFunction

