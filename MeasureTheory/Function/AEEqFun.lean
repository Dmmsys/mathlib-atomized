/-
Copyright (c) 2019 Johannes Hölzl, Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Zhouhang Zhou
-/
module

public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.Order.Filter.Germ.Basic
public import Mathlib.Topology.ContinuousMap.Algebra

/-!

# Almost everywhere equal functions

We build a space of equivalence classes of functions, where two functions are treated as identical
if they are almost everywhere equal. We form the set of equivalence classes under the relation of
being almost everywhere equal, which is sometimes known as the `L⁰` space.
To use this space as a basis for the `L^p` spaces and for the Bochner integral, we consider
equivalence classes of strongly measurable functions (or, equivalently, of almost everywhere
strongly measurable functions.)

See `Mathlib/MeasureTheory/Function/L1Space/AEEqFun.lean` for `L¹` space.

## Notation

* `α →ₘ[μ] β` is the type of `L⁰` space, where `α` is a measurable space, `β` is a topological
  space, and `μ` is a measure on `α`. `f : α →ₘ β` is a "function" in `L⁰`.
  In comments, `[f]` is also used to denote an `L⁰` function.

  `ₘ` can be typed as `\_m`. Sometimes it is shown as a box if font is missing.

## Main statements

* The linear structure of `L⁰` :
  Addition and scalar multiplication are defined on `L⁰` in the natural way, i.e.,
  `[f] + [g] := [f + g]`, `c • [f] := [c • f]`. So defined, `α →ₘ β` inherits the linear structure
  of `β`. For example, if `β` is a module, then `α →ₘ β` is a module over the same ring.

  See `mk_add_mk`, `neg_mk`, `mk_sub`, `smul_mk`,
  `coeFn_add`, `coeFn_neg`, `coeFn_sub`, `coeFn_smul`

* The order structure of `L⁰` :
  `≤` can be defined in a similar way: `[f] ≤ [g]` if `f a ≤ g a` for almost all `a` in domain.
  And `α →ₘ β` inherits the preorder and partial order of `β`.

  TODO: Define `sup` and `inf` on `L⁰` so that it forms a lattice. It seems that `β` must be a
  linear order, since otherwise `f ⊔ g` may not be a measurable function.

## Implementation notes

* `f.cast`:      To find a representative of `f : α →ₘ β`, use the coercion `(f : α → β)`, which
                 is implemented as `f.toFun`.
                 For each operation `op` in `L⁰`, there is a lemma called `coe_fn_op`,
                 characterizing, say, `(f op g : α → β)`.
* `AEEqFun.mk`:  To construct an `L⁰` function `α →ₘ β` from an almost everywhere strongly
                 measurable function `f : α → β`, use `ae_eq_fun.mk`
* `comp`:        Use `comp g f` to get `[g ∘ f]` from `g : β → γ` and `[f] : α →ₘ γ` when `g` is
                 continuous. Use `compMeasurable` if `g` is only measurable (this requires the
                 target space to be second countable).
* `comp₂`:       Use `comp₂ g f₁ f₂` to get `[fun a ↦ g (f₁ a) (f₂ a)]`.
                 For example, `[f + g]` is `comp₂ (+)`


## Tags

function space, almost everywhere equal, `L⁰`, ae_eq_fun

-/

@[expose] public section

-- Guard against import creep
assert_not_exists InnerProductSpace

noncomputable section

open Topology Set Filter TopologicalSpace ENNReal EMetric MeasureTheory Function

variable {α β γ δ : Type*} [MeasurableSpace α] {μ ν : Measure α}

namespace MeasureTheory

section MeasurableSpace

variable [TopologicalSpace β]
variable (β)

/-- The equivalence relation of being almost everywhere equal for almost everywhere strongly
measurable functions. -/
@[instance_reducible]
/-
**MeasureTheory.Measure.aeEqSetoid** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.Meas
ure`。
形式化陈述：{α : Type u_1} →   (β : Type u_2) →     [inst : MeasurableSpace α] →      
 [inst_1 : TopologicalSpace β] →         (μ : MeasureTheory.Measure α) → Setoid 
{ f // MeasureTheory.AEStronglyMeasurable f μ }
参数：β : Type u_2；μ : MeasureTheory.Measure α。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α

--- 原说明 ---
The equivalence relation of being almost everywhere equal for almost everywhere 
strongly
measurable functions.
-/
def Measure.aeEqSetoid (μ : Measure α) : Setoid { f : α → β // AEStronglyMeasurable f μ } :=
  ⟨fun f g => (f : α → β) =ᵐ[μ] g, fun {f} => ae_eq_refl f.val, fun {_ _} => ae_eq_symm,
    fun {_ _ _} => ae_eq_trans⟩

variable (α)

/-- The space of equivalence classes of almost everywhere strongly measurable functions, where two
strongly measurable functions are equivalent if they agree almost everywhere, i.e.,
they differ on a set of measure `0`. -/
/-
**MeasureTheory.AEEqFun** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：AEEqFun (μ : Measure α) : Type _
参数：μ : Measure α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The space of equivalence classes of almost everywhere strongly measurable functi
ons, where two
strongly measurable functions are equivalent if they agree almost everywhere, i.
e.,
they differ on a set of measure `0`.
-/
def AEEqFun (μ : Measure α) : Type _ :=
  Quotient (μ.aeEqSetoid β)

variable {α β}

@[inherit_doc MeasureTheory.AEEqFun]
notation:25 α " →ₘ[" μ "] " β => AEEqFun α β μ

end MeasurableSpace

variable [TopologicalSpace δ]

namespace AEEqFun

section
variable [TopologicalSpace β]

/-- Construct the equivalence class `[f]` of an almost everywhere measurable function `f`, based
on the equivalence relation of being almost everywhere equal. -/
/-
**MeasureTheory.AEEqFun.mk** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.AEEqFun`。
形式化陈述：mk {β : Type*} [TopologicalSpace β] (f : α -> β) (hf : AEStronglyMeasurabl
e f μ) : α ->ₘ[μ] β
参数：f : α -> β；hf : AEStronglyMeasurable f μ。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)

--- 原说明 ---
Construct the equivalence class `[f]` of an almost everywhere measurable functio
n `f`, based
on the equivalence relation of being almost everywhere equal.
-/
def mk {β : Type*} [TopologicalSpace β] (f : α → β) (hf : AEStronglyMeasurable f μ) : α →ₘ[μ] β :=
  Quotient.mk'' ⟨f, hf⟩

open scoped Classical in
/-- Coercion from a space of equivalence classes of almost everywhere strongly measurable
functions to functions. We ensure that if `f` has a constant representative,
then we choose that one. -/
@[coe]
/-
**MeasureTheory.AEEqFun.cast** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.AEEqFun`。
形式化陈述：cast (f : α ->ₘ[μ] β) : α -> β
参数：f : α ->ₘ[μ] β。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.aestronglyMeasurable_const`：aestronglyMeasurable_const {b 
: β} : AEStronglyMeasurable[m] (fun _ : α => b) μ

--- 原说明 ---
Coercion from a space of equivalence classes of almost everywhere strongly measu
rable
functions to functions. We ensure that if `f` has a constant representative,
then we choose that one.
-/
def cast (f : α →ₘ[μ] β) : α → β :=
  if h : ∃ (b : β), f = mk (const α b) aestronglyMeasurable_const then
    const α <| Classical.choose h else
    AEStronglyMeasurable.mk _ (Quotient.out f : { f : α → β // AEStronglyMeasurable f μ }).2

/-- A measurable representative of an `AEEqFun` [f] -/
/-
**MeasureTheory.AEEqFun.instCoeFun** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.AEEq
Fun`。
形式化陈述：instCoeFun : CoeFun (α ->ₘ[μ] β) fun _ => α -> β
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A measurable representative of an `AEEqFun` [f]
-/
instance instCoeFun : CoeFun (α →ₘ[μ] β) fun _ => α → β := ⟨cast⟩

@[fun_prop]
/-
**MeasureTheory.AEEqFun.stronglyMeasurable** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.AEEqFun`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : MeasurableSpace α] {μ : MeasureThe
ory.Measure α} [inst_1 : TopologicalSpace β]   (f : α →ₘ[μ] β), MeasureTheory.St
ronglyMeasurable ↑f
参数：f : α →ₘ[μ] β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.aestronglyMeasurable_const`：aestronglyMeasurable_const {b 
: β} : AEStronglyMeasurable[m] (fun _ : α => b) μ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `MeasureTheory.stronglyMeasurable_const`：stronglyMeasurable_const {b : β}
 : StronglyMeasurable fun _ : α => b
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用引理 `MeasureTheory.AEStronglyMeasurable.stronglyMeasurable_mk`：stronglyMeasur
able_mk (hf : AEStronglyMeasurable[m] f μ) : StronglyMeasurable[m] (hf.mk f)
-/
protected theorem stronglyMeasurable (f : α →ₘ[μ] β) : StronglyMeasurable f := by
  simp only [cast]
  split_ifs with h
  · exact stronglyMeasurable_const
  · apply AEStronglyMeasurable.stronglyMeasurable_mk

@[fun_prop]
/-
**MeasureTheory.AEEqFun.aestronglyMeasurable** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.AEEqFun`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : MeasurableSpace α] {μ : MeasureThe
ory.Measure α} [inst_1 : TopologicalSpace β]   (f : α →ₘ[μ] β), MeasureTheory.AE
StronglyMeasurable (↑f) μ
参数：f : α →ₘ[μ] β；↑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.StronglyMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} 
{β : Type u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : Measu
reTheory.Measure α}   {f : α → β}, MeasureT…
· 使用定理 `MeasureTheory.AEEqFun.stronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2
} [inst : MeasurableSpace α] {μ : MeasureTheory.Measure α} [inst_1 : Topological
Space β]   (f : α →ₘ[μ] β), Me…
-/
protected theorem aestronglyMeasurable (f : α →ₘ[μ] β) : AEStronglyMeasurable f μ :=
  f.stronglyMeasurable.aestronglyMeasurable

@[fun_prop]
/-
**MeasureTheory.AEEqFun.measurable** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.AEEq
Fun`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : MeasurableSpace α] {μ : MeasureThe
ory.Measure α} [inst_1 : TopologicalSpace β]   [TopologicalSpace.PseudoMetrizabl
eSpace β] [inst_3 : MeasurableSpace β] [BorelSpace β] (f : α →ₘ[μ] β), Measurabl
e ↑f
参数：f : α →ₘ[μ] β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.StronglyMeasurable.measurable`：∀ {α : Type u_1} {β : Type 
u_2} {f : α → β} {x : MeasurableSpace α} [inst : TopologicalSpace β]   [Topologi
calSpace.PseudoMetrizableSpace β]…
· 使用定理 `MeasureTheory.AEEqFun.stronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2
} [inst : MeasurableSpace α] {μ : MeasureTheory.Measure α} [inst_1 : Topological
Space β]   (f : α →ₘ[μ] β), Me…
-/
protected theorem measurable [PseudoMetrizableSpace β] [MeasurableSpace β] [BorelSpace β]
    (f : α →ₘ[μ] β) : Measurable f :=
  f.stronglyMeasurable.measurable

@[fun_prop]
/-
**MeasureTheory.AEEqFun.aemeasurable** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.AE
EqFun`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : MeasurableSpace α] {μ : MeasureThe
ory.Measure α} [inst_1 : TopologicalSpace β]   [TopologicalSpace.PseudoMetrizabl
eSpace β] [inst_3 : MeasurableSpace β] [BorelSpace β] (f : α →ₘ[μ] β),   AEMeasu
rable (↑f) μ
参数：f : α →ₘ[μ] β；↑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `MeasureTheory.AEEqFun.measurable`：∀ {α : Type u_1} {β : Type u_2} [inst 
: MeasurableSpace α] {μ : MeasureTheory.Measure α} [inst_1 : TopologicalSpace β]
   [TopologicalSpace.P…
-/
protected theorem aemeasurable [PseudoMetrizableSpace β] [MeasurableSpace β] [BorelSpace β]
    (f : α →ₘ[μ] β) : AEMeasurable f μ :=
  f.measurable.aemeasurable

@[simp]
/-
**MeasureTheory.AEEqFun.quot_mk_eq_mk** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.A
EEqFun`。
形式化陈述：quot_mk_eq_mk (f : α -> β) (hf) : (Quot.mk (@Setoid.r _ <| μ.aeEqSetoid β)
 ⟨f, hf⟩ : α ->ₘ[μ] β) = mk f hf
参数：f : α -> β；hf。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem quot_mk_eq_mk (f : α → β) (hf) :
    (Quot.mk (@Setoid.r _ <| μ.aeEqSetoid β) ⟨f, hf⟩ : α →ₘ[μ] β) = mk f hf :=
  rfl

@[simp]
/-
**MeasureTheory.AEEqFun.mk_eq_mk** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.AEEqFu
n`。
形式化陈述：mk_eq_mk {f g : α -> β} {hf hg} : (mk f hf : α ->ₘ[μ] β) = mk g hg ↔ f =ᵐ[
μ] g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.eq''`：∀ {α : Sort u_1} {s₁ : Setoid α} {a b : α}, Quotient.mk''
 a = Quotient.mk'' b ↔ s₁ a b
-/
theorem mk_eq_mk {f g : α → β} {hf hg} : (mk f hf : α →ₘ[μ] β) = mk g hg ↔ f =ᵐ[μ] g :=
  Quotient.eq''

@[simp]
/-
**MeasureTheory.AEEqFun.mk_coeFn** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.AEEqFu
n`。
形式化陈述：mk_coeFn (f : α ->ₘ[μ] β) : mk f f.aestronglyMeasurable = f
参数：f : α ->ₘ[μ] β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEEqFun.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u
_2} [inst : MeasurableSpace α] {μ : MeasureTheory.Measure α} [inst_1 : Topologic
alSpace β]   (f : α →ₘ[μ] β), Me…
· 使用定理 `MeasureTheory.aestronglyMeasurable_const`：aestronglyMeasurable_const {b 
: β} : AEStronglyMeasurable[m] (fun _ : α => b) μ
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.AEEqFun.mk.congr_simp`：∀ {α : Type u_1} [inst : Measurable
Space α] {μ : MeasureTheory.Measure α} {β : Type u_5} [inst_1 : TopologicalSpace
 β]   (f f_1 : α → β) (e_…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Quotient.out_eq'`：out_eq' (q : Quotient s₁) : Quotient.mk'' q.out = q
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `MeasureTheory.AEEqFun.mk.eq_1`：∀ {α : Type u_1} [inst : MeasurableSpace 
α] {μ : MeasureTheory.Measure α} {β : Type u_5} [inst_1 : TopologicalSpace β]   
(f : α → β) (hf : M…
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.AEEqFun.mk_eq_mk`：mk_eq_mk {f g : α -> β} {hf hg} : (mk f 
hf : α ->ₘ[μ] β) = mk g hg ↔ f =ᵐ[μ] g
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `MeasureTheory.AEStronglyMeasurable.ae_eq_mk`：ae_eq_mk (hf : AEStronglyMe
asurable[m] f μ) : f =ᵐ[μ] hf.mk f
-/
theorem mk_coeFn (f : α →ₘ[μ] β) : mk f f.aestronglyMeasurable = f := by
  conv_lhs => simp only [cast]
  split_ifs with h
  · exact Classical.choose_spec h |>.symm
  conv_rhs => rw [← Quotient.out_eq' f]
  rw [← mk, mk_eq_mk]
  exact (AEStronglyMeasurable.ae_eq_mk _).symm

@[ext]
/-
**MeasureTheory.AEEqFun.ext** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.AEEqFun`。
形式化陈述：ext {f g : α ->ₘ[μ] β} (h : f =ᵐ[μ] g) : f = g
参数：h : f =ᵐ[μ] g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.AEEqFun.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u
_2} [inst : MeasurableSpace α] {μ : MeasureTheory.Measure α} [inst_1 : Topologic
alSpace β]   (f : α →ₘ[μ] β), Me…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.AEEqFun.mk_coeFn`：mk_coeFn (f : α ->ₘ[μ] β) : mk f f.aestr
onglyMeasurable = f
· 使用定理 `MeasureTheory.AEEqFun.mk_eq_mk`：mk_eq_mk {f g : α -> β} {hf hg} : (mk f 
hf : α ->ₘ[μ] β) = mk g hg ↔ f =ᵐ[μ] g
-/
theorem ext {f g : α →ₘ[μ] β} (h : f =ᵐ[μ] g) : f = g := by
  rwa [← f.mk_coeFn, ← g.mk_coeFn, mk_eq_mk]
/-
**MeasureTheory.AEEqFun.coeFn_mk** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.AEEqFu
n`。
形式化陈述：coeFn_mk (f : α -> β) (hf) : (mk f hf : α ->ₘ[μ] β) =ᵐ[μ] f
参数：f : α -> β；hf。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.AEEqFun.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u
_2} [inst : MeasurableSpace α] {μ : MeasureTheory.Measure α} [inst_1 : Topologic
alSpace β]   (f : α →ₘ[μ] β), Me…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.AEEqFun.mk_eq_mk`：mk_eq_mk {f g : α -> β} {hf hg} : (mk f 
hf : α ->ₘ[μ] β) = mk g hg ↔ f =ᵐ[μ] g
· 使用定理 `MeasureTheory.AEEqFun.mk_coeFn`：mk_coeFn (f : α ->ₘ[μ] β) : mk f f.aestr
onglyMeasurable = f
-/
theorem coeFn_mk (f : α → β) (hf) : (mk f hf : α →ₘ[μ] β) =ᵐ[μ] f := by
  rw [← mk_eq_mk (hf := AEEqFun.aestronglyMeasurable ..) (hg := hf), mk_coeFn]

@[elab_as_elim]
/-
**MeasureTheory.AEEqFun.induction_on** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.AE
EqFun`。
形式化陈述：induction_on (f : α ->ₘ[μ] β) {p : (α ->ₘ[μ] β) -> Prop} (H : forall f hf,
 p (mk f hf)) : p f
参数：f : α ->ₘ[μ] β；α ->ₘ[μ] β；H : forall f hf, p (mk f hf)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn'`：∀ {α : Sort u_1} {s₁ : Setoid α} {p : Quotient s₁
 → Prop} (q : Quotient s₁), (∀ (a : α), p (Quotient.mk'' a)) → p q
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
· 使用定理 `Subtype.forall`：∀ {α : Sort u} {p : α → Prop} {q : { a // p a } → Prop},
 (∀ (x : { a // p a }), q x) ↔ ∀ (a : α) (b : p a), q ⟨a, b⟩
-/
theorem induction_on (f : α →ₘ[μ] β) {p : (α →ₘ[μ] β) → Prop} (H : ∀ f hf, p (mk f hf)) : p f :=
  Quotient.inductionOn' f <| Subtype.forall.2 H

@[elab_as_elim]
/-
**MeasureTheory.AEEqFun.induction_on** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.AE
EqFun`。
形式化陈述：induction_on (f : α ->ₘ[μ] β) {p : (α ->ₘ[μ] β) -> Prop} (H : forall f hf,
 p (mk f hf)) : p f
参数：f : α ->ₘ[μ] β；α ->ₘ[μ] β；H : forall f hf, p (mk f hf)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn'`：∀ {α : Sort u_1} {s₁ : Setoid α} {p : Quotient s₁
 → Prop} (q : Quotient s₁), (∀ (a : α), p (Quotient.mk'' a)) → p q
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
· 使用定理 `Subtype.forall`：∀ {α : Sort u} {p : α → Prop} {q : { a // p a } → Prop},
 (∀ (x : { a // p a }), q x) ↔ ∀ (a : α) (b : p a), q ⟨a, b⟩
-/
theorem induction_on₂ {α' β' : Type*} [MeasurableSpace α'] [TopologicalSpace β'] {μ' : Measure α'}
    (f : α →ₘ[μ] β) (f' : α' →ₘ[μ'] β') {p : (α →ₘ[μ] β) → (α' →ₘ[μ'] β') → Prop}
    (H : ∀ f hf f' hf', p (mk f hf) (mk f' hf')) : p f f' :=
  induction_on f fun f hf => induction_on f' <| H f hf

@[elab_as_elim]
/-
**MeasureTheory.AEEqFun.induction_on** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.AE
EqFun`。
形式化陈述：induction_on (f : α ->ₘ[μ] β) {p : (α ->ₘ[μ] β) -> Prop} (H : forall f hf,
 p (mk f hf)) : p f
参数：f : α ->ₘ[μ] β；α ->ₘ[μ] β；H : forall f hf, p (mk f hf)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn'`：∀ {α : Sort u_1} {s₁ : Setoid α} {p : Quotient s₁
 → Prop} (q : Quotient s₁), (∀ (a : α), p (Quotient.mk'' a)) → p q
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
· 使用定理 `Subtype.forall`：∀ {α : Sort u} {p : α → Prop} {q : { a // p a } → Prop},
 (∀ (x : { a // p a }), q x) ↔ ∀ (a : α) (b : p a), q ⟨a, b⟩
-/
theorem induction_on₃ {α' β' : Type*} [MeasurableSpace α'] [TopologicalSpace β'] {μ' : Measure α'}
    {α'' β'' : Type*} [MeasurableSpace α''] [TopologicalSpace β''] {μ'' : Measure α''}
    (f : α →ₘ[μ] β) (f' : α' →ₘ[μ'] β') (f'' : α'' →ₘ[μ''] β'')
    {p : (α →ₘ[μ] β) → (α' →ₘ[μ'] β') → (α'' →ₘ[μ''] β'') → Prop}
    (H : ∀ f hf f' hf' f'' hf'', p (mk f hf) (mk f' hf') (mk f'' hf'')) : p f f' f'' :=
  induction_on f fun f hf => induction_on₂ f' f'' <| H f hf

end

/-!
### Composition of an a.e. equal function with a (quasi-)measure-preserving function
-/

section compQuasiMeasurePreserving

variable [TopologicalSpace γ] [MeasurableSpace β] {ν : MeasureTheory.Measure β} {f : α → β}

open MeasureTheory.Measure (QuasiMeasurePreserving)

/-- Composition of an almost everywhere equal function and a quasi-measure-preserving function.

See also `AEEqFun.compMeasurePreserving`. -/
/-
**MeasureTheory.AEEqFun.compQuasiMeasurePreserving** 是 Mathlib 中的一个定义，位于命名空间 `Me
asureTheory.AEEqFun`。
形式化陈述：compQuasiMeasurePreserving (g : β ->ₘ[ν] γ) (f : α -> β) (hf : QuasiMeasur
ePreserving f μ ν) : α ->ₘ[μ] γ
参数：g : β ->ₘ[ν] γ；f : α -> β；hf : QuasiMeasurePreserving f μ ν。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of an almost everywhere equal function and a quasi-measure-preservin
g function.

See also `AEEqFun.compMeasurePreserving`.
-/
def compQuasiMeasurePreserving (g : β →ₘ[ν] γ) (f : α → β) (hf : QuasiMeasurePreserving f μ ν) :
    α →ₘ[μ] γ :=
  Quotient.liftOn' g (fun g ↦ mk (g ∘ f) <| g.2.comp_quasiMeasurePreserving hf) fun _ _ h ↦
    mk_eq_mk.2 <| h.comp_tendsto hf.tendsto_ae

@[simp]
/-
**MeasureTheory.AEEqFun.compQuasiMeasurePreserving_mk** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory.AEEqFun`。
形式化陈述：compQuasiMeasurePreserving_mk {g : β -> γ} (hg : AEStronglyMeasurable g ν)
 (hf : QuasiMeasurePreserving f μ ν) : (mk g hg).compQuasiMeasurePreserving f hf
 = mk (g ∘ f) (hg.comp_quasiMeasurePreserving hf)
参数：hg : AEStronglyMeasurable g ν；hf : QuasiMeasurePreserving f μ ν。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem compQuasiMeasurePreserving_mk {g : β → γ} (hg : AEStronglyMeasurable g ν)
    (hf : QuasiMeasurePreserving f μ ν) :
    (mk g hg).compQuasiMeasurePreserving f hf = mk (g ∘ f) (hg.comp_quasiMeasurePreserving hf) :=
  rfl
/-
**MeasureTheory.AEEqFun.compQuasiMeasurePreserving_eq_mk** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory.AEEqFun`。
形式化陈述：compQuasiMeasurePreserving_eq_mk (g : β ->ₘ[ν] γ) (hf : QuasiMeasurePreser
ving f μ ν) : g.compQuasiMeasurePreserving f hf = mk (g ∘ f) (g.aestronglyMeasur
able.comp_quasiMeasurePreserving hf)
参数：g : β ->ₘ[ν] γ；hf : QuasiMeasurePreserving f μ ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEStronglyMeasurable.comp_quasiMeasurePreserving`：comp_qua
siMeasurePreserving {γ : Type*} {_ : MeasurableSpace γ} {_ : MeasurableSpace α} 
{f : γ -> α} {μ : Measure γ} {ν : Measure α} (hg : A…
· 使用定理 `MeasureTheory.AEEqFun.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u
_2} [inst : MeasurableSpace α] {μ : MeasureTheory.Measure α} [inst_1 : Topologic
alSpace β]   (f : α →ₘ[μ] β), Me…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.AEEqFun.compQuasiMeasurePreserving_mk`：compQuasiMeasurePre
serving_mk {g : β -> γ} (hg : AEStronglyMeasurable g ν) (hf : QuasiMeasurePreser
ving f μ ν) : (mk g hg).compQuasiMeasureP…
· 使用定理 `MeasureTheory.AEEqFun.mk_coeFn`：mk_coeFn (f : α ->ₘ[μ] β) : mk f f.aestr
onglyMeasurable = f
-/
theorem compQuasiMeasurePreserving_eq_mk (g : β →ₘ[ν] γ) (hf : QuasiMeasurePreserving f μ ν) :
    g.compQuasiMeasurePreserving f hf =
      mk (g ∘ f) (g.aestronglyMeasurable.comp_quasiMeasurePreserving hf) := by
  rw [← compQuasiMeasurePreserving_mk g.aestronglyMeasurable hf, mk_coeFn]
/-
**MeasureTheory.AEEqFun.coeFn_compQuasiMeasurePreserving** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory.AEEqFun`。
形式化陈述：coeFn_compQuasiMeasurePreserving (g : β ->ₘ[ν] γ) (hf : QuasiMeasurePreser
ving f μ ν) : g.compQuasiMeasurePreserving f hf =ᵐ[μ] g ∘ f
参数：g : β ->ₘ[ν] γ；hf : QuasiMeasurePreserving f μ ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.AEStronglyMeasurable.comp_quasiMeasurePreserving`：comp_qua
siMeasurePreserving {γ : Type*} {_ : MeasurableSpace γ} {_ : MeasurableSpace α} 
{f : γ -> α} {μ : Measure γ} {ν : Measure α} (hg : A…
· 使用定理 `MeasureTheory.AEEqFun.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u
_2} [inst : MeasurableSpace α] {μ : MeasureTheory.Measure α} [inst_1 : Topologic
alSpace β]   (f : α →ₘ[μ] β), Me…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.AEEqFun.compQuasiMeasurePreserving_eq_mk`：compQuasiMeasure
Preserving_eq_mk (g : β ->ₘ[ν] γ) (hf : QuasiMeasurePreserving f μ ν) : g.compQu
asiMeasurePreserving f hf = mk (g ∘ f) (g.ae…
· 使用定理 `MeasureTheory.AEEqFun.coeFn_mk`：coeFn_mk (f : α -> β) (hf) : (mk f hf : 
α ->ₘ[μ] β) =ᵐ[μ] f
-/
theorem coeFn_compQuasiMeasurePreserving (g : β →ₘ[ν] γ) (hf : QuasiMeasurePreserving f μ ν) :
    g.compQuasiMeasurePreserving f hf =ᵐ[μ] g ∘ f := by
  rw [compQuasiMeasurePreserving_eq_mk]
  apply coeFn_mk
/-
**MeasureTheory.AEEqFun.compQuasiMeasurePreserving_congr** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory.AEEqFun`。
形式化陈述：compQuasiMeasurePreserving_congr (g : β ->ₘ[ν] γ) (hf : QuasiMeasurePreser
ving f μ ν) {f' : α -> β} (hf' : Measurable f') (h : f =ᵐ[μ] f') : compQuasiMeas
urePreserving g f hf = compQuasiMeasurePreserving g f' (hf.congr hf' h)
参数：g : β ->ₘ[ν] γ；hf : QuasiMeasurePreserving f μ ν；hf' : Measurable f'；h : f =ᵐ
[μ] f'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.AEEqFun.ext`：ext {f g : α ->ₘ[μ] β} (h : f =ᵐ[μ] g) : f = 
g
· 使用定理 `MeasureTheory.Measure.QuasiMeasurePreserving.congr`：∀ {α : Type u_1} {β 
: Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μa : MeasureTheor
y.Measure α}   {μb : MeasureTheory.Measu…
· 使用引理 `Mathlib.Tactic.GCongr.rel_imp_rel`：rel_imp_rel (h₁ : r c a) (h₂ : r b d)
 : r a b -> r c d
· 使用定理 `instIsTransOfTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [Trans r r r], I
sTrans α r
· 使用定理 `MeasureTheory.AEEqFun.coeFn_compQuasiMeasurePreserving`：coeFn_compQuasiM
easurePreserving (g : β ->ₘ[ν] γ) (hf : QuasiMeasurePreserving f μ ν) : g.compQu
asiMeasurePreserving f hf =ᵐ[μ] g ∘ f
· 使用定理 `Filter.EventuallyEq.refl`：∀ {α : Type u} {β : Type v} (l : Filter α) (f 
: α → β), f =ᶠ[l] f
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `Filter.EventuallyEq.fun_comp`：∀ {α : Type u} {β : Type v} {γ : Type w} {
f g : α → β} {l : Filter α}, f =ᶠ[l] g → ∀ (h : β → γ), h ∘ f =ᶠ[l] h ∘ g
-/
theorem compQuasiMeasurePreserving_congr (g : β →ₘ[ν] γ) (hf : QuasiMeasurePreserving f μ ν)
    {f' : α → β} (hf' : Measurable f') (h : f =ᵐ[μ] f') :
    compQuasiMeasurePreserving g f hf = compQuasiMeasurePreserving g f' (hf.congr hf' h) := by
  ext
  grw [coeFn_compQuasiMeasurePreserving, coeFn_compQuasiMeasurePreserving, h]

@[simp]
/-
**MeasureTheory.AEEqFun.compQuasiMeasurePreserving_id** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory.AEEqFun`。
形式化陈述：compQuasiMeasurePreserving_id (g : β ->ₘ[ν] γ) : compQuasiMeasurePreservin
g g id (.id ν) = g
参数：g : β ->ₘ[ν] γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEEqFun.ext`：ext {f g : α ->ₘ[μ] β} (h : f =ᵐ[μ] g) : f = 
g
· 使用定理 `MeasureTheory.Measure.QuasiMeasurePreserving.id`：∀ {α : Type u_1} {_m0 :
 MeasurableSpace α} (μ : MeasureTheory.Measure α),   MeasureTheory.Measure.Quasi
MeasurePreserving id μ μ
· 使用定理 `MeasureTheory.AEEqFun.coeFn_compQuasiMeasurePreserving`：coeFn_compQuasiM
easurePreserving (g : β ->ₘ[ν] γ) (hf : QuasiMeasurePreserving f μ ν) : g.compQu
asiMeasurePreserving f hf =ᵐ[μ] g ∘ f
-/
theorem compQuasiMeasurePreserving_id (g : β →ₘ[ν] γ) :
    compQuasiMeasurePreserving g id (.id ν) = g := by
  ext
  exact coeFn_compQuasiMeasurePreserving _ _
/-
**MeasureTheory.AEEqFun.compQuasiMeasurePreserving_comp** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory.AEEqFun`。
形式化陈述：compQuasiMeasurePreserving_comp {γ : Type*} {mγ : MeasurableSpace γ} {ξ : 
Measure γ} (g : γ ->ₘ[ξ] δ) {f : β -> γ} (hf : QuasiMeasurePreserving f ν ξ) {f'
 : α -> β} (hf' : QuasiMeasurePreserving f' μ ν) : compQuasiMeasurePreserving g 
(f ∘ f') (hf.comp hf') = compQuasiMeasurePreserving (compQuasiMeasurePreserving 
g f hf) f' hf'
参数：g : γ ->ₘ[ξ] δ；hf : QuasiMeasurePreserving f ν ξ；hf' : QuasiMeasurePreserving
 f' μ ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEEqFun.ext`：ext {f g : α ->ₘ[μ] β} (h : f =ᵐ[μ] g) : f = 
g
· 使用定理 `MeasureTheory.Measure.QuasiMeasurePreserving.comp`：∀ {α : Type u_1} {β :
 Type u_2} {γ : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {m
γ : MeasurableSpace γ} {μa : MeasureThe…
· 使用引理 `Mathlib.Tactic.GCongr.rel_imp_rel`：rel_imp_rel (h₁ : r c a) (h₂ : r b d)
 : r a b -> r c d
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `instIsTransOfTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [Trans r r r], I
sTrans α r
· 使用定理 `MeasureTheory.AEEqFun.coeFn_compQuasiMeasurePreserving`：coeFn_compQuasiM
easurePreserving (g : β ->ₘ[ν] γ) (hf : QuasiMeasurePreserving f μ ν) : g.compQu
asiMeasurePreserving f hf =ᵐ[μ] g ∘ f
· 使用定理 `Filter.EventuallyEq.refl`：∀ {α : Type u} {β : Type v} (l : Filter α) (f 
: α → β), f =ᶠ[l] f
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `MeasureTheory.Measure.QuasiMeasurePreserving.ae_eq`：ae_eq (h : QuasiMeas
urePreserving f μa μb) {g₁ g₂ : β -> δ} (hg : g₁ =ᵐ[μb] g₂) : g₁ ∘ f =ᵐ[μa] g₂ ∘
 f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.comp_assoc`：comp_assoc (f : φ -> δ) (g : β -> φ) (h : α -> β) :
 (f ∘ g) ∘ h = f ∘ g ∘ h
-/
theorem compQuasiMeasurePreserving_comp {γ : Type*} {mγ : MeasurableSpace γ}
    {ξ : Measure γ} (g : γ →ₘ[ξ] δ) {f : β → γ} (hf : QuasiMeasurePreserving f ν ξ) {f' : α → β}
    (hf' : QuasiMeasurePreserving f' μ ν) :
    compQuasiMeasurePreserving g (f ∘ f') (hf.comp hf') =
    compQuasiMeasurePreserving (compQuasiMeasurePreserving g f hf) f' hf' := by
  ext
  grw [coeFn_compQuasiMeasurePreserving, coeFn_compQuasiMeasurePreserving,
    coeFn_compQuasiMeasurePreserving, comp_assoc]
/-
**MeasureTheory.AEEqFun.compQuasiMeasurePreserving_iterate** 是 Mathlib 中的一个定理，位于
命名空间 `MeasureTheory.AEEqFun`。
形式化陈述：compQuasiMeasurePreserving_iterate (g : α ->ₘ[μ] γ) {f : α -> α} (hf : Qua
siMeasurePreserving f μ μ) (n : Nat) : (compQuasiMeasurePreserving · f hf)^[n] g
 = compQuasiMeasurePreserving g (f^[n]) (hf.iterate n)
参数：g : α ->ₘ[μ] γ；hf : QuasiMeasurePreserving f μ μ；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.QuasiMeasurePreserving.iterate`：∀ {α : Type u_1} {
mα : MeasurableSpace α} {μa : MeasureTheory.Measure α} {f : α → α},   MeasureThe
ory.Measure.QuasiMeasurePreserving f μa μa…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.AEEqFun.compQuasiMeasurePreserving_id`：compQuasiMeasurePre
serving_id (g : β ->ₘ[ν] γ) : compQuasiMeasurePreserving g id (.id ν) = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `MeasureTheory.Measure.QuasiMeasurePreserving.comp`：∀ {α : Type u_1} {β :
 Type u_2} {γ : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}   {m
γ : MeasurableSpace γ} {μa : MeasureThe…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Function.iterate_add`：∀ {α : Type u} (f : α → α) (m n : ℕ), f^[m + n] = 
f^[m] ∘ f^[n]
· 使用定理 `Function.iterate_one`：iterate_one : f^[1] = f
· 使用定理 `MeasureTheory.AEEqFun.compQuasiMeasurePreserving.congr_simp`：∀ {α : Type
 u_1} {β : Type u_2} {γ : Type u_3} [inst : MeasurableSpace α] {μ : MeasureTheor
y.Measure α}   [inst_1 : TopologicalSpace γ] [ins…
-/
theorem compQuasiMeasurePreserving_iterate (g : α →ₘ[μ] γ) {f : α → α}
    (hf : QuasiMeasurePreserving f μ μ) (n : ℕ) :
    (compQuasiMeasurePreserving · f hf)^[n] g =
    compQuasiMeasurePreserving g (f^[n]) (hf.iterate n) := by
  induction n with
  | zero => simp
  | succ n hind =>
    nth_rewrite 1 [add_comm]
    simp [iterate_add, hind, ← compQuasiMeasurePreserving_comp]

end compQuasiMeasurePreserving

section compMeasurePreserving

variable [TopologicalSpace γ] [MeasurableSpace β] {ν : MeasureTheory.Measure β}
  {f : α → β} {g : β → γ}

/-- Composition of an almost everywhere equal function and a quasi-measure-preserving function.

This is an important special case of `AEEqFun.compQuasiMeasurePreserving`. We use a separate
definition so that lemmas that need `f` to be measure preserving can be `@[simp]` lemmas. -/
/-
**MeasureTheory.AEEqFun.compMeasurePreserving** 是 Mathlib 中的一个定义，位于命名空间 `Measure
Theory.AEEqFun`。
形式化陈述：compMeasurePreserving (g : β ->ₘ[ν] γ) (f : α -> β) (hf : MeasurePreservin
g f μ ν) : α ->ₘ[μ] γ
参数：g : β ->ₘ[ν] γ；f : α -> β；hf : MeasurePreserving f μ ν。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.MeasurePreserving.quasiMeasurePreserving`：∀ {α : Type u_1}
 {β : Type u_2} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {μa : Me
asureTheory.Measure α}   {μb : MeasureTheory…

--- 原说明 ---
Composition of an almost everywhere equal function and a quasi-measure-preservin
g function.

This is an important special case of `AEEqFun.compQuasiMeasurePreserving`. We us
e a separate
definition so that lemmas that need `f` to be measure preserving can be `@[simp]
` lemmas.
-/
def compMeasurePreserving (g : β →ₘ[ν] γ) (f : α → β) (hf : MeasurePreserving f μ ν) : α →ₘ[μ] γ :=
  g.compQuasiMeasurePreserving f hf.quasiMeasurePreserving

@[simp]
/-
**MeasureTheory.AEEqFun.compMeasurePreserving_mk** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.AEEqFun`。
形式化陈述：compMeasurePreserving_mk (hg : AEStronglyMeasurable g ν) (hf : MeasurePres
erving f μ ν) : (mk g hg).compMeasurePreserving f hf = mk (g ∘ f) (hg.comp_quasi
MeasurePreserving hf.quasiMeasurePreserving)
参数：hg : AEStronglyMeasurable g ν；hf : MeasurePreserving f μ ν。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem compMeasurePreserving_mk (hg : AEStronglyMeasurable g ν) (hf : MeasurePreserving f μ ν) :
    (mk g hg).compMeasurePreserving f hf =
      mk (g ∘ f) (hg.comp_quasiMeasurePreserving hf.quasiMeasurePreserving) :=
  rfl
/-
**MeasureTheory.AEEqFun.compMeasurePreserving_eq_mk** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory.AEEqFun`。
形式化陈述：compMeasurePreserving_eq_mk (g : β ->ₘ[ν] γ) (hf : MeasurePreserving f μ ν
) : g.compMeasurePreserving f hf = mk (g ∘ f) (g.aestronglyMeasurable.comp_quasi
MeasurePreserving hf.quasiMeasurePreserving)
参数：g : β ->ₘ[ν] γ；hf : MeasurePreserving f μ ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEEqFun.compQuasiMeasurePreserving_eq_mk`：compQuasiMeasure
Preserving_eq_mk (g : β ->ₘ[ν] γ) (hf : QuasiMeasurePreserving f μ ν) : g.compQu
asiMeasurePreserving f hf = mk (g ∘ f) (g.ae…
· 使用定理 `MeasureTheory.MeasurePreserving.quasiMeasurePreserving`：∀ {α : Type u_1}
 {β : Type u_2} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {μa : Me
asureTheory.Measure α}   {μb : MeasureTheory…
-/
theorem compMeasurePreserving_eq_mk (g : β →ₘ[ν] γ) (hf : MeasurePreserving f μ ν) :
    g.compMeasurePreserving f hf =
      mk (g ∘ f) (g.aestronglyMeasurable.comp_quasiMeasurePreserving hf.quasiMeasurePreserving) :=
  g.compQuasiMeasurePreserving_eq_mk _
/-
**MeasureTheory.AEEqFun.coeFn_compMeasurePreserving** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory.AEEqFun`。
形式化陈述：coeFn_compMeasurePreserving (g : β ->ₘ[ν] γ) (hf : MeasurePreserving f μ ν
) : g.compMeasurePreserving f hf =ᵐ[μ] g ∘ f
参数：g : β ->ₘ[ν] γ；hf : MeasurePreserving f μ ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEEqFun.coeFn_compQuasiMeasurePreserving`：coeFn_compQuasiM
easurePreserving (g : β ->ₘ[ν] γ) (hf : QuasiMeasurePreserving f μ ν) : g.compQu
asiMeasurePreserving f hf =ᵐ[μ] g ∘ f
· 使用定理 `MeasureTheory.MeasurePreserving.quasiMeasurePreserving`：∀ {α : Type u_1}
 {β : Type u_2} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {μa : Me
asureTheory.Measure α}   {μb : MeasureTheory…
-/
theorem coeFn_compMeasurePreserving (g : β →ₘ[ν] γ) (hf : MeasurePreserving f μ ν) :
    g.compMeasurePreserving f hf =ᵐ[μ] g ∘ f :=
  g.coeFn_compQuasiMeasurePreserving _
/-
**MeasureTheory.AEEqFun.compMeasurePreserving_congr** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory.AEEqFun`。
形式化陈述：compMeasurePreserving_congr (g : β ->ₘ[ν] γ) (hf : MeasurePreserving f μ ν
) {f' : α -> β} (hf' : Measurable f') (h : f =ᵐ[μ] f') : compMeasurePreserving g
 f hf = compMeasurePreserving g f' (hf.congr hf' h)
参数：g : β ->ₘ[ν] γ；hf : MeasurePreserving f μ ν；hf' : Measurable f'；h : f =ᵐ[μ] f
'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.AEEqFun.compQuasiMeasurePreserving_congr`：compQuasiMeasure
Preserving_congr (g : β ->ₘ[ν] γ) (hf : QuasiMeasurePreserving f μ ν) {f' : α ->
 β} (hf' : Measurable f') (h : f =ᵐ[μ] f') :…
· 使用定理 `MeasureTheory.MeasurePreserving.quasiMeasurePreserving`：∀ {α : Type u_1}
 {β : Type u_2} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {μa : Me
asureTheory.Measure α}   {μb : MeasureTheory…
-/
theorem compMeasurePreserving_congr (g : β →ₘ[ν] γ) (hf : MeasurePreserving f μ ν)
    {f' : α → β} (hf' : Measurable f') (h : f =ᵐ[μ] f') :
    compMeasurePreserving g f hf = compMeasurePreserving g f' (hf.congr hf' h) :=
  compQuasiMeasurePreserving_congr _ _ hf' h

@[simp]
/-
**MeasureTheory.AEEqFun.compMeasurePreserving_id** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.AEEqFun`。
形式化陈述：compMeasurePreserving_id (g : β ->ₘ[ν] γ) : compMeasurePreserving g id (.i
d ν) = g
参数：g : β ->ₘ[ν] γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEEqFun.compQuasiMeasurePreserving_id`：compQuasiMeasurePre
serving_id (g : β ->ₘ[ν] γ) : compQuasiMeasurePreserving g id (.id ν) = g
-/
theorem compMeasurePreserving_id (g : β →ₘ[ν] γ) :
    compMeasurePreserving g id (.id ν) = g :=
  compQuasiMeasurePreserving_id _
/-
**MeasureTheory.AEEqFun.compMeasurePreserving_comp** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory.AEEqFun`。
形式化陈述：compMeasurePreserving_comp {γ : Type*} {mγ : MeasurableSpace γ} {ξ : Measu
re γ} (g : γ ->ₘ[ξ] δ) {f : β -> γ} (hf : MeasurePreserving f ν ξ) {f' : α -> β}
 (hf' : MeasurePreserving f' μ ν) : compMeasurePreserving g (f ∘ f') (hf.comp hf
') = compMeasurePreserving (compMeasurePreserving g f hf) f' hf'
参数：g : γ ->ₘ[ξ] δ；hf : MeasurePreserving f ν ξ；hf' : MeasurePreserving f' μ ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEEqFun.compQuasiMeasurePreserving_comp`：compQuasiMeasureP
reserving_comp {γ : Type*} {mγ : MeasurableSpace γ} {ξ : Measure γ} (g : γ ->ₘ[ξ
] δ) {f : β -> γ} (hf : QuasiMeasurePreserv…
· 使用定理 `MeasureTheory.MeasurePreserving.quasiMeasurePreserving`：∀ {α : Type u_1}
 {β : Type u_2} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {μa : Me
asureTheory.Measure α}   {μb : MeasureTheory…
-/
theorem compMeasurePreserving_comp {γ : Type*} {mγ : MeasurableSpace γ}
    {ξ : Measure γ} (g : γ →ₘ[ξ] δ) {f : β → γ} (hf : MeasurePreserving f ν ξ) {f' : α → β}
    (hf' : MeasurePreserving f' μ ν) :
    compMeasurePreserving g (f ∘ f') (hf.comp hf') =
    compMeasurePreserving (compMeasurePreserving g f hf) f' hf' :=
  compQuasiMeasurePreserving_comp _ _ _
/-
**MeasureTheory.AEEqFun.compMeasurePreserving_iterate** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory.AEEqFun`。
形式化陈述：compMeasurePreserving_iterate (g : α ->ₘ[μ] γ) {f : α -> α} (hf : MeasureP
reserving f μ μ) (n : Nat) : (compMeasurePreserving · f hf)^[n] g = compMeasureP
reserving g (f^[n]) (hf.iterate n)
参数：g : α ->ₘ[μ] γ；hf : MeasurePreserving f μ μ；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEEqFun.compQuasiMeasurePreserving_iterate`：compQuasiMeasu
rePreserving_iterate (g : α ->ₘ[μ] γ) {f : α -> α} (hf : QuasiMeasurePreserving 
f μ μ) (n : Nat) : (compQuasiMeasurePreserving…
· 使用定理 `MeasureTheory.MeasurePreserving.quasiMeasurePreserving`：∀ {α : Type u_1}
 {β : Type u_2} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {μa : Me
asureTheory.Measure α}   {μb : MeasureTheory…
-/
theorem compMeasurePreserving_iterate (g : α →ₘ[μ] γ) {f : α → α}
    (hf : MeasurePreserving f μ μ) (n : ℕ) :
    (compMeasurePreserving · f hf)^[n] g = compMeasurePreserving g (f^[n]) (hf.iterate n) :=
  compQuasiMeasurePreserving_iterate _ _ _

end compMeasurePreserving

variable [TopologicalSpace β] [TopologicalSpace γ]

/-- Given a continuous function `g : β → γ`, and an almost everywhere equal function `[f] : α →ₘ β`,
return the equivalence class of `g ∘ f`, i.e., the almost everywhere equal function
`[g ∘ f] : α →ₘ γ`. -/
/-
**MeasureTheory.AEEqFun.comp** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.AEEqFun`。
形式化陈述：comp (g : β -> γ) (hg : Continuous g) (f : α ->ₘ[μ] β) : α ->ₘ[μ] γ
参数：g : β -> γ；hg : Continuous g；f : α ->ₘ[μ] β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a continuous function `g : β → γ`, and an almost everywhere equal function
 `[f] : α →ₘ β`,
return the equivalence class of `g ∘ f`, i.e., the almost everywhere equal funct
ion
`[g ∘ f] : α →ₘ γ`.
-/
def comp (g : β → γ) (hg : Continuous g) (f : α →ₘ[μ] β) : α →ₘ[μ] γ :=
  Quotient.liftOn' f (fun f => mk (g ∘ (f : α → β)) (hg.comp_aestronglyMeasurable f.2))
    fun _ _ H => mk_eq_mk.2 <| H.fun_comp g

@[simp]
/-
**MeasureTheory.AEEqFun.comp_mk** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.AEEqFun
`。
形式化陈述：comp_mk (g : β -> γ) (hg : Continuous g) (f : α -> β) (hf) : comp g hg (mk
 f hf : α ->ₘ[μ] β) = mk (g ∘ f) (hg.comp_aestronglyMeasurable hf)
参数：g : β -> γ；hg : Continuous g；f : α -> β；hf。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_mk (g : β → γ) (hg : Continuous g) (f : α → β) (hf) :
    comp g hg (mk f hf : α →ₘ[μ] β) = mk (g ∘ f) (hg.comp_aestronglyMeasurable hf) :=
  rfl

@[simp]
/-
**MeasureTheory.AEEqFun.comp_id** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.AEEqFun
`。
形式化陈述：comp_id (f : α ->ₘ[μ] β) : comp id (continuous_id) f = f
参数：f : α ->ₘ[μ] β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
-/
theorem comp_id (f : α →ₘ[μ] β) : comp id (continuous_id) f = f := by
  rcases f; rfl

@[simp]
/-
**MeasureTheory.AEEqFun.comp_comp** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.AEEqF
un`。
形式化陈述：comp_comp (g : γ -> δ) (g' : β -> γ) (hg : Continuous g) (hg' : Continuous
 g') (f : α ->ₘ[μ] β) : comp g hg (comp g' hg' f) = comp (g ∘ g') (hg.comp hg') 
f
参数：g : γ -> δ；g' : β -> γ；hg : Continuous g；hg' : Continuous g'；f : α ->ₘ[μ] β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
-/
theorem comp_comp (g : γ → δ) (g' : β → γ) (hg : Continuous g) (hg' : Continuous g')
    (f : α →ₘ[μ] β) : comp g hg (comp g' hg' f) = comp (g ∘ g') (hg.comp hg') f := by
  rcases f; rfl
/-
**MeasureTheory.AEEqFun.comp_eq_mk** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.AEEq
Fun`。
形式化陈述：comp_eq_mk (g : β -> γ) (hg : Continuous g) (f : α ->ₘ[μ] β) : comp g hg f
 = mk (g ∘ f) (hg.comp_aestronglyMeasurable f.aestronglyMeasurable)
参数：g : β -> γ；hg : Continuous g；f : α ->ₘ[μ] β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp_aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} [inst : TopologicalSpace β] [inst_1 : TopologicalSpace γ]   {m m₀ :
 MeasurableSpace α} {μ : M…
· 使用定理 `MeasureTheory.AEEqFun.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u
_2} [inst : MeasurableSpace α] {μ : MeasureTheory.Measure α} [inst_1 : Topologic
alSpace β]   (f : α →ₘ[μ] β), Me…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.AEEqFun.comp_mk`：comp_mk (g : β -> γ) (hg : Continuous g) 
(f : α -> β) (hf) : comp g hg (mk f hf : α ->ₘ[μ] β) = mk (g ∘ f) (hg.comp_aestr
onglyMeasurable hf)
· 使用定理 `MeasureTheory.AEEqFun.mk_coeFn`：mk_coeFn (f : α ->ₘ[μ] β) : mk f f.aestr
onglyMeasurable = f
-/
theorem comp_eq_mk (g : β → γ) (hg : Continuous g) (f : α →ₘ[μ] β) :
    comp g hg f = mk (g ∘ f) (hg.comp_aestronglyMeasurable f.aestronglyMeasurable) := by
  rw [← comp_mk g hg f f.aestronglyMeasurable, mk_coeFn]
/-
**MeasureTheory.AEEqFun.coeFn_comp** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.AEEq
Fun`。
形式化陈述：coeFn_comp (g : β -> γ) (hg : Continuous g) (f : α ->ₘ[μ] β) : comp g hg f
 =ᵐ[μ] g ∘ f
参数：g : β -> γ；hg : Continuous g；f : α ->ₘ[μ] β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Continuous.comp_aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} [inst : TopologicalSpace β] [inst_1 : TopologicalSpace γ]   {m m₀ :
 MeasurableSpace α} {μ : M…
· 使用定理 `MeasureTheory.AEEqFun.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u
_2} [inst : MeasurableSpace α] {μ : MeasureTheory.Measure α} [inst_1 : Topologic
alSpace β]   (f : α →ₘ[μ] β), Me…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.AEEqFun.comp_eq_mk`：comp_eq_mk (g : β -> γ) (hg : Continuo
us g) (f : α ->ₘ[μ] β) : comp g hg f = mk (g ∘ f) (hg.comp_aestronglyMeasurable 
f.aestronglyMeasurable…
· 使用定理 `MeasureTheory.AEEqFun.coeFn_mk`：coeFn_mk (f : α -> β) (hf) : (mk f hf : 
α ->ₘ[μ] β) =ᵐ[μ] f
-/
theorem coeFn_comp (g : β → γ) (hg : Continuous g) (f : α →ₘ[μ] β) : comp g hg f =ᵐ[μ] g ∘ f := by
  rw [comp_eq_mk]
  apply coeFn_mk
/-
**MeasureTheory.AEEqFun.comp_compQuasiMeasurePreserving** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory.AEEqFun`。
形式化陈述：comp_compQuasiMeasurePreserving {β : Type*} [MeasurableSpace β] {ν} (g : γ
 -> δ) (hg : Continuous g) (f : β ->ₘ[ν] γ) {φ : α -> β} (hφ : Measure.QuasiMeas
urePreserving φ μ ν) : (comp g hg f).compQuasiMeasurePreserving φ hφ = comp g hg
 (f.compQuasiMeasurePreserving φ hφ)
参数：g : γ -> δ；hg : Continuous g；f : β ->ₘ[ν] γ；hφ : Measure.QuasiMeasurePreservi
ng φ μ ν。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_compQuasiMeasurePreserving
    {β : Type*} [MeasurableSpace β] {ν} (g : γ → δ) (hg : Continuous g)
    (f : β →ₘ[ν] γ) {φ : α → β} (hφ : Measure.QuasiMeasurePreserving φ μ ν) :
    (comp g hg f).compQuasiMeasurePreserving φ hφ =
      comp g hg (f.compQuasiMeasurePreserving φ hφ) := by
  rcases f; rfl

section CompMeasurable

variable [MeasurableSpace β] [PseudoMetrizableSpace β] [BorelSpace β] [MeasurableSpace γ]
  [PseudoMetrizableSpace γ] [OpensMeasurableSpace γ] [SecondCountableTopology γ]

/-- Given a measurable function `g : β → γ`, and an almost everywhere equal function `[f] : α →ₘ β`,
return the equivalence class of `g ∘ f`, i.e., the almost everywhere equal function
`[g ∘ f] : α →ₘ γ`. This requires that `γ` has a second countable topology. -/
/-
**MeasureTheory.AEEqFun.compMeasurable** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.
AEEqFun`。
形式化陈述：compMeasurable (g : β -> γ) (hg : Measurable g) (f : α ->ₘ[μ] β) : α ->ₘ[μ
] γ
参数：g : β -> γ；hg : Measurable g；f : α ->ₘ[μ] β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a measurable function `g : β → γ`, and an almost everywhere equal function
 `[f] : α →ₘ β`,
return the equivalence class of `g ∘ f`, i.e., the almost everywhere equal funct
ion
`[g ∘ f] : α →ₘ γ`. This requires that `γ` has a second countable topology.
-/
def compMeasurable (g : β → γ) (hg : Measurable g) (f : α →ₘ[μ] β) : α →ₘ[μ] γ :=
  Quotient.liftOn' f
    (fun f' => mk (g ∘ (f' : α → β)) (hg.comp_aemeasurable f'.2.aemeasurable).aestronglyMeasurable)
    fun _ _ H => mk_eq_mk.2 <| H.fun_comp g

@[simp]
/-
**MeasureTheory.AEEqFun.compMeasurable_mk** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.AEEqFun`。
形式化陈述：compMeasurable_mk (g : β -> γ) (hg : Measurable g) (f : α -> β) (hf : AESt
ronglyMeasurable f μ) : compMeasurable g hg (mk f hf : α ->ₘ[μ] β) = mk (g ∘ f) 
(hg.comp_aemeasurable hf.aemeasurable).aestronglyMeasurable
参数：g : β -> γ；hg : Measurable g；f : α -> β；hf : AEStronglyMeasurable f μ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem compMeasurable_mk (g : β → γ) (hg : Measurable g) (f : α → β)
    (hf : AEStronglyMeasurable f μ) :
    compMeasurable g hg (mk f hf : α →ₘ[μ] β) =
      mk (g ∘ f) (hg.comp_aemeasurable hf.aemeasurable).aestronglyMeasurable :=
  rfl
/-
**MeasureTheory.AEEqFun.compMeasurable_eq_mk** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.AEEqFun`。
形式化陈述：compMeasurable_eq_mk (g : β -> γ) (hg : Measurable g) (f : α ->ₘ[μ] β) : c
ompMeasurable g hg f = mk (g ∘ f) (hg.comp_aemeasurable f.aemeasurable).aestrong
lyMeasurable
参数：g : β -> γ；hg : Measurable g；f : α ->ₘ[μ] β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AEMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst
 : TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   
{f : α → β} [inst_1 : M…
· 使用定理 `Measurable.comp_aemeasurable`：Measurable.comp_aemeasurable [MeasurableSp
ace δ] {f : α -> δ} {g : δ -> β} (hg : Measurable g) (hf : AEMeasurable f μ) : A
EMeasurable (g ∘ f…
· 使用定理 `MeasureTheory.AEEqFun.aemeasurable`：∀ {α : Type u_1} {β : Type u_2} [ins
t : MeasurableSpace α] {μ : MeasureTheory.Measure α} [inst_1 : TopologicalSpace 
β]   [TopologicalSpace.P…
· 使用定理 `MeasureTheory.AEEqFun.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u
_2} [inst : MeasurableSpace α] {μ : MeasureTheory.Measure α} [inst_1 : Topologic
alSpace β]   (f : α →ₘ[μ] β), Me…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.AEStronglyMeasurable.aemeasurable`：∀ {α : Type u_1} {m₀ : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} {β : Type u_5} [inst : Measurab
leSpace β]   [inst_1 : TopologicalSpa…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.AEEqFun.compMeasurable_mk`：compMeasurable_mk (g : β -> γ) 
(hg : Measurable g) (f : α -> β) (hf : AEStronglyMeasurable f μ) : compMeasurabl
e g hg (mk f hf : α ->ₘ[μ] β)…
· 使用定理 `MeasureTheory.AEEqFun.mk_coeFn`：mk_coeFn (f : α ->ₘ[μ] β) : mk f f.aestr
onglyMeasurable = f
-/
theorem compMeasurable_eq_mk (g : β → γ) (hg : Measurable g) (f : α →ₘ[μ] β) :
    compMeasurable g hg f =
    mk (g ∘ f) (hg.comp_aemeasurable f.aemeasurable).aestronglyMeasurable := by
  rw [← compMeasurable_mk g hg f f.aestronglyMeasurable, mk_coeFn]
/-
**MeasureTheory.AEEqFun.coeFn_compMeasurable** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.AEEqFun`。
形式化陈述：coeFn_compMeasurable (g : β -> γ) (hg : Measurable g) (f : α ->ₘ[μ] β) : c
ompMeasurable g hg f =ᵐ[μ] g ∘ f
参数：g : β -> γ；hg : Measurable g；f : α ->ₘ[μ] β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `AEMeasurable.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst
 : TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   
{f : α → β} [inst_1 : M…
· 使用定理 `Measurable.comp_aemeasurable`：Measurable.comp_aemeasurable [MeasurableSp
ace δ] {f : α -> δ} {g : δ -> β} (hg : Measurable g) (hf : AEMeasurable f μ) : A
EMeasurable (g ∘ f…
· 使用定理 `MeasureTheory.AEEqFun.aemeasurable`：∀ {α : Type u_1} {β : Type u_2} [ins
t : MeasurableSpace α] {μ : MeasureTheory.Measure α} [inst_1 : TopologicalSpace 
β]   [TopologicalSpace.P…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.AEEqFun.compMeasurable_eq_mk`：compMeasurable_eq_mk (g : β 
-> γ) (hg : Measurable g) (f : α ->ₘ[μ] β) : compMeasurable g hg f = mk (g ∘ f) 
(hg.comp_aemeasurable f.aemeasur…
· 使用定理 `MeasureTheory.AEEqFun.coeFn_mk`：coeFn_mk (f : α -> β) (hf) : (mk f hf : 
α ->ₘ[μ] β) =ᵐ[μ] f
-/
theorem coeFn_compMeasurable (g : β → γ) (hg : Measurable g) (f : α →ₘ[μ] β) :
    compMeasurable g hg f =ᵐ[μ] g ∘ f := by
  rw [compMeasurable_eq_mk]
  apply coeFn_mk

end CompMeasurable

/-- The class of `x ↦ (f x, g x)`. -/
/-
**MeasureTheory.AEEqFun.pair** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.AEEqFun`。
形式化陈述：pair (f : α ->ₘ[μ] β) (g : α ->ₘ[μ] γ) : α ->ₘ[μ] β × γ
参数：f : α ->ₘ[μ] β；g : α ->ₘ[μ] γ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The class of `x ↦ (f x, g x)`.
-/
def pair (f : α →ₘ[μ] β) (g : α →ₘ[μ] γ) : α →ₘ[μ] β × γ :=
  Quotient.liftOn₂' f g (fun f g => mk (fun x => (f.1 x, g.1 x)) (f.2.prodMk g.2))
    fun _f _g _f' _g' Hf Hg => mk_eq_mk.2 <| Hf.prodMk Hg

@[simp]
/-
**MeasureTheory.AEEqFun.pair_mk_mk** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.AEEq
Fun`。
形式化陈述：pair_mk_mk (f : α -> β) (hf) (g : α -> γ) (hg) : (mk f hf : α ->ₘ[μ] β).pa
ir (mk g hg) = mk (fun x => (f x, g x)) (hf.prodMk hg)
参数：f : α -> β；hf；g : α -> γ；hg。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pair_mk_mk (f : α → β) (hf) (g : α → γ) (hg) :
    (mk f hf : α →ₘ[μ] β).pair (mk g hg) = mk (fun x => (f x, g x)) (hf.prodMk hg) :=
  rfl
/-
**MeasureTheory.AEEqFun.pair_eq_mk** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.AEEq
Fun`。
形式化陈述：pair_eq_mk (f : α ->ₘ[μ] β) (g : α ->ₘ[μ] γ) : f.pair g = mk (fun x => (f 
x, g x)) (f.aestronglyMeasurable.prodMk g.aestronglyMeasurable)
参数：f : α ->ₘ[μ] β；g : α ->ₘ[μ] γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MeasureTheory.AEStronglyMeasurable.prodMk`：∀ {α : Type u_1} {β : Type u_
2} {γ : Type u_3} [inst : TopologicalSpace β] [inst_1 : TopologicalSpace γ]   {m
 m₀ : MeasurableSpace α} {μ : M…
· 使用定理 `MeasureTheory.AEEqFun.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u
_2} [inst : MeasurableSpace α] {μ : MeasureTheory.Measure α} [inst_1 : Topologic
alSpace β]   (f : α →ₘ[μ] β), Me…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.AEEqFun.mk_coeFn`：mk_coeFn (f : α ->ₘ[μ] β) : mk f f.aestr
onglyMeasurable = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pair_eq_mk (f : α →ₘ[μ] β) (g : α →ₘ[μ] γ) :
    f.pair g =
      mk (fun x => (f x, g x)) (f.aestronglyMeasurable.prodMk g.aestronglyMeasurable) := by
  simp only [← pair_mk_mk, mk_coeFn, f.aestronglyMeasurable, g.aestronglyMeasurable]
/-
**MeasureTheory.AEEqFun.coeFn_pair** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.AEEq
Fun`。
形式化陈述：coeFn_pair (f : α ->ₘ[μ] β) (g : α ->ₘ[μ] γ) : f.pair g =ᵐ[μ] fun x => (f 
x, g x)
参数：f : α ->ₘ[μ] β；g : α ->ₘ[μ] γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.AEStronglyMeasurable.prodMk`：∀ {α : Type u_1} {β : Type u_
2} {γ : Type u_3} [inst : TopologicalSpace β] [inst_1 : TopologicalSpace γ]   {m
 m₀ : MeasurableSpace α} {μ : M…
· 使用定理 `MeasureTheory.AEEqFun.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u
_2} [inst : MeasurableSpace α] {μ : MeasureTheory.Measure α} [inst_1 : Topologic
alSpace β]   (f : α →ₘ[μ] β), Me…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.AEEqFun.pair_eq_mk`：pair_eq_mk (f : α ->ₘ[μ] β) (g : α ->ₘ
[μ] γ) : f.pair g = mk (fun x => (f x, g x)) (f.aestronglyMeasurable.prodMk g.ae
stronglyMeasurable)
· 使用定理 `MeasureTheory.AEEqFun.coeFn_mk`：coeFn_mk (f : α -> β) (hf) : (mk f hf : 
α ->ₘ[μ] β) =ᵐ[μ] f
-/
theorem coeFn_pair (f : α →ₘ[μ] β) (g : α →ₘ[μ] γ) : f.pair g =ᵐ[μ] fun x => (f x, g x) := by
  rw [pair_eq_mk]
  apply coeFn_mk

/-- Given a continuous function `g : β → γ → δ`, and almost everywhere equal functions
`[f₁] : α →ₘ β` and `[f₂] : α →ₘ γ`, return the equivalence class of the function
`fun a => g (f₁ a) (f₂ a)`, i.e., the almost everywhere equal function
`[fun a => g (f₁ a) (f₂ a)] : α →ₘ γ` -/
/-
**MeasureTheory.AEEqFun.comp** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.AEEqFun`。
形式化陈述：comp (g : β -> γ) (hg : Continuous g) (f : α ->ₘ[μ] β) : α ->ₘ[μ] γ
参数：g : β -> γ；hg : Continuous g；f : α ->ₘ[μ] β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a continuous function `g : β → γ → δ`, and almost everywhere equal functio
ns
`[f₁] : α →ₘ β` and `[f₂] : α →ₘ γ`, return the equivalence class of the functio
n
`fun a => g (f₁ a) (f₂ a)`, i.e., the almost everywhere equal function
`[fun a => g (f₁ a) (f₂ a)] : α →ₘ γ`
-/
def comp₂ (g : β → γ → δ) (hg : Continuous (uncurry g)) (f₁ : α →ₘ[μ] β) (f₂ : α →ₘ[μ] γ) :
    α →ₘ[μ] δ :=
  comp _ hg (f₁.pair f₂)

@[simp]
/-
**MeasureTheory.AEEqFun.comp** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.AEEqFun`。
形式化陈述：comp (g : β -> γ) (hg : Continuous g) (f : α ->ₘ[μ] β) : α ->ₘ[μ] γ
参数：g : β -> γ；hg : Continuous g；f : α ->ₘ[μ] β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp₂_mk_mk (g : β → γ → δ) (hg : Continuous (uncurry g)) (f₁ : α → β) (f₂ : α → γ)
    (hf₁ hf₂) :
    comp₂ g hg (mk f₁ hf₁ : α →ₘ[μ] β) (mk f₂ hf₂) =
      mk (fun a => g (f₁ a) (f₂ a)) (hg.comp_aestronglyMeasurable (hf₁.prodMk hf₂)) :=
  rfl
/-
**MeasureTheory.AEEqFun.comp** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.AEEqFun`。
形式化陈述：comp (g : β -> γ) (hg : Continuous g) (f : α ->ₘ[μ] β) : α ->ₘ[μ] γ
参数：g : β -> γ；hg : Continuous g；f : α ->ₘ[μ] β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp₂_eq_pair (g : β → γ → δ) (hg : Continuous (uncurry g)) (f₁ : α →ₘ[μ] β)
    (f₂ : α →ₘ[μ] γ) : comp₂ g hg f₁ f₂ = comp _ hg (f₁.pair f₂) :=
  rfl
/-
**MeasureTheory.AEEqFun.comp** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.AEEqFun`。
形式化陈述：comp (g : β -> γ) (hg : Continuous g) (f : α ->ₘ[μ] β) : α ->ₘ[μ] γ
参数：g : β -> γ；hg : Continuous g；f : α ->ₘ[μ] β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp₂_eq_mk (g : β → γ → δ) (hg : Continuous (uncurry g)) (f₁ : α →ₘ[μ] β)
    (f₂ : α →ₘ[μ] γ) : comp₂ g hg f₁ f₂ = mk (fun a => g (f₁ a) (f₂ a))
      (hg.comp_aestronglyMeasurable (f₁.aestronglyMeasurable.prodMk f₂.aestronglyMeasurable)) := by
  rw [comp₂_eq_pair, pair_eq_mk, comp_mk]; rfl
/-
**MeasureTheory.AEEqFun.coeFn_comp** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.AEEq
Fun`。
形式化陈述：coeFn_comp (g : β -> γ) (hg : Continuous g) (f : α ->ₘ[μ] β) : comp g hg f
 =ᵐ[μ] g ∘ f
参数：g : β -> γ；hg : Continuous g；f : α ->ₘ[μ] β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Continuous.comp_aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} [inst : TopologicalSpace β] [inst_1 : TopologicalSpace γ]   {m m₀ :
 MeasurableSpace α} {μ : M…
· 使用定理 `MeasureTheory.AEEqFun.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u
_2} [inst : MeasurableSpace α] {μ : MeasureTheory.Measure α} [inst_1 : Topologic
alSpace β]   (f : α →ₘ[μ] β), Me…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.AEEqFun.comp_eq_mk`：comp_eq_mk (g : β -> γ) (hg : Continuo
us g) (f : α ->ₘ[μ] β) : comp g hg f = mk (g ∘ f) (hg.comp_aestronglyMeasurable 
f.aestronglyMeasurable…
· 使用定理 `MeasureTheory.AEEqFun.coeFn_mk`：coeFn_mk (f : α -> β) (hf) : (mk f hf : 
α ->ₘ[μ] β) =ᵐ[μ] f
-/
theorem coeFn_comp₂ (g : β → γ → δ) (hg : Continuous (uncurry g)) (f₁ : α →ₘ[μ] β)
    (f₂ : α →ₘ[μ] γ) : comp₂ g hg f₁ f₂ =ᵐ[μ] fun a => g (f₁ a) (f₂ a) := by
  rw [comp₂_eq_mk]
  apply coeFn_mk

section

variable [MeasurableSpace β] [PseudoMetrizableSpace β] [BorelSpace β]
  [MeasurableSpace γ] [PseudoMetrizableSpace γ] [BorelSpace γ] [SecondCountableTopologyEither β γ]
  [MeasurableSpace δ] [PseudoMetrizableSpace δ] [OpensMeasurableSpace δ] [SecondCountableTopology δ]

/-- Given a measurable function `g : β → γ → δ`, and almost everywhere equal functions
`[f₁] : α →ₘ β` and `[f₂] : α →ₘ γ`, return the equivalence class of the function
`fun a => g (f₁ a) (f₂ a)`, i.e., the almost everywhere equal function
`[fun a => g (f₁ a) (f₂ a)] : α →ₘ γ`. This requires `δ` to have second-countable topology. -/
/-
**MeasureTheory.AEEqFun.comp** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.AEEqFun`。
形式化陈述：comp (g : β -> γ) (hg : Continuous g) (f : α ->ₘ[μ] β) : α ->ₘ[μ] γ
参数：g : β -> γ；hg : Continuous g；f : α ->ₘ[μ] β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a measurable function `g : β → γ → δ`, and almost everywhere equal functio
ns
`[f₁] : α →ₘ β` and `[f₂] : α →ₘ γ`, return the equivalence class of the functio
n
`fun a => g (f₁ a) (f₂ a)`, i.e., the almost everywhere equal function
`[fun a => g (f₁ a) (f₂ a)] : α →ₘ γ`. This requires `δ` to have second-countabl
e topology.
-/
def comp₂Measurable (g : β → γ → δ) (hg : Measurable (uncurry g)) (f₁ : α →ₘ[μ] β)
    (f₂ : α →ₘ[μ] γ) : α →ₘ[μ] δ :=
  compMeasurable _ hg (f₁.pair f₂)

@[simp]
/-
**MeasureTheory.AEEqFun.comp** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.AEEqFun`。
形式化陈述：comp (g : β -> γ) (hg : Continuous g) (f : α ->ₘ[μ] β) : α ->ₘ[μ] γ
参数：g : β -> γ；hg : Continuous g；f : α ->ₘ[μ] β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp₂Measurable_mk_mk (g : β → γ → δ) (hg : Measurable (uncurry g)) (f₁ : α → β)
    (f₂ : α → γ) (hf₁ hf₂) :
    comp₂Measurable g hg (mk f₁ hf₁ : α →ₘ[μ] β) (mk f₂ hf₂) =
      mk (fun a => g (f₁ a) (f₂ a))
        (hg.comp_aemeasurable (hf₁.aemeasurable.prodMk hf₂.aemeasurable)).aestronglyMeasurable :=
  rfl
/-
**MeasureTheory.AEEqFun.comp** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.AEEqFun`。
形式化陈述：comp (g : β -> γ) (hg : Continuous g) (f : α ->ₘ[μ] β) : α ->ₘ[μ] γ
参数：g : β -> γ；hg : Continuous g；f : α ->ₘ[μ] β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp₂Measurable_eq_pair (g : β → γ → δ) (hg : Measurable (uncurry g)) (f₁ : α →ₘ[μ] β)
    (f₂ : α →ₘ[μ] γ) : comp₂Measurable g hg f₁ f₂ = compMeasurable _ hg (f₁.pair f₂) :=
  rfl
/-
**MeasureTheory.AEEqFun.comp** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.AEEqFun`。
形式化陈述：comp (g : β -> γ) (hg : Continuous g) (f : α ->ₘ[μ] β) : α ->ₘ[μ] γ
参数：g : β -> γ；hg : Continuous g；f : α ->ₘ[μ] β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp₂Measurable_eq_mk (g : β → γ → δ) (hg : Measurable (uncurry g)) (f₁ : α →ₘ[μ] β)
    (f₂ : α →ₘ[μ] γ) :
    comp₂Measurable g hg f₁ f₂ =
      mk (fun a => g (f₁ a) (f₂ a))
        (hg.comp_aemeasurable (f₁.aemeasurable.prodMk f₂.aemeasurable)).aestronglyMeasurable := by
  rw [comp₂Measurable_eq_pair, pair_eq_mk, compMeasurable_mk]; rfl
/-
**MeasureTheory.AEEqFun.coeFn_comp** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.AEEq
Fun`。
形式化陈述：coeFn_comp (g : β -> γ) (hg : Continuous g) (f : α ->ₘ[μ] β) : comp g hg f
 =ᵐ[μ] g ∘ f
参数：g : β -> γ；hg : Continuous g；f : α ->ₘ[μ] β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Continuous.comp_aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} [inst : TopologicalSpace β] [inst_1 : TopologicalSpace γ]   {m m₀ :
 MeasurableSpace α} {μ : M…
· 使用定理 `MeasureTheory.AEEqFun.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u
_2} [inst : MeasurableSpace α] {μ : MeasureTheory.Measure α} [inst_1 : Topologic
alSpace β]   (f : α →ₘ[μ] β), Me…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.AEEqFun.comp_eq_mk`：comp_eq_mk (g : β -> γ) (hg : Continuo
us g) (f : α ->ₘ[μ] β) : comp g hg f = mk (g ∘ f) (hg.comp_aestronglyMeasurable 
f.aestronglyMeasurable…
· 使用定理 `MeasureTheory.AEEqFun.coeFn_mk`：coeFn_mk (f : α -> β) (hf) : (mk f hf : 
α ->ₘ[μ] β) =ᵐ[μ] f
-/
theorem coeFn_comp₂Measurable (g : β → γ → δ) (hg : Measurable (uncurry g)) (f₁ : α →ₘ[μ] β)
    (f₂ : α →ₘ[μ] γ) : comp₂Measurable g hg f₁ f₂ =ᵐ[μ] fun a => g (f₁ a) (f₂ a) := by
  rw [comp₂Measurable_eq_mk]
  apply coeFn_mk

end

/-- Interpret `f : α →ₘ[μ] β` as a germ at `ae μ` forgetting that `f` is almost everywhere
strongly measurable. -/
/-
**MeasureTheory.AEEqFun.toGerm** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.AEEqFun`
。
形式化陈述：toGerm (f : α ->ₘ[μ] β) : Germ (ae μ) β
参数：f : α ->ₘ[μ] β。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α

--- 原说明 ---
Interpret `f : α →ₘ[μ] β` as a germ at `ae μ` forgetting that `f` is almost ever
ywhere
strongly measurable.
-/
def toGerm (f : α →ₘ[μ] β) : Germ (ae μ) β :=
  Quotient.liftOn' f (fun f => ((f : α → β) : Germ (ae μ) β)) fun _ _ H => Germ.coe_eq.2 H

@[simp]
/-
**MeasureTheory.AEEqFun.mk_toGerm** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.AEEqF
un`。
形式化陈述：mk_toGerm (f : α -> β) (hf) : (mk f hf : α ->ₘ[μ] β).toGerm = f
参数：f : α -> β；hf。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
-/
theorem mk_toGerm (f : α → β) (hf) : (mk f hf : α →ₘ[μ] β).toGerm = f :=
  rfl
/-
**MeasureTheory.AEEqFun.toGerm_eq** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.AEEqF
un`。
形式化陈述：toGerm_eq (f : α ->ₘ[μ] β) : f.toGerm = (f : α -> β)
参数：f : α ->ₘ[μ] β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.AEEqFun.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u
_2} [inst : MeasurableSpace α] {μ : MeasureTheory.Measure α} [inst_1 : Topologic
alSpace β]   (f : α →ₘ[μ] β), Me…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.AEEqFun.mk_toGerm`：mk_toGerm (f : α -> β) (hf) : (mk f hf 
: α ->ₘ[μ] β).toGerm = f
· 使用定理 `MeasureTheory.AEEqFun.mk_coeFn`：mk_coeFn (f : α ->ₘ[μ] β) : mk f f.aestr
onglyMeasurable = f
-/
theorem toGerm_eq (f : α →ₘ[μ] β) : f.toGerm = (f : α → β) := by
  rw [← mk_toGerm f f.aestronglyMeasurable, mk_coeFn]
/-
**MeasureTheory.AEEqFun.toGerm_injective** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.AEEqFun`。
形式化陈述：toGerm_injective : Injective (toGerm : (α ->ₘ[μ] β) -> Germ (ae μ) β)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.AEEqFun.ext`：ext {f g : α ->ₘ[μ] β} (h : f =ᵐ[μ] g) : f = 
g
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.Germ.coe_eq`：coe_eq : (f : Germ l β) = g ↔ f =ᶠ[l] g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.AEEqFun.toGerm_eq`：toGerm_eq (f : α ->ₘ[μ] β) : f.toGerm =
 (f : α -> β)
-/
theorem toGerm_injective : Injective (toGerm : (α →ₘ[μ] β) → Germ (ae μ) β) := fun f g H =>
  ext <| Germ.coe_eq.1 <| by rwa [← toGerm_eq, ← toGerm_eq]

@[simp]
/-
**MeasureTheory.AEEqFun.compQuasiMeasurePreserving_toGerm** 是 Mathlib 中的一个定理，位于命
名空间 `MeasureTheory.AEEqFun`。
形式化陈述：compQuasiMeasurePreserving_toGerm {β : Type*} [MeasurableSpace β] {f : α -
> β} {ν} (g : β ->ₘ[ν] γ) (hf : Measure.QuasiMeasurePreserving f μ ν) : (g.compQ
uasiMeasurePreserving f hf).toGerm = g.toGerm.compTendsto f hf.tendsto_ae
参数：g : β ->ₘ[ν] γ；hf : Measure.QuasiMeasurePreserving f μ ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Measure.QuasiMeasurePreserving.tendsto_ae`：tendsto_ae (h :
 QuasiMeasurePreserving f μa μb) : Tendsto f (ae μa) (ae μb)
-/
theorem compQuasiMeasurePreserving_toGerm {β : Type*} [MeasurableSpace β] {f : α → β} {ν}
    (g : β →ₘ[ν] γ) (hf : Measure.QuasiMeasurePreserving f μ ν) :
    (g.compQuasiMeasurePreserving f hf).toGerm = g.toGerm.compTendsto f hf.tendsto_ae := by
  rcases g; rfl

@[simp]
/-
**MeasureTheory.AEEqFun.compMeasurePreserving_toGerm** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory.AEEqFun`。
形式化陈述：compMeasurePreserving_toGerm {β : Type*} [MeasurableSpace β] {f : α -> β} 
{ν} (g : β ->ₘ[ν] γ) (hf : MeasurePreserving f μ ν) : (g.compMeasurePreserving f
 hf).toGerm = g.toGerm.compTendsto f hf.quasiMeasurePreserving.tendsto_ae
参数：g : β ->ₘ[ν] γ；hf : MeasurePreserving f μ ν。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEEqFun.compQuasiMeasurePreserving_toGerm`：compQuasiMeasur
ePreserving_toGerm {β : Type*} [MeasurableSpace β] {f : α -> β} {ν} (g : β ->ₘ[ν
] γ) (hf : Measure.QuasiMeasurePreserving f μ…
· 使用定理 `MeasureTheory.MeasurePreserving.quasiMeasurePreserving`：∀ {α : Type u_1}
 {β : Type u_2} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {μa : Me
asureTheory.Measure α}   {μb : MeasureTheory…
-/
theorem compMeasurePreserving_toGerm {β : Type*} [MeasurableSpace β] {f : α → β} {ν}
    (g : β →ₘ[ν] γ) (hf : MeasurePreserving f μ ν) :
    (g.compMeasurePreserving f hf).toGerm =
      g.toGerm.compTendsto f hf.quasiMeasurePreserving.tendsto_ae :=
  compQuasiMeasurePreserving_toGerm _ _
/-
**MeasureTheory.AEEqFun.comp_toGerm** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.AEE
qFun`。
形式化陈述：comp_toGerm (g : β -> γ) (hg : Continuous g) (f : α ->ₘ[μ] β) : (comp g hg
 f).toGerm = f.toGerm.map g
参数：g : β -> γ；hg : Continuous g；f : α ->ₘ[μ] β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEEqFun.induction_on`：induction_on (f : α ->ₘ[μ] β) {p : (
α ->ₘ[μ] β) -> Prop} (H : forall f hf, p (mk f hf)) : p f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem comp_toGerm (g : β → γ) (hg : Continuous g) (f : α →ₘ[μ] β) :
    (comp g hg f).toGerm = f.toGerm.map g :=
  induction_on f fun f _ => by simp
/-
**MeasureTheory.AEEqFun.compMeasurable_toGerm** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.AEEqFun`。
形式化陈述：compMeasurable_toGerm [MeasurableSpace β] [BorelSpace β] [PseudoMetrizable
Space β] [PseudoMetrizableSpace γ] [SecondCountableTopology γ] [MeasurableSpace 
γ] [OpensMeasurableSpace γ] (g : β -> γ) (hg : Measurable g) (f : α ->ₘ[μ] β) : 
(compMeasurable g hg f).toGerm = f.toGerm.map g
参数：g : β -> γ；hg : Measurable g；f : α ->ₘ[μ] β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEEqFun.induction_on`：induction_on (f : α ->ₘ[μ] β) {p : (
α ->ₘ[μ] β) -> Prop} (H : forall f hf, p (mk f hf)) : p f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem compMeasurable_toGerm [MeasurableSpace β] [BorelSpace β] [PseudoMetrizableSpace β]
    [PseudoMetrizableSpace γ] [SecondCountableTopology γ] [MeasurableSpace γ]
    [OpensMeasurableSpace γ] (g : β → γ) (hg : Measurable g) (f : α →ₘ[μ] β) :
    (compMeasurable g hg f).toGerm = f.toGerm.map g :=
  induction_on f fun f _ => by simp

set_option backward.isDefEq.respectTransparency false in
/-
**MeasureTheory.AEEqFun.comp** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.AEEqFun`。
形式化陈述：comp (g : β -> γ) (hg : Continuous g) (f : α ->ₘ[μ] β) : α ->ₘ[μ] γ
参数：g : β -> γ；hg : Continuous g；f : α ->ₘ[μ] β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp₂_toGerm (g : β → γ → δ) (hg : Continuous (uncurry g)) (f₁ : α →ₘ[μ] β)
    (f₂ : α →ₘ[μ] γ) : (comp₂ g hg f₁ f₂).toGerm = f₁.toGerm.map₂ g f₂.toGerm :=
  induction_on₂ f₁ f₂ fun f₁ _ f₂ _ => by simp

set_option backward.isDefEq.respectTransparency false in
/-
**MeasureTheory.AEEqFun.comp** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.AEEqFun`。
形式化陈述：comp (g : β -> γ) (hg : Continuous g) (f : α ->ₘ[μ] β) : α ->ₘ[μ] γ
参数：g : β -> γ；hg : Continuous g；f : α ->ₘ[μ] β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp₂Measurable_toGerm [PseudoMetrizableSpace β] [MeasurableSpace β] [BorelSpace β]
    [PseudoMetrizableSpace γ] [SecondCountableTopologyEither β γ]
    [MeasurableSpace γ] [BorelSpace γ] [PseudoMetrizableSpace δ] [SecondCountableTopology δ]
    [MeasurableSpace δ] [OpensMeasurableSpace δ] (g : β → γ → δ) (hg : Measurable (uncurry g))
    (f₁ : α →ₘ[μ] β) (f₂ : α →ₘ[μ] γ) :
    (comp₂Measurable g hg f₁ f₂).toGerm = f₁.toGerm.map₂ g f₂.toGerm :=
  induction_on₂ f₁ f₂ fun f₁ _ f₂ _ => by simp

/-- Given a predicate `p` and an equivalence class `[f]`, return true if `p` holds of `f a`
for almost all `a` -/
/-
**MeasureTheory.AEEqFun.LiftPred** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.AEEqFu
n`。
形式化陈述：LiftPred (p : β -> Prop) (f : α ->ₘ[μ] β) : Prop
参数：p : β -> Prop；f : α ->ₘ[μ] β。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α

--- 原说明 ---
Given a predicate `p` and an equivalence class `[f]`, return true if `p` holds o
f `f a`
for almost all `a`
-/
def LiftPred (p : β → Prop) (f : α →ₘ[μ] β) : Prop :=
  f.toGerm.LiftPred p

/-- Given a relation `r` and equivalence class `[f]` and `[g]`, return true if `r` holds of
`(f a, g a)` for almost all `a` -/
/-
**MeasureTheory.AEEqFun.LiftRel** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.AEEqFun
`。
形式化陈述：LiftRel (r : β -> γ -> Prop) (f : α ->ₘ[μ] β) (g : α ->ₘ[μ] γ) : Prop
参数：r : β -> γ -> Prop；f : α ->ₘ[μ] β；g : α ->ₘ[μ] γ。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α

--- 原说明 ---
Given a relation `r` and equivalence class `[f]` and `[g]`, return true if `r` h
olds of
`(f a, g a)` for almost all `a`
-/
def LiftRel (r : β → γ → Prop) (f : α →ₘ[μ] β) (g : α →ₘ[μ] γ) : Prop :=
  f.toGerm.LiftRel r g.toGerm
/-
**MeasureTheory.AEEqFun.liftRel_mk_mk** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.A
EEqFun`。
形式化陈述：liftRel_mk_mk {r : β -> γ -> Prop} {f : α -> β} {g : α -> γ} {hf hg} : Lif
tRel r (mk f hf : α ->ₘ[μ] β) (mk g hg) ↔ forallᵐ a ∂μ, r (f a) (g a)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem liftRel_mk_mk {r : β → γ → Prop} {f : α → β} {g : α → γ} {hf hg} :
    LiftRel r (mk f hf : α →ₘ[μ] β) (mk g hg) ↔ ∀ᵐ a ∂μ, r (f a) (g a) :=
  Iff.rfl
/-
**MeasureTheory.AEEqFun.liftRel_iff_coeFn** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.AEEqFun`。
形式化陈述：liftRel_iff_coeFn {r : β -> γ -> Prop} {f : α ->ₘ[μ] β} {g : α ->ₘ[μ] γ} :
 LiftRel r f g ↔ forallᵐ a ∂μ, r (f a) (g a)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.AEEqFun.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u
_2} [inst : MeasurableSpace α] {μ : MeasureTheory.Measure α} [inst_1 : Topologic
alSpace β]   (f : α →ₘ[μ] β), Me…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.AEEqFun.liftRel_mk_mk`：liftRel_mk_mk {r : β -> γ -> Prop} 
{f : α -> β} {g : α -> γ} {hf hg} : LiftRel r (mk f hf : α ->ₘ[μ] β) (mk g hg) ↔
 forallᵐ a ∂μ, r (f a) (g…
· 使用定理 `MeasureTheory.AEEqFun.mk_coeFn`：mk_coeFn (f : α ->ₘ[μ] β) : mk f f.aestr
onglyMeasurable = f
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem liftRel_iff_coeFn {r : β → γ → Prop} {f : α →ₘ[μ] β} {g : α →ₘ[μ] γ} :
    LiftRel r f g ↔ ∀ᵐ a ∂μ, r (f a) (g a) := by
  rw [← liftRel_mk_mk (hf := f.aestronglyMeasurable) (hg := g.aestronglyMeasurable),
    mk_coeFn, mk_coeFn]

section Order

/-
**MeasureTheory.AEEqFun.instPreorder** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.AE
EqFun`。
形式化陈述：instPreorder [Preorder β] : Preorder (α ->ₘ[μ] β)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
-/
instance instPreorder [Preorder β] : Preorder (α →ₘ[μ] β) :=
  Preorder.lift toGerm

@[simp]
/-
**MeasureTheory.AEEqFun.mk_le_mk** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.AEEqFu
n`。
形式化陈述：mk_le_mk [Preorder β] {f g : α -> β} (hf hg) : (mk f hf : α ->ₘ[μ] β) <= m
k g hg ↔ f <=ᵐ[μ] g
参数：hf hg。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mk_le_mk [Preorder β] {f g : α → β} (hf hg) : (mk f hf : α →ₘ[μ] β) ≤ mk g hg ↔ f ≤ᵐ[μ] g :=
  Iff.rfl

@[simp, norm_cast]
/-
**MeasureTheory.AEEqFun.coeFn_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.AEEqFu
n`。
形式化陈述：coeFn_le [Preorder β] {f g : α ->ₘ[μ] β} : (f : α -> β) <=ᵐ[μ] g ↔ f <= g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.AEEqFun.liftRel_iff_coeFn`：liftRel_iff_coeFn {r : β -> γ -
> Prop} {f : α ->ₘ[μ] β} {g : α ->ₘ[μ] γ} : LiftRel r f g ↔ forallᵐ a ∂μ, r (f a
) (g a)
-/
theorem coeFn_le [Preorder β] {f g : α →ₘ[μ] β} : (f : α → β) ≤ᵐ[μ] g ↔ f ≤ g :=
  liftRel_iff_coeFn.symm
/-
**MeasureTheory.AEEqFun.instPartialOrder** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheor
y.AEEqFun`。
形式化陈述：instPartialOrder [PartialOrder β] : PartialOrder (α ->ₘ[μ] β)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.AEEqFun.toGerm_injective`：toGerm_injective : Injective (to
Germ : (α ->ₘ[μ] β) -> Germ (ae μ) β)
-/
instance instPartialOrder [PartialOrder β] : PartialOrder (α →ₘ[μ] β) :=
  PartialOrder.lift toGerm toGerm_injective

section Lattice

section Sup

variable [SemilatticeSup β] [ContinuousSup β]

/-
**MeasureTheory.AEEqFun.instSup** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.AEEqFun
`。
形式化陈述：instSup : Max (α ->ₘ[μ] β) where max f g
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSup : Max (α →ₘ[μ] β) where max f g := AEEqFun.comp₂ (· ⊔ ·) continuous_sup f g
/-
**MeasureTheory.AEEqFun.coeFn_sup** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.AEEqF
un`。
形式化陈述：coeFn_sup (f g : α ->ₘ[μ] β) : ⇑(f ⊔ g) =ᵐ[μ] fun x => f x ⊔ g x
参数：f g : α ->ₘ[μ] β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEEqFun.coeFn_comp₂`：coeFn_comp₂ (g : β -> γ -> δ) (hg : C
ontinuous (uncurry g)) (f₁ : α ->ₘ[μ] β) (f₂ : α ->ₘ[μ] γ) : comp₂ g hg f₁ f₂ =ᵐ
[μ] fun a => g (f₁ a) (…
-/
theorem coeFn_sup (f g : α →ₘ[μ] β) : ⇑(f ⊔ g) =ᵐ[μ] fun x => f x ⊔ g x :=
  coeFn_comp₂ _ _ _ _
/-
**MeasureTheory.AEEqFun.le_sup_left** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.AEE
qFun`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : MeasurableSpace α] {μ : MeasureThe
ory.Measure α} [inst_1 : TopologicalSpace β]   [inst_2 : SemilatticeSup β] [inst
_3 : ContinuousSup β] (f g : α →ₘ[μ] β), f ≤ f ⊔ g
参数：f g : α →ₘ[μ] β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.AEEqFun.coeFn_le`：coeFn_le [Preorder β] {f g : α ->ₘ[μ] β}
 : (f : α -> β) <=ᵐ[μ] g ↔ f <= g
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.AEEqFun.coeFn_sup`：coeFn_sup (f g : α ->ₘ[μ] β) : ⇑(f ⊔ g)
 =ᵐ[μ] fun x => f x ⊔ g x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
-/
protected theorem le_sup_left (f g : α →ₘ[μ] β) : f ≤ f ⊔ g := by
  rw [← coeFn_le]
  filter_upwards [coeFn_sup f g] with _ ha
  rw [ha]
  exact le_sup_left
/-
**MeasureTheory.AEEqFun.le_sup_right** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.AE
EqFun`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : MeasurableSpace α] {μ : MeasureThe
ory.Measure α} [inst_1 : TopologicalSpace β]   [inst_2 : SemilatticeSup β] [inst
_3 : ContinuousSup β] (f g : α →ₘ[μ] β), g ≤ f ⊔ g
参数：f g : α →ₘ[μ] β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.AEEqFun.coeFn_le`：coeFn_le [Preorder β] {f g : α ->ₘ[μ] β}
 : (f : α -> β) <=ᵐ[μ] g ↔ f <= g
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.AEEqFun.coeFn_sup`：coeFn_sup (f g : α ->ₘ[μ] β) : ⇑(f ⊔ g)
 =ᵐ[μ] fun x => f x ⊔ g x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
-/
protected theorem le_sup_right (f g : α →ₘ[μ] β) : g ≤ f ⊔ g := by
  rw [← coeFn_le]
  filter_upwards [coeFn_sup f g] with _ ha
  rw [ha]
  exact le_sup_right
/-
**MeasureTheory.AEEqFun.sup_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.AEEqFun`
。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : MeasurableSpace α] {μ : MeasureThe
ory.Measure α} [inst_1 : TopologicalSpace β]   [inst_2 : SemilatticeSup β] [inst
_3 : ContinuousSup β] (f g f' : α →ₘ[μ] β), f ≤ f' → g ≤ f' → f ⊔ g ≤ f'
参数：f g f' : α →ₘ[μ] β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.AEEqFun.coeFn_le`：coeFn_le [Preorder β] {f g : α ->ₘ[μ] β}
 : (f : α -> β) <=ᵐ[μ] g ↔ f <= g
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.AEEqFun.coeFn_sup`：coeFn_sup (f g : α ->ₘ[μ] β) : ⇑(f ⊔ g)
 =ᵐ[μ] fun x => f x ⊔ g x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
-/
protected theorem sup_le (f g f' : α →ₘ[μ] β) (hf : f ≤ f') (hg : g ≤ f') : f ⊔ g ≤ f' := by
  rw [← coeFn_le] at hf hg ⊢
  filter_upwards [hf, hg, coeFn_sup f g] with _ haf hag ha_sup
  rw [ha_sup]
  exact sup_le haf hag

end Sup

section Inf

variable [SemilatticeInf β] [ContinuousInf β]

/-
**MeasureTheory.AEEqFun.instInf** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.AEEqFun
`。
形式化陈述：instInf : Min (α ->ₘ[μ] β) where min f g
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instInf : Min (α →ₘ[μ] β) where min f g := AEEqFun.comp₂ (· ⊓ ·) continuous_inf f g
/-
**MeasureTheory.AEEqFun.coeFn_inf** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.AEEqF
un`。
形式化陈述：coeFn_inf (f g : α ->ₘ[μ] β) : ⇑(f ⊓ g) =ᵐ[μ] fun x => f x ⊓ g x
参数：f g : α ->ₘ[μ] β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEEqFun.coeFn_comp₂`：coeFn_comp₂ (g : β -> γ -> δ) (hg : C
ontinuous (uncurry g)) (f₁ : α ->ₘ[μ] β) (f₂ : α ->ₘ[μ] γ) : comp₂ g hg f₁ f₂ =ᵐ
[μ] fun a => g (f₁ a) (…
-/
theorem coeFn_inf (f g : α →ₘ[μ] β) : ⇑(f ⊓ g) =ᵐ[μ] fun x => f x ⊓ g x :=
  coeFn_comp₂ _ _ _ _
/-
**MeasureTheory.AEEqFun.inf_le_left** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.AEE
qFun`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : MeasurableSpace α] {μ : MeasureThe
ory.Measure α} [inst_1 : TopologicalSpace β]   [inst_2 : SemilatticeInf β] [inst
_3 : ContinuousInf β] (f g : α →ₘ[μ] β), f ⊓ g ≤ f
参数：f g : α →ₘ[μ] β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.AEEqFun.coeFn_le`：coeFn_le [Preorder β] {f g : α ->ₘ[μ] β}
 : (f : α -> β) <=ᵐ[μ] g ↔ f <= g
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.AEEqFun.coeFn_inf`：coeFn_inf (f g : α ->ₘ[μ] β) : ⇑(f ⊓ g)
 =ᵐ[μ] fun x => f x ⊓ g x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
-/
protected theorem inf_le_left (f g : α →ₘ[μ] β) : f ⊓ g ≤ f := by
  rw [← coeFn_le]
  filter_upwards [coeFn_inf f g] with _ ha
  rw [ha]
  exact inf_le_left
/-
**MeasureTheory.AEEqFun.inf_le_right** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.AE
EqFun`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : MeasurableSpace α] {μ : MeasureThe
ory.Measure α} [inst_1 : TopologicalSpace β]   [inst_2 : SemilatticeInf β] [inst
_3 : ContinuousInf β] (f g : α →ₘ[μ] β), f ⊓ g ≤ g
参数：f g : α →ₘ[μ] β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.AEEqFun.coeFn_le`：coeFn_le [Preorder β] {f g : α ->ₘ[μ] β}
 : (f : α -> β) <=ᵐ[μ] g ↔ f <= g
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.AEEqFun.coeFn_inf`：coeFn_inf (f g : α ->ₘ[μ] β) : ⇑(f ⊓ g)
 =ᵐ[μ] fun x => f x ⊓ g x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
-/
protected theorem inf_le_right (f g : α →ₘ[μ] β) : f ⊓ g ≤ g := by
  rw [← coeFn_le]
  filter_upwards [coeFn_inf f g] with _ ha
  rw [ha]
  exact inf_le_right
/-
**MeasureTheory.AEEqFun.le_inf** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.AEEqFun`
。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : MeasurableSpace α] {μ : MeasureThe
ory.Measure α} [inst_1 : TopologicalSpace β]   [inst_2 : SemilatticeInf β] [inst
_3 : ContinuousInf β] (f' f g : α →ₘ[μ] β), f' ≤ f → f' ≤ g → f' ≤ f ⊓ g
参数：f' f g : α →ₘ[μ] β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.AEEqFun.coeFn_le`：coeFn_le [Preorder β] {f g : α ->ₘ[μ] β}
 : (f : α -> β) <=ᵐ[μ] g ↔ f <= g
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.AEEqFun.coeFn_inf`：coeFn_inf (f g : α ->ₘ[μ] β) : ⇑(f ⊓ g)
 =ᵐ[μ] fun x => f x ⊓ g x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `le_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {c a b : α}, c ≤ a → c 
≤ b → c ≤ a ⊓ b
-/
protected theorem le_inf (f' f g : α →ₘ[μ] β) (hf : f' ≤ f) (hg : f' ≤ g) : f' ≤ f ⊓ g := by
  rw [← coeFn_le] at hf hg ⊢
  filter_upwards [hf, hg, coeFn_inf f g] with _ haf hag ha_inf
  rw [ha_inf]
  exact le_inf haf hag

end Inf

/-
**MeasureTheory.AEEqFun.instLattice** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.AEE
qFun`。
形式化陈述：instLattice [Lattice β] [TopologicalLattice β] : Lattice (α ->ₘ[μ] β)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalLattice.toContinuousSup`：∀ {L : Type u_1} {inst : Topological
Space L} {inst_1 : Lattice L} [self : TopologicalLattice L], ContinuousSup L
· 使用定理 `TopologicalLattice.toContinuousInf`：∀ {L : Type u_1} {inst : Topological
Space L} {inst_1 : Lattice L} [self : TopologicalLattice L], ContinuousInf L
-/
instance instLattice [Lattice β] [TopologicalLattice β] : Lattice (α →ₘ[μ] β) :=
  { AEEqFun.instPartialOrder with
    sup := max
    le_sup_left := AEEqFun.le_sup_left
    le_sup_right := AEEqFun.le_sup_right
    sup_le := AEEqFun.sup_le
    inf := min
    inf_le_left := AEEqFun.inf_le_left
    inf_le_right := AEEqFun.inf_le_right
    le_inf := AEEqFun.le_inf }

end Lattice

end Order

variable (α)

/-- The equivalence class of a constant function: `[fun _ : α => b]`, based on the equivalence
relation of being almost everywhere equal -/
/-
**MeasureTheory.AEEqFun.const** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.AEEqFun`。
形式化陈述：const (b : β) : α ->ₘ[μ] β
参数：b : β。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.aestronglyMeasurable_const`：aestronglyMeasurable_const {b 
: β} : AEStronglyMeasurable[m] (fun _ : α => b) μ

--- 原说明 ---
The equivalence class of a constant function: `[fun _ : α => b]`, based on the e
quivalence
relation of being almost everywhere equal
-/
def const (b : β) : α →ₘ[μ] β :=
  mk (fun _ : α ↦ b) aestronglyMeasurable_const
/-
**MeasureTheory.AEEqFun.coeFn_const** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.AEE
qFun`。
形式化陈述：coeFn_const (b : β) : (const α b : α ->ₘ[μ] β) =ᵐ[μ] Function.const α b
参数：b : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEEqFun.coeFn_mk`：coeFn_mk (f : α -> β) (hf) : (mk f hf : 
α ->ₘ[μ] β) =ᵐ[μ] f
· 使用定理 `MeasureTheory.aestronglyMeasurable_const`：aestronglyMeasurable_const {b 
: β} : AEStronglyMeasurable[m] (fun _ : α => b) μ
-/
theorem coeFn_const (b : β) : (const α b : α →ₘ[μ] β) =ᵐ[μ] Function.const α b :=
  coeFn_mk _ _

set_option backward.isDefEq.respectTransparency false in
/-- If the measure is nonzero, we can strengthen `coeFn_const` to get an equality. -/
@[simp]
/-
**MeasureTheory.AEEqFun.coeFn_const_eq** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
AEEqFun`。
形式化陈述：coeFn_const_eq [NeZero μ] (b : β) (x : α) : (const α b : α ->ₘ[μ] β) x = b
参数：b : β；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.aestronglyMeasurable_const`：aestronglyMeasurable_const {b 
: β} : AEStronglyMeasurable[m] (fun _ : α => b) μ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `Function.const.eq_1`：∀ {α : Sort u} (β : Sort v) (a : α) (x : β), Functi
on.const β a x = a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Measure.ae.neBot`：∀ {α : Type u_1} {m0 : MeasurableSpace α
} {μ : MeasureTheory.Measure α} [NeZero μ], (MeasureTheory.ae μ).NeBot
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc

--- 原说明 ---
If the measure is nonzero, we can strengthen `coeFn_const` to get an equality.
-/
theorem coeFn_const_eq [NeZero μ] (b : β) (x : α) : (const α b : α →ₘ[μ] β) x = b := by
  simp only [cast]
  split_ifs with h
  case neg => exact h.elim ⟨b, rfl⟩
  have := Classical.choose_spec h
  set b' := Classical.choose h
  simp_rw [const, mk_eq_mk, EventuallyEq, ← const_def, eventually_const] at this
  rw [Function.const, this]
/-
**MeasureTheory.AEEqFun.coeFn_const_eq'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.AEEqFun`。
形式化陈述：coeFn_const_eq' (b : β) : exists b', ((const α b : α ->ₘ[μ] β) : α -> β) =
 fun _ => b'
参数：b : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.aestronglyMeasurable_const`：aestronglyMeasurable_const {b 
: β} : AEStronglyMeasurable[m] (fun _ : α => b) μ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
theorem coeFn_const_eq' (b : β) : ∃ b', ((const α b : α →ₘ[μ] β) : α → β) = fun _ ↦ b' := by
  simp only [cast]
  split_ifs with h
  case neg => exact h.elim ⟨b, rfl⟩
  exact ⟨Classical.choose h, by ext; simp⟩

variable {α}
/-
**MeasureTheory.AEEqFun.instInhabited** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.A
EEqFun`。
形式化陈述：instInhabited [Inhabited β] : Inhabited (α ->ₘ[μ] β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instInhabited [Inhabited β] : Inhabited (α →ₘ[μ] β) :=
  ⟨const α default⟩

@[to_additive]
/-
**MeasureTheory.AEEqFun.instOne** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.AEEqFun
`。
形式化陈述：instOne [One β] : One (α ->ₘ[μ] β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instOne [One β] : One (α →ₘ[μ] β) :=
  ⟨const α 1⟩

@[to_additive]
/-
**MeasureTheory.AEEqFun.one_def** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.AEEqFun
`。
形式化陈述：one_def [One β] : (1 : α ->ₘ[μ] β) = mk (fun _ : α => 1) aestronglyMeasura
ble_const
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem one_def [One β] : (1 : α →ₘ[μ] β) = mk (fun _ : α => 1) aestronglyMeasurable_const :=
  rfl

@[to_additive]
/-
**MeasureTheory.AEEqFun.coeFn_one** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.AEEqF
un`。
形式化陈述：coeFn_one [One β] : ⇑(1 : α ->ₘ[μ] β) =ᵐ[μ] 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEEqFun.coeFn_const`：coeFn_const (b : β) : (const α b : α 
->ₘ[μ] β) =ᵐ[μ] Function.const α b
-/
theorem coeFn_one [One β] : ⇑(1 : α →ₘ[μ] β) =ᵐ[μ] 1 :=
  coeFn_const ..

@[to_additive (attr := simp)]
/-
**MeasureTheory.AEEqFun.coeFn_one_eq** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.AE
EqFun`。
形式化陈述：coeFn_one_eq [NeZero μ] [One β] {x : α} : (1 : α ->ₘ[μ] β) x = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEEqFun.coeFn_const_eq`：coeFn_const_eq [NeZero μ] (b : β) 
(x : α) : (const α b : α ->ₘ[μ] β) x = b
-/
theorem coeFn_one_eq [NeZero μ] [One β] {x : α} : (1 : α →ₘ[μ] β) x = 1 :=
  coeFn_const_eq ..

@[to_additive (attr := simp)]
/-
**MeasureTheory.AEEqFun.one_toGerm** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.AEEq
Fun`。
形式化陈述：one_toGerm [One β] : (1 : α ->ₘ[μ] β).toGerm = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
-/
theorem one_toGerm [One β] : (1 : α →ₘ[μ] β).toGerm = 1 :=
  rfl

-- Note we set up the scalar actions before the `Monoid` structures in case we want to
-- try to override the `nsmul` or `zsmul` fields in future.
section SMul

variable {𝕜 𝕜' : Type*}
variable [SMul 𝕜 γ] [ContinuousConstSMul 𝕜 γ]
variable [SMul 𝕜' γ] [ContinuousConstSMul 𝕜' γ]

/-
**MeasureTheory.AEEqFun.instSMul** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.AEEqFu
n`。
形式化陈述：instSMul : SMul 𝕜 (α ->ₘ[μ] γ)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSMul : SMul 𝕜 (α →ₘ[μ] γ) :=
  ⟨fun c f => comp (c • ·) (continuous_id.const_smul c) f⟩

@[simp]
/-
**MeasureTheory.AEEqFun.smul_mk** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.AEEqFun
`。
形式化陈述：smul_mk (c : 𝕜) (f : α -> γ) (hf : AEStronglyMeasurable f μ) : c • (mk f h
f : α ->ₘ[μ] γ) = mk (c • f) (hf.const_smul _)
参数：c : 𝕜；f : α -> γ；hf : AEStronglyMeasurable f μ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_mk (c : 𝕜) (f : α → γ) (hf : AEStronglyMeasurable f μ) :
    c • (mk f hf : α →ₘ[μ] γ) = mk (c • f) (hf.const_smul _) :=
  rfl
/-
**MeasureTheory.AEEqFun.coeFn_smul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.AEEq
Fun`。
形式化陈述：coeFn_smul (c : 𝕜) (f : α ->ₘ[μ] γ) : ⇑(c • f) =ᵐ[μ] c • ⇑f
参数：c : 𝕜；f : α ->ₘ[μ] γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEEqFun.coeFn_comp`：coeFn_comp (g : β -> γ) (hg : Continuo
us g) (f : α ->ₘ[μ] β) : comp g hg f =ᵐ[μ] g ∘ f
-/
theorem coeFn_smul (c : 𝕜) (f : α →ₘ[μ] γ) : ⇑(c • f) =ᵐ[μ] c • ⇑f :=
  coeFn_comp _ _ _
/-
**MeasureTheory.AEEqFun.smul_toGerm** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.AEE
qFun`。
形式化陈述：smul_toGerm (c : 𝕜) (f : α ->ₘ[μ] γ) : (c • f).toGerm = c • f.toGerm
参数：c : 𝕜；f : α ->ₘ[μ] γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEEqFun.comp_toGerm`：comp_toGerm (g : β -> γ) (hg : Contin
uous g) (f : α ->ₘ[μ] β) : (comp g hg f).toGerm = f.toGerm.map g
-/
theorem smul_toGerm (c : 𝕜) (f : α →ₘ[μ] γ) : (c • f).toGerm = c • f.toGerm :=
  comp_toGerm _ _ _
/-
**MeasureTheory.AEEqFun.instSMulCommClass** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheo
ry.AEEqFun`。
形式化陈述：instSMulCommClass [SMulCommClass 𝕜 𝕜' γ] : SMulCommClass 𝕜 𝕜' (α ->ₘ[μ] γ)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEEqFun.induction_on`：induction_on (f : α ->ₘ[μ] β) {p : (
α ->ₘ[μ] β) -> Prop} (H : forall f hf, p (mk f hf)) : p f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MeasureTheory.AEStronglyMeasurable.const_smul`：∀ {α : Type u_1} {β : Typ
e u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory
.Measure α}   {f : α → β} {𝕜 : Type…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.AEEqFun.mk.congr_simp`：∀ {α : Type u_1} [inst : Measurable
Space α] {μ : MeasureTheory.Measure α} {β : Type u_5} [inst_1 : TopologicalSpace
 β]   (f f_1 : α → β) (e_…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance instSMulCommClass [SMulCommClass 𝕜 𝕜' γ] : SMulCommClass 𝕜 𝕜' (α →ₘ[μ] γ) :=
  ⟨fun a b f => induction_on f fun f hf => by simp_rw [smul_mk, smul_comm]⟩
/-
**MeasureTheory.AEEqFun.instIsScalarTower** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheo
ry.AEEqFun`。
形式化陈述：instIsScalarTower [SMul 𝕜 𝕜'] [IsScalarTower 𝕜 𝕜' γ] : IsScalarTower 𝕜 𝕜' 
(α ->ₘ[μ] γ)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEEqFun.induction_on`：induction_on (f : α ->ₘ[μ] β) {p : (
α ->ₘ[μ] β) -> Prop} (H : forall f hf, p (mk f hf)) : p f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MeasureTheory.AEStronglyMeasurable.const_smul`：∀ {α : Type u_1} {β : Typ
e u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory
.Measure α}   {f : α → β} {𝕜 : Type…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.AEEqFun.mk.congr_simp`：∀ {α : Type u_1} [inst : Measurable
Space α] {μ : MeasureTheory.Measure α} {β : Type u_5} [inst_1 : TopologicalSpace
 β]   (f f_1 : α → β) (e_…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance instIsScalarTower [SMul 𝕜 𝕜'] [IsScalarTower 𝕜 𝕜' γ] : IsScalarTower 𝕜 𝕜' (α →ₘ[μ] γ) :=
  ⟨fun a b f => induction_on f fun f hf => by simp_rw [smul_mk, smul_assoc]⟩
/-
**MeasureTheory.AEEqFun.instIsCentralScalar** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTh
eory.AEEqFun`。
形式化陈述：instIsCentralScalar [SMul 𝕜ᵐᵒᵖ γ] [IsCentralScalar 𝕜 γ] : IsCentralScalar 
𝕜 (α ->ₘ[μ] γ)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEEqFun.induction_on`：induction_on (f : α ->ₘ[μ] β) {p : (
α ->ₘ[μ] β) -> Prop} (H : forall f hf, p (mk f hf)) : p f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MeasureTheory.AEStronglyMeasurable.const_smul`：∀ {α : Type u_1} {β : Typ
e u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory
.Measure α}   {f : α → β} {𝕜 : Type…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsCentralScalar.op_smul_eq_smul`：∀ {M : Type u_9} {α : Type u_10} {inst 
: SMul M α} {inst_1 : SMul Mᵐᵒᵖ α} [self : IsCentralScalar M α] (m : M) (a : α),
   MulOpposite.op m •…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.AEEqFun.mk.congr_simp`：∀ {α : Type u_1} [inst : Measurable
Space α] {μ : MeasureTheory.Measure α} {β : Type u_5} [inst_1 : TopologicalSpace
 β]   (f f_1 : α → β) (e_…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance instIsCentralScalar [SMul 𝕜ᵐᵒᵖ γ] [IsCentralScalar 𝕜 γ] : IsCentralScalar 𝕜 (α →ₘ[μ] γ) :=
  ⟨fun a f => induction_on f fun f hf => by simp_rw [smul_mk, op_smul_eq_smul]⟩

end SMul

section Mul

variable [Mul γ] [ContinuousMul γ]

@[to_additive]
/-
**MeasureTheory.AEEqFun.instMul** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.AEEqFun
`。
形式化陈述：instMul : Mul (α ->ₘ[μ] γ)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_mul`：continuous_mul : Continuous fun p : M × M => p.1 * p.2
-/
instance instMul : Mul (α →ₘ[μ] γ) :=
  ⟨comp₂ (· * ·) continuous_mul⟩

@[to_additive (attr := simp)]
/-
**MeasureTheory.AEEqFun.mk_mul_mk** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.AEEqF
un`。
形式化陈述：mk_mul_mk (f g : α -> γ) (hf : AEStronglyMeasurable f μ) (hg : AEStronglyM
easurable g μ) : (mk f hf : α ->ₘ[μ] γ) * mk g hg = mk (f * g) (hf.mul hg)
参数：f g : α -> γ；hf : AEStronglyMeasurable f μ；hg : AEStronglyMeasurable g μ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_mul_mk (f g : α → γ) (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    (mk f hf : α →ₘ[μ] γ) * mk g hg = mk (f * g) (hf.mul hg) :=
  rfl

@[to_additive]
/-
**MeasureTheory.AEEqFun.coeFn_mul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.AEEqF
un`。
形式化陈述：coeFn_mul (f g : α ->ₘ[μ] γ) : ⇑(f * g) =ᵐ[μ] f * g
参数：f g : α ->ₘ[μ] γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEEqFun.coeFn_comp₂`：coeFn_comp₂ (g : β -> γ -> δ) (hg : C
ontinuous (uncurry g)) (f₁ : α ->ₘ[μ] β) (f₂ : α ->ₘ[μ] γ) : comp₂ g hg f₁ f₂ =ᵐ
[μ] fun a => g (f₁ a) (…
· 使用定理 `continuous_mul`：continuous_mul : Continuous fun p : M × M => p.1 * p.2
-/
theorem coeFn_mul (f g : α →ₘ[μ] γ) : ⇑(f * g) =ᵐ[μ] f * g :=
  coeFn_comp₂ _ _ _ _

@[to_additive (attr := simp)]
/-
**MeasureTheory.AEEqFun.mul_toGerm** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.AEEq
Fun`。
形式化陈述：mul_toGerm (f g : α ->ₘ[μ] γ) : (f * g).toGerm = f.toGerm * g.toGerm
参数：f g : α ->ₘ[μ] γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEEqFun.comp₂_toGerm`：comp₂_toGerm (g : β -> γ -> δ) (hg :
 Continuous (uncurry g)) (f₁ : α ->ₘ[μ] β) (f₂ : α ->ₘ[μ] γ) : (comp₂ g hg f₁ f₂
).toGerm = f₁.toGerm.map…
· 使用定理 `continuous_mul`：continuous_mul : Continuous fun p : M × M => p.1 * p.2
-/
theorem mul_toGerm (f g : α →ₘ[μ] γ) : (f * g).toGerm = f.toGerm * g.toGerm :=
  comp₂_toGerm _ _ _ _

end Mul

/-
**MeasureTheory.AEEqFun.instAddMonoid** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.A
EEqFun`。
形式化陈述：instAddMonoid [AddMonoid γ] [ContinuousAdd γ] : AddMonoid (α ->ₘ[μ] γ)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.AEEqFun.toGerm_injective`：toGerm_injective : Injective (to
Germ : (α ->ₘ[μ] β) -> Germ (ae μ) β)
-/
instance instAddMonoid [AddMonoid γ] [ContinuousAdd γ] : AddMonoid (α →ₘ[μ] γ) :=
  toGerm_injective.addMonoid toGerm zero_toGerm add_toGerm fun _ _ => smul_toGerm _ _
/-
**MeasureTheory.AEEqFun.instAddCommMonoid** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheo
ry.AEEqFun`。
形式化陈述：instAddCommMonoid [AddCommMonoid γ] [ContinuousAdd γ] : AddCommMonoid (α -
>ₘ[μ] γ)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.AEEqFun.toGerm_injective`：toGerm_injective : Injective (to
Germ : (α ->ₘ[μ] β) -> Germ (ae μ) β)
-/
instance instAddCommMonoid [AddCommMonoid γ] [ContinuousAdd γ] : AddCommMonoid (α →ₘ[μ] γ) :=
  toGerm_injective.addCommMonoid toGerm zero_toGerm add_toGerm fun _ _ => smul_toGerm _ _

section Monoid

variable [Monoid γ] [ContinuousMul γ]

/-
**MeasureTheory.AEEqFun.instPowNat** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.AEEq
Fun`。
形式化陈述：instPowNat : Pow (α ->ₘ[μ] γ) Nat
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_pow`：∀ {M : Type u_3} [inst : TopologicalSpace M] [inst_1 : M
onoid M] [ContinuousMul M] (n : ℕ), Continuous fun a => a ^ n
-/
instance instPowNat : Pow (α →ₘ[μ] γ) ℕ :=
  ⟨fun f n => comp _ (continuous_pow n) f⟩

@[simp]
/-
**MeasureTheory.AEEqFun.mk_pow** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.AEEqFun`
。
形式化陈述：mk_pow (f : α -> γ) (hf) (n : Nat) : (mk f hf : α ->ₘ[μ] γ) ^ n = mk (f ^ 
n) ((_root_.continuous_pow n).comp_aestronglyMeasurable hf)
参数：f : α -> γ；hf；n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_pow (f : α → γ) (hf) (n : ℕ) :
    (mk f hf : α →ₘ[μ] γ) ^ n =
      mk (f ^ n) ((_root_.continuous_pow n).comp_aestronglyMeasurable hf) :=
  rfl
/-
**MeasureTheory.AEEqFun.coeFn_pow** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.AEEqF
un`。
形式化陈述：coeFn_pow (f : α ->ₘ[μ] γ) (n : Nat) : ⇑(f ^ n) =ᵐ[μ] (⇑f) ^ n
参数：f : α ->ₘ[μ] γ；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEEqFun.coeFn_comp`：coeFn_comp (g : β -> γ) (hg : Continuo
us g) (f : α ->ₘ[μ] β) : comp g hg f =ᵐ[μ] g ∘ f
· 使用定理 `continuous_pow`：∀ {M : Type u_3} [inst : TopologicalSpace M] [inst_1 : M
onoid M] [ContinuousMul M] (n : ℕ), Continuous fun a => a ^ n
-/
theorem coeFn_pow (f : α →ₘ[μ] γ) (n : ℕ) : ⇑(f ^ n) =ᵐ[μ] (⇑f) ^ n :=
  coeFn_comp _ _ _

@[simp]
/-
**MeasureTheory.AEEqFun.pow_toGerm** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.AEEq
Fun`。
形式化陈述：pow_toGerm (f : α ->ₘ[μ] γ) (n : Nat) : (f ^ n).toGerm = f.toGerm ^ n
参数：f : α ->ₘ[μ] γ；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEEqFun.comp_toGerm`：comp_toGerm (g : β -> γ) (hg : Contin
uous g) (f : α ->ₘ[μ] β) : (comp g hg f).toGerm = f.toGerm.map g
· 使用定理 `continuous_pow`：∀ {M : Type u_3} [inst : TopologicalSpace M] [inst_1 : M
onoid M] [ContinuousMul M] (n : ℕ), Continuous fun a => a ^ n
-/
theorem pow_toGerm (f : α →ₘ[μ] γ) (n : ℕ) : (f ^ n).toGerm = f.toGerm ^ n :=
  comp_toGerm _ _ _

@[to_additive existing]
/-
**MeasureTheory.AEEqFun.instMonoid** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.AEEq
Fun`。
形式化陈述：instMonoid : Monoid (α ->ₘ[μ] γ)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.AEEqFun.toGerm_injective`：toGerm_injective : Injective (to
Germ : (α ->ₘ[μ] β) -> Germ (ae μ) β)
· 使用定理 `MeasureTheory.AEEqFun.pow_toGerm`：pow_toGerm (f : α ->ₘ[μ] γ) (n : Nat) 
: (f ^ n).toGerm = f.toGerm ^ n
-/
instance instMonoid : Monoid (α →ₘ[μ] γ) :=
  toGerm_injective.monoid toGerm one_toGerm mul_toGerm pow_toGerm

/-- `AEEqFun.toGerm` as a `MonoidHom`. -/
@[to_additive (attr := simps) /-- `AEEqFun.toGerm` as an `AddMonoidHom`. -/]
/-
**MeasureTheory.AEEqFun.toGermMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory
.AEEqFun`。
形式化陈述：toGermMonoidHom : (α ->ₘ[μ] γ) ->* (ae μ).Germ γ where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α

--- 原说明 ---
`AEEqFun.toGerm` as a `MonoidHom`.
-/
def toGermMonoidHom : (α →ₘ[μ] γ) →* (ae μ).Germ γ where
  toFun := toGerm
  map_one' := one_toGerm
  map_mul' := mul_toGerm

end Monoid

@[to_additive existing]
/-
**MeasureTheory.AEEqFun.instCommMonoid** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.
AEEqFun`。
形式化陈述：instCommMonoid [CommMonoid γ] [ContinuousMul γ] : CommMonoid (α ->ₘ[μ] γ)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.AEEqFun.toGerm_injective`：toGerm_injective : Injective (to
Germ : (α ->ₘ[μ] β) -> Germ (ae μ) β)
-/
instance instCommMonoid [CommMonoid γ] [ContinuousMul γ] : CommMonoid (α →ₘ[μ] γ) :=
  toGerm_injective.commMonoid toGerm one_toGerm mul_toGerm pow_toGerm

@[to_additive]
/-
**MeasureTheory.AEEqFun.coeFn_finsetProd** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.AEEqFun`。
形式化陈述：coeFn_finsetProd [CommMonoid γ] [ContinuousMul γ] {ι : Type*} (s : Finset 
ι) (f : ι -> α ->ₘ[μ] γ) : ⇑(∏ i in s, f i) =ᵐ[μ] ∏ i in s, ⇑(f i)
参数：s : Finset ι；f : ι -> α ->ₘ[μ] γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst : De
cidableEq α],   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → motive s → motive 
(inser…
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_insert`：prod_insert [DecidableEq ι] : a ∉ s -> ∏ x in insert
 a s, f x = f a * ∏ x in s, f x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `Mathlib.Tactic.GCongr.rel_imp_rel`：rel_imp_rel (h₁ : r c a) (h₂ : r b d)
 : r a b -> r c d
· 使用定理 `instIsTransOfTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [Trans r r r], I
sTrans α r
· 使用定理 `MeasureTheory.AEEqFun.coeFn_mul`：coeFn_mul (f g : α ->ₘ[μ] γ) : ⇑(f * g)
 =ᵐ[μ] f * g
· 使用定理 `Filter.EventuallyEq.refl`：∀ {α : Type u} {β : Type v} (l : Filter α) (f 
: α → β), f =ᶠ[l] f
· 使用定理 `Filter.EventuallyEq.mul`：∀ {α : Type u} {β : Type v} [inst : Mul β] {f f
' g g' : α → β} {l : Filter α},   f =ᶠ[l] g → f' =ᶠ[l] g' → f * f' =ᶠ[l] g * g'
-/
theorem coeFn_finsetProd [CommMonoid γ] [ContinuousMul γ]
    {ι : Type*} (s : Finset ι) (f : ι → α →ₘ[μ] γ) :
    ⇑(∏ i ∈ s, f i) =ᵐ[μ] ∏ i ∈ s, ⇑(f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [coeFn_one]
  | insert a s ha ih =>
    simp only [ha, not_false_eq_true, Finset.prod_insert]
    grw [coeFn_mul, ih]

@[to_additive]
/-
**MeasureTheory.AEEqFun.coeFn_fun_finsetProd** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.AEEqFun`。
形式化陈述：coeFn_fun_finsetProd [CommMonoid γ] [ContinuousMul γ] {ι : Type*} (s : Fin
set ι) (f : ι -> α ->ₘ[μ] γ) : ⇑(∏ i in s, f i) =ᵐ[μ] fun x => ∏ i in s, f i x
参数：s : Finset ι；f : ι -> α ->ₘ[μ] γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.GCongr.rel_imp_rel`：rel_imp_rel (h₁ : r c a) (h₂ : r b d)
 : r a b -> r c d
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `instIsTransOfTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [Trans r r r], I
sTrans α r
· 使用定理 `MeasureTheory.AEEqFun.coeFn_finsetProd`：coeFn_finsetProd [CommMonoid γ] 
[ContinuousMul γ] {ι : Type*} (s : Finset ι) (f : ι -> α ->ₘ[μ] γ) : ⇑(∏ i in s,
 f i) =ᵐ[μ] ∏ i in s, ⇑(f i)
· 使用定理 `Filter.EventuallyEq.refl`：∀ {α : Type u} {β : Type v} (l : Filter α) (f 
: α → β), f =ᶠ[l] f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_apply`：Finset.prod_apply {α : Type*} {M : α -> Type*} [foral
l a, CommMonoid (M a)] (a : α) (s : Finset ι) (g : ι -> forall a, M a) : (∏ c in
 s, g c…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coeFn_fun_finsetProd [CommMonoid γ] [ContinuousMul γ]
    {ι : Type*} (s : Finset ι) (f : ι → α →ₘ[μ] γ) :
    ⇑(∏ i ∈ s, f i) =ᵐ[μ] fun x ↦ ∏ i ∈ s, f i x := by
  grw [coeFn_finsetProd]
  filter_upwards with x using by simp

section Group

variable [Group γ] [IsTopologicalGroup γ]

section Inv

@[to_additive]
/-
**MeasureTheory.AEEqFun.instInv** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.AEEqFun
`。
形式化陈述：instInv : Inv (α ->ₘ[μ] γ)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instInv : Inv (α →ₘ[μ] γ) :=
  ⟨comp Inv.inv continuous_inv⟩

@[to_additive (attr := simp)]
/-
**MeasureTheory.AEEqFun.inv_mk** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.AEEqFun`
。
形式化陈述：inv_mk (f : α -> γ) (hf) : (mk f hf : α ->ₘ[μ] γ)⁻¹ = mk f⁻¹ hf.inv
参数：f : α -> γ；hf。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inv_mk (f : α → γ) (hf) : (mk f hf : α →ₘ[μ] γ)⁻¹ = mk f⁻¹ hf.inv :=
  rfl

@[to_additive]
/-
**MeasureTheory.AEEqFun.coeFn_inv** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.AEEqF
un`。
形式化陈述：coeFn_inv (f : α ->ₘ[μ] γ) : ⇑f⁻¹ =ᵐ[μ] f⁻¹
参数：f : α ->ₘ[μ] γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEEqFun.coeFn_comp`：coeFn_comp (g : β -> γ) (hg : Continuo
us g) (f : α ->ₘ[μ] β) : comp g hg f =ᵐ[μ] g ∘ f
-/
theorem coeFn_inv (f : α →ₘ[μ] γ) : ⇑f⁻¹ =ᵐ[μ] f⁻¹ :=
  coeFn_comp _ _ _

@[to_additive]
/-
**MeasureTheory.AEEqFun.inv_toGerm** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.AEEq
Fun`。
形式化陈述：inv_toGerm (f : α ->ₘ[μ] γ) : f⁻¹.toGerm = f.toGerm⁻¹
参数：f : α ->ₘ[μ] γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEEqFun.comp_toGerm`：comp_toGerm (g : β -> γ) (hg : Contin
uous g) (f : α ->ₘ[μ] β) : (comp g hg f).toGerm = f.toGerm.map g
-/
theorem inv_toGerm (f : α →ₘ[μ] γ) : f⁻¹.toGerm = f.toGerm⁻¹ :=
  comp_toGerm _ _ _

end Inv

section Div

@[to_additive]
/-
**MeasureTheory.AEEqFun.instDiv** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.AEEqFun
`。
形式化陈述：instDiv : Div (α ->ₘ[μ] γ)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instDiv : Div (α →ₘ[μ] γ) :=
  ⟨comp₂ Div.div continuous_div'⟩

@[to_additive (attr := simp)]
/-
**MeasureTheory.AEEqFun.mk_div** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.AEEqFun`
。
形式化陈述：mk_div (f g : α -> γ) (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeas
urable g μ) : mk (f / g) (hf.div hg) = (mk f hf : α ->ₘ[μ] γ) / mk g hg
参数：f g : α -> γ；hf : AEStronglyMeasurable f μ；hg : AEStronglyMeasurable g μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEStronglyMeasurable.div`：∀ {α : Type u_1} {β : Type u_2} 
[inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Measur
e α}   {f g : α → β} [inst_1…
-/
theorem mk_div (f g : α → γ) (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    mk (f / g) (hf.div hg) = (mk f hf : α →ₘ[μ] γ) / mk g hg :=
  rfl

@[to_additive]
/-
**MeasureTheory.AEEqFun.coeFn_div** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.AEEqF
un`。
形式化陈述：coeFn_div (f g : α ->ₘ[μ] γ) : ⇑(f / g) =ᵐ[μ] f / g
参数：f g : α ->ₘ[μ] γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEEqFun.coeFn_comp₂`：coeFn_comp₂ (g : β -> γ -> δ) (hg : C
ontinuous (uncurry g)) (f₁ : α ->ₘ[μ] β) (f₂ : α ->ₘ[μ] γ) : comp₂ g hg f₁ f₂ =ᵐ
[μ] fun a => g (f₁ a) (…
-/
theorem coeFn_div (f g : α →ₘ[μ] γ) : ⇑(f / g) =ᵐ[μ] f / g :=
  coeFn_comp₂ _ _ _ _

@[to_additive]
/-
**MeasureTheory.AEEqFun.div_toGerm** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.AEEq
Fun`。
形式化陈述：div_toGerm (f g : α ->ₘ[μ] γ) : (f / g).toGerm = f.toGerm / g.toGerm
参数：f g : α ->ₘ[μ] γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEEqFun.comp₂_toGerm`：comp₂_toGerm (g : β -> γ -> δ) (hg :
 Continuous (uncurry g)) (f₁ : α ->ₘ[μ] β) (f₂ : α ->ₘ[μ] γ) : (comp₂ g hg f₁ f₂
).toGerm = f₁.toGerm.map…
-/
theorem div_toGerm (f g : α →ₘ[μ] γ) : (f / g).toGerm = f.toGerm / g.toGerm :=
  comp₂_toGerm _ _ _ _

end Div

section ZPow

/-
**MeasureTheory.AEEqFun.instPowInt** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.AEEq
Fun`。
形式化陈述：instPowInt : Pow (α ->ₘ[μ] γ) Int
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_zpow`：∀ {G : Type w} [inst : TopologicalSpace G] [inst_1 : Gr
oup G] [IsTopologicalGroup G] (z : ℤ), Continuous fun a => a ^ z
-/
instance instPowInt : Pow (α →ₘ[μ] γ) ℤ :=
  ⟨fun f n => comp _ (continuous_zpow n) f⟩

@[simp]
/-
**MeasureTheory.AEEqFun.mk_zpow** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.AEEqFun
`。
形式化陈述：mk_zpow (f : α -> γ) (hf) (n : Int) : (mk f hf : α ->ₘ[μ] γ) ^ n = mk (f ^
 n) ((continuous_zpow n).comp_aestronglyMeasurable hf)
参数：f : α -> γ；hf；n : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_zpow (f : α → γ) (hf) (n : ℤ) :
    (mk f hf : α →ₘ[μ] γ) ^ n = mk (f ^ n) ((continuous_zpow n).comp_aestronglyMeasurable hf) :=
  rfl
/-
**MeasureTheory.AEEqFun.coeFn_zpow** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.AEEq
Fun`。
形式化陈述：coeFn_zpow (f : α ->ₘ[μ] γ) (n : Int) : ⇑(f ^ n) =ᵐ[μ] (⇑f) ^ n
参数：f : α ->ₘ[μ] γ；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEEqFun.coeFn_comp`：coeFn_comp (g : β -> γ) (hg : Continuo
us g) (f : α ->ₘ[μ] β) : comp g hg f =ᵐ[μ] g ∘ f
· 使用定理 `continuous_zpow`：∀ {G : Type w} [inst : TopologicalSpace G] [inst_1 : Gr
oup G] [IsTopologicalGroup G] (z : ℤ), Continuous fun a => a ^ z
-/
theorem coeFn_zpow (f : α →ₘ[μ] γ) (n : ℤ) : ⇑(f ^ n) =ᵐ[μ] (⇑f) ^ n :=
  coeFn_comp _ _ _

@[simp]
/-
**MeasureTheory.AEEqFun.zpow_toGerm** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.AEE
qFun`。
形式化陈述：zpow_toGerm (f : α ->ₘ[μ] γ) (n : Int) : (f ^ n).toGerm = f.toGerm ^ n
参数：f : α ->ₘ[μ] γ；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEEqFun.comp_toGerm`：comp_toGerm (g : β -> γ) (hg : Contin
uous g) (f : α ->ₘ[μ] β) : (comp g hg f).toGerm = f.toGerm.map g
· 使用定理 `continuous_zpow`：∀ {G : Type w} [inst : TopologicalSpace G] [inst_1 : Gr
oup G] [IsTopologicalGroup G] (z : ℤ), Continuous fun a => a ^ z
-/
theorem zpow_toGerm (f : α →ₘ[μ] γ) (n : ℤ) : (f ^ n).toGerm = f.toGerm ^ n :=
  comp_toGerm _ _ _

end ZPow

end Group

/-
**MeasureTheory.AEEqFun.instAddGroup** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.AE
EqFun`。
形式化陈述：instAddGroup [AddGroup γ] [IsTopologicalAddGroup γ] : AddGroup (α ->ₘ[μ] γ
)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `MeasureTheory.AEEqFun.toGerm_injective`：toGerm_injective : Injective (to
Germ : (α ->ₘ[μ] β) -> Germ (ae μ) β)
· 使用定理 `MeasureTheory.AEEqFun.neg_toGerm`：∀ {α : Type u_1} {γ : Type u_3} [inst 
: MeasurableSpace α] {μ : MeasureTheory.Measure α} [inst_1 : TopologicalSpace γ]
   [inst_2 : AddGroup …
· 使用定理 `MeasureTheory.AEEqFun.sub_toGerm`：∀ {α : Type u_1} {γ : Type u_3} [inst 
: MeasurableSpace α] {μ : MeasureTheory.Measure α} [inst_1 : TopologicalSpace γ]
   [inst_2 : AddGroup …
-/
instance instAddGroup [AddGroup γ] [IsTopologicalAddGroup γ] : AddGroup (α →ₘ[μ] γ) :=
  toGerm_injective.addGroup toGerm zero_toGerm add_toGerm neg_toGerm sub_toGerm
    (fun _ _ => smul_toGerm _ _) fun _ _ => smul_toGerm _ _
/-
**MeasureTheory.AEEqFun.instAddCommGroup** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheor
y.AEEqFun`。
形式化陈述：instAddCommGroup [AddCommGroup γ] [IsTopologicalAddGroup γ] : AddCommGroup
 (α ->ₘ[μ] γ)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAddCommGroup [AddCommGroup γ] [IsTopologicalAddGroup γ] : AddCommGroup (α →ₘ[μ] γ) :=
  { add_comm := add_comm }

@[to_additive existing]
/-
**MeasureTheory.AEEqFun.instGroup** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.AEEqF
un`。
形式化陈述：instGroup [Group γ] [IsTopologicalGroup γ] : Group (α ->ₘ[μ] γ)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `MeasureTheory.AEEqFun.toGerm_injective`：toGerm_injective : Injective (to
Germ : (α ->ₘ[μ] β) -> Germ (ae μ) β)
· 使用定理 `MeasureTheory.AEEqFun.inv_toGerm`：inv_toGerm (f : α ->ₘ[μ] γ) : f⁻¹.toGe
rm = f.toGerm⁻¹
· 使用定理 `MeasureTheory.AEEqFun.div_toGerm`：div_toGerm (f g : α ->ₘ[μ] γ) : (f / g
).toGerm = f.toGerm / g.toGerm
· 使用定理 `MeasureTheory.AEEqFun.zpow_toGerm`：zpow_toGerm (f : α ->ₘ[μ] γ) (n : Int
) : (f ^ n).toGerm = f.toGerm ^ n
-/
instance instGroup [Group γ] [IsTopologicalGroup γ] : Group (α →ₘ[μ] γ) :=
  toGerm_injective.group _ one_toGerm mul_toGerm inv_toGerm div_toGerm pow_toGerm zpow_toGerm

@[to_additive existing]
/-
**MeasureTheory.AEEqFun.instCommGroup** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.A
EEqFun`。
形式化陈述：instCommGroup [CommGroup γ] [IsTopologicalGroup γ] : CommGroup (α ->ₘ[μ] γ
)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCommGroup [CommGroup γ] [IsTopologicalGroup γ] : CommGroup (α →ₘ[μ] γ) :=
  { mul_comm := mul_comm }

section Module

variable {𝕜 : Type*}

/-
**MeasureTheory.AEEqFun.instMulAction** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.A
EEqFun`。
形式化陈述：instMulAction [Monoid 𝕜] [MulAction 𝕜 γ] [ContinuousConstSMul 𝕜 γ] : MulAc
tion 𝕜 (α ->ₘ[μ] γ)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.AEEqFun.toGerm_injective`：toGerm_injective : Injective (to
Germ : (α ->ₘ[μ] β) -> Germ (ae μ) β)
-/
instance instMulAction [Monoid 𝕜] [MulAction 𝕜 γ] [ContinuousConstSMul 𝕜 γ] :
    MulAction 𝕜 (α →ₘ[μ] γ) :=
  toGerm_injective.mulAction toGerm smul_toGerm
/-
**MeasureTheory.AEEqFun.instDistribMulAction** 是 Mathlib 中的一个实例，位于命名空间 `MeasureT
heory.AEEqFun`。
形式化陈述：instDistribMulAction [Monoid 𝕜] [AddMonoid γ] [ContinuousAdd γ] [DistribMu
lAction 𝕜 γ] [ContinuousConstSMul 𝕜 γ] : DistribMulAction 𝕜 (α ->ₘ[μ] γ)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.AEEqFun.toGerm_injective`：toGerm_injective : Injective (to
Germ : (α ->ₘ[μ] β) -> Germ (ae μ) β)
-/
instance instDistribMulAction [Monoid 𝕜] [AddMonoid γ] [ContinuousAdd γ] [DistribMulAction 𝕜 γ]
    [ContinuousConstSMul 𝕜 γ] : DistribMulAction 𝕜 (α →ₘ[μ] γ) :=
  toGerm_injective.distribMulAction (toGermAddMonoidHom : (α →ₘ[μ] γ) →+ _) fun c : 𝕜 =>
    smul_toGerm c
/-
**MeasureTheory.AEEqFun.instModule** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.AEEq
Fun`。
形式化陈述：instModule [Semiring 𝕜] [AddCommMonoid γ] [ContinuousAdd γ] [Module 𝕜 γ] [
ContinuousConstSMul 𝕜 γ] : Module 𝕜 (α ->ₘ[μ] γ)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.AEEqFun.toGerm_injective`：toGerm_injective : Injective (to
Germ : (α ->ₘ[μ] β) -> Germ (ae μ) β)
-/
instance instModule [Semiring 𝕜] [AddCommMonoid γ] [ContinuousAdd γ] [Module 𝕜 γ]
    [ContinuousConstSMul 𝕜 γ] : Module 𝕜 (α →ₘ[μ] γ) :=
  toGerm_injective.module 𝕜 (toGermAddMonoidHom : (α →ₘ[μ] γ) →+ _) smul_toGerm

end Module

open ENNReal

/-- For `f : α → ℝ≥0∞`, define `∫ [f]` to be `∫ f` -/
/-
**MeasureTheory.AEEqFun.lintegral** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.AEEqF
un`。
形式化陈述：lintegral (f : α ->ₘ[μ] Real>=0∞) : Real>=0∞
参数：f : α ->ₘ[μ] Real>=0∞。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For `f : α → ℝ≥0∞`, define `∫ [f]` to be `∫ f`
-/
def lintegral (f : α →ₘ[μ] ℝ≥0∞) : ℝ≥0∞ :=
  Quotient.liftOn' f (fun f => ∫⁻ a, (f : α → ℝ≥0∞) a ∂μ) fun _ _ => lintegral_congr_ae

@[simp]
/-
**MeasureTheory.AEEqFun.lintegral_mk** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.AE
EqFun`。
形式化陈述：lintegral_mk (f : α -> Real>=0∞) (hf) : (mk f hf : α ->ₘ[μ] Real>=0∞).lint
egral = ∫⁻ a, f a ∂μ
参数：f : α -> Real>=0∞；hf。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lintegral_mk (f : α → ℝ≥0∞) (hf) : (mk f hf : α →ₘ[μ] ℝ≥0∞).lintegral = ∫⁻ a, f a ∂μ :=
  rfl
/-
**MeasureTheory.AEEqFun.lintegral_coeFn** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.AEEqFun`。
形式化陈述：lintegral_coeFn (f : α ->ₘ[μ] Real>=0∞) : ∫⁻ a, f a ∂μ = f.lintegral
参数：f : α ->ₘ[μ] Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEEqFun.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u
_2} [inst : MeasurableSpace α] {μ : MeasureTheory.Measure α} [inst_1 : Topologic
alSpace β]   (f : α →ₘ[μ] β), Me…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.AEEqFun.lintegral_mk`：lintegral_mk (f : α -> Real>=0∞) (hf
) : (mk f hf : α ->ₘ[μ] Real>=0∞).lintegral = ∫⁻ a, f a ∂μ
· 使用定理 `MeasureTheory.AEEqFun.mk_coeFn`：mk_coeFn (f : α ->ₘ[μ] β) : mk f f.aestr
onglyMeasurable = f
-/
theorem lintegral_coeFn (f : α →ₘ[μ] ℝ≥0∞) : ∫⁻ a, f a ∂μ = f.lintegral := by
  rw [← lintegral_mk (hf := f.aestronglyMeasurable), mk_coeFn]

@[simp]
nonrec theorem lintegral_zero : lintegral (0 : α →ₘ[μ] ℝ≥0∞) = 0 :=
  lintegral_zero

@[simp]
/-
**MeasureTheory.AEEqFun.lintegral_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.AEEqFun`。
形式化陈述：lintegral_eq_zero_iff {f : α ->ₘ[μ] Real>=0∞} : lintegral f = 0 ↔ f = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEEqFun.induction_on`：induction_on (f : α ->ₘ[μ] β) {p : (
α ->ₘ[μ] β) -> Prop} (H : forall f hf, p (mk f hf)) : p f
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.lintegral_eq_zero_iff'`：lintegral_eq_zero_iff' {f : α -> R
eal>=0∞} (hf : AEMeasurable f μ) : ∫⁻ a, f a ∂μ = 0 ↔ f =ᵐ[μ] 0
· 使用定理 `MeasureTheory.AEStronglyMeasurable.aemeasurable`：∀ {α : Type u_1} {m₀ : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} {β : Type u_5} [inst : Measurab
leSpace β]   [inst_1 : TopologicalSpa…
· 使用定理 `TopologicalSpace.MetrizableSpace.toPseudoMetrizableSpace`：∀ {X : Type u_
5} {t : TopologicalSpace X} [self : TopologicalSpace.MetrizableSpace X],   Topol
ogicalSpace.PseudoMetrizableSpace X
· 使用定理 `ENNReal.instMetrizableSpace`：TopologicalSpace.MetrizableSpace ENNReal
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `MeasureTheory.aestronglyMeasurable_const`：aestronglyMeasurable_const {b 
: β} : AEStronglyMeasurable[m] (fun _ : α => b) μ
· 使用定理 `MeasureTheory.AEEqFun.mk_eq_mk`：mk_eq_mk {f g : α -> β} {hf hg} : (mk f 
hf : α ->ₘ[μ] β) = mk g hg ↔ f =ᵐ[μ] g
-/
theorem lintegral_eq_zero_iff {f : α →ₘ[μ] ℝ≥0∞} : lintegral f = 0 ↔ f = 0 :=
  induction_on f fun _f hf => (lintegral_eq_zero_iff' hf.aemeasurable).trans mk_eq_mk.symm
/-
**MeasureTheory.AEEqFun.lintegral_add** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.A
EEqFun`。
形式化陈述：lintegral_add (f g : α ->ₘ[μ] Real>=0∞) : lintegral (f + g) = lintegral f 
+ lintegral g
参数：f g : α ->ₘ[μ] Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEEqFun.induction_on₂`：induction_on₂ {α' β' : Type*} [Meas
urableSpace α'] [TopologicalSpace β'] {μ' : Measure α'} (f : α ->ₘ[μ] β) (f' : α
' ->ₘ[μ'] β') {p : (α ->ₘ…
· 使用定理 `ENNReal.instContinuousAdd`：ContinuousAdd ENNReal
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lintegral_add_left'`：lintegral_add_left' {f : α -> Real>=0
∞} (hf : AEMeasurable f μ) (g : α -> Real>=0∞) : ∫⁻ a, f a + g a ∂μ = ∫⁻ a, f a 
∂μ + ∫⁻ a, g a ∂μ
· 使用定理 `MeasureTheory.AEStronglyMeasurable.aemeasurable`：∀ {α : Type u_1} {m₀ : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} {β : Type u_5} [inst : Measurab
leSpace β]   [inst_1 : TopologicalSpa…
· 使用定理 `TopologicalSpace.MetrizableSpace.toPseudoMetrizableSpace`：∀ {X : Type u_
5} {t : TopologicalSpace X} [self : TopologicalSpace.MetrizableSpace X],   Topol
ogicalSpace.PseudoMetrizableSpace X
· 使用定理 `ENNReal.instMetrizableSpace`：TopologicalSpace.MetrizableSpace ENNReal
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lintegral_add (f g : α →ₘ[μ] ℝ≥0∞) : lintegral (f + g) = lintegral f + lintegral g :=
  induction_on₂ f g fun f hf g _ => by simp [lintegral_add_left' hf.aemeasurable]
/-
**MeasureTheory.AEEqFun.lintegral_mono** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
AEEqFun`。
形式化陈述：lintegral_mono {f g : α ->ₘ[μ] Real>=0∞} : f <= g -> lintegral f <= linteg
ral g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEEqFun.induction_on₂`：induction_on₂ {α' β' : Type*} [Meas
urableSpace α'] [TopologicalSpace β'] {μ' : Measure α'} (f : α ->ₘ[μ] β) (f' : α
' ->ₘ[μ'] β') {p : (α ->ₘ…
· 使用定理 `MeasureTheory.lintegral_mono_ae`：lintegral_mono_ae {f g : α -> Real>=0∞}
 (h : forallᵐ a ∂μ, f a <= g a) : ∫⁻ a, f a ∂μ <= ∫⁻ a, g a ∂μ
-/
theorem lintegral_mono {f g : α →ₘ[μ] ℝ≥0∞} : f ≤ g → lintegral f ≤ lintegral g :=
  induction_on₂ f g fun _f _ _g _ hfg => lintegral_mono_ae hfg

section Abs

/-
**MeasureTheory.AEEqFun.coeFn_abs** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.AEEqF
un`。
形式化陈述：coeFn_abs {β} [TopologicalSpace β] [Lattice β] [TopologicalLattice β] [Add
Group β] [IsTopologicalAddGroup β] (f : α ->ₘ[μ] β) : ⇑|f| =ᵐ[μ] fun x => |f x|
参数：f : α ->ₘ[μ] β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.AEEqFun.coeFn_neg`：∀ {α : Type u_1} {γ : Type u_3} [inst :
 MeasurableSpace α] {μ : MeasureTheory.Measure α} [inst_1 : TopologicalSpace γ] 
  [inst_2 : AddGroup …
· 使用定理 `TopologicalLattice.toContinuousSup`：∀ {L : Type u_1} {inst : Topological
Space L} {inst_1 : Lattice L} [self : TopologicalLattice L], ContinuousSup L
· 使用定理 `MeasureTheory.AEEqFun.coeFn_sup`：coeFn_sup (f g : α ->ₘ[μ] β) : ⇑(f ⊔ g)
 =ᵐ[μ] fun x => f x ⊔ g x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Pi.neg_apply`：∀ {ι : Type u_1} {G : ι → Type u_4} [inst : (i : ι) → Neg 
(G i)] (f : (i : ι) → G i) (i : ι), (-f) i = -f i
-/
theorem coeFn_abs {β} [TopologicalSpace β] [Lattice β] [TopologicalLattice β] [AddGroup β]
    [IsTopologicalAddGroup β] (f : α →ₘ[μ] β) : ⇑|f| =ᵐ[μ] fun x => |f x| := by
  simp_rw [abs]
  filter_upwards [AEEqFun.coeFn_sup f (-f), AEEqFun.coeFn_neg f] with x hx_sup hx_neg
  rw [hx_sup, hx_neg, Pi.neg_apply]

end Abs

section Star

variable {R : Type*} [TopologicalSpace R]

/-
**MeasureTheory.AEEqFun.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.AEEqFun`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Star R] [ContinuousStar R] : Star (α →ₘ[μ] R) where
  star f := (AEEqFun.comp _ continuous_star f)
/-
**MeasureTheory.AEEqFun.coeFn_star** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.AEEq
Fun`。
形式化陈述：coeFn_star [Star R] [ContinuousStar R] (f : α ->ₘ[μ] R) : ↑(star f) =ᵐ[μ] 
(star f : α -> R)
参数：f : α ->ₘ[μ] R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEEqFun.coeFn_comp`：coeFn_comp (g : β -> γ) (hg : Continuo
us g) (f : α ->ₘ[μ] β) : comp g hg f =ᵐ[μ] g ∘ f
· 使用定理 `ContinuousStar.continuous_star`：∀ {R : Type u_1} {inst : TopologicalSpac
e R} {inst_1 : Star R} [self : ContinuousStar R], Continuous star
-/
lemma coeFn_star [Star R] [ContinuousStar R] (f : α →ₘ[μ] R) : ↑(star f) =ᵐ[μ] (star f : α → R) :=
  coeFn_comp _ (continuous_star) f
/-
**MeasureTheory.AEEqFun.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.AEEqFun`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [InvolutiveStar R] [ContinuousStar R] : InvolutiveStar (α →ₘ[μ] R) where
  star_involutive f := comp_comp _ _ _ _ f |>.trans <| by simp [star_involutive.comp_self]
/-
**MeasureTheory.AEEqFun.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.AEEqFun`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Star R] [TrivialStar R] [ContinuousStar R] : TrivialStar (α →ₘ[μ] R) where
  star_trivial f := show comp _ _ f = f by simp [funext star_trivial, ← Function.id_def]

end Star

section PosPart

variable [LinearOrder γ] [OrderClosedTopology γ] [Zero γ]

/-- Positive part of an `AEEqFun`. -/
/-
**MeasureTheory.AEEqFun.posPart** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.AEEqFun
`。
形式化陈述：posPart (f : α ->ₘ[μ] γ) : α ->ₘ[μ] γ
参数：f : α ->ₘ[μ] γ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Positive part of an `AEEqFun`.
-/
def posPart (f : α →ₘ[μ] γ) : α →ₘ[μ] γ :=
  comp (fun x => max x 0) (by fun_prop) f

@[simp]
/-
**MeasureTheory.AEEqFun.posPart_mk** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.AEEq
Fun`。
形式化陈述：posPart_mk (f : α -> γ) (hf) : posPart (mk f hf : α ->ₘ[μ] γ) = mk (fun x 
=> max (f x) 0) (by fun_prop)
参数：f : α -> γ；hf。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem posPart_mk (f : α → γ) (hf) :
    posPart (mk f hf : α →ₘ[μ] γ) = mk (fun x ↦ max (f x) 0) (by fun_prop) :=
  rfl
/-
**MeasureTheory.AEEqFun.coeFn_posPart** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.A
EEqFun`。
形式化陈述：coeFn_posPart (f : α ->ₘ[μ] γ) : ⇑(posPart f) =ᵐ[μ] fun a => max (f a) 0
参数：f : α ->ₘ[μ] γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEEqFun.coeFn_comp`：coeFn_comp (g : β -> γ) (hg : Continuo
us g) (f : α ->ₘ[μ] β) : comp g hg f =ᵐ[μ] g ∘ f
-/
theorem coeFn_posPart (f : α →ₘ[μ] γ) : ⇑(posPart f) =ᵐ[μ] fun a => max (f a) 0 :=
  coeFn_comp _ _ _

end PosPart

section AELimit

/-- The ae-limit is ae-unique. -/
/-
**MeasureTheory.AEEqFun.tendsto_ae_unique** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.AEEqFun`。
形式化陈述：tendsto_ae_unique {ι : Type*} [T2Space β] {g h : α -> β} {f : ι -> α -> β}
 {l : Filter ι} [l.NeBot] (hg : forallᵐ ω ∂μ, Tendsto (fun i => f i ω) l (𝓝 (g ω
))) (hh : forallᵐ ω ∂μ, Tendsto (fun i => f i ω) l (𝓝 (h ω))) : g =ᵐ[μ] h
参数：hg : forallᵐ ω ∂μ, Tendsto (fun i => f i ω) l (𝓝 (g ω))；hh : forallᵐ ω ∂μ, Te
ndsto (fun i => f i ω) l (𝓝 (h ω))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `tendsto_nhds_unique`：tendsto_nhds_unique [T2Space X] {f : Y -> X} {l : F
ilter Y} {a b : X} [NeBot l] (ha : Tendsto f l (𝓝 a)) (hb : Tendsto f l (𝓝 b)) :
 a = b

--- 原说明 ---
The ae-limit is ae-unique.
-/
theorem tendsto_ae_unique {ι : Type*} [T2Space β]
    {g h : α → β} {f : ι → α → β} {l : Filter ι} [l.NeBot]
    (hg : ∀ᵐ ω ∂μ, Tendsto (fun i => f i ω) l (𝓝 (g ω)))
    (hh : ∀ᵐ ω ∂μ, Tendsto (fun i => f i ω) l (𝓝 (h ω))) : g =ᵐ[μ] h := by
  filter_upwards [hg, hh] with ω hg1 hh1 using tendsto_nhds_unique hg1 hh1

end AELimit

end AEEqFun

end MeasureTheory

namespace ContinuousMap

open MeasureTheory

variable [TopologicalSpace α] [BorelSpace α] (μ)
variable [TopologicalSpace β] [SecondCountableTopologyEither α β] [PseudoMetrizableSpace β]

/-- The equivalence class of `μ`-almost-everywhere measurable functions associated to a continuous
map. -/
/-
**ContinuousMap.toAEEqFun** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMap`。
形式化陈述：toAEEqFun (f : C(α, β)) : α ->ₘ[μ] β
参数：f : C(α, β)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence class of `μ`-almost-everywhere measurable functions associated t
o a continuous
map.
-/
def toAEEqFun (f : C(α, β)) : α →ₘ[μ] β :=
  AEEqFun.mk f f.continuous.aestronglyMeasurable
/-
**ContinuousMap.coeFn_toAEEqFun** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousMap`。
形式化陈述：coeFn_toAEEqFun (f : C(α, β)) : f.toAEEqFun μ =ᵐ[μ] f
参数：f : C(α, β)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEEqFun.coeFn_mk`：coeFn_mk (f : α -> β) (hf) : (mk f hf : 
α ->ₘ[μ] β) =ᵐ[μ] f
-/
theorem coeFn_toAEEqFun (f : C(α, β)) : f.toAEEqFun μ =ᵐ[μ] f :=
  AEEqFun.coeFn_mk f _

variable [Group β] [IsTopologicalGroup β]

/-- The `MulHom` from the group of continuous maps from `α` to `β` to the group of equivalence
classes of `μ`-almost-everywhere measurable functions. -/
@[to_additive /-- The `AddHom` from the group of continuous maps from `α` to `β` to the group of
equivalence classes of `μ`-almost-everywhere measurable functions. -/]
/-
**ContinuousMap.toAEEqFunMulHom** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMap`。
形式化陈述：toAEEqFunMulHom : C(α, β) ->* α ->ₘ[μ] β where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
-/
def toAEEqFunMulHom : C(α, β) →* α →ₘ[μ] β where
  toFun := ContinuousMap.toAEEqFun μ
  map_one' := rfl
  map_mul' f g :=
    AEEqFun.mk_mul_mk _ _ f.continuous.aestronglyMeasurable g.continuous.aestronglyMeasurable

variable {𝕜 : Type*} [Semiring 𝕜]
variable [TopologicalSpace γ] [PseudoMetrizableSpace γ] [AddCommGroup γ] [Module 𝕜 γ]
  [IsTopologicalAddGroup γ] [ContinuousConstSMul 𝕜 γ] [SecondCountableTopologyEither α γ]

/-- The linear map from the group of continuous maps from `α` to `β` to the group of equivalence
classes of `μ`-almost-everywhere measurable functions. -/
/-
**ContinuousMap.toAEEqFunLinearMap** 是 Mathlib 中的一个定义，位于命名空间 `ContinuousMap`。
形式化陈述：toAEEqFunLinearMap : C(α, γ) ->ₗ[𝕜] α ->ₘ[μ] γ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The linear map from the group of continuous maps from `α` to `β` to the group of
 equivalence
classes of `μ`-almost-everywhere measurable functions.
-/
def toAEEqFunLinearMap : C(α, γ) →ₗ[𝕜] α →ₘ[μ] γ :=
  { toAEEqFunAddHom μ with
    map_smul' := fun c f => AEEqFun.smul_mk c f f.continuous.aestronglyMeasurable }

end ContinuousMap

