/-
Copyright (c) 2019 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Tactic.FieldSimp

/-!
# Jensen's inequality and maximum principle for convex functions

In this file, we prove the finite Jensen inequality and the finite maximum principle for convex
functions. The integral versions are to be found in `Analysis.Convex.Integral`.

## Main declarations

Jensen's inequalities:
* `ConvexOn.map_centerMass_le`, `ConvexOn.map_sum_le`: Convex Jensen's inequality. The image of a
  convex combination of points under a convex function is less than the convex combination of the
  images.
* `ConcaveOn.le_map_centerMass`, `ConcaveOn.le_map_sum`: Concave Jensen's inequality.
* `StrictConvexOn.map_sum_lt`: Convex strict Jensen inequality.
* `StrictConcaveOn.lt_map_sum`: Concave strict Jensen inequality.

As corollaries, we get:
* `StrictConvexOn.map_sum_eq_iff`: Equality case of the convex Jensen inequality.
* `StrictConcaveOn.map_sum_eq_iff`: Equality case of the concave Jensen inequality.
* `ConvexOn.exists_ge_of_mem_convexHull`: Maximum principle for convex functions.
* `ConcaveOn.exists_le_of_mem_convexHull`: Minimum principle for concave functions.
-/

public section


open Finset LinearMap Set Convex Pointwise

variable {𝕜 E F β ι : Type*}

/-! ### Jensen's inequality -/


section Jensen

variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup E] [AddCommGroup β]
  [PartialOrder β] [IsOrderedAddMonoid β] [Module 𝕜 E] [Module 𝕜 β] [IsStrictOrderedModule 𝕜 β]
  {s : Set E} {f : E → β} {t : Finset ι} {w : ι → 𝕜} {p : ι → E} {v : 𝕜} {q : E}

/-- Convex **Jensen's inequality**, `Finset.centerMass` version. -/
/-
**ConvexOn.map_centerMass_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ConvexOn.map_centerMass_le (hf : ConvexOn 𝕜 s f) (h₀ : forall i in t, 0 <=
 w i) (h₁ : 0 < ∑ i in t, w i) (hmem : forall i in t, p i in s) : f (t.centerMas
s w p) <= t.centerMass w (f ∘ p)
参数：hf : ConvexOn 𝕜 s f；h₀ : forall i in t, 0 <= w i；h₁ : 0 < ∑ i in t, w i；hmem 
: forall i in t, p i in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Prod.fst_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : Add
CommMonoid M] [inst_1 : AddCommMonoid N] {s : Finset ι}   {f : ι → M × N}, (∑ c 
∈ …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Prod.snd_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : Add
CommMonoid M] [inst_1 : AddCommMonoid N] {s : Finset ι}   {f : ι → M × N}, (∑ c 
∈ …
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Convex.centerMass_mem`：Convex.centerMass_mem (hs : Convex R s) : (forall
 i in t, 0 <= w i) -> (0 < ∑ i in t, w i) -> (forall i in t, z i in s) -> t.cent
erMass w z …
· 使用定理 `ConvexOn.convex_epigraph`：ConvexOn.convex_epigraph (hf : ConvexOn 𝕜 s f)
 : Convex 𝕜 { p : E × β | p.1 in s ∧ f p.1 <= p.2 }
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…

--- 原说明 ---
Convex **Jensen's inequality**, `Finset.centerMass` version.
-/
theorem ConvexOn.map_centerMass_le (hf : ConvexOn 𝕜 s f) (h₀ : ∀ i ∈ t, 0 ≤ w i)
    (h₁ : 0 < ∑ i ∈ t, w i) (hmem : ∀ i ∈ t, p i ∈ s) :
    f (t.centerMass w p) ≤ t.centerMass w (f ∘ p) := by
  have hmem' : ∀ i ∈ t, (p i, (f ∘ p) i) ∈ { p : E × β | p.1 ∈ s ∧ f p.1 ≤ p.2 } := fun i hi =>
    ⟨hmem i hi, le_rfl⟩
  convert! (hf.convex_epigraph.centerMass_mem h₀ h₁ hmem').2 <;>
    simp only [centerMass, Function.comp, Prod.smul_fst, Prod.fst_sum, Prod.smul_snd, Prod.snd_sum]

/-- Concave **Jensen's inequality**, `Finset.centerMass` version. -/
/-
**ConcaveOn.le_map_centerMass** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ConcaveOn.le_map_centerMass (hf : ConcaveOn 𝕜 s f) (h₀ : forall i in t, 0 
<= w i) (h₁ : 0 < ∑ i in t, w i) (hmem : forall i in t, p i in s) : t.centerMass
 w (f ∘ p) <= f (t.centerMass w p)
参数：hf : ConcaveOn 𝕜 s f；h₀ : forall i in t, 0 <= w i；h₁ : 0 < ∑ i in t, w i；hmem
 : forall i in t, p i in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ConvexOn.map_centerMass_le`：ConvexOn.map_centerMass_le (hf : ConvexOn 𝕜 
s f) (h₀ : forall i in t, 0 <= w i) (h₁ : 0 < ∑ i in t, w i) (hmem : forall i in
 t, p i in s) : …
· 使用定理 `OrderDual.isOrderedAddMonoid`：∀ {α : Type u} [inst : AddCommMonoid α] [i
nst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedAddMonoid αᵒᵈ
· 使用定理 `OrderDual.instIsStrictOrderedModule`：∀ {α : Type u_1} {β : Type u_2} [in
st : Preorder α] [inst_1 : MonoidWithZero α] [inst_2 : AddCommGroup β]   [inst_3
 : PartialOrder β] [IsOrd…

--- 原说明 ---
Concave **Jensen's inequality**, `Finset.centerMass` version.
-/
theorem ConcaveOn.le_map_centerMass (hf : ConcaveOn 𝕜 s f) (h₀ : ∀ i ∈ t, 0 ≤ w i)
    (h₁ : 0 < ∑ i ∈ t, w i) (hmem : ∀ i ∈ t, p i ∈ s) :
    t.centerMass w (f ∘ p) ≤ f (t.centerMass w p) :=
  ConvexOn.map_centerMass_le (β := βᵒᵈ) hf h₀ h₁ hmem

/-- Convex **Jensen's inequality**, `Finset.sum` version. -/
/-
**ConvexOn.map_sum_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ConvexOn.map_sum_le (hf : ConvexOn 𝕜 s f) (h₀ : forall i in t, 0 <= w i) (
h₁ : ∑ i in t, w i = 1) (hmem : forall i in t, p i in s) : f (∑ i in t, w i • p 
i) <= ∑ i in t, w i • f (p i)
参数：hf : ConvexOn 𝕜 s f；h₀ : forall i in t, 0 <= w i；h₁ : ∑ i in t, w i = 1；hmem 
: forall i in t, p i in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `ConvexOn.map_centerMass_le`：ConvexOn.map_centerMass_le (hf : ConvexOn 𝕜 
s f) (h₀ : forall i in t, 0 <= w i) (h₁ : 0 < ∑ i in t, w i) (hmem : forall i in
 t, p i in s) : …
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
Convex **Jensen's inequality**, `Finset.sum` version.
-/
theorem ConvexOn.map_sum_le (hf : ConvexOn 𝕜 s f) (h₀ : ∀ i ∈ t, 0 ≤ w i) (h₁ : ∑ i ∈ t, w i = 1)
    (hmem : ∀ i ∈ t, p i ∈ s) : f (∑ i ∈ t, w i • p i) ≤ ∑ i ∈ t, w i • f (p i) := by
  simpa only [centerMass, h₁, inv_one, one_smul] using!
    hf.map_centerMass_le h₀ (h₁.symm ▸ zero_lt_one) hmem

/-- Concave **Jensen's inequality**, `Finset.sum` version. -/
/-
**ConcaveOn.le_map_sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ConcaveOn.le_map_sum (hf : ConcaveOn 𝕜 s f) (h₀ : forall i in t, 0 <= w i)
 (h₁ : ∑ i in t, w i = 1) (hmem : forall i in t, p i in s) : (∑ i in t, w i • f 
(p i)) <= f (∑ i in t, w i • p i)
参数：hf : ConcaveOn 𝕜 s f；h₀ : forall i in t, 0 <= w i；h₁ : ∑ i in t, w i = 1；hmem
 : forall i in t, p i in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ConvexOn.map_sum_le`：ConvexOn.map_sum_le (hf : ConvexOn 𝕜 s f) (h₀ : for
all i in t, 0 <= w i) (h₁ : ∑ i in t, w i = 1) (hmem : forall i in t, p i in s) 
: f (∑ i …
· 使用定理 `OrderDual.isOrderedAddMonoid`：∀ {α : Type u} [inst : AddCommMonoid α] [i
nst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedAddMonoid αᵒᵈ
· 使用定理 `OrderDual.instIsStrictOrderedModule`：∀ {α : Type u_1} {β : Type u_2} [in
st : Preorder α] [inst_1 : MonoidWithZero α] [inst_2 : AddCommGroup β]   [inst_3
 : PartialOrder β] [IsOrd…

--- 原说明 ---
Concave **Jensen's inequality**, `Finset.sum` version.
-/
theorem ConcaveOn.le_map_sum (hf : ConcaveOn 𝕜 s f) (h₀ : ∀ i ∈ t, 0 ≤ w i)
    (h₁ : ∑ i ∈ t, w i = 1) (hmem : ∀ i ∈ t, p i ∈ s) :
    (∑ i ∈ t, w i • f (p i)) ≤ f (∑ i ∈ t, w i • p i) :=
  ConvexOn.map_sum_le (β := βᵒᵈ) hf h₀ h₁ hmem

/-- Convex **Jensen's inequality** where an element plays a distinguished role. -/
/-
**ConvexOn.map_add_sum_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ConvexOn.map_add_sum_le (hf : ConvexOn 𝕜 s f) (h₀ : forall i in t, 0 <= w 
i) (h₁ : v + ∑ i in t, w i = 1) (hmem : forall i in t, p i in s) (hv : 0 <= v) (
hq : q in s) : f (v • q + ∑ i in t, w i • p i) <= v • f q + ∑ i in t, w i • f (p
 i)
参数：hf : ConvexOn 𝕜 s f；h₀ : forall i in t, 0 <= w i；h₁ : v + ∑ i in t, w i = 1；h
mem : forall i in t, p i in s；hv : 0 <= v；hq : q in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ConvexOn.map_sum_le`：ConvexOn.map_sum_le (hf : ConvexOn 𝕜 s f) (h₀ : for
all i in t, 0 <= w i) (h₁ : ∑ i in t, w i = 1) (hmem : forall i in t, p i in s) 
: f (∑ i …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Finset.forall_mem_insertNone`：forall_mem_insertNone {s : Finset α} {p : 
Option α -> Prop} : (forall a in insertNone s, p a) ↔ p none ∧ forall a in s, p 
a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_insertNone`：∀ {α : Type u_1} {M : Type u_2} [inst : AddCommMo
noid M] (f : Option α → M) (s : Finset α),   ∑ x ∈ Finset.insertNone s, f x = f 
none + ∑ x …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂

--- 原说明 ---
Convex **Jensen's inequality** where an element plays a distinguished role.
-/
lemma ConvexOn.map_add_sum_le (hf : ConvexOn 𝕜 s f) (h₀ : ∀ i ∈ t, 0 ≤ w i)
    (h₁ : v + ∑ i ∈ t, w i = 1) (hmem : ∀ i ∈ t, p i ∈ s) (hv : 0 ≤ v) (hq : q ∈ s) :
    f (v • q + ∑ i ∈ t, w i • p i) ≤ v • f q + ∑ i ∈ t, w i • f (p i) := by
  let W j := Option.elim j v w
  let P j := Option.elim j q p
  have : f (∑ j ∈ insertNone t, W j • P j) ≤ ∑ j ∈ insertNone t, W j • f (P j) :=
    hf.map_sum_le (forall_mem_insertNone.2 ⟨hv, h₀⟩) (by simpa using! h₁)
      (forall_mem_insertNone.2 ⟨hq, hmem⟩)
  simpa using! this

/-- Concave **Jensen's inequality** where an element plays a distinguished role. -/
/-
**ConcaveOn.map_add_sum_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ConcaveOn.map_add_sum_le (hf : ConcaveOn 𝕜 s f) (h₀ : forall i in t, 0 <= 
w i) (h₁ : v + ∑ i in t, w i = 1) (hmem : forall i in t, p i in s) (hv : 0 <= v)
 (hq : q in s) : v • f q + ∑ i in t, w i • f (p i) <= f (v • q + ∑ i in t, w i •
 p i)
参数：hf : ConcaveOn 𝕜 s f；h₀ : forall i in t, 0 <= w i；h₁ : v + ∑ i in t, w i = 1；
hmem : forall i in t, p i in s；hv : 0 <= v；hq : q in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ConvexOn.map_add_sum_le`：ConvexOn.map_add_sum_le (hf : ConvexOn 𝕜 s f) (
h₀ : forall i in t, 0 <= w i) (h₁ : v + ∑ i in t, w i = 1) (hmem : forall i in t
, p i in s) (…
· 使用定理 `OrderDual.isOrderedAddMonoid`：∀ {α : Type u} [inst : AddCommMonoid α] [i
nst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedAddMonoid αᵒᵈ
· 使用定理 `OrderDual.instIsStrictOrderedModule`：∀ {α : Type u_1} {β : Type u_2} [in
st : Preorder α] [inst_1 : MonoidWithZero α] [inst_2 : AddCommGroup β]   [inst_3
 : PartialOrder β] [IsOrd…
· 使用定理 `ConcaveOn.dual`：ConcaveOn.dual (hf : ConcaveOn 𝕜 s f) : ConvexOn 𝕜 s (to
Dual ∘ f)

--- 原说明 ---
Concave **Jensen's inequality** where an element plays a distinguished role.
-/
lemma ConcaveOn.map_add_sum_le (hf : ConcaveOn 𝕜 s f) (h₀ : ∀ i ∈ t, 0 ≤ w i)
    (h₁ : v + ∑ i ∈ t, w i = 1) (hmem : ∀ i ∈ t, p i ∈ s) (hv : 0 ≤ v) (hq : q ∈ s) :
    v • f q + ∑ i ∈ t, w i • f (p i) ≤ f (v • q + ∑ i ∈ t, w i • p i) :=
  hf.dual.map_add_sum_le h₀ h₁ hmem hv hq

/-! ### Strict Jensen inequality -/

/-- Convex **strict Jensen inequality**.

If the function is strictly convex, the weights are strictly positive and the indexed family of
points is non-constant, then Jensen's inequality is strict.

See also `StrictConvexOn.map_sum_eq_iff`. -/
/-
**StrictConvexOn.map_sum_lt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StrictConvexOn.map_sum_lt (hf : StrictConvexOn 𝕜 s f) (h₀ : forall i in t,
 0 < w i) (h₁ : ∑ i in t, w i = 1) (hmem : forall i in t, p i in s) (hp : exists
 j in t, exists k in t, p j != p k) : f (∑ i in t, w i • p i) < ∑ i in t, w i • 
f (p i)
参数：hf : StrictConvexOn 𝕜 s f；h₀ : forall i in t, 0 < w i；h₁ : ∑ i in t, w i = 1；
hmem : forall i in t, p i in s；hp : exists j in t, exists k in t, p j != p k。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_erase`：mem_erase {a b : α} {s : Finset α} : a in erase s b ↔ 
a != b ∧ a in s
· 使用定理 `ne_of_apply_ne`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) {x y : α}, f
 x ≠ f y → x ≠ y
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Finset.mem_cons`：mem_cons {h} : b in s.cons a h ↔ b = a ∨ b in s
· 使用定理 `not_or_intro`：∀ {a b : Prop}, ¬a → ¬b → ¬(a ∨ b)
· 使用定理 `Finset.cons_eq_insert`：cons_eq_insert (a s h) : @cons α a s h = insert a
 s
· 使用定理 `Finset.insert_erase`：∀ {α : Type u_1} [inst : DecidableEq α] {s : Finset
 α} {a : α}, a ∈ s → insert a (s.erase a) = s
· 使用定理 `Finset.cons.congr_simp`：∀ {α : Type u_1} (a a_1 : α) (e_a : a = a_1) (s 
s_1 : Finset α) (e_s : s = s_1) (h : a ∉ s),   Finset.cons a s h = Finset.cons a
_1 s_1 ⋯
· 使用定理 `Finset.sum_cons`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι} 
[inst : AddCommMonoid M] {f : ι → M} (h : a ∉ s),   ∑ x ∈ Finset.cons a s h, f x
 = f …
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_eq_cancel_eq`：eq_eq_cancel_eq {M : Type*} [M
onoidWithZero M] [IsLeftCancelMulZero M] {e₁ e₂ f₁ f₂ L : M} (H₁ : e₁ = L * f₁) 
(H₂ : e₂ = L * f₂) (HL : L != …
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `instIsCancelMulZero`：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀], IsCanc
elMulZero G₀
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_mul_of_eq_eq_eq_mul`：eq_mul_of_eq_eq_eq_mul 
{M : Type*} [Mul M] {a b c D e f : M} (h₁ : a = b) (h₂ : b = c) (h₃ : c = D * e)
 (h₄ : e = f) : a = D * f
· 使用定理 `Mathlib.Tactic.FieldSimp.subst_add`：subst_add {M : Type*} [Semiring M] {
x₁ x₂ X₁ X₂ Y y a : M} (h₁ : x₁ = a * X₁) (h₂ : x₂ = a * X₂) (H_atom : X₁ + X₂ =
 Y) (hy : a * Y = y) : x…
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval`：div_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al / l₂.eval = l.eval) : x₁ /…
（共 95 条，此处仅展示前 30 条）

--- 原说明 ---
Convex **strict Jensen inequality**.

If the function is strictly convex, the weights are strictly positive and the in
dexed family of
points is non-constant, then Jensen's inequality is strict.

See also `StrictConvexOn.map_sum_eq_iff`.
-/
lemma StrictConvexOn.map_sum_lt (hf : StrictConvexOn 𝕜 s f) (h₀ : ∀ i ∈ t, 0 < w i)
    (h₁ : ∑ i ∈ t, w i = 1) (hmem : ∀ i ∈ t, p i ∈ s) (hp : ∃ j ∈ t, ∃ k ∈ t, p j ≠ p k) :
    f (∑ i ∈ t, w i • p i) < ∑ i ∈ t, w i • f (p i) := by
  classical
  obtain ⟨j, hj, k, hk, hjk⟩ := hp
  -- We replace `t` by `t \ {j, k}`
  have : k ∈ t.erase j := mem_erase.2 ⟨ne_of_apply_ne _ hjk.symm, hk⟩
  let u := (t.erase j).erase k
  have hj : j ∉ u := by simp [u]
  have hk : k ∉ u := by simp [u]
  have ht :
      t = (u.cons k hk).cons j (mem_cons.not.2 <| not_or_intro (ne_of_apply_ne _ hjk) hj) := by
    simp [u, insert_erase this, insert_erase ‹j ∈ t›, *]
  clear_value u
  subst ht
  simp only [sum_cons]
  have := h₀ j <| by simp
  have := h₀ k <| by simp
  let c := w j + w k
  have hc : w j / c + w k / c = 1 := by simp [field, c]
  calc f (w j • p j + (w k • p k + ∑ x ∈ u, w x • p x))
    _ = f (c • ((w j / c) • p j + (w k / c) • p k) + ∑ x ∈ u, w x • p x) := by
      congrm f ?_
      match_scalars <;> simp [field, c]
    _ ≤ c • f ((w j / c) • p j + (w k / c) • p k) + ∑ x ∈ u, w x • f (p x) :=
      -- apply the usual Jensen's inequality w.r.t. the weighted average of the two distinguished
      -- points and all the other points
        hf.convexOn.map_add_sum_le (fun i hi ↦ (h₀ _ <| by simp [hi]).le)
          (by simpa [-cons_eq_insert, ← add_assoc] using h₁)
          (forall_of_forall_cons <| forall_of_forall_cons hmem) (by positivity) <| by
           refine hf.1 (hmem _ <| by simp) (hmem _ <| by simp) ?_ ?_ hc <;> positivity
    _ < c • ((w j / c) • f (p j) + (w k / c) • f (p k)) + ∑ x ∈ u, w x • f (p x) := by
      -- then apply the definition of strict convexity for the two distinguished points
      gcongr; refine hf.2 (hmem _ <| by simp) (hmem _ <| by simp) hjk ?_ ?_ hc <;> positivity
    _ = (w j • f (p j) + w k • f (p k)) + ∑ x ∈ u, w x • f (p x) := by
      match_scalars <;> simp [field, c]
    _ = w j • f (p j) + (w k • f (p k) + ∑ x ∈ u, w x • f (p x)) := by abel_nf

/-- Concave **strict Jensen inequality**.

If the function is strictly concave, the weights are strictly positive and the indexed family of
points is non-constant, then Jensen's inequality is strict.

See also `StrictConcaveOn.map_sum_eq_iff`. -/
/-
**StrictConcaveOn.lt_map_sum** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StrictConcaveOn.lt_map_sum (hf : StrictConcaveOn 𝕜 s f) (h₀ : forall i in 
t, 0 < w i) (h₁ : ∑ i in t, w i = 1) (hmem : forall i in t, p i in s) (hp : exis
ts j in t, exists k in t, p j != p k) : ∑ i in t, w i • f (p i) < f (∑ i in t, w
 i • p i)
参数：hf : StrictConcaveOn 𝕜 s f；h₀ : forall i in t, 0 < w i；h₁ : ∑ i in t, w i = 1
；hmem : forall i in t, p i in s；hp : exists j in t, exists k in t, p j != p k。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `StrictConvexOn.map_sum_lt`：StrictConvexOn.map_sum_lt (hf : StrictConvexO
n 𝕜 s f) (h₀ : forall i in t, 0 < w i) (h₁ : ∑ i in t, w i = 1) (hmem : forall i
 in t, p i in s…
· 使用定理 `OrderDual.isOrderedAddMonoid`：∀ {α : Type u} [inst : AddCommMonoid α] [i
nst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedAddMonoid αᵒᵈ
· 使用定理 `OrderDual.instIsStrictOrderedModule`：∀ {α : Type u_1} {β : Type u_2} [in
st : Preorder α] [inst_1 : MonoidWithZero α] [inst_2 : AddCommGroup β]   [inst_3
 : PartialOrder β] [IsOrd…
· 使用定理 `StrictConcaveOn.dual`：StrictConcaveOn.dual (hf : StrictConcaveOn 𝕜 s f) 
: StrictConvexOn 𝕜 s (toDual ∘ f)

--- 原说明 ---
Concave **strict Jensen inequality**.

If the function is strictly concave, the weights are strictly positive and the i
ndexed family of
points is non-constant, then Jensen's inequality is strict.

See also `StrictConcaveOn.map_sum_eq_iff`.
-/
lemma StrictConcaveOn.lt_map_sum (hf : StrictConcaveOn 𝕜 s f) (h₀ : ∀ i ∈ t, 0 < w i)
    (h₁ : ∑ i ∈ t, w i = 1) (hmem : ∀ i ∈ t, p i ∈ s) (hp : ∃ j ∈ t, ∃ k ∈ t, p j ≠ p k) :
    ∑ i ∈ t, w i • f (p i) < f (∑ i ∈ t, w i • p i) := hf.dual.map_sum_lt h₀ h₁ hmem hp

/-! ### Equality case of Jensen's inequality -/

/-- A form of the **equality case of Jensen's equality**.

For a strictly convex function `f` and positive weights `w`, if
`f (∑ i ∈ t, w i • p i) = ∑ i ∈ t, w i • f (p i)`, then the points `p` are all equal.

See also `StrictConvexOn.map_sum_eq_iff`. -/
/-
**StrictConvexOn.eq_of_le_map_sum** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StrictConvexOn.eq_of_le_map_sum (hf : StrictConvexOn 𝕜 s f) (h₀ : forall i
 in t, 0 < w i) (h₁ : ∑ i in t, w i = 1) (hmem : forall i in t, p i in s) (h_eq 
: ∑ i in t, w i • f (p i) <= f (∑ i in t, w i • p i)) : forall ⦃j⦄, j in t -> fo
rall ⦃k⦄, k in t -> p j = p k
参数：hf : StrictConvexOn 𝕜 s f；h₀ : forall i in t, 0 < w i；h₁ : ∑ i in t, w i = 1；
hmem : forall i in t, p i in s；h_eq : ∑ i in t, w i • f (p i) <= f (∑ i in t, w 
i • p i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用引理 `StrictConvexOn.map_sum_lt`：StrictConvexOn.map_sum_lt (hf : StrictConvexO
n 𝕜 s f) (h₀ : forall i in t, 0 < w i) (h₁ : ∑ i in t, w i = 1) (hmem : forall i
 in t, p i in s…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g

--- 原说明 ---
A form of the **equality case of Jensen's equality**.

For a strictly convex function `f` and positive weights `w`, if
`f (∑ i ∈ t, w i • p i) = ∑ i ∈ t, w i • f (p i)`, then the points `p` are all e
qual.

See also `StrictConvexOn.map_sum_eq_iff`.
-/
lemma StrictConvexOn.eq_of_le_map_sum (hf : StrictConvexOn 𝕜 s f) (h₀ : ∀ i ∈ t, 0 < w i)
    (h₁ : ∑ i ∈ t, w i = 1) (hmem : ∀ i ∈ t, p i ∈ s)
    (h_eq : ∑ i ∈ t, w i • f (p i) ≤ f (∑ i ∈ t, w i • p i)) :
    ∀ ⦃j⦄, j ∈ t → ∀ ⦃k⦄, k ∈ t → p j = p k := by
  by_contra!; exact h_eq.not_gt <| hf.map_sum_lt h₀ h₁ hmem this

/-- A form of the **equality case of Jensen's equality**.

For a strictly concave function `f` and positive weights `w`, if
`f (∑ i ∈ t, w i • p i) = ∑ i ∈ t, w i • f (p i)`, then the points `p` are all equal.

See also `StrictConcaveOn.map_sum_eq_iff`. -/
/-
**StrictConcaveOn.eq_of_map_sum_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StrictConcaveOn.eq_of_map_sum_eq (hf : StrictConcaveOn 𝕜 s f) (h₀ : forall
 i in t, 0 < w i) (h₁ : ∑ i in t, w i = 1) (hmem : forall i in t, p i in s) (h_e
q : f (∑ i in t, w i • p i) <= ∑ i in t, w i • f (p i)) : forall ⦃j⦄, j in t -> 
forall ⦃k⦄, k in t -> p j = p k
参数：hf : StrictConcaveOn 𝕜 s f；h₀ : forall i in t, 0 < w i；h₁ : ∑ i in t, w i = 1
；hmem : forall i in t, p i in s；h_eq : f (∑ i in t, w i • p i) <= ∑ i in t, w i 
• f (p i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `StrictConvexOn.eq_of_le_map_sum`：StrictConvexOn.eq_of_le_map_sum (hf : S
trictConvexOn 𝕜 s f) (h₀ : forall i in t, 0 < w i) (h₁ : ∑ i in t, w i = 1) (hme
m : forall i in t, p …
· 使用定理 `OrderDual.isOrderedAddMonoid`：∀ {α : Type u} [inst : AddCommMonoid α] [i
nst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedAddMonoid αᵒᵈ
· 使用定理 `OrderDual.instIsStrictOrderedModule`：∀ {α : Type u_1} {β : Type u_2} [in
st : Preorder α] [inst_1 : MonoidWithZero α] [inst_2 : AddCommGroup β]   [inst_3
 : PartialOrder β] [IsOrd…
· 使用定理 `StrictConcaveOn.dual`：StrictConcaveOn.dual (hf : StrictConcaveOn 𝕜 s f) 
: StrictConvexOn 𝕜 s (toDual ∘ f)

--- 原说明 ---
A form of the **equality case of Jensen's equality**.

For a strictly concave function `f` and positive weights `w`, if
`f (∑ i ∈ t, w i • p i) = ∑ i ∈ t, w i • f (p i)`, then the points `p` are all e
qual.

See also `StrictConcaveOn.map_sum_eq_iff`.
-/
lemma StrictConcaveOn.eq_of_map_sum_eq (hf : StrictConcaveOn 𝕜 s f) (h₀ : ∀ i ∈ t, 0 < w i)
    (h₁ : ∑ i ∈ t, w i = 1) (hmem : ∀ i ∈ t, p i ∈ s)
    (h_eq : f (∑ i ∈ t, w i • p i) ≤ ∑ i ∈ t, w i • f (p i)) :
    ∀ ⦃j⦄, j ∈ t → ∀ ⦃k⦄, k ∈ t → p j = p k :=
  hf.dual.eq_of_le_map_sum h₀ h₁ hmem h_eq

/-- A form of the **equality case of Jensen's equality** for the case of strict convex and positive
weights. -/
/-
**StrictConvexOn.map_sum_eq_iff_of_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictConvexOn.map_sum_eq_iff_of_pos (hf : StrictConvexOn 𝕜 s f) (h₀ : for
all i in t, 0 < w i) (h₁ : ∑ i in t, w i = 1) (hmem : forall i in t, p i in s) :
 f (∑ i in t, w i • p i) = ∑ i in t, w i • f (p i) ↔ forall ⦃j⦄, j in t -> foral
l ⦃k⦄, k in t -> p j = p k
参数：hf : StrictConvexOn 𝕜 s f；h₀ : forall i in t, 0 < w i；h₁ : ∑ i in t, w i = 1；
hmem : forall i in t, p i in s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `StrictConvexOn.eq_of_le_map_sum`：StrictConvexOn.eq_of_le_map_sum (hf : S
trictConvexOn 𝕜 s f) (h₀ : forall i in t, 0 < w i) (h₁ : ∑ i in t, w i = 1) (hme
m : forall i in t, p …
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Finset.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Finset α) : s = ∅
 ∨ s.Nonempty
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…

--- 原说明 ---
A form of the **equality case of Jensen's equality** for the case of strict conv
ex and positive
weights.
-/
theorem StrictConvexOn.map_sum_eq_iff_of_pos (hf : StrictConvexOn 𝕜 s f) (h₀ : ∀ i ∈ t, 0 < w i)
    (h₁ : ∑ i ∈ t, w i = 1) (hmem : ∀ i ∈ t, p i ∈ s) :
    f (∑ i ∈ t, w i • p i) = ∑ i ∈ t, w i • f (p i) ↔ ∀ ⦃j⦄, j ∈ t → ∀ ⦃k⦄, k ∈ t → p j = p k := by
  refine ⟨fun h j hj k hk ↦ hf.eq_of_le_map_sum h₀ h₁ hmem h.ge hj hk, fun h ↦ ?_⟩
  rcases t.eq_empty_or_nonempty with (rfl | ⟨i, hi⟩)
  · simp at h₁
  · suffices f (∑ k ∈ t, w k • p i) = ∑ k ∈ t, w k • f (p i) by convert this using 3 <;> grind
    simp [← sum_smul, h₁]

/-- A form of the **equality case of Jensen's equality** for the case of strict concave and positive
weights. -/
/-
**StrictConcaveOn.map_sum_eq_iff_of_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictConcaveOn.map_sum_eq_iff_of_pos (hf : StrictConcaveOn 𝕜 s f) (h₀ : f
orall i in t, 0 < w i) (h₁ : ∑ i in t, w i = 1) (hmem : forall i in t, p i in s)
 : f (∑ i in t, w i • p i) = ∑ i in t, w i • f (p i) ↔ forall ⦃j⦄, j in t -> for
all ⦃k⦄, k in t -> p j = p k
参数：hf : StrictConcaveOn 𝕜 s f；h₀ : forall i in t, 0 < w i；h₁ : ∑ i in t, w i = 1
；hmem : forall i in t, p i in s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictConvexOn.map_sum_eq_iff_of_pos`：StrictConvexOn.map_sum_eq_iff_of_p
os (hf : StrictConvexOn 𝕜 s f) (h₀ : forall i in t, 0 < w i) (h₁ : ∑ i in t, w i
 = 1) (hmem : forall i in …
· 使用定理 `OrderDual.isOrderedAddMonoid`：∀ {α : Type u} [inst : AddCommMonoid α] [i
nst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedAddMonoid αᵒᵈ
· 使用定理 `OrderDual.instIsStrictOrderedModule`：∀ {α : Type u_1} {β : Type u_2} [in
st : Preorder α] [inst_1 : MonoidWithZero α] [inst_2 : AddCommGroup β]   [inst_3
 : PartialOrder β] [IsOrd…
· 使用定理 `StrictConcaveOn.dual`：StrictConcaveOn.dual (hf : StrictConcaveOn 𝕜 s f) 
: StrictConvexOn 𝕜 s (toDual ∘ f)

--- 原说明 ---
A form of the **equality case of Jensen's equality** for the case of strict conc
ave and positive
weights.
-/
theorem StrictConcaveOn.map_sum_eq_iff_of_pos (hf : StrictConcaveOn 𝕜 s f) (h₀ : ∀ i ∈ t, 0 < w i)
    (h₁ : ∑ i ∈ t, w i = 1) (hmem : ∀ i ∈ t, p i ∈ s) :
    f (∑ i ∈ t, w i • p i) = ∑ i ∈ t, w i • f (p i) ↔ ∀ ⦃j⦄, j ∈ t → ∀ ⦃k⦄, k ∈ t → p j = p k :=
  hf.dual.map_sum_eq_iff_of_pos h₀ h₁ hmem

/-- A form of the **equality case of Jensen's equality** for the case of strict convex and
non-negative weights. -/
/-
**StrictConvexOn.map_sum_eq_iff_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictConvexOn.map_sum_eq_iff_of_nonneg (hf : StrictConvexOn 𝕜 s f) (h₀ : 
forall i in t, 0 <= w i) (h₁ : ∑ i in t, w i = 1) (hmem : forall i in t, p i in 
s) : f (∑ i in t, w i • p i) = ∑ i in t, w i • f (p i) ↔ forall ⦃j⦄, j in t -> w
 j != 0 -> forall ⦃k⦄, k in t -> w k != 0 -> p j = p k
参数：hf : StrictConvexOn 𝕜 s f；h₀ : forall i in t, 0 <= w i；h₁ : ∑ i in t, w i = 1
；hmem : forall i in t, p i in s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictConvexOn.map_sum_eq_iff_of_pos`：StrictConvexOn.map_sum_eq_iff_of_p
os (hf : StrictConvexOn 𝕜 s f) (h₀ : forall i in t, 0 < w i) (h₁ : ∑ i in t, w i
 = 1) (hmem : forall i in …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_filter_ne_zero`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCo
mmMonoid M] {f : ι → M} (s : Finset ι)   [inst_1 : (x : ι) → Decidable (f x ≠ 0)
], ∑ x ∈ s with…
· 使用定理 `Finset.mem_of_mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : Decida
blePred p] {s : Finset α}, ∀ x ∈ Finset.filter p s, x ∈ s

--- 原说明 ---
A form of the **equality case of Jensen's equality** for the case of strict conv
ex and
non-negative weights.
-/
theorem StrictConvexOn.map_sum_eq_iff_of_nonneg (hf : StrictConvexOn 𝕜 s f) (h₀ : ∀ i ∈ t, 0 ≤ w i)
    (h₁ : ∑ i ∈ t, w i = 1) (hmem : ∀ i ∈ t, p i ∈ s) :
    f (∑ i ∈ t, w i • p i) = ∑ i ∈ t, w i • f (p i) ↔
      ∀ ⦃j⦄, j ∈ t → w j ≠ 0 → ∀ ⦃k⦄, k ∈ t → w k ≠ 0 → p j = p k := by
  have :
      f (∑ i ∈ t with w i ≠ 0, w i • p i) = ∑ i ∈ t with w i ≠ 0, w i • f (p i) ↔
        ∀ ⦃j : ι⦄, j ∈ {x ∈ t | w x ≠ 0} → ∀ ⦃k : ι⦄, k ∈ {x ∈ t | w x ≠ 0} → p j = p k :=
    hf.map_sum_eq_iff_of_pos (by grind)
      (sum_filter_ne_zero _ |>.trans h₁) (hmem _ <| mem_of_mem_filter · ·)
  grind [sum_filter_of_ne, left_ne_zero_of_smul]

/-- A form of the **equality case of Jensen's equality** for the case of strict concave and
non-negative weights. -/
/-
**StrictConcaveOn.map_sum_eq_iff_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictConcaveOn.map_sum_eq_iff_of_nonneg (hf : StrictConcaveOn 𝕜 s f) (h₀ 
: forall i in t, 0 <= w i) (h₁ : ∑ i in t, w i = 1) (hmem : forall i in t, p i i
n s) : f (∑ i in t, w i • p i) = ∑ i in t, w i • f (p i) ↔ forall ⦃j⦄, j in t ->
 w j != 0 -> forall ⦃k⦄, k in t -> w k != 0 -> p j = p k
参数：hf : StrictConcaveOn 𝕜 s f；h₀ : forall i in t, 0 <= w i；h₁ : ∑ i in t, w i = 
1；hmem : forall i in t, p i in s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictConvexOn.map_sum_eq_iff_of_nonneg`：StrictConvexOn.map_sum_eq_iff_o
f_nonneg (hf : StrictConvexOn 𝕜 s f) (h₀ : forall i in t, 0 <= w i) (h₁ : ∑ i in
 t, w i = 1) (hmem : forall i…
· 使用定理 `OrderDual.isOrderedAddMonoid`：∀ {α : Type u} [inst : AddCommMonoid α] [i
nst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedAddMonoid αᵒᵈ
· 使用定理 `OrderDual.instIsStrictOrderedModule`：∀ {α : Type u_1} {β : Type u_2} [in
st : Preorder α] [inst_1 : MonoidWithZero α] [inst_2 : AddCommGroup β]   [inst_3
 : PartialOrder β] [IsOrd…
· 使用定理 `StrictConcaveOn.dual`：StrictConcaveOn.dual (hf : StrictConcaveOn 𝕜 s f) 
: StrictConvexOn 𝕜 s (toDual ∘ f)

--- 原说明 ---
A form of the **equality case of Jensen's equality** for the case of strict conc
ave and
non-negative weights.
-/
theorem StrictConcaveOn.map_sum_eq_iff_of_nonneg (hf : StrictConcaveOn 𝕜 s f)
    (h₀ : ∀ i ∈ t, 0 ≤ w i) (h₁ : ∑ i ∈ t, w i = 1) (hmem : ∀ i ∈ t, p i ∈ s) :
    f (∑ i ∈ t, w i • p i) = ∑ i ∈ t, w i • f (p i) ↔
      ∀ ⦃j⦄, j ∈ t → w j ≠ 0 → ∀ ⦃k⦄, k ∈ t → w k ≠ 0 → p j = p k :=
  hf.dual.map_sum_eq_iff_of_nonneg h₀ h₁ hmem
/-
**StrictConvexOn.map_sum_lt_iff_of_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictConvexOn.map_sum_lt_iff_of_pos (hf : StrictConvexOn 𝕜 s f) (h₀ : for
all i in t, 0 < w i) (h₁ : ∑ i in t, w i = 1) (hmem : forall i in t, p i in s) :
 f (∑ i in t, w i • p i) < ∑ i in t, w i • f (p i) ↔ exists j in t, exists k in 
t, p j != p k
参数：hf : StrictConvexOn 𝕜 s f；h₀ : forall i in t, 0 < w i；h₁ : ∑ i in t, w i = 1；
hmem : forall i in t, p i in s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `Eq.not_lt`：∀ {α : Type u_2} [inst : Preorder α] {a b : α}, a = b → ¬a < 
b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `StrictConvexOn.map_sum_eq_iff_of_pos`：StrictConvexOn.map_sum_eq_iff_of_p
os (hf : StrictConvexOn 𝕜 s f) (h₀ : forall i in t, 0 < w i) (h₁ : ∑ i in t, w i
 = 1) (hmem : forall i in …
· 使用引理 `StrictConvexOn.map_sum_lt`：StrictConvexOn.map_sum_lt (hf : StrictConvexO
n 𝕜 s f) (h₀ : forall i in t, 0 < w i) (h₁ : ∑ i in t, w i = 1) (hmem : forall i
 in t, p i in s…
-/
theorem StrictConvexOn.map_sum_lt_iff_of_pos (hf : StrictConvexOn 𝕜 s f) (h₀ : ∀ i ∈ t, 0 < w i)
    (h₁ : ∑ i ∈ t, w i = 1) (hmem : ∀ i ∈ t, p i ∈ s) :
    f (∑ i ∈ t, w i • p i) < ∑ i ∈ t, w i • f (p i) ↔ ∃ j ∈ t, ∃ k ∈ t, p j ≠ p k := by
  refine ⟨fun h ↦ ?_, hf.map_sum_lt h₀ h₁ hmem⟩
  contrapose! h
  exact hf.map_sum_eq_iff_of_pos h₀ h₁ hmem |>.mpr h |>.not_lt
/-
**StrictConcaveOn.lt_map_sum_iff_of_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictConcaveOn.lt_map_sum_iff_of_pos (hf : StrictConcaveOn 𝕜 s f) (h₀ : f
orall i in t, 0 < w i) (h₁ : ∑ i in t, w i = 1) (hmem : forall i in t, p i in s)
 : ∑ i in t, w i • f (p i) < f (∑ i in t, w i • p i) ↔ exists j in t, exists k i
n t, p j != p k
参数：hf : StrictConcaveOn 𝕜 s f；h₀ : forall i in t, 0 < w i；h₁ : ∑ i in t, w i = 1
；hmem : forall i in t, p i in s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictConvexOn.map_sum_lt_iff_of_pos`：StrictConvexOn.map_sum_lt_iff_of_p
os (hf : StrictConvexOn 𝕜 s f) (h₀ : forall i in t, 0 < w i) (h₁ : ∑ i in t, w i
 = 1) (hmem : forall i in …
· 使用定理 `OrderDual.isOrderedAddMonoid`：∀ {α : Type u} [inst : AddCommMonoid α] [i
nst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedAddMonoid αᵒᵈ
· 使用定理 `OrderDual.instIsStrictOrderedModule`：∀ {α : Type u_1} {β : Type u_2} [in
st : Preorder α] [inst_1 : MonoidWithZero α] [inst_2 : AddCommGroup β]   [inst_3
 : PartialOrder β] [IsOrd…
· 使用定理 `StrictConcaveOn.dual`：StrictConcaveOn.dual (hf : StrictConcaveOn 𝕜 s f) 
: StrictConvexOn 𝕜 s (toDual ∘ f)
-/
theorem StrictConcaveOn.lt_map_sum_iff_of_pos (hf : StrictConcaveOn 𝕜 s f) (h₀ : ∀ i ∈ t, 0 < w i)
    (h₁ : ∑ i ∈ t, w i = 1) (hmem : ∀ i ∈ t, p i ∈ s) :
    ∑ i ∈ t, w i • f (p i) < f (∑ i ∈ t, w i • p i) ↔ ∃ j ∈ t, ∃ k ∈ t, p j ≠ p k :=
  hf.dual.map_sum_lt_iff_of_pos h₀ h₁ hmem
/-
**StrictConvexOn.map_sum_lt_iff_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictConvexOn.map_sum_lt_iff_of_nonneg (hf : StrictConvexOn 𝕜 s f) (h₀ : 
forall i in t, 0 <= w i) (h₁ : ∑ i in t, w i = 1) (hmem : forall i in t, p i in 
s) : f (∑ i in t, w i • p i) < ∑ i in t, w i • f (p i) ↔ exists j in t, exists k
 in t, w j != 0 ∧ w k != 0 ∧ p j != p k
参数：hf : StrictConvexOn 𝕜 s f；h₀ : forall i in t, 0 <= w i；h₁ : ∑ i in t, w i = 1
；hmem : forall i in t, p i in s。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem StrictConvexOn.map_sum_lt_iff_of_nonneg (hf : StrictConvexOn 𝕜 s f) (h₀ : ∀ i ∈ t, 0 ≤ w i)
    (h₁ : ∑ i ∈ t, w i = 1) (hmem : ∀ i ∈ t, p i ∈ s) :
    f (∑ i ∈ t, w i • p i) < ∑ i ∈ t, w i • f (p i) ↔
      ∃ j ∈ t, ∃ k ∈ t, w j ≠ 0 ∧ w k ≠ 0 ∧ p j ≠ p k := by
  grind [hf.convexOn.map_sum_le h₀ h₁ hmem |>.not_lt_iff_eq, hf.map_sum_eq_iff_of_nonneg h₀ h₁ hmem]
/-
**StrictConcaveOn.lt_map_sum_iff_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictConcaveOn.lt_map_sum_iff_of_nonneg (hf : StrictConcaveOn 𝕜 s f) (h₀ 
: forall i in t, 0 <= w i) (h₁ : ∑ i in t, w i = 1) (hmem : forall i in t, p i i
n s) : ∑ i in t, w i • f (p i) < f (∑ i in t, w i • p i) ↔ exists j in t, exists
 k in t, w j != 0 ∧ w k != 0 ∧ p j != p k
参数：hf : StrictConcaveOn 𝕜 s f；h₀ : forall i in t, 0 <= w i；h₁ : ∑ i in t, w i = 
1；hmem : forall i in t, p i in s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictConvexOn.map_sum_lt_iff_of_nonneg`：StrictConvexOn.map_sum_lt_iff_o
f_nonneg (hf : StrictConvexOn 𝕜 s f) (h₀ : forall i in t, 0 <= w i) (h₁ : ∑ i in
 t, w i = 1) (hmem : forall i…
· 使用定理 `OrderDual.isOrderedAddMonoid`：∀ {α : Type u} [inst : AddCommMonoid α] [i
nst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedAddMonoid αᵒᵈ
· 使用定理 `OrderDual.instIsStrictOrderedModule`：∀ {α : Type u_1} {β : Type u_2} [in
st : Preorder α] [inst_1 : MonoidWithZero α] [inst_2 : AddCommGroup β]   [inst_3
 : PartialOrder β] [IsOrd…
· 使用定理 `StrictConcaveOn.dual`：StrictConcaveOn.dual (hf : StrictConcaveOn 𝕜 s f) 
: StrictConvexOn 𝕜 s (toDual ∘ f)
-/
theorem StrictConcaveOn.lt_map_sum_iff_of_nonneg (hf : StrictConcaveOn 𝕜 s f)
    (h₀ : ∀ i ∈ t, 0 ≤ w i) (h₁ : ∑ i ∈ t, w i = 1) (hmem : ∀ i ∈ t, p i ∈ s) :
    ∑ i ∈ t, w i • f (p i) < f (∑ i ∈ t, w i • p i) ↔
      ∃ j ∈ t, ∃ k ∈ t, w j ≠ 0 ∧ w k ≠ 0 ∧ p j ≠ p k :=
  hf.dual.map_sum_lt_iff_of_nonneg h₀ h₁ hmem

/-- Canonical form of the **equality case of Jensen's equality**.

For a strictly convex function `f` and positive weights `w`, we have
`f (∑ i ∈ t, w i • p i) = ∑ i ∈ t, w i • f (p i)` if and only if the points `p` are all equal
(and in fact all equal to their center of mass w.r.t. `w`). -/
/-
**StrictConvexOn.map_sum_eq_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StrictConvexOn.map_sum_eq_iff {w : ι -> 𝕜} {p : ι -> E} (hf : StrictConvex
On 𝕜 s f) (h₀ : forall i in t, 0 < w i) (h₁ : ∑ i in t, w i = 1) (hmem : forall 
i in t, p i in s) : f (∑ i in t, w i • p i) = ∑ i in t, w i • f (p i) ↔ forall j
 in t, p j = ∑ i in t, w i • p i
参数：hf : StrictConvexOn 𝕜 s f；h₀ : forall i in t, 0 < w i；h₁ : ∑ i in t, w i = 1；
hmem : forall i in t, p i in s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Finset α) : s = ∅
 ∨ s.Nonempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `StrictConvexOn.eq_of_le_map_sum`：StrictConvexOn.eq_of_le_map_sum (hf : S
trictConvexOn 𝕜 s f) (h₀ : forall i in t, 0 < w i) (h₁ : ∑ i in t, w i = 1) (hme
m : forall i in t, p …
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.sum_smul`：Finset.sum_smul {f : ι -> R} {s : Finset ι} {x : M} : (
∑ i in s, f i) • x = ∑ i in s, f i • x
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'

--- 原说明 ---
Canonical form of the **equality case of Jensen's equality**.

For a strictly convex function `f` and positive weights `w`, we have
`f (∑ i ∈ t, w i • p i) = ∑ i ∈ t, w i • f (p i)` if and only if the points `p` 
are all equal
(and in fact all equal to their center of mass w.r.t. `w`).
-/
lemma StrictConvexOn.map_sum_eq_iff {w : ι → 𝕜} {p : ι → E} (hf : StrictConvexOn 𝕜 s f)
    (h₀ : ∀ i ∈ t, 0 < w i) (h₁ : ∑ i ∈ t, w i = 1) (hmem : ∀ i ∈ t, p i ∈ s) :
    f (∑ i ∈ t, w i • p i) = ∑ i ∈ t, w i • f (p i) ↔ ∀ j ∈ t, p j = ∑ i ∈ t, w i • p i := by
  refine ⟨?_, fun h ↦ ?_⟩
  · obtain rfl | ⟨i₀, hi₀⟩ := t.eq_empty_or_nonempty
    · simp
    intro h_eq i hi
    have H (j) (hj : j ∈ t) : p j = p i₀ := hf.eq_of_le_map_sum h₀ h₁ hmem h_eq.ge hj hi₀
    calc p i = p i₀ := by rw [H _ hi]
      _ = (1 : 𝕜) • p i₀ := by simp
      _ = (∑ j ∈ t, w j) • p i₀ := by rw [h₁]
      _ = ∑ j ∈ t, (w j • p i₀) := by rw [sum_smul]
      _ = ∑ j ∈ t, (w j • p j) := by congr! 2 with j hj; rw [← H _ hj]
  · grind [hf.map_sum_eq_iff_of_pos h₀ h₁ hmem]

/-- Canonical form of the **equality case of Jensen's equality**.

For a strictly concave function `f` and positive weights `w`, we have
`f (∑ i ∈ t, w i • p i) = ∑ i ∈ t, w i • f (p i)` if and only if the points `p` are all equal
(and in fact all equal to their center of mass w.r.t. `w`). -/
/-
**StrictConcaveOn.map_sum_eq_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StrictConcaveOn.map_sum_eq_iff (hf : StrictConcaveOn 𝕜 s f) (h₀ : forall i
 in t, 0 < w i) (h₁ : ∑ i in t, w i = 1) (hmem : forall i in t, p i in s) : f (∑
 i in t, w i • p i) = ∑ i in t, w i • f (p i) ↔ forall j in t, p j = ∑ i in t, w
 i • p i
参数：hf : StrictConcaveOn 𝕜 s f；h₀ : forall i in t, 0 < w i；h₁ : ∑ i in t, w i = 1
；hmem : forall i in t, p i in s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `StrictConvexOn.map_sum_eq_iff`：StrictConvexOn.map_sum_eq_iff {w : ι -> 𝕜
} {p : ι -> E} (hf : StrictConvexOn 𝕜 s f) (h₀ : forall i in t, 0 < w i) (h₁ : ∑
 i in t, w i = 1) (…
· 使用定理 `OrderDual.isOrderedAddMonoid`：∀ {α : Type u} [inst : AddCommMonoid α] [i
nst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedAddMonoid αᵒᵈ
· 使用定理 `OrderDual.instIsStrictOrderedModule`：∀ {α : Type u_1} {β : Type u_2} [in
st : Preorder α] [inst_1 : MonoidWithZero α] [inst_2 : AddCommGroup β]   [inst_3
 : PartialOrder β] [IsOrd…
· 使用定理 `StrictConcaveOn.dual`：StrictConcaveOn.dual (hf : StrictConcaveOn 𝕜 s f) 
: StrictConvexOn 𝕜 s (toDual ∘ f)

--- 原说明 ---
Canonical form of the **equality case of Jensen's equality**.

For a strictly concave function `f` and positive weights `w`, we have
`f (∑ i ∈ t, w i • p i) = ∑ i ∈ t, w i • f (p i)` if and only if the points `p` 
are all equal
(and in fact all equal to their center of mass w.r.t. `w`).
-/
lemma StrictConcaveOn.map_sum_eq_iff (hf : StrictConcaveOn 𝕜 s f) (h₀ : ∀ i ∈ t, 0 < w i)
    (h₁ : ∑ i ∈ t, w i = 1) (hmem : ∀ i ∈ t, p i ∈ s) :
    f (∑ i ∈ t, w i • p i) = ∑ i ∈ t, w i • f (p i) ↔ ∀ j ∈ t, p j = ∑ i ∈ t, w i • p i :=
  hf.dual.map_sum_eq_iff h₀ h₁ hmem

/-- Canonical form of the **equality case of Jensen's equality**.

For a strictly convex function `f` and nonnegative weights `w`, we have
`f (∑ i ∈ t, w i • p i) = ∑ i ∈ t, w i • f (p i)` if and only if the points `p` with nonzero
weight are all equal (and in fact all equal to their center of mass w.r.t. `w`). -/
/-
**StrictConvexOn.map_sum_eq_iff'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StrictConvexOn.map_sum_eq_iff' (hf : StrictConvexOn 𝕜 s f) (h₀ : forall i 
in t, 0 <= w i) (h₁ : ∑ i in t, w i = 1) (hmem : forall i in t, p i in s) : f (∑
 i in t, w i • p i) = ∑ i in t, w i • f (p i) ↔ forall j in t, w j != 0 -> p j =
 ∑ i in t, w i • p i
参数：hf : StrictConvexOn 𝕜 s f；h₀ : forall i in t, 0 <= w i；h₁ : ∑ i in t, w i = 1
；hmem : forall i in t, p i in s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `IsStrictOrderedRing.isDomain`：∀ {R : Type u} [inst : Semiring R] [inst_1
 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], IsDomain R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_filter_of_ne`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} 
[inst : AddCommMonoid M] {f : ι → M} {p : ι → Prop}   [inst_1 : DecidablePred p]
, (∀ x ∈ s, f…
· 使用引理 `StrictConvexOn.map_sum_eq_iff`：StrictConvexOn.map_sum_eq_iff {w : ι -> 𝕜
} {p : ι -> E} (hf : StrictConvexOn 𝕜 s f) (h₀ : forall i in t, 0 < w i) (h₁ : ∑
 i in t, w i = 1) (…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `LE.le.lt_iff_ne'`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, b 
≤ a → (b < a ↔ a ≠ b)
· 使用定理 `Finset.sum_filter_ne_zero`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCo
mmMonoid M] {f : ι → M} (s : Finset ι)   [inst_1 : (x : ι) → Decidable (f x ≠ 0)
], ∑ x ∈ s with…
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Canonical form of the **equality case of Jensen's equality**.

For a strictly convex function `f` and nonnegative weights `w`, we have
`f (∑ i ∈ t, w i • p i) = ∑ i ∈ t, w i • f (p i)` if and only if the points `p` 
with nonzero
weight are all equal (and in fact all equal to their center of mass w.r.t. `w`).
-/
lemma StrictConvexOn.map_sum_eq_iff' (hf : StrictConvexOn 𝕜 s f) (h₀ : ∀ i ∈ t, 0 ≤ w i)
    (h₁ : ∑ i ∈ t, w i = 1) (hmem : ∀ i ∈ t, p i ∈ s) :
    f (∑ i ∈ t, w i • p i) = ∑ i ∈ t, w i • f (p i) ↔
      ∀ j ∈ t, w j ≠ 0 → p j = ∑ i ∈ t, w i • p i := by
  have hw (i) (_ : i ∈ t) : w i • p i ≠ 0 → w i ≠ 0 := by simp_all
  have hw' (i) (_ : i ∈ t) : w i • f (p i) ≠ 0 → w i ≠ 0 := by simp_all
  rw [← sum_filter_of_ne hw, ← sum_filter_of_ne hw', hf.map_sum_eq_iff]
  · simp
  · simp +contextual [(h₀ _ _).lt_iff_ne']
  · rwa [sum_filter_ne_zero]
  · simp +contextual [hmem _ _]

/-- Canonical form of the **equality case of Jensen's equality**.

For a strictly concave function `f` and nonnegative weights `w`, we have
`f (∑ i ∈ t, w i • p i) = ∑ i ∈ t, w i • f (p i)` if and only if the points `p` with nonzero
weight are all equal (and in fact all equal to their center of mass w.r.t. `w`). -/
/-
**StrictConcaveOn.map_sum_eq_iff'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StrictConcaveOn.map_sum_eq_iff' (hf : StrictConcaveOn 𝕜 s f) (h₀ : forall 
i in t, 0 <= w i) (h₁ : ∑ i in t, w i = 1) (hmem : forall i in t, p i in s) : f 
(∑ i in t, w i • p i) = ∑ i in t, w i • f (p i) ↔ forall j in t, w j != 0 -> p j
 = ∑ i in t, w i • p i
参数：hf : StrictConcaveOn 𝕜 s f；h₀ : forall i in t, 0 <= w i；h₁ : ∑ i in t, w i = 
1；hmem : forall i in t, p i in s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `StrictConvexOn.map_sum_eq_iff'`：StrictConvexOn.map_sum_eq_iff' (hf : Str
ictConvexOn 𝕜 s f) (h₀ : forall i in t, 0 <= w i) (h₁ : ∑ i in t, w i = 1) (hmem
 : forall i in t, p …
· 使用定理 `OrderDual.isOrderedAddMonoid`：∀ {α : Type u} [inst : AddCommMonoid α] [i
nst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedAddMonoid αᵒᵈ
· 使用定理 `OrderDual.instIsStrictOrderedModule`：∀ {α : Type u_1} {β : Type u_2} [in
st : Preorder α] [inst_1 : MonoidWithZero α] [inst_2 : AddCommGroup β]   [inst_3
 : PartialOrder β] [IsOrd…
· 使用定理 `StrictConcaveOn.dual`：StrictConcaveOn.dual (hf : StrictConcaveOn 𝕜 s f) 
: StrictConvexOn 𝕜 s (toDual ∘ f)

--- 原说明 ---
Canonical form of the **equality case of Jensen's equality**.

For a strictly concave function `f` and nonnegative weights `w`, we have
`f (∑ i ∈ t, w i • p i) = ∑ i ∈ t, w i • f (p i)` if and only if the points `p` 
with nonzero
weight are all equal (and in fact all equal to their center of mass w.r.t. `w`).
-/
lemma StrictConcaveOn.map_sum_eq_iff' (hf : StrictConcaveOn 𝕜 s f) (h₀ : ∀ i ∈ t, 0 ≤ w i)
    (h₁ : ∑ i ∈ t, w i = 1) (hmem : ∀ i ∈ t, p i ∈ s) :
    f (∑ i ∈ t, w i • p i) = ∑ i ∈ t, w i • f (p i) ↔
      ∀ j ∈ t, w j ≠ 0 → p j = ∑ i ∈ t, w i • p i := hf.dual.map_sum_eq_iff' h₀ h₁ hmem

/-- Canonical form of the **strict Jensen's inequality**. -/
/-
**StrictConvexOn.map_sum_lt_iff_of_pos'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictConvexOn.map_sum_lt_iff_of_pos' (hf : StrictConvexOn 𝕜 s f) (h₀ : fo
rall i in t, 0 < w i) (h₁ : ∑ i in t, w i = 1) (hmem : forall i in t, p i in s) 
: f (∑ i in t, w i • p i) < ∑ i in t, w i • f (p i) ↔ exists j in t, p j != ∑ i 
in t, w i • p i
参数：hf : StrictConvexOn 𝕜 s f；h₀ : forall i in t, 0 < w i；h₁ : ∑ i in t, w i = 1；
hmem : forall i in t, p i in s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `LE.le.lt_iff_ne`：lt_iff_ne (h : a <= b) : a < b ↔ a != b
· 使用定理 `ConvexOn.map_sum_le`：ConvexOn.map_sum_le (hf : ConvexOn 𝕜 s f) (h₀ : for
all i in t, 0 <= w i) (h₁ : ∑ i in t, w i = 1) (hmem : forall i in t, p i in s) 
: f (∑ i …
· 使用定理 `StrictConvexOn.convexOn`：StrictConvexOn.convexOn {s : Set E} {f : E -> β
} (hf : StrictConvexOn 𝕜 s f) : ConvexOn 𝕜 s f
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose_iff₂`：contrapose_iff₂ {p q : Prop} 
: (p ↔ ¬ q) -> (¬ p ↔ q)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `StrictConvexOn.map_sum_eq_iff`：StrictConvexOn.map_sum_eq_iff {w : ι -> 𝕜
} {p : ι -> E} (hf : StrictConvexOn 𝕜 s f) (h₀ : forall i in t, 0 < w i) (h₁ : ∑
 i in t, w i = 1) (…

--- 原说明 ---
Canonical form of the **strict Jensen's inequality**.
-/
theorem StrictConvexOn.map_sum_lt_iff_of_pos' (hf : StrictConvexOn 𝕜 s f) (h₀ : ∀ i ∈ t, 0 < w i)
    (h₁ : ∑ i ∈ t, w i = 1) (hmem : ∀ i ∈ t, p i ∈ s) :
    f (∑ i ∈ t, w i • p i) < ∑ i ∈ t, w i • f (p i) ↔ ∃ j ∈ t, p j ≠ ∑ i ∈ t, w i • p i := by
  apply hf.convexOn.map_sum_le (h₀ · · |>.le) h₁ hmem |>.lt_iff_ne.trans
  contrapose!
  exact hf.map_sum_eq_iff h₀ h₁ hmem

/-- Canonical form of the **strict Jensen's inequality**. -/
/-
**StrictConcaveOn.lt_map_sum_iff_of_pos'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictConcaveOn.lt_map_sum_iff_of_pos' (hf : StrictConcaveOn 𝕜 s f) (h₀ : 
forall i in t, 0 < w i) (h₁ : ∑ i in t, w i = 1) (hmem : forall i in t, p i in s
) : ∑ i in t, w i • f (p i) < f (∑ i in t, w i • p i) ↔ exists j in t, p j != ∑ 
i in t, w i • p i
参数：hf : StrictConcaveOn 𝕜 s f；h₀ : forall i in t, 0 < w i；h₁ : ∑ i in t, w i = 1
；hmem : forall i in t, p i in s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictConvexOn.map_sum_lt_iff_of_pos'`：StrictConvexOn.map_sum_lt_iff_of_
pos' (hf : StrictConvexOn 𝕜 s f) (h₀ : forall i in t, 0 < w i) (h₁ : ∑ i in t, w
 i = 1) (hmem : forall i in…
· 使用定理 `OrderDual.isOrderedAddMonoid`：∀ {α : Type u} [inst : AddCommMonoid α] [i
nst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedAddMonoid αᵒᵈ
· 使用定理 `OrderDual.instIsStrictOrderedModule`：∀ {α : Type u_1} {β : Type u_2} [in
st : Preorder α] [inst_1 : MonoidWithZero α] [inst_2 : AddCommGroup β]   [inst_3
 : PartialOrder β] [IsOrd…
· 使用定理 `StrictConcaveOn.dual`：StrictConcaveOn.dual (hf : StrictConcaveOn 𝕜 s f) 
: StrictConvexOn 𝕜 s (toDual ∘ f)

--- 原说明 ---
Canonical form of the **strict Jensen's inequality**.
-/
theorem StrictConcaveOn.lt_map_sum_iff_of_pos' (hf : StrictConcaveOn 𝕜 s f) (h₀ : ∀ i ∈ t, 0 < w i)
    (h₁ : ∑ i ∈ t, w i = 1) (hmem : ∀ i ∈ t, p i ∈ s) :
    ∑ i ∈ t, w i • f (p i) < f (∑ i ∈ t, w i • p i) ↔ ∃ j ∈ t, p j ≠ ∑ i ∈ t, w i • p i :=
  hf.dual.map_sum_lt_iff_of_pos' h₀ h₁ hmem

/-- Canonical form of the **strict Jensen's inequality**. -/
/-
**StrictConvexOn.map_sum_lt_iff_of_nonneg'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictConvexOn.map_sum_lt_iff_of_nonneg' (hf : StrictConvexOn 𝕜 s f) (h₀ :
 forall i in t, 0 <= w i) (h₁ : ∑ i in t, w i = 1) (hmem : forall i in t, p i in
 s) : f (∑ i in t, w i • p i) < ∑ i in t, w i • f (p i) ↔ exists j in t, w j != 
0 ∧ p j != ∑ i in t, w i • p i
参数：hf : StrictConvexOn 𝕜 s f；h₀ : forall i in t, 0 <= w i；h₁ : ∑ i in t, w i = 1
；hmem : forall i in t, p i in s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictConvexOn.map_sum_lt_iff_of_pos'`：StrictConvexOn.map_sum_lt_iff_of_
pos' (hf : StrictConvexOn 𝕜 s f) (h₀ : forall i in t, 0 < w i) (h₁ : ∑ i in t, w
 i = 1) (hmem : forall i in…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_filter_ne_zero`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCo
mmMonoid M] {f : ι → M} (s : Finset ι)   [inst_1 : (x : ι) → Decidable (f x ≠ 0)
], ∑ x ∈ s with…
· 使用定理 `Finset.mem_of_mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : Decida
blePred p] {s : Finset α}, ∀ x ∈ Finset.filter p s, x ∈ s

--- 原说明 ---
Canonical form of the **strict Jensen's inequality**.
-/
theorem StrictConvexOn.map_sum_lt_iff_of_nonneg' (hf : StrictConvexOn 𝕜 s f) (h₀ : ∀ i ∈ t, 0 ≤ w i)
    (h₁ : ∑ i ∈ t, w i = 1) (hmem : ∀ i ∈ t, p i ∈ s) :
    f (∑ i ∈ t, w i • p i) < ∑ i ∈ t, w i • f (p i) ↔
      ∃ j ∈ t, w j ≠ 0 ∧ p j ≠ ∑ i ∈ t, w i • p i := by
  have :
      f (∑ i ∈ t with w i ≠ 0, w i • p i) < ∑ i ∈ t with w i ≠ 0, w i • f (p i) ↔
        ∃ j ∈ {x ∈ t | w x ≠ 0}, p j ≠ ∑ i ∈ t with w i ≠ 0, w i • p i :=
    hf.map_sum_lt_iff_of_pos' (by grind)
      (sum_filter_ne_zero _ |>.trans h₁) (hmem _ <| mem_of_mem_filter · ·)
  grind [sum_filter_of_ne, left_ne_zero_of_smul]

/-- Canonical form of the **strict Jensen's inequality**. -/
/-
**StrictConcaveOn.lt_map_sum_iff_of_nonneg'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：StrictConcaveOn.lt_map_sum_iff_of_nonneg' (hf : StrictConcaveOn 𝕜 s f) (h₀
 : forall i in t, 0 <= w i) (h₁ : ∑ i in t, w i = 1) (hmem : forall i in t, p i 
in s) : ∑ i in t, w i • f (p i) < f (∑ i in t, w i • p i) ↔ exists j in t, w j !
= 0 ∧ p j != ∑ i in t, w i • p i
参数：hf : StrictConcaveOn 𝕜 s f；h₀ : forall i in t, 0 <= w i；h₁ : ∑ i in t, w i = 
1；hmem : forall i in t, p i in s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictConvexOn.map_sum_lt_iff_of_nonneg'`：StrictConvexOn.map_sum_lt_iff_
of_nonneg' (hf : StrictConvexOn 𝕜 s f) (h₀ : forall i in t, 0 <= w i) (h₁ : ∑ i 
in t, w i = 1) (hmem : forall …
· 使用定理 `OrderDual.isOrderedAddMonoid`：∀ {α : Type u} [inst : AddCommMonoid α] [i
nst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedAddMonoid αᵒᵈ
· 使用定理 `OrderDual.instIsStrictOrderedModule`：∀ {α : Type u_1} {β : Type u_2} [in
st : Preorder α] [inst_1 : MonoidWithZero α] [inst_2 : AddCommGroup β]   [inst_3
 : PartialOrder β] [IsOrd…
· 使用定理 `StrictConcaveOn.dual`：StrictConcaveOn.dual (hf : StrictConcaveOn 𝕜 s f) 
: StrictConvexOn 𝕜 s (toDual ∘ f)

--- 原说明 ---
Canonical form of the **strict Jensen's inequality**.
-/
theorem StrictConcaveOn.lt_map_sum_iff_of_nonneg' (hf : StrictConcaveOn 𝕜 s f)
    (h₀ : ∀ i ∈ t, 0 ≤ w i) (h₁ : ∑ i ∈ t, w i = 1) (hmem : ∀ i ∈ t, p i ∈ s) :
    ∑ i ∈ t, w i • f (p i) < f (∑ i ∈ t, w i • p i) ↔ ∃ j ∈ t, w j ≠ 0 ∧ p j ≠ ∑ i ∈ t, w i • p i :=
  hf.dual.map_sum_lt_iff_of_nonneg' h₀ h₁ hmem

end Jensen

/-! ### Maximum principle -/


section MaximumPrinciple

variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup E]
  [AddCommGroup β] [LinearOrder β] [IsOrderedAddMonoid β] [Module 𝕜 E]
  [Module 𝕜 β] [IsStrictOrderedModule 𝕜 β] {s : Set E} {f : E → β} {w : ι → 𝕜} {p : ι → E}
  {x y z : E}

/-
**ConvexOn.le_sup_of_mem_convexHull** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ConvexOn.le_sup_of_mem_convexHull {t : Finset E} (hf : ConvexOn 𝕜 s f) (ht
s : ↑t subseteq s) (hx : x in convexHull 𝕜 (t : Set E)) : f x <= t.sup' (coe_non
empty.1 <| convexHull_nonempty_iff.1 ⟨x, hx⟩) f
参数：hf : ConvexOn 𝕜 s f；hts : ↑t subseteq s；hx : x in convexHull 𝕜 (t : Set E)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.coe_nonempty`：coe_nonempty {s : Finset α} : (s : Set α).Nonempty 
↔ s.Nonempty
· 使用定理 `convexHull_nonempty_iff`：convexHull_nonempty_iff : (convexHull 𝕜 s).None
mpty ↔ s.Nonempty
· 使用定理 `Finset.mem_convexHull`：Finset.mem_convexHull {s : Finset E} {x : E} : x 
in convexHull R (s : Set E) ↔ exists w : E -> R, (forall y in s, 0 <= w y) ∧ ∑ y
 in s, w y …
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `ConvexOn.map_centerMass_le`：ConvexOn.map_centerMass_le (hf : ConvexOn 𝕜 
s f) (h₀ : forall i in t, 0 <= w i) (h₁ : 0 < ∑ i in t, w i) (hmem : forall i in
 t, p i in s) : …
· 使用定理 `lt_of_lt_of_eq`：∀ {α : Type u_1} {a b c : α} [inst : LT α], a < b → b = 
c → a < c
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instNontrivialOfCharZero`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [
CharZero α], Nontrivial α
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.centerMass_le_sup`：centerMass_le_sup {s : Finset ι} {f : ι -> α} 
{w : ι -> R} (hw₀ : forall i in s, 0 <= w i) (hw₁ : 0 < ∑ i in s, w i) : s.cente
rMass w f <= s…
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
-/
theorem ConvexOn.le_sup_of_mem_convexHull {t : Finset E} (hf : ConvexOn 𝕜 s f) (hts : ↑t ⊆ s)
    (hx : x ∈ convexHull 𝕜 (t : Set E)) :
    f x ≤ t.sup' (coe_nonempty.1 <| convexHull_nonempty_iff.1 ⟨x, hx⟩) f := by
  obtain ⟨w, hw₀, hw₁, rfl⟩ := mem_convexHull.1 hx
  exact (hf.map_centerMass_le hw₀ (by positivity) hts).trans
    (centerMass_le_sup hw₀ <| by positivity)
/-
**ConvexOn.inf_le_of_mem_convexHull** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ConvexOn.inf_le_of_mem_convexHull {t : Finset E} (hf : ConcaveOn 𝕜 s f) (h
ts : ↑t subseteq s) (hx : x in convexHull 𝕜 (t : Set E)) : t.inf' (coe_nonempty.
1 <| convexHull_nonempty_iff.1 ⟨x, hx⟩) f <= f x
参数：hf : ConcaveOn 𝕜 s f；hts : ↑t subseteq s；hx : x in convexHull 𝕜 (t : Set E)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ConvexOn.le_sup_of_mem_convexHull`：ConvexOn.le_sup_of_mem_convexHull {t 
: Finset E} (hf : ConvexOn 𝕜 s f) (hts : ↑t subseteq s) (hx : x in convexHull 𝕜 
(t : Set E)) : f x <= t…
· 使用定理 `OrderDual.isOrderedAddMonoid`：∀ {α : Type u} [inst : AddCommMonoid α] [i
nst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedAddMonoid αᵒᵈ
· 使用定理 `OrderDual.instIsStrictOrderedModule`：∀ {α : Type u_1} {β : Type u_2} [in
st : Preorder α] [inst_1 : MonoidWithZero α] [inst_2 : AddCommGroup β]   [inst_3
 : PartialOrder β] [IsOrd…
· 使用定理 `ConcaveOn.dual`：ConcaveOn.dual (hf : ConcaveOn 𝕜 s f) : ConvexOn 𝕜 s (to
Dual ∘ f)
-/
theorem ConvexOn.inf_le_of_mem_convexHull {t : Finset E} (hf : ConcaveOn 𝕜 s f) (hts : ↑t ⊆ s)
    (hx : x ∈ convexHull 𝕜 (t : Set E)) :
    t.inf' (coe_nonempty.1 <| convexHull_nonempty_iff.1 ⟨x, hx⟩) f ≤ f x :=
  hf.dual.le_sup_of_mem_convexHull hts hx

/-- If a function `f` is convex on `s`, then the value it takes at some center of mass of points of
`s` is less than the value it takes on one of those points. -/
/-
**ConvexOn.exists_ge_of_centerMass** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ConvexOn.exists_ge_of_centerMass {t : Finset ι} (h : ConvexOn 𝕜 s f) (hw₀ 
: forall i in t, 0 <= w i) (hw₁ : 0 < ∑ i in t, w i) (hp : forall i in t, p i in
 s) : exists i in t, f (t.centerMass w p) <= f (p i)
参数：h : ConvexOn 𝕜 s f；hw₀ : forall i in t, 0 <= w i；hw₁ : 0 < ∑ i in t, w i；hp :
 forall i in t, p i in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_filter_ne_zero`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCo
mmMonoid M] {f : ι → M} (s : Finset ι)   [inst_1 : (x : ι) → Decidable (f x ≠ 0)
], ∑ x ∈ s with…
· 使用定理 `Finset.exists_le_of_sum_le`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddC
ommMonoid M] [inst_1 : LinearOrder M] {f g : ι → M} {s : Finset ι}   [IsOrderedC
ancelAddMonoid M…
· 使用定理 `IsOrderedAddMonoid.toIsOrderedCancelAddMonoid`：∀ {α : Type u} [inst : Ad
dCommGroup α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedCancelAddMo
noid α
· 使用定理 `Finset.nonempty_of_sum_ne_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Fin
set ι} {f : ι → M} [inst : AddCommMonoid M], ∑ x ∈ s, f x ≠ 0 → s.Nonempty
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_smul`：Finset.sum_smul {f : ι -> R} {s : Finset ι} {x : M} : (
∑ i in s, f i) • x = ∑ i in s, f i • x
· 使用引理 `smul_le_smul_iff_of_pos_left`：smul_le_smul_iff_of_pos_left [PosSMulMono 
α β] [PosSMulReflectLE α β] (ha : 0 < a) : a • b₁ <= a • b₂ ↔ b₁ <= b₂
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.isDomain`：∀ {R : Type u} [inst : Semiring R] [inst_1
 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], IsDomain R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inv_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : PartialOr
der G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a⁻¹ ↔ 0 < a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `inv_smul_smul₀`：∀ {α : Type u_4} {β : Type u_5} [inst : GroupWithZero α]
 [inst_1 : MulAction α β] {a : α},   a ≠ 0 → ∀ (x : β), a⁻¹ • a • x = x
· 使用定理 `Finset.centerMass.eq_1`：∀ {R : Type u_1} {E : Type u_3} {ι : Type u_5} [
inst : Field R] [inst_1 : AddCommGroup E] [inst_2 : _root_.Module R E]   (t : Fi
nset ι) (w :…
· 使用定理 `Finset.centerMass_filter_ne_zero`：Finset.centerMass_filter_ne_zero [fora
ll i, Decidable (w i != 0)] : {i in t | w i != 0}.centerMass w z = t.centerMass 
w z
· 使用定理 `ConvexOn.map_centerMass_le`：ConvexOn.map_centerMass_le (hf : ConvexOn 𝕜 
s f) (h₀ : forall i in t, 0 <= w i) (h₁ : 0 < ∑ i in t, w i) (hmem : forall i in
 t, p i in s) : …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LE.le.lt_of_ne`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a ≠ b → a < b
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
If a function `f` is convex on `s`, then the value it takes at some center of ma
ss of points of
`s` is less than the value it takes on one of those points.
-/
lemma ConvexOn.exists_ge_of_centerMass {t : Finset ι} (h : ConvexOn 𝕜 s f)
    (hw₀ : ∀ i ∈ t, 0 ≤ w i) (hw₁ : 0 < ∑ i ∈ t, w i) (hp : ∀ i ∈ t, p i ∈ s) :
    ∃ i ∈ t, f (t.centerMass w p) ≤ f (p i) := by
  set y := t.centerMass w p
  -- TODO: can `rsuffices` be used to write the `exact` first, then the proof of this obtain?
  obtain ⟨i, hi, hfi⟩ : ∃ i ∈ {i ∈ t | w i ≠ 0}, w i • f y ≤ w i • (f ∘ p) i := by
    have hw' : (0 : 𝕜) < ∑ i ∈ t with w i ≠ 0, w i := by rwa [sum_filter_ne_zero]
    refine exists_le_of_sum_le (nonempty_of_sum_ne_zero hw'.ne') ?_
    rw [← sum_smul, ← smul_le_smul_iff_of_pos_left (inv_pos.2 hw'), inv_smul_smul₀ hw'.ne', ←
      centerMass, centerMass_filter_ne_zero]
    exact h.map_centerMass_le hw₀ hw₁ hp
  rw [mem_filter] at hi
  exact ⟨i, hi.1, (smul_le_smul_iff_of_pos_left <| (hw₀ i hi.1).lt_of_ne hi.2.symm).1 hfi⟩

/-- If a function `f` is concave on `s`, then the value it takes at some center of mass of points of
`s` is greater than the value it takes on one of those points. -/
/-
**ConcaveOn.exists_le_of_centerMass** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ConcaveOn.exists_le_of_centerMass {t : Finset ι} (h : ConcaveOn 𝕜 s f) (hw
₀ : forall i in t, 0 <= w i) (hw₁ : 0 < ∑ i in t, w i) (hp : forall i in t, p i 
in s) : exists i in t, f (p i) <= f (t.centerMass w p)
参数：h : ConcaveOn 𝕜 s f；hw₀ : forall i in t, 0 <= w i；hw₁ : 0 < ∑ i in t, w i；hp 
: forall i in t, p i in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ConvexOn.exists_ge_of_centerMass`：ConvexOn.exists_ge_of_centerMass {t : 
Finset ι} (h : ConvexOn 𝕜 s f) (hw₀ : forall i in t, 0 <= w i) (hw₁ : 0 < ∑ i in
 t, w i) (hp : forall …
· 使用定理 `OrderDual.isOrderedAddMonoid`：∀ {α : Type u} [inst : AddCommMonoid α] [i
nst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedAddMonoid αᵒᵈ
· 使用定理 `OrderDual.instIsStrictOrderedModule`：∀ {α : Type u_1} {β : Type u_2} [in
st : Preorder α] [inst_1 : MonoidWithZero α] [inst_2 : AddCommGroup β]   [inst_3
 : PartialOrder β] [IsOrd…
· 使用定理 `ConcaveOn.dual`：ConcaveOn.dual (hf : ConcaveOn 𝕜 s f) : ConvexOn 𝕜 s (to
Dual ∘ f)

--- 原说明 ---
If a function `f` is concave on `s`, then the value it takes at some center of m
ass of points of
`s` is greater than the value it takes on one of those points.
-/
lemma ConcaveOn.exists_le_of_centerMass {t : Finset ι} (h : ConcaveOn 𝕜 s f)
    (hw₀ : ∀ i ∈ t, 0 ≤ w i) (hw₁ : 0 < ∑ i ∈ t, w i) (hp : ∀ i ∈ t, p i ∈ s) :
    ∃ i ∈ t, f (p i) ≤ f (t.centerMass w p) := h.dual.exists_ge_of_centerMass hw₀ hw₁ hp

/-- **Maximum principle** for convex functions. If a function `f` is convex on the convex hull of
`s`, then the eventual maximum of `f` on `convexHull 𝕜 s` lies in `s`. -/
/-
**ConvexOn.exists_ge_of_mem_convexHull** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ConvexOn.exists_ge_of_mem_convexHull {t : Set E} (hf : ConvexOn 𝕜 s f) (ht
s : t subseteq s) (hx : x in convexHull 𝕜 t) : exists y in t, f x <= f y
参数：hf : ConvexOn 𝕜 s f；hts : t subseteq s；hx : x in convexHull 𝕜 t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `convexHull_eq`：convexHull_eq (s : Set E) : convexHull R s = { x : E | ex
ists (ι : Type) (t : Finset ι) (w : ι -> R) (z : ι -> E), (forall i in t, 0 <= w
 i)…
· 使用引理 `ConvexOn.exists_ge_of_centerMass`：ConvexOn.exists_ge_of_centerMass {t : 
Finset ι} (h : ConvexOn 𝕜 s f) (hw₀ : forall i in t, 0 <= w i) (hw₁ : 0 < ∑ i in
 t, w i) (hp : forall …
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
**Maximum principle** for convex functions. If a function `f` is convex on the c
onvex hull of
`s`, then the eventual maximum of `f` on `convexHull 𝕜 s` lies in `s`.
-/
lemma ConvexOn.exists_ge_of_mem_convexHull {t : Set E} (hf : ConvexOn 𝕜 s f) (hts : t ⊆ s)
    (hx : x ∈ convexHull 𝕜 t) : ∃ y ∈ t, f x ≤ f y := by
  rw [_root_.convexHull_eq] at hx
  obtain ⟨α, t, w, p, hw₀, hw₁, hp, rfl⟩ := hx
  obtain ⟨i, hit, Hi⟩ := hf.exists_ge_of_centerMass hw₀ (hw₁.symm ▸ zero_lt_one)
    fun i hi ↦ hts (hp i hi)
  exact ⟨p i, hp i hit, Hi⟩

/-- **Minimum principle** for concave functions. If a function `f` is concave on the convex hull of
`s`, then the eventual minimum of `f` on `convexHull 𝕜 s` lies in `s`. -/
/-
**ConcaveOn.exists_le_of_mem_convexHull** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ConcaveOn.exists_le_of_mem_convexHull {t : Set E} (hf : ConcaveOn 𝕜 s f) (
hts : t subseteq s) (hx : x in convexHull 𝕜 t) : exists y in t, f y <= f x
参数：hf : ConcaveOn 𝕜 s f；hts : t subseteq s；hx : x in convexHull 𝕜 t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ConvexOn.exists_ge_of_mem_convexHull`：ConvexOn.exists_ge_of_mem_convexHu
ll {t : Set E} (hf : ConvexOn 𝕜 s f) (hts : t subseteq s) (hx : x in convexHull 
𝕜 t) : exists y in t, f x …
· 使用定理 `OrderDual.isOrderedAddMonoid`：∀ {α : Type u} [inst : AddCommMonoid α] [i
nst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedAddMonoid αᵒᵈ
· 使用定理 `OrderDual.instIsStrictOrderedModule`：∀ {α : Type u_1} {β : Type u_2} [in
st : Preorder α] [inst_1 : MonoidWithZero α] [inst_2 : AddCommGroup β]   [inst_3
 : PartialOrder β] [IsOrd…
· 使用定理 `ConcaveOn.dual`：ConcaveOn.dual (hf : ConcaveOn 𝕜 s f) : ConvexOn 𝕜 s (to
Dual ∘ f)

--- 原说明 ---
**Minimum principle** for concave functions. If a function `f` is concave on the
 convex hull of
`s`, then the eventual minimum of `f` on `convexHull 𝕜 s` lies in `s`.
-/
lemma ConcaveOn.exists_le_of_mem_convexHull {t : Set E} (hf : ConcaveOn 𝕜 s f) (hts : t ⊆ s)
    (hx : x ∈ convexHull 𝕜 t) : ∃ y ∈ t, f y ≤ f x := hf.dual.exists_ge_of_mem_convexHull hts hx

/-- **Maximum principle** for convex functions on a segment. If a function `f` is convex on the
segment `[x, y]`, then the eventual maximum of `f` on `[x, y]` is at `x` or `y`. -/
/-
**ConvexOn.le_max_of_mem_segment** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ConvexOn.le_max_of_mem_segment (hf : ConvexOn 𝕜 s f) (hx : x in s) (hy : y
 in s) (hz : z in [x -[𝕜] y]) : f z <= max (f x) (f y)
参数：hf : ConvexOn 𝕜 s f；hx : x in s；hy : y in s；hz : z in [x -[𝕜] y]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用引理 `ConvexOn.exists_ge_of_mem_convexHull`：ConvexOn.exists_ge_of_mem_convexHu
ll {t : Set E} (hf : ConvexOn 𝕜 s f) (hts : t subseteq s) (hx : x in convexHull 
𝕜 t) : exists y in t, f x …
· 使用定理 `Set.pair_subset`：pair_subset (ha : a in s) (hb : b in s) : {a, b} subset
eq s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `convexHull_pair`：convexHull_pair [IsOrderedRing 𝕜] (x y : E) : convexHul
l 𝕜 {x, y} = segment 𝕜 x y
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R

--- 原说明 ---
**Maximum principle** for convex functions on a segment. If a function `f` is co
nvex on the
segment `[x, y]`, then the eventual maximum of `f` on `[x, y]` is at `x` or `y`.
-/
lemma ConvexOn.le_max_of_mem_segment (hf : ConvexOn 𝕜 s f) (hx : x ∈ s) (hy : y ∈ s)
    (hz : z ∈ [x -[𝕜] y]) : f z ≤ max (f x) (f y) := by
  rw [← convexHull_pair] at hz; simpa using hf.exists_ge_of_mem_convexHull (pair_subset hx hy) hz

/-- **Minimum principle** for concave functions on a segment. If a function `f` is concave on the
segment `[x, y]`, then the eventual minimum of `f` on `[x, y]` is at `x` or `y`. -/
/-
**ConcaveOn.min_le_of_mem_segment** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ConcaveOn.min_le_of_mem_segment (hf : ConcaveOn 𝕜 s f) (hx : x in s) (hy :
 y in s) (hz : z in [x -[𝕜] y]) : min (f x) (f y) <= f z
参数：hf : ConcaveOn 𝕜 s f；hx : x in s；hy : y in s；hz : z in [x -[𝕜] y]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ConvexOn.le_max_of_mem_segment`：ConvexOn.le_max_of_mem_segment (hf : Con
vexOn 𝕜 s f) (hx : x in s) (hy : y in s) (hz : z in [x -[𝕜] y]) : f z <= max (f 
x) (f y)
· 使用定理 `OrderDual.isOrderedAddMonoid`：∀ {α : Type u} [inst : AddCommMonoid α] [i
nst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedAddMonoid αᵒᵈ
· 使用定理 `OrderDual.instIsStrictOrderedModule`：∀ {α : Type u_1} {β : Type u_2} [in
st : Preorder α] [inst_1 : MonoidWithZero α] [inst_2 : AddCommGroup β]   [inst_3
 : PartialOrder β] [IsOrd…
· 使用定理 `ConcaveOn.dual`：ConcaveOn.dual (hf : ConcaveOn 𝕜 s f) : ConvexOn 𝕜 s (to
Dual ∘ f)

--- 原说明 ---
**Minimum principle** for concave functions on a segment. If a function `f` is c
oncave on the
segment `[x, y]`, then the eventual minimum of `f` on `[x, y]` is at `x` or `y`.
-/
lemma ConcaveOn.min_le_of_mem_segment (hf : ConcaveOn 𝕜 s f) (hx : x ∈ s) (hy : y ∈ s)
    (hz : z ∈ [x -[𝕜] y]) : min (f x) (f y) ≤ f z := hf.dual.le_max_of_mem_segment hx hy hz

/-- **Maximum principle** for convex functions on an interval. If a function `f` is convex on the
interval `[x, y]`, then the eventual maximum of `f` on `[x, y]` is at `x` or `y`. -/
/-
**ConvexOn.le_max_of_mem_Icc** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ConvexOn.le_max_of_mem_Icc {s : Set 𝕜} {f : 𝕜 -> β} {x y z : 𝕜} (hf : Conv
exOn 𝕜 s f) (hx : x in s) (hy : y in s) (hz : z in Icc x y) : f z <= max (f x) (
f y)
参数：hf : ConvexOn 𝕜 s f；hx : x in s；hy : y in s；hz : z in Icc x y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ConvexOn.le_max_of_mem_segment`：ConvexOn.le_max_of_mem_segment (hf : Con
vexOn 𝕜 s f) (hx : x in s) (hy : y in s) (hz : z in [x -[𝕜] y]) : f z <= max (f 
x) (f y)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `segment_eq_Icc`：segment_eq_Icc (h : x <= y) : [x -[𝕜] y] = Icc x y
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
**Maximum principle** for convex functions on an interval. If a function `f` is 
convex on the
interval `[x, y]`, then the eventual maximum of `f` on `[x, y]` is at `x` or `y`
.
-/
lemma ConvexOn.le_max_of_mem_Icc {s : Set 𝕜} {f : 𝕜 → β} {x y z : 𝕜} (hf : ConvexOn 𝕜 s f)
    (hx : x ∈ s) (hy : y ∈ s) (hz : z ∈ Icc x y) : f z ≤ max (f x) (f y) := by
  rw [← segment_eq_Icc (hz.1.trans hz.2)] at hz; exact hf.le_max_of_mem_segment hx hy hz

/-- **Minimum principle** for concave functions on an interval. If a function `f` is concave on the
interval `[x, y]`, then the eventual minimum of `f` on `[x, y]` is at `x` or `y`. -/
/-
**ConcaveOn.min_le_of_mem_Icc** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ConcaveOn.min_le_of_mem_Icc {s : Set 𝕜} {f : 𝕜 -> β} {x y z : 𝕜} (hf : Con
caveOn 𝕜 s f) (hx : x in s) (hy : y in s) (hz : z in Icc x y) : min (f x) (f y) 
<= f z
参数：hf : ConcaveOn 𝕜 s f；hx : x in s；hy : y in s；hz : z in Icc x y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ConvexOn.le_max_of_mem_Icc`：ConvexOn.le_max_of_mem_Icc {s : Set 𝕜} {f : 
𝕜 -> β} {x y z : 𝕜} (hf : ConvexOn 𝕜 s f) (hx : x in s) (hy : y in s) (hz : z in
 Icc x y) : f z …
· 使用定理 `OrderDual.isOrderedAddMonoid`：∀ {α : Type u} [inst : AddCommMonoid α] [i
nst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedAddMonoid αᵒᵈ
· 使用定理 `OrderDual.instIsStrictOrderedModule`：∀ {α : Type u_1} {β : Type u_2} [in
st : Preorder α] [inst_1 : MonoidWithZero α] [inst_2 : AddCommGroup β]   [inst_3
 : PartialOrder β] [IsOrd…
· 使用定理 `ConcaveOn.dual`：ConcaveOn.dual (hf : ConcaveOn 𝕜 s f) : ConvexOn 𝕜 s (to
Dual ∘ f)

--- 原说明 ---
**Minimum principle** for concave functions on an interval. If a function `f` is
 concave on the
interval `[x, y]`, then the eventual minimum of `f` on `[x, y]` is at `x` or `y`
.
-/
lemma ConcaveOn.min_le_of_mem_Icc {s : Set 𝕜} {f : 𝕜 → β} {x y z : 𝕜} (hf : ConcaveOn 𝕜 s f)
    (hx : x ∈ s) (hy : y ∈ s) (hz : z ∈ Icc x y) : min (f x) (f y) ≤ f z :=
  hf.dual.le_max_of_mem_Icc hx hy hz
/-
**ConvexOn.bddAbove_convexHull** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ConvexOn.bddAbove_convexHull {s t : Set E} (hst : s subseteq t) (hf : Conv
exOn 𝕜 t f) : BddAbove (f '' s) -> BddAbove (f '' convexHull 𝕜 s)
参数：hst : s subseteq t；hf : ConvexOn 𝕜 t f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ConvexOn.exists_ge_of_mem_convexHull`：ConvexOn.exists_ge_of_mem_convexHu
ll {t : Set E} (hf : ConvexOn 𝕜 s f) (hts : t subseteq s) (hx : x in convexHull 
𝕜 t) : exists y in t, f x …
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
-/
lemma ConvexOn.bddAbove_convexHull {s t : Set E} (hst : s ⊆ t) (hf : ConvexOn 𝕜 t f) :
    BddAbove (f '' s) → BddAbove (f '' convexHull 𝕜 s) := by
  rintro ⟨b, hb⟩
  refine ⟨b, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨y, hy, hxy⟩ := hf.exists_ge_of_mem_convexHull hst hx
  exact hxy.trans <| hb <| mem_image_of_mem _ hy
/-
**ConcaveOn.bddBelow_convexHull** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ConcaveOn.bddBelow_convexHull {s t : Set E} (hst : s subseteq t) (hf : Con
caveOn 𝕜 t f) : BddBelow (f '' s) -> BddBelow (f '' convexHull 𝕜 s)
参数：hst : s subseteq t；hf : ConcaveOn 𝕜 t f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ConvexOn.bddAbove_convexHull`：ConvexOn.bddAbove_convexHull {s t : Set E}
 (hst : s subseteq t) (hf : ConvexOn 𝕜 t f) : BddAbove (f '' s) -> BddAbove (f '
' convexHull 𝕜 s)
· 使用定理 `OrderDual.isOrderedAddMonoid`：∀ {α : Type u} [inst : AddCommMonoid α] [i
nst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedAddMonoid αᵒᵈ
· 使用定理 `OrderDual.instIsStrictOrderedModule`：∀ {α : Type u_1} {β : Type u_2} [in
st : Preorder α] [inst_1 : MonoidWithZero α] [inst_2 : AddCommGroup β]   [inst_3
 : PartialOrder β] [IsOrd…
· 使用定理 `ConcaveOn.dual`：ConcaveOn.dual (hf : ConcaveOn 𝕜 s f) : ConvexOn 𝕜 s (to
Dual ∘ f)
-/
lemma ConcaveOn.bddBelow_convexHull {s t : Set E} (hst : s ⊆ t) (hf : ConcaveOn 𝕜 t f) :
    BddBelow (f '' s) → BddBelow (f '' convexHull 𝕜 s) := hf.dual.bddAbove_convexHull hst

end MaximumPrinciple

