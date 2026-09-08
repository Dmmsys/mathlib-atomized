/-
Copyright (c) 2018 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Data.Fintype.Lattice
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.MetricSpace.Antilipschitz

/-!
# Isometries

We define isometries, i.e., maps between emetric spaces that preserve
the edistance (on metric spaces, these are exactly the maps that preserve distances),
and prove their basic properties. We also introduce isometric bijections.

Since a lot of elementary properties don't require `eq_of_dist_eq_zero` we start setting up the
theory for `PseudoMetricSpace` and we specialize to `MetricSpace` when needed.
-/

@[expose] public section

open Topology

noncomputable section

universe u v w

variable {F ι : Type*} {α : Type u} {β : Type v} {γ : Type w}

open Function Set

open scoped Topology ENNReal

/-- An isometry (also known as isometric embedding) is a map preserving the edistance
between pseudoemetric spaces, or equivalently the distance between pseudometric space. -/
/-
**Isometry** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Isometry [PseudoEMetricSpace α] [PseudoEMetricSpace β] (f : α -> β) : Prop
参数：f : α -> β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An isometry (also known as isometric embedding) is a map preserving the edistanc
e
between pseudoemetric spaces, or equivalently the distance between pseudometric 
space.
-/
def Isometry [PseudoEMetricSpace α] [PseudoEMetricSpace β] (f : α → β) : Prop :=
  ∀ x1 x2 : α, edist (f x1) (f x2) = edist x1 x2

/-- On pseudometric spaces, a map is an isometry if and only if it preserves nonnegative
distances. -/
/-
**isometry_iff_nndist_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isometry_iff_nndist_eq [PseudoMetricSpace α] [PseudoMetricSpace β] {f : α 
-> β} : Isometry f ↔ forall x y, nndist (f x) (f y) = nndist x y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `edist_nndist`：edist_nndist (x y : α) : edist x y = nndist x y
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
On pseudometric spaces, a map is an isometry if and only if it preserves nonnega
tive
distances.
-/
theorem isometry_iff_nndist_eq [PseudoMetricSpace α] [PseudoMetricSpace β] {f : α → β} :
    Isometry f ↔ ∀ x y, nndist (f x) (f y) = nndist x y := by
  simp only [Isometry, edist_nndist, ENNReal.coe_inj]

/-- On pseudometric spaces, a map is an isometry if and only if it preserves distances. -/
/-
**isometry_iff_dist_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isometry_iff_dist_eq [PseudoMetricSpace α] [PseudoMetricSpace β] {f : α ->
 β} : Isometry f ↔ forall x y, dist (f x) (f y) = dist x y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
On pseudometric spaces, a map is an isometry if and only if it preserves distanc
es.
-/
theorem isometry_iff_dist_eq [PseudoMetricSpace α] [PseudoMetricSpace β] {f : α → β} :
    Isometry f ↔ ∀ x y, dist (f x) (f y) = dist x y := by
  simp only [isometry_iff_nndist_eq, ← coe_nndist, NNReal.coe_inj]

/-- An isometry preserves distances. -/
alias ⟨Isometry.dist_eq, _⟩ := isometry_iff_dist_eq

/-- A map that preserves distances is an isometry -/
alias ⟨_, Isometry.of_dist_eq⟩ := isometry_iff_dist_eq

/-- An isometry preserves non-negative distances. -/
alias ⟨Isometry.nndist_eq, _⟩ := isometry_iff_nndist_eq

/-- A map that preserves non-negative distances is an isometry. -/
alias ⟨_, Isometry.of_nndist_eq⟩ := isometry_iff_nndist_eq

namespace Isometry

section PseudoEMetricIsometry

variable [PseudoEMetricSpace α] [PseudoEMetricSpace β] [PseudoEMetricSpace γ]
variable {f : α → β} {x : α}

/-- An isometry preserves edistances. -/
/-
**Isometry.edist_eq** 是 Mathlib 中的一个定理，位于命名空间 `Isometry`。
形式化陈述：edist_eq (hf : Isometry f) (x y : α) : edist (f x) (f y) = edist x y
参数：hf : Isometry f；x y : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An isometry preserves edistances.
-/
theorem edist_eq (hf : Isometry f) (x y : α) : edist (f x) (f y) = edist x y :=
  hf x y
/-
**Isometry.lipschitz** 是 Mathlib 中的一个定理，位于命名空间 `Isometry`。
形式化陈述：lipschitz (h : Isometry f) : LipschitzWith 1 f
参数：h : Isometry f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzWith.of_edist_le`：∀ {α : Type u} {β : Type v} [inst : PseudoEMe
tricSpace α] [inst_1 : PseudoEMetricSpace β] {f : α → β},   (∀ (x y : α), edist 
(f x) (f y) ≤ e…
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
-/
theorem lipschitz (h : Isometry f) : LipschitzWith 1 f :=
  LipschitzWith.of_edist_le fun x y => (h x y).le
/-
**Isometry.antilipschitz** 是 Mathlib 中的一个定理，位于命名空间 `Isometry`。
形式化陈述：antilipschitz (h : Isometry f) : AntilipschitzWith 1 f
参数：h : Isometry f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem antilipschitz (h : Isometry f) : AntilipschitzWith 1 f := fun x y => by
  simp only [h x y, ENNReal.coe_one, one_mul, le_refl]

/-- Any map on a subsingleton is an isometry -/
@[nontriviality]
/-
**Isometry._root_.isometry_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `Isometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any map on a subsingleton is an isometry
-/
theorem _root_.isometry_subsingleton [Subsingleton α] : Isometry f := fun x y => by
  rw [Subsingleton.elim x y]; simp

/-- The identity is an isometry -/
/-
**Isometry._root_.isometry_id** 是 Mathlib 中的一个定理，位于命名空间 `Isometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity is an isometry
-/
theorem _root_.isometry_id : Isometry (id : α → α) := fun _ _ => rfl
/-
**Isometry.prodMap** 是 Mathlib 中的一个定理，位于命名空间 `Isometry`。
形式化陈述：prodMap {δ} [PseudoEMetricSpace δ] {f : α -> β} {g : γ -> δ} (hf : Isometr
y f) (hg : Isometry g) : Isometry (Prod.map f g)
参数：hf : Isometry f；hg : Isometry g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Isometry.edist_eq`：edist_eq (hf : Isometry f) (x y : α) : edist (f x) (f
 y) = edist x y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prodMap {δ} [PseudoEMetricSpace δ] {f : α → β} {g : γ → δ} (hf : Isometry f)
    (hg : Isometry g) : Isometry (Prod.map f g) := fun x y => by
  simp only [Prod.edist_eq, Prod.map_fst, hf.edist_eq, Prod.map_snd, hg.edist_eq]
/-
**Isometry.piMap** 是 Mathlib 中的一个定理，位于命名空间 `Isometry`。
形式化陈述：∀ {ι : Type u_5} [inst : Fintype ι] {α : ι → Type u_3} {β : ι → Type u_4} 
[inst_1 : (i : ι) → PseudoEMetricSpace (α i)]   [inst_2 : (i : ι) → PseudoEMetri
cSpace (β i)] (f : (i : ι) → α i → β i),   (∀ (i : ι), Isometry (f i)) → Isometr
y (Pi.map f)
参数：i : ι；α i；i : ι；β i；f : (i : ι) → α i → β i；∀ (i : ι), Isometry (f i)；Pi.map 
f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Isometry.edist_eq`：edist_eq (hf : Isometry f) (x y : α) : edist (f x) (f
 y) = edist x y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem piMap {ι} [Fintype ι] {α β : ι → Type*} [∀ i, PseudoEMetricSpace (α i)]
    [∀ i, PseudoEMetricSpace (β i)] (f : ∀ i, α i → β i) (hf : ∀ i, Isometry (f i)) :
    Isometry (Pi.map f) := fun x y => by
  simp only [edist_pi_def, (hf _).edist_eq, Pi.map_apply]
/-
**Isometry.single** 是 Mathlib 中的一个定义，位于命名空间 `QuadraticMap`。
形式化陈述：Isometry.single [Fintype ι] [DecidableEq ι] (Q : forall i, QuadraticMap R 
(Mᵢ i) P) (i : ι) : Q i ->qᵢ pi Q where toLinearMap
参数：Q : forall i, QuadraticMap R (Mᵢ i) P；i : ι。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `edist_pi_def`：edist_pi_def [forall b, EDist (X b)] (f g : forall b, X b)
 : edist f g = Finset.sup univ fun b => edist (f b) (g b)
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Finset.sup_le`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSup α]
 [inst_1 : OrderBot α] {s : Finset β} {f : β → α} {a : α},   (∀ b ∈ s, f b ≤ a) 
→ s…
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Pi.single_eq_same`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) →
 Zero (M i)] [inst_1 : DecidableEq ι] (i : ι) (x : M i),   Pi.single i x i = x
· 使用定理 `Pi.single_eq_of_ne'`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι)
 → Zero (M i)] [inst_1 : DecidableEq ι] {i i' : ι},   i ≠ i' → ∀ (x : M i), Pi.s
ingle i x…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `PseudoEMetricSpace.edist_self`：∀ {α : Type u} [self : PseudoEMetricSpace
 α] (x : α), edist x x = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `Finset.le_sup_of_le`：le_sup_of_le {b : β} (hb : b in s) (h : a <= f b) :
 a <= s.sup f
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
-/
protected lemma single [Fintype ι] [DecidableEq ι] {E : ι → Type*} [∀ i, PseudoEMetricSpace (E i)]
    [∀ i, Zero (E i)] (i : ι) :
    Isometry (Pi.single (M := E) i) := by
  intro x y
  rw [edist_pi_def]
  refine le_antisymm (Finset.sup_le fun j ↦ ?_) (Finset.le_sup_of_le (Finset.mem_univ i) (by simp))
  obtain rfl | h := eq_or_ne i j
  · simp
  · simp [h]
/-
**Isometry.inl** 是 Mathlib 中的一个定义，位于命名空间 `QuadraticMap`。
形式化陈述：Isometry.inl (Q₁ : QuadraticMap R M₁ P) (Q₂ : QuadraticMap R M₂ P) : Q₁ ->
qᵢ (Q₁.prod Q₂) where toLinearMap
参数：Q₁ : QuadraticMap R M₁ P；Q₂ : QuadraticMap R M₂ P。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Prod.edist_eq`：Prod.edist_eq [PseudoEMetricSpace β] (x y : α × β) : edis
t x y = max (edist x.1 y.1) (edist x.2 y.2)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `PseudoEMetricSpace.edist_self`：∀ {α : Type u} [self : PseudoEMetricSpace
 α] (x : α), edist x x = 0
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected lemma inl [AddZeroClass α] [AddZeroClass β] : Isometry (AddMonoidHom.inl α β) := by
  intro x y
  rw [Prod.edist_eq]
  simp
/-
**Isometry.inr** 是 Mathlib 中的一个定义，位于命名空间 `QuadraticMap`。
形式化陈述：Isometry.inr (Q₁ : QuadraticMap R M₁ P) (Q₂ : QuadraticMap R M₂ P) : Q₂ ->
qᵢ (Q₁.prod Q₂) where toLinearMap
参数：Q₁ : QuadraticMap R M₁ P；Q₂ : QuadraticMap R M₂ P。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Prod.edist_eq`：Prod.edist_eq [PseudoEMetricSpace β] (x y : α × β) : edis
t x y = max (edist x.1 y.1) (edist x.2 y.2)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `PseudoEMetricSpace.edist_self`：∀ {α : Type u} [self : PseudoEMetricSpace
 α] (x : α), edist x x = 0
· 使用定理 `sup_of_le_right`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, a ≤
 b → a ⊔ b = b
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected lemma inr [AddZeroClass α] [AddZeroClass β] : Isometry (AddMonoidHom.inr α β) := by
  intro x y
  rw [Prod.edist_eq]
  simp

/-- The composition of isometries is an isometry. -/
/-
**Isometry.comp** 是 Mathlib 中的一个定理，位于命名空间 `Isometry`。
形式化陈述：comp {g : β -> γ} {f : α -> β} (hg : Isometry g) (hf : Isometry f) : Isome
try (g ∘ f)
参数：hg : Isometry g；hf : Isometry f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c

--- 原说明 ---
The composition of isometries is an isometry.
-/
theorem comp {g : β → γ} {f : α → β} (hg : Isometry g) (hf : Isometry f) : Isometry (g ∘ f) :=
  fun _ _ => (hg _ _).trans (hf _ _)

omit [PseudoEMetricSpace α] in
/-
**Isometry.postcomp_pi** 是 Mathlib 中的一个引理，位于命名空间 `Isometry`。
形式化陈述：postcomp_pi [Fintype α] {g : β -> γ} (hg : Isometry g) : Isometry (fun f :
 α -> β => g ∘ f)
参数：hg : Isometry g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Isometry.edist_eq`：edist_eq (hf : Isometry f) (x y : α) : edist (f x) (f
 y) = edist x y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma postcomp_pi [Fintype α] {g : β → γ} (hg : Isometry g) : Isometry (fun f : α → β ↦ g ∘ f) :=
  fun _ _ ↦ by simp [edist_pi_def, hg.edist_eq]

/-- An isometry from a metric space is a uniform continuous map -/
/-
**Isometry.uniformContinuous** 是 Mathlib 中的一个定理，位于命名空间 `Isometry`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : PseudoEMetricSpace α] [inst_1 : Pseudo
EMetricSpace β] {f : α → β},   Isometry f → UniformContinuous f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzWith.uniformContinuous`：∀ {α : Type u} {β : Type v} [inst : Pse
udoEMetricSpace α] [inst_1 : PseudoEMetricSpace β] {K : NNReal} {f : α → β},   L
ipschitzWith K f → Un…
· 使用定理 `Isometry.lipschitz`：lipschitz (h : Isometry f) : LipschitzWith 1 f

--- 原说明 ---
An isometry from a metric space is a uniform continuous map
-/
protected theorem uniformContinuous (hf : Isometry f) : UniformContinuous f :=
  hf.lipschitz.uniformContinuous

/-- An isometry from a metric space is a uniform inducing map -/
/-
**Isometry.isUniformInducing** 是 Mathlib 中的一个定理，位于命名空间 `Isometry`。
形式化陈述：isUniformInducing (hf : Isometry f) : IsUniformInducing f
参数：hf : Isometry f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AntilipschitzWith.isUniformInducing`：isUniformInducing (hf : Antilipschi
tzWith K f) (hfc : UniformContinuous f) : IsUniformInducing f
· 使用定理 `Isometry.antilipschitz`：antilipschitz (h : Isometry f) : AntilipschitzWi
th 1 f
· 使用定理 `Isometry.uniformContinuous`：∀ {α : Type u} {β : Type v} [inst : PseudoEM
etricSpace α] [inst_1 : PseudoEMetricSpace β] {f : α → β},   Isometry f → Unifor
mContinuous f

--- 原说明 ---
An isometry from a metric space is a uniform inducing map
-/
theorem isUniformInducing (hf : Isometry f) : IsUniformInducing f :=
  hf.antilipschitz.isUniformInducing hf.uniformContinuous
/-
**Isometry.tendsto_nhds_iff** 是 Mathlib 中的一个定理，位于命名空间 `Isometry`。
形式化陈述：tendsto_nhds_iff {ι : Type*} {f : α -> β} {g : ι -> α} {a : Filter ι} {b :
 α} (hf : Isometry f) : Filter.Tendsto g a (𝓝 b) ↔ Filter.Tendsto (f ∘ g) a (𝓝 (
f b))
参数：hf : Isometry f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Topology.IsInducing.tendsto_nhds_iff`：tendsto_nhds_iff {f : ι -> Y} {l :
 Filter ι} {y : Y} (hg : IsInducing g) : Tendsto f l (𝓝 y) ↔ Tendsto (g ∘ f) l (
𝓝 (g y))
· 使用定理 `IsUniformInducing.isInducing`：IsUniformInducing.isInducing {f : α -> β} 
(h : IsUniformInducing f) : IsInducing f
· 使用定理 `Isometry.isUniformInducing`：isUniformInducing (hf : Isometry f) : IsUnif
ormInducing f
-/
theorem tendsto_nhds_iff {ι : Type*} {f : α → β} {g : ι → α} {a : Filter ι} {b : α}
    (hf : Isometry f) : Filter.Tendsto g a (𝓝 b) ↔ Filter.Tendsto (f ∘ g) a (𝓝 (f b)) :=
  hf.isUniformInducing.isInducing.tendsto_nhds_iff

/-- An isometry is continuous. -/
/-
**Isometry.continuous** 是 Mathlib 中的一个定理，位于命名空间 `Isometry`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : PseudoEMetricSpace α] [inst_1 : Pseudo
EMetricSpace β] {f : α → β},   Isometry f → Continuous f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LipschitzWith.continuous`：∀ {α : Type u} {β : Type v} [inst : PseudoEMet
ricSpace α] [inst_1 : PseudoEMetricSpace β] {K : NNReal} {f : α → β},   Lipschit
zWith K f → Co…
· 使用定理 `Isometry.lipschitz`：lipschitz (h : Isometry f) : LipschitzWith 1 f

--- 原说明 ---
An isometry is continuous.
-/
protected theorem continuous (hf : Isometry f) : Continuous f :=
  hf.lipschitz.continuous

/-- The right inverse of an isometry is an isometry. -/
/-
**Isometry.right_inv** 是 Mathlib 中的一个定理，位于命名空间 `Isometry`。
形式化陈述：right_inv {f : α -> β} {g : β -> α} (h : Isometry f) (hg : RightInverse g 
f) : Isometry g
参数：h : Isometry f；hg : RightInverse g f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
The right inverse of an isometry is an isometry.
-/
theorem right_inv {f : α → β} {g : β → α} (h : Isometry f) (hg : RightInverse g f) : Isometry g :=
  fun x y => by rw [← h, hg _, hg _]
/-
**Isometry.preimage_closedEBall** 是 Mathlib 中的一个定理，位于命名空间 `Isometry`。
形式化陈述：preimage_closedEBall (h : Isometry f) (x : α) (r : Real>=0∞) : f ⁻¹' Metri
c.closedEBall (f x) r = Metric.closedEBall x r
参数：h : Isometry f；x : α；r : Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Isometry.edist_eq`：edist_eq (hf : Isometry f) (x y : α) : edist (f x) (f
 y) = edist x y
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem preimage_closedEBall (h : Isometry f) (x : α) (r : ℝ≥0∞) :
    f ⁻¹' Metric.closedEBall (f x) r = Metric.closedEBall x r := by
  ext y
  simp [h.edist_eq]

@[deprecated (since := "2026-01-24")]
alias preimage_emetric_closedBall := preimage_closedEBall
/-
**Isometry.preimage_eball** 是 Mathlib 中的一个定理，位于命名空间 `Isometry`。
形式化陈述：preimage_eball (h : Isometry f) (x : α) (r : Real>=0∞) : f ⁻¹' Metric.ebal
l (f x) r = Metric.eball x r
参数：h : Isometry f；x : α；r : Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Isometry.edist_eq`：edist_eq (hf : Isometry f) (x y : α) : edist (f x) (f
 y) = edist x y
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem preimage_eball (h : Isometry f) (x : α) (r : ℝ≥0∞) :
    f ⁻¹' Metric.eball (f x) r = Metric.eball x r := by
  ext y
  simp [h.edist_eq]

@[deprecated (since := "2026-01-24")]
alias preimage_emetric_ball := preimage_eball

/-- Isometries preserve the diameter in pseudoemetric spaces. -/
/-
**Isometry.ediam_image** 是 Mathlib 中的一个定理，位于命名空间 `Isometry`。
形式化陈述：ediam_image (hf : Isometry f) (s : Set α) : Metric.ediam (f '' s) = Metric
.ediam s
参数：hf : Isometry f；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_forall_ge_iff`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α},
 (∀ (c : α), a ≤ c ↔ b ≤ c) → a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Isometry.edist_eq`：edist_eq (hf : Isometry f) (x y : α) : edist (f x) (f
 y) = edist x y
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Isometries preserve the diameter in pseudoemetric spaces.
-/
theorem ediam_image (hf : Isometry f) (s : Set α) : Metric.ediam (f '' s) = Metric.ediam s :=
  eq_of_forall_ge_iff fun d => by simp only [Metric.ediam_le_iff, forall_mem_image, hf.edist_eq]
/-
**Isometry.ediam_range** 是 Mathlib 中的一个定理，位于命名空间 `Isometry`。
形式化陈述：ediam_range (hf : Isometry f) : Metric.ediam (range f) = Metric.ediam (uni
v : Set α)
参数：hf : Isometry f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Isometry.ediam_image`：ediam_image (hf : Isometry f) (s : Set α) : Metric
.ediam (f '' s) = Metric.ediam s
-/
theorem ediam_range (hf : Isometry f) : Metric.ediam (range f) = Metric.ediam (univ : Set α) := by
  rw [← image_univ]
  exact hf.ediam_image univ
/-
**Isometry.mapsTo_eball** 是 Mathlib 中的一个定理，位于命名空间 `Isometry`。
形式化陈述：mapsTo_eball (hf : Isometry f) (x : α) (r : Real>=0∞) : MapsTo f (Metric.e
ball x r) (Metric.eball (f x) r)
参数：hf : Isometry f；x : α；r : Real>=0∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Isometry.preimage_eball`：preimage_eball (h : Isometry f) (x : α) (r : Re
al>=0∞) : f ⁻¹' Metric.eball (f x) r = Metric.eball x r
-/
theorem mapsTo_eball (hf : Isometry f) (x : α) (r : ℝ≥0∞) :
    MapsTo f (Metric.eball x r) (Metric.eball (f x) r) :=
  (hf.preimage_eball x r).ge

@[deprecated (since := "2026-01-24")]
alias mapsTo_emetric_ball := mapsTo_eball
/-
**Isometry.mapsTo_closedEBall** 是 Mathlib 中的一个定理，位于命名空间 `Isometry`。
形式化陈述：mapsTo_closedEBall (hf : Isometry f) (x : α) (r : Real>=0∞) : MapsTo f (Me
tric.closedEBall x r) (Metric.closedEBall (f x) r)
参数：hf : Isometry f；x : α；r : Real>=0∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Isometry.preimage_closedEBall`：preimage_closedEBall (h : Isometry f) (x 
: α) (r : Real>=0∞) : f ⁻¹' Metric.closedEBall (f x) r = Metric.closedEBall x r
-/
theorem mapsTo_closedEBall (hf : Isometry f) (x : α) (r : ℝ≥0∞) :
    MapsTo f (Metric.closedEBall x r) (Metric.closedEBall (f x) r) :=
  (hf.preimage_closedEBall x r).ge

@[deprecated (since := "2026-01-24")]
alias mapsTo_emetric_closedBall := mapsTo_closedEBall

/-- The injection from a subtype is an isometry -/
/-
**Isometry._root_.isometry_subtype_coe** 是 Mathlib 中的一个定理，位于命名空间 `Isometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The injection from a subtype is an isometry
-/
theorem _root_.isometry_subtype_coe {s : Set α} : Isometry ((↑) : s → α) := fun _ _ => rfl
/-
**Isometry._root_.NNReal.isometry_coe** 是 Mathlib 中的一个定理，位于命名空间 `Isometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.NNReal.isometry_coe : Isometry ((↑) : NNReal → ℝ) := fun _ _ ↦ rfl
/-
**Isometry.comp_continuousOn_iff** 是 Mathlib 中的一个定理，位于命名空间 `Isometry`。
形式化陈述：comp_continuousOn_iff {γ} [TopologicalSpace γ] (hf : Isometry f) {g : γ ->
 α} {s : Set γ} : ContinuousOn (f ∘ g) s ↔ ContinuousOn g s
参数：hf : Isometry f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用引理 `Topology.IsInducing.continuousOn_iff`：Topology.IsInducing.continuousOn_i
ff {f : α -> β} {g : β -> γ} (hg : IsInducing g) {s : Set α} : ContinuousOn f s 
↔ ContinuousOn (g ∘ f) s
· 使用定理 `IsUniformInducing.isInducing`：IsUniformInducing.isInducing {f : α -> β} 
(h : IsUniformInducing f) : IsInducing f
· 使用定理 `Isometry.isUniformInducing`：isUniformInducing (hf : Isometry f) : IsUnif
ormInducing f
-/
theorem comp_continuousOn_iff {γ} [TopologicalSpace γ] (hf : Isometry f) {g : γ → α} {s : Set γ} :
    ContinuousOn (f ∘ g) s ↔ ContinuousOn g s :=
  hf.isUniformInducing.isInducing.continuousOn_iff.symm
/-
**Isometry.comp_continuous_iff** 是 Mathlib 中的一个定理，位于命名空间 `Isometry`。
形式化陈述：comp_continuous_iff {γ} [TopologicalSpace γ] (hf : Isometry f) {g : γ -> α
} : Continuous (f ∘ g) ↔ Continuous g
参数：hf : Isometry f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用引理 `Topology.IsInducing.continuous_iff`：continuous_iff (hg : IsInducing g) :
 Continuous f ↔ Continuous (g ∘ f)
· 使用定理 `IsUniformInducing.isInducing`：IsUniformInducing.isInducing {f : α -> β} 
(h : IsUniformInducing f) : IsInducing f
· 使用定理 `Isometry.isUniformInducing`：isUniformInducing (hf : Isometry f) : IsUnif
ormInducing f
-/
theorem comp_continuous_iff {γ} [TopologicalSpace γ] (hf : Isometry f) {g : γ → α} :
    Continuous (f ∘ g) ↔ Continuous g :=
  hf.isUniformInducing.isInducing.continuous_iff.symm

end PseudoEMetricIsometry

--section
section EMetricIsometry

variable [EMetricSpace α] [PseudoEMetricSpace β] {f : α → β}

/-- An isometry from an emetric space is injective -/
/-
**Isometry.injective** 是 Mathlib 中的一个定理，位于命名空间 `Isometry`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : EMetricSpace α] [inst_1 : PseudoEMetri
cSpace β] {f : α → β},   Isometry f → Function.Injective f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AntilipschitzWith.injective`：∀ {α : Type u_4} {β : Type u_5} [inst : EMe
tricSpace α] [inst_1 : PseudoEMetricSpace β] {K : NNReal} {f : α → β},   Antilip
schitzWith K f → …
· 使用定理 `Isometry.antilipschitz`：antilipschitz (h : Isometry f) : AntilipschitzWi
th 1 f

--- 原说明 ---
An isometry from an emetric space is injective
-/
protected theorem injective (h : Isometry f) : Injective f :=
  h.antilipschitz.injective

/-- An isometry from an emetric space is a uniform embedding -/
/-
**Isometry.isUniformEmbedding** 是 Mathlib 中的一个引理，位于命名空间 `Isometry`。
形式化陈述：isUniformEmbedding (hf : Isometry f) : IsUniformEmbedding f
参数：hf : Isometry f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AntilipschitzWith.isUniformEmbedding`：isUniformEmbedding {α β : Type*} [
EMetricSpace α] [PseudoEMetricSpace β] {K : Real>=0} {f : α -> β} (hf : Antilips
chitzWith K f) (hfc : Unif…
· 使用定理 `Isometry.antilipschitz`：antilipschitz (h : Isometry f) : AntilipschitzWi
th 1 f
· 使用定理 `LipschitzWith.uniformContinuous`：∀ {α : Type u} {β : Type v} [inst : Pse
udoEMetricSpace α] [inst_1 : PseudoEMetricSpace β] {K : NNReal} {f : α → β},   L
ipschitzWith K f → Un…
· 使用定理 `Isometry.lipschitz`：lipschitz (h : Isometry f) : LipschitzWith 1 f

--- 原说明 ---
An isometry from an emetric space is a uniform embedding
-/
lemma isUniformEmbedding (hf : Isometry f) : IsUniformEmbedding f :=
  hf.antilipschitz.isUniformEmbedding hf.lipschitz.uniformContinuous

/-- An isometry from an emetric space is an embedding -/
/-
**Isometry.isEmbedding** 是 Mathlib 中的一个定理，位于命名空间 `Isometry`。
形式化陈述：isEmbedding (hf : Isometry f) : IsEmbedding f
参数：hf : Isometry f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUniformEmbedding.isEmbedding`：∀ {α : Type u} {β : Type v} [inst : Unif
ormSpace α] [inst_1 : UniformSpace β] {f : α → β},   IsUniformEmbedding f → Topo
logy.IsEmbedding f
· 使用引理 `Isometry.isUniformEmbedding`：isUniformEmbedding (hf : Isometry f) : IsUn
iformEmbedding f

--- 原说明 ---
An isometry from an emetric space is an embedding
-/
theorem isEmbedding (hf : Isometry f) : IsEmbedding f := hf.isUniformEmbedding.isEmbedding

/-- An isometry from a complete emetric space is a closed embedding -/
/-
**Isometry.isClosedEmbedding** 是 Mathlib 中的一个定理，位于命名空间 `Isometry`。
形式化陈述：isClosedEmbedding [CompleteSpace α] [EMetricSpace γ] {f : α -> γ} (hf : Is
ometry f) : IsClosedEmbedding f
参数：hf : Isometry f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AntilipschitzWith.isClosedEmbedding`：isClosedEmbedding {α : Type*} {β : 
Type*} [EMetricSpace α] [EMetricSpace β] {K : Real>=0} {f : α -> β} [CompleteSpa
ce α] (hf : Antilipschitz…
· 使用定理 `Isometry.antilipschitz`：antilipschitz (h : Isometry f) : AntilipschitzWi
th 1 f
· 使用定理 `LipschitzWith.uniformContinuous`：∀ {α : Type u} {β : Type v} [inst : Pse
udoEMetricSpace α] [inst_1 : PseudoEMetricSpace β] {K : NNReal} {f : α → β},   L
ipschitzWith K f → Un…
· 使用定理 `Isometry.lipschitz`：lipschitz (h : Isometry f) : LipschitzWith 1 f

--- 原说明 ---
An isometry from a complete emetric space is a closed embedding
-/
theorem isClosedEmbedding [CompleteSpace α] [EMetricSpace γ] {f : α → γ} (hf : Isometry f) :
    IsClosedEmbedding f :=
  hf.antilipschitz.isClosedEmbedding hf.lipschitz.uniformContinuous

end EMetricIsometry

--section
section PseudoMetricIsometry

variable [PseudoMetricSpace α] [PseudoMetricSpace β] {f : α → β}

/-- An isometry preserves the diameter in pseudometric spaces. -/
/-
**Isometry.diam_image** 是 Mathlib 中的一个定理，位于命名空间 `Isometry`。
形式化陈述：diam_image (hf : Isometry f) (s : Set α) : Metric.diam (f '' s) = Metric.d
iam s
参数：hf : Isometry f；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.diam.eq_1`：∀ {α : Type u} [inst : PseudoMetricSpace α] (s : Set α
), Metric.diam s = (Metric.ediam s).toReal
· 使用定理 `Isometry.ediam_image`：ediam_image (hf : Isometry f) (s : Set α) : Metric
.ediam (f '' s) = Metric.ediam s

--- 原说明 ---
An isometry preserves the diameter in pseudometric spaces.
-/
theorem diam_image (hf : Isometry f) (s : Set α) : Metric.diam (f '' s) = Metric.diam s := by
  rw [Metric.diam, Metric.diam, hf.ediam_image]
/-
**Isometry.diam_range** 是 Mathlib 中的一个定理，位于命名空间 `Isometry`。
形式化陈述：diam_range (hf : Isometry f) : Metric.diam (range f) = Metric.diam (univ :
 Set α)
参数：hf : Isometry f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Isometry.diam_image`：diam_image (hf : Isometry f) (s : Set α) : Metric.d
iam (f '' s) = Metric.diam s
-/
theorem diam_range (hf : Isometry f) : Metric.diam (range f) = Metric.diam (univ : Set α) := by
  rw [← image_univ]
  exact hf.diam_image univ
/-
**Isometry.preimage_setOfPred_dist** 是 Mathlib 中的一个定理，位于命名空间 `Isometry`。
形式化陈述：preimage_setOfPred_dist (hf : Isometry f) (x : α) (p : Real -> Prop) : f ⁻
¹' { y | p (dist y (f x)) } = { y | p (dist y x) }
参数：hf : Isometry f；x : α；p : Real -> Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Isometry.dist_eq`：∀ {α : Type u} {β : Type v} [inst : PseudoMetricSpace 
α] [inst_1 : PseudoMetricSpace β] {f : α → β},   Isometry f → ∀ (x y : α), dist 
(f x) …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem preimage_setOfPred_dist (hf : Isometry f) (x : α) (p : ℝ → Prop) :
    f ⁻¹' { y | p (dist y (f x)) } = { y | p (dist y x) } := by
  simp [hf.dist_eq]

@[deprecated (since := "2026-07-09")] alias preimage_setOf_dist := preimage_setOfPred_dist
/-
**Isometry.preimage_closedBall** 是 Mathlib 中的一个定理，位于命名空间 `Isometry`。
形式化陈述：preimage_closedBall (hf : Isometry f) (x : α) (r : Real) : f ⁻¹' Metric.cl
osedBall (f x) r = Metric.closedBall x r
参数：hf : Isometry f；x : α；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.preimage_setOfPred_dist`：preimage_setOfPred_dist (hf : Isometry
 f) (x : α) (p : Real -> Prop) : f ⁻¹' { y | p (dist y (f x)) } = { y | p (dist 
y x) }
-/
theorem preimage_closedBall (hf : Isometry f) (x : α) (r : ℝ) :
    f ⁻¹' Metric.closedBall (f x) r = Metric.closedBall x r :=
  hf.preimage_setOfPred_dist x (· ≤ r)
/-
**Isometry.preimage_ball** 是 Mathlib 中的一个定理，位于命名空间 `Isometry`。
形式化陈述：preimage_ball (hf : Isometry f) (x : α) (r : Real) : f ⁻¹' Metric.ball (f 
x) r = Metric.ball x r
参数：hf : Isometry f；x : α；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.preimage_setOfPred_dist`：preimage_setOfPred_dist (hf : Isometry
 f) (x : α) (p : Real -> Prop) : f ⁻¹' { y | p (dist y (f x)) } = { y | p (dist 
y x) }
-/
theorem preimage_ball (hf : Isometry f) (x : α) (r : ℝ) :
    f ⁻¹' Metric.ball (f x) r = Metric.ball x r :=
  hf.preimage_setOfPred_dist x (· < r)
/-
**Isometry.preimage_sphere** 是 Mathlib 中的一个定理，位于命名空间 `Isometry`。
形式化陈述：preimage_sphere (hf : Isometry f) (x : α) (r : Real) : f ⁻¹' Metric.sphere
 (f x) r = Metric.sphere x r
参数：hf : Isometry f；x : α；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.preimage_setOfPred_dist`：preimage_setOfPred_dist (hf : Isometry
 f) (x : α) (p : Real -> Prop) : f ⁻¹' { y | p (dist y (f x)) } = { y | p (dist 
y x) }
-/
theorem preimage_sphere (hf : Isometry f) (x : α) (r : ℝ) :
    f ⁻¹' Metric.sphere (f x) r = Metric.sphere x r :=
  hf.preimage_setOfPred_dist x (· = r)
/-
**Isometry.mapsTo_ball** 是 Mathlib 中的一个定理，位于命名空间 `Isometry`。
形式化陈述：mapsTo_ball (hf : Isometry f) (x : α) (r : Real) : MapsTo f (Metric.ball x
 r) (Metric.ball (f x) r)
参数：hf : Isometry f；x : α；r : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Isometry.preimage_ball`：preimage_ball (hf : Isometry f) (x : α) (r : Rea
l) : f ⁻¹' Metric.ball (f x) r = Metric.ball x r
-/
theorem mapsTo_ball (hf : Isometry f) (x : α) (r : ℝ) :
    MapsTo f (Metric.ball x r) (Metric.ball (f x) r) :=
  (hf.preimage_ball x r).ge
/-
**Isometry.mapsTo_sphere** 是 Mathlib 中的一个定理，位于命名空间 `Isometry`。
形式化陈述：mapsTo_sphere (hf : Isometry f) (x : α) (r : Real) : MapsTo f (Metric.sphe
re x r) (Metric.sphere (f x) r)
参数：hf : Isometry f；x : α；r : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Isometry.preimage_sphere`：preimage_sphere (hf : Isometry f) (x : α) (r :
 Real) : f ⁻¹' Metric.sphere (f x) r = Metric.sphere x r
-/
theorem mapsTo_sphere (hf : Isometry f) (x : α) (r : ℝ) :
    MapsTo f (Metric.sphere x r) (Metric.sphere (f x) r) :=
  (hf.preimage_sphere x r).ge
/-
**Isometry.mapsTo_closedBall** 是 Mathlib 中的一个定理，位于命名空间 `Isometry`。
形式化陈述：mapsTo_closedBall (hf : Isometry f) (x : α) (r : Real) : MapsTo f (Metric.
closedBall x r) (Metric.closedBall (f x) r)
参数：hf : Isometry f；x : α；r : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Isometry.preimage_closedBall`：preimage_closedBall (hf : Isometry f) (x :
 α) (r : Real) : f ⁻¹' Metric.closedBall (f x) r = Metric.closedBall x r
-/
theorem mapsTo_closedBall (hf : Isometry f) (x : α) (r : ℝ) :
    MapsTo f (Metric.closedBall x r) (Metric.closedBall (f x) r) :=
  (hf.preimage_closedBall x r).ge

end PseudoMetricIsometry

-- section
end Isometry

-- namespace
/-- A uniform embedding from a uniform space to a metric space is an isometry with respect to the
induced metric space structure on the source space. -/
/-
**IsUniformEmbedding.to_isometry** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsUniformEmbedding.to_isometry {α β} [UniformSpace α] [MetricSpace β] {f :
 α -> β} (h : IsUniformEmbedding f) : (letI
参数：h : IsUniformEmbedding f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.of_dist_eq`：∀ {α : Type u} {β : Type v} [inst : PseudoMetricSpa
ce α] [inst_1 : PseudoMetricSpace β] {f : α → β},   (∀ (x y : α), dist (f x) (f 
y) = dist…

--- 原说明 ---
A uniform embedding from a uniform space to a metric space is an isometry with r
espect to the
induced metric space structure on the source space.
-/
theorem IsUniformEmbedding.to_isometry {α β} [UniformSpace α] [MetricSpace β] {f : α → β}
    (h : IsUniformEmbedding f) : (letI := h.comapMetricSpace f; Isometry f) :=
  let _ := h.comapMetricSpace f
  Isometry.of_dist_eq fun _ _ => rfl

/-- An embedding from a topological space to a pseudometric space is an isometry with respect to the
induced pseudometric space structure on the source space. -/
/-
**Topology.IsEmbedding.to_isometry** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Topology.IsEmbedding.to_isometry {α β} [TopologicalSpace α] [PseudoMetricS
pace β] {f : α -> β} (h : IsEmbedding f) : (letI
参数：h : IsEmbedding f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.toIsInducing`：∀ {X : Type u_1} {Y : Type u_2} [tX :
 TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbeddi
ng f → Topology.IsInduc…
· 使用定理 `Isometry.of_dist_eq`：∀ {α : Type u} {β : Type v} [inst : PseudoMetricSpa
ce α] [inst_1 : PseudoMetricSpace β] {f : α → β},   (∀ (x y : α), dist (f x) (f 
y) = dist…

--- 原说明 ---
An embedding from a topological space to a pseudometric space is an isometry wit
h respect to the
induced pseudometric space structure on the source space.
-/
theorem Topology.IsEmbedding.to_isometry {α β} [TopologicalSpace α] [PseudoMetricSpace β]
    {f : α → β} (h : IsEmbedding f) : (letI := h.comapPseudoMetricSpace; Isometry f) :=
  let _ := h.comapPseudoMetricSpace
  Isometry.of_dist_eq fun _ _ => rfl
/-
**PseudoEMetricSpace.isometry_induced** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：PseudoEMetricSpace.isometry_induced (f : α -> β) [m : PseudoEMetricSpace β
] : letI
参数：f : α -> β。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem PseudoEMetricSpace.isometry_induced (f : α → β) [m : PseudoEMetricSpace β] :
    letI := m.induced f; Isometry f := fun _ _ ↦ rfl
/-
**PseudoMetricSpace.isometry_induced** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：PseudoMetricSpace.isometry_induced (f : α -> β) [m : PseudoMetricSpace β] 
: letI
参数：f : α -> β。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem PseudoMetricSpace.isometry_induced (f : α → β) [m : PseudoMetricSpace β] :
    letI := m.induced f; Isometry f := fun _ _ ↦ rfl
/-
**EMetricSpace.isometry_induced** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：EMetricSpace.isometry_induced (f : α -> β) (hf : f.Injective) [m : EMetric
Space β] : letI
参数：f : α -> β；hf : f.Injective。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem EMetricSpace.isometry_induced (f : α → β) (hf : f.Injective) [m : EMetricSpace β] :
    letI := m.induced f hf; Isometry f := fun _ _ ↦ rfl
/-
**MetricSpace.isometry_induced** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MetricSpace.isometry_induced (f : α -> β) (hf : f.Injective) [m : MetricSp
ace β] : letI
参数：f : α -> β；hf : f.Injective。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem MetricSpace.isometry_induced (f : α → β) (hf : f.Injective) [m : MetricSpace β] :
    letI := m.induced f hf; Isometry f := fun _ _ ↦ rfl

/-- `IsometryClass F α β` states that `F` is a type of isometries. -/
/-
**IsometryClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_3) →   (α : outParam (Type u_4)) →     (β : outParam (Type u_5
)) → [PseudoEMetricSpace α] → [PseudoEMetricSpace β] → [FunLike F α β] → Prop
参数：Type u_4；Type u_5。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`IsometryClass F α β` states that `F` is a type of isometries.
-/
class IsometryClass (F : Type*) (α β : outParam Type*)
    [PseudoEMetricSpace α] [PseudoEMetricSpace β] [FunLike F α β] : Prop where
  protected isometry (f : F) : Isometry f

namespace IsometryClass

section PseudoEMetricSpace
variable [PseudoEMetricSpace α] [PseudoEMetricSpace β]

section
variable [FunLike F α β] [IsometryClass F α β] (f : F)

/-
**IsometryClass.edist_eq** 是 Mathlib 中的一个定理，位于命名空间 `IsometryClass`。
形式化陈述：∀ {F : Type u_1} {α : Type u} {β : Type v} [inst : PseudoEMetricSpace α] [
inst_1 : PseudoEMetricSpace β]   [inst_2 : FunLike F α β] [IsometryClass F α β] 
(f : F) (x y : α), edist (f x) (f y) = edist x y
参数：f : F；x y : α；f x；f y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.edist_eq`：edist_eq (hf : Isometry f) (x y : α) : edist (f x) (f
 y) = edist x y
· 使用定理 `IsometryClass.isometry`：∀ {F : Type u_3} {α : outParam (Type u_4)} {β : 
outParam (Type u_5)} {inst : PseudoEMetricSpace α}   {inst_1 : PseudoEMetricSpac
e β} {inst_2…
-/
protected theorem edist_eq (x y : α) : edist (f x) (f y) = edist x y :=
  (IsometryClass.isometry f).edist_eq x y
/-
**IsometryClass.continuous** 是 Mathlib 中的一个定理，位于命名空间 `IsometryClass`。
形式化陈述：∀ {F : Type u_1} {α : Type u} {β : Type v} [inst : PseudoEMetricSpace α] [
inst_1 : PseudoEMetricSpace β]   [inst_2 : FunLike F α β] [IsometryClass F α β] 
(f : F), Continuous ⇑f
参数：f : F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.continuous`：∀ {α : Type u} {β : Type v} [inst : PseudoEMetricSp
ace α] [inst_1 : PseudoEMetricSpace β] {f : α → β},   Isometry f → Continuous f
· 使用定理 `IsometryClass.isometry`：∀ {F : Type u_3} {α : outParam (Type u_4)} {β : 
outParam (Type u_5)} {inst : PseudoEMetricSpace α}   {inst_1 : PseudoEMetricSpac
e β} {inst_2…
-/
protected theorem continuous : Continuous f :=
  (IsometryClass.isometry f).continuous
/-
**IsometryClass.lipschitz** 是 Mathlib 中的一个定理，位于命名空间 `IsometryClass`。
形式化陈述：∀ {F : Type u_1} {α : Type u} {β : Type v} [inst : PseudoEMetricSpace α] [
inst_1 : PseudoEMetricSpace β]   [inst_2 : FunLike F α β] [IsometryClass F α β] 
(f : F), LipschitzWith 1 ⇑f
参数：f : F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.lipschitz`：lipschitz (h : Isometry f) : LipschitzWith 1 f
· 使用定理 `IsometryClass.isometry`：∀ {F : Type u_3} {α : outParam (Type u_4)} {β : 
outParam (Type u_5)} {inst : PseudoEMetricSpace α}   {inst_1 : PseudoEMetricSpac
e β} {inst_2…
-/
protected theorem lipschitz : LipschitzWith 1 f :=
  (IsometryClass.isometry f).lipschitz
/-
**IsometryClass.antilipschitz** 是 Mathlib 中的一个定理，位于命名空间 `IsometryClass`。
形式化陈述：∀ {F : Type u_1} {α : Type u} {β : Type v} [inst : PseudoEMetricSpace α] [
inst_1 : PseudoEMetricSpace β]   [inst_2 : FunLike F α β] [IsometryClass F α β] 
(f : F), AntilipschitzWith 1 ⇑f
参数：f : F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.antilipschitz`：antilipschitz (h : Isometry f) : AntilipschitzWi
th 1 f
· 使用定理 `IsometryClass.isometry`：∀ {F : Type u_3} {α : outParam (Type u_4)} {β : 
outParam (Type u_5)} {inst : PseudoEMetricSpace α}   {inst_1 : PseudoEMetricSpac
e β} {inst_2…
-/
protected theorem antilipschitz : AntilipschitzWith 1 f :=
  (IsometryClass.isometry f).antilipschitz
/-
**IsometryClass.ediam_image** 是 Mathlib 中的一个定理，位于命名空间 `IsometryClass`。
形式化陈述：ediam_image (s : Set α) : Metric.ediam (f '' s) = Metric.ediam s
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.ediam_image`：ediam_image (hf : Isometry f) (s : Set α) : Metric
.ediam (f '' s) = Metric.ediam s
· 使用定理 `IsometryClass.isometry`：∀ {F : Type u_3} {α : outParam (Type u_4)} {β : 
outParam (Type u_5)} {inst : PseudoEMetricSpace α}   {inst_1 : PseudoEMetricSpac
e β} {inst_2…
-/
theorem ediam_image (s : Set α) : Metric.ediam (f '' s) = Metric.ediam s :=
  (IsometryClass.isometry f).ediam_image s
/-
**IsometryClass.ediam_range** 是 Mathlib 中的一个定理，位于命名空间 `IsometryClass`。
形式化陈述：ediam_range : Metric.ediam (range f) = Metric.ediam (univ : Set α)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.ediam_range`：ediam_range (hf : Isometry f) : Metric.ediam (rang
e f) = Metric.ediam (univ : Set α)
· 使用定理 `IsometryClass.isometry`：∀ {F : Type u_3} {α : outParam (Type u_4)} {β : 
outParam (Type u_5)} {inst : PseudoEMetricSpace α}   {inst_1 : PseudoEMetricSpac
e β} {inst_2…
-/
theorem ediam_range : Metric.ediam (range f) = Metric.ediam (univ : Set α) :=
  (IsometryClass.isometry f).ediam_range
/-
**IsometryClass.toContinuousMapClass** 是 Mathlib 中的一个实例，位于命名空间 `IsometryClass`。
形式化陈述：toContinuousMapClass : ContinuousMapClass F α β where map_continuous
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsometryClass.continuous`：∀ {F : Type u_1} {α : Type u} {β : Type v} [in
st : PseudoEMetricSpace α] [inst_1 : PseudoEMetricSpace β]   [inst_2 : FunLike F
 α β] [Isometr…
-/
instance toContinuousMapClass : ContinuousMapClass F α β where
  map_continuous := IsometryClass.continuous

end

/-
**IsometryClass.toHomeomorphClass** 是 Mathlib 中的一个实例，位于命名空间 `IsometryClass`。
形式化陈述：toHomeomorphClass [EquivLike F α β] [IsometryClass F α β] : HomeomorphClas
s F α β where map_continuous
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsometryClass.continuous`：∀ {F : Type u_1} {α : Type u} {β : Type v} [in
st : PseudoEMetricSpace α] [inst_1 : PseudoEMetricSpace β]   [inst_2 : FunLike F
 α β] [Isometr…
· 使用定理 `Isometry.continuous`：∀ {α : Type u} {β : Type v} [inst : PseudoEMetricSp
ace α] [inst_1 : PseudoEMetricSpace β] {f : α → β},   Isometry f → Continuous f
· 使用定理 `Isometry.right_inv`：right_inv {f : α -> β} {g : β -> α} (h : Isometry f)
 (hg : RightInverse g f) : Isometry g
· 使用定理 `IsometryClass.isometry`：∀ {F : Type u_3} {α : outParam (Type u_4)} {β : 
outParam (Type u_5)} {inst : PseudoEMetricSpace α}   {inst_1 : PseudoEMetricSpac
e β} {inst_2…
· 使用定理 `EquivLike.right_inv`：∀ {E : Sort u_1} {α : outParam (Sort u_2)} {β : out
Param (Sort u_3)} [self : EquivLike E α β] (e : E),   Function.RightInverse (Equ
ivLike.in…
-/
instance toHomeomorphClass [EquivLike F α β] [IsometryClass F α β] : HomeomorphClass F α β where
  map_continuous := IsometryClass.continuous
  inv_continuous f := ((IsometryClass.isometry f).right_inv (EquivLike.right_inv f)).continuous

end PseudoEMetricSpace

section PseudoMetricSpace
variable [PseudoMetricSpace α] [PseudoMetricSpace β] [FunLike F α β] [IsometryClass F α β] (f : F)

/-
**IsometryClass.dist_eq** 是 Mathlib 中的一个定理，位于命名空间 `IsometryClass`。
形式化陈述：∀ {F : Type u_1} {α : Type u} {β : Type v} [inst : PseudoMetricSpace α] [i
nst_1 : PseudoMetricSpace β]   [inst_2 : FunLike F α β] [IsometryClass F α β] (f
 : F) (x y : α), dist (f x) (f y) = dist x y
参数：f : F；x y : α；f x；f y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.dist_eq`：∀ {α : Type u} {β : Type v} [inst : PseudoMetricSpace 
α] [inst_1 : PseudoMetricSpace β] {f : α → β},   Isometry f → ∀ (x y : α), dist 
(f x) …
· 使用定理 `IsometryClass.isometry`：∀ {F : Type u_3} {α : outParam (Type u_4)} {β : 
outParam (Type u_5)} {inst : PseudoEMetricSpace α}   {inst_1 : PseudoEMetricSpac
e β} {inst_2…
-/
protected theorem dist_eq (x y : α) : dist (f x) (f y) = dist x y :=
  (IsometryClass.isometry f).dist_eq x y
/-
**IsometryClass.nndist_eq** 是 Mathlib 中的一个定理，位于命名空间 `IsometryClass`。
形式化陈述：∀ {F : Type u_1} {α : Type u} {β : Type v} [inst : PseudoMetricSpace α] [i
nst_1 : PseudoMetricSpace β]   [inst_2 : FunLike F α β] [IsometryClass F α β] (f
 : F) (x y : α), nndist (f x) (f y) = nndist x y
参数：f : F；x y : α；f x；f y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.nndist_eq`：∀ {α : Type u} {β : Type v} [inst : PseudoMetricSpac
e α] [inst_1 : PseudoMetricSpace β] {f : α → β},   Isometry f → ∀ (x y : α), nnd
ist (f x…
· 使用定理 `IsometryClass.isometry`：∀ {F : Type u_3} {α : outParam (Type u_4)} {β : 
outParam (Type u_5)} {inst : PseudoEMetricSpace α}   {inst_1 : PseudoEMetricSpac
e β} {inst_2…
-/
protected theorem nndist_eq (x y : α) : nndist (f x) (f y) = nndist x y :=
  (IsometryClass.isometry f).nndist_eq x y
/-
**IsometryClass.diam_image** 是 Mathlib 中的一个定理，位于命名空间 `IsometryClass`。
形式化陈述：diam_image (s : Set α) : Metric.diam (f '' s) = Metric.diam s
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.diam_image`：diam_image (hf : Isometry f) (s : Set α) : Metric.d
iam (f '' s) = Metric.diam s
· 使用定理 `IsometryClass.isometry`：∀ {F : Type u_3} {α : outParam (Type u_4)} {β : 
outParam (Type u_5)} {inst : PseudoEMetricSpace α}   {inst_1 : PseudoEMetricSpac
e β} {inst_2…
-/
theorem diam_image (s : Set α) : Metric.diam (f '' s) = Metric.diam s :=
  (IsometryClass.isometry f).diam_image s
/-
**IsometryClass.diam_range** 是 Mathlib 中的一个定理，位于命名空间 `IsometryClass`。
形式化陈述：diam_range : Metric.diam (range f) = Metric.diam (univ : Set α)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.diam_range`：diam_range (hf : Isometry f) : Metric.diam (range f
) = Metric.diam (univ : Set α)
· 使用定理 `IsometryClass.isometry`：∀ {F : Type u_3} {α : outParam (Type u_4)} {β : 
outParam (Type u_5)} {inst : PseudoEMetricSpace α}   {inst_1 : PseudoEMetricSpac
e β} {inst_2…
-/
theorem diam_range : Metric.diam (range f) = Metric.diam (univ : Set α) :=
  (IsometryClass.isometry f).diam_range

end PseudoMetricSpace

end IsometryClass

-- such a bijection need not exist
/-- `α` and `β` are isometric if there is an isometric bijection between them. -/
/-
**IsometryEquiv** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u) → (β : Type v) → [PseudoEMetricSpace α] → [PseudoEMetricSpace
 β] → Type (max u v)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`α` and `β` are isometric if there is an isometric bijection between them.
-/
structure IsometryEquiv (α : Type u) (β : Type v) [PseudoEMetricSpace α] [PseudoEMetricSpace β]
    extends α ≃ β where
  isometry_toFun : Isometry toFun

@[inherit_doc]
infixl:25 " ≃ᵢ " => IsometryEquiv

namespace IsometryEquiv

section PseudoEMetricSpace

variable [PseudoEMetricSpace α] [PseudoEMetricSpace β] [PseudoEMetricSpace γ]

/-
**IsometryEquiv.toEquiv_injective** 是 Mathlib 中的一个定理，位于命名空间 `IsometryEquiv`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : PseudoEMetricSpace α] [inst_1 : Pseudo
EMetricSpace β],   Function.Injective IsometryEquiv.toEquiv
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toEquiv_injective : Injective (toEquiv : (α ≃ᵢ β) → (α ≃ β))
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl
/-
**IsometryEquiv.toEquiv_inj** 是 Mathlib 中的一个定理，位于命名空间 `IsometryEquiv`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : PseudoEMetricSpace α] [inst_1 : Pseudo
EMetricSpace β] {e₁ e₂ : α ≃ᵢ β},   e₁.toEquiv = e₂.toEquiv ↔ e₁ = e₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `IsometryEquiv.toEquiv_injective`：∀ {α : Type u} {β : Type v} [inst : Pse
udoEMetricSpace α] [inst_1 : PseudoEMetricSpace β],   Function.Injective Isometr
yEquiv.toEquiv
-/
@[simp] theorem toEquiv_inj {e₁ e₂ : α ≃ᵢ β} : e₁.toEquiv = e₂.toEquiv ↔ e₁ = e₂ :=
  toEquiv_injective.eq_iff
/-
**IsometryEquiv.** 是 Mathlib 中的一个实例，位于命名空间 `IsometryEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : EquivLike (α ≃ᵢ β) α β where
  coe e := e.toEquiv
  inv e := e.toEquiv.symm
  left_inv e := e.left_inv
  right_inv e := e.right_inv
  coe_injective' _ _ h _ := toEquiv_injective <| DFunLike.ext' h
/-
**IsometryEquiv.** 是 Mathlib 中的一个实例，位于命名空间 `IsometryEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsometryClass (IsometryEquiv α β) α β where
  isometry := isometry_toFun
/-
**IsometryEquiv.coe_eq_toEquiv** 是 Mathlib 中的一个定理，位于命名空间 `IsometryEquiv`。
形式化陈述：coe_eq_toEquiv (h : α ≃ᵢ β) (a : α) : h a = h.toEquiv a
参数：h : α ≃ᵢ β；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_eq_toEquiv (h : α ≃ᵢ β) (a : α) : h a = h.toEquiv a := rfl
/-
**IsometryEquiv.coe_toEquiv** 是 Mathlib 中的一个定理，位于命名空间 `IsometryEquiv`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : PseudoEMetricSpace α] [inst_1 : Pseudo
EMetricSpace β] (h : α ≃ᵢ β), ⇑h.toEquiv = ⇑h
参数：h : α ≃ᵢ β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem coe_toEquiv (h : α ≃ᵢ β) : ⇑h.toEquiv = h := rfl
/-
**IsometryEquiv.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `IsometryEquiv`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : PseudoEMetricSpace α] [inst_1 : Pseudo
EMetricSpace β] (e : α ≃ β)   (h : Isometry e.toFun), ⇑{ toEquiv := e, isometry_
toFun := h } = ⇑e
参数：e : α ≃ β；h : Isometry e.toFun。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem coe_mk (e : α ≃ β) (h) : ⇑(mk e h) = e := rfl
/-
**IsometryEquiv.isometry** 是 Mathlib 中的一个定理，位于命名空间 `IsometryEquiv`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : PseudoEMetricSpace α] [inst_1 : Pseudo
EMetricSpace β] (h : α ≃ᵢ β), Isometry ⇑h
参数：h : α ≃ᵢ β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsometryEquiv.isometry_toFun`：∀ {α : Type u} {β : Type v} [inst : Pseudo
EMetricSpace α] [inst_1 : PseudoEMetricSpace β] (self : α ≃ᵢ β),   Isometry self
.toFun
-/
protected theorem isometry (h : α ≃ᵢ β) : Isometry h :=
  h.isometry_toFun
/-
**IsometryEquiv.bijective** 是 Mathlib 中的一个定理，位于命名空间 `IsometryEquiv`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : PseudoEMetricSpace α] [inst_1 : Pseudo
EMetricSpace β] (h : α ≃ᵢ β),   Function.Bijective ⇑h
参数：h : α ≃ᵢ β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.bijective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijec
tive ⇑e
-/
protected theorem bijective (h : α ≃ᵢ β) : Bijective h :=
  h.toEquiv.bijective
/-
**IsometryEquiv.injective** 是 Mathlib 中的一个定理，位于命名空间 `IsometryEquiv`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : PseudoEMetricSpace α] [inst_1 : Pseudo
EMetricSpace β] (h : α ≃ᵢ β),   Function.Injective ⇑h
参数：h : α ≃ᵢ β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
-/
protected theorem injective (h : α ≃ᵢ β) : Injective h :=
  h.toEquiv.injective
/-
**IsometryEquiv.surjective** 是 Mathlib 中的一个定理，位于命名空间 `IsometryEquiv`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : PseudoEMetricSpace α] [inst_1 : Pseudo
EMetricSpace β] (h : α ≃ᵢ β),   Function.Surjective ⇑h
参数：h : α ≃ᵢ β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
-/
protected theorem surjective (h : α ≃ᵢ β) : Surjective h :=
  h.toEquiv.surjective
/-
**IsometryEquiv.edist_eq** 是 Mathlib 中的一个定理，位于命名空间 `IsometryEquiv`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : PseudoEMetricSpace α] [inst_1 : Pseudo
EMetricSpace β] (h : α ≃ᵢ β) (x y : α),   edist (h x) (h y) = edist x y
参数：h : α ≃ᵢ β；x y : α；h x；h y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.edist_eq`：edist_eq (hf : Isometry f) (x y : α) : edist (f x) (f
 y) = edist x y
· 使用定理 `IsometryEquiv.isometry`：∀ {α : Type u} {β : Type v} [inst : PseudoEMetri
cSpace α] [inst_1 : PseudoEMetricSpace β] (h : α ≃ᵢ β), Isometry ⇑h
-/
protected theorem edist_eq (h : α ≃ᵢ β) (x y : α) : edist (h x) (h y) = edist x y :=
  h.isometry.edist_eq x y
/-
**IsometryEquiv.dist_eq** 是 Mathlib 中的一个定理，位于命名空间 `IsometryEquiv`。
形式化陈述：∀ {α : Type u_3} {β : Type u_4} [inst : PseudoMetricSpace α] [inst_1 : Pse
udoMetricSpace β] (h : α ≃ᵢ β) (x y : α),   dist (h x) (h y) = dist x y
参数：h : α ≃ᵢ β；x y : α；h x；h y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.dist_eq`：∀ {α : Type u} {β : Type v} [inst : PseudoMetricSpace 
α] [inst_1 : PseudoMetricSpace β] {f : α → β},   Isometry f → ∀ (x y : α), dist 
(f x) …
· 使用定理 `IsometryEquiv.isometry`：∀ {α : Type u} {β : Type v} [inst : PseudoEMetri
cSpace α] [inst_1 : PseudoEMetricSpace β] (h : α ≃ᵢ β), Isometry ⇑h
-/
protected theorem dist_eq {α β : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β] (h : α ≃ᵢ β)
    (x y : α) : dist (h x) (h y) = dist x y :=
  h.isometry.dist_eq x y
/-
**IsometryEquiv.nndist_eq** 是 Mathlib 中的一个定理，位于命名空间 `IsometryEquiv`。
形式化陈述：∀ {α : Type u_3} {β : Type u_4} [inst : PseudoMetricSpace α] [inst_1 : Pse
udoMetricSpace β] (h : α ≃ᵢ β) (x y : α),   nndist (h x) (h y) = nndist x y
参数：h : α ≃ᵢ β；x y : α；h x；h y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.nndist_eq`：∀ {α : Type u} {β : Type v} [inst : PseudoMetricSpac
e α] [inst_1 : PseudoMetricSpace β] {f : α → β},   Isometry f → ∀ (x y : α), nnd
ist (f x…
· 使用定理 `IsometryEquiv.isometry`：∀ {α : Type u} {β : Type v} [inst : PseudoEMetri
cSpace α] [inst_1 : PseudoEMetricSpace β] (h : α ≃ᵢ β), Isometry ⇑h
-/
protected theorem nndist_eq {α β : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β] (h : α ≃ᵢ β)
    (x y : α) : nndist (h x) (h y) = nndist x y :=
  h.isometry.nndist_eq x y
/-
**IsometryEquiv.continuous** 是 Mathlib 中的一个定理，位于命名空间 `IsometryEquiv`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : PseudoEMetricSpace α] [inst_1 : Pseudo
EMetricSpace β] (h : α ≃ᵢ β), Continuous ⇑h
参数：h : α ≃ᵢ β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.continuous`：∀ {α : Type u} {β : Type v} [inst : PseudoEMetricSp
ace α] [inst_1 : PseudoEMetricSpace β] {f : α → β},   Isometry f → Continuous f
· 使用定理 `IsometryEquiv.isometry`：∀ {α : Type u} {β : Type v} [inst : PseudoEMetri
cSpace α] [inst_1 : PseudoEMetricSpace β] (h : α ≃ᵢ β), Isometry ⇑h
-/
protected theorem continuous (h : α ≃ᵢ β) : Continuous h :=
  h.isometry.continuous

@[simp]
/-
**IsometryEquiv.ediam_image** 是 Mathlib 中的一个定理，位于命名空间 `IsometryEquiv`。
形式化陈述：ediam_image (h : α ≃ᵢ β) (s : Set α) : Metric.ediam (h '' s) = Metric.edia
m s
参数：h : α ≃ᵢ β；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.ediam_image`：ediam_image (hf : Isometry f) (s : Set α) : Metric
.ediam (f '' s) = Metric.ediam s
· 使用定理 `IsometryEquiv.isometry`：∀ {α : Type u} {β : Type v} [inst : PseudoEMetri
cSpace α] [inst_1 : PseudoEMetricSpace β] (h : α ≃ᵢ β), Isometry ⇑h
-/
theorem ediam_image (h : α ≃ᵢ β) (s : Set α) : Metric.ediam (h '' s) = Metric.ediam s :=
  h.isometry.ediam_image s

@[ext]
/-
**IsometryEquiv.ext** 是 Mathlib 中的一个定理，位于命名空间 `IsometryEquiv`。
形式化陈述：ext ⦃h₁ h₂ : α ≃ᵢ β⦄ (H : forall x, h₁ x = h₂ x) : h₁ = h₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext ⦃h₁ h₂ : α ≃ᵢ β⦄ (H : ∀ x, h₁ x = h₂ x) : h₁ = h₂ :=
  DFunLike.ext _ _ H

/-- Alternative constructor for isometric bijections,
taking as input an isometry, and a right inverse. -/
/-
**IsometryEquiv.mk'** 是 Mathlib 中的一个定义，位于命名空间 `IsometryEquiv`。
形式化陈述：mk' {α : Type u} [EMetricSpace α] (f : α -> β) (g : β -> α) (hfg : forall 
x, f (g x) = x) (hf : Isometry f) : α ≃ᵢ β where toFun
参数：f : α -> β；g : β -> α；hfg : forall x, f (g x) = x；hf : Isometry f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Alternative constructor for isometric bijections,
taking as input an isometry, and a right inverse.
-/
def mk' {α : Type u} [EMetricSpace α] (f : α → β) (g : β → α) (hfg : ∀ x, f (g x) = x)
    (hf : Isometry f) : α ≃ᵢ β where
  toFun := f
  invFun := g
  left_inv _ := hf.injective <| hfg _
  right_inv := hfg
  isometry_toFun := hf

/-- The identity isometry of a space. -/
/-
**IsometryEquiv.refl** 是 Mathlib 中的一个定义，位于命名空间 `IsometryEquiv`。
形式化陈述：(α : Type u_3) → [inst : PseudoEMetricSpace α] → α ≃ᵢ α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `isometry_id`：∀ {α : Type u} [inst : PseudoEMetricSpace α], Isometry id

--- 原说明 ---
The identity isometry of a space.
-/
protected def refl (α : Type*) [PseudoEMetricSpace α] : α ≃ᵢ α :=
  { Equiv.refl α with isometry_toFun := isometry_id }

/-- The composition of two isometric isomorphisms, as an isometric isomorphism. -/
/-
**IsometryEquiv.trans** 是 Mathlib 中的一个定义，位于命名空间 `IsometryEquiv`。
形式化陈述：{α : Type u} →   {β : Type v} →     {γ : Type w} →       [inst : PseudoEMe
tricSpace α] →         [inst_1 : PseudoEMetricSpace β] → [inst_2 : PseudoEMetric
Space γ] → α ≃ᵢ β → β ≃ᵢ γ → α ≃ᵢ γ
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
The composition of two isometric isomorphisms, as an isometric isomorphism.
-/
protected def trans (h₁ : α ≃ᵢ β) (h₂ : β ≃ᵢ γ) : α ≃ᵢ γ :=
  { Equiv.trans h₁.toEquiv h₂.toEquiv with
    isometry_toFun := h₂.isometry_toFun.comp h₁.isometry_toFun }

@[simp]
/-
**IsometryEquiv.trans_apply** 是 Mathlib 中的一个定理，位于命名空间 `IsometryEquiv`。
形式化陈述：trans_apply (h₁ : α ≃ᵢ β) (h₂ : β ≃ᵢ γ) (x : α) : h₁.trans h₂ x = h₂ (h₁ x
)
参数：h₁ : α ≃ᵢ β；h₂ : β ≃ᵢ γ；x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem trans_apply (h₁ : α ≃ᵢ β) (h₂ : β ≃ᵢ γ) (x : α) : h₁.trans h₂ x = h₂ (h₁ x) :=
  rfl

/-- The inverse of an isometric isomorphism, as an isometric isomorphism. -/
/-
**IsometryEquiv.symm** 是 Mathlib 中的一个定义，位于命名空间 `IsometryEquiv`。
形式化陈述：{α : Type u} → {β : Type v} → [inst : PseudoEMetricSpace α] → [inst_1 : Ps
eudoEMetricSpace β] → α ≃ᵢ β → β ≃ᵢ α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The inverse of an isometric isomorphism, as an isometric isomorphism.
-/
protected def symm (h : α ≃ᵢ β) : β ≃ᵢ α where
  isometry_toFun := h.isometry.right_inv h.right_inv
  toEquiv := h.toEquiv.symm

/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
  because it is a composition of multiple projections. -/
/-
**IsometryEquiv.Simps.apply** 是 Mathlib 中的一个定义，位于命名空间 `IsometryEquiv.Simps`。
形式化陈述：{α : Type u} → {β : Type v} → [inst : PseudoEMetricSpace α] → [inst_1 : Ps
eudoEMetricSpace β] → α ≃ᵢ β → α → β
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See Note [custom simps projection]. We need to specify this projection explicitl
y in this case,
  because it is a composition of multiple projections.
-/
def Simps.apply (h : α ≃ᵢ β) : α → β := h

/-- See Note [custom simps projection] -/
/-
**IsometryEquiv.Simps.symm_apply** 是 Mathlib 中的一个定义，位于命名空间 `IsometryEquiv.Simps`
。
形式化陈述：{α : Type u} → {β : Type v} → [inst : PseudoEMetricSpace α] → [inst_1 : Ps
eudoEMetricSpace β] → α ≃ᵢ β → β → α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See Note [custom simps projection]
-/
def Simps.symm_apply (h : α ≃ᵢ β) : β → α :=
  h.symm

initialize_simps_projections IsometryEquiv (toFun → apply, invFun → symm_apply)

@[simp]
/-
**IsometryEquiv.coe_symm_toEquiv** 是 Mathlib 中的一个定理，位于命名空间 `IsometryEquiv`。
形式化陈述：coe_symm_toEquiv (h : α ≃ᵢ β) : ⇑h.toEquiv.symm = h.symm
参数：h : α ≃ᵢ β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem coe_symm_toEquiv (h : α ≃ᵢ β) : ⇑h.toEquiv.symm = h.symm := rfl

@[simp]
/-
**IsometryEquiv.symm_symm** 是 Mathlib 中的一个定理，位于命名空间 `IsometryEquiv`。
形式化陈述：symm_symm (h : α ≃ᵢ β) : h.symm.symm = h
参数：h : α ≃ᵢ β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_symm (h : α ≃ᵢ β) : h.symm.symm = h := rfl
/-
**IsometryEquiv.symm_bijective** 是 Mathlib 中的一个定理，位于命名空间 `IsometryEquiv`。
形式化陈述：symm_bijective : Bijective (IsometryEquiv.symm : (α ≃ᵢ β) -> β ≃ᵢ α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.bijective_iff_has_inverse`：bijective_iff_has_inverse : Bijectiv
e f ↔ exists g, LeftInverse g f ∧ RightInverse g f
· 使用定理 `IsometryEquiv.symm_symm`：symm_symm (h : α ≃ᵢ β) : h.symm.symm = h
-/
theorem symm_bijective : Bijective (IsometryEquiv.symm : (α ≃ᵢ β) → β ≃ᵢ α) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

@[simp]
/-
**IsometryEquiv.apply_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `IsometryEquiv`。
形式化陈述：apply_symm_apply (h : α ≃ᵢ β) (y : β) : h (h.symm y) = y
参数：h : α ≃ᵢ β；y : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
-/
theorem apply_symm_apply (h : α ≃ᵢ β) (y : β) : h (h.symm y) = y :=
  h.toEquiv.apply_symm_apply y

@[simp]
/-
**IsometryEquiv.symm_apply_apply** 是 Mathlib 中的一个定理，位于命名空间 `IsometryEquiv`。
形式化陈述：symm_apply_apply (h : α ≃ᵢ β) (x : α) : h.symm (h x) = x
参数：h : α ≃ᵢ β；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
-/
theorem symm_apply_apply (h : α ≃ᵢ β) (x : α) : h.symm (h x) = x :=
  h.toEquiv.symm_apply_apply x
/-
**IsometryEquiv.symm_apply_eq** 是 Mathlib 中的一个定理，位于命名空间 `IsometryEquiv`。
形式化陈述：symm_apply_eq (h : α ≃ᵢ β) {x : α} {y : β} : h.symm y = x ↔ y = h x
参数：h : α ≃ᵢ β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm_apply_eq`：symm_apply_eq {α β} (e : α ≃ β) {x y} : e.symm x = 
y ↔ x = e y
-/
theorem symm_apply_eq (h : α ≃ᵢ β) {x : α} {y : β} : h.symm y = x ↔ y = h x :=
  h.toEquiv.symm_apply_eq
/-
**IsometryEquiv.eq_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `IsometryEquiv`。
形式化陈述：eq_symm_apply (h : α ≃ᵢ β) {x : α} {y : β} : x = h.symm y ↔ h x = y
参数：h : α ≃ᵢ β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.eq_symm_apply`：eq_symm_apply {α β} (e : α ≃ β) {x y} : y = e.symm 
x ↔ e y = x
-/
theorem eq_symm_apply (h : α ≃ᵢ β) {x : α} {y : β} : x = h.symm y ↔ h x = y :=
  h.toEquiv.eq_symm_apply
/-
**IsometryEquiv.symm_comp_self** 是 Mathlib 中的一个定理，位于命名空间 `IsometryEquiv`。
形式化陈述：symm_comp_self (h : α ≃ᵢ β) : (h.symm : β -> α) ∘ h = id
参数：h : α ≃ᵢ β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Equiv.left_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Function
.LeftInverse self.invFun self.toFun
-/
theorem symm_comp_self (h : α ≃ᵢ β) : (h.symm : β → α) ∘ h = id := funext h.left_inv
/-
**IsometryEquiv.self_comp_symm** 是 Mathlib 中的一个定理，位于命名空间 `IsometryEquiv`。
形式化陈述：self_comp_symm (h : α ≃ᵢ β) : (h : α -> β) ∘ h.symm = id
参数：h : α ≃ᵢ β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Equiv.right_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Functio
n.RightInverse self.invFun self.toFun
-/
theorem self_comp_symm (h : α ≃ᵢ β) : (h : α → β) ∘ h.symm = id := funext h.right_inv
/-
**IsometryEquiv.range_eq_univ** 是 Mathlib 中的一个定理，位于命名空间 `IsometryEquiv`。
形式化陈述：range_eq_univ (h : α ≃ᵢ β) : range h = univ
参数：h : α ≃ᵢ β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EquivLike.range_eq_univ`：range_eq_univ {α : Type*} {β : Type*} {E : Type
*} [EquivLike E α β] (e : E) : range e = univ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem range_eq_univ (h : α ≃ᵢ β) : range h = univ := by simp
/-
**IsometryEquiv.image_symm** 是 Mathlib 中的一个定理，位于命名空间 `IsometryEquiv`。
形式化陈述：image_symm (h : α ≃ᵢ β) : image h.symm = preimage h
参数：h : α ≃ᵢ β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_eq_preimage_of_inverse`：image_eq_preimage_of_inverse {f : α ->
 β} {g : β -> α} (h₁ : LeftInverse g f) (h₂ : RightInverse g f) : image f = prei
mage g
· 使用定理 `Equiv.left_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Function
.LeftInverse self.invFun self.toFun
· 使用定理 `Equiv.right_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Functio
n.RightInverse self.invFun self.toFun
-/
theorem image_symm (h : α ≃ᵢ β) : image h.symm = preimage h :=
  image_eq_preimage_of_inverse h.symm.toEquiv.left_inv h.symm.toEquiv.right_inv
/-
**IsometryEquiv.preimage_symm** 是 Mathlib 中的一个定理，位于命名空间 `IsometryEquiv`。
形式化陈述：preimage_symm (h : α ≃ᵢ β) : preimage h.symm = image h
参数：h : α ≃ᵢ β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_eq_preimage_of_inverse`：image_eq_preimage_of_inverse {f : α ->
 β} {g : β -> α} (h₁ : LeftInverse g f) (h₂ : RightInverse g f) : image f = prei
mage g
· 使用定理 `Equiv.left_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Function
.LeftInverse self.invFun self.toFun
· 使用定理 `Equiv.right_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Functio
n.RightInverse self.invFun self.toFun
-/
theorem preimage_symm (h : α ≃ᵢ β) : preimage h.symm = image h :=
  (image_eq_preimage_of_inverse h.toEquiv.left_inv h.toEquiv.right_inv).symm

@[simp]
/-
**IsometryEquiv.symm_trans_apply** 是 Mathlib 中的一个定理，位于命名空间 `IsometryEquiv`。
形式化陈述：symm_trans_apply (h₁ : α ≃ᵢ β) (h₂ : β ≃ᵢ γ) (x : γ) : (h₁.trans h₂).symm 
x = h₁.symm (h₂.symm x)
参数：h₁ : α ≃ᵢ β；h₂ : β ≃ᵢ γ；x : γ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_trans_apply (h₁ : α ≃ᵢ β) (h₂ : β ≃ᵢ γ) (x : γ) :
    (h₁.trans h₂).symm x = h₁.symm (h₂.symm x) :=
  rfl
/-
**IsometryEquiv.ediam_univ** 是 Mathlib 中的一个定理，位于命名空间 `IsometryEquiv`。
形式化陈述：ediam_univ (h : α ≃ᵢ β) : Metric.ediam (univ : Set α) = Metric.ediam (univ
 : Set β)
参数：h : α ≃ᵢ β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsometryEquiv.range_eq_univ`：range_eq_univ (h : α ≃ᵢ β) : range h = univ
· 使用定理 `Isometry.ediam_range`：ediam_range (hf : Isometry f) : Metric.ediam (rang
e f) = Metric.ediam (univ : Set α)
· 使用定理 `IsometryEquiv.isometry`：∀ {α : Type u} {β : Type v} [inst : PseudoEMetri
cSpace α] [inst_1 : PseudoEMetricSpace β] (h : α ≃ᵢ β), Isometry ⇑h
-/
theorem ediam_univ (h : α ≃ᵢ β) : Metric.ediam (univ : Set α) = Metric.ediam (univ : Set β) := by
  rw [← h.range_eq_univ, h.isometry.ediam_range]

@[simp]
/-
**IsometryEquiv.ediam_preimage** 是 Mathlib 中的一个定理，位于命名空间 `IsometryEquiv`。
形式化陈述：ediam_preimage (h : α ≃ᵢ β) (s : Set β) : Metric.ediam (h ⁻¹' s) = Metric.
ediam s
参数：h : α ≃ᵢ β；s : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsometryEquiv.image_symm`：image_symm (h : α ≃ᵢ β) : image h.symm = preim
age h
· 使用定理 `IsometryEquiv.ediam_image`：ediam_image (h : α ≃ᵢ β) (s : Set α) : Metric
.ediam (h '' s) = Metric.ediam s
-/
theorem ediam_preimage (h : α ≃ᵢ β) (s : Set β) : Metric.ediam (h ⁻¹' s) = Metric.ediam s := by
  rw [← image_symm, ediam_image]

@[simp]
/-
**IsometryEquiv.preimage_eball** 是 Mathlib 中的一个定理，位于命名空间 `IsometryEquiv`。
形式化陈述：preimage_eball (h : α ≃ᵢ β) (x : β) (r : Real>=0∞) : h ⁻¹' Metric.eball x 
r = Metric.eball (h.symm x) r
参数：h : α ≃ᵢ β；x : β；r : Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Isometry.preimage_eball`：preimage_eball (h : Isometry f) (x : α) (r : Re
al>=0∞) : f ⁻¹' Metric.eball (f x) r = Metric.eball x r
· 使用定理 `IsometryEquiv.isometry`：∀ {α : Type u} {β : Type v} [inst : PseudoEMetri
cSpace α] [inst_1 : PseudoEMetricSpace β] (h : α ≃ᵢ β), Isometry ⇑h
· 使用定理 `IsometryEquiv.apply_symm_apply`：apply_symm_apply (h : α ≃ᵢ β) (y : β) : 
h (h.symm y) = y
-/
theorem preimage_eball (h : α ≃ᵢ β) (x : β) (r : ℝ≥0∞) :
    h ⁻¹' Metric.eball x r = Metric.eball (h.symm x) r := by
  rw [← h.isometry.preimage_eball (h.symm x) r, h.apply_symm_apply]

@[deprecated (since := "2026-01-24")]
alias preimage_emetric_ball := preimage_eball

@[simp]
/-
**IsometryEquiv.preimage_closedEBall** 是 Mathlib 中的一个定理，位于命名空间 `IsometryEquiv`。
形式化陈述：preimage_closedEBall (h : α ≃ᵢ β) (x : β) (r : Real>=0∞) : h ⁻¹' Metric.cl
osedEBall x r = Metric.closedEBall (h.symm x) r
参数：h : α ≃ᵢ β；x : β；r : Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Isometry.preimage_closedEBall`：preimage_closedEBall (h : Isometry f) (x 
: α) (r : Real>=0∞) : f ⁻¹' Metric.closedEBall (f x) r = Metric.closedEBall x r
· 使用定理 `IsometryEquiv.isometry`：∀ {α : Type u} {β : Type v} [inst : PseudoEMetri
cSpace α] [inst_1 : PseudoEMetricSpace β] (h : α ≃ᵢ β), Isometry ⇑h
· 使用定理 `IsometryEquiv.apply_symm_apply`：apply_symm_apply (h : α ≃ᵢ β) (y : β) : 
h (h.symm y) = y
-/
theorem preimage_closedEBall (h : α ≃ᵢ β) (x : β) (r : ℝ≥0∞) :
    h ⁻¹' Metric.closedEBall x r = Metric.closedEBall (h.symm x) r := by
  rw [← h.isometry.preimage_closedEBall (h.symm x) r, h.apply_symm_apply]

@[deprecated (since := "2026-01-24")]
alias preimage_emetric_closedBall := preimage_closedEBall

@[simp]
/-
**IsometryEquiv.image_eball** 是 Mathlib 中的一个定理，位于命名空间 `IsometryEquiv`。
形式化陈述：image_eball (h : α ≃ᵢ β) (x : α) (r : Real>=0∞) : h '' Metric.eball x r = 
Metric.eball (h x) r
参数：h : α ≃ᵢ β；x : α；r : Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsometryEquiv.preimage_symm`：preimage_symm (h : α ≃ᵢ β) : preimage h.sym
m = image h
· 使用定理 `IsometryEquiv.preimage_eball`：preimage_eball (h : α ≃ᵢ β) (x : β) (r : R
eal>=0∞) : h ⁻¹' Metric.eball x r = Metric.eball (h.symm x) r
· 使用定理 `IsometryEquiv.symm_symm`：symm_symm (h : α ≃ᵢ β) : h.symm.symm = h
-/
theorem image_eball (h : α ≃ᵢ β) (x : α) (r : ℝ≥0∞) :
    h '' Metric.eball x r = Metric.eball (h x) r := by
  rw [← h.preimage_symm, h.symm.preimage_eball, symm_symm]

@[deprecated (since := "2026-01-24")]
alias image_emetric_ball := image_eball

@[simp]
/-
**IsometryEquiv.image_closedEBall** 是 Mathlib 中的一个定理，位于命名空间 `IsometryEquiv`。
形式化陈述：image_closedEBall (h : α ≃ᵢ β) (x : α) (r : Real>=0∞) : h '' Metric.closed
EBall x r = Metric.closedEBall (h x) r
参数：h : α ≃ᵢ β；x : α；r : Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsometryEquiv.preimage_symm`：preimage_symm (h : α ≃ᵢ β) : preimage h.sym
m = image h
· 使用定理 `IsometryEquiv.preimage_closedEBall`：preimage_closedEBall (h : α ≃ᵢ β) (x
 : β) (r : Real>=0∞) : h ⁻¹' Metric.closedEBall x r = Metric.closedEBall (h.symm
 x) r
· 使用定理 `IsometryEquiv.symm_symm`：symm_symm (h : α ≃ᵢ β) : h.symm.symm = h
-/
theorem image_closedEBall (h : α ≃ᵢ β) (x : α) (r : ℝ≥0∞) :
    h '' Metric.closedEBall x r = Metric.closedEBall (h x) r := by
  rw [← h.preimage_symm, h.symm.preimage_closedEBall, symm_symm]

@[deprecated (since := "2026-01-24")]
alias image_emetric_closedBall := image_closedEBall

/-- The (bundled) homeomorphism associated to an isometric isomorphism. -/
@[simps toEquiv]
/-
**IsometryEquiv.toHomeomorph** 是 Mathlib 中的一个定义，位于命名空间 `IsometryEquiv`。
形式化陈述：{α : Type u} → {β : Type v} → [inst : PseudoEMetricSpace α] → [inst_1 : Ps
eudoEMetricSpace β] → α ≃ᵢ β → α ≃ₜ β
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsometryEquiv.continuous`：∀ {α : Type u} {β : Type v} [inst : PseudoEMet
ricSpace α] [inst_1 : PseudoEMetricSpace β] (h : α ≃ᵢ β), Continuous ⇑h

--- 原说明 ---
The (bundled) homeomorphism associated to an isometric isomorphism.
-/
protected def toHomeomorph (h : α ≃ᵢ β) : α ≃ₜ β where
  continuous_toFun := h.continuous
  continuous_invFun := h.symm.continuous
  toEquiv := h.toEquiv

@[simp]
/-
**IsometryEquiv.coe_toHomeomorph** 是 Mathlib 中的一个定理，位于命名空间 `IsometryEquiv`。
形式化陈述：coe_toHomeomorph (h : α ≃ᵢ β) : ⇑h.toHomeomorph = h
参数：h : α ≃ᵢ β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toHomeomorph (h : α ≃ᵢ β) : ⇑h.toHomeomorph = h :=
  rfl

@[simp]
/-
**IsometryEquiv.coe_toHomeomorph_symm** 是 Mathlib 中的一个定理，位于命名空间 `IsometryEquiv`。
形式化陈述：coe_toHomeomorph_symm (h : α ≃ᵢ β) : ⇑h.toHomeomorph.symm = h.symm
参数：h : α ≃ᵢ β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toHomeomorph_symm (h : α ≃ᵢ β) : ⇑h.toHomeomorph.symm = h.symm :=
  rfl

@[simp]
/-
**IsometryEquiv.comp_continuousOn_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsometryEquiv`。
形式化陈述：comp_continuousOn_iff {γ} [TopologicalSpace γ] (h : α ≃ᵢ β) {f : γ -> α} {
s : Set γ} : ContinuousOn (h ∘ f) s ↔ ContinuousOn f s
参数：h : α ≃ᵢ β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.comp_continuousOn_iff`：comp_continuousOn_iff (h : X ≃ₜ Y) (f 
: Z -> X) (s : Set Z) : ContinuousOn (h ∘ f) s ↔ ContinuousOn f s
-/
theorem comp_continuousOn_iff {γ} [TopologicalSpace γ] (h : α ≃ᵢ β) {f : γ → α} {s : Set γ} :
    ContinuousOn (h ∘ f) s ↔ ContinuousOn f s :=
  h.toHomeomorph.comp_continuousOn_iff _ _

@[simp]
/-
**IsometryEquiv.comp_continuous_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsometryEquiv`。
形式化陈述：comp_continuous_iff {γ} [TopologicalSpace γ] (h : α ≃ᵢ β) {f : γ -> α} : C
ontinuous (h ∘ f) ↔ Continuous f
参数：h : α ≃ᵢ β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.comp_continuous_iff`：comp_continuous_iff (h : X ≃ₜ Y) {f : Z 
-> X} : Continuous (h ∘ f) ↔ Continuous f
-/
theorem comp_continuous_iff {γ} [TopologicalSpace γ] (h : α ≃ᵢ β) {f : γ → α} :
    Continuous (h ∘ f) ↔ Continuous f :=
  h.toHomeomorph.comp_continuous_iff

@[simp]
/-
**IsometryEquiv.comp_continuous_iff'** 是 Mathlib 中的一个定理，位于命名空间 `IsometryEquiv`。
形式化陈述：comp_continuous_iff' {γ} [TopologicalSpace γ] (h : α ≃ᵢ β) {f : β -> γ} : 
Continuous (f ∘ h) ↔ Continuous f
参数：h : α ≃ᵢ β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.comp_continuous_iff'`：comp_continuous_iff' (h : X ≃ₜ Y) {f : 
Y -> Z} : Continuous (f ∘ h) ↔ Continuous f
-/
theorem comp_continuous_iff' {γ} [TopologicalSpace γ] (h : α ≃ᵢ β) {f : β → γ} :
    Continuous (f ∘ h) ↔ Continuous f :=
  h.toHomeomorph.comp_continuous_iff'

/-- The group of isometries. -/
/-
**IsometryEquiv.** 是 Mathlib 中的一个实例，位于命名空间 `IsometryEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The group of isometries.
-/
instance : Group (α ≃ᵢ α) where
  one := IsometryEquiv.refl _
  mul e₁ e₂ := e₂.trans e₁
  inv := IsometryEquiv.symm
  mul_assoc _ _ _ := rfl
  one_mul _ := ext fun _ => rfl
  mul_one _ := ext fun _ => rfl
  inv_mul_cancel e := ext e.symm_apply_apply
/-
**IsometryEquiv.coe_one** 是 Mathlib 中的一个定理，位于命名空间 `IsometryEquiv`。
形式化陈述：∀ {α : Type u} [inst : PseudoEMetricSpace α], ⇑1 = id
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem coe_one : ⇑(1 : α ≃ᵢ α) = id := rfl
/-
**IsometryEquiv.coe_mul** 是 Mathlib 中的一个定理，位于命名空间 `IsometryEquiv`。
形式化陈述：∀ {α : Type u} [inst : PseudoEMetricSpace α] (e₁ e₂ : α ≃ᵢ α), ⇑(e₁ * e₂) 
= ⇑e₁ ∘ ⇑e₂
参数：e₁ e₂ : α ≃ᵢ α；e₁ * e₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem coe_mul (e₁ e₂ : α ≃ᵢ α) : ⇑(e₁ * e₂) = e₁ ∘ e₂ := rfl
/-
**IsometryEquiv.mul_apply** 是 Mathlib 中的一个定理，位于命名空间 `IsometryEquiv`。
形式化陈述：mul_apply (e₁ e₂ : α ≃ᵢ α) (x : α) : (e₁ * e₂) x = e₁ (e₂ x)
参数：e₁ e₂ : α ≃ᵢ α；x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mul_apply (e₁ e₂ : α ≃ᵢ α) (x : α) : (e₁ * e₂) x = e₁ (e₂ x) := rfl
/-
**IsometryEquiv.inv_apply_self** 是 Mathlib 中的一个定理，位于命名空间 `IsometryEquiv`。
形式化陈述：∀ {α : Type u} [inst : PseudoEMetricSpace α] (e : α ≃ᵢ α) (x : α), e⁻¹ (e 
x) = x
参数：e : α ≃ᵢ α；x : α；e x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsometryEquiv.symm_apply_apply`：symm_apply_apply (h : α ≃ᵢ β) (x : α) : 
h.symm (h x) = x
-/
@[simp] theorem inv_apply_self (e : α ≃ᵢ α) (x : α) : e⁻¹ (e x) = x := e.symm_apply_apply x
/-
**IsometryEquiv.apply_inv_self** 是 Mathlib 中的一个定理，位于命名空间 `IsometryEquiv`。
形式化陈述：∀ {α : Type u} [inst : PseudoEMetricSpace α] (e : α ≃ᵢ α) (x : α), e (e⁻¹ 
x) = x
参数：e : α ≃ᵢ α；x : α；e⁻¹ x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsometryEquiv.apply_symm_apply`：apply_symm_apply (h : α ≃ᵢ β) (y : β) : 
h (h.symm y) = y
-/
@[simp] theorem apply_inv_self (e : α ≃ᵢ α) (x : α) : e (e⁻¹ x) = x := e.apply_symm_apply x
/-
**IsometryEquiv.completeSpace_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsometryEquiv`。
形式化陈述：completeSpace_iff (e : α ≃ᵢ β) : CompleteSpace α ↔ CompleteSpace β
参数：e : α ≃ᵢ β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsometryEquiv.range_eq_univ`：range_eq_univ (h : α ≃ᵢ β) : range h = univ
· 使用定理 `isComplete_image_iff`：isComplete_image_iff {m : α -> β} {s : Set α} (hm 
: IsUniformInducing m) : IsComplete (m '' s) ↔ IsComplete s
· 使用定理 `Isometry.isUniformInducing`：isUniformInducing (hf : Isometry f) : IsUnif
ormInducing f
· 使用定理 `IsometryEquiv.isometry`：∀ {α : Type u} {β : Type v} [inst : PseudoEMetri
cSpace α] [inst_1 : PseudoEMetricSpace β] (h : α ≃ᵢ β), Isometry ⇑h
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem completeSpace_iff (e : α ≃ᵢ β) : CompleteSpace α ↔ CompleteSpace β := by
  simp only [completeSpace_iff_isComplete_univ, ← e.range_eq_univ, ← image_univ,
    isComplete_image_iff e.isometry.isUniformInducing]
/-
**IsometryEquiv.completeSpace** 是 Mathlib 中的一个定理，位于命名空间 `IsometryEquiv`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : PseudoEMetricSpace α] [inst_1 : Pseudo
EMetricSpace β] [CompleteSpace β]   (e : α ≃ᵢ β), CompleteSpace α
参数：e : α ≃ᵢ β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsometryEquiv.completeSpace_iff`：completeSpace_iff (e : α ≃ᵢ β) : Comple
teSpace α ↔ CompleteSpace β
-/
protected theorem completeSpace [CompleteSpace β] (e : α ≃ᵢ β) : CompleteSpace α :=
  e.completeSpace_iff.2 ‹_›

/-- The natural isometry `∀ i, Y i ≃ᵢ ∀ j, Y (e.symm j)` obtained from a bijection `ι ≃ ι'` of
fintypes. `Equiv.piCongrLeft'` as an `IsometryEquiv`. -/
@[simps!]
/-
**IsometryEquiv.piCongrLeft'** 是 Mathlib 中的一个定义，位于命名空间 `IsometryEquiv`。
形式化陈述：piCongrLeft' {ι' : Type*} [Fintype ι] [Fintype ι'] {Y : ι -> Type*} [foral
l j, PseudoEMetricSpace (Y j)] (e : ι ≃ ι') : (forall i, Y i) ≃ᵢ forall j, Y (e.
symm j) where toEquiv
参数：Y j；e : ι ≃ ι'。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The natural isometry `∀ i, Y i ≃ᵢ ∀ j, Y (e.symm j)` obtained from a bijection `
ι ≃ ι'` of
fintypes. `Equiv.piCongrLeft'` as an `IsometryEquiv`.
-/
def piCongrLeft' {ι' : Type*} [Fintype ι] [Fintype ι'] {Y : ι → Type*}
    [∀ j, PseudoEMetricSpace (Y j)] (e : ι ≃ ι') : (∀ i, Y i) ≃ᵢ ∀ j, Y (e.symm j) where
  toEquiv := Equiv.piCongrLeft' _ e
  isometry_toFun x1 x2 := by
    simp_rw [edist_pi_def, Finset.sup_univ_eq_iSup]
    exact (Equiv.iSup_comp (g := fun b ↦ edist (x1 b) (x2 b)) e.symm)

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- The natural isometry `∀ i, Y (e i) ≃ᵢ ∀ j, Y j` obtained from a bijection `ι ≃ ι'` of fintypes.
`Equiv.piCongrLeft` as an `IsometryEquiv`. -/
@[simps!]
/-
**IsometryEquiv.piCongrLeft** 是 Mathlib 中的一个定义，位于命名空间 `IsometryEquiv`。
形式化陈述：piCongrLeft {ι' : Type*} [Fintype ι] [Fintype ι'] {Y : ι' -> Type*} [foral
l j, PseudoEMetricSpace (Y j)] (e : ι ≃ ι') : (forall i, Y (e i)) ≃ᵢ forall j, Y
 j
参数：Y j；e : ι ≃ ι'。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The natural isometry `∀ i, Y (e i) ≃ᵢ ∀ j, Y j` obtained from a bijection `ι ≃ ι
'` of fintypes.
`Equiv.piCongrLeft` as an `IsometryEquiv`.
-/
def piCongrLeft {ι' : Type*} [Fintype ι] [Fintype ι'] {Y : ι' → Type*}
    [∀ j, PseudoEMetricSpace (Y j)] (e : ι ≃ ι') : (∀ i, Y (e i)) ≃ᵢ ∀ j, Y j :=
  (piCongrLeft' e.symm).symm

/-- The natural isometry `(α ⊕ β → γ) ≃ᵢ (α → γ) × (β → γ)` between the type of maps on a sum of
fintypes `α ⊕ β` and the pairs of functions on the types `α` and `β`.
`Equiv.sumArrowEquivProdArrow` as an `IsometryEquiv`. -/
@[simps!]
/-
**IsometryEquiv.sumArrowIsometryEquivProdArrow** 是 Mathlib 中的一个定义，位于命名空间 `Isomet
ryEquiv`。
形式化陈述：sumArrowIsometryEquivProdArrow [Fintype α] [Fintype β] : (α oplus β -> γ) 
≃ᵢ (α -> γ) × (β -> γ) where toEquiv
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural isometry `(α ⊕ β → γ) ≃ᵢ (α → γ) × (β → γ)` between the type of maps
 on a sum of
fintypes `α ⊕ β` and the pairs of functions on the types `α` and `β`.
`Equiv.sumArrowEquivProdArrow` as an `IsometryEquiv`.
-/
def sumArrowIsometryEquivProdArrow [Fintype α] [Fintype β] : (α ⊕ β → γ) ≃ᵢ (α → γ) × (β → γ) where
  toEquiv := Equiv.sumArrowEquivProdArrow _ _ _
  isometry_toFun _ _ := by simp [Prod.edist_eq, edist_pi_def, Finset.sup_univ_eq_iSup, iSup_sum]

@[simp]
/-
**IsometryEquiv.sumArrowIsometryEquivProdArrow_toHomeomorph** 是 Mathlib 中的一个定理，位
于命名空间 `IsometryEquiv`。
形式化陈述：sumArrowIsometryEquivProdArrow_toHomeomorph {α β : Type*} [Fintype α] [Fin
type β] : sumArrowIsometryEquivProdArrow.toHomeomorph = Homeomorph.sumArrowHomeo
morphProdArrow (ι
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sumArrowIsometryEquivProdArrow_toHomeomorph {α β : Type*} [Fintype α] [Fintype β] :
    sumArrowIsometryEquivProdArrow.toHomeomorph
    = Homeomorph.sumArrowHomeomorphProdArrow (ι := α) (ι' := β) (X := γ) :=
  rfl
/-
**IsometryEquiv._root_.Fin.edist_append_eq_max_edist** 是 Mathlib 中的一个定理，位于命名空间 `
IsometryEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Fin.edist_append_eq_max_edist (m n : ℕ) {x x2 : Fin m → α} {y y2 : Fin n → α} :
    edist (Fin.append x y) (Fin.append x2 y2) = max (edist x x2) (edist y y2) := by
  simp [edist_pi_def, Finset.sup_univ_eq_iSup, ← Equiv.iSup_comp (e := finSumFinEquiv),
    iSup_sum]

/-- The natural `IsometryEquiv` between `(Fin m → α) × (Fin n → α)` and `Fin (m + n) → α`.
`Fin.appendEquiv` as an `IsometryEquiv`. -/
@[simps!]
/-
**IsometryEquiv._root_.Fin.appendIsometry** 是 Mathlib 中的一个定义，位于命名空间 `IsometryEqu
iv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural `IsometryEquiv` between `(Fin m → α) × (Fin n → α)` and `Fin (m + n)
 → α`.
`Fin.appendEquiv` as an `IsometryEquiv`.
-/
def _root_.Fin.appendIsometry (m n : ℕ) : (Fin m → α) × (Fin n → α) ≃ᵢ (Fin (m + n) → α) where
  toEquiv := Fin.appendEquiv _ _
  isometry_toFun _ _ := by simp_rw [Fin.appendEquiv, Fin.edist_append_eq_max_edist, Prod.edist_eq]

@[simp]
/-
**IsometryEquiv._root_.Fin.appendIsometry_toHomeomorph** 是 Mathlib 中的一个定理，位于命名空间
 `IsometryEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Fin.appendIsometry_toHomeomorph (m n : ℕ) :
    (Fin.appendIsometry m n).toHomeomorph = Fin.appendHomeomorph (X := α) m n :=
  rfl

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- The natural `IsometryEquiv` `(Fin m → ℝ) × (Fin l → ℝ) ≃ᵢ (Fin n → ℝ)` when `m + l = n`. -/
@[simps!]
/-
**IsometryEquiv._root_.Fin.appendIsometryOfEq** 是 Mathlib 中的一个定义，位于命名空间 `Isometr
yEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural `IsometryEquiv` `(Fin m → ℝ) × (Fin l → ℝ) ≃ᵢ (Fin n → ℝ)` when `m +
 l = n`.
-/
def _root_.Fin.appendIsometryOfEq {n m l : ℕ} (hmln : m + l = n) :
    (Fin m → α) × (Fin l → α) ≃ᵢ (Fin n → α) :=
  (Fin.appendIsometry m l).trans (IsometryEquiv.piCongrLeft (Y := fun _ ↦ α) (finCongr hmln))

variable (ι α)

/-- `Equiv.funUnique` as an `IsometryEquiv`. -/
@[simps!]
/-
**IsometryEquiv.funUnique** 是 Mathlib 中的一个定义，位于命名空间 `IsometryEquiv`。
形式化陈述：funUnique [Unique ι] [Fintype ι] : (ι -> α) ≃ᵢ α where toEquiv
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Equiv.funUnique` as an `IsometryEquiv`.
-/
def funUnique [Unique ι] [Fintype ι] : (ι → α) ≃ᵢ α where
  toEquiv := Equiv.funUnique ι α
  isometry_toFun x hx := by simp [edist_pi_def, Finset.univ_unique, Finset.sup_singleton]

/-- `piFinTwoEquiv` as an `IsometryEquiv`. -/
@[simps!]
/-
**IsometryEquiv.piFinTwo** 是 Mathlib 中的一个定义，位于命名空间 `IsometryEquiv`。
形式化陈述：piFinTwo (α : Fin 2 -> Type*) [forall i, PseudoEMetricSpace (α i)] : (fora
ll i, α i) ≃ᵢ α 0 × α 1 where toEquiv
参数：α : Fin 2 -> Type*；α i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`piFinTwoEquiv` as an `IsometryEquiv`.
-/
def piFinTwo (α : Fin 2 → Type*) [∀ i, PseudoEMetricSpace (α i)] : (∀ i, α i) ≃ᵢ α 0 × α 1 where
  toEquiv := piFinTwoEquiv α
  isometry_toFun x hx := by simp [edist_pi_def, Fin.univ_succ, Prod.edist_eq]

end PseudoEMetricSpace

section PseudoMetricSpace

variable [PseudoMetricSpace α] [PseudoMetricSpace β] (h : α ≃ᵢ β)

@[simp]
/-
**IsometryEquiv.diam_image** 是 Mathlib 中的一个定理，位于命名空间 `IsometryEquiv`。
形式化陈述：diam_image (s : Set α) : Metric.diam (h '' s) = Metric.diam s
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.diam_image`：diam_image (hf : Isometry f) (s : Set α) : Metric.d
iam (f '' s) = Metric.diam s
· 使用定理 `IsometryEquiv.isometry`：∀ {α : Type u} {β : Type v} [inst : PseudoEMetri
cSpace α] [inst_1 : PseudoEMetricSpace β] (h : α ≃ᵢ β), Isometry ⇑h
-/
theorem diam_image (s : Set α) : Metric.diam (h '' s) = Metric.diam s :=
  h.isometry.diam_image s

@[simp]
/-
**IsometryEquiv.diam_preimage** 是 Mathlib 中的一个定理，位于命名空间 `IsometryEquiv`。
形式化陈述：diam_preimage (s : Set β) : Metric.diam (h ⁻¹' s) = Metric.diam s
参数：s : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsometryEquiv.image_symm`：image_symm (h : α ≃ᵢ β) : image h.symm = preim
age h
· 使用定理 `IsometryEquiv.diam_image`：diam_image (s : Set α) : Metric.diam (h '' s) 
= Metric.diam s
-/
theorem diam_preimage (s : Set β) : Metric.diam (h ⁻¹' s) = Metric.diam s := by
  rw [← image_symm, diam_image]

include h in
/-
**IsometryEquiv.diam_univ** 是 Mathlib 中的一个定理，位于命名空间 `IsometryEquiv`。
形式化陈述：diam_univ : Metric.diam (univ : Set α) = Metric.diam (univ : Set β)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `IsometryEquiv.ediam_univ`：ediam_univ (h : α ≃ᵢ β) : Metric.ediam (univ :
 Set α) = Metric.ediam (univ : Set β)
-/
theorem diam_univ : Metric.diam (univ : Set α) = Metric.diam (univ : Set β) :=
  congr_arg ENNReal.toReal h.ediam_univ

@[simp]
/-
**IsometryEquiv.preimage_ball** 是 Mathlib 中的一个定理，位于命名空间 `IsometryEquiv`。
形式化陈述：preimage_ball (h : α ≃ᵢ β) (x : β) (r : Real) : h ⁻¹' Metric.ball x r = Me
tric.ball (h.symm x) r
参数：h : α ≃ᵢ β；x : β；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Isometry.preimage_ball`：preimage_ball (hf : Isometry f) (x : α) (r : Rea
l) : f ⁻¹' Metric.ball (f x) r = Metric.ball x r
· 使用定理 `IsometryEquiv.isometry`：∀ {α : Type u} {β : Type v} [inst : PseudoEMetri
cSpace α] [inst_1 : PseudoEMetricSpace β] (h : α ≃ᵢ β), Isometry ⇑h
· 使用定理 `IsometryEquiv.apply_symm_apply`：apply_symm_apply (h : α ≃ᵢ β) (y : β) : 
h (h.symm y) = y
-/
theorem preimage_ball (h : α ≃ᵢ β) (x : β) (r : ℝ) :
    h ⁻¹' Metric.ball x r = Metric.ball (h.symm x) r := by
  rw [← h.isometry.preimage_ball (h.symm x) r, h.apply_symm_apply]

@[simp]
/-
**IsometryEquiv.preimage_sphere** 是 Mathlib 中的一个定理，位于命名空间 `IsometryEquiv`。
形式化陈述：preimage_sphere (h : α ≃ᵢ β) (x : β) (r : Real) : h ⁻¹' Metric.sphere x r 
= Metric.sphere (h.symm x) r
参数：h : α ≃ᵢ β；x : β；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Isometry.preimage_sphere`：preimage_sphere (hf : Isometry f) (x : α) (r :
 Real) : f ⁻¹' Metric.sphere (f x) r = Metric.sphere x r
· 使用定理 `IsometryEquiv.isometry`：∀ {α : Type u} {β : Type v} [inst : PseudoEMetri
cSpace α] [inst_1 : PseudoEMetricSpace β] (h : α ≃ᵢ β), Isometry ⇑h
· 使用定理 `IsometryEquiv.apply_symm_apply`：apply_symm_apply (h : α ≃ᵢ β) (y : β) : 
h (h.symm y) = y
-/
theorem preimage_sphere (h : α ≃ᵢ β) (x : β) (r : ℝ) :
    h ⁻¹' Metric.sphere x r = Metric.sphere (h.symm x) r := by
  rw [← h.isometry.preimage_sphere (h.symm x) r, h.apply_symm_apply]

@[simp]
/-
**IsometryEquiv.preimage_closedBall** 是 Mathlib 中的一个定理，位于命名空间 `IsometryEquiv`。
形式化陈述：preimage_closedBall (h : α ≃ᵢ β) (x : β) (r : Real) : h ⁻¹' Metric.closedB
all x r = Metric.closedBall (h.symm x) r
参数：h : α ≃ᵢ β；x : β；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Isometry.preimage_closedBall`：preimage_closedBall (hf : Isometry f) (x :
 α) (r : Real) : f ⁻¹' Metric.closedBall (f x) r = Metric.closedBall x r
· 使用定理 `IsometryEquiv.isometry`：∀ {α : Type u} {β : Type v} [inst : PseudoEMetri
cSpace α] [inst_1 : PseudoEMetricSpace β] (h : α ≃ᵢ β), Isometry ⇑h
· 使用定理 `IsometryEquiv.apply_symm_apply`：apply_symm_apply (h : α ≃ᵢ β) (y : β) : 
h (h.symm y) = y
-/
theorem preimage_closedBall (h : α ≃ᵢ β) (x : β) (r : ℝ) :
    h ⁻¹' Metric.closedBall x r = Metric.closedBall (h.symm x) r := by
  rw [← h.isometry.preimage_closedBall (h.symm x) r, h.apply_symm_apply]

@[simp]
/-
**IsometryEquiv.image_ball** 是 Mathlib 中的一个定理，位于命名空间 `IsometryEquiv`。
形式化陈述：image_ball (h : α ≃ᵢ β) (x : α) (r : Real) : h '' Metric.ball x r = Metric
.ball (h x) r
参数：h : α ≃ᵢ β；x : α；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsometryEquiv.preimage_symm`：preimage_symm (h : α ≃ᵢ β) : preimage h.sym
m = image h
· 使用定理 `IsometryEquiv.preimage_ball`：preimage_ball (h : α ≃ᵢ β) (x : β) (r : Rea
l) : h ⁻¹' Metric.ball x r = Metric.ball (h.symm x) r
· 使用定理 `IsometryEquiv.symm_symm`：symm_symm (h : α ≃ᵢ β) : h.symm.symm = h
-/
theorem image_ball (h : α ≃ᵢ β) (x : α) (r : ℝ) : h '' Metric.ball x r = Metric.ball (h x) r := by
  rw [← h.preimage_symm, h.symm.preimage_ball, symm_symm]

@[simp]
/-
**IsometryEquiv.image_sphere** 是 Mathlib 中的一个定理，位于命名空间 `IsometryEquiv`。
形式化陈述：image_sphere (h : α ≃ᵢ β) (x : α) (r : Real) : h '' Metric.sphere x r = Me
tric.sphere (h x) r
参数：h : α ≃ᵢ β；x : α；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsometryEquiv.preimage_symm`：preimage_symm (h : α ≃ᵢ β) : preimage h.sym
m = image h
· 使用定理 `IsometryEquiv.preimage_sphere`：preimage_sphere (h : α ≃ᵢ β) (x : β) (r :
 Real) : h ⁻¹' Metric.sphere x r = Metric.sphere (h.symm x) r
· 使用定理 `IsometryEquiv.symm_symm`：symm_symm (h : α ≃ᵢ β) : h.symm.symm = h
-/
theorem image_sphere (h : α ≃ᵢ β) (x : α) (r : ℝ) :
    h '' Metric.sphere x r = Metric.sphere (h x) r := by
  rw [← h.preimage_symm, h.symm.preimage_sphere, symm_symm]

@[simp]
/-
**IsometryEquiv.image_closedBall** 是 Mathlib 中的一个定理，位于命名空间 `IsometryEquiv`。
形式化陈述：image_closedBall (h : α ≃ᵢ β) (x : α) (r : Real) : h '' Metric.closedBall 
x r = Metric.closedBall (h x) r
参数：h : α ≃ᵢ β；x : α；r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsometryEquiv.preimage_symm`：preimage_symm (h : α ≃ᵢ β) : preimage h.sym
m = image h
· 使用定理 `IsometryEquiv.preimage_closedBall`：preimage_closedBall (h : α ≃ᵢ β) (x :
 β) (r : Real) : h ⁻¹' Metric.closedBall x r = Metric.closedBall (h.symm x) r
· 使用定理 `IsometryEquiv.symm_symm`：symm_symm (h : α ≃ᵢ β) : h.symm.symm = h
-/
theorem image_closedBall (h : α ≃ᵢ β) (x : α) (r : ℝ) :
    h '' Metric.closedBall x r = Metric.closedBall (h x) r := by
  rw [← h.preimage_symm, h.symm.preimage_closedBall, symm_symm]

end PseudoMetricSpace

end IsometryEquiv

/-- An isometry induces an isometric isomorphism between the source space and the
range of the isometry. -/
@[simps! +simpRhs toEquiv apply]
/-
**Isometry.isometryEquivOnRange** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Isometry.isometryEquivOnRange [EMetricSpace α] [PseudoEMetricSpace β] {f :
 α -> β} (h : Isometry f) : α ≃ᵢ range f where isometry_toFun
参数：h : Isometry f。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Isometry.injective`：∀ {α : Type u} {β : Type v} [inst : EMetricSpace α] 
[inst_1 : PseudoEMetricSpace β] {f : α → β},   Isometry f → Function.Injective f

--- 原说明 ---
An isometry induces an isometric isomorphism between the source space and the
range of the isometry.
-/
def Isometry.isometryEquivOnRange [EMetricSpace α] [PseudoEMetricSpace β] {f : α → β}
    (h : Isometry f) : α ≃ᵢ range f where
  isometry_toFun := h
  toEquiv := Equiv.ofInjective f h.injective

open NNReal in
/-- Post-composition by an isometry does not change the Lipschitz-property of a function. -/
/-
**Isometry.lipschitzWith_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Isometry.lipschitzWith_iff {α β γ : Type*} [PseudoEMetricSpace α] [PseudoE
MetricSpace β] [PseudoEMetricSpace γ] {f : α -> β} {g : β -> γ} (K : Real>=0) (h
 : Isometry g) : LipschitzWith K (g ∘ f) ↔ LipschitzWith K f
参数：K : Real>=0；h : Isometry g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Isometry.edist_eq`：edist_eq (hf : Isometry f) (x y : α) : edist (f x) (f
 y) = edist x y
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Post-composition by an isometry does not change the Lipschitz-property of a func
tion.
-/
lemma Isometry.lipschitzWith_iff {α β γ : Type*} [PseudoEMetricSpace α] [PseudoEMetricSpace β]
    [PseudoEMetricSpace γ] {f : α → β} {g : β → γ} (K : ℝ≥0) (h : Isometry g) :
    LipschitzWith K (g ∘ f) ↔ LipschitzWith K f := by
  simp [LipschitzWith, h.edist_eq]

namespace IsometryClass

variable [PseudoEMetricSpace α] [PseudoEMetricSpace β] [EquivLike F α β] [IsometryClass F α β]

/-- Turn an element of a type `F` satisfying `EquivLike F α β` and `IsometryClass F α β` into
an actual `IsometryEquiv`. This is declared as the default coercion from `F` to `α ≃ᵢ β`. -/
@[coe]
/-
**IsometryClass.toIsometryEquiv** 是 Mathlib 中的一个定义，位于命名空间 `IsometryClass`。
形式化陈述：toIsometryEquiv (f : F) : α ≃ᵢ β
参数：f : F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn an element of a type `F` satisfying `EquivLike F α β` and `IsometryClass F 
α β` into
an actual `IsometryEquiv`. This is declared as the default coercion from `F` to 
`α ≃ᵢ β`.
-/
def toIsometryEquiv (f : F) : α ≃ᵢ β :=
  { (f : α ≃ β) with
    isometry_toFun := IsometryClass.isometry f }

@[simp]
/-
**IsometryClass.coe_coe** 是 Mathlib 中的一个定理，位于命名空间 `IsometryClass`。
形式化陈述：coe_coe (f : F) : ⇑(toIsometryEquiv f) = ⇑f
参数：f : F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_coe (f : F) : ⇑(toIsometryEquiv f) = ⇑f := rfl
/-
**IsometryClass.** 是 Mathlib 中的一个实例，位于命名空间 `IsometryClass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeOut F (α ≃ᵢ β) :=
  ⟨toIsometryEquiv⟩
/-
**IsometryClass.toIsometryEquiv_injective** 是 Mathlib 中的一个定理，位于命名空间 `IsometryCla
ss`。
形式化陈述：toIsometryEquiv_injective : Function.Injective ((↑) : F -> α ≃ᵢ β)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
-/
theorem toIsometryEquiv_injective : Function.Injective ((↑) : F → α ≃ᵢ β) :=
  fun _ _ e ↦ DFunLike.ext _ _ fun a ↦ DFunLike.congr_fun e a

end IsometryClass

