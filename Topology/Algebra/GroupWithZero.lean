/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.Group.Pi.Lemmas
public import Mathlib.Algebra.GroupWithZero.Units.Equiv
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Topological group with zero

In this file we define `ContinuousInv₀` to be a mixin typeclass a type with `Inv` and
`Zero` (e.g., a `GroupWithZero`) such that `fun x ↦ x⁻¹` is continuous at all nonzero points. Any
normed (semi)field has this property. Currently the only example of `ContinuousInv₀` in
`mathlib` which is not a normed field is the type `NNReal` (a.k.a. `ℝ≥0`) of nonnegative real
numbers.

Then we prove lemmas about continuity of `x ↦ x⁻¹` and `f / g` providing dot-style `*.inv₀` and
`*.div` operations on `Filter.Tendsto`, `ContinuousAt`, `ContinuousWithinAt`, `ContinuousOn`,
and `Continuous`. As a special case, we provide `*.div_const` operations that require only
`DivInvMonoid` and `ContinuousMul` instances.

All lemmas about `(⁻¹)` use `inv₀` in their names because lemmas without `₀` are used for
`IsTopologicalGroup`s. We also use `'` in the typeclass name `ContinuousInv₀` for the sake of
consistency of notation.

On a `GroupWithZero` with continuous multiplication, we also define left and right multiplication
as homeomorphisms.
-/

@[expose] public section
open Topology Filter Function

/-!
### A `DivInvMonoid` with continuous multiplication

If `G₀` is a `DivInvMonoid` with continuous `(*)`, then `(/y)` is continuous for any `y`. In this
section we prove lemmas that immediately follow from this fact providing `*.div_const` dot-style
operations on `Filter.Tendsto`, `ContinuousAt`, `ContinuousWithinAt`, `ContinuousOn`, and
`Continuous`.
-/


variable {α β G₀ : Type*}

section DivConst

variable [DivInvMonoid G₀] [TopologicalSpace G₀] [SeparatelyContinuousMul G₀]
  {f : α → G₀} {s : Set α} {l : Filter α}

/-
**Filter.Tendsto.div_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.div_const {x : G₀} (hf : Tendsto f l (𝓝 x)) (y : G₀) : Tend
sto (fun a => f a / y) l (𝓝 (x / y))
参数：hf : Tendsto f l (𝓝 x)；y : G₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Filter.Tendsto.mul_const`：Filter.Tendsto.mul_const {α : Type*} {f : α ->
 M} {x : Filter α} {a : M} (b : M) (hf : Tendsto f x (𝓝 a)) : Tendsto (f · * b) 
x (𝓝 (a * b))
-/
theorem Filter.Tendsto.div_const {x : G₀} (hf : Tendsto f l (𝓝 x)) (y : G₀) :
    Tendsto (fun a => f a / y) l (𝓝 (x / y)) := by
  simpa only [div_eq_mul_inv] using hf.mul_const _

variable [TopologicalSpace α]

nonrec theorem ContinuousAt.div_const {a : α} (hf : ContinuousAt f a) (y : G₀) :
    ContinuousAt (fun x => f x / y) a :=
  hf.div_const y

nonrec theorem ContinuousWithinAt.div_const {a} (hf : ContinuousWithinAt f s a) (y : G₀) :
    ContinuousWithinAt (fun x => f x / y) s a :=
  hf.div_const _
/-
**ContinuousOn.div_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.div_const (hf : ContinuousOn f s) (y : G₀) : ContinuousOn (fu
n x => f x / y) s
参数：hf : ContinuousOn f s；y : G₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `ContinuousOn.mul_const`：ContinuousOn.mul_const (hf : ContinuousOn f s) (
b : M) : ContinuousOn (f · * b) s
-/
theorem ContinuousOn.div_const (hf : ContinuousOn f s) (y : G₀) :
    ContinuousOn (fun x => f x / y) s := by
  simpa only [div_eq_mul_inv] using hf.mul_const _

@[continuity, fun_prop]
/-
**Continuous.div_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.div_const (hf : Continuous f) (y : G₀) : Continuous fun x => f 
x / y
参数：hf : Continuous f；y : G₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Continuous.mul_const`：Continuous.mul_const (hf : Continuous f) (b : M) :
 Continuous (f · * b)
-/
theorem Continuous.div_const (hf : Continuous f) (y : G₀) : Continuous fun x => f x / y := by
  simpa only [div_eq_mul_inv] using hf.mul_const _

end DivConst

/-- A type with `0` and `Inv` such that `fun x ↦ x⁻¹` is continuous at all nonzero points. Any
normed (semi)field has this property. -/
/-
**ContinuousInv** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(G : Type u) → [TopologicalSpace G] → [Inv G] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A type with `0` and `Inv` such that `fun x ↦ x⁻¹` is continuous at all nonzero p
oints. Any
normed (semi)field has this property.
-/
class ContinuousInv₀ (G₀ : Type*) [Zero G₀] [Inv G₀] [TopologicalSpace G₀] : Prop where
  /-- The map `fun x ↦ x⁻¹` is continuous at all nonzero points. -/
  continuousAt_inv₀ : ∀ ⦃x : G₀⦄, x ≠ 0 → ContinuousAt Inv.inv x

export ContinuousInv₀ (continuousAt_inv₀)

section Inv₀

variable [Zero G₀] [Inv G₀] [TopologicalSpace G₀] [ContinuousInv₀ G₀] {l : Filter α} {f : α → G₀}
  {s : Set α} {a : α}

/-!
### Continuity of `fun x ↦ x⁻¹` at a non-zero point

We define `ContinuousInv₀` to be a `GroupWithZero` such that the operation `x ↦ x⁻¹`
is continuous at all nonzero points. In this section we prove dot-style `*.inv₀` lemmas for
`Filter.Tendsto`, `ContinuousAt`, `ContinuousWithinAt`, `ContinuousOn`, and `Continuous`.
-/

/-
**tendsto_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_inv (a : G) : Tendsto Inv.inv (𝓝 a) (𝓝 a⁻¹)
参数：a : G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuousAt_inv`：continuousAt_inv {x : G} : ContinuousAt Inv.inv x

--- 原说明 ---
### Continuity of `fun x ↦ x⁻¹` at a non-zero point

We define `ContinuousInv₀` to be a `GroupWithZero` such that the operation `x ↦ 
x⁻¹`
is continuous at all nonzero points. In this section we prove dot-style `*.inv₀`
 lemmas for
`Filter.Tendsto`, `ContinuousAt`, `ContinuousWithinAt`, `ContinuousOn`, and `Con
tinuous`.
-/
theorem tendsto_inv₀ {x : G₀} (hx : x ≠ 0) : Tendsto Inv.inv (𝓝 x) (𝓝 x⁻¹) :=
  continuousAt_inv₀ hx
/-
**continuousOn_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousOn_inv {s : Set G} : ContinuousOn Inv.inv s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `ContinuousInv.continuous_inv`：∀ {G : Type u} {inst : TopologicalSpace G}
 {inst_1 : Inv G} [self : ContinuousInv G], Continuous fun a => a⁻¹
-/
theorem continuousOn_inv₀ : ContinuousOn (Inv.inv : G₀ → G₀) {0}ᶜ := fun _x hx =>
  (continuousAt_inv₀ hx).continuousWithinAt

/-- If a function converges to a nonzero value, its inverse converges to the inverse of this value.
We use the name `Filter.Tendsto.inv₀` as `Filter.Tendsto.inv` is already used in multiplicative
topological groups. -/
/-
**Filter.Tendsto.inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.inv {f : α -> G} {l : Filter α} {y : G} (h : Tendsto f l (𝓝
 y)) : Tendsto (fun x => (f x)⁻¹) l (𝓝 y⁻¹)
参数：h : Tendsto f l (𝓝 y)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用定理 `ContinuousInv.continuous_inv`：∀ {G : Type u} {inst : TopologicalSpace G}
 {inst_1 : Inv G} [self : ContinuousInv G], Continuous fun a => a⁻¹

--- 原说明 ---
If a function converges to a nonzero value, its inverse converges to the inverse
 of this value.
We use the name `Filter.Tendsto.inv₀` as `Filter.Tendsto.inv` is already used in
 multiplicative
topological groups.
-/
theorem Filter.Tendsto.inv₀ {a : G₀} (hf : Tendsto f l (𝓝 a)) (ha : a ≠ 0) :
    Tendsto (fun x => (f x)⁻¹) l (𝓝 a⁻¹) :=
  (tendsto_inv₀ ha).comp hf

variable [TopologicalSpace α]

@[to_fun (attr := fun_prop)]
nonrec theorem ContinuousWithinAt.inv₀ (hf : ContinuousWithinAt f s a) (ha : f a ≠ 0) :
    ContinuousWithinAt f⁻¹ s a :=
  hf.inv₀ ha

@[to_fun (attr := fun_prop)]
nonrec theorem ContinuousAt.inv₀ (hf : ContinuousAt f a) (ha : f a ≠ 0) :
    ContinuousAt f⁻¹ a :=
  hf.inv₀ ha

@[to_fun (attr := continuity, fun_prop)]
/-
**Continuous.inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.inv (hf : Continuous f) : Continuous f⁻¹
参数：hf : Continuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `ContinuousInv.continuous_inv`：∀ {G : Type u} {inst : TopologicalSpace G}
 {inst_1 : Inv G} [self : ContinuousInv G], Continuous fun a => a⁻¹
-/
theorem Continuous.inv₀ (hf : Continuous f) (h0 : ∀ x, f x ≠ 0) : Continuous f⁻¹ :=
  continuous_iff_continuousAt.2 fun x => (hf.tendsto x).inv₀ (h0 x)

@[to_fun (attr := fun_prop)]
/-
**ContinuousOn.inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.inv (hf : ContinuousOn f s) : ContinuousOn f⁻¹ s
参数：hf : ContinuousOn f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.inv`：∀ {G : Type u_1} {X : Type u_3} [inst : Topologi
calSpace X] [inst_1 : TopologicalSpace G] [inst_2 : Inv G]   [ContinuousInv G] {
f : X → G} {…
-/
theorem ContinuousOn.inv₀ (hf : ContinuousOn f s) (h0 : ∀ x ∈ s, f x ≠ 0) :
    ContinuousOn f⁻¹ s := fun x hx => (hf x hx).inv₀ (h0 x hx)

end Inv₀

section GroupWithZero

variable [GroupWithZero G₀] [TopologicalSpace G₀] [ContinuousInv₀ G₀]

/-- If `G₀` is a group with zero with topology such that `x ↦ x⁻¹` is continuous at all nonzero
points. Then the coercion `G₀ˣ → G₀` is a topological embedding. -/
/-
**Units.isEmbedding_val** 是 Mathlib 中的一个定理，位于命名空间 `Units`。
形式化陈述：∀ {G : Type w} [inst : Group G] [inst_1 : TopologicalSpace G] [ContinuousI
nv G], Topology.IsEmbedding Units.val
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.isEmbedding`：isEmbedding (h : X ≃ₜ Y) : IsEmbedding h

--- 原说明 ---
If `G₀` is a group with zero with topology such that `x ↦ x⁻¹` is continuous at 
all nonzero
points. Then the coercion `G₀ˣ → G₀` is a topological embedding.
-/
theorem Units.isEmbedding_val₀ : IsEmbedding (val : G₀ˣ → G₀) :=
  embedding_val_mk <| (continuousOn_inv₀ (G₀ := G₀)).mono fun _ ↦ IsUnit.ne_zero

/-- If a group with zero has continuous inversion, then its group of units is homeomorphic to
the set of nonzero elements. -/
/-
**unitsHomeomorphNeZero** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：unitsHomeomorphNeZero : G₀ˣ ≃ₜ {g : G₀ // g != 0}
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Units.isEmbedding_val₀`：Units.isEmbedding_val₀ : IsEmbedding (val : G₀ˣ 
-> G₀)

--- 原说明 ---
If a group with zero has continuous inversion, then its group of units is homeom
orphic to
the set of nonzero elements.
-/
noncomputable def unitsHomeomorphNeZero : G₀ˣ ≃ₜ {g : G₀ // g ≠ 0} :=
  Units.isEmbedding_val₀.toHomeomorph.trans <| show _ ≃ₜ {g | _} from .setCongr <|
    Set.ext fun x ↦ (Units.exists_iff_ne_zero (p := (· = x))).trans <| by simp

variable (G₀) in
/-- If a group with zero has continuous inversion, then the inversion map restricts to an
auto-homeomorphism on the set of nonzero elements. -/
/-
**Homeomorph.inv** 是 Mathlib 中的一个定义，位于命名空间 `Homeomorph`。
形式化陈述：(G : Type u_1) → [inst : TopologicalSpace G] → [inst_1 : InvolutiveInv G] 
→ [ContinuousInv G] → G ≃ₜ G
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a group with zero has continuous inversion, then the inversion map restricts 
to an
auto-homeomorphism on the set of nonzero elements.
-/
def Homeomorph.inv₀ : {g : G₀ // g ≠ 0} ≃ₜ {g : G₀ // g ≠ 0} where
  toFun g := ⟨g⁻¹, inv_ne_zero g.2⟩
  invFun g := ⟨g⁻¹, inv_ne_zero g.2⟩
  left_inv _ := by simp
  right_inv _ := by simp
  continuous_toFun := continuous_induced_rng.mpr continuousOn_inv₀.domRestrict
  continuous_invFun := continuous_induced_rng.mpr continuousOn_inv₀.domRestrict

end GroupWithZero

section NhdsInv

open scoped Pointwise

variable [GroupWithZero G₀] [TopologicalSpace G₀] [ContinuousInv₀ G₀] {x : G₀}

/-
**nhds_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhds_inv (a : G) : 𝓝 a⁻¹ = (𝓝 a)⁻¹
参数：a : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Homeomorph.map_nhds_eq`：map_nhds_eq (h : X ≃ₜ Y) (x : X) : map h (𝓝 x) =
 𝓝 (h x)
-/
lemma nhds_inv₀ (hx : x ≠ 0) : 𝓝 x⁻¹ = (𝓝 x)⁻¹ := by
  refine le_antisymm (inv_le_iff_le_inv.1 ?_) (tendsto_inv₀ hx)
  simpa only [inv_inv] using! tendsto_inv₀ (inv_ne_zero hx)
/-
**tendsto_inv_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_inv_iff {l : Filter α} {m : α -> G} {a : G} : Tendsto (fun x => (m
 x)⁻¹) l (𝓝 a⁻¹) ↔ Tendsto m l (𝓝 a)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `Filter.Tendsto.inv`：Filter.Tendsto.inv {f : α -> G} {l : Filter α} {y : 
G} (h : Tendsto f l (𝓝 y)) : Tendsto (fun x => (f x)⁻¹) l (𝓝 y⁻¹)
-/
lemma tendsto_inv_iff₀ {l : Filter α} {f : α → G₀} (hx : x ≠ 0) :
    Tendsto (fun x ↦ (f x)⁻¹) l (𝓝 x⁻¹) ↔ Tendsto f l (𝓝 x) := by
  simp only [nhds_inv₀ hx, ← Filter.comap_inv, tendsto_comap_iff, Function.comp_def, inv_inv]

end NhdsInv

/-!
### Continuity of division

If `G₀` is a `GroupWithZero` with `x ↦ x⁻¹` continuous at all nonzero points and `(*)`, then
division `(/)` is continuous at any point where the denominator is continuous.
-/

section Div

variable [GroupWithZero G₀] [TopologicalSpace G₀] [ContinuousInv₀ G₀] [ContinuousMul G₀]
  {f g : α → G₀}

/-
**Filter.Tendsto.div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.div {l : Filter α} {a b : G₀} (hf : Tendsto f l (𝓝 a)) (hg 
: Tendsto g l (𝓝 b)) (hy : b != 0) : Tendsto (f / g) l (𝓝 (a / b))
参数：hf : Tendsto f l (𝓝 a)；hg : Tendsto g l (𝓝 b)；hy : b != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Filter.Tendsto.mul`：Filter.Tendsto.mul {α : Type*} {f g : α -> M} {x : F
ilter α} {a b : M} (hf : Tendsto f x (𝓝 a)) (hg : Tendsto g x (𝓝 b)) : Tendsto (
fun x =>…
· 使用定理 `Filter.Tendsto.inv₀`：Filter.Tendsto.inv₀ {a : G₀} (hf : Tendsto f l (𝓝 a
)) (ha : a != 0) : Tendsto (fun x => (f x)⁻¹) l (𝓝 a⁻¹)
-/
theorem Filter.Tendsto.div {l : Filter α} {a b : G₀} (hf : Tendsto f l (𝓝 a))
    (hg : Tendsto g l (𝓝 b)) (hy : b ≠ 0) : Tendsto (f / g) l (𝓝 (a / b)) := by
  simpa only [div_eq_mul_inv] using! hf.mul (hg.inv₀ hy)

/-- If `f → a` and `g → b` along a nontrivial filter, valued in a Hausdorff
`GroupWithZero` with continuous multiplication and `ContinuousInv₀`, and `b ≠ 0`,
then `f / g → 1` if and only if `a = b`. -/
/-
**tendsto_div_nhds_one_iff_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_div_nhds_one_iff_eq {α : Type*} {l : Filter α} [l.NeBot] [T2Space 
G] {f g : α -> G} {a b : G} (hf : Tendsto f l (𝓝 a)) (hg : Tendsto g l (𝓝 b)) : 
Tendsto (fun x => f x / g x) l (𝓝 1) ↔ a = b
参数：hf : Tendsto f l (𝓝 a)；hg : Tendsto g l (𝓝 b)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_nhds_unique`：tendsto_nhds_unique [T2Space X] {f : Y -> X} {l : F
ilter Y} {a b : X} [NeBot l] (ha : Tendsto f l (𝓝 a)) (hb : Tendsto f l (𝓝 b)) :
 a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_mul_cancel`：div_mul_cancel (a b : G) : a / b * b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Filter.Tendsto.mul`：Filter.Tendsto.mul {α : Type*} {f g : α -> M} {x : F
ilter α} {a b : M} (hf : Tendsto f x (𝓝 a)) (hg : Tendsto g x (𝓝 b)) : Tendsto (
fun x =>…
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `div_self'`：div_self' (a : G) : a / a = 1
· 使用定理 `Filter.Tendsto.div'`：Filter.Tendsto.div' {f g : α -> G} {l : Filter α} {
a b : G} (hf : Tendsto f l (𝓝 a)) (hg : Tendsto g l (𝓝 b)) : Tendsto (fun x => f
 x / g x)…
· 使用定理 `IsTopologicalGroup.to_continuousDiv`：∀ {G : Type u} [inst : TopologicalS
pace G] [inst_1 : Group G] [IsTopologicalGroup G], ContinuousDiv G

--- 原说明 ---
If `f → a` and `g → b` along a nontrivial filter, valued in a Hausdorff
`GroupWithZero` with continuous multiplication and `ContinuousInv₀`, and `b ≠ 0`
,
then `f / g → 1` if and only if `a = b`.
-/
theorem tendsto_div_nhds_one_iff_eq₀
    {l : Filter α} [l.NeBot] [T2Space G₀] {a b : G₀}
    (hf : Tendsto f l (𝓝 a)) (hg : Tendsto g l (𝓝 b)) (hb : b ≠ 0) :
    Tendsto (fun x ↦ f x / g x) l (𝓝 1) ↔ a = b :=
  ⟨fun hfg => (div_eq_one_iff_eq hb).mp (tendsto_nhds_unique (hf.div hg hb) hfg),
   fun hab => (div_eq_one_iff_eq hb).mpr hab ▸ hf.div hg hb⟩

alias ⟨eq_of_tendsto_div_nhds_one₀, _⟩ := tendsto_div_nhds_one_iff_eq₀
/-
**Filter.tendsto_mul_iff_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.tendsto_mul_iff_of_ne_zero [T1Space G₀] {f g : α -> G₀} {l : Filter
 α} {x y : G₀} (hg : Tendsto g l (𝓝 y)) (hy : y != 0) : Tendsto (fun n => f n * 
g n) l (𝓝 <| x * y) ↔ Tendsto f l (𝓝 x)
参数：hg : Tendsto g l (𝓝 y)；hy : y != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_div_cancel_right₀`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀] [ins
t_1 : Div M₀] [MulDivCancelClass M₀] (a : M₀) {b : M₀},   b ≠ 0 → a * b / b = a
· 使用定理 `GroupWithZero.toMulDivCancelClass`：∀ {G₀ : Type u} [inst : GroupWithZero
 G₀], MulDivCancelClass G₀
· 使用定理 `Filter.Tendsto.congr'`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {
l₁ : Filter α} {l₂ : Filter β},   f₁ =ᶠ[l₁] f₂ → Filter.Tendsto f₁ l₁ l₂ → Filte
r.Tendsto f…
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.Tendsto.eventually_ne`：Filter.Tendsto.eventually_ne {X} [Topologi
calSpace Y] [T1Space Y] {g : X -> Y} {l : Filter X} {b₁ b₂ : Y} (hg : Tendsto g 
l (𝓝 b₁)) (hb : b₁…
· 使用定理 `Filter.Tendsto.div`：Filter.Tendsto.div {l : Filter α} {a b : G₀} (hf : T
endsto f l (𝓝 a)) (hg : Tendsto g l (𝓝 b)) (hy : b != 0) : Tendsto (f / g) l (𝓝 
(a / b))
· 使用定理 `Filter.Tendsto.mul`：Filter.Tendsto.mul {α : Type*} {f g : α -> M} {x : F
ilter α} {a b : M} (hf : Tendsto f x (𝓝 a)) (hg : Tendsto g x (𝓝 b)) : Tendsto (
fun x =>…
-/
theorem Filter.tendsto_mul_iff_of_ne_zero [T1Space G₀] {f g : α → G₀} {l : Filter α} {x y : G₀}
    (hg : Tendsto g l (𝓝 y)) (hy : y ≠ 0) :
    Tendsto (fun n => f n * g n) l (𝓝 <| x * y) ↔ Tendsto f l (𝓝 x) := by
  refine ⟨fun hfg => ?_, fun hf => hf.mul hg⟩
  rw [← mul_div_cancel_right₀ x hy]
  refine Tendsto.congr' ?_ (hfg.div hg hy)
  exact (hg.eventually_ne hy).mono fun n hn => mul_div_cancel_right₀ _ hn

variable [TopologicalSpace α] [TopologicalSpace β] {s : Set α} {a : α}

nonrec theorem ContinuousWithinAt.div (hf : ContinuousWithinAt f s a)
    (hg : ContinuousWithinAt g s a) (h₀ : g a ≠ 0) : ContinuousWithinAt (f / g) s a :=
  hf.div hg h₀
/-
**ContinuousOn.div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.div (hf : ContinuousOn f s) (hg : ContinuousOn g s) (h₀ : for
all x in s, g x != 0) : ContinuousOn (f / g) s
参数：hf : ContinuousOn f s；hg : ContinuousOn g s；h₀ : forall x in s, g x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.div`：∀ {α : Type u_1} {G₀ : Type u_3} [inst : GroupWi
thZero G₀] [inst_1 : TopologicalSpace G₀] [ContinuousInv₀ G₀]   [ContinuousMul G
₀] {f g : α …
-/
theorem ContinuousOn.div (hf : ContinuousOn f s) (hg : ContinuousOn g s) (h₀ : ∀ x ∈ s, g x ≠ 0) :
    ContinuousOn (f / g) s := fun x hx => (hf x hx).div (hg x hx) (h₀ x hx)

/-- Continuity at a point of the result of dividing two functions continuous at that point, where
the denominator is nonzero. -/
nonrec theorem ContinuousAt.div (hf : ContinuousAt f a) (hg : ContinuousAt g a) (h₀ : g a ≠ 0) :
    ContinuousAt (f / g) a :=
  hf.div hg h₀

@[continuity]
/-
**Continuous.div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.div (hf : Continuous f) (hg : Continuous g) (h₀ : forall x, g x
 != 0) : Continuous (f / g)
参数：hf : Continuous f；hg : Continuous g；h₀ : forall x, g x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Continuous.mul`：Continuous.mul (hf : Continuous f) (hg : Continuous g) :
 Continuous (f * g)
· 使用定理 `Continuous.inv₀`：Continuous.inv₀ (hf : Continuous f) (h0 : forall x, f x
 != 0) : Continuous f⁻¹
-/
theorem Continuous.div (hf : Continuous f) (hg : Continuous g) (h₀ : ∀ x, g x ≠ 0) :
    Continuous (f / g) := by simpa only [div_eq_mul_inv] using! hf.mul (hg.inv₀ h₀)
/-
**continuousOn_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousOn_div : ContinuousOn (fun p : G₀ × G₀ => p.1 / p.2) { p | p.2 !
= 0 }
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.div`：ContinuousOn.div (hf : ContinuousOn f s) (hg : Continu
ousOn g s) (h₀ : forall x in s, g x != 0) : ContinuousOn (f / g) s
· 使用定理 `continuousOn_fst`：continuousOn_fst {s : Set (α × β)} : ContinuousOn Prod
.fst s
· 使用定理 `continuousOn_snd`：continuousOn_snd {s : Set (α × β)} : ContinuousOn Prod
.snd s
-/
theorem continuousOn_div : ContinuousOn (fun p : G₀ × G₀ => p.1 / p.2) { p | p.2 ≠ 0 } :=
  continuousOn_fst.div continuousOn_snd fun _ => id

@[fun_prop]
/-
**Continuous.div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.div (hf : Continuous f) (hg : Continuous g) (h₀ : forall x, g x
 != 0) : Continuous (f / g)
参数：hf : Continuous f；hg : Continuous g；h₀ : forall x, g x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Continuous.mul`：Continuous.mul (hf : Continuous f) (hg : Continuous g) :
 Continuous (f * g)
· 使用定理 `Continuous.inv₀`：Continuous.inv₀ (hf : Continuous f) (h0 : forall x, f x
 != 0) : Continuous f⁻¹
-/
theorem Continuous.div₀ (hf : Continuous f) (hg : Continuous g) (h₀ : ∀ x, g x ≠ 0) :
    Continuous (fun x => f x / g x) := by
  simpa only [div_eq_mul_inv] using! hf.mul (hg.inv₀ h₀)

@[fun_prop]
/-
**ContinuousAt.div** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousAt`。
形式化陈述：∀ {α : Type u_1} {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : Topol
ogicalSpace G₀] [ContinuousInv₀ G₀]   [ContinuousMul G₀] {f g : α → G₀} [inst_4 
: TopologicalSpace α] {a : α},   ContinuousAt f a → ContinuousAt g a → g a ≠ 0 →
 ContinuousAt (f / g) a
参数：f / g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.div`：Filter.Tendsto.div {l : Filter α} {a b : G₀} (hf : T
endsto f l (𝓝 a)) (hg : Tendsto g l (𝓝 b)) (hy : b != 0) : Tendsto (f / g) l (𝓝 
(a / b))
-/
theorem ContinuousAt.div₀ (hf : ContinuousAt f a) (hg : ContinuousAt g a) (h₀ : g a ≠ 0) :
    ContinuousAt (fun x => f x / g x) a := ContinuousAt.div hf hg h₀

@[fun_prop]
/-
**ContinuousOn.div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.div (hf : ContinuousOn f s) (hg : ContinuousOn g s) (h₀ : for
all x in s, g x != 0) : ContinuousOn (f / g) s
参数：hf : ContinuousOn f s；hg : ContinuousOn g s；h₀ : forall x in s, g x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.div`：∀ {α : Type u_1} {G₀ : Type u_3} [inst : GroupWi
thZero G₀] [inst_1 : TopologicalSpace G₀] [ContinuousInv₀ G₀]   [ContinuousMul G
₀] {f g : α …
-/
theorem ContinuousOn.div₀ (hf : ContinuousOn f s) (hg : ContinuousOn g s) (h₀ : ∀ x ∈ s, g x ≠ 0) :
    ContinuousOn (fun x => f x / g x) s := ContinuousOn.div hf hg h₀

/-- The function `f x / g x` is discontinuous when `g x = 0`. However, under appropriate
conditions, `h x (f x / g x)` is still continuous.  The condition is that if `g a = 0` then `h x y`
must tend to `h a 0` when `x` tends to `a`, with no information about `y`. This is represented by
the `⊤` filter.  Note: `tendsto_prod_top_iff` characterizes this convergence in uniform spaces.  See
also `Filter.prod_top` and `Filter.mem_prod_top`. -/
/-
**ContinuousAt.comp_div_cases** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousAt.comp_div_cases {f g : α -> G₀} (h : α -> G₀ -> β) (hf : Conti
nuousAt f a) (hg : ContinuousAt g a) (hh : g a != 0 -> ContinuousAt ↿h (a, f a /
 g a)) (h2h : g a = 0 -> Tendsto ↿h (𝓝 a ×ˢ ⊤) (𝓝 (h a 0))) : ContinuousAt (fun 
x => h x (f x / g x)) a
参数：h : α -> G₀ -> β；hf : ContinuousAt f a；hg : ContinuousAt g a；hh : g a != 0 ->
 ContinuousAt ↿h (a, f a / g a)；h2h : g a = 0 -> Tendsto ↿h (𝓝 a ×ˢ ⊤) (𝓝 (h a 0
))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousAt.eq_1`：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSp
ace X] [inst_1 : TopologicalSpace Y] (f : X → Y) (x : X),   ContinuousAt f x = F
ilter.T…
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Filter.Tendsto.prodMk`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f
 : Filter α} {g : Filter β} {h : Filter γ} {m₁ : α → β} {m₂ : α → γ},   Filter.T
endsto m₁ f…
· 使用定理 `ContinuousAt.tendsto`：ContinuousAt.tendsto (h : ContinuousAt f x) : Tend
sto f (𝓝 x) (𝓝 (f x))
· 使用定理 `continuousAt_id`：continuousAt_id : ContinuousAt id x
· 使用定理 `Filter.tendsto_top`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l : Fil
ter α}, Filter.Tendsto f l ⊤
· 使用定理 `ContinuousAt.comp'`：ContinuousAt.comp' {g : Y -> Z} {x : X} (hg : Contin
uousAt g (f x)) (hf : ContinuousAt f x) : ContinuousAt (fun x => g (f x)) x
· 使用定理 `ContinuousAt.prodMk`：ContinuousAt.prodMk {f : X -> Y} {g : X -> Z} {x : 
X} (hf : ContinuousAt f x) (hg : ContinuousAt g x) : ContinuousAt (fun x => (f x
, g x)) x
· 使用定理 `continuousAt_id'`：continuousAt_id' (y) : ContinuousAt (fun x : X => x) y
· 使用定理 `ContinuousAt.div₀`：ContinuousAt.div₀ (hf : ContinuousAt f a) (hg : Conti
nuousAt g a) (h₀ : g a != 0) : ContinuousAt (fun x => f x / g x) a

--- 原说明 ---
The function `f x / g x` is discontinuous when `g x = 0`. However, under appropr
iate
conditions, `h x (f x / g x)` is still continuous.  The condition is that if `g 
a = 0` then `h x y`
must tend to `h a 0` when `x` tends to `a`, with no information about `y`. This 
is represented by
the `⊤` filter.  Note: `tendsto_prod_top_iff` characterizes this convergence in 
uniform spaces.  See
also `Filter.prod_top` and `Filter.mem_prod_top`.
-/
theorem ContinuousAt.comp_div_cases {f g : α → G₀} (h : α → G₀ → β) (hf : ContinuousAt f a)
    (hg : ContinuousAt g a) (hh : g a ≠ 0 → ContinuousAt ↿h (a, f a / g a))
    (h2h : g a = 0 → Tendsto ↿h (𝓝 a ×ˢ ⊤) (𝓝 (h a 0))) :
    ContinuousAt (fun x => h x (f x / g x)) a := by
  change ContinuousAt (↿h ∘ fun x => (x, f x / g x)) a
  by_cases hga : g a = 0
  · rw [ContinuousAt]
    simp_rw [comp_apply, hga, div_zero]
    exact (h2h hga).comp (continuousAt_id.tendsto.prodMk tendsto_top)
  · fun_prop

/-- `h x (f x / g x)` is continuous under certain conditions, even if the denominator is sometimes
  `0`. See docstring of `ContinuousAt.comp_div_cases`. -/
/-
**Continuous.comp_div_cases** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.comp_div_cases {f g : α -> G₀} (h : α -> G₀ -> β) (hf : Continu
ous f) (hg : Continuous g) (hh : forall a, g a != 0 -> ContinuousAt ↿h (a, f a /
 g a)) (h2h : forall a, g a = 0 -> Tendsto ↿h (𝓝 a ×ˢ ⊤) (𝓝 (h a 0))) : Continuo
us fun x => h x (f x / g x)
参数：h : α -> G₀ -> β；hf : Continuous f；hg : Continuous g；hh : forall a, g a != 0 
-> ContinuousAt ↿h (a, f a / g a)；h2h : forall a, g a = 0 -> Tendsto ↿h (𝓝 a ×ˢ 
⊤) (𝓝 (h a 0))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用定理 `ContinuousAt.comp_div_cases`：ContinuousAt.comp_div_cases {f g : α -> G₀}
 (h : α -> G₀ -> β) (hf : ContinuousAt f a) (hg : ContinuousAt g a) (hh : g a !=
 0 -> ContinuousA…
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x

--- 原说明 ---
`h x (f x / g x)` is continuous under certain conditions, even if the denominato
r is sometimes
  `0`. See docstring of `ContinuousAt.comp_div_cases`.
-/
theorem Continuous.comp_div_cases {f g : α → G₀} (h : α → G₀ → β) (hf : Continuous f)
    (hg : Continuous g) (hh : ∀ a, g a ≠ 0 → ContinuousAt ↿h (a, f a / g a))
    (h2h : ∀ a, g a = 0 → Tendsto ↿h (𝓝 a ×ˢ ⊤) (𝓝 (h a 0))) :
    Continuous fun x => h x (f x / g x) :=
  continuous_iff_continuousAt.mpr fun a =>
    hf.continuousAt.comp_div_cases _ hg.continuousAt (hh a) (h2h a)

end Div

/-! ### Left and right multiplication as homeomorphisms -/


namespace Homeomorph

variable [TopologicalSpace α] [GroupWithZero α] [SeparatelyContinuousMul α]

/-- Left multiplication by a nonzero element in a `GroupWithZero` with continuous multiplication
is a homeomorphism of the underlying type. -/
/-
**Homeomorph.mulLeft** 是 Mathlib 中的一个定义，位于命名空间 `Homeomorph`。
形式化陈述：{G : Type w} → [inst : TopologicalSpace G] → [inst_1 : Group G] → [Separat
elyContinuousMul G] → G → G ≃ₜ G
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Left multiplication by a nonzero element in a `GroupWithZero` with continuous mu
ltiplication
is a homeomorphism of the underlying type.
-/
protected def mulLeft₀ (c : α) (hc : c ≠ 0) : α ≃ₜ α :=
  { Equiv.mulLeft₀ c hc with
    continuous_toFun := continuous_const_mul _
    continuous_invFun := continuous_const_mul _ }

/-- Right multiplication by a nonzero element in a `GroupWithZero` with continuous multiplication
is a homeomorphism of the underlying type. -/
/-
**Homeomorph.mulRight** 是 Mathlib 中的一个定义，位于命名空间 `Homeomorph`。
形式化陈述：{G : Type w} → [inst : TopologicalSpace G] → [inst_1 : Group G] → [Separat
elyContinuousMul G] → G → G ≃ₜ G
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Right multiplication by a nonzero element in a `GroupWithZero` with continuous m
ultiplication
is a homeomorphism of the underlying type.
-/
protected def mulRight₀ (c : α) (hc : c ≠ 0) : α ≃ₜ α :=
  { Equiv.mulRight₀ c hc with
    continuous_toFun := continuous_mul_const _
    continuous_invFun := continuous_mul_const _ }

@[simp]
/-
**Homeomorph.coe_mulLeft** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Homeomorph.coe_mulLeft (a : G) : ⇑(Homeomorph.mulLeft a) = (a * ·)
参数：a : G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mulLeft₀ (c : α) (hc : c ≠ 0) : ⇑(Homeomorph.mulLeft₀ c hc) = (c * ·) :=
  rfl

@[simp]
/-
**Homeomorph.mulLeft** 是 Mathlib 中的一个定义，位于命名空间 `Homeomorph`。
形式化陈述：{G : Type w} → [inst : TopologicalSpace G] → [inst_1 : Group G] → [Separat
elyContinuousMul G] → G → G ≃ₜ G
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mulLeft₀_symm_apply (c : α) (hc : c ≠ 0) :
    ((Homeomorph.mulLeft₀ c hc).symm : α → α) = (c⁻¹ * ·) :=
  rfl

@[simp]
/-
**Homeomorph.coe_mulRight** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Homeomorph.coe_mulRight (a : G) : ⇑(Homeomorph.mulRight a) = (· * a)
参数：a : G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mulRight₀ (c : α) (hc : c ≠ 0) : ⇑(Homeomorph.mulRight₀ c hc) = (· * c) :=
  rfl

@[simp]
/-
**Homeomorph.mulRight** 是 Mathlib 中的一个定义，位于命名空间 `Homeomorph`。
形式化陈述：{G : Type w} → [inst : TopologicalSpace G] → [inst_1 : Group G] → [Separat
elyContinuousMul G] → G → G ≃ₜ G
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mulRight₀_symm_apply (c : α) (hc : c ≠ 0) :
    ((Homeomorph.mulRight₀ c hc).symm : α → α) = (· * c⁻¹) :=
  rfl

end Homeomorph

section map_comap

variable [TopologicalSpace G₀] [GroupWithZero G₀] [SeparatelyContinuousMul G₀] {a : G₀}

/-
**map_mul_left_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_mul_left_nhds (x y : G) : map (x * ·) (𝓝 y) = 𝓝 (x * y)
参数：x y : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.map_nhds_eq`：map_nhds_eq (h : X ≃ₜ Y) (x : X) : map h (𝓝 x) =
 𝓝 (h x)
· 使用定理 `instSeparatelyContinuousMulOfContinuousMul`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Mul M] [ContinuousMul M], SeparatelyContinuousMul M
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
-/
theorem map_mul_left_nhds₀ (ha : a ≠ 0) (b : G₀) : map (a * ·) (𝓝 b) = 𝓝 (a * b) :=
  (Homeomorph.mulLeft₀ a ha).map_nhds_eq b
/-
**map_mul_left_nhds_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_mul_left_nhds_one (x : G) : map (x * ·) (𝓝 1) = 𝓝 x
参数：x : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_mul_left_nhds`：map_mul_left_nhds (x y : G) : map (x * ·) (𝓝 y) = 𝓝 (
x * y)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_mul_left_nhds_one₀ (ha : a ≠ 0) : map (a * ·) (𝓝 1) = 𝓝 (a) := by
  rw [map_mul_left_nhds₀ ha, mul_one]
/-
**map_mul_right_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_mul_right_nhds (x y : G) : map (· * x) (𝓝 y) = 𝓝 (y * x)
参数：x y : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.map_nhds_eq`：map_nhds_eq (h : X ≃ₜ Y) (x : X) : map h (𝓝 x) =
 𝓝 (h x)
· 使用定理 `instSeparatelyContinuousMulOfContinuousMul`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Mul M] [ContinuousMul M], SeparatelyContinuousMul M
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
-/
theorem map_mul_right_nhds₀ (ha : a ≠ 0) (b : G₀) : map (· * a) (𝓝 b) = 𝓝 (b * a) :=
  (Homeomorph.mulRight₀ a ha).map_nhds_eq b
/-
**map_mul_right_nhds_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_mul_right_nhds_one (x : G) : map (· * x) (𝓝 1) = 𝓝 x
参数：x : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_mul_right_nhds`：map_mul_right_nhds (x y : G) : map (· * x) (𝓝 y) = 𝓝
 (y * x)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_mul_right_nhds_one₀ (ha : a ≠ 0) : map (· * a) (𝓝 1) = 𝓝 (a) := by
  rw [map_mul_right_nhds₀ ha, one_mul]
/-
**nhds_translation_mul_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhds_translation_mul_inv (x : G) : comap (· * x⁻¹) (𝓝 1) = 𝓝 x
参数：x : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instSeparatelyContinuousMulOfContinuousMul`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Mul M] [ContinuousMul M], SeparatelyContinuousMul M
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `Homeomorph.comap_nhds_eq`：comap_nhds_eq (h : X ≃ₜ Y) (y : Y) : comap h (
𝓝 y) = 𝓝 (h.symm y)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem nhds_translation_mul_inv₀ (ha : a ≠ 0) : comap (· * a⁻¹) (𝓝 1) = 𝓝 a :=
  ((Homeomorph.mulRight₀ a ha).symm.comap_nhds_eq 1).trans <| by simp

/-- If a group with zero has continuous multiplication and `fun x ↦ x⁻¹` is continuous at one,
then it is continuous at any unit. -/
/-
**ContinuousInv** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(G : Type u) → [TopologicalSpace G] → [Inv G] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a group with zero has continuous multiplication and `fun x ↦ x⁻¹` is continuo
us at one,
then it is continuous at any unit.
-/
theorem ContinuousInv₀.of_nhds_one (h : Tendsto Inv.inv (𝓝 (1 : G₀)) (𝓝 1)) :
    ContinuousInv₀ G₀ where
  continuousAt_inv₀ x hx := by
    have hx' := inv_ne_zero hx
    rw [ContinuousAt, ← map_mul_left_nhds_one₀ hx, ← nhds_translation_mul_inv₀ hx',
      tendsto_map'_iff, tendsto_comap_iff]
    simpa only [Function.comp_def, mul_inv_rev, mul_inv_cancel_right₀ hx']

end map_comap

section ZPow

variable [GroupWithZero G₀] [TopologicalSpace G₀] [ContinuousInv₀ G₀] [ContinuousMul G₀]

/-
**continuousAt_zpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousAt_zpow (x : G) (z : Int) : ContinuousAt (fun x => x ^ z) x
参数：x : G；z : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `continuous_zpow`：∀ {G : Type w} [inst : TopologicalSpace G] [inst_1 : Gr
oup G] [IsTopologicalGroup G] (z : ℤ), Continuous fun a => a ^ z
-/
theorem continuousAt_zpow₀ (x : G₀) (m : ℤ) (h : x ≠ 0 ∨ 0 ≤ m) :
    ContinuousAt (fun x => x ^ m) x := by
  rcases m with m | m
  · simpa only [Int.ofNat_eq_natCast, zpow_natCast] using continuousAt_pow x m
  · simp only [zpow_negSucc]
    have hx : x ≠ 0 := h.resolve_right (Int.negSucc_lt_zero m).not_ge
    exact (continuousAt_pow x (m + 1)).inv₀ (pow_ne_zero _ hx)
/-
**continuousOn_zpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousOn_zpow {s : Set G} (z : Int) : ContinuousOn (fun x => x ^ z) s
参数：z : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `continuous_zpow`：∀ {G : Type w} [inst : TopologicalSpace G] [inst_1 : Gr
oup G] [IsTopologicalGroup G] (z : ℤ), Continuous fun a => a ^ z
-/
theorem continuousOn_zpow₀ (m : ℤ) : ContinuousOn (fun x : G₀ => x ^ m) {0}ᶜ := fun _x hx =>
  (continuousAt_zpow₀ _ _ (Or.inl hx)).continuousWithinAt
/-
**Filter.Tendsto.zpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.zpow {α} {l : Filter α} {f : α -> G} {x : G} (hf : Tendsto 
f l (𝓝 x)) (z : Int) : Tendsto (fun x => f x ^ z) l (𝓝 (x ^ z))
参数：hf : Tendsto f l (𝓝 x)；z : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `ContinuousAt.tendsto`：ContinuousAt.tendsto (h : ContinuousAt f x) : Tend
sto f (𝓝 x) (𝓝 (f x))
· 使用定理 `continuousAt_zpow`：continuousAt_zpow (x : G) (z : Int) : ContinuousAt (f
un x => x ^ z) x
-/
theorem Filter.Tendsto.zpow₀ {f : α → G₀} {l : Filter α} {a : G₀} (hf : Tendsto f l (𝓝 a)) (m : ℤ)
    (h : a ≠ 0 ∨ 0 ≤ m) : Tendsto (fun x => f x ^ m) l (𝓝 (a ^ m)) :=
  (continuousAt_zpow₀ _ m h).tendsto.comp hf

variable {X : Type*} [TopologicalSpace X] {a : X} {s : Set X} {f : X → G₀}

@[fun_prop]
nonrec theorem ContinuousAt.zpow₀ (hf : ContinuousAt f a) (m : ℤ) (h : f a ≠ 0 ∨ 0 ≤ m) :
    ContinuousAt (fun x => f x ^ m) a :=
  hf.zpow₀ m h

nonrec theorem ContinuousWithinAt.zpow₀ (hf : ContinuousWithinAt f s a) (m : ℤ)
    (h : f a ≠ 0 ∨ 0 ≤ m) : ContinuousWithinAt (fun x => f x ^ m) s a :=
  hf.zpow₀ m h

@[fun_prop]
/-
**ContinuousOn.zpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.zpow {f : α -> G} {s : Set α} (hf : ContinuousOn f s) (z : In
t) : ContinuousOn (f ^ z) s
参数：hf : ContinuousOn f s；z : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.zpow`：ContinuousWithinAt.zpow {f : α -> G} {x : α} {s
 : Set α} (hf : ContinuousWithinAt f s x) (z : Int) : ContinuousWithinAt (f ^ z)
 s x
-/
theorem ContinuousOn.zpow₀ (hf : ContinuousOn f s) (m : ℤ) (h : ∀ a ∈ s, f a ≠ 0 ∨ 0 ≤ m) :
    ContinuousOn (fun x => f x ^ m) s := fun a ha => (hf a ha).zpow₀ m (h a ha)

@[continuity, fun_prop]
/-
**Continuous.zpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.zpow {f : α -> G} (h : Continuous f) (z : Int) : Continuous (f 
^ z)
参数：h : Continuous f；z : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `continuous_zpow`：∀ {G : Type w} [inst : TopologicalSpace G] [inst_1 : Gr
oup G] [IsTopologicalGroup G] (z : ℤ), Continuous fun a => a ^ z
-/
theorem Continuous.zpow₀ (hf : Continuous f) (m : ℤ) (h0 : ∀ a, f a ≠ 0 ∨ 0 ≤ m) :
    Continuous fun x => f x ^ m :=
  continuous_iff_continuousAt.2 fun x => (hf.tendsto x).zpow₀ m (h0 x)

end ZPow

