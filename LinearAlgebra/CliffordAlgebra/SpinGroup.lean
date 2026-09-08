/-
Copyright (c) 2022 Jiale Miao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiale Miao, Utensil Song, Eric Wieser
-/
module

public import Mathlib.Algebra.Ring.Action.ConjAct
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.Algebra.Star.Unitary
public import Mathlib.LinearAlgebra.CliffordAlgebra.Star
public import Mathlib.LinearAlgebra.CliffordAlgebra.Even
public import Mathlib.LinearAlgebra.CliffordAlgebra.Inversion

/-!
# The Pin group and the Spin group

In this file we define `lipschitzGroup`, `pinGroup` and `spinGroup` and show they form a group.

## Main definitions

* `lipschitzGroup`: the Lipschitz group with a quadratic form.
* `pinGroup`: the Pin group defined as the infimum of `lipschitzGroup` and `unitary`.
* `spinGroup`: the Spin group defined as the infimum of `pinGroup` and `CliffordAlgebra.even`.

## Implementation Notes

The definition of the Lipschitz group
$\{ x \in \mathop{\mathcal{C}\ell} | x \text{ is invertible and } x v x^{-1} ∈ V \}$ is given by:

* [fulton2004], Chapter 20
* https://en.wikipedia.org/wiki/Clifford_algebra#Lipschitz_group

But they presumably form a group only in finite dimensions. So we define `lipschitzGroup` with
closure of all the invertible elements in the form of `ι Q m`, and we show this definition is
at least as large as the other definition (See `lipschitzGroup.conjAct_smul_range_ι` and
`lipschitzGroup.involute_act_ι_mem_range_ι`).
The reverse statement presumably is true only in finite dimensions.

Here are some discussions about the latent ambiguity of definition :
https://mathoverflow.net/q/427881/172242 and https://mathoverflow.net/q/251288/172242

## TODO

Try to show the reverse statement is true in finite dimensions.
-/

@[expose] public section

variable {R : Type*} [CommRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {Q : QuadraticForm R M}

section Pin

open CliffordAlgebra MulAction

open scoped Pointwise

/-- `lipschitzGroup` is the subgroup closure of all the invertible elements in the form of `ι Q m`
where `ι` is the canonical linear map `M →ₗ[R] CliffordAlgebra Q`. -/
/-
**lipschitzGroup** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：lipschitzGroup (Q : QuadraticForm R M) : Subgroup (CliffordAlgebra Q)ˣ
参数：Q : QuadraticForm R M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`lipschitzGroup` is the subgroup closure of all the invertible elements in the f
orm of `ι Q m`
where `ι` is the canonical linear map `M →ₗ[R] CliffordAlgebra Q`.
-/
def lipschitzGroup (Q : QuadraticForm R M) : Subgroup (CliffordAlgebra Q)ˣ :=
  Subgroup.closure ((↑) ⁻¹' Set.range (ι Q) : Set (CliffordAlgebra Q)ˣ)

namespace lipschitzGroup

/-- The conjugation action by elements of the Lipschitz group keeps vectors as vectors. -/
/-
**lipschitzGroup.conjAct_smul_** 是 Mathlib 中的一个定理，位于命名空间 `lipschitzGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The conjugation action by elements of the Lipschitz group keeps vectors as vecto
rs.
-/
theorem conjAct_smul_ι_mem_range_ι {x : (CliffordAlgebra Q)ˣ} (hx : x ∈ lipschitzGroup Q)
    [Invertible (2 : R)] (m : M) :
    ConjAct.toConjAct x • ι Q m ∈ LinearMap.range (ι Q) := by
  unfold lipschitzGroup at hx
  rw [ConjAct.units_smul_def, ConjAct.ofConjAct_toConjAct]
  induction hx using Subgroup.closure_induction'' generalizing m with
  | mem x hx =>
    obtain ⟨a, ha⟩ := hx
    let := x.invertible
    let : Invertible (ι Q a) := by rwa [ha]
    let : Invertible (Q a) := invertibleOfInvertibleι Q a
    simp_rw [← invOf_units x, ← ha, ι_mul_ι_mul_invOf_ι, LinearMap.mem_range_self]
  | inv_mem x hx =>
    obtain ⟨a, ha⟩ := hx
    let := x.invertible
    let : Invertible (ι Q a) := by rwa [ha]
    let : Invertible (Q a) := invertibleOfInvertibleι Q a
    simp_rw [← invOf_units x, inv_inv, ← ha, invOf_ι_mul_ι_mul_ι, LinearMap.mem_range_self]
  | one => simp_rw [inv_one, Units.val_one, one_mul, mul_one, LinearMap.mem_range_self]
  | mul y z _ _ hy hz =>
    simp_rw [mul_inv_rev, Units.val_mul]
    suffices ↑y * (↑z * ι Q m * ↑z⁻¹) * ↑y⁻¹ ∈ _ by
      simpa only [mul_assoc] using this
    obtain ⟨z', hz'⟩ := hz m
    obtain ⟨y', hy'⟩ := hy z'
    simp_rw [← hz', ← hy', LinearMap.mem_range_self]

/-- This is another version of `lipschitzGroup.conjAct_smul_ι_mem_range_ι` which uses `involute`. -/
/-
**lipschitzGroup.involute_act_** 是 Mathlib 中的一个定理，位于命名空间 `lipschitzGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is another version of `lipschitzGroup.conjAct_smul_ι_mem_range_ι` which use
s `involute`.
-/
theorem involute_act_ι_mem_range_ι [Invertible (2 : R)]
    {x : (CliffordAlgebra Q)ˣ} (hx : x ∈ lipschitzGroup Q) (b : M) :
      involute (Q := Q) ↑x * ι Q b * ↑x⁻¹ ∈ LinearMap.range (ι Q) := by
  unfold lipschitzGroup at hx
  induction hx using Subgroup.closure_induction'' generalizing b with
  | mem x hx =>
    obtain ⟨a, ha⟩ := hx
    let := x.invertible
    let : Invertible (ι Q a) := by rwa [ha]
    let : Invertible (Q a) := invertibleOfInvertibleι Q a
    simp_rw [← invOf_units x, ← ha, involute_ι, neg_mul, ι_mul_ι_mul_invOf_ι Q a b, ← map_neg,
      LinearMap.mem_range_self]
  | inv_mem x hx =>
    obtain ⟨a, ha⟩ := hx
    let := x.invertible
    let : Invertible (ι Q a) := by rwa [ha]
    let : Invertible (Q a) := invertibleOfInvertibleι Q a
    let := invertibleNeg (ι Q a)
    let := Invertible.map involute (ι Q a)
    simp_rw [← invOf_units x, inv_inv, ← ha, map_invOf, involute_ι, invOf_neg, neg_mul,
      invOf_ι_mul_ι_mul_ι, ← map_neg, LinearMap.mem_range_self]
  | one => simp_rw [inv_one, Units.val_one, map_one, one_mul, mul_one, LinearMap.mem_range_self]
  | mul y z _ _ hy hz =>
    simp_rw [mul_inv_rev, Units.val_mul, map_mul]
    suffices involute (Q := Q) ↑y * (involute (Q := Q) ↑z * ι Q b * ↑z⁻¹) * ↑y⁻¹ ∈ _ by
      simpa only [mul_assoc] using this
    obtain ⟨z', hz'⟩ := hz b
    obtain ⟨y', hy'⟩ := hy z'
    simp_rw [← hz', ← hy', LinearMap.mem_range_self]

/-- If x is in `lipschitzGroup Q`, then `(ι Q).range` is closed under twisted conjugation.
The reverse statement presumably is true only in finite dimensions. -/
/-
**lipschitzGroup.conjAct_smul_range_** 是 Mathlib 中的一个定理，位于命名空间 `lipschitzGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If x is in `lipschitzGroup Q`, then `(ι Q).range` is closed under twisted conjug
ation.
The reverse statement presumably is true only in finite dimensions.
-/
theorem conjAct_smul_range_ι {x : (CliffordAlgebra Q)ˣ} (hx : x ∈ lipschitzGroup Q)
    [Invertible (2 : R)] :
    ConjAct.toConjAct x • LinearMap.range (ι Q) = LinearMap.range (ι Q) := by
  suffices ∀ x ∈ lipschitzGroup Q,
      ConjAct.toConjAct x • LinearMap.range (ι Q) ≤ LinearMap.range (ι Q) by
    apply le_antisymm
    · exact this _ hx
    · have := smul_mono_right (ConjAct.toConjAct x) <| this _ (inv_mem hx)
      refine Eq.trans_le ?_ this
      simp only [map_inv, smul_inv_smul]
  intro x hx
  rw [Submodule.pointwise_smul_def, Submodule.map_le_iff_le_comap]
  rintro _ ⟨m, rfl⟩
  exact conjAct_smul_ι_mem_range_ι hx _
/-
**lipschitzGroup.coe_mem_iff_mem** 是 Mathlib 中的一个定理，位于命名空间 `lipschitzGroup`。
形式化陈述：coe_mem_iff_mem {x : (CliffordAlgebra Q)ˣ} : ↑x in (lipschitzGroup Q).toSu
bmonoid.map (Units.coeHom <| CliffordAlgebra Q) ↔ x in lipschitzGroup Q
参数：CliffordAlgebra Q。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_eq_right`：∀ {α : Sort u_1} {p : α → Prop} {a' : α}, (∃ a, p a ∧ a
 = a') ↔ p a'
-/
theorem coe_mem_iff_mem {x : (CliffordAlgebra Q)ˣ} :
    ↑x ∈ (lipschitzGroup Q).toSubmonoid.map (Units.coeHom <| CliffordAlgebra Q) ↔
    x ∈ lipschitzGroup Q := by
  simp only [Submonoid.mem_map, Subgroup.mem_toSubmonoid, Units.coeHom_apply]
  norm_cast
  exact exists_eq_right

end lipschitzGroup

/-- `pinGroup Q` is defined as the infimum of `lipschitzGroup Q` and `unitary (CliffordAlgebra Q)`.
See `mem_iff`. -/
/-
**pinGroup** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：pinGroup (Q : QuadraticForm R M) : Submonoid (CliffordAlgebra Q)
参数：Q : QuadraticForm R M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`pinGroup Q` is defined as the infimum of `lipschitzGroup Q` and `unitary (Cliff
ordAlgebra Q)`.
See `mem_iff`.
-/
def pinGroup (Q : QuadraticForm R M) : Submonoid (CliffordAlgebra Q) :=
  (lipschitzGroup Q).toSubmonoid.map (Units.coeHom <| CliffordAlgebra Q) ⊓ unitary _

namespace pinGroup

/-- An element is in `pinGroup Q` if and only if it is in `lipschitzGroup Q` and `unitary`. -/
/-
**pinGroup.mem_iff** 是 Mathlib 中的一个定理，位于命名空间 `pinGroup`。
形式化陈述：mem_iff {x : CliffordAlgebra Q} : x in pinGroup Q ↔ x in (lipschitzGroup Q
).toSubmonoid.map (Units.coeHom <| CliffordAlgebra Q) ∧ x in unitary (CliffordAl
gebra Q)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
An element is in `pinGroup Q` if and only if it is in `lipschitzGroup Q` and `un
itary`.
-/
theorem mem_iff {x : CliffordAlgebra Q} :
    x ∈ pinGroup Q ↔
      x ∈ (lipschitzGroup Q).toSubmonoid.map (Units.coeHom <| CliffordAlgebra Q) ∧
        x ∈ unitary (CliffordAlgebra Q) :=
  Iff.rfl
/-
**pinGroup.mem_lipschitzGroup** 是 Mathlib 中的一个定理，位于命名空间 `pinGroup`。
形式化陈述：mem_lipschitzGroup {x : CliffordAlgebra Q} (hx : x in pinGroup Q) : x in (
lipschitzGroup Q).toSubmonoid.map (Units.coeHom <| CliffordAlgebra Q)
参数：hx : x in pinGroup Q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem mem_lipschitzGroup {x : CliffordAlgebra Q} (hx : x ∈ pinGroup Q) :
    x ∈ (lipschitzGroup Q).toSubmonoid.map (Units.coeHom <| CliffordAlgebra Q) :=
  hx.1
/-
**pinGroup.mem_unitary** 是 Mathlib 中的一个定理，位于命名空间 `pinGroup`。
形式化陈述：mem_unitary {x : CliffordAlgebra Q} (hx : x in pinGroup Q) : x in unitary 
(CliffordAlgebra Q)
参数：hx : x in pinGroup Q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem mem_unitary {x : CliffordAlgebra Q} (hx : x ∈ pinGroup Q) :
    x ∈ unitary (CliffordAlgebra Q) :=
  hx.2
/-
**pinGroup.units_mem_iff** 是 Mathlib 中的一个定理，位于命名空间 `pinGroup`。
形式化陈述：units_mem_iff {x : (CliffordAlgebra Q)ˣ} : ↑x in pinGroup Q ↔ x in lipschi
tzGroup Q ∧ ↑x in unitary (CliffordAlgebra Q)
参数：CliffordAlgebra Q。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pinGroup.mem_iff`：mem_iff {x : CliffordAlgebra Q} : x in pinGroup Q ↔ x 
in (lipschitzGroup Q).toSubmonoid.map (Units.coeHom <| CliffordAlgebra Q) ∧ x in
 unita…
· 使用定理 `lipschitzGroup.coe_mem_iff_mem`：coe_mem_iff_mem {x : (CliffordAlgebra Q)
ˣ} : ↑x in (lipschitzGroup Q).toSubmonoid.map (Units.coeHom <| CliffordAlgebra Q
) ↔ x in lipschitzGr…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem units_mem_iff {x : (CliffordAlgebra Q)ˣ} :
    ↑x ∈ pinGroup Q ↔ x ∈ lipschitzGroup Q ∧ ↑x ∈ unitary (CliffordAlgebra Q) := by
  rw [mem_iff, lipschitzGroup.coe_mem_iff_mem]
/-
**pinGroup.units_mem_lipschitzGroup** 是 Mathlib 中的一个定理，位于命名空间 `pinGroup`。
形式化陈述：units_mem_lipschitzGroup {x : (CliffordAlgebra Q)ˣ} (hx : ↑x in pinGroup Q
) : x in lipschitzGroup Q
参数：CliffordAlgebra Q；hx : ↑x in pinGroup Q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `pinGroup.units_mem_iff`：units_mem_iff {x : (CliffordAlgebra Q)ˣ} : ↑x in
 pinGroup Q ↔ x in lipschitzGroup Q ∧ ↑x in unitary (CliffordAlgebra Q)
-/
theorem units_mem_lipschitzGroup {x : (CliffordAlgebra Q)ˣ} (hx : ↑x ∈ pinGroup Q) :
    x ∈ lipschitzGroup Q :=
  (units_mem_iff.1 hx).1

/-- The conjugation action by elements of the spin group keeps vectors as vectors. -/
/-
**pinGroup.conjAct_smul_** 是 Mathlib 中的一个定理，位于命名空间 `pinGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The conjugation action by elements of the spin group keeps vectors as vectors.
-/
theorem conjAct_smul_ι_mem_range_ι {x : (CliffordAlgebra Q)ˣ} (hx : ↑x ∈ pinGroup Q)
    [Invertible (2 : R)] (y : M) : ConjAct.toConjAct x • ι Q y ∈ LinearMap.range (ι Q) :=
  lipschitzGroup.conjAct_smul_ι_mem_range_ι (units_mem_lipschitzGroup hx) y

/-- This is another version of `conjAct_smul_ι_mem_range_ι` which uses `involute`. -/
/-
**pinGroup.involute_act_** 是 Mathlib 中的一个定理，位于命名空间 `pinGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is another version of `conjAct_smul_ι_mem_range_ι` which uses `involute`.
-/
theorem involute_act_ι_mem_range_ι {x : (CliffordAlgebra Q)ˣ} (hx : ↑x ∈ pinGroup Q)
    [Invertible (2 : R)] (y : M) : involute (Q := Q) ↑x * ι Q y * ↑x⁻¹ ∈ LinearMap.range (ι Q) :=
  lipschitzGroup.involute_act_ι_mem_range_ι (units_mem_lipschitzGroup hx) y

/-- If x is in `pinGroup Q`, then `(ι Q).range` is closed under twisted conjugation. The reverse
statement presumably being true only in finite dimensions. -/
/-
**pinGroup.conjAct_smul_range_** 是 Mathlib 中的一个定理，位于命名空间 `pinGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If x is in `pinGroup Q`, then `(ι Q).range` is closed under twisted conjugation.
 The reverse
statement presumably being true only in finite dimensions.
-/
theorem conjAct_smul_range_ι {x : (CliffordAlgebra Q)ˣ} (hx : ↑x ∈ pinGroup Q)
    [Invertible (2 : R)] : ConjAct.toConjAct x • LinearMap.range (ι Q) = LinearMap.range (ι Q) :=
  lipschitzGroup.conjAct_smul_range_ι (units_mem_lipschitzGroup hx)

@[simp]
/-
**pinGroup.star_mul_self_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `pinGroup`。
形式化陈述：star_mul_self_of_mem {x : CliffordAlgebra Q} (hx : x in pinGroup Q) : star
 x * x = 1
参数：hx : x in pinGroup Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem star_mul_self_of_mem {x : CliffordAlgebra Q} (hx : x ∈ pinGroup Q) : star x * x = 1 :=
  hx.2.1

@[simp]
/-
**pinGroup.mul_star_self_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `pinGroup`。
形式化陈述：mul_star_self_of_mem {x : CliffordAlgebra Q} (hx : x in pinGroup Q) : x * 
star x = 1
参数：hx : x in pinGroup Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem mul_star_self_of_mem {x : CliffordAlgebra Q} (hx : x ∈ pinGroup Q) : x * star x = 1 :=
  hx.2.2

/-- See `star_mem_iff` for both directions. -/
/-
**pinGroup.star_mem** 是 Mathlib 中的一个定理，位于命名空间 `pinGroup`。
形式化陈述：star_mem {x : CliffordAlgebra Q} (hx : x in pinGroup Q) : star x in pinGro
up Q
参数：hx : x in pinGroup Q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pinGroup.mem_iff`：mem_iff {x : CliffordAlgebra Q} : x in pinGroup Q ↔ x 
in (lipschitzGroup Q).toSubmonoid.map (Units.coeHom <| CliffordAlgebra Q) ∧ x in
 unita…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Units.val_inj`：val_inj {a b : αˣ} : (a : α) = b ↔ a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `inv_mul_cancel_left`：inv_mul_cancel_left (a b : G) : a⁻¹ * (a * b) = b
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `SubgroupClass.toInvMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4)} 
{inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   Inv
MemClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Unitary.star_mem`：star_mem {U : R} (hU : U in unitary R) : star U in uni
tary R
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
See `star_mem_iff` for both directions.
-/
theorem star_mem {x : CliffordAlgebra Q} (hx : x ∈ pinGroup Q) : star x ∈ pinGroup Q := by
  rw [mem_iff] at hx ⊢
  refine ⟨?_, Unitary.star_mem hx.2⟩
  rcases hx with ⟨⟨y, hy₁, hy₂⟩, _hx₂, hx₃⟩
  simp only [Subgroup.coe_toSubmonoid, SetLike.mem_coe] at hy₁
  simp only [Units.coeHom_apply] at hy₂
  simp only [Submonoid.mem_map, Subgroup.mem_toSubmonoid, Units.coeHom_apply]
  refine ⟨star y, ?_, by simp only [hy₂, Units.coe_star]⟩
  rw [← hy₂] at hx₃
  have hy₃ : y * star y = 1 := by
    rw [← Units.val_inj]
    simp only [hx₃, Units.val_mul, Units.coe_star, Units.val_one]
  apply_fun fun x => y⁻¹ * x at hy₃
  simp only [inv_mul_cancel_left, mul_one] at hy₃
  simp only [hy₃, hy₁, inv_mem_iff]

/-- An element is in `pinGroup Q` if and only if `star x` is in `pinGroup Q`.
See `star_mem` for only one direction. -/
@[simp]
/-
**pinGroup.star_mem_iff** 是 Mathlib 中的一个定理，位于命名空间 `pinGroup`。
形式化陈述：star_mem_iff {x : CliffordAlgebra Q} : star x in pinGroup Q ↔ x in pinGrou
p Q
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r
· 使用定理 `pinGroup.star_mem`：star_mem {x : CliffordAlgebra Q} (hx : x in pinGroup 
Q) : star x in pinGroup Q

--- 原说明 ---
An element is in `pinGroup Q` if and only if `star x` is in `pinGroup Q`.
See `star_mem` for only one direction.
-/
theorem star_mem_iff {x : CliffordAlgebra Q} : star x ∈ pinGroup Q ↔ x ∈ pinGroup Q := by
  refine ⟨?_, star_mem⟩
  intro hx
  convert! star_mem hx
  exact (star_star x).symm
/-
**pinGroup.** 是 Mathlib 中的一个实例，位于命名空间 `pinGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Star (pinGroup Q) where
  star x := ⟨star x, star_mem x.prop⟩

@[simp, norm_cast]
/-
**pinGroup.coe_star** 是 Mathlib 中的一个定理，位于命名空间 `pinGroup`。
形式化陈述：coe_star {x : pinGroup Q} : ↑(star x) = (star x : CliffordAlgebra Q)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_star {x : pinGroup Q} : ↑(star x) = (star x : CliffordAlgebra Q) :=
  rfl
/-
**pinGroup.coe_star_mul_self** 是 Mathlib 中的一个定理，位于命名空间 `pinGroup`。
形式化陈述：coe_star_mul_self (x : pinGroup Q) : (star x : CliffordAlgebra Q) * x = 1
参数：x : pinGroup Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `pinGroup.star_mul_self_of_mem`：star_mul_self_of_mem {x : CliffordAlgebra
 Q} (hx : x in pinGroup Q) : star x * x = 1
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
theorem coe_star_mul_self (x : pinGroup Q) : (star x : CliffordAlgebra Q) * x = 1 :=
  star_mul_self_of_mem x.prop
/-
**pinGroup.coe_mul_star_self** 是 Mathlib 中的一个定理，位于命名空间 `pinGroup`。
形式化陈述：coe_mul_star_self (x : pinGroup Q) : (x : CliffordAlgebra Q) * star x = 1
参数：x : pinGroup Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `pinGroup.mul_star_self_of_mem`：mul_star_self_of_mem {x : CliffordAlgebra
 Q} (hx : x in pinGroup Q) : x * star x = 1
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
theorem coe_mul_star_self (x : pinGroup Q) : (x : CliffordAlgebra Q) * star x = 1 :=
  mul_star_self_of_mem x.prop

@[simp]
/-
**pinGroup.star_mul_self** 是 Mathlib 中的一个定理，位于命名空间 `pinGroup`。
形式化陈述：star_mul_self (x : pinGroup Q) : star x * x = 1
参数：x : pinGroup Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `pinGroup.coe_star_mul_self`：coe_star_mul_self (x : pinGroup Q) : (star x
 : CliffordAlgebra Q) * x = 1
-/
theorem star_mul_self (x : pinGroup Q) : star x * x = 1 :=
  Subtype.ext <| coe_star_mul_self x

@[simp]
/-
**pinGroup.mul_star_self** 是 Mathlib 中的一个定理，位于命名空间 `pinGroup`。
形式化陈述：mul_star_self (x : pinGroup Q) : x * star x = 1
参数：x : pinGroup Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `pinGroup.coe_mul_star_self`：coe_mul_star_self (x : pinGroup Q) : (x : Cl
iffordAlgebra Q) * star x = 1
-/
theorem mul_star_self (x : pinGroup Q) : x * star x = 1 :=
  Subtype.ext <| coe_mul_star_self x

/-- `pinGroup Q` forms a group where the inverse is `star`. -/
/-
**pinGroup.** 是 Mathlib 中的一个实例，位于命名空间 `pinGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`pinGroup Q` forms a group where the inverse is `star`.
-/
instance : Group (pinGroup Q) where
  inv := star
  inv_mul_cancel := star_mul_self
/-
**pinGroup.** 是 Mathlib 中的一个实例，位于命名空间 `pinGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : StarMul (pinGroup Q) where
  star_involutive _ := Subtype.ext <| star_involutive _
  star_mul _ _ := Subtype.ext <| star_mul _ _
/-
**pinGroup.** 是 Mathlib 中的一个实例，位于命名空间 `pinGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (pinGroup Q) :=
  ⟨1⟩
/-
**pinGroup.star_eq_inv** 是 Mathlib 中的一个定理，位于命名空间 `pinGroup`。
形式化陈述：star_eq_inv (x : pinGroup Q) : star x = x⁻¹
参数：x : pinGroup Q。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem star_eq_inv (x : pinGroup Q) : star x = x⁻¹ :=
  rfl
/-
**pinGroup.star_eq_inv'** 是 Mathlib 中的一个定理，位于命名空间 `pinGroup`。
形式化陈述：star_eq_inv' : (star : pinGroup Q -> pinGroup Q) = Inv.inv
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem star_eq_inv' : (star : pinGroup Q → pinGroup Q) = Inv.inv :=
  rfl

/-- The elements in `pinGroup Q` embed into (CliffordAlgebra Q)ˣ. -/
@[simps]
/-
**pinGroup.toUnits** 是 Mathlib 中的一个定义，位于命名空间 `pinGroup`。
形式化陈述：toUnits : pinGroup Q ->* (CliffordAlgebra Q)ˣ where toFun x
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `pinGroup.coe_mul_star_self`：coe_mul_star_self (x : pinGroup Q) : (x : Cl
iffordAlgebra Q) * star x = 1
· 使用定理 `pinGroup.coe_star_mul_self`：coe_star_mul_self (x : pinGroup Q) : (star x
 : CliffordAlgebra Q) * x = 1

--- 原说明 ---
The elements in `pinGroup Q` embed into (CliffordAlgebra Q)ˣ.
-/
def toUnits : pinGroup Q →* (CliffordAlgebra Q)ˣ where
  toFun x := ⟨x, ↑x⁻¹, coe_mul_star_self x, coe_star_mul_self x⟩
  map_one' := Units.ext rfl
  map_mul' _x _y := Units.ext rfl
/-
**pinGroup.toUnits_injective** 是 Mathlib 中的一个定理，位于命名空间 `pinGroup`。
形式化陈述：toUnits_injective : Function.Injective (toUnits : pinGroup Q -> (CliffordA
lgebra Q)ˣ)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Units.ext_iff`：∀ {α : Type u} [inst : Monoid α] {u v : αˣ}, u = v ↔ ↑u =
 ↑v
-/
theorem toUnits_injective : Function.Injective (toUnits : pinGroup Q → (CliffordAlgebra Q)ˣ) :=
  fun _x _y h => Subtype.ext <| Units.ext_iff.mp h

end pinGroup

end Pin

section Spin

open CliffordAlgebra MulAction

open scoped Pointwise

/-- `spinGroup Q` is defined as the infimum of `pinGroup Q` and `CliffordAlgebra.even Q`.
See `mem_iff`. -/
/-
**spinGroup** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：spinGroup (Q : QuadraticForm R M) : Submonoid (CliffordAlgebra Q)
参数：Q : QuadraticForm R M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`spinGroup Q` is defined as the infimum of `pinGroup Q` and `CliffordAlgebra.eve
n Q`.
See `mem_iff`.
-/
def spinGroup (Q : QuadraticForm R M) : Submonoid (CliffordAlgebra Q) :=
  pinGroup Q ⊓ (CliffordAlgebra.even Q).toSubring.toSubmonoid

namespace spinGroup

/-- An element is in `spinGroup Q` if and only if it is in `pinGroup Q` and `even Q`. -/
/-
**spinGroup.mem_iff** 是 Mathlib 中的一个定理，位于命名空间 `spinGroup`。
形式化陈述：mem_iff {x : CliffordAlgebra Q} : x in spinGroup Q ↔ x in pinGroup Q ∧ x i
n even Q
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
An element is in `spinGroup Q` if and only if it is in `pinGroup Q` and `even Q`
.
-/
theorem mem_iff {x : CliffordAlgebra Q} : x ∈ spinGroup Q ↔ x ∈ pinGroup Q ∧ x ∈ even Q :=
  Iff.rfl
/-
**spinGroup.mem_pin** 是 Mathlib 中的一个定理，位于命名空间 `spinGroup`。
形式化陈述：mem_pin {x : CliffordAlgebra Q} (hx : x in spinGroup Q) : x in pinGroup Q
参数：hx : x in spinGroup Q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem mem_pin {x : CliffordAlgebra Q} (hx : x ∈ spinGroup Q) : x ∈ pinGroup Q :=
  hx.1
/-
**spinGroup.mem_even** 是 Mathlib 中的一个定理，位于命名空间 `spinGroup`。
形式化陈述：mem_even {x : CliffordAlgebra Q} (hx : x in spinGroup Q) : x in even Q
参数：hx : x in spinGroup Q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem mem_even {x : CliffordAlgebra Q} (hx : x ∈ spinGroup Q) : x ∈ even Q :=
  hx.2
/-
**spinGroup.units_mem_lipschitzGroup** 是 Mathlib 中的一个定理，位于命名空间 `spinGroup`。
形式化陈述：units_mem_lipschitzGroup {x : (CliffordAlgebra Q)ˣ} (hx : ↑x in spinGroup 
Q) : x in lipschitzGroup Q
参数：CliffordAlgebra Q；hx : ↑x in spinGroup Q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `pinGroup.units_mem_lipschitzGroup`：units_mem_lipschitzGroup {x : (Cliffo
rdAlgebra Q)ˣ} (hx : ↑x in pinGroup Q) : x in lipschitzGroup Q
· 使用定理 `spinGroup.mem_pin`：mem_pin {x : CliffordAlgebra Q} (hx : x in spinGroup 
Q) : x in pinGroup Q
-/
theorem units_mem_lipschitzGroup {x : (CliffordAlgebra Q)ˣ} (hx : ↑x ∈ spinGroup Q) :
    x ∈ lipschitzGroup Q :=
  pinGroup.units_mem_lipschitzGroup (mem_pin hx)

/-- If x is in `spinGroup Q`, then `involute x` is equal to x. -/
/-
**spinGroup.involute_eq** 是 Mathlib 中的一个定理，位于命名空间 `spinGroup`。
形式化陈述：involute_eq {x : CliffordAlgebra Q} (hx : x in spinGroup Q) : involute x =
 x
参数：hx : x in spinGroup Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CliffordAlgebra.involute_eq_of_mem_even`：involute_eq_of_mem_even {x : Cl
iffordAlgebra Q} (h : x in evenOdd Q 0) : involute x = x
· 使用定理 `spinGroup.mem_even`：mem_even {x : CliffordAlgebra Q} (hx : x in spinGrou
p Q) : x in even Q

--- 原说明 ---
If x is in `spinGroup Q`, then `involute x` is equal to x.
-/
theorem involute_eq {x : CliffordAlgebra Q} (hx : x ∈ spinGroup Q) : involute x = x :=
  involute_eq_of_mem_even (mem_even hx)
/-
**spinGroup.units_involute_act_eq_conjAct** 是 Mathlib 中的一个定理，位于命名空间 `spinGroup`。
形式化陈述：units_involute_act_eq_conjAct {x : (CliffordAlgebra Q)ˣ} (hx : ↑x in spinG
roup Q) (y : M) : involute (Q
参数：CliffordAlgebra Q；hx : ↑x in spinGroup Q；y : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `spinGroup.involute_eq`：involute_eq {x : CliffordAlgebra Q} (hx : x in sp
inGroup Q) : involute x = x
· 使用定理 `ConjAct.units_smul_def`：units_smul_def (g : ConjAct Mˣ) (h : M) : g • h 
= ofConjAct g * h * ↑(ofConjAct g)⁻¹
· 使用定理 `ConjAct.ofConjAct_toConjAct`：ofConjAct_toConjAct (x : G) : ofConjAct (to
ConjAct x) = x
-/
theorem units_involute_act_eq_conjAct {x : (CliffordAlgebra Q)ˣ} (hx : ↑x ∈ spinGroup Q) (y : M) :
    involute (Q := Q) ↑x * ι Q y * ↑x⁻¹ = ConjAct.toConjAct x • (ι Q y) := by
  rw [involute_eq hx, @ConjAct.units_smul_def, @ConjAct.ofConjAct_toConjAct]

/-- The conjugation action by elements of the spin group keeps vectors as vectors. -/
/-
**spinGroup.conjAct_smul_** 是 Mathlib 中的一个定理，位于命名空间 `spinGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The conjugation action by elements of the spin group keeps vectors as vectors.
-/
theorem conjAct_smul_ι_mem_range_ι {x : (CliffordAlgebra Q)ˣ} (hx : ↑x ∈ spinGroup Q)
    [Invertible (2 : R)] (y : M) : ConjAct.toConjAct x • ι Q y ∈ LinearMap.range (ι Q) :=
  lipschitzGroup.conjAct_smul_ι_mem_range_ι (units_mem_lipschitzGroup hx) y

/-- This is another version of `conjAct_smul_ι_mem_range_ι` which uses `involute`. -/
/-
**spinGroup.involute_act_** 是 Mathlib 中的一个定理，位于命名空间 `spinGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is another version of `conjAct_smul_ι_mem_range_ι` which uses `involute`.
-/
theorem involute_act_ι_mem_range_ι {x : (CliffordAlgebra Q)ˣ} (hx : ↑x ∈ spinGroup Q)
    [Invertible (2 : R)] (y : M) : involute (Q := Q) ↑x * ι Q y * ↑x⁻¹ ∈ LinearMap.range (ι Q) :=
  lipschitzGroup.involute_act_ι_mem_range_ι (units_mem_lipschitzGroup hx) y

/- If x is in `spinGroup Q`, then `(ι Q).range` is closed under twisted conjugation. The reverse
statement presumably being true only in finite dimensions. -/
/-
**spinGroup.conjAct_smul_range_** 是 Mathlib 中的一个定理，位于命名空间 `spinGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If x is in `spinGroup Q`, then `(ι Q).range` is closed under twisted conjugation
. The reverse
statement presumably being true only in finite dimensions.
-/
theorem conjAct_smul_range_ι {x : (CliffordAlgebra Q)ˣ} (hx : ↑x ∈ spinGroup Q)
    [Invertible (2 : R)] : ConjAct.toConjAct x • LinearMap.range (ι Q) = LinearMap.range (ι Q) :=
  lipschitzGroup.conjAct_smul_range_ι (units_mem_lipschitzGroup hx)

@[simp]
/-
**spinGroup.star_mul_self_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `spinGroup`。
形式化陈述：star_mul_self_of_mem {x : CliffordAlgebra Q} (hx : x in spinGroup Q) : sta
r x * x = 1
参数：hx : x in spinGroup Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem star_mul_self_of_mem {x : CliffordAlgebra Q} (hx : x ∈ spinGroup Q) : star x * x = 1 :=
  hx.1.2.1

@[simp]
/-
**spinGroup.mul_star_self_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `spinGroup`。
形式化陈述：mul_star_self_of_mem {x : CliffordAlgebra Q} (hx : x in spinGroup Q) : x *
 star x = 1
参数：hx : x in spinGroup Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem mul_star_self_of_mem {x : CliffordAlgebra Q} (hx : x ∈ spinGroup Q) : x * star x = 1 :=
  hx.1.2.2

/-- See `star_mem_iff` for both directions. -/
/-
**spinGroup.star_mem** 是 Mathlib 中的一个定理，位于命名空间 `spinGroup`。
形式化陈述：star_mem {x : CliffordAlgebra Q} (hx : x in spinGroup Q) : star x in spinG
roup Q
参数：hx : x in spinGroup Q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `spinGroup.mem_iff`：mem_iff {x : CliffordAlgebra Q} : x in spinGroup Q ↔ 
x in pinGroup Q ∧ x in even Q
· 使用定理 `pinGroup.star_mem`：star_mem {x : CliffordAlgebra Q} (hx : x in pinGroup 
Q) : star x in pinGroup Q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True

--- 原说明 ---
See `star_mem_iff` for both directions.
-/
theorem star_mem {x : CliffordAlgebra Q} (hx : x ∈ spinGroup Q) : star x ∈ spinGroup Q := by
  rw [mem_iff] at hx ⊢
  obtain ⟨hx₁, hx₂⟩ := hx
  refine ⟨pinGroup.star_mem hx₁, ?_⟩
  dsimp only [CliffordAlgebra.even] at hx₂ ⊢
  simp only [Submodule.mem_toSubalgebra] at hx₂ ⊢
  simp only [star_def, reverse_mem_evenOdd_iff, involute_mem_evenOdd_iff, hx₂]

/-- An element is in `spinGroup Q` if and only if `star x` is in `spinGroup Q`.
See `star_mem` for only one direction.
-/
@[simp]
/-
**spinGroup.star_mem_iff** 是 Mathlib 中的一个定理，位于命名空间 `spinGroup`。
形式化陈述：star_mem_iff {x : CliffordAlgebra Q} : star x in spinGroup Q ↔ x in spinGr
oup Q
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r
· 使用定理 `spinGroup.star_mem`：star_mem {x : CliffordAlgebra Q} (hx : x in spinGrou
p Q) : star x in spinGroup Q

--- 原说明 ---
An element is in `spinGroup Q` if and only if `star x` is in `spinGroup Q`.
See `star_mem` for only one direction.
-/
theorem star_mem_iff {x : CliffordAlgebra Q} : star x ∈ spinGroup Q ↔ x ∈ spinGroup Q := by
  refine ⟨?_, star_mem⟩
  intro hx
  convert! star_mem hx
  exact (star_star x).symm
/-
**spinGroup.** 是 Mathlib 中的一个实例，位于命名空间 `spinGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Star (spinGroup Q) where
  star x := ⟨star x, star_mem x.prop⟩

@[simp, norm_cast]
/-
**spinGroup.coe_star** 是 Mathlib 中的一个定理，位于命名空间 `spinGroup`。
形式化陈述：coe_star {x : spinGroup Q} : ↑(star x) = (star x : CliffordAlgebra Q)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_star {x : spinGroup Q} : ↑(star x) = (star x : CliffordAlgebra Q) :=
  rfl
/-
**spinGroup.coe_star_mul_self** 是 Mathlib 中的一个定理，位于命名空间 `spinGroup`。
形式化陈述：coe_star_mul_self (x : spinGroup Q) : (star x : CliffordAlgebra Q) * x = 1
参数：x : spinGroup Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `spinGroup.star_mul_self_of_mem`：star_mul_self_of_mem {x : CliffordAlgebr
a Q} (hx : x in spinGroup Q) : star x * x = 1
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
theorem coe_star_mul_self (x : spinGroup Q) : (star x : CliffordAlgebra Q) * x = 1 :=
  star_mul_self_of_mem x.prop
/-
**spinGroup.coe_mul_star_self** 是 Mathlib 中的一个定理，位于命名空间 `spinGroup`。
形式化陈述：coe_mul_star_self (x : spinGroup Q) : (x : CliffordAlgebra Q) * star x = 1
参数：x : spinGroup Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `spinGroup.mul_star_self_of_mem`：mul_star_self_of_mem {x : CliffordAlgebr
a Q} (hx : x in spinGroup Q) : x * star x = 1
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
theorem coe_mul_star_self (x : spinGroup Q) : (x : CliffordAlgebra Q) * star x = 1 :=
  mul_star_self_of_mem x.prop

@[simp]
/-
**spinGroup.star_mul_self** 是 Mathlib 中的一个定理，位于命名空间 `spinGroup`。
形式化陈述：star_mul_self (x : spinGroup Q) : star x * x = 1
参数：x : spinGroup Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `spinGroup.coe_star_mul_self`：coe_star_mul_self (x : spinGroup Q) : (star
 x : CliffordAlgebra Q) * x = 1
-/
theorem star_mul_self (x : spinGroup Q) : star x * x = 1 :=
  Subtype.ext <| coe_star_mul_self x

@[simp]
/-
**spinGroup.mul_star_self** 是 Mathlib 中的一个定理，位于命名空间 `spinGroup`。
形式化陈述：mul_star_self (x : spinGroup Q) : x * star x = 1
参数：x : spinGroup Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `spinGroup.coe_mul_star_self`：coe_mul_star_self (x : spinGroup Q) : (x : 
CliffordAlgebra Q) * star x = 1
-/
theorem mul_star_self (x : spinGroup Q) : x * star x = 1 :=
  Subtype.ext <| coe_mul_star_self x

/-- `spinGroup Q` forms a group where the inverse is `star`. -/
/-
**spinGroup.** 是 Mathlib 中的一个实例，位于命名空间 `spinGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`spinGroup Q` forms a group where the inverse is `star`.
-/
instance : Group (spinGroup Q) where
  inv := star
  inv_mul_cancel := star_mul_self
/-
**spinGroup.** 是 Mathlib 中的一个实例，位于命名空间 `spinGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : StarMul (spinGroup Q) where
  star_involutive _ := Subtype.ext <| star_involutive _
  star_mul _ _ := Subtype.ext <| star_mul _ _
/-
**spinGroup.** 是 Mathlib 中的一个实例，位于命名空间 `spinGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (spinGroup Q) :=
  ⟨1⟩
/-
**spinGroup.star_eq_inv** 是 Mathlib 中的一个定理，位于命名空间 `spinGroup`。
形式化陈述：star_eq_inv (x : spinGroup Q) : star x = x⁻¹
参数：x : spinGroup Q。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem star_eq_inv (x : spinGroup Q) : star x = x⁻¹ :=
  rfl
/-
**spinGroup.star_eq_inv'** 是 Mathlib 中的一个定理，位于命名空间 `spinGroup`。
形式化陈述：star_eq_inv' : (star : spinGroup Q -> spinGroup Q) = Inv.inv
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem star_eq_inv' : (star : spinGroup Q → spinGroup Q) = Inv.inv :=
  rfl

/-- The elements in `spinGroup Q` embed into (CliffordAlgebra Q)ˣ. -/
@[simps]
/-
**spinGroup.toUnits** 是 Mathlib 中的一个定义，位于命名空间 `spinGroup`。
形式化陈述：toUnits : spinGroup Q ->* (CliffordAlgebra Q)ˣ where toFun x
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `spinGroup.coe_mul_star_self`：coe_mul_star_self (x : spinGroup Q) : (x : 
CliffordAlgebra Q) * star x = 1
· 使用定理 `spinGroup.coe_star_mul_self`：coe_star_mul_self (x : spinGroup Q) : (star
 x : CliffordAlgebra Q) * x = 1

--- 原说明 ---
The elements in `spinGroup Q` embed into (CliffordAlgebra Q)ˣ.
-/
def toUnits : spinGroup Q →* (CliffordAlgebra Q)ˣ where
  toFun x := ⟨x, ↑x⁻¹, coe_mul_star_self x, coe_star_mul_self x⟩
  map_one' := Units.ext rfl
  map_mul' _x _y := Units.ext rfl
/-
**spinGroup.toUnits_injective** 是 Mathlib 中的一个定理，位于命名空间 `spinGroup`。
形式化陈述：toUnits_injective : Function.Injective (toUnits : spinGroup Q -> (Clifford
Algebra Q)ˣ)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Units.ext_iff`：∀ {α : Type u} [inst : Monoid α] {u v : αˣ}, u = v ↔ ↑u =
 ↑v
-/
theorem toUnits_injective : Function.Injective (toUnits : spinGroup Q → (CliffordAlgebra Q)ˣ) :=
  fun _x _y h => Subtype.ext <| Units.ext_iff.mp h

end spinGroup

end Spin

