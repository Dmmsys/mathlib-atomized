/-
Copyright (c) 2021 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Kim Morrison
-/
module

public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.GroupWithZero.Divisibility
public import Mathlib.Algebra.Order.Group.Pointwise.Interval
public import Mathlib.Topology.Algebra.GroupWithZero
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Order.LocalExtr

/-!
# Topological fields

A topological division ring is a topological ring whose inversion function is continuous at every
non-zero element.

-/

@[expose] public section

variable {K : Type*} [DivisionRing K] [TopologicalSpace K]

/-- Left-multiplication by a nonzero element of a topological division ring is proper, i.e.,
inverse images of compact sets are compact. -/
/-
**Filter.tendsto_cocompact_mul_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.tendsto_cocompact_mul_left {a b : M} (ha : b * a = 1) : Filter.Tend
sto (fun x : M => a * x) (Filter.cocompact M) (Filter.cocompact M)
参数：ha : b * a = 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.of_tendsto_comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Typ
e u_3} {f : α → β} {g : β → γ} {a : Filter α} {b : Filter β} {c : Filter γ},   F
ilter.Tendsto (g ∘ f…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x
· 使用定理 `Filter.comap_cocompact_le`：Filter.comap_cocompact_le {f : X -> Y} (hf : 
Continuous f) : (Filter.cocompact Y).comap f <= Filter.cocompact X
· 使用定理 `continuous_const_mul`：continuous_const_mul (m : M) : Continuous (m * ·)

--- 原说明 ---
Left-multiplication by a nonzero element of a topological division ring is prope
r, i.e.,
inverse images of compact sets are compact.
-/
theorem Filter.tendsto_cocompact_mul_left₀ [SeparatelyContinuousMul K] {a : K} (ha : a ≠ 0) :
    Filter.Tendsto (fun x : K => a * x) (Filter.cocompact K) (Filter.cocompact K) :=
  Filter.tendsto_cocompact_mul_left (inv_mul_cancel₀ ha)

/-- Right-multiplication by a nonzero element of a topological division ring is proper, i.e.,
inverse images of compact sets are compact. -/
/-
**Filter.tendsto_cocompact_mul_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.tendsto_cocompact_mul_right {a b : M} (ha : a * b = 1) : Filter.Ten
dsto (fun x : M => x * a) (Filter.cocompact M) (Filter.cocompact M)
参数：ha : a * b = 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.of_tendsto_comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Typ
e u_3} {f : α → β} {g : β → γ} {a : Filter α} {b : Filter β} {c : Filter γ},   F
ilter.Tendsto (g ∘ f…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `comp_mul_right`：comp_mul_right (x y : α) : (· * x) ∘ (· * y) = (· * (y *
 x))
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x
· 使用定理 `Filter.comap_cocompact_le`：Filter.comap_cocompact_le {f : X -> Y} (hf : 
Continuous f) : (Filter.cocompact Y).comap f <= Filter.cocompact X
· 使用定理 `continuous_mul_const`：continuous_mul_const (m : M) : Continuous (· * m)

--- 原说明 ---
Right-multiplication by a nonzero element of a topological division ring is prop
er, i.e.,
inverse images of compact sets are compact.
-/
theorem Filter.tendsto_cocompact_mul_right₀ [SeparatelyContinuousMul K] {a : K} (ha : a ≠ 0) :
    Filter.Tendsto (fun x : K => x * a) (Filter.cocompact K) (Filter.cocompact K) :=
  Filter.tendsto_cocompact_mul_right (mul_inv_cancel₀ ha)

/-- Compact Hausdorff topological fields are finite. This is not an instance, as it would apply to
every `Finite` goal, causing slowly failing typeclass search in some cases. -/
/-
**DivisionRing.finite_of_compactSpace_of_t2Space** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DivisionRing.finite_of_compactSpace_of_t2Space {K} [DivisionRing K] [Topol
ogicalSpace K] [IsTopologicalRing K] [CompactSpace K] [T2Space K] : Finite K
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `discreteTopology_iff_isOpen_singleton_zero`：∀ {G : Type w} [inst : Topol
ogicalSpace G] [inst_1 : AddGroup G] [SeparatelyContinuousAdd G],   DiscreteTopo
logy G ↔ IsOpen {0}
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用引理 `GroupWithZero.isOpen_singleton_zero`：GroupWithZero.isOpen_singleton_zero
 [GroupWithZero M] [TopologicalSpace M] [ContinuousMul M] [CompactSpace M] [T1Sp
ace M] : IsOpen {(0 : M)}
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `finite_of_compact_of_discrete`：finite_of_compact_of_discrete [CompactSpa
ce X] [DiscreteTopology X] : Finite X

--- 原说明 ---
Compact Hausdorff topological fields are finite. This is not an instance, as it 
would apply to
every `Finite` goal, causing slowly failing typeclass search in some cases.
-/
theorem DivisionRing.finite_of_compactSpace_of_t2Space {K} [DivisionRing K] [TopologicalSpace K]
    [IsTopologicalRing K] [CompactSpace K] [T2Space K] : Finite K := by
  suffices DiscreteTopology K by
    exact finite_of_compact_of_discrete
  rw [discreteTopology_iff_isOpen_singleton_zero]
  exact GroupWithZero.isOpen_singleton_zero

variable (K)

/-- A topological division ring is a division ring with a topology where all operations are
continuous, including inversion. -/
/-
**IsTopologicalDivisionRing** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(K : Type u_1) → [DivisionRing K] → [TopologicalSpace K] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A topological division ring is a division ring with a topology where all operati
ons are
continuous, including inversion.
-/
class IsTopologicalDivisionRing : Prop extends IsTopologicalRing K, ContinuousInv₀ K

section Subfield

variable {α : Type*} [Field α] [TopologicalSpace α] [IsTopologicalDivisionRing α]

/-- The (topological-space) closure of a subfield of a topological field is
itself a subfield. -/
/-
**Subfield.topologicalClosure** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Subfield.topologicalClosure (K : Subfield α) : Subfield α
参数：K : Subfield α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The (topological-space) closure of a subfield of a topological field is
itself a subfield.
-/
def Subfield.topologicalClosure (K : Subfield α) : Subfield α :=
  { K.toSubring.topologicalClosure with
    carrier := _root_.closure (K : Set α)
    inv_mem' := fun x hx => by
      rcases eq_or_ne x 0 with (rfl | h)
      · rwa [inv_zero]
      · rw [← inv_coe_set, ← Set.image_inv_eq_inv]
        exact mem_closure_image (continuousAt_inv₀ h) hx }
/-
**Subfield.le_topologicalClosure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subfield.le_topologicalClosure (s : Subfield α) : s <= s.topologicalClosur
e
参数：s : Subfield α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
-/
theorem Subfield.le_topologicalClosure (s : Subfield α) : s ≤ s.topologicalClosure :=
  _root_.subset_closure
/-
**Subfield.isClosed_topologicalClosure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subfield.isClosed_topologicalClosure (s : Subfield α) : IsClosed (s.topolo
gicalClosure : Set α)
参数：s : Subfield α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
-/
theorem Subfield.isClosed_topologicalClosure (s : Subfield α) :
    IsClosed (s.topologicalClosure : Set α) :=
  isClosed_closure
/-
**Subfield.topologicalClosure_minimal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subfield.topologicalClosure_minimal (s : Subfield α) {t : Subfield α} (h :
 s <= t) (ht : IsClosed (t : Set α)) : s.topologicalClosure <= t
参数：s : Subfield α；h : s <= t；ht : IsClosed (t : Set α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `closure_minimal`：closure_minimal (h₁ : s subseteq t) (h₂ : IsClosed t) :
 closure s subseteq t
-/
theorem Subfield.topologicalClosure_minimal (s : Subfield α) {t : Subfield α} (h : s ≤ t)
    (ht : IsClosed (t : Set α)) : s.topologicalClosure ≤ t :=
  closure_minimal h ht

end Subfield

section Units

/-- In an ordered field, the units of the nonnegative elements are the positive elements. -/
@[simps!]
/-
**Nonneg.unitsHomeomorphPos** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Nonneg.unitsHomeomorphPos (R : Type*) [DivisionSemiring R] [PartialOrder R
] [IsStrictOrderedRing R] [PosMulReflectLT R] [TopologicalSpace R] [ContinuousIn
v₀ R] : { r : R // 0 <= r }ˣ ≃ₜ { r : R // 0 < r } where __
参数：R : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In an ordered field, the units of the nonnegative elements are the positive elem
ents.
-/
def Nonneg.unitsHomeomorphPos (R : Type*) [DivisionSemiring R] [PartialOrder R]
    [IsStrictOrderedRing R] [PosMulReflectLT R]
    [TopologicalSpace R] [ContinuousInv₀ R] :
    { r : R // 0 ≤ r }ˣ ≃ₜ { r : R // 0 < r } where
  __ := Nonneg.unitsEquivPos R
  continuous_toFun := by
    rw [Topology.IsEmbedding.subtypeVal.continuous_iff]
    exact Continuous.subtype_val (p := (0 ≤ ·)) Units.continuous_val
  continuous_invFun := by
    rw [Units.continuous_iff]
    refine ⟨by fun_prop, ?_⟩
    suffices Continuous fun (x : { r : R // 0 < r }) ↦ (x⁻¹ : R) by
      simpa [Topology.IsEmbedding.subtypeVal.continuous_iff, Function.comp_def]
    rw [continuous_iff_continuousAt]
    exact fun x ↦ ContinuousAt.inv₀ (by fun_prop) x.2.ne'

end Units

section affineHomeomorph

/-!
This section is about affine homeomorphisms from a topological field `𝕜` to itself.
Technically it does not require `𝕜` to be a topological field, a topological ring that
happens to be a field is enough.
-/


variable {𝕜 : Type*} [Field 𝕜] [TopologicalSpace 𝕜] [IsTopologicalRing 𝕜]

/--
The map `fun x => a * x + b`, as a homeomorphism from `𝕜` (a topological field) to itself,
when `a ≠ 0`.
-/
@[simps]
/-
**affineHomeomorph** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：affineHomeomorph (a b : 𝕜) (h : a != 0) : 𝕜 ≃ₜ 𝕜 where toFun x
参数：a b : 𝕜；h : a != 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map `fun x => a * x + b`, as a homeomorphism from `𝕜` (a topological field) 
to itself,
when `a ≠ 0`.
-/
def affineHomeomorph (a b : 𝕜) (h : a ≠ 0) : 𝕜 ≃ₜ 𝕜 where
  toFun x := a * x + b
  invFun y := (y - b) / a
  left_inv x := by
    simp only [add_sub_cancel_right]
    exact mul_div_cancel_left₀ x h
  right_inv y := by simp [mul_div_cancel₀ _ h]

set_option backward.isDefEq.respectTransparency false in
/-
**affineHomeomorph_image_Icc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：affineHomeomorph_image_Icc {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrict
OrderedRing 𝕜] [TopologicalSpace 𝕜] [IsTopologicalRing 𝕜] (a b c d : 𝕜) (h : 0 <
 a) : affineHomeomorph a b h.ne' '' Set.Icc c d = Set.Icc (a * c + b) (a * d + b
)
参数：a b c d : 𝕜；h : 0 < a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `affineHomeomorph_apply`：∀ {𝕜 : Type u_2} [inst : Field 𝕜] [inst_1 : Topo
logicalSpace 𝕜] [inst_2 : IsTopologicalRing 𝕜] (a b : 𝕜) (h : a ≠ 0)   (x : 𝕜), 
(affineHomeo…
· 使用定理 `Set.image_affine_Icc'`：image_affine_Icc' (h : 0 < a) (b c d : K) : (a * 
· + b) '' Icc c d = Icc (a * c + b) (a * d + b)
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem affineHomeomorph_image_Icc {𝕜 : Type*}
    [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜]
    [IsTopologicalRing 𝕜] (a b c d : 𝕜) (h : 0 < a) :
    affineHomeomorph a b h.ne' '' Set.Icc c d = Set.Icc (a * c + b) (a * d + b) := by
  simp [h]

set_option backward.isDefEq.respectTransparency false in
/-
**affineHomeomorph_image_Ico** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：affineHomeomorph_image_Ico {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrict
OrderedRing 𝕜] [TopologicalSpace 𝕜] [IsTopologicalRing 𝕜] (a b c d : 𝕜) (h : 0 <
 a) : affineHomeomorph a b h.ne' '' Set.Ico c d = Set.Ico (a * c + b) (a * d + b
)
参数：a b c d : 𝕜；h : 0 < a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `affineHomeomorph_apply`：∀ {𝕜 : Type u_2} [inst : Field 𝕜] [inst_1 : Topo
logicalSpace 𝕜] [inst_2 : IsTopologicalRing 𝕜] (a b : 𝕜) (h : a ≠ 0)   (x : 𝕜), 
(affineHomeo…
· 使用定理 `Set.image_affine_Ico`：image_affine_Ico (h : 0 < a) (b c d : K) : (a * · 
+ b) '' Ico c d = Ico (a * c + b) (a * d + b)
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem affineHomeomorph_image_Ico {𝕜 : Type*}
    [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜]
    [IsTopologicalRing 𝕜] (a b c d : 𝕜) (h : 0 < a) :
    affineHomeomorph a b h.ne' '' Set.Ico c d = Set.Ico (a * c + b) (a * d + b) := by
  simp [h]

set_option backward.isDefEq.respectTransparency false in
/-
**affineHomeomorph_image_Ioc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：affineHomeomorph_image_Ioc {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrict
OrderedRing 𝕜] [TopologicalSpace 𝕜] [IsTopologicalRing 𝕜] (a b c d : 𝕜) (h : 0 <
 a) : affineHomeomorph a b h.ne' '' Set.Ioc c d = Set.Ioc (a * c + b) (a * d + b
)
参数：a b c d : 𝕜；h : 0 < a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `affineHomeomorph_apply`：∀ {𝕜 : Type u_2} [inst : Field 𝕜] [inst_1 : Topo
logicalSpace 𝕜] [inst_2 : IsTopologicalRing 𝕜] (a b : 𝕜) (h : a ≠ 0)   (x : 𝕜), 
(affineHomeo…
· 使用定理 `Set.image_affine_Ioc`：image_affine_Ioc (h : 0 < a) (b c d : K) : (a * · 
+ b) '' Ioc c d = Ioc (a * c + b) (a * d + b)
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem affineHomeomorph_image_Ioc {𝕜 : Type*}
    [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜]
    [IsTopologicalRing 𝕜] (a b c d : 𝕜) (h : 0 < a) :
    affineHomeomorph a b h.ne' '' Set.Ioc c d = Set.Ioc (a * c + b) (a * d + b) := by
  simp [h]

set_option backward.isDefEq.respectTransparency false in
/-
**affineHomeomorph_image_Ioo** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：affineHomeomorph_image_Ioo {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrict
OrderedRing 𝕜] [TopologicalSpace 𝕜] [IsTopologicalRing 𝕜] (a b c d : 𝕜) (h : 0 <
 a) : affineHomeomorph a b h.ne' '' Set.Ioo c d = Set.Ioo (a * c + b) (a * d + b
)
参数：a b c d : 𝕜；h : 0 < a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `affineHomeomorph_apply`：∀ {𝕜 : Type u_2} [inst : Field 𝕜] [inst_1 : Topo
logicalSpace 𝕜] [inst_2 : IsTopologicalRing 𝕜] (a b : 𝕜) (h : a ≠ 0)   (x : 𝕜), 
(affineHomeo…
· 使用定理 `Set.image_affine_Ioo`：image_affine_Ioo (h : 0 < a) (b c d : K) : (a * · 
+ b) '' Ioo c d = Ioo (a * c + b) (a * d + b)
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem affineHomeomorph_image_Ioo {𝕜 : Type*}
    [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜]
    [IsTopologicalRing 𝕜] (a b c d : 𝕜) (h : 0 < a) :
    affineHomeomorph a b h.ne' '' Set.Ioo c d = Set.Ioo (a * c + b) (a * d + b) := by
  simp [h]

end affineHomeomorph

section LocalExtr

variable {α β : Type*} [TopologicalSpace α]
  [Semifield β] [LinearOrder β] [IsStrictOrderedRing β] {a : α}

open Topology

/-
**IsLocalMin.inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLocalMin.inv {f : α -> β} {a : α} (h1 : IsLocalMin f a) (h2 : forallᶠ z 
in 𝓝 a, 0 < f z) : IsLocalMax f⁻¹ a
参数：h1 : IsLocalMin f a；h2 : forallᶠ z in 𝓝 a, 0 < f z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `inv_le_inv₀`：inv_le_inv₀ (ha : 0 < a) (hb : 0 < b) : a⁻¹ <= b⁻¹ ↔ b <= a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `Filter.Eventually.self_of_nhds`：Filter.Eventually.self_of_nhds {p : X ->
 Prop} (h : forallᶠ y in 𝓝 x, p y) : p x
-/
theorem IsLocalMin.inv {f : α → β} {a : α} (h1 : IsLocalMin f a) (h2 : ∀ᶠ z in 𝓝 a, 0 < f z) :
    IsLocalMax f⁻¹ a := by
  filter_upwards [h1, h2] with z h3 h4 using (inv_le_inv₀ h4 h2.self_of_nhds).mpr h3

end LocalExtr

section Preconnected

/-! Some results about functions on preconnected sets valued in a ring or field with a topology. -/

open Set

variable {α 𝕜 : Type*} {f g : α → 𝕜} {S : Set α} [TopologicalSpace α] [TopologicalSpace 𝕜]
  [T1Space 𝕜]

/-- If `f` is a function `α → 𝕜` which is continuous on a preconnected set `S`, and
`f ^ 2 = 1` on `S`, then either `f = 1` on `S`, or `f = -1` on `S`. -/
/-
**IsPreconnected.eq_one_or_eq_neg_one_of_sq_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsPreconnected.eq_one_or_eq_neg_one_of_sq_eq [Ring 𝕜] [NoZeroDivisors 𝕜] (
hS : IsPreconnected S) (hf : ContinuousOn f S) (hsq : EqOn (f ^ 2) 1 S) : EqOn f
 1 S ∨ EqOn f (-1) S
参数：hS : IsPreconnected S；hf : ContinuousOn f S；hsq : EqOn (f ^ 2) 1 S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
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
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `IsPreconnected.eqOn_const_of_mapsTo`：IsPreconnected.eqOn_const_of_mapsTo
 {S : Set α} (hS : IsPreconnected S) {β} [TopologicalSpace β] {T : Set β} (hT : 
IsDiscrete T) {f : α -> β…
· 使用引理 `Set.Finite.isDiscrete`：Set.Finite.isDiscrete [T1Space X] {s : Set X} (hs
 : s.Finite) : IsDiscrete s
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α

--- 原说明 ---
If `f` is a function `α → 𝕜` which is continuous on a preconnected set `S`, and
`f ^ 2 = 1` on `S`, then either `f = 1` on `S`, or `f = -1` on `S`.
-/
theorem IsPreconnected.eq_one_or_eq_neg_one_of_sq_eq [Ring 𝕜] [NoZeroDivisors 𝕜]
    (hS : IsPreconnected S) (hf : ContinuousOn f S) (hsq : EqOn (f ^ 2) 1 S) :
    EqOn f 1 S ∨ EqOn f (-1) S := by
  have hmaps : MapsTo f S {1, -1} := by
    simpa only [EqOn, Pi.one_apply, Pi.pow_apply, sq_eq_one_iff] using! hsq
  simpa using! hS.eqOn_const_of_mapsTo (toFinite _).isDiscrete hf hmaps

/-- If `f, g` are functions `α → 𝕜`, both continuous on a preconnected set `S`, with
`f ^ 2 = g ^ 2` on `S`, and `g z ≠ 0` all `z ∈ S`, then either `f = g` or `f = -g` on
`S`. -/
/-
**IsPreconnected.eq_or_eq_neg_of_sq_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsPreconnected.eq_or_eq_neg_of_sq_eq [Field 𝕜] [ContinuousInv₀ 𝕜] [Continu
ousMul 𝕜] (hS : IsPreconnected S) (hf : ContinuousOn f S) (hg : ContinuousOn g S
) (hsq : EqOn (f ^ 2) (g ^ 2) S) (hg_ne : forall {x : α}, x in S -> g x != 0) : 
EqOn f g S ∨ EqOn f (-g) S
参数：hS : IsPreconnected S；hf : ContinuousOn f S；hg : ContinuousOn g S；hsq : EqOn 
(f ^ 2) (g ^ 2) S；hg_ne : forall {x : α}, x in S -> g x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `div_pow`：div_pow (a b : α) (n : Nat) : (a / b) ^ n = a ^ n / b ^ n
· 使用引理 `div_eq_one_iff_eq`：div_eq_one_iff_eq (hb : b != 0) : a / b = 1 ↔ a = b
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Field.isDomain`：∀ {K : Type u_1} [inst : Field K], IsDomain K
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用引理 `div_eq_iff`：div_eq_iff (hb : b != 0) : a / b = c ↔ a = c * b
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `IsPreconnected.eq_one_or_eq_neg_one_of_sq_eq`：IsPreconnected.eq_one_or_e
q_neg_one_of_sq_eq [Ring 𝕜] [NoZeroDivisors 𝕜] (hS : IsPreconnected S) (hf : Con
tinuousOn f S) (hsq : EqOn (f ^ 2)…
· 使用定理 `ContinuousOn.div`：ContinuousOn.div (hf : ContinuousOn f s) (hg : Continu
ousOn g s) (h₀ : forall x in s, g x != 0) : ContinuousOn (f / g) s

--- 原说明 ---
If `f, g` are functions `α → 𝕜`, both continuous on a preconnected set `S`, with
`f ^ 2 = g ^ 2` on `S`, and `g z ≠ 0` all `z ∈ S`, then either `f = g` or `f = -
g` on
`S`.
-/
theorem IsPreconnected.eq_or_eq_neg_of_sq_eq [Field 𝕜] [ContinuousInv₀ 𝕜] [ContinuousMul 𝕜]
    (hS : IsPreconnected S) (hf : ContinuousOn f S) (hg : ContinuousOn g S)
    (hsq : EqOn (f ^ 2) (g ^ 2) S) (hg_ne : ∀ {x : α}, x ∈ S → g x ≠ 0) :
    EqOn f g S ∨ EqOn f (-g) S := by
  have hsq : EqOn ((f / g) ^ 2) 1 S := fun x hx => by
    simpa [div_eq_one_iff_eq (pow_ne_zero _ (hg_ne hx)), div_pow] using hsq hx
  simpa +contextual [EqOn, div_eq_iff (hg_ne _)]
    using hS.eq_one_or_eq_neg_one_of_sq_eq (hf.div hg fun z => hg_ne) hsq

/-- If `f, g` are functions `α → 𝕜`, both continuous on a preconnected set `S`, with
`f ^ 2 = g ^ 2` on `S`, and `g z ≠ 0` all `z ∈ S`, then as soon as `f = g` holds at
one point of `S` it holds for all points. -/
/-
**IsPreconnected.eq_of_sq_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsPreconnected.eq_of_sq_eq [Field 𝕜] [ContinuousInv₀ 𝕜] [ContinuousMul 𝕜] 
(hS : IsPreconnected S) (hf : ContinuousOn f S) (hg : ContinuousOn g S) (hsq : E
qOn (f ^ 2) (g ^ 2) S) (hg_ne : forall {x : α}, x in S -> g x != 0) {y : α} (hy 
: y in S) (hy' : f y = g y) : EqOn f g S
参数：hS : IsPreconnected S；hf : ContinuousOn f S；hg : ContinuousOn g S；hsq : EqOn 
(f ^ 2) (g ^ 2) S；hg_ne : forall {x : α}, x in S -> g x != 0；hy : y in S；hy' : f
 y = g y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPreconnected.eq_or_eq_neg_of_sq_eq`：IsPreconnected.eq_or_eq_neg_of_sq_
eq [Field 𝕜] [ContinuousInv₀ 𝕜] [ContinuousMul 𝕜] (hS : IsPreconnected S) (hf : 
ContinuousOn f S) (hg : Co…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Pi.neg_apply`：∀ {ι : Type u_1} {G : ι → Type u_4} [inst : (i : ι) → Neg 
(G i)] (f : (i : ι) → G i) (i : ι), (-f) i = -f i
· 使用定理 `neg_eq_iff_add_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, 
-a = b ↔ a + b = 0
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `mul_eq_zero`：mul_eq_zero : a * b = 0 ↔ a = 0 ∨ b = 0
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Field.isDomain`：∀ {K : Type u_1} [inst : Field K], IsDomain K
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p

--- 原说明 ---
If `f, g` are functions `α → 𝕜`, both continuous on a preconnected set `S`, with
`f ^ 2 = g ^ 2` on `S`, and `g z ≠ 0` all `z ∈ S`, then as soon as `f = g` holds
 at
one point of `S` it holds for all points.
-/
theorem IsPreconnected.eq_of_sq_eq [Field 𝕜] [ContinuousInv₀ 𝕜] [ContinuousMul 𝕜]
    (hS : IsPreconnected S) (hf : ContinuousOn f S) (hg : ContinuousOn g S)
    (hsq : EqOn (f ^ 2) (g ^ 2) S) (hg_ne : ∀ {x : α}, x ∈ S → g x ≠ 0) {y : α} (hy : y ∈ S)
    (hy' : f y = g y) : EqOn f g S := fun x hx => by
  rcases hS.eq_or_eq_neg_of_sq_eq hf hg @hsq @hg_ne with (h | h)
  · exact h hx
  · rw [h _, Pi.neg_apply, neg_eq_iff_add_eq_zero, ← two_mul, mul_eq_zero,
      (iff_of_eq (iff_false _)).2 (hg_ne _)] at hy' ⊢ <;> assumption

end Preconnected

section ContinuousSMul

variable {F : Type*} [DivisionRing F] [TopologicalSpace F] [IsTopologicalRing F]
    (X : Type*) [TopologicalSpace X] [MulAction F X] [ContinuousSMul F X]

/-
**Subfield.continuousSMul** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Subfield.continuousSMul (M : Subfield F) : ContinuousSMul M X
参数：M : Subfield F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Subfield.continuousSMul (M : Subfield F) : ContinuousSMul M X :=
  Subring.continuousSMul M.toSubring X

end ContinuousSMul

