/-
Copyright (c) 2024 Yoh Tanimoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoh Tanimoto
-/
module

public import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-!
# Compactly supported bounded continuous functions

The two-sided ideal of compactly supported bounded continuous functions taking values in a metric
space, with the uniform distance.
-/

@[expose] public section

open Set BoundedContinuousFunction

section CompactlySupported

/-- The two-sided ideal of compactly supported functions. -/
/-
**compactlySupported** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：compactlySupported (α γ : Type*) [TopologicalSpace α] [NonUnitalNormedRing
 γ] : TwoSidedIdeal (α ->ᵇ γ)
参数：α γ : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The two-sided ideal of compactly supported functions.
-/
noncomputable def compactlySupported (α γ : Type*) [TopologicalSpace α] [NonUnitalNormedRing γ] :
    TwoSidedIdeal (α →ᵇ γ) :=
  .mk' {z | HasCompactSupport z} .zero .add .neg .mul_left .mul_right

variable {α γ : Type*} [TopologicalSpace α] [NonUnitalNormedRing γ]

@[inherit_doc]
scoped[BoundedContinuousFunction] notation
  "C_cb(" α ", " γ ")" => compactlySupported α γ
/-
**mem_compactlySupported** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mem_compactlySupported {f : α ->ᵇ γ} : f in C_cb(α, γ) ↔ HasCompactSupport
 f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `TwoSidedIdeal.mem_mk'`：mem_mk' (carrier : Set R) (zero_mem add_mem neg_m
em mul_mem_left mul_mem_right) (x : R) : x in mk' carrier zero_mem add_mem neg_m
em mul_mem_…
· 使用定理 `HasCompactSupport.zero`：∀ {α : Type u_9} {β : Type u_10} [inst : Topolog
icalSpace α] [inst_1 : Zero β], HasCompactSupport 0
· 使用定理 `HasCompactSupport.add`：∀ {α : Type u_2} {β : Type u_4} [inst : Topologic
alSpace α] [inst_1 : AddZeroClass β] {f f' : α → β},   HasCompactSupport f → Has
CompactSupp…
· 使用定理 `HasCompactSupport.neg`：∀ {α : Type u_9} {β : Type u_10} [inst : Topologi
calSpace α] [inst_1 : SubtractionMonoid β] {f : α → β},   HasCompactSupport f → 
HasCompactS…
· 使用定理 `HasCompactSupport.mul_left`：HasCompactSupport.mul_left (hf : HasCompactS
upport f') : HasCompactSupport (f * f')
· 使用定理 `HasCompactSupport.mul_right`：HasCompactSupport.mul_right (hf : HasCompac
tSupport f) : HasCompactSupport (f * f')
-/
lemma mem_compactlySupported {f : α →ᵇ γ} :
    f ∈ C_cb(α, γ) ↔ HasCompactSupport f :=
  TwoSidedIdeal.mem_mk' {z : α →ᵇ γ | HasCompactSupport z} .zero .add .neg .mul_left .mul_right f
/-
**exist_norm_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：exist_norm_eq [c : Nonempty α] {f : α ->ᵇ γ} (h : f in C_cb(α, γ)) : exist
s (x : α), ‖f x‖ = ‖f‖
参数：h : f in C_cb(α, γ)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.exists_isMaxOn`：IsCompact.exists_isMaxOn [ClosedIciTopology α]
 {s : Set β} (hs : IsCompact s) (ne_s : s.Nonempty) {f : β -> α} (hf : Continuou
sOn f s) : exi…
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `mem_compactlySupported`：mem_compactlySupported {f : α ->ᵇ γ} : f in C_cb
(α, γ) ↔ HasCompactSupport f
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `Continuous.norm`：∀ {α : Type u_1} {E : Type u_4} [inst : SeminormedAddGr
oup E] [inst_1 : TopologicalSpace α] {f : α → E},   Continuous f → Continuous fu
n x =…
· 使用定理 `ContinuousMapClass.map_continuous`：∀ {F : Type u_1} {X : outParam (Type 
u_2)} {Y : outParam (Type u_3)} {inst : TopologicalSpace X}   {inst_1 : Topologi
calSpace Y} {inst_2 : F…
· 使用定理 `BoundedContinuousMapClass.toContinuousMapClass`：∀ {F : Type u_2} {α : ou
tParam (Type u_3)} {β : outParam (Type u_4)} {inst : TopologicalSpace α}   {inst
_1 : PseudoMetricSpace β} {inst_2 : …
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `BoundedContinuousFunction.norm_coe_le_norm`：norm_coe_le_norm (x : α) : ‖
f x‖ <= ‖f‖
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `BoundedContinuousFunction.norm_le`：norm_le (C0 : (0 : Real) <= C) : ‖f‖ 
<= C ↔ forall x : α, ‖f x‖ <= C
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `image_eq_zero_of_notMem_tsupport`：∀ {X : Type u_1} {α : Type u_2} [inst 
: Zero α] [inst_1 : TopologicalSpace X] {f : X → α} {x : X},   x ∉ tsupport f → 
f x = 0
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `DFunLike.ext'_iff`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [i
 : DFunLike F α β] {f g : F}, f = g ↔ ⇑f = ⇑g
· 使用定理 `BoundedContinuousFunction.coe_zero`：∀ {α : Type u} {β : Type v} [inst : 
TopologicalSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero β], ⇑0 = 0
· 使用定理 `tsupport_eq_empty_iff`：∀ {X : Type u_1} {α : Type u_2} [inst : Zero α] [
inst_1 : TopologicalSpace X] {f : X → α}, tsupport f = ∅ ↔ f = 0
· 使用定理 `Set.not_nonempty_iff_eq_empty`：not_nonempty_iff_eq_empty : ¬s.Nonempty ↔
 s = ∅
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma exist_norm_eq [c : Nonempty α] {f : α →ᵇ γ} (h : f ∈ C_cb(α, γ)) : ∃ (x : α),
    ‖f x‖ = ‖f‖ := by
  by_cases hs : (tsupport f).Nonempty
  · obtain ⟨x, _, hmax⟩ := mem_compactlySupported.mp h |>.exists_isMaxOn hs <|
      (map_continuous f).norm.continuousOn
    refine ⟨x, le_antisymm (norm_coe_le_norm f x) (norm_le (norm_nonneg _) |>.mpr fun y ↦ ?_)⟩
    by_cases hy : y ∈ tsupport f
    · exact hmax hy
    · simp [image_eq_zero_of_notMem_tsupport hy]
  · suffices f = 0 by simp [this]
    rwa [not_nonempty_iff_eq_empty, tsupport_eq_empty_iff, ← coe_zero, ← DFunLike.ext'_iff] at hs
/-
**norm_lt_iff_of_compactlySupported** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_lt_iff_of_compactlySupported {f : α ->ᵇ γ} (h : f in C_cb(α, γ)) {M :
 Real} (M0 : 0 < M) : ‖f‖ < M ↔ forall (x : α), ‖f x‖ < M
参数：h : f in C_cb(α, γ)；M0 : 0 < M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `BoundedContinuousFunction.norm_coe_le_norm`：norm_coe_le_norm (x : α) : ‖
f x‖ <= ‖f‖
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BoundedContinuousFunction.norm_eq_zero_of_empty`：norm_eq_zero_of_empty [
IsEmpty α] : ‖f‖ = 0
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用引理 `exist_norm_eq`：exist_norm_eq [c : Nonempty α] {f : α ->ᵇ γ} (h : f in C_
cb(α, γ)) : exists (x : α), ‖f x‖ = ‖f‖
-/
theorem norm_lt_iff_of_compactlySupported {f : α →ᵇ γ} (h : f ∈ C_cb(α, γ)) {M : ℝ}
    (M0 : 0 < M) : ‖f‖ < M ↔ ∀ (x : α), ‖f x‖ < M := by
  refine ⟨fun hn x ↦ lt_of_le_of_lt (norm_coe_le_norm f x) hn, ?_⟩
  · obtain (he | he) := isEmpty_or_nonempty α
    · simpa
    · obtain ⟨x, hx⟩ := exist_norm_eq h
      exact fun h ↦ hx ▸ h x
/-
**norm_lt_iff_of_nonempty_compactlySupported** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_lt_iff_of_nonempty_compactlySupported [c : Nonempty α] {f : α ->ᵇ γ} 
(h : f in C_cb(α, γ)) {M : Real} : ‖f‖ < M ↔ forall (x : α), ‖f x‖ < M
参数：h : f in C_cb(α, γ)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `norm_lt_iff_of_compactlySupported`：norm_lt_iff_of_compactlySupported {f 
: α ->ᵇ γ} (h : f in C_cb(α, γ)) {M : Real} (M0 : 0 < M) : ‖f‖ < M ↔ forall (x :
 α), ‖f x‖ < M
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
-/
theorem norm_lt_iff_of_nonempty_compactlySupported [c : Nonempty α] {f : α →ᵇ γ}
    (h : f ∈ C_cb(α, γ)) {M : ℝ} : ‖f‖ < M ↔ ∀ (x : α), ‖f x‖ < M := by
  obtain (hM | hM) := lt_or_ge 0 M
  · exact norm_lt_iff_of_compactlySupported h hM
  · exact ⟨fun h ↦ False.elim <| (h.trans_le hM).not_ge (by positivity),
      fun h ↦ False.elim <| (h (Classical.arbitrary α) |>.trans_le hM).not_ge (by positivity)⟩
/-
**compactlySupported_eq_top_of_isCompact** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：compactlySupported_eq_top_of_isCompact (h : IsCompact (Set.univ : Set α)) 
: C_cb(α, γ) = ⊤
参数：h : IsCompact (Set.univ : Set α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `IsCompact.of_isClosed_subset`：IsCompact.of_isClosed_subset (hs : IsCompa
ct s) (ht : IsClosed t) (h : t subseteq s) : IsCompact t
· 使用定理 `isClosed_tsupport`：∀ {X : Type u_1} {α : Type u_2} [inst : Zero α] [inst
_1 : TopologicalSpace X] (f : X → α), IsClosed (tsupport f)
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
-/
theorem compactlySupported_eq_top_of_isCompact (h : IsCompact (Set.univ : Set α)) :
    C_cb(α, γ) = ⊤ :=
  eq_top_iff.mpr fun _ _ ↦ h.of_isClosed_subset (isClosed_tsupport _) (subset_univ _)

/- This is intentionally not marked `@[simp]` to prevent Lean looking for a `CompactSpace α`
/-
**every** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance every time it sees `C_cb(α, γ)`. -/
/-
**compactlySupported_eq_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：compactlySupported_eq_top [CompactSpace α] : C_cb(α, γ) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `compactlySupported_eq_top_of_isCompact`：compactlySupported_eq_top_of_isC
ompact (h : IsCompact (Set.univ : Set α)) : C_cb(α, γ) = ⊤
· 使用定理 `CompactSpace.isCompact_univ`：∀ {X : Type u_1} {inst : TopologicalSpace X
} [self : CompactSpace X], IsCompact Set.univ

--- 原说明 ---
This is intentionally not marked `@[simp]` to prevent Lean looking for a `Compac
tSpace α`
instance every time it sees `C_cb(α, γ)`.
-/
theorem compactlySupported_eq_top [CompactSpace α] : C_cb(α, γ) = ⊤ :=
  compactlySupported_eq_top_of_isCompact CompactSpace.isCompact_univ
/-
**compactlySupported_eq_top_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：compactlySupported_eq_top_iff [Nontrivial γ] : C_cb(α, γ) = ⊤ ↔ IsCompact 
(Set.univ : Set α)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_ne`：exists_ne [Nontrivial α] (x : α) : exists y, y != x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `BoundedContinuousFunction.const_apply`：∀ (α : Type u) {β : Type v} [inst
 : TopologicalSpace α] [inst_1 : PseudoMetricSpace β] (b : β),   ⇑(BoundedContin
uousFunction.const α b) = f…
· 使用定理 `Function.support_const`：∀ {ι : Type u_1} {M : Type u_3} [inst : Zero M] 
{c : M}, c ≠ 0 → (Function.support fun x => c) = Set.univ
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `HasCompactSupport.isCompact`：∀ {α : Type u_2} {β : Type u_4} [inst : Top
ologicalSpace α] [inst_1 : Zero β] {f : α → β},   HasCompactSupport f → IsCompac
t (tsupport f)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `mem_compactlySupported`：mem_compactlySupported {f : α ->ᵇ γ} : f in C_cb
(α, γ) ↔ HasCompactSupport f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `compactlySupported_eq_top_of_isCompact`：compactlySupported_eq_top_of_isC
ompact (h : IsCompact (Set.univ : Set α)) : C_cb(α, γ) = ⊤
-/
theorem compactlySupported_eq_top_iff [Nontrivial γ] :
    C_cb(α, γ) = ⊤ ↔ IsCompact (Set.univ : Set α) := by
  refine ⟨fun h ↦ ?_, compactlySupported_eq_top_of_isCompact⟩
  obtain ⟨x, hx⟩ := exists_ne (0 : γ)
  simpa [tsupport, Function.support_const hx]
    using (mem_compactlySupported (f := const α x).mp (by simp [h])).isCompact

/-- A compactly supported continuous function is automatically bounded. This constructor gives
an object of `α →ᵇ γ` from `g : α → γ` and these assumptions. -/
/-
**ofCompactSupport** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ofCompactSupport (g : α -> γ) (hg₁ : Continuous g) (hg₂ : HasCompactSuppor
t g) : α ->ᵇ γ where toFun
参数：g : α -> γ；hg₁ : Continuous g；hg₂ : HasCompactSupport g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A compactly supported continuous function is automatically bounded. This constru
ctor gives
an object of `α →ᵇ γ` from `g : α → γ` and these assumptions.
-/
def ofCompactSupport (g : α → γ) (hg₁ : Continuous g) (hg₂ : HasCompactSupport g) : α →ᵇ γ where
  toFun := g
  continuous_toFun := hg₁
  map_bounded' := by
    obtain (hs | hs) := (tsupport g).eq_empty_or_nonempty
    · exact ⟨0, by simp [tsupport_eq_empty_iff.mp hs]⟩
    · obtain ⟨z, _, hmax⟩ := hg₂.exists_isMaxOn hs <| hg₁.norm.continuousOn
      refine ⟨2 * ‖g z‖, dist_le_two_norm' fun x ↦ ?_⟩
      by_cases hx : x ∈ tsupport g
      · exact isMaxOn_iff.mp hmax x hx
      · simp [image_eq_zero_of_notMem_tsupport hx]
/-
**ofCompactSupport_mem** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ofCompactSupport_mem (g : α -> γ) (hg₁ : Continuous g) (hg₂ : HasCompactSu
pport g) : ofCompactSupport g hg₁ hg₂ in C_cb(α, γ)
参数：g : α -> γ；hg₁ : Continuous g；hg₂ : HasCompactSupport g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `mem_compactlySupported`：mem_compactlySupported {f : α ->ᵇ γ} : f in C_cb
(α, γ) ↔ HasCompactSupport f
-/
lemma ofCompactSupport_mem (g : α → γ) (hg₁ : Continuous g) (hg₂ : HasCompactSupport g) :
    ofCompactSupport g hg₁ hg₂ ∈ C_cb(α, γ) := mem_compactlySupported.mpr hg₂
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMul C(α, γ) C_cb(α, γ) where
  smul := fun (g : C(α, γ)) => (fun (f : C_cb(α, γ)) =>
    ⟨ofCompactSupport (g * (f : α →ᵇ γ) : α → γ) (Continuous.mul g.2 f.1.1.2)
    (HasCompactSupport.mul_left (mem_compactlySupported.mp f.2)), by
      apply mem_compactlySupported.mpr
      rw [ofCompactSupport]
      exact HasCompactSupport.mul_left <| mem_compactlySupported.mp f.2
    ⟩)

end CompactlySupported

