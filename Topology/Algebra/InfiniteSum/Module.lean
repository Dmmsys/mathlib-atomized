/-
Copyright (c) 2020 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth, Yury Kudryashov, Frédéric Dupuis
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.Constructions
public import Mathlib.Topology.Algebra.Module.Equiv

/-! # Infinite sums in topological vector spaces -/

@[expose] public section

variable {α β γ δ : Type*}

open Filter Finset Function

section ConstSMul

variable [TopologicalSpace α] [AddCommMonoid α] [DistribSMul γ α]
  [ContinuousConstSMul γ α] {f : β → α} {L : SummationFilter β}

/-
**HasSum.const_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasSum.const_smul {a : α} (b : γ) (hf : HasSum f a L) : HasSum (fun i => b
 • f i) (b • a) L
参数：b : γ；hf : HasSum f a L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSum.map`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : AddCo
mmMonoid α] [inst_1 : TopologicalSpace α] {f : β → α}   {a : α} {L : SummationFi
…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `ContinuousConstSMul.continuous_const_smul`：∀ {Γ : Type u_1} {T : Type u_
2} {inst : TopologicalSpace T} {inst_1 : SMul Γ T} [self : ContinuousConstSMul Γ
 T]   (γ : Γ), Continuous fun x…
-/
theorem HasSum.const_smul {a : α} (b : γ) (hf : HasSum f a L) :
    HasSum (fun i ↦ b • f i) (b • a) L :=
  hf.map (DistribSMul.toAddMonoidHom α _) <| continuous_const_smul _
/-
**Summable.const_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Summable.const_smul (b : γ) (hf : Summable f L) : Summable (fun i => b • f
 i) L
参数：b : γ；hf : Summable f L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSum.summable`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α}, H
asSum…
· 使用定理 `HasSum.const_smul`：HasSum.const_smul {a : α} (b : γ) (hf : HasSum f a L)
 : HasSum (fun i => b • f i) (b • a) L
· 使用定理 `Summable.hasSum`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α}, Summable 
f L →…
-/
theorem Summable.const_smul (b : γ) (hf : Summable f L) : Summable (fun i ↦ b • f i) L :=
  (hf.hasSum.const_smul _).summable

/-- Infinite sums commute with scalar multiplication. Version for scalars living in a `Monoid`, but
  requiring a summability hypothesis. -/
/-
**Summable.tsum_const_smul** 是 Mathlib 中的一个定理，位于命名空间 `Summable`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : TopologicalSpace α]
 [inst_1 : AddCommMonoid α]   [inst_2 : DistribSMul γ α] [ContinuousConstSMul γ 
α] {f : β → α} {L : SummationFilter β} [T2Space α] [L.NeBot]   (b : γ), Summable
 f L → ∑'[L] (i : β), b • f i = b • ∑'[L] (i : β), f i
参数：b : γ；i : β；i : β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSum.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α} [T2
Spac…
· 使用定理 `HasSum.const_smul`：HasSum.const_smul {a : α} (b : γ) (hf : HasSum f a L)
 : HasSum (fun i => b • f i) (b • a) L
· 使用定理 `Summable.hasSum`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α}, Summable 
f L →…

--- 原说明 ---
Infinite sums commute with scalar multiplication. Version for scalars living in 
a `Monoid`, but
  requiring a summability hypothesis.
-/
protected theorem Summable.tsum_const_smul [T2Space α] [L.NeBot] (b : γ) (hf : Summable f L) :
    ∑'[L] i, b • f i = b • ∑'[L] i, f i :=
  (hf.hasSum.const_smul _).tsum_eq

/-- Infinite sums commute with scalar multiplication. Version for scalars living in a `Group`, but
  not requiring any summability hypothesis. -/
/-
**tsum_const_smul'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：tsum_const_smul' {γ : Type*} [Group γ] [DistribMulAction γ α] [ContinuousC
onstSMul γ α] [T2Space α] (g : γ) : ∑'[L] (i : β), g • f i = g • ∑'[L] (i : β), 
f i
参数：g : γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DistribSMul.toAddMonoidHom_apply`：∀ {M : Type u_1} (A : Type u_7) [inst 
: AddZeroClass A] [inst_1 : DistribSMul M A] (x : M) (x_1 : A),   (DistribSMul.t
oAddMonoidHom A x) x_1…
· 使用引理 `inv_smul_smul`：inv_smul_smul (g : G) (a : α) : g⁻¹ • g • a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `smul_inv_smul`：smul_inv_smul (g : G) (a : α) : g • g⁻¹ • a = a
· 使用定理 `AddMonoidHom.map_add'`：∀ {M : Type u_10} {N : Type u_11} [inst : AddZero
 M] [inst_1 : AddZero N] (self : M →+ N) (x y : M),   (↑self).toFun (x + y) = (↑
self).toFun…
· 使用定理 `Topology.IsClosedEmbedding.map_tsum`：∀ {ι : Type u_4} {α : Type u_5} {α'
 : Type u_6} {G : Type u_7} [inst : AddCommMonoid α] [inst_1 : AddCommMonoid α']
   [inst_2 : TopologicalS…
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
· 使用定理 `Homeomorph.isClosedEmbedding`：isClosedEmbedding (h : X ≃ₜ Y) : IsClosedE
mbedding h

--- 原说明 ---
Infinite sums commute with scalar multiplication. Version for scalars living in 
a `Group`, but
  not requiring any summability hypothesis.
-/
lemma tsum_const_smul' {γ : Type*} [Group γ] [DistribMulAction γ α] [ContinuousConstSMul γ α]
    [T2Space α] (g : γ) :
    ∑'[L] (i : β), g • f i = g • ∑'[L] (i : β), f i :=
  ((Homeomorph.smul g).isClosedEmbedding.map_tsum f (g := show α ≃+ α from
    { DistribSMul.toAddMonoidHom _ g with
      invFun := DistribSMul.toAddMonoidHom _ g⁻¹
      left_inv a := by simp, right_inv a := by simp })).symm

/-- Infinite sums commute with scalar multiplication. Version for scalars living in a
  `DivisionSemiring`; no summability hypothesis. This could be made to work for a
  `[GroupWithZero γ]` if there was such a thing as `DistribMulActionWithZero`. -/
/-
**tsum_const_smul''** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：tsum_const_smul'' {γ : Type*} [DivisionSemiring γ] [Module γ α] [Continuou
sConstSMul γ α] [T2Space α] (g : γ) : ∑'[L] (i : β), g • f i = g • ∑'[L] (i : β)
, f i
参数：g : γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `tsum_zero`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [ins
t_1 : TopologicalSpace α] {L : SummationFilter β},   ∑'[L] (x : β), 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `tsum_const_smul'`：tsum_const_smul' {γ : Type*} [Group γ] [DistribMulActi
on γ α] [ContinuousConstSMul γ α] [T2Space α] (g : γ) : ∑'[L] (i : β), g • f i =
 g • ∑…

--- 原说明 ---
Infinite sums commute with scalar multiplication. Version for scalars living in 
a
  `DivisionSemiring`; no summability hypothesis. This could be made to work for 
a
  `[GroupWithZero γ]` if there was such a thing as `DistribMulActionWithZero`.
-/
lemma tsum_const_smul'' {γ : Type*} [DivisionSemiring γ] [Module γ α] [ContinuousConstSMul γ α]
    [T2Space α] (g : γ) :
    ∑'[L] (i : β), g • f i = g • ∑'[L] (i : β), f i := by
  rcases eq_or_ne g 0 with rfl | hg
  · simp
  · exact tsum_const_smul' (Units.mk0 g hg)

end ConstSMul



variable {ι κ R R₂ M M₂ : Type*}

section SMulConst

variable [Semiring R] [TopologicalSpace R] [TopologicalSpace M] [AddCommMonoid M] [Module R M]
  [ContinuousSMul R M] {f : ι → R} {L : SummationFilter ι}

/-
**HasSum.smul_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasSum.smul_const {r : R} (hf : HasSum f r L) (a : M) : HasSum (fun z => f
 z • a) (r • a) L
参数：hf : HasSum f r L；a : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSum.map`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : AddCo
mmMonoid α] [inst_1 : TopologicalSpace α] {f : β → α}   {a : α} {L : SummationFi
…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `Continuous.smul`：Continuous.smul (hf : Continuous f) (hg : Continuous g)
 : Continuous (f • g)
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
-/
theorem HasSum.smul_const {r : R} (hf : HasSum f r L) (a : M) :
    HasSum (fun z ↦ f z • a) (r • a) L :=
  hf.map ((smulAddHom R M).flip a) (continuous_id.smul continuous_const)
/-
**Summable.smul_const** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Summable.smul_const (hf : Summable f L) (a : M) : Summable (fun z => f z •
 a) L
参数：hf : Summable f L；a : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSum.summable`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α}, H
asSum…
· 使用定理 `HasSum.smul_const`：HasSum.smul_const {r : R} (hf : HasSum f r L) (a : M)
 : HasSum (fun z => f z • a) (r • a) L
· 使用定理 `Summable.hasSum`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α}, Summable 
f L →…
-/
theorem Summable.smul_const (hf : Summable f L) (a : M) : Summable (fun z ↦ f z • a) L :=
  (hf.hasSum.smul_const _).summable
/-
**Summable.tsum_smul_const** 是 Mathlib 中的一个定理，位于命名空间 `Summable`。
形式化陈述：∀ {ι : Type u_5} {R : Type u_7} {M : Type u_9} [inst : Semiring R] [inst_1
 : TopologicalSpace R]   [inst_2 : TopologicalSpace M] [inst_3 : AddCommMonoid M
] [inst_4 : _root_.Module R M] [ContinuousSMul R M] {f : ι → R}   {L : Summation
Filter ι} [T2Space M] [L.NeBot],   Summable f L → ∀ (a : M), ∑'[L] (z : ι), f z 
• a = (∑'[L] (z : ι), f z) • a
参数：a : M；z : ι；∑'[L] (z : ι), f z。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSum.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α} [T2
Spac…
· 使用定理 `HasSum.smul_const`：HasSum.smul_const {r : R} (hf : HasSum f r L) (a : M)
 : HasSum (fun z => f z • a) (r • a) L
· 使用定理 `Summable.hasSum`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α}, Summable 
f L →…
-/
protected theorem Summable.tsum_smul_const [T2Space M] [L.NeBot] (hf : Summable f L) (a : M) :
    ∑'[L] z, f z • a = (∑'[L] z, f z) • a :=
  (hf.hasSum.smul_const _).tsum_eq

end SMulConst

/-!
Note we cannot derive the `mul` lemmas from these `smul` lemmas, as the `mul` versions do not
require associativity, but `Module` does.
-/
section tsum_smul_tsum

variable [Semiring R] [AddCommMonoid M] [Module R M]
variable [TopologicalSpace R] [TopologicalSpace M] [T3Space M]
variable [ContinuousAdd M] [ContinuousSMul R M]
variable {f : ι → R} {g : κ → M} {s : R} {t u : M}

/-
**HasSum.smul_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasSum.smul_eq (hf : HasSum f s) (hg : HasSum g t) (hfg : HasSum (fun x : 
ι × κ => f x.1 • g x.2) u) : s • t = u
参数：hf : HasSum f s；hg : HasSum g t；hfg : HasSum (fun x : ι × κ => f x.1 • g x.2)
 u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSum.smul_const`：HasSum.smul_const {r : R} (hf : HasSum f r L) (a : M)
 : HasSum (fun z => f z • a) (r • a) L
· 使用定理 `HasSum.const_smul`：HasSum.const_smul {a : α} (b : γ) (hf : HasSum f a L)
 : HasSum (fun i => b • f i) (b • a) L
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `HasSum.prod_fiberwise`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [i
nst : AddCommMonoid α] [inst_1 : TopologicalSpace α] [ContinuousAdd α]   [Regula
rSpace α] {…
· 使用定理 `T3Space.toRegularSpace`：∀ {X : Type u} {inst : TopologicalSpace X} [self
 : T3Space X], RegularSpace X
· 使用定理 `HasSum.unique`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] 
[inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} [T2Space α] 
[L.…
· 使用定理 `T25Space.t2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T25Space
 X], T2Space X
· 使用定理 `T3Space.t25Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T3Space 
X], T25Space X
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
-/
theorem HasSum.smul_eq (hf : HasSum f s) (hg : HasSum g t)
    (hfg : HasSum (fun x : ι × κ ↦ f x.1 • g x.2) u) : s • t = u :=
  have key₁ : HasSum (fun i ↦ f i • t) (s • t) := hf.smul_const t
  have : ∀ i : ι, HasSum (fun c : κ ↦ f i • g c) (f i • t) := fun i ↦ hg.const_smul (f i)
  have key₂ : HasSum (fun i ↦ f i • t) u := HasSum.prod_fiberwise hfg this
  key₁.unique key₂
/-
**HasSum.smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasSum.smul (hf : HasSum f s) (hg : HasSum g t) (hfg : Summable fun x : ι 
× κ => f x.1 • g x.2) : HasSum (fun x : ι × κ => f x.1 • g x.2) (s • t)
参数：hf : HasSum f s；hg : HasSum g t；hfg : Summable fun x : ι × κ => f x.1 • g x.2
。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HasSum.smul_eq`：HasSum.smul_eq (hf : HasSum f s) (hg : HasSum g t) (hfg 
: HasSum (fun x : ι × κ => f x.1 • g x.2) u) : s • t = u
-/
theorem HasSum.smul (hf : HasSum f s) (hg : HasSum g t)
    (hfg : Summable fun x : ι × κ ↦ f x.1 • g x.2) :
    HasSum (fun x : ι × κ ↦ f x.1 • g x.2) (s • t) :=
  let ⟨_u, hu⟩ := hfg
  (hf.smul_eq hg hu).symm ▸ hu

/-- Scalar product of two infinite sums indexed by arbitrary types. -/
/-
**tsum_smul_tsum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tsum_smul_tsum (hf : Summable f) (hg : Summable g) (hfg : Summable fun x :
 ι × κ => f x.1 • g x.2) : ((∑' x, f x) • ∑' y, g y) = ∑' z : ι × κ, f z.1 • g z
.2
参数：hf : Summable f；hg : Summable g；hfg : Summable fun x : ι × κ => f x.1 • g x.2
。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSum.smul_eq`：HasSum.smul_eq (hf : HasSum f s) (hg : HasSum g t) (hfg 
: HasSum (fun x : ι × κ => f x.1 • g x.2) u) : s • t = u
· 使用定理 `Summable.hasSum`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α}, Summable 
f L →…

--- 原说明 ---
Scalar product of two infinite sums indexed by arbitrary types.
-/
theorem tsum_smul_tsum (hf : Summable f) (hg : Summable g)
    (hfg : Summable fun x : ι × κ ↦ f x.1 • g x.2) :
    ((∑' x, f x) • ∑' y, g y) = ∑' z : ι × κ, f z.1 • g z.2 :=
  hf.hasSum.smul_eq hg.hasSum hfg.hasSum

end tsum_smul_tsum

section HasSum

-- Results in this section hold for continuous additive monoid homomorphisms or equivalences but we
-- don't have bundled continuous additive homomorphisms.
variable [Semiring R] [Semiring R₂] [AddCommMonoid M] [Module R M] [AddCommMonoid M₂] [Module R₂ M₂]
  [TopologicalSpace M] [TopologicalSpace M₂] {σ : R →+* R₂} {σ' : R₂ →+* R} [RingHomInvPair σ σ']
  [RingHomInvPair σ' σ] {L : SummationFilter ι}

/-- Applying a continuous linear map commutes with taking an (infinite) sum. -/
/-
**ContinuousLinearMap.hasSum** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：∀ {ι : Type u_5} {R : Type u_7} {R₂ : Type u_8} {M : Type u_9} {M₂ : Type 
u_10} [inst : Semiring R]   [inst_1 : Semiring R₂] [inst_2 : AddCommMonoid M] [i
nst_3 : _root_.Module R M] [inst_4 : AddCommMonoid M₂]   [inst_5 : _root_.Module
 R₂ M₂] [inst_6 : TopologicalSpace M] [inst_7 : TopologicalSpace M₂] {σ : R →+* 
R₂}   {L : SummationFilter ι} {f : ι → M} (φ : M →SL[σ] M₂) {x : M}, HasSum f x 
L → HasSum (fun b => φ (f b)) (φ x) L
参数：φ : M →SL[σ] M₂；fun b => φ (f b)；φ x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSum.map`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : AddCo
mmMonoid α] [inst_1 : TopologicalSpace α] {f : β → α}   {a : α} {L : SummationFi
…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `ContinuousLinearMap.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst 
: Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_
2 : TopologicalSpace…

--- 原说明 ---
Applying a continuous linear map commutes with taking an (infinite) sum.
-/
protected theorem ContinuousLinearMap.hasSum {f : ι → M} (φ : M →SL[σ] M₂) {x : M}
    (hf : HasSum f x L) : HasSum (fun b : ι ↦ φ (f b)) (φ x) L := by
  simpa only using! hf.map φ.toLinearMap.toAddMonoidHom φ.continuous

alias HasSum.mapL := ContinuousLinearMap.hasSum
/-
**ContinuousLinearMap.summable** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：∀ {ι : Type u_5} {R : Type u_7} {R₂ : Type u_8} {M : Type u_9} {M₂ : Type 
u_10} [inst : Semiring R]   [inst_1 : Semiring R₂] [inst_2 : AddCommMonoid M] [i
nst_3 : _root_.Module R M] [inst_4 : AddCommMonoid M₂]   [inst_5 : _root_.Module
 R₂ M₂] [inst_6 : TopologicalSpace M] [inst_7 : TopologicalSpace M₂] {σ : R →+* 
R₂}   {L : SummationFilter ι} {f : ι → M} (φ : M →SL[σ] M₂), Summable f L → Summ
able (fun b => φ (f b)) L
参数：φ : M →SL[σ] M₂；fun b => φ (f b)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSum.summable`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α}, H
asSum…
· 使用定理 `HasSum.mapL`：∀ {ι : Type u_5} {R : Type u_7} {R₂ : Type u_8} {M : Type u
_9} {M₂ : Type u_10} [inst : Semiring R]   [inst_1 : Semiring R₂] [inst_2 : AddC
o…
· 使用定理 `Summable.hasSum`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α}, Summable 
f L →…
-/
protected theorem ContinuousLinearMap.summable {f : ι → M} (φ : M →SL[σ] M₂) (hf : Summable f L) :
    Summable (fun b : ι ↦ φ (f b)) L :=
  (hf.hasSum.mapL φ).summable

alias Summable.mapL := ContinuousLinearMap.summable
/-
**ContinuousLinearMap.map_tsum** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：∀ {ι : Type u_5} {R : Type u_7} {R₂ : Type u_8} {M : Type u_9} {M₂ : Type 
u_10} [inst : Semiring R]   [inst_1 : Semiring R₂] [inst_2 : AddCommMonoid M] [i
nst_3 : _root_.Module R M] [inst_4 : AddCommMonoid M₂]   [inst_5 : _root_.Module
 R₂ M₂] [inst_6 : TopologicalSpace M] [inst_7 : TopologicalSpace M₂] {σ : R →+* 
R₂}   {L : SummationFilter ι} [T2Space M₂] [L.NeBot] {f : ι → M} (φ : M →SL[σ] M
₂),   Summable f L → φ (∑'[L] (z : ι), f z) = ∑'[L] (z : ι), φ (f z)
参数：φ : M →SL[σ] M₂；∑'[L] (z : ι), f z；z : ι；f z。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HasSum.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α} [T2
Spac…
· 使用定理 `HasSum.mapL`：∀ {ι : Type u_5} {R : Type u_7} {R₂ : Type u_8} {M : Type u
_9} {M₂ : Type u_10} [inst : Semiring R]   [inst_1 : Semiring R₂] [inst_2 : AddC
o…
· 使用定理 `Summable.hasSum`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α}, Summable 
f L →…
-/
protected theorem ContinuousLinearMap.map_tsum [T2Space M₂] [L.NeBot] {f : ι → M} (φ : M →SL[σ] M₂)
    (hf : Summable f L) : φ (∑'[L] z, f z) = ∑'[L] z, φ (f z) :=
  (hf.hasSum.mapL φ).tsum_eq.symm

/-- Applying a continuous linear map commutes with taking an (infinite) sum. -/
/-
**ContinuousLinearEquiv.hasSum** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearEquiv`
。
形式化陈述：∀ {ι : Type u_5} {R : Type u_7} {R₂ : Type u_8} {M : Type u_9} {M₂ : Type 
u_10} [inst : Semiring R]   [inst_1 : Semiring R₂] [inst_2 : AddCommMonoid M] [i
nst_3 : _root_.Module R M] [inst_4 : AddCommMonoid M₂]   [inst_5 : _root_.Module
 R₂ M₂] [inst_6 : TopologicalSpace M] [inst_7 : TopologicalSpace M₂] {σ : R →+* 
R₂}   {σ' : R₂ →+* R} [inst_8 : RingHomInvPair σ σ'] [inst_9 : RingHomInvPair σ'
 σ] {L : SummationFilter ι} {f : ι → M}   (e : M ≃SL[σ] M₂) {y : M₂}, HasSum (fu
n b => e (f b)) y L ↔ HasSum f (e.symm y) L
参数：e : M ≃SL[σ] M₂；fun b => e (f b)；e.symm y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ContinuousLinearEquiv.symm_apply_apply`：symm_apply_apply (e : M₁ ≃SL[σ₁₂
] M₂) (b : M₁) : e.symm (e b) = b
· 使用定理 `HasSum.mapL`：∀ {ι : Type u_5} {R : Type u_7} {R₂ : Type u_8} {M : Type u
_9} {M₂ : Type u_10} [inst : Semiring R]   [inst_1 : Semiring R₂] [inst_2 : AddC
o…
· 使用定理 `ContinuousLinearEquiv.apply_symm_apply`：apply_symm_apply (e : M₁ ≃SL[σ₁₂
] M₂) (c : M₂) : e (e.symm c) = c
· 使用定理 `ContinuousLinearMap.hasSum`：∀ {ι : Type u_5} {R : Type u_7} {R₂ : Type u
_8} {M : Type u_9} {M₂ : Type u_10} [inst : Semiring R]   [inst_1 : Semiring R₂]
 [inst_2 : AddCo…

--- 原说明 ---
Applying a continuous linear map commutes with taking an (infinite) sum.
-/
protected theorem ContinuousLinearEquiv.hasSum {f : ι → M} (e : M ≃SL[σ] M₂) {y : M₂} :
    HasSum (fun b : ι ↦ e (f b)) y L ↔ HasSum f (e.symm y) L :=
  ⟨fun h ↦ by simpa only [e.symm.coe_coe, e.symm_apply_apply] using h.mapL (e.symm : M₂ →SL[σ'] M),
    fun h ↦ by simpa only [e.coe_coe, e.apply_symm_apply] using (e : M →SL[σ] M₂).hasSum h⟩

/-- Applying a continuous linear map commutes with taking an (infinite) sum. -/
/-
**ContinuousLinearEquiv.hasSum'** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearEquiv
`。
形式化陈述：∀ {ι : Type u_5} {R : Type u_7} {R₂ : Type u_8} {M : Type u_9} {M₂ : Type 
u_10} [inst : Semiring R]   [inst_1 : Semiring R₂] [inst_2 : AddCommMonoid M] [i
nst_3 : _root_.Module R M] [inst_4 : AddCommMonoid M₂]   [inst_5 : _root_.Module
 R₂ M₂] [inst_6 : TopologicalSpace M] [inst_7 : TopologicalSpace M₂] {σ : R →+* 
R₂}   {σ' : R₂ →+* R} [inst_8 : RingHomInvPair σ σ'] [inst_9 : RingHomInvPair σ'
 σ] {L : SummationFilter ι} {f : ι → M}   (e : M ≃SL[σ] M₂) {x : M}, HasSum (fun
 b => e (f b)) (e x) L ↔ HasSum f x L
参数：e : M ≃SL[σ] M₂；fun b => e (f b)；e x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearEquiv.hasSum`：∀ {ι : Type u_5} {R : Type u_7} {R₂ : Type
 u_8} {M : Type u_9} {M₂ : Type u_10} [inst : Semiring R]   [inst_1 : Semiring R
₂] [inst_2 : AddCo…
· 使用定理 `ContinuousLinearEquiv.symm_apply_apply`：symm_apply_apply (e : M₁ ≃SL[σ₁₂
] M₂) (b : M₁) : e.symm (e b) = b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Applying a continuous linear map commutes with taking an (infinite) sum.
-/
protected theorem ContinuousLinearEquiv.hasSum' {f : ι → M} (e : M ≃SL[σ] M₂) {x : M} :
    HasSum (fun b : ι ↦ e (f b)) (e x) L ↔ HasSum f x L := by
  rw [e.hasSum, ContinuousLinearEquiv.symm_apply_apply]
/-
**ContinuousLinearEquiv.summable** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearEqui
v`。
形式化陈述：∀ {ι : Type u_5} {R : Type u_7} {R₂ : Type u_8} {M : Type u_9} {M₂ : Type 
u_10} [inst : Semiring R]   [inst_1 : Semiring R₂] [inst_2 : AddCommMonoid M] [i
nst_3 : _root_.Module R M] [inst_4 : AddCommMonoid M₂]   [inst_5 : _root_.Module
 R₂ M₂] [inst_6 : TopologicalSpace M] [inst_7 : TopologicalSpace M₂] {σ : R →+* 
R₂}   {σ' : R₂ →+* R} [inst_8 : RingHomInvPair σ σ'] [inst_9 : RingHomInvPair σ'
 σ] {L : SummationFilter ι} {f : ι → M}   (e : M ≃SL[σ] M₂), Summable (fun b => 
e (f b)) L ↔ Summable f L
参数：e : M ≃SL[σ] M₂；fun b => e (f b)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSum.summable`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α}, H
asSum…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ContinuousLinearEquiv.hasSum`：∀ {ι : Type u_5} {R : Type u_7} {R₂ : Type
 u_8} {M : Type u_9} {M₂ : Type u_10} [inst : Semiring R]   [inst_1 : Semiring R
₂] [inst_2 : AddCo…
· 使用定理 `Summable.hasSum`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α}, Summable 
f L →…
· 使用定理 `ContinuousLinearMap.summable`：∀ {ι : Type u_5} {R : Type u_7} {R₂ : Type
 u_8} {M : Type u_9} {M₂ : Type u_10} [inst : Semiring R]   [inst_1 : Semiring R
₂] [inst_2 : AddCo…
-/
protected theorem ContinuousLinearEquiv.summable {f : ι → M} (e : M ≃SL[σ] M₂) :
    (Summable (fun b : ι ↦ e (f b)) L) ↔ Summable f L :=
  ⟨fun hf ↦ (e.hasSum.1 hf.hasSum).summable, (e : M →SL[σ] M₂).summable⟩
/-
**ContinuousLinearEquiv.tsum_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousLinearEquiv.tsum_eq_iff [T2Space M] [T2Space M₂] {f : ι -> M} (e
 : M ≃SL[σ] M₂) {y : M₂} : (∑'[L] z, e (f z)) = y ↔ ∑'[L] z, f z = e.symm y
参数：e : M ≃SL[σ] M₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSum.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α} [T2
Spac…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ContinuousLinearEquiv.hasSum`：∀ {ι : Type u_5} {R : Type u_7} {R₂ : Type
 u_8} {M : Type u_9} {M₂ : Type u_10} [inst : Semiring R]   [inst_1 : Semiring R
₂] [inst_2 : AddCo…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Summable.hasSum_iff`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMono
id α] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α
} [T2Spac…
· 使用定理 `ContinuousLinearEquiv.summable`：∀ {ι : Type u_5} {R : Type u_7} {R₂ : Ty
pe u_8} {M : Type u_9} {M₂ : Type u_10} [inst : Semiring R]   [inst_1 : Semiring
 R₂] [inst_2 : AddCo…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `tsum_bot`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [inst
_1 : TopologicalSpace α] {L : SummationFilter β},   ¬L.NeBot → ∀ (f : β → α), …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AddEquiv.map_finsum`：∀ {M : Type u_2} {N : Type u_3} {α : Sort u_4} [ins
t : AddCommMonoid M] [inst_1 : AddCommMonoid N] (g : M ≃+ N)   (f : α → M), g (∑
ᶠ (i : α)…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `tsum_eq_zero_of_not_summable`：∀ {α : Type u_1} {β : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → 
α}, ¬Summable f L …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `ContinuousSemilinearEquivClass.continuousSemilinearMapClass`：∀ (F : Type
 u_1) {R : Type u_2} {S : Type u_3} [inst : Semiring R] [inst_1 : Semiring S] (σ
 : R →+* S) {σ' : S →+* R}   [inst_2 : RingHomInv…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ContinuousLinearEquiv.apply_symm_apply`：apply_symm_apply (e : M₁ ≃SL[σ₁₂
] M₂) (c : M₂) : e (e.symm c) = c
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem ContinuousLinearEquiv.tsum_eq_iff [T2Space M] [T2Space M₂]
    {f : ι → M} (e : M ≃SL[σ] M₂) {y : M₂} :
    (∑'[L] z, e (f z)) = y ↔ ∑'[L] z, f z = e.symm y := by
  by_cases hf : Summable f L
  · by_cases hL : L.NeBot
    · exact ⟨fun h ↦ (e.hasSum.mp ((e.summable.mpr hf).hasSum_iff.mpr h)).tsum_eq, fun h ↦
        (e.hasSum.mpr (hf.hasSum_iff.mpr h)).tsum_eq⟩
    · simp only [tsum_bot hL, eq_symm_apply]
      constructor <;> rintro rfl
      exacts [e.map_finsum f, (e.map_finsum f).symm]
  · have hf' : ¬Summable (fun z ↦ e (f z)) L := fun h ↦ hf (e.summable.mp h)
    rw [tsum_eq_zero_of_not_summable hf, tsum_eq_zero_of_not_summable hf']
    refine ⟨?_, fun H ↦ ?_⟩
    · rintro rfl
      simp
    · simpa using congr_arg (fun z ↦ e z) H
/-
**ContinuousLinearEquiv.map_tsum** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousLinearEqui
v`。
形式化陈述：∀ {ι : Type u_5} {R : Type u_7} {R₂ : Type u_8} {M : Type u_9} {M₂ : Type 
u_10} [inst : Semiring R]   [inst_1 : Semiring R₂] [inst_2 : AddCommMonoid M] [i
nst_3 : _root_.Module R M] [inst_4 : AddCommMonoid M₂]   [inst_5 : _root_.Module
 R₂ M₂] [inst_6 : TopologicalSpace M] [inst_7 : TopologicalSpace M₂] {σ : R →+* 
R₂}   {σ' : R₂ →+* R} [inst_8 : RingHomInvPair σ σ'] [inst_9 : RingHomInvPair σ'
 σ] {L : SummationFilter ι} [T2Space M]   [T2Space M₂] {f : ι → M} (e : M ≃SL[σ]
 M₂), e (∑'[L] (z : ι), f z) = ∑'[L] (z : ι), e (f z)
参数：e : M ≃SL[σ] M₂；∑'[L] (z : ι), f z；z : ι；f z。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `symm`：symm [Std.Symm r] : a ≺ b -> b ≺ a
· 使用定理 `IsEquiv.toSymm`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsEquiv α r]
, Std.Symm r
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ContinuousLinearEquiv.tsum_eq_iff`：ContinuousLinearEquiv.tsum_eq_iff [T2
Space M] [T2Space M₂] {f : ι -> M} (e : M ≃SL[σ] M₂) {y : M₂} : (∑'[L] z, e (f z
)) = y ↔ ∑'[L] z, f z =…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearEquiv.symm_apply_apply`：symm_apply_apply (e : M₁ ≃SL[σ₁₂
] M₂) (b : M₁) : e.symm (e b) = b
-/
protected theorem ContinuousLinearEquiv.map_tsum [T2Space M] [T2Space M₂]
    {f : ι → M} (e : M ≃SL[σ] M₂) : e (∑'[L] z, f z) = ∑'[L] z, e (f z) := by
  refine symm (e.tsum_eq_iff.mpr ?_)
  rw [e.symm_apply_apply _]

end HasSum



section automorphize

variable {M : Type*} [TopologicalSpace M] [AddCommMonoid M] [T2Space M] {R : Type*}
  [DivisionRing R] [Module R M] [ContinuousConstSMul R M]

/-- Given a group `α` acting on a type `β`, and a function `f : β → M`, we "automorphize" `f` to a
  function `β ⧸ α → M` by summing over `α` orbits, `b ↦ ∑' (a : α), f(a • b)`. -/
@[to_additive /-- Given an additive group `α` acting on a type `β`, and a function `f : β → M`,
  we automorphize `f` to a function `β ⧸ α → M` by summing over `α` orbits,
  `b ↦ ∑' (a : α), f(a • b)`. -/]
/-
**MulAction.automorphize** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：MulAction.automorphize [Group α] [MulAction α β] (f : β -> M) : Quotient (
MulAction.orbitRel α β) -> M
参数：f : β -> M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def MulAction.automorphize [Group α] [MulAction α β] (f : β → M) :
    Quotient (MulAction.orbitRel α β) → M := by
  refine @Quotient.lift _ _ (_) (fun b ↦ ∑' (a : α), f (a • b)) ?_
  intro b₁ b₂ ⟨a, (ha : a • b₂ = b₁)⟩
  rw [← ha]
  convert! (Equiv.mulRight a).tsum_eq (fun a' ↦ f (a' • b₂)) using 1
  simp only [Equiv.coe_mulRight]
  congr
  ext
  congr 1
  simp only [mul_smul]

/-- Automorphization of a function into an `R`-`Module` distributes, that is, commutes with the
`R`-scalar multiplication. -/
@[to_additive (dont_translate := R) automorphize_smul_left /--
Automorphization of a function into an `R`-`Module` distributes, that is, commutes with the
`R`-scalar multiplication. -/]
/-
**MulAction.automorphize_smul_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MulAction.automorphize_smul_left [Group α] [MulAction α β] (f : β -> M) (g
 : Quotient (MulAction.orbitRel α β) -> R) : MulAction.automorphize ((g ∘ (@Quot
ient.mk' _ (_))) • f) = g • (MulAction.automorphize f : Quotient (MulAction.orbi
tRel α β) -> M)
参数：f : β -> M；g : Quotient (MulAction.orbitRel α β) -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Quotient.mk'`：Quotient.mk'_surjective [s : Setoid α] : Function.Surjecti
ve (Quotient.mk' : α -> Quotient s)
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Quotient.eq`：Quotient.eq {r : Setoid α} {x y : α} : Quotient.mk r x = ⟦y
⟧ ↔ r x y
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `tsum_const_smul''`：tsum_const_smul'' {γ : Type*} [DivisionSemiring γ] [M
odule γ α] [ContinuousConstSMul γ α] [T2Space α] (g : γ) : ∑'[L] (i : β), g • f 
i = g •…
-/
lemma MulAction.automorphize_smul_left [Group α] [MulAction α β] (f : β → M)
    (g : Quotient (MulAction.orbitRel α β) → R) :
    MulAction.automorphize ((g ∘ (@Quotient.mk' _ (_))) • f)
      = g • (MulAction.automorphize f : Quotient (MulAction.orbitRel α β) → M) := by
  ext x
  induction x using Quotient.inductionOn with | _ b
  simp only [automorphize, Pi.smul_apply', comp_apply]
  set π : β → Quotient (MulAction.orbitRel α β) := Quotient.mk (MulAction.orbitRel α β)
  have H₁ : ∀ a : α, π (a • b) = π b := by
    intro a
    apply (@Quotient.eq _ (MulAction.orbitRel α β) (a • b) b).mpr
    use a
  change ∑' a : α, g (π (a • b)) • f (a • b) = g (π b) • ∑' a : α, f (a • b)
  simp_rw [H₁]
  exact tsum_const_smul'' _

section

variable {G : Type*} [Group G] {Γ : Subgroup G}

/-- Given a subgroup `Γ` of a group `G`, and a function `f : G → M`, we "automorphize" `f` to a
  function `G ⧸ Γ → M` by summing over `Γ` orbits, `g ↦ ∑' (γ : Γ), f(γ • g)`. -/
@[to_additive /-- Given a subgroup `Γ` of an additive group `G`, and a function `f : G → M`, we
  automorphize `f` to a function `G ⧸ Γ → M` by summing over `Γ` orbits,
  `g ↦ ∑' (γ : Γ), f(γ • g)`. -/]
/-
**QuotientGroup.automorphize** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：QuotientGroup.automorphize (f : G -> M) : G ⧸ Γ -> M
参数：f : G -> M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def QuotientGroup.automorphize (f : G → M) : G ⧸ Γ → M := MulAction.automorphize f

/-- Automorphization of a function into an `R`-`Module` distributes, that is, commutes with the
`R`-scalar multiplication. -/
/-
**QuotientGroup.automorphize_smul_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：QuotientGroup.automorphize_smul_left (f : G -> M) (g : G ⧸ Γ -> R) : (Quot
ientGroup.automorphize ((g ∘ (@Quotient.mk' _ (_)) : G -> R) • f) : G ⧸ Γ -> M) 
= g • (QuotientGroup.automorphize f : G ⧸ Γ -> M)
参数：f : G -> M；g : G ⧸ Γ -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MulAction.automorphize_smul_left`：MulAction.automorphize_smul_left [Grou
p α] [MulAction α β] (f : β -> M) (g : Quotient (MulAction.orbitRel α β) -> R) :
 MulAction.automorphiz…

--- 原说明 ---
Automorphization of a function into an `R`-`Module` distributes, that is, commut
es with the
`R`-scalar multiplication.
-/
lemma QuotientGroup.automorphize_smul_left (f : G → M) (g : G ⧸ Γ → R) :
    (QuotientGroup.automorphize ((g ∘ (@Quotient.mk' _ (_)) : G → R) • f) : G ⧸ Γ → M)
      = g • (QuotientGroup.automorphize f : G ⧸ Γ → M) :=
  MulAction.automorphize_smul_left f g

end

section

variable {G : Type*} [AddGroup G] {Γ : AddSubgroup G}

/-- Automorphization of a function into an `R`-`Module` distributes, that is, commutes with the
`R`-scalar multiplication. -/
/-
**QuotientAddGroup.automorphize_smul_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：QuotientAddGroup.automorphize_smul_left (f : G -> M) (g : G ⧸ Γ -> R) : Qu
otientAddGroup.automorphize ((g ∘ (@Quotient.mk' _ (_))) • f) = g • (QuotientAdd
Group.automorphize f : G ⧸ Γ -> M)
参数：f : G -> M；g : G ⧸ Γ -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddAction.automorphize_smul_left`：∀ {α : Type u_1} {β : Type u_2} {M : T
ype u_11} [inst : TopologicalSpace M] [inst_1 : AddCommMonoid M] [T2Space M]   {
R : Type u_12} [inst_3…

--- 原说明 ---
Automorphization of a function into an `R`-`Module` distributes, that is, commut
es with the
`R`-scalar multiplication.
-/
lemma QuotientAddGroup.automorphize_smul_left (f : G → M) (g : G ⧸ Γ → R) :
    QuotientAddGroup.automorphize ((g ∘ (@Quotient.mk' _ (_))) • f)
      = g • (QuotientAddGroup.automorphize f : G ⧸ Γ → M) :=
  AddAction.automorphize_smul_left f g

end

end automorphize

