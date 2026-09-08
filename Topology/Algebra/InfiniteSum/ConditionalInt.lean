/-
Copyright (c) 2025 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Interval
public import Mathlib.Analysis.Normed.Group.Int
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.MulAction
public import Mathlib.Order.Filter.AtTopBot.Interval
public import Mathlib.Topology.Algebra.InfiniteSum.Defs


/-!
# Sums over symmetric integer intervals

This file contains some lemmas about sums over symmetric integer intervals `Ixx -N N` used, for
example in the definition of the Eisenstein series `E2`.
In particular we define `symmetricIcc`, `symmetricIco`, `symmetricIoc` and `symmetricIoo` as
`SummationFilter`s corresponding to the intervals `Icc -N N`, `Ico -N N`, `Ioc -N N` respectively.
We also prove that these filters are all `NeBot` and `LeAtTop`.

-/

@[expose] public section

open Finset Topology Function Filter SummationFilter

namespace SummationFilter

section IntervalFilters

variable (G : Type*) [Neg G] [Preorder G] [LocallyFiniteOrder G]

/-- The SummationFilter on a locally finite order `G` corresponding to the symmetric
intervals `Icc (-N) N`· -/
@[simps]
/-
**SummationFilter.symmetricIcc** 是 Mathlib 中的一个定义，位于命名空间 `SummationFilter`。
形式化陈述：symmetricIcc : SummationFilter G where filter
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The SummationFilter on a locally finite order `G` corresponding to the symmetric
intervals `Icc (-N) N`·
-/
def symmetricIcc : SummationFilter G where
  filter := atTop.map (fun g ↦ Icc (-g) g)

/-- The SummationFilter on a locally finite order `G` corresponding to the symmetric
intervals `Ioo (-N) N`· Note that for `G = ℤ` this coincides with
`symmetricIcc` so one should use that. See `symmetricIcc_eq_symmetricIoo_int`. -/
@[simps]
/-
**SummationFilter.symmetricIoo** 是 Mathlib 中的一个定义，位于命名空间 `SummationFilter`。
形式化陈述：symmetricIoo : SummationFilter G where filter
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The SummationFilter on a locally finite order `G` corresponding to the symmetric
intervals `Ioo (-N) N`· Note that for `G = ℤ` this coincides with
`symmetricIcc` so one should use that. See `symmetricIcc_eq_symmetricIoo_int`.
-/
def symmetricIoo : SummationFilter G where
  filter := atTop.map (fun g ↦ Ioo (-g) g)

/-- The SummationFilter on a locally finite order `G` corresponding to the symmetric
intervals `Ico (-N) N`· -/
@[simps]
/-
**SummationFilter.symmetricIco** 是 Mathlib 中的一个定义，位于命名空间 `SummationFilter`。
形式化陈述：symmetricIco : SummationFilter G where filter
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The SummationFilter on a locally finite order `G` corresponding to the symmetric
intervals `Ico (-N) N`·
-/
def symmetricIco : SummationFilter G where
  filter := atTop.map (fun N ↦ Ico (-N) N)

/-- The SummationFilter on a locally finite order `G` corresponding to the symmetric
intervals `Ioc (-N) N`· -/
@[simps]
/-
**SummationFilter.symmetricIoc** 是 Mathlib 中的一个定义，位于命名空间 `SummationFilter`。
形式化陈述：symmetricIoc : SummationFilter G where filter
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The SummationFilter on a locally finite order `G` corresponding to the symmetric
intervals `Ioc (-N) N`·
-/
def symmetricIoc : SummationFilter G where
  filter := atTop.map (fun N ↦ Ioc (-N) N)

variable [(atTop : Filter G).NeBot]
/-
**SummationFilter.** 是 Mathlib 中的一个实例，位于命名空间 `SummationFilter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (symmetricIcc G).NeBot where
  ne_bot := by simp [symmetricIcc, Filter.NeBot.map]
/-
**SummationFilter.** 是 Mathlib 中的一个实例，位于命名空间 `SummationFilter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (symmetricIco G).NeBot where
  ne_bot := by simp [symmetricIco, Filter.NeBot.map]
/-
**SummationFilter.** 是 Mathlib 中的一个实例，位于命名空间 `SummationFilter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (symmetricIoc G).NeBot where
  ne_bot := by simp [symmetricIoc, Filter.NeBot.map]
/-
**SummationFilter.** 是 Mathlib 中的一个实例，位于命名空间 `SummationFilter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (symmetricIoo G).NeBot where
  ne_bot := by simp [symmetricIoo, Filter.NeBot.map]

section LeAtTop

variable {G : Type*} [AddCommGroup G] [PartialOrder G] [IsOrderedAddMonoid G] [LocallyFiniteOrder G]

/-
**SummationFilter.symmetricIcc_le_Conditional** 是 Mathlib 中的一个引理，位于命名空间 `Summati
onFilter`。
形式化陈述：symmetricIcc_le_Conditional : (symmetricIcc G).filter <= (conditional G).f
ilter
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.map_mono`：map_mono : Monotone (map m)
· 使用定理 `Filter.Tendsto.prodMk`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f
 : Filter α} {g : Filter β} {h : Filter γ} {m₁ : α → β} {m₂ : α → γ},   Filter.T
endsto m₁ f…
· 使用定理 `Filter.tendsto_neg_atTop_atBot`：∀ {G : Type u_2} [inst : AddCommGroup G]
 [inst_1 : PartialOrder G] [IsOrderedAddMonoid G],   Filter.Tendsto Neg.neg Filt
er.atTop Filter.atBo…
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x
-/
lemma symmetricIcc_le_Conditional :
    (symmetricIcc G).filter ≤ (conditional G).filter :=
  Filter.map_mono (tendsto_neg_atTop_atBot.prodMk tendsto_id)
/-
**SummationFilter.** 是 Mathlib 中的一个实例，位于命名空间 `SummationFilter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (symmetricIcc G).LeAtTop where
  le_atTop := le_trans symmetricIcc_le_Conditional (conditional G).le_atTop

variable [NoTopOrder G] [NoBotOrder G]
/-
**SummationFilter.** 是 Mathlib 中的一个实例，位于命名空间 `SummationFilter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (symmetricIco G).LeAtTop where
  le_atTop := by
    rw [symmetricIco, map_le_iff_le_comap, ← @tendsto_iff_comap]
    exact tendsto_Ico_neg_atTop_atTop
/-
**SummationFilter.** 是 Mathlib 中的一个实例，位于命名空间 `SummationFilter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (symmetricIoc G).LeAtTop where
  le_atTop := by
    rw [symmetricIoc, map_le_iff_le_comap, ← @tendsto_iff_comap]
    exact tendsto_Ioc_neg_atTop_atTop
/-
**SummationFilter.** 是 Mathlib 中的一个实例，位于命名空间 `SummationFilter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (symmetricIoo G).LeAtTop where
  le_atTop := by
    rw [symmetricIoo, map_le_iff_le_comap, ← @tendsto_iff_comap]
    exact tendsto_Ioo_neg_atTop_atTop

end LeAtTop

end IntervalFilters
section Int

variable {α : Type*} {f : ℤ → α} [CommGroup α] [TopologicalSpace α] [ContinuousMul α]

/-
**SummationFilter.symmetricIcc_eq_map_Icc_nat** 是 Mathlib 中的一个引理，位于命名空间 `Summati
onFilter`。
形式化陈述：symmetricIcc_eq_map_Icc_nat : (symmetricIcc Int).filter = atTop.map (fun N
 : Nat => Icc (-(N : Int)) N)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SummationFilter.symmetricIcc_filter`：∀ (G : Type u_1) [inst : Neg G] [in
st_1 : Preorder G] [inst_2 : LocallyFiniteOrder G],   (SummationFilter.symmetric
Icc G).filter = Filter.ma…
· 使用定理 `Filter.map_map`：map_map : Filter.map m' (Filter.map m f) = Filter.map (m
' ∘ m) f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma symmetricIcc_eq_map_Icc_nat :
    (symmetricIcc ℤ).filter = atTop.map (fun N : ℕ ↦ Icc (-(N : ℤ)) N) := by
  simp [← Nat.map_cast_int_atTop, Function.comp_def]
/-
**SummationFilter.symmetricIcc_eq_symmetricIoo_int** 是 Mathlib 中的一个引理，位于命名空间 `Su
mmationFilter`。
形式化陈述：symmetricIcc_eq_symmetricIoo_int : symmetricIcc Int = symmetricIoo Int
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SummationFilter.mk.injEq`：∀ {β : Type u_4} (filter filter_1 : Filter (Fi
nset β)),   ({ filter := filter } = { filter := filter_1 }) = (filter = filter_1
)
· 使用定理 `Filter.ext`：∀ {α : Type u_1} {f g : Filter α}, (∀ (s : Set α), s ∈ f ↔ s
 ∈ g) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Filter.map_map`：map_map : Filter.map m' (Filter.map m f) = Filter.map (m
' ∘ m) f
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `neg_add_rev`：∀ {G : Type u_1} [inst : SubtractionMonoid G] (a b : G), -(
a + b) = -b + -a
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
-/
lemma symmetricIcc_eq_symmetricIoo_int : symmetricIcc ℤ = symmetricIoo ℤ := by
  simp only [symmetricIcc, symmetricIoo, mk.injEq]
  ext s
  simp only [← Nat.map_cast_int_atTop, Filter.map_map, Filter.mem_map, mem_atTop_sets,
    Set.mem_preimage, comp_apply]
  refine ⟨fun ⟨a, ha⟩ ↦ ⟨a + 1, fun b hb ↦ ?_⟩, fun ⟨a, ha⟩ ↦ ⟨a - 1, fun b hb ↦ ?_⟩⟩ <;>
  [convert! ha (b - 1) (by grind) using 1; convert! ha (b + 1) (by grind) using 1] <;>
  simp [Finset.ext_iff] <;> grind

@[to_additive]
/-
**SummationFilter._root_.HasProd.hasProd_symmetricIco_of_hasProd_symmetricIcc** 
是 Mathlib 中的一个引理，位于命名空间 `SummationFilter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.HasProd.hasProd_symmetricIco_of_hasProd_symmetricIcc {a : α}
    (hf : HasProd f a (symmetricIcc ℤ)) (hf2 : Tendsto (fun N : ℕ ↦ (f N)⁻¹) atTop (𝓝 1)) :
    HasProd f a (symmetricIco ℤ) := by
  simp only [HasProd, tendsto_map'_iff, symmetricIcc_eq_map_Icc_nat,
    ← Nat.map_cast_int_atTop, symmetricIco] at *
  apply tendsto_of_div_tendsto_one _ hf
  simpa [Pi.div_def, fun N : ℕ ↦ prod_Icc_eq_prod_Ico_mul f (show (-N : ℤ) ≤ N by lia)]
    using hf2

@[to_additive]
/-
**SummationFilter.multipliable_symmetricIco_of_multipliable_symmetricIcc** 是 Mat
hlib 中的一个引理，位于命名空间 `SummationFilter`。
形式化陈述：multipliable_symmetricIco_of_multipliable_symmetricIcc (hf : Multipliable 
f (symmetricIcc Int)) (hf2 : Tendsto (fun N : Nat => (f N)⁻¹) atTop (𝓝 1)) : Mul
tipliable f (symmetricIco Int)
参数：hf : Multipliable f (symmetricIcc Int)；hf2 : Tendsto (fun N : Nat => (f N)⁻¹)
 atTop (𝓝 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasProd.multipliable`：HasProd.multipliable (h : HasProd f a L) : Multipl
iable f L
· 使用定理 `HasProd.hasProd_symmetricIco_of_hasProd_symmetricIcc`：∀ {α : Type u_1} {
f : ℤ → α} [inst : CommGroup α] [inst_1 : TopologicalSpace α] [ContinuousMul α] 
{a : α},   HasProd f a (SummationFilter.sy…
· 使用定理 `Multipliable.hasProd`：Multipliable.hasProd (ha : Multipliable f L) : Has
Prod f (∏'[L] b, f b) L
-/
lemma multipliable_symmetricIco_of_multipliable_symmetricIcc
    (hf : Multipliable f (symmetricIcc ℤ)) (hf2 : Tendsto (fun N : ℕ ↦ (f N)⁻¹) atTop (𝓝 1)) :
    Multipliable f (symmetricIco ℤ) :=
  (hf.hasProd.hasProd_symmetricIco_of_hasProd_symmetricIcc hf2).multipliable

@[to_additive]
/-
**SummationFilter.tprod_symmetricIcc_eq_tprod_symmetricIco** 是 Mathlib 中的一个引理，位于
命名空间 `SummationFilter`。
形式化陈述：tprod_symmetricIcc_eq_tprod_symmetricIco [T2Space α] (hf : Multipliable f 
(symmetricIcc Int)) (hf2 : Tendsto (fun N : Nat => (f N)⁻¹) atTop (𝓝 1)) : ∏'[sy
mmetricIco Int] b, f b = ∏'[symmetricIcc Int] b, f b
参数：hf : Multipliable f (symmetricIcc Int)；hf2 : Tendsto (fun N : Nat => (f N)⁻¹)
 atTop (𝓝 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasProd.tprod_eq`：HasProd.tprod_eq (ha : HasProd f a L) : ∏'[L] b, f b =
 a
· 使用定理 `SummationFilter.instNeBotSymmetricIco`：∀ (G : Type u_1) [inst : Neg G] [
inst_1 : Preorder G] [inst_2 : LocallyFiniteOrder G] [Filter.atTop.NeBot],   (Su
mmationFilter.symmetricIco …
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanInt`：Archimedean ℤ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `HasProd.hasProd_symmetricIco_of_hasProd_symmetricIcc`：∀ {α : Type u_1} {
f : ℤ → α} [inst : CommGroup α] [inst_1 : TopologicalSpace α] [ContinuousMul α] 
{a : α},   HasProd f a (SummationFilter.sy…
· 使用定理 `Multipliable.hasProd`：Multipliable.hasProd (ha : Multipliable f L) : Has
Prod f (∏'[L] b, f b) L
-/
lemma tprod_symmetricIcc_eq_tprod_symmetricIco [T2Space α]
    (hf : Multipliable f (symmetricIcc ℤ)) (hf2 : Tendsto (fun N : ℕ ↦ (f N)⁻¹) atTop (𝓝 1)) :
    ∏'[symmetricIco ℤ] b, f b = ∏'[symmetricIcc ℤ] b, f b :=
  (hf.hasProd.hasProd_symmetricIco_of_hasProd_symmetricIcc hf2).tprod_eq

@[to_additive]
/-
**SummationFilter.hasProd_symmetricIcc_iff** 是 Mathlib 中的一个引理，位于命名空间 `SummationF
ilter`。
形式化陈述：hasProd_symmetricIcc_iff {α : Type*} [CommMonoid α] [TopologicalSpace α] {
f : Int -> α} {a : α} : HasProd f a (symmetricIcc Int) ↔ Tendsto (fun N : Nat =>
 ∏ n in Icc (-(N : Int)) N, f n) atTop (𝓝 a)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.map_map`：map_map : Filter.map m' (Filter.map m f) = Filter.map (m
' ∘ m) f
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma hasProd_symmetricIcc_iff {α : Type*} [CommMonoid α] [TopologicalSpace α]
    {f : ℤ → α} {a : α} : HasProd f a (symmetricIcc ℤ) ↔
    Tendsto (fun N : ℕ ↦ ∏ n ∈ Icc (-(N : ℤ)) N, f n) atTop (𝓝 a) := by
  simp [HasProd, symmetricIcc, ← Nat.map_cast_int_atTop, comp_def]

@[to_additive]
/-
**SummationFilter.hasProd_symmetricIco_int_iff** 是 Mathlib 中的一个引理，位于命名空间 `Summat
ionFilter`。
形式化陈述：hasProd_symmetricIco_int_iff {α : Type*} [CommMonoid α] [TopologicalSpace 
α] {f : Int -> α} {a : α} : HasProd f a (symmetricIco Int) ↔ Tendsto (fun N : Na
t => ∏ n in Ico (-(N : Int)) (N : Int), f n) atTop (𝓝 a)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.map_map`：map_map : Filter.map m' (Filter.map m f) = Filter.map (m
' ∘ m) f
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma hasProd_symmetricIco_int_iff {α : Type*} [CommMonoid α] [TopologicalSpace α]
    {f : ℤ → α} {a : α} : HasProd f a (symmetricIco ℤ) ↔
    Tendsto (fun N : ℕ ↦ ∏ n ∈ Ico (-(N : ℤ)) (N : ℤ), f n) atTop (𝓝 a) := by
  simp [HasProd, symmetricIco, ← Nat.map_cast_int_atTop, comp_def]

@[to_additive]
/-
**SummationFilter.hasProd_symmetricIoc_int_iff** 是 Mathlib 中的一个引理，位于命名空间 `Summat
ionFilter`。
形式化陈述：hasProd_symmetricIoc_int_iff {α : Type*} [CommMonoid α] [TopologicalSpace 
α] {f : Int -> α} {a : α} : HasProd f a (symmetricIoc Int) ↔ Tendsto (fun N : Na
t => ∏ n in Ioc (-(N : Int)) (N : Int), f n) atTop (𝓝 a)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.map_map`：map_map : Filter.map m' (Filter.map m f) = Filter.map (m
' ∘ m) f
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma hasProd_symmetricIoc_int_iff {α : Type*} [CommMonoid α] [TopologicalSpace α]
    {f : ℤ → α} {a : α} : HasProd f a (symmetricIoc ℤ) ↔
    Tendsto (fun N : ℕ ↦ ∏ n ∈ Ioc (-(N : ℤ)) (N : ℤ), f n) atTop (𝓝 a) := by
  simp [HasProd, symmetricIoc, ← Nat.map_cast_int_atTop, comp_def]
/-
**SummationFilter._root_.Summable.tendsto_zero_of_even_summable_symmetricIcc** 是
 Mathlib 中的一个引理，位于命名空间 `SummationFilter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Summable.tendsto_zero_of_even_summable_symmetricIcc {F : Type*} [NormedAddCommGroup F]
    [NormSMulClass ℤ F] {f : ℤ → F} (hf : Summable f (symmetricIcc ℤ)) (hs : f.Even) :
    Tendsto f atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  obtain ⟨L, hL⟩ := hf
  rw [HasSum, symmetricIcc_filter, tendsto_map'_iff, Function.comp_def] at hL
  have := hL.sub (hL.comp (tendsto_atTop_add_const_right _ (-1) tendsto_id))
  simp only [id_eq, Int.reduceNeg, Function.comp_apply, sub_self, ← sub_eq_add_neg] at this
  rw [tendsto_zero_iff_norm_tendsto_zero] at this
  refine (mul_zero (_ : ℝ) ▸ this.const_mul 2⁻¹).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with x hx
  have : Finset.Icc (-x) x = Icc (-(x - 1)) (x - 1) ∪ {-x, x} := by
    lift x to ℕ using by positivity
    convert! Finset.Icc_succ_succ (x - 1) (x - 1) <;> grind
  rw [this, Finset.sum_union, Finset.sum_insert, Finset.sum_singleton,
    hs x, add_comm, add_sub_cancel_right, ← two_zsmul, norm_smul, Int.norm_eq_abs,
    Int.cast_two, abs_two, inv_mul_cancel_left₀ two_ne_zero] <;>
  · simp only [disjoint_iff_ne, mem_insert, mem_singleton, mem_Icc]
    omega

end Int

end SummationFilter

