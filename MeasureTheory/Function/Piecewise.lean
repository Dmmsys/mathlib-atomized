/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Data.Setoid.Partition
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable

/-!
# Measurability of piecewise functions

In this file, we prove some results about measurability of functions defined by using
`IndexedPartition.piecewise`.

-/

@[expose] public section

open MeasureTheory Set Filter

namespace IndexedPartition

variable {ι α β : Type*} [MeasurableSpace α] {s : ι → Set α} {f : ι → α → β}

@[fun_prop]
/-
**IndexedPartition.measurable_piecewise** 是 Mathlib 中的一个定理，位于命名空间 `IndexedPartit
ion`。
形式化陈述：measurable_piecewise [MeasurableSpace β] [Countable ι] (hs : IndexedPartit
ion s) (hm : forall i, MeasurableSet (s i)) (hf : forall i, Measurable (f i)) : 
Measurable (hs.piecewise f)
参数：hs : IndexedPartition s；hm : forall i, MeasurableSet (s i)；hf : forall i, Mea
surable (f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IndexedPartition.piecewise_preimage`：piecewise_preimage (f : ι -> α -> β
) (t : Set β) : hs.piecewise f ⁻¹' t = ⋃ i, s i inter (f i ⁻¹' t)
· 使用定理 `MeasurableSet.iUnion`：∀ {α : Type u_1} {ι : Sort u_6} {m : MeasurableSpa
ce α} [Countable ι] ⦃f : ι → Set α⦄,   (∀ (b : ι), MeasurableSet (f b)) → Measur
ableSet (⋃…
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
-/
theorem measurable_piecewise [MeasurableSpace β] [Countable ι]
    (hs : IndexedPartition s) (hm : ∀ i, MeasurableSet (s i)) (hf : ∀ i, Measurable (f i)) :
    Measurable (hs.piecewise f) :=
  fun t ht => by simpa [piecewise_preimage] using .iUnion (fun i => (hm i).inter ((hf i) ht))

@[fun_prop]
/-
**IndexedPartition.aemeasurable_piecewise** 是 Mathlib 中的一个定理，位于命名空间 `IndexedPart
ition`。
形式化陈述：aemeasurable_piecewise {μ : Measure α} [MeasurableSpace β] [Countable ι] (
hs : IndexedPartition s) (hm : forall i, MeasurableSet (s i)) (hf : forall i, AE
Measurable (f i) μ) : AEMeasurable (hs.piecewise f) μ
参数：hs : IndexedPartition s；hm : forall i, MeasurableSet (s i)；hf : forall i, AEM
easurable (f i) μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `IndexedPartition.measurable_piecewise`：measurable_piecewise [MeasurableS
pace β] [Countable ι] (hs : IndexedPartition s) (hm : forall i, MeasurableSet (s
 i)) (hf : forall i, Measur…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.ae_all_iff`：ae_all_iff {ι : Sort*} [Countable ι] {p : α ->
 ι -> Prop} : (forallᵐ a ∂μ, forall i, p a i) ↔ forall i, forallᵐ a ∂μ, p a i
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem aemeasurable_piecewise {μ : Measure α} [MeasurableSpace β] [Countable ι]
    (hs : IndexedPartition s) (hm : ∀ i, MeasurableSet (s i)) (hf : ∀ i, AEMeasurable (f i) μ) :
    AEMeasurable (hs.piecewise f) μ := by
  choose p hp hq using hf
  refine ⟨hs.piecewise p, hs.measurable_piecewise hm hp, ?_⟩
  filter_upwards [ae_all_iff.2 hq] with x hx using hx (hs.index x)

/-- This is the analogue of `SimpleFunc.piecewise` for `IndexedPartition`. -/
/-
**IndexedPartition.simpleFunc_piecewise** 是 Mathlib 中的一个定义，位于命名空间 `IndexedPartit
ion`。
形式化陈述：simpleFunc_piecewise [Finite ι] (hs : IndexedPartition s) (hm : forall i, 
MeasurableSet (s i)) (f : ι -> SimpleFunc α β) : SimpleFunc α β where toFun
参数：hs : IndexedPartition s；hm : forall i, MeasurableSet (s i)；f : ι -> SimpleFun
c α β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is the analogue of `SimpleFunc.piecewise` for `IndexedPartition`.
-/
def simpleFunc_piecewise [Finite ι] (hs : IndexedPartition s)
    (hm : ∀ i, MeasurableSet (s i)) (f : ι → SimpleFunc α β) : SimpleFunc α β where
  toFun := hs.piecewise (fun i => f i)
  measurableSet_fiber' := fun _ =>
    letI : MeasurableSpace β := ⊤
    hs.measurable_piecewise hm (fun i => (f i).measurable) trivial
  finite_range' := (finite_iUnion (fun i => (f i).finite_range)).subset
    (hs.range_piecewise_subset _)

@[fun_prop]
/-
**IndexedPartition.stronglyMeasurable_piecewise** 是 Mathlib 中的一个定理，位于命名空间 `Index
edPartition`。
形式化陈述：stronglyMeasurable_piecewise [Countable ι] (hs : IndexedPartition s) (hm :
 forall i, MeasurableSet (s i)) [TopologicalSpace β] (hf : forall i, StronglyMea
surable (f i)) : StronglyMeasurable (hs.piecewise f)
参数：hs : IndexedPartition s；hm : forall i, MeasurableSet (s i)；hf : forall i, Str
onglyMeasurable (f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `exists_true_iff_nonempty`：exists_true_iff_nonempty {α : Sort*} : (exists
 _ : α, True) ↔ Nonempty α
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `instInfiniteNat`：Infinite ℕ
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `MeasurableSet.biUnion`：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSp
ace α} {f : β → Set α} {s : Set β},   s.Countable → (∀ b ∈ s, MeasurableSet (f b
)) → Measur…
· 使用定理 `Set.to_countable`：to_countable (s : Set α) [Countable s] : s.Countable
· 使用定理 `SetCoe.countable`：∀ {α : Type u} [Countable α] (s : Set α), Countable ↑s
· 使用定理 `Equiv.bijective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijec
tive ⇑e
· 使用引理 `Filter.eventually_atTop`：eventually_atTop : (forallᶠ x in atTop, p x) ↔ 
exists a, forall b, a <= b -> p b
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `EmbeddingLike.apply_eq_iff_eq`：apply_eq_iff_eq (f : F) {x y : α} : f x =
 f y ↔ x = y
（共 41 条，此处仅展示前 30 条）
-/
theorem stronglyMeasurable_piecewise [Countable ι] (hs : IndexedPartition s)
    (hm : ∀ i, MeasurableSet (s i)) [TopologicalSpace β] (hf : ∀ i, StronglyMeasurable (f i)) :
    StronglyMeasurable (hs.piecewise f) := by
  by_cases Fi : Finite ι
  · refine ⟨fun n => simpleFunc_piecewise hs hm (fun i => (hf i).approx n), fun x => ?_⟩
    simp [simpleFunc_piecewise, piecewise_apply, StronglyMeasurable.tendsto_approx]
  simp only [not_finite_iff_infinite] at Fi
  obtain ⟨e, -⟩ := exists_true_iff_nonempty.mpr (nonempty_equiv_of_countable (α := ℕ) (β := ι))
  classical
  let g (n : ℕ) (i : ι) : Fin (n + 1) :=
    if hi : ∃ m < n, i = e m then ⟨hi.choose, by grind⟩ else Fin.last n
  have sg (n : ℕ) : (g n).Surjective := by
    intro b
    unfold g
    refine ⟨e b, ?_⟩
    by_cases hb : b < n
    · have : ∃ m < n, e b = e m := ⟨b, ⟨hb, rfl⟩⟩
      simpa only [this, Fin.ext_iff] using! e.injective this.choose_spec.2.symm
    · simp [hb]
      grind
  have G (n : ℕ) := hs.coarserPartition (g n) (sg n)
  refine ⟨fun n => (G n).simpleFunc_piecewise (fun i => ?_) (fun i => (hf (e i)).approx n),
    fun x => ?_⟩
  · exact .biUnion (to_countable _) fun _ _ ↦ hm _
  simp only [simpleFunc_piecewise, SimpleFunc.coe_mk, piecewise_apply]
  have : ∀ᶠ n in atTop, e ((G n).index x) = hs.index x := by
    obtain ⟨y, hy⟩ := e.bijective.2 (hs.index x)
    refine eventually_atTop.mpr ⟨y + 1, fun b hb => ?_⟩
    have : y = (⟨y, by lia⟩ : Fin (b + 1)).1 := rfl
    rw [← hy, EmbeddingLike.apply_eq_iff_eq, this, ← Fin.ext_iff, ← (G b).mem_iff_index_eq]
    have : ∃ m < b, hs.index x = e m := ⟨y, ⟨by lia, hy.symm⟩⟩
    simpa [g, hs.mem_iff_index_eq, this] using! e.injective (hy.trans this.choose_spec.2).symm
  have : ∀ᶠ n in atTop, (hf (hs.index x)).approx n x = (hf (e ((G n).index x))).approx n x := by
    filter_upwards [this] with n hn using by rw [hn]
  exact (Filter.tendsto_congr' this).mp (by simp [StronglyMeasurable.tendsto_approx])

@[fun_prop]
/-
**IndexedPartition.aestronglyMeasurable_piecewise** 是 Mathlib 中的一个定理，位于命名空间 `Ind
exedPartition`。
形式化陈述：aestronglyMeasurable_piecewise {μ : Measure α} [Countable ι] (hs : Indexed
Partition s) (hm : forall i, MeasurableSet (s i)) [TopologicalSpace β] (hf : for
all i, AEStronglyMeasurable (f i) μ) : AEStronglyMeasurable (hs.piecewise f) μ
参数：hs : IndexedPartition s；hm : forall i, MeasurableSet (s i)；hf : forall i, AES
tronglyMeasurable (f i) μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `IndexedPartition.stronglyMeasurable_piecewise`：stronglyMeasurable_piecew
ise [Countable ι] (hs : IndexedPartition s) (hm : forall i, MeasurableSet (s i))
 [TopologicalSpace β] (hf : forall …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.ae_all_iff`：ae_all_iff {ι : Sort*} [Countable ι] {p : α ->
 ι -> Prop} : (forallᵐ a ∂μ, forall i, p a i) ↔ forall i, forallᵐ a ∂μ, p a i
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem aestronglyMeasurable_piecewise {μ : Measure α} [Countable ι] (hs : IndexedPartition s)
    (hm : ∀ i, MeasurableSet (s i)) [TopologicalSpace β] (hf : ∀ i, AEStronglyMeasurable (f i) μ) :
    AEStronglyMeasurable (hs.piecewise f) μ := by
  choose p hp hq using hf
  refine ⟨hs.piecewise p, hs.stronglyMeasurable_piecewise hm hp, ?_⟩
  filter_upwards [ae_all_iff.2 hq] with x hx using hx (hs.index x)

end IndexedPartition

