/-
Copyright (c) 2021 Alex J. Best. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best
-/
module

public import Mathlib.Analysis.Convex.Body
public import Mathlib.Analysis.Convex.Measure
public import Mathlib.MeasureTheory.Group.FundamentalDomain

/-!
# Geometry of numbers

In this file we prove some of the fundamental theorems in the geometry of numbers, as studied by
Hermann Minkowski.

## Main results

* `exists_pair_mem_lattice_not_disjoint_vadd`: Blichfeldt's principle, existence of two distinct
  points in a subgroup such that the translates of a set by these two points are not disjoint when
  the covolume of the subgroup is larger than the volume of the set.
* `exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure`: Minkowski's theorem, existence of
  a non-zero lattice point inside a convex symmetric domain of large enough volume.

## TODO

* Calculate the volume of the fundamental domain of a finite index subgroup
* Voronoi diagrams
* See [Pete L. Clark, *Abstract Geometry of Numbers: Linear Forms* (arXiv)](https://arxiv.org/abs/1405.2119)
  for some more ideas.

## References

* [Pete L. Clark, *Geometry of Numbers with Applications to Number Theory*][clark_gon] p.28
-/

public section


namespace MeasureTheory

open ENNReal Module MeasureTheory MeasureTheory.Measure Set Filter

open scoped Pointwise NNReal

variable {E L : Type*} [MeasurableSpace E] {μ : Measure E} {F s : Set E}

/-- **Blichfeldt's Theorem**. If the volume of the set `s` is larger than the covolume of the
countable subgroup `L` of `E`, then there exist two distinct points `x, y ∈ L` such that `(x + s)`
and `(y + s)` are not disjoint. -/
/-
**MeasureTheory.exists_pair_mem_lattice_not_disjoint_vadd** 是 Mathlib 中的一个定理，位于命
名空间 `MeasureTheory`。
形式化陈述：exists_pair_mem_lattice_not_disjoint_vadd [AddGroup L] [Countable L] [AddA
ction L E] [MeasurableSpace L] [MeasurableVAdd L E] [VAddInvariantMeasure L E μ]
 (fund : IsAddFundamentalDomain L F μ) (hS : NullMeasurableSet s μ) (h : μ F < μ
 s) : exists x y : L, x != y ∧ ¬Disjoint (x +ᵥ s) (y +ᵥ s)
参数：fund : IsAddFundamentalDomain L F μ；hS : NullMeasurableSet s μ；h : μ F < μ s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `Eq.trans_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ c →
 a ≤ c
· 使用定理 `MeasureTheory.IsAddFundamentalDomain.measure_eq_tsum`：∀ {G : Type u_1} {
α : Type u_3} [inst : AddGroup G] [inst_1 : AddAction G α] [inst_2 : MeasurableS
pace α] {s : Set α}   {μ : MeasureTheory.M…
· 使用定理 `MeasurableVAdd.toMeasurableConstVAdd`：∀ {M : Type u_2} {α : Type u_3} {i
nst : VAdd M α} {inst_1 : MeasurableSpace M} {inst_2 : MeasurableSpace α}   [sel
f : MeasurableVAdd M α], M…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.measure_iUnion₀`：measure_iUnion₀ [Countable ι] {f : ι -> S
et α} (hd : Pairwise (AEDisjoint μ on f)) (h : forall i, NullMeasurableSet (f i)
 μ) : μ (⋃ i, f i) …
· 使用定理 `Pairwise.mono`：Pairwise.mono (h : t subseteq s) (hs : s.Pairwise r) : t.
Pairwise r
· 使用定理 `Disjoint.aedisjoint`：∀ {α : Type u_2} {m : MeasurableSpace α} {μ : Measu
reTheory.Measure α} {s t : Set α},   Disjoint s t → MeasureTheory.AEDisjoint μ s
 t
· 使用定理 `Disjoint.mono`：Disjoint.mono {x y : Perm α} (h : Disjoint f g) (hf : x.s
upport <= f.support) (hg : y.support <= g.support) : Disjoint x y
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `MeasureTheory.NullMeasurableSet.inter`：∀ {α : Type u_2} {m0 : Measurable
Space α} {μ : MeasureTheory.Measure α} {s t : Set α},   MeasureTheory.NullMeasur
ableSet s μ → MeasureTheory…
· 使用定理 `MeasureTheory.NullMeasurableSet.vadd`：∀ {G : Type u} {α : Type w} {m : M
easurableSpace α} [inst : AddGroup G] [inst_1 : AddAction G α]   {μ : MeasureThe
ory.Measure α} [MeasureThe…
· 使用定理 `MeasureTheory.IsAddFundamentalDomain.nullMeasurableSet`：∀ {G : Type u_1}
 {α : Type u_2} [inst : Zero G] [inst_1 : VAdd G α] [inst_2 : MeasurableSpace α]
 {s : Set α}   {μ : autoParam (MeasureTheory…
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.iUnion_subset`：iUnion_subset {s : ι -> Set α} {t : Set α} (h : foral
l i, s i subseteq t) : ⋃ i, s i subseteq t
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t

--- 原说明 ---
**Blichfeldt's Theorem**. If the volume of the set `s` is larger than the covolu
me of the
countable subgroup `L` of `E`, then there exist two distinct points `x, y ∈ L` s
uch that `(x + s)`
and `(y + s)` are not disjoint.
-/
theorem exists_pair_mem_lattice_not_disjoint_vadd [AddGroup L] [Countable L] [AddAction L E]
    [MeasurableSpace L] [MeasurableVAdd L E] [VAddInvariantMeasure L E μ]
    (fund : IsAddFundamentalDomain L F μ) (hS : NullMeasurableSet s μ) (h : μ F < μ s) :
    ∃ x y : L, x ≠ y ∧ ¬Disjoint (x +ᵥ s) (y +ᵥ s) := by
  contrapose! h
  exact ((fund.measure_eq_tsum _).trans (measure_iUnion₀
    (Pairwise.mono h fun i j hij => (hij.mono inf_le_left inf_le_left).aedisjoint)
      fun _ => (hS.vadd _).inter fund.nullMeasurableSet).symm).trans_le
      (measure_mono <| Set.iUnion_subset fun _ => Set.inter_subset_right)

/-- The **Minkowski Convex Body Theorem**. If `s` is a convex symmetric domain of `E` whose volume
is large enough compared to the covolume of a lattice `L` of `E`, then it contains a non-zero
lattice point of `L`. -/
/-
**MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure** 是
 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure [NormedAddCom
mGroup E] [NormedSpace Real E] [BorelSpace E] [FiniteDimensional Real E] [IsAddH
aarMeasure μ] {L : AddSubgroup E} [Countable L] (fund : IsAddFundamentalDomain L
 F μ) (h_symm : forall x in s, -x in s) (h_conv : Convex Real s) (h : μ F * 2 ^ 
finrank Real E < μ s) : exists x != 0, ((x : L) : E) in s
参数：fund : IsAddFundamentalDomain L F μ；h_symm : forall x in s, -x in s；h_conv : 
Convex Real s；h : μ F * 2 ^ finrank Real E < μ s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.addHaar_smul_of_nonneg`：addHaar_smul_of_nonneg {r 
: Real} (hr : 0 <= r) (s : Set E) : μ (r • s) = ENNReal.ofReal (r ^ finrank Real
 E) * μ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.mul_lt_mul_iff_left`：∀ {a b c : ENNReal}, c ≠ 0 → c ≠ ⊤ → (a * c
 < b * c ↔ a < b)
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `ENNReal.instNoZeroDivisors`：NoZeroDivisors ENNReal
· 使用引理 `two_ne_zero'`：two_ne_zero' [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用引理 `ENNReal.pow_ne_top`：pow_ne_top (ha : a != ∞) : a ^ n != ∞
· 使用引理 `ENNReal.ofNat_ne_top`：ofNat_ne_top {n : Nat} [Nat.AtLeastTwo n] : ofNat(
n) != ∞
· 使用定理 `mul_right_comm`：mul_right_comm (a b c : G) : a * b * c = a * c * b
· 使用定理 `ENNReal.ofReal_pow`：ofReal_pow {p : Real} (hp : 0 <= p) (n : Nat) : ENNR
eal.ofReal (p ^ n) = ENNReal.ofReal p ^ n
· 使用定理 `ENNReal.ofReal_inv_of_pos`：ofReal_inv_of_pos {x : Real} (hx : 0 < x) : E
NNReal.ofReal x⁻¹ = (ENNReal.ofReal x)⁻¹
· 使用定理 `zero_lt_two`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : Part
ialOrder α] [ZeroLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 2
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ENNReal.ofReal_ofNat`：∀ (n : ℕ) [inst : n.AtLeastTwo], ENNReal.ofReal (O
fNat.ofNat n) = OfNat.ofNat n
· 使用定理 `ENNReal.inv_mul_cancel`：∀ {a : ENNReal}, a ≠ 0 → a ≠ ⊤ → a⁻¹ * a = 1
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
（共 63 条，此处仅展示前 30 条）

--- 原说明 ---
The **Minkowski Convex Body Theorem**. If `s` is a convex symmetric domain of `E
` whose volume
is large enough compared to the covolume of a lattice `L` of `E`, then it contai
ns a non-zero
lattice point of `L`.
-/
theorem exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure [NormedAddCommGroup E]
    [NormedSpace ℝ E] [BorelSpace E] [FiniteDimensional ℝ E] [IsAddHaarMeasure μ]
    {L : AddSubgroup E} [Countable L] (fund : IsAddFundamentalDomain L F μ)
    (h_symm : ∀ x ∈ s, -x ∈ s) (h_conv : Convex ℝ s) (h : μ F * 2 ^ finrank ℝ E < μ s) :
    ∃ x ≠ 0, ((x : L) : E) ∈ s := by
  have h_vol : μ F < μ ((2⁻¹ : ℝ) • s) := by
    rw [addHaar_smul_of_nonneg μ (by simp : 0 ≤ (2 : ℝ)⁻¹) s,
      ← ENNReal.mul_lt_mul_iff_left (pow_ne_zero (finrank ℝ E) (two_ne_zero' _)) (by finiteness),
      mul_right_comm, ofReal_pow (by simp : 0 ≤ (2 : ℝ)⁻¹), ofReal_inv_of_pos zero_lt_two]
    simpa [← mul_pow, ENNReal.inv_mul_cancel two_ne_zero ofNat_ne_top]
  obtain ⟨x, y, hxy, h⟩ :=
    exists_pair_mem_lattice_not_disjoint_vadd fund ((h_conv.smul _).nullMeasurableSet _) h_vol
  obtain ⟨_, ⟨v, hv, rfl⟩, w, hw, hvw⟩ := Set.not_disjoint_iff.mp h
  refine ⟨x - y, sub_ne_zero.2 hxy, ?_⟩
  rw [Set.mem_inv_smul_set_iff₀ (two_ne_zero' ℝ)] at hv hw
  simp_rw [AddSubgroup.vadd_def, vadd_eq_add, add_comm _ w, ← sub_eq_sub_iff_add_eq_add, ←
    AddSubgroup.coe_sub] at hvw
  rw [← hvw, ← inv_smul_smul₀ (two_ne_zero' ℝ) (_ - _), smul_sub, sub_eq_add_neg, smul_add]
  refine h_conv hw (h_symm _ hv) ?_ ?_ ?_ <;> norm_num

/-- The **Minkowski Convex Body Theorem for compact domain**. If `s` is a convex compact symmetric
domain of `E` whose volume is large enough compared to the covolume of a lattice `L` of `E`, then it
contains a non-zero lattice point of `L`. Compared to
`exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure`, this version requires in addition
that `s` is compact and `L` is discrete but provides a weaker inequality rather than a strict
inequality. -/
/-
**MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure** 是
 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure [NormedAddCom
mGroup E] [NormedSpace Real E] [BorelSpace E] [FiniteDimensional Real E] [Nontri
vial E] [IsAddHaarMeasure μ] {L : AddSubgroup E} [Countable L] [DiscreteTopology
 L] (fund : IsAddFundamentalDomain L F μ) (h_symm : forall x in s, -x in s) (h_c
onv : Convex Real s) (h_cpt : IsCompact s) (h : μ F * 2 ^ finrank Real E <= μ s)
 : exists x != 0, ((x : L) : E) in s
参数：fund : IsAddFundamentalDomain L F μ；h_symm : forall x in s, -x in s；h_conv : 
Convex Real s；h_cpt : IsCompact s；h : μ F * 2 ^ finrank Real E <= μ s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `MeasureTheory.IsAddFundamentalDomain.measure_ne_zero`：∀ {G : Type u_1} {
α : Type u_3} [inst : AddGroup G] [inst_1 : AddAction G α] [inst_2 : MeasurableS
pace α] {s : Set α}   {μ : MeasureTheory.M…
· 使用定理 `MeasureTheory.Subgroup.vaddInvariantMeasure`：∀ {G : Type u_3} {α : Type 
u_4} [inst : AddGroup G] [inst_1 : AddAction G α] [inst_2 : MeasurableSpace α]  
 {μ : MeasureTheory.Measure α} [M…
· 使用定理 `MeasureTheory.Measure.IsAddLeftInvariant.vaddInvariantMeasure`：∀ {G : Ty
pe u_1} [inst : MeasurableSpace G] {μ : MeasureTheory.Measure G} [inst_1 : Add G
] [μ.IsAddLeftInvariant],   MeasureTheory.VAddInvar…
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsAddLeftInvariant`：∀ {G : Type
 u_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpac
e G}   {μ : MeasureTheory.Measure G} [self : μ.Is…
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用定理 `MeasureTheory.Measure.instNeZeroOfNonempty`：∀ {X : Type u_1} [inst : Top
ologicalSpace X] {m : MeasurableSpace X} (μ : MeasureTheory.Measure X) [μ.IsOpen
PosMeasure]   [Nonempty X], NeZe…
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.toIsOpenPosMeasure`：∀ {G : Type u
_3} {inst : AddGroup G} {inst_1 : TopologicalSpace G} {inst_2 : MeasurableSpace 
G}   {μ : MeasureTheory.Measure G} [self : μ.Is…
· 使用定理 `Nontrivial.to_nonempty`：∀ {α : Type u_1} [Nontrivial α], Nonempty α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `ENNReal.instNoZeroDivisors`：NoZeroDivisors ENNReal
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `ENNReal.instNontrivial`：Nontrivial ENNReal
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `MeasureTheory.nonempty_of_measure_ne_zero`：nonempty_of_measure_ne_zero (
h : μ s != 0) : s.Nonempty
· 使用定理 `exists_seq_strictAnti_tendsto`：exists_seq_strictAnti_tendsto [DenselyOrd
ered α] [NoMaxOrder α] [FirstCountableTopology α] (x : α) : exists u : Nat -> α,
 StrictAnti u ∧ (fo…
· 使用定理 `NNReal.instOrderTopology`：OrderTopology NNReal
· 使用定理 `NNReal.instDenselyOrdered`：DenselyOrdered NNReal
· 使用定理 `IsStrictOrderedRing.toNoMaxOrder`：∀ {R : Type u} [inst : Semiring R] [in
st_1 : PartialOrder R] [IsStrictOrderedRing R], NoMaxOrder R
· 使用定理 `NNReal.instIsStrictOrderedRing_1`：IsStrictOrderedRing NNReal
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.firstCountableTopology`：∀ {X : Ty
pe u_2} [inst : TopologicalSpace X] [h : TopologicalSpace.PseudoMetrizableSpace 
X], FirstCountableTopology X
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
（共 105 条，此处仅展示前 30 条）

--- 原说明 ---
The **Minkowski Convex Body Theorem for compact domain**. If `s` is a convex com
pact symmetric
domain of `E` whose volume is large enough compared to the covolume of a lattice
 `L` of `E`, then it
contains a non-zero lattice point of `L`. Compared to
`exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure`, this version req
uires in addition
that `s` is compact and `L` is discrete but provides a weaker inequality rather 
than a strict
inequality.
-/
theorem exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure [NormedAddCommGroup E]
    [NormedSpace ℝ E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E] [IsAddHaarMeasure μ]
    {L : AddSubgroup E} [Countable L] [DiscreteTopology L] (fund : IsAddFundamentalDomain L F μ)
    (h_symm : ∀ x ∈ s, -x ∈ s) (h_conv : Convex ℝ s) (h_cpt : IsCompact s)
    (h : μ F * 2 ^ finrank ℝ E ≤ μ s) :
    ∃ x ≠ 0, ((x : L) : E) ∈ s := by
  have h_mes : μ s ≠ 0 := fun hμ ↦ fund.measure_ne_zero (NeZero.ne μ) <| by simpa [hμ] using h
  have h_nemp : s.Nonempty := nonempty_of_measure_ne_zero h_mes
  let u : ℕ → ℝ≥0 := (exists_seq_strictAnti_tendsto 0).choose
  let K : ConvexBody E := ⟨s, h_conv, h_cpt, h_nemp⟩
  let S : ℕ → ConvexBody E := fun n => (1 + u n) • K
  let Z : ℕ → Set E := fun n => (S n) ∩ (L \ {0})
  -- The convex bodies `S n` have volume strictly larger than `μ s` and thus we can apply
  -- `exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure` to them and obtain that
  -- `S n` contains a nonzero point of `L`. Since the intersection of the `S n` is equal to `s`,
  -- it follows that `s` contains a nonzero point of `L`.
  have h_zero : 0 ∈ K := K.zero_mem_of_symmetric h_symm
  suffices Set.Nonempty (⋂ n, Z n) by
    simp_rw [Z, S, ConvexBody.coe_smul', NNReal.smul_def, ← Set.iInter_inter, NNReal.coe_add,
      NNReal.coe_one] at this
    rw [K.iInter_smul_eq_self h_zero] at this
    · obtain ⟨x, hx⟩ := this
      exact ⟨⟨x, by simp_all⟩, by aesop⟩
    · exact (exists_seq_strictAnti_tendsto (0 : ℝ≥0)).choose_spec.2.2
  have h_clos : IsClosed ((L : Set E) \ {0}) := by
    rsuffices ⟨U, hU⟩ : ∃ U : Set E, IsOpen U ∧ U ∩ L = {0}
    · rw [sdiff_eq_sdiff_iff_inf_eq_inf (z := U).mpr (by simp [Set.inter_comm .. ▸ hU.2, zero_mem])]
      exact AddSubgroup.isClosed_of_discrete.sdiff hU.1
    exact isOpen_inter_eq_singleton_of_mem_discrete ⟨inferInstance⟩ (zero_mem L)
  refine IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed Z (fun n => ?_)
    (fun n => ?_) ((S 0).isCompact.inter_right h_clos) (fun n => (S n).isClosed.inter h_clos)
  · refine Set.inter_subset_inter_left _ (SetLike.coe_subset_coe.mpr ?_)
    refine ConvexBody.smul_le_of_le K h_zero ?_
    rw [add_le_add_iff_left]
    exact le_of_lt <| (exists_seq_strictAnti_tendsto (0 : ℝ≥0)).choose_spec.1 (Nat.lt_add_one n)
  · suffices μ F * 2 ^ finrank ℝ E < μ (S n : Set E) by
      have h_symm' : ∀ x ∈ S n, -x ∈ S n := by
        rintro _ ⟨y, hy, rfl⟩
        exact ⟨-y, h_symm _ hy, by simp⟩
      obtain ⟨x, hx_nz, hx_mem⟩ := exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
        fund h_symm' (S n).convex this
      exact ⟨x, hx_mem, by simp_all⟩
    refine lt_of_le_of_lt h ?_
    rw [ConvexBody.coe_smul', NNReal.smul_def, addHaar_smul_of_nonneg _ (NNReal.coe_nonneg _)]
    rw [show μ s < _ ↔ 1 * μ s < _ by rw [one_mul]]
    dsimp [K]
    gcongr
    · exact h_cpt.measure_ne_top
    rw [ofReal_pow (by positivity)]
    refine one_lt_pow₀ ?_ (ne_of_gt finrank_pos)
    simp [u, (exists_seq_strictAnti_tendsto (0 : ℝ≥0)).choose_spec.2.1 n]

end MeasureTheory

