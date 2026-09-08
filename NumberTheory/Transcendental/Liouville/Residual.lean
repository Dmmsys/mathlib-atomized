/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.NumberTheory.Transcendental.Liouville.Basic
public import Mathlib.Topology.Baire.Lemmas
public import Mathlib.Topology.Baire.LocallyCompactRegular
public import Mathlib.Topology.Instances.Irrational

/-!
# Density of Liouville numbers

In this file we prove that the set of Liouville numbers form a dense `Gδ` set. We also prove a
similar statement about irrational numbers.
-/

public section


open scoped Filter

open Filter Set Metric

/-
**setOfPred_liouville_eq_iInter_iUnion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：setOfPred_liouville_eq_iInter_iUnion : { x | Liouville x } = ⋂ n : Nat, ⋃ 
(a : Int) (b : Int) (_ : 1 < b), ball ((a : Real) / b) (1 / (b : Real) ^ n) \ {(
a : Real) / b}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem setOfPred_liouville_eq_iInter_iUnion :
    { x | Liouville x } =
      ⋂ n : ℕ, ⋃ (a : ℤ) (b : ℤ) (_ : 1 < b),
      ball ((a : ℝ) / b) (1 / (b : ℝ) ^ n) \ {(a : ℝ) / b} := by
  ext x
  simp only [mem_iInter, mem_iUnion, Liouville, mem_ofPred_eq, exists_prop, Set.mem_sdiff,
    mem_singleton_iff, mem_ball, Real.dist_eq, and_comm]

@[deprecated (since := "2026-07-09")]
alias setOf_liouville_eq_iInter_iUnion := setOfPred_liouville_eq_iInter_iUnion
/-
**IsG** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsGδ.setOfPred_liouville : IsGδ { x | Liouville x } := by
  rw [setOfPred_liouville_eq_iInter_iUnion]
  refine .iInter fun n => IsOpen.isGδ ?_
  refine isOpen_iUnion fun a => isOpen_iUnion fun b => isOpen_iUnion fun _hb => ?_
  exact isOpen_ball.inter isClosed_singleton.isOpen_compl

@[deprecated (since := "2026-07-09")]
alias IsGδ.setOf_liouville := IsGδ.setOfPred_liouville
/-
**setOfPred_liouville_eq_irrational_inter_iInter_iUnion** 是 Mathlib 中的一个定理，位于命名空
间 ``。
形式化陈述：setOfPred_liouville_eq_irrational_inter_iInter_iUnion : { x | Liouville x 
} = { x | Irrational x } inter ⋂ n : Nat, ⋃ (a : Int) (b : Int) (_ : 1 < b), bal
l (a / b) (1 / (b : Real) ^ n)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Set.subset_inter`：subset_inter {s t r : Set α} (rs : r subseteq s) (rt :
 r subseteq t) : r subseteq s inter t
· 使用定理 `Liouville.irrational`：∀ {x : ℝ}, Liouville x → Irrational x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `setOfPred_liouville_eq_iInter_iUnion`：setOfPred_liouville_eq_iInter_iUni
on : { x | Liouville x } = ⋂ n : Nat, ⋃ (a : Int) (b : Int) (_ : 1 < b), ball ((
a : Real) / b) (1 / (b : R…
· 使用定理 `Set.iInter_mono`：iInter_mono {s t : ι -> Set α} (h : forall i, s i subse
teq t i) : ⋂ i, s i subseteq ⋂ i, t i
· 使用定理 `Set.iUnion₂_mono`：iUnion₂_mono {s t : forall i, κ i -> Set α} (h : foral
l i j, s i j subseteq t i j) : ⋃ (i) (j), s i j subseteq ⋃ (i) (j), t i j
· 使用定理 `Set.iUnion_mono`：iUnion_mono {s t : ι -> Set α} (h : forall i, s i subse
teq t i) : ⋃ i, s i subseteq ⋃ i, t i
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.inter_iInter`：inter_iInter [Nonempty ι] (s : Set β) (t : ι -> Set β)
 : (s inter ⋂ i, t i) = ⋂ i, s inter t i
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.inter_iUnion`：inter_iUnion (s : Set β) (t : ι -> Set β) : (s inter ⋃
 i, t i) = ⋃ i, s inter t i
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `Set.sdiff_subset_sdiff`：sdiff_subset_sdiff {s₁ s₂ t₁ t₂ : Set α} : s₁ su
bseteq s₂ -> t₂ subseteq t₁ -> s₁ \ t₁ subseteq s₂ \ t₂
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
theorem setOfPred_liouville_eq_irrational_inter_iInter_iUnion :
    { x | Liouville x } =
      { x | Irrational x } ∩ ⋂ n : ℕ, ⋃ (a : ℤ) (b : ℤ) (_ : 1 < b),
      ball (a / b) (1 / (b : ℝ) ^ n) := by
  refine Subset.antisymm ?_ ?_
  · refine subset_inter (fun x hx => hx.irrational) ?_
    rw [setOfPred_liouville_eq_iInter_iUnion]
    exact iInter_mono fun n => iUnion₂_mono fun a b => iUnion_mono fun _hb => sdiff_subset
  · simp only [inter_iInter, inter_iUnion, setOfPred_liouville_eq_iInter_iUnion]
    refine iInter_mono fun n => iUnion₂_mono fun a b => iUnion_mono fun hb => ?_
    rw [inter_comm]
    exact sdiff_subset_sdiff Subset.rfl (singleton_subset_iff.2 ⟨a / b, by norm_cast⟩)

@[deprecated (since := "2026-07-09")]
alias setOf_liouville_eq_irrational_inter_iInter_iUnion :=
  setOfPred_liouville_eq_irrational_inter_iInter_iUnion

/-- The set of Liouville numbers is a residual set. -/
/-
**eventually_residual_liouville** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eventually_residual_liouville : forallᶠ x in residual Real, Liouville x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.Eventually.eq_1`：∀ {α : Type u_1} (p : α → Prop) (f : Filter α), 
Filter.Eventually p f = ({x | p x} ∈ f)
· 使用定理 `setOfPred_liouville_eq_irrational_inter_iInter_iUnion`：setOfPred_liouvil
le_eq_irrational_inter_iInter_iUnion : { x | Liouville x } = { x | Irrational x 
} inter ⋂ n : Nat, ⋃ (a : Int) (b : Int) (_…
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
· 使用定理 `eventually_residual_irrational`：eventually_residual_irrational : forallᶠ
 x in residual Real, Irrational x
· 使用定理 `residual_of_dense_Gδ`：residual_of_dense_Gδ {s : Set X} (ho : IsGδ s) (hd
 : Dense s) : s in residual X
· 使用定理 `IsGδ.iInter`：∀ {X : Type u_1} {ι' : Sort u_4} [inst : TopologicalSpace X
] [Countable ι'] {s : ι' → Set X},   (∀ (i : ι'), IsGδ (s i)) → IsGδ (⋂ i, s i)
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `IsOpen.isGδ`：IsOpen.isGδ {s : Set X} (h : IsOpen s) : IsGδ s
· 使用定理 `isOpen_iUnion`：isOpen_iUnion {f : ι -> Set X} (h : forall i, IsOpen (f i
)) : IsOpen (⋃ i, f i)
· 使用定理 `Metric.isOpen_ball`：∀ {α : Type u} [inst : PseudoMetricSpace α] {x : α} 
{ε : ℝ}, IsOpen (Metric.ball x ε)
· 使用定理 `Dense.mono`：Dense.mono (h : s₁ subseteq s₂) (hd : Dense s₁) : Dense s₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Rat.pos`：pos (a : Rat) : 0 < a.den
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Int.cast_mul`：cast_mul {α : Type*} [NonAssocRing α] : forall m n, ((m * 
n : Int) : α) = m * n
· 使用定理 `Int.cast_ofNat`：cast_ofNat (n : Nat) [n.AtLeastTwo] : ((ofNat(n) : Int) 
: R) = ofNat(n)
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Rat.divInt_mul_right`：∀ {n d a : ℤ}, a ≠ 0 → Rat.divInt (n * a) (d * a) 
= Rat.divInt n d
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
（共 49 条，此处仅展示前 30 条）

--- 原说明 ---
The set of Liouville numbers is a residual set.
-/
theorem eventually_residual_liouville : ∀ᶠ x in residual ℝ, Liouville x := by
  rw [Filter.Eventually, setOfPred_liouville_eq_irrational_inter_iInter_iUnion]
  refine eventually_residual_irrational.and ?_
  refine residual_of_dense_Gδ ?_ (Rat.isDenseEmbedding_coe_real.dense.mono ?_)
  · exact .iInter fun n => IsOpen.isGδ <|
          isOpen_iUnion fun a => isOpen_iUnion fun b => isOpen_iUnion fun _hb => isOpen_ball
  · rintro _ ⟨r, rfl⟩
    simp only [mem_iInter, mem_iUnion]
    refine fun n => ⟨r.num * 2, r.den * 2, ?_, ?_⟩
    · have := r.pos; lia
    · convert! @mem_ball_self ℝ _ (r : ℝ) _ _
      · push_cast
        -- Workaround for https://github.com/leanprover/lean4/pull/6438; this eliminates an
        -- `Expr.mdata` that would cause `norm_cast` to skip a numeral.
        rw [Eq.refl (2 : ℝ)]
        norm_cast
        simp [Rat.divInt_mul_right (two_ne_zero)]
      · refine one_div_pos.2 (pow_pos (Int.cast_pos.2 ?_) _)
        exact mul_pos (Int.natCast_pos.2 r.pos) zero_lt_two

/-- The set of Liouville numbers in dense. -/
/-
**dense_liouville** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dense_liouville : Dense { x | Liouville x }
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dense_of_mem_residual`：dense_of_mem_residual {s : Set X} (hs : s in resi
dual X) : Dense s
· 使用定理 `BaireSpace.of_t2Space_locallyCompactSpace`：∀ {X : Type u_1} [inst : Topo
logicalSpace X] [R1Space X] [LocallyCompactSpace X], BaireSpace X
· 使用定理 `instR1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [RegularSpace 
X], R1Space X
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.regularSpace`：∀ {X : Type u_2} [i
nst : TopologicalSpace X] [TopologicalSpace.PseudoMetrizableSpace X], RegularSpa
ce X
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `instProperSpaceReal`：ProperSpace ℝ
· 使用定理 `eventually_residual_liouville`：eventually_residual_liouville : forallᶠ x
 in residual Real, Liouville x

--- 原说明 ---
The set of Liouville numbers in dense.
-/
theorem dense_liouville : Dense { x | Liouville x } :=
  dense_of_mem_residual eventually_residual_liouville
