/-
Copyright (c) 2024 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.FieldTheory.Galois.GaloisClosure
public import Mathlib.Topology.Algebra.Group.ClosedSubgroup

/-!

# The Fundamental Theorem of Infinite Galois Theory

In this file, we prove the fundamental theorem of infinite Galois theory and the special case for
open subgroups and normal subgroups. We first verify that `IntermediateField.fixingSubgroup` and
`IntermediateField.fixedField` are inverses of each other between intermediate fields and
closed subgroups of the Galois group.

## Main definitions and results

In `K/k`, for any intermediate field `L` :

* `fixingSubgroup_isClosed` : the subgroup fixing `L` (`Gal(K/L)`) is closed.

* `fixedField_fixingSubgroup` : the field fixed by the
  subgroup fixing `L` is equal to `L` itself.

For any subgroup `H` of `Gal(K/k)` :

* `restrict_fixedField` : For a Galois intermediate field `M`, the fixed field of the image of `H`
  restricted to `M` is equal to the fixed field of `H` intersected with `M`.
* `fixingSubgroup_fixedField` : If `H` is closed, the fixing subgroup of the fixed field of `H`
  is equal to `H` itself.

The fundamental theorem of infinite Galois theory :

* `IntermediateFieldEquivClosedSubgroup` : The order equivalence is given by mapping any
  intermediate field `L` to the subgroup fixing `L`, and the inverse maps any
  closed subgroup of `Gal(K/k)` `H` to the fixed field of `H`. The composition is equal to
  the identity as described in the lemmas above, and compatibility with the order follows easily.

Special cases :

* `isOpen_iff_finite` : The fixing subgroup of an intermediate field `L` is open if and only if
  `L` is finite-dimensional.

* `normal_iff_isGalois` : The fixing subgroup of an intermediate field `L` is normal if and only if
  `L` is Galois.

-/

@[expose] public section

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

namespace InfiniteGalois

open scoped Pointwise
open FiniteGaloisIntermediateField AlgEquiv
--Note: The `adjoin`s below are `FiniteGaloisIntermediateField.adjoin`

/-
**InfiniteGalois.fixingSubgroup_isClosed** 是 Mathlib 中的一个引理，位于命名空间 `InfiniteGalo
is`。
形式化陈述：fixingSubgroup_isClosed (L : IntermediateField k K) [IsGalois k K] : IsClo
sed (L.fixingSubgroup : Set Gal(K/k)) where isOpen_compl
参数：L : IntermediateField k K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isOpen_iff_mem_nhds`：isOpen_iff_mem_nhds : IsOpen s ↔ forall x in s, s i
n 𝓝 x
· 使用定理 `mem_nhds_iff`：mem_nhds_iff : s in 𝓝 x ↔ exists t subseteq s, IsOpen t ∧ 
x in t
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.not_subset`：not_subset : ¬s subseteq t ↔ exists a in s, a ∉ t
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `mem_fixingSubgroup_iff`：mem_fixingSubgroup_iff {s : Set α} {m : M} : m i
n fixingSubgroup M s ↔ forall y in s, m • y = y
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Set.mem_smul_set`：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β] {t :
 Set β} {a : α} {x : β}, x ∈ a • t ↔ ∃ y ∈ t, a • y = x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `FiniteGaloisIntermediateField.adjoin_simple_le_iff`：adjoin_simple_le_iff
 [IsGalois k K] {x : K} {L : FiniteGaloisIntermediateField k K} : adjoin k {x} <
= L ↔ x in L.toIntermediateField
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `IsOpen.smul`：IsOpen.smul {s : Set α} (hs : IsOpen s) (c : G) : IsOpen (c
 • s)
· 使用定理 `instSeparatelyContinuousMulOfContinuousMul`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Mul M] [ContinuousMul M], SeparatelyContinuousMul M
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `instIsTopologicalGroupAlgEquiv`：∀ (K : Type u_1) (L : Type u_2) [inst : 
Field K] [inst_1 : Field L] [inst_2 : Algebra K L], IsTopologicalGroup Gal(L/K)
· 使用定理 `IntermediateField.fixingSubgroup_isOpen`：IntermediateField.fixingSubgrou
p_isOpen {K L : Type*} [Field K] [Field L] [Algebra K L] (E : IntermediateField 
K L) [FiniteDimensional K E] …
· 使用定理 `FiniteGaloisIntermediateField.instFiniteDimensionalSubtypeMemIntermediat
eField`：∀ (k : Type u_1) (K : Type u_2) [inst : Field k] [inst_1 : Field K] [ins
t_2 : Algebra k K]   (L : FiniteGaloisIntermediateField k K), Finite…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
-/
lemma fixingSubgroup_isClosed (L : IntermediateField k K) [IsGalois k K] :
    IsClosed (L.fixingSubgroup : Set Gal(K/k)) where
  isOpen_compl := isOpen_iff_mem_nhds.mpr fun σ h => by
    apply mem_nhds_iff.mpr
    rcases Set.not_subset.mp ((mem_fixingSubgroup_iff Gal(K/k)).not.mp h) with ⟨y, yL, ne⟩
    use σ • ((adjoin k {y}).1.fixingSubgroup : Set Gal(K/k))
    constructor
    · intro f hf
      rcases (Set.mem_smul_set.mp hf) with ⟨g, hg, eq⟩
      simp only [Set.mem_compl_iff, SetLike.mem_coe, ← eq]
      apply (mem_fixingSubgroup_iff Gal(K/k)).not.mpr
      push Not
      use y
      simp only [yL, smul_eq_mul, AlgEquiv.smul_def, AlgEquiv.mul_apply, ne_eq, true_and]
      have : g y = y := (mem_fixingSubgroup_iff Gal(K/k)).mp hg y <|
        adjoin_simple_le_iff.mp le_rfl
      simpa only [this, ne_eq, AlgEquiv.smul_def] using! ne
    · simp only [(IntermediateField.fixingSubgroup_isOpen (adjoin k {y}).1).smul σ, true_and]
      use 1
      simp only [SetLike.mem_coe, smul_eq_mul, mul_one, and_true, Subgroup.one_mem]
/-
**InfiniteGalois.fixedField_fixingSubgroup** 是 Mathlib 中的一个引理，位于命名空间 `InfiniteGa
lois`。
形式化陈述：fixedField_fixingSubgroup (L : IntermediateField k K) [IsGalois k K] : Int
ermediateField.fixedField L.fixingSubgroup = L
参数：L : IntermediateField k K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `IsGalois.tower_top_intermediateField`：∀ {F : Type u_1} {E : Type u_3} [i
nst : Field F] [inst_1 : Field E] [inst_2 : Algebra F E] (K : IntermediateField 
F E)   [IsGalois F E], IsG…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用引理 `FiniteGaloisIntermediateField.subset_adjoin`：subset_adjoin [IsGalois k K
] (s : Set K) [Finite s] : s subseteq (adjoin k s).toIntermediateField
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `IsGalois.tfae`：tfae [FiniteDimensional F E] : List.TFAE [ IsGalois F E, 
IntermediateField.fixedField (⊤ : Subgroup Gal(E/F)) = ⊥, Nat.card Gal(E/F) = fi
nra…
· 使用定理 `FiniteGaloisIntermediateField.instFiniteDimensionalSubtypeMemIntermediat
eField`：∀ (k : Type u_1) (K : Type u_2) [inst : Field k] [inst_1 : Field K] [ins
t_2 : Algebra k K]   (L : FiniteGaloisIntermediateField k K), Finite…
· 使用定理 `FiniteGaloisIntermediateField.instIsGaloisSubtypeMemIntermediateField`：∀
 (k : Type u_1) (K : Type u_2) [inst : Field k] [inst_1 : Field K] [inst_2 : Alg
ebra k K]   (L : FiniteGaloisIntermediateField k K), IsGalo…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IntermediateField.mem_fixedField_iff`：∀ {F : Type u_1} [inst : Field F] 
{E : Type u_2} [inst_1 : Field E] [inst_2 : Algebra F E] (H : Subgroup Gal(E/F))
   (x : E), x ∈ Intermedia…
· 使用定理 `IsGalois.to_normal`：∀ {F : Type u_1} {inst : Field F} {E : Type u_2} {in
st_1 : Field E} {inst_2 : Algebra F E} [self : IsGalois F E],   Normal F E
· 使用定理 `AlgEquiv.restrictNormalHom_surjective`：AlgEquiv.restrictNormalHom_surjec
tive [Normal F K₁] [Normal F E] : Function.Surjective (AlgEquiv.restrictNormalHo
m K₁ : Gal(E/F) -> K₁ ≃ₐ[F]…
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用引理 `AlgEquiv.restrictNormalHom_apply`：AlgEquiv.restrictNormalHom_apply (L : 
IntermediateField F K₁) [Normal F L] (σ : Gal(K₁/F)) (x : L) : restrictNormalHom
 L σ x = σ x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `true_implies`：∀ (p : Prop), (True → p) = p
· 使用定理 `IntermediateField.mem_bot`：mem_bot {x : E} : x in (⊥ : IntermediateField
 F E) ↔ x in Set.range (algebraMap F E)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IntermediateField.le_iff_le`：le_iff_le : K <= fixedField H ↔ H <= fixing
Subgroup K
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
lemma fixedField_fixingSubgroup (L : IntermediateField k K) [IsGalois k K] :
    IntermediateField.fixedField L.fixingSubgroup = L := by
  apply le_antisymm
  · intro x hx
    rw [IntermediateField.mem_fixedField_iff] at hx
    have mem : x ∈ (adjoin L {x}).1 := subset_adjoin _ _ rfl
    have : IntermediateField.fixedField (⊤ : Subgroup ((adjoin L {x}) ≃ₐ[L] (adjoin L {x}))) = ⊥ :=
      (IsGalois.tfae.out 0 1).mp (by infer_instance)
    have : ⟨x, mem⟩ ∈ (⊥ : IntermediateField L (adjoin L {x})) := by
      rw [← this, IntermediateField.mem_fixedField_iff]
      intro f _
      rcases restrictNormalHom_surjective K f with ⟨σ, hσ⟩
      apply Subtype.val_injective
      rw [← hσ, restrictNormalHom_apply (adjoin L {x}).1 σ ⟨x, mem⟩]
      have := hx ((IntermediateField.fixingSubgroupEquiv L).symm σ)
      simpa only [SetLike.coe_mem, true_implies]
    rcases IntermediateField.mem_bot.mp this with ⟨y, hy⟩
    obtain ⟨rfl⟩ : y = x := congrArg Subtype.val hy
    exact y.2
  · exact (IntermediateField.le_iff_le L.fixingSubgroup L).mpr le_rfl
/-
**InfiniteGalois.fixedField_bot** 是 Mathlib 中的一个引理，位于命名空间 `InfiniteGalois`。
形式化陈述：fixedField_bot [IsGalois k K] : IntermediateField.fixedField (⊤ : Subgroup
 Gal(K/k)) = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IntermediateField.fixingSubgroup_bot`：∀ {F : Type u_1} [inst : Field F] 
{E : Type u_2} [inst_1 : Field E] [inst_2 : Algebra F E], ⊥.fixingSubgroup = ⊤
· 使用引理 `InfiniteGalois.fixedField_fixingSubgroup`：fixedField_fixingSubgroup (L :
 IntermediateField k K) [IsGalois k K] : IntermediateField.fixedField L.fixingSu
bgroup = L
-/
lemma fixedField_bot [IsGalois k K] :
    IntermediateField.fixedField (⊤ : Subgroup Gal(K/k)) = ⊥ := by
  rw [← IntermediateField.fixingSubgroup_bot, fixedField_fixingSubgroup]
/-
**InfiniteGalois.mem_bot_iff_fixed** 是 Mathlib 中的一个定理，位于命名空间 `InfiniteGalois`。
形式化陈述：mem_bot_iff_fixed [IsGalois k K] (x : K) : x in (⊥ : IntermediateField k K
) ↔ forall (f : Gal(K/k)), f x = x
参数：x : K。
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
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_bot_iff_fixed [IsGalois k K] (x : K) :
    x ∈ (⊥ : IntermediateField k K) ↔ ∀ (f : Gal(K/k)), f x = x := by
  simp [← fixedField_bot, IntermediateField.mem_fixedField_iff]
/-
**InfiniteGalois.mem_range_algebraMap_iff_fixed** 是 Mathlib 中的一个定理，位于命名空间 `Infin
iteGalois`。
形式化陈述：mem_range_algebraMap_iff_fixed [IsGalois k K] (x : K) : x in Set.range (al
gebraMap k K) ↔ forall f : Gal(K/k), f x = x
参数：x : K。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `InfiniteGalois.mem_bot_iff_fixed`：mem_bot_iff_fixed [IsGalois k K] (x : 
K) : x in (⊥ : IntermediateField k K) ↔ forall (f : Gal(K/k)), f x = x
-/
theorem mem_range_algebraMap_iff_fixed [IsGalois k K] (x : K) :
    x ∈ Set.range (algebraMap k K) ↔ ∀ f : Gal(K/k), f x = x :=
  mem_bot_iff_fixed x

open IntermediateField in
/-- For a subgroup `H` of `Gal(K/k)`, the fixed field of the image of `H` under the restriction to
a normal intermediate field `E` is equal to the fixed field of `H` in `K` intersecting with `E`. -/
/-
**InfiniteGalois.restrict_fixedField** 是 Mathlib 中的一个引理，位于命名空间 `InfiniteGalois`。
形式化陈述：restrict_fixedField (H : Subgroup Gal(K/k)) (L : IntermediateField k K) [N
ormal k L] : fixedField H ⊓ L = lift (fixedField (Subgroup.map (restrictNormalHo
m L) H))
参数：H : Subgroup Gal(K/k)；L : IntermediateField k K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext'`：ext' (h : (p : Set B) = q) : p = q
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Membership.mem.out`：∀ {α : Type u} {a : α} {p : α → Prop}, a ∈ {x | p x}
 → p a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IntermediateField.mem_lift`：mem_lift {F : IntermediateField K L} {E : In
termediateField K F} (x : F) : x.1 in lift E ↔ x in E
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `AlgEquiv.restrictNormal_commutes`：AlgEquiv.restrictNormal_commutes [Norm
al F E] (x : E) : algebraMap E K₂ (χ.restrictNormal E x) = χ (algebraMap E K₁ x)
· 使用定理 `IntermediateField.lift_le`：lift_le {F : IntermediateField K L} (E : Inte
rmediateField K F) : lift E <= F
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b

--- 原说明 ---
For a subgroup `H` of `Gal(K/k)`, the fixed field of the image of `H` under the 
restriction to
a normal intermediate field `E` is equal to the fixed field of `H` in `K` inters
ecting with `E`.
-/
lemma restrict_fixedField (H : Subgroup Gal(K/k)) (L : IntermediateField k K) [Normal k L] :
    fixedField H ⊓ L = lift (fixedField (Subgroup.map (restrictNormalHom L) H)) := by
  apply SetLike.ext'
  ext x
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have xL := h.out.2
    apply (mem_lift (⟨x, xL⟩ : L)).mpr
    simp only [mem_fixedField_iff, Subgroup.mem_map, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂]
    intro σ hσ
    apply Subtype.val_injective
    dsimp only
    nth_rw 2 [← (h.out.1 ⟨σ, hσ⟩)]
    exact AlgEquiv.restrictNormal_commutes σ L ⟨x, xL⟩
  · have xL := lift_le _ h
    apply (mem_lift (⟨x, xL⟩ : L)).mp at h
    simp only [mem_fixedField_iff, Subgroup.mem_map, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂] at h
    simp only [coe_inf, Set.mem_inter_iff, SetLike.mem_coe, mem_fixedField_iff, xL, and_true]
    intro σ hσ
    have : ((restrictNormalHom L σ) ⟨x, xL⟩).1 = x := by rw [h σ hσ]
    nth_rw 2 [← this]
    exact (AlgEquiv.restrictNormal_commutes σ L ⟨x, xL⟩).symm

open IntermediateField in
/-
**InfiniteGalois.fixingSubgroup_fixedField** 是 Mathlib 中的一个引理，位于命名空间 `InfiniteGa
lois`。
形式化陈述：fixingSubgroup_fixedField (H : ClosedSubgroup Gal(K/k)) [IsGalois k K] : (
IntermediateField.fixedField H).fixingSubgroup = H.1
参数：H : ClosedSubgroup Gal(K/k)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `IsClosed.isOpen_compl`：∀ {X : Type u} {inst : TopologicalSpace X} {s : S
et X} [self : IsClosed s], IsOpen sᶜ
· 使用定理 `ClosedSubgroup.isClosed'`：∀ {G : Type u} [inst : Group G] [inst_1 : Topo
logicalSpace G] (self : ClosedSubgroup G), IsClosed (↑self).carrier
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `GroupFilterBasis.nhds_eq`：nhds_eq (B : GroupFilterBasis G) {x₀ : G} : @n
hds G B.topology x₀ = B.N x₀
· 使用定理 `Membership.mem.out`：∀ {α : Type u} {a : α} {p : α → Prop}, a ∈ {x | p x}
 → p a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Set.smul_set_subset_iff`：smul_set_subset_iff : a • s subseteq t ↔ forall
 ⦃b⦄, b in s -> a • b in t
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.smul_mem_smul_set`：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β]
 {s : Set β} {a : α} {b : β}, b ∈ s → a • b ∈ a • s
· 使用定理 `IntermediateField.fixingSubgroup_le`：fixingSubgroup_le {K1 K2 : Intermed
iateField F E} (h12 : K1 <= K2) : K2.fixingSubgroup <= K1.fixingSubgroup
· 使用引理 `IntermediateField.le_normalClosure`：le_normalClosure : K <= normalClosur
e F K L
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_fixingSubgroup_iff`：mem_fixingSubgroup_iff {s : Set α} {m : M} : m i
n fixingSubgroup M s ↔ forall y in s, m • y = y
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `IsGalois.to_normal`：∀ {F : Type u_1} {inst : Field F} {E : Type u_2} {in
st_1 : Field E} {inst_2 : Algebra F E} [self : IsGalois F E],   Normal F E
· 使用定理 `IntermediateField.fixingSubgroup_fixedField`：fixingSubgroup_fixedField [
FiniteDimensional F E] : fixingSubgroup (fixedField H) = H
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `AlgEquiv.restrictNormalHom_apply`：AlgEquiv.restrictNormalHom_apply (L : 
IntermediateField F K₁) [Normal F L] (σ : Gal(K₁/F)) (x : L) : restrictNormalHom
 L σ x = σ x
· 使用引理 `InfiniteGalois.restrict_fixedField`：restrict_fixedField (H : Subgroup Ga
l(K/k)) (L : IntermediateField k K) [Normal k L] : fixedField H ⊓ L = lift (fixe
dField (Subgroup.map (re…
· 使用定理 `IntermediateField.mem_lift`：mem_lift {F : IntermediateField K L} {E : In
termediateField K F} (x : F) : x.1 in lift E ↔ x in E
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `mul_inv_cancel_left`：mul_inv_cancel_left (a b : G) : a * (a⁻¹ * b) = b
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
（共 37 条，此处仅展示前 30 条）
-/
lemma fixingSubgroup_fixedField (H : ClosedSubgroup Gal(K/k)) [IsGalois k K] :
    (IntermediateField.fixedField H).fixingSubgroup = H.1 := by
  apply le_antisymm _ ((IntermediateField.le_iff_le H.toSubgroup
    (IntermediateField.fixedField H.toSubgroup)).mp le_rfl)
  intro σ hσ
  by_contra h
  have nhds : H.carrierᶜ ∈ nhds σ := H.isClosed'.isOpen_compl.mem_nhds h
  rw [GroupFilterBasis.nhds_eq (x₀ := σ) (galGroupBasis k K)] at nhds
  rcases nhds with ⟨b, ⟨gp, ⟨L, hL, eq'⟩, eq⟩, sub⟩
  rw [← eq'] at eq
  have := hL.out
  let L' : FiniteGaloisIntermediateField k K := {
    normalClosure k L K with
    finiteDimensional := normalClosure.is_finiteDimensional k L K
    isGalois := IsGalois.normalClosure k L K }
  have compl : σ • L'.1.fixingSubgroup.carrier ⊆ H.carrierᶜ := by
    rintro φ ⟨τ, hτ, muleq⟩
    have sub' : σ • b ⊆ H.carrierᶜ := Set.smul_set_subset_iff.mpr sub
    apply sub'
    simp only [← muleq, ← eq]
    apply Set.smul_mem_smul_set
    exact (L.fixingSubgroup_le (IntermediateField.le_normalClosure L) hτ)
  have fix : ∀ x ∈ IntermediateField.fixedField H.toSubgroup ⊓ ↑L', σ x = x :=
    fun x hx ↦ ((mem_fixingSubgroup_iff Gal(K/k)).mp hσ) x hx.1
  rw [restrict_fixedField H.1 L'.1] at fix
  have : (restrictNormalHom L') σ ∈ (Subgroup.map (restrictNormalHom L') H.1) := by
    rw [← IntermediateField.fixingSubgroup_fixedField (Subgroup.map (restrictNormalHom L') H.1)]
    apply (mem_fixingSubgroup_iff (L' ≃ₐ[k] L')).mpr
    intro y hy
    apply Subtype.val_injective
    simp only [AlgEquiv.smul_def, restrictNormalHom_apply L'.1 σ y,
      fix y.1 ((IntermediateField.mem_lift y).mpr hy)]
  rcases this with ⟨h, mem, eq⟩
  have : h ∈ σ • L'.1.fixingSubgroup.carrier := by
    use σ⁻¹ * h
    simp only [Subsemigroup.mem_carrier, Submonoid.mem_toSubsemigroup, Subgroup.mem_toSubmonoid,
      smul_eq_mul, mul_inv_cancel_left, and_true]
    apply (mem_fixingSubgroup_iff Gal(K/k)).mpr
    intro y hy
    simp only [AlgEquiv.smul_def, AlgEquiv.mul_apply]
    have : ((restrictNormalHom L') h ⟨y,hy⟩).1 = ((restrictNormalHom L') σ ⟨y,hy⟩).1 := by rw [eq]
    rw [restrictNormalHom_apply L'.1 h ⟨y, hy⟩, restrictNormalHom_apply L'.1 σ ⟨y, hy⟩] at this
    simp only [this, ← AlgEquiv.mul_apply, inv_mul_cancel, one_apply]
  absurd compl
  apply Set.not_subset.mpr
  use h
  simpa only [this, Set.mem_compl_iff, Subsemigroup.mem_carrier, Submonoid.mem_toSubsemigroup,
    Subgroup.mem_toSubmonoid, not_not, true_and] using! mem

/-- The Galois correspondence from intermediate fields to closed subgroups. -/
/-
**InfiniteGalois.IntermediateFieldEquivClosedSubgroup** 是 Mathlib 中的一个定义，位于命名空间 
`InfiniteGalois`。
形式化陈述：IntermediateFieldEquivClosedSubgroup [IsGalois k K] : IntermediateField k 
K ≃o (ClosedSubgroup Gal(K/k))ᵒᵈ where toFun L
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `InfiniteGalois.fixingSubgroup_isClosed`：fixingSubgroup_isClosed (L : Int
ermediateField k K) [IsGalois k K] : IsClosed (L.fixingSubgroup : Set Gal(K/k)) 
where isOpen_compl
· 使用引理 `InfiniteGalois.fixedField_fixingSubgroup`：fixedField_fixingSubgroup (L :
 IntermediateField k K) [IsGalois k K] : IntermediateField.fixedField L.fixingSu
bgroup = L

--- 原说明 ---
The Galois correspondence from intermediate fields to closed subgroups.
-/
def IntermediateFieldEquivClosedSubgroup [IsGalois k K] :
    IntermediateField k K ≃o (ClosedSubgroup Gal(K/k))ᵒᵈ where
  toFun L := ⟨L.fixingSubgroup, fixingSubgroup_isClosed L⟩
  invFun H := IntermediateField.fixedField H.1
  left_inv L := fixedField_fixingSubgroup L
  right_inv H := by
    simp_rw [fixingSubgroup_fixedField H]
    rfl
  map_rel_iff' {K L} := by
    rw [← fixedField_fixingSubgroup L, IntermediateField.le_iff_le, fixedField_fixingSubgroup L]
    rfl

/-- The Galois correspondence as a `GaloisInsertion` -/
/-
**InfiniteGalois.GaloisInsertionIntermediateFieldClosedSubgroup** 是 Mathlib 中的一个
定义，位于命名空间 `InfiniteGalois`。
形式化陈述：GaloisInsertionIntermediateFieldClosedSubgroup [IsGalois k K] : GaloisInse
rtion (OrderDual.toDual ∘ fun (E : IntermediateField k K) => (⟨E.fixingSubgroup,
 fixingSubgroup_isClosed E⟩ : ClosedSubgroup Gal(K/k))) ((fun (H : ClosedSubgrou
p Gal(K/k)) => IntermediateField.fixedField H) ∘ OrderDual.toDual)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Galois correspondence as a `GaloisInsertion`
-/
def GaloisInsertionIntermediateFieldClosedSubgroup [IsGalois k K] :
    GaloisInsertion (OrderDual.toDual ∘ fun (E : IntermediateField k K) ↦
      (⟨E.fixingSubgroup, fixingSubgroup_isClosed E⟩ : ClosedSubgroup Gal(K/k)))
      ((fun (H : ClosedSubgroup Gal(K/k)) ↦ IntermediateField.fixedField H) ∘
        OrderDual.toDual) :=
  OrderIso.toGaloisInsertion IntermediateFieldEquivClosedSubgroup

/-- The Galois correspondence as a `GaloisCoinsertion` -/
/-
**InfiniteGalois.GaloisCoinsertionIntermediateFieldSubgroup** 是 Mathlib 中的一个定义，位
于命名空间 `InfiniteGalois`。
形式化陈述：GaloisCoinsertionIntermediateFieldSubgroup [IsGalois k K] : GaloisCoinsert
ion (OrderDual.toDual ∘ fun (E : IntermediateField k K) => E.fixingSubgroup) ((f
un (H : Subgroup Gal(K/k)) => IntermediateField.fixedField H) ∘ OrderDual.toDual
) where choice H _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Galois correspondence as a `GaloisCoinsertion`
-/
def GaloisCoinsertionIntermediateFieldSubgroup [IsGalois k K] :
    GaloisCoinsertion (OrderDual.toDual ∘ fun (E : IntermediateField k K) ↦ E.fixingSubgroup)
      ((fun (H : Subgroup Gal(K/k)) ↦ IntermediateField.fixedField H) ∘ OrderDual.toDual) where
  choice H _ := IntermediateField.fixedField H
  gc E H := (IntermediateField.le_iff_le H E).symm
  u_l_le K := le_of_eq (fixedField_fixingSubgroup K)
  choice_eq _ _ := rfl

open IntermediateField in
/-- If `H` is a closed normal subgroup of `Gal(K / k)`,
then `Gal(fixedField H / k)` is isomorphic to `Gal(K / k) ⧸ H`. -/
/-
**InfiniteGalois.normalAutEquivQuotient** 是 Mathlib 中的一个定义，位于命名空间 `InfiniteGaloi
s`。
形式化陈述：normalAutEquivQuotient [IsGalois k K] (H : ClosedSubgroup Gal(K/k)) [H.Nor
mal] : Gal(K/k) ⧸ H.1 ≃* Gal(fixedField H.1/k)
参数：H : ClosedSubgroup Gal(K/k)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `H` is a closed normal subgroup of `Gal(K / k)`,
then `Gal(fixedField H / k)` is isomorphic to `Gal(K / k) ⧸ H`.
-/
noncomputable def normalAutEquivQuotient [IsGalois k K]
    (H : ClosedSubgroup Gal(K/k)) [H.Normal] :
    Gal(K/k) ⧸ H.1 ≃* Gal(fixedField H.1/k) :=
  QuotientGroup.liftEquiv _ (restrictNormalHom_surjective K)
    ((fixingSubgroup_fixedField H).symm.trans (fixedField H.1).restrictNormalHom_ker.symm)

open IntermediateField in
/-
**InfiniteGalois.normalAutEquivQuotient_apply** 是 Mathlib 中的一个引理，位于命名空间 `Infinit
eGalois`。
形式化陈述：normalAutEquivQuotient_apply [IsGalois k K] (H : ClosedSubgroup Gal(K/k)) 
[H.Normal] (σ : Gal(K/k)) : normalAutEquivQuotient H σ = restrictNormalHom (fixe
dField H.1) σ
参数：H : ClosedSubgroup Gal(K/k)；σ : Gal(K/k)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma normalAutEquivQuotient_apply [IsGalois k K]
    (H : ClosedSubgroup Gal(K/k)) [H.Normal] (σ : Gal(K/k)) :
    normalAutEquivQuotient H σ = restrictNormalHom (fixedField H.1) σ := rfl

set_option backward.isDefEq.respectTransparency false in
open IntermediateField in
/-
**InfiniteGalois.isOpen_iff_finite** 是 Mathlib 中的一个定理，位于命名空间 `InfiniteGalois`。
形式化陈述：isOpen_iff_finite (L : IntermediateField k K) [IsGalois k K] : IsOpen L.fi
xingSubgroup.carrier ↔ FiniteDimensional k L
参数：L : IntermediateField k K。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `GroupFilterBasis.nhds_one_eq`：nhds_one_eq (B : GroupFilterBasis G) : @nh
ds G B.topology (1 : G) = B.toFilterBasis.filter
· 使用定理 `Membership.mem.out`：∀ {α : Type u} {a : α} {p : α → Prop}, a ∈ {x | p x}
 → p a
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `InfiniteGalois.fixedField_fixingSubgroup`：fixedField_fixingSubgroup (L :
 IntermediateField k K) [IsGalois k K] : IntermediateField.fixedField L.fixingSu
bgroup = L
· 使用定理 `IntermediateField.le_iff_le`：le_iff_le : K <= fixedField H ↔ H <= fixing
Subgroup K
· 使用引理 `IntermediateField.le_normalClosure`：le_normalClosure : K <= normalClosur
e F K L
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `FiniteDimensional.left`：∀ (F : Type u) (K : Type v) (A : Type w) [inst :
 Ring F] [inst_1 : Ring K] [inst_2 : _root_.Module F K]   [inst_3 : AddCommGroup
 A] [inst_4 …
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `IsScalarTower.of_algHom`：∀ {R : Type u_1} {A : Type u_2} {B : Type u_3} 
[inst : CommSemiring R] [inst_1 : CommSemiring A]   [inst_2 : CommSemiring B] [i
nst_3 : Algeb…
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `IntermediateField.fixingSubgroup_isOpen`：IntermediateField.fixingSubgrou
p_isOpen {K L : Type*} [Field K] [Field L] [Algebra K L] (E : IntermediateField 
K L) [FiniteDimensional K E] …
-/
theorem isOpen_iff_finite (L : IntermediateField k K) [IsGalois k K] :
    IsOpen L.fixingSubgroup.carrier ↔ FiniteDimensional k L := by
  refine ⟨fun h ↦ ?_, fun h ↦ IntermediateField.fixingSubgroup_isOpen L⟩
  have : (IntermediateFieldEquivClosedSubgroup.toFun L).carrier ∈ nhds 1 :=
    IsOpen.mem_nhds h (congrFun rfl)
  rw [GroupFilterBasis.nhds_one_eq] at this
  rcases this with ⟨S, ⟨gp, ⟨M, hM, eq'⟩, eq⟩, sub⟩
  rw [← eq, ← eq'] at sub
  have := hM.out
  let L' : FiniteGaloisIntermediateField k K := {
    normalClosure k M K with
    finiteDimensional := normalClosure.is_finiteDimensional k M K
    isGalois := IsGalois.normalClosure k M K }
  have : L ≤ L'.1 := by
    apply le_trans _ (IntermediateField.le_normalClosure M)
    rw [← fixedField_fixingSubgroup M, IntermediateField.le_iff_le]
    exact sub
  let _ : Algebra L L'.1 := RingHom.toAlgebra (IntermediateField.inclusion this)
  exact FiniteDimensional.left k L L'.1
/-
**InfiniteGalois.normal_iff_isGalois** 是 Mathlib 中的一个定理，位于命名空间 `InfiniteGalois`。
形式化陈述：normal_iff_isGalois (L : IntermediateField k K) [IsGalois k K] : L.fixingS
ubgroup.Normal ↔ IsGalois k L
参数：L : IntermediateField k K。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `IsGalois.to_normal`：∀ {F : Type u_1} {inst : Field F} {E : Type u_2} {in
st_1 : Field E} {inst_2 : Algebra F E} [self : IsGalois F E],   Normal F E
· 使用定理 `FiniteGaloisIntermediateField.instIsGaloisSubtypeMemIntermediateField`：∀
 (k : Type u_1) (K : Type u_2) [inst : Field k] [inst_1 : Field K] [inst_2 : Alg
ebra k K]   (L : FiniteGaloisIntermediateField k K), IsGalo…
· 使用定理 `Subgroup.Normal.map`：∀ {G : Type u_1} [inst : Group G] {N : Type u_5} [i
nst_1 : Group N] {H : Subgroup G},   H.Normal → ∀ (f : G →* N), Function.Surject
ive ⇑f → …
· 使用定理 `AlgEquiv.restrictNormalHom_surjective`：AlgEquiv.restrictNormalHom_surjec
tive [Normal F K₁] [Normal F E] : Function.Surjective (AlgEquiv.restrictNormalHo
m K₁ : Gal(E/F) -> K₁ ≃ₐ[F]…
· 使用定理 `Normal.of_algEquiv`：Normal.of_algEquiv [h : Normal F E] (f : E ≃ₐ[F] E')
 : Normal F E'
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `InfiniteGalois.restrict_fixedField`：restrict_fixedField (H : Subgroup Ga
l(K/k)) (L : IntermediateField k K) [Normal k L] : fixedField H ⊓ L = lift (fixe
dField (Subgroup.map (re…
· 使用引理 `InfiniteGalois.fixedField_fixingSubgroup`：fixedField_fixingSubgroup (L :
 IntermediateField k K) [IsGalois k K] : IntermediateField.fixedField L.fixingSu
bgroup = L
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `FiniteGaloisIntermediateField.adjoin_simple_le_iff`：adjoin_simple_le_iff
 [IsGalois k K] {x : K} {L : FiniteGaloisIntermediateField k K} : adjoin k {x} <
= L ↔ x in L.toIntermediateField
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `IsGalois.to_isSeparable`：∀ {F : Type u_1} {inst : Field F} {E : Type u_2
} {inst_1 : Field E} {inst_2 : Algebra F E} [self : IsGalois F E],   Algebra.IsS
eparable F E
· 使用引理 `IntermediateField.restrictNormalHom_ker`：IntermediateField.restrictNorma
lHom_ker (E : IntermediateField K L) [Normal K E] : (restrictNormalHom E).ker = 
E.fixingSubgroup
· 使用定理 `MonoidHom.normal_ker`：∀ {G : Type u_1} [inst : Group G] {M : Type u_7} [
inst_1 : MulOneClass M] (f : G →* M), f.ker.Normal
-/
theorem normal_iff_isGalois (L : IntermediateField k K) [IsGalois k K] :
    L.fixingSubgroup.Normal ↔ IsGalois k L := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · let g (x : K) := L.fixingSubgroup.map (restrictNormalHom (adjoin k {x}))
    let f (x : L) : IntermediateField k K := IntermediateField.lift <|
      IntermediateField.fixedField <| g x.1
    have (x : K) : (g x).Normal :=
      Subgroup.Normal.map h (restrictNormalHom (adjoin k {x})) (restrictNormalHom_surjective K)
    have (l : L) : Normal k (f l) :=
      Normal.of_algEquiv <| IntermediateField.liftAlgEquiv <| IntermediateField.fixedField (g l.1)
    have n : Normal k ↥(⨆ l : L, f l) := IntermediateField.normal_iSup k K f
    have : (⨆ l : L, f l) = L := by
      apply le_antisymm
      · apply iSup_le
        intro l
        simpa only [f, g, ← restrict_fixedField L.fixingSubgroup (adjoin k {l.1}),
          fixedField_fixingSubgroup L] using inf_le_left
      · intro l hl
        apply le_iSup f ⟨l, hl⟩
        simpa only [f, g, ← restrict_fixedField L.fixingSubgroup (adjoin k {l}),
          fixedField_fixingSubgroup L, IntermediateField.mem_inf, hl, true_and]
          using adjoin_simple_le_iff.mp le_rfl
    rw [this] at n
    constructor
  · simpa only [IntermediateFieldEquivClosedSubgroup, RelIso.coe_fn_mk, Equiv.coe_fn_mk,
      ← L.restrictNormalHom_ker] using MonoidHom.normal_ker (restrictNormalHom L)
/-
**InfiniteGalois.isOpen_and_normal_iff_finite_and_isGalois** 是 Mathlib 中的一个定理，位于
命名空间 `InfiniteGalois`。
形式化陈述：isOpen_and_normal_iff_finite_and_isGalois (L : IntermediateField k K) [IsG
alois k K] : IsOpen L.fixingSubgroup.carrier ∧ L.fixingSubgroup.Normal ↔ FiniteD
imensional k L ∧ IsGalois k L
参数：L : IntermediateField k K。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `InfiniteGalois.isOpen_iff_finite`：isOpen_iff_finite (L : IntermediateFie
ld k K) [IsGalois k K] : IsOpen L.fixingSubgroup.carrier ↔ FiniteDimensional k L
· 使用定理 `InfiniteGalois.normal_iff_isGalois`：normal_iff_isGalois (L : Intermediat
eField k K) [IsGalois k K] : L.fixingSubgroup.Normal ↔ IsGalois k L
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isOpen_and_normal_iff_finite_and_isGalois (L : IntermediateField k K) [IsGalois k K] :
    IsOpen L.fixingSubgroup.carrier ∧ L.fixingSubgroup.Normal ↔
    FiniteDimensional k L ∧ IsGalois k L := by
  rw [isOpen_iff_finite, normal_iff_isGalois]

end InfiniteGalois

