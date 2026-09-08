/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl, Sander Dahmen, Kim Morrison, Chris Hughes, Anne Baanen
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.LinearAlgebra.Basis.Prod
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Rank of various constructions

## Main statements

- `rank_quotient_add_rank_le` : `rank M/N + rank N ≤ rank M`.
- `lift_rank_add_lift_rank_le_rank_prod`: `rank M × N ≤ rank M + rank N`.
- `rank_span_le_of_finite`: `rank (span s) ≤ #s` for finite `s`.

For free modules, we have

- `rank_prod` : `rank M × N = rank M + rank N`.
- `rank_finsupp` : `rank (ι →₀ M) = #ι * rank M`
- `rank_directSum`: `rank (⨁ Mᵢ) = ∑ rank Mᵢ`
- `rank_tensorProduct`: `rank (M ⊗ N) = rank M * rank N`.

Lemmas for ranks of submodules and subalgebras are also provided.
We have `finrank` variants for most lemmas as well.

-/

@[expose] public section


noncomputable section

universe u u' v v' u₁' w w'

variable {R : Type u} {S : Type u'} {M : Type v} {M' : Type v'} {M₁ : Type v}
variable {ι : Type w} {ι' : Type w'} {η : Type u₁'} {φ : η → Type*}

open Basis Cardinal DirectSum Function Module Set Submodule

section Quotient

variable [Ring R] [CommRing S] [AddCommGroup M] [AddCommGroup M'] [AddCommGroup M₁]
variable [Module R M]

set_option backward.isDefEq.respectTransparency false in
/-
**LinearIndependent.sumElim_of_quotient** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearIndependent.sumElim_of_quotient {M' : Submodule R M} {ι₁ ι₂} {f : ι₁
 -> M'} (hf : LinearIndependent R f) (g : ι₂ -> M) (hg : LinearIndependent R (Su
bmodule.Quotient.mk (p
参数：hf : LinearIndependent R f；g : ι₂ -> M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIndependent.sum_type`：LinearIndependent.sum_type {v' : ι' -> M} (h
v : LinearIndependent R v) (hv' : LinearIndependent R v') (h : Disjoint (Submodu
le.span R (range…
· 使用定理 `LinearIndependent.map'`：LinearIndependent.map' (hv : LinearIndependent R
 v) (f : M ->ₗ[R] M') (hf_inj : LinearMap.ker f = ⊥) : LinearIndependent R (f ∘ 
v)
· 使用定理 `Submodule.ker_subtype`：ker_subtype : ker p.subtype = ⊥
· 使用定理 `LinearIndependent.of_comp`：LinearIndependent.of_comp (f : M ->ₗ[R] M') (
hfv : LinearIndependent R (f ∘ v)) : LinearIndependent R v
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.disjoint_def`：disjoint_def {p p' : Submodule R M} : Disjoint p
 p' ↔ forall x in p, x in p' -> x = (0 : M)
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
· 使用定理 `Set.range_subset_iff`：range_subset_iff : range f subseteq s ↔ forall y, 
f y in s
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finsupp.mem_span_range_iff_exists_finsupp`：mem_span_range_iff_exists_fin
supp {v : α -> M} {x : M} : x in span R (range v) ↔ exists c : α ->₀ R, (c.sum f
un i a => a • v i) = x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `linearIndependent_iff`：linearIndependent_iff : LinearIndependent R v ↔ f
orall l, Finsupp.linearCombination R v l = 0 -> l = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `map_finsuppSum`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} {P : Typ
e u_11} [inst : Zero M] [inst_1 : AddCommMonoid N]   [inst_2 : AddCommMonoid P] 
{H :…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `Finsupp.sum_zero_index`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} 
[inst : Zero M] [inst_1 : AddCommMonoid N] {h : α → M → N},   Finsupp.sum 0 h = 
0
-/
theorem LinearIndependent.sumElim_of_quotient
    {M' : Submodule R M} {ι₁ ι₂} {f : ι₁ → M'} (hf : LinearIndependent R f) (g : ι₂ → M)
    (hg : LinearIndependent R (Submodule.Quotient.mk (p := M') ∘ g)) :
    LinearIndependent R (Sum.elim (f · : ι₁ → M) g) := by
  refine .sum_type (hf.map' M'.subtype M'.ker_subtype) (.of_comp M'.mkQ hg) ?_
  refine disjoint_def.mpr fun x h₁ h₂ ↦ ?_
  have : x ∈ M' := span_le.mpr (Set.range_subset_iff.mpr fun i ↦ (f i).prop) h₁
  obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp h₂
  simp_rw [← Quotient.mk_eq_zero, ← mkQ_apply, map_finsuppSum, map_smul, mkQ_apply] at this
  rw [linearIndependent_iff.mp hg _ this, Finsupp.sum_zero_index]
/-
**LinearIndepOn.union_of_quotient** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearIndepOn.union_of_quotient {s t : Set ι} {f : ι -> M} (hs : LinearInd
epOn R f s) (ht : LinearIndepOn R (mkQ (span R (f '' s)) ∘ f) t) : LinearIndepOn
 R f (s union t)
参数：hs : LinearIndepOn R f s；ht : LinearIndepOn R (mkQ (span R (f '' s)) ∘ f) t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIndepOn.union`：LinearIndepOn.union {t : Set ι} (hs : LinearIndepOn
 R v s) (ht : LinearIndepOn R v t) (hdj : Disjoint (span R (v '' s)) (span R (v 
'' t))) :…
· 使用定理 `LinearIndepOn.of_comp`：LinearIndepOn.of_comp (f : M ->ₗ[R] M') (hfv : Li
nearIndepOn R (f ∘ v) s) : LinearIndepOn R v s
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.ker_mkQ`：ker_mkQ : ker p.mkQ = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Disjoint.symm`：Disjoint.symm (x y : Finmap β) (h : Disjoint x y) : Disjo
int y x
· 使用定理 `Submodule.range_ker_disjoint`：Submodule.range_ker_disjoint {f : M ->ₗ[R]
 M'} (hv : LinearIndependent R (f ∘ v)) : Disjoint (span R (range v)) (LinearMap
.ker f)
-/
theorem LinearIndepOn.union_of_quotient {s t : Set ι} {f : ι → M} (hs : LinearIndepOn R f s)
    (ht : LinearIndepOn R (mkQ (span R (f '' s)) ∘ f) t) : LinearIndepOn R f (s ∪ t) := by
  apply hs.union ht.of_comp
  convert! (Submodule.range_ker_disjoint ht).symm
  · simp
  aesop
/-
**LinearIndepOn.union_id_of_quotient** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearIndepOn.union_id_of_quotient {M' : Submodule R M} {s : Set M} (hs : 
s subseteq M') (hs' : LinearIndepOn R id s) {t : Set M} (ht : LinearIndepOn R (m
kQ M') t) : LinearIndepOn R id (s union t)
参数：hs : s subseteq M'；hs' : LinearIndepOn R id s；ht : LinearIndepOn R (mkQ M') t
。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIndepOn.union_of_quotient`：LinearIndepOn.union_of_quotient {s t : 
Set ι} {f : ι -> M} (hs : LinearIndepOn R f s) (ht : LinearIndepOn R (mkQ (span 
R (f '' s)) ∘ f) t) :…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_id`：image_id (s : Set α) : id '' s = s
· 使用定理 `LinearIndepOn.of_comp`：LinearIndepOn.of_comp (f : M ->ₗ[R] M') (hfv : Li
nearIndepOn R (f ∘ v) s) : LinearIndepOn R v s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
-/
theorem LinearIndepOn.union_id_of_quotient {M' : Submodule R M}
    {s : Set M} (hs : s ⊆ M') (hs' : LinearIndepOn R id s) {t : Set M}
    (ht : LinearIndepOn R (mkQ M') t) : LinearIndepOn R id (s ∪ t) :=
  hs'.union_of_quotient <| by
    rw [image_id]
    exact ht.of_comp ((span R s).mapQ M' (LinearMap.id) (span_le.2 hs))
/-
**linearIndepOn_union_iff_quotient** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：linearIndepOn_union_iff_quotient {s t : Set ι} {f : ι -> M} (hst : Disjoin
t s t) : LinearIndepOn R f (s union t) ↔ LinearIndepOn R f s ∧ LinearIndepOn R (
mkQ (span R (f '' s)) ∘ f) t
参数：hst : Disjoint s t。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LinearIndepOn.mono`：LinearIndepOn.mono {t s : Set ι} (hs : LinearIndepOn
 R v s) (h : t subseteq s) : LinearIndepOn R v t
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
· 使用定理 `LinearIndependent.map`：LinearIndependent.map (hv : LinearIndependent R v
) {f : M ->ₗ[R] M'} (hf_inj : Disjoint (span R (range v)) (LinearMap.ker f)) : L
inearIndepe…
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.ker_mkQ`：ker_mkQ : ker p.mkQ = p
· 使用定理 `Disjoint.symm`：Disjoint.symm (x y : Finmap β) (h : Disjoint x y) : Disjo
int y x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `linearIndepOn_union_iff`：linearIndepOn_union_iff {t : Set ι} (hdj : Disj
oint s t) : LinearIndepOn R v (s union t) ↔ LinearIndepOn R v s ∧ LinearIndepOn 
R v t ∧ Disjo…
· 使用定理 `LinearIndepOn.union_of_quotient`：LinearIndepOn.union_of_quotient {s t : 
Set ι} {f : ι -> M} (hs : LinearIndepOn R f s) (ht : LinearIndepOn R (mkQ (span 
R (f '' s)) ∘ f) t) :…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem linearIndepOn_union_iff_quotient {s t : Set ι} {f : ι → M} (hst : Disjoint s t) :
    LinearIndepOn R f (s ∪ t) ↔
    LinearIndepOn R f s ∧ LinearIndepOn R (mkQ (span R (f '' s)) ∘ f) t := by
  refine ⟨fun h ↦ ⟨?_, ?_⟩, fun h ↦ h.1.union_of_quotient h.2⟩
  · exact h.mono subset_union_left
  apply (h.mono subset_union_right).map
  simpa [← image_eq_range] using ((linearIndepOn_union_iff hst).1 h).2.2.symm
/-
**LinearIndepOn.quotient_iff_union** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearIndepOn.quotient_iff_union {s t : Set ι} {f : ι -> M} (hs : LinearIn
depOn R f s) (hst : Disjoint s t) : LinearIndepOn R (mkQ (span R (f '' s)) ∘ f) 
t ↔ LinearIndepOn R f (s union t)
参数：hs : LinearIndepOn R f s；hst : Disjoint s t。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `linearIndepOn_union_iff_quotient`：linearIndepOn_union_iff_quotient {s t 
: Set ι} {f : ι -> M} (hst : Disjoint s t) : LinearIndepOn R f (s union t) ↔ Lin
earIndepOn R f s ∧ Lin…
· 使用定理 `and_iff_right`：∀ {a b : Prop}, a → (a ∧ b ↔ b)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem LinearIndepOn.quotient_iff_union {s t : Set ι} {f : ι → M} (hs : LinearIndepOn R f s)
    (hst : Disjoint s t) :
    LinearIndepOn R (mkQ (span R (f '' s)) ∘ f) t ↔ LinearIndepOn R f (s ∪ t) := by
  rw [linearIndepOn_union_iff_quotient hst, and_iff_right hs]
/-
**rank_quotient_add_rank_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rank_quotient_add_rank_le [Nontrivial R] (M' : Submodule R M) : Module.ran
k R (M ⧸ M') + Module.rank R M' <= Module.rank R M
参数：M' : Submodule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.rank_def`：∀ (R : Type u_1) (M : Type u_2) [inst : Semiring R] [in
st_1 : AddCommMonoid M] [inst_2 : _root_.Module R M],   Module.rank R M = ⨆ ι, C
ardin…
· 使用定理 `Cardinal.ciSup_add_ciSup`：∀ {ι : Type u} {ι' : Type w} (f : ι → Cardinal
.{v}) [Nonempty ι] [Nonempty ι'],   BddAbove (Set.range f) →     ∀ (g : ι' → Car
dinal.{v}), Bd…
· 使用定理 `Cardinal.bddAbove_of_small`：bddAbove_of_small {s : Set Cardinal.{u}} [h 
: Small.{u} s] : BddAbove s
· 使用定理 `Submodule.Quotient.instSmallQuotient`：∀ {R : Type u_3} {M : Type u_4} [i
nst : Ring R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {N : Subm
odule R M} [Small.{u, u_4}…
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `ciSup_le`：ciSup_le [Nonempty ι] {f : ι -> α} {c : α} (H : forall x, f x 
<= c) : iSup f <= c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Cardinal.mk_sum`：mk_sum (α : Type u) (β : Type v) : #(α oplus β) = lift.
{v, u} #α + lift.{u, v} #β
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `LinearIndependent.cardinal_le_rank`：cardinal_le_rank {ι : Type v} {v : ι
 -> M} (hv : LinearIndependent R v) : #ι <= Module.rank R M
· 使用定理 `LinearIndependent.sumElim_of_quotient`：LinearIndependent.sumElim_of_quot
ient {M' : Submodule R M} {ι₁ ι₂} {f : ι₁ -> M'} (hf : LinearIndependent R f) (g
 : ι₂ -> M) (hg : LinearInd…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Submodule.Quotient.mk_surjective`：mk_surjective : Function.Surjective (@
mk _ _ _ _ _ p)
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem rank_quotient_add_rank_le [Nontrivial R] (M' : Submodule R M) :
    Module.rank R (M ⧸ M') + Module.rank R M' ≤ Module.rank R M := by
  conv_lhs => simp only [Module.rank_def]
  rw [Cardinal.ciSup_add_ciSup _ bddAbove_of_small _ bddAbove_of_small]
  refine ciSup_le fun ⟨s, hs⟩ ↦ ciSup_le fun ⟨t, ht⟩ ↦ ?_
  choose f hf using Submodule.Quotient.mk_surjective M'
  simpa [add_comm] using! (LinearIndependent.sumElim_of_quotient ht (fun (i : s) ↦ f i)
    (by simpa [Function.comp_def, hf] using! hs)).cardinal_le_rank
/-
**rank_quotient_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rank_quotient_le (p : Submodule R M) : Module.rank R (M ⧸ p) <= Module.ran
k R M
参数：p : Submodule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.rank_le_of_surjective`：LinearMap.rank_le_of_surjective (f : M 
->ₗ[R] M₁) (h : Surjective f) : Module.rank R M₁ <= Module.rank R M
· 使用定理 `Quot.mk_surjective`：Quot.mk_surjective {r : α -> α -> Prop} : Function.S
urjective (Quot.mk r)
-/
theorem rank_quotient_le (p : Submodule R M) : Module.rank R (M ⧸ p) ≤ Module.rank R M :=
  (mkQ p).rank_le_of_surjective Quot.mk_surjective

/-- The dimension of a quotient is bounded by the dimension of the ambient space. -/
/-
**Submodule.finrank_quotient_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submodule.finrank_quotient_le [StrongRankCondition R] [Module.Finite R M] 
(s : Submodule R M) : finrank R (M ⧸ s) <= finrank R M
参数：s : Submodule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.toNat_le_toNat`：toNat_le_toNat (hcd : c <= d) (hd : d < ℵ₀) : t
oNat c <= toNat d
· 使用定理 `LinearMap.rank_le_of_surjective`：LinearMap.rank_le_of_surjective (f : M 
->ₗ[R] M₁) (h : Surjective f) : Module.rank R M₁ <= Module.rank R M
· 使用定理 `Quot.mk_surjective`：Quot.mk_surjective {r : α -> α -> Prop} : Function.S
urjective (Quot.mk r)
· 使用定理 `Module.rank_lt_aleph0`：rank_lt_aleph0 [Module.Finite R M] : Module.rank 
R M < ℵ₀

--- 原说明 ---
The dimension of a quotient is bounded by the dimension of the ambient space.
-/
theorem Submodule.finrank_quotient_le [StrongRankCondition R] [Module.Finite R M]
    (s : Submodule R M) : finrank R (M ⧸ s) ≤ finrank R M :=
  toNat_le_toNat ((Submodule.mkQ s).rank_le_of_surjective Quot.mk_surjective)
    (rank_lt_aleph0 _ _)

end Quotient

variable [Semiring R] [CommSemiring S] [AddCommMonoid M] [AddCommMonoid M'] [AddCommMonoid M₁]
variable [Module R M]

section ULift

@[simp]
/-
**rank_ulift** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rank_ulift : Module.rank R (ULift.{w} M) = Cardinal.lift.{w} (Module.rank 
R M)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.lift_injective`：lift_injective : Injective lift.{u, v}
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Cardinal.lift_lift`：lift_lift.{u_1} (a : Cardinal.{u_1}) : lift.{w} (lif
t.{v} a) = lift.{max v w} a
· 使用定理 `LinearEquiv.lift_rank_eq`：LinearEquiv.lift_rank_eq (f : M ≃ₗ[R] M') : Ca
rdinal.lift.{v'} (Module.rank R M) = Cardinal.lift.{v} (Module.rank R M')
-/
theorem rank_ulift : Module.rank R (ULift.{w} M) = Cardinal.lift.{w} (Module.rank R M) :=
  Cardinal.lift_injective.{v} <| Eq.symm <| (lift_lift _).trans ULift.moduleEquiv.symm.lift_rank_eq

@[simp]
/-
**finrank_ulift** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finrank_ulift : finrank R (ULift M) = finrank R M
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `rank_ulift`：rank_ulift : Module.rank R (ULift.{w} M) = Cardinal.lift.{w}
 (Module.rank R M)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Cardinal.toNat_lift`：toNat_lift (c : Cardinal.{v}) : toNat (lift.{u, v} 
c) = toNat c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem finrank_ulift : finrank R (ULift M) = finrank R M := by
  simp_rw [finrank, rank_ulift, toNat_lift]

end ULift

section Prod

variable (R M M')
variable [Module R M₁] [Module R M']

/-
**rank_add_rank_le_rank_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rank_add_rank_le_rank_prod [Nontrivial R] : Module.rank R M + Module.rank 
R M₁ <= Module.rank R (M × M₁)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.rank_def`：∀ (R : Type u_1) (M : Type u_2) [inst : Semiring R] [in
st_1 : AddCommMonoid M] [inst_2 : _root_.Module R M],   Module.rank R M = ⨆ ι, C
ardin…
· 使用定理 `Cardinal.ciSup_add_ciSup`：∀ {ι : Type u} {ι' : Type w} (f : ι → Cardinal
.{v}) [Nonempty ι] [Nonempty ι'],   BddAbove (Set.range f) →     ∀ (g : ι' → Car
dinal.{v}), Bd…
· 使用定理 `Cardinal.bddAbove_of_small`：bddAbove_of_small {s : Set Cardinal.{u}} [h 
: Small.{u} s] : BddAbove s
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `ciSup_le`：ciSup_le [Nonempty ι] {f : ι -> α} {c : α} (H : forall x, f x 
<= c) : iSup f <= c
· 使用定理 `LinearIndependent.cardinal_le_rank`：cardinal_le_rank {ι : Type v} {v : ι
 -> M} (hv : LinearIndependent R v) : #ι <= Module.rank R M
· 使用定理 `linearIndependent_inl_union_inr'`：linearIndependent_inl_union_inr' {v : 
ι -> M} {v' : ι' -> M'} (hv : LinearIndependent R v) (hv' : LinearIndependent R 
v') : LinearIndependen…
-/
theorem rank_add_rank_le_rank_prod [Nontrivial R] :
    Module.rank R M + Module.rank R M₁ ≤ Module.rank R (M × M₁) := by
  conv_lhs => simp only [Module.rank_def]
  rw [Cardinal.ciSup_add_ciSup _ bddAbove_of_small _ bddAbove_of_small]
  exact ciSup_le fun ⟨s, hs⟩ ↦ ciSup_le fun ⟨t, ht⟩ ↦
    (linearIndependent_inl_union_inr' hs ht).cardinal_le_rank
/-
**lift_rank_add_lift_rank_le_rank_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lift_rank_add_lift_rank_le_rank_prod [Nontrivial R] : lift.{v'} (Module.ra
nk R M) + lift.{v} (Module.rank R M') <= Module.rank R (M × M')
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `rank_ulift`：rank_ulift : Module.rank R (ULift.{w} M) = Cardinal.lift.{w}
 (Module.rank R M)
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `rank_add_rank_le_rank_prod`：rank_add_rank_le_rank_prod [Nontrivial R] : 
Module.rank R M + Module.rank R M₁ <= Module.rank R (M × M₁)
· 使用定理 `LinearEquiv.rank_eq`：LinearEquiv.rank_eq (f : M ≃ₗ[R] M₁) : Module.rank 
R M = Module.rank R M₁
-/
theorem lift_rank_add_lift_rank_le_rank_prod [Nontrivial R] :
    lift.{v'} (Module.rank R M) + lift.{v} (Module.rank R M') ≤ Module.rank R (M × M') := by
  rw [← rank_ulift, ← rank_ulift]
  exact (rank_add_rank_le_rank_prod R _).trans_eq
    (ULift.moduleEquiv.prodCongr ULift.moduleEquiv).rank_eq

variable {R M M'}
variable [StrongRankCondition R] [Module.Free R M] [Module.Free R M'] [Module.Free R M₁]

open Module.Free

/-- If `M` and `M'` are free, then the rank of `M × M'` is
`(Module.rank R M).lift + (Module.rank R M').lift`. -/
@[simp]
/-
**rank_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rank_prod : Module.rank R (M × M') = Cardinal.lift.{v'} (Module.rank R M) 
+ Cardinal.lift.{v, v'} (Module.rank R M')
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Module.Free.rank_eq_card_chooseBasisIndex`：rank_eq_card_chooseBasisIndex
 : Module.rank R M = #(ChooseBasisIndex R M)
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Cardinal.mk_sum`：mk_sum (α : Type u) (β : Type v) : #(α oplus β) = lift.
{v, u} #α + lift.{u, v} #β
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.Basis.mk_eq_rank`：mk_eq_rank (v : Basis ι R M) : Cardinal.lift.{v
} #ι = Cardinal.lift.{w} (Module.rank R M)

--- 原说明 ---
If `M` and `M'` are free, then the rank of `M × M'` is
`(Module.rank R M).lift + (Module.rank R M').lift`.
-/
theorem rank_prod : Module.rank R (M × M') =
    Cardinal.lift.{v'} (Module.rank R M) + Cardinal.lift.{v, v'} (Module.rank R M') := by
  simpa [rank_eq_card_chooseBasisIndex R M, rank_eq_card_chooseBasisIndex R M', lift_umax]
    using ((chooseBasis R M).prod (chooseBasis R M')).mk_eq_rank.symm

/-- If `M` and `M'` are free (and lie in the same universe), the rank of `M × M'` is
  `(Module.rank R M) + (Module.rank R M')`. -/
/-
**rank_prod'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rank_prod' : Module.rank R (M × M₁) = Module.rank R M + Module.rank R M₁
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `rank_prod`：rank_prod : Module.rank R (M × M') = Cardinal.lift.{v'} (Modu
le.rank R M) + Cardinal.lift.{v, v'} (Module.rank R M')
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `M` and `M'` are free (and lie in the same universe), the rank of `M × M'` is
  `(Module.rank R M) + (Module.rank R M')`.
-/
theorem rank_prod' : Module.rank R (M × M₁) = Module.rank R M + Module.rank R M₁ := by simp

/-- The `finrank` of `M × M'` is `(finrank R M) + (finrank R M')`. -/
@[simp]
/-
**Module.finrank_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.finrank_prod [Module.Finite R M] [Module.Finite R M'] : finrank R (
M × M') = finrank R M + finrank R M'
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `rank_prod`：rank_prod : Module.rank R (M × M') = Cardinal.lift.{v'} (Modu
le.rank R M) + Cardinal.lift.{v, v'} (Module.rank R M')
· 使用定理 `Cardinal.toNat_add`：toNat_add (hc : c < ℵ₀) (hd : d < ℵ₀) : toNat (c + d
) = toNat c + toNat d
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Module.rank_lt_aleph0`：rank_lt_aleph0 [Module.Finite R M] : Module.rank 
R M < ℵ₀
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Cardinal.toNat_lift`：toNat_lift (c : Cardinal.{v}) : toNat (lift.{u, v} 
c) = toNat c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The `finrank` of `M × M'` is `(finrank R M) + (finrank R M')`.
-/
theorem Module.finrank_prod [Module.Finite R M] [Module.Finite R M'] :
    finrank R (M × M') = finrank R M + finrank R M' := by
  simp [finrank, rank_lt_aleph0 R M, rank_lt_aleph0 R M']

end Prod

section Finsupp

variable (R M M')
variable [StrongRankCondition R] [Module.Free R M] [Module R M'] [Module.Free R M']

open Module.Free

@[simp]
/-
**rank_finsupp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rank_finsupp (ι : Type w) : Module.rank R (ι ->₀ M) = Cardinal.lift.{v} #ι
 * Cardinal.lift.{w} (Module.rank R M)
参数：ι : Type w。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Free.exists_basis`：∀ (R : Type u) (M : Type v) {inst : Semiring R
} {inst_1 : AddCommMonoid M} {inst_2 : _root_.Module R M}   [self : Module.Free 
R M], Nonempty…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.Basis.mk_eq_rank''`：Module.Basis.mk_eq_rank'' {ι : Type v} (v : B
asis ι R M) : #ι = Module.rank R M
· 使用定理 `Cardinal.mk_sigma`：mk_sigma {ι} (f : ι -> Type*) : #(Σ i, f i) = sum fun
 i => #(f i)
· 使用定理 `Cardinal.sum_const`：sum_const (ι : Type u) (a : Cardinal.{v}) : (sum fun
 _ : ι => a) = lift.{v} #ι * lift.{u} a
-/
theorem rank_finsupp (ι : Type w) :
    Module.rank R (ι →₀ M) = Cardinal.lift.{v} #ι * Cardinal.lift.{w} (Module.rank R M) := by
  obtain ⟨⟨_, bs⟩⟩ := Module.Free.exists_basis (R := R) (M := M)
  rw [← bs.mk_eq_rank'', ← (Finsupp.basis fun _ : ι => bs).mk_eq_rank'', Cardinal.mk_sigma,
    Cardinal.sum_const]
/-
**rank_finsupp'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rank_finsupp' (ι : Type v) : Module.rank R (ι ->₀ M) = #ι * Module.rank R 
M
参数：ι : Type v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `rank_finsupp`：rank_finsupp (ι : Type w) : Module.rank R (ι ->₀ M) = Card
inal.lift.{v} #ι * Cardinal.lift.{w} (Module.rank R M)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem rank_finsupp' (ι : Type v) : Module.rank R (ι →₀ M) = #ι * Module.rank R M := by
  simp [rank_finsupp]

/-- The rank of `(ι →₀ R)` is `(#ι).lift`. -/
/-
**rank_finsupp_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rank_finsupp_self (ι : Type w) : Module.rank R (ι ->₀ R) = Cardinal.lift.{
u} #ι
参数：ι : Type w。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `rank_finsupp`：rank_finsupp (ι : Type w) : Module.rank R (ι ->₀ M) = Card
inal.lift.{v} #ι * Cardinal.lift.{w} (Module.rank R M)
· 使用定理 `Module.rank_self`：rank_self : Module.rank R R = 1
· 使用定理 `Cardinal.lift_one`：lift_one : lift 1 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The rank of `(ι →₀ R)` is `(#ι).lift`.
-/
theorem rank_finsupp_self (ι : Type w) : Module.rank R (ι →₀ R) = Cardinal.lift.{u} #ι := by
  simp

/-- If `R` and `ι` lie in the same universe, the rank of `(ι →₀ R)` is `# ι`. -/
/-
**rank_finsupp_self'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rank_finsupp_self' {ι : Type u} : Module.rank R (ι ->₀ R) = #ι
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `rank_finsupp`：rank_finsupp (ι : Type w) : Module.rank R (ι ->₀ M) = Card
inal.lift.{v} #ι * Cardinal.lift.{w} (Module.rank R M)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `Module.rank_self`：rank_self : Module.rank R R = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `R` and `ι` lie in the same universe, the rank of `(ι →₀ R)` is `# ι`.
-/
theorem rank_finsupp_self' {ι : Type u} : Module.rank R (ι →₀ R) = #ι := by simp

/-- The rank of the direct sum is the sum of the ranks. -/
@[simp]
/-
**rank_directSum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rank_directSum {ι : Type v} (M : ι -> Type w) [forall i : ι, AddCommMonoid
 (M i)] [forall i : ι, Module R (M i)] [forall i : ι, Module.Free R (M i)] : Mod
ule.rank R (⨁ i, M i) = Cardinal.sum fun i => Module.rank R (M i)
参数：M : ι -> Type w；M i；M i；M i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.Basis.mk_eq_rank''`：Module.Basis.mk_eq_rank'' {ι : Type v} (v : B
asis ι R M) : #ι = Module.rank R M
· 使用定理 `Cardinal.mk_sigma`：mk_sigma {ι} (f : ι -> Type*) : #(Σ i, f i) = sum fun
 i => #(f i)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The rank of the direct sum is the sum of the ranks.
-/
theorem rank_directSum {ι : Type v} (M : ι → Type w) [∀ i : ι, AddCommMonoid (M i)]
    [∀ i : ι, Module R (M i)] [∀ i : ι, Module.Free R (M i)] :
    Module.rank R (⨁ i, M i) = Cardinal.sum fun i => Module.rank R (M i) := by
  let B i := chooseBasis R (M i)
  let b : Basis _ R (⨁ i, M i) := DFinsupp.basis fun i => B i
  simp [← b.mk_eq_rank'', fun i => (B i).mk_eq_rank'']

/-- If `m` and `n` are finite, the rank of `m × n` matrices over a module `M` is
`(#m).lift * (#n).lift * rank R M`. -/
@[simp]
/-
**rank_matrix_module** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rank_matrix_module (m : Type w) (n : Type w') [Finite m] [Finite n] : Modu
le.rank R (Matrix m n M) = lift.{max v w'} #m * lift.{max v w} #n * lift.{max w 
w'} (Module.rank R M)
参数：m : Type w；n : Type w'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `Module.Free.exists_basis`：∀ (R : Type u) (M : Type v) {inst : Semiring R
} {inst_1 : AddCommMonoid M} {inst_2 : _root_.Module R M}   [self : Module.Free 
R M], Nonempty…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.Basis.mk_eq_rank''`：Module.Basis.mk_eq_rank'' {ι : Type v} (v : B
asis ι R M) : #ι = Module.rank R M
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Cardinal.mk_prod`：mk_prod (α : Type u) (β : Type v) : #(α × β) = lift.{v
, u} #α * lift.{u, v} #β
· 使用定理 `Cardinal.lift_mul`：lift_mul (a b : Cardinal.{u}) : lift.{v} (a * b) = li
ft.{v} a * lift.{v} b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Cardinal.lift_lift`：lift_lift.{u_1} (a : Cardinal.{u_1}) : lift.{w} (lif
t.{v} a) = lift.{max v w} a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `m` and `n` are finite, the rank of `m × n` matrices over a module `M` is
`(#m).lift * (#n).lift * rank R M`.
-/
theorem rank_matrix_module (m : Type w) (n : Type w') [Finite m] [Finite n] :
    Module.rank R (Matrix m n M) =
      lift.{max v w'} #m * lift.{max v w} #n * lift.{max w w'} (Module.rank R M) := by
  cases nonempty_fintype m
  cases nonempty_fintype n
  obtain ⟨I, b⟩ := Module.Free.exists_basis (R := R) (M := M)
  rw [← (b.matrix m n).mk_eq_rank'']
  simp only [mk_prod, lift_mul, lift_lift, ← mul_assoc, b.mk_eq_rank'']


/-- If `m` and `n` are finite and lie in the same universe, the rank of `m × n` matrices over a
module `M` is `(#m * #n).lift * rank R M`. -/
@[simp high]
/-
**rank_matrix_module'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rank_matrix_module' (m n : Type w) [Finite m] [Finite n] : Module.rank R (
Matrix m n M) = lift.{max v} (#m * #n) * lift.{w} (Module.rank R M)
参数：m n : Type w。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `rank_matrix_module`：rank_matrix_module (m : Type w) (n : Type w') [Finit
e m] [Finite n] : Module.rank R (Matrix m n M) = lift.{max v w'} #m * lift.{max 
v w} #n …
· 使用定理 `Cardinal.lift_mul`：lift_mul (a b : Cardinal.{u}) : lift.{v} (a * b) = li
ft.{v} a * lift.{v} b
· 使用定理 `Cardinal.lift_umax`：lift_umax : lift.{max u v, u} = lift.{v, u}

--- 原说明 ---
If `m` and `n` are finite and lie in the same universe, the rank of `m × n` matr
ices over a
module `M` is `(#m * #n).lift * rank R M`.
-/
theorem rank_matrix_module' (m n : Type w) [Finite m] [Finite n] :
    Module.rank R (Matrix m n M) =
      lift.{max v} (#m * #n) * lift.{w} (Module.rank R M) := by
  rw [rank_matrix_module, lift_mul, lift_umax.{w, v}]

/-- If `m` and `n` are finite, the rank of `m × n` matrices is `(#m).lift * (#n).lift`. -/
/-
**rank_matrix** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rank_matrix (m : Type v) (n : Type w) [Finite m] [Finite n] : Module.rank 
R (Matrix m n R) = Cardinal.lift.{max v w u, v} #m * Cardinal.lift.{max v w u, w
} #n
参数：m : Type v；n : Type w。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `rank_matrix_module`：rank_matrix_module (m : Type w) (n : Type w') [Finit
e m] [Finite n] : Module.rank R (Matrix m n M) = lift.{max v w'} #m * lift.{max 
v w} #n …
· 使用定理 `Module.rank_self`：rank_self : Module.rank R R = 1
· 使用定理 `Cardinal.lift_one`：lift_one : lift 1 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lift_lift`：lift_lift.{u_1} (a : Cardinal.{u_1}) : lift.{w} (lif
t.{v} a) = lift.{max v w} a
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a

--- 原说明 ---
If `m` and `n` are finite, the rank of `m × n` matrices is `(#m).lift * (#n).lif
t`.
-/
theorem rank_matrix (m : Type v) (n : Type w) [Finite m] [Finite n] :
    Module.rank R (Matrix m n R) =
      Cardinal.lift.{max v w u, v} #m * Cardinal.lift.{max v w u, w} #n := by
  rw [rank_matrix_module, rank_self, lift_one, mul_one, ← lift_lift.{v, max u w}, lift_id,
    ← lift_lift.{w, max u v}, lift_id]

/-- If `m` and `n` are finite and lie in the same universe, the rank of `m × n` matrices is
  `(#n * #m).lift`. -/
/-
**rank_matrix'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rank_matrix' (m n : Type v) [Finite m] [Finite n] : Module.rank R (Matrix 
m n R) = Cardinal.lift.{u} (#m * #n)
参数：m n : Type v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `rank_matrix`：rank_matrix (m : Type v) (n : Type w) [Finite m] [Finite n]
 : Module.rank R (Matrix m n R) = Cardinal.lift.{max v w u, v} #m * Cardinal.lif
t…
· 使用定理 `Cardinal.lift_mul`：lift_mul (a b : Cardinal.{u}) : lift.{v} (a * b) = li
ft.{v} a * lift.{v} b
· 使用定理 `Cardinal.lift_umax`：lift_umax : lift.{max u v, u} = lift.{v, u}

--- 原说明 ---
If `m` and `n` are finite and lie in the same universe, the rank of `m × n` matr
ices is
  `(#n * #m).lift`.
-/
theorem rank_matrix' (m n : Type v) [Finite m] [Finite n] :
    Module.rank R (Matrix m n R) = Cardinal.lift.{u} (#m * #n) := by
  rw [rank_matrix, lift_mul, lift_umax.{v, u}]

/-- If `m` and `n` are finite and lie in the same universe as `R`, the rank of `m × n` matrices
  is `# m * # n`. -/
/-
**rank_matrix''** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rank_matrix'' (m n : Type u) [Finite m] [Finite n] : Module.rank R (Matrix
 m n R) = #m * #n
参数：m n : Type u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `rank_matrix_module'`：rank_matrix_module' (m n : Type w) [Finite m] [Fini
te n] : Module.rank R (Matrix m n M) = lift.{max v} (#m * #n) * lift.{w} (Module
.rank R M…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `Module.rank_self`：rank_self : Module.rank R R = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `m` and `n` are finite and lie in the same universe as `R`, the rank of `m × 
n` matrices
  is `# m * # n`.
-/
theorem rank_matrix'' (m n : Type u) [Finite m] [Finite n] :
    Module.rank R (Matrix m n R) = #m * #n := by simp

open Fintype

namespace Module

@[simp]
/-
**Module.finrank_finsupp** 是 Mathlib 中的一个定理，位于命名空间 `Module`。
形式化陈述：finrank_finsupp {ι : Type v} [Fintype ι] : finrank R (ι ->₀ M) = card ι * 
finrank R M
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.finrank.eq_1`：∀ (R : Type u_1) (M : Type u_2) [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M],   Module.finrank R M =
 Cardinal…
· 使用定理 `rank_finsupp`：rank_finsupp (ι : Type w) : Module.rank R (ι ->₀ M) = Card
inal.lift.{v} #ι * Cardinal.lift.{w} (Module.rank R M)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.mk_toNat_eq_card`：mk_toNat_eq_card [Fintype α] : toNat #α = Fin
type.card α
· 使用定理 `Cardinal.toNat_mul`：toNat_mul (x y : Cardinal) : toNat (x * y) = toNat x
 * toNat y
· 使用定理 `Cardinal.toNat_lift`：toNat_lift (c : Cardinal.{v}) : toNat (lift.{u, v} 
c) = toNat c
-/
theorem finrank_finsupp {ι : Type v} [Fintype ι] : finrank R (ι →₀ M) = card ι * finrank R M := by
  rw [finrank, finrank, rank_finsupp, ← mk_toNat_eq_card, toNat_mul, toNat_lift, toNat_lift]

/-- The `finrank` of `(ι →₀ R)` is `Fintype.card ι`. -/
@[simp]
/-
**Module.finrank_finsupp_self** 是 Mathlib 中的一个定理，位于命名空间 `Module`。
形式化陈述：finrank_finsupp_self {ι : Type v} [Fintype ι] : finrank R (ι ->₀ R) = card
 ι
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.finrank.eq_1`：∀ (R : Type u_1) (M : Type u_2) [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M],   Module.finrank R M =
 Cardinal…
· 使用定理 `rank_finsupp_self`：rank_finsupp_self (ι : Type w) : Module.rank R (ι ->₀
 R) = Cardinal.lift.{u} #ι
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.mk_toNat_eq_card`：mk_toNat_eq_card [Fintype α] : toNat #α = Fin
type.card α
· 使用定理 `Cardinal.toNat_lift`：toNat_lift (c : Cardinal.{v}) : toNat (lift.{u, v} 
c) = toNat c

--- 原说明 ---
The `finrank` of `(ι →₀ R)` is `Fintype.card ι`.
-/
theorem finrank_finsupp_self {ι : Type v} [Fintype ι] : finrank R (ι →₀ R) = card ι := by
  rw [finrank, rank_finsupp_self, ← mk_toNat_eq_card, toNat_lift]

/-- The `finrank` of the direct sum is the sum of the `finrank`s. -/
@[simp]
/-
**Module.finrank_directSum** 是 Mathlib 中的一个定理，位于命名空间 `Module`。
形式化陈述：finrank_directSum {ι : Type v} [Fintype ι] (M : ι -> Type w) [forall i : ι
, AddCommMonoid (M i)] [forall i : ι, Module R (M i)] [forall i : ι, Module.Free
 R (M i)] [forall i : ι, Module.Finite R (M i)] : finrank R (⨁ i, M i) = ∑ i, fi
nrank R (M i)
参数：M : ι -> Type w；M i；M i；M i；M i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `rank_directSum`：rank_directSum {ι : Type v} (M : ι -> Type w) [forall i 
: ι, AddCommMonoid (M i)] [forall i : ι, Module R (M i)] [forall i : ι, Module.F
ree …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Module.Free.rank_eq_card_chooseBasisIndex`：rank_eq_card_chooseBasisIndex
 : Module.rank R M = #(ChooseBasisIndex R M)
· 使用定理 `Cardinal.mk_toNat_eq_card`：mk_toNat_eq_card [Fintype α] : toNat #α = Fin
type.card α
· 使用定理 `Fintype.card_sigma`：∀ {ι : Type u_8} {α : ι → Type u_7} [inst : Fintype 
ι] [inst_1 : (i : ι) → Fintype (α i)],   Fintype.card (Sigma α) = ∑ i, Fintype.c
ard (α i…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The `finrank` of the direct sum is the sum of the `finrank`s.
-/
theorem finrank_directSum {ι : Type v} [Fintype ι] (M : ι → Type w) [∀ i : ι, AddCommMonoid (M i)]
    [∀ i : ι, Module R (M i)] [∀ i : ι, Module.Free R (M i)] [∀ i : ι, Module.Finite R (M i)] :
    finrank R (⨁ i, M i) = ∑ i, finrank R (M i) := by
  simp only [finrank, fun i => rank_eq_card_chooseBasisIndex R (M i), rank_directSum, ← mk_sigma,
    mk_toNat_eq_card, card_sigma]

/-- If `m` and `n` are `Fintype`, the `finrank` of `m × n` matrices over a module `M` is
  `(Fintype.card m) * (Fintype.card n) * finrank R M`. -/
/-
**Module.finrank_matrix** 是 Mathlib 中的一个定理，位于命名空间 `Module`。
形式化陈述：finrank_matrix (m n : Type*) [Fintype m] [Fintype n] : finrank R (Matrix m
 n M) = card m * card n * finrank R M
参数：m n : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `rank_matrix_module`：rank_matrix_module (m : Type w) (n : Type w') [Finit
e m] [Finite n] : Module.rank R (Matrix m n M) = lift.{max v w'} #m * lift.{max 
v w} #n …
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Cardinal.mk_fintype`：mk_fintype (α : Type u) [h : Fintype α] : #α = Fint
ype.card α
· 使用定理 `Cardinal.lift_natCast`：lift_natCast (n : Nat) : lift.{u} (n : Cardinal.{
v}) = n
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `Cardinal.toNat_natCast`：∀ (n : ℕ), Cardinal.toNat ↑n = n
· 使用定理 `Cardinal.toNat_lift`：toNat_lift (c : Cardinal.{v}) : toNat (lift.{u, v} 
c) = toNat c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `m` and `n` are `Fintype`, the `finrank` of `m × n` matrices over a module `M
` is
  `(Fintype.card m) * (Fintype.card n) * finrank R M`.
-/
theorem finrank_matrix (m n : Type*) [Fintype m] [Fintype n] :
    finrank R (Matrix m n M) = card m * card n * finrank R M := by simp [finrank]

end Module

end Finsupp

section Pi

variable [StrongRankCondition R] [Module.Free R M]
variable [∀ i, AddCommMonoid (φ i)] [∀ i, Module R (φ i)] [∀ i, Module.Free R (φ i)]

open Module.Free

open LinearMap

/-- The rank of a finite product of free modules is the sum of the ranks. -/
-- this result is not true without the freeness assumption
@[simp]
/-
**rank_pi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rank_pi [Finite η] : Module.rank R (forall i, φ i) = Cardinal.sum fun i =>
 Module.rank R (φ i)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.Basis.mk_eq_rank''`：Module.Basis.mk_eq_rank'' {ι : Type v} (v : B
asis ι R M) : #ι = Module.rank R M
· 使用定理 `Cardinal.mk_sigma`：mk_sigma {ι} (f : ι -> Type*) : #(Σ i, f i) = sum fun
 i => #(f i)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem rank_pi [Finite η] : Module.rank R (∀ i, φ i) =
    Cardinal.sum fun i => Module.rank R (φ i) := by
  cases nonempty_fintype η
  let B i := chooseBasis R (φ i)
  let b : Basis _ R (∀ i, φ i) := Pi.basis fun i => B i
  simp [← b.mk_eq_rank'', fun i => (B i).mk_eq_rank'']

variable (R)

/-- The `finrank` of `(ι → R)` is `Fintype.card ι`. -/
/-
**Module.finrank_pi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.finrank_pi {ι : Type v} [Fintype ι] : finrank R (ι -> R) = Fintype.
card ι
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `rank_pi`：rank_pi [Finite η] : Module.rank R (forall i, φ i) = Cardinal.s
um fun i => Module.rank R (φ i)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Module.rank_self`：rank_self : Module.rank R R = 1
· 使用定理 `Cardinal.sum_const`：sum_const (ι : Type u) (a : Cardinal.{v}) : (sum fun
 _ : ι => a) = lift.{v} #ι * lift.{u} a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Cardinal.mk_fintype`：mk_fintype (α : Type u) [h : Fintype α] : #α = Fint
ype.card α
· 使用定理 `Cardinal.lift_natCast`：lift_natCast (n : Nat) : lift.{u} (n : Cardinal.{
v}) = n
· 使用定理 `Cardinal.lift_one`：lift_one : lift 1 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Cardinal.toNat_natCast`：∀ (n : ℕ), Cardinal.toNat ↑n = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The `finrank` of `(ι → R)` is `Fintype.card ι`.
-/
theorem Module.finrank_pi {ι : Type v} [Fintype ι] :
    finrank R (ι → R) = Fintype.card ι := by
  simp [finrank]

--TODO: this should follow from `LinearEquiv.finrank_eq`, that is over a field.
/-- The `finrank` of a finite product is the sum of the `finrank`s. -/
/-
**Module.finrank_pi_fintype** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.finrank_pi_fintype {ι : Type v} [Fintype ι] {M : ι -> Type w} [fora
ll i : ι, AddCommMonoid (M i)] [forall i : ι, Module R (M i)] [forall i : ι, Mod
ule.Free R (M i)] [forall i : ι, Module.Finite R (M i)] : finrank R (forall i, M
 i) = ∑ i, finrank R (M i)
参数：M i；M i；M i；M i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `rank_pi`：rank_pi [Finite η] : Module.rank R (forall i, φ i) = Cardinal.s
um fun i => Module.rank R (φ i)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Module.Free.rank_eq_card_chooseBasisIndex`：rank_eq_card_chooseBasisIndex
 : Module.rank R M = #(ChooseBasisIndex R M)
· 使用定理 `Cardinal.mk_toNat_eq_card`：mk_toNat_eq_card [Fintype α] : toNat #α = Fin
type.card α
· 使用定理 `Fintype.card_sigma`：∀ {ι : Type u_8} {α : ι → Type u_7} [inst : Fintype 
ι] [inst_1 : (i : ι) → Fintype (α i)],   Fintype.card (Sigma α) = ∑ i, Fintype.c
ard (α i…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The `finrank` of a finite product is the sum of the `finrank`s.
-/
theorem Module.finrank_pi_fintype
    {ι : Type v} [Fintype ι] {M : ι → Type w} [∀ i : ι, AddCommMonoid (M i)]
    [∀ i : ι, Module R (M i)] [∀ i : ι, Module.Free R (M i)] [∀ i : ι, Module.Finite R (M i)] :
    finrank R (∀ i, M i) = ∑ i, finrank R (M i) := by
  simp only [finrank, fun i => rank_eq_card_chooseBasisIndex R (M i), rank_pi, ← mk_sigma,
    mk_toNat_eq_card, Fintype.card_sigma]

variable {R}
variable [Fintype η]
/-
**rank_fun** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rank_fun {M η : Type u} [Fintype η] [AddCommMonoid M] [Module R M] [Module
.Free R M] : Module.rank R (η -> M) = Fintype.card η * Module.rank R M
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `rank_pi`：rank_pi [Finite η] : Module.rank R (forall i, φ i) = Cardinal.s
um fun i => Module.rank R (φ i)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Cardinal.sum_const'`：sum_const' (ι : Type u) (a : Cardinal.{u}) : (sum f
un _ : ι => a) = #ι * a
· 使用定理 `Cardinal.mk_fintype`：mk_fintype (α : Type u) [h : Fintype α] : #α = Fint
ype.card α
-/
theorem rank_fun {M η : Type u} [Fintype η] [AddCommMonoid M] [Module R M] [Module.Free R M] :
    Module.rank R (η → M) = Fintype.card η * Module.rank R M := by
  rw [rank_pi, Cardinal.sum_const', Cardinal.mk_fintype]
/-
**rank_fun_eq_lift_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rank_fun_eq_lift_mul : Module.rank R (η -> M) = (Fintype.card η : Cardinal
.{max u₁' v}) * Cardinal.lift.{u₁'} (Module.rank R M)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `rank_pi`：rank_pi [Finite η] : Module.rank R (forall i, φ i) = Cardinal.s
um fun i => Module.rank R (φ i)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Cardinal.sum_const`：sum_const (ι : Type u) (a : Cardinal.{v}) : (sum fun
 _ : ι => a) = lift.{v} #ι * lift.{u} a
· 使用定理 `Cardinal.mk_fintype`：mk_fintype (α : Type u) [h : Fintype α] : #α = Fint
ype.card α
· 使用定理 `Cardinal.lift_natCast`：lift_natCast (n : Nat) : lift.{u} (n : Cardinal.{
v}) = n
-/
theorem rank_fun_eq_lift_mul : Module.rank R (η → M) =
    (Fintype.card η : Cardinal.{max u₁' v}) * Cardinal.lift.{u₁'} (Module.rank R M) := by
  rw [rank_pi, Cardinal.sum_const, Cardinal.mk_fintype, Cardinal.lift_natCast]
/-
**rank_fun'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rank_fun' : Module.rank R (η -> R) = Fintype.card η
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `rank_fun_eq_lift_mul`：rank_fun_eq_lift_mul : Module.rank R (η -> M) = (F
intype.card η : Cardinal.{max u₁' v}) * Cardinal.lift.{u₁'} (Module.rank R M)
· 使用定理 `Module.rank_self`：rank_self : Module.rank R R = 1
· 使用定理 `Cardinal.lift_one`：lift_one : lift 1 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem rank_fun' : Module.rank R (η → R) = Fintype.card η := by
  rw [rank_fun_eq_lift_mul, rank_self, Cardinal.lift_one, mul_one]
/-
**rank_fin_fun** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rank_fin_fun (n : Nat) : Module.rank R (Fin n -> R) = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `rank_pi`：rank_pi [Finite η] : Module.rank R (forall i, φ i) = Cardinal.s
um fun i => Module.rank R (φ i)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Module.rank_self`：rank_self : Module.rank R R = 1
· 使用定理 `Cardinal.sum_const`：sum_const (ι : Type u) (a : Cardinal.{v}) : (sum fun
 _ : ι => a) = lift.{v} #ι * lift.{u} a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Cardinal.mk_fintype`：mk_fintype (α : Type u) [h : Fintype α] : #α = Fint
ype.card α
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `Cardinal.lift_natCast`：lift_natCast (n : Nat) : lift.{u} (n : Cardinal.{
v}) = n
· 使用定理 `Cardinal.lift_uzero`：lift_uzero (a : Cardinal.{u}) : lift.{0} a = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem rank_fin_fun (n : ℕ) : Module.rank R (Fin n → R) = n := by simp

variable (R)

/-- The vector space of functions on a `Fintype ι` has `finrank` equal to the cardinality of `ι`. -/
@[simp]
/-
**Module.finrank_fintype_fun_eq_card** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.finrank_fintype_fun_eq_card : finrank R (η -> R) = Fintype.card η
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.finrank_eq_of_rank_eq`：finrank_eq_of_rank_eq {n : Nat} (h : Modul
e.rank R M = ↑n) : finrank R M = n
· 使用定理 `rank_fun'`：rank_fun' : Module.rank R (η -> R) = Fintype.card η

--- 原说明 ---
The vector space of functions on a `Fintype ι` has `finrank` equal to the cardin
ality of `ι`.
-/
theorem Module.finrank_fintype_fun_eq_card : finrank R (η → R) = Fintype.card η :=
  finrank_eq_of_rank_eq rank_fun'

/-- The vector space of functions on `Fin n` has `finrank` equal to `n`. -/
/-
**Module.finrank_fin_fun** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.finrank_fin_fun {n : Nat} : finrank R (Fin n -> R) = n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.finrank_fintype_fun_eq_card`：Module.finrank_fintype_fun_eq_card :
 finrank R (η -> R) = Fintype.card η
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The vector space of functions on `Fin n` has `finrank` equal to `n`.
-/
theorem Module.finrank_fin_fun {n : ℕ} : finrank R (Fin n → R) = n := by simp

variable {R}

-- TODO: merge with the `Finrank` content
/-- An `n`-dimensional `R`-vector space is equivalent to `Fin n → R`. -/
/-
**finDimVectorspaceEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：finDimVectorspaceEquiv (n : Nat) (hn : Module.rank R M = n) : M ≃ₗ[R] Fin 
n -> R
参数：n : Nat；hn : Module.rank R M = n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An `n`-dimensional `R`-vector space is equivalent to `Fin n → R`.
-/
def finDimVectorspaceEquiv (n : ℕ) (hn : Module.rank R M = n) : M ≃ₗ[R] Fin n → R := by
  haveI := nontrivial_of_invariantBasisNumber R
  have : Cardinal.lift.{u} (n : Cardinal.{v}) = Cardinal.lift.{v} (n : Cardinal.{u}) := by simp
  have hn := Cardinal.lift_inj.{v, u}.2 hn
  rw [this] at hn
  rw [← @rank_fin_fun R _ _ n] at hn
  haveI : Module.Free R (Fin n → R) := Module.Free.pi _ _
  exact Classical.choice (nonempty_linearEquiv_of_lift_rank_eq hn)

end Pi

section TensorProduct

open TensorProduct

variable [StrongRankCondition R] [StrongRankCondition S]
variable [Module S M] [Module S M'] [Module.Free S M']
variable [Module S M₁] [Module.Free S M₁]
variable [Algebra S R] [IsScalarTower S R M] [Module.Free R M]

open Module.Free

/-- The `S`-rank of `M ⊗[R] M'` is `(Module.rank S M).lift * (Module.rank R M').lift`. -/
@[simp]
/-
**rank_tensorProduct** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rank_tensorProduct : Module.rank R (M otimes[S] M') = Cardinal.lift.{v'} (
Module.rank R M) * Cardinal.lift.{v} (Module.rank S M')
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `Module.Free.exists_basis`：∀ (R : Type u) (M : Type v) {inst : Semiring R
} {inst_1 : AddCommMonoid M} {inst_2 : _root_.Module R M}   [self : Module.Free 
R M], Nonempty…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.Basis.mk_eq_rank''`：Module.Basis.mk_eq_rank'' {ι : Type v} (v : B
asis ι R M) : #ι = Module.rank R M
· 使用定理 `Cardinal.mk_prod`：mk_prod (α : Type u) (β : Type v) : #(α × β) = lift.{v
, u} #α * lift.{u, v} #β

--- 原说明 ---
The `S`-rank of `M ⊗[R] M'` is `(Module.rank S M).lift * (Module.rank R M').lift
`.
-/
theorem rank_tensorProduct :
    Module.rank R (M ⊗[S] M') =
      Cardinal.lift.{v'} (Module.rank R M) * Cardinal.lift.{v} (Module.rank S M') := by
  obtain ⟨⟨_, bM⟩⟩ := Module.Free.exists_basis (R := R) (M := M)
  obtain ⟨⟨_, bN⟩⟩ := Module.Free.exists_basis (R := S) (M := M')
  rw [← bM.mk_eq_rank'', ← bN.mk_eq_rank'', ← (bM.tensorProduct bN).mk_eq_rank'', Cardinal.mk_prod]

/-- If `M` and `M'` lie in the same universe, the `S`-rank of `M ⊗[R] M'` is
  `(Module.rank S M) * (Module.rank R M')`. -/
/-
**rank_tensorProduct'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rank_tensorProduct' : Module.rank R (M otimes[S] M₁) = Module.rank R M * M
odule.rank S M₁
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `rank_tensorProduct`：rank_tensorProduct : Module.rank R (M otimes[S] M') 
= Cardinal.lift.{v'} (Module.rank R M) * Cardinal.lift.{v} (Module.rank S M')
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `M` and `M'` lie in the same universe, the `S`-rank of `M ⊗[R] M'` is
  `(Module.rank S M) * (Module.rank R M')`.
-/
theorem rank_tensorProduct' :
    Module.rank R (M ⊗[S] M₁) = Module.rank R M * Module.rank S M₁ := by simp
/-
**Module.rank_baseChange** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.rank_baseChange : Module.rank R (R otimes[S] M') = Cardinal.lift.{u
} (Module.rank S M')
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `rank_tensorProduct`：rank_tensorProduct : Module.rank R (M otimes[S] M') 
= Cardinal.lift.{v'} (Module.rank R M) * Cardinal.lift.{v} (Module.rank S M')
· 使用定理 `Module.rank_self`：rank_self : Module.rank R R = 1
· 使用定理 `Cardinal.lift_one`：lift_one : lift 1 = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Module.rank_baseChange :
    Module.rank R (R ⊗[S] M') = Cardinal.lift.{u} (Module.rank S M') := by simp

/-- The `S`-`finrank` of `M ⊗[R] M'` is `(finrank S M) * (finrank R M')`. -/
@[simp]
/-
**Module.finrank_tensorProduct** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.finrank_tensorProduct : finrank R (M otimes[S] M') = finrank R M * 
finrank S M'
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `rank_tensorProduct`：rank_tensorProduct : Module.rank R (M otimes[S] M') 
= Cardinal.lift.{v'} (Module.rank R M) * Cardinal.lift.{v} (Module.rank S M')
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Cardinal.toNat_lift`：toNat_lift (c : Cardinal.{v}) : toNat (lift.{u, v} 
c) = toNat c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The `S`-`finrank` of `M ⊗[R] M'` is `(finrank S M) * (finrank R M')`.
-/
theorem Module.finrank_tensorProduct :
    finrank R (M ⊗[S] M') = finrank R M * finrank S M' := by simp [finrank]
/-
**Module.finrank_baseChange** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.finrank_baseChange : finrank R (R otimes[S] M') = finrank S M'
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Module.finrank_tensorProduct`：Module.finrank_tensorProduct : finrank R (
M otimes[S] M') = finrank R M * finrank S M'
· 使用定理 `Module.finrank_self`：finrank_self : finrank R R = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Module.finrank_baseChange : finrank R (R ⊗[S] M') = finrank S M' := by simp

end TensorProduct

section SubmoduleRank

section

open Module

namespace Submodule

/-
**Submodule.lt_of_le_of_finrank_lt_finrank** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`
。
形式化陈述：lt_of_le_of_finrank_lt_finrank {s t : Submodule R M} (le : s <= t) (lt : f
inrank R s < finrank R t) : s < t
参数：le : s <= t；lt : finrank R s < finrank R t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem lt_of_le_of_finrank_lt_finrank {s t : Submodule R M} (le : s ≤ t)
    (lt : finrank R s < finrank R t) : s < t :=
  lt_of_le_of_ne le fun h => ne_of_lt lt (by rw [h])
/-
**Submodule.lt_top_of_finrank_lt_finrank** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：lt_top_of_finrank_lt_finrank {s : Submodule R M} (lt : finrank R s < finra
nk R M) : s < ⊤
参数：lt : finrank R s < finrank R M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.lt_of_le_of_finrank_lt_finrank`：lt_of_le_of_finrank_lt_finrank
 {s t : Submodule R M} (le : s <= t) (lt : finrank R s < finrank R t) : s < t
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `finrank_top`：finrank_top : finrank R (⊤ : Submodule R M) = finrank R M
-/
theorem lt_top_of_finrank_lt_finrank {s : Submodule R M} (lt : finrank R s < finrank R M) :
    s < ⊤ := by
  rw [← finrank_top R M] at lt
  exact lt_of_le_of_finrank_lt_finrank le_top lt

end Submodule

variable [StrongRankCondition R]

/-- The dimension of a submodule is bounded by the dimension of the ambient space. -/
/-
**Submodule.finrank_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submodule.finrank_le [Module.Finite R M] (s : Submodule R M) : finrank R s
 <= finrank R M
参数：s : Submodule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.toNat_le_toNat`：toNat_le_toNat (hcd : c <= d) (hd : d < ℵ₀) : t
oNat c <= toNat d
· 使用定理 `Submodule.rank_le`：Submodule.rank_le (s : Submodule R M) : Module.rank R
 s <= Module.rank R M
· 使用定理 `Module.rank_lt_aleph0`：rank_lt_aleph0 [Module.Finite R M] : Module.rank 
R M < ℵ₀

--- 原说明 ---
The dimension of a submodule is bounded by the dimension of the ambient space.
-/
theorem Submodule.finrank_le [Module.Finite R M] (s : Submodule R M) :
    finrank R s ≤ finrank R M :=
  toNat_le_toNat (Submodule.rank_le s) (rank_lt_aleph0 _ _)

/-- Pushforwards of finite submodules have a smaller finrank. -/
/-
**Submodule.finrank_map_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submodule.finrank_map_le [Module R M'] (f : M ->ₗ[R] M') (p : Submodule R 
M) [Module.Finite R p] : finrank R (p.map f) <= finrank R p
参数：f : M ->ₗ[R] M'；p : Submodule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.finrank_le_finrank_of_rank_le_rank`：finrank_le_finrank_of_rank_le
_rank (h : lift.{w} (Module.rank R M) <= Cardinal.lift.{v} (Module.rank R N)) (h
' : Module.rank R N < ℵ₀) : fin…
· 使用定理 `lift_rank_map_le`：lift_rank_map_le (f : M ->ₗ[R] M') (p : Submodule R M)
 : Cardinal.lift.{v} (Module.rank R (p.map f)) <= Cardinal.lift.{v'} (Module.ran
k R p)
· 使用定理 `Module.rank_lt_aleph0`：rank_lt_aleph0 [Module.Finite R M] : Module.rank 
R M < ℵ₀

--- 原说明 ---
Pushforwards of finite submodules have a smaller finrank.
-/
theorem Submodule.finrank_map_le
    [Module R M'] (f : M →ₗ[R] M') (p : Submodule R M) [Module.Finite R p] :
    finrank R (p.map f) ≤ finrank R p :=
  finrank_le_finrank_of_rank_le_rank (lift_rank_map_le _ _) (rank_lt_aleph0 _ _)
/-
**Submodule.finrank_mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submodule.finrank_mono {s t : Submodule R M} [Module.Finite R t] (hst : s 
<= t) : finrank R s <= finrank R t
参数：hst : s <= t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.toNat_le_toNat`：toNat_le_toNat (hcd : c <= d) (hd : d < ℵ₀) : t
oNat c <= toNat d
· 使用引理 `Submodule.rank_mono`：Submodule.rank_mono {s t : Submodule R M} (h : s <=
 t) : Module.rank R s <= Module.rank R t
· 使用定理 `Module.rank_lt_aleph0`：rank_lt_aleph0 [Module.Finite R M] : Module.rank 
R M < ℵ₀
-/
theorem Submodule.finrank_mono {s t : Submodule R M} [Module.Finite R t] (hst : s ≤ t) :
    finrank R s ≤ finrank R t :=
  Cardinal.toNat_le_toNat (Submodule.rank_mono hst) (rank_lt_aleph0 R ↥t)

end

end SubmoduleRank

section Span

variable [StrongRankCondition R]

/-
**rank_span_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rank_span_le (s : Set M) : Module.rank R (span R s) <= #s
参数：s : Set M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.span_eq_range_linearCombination`：span_eq_range_linearCombination
 (s : Set M) : span R s = LinearMap.range (linearCombination R ((↑) : s -> M))
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `StrictMono.le_iff_le`：StrictMono.le_iff_le (hf : StrictMono f) {a b : α}
 : f a <= f b ↔ a <= b
· 使用定理 `Cardinal.lift_strictMono`：lift_strictMono : StrictMono lift
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `lift_rank_range_le`：lift_rank_range_le (f : M ->ₗ[R] M') : Cardinal.lift
.{v} (Module.rank R (LinearMap.range f)) <= Cardinal.lift.{v'} (Module.rank R M)
· 使用定理 `rank_finsupp_self`：rank_finsupp_self (ι : Type w) : Module.rank R (ι ->₀
 R) = Cardinal.lift.{u} #ι
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Cardinal.lift_lift`：lift_lift.{u_1} (a : Cardinal.{u_1}) : lift.{w} (lif
t.{v} a) = lift.{max v w} a
-/
theorem rank_span_le (s : Set M) : Module.rank R (span R s) ≤ #s := by
  rw [Finsupp.span_eq_range_linearCombination, ← lift_strictMono.le_iff_le]
  refine (lift_rank_range_le _).trans ?_
  rw [rank_finsupp_self]
  simp only [lift_lift, le_refl]
/-
**rank_span_finset_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rank_span_finset_le (s : Finset M) : Module.rank R (span R (s : Set M)) <=
 s.card
参数：s : Finset M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Cardinal.mk_fintype`：mk_fintype (α : Type u) [h : Fintype α] : #α = Fint
ype.card α
· 使用定理 `Fintype.card_coe`：Fintype.card_coe (s : Finset α) [Fintype s] : Fintype.
card s = #s
· 使用定理 `rank_span_le`：rank_span_le (s : Set M) : Module.rank R (span R s) <= #s
-/
theorem rank_span_finset_le (s : Finset M) : Module.rank R (span R (s : Set M)) ≤ s.card := by
  simpa using rank_span_le (s : Set M)
/-
**rank_span_of_finset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rank_span_of_finset (s : Finset M) : Module.rank R (span R (s : Set M)) < 
ℵ₀
参数：s : Finset M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `rank_span_finset_le`：rank_span_finset_le (s : Finset M) : Module.rank R 
(span R (s : Set M)) <= s.card
· 使用定理 `Cardinal.natCast_lt_aleph0`：∀ {n : ℕ}, ↑n < Cardinal.aleph0
-/
theorem rank_span_of_finset (s : Finset M) : Module.rank R (span R (s : Set M)) < ℵ₀ :=
  (rank_span_finset_le s).trans_lt natCast_lt_aleph0

open Submodule Module

variable (R) in
/-- The rank of a set of vectors as a natural number. -/
/-
**Set.finrank** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：(R : Type u) → {M : Type v} → [inst : Semiring R] → [inst_1 : AddCommMonoi
d M] → [_root_.Module R M] → Set M → ℕ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The rank of a set of vectors as a natural number.
-/
protected noncomputable def Set.finrank (s : Set M) : ℕ :=
  finrank R (span R s)
/-
**finrank_span_le_card** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finrank_span_le_card (s : Set M) [Fintype s] : finrank R (span R s) <= s.t
oFinset.card
参数：s : Set M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.finrank_le_of_rank_le`：finrank_le_of_rank_le {n : Nat} (h : Modul
e.rank R M <= ↑n) : finrank R M <= n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.toFinset_card`：toFinset_card {α : Type*} (s : Set α) [Fintype s] : s
.toFinset.card = Fintype.card s
· 使用定理 `Set.fintypeCard_eq_ncard`：fintypeCard_eq_ncard [Fintype s] : Fintype.car
d s = s.ncard
· 使用定理 `Cardinal.mk_fintype`：mk_fintype (α : Type u) [h : Fintype α] : #α = Fint
ype.card α
· 使用定理 `rank_span_le`：rank_span_le (s : Set M) : Module.rank R (span R s) <= #s
-/
theorem finrank_span_le_card (s : Set M) [Fintype s] : finrank R (span R s) ≤ s.toFinset.card :=
  finrank_le_of_rank_le (by simpa using rank_span_le (R := R) s)
/-
**finrank_span_finset_le_card** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finrank_span_finset_le_card (s : Finset M) : (s : Set M).finrank R <= s.ca
rd
参数：s : Finset M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `finrank_span_le_card`：finrank_span_le_card (s : Set M) [Fintype s] : fin
rank R (span R s) <= s.toFinset.card
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.toFinset_coe`：Finset.toFinset_coe (s : Finset α) [Fintype (s : Se
t α)] : (s : Set α).toFinset = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem finrank_span_finset_le_card (s : Finset M) : (s : Set M).finrank R ≤ s.card :=
  calc
    (s : Set M).finrank R ≤ (s : Set M).toFinset.card := finrank_span_le_card (M := M) s
    _ = s.card := by simp
/-
**finrank_range_le_card** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finrank_range_le_card {ι : Type*} [Fintype ι] (b : ι -> M) : (Set.range b)
.finrank R <= Fintype.card ι
参数：b : ι -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `finrank_span_le_card`：finrank_span_le_card (s : Set M) [Fintype s] : fin
rank R (span R s) <= s.toFinset.card
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.toFinset_range`：toFinset_range [DecidableEq α] [Fintype β] (f : β ->
 α) [Fintype (Set.range f)] : (Set.range f).toFinset = Finset.univ.image f
· 使用定理 `Finset.card_image_le`：card_image_le [DecidableEq β] : #(s.image f) <= #s
-/
theorem finrank_range_le_card {ι : Type*} [Fintype ι] (b : ι → M) :
    (Set.range b).finrank R ≤ Fintype.card ι := by
  classical
  refine (finrank_span_le_card _).trans ?_
  rw [Set.toFinset_range]
  exact Finset.card_image_le
/-
**finrank_span_eq_card** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finrank_span_eq_card [Nontrivial R] {ι : Type*} [Fintype ι] {b : ι -> M} (
hb : LinearIndependent R b) : finrank R (span R (Set.range b)) = Fintype.card ι
参数：hb : LinearIndependent R b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.finrank_eq_of_rank_eq`：finrank_eq_of_rank_eq {n : Nat} (h : Modul
e.rank R M = ↑n) : finrank R M = n
· 使用定理 `rank_span`：rank_span {v : ι -> M} (hv : LinearIndependent R v) : Module.
rank R ↑(span R (range v)) = #(range v)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_eq_nat_iff`：lift_eq_nat_iff {a : Cardinal.{u}} {n : Nat} :
 lift.{v} a = n ↔ a = n
· 使用定理 `Cardinal.lift_natCast`：lift_natCast (n : Nat) : lift.{u} (n : Cardinal.{
v}) = n
· 使用定理 `Cardinal.mk_fintype`：mk_fintype (α : Type u) [h : Fintype α] : #α = Fint
ype.card α
· 使用定理 `Cardinal.mk_range_eq_of_injective`：mk_range_eq_of_injective {α : Type u}
 {β : Type v} {f : α -> β} (hf : Injective f) : lift.{u} #(range f) = lift.{v} #
α
· 使用定理 `LinearIndependent.injective`：LinearIndependent.injective [Nontrivial R] 
(hv : LinearIndependent R v) : Injective v
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lift_inj`：lift_inj {a b : Cardinal.{u}} : lift.{v, u} a = lift.
{v, u} b ↔ a = b
-/
theorem finrank_span_eq_card [Nontrivial R] {ι : Type*} [Fintype ι] {b : ι → M}
    (hb : LinearIndependent R b) :
    finrank R (span R (Set.range b)) = Fintype.card ι :=
  finrank_eq_of_rank_eq
    (by
      have : Module.rank R (span R (Set.range b)) = #(Set.range b) := rank_span hb
      rwa [← lift_inj, mk_range_eq_of_injective hb.injective, Cardinal.mk_fintype, lift_natCast,
        lift_eq_nat_iff] at this)
/-
**finrank_span_set_eq_card** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finrank_span_set_eq_card {s : Set M} [Fintype s] (hs : LinearIndepOn R id 
s) : finrank R (span R s) = s.toFinset.card
参数：hs : LinearIndepOn R id s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.finrank_eq_of_rank_eq`：finrank_eq_of_rank_eq {n : Nat} (h : Modul
e.rank R M = ↑n) : finrank R M = n
· 使用定理 `rank_span_set`：rank_span_set {s : Set M} (hs : LinearIndepOn R id s) : M
odule.rank R ↑(span R s) = #s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.toFinset_card`：toFinset_card {α : Type*} (s : Set α) [Fintype s] : s
.toFinset.card = Fintype.card s
· 使用定理 `Cardinal.mk_fintype`：mk_fintype (α : Type u) [h : Fintype α] : #α = Fint
ype.card α
-/
theorem finrank_span_set_eq_card {s : Set M} [Fintype s] (hs : LinearIndepOn R id s) :
    finrank R (span R s) = s.toFinset.card :=
  finrank_eq_of_rank_eq
    (by
      have : Module.rank R (span R s) = #s := rank_span_set hs
      rwa [Cardinal.mk_fintype, ← Set.toFinset_card] at this)
/-
**finrank_span_finset_eq_card** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finrank_span_finset_eq_card {s : Finset M} (hs : LinearIndepOn R id (s : S
et M)) : finrank R (span R (s : Set M)) = s.card
参数：hs : LinearIndepOn R id (s : Set M)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.toFinset_coe`：Finset.toFinset_coe (s : Finset α) [Fintype (s : Se
t α)] : (s : Set α).toFinset = s
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `finrank_span_set_eq_card`：finrank_span_set_eq_card {s : Set M} [Fintype 
s] (hs : LinearIndepOn R id s) : finrank R (span R s) = s.toFinset.card
-/
theorem finrank_span_finset_eq_card {s : Finset M} (hs : LinearIndepOn R id (s : Set M)) :
    finrank R (span R (s : Set M)) = s.card := by
  convert! finrank_span_set_eq_card (s := (s : Set M)) hs
  ext
  simp
/-
**span_lt_of_subset_of_card_lt_finrank** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：span_lt_of_subset_of_card_lt_finrank {s : Set M} [Fintype s] {t : Submodul
e R M} (subset : s subseteq t) (card_lt : s.toFinset.card < finrank R t) : span 
R s < t
参数：subset : s subseteq t；card_lt : s.toFinset.card < finrank R t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.lt_of_le_of_finrank_lt_finrank`：lt_of_le_of_finrank_lt_finrank
 {s t : Submodule R M} (le : s <= t) (lt : finrank R s < finrank R t) : s < t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `finrank_span_le_card`：finrank_span_le_card (s : Set M) [Fintype s] : fin
rank R (span R s) <= s.toFinset.card
-/
theorem span_lt_of_subset_of_card_lt_finrank {s : Set M} [Fintype s] {t : Submodule R M}
    (subset : s ⊆ t) (card_lt : s.toFinset.card < finrank R t) : span R s < t :=
  lt_of_le_of_finrank_lt_finrank (span_le.mpr subset)
    (lt_of_le_of_lt (finrank_span_le_card _) card_lt)
/-
**span_lt_top_of_card_lt_finrank** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：span_lt_top_of_card_lt_finrank {s : Set M} [Fintype s] (card_lt : s.toFins
et.card < finrank R M) : span R s < ⊤
参数：card_lt : s.toFinset.card < finrank R M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.lt_top_of_finrank_lt_finrank`：lt_top_of_finrank_lt_finrank {s 
: Submodule R M} (lt : finrank R s < finrank R M) : s < ⊤
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `finrank_span_le_card`：finrank_span_le_card (s : Set M) [Fintype s] : fin
rank R (span R s) <= s.toFinset.card
-/
theorem span_lt_top_of_card_lt_finrank {s : Set M} [Fintype s]
    (card_lt : s.toFinset.card < finrank R M) : span R s < ⊤ :=
  lt_top_of_finrank_lt_finrank (lt_of_le_of_lt (finrank_span_le_card _) card_lt)
/-
**finrank_le_of_span_eq_top** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：finrank_le_of_span_eq_top {ι : Type*} [Fintype ι] {v : ι -> M} (hv : Submo
dule.span R (Set.range v) = ⊤) : finrank R M <= Fintype.card ι
参数：hv : Submodule.span R (Set.range v) = ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `finrank_top`：finrank_top : finrank R (⊤ : Submodule R M) = finrank R M
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `finrank_span_le_card`：finrank_span_le_card (s : Set M) [Fintype s] : fin
rank R (span R s) <= s.toFinset.card
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Set.toFinset_card`：toFinset_card {α : Type*} (s : Set α) [Fintype s] : s
.toFinset.card = Fintype.card s
· 使用定理 `Fintype.card_range_le`：card_range_le {α β : Type*} (f : α -> β) [Fintype
 α] [Fintype (Set.range f)] : Fintype.card (Set.range f) <= Fintype.card α
-/
lemma finrank_le_of_span_eq_top {ι : Type*} [Fintype ι] {v : ι → M}
    (hv : Submodule.span R (Set.range v) = ⊤) : finrank R M ≤ Fintype.card ι := by
  classical
  rw [← finrank_top, ← hv]
  exact (finrank_span_le_card _).trans (by convert! Fintype.card_range_le v; rw [Set.toFinset_card])

@[simp]
/-
**Pi.dim_spanSubset** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Pi.dim_spanSubset [Finite ι] [Nontrivial R] {s : Set ι} : Module.finrank R
 (Pi.spanSubset R s) = s.ncard
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Pi.spanSubset.eq_1`：∀ (R : Type u_2) {η : Type u_4} [inst : Semiring R] 
[inst_1 : Finite η] (s : Set η),   Pi.spanSubset R s = Submodule.span R (⇑(Pi.ba
sisFun R…
· 使用定理 `finrank_span_set_eq_card`：finrank_span_set_eq_card {s : Set M} [Fintype 
s] (hs : LinearIndepOn R id s) : finrank R (span R s) = s.toFinset.card
· 使用定理 `LinearIndepOn.id_image`：LinearIndepOn.id_image (hs : LinearIndepOn R v s
) : LinearIndepOn R id (v '' s)
· 使用定理 `Module.Basis.linearIndepOn`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_
5} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M]
 (b : Module.Bas…
· 使用定理 `Set.toFinset_card`：toFinset_card {α : Type*} (s : Set α) [Fintype s] : s
.toFinset.card = Fintype.card s
· 使用定理 `Fintype.card_eq_nat_card`：∀ {α : Type u_1} {x : Fintype α}, Fintype.card
 α = Nat.card α
· 使用定理 `Nat.card_coe_set_eq`：∀ {α : Type u_1} (s : Set α), Nat.card ↑s = s.ncard
· 使用定理 `Set.ncard_image_of_injective`：ncard_image_of_injective (s : Set α) (H : 
f.Injective) : (f '' s).ncard = s.ncard
· 使用定理 `Module.Basis.injective`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_6} [
inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] (b 
: Module.Bas…
-/
lemma Pi.dim_spanSubset [Finite ι] [Nontrivial R] {s : Set ι} :
    Module.finrank R (Pi.spanSubset R s) = s.ncard := by
  classical
  have := Fintype.ofFinite ι
  rw [Pi.spanSubset, finrank_span_set_eq_card <| (Pi.basisFun R ι).linearIndepOn _ |>.id_image,
    Set.toFinset_card, Fintype.card_eq_nat_card, Nat.card_coe_set_eq]
  exact Set.ncard_image_of_injective s <| (Pi.basisFun R ι).injective

end Span

section SubalgebraRank

open Module

section Semiring

variable {F E : Type*} [CommSemiring F] [Semiring E] [Algebra F E]

@[simp]
/-
**Subalgebra.rank_toSubmodule** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subalgebra.rank_toSubmodule (S : Subalgebra F E) : Module.rank F (Subalgeb
ra.toSubmodule S) = Module.rank F S
参数：S : Subalgebra F E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Subalgebra.rank_toSubmodule (S : Subalgebra F E) :
    Module.rank F (Subalgebra.toSubmodule S) = Module.rank F S :=
  rfl

@[simp]
/-
**Subalgebra.finrank_toSubmodule** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subalgebra.finrank_toSubmodule (S : Subalgebra F E) : finrank F (Subalgebr
a.toSubmodule S) = finrank F S
参数：S : Subalgebra F E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Subalgebra.finrank_toSubmodule (S : Subalgebra F E) :
    finrank F (Subalgebra.toSubmodule S) = finrank F S :=
  rfl
/-
**subalgebra_top_rank_eq_submodule_top_rank** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：subalgebra_top_rank_eq_submodule_top_rank : Module.rank F (⊤ : Subalgebra 
F E) = Module.rank F (⊤ : Submodule F E)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.top_toSubmodule`：top_toSubmodule : Subalgebra.toSubmodule (⊤ : S
ubalgebra R A) = ⊤
-/
theorem subalgebra_top_rank_eq_submodule_top_rank :
    Module.rank F (⊤ : Subalgebra F E) = Module.rank F (⊤ : Submodule F E) := by
  rw [← Algebra.top_toSubmodule]
  rfl
/-
**subalgebra_top_finrank_eq_submodule_top_finrank** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：subalgebra_top_finrank_eq_submodule_top_finrank : finrank F (⊤ : Subalgebr
a F E) = finrank F (⊤ : Submodule F E)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.top_toSubmodule`：top_toSubmodule : Subalgebra.toSubmodule (⊤ : S
ubalgebra R A) = ⊤
-/
theorem subalgebra_top_finrank_eq_submodule_top_finrank :
    finrank F (⊤ : Subalgebra F E) = finrank F (⊤ : Submodule F E) := by
  rw [← Algebra.top_toSubmodule]
  rfl
/-
**Subalgebra.rank_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subalgebra.rank_top : Module.rank F (⊤ : Subalgebra F E) = Module.rank F E
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `subalgebra_top_rank_eq_submodule_top_rank`：subalgebra_top_rank_eq_submod
ule_top_rank : Module.rank F (⊤ : Subalgebra F E) = Module.rank F (⊤ : Submodule
 F E)
· 使用定理 `rank_top`：rank_top : Module.rank R (⊤ : Submodule R M) = Module.rank R M
-/
theorem Subalgebra.rank_top : Module.rank F (⊤ : Subalgebra F E) = Module.rank F E := by
  rw [subalgebra_top_rank_eq_submodule_top_rank]
  exact _root_.rank_top F E

end Semiring

section Ring

variable {F E : Type*} [CommRing F] [IsDomain F] [Ring E] [Algebra F E]
variable [StrongRankCondition F] [IsTorsionFree F E] [Nontrivial E]

@[simp]
/-
**Subalgebra.rank_bot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subalgebra.rank_bot : Module.rank F (⊥ : Subalgebra F E) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LinearEquiv.rank_eq`：LinearEquiv.rank_eq (f : M ≃ₗ[R] M₁) : Module.rank 
R M = Module.rank R M₁
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.toSubmodule_bot`：toSubmodule_bot : Subalgebra.toSubmodule (⊥ : S
ubalgebra R A) = 1
· 使用定理 `Submodule.one_eq_span`：one_eq_span : (1 : Submodule R A) = R ∙ 1
· 使用定理 `rank_span_set`：rank_span_set {s : Set M} (hs : LinearIndepOn R id s) : M
odule.rank R ↑(span R s) = #s
· 使用定理 `Module.nontrivial`：∀ (R : Type u_5) (M : Type u_6) [inst : MonoidWithZer
o R] [Nontrivial M] [inst_2 : Zero M] [MulActionWithZero R M],   Nontrivial R
· 使用引理 `LinearIndepOn.singleton`：LinearIndepOn.singleton (hi : v i != 0) : Linea
rIndepOn R v {i}
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `Cardinal.mk_singleton`：mk_singleton {α : Type u} (x : α) : #({x} : Set α
) = 1
-/
theorem Subalgebra.rank_bot : Module.rank F (⊥ : Subalgebra F E) = 1 :=
  (Subalgebra.toSubmoduleEquiv (⊥ : Subalgebra F E)).symm.rank_eq.trans <| by
    rw [Algebra.toSubmodule_bot, one_eq_span, rank_span_set, mk_singleton _]
    have := Module.nontrivial F E
    exact .singleton one_ne_zero

@[simp]
/-
**Subalgebra.finrank_bot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subalgebra.finrank_bot : finrank F (⊥ : Subalgebra F E) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.finrank_eq_of_rank_eq`：finrank_eq_of_rank_eq {n : Nat} (h : Modul
e.rank R M = ↑n) : finrank R M = n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subalgebra.rank_bot`：Subalgebra.rank_bot : Module.rank F (⊥ : Subalgebra
 F E) = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Subalgebra.finrank_bot : finrank F (⊥ : Subalgebra F E) = 1 :=
  finrank_eq_of_rank_eq (by simp)

end Ring

end SubalgebraRank

section Extend

namespace Module.Basis

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    {W : Submodule R V} {m n : Type*}
    (bW : Basis m R W) (bQ : Basis n R (V ⧸ W))

/-- Given a basis `bW` of a submodule of an `R`-module `V`,
and a basis `bQ` of the quotient `V ⧸ W`,
this is a basis of `V` combining `bW` and a lift of `bQ`. -/
/-
**Module.Basis.sumQuot** 是 Mathlib 中的一个定义，位于命名空间 `Module.Basis`。
形式化陈述：sumQuot : Basis (m oplus n) R V
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a basis `bW` of a submodule of an `R`-module `V`,
and a basis `bQ` of the quotient `V ⧸ W`,
this is a basis of `V` combining `bW` and a lift of `bQ`.
-/
noncomputable def sumQuot :
    Basis (m ⊕ n) R V := by
  let b : m ⊕ n → V := Sum.elim (fun i ↦ bW i) ((Function.surjInv W.mkQ_surjective) ∘ bQ)
  have br : W.mkQ ∘ b ∘ Sum.inr = bQ := by
    ext j
    apply Function.rightInverse_surjInv W.mkQ_surjective
  apply Basis.mk (v := b)
  · apply LinearIndependent.sumElim_of_quotient
    · exact bW.linearIndependent
    · convert! bQ.linearIndependent
  · unfold b
    rw [Set.Sum.elim_range, Submodule.span_union,
      show Set.range (fun i ↦ (bW i : V)) = W.subtype '' (Set.range (fun i ↦ bW i)) by aesop,
      ← Submodule.map_span, bW.span_eq, Submodule.map_top, Submodule.range_subtype, top_le_iff,
      ← Submodule.map_mkQ_eq_top, Submodule.map_span, ← Set.range_comp, ← bQ.span_eq]
    congr 2

@[simp]
/-
**Module.Basis.sumQuot_inl** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：sumQuot_inl (i : m) : sumQuot bW bQ (Sum.inl i) = bW i
参数：i : m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Module.Basis.coe_mk`：coe_mk : ⇑(Basis.mk hli hsp) = v
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sumQuot_inl (i : m) :
    sumQuot bW bQ (Sum.inl i) = bW i := by
  simp [sumQuot]

@[simp]
/-
**Module.Basis.sumQuot_inr** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：sumQuot_inr (j : n) : Submodule.Quotient.mk (sumQuot bW bQ (Sum.inr j)) = 
bQ j
参数：j : n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Module.Basis.coe_mk`：coe_mk : ⇑(Basis.mk hli hsp) = v
· 使用定理 `Function.rightInverse_surjInv`：rightInverse_surjInv (hf : Surjective f) 
: RightInverse (surjInv hf) f
· 使用定理 `Submodule.mkQ_surjective`：mkQ_surjective : Function.Surjective p.mkQ
-/
theorem sumQuot_inr (j : n) :
    Submodule.Quotient.mk (sumQuot bW bQ (Sum.inr j)) = bQ j := by
  simpa only [sumQuot, Basis.coe_mk, Sum.elim_inr, Function.comp_apply, ← W.mkQ_apply]
    using Function.rightInverse_surjInv W.mkQ_surjective _

@[simp]
/-
**Module.Basis.sumQuot_repr_left** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：sumQuot_repr_left (i : m) : (sumQuot bW bQ).repr (bW i) = Finsupp.single (
Sum.inl i) 1
参数：i : m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.Basis.apply_eq_iff`：apply_eq_iff {b : Basis ι R M} {x : M} {i : ι
} : b i = x ↔ b.repr x = Finsupp.single i 1
· 使用定理 `Module.Basis.sumQuot_inl`：sumQuot_inl (i : m) : sumQuot bW bQ (Sum.inl i
) = bW i
-/
theorem sumQuot_repr_left (i : m) :
    (sumQuot bW bQ).repr (bW i) = Finsupp.single (Sum.inl i) 1 := by
  rw [← Module.Basis.apply_eq_iff, sumQuot_inl]

set_option backward.isDefEq.respectTransparency false in
/-
**Module.Basis.sumQuot_repr_inl** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：sumQuot_repr_inl (w : W) (i : m) : (sumQuot bW bQ).repr w (Sum.inl i) = bW
.repr w i
参数：w : W；i : m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.Basis.repr_apply_eq`：repr_apply_eq (f : M -> ι -> R) (hadd : fora
ll x y, f (x + y) = f x + f y) (hsmul : forall (c : R) (x : M), f (c • x) = c • 
f x) (f_eq : for…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `Module.Basis.sumQuot_repr_left`：sumQuot_repr_left (i : m) : (sumQuot bW 
bQ).repr (bW i) = Finsupp.single (Sum.inl i) 1
· 使用定理 `Finsupp.single_apply`：single_apply [Decidable (a = a')] : single a b a' 
= if a = a' then b else 0
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Sum.inl.injEq`：∀ {α : Type u} {β : Type v} (val val_1 : α), (Sum.inl val
 = Sum.inl val_1) = (val = val_1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sumQuot_repr_inl (w : W) (i : m) :
    (sumQuot bW bQ).repr w (Sum.inl i) = bW.repr w i := by
  classical
  refine Eq.symm <| (bW.repr_apply_eq
      (fun w i => (sumQuot bW bQ).repr (W.subtype w) (Sum.inl i)) ?_ ?_ ?_ w i) <;>
  aesop (add simp Finsupp.single_apply)

@[simp]
/-
**Module.Basis.sumQuot_repr_inl_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：sumQuot_repr_inl_of_mem (v : V) (hv : v in W) (i : m) : (sumQuot bW bQ).re
pr v (Sum.inl i) = bW.repr ⟨v, hv⟩ i
参数：v : V；hv : v in W；i : m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.sumQuot_repr_inl`：sumQuot_repr_inl (w : W) (i : m) : (sumQu
ot bW bQ).repr w (Sum.inl i) = bW.repr w i
-/
theorem sumQuot_repr_inl_of_mem (v : V) (hv : v ∈ W) (i : m) :
    (sumQuot bW bQ).repr v (Sum.inl i) = bW.repr ⟨v, hv⟩ i :=
  sumQuot_repr_inl bW bQ ⟨v, hv⟩ i

@[simp]
/-
**Module.Basis.sumQuot_repr_inr** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：sumQuot_repr_inr (v : V) (j : n) : (sumQuot bW bQ).repr v (Sum.inr j) = bQ
.repr (W.mkQ v) j
参数：v : V；j : n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.comp_apply`：comp_apply (x : M₁) : f.comp g x = f (g x)
· 使用定理 `LinearMap.ext_iff`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ : 
Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid M
] [inst…
· 使用定理 `Module.Basis.ext`：ext {f₁ f₂ : M ->ₛₗ[σ] M₁} (h : forall i, f₁ (b i) = f
₂ (b i)) : f₁ = f₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Module.Basis.sumQuot_inl`：sumQuot_inl (i : m) : sumQuot bW bQ (Sum.inl i
) = bW i
· 使用定理 `Module.Basis.coord_apply`：∀ {ι : Type u_10} {R : Type u_11} {M : Type u_
12} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M
] (b : Module.…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Module.Basis.sumQuot_repr_left`：sumQuot_repr_left (i : m) : (sumQuot bW 
bQ).repr (bW i) = Finsupp.single (Sum.inl i) 1
· 使用定理 `Finsupp.single_eq_of_ne`：single_eq_of_ne (h : a' != a) : (single a b : α
 ->₀ M) a' = 0
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.Quotient.mk_eq_zero`：mk_eq_zero : (mk x : M ⧸ p) = 0 ↔ x in p
· 使用定理 `Submodule.coe_mem`：coe_mem (x : p) : (x : M) in p
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
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Module.Basis.repr_self`：repr_self : b.repr (b i) = Finsupp.single i 1
· 使用定理 `Finsupp.single_apply`：single_apply [Decidable (a = a')] : single a b a' 
= if a = a' then b else 0
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Sum.inr.injEq`：∀ {α : Type u} {β : Type v} (val val_1 : β), (Sum.inr val
 = Sum.inr val_1) = (val = val_1)
（共 31 条，此处仅展示前 30 条）
-/
theorem sumQuot_repr_inr (v : V) (j : n) :
    (sumQuot bW bQ).repr v (Sum.inr j) = bQ.repr (W.mkQ v) j := by
  simp only [← Module.Basis.coord_apply]
  rw [← LinearMap.comp_apply]
  revert v
  rw [← LinearMap.ext_iff]
  apply (sumQuot bW bQ).ext
  intro x
  induction x with
  | inl i =>
    simp [sumQuot_inl, LinearMap.comp_apply,
      (Quotient.mk_eq_zero W).mpr (Submodule.coe_mem (bW i))]
  | inr i =>
    classical
    simp [LinearMap.comp_apply, sumQuot_inr, Finsupp.single_apply]
/-
**Module.Basis.sumQuot_repr_inr_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：sumQuot_repr_inr_of_mem (v : V) (hv : v in W) (j : n) : (sumQuot bW bQ).re
pr v (Sum.inr j) = 0
参数：v : V；hv : v in W；j : n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.sumQuot_repr_inr`：sumQuot_repr_inr (v : V) (j : n) : (sumQu
ot bW bQ).repr v (Sum.inr j) = bQ.repr (W.mkQ v) j
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
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sumQuot_repr_inr_of_mem (v : V) (hv : v ∈ W) (j : n) :
    (sumQuot bW bQ).repr v (Sum.inr j) = 0 := by
  suffices W.mkQ v = 0 by simp [sumQuot_repr_inr, this]
  aesop

end Module.Basis

end Extend

