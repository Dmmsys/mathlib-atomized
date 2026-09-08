/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Floris van Doorn, Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Action.Basic
public import Mathlib.Algebra.Group.Action.Opposite
public import Mathlib.Algebra.Group.Pointwise.Set.Scalar
public import Mathlib.Algebra.Group.Units.Equiv
public import Mathlib.Data.Set.Lattice.Image
public import Mathlib.Data.Set.Pairwise.Basic
public import Mathlib.Algebra.Group.Pointwise.Set.Basic

/-!
# Pointwise actions on sets

This file proves that several kinds of actions of a type `α` on another type `β` transfer to actions
of `α`/`Set α` on `Set β`.

## Implementation notes

* We put all instances in the scope `Pointwise`, so that these instances are not available by
  default. Note that we do not mark them as reducible (as argued by note [reducible non-instances])
  since we expect the scope to be open whenever the instances are actually used (and making the
  instances reducible changes the behavior of `simp`).
-/

@[expose] public section

assert_not_exists MonoidWithZero IsOrderedMonoid

open Function MulOpposite
open scoped Pointwise

variable {F α β γ : Type*}

namespace Set

/-! ### Translation/scaling of sets -/

@[to_additive vadd_set_prod]
/-
**Set.smul_set_prod** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：smul_set_prod {M α : Type*} [SMul M α] [SMul M β] (c : M) (s : Set α) (t :
 Set β) : c • (s ×ˢ t) = (c • s) ×ˢ (c • t)
参数：c : M；s : Set α；t : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.prodMap_image_prod`：prodMap_image_prod (f : α -> β) (g : γ -> δ) (s 
: Set α) (t : Set γ) : (Prod.map f g) '' (s ×ˢ t) = (f '' s) ×ˢ (g '' t)

--- 原说明 ---
### Translation/scaling of sets
-/
lemma smul_set_prod {M α : Type*} [SMul M α] [SMul M β] (c : M) (s : Set α) (t : Set β) :
    c • (s ×ˢ t) = (c • s) ×ˢ (c • t) :=
  prodMap_image_prod (c • ·) (c • ·) s t

@[to_additive]
/-
**Set.smul_set_pi** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：smul_set_pi {G ι : Type*} {α : ι -> Type*} [Group G] [forall i, MulAction 
G (α i)] (c : G) (I : Set ι) (s : forall i, Set (α i)) : c • I.pi s = I.pi (c • 
s)
参数：α i；c : G；I : Set ι；s : forall i, Set (α i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.smul_set_pi_of_surjective`：smul_set_pi_of_surjective (c : M) (I : Se
t ι) (s : forall i, Set (π i)) (hsurj : forall i ∉ I, Function.Surjective (c • ·
 : π i -> π i)) : c…
· 使用定理 `Function.Bijective.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → 
β}, Function.Bijective f → Function.Surjective f
· 使用定理 `MulAction.bijective`：∀ {α : Type u_5} {β : Type u_6} [inst : Group α] [i
nst_1 : MulAction α β] (g : α), Function.Bijective fun x => g • x
-/
lemma smul_set_pi {G ι : Type*} {α : ι → Type*} [Group G] [∀ i, MulAction G (α i)]
    (c : G) (I : Set ι) (s : ∀ i, Set (α i)) : c • I.pi s = I.pi (c • s) :=
  smul_set_pi_of_surjective c I s fun _ _ ↦ (MulAction.bijective c).surjective

@[to_additive]
/-
**Set.smul_set_pi_of_isUnit** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：smul_set_pi_of_isUnit {M ι : Type*} {α : ι -> Type*} [Monoid M] [forall i,
 MulAction M (α i)] {c : M} (hc : IsUnit c) (I : Set ι) (s : forall i, Set (α i)
) : c • I.pi s = I.pi (c • s)
参数：α i；hc : IsUnit c；I : Set ι；s : forall i, Set (α i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `instCanLiftUnitsValIsUnit`：∀ {M : Type u_1} [inst : Monoid M], CanLift M
 Mˣ Units.val IsUnit
· 使用引理 `Set.smul_set_pi`：smul_set_pi {G ι : Type*} {α : ι -> Type*} [Group G] [f
orall i, MulAction G (α i)] (c : G) (I : Set ι) (s : forall i, Set (α i)) : c • 
I.pi …
-/
lemma smul_set_pi_of_isUnit {M ι : Type*} {α : ι → Type*} [Monoid M] [∀ i, MulAction M (α i)]
    {c : M} (hc : IsUnit c) (I : Set ι) (s : ∀ i, Set (α i)) : c • I.pi s = I.pi (c • s) := by
  lift c to Mˣ using hc
  exact smul_set_pi c I s

section Mul
variable {ι : Sort*} {κ : ι → Sort*} [Mul α] {s s₁ s₂ t t₁ t₂ u : Set α} {a b : α}

/-
**Set.smul_set_subset_mul** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_2} [inst : Mul α] {s t : Set α} {a : α}, a ∈ s → a • t ⊆ s *
 t
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_subset_image2_right`：image_subset_image2_right (ha : a in s) :
 f a '' t subseteq image2 f s t
-/
@[to_additive] lemma smul_set_subset_mul : a ∈ s → a • t ⊆ s * t := image_subset_image2_right

open scoped RightActions in
/-
**Set.op_smul_set_subset_mul** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_2} [inst : Mul α] {s t : Set α} {a : α}, a ∈ t → MulOpposite
.op a • s ⊆ s * t
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_subset_image2_left`：image_subset_image2_left (hb : b in t) : (
fun a => f a b) '' s subseteq image2 f s t
-/
@[to_additive] lemma op_smul_set_subset_mul : a ∈ t → s <• a ⊆ s * t := image_subset_image2_left

@[to_additive]
/-
**Set.image_op_smul** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：image_op_smul : (op '' s) • t = t * s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image2_smul`：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β] {s : 
Set α} {t : Set β}, Set.image2 (fun x1 x2 => x1 • x2) s t = s • t
· 使用定理 `Set.image2_mul`：image2_mul : image2 (· * ·) s t = s * t
· 使用定理 `Set.image2_image_left`：image2_image_left (f : γ -> β -> δ) (g : α -> γ) 
: image2 f (g '' s) t = image2 (fun a b => f (g a) b) s t
· 使用定理 `Set.image2_swap`：image2_swap (s : Set α) (t : Set β) : image2 f s t = im
age2 (fun a b => f b a) t s
-/
theorem image_op_smul : (op '' s) • t = t * s := by
  rw [← image2_smul, ← image2_mul, image2_image_left, image2_swap]
  rfl

@[to_additive (attr := simp)]
/-
**Set.iUnion_op_smul_set** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iUnion_op_smul_set (s t : Set α) : ⋃ a in t, MulOpposite.op a • s = s * t
参数：s t : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.iUnion_image_right`：iUnion_image_right : ⋃ b in t, (f · b) '' s = im
age2 f s t
-/
theorem iUnion_op_smul_set (s t : Set α) : ⋃ a ∈ t, MulOpposite.op a • s = s * t :=
  iUnion_image_right _

@[to_additive]
/-
**Set.mul_subset_iff_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mul_subset_iff_left : s * t subseteq u ↔ forall a in s, a • t subseteq u
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_subset_iff_left`：image2_subset_iff_left : image2 f s t subset
eq u ↔ forall a in s, (fun b => f a b) '' t subseteq u
-/
theorem mul_subset_iff_left : s * t ⊆ u ↔ ∀ a ∈ s, a • t ⊆ u :=
  image2_subset_iff_left

@[to_additive]
/-
**Set.mul_subset_iff_right** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mul_subset_iff_right : s * t subseteq u ↔ forall b in t, op b • s subseteq
 u
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_subset_iff_right`：image2_subset_iff_right : image2 f s t subs
eteq u ↔ forall b in t, (fun a => f a b) '' s subseteq u
-/
theorem mul_subset_iff_right : s * t ⊆ u ↔ ∀ b ∈ t, op b • s ⊆ u :=
  image2_subset_iff_right
/-
**Set.pair_mul** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_2} [inst : Mul α] (a b : α) (s : Set α), {a, b} * s = a • s 
∪ b • s
参数：a b : α；s : Set α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.insert_eq`：insert_eq (x : α) (s : Set α) : insert x s = ({x} : Set α
) union s
· 使用定理 `Set.union_mul`：union_mul : (s₁ union s₂) * t = s₁ * t union s₂ * t
· 使用定理 `Set.singleton_mul`：singleton_mul : {a} * t = (a * ·) '' t
-/
@[to_additive] lemma pair_mul (a b : α) (s : Set α) : {a, b} * s = a • s ∪ b • s := by
  rw [insert_eq, union_mul, singleton_mul, singleton_mul]; rfl

open scoped RightActions
/-
**Set.mul_pair** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_2} [inst : Mul α] (s : Set α) (a b : α), s * {a, b} = MulOpp
osite.op a • s ∪ MulOpposite.op b • s
参数：s : Set α；a b : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.insert_eq`：insert_eq (x : α) (s : Set α) : insert x s = ({x} : Set α
) union s
· 使用定理 `Set.mul_union`：mul_union : s * (t₁ union t₂) = s * t₁ union s * t₂
· 使用定理 `Set.mul_singleton`：mul_singleton : s * {b} = (· * b) '' s
-/
@[to_additive] lemma mul_pair (s : Set α) (a b : α) : s * {a, b} = s <• a ∪ s <• b := by
  rw [insert_eq, mul_union, mul_singleton, mul_singleton]; rfl
/-
**Set.range_mul** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_2} [inst : Mul α] {ι : Sort u_7} (a : α) (f : ι → α), (Set.r
ange fun i => a * f i) = a • Set.range f
参数：a : α；f : ι → α；Set.range fun i => a * f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.range_smul`：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β] {ι : S
ort u_5} (a : α) (f : ι → β),   (Set.range fun i => a • f i) = a • Set.range f
-/
@[to_additive] lemma range_mul {ι : Sort*} (a : α) (f : ι → α) :
    range (fun i ↦ a * f i) = a • range f := range_smul a f

end Mul

@[to_additive]
/-
**Set.image_smul_distrib** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：image_smul_distrib [Mul α] [Mul β] [FunLike F α β] [MulHomClass F α β] (f 
: F) (a : α) (s : Set α) : f '' (a • s) = f a • f '' s
参数：f : F；a : α；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_comm`：image_comm {β'} {f : β -> γ} {g : α -> β} {f' : α -> β'}
 {g' : β' -> γ} (h_comm : forall a, f (g a) = g' (f' a)) : (s.image g).image f =
 (s.…
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
-/
lemma image_smul_distrib [Mul α] [Mul β] [FunLike F α β] [MulHomClass F α β]
    (f : F) (a : α) (s : Set α) :
    f '' (a • s) = f a • f '' s :=
  image_comm <| map_mul _ _

open scoped RightActions in
@[to_additive]
/-
**Set.image_op_smul_distrib** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：image_op_smul_distrib [Mul α] [Mul β] [FunLike F α β] [MulHomClass F α β] 
(f : F) (a : α) (s : Set α) : f '' (s <• a) = f '' s <• f a
参数：f : F；a : α；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_comm`：image_comm {β'} {f : β -> γ} {g : α -> β} {f' : α -> β'}
 {g' : β' -> γ} (h_comm : forall a, f (g a) = g' (f' a)) : (s.image g).image f =
 (s.…
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
-/
lemma image_op_smul_distrib [Mul α] [Mul β] [FunLike F α β] [MulHomClass F α β]
    (f : F) (a : α) (s : Set α) : f '' (s <• a) = f '' s <• f a := image_comm fun _ ↦ map_mul ..

section Semigroup
variable [Semigroup α]

@[to_additive]
/-
**Set.op_smul_set_mul_eq_mul_smul_set** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：op_smul_set_mul_eq_mul_smul_set (a : α) (s : Set α) (t : Set α) : op a • s
 * t = s * a • t
参数：a : α；s : Set α；t : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.op_smul_set_smul_eq_smul_smul_set`：op_smul_set_smul_eq_smul_smul_set
 (a : α) (s : Set β) (t : Set γ) (h : forall (a : α) (b : β) (c : γ), (op a • b)
 • c = b • a • c) : (op a •…
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
-/
lemma op_smul_set_mul_eq_mul_smul_set (a : α) (s : Set α) (t : Set α) :
    op a • s * t = s * a • t :=
  op_smul_set_smul_eq_smul_smul_set _ _ _ fun _ _ _ => mul_assoc _ _ _

end Semigroup

section IsLeftCancelSMul

variable [SMul α β] [IsLeftCancelSMul α β] {s : Set α} {t : Set β}

@[to_additive]
/-
**Set.pairwiseDisjoint_smul_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：pairwiseDisjoint_smul_iff : s.PairwiseDisjoint (· • t) ↔ (s ×ˢ t).InjOn fu
n p => p.1 • p.2
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.pairwiseDisjoint_image_right_iff`：pairwiseDisjoint_image_right_iff {
f : α -> β -> γ} {s : Set α} {t : Set β} (hf : forall a in s, Injective (f a)) :
 (s.PairwiseDisjoint fun a…
· 使用引理 `IsLeftCancelSMul.left_cancel`：IsLeftCancelSMul.left_cancel {G P} [SMul G
 P] [IsLeftCancelSMul G P] (a : G) (b c : P) : a • b = a • c -> b = c
-/
theorem pairwiseDisjoint_smul_iff :
    s.PairwiseDisjoint (· • t) ↔ (s ×ˢ t).InjOn fun p ↦ p.1 • p.2 :=
  pairwiseDisjoint_image_right_iff fun a _ _ _ h ↦ IsLeftCancelSMul.left_cancel a _ _ h

end IsLeftCancelSMul

@[to_additive]
/-
**Set.smulCommClass_set** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
形式化陈述：smulCommClass_set [SMul α γ] [SMul β γ] [SMulCommClass α β γ] : SMulCommCl
ass α β (Set γ)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Commute.set_image`：∀ {α : Type u_1} {f g : α → α}, Function.Com
mute f g → Function.Commute (Set.image f) (Set.image g)
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
-/
instance smulCommClass_set [SMul α γ] [SMul β γ] [SMulCommClass α β γ] :
    SMulCommClass α β (Set γ) :=
  ⟨fun _ _ ↦ Commute.set_image <| smul_comm _ _⟩

@[to_additive]
/-
**Set.smulCommClass_set'** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
形式化陈述：smulCommClass_set' [SMul α γ] [SMul β γ] [SMulCommClass α β γ] : SMulCommC
lass α (Set β) (Set γ)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_image2_distrib_right`：image_image2_distrib_right {g : γ -> δ} 
{f' : α -> β' -> δ} {g' : β -> β'} (h_distrib : forall a b, g (f a b) = f' a (g'
 b)) : (image2 f s t…
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
-/
instance smulCommClass_set' [SMul α γ] [SMul β γ] [SMulCommClass α β γ] :
    SMulCommClass α (Set β) (Set γ) :=
  ⟨fun _ _ _ ↦ image_image2_distrib_right <| smul_comm _⟩

@[to_additive]
/-
**Set.smulCommClass_set''** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
形式化陈述：smulCommClass_set'' [SMul α γ] [SMul β γ] [SMulCommClass α β γ] : SMulComm
Class (Set α) β (Set γ)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
-/
instance smulCommClass_set'' [SMul α γ] [SMul β γ] [SMulCommClass α β γ] :
    SMulCommClass (Set α) β (Set γ) :=
  haveI := SMulCommClass.symm α β γ
  SMulCommClass.symm _ _ _

@[to_additive]
/-
**Set.smulCommClass** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
形式化陈述：smulCommClass [SMul α γ] [SMul β γ] [SMulCommClass α β γ] : SMulCommClass 
(Set α) (Set β) (Set γ)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_left_comm`：image2_left_comm {f : α -> δ -> ε} {g : β -> γ -> 
δ} {f' : α -> γ -> δ'} {g' : β -> δ' -> ε} (h_left_comm : forall a b c, f a (g b
 c) = g' b…
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
-/
instance smulCommClass [SMul α γ] [SMul β γ] [SMulCommClass α β γ] :
    SMulCommClass (Set α) (Set β) (Set γ) :=
  ⟨fun _ _ _ ↦ image2_left_comm smul_comm⟩

@[to_additive]
/-
**Set.isScalarTower** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
形式化陈述：isScalarTower [SMul α β] [SMul α γ] [SMul β γ] [IsScalarTower α β γ] : IsS
calarTower α β (Set γ) where smul_assoc a b T
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用定理 `Set.image_image`：image_image (g : β -> γ) (f : α -> β) (s : Set α) : g '
' f '' s = (fun x => g (f x)) '' s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance isScalarTower [SMul α β] [SMul α γ] [SMul β γ] [IsScalarTower α β γ] :
    IsScalarTower α β (Set γ) where
  smul_assoc a b T := by simp only [← image_smul, image_image, smul_assoc]

@[to_additive]
/-
**Set.isScalarTower'** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
形式化陈述：isScalarTower' [SMul α β] [SMul α γ] [SMul β γ] [IsScalarTower α β γ] : Is
ScalarTower α (Set β) (Set γ)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_image_left_comm`：image2_image_left_comm {f : α' -> β -> γ} {g
 : α -> α'} {f' : α -> β -> δ} {g' : δ -> γ} (h_left_comm : forall a b, f (g a) 
b = g' (f' a b))…
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
-/
instance isScalarTower' [SMul α β] [SMul α γ] [SMul β γ] [IsScalarTower α β γ] :
    IsScalarTower α (Set β) (Set γ) :=
  ⟨fun _ _ _ ↦ image2_image_left_comm <| smul_assoc _⟩

@[to_additive]
/-
**Set.isScalarTower''** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
形式化陈述：isScalarTower'' [SMul α β] [SMul α γ] [SMul β γ] [IsScalarTower α β γ] : I
sScalarTower (Set α) (Set β) (Set γ) where smul_assoc _ _ _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image2_assoc`：image2_assoc {f : δ -> γ -> ε} {g : α -> β -> δ} {f' :
 α -> ε' -> ε} {g' : β -> γ -> ε'} (h_assoc : forall a b c, f (g a b) c = f' a (
g' b c…
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
-/
instance isScalarTower'' [SMul α β] [SMul α γ] [SMul β γ] [IsScalarTower α β γ] :
    IsScalarTower (Set α) (Set β) (Set γ) where
  smul_assoc _ _ _ := image2_assoc smul_assoc

@[to_additive]
/-
**Set.isCentralScalar** 是 Mathlib 中的一个实例，位于命名空间 `Set`。
形式化陈述：isCentralScalar [SMul α β] [SMul αᵐᵒᵖ β] [IsCentralScalar α β] : IsCentral
Scalar α (Set β)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsCentralScalar.op_smul_eq_smul`：∀ {M : Type u_9} {α : Type u_10} {inst 
: SMul M α} {inst_1 : SMul Mᵐᵒᵖ α} [self : IsCentralScalar M α] (m : M) (a : α),
   MulOpposite.op m •…
-/
instance isCentralScalar [SMul α β] [SMul αᵐᵒᵖ β] [IsCentralScalar α β] :
    IsCentralScalar α (Set β) :=
  ⟨fun _ S ↦ (congr_arg fun f ↦ f '' S) <| funext fun _ ↦ op_smul_eq_smul _ _⟩

/-- A multiplicative action of a monoid `α` on a type `β` gives a multiplicative action of `Set α`
on `Set β`. -/
@[to_additive (attr := instance_reducible)
/-- An additive action of an additive monoid `α` on a type `β` gives an additive action of `Set α`
on `Set β` -/]
/-
**Set.mulAction** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：{α : Type u_2} → {β : Type u_3} → [inst : Monoid α] → [MulAction α β] → Mu
lAction (Set α) (Set β)
参数：Set α；Set β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected noncomputable def mulAction [Monoid α] [MulAction α β] : MulAction (Set α) (Set β) where
  mul_smul _ _ _ := image2_assoc mul_smul
  one_smul s := image2_singleton_left.trans <| by simp_rw [one_smul, image_id']

/-- A multiplicative action of a monoid on a type `β` gives a multiplicative action on `Set β`. -/
@[to_additive (attr := instance_reducible)
/-- An additive action of an additive monoid on a type `β` gives an additive action on `Set β`. -/]
/-
**Set.mulActionSet** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：{α : Type u_2} → {β : Type u_3} → [inst : Monoid α] → [MulAction α β] → Mu
lAction α (Set β)
参数：Set β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected def mulActionSet [Monoid α] [MulAction α β] : MulAction α (Set β) where
  mul_smul _ _ _ := by simp only [← image_smul, image_image, ← mul_smul]
  one_smul _ := by simp only [← image_smul, one_smul, image_id']

scoped[Pointwise] attribute [instance] Set.mulActionSet Set.addActionSet Set.mulAction Set.addAction

section Group

variable [Group α] [MulAction α β] {s t A B : Set β} {a b : α} {x : β}

@[to_additive (attr := simp)]
/-
**Set.smul_mem_smul_set_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：smul_mem_smul_set_iff : a • x in a • s ↔ x in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.mem_set_image`：∀ {α : Type u_1} {β : Type u_2} {f : α
 → β}, Function.Injective f → ∀ {s : Set α} {a : α}, f a ∈ f '' s ↔ a ∈ s
· 使用定理 `MulAction.injective`：∀ {α : Type u_5} {β : Type u_6} [inst : Group α] [i
nst_1 : MulAction α β] (g : α), Function.Injective fun x => g • x
-/
theorem smul_mem_smul_set_iff : a • x ∈ a • s ↔ x ∈ s :=
  (MulAction.injective _).mem_set_image

@[to_additive]
/-
**Set.mem_smul_set_iff_inv_smul_mem** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mem_smul_set_iff_inv_smul_mem : x in a • A ↔ a⁻¹ • x in A
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_image_equiv`：∀ {α : Type u_3} {β : Type u_4} {S : Set α} {f : α 
≃ β} {x : β}, x ∈ ⇑f '' S ↔ f.symm x ∈ S
-/
theorem mem_smul_set_iff_inv_smul_mem : x ∈ a • A ↔ a⁻¹ • x ∈ A :=
  show x ∈ MulAction.toPerm a '' A ↔ _ from mem_image_equiv

@[to_additive]
/-
**Set.mem_inv_smul_set_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mem_inv_smul_set_iff : x in a⁻¹ • A ↔ a • x in A
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_inv_smul_set_iff : x ∈ a⁻¹ • A ↔ a • x ∈ A := by
  simp only [← image_smul, mem_image, inv_smul_eq_iff, exists_eq_right]

@[to_additive (attr := simp)]
/-
**Set.mem_smul_set_inv** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：mem_smul_set_inv {s : Set α} : a in b • s⁻¹ ↔ b in a • s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mem_smul_set_inv {s : Set α} : a ∈ b • s⁻¹ ↔ b ∈ a • s := by
  simp [mem_smul_set_iff_inv_smul_mem]

@[to_additive]
/-
**Set.preimage_smul** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_smul (a : α) (t : Set β) : (fun x => a • x) ⁻¹' t = a⁻¹ • t
参数：a : α；t : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用引理 `Equiv.image_symm_eq_preimage`：image_symm_eq_preimage (e : α ≃ β) (s : Se
t β) : e.symm '' s = e ⁻¹' s
-/
theorem preimage_smul (a : α) (t : Set β) : (fun x ↦ a • x) ⁻¹' t = a⁻¹ • t :=
  ((MulAction.toPerm a).image_symm_eq_preimage _).symm

@[to_additive]
/-
**Set.preimage_smul_inv** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：preimage_smul_inv (a : α) (t : Set β) : (fun x => a⁻¹ • x) ⁻¹' t = a • t
参数：a : α；t : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.preimage_smul`：preimage_smul (a : α) (t : Set β) : (fun x => a • x) 
⁻¹' t = a⁻¹ • t
-/
theorem preimage_smul_inv (a : α) (t : Set β) : (fun x ↦ a⁻¹ • x) ⁻¹' t = a • t :=
  preimage_smul (toUnits a)⁻¹ t

@[to_additive (attr := simp)]
/-
**Set.smul_set_subset_smul_set_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：smul_set_subset_smul_set_iff : a • A subseteq a • B ↔ A subseteq B
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_subset_image_iff`：image_subset_image_iff {f : α -> β} (hf : In
jective f) : f '' s subseteq f '' t ↔ s subseteq t
· 使用定理 `MulAction.injective`：∀ {α : Type u_5} {β : Type u_6} [inst : Group α] [i
nst_1 : MulAction α β] (g : α), Function.Injective fun x => g • x
-/
theorem smul_set_subset_smul_set_iff : a • A ⊆ a • B ↔ A ⊆ B :=
  image_subset_image_iff <| MulAction.injective _

@[to_additive]
/-
**Set.smul_set_subset_iff_subset_inv_smul_set** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：smul_set_subset_iff_subset_inv_smul_set : a • A subseteq B ↔ A subseteq a⁻
¹ • B
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用引理 `Equiv.image_symm_eq_preimage`：image_symm_eq_preimage (e : α ≃ β) (s : Se
t β) : e.symm '' s = e ⁻¹' s
-/
theorem smul_set_subset_iff_subset_inv_smul_set : a • A ⊆ B ↔ A ⊆ a⁻¹ • B := by
  refine image_subset_iff.trans ?_
  congr! 1
  exact ((MulAction.toPerm _).image_symm_eq_preimage _).symm

@[to_additive]
/-
**Set.subset_smul_set_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：subset_smul_set_iff : A subseteq a • B ↔ a⁻¹ • A subseteq B
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用引理 `Equiv.image_eq_preimage_symm`：image_eq_preimage_symm (e : α ≃ β) (s : Se
t α) : e '' s = e.symm ⁻¹' s
-/
theorem subset_smul_set_iff : A ⊆ a • B ↔ a⁻¹ • A ⊆ B := by
  refine (image_subset_iff.trans ?_).symm; congr! 1;
  exact ((MulAction.toPerm _).image_eq_preimage_symm _).symm

@[to_additive]
/-
**Set.smul_set_inter** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：smul_set_inter : a • (s inter t) = a • s inter a • t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_inter`：image_inter {f : α -> β} {s t : Set α} (H : Injective f
) : f '' (s inter t) = f '' s inter f '' t
· 使用定理 `MulAction.injective`：∀ {α : Type u_5} {β : Type u_6} [inst : Group α] [i
nst_1 : MulAction α β] (g : α), Function.Injective fun x => g • x
-/
theorem smul_set_inter : a • (s ∩ t) = a • s ∩ a • t :=
  image_inter <| MulAction.injective a

@[to_additive]
/-
**Set.smul_set_iInter** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：smul_set_iInter {ι : Sort*} (a : α) (t : ι -> Set β) : (a • ⋂ i, t i) = ⋂ 
i, a • t i
参数：a : α；t : ι -> Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_iInter`：image_iInter {f : α -> β} (hf : Bijective f) (s : ι ->
 Set α) : (f '' ⋂ i, s i) = ⋂ i, f '' s i
· 使用定理 `MulAction.bijective`：∀ {α : Type u_5} {β : Type u_6} [inst : Group α] [i
nst_1 : MulAction α β] (g : α), Function.Bijective fun x => g • x
-/
theorem smul_set_iInter {ι : Sort*}
    (a : α) (t : ι → Set β) : (a • ⋂ i, t i) = ⋂ i, a • t i :=
  image_iInter (MulAction.bijective a) t

@[to_additive]
/-
**Set.smul_set_sdiff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：smul_set_sdiff : a • (s \ t) = a • s \ a • t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_sdiff`：image_sdiff {f : α -> β} (hf : Injective f) (s t : Set 
α) : f '' (s \ t) = f '' s \ f '' t
· 使用定理 `MulAction.injective`：∀ {α : Type u_5} {β : Type u_6} [inst : Group α] [i
nst_1 : MulAction α β] (g : α), Function.Injective fun x => g • x
-/
theorem smul_set_sdiff : a • (s \ t) = a • s \ a • t :=
  image_sdiff (MulAction.injective a) _ _

open scoped symmDiff in
@[to_additive]
/-
**Set.smul_set_symmDiff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：smul_set_symmDiff : a • s ∆ t = (a • s) ∆ (a • t)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_symmDiff`：image_symmDiff (hf : Injective f) (s t : Set α) : f 
'' s ∆ t = (f '' s) ∆ (f '' t)
· 使用定理 `MulAction.injective`：∀ {α : Type u_5} {β : Type u_6} [inst : Group α] [i
nst_1 : MulAction α β] (g : α), Function.Injective fun x => g • x
-/
theorem smul_set_symmDiff : a • s ∆ t = (a • s) ∆ (a • t) :=
  image_symmDiff (MulAction.injective a) _ _

@[to_additive (attr := simp)]
/-
**Set.smul_set_univ** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：smul_set_univ : a • (univ : Set β) = univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_univ_of_surjective`：image_univ_of_surjective {ι : Type*} {f : 
ι -> β} (H : Surjective f) : f '' univ = univ
· 使用定理 `MulAction.surjective`：∀ {α : Type u_5} {β : Type u_6} [inst : Group α] [
inst_1 : MulAction α β] (g : α), Function.Surjective fun x => g • x
-/
theorem smul_set_univ : a • (univ : Set β) = univ :=
  image_univ_of_surjective <| MulAction.surjective a

@[to_additive (attr := simp)]
/-
**Set.smul_set_eq_univ** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：smul_set_eq_univ : a • s = univ ↔ s = univ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `smul_eq_iff_eq_inv_smul`：smul_eq_iff_eq_inv_smul (g : α) {x y : β} : g •
 x = y ↔ x = g⁻¹ • y
· 使用定理 `Set.smul_set_univ`：smul_set_univ : a • (univ : Set β) = univ
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem smul_set_eq_univ : a • s = univ ↔ s = univ := by
  rw [smul_eq_iff_eq_inv_smul, smul_set_univ]

@[to_additive (attr := simp)]
/-
**Set.smul_univ** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：smul_univ {s : Set α} (hs : s.Nonempty) : s • (univ : Set β) = univ
参数：hs : s.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_univ_of_forall`：eq_univ_of_forall {s : Set α} : (forall x, x in s
) -> s = univ
· 使用定理 `trivial`：True
· 使用引理 `smul_inv_smul`：smul_inv_smul (g : G) (a : α) : g • g⁻¹ • a = a
-/
theorem smul_univ {s : Set α} (hs : s.Nonempty) : s • (univ : Set β) = univ :=
  let ⟨a, ha⟩ := hs
  eq_univ_of_forall fun b ↦ ⟨a, ha, a⁻¹ • b, trivial, smul_inv_smul _ _⟩

@[to_additive]
/-
**Set.smul_set_compl** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：smul_set_compl : a • sᶜ = (a • s)ᶜ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.compl_eq_univ_sdiff`：compl_eq_univ_sdiff (s : Set α) : sᶜ = univ \ s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.smul_set_sdiff`：smul_set_sdiff : a • (s \ t) = a • s \ a • t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.smul_set_univ`：smul_set_univ : a • (univ : Set β) = univ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem smul_set_compl : a • sᶜ = (a • s)ᶜ := by
  simp_rw [Set.compl_eq_univ_sdiff, smul_set_sdiff, smul_set_univ]

@[to_additive]
/-
**Set.smul_inter_nonempty_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：smul_inter_nonempty_iff {s t : Set α} {x : α} : (x • s inter t).Nonempty ↔
 exists a b, (a in t ∧ b in s) ∧ a * b⁻¹ = x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_smul_set`：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β] {t :
 Set β} {a : α} {x : β}, x ∈ a • t ↔ ∃ y ∈ t, a • y = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_inv_cancel_right`：mul_inv_cancel_right (a b : G) : a * b * b⁻¹ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.mem_inter`：mem_inter {x : α} {a b : Set α} (ha : x in a) (hb : x in 
b) : x in a inter b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inv_mul_cancel_right`：inv_mul_cancel_right (a b : G) : a * b⁻¹ * b = a
-/
theorem smul_inter_nonempty_iff {s t : Set α} {x : α} :
    (x • s ∩ t).Nonempty ↔ ∃ a b, (a ∈ t ∧ b ∈ s) ∧ a * b⁻¹ = x := by
  constructor
  · rintro ⟨a, h, ha⟩
    obtain ⟨b, hb, rfl⟩ := mem_smul_set.mp h
    exact ⟨x • b, b, ⟨ha, hb⟩, by simp⟩
  · rintro ⟨a, b, ⟨ha, hb⟩, rfl⟩
    exact ⟨a, mem_inter (mem_smul_set.mpr ⟨b, hb, by simp⟩) ha⟩

@[to_additive]
/-
**Set.smul_inter_nonempty_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：smul_inter_nonempty_iff' {s t : Set α} {x : α} : (x • s inter t).Nonempty 
↔ exists a b, (a in t ∧ b in s) ∧ a / b = x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem smul_inter_nonempty_iff' {s t : Set α} {x : α} :
    (x • s ∩ t).Nonempty ↔ ∃ a b, (a ∈ t ∧ b ∈ s) ∧ a / b = x := by
  simp_rw [smul_inter_nonempty_iff, div_eq_mul_inv]

@[to_additive]
/-
**Set.op_smul_inter_nonempty_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：op_smul_inter_nonempty_iff {s t : Set α} {x : αᵐᵒᵖ} : (x • s inter t).None
mpty ↔ exists a b, (a in s ∧ b in t) ∧ a⁻¹ * b = MulOpposite.unop x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_smul_set`：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β] {t :
 Set β} {a : α} {x : β}, x ∈ a • t ↔ ∃ y ∈ t, a • y = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_mul_cancel_left`：inv_mul_cancel_left (a b : G) : a⁻¹ * (a * b) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Set.mem_inter`：mem_inter {x : α} {a b : Set α} (ha : x in a) (hb : x in 
b) : x in a inter b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_inv_cancel_left`：mul_inv_cancel_left (a b : G) : a * (a⁻¹ * b) = b
-/
theorem op_smul_inter_nonempty_iff {s t : Set α} {x : αᵐᵒᵖ} :
    (x • s ∩ t).Nonempty ↔ ∃ a b, (a ∈ s ∧ b ∈ t) ∧ a⁻¹ * b = MulOpposite.unop x := by
  constructor
  · rintro ⟨a, h, ha⟩
    obtain ⟨b, hb, rfl⟩ := mem_smul_set.mp h
    exact ⟨b, x • b, ⟨hb, ha⟩, by simp⟩
  · rintro ⟨a, b, ⟨ha, hb⟩, H⟩
    have : MulOpposite.op (a⁻¹ * b) = x := congr_arg MulOpposite.op H
    exact ⟨b, mem_inter (mem_smul_set.mpr ⟨a, ha, by simp [← this]⟩) hb⟩

@[to_additive (attr := simp)]
/-
**Set.iUnion_inv_smul** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iUnion_inv_smul : ⋃ g : α, g⁻¹ • s = ⋃ g : α, g • s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.iSup_congr`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : So
rt u_5} [inst : SupSet α] {f : ι → α} {g : ι' → α} (h : ι → ι'),   Function.Surj
ective h → (∀ (x : ι…
· 使用定理 `inv_surjective`：inv_surjective : Function.Surjective (Inv.inv : G -> G)
-/
theorem iUnion_inv_smul : ⋃ g : α, g⁻¹ • s = ⋃ g : α, g • s :=
  (Function.Surjective.iSup_congr _ inv_surjective) fun _ ↦ rfl

@[to_additive]
/-
**Set.iUnion_smul_eq_ofPred_exists** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：iUnion_smul_eq_ofPred_exists {s : Set β} : ⋃ g : α, g • s = { a | exists g
 : α, g • a in s }
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iUnion_smul_eq_ofPred_exists {s : Set β} : ⋃ g : α, g • s = { a | ∃ g : α, g • a ∈ s } := by
  simp_rw [← iUnion_ofPred, ← iUnion_inv_smul, ← preimage_smul, preimage]

@[deprecated (since := "2026-07-09")]
alias iUnion_smul_eq_setOf_exists := iUnion_smul_eq_ofPred_exists

@[deprecated (since := "2026-07-09")]
alias iUnion_vadd_eq_setOf_exists := iUnion_vadd_eq_ofPred_exists

@[to_additive (attr := simp)]
/-
**Set.inv_smul_set_distrib** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：inv_smul_set_distrib (a : α) (s : Set α) : (a • s)⁻¹ = op a⁻¹ • s⁻¹
参数：a : α；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma inv_smul_set_distrib (a : α) (s : Set α) : (a • s)⁻¹ = op a⁻¹ • s⁻¹ := by
  ext; simp [mem_smul_set_iff_inv_smul_mem]

@[to_additive (attr := simp)]
/-
**Set.inv_op_smul_set_distrib** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：inv_op_smul_set_distrib (a : α) (s : Set α) : (op a • s)⁻¹ = a⁻¹ • s⁻¹
参数：a : α；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma inv_op_smul_set_distrib (a : α) (s : Set α) : (op a • s)⁻¹ = a⁻¹ • s⁻¹ := by
  ext; simp [mem_smul_set_iff_inv_smul_mem]

@[to_additive (attr := simp)]
/-
**Set.disjoint_smul_set** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：disjoint_smul_set : Disjoint (a • s) (a • t) ↔ Disjoint s t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.disjoint_image_iff`：disjoint_image_iff (hf : Injective f) : Disjoint
 (f '' s) (f '' t) ↔ Disjoint s t
· 使用定理 `MulAction.injective`：∀ {α : Type u_5} {β : Type u_6} [inst : Group α] [i
nst_1 : MulAction α β] (g : α), Function.Injective fun x => g • x
-/
lemma disjoint_smul_set : Disjoint (a • s) (a • t) ↔ Disjoint s t :=
  disjoint_image_iff <| MulAction.injective _

@[to_additive]
/-
**Set.disjoint_smul_set_left** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：disjoint_smul_set_left : Disjoint (a • s) t ↔ Disjoint s (a⁻¹ • t)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `smul_inv_smul`：smul_inv_smul (g : G) (a : α) : g • g⁻¹ • a = a
· 使用引理 `Set.disjoint_smul_set`：disjoint_smul_set : Disjoint (a • s) (a • t) ↔ Di
sjoint s t
-/
lemma disjoint_smul_set_left : Disjoint (a • s) t ↔ Disjoint s (a⁻¹ • t) := by
  simpa using disjoint_smul_set (a := a) (t := a⁻¹ • t)

@[to_additive]
/-
**Set.disjoint_smul_set_right** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：disjoint_smul_set_right : Disjoint s (a • t) ↔ Disjoint (a⁻¹ • s) t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `smul_inv_smul`：smul_inv_smul (g : G) (a : α) : g • g⁻¹ • a = a
· 使用引理 `Set.disjoint_smul_set`：disjoint_smul_set : Disjoint (a • s) (a • t) ↔ Di
sjoint s t
-/
lemma disjoint_smul_set_right : Disjoint s (a • t) ↔ Disjoint (a⁻¹ • s) t := by
  simpa using disjoint_smul_set (a := a) (s := a⁻¹ • s)
/-
**Set.pairwise_disjoint_smul_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : Group α] [inst_1 : MulAction α β] 
{s : Set β},   Pairwise (Function.onFun Disjoint fun a => a • s) ↔ ∀ (a : α), (a
 • s ∩ s).Nonempty → a = 1
参数：Function.onFun Disjoint fun a => a • s；a : α；a • s ∩ s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_imp_not`：not_imp_not : ¬a -> ¬b ↔ b -> a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
@[to_additive] lemma pairwise_disjoint_smul_iff :
    Pairwise (Disjoint on fun a : α ↦ a • s) ↔ ∀ a : α, (a • s ∩ s).Nonempty → a = 1 := by
  simp_rw [Pairwise, disjoint_smul_set_right, ← mul_smul,
    ← not_imp_not (b := _ ≠ _), not_ne_iff, not_disjoint_iff_nonempty_inter]
  exact ⟨fun h a ↦ by simpa using @h a 1,
    fun h i j ne ↦ by simpa [inv_mul_eq_one, eq_comm] using h _ ne⟩

/-- Any intersection of translates of two sets `s` and `t` can be covered by a single translate of
`(s⁻¹ * s) ∩ (t⁻¹ * t)`.

This is useful to show that the intersection of approximate subgroups is an approximate subgroup. -/
@[to_additive
/-- Any intersection of translates of two sets `s` and `t` can be covered by a single translate of
`(-s + s) ∩ (-t + t)`.

This is useful to show that the intersection of approximate subgroups is an approximate subgroup.
-/]
/-
**Set.exists_smul_inter_smul_subset_smul_inv_mul_inter_inv_mul** 是 Mathlib 中的一个引
理，位于命名空间 `Set`。
形式化陈述：exists_smul_inter_smul_subset_smul_inv_mul_inter_inv_mul (s t : Set α) (a 
b : α) : exists z : α, a • s inter b • t subseteq z • ((s⁻¹ * s) inter (t⁻¹ * t)
)
参数：s t : Set α；a b : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Set.inter_subset_inter`：inter_subset_inter {s₁ s₂ t₁ t₂ : Set α} (h₁ : s
₁ subseteq t₁) (h₂ : s₂ subseteq t₂) : s₁ inter s₂ subseteq t₁ inter t₂
· 使用定理 `Set.smul_set_subset_mul`：∀ {α : Type u_2} [inst : Mul α] {s t : Set α} {
a : α}, a ∈ s → a • t ⊆ s * t
· 使用定理 `Set.smul_set_inter`：smul_set_inter : a • (s inter t) = a • s inter a • t
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `smul_mul_assoc`：smul_mul_assoc [Mul β] [SMul α β] [IsScalarTower α β β] 
(r : α) (x y : β) : r • x * y = r • (x * y)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma exists_smul_inter_smul_subset_smul_inv_mul_inter_inv_mul (s t : Set α) (a b : α) :
    ∃ z : α, a • s ∩ b • t ⊆ z • ((s⁻¹ * s) ∩ (t⁻¹ * t)) := by
  obtain hAB | ⟨z, hzA, hzB⟩ := (a • s ∩ b • t).eq_empty_or_nonempty
  · exact ⟨1, by simp [hAB]⟩
  refine ⟨z, ?_⟩
  calc
    a • s ∩ b • t ⊆ (z • s⁻¹) * s ∩ ((z • t⁻¹) * t) := by
      gcongr <;> apply smul_set_subset_mul <;> simpa
    _ = z • ((s⁻¹ * s) ∩ (t⁻¹ * t)) := by simp_rw [Set.smul_set_inter, smul_mul_assoc]

end Group

section Monoid
variable [Monoid α] [MulAction α β] {s : Set β} {a : α} {b : β}

/-
**Set.mem_invOf_smul_set** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : Monoid α] [inst_1 : MulAction α β]
 {s : Set β} {a : α} {b : β}   [inst_2 : Invertible a], b ∈ ⅟a • s ↔ a • b ∈ s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_inv_smul_set_iff`：mem_inv_smul_set_iff : x in a⁻¹ • A ↔ a • x in
 A
-/
@[simp] lemma mem_invOf_smul_set [Invertible a] : b ∈ ⅟a • s ↔ a • b ∈ s :=
  mem_inv_smul_set_iff (a := unitOfInvertible a)

end Monoid

section Group
variable [Group α] [CommGroup β] [FunLike F α β] [MonoidHomClass F α β]

@[to_additive]
/-
**Set.smul_graphOn** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：smul_graphOn (x : α × β) (s : Set α) (f : F) : x • s.graphOn f = (x.1 • s)
.graphOn fun a => x.2 / f x.1 * f a
参数：x : α × β；s : Set α；f : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `map_inv`：map_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f 
: F) (a : G) : f a⁻¹ = (f a)⁻¹
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma smul_graphOn (x : α × β) (s : Set α) (f : F) :
    x • s.graphOn f = (x.1 • s).graphOn fun a ↦ x.2 / f x.1 * f a := by
  ext ⟨a, b⟩
  simp [mem_smul_set_iff_inv_smul_mem, inv_mul_eq_iff_eq_mul, mul_left_comm _ _⁻¹,
    eq_inv_mul_iff_mul_eq, ← mul_div_right_comm, div_eq_iff_eq_mul, mul_comm b]

@[to_additive]
/-
**Set.smul_graphOn_univ** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：smul_graphOn_univ (x : α × β) (f : F) : x • univ.graphOn f = univ.graphOn 
fun a => x.2 / f x.1 * f a
参数：x : α × β；f : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.smul_graphOn`：smul_graphOn (x : α × β) (s : Set α) (f : F) : x • s.g
raphOn f = (x.1 • s).graphOn fun a => x.2 / f x.1 * f a
· 使用定理 `Set.smul_set_univ`：smul_set_univ : a • (univ : Set β) = univ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma smul_graphOn_univ (x : α × β) (f : F) :
    x • univ.graphOn f = univ.graphOn fun a ↦ x.2 / f x.1 * f a := by simp [smul_graphOn]

end Group

section CommGroup
variable [CommGroup α]

/-
**Set.smul_div_smul_comm** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：∀ {α : Type u_2} [inst : CommGroup α] (a : α) (s : Set α) (b : α) (t : Set
 α), a • s / b • t = (a / b) • (s / t)
参数：a : α；s : Set α；b : α；t : Set α；a / b；s / t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_div_mul_comm`：mul_div_mul_comm : a * b / (c * d) = a / c * (b / d)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.singleton_div_singleton`：singleton_div_singleton : ({a} : Set α) / {
b} = {a / b}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[to_additive] lemma smul_div_smul_comm (a : α) (s : Set α) (b : α) (t : Set α) :
    a • s / b • t = (a / b) • (s / t) := by
  simp_rw [← image_smul, smul_eq_mul, ← singleton_mul, mul_div_mul_comm _ s,
    singleton_div_singleton]

end CommGroup
end Set

