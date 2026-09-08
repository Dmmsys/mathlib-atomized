/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Algebra.Subalgebra.Basic

/-!
# Complete lattice structure of subalgebras

In this file we define `Algebra.adjoin` and the complete lattice structure on subalgebras.

More lemmas about `adjoin` can be found in `Mathlib/RingTheory/Adjoin/Basic.lean`.
-/

@[expose] public section

assert_not_exists Polynomial

universe u u' v w w'

namespace Algebra

variable (R : Type u) {A : Type v} {B : Type w}
variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

/-- The minimal subalgebra that includes `s`. -/
@[simps -isSimp toSubsemiring]
/-
**Algebra.adjoin** 是 Mathlib 中的一个定义，位于命名空间 `Algebra`。
形式化陈述：adjoin (s : Set A) : Subalgebra R A
参数：s : Set A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The minimal subalgebra that includes `s`.
-/
def adjoin (s : Set A) : Subalgebra R A :=
  { Subsemiring.closure (Set.range (algebraMap R A) ∪ s) with
    algebraMap_mem' := fun r => Subsemiring.subset_closure <| Or.inl ⟨r, rfl⟩ }

variable {R}
/-
**Algebra.gc** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] [inst_1 : Semiring A] 
[inst_2 : Algebra R A],   GaloisConnection (Algebra.adjoin R) SetLike.coe
参数：Algebra.adjoin R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t
· 使用定理 `Subsemiring.subset_closure`：subset_closure {s : Set R} : s subseteq clos
ure s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subsemiring.closure_le`：closure_le {s : Set R} {t : Subsemiring R} : clo
sure s <= t ↔ s subseteq t
· 使用定理 `Set.union_subset`：union_subset {s t r : Set α} (sr : s subseteq r) (tr :
 t subseteq r) : s union t subseteq r
· 使用定理 `Subalgebra.range_subset`：range_subset : Set.range (algebraMap R A) subse
teq S
-/
protected theorem gc : GaloisConnection (adjoin R : Set A → Subalgebra R A) (↑) := fun s S =>
  ⟨fun H => le_trans (le_trans Set.subset_union_right Subsemiring.subset_closure) H,
   fun H => show Subsemiring.closure (Set.range (algebraMap R A) ∪ s) ≤ S.toSubsemiring from
      Subsemiring.closure_le.2 <| Set.union_subset S.range_subset H⟩

/-- Galois insertion between `adjoin` and `coe`. -/
/-
**Algebra.gi** 是 Mathlib 中的一个定义，位于命名空间 `Algebra`。
形式化陈述：{R : Type u} →   {A : Type v} →     [inst : CommSemiring R] →       [inst_
1 : Semiring A] → [inst_2 : Algebra R A] → GaloisInsertion (Algebra.adjoin R) Se
tLike.coe
参数：Algebra.adjoin R。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.gc`：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] [inst_1 
: Semiring A] [inst_2 : Algebra R A],   GaloisConnection (Algebra.adjoin R) SetL
…

--- 原说明 ---
Galois insertion between `adjoin` and `coe`.
-/
protected def gi : GaloisInsertion (adjoin R : Set A → Subalgebra R A) (↑) where
  choice s hs := (adjoin R s).copy s <| le_antisymm (Algebra.gc.le_u_l s) hs
  gc := Algebra.gc
  le_l_u S := (Algebra.gc (S : Set A) (adjoin R S)).1 <| le_rfl
  choice_eq _ _ := Subalgebra.copy_eq _ _ _
/-
**Algebra.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CompleteLattice (Subalgebra R A) where
  __ := GaloisInsertion.liftCompleteLattice Algebra.gi
  bot := (Algebra.ofId R A).range
  bot_le _S := fun _a ⟨_r, hr⟩ => hr ▸ algebraMap_mem _ _
/-
**Algebra.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {C : Type*} [CommSemiring C] [Algebra R C] (S₁ S₂ : Subalgebra R C) :
  Algebra ↑(min S₁ S₂) S₁ := RingHom.toAlgebra (Subalgebra.inclusion inf_le_left).toRingHom
/-
**Algebra.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {C : Type*} [CommSemiring C] [Algebra R C] (S₁ S₂ : Subalgebra R C) :
  Algebra ↑(S₁ ⊓ S₂) S₂ := RingHom.toAlgebra (Subalgebra.inclusion inf_le_right).toRingHom
/-
**Algebra.sup_def** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：sup_def (S T : Subalgebra R A) : S ⊔ T = adjoin R (S union T : Set A)
参数：S T : Subalgebra R A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sup_def (S T : Subalgebra R A) : S ⊔ T = adjoin R (S ∪ T : Set A) := rfl
/-
**Algebra.sSup_def** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：sSup_def (S : Set (Subalgebra R A)) : sSup S = adjoin R (⋃₀ (SetLike.coe '
' S))
参数：S : Set (Subalgebra R A)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sSup_def (S : Set (Subalgebra R A)) : sSup S = adjoin R (⋃₀ (SetLike.coe '' S)) := rfl

@[simp, norm_cast]
/-
**Algebra.coe_top** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：coe_top : (↑(⊤ : Subalgebra R A) : Set A) = Set.univ
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_top : (↑(⊤ : Subalgebra R A) : Set A) = Set.univ := rfl

@[simp]
/-
**Algebra.mem_top** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：mem_top {x : A} : x in (⊤ : Subalgebra R A)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
-/
theorem mem_top {x : A} : x ∈ (⊤ : Subalgebra R A) := Set.mem_univ x

@[simp]
/-
**Algebra.top_toSubmodule** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：top_toSubmodule : Subalgebra.toSubmodule (⊤ : Subalgebra R A) = ⊤
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem top_toSubmodule : Subalgebra.toSubmodule (⊤ : Subalgebra R A) = ⊤ := rfl

@[simp]
/-
**Algebra.top_toSubsemiring** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：top_toSubsemiring : (⊤ : Subalgebra R A).toSubsemiring = ⊤
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem top_toSubsemiring : (⊤ : Subalgebra R A).toSubsemiring = ⊤ := rfl

@[simp]
/-
**Algebra.top_toSubring** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：top_toSubring {R A : Type*} [CommRing R] [Ring A] [Algebra R A] : (⊤ : Sub
algebra R A).toSubring = ⊤
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem top_toSubring {R A : Type*} [CommRing R] [Ring A] [Algebra R A] :
    (⊤ : Subalgebra R A).toSubring = ⊤ := rfl

@[simp]
/-
**Algebra.toSubmodule_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：toSubmodule_eq_top {S : Subalgebra R A} : Subalgebra.toSubmodule S = ⊤ ↔ S
 = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Injective f → ∀ {a b : α} {c : β}, f b = c → (f a = c ↔ a = b)
· 使用定理 `RelEmbedding.injective`：injective (f : r ↪r s) : Injective f
· 使用定理 `Algebra.top_toSubmodule`：top_toSubmodule : Subalgebra.toSubmodule (⊤ : S
ubalgebra R A) = ⊤
-/
theorem toSubmodule_eq_top {S : Subalgebra R A} : Subalgebra.toSubmodule S = ⊤ ↔ S = ⊤ :=
  Subalgebra.toSubmodule.injective.eq_iff' top_toSubmodule

@[simp]
/-
**Algebra.toSubsemiring_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：toSubsemiring_eq_top {S : Subalgebra R A} : S.toSubsemiring = ⊤ ↔ S = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Injective f → ∀ {a b : α} {c : β}, f b = c → (f a = c ↔ a = b)
· 使用定理 `Subalgebra.toSubsemiring_injective`：toSubsemiring_injective : Function.I
njective (toSubsemiring : Subalgebra R A -> Subsemiring A)
· 使用定理 `Algebra.top_toSubsemiring`：top_toSubsemiring : (⊤ : Subalgebra R A).toSu
bsemiring = ⊤
-/
theorem toSubsemiring_eq_top {S : Subalgebra R A} : S.toSubsemiring = ⊤ ↔ S = ⊤ :=
  Subalgebra.toSubsemiring_injective.eq_iff' top_toSubsemiring

@[simp]
/-
**Algebra.toSubring_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：toSubring_eq_top {R A : Type*} [CommRing R] [Ring A] [Algebra R A] {S : Su
balgebra R A} : S.toSubring = ⊤ ↔ S = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Injective f → ∀ {a b : α} {c : β}, f b = c → (f a = c ↔ a = b)
· 使用定理 `Subalgebra.toSubring_injective`：toSubring_injective {R : Type u} {A : Ty
pe v} [CommRing R] [Ring A] [Algebra R A] : Function.Injective (toSubring : Suba
lgebra R A -> Subrin…
· 使用定理 `Algebra.top_toSubring`：top_toSubring {R A : Type*} [CommRing R] [Ring A]
 [Algebra R A] : (⊤ : Subalgebra R A).toSubring = ⊤
-/
theorem toSubring_eq_top {R A : Type*} [CommRing R] [Ring A] [Algebra R A] {S : Subalgebra R A} :
    S.toSubring = ⊤ ↔ S = ⊤ :=
  Subalgebra.toSubring_injective.eq_iff' top_toSubring
/-
**Algebra.mem_sup_left** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：mem_sup_left {S T : Subalgebra R A} : forall {x : A}, x in S -> x in S ⊔ T
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
-/
theorem mem_sup_left {S T : Subalgebra R A} : ∀ {x : A}, x ∈ S → x ∈ S ⊔ T :=
  have : S ≤ S ⊔ T := le_sup_left; (this ·)
/-
**Algebra.mem_sup_right** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：mem_sup_right {S T : Subalgebra R A} : forall {x : A}, x in T -> x in S ⊔ 
T
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
-/
theorem mem_sup_right {S T : Subalgebra R A} : ∀ {x : A}, x ∈ T → x ∈ S ⊔ T :=
  have : T ≤ S ⊔ T := le_sup_right; (this ·)
/-
**Algebra.mul_mem_sup** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：mul_mem_sup {S T : Subalgebra R A} {x y : A} (hx : x in S) (hy : y in T) :
 x * y in S ⊔ T
参数：hx : x in S；hy : y in T。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.mul_mem`：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] 
[inst_1 : Semiring A] [inst_2 : Algebra R A] (S : Subalgebra R A)   {x y : A}, x
 ∈ S → y…
· 使用定理 `Algebra.mem_sup_left`：mem_sup_left {S T : Subalgebra R A} : forall {x : 
A}, x in S -> x in S ⊔ T
· 使用定理 `Algebra.mem_sup_right`：mem_sup_right {S T : Subalgebra R A} : forall {x 
: A}, x in T -> x in S ⊔ T
-/
theorem mul_mem_sup {S T : Subalgebra R A} {x y : A} (hx : x ∈ S) (hy : y ∈ T) : x * y ∈ S ⊔ T :=
  (S ⊔ T).mul_mem (mem_sup_left hx) (mem_sup_right hy)
/-
**Algebra.map_sup** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：map_sup (f : A ->ₐ[R] B) (S T : Subalgebra R A) : (S ⊔ T).map f = S.map f 
⊔ T.map f
参数：f : A ->ₐ[R] B；S T : Subalgebra R A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_sup`：l_sup (gc : GaloisConnection l u) : l (a₁ ⊔ a₂) 
= l a₁ ⊔ l a₂
· 使用定理 `Subalgebra.gc_map_comap`：gc_map_comap (f : A ->ₐ[R] B) : GaloisConnectio
n (map f) (comap f)
-/
theorem map_sup (f : A →ₐ[R] B) (S T : Subalgebra R A) : (S ⊔ T).map f = S.map f ⊔ T.map f :=
  (Subalgebra.gc_map_comap f).l_sup
/-
**Algebra.map_inf** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：map_inf (f : A ->ₐ[R] B) (hf : Function.Injective f) (S T : Subalgebra R A
) : (S ⊓ T).map f = S.map f ⊓ T.map f
参数：f : A ->ₐ[R] B；hf : Function.Injective f；S T : Subalgebra R A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.image_inter`：image_inter {f : α -> β} {s t : Set α} (H : Injective f
) : f '' (s inter t) = f '' s inter f '' t
-/
theorem map_inf (f : A →ₐ[R] B) (hf : Function.Injective f) (S T : Subalgebra R A) :
    (S ⊓ T).map f = S.map f ⊓ T.map f := SetLike.coe_injective (Set.image_inter hf)

@[simp, norm_cast]
/-
**Algebra.coe_inf** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：coe_inf (S T : Subalgebra R A) : (↑(S ⊓ T) : Set A) = (S inter T : Set A)
参数：S T : Subalgebra R A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_inf (S T : Subalgebra R A) : (↑(S ⊓ T) : Set A) = (S ∩ T : Set A) := rfl

@[simp]
/-
**Algebra.mem_inf** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：mem_inf {S T : Subalgebra R A} {x : A} : x in S ⊓ T ↔ x in S ∧ x in T
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_inf {S T : Subalgebra R A} {x : A} : x ∈ S ⊓ T ↔ x ∈ S ∧ x ∈ T := Iff.rfl

open Subalgebra in
@[simp]
/-
**Algebra.inf_toSubmodule** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：inf_toSubmodule (S T : Subalgebra R A) : toSubmodule (S ⊓ T) = toSubmodule
 S ⊓ toSubmodule T
参数：S T : Subalgebra R A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inf_toSubmodule (S T : Subalgebra R A) :
    toSubmodule (S ⊓ T) = toSubmodule S ⊓ toSubmodule T := rfl

@[simp]
/-
**Algebra.inf_toSubsemiring** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：inf_toSubsemiring (S T : Subalgebra R A) : (S ⊓ T).toSubsemiring = S.toSub
semiring ⊓ T.toSubsemiring
参数：S T : Subalgebra R A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inf_toSubsemiring (S T : Subalgebra R A) :
    (S ⊓ T).toSubsemiring = S.toSubsemiring ⊓ T.toSubsemiring :=
  rfl

@[simp]
/-
**Algebra.sup_toSubsemiring** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：sup_toSubsemiring (S T : Subalgebra R A) : (S ⊔ T).toSubsemiring = S.toSub
semiring ⊔ T.toSubsemiring
参数：S T : Subalgebra R A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subsemiring.closure_eq`：closure_eq (s : Subsemiring R) : closure (s : Se
t R) = s
· 使用定理 `Subsemiring.closure_union`：closure_union (s t : Set R) : closure (s unio
n t) = closure s ⊔ closure t
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Algebra.adjoin_toSubsemiring`：∀ (R : Type u) {A : Type v} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A] (s : Set A),   (Algebra.a
djoin R s).toSubse…
· 使用定理 `Set.union_eq_right`：union_eq_right {s t : Set α} : s union t = t ↔ s sub
seteq t
· 使用定理 `Set.mem_union_left`：mem_union_left {x : α} {a : Set α} (b : Set α) : x i
n a -> x in a union b
· 使用定理 `algebraMap_mem`：∀ {S : Type u_1} {R : Type u_2} {A : Type u_3} [inst : C
ommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_3 : SetLike 
S A]…
· 使用定理 `AddSubmonoidWithOneClass.toOneMemClass`：∀ {S : Type u_1} {R : outParam (
Type u_2)} {inst : AddMonoidWithOne R} {inst_1 : SetLike S R}   [self : AddSubmo
noidWithOneClass S R], OneMe…
· 使用定理 `SubsemiringClass.addSubmonoidWithOneClass`：∀ (S : Type u_1) (R : Type u)
 {x : NonAssocSemiring R} [inst : SetLike S R] [h : SubsemiringClass S R],   Add
SubmonoidWithOneClass S R
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A
-/
theorem sup_toSubsemiring (S T : Subalgebra R A) :
    (S ⊔ T).toSubsemiring = S.toSubsemiring ⊔ T.toSubsemiring := by
  rw [← S.toSubsemiring.closure_eq, ← T.toSubsemiring.closure_eq, ← Subsemiring.closure_union]
  simp_rw [sup_def, adjoin_toSubsemiring, Subalgebra.coe_toSubsemiring]
  congr 1
  rw [Set.union_eq_right]
  rintro _ ⟨x, rfl⟩
  exact Set.mem_union_left _ (algebraMap_mem S x)

@[simp, norm_cast]
/-
**Algebra.coe_sInf** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：coe_sInf (S : Set (Subalgebra R A)) : (↑(sInf S) : Set A) = ⋂ s in S, ↑s
参数：S : Set (Subalgebra R A)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sInf_image`：∀ {α : Type u_1} {β : Type u_2} [inst : CompleteLattice α] {
s : Set β} {f : β → α}, sInf (f '' s) = ⨅ a ∈ s, f a
-/
theorem coe_sInf (S : Set (Subalgebra R A)) : (↑(sInf S) : Set A) = ⋂ s ∈ S, ↑s :=
  sInf_image

@[simp]
/-
**Algebra.mem_sInf** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：mem_sInf {S : Set (Subalgebra R A)} {x : A} : x in sInf S ↔ forall p in S,
 x in p
参数：Subalgebra R A。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Algebra.coe_sInf`：coe_sInf (S : Set (Subalgebra R A)) : (↑(sInf S) : Set
 A) = ⋂ s in S, ↑s
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_sInf {S : Set (Subalgebra R A)} {x : A} : x ∈ sInf S ↔ ∀ p ∈ S, x ∈ p := by
  simp only [← SetLike.mem_coe, coe_sInf, Set.mem_iInter₂]

@[simp]
/-
**Algebra.sInf_toSubmodule** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：sInf_toSubmodule (S : Set (Subalgebra R A)) : Subalgebra.toSubmodule (sInf
 S) = sInf (Subalgebra.toSubmodule '' S)
参数：S : Set (Subalgebra R A)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.coe_sInf`：coe_sInf (S : Set (Subalgebra R A)) : (↑(sInf S) : Set
 A) = ⋂ s in S, ↑s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iInter_exists`：iInter_exists {p : ι -> Prop} {f : Exists p -> Set α}
 : ⋂ x, f x = ⋂ (i) (h : p i), f ⟨i, h⟩
· 使用定理 `Set.biInter_and'`：biInter_and' (p : ι' -> Prop) (q : ι -> ι' -> Prop) (s
 : forall x y, p y ∧ q x y -> Set α) : ⋂ (x : ι) (y : ι') (h : p y ∧ q x y), s x
 y h =…
· 使用定理 `Set.iInter_iInter_eq_right`：iInter_iInter_eq_right {b : β} {s : forall x
 : β, b = x -> Set α} : ⋂ (x) (h : b = x), s x h = s b rfl
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sInf_toSubmodule (S : Set (Subalgebra R A)) :
    Subalgebra.toSubmodule (sInf S) = sInf (Subalgebra.toSubmodule '' S) :=
  SetLike.coe_injective <| by simp

@[simp]
/-
**Algebra.sInf_toSubsemiring** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：sInf_toSubsemiring (S : Set (Subalgebra R A)) : (sInf S).toSubsemiring = s
Inf (Subalgebra.toSubsemiring '' S)
参数：S : Set (Subalgebra R A)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.coe_sInf`：coe_sInf (S : Set (Subalgebra R A)) : (↑(sInf S) : Set
 A) = ⋂ s in S, ↑s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iInter_exists`：iInter_exists {p : ι -> Prop} {f : Exists p -> Set α}
 : ⋂ x, f x = ⋂ (i) (h : p i), f ⟨i, h⟩
· 使用定理 `Set.biInter_and'`：biInter_and' (p : ι' -> Prop) (q : ι -> ι' -> Prop) (s
 : forall x y, p y ∧ q x y -> Set α) : ⋂ (x : ι) (y : ι') (h : p y ∧ q x y), s x
 y h =…
· 使用定理 `Set.iInter_iInter_eq_right`：iInter_iInter_eq_right {b : β} {s : forall x
 : β, b = x -> Set α} : ⋂ (x) (h : b = x), s x h = s b rfl
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sInf_toSubsemiring (S : Set (Subalgebra R A)) :
    (sInf S).toSubsemiring = sInf (Subalgebra.toSubsemiring '' S) :=
  SetLike.coe_injective <| by simp

open Subalgebra in
@[simp]
/-
**Algebra.sSup_toSubsemiring** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：sSup_toSubsemiring (S : Set (Subalgebra R A)) (hS : S.Nonempty) : (sSup S)
.toSubsemiring = sSup (toSubsemiring '' S)
参数：S : Set (Subalgebra R A)；hS : S.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_image`：image_image (g : β -> γ) (f : α -> β) (s : Set α) : g '
' f '' s = (fun x => g (f x)) '' s
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subsemiring.closure_eq`：closure_eq (s : Subsemiring R) : closure (s : Se
t R) = s
· 使用定理 `sSup_image`：sSup_image {s : Set β} {f : β -> α} : sSup (f '' s) = ⨆ a in
 s, f a
· 使用定理 `Subsemiring.closure_sUnion`：closure_sUnion (s : Set (Set R)) : closure (
⋃₀ s) = ⨆ t in s, closure t
· 使用定理 `Algebra.sSup_def`：sSup_def (S : Set (Subalgebra R A)) : sSup S = adjoin 
R (⋃₀ (SetLike.coe '' S))
· 使用定理 `Algebra.adjoin_toSubsemiring`：∀ (R : Type u) {A : Type v} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A] (s : Set A),   (Algebra.a
djoin R s).toSubse…
· 使用定理 `Set.union_eq_right`：union_eq_right {s t : Set α} : s union t = t ↔ s sub
seteq t
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `algebraMap_mem`：∀ {S : Type u_1} {R : Type u_2} {A : Type u_3} [inst : C
ommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_3 : SetLike 
S A]…
· 使用定理 `AddSubmonoidWithOneClass.toOneMemClass`：∀ {S : Type u_1} {R : outParam (
Type u_2)} {inst : AddMonoidWithOne R} {inst_1 : SetLike S R}   [self : AddSubmo
noidWithOneClass S R], OneMe…
· 使用定理 `SubsemiringClass.addSubmonoidWithOneClass`：∀ (S : Type u_1) (R : Type u)
 {x : NonAssocSemiring R} [inst : SetLike S R] [h : SubsemiringClass S R],   Add
SubmonoidWithOneClass S R
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A
-/
theorem sSup_toSubsemiring (S : Set (Subalgebra R A)) (hS : S.Nonempty) :
    (sSup S).toSubsemiring = sSup (toSubsemiring '' S) := by
  have h : toSubsemiring '' S = Subsemiring.closure '' SetLike.coe '' S := by
    rw [Set.image_image]
    congr! with x
    exact x.toSubsemiring.closure_eq.symm
  rw [h, sSup_image, ← Subsemiring.closure_sUnion, sSup_def, adjoin_toSubsemiring]
  congr 1
  rw [Set.union_eq_right]
  rintro _ ⟨x, rfl⟩
  obtain ⟨y, hy⟩ := hS
  simp only [Set.mem_sUnion, Set.mem_image, exists_exists_and_eq_and, SetLike.mem_coe]
  exact ⟨y, hy, algebraMap_mem y x⟩

@[simp, norm_cast]
/-
**Algebra.coe_iInf** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：coe_iInf {ι : Sort*} {S : ι -> Subalgebra R A} : (↑(⨅ i, S i) : Set A) = ⋂
 i, S i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.coe_sInf`：coe_sInf (S : Set (Subalgebra R A)) : (↑(sInf S) : Set
 A) = ⋂ s in S, ↑s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iInter_exists`：iInter_exists {p : ι -> Prop} {f : Exists p -> Set α}
 : ⋂ x, f x = ⋂ (i) (h : p i), f ⟨i, h⟩
· 使用定理 `Set.iInter_iInter_eq'`：iInter_iInter_eq' {f : ι -> α} {g : α -> Set β} :
 ⋂ (x) (y) (_ : f y = x), g x = ⋂ y, g (f y)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coe_iInf {ι : Sort*} {S : ι → Subalgebra R A} : (↑(⨅ i, S i) : Set A) = ⋂ i, S i := by
  simp [iInf]

@[simp]
/-
**Algebra.mem_iInf** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：mem_iInf {ι : Sort*} {S : ι -> Subalgebra R A} {x : A} : x in ⨅ i, S i ↔ f
orall i, x in S i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_iInf {ι : Sort*} {S : ι → Subalgebra R A} {x : A} : x ∈ ⨅ i, S i ↔ ∀ i, x ∈ S i := by
  simp only [iInf, mem_sInf, Set.forall_mem_range]
/-
**Algebra.map_iInf** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：map_iInf {ι : Sort*} [Nonempty ι] (f : A ->ₐ[R] B) (hf : Function.Injectiv
e f) (s : ι -> Subalgebra R A) : (iInf s).map f = ⨅ (i : ι), (s i).map f
参数：f : A ->ₐ[R] B；hf : Function.Injective f；s : ι -> Subalgebra R A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Subalgebra.coe_map`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_3 : Semiring B
] [inst_…
· 使用定理 `Algebra.coe_iInf`：coe_iInf {ι : Sort*} {S : ι -> Subalgebra R A} : (↑(⨅ 
i, S i) : Set A) = ⋂ i, S i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.InjOn.image_iInter_eq`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_5
} [Nonempty ι] {s : ι → Set α} {f : α → β},   Set.InjOn f (⋃ i, s i) → f '' ⋂ i,
 s i = ⋂ i, f '…
· 使用定理 `Set.injOn_of_injective`：injOn_of_injective (h : Injective f) {s : Set α}
 : InjOn f s
-/
theorem map_iInf {ι : Sort*} [Nonempty ι] (f : A →ₐ[R] B) (hf : Function.Injective f)
    (s : ι → Subalgebra R A) : (iInf s).map f = ⨅ (i : ι), (s i).map f := by
  apply SetLike.coe_injective
  simpa using (Set.injOn_of_injective hf).image_iInter_eq (s := SetLike.coe ∘ s)

open Subalgebra in
@[simp]
/-
**Algebra.iInf_toSubmodule** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：iInf_toSubmodule {ι : Sort*} (S : ι -> Subalgebra R A) : toSubmodule (⨅ i,
 S i) = ⨅ i, toSubmodule (S i)
参数：S : ι -> Subalgebra R A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.coe_iInf`：coe_iInf {ι : Sort*} {S : ι -> Subalgebra R A} : (↑(⨅ 
i, S i) : Set A) = ⋂ i, S i
· 使用定理 `Submodule.coe_iInf`：coe_iInf {ι} (p : ι -> Submodule R M) : (↑(⨅ i, p i)
 : Set M) = ⋂ i, ↑(p i)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iInf_toSubmodule {ι : Sort*} (S : ι → Subalgebra R A) :
    toSubmodule (⨅ i, S i) = ⨅ i, toSubmodule (S i) :=
  SetLike.coe_injective <| by simp

@[simp]
/-
**Algebra.iInf_toSubsemiring** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：iInf_toSubsemiring {ι : Sort*} (S : ι -> Subalgebra R A) : (iInf S).toSubs
emiring = ⨅ i, (S i).toSubsemiring
参数：S : ι -> Subalgebra R A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.sInf_toSubsemiring`：sInf_toSubsemiring (S : Set (Subalgebra R A)
) : (sInf S).toSubsemiring = sInf (Subalgebra.toSubsemiring '' S)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iInf_toSubsemiring {ι : Sort*} (S : ι → Subalgebra R A) :
    (iInf S).toSubsemiring = ⨅ i, (S i).toSubsemiring := by
  simp only [iInf, sInf_toSubsemiring, ← Set.range_comp, Function.comp_def]

@[simp]
/-
**Algebra.iSup_toSubsemiring** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：iSup_toSubsemiring {ι : Sort*} [Nonempty ι] (S : ι -> Subalgebra R A) : (i
Sup S).toSubsemiring = ⨆ i, (S i).toSubsemiring
参数：S : ι -> Subalgebra R A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.sSup_toSubsemiring`：sSup_toSubsemiring (S : Set (Subalgebra R A)
) (hS : S.Nonempty) : (sSup S).toSubsemiring = sSup (toSubsemiring '' S)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iSup_toSubsemiring {ι : Sort*} [Nonempty ι] (S : ι → Subalgebra R A) :
    (iSup S).toSubsemiring = ⨆ i, (S i).toSubsemiring := by
  simp only [iSup, Set.range_nonempty, sSup_toSubsemiring, ← Set.range_comp, Function.comp_def]
/-
**Algebra.mem_iSup_of_mem** 是 Mathlib 中的一个引理，位于命名空间 `Algebra`。
形式化陈述：mem_iSup_of_mem {ι : Sort*} {S : ι -> Subalgebra R A} (i : ι) {x : A} (hx 
: x in S i) : x in iSup S
参数：i : ι；hx : x in S i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
-/
lemma mem_iSup_of_mem {ι : Sort*} {S : ι → Subalgebra R A} (i : ι) {x : A} (hx : x ∈ S i) :
    x ∈ iSup S :=
  le_iSup S i hx

@[elab_as_elim]
/-
**Algebra.iSup_induction** 是 Mathlib 中的一个引理，位于命名空间 `Algebra`。
形式化陈述：iSup_induction {ι : Sort*} (S : ι -> Subalgebra R A) {motive : A -> Prop} 
{x : A} (mem : x in ⨆ i, S i) (basic : forall i, forall a in S i, motive a) (add
 : forall a b, motive a -> motive b -> motive (a + b)) (mul : forall a b, motive
 a -> motive b -> motive (a * b)) (algebraMap : forall r, motive (algebraMap R A
 r)) : motive x
参数：S : ι -> Subalgebra R A；mem : x in ⨆ i, S i；basic : forall i, forall a in S i
, motive a；add : forall a b, motive a -> motive b -> motive (a + b)；mul : forall
 a b, motive a -> motive b -> motive (a * b)；algebraMap : forall r, motive (alge
braMap R A r)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.map_one`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} (f : α →+* β), f 1 = 1
· 使用定理 `RingHom.map_zero`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring 
α} {x_1 : NonAssocSemiring β} (f : α →+* β), f 0 = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup_le_iff`：iSup_le_iff : iSup f <= a ↔ forall i, f i <= a
-/
lemma iSup_induction {ι : Sort*} (S : ι → Subalgebra R A) {motive : A → Prop}
    {x : A} (mem : x ∈ ⨆ i, S i)
    (basic : ∀ i, ∀ a ∈ S i, motive a)
    (add : ∀ a b, motive a → motive b → motive (a + b))
    (mul : ∀ a b, motive a → motive b → motive (a * b))
    (algebraMap : ∀ r, motive (algebraMap R A r)) : motive x := by
  let T : Subalgebra R A :=
  { carrier := {x | motive x}
    mul_mem' {a b} := mul a b
    add_mem' {a b} := add a b
    algebraMap_mem' := algebraMap }
  suffices iSup S ≤ T from this mem
  rwa [iSup_le_iff]

/-- A dependent version of `Subalgebra.iSup_induction`. -/
@[elab_as_elim]
/-
**Algebra.iSup_induction'** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：iSup_induction' {ι : Sort*} (S : ι -> Subalgebra R A) {motive : forall x, 
(x in ⨆ i, S i) -> Prop} {x : A} (mem : x in ⨆ i, S i) (basic : forall (i) (x) (
hx : x in S i), motive x (mem_iSup_of_mem i hx)) (add : forall x y hx hy, motive
 x hx -> motive y hy -> motive (x + y) (add_mem ‹_› ‹_›)) (mul : forall x y hx h
y, motive x hx -> motive y hy -> motive (x * y) (mul_mem ‹_› ‹_›)) (algebraMap :
 forall r, motive (algebraMap R A r) (Subalgebra.algebraMap_mem (⨆ i, S i) ‹_›))
 : motive x mem
参数：S : ι -> Subalgebra R A；x in ⨆ i, S i；mem : x in ⨆ i, S i；basic : forall (i) 
(x) (hx : x in S i), motive x (mem_iSup_of_mem i hx)；add : forall x y hx hy, mot
ive x hx -> motive y hy -> motive (x + y) (add_mem ‹_› ‹_›)；mul : forall x y hx 
hy, motive x hx -> motive y hy -> motive (x * y) (mul_mem ‹_› ‹_›)；algebraMap : 
forall r, motive (algebraMap R A r) (Subalgebra.algebraMap_mem (⨆ i, S i) ‹_›)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Algebra.mem_iSup_of_mem`：mem_iSup_of_mem {ι : Sort*} {S : ι -> Subalgebr
a R A} (i : ι) {x : A} (hx : x in S i) : x in iSup S
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
· 使用定理 `SubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Ty
pe u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringC
lass S R], AddSubmonoidCla…
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `SubsemiringClass.toSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Type 
u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringClas
s S R], SubmonoidClass …
· 使用定理 `Subalgebra.algebraMap_mem`：∀ {R : Type u} {A : Type v} [inst : CommSemir
ing R] [inst_1 : Semiring A] [inst_2 : Algebra R A] (S : Subalgebra R A)   (r : 
R), (algebraMap…
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用引理 `Algebra.iSup_induction`：iSup_induction {ι : Sort*} (S : ι -> Subalgebra 
R A) {motive : A -> Prop} {x : A} (mem : x in ⨆ i, S i) (basic : forall i, foral
l a in S i, …

--- 原说明 ---
A dependent version of `Subalgebra.iSup_induction`.
-/
theorem iSup_induction' {ι : Sort*} (S : ι → Subalgebra R A) {motive : ∀ x, (x ∈ ⨆ i, S i) → Prop}
    {x : A} (mem : x ∈ ⨆ i, S i)
    (basic : ∀ (i) (x) (hx : x ∈ S i), motive x (mem_iSup_of_mem i hx))
    (add : ∀ x y hx hy, motive x hx → motive y hy → motive (x + y) (add_mem ‹_› ‹_›))
    (mul : ∀ x y hx hy, motive x hx → motive y hy → motive (x * y) (mul_mem ‹_› ‹_›))
    (algebraMap : ∀ r, motive (algebraMap R A r) (Subalgebra.algebraMap_mem (⨆ i, S i) ‹_›)) :
    motive x mem := by
  refine Exists.elim ?_ fun (hx : x ∈ ⨆ i, S i) (hc : motive x hx) ↦ hc
  exact iSup_induction S (motive := fun x' ↦ ∃ h, motive x' h) mem
    (fun _ _ h ↦ ⟨_, basic _ _ h⟩) (fun _ _ h h' ↦ ⟨_, add _ _ _ _ h.2 h'.2⟩)
    (fun _ _ h h' ↦ ⟨_, mul _ _ _ _ h.2 h'.2⟩) fun _ ↦ ⟨_, algebraMap _⟩
/-
**Algebra.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (Subalgebra R A) := ⟨⊥⟩
/-
**Algebra.mem_bot** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：mem_bot {x : A} : x in (⊥ : Subalgebra R A) ↔ x in Set.range (algebraMap R
 A)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_bot {x : A} : x ∈ (⊥ : Subalgebra R A) ↔ x ∈ Set.range (algebraMap R A) := Iff.rfl

/-- TODO: change proof to `rfl` when fixing https://github.com/leanprover-community/mathlib4/issues/18110. -/
/-
**Algebra.toSubmodule_bot** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：toSubmodule_bot : Subalgebra.toSubmodule (⊥ : Subalgebra R A) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.one_eq_range`：one_eq_range : (1 : Submodule R A) = LinearMap.r
ange (Algebra.linearMap R A)

--- 原说明 ---
TODO: change proof to `rfl` when fixing https://github.com/leanprover-community/
mathlib4/issues/18110.
-/
theorem toSubmodule_bot : Subalgebra.toSubmodule (⊥ : Subalgebra R A) = 1 :=
  Submodule.one_eq_range.symm

@[simp, norm_cast]
/-
**Algebra.coe_bot** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：coe_bot : ((⊥ : Subalgebra R A) : Set A) = Set.range (algebraMap R A)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_bot : ((⊥ : Subalgebra R A) : Set A) = Set.range (algebraMap R A) := rfl

@[simp]
/-
**Algebra.toSubring_bot** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：toSubring_bot (A : Type*) [CommRing A] (R : Subring A) : (⊥ : Subalgebra R
 A).toSubring = R
参数：A : Type*；R : Subring A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subring.ext`：ext {S T : Subring R} (h : forall x, x in S ↔ x in T) : S =
 T
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Subalgebra.neg_mem`：∀ {R : Type u} {A : Type v} [inst : CommRing R] [ins
t_1 : Ring A] [inst_2 : Algebra R A] (S : Subalgebra R A) {x : A},   x ∈ S → -x 
∈ S
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Subalgebra.mem_carrier`：mem_carrier {s : Subalgebra R A} {x : A} : x in 
s.carrier ↔ x in s
-/
theorem toSubring_bot (A : Type*) [CommRing A] (R : Subring A) :
    (⊥ : Subalgebra R A).toSubring = R := by
  aesop (add norm Subalgebra.mem_carrier.symm)
/-
**Algebra.eq_top_iff** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：eq_top_iff {S : Subalgebra R A} : S = ⊤ ↔ forall x : A, x in S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.mem_top`：mem_top {x : A} : x in (⊤ : Subalgebra R A)
· 使用定理 `Subalgebra.ext`：ext {S T : Subalgebra R A} (h : forall x : A, x in S ↔ x
 in T) : S = T
-/
theorem eq_top_iff {S : Subalgebra R A} : S = ⊤ ↔ ∀ x : A, x ∈ S :=
  ⟨fun h x => by rw [h]; exact mem_top, fun h => by
    ext x; exact ⟨fun _ => mem_top, fun _ => h x⟩⟩
/-
**Algebra._root_.AlgHom.range_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.AlgHom.range_eq_top (f : A →ₐ[R] B) :
    f.range = (⊤ : Subalgebra R B) ↔ Function.Surjective f :=
  Algebra.eq_top_iff

@[simp]
/-
**Algebra.range_ofId** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：range_ofId : (Algebra.ofId R A).range = ⊥
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem range_ofId : (Algebra.ofId R A).range = ⊥ := rfl

@[simp]
/-
**Algebra.range_id** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：range_id : (AlgHom.id R A).range = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.range_id`：range_id : range (@id α) = univ
-/
theorem range_id : (AlgHom.id R A).range = ⊤ :=
  SetLike.coe_injective Set.range_id

@[simp]
/-
**Algebra.map_top** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：map_top (f : A ->ₐ[R] B) : (⊤ : Subalgebra R A).map f = f.range
参数：f : A ->ₐ[R] B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
-/
theorem map_top (f : A →ₐ[R] B) : (⊤ : Subalgebra R A).map f = f.range :=
  SetLike.coe_injective Set.image_univ

@[simp]
/-
**Algebra.map_bot** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：map_bot (f : A ->ₐ[R] B) : (⊥ : Subalgebra R A).map f = ⊥
参数：f : A ->ₐ[R] B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.toSubmodule_injective`：toSubmodule_injective : Function.Injec
tive (toSubmodule : Subalgebra R A -> Submodule R A)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Subalgebra.map_toSubmodule`：map_toSubmodule {S : Subalgebra R A} {f : A 
->ₐ[R] B} : (toSubmodule <| S.map f) = S.toSubmodule.map f.toLinearMap
· 使用定理 `Submodule.map.congr_simp`：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5
} {M₂ : Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddComm
Monoid M] [ins…
· 使用定理 `Algebra.toSubmodule_bot`：toSubmodule_bot : Subalgebra.toSubmodule (⊥ : S
ubalgebra R A) = 1
· 使用定理 `Submodule.map_one`：∀ {R : Type u} [inst : CommSemiring R] {A : Type v} [
inst_1 : Semiring A] [inst_2 : Algebra R A] {A' : Type u_1}   [inst_3 : Semiring
 A'] [i…
-/
theorem map_bot (f : A →ₐ[R] B) : (⊥ : Subalgebra R A).map f = ⊥ :=
  Subalgebra.toSubmodule_injective <| by
    simpa only [Subalgebra.map_toSubmodule, toSubmodule_bot] using Submodule.map_one _

@[simp]
/-
**Algebra.comap_top** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：comap_top (f : A ->ₐ[R] B) : (⊤ : Subalgebra R B).comap f = ⊤
参数：f : A ->ₐ[R] B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Algebra.eq_top_iff`：eq_top_iff {S : Subalgebra R A} : S = ⊤ ↔ forall x :
 A, x in S
· 使用定理 `Algebra.mem_top`：mem_top {x : A} : x in (⊤ : Subalgebra R A)
-/
theorem comap_top (f : A →ₐ[R] B) : (⊤ : Subalgebra R B).comap f = ⊤ :=
  eq_top_iff.2 fun _x => mem_top

/-- `AlgHom` to `⊤ : Subalgebra R A`. -/
/-
**Algebra.toTop** 是 Mathlib 中的一个定义，位于命名空间 `Algebra`。
形式化陈述：toTop : A ->ₐ[R] (⊤ : Subalgebra R A)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`AlgHom` to `⊤ : Subalgebra R A`.
-/
def toTop : A →ₐ[R] (⊤ : Subalgebra R A) :=
  (AlgHom.id R A).codRestrict ⊤ fun _ => mem_top
/-
**Algebra.surjective_algebraMap_iff** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：surjective_algebraMap_iff : Function.Surjective (algebraMap R A) ↔ (⊤ : Su
balgebra R A) = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用定理 `Subalgebra.algebraMap_mem`：∀ {R : Type u} {A : Type v} [inst : CommSemir
ing R] [inst_1 : Semiring A] [inst_2 : Algebra R A] (S : Subalgebra R A)   (r : 
R), (algebraMap…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Algebra.mem_bot`：mem_bot {x : A} : x in (⊥ : Subalgebra R A) ↔ x in Set.
range (algebraMap R A)
· 使用定理 `Algebra.mem_top`：mem_top {x : A} : x in (⊤ : Subalgebra R A)
-/
theorem surjective_algebraMap_iff :
    Function.Surjective (algebraMap R A) ↔ (⊤ : Subalgebra R A) = ⊥ :=
  ⟨fun h =>
    eq_bot_iff.2 fun y _ =>
      let ⟨_x, hx⟩ := h y
      hx ▸ Subalgebra.algebraMap_mem _ _,
    fun h y => Algebra.mem_bot.1 <| eq_bot_iff.1 h (Algebra.mem_top : y ∈ _)⟩
/-
**Algebra.bijective_algebraMap_iff** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：bijective_algebraMap_iff {R A : Type*} [Field R] [Semiring A] [Nontrivial 
A] [Algebra R A] : Function.Bijective (algebraMap R A) ↔ (⊤ : Subalgebra R A) = 
⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Algebra.surjective_algebraMap_iff`：surjective_algebraMap_iff : Function.
Surjective (algebraMap R A) ↔ (⊤ : Subalgebra R A) = ⊥
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem bijective_algebraMap_iff {R A : Type*} [Field R] [Semiring A] [Nontrivial A]
    [Algebra R A] : Function.Bijective (algebraMap R A) ↔ (⊤ : Subalgebra R A) = ⊥ :=
  ⟨fun h => surjective_algebraMap_iff.1 h.2, fun h =>
    ⟨(algebraMap R A).injective, surjective_algebraMap_iff.2 h⟩⟩

/-- The bottom subalgebra is isomorphic to the base ring. -/
/-
**Algebra.botEquivOfInjective** 是 Mathlib 中的一个定义，位于命名空间 `Algebra`。
形式化陈述：botEquivOfInjective (h : Function.Injective (algebraMap R A)) : (⊥ : Subal
gebra R A) ≃ₐ[R] R
参数：h : Function.Injective (algebraMap R A)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The bottom subalgebra is isomorphic to the base ring.
-/
noncomputable def botEquivOfInjective (h : Function.Injective (algebraMap R A)) :
    (⊥ : Subalgebra R A) ≃ₐ[R] R :=
  AlgEquiv.symm <|
    AlgEquiv.ofBijective (Algebra.ofId R _)
      ⟨fun _x _y hxy => h (congr_arg Subtype.val hxy :), fun ⟨_y, x, hx⟩ => ⟨x, Subtype.ext hx⟩⟩

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- The bottom subalgebra is isomorphic to the field. -/
@[simps! symm_apply]
/-
**Algebra.botEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Algebra`。
形式化陈述：botEquiv (F R : Type*) [Field F] [Semiring R] [Nontrivial R] [Algebra F R]
 : (⊥ : Subalgebra F R) ≃ₐ[F] F
参数：F R : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The bottom subalgebra is isomorphic to the field.
-/
noncomputable def botEquiv (F R : Type*) [Field F] [Semiring R] [Nontrivial R] [Algebra F R] :
    (⊥ : Subalgebra F R) ≃ₐ[F] F :=
  botEquivOfInjective (RingHom.injective _)

end Algebra

namespace Subalgebra

open Algebra

variable {R : Type u} {A : Type v} {B : Type w}
variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]
variable (S : Subalgebra R A)

/-- The top subalgebra is isomorphic to the algebra.

This is the algebra version of `Submodule.topEquiv`. -/
@[simps!]
/-
**Subalgebra.topEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Subalgebra`。
形式化陈述：topEquiv : (⊤ : Subalgebra R A) ≃ₐ[R] A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The top subalgebra is isomorphic to the algebra.

This is the algebra version of `Submodule.topEquiv`.
-/
def topEquiv : (⊤ : Subalgebra R A) ≃ₐ[R] A :=
  AlgEquiv.ofAlgHom (Subalgebra.val ⊤) toTop rfl rfl
/-
**Subalgebra._root_.AlgHom.subsingleton** 是 Mathlib 中的一个实例，位于命名空间 `Subalgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance _root_.AlgHom.subsingleton [Subsingleton (Subalgebra R A)] : Subsingleton (A →ₐ[R] B) :=
  ⟨fun f g =>
    AlgHom.ext fun a =>
      have : a ∈ (⊥ : Subalgebra R A) := Subsingleton.elim (⊤ : Subalgebra R A) ⊥ ▸ mem_top
      let ⟨_x, hx⟩ := Set.mem_range.mp (mem_bot.mp this)
      hx ▸ (f.commutes _).trans (g.commutes _).symm⟩
/-
**Subalgebra._root_.AlgEquiv.subsingleton_left** 是 Mathlib 中的一个实例，位于命名空间 `Subalg
ebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance _root_.AlgEquiv.subsingleton_left [Subsingleton (Subalgebra R A)] :
    Subsingleton (A ≃ₐ[R] B) :=
  ⟨fun f g => AlgEquiv.ext fun x => AlgHom.ext_iff.mp (Subsingleton.elim f.toAlgHom g.toAlgHom) x⟩
/-
**Subalgebra._root_.AlgEquiv.subsingleton_right** 是 Mathlib 中的一个实例，位于命名空间 `Subal
gebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance _root_.AlgEquiv.subsingleton_right [Subsingleton (Subalgebra R B)] :
    Subsingleton (A ≃ₐ[R] B) :=
  ⟨fun f g => by rw [← f.symm_symm, Subsingleton.elim f.symm g.symm, g.symm_symm]⟩
/-
**Subalgebra.** 是 Mathlib 中的一个实例，位于命名空间 `Subalgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Unique (Subalgebra R R) :=
  { (inferInstance : Inhabited (Subalgebra R R)) with
    uniq := by
      intro S
      refine le_antisymm ?_ bot_le
      intro _ _
      simp only [Set.mem_range, mem_bot, algebraMap_self_apply, exists_apply_eq_apply, default] }

section Center

variable (R A)

@[simp]
/-
**Subalgebra.center_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：center_eq_top (A : Type*) [CommSemiring A] [Algebra R A] : center R A = ⊤
参数：A : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.center_eq_univ`：center_eq_univ : center M = univ
-/
theorem center_eq_top (A : Type*) [CommSemiring A] [Algebra R A] : center R A = ⊤ :=
  SetLike.coe_injective (Set.center_eq_univ A)

end Center

section Centralizer

variable (R)

@[simp]
/-
**Subalgebra.centralizer_eq_top_iff_subset** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra
`。
形式化陈述：centralizer_eq_top_iff_subset {s : Set A} : centralizer R s = ⊤ ↔ s subset
eq center R A
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `SetLike.ext'_iff`：∀ {A : Type u_1} {B : Type u_2} [i : SetLike A B] {p q
 : A}, p = q ↔ ↑p = ↑q
· 使用定理 `Set.centralizer_eq_top_iff_subset`：centralizer_eq_top_iff_subset : centr
alizer S = Set.univ ↔ S subseteq center M
-/
theorem centralizer_eq_top_iff_subset {s : Set A} : centralizer R s = ⊤ ↔ s ⊆ center R A :=
  SetLike.ext'_iff.trans Set.centralizer_eq_top_iff_subset

end Centralizer

end Subalgebra

section Equalizer

namespace AlgHom

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

@[simp]
/-
**AlgHom.equalizer_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：equalizer_eq_top {φ ψ : A ->ₐ[R] B} : equalizer φ ψ = ⊤ ↔ φ = ψ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem equalizer_eq_top {φ ψ : A →ₐ[R] B} : equalizer φ ψ = ⊤ ↔ φ = ψ := by
  simp [SetLike.ext_iff, DFunLike.ext_iff]

@[simp]
/-
**AlgHom.equalizer_same** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：equalizer_same (φ : A ->ₐ[R] B) : equalizer φ φ = ⊤
参数：φ : A ->ₐ[R] B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `AlgHom.equalizer_eq_top`：equalizer_eq_top {φ ψ : A ->ₐ[R] B} : equalizer
 φ ψ = ⊤ ↔ φ = ψ
-/
theorem equalizer_same (φ : A →ₐ[R] B) : equalizer φ φ = ⊤ := equalizer_eq_top.2 rfl

variable {F : Type*} [FunLike F A B] [AlgHomClass F R A B]
/-
**AlgHom.eqOn_sup** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：eqOn_sup {φ ψ : F} {S T : Subalgebra R A} (hS : Set.EqOn φ ψ S) (hT : Set.
EqOn φ ψ T) : Set.EqOn φ ψ ↑(S ⊔ T)
参数：hS : Set.EqOn φ ψ S；hT : Set.EqOn φ ψ T。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgHom.coe_coe`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : CommSem
iring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra R A] [i
nst_…
· 使用定理 `AlgHom.le_equalizer`：le_equalizer {φ ψ : A ->ₐ[R] B} {S : Subalgebra R A
} : S <= equalizer φ ψ ↔ Set.EqOn φ ψ S
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
-/
theorem eqOn_sup {φ ψ : F} {S T : Subalgebra R A} (hS : Set.EqOn φ ψ S) (hT : Set.EqOn φ ψ T) :
    Set.EqOn φ ψ ↑(S ⊔ T) := by
  rw [← AlgHom.coe_coe φ, ← AlgHom.coe_coe ψ, ← le_equalizer] at hS hT ⊢
  exact sup_le hS hT
/-
**AlgHom.ext_on_codisjoint** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：ext_on_codisjoint {φ ψ : F} {S T : Subalgebra R A} (hST : Codisjoint S T) 
(hS : Set.EqOn φ ψ S) (hT : Set.EqOn φ ψ T) : φ = ψ
参数：hST : Codisjoint S T；hS : Set.EqOn φ ψ S；hT : Set.EqOn φ ψ T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
· 使用定理 `AlgHom.eqOn_sup`：eqOn_sup {φ ψ : F} {S T : Subalgebra R A} (hS : Set.EqO
n φ ψ S) (hT : Set.EqOn φ ψ T) : Set.EqOn φ ψ ↑(S ⊔ T)
· 使用定理 `trivial`：True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Codisjoint.eq_top`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : 
OrderTop α] {a b : α}, Codisjoint a b → a ⊔ b = ⊤
-/
theorem ext_on_codisjoint {φ ψ : F} {S T : Subalgebra R A} (hST : Codisjoint S T)
    (hS : Set.EqOn φ ψ S) (hT : Set.EqOn φ ψ T) : φ = ψ :=
  DFunLike.ext _ _ fun _ ↦ eqOn_sup hS hT <| hST.eq_top.symm ▸ trivial

end AlgHom

end Equalizer

section MapComap

namespace Subalgebra

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

/-
**Subalgebra.map_comap_eq** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：map_comap_eq (f : A ->ₐ[R] B) (S : Subalgebra R B) : (S.comap f).map f = S
 ⊓ f.range
参数：f : A ->ₐ[R] B；S : Subalgebra R B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.image_preimage_eq_inter_range`：image_preimage_eq_inter_range {f : α 
-> β} {t : Set β} : f '' f ⁻¹' t = t inter range f
-/
theorem map_comap_eq (f : A →ₐ[R] B) (S : Subalgebra R B) : (S.comap f).map f = S ⊓ f.range :=
  SetLike.coe_injective Set.image_preimage_eq_inter_range
/-
**Subalgebra.map_comap_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：map_comap_eq_self {f : A ->ₐ[R] B} {S : Subalgebra R B} (h : S <= f.range)
 : (S.comap f).map f = S
参数：h : S <= f.range。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `Subalgebra.map_comap_eq`：map_comap_eq (f : A ->ₐ[R] B) (S : Subalgebra R
 B) : (S.comap f).map f = S ⊓ f.range
-/
theorem map_comap_eq_self
    {f : A →ₐ[R] B} {S : Subalgebra R B} (h : S ≤ f.range) : (S.comap f).map f = S := by
  simpa only [inf_of_le_left h] using map_comap_eq f S
/-
**Subalgebra.map_comap_eq_self_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Subalgeb
ra`。
形式化陈述：map_comap_eq_self_of_surjective {f : A ->ₐ[R] B} (hf : Function.Surjective
 f) (S : Subalgebra R B) : (S.comap f).map f = S
参数：hf : Function.Surjective f；S : Subalgebra R B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.map_comap_eq_self`：map_comap_eq_self {f : A ->ₐ[R] B} {S : Su
balgebra R B} (h : S <= f.range) : (S.comap f).map f = S
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `AlgHom.range_eq_top`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : Co
mmSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_3 : Semiring 
B] [inst_…
-/
theorem map_comap_eq_self_of_surjective
    {f : A →ₐ[R] B} (hf : Function.Surjective f) (S : Subalgebra R B) : (S.comap f).map f = S :=
  map_comap_eq_self <| by simp [(AlgHom.range_eq_top f).2 hf]

end Subalgebra

end MapComap

section saturation

namespace Subalgebra

variable {R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
  {s : Subalgebra R S} {M : Submonoid S} {H : M ≤ s.toSubmonoid}

/-- The saturation of a subalgebra `s` with respect to a submonoid `M` is the smallest
subalgebra closed under division by `s`. -/
/-
**Subalgebra.saturation** 是 Mathlib 中的一个定义，位于命名空间 `Subalgebra`。
形式化陈述：saturation (s : Subalgebra R S) (M : Submonoid S) (H : M <= s.toSubmonoid)
 : Subalgebra R S where carrier
参数：s : Subalgebra R S；M : Submonoid S；H : M <= s.toSubmonoid。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The saturation of a subalgebra `s` with respect to a submonoid `M` is the smalle
st
subalgebra closed under division by `s`.
-/
def saturation (s : Subalgebra R S) (M : Submonoid S) (H : M ≤ s.toSubmonoid) :
    Subalgebra R S where
  carrier := { x | ∃ m ∈ M, m * x ∈ s }
  mul_mem' := by
    intro a b ⟨m, hm, ha⟩ ⟨n, hn, hb⟩
    refine ⟨_, mul_mem hm hn, mul_mul_mul_comm m n a b ▸ mul_mem ha hb⟩
  add_mem' := by
    intro a b ⟨m, hm, ha⟩ ⟨n, hn, hb⟩
    refine ⟨_, mul_mem hn hm, ?_⟩
    rw [mul_add, mul_assoc, mul_comm n m, mul_assoc]
    exact add_mem (mul_mem (H hn) ha) (mul_mem (H hm) hb)
  algebraMap_mem' r := ⟨1, one_mem _, by simp⟩
/-
**Subalgebra.mem_saturation_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : CommSemiring R] [inst_1 : CommSemi
ring S] [inst_2 : Algebra R S]   {s : Subalgebra R S} {M : Submonoid S} {H : M ≤
 s.toSubmonoid} {x : S}, x ∈ s.saturation M H ↔ ∃ m ∈ M, m • x ∈ s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma mem_saturation_iff {x : S} :
    x ∈ s.saturation M H ↔ ∃ m ∈ M, m • x ∈ s := .rfl
/-
**Subalgebra.le_saturation** 是 Mathlib 中的一个引理，位于命名空间 `Subalgebra`。
形式化陈述：le_saturation : s <= s.saturation M H
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OneMemClass.one_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
One M} {inst_1 : SetLike S M} [self : OneMemClass S M] (s : S), 1 ∈ s
· 使用定理 `SubmonoidClass.toOneMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   On
eMemClass S M
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
lemma le_saturation : s ≤ s.saturation M H :=
  fun x hx ↦ ⟨1, one_mem M, by simpa⟩
/-
**Subalgebra.saturation_saturation** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : CommSemiring R] [inst_1 : CommSemi
ring S] [inst_2 : Algebra R S]   {s : Subalgebra R S} {M : Submonoid S} {H : M ≤
 s.toSubmonoid}, (s.saturation M H).saturation M ⋯ = s.saturation M H
参数：s.saturation M H。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≤ b → a = b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `Subalgebra.le_saturation`：le_saturation : s <= s.saturation M H
· 使用定理 `Submonoid.mul_mem`：∀ {M : Type u_1} [inst : MulOneClass M] (S : Submonoi
d M) {x y : M}, x ∈ S → y ∈ S → x * y ∈ S
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
-/
@[simp] lemma saturation_saturation :
    (s.saturation M H).saturation M (H.trans s.le_saturation) = s.saturation M H :=
  le_saturation.antisymm' fun x ⟨m, hm, n, hn, h⟩ ↦ ⟨_, M.mul_mem hn hm, mul_assoc n m x ▸ h⟩
/-
**Subalgebra.mem_saturation_of_mul_mem_left** 是 Mathlib 中的一个引理，位于命名空间 `Subalgebr
a`。
形式化陈述：mem_saturation_of_mul_mem_left {x y} (hxy : x * y in s.saturation M H) (hx
 : x in M) : y in s.saturation M H
参数：hxy : x * y in s.saturation M H；hx : x in M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `Subalgebra.le_saturation`：le_saturation : s <= s.saturation M H
· 使用定理 `Subalgebra.saturation_saturation`：∀ {R : Type u_1} {S : Type u_2} [inst 
: CommSemiring R] [inst_1 : CommSemiring S] [inst_2 : Algebra R S]   {s : Subalg
ebra R S} {M : Submono…
-/
lemma mem_saturation_of_mul_mem_left {x y} (hxy : x * y ∈ s.saturation M H)
    (hx : x ∈ M) : y ∈ s.saturation M H :=
  saturation_saturation.le ⟨_, hx, hxy⟩
/-
**Subalgebra.mem_saturation_of_mul_mem_right** 是 Mathlib 中的一个引理，位于命名空间 `Subalgeb
ra`。
形式化陈述：mem_saturation_of_mul_mem_right {x y} (hxy : x * y in s.saturation M H) (h
y : y in M) : x in s.saturation M H
参数：hxy : x * y in s.saturation M H；hy : y in M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Subalgebra.mem_saturation_of_mul_mem_left`：mem_saturation_of_mul_mem_lef
t {x y} (hxy : x * y in s.saturation M H) (hx : x in M) : y in s.saturation M H
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
lemma mem_saturation_of_mul_mem_right {x y} (hxy : x * y ∈ s.saturation M H)
    (hy : y ∈ M) : x ∈ s.saturation M H :=
  mem_saturation_of_mul_mem_left (mul_comm x y ▸ hxy) hy

end Subalgebra

end saturation

section Adjoin

universe uR uS uA uB

open Submodule Subsemiring

variable {R : Type uR} {S : Type uS} {A : Type uA} {B : Type uB}

namespace Algebra

/--
If `x₁ x₂ ... xₙ : A` then `R[x₁,x₂,...,xₙ]` is the `Subalgebra R A` generated by these elements. -/
scoped syntax:max (name := subalgebra_adjoin) term "[" term,* (" : " term)? "]" : term

/--
If `x₁ x₂ ... xₙ : A` then `R[x₁,x₂,...,xₙ]` is the `Subalgebra R A` generated by these elements. -/
macro_rules (kind := subalgebra_adjoin)
  | `($R[$xs,*]) => `(Algebra.adjoin $R {$xs:term,*})
  | `($R[$xs,* : $A]) => do
    let xs' ← xs.getElems.mapM fun x => `(($x : $A))
    `(Algebra.adjoin $R ({$[$xs':term],*} : Set $A))

open Lean PrettyPrinter.Delaborator SubExpr in
/-- Supporting function for the `R[x₁,x₂,...,xₙ]` adjunction notation. -/
@[app_delab Algebra.adjoin]
meta partial def delabAdjoinNotation : Delab := whenPPOption getPPNotation do
  withOverApp 6 do
  let F ← withNaryArg 0 delab
  let xs ← withNaryArg 5 delabInsertArray
  `($F[$(xs.toArray),*])
where
  delabInsertArray : DelabM (List Term) := do
    let e ← getExpr
    if e.isAppOfArity ``EmptyCollection.emptyCollection 2 then
      return []
    if e.isAppOfArity ``singleton 4 then
      let x ← withNaryArg 3 delab
      return [x]
    if e.isAppOfArity ``insert 5 then
      let x ← withNaryArg 3 delab
      let xs ← withNaryArg 4 delabInsertArray
      return x :: xs
    failure

open Algebra

section Semiring

variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]
variable [Algebra R S] [Algebra R A] [Algebra S A] [Algebra R B] [IsScalarTower R S A]
variable {s t : Set A}

@[simp, aesop safe 20 (rule_sets := [SetLike])]
/-
**Algebra.subset_adjoin** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：subset_adjoin : s subseteq adjoin R s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.le_u_l`：le_u_l (a) : a <= u (l a)
· 使用定理 `Algebra.gc`：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] [inst_1 
: Semiring A] [inst_2 : Algebra R A],   GaloisConnection (Algebra.adjoin R) SetL
…
-/
theorem subset_adjoin : s ⊆ adjoin R s :=
  Algebra.gc.le_u_l s

@[aesop 80% (rule_sets := [SetLike])]
/-
**Algebra.mem_adjoin_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：mem_adjoin_of_mem {s : Set A} {x : A} (hx : x in s) : x in adjoin R s
参数：hx : x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.subset_adjoin`：subset_adjoin : s subseteq adjoin R s
-/
theorem mem_adjoin_of_mem {s : Set A} {x : A} (hx : x ∈ s) : x ∈ adjoin R s := subset_adjoin hx

/-
The following set-up allows one to write `xₖ : R[x₁, ..., xₙ]` instead of
`(⟨xₖ, "membership proof"⟩ : R[x₁, ..., xₙ])`.

The idea is to recurse through the list of `x₁, ..., xₙ` until we find the appropriate `xₖ`.
By design, it only triggers if the set is of the form `insert x₁ (insert x₂ (...(s)))` or
`{x₁, ..., xₙ}`.
-/

variable {α : Type*}

/-- Supporting class for coercions `xₖ : R[x₁, ..., xₙ]`. -/
/-
**Algebra.CoeAdjoinAux** 是 Mathlib 中的一个类，位于命名空间 `Algebra`。
形式化陈述：CoeAdjoinAux (x : α) (s : Set α) : Prop where mem : x in s  scoped instanc
e (x : α) : CoeAdjoinAux x {x}
参数：x : α；s : Set α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Supporting class for coercions `xₖ : R[x₁, ..., xₙ]`.
-/
class CoeAdjoinAux (x : α) (s : Set α) : Prop where mem : x ∈ s
/-
**Algebra.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
scoped instance (x : α) : CoeAdjoinAux x {x} := ⟨Set.mem_singleton x⟩
/-
**Algebra.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
scoped instance (x : α) (s : Set α) : CoeAdjoinAux x (insert x s) := ⟨Set.mem_insert x s⟩
/-
**Algebra.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
scoped instance (x y : α) (s : Set α) [CoeAdjoinAux x s] : CoeAdjoinAux x (insert y s) :=
  ⟨Set.mem_insert_of_mem y CoeAdjoinAux.mem⟩

/-- Enables notation `xₖ : R[x₁, ..., xₙ]` instead of
`(⟨xₖ, "membership proof"⟩ : R[x₁, ..., xₙ])`. -/
/-
**Algebra.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Enables notation `xₖ : R[x₁, ..., xₙ]` instead of
`(⟨xₖ, "membership proof"⟩ : R[x₁, ..., xₙ])`.
-/
scoped instance {A B : Type*} [CommSemiring A] [Semiring B] [Algebra A B]
    (s : Set B) (x : B) [CoeAdjoinAux x s] :
    CoeDep B x (adjoin A s) where
  coe := ⟨x, mem_adjoin_of_mem CoeAdjoinAux.mem⟩
/-
**Algebra.adjoin_le** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：adjoin_le {S : Subalgebra R A} (H : s subseteq S) : adjoin R s <= S
参数：H : s subseteq S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_le`：l_le {a : α} {b : β} : a <= u b -> l a <= b
· 使用定理 `Algebra.gc`：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] [inst_1 
: Semiring A] [inst_2 : Algebra R A],   GaloisConnection (Algebra.adjoin R) SetL
…
-/
theorem adjoin_le {S : Subalgebra R A} (H : s ⊆ S) : adjoin R s ≤ S :=
  Algebra.gc.l_le H
/-
**Algebra.adjoin_singleton_le** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：adjoin_singleton_le {S : Subalgebra R A} {a : A} (H : a in S) : R[a] <= S
参数：H : a in S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.adjoin_le`：adjoin_le {S : Subalgebra R A} (H : s subseteq S) : a
djoin R s <= S
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
-/
theorem adjoin_singleton_le {S : Subalgebra R A} {a : A} (H : a ∈ S) : R[a] ≤ S :=
  adjoin_le (Set.singleton_subset_iff.mpr H)
/-
**Algebra.adjoin_eq_sInf** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：adjoin_eq_sInf : adjoin R s = sInf { p : Subalgebra R A | s subseteq p }
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_sInf`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, (∀ b ∈ s, a ≤ b) → a ≤ sInf s
· 使用定理 `Algebra.adjoin_le`：adjoin_le {S : Subalgebra R A} (H : s subseteq S) : a
djoin R s <= S
· 使用定理 `sInf_le`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, a ∈ s → sInf s ≤ a
· 使用定理 `Algebra.subset_adjoin`：subset_adjoin : s subseteq adjoin R s
-/
theorem adjoin_eq_sInf : adjoin R s = sInf { p : Subalgebra R A | s ⊆ p } :=
  le_antisymm (le_sInf fun _ h => adjoin_le h) (sInf_le subset_adjoin)
/-
**Algebra.adjoin_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：adjoin_le_iff {S : Subalgebra R A} : adjoin R s <= S ↔ s subseteq S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.gc`：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] [inst_1 
: Semiring A] [inst_2 : Algebra R A],   GaloisConnection (Algebra.adjoin R) SetL
…
-/
theorem adjoin_le_iff {S : Subalgebra R A} : adjoin R s ≤ S ↔ s ⊆ S :=
  Algebra.gc _ _

@[gcongr]
/-
**Algebra.adjoin_mono** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：adjoin_mono (H : s subseteq t) : adjoin R s <= adjoin R t
参数：H : s subseteq t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.monotone_l`：∀ {α : Type u} {β : Type v} [inst : Preorde
r α] [inst_1 : Preorder β] {u : α → β} {l : β → α},   GaloisConnection l u → Mon
otone l
· 使用定理 `Algebra.gc`：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] [inst_1 
: Semiring A] [inst_2 : Algebra R A],   GaloisConnection (Algebra.adjoin R) SetL
…
-/
theorem adjoin_mono (H : s ⊆ t) : adjoin R s ≤ adjoin R t :=
  Algebra.gc.monotone_l H
/-
**Algebra.adjoin_eq_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：adjoin_eq_of_le (S : Subalgebra R A) (h₁ : s subseteq S) (h₂ : S <= adjoin
 R s) : adjoin R s = S
参数：S : Subalgebra R A；h₁ : s subseteq S；h₂ : S <= adjoin R s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Algebra.adjoin_le`：adjoin_le {S : Subalgebra R A} (H : s subseteq S) : a
djoin R s <= S
-/
theorem adjoin_eq_of_le (S : Subalgebra R A) (h₁ : s ⊆ S) (h₂ : S ≤ adjoin R s) : adjoin R s = S :=
  le_antisymm (adjoin_le h₁) h₂
/-
**Algebra.adjoin_eq** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：adjoin_eq (S : Subalgebra R A) : adjoin R ↑S = S
参数：S : Subalgebra R A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.adjoin_eq_of_le`：adjoin_eq_of_le (S : Subalgebra R A) (h₁ : s su
bseteq S) (h₂ : S <= adjoin R s) : adjoin R s = S
· 使用定理 `Set.Subset.refl`：∀ {α : Type u} (a : Set α), a ⊆ a
· 使用定理 `Algebra.subset_adjoin`：subset_adjoin : s subseteq adjoin R s
-/
theorem adjoin_eq (S : Subalgebra R A) : adjoin R ↑S = S :=
  adjoin_eq_of_le _ (Set.Subset.refl _) subset_adjoin
/-
**Algebra.adjoin_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：adjoin_iUnion {α : Type*} (s : α -> Set A) : adjoin R (Set.iUnion s) = ⨆ i
 : α, adjoin R (s i)
参数：s : α -> Set A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_iSup`：l_iSup {f : ι -> α} : l (iSup f) = ⨆ i, l (f i)
· 使用定理 `Algebra.gc`：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] [inst_1 
: Semiring A] [inst_2 : Algebra R A],   GaloisConnection (Algebra.adjoin R) SetL
…
-/
theorem adjoin_iUnion {α : Type*} (s : α → Set A) :
    adjoin R (Set.iUnion s) = ⨆ i : α, adjoin R (s i) :=
  (@Algebra.gc R A _ _ _).l_iSup
/-
**Algebra.adjoin_attach_biUnion** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：adjoin_attach_biUnion [DecidableEq A] {α : Type*} {s : Finset α} (f : s ->
 Finset A) : adjoin R (s.attach.biUnion f : Set A) = ⨆ x, adjoin R (f x)
参数：f : s -> Finset A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.coe_biUnion`：coe_biUnion : (s.biUnion t : Set β) = ⋃ x in (s : Se
t α), t x
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Finset.coe_attach`：coe_attach (s : Finset α) : (s.attach : Set s) = Set.
univ
· 使用定理 `Set.iUnion_true`：iUnion_true {s : True -> Set α} : iUnion s = s trivial
· 使用定理 `Algebra.adjoin_iUnion`：adjoin_iUnion {α : Type*} (s : α -> Set A) : adjo
in R (Set.iUnion s) = ⨆ i : α, adjoin R (s i)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem adjoin_attach_biUnion [DecidableEq A] {α : Type*} {s : Finset α} (f : s → Finset A) :
    adjoin R (s.attach.biUnion f : Set A) = ⨆ x, adjoin R (f x) := by simp [adjoin_iUnion]

@[elab_as_elim]
/-
**Algebra.adjoin_induction** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：adjoin_induction {p : (x : A) -> x in adjoin R s -> Prop} (mem : forall (x
) (hx : x in s), p x (subset_adjoin hx)) (algebraMap : forall r, p (algebraMap R
 A r) (algebraMap_mem _ r)) (add : forall x y hx hy, p x hx -> p y hy -> p (x + 
y) (add_mem hx hy)) (mul : forall x y hx hy, p x hx -> p y hy -> p (x * y) (mul_
mem hx hy)) {x : A} (hx : x in adjoin R s) : p x hx
参数：x : A；mem : forall (x) (hx : x in s), p x (subset_adjoin hx)；algebraMap : for
all r, p (algebraMap R A r) (algebraMap_mem _ r)；add : forall x y hx hy, p x hx 
-> p y hy -> p (x + y) (add_mem hx hy)；mul : forall x y hx hy, p x hx -> p y hy 
-> p (x * y) (mul_mem hx hy)；hx : x in adjoin R s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.subset_adjoin`：subset_adjoin : s subseteq adjoin R s
· 使用定理 `algebraMap_mem`：∀ {S : Type u_1} {R : Type u_2} {A : Type u_3} [inst : C
ommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_3 : SetLike 
S A]…
· 使用定理 `AddSubmonoidWithOneClass.toOneMemClass`：∀ {S : Type u_1} {R : outParam (
Type u_2)} {inst : AddMonoidWithOne R} {inst_1 : SetLike S R}   [self : AddSubmo
noidWithOneClass S R], OneMe…
· 使用定理 `SubsemiringClass.addSubmonoidWithOneClass`：∀ (S : Type u_1) (R : Type u)
 {x : NonAssocSemiring R} [inst : SetLike S R] [h : SubsemiringClass S R],   Add
SubmonoidWithOneClass S R
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
· 使用定理 `SubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Ty
pe u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringC
lass S R], AddSubmonoidCla…
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `SubsemiringClass.toSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Type 
u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringClas
s S R], SubmonoidClass …
· 使用定理 `RingHom.map_one`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} (f : α →+* β), f 1 = 1
· 使用定理 `RingHom.map_zero`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring 
α} {x_1 : NonAssocSemiring β} (f : α →+* β), f 0 = 0
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `Algebra.adjoin_le`：adjoin_le {S : Subalgebra R A} (H : s subseteq S) : a
djoin R s <= S
-/
theorem adjoin_induction {p : (x : A) → x ∈ adjoin R s → Prop}
    (mem : ∀ (x) (hx : x ∈ s), p x (subset_adjoin hx))
    (algebraMap : ∀ r, p (algebraMap R A r) (algebraMap_mem _ r))
    (add : ∀ x y hx hy, p x hx → p y hy → p (x + y) (add_mem hx hy))
    (mul : ∀ x y hx hy, p x hx → p y hy → p (x * y) (mul_mem hx hy))
    {x : A} (hx : x ∈ adjoin R s) : p x hx :=
  let S : Subalgebra R A :=
    { carrier := { x | ∃ hx, p x hx }
      mul_mem' := by rintro _ _ ⟨_, hpx⟩ ⟨_, hpy⟩; exact ⟨_, mul _ _ _ _ hpx hpy⟩
      add_mem' := by rintro _ _ ⟨_, hpx⟩ ⟨_, hpy⟩; exact ⟨_, add _ _ _ _ hpx hpy⟩
      algebraMap_mem' := fun r ↦ ⟨_, algebraMap r⟩ }
  adjoin_le (S := S) (fun y hy ↦ ⟨subset_adjoin hy, mem y hy⟩) hx |>.elim fun _ ↦ _root_.id

/-- Induction principle for the algebra generated by a set `s`: show that `p x y` holds for any
`x y ∈ adjoin R s` given that it holds for `x y ∈ s` and that it satisfies a number of
natural properties. -/
@[elab_as_elim]
/-
**Algebra.adjoin_induction** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：adjoin_induction {p : (x : A) -> x in adjoin R s -> Prop} (mem : forall (x
) (hx : x in s), p x (subset_adjoin hx)) (algebraMap : forall r, p (algebraMap R
 A r) (algebraMap_mem _ r)) (add : forall x y hx hy, p x hx -> p y hy -> p (x + 
y) (add_mem hx hy)) (mul : forall x y hx hy, p x hx -> p y hy -> p (x * y) (mul_
mem hx hy)) {x : A} (hx : x in adjoin R s) : p x hx
参数：x : A；mem : forall (x) (hx : x in s), p x (subset_adjoin hx)；algebraMap : for
all r, p (algebraMap R A r) (algebraMap_mem _ r)；add : forall x y hx hy, p x hx 
-> p y hy -> p (x + y) (add_mem hx hy)；mul : forall x y hx hy, p x hx -> p y hy 
-> p (x * y) (mul_mem hx hy)；hx : x in adjoin R s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.subset_adjoin`：subset_adjoin : s subseteq adjoin R s
· 使用定理 `algebraMap_mem`：∀ {S : Type u_1} {R : Type u_2} {A : Type u_3} [inst : C
ommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_3 : SetLike 
S A]…
· 使用定理 `AddSubmonoidWithOneClass.toOneMemClass`：∀ {S : Type u_1} {R : outParam (
Type u_2)} {inst : AddMonoidWithOne R} {inst_1 : SetLike S R}   [self : AddSubmo
noidWithOneClass S R], OneMe…
· 使用定理 `SubsemiringClass.addSubmonoidWithOneClass`：∀ (S : Type u_1) (R : Type u)
 {x : NonAssocSemiring R} [inst : SetLike S R] [h : SubsemiringClass S R],   Add
SubmonoidWithOneClass S R
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
· 使用定理 `SubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Ty
pe u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringC
lass S R], AddSubmonoidCla…
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `SubsemiringClass.toSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Type 
u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringClas
s S R], SubmonoidClass …
· 使用定理 `RingHom.map_one`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} (f : α →+* β), f 1 = 1
· 使用定理 `RingHom.map_zero`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring 
α} {x_1 : NonAssocSemiring β} (f : α →+* β), f 0 = 0
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `Algebra.adjoin_le`：adjoin_le {S : Subalgebra R A} (H : s subseteq S) : a
djoin R s <= S

--- 原说明 ---
Induction principle for the algebra generated by a set `s`: show that `p x y` ho
lds for any
`x y ∈ adjoin R s` given that it holds for `x y ∈ s` and that it satisfies a num
ber of
natural properties.
-/
theorem adjoin_induction₂ {s : Set A} {p : (x y : A) → x ∈ adjoin R s → y ∈ adjoin R s → Prop}
    (mem_mem : ∀ (x) (y) (hx : x ∈ s) (hy : y ∈ s), p x y (subset_adjoin hx) (subset_adjoin hy))
    (algebraMap_both : ∀ r₁ r₂, p (algebraMap R A r₁) (algebraMap R A r₂) (algebraMap_mem _ r₁)
      (algebraMap_mem _ r₂))
    (algebraMap_left : ∀ (r) (x) (hx : x ∈ s), p (algebraMap R A r) x (algebraMap_mem _ r)
      (subset_adjoin hx))
    (algebraMap_right : ∀ (r) (x) (hx : x ∈ s), p x (algebraMap R A r) (subset_adjoin hx)
      (algebraMap_mem _ r))
    (add_left : ∀ x y z hx hy hz, p x z hx hz → p y z hy hz → p (x + y) z (add_mem hx hy) hz)
    (add_right : ∀ x y z hx hy hz, p x y hx hy → p x z hx hz → p x (y + z) hx (add_mem hy hz))
    (mul_left : ∀ x y z hx hy hz, p x z hx hz → p y z hy hz → p (x * y) z (mul_mem hx hy) hz)
    (mul_right : ∀ x y z hx hy hz, p x y hx hy → p x z hx hz → p x (y * z) hx (mul_mem hy hz))
    {x y : A} (hx : x ∈ adjoin R s) (hy : y ∈ adjoin R s) :
    p x y hx hy := by
  induction hy using adjoin_induction with
  | mem z hz => induction hx using adjoin_induction with
    | mem _ h => exact mem_mem _ _ h hz
    | algebraMap _ => exact algebraMap_left _ _ hz
    | mul _ _ _ _ h₁ h₂ => exact mul_left _ _ _ _ _ _ h₁ h₂
    | add _ _ _ _ h₁ h₂ => exact add_left _ _ _ _ _ _ h₁ h₂
  | algebraMap r =>
    induction hx using adjoin_induction with
    | mem _ h => exact algebraMap_right _ _ h
    | algebraMap _ => exact algebraMap_both _ _
    | mul _ _ _ _ h₁ h₂ => exact mul_left _ _ _ _ _ _ h₁ h₂
    | add _ _ _ _ h₁ h₂ => exact add_left _ _ _ _ _ _ h₁ h₂
  | mul _ _ _ _ h₁ h₂ => exact mul_right _ _ _ _ _ _ h₁ h₂
  | add _ _ _ _ h₁ h₂ => exact add_right _ _ _ _ _ _ h₁ h₂

@[simp]
/-
**Algebra.adjoin_adjoin_coe_preimage** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：adjoin_adjoin_coe_preimage {s : Set A} : adjoin R (((↑) : adjoin R s -> A)
 ⁻¹' s) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Algebra.eq_top_iff`：eq_top_iff {S : Subalgebra R A} : S = ⊤ ↔ forall x :
 A, x in S
· 使用定理 `Algebra.adjoin_induction`：adjoin_induction {p : (x : A) -> x in adjoin R
 s -> Prop} (mem : forall (x) (hx : x in s), p x (subset_adjoin hx)) (algebraMap
 : forall r, p…
· 使用定理 `Algebra.subset_adjoin`：subset_adjoin : s subseteq adjoin R s
· 使用定理 `Subalgebra.algebraMap_mem`：∀ {R : Type u} {A : Type v} [inst : CommSemir
ing R] [inst_1 : Semiring A] [inst_2 : Algebra R A] (S : Subalgebra R A)   (r : 
R), (algebraMap…
· 使用定理 `Subalgebra.add_mem`：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] 
[inst_1 : Semiring A] [inst_2 : Algebra R A] (S : Subalgebra R A)   {x y : A}, x
 ∈ S → y…
· 使用定理 `Subalgebra.mul_mem`：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] 
[inst_1 : Semiring A] [inst_2 : Algebra R A] (S : Subalgebra R A)   {x y : A}, x
 ∈ S → y…
-/
theorem adjoin_adjoin_coe_preimage {s : Set A} : adjoin R (((↑) : adjoin R s → A) ⁻¹' s) = ⊤ := by
  refine eq_top_iff.2 fun ⟨x, hx⟩ ↦
      adjoin_induction (fun a ha ↦ ?_) (fun r ↦ ?_) (fun _ _ _ _ ↦ ?_) (fun _ _ _ _ ↦ ?_) hx
  · exact subset_adjoin ha
  · exact Subalgebra.algebraMap_mem _ r
  · exact Subalgebra.add_mem _
  · exact Subalgebra.mul_mem _
/-
**Algebra.adjoin_union** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：adjoin_union (s t : Set A) : adjoin R (s union t) = adjoin R s ⊔ adjoin R 
t
参数：s t : Set A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_sup`：l_sup (gc : GaloisConnection l u) : l (a₁ ⊔ a₂) 
= l a₁ ⊔ l a₂
· 使用定理 `Algebra.gc`：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] [inst_1 
: Semiring A] [inst_2 : Algebra R A],   GaloisConnection (Algebra.adjoin R) SetL
…
-/
theorem adjoin_union (s t : Set A) : adjoin R (s ∪ t) = adjoin R s ⊔ adjoin R t :=
  (Algebra.gc : GaloisConnection _ ((↑) : Subalgebra R A → Set A)).l_sup

variable (R A)

@[simp]
/-
**Algebra.adjoin_empty** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：adjoin_empty : adjoin R (∅ : Set A) = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_bot`：∀ {α : Type u} {β : Type v} [inst : PartialOrder
 α] [inst_1 : Preorder β] [inst_2 : OrderBot α] [inst_3 : OrderBot β]   {u : α →
 β} {l : β →…
· 使用定理 `Algebra.gc`：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] [inst_1 
: Semiring A] [inst_2 : Algebra R A],   GaloisConnection (Algebra.adjoin R) SetL
…
-/
theorem adjoin_empty : adjoin R (∅ : Set A) = ⊥ := Algebra.gc.l_bot

@[simp]
/-
**Algebra.adjoin_univ** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：adjoin_univ : adjoin R (Set.univ : Set A) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisInsertion.l_top`：l_top [Preorder α] [PartialOrder β] [OrderTop α] 
[OrderTop β] (gi : GaloisInsertion l u) : l ⊤ = ⊤
-/
theorem adjoin_univ : adjoin R (Set.univ : Set A) = ⊤ := Algebra.gi.l_top

variable {R} in
@[simp]
/-
**Algebra.adjoin_singleton_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：adjoin_singleton_algebraMap (x : R) : R[algebraMap R A x] = ⊥
参数：x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `bot_unique`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ → a = ⊥
· 使用定理 `Algebra.adjoin_singleton_le`：adjoin_singleton_le {S : Subalgebra R A} {a
 : A} (H : a in S) : R[a] <= S
· 使用定理 `Subalgebra.algebraMap_mem`：∀ {R : Type u} {A : Type v} [inst : CommSemir
ing R] [inst_1 : Semiring A] [inst_2 : Algebra R A] (S : Subalgebra R A)   (r : 
R), (algebraMap…
-/
theorem adjoin_singleton_algebraMap (x : R) : R[algebraMap R A x] = ⊥ :=
  bot_unique <| adjoin_singleton_le <| Subalgebra.algebraMap_mem _ _

@[simp]
/-
**Algebra.adjoin_singleton_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：adjoin_singleton_natCast (n : Nat) : R[n : A] = ⊥
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_natCast`：map_natCast [FunLike F R S] [RingHomClass F R S] (f : F) : 
forall n : Nat, f (n : R) = n
· 使用定理 `Algebra.adjoin_singleton_algebraMap`：adjoin_singleton_algebraMap (x : R)
 : R[algebraMap R A x] = ⊥
-/
theorem adjoin_singleton_natCast (n : ℕ) : R[n : A] = ⊥ := by
  simpa using adjoin_singleton_algebraMap A (n : R)

@[simp]
/-
**Algebra.adjoin_singleton_zero** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：adjoin_singleton_zero : R[0 : A] = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.adjoin_singleton_natCast`：adjoin_singleton_natCast (n : Nat) : R
[n : A] = ⊥
-/
theorem adjoin_singleton_zero : R[0 : A] = ⊥ :=
  mod_cast adjoin_singleton_natCast R A 0

@[simp]
/-
**Algebra.adjoin_singleton_one** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：adjoin_singleton_one : R[1 : A]= ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.adjoin_singleton_natCast`：adjoin_singleton_natCast (n : Nat) : R
[n : A] = ⊥
-/
theorem adjoin_singleton_one : R[1 : A]= ⊥ :=
  mod_cast adjoin_singleton_natCast R A 1

variable {A} (s)

variable {R} in
@[simp]
/-
**Algebra.adjoin_insert_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：adjoin_insert_algebraMap (x : R) (s : Set A) : adjoin R (insert (algebraMa
p R A x) s) = adjoin R s
参数：x : R；s : Set A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.insert_eq`：insert_eq (x : α) (s : Set α) : insert x s = ({x} : Set α
) union s
· 使用定理 `Algebra.adjoin_union`：adjoin_union (s t : Set A) : adjoin R (s union t) 
= adjoin R s ⊔ adjoin R t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Algebra.adjoin_singleton_algebraMap`：adjoin_singleton_algebraMap (x : R)
 : R[algebraMap R A x] = ⊥
· 使用定理 `sup_of_le_right`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, a ≤
 b → a ⊔ b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem adjoin_insert_algebraMap (x : R) (s : Set A) :
    adjoin R (insert (algebraMap R A x) s) = adjoin R s := by
  rw [Set.insert_eq, adjoin_union]
  simp

@[simp]
/-
**Algebra.adjoin_insert_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：adjoin_insert_natCast (n : Nat) (s : Set A) : adjoin R (insert (n : A) s) 
= adjoin R s
参数：n : Nat；s : Set A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `algebraMap.coe_natCast`：coe_natCast (a : Nat) : (↑(a : R) : A) = a
· 使用定理 `Algebra.adjoin_insert_algebraMap`：adjoin_insert_algebraMap (x : R) (s : 
Set A) : adjoin R (insert (algebraMap R A x) s) = adjoin R s
-/
theorem adjoin_insert_natCast (n : ℕ) (s : Set A) : adjoin R (insert (n : A) s) = adjoin R s :=
  mod_cast adjoin_insert_algebraMap (n : R) s

@[simp]
/-
**Algebra.adjoin_insert_zero** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：adjoin_insert_zero (s : Set A) : adjoin R (insert 0 s) = adjoin R s
参数：s : Set A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.adjoin_insert_natCast`：adjoin_insert_natCast (n : Nat) (s : Set 
A) : adjoin R (insert (n : A) s) = adjoin R s
-/
theorem adjoin_insert_zero (s : Set A) : adjoin R (insert 0 s) = adjoin R s :=
  mod_cast adjoin_insert_natCast R 0 s

@[simp]
/-
**Algebra.adjoin_insert_one** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：adjoin_insert_one (s : Set A) : adjoin R (insert 1 s) = adjoin R s
参数：s : Set A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.adjoin_insert_natCast`：adjoin_insert_natCast (n : Nat) (s : Set 
A) : adjoin R (insert (n : A) s) = adjoin R s
-/
theorem adjoin_insert_one (s : Set A) : adjoin R (insert 1 s) = adjoin R s :=
  mod_cast adjoin_insert_natCast R 1 s
/-
**Algebra.adjoin_eq_span** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：adjoin_eq_span : Subalgebra.toSubmodule (adjoin R s) = span R (Submonoid.c
losure s)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subsemiring.mem_closure_iff_exists_list`：mem_closure_iff_exists_list {R}
 [Semiring R] {s : Set R} {x} : x in closure s ↔ exists L : List (List R), (fora
ll t in L, forall y in t, y i…
· 使用定理 `ZeroMemClass.zero_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst 
: Zero M} {inst_1 : SetLike S M} [self : ZeroMemClass S M] (s : S),   0 ∈ s
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `List.sum_cons`：∀ {α : Type u} [inst : Add α] [inst_1 : Zero α] {a : α} {
l : List α}, (a :: l).sum = a + l.sum
· 使用定理 `Submodule.add_mem`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [inst
_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodule R M) {x y 
: M}, x…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `List.forall_mem_cons`：∀ {α : Type u_1} {p : α → Prop} {a : α} {l : List 
α}, (∀ x ∈ a :: l, p x) ↔ p a ∧ ∀ x ∈ l, p x
· 使用定理 `Submonoid.one_mem'`：∀ {M : Type u_3} [inst : MulOneClass M] (self : Subm
onoid M), 1 ∈ self.carrier
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `List.prod_cons`：∀ {α : Type u} [inst : Mul α] [inst_1 : One α] {a : α} {
l : List α}, (a :: l).prod = a * l.prod
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `RingHom.map_mul`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} (f : α →+* β) (a b : α),   f (a * b) = f a * f b
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Submonoid.mul_mem`：∀ {M : Type u_1} [inst : MulOneClass M] (S : Submonoi
d M) {x y : M}, x ∈ S → y ∈ S → x * y ∈ S
· 使用定理 `Submonoid.subset_closure`：subset_closure : s subseteq closure s
· 使用引理 `mul_smul_comm`：mul_smul_comm [Mul β] [SMul α β] [SMulCommClass α β β] (s
 : α) (x y : β) : x * s • y = s • (x * y)
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
· 使用定理 `Submonoid.closure_le`：closure_le : closure s <= S ↔ s subseteq S
· 使用定理 `Algebra.subset_adjoin`：subset_adjoin : s subseteq adjoin R s
-/
theorem adjoin_eq_span : Subalgebra.toSubmodule (adjoin R s) = span R (Submonoid.closure s) := by
  apply le_antisymm
  · intro r hr
    rcases Subsemiring.mem_closure_iff_exists_list.1 hr with ⟨L, HL, rfl⟩
    clear hr
    induction L with
    | nil => exact zero_mem _
    | cons hd tl ih => ?_
    rw [List.forall_mem_cons] at HL
    rw [List.map_cons, List.sum_cons]
    refine Submodule.add_mem _ ?_ (ih HL.2)
    replace HL := HL.1
    clear ih tl
    suffices ∃ (z r : _) (_hr : r ∈ Submonoid.closure s), z • r = List.prod hd by
      rcases this with ⟨z, r, hr, hzr⟩
      rw [← hzr]
      exact smul_mem _ _ (subset_span hr)
    induction hd with
    | nil => exact ⟨1, 1, (Submonoid.closure s).one_mem', one_smul _ _⟩
    | cons hd tl ih => ?_
    rw [List.forall_mem_cons] at HL
    rcases ih HL.2 with ⟨z, r, hr, hzr⟩
    rw [List.prod_cons, ← hzr]
    rcases HL.1 with (⟨hd, rfl⟩ | hs)
    · refine ⟨hd * z, r, hr, ?_⟩
      rw [Algebra.smul_def, Algebra.smul_def, (algebraMap _ _).map_mul, _root_.mul_assoc]
    · exact
        ⟨z, hd * r, Submonoid.mul_mem _ (Submonoid.subset_closure hs) hr,
          (mul_smul_comm _ _ _).symm⟩
  refine span_le.2 ?_
  change Submonoid.closure s ≤ (adjoin R s).toSubsemiring.toSubmonoid
  exact Submonoid.closure_le.2 subset_adjoin
/-
**Algebra.span_le_adjoin** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：span_le_adjoin (s : Set A) : span R s <= Subalgebra.toSubmodule (adjoin R 
s)
参数：s : Set A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
· 使用定理 `Algebra.subset_adjoin`：subset_adjoin : s subseteq adjoin R s
-/
theorem span_le_adjoin (s : Set A) : span R s ≤ Subalgebra.toSubmodule (adjoin R s) :=
  span_le.mpr subset_adjoin
/-
**Algebra.adjoin_toSubmodule_le** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：adjoin_toSubmodule_le {s : Set A} {t : Submodule R A} : Subalgebra.toSubmo
dule (adjoin R s) <= t ↔ ↑(Submonoid.closure s) subseteq (t : Set A)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.adjoin_eq_span`：adjoin_eq_span : Subalgebra.toSubmodule (adjoin 
R s) = span R (Submonoid.closure s)
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem adjoin_toSubmodule_le {s : Set A} {t : Submodule R A} :
    Subalgebra.toSubmodule (adjoin R s) ≤ t ↔ ↑(Submonoid.closure s) ⊆ (t : Set A) := by
  rw [adjoin_eq_span, span_le]
/-
**Algebra.adjoin_eq_span_of_subset** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：adjoin_eq_span_of_subset {s : Set A} (hs : ↑(Submonoid.closure s) subseteq
 (span R s : Set A)) : Subalgebra.toSubmodule (adjoin R s) = span R s
参数：hs : ↑(Submonoid.closure s) subseteq (span R s : Set A)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Algebra.adjoin_toSubmodule_le`：adjoin_toSubmodule_le {s : Set A} {t : Su
bmodule R A} : Subalgebra.toSubmodule (adjoin R s) <= t ↔ ↑(Submonoid.closure s)
 subseteq (t : Set …
· 使用定理 `Algebra.span_le_adjoin`：span_le_adjoin (s : Set A) : span R s <= Subalge
bra.toSubmodule (adjoin R s)
-/
theorem adjoin_eq_span_of_subset {s : Set A} (hs : ↑(Submonoid.closure s) ⊆ (span R s : Set A)) :
    Subalgebra.toSubmodule (adjoin R s) = span R s :=
  le_antisymm ((adjoin_toSubmodule_le R).mpr hs) (span_le_adjoin R s)

@[simp]
/-
**Algebra.adjoin_span** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：adjoin_span {s : Set A} : adjoin R (Submodule.span R s : Set A) = adjoin R
 s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Algebra.adjoin_le`：adjoin_le {S : Subalgebra R A} (H : s subseteq S) : a
djoin R s <= S
· 使用定理 `Algebra.span_le_adjoin`：span_le_adjoin (s : Set A) : span R s <= Subalge
bra.toSubmodule (adjoin R s)
· 使用定理 `Algebra.adjoin_mono`：adjoin_mono (H : s subseteq t) : adjoin R s <= adjo
in R t
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
-/
theorem adjoin_span {s : Set A} : adjoin R (Submodule.span R s : Set A) = adjoin R s :=
  le_antisymm (adjoin_le (span_le_adjoin _ _)) (adjoin_mono Submodule.subset_span)
/-
**Algebra.adjoin_image** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：adjoin_image (f : A ->ₐ[R] B) (s : Set A) : adjoin R (f '' s) = (adjoin R 
s).map f
参数：f : A ->ₐ[R] B；s : Set A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_forall_ge_iff`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α},
 (∀ (c : α), a ≤ c ↔ b ≤ c) → a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subalgebra.coe_comap`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : C
ommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_3 : Semiring
 B] [inst_…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem adjoin_image (f : A →ₐ[R] B) (s : Set A) : adjoin R (f '' s) = (adjoin R s).map f :=
  eq_of_forall_ge_iff fun t ↦ by simp [Subalgebra.map_le, adjoin_le_iff]

@[simp]
/-
**Algebra.adjoin_insert_adjoin** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：adjoin_insert_adjoin (x : A) : adjoin R (insert x ↑(adjoin R s)) = adjoin 
R (insert x s)
参数：x : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_forall_ge_iff`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α},
 (∀ (c : α), a ≤ c ↔ b ≤ c) → a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem adjoin_insert_adjoin (x : A) : adjoin R (insert x ↑(adjoin R s)) = adjoin R (insert x s) :=
  eq_of_forall_ge_iff fun t ↦ by simp [adjoin_le_iff, Set.insert_subset_iff]
/-
**Algebra.mem_adjoin_of_map_mul** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：mem_adjoin_of_map_mul {s} {x : A} {f : A ->ₗ[R] B} (hf : forall a₁ a₂, f (
a₁ * a₂) = f a₁ * f a₂) (h : x in adjoin R s) : f x in adjoin R (f '' (s union {
1}))
参数：hf : forall a₁ a₂, f (a₁ * a₂) = f a₁ * f a₂；h : x in adjoin R s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.adjoin_induction`：adjoin_induction {p : (x : A) -> x in adjoin R
 s -> Prop} (mem : forall (x) (hx : x in s), p x (subset_adjoin hx)) (algebraMap
 : forall r, p…
· 使用定理 `Algebra.subset_adjoin`：subset_adjoin : s subseteq adjoin R s
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.algebraMap_eq_smul_one`：algebraMap_eq_smul_one (r : R) : algebra
Map R A r = r • (1 : A)
· 使用定理 `LinearMap.map_smul`：∀ {R : Type u_1} {M : Type u_8} {M₂ : Type u_10} [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid M₂] [inst_
3 : _roo…
· 使用定理 `Subalgebra.smul_mem`：smul_mem {x : A} (hx : x in S) (r : R) : r • x in S
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.union_singleton`：union_singleton : s union {a} = insert a s
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subalgebra.add_mem`：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] 
[inst_1 : Semiring A] [inst_2 : Algebra R A] (S : Subalgebra R A)   {x y : A}, x
 ∈ S → y…
· 使用定理 `Subalgebra.mul_mem`：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] 
[inst_1 : Semiring A] [inst_2 : Algebra R A] (S : Subalgebra R A)   {x y : A}, x
 ∈ S → y…
-/
theorem mem_adjoin_of_map_mul {s} {x : A} {f : A →ₗ[R] B} (hf : ∀ a₁ a₂, f (a₁ * a₂) = f a₁ * f a₂)
    (h : x ∈ adjoin R s) : f x ∈ adjoin R (f '' (s ∪ {1})) := by
  induction h using adjoin_induction with
  | mem a ha => exact subset_adjoin ⟨a, ⟨Set.subset_union_left ha, rfl⟩⟩
  | algebraMap r =>
    have : f 1 ∈ adjoin R (f '' (s ∪ {1})) :=
      subset_adjoin ⟨1, ⟨Set.subset_union_right <| Set.mem_singleton 1, rfl⟩⟩
    convert! Subalgebra.smul_mem (adjoin R (f '' (s ∪ { 1 }))) this r
    rw [algebraMap_eq_smul_one]
    exact f.map_smul _ _
  | add y z _ _ hy hz => simpa [hy, hz] using Subalgebra.add_mem _ hy hz
  | mul y z _ _ hy hz => simpa [hf, hy, hz] using Subalgebra.mul_mem _ hy hz
/-
**Algebra.adjoin_le_centralizer_centralizer** 是 Mathlib 中的一个引理，位于命名空间 `Algebra`。
形式化陈述：adjoin_le_centralizer_centralizer (s : Set A) : adjoin R s <= Subalgebra.c
entralizer R (Subalgebra.centralizer R s)
参数：s : Set A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.adjoin_le`：adjoin_le {S : Subalgebra R A} (H : s subseteq S) : a
djoin R s <= S
· 使用引理 `Set.subset_centralizer_centralizer`：subset_centralizer_centralizer : S s
ubseteq S.centralizer.centralizer
-/
lemma adjoin_le_centralizer_centralizer (s : Set A) :
    adjoin R s ≤ Subalgebra.centralizer R (Subalgebra.centralizer R s) :=
  adjoin_le Set.subset_centralizer_centralizer

/-- If all elements of `s : Set A` commute pairwise, then `adjoin R s` is commutative. -/
/-
**Algebra.isMulCommutative_adjoin** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：isMulCommutative_adjoin {s : Set A} (hcomm : forall x in s, forall y in s,
 x * y = y * x) : IsMulCommutative (adjoin R s)
参数：hcomm : forall x in s, forall y in s, x * y = y * x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Algebra.adjoin_le_centralizer_centralizer`：adjoin_le_centralizer_central
izer (s : Set A) : adjoin R s <= Subalgebra.centralizer R (Subalgebra.centralize
r R s)
· 使用定理 `IsMulCommutative.of_setLike_mul_comm`：∀ {S : Type u_3} {M : Type u_4} [i
nst : SetLike S M] [inst_1 : Mul M] [inst_2 : MulMemClass S M] {s : S},   (∀ a ∈
 s, ∀ b ∈ s, a * b = b * a…
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `SubsemiringClass.toSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Type 
u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringClas
s S R], SubmonoidClass …
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A
· 使用引理 `Set.centralizer_centralizer_comm_of_comm`：centralizer_centralizer_comm_o
f_comm (h_comm : forall x in S, forall y in S, x * y = y * x) : forall x in S.ce
ntralizer.centralizer, forall …

--- 原说明 ---
If all elements of `s : Set A` commute pairwise, then `adjoin R s` is commutativ
e.
-/
theorem isMulCommutative_adjoin {s : Set A} (hcomm : ∀ x ∈ s, ∀ y ∈ s, x * y = y * x) :
    IsMulCommutative (adjoin R s) :=
  have := adjoin_le_centralizer_centralizer R s
  .of_setLike_mul_comm fun _ h₁ _ h₂ ↦
    Set.centralizer_centralizer_comm_of_comm hcomm _ (this h₁) _ (this h₂)
/-
**Algebra.isMulCommutative_adjoin_singleton** 是 Mathlib 中的一个实例，位于命名空间 `Algebra`。
形式化陈述：isMulCommutative_adjoin_singleton (x : A) : IsMulCommutative (adjoin R ({x
} : Set A))
参数：x : A。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.isMulCommutative_adjoin`：isMulCommutative_adjoin {s : Set A} (hc
omm : forall x in s, forall y in s, x * y = y * x) : IsMulCommutative (adjoin R 
s)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance isMulCommutative_adjoin_singleton (x : A) :
    IsMulCommutative (adjoin R ({x} : Set A)) :=
  isMulCommutative_adjoin R (by simp)

open scoped IsMulCommutative in
/-- If all elements of `s : Set A` commute pairwise, then `adjoin R s` is a non-unital commutative
semiring.

See note [reducible non-instances]. -/
@[deprecated isMulCommutative_adjoin (since := "2026-03-11")]
/-
**Algebra.adjoinCommSemiringOfComm** 是 Mathlib 中的一个缩写定义，位于命名空间 `Algebra`。
形式化陈述：adjoinCommSemiringOfComm {s : Set A} (hcomm : forall a in s, forall b in s
, a * b = b * a) : CommSemiring (adjoin R s)
参数：hcomm : forall a in s, forall b in s, a * b = b * a。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.isMulCommutative_adjoin`：isMulCommutative_adjoin {s : Set A} (hc
omm : forall x in s, forall y in s, x * y = y * x) : IsMulCommutative (adjoin R 
s)

--- 原说明 ---
If all elements of `s : Set A` commute pairwise, then `adjoin R s` is a non-unit
al commutative
semiring.

See note [reducible non-instances].
-/
abbrev adjoinCommSemiringOfComm {s : Set A} (hcomm : ∀ a ∈ s, ∀ b ∈ s, a * b = b * a) :
    CommSemiring (adjoin R s) :=
  have := isMulCommutative_adjoin R hcomm
  inferInstance
/-
**Algebra.instIsMulCommutative_adjoin** 是 Mathlib 中的一个实例，位于命名空间 `Algebra`。
形式化陈述：instIsMulCommutative_adjoin {S : Type*} [SetLike S A] [MulMemClass S A] (s
 : S) [IsMulCommutative s] : IsMulCommutative (adjoin R (s : Set A))
参数：s : S。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.isMulCommutative_adjoin`：isMulCommutative_adjoin {s : Set A} (hc
omm : forall x in s, forall y in s, x * y = y * x) : IsMulCommutative (adjoin R 
s)
· 使用引理 `setLike_mul_comm`：setLike_mul_comm {S M : Type*} [SetLike S M] [Mul M] [
MulMemClass S M] {s : S} [IsMulCommutative s] ⦃a b : M⦄ (ha : a in s) (hb : b in
 s) : …
-/
instance instIsMulCommutative_adjoin {S : Type*} [SetLike S A] [MulMemClass S A] (s : S)
    [IsMulCommutative s] : IsMulCommutative (adjoin R (s : Set A)) :=
  isMulCommutative_adjoin R fun _ h₁ _ h₂ => setLike_mul_comm h₁ h₂

variable {R}
/-
**Algebra.commute_of_mem_adjoin_of_forall_mem_commute** 是 Mathlib 中的一个引理，位于命名空间 
`Algebra`。
形式化陈述：commute_of_mem_adjoin_of_forall_mem_commute {a b : A} {s : Set A} (hb : b 
in adjoin R s) (h : forall b in s, Commute a b) : Commute a b
参数：hb : b in adjoin R s；h : forall b in s, Commute a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.adjoin_induction`：adjoin_induction {p : (x : A) -> x in adjoin R
 s -> Prop} (mem : forall (x) (hx : x in s), p x (subset_adjoin hx)) (algebraMap
 : forall r, p…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.commutes`：commutes (r : R) (x : A) : algebraMap R A r * x = x * 
algebraMap R A r
· 使用定理 `Commute.add_right`：add_right [Distrib R] {a b c : R} : Commute a b -> Co
mmute a c -> Commute a (b + c)
· 使用定理 `Commute.mul_right`：mul_right (hab : Commute a b) (hac : Commute a c) : C
ommute a (b * c)
-/
lemma commute_of_mem_adjoin_of_forall_mem_commute {a b : A} {s : Set A}
    (hb : b ∈ adjoin R s) (h : ∀ b ∈ s, Commute a b) :
    Commute a b := by
  induction hb using adjoin_induction with
  | mem x hx => exact h x hx
  | algebraMap r => exact commutes r a |>.symm
  | add y z _ _ hy hz => exact hy.add_right hz
  | mul y z _ _ hy hz => exact hy.mul_right hz
/-
**Algebra.commute_of_mem_adjoin_singleton_of_commute** 是 Mathlib 中的一个引理，位于命名空间 `
Algebra`。
形式化陈述：commute_of_mem_adjoin_singleton_of_commute {a b c : A} (hc : c in R[b]) (h
 : Commute a b) : Commute a c
参数：hc : c in R[b]；h : Commute a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Algebra.commute_of_mem_adjoin_of_forall_mem_commute`：commute_of_mem_adjo
in_of_forall_mem_commute {a b : A} {s : Set A} (hb : b in adjoin R s) (h : foral
l b in s, Commute a b) : Commute a b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
lemma commute_of_mem_adjoin_singleton_of_commute {a b c : A}
    (hc : c ∈ R[b]) (h : Commute a b) :
    Commute a c :=
  commute_of_mem_adjoin_of_forall_mem_commute hc <| by simpa
/-
**Algebra.commute_of_mem_adjoin_self** 是 Mathlib 中的一个引理，位于命名空间 `Algebra`。
形式化陈述：commute_of_mem_adjoin_self {a b : A} (hb : b in R[a]) : Commute a b
参数：hb : b in R[a]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Algebra.commute_of_mem_adjoin_singleton_of_commute`：commute_of_mem_adjoi
n_singleton_of_commute {a b c : A} (hc : c in R[b]) (h : Commute a b) : Commute 
a c
-/
lemma commute_of_mem_adjoin_self {a b : A} (hb : b ∈ R[a]) :
    Commute a b :=
  commute_of_mem_adjoin_singleton_of_commute hb rfl

variable (R)

@[simp]
/-
**Algebra.self_mem_adjoin_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：self_mem_adjoin_singleton (x : A) : x in R[x]
参数：x : A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.subset_adjoin`：subset_adjoin : s subseteq adjoin R s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_singleton_iff`：mem_singleton_iff {a b : α} : a in ({b} : Set α) 
↔ a = b
-/
theorem self_mem_adjoin_singleton (x : A) : x ∈ R[x] :=
  Algebra.subset_adjoin (Set.mem_singleton_iff.mpr rfl)

end Semiring

section CommSemiring

variable [CommSemiring R] [CommSemiring A]
variable [Algebra R A] {s t : Set A}
variable (R s t)

/-
**Algebra.adjoin_union_coe_submodule** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：adjoin_union_coe_submodule : Subalgebra.toSubmodule (adjoin R (s union t))
 = Subalgebra.toSubmodule (adjoin R s) * Subalgebra.toSubmodule (adjoin R t)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.adjoin_eq_span`：adjoin_eq_span : Subalgebra.toSubmodule (adjoin 
R s) = span R (Submonoid.closure s)
· 使用定理 `Submodule.span_mul_span`：span_mul_span : span R S * span R T = span R (S
 * T)
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Submonoid.closure_union`：closure_union (s t : Set M) : closure (s union 
t) = closure s ⊔ closure t
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem adjoin_union_coe_submodule :
    Subalgebra.toSubmodule (adjoin R (s ∪ t)) =
      Subalgebra.toSubmodule (adjoin R s) * Subalgebra.toSubmodule (adjoin R t) := by
  rw [adjoin_eq_span, adjoin_eq_span, adjoin_eq_span, span_mul_span]
  congr 1 with z; simp [Submonoid.closure_union, Submonoid.mem_sup, Set.mem_mul]

end CommSemiring

section Ring

variable [CommRing R] [Ring A]
variable [Algebra R A] {s t : Set A}

@[simp]
/-
**Algebra.adjoin_singleton_intCast** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：adjoin_singleton_intCast (n : Int) : R[n : A] = ⊥
参数：n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_intCast`：map_intCast [FunLike F α β] [RingHomClass F α β] (f : F) (n
 : Int) : f n = n
· 使用定理 `Algebra.adjoin_singleton_algebraMap`：adjoin_singleton_algebraMap (x : R)
 : R[algebraMap R A x] = ⊥
-/
theorem adjoin_singleton_intCast (n : ℤ) : R[n : A] = ⊥ := by
  simpa using adjoin_singleton_algebraMap A (n : R)

@[simp]
/-
**Algebra.adjoin_insert_intCast** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：adjoin_insert_intCast (n : Int) (s : Set A) : adjoin R (insert (n : A) s) 
= adjoin R s
参数：n : Int；s : Set A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_intCast`：map_intCast [FunLike F α β] [RingHomClass F α β] (f : F) (n
 : Int) : f n = n
· 使用定理 `Algebra.adjoin_insert_algebraMap`：adjoin_insert_algebraMap (x : R) (s : 
Set A) : adjoin R (insert (algebraMap R A x) s) = adjoin R s
-/
theorem adjoin_insert_intCast (n : ℤ) (s : Set A) : adjoin R (insert (n : A) s) = adjoin R s := by
  simpa using adjoin_insert_algebraMap (n : R) s
/-
**Algebra.adjoin_eq_ring_closure** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：adjoin_eq_ring_closure (s : Set A) : (adjoin R s).toSubring = Subring.clos
ure (Set.range (algebraMap R A) union s)
参数：s : Set A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subring.closure_eq_of_le`：closure_eq_of_le {s : Set R} {t : Subring R} (
h₁ : s subseteq t) (h₂ : t <= closure s) : closure s = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Subsemiring.closure_induction`：closure_induction {s : Set R} {p : (x : R
) -> x in closure s -> Prop} (mem : forall (x) (hx : x in s), p x (subset_closur
e hx)) (zero : p 0 …
· 使用定理 `Subring.subset_closure`：subset_closure {s : Set R} : s subseteq closure 
s
· 使用定理 `Subring.zero_mem`：∀ {R : Type u} [inst : NonAssocRing R] (s : Subring R)
, 0 ∈ s
· 使用定理 `Subring.one_mem`：∀ {R : Type u} [inst : NonAssocRing R] (s : Subring R),
 1 ∈ s
· 使用定理 `Subring.add_mem`：∀ {R : Type u} [inst : NonAssocRing R] (s : Subring R) 
{x y : R}, x ∈ s → y ∈ s → x + y ∈ s
· 使用定理 `Subring.mul_mem`：∀ {R : Type u} [inst : NonAssocRing R] (s : Subring R) 
{x y : R}, x ∈ s → y ∈ s → x * y ∈ s
-/
theorem adjoin_eq_ring_closure (s : Set A) :
    (adjoin R s).toSubring = Subring.closure (Set.range (algebraMap R A) ∪ s) :=
  .symm <| Subring.closure_eq_of_le (by simp [adjoin]) fun x hx =>
    Subsemiring.closure_induction Subring.subset_closure (Subring.zero_mem _) (Subring.one_mem _)
      (fun _ _ _ _ => Subring.add_mem _) (fun _ _ _ _ => Subring.mul_mem _) hx
/-
**Algebra.mem_adjoin_iff** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：mem_adjoin_iff {s : Set A} {x : A} : x in adjoin R s ↔ x in Subring.closur
e (Set.range (algebraMap R A) union s)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subalgebra.mem_toSubring`：mem_toSubring {R : Type u} {A : Type v} [CommR
ing R] [Ring A] [Algebra R A] {S : Subalgebra R A} {x} : x in S.toSubring ↔ x in
 S
· 使用定理 `Algebra.adjoin_eq_ring_closure`：adjoin_eq_ring_closure (s : Set A) : (ad
join R s).toSubring = Subring.closure (Set.range (algebraMap R A) union s)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_adjoin_iff {s : Set A} {x : A} :
    x ∈ adjoin R s ↔ x ∈ Subring.closure (Set.range (algebraMap R A) ∪ s) := by
  rw [← Subalgebra.mem_toSubring, adjoin_eq_ring_closure]

variable (R)

open scoped IsMulCommutative in
/-- If all elements of `s : Set A` commute pairwise, then `adjoin R s` is a commutative
ring. -/
@[deprecated isMulCommutative_adjoin (since := "2026-03-11")]
/-
**Algebra.adjoinCommRingOfComm** 是 Mathlib 中的一个缩写定义，位于命名空间 `Algebra`。
形式化陈述：adjoinCommRingOfComm {s : Set A} (hcomm : forall a in s, forall b in s, a 
* b = b * a) : CommRing (adjoin R s)
参数：hcomm : forall a in s, forall b in s, a * b = b * a。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If all elements of `s : Set A` commute pairwise, then `adjoin R s` is a commutat
ive
ring.
-/
abbrev adjoinCommRingOfComm {s : Set A} (hcomm : ∀ a ∈ s, ∀ b ∈ s, a * b = b * a) :
    CommRing (adjoin R s) :=
  have := isMulCommutative_adjoin R hcomm
  inferInstance

end Ring

end Algebra

open Algebra Subalgebra

namespace AlgHom

variable [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]

/-
**AlgHom.map_adjoin** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：map_adjoin (φ : A ->ₐ[R] B) (s : Set A) : (adjoin R s).map φ = adjoin R (φ
 '' s)
参数：φ : A ->ₐ[R] B；s : Set A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.adjoin_image`：adjoin_image (f : A ->ₐ[R] B) (s : Set A) : adjoin
 R (f '' s) = (adjoin R s).map f
-/
theorem map_adjoin (φ : A →ₐ[R] B) (s : Set A) : (adjoin R s).map φ = adjoin R (φ '' s) :=
  (adjoin_image _ _ _).symm

@[simp]
/-
**AlgHom.map_adjoin_singleton** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：map_adjoin_singleton (e : A ->ₐ[R] B) (x : A) : (R[x]).map e = R[e x]
参数：e : A ->ₐ[R] B；x : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgHom.map_adjoin`：map_adjoin (φ : A ->ₐ[R] B) (s : Set A) : (adjoin R s
).map φ = adjoin R (φ '' s)
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
-/
theorem map_adjoin_singleton (e : A →ₐ[R] B) (x : A) :
    (R[x]).map e = R[e x] := by
  rw [map_adjoin, Set.image_singleton]
/-
**AlgHom.adjoin_le_equalizer** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：adjoin_le_equalizer (φ₁ φ₂ : A ->ₐ[R] B) {s : Set A} (h : s.EqOn φ₁ φ₂) : 
adjoin R s <= equalizer φ₁ φ₂
参数：φ₁ φ₂ : A ->ₐ[R] B；h : s.EqOn φ₁ φ₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.adjoin_le`：adjoin_le {S : Subalgebra R A} (H : s subseteq S) : a
djoin R s <= S
-/
theorem adjoin_le_equalizer (φ₁ φ₂ : A →ₐ[R] B) {s : Set A} (h : s.EqOn φ₁ φ₂) :
    adjoin R s ≤ equalizer φ₁ φ₂ :=
  adjoin_le h
/-
**AlgHom.ext_of_adjoin_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：ext_of_adjoin_eq_top {s : Set A} (h : adjoin R s = ⊤) ⦃φ₁ φ₂ : A ->ₐ[R] B⦄
 (hs : s.EqOn φ₁ φ₂) : φ₁ = φ₂
参数：h : adjoin R s = ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `AlgHom.adjoin_le_equalizer`：adjoin_le_equalizer (φ₁ φ₂ : A ->ₐ[R] B) {s 
: Set A} (h : s.EqOn φ₁ φ₂) : adjoin R s <= equalizer φ₁ φ₂
· 使用定理 `trivial`：True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem ext_of_adjoin_eq_top {s : Set A} (h : adjoin R s = ⊤) ⦃φ₁ φ₂ : A →ₐ[R] B⦄
    (hs : s.EqOn φ₁ φ₂) : φ₁ = φ₂ :=
  ext fun _x => adjoin_le_equalizer φ₁ φ₂ hs <| h.symm ▸ trivial

/-- Two algebra morphisms are equal on `Algebra.span s` iff they are equal on `s`. -/
/-
**AlgHom.eqOn_adjoin_iff** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：eqOn_adjoin_iff {φ ψ : A ->ₐ[R] B} {s : Set A} : Set.EqOn φ ψ (adjoin R s)
 ↔ Set.EqOn φ ψ s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Two algebra morphisms are equal on `Algebra.span s` iff they are equal on `s`.
-/
theorem eqOn_adjoin_iff {φ ψ : A →ₐ[R] B} {s : Set A} :
    Set.EqOn φ ψ (adjoin R s) ↔ Set.EqOn φ ψ s := by
  have (S : Set A) : S ≤ equalizer φ ψ ↔ Set.EqOn φ ψ S := Iff.rfl
  simp only [← this, SetLike.coe_subset_coe, adjoin_le_iff]
/-
**AlgHom.adjoin_ext** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：adjoin_ext {s : Set A} ⦃φ₁ φ₂ : adjoin R s ->ₐ[R] B⦄ (h : forall x hx, φ₁ 
⟨x, subset_adjoin hx⟩ = φ₂ ⟨x, subset_adjoin hx⟩) : φ₁ = φ₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.subset_adjoin`：subset_adjoin : s subseteq adjoin R s
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `Algebra.adjoin_induction`：adjoin_induction {p : (x : A) -> x in adjoin R
 s -> Prop} (mem : forall (x) (hx : x in s), p x (subset_adjoin hx)) (algebraMap
 : forall r, p…
· 使用定理 `algebraMap_mem`：∀ {S : Type u_1} {R : Type u_2} {A : Type u_3} [inst : C
ommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_3 : SetLike 
S A]…
· 使用定理 `AddSubmonoidWithOneClass.toOneMemClass`：∀ {S : Type u_1} {R : outParam (
Type u_2)} {inst : AddMonoidWithOne R} {inst_1 : SetLike S R}   [self : AddSubmo
noidWithOneClass S R], OneMe…
· 使用定理 `SubsemiringClass.addSubmonoidWithOneClass`：∀ (S : Type u_1) (R : Type u)
 {x : NonAssocSemiring R} [inst : SetLike S R] [h : SubsemiringClass S R],   Add
SubmonoidWithOneClass S R
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A
· 使用定理 `AlgHom.commutes`：commutes (r : R) : φ (algebraMap R A r) = algebraMap R 
B r
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
· 使用定理 `SubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Ty
pe u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringC
lass S R], AddSubmonoidCla…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `SubsemiringClass.toSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Type 
u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringClas
s S R], SubmonoidClass …
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
-/
theorem adjoin_ext {s : Set A} ⦃φ₁ φ₂ : adjoin R s →ₐ[R] B⦄
    (h : ∀ x hx, φ₁ ⟨x, subset_adjoin hx⟩ = φ₂ ⟨x, subset_adjoin hx⟩) : φ₁ = φ₂ :=
  ext fun ⟨x, hx⟩ ↦ adjoin_induction h (fun _ ↦ φ₂.commutes _ ▸ φ₁.commutes _)
    (fun _ _ _ _ h₁ h₂ ↦ by convert! congr_arg₂ (· + ·) h₁ h₂ <;> rw [← map_add] <;> rfl)
    (fun _ _ _ _ h₁ h₂ ↦ by convert! congr_arg₂ (· * ·) h₁ h₂ <;> rw [← map_mul] <;> rfl) hx
/-
**AlgHom.ext_of_eq_adjoin** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：ext_of_eq_adjoin {S : Subalgebra R A} {s : Set A} (hS : S = adjoin R s) ⦃φ
₁ φ₂ : S ->ₐ[R] B⦄ (h : forall x hx, φ₁ ⟨x, hS.ge (subset_adjoin hx)⟩ = φ₂ ⟨x, h
S.ge (subset_adjoin hx)⟩) : φ₁ = φ₂
参数：hS : S = adjoin R s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Algebra.subset_adjoin`：subset_adjoin : s subseteq adjoin R s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgHom.adjoin_ext`：adjoin_ext {s : Set A} ⦃φ₁ φ₂ : adjoin R s ->ₐ[R] B⦄ 
(h : forall x hx, φ₁ ⟨x, subset_adjoin hx⟩ = φ₂ ⟨x, subset_adjoin hx⟩) : φ₁ = φ₂
-/
theorem ext_of_eq_adjoin {S : Subalgebra R A} {s : Set A} (hS : S = adjoin R s) ⦃φ₁ φ₂ : S →ₐ[R] B⦄
    (h : ∀ x hx, φ₁ ⟨x, hS.ge (subset_adjoin hx)⟩ = φ₂ ⟨x, hS.ge (subset_adjoin hx)⟩) :
    φ₁ = φ₂ := by
  subst hS; exact adjoin_ext h
/-
**AlgHom._root_.Algebra.forall_mem_adjoin_smul_eq_self_iff** 是 Mathlib 中的一个定理，位于
命名空间 `AlgHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Algebra.forall_mem_adjoin_smul_eq_self_iff (S : Set A) {M : Type*} [Monoid M]
    [MulSemiringAction M A] [SMulCommClass M R A] (m : M) :
    (∀ x ∈ adjoin R S, m • x = x) ↔ (∀ x ∈ S, m • x = x) :=
  AlgHom.eqOn_adjoin_iff (φ := MulSemiringAction.toAlgHom R A m) (ψ := .id R A)

end AlgHom

section NatInt

/-
**Algebra.adjoin_nat** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Algebra.adjoin_nat {R : Type*} [Semiring R] (s : Set R) : adjoin Nat s = s
ubalgebraOfSubsemiring (Subsemiring.closure s)
参数：s : Set R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Algebra.adjoin_le`：adjoin_le {S : Subalgebra R A} (H : s subseteq S) : a
djoin R s <= S
· 使用定理 `Subsemiring.subset_closure`：subset_closure {s : Set R} : s subseteq clos
ure s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subsemiring.closure_le`：closure_le {s : Set R} {t : Subsemiring R} : clo
sure s <= t ↔ s subseteq t
· 使用定理 `Algebra.subset_adjoin`：subset_adjoin : s subseteq adjoin R s
-/
theorem Algebra.adjoin_nat {R : Type*} [Semiring R] (s : Set R) :
    adjoin ℕ s = subalgebraOfSubsemiring (Subsemiring.closure s) :=
  le_antisymm (adjoin_le Subsemiring.subset_closure)
    (Subsemiring.closure_le.2 subset_adjoin : Subsemiring.closure s ≤ (adjoin ℕ s).toSubsemiring)
/-
**Algebra.adjoin_int** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Algebra.adjoin_int {R : Type*} [Ring R] (s : Set R) : adjoin Int s = subal
gebraOfSubring (Subring.closure s)
参数：s : Set R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Algebra.adjoin_le`：adjoin_le {S : Subalgebra R A} (H : s subseteq S) : a
djoin R s <= S
· 使用定理 `Subring.subset_closure`：subset_closure {s : Set R} : s subseteq closure 
s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subring.closure_le`：closure_le {s : Set R} {t : Subring R} : closure s <
= t ↔ s subseteq t
· 使用定理 `Algebra.subset_adjoin`：subset_adjoin : s subseteq adjoin R s
-/
theorem Algebra.adjoin_int {R : Type*} [Ring R] (s : Set R) :
    adjoin ℤ s = subalgebraOfSubring (Subring.closure s) :=
  le_antisymm (adjoin_le Subring.subset_closure)
    (Subring.closure_le.2 subset_adjoin : Subring.closure s ≤ (adjoin ℤ s).toSubring)

/-- The `ℕ`-algebra equivalence between `Subsemiring.closure s` and `Algebra.adjoin ℕ s` given
by the identity map. -/
/-
**Subsemiring.closureEquivAdjoinNat** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Subsemiring.closureEquivAdjoinNat {R : Type*} [Semiring R] (s : Set R) : S
ubsemiring.closure s ≃ₐ[Nat] Algebra.adjoin Nat s
参数：s : Set R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `ℕ`-algebra equivalence between `Subsemiring.closure s` and `Algebra.adjoin 
ℕ s` given
by the identity map.
-/
def Subsemiring.closureEquivAdjoinNat {R : Type*} [Semiring R] (s : Set R) :
    Subsemiring.closure s ≃ₐ[ℕ] Algebra.adjoin ℕ s :=
  Subalgebra.equivOfEq (subalgebraOfSubsemiring <| Subsemiring.closure s) _ (adjoin_nat s).symm

/-- The `ℤ`-algebra equivalence between `Subring.closure s` and `Algebra.adjoin ℤ s` given by
the identity map. -/
/-
**Subring.closureEquivAdjoinInt** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Subring.closureEquivAdjoinInt {R : Type*} [Ring R] (s : Set R) : Subring.c
losure s ≃ₐ[Int] Algebra.adjoin Int s
参数：s : Set R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `ℤ`-algebra equivalence between `Subring.closure s` and `Algebra.adjoin ℤ s`
 given by
the identity map.
-/
def Subring.closureEquivAdjoinInt {R : Type*} [Ring R] (s : Set R) :
    Subring.closure s ≃ₐ[ℤ] Algebra.adjoin ℤ s :=
  Subalgebra.equivOfEq (subalgebraOfSubring <| Subring.closure s) _ (adjoin_int s).symm

end NatInt

section

variable (F E : Type*) {K : Type*} [CommSemiring E] [Semiring K] [SMul F E] [Algebra E K]

/-- If `K / E / F` is a ring extension tower, `L` is a submonoid of `K / F` which is generated by
`S` as an `F`-module, then `E[L]` is generated by `S` as an `E`-module. -/
/-
**Submonoid.adjoin_eq_span_of_eq_span** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submonoid.adjoin_eq_span_of_eq_span [Semiring F] [Module F K] [IsScalarTow
er F E K] (L : Submonoid K) {S : Set K} (h : (L : Set K) = span F S) : toSubmodu
le (adjoin E (L : Set K)) = span E S
参数：L : Submonoid K；h : (L : Set K) = span F S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.adjoin_eq_span`：adjoin_eq_span : Subalgebra.toSubmodule (adjoin 
R s) = span R (Submonoid.closure s)
· 使用定理 `Submonoid.closure_eq`：closure_eq : closure (S : Set M) = S
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
· 使用定理 `Submodule.span_subset_span`：span_subset_span : ↑(span R s) subseteq (spa
n S s : Set M)
· 使用定理 `Submodule.span_mono`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {s t : Set M}, s ⊆ t 
→ Submodu…
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s

--- 原说明 ---
If `K / E / F` is a ring extension tower, `L` is a submonoid of `K / F` which is
 generated by
`S` as an `F`-module, then `E[L]` is generated by `S` as an `E`-module.
-/
theorem Submonoid.adjoin_eq_span_of_eq_span [Semiring F] [Module F K] [IsScalarTower F E K]
    (L : Submonoid K) {S : Set K} (h : (L : Set K) = span F S) :
    toSubmodule (adjoin E (L : Set K)) = span E S := by
  rw [adjoin_eq_span, L.closure_eq, h]
  exact (span_le.mpr <| span_subset_span _ _ _).antisymm (span_mono subset_span)

variable [CommSemiring F] [Algebra F K] [IsScalarTower F E K] (L : Subalgebra F K) {F}

/-- If `K / E / F` is a ring extension tower, `L` is a subalgebra of `K / F` which is generated by
`S` as an `F`-module, then `E[L]` is generated by `S` as an `E`-module. -/
/-
**Subalgebra.adjoin_eq_span_of_eq_span** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subalgebra.adjoin_eq_span_of_eq_span {S : Set K} (h : toSubmodule L = span
 F S) : toSubmodule (adjoin E (L : Set K)) = span E S
参数：h : toSubmodule L = span F S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.adjoin_eq_span_of_eq_span`：Submonoid.adjoin_eq_span_of_eq_span
 [Semiring F] [Module F K] [IsScalarTower F E K] (L : Submonoid K) {S : Set K} (
h : (L : Set K) = span F …
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂

--- 原说明 ---
If `K / E / F` is a ring extension tower, `L` is a subalgebra of `K / F` which i
s generated by
`S` as an `F`-module, then `E[L]` is generated by `S` as an `E`-module.
-/
theorem Subalgebra.adjoin_eq_span_of_eq_span {S : Set K} (h : toSubmodule L = span F S) :
    toSubmodule (adjoin E (L : Set K)) = span E S :=
  L.toSubmonoid.adjoin_eq_span_of_eq_span F E (congr_arg ((↑) : _ → Set K) h)

end

section CommSemiring
variable (R) [CommSemiring R] [Ring A] [Algebra R A] [Ring B] [Algebra R B]

/-
**NonUnitalAlgebra.adjoin_le_algebra_adjoin** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：NonUnitalAlgebra.adjoin_le_algebra_adjoin (s : Set A) : adjoin R s <= (Alg
ebra.adjoin R s).toNonUnitalSubalgebra
参数：s : Set A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalAlgebra.adjoin_le`：adjoin_le {S : NonUnitalSubalgebra R A} {s :
 Set A} (hs : s subseteq S) : adjoin R s <= S
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Algebra.subset_adjoin`：subset_adjoin : s subseteq adjoin R s
-/
lemma NonUnitalAlgebra.adjoin_le_algebra_adjoin (s : Set A) :
    adjoin R s ≤ (Algebra.adjoin R s).toNonUnitalSubalgebra := adjoin_le Algebra.subset_adjoin
/-
**Algebra.adjoin_nonUnitalSubalgebra** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Algebra.adjoin_nonUnitalSubalgebra (s : Set A) : adjoin R (NonUnitalAlgebr
a.adjoin R s : Set A) = adjoin R s
参数：s : Set A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Algebra.adjoin_le`：adjoin_le {S : Subalgebra R A} (H : s subseteq S) : a
djoin R s <= S
· 使用引理 `NonUnitalAlgebra.adjoin_le_algebra_adjoin`：NonUnitalAlgebra.adjoin_le_al
gebra_adjoin (s : Set A) : adjoin R s <= (Algebra.adjoin R s).toNonUnitalSubalge
bra
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `NonUnitalAlgebra.subset_adjoin`：subset_adjoin {s : Set A} : s subseteq a
djoin R s
· 使用定理 `Algebra.subset_adjoin`：subset_adjoin : s subseteq adjoin R s
-/
lemma Algebra.adjoin_nonUnitalSubalgebra (s : Set A) :
    adjoin R (NonUnitalAlgebra.adjoin R s : Set A) = adjoin R s :=
  le_antisymm
    (adjoin_le <| NonUnitalAlgebra.adjoin_le_algebra_adjoin R s)
    (adjoin_le <| (NonUnitalAlgebra.subset_adjoin R).trans subset_adjoin)

end CommSemiring

namespace Subalgebra

section toNonUnitalSubalgebra

variable [CommSemiring R] [Semiring A] [Algebra R A]

/-- The forgetful map from subalgebras to non-unital subalgebras, as an order embedding. -/
/-
**Subalgebra.toNonUnitalSubalgebraOrderEmbedding** 是 Mathlib 中的一个定义，位于命名空间 `Suba
lgebra`。
形式化陈述：toNonUnitalSubalgebraOrderEmbedding : Subalgebra R A ↪o NonUnitalSubalgebr
a R A where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Subalgebra.toNonUnitalSubalgebra_injective`：toNonUnitalSubalgebra_inject
ive : Function.Injective (toNonUnitalSubalgebra : Subalgebra R A -> NonUnitalSub
algebra R A)

--- 原说明 ---
The forgetful map from subalgebras to non-unital subalgebras, as an order embedd
ing.
-/
def toNonUnitalSubalgebraOrderEmbedding : Subalgebra R A ↪o NonUnitalSubalgebra R A where
  toFun := toNonUnitalSubalgebra
  inj' := toNonUnitalSubalgebra_injective
  map_rel_iff' := by simp [SetLike.le_def]

@[simp]
/-
**Subalgebra.toNonUnitalSubalgebra_le_toNonUnitalSubalgebra** 是 Mathlib 中的一个引理，位
于命名空间 `Subalgebra`。
形式化陈述：toNonUnitalSubalgebra_le_toNonUnitalSubalgebra {S T : Subalgebra R A} : S.
toNonUnitalSubalgebra <= T.toNonUnitalSubalgebra ↔ S <= T
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderEmbedding.le_iff_le`：le_iff_le {a b} : f a <= f b ↔ a <= b
-/
lemma toNonUnitalSubalgebra_le_toNonUnitalSubalgebra {S T : Subalgebra R A} :
    S.toNonUnitalSubalgebra ≤ T.toNonUnitalSubalgebra ↔ S ≤ T :=
  toNonUnitalSubalgebraOrderEmbedding.le_iff_le

alias ⟨_, toNonUnitalSubalgebra_mono⟩ := toNonUnitalSubalgebra_le_toNonUnitalSubalgebra

end toNonUnitalSubalgebra

variable [CommSemiring R] [Ring A] [Algebra R A] [Ring B] [Algebra R B]

/-
**Subalgebra.comap_map_eq** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：comap_map_eq (f : A ->ₐ[R] B) (S : Subalgebra R A) : (S.map f).comap f = S
 ⊔ Algebra.adjoin R (f ⁻¹' {0})
参数：f : A ->ₐ[R] B；S : Subalgebra R A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subalgebra.mem_map`：mem_map {S : Subalgebra R A} {f : A ->ₐ[R] B} {y : B
} : y in map f S ↔ exists x in S, f x = y
· 使用定理 `Subalgebra.mem_comap`：mem_comap (S : Subalgebra R B) (f : A ->ₐ[R] B) (x
 : A) : x in S.comap f ↔ f x in S
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.adjoin_eq`：adjoin_eq (S : Subalgebra R A) : adjoin R ↑S = S
· 使用定理 `Algebra.adjoin_union`：adjoin_union (s t : Set A) : adjoin R (s union t) 
= adjoin R s ⊔ adjoin R t
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b
· 使用定理 `Subalgebra.add_mem`：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] 
[inst_1 : Semiring A] [inst_2 : Algebra R A] (S : Subalgebra R A)   {x y : A}, x
 ∈ S → y…
· 使用定理 `Algebra.subset_adjoin`：subset_adjoin : s subseteq adjoin R s
· 使用定理 `Subalgebra.map_le`：map_le {S : Subalgebra R A} {f : A ->ₐ[R] B} {U : Sub
algebra R B} : map f S <= U ↔ S <= comap f U
· 使用定理 `Algebra.map_sup`：map_sup (f : A ->ₐ[R] B) (S T : Subalgebra R A) : (S ⊔ 
T).map f = S.map f ⊔ T.map f
· 使用定理 `AlgHom.map_adjoin`：map_adjoin (φ : A ->ₐ[R] B) (s : Set A) : (adjoin R s
).map φ = adjoin R (φ '' s)
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `sup_eq_left`：sup_eq_left : a ⊔ b = a ↔ b <= a
· 使用定理 `Algebra.adjoin_le_iff`：adjoin_le_iff {S : Subalgebra R A} : adjoin R s <
= S ↔ s subseteq S
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.image_preimage_subset`：image_preimage_subset (f : α -> β) (s : Set β
) : f '' f ⁻¹' s subseteq s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用定理 `Subalgebra.zero_mem`：∀ {R : Type u} {A : Type v} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A] (S : Subalgebra R A),   0 ∈ S
-/
theorem comap_map_eq (f : A →ₐ[R] B) (S : Subalgebra R A) :
    (S.map f).comap f = S ⊔ Algebra.adjoin R (f ⁻¹' {0}) := by
  apply le_antisymm
  · intro x hx
    rw [mem_comap, mem_map] at hx
    obtain ⟨y, hy, hxy⟩ := hx
    replace hxy : x - y ∈ f ⁻¹' {0} := by simp [hxy]
    rw [← Algebra.adjoin_eq S, ← Algebra.adjoin_union, ← add_sub_cancel y x]
    exact Subalgebra.add_mem _
      (Algebra.subset_adjoin <| Or.inl hy) (Algebra.subset_adjoin <| Or.inr hxy)
  · rw [← map_le, Algebra.map_sup, f.map_adjoin]
    apply le_of_eq
    rw [sup_eq_left, Algebra.adjoin_le_iff]
    exact (Set.image_preimage_subset f {0}).trans (Set.singleton_subset_iff.2 (S.map f).zero_mem)
/-
**Subalgebra.comap_map_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：comap_map_eq_self {f : A ->ₐ[R] B} {S : Subalgebra R A} (h : f ⁻¹' {0} sub
seteq S) : (S.map f).comap f = S
参数：h : f ⁻¹' {0} subseteq S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `left_eq_sup`：left_eq_sup : a = a ⊔ b ↔ b <= a
· 使用定理 `Algebra.adjoin_le_iff`：adjoin_le_iff {S : Subalgebra R A} : adjoin R s <
= S ↔ s subseteq S
· 使用定理 `Subalgebra.comap_map_eq`：comap_map_eq (f : A ->ₐ[R] B) (S : Subalgebra R
 A) : (S.map f).comap f = S ⊔ Algebra.adjoin R (f ⁻¹' {0})
-/
theorem comap_map_eq_self {f : A →ₐ[R] B} {S : Subalgebra R A}
    (h : f ⁻¹' {0} ⊆ S) : (S.map f).comap f = S := by
  convert! comap_map_eq f S
  rwa [left_eq_sup, Algebra.adjoin_le_iff]

end Subalgebra

end Adjoin

